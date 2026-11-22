module TypeChecker.Phases.OwnershipCheckTest

import TestFramework

import Compiler.Frontend.TypeChecker.Data
import TypeChecker.Helper

%default total

--------------------------------------------------------------------------------
-- Pass C, part 2: ownership, initialization and cleanup
--------------------------------------------------------------------------------
-- OwnershipCheck interprets the recorded events over control flow (plan steps 15
-- and 21): definite initialization and mutability, linearity and affine drops,
-- partial moves, exclusive loans with non-lexical lifetimes, reference
-- lifetimes, and the proofs behind scratch, `:=`, uncompute and transformed
-- blocks. An initialization or mutability error points at the offending read
-- or write; a loan conflict at the conflicting access; an unconsumed or
-- unreclaimable qubit at the binding that introduced it.
--------------------------------------------------------------------------------

-- Initialization and mutability (plan step 15 rule 1)
initializationTests : List TestResult
initializationTests = Test.do
  test "a local may be initialized once after its declaration" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; x = 1; x }" `shouldBe` accepted

  test "reading an uninitialized local is rejected" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 29))

  test "a local initialized in one branch only is not definitely initialized" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { x = 1; } x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 52))

  test "a local initialized in both branches is definitely initialized" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { x = 1; } else { x = 2; } x }"
      `shouldBe` accepted

  test "an uninitialized local in a const fn is rejected" $
    typeCheckOutcome "const fn f() -> u32 { let x: u32; x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 35))

  test "a compound assignment needs an initialized target" $
    typeCheckOutcome "fn f() { let mut x: i32; x += 1; }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 26))

  test "a second assignment needs mut" $
    typeCheckOutcome "fn f() { let x: i32; x = 1; x = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 29))

  test "an initialized immutable local cannot be reassigned" $
    typeCheckOutcome "fn f() { let x = 1; x = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 21))

  test "a mutable local can be reassigned" $
    typeCheckOutcome "fn f() -> i32 { let mut x = 1; x = 2; x }" `shouldBe` accepted

  test "an element of an immutable array cannot be assigned" $
    typeCheckOutcome "fn f() { let a = [1, 2]; a[0] = 3; }"
      `shouldBe` rejectedWith (ImmutableAssignment "a" (spanAt 1 26))

  test "a field of an immutable tuple cannot be assigned" $
    typeCheckOutcome "fn f() { let t = (0, 0.0); t.0 = 3; }"
      `shouldBe` rejectedWith (ImmutableAssignment "t" (spanAt 1 28))

  test "elements of mutable arrays and tuples can be assigned" $
    typeCheckOutcome "fn f() { let mut x: [i32; 2] = [0, 0]; x[0] = 10; let mut t: (i32, f64) = (0, 0.0); t.0 = 3; }"
      `shouldBe` accepted

  test "a mutable borrow needs a mutable place" $
    typeCheckOutcome "fn f() { let x = 10; let r = &mut x; }"
      `shouldBe` rejectedWith (MutableBorrowOfImmutable "x" (spanAt 1 30))

  test "a qubit can be moved and replaced in place" $
    typeCheckOutcome "fn f() -> qbit { let mut q = qalloc(); q = H(q); q }" `shouldBe` accepted

  test "replacing a live linear qubit loses it" $
    typeCheckOutcome "fn f() -> qbit { let mut q = qalloc(); q = qalloc(); q }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 40))

  test "a loop body runs before its break" $
    typeCheckOutcome "fn f() -> i32 { let x: i32; loop { x = 1; break; } x }" `shouldBe` accepted

  test "an immutable local assigned in a loop is assigned twice" $
    typeCheckOutcome "fn f() { let x: i32; loop { x = 1; } }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 29))

  test "an immutable parameter cannot be assigned" $
    typeCheckOutcome "fn f(x: i32) { x = 1; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 16))

  test "a compound assignment needs a mutable target" $
    typeCheckOutcome "fn f() { let x = 1; x += 1; }"
      `shouldBe` rejectedWith (ImmutableAssignment "x" (spanAt 1 21))

  test "a constant cannot be assigned" $
    typeCheckOutcome "const N: i32 = 1; fn f() { N = 2; }"
      `shouldBe` rejectedWith (ImmutableAssignment "N" (spanAt 1 28))

-- Linearity (plan step 15 rule 2)
linearityTests : List TestResult
linearityTests = Test.do
  test "a linear qubit must be consumed" $
    typeCheckOutcome "fn f() { let q = qalloc(); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 14))

  test "a linear qubit parameter must be consumed" $
    typeCheckOutcome "fn f(q: qbit) {}"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 6))

  test "returning a qubit consumes it" $
    typeCheckOutcome "fn f() -> qbit { qalloc() }" `shouldBe` accepted

  test "a qubit consumed on one path only is not consumed" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); if c { discard(q); } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 21))

  test "a qubit consumed on every path is consumed" $
    typeCheckOutcome "fn f(c: bool) { let q = qalloc(); if c { discard(q); } else { let b = measr(q); } }"
      `shouldBe` accepted

  test "a qubit consumed only inside a loop that may not run is not consumed" $
    typeCheckOutcome "fn f(n: u32) { let q = qalloc(); for i in 0..n { discard(q); break; } }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 20))

-- Partial moves (plan step 15 rule 3)
partialMoveTests : List TestResult
partialMoveTests = Test.do
  test "tuple components can be moved separately" $
    typeCheckOutcome "fn f() { let p = (qalloc(), qalloc()); discard(p.0); discard(p.1); }"
      `shouldBe` accepted

  test "a partially moved tuple cannot be used whole" $
    typeCheckOutcome "fn f() -> (qbit, qbit) { let p = (qalloc(), qalloc()); discard(p.0); p }"
      `shouldBe` rejectedWith (UseAfterMove "p" (spanAt 1 70))

  test "array elements at constant indexes can be moved separately" $
    typeCheckOutcome "fn f() -> [bit; 2] { let qs = qalloc(3); let (b0, b1) = measr(qs[0], qs[1]); discard(qs[2]); [b0, b1] }"
      `shouldBe` accepted

  test "an array with a moved element cannot be used whole" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); discard(qs[0]); discard(qs); }"
      `shouldBe` rejectedWith (UseAfterMove "qs" (spanAt 1 54))

  test "the remaining elements of a partially moved array must be consumed" $
    typeCheckOutcome "fn f() { let qs = qalloc(2); discard(qs[0]); }"
      `shouldBe` rejectedWith (LinearQbitNotConsumed (spanAt 1 14))

  test "a move through a dynamic index is not tracked" $
    typeCheckOutcome "fn f(i: usize) { let qs = qalloc(2); discard(qs[i]); discard(qs[1 - i]); }"
      `shouldBe` rejectedWith (UntrackedElementMove (spanAt 1 46))

  test "a borrow through a dynamic index stays usable" $
    typeCheckOutcome "fn f(i: usize) { let qs = qalloc(4); H(&qs[i]); discard(qs); }" `shouldBe` accepted

  test "an owned qubit cannot be moved out through a reference" $
    typeCheckOutcome "fn f(qs: &[qbit]) { discard(qs[0]); }"
      `shouldBe` rejectedWith (MoveOutOfBorrow (spanAt 1 29))

  test "a moved array element can be replaced at a constant index" $
    typeCheckOutcome "fn f() { let mut qs = qalloc(2); discard(qs[0]); qs[0] = qalloc(); discard(qs); }"
      `shouldBe` accepted

-- Exclusive loans and non-lexical lifetimes (plan step 15 rule 4)
loanTests : List TestResult
loanTests = Test.do
  test "a qubit cannot be borrowed twice in one call" $
    typeCheckOutcome "fn f(q: &qbit) { CX(q, q); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 24))

  test "two different qubits can be borrowed in one call" $
    typeCheckOutcome "fn f(a: &qbit, b: &qbit) { CX(a, b); }" `shouldBe` accepted

  test "disjoint elements of a qubit slice can be borrowed together" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let qv: &[qbit] = &qs[..]; CX(&qv[1], &qv[2]); discard(qs); }"
      `shouldBe` accepted

  test "the same element of a qubit slice cannot be borrowed twice" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let qv: &[qbit] = &qs[..]; CX(&qv[1], &qv[1]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 79))

  test "overlapping qubit slices cannot be live together" $
    typeCheckOutcome "fn f() { let qs: [qbit; 4] = qalloc(4); let a = &qs[0..2]; let b = &qs[1..3]; H(&a[0]); H(&b[0]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 68))

  test "a loan ends at its last use" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r1 = &mut a; r1[0] = 3; let r2 = &mut a; r2[0] = 4; }"
      `shouldBe` accepted

  test "two live mutable loans of one place conflict" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r1 = &mut a; let r2 = &mut a; r1[0] = 3; r2[0] = 4; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 56))

  test "shared classical loans can coexist" $
    typeCheckOutcome "fn f() -> i32 { let a = [1, 2]; let r1 = &a; let r2 = &a; r1[0] + r2[1] }"
      `shouldBe` accepted

  test "a place cannot be read while it is mutably borrowed" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r = &mut a; let y = a[0]; r[0] = 1; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 54))

  test "a borrowed qubit cannot be moved while the loan is live" $
    typeCheckOutcome "fn f() { let q = qalloc(); let r = &q; discard(q); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 48))

  test "a loop index that cannot reach the target does not overlap it" $
    typeCheckOutcome "unitary fn f(qs: [qbit; 5]) -> [qbit; 5] { for i in 0..4 { ctrl(&qs[i]).apply(X)(&qs[4]); } qs }"
      `shouldBe` accepted

  test "a loop index that can reach the target overlaps it" $
    typeCheckOutcome "unitary fn f(qs: [qbit; 5]) -> [qbit; 5] { for i in 0..5 { ctrl(&qs[i]).apply(X)(&qs[4]); } qs }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 82))

  test "dynamic indexes are not proven disjoint" $
    typeCheckOutcome "fn f(qs: &[qbit], i: usize, j: usize) { CX(&qs[i], &qs[j]); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 52))

  test "a loan used again on the next iteration stays live" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; for i in 0..2 { H(r); H(&qs[0]); } }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 61))

  test "a place cannot be written while it is shared-borrowed" $
    typeCheckOutcome "fn f() { let mut a = [1, 2]; let r = &a; a[0] = 3; let y = r[0]; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 42))

  test "a place cannot be mutably borrowed twice in one call" $
    typeCheckOutcome "fn g(a: &mut [i32], b: &mut [i32]) {} fn f() { let mut x = [1]; g(&mut x, &mut x); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 75))

  test "a place can be shared-borrowed twice in one call" $
    typeCheckOutcome "fn g(a: &[i32], b: &[i32]) {} fn f() { let x = [1]; g(&x, &x); }" `shouldBe` accepted

-- Reference lifetimes (plan step 15 rule 5)
referenceLifetimeTests : List TestResult
referenceLifetimeTests = Test.do
  test "a reference into a parameter may be returned" $
    typeCheckOutcome "fn first(xs: &[i32]) -> &i32 { &xs[0] }" `shouldBe` accepted

  test "a reference to a local cannot be returned" $
    typeCheckOutcome "fn f() -> &i32 { let x = 5; &x }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 29))

  test "a const fn cannot return a reference to its local" $
    typeCheckOutcome "const fn r() -> &u32 { let x = 5; &x }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 35))

  test "a reference to a local cannot escape inside a tuple" $
    typeCheckOutcome "fn f(a: &i32) -> (i32, &i32) { let x = 1; (x, &x) }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 47))

  test "a block cannot return a reference to its own local" $
    typeCheckOutcome "fn f() -> i32 { let r = { let x = 1; &x }; r + 1 }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 38))

  test "a reference to a constant may be returned without reference parameters" $
    typeCheckOutcome "const A: [i32; 2] = [1, 2]; fn f() -> &[i32] { &A }" `shouldBe` accepted

-- Joins and reference provenance (plan steps 14 and 15; spec §9).
provenanceAndFlowTests : List TestResult
provenanceAndFlowTests = Test.do
  test "a divergent branch does not invalidate initialization on the continuing branch" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; if c { return 0; } else { x = 1; } x }" `shouldBe` accepted

  test "a while body may execute zero times when establishing initialization" $
    typeCheckOutcome "fn f(c: bool) -> i32 { let x: i32; while c { x = 1; break; } x }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 62))

  test "a borrow also requires a definitely initialized referent" $
    typeCheckOutcome "fn f() { let x: i32; let r = &x; let y = r + 1; }"
      `shouldBe` rejectedWith (UninitializedPlace "x" (spanAt 1 30))

  test "a mutable moved local may receive a fresh resource" $
    typeCheckOutcome "fn f() { let mut q = qalloc(); discard(q); q = qalloc(); discard(q); }" `shouldBe` accepted

  test "replacing a moved tuple component restores whole-value usability" $
    typeCheckOutcome "fn f() -> (qbit, qbit) { let mut p = (qalloc(), qalloc()); discard(p.0); p.0 = qalloc(); p }"
      `shouldBe` accepted

  test "disjoint qubit subslices may be live together" $
    typeCheckOutcome "fn f() { let qs = qalloc(4); let a = &qs[..2]; let b = &qs[2..]; CX(&a[1], &b[0]); discard(qs); }" `shouldBe` accepted

  test "a child reborrow ends before the parent is used again" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; H(r); H(&qs[0]); }" `shouldBe` accepted

  test "a live child reborrow suspends conflicting parent access" $
    typeCheckOutcome "fn f(qs: &[qbit]) { let r = &qs[0]; H(&qs[0]); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 39))

  test "nested slice offsets are normalized when checking aliases" $
    typeCheckOutcome "fn f() { let qs = qalloc(4); let tail = &qs[1..]; CX(&tail[0], &qs[1]); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 64))

  test "conditional quantum aliases remain usable until their last use" $
    typeCheckOutcome "fn f(c: bool) { let qs = qalloc(2); let r = if c { &qs[0] } else { &qs[1] }; H(r); discard(qs); }" `shouldBe` accepted

  test "a conditional alias reserves every possible origin while live" $
    typeCheckOutcome "fn f(c: bool) { let qs = qalloc(2); let r = if c { &qs[0] } else { &qs[1] }; H(&qs[0]); H(r); discard(qs); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 80))

  test "a mutable reference binding can change its referent" $
    typeCheckOutcome "fn f() { let mut a = [1]; let mut b = [2]; let mut r = &mut a; r[0] = 3; r = &mut b; r[0] = 4; a[0] = 5; }" `shouldBe` accepted

  test "a reference returned by a function retains its input origin" $
    typeCheckOutcome "fn identity(x: &i32) -> &i32 { x } fn f() -> i32 { let x = 1; let r = identity(&x); r + 1 }" `shouldBe` accepted

  test "a reference to a local cannot escape inside an array" $
    typeCheckOutcome "fn f() -> [&i32; 1] { let x = 1; [&x] }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 35))

  test "a parameter-origin reference may be returned inside an array" $
    typeCheckOutcome "fn f(x: &i32) -> [&i32; 1] { [x] }" `shouldBe` accepted

-- A returned loan keeps its origin and lifetime across the call boundary
-- (plan steps 14 and 15; spec §9, §51). The plan requires ambiguous lifetime
-- elision to fail (plan steps 9 and 15), but does not prescribe a diagnostic
-- constructor. Require a reported type error for that boundary without
-- classifying it as a dangling-reference error.
returnedReferenceTests : List TestResult
returnedReferenceTests = Test.do
  test "a returned qubit reference conflicts with access to its original element" $
    typeCheckOutcome "fn first(qs: &[qbit]) -> &qbit { &qs[0] } fn f(qs: &[qbit]) { let r = first(qs); H(&qs[0]); H(r); }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 84))

  test "the original qubit becomes available after the returned reference's last use" $
    typeCheckOutcome "fn first(qs: &[qbit]) -> &qbit { &qs[0] } fn f(qs: &[qbit]) { let r = first(qs); H(r); H(&qs[0]); }"
      `shouldBe` accepted

  test "a returned mutable slice keeps the original array exclusively borrowed" $
    typeCheckOutcome "fn identity(xs: &mut [i32]) -> &mut [i32] { xs } fn f() { let mut a = [1, 2]; let r = identity(&mut a); a[0] = 3; r[0] = 4; }"
      `shouldBe` rejectedWith (OverlappingBorrow (spanAt 1 105))

  test "the original array is writable after a returned mutable slice's last use" $
    typeCheckOutcome "fn identity(xs: &mut [i32]) -> &mut [i32] { xs } fn f() { let mut a = [1, 2]; let r = identity(&mut a); r[0] = 4; a[0] = 3; }"
      `shouldBe` accepted

  test "a reference to a local cannot escape through a function result" $
    typeCheckOutcome "fn identity(x: &i32) -> &i32 { x } fn f() -> &i32 { let x = 1; identity(&x) }"
      `shouldBe` rejectedWith (EscapingReference (spanAt 1 64))

  test "a reference to a constant may escape through a function result" $
    typeCheckOutcome "const N: i32 = 1; fn identity(x: &i32) -> &i32 { x } fn f() -> &i32 { identity(&N) }"
      `shouldBe` accepted

  test "a return lifetime cannot be elided between two reference parameters" $
    rejected (typeCheckOutcome "fn choose(c: bool, a: &i32, b: &i32) -> &i32 { if c { a } else { b } }")
      `shouldBe` True

export
runOwnershipCheckTests : IO Bool
runOwnershipCheckTests =
  runTests $ concat
    [ initializationTests
    , linearityTests
    , partialMoveTests
    , loanTests
    , referenceLifetimeTests
    , provenanceAndFlowTests
    , returnedReferenceTests
    ]
