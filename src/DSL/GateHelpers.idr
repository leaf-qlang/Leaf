module DSL.GateHelpers

import Data.Fin
import Data.Vect
import DSL.Gates
import DSL.Circuit
import public DSL.Control
import DSL.Core

%default total

-- 1-qbit Clifford + T gates
public export
identity : {0 ctx : ClassicalContext} ->
           {0 inputWidth : Nat} ->
           {0 outputWidth : Nat} ->
           (q : Fin outputWidth) ->
           Circuit ctx inputWidth outputWidth UnitType ->
           Circuit ctx inputWidth outputWidth UnitType
identity q circ = Sequence circ (SingleGate (UGate (Id q)))

public export
x : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
x q circ = Sequence circ (SingleGate (UGate (X q)))

public export
y : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
y q circ = Sequence circ (SingleGate (UGate (Y q)))

public export
z : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
z q circ = Sequence circ (SingleGate (UGate (Z q)))

public export
hadamard : {0 ctx : ClassicalContext} ->
           {0 inputWidth : Nat} ->
           {0 outputWidth : Nat} ->
           (q : Fin outputWidth) ->
           Circuit ctx inputWidth outputWidth UnitType ->
           Circuit ctx inputWidth outputWidth UnitType
hadamard q circ = Sequence circ (SingleGate (UGate (H q)))

public export
s : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
s q circ = Sequence circ (SingleGate (UGate (S q)))

public export
t : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
t q circ = Sequence circ (SingleGate (UGate (T q)))

public export
sDag : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       (q : Fin outputWidth) ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
sDag q circ = Sequence circ (SingleGate (UGate (SDG q)))

public export
tDag : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       (q : Fin outputWidth) ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
tDag q circ = Sequence circ (SingleGate (UGate (TDG q)))

public export
sx : {0 ctx : ClassicalContext} ->
     {0 inputWidth : Nat} ->
     {0 outputWidth : Nat} ->
     (q : Fin outputWidth) ->
     Circuit ctx inputWidth outputWidth UnitType ->
     Circuit ctx inputWidth outputWidth UnitType
sx q circ = Sequence circ (SingleGate (UGate (SX q)))

public export
sxDag : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (q : Fin outputWidth) ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
sxDag q circ = Sequence circ (SingleGate (UGate (SXDG q)))


-- Rotation gates
public export
rotX : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       Radians ->
       (q : Fin outputWidth) ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
rotX angle q circ = Sequence circ (SingleGate (UGate (RX angle q)))

public export
rotY : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       Radians ->
       (q : Fin outputWidth) ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
rotY angle q circ = Sequence circ (SingleGate (UGate (RY angle q)))

public export
rotZ : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       Radians ->
       (q : Fin outputWidth) ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
rotZ angle q circ = Sequence circ (SingleGate (UGate (RZ angle q)))


-- U-family gates
public export
u : {0 ctx : ClassicalContext} ->
    {0 inputWidth : Nat} ->
    {0 outputWidth : Nat} ->
    Radians ->
    Radians ->
    Radians ->
    (q : Fin outputWidth) ->
    Circuit ctx inputWidth outputWidth UnitType ->
    Circuit ctx inputWidth outputWidth UnitType
u theta phi lambda q circ = Sequence circ (SingleGate (UGate (U theta phi lambda q)))

public export
u1 : {0 ctx : ClassicalContext} ->
     {0 inputWidth : Nat} ->
     {0 outputWidth : Nat} ->
     Radians ->
     (q : Fin outputWidth) ->
     Circuit ctx inputWidth outputWidth UnitType ->
     Circuit ctx inputWidth outputWidth UnitType
u1 lambda q circ = Sequence circ (SingleGate (UGate (U1 lambda q)))

public export
u2 : {0 ctx : ClassicalContext} ->
     {0 inputWidth : Nat} ->
     {0 outputWidth : Nat} ->
     Radians ->
     Radians ->
     (q : Fin outputWidth) ->
     Circuit ctx inputWidth outputWidth UnitType ->
     Circuit ctx inputWidth outputWidth UnitType
u2 phi lambda q circ = Sequence circ (SingleGate (UGate (U2 phi lambda q)))


public export
u3 : {0 ctx : ClassicalContext} ->
     {0 inputWidth : Nat} ->
     {0 outputWidth : Nat} ->
     Radians ->
     Radians ->
     Radians ->
     (q : Fin outputWidth) ->
     Circuit ctx inputWidth outputWidth UnitType ->
     Circuit ctx inputWidth outputWidth UnitType
u3 theta phi lambda q circ = Sequence circ (SingleGate (UGate (U3 theta phi lambda q)))


-- Additional operations
public export
measure : {0 ctx : ClassicalContext} ->
          {0 inputWidth : Nat} ->
          {0 outputWidth : Nat} ->
          (q : Fin outputWidth) ->
          Circuit ctx inputWidth outputWidth UnitType ->
          Circuit ctx inputWidth outputWidth BitType
measure q circ = Sequence circ (Measure q)

public export
reset : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (q : Fin outputWidth) ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
reset q circ = Sequence circ (SingleGate (Reset q))


-- Two-qbit gates
public export
cnot : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       (c, t : Fin outputWidth) ->
       {auto 0 neq : Not (c = t)} ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
cnot c t circ = Sequence circ (SingleGate (UGate (CX c t)))

public export
ctrlY : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (c, t : Fin outputWidth) ->
        {auto 0 neq : Not (c = t)} ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
ctrlY c t circ = Sequence circ (SingleGate (UGate (CY c t)))

public export
ctrlZ : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (c, t : Fin outputWidth) ->
        {auto 0 neq : Not (c = t)} ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
ctrlZ c t circ = Sequence circ (SingleGate (UGate (CZ c t)))

public export
swap : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       (a, b : Fin outputWidth) ->
       {auto 0 neq : Not (a = b)} ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
swap a b circ = Sequence circ (SingleGate (UGate (SWAP a b)))

public export
ctrlH : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (c, t : Fin outputWidth) ->
        {auto 0 neq : Not (c = t)} ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
ctrlH c t circ = Sequence circ (SingleGate (UGate (CH c t)))

public export
ctrlS : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (c, t : Fin outputWidth) ->
        {auto 0 neq : Not (c = t)} ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
ctrlS c t circ = Sequence circ (SingleGate (UGate (CS c t)))

public export
ctrlSDag : {0 ctx : ClassicalContext} ->
           {0 inputWidth : Nat} ->
           {0 outputWidth : Nat} ->
           (c, t : Fin outputWidth) ->
           {auto 0 neq : Not (c = t)} ->
           Circuit ctx inputWidth outputWidth UnitType ->
           Circuit ctx inputWidth outputWidth UnitType
ctrlSDag c t circ = Sequence circ (SingleGate (UGate (CSDG c t)))

public export
ctrlT : {0 ctx : ClassicalContext} ->
        {0 inputWidth : Nat} ->
        {0 outputWidth : Nat} ->
        (c, t : Fin outputWidth) ->
        {auto 0 neq : Not (c = t)} ->
        Circuit ctx inputWidth outputWidth UnitType ->
        Circuit ctx inputWidth outputWidth UnitType
ctrlT c t circ = Sequence circ (SingleGate (UGate (CT c t)))

public export
ctrlTDag : {0 ctx : ClassicalContext} ->
           {0 inputWidth : Nat} ->
           {0 outputWidth : Nat} ->
           (c, t : Fin outputWidth) ->
           {auto 0 neq : Not (c = t)} ->
           Circuit ctx inputWidth outputWidth UnitType ->
           Circuit ctx inputWidth outputWidth UnitType
ctrlTDag c t circ = Sequence circ (SingleGate (UGate (CTDG c t)))

public export
ctrlSX : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlSX c t circ = Sequence circ (SingleGate (UGate (CSX c t)))

public export
ctrlSXDag : {0 ctx : ClassicalContext} ->
            {0 inputWidth : Nat} ->
            {0 outputWidth : Nat} ->
            (c, t : Fin outputWidth) ->
            {auto 0 neq : Not (c = t)} ->
            Circuit ctx inputWidth outputWidth UnitType ->
            Circuit ctx inputWidth outputWidth UnitType
ctrlSXDag c t circ = Sequence circ (SingleGate (UGate (CSXDG c t)))


-- ctrl rotation gates
public export
ctrlRX : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlRX angle c t circ = Sequence circ (SingleGate (UGate (CRX angle c t)))

public export
ctrlRY : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlRY angle c t circ = Sequence circ (SingleGate (UGate (CRY angle c t)))

public export
ctrlRZ : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlRZ angle c t circ = Sequence circ (SingleGate (UGate (CRZ angle c t)))

-- ctrl U gates
public export
ctrlU1 : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlU1 lambda c t circ = Sequence circ (SingleGate (UGate (CU1 lambda c t)))

public export
ctrlU2 : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlU2 phi lambda c t circ = Sequence circ (SingleGate (UGate (CU2 phi lambda c t)))

public export
ctrlU3 : {0 ctx : ClassicalContext} ->
         {0 inputWidth : Nat} ->
         {0 outputWidth : Nat} ->
         Radians ->
         Radians ->
         Radians ->
         (c, t : Fin outputWidth) ->
         {auto 0 neq : Not (c = t)} ->
         Circuit ctx inputWidth outputWidth UnitType ->
         Circuit ctx inputWidth outputWidth UnitType
ctrlU3 theta phi lambda c t circ = Sequence circ (SingleGate (UGate (CU3 theta phi lambda c t)))

-- Two-qbit interaction gates
public export
rxx : {0 ctx : ClassicalContext} ->
      {0 inputWidth : Nat} ->
      {0 outputWidth : Nat} ->
      Radians ->
      (a, b : Fin outputWidth) ->
      {auto 0 neq : Not (a = b)} ->
      Circuit ctx inputWidth outputWidth UnitType ->
      Circuit ctx inputWidth outputWidth UnitType
rxx angle a b circ = Sequence circ (SingleGate (UGate (RXX angle a b)))

public export
ryy : {0 ctx : ClassicalContext} ->
      {0 inputWidth : Nat} ->
      {0 outputWidth : Nat} ->
      Radians ->
      (a, b : Fin outputWidth) ->
      {auto 0 neq : Not (a = b)} ->
      Circuit ctx inputWidth outputWidth UnitType ->
      Circuit ctx inputWidth outputWidth UnitType
ryy angle a b circ = Sequence circ (SingleGate (UGate (RYY angle a b)))

public export
rzz : {0 ctx : ClassicalContext} ->
      {0 inputWidth : Nat} ->
      {0 outputWidth : Nat} ->
      Radians ->
      (a, b : Fin outputWidth) ->
      {auto 0 neq : Not (a = b)} ->
      Circuit ctx inputWidth outputWidth UnitType ->
      Circuit ctx inputWidth outputWidth UnitType
rzz angle a b circ = Sequence circ (SingleGate (UGate (RZZ angle a b)))

public export
rzx : {0 ctx : ClassicalContext} ->
      {0 inputWidth : Nat} ->
      {0 outputWidth : Nat} ->
      Radians ->
      (a, b : Fin outputWidth) ->
      {auto 0 neq : Not (a = b)} ->
      Circuit ctx inputWidth outputWidth UnitType ->
      Circuit ctx inputWidth outputWidth UnitType
rzx angle a b circ = Sequence circ (SingleGate (UGate (RZX angle a b)))

-- Three-qbit gates
public export
toffoli : {0 ctx : ClassicalContext} ->
          {0 inputWidth : Nat} ->
          {0 outputWidth : Nat} ->
          (c1, c2, t : Fin outputWidth) ->
          {auto 0 d12 : Not (c1 = c2)} ->
          {auto 0 d1t : Not (c1 = t)} ->
          {auto 0 d2t : Not (c2 = t)} ->
          Circuit ctx inputWidth outputWidth UnitType ->
          Circuit ctx inputWidth outputWidth UnitType
toffoli c1 c2 t circ = Sequence circ (SingleGate (UGate (CCX c1 c2 t)))

public export
fredkin : {0 ctx : ClassicalContext} ->
          {0 inputWidth : Nat} ->
          {0 outputWidth : Nat} ->
          (c, a, b : Fin outputWidth) ->
          {auto 0 cab : Not (a = b)} ->
          {auto 0 ca  : Not (c = a)} ->
          {auto 0 cb  : Not (c = b)} ->
          Circuit ctx inputWidth outputWidth UnitType ->
          Circuit ctx inputWidth outputWidth UnitType
fredkin c a b circ = Sequence circ (SingleGate (UGate (CSWAP c a b)))

-- Generic multi-controlled gate construction
public export
ctrl : {0 ctx : ClassicalContext} ->
       {0 inputWidth : Nat} ->
       {0 outputWidth : Nat} ->
       {k : Nat} ->
       (cs : Vect k (Fin outputWidth)) ->    -- control wires
       (bs : Vect k QState) ->               -- control wire polarities: 0, 1, +, -, +i, -i
       (inner : UnitaryGate outputWidth) ->  -- gate to be controlled
       {auto 0 distinct : AllDistinct cs} ->
       {auto 0 disjoint : Disjoint cs (snd (wiresUnitary inner))} ->
       Circuit ctx inputWidth outputWidth UnitType ->
       Circuit ctx inputWidth outputWidth UnitType
ctrl cs bs inner {distinct} {disjoint} circ =
  let uCtrl : UnitaryGate outputWidth
      uCtrl = Controlled cs bs inner
        {distinct = distinct}
        {disjoint = disjoint}
  in Sequence circ (SingleGate (UGate uCtrl))

