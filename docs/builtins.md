### Built-in Functions


[Qubit operations](quantum-data-operations.md#operations-on-qubits):
```leaf
qalloc(), measr(), discard(), reset(), uncompute(), weaken(), tensor()
```

[Quantum contracts](quantum-contracts.md#quantum-contracts):
```leaf
clean(), basis(), isolated(), product(), separable(), stabilized()
```

[Circuit operations](quantum-gates.md#barrier):
```leaf
barrier()
```

[Adjoint operations](adjoint-operator.md):
```leaf
adjoint()
```

[Control operations](control-modifiers.md):
```leaf
ctrl().on().apply()
```

Array, slice and range operations:

`len()` returns the number of elements of an array, a slice, or a reference to either, as a `usize`.

`rev()` reverses a range, which is how a `for` loop counts down. It requires a range with both endpoints, so `rev(1..)` and `rev(..6)` are invalid:

Complex-valued phase() Prelude function is often used as helper for quantum states specification:
```leaf
phase(1.23) = exp(i * 1.23);
```

The turns() Prelude function translates floating point numbers representing fractions of 2π into angle type values. The angle has the width of the float it is made from: `turns` applied to an `f32` gives an `angle32`, and applied to an `f64` gives an `angle64`:
```leaf
turns(0.25) = π/2;
```

Declaring angle parameters via Param() Prelude built-in:
```leaf
Param("theta")
```

Trigonometric Prelude functions, which apply to `f32` and `f64`:
```leaf
cos(), acos(), sin(), asin(), tan(), atan()
```

Math utility Prelude functions:
```leaf
abs(), exp(), ceil(), floor(), ln(), log2(), log10(), max(), min(), round(), sqrt()
```
Here `abs` can be applied to signed integers and floats, `min/max` apply to any numeric type, and all the other functions apply to `f32` and `f64` only. Each function is overloaded per numeric type and its result has the type of its argument(s): `sqrt(x)` is an `f32` when `x` is an `f32` and an `f64` when `x` is an `f64`, and `min(a, b)` requires `a` and `b` to have the same type. Use `as` to convert between numeric types.
