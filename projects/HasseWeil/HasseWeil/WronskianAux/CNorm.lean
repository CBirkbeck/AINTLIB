import Mathlib.Algebra.Polynomial.Basic

/-!
# C-normalization simp set for polynomial ring tactics

`Polynomial.derivative_pow` produces `C ((n : ℕ) : R) * p^(n-1) * derivative p`,
where `((n : ℕ) : R)` is `Nat.cast n`. On the other side of an identity,
`Polynomial.C` is often applied to literals `(n : R)` which use `OfNat.ofNat`.
`ring` sees `C (Nat.cast n : R)` and `C (OfNat.ofNat n : R)` as distinct atoms,
blocking cancellation.

The pair `Nat.cast_ofNat` (already `@[simp]` in mathlib) plus
`Polynomial.C_ofNat` (not `@[simp]`) normalizes every `C k` for numeric `k` to
the polynomial literal `(k : Polynomial R)`. `Polynomial.C_ofNat` must be
explicitly included in `simp only` at call sites; this file just documents the
intended usage.

Typical use:
```
simp only [..., Polynomial.C_ofNat, Polynomial.C_mul, Polynomial.C_sub,
           Polynomial.C_pow, Polynomial.C_add, ...]
```
(`Nat.cast_ofNat` fires automatically since it is `@[simp]` — `simp only`
actually does not pick it up, so include it too for safety.)
-/
