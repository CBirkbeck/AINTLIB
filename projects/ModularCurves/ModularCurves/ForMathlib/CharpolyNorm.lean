/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-D29.
-/
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The characteristic polynomial of an algebra element as a norm

For a finite free `R`-algebra `B` and `b : B`, the characteristic polynomial of
multiplication by `b` is the norm of `X − b` relative to `B[X]/R[X]` (KM 1.8.2:
"the characteristic polynomial of `f ∈ B` is just the norm of `T − f` relative to
`B ⊗ R[T]/R[T]`"), with `B[X]` spelled as the base change `R[X] ⊗[R] B`.

Both sides are determinants of the same matrix over `R[X]`: the characteristic
matrix `X•1 − A.map C` of `A := leftMulMatrix b`.

This is the engine turning the norm-form of the full-set-of-sections condition
into its characteristic-polynomial form (KM 1.8.2 (2) ⟹ (1), ticket T-D30).

Note the statement is about `Algebra.lmul R B b`, not a general endomorphism: for
`g` a general endomorphism, `Algebra.norm` on the endomorphism algebra is
`det ^ (rank)`, not the characteristic polynomial — the algebra-element reading is
the (only) correct one.

Upstream candidate: mathlib has `LinearMap.charpoly`, `Algebra.norm`, and
`LinearMap.charpoly_baseChange`, but not this bridge.
-/

open Polynomial TensorProduct

universe u v

namespace Algebra

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
  [Module.Free R B] [Module.Finite R B]

/-- **Characteristic polynomial as a norm** (KM 1.8.2): for a finite free `R`-algebra `B` and
`b : B`, the characteristic polynomial of multiplication by `b` equals the norm, relative to
`(R[X] ⊗[R] B) / R[X]`, of `X ⊗ 1 − 1 ⊗ b` ("`T − b`"). -/
theorem charpoly_lmul_eq_norm (b : B) :
    (Algebra.lmul R B b).charpoly =
      Algebra.norm R[X] ((X : R[X]) ⊗ₜ[R] (1 : B) - (1 : R[X]) ⊗ₜ[R] b) := by
  rw [LinearMap.charpoly_def, ← leftMulMatrix_apply, Matrix.charpoly,
    norm_eq_matrix_det ((Module.Free.chooseBasis R B).baseChange R[X])]
  congr 1
  ext i j
  simp [Matrix.charmatrix_apply, Matrix.diagonal_apply, leftMulMatrix_eq_repr_mul, sub_mul,
    Finsupp.single_apply, smul_def, Polynomial.algebraMap_eq, eq_comm]

end Algebra
