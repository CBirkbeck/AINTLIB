/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q4 (KM A7 appendix).
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations

/-!
# Base change for rings of invariants (Katz–Mazur, Appendix A7)

For a finite group `G` acting on an `R`-algebra `A` by `R`-algebra automorphisms and
a base change `R → R'`, the group acts on `A ⊗[R] R'` through the left factor
(`g • (a ⊗ r') = (g • a) ⊗ r'`) and there is a natural comparison homomorphism

  `Aᴳ ⊗[R] R'  →  (A ⊗[R] R')ᴳ`    (KM A7.1: the map `∗(A, G, R, R')`).

This file provides:

* the `MulSemiringAction G (A ⊗[R] R')` instance extending mathlib's left-factor
  `DistribMulAction` (T-Q4a);
* `fixedPointsBaseChange : Aᴳ ⊗[R] R' →ₐ[R] (A ⊗[R] R')ᴳ`, KM's natural map
  (T-Q4b);
* `fixedPointsBaseChange_bijective_of_flat` — ∗ holds for flat `R'`
  (KM A7.1.3 (1): "A^G is a kernel: 0 → A^G → A → ⊕_g A via ⊕(1−g)", and flat base
  change preserves kernels) (T-Q4c);
* `fixedPointsBaseChange_bijective_of_isUnit` — ∗ holds when `#G` is invertible in
  `R` (KM A7.1.3 (4): the divided trace `T = (1/#G)·Σ_g g` exhibits `A^G` as a
  direct factor of `A`) (T-Q4d).

Source: Katz–Mazur, *Arithmetic moduli of elliptic curves*, Appendix A7 "Base-change
for rings of invariants", pp. 215–218. The étale-torsor sufficient condition
(A7.1.1/A7.1.2, via SGA III Exp. V) is deliberately not stated here — it belongs to
the free-action vocabulary (ticket T-Q2).
-/

universe u

open TensorProduct

variable {G : Type*} [Group G]
variable {R : Type u} {A : Type u} {R' : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [CommRing R'] [Algebra R R']

namespace MulSemiringAction

/-- The action of `G` on a base change `A ⊗[R] R'` through the left factor, as a
ring action (KM A7.1: "the group G acts R'-linearly on A ⊗_R R' [by g(a⊗r') =
g(a)⊗r']"). The underlying scalar action is mathlib's `TensorProduct.leftHasSMul`,
so this instance creates no diamond. -/
instance : MulSemiringAction G (A ⊗[R] R') where
  __ := TensorProduct.leftDistribMulAction
  smul_one g := by
    rw [Algebra.TensorProduct.one_def, smul_tmul', smul_one]
  smul_mul g x y := by
    induction x with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp [add_mul, h₁, h₂]
    | tmul a r =>
      induction y with
      | zero => simp
      | add y₁ y₂ h₁ h₂ => simp [mul_add, h₁, h₂]
      | tmul b s =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, smul_tmul', smul_tmul', smul_tmul',
          Algebra.TensorProduct.tmul_mul_tmul, smul_mul']

theorem smul_tmul_baseChange (g : G) (a : A) (r : R') :
    g • (a ⊗ₜ[R] r) = (g • a) ⊗ₜ[R] r :=
  smul_tmul' g a r

instance : SMulCommClass G R (A ⊗[R] R') where
  smul_comm g r x := by
    induction x with
    | zero => simp
    | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
    | tmul a s =>
      rw [smul_tmul', TensorProduct.smul_tmul', smul_tmul',
        TensorProduct.smul_tmul', smul_comm]

end MulSemiringAction

/-- **The base-change comparison map for rings of invariants** (KM A7.1: the natural
homomorphism `A^G ⊗_R R' → (A ⊗_R R')^G` whose bijectivity is the statement
`∗(A, G, R, R')`). -/
noncomputable def fixedPointsBaseChange :
    (FixedPoints.subalgebra R A G) ⊗[R] R' →ₐ[R]
      FixedPoints.subalgebra R (A ⊗[R] R') G :=
  AlgHom.codRestrict
    (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val (AlgHom.id R R'))
    (FixedPoints.subalgebra R (A ⊗[R] R') G)
    (by
      intro x
      induction x with
      | zero => exact Subalgebra.zero_mem _
      | add x₁ x₂ h₁ h₂ => simpa using Subalgebra.add_mem _ h₁ h₂
      | tmul a r =>
        intro g
        rw [Algebra.TensorProduct.map_tmul, MulSemiringAction.smul_tmul_baseChange]
        exact congrArg (· ⊗ₜ[R] _) (congrArg _ (a.2 g)))

@[simp]
theorem fixedPointsBaseChange_tmul (a : FixedPoints.subalgebra R A G) (r : R') :
    (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') (a ⊗ₜ[R] r) : A ⊗[R] R') =
      (a : A) ⊗ₜ[R] r := rfl

/-- **∗(A, G, R, R') holds for flat R'** (KM A7.1.3 (1)): the comparison map is
bijective when `R'` is flat over `R`. -/
theorem fixedPointsBaseChange_bijective_of_flat [Finite G] [Module.Flat R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  sorry

/-- **∗(A, G, R, R') holds when `#G` is invertible in `R`** (KM A7.1.3 (4)): the
comparison map is bijective — via the divided trace `T = (1/#G)·Σ_g g`, which
exhibits `A^G` as a direct `R`-module factor of `A`. -/
theorem fixedPointsBaseChange_bijective_of_isUnit [Finite G]
    (h : IsUnit ((Nat.card G : ℕ) : R)) :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  sorry
