/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q4 (KM A7 appendix).
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.SetTheory.Cardinal.Finite

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
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]
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

omit [SMulCommClass G R A] in
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
        exact congrArg (fun y => y ⊗ₜ[R] ((AlgHom.id R R') r)) (a.2 g))

@[simp]
theorem fixedPointsBaseChange_tmul (a : FixedPoints.subalgebra R A G) (r : R') :
    (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') (a ⊗ₜ[R] r) : A ⊗[R] R') =
      (a : A) ⊗ₜ[R] r := by
  simp [fixedPointsBaseChange]

/-- The "difference" map whose kernel is the ring of invariants: KM A7.1.3 (1),
"A^G is a kernel: 0 → A^G → A → ⊕_g A via ⊕(1−g)". -/
private noncomputable def invariantsDelta (G : Type*) [Group G] (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [MulSemiringAction G A]
    [SMulCommClass G R A] [SMulCommClass R G A] : A →ₗ[R] (G → A) :=
  LinearMap.pi fun g => DistribSMul.toLinearMap R A g - LinearMap.id

private theorem invariantsDelta_apply (g : G) (x : A) :
    invariantsDelta G R A x g = g • x - x := rfl

private theorem exact_subtype_invariantsDelta :
    Function.Exact (FixedPoints.subalgebra R A G).toSubmodule.subtype
      (invariantsDelta G R A) := by
  intro y
  constructor
  · intro hy
    refine ⟨⟨y, fun g => ?_⟩, rfl⟩
    have h1 := congrFun hy g
    rw [invariantsDelta_apply] at h1
    exact sub_eq_zero.mp h1
  · rintro ⟨⟨x, hx⟩, rfl⟩
    funext g
    rw [invariantsDelta_apply]
    exact sub_eq_zero.mpr (hx g)

omit [SMulCommClass R G A] in
/-- The underlying map of the comparison hom is the tensored inclusion. -/
private theorem map_val_id_eq_rTensor
    (x : (FixedPoints.subalgebra R A G) ⊗[R] R') :
    (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
      (AlgHom.id R R')) x =
    LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype x := by
  induction x with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
  | tmul a r => rfl

/-- **∗(A, G, R, R') holds for flat R'** (KM A7.1.3 (1)): the comparison map is
bijective when `R'` is flat over `R`. -/
theorem fixedPointsBaseChange_bijective_of_flat [Finite G] [Module.Flat R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  classical
  cases nonempty_fintype G
  have hval : Function.Injective
      ⇑(LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  constructor
  · -- injectivity
    intro x₁ x₂ h12
    have h13 := congrArg Subtype.val h12
    rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₁ : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₁ from rfl,
      show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₂ : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₂ from rfl, map_val_id_eq_rTensor, map_val_id_eq_rTensor] at h13
    exact hval h13
  · -- surjectivity
    rintro ⟨z, hz⟩
    -- the tensored difference map kills `z`
    have hεz : LinearMap.rTensor R' (invariantsDelta G R A) z = 0 := by
      have hpi : ∀ (x : A ⊗[R] R') (g : G),
          TensorProduct.piLeft (R := R) (M := fun _ : G => A) (N := R')
            (LinearMap.rTensor R' (invariantsDelta G R A) x) g =
            g • x - x := by
        intro x
        induction x with
        | zero => intro g; simp
        | add x₁ x₂ h₁ h₂ =>
          intro g
          rw [map_add, map_add]
          simp only [Pi.add_apply]
          rw [h₁ g, h₂ g, smul_add]
          abel
        | tmul a r =>
          intro g
          rw [LinearMap.rTensor_tmul]
          simp only [TensorProduct.piLeft, LinearEquiv.trans_apply,
            TensorProduct.comm_tmul, TensorProduct.piRight_apply,
            TensorProduct.piRightHom_tmul, LinearEquiv.piCongrRight_apply]
          rw [invariantsDelta_apply, TensorProduct.sub_tmul,
            MulSemiringAction.smul_tmul_baseChange]
      have h0 : TensorProduct.piLeft (R := R) (M := fun _ : G => A) (N := R')
          (LinearMap.rTensor R' (invariantsDelta G R A) z) = 0 := by
        funext g
        rw [hpi z g]
        show g • z - z = 0
        rw [sub_eq_zero]
        exact hz g
      have h0' := congrArg (TensorProduct.piLeft (R := R) (M := fun _ : G => A) (N := R')).symm h0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at h0'
    obtain ⟨w, hw⟩ := ((Module.Flat.rTensor_exact R'
      (exact_subtype_invariantsDelta (G := G) (R := R) (A := A))) z).mp hεz
    refine ⟨w, Subtype.ext ?_⟩
    rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') w : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) w from rfl, map_val_id_eq_rTensor]
    exact hw

/-- **∗(A, G, R, R') holds when `#G` is invertible in `R`** (KM A7.1.3 (4)): the
comparison map is bijective — via the divided trace `T = (1/#G)·Σ_g g`, which
exhibits `A^G` as a direct `R`-module factor of `A`. -/
theorem fixedPointsBaseChange_bijective_of_isUnit [Finite G]
    (h : IsUnit ((Nat.card G : ℕ) : R)) :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  classical
  cases nonempty_fintype G
  obtain ⟨u, hu⟩ := h
  have hcard : ((Fintype.card G : ℕ) : R) = (u : R) := by
    rw [hu, Nat.card_eq_fintype_card]
  -- the divided trace
  set Tfull : A →ₗ[R] A :=
    ((u⁻¹ : Rˣ) : R) • ∑ g : G, DistribSMul.toLinearMap R A g with hTfull
  have hTapp : ∀ x : A, Tfull x = ((u⁻¹ : Rˣ) : R) • ∑ g : G, g • x := by
    intro x
    rw [hTfull]
    simp [DistribSMul.toLinearMap]
  have hTmem : ∀ x : A, Tfull x ∈ FixedPoints.subalgebra R A G := by
    intro x g₀
    show g₀ • Tfull x = Tfull x
    rw [hTapp, smul_comm g₀, Finset.smul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ (fun g => by
      simp [mul_smul])
  have hTr : ∀ s : FixedPoints.subalgebra R A G, Tfull (s : A) = (s : A) := by
    intro s
    rw [hTapp, Finset.sum_congr rfl (fun g _ => s.2 g), Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul, hcard]
    simp
  -- the tensored trace averages the tensor action
  have htensor : ∀ x : A ⊗[R] R',
      LinearMap.rTensor R' Tfull x = ((u⁻¹ : Rˣ) : R) • ∑ g : G, g • x := by
    intro x
    induction x with
    | zero => simp
    | add x₁ x₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, ← smul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun g _ => (smul_add g x₁ x₂).symm
    | tmul a r =>
      rw [LinearMap.rTensor_tmul, hTapp, ← TensorProduct.smul_tmul',
        TensorProduct.sum_tmul]
      congr 1
  have hproj : ∀ z : A ⊗[R] R', (∀ g : G, g • z = z) →
      LinearMap.rTensor R' Tfull z = z := by
    intro z hz
    rw [htensor, Finset.sum_congr rfl (fun g _ => hz g), Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul, hcard]
    simp
  -- the corestricted trace is a retraction of the inclusion
  set T : A →ₗ[R] (FixedPoints.subalgebra R A G).toSubmodule :=
    LinearMap.codRestrict (FixedPoints.subalgebra R A G).toSubmodule Tfull hTmem
    with hT
  have hcompleft : (FixedPoints.subalgebra R A G).toSubmodule.subtype ∘ₗ T
      = Tfull := by
    ext x
    rfl
  have hTsub : T ∘ₗ (FixedPoints.subalgebra R A G).toSubmodule.subtype
      = LinearMap.id := by
    ext s
    show Tfull (s : A) = (s : A)
    exact hTr s
  have hval : Function.Injective
      ⇑(LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype) := by
    have hLI : (LinearMap.rTensor R' T).comp
        (LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype) =
        LinearMap.id := by
      rw [← LinearMap.rTensor_comp, hTsub, LinearMap.rTensor_id]
    intro x y hxy
    have h2 := congrArg (LinearMap.rTensor R' T) hxy
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, hLI, LinearMap.id_apply,
      LinearMap.id_apply] at h2
  constructor
  · -- injectivity
    intro x₁ x₂ h12
    have h13 := congrArg Subtype.val h12
    rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₁ :
          A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₁ from rfl,
      show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₂ :
          A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₂ from rfl,
      map_val_id_eq_rTensor, map_val_id_eq_rTensor] at h13
    exact hval h13
  · -- surjectivity: the tensored trace provides a preimage of any fixed element
    rintro ⟨z, hz⟩
    refine ⟨LinearMap.rTensor R' T z, Subtype.ext ?_⟩
    rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')
          (LinearMap.rTensor R' T z) : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) (LinearMap.rTensor R' T z) from rfl,
      map_val_id_eq_rTensor, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      hcompleft]
    exact hproj z (fun g => hz g)
