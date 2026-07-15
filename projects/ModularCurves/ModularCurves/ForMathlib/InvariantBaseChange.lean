/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q4 (KM A7 appendix).
-/
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps
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

universe u v

open TensorProduct

variable {G : Type*} [Group G]
variable {R : Type v} {A : Type u} {R' : Type u}
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
private noncomputable def invariantsDelta (G : Type*) [Group G] (R : Type v) (A : Type u)
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

/-- **Injectivity of ∗ reduces to injectivity of the tensored inclusion** (KM A7.1.3):
the comparison map `fixedPointsBaseChange` is injective as soon as the base change
`rTensor R'` of the inclusion `A^G ↪ A` is injective. Common to every sufficient
condition on `R'` (flatness, `#G` invertible, …). -/
private theorem fixedPointsBaseChange_injective_of_rTensor_subtype_injective
    (hval : Function.Injective
      ⇑(LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype)) :
    Function.Injective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  intro x₁ x₂ h12
  have h13 := congrArg Subtype.val h12
  rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₁ : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₁ from rfl,
      show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x₂ : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) x₂ from rfl,
      map_val_id_eq_rTensor, map_val_id_eq_rTensor] at h13
  exact hval h13

/-- The **divided trace** `c · Σ_{g ∈ G} g` on `A`, an `R`-linear endomorphism.
For `c = 1/#G` (available when `#G` is invertible in `R`) this is the averaging
operator of KM A7.1.3 (4), which retracts the inclusion `A^G ↪ A`. -/
private noncomputable def dividedTrace [Fintype G] (c : R) : A →ₗ[R] A :=
  c • ∑ g : G, DistribSMul.toLinearMap R A g

omit [SMulCommClass R G A] in
private theorem dividedTrace_apply [Fintype G] (c : R) (x : A) :
    dividedTrace (G := G) (R := R) (A := A) c x = c • ∑ g : G, g • x := by
  simp [dividedTrace, DistribSMul.toLinearMap]

omit [SMulCommClass R G A] in
/-- The divided trace lands in the invariants: `c · Σ_g g·x` is `G`-fixed. -/
private theorem dividedTrace_mem_fixedPoints [Fintype G] (c : R) (x : A) :
    dividedTrace (G := G) (R := R) (A := A) c x ∈ FixedPoints.subalgebra R A G := by
  intro g₀
  show g₀ • dividedTrace (G := G) c x = dividedTrace (G := G) c x
  rw [dividedTrace_apply, smul_comm g₀, Finset.smul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g₀) _ _ fun g => by simp [mul_smul]

omit [SMulCommClass R G A] in
/-- When `c · #G = 1`, the divided trace fixes the invariants: it is a retraction of
the inclusion `A^G ↪ A` (KM A7.1.3 (4), exhibiting `A^G` as a direct `R`-factor). -/
private theorem dividedTrace_apply_coe [Fintype G] (c : R)
    (hc : c * ((Fintype.card G : ℕ) : R) = 1) (s : FixedPoints.subalgebra R A G) :
    dividedTrace (G := G) (R := R) (A := A) c (s : A) = (s : A) := by
  rw [dividedTrace_apply, Finset.sum_congr rfl fun g _ => s.2 g, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

/-- The base change (`rTensor R'`) of the divided trace averages the tensor action:
`(T ⊗ id) x = c · Σ_g g·x` for the left-factor `G`-action on `A ⊗ R'`. -/
private theorem rTensor_dividedTrace [Fintype G] (c : R) (x : A ⊗[R] R') :
    LinearMap.rTensor R' (dividedTrace (G := G) (R := R) (A := A) c) x
      = c • ∑ g : G, g • x := by
  induction x with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, h₁, h₂, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun g _ => (smul_add g x₁ x₂).symm
  | tmul a r =>
    rw [LinearMap.rTensor_tmul, dividedTrace_apply, ← TensorProduct.smul_tmul',
      TensorProduct.sum_tmul]
    congr 1

/-- On a `G`-fixed element of `A ⊗ R'`, the base-changed divided trace (with
`c · #G = 1`) acts as the identity — the source of surjectivity of ∗ (KM A7.1.3 (4)). -/
private theorem rTensor_dividedTrace_apply_of_forall_smul_eq [Fintype G] (c : R)
    (hc : c * ((Fintype.card G : ℕ) : R) = 1) (z : A ⊗[R] R')
    (hz : ∀ g : G, g • z = z) :
    LinearMap.rTensor R' (dividedTrace (G := G) (R := R) (A := A) c) z = z := by
  rw [rTensor_dividedTrace, Finset.sum_congr rfl fun g _ => hz g, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul]

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
  set c : R := ((u⁻¹ : Rˣ) : R) with hc_def
  have hcard : ((Fintype.card G : ℕ) : R) = (u : R) := by
    rw [hu, Nat.card_eq_fintype_card]
  have hc : c * ((Fintype.card G : ℕ) : R) = 1 := by
    rw [hc_def, hcard]; exact u.inv_mul
  -- the corestricted divided trace `T` is an `R`-linear retraction of `A^G ↪ A`
  set T : A →ₗ[R] (FixedPoints.subalgebra R A G).toSubmodule :=
    LinearMap.codRestrict (FixedPoints.subalgebra R A G).toSubmodule
      (dividedTrace (G := G) c) (dividedTrace_mem_fixedPoints c)
  have hcompleft : (FixedPoints.subalgebra R A G).toSubmodule.subtype ∘ₗ T
      = dividedTrace (G := G) c := by
    ext x
    rfl
  have hTsub : T ∘ₗ (FixedPoints.subalgebra R A G).toSubmodule.subtype
      = LinearMap.id := by
    ext s
    show dividedTrace (G := G) c (s : A) = (s : A)
    exact dividedTrace_apply_coe c hc s
  constructor
  · -- injectivity: `A^G ↪ A` is a split mono, so it stays injective after base change
    refine fixedPointsBaseChange_injective_of_rTensor_subtype_injective ?_
    have hLinv : Function.LeftInverse (LinearMap.rTensor R' T)
        (LinearMap.rTensor R' (FixedPoints.subalgebra R A G).toSubmodule.subtype) := by
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hTsub, LinearMap.rTensor_id,
        LinearMap.id_apply]
    exact hLinv.injective
  · -- surjectivity: the base-changed trace `T ⊗ id` gives a preimage of any fixed element
    rintro ⟨z, hz⟩
    refine ⟨LinearMap.rTensor R' T z, Subtype.ext ?_⟩
    rw [show (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')
          (LinearMap.rTensor R' T z) : A ⊗[R] R') =
        (Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val
          (AlgHom.id R R')) (LinearMap.rTensor R' T z) from rfl,
      map_val_id_eq_rTensor, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      hcompleft]
    exact rTensor_dividedTrace_apply_of_forall_smul_eq c hc z fun g => hz g
