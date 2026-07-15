import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The fibrewise flatness criterion for finitely presented modules over a local ring

**The engine of BB-FLAT.** Let `A → B` be a ring map with `B` local, `M` a finitely
presented `B`-module, and `q ⊆ A` an ideal with `q·B ⊆ 𝔪_B`. If

* `M` is **flat over `A`** (restriction of scalars), and
* the **fibre** `(B/qB) ⊗[B] M` is flat over `B/qB`,

then `M` is **free** (hence flat) over `B`.

This is the module-finite case of the *critère de platitude par fibres*
(EGA IV 11.3.10; the module-finite shadow of Stacks 00MP): because `M` is finitely
presented over `B` itself, the general criterion's Artin–Rees/local-criterion machinery
collapses — the classical *élimination des Tor* ladder reduces the mathlib hypothesis
`𝔪 ⊗ M → M` injective (`Module.free_of_maximalIdeal_rTensor_injective`) to the two
flatness inputs:

1. `q ⊗[A] M → M` is injective (`A`-flatness), and the comparison
   `q ⊗[A] M → (q·B) ⊗[B] M` is *surjective*, so `(q·B) ⊗[B] M → B ⊗[B] M` is
   injective (`rTensor_subtype_map_injective_of_flat`);
2. `(𝔪/qB) ⊗[B] M → (B/qB) ⊗[B] M` is injective — fibre flatness, transported through
   the base-change cancellation `X ⊗[B] M ≃ X ⊗[B/qB] ((B/qB) ⊗[B] M)`;
3. the two-out-of-three chase along `0 → qB → 𝔪 → 𝔪/qB → 0` concludes
   (`maximalIdeal_rTensor_injective_of_flat_of_fibre_flat`).

No noetherian hypotheses, no Buchsbaum–Eisenbud/flat-locus theory, no Tor modules.
Everything is elementary tensor algebra on top of mathlib's `LocalRing/Module` endgame.
-/

open TensorProduct

universe u

namespace ModularCurves

section Comparison

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- The comparison map `q ⊗[A] M → (q·B) ⊗[B] M`, `a ⊗ m ↦ (algebraMap a) ⊗ m`. -/
noncomputable def idealMapTensorComparison (q : Ideal A) :
    q ⊗[A] M →ₗ[A] (q.map (algebraMap A B)) ⊗[B] M :=
  TensorProduct.lift
    { toFun := fun a =>
        ((TensorProduct.mk B (q.map (algebraMap A B)) M)
          ⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.2⟩).restrictScalars A
      map_add' := fun a b => by
        ext m
        simp only [LinearMap.coe_restrictScalars, LinearMap.add_apply,
          TensorProduct.mk_apply]
        rw [show (⟨algebraMap A B ↑(a + b), Ideal.mem_map_of_mem _ (a + b).2⟩ :
            q.map (algebraMap A B))
          = ⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.2⟩
            + ⟨algebraMap A B b, Ideal.mem_map_of_mem _ b.2⟩ from
          Subtype.ext (by simp)]
        exact TensorProduct.add_tmul _ _ _
      map_smul' := fun c a => by
        ext m
        simp only [LinearMap.coe_restrictScalars, RingHom.id_apply,
          LinearMap.smul_apply, TensorProduct.mk_apply]
        rw [show (⟨algebraMap A B ↑(c • a), Ideal.mem_map_of_mem _ (c • a).2⟩ :
            q.map (algebraMap A B))
          = (algebraMap A B c) • ⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.2⟩ from
          Subtype.ext (by simp [Algebra.smul_def])]
        rw [← TensorProduct.smul_tmul', algebraMap_smul B c] }

@[simp]
lemma idealMapTensorComparison_tmul (q : Ideal A) (a : q) (m : M) :
    idealMapTensorComparison (B := B) (M := M) q (a ⊗ₜ[A] m)
      = (⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.2⟩ :
          q.map (algebraMap A B)) ⊗ₜ[B] m := rfl

lemma idealMapTensorComparison_surjective (q : Ideal A) :
    Function.Surjective (idealMapTensorComparison (B := B) (M := M) q) := by
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
  | tmul t m =>
    obtain ⟨t, ht⟩ := t
    -- induct over the span presentation of `q.map (algebraMap A B)`,
    -- carrying the tensor slot `m` through the smul case
    have key : ∀ (t : B) (ht : t ∈ Submodule.span B ((algebraMap A B) '' (q : Set A)))
        (m : M), ∃ z, idealMapTensorComparison (B := B) (M := M) q z
          = (⟨t, ht⟩ : q.map (algebraMap A B)) ⊗ₜ[B] m := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t htmem =>
        intro m
        obtain ⟨a, haq, rfl⟩ := htmem
        exact ⟨(⟨a, haq⟩ : q) ⊗ₜ[A] m, rfl⟩
      | zero =>
        intro m
        refine ⟨0, ?_⟩
        rw [map_zero, show ((⟨(0 : B), Submodule.zero_mem _⟩ :
          q.map (algebraMap A B))) = 0 from rfl, TensorProduct.zero_tmul]
      | add t₁ t₂ h₁ h₂ ih₁ ih₂ =>
        intro m
        obtain ⟨z₁, hz₁⟩ := ih₁ m
        obtain ⟨z₂, hz₂⟩ := ih₂ m
        refine ⟨z₁ + z₂, ?_⟩
        rw [map_add, hz₁, hz₂, show ((⟨t₁ + t₂, Submodule.add_mem _ h₁ h₂⟩ :
          q.map (algebraMap A B))) = ⟨t₁, h₁⟩ + ⟨t₂, h₂⟩ from rfl,
          TensorProduct.add_tmul]
      | smul b t ht ih =>
        intro m
        obtain ⟨z, hz⟩ := ih (b • m)
        refine ⟨z, hz.trans ?_⟩
        rw [show ((⟨b • t, Submodule.smul_mem _ b ht⟩ :
          q.map (algebraMap A B))) = b • ⟨t, ht⟩ from rfl]
        exact (TensorProduct.smul_tmul b _ m).symm
    obtain ⟨z, hz⟩ := key t ht m
    exact ⟨z, hz⟩

/-- **Step (2) of the élimination des Tor**: if `M` is `A`-flat then
`(q·B) ⊗[B] M → B ⊗[B] M` is injective — the `A`-side injectivity
`q ⊗[A] M ↪ A ⊗[A] M` transfers along the surjective comparison map. -/
theorem rTensor_subtype_map_injective_of_flat [Module.Flat A M] (q : Ideal A) :
    Function.Injective
      (LinearMap.rTensor M (q.map (algebraMap A B)).subtype) := by
  have hcomp : ∀ z : q ⊗[A] M,
      (TensorProduct.lid B M).toLinearMap
        (LinearMap.rTensor M (q.map (algebraMap A B)).subtype
          (idealMapTensorComparison q z))
      = (TensorProduct.lid A M).toLinearMap
          (LinearMap.rTensor M q.subtype z) := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      simp only [idealMapTensorComparison_tmul, LinearMap.rTensor_tmul,
        Submodule.coe_subtype, LinearEquiv.coe_coe, TensorProduct.lid_tmul]
      exact algebraMap_smul B (a : A) m
  have hAinj : Function.Injective
      ((TensorProduct.lid A M).toLinearMap.comp
        (LinearMap.rTensor M q.subtype)) := by
    refine (TensorProduct.lid A M).injective.comp ?_
    exact Module.Flat.rTensor_preserves_injective_linearMap q.subtype
      Subtype.val_injective
  intro x y hxy
  obtain ⟨x', rfl⟩ := idealMapTensorComparison_surjective (M := M) q x
  obtain ⟨y', rfl⟩ := idealMapTensorComparison_surjective (M := M) q y
  have heq : ((TensorProduct.lid A M).toLinearMap.comp
        (LinearMap.rTensor M q.subtype)) x'
      = ((TensorProduct.lid A M).toLinearMap.comp
        (LinearMap.rTensor M q.subtype)) y' := by
    simp only [LinearMap.comp_apply]
    rw [← hcomp, ← hcomp, hxy]
  rw [hAinj heq]

end Comparison

section Engine

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

open IsLocalRing

/-- **The fibrewise criterion, local engine (élimination des Tor).** Over a local
ring `B`, if `M` is flat over `A`, `q·B ⊆ 𝔪`, and the fibre `(B/qB) ⊗[B] M` is flat
over `B/qB`, then `𝔪 ⊗[B] M → B ⊗[B] M` is injective. -/
theorem maximalIdeal_rTensor_injective_of_flat_of_fibre_flat
    [IsLocalRing B] [Module.Flat A M] (q : Ideal A)
    (hq : q.map (algebraMap A B) ≤ maximalIdeal B)
    (hfib : Module.Flat (B ⧸ q.map (algebraMap A B))
      ((B ⧸ q.map (algebraMap A B)) ⊗[B] M)) :
    Function.Injective (LinearMap.rTensor M (maximalIdeal B).subtype) := by
  set q' : Ideal B := q.map (algebraMap A B) with hq'def
  -- the image ideal `𝔪/q'` in the fibre ring `B ⧸ q'`
  set mq : Ideal (B ⧸ q') := (maximalIdeal B).map (Ideal.Quotient.mk q') with hmqdef
  -- the B-linear restriction `𝔪 → 𝔪/q'` of the quotient map
  have hmem : ∀ z : maximalIdeal B,
      q'.mkQ ((maximalIdeal B).subtype z) ∈ mq.restrictScalars B := fun z =>
    Ideal.mem_map_of_mem _ z.2
  set mkRestr : maximalIdeal B →ₗ[B] (mq.restrictScalars B) :=
    LinearMap.codRestrict (mq.restrictScalars B)
      (q'.mkQ.comp (maximalIdeal B).subtype) hmem with hmkRestrdef
  -- the exact sequence `q' → 𝔪 → 𝔪/q' → 0` of B-modules
  have hexact : Function.Exact (Submodule.inclusion hq) mkRestr := by
    intro z
    constructor
    · intro hz
      have hz' : (z : B) ∈ q' := by
        have hval := congrArg Subtype.val hz
        rw [show (mkRestr z : B ⧸ q') = q'.mkQ (z : B) from rfl] at hval
        rwa [show ((0 : mq.restrictScalars B) : B ⧸ q') = 0 from rfl,
          Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hval
      exact ⟨⟨(z : B), hz'⟩, Subtype.ext rfl⟩
    · rintro ⟨w, rfl⟩
      refine Subtype.ext ?_
      rw [show (mkRestr (Submodule.inclusion hq w) : B ⧸ q')
          = q'.mkQ (w : B) from rfl]
      rw [show ((0 : mq.restrictScalars B) : B ⧸ q') = 0 from rfl,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact w.2
  have hsurjR : Function.Surjective mkRestr := by
    rintro ⟨w, hw⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      Ideal.Quotient.mk_surjective).mp hw
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  -- tensor the sequence with M (right exactness needs no flatness)
  have hexactT : Function.Exact
      (LinearMap.rTensor M (Submodule.inclusion hq))
      (LinearMap.rTensor M mkRestr) :=
    rTensor_exact M hexact hsurjR
  -- the fibre-side inclusion, tensored: injective by fibre flatness + cancellation
  set incl : (mq.restrictScalars B) →ₗ[B] (B ⧸ q') :=
    (mq.subtype).restrictScalars B with hincldef
  have hγ : Function.Injective (LinearMap.rTensor M incl) := by
    haveI : Module.Flat (B ⧸ q') ((B ⧸ q') ⊗[B] M) := hfib
    let e₁ := (AlgebraTensorModule.cancelBaseChange B (B ⧸ q') (B ⧸ q') mq M).symm
    let e₂ := (AlgebraTensorModule.cancelBaseChange B (B ⧸ q') (B ⧸ q') (B ⧸ q') M).symm
    have hsqL : (e₂.toLinearMap.restrictScalars B).comp (LinearMap.rTensor M incl)
        = ((LinearMap.rTensor ((B ⧸ q') ⊗[B] M) mq.subtype).restrictScalars B).comp
            (e₁.toLinearMap.restrictScalars B) := by
      apply TensorProduct.ext'
      intro t m
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
        LinearEquiv.coe_coe, LinearMap.rTensor_tmul]
      simp only [e₁, e₂, hincldef,
        AlgebraTensorModule.cancelBaseChange_symm_tmul]
      rfl
    have hsq : ∀ z : (mq.restrictScalars B) ⊗[B] M,
        e₂ (LinearMap.rTensor M incl z)
          = LinearMap.rTensor ((B ⧸ q') ⊗[B] M) mq.subtype (e₁ z) :=
      fun z => LinearMap.congr_fun hsqL z
    intro x y hxy
    have hmid : LinearMap.rTensor ((B ⧸ q') ⊗[B] M) mq.subtype (e₁ x)
        = LinearMap.rTensor ((B ⧸ q') ⊗[B] M) mq.subtype (e₁ y) := by
      rw [← hsq, ← hsq, hxy]
    exact e₁.injective (Module.Flat.rTensor_preserves_injective_linearMap
      (M := (B ⧸ q') ⊗[B] M) mq.subtype Subtype.val_injective hmid)
  -- the commuting square with the quotient map on the B-side
  have hsquare : ∀ z : (maximalIdeal B) ⊗[B] M,
      LinearMap.rTensor M incl (LinearMap.rTensor M mkRestr z)
        = LinearMap.rTensor M q'.mkQ
            (LinearMap.rTensor M (maximalIdeal B).subtype z) := by
    intro z
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp]
    rfl
  -- the chase
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : LinearMap.rTensor M mkRestr x = 0 := by
    apply hγ
    rw [hsquare x, hx, map_zero, map_zero]
  obtain ⟨y, rfl⟩ := (hexactT x).mp h1
  have h2 : LinearMap.rTensor M (q'.subtype) y = 0 := by
    have hcomp : (maximalIdeal B).subtype.comp (Submodule.inclusion hq)
        = q'.subtype := rfl
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp] at hx
    exact hx
  have hy0 : y = 0 := by
    have hinj := rTensor_subtype_map_injective_of_flat (A := A) (B := B) (M := M) q
    exact (injective_iff_map_eq_zero _).mp hinj y h2
  rw [hy0, map_zero]

/-- **The fibrewise criterion for finitely presented modules over a local ring.**
`A → B` with `B` local, `M` a finitely presented `B`-module which is flat over `A`;
if the fibre `(B/qB) ⊗[B] M` is flat over `B/qB` for an ideal `q ⊆ A` with
`q·B ⊆ 𝔪_B`, then `M` is **free** over `B`. (The module-finite case of the critère
de platitude par fibres, EGA IV 11.3.10; no noetherian hypotheses.) -/
theorem free_of_flat_of_fibre_flat
    [IsLocalRing B] [Module.FinitePresentation B M] [Module.Flat A M] (q : Ideal A)
    (hq : q.map (algebraMap A B) ≤ maximalIdeal B)
    (hfib : Module.Flat (B ⧸ q.map (algebraMap A B))
      ((B ⧸ q.map (algebraMap A B)) ⊗[B] M)) :
    Module.Free B M :=
  Module.free_of_maximalIdeal_rTensor_injective
    (maximalIdeal_rTensor_injective_of_flat_of_fibre_flat (A := A) q hq hfib)

end Engine

end ModularCurves
