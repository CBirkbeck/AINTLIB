import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Flat
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

section RingCriterion

open IsLocalRing TensorProduct

variable {A R T : Type u} [CommRing A] [CommRing R] [CommRing T]
  [Algebra A R] [Algebra A T] [Algebra R T] [IsScalarTower A R T]

/-- The canonical inclusion of the fibre rings over a prime `q ⊆ A`:
`κ(q) ⊗[A] R → κ(q) ⊗[A] T` (mathlib's `Algebra.TensorProduct.lTensor`). -/
noncomputable abbrev fiberInclusion (q : Ideal A) [q.IsPrime] :
    (q.ResidueField ⊗[A] R) →ₐ[q.ResidueField] (q.ResidueField ⊗[A] T) :=
  Algebra.TensorProduct.lTensor (S := q.ResidueField) q.ResidueField
    (IsScalarTower.toAlgHom A R T)

/-- The residue field of a prime `q ⊆ A` maps to any `A`-algebra quotient in which
`q` dies and the complement of `q` is inverted — for us, `B ⧸ q·B` with `B` local and
`q = (algebraMap A B)⁻¹ 𝔪_B`. -/
noncomputable def residueFieldToQuotient {B : Type u} [CommRing B]
    [Algebra A B] (q : Ideal A) [q.IsPrime]
    (hq : ∀ a : A, a ∉ q → IsUnit (Ideal.Quotient.mk (q.map (algebraMap A B))
      (algebraMap A B a))) :
    q.ResidueField →+* B ⧸ q.map (algebraMap A B) := by
  refine Ideal.Quotient.lift _ (IsLocalization.lift (M := q.primeCompl)
    (g := (Ideal.Quotient.mk (q.map (algebraMap A B))).comp (algebraMap A B)) ?_) ?_
  · exact fun s => hq s.1 s.2
  · intro x hx
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
    induction hx using Submodule.span_induction with
    | mem x hxmem =>
      obtain ⟨a, ha, rfl⟩ := hxmem
      rw [IsLocalization.lift_eq, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul b x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

@[simp]
lemma residueFieldToQuotient_algebraMap {B : Type u} [CommRing B]
    [Algebra A B] (q : Ideal A) [q.IsPrime] (hq) (a : A) :
    residueFieldToQuotient (A := A) (B := B) q hq (algebraMap A q.ResidueField a)
      = Ideal.Quotient.mk (q.map (algebraMap A B)) (algebraMap A B a) := by
  have h1 : algebraMap A q.ResidueField a
      = IsLocalRing.residue _ (algebraMap A (Localization.AtPrime q) a) := rfl
  rw [h1, residueFieldToQuotient]
  exact IsLocalization.lift_eq _ a

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Fibre-flatness base change.** If the fibre map `κ(q) ⊗[A] R → κ(q) ⊗[A] T` is
flat and `D` is a `κ(q) ⊗[A] R`-algebra, then `D ⊗[R] T` is flat over `D`. This is the
transfer of the fibre hypothesis to the quotients of localizations that the local
engine consumes. -/
theorem flat_baseChange_of_fiberInclusion_flat (q : Ideal A) [q.IsPrime]
    (hfib : RingHom.Flat (fiberInclusion (R := R) (T := T) q).toRingHom)
    (D : Type u) [CommRing D] [Algebra (q.ResidueField ⊗[A] R) D]
    [Algebra R D] [IsScalarTower R (q.ResidueField ⊗[A] R) D] :
    Module.Flat D (D ⊗[R] T) := by
  set K := q.ResidueField
  -- flatness of `κ⊗T` over `κ⊗R` (through the `fiberInclusion` algebra structure)
  letI : Algebra (K ⊗[A] R) (K ⊗[A] T) :=
    (fiberInclusion (R := R) (T := T) q).toRingHom.toAlgebra
  haveI hKT : Module.Flat (K ⊗[A] R) (K ⊗[A] T) := hfib
  -- the pushout cancellation `(κ⊗R) ⊗[R] T ≃ₐ[κ⊗R] κ⊗T`
  let e : (K ⊗[A] T) ≃ₐ[K ⊗[A] R] ((K ⊗[A] R) ⊗[R] T) :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg A K R (K ⊗[A] R) T).symm
      commutes' := fun x =>
        congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor A R T K) x) }
  haveI hKRT : Module.Flat (K ⊗[A] R) ((K ⊗[A] R) ⊗[R] T) :=
    Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  -- base change along `κ⊗R → D`, then cancel
  haveI : Module.Flat D (D ⊗[K ⊗[A] R] ((K ⊗[A] R) ⊗[R] T)) :=
    Module.Flat.baseChange (K ⊗[A] R) D ((K ⊗[A] R) ⊗[R] T)
  exact Module.Flat.of_linearEquiv
    (AlgebraTensorModule.cancelBaseChange R (K ⊗[A] R) D D T).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The fibrewise flatness criterion, ring level.** Let `A → R → T` with `T` a
finitely presented `R`-module, flat over `A`. If for every prime `q ⊆ A` the fibre map
`κ(q) ⊗[A] R → κ(q) ⊗[A] T` is flat, then `T` is flat over `R`. (The module-finite
case of the critère de platitude par fibres, EGA IV 11.3.10; no noetherian
hypotheses.) -/
theorem flat_of_fibre_flat_of_finitePresentation
    [Module.FinitePresentation R T] [Module.Flat A T]
    (hfib : ∀ (q : Ideal A) [q.IsPrime],
      RingHom.Flat (fiberInclusion (R := R) (T := T) q).toRingHom) :
    Module.Flat R T := by
  -- flatness is local at the maximal ideals of `R`
  refine Module.flat_of_localized_maximal T fun P hP => ?_
  haveI : P.IsPrime := hP.isPrime
  -- the localized RING `T_P` (localization of `T` at the image submonoid)
  set Sub : Submonoid T := Algebra.algebraMapSubmonoid T P.primeCompl with hSubdef
  set B := Localization.AtPrime P with hBdef
  set CP := Localization Sub with hCPdef
  -- `CP` is the localized module of `T` at `P.primeCompl`
  haveI hlocmod : IsLocalizedModule P.primeCompl
      ((IsScalarTower.toAlgHom R T CP).toLinearMap) :=
    (isLocalizedModule_iff_isLocalization).mpr (Localization.isLocalization)
  -- transfer target: it suffices to prove flatness of `CP` over `R`
  have hCPflat : Module.Flat R CP := by
    haveI hRB : Module.Flat R B := IsLocalization.flat B P.primeCompl
    -- `A`-algebra tower structures (the Ore instances give `Algebra A B`, `Algebra A CP`)
    haveI hART : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
    haveI hATC : IsScalarTower A T CP := IsScalarTower.of_algebraMap_eq' rfl
    haveI hABC : IsScalarTower A B CP := IsScalarTower.of_algebraMap_eq' <| by
      ext a
      rw [RingHom.comp_apply,
        show algebraMap A B a = algebraMap R B (algebraMap A R a) from rfl,
        show (algebraMap B CP : B →+* CP)
          = IsLocalization.map (T := Sub) CP (algebraMap R T)
            (show P.primeCompl ≤ Sub.comap (algebraMap R T) from
              Submonoid.le_comap_map _) from rfl,
        IsLocalization.map_eq,
        show algebraMap A CP a = algebraMap T CP (algebraMap A T a) from rfl,
        IsScalarTower.algebraMap_apply A R T a]
    -- the pullback prime of `A`
    set q : Ideal A := (IsLocalRing.maximalIdeal B).comap (algebraMap A B) with hqdef
    haveI hqprime : q.IsPrime := Ideal.IsPrime.comap _
    have hqB : q.map (algebraMap A B) ≤ IsLocalRing.maximalIdeal B := Ideal.map_comap_le
    -- ENGINE input (1): finite presentation of `CP` over `B`
    haveI hfp : Module.FinitePresentation B CP := by
      have hbc : IsBaseChange B ((IsScalarTower.toAlgHom R T CP).toLinearMap) :=
        (isLocalizedModule_iff_isBaseChange P.primeCompl B _).mp hlocmod
      exact FinitePresentation.of_isBaseChange _ hbc
    -- ENGINE input (2): `A`-flatness of `CP` (ring composite `A → T → CP`)
    haveI hACP : Module.Flat A CP := by
      have h1 : RingHom.Flat (algebraMap A T) := by
        rw [RingHom.flat_algebraMap_iff]; infer_instance
      have h2 : RingHom.Flat (algebraMap T CP) := by
        rw [RingHom.flat_algebraMap_iff]
        exact IsLocalization.flat CP Sub
      have h3 : RingHom.Flat ((algebraMap T CP).comp (algebraMap A T)) :=
        RingHom.Flat.comp h1 h2
      have heq : (algebraMap T CP).comp (algebraMap A T) = algebraMap A CP := by
        rw [← IsScalarTower.algebraMap_eq A T CP]
      rw [heq] at h3
      rwa [RingHom.flat_algebraMap_iff] at h3
    -- ENGINE input (3): fibre flatness over `B ⧸ qB`
    haveI hfibB : Module.Flat (B ⧸ q.map (algebraMap A B))
        ((B ⧸ q.map (algebraMap A B)) ⊗[B] CP) := by
      set BQ := B ⧸ q.map (algebraMap A B) with hBQdef
      -- the `κ(q) ⊗[A] R`-algebra structure on `BQ`
      have hunit : ∀ a : A, a ∉ q →
          IsUnit (Ideal.Quotient.mk (q.map (algebraMap A B)) (algebraMap A B a)) := by
        intro a ha
        have : IsUnit (algebraMap A B a) := by
          rw [← IsLocalRing.notMem_maximalIdeal (R := B)]
          exact fun hmem => ha (Ideal.mem_comap.mpr hmem)
        exact this.map _
      letI : Algebra q.ResidueField BQ := (residueFieldToQuotient q hunit).toAlgebra
      haveI : IsScalarTower A q.ResidueField BQ := IsScalarTower.of_algebraMap_eq' <| by
        ext a
        rw [RingHom.comp_apply,
          show (algebraMap q.ResidueField BQ : q.ResidueField →+* BQ)
            = residueFieldToQuotient q hunit from rfl,
          residueFieldToQuotient_algebraMap,
          IsScalarTower.algebraMap_apply A B BQ]
        rfl
      letI : Algebra (q.ResidueField ⊗[A] R) BQ :=
        (Algebra.TensorProduct.lift
          (IsScalarTower.toAlgHom A q.ResidueField BQ)
          (IsScalarTower.toAlgHom A R BQ)
          (fun _ _ => Commute.all _ _)).toRingHom.toAlgebra
      haveI : IsScalarTower R (q.ResidueField ⊗[A] R) BQ :=
        IsScalarTower.of_algebraMap_eq' <| by
          ext r
          show algebraMap R BQ r = (Algebra.TensorProduct.lift
            (IsScalarTower.toAlgHom A q.ResidueField BQ)
            (IsScalarTower.toAlgHom A R BQ)
            (fun _ _ => Commute.all _ _)) ((1 : q.ResidueField) ⊗ₜ[A] r)
          rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
          rfl
      -- fibre-flatness base-changed to `BQ`, then transferred through `CP ≅ B ⊗[R] T`
      haveI hDT : Module.Flat BQ (BQ ⊗[R] T) :=
        flat_baseChange_of_fiberInclusion_flat (A := A) q (hfib q) BQ
      -- `BQ ⊗[B] CP ≃ BQ ⊗[B] (B ⊗[R] T) ≃ BQ ⊗[R] T`
      have hbc : IsBaseChange B ((IsScalarTower.toAlgHom R T CP).toLinearMap) :=
        (isLocalizedModule_iff_isBaseChange P.primeCompl B _).mp hlocmod
      have e1 : CP ≃ₗ[B] B ⊗[R] T := hbc.equiv.symm
      have e2 : BQ ⊗[B] CP ≃ₗ[BQ] BQ ⊗[B] (B ⊗[R] T) :=
        AlgebraTensorModule.congr (LinearEquiv.refl BQ BQ) e1
      have e3 : BQ ⊗[B] (B ⊗[R] T) ≃ₗ[BQ] BQ ⊗[R] T :=
        AlgebraTensorModule.cancelBaseChange R B BQ BQ T
      exact Module.Flat.of_linearEquiv (e2.trans e3)
    -- the ENGINE fires
    haveI hfree : Module.Free B CP :=
      free_of_flat_of_fibre_flat (A := A) (B := B) (M := CP) q hqB hfibB
    haveI : Module.Flat B CP := inferInstance
    exact Module.Flat.trans R B CP
  -- conclude via the localized-module transfer
  have e := IsLocalizedModule.linearEquiv P.primeCompl
    (LocalizedModule.mkLinearMap P.primeCompl T)
    ((IsScalarTower.toAlgHom R T CP).toLinearMap)
  exact Module.Flat.of_linearEquiv e

end RingCriterion

end ModularCurves
