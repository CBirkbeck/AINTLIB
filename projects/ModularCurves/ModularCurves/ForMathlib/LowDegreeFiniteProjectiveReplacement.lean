/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import ModularCurves.ForMathlib.BaseChangeKerCoker
import ModularCurves.ForMathlib.FiniteFreeResolution

/-!
# A finite-projective replacement for a two-term complex

This file proves the amplitude `[0, 1]` module-theoretic form of Mumford,
*Abelian Varieties*, Section 5, Lemma 1. Let `f : C0 → Z1` be a map of flat
modules over a Noetherian ring. If its kernel and cokernel are finite, then it
admits a two-term replacement `KZero → KOne` with `KZero` finite projective
and `KOne` finite free. Its degree-zero kernel and degree-one cokernel agree
with those of `f` after every algebra base change.

The Noetherian hypothesis belongs only to this algebraic construction. Geometric
applications over an arbitrary base must remove it by approximation before
exposing their final statements.
-/

open Function
open CategoryTheory
open TensorProduct

universe u v

namespace ModularCurves

variable {R : Type u} [CommRing R]
variable {P Q T : Type v} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
  [Module R P] [Module R Q] [Module R T]

/-- If cycles commute with base change, then the base-changed cokernel into the old cycle
module computes degree-one homology of the base-changed short complex. -/
noncomputable def LinearMap.baseChangeHomologyOneEquiv
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : g ∘ₗ f = 0)
    (A : Type*) [CommRing A] [Algebra R A]
    (hbij : Function.Bijective (kerBaseChangeComparison A g)) :
    let hA := LinearMap.baseChange_comp_eq_zero f g h A
    let S := ShortComplex.moduleCatMk (f.baseChange A) (g.baseChange A) hA
    ((A ⊗[R] LinearMap.ker g) ⧸
        LinearMap.range ((LinearMap.codRestrictToKer f g h).baseChange A)) ≃ₗ[A]
      S.homology := by
  dsimp only
  let e := LinearEquiv.ofBijective (kerBaseChangeComparison A g) hbij
  letI : HasQuotient (LinearMap.ker (g.baseChange A))
      (Submodule A (LinearMap.ker (g.baseChange A))) :=
    @Submodule.hasQuotient A (LinearMap.ker (g.baseChange A))
      inferInstance (LinearMap.ker (g.baseChange A)).addCommGroup
      (LinearMap.ker (g.baseChange A)).module
  let hA := LinearMap.baseChange_comp_eq_zero f g h A
  let fA : (A ⊗[R] P) →ₗ[A] LinearMap.ker (g.baseChange A) :=
    LinearMap.codRestrictToKer (f.baseChange A) (g.baseChange A) hA
  let p : Submodule A (A ⊗[R] LinearMap.ker g) :=
    LinearMap.range ((LinearMap.codRestrictToKer f g h).baseChange A)
  let q : Submodule A (LinearMap.ker (g.baseChange A)) :=
    LinearMap.range fA
  have hpq : p.map e.toLinearMap = q := by
    dsimp only [p, q, fA, e]
    rw [← LinearMap.range_comp]
    exact congrArg LinearMap.range
      (kerBaseChangeComparison_comp_codRestrictToKer_baseChange A f g h)
  let eQuot : ((A ⊗[R] LinearMap.ker g) ⧸ p) ≃ₗ[A]
      ((LinearMap.ker (g.baseChange A)) ⧸ q) :=
    @Submodule.Quotient.equiv A (A ⊗[R] LinearMap.ker g)
      inferInstance inferInstance inferInstance
      (LinearMap.ker (g.baseChange A))
      (LinearMap.ker (g.baseChange A)).addCommGroup
      (LinearMap.ker (g.baseChange A)).module p q e hpq
  exact eQuot.trans
    (ShortComplex.moduleCatHomologyIso
      (ShortComplex.moduleCatMk (f.baseChange A) (g.baseChange A)
        (LinearMap.baseChange_comp_eq_zero f g h A))).toLinearEquiv.symm

namespace LowDegreeFiniteReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {C0 Z1 : Type v} [AddCommGroup C0] [AddCommGroup Z1]
  [Module R C0] [Module R Z1]

variable (f : C0 →ₗ[R] Z1)

/-- The degree-zero cohomology module of the two-term complex defined by `f`. -/
abbrev HZero := LinearMap.ker f

/-- The degree-one cohomology module of the two-term complex defined by `f`. -/
abbrev HOne := Z1 ⧸ LinearMap.range f

variable [Module.Finite R (HOne f)]

/-- The finite free degree-one term of the replacement complex. -/
noncomputable abbrev KOne :=
  Fin (FiniteFreeResolution.augRank R (HOne f)) → R

private noncomputable def kOneAug : KOne f →ₗ[R] HOne f :=
  FiniteFreeResolution.aug R (HOne f)

omit [IsNoetherianRing R] in
private theorem kOneAug_surjective : Function.Surjective (kOneAug f) :=
  FiniteFreeResolution.aug_surjective R (HOne f)

/-- The comparison map from the degree-one replacement term to the original complex. -/
noncomputable def kOneLift : KOne f →ₗ[R] Z1 :=
  (Module.projective_lifting_property (LinearMap.range f).mkQ (kOneAug f)
    (Submodule.mkQ_surjective (LinearMap.range f))).choose

omit [IsNoetherianRing R] in
private theorem mkQ_comp_kOneLift :
    (LinearMap.range f).mkQ ∘ₗ kOneLift f = kOneAug f :=
  (Module.projective_lifting_property (LinearMap.range f).mkQ (kOneAug f)
    (Submodule.mkQ_surjective (LinearMap.range f))).choose_spec

private noncomputable abbrev PreA :=
  Fin (FiniteFreeResolution.coverSub R (LinearMap.ker (kOneAug f))).1 → R

private noncomputable def preAToKOne : PreA f →ₗ[R] KOne f :=
  (FiniteFreeResolution.coverSub R (LinearMap.ker (kOneAug f))).2.1

private theorem range_preAToKOne :
    LinearMap.range (preAToKOne f) = LinearMap.ker (kOneAug f) :=
  (FiniteFreeResolution.coverSub R (LinearMap.ker (kOneAug f))).2.2

private theorem kOneAug_comp_preAToKOne :
    kOneAug f ∘ₗ preAToKOne f = 0 :=
  LinearMap.range_le_ker_iff.mp (le_of_eq (range_preAToKOne f))

private noncomputable def preAToRange : PreA f →ₗ[R] LinearMap.range f :=
  LinearMap.codRestrict (LinearMap.range f) (kOneLift f ∘ₗ preAToKOne f) fun x ↦ by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
      ← LinearMap.comp_apply, ← LinearMap.comp_assoc, mkQ_comp_kOneLift,
      kOneAug_comp_preAToKOne, LinearMap.zero_apply]

@[simp]
private theorem preAToRange_coe (x : PreA f) :
    (preAToRange f x : Z1) = kOneLift f (preAToKOne f x) :=
  rfl

private noncomputable def preALift : PreA f →ₗ[R] C0 :=
  (Module.projective_lifting_property f.rangeRestrict (preAToRange f)
    f.surjective_rangeRestrict).choose

private theorem rangeRestrict_comp_preALift :
    f.rangeRestrict ∘ₗ preALift f = preAToRange f :=
  (Module.projective_lifting_property f.rangeRestrict (preAToRange f)
    f.surjective_rangeRestrict).choose_spec

private theorem f_comp_preALift :
    f ∘ₗ preALift f = kOneLift f ∘ₗ preAToKOne f := by
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val
    (LinearMap.congr_fun (rangeRestrict_comp_preALift f) x)

variable [Module.Finite R (HZero f)]

private noncomputable abbrev PreB :=
  Fin (FiniteFreeResolution.augRank R (HZero f)) → R

private noncomputable def preBToHZero : PreB f →ₗ[R] HZero f :=
  FiniteFreeResolution.aug R (HZero f)

omit [IsNoetherianRing R] [Module.Finite R (HOne f)] in
private theorem preBToHZero_surjective : Function.Surjective (preBToHZero f) :=
  FiniteFreeResolution.aug_surjective R (HZero f)

private noncomputable def preBToC0 : PreB f →ₗ[R] C0 :=
  (LinearMap.ker f).subtype ∘ₗ preBToHZero f

omit [IsNoetherianRing R] [Module.Finite R (HOne f)] in
private theorem f_comp_preBToC0 : f ∘ₗ preBToC0 f = 0 := by
  rw [preBToC0, ← LinearMap.comp_assoc, LinearMap.comp_ker_subtype,
    LinearMap.zero_comp]

private noncomputable abbrev Pre := PreA f × PreB f

private noncomputable def alphaFirst : Pre f →ₗ[R] KOne f :=
  preAToKOne f ∘ₗ LinearMap.fst R (PreA f) (PreB f)

private noncomputable def alphaSecond : Pre f →ₗ[R] C0 :=
  preALift f ∘ₗ LinearMap.fst R (PreA f) (PreB f) +
    preBToC0 f ∘ₗ LinearMap.snd R (PreA f) (PreB f)

private noncomputable def alpha : Pre f →ₗ[R] KOne f × C0 :=
  (alphaFirst f).prod (alphaSecond f)

private noncomputable def beta : KOne f × C0 →ₗ[R] Z1 :=
  kOneLift f ∘ₗ LinearMap.fst R (KOne f) C0 -
    f ∘ₗ LinearMap.snd R (KOne f) C0

private theorem beta_comp_alpha : beta f ∘ₗ alpha f = 0 := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  simp only [LinearMap.comp_apply, alpha, beta, LinearMap.sub_apply,
    LinearMap.prod_apply, Function.prod_apply, alphaFirst, alphaSecond,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.add_apply,
    LinearMap.zero_apply]
  have hA := LinearMap.congr_fun (f_comp_preALift f) a
  have hB := LinearMap.congr_fun (f_comp_preBToC0 f) b
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hA hB
  rw [map_add, hA, hB, add_zero, sub_self]

omit [IsNoetherianRing R] [Module.Finite R (HZero f)] in
private theorem beta_surjective : Function.Surjective (beta f) := by
  intro z
  obtain ⟨k, hk⟩ := kOneAug_surjective f ((LinearMap.range f).mkQ z)
  have hlift := LinearMap.congr_fun (mkQ_comp_kOneLift f) k
  simp only [LinearMap.comp_apply] at hlift
  have hmem : kOneLift f k - z ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub,
      hlift, hk, sub_self]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨(k, c), ?_⟩
  simp only [beta, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  rw [hc, sub_sub_cancel]

private theorem exact_alpha_beta : Function.Exact (alpha f) (beta f) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · rintro ⟨k, c⟩ hy
    have hbeta : kOneLift f k - f c = 0 := by
      simpa only [LinearMap.mem_ker, beta, LinearMap.sub_apply,
        LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply] using hy
    have hkc : kOneLift f k = f c := sub_eq_zero.mp hbeta
    have hlift := LinearMap.congr_fun (mkQ_comp_kOneLift f) k
    simp only [LinearMap.comp_apply] at hlift
    have hkaug : kOneAug f k = 0 := by
      calc
        kOneAug f k = (LinearMap.range f).mkQ (kOneLift f k) := hlift.symm
        _ = (LinearMap.range f).mkQ (f c) := congrArg _ hkc
        _ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨c, rfl⟩
    have hkRange : k ∈ LinearMap.range (preAToKOne f) := by
      rw [range_preAToKOne]
      exact LinearMap.mem_ker.mpr hkaug
    obtain ⟨a, ha⟩ := hkRange
    have hpre := LinearMap.congr_fun (f_comp_preALift f) a
    simp only [LinearMap.comp_apply] at hpre
    have hcKer : c - preALift f a ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, ← hkc, hpre, ha, sub_self]
    obtain ⟨b, hb⟩ := preBToHZero_surjective f ⟨c - preALift f a, hcKer⟩
    have hbval := congrArg Subtype.val hb
    change preBToC0 f b = c - preALift f a at hbval
    refine ⟨(a, b), ?_⟩
    apply Prod.ext
    · simpa only [alpha, LinearMap.prod_apply, Function.prod_apply, alphaFirst,
        LinearMap.comp_apply, LinearMap.fst_apply] using ha
    · simp only [alpha, LinearMap.prod_apply, Function.prod_apply, alphaSecond,
        LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
      rw [hbval]
      abel
  · exact LinearMap.range_le_ker_iff.mpr (beta_comp_alpha f)

/-- The finite projective degree-zero term of the replacement complex. -/
noncomputable abbrev KZero := Pre f ⧸ LinearMap.ker (alpha f)

private noncomputable def kZeroEmbed : KZero f →ₗ[R] KOne f × C0 :=
  (LinearMap.ker (alpha f)).liftQ (alpha f) le_rfl

private theorem kZeroEmbed_injective : Function.Injective (kZeroEmbed f) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot' (LinearMap.ker (alpha f)) (alpha f) rfl

private theorem range_kZeroEmbed :
    LinearMap.range (kZeroEmbed f) = LinearMap.range (alpha f) :=
  Submodule.range_liftQ (LinearMap.ker (alpha f)) (alpha f) le_rfl

private theorem exact_kZeroEmbed_beta : Function.Exact (kZeroEmbed f) (beta f) := by
  rw [LinearMap.exact_iff, range_kZeroEmbed]
  exact LinearMap.exact_iff.mp (exact_alpha_beta f)

variable [Module.Flat R C0] [Module.Flat R Z1]

/-- The degree-zero replacement term is projective. It is finite by typeclass inference. -/
theorem kZero_projective : Module.Projective R (KZero f) := by
  letI : Module.Flat R (KOne f × C0) := Module.Flat.prod
  exact Module.Projective.quotient_ker_of_exact_surjective
    (alpha f) (beta f) (exact_alpha_beta f) (beta_surjective f)

/-- The differential of the finite-projective replacement complex. -/
noncomputable def kZeroToKOne : KZero f →ₗ[R] KOne f :=
  LinearMap.fst R (KOne f) C0 ∘ₗ kZeroEmbed f

/-- The comparison map from the degree-zero replacement term to the original complex. -/
noncomputable def kZeroToCZero : KZero f →ₗ[R] C0 :=
  LinearMap.snd R (KOne f) C0 ∘ₗ kZeroEmbed f

omit [Module.Flat R C0] [Module.Flat R Z1] in
/-- The replacement differential and comparison maps form a map of complexes. -/
theorem comparison_commutes :
    kOneLift f ∘ₗ kZeroToKOne f = f ∘ₗ kZeroToCZero f := by
  have hcomp : beta f ∘ₗ kZeroEmbed f = 0 :=
    LinearMap.range_le_ker_iff.mp
      (le_of_eq (LinearMap.exact_iff.mp (exact_kZeroEmbed_beta f)).symm)
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomp x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, beta,
    LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    kZeroToKOne, kZeroToCZero] at hx ⊢
  exact sub_eq_zero.mp hx

omit [Module.Flat R C0] in
private theorem baseChange_exact_kZeroEmbed_beta
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Exact ((kZeroEmbed f).baseChange A) ((beta f).baseChange A) := by
  have hrange : LinearMap.range (beta f) = ⊤ :=
    LinearMap.range_eq_top.mpr (beta_surjective f)
  letI : Subsingleton (Z1 ⧸ LinearMap.range (beta f)) := by
    rw [hrange]
    infer_instance
  exact LinearMap.baseChange_exact_of_exact_of_flat_coker A
    (kZeroEmbed f) (beta f)
    (LinearMap.range_le_ker_iff.mp
      (le_of_eq (LinearMap.exact_iff.mp (exact_kZeroEmbed_beta f)).symm))
    (exact_kZeroEmbed_beta f)

omit [Module.Flat R C0] in
private theorem baseChange_kZeroEmbed_injective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Injective ((kZeroEmbed f).baseChange A) := by
  have h := LinearMap.lTensor_injective_of_exact_of_flat
    (beta f) (beta_surjective f) (kZeroEmbed f)
    (kZeroEmbed_injective f) (exact_kZeroEmbed_beta f) A
  simpa only [LinearMap.baseChange_eq_ltensor] using h

omit [IsNoetherianRing R] [Module.Finite R (HZero f)]
  [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChange_beta_surjective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Surjective ((beta f).baseChange A) :=
  LinearMap.baseChange_surjective A (beta_surjective f)

private noncomputable def baseChangeProdEquiv
    (A : Type*) [CommRing A] [Algebra R A] :
    (A ⊗[R] (KOne f × C0)) ≃ₗ[A] (A ⊗[R] (KOne f)) × (A ⊗[R] C0) :=
  TensorProduct.prodRight R A A (KOne f) C0

private noncomputable def baseChangeEmbedProd
    (A : Type*) [CommRing A] [Algebra R A] :
    (A ⊗[R] (KZero f)) →ₗ[A] (A ⊗[R] (KOne f)) × (A ⊗[R] C0) :=
  (baseChangeProdEquiv f A).toLinearMap ∘ₗ (kZeroEmbed f).baseChange A

private noncomputable def baseChangeBetaProd
    (A : Type*) [CommRing A] [Algebra R A] :
    (A ⊗[R] (KOne f)) × (A ⊗[R] C0) →ₗ[A] (A ⊗[R] Z1) :=
  (beta f).baseChange A ∘ₗ (baseChangeProdEquiv f A).symm.toLinearMap

omit [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChangeEmbedProd_eq
    (A : Type*) [CommRing A] [Algebra R A] :
    baseChangeEmbedProd f A =
      ((kZeroToKOne f).baseChange A).prod ((kZeroToCZero f).baseChange A) := by
  apply AlgebraTensorModule.ext
  intro a x
  simp [baseChangeEmbedProd, baseChangeProdEquiv, kZeroToKOne, kZeroToCZero]

omit [IsNoetherianRing R] [Module.Finite R (HZero f)]
  [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChangeBetaProd_eq
    (A : Type*) [CommRing A] [Algebra R A] :
    baseChangeBetaProd f A =
      (kOneLift f).baseChange A ∘ₗ
          LinearMap.fst A (A ⊗[R] (KOne f)) (A ⊗[R] C0) -
        f.baseChange A ∘ₗ
          LinearMap.snd A (A ⊗[R] (KOne f)) (A ⊗[R] C0) := by
  apply LinearMap.prod_ext
  · apply AlgebraTensorModule.ext
    intro a k
    simp only [LinearMap.comp_apply, LinearMap.inl_apply,
      baseChangeBetaProd, baseChangeProdEquiv]
    rw [show (0 : A ⊗[R] C0) = a ⊗ₜ[R] (0 : C0) by simp]
    have hpair :
        (TensorProduct.prodRight R A A (KOne f) C0).symm
            (a ⊗ₜ[R] k, a ⊗ₜ[R] (0 : C0)) = a ⊗ₜ[R] (k, 0) :=
      TensorProduct.prodRight_symm_tmul R A A (KOne f) C0 a k 0
    change (beta f).baseChange A
      ((TensorProduct.prodRight R A A (KOne f) C0).symm
        (a ⊗ₜ[R] k, a ⊗ₜ[R] (0 : C0))) = _
    rw [hpair]
    simp [beta]
  · apply AlgebraTensorModule.ext
    intro a c
    simp only [LinearMap.comp_apply, LinearMap.inr_apply,
      baseChangeBetaProd, baseChangeProdEquiv]
    rw [show (0 : A ⊗[R] (KOne f)) = a ⊗ₜ[R] (0 : KOne f) by simp]
    have hpair :
        (TensorProduct.prodRight R A A (KOne f) C0).symm
            (a ⊗ₜ[R] (0 : KOne f), a ⊗ₜ[R] c) = a ⊗ₜ[R] (0, c) :=
      TensorProduct.prodRight_symm_tmul R A A (KOne f) C0 a 0 c
    change (beta f).baseChange A
      ((TensorProduct.prodRight R A A (KOne f) C0).symm
        (a ⊗ₜ[R] (0 : KOne f), a ⊗ₜ[R] c)) = _
    rw [hpair]
    simp [beta]

omit [Module.Flat R C0] in
private theorem baseChange_exact_embedProd_betaProd
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Exact (baseChangeEmbedProd f A) (baseChangeBetaProd f A) := by
  apply (LinearEquiv.conj_symm_exact_iff_exact
    ((kZeroEmbed f).baseChange A) ((beta f).baseChange A)
    (baseChangeProdEquiv f A).symm).mpr
  exact baseChange_exact_kZeroEmbed_beta f A

omit [Module.Flat R C0] in
private theorem baseChangeEmbedProd_injective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Injective (baseChangeEmbedProd f A) :=
  (baseChangeProdEquiv f A).injective.comp
    (baseChange_kZeroEmbed_injective f A)

omit [IsNoetherianRing R] [Module.Finite R (HZero f)]
  [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChangeBetaProd_surjective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Surjective (baseChangeBetaProd f A) :=
  (baseChange_beta_surjective f A).comp
    (baseChangeProdEquiv f A).symm.surjective

omit [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChange_comparison_commutes
    (A : Type*) [CommRing A] [Algebra R A] :
    (kOneLift f).baseChange A ∘ₗ (kZeroToKOne f).baseChange A =
      f.baseChange A ∘ₗ (kZeroToCZero f).baseChange A := by
  rw [← LinearMap.baseChange_comp, comparison_commutes,
    LinearMap.baseChange_comp]

private noncomputable def baseChangeKernelComparison
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.ker ((kZeroToKOne f).baseChange A) →ₗ[A]
      LinearMap.ker (f.baseChange A) :=
  LinearMap.codRestrict _
    ((kZeroToCZero f).baseChange A ∘ₗ
      (LinearMap.ker ((kZeroToKOne f).baseChange A)).subtype) fun x ↦ by
        rw [LinearMap.mem_ker, LinearMap.comp_apply]
        have hx := LinearMap.congr_fun (baseChange_comparison_commutes f A) x
        simp only [LinearMap.comp_apply, LinearMap.mem_ker.mp x.property,
          map_zero] at hx
        exact hx.symm

omit [Module.Flat R C0] in
private theorem baseChangeKernelComparison_bijective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Bijective (baseChangeKernelComparison f A) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply baseChangeEmbedProd_injective f A
    rw [baseChangeEmbedProd_eq]
    apply Prod.ext
    · simp only [LinearMap.prod_apply, Function.prod_apply,
        LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property]
    · exact congrArg Subtype.val hxy
  · intro c
    have hker :
        (0, (c : A ⊗[R] C0)) ∈ LinearMap.ker (baseChangeBetaProd f A) := by
      rw [LinearMap.mem_ker, baseChangeBetaProd_eq]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, map_zero, zero_sub, neg_eq_zero]
      exact c.property
    rw [(baseChange_exact_embedProd_betaProd f A).linearMap_ker_eq] at hker
    obtain ⟨x, hx⟩ := hker
    rw [baseChangeEmbedProd_eq] at hx
    simp only [LinearMap.prod_apply, Function.prod_apply] at hx
    refine ⟨⟨x, congrArg Prod.fst hx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Prod.snd hx

private noncomputable def baseChangeCokerComparison
    (A : Type*) [CommRing A] [Algebra R A] :
    (A ⊗[R] (KOne f)) →ₗ[A]
      (A ⊗[R] Z1) ⧸ LinearMap.range (f.baseChange A) :=
  (LinearMap.range (f.baseChange A)).mkQ ∘ₗ (kOneLift f).baseChange A

omit [IsNoetherianRing R] [Module.Finite R (HZero f)]
  [Module.Flat R C0] [Module.Flat R Z1] in
private theorem baseChangeCokerComparison_surjective
    (A : Type*) [CommRing A] [Algebra R A] :
    Function.Surjective (baseChangeCokerComparison f A) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
      obtain ⟨⟨k, c⟩, hkc⟩ := baseChangeBetaProd_surjective f A z
      rw [baseChangeBetaProd_eq] at hkc
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.fst_apply, LinearMap.snd_apply] at hkc
      refine ⟨k, ?_⟩
      change (LinearMap.range (f.baseChange A)).mkQ
        ((kOneLift f).baseChange A k) = Submodule.Quotient.mk z
      rw [← hkc]
      change (LinearMap.range (f.baseChange A)).mkQ
          ((kOneLift f).baseChange A k) =
        (LinearMap.range (f.baseChange A)).mkQ
          ((kOneLift f).baseChange A k - f.baseChange A c)
      have hcRange :
          f.baseChange A c ∈ LinearMap.range (f.baseChange A) :=
        ⟨c, rfl⟩
      have hcZero :
          (LinearMap.range (f.baseChange A)).mkQ (f.baseChange A c) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcRange
      rw [map_sub, hcZero, sub_zero]

omit [Module.Flat R C0] [Module.Flat R Z1] in
private theorem range_baseChange_kZeroToKOne_le_ker_baseChangeCokerComparison
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.range ((kZeroToKOne f).baseChange A) ≤
      LinearMap.ker (baseChangeCokerComparison f A) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change (LinearMap.range (f.baseChange A)).mkQ
    ((kOneLift f).baseChange A ((kZeroToKOne f).baseChange A x)) = 0
  have hcomm := LinearMap.congr_fun (baseChange_comparison_commutes f A) x
  simp only [LinearMap.comp_apply] at hcomm
  rw [hcomm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨(kZeroToCZero f).baseChange A x, rfl⟩

omit [Module.Flat R C0] in
private theorem ker_baseChangeCokerComparison_le_range_baseChange_kZeroToKOne
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.ker (baseChangeCokerComparison f A) ≤
      LinearMap.range ((kZeroToKOne f).baseChange A) := by
  intro k hk
  rw [LinearMap.mem_ker] at hk
  change (LinearMap.range (f.baseChange A)).mkQ
    ((kOneLift f).baseChange A k) = 0 at hk
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
  obtain ⟨c, hc⟩ := hk
  have hpair :
      (k, c) ∈ LinearMap.ker (baseChangeBetaProd f A) := by
    rw [LinearMap.mem_ker, baseChangeBetaProd_eq]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    exact sub_eq_zero.mpr hc.symm
  rw [(baseChange_exact_embedProd_betaProd f A).linearMap_ker_eq] at hpair
  obtain ⟨x, hx⟩ := hpair
  rw [baseChangeEmbedProd_eq] at hx
  simp only [LinearMap.prod_apply, Function.prod_apply] at hx
  exact ⟨x, congrArg Prod.fst hx⟩

omit [Module.Flat R C0] in
private theorem range_baseChange_kZeroToKOne_eq_ker_baseChangeCokerComparison
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.range ((kZeroToKOne f).baseChange A) =
      LinearMap.ker (baseChangeCokerComparison f A) :=
  le_antisymm
    (range_baseChange_kZeroToKOne_le_ker_baseChangeCokerComparison f A)
    (ker_baseChangeCokerComparison_le_range_baseChange_kZeroToKOne f A)

/-- The replacement computes degree-zero cohomology after every algebra base change. -/
noncomputable def baseChangeKernelEquiv
    (A : Type*) [CommRing A] [Algebra R A] :
    LinearMap.ker ((kZeroToKOne f).baseChange A) ≃ₗ[A]
      LinearMap.ker (f.baseChange A) :=
  LinearEquiv.ofBijective (baseChangeKernelComparison f A)
    (baseChangeKernelComparison_bijective f A)

/-- The replacement computes degree-one cohomology after every algebra base change. -/
noncomputable def baseChangeCokerEquiv
    (A : Type*) [CommRing A] [Algebra R A] :
    ((A ⊗[R] KOne f) ⧸ LinearMap.range ((kZeroToKOne f).baseChange A)) ≃ₗ[A]
      ((A ⊗[R] Z1) ⧸ LinearMap.range (f.baseChange A)) :=
  (Submodule.quotEquivOfEq _ _
      (range_baseChange_kZeroToKOne_eq_ker_baseChangeCokerComparison f A)).trans
    ((baseChangeCokerComparison f A).quotKerEquivOfSurjective
      (baseChangeCokerComparison_surjective f A))

end LowDegreeFiniteReplacement
end ModularCurves
