/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d.
-/
import ModularCurves.ForMathlib.GradedQuotient
import ModularCurves.ForMathlib.ProjectiveSpaceChart
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# `Proj` of a quotient grading is a closed subscheme of `Proj`

For a homogeneous ideal `I` of a graded algebra `𝒜`, the morphism
`Proj.map (quotientGradingHom I) : Proj (𝒜/I) ⟶ Proj 𝒜` is a closed immersion:
closed immersions are Zariski-local on the target, over each basic open `D₊(s)` the
map is `Spec` of `Away.map (quotientGradingHom I) s`, and that ring map is surjective
because the quotient grading consists of images.
-/

namespace HomogeneousIdeal

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

theorem away_map_quotientGradingHom_surjective {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map (quotientGradingHom I) s) := by
  intro z
  obtain ⟨n, a', ha', rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (mk_mem_quotientGrading I hs) z
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp ha'
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs n a ha, ?_⟩
  rw [Away.map_mk]
  rfl

variable {I} in
private theorem mem_span_sigma_of_mem_irrelevant {z : A}
    (hz : z ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    z ∈ Ideal.span (Set.range fun x : Σ i : ℕ+, 𝒜 i => (x.2 : A)) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c _ => ?_
  by_cases hc0 : c = 0
  · subst hc0
    have hz0 : GradedRing.proj 𝒜 0 z = 0 := hz
    rw [GradedRing.proj_apply] at hz0
    rw [hz0]
    exact zero_mem _
  · exact Ideal.subset_span
      ⟨⟨⟨c, Nat.pos_of_ne_zero hc0⟩, DirectSum.decompose 𝒜 z c⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj` of a quotient is a closed subscheme**: the morphism induced by the quotient
map on a homogeneous ideal is a closed immersion. -/
theorem isClosedImmersion_proj_map_quotientGradingHom :
    IsClosedImmersion (Proj.map (quotientGradingHom I)
      (quotientGradingHom_irrelevant_le I)) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_eq_top 𝒜 (fun x : Σ i : ℕ+, 𝒜 i => (x.2 : A))
      fun _ hz => mem_span_sigma_of_mem_irrelevant hz)]
  rintro ⟨i, t, ht⟩
  have hi : 0 < (i : ℕ) := i.2
  have hcomm := Proj.awayι_comp_map (quotientGradingHom I)
    (quotientGradingHom_irrelevant_le I) hi t ht
  -- unfold both `awayι`s and cancel the (mono) open immersion of the target open
  rw [← Proj.basicOpenIsoSpec_inv_ι, ← Proj.basicOpenIsoSpec_inv_ι,
    Category.assoc] at hcomm
  have hres : (Proj.basicOpen (quotientGrading I) (quotientGradingHom I t)).ι ≫
      Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) =
      (Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) ∣_
        Proj.basicOpen 𝒜 t) ≫ (Proj.basicOpen 𝒜 t).ι := by
    rw [morphismRestrict_ι]
    rfl
  rw [hres] at hcomm
  -- hcomm : isoQ.inv ≫ (g ∣_ U) ≫ U.ι = Spec.map (Away.map …) ≫ iso𝒜.inv ≫ U.ι
  rw [← Category.assoc, ← Category.assoc] at hcomm
  replace hcomm := (cancel_mono (Proj.basicOpen 𝒜 t).ι).mp hcomm
  -- hcomm : isoQ.inv ≫ (g ∣_ U) = Spec.map (Away.map …) ≫ iso𝒜.inv
  have key : (Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) ∣_
      Proj.basicOpen 𝒜 t) =
      (Proj.basicOpenIsoSpec (quotientGrading I) (quotientGradingHom I t)
          (mk_mem_quotientGrading I ht) hi).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (quotientGradingHom I) t)) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hi).inv := by
    rw [← Iso.inv_comp_eq]
    exact hcomm
  rw [key]
  haveI h1 : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Away.map (quotientGradingHom I) t))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_quotientGradingHom_surjective I ht)
  haveI h2 : IsClosedImmersion ((Proj.basicOpenIsoSpec 𝒜 t ht hi).inv) := inferInstance
  haveI h3 : IsClosedImmersion ((Proj.basicOpenIsoSpec (quotientGrading I)
      (quotientGradingHom I t) (mk_mem_quotientGrading I ht) hi).hom) := inferInstance
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ h3
    (MorphismProperty.IsStableUnderComposition.comp_mem _ _ h1 h2)

section Kernel

open HomogeneousLocalization

/-- Normal-form stability: multiplying numerator and denominator by a power of `s`. -/
private lemma away_mk_shift {e : ℕ} {s : A} (hs : s ∈ 𝒜 e) (n m : ℕ) (p : A)
    (hp : p ∈ 𝒜 (n • e)) :
    HomogeneousLocalization.Away.mk 𝒜 hs (n + m) (s ^ m * p)
        (by
          have h1 : s ^ m ∈ 𝒜 (m • e) := SetLike.pow_mem_graded m hs
          have h2 := SetLike.mul_mem_graded h1 hp
          rw [show m • e + n • e = (n + m) • e by rw [add_smul]; ring] at h2
          exact h2) =
      HomogeneousLocalization.Away.mk 𝒜 hs n p hp := by
  apply val_injective
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [pow_add, mul_assoc]⟩

/-- Products of `Away.mk`s. -/
private lemma away_mk_mul {e : ℕ} {s : A} (hs : s ∈ 𝒜 e) (i j : ℕ) (p q : A)
    (hp : p ∈ 𝒜 (i • e)) (hq : q ∈ 𝒜 (j • e)) :
    HomogeneousLocalization.Away.mk 𝒜 hs i p hp *
        HomogeneousLocalization.Away.mk 𝒜 hs j q hq =
      HomogeneousLocalization.Away.mk 𝒜 hs (i + j) (p * q)
        (by
          have h2 := SetLike.mul_mem_graded hp hq
          rw [← add_smul] at h2
          exact h2) := by
  apply val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp [pow_add]⟩

/-- A `mk` with zero numerator is zero. -/
private lemma away_mk_zero {e : ℕ} {s : A} (hs : s ∈ 𝒜 e) (n : ℕ)
    (hp : (0 : A) ∈ 𝒜 (n • e)) :
    HomogeneousLocalization.Away.mk 𝒜 hs n 0 hp = 0 := by
  apply val_injective
  rw [Away.val_mk, val_zero]
  exact Localization.mk_zero _

/-- **The chartwise kernel is principal**: for `I = (F)` with `F` homogeneous of degree
`d` and `s` homogeneous of degree `1`, the kernel of
`(A_s)₀ → ((A/I)_s)₀` is generated by `F/sᵈ`. -/
theorem ker_away_map_quotientGradingHom {d : ℕ} {F : A} (hF : F ∈ 𝒜 d)
    (hI : I.toIdeal = Ideal.span {F}) {s : A} (hs : s ∈ 𝒜 1) :
    RingHom.ker (Away.map (quotientGradingHom I) s) =
      Ideal.span {HomogeneousLocalization.Away.mk 𝒜 hs d F (by simpa using hF)} := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hs z
    rw [RingHom.mem_ker, Away.map_mk] at hz
    -- extract: some power of `s` multiplies `p` into `I`
    have hval := congrArg (valRingHom (Submonoid.powers ((quotientGradingHom I) s))) hz
    rw [valRingHom_apply, valRingHom_apply, Away.val_mk, val_zero] at hval
    have hunit : IsUnit (algebraMap (A ⧸ I.toIdeal)
        (Localization (Submonoid.powers ((quotientGradingHom I) s)))
        (((quotientGradingHom I) s) ^ n)) :=
      IsLocalization.map_units _
        (⟨_ ^ n, n, rfl⟩ : Submonoid.powers ((quotientGradingHom I) s))
    have hzero : algebraMap (A ⧸ I.toIdeal)
        (Localization (Submonoid.powers ((quotientGradingHom I) s)))
        ((quotientGradingHom I) p) = 0 := by
      have h1 : (Localization.mk ((quotientGradingHom I) p)
          (⟨_ ^ n, n, rfl⟩ : Submonoid.powers ((quotientGradingHom I) s))) *
          algebraMap (A ⧸ I.toIdeal) _ (((quotientGradingHom I) s) ^ n) =
          algebraMap (A ⧸ I.toIdeal) _ ((quotientGradingHom I) p) := by
        rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
          Localization.mk_mul, mul_one]
        rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        exact ⟨1, by simp [mul_comm]⟩
      rw [← h1, hval, zero_mul]
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers ((quotientGradingHom I) s)) _ _).mp hzero
    have hmem : s ^ k * p ∈ I.toIdeal := by
      have : (quotientGradingHom I) (s ^ k * p) = 0 := by
        rw [map_mul, map_pow]
        exact hc
      rwa [quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker] at this
    rw [hI, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc'⟩ := hmem
    -- take the homogeneous component of degree `k + n` in `s^k p = F c`
    by_cases hd : d ≤ k + n
    · have hcomp : s ^ k * p =
          F * (DirectSum.decompose 𝒜 c (k + n - d) : A) := by
        have h1 : s ^ k * p ∈ 𝒜 (k + n) := by
          have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k hs) hp
          simpa [add_smul, smul_eq_mul, mul_comm] using this
        have h2 := congrArg (fun x => (DirectSum.decompose 𝒜 x (k + n) : A)) hc'
        simp only at h2
        rw [DirectSum.decompose_of_mem_same 𝒜 h1] at h2
        have h3 := DirectSum.coe_decompose_mul_add_of_left_mem (j := k + n - d) 𝒜
          (b := c) hF
        rw [show d + (k + n - d) = k + n by omega] at h3
        rw [h2, h3]
      -- now `p/sⁿ = (F/s^d) · (c'/s^{k+n-d})`, up to an `s`-power shift
      have hc'' : (DirectSum.decompose 𝒜 c (k + n - d) : A) ∈ 𝒜 ((k + n - d) • 1) := by
        simpa using (DirectSum.decompose 𝒜 c (k + n - d)).2
      -- assemble the factorisation, comparing values in the localization
      rw [Ideal.mem_span_singleton]
      refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs (k + n - d)
        (DirectSum.decompose 𝒜 c (k + n - d) : A) hc'', ?_⟩
      rw [away_mk_mul]
      apply val_injective
      rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      rw [← hcomp, show d + (k + n - d) = k + n by omega]
      ring
    · -- degree too small: the degree-`(k+n)` component of `F·c` vanishes
      have h1 : s ^ k * p ∈ 𝒜 (k + n) := by
        have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k hs) hp
        simpa [add_smul, smul_eq_mul, mul_comm] using this
      have h2 := congrArg (fun x => (DirectSum.decompose 𝒜 x (k + n) : A)) hc'
      simp only at h2
      rw [DirectSum.decompose_of_mem_same 𝒜 h1,
        DirectSum.coe_decompose_mul_of_left_mem_of_not_le 𝒜 hF hd] at h2
      have h4 : HomogeneousLocalization.Away.mk 𝒜 hs n p hp = 0 := by
        rw [← away_mk_shift (𝒜 := 𝒜) hs n k p hp]
        apply val_injective
        rw [Away.val_mk, val_zero, h2]
        exact Localization.mk_zero _
      rw [h4]
      exact zero_mem _
  · intro hz
    rw [Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    rw [RingHom.mem_ker, map_mul]
    have hFzero : Away.map (quotientGradingHom I) s
        (HomogeneousLocalization.Away.mk 𝒜 hs d F (by simp [hF])) = 0 := by
      rw [Away.map_mk]
      have hFI : (quotientGradingHom I) F = 0 := by
        rw [quotientGradingHom_apply, ← RingHom.mem_ker, Ideal.mk_ker, hI]
        exact Ideal.subset_span rfl
      apply val_injective
      rw [Away.val_mk, val_zero, hFI]
      exact Localization.mk_zero _
    rw [hFzero, zero_mul]

end Kernel

end HomogeneousIdeal
