/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram

VENDORED into AINTLIB (2026-07-04) from WilliamCoram/PhD (PhD/ToPR/MvRestricted.lean),
pending its mathlib PR. Import paths redirected to this workspace's vendored copies.
-/
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Order.Lex
import «Adic spaces».Vendored.CoramMvGaussNorm

/-! # Norm instances on multivariate restricted power series (vendored) -/




variable {R : Type*} {σ : Type*} (c : σ → ℝ)

class StrongPos (c : σ → ℝ) : Prop where pos : ∀ i, 0 < c i

lemma StrongPos_pos [StrongPos c] : ∀ i, 0 < c i := by expose_names; exact inst.pos

instance (hc : ∀ i, 0 < c i) : StrongPos c := {pos := hc}

instance (c : ℝ) (hc : 0 < c) : StrongPos (fun _ : Unit ↦ c) := {pos := by grind}

lemma StrongPos_unit_iff (c : ℝ) : StrongPos (fun _ : Unit ↦ c) ↔ 0 < c := by
  constructor
  · exact fun _ ↦ StrongPos_pos (fun _ : Unit ↦ c) 0
  · exact fun h ↦ {pos := fun _ ↦ h}
namespace MvRestricted

variable (R) in
noncomputable
abbrev gaussNorm [NormedRing R] [IsUltrametricDist R] (f : MvPowerSeries.Restricted R c) : ℝ :=
  MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1

lemma hasGaussNorm [NormedRing R] [IsUltrametricDist R] (f : MvPowerSeries.Restricted R c) :
  MvPowerSeries.HasGaussNorm norm c f.1 := Filter.Tendsto.bddAbove_range_of_cofinite f.2

noncomputable
instance isRingNorm [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    RingNorm (MvPowerSeries.Restricted R c) where
  toFun f := gaussNorm R c f
  map_zero' := MvPowerSeries.gaussNorm_zero norm c norm_zero
  add_le' f g := by
    have h := MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
      norm_nonneg (IsUltrametricDist.norm_add_le_max) (hasGaussNorm c f) (hasGaussNorm c g)
    have : max (gaussNorm R c f) (gaussNorm R c g) ≤
        gaussNorm R c f + gaussNorm R c g := by
      refine max_le_add_of_nonneg ?_ ?_
      all_goals exact (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
    exact h.trans this
  neg' f := MvPowerSeries.gaussNorm_neg norm c norm_neg f.1
  mul_le' f g := MvPowerSeries.gaussNorm_mul_le norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg norm_mul_le IsUltrametricDist.norm_add_le_max norm_zero (hasGaussNorm c f)
    (hasGaussNorm c g)
  eq_zero_of_map_eq_zero' f := by
    simpa using (MvPowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
      (StrongPos_pos c) (hasGaussNorm c f)).mp

variable (R) in
noncomputable
instance isNormedRing [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
  NormedRing (MvPowerSeries.Restricted R c) := RingNorm.toNormedRing (isRingNorm c)

lemma norm_eq [NormedRing R] [IsUltrametricDist R] [StrongPos c] (f : MvPowerSeries.Restricted R c) :
    ‖f‖ = MvPowerSeries.gaussNorm (norm : R → ℝ) c f.1 := by rfl

variable (R) in
noncomputable
instance isNonarchimedean [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    IsNonarchimedean (R := ℝ) (α := MvPowerSeries.Restricted R c) norm :=
  fun f g => MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)

variable (R) in
noncomputable
instance isUltrametricDist
    [NormedRing R] [IsUltrametricDist R] [StrongPos c] :
    IsUltrametricDist (MvPowerSeries.Restricted R c) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (isNonarchimedean R c)

section AbsoluteValue

private lemma foo (hc : ∀ i, 0 ≤ c i) (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
  Finset.prod_nonneg (fun i _ ↦ pow_nonneg (hc i) (t i))

lemma gaussNorm_achieved [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c)
    (f : MvPowerSeries.Restricted R c) :
    ∃ a, MvPowerSeries.AchievesGaussNorm norm c f.1 a := by
  simp_rw [MvPowerSeries.AchievesGaussNorm]
  by_cases hG : gaussNorm R c f = 0
  · use 0
    have := MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) 0
    simp only [hG] at this ⊢
    exact le_antisymm this (mul_nonneg (norm_nonneg _) (foo c hc 0))
  · have hpos : 0 < gaussNorm R c f :=
      (MvPowerSeries.gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' hG
    have hfin : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}.Finite := by
      have : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
      simp_rw [MvPowerSeries.IsRestrictedGauss, NormedAddGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm R c f / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      convert this with t
      grind [foo c hc t]
    have hne : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have hlt : gaussNorm R c f ≤ gaussNorm R c f / 2 := by
        apply ciSup_le
        intro t
        have : t ∉ {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)} := by
          simp [hemp]
        grind
      linarith
    obtain ⟨m, hm_mem, hm_max⟩ := hfin.toFinset.exists_max_image
      (fun t ↦ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)) (by aesop)
    use m
    apply le_antisymm (MvPowerSeries.le_gaussNorm norm c f.1 (hasGaussNorm c f) m)
    apply ciSup_le
    intro t
    by_cases ht : t ∈ {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}
    · exact hm_max t (by aesop)
    · exact le_trans (le_of_lt (by aesop)) (by aesop)

lemma achievingPoints_finite [NormedRing R] [IsUltrametricDist R] (hc : 0 ≤ c)
    (f : MvPowerSeries.Restricted R c) (h : gaussNorm R c f ≠ 0) :
    {a | MvPowerSeries.AchievesGaussNorm norm c f.1 a}.Finite := by
  simp_rw [MvPowerSeries.AchievesGaussNorm]
  have hpos : 0 < gaussNorm R c f :=
      (MvPowerSeries.gaussNorm_nonneg norm c f.1 norm_nonneg).lt_of_ne' h
  have hfin : {t | gaussNorm R c f / 2 ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·)}.Finite := by
      have : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
      simp_rw [MvPowerSeries.IsRestrictedGauss, NormedAddGroup.tendsto_nhds_zero] at this
      have := this (gaussNorm R c f / 2) (by aesop)
      simp only [norm_mul, Real.norm_eq_abs, Filter.eventually_cofinite, not_lt, abs_norm] at this
      convert this with t
      grind [foo c hc t]
  refine Set.Finite.subset hfin ?_
  grind

lemma test (hc : ∀ (i : σ), 0 < c i) : 0 ≤ c := by
  intro i
  exact Std.le_of_lt (hc i)

lemma bar [NormedRing R] [IsUltrametricDist R] [LinearOrder σ] (hc : ∀ i, 0 < c i)
    (f g : MvPowerSeries.Restricted R c) (hf : gaussNorm R c f ≠ 0) (hg : gaussNorm R c g ≠ 0) :
    ∃ i j, MvPowerSeries.AchievesGaussNorm norm c f.1 i ∧
      MvPowerSeries.AchievesGaussNorm norm c g.1 j ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
      norm (MvPowerSeries.coeff p.1 f.1 * MvPowerSeries.coeff p.2 g.1) <
      norm (MvPowerSeries.coeff i f.1) * norm (MvPowerSeries.coeff j g.1) := by
  -- need to work out how to convert and clean the proof from before
  sorry

noncomputable
instance isAbsoluteValue [NormedRing R] [IsUltrametricDist R] [LinearOrder σ] [StrongPos c]
    (hnorm : ∀ a b : R, norm (a * b) = norm a * norm b) : IsAbsoluteValue (gaussNorm R c) where
  abv_nonneg' g := MvPowerSeries.gaussNorm_nonneg norm c g.1 norm_nonneg
  abv_eq_zero' := by
    intro g
    convert MvPowerSeries.gaussNorm_eq_zero_iff norm c g.1 norm_zero norm_nonneg (by aesop)
      (StrongPos_pos c) (hasGaussNorm c g)
    aesop
  abv_add' f g := (MvPowerSeries.gaussNorm_add_le_max norm c f.1 g.1 (StrongLT.le (StrongPos_pos c))
    norm_nonneg IsUltrametricDist.norm_add_le_max (hasGaussNorm c f) (hasGaussNorm c g)).trans
    (max_le_add_of_nonneg (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
    (MvPowerSeries.gaussNorm_nonneg norm c _ norm_nonneg))
  abv_mul' f g := by
    by_cases h1 : gaussNorm R c f = 0
    · simp [h1]
      suffices f * g = 0 by
        simpa [this] using MvPowerSeries.gaussNorm_zero norm c norm_zero
      suffices f = 0 by
        grind
      convert (MvPowerSeries.gaussNorm_eq_zero_iff norm c f.1 norm_zero norm_nonneg (by aesop)
        (StrongPos_pos c) (hasGaussNorm c f)).mp h1
      aesop
    by_cases h2 : gaussNorm R c g = 0
    · simp [h2]
      suffices f * g = 0 by
        simpa [this] using MvPowerSeries.gaussNorm_zero norm c norm_zero
      suffices g = 0 by
        grind
      convert (MvPowerSeries.gaussNorm_eq_zero_iff norm c g.1 norm_zero norm_nonneg (by aesop)
        (StrongPos_pos c) (hasGaussNorm c g)).mp h2
      aesop
    exact MvPowerSeries.gaussNorm_mul_eq_mul norm c f.1 g.1 (hasGaussNorm c f) (hasGaussNorm c g)
      (hasGaussNorm c (f * g)) norm_nonneg norm_zero IsUltrametricDist.isNonarchimedean_norm hnorm
      norm_neg (by aesop) (StrongPos_pos c) (bar c (StrongPos_pos c) f g h1 h2)

end AbsoluteValue

end MvRestricted

section MvPolynomial

lemma MvPolynomial.IsRestrictedGauss [NormedCommRing R] [IsUltrametricDist R] (f : MvPolynomial σ R) :
    MvPowerSeries.IsRestrictedGauss c f.toMvPowerSeries := by
  suffices {t | ¬ (‖(MvPowerSeries.coeff t) f.toMvPowerSeries‖ * t.prod (c · ^ ·) = 0)}.Finite by
    exact tendsto_nhds_of_eventually_eq this
  simp only [coeff_coe, mul_eq_zero, norm_eq_zero, not_or, ← mem_support_iff]
  exact Set.Finite.sep (Finset.finite_toSet _) _

def MvPolynomial.toMvRestricted [NormedCommRing R] [IsUltrametricDist R] [StrongPos c]
    (f : MvPolynomial σ R) : MvPowerSeries.Restricted R c :=
  ⟨f.toMvPowerSeries, MvPolynomial.IsRestrictedGauss c f⟩

end MvPolynomial
