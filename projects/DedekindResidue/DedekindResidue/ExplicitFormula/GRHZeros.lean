/-
DedekindResidue: GRH pins the zeros of the entire completion to the critical line.

Under `GeneralizedRiemannHypothesis K`, every zero `ρ` of
`completedDedekindZetaEntire K` has `Re ρ = 1/2`: zeros with `Re > 1/2` are excluded
directly (away from `s = 1`, where the entire completion does not vanish), and zeros
with `Re < 1/2` reflect through the functional equation. This is the bridge between
the zero-capture sums of the explicit formula and Belabas–Friedman's critical-line
sums over `γ_ρ = Im ρ`.
-/
module

public import Mathlib
public import DedekindResidue.ExplicitFormula.ZeroCapture
public import DedekindResidue.CompletedZeta.GRH

@[expose] public section

namespace DedekindResidue

open Complex NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The theta constant term `h·w⁻¹·vol` is positive. -/
theorem heckeFConst_pos : 0 < heckeFConst K := by
  rw [heckeFConst]
  have h1 : 0 < (Fintype.card (ClassGroup (𝓞 K)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have h2 := unitBoxVol_pos K
  have h3 : 0 < ((NumberField.Units.torsionOrder K : ℕ) : ℝ) := by
    exact_mod_cast NumberField.Units.torsionOrder_pos K
  positivity

/-- The entire completion does not vanish at `1`: its value there is `2g₀/adjust`,
a positive multiple of the class-number–regulator constant. -/
theorem completedDedekindZetaEntire_one_ne_zero :
    completedDedekindZetaEntire K 1 ≠ 0 := by
  have hval : completedDedekindZetaEntire K 1
      = ((heckeAdjust K : ℝ) : ℂ)⁻¹ * (2 * ((heckeFConst K : ℝ) : ℂ)) := by
    rw [completedDedekindZetaEntire]
    have hg : (heckeFEPair K).g₀ = ((heckeFConst K : ℝ) : ℂ) := rfl
    rw [hg]
    ring
  rw [hval]
  refine mul_ne_zero (inv_ne_zero ?_) (mul_ne_zero two_ne_zero ?_)
  · exact_mod_cast (heckeAdjust_pos K).ne'
  · exact_mod_cast (heckeFConst_pos K).ne'

/-- The entire completion does not vanish at `0`: its value there is `2f₀/adjust`. -/
theorem completedDedekindZetaEntire_zero_ne_zero :
    completedDedekindZetaEntire K 0 ≠ 0 := by
  have hval : completedDedekindZetaEntire K 0
      = ((heckeAdjust K : ℝ) : ℂ)⁻¹ * (2 * ((heckeFConst K : ℝ) : ℂ)) := by
    rw [completedDedekindZetaEntire]
    have hf : (heckeFEPair K).f₀ = ((heckeFConst K : ℝ) : ℂ) := rfl
    rw [hf]
    ring
  rw [hval]
  refine mul_ne_zero (inv_ne_zero ?_) (mul_ne_zero two_ne_zero ?_)
  · exact_mod_cast (heckeAdjust_pos K).ne'
  · exact_mod_cast (heckeFConst_pos K).ne'

/-- **GRH pins the zeros to the critical line**: every zero of the entire completion
has real part `1/2`. -/
theorem re_eq_half_of_completedDedekindZetaEntire_eq_zero
    (hGRH : GeneralizedRiemannHypothesis K) {ρ : ℂ}
    (hρ : completedDedekindZetaEntire K ρ = 0) : ρ.re = 1/2 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    exact completedDedekindZetaEntire_zero_ne_zero K (h ▸ hρ)
  have hρ1 : ρ ≠ 1 := by
    intro h
    exact completedDedekindZetaEntire_one_ne_zero K (h ▸ hρ)
  have hiff := (generalizedRiemannHypothesis_iff K).mp hGRH
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Re ρ < 1/2 : reflect through the functional equation
    have h2 : completedDedekindZetaEntire K (1 - ρ) = 0 := by
      rw [completedDedekindZetaEntire_one_sub]
      exact hρ
    have h10 : (1:ℂ) - ρ ≠ 0 := by
      intro h
      exact hρ1 (by linear_combination -h)
    have h11 : (1:ℂ) - ρ ≠ 1 := by
      intro h
      exact hρ0 (by linear_combination -h)
    have h6 := h2
    rw [completedDedekindZetaEntire_eq K h10 h11] at h6
    have h5 : (1 - ρ) * ((1 - ρ) - 1) ≠ 0 :=
      mul_ne_zero h10 (sub_ne_zero.mpr h11)
    have h3 : completedDedekindZeta K (1 - ρ) = 0 := by
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact absurd h7 h5
      · exact h7
    refine hiff (1 - ρ) ?_ h11 h3
    rw [Complex.sub_re, Complex.one_re]
    linarith
  · -- Re ρ > 1/2 : excluded directly
    have h6 := hρ
    rw [completedDedekindZetaEntire_eq K hρ0 hρ1] at h6
    have h5 : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
    have h3 : completedDedekindZeta K ρ = 0 := by
      rcases mul_eq_zero.mp h6 with h7 | h7
      · exact absurd h7 h5
      · exact h7
    exact hiff ρ hgt hρ1 h3

/-- **The global zero divisor** of the entire completion (order at each point, as a
`ℤ`-valued function on `ℂ`). Since the divisor's value at an interior point is the
local order, this agrees with every window divisor on the window. -/
noncomputable def zetaZeroDivisor : ℂ → ℤ :=
  MeromorphicOn.divisor (completedDedekindZetaEntire K) Set.univ

/-- The global divisor's support is locally finite. -/
theorem locallyFiniteSupport_zetaZeroDivisor :
    LocallyFiniteSupport (zetaZeroDivisor K) := by
  intro z
  obtain ⟨t, ht, hfin⟩ :=
    (MeromorphicOn.divisor (completedDedekindZetaEntire K)
      Set.univ).supportLocallyFiniteWithinDomain z (Set.mem_univ z)
  exact ⟨t, ht, hfin⟩

/-- **The zero set is countable**: the support of the global divisor is a countable
subset of `ℂ` (locally finite ⟹ finite on each closed ball ⟹ countable union). -/
theorem countable_support_zetaZeroDivisor :
    (Function.support (zetaZeroDivisor K)).Countable := by
  have hfin : ∀ n : ℕ,
      (Metric.closedBall (0:ℂ) n ∩ Function.support (zetaZeroDivisor K)).Finite :=
    fun n => (locallyFiniteSupport_zetaZeroDivisor K).finite_inter_support_of_isCompact
      (isCompact_closedBall 0 n)
  have hcover : Function.support (zetaZeroDivisor K)
      = ⋃ n : ℕ, (Metric.closedBall (0:ℂ) n ∩ Function.support (zetaZeroDivisor K)) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge (dist z 0)
      exact ⟨n, hn, hz⟩
    · rintro ⟨n, _, hz⟩
      exact hz
  rw [hcover]
  exact Set.countable_iUnion (fun n => (hfin n).countable)

/-- **The zero index**: the subtype of points where the global divisor is nonzero
(equivalently, the zeros of the entire completion, carrying their multiplicities
through the divisor value). -/
def ZetaZeros : Type _ := {ρ : ℂ // zetaZeroDivisor K ρ ≠ 0}

instance : Countable (ZetaZeros K) := by
  have h := (countable_support_zetaZeroDivisor K).to_subtype
  exact h

/-- Membership in the zero index is equivalent to being a zero of the entire
completion. -/
theorem zetaZeroDivisor_ne_zero_iff {ρ : ℂ} :
    zetaZeroDivisor K ρ ≠ 0 ↔ completedDedekindZetaEntire K ρ = 0 := by
  constructor
  · intro h
    exact completedDedekindZetaEntire_eq_zero_of_divisor_ne_zero K (U := Set.univ) h
  · intro h
    exact divisor_ne_zero_of_completedDedekindZetaEntire_eq_zero K (Set.mem_univ ρ) h

/-- **Under GRH every indexed zero sits on the critical line.** -/
theorem ZetaZeros_re_eq_half (hGRH : GeneralizedRiemannHypothesis K)
    (ρ : ZetaZeros K) : (ρ.1).re = 1/2 :=
  re_eq_half_of_completedDedekindZetaEntire_eq_zero K hGRH
    ((zetaZeroDivisor_ne_zero_iff K).mp ρ.2)

/-- The window divisors agree with the global divisor on their windows. -/
theorem divisor_apply_eq_zetaZeroDivisor {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    (MeromorphicOn.divisor (completedDedekindZetaEntire K) U) u
      = zetaZeroDivisor K u := by
  have hm : ∀ (V : Set ℂ), MeromorphicOn (completedDedekindZetaEntire K) V :=
    fun V ζ _ => ((differentiable_completedDedekindZetaEntire K).analyticAt ζ).meromorphicAt
  rw [MeromorphicOn.divisor_apply (hm U) hu, zetaZeroDivisor,
    MeromorphicOn.divisor_apply (hm Set.univ) (Set.mem_univ u)]

/-- The global divisor is nonnegative (the completion is entire). -/
theorem zetaZeroDivisor_nonneg (u : ℂ) : 0 ≤ zetaZeroDivisor K u := by
  rw [zetaZeroDivisor]
  exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ =>
    (differentiable_completedDedekindZetaEntire K).analyticAt ζ)) u

/-- A finite family of indexed zeros inside a closed ball contributes at most the
ball's divisor finsum. -/
theorem sum_zetaZeroDivisor_le_ball_finsum (c₀ : ℂ) (r : ℝ)
    (u : Finset (ZetaZeros K)) (hu : ∀ ρ ∈ u, (ρ : ZetaZeros K).1 ∈ Metric.closedBall c₀ r) :
    (∑ ρ ∈ u, zetaZeroDivisor K ρ.1)
      ≤ ∑ᶠ z, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
          (Metric.closedBall c₀ r)) z := by
  classical
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ := fun ζ =>
    (differentiable_completedDedekindZetaEntire K).analyticAt ζ
  set Dcl : ℂ → ℤ := fun z => (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.closedBall c₀ r)) z with hDcl
  have hmcl : MeromorphicOn (completedDedekindZetaEntire K) (Metric.closedBall c₀ r) :=
    fun ζ _ => (hHanal ζ).meromorphicAt
  have hfin : (Function.support Dcl).Finite :=
    MeromorphicOn.divisor_support_finite_of_subset hmcl
      (isCompact_closedBall c₀ r) subset_rfl
  have hDclnn : ∀ z, 0 ≤ Dcl z := fun z =>
    (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) z
  have hagree : ∀ ρ ∈ u, Dcl (ρ : ZetaZeros K).1 = zetaZeroDivisor K (ρ : ZetaZeros K).1 := by
    intro ρ hρ
    exact divisor_apply_eq_zetaZeroDivisor K (hu ρ hρ)
  -- pass to the image in ℂ
  have hinj : Set.InjOn (fun ρ : ZetaZeros K => ρ.1) u := by
    intro ρ _ ρ' _ h
    exact Subtype.ext h
  have himg : (∑ ρ ∈ u, zetaZeroDivisor K ρ.1)
      = ∑ z ∈ u.image (fun ρ : ZetaZeros K => ρ.1), zetaZeroDivisor K z :=
    (Finset.sum_image (fun ρ hρ ρ' hρ' h => hinj hρ hρ' h)).symm
  have hsub : u.image (fun ρ : ZetaZeros K => ρ.1) ⊆ hfin.toFinset := by
    intro z hz
    obtain ⟨ρ, hρu, rfl⟩ := Finset.mem_image.mp hz
    refine hfin.mem_toFinset.mpr (Function.mem_support.mpr ?_)
    rw [hagree ρ hρu]
    exact ρ.2
  calc (∑ ρ ∈ u, zetaZeroDivisor K ρ.1)
      = ∑ z ∈ u.image (fun ρ : ZetaZeros K => ρ.1), zetaZeroDivisor K z := himg
    _ = ∑ z ∈ u.image (fun ρ : ZetaZeros K => ρ.1), Dcl z := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        obtain ⟨ρ, hρu, rfl⟩ := Finset.mem_image.mp hz
        exact (hagree ρ hρu).symm
    _ ≤ ∑ z ∈ hfin.toFinset, Dcl z :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hDclnn z)
    _ = ∑ᶠ z, Dcl z := (finsum_eq_sum Dcl hfin).symm

/-- **The unit-slab zero count** (Jensen counting made summation-ready): there is a
constant `C` with: for every `n`, any finite family of indexed zeros with ordinates
in `[n, n+1]` (either sign) has divisor-weighted count at most `C·log(3+n)`. -/
theorem exists_slab_zetaZeroDivisor_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ u : Finset (ZetaZeros K),
      (∀ ρ ∈ u, (n:ℝ) ≤ |((ρ : ZetaZeros K).1).im| ∧ |((ρ : ZetaZeros K).1).im| ≤ n+1) →
      (∑ ρ ∈ u, (zetaZeroDivisor K ρ.1 : ℝ)) ≤ C * Real.log (3+n) := by
  classical
  obtain ⟨A, hA2, cL, hcL, hlow⟩ := exists_H_center_lower K
  obtain ⟨Cc, hCc, hcount⟩ := exists_ball_zero_count_big K A hA2 cL hcL hlow
  have hHanal : ∀ ζ : ℂ, AnalyticAt ℂ (completedDedekindZetaEntire K) ζ := fun ζ =>
    (differentiable_completedDedekindZetaEntire K).analyticAt ζ
  -- the fixed-zone constant
  set C₀ : ℤ := ∑ᶠ z, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
    (Metric.closedBall (0:ℂ) (A+8))) z with hC₀
  have hC₀nn : (0:ℤ) ≤ C₀ := by
    rw [hC₀]
    have hm : MeromorphicOn (completedDedekindZetaEntire K)
        (Metric.closedBall (0:ℂ) (A+8)) := fun ζ _ => (hHanal ζ).meromorphicAt
    have hfin : (Function.support (fun z => (MeromorphicOn.divisor
        (completedDedekindZetaEntire K) (Metric.closedBall (0:ℂ) (A+8))) z)).Finite :=
      MeromorphicOn.divisor_support_finite_of_subset hm
        (isCompact_closedBall (0:ℂ) (A+8)) subset_rfl
    rw [finsum_eq_sum _ hfin]
    refine Finset.sum_nonneg (fun z _ => ?_)
    exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun ζ _ => hHanal ζ)) z
  refine ⟨2*Cc + (C₀ : ℝ) + 1, by positivity, fun n u hu => ?_⟩
  -- basic facts about the zeros in `u`
  have hz : ∀ ρ ∈ u, completedDedekindZetaEntire K ((ρ : ZetaZeros K).1) = 0 :=
    fun ρ _ => (zetaZeroDivisor_ne_zero_iff K).mp ρ.2
  have hre : ∀ ρ ∈ u, 0 ≤ ((ρ : ZetaZeros K).1).re ∧ ((ρ : ZetaZeros K).1).re ≤ 1 :=
    fun ρ hρ => re_mem_of_completedDedekindZetaEntire_eq_zero K (hz ρ hρ)
  have hlog3 : (1:ℝ) ≤ Real.log (3+n) := by
    have he : Real.exp 1 ≤ 3 + (n:ℝ) := by
      have := Real.exp_one_lt_d9
      have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (3+n) := Real.log_le_log (Real.exp_pos 1) he
  rcases le_or_gt (A + 5) (n:ℝ) with hbig | hsmall
  · -- large slab: two balls at heights ±(n + 1/2)
    set upos := u.filter (fun ρ : ZetaZeros K => 0 ≤ (ρ.1).im) with hupos
    set uneg := u.filter (fun ρ : ZetaZeros K => ¬ 0 ≤ (ρ.1).im) with huneg
    have hsplit : (∑ ρ ∈ u, (zetaZeroDivisor K ρ.1 : ℝ))
        = (∑ ρ ∈ upos, (zetaZeroDivisor K ρ.1 : ℝ))
          + ∑ ρ ∈ uneg, (zetaZeroDivisor K ρ.1 : ℝ) := by
      rw [hupos, huneg]
      exact (Finset.sum_filter_add_sum_filter_not u _ _).symm
    have hball : ∀ (Tc : ℝ), |Tc| = (n:ℝ) + 1/2 →
        ∀ (v : Finset (ZetaZeros K)), v ⊆ u →
        (∀ ρ ∈ v, |((ρ : ZetaZeros K).1).im - Tc| ≤ 1/2) →
        (∑ ρ ∈ v, (zetaZeroDivisor K ρ.1 : ℝ)) ≤ Cc * Real.log (3+n) := by
      intro Tc hTc v hvu hvim
      have hmem : ∀ ρ ∈ v, (ρ : ZetaZeros K).1
          ∈ Metric.closedBall ((A:ℂ) + (Tc:ℂ)*Complex.I) (A+2) := by
        intro ρ hρ
        exact Metric.mem_closedBall.mpr (by
          have hreρ := hre ρ (hvu hρ)
          have himρ := hvim ρ hρ
          rw [dist_eq_norm]
          have hsq : ‖(ρ : ZetaZeros K).1 - ((A:ℂ) + (Tc:ℂ)*Complex.I)‖^2
              = ((ρ.1).re - A)^2 + ((ρ.1).im - Tc)^2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
            simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
              Complex.mul_re, Complex.mul_im]
            ring
          have h2 : ((ρ.1).re - A)^2 ≤ A^2 := by nlinarith [hreρ.1, hreρ.2]
          have h3 : ((ρ.1).im - Tc)^2 ≤ (1/2)^2 := by
            have := abs_le.mp himρ
            nlinarith [this.1, this.2]
          nlinarith [norm_nonneg ((ρ : ZetaZeros K).1 - ((A:ℂ) + (Tc:ℂ)*Complex.I)),
            hsq])
      have hint := sum_zetaZeroDivisor_le_ball_finsum K
        ((A:ℂ) + (Tc:ℂ)*Complex.I) (A+2) v hmem
      have hcnt := hcount Tc (by rw [hTc]; linarith)
      have hlogle : Real.log (2 + |Tc|) ≤ Real.log (3+n) := by
        refine Real.log_le_log (by rw [hTc]; linarith) ?_
        rw [hTc]
        linarith
      calc (∑ ρ ∈ v, (zetaZeroDivisor K ρ.1 : ℝ))
          = ((∑ ρ ∈ v, zetaZeroDivisor K ρ.1 : ℤ) : ℝ) := by push_cast; rfl
        _ ≤ ((∑ᶠ z, (MeromorphicOn.divisor (completedDedekindZetaEntire K)
              (Metric.closedBall ((A:ℂ) + (Tc:ℂ)*Complex.I) (A+2))) z : ℤ) : ℝ) := by
            exact_mod_cast hint
        _ ≤ Cc * Real.log (2 + |Tc|) := hcnt
        _ ≤ Cc * Real.log (3+n) := mul_le_mul_of_nonneg_left hlogle hCc.le
    have hpos : (∑ ρ ∈ upos, (zetaZeroDivisor K ρ.1 : ℝ)) ≤ Cc * Real.log (3+n) := by
      refine hball ((n:ℝ) + 1/2) (abs_of_pos (by positivity)) upos
        (Finset.filter_subset _ _) (fun ρ hρ => ?_)
      have h1 := hu ρ (Finset.filter_subset _ _ hρ)
      have h2 : 0 ≤ (ρ.1).im := (Finset.mem_filter.mp hρ).2
      rw [abs_of_nonneg h2] at h1
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    have hneg : (∑ ρ ∈ uneg, (zetaZeroDivisor K ρ.1 : ℝ)) ≤ Cc * Real.log (3+n) := by
      refine hball (-((n:ℝ) + 1/2)) (by rw [abs_neg]; exact abs_of_pos (by positivity))
        uneg (Finset.filter_subset _ _) (fun ρ hρ => ?_)
      have h1 := hu ρ (Finset.filter_subset _ _ hρ)
      have h2 : ¬ 0 ≤ (ρ.1).im := (Finset.mem_filter.mp hρ).2
      push Not at h2
      rw [abs_of_neg h2] at h1
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    have hCnn : 0 ≤ Cc * Real.log (3+n) := by
      refine mul_nonneg hCc.le (by linarith)
    calc (∑ ρ ∈ u, (zetaZeroDivisor K ρ.1 : ℝ))
        ≤ Cc * Real.log (3+n) + Cc * Real.log (3+n) := by
          rw [hsplit]
          exact add_le_add hpos hneg
      _ = 2*Cc * Real.log (3+n) := by ring
      _ ≤ (2*Cc + (C₀ : ℝ) + 1) * Real.log (3+n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          have : (0:ℝ) ≤ (C₀:ℝ) := by exact_mod_cast hC₀nn
          linarith
  · -- small slab: one fixed ball
    have hmem : ∀ ρ ∈ u, (ρ : ZetaZeros K).1 ∈ Metric.closedBall (0:ℂ) (A+8) := by
      intro ρ hρ
      have hreρ := hre ρ hρ
      have himρ := hu ρ hρ
      refine Metric.mem_closedBall.mpr ?_
      rw [dist_zero_right]
      have hsq : ‖(ρ : ZetaZeros K).1‖^2 = (ρ.1).re^2 + (ρ.1).im^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      have h2 : (ρ.1).re^2 ≤ 1 := by nlinarith [hreρ.1, hreρ.2]
      have h3 : (ρ.1).im^2 ≤ ((n:ℝ)+1)^2 := by
        have h4 := himρ.2
        have h5 := abs_nonneg ((ρ.1).im)
        nlinarith [neg_abs_le ((ρ.1).im), le_abs_self ((ρ.1).im)]
      have h6 : ((n:ℝ)+1)^2 ≤ (A+6)^2 := by nlinarith
      nlinarith [norm_nonneg ((ρ : ZetaZeros K).1), hsq]
    have hint := sum_zetaZeroDivisor_le_ball_finsum K (0:ℂ) (A+8) u hmem
    calc (∑ ρ ∈ u, (zetaZeroDivisor K ρ.1 : ℝ))
        = ((∑ ρ ∈ u, zetaZeroDivisor K ρ.1 : ℤ) : ℝ) := by push_cast; rfl
      _ ≤ ((C₀ : ℤ) : ℝ) := by
          rw [hC₀]
          exact_mod_cast hint
      _ ≤ (2*Cc + (C₀ : ℝ) + 1) * 1 := by
          have h7 : (0:ℝ) < Cc := hCc
          nlinarith
      _ ≤ (2*Cc + (C₀ : ℝ) + 1) * Real.log (3+n) := by
          refine mul_le_mul_of_nonneg_left hlog3 ?_
          have : (0:ℝ) ≤ (C₀:ℝ) := by exact_mod_cast hC₀nn
          linarith

/-- The slab-count majorant series `∑ log(3+n)/(h²+n²)` converges
(`log(3+n) ≤ 2√(n+1+ ...)` elementary, no asymptotics). -/
theorem summable_log_div_sq (h : ℝ) (hh : 0 < h) :
    Summable (fun n : ℕ => Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) := by
  set c₁ : ℝ := min (h^2) (1/4) with hc₁
  have hc₁0 : 0 < c₁ := by
    rw [hc₁]
    exact lt_min (by positivity) (by norm_num)
  have hbase : Summable (fun n : ℕ => (((n:ℝ)+1)) ^ (-(3/2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n:ℝ)) ^ (-(3/2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    have h1 := (summable_nat_add_iff 1).mpr h0
    refine h1.congr (fun n => ?_)
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((hbase.mul_left (4/c₁)))
  · have hlog : 0 ≤ Real.log (3+(n:ℝ)) := by
      refine Real.log_nonneg ?_
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    positivity
  · have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    -- log(3+n) ≤ 2√(3+n) ≤ 4√(n+1)
    have hlog2 : Real.log (3+(n:ℝ)) ≤ 2 * Real.sqrt (3+(n:ℝ)) := by
      have hs : Real.sqrt (3+(n:ℝ)) ^ 2 = 3+(n:ℝ) := Real.sq_sqrt (by linarith)
      have hspos : 0 < Real.sqrt (3+(n:ℝ)) := Real.sqrt_pos.mpr (by linarith)
      calc Real.log (3+(n:ℝ)) = Real.log ((Real.sqrt (3+(n:ℝ)))^2) := by rw [hs]
        _ = 2 * Real.log (Real.sqrt (3+(n:ℝ))) := by
            rw [Real.log_pow]
            push_cast
            ring
        _ ≤ 2 * (Real.sqrt (3+(n:ℝ)) - 1) := by
            have := Real.log_le_sub_one_of_pos hspos
            linarith
        _ ≤ 2 * Real.sqrt (3+(n:ℝ)) := by linarith
    have hsqrt : Real.sqrt (3+(n:ℝ)) ≤ 2 * Real.sqrt ((n:ℝ)+1) := by
      have h44 : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      rw [show (2:ℝ) * Real.sqrt ((n:ℝ)+1) = Real.sqrt (4*((n:ℝ)+1)) by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), h44]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : c₁ * ((n:ℝ)+1)^2 ≤ h^2 + (n:ℝ)^2 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp only [Nat.cast_zero]
        have : c₁ ≤ h^2 := min_le_left _ _
        nlinarith
      · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast h0
        have h4 : c₁ ≤ 1/4 := min_le_right _ _
        nlinarith
    have hpos : 0 < h^2 + (n:ℝ)^2 := by positivity
    have hpos2 : 0 < c₁ * ((n:ℝ)+1)^2 := by positivity
    calc Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)
        ≤ (4 * Real.sqrt ((n:ℝ)+1)) / (c₁ * ((n:ℝ)+1)^2) := by
          refine div_le_div₀ ?_ ?_ hpos2 hden
          · positivity
          · calc Real.log (3+(n:ℝ)) ≤ 2 * Real.sqrt (3+(n:ℝ)) := hlog2
              _ ≤ 2 * (2 * Real.sqrt ((n:ℝ)+1)) := by
                  refine mul_le_mul_of_nonneg_left hsqrt (by norm_num)
              _ = 4 * Real.sqrt ((n:ℝ)+1) := by ring
      _ = (4/c₁) * (Real.sqrt ((n:ℝ)+1) / ((n:ℝ)+1)^2) := by
          field_simp
      _ = (4/c₁) * (((n:ℝ)+1)) ^ (-(3/2 : ℝ)) := by
          congr 1
          rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ)+1),
            show (3/2:ℝ) = 1/2 + 1 by norm_num,
            Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ)+1),
            Real.rpow_one, ← Real.sqrt_eq_rpow]
          have hs2 : Real.sqrt ((n:ℝ)+1) * Real.sqrt ((n:ℝ)+1) = (n:ℝ)+1 :=
            Real.mul_self_sqrt (by positivity)
          have hsne : Real.sqrt ((n:ℝ)+1) ≠ 0 := by positivity
          have hne : ((n:ℝ)+1) ≠ 0 := by positivity
          field_simp
          linear_combination hs2

/-- **Landau-type absolute convergence over the zero index**: for every `h > 0`,
`∑_ρ div(ρ)/(h² + γ_ρ²)` converges. -/
theorem summable_zetaZeros_inv_sq (h : ℝ) (hh : 0 < h) :
    Summable (fun ρ : ZetaZeros K =>
      (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2)) := by
  classical
  obtain ⟨C, hC, hslab⟩ := exists_slab_zetaZeroDivisor_sum_le K
  have hnn : ∀ ρ : ZetaZeros K,
      0 ≤ (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2) := by
    intro ρ
    have h1 : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
      exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
    positivity
  have hmaj : Summable (fun n : ℕ => C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2))) :=
    (summable_log_div_sq h hh).mul_left C
  set ctot : ℝ := ∑' n : ℕ, C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) with hctot
  refine summable_of_sum_le (c := ctot) (fun ρ => hnn ρ) (fun v => ?_)
  -- partition the finite family by ⌊|γ|⌋
  set g : ZetaZeros K → ℕ := fun ρ => ⌊|((ρ : ZetaZeros K).1).im|⌋₊ with hg
  have hmaps : ∀ ρ ∈ v, g ρ ∈ v.image g := fun ρ hρ => Finset.mem_image_of_mem g hρ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ n ∈ v.image g,
      (∑ ρ ∈ v.filter (fun ρ => g ρ = n),
        (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2))
      ≤ C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) := by
    intro n _
    have hbound : ∀ ρ ∈ v.filter (fun ρ => g ρ = n),
        (n:ℝ) ≤ |((ρ : ZetaZeros K).1).im| ∧ |((ρ : ZetaZeros K).1).im| ≤ n+1 := by
      intro ρ hρ
      have hgn : g ρ = n := (Finset.mem_filter.mp hρ).2
      rw [hg] at hgn
      constructor
      · rw [← hgn]
        exact Nat.floor_le (abs_nonneg _)
      · rw [← hgn]
        exact le_of_lt (Nat.lt_floor_add_one _)
    have hstep : ∀ ρ ∈ v.filter (fun ρ => g ρ = n),
        (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2)
        ≤ (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + (n:ℝ)^2) := by
      intro ρ hρ
      have h1 := (hbound ρ hρ).1
      have h2 : (n:ℝ)^2 ≤ ((ρ : ZetaZeros K).1).im^2 := by
        have h3 := abs_nonneg ((ρ : ZetaZeros K).1).im
        have h4 : (n:ℝ)^2 ≤ |((ρ : ZetaZeros K).1).im|^2 := by nlinarith
        rwa [sq_abs] at h4
      have h5 : (0:ℝ) ≤ (zetaZeroDivisor K ρ.1 : ℝ) := by
        exact_mod_cast zetaZeroDivisor_nonneg K ρ.1
      refine div_le_div_of_nonneg_left h5 (by positivity) ?_
      linarith
    calc (∑ ρ ∈ v.filter (fun ρ => g ρ = n),
          (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2))
        ≤ ∑ ρ ∈ v.filter (fun ρ => g ρ = n),
          (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + (n:ℝ)^2) :=
          Finset.sum_le_sum hstep
      _ = (∑ ρ ∈ v.filter (fun ρ => g ρ = n), (zetaZeroDivisor K ρ.1 : ℝ))
            / (h^2 + (n:ℝ)^2) := by
          rw [Finset.sum_div]
      _ ≤ (C * Real.log (3+(n:ℝ))) / (h^2 + (n:ℝ)^2) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact hslab n _ hbound
      _ = C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) := by ring
  calc (∑ n ∈ v.image g, ∑ ρ ∈ v.filter (fun ρ => g ρ = n),
        (zetaZeroDivisor K ρ.1 : ℝ) / (h^2 + ((ρ : ZetaZeros K).1).im^2))
      ≤ ∑ n ∈ v.image g, C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) :=
        Finset.sum_le_sum hfiber
    _ ≤ ∑' n : ℕ, C * (Real.log (3+(n:ℝ)) / (h^2 + (n:ℝ)^2)) := by
        refine sum_le_hasSum _ (fun n _ => ?_) hmaj.hasSum
        have hlog : 0 ≤ Real.log (3+(n:ℝ)) := by
          refine Real.log_nonneg ?_
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        positivity

end DedekindResidue

end
