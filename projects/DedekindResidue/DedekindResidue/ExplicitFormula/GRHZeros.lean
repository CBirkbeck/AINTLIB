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

end DedekindResidue

end
