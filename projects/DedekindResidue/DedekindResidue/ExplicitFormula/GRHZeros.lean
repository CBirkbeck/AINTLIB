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

end DedekindResidue

end
