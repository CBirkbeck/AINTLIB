import BernoulliRegular.FLT37.PrimaryUnits
import BernoulliRegular.FLT37.CaseI

/-!
# LV010 Stage 1: weak-primary normalization of case-I factor

For FLT case I, the factor `α := a + ζ b` admits a *weak primary* form
after multiplication by an appropriate ζ-power. Specifically: there
exists `k : Fin p` such that `(ζ - 1)^2 ∣ ζ^k · (a + ζ b) - (a + b)` in
`𝓞 K`. Equivalently, `ζ^k · α ≡ a + b (mod (ζ-1)^2)`.

The choice of `k`: from the (ζ-1)¹ Taylor expansion,
`ζ^k · (a + ζ b) ≡ (a + b) + (k(a+b) + b)·(ζ-1) (mod (ζ-1)^2)`.

Hence `(ζ-1)^2 ∣ ζ^k · α - (a+b)` iff `(ζ-1)^2 ∣ (k(a+b) + b)·(ζ-1)`,
iff `(ζ-1) ∣ k(a+b) + b` in `𝓞 K`, iff `p ∣ k(a+b) + b` in `ℤ` (since
`(ζ-1)·𝓞 K ∩ ℤ = pℤ`).

Solving `k(a+b) + b ≡ 0 (mod p)` for `k`: `k ≡ -b · (a+b)⁻¹ (mod p)`.
The inverse exists because `p ∤ (a+b)` under FLT case I (from
`fltCaseI_p_not_dvd_a_add_b`).

This is the *Stage 1* input to Vandiver's class-equality discharge: from
weak primary form, the Kummer-ratio `α'/σα' = β^p` (Stage 2) follows.

## References

* Washington, *Introduction to Cyclotomic Fields*, §9.3 (Vandiver's
  Theorem on case I under VC).
* Existing `zetaSubOne_sq_dvd_factor_sub_taylor`
  (`PrimaryUnits.lean:733`).
* Existing `fltCaseI_p_not_dvd_a_add_b` (`CaseI.lean:279`).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- **Weak primary normalization of `ζ^k · (a + ζ b)`.** Combining the
two-term Taylor expansion via `zetaSubOne_sq_dvd_factor_sub_taylor`:
`(ζ-1)^2 ∣ ζ^k · (a + ζ b) - ((a + b) + (k(a+b) + b)·(ζ-1))`.

This is the (ζ-1)² Taylor expansion of `ζ^k · (a + ζ b)`, with explicit
coefficients in (ζ-1)⁰ = `a+b` and (ζ-1)¹ = `k(a+b) + b`. -/
theorem zetaSubOne_sq_dvd_zeta_pow_mul_factor_sub_taylor
    (a b : ℤ) (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
        ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K))) -
        (((a + b : ℤ) : 𝓞 K) +
          ((k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K)) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) := by
  -- Apply `zetaSubOne_sq_dvd_factor_sub_taylor` to the two summands
  -- `ζ^k · a` (coefficients `0, a, k`) and `ζ^{k+1} · b` (coefficients
  -- `0, b, k+1`), then `dvd_add` and rearrange.
  have hA' := zetaSubOne_sq_dvd_factor_sub_taylor p K 0 a k
  have hB' := zetaSubOne_sq_dvd_factor_sub_taylor p K 0 b (k + 1)
  have hsum := dvd_add hA' hB'
  have hcalc :
      (((0 : ℤ) : 𝓞 K) + (((zeta_spec p ℚ K).toInteger : 𝓞 K)) ^ k * (a : 𝓞 K) -
          (((0 + a : ℤ) : 𝓞 K) + (a : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) +
      (((0 : ℤ) : 𝓞 K) + (((zeta_spec p ℚ K).toInteger : 𝓞 K)) ^ (k + 1) * (b : 𝓞 K) -
          (((0 + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * ((k + 1 : ℕ) : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K))) -
        (((a + b : ℤ) : 𝓞 K) +
          ((k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K)) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by
    push_cast
    ring
  rw [hcalc] at hsum
  exact hsum

/-- **Choice of `k`: weak primary k for case I.** Given `p ∤ (a+b)` (under
case I this holds), there exists `k : ℕ` with `k < p` such that
`p ∣ k·(a+b) + b`, i.e., the (ζ-1)¹ coefficient of
`ζ^k · (a + ζ b) - (a+b)` vanishes mod `p`. -/
theorem caseI_exists_weakPrimary_k_natAbs
    {a b : ℤ} (hab_coprime : ¬ (p : ℤ) ∣ (a + b)) :
    ∃ k : ℕ, k < p ∧ (p : ℤ) ∣ ((k : ℤ) * (a + b) + b) := by
  have h_a_plus_b_zmod : ((a + b : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hab_coprime
  -- Choose `kZ := -b · (a+b)⁻¹` in `ZMod p`; its lift `kZ.val` is the witness.
  set kZ : ZMod p := -((b : ZMod p) * ((a + b : ZMod p)⁻¹)) with hkZ_def
  refine ⟨kZ.val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, hkZ_def]
  have h_apb_zmod' : ((a : ZMod p) + (b : ZMod p)) ≠ 0 := by
    rwa [Int.cast_add] at h_a_plus_b_zmod
  field_simp
  ring

/-- **Stage 1: weak-primary normalization for case-I factor.** Given
the FLT case I hypotheses (`a^p + b^p = c^p`, `p ∤ c`), there exists
`k : Fin p` such that `(ζ-1)^2 ∣ ζ^k · (a + ζ b) - (a+b)`. -/
theorem caseI_exists_zeta_pow_weakPrimary
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) :
    ∃ k : ℕ, k < p ∧
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K)) := by
  have hab_coprime : ¬ (p : ℤ) ∣ (a + b) := fltCaseI_p_not_dvd_a_add_b heq hc
  obtain ⟨k, hk_lt, hk_div⟩ := caseI_exists_weakPrimary_k_natAbs hab_coprime
  refine ⟨k, hk_lt, ?_⟩
  -- The Taylor expansion gives `(ζ-1)² ∣ ζ^k·(a+ζb) - ((a+b) + (k(a+b)+b)·(ζ-1))`;
  -- from `p ∣ k(a+b)+b` we get `(ζ-1) ∣ k(a+b)+b`, hence `(ζ-1)² ∣ (k(a+b)+b)·(ζ-1)`,
  -- and the goal is the sum of the two divisibilities.
  have h_taylor :=
    zetaSubOne_sq_dvd_zeta_pow_mul_factor_sub_taylor (p := p) (K := K) a b k
  have hp_dvd_zeta : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((k : ℤ) * (a + b) + b : ℤ) : 𝓞 K) := by
    rw [zetaSubOne_dvd_intCast_iff]; exact hk_div
  have h_eq_form :
      (((k : ℤ) * (a + b) + b : ℤ) : 𝓞 K) =
        (k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) := by
    push_cast
    ring
  rw [h_eq_form] at hp_dvd_zeta
  have h_ext : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K)) *
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) := by
    rw [pow_two]
    exact mul_dvd_mul_right hp_dvd_zeta _
  have h_eq_target :
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K))) -
        ((a + b : ℤ) : 𝓞 K) =
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) * (b : 𝓞 K))) -
        (((a + b : ℤ) : 𝓞 K) +
          ((k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K)) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) +
      ((k : 𝓞 K) * ((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K)) *
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) := by
    ring
  rw [h_eq_target]
  exact dvd_add h_taylor h_ext

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
