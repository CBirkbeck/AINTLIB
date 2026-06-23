/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Data.Finset.NatDivisors
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Fourier coefficient formula for Hecke operators

States the key Fourier coefficient formulas for the action of Hecke operators
on q-expansions, building on the T_n definitions from `GL2/HeckeT_n.lean`
and Mathlib's q-expansion infrastructure.

## Main results

The Fourier formulas use the canonical period-1 convention (the standard
Miyake / Diamond–Shurman convention), consumed by `Newforms.lean`:

* `fourierCoeff_heckeT_n_period_one` — the general `T_n` Fourier formula
  (DS Prop 5.3.1, period-1 convention):
    `a_m(T_n f) = Σ_{d | gcd(m,n)} d^{k-1} χ(d) a_{mn/d²}(f)`.
* `IsNormalisedEigenform_one` — period-1 normalised-eigenform predicate
  using `(qExpansion (1 : ℝ) f).coeff 1 = 1`, superseding
  `IsNormalisedEigenform` (whose period-`N` condition is vacuous for
  `N > 1`).
* `eigenvalue_eq_fourierCoeff_one`,
  `eigenform_coeff_multiplicative_one` — period-1 bridges consumed by
  `Newforms.lean` via `Newform.eigenvalue_eq_coeff` and
  `Newform.eigenvalue_coprime_mul`.

## Implementation notes

**Normalisation**: Our slash action omits `det^{k-1}`. Consequently:
- `T_p` in our convention equals `p^{1-k} T_p^{DS}`.
- The Fourier formula picks up `p^{1-k}` on the leading term instead of `p^{k-1}`
  on the second term.

**q-expansion API.**  For `f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k`,
the **canonical Fourier period is `h = 1`** — not `N` — because
`ModularGroup.T ∈ Γ₁(N)`, so every `Γ₁(N)`-form is `1`-periodic.  At
`h = 1`, `(qExpansion (1 : ℝ) f).coeff n` is the standard Fourier
coefficient `a_n`.  A period-`N` q-expansion is also well-defined (every
integer is a strict period of `Γ₁(N)`) but is *sparse*: its coefficient
vanishes at every non-multiple of `N`.  The period-`N` formulas in this
file are retained for historical compatibility; the period-1 variants
are the convention used downstream in `Newforms.lean` / `LFunction.lean`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.2 Prop 5.2.2, §5.3 Prop 5.3.1
* [Miy] Miyake, *Modular Forms*, §4.5 Thm 4.5.13, Thm 4.5.16
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
  ModularFormClass UpperHalfPlane

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ}

private theorem gcd_quot_sq_eq {m a b d₁ : ℕ} (hab : Nat.Coprime a b) (hd₁m : d₁ ∣ m)
    (hd₁a : d₁ ∣ a) : (m * a / (d₁ * d₁)).gcd b = m.gcd b := by
  rw [Nat.mul_div_mul_comm hd₁m hd₁a,
    Nat.Coprime.gcd_mul_right_cancel (m / d₁) (hab.coprime_dvd_left (Nat.div_dvd_of_dvd hd₁a))]
  conv_rhs => rw [show m = m / d₁ * d₁ from (Nat.div_mul_cancel hd₁m).symm]
  rw [Nat.Coprime.gcd_mul_right_cancel (m / d₁) (hab.coprime_dvd_left hd₁a)]

private theorem div_sq_product {m a b d₁ d₂ : ℕ} (hd₁ : d₁ * d₁ ∣ m * a) :
    m * (a * b) / (d₁ * d₂ * (d₁ * d₂)) = m * a / (d₁ * d₁) * b / (d₂ * d₂) := by
  rw [show d₁ * d₂ * (d₁ * d₂) = d₁ * d₁ * (d₂ * d₂) by ring,
    show m * (a * b) = m * a * b by ring, ← Nat.div_div_eq_div_mul]
  congr 1
  exact Nat.mul_div_right_comm hd₁ b

private theorem unitOfCoprime_mul {N d₁ d₂ : ℕ} (h₁ : d₁.Coprime N) (h₂ : d₂.Coprime N)
    (h₁₂ : (d₁ * d₂).Coprime N) (χ : (ZMod N)ˣ →* ℂˣ) :
    (↑(χ (ZMod.unitOfCoprime (d₁ * d₂) h₁₂)) : ℂ) =
      ↑(χ (ZMod.unitOfCoprime d₁ h₁)) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) := by
  rw [show χ (ZMod.unitOfCoprime (d₁ * d₂) h₁₂) =
      χ (ZMod.unitOfCoprime d₁ h₁) * χ (ZMod.unitOfCoprime d₂ h₂) by
    rw [← map_mul]
    congr 1
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_mul, Nat.cast_mul]]
  push_cast
  ring

private lemma unitOfCoprime_one_eq_one {N : ℕ} :
    ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
  ext
  simp only [ZMod.coe_unitOfCoprime, Nat.cast_one, Units.val_one]

private lemma chi_unitOfCoprime_one_eq_one {N : ℕ} (χ : (ZMod N)ˣ →* ℂˣ) (h : Nat.Coprime 1 N) :
    (↑(χ (ZMod.unitOfCoprime 1 h)) : ℂ) = 1 := by
  simp only [unitOfCoprime_one_eq_one, map_one, Units.val_one]

lemma one_mem_strictPeriods_Gamma1_map (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

private theorem mul_injOn_divisors_coprime {m a b : ℕ} (hab : Nat.Coprime a b) :
    Set.InjOn (fun p : ℕ × ℕ ↦ p.1 * p.2)
      (↑((m.gcd a).divisors ×ˢ (m.gcd b).divisors)) := by
  intro ⟨d₁, d₂⟩ hd ⟨e₁, e₂⟩ he hmul
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hd he
  have hmul' : d₁ * d₂ = e₁ * e₂ := hmul
  have heq1 : d₁ = e₁ := Nat.dvd_antisymm
    (((hab.coprime_dvd_left
        ((Nat.dvd_of_mem_divisors hd.1).trans (Nat.gcd_dvd_right m a))).coprime_dvd_right
        ((Nat.dvd_of_mem_divisors he.2).trans (Nat.gcd_dvd_right m b))).dvd_of_dvd_mul_right
      (hmul' ▸ dvd_mul_right d₁ d₂))
    (((hab.coprime_dvd_left
        ((Nat.dvd_of_mem_divisors he.1).trans (Nat.gcd_dvd_right m a))).coprime_dvd_right
        ((Nat.dvd_of_mem_divisors hd.2).trans (Nat.gcd_dvd_right m b))).dvd_of_dvd_mul_right
      (hmul'.symm ▸ dvd_mul_right e₁ e₂))
  exact Prod.ext heq1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors hd.1) (heq1 ▸ hmul'))

private theorem divisorSum_coprime_summand {N : ℕ} [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (c : ℕ → ℂ) (m a b d₁ : ℕ) (hd₁sq : d₁ * d₁ ∣ m * a)
    (h_inner : (m * a / (d₁ * d₁)).gcd b = m.gcd b) :
    ∑ d₂ ∈ (m.gcd b).divisors,
      (if h : (d₁ * d₂).Coprime N then
        (↑(d₁ * d₂) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (d₁ * d₂) h)) *
          c (m * (a * b) / (d₁ * d₂ * (d₁ * d₂)))
      else 0) =
    if h₁ : d₁.Coprime N then
      (↑d₁ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₁ h₁)) *
        (∑ d₂ ∈ ((m * a / (d₁ * d₁)).gcd b).divisors,
          if h₂ : d₂.Coprime N then
            (↑d₂ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) *
              c (m * a / (d₁ * d₁) * b / (d₂ * d₂))
          else 0)
    else 0 := by
  by_cases h₁ : d₁.Coprime N
  · rw [dif_pos h₁, h_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ ↦ ?_
    by_cases h₂ : d₂.Coprime N
    · have h₁₂ : (d₁ * d₂).Coprime N := h₁.mul_left h₂
      rw [dif_pos h₁₂, dif_pos h₂, show (↑(d₁ * d₂) : ℂ) = (↑d₁ : ℂ) * ↑d₂ by push_cast; ring,
        mul_zpow, div_sq_product hd₁sq, unitOfCoprime_mul h₁ h₂ h₁₂ χ]
      ring
    · rw [dif_neg fun h ↦ h₂ (h.coprime_dvd_left (dvd_mul_left d₂ d₁)), dif_neg h₂]
      simp only [mul_zero]
  · rw [dif_neg h₁]
    refine Finset.sum_eq_zero fun d₂ _ ↦ ?_
    exact dif_neg fun h ↦ h₁ (h.coprime_dvd_left (dvd_mul_right d₁ d₂))

private theorem divisorSum_coprime_conv {N : ℕ} [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (c : ℕ → ℂ) (m a b : ℕ) (hab : Nat.Coprime a b) :
    ∑ d ∈ (m.gcd (a * b)).divisors,
      (if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * (a * b) / (d * d))
      else 0) =
    ∑ d₁ ∈ (m.gcd a).divisors,
      (if h₁ : d₁.Coprime N then
        (↑d₁ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₁ h₁)) *
          (∑ d₂ ∈ ((m * a / (d₁ * d₁)).gcd b).divisors,
            if h₂ : d₂.Coprime N then
              (↑d₂ : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d₂ h₂)) *
                c (m * a / (d₁ * d₁) * b / (d₂ * d₂))
            else 0)
      else 0) := by
  rw [hab.gcd_mul m, Nat.divisors_mul,
    show (m.gcd a).divisors * (m.gcd b).divisors =
      Finset.image (fun p : ℕ × ℕ ↦ p.1 * p.2)
        ((m.gcd a).divisors ×ˢ (m.gcd b).divisors) by
      ext d
      simp only [Finset.mem_mul, Finset.mem_image, Finset.mem_product]
      exact ⟨fun ⟨x, hx, y, hy, h⟩ ↦ ⟨(x, y), ⟨hx, hy⟩, h⟩,
        fun ⟨⟨x, y⟩, ⟨hx, hy⟩, h⟩ ↦ ⟨x, hx, y, hy, h⟩⟩,
    Finset.sum_image (fun _ ha _ hb h ↦ mul_injOn_divisors_coprime hab ha hb h),
    Finset.sum_product]
  refine Finset.sum_congr rfl fun d₁ hd₁ ↦ ?_
  have hd₁m : d₁ ∣ m := (Nat.dvd_of_mem_divisors hd₁).trans (Nat.gcd_dvd_left m a)
  have hd₁a : d₁ ∣ a := (Nat.dvd_of_mem_divisors hd₁).trans (Nat.gcd_dvd_right m a)
  exact divisorSum_coprime_summand k χ c m a b d₁ (Nat.mul_dvd_mul hd₁m hd₁a)
    (gcd_quot_sq_eq hab hd₁m hd₁a)

private theorem sum_divisors_ppow_eq_range {N : ℕ} (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (c : ℕ → ℂ) (s n : ℕ) :
    (∑ d ∈ (p ^ s).divisors,
      if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) * c (n / (d * d))
      else 0) =
    ∑ j ∈ Finset.range (s + 1),
      (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
        c (n / (p ^ j * p ^ j)) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  exact Finset.sum_congr rfl fun j _ ↦ dif_pos (hpN.pow_left j)

private theorem ppow_summand_factor {N : ℕ} (k : ℤ) {p : ℕ} (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) (c : ℕ → ℂ) (j n : ℕ) :
    (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
        ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hpN.pow_left (j + 1)))) *
        c (n / (p ^ (j + 1) * p ^ (j + 1))) =
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        ((↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
          c (n / (p ^ (j + 1) * p ^ (j + 1)))) := by
  have h_pow : (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) =
      (↑p : ℂ) ^ (k - 1) * (↑(p ^ j) : ℂ) ^ (k - 1) := by
    rw [pow_succ']
    push_cast
    rw [mul_zpow]
  have h_chi : (↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hpN.pow_left (j + 1)))) : ℂ) =
      ↑(χ (ZMod.unitOfCoprime p hpN)) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) := by
    have : ZMod.unitOfCoprime (p ^ (j + 1)) (hpN.pow_left (j + 1)) =
        ZMod.unitOfCoprime p hpN * ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j) := by
      ext
      simp only [ZMod.coe_unitOfCoprime, pow_succ', Units.val_mul, Nat.cast_mul]
    rw [this, map_mul]
    push_cast
    ring
  rw [h_pow, h_chi]
  ring

private theorem ppow_range_sum_factor {N : ℕ} (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (c : ℕ → ℂ) (s m r : ℕ) :
    ∑ j ∈ Finset.range (s + 1),
        (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hpN.pow_left (j + 1)))) *
          c (m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1))) =
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        ∑ j ∈ Finset.range (s + 1),
          (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
            c (m * p ^ r / (p ^ j * p ^ j)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ppow_summand_factor k hpN χ c j (m * p ^ (r + 2)),
    show m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1)) = m * p ^ r / (p ^ j * p ^ j) by
      rw [show p ^ (j + 1) * p ^ (j + 1) = p * p * (p ^ j * p ^ j) by ring,
        show m * p ^ (r + 2) = p * p * (m * p ^ r) by ring]
      exact Nat.mul_div_mul_left _ _ (Nat.mul_pos hp.pos hp.pos)]

private theorem ppow_divisorSum_recurrence_dvd [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (r m : ℕ) (c : ℕ → ℂ) (hdvd : p ∣ m) :
    (((∑ d ∈ ((p * m).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (p * m * p ^ (r + 1) / (d * d))
          else 0) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then
            ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
              if h : d.Coprime N then
                (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                  c (m / p * p ^ (r + 1) / (d * d))
              else 0
          else 0)) -
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        (∑ d ∈ (m.gcd (p ^ r)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (m * p ^ r / (d * d))
          else 0)) =
    ∑ d ∈ (m.gcd (p ^ (r + 2))).divisors,
      if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * p ^ (r + 2) / (d * d))
      else 0 := by
  have gcd_pm : (p * m).gcd (p ^ (r + 1)) = p * m.gcd (p ^ r) := by
    conv_lhs => rw [pow_succ, mul_comm (p ^ r) p]
    exact Nat.gcd_mul_left p m (p ^ r)
  have gcd_is_ppow : ∀ (a v : ℕ), ∃ s, a.gcd (p ^ v) = p ^ s := fun a v ↦
    let ⟨s, _, hs⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right a (p ^ v)); ⟨s, hs⟩
  have gcd_m2 : m.gcd (p ^ (r + 2)) = p * (m / p).gcd (p ^ (r + 1)) := by
    conv_lhs => rw [show m = p * (m / p) from (Nat.mul_div_cancel' hdvd).symm,
      show p ^ (r + 2) = p * p ^ (r + 1) by ring]
    exact Nat.gcd_mul_left p (m / p) (p ^ (r + 1))
  obtain ⟨s₁, hs₁⟩ := gcd_is_ppow m r
  obtain ⟨s₂, hs₂⟩ := gcd_is_ppow (m / p) (r + 1)
  simp only [hdvd, ↓reduceIte]
  rw [gcd_pm, hs₁, gcd_m2, hs₂,
    show p * p ^ s₁ = p ^ (s₁ + 1) from (pow_succ' p s₁).symm,
    show p * p ^ s₂ = p ^ (s₂ + 1) from (pow_succ' p s₂).symm,
    sum_divisors_ppow_eq_range k hp hpN χ c (s₁ + 1) (p * m * p ^ (r + 1)),
    sum_divisors_ppow_eq_range k hp hpN χ c s₂ (m / p * p ^ (r + 1)),
    sum_divisors_ppow_eq_range k hp hpN χ c s₁ (m * p ^ r),
    sum_divisors_ppow_eq_range k hp hpN χ c (s₂ + 1) (m * p ^ (r + 2)),
    Finset.sum_range_succ'
      (fun j ↦ (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
        c (p * m * p ^ (r + 1) / (p ^ j * p ^ j))),
    Finset.sum_range_succ'
      (fun j ↦ (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
        c (m * p ^ (r + 2) / (p ^ j * p ^ j)))]
  simp only [pow_zero, Nat.cast_one, one_zpow, one_mul, chi_unitOfCoprime_one_eq_one χ, Nat.div_one]
  rw [show p * m * p ^ (r + 1) = m * p ^ (r + 2) by ring]
  have h_mp_prod : m / p * p ^ (r + 1) = m * p ^ r := by
    rw [show p ^ (r + 1) = p * p ^ r by ring, ← mul_assoc, Nat.div_mul_cancel hdvd]
  rw [ppow_range_sum_factor k hp hpN χ c s₁ m r,
    show (∑ j ∈ Finset.range (s₂ + 1),
        (↑(p ^ (j + 1)) : ℂ) ^ (k - 1) *
          ↑(χ (ZMod.unitOfCoprime (p ^ (j + 1)) (hpN.pow_left (j + 1)))) *
          c (m * p ^ (r + 2) / (p ^ (j + 1) * p ^ (j + 1)))) =
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        ∑ j ∈ Finset.range (s₂ + 1),
          (↑(p ^ j) : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime (p ^ j) (hpN.pow_left j))) *
            c (m / p * p ^ (r + 1) / (p ^ j * p ^ j)) by
      rw [ppow_range_sum_factor k hp hpN χ c s₂ m r]
      simp_rw [← h_mp_prod]]
  ring

private theorem ppow_divisorSum_recurrence_not_dvd [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (r m : ℕ) (c : ℕ → ℂ) (hdvd : ¬ p ∣ m) :
    (((∑ d ∈ ((p * m).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (p * m * p ^ (r + 1) / (d * d))
          else 0) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then
            ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
              if h : d.Coprime N then
                (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                  c (m / p * p ^ (r + 1) / (d * d))
              else 0
          else 0)) -
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        (∑ d ∈ (m.gcd (p ^ r)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (m * p ^ r / (d * d))
          else 0)) =
    ∑ d ∈ (m.gcd (p ^ (r + 2))).divisors,
      if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * p ^ (r + 2) / (d * d))
      else 0 := by
  have gcd_pm : (p * m).gcd (p ^ (r + 1)) = p * m.gcd (p ^ r) := by
    conv_lhs => rw [pow_succ, mul_comm (p ^ r) p]
    exact Nat.gcd_mul_left p m (p ^ r)
  have gcd_m : ∀ v, m.gcd (p ^ v) = 1 := fun v ↦ Nat.Prime.coprime_pow_of_not_dvd hp hdvd
  have gcd_pm_eq : (p * m).gcd (p ^ (r + 1)) = p := by rw [gcd_pm, gcd_m r, mul_one]
  simp only [hdvd, ↓reduceIte, mul_zero, add_zero]
  rw [gcd_m (r + 2), Nat.divisors_one, Finset.sum_singleton]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true]
  rw [gcd_m r, Nat.divisors_one, Finset.sum_singleton,
    gcd_pm_eq, hp.divisors, Finset.sum_insert (by simp; exact Ne.symm hp.one_lt.ne')]
  simp only [Finset.sum_singleton, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow, one_mul,
    Nat.div_one, hpN]
  rw [show p * m * p ^ (r + 1) / (p * p) = m * p ^ r by
      rw [show p * m * p ^ (r + 1) = p * p * (m * p ^ r) by ring]
      exact Nat.mul_div_cancel_left _ (Nat.mul_pos hp.pos hp.pos),
    show p * m * p ^ (r + 1) = m * p ^ (r + 2) by ring]
  simp only [chi_unitOfCoprime_one_eq_one χ, one_mul]
  ring

private theorem ppow_divisorSum_recurrence [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (r : ℕ) (m : ℕ) (c : ℕ → ℂ) :
    (((∑ d ∈ ((p * m).gcd (p ^ (r + 1))).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (p * m * p ^ (r + 1) / (d * d))
          else 0) +
        (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
          (if p ∣ m then
            ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
              if h : d.Coprime N then
                (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                  c (m / p * p ^ (r + 1) / (d * d))
              else 0
          else 0)) -
      (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        (∑ d ∈ (m.gcd (p ^ r)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              c (m * p ^ r / (d * d))
          else 0)) =
    ∑ d ∈ (m.gcd (p ^ (r + 2))).divisors,
      if h : d.Coprime N then
        (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
          c (m * p ^ (r + 2) / (d * d))
      else 0 := by
  by_cases hdvd : p ∣ m
  · exact ppow_divisorSum_recurrence_dvd k hp hpN χ r m c hdvd
  · exact ppow_divisorSum_recurrence_not_dvd k hp hpN χ r m c hdvd

private theorem heckeT_ppow_preserves_charSpace [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (r : ℕ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  rw [show diamondOpHom k d (heckeT_ppow k p hp r f) =
      heckeT_ppow k p hp r (diamondOpHom k d f) from
    DFunLike.congr_fun (heckeT_ppow_comm_diamondOp k hp hpN r d) f, hf d, map_smul]

private theorem diamondOp_n_charSpace [NeZero N] (k : ℤ) {p : ℕ} (hpN : Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    diamondOp_n k p f = (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) • f := by
  rw [diamondOp_n_coprime k hpN]
  exact (mem_modFormCharSpace_iff k χ f).mp hf (ZMod.unitOfCoprime p hpN)

private theorem coeff_qExpansion_heckeT_ppow_succ_succ [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (r : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ)
    {h : ℝ} (hh0 : 0 < h) (hh : h ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods) (m : ℕ) :
    (qExpansion h (heckeT_ppow k p hp (r + 2) f)).coeff m =
      (qExpansion h (heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f))).coeff m -
        ((↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN))) *
          (qExpansion h (heckeT_ppow k p hp r f)).coeff m := by
  have h_apply : heckeT_ppow k p hp (r + 2) f =
      heckeT_p_all k p hp (heckeT_ppow k p hp (r + 1) f) -
      (↑p : ℂ) ^ (k - 1) • (diamondOp_n k p (heckeT_ppow k p hp r f)) :=
    DFunLike.congr_fun (heckeT_ppow_succ_succ (N := N) k p hp r) f
  rw [diamondOp_n_charSpace k hpN χ (heckeT_ppow_preserves_charSpace k hp hpN r χ hf),
    smul_smul, heckeT_p_all_coprime k hp hpN] at h_apply
  set χp := (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)
  set cpk := (↑p : ℂ) ^ (k - 1)
  have h_coe : (⇑(heckeT_ppow k p hp (r + 2) f) : ℍ → ℂ) =
      ⇑(heckeT_p k p hp hpN (heckeT_ppow k p hp (r + 1) f)) -
      ⇑((cpk * χp) • heckeT_ppow k p hp r f : ModularForm _ k) := by
    rw [ModularForm.IsGLPos.coe_smul]
    exact congr_arg (↑· : ModularForm _ k → ℍ → ℂ) h_apply
  conv_lhs => rw [h_coe]
  rw [ModularForm.qExpansion_sub hh0 hh]
  simp only [map_sub]
  congr 1
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul hh0 hh, PowerSeries.coeff_smul,
    smul_eq_mul]

private abbrev HeckeTpCoeffFormula (k : ℤ) {p N : ℕ} [NeZero N] (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (t : ℝ) : Prop :=
  ∀ (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k), g ∈ modFormCharSpace k χ → ∀ m',
    (qExpansion t (heckeT_p k p hp hpN g)).coeff m' =
      (qExpansion t g).coeff (p * m') + (↑p : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime p hpN)) *
        (if p ∣ m' then (qExpansion t g).coeff (m' / p) else 0)

private theorem fourierCoeff_heckeT_ppow_one_eq [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) {t : ℝ} (hTp : HeckeTpCoeffFormula k hp hpN χ t)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion t (heckeT_ppow k p hp 1 f)).coeff m =
      ∑ d ∈ (Nat.gcd m (p ^ 1)).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * p ^ 1 / (d * d))
        else 0 := by
  rw [pow_one, heckeT_ppow_one_eq_heckeT_p k hp hpN, hTp f hf m]
  by_cases hdvd : p ∣ m
  · rw [Nat.gcd_eq_right hdvd, hp.divisors, Finset.sum_insert (by simp; exact hp.one_lt.ne)]
    simp only [Finset.sum_singleton, Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one,
      one_zpow, unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one, hpN,
      if_pos hdvd]
    rw [Nat.mul_div_mul_right m p hp.pos, Nat.mul_comm p m]
  · rw [(hp.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m p)).resolve_right fun h ↦
        hdvd (h ▸ Nat.gcd_dvd_left m p), Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, unitOfCoprime_one_eq_one, map_one,
      Units.val_one, Nat.cast_one, one_zpow, one_mul, Nat.div_one]
    rw [if_neg hdvd, mul_zero, add_zero, Nat.mul_comm p m]

private theorem fourierCoeff_heckeT_ppow_succ_succ_eq [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) {t : ℝ} (ht0 : 0 < t)
    (ht : t ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods) (hTp : HeckeTpCoeffFormula k hp hpN χ t)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (r m : ℕ)
    (ih1 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion t (heckeT_ppow k p hp (r + 1) g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ (r + 1))).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion t g).coeff (m' * p ^ (r + 1) / (d * d))
            else 0)
    (ih0 : ∀ g ∈ modFormCharSpace k χ, ∀ m',
        (qExpansion t (heckeT_ppow k p hp r g)).coeff m' =
          ∑ d ∈ (Nat.gcd m' (p ^ r)).divisors,
            if h : d.Coprime N then
              (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
                (qExpansion t g).coeff (m' * p ^ r / (d * d))
            else 0) :
    (qExpansion t (heckeT_ppow k p hp (r + 2) f)).coeff m =
      ∑ d ∈ (Nat.gcd m (p ^ (r + 2))).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * p ^ (r + 2) / (d * d))
        else 0 := by
  rw [coeff_qExpansion_heckeT_ppow_succ_succ k hp hpN χ r hf ht0 ht m,
    hTp _ (heckeT_ppow_preserves_charSpace k hp hpN (r + 1) χ hf) m, ih1 f hf (p * m), ih0 f hf m]
  conv_lhs => rw [show (if p ∣ m then (qExpansion t ⇑((heckeT_ppow k p hp (r + 1)) f)).coeff (m / p)
        else 0) =
      if p ∣ m then ∑ d ∈ ((m / p).gcd (p ^ (r + 1))).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m / p * p ^ (r + 1) / (d * d))
        else 0
      else 0 by split_ifs with hd <;> [exact ih1 f hf (m / p); rfl]]
  exact ppow_divisorSum_recurrence k hp hpN χ r m (fun j ↦ (qExpansion t f).coeff j)

private abbrev HeckeTppowCoeffFormula (k : ℤ) {p N : ℕ} [NeZero N] (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) (t : ℝ) : Prop :=
  ∀ (v : ℕ) (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k), g ∈ modFormCharSpace k χ → ∀ m',
    (qExpansion t (heckeT_ppow k p hp v g)).coeff m' =
      ∑ d ∈ (Nat.gcd m' (p ^ v)).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t g).coeff (m' * p ^ v / (d * d))
        else 0

private theorem fourierCoeff_heckeT_n_prime [NeZero N] (k : ℤ) {n : ℕ} [NeZero n]
    (hn_prime : Nat.Prime n) (hnN : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) {t : ℝ}
    (hTp : HeckeTpCoeffFormula k hn_prime hnN χ t)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion t (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * n / (d * d))
        else 0 := by
  rw [heckeT_n_prime_coprime k hn_prime hnN, hTp f hf m]
  by_cases hdvd : n ∣ m
  · rw [Nat.gcd_eq_right hdvd, hn_prime.divisors,
      Finset.sum_insert (by simp; exact hn_prime.one_lt.ne)]
    simp only [Finset.sum_singleton, Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one,
      one_zpow, unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul, Nat.div_one, hnN,
      if_pos hdvd]
    rw [Nat.mul_div_mul_right m n hn_prime.pos, Nat.mul_comm n m]
  · rw [(hn_prime.eq_one_or_self_of_dvd _ (Nat.gcd_dvd_right m n)).resolve_right fun h ↦
        hdvd (h ▸ Nat.gcd_dvd_left m n), Nat.divisors_one, Finset.sum_singleton]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, unitOfCoprime_one_eq_one, map_one,
      Units.val_one, Nat.cast_one, one_zpow, one_mul, Nat.div_one]
    rw [if_neg hdvd, mul_zero, add_zero, Nat.mul_comm n m]

private theorem fourierCoeff_heckeT_n_eq_ppow [NeZero N] (k : ℤ) {p : ℕ} (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) {t : ℝ} (hTppow : HeckeTppowCoeffFormula k hp χ t) (n : ℕ) [NeZero n]
    (v m : ℕ) (hn_ppow : n = p ^ v) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (h_eq : heckeT_n k n f = heckeT_ppow k p hp v f) :
    (qExpansion t (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * n / (d * d))
        else 0 := by
  rw [h_eq, hn_ppow]
  exact hTppow v f hf m

private theorem fourierCoeff_heckeT_n_coprime_split [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {t : ℝ} (n pv q m : ℕ) [NeZero n] [NeZero pv] [NeZero q] (hcop : Nat.Coprime pv q)
    (hn_eq : n = pv * q) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (h_apply : heckeT_n k n f = heckeT_n k pv (heckeT_n k q f))
    (ih_pv : (qExpansion t (heckeT_n k pv (heckeT_n k q f))).coeff m =
        ∑ d ∈ (Nat.gcd m pv).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion t (heckeT_n k q f)).coeff (m * pv / (d * d))
          else 0)
    (ih_q : ∀ m', (qExpansion t (heckeT_n k q f)).coeff m' =
        ∑ d ∈ (Nat.gcd m' q).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion t f).coeff (m' * q / (d * d))
          else 0) :
    (qExpansion t (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * n / (d * d))
        else 0 := by
  rw [h_apply, ih_pv]
  simp_rw [ih_q]
  rw [hn_eq]
  exact (divisorSum_coprime_conv k χ (fun j ↦ (qExpansion t f).coeff j) m pv q hcop).symm

private abbrev HeckeTnCoeffFormulaAt (k : ℤ) {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (t : ℝ) (n : ℕ) [NeZero n] : Prop :=
  ∀ (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k), g ∈ modFormCharSpace k χ → ∀ m',
    (qExpansion t (heckeT_n k n g)).coeff m' =
      ∑ d ∈ (Nat.gcd m' n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t g).coeff (m' * n / (d * d))
        else 0

private theorem fourierCoeff_heckeT_n_composite [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (hn_gt : 1 < n) (hnN : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) {t : ℝ}
    (hppow : ∀ {p : ℕ} (hp : Nat.Prime p), Nat.Coprime p N → HeckeTppowCoeffFormula k hp χ t)
    (ih : ∀ n' < n, ∀ (_ : n' ≠ 0), n'.Coprime N →
      haveI : NeZero n' := ⟨‹n' ≠ 0›⟩; HeckeTnCoeffFormulaAt k χ t n')
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion t (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion t f).coeff (m * n / (d * d))
        else 0 := by
  have hn0 : n ≠ 0 := by omega
  set p := n.minFac
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  set v := n.factorization p
  set q := n / p ^ v
  have hq_pos : 0 < q :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd n p)) (pow_pos hp.pos v)
  have hn_eq : n = p ^ v * q := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have : NeZero q := ⟨hq_pos.ne'⟩
  have h_unfold := heckeT_n_unfold (N := N) k n hn_gt
  by_cases hq1 : q = 1
  · have hn_ppow : n = p ^ v := by rw [hn_eq, hq1, mul_one]
    have h_eq : heckeT_n (N := N) k n f = heckeT_ppow k p hp v f := by
      have h1 := DFunLike.congr_fun h_unfold f
      simp only at h1
      rw [h1]
      change (heckeT_ppow k p hp v) ((heckeT_n k q) f) = (heckeT_ppow k p hp v) f
      congr 1
      have : (heckeT_n (N := N) k q : Module.End ℂ _) = 1 := by
        simp only [show q = 1 from hq1]
        exact heckeT_n_one k
      exact DFunLike.congr_fun this f
    exact fourierCoeff_heckeT_n_eq_ppow k hp χ
      (hppow hp (hnN.coprime_dvd_left (Nat.minFac_dvd n))) n v m hn_ppow hf h_eq
  · have hq_gt1 : 1 < q := by omega
    have hqN : q.Coprime N := hn_eq ▸ hnN |>.coprime_dvd_left (dvd_mul_left q (p ^ v))
    have : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    have h_apply : heckeT_n k n f = heckeT_n k (p ^ v) (heckeT_n k q f) := by
      rw [h_unfold, heckeT_n_prime_pow k hp v
        (hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd n))]
      rfl
    exact fourierCoeff_heckeT_n_coprime_split k χ n (p ^ v) q m
      ((Nat.coprime_ordCompl hp hn0).pow_left v) hn_eq h_apply
      (ih (p ^ v) (hn_eq ▸ lt_mul_of_one_lt_right (pow_pos hp.pos v) hq_gt1)
        (pow_pos hp.pos v).ne' (hn_eq ▸ hnN |>.coprime_dvd_left (dvd_mul_right (p ^ v) q))
        (heckeT_n k q f) (heckeT_n_preserves_charSpace k q hqN χ hf) m)
      (ih q (heckeT_n_unfold_lt n hn_gt) hq_pos.ne' hqN f hf)

/-- A modular form is a **common eigenfunction** of all `T_n` with `(n,N) = 1`
if `T_n f = a · f` for some eigenvalue `a ∈ ℂ`. -/
abbrev IsCommonEigenfunction [NeZero N] (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    ∃ a : ℂ, heckeT_n k n.val f = a • f

/-- The eigenvalue of a common eigenfunction at `n`. -/
def eigenvalue [NeZero N] (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsCommonEigenfunction k f) (n : ℕ+) (hn : Nat.Coprime n.val N) : ℂ :=
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  (hf n hn).choose

/-- The eigenvalue equation: `T_n f = eigenvalue k f hf n hn • f`. -/
theorem eigenvalue_spec [NeZero N] (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : IsCommonEigenfunction k f) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n k n.val f = eigenvalue k f hf n hn • f :=
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  (hf n hn).choose_spec

private theorem fourierCoeff_heckeT_ppow_period_one [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ) (v : ℕ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_ppow k p hp v f)).coeff m =
      ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m * p ^ v / (d * d))
        else 0 := by
  have hTp : HeckeTpCoeffFormula k hp hpN χ (1 : ℝ) :=
    fun g hg m' ↦ fourierCoeff_heckeT_p_period_one k hp hpN χ hg m'
  suffices key : ∀ v, ∀ f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      f ∈ modFormCharSpace k χ → ∀ m,
      (qExpansion (1 : ℝ) (heckeT_ppow k p hp v f)).coeff m =
        ∑ d ∈ (Nat.gcd m (p ^ v)).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion (1 : ℝ) f).coeff (m * p ^ v / (d * d))
          else 0 from key v f hf m
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih_v =>
  intro f hf m
  match v with
  | 0 =>
    simp [pow_zero, heckeT_ppow, Module.End.one_apply, Nat.gcd_one_right, Nat.divisors_one,
      Finset.sum_singleton, Nat.Coprime, unitOfCoprime_one_eq_one]
  | 1 => exact fourierCoeff_heckeT_ppow_one_eq k hp hpN χ hTp hf m
  | r + 2 =>
    exact fourierCoeff_heckeT_ppow_succ_succ_eq k hp hpN χ one_pos
      (one_mem_strictPeriods_Gamma1_map N) hTp hf r m
      (fun g hg m' ↦ ih_v (r + 1) (by omega) g hg m')
      (fun g hg m' ↦ ih_v r (by omega) g hg m')

/-- **Period-1 general Fourier coefficient formula for `T_n`.** The same divisor-sum formula as
`fourierCoeff_heckeT_n`, `a_m(T_n f) = Σ_{d | gcd(m, n)} d^{k-1} · χ(d) · a_{mn/d²}(f)`, with
every `coeff` taken at the canonical Fourier period `h = 1`. -/
theorem fourierCoeff_heckeT_n_period_one [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) (m : ℕ) :
    (qExpansion (1 : ℝ) (heckeT_n k n f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m * n / (d * d))
        else 0 := by
  suffices key : ∀ (n : ℕ) (hn0 : n ≠ 0) (hn : Nat.Coprime n N)
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hf : f ∈ modFormCharSpace k χ) (m : ℕ),
      haveI : NeZero n := ⟨hn0⟩
      (qExpansion (1 : ℝ) (heckeT_n k n f)).coeff m =
        ∑ d ∈ (Nat.gcd m n).divisors,
          if h : d.Coprime N then
            (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
              (qExpansion (1 : ℝ) f).coeff (m * n / (d * d))
          else 0 by
    exact key n (NeZero.ne n) hn f hf m
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro hn0 hnN f hf m
  have : NeZero n := ⟨hn0⟩
  by_cases hn1 : n = 1
  · subst hn1
    simp [heckeT_n_one, Module.End.one_apply, Nat.gcd_one_right, Nat.divisors_one,
      Finset.sum_singleton, Nat.Coprime, unitOfCoprime_one_eq_one]
  · have hn_gt : 1 < n := by omega
    by_cases hn_prime : Nat.Prime n
    · exact fourierCoeff_heckeT_n_prime k hn_prime hnN χ
        (fun g hg m' ↦ fourierCoeff_heckeT_p_period_one k hn_prime hnN χ hg m') hf m
    · exact fourierCoeff_heckeT_n_composite k n hn_gt hnN χ
        (fun hp hpN v g hg m' ↦ fourierCoeff_heckeT_ppow_period_one k hp hpN χ v hg m') ih hf m

/-- **Period-1 normalised eigenform.**  A common eigenfunction `f` with canonical Fourier
normalisation `a_1 = (qExpansion (1 : ℝ) f).coeff 1 = 1`. This is the Miyake / Diamond–Shurman
`a_1 = 1` normalisation and supersedes `IsNormalisedEigenform`, whose period-`N` condition is
vacuous for `N > 1`. -/
def IsNormalisedEigenform_one [NeZero N] (k : ℤ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  IsCommonEigenfunction k f ∧ (qExpansion (1 : ℝ) f).coeff 1 = 1

/-- **Period-1 eigenvalue = Fourier coefficient** (period-1 analog of
`eigenvalue_eq_fourierCoeff`): if `f` is a period-1 normalised eigenform in `M_k(Γ₁(N), χ)` and
`(n, N) = 1`, then `λ_n = a_n(f)`. -/
theorem eigenvalue_eq_fourierCoeff_one [NeZero N] (k : ℤ) (n : ℕ+) (hn : Nat.Coprime n.val N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ) (hf_eigen : IsNormalisedEigenform_one k f) :
    eigenvalue k f hf_eigen.1 n hn = (qExpansion (1 : ℝ) f).coeff n.val := by
  have : NeZero n.val := ⟨n.pos.ne'⟩
  have h1 := fourierCoeff_heckeT_n_period_one k n.val hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton, Nat.Coprime, dite_true,
    Nat.cast_one, one_zpow, unitOfCoprime_one_eq_one, map_one, Units.val_one, one_mul,
    Nat.div_one] at h1
  have h_lhs : (qExpansion (1 : ℝ) (heckeT_n k n.val f)).coeff 1 =
      eigenvalue k f hf_eigen.1 n hn := by
    rw [eigenvalue_spec k f hf_eigen.1 n hn]
    simp [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N), hf_eigen.2]
  rw [← h1, h_lhs]

/-- **Period-1 Hecke multiplicativity relations** for Fourier coefficients of a normalised
eigenform: `a_m · a_n = Σ_{d | gcd(m, n)} d^{k-1} · χ(d) · a_{mn/d²}`. In particular
`a_m · a_n = a_{mn}` when `gcd(m, n) = 1`. Period-1 analog of
`eigenform_coeff_multiplicative`. -/
theorem eigenform_coeff_multiplicative_one [NeZero N] (k : ℤ) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (_ : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf_char : f ∈ modFormCharSpace k χ)
    (hf_eigen : IsNormalisedEigenform_one k f) :
    (qExpansion (1 : ℝ) f).coeff m.val * (qExpansion (1 : ℝ) f).coeff n.val =
      ∑ d ∈ (Nat.gcd m.val n.val).divisors,
        if h : d.Coprime N then
          (↑d : ℂ) ^ (k - 1) * ↑(χ (ZMod.unitOfCoprime d h)) *
            (qExpansion (1 : ℝ) f).coeff (m.val * n.val / (d * d))
        else 0 := by
  have : NeZero m.val := ⟨m.pos.ne'⟩
  have : NeZero n.val := ⟨n.pos.ne'⟩
  have h_smul : (qExpansion (1 : ℝ) (heckeT_n k m.val f)).coeff n.val =
      eigenvalue k f hf_eigen.1 m hm * (qExpansion (1 : ℝ) f).coeff n.val := by
    rw [eigenvalue_spec k f hf_eigen.1 m hm, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_smul, smul_eq_mul]
  rw [← eigenvalue_eq_fourierCoeff_one k m hm χ hf_char hf_eigen, ← h_smul, Nat.gcd_comm m.val,
    Nat.mul_comm m.val]
  exact fourierCoeff_heckeT_n_period_one k m.val hm χ hf_char n.val

end HeckeRing.GL2
