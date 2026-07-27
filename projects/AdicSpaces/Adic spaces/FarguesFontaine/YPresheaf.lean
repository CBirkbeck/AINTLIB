/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartSpa

/-!
# The interval-trace basis of `Y` (D-ii-1)

The loci `κ(v) ∈ [1/q₁, 1/q₂]` for rational radius-exponent pairs — the
index geometry of the `BIQ`-valued structure presheaf of the curve:

* `FarguesFontaine.intervalTrace` : the trace, in `KGE`/`KLE` form;
* `FarguesFontaine.bigWindow_eq_intervalTrace` : the Big windows are the
  `(1/p^n, 1/p^{n+1})`-traces;
* `FarguesFontaine.intervalTrace_mono` : traces are monotone in the interval.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **The trace of a radius-exponent interval on `Y`**: the locus
`κ(v) ∈ [1/q₁, 1/q₂]` for a decreasing exponent pair `q₂ < q₁` (radius
exponents; the `BIQ q₁ q₂`-indexing convention). -/
def intervalTrace (q₁ q₂ : ℚ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ (1 / q₁) v ∧ KLE p F ϖ (1 / q₂) v}

/-- The Big windows are interval traces. -/
theorem bigWindow_eq_intervalTrace (n : ℤ) :
    bigWindow p F ϖ n
      = intervalTrace p F ϖ (1 / (p : ℚ) ^ n) (1 / (p : ℚ) ^ (n + 1)) := by
  ext v
  show (v ∈ Y p F ϖ ∧ KGE p F ϖ ((p : ℚ) ^ n) v ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v)
    ↔ (v ∈ Y p F ϖ ∧ KGE p F ϖ (1 / (1 / (p : ℚ) ^ n)) v
        ∧ KLE p F ϖ (1 / (1 / (p : ℚ) ^ (n + 1))) v)
  rw [one_div_one_div, one_div_one_div]

/-- Interval traces are monotone: a smaller exponent interval has a smaller
trace. -/
theorem intervalTrace_mono {q₁ q₂ r₁ r₂ : ℚ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : r₁ ≤ q₁) (h₂ : q₂ ≤ r₂) :
    intervalTrace p F ϖ r₁ r₂ ⊆ intervalTrace p F ϖ q₁ q₂ := by
  rintro v ⟨hY, hge, hle⟩
  refine ⟨hY, ?_, ?_⟩
  · refine KGE_mono p F ϖ hY ?_ ?_ hge
    · positivity
    · exact one_div_le_one_div_of_le hr₁ h₁
  · refine KLE_mono p F ϖ hY ?_ ?_ hle
    · positivity
    · exact one_div_le_one_div_of_le hq₂ h₂

/-- **Dyadic interval traces are rational subsets**: the trace at exponents
`(j₁/p^s, j₂/p^s)` is the `κ' ∈ [1/j₁, 1/j₂]` chart of the `p^s`-th root
uniformizer. -/
theorem intervalTrace_dyadic_eq_rationalOpen (s j₁ j₂ : ℕ)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) :
    intervalTrace p F ϖ ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))
      = rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ s) 1 (j₁ + j₂ - 1))
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ s := pow_pos hppos s
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ s with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ s = teichPi p F ϖ :=
    teichPi_frobRoot_pow p F ϖ s
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    Y_eq_of_teichPi_pow p F ϖ hpk hteich
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 j₁ 1 j₂
    one_pos hj₁ one_pos hj₂ v
  rw [show 1 + 1 - 1 = 1 from by omega] at hiff
  rw [hiff, hYeq]
  have hq1 : (0 : ℚ) < 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₁ : ℚ) := by exact_mod_cast hj₁
    positivity
  have hq2 : (0 : ℚ) < 1 / ((j₂ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₂ : ℚ) := by exact_mod_cast hj₂
    positivity
  have hab1 : 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s))
      = ((p ^ s : ℕ) : ℚ) / ((j₁ : ℕ) : ℚ) := by
    push_cast
    rw [one_div_div]
  have hab2 : 1 / ((j₂ : ℚ) / ((p : ℚ) ^ s))
      = ((p ^ s : ℕ) : ℚ) / ((j₂ : ℕ) : ℚ) := by
    push_cast
    rw [one_div_div]
  have hcolL : (teichPi p F ϖ' ^ j₁) ^ p ^ s = teichPi p F ϖ ^ j₁ := by
    rw [← pow_mul, mul_comm j₁ (p ^ s), pow_mul, hteich]
  have hcolR : (teichPi p F ϖ' ^ j₂) ^ p ^ s = teichPi p F ϖ ^ j₂ := by
    rw [← pow_mul, mul_comm j₂ (p ^ s), pow_mul, hteich]
  have hcolP : (((p : Ainf p F)) ^ 1) ^ p ^ s = ((p : Ainf p F)) ^ p ^ s := by
    rw [← pow_mul, one_mul]
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 hj₁ hab1).mp hge
    have hlev := (KLE_iff hY hq2 hj₂ hab2).mp hle
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      rw [hcolL, hcolP]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      rw [hcolR, hcolP]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 hj₁ hab1).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hcolL, hcolP] at h
      exact h
    · refine (KLE_iff hY hq2 hj₂ hab2).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hcolR, hcolP] at h
      exact h


/-- **Dyadic interval traces are open in `Spa (A_inf, A_inf)`.** -/
theorem isOpen_intervalTrace_dyadic (s j₁ j₂ : ℕ)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) :
    IsOpen {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ intervalTrace p F ϖ
        ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))} := by
  rw [show {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ intervalTrace p F ϖ
        ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))}
    = {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ rationalOpen
        (chartT p F (PseudoUniformizer.frobRoot p F ϖ s) 1 (j₁ + j₂ - 1))
        (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂)} from by
    rw [← intervalTrace_dyadic_eq_rationalOpen p F ϖ s j₁ j₂ hj₁ hj₂]]
  exact isOpen_rationalOpen_trace (chartT_nonempty p F _ 1 (j₁ + j₂ - 1)) _

end FarguesFontaine

end
