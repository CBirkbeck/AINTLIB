/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.ArCompletion

/-!
# Euclidean division on `A^r` (Kedlaya §2, Lemmas 2.6–2.10)

Kedlaya (*Noetherian properties of Fargues–Fontaine curves*, §2) shows the completed
ring `A^r` admits a Euclidean division algorithm for the coordinate degree: Lemma 2.8
(approximate division), Proposition 2.9 (exact division), Corollary 2.10 (`A^r` is a
Euclidean domain, hence a PID).

This file builds the ingredients in source order. The engine is the **Witt
homogeneity estimate (2.8.1)**: whenever `λ_r(p) ≤ ε`,
`λ_r([z₁] ± ⋯ ± [zₙ] − [z₁ ± ⋯ ± zₙ]) ≤ ε·max λ_r([zᵢ])`. In the campaign
specialization the proof is a scaling argument: after dividing by a max-attaining
coefficient all entries are integral, the discrepancy lies in `W(O_F)` with vanishing
zeroth coordinate (the zeroth coordinate is a ring homomorphism), hence is `p` times
an integral vector and has value at most `ρ`.

## Main results

* `FarguesFontaine.gaussValueF_map_le_of_coeff_zero` : the normalized master bound.
* `FarguesFontaine.gaussValueF_teichmuller_add_sub_le`,
  `FarguesFontaine.gaussValueF_teichmuller_sub_sub_le` : the binary forms of (2.8.1).

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  formula (2.8.1), Definition 2.4, Remark 2.7, Lemma 2.8, Proposition 2.9,
  Corollary 2.10.
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- **The normalized homogeneity master bound**: an integral Witt vector with
vanishing zeroth coordinate has Gauss value at most `ρ` (it is `p` times an
integral vector). -/
theorem gaussValueF_map_le_of_coeff_zero {ρ : NNReal} (hρ1 : ρ ≤ 1) {E : Ainf p F}
    (h0 : E.coeff 0 = 0) :
    gaussValueF p F ρ (WittVector.map ((powerBoundedSubring.toSubring F).subtype) E)
      ≤ ρ := by
  obtain ⟨X, hX⟩ := exists_eq_sum_teichCoeff_add p F E 1
  have ht0 : teichCoeff p F E 0 = 0 := by
    rw [teichCoeff]
    simp [h0]
  have hE : E = (p : Ainf p F) * X := by
    rw [hX, Finset.sum_range_one, pow_zero, mul_one, ht0,
      WittVector.teichmuller_zero, zero_add, pow_one]
  have hBmapX : BddAbove (Set.range (gaussTermF p F ρ
      (WittVector.map ((powerBoundedSubring.toSubring F).subtype) X))) := by
    refine ⟨1, ?_⟩
    rintro s ⟨n, rfl⟩
    rw [gaussTermF_map]
    exact gaussTerm_le_one p F hρ1 X n
  rw [hE, map_mul, map_natCast, gaussValueF_p_mul p F hBmapX, gaussValueF_map]
  calc ρ * gaussValue p F ρ X ≤ ρ * 1 :=
        mul_le_mul_of_nonneg_left (gaussValue_le_one p F hρ1 X) zero_le
    _ = ρ := mul_one ρ

/-- Gauss value of the zero vector. -/
theorem gaussValueF_zero {ρ : NNReal} :
    gaussValueF p F ρ (0 : WittVector p F) = 0 := by
  have h : ∀ n, gaussTermF p F ρ (0 : WittVector p F) n = 0 := by
    intro n
    rw [gaussTermF, teichCoeffF, WittVector.zero_coeff, map_zero,
      Valuation.map_zero, mul_zero]
  rw [gaussValueF]
  simp [h]

/-- Every pair admits a max-attaining nonzero coefficient (given the max is
nonzero). -/
theorem exists_attaining_coeff {a b : F}
    (hmax : max (perfectoidValuation p F a) (perfectoidValuation p F b) ≠ 0) :
    ∃ c : F, c ≠ 0
      ∧ perfectoidValuation p F c
        = max (perfectoidValuation p F a) (perfectoidValuation p F b)
      ∧ perfectoidValuation p F a ≤ perfectoidValuation p F c
      ∧ perfectoidValuation p F b ≤ perfectoidValuation p F c := by
  rcases max_cases (perfectoidValuation p F a) (perfectoidValuation p F b)
    with ⟨heq, hle⟩ | ⟨heq, hle⟩
  · refine ⟨a, fun h0 => hmax ?_, heq.symm, le_rfl, hle⟩
    rw [heq, h0, Valuation.map_zero]
  · refine ⟨b, fun h0 => hmax ?_, heq.symm, hle.le, le_rfl⟩
    rw [heq, h0, Valuation.map_zero]

/-- **Witt homogeneity (2.8.1), binary sum form**: the discrepancy between the sum of
two Teichmüller lifts and the Teichmüller lift of the sum is `ρ`-small relative to
the entries. -/
theorem gaussValueF_teichmuller_add_sub_le {ρ : NNReal} (hρ1 : ρ ≤ 1) (a b : F) :
    gaussValueF p F ρ (WittVector.teichmuller p a + WittVector.teichmuller p b
      - WittVector.teichmuller p (a + b))
      ≤ ρ * max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
  rcases eq_or_ne (max (perfectoidValuation p F a) (perfectoidValuation p F b)) 0
    with hmax | hmax
  · have ha : a = 0 := by
      refine (Valuation.zero_iff (perfectoidValuation p F)).mp
        (le_antisymm ?_ zero_le)
      rw [← hmax]
      exact le_max_left _ _
    have hb : b = 0 := by
      refine (Valuation.zero_iff (perfectoidValuation p F)).mp
        (le_antisymm ?_ zero_le)
      rw [← hmax]
      exact le_max_right _ _
    have hexpr : WittVector.teichmuller p a + WittVector.teichmuller p b
        - WittVector.teichmuller p (a + b) = 0 := by
      rw [ha, hb, add_zero, WittVector.teichmuller_zero, add_zero, sub_zero]
    rw [hexpr, gaussValueF_zero]
    exact zero_le
  · obtain ⟨c, hc0, hcmax, hac, hbc⟩ := exists_attaining_coeff p F hmax
    have hvc0 : perfectoidValuation p F c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hanorm : perfectoidValuation p F (a * c⁻¹) ≤ 1 := by
      rw [Valuation.map_mul, map_inv₀]
      calc perfectoidValuation p F a * (perfectoidValuation p F c)⁻¹
          ≤ perfectoidValuation p F c * (perfectoidValuation p F c)⁻¹ :=
            mul_le_mul_of_nonneg_right hac zero_le
        _ = 1 := mul_inv_cancel₀ hvc0
    have hbnorm : perfectoidValuation p F (b * c⁻¹) ≤ 1 := by
      rw [Valuation.map_mul, map_inv₀]
      calc perfectoidValuation p F b * (perfectoidValuation p F c)⁻¹
          ≤ perfectoidValuation p F c * (perfectoidValuation p F c)⁻¹ :=
            mul_le_mul_of_nonneg_right hbc zero_le
        _ = 1 := mul_inv_cancel₀ hvc0
    obtain ⟨aInt, haInt⟩ := (perfectoidValuation_integers p F).exists_of_le_one hanorm
    obtain ⟨bInt, hbInt⟩ := (perfectoidValuation_integers p F).exists_of_le_one hbnorm
    have haInt' : ((aInt : OF F) : F) = a * c⁻¹ := haInt
    have hbInt' : ((bInt : OF F) : F) = b * c⁻¹ := hbInt
    set E : Ainf p F := WittVector.teichmuller p aInt + WittVector.teichmuller p bInt
      - WittVector.teichmuller p (aInt + bInt) with hE
    have h0 : E.coeff 0 = 0 := by
      have h1 : WittVector.constantCoeff E = 0 := by
        rw [hE, map_sub, map_add]
        have hca : WittVector.constantCoeff (WittVector.teichmuller p aInt) = aInt :=
          WittVector.teichmuller_coeff_zero p aInt
        have hcb : WittVector.constantCoeff (WittVector.teichmuller p bInt) = bInt :=
          WittVector.teichmuller_coeff_zero p bInt
        have hcab : WittVector.constantCoeff (WittVector.teichmuller p (aInt + bInt))
            = aInt + bInt := WittVector.teichmuller_coeff_zero p (aInt + bInt)
        rw [hca, hcb, hcab]
        ring
      exact h1
    have hmaster := gaussValueF_map_le_of_coeff_zero p F hρ1 h0
    have hkey : WittVector.teichmuller p c
        * WittVector.map ((powerBoundedSubring.toSubring F).subtype) E
        = WittVector.teichmuller p a + WittVector.teichmuller p b
          - WittVector.teichmuller p (a + b) := by
      rw [hE, map_sub, map_add, WittVector.map_teichmuller,
        WittVector.map_teichmuller, WittVector.map_teichmuller]
      have hsa : ((powerBoundedSubring.toSubring F).subtype) aInt = a * c⁻¹ := haInt'
      have hsb : ((powerBoundedSubring.toSubring F).subtype) bInt = b * c⁻¹ := hbInt'
      have hsab : ((powerBoundedSubring.toSubring F).subtype) (aInt + bInt)
          = a * c⁻¹ + b * c⁻¹ := by
        rw [map_add, hsa, hsb]
      rw [hsa, hsb, hsab, mul_sub, mul_add, ← map_mul, ← map_mul, ← map_mul]
      have h1 : c * (a * c⁻¹) = a := by
        field_simp
      have h2 : c * (b * c⁻¹) = b := by
        field_simp
      have h3 : c * (a * c⁻¹ + b * c⁻¹) = a + b := by
        field_simp
      rw [h1, h2, h3]
    rw [← hkey, gaussValueF_teichmuller_mul]
    calc perfectoidValuation p F c * gaussValueF p F ρ
          (WittVector.map ((powerBoundedSubring.toSubring F).subtype) E)
        ≤ perfectoidValuation p F c * ρ :=
          mul_le_mul_of_nonneg_left hmaster zero_le
      _ = ρ * max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
          rw [mul_comm, hcmax]

/-- **Witt homogeneity (2.8.1), binary difference form** (same scaling proof — the
zeroth coordinate is a ring homomorphism, killing the signs). -/
theorem gaussValueF_teichmuller_sub_sub_le {ρ : NNReal} (hρ1 : ρ ≤ 1) (a b : F) :
    gaussValueF p F ρ (WittVector.teichmuller p a - WittVector.teichmuller p b
      - WittVector.teichmuller p (a - b))
      ≤ ρ * max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
  rcases eq_or_ne (max (perfectoidValuation p F a) (perfectoidValuation p F b)) 0
    with hmax | hmax
  · have ha : a = 0 := by
      refine (Valuation.zero_iff (perfectoidValuation p F)).mp
        (le_antisymm ?_ zero_le)
      rw [← hmax]
      exact le_max_left _ _
    have hb : b = 0 := by
      refine (Valuation.zero_iff (perfectoidValuation p F)).mp
        (le_antisymm ?_ zero_le)
      rw [← hmax]
      exact le_max_right _ _
    have hexpr : WittVector.teichmuller p a - WittVector.teichmuller p b
        - WittVector.teichmuller p (a - b) = 0 := by
      rw [ha, hb, sub_zero, WittVector.teichmuller_zero, sub_zero, sub_self]
    rw [hexpr, gaussValueF_zero]
    exact zero_le
  · obtain ⟨c, hc0, hcmax, hac, hbc⟩ := exists_attaining_coeff p F hmax
    have hvc0 : perfectoidValuation p F c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0
    have hanorm : perfectoidValuation p F (a * c⁻¹) ≤ 1 := by
      rw [Valuation.map_mul, map_inv₀]
      calc perfectoidValuation p F a * (perfectoidValuation p F c)⁻¹
          ≤ perfectoidValuation p F c * (perfectoidValuation p F c)⁻¹ :=
            mul_le_mul_of_nonneg_right hac zero_le
        _ = 1 := mul_inv_cancel₀ hvc0
    have hbnorm : perfectoidValuation p F (b * c⁻¹) ≤ 1 := by
      rw [Valuation.map_mul, map_inv₀]
      calc perfectoidValuation p F b * (perfectoidValuation p F c)⁻¹
          ≤ perfectoidValuation p F c * (perfectoidValuation p F c)⁻¹ :=
            mul_le_mul_of_nonneg_right hbc zero_le
        _ = 1 := mul_inv_cancel₀ hvc0
    obtain ⟨aInt, haInt⟩ := (perfectoidValuation_integers p F).exists_of_le_one hanorm
    obtain ⟨bInt, hbInt⟩ := (perfectoidValuation_integers p F).exists_of_le_one hbnorm
    have haInt' : ((aInt : OF F) : F) = a * c⁻¹ := haInt
    have hbInt' : ((bInt : OF F) : F) = b * c⁻¹ := hbInt
    set E : Ainf p F := WittVector.teichmuller p aInt - WittVector.teichmuller p bInt
      - WittVector.teichmuller p (aInt - bInt) with hE
    have h0 : E.coeff 0 = 0 := by
      have h1 : WittVector.constantCoeff E = 0 := by
        rw [hE, map_sub, map_sub]
        have hca : WittVector.constantCoeff (WittVector.teichmuller p aInt) = aInt :=
          WittVector.teichmuller_coeff_zero p aInt
        have hcb : WittVector.constantCoeff (WittVector.teichmuller p bInt) = bInt :=
          WittVector.teichmuller_coeff_zero p bInt
        have hcab : WittVector.constantCoeff (WittVector.teichmuller p (aInt - bInt))
            = aInt - bInt := WittVector.teichmuller_coeff_zero p (aInt - bInt)
        rw [hca, hcb, hcab]
        ring
      exact h1
    have hmaster := gaussValueF_map_le_of_coeff_zero p F hρ1 h0
    have hkey : WittVector.teichmuller p c
        * WittVector.map ((powerBoundedSubring.toSubring F).subtype) E
        = WittVector.teichmuller p a - WittVector.teichmuller p b
          - WittVector.teichmuller p (a - b) := by
      rw [hE, map_sub, map_sub, WittVector.map_teichmuller,
        WittVector.map_teichmuller, WittVector.map_teichmuller]
      have hsa : ((powerBoundedSubring.toSubring F).subtype) aInt = a * c⁻¹ := haInt'
      have hsb : ((powerBoundedSubring.toSubring F).subtype) bInt = b * c⁻¹ := hbInt'
      have hsab : ((powerBoundedSubring.toSubring F).subtype) (aInt - bInt)
          = a * c⁻¹ - b * c⁻¹ := by
        rw [map_sub, hsa, hsb]
      rw [hsa, hsb, hsab, mul_sub, mul_sub, ← map_mul, ← map_mul, ← map_mul]
      have h1 : c * (a * c⁻¹) = a := by
        field_simp
      have h2 : c * (b * c⁻¹) = b := by
        field_simp
      have h3 : c * (a * c⁻¹ - b * c⁻¹) = a - b := by
        field_simp
      rw [h1, h2, h3]
    rw [← hkey, gaussValueF_teichmuller_mul]
    calc perfectoidValuation p F c * gaussValueF p F ρ
          (WittVector.map ((powerBoundedSubring.toSubring F).subtype) E)
        ≤ perfectoidValuation p F c * ρ :=
          mul_le_mul_of_nonneg_left hmaster zero_le
      _ = ρ * max (perfectoidValuation p F a) (perfectoidValuation p F b) := by
          rw [mul_comm, hcmax]

end FarguesFontaine

end
