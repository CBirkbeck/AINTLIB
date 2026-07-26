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

/-- **Witt homogeneity (2.8.1), `n`-ary form**: the discrepancy between a finite sum
of Teichmüller lifts and the Teichmüller lift of the sum is `ρ`-small relative to a
common coefficient bound. -/
theorem gaussValueF_teichmuller_sum_sub_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ι : Type*} (s : Finset ι) (f : ι → F) {B : NNReal}
    (hf : ∀ i ∈ s, perfectoidValuation p F (f i) ≤ B) :
    gaussValueF p F ρ ((∑ i ∈ s, WittVector.teichmuller p (f i))
      - WittVector.teichmuller p (∑ i ∈ s, f i))
      ≤ ρ * B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hexpr : ((∑ i ∈ (∅ : Finset ι), WittVector.teichmuller p (f i))
        - WittVector.teichmuller p (∑ i ∈ (∅ : Finset ι), f i)) = 0 := by
      rw [Finset.sum_empty, Finset.sum_empty, WittVector.teichmuller_zero, sub_zero]
    rw [hexpr, gaussValueF_zero]
    exact zero_le
  | insert a t ha ih =>
    have hfa : perfectoidValuation p F (f a) ≤ B := hf a (Finset.mem_insert_self a t)
    have hft : ∀ i ∈ t, perfectoidValuation p F (f i) ≤ B :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hS : perfectoidValuation p F (∑ i ∈ t, f i) ≤ B :=
      Valuation.map_sum_le _ hft
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hsplit : (WittVector.teichmuller p (f a)
          + ∑ i ∈ t, WittVector.teichmuller p (f i))
        - WittVector.teichmuller p (f a + ∑ i ∈ t, f i)
        = (WittVector.teichmuller p (f a)
            + WittVector.teichmuller p (∑ i ∈ t, f i)
            - WittVector.teichmuller p (f a + ∑ i ∈ t, f i))
          + ((∑ i ∈ t, WittVector.teichmuller p (f i))
            - WittVector.teichmuller p (∑ i ∈ t, f i)) := by
      ring
    rw [hsplit]
    have hBsum : BddAbove (Set.range (gaussTermF p F ρ
        (∑ i ∈ t, WittVector.teichmuller p (f i)))) :=
      (gaussValueF_finset_sum_le p F hρ0 hρ1 B t
        (fun i => WittVector.teichmuller p (f i))
        (fun i hi => ⟨bddAbove_gaussTermF_teichmuller p F (f i), by
          rw [gaussValueF_teichmuller]
          exact hft i hi⟩)).1
    have hB1 : BddAbove (Set.range (gaussTermF p F ρ
        (WittVector.teichmuller p (f a)
          + WittVector.teichmuller p (∑ i ∈ t, f i)
          - WittVector.teichmuller p (f a + ∑ i ∈ t, f i)))) := by
      have h1 := bddAbove_gaussTermF_add p F hρ0 hρ1
        (bddAbove_gaussTermF_add p F hρ0 hρ1
          (bddAbove_gaussTermF_teichmuller p F (f a))
          (bddAbove_gaussTermF_teichmuller p F (∑ i ∈ t, f i)))
        (bddAbove_gaussTermF_neg p F hρ0 hρ1
          (bddAbove_gaussTermF_teichmuller p F (f a + ∑ i ∈ t, f i)))
      rwa [← sub_eq_add_neg] at h1
    have hB2 : BddAbove (Set.range (gaussTermF p F ρ
        ((∑ i ∈ t, WittVector.teichmuller p (f i))
          - WittVector.teichmuller p (∑ i ∈ t, f i)))) := by
      have h1 := bddAbove_gaussTermF_add p F hρ0 hρ1 hBsum
        (bddAbove_gaussTermF_neg p F hρ0 hρ1
          (bddAbove_gaussTermF_teichmuller p F (∑ i ∈ t, f i)))
      rwa [← sub_eq_add_neg] at h1
    refine le_trans (gaussValueF_add_le p F hρ0 hρ1 hB1 hB2) (max_le ?_ (ih hft))
    refine le_trans (gaussValueF_teichmuller_add_sub_le p F hρ1.le (f a)
      (∑ i ∈ t, f i)) ?_
    exact mul_le_mul_of_nonneg_left (max_le hfa hS) zero_le

variable (ϖ : PseudoUniformizer F)

/-- **The degree** (Kedlaya Definition 2.4): the largest coordinate index realizing
`λ_r(x) = max_n ρⁿ|xₙ|`. Junk value `0` for `x = 0` (Kedlaya's `deg 0 = -∞`) and for
points outside `A^r`. -/
def degAr {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : hatK p F hρ0 hρ1) : ℕ :=
  sSup {n | Valued.v x = ρ ^ n * perfectoidValuation p F
    (teichCoeffAr p F ϖ hρ0 hρ1 x n)}

/-- The attainment set of a nonzero element of `A^r` is bounded above. -/
theorem bddAbove_attainment {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    BddAbove {n | Valued.v x = ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x n)} := by
  have hvpos : 0 < Valued.v x := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    ((tendsto_gaussTerm_teichCoeffAr p F ϖ hx).eventually_lt_const hvpos)
  refine ⟨K, fun n hn => ?_⟩
  by_contra hcon
  push Not at hcon
  have h1 := hK n hcon.le
  rw [← hn] at h1
  exact absurd h1 (lt_irrefl _)

/-- **Degree specification** (Kedlaya Definition 2.4): nonzero elements of `A^r`
attain their value at the degree index, which dominates every attaining index. -/
theorem degAr_spec {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    Valued.v x = ρ ^ (degAr p F ϖ hρ0 hρ1 x) * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 x (degAr p F ϖ hρ0 hρ1 x))
      ∧ ∀ m, Valued.v x = ρ ^ m * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 x m) → m ≤ degAr p F ϖ hρ0 hρ1 x := by
  have hne : {n | Valued.v x = ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x n)}.Nonempty := by
    obtain ⟨n₀, hn₀, -⟩ := exists_valued_eq_teichCoeffAr p F ϖ hx hx0
    exact ⟨n₀, hn₀⟩
  have hbdd := bddAbove_attainment p F ϖ hx hx0
  constructor
  · exact Nat.sSup_mem hne hbdd
  · intro m hm
    exact le_csSup hbdd hm

/-- Terms above the degree are strictly below the value. -/
theorem gaussTerm_lt_of_degAr_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0)
    {n : ℕ} (hn : degAr p F ϖ hρ0 hρ1 x < n) :
    ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
      < Valued.v x := by
  have hle : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
      ≤ Valued.v x := by
    rw [valued_eq_iSup_teichCoeffAr p F ϖ hx]
    have hB : BddAbove (Set.range (fun n => ρ ^ n * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 x n))) := by
      obtain ⟨n₁, hn₁, hmax⟩ := exists_valued_eq_teichCoeffAr p F ϖ hx hx0
      exact ⟨ρ ^ n₁ * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n₁), by
        rintro s ⟨k, rfl⟩
        exact hmax k⟩
    exact le_ciSup hB n
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd ((degAr_spec p F ϖ hx hx0).2 n heq.symm) (Nat.not_le.mpr hn)

/-- **The `ε` of Kedlaya Lemma 2.8**: past the degree, all terms are uniformly
`ε`-below the value, for some `ε ∈ [ρ, 1)`. -/
theorem exists_eps_terms_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    ∃ ε : NNReal, ρ ≤ ε ∧ ε < 1
      ∧ ∀ n, degAr p F ϖ hρ0 hρ1 x < n
        → ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
          ≤ ε * Valued.v x := by
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  have hvpos : 0 < Valued.v x := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0)
  have hρv : 0 < ρ * Valued.v x := mul_pos hρ0 hvpos
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    ((tendsto_gaussTerm_teichCoeffAr p F ϖ hx).eventually_lt_const hρv)
  set R : NNReal := (Finset.Ioc m K).sup (fun n => ρ ^ n * perfectoidValuation p F
    (teichCoeffAr p F ϖ hρ0 hρ1 x n) * (Valued.v x)⁻¹) with hR
  refine ⟨max ρ R, le_max_left _ _, ?_, ?_⟩
  · refine max_lt hρ1 ?_
    rw [hR]
    rcases Finset.eq_empty_or_nonempty (Finset.Ioc m K) with hemp | hne
    · rw [hemp, Finset.sup_empty, bot_eq_zero]
      exact zero_lt_one
    · refine (Finset.sup_lt_iff (by rw [bot_eq_zero]; exact zero_lt_one)).mpr
        fun n hn => ?_
      have hlt := gaussTerm_lt_of_degAr_lt p F ϖ hx hx0 (Finset.mem_Ioc.mp hn).1
      calc ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
            * (Valued.v x)⁻¹
          < Valued.v x * (Valued.v x)⁻¹ :=
            mul_lt_mul_of_pos_right hlt (inv_pos.mpr hvpos)
        _ = 1 := mul_inv_cancel₀ hvpos.ne'
  · intro n hn
    rcases le_or_gt n K with hnK | hnK
    · have hmem : n ∈ Finset.Ioc m K := Finset.mem_Ioc.mpr ⟨hn, hnK⟩
      have h1 : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
          * (Valued.v x)⁻¹ ≤ R :=
        Finset.le_sup (f := fun n => ρ ^ n * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 x n) * (Valued.v x)⁻¹) hmem
      have h2 : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
          = ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
            * (Valued.v x)⁻¹ * Valued.v x := by
        rw [mul_assoc, inv_mul_cancel₀ hvpos.ne', mul_one]
      rw [h2]
      exact mul_le_mul_of_nonneg_right (le_trans h1 (le_max_right ρ R)) zero_le
    · refine le_trans (hK n hnK.le).le ?_
      exact mul_le_mul_of_nonneg_right (le_max_left ρ R) zero_le

end FarguesFontaine

end
