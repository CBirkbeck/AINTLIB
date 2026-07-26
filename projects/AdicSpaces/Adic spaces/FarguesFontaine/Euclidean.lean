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

/-- Antidiagonal sups of products of two vanishing `NNReal` sequences vanish. -/
theorem tendsto_antidiagonal_sup_zero {fa fb : ℕ → NNReal}
    (ha : Filter.Tendsto fa Filter.atTop (nhds 0))
    (hb : Filter.Tendsto fb Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => (Finset.range (n + 1)).sup
      (fun i => fa i * fb (n - i))) Filter.atTop (nhds 0) := by
  have hbdd : ∀ {f : ℕ → NNReal}, Filter.Tendsto f Filter.atTop (nhds 0)
      → ∃ M : NNReal, 1 ≤ M ∧ ∀ n, f n ≤ M := by
    intro f hf
    obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (hf.eventually_lt_const one_pos)
    refine ⟨max 1 ((Finset.range (K₀ + 1)).sup f), le_max_left _ _, fun n => ?_⟩
    rcases lt_or_ge n (K₀ + 1) with hn | hn
    · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.mpr hn))
    · exact le_max_of_le_left (hK₀ n (by omega)).le
  obtain ⟨Ma, hMa1, hMaB⟩ := hbdd ha
  obtain ⟨Mb, hMb1, hMbB⟩ := hbdd hb
  have hMa0 : 0 < Ma := lt_of_lt_of_le one_pos hMa1
  have hMb0 : 0 < Mb := lt_of_lt_of_le one_pos hMb1
  rw [tendsto_order]
  constructor
  · intro s hs
    simp at hs
  · intro s hs
    obtain ⟨b', hb'0, hb's⟩ := exists_between hs
    have hδa0 : 0 < b' * Mb⁻¹ := mul_pos hb'0 (inv_pos.mpr hMb0)
    have hδb0 : 0 < b' * Ma⁻¹ := mul_pos hb'0 (inv_pos.mpr hMa0)
    obtain ⟨Ka, hKa⟩ := Filter.eventually_atTop.mp (ha.eventually_lt_const hδa0)
    obtain ⟨Kb, hKb⟩ := Filter.eventually_atTop.mp (hb.eventually_lt_const hδb0)
    refine Filter.eventually_atTop.mpr ⟨Ka + Kb, fun n hn => ?_⟩
    refine (Finset.sup_lt_iff (by rw [bot_eq_zero]; exact hs)).mpr fun i hi => ?_
    have hcase : Ka ≤ i ∨ Kb ≤ n - i := by
      by_contra hcon
      push Not at hcon
      have h1 : i < Ka := hcon.1
      have h2 : n - i < Kb := hcon.2
      have h3 : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      omega
    rcases hcase with hcase | hcase
    · calc fa i * fb (n - i) ≤ fa i * Mb :=
            mul_le_mul_of_nonneg_left (hMbB _) zero_le
        _ < (b' * Mb⁻¹) * Mb :=
            mul_lt_mul_of_pos_right (hKa i hcase) hMb0
        _ = b' := by rw [mul_assoc, inv_mul_cancel₀ hMb0.ne', mul_one]
        _ < s := hb's
    · calc fa i * fb (n - i) ≤ Ma * fb (n - i) :=
            mul_le_mul_of_nonneg_right (hMaB _) zero_le
        _ < Ma * (b' * Ma⁻¹) :=
            mul_lt_mul_of_pos_left (hKb _ hcase) hMa0
        _ = b' := by rw [mul_comm b' _, ← mul_assoc, mul_inv_cancel₀ hMa0.ne',
            one_mul]
        _ < s := hb's

/-- **The convolution of coordinate sequences** (the coefficients of a product of
two series). -/
def convF (a b : ℕ → F) (n : ℕ) : F :=
  ∑ i ∈ Finset.range (n + 1), a i * b (n - i)

/-- Decay is preserved under convolution (Cauchy-product vanishing). -/
theorem tendsto_convF {ρ : NNReal} {a b : ℕ → F}
    (ha : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (a n))
      Filter.atTop (nhds 0))
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (convF F a b n))
      Filter.atTop (nhds 0) := by
  have hsup := tendsto_antidiagonal_sup_zero
    (fa := fun n => ρ ^ n * perfectoidValuation p F (a n))
    (fb := fun n => ρ ^ n * perfectoidValuation p F (b n)) ha hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsup
    (fun n => zero_le) fun n => ?_
  have h1 : perfectoidValuation p F (convF F a b n)
      ≤ (Finset.range (n + 1)).sup
        (fun i => perfectoidValuation p F (a i * b (n - i))) := by
    rw [convF]
    exact Valuation.map_sum_le _ fun i hi => Finset.le_sup
      (f := fun i => perfectoidValuation p F (a i * b (n - i))) hi
  have hne : (Finset.range (n + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)
  obtain ⟨i₀, hi₀mem, hi₀⟩ := Finset.exists_mem_eq_sup _ hne
    (fun i => perfectoidValuation p F (a i * b (n - i)))
  have hi₀n : i₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi₀mem)
  calc ρ ^ n * perfectoidValuation p F (convF F a b n)
      ≤ ρ ^ n * (Finset.range (n + 1)).sup
        (fun i => perfectoidValuation p F (a i * b (n - i))) :=
        mul_le_mul_of_nonneg_left h1 zero_le
    _ = ρ ^ n * perfectoidValuation p F (a i₀ * b (n - i₀)) := by rw [hi₀]
    _ = (ρ ^ i₀ * perfectoidValuation p F (a i₀))
        * (ρ ^ (n - i₀) * perfectoidValuation p F (b (n - i₀))) := by
        rw [Valuation.map_mul,
          show ρ ^ n = ρ ^ i₀ * ρ ^ (n - i₀) from by
            rw [← pow_add, Nat.add_sub_cancel' hi₀n]]
        ring
    _ ≤ (Finset.range (n + 1)).sup (fun i =>
          (ρ ^ i * perfectoidValuation p F (a i))
          * (ρ ^ (n - i) * perfectoidValuation p F (b (n - i)))) :=
        Finset.le_sup (f := fun i => (ρ ^ i * perfectoidValuation p F (a i))
          * (ρ ^ (n - i) * perfectoidValuation p F (b (n - i)))) hi₀mem

/-- Vanishing `NNReal` sequences have bounded range. -/
theorem bddAbove_range_of_tendsto_zero {f : ℕ → NNReal}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    BddAbove (Set.range f) := by
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (hf.eventually_lt_const one_pos)
  refine ⟨max 1 ((Finset.range (K₀ + 1)).sup f), ?_⟩
  rintro s ⟨n, rfl⟩
  rcases lt_or_ge n (K₀ + 1) with hn | hn
  · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.mpr hn))
  · exact le_max_of_le_left (hK₀ n (by omega)).le

/-- Total form of the `A^r` term bound (no nonvanishing hypothesis). -/
theorem gaussTerm_teichCoeffAr_le' {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (n : ℕ) :
    ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
      ≤ Valued.v x := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · have hx0 : x = 0 := (Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp h0
    rw [hx0, teichCoeffAr_zero, Valuation.map_zero, mul_zero]
    exact zero_le
  · exact gaussTerm_teichCoeffAr_le p F ϖ hx h0 n

/-- **Digit comparison (DC⁺)**: coordinate differences on `A^r` are controlled by
the value of the difference plus one `ρ`-damped term. The engine of Kedlaya's
Remark 2.7 at a single radius. -/
theorem digit_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (n : ℕ) :
    ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
        - teichCoeffAr p F ϖ hρ0 hρ1 y n)
      ≤ max (Valued.v (x - y)) (ρ * max (Valued.v x) (Valued.v y)) := by
  set a : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with ha
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 y with hb
  set e : ℕ → F := fun k => a k - b k with he
  have hdx := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  rw [← ha] at hdx
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  rw [← hb] at hdy
  have hde : Filter.Tendsto (fun k => ρ ^ k * perfectoidValuation p F (e k))
      Filter.atTop (nhds 0) := by
    have hbound : ∀ k, ρ ^ k * perfectoidValuation p F (e k)
        ≤ max (ρ ^ k * perfectoidValuation p F (a k))
            (ρ ^ k * perfectoidValuation p F (b k)) := by
      intro k
      refine le_trans (mul_le_mul_of_nonneg_left
        (Valuation.map_sub (perfectoidValuation p F) (a k) (b k)) zero_le) ?_
      exact (nnreal_mul_max _ _ _).le
    have hmax := hdx.max hdy
    have hmax' : Filter.Tendsto (fun k => max
        (ρ ^ k * perfectoidValuation p F (a k))
        (ρ ^ k * perfectoidValuation p F (b k))) Filter.atTop (nhds 0) := by
      simpa using hmax
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmax'
      (fun k => zero_le) hbound
  set M := max (Valued.v x) (Valued.v y) with hM
  have hΦe := valued_PhiHatK p F ϖ hρ0 hρ1 hde
  have hrx : PhiHatK p F ϖ hρ0 hρ1 a = x := by
    rw [ha]
    exact PhiHatK_teichCoeffAr p F ϖ hx
  have hry : PhiHatK p F ϖ hρ0 hρ1 b = y := by
    rw [hb]
    exact PhiHatK_teichCoeffAr p F ϖ hy
  have hSx : Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1
      (prefixAloc p F ϖ a N)) Filter.atTop (nhds x) := by
    have h1 := tendsto_PhiHatK p F ϖ hρ0 hρ1 hdx
    rwa [hrx] at h1
  have hSy : Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1
      (prefixAloc p F ϖ b N)) Filter.atTop (nhds y) := by
    have h1 := tendsto_PhiHatK p F ϖ hρ0 hρ1 hdy
    rwa [hry] at h1
  have hSe := tendsto_PhiHatK p F ϖ hρ0 hρ1 hde
  have hPNval : ∀ N : ℕ, Valued.v (AlocToHatK p F ϖ hρ0 hρ1
      (prefixAloc p F ϖ a N - prefixAloc p F ϖ b N - prefixAloc p F ϖ e N))
      ≤ ρ * M := by
    intro N
    rw [valued_AlocToHatK, ← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, map_sub,
      map_sub, alocToWittF_prefixAloc, alocToWittF_prefixAloc,
      alocToWittF_prefixAloc]
    have hdistrib : (∑ k ∈ Finset.range N,
          WittVector.teichmuller p (a k) * (p : WittVector p F) ^ k)
        - (∑ k ∈ Finset.range N,
          WittVector.teichmuller p (b k) * (p : WittVector p F) ^ k)
        - (∑ k ∈ Finset.range N,
          WittVector.teichmuller p (e k) * (p : WittVector p F) ^ k)
        = ∑ k ∈ Finset.range N, (p : WittVector p F) ^ k
          * (WittVector.teichmuller p (a k) - WittVector.teichmuller p (b k)
            - WittVector.teichmuller p (a k - b k)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hek : WittVector.teichmuller p (e k)
          = WittVector.teichmuller p (a k - b k) := rfl
      rw [hek]
      ring
    rw [hdistrib]
    refine (gaussValueF_finset_sum_le p F hρ0 hρ1 (ρ * M) (Finset.range N)
      _ fun k _ => ?_).2
    have hBtriple : BddAbove (Set.range (gaussTermF p F ρ
        (WittVector.teichmuller p (a k) - WittVector.teichmuller p (b k)
          - WittVector.teichmuller p (a k - b k)))) := by
      have h1 := bddAbove_gaussTermF_add p F hρ0 hρ1
        (bddAbove_gaussTermF_add p F hρ0 hρ1
          (bddAbove_gaussTermF_teichmuller p F (a k))
          (bddAbove_gaussTermF_neg p F hρ0 hρ1
            (bddAbove_gaussTermF_teichmuller p F (b k))))
        (bddAbove_gaussTermF_neg p F hρ0 hρ1
          (bddAbove_gaussTermF_teichmuller p F (a k - b k)))
      have h2 : WittVector.teichmuller p (a k) + -WittVector.teichmuller p (b k)
          + -WittVector.teichmuller p (a k - b k)
          = WittVector.teichmuller p (a k) - WittVector.teichmuller p (b k)
            - WittVector.teichmuller p (a k - b k) := by
        ring
      rwa [h2] at h1
    refine ⟨bddAbove_gaussTermF_p_pow_mul p F hBtriple k, ?_⟩
    rw [gaussValueF_p_pow_mul p F hBtriple k]
    refine le_trans (mul_le_mul_of_nonneg_left
      (gaussValueF_teichmuller_sub_sub_le p F hρ1.le (a k) (b k)) zero_le) ?_
    have h3 : ρ ^ k * (ρ * max (perfectoidValuation p F (a k))
        (perfectoidValuation p F (b k)))
        = ρ * max (ρ ^ k * perfectoidValuation p F (a k))
          (ρ ^ k * perfectoidValuation p F (b k)) := by
      rw [← mul_assoc, mul_comm (ρ ^ k) ρ, mul_assoc, nnreal_mul_max]
    rw [h3]
    refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) zero_le
    · exact le_trans (gaussTerm_teichCoeffAr_le' p F ϖ hx k) (le_max_left _ _)
    · exact le_trans (gaussTerm_teichCoeffAr_le' p F ϖ hy k) (le_max_right _ _)
  rcases eq_or_ne M 0 with hM0 | hM0
  · have hvx : Valued.v x = 0 :=
      le_antisymm (le_trans (le_max_left _ _) hM0.le) zero_le
    have hvy : Valued.v y = 0 :=
      le_antisymm (le_trans (le_max_right _ _) hM0.le) zero_le
    have hx0 : x = 0 := (Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp hvx
    have hy0 : y = 0 := (Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp hvy
    have hgoal : a n - b n = 0 := by
      rw [ha, hb, hx0, hy0, teichCoeffAr_zero, sub_zero]
    rw [hgoal, Valuation.map_zero, mul_zero]
    exact zero_le
  · have hρM : 0 < ρ * M := mul_pos hρ0 (pos_iff_ne_zero.mpr hM0)
    have hlim : Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1
        (prefixAloc p F ϖ a N - prefixAloc p F ϖ b N - prefixAloc p F ϖ e N))
        Filter.atTop (nhds ((x - y) - PhiHatK p F ϖ hρ0 hρ1 e)) := by
      have h1 := (hSx.sub hSy).sub hSe
      refine h1.congr fun N => ?_
      rw [map_sub, map_sub]
    have hH : Valued.v ((x - y) - PhiHatK p F ϖ hρ0 hρ1 e) ≤ ρ * M := by
      obtain ⟨N₀, hN₀⟩ := (eventually_valued_sub_le_of_tendsto p F
        (hρ0 := hρ0) (hρ1 := hρ1) hlim hρM).exists
      have h2 : (x - y) - PhiHatK p F ϖ hρ0 hρ1 e
          = (((x - y) - PhiHatK p F ϖ hρ0 hρ1 e)
              - AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ a N₀
                - prefixAloc p F ϖ b N₀ - prefixAloc p F ϖ e N₀))
            + AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ a N₀
                - prefixAloc p F ϖ b N₀ - prefixAloc p F ϖ e N₀) := by
        ring
      rw [h2]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ (hPNval N₀))
      rw [Valuation.map_sub_swap]
      exact hN₀
    have hΦval : Valued.v (PhiHatK p F ϖ hρ0 hρ1 e)
        ≤ max (Valued.v (x - y)) (ρ * M) := by
      have h3 : PhiHatK p F ϖ hρ0 hρ1 e
          = (x - y) - ((x - y) - PhiHatK p F ϖ hρ0 hρ1 e) := by
        ring
      rw [h3]
      exact le_trans (Valuation.map_sub _ _ _)
        (max_le (le_max_left _ _) (le_max_of_le_right hH))
    have hBe := bddAbove_range_of_tendsto_zero hde
    have h4 : ρ ^ n * perfectoidValuation p F (e n)
        ≤ ⨆ k, ρ ^ k * perfectoidValuation p F (e k) := le_ciSup hBe n
    calc ρ ^ n * perfectoidValuation p F (a n - b n)
        = ρ ^ n * perfectoidValuation p F (e n) := rfl
      _ ≤ ⨆ k, ρ ^ k * perfectoidValuation p F (e k) := h4
      _ = Valued.v (PhiHatK p F ϖ hρ0 hρ1 e) := hΦe.symm
      _ ≤ max (Valued.v (x - y)) (ρ * M) := hΦval

end FarguesFontaine

end
