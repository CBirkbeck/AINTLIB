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

/-- Total form of the `A^r` term bound (no nonvanishing hypothesis). -/
theorem gaussTerm_teichCoeffAr_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (n : ℕ) :
    ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
      ≤ Valued.v x := by
  rcases eq_or_ne (Valued.v x) 0 with h0 | h0
  · have hx0 : x = 0 := (Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp h0
    rw [hx0, teichCoeffAr_zero, Valuation.map_zero, mul_zero]
    exact zero_le
  · exact gaussTerm_teichCoeffAr_le_of_ne_zero p F ϖ hx h0 n

/-- **The uniform prefix bound.** For `x, y ∈ A^r` with digit sequences `a`, `b` and
digitwise difference `e = a - b`, every `Φ`-prefix of `a - b - e` has value at most
`ρ·max(‖x‖,‖y‖)`. Termwise `[aₖ] - [bₖ] - [aₖ - bₖ]` carries the Teichmüller bound
`ρ·max(|aₖ|,|bₖ|)`, which the `A^r` coordinate bound turns into `ρ·max(‖x‖,‖y‖)`
uniformly in `k`; the Gauss norm of a finite sum is then the max of the terms. -/
private theorem valued_prefix_sub_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (N : ℕ) :
    Valued.v (AlocToHatK p F ϖ hρ0 hρ1
        (prefixAloc p F ϖ (teichCoeffAr p F ϖ hρ0 hρ1 x) N
          - prefixAloc p F ϖ (teichCoeffAr p F ϖ hρ0 hρ1 y) N
          - prefixAloc p F ϖ (fun k => teichCoeffAr p F ϖ hρ0 hρ1 x k
              - teichCoeffAr p F ϖ hρ0 hρ1 y k) N))
      ≤ ρ * max (Valued.v x) (Valued.v y) := by
  set a : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with ha
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 y with hb
  set e : ℕ → F := fun k => a k - b k with he
  set M := max (Valued.v x) (Valued.v y) with hM
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
  · exact le_trans (gaussTerm_teichCoeffAr_le p F ϖ hx k) (le_max_left _ _)
  · exact le_trans (gaussTerm_teichCoeffAr_le p F ϖ hy k) (le_max_right _ _)

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
      ≤ ρ * M := fun N => valued_prefix_sub_sub_le p F ϖ hx hy N
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

/-- Values are stable under dominated perturbation (ultrametric isosceles). -/
theorem valued_eq_of_valued_sub_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hxy : Valued.v (x - y) < Valued.v x) :
    Valued.v y = Valued.v x := by
  have h1 : Valued.v (-(x - y)) < Valued.v x := by
    rw [Valuation.map_neg]
    exact hxy
  have h2 : y = x + -(x - y) := by ring
  rw [h2, Valuation.map_add_eq_of_lt_left _ h1]

/-- **Remark 2.7 (leading-support stability)**: a perturbation strictly below the
value changes no radius-`ρ` attaining index — the degrees agree. -/
theorem degAr_eq_of_valued_sub_lt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hxy : Valued.v (x - y) < Valued.v x) :
    degAr p F ϖ hρ0 hρ1 x = degAr p F ϖ hρ0 hρ1 y := by
  have hvy : Valued.v y = Valued.v x := valued_eq_of_valued_sub_lt p F hxy
  have hApos : 0 < Valued.v x := lt_of_le_of_lt zero_le hxy
  have hBA : max (Valued.v (x - y)) (ρ * Valued.v x) < Valued.v x :=
    max_lt hxy (mul_lt_of_lt_one_left hApos hρ1)
  have hδ : ∀ n, ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
      - teichCoeffAr p F ϖ hρ0 hρ1 y n)
      ≤ max (Valued.v (x - y)) (ρ * Valued.v x) := by
    intro n
    have h3 := digit_sub_le p F ϖ hx hy n
    rwa [hvy, max_self] at h3
  have hsets : {n | Valued.v x = ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x n)}
      = {n | Valued.v y = ρ ^ n * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 y n)} := by
    ext n
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hax
      have hxle : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
          ≤ max (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y n))
            (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
              - teichCoeffAr p F ϖ hρ0 hρ1 y n)) := by
        have h4 : teichCoeffAr p F ϖ hρ0 hρ1 x n
            = teichCoeffAr p F ϖ hρ0 hρ1 y n + (teichCoeffAr p F ϖ hρ0 hρ1 x n
              - teichCoeffAr p F ϖ hρ0 hρ1 y n) := by
          ring
        conv_lhs => rw [h4]
        refine le_trans (mul_le_mul_of_nonneg_left
          (Valuation.map_add _ _ _) zero_le) ?_
        exact (nnreal_mul_max _ _ _).le
      have h5 : Valued.v x ≤ max
          (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y n))
          (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
            - teichCoeffAr p F ϖ hρ0 hρ1 y n)) := hax ▸ hxle
      have h6 : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y n)
          ≤ Valued.v x := by
        rw [← hvy]
        exact gaussTerm_teichCoeffAr_le p F ϖ hy n
      rcases max_cases
        (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y n))
        (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
          - teichCoeffAr p F ϖ hρ0 hρ1 y n)) with ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at h5
        rw [hvy]
        exact (le_antisymm h6 h5).symm
      · rw [heq] at h5
        exact absurd (lt_of_le_of_lt (le_trans h5 (hδ n)) hBA) (lt_irrefl _)
    · intro hay
      have hyle : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y n)
          ≤ max (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n))
            (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
              - teichCoeffAr p F ϖ hρ0 hρ1 y n)) := by
        have h4 : teichCoeffAr p F ϖ hρ0 hρ1 y n
            = teichCoeffAr p F ϖ hρ0 hρ1 x n - (teichCoeffAr p F ϖ hρ0 hρ1 x n
              - teichCoeffAr p F ϖ hρ0 hρ1 y n) := by
          ring
        conv_lhs => rw [h4]
        refine le_trans (mul_le_mul_of_nonneg_left
          (Valuation.map_sub _ _ _) zero_le) ?_
        exact (nnreal_mul_max _ _ _).le
      have h5 : Valued.v x ≤ max
          (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n))
          (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
            - teichCoeffAr p F ϖ hρ0 hρ1 y n)) := by
        rw [← hvy]
        exact hay ▸ hyle
      have h6 : ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
          ≤ Valued.v x := gaussTerm_teichCoeffAr_le p F ϖ hx n
      rcases max_cases
        (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n))
        (ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n
          - teichCoeffAr p F ϖ hρ0 hρ1 y n)) with ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at h5
        exact (le_antisymm h6 h5).symm
      · rw [heq] at h5
        exact absurd (lt_of_le_of_lt (le_trans h5 (hδ n)) hBA) (lt_irrefl _)
  rw [degAr, degAr, hsets]

/-- The `Aloc` partial sums of the double series `Σₙ pⁿ·Σ_{i+j=n}[aᵢbⱼ]` (Kedlaya's
`T_N`, the antidiagonal regrouping of a prefix product). -/
def convPartialAloc (a b : ℕ → F) (N : ℕ) : Aloc p F ϖ :=
  ∑ n ∈ Finset.range N, (p : Aloc p F ϖ) ^ n
    * ∑ k ∈ Finset.range (n + 1), alocTeich p F ϖ (a k * b (n - k))

/-- `alocToWittF` sends the convolution partial to the Witt-side double sum. -/
theorem alocToWittF_convPartialAloc (a b : ℕ → F) (N : ℕ) :
    alocToWittF p F ϖ (convPartialAloc p F ϖ a b N)
      = ∑ n ∈ Finset.range N, (p : WittVector p F) ^ n
        * ∑ k ∈ Finset.range (n + 1),
          WittVector.teichmuller p (a k * b (n - k)) := by
  rw [convPartialAloc, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_pow, map_natCast, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [alocToWittF_alocTeich]

/-- **The Witt-addition error of the convolution partials** (sol step 3): the
partials differ from the convolution prefixes by at most `ρ·v(x)v(y)` — uniformly
in `N`. -/
theorem gaussValueF_convPartial_sub_prefix_le {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a b : ℕ → F) {A B : NNReal}
    (hA : ∀ n, ρ ^ n * perfectoidValuation p F (a n) ≤ A)
    (hB : ∀ n, ρ ^ n * perfectoidValuation p F (b n) ≤ B) (N : ℕ) :
    gaussValueF p F ρ (alocToWittF p F ϖ (convPartialAloc p F ϖ a b N)
        - alocToWittF p F ϖ (prefixAloc p F ϖ (convF F a b) N))
      ≤ ρ * (A * B) := by
  rw [alocToWittF_convPartialAloc, alocToWittF_prefixAloc]
  have hdistrib : (∑ n ∈ Finset.range N, (p : WittVector p F) ^ n
        * ∑ k ∈ Finset.range (n + 1),
          WittVector.teichmuller p (a k * b (n - k)))
      - (∑ n ∈ Finset.range N,
          WittVector.teichmuller p (convF F a b n) * (p : WittVector p F) ^ n)
      = ∑ n ∈ Finset.range N, (p : WittVector p F) ^ n
        * ((∑ k ∈ Finset.range (n + 1),
            WittVector.teichmuller p (a k * b (n - k)))
          - WittVector.teichmuller p (convF F a b n)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hdistrib]
  refine (gaussValueF_finset_sum_le p F hρ0 hρ1 (ρ * (A * B)) (Finset.range N)
    _ fun n _ => ?_).2
  set Bn : NNReal := (Finset.range (n + 1)).sup
    (fun k => perfectoidValuation p F (a k * b (n - k))) with hBn
  have hf : ∀ k ∈ Finset.range (n + 1),
      perfectoidValuation p F (a k * b (n - k)) ≤ Bn :=
    fun k hk => Finset.le_sup
      (f := fun k => perfectoidValuation p F (a k * b (n - k))) hk
  have hq := gaussValueF_teichmuller_sum_sub_le p F hρ0 hρ1
    (Finset.range (n + 1)) (fun k => a k * b (n - k)) hf
  have hBq : BddAbove (Set.range (gaussTermF p F ρ
      ((∑ k ∈ Finset.range (n + 1),
        WittVector.teichmuller p (a k * b (n - k)))
        - WittVector.teichmuller p (convF F a b n)))) := by
    have hBsum : BddAbove (Set.range (gaussTermF p F ρ
        (∑ k ∈ Finset.range (n + 1),
          WittVector.teichmuller p (a k * b (n - k))))) :=
      (gaussValueF_finset_sum_le p F hρ0 hρ1 Bn (Finset.range (n + 1))
        (fun k => WittVector.teichmuller p (a k * b (n - k)))
        (fun k hk => ⟨bddAbove_gaussTermF_teichmuller p F _, by
          rw [gaussValueF_teichmuller]
          exact hf k hk⟩)).1
    have h1 := bddAbove_gaussTermF_add p F hρ0 hρ1 hBsum
      (bddAbove_gaussTermF_neg p F hρ0 hρ1
        (bddAbove_gaussTermF_teichmuller p F (convF F a b n)))
    rwa [← sub_eq_add_neg] at h1
  refine ⟨bddAbove_gaussTermF_p_pow_mul p F hBq n, ?_⟩
  rw [gaussValueF_p_pow_mul p F hBq n]
  have hqconv : gaussValueF p F ρ
      ((∑ k ∈ Finset.range (n + 1),
        WittVector.teichmuller p (a k * b (n - k)))
        - WittVector.teichmuller p (convF F a b n)) ≤ ρ * Bn := hq
  refine le_trans (mul_le_mul_of_nonneg_left hqconv zero_le) ?_
  -- ρⁿ·(ρ·Bₙ) ≤ ρ·(A·B): reduces to ρⁿ·Bₙ ≤ A·B via the attained index
  have hscaled : ρ ^ n * Bn ≤ A * B := by
    rw [hBn]
    rcases Finset.eq_empty_or_nonempty (Finset.range (n + 1)) with hemp | hne
    · exact absurd hemp (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)).ne_empty
    · obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_mem_eq_sup _ hne
        (fun k => perfectoidValuation p F (a k * b (n - k)))
      rw [hk₀]
      have hk₀n : k₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀mem)
      calc ρ ^ n * perfectoidValuation p F (a k₀ * b (n - k₀))
          = (ρ ^ k₀ * perfectoidValuation p F (a k₀))
            * (ρ ^ (n - k₀) * perfectoidValuation p F (b (n - k₀))) := by
            rw [Valuation.map_mul,
              show ρ ^ n = ρ ^ k₀ * ρ ^ (n - k₀) from by
                rw [← pow_add, Nat.add_sub_cancel' hk₀n]]
            ring
        _ ≤ A * B := mul_le_mul (hA k₀) (hB (n - k₀)) zero_le zero_le
  calc ρ ^ n * (ρ * Bn) = ρ * (ρ ^ n * Bn) := by ring
    _ ≤ ρ * (A * B) := mul_le_mul_of_nonneg_left hscaled zero_le

/-- **The prefix-product tail** (sol step 2, identity (10)): a prefix product
differs from the convolution partial only in antidiagonal terms of total index at
least `N`, so any uniform tail bound controls the difference. -/
theorem gaussValueF_prefix_mul_sub_convPartial_le {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a b : ℕ → F) {T : NNReal} (N : ℕ)
    (hT : ∀ i j : ℕ, N ≤ i + j →
      (ρ ^ i * perfectoidValuation p F (a i))
        * (ρ ^ j * perfectoidValuation p F (b j)) ≤ T) :
    gaussValueF p F ρ
      (alocToWittF p F ϖ (prefixAloc p F ϖ a N)
          * alocToWittF p F ϖ (prefixAloc p F ϖ b N)
        - alocToWittF p F ϖ (convPartialAloc p F ϖ a b N)) ≤ T := by
  classical
  rw [alocToWittF_prefixAloc, alocToWittF_prefixAloc, alocToWittF_convPartialAloc]
  set box : Finset (ℕ × ℕ) := Finset.range N ×ˢ Finset.range N with hbox
  set TRI : Finset (ℕ × ℕ) := (Finset.range N).biUnion
    (fun n => Finset.antidiagonal n) with hTRI
  have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
      (fun n => (Finset.antidiagonal n : Finset (ℕ × ℕ))) := by
    intro m _ n _ hmn
    simp only [Function.onFun, Finset.disjoint_left]
    intro q hqm hqn
    exact hmn (by rw [← Finset.mem_antidiagonal.mp hqm,
      ← Finset.mem_antidiagonal.mp hqn])
  have hprod : (∑ i ∈ Finset.range N,
        WittVector.teichmuller p (a i) * (p : WittVector p F) ^ i)
      * (∑ j ∈ Finset.range N,
        WittVector.teichmuller p (b j) * (p : WittVector p F) ^ j)
      = ∑ q ∈ box, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2) := by
    have hnested : (∑ q ∈ box, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2))
        = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (p : WittVector p F) ^ (i + j)
            * WittVector.teichmuller p (a i * b j) :=
      Finset.sum_product' (Finset.range N) (Finset.range N)
        (fun i j => (p : WittVector p F) ^ (i + j)
          * WittVector.teichmuller p (a i * b j))
    rw [hnested, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, pow_add]
    ring
  have hanti : ∀ n : ℕ, (∑ q ∈ Finset.antidiagonal n,
      WittVector.teichmuller p (a q.1 * b q.2))
      = ∑ k ∈ Finset.range (n + 1), WittVector.teichmuller p (a k * b (n - k)) :=
    fun n => Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ n
  have hpartial : (∑ n ∈ Finset.range N, (p : WittVector p F) ^ n
      * ∑ k ∈ Finset.range (n + 1), WittVector.teichmuller p (a k * b (n - k)))
      = ∑ q ∈ TRI, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2) := by
    rw [hTRI, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hanti n, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [Finset.mem_antidiagonal.mp hq]
  have hsub : TRI ⊆ box := by
    intro q hq
    rw [hTRI, Finset.mem_biUnion] at hq
    obtain ⟨n, hn, hqn⟩ := hq
    have hq' : q.1 + q.2 = n := Finset.mem_antidiagonal.mp hqn
    have hnN : n < N := Finset.mem_range.mp hn
    rw [hbox, Finset.mem_product]
    constructor
    · exact Finset.mem_range.mpr (lt_of_le_of_lt
        (le_trans (Nat.le_add_right _ _) hq'.le) hnN)
    · exact Finset.mem_range.mpr (lt_of_le_of_lt
        (le_trans (Nat.le_add_left _ _) hq'.le) hnN)
  have hdiff : (∑ q ∈ box, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2))
      - (∑ q ∈ TRI, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2))
      = ∑ q ∈ box \ TRI, (p : WittVector p F) ^ (q.1 + q.2)
        * WittVector.teichmuller p (a q.1 * b q.2) :=
    (eq_sub_of_add_eq (Finset.sum_sdiff hsub)).symm
  rw [hprod, hpartial, hdiff]
  refine (gaussValueF_finset_sum_le p F hρ0 hρ1 T (box \ TRI) _ fun q hq => ?_).2
  have hqmem := Finset.mem_sdiff.mp hq
  have hqN : N ≤ q.1 + q.2 := by
    by_contra hcon
    push Not at hcon
    refine hqmem.2 ?_
    rw [hTRI, Finset.mem_biUnion]
    exact ⟨q.1 + q.2, Finset.mem_range.mpr hcon, Finset.mem_antidiagonal.mpr rfl⟩
  refine ⟨bddAbove_gaussTermF_p_pow_mul p F
    (bddAbove_gaussTermF_teichmuller p F _) _, ?_⟩
  rw [gaussValueF_p_pow_mul p F (bddAbove_gaussTermF_teichmuller p F _) _,
    gaussValueF_teichmuller]
  calc ρ ^ (q.1 + q.2) * perfectoidValuation p F (a q.1 * b q.2)
      = (ρ ^ q.1 * perfectoidValuation p F (a q.1))
        * (ρ ^ q.2 * perfectoidValuation p F (b q.2)) := by
        rw [Valuation.map_mul, pow_add]
        ring
    _ ≤ T := hT q.1 q.2 hqN

/-- **The product decomposition** (sol (13), Kedlaya's leading-term control): a
product on `A^r` differs from the `Φ`-series of the coordinate convolution by at
most `ρ·v(x)v(y)`. -/
theorem valued_mul_sub_PhiHatK_convF_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) :
    Valued.v (x * y - PhiHatK p F ϖ hρ0 hρ1
        (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x) (teichCoeffAr p F ϖ hρ0 hρ1 y)))
      ≤ ρ * (Valued.v x * Valued.v y) := by
  set a : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with ha
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 y with hb
  have hdx := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  rw [← ha] at hdx
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  rw [← hb] at hdy
  have hdc := tendsto_convF p F hdx hdy
  have hA : ∀ n, ρ ^ n * perfectoidValuation p F (a n) ≤ Valued.v x :=
    fun n => gaussTerm_teichCoeffAr_le p F ϖ hx n
  have hB : ∀ n, ρ ^ n * perfectoidValuation p F (b n) ≤ Valued.v y :=
    fun n => gaussTerm_teichCoeffAr_le p F ϖ hy n
  rcases eq_or_ne (Valued.v x * Valued.v y) 0 with hvv | hvv
  · -- degenerate: all convolution terms vanish, both sides of the difference do
    have hterm0 : ∀ n, ρ ^ n * perfectoidValuation p F (convF F a b n) = 0 := by
      intro n
      refine le_antisymm ?_ zero_le
      have h1 : perfectoidValuation p F (convF F a b n)
          ≤ (Finset.range (n + 1)).sup
            (fun k => perfectoidValuation p F (a k * b (n - k))) := by
        rw [convF]
        exact Valuation.map_sum_le _ fun k hk => Finset.le_sup
          (f := fun k => perfectoidValuation p F (a k * b (n - k))) hk
      refine le_trans (mul_le_mul_of_nonneg_left h1 zero_le) ?_
      rw [← hvv]
      rcases Finset.eq_empty_or_nonempty (Finset.range (n + 1)) with hemp | hne
      · exact absurd hemp
          (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)).ne_empty
      obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_mem_eq_sup _ hne
        (fun k => perfectoidValuation p F (a k * b (n - k)))
      rw [hk₀]
      have hk₀n : k₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀mem)
      calc ρ ^ n * perfectoidValuation p F (a k₀ * b (n - k₀))
          = (ρ ^ k₀ * perfectoidValuation p F (a k₀))
            * (ρ ^ (n - k₀) * perfectoidValuation p F (b (n - k₀))) := by
            rw [Valuation.map_mul,
              show ρ ^ n = ρ ^ k₀ * ρ ^ (n - k₀) from by
                rw [← pow_add, Nat.add_sub_cancel' hk₀n]]
            ring
        _ ≤ Valued.v x * Valued.v y :=
            mul_le_mul (hA k₀) (hB (n - k₀)) zero_le zero_le
    have hΦ0 : Valued.v (PhiHatK p F ϖ hρ0 hρ1 (convF F a b)) = 0 := by
      rw [valued_PhiHatK p F ϖ hρ0 hρ1 hdc]
      exact le_antisymm (ciSup_le fun n => (hterm0 n).le) zero_le
    have hvxy : Valued.v (x * y) = 0 := by
      rw [Valuation.map_mul]
      exact hvv
    refine le_trans (le_trans (Valuation.map_sub _ _ _) (max_le hvxy.le hΦ0.le))
      zero_le
  · -- main branch
    have hvx0 : Valued.v x ≠ 0 := fun h => hvv (by rw [h, zero_mul])
    have hvy0 : Valued.v y ≠ 0 := fun h => hvv (by rw [h, mul_zero])
    have hρvv : 0 < ρ * (Valued.v x * Valued.v y) :=
      mul_pos hρ0 (pos_iff_ne_zero.mpr hvv)
    -- the three convergences
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
    have hSxy := hSx.mul hSy
    have hSc := tendsto_PhiHatK p F ϖ hρ0 hρ1 hdc
    have ev1 := eventually_valued_sub_le_of_tendsto p F
      (hρ0 := hρ0) (hρ1 := hρ1) hSxy hρvv
    have ev2 := eventually_valued_sub_le_of_tendsto p F
      (hρ0 := hρ0) (hρ1 := hρ1) hSc hρvv
    -- the tail threshold for (I₁)
    have hvxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr hvx0
    have hvypos : 0 < Valued.v y := pos_iff_ne_zero.mpr hvy0
    have hρvx : 0 < ρ * Valued.v x := mul_pos hρ0 hvxpos
    have hρvy : 0 < ρ * Valued.v y := mul_pos hρ0 hvypos
    obtain ⟨Ka, hKa⟩ := Filter.eventually_atTop.mp (hdx.eventually_lt_const hρvx)
    obtain ⟨Kb, hKb⟩ := Filter.eventually_atTop.mp (hdy.eventually_lt_const hρvy)
    have hT : ∀ N, Ka + Kb ≤ N → ∀ i j : ℕ, N ≤ i + j →
        (ρ ^ i * perfectoidValuation p F (a i))
          * (ρ ^ j * perfectoidValuation p F (b j))
        ≤ ρ * (Valued.v x * Valued.v y) := by
      intro N hN i j hij
      have hcase : Ka ≤ i ∨ Kb ≤ j := by
        by_contra hcon
        push Not at hcon
        omega
      rcases hcase with hcase | hcase
      · calc (ρ ^ i * perfectoidValuation p F (a i))
              * (ρ ^ j * perfectoidValuation p F (b j))
            ≤ (ρ ^ i * perfectoidValuation p F (a i)) * Valued.v y :=
              mul_le_mul_of_nonneg_left (hB j) zero_le
          _ ≤ (ρ * Valued.v x) * Valued.v y :=
              mul_le_mul_of_nonneg_right (hKa i hcase).le zero_le
          _ = ρ * (Valued.v x * Valued.v y) := by ring
      · calc (ρ ^ i * perfectoidValuation p F (a i))
              * (ρ ^ j * perfectoidValuation p F (b j))
            ≤ Valued.v x * (ρ ^ j * perfectoidValuation p F (b j)) :=
              mul_le_mul_of_nonneg_right (hA i) zero_le
          _ ≤ Valued.v x * (ρ * Valued.v y) :=
              mul_le_mul_of_nonneg_left (hKb j hcase).le zero_le
          _ = ρ * (Valued.v x * Valued.v y) := by ring
    obtain ⟨N, hNall⟩ :=
      ((ev1.and ev2).and (Filter.eventually_ge_atTop (Ka + Kb))).exists
    obtain ⟨⟨hN1, hN2⟩, hNge⟩ := hNall
    -- the four-term chain
    have hchain : x * y - PhiHatK p F ϖ hρ0 hρ1 (convF F a b)
        = (x * y - AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ a N)
            * AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))
          + ((AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ a N)
              * AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)
            - AlocToHatK p F ϖ hρ0 hρ1 (convPartialAloc p F ϖ a b N))
          + ((AlocToHatK p F ϖ hρ0 hρ1 (convPartialAloc p F ϖ a b N)
              - AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ (convF F a b) N))
            + (AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ (convF F a b) N)
              - PhiHatK p F ϖ hρ0 hρ1 (convF F a b)))) := by
      ring
    rw [hchain]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_sub_swap]
      exact hN1
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [← map_mul, ← map_sub, valued_AlocToHatK,
        ← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, map_sub, map_mul]
      exact gaussValueF_prefix_mul_sub_convPartial_le p F ϖ hρ0 hρ1 a b N
        (hT N hNge)
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [← map_sub, valued_AlocToHatK,
        ← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, map_sub]
      exact gaussValueF_convPartial_sub_prefix_le p F ϖ hρ0 hρ1 a b hA hB N
    · exact hN2

/-- Scaled convolution terms are bounded by the product of the input bounds. -/
theorem gaussTerm_convF_le {ρ : NNReal} (a b : ℕ → F) {A B : NNReal}
    (hA : ∀ n, ρ ^ n * perfectoidValuation p F (a n) ≤ A)
    (hB : ∀ n, ρ ^ n * perfectoidValuation p F (b n) ≤ B) (n : ℕ) :
    ρ ^ n * perfectoidValuation p F (convF F a b n) ≤ A * B := by
  have h1 : perfectoidValuation p F (convF F a b n)
      ≤ (Finset.range (n + 1)).sup
        (fun k => perfectoidValuation p F (a k * b (n - k))) := by
    rw [convF]
    exact Valuation.map_sum_le _ fun k hk => Finset.le_sup
      (f := fun k => perfectoidValuation p F (a k * b (n - k))) hk
  refine le_trans (mul_le_mul_of_nonneg_left h1 zero_le) ?_
  have hne : (Finset.range (n + 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero n)
  obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_mem_eq_sup _ hne
    (fun k => perfectoidValuation p F (a k * b (n - k)))
  rw [hk₀]
  have hk₀n : k₀ ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₀mem)
  calc ρ ^ n * perfectoidValuation p F (a k₀ * b (n - k₀))
      = (ρ ^ k₀ * perfectoidValuation p F (a k₀))
        * (ρ ^ (n - k₀) * perfectoidValuation p F (b (n - k₀))) := by
        rw [Valuation.map_mul,
          show ρ ^ n = ρ ^ k₀ * ρ ^ (n - k₀) from by
            rw [← pow_add, Nat.add_sub_cancel' hk₀n]]
        ring
    _ ≤ A * B := mul_le_mul (hA k₀) (hB (n - k₀)) zero_le zero_le

/-- **Off-diagonal antidiagonal products are strictly dominated.** For nonzero `x, y ∈ A^r`
with dominant indices `m = deg x` and `l = deg y`, an antidiagonal pair `(k, n − k)` missing
`(m, l)` on either side has product strictly below `‖x‖·‖y‖`: the missed factor drops
strictly (`gaussTerm_lt_of_degAr_lt`) while the other stays bounded by its norm. -/
private theorem gaussTerm_mul_lt_of_ne_dominant {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (n k : ℕ)
    (hcase : degAr p F ϖ hρ0 hρ1 x < k ∨ degAr p F ϖ hρ0 hρ1 y < n - k) :
    (ρ ^ k * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x k))
        * (ρ ^ (n - k) * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 y (n - k)))
      < Valued.v x * Valued.v y := by
  have hvxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0)
  have hvypos : 0 < Valued.v y := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hy0)
  rcases hcase with hcase | hcase
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (gaussTerm_teichCoeffAr_le p F ϖ hy (n - k)) zero_le)
      (mul_lt_mul_of_pos_right (gaussTerm_lt_of_degAr_lt p F ϖ hx hx0 hcase) hvypos)
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (gaussTerm_teichCoeffAr_le p F ϖ hx k) zero_le)
      (mul_lt_mul_of_pos_left (gaussTerm_lt_of_degAr_lt p F ϖ hy hy0 hcase) hvxpos)

/-- **Antidiagonal sums away from the dominant pair are strictly dominated.** If every
index `k` of the finite set `S` gives an antidiagonal pair `(k, n − k)` whose scaled
coordinate product is `< c`, then the whole sum `∑_{k ∈ S} a k · b (n − k)` scales to
strictly below `c` as well.

The valuation of a sum is at most the sup of the terms, so it suffices to bound the
maximising term — and that term is one of the pairs the hypothesis covers. The empty sum
is handled separately, where the bound is just `0 < c`. -/
private theorem valued_sum_antidiagonal_lt {ρ : NNReal} (hρ0 : 0 < ρ) {c : NNReal}
    (hc : 0 < c) (a b : ℕ → F) (n : ℕ) (S : Finset ℕ) (hSn : ∀ k ∈ S, k ≤ n)
    (hlt : ∀ k ∈ S, (ρ ^ k * perfectoidValuation p F (a k))
      * (ρ ^ (n - k) * perfectoidValuation p F (b (n - k))) < c) :
    ρ ^ n * perfectoidValuation p F (∑ k ∈ S, a k * b (n - k)) < c := by
  rcases Finset.eq_empty_or_nonempty S with hemp | hne
  · rw [hemp, Finset.sum_empty, Valuation.map_zero, mul_zero]
    exact hc
  · have h1 : perfectoidValuation p F (∑ k ∈ S, a k * b (n - k))
        ≤ S.sup (fun k => perfectoidValuation p F (a k * b (n - k))) :=
      Valuation.map_sum_le _ fun k hk => Finset.le_sup
        (f := fun k => perfectoidValuation p F (a k * b (n - k))) hk
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 zero_le) ?_
    obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_mem_eq_sup _ hne
      (fun k => perfectoidValuation p F (a k * b (n - k)))
    rw [hk₀]
    calc ρ ^ n * perfectoidValuation p F (a k₀ * b (n - k₀))
        = (ρ ^ k₀ * perfectoidValuation p F (a k₀))
          * (ρ ^ (n - k₀) * perfectoidValuation p F (b (n - k₀))) := by
          rw [Valuation.map_mul,
            show ρ ^ n = ρ ^ k₀ * ρ ^ (n - k₀) from by
              rw [← pow_add, Nat.add_sub_cancel' (hSn k₀ hk₀mem)]]
          ring
      _ < c := hlt k₀ hk₀mem

/-- **The convolution attains `‖x‖·‖y‖` at index `deg x + deg y`.** At that index the
antidiagonal carries exactly one dominant term `a_m · b_l`, whose scaled value is the
product of the two attained values; every other term is strictly smaller
(`gaussTerm_mul_lt_of_ne_dominant`), so the ultrametric sum equals the dominant one. -/
private theorem gaussTerm_convF_attain {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ρ ^ (degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y) * perfectoidValuation p F
        (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x) (teichCoeffAr p F ϖ hρ0 hρ1 y)
          (degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y))
      = Valued.v x * Valued.v y := by
  set a : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with ha
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 y with hb
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  set l := degAr p F ϖ hρ0 hρ1 y with hl
  obtain ⟨hxattain, -⟩ := degAr_spec p F ϖ hx hx0
  obtain ⟨hyattain, -⟩ := degAr_spec p F ϖ hy hy0
  have hvxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0)
  have hvypos : 0 < Valued.v y := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hy0)
  have hlead : ρ ^ (m + l) * perfectoidValuation p F (a m * b l)
      = Valued.v x * Valued.v y := by
    calc ρ ^ (m + l) * perfectoidValuation p F (a m * b l)
        = (ρ ^ m * perfectoidValuation p F (a m))
          * (ρ ^ l * perfectoidValuation p F (b l)) := by
          rw [Valuation.map_mul, pow_add]
          ring
      _ = Valued.v x * Valued.v y := by rw [← hxattain, ← hyattain]
  have hrest : ρ ^ (m + l) * perfectoidValuation p F
      (∑ k ∈ (Finset.range (m + l + 1)).erase m, a k * b (m + l - k))
      < Valued.v x * Valued.v y :=
    valued_sum_antidiagonal_lt p F hρ0 (mul_pos hvxpos hvypos) a b (m + l) _
      (fun k hk => Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hk)))
      (fun k hk => gaussTerm_mul_lt_of_ne_dominant p F ϖ hx hy hx0 hy0 (m + l) k
        (by have := Finset.ne_of_mem_erase hk
            have := Nat.lt_succ_iff.mp
              (Finset.mem_range.mp (Finset.mem_of_mem_erase hk))
            omega))
  rw [show convF F a b (m + l) = a m * b l + ∑ k ∈ (Finset.range (m + l + 1)).erase m,
      a k * b (m + l - k) from by
    rw [convF, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (by omega : m < m + l + 1)),
      show m + l - m = l from by omega]]
  rw [Valuation.map_add_eq_of_lt_left _ (lt_of_mul_lt_mul_left
    (by rw [hlead]; exact hrest) zero_le)]
  exact hlead

/-- **The convolution drops strictly above `deg x + deg y`.** Past that index every
antidiagonal pair misses the dominant one, so the whole sum is strictly dominated. -/
private theorem gaussTerm_convF_lt_of_gt {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) {n : ℕ}
    (hn : degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y < n) :
    ρ ^ n * perfectoidValuation p F (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x)
        (teichCoeffAr p F ϖ hρ0 hρ1 y) n)
      < Valued.v x * Valued.v y := by
  have hvxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0)
  have hvypos : 0 < Valued.v y := pos_iff_ne_zero.mpr
    ((Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hy0)
  rw [convF]
  exact valued_sum_antidiagonal_lt p F hρ0 (mul_pos hvxpos hvypos) _ _ n _
    (fun k hk => Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    (fun k hk => gaussTerm_mul_lt_of_ne_dominant p F ϖ hx hy hx0 hy0 n k
      (by have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk); omega))

/-- **The value is multiplicative under convolution** (Kedlaya Lemma 2.6, value half):
reconstructing the convolution of the two coordinate sequences gives an element of value
`‖x‖·‖y‖`.  The upper bound is termwise; the lower bound is attainment at
`deg x + deg y`. -/
theorem valued_PhiHatK_convF {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    Valued.v (PhiHatK p F ϖ hρ0 hρ1 (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x)
        (teichCoeffAr p F ϖ hρ0 hρ1 y)))
      = Valued.v x * Valued.v y := by
  have hdx := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  have hdc := tendsto_convF p F hdx hdy
  rw [valued_PhiHatK p F ϖ hρ0 hρ1 hdc]
  refine le_antisymm (ciSup_le fun n => gaussTerm_convF_le p F _ _
    (fun n => gaussTerm_teichCoeffAr_le p F ϖ hx n)
    (fun n => gaussTerm_teichCoeffAr_le p F ϖ hy n) n) ?_
  have h1 := le_ciSup (bddAbove_range_of_tendsto_zero hdc)
    (degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y)
  rwa [gaussTerm_convF_attain p F ϖ hx hy hx0 hy0] at h1

/-- **The degree is additive under convolution** (Kedlaya Lemma 2.6, degree half).  The
attainment set of the reconstruction is bounded above by `deg x + deg y` and contains it,
so its supremum is exactly that. -/
theorem degAr_PhiHatK_convF {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    degAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1
        (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x) (teichCoeffAr p F ϖ hρ0 hρ1 y)))
      = degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y := by
  have hΦval := valued_PhiHatK_convF p F ϖ hx hy hx0 hy0
  have hattain := gaussTerm_convF_attain p F ϖ hx hy hx0 hy0
  set a : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with ha
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 y with hb
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  set l := degAr p F ϖ hρ0 hρ1 y with hl
  have hdx := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  rw [← ha] at hdx
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  rw [← hb] at hdy
  have hdc := tendsto_convF p F hdx hdy
  have hset : {n | Valued.v (PhiHatK p F ϖ hρ0 hρ1 (convF F a b))
      = ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1
        (PhiHatK p F ϖ hρ0 hρ1 (convF F a b)) n)}
      = {n | Valued.v x * Valued.v y
        = ρ ^ n * perfectoidValuation p F (convF F a b n)} := by
    ext n
    simp only [Set.mem_setOf_eq, teichCoeffAr_PhiHatK p F ϖ hρ0 hρ1 hdc n, hΦval]
  rw [degAr, hset]
  have hub : ∀ n ∈ {n | Valued.v x * Valued.v y
      = ρ ^ n * perfectoidValuation p F (convF F a b n)}, n ≤ m + l := by
    intro n hn
    by_contra hcon
    push Not at hcon
    have h2 := gaussTerm_convF_lt_of_gt p F ϖ hx hy hx0 hy0 hcon
    rw [← hn] at h2
    exact absurd h2 (lt_irrefl _)
  exact le_antisymm (csSup_le ⟨m + l, hattain.symm⟩ hub)
    (le_csSup ⟨m + l, hub⟩ hattain.symm)

/-- **Degree of the convolution series** (sol step 4): the unique dominant
antidiagonal term at `deg x + deg y` makes `Φ(conv)` attain `v(x)v(y)` there and
drop strictly above. -/
theorem valued_degAr_PhiHatK_convF {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    Valued.v (PhiHatK p F ϖ hρ0 hρ1 (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x)
        (teichCoeffAr p F ϖ hρ0 hρ1 y))) = Valued.v x * Valued.v y
      ∧ degAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1
          (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x) (teichCoeffAr p F ϖ hρ0 hρ1 y)))
        = degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y :=
  ⟨valued_PhiHatK_convF p F ϖ hx hy hx0 hy0,
    degAr_PhiHatK_convF p F ϖ hx hy hx0 hy0⟩

/-- **The degree is additive** (Kedlaya Lemma 2.6, specialized to the single
radius): `deg(xy) = deg x + deg y` on `A^r`. -/
theorem degAr_mul {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    degAr p F ϖ hρ0 hρ1 (x * y)
      = degAr p F ϖ hρ0 hρ1 x + degAr p F ϖ hρ0 hρ1 y := by
  obtain ⟨hΦval, hΦdeg⟩ := valued_degAr_PhiHatK_convF p F ϖ hx hy hx0 hy0
  have hdx := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  have hdc := tendsto_convF p F hdx hdy
  have hvx0 : Valued.v x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0
  have hvy0 : Valued.v y ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hy0
  have hvv : 0 < Valued.v x * Valued.v y :=
    mul_pos (pos_iff_ne_zero.mpr hvx0) (pos_iff_ne_zero.mpr hvy0)
  have hE := valued_mul_sub_PhiHatK_convF_le p F ϖ hx hy
  have hlt : Valued.v (x * y - PhiHatK p F ϖ hρ0 hρ1
      (convF F (teichCoeffAr p F ϖ hρ0 hρ1 x) (teichCoeffAr p F ϖ hρ0 hρ1 y)))
      < Valued.v (x * y) := by
    rw [Valuation.map_mul]
    exact lt_of_le_of_lt hE (mul_lt_of_lt_one_left hvv hρ1)
  rw [degAr_eq_of_valued_sub_lt p F ϖ (mul_mem hx hy)
    (PhiHatK_mem_ArSub p F ϖ hρ0 hρ1 hdc) hlt]
  exact hΦdeg

/-- The division-step coordinate sequence decays: shifted coordinates of `y`
divided by the leading coefficient of `x`. -/
theorem tendsto_div_shift {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {y : hatK p F hρ0 hρ1} (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (m : ℕ) (c : F) :
    Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m) / c)) Filter.atTop (nhds 0) := by
  have hdy := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  have hshift : Filter.Tendsto (fun n => ρ ^ (n + m) * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))) Filter.atTop (nhds 0) :=
    hdy.comp (Filter.tendsto_add_atTop_nat m)
  have hscaled := hshift.mul_const ((ρ ^ m)⁻¹ * (perfectoidValuation p F c)⁻¹)
  rw [zero_mul] at hscaled
  refine hscaled.congr fun n => ?_
  rw [map_div₀]
  have hpow : ρ ^ (n + m) * (ρ ^ m)⁻¹ = ρ ^ n := by
    rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_pos hρ0 m).ne', mul_one]
  calc ρ ^ (n + m) * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))
        * ((ρ ^ m)⁻¹ * (perfectoidValuation p F c)⁻¹)
      = (ρ ^ (n + m) * (ρ ^ m)⁻¹) * (perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m)) * (perfectoidValuation p F c)⁻¹) := by
        ring
    _ = ρ ^ n * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))
          * (perfectoidValuation p F c)⁻¹) := by
        rw [hpow]

/-- **The division quotient** (Kedlaya's `z_l`): the `Φ`-series of the shifted
coordinates of `y` divided by the leading coefficient of `x`. -/
def divStep {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x y : hatK p F hρ0 hρ1) :
    hatK p F hρ0 hρ1 :=
  PhiHatK p F ϖ hρ0 hρ1 (fun n => teichCoeffAr p F ϖ hρ0 hρ1 y
    (n + degAr p F ϖ hρ0 hρ1 x) / teichCoeffAr p F ϖ hρ0 hρ1 x
      (degAr p F ϖ hρ0 hρ1 x))

theorem divStep_mem {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) :
    divStep p F ϖ hρ0 hρ1 x y ∈ ArSub p F ϖ hρ0 hρ1 :=
  PhiHatK_mem_ArSub p F ϖ hρ0 hρ1 (tendsto_div_shift p F ϖ hy _ _)

/-- **Quotient value bound**: `v(z) ≤ v(y)/v(x)` (equality is not needed). -/
theorem valued_divStep_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    Valued.v (divStep p F ϖ hρ0 hρ1 x y) * Valued.v x ≤ Valued.v y := by
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  obtain ⟨hxattain, -⟩ := degAr_spec p F ϖ hx hx0
  have hvx0 : Valued.v x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0
  have hxm0 : perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x m) ≠ 0 := by
    intro h0
    exact hvx0 (hxattain.trans (by rw [← hm, h0, mul_zero]))
  rw [divStep, valued_PhiHatK p F ϖ hρ0 hρ1 (tendsto_div_shift p F ϖ hy _ _),
    mul_comm, NNReal.mul_iSup]
  refine ciSup_le fun n => ?_
  rw [map_div₀, ← hm]
  calc Valued.v x * (ρ ^ n * (perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))
        * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹))
      = ρ ^ m * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m)
        * (ρ ^ n * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))
          * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹)) := by
        rw [← hm] at hxattain
        rw [hxattain]
    _ = ρ ^ (n + m) * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m))
        * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹) := by
        rw [pow_add]
        ring
    _ = ρ ^ (n + m) * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 y (n + m)) := by
        rw [mul_inv_cancel₀ hxm0, mul_one]
    _ ≤ Valued.v y := gaussTerm_teichCoeffAr_le p F ϖ hy (n + m)

/-- One division step never increases the value. -/
theorem valued_sub_divStep_mul_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    Valued.v (y - divStep p F ϖ hρ0 hρ1 x y * x) ≤ Valued.v y := by
  refine le_trans (Valuation.map_sub _ _ _) (max_le le_rfl ?_)
  rw [Valuation.map_mul]
  exact valued_divStep_le p F ϖ hx hy hx0

/-- **The `Φ`-subtraction comparison** (the `H∞` bound of (DC⁺), standalone): the
difference of two `A^r` elements deviates from the `Φ`-series of the pointwise
coordinate difference by at most `ρ·max` of the values. -/
theorem valued_sub_sub_PhiHatK_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) :
    Valued.v ((x - y) - PhiHatK p F ϖ hρ0 hρ1
        (fun k => teichCoeffAr p F ϖ hρ0 hρ1 x k - teichCoeffAr p F ϖ hρ0 hρ1 y k))
      ≤ ρ * max (Valued.v x) (Valued.v y) := by
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
    have hmax' : Filter.Tendsto (fun k => max
        (ρ ^ k * perfectoidValuation p F (a k))
        (ρ ^ k * perfectoidValuation p F (b k))) Filter.atTop (nhds 0) := by
      simpa using hdx.max hdy
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmax'
      (fun k => zero_le) hbound
  set M := max (Valued.v x) (Valued.v y) with hM
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
      ≤ ρ * M := fun N => valued_prefix_sub_sub_le p F ϖ hx hy N
  rcases eq_or_ne M 0 with hM0 | hM0
  · have hvx : Valued.v x = 0 :=
      le_antisymm (le_trans (le_max_left _ _) hM0.le) zero_le
    have hvy : Valued.v y = 0 :=
      le_antisymm (le_trans (le_max_right _ _) hM0.le) zero_le
    have hΦe0 : Valued.v (PhiHatK p F ϖ hρ0 hρ1 e) = 0 := by
      rw [valued_PhiHatK p F ϖ hρ0 hρ1 hde]
      refine le_antisymm (ciSup_le fun k => ?_) zero_le
      refine le_trans (mul_le_mul_of_nonneg_left
        (Valuation.map_sub (perfectoidValuation p F) (a k) (b k)) zero_le) ?_
      refine le_trans (nnreal_mul_max _ _ _).le (max_le ?_ ?_)
      · rw [← hvx]
        exact gaussTerm_teichCoeffAr_le p F ϖ hx k
      · rw [← hvy]
        exact gaussTerm_teichCoeffAr_le p F ϖ hy k
    have hsub0 : Valued.v (x - y) = 0 := by
      refine le_antisymm (le_trans (Valuation.map_sub _ _ _)
        (max_le hvx.le hvy.le)) zero_le
    refine le_trans (le_trans (Valuation.map_sub _ _ _)
      (max_le hsub0.le hΦe0.le)) zero_le
  · have hρM : 0 < ρ * M := mul_pos hρ0 (pos_iff_ne_zero.mpr hM0)
    have hlim : Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1
        (prefixAloc p F ϖ a N - prefixAloc p F ϖ b N - prefixAloc p F ϖ e N))
        Filter.atTop (nhds ((x - y) - PhiHatK p F ϖ hρ0 hρ1 e)) := by
      have h1 := (hSx.sub hSy).sub hSe
      refine h1.congr fun N => ?_
      rw [map_sub, map_sub]
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

/-- **The (2.8.2) coefficient analysis**: past the working index `N`, the pointwise
difference between the coordinates of `y` and the quotient convolution is
`c`-small — the exact cancellation at `j = m` removes `yₙ`, the `j > m` terms are
`ε`-damped by `x`, and the `j < m` terms are `c`-damped by the `N`-property of `y`. -/
theorem gaussTerm_sub_convF_divStep_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) {ε c : NNReal} {N : ℕ}
    (hεx : ∀ j, degAr p F ϖ hρ0 hρ1 x < j
      → ρ ^ j * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x j)
        ≤ ε * Valued.v x)
    (hw1 : ε * Valued.v y ≤ c)
    (hmN : degAr p F ϖ hρ0 hρ1 x ≤ N)
    (hw2 : ∀ n, N < n → ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 y n) ≤ c) :
    ∀ n, N ≤ n → ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 y n
        - convF F (fun k => teichCoeffAr p F ϖ hρ0 hρ1 y
            (k + degAr p F ϖ hρ0 hρ1 x)
          / teichCoeffAr p F ϖ hρ0 hρ1 x (degAr p F ϖ hρ0 hρ1 x))
          (teichCoeffAr p F ϖ hρ0 hρ1 x) n) ≤ c := by
  intro n hn
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  obtain ⟨hxattain, -⟩ := degAr_spec p F ϖ hx hx0
  rw [← hm] at hxattain
  have hvx0 : Valued.v x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0
  have hvxpos : 0 < Valued.v x := pos_iff_ne_zero.mpr hvx0
  have hxm0 : perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m) ≠ 0 := by
    intro h0
    exact hvx0 (hxattain.trans (by rw [h0, mul_zero]))
  have hmn : m ≤ n := le_trans hmN hn
  -- the exact cancellation: the k = n - m term of the convolution is yₙ
  have hsplit : convF F (fun k => teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
      / teichCoeffAr p F ϖ hρ0 hρ1 x m) (teichCoeffAr p F ϖ hρ0 hρ1 x) n
      = teichCoeffAr p F ϖ hρ0 hρ1 y n
        + ∑ k ∈ (Finset.range (n + 1)).erase (n - m),
          (teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
            / teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k) := by
    have hmem : n - m ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by omega)
    rw [convF, ← Finset.add_sum_erase _ _ hmem]
    congr 1
    have hidx1 : n - m + m = n := by omega
    have hidx2 : n - (n - m) = m := by omega
    rw [hidx1, hidx2, div_mul_cancel₀ _ (fun h0 => hxm0 (by rw [h0, map_zero]))]
  rw [hsplit]
  have hcancel : teichCoeffAr p F ϖ hρ0 hρ1 y n
      - (teichCoeffAr p F ϖ hρ0 hρ1 y n
        + ∑ k ∈ (Finset.range (n + 1)).erase (n - m),
          (teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
            / teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k))
      = -(∑ k ∈ (Finset.range (n + 1)).erase (n - m),
          (teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
            / teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k)) := by
    ring
  rw [hcancel, Valuation.map_neg]
  -- bound the erased sum termwise
  rcases Finset.eq_empty_or_nonempty ((Finset.range (n + 1)).erase (n - m))
    with hemp | hne
  · rw [hemp, Finset.sum_empty, Valuation.map_zero, mul_zero]
    exact zero_le
  · have h1 : perfectoidValuation p F
        (∑ k ∈ (Finset.range (n + 1)).erase (n - m),
          (teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
            / teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k))
        ≤ ((Finset.range (n + 1)).erase (n - m)).sup
          (fun k => perfectoidValuation p F
            ((teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
              / teichCoeffAr p F ϖ hρ0 hρ1 x m)
            * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k))) :=
      Valuation.map_sum_le _ fun k hk => Finset.le_sup
        (f := fun k => perfectoidValuation p F
          ((teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
            / teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k))) hk
    refine le_trans (mul_le_mul_of_nonneg_left h1 zero_le) ?_
    obtain ⟨k₀, hk₀mem, hk₀⟩ := Finset.exists_mem_eq_sup _ hne
      (fun k => perfectoidValuation p F
        ((teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
          / teichCoeffAr p F ϖ hρ0 hρ1 x m)
        * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k)))
    rw [hk₀]
    have hk₀ne : k₀ ≠ n - m := Finset.ne_of_mem_erase hk₀mem
    have hk₀n : k₀ ≤ n := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_of_mem_erase hk₀mem))
    -- multiply out the leading denominator: the two-sided bound at scale v(x)
    have hstep : ρ ^ n * perfectoidValuation p F
        ((teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)
          / teichCoeffAr p F ϖ hρ0 hρ1 x m)
        * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)) * Valued.v x
        = (ρ ^ (k₀ + m) * perfectoidValuation p F
            (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)))
          * (ρ ^ (n - k₀) * perfectoidValuation p F
            (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀))) := by
      rw [Valuation.map_mul, map_div₀, hxattain]
      rw [show ρ ^ (k₀ + m) = ρ ^ k₀ * ρ ^ m from by rw [pow_add]]
      rw [show ρ ^ n = ρ ^ k₀ * ρ ^ (n - k₀) from by
        rw [← pow_add, Nat.add_sub_cancel' hk₀n]]
      rw [div_eq_mul_inv]
      have hcancel2 : perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m)
          * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹ = 1 :=
        mul_inv_cancel₀ hxm0
      calc ρ ^ k₀ * ρ ^ (n - k₀) * (perfectoidValuation p F
            (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m))
            * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹
            * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)))
          * (ρ ^ m * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))
          = (ρ ^ k₀ * ρ ^ m * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)))
            * (ρ ^ (n - k₀) * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)))
            * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m)
              * (perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m))⁻¹) := by
            ring
        _ = (ρ ^ k₀ * ρ ^ m * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)))
            * (ρ ^ (n - k₀) * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀))) := by
            rw [hcancel2, mul_one]
    -- the two cases, both at scale c·v(x)
    have hbound : (ρ ^ (k₀ + m) * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)))
        * (ρ ^ (n - k₀) * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)))
        ≤ c * Valued.v x := by
      rcases lt_or_gt_of_ne hk₀ne with hcase | hcase
      · -- k₀ < n - m, so n - k₀ > m: the x-term is ε-damped
        have hj : m < n - k₀ := by omega
        have h1 : (ρ ^ (k₀ + m) * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)))
            * (ρ ^ (n - k₀) * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)))
            ≤ Valued.v y * (ε * Valued.v x) :=
          mul_le_mul (gaussTerm_teichCoeffAr_le p F ϖ hy (k₀ + m))
            (hεx (n - k₀) hj) zero_le zero_le
        have h2 : Valued.v y * (ε * Valued.v x)
            = (ε * Valued.v y) * Valued.v x := by
          ring
        rw [h2] at h1
        exact le_trans h1 (mul_le_mul_of_nonneg_right hw1 zero_le)
      · -- k₀ > n - m, so k₀ + m > n ≥ N: the y-term is c-damped
        have hk : N < k₀ + m := by omega
        exact mul_le_mul (hw2 (k₀ + m) hk)
          (gaussTerm_teichCoeffAr_le p F ϖ hx (n - k₀)) zero_le zero_le
    have hfinal : ρ ^ n * perfectoidValuation p F
        ((teichCoeffAr p F ϖ hρ0 hρ1 y (k₀ + m)
          / teichCoeffAr p F ϖ hρ0 hρ1 x m)
        * teichCoeffAr p F ϖ hρ0 hρ1 x (n - k₀)) * Valued.v x
        ≤ c * Valued.v x := by
      rw [hstep]
      exact hbound
    exact le_of_mul_le_mul_right hfinal hvxpos

/-- **The descent step of Kedlaya Lemma 2.8**: one division step pushes every
coordinate term from index `N` on below the threshold `c` — including index `N`
itself, which drives the strict descent of the top `ε`-index. -/
theorem descent_step {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x y : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (hy : y ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) {ε c : NNReal} {N : ℕ}
    (hρε : ρ ≤ ε)
    (hεx : ∀ j, degAr p F ϖ hρ0 hρ1 x < j
      → ρ ^ j * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x j)
        ≤ ε * Valued.v x)
    (hw1 : ε * Valued.v y ≤ c)
    (hmN : degAr p F ϖ hρ0 hρ1 x ≤ N)
    (hw2 : ∀ n, N < n → ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 y n) ≤ c) :
    ∀ n, N ≤ n → ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1
      (y - divStep p F ϖ hρ0 hρ1 x y * x) n) ≤ c := by
  intro n hn
  set m := degAr p F ϖ hρ0 hρ1 x with hm
  set z := divStep p F ϖ hρ0 hρ1 x y with hz
  set zc : ℕ → F := fun k => teichCoeffAr p F ϖ hρ0 hρ1 y (k + m)
    / teichCoeffAr p F ϖ hρ0 hρ1 x m with hzc
  have hzcdec := tendsto_div_shift p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) hy m
    (teichCoeffAr p F ϖ hρ0 hρ1 x m)
  have hzmem : z ∈ ArSub p F ϖ hρ0 hρ1 := divStep_mem p F ϖ hx hy
  have hzxmem : z * x ∈ ArSub p F ϖ hρ0 hρ1 := mul_mem hzmem hx
  have hyzxmem : y - z * x ∈ ArSub p F ϖ hρ0 hρ1 := sub_mem hy hzxmem
  have hfun : teichCoeffAr p F ϖ hρ0 hρ1 z = zc :=
    funext fun k => teichCoeffAr_PhiHatK p F ϖ hρ0 hρ1 hzcdec k
  have hxdec := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  have hydec := tendsto_gaussTerm_teichCoeffAr p F ϖ hy
  have hcseqdec : Filter.Tendsto (fun k => ρ ^ k * perfectoidValuation p F
      (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x) k)) Filter.atTop (nhds 0) :=
    tendsto_convF p F hzcdec hxdec
  have hΦcmem := PhiHatK_mem_ArSub p F ϖ hρ0 hρ1 hcseqdec
  have hΦccoords : ∀ k, teichCoeffAr p F ϖ hρ0 hρ1
      (PhiHatK p F ϖ hρ0 hρ1 (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x))) k
      = convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x) k :=
    fun k => teichCoeffAr_PhiHatK p F ϖ hρ0 hρ1 hcseqdec k
  -- value ladders
  have hvzvx : Valued.v z * Valued.v x ≤ Valued.v y :=
    valued_divStep_le p F ϖ hx hy hx0
  have hchainc : ρ * (Valued.v z * Valued.v x) ≤ c :=
    le_trans (mul_le_mul_of_nonneg_left hvzvx zero_le)
      (le_trans (mul_le_mul_of_nonneg_right hρε zero_le) hw1)
  have hρvyc : ρ * Valued.v y ≤ c :=
    le_trans (mul_le_mul_of_nonneg_right hρε zero_le) hw1
  -- the E-error
  have hE := valued_mul_sub_PhiHatK_convF_le p F ϖ hzmem hx
  rw [hfun] at hE
  have hEc : Valued.v (z * x - PhiHatK p F ϖ hρ0 hρ1
      (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x))) ≤ c := le_trans hE hchainc
  -- value of Φc
  have hzterms : ∀ k, ρ ^ k * perfectoidValuation p F (zc k) ≤ Valued.v z := by
    intro k
    have h1 := gaussTerm_teichCoeffAr_le p F ϖ hzmem k
    rwa [hfun] at h1
  have hxterms : ∀ k, ρ ^ k * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x k) ≤ Valued.v x :=
    fun k => gaussTerm_teichCoeffAr_le p F ϖ hx k
  have hvΦc : Valued.v (PhiHatK p F ϖ hρ0 hρ1
      (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x))) ≤ Valued.v y := by
    rw [valued_PhiHatK p F ϖ hρ0 hρ1 hcseqdec]
    refine le_trans (ciSup_le fun k =>
      gaussTerm_convF_le p F zc _ hzterms hxterms k) hvzvx
  -- piece 1: (y − Φc) vs Φ of the pointwise difference
  set w : ℕ → F := fun k => teichCoeffAr p F ϖ hρ0 hρ1 y k
    - convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x) k with hw
  have hP1 := valued_sub_sub_PhiHatK_le p F ϖ hy hΦcmem
  have hfun2 : (fun k => teichCoeffAr p F ϖ hρ0 hρ1 y k
      - teichCoeffAr p F ϖ hρ0 hρ1
        (PhiHatK p F ϖ hρ0 hρ1 (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x))) k)
      = w := by
    funext k
    rw [hw, hΦccoords k]
  rw [hfun2] at hP1
  have hP1c : Valued.v ((y - PhiHatK p F ϖ hρ0 hρ1
      (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x)))
      - PhiHatK p F ϖ hρ0 hρ1 w) ≤ c := by
    refine le_trans hP1 (le_trans ?_ hρvyc)
    exact mul_le_mul_of_nonneg_left (max_le le_rfl hvΦc) zero_le
  -- w decays and Φw is admissible
  have hwdec : Filter.Tendsto (fun k => ρ ^ k * perfectoidValuation p F (w k))
      Filter.atTop (nhds 0) := by
    have hbound : ∀ k, ρ ^ k * perfectoidValuation p F (w k)
        ≤ max (ρ ^ k * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y k))
          (ρ ^ k * perfectoidValuation p F
            (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x) k)) := by
      intro k
      refine le_trans (mul_le_mul_of_nonneg_left
        (Valuation.map_sub (perfectoidValuation p F) _ _) zero_le) ?_
      exact (nnreal_mul_max _ _ _).le
    have hmax' : Filter.Tendsto (fun k => max
        (ρ ^ k * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 y k))
        (ρ ^ k * perfectoidValuation p F
          (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x) k)))
        Filter.atTop (nhds 0) := by
      simpa using hydec.max hcseqdec
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmax'
      (fun k => zero_le) hbound
  have hΦwmem := PhiHatK_mem_ArSub p F ϖ hρ0 hρ1 hwdec
  have hΦwcoords : ∀ k, teichCoeffAr p F ϖ hρ0 hρ1
      (PhiHatK p F ϖ hρ0 hρ1 w) k = w k :=
    fun k => teichCoeffAr_PhiHatK p F ϖ hρ0 hρ1 hwdec k
  have hvΦw : Valued.v (PhiHatK p F ϖ hρ0 hρ1 w) ≤ Valued.v y := by
    rw [valued_PhiHatK p F ϖ hρ0 hρ1 hwdec]
    refine ciSup_le fun k => ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Valuation.map_sub (perfectoidValuation p F) _ _) zero_le) ?_
    refine le_trans (nnreal_mul_max _ _ _).le (max_le ?_ ?_)
    · exact gaussTerm_teichCoeffAr_le p F ϖ hy k
    · exact le_trans (gaussTerm_convF_le p F zc _ hzterms hxterms k) hvzvx
  -- v((y − zx) − Φw) ≤ c
  have hkey : Valued.v ((y - z * x) - PhiHatK p F ϖ hρ0 hρ1 w) ≤ c := by
    have hsplit : (y - z * x) - PhiHatK p F ϖ hρ0 hρ1 w
        = ((y - PhiHatK p F ϖ hρ0 hρ1
            (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x)))
          - PhiHatK p F ϖ hρ0 hρ1 w)
          + (PhiHatK p F ϖ hρ0 hρ1 (convF F zc (teichCoeffAr p F ϖ hρ0 hρ1 x))
            - z * x) := by
      ring
    rw [hsplit]
    refine le_trans (Valuation.map_add _ _ _) (max_le hP1c ?_)
    rw [Valuation.map_sub_swap]
    exact hEc
  -- DC⁺ transfer to the coordinates of y − zx
  have hDC := digit_sub_le p F ϖ hyzxmem hΦwmem n
  have hDCc : ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 (y - z * x) n
        - teichCoeffAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1 w) n) ≤ c := by
    refine le_trans hDC (max_le hkey ?_)
    refine le_trans ?_ hρvyc
    refine mul_le_mul_of_nonneg_left (max_le ?_ hvΦw) zero_le
    exact valued_sub_divStep_mul_le p F ϖ hx hy hx0
  -- R3 bounds the Φw coordinate itself
  have hR3 := gaussTerm_sub_convF_divStep_le p F ϖ hx hy hx0
    (ε := ε) (c := c) (N := N) hεx hw1 hmN hw2 n hn
  -- assemble
  have hsplit2 : teichCoeffAr p F ϖ hρ0 hρ1 (y - z * x) n
      = (teichCoeffAr p F ϖ hρ0 hρ1 (y - z * x) n
          - teichCoeffAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1 w) n)
        + w n := by
    rw [hΦwcoords n]
    ring
  rw [hsplit2]
  refine le_trans (mul_le_mul_of_nonneg_left
    (Valuation.map_add (perfectoidValuation p F) _ _) zero_le) ?_
  refine le_trans (nnreal_mul_max _ _ _).le (max_le hDCc ?_)
  exact hR3

/-- **The division iteration** (the well-founded loop of Kedlaya Lemma 2.8): under
the `ε`-property of `x`, any `y` whose coordinate terms are below `ε·V` past `K`
admits a quotient `z` with remainder value at most `V` and, unless the remainder is
already `ε·V`-small, remainder degree below `deg x`. Strong induction on `K`: each
descent step shrinks the window by one. -/
theorem division_descent {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0)
    {ε V : NNReal} (hρε : ρ ≤ ε) (hε1 : ε < 1)
    (hεx : ∀ j, degAr p F ϖ hρ0 hρ1 x < j
      → ρ ^ j * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x j)
        ≤ ε * Valued.v x) :
    ∀ K : ℕ, ∀ y : hatK p F hρ0 hρ1, y ∈ ArSub p F ϖ hρ0 hρ1
      → Valued.v y ≤ V
      → (∀ n, K < n → ρ ^ n * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 y n) ≤ ε * V)
      → ∃ z : hatK p F hρ0 hρ1, z ∈ ArSub p F ϖ hρ0 hρ1
        ∧ Valued.v (y - z * x) ≤ V
        ∧ (ε * V < Valued.v (y - z * x)
          → degAr p F ϖ hρ0 hρ1 (y - z * x) < degAr p F ϖ hρ0 hρ1 x) := by
  intro K
  induction K using Nat.strong_induction_on with
  | _ K IH =>
    intro y hy hvy hK
    rcases lt_or_ge K (degAr p F ϖ hρ0 hρ1 x) with hKm | hKm
    · -- base: the window is already inside the degree of x
      refine ⟨0, zero_mem _, ?_, ?_⟩
      · rw [zero_mul, sub_zero]
        exact hvy
      · rw [zero_mul, sub_zero]
        intro hbig
        have hy0 : y ≠ 0 := by
          intro h0
          rw [h0, Valuation.map_zero] at hbig
          exact absurd hbig (not_lt_of_ge zero_le)
        have hub : ∀ n ∈ {n | Valued.v y = ρ ^ n * perfectoidValuation p F
            (teichCoeffAr p F ϖ hρ0 hρ1 y n)}, n ≤ K := by
          intro n hn
          by_contra hcon
          push Not at hcon
          have h1 := hK n hcon
          rw [← hn] at h1
          exact absurd (lt_of_lt_of_le hbig h1) (lt_irrefl _)
        obtain ⟨n₀, hn₀, -⟩ := exists_valued_eq_teichCoeffAr p F ϖ hy hy0
        exact lt_of_le_of_lt (csSup_le ⟨n₀, hn₀⟩ hub) hKm
    · -- step: apply the descent and recurse on K - 1
      rcases le_or_gt (Valued.v y) (ε * V) with hsmall | hbig
      · refine ⟨0, zero_mem _, ?_, ?_⟩
        · rw [zero_mul, sub_zero]
          exact hvy
        · rw [zero_mul, sub_zero]
          intro hbig2
          exact absurd (lt_of_le_of_lt hsmall hbig2) (lt_irrefl _)
      · have hstep := descent_step p F ϖ hx hy hx0 (ε := ε) (c := ε * V)
          (N := K) hρε hεx
          (mul_le_mul_of_nonneg_left hvy zero_le) hKm hK
        set y' := y - divStep p F ϖ hρ0 hρ1 x y * x with hy'
        have hy'mem : y' ∈ ArSub p F ϖ hρ0 hρ1 :=
          sub_mem hy (mul_mem (divStep_mem p F ϖ hx hy) hx)
        have hvy' : Valued.v y' ≤ V :=
          le_trans (valued_sub_divStep_mul_le p F ϖ hx hy hx0) hvy
        rcases Nat.eq_zero_or_pos K with hK0 | hKpos
        · -- K = 0: every coordinate of y' is ε·V-small, so v(y') ≤ ε·V
          refine ⟨divStep p F ϖ hρ0 hρ1 x y, divStep_mem p F ϖ hx hy, hvy', ?_⟩
          intro hbig2
          exfalso
          have hval : Valued.v y' ≤ ε * V := by
            rw [valued_eq_iSup_teichCoeffAr p F ϖ hy'mem]
            refine ciSup_le fun n => ?_
            refine hstep n ?_
            omega
          exact absurd (lt_of_le_of_lt hval hbig2) (lt_irrefl _)
        · have hK' : ∀ n, K - 1 < n → ρ ^ n * perfectoidValuation p F
              (teichCoeffAr p F ϖ hρ0 hρ1 y' n) ≤ ε * V := by
            intro n hn
            exact hstep n (by omega)
          obtain ⟨z', hz'mem, hz'val, hz'deg⟩ :=
            IH (K - 1) (by omega) y' hy'mem hvy' hK'
          refine ⟨divStep p F ϖ hρ0 hρ1 x y + z',
            add_mem (divStep_mem p F ϖ hx hy) hz'mem, ?_, ?_⟩
          · have halg : y - (divStep p F ϖ hρ0 hρ1 x y + z') * x = y' - z' * x := by
              rw [hy']
              ring
            rw [halg]
            exact hz'val
          · have halg : y - (divStep p F ϖ hρ0 hρ1 x y + z') * x = y' - z' * x := by
              rw [hy']
              ring
            rw [halg]
            exact hz'deg

/-- **Kedlaya Lemma 2.8 (approximate division)**: for nonzero `x` there is
`ε ∈ [ρ, 1)` such that every `y` admits a quotient `z` with remainder of value at
most `v(y)`, and of degree below `deg x` unless the remainder is already
`ε·v(y)`-small. -/
theorem approx_division {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    ∃ ε : NNReal, ρ ≤ ε ∧ ε < 1
      ∧ ∀ y : hatK p F hρ0 hρ1, y ∈ ArSub p F ϖ hρ0 hρ1
        → ∃ z : hatK p F hρ0 hρ1, z ∈ ArSub p F ϖ hρ0 hρ1
          ∧ Valued.v (y - z * x) ≤ Valued.v y
          ∧ (ε * Valued.v y < Valued.v (y - z * x)
            → degAr p F ϖ hρ0 hρ1 (y - z * x) < degAr p F ϖ hρ0 hρ1 x) := by
  obtain ⟨ε, hρε, hε1, hεx⟩ := exists_eps_terms_le p F ϖ hx hx0
  refine ⟨ε, hρε, hε1, fun y hy => ?_⟩
  rcases eq_or_ne (Valued.v y) 0 with hvy0 | hvy0
  · refine ⟨0, zero_mem _, ?_, ?_⟩
    · rw [zero_mul, sub_zero]
    · rw [zero_mul, sub_zero]
      intro hbig
      rw [hvy0, mul_zero] at hbig
      exact absurd hbig (lt_irrefl 0)
  · have hεvy : 0 < ε * Valued.v y :=
      mul_pos (lt_of_lt_of_le hρ0 hρε) (pos_iff_ne_zero.mpr hvy0)
    obtain ⟨K, hKw⟩ := Filter.eventually_atTop.mp
      ((tendsto_gaussTerm_teichCoeffAr p F ϖ hy).eventually_lt_const hεvy)
    exact division_descent p F ϖ hx hx0 hρε hε1 hεx K y hy le_rfl
      (fun n hn => (hKw n (by omega)).le)

/-- Vanishing value bounds force convergence (Cauchy + limit identification). -/
theorem tendsto_of_valued_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {g : ℕ → hatK p F hρ0 hρ1} {y : hatK p F hρ0 hρ1}
    {f : ℕ → NNReal} (hle : ∀ i, Valued.v (g i - y) ≤ f i)
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    Filter.Tendsto g Filter.atTop (nhds y) := by
  have hcauchy : CauchySeq g := by
    refine cauchySeq_of_valued_le p F (hρ0 := hρ0) (hρ1 := hρ1) g fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hf.eventually_lt_const hε)
    refine ⟨N₀, fun m n hm hn => ?_⟩
    have h1 : g m - g n = (g m - y) - (g n - y) := by ring
    rw [h1]
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · exact le_trans (hle m) (hN₀ m hm).le
    · exact le_trans (hle n) (hN₀ n hn).le
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLy : L = y := by
    have hzero : Valued.v (L - y) = 0 := by
      by_contra hne
      have hpos : 0 < Valued.v (L - y) := pos_iff_ne_zero.mpr hne
      have hhalfpos : 0 < Valued.v (L - y) / 2 := div_pos hpos two_pos
      obtain ⟨i, hi1, hi2⟩ := ((eventually_valued_sub_le_of_tendsto p F
        (hρ0 := hρ0) (hρ1 := hρ1) hL hhalfpos).and
        (Filter.eventually_atTop.mpr
          (Filter.eventually_atTop.mp (hf.eventually_lt_const hhalfpos)))).exists
      have hsplit : L - y = (L - g i) + (g i - y) := by ring
      have h2 : Valued.v (L - y) ≤ Valued.v (L - y) / 2 := by
        conv_lhs => rw [hsplit]
        refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
        · rw [Valuation.map_sub_swap]
          exact hi1
        · exact le_trans (hle i) hi2.le
      exact absurd (lt_of_le_of_lt h2 (NNReal.half_lt_self hne)) (lt_irrefl _)
    exact sub_eq_zero.mp ((Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp hzero)
  rwa [hLy] at hL

/-- **Kedlaya Proposition 2.9 (exact division)**: division on `A^r` by a nonzero
element leaves a remainder that vanishes or has degree strictly below the divisor.
The quotient sequence from Lemma 2.8 either drops the degree in finitely many
steps or shrinks geometrically, and `A^r` is closed. -/
theorem exact_division {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0)
    {y : hatK p F hρ0 hρ1} (hy : y ∈ ArSub p F ϖ hρ0 hρ1) :
    ∃ z : hatK p F hρ0 hρ1, z ∈ ArSub p F ϖ hρ0 hρ1
      ∧ Valued.v (y - z * x) ≤ Valued.v y
      ∧ (y - z * x = 0
        ∨ degAr p F ϖ hρ0 hρ1 (y - z * x) < degAr p F ϖ hρ0 hρ1 x) := by
  obtain ⟨ε, hρε, hε1, hdiv⟩ := approx_division p F ϖ hx hx0
  set step : {u : hatK p F hρ0 hρ1 // u ∈ ArSub p F ϖ hρ0 hρ1}
      → {u : hatK p F hρ0 hρ1 // u ∈ ArSub p F ϖ hρ0 hρ1} := fun u =>
    if degAr p F ϖ hρ0 hρ1 u.1 < degAr p F ϖ hρ0 hρ1 x then u
    else ⟨u.1 - (hdiv u.1 u.2).choose * x,
      sub_mem u.2 (mul_mem (hdiv u.1 u.2).choose_spec.1 hx)⟩ with hstep
  set seq : ℕ → {u : hatK p F hρ0 hρ1 // u ∈ ArSub p F ϖ hρ0 hρ1} :=
    fun l => step^[l] ⟨y, hy⟩ with hseq
  have hsucc : ∀ l, seq (l + 1) = step (seq l) :=
    fun l => Function.iterate_succ_apply' step l ⟨y, hy⟩
  have hval : ∀ l, Valued.v (seq l).1 ≤ Valued.v y := by
    intro l
    induction l with
    | zero => exact le_rfl
    | succ n ih =>
      rw [hsucc n]
      simp only [hstep]
      by_cases h : degAr p F ϖ hρ0 hρ1 (seq n).1 < degAr p F ϖ hρ0 hρ1 x
      · rw [if_pos h]
        exact ih
      · rw [if_neg h]
        exact le_trans (hdiv (seq n).1 (seq n).2).choose_spec.2.1 ih
  have hZmem : ∀ l, (y - (seq l).1) / x ∈ ArSub p F ϖ hρ0 hρ1 := by
    intro l
    induction l with
    | zero =>
      have h0 : (y - (seq 0).1) / x = 0 := by
        rw [show (seq 0).1 = y from rfl, sub_self, zero_div]
      rw [h0]
      exact zero_mem _
    | succ n ih =>
      rw [hsucc n]
      simp only [hstep]
      by_cases h : degAr p F ϖ hρ0 hρ1 (seq n).1 < degAr p F ϖ hρ0 hρ1 x
      · rw [if_pos h]
        exact ih
      · rw [if_neg h]
        have halg : (y - ((seq n).1 - (hdiv (seq n).1 (seq n).2).choose * x)) / x
            = (y - (seq n).1) / x + (hdiv (seq n).1 (seq n).2).choose := by
          field_simp
          ring
        rw [halg]
        exact add_mem ih (hdiv (seq n).1 (seq n).2).choose_spec.1
  by_cases hdrop : ∃ l, degAr p F ϖ hρ0 hρ1 (seq l).1 < degAr p F ϖ hρ0 hρ1 x
  · obtain ⟨l, hl⟩ := hdrop
    have hid : y - (y - (seq l).1) / x * x = (seq l).1 := by
      rw [div_mul_cancel₀ _ hx0]
      ring
    refine ⟨(y - (seq l).1) / x, hZmem l, ?_, Or.inr ?_⟩
    · rw [hid]
      exact hval l
    · rw [hid]
      exact hl
  · push Not at hdrop
    have hgeo : ∀ l, Valued.v (seq l).1 ≤ ε ^ l * Valued.v y := by
      intro l
      induction l with
      | zero =>
        rw [pow_zero, one_mul]
        exact hval 0
      | succ n ih =>
        have hnodrop : ¬ degAr p F ϖ hρ0 hρ1
            ((seq n).1 - (hdiv (seq n).1 (seq n).2).choose * x)
            < degAr p F ϖ hρ0 hρ1 x := by
          have h2 := hdrop (n + 1)
          rw [hsucc n] at h2
          simp only [hstep] at h2
          rw [if_neg (not_lt.mpr (hdrop n))] at h2
          exact not_lt.mpr h2
        have hle2 : Valued.v ((seq n).1 - (hdiv (seq n).1 (seq n).2).choose * x)
            ≤ ε * Valued.v (seq n).1 := by
          by_contra hcon
          push Not at hcon
          exact hnodrop ((hdiv (seq n).1 (seq n).2).choose_spec.2.2 hcon)
        rw [hsucc n]
        simp only [hstep]
        rw [if_neg (not_lt.mpr (hdrop n))]
        calc Valued.v ((seq n).1 - (hdiv (seq n).1 (seq n).2).choose * x)
            ≤ ε * Valued.v (seq n).1 := hle2
          _ ≤ ε * (ε ^ n * Valued.v y) := mul_le_mul_of_nonneg_left ih zero_le
          _ = ε ^ (n + 1) * Valued.v y := by ring
    set Z : ℕ → hatK p F hρ0 hρ1 := fun l => (y - (seq l).1) / x with hZdef
    have hZx : ∀ l, Valued.v (Z l * x - y) ≤ ε ^ l * Valued.v y := by
      intro l
      have h1 : Z l * x - y = -((seq l).1) := by
        rw [hZdef, div_mul_cancel₀ _ hx0]
        ring
      rw [h1, Valuation.map_neg]
      exact hgeo l
    have hεgeo : Filter.Tendsto (fun l => ε ^ l * Valued.v y)
        Filter.atTop (nhds 0) := by
      have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (zero_le : (0 : NNReal) ≤ ε) hε1).mul_const (Valued.v y)
      rwa [zero_mul] at h1
    have hZxlim : Filter.Tendsto (fun l => Z l * x) Filter.atTop (nhds y) :=
      tendsto_of_valued_sub_le p F (hρ0 := hρ0) (hρ1 := hρ1) hZx hεgeo
    have hZlim : Filter.Tendsto Z Filter.atTop (nhds (y / x)) := by
      have h1 := hZxlim.mul_const x⁻¹
      have h2 : ∀ l, Z l * x * x⁻¹ = Z l := fun l => by
        rw [mul_assoc, mul_inv_cancel₀ hx0, mul_one]
      rw [show y / x = y * x⁻¹ from div_eq_mul_inv y x]
      exact h1.congr h2
    have hclosed : IsClosed (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1)) := by
      have hcarrier : (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1))
          = closure ((AlocToHatK p F ϖ hρ0 hρ1).range :
            Set (hatK p F hρ0 hρ1)) := rfl
      rw [hcarrier]
      exact isClosed_closure
    have hyxmem : y / x ∈ ArSub p F ϖ hρ0 hρ1 :=
      hclosed.mem_of_tendsto hZlim (Filter.Eventually.of_forall fun l => hZmem l)
    refine ⟨y / x, hyxmem, ?_, Or.inl ?_⟩
    · rw [div_mul_cancel₀ _ hx0, sub_self, Valuation.map_zero]
      exact zero_le
    · rw [div_mul_cancel₀ _ hx0, sub_self]

/-- **Kedlaya Corollary 2.10**: `A^r` is a principal ideal ring — every ideal is
generated by an element of minimal degree, by exact division. -/
theorem isPrincipalIdealRing_ArSub {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsPrincipalIdealRing ↥(ArSub p F ϖ hρ0 hρ1) := by
  refine ⟨fun I => ?_⟩
  rcases eq_or_ne I ⊥ with rfl | hI
  · exact ⟨⟨0, (Ideal.span_zero).symm⟩⟩
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    set S : Set ℕ := {d | ∃ b : ↥(ArSub p F ϖ hρ0 hρ1), b ∈ I ∧ b ≠ 0
      ∧ degAr p F ϖ hρ0 hρ1 (b : hatK p F hρ0 hρ1) = d} with hS
    have hSne : S.Nonempty := ⟨degAr p F ϖ hρ0 hρ1 (a : hatK p F hρ0 hρ1),
      a, haI, ha0, rfl⟩
    obtain ⟨x₀, hx₀I, hx₀0, hx₀deg⟩ := Nat.sInf_mem hSne
    have hx₀ne : (x₀ : hatK p F hρ0 hρ1) ≠ 0 :=
      fun h => hx₀0 (Subtype.ext h)
    refine ⟨⟨x₀, le_antisymm ?_ ?_⟩⟩
    · intro y hyI
      obtain ⟨z, hzmem, -, hdichot⟩ := exact_division p F ϖ x₀.2 hx₀ne y.2
      set zz : ↥(ArSub p F ϖ hρ0 hρ1) := ⟨z, hzmem⟩ with hzz
      set ww : ↥(ArSub p F ϖ hρ0 hρ1) := y - zz * x₀ with hww
      have hwwcoe : (ww : hatK p F hρ0 hρ1)
          = (y : hatK p F hρ0 hρ1) - z * (x₀ : hatK p F hρ0 hρ1) := rfl
      have hwwI : ww ∈ I := by
        rw [hww]
        exact I.sub_mem hyI (I.mul_mem_left zz hx₀I)
      rcases hdichot with hzero | hdeg
      · have hyx : y = zz * x₀ :=
          sub_eq_zero.mp (Subtype.ext (hwwcoe.trans hzero))
        rw [Ideal.mem_span_singleton]
        exact ⟨zz, by rw [hyx]; ring⟩
      · rcases eq_or_ne ww 0 with hww0 | hww0
        · have hyx : y = zz * x₀ := sub_eq_zero.mp hww0
          rw [Ideal.mem_span_singleton]
          exact ⟨zz, by rw [hyx]; ring⟩
        · exfalso
          have hwS : degAr p F ϖ hρ0 hρ1 (ww : hatK p F hρ0 hρ1) ∈ S :=
            ⟨ww, hwwI, hww0, rfl⟩
          have hmin := Nat.sInf_le hwS
          have hdeg' : degAr p F ϖ hρ0 hρ1 (ww : hatK p F hρ0 hρ1) < sInf S := by
            rw [hwwcoe, ← hx₀deg]
            exact hdeg
          exact absurd (lt_of_le_of_lt hmin hdeg') (lt_irrefl _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hx₀I

end FarguesFontaine

end
