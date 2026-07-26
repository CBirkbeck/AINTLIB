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
        exact gaussTerm_teichCoeffAr_le' p F ϖ hy n
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
          ≤ Valued.v x := gaussTerm_teichCoeffAr_le' p F ϖ hx n
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
    fun n => gaussTerm_teichCoeffAr_le' p F ϖ hx n
  have hB : ∀ n, ρ ^ n * perfectoidValuation p F (b n) ≤ Valued.v y :=
    fun n => gaussTerm_teichCoeffAr_le' p F ϖ hy n
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

end FarguesFontaine

end
