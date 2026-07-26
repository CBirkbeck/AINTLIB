/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.StronglyNoetherianB
import «Adic spaces».WedhornCechAcyclicity

/-!
# `B^I` is sheafy (Wedhorn Theorem 8.28(b) for Kedlaya's interval rings)

The payoff of Kedlaya §2–§4 for the Fargues–Fontaine campaign: `(B^I, B^{I,+})` is a
complete strongly noetherian Tate affinoid ring, so its structure presheaf is a sheaf
by Wedhorn Theorem 8.28(b) (`isSheafy_of_stronglyNoetherian_828b`).

This file supplies the affinoid-ring instances: `B^{I,+}` (the unit ball `BIPlusIn`)
is bounded, integrally closed (via power-boundedness and the power-multiplicativity
of `wI`), and power-bounded; `B^I` is complete for the right uniformity. The strongly
noetherian input is `isStronglyNoetherian_BISub` (Kedlaya Theorem 4.10, AD-9 form).

## Main results

* `FarguesFontaine.isBounded_BIPlusIn`, `FarguesFontaine.wI_le_one_of_isPowerBounded`,
  `FarguesFontaine.BIPlusIn_isIntegrallyClosed` : the unit ball is a ring of integral
  elements (`isRingOfIntegralElements_BIPlusIn`).
* `FarguesFontaine.isSheafy_BISub` : **`Spa(B^I, B^{I,+})` has a sheafy structure
  presheaf** for the AD-9 intervals.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Theorem "strongly noetherian Robba2"; [T. Wedhorn, *Adic Spaces*][wedhorn2019adic],
  Theorem 8.28(b).
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- The ambient `wI`-ball is a neighborhood of `0` in `B^I` (subtype form). -/
theorem wI_ball_mem_nhds_BISub {ε : NNReal} (hε : 0 < ε) :
    (Subtype.val ⁻¹' {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε})
      ∈ nhds (0 : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  have hball : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε} ∈ nhds
        (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    have h := wI_ball_mem_nhds p F
      (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) hε
    simpa using h
  exact continuous_subtype_val.continuousAt.preimage_mem_nhds hball

/-- **`B^{I,+}` is a bounded subring of `B^I`.** -/
theorem isBounded_BIPlusIn :
    TopologicalRing.IsBounded
      ((BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :
        Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
          Set ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  intro U hU
  obtain ⟨U', hU', hU'sub⟩ := (mem_nhds_subtype _ _ _).mp hU
  obtain ⟨ε, hε, hball⟩ := exists_wI_ball_subset p F hU'
  refine ⟨Subtype.val ⁻¹' {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε}, wI_ball_mem_nhds_BISub p F ϖ hε, ?_⟩
  rintro w ⟨s, hs, v, hv, rfl⟩
  refine hU'sub ?_
  show ((s * v : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ∈ U'
  refine hball ?_
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
    ((s : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      * (v : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) ≤ ε
  calc wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
          ((s : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            * (v : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
        ≤ wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (s : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          * wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (v : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := wI_mul_le p F _ _
    _ ≤ 1 * ε := by
        refine mul_le_mul ?_ hv zero_le zero_le
        exact (mem_BIPlusIn_iff p F ϖ).mp hs
    _ = ε := one_mul ε

/-- **Power-bounded elements of `B^I` lie in the unit ball** (Wedhorn Prop 5.30-style,
via the power-multiplicativity of `wI` and the Tate element `p`). -/
theorem wI_le_one_of_isPowerBounded {a : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)}
    (h : TopologicalRing.IsPowerBounded a) :
    wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨V, hV, hVsub⟩ := h _ (wI_ball_mem_nhds_BISub p F ϖ one_pos)
  obtain ⟨V', hV', hV'sub⟩ := (mem_nhds_subtype _ _ _).mp hV
  obtain ⟨δ, hδ, hδball⟩ := exists_wI_ball_subset p F hV'
  -- a power of the Tate element lands in `V`
  have hr1 : max ρ₁ ρ₂ < 1 := max_lt hρ₁1 hρ₂1
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    hr1).eventually_lt_const hδ).exists
  have hqm : (pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m ∈ V := by
    refine hV'sub ?_
    show ((pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ∈ V'
    refine hδball ?_
    show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 _ ≤ δ
    have hcoe : ((pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        = (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m := rfl
    rw [hcoe, wI_pow p F, pImage, wI_p_image]
    exact hm.le
  -- the coordinate where the value exceeds 1
  rcases lt_max_iff.mp hlt with hbig | hbig
  · -- first coordinate
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
      ((ρ₁ ^ m)⁻¹ : NNReal) hbig
    have hmem := hVsub ⟨a ^ n, ⟨n, rfl⟩, _, hqm, rfl⟩
    have hval : Valued.v (((a ^ n * pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1)
        = Valued.v ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ n
          * ρ₁ ^ m := by
      show Valued.v (((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ^ n
        * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m).1) = _
      rw [show (((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ^ n
          * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m).1)
        = ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ n
          * ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1) ^ m from rfl,
        Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
      congr 1
      rw [show (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).1
        = BlocToHatK p F ϖ hρ₁0 hρ₁1
          (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)) from rfl,
        valued_BlocToHatK, wLoc_algebraMap, gaussValue_p p F hρ₁1.le]
    have hle := hmem
    have hle2 : Valued.v (((a ^ n * pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ≤ 1 :=
      le_trans (le_max_left _ _) hle
    rw [hval] at hle2
    have hρm : (0 : NNReal) < ρ₁ ^ m := pow_pos hρ₁0 m
    have hgt : (1 : NNReal) < Valued.v
        ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ n * ρ₁ ^ m := by
      calc (1 : NNReal) = (ρ₁ ^ m)⁻¹ * ρ₁ ^ m :=
            (inv_mul_cancel₀ (ne_of_gt hρm)).symm
        _ < Valued.v ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).1) ^ n
            * ρ₁ ^ m := by
            exact mul_lt_mul_of_pos_right hn hρm
    exact absurd hle2 (not_le.mpr hgt)
  · -- second coordinate
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
      ((ρ₂ ^ m)⁻¹ : NNReal) hbig
    have hmem := hVsub ⟨a ^ n, ⟨n, rfl⟩, _, hqm, rfl⟩
    have hval : Valued.v (((a ^ n * pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2)
        = Valued.v ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ n
          * ρ₂ ^ m := by
      show Valued.v (((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ^ n
        * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m).2) = _
      rw [show (((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ^ n
          * (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) ^ m).2)
        = ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ n
          * ((pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2) ^ m from rfl,
        Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
      congr 1
      rw [show (pImage p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).2
        = BlocToHatK p F ϖ hρ₂0 hρ₂1
          (algebraMap (Ainf p F) (Bloc p F ϖ) (p : Ainf p F)) from rfl,
        valued_BlocToHatK, wLoc_algebraMap, gaussValue_p p F hρ₂1.le]
    have hle := hmem
    have hle2 : Valued.v (((a ^ n * pEltB p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ^ m
        : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ≤ 1 :=
      le_trans (le_max_right _ _) hle
    rw [hval] at hle2
    have hρm : (0 : NNReal) < ρ₂ ^ m := pow_pos hρ₂0 m
    have hgt : (1 : NNReal) < Valued.v
        ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ n * ρ₂ ^ m := by
      calc (1 : NNReal) = (ρ₂ ^ m)⁻¹ * ρ₂ ^ m :=
            (inv_mul_cancel₀ (ne_of_gt hρm)).symm
        _ < Valued.v ((a : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)).2) ^ n
            * ρ₂ ^ m := by
            exact mul_lt_mul_of_pos_right hn hρm
    exact absurd hle2 (not_le.mpr hgt)

/-- `B^{I,+}` consists of power-bounded elements. -/
theorem BIPlusIn_subset_powerBounded :
    ((BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :
      Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
        Set ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      ⊆ TopologicalRing.powerBoundedSubring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  intro z hz
  refine (isBounded_BIPlusIn p F ϖ).subset ?_
  rintro - ⟨k, rfl⟩
  exact pow_mem hz k

noncomputable local instance instAlgebraBIPlusIn :
    Algebra ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).subtype.toAlgebra

/-- `B^{I,+}` is integrally closed in `B^I` (via power-boundedness). -/
theorem BIPlusIn_isIntegrallyClosed (a : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (ha : IsIntegral ↥(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) a) :
    a ∈ BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  (mem_BIPlusIn_iff p F ϖ).mpr (wI_le_one_of_isPowerBounded p F ϖ
    ((isBounded_BIPlusIn p F ϖ).isPowerBounded_of_isIntegral ha))

/-- **`(B^I, B^{I,+})` is an affinoid ring** (Wedhorn Definition 7.14): the unit ball
is open, integrally closed, and power-bounded. -/
theorem isRingOfIntegralElements_BIPlusIn :
    IsRingOfIntegralElements (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  isOpen := isOpen_BIPlusIn p F ϖ
  isIntegrallyClosed := BIPlusIn_isIntegrallyClosed p F ϖ
  subset_powerBounded := BIPlusIn_subset_powerBounded p F ϖ

/-- The interval ring is a uniform additive group (subtype of the product of
completed fields). -/
theorem isUniformAddGroup_BISub :
    IsUniformAddGroup ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  IsUniformAddGroup.comap
    ((BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).subtype.toAddMonoidHom)

/-- `B^I` is complete for the right uniformity of its additive group. -/
theorem completeSpace_right_BISub :
    @CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (IsTopologicalAddGroup.rightUniformSpace
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  haveI := isUniformAddGroup_BISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact (isComplete_BISub p F ϖ).completeSpace_coe

/-- **`B^I` is sheafy** (Kedlaya's interval rings satisfy Wedhorn Theorem 8.28(b)):
for the AD-9 intervals, the structure presheaf of `Spa(B^I, B^{I,+})` is a sheaf. -/
theorem isSheafy_BISub (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁) :
    letI : ValuationSpectrum.PlusSubring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
      ⟨BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1⟩
    letI : @CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        (IsTopologicalAddGroup.rightUniformSpace
          ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
      completeSpace_right_BISub p F ϖ
    letI : IsRingOfIntegralElements
        (ValuationSpectrum.ringPlus ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
          : Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
      isRingOfIntegralElements_BIPlusIn p F ϖ
    ValuationSpectrum.IsSheafy ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  letI : ValuationSpectrum.PlusSubring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    ⟨BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1⟩
  letI : @CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      (IsTopologicalAddGroup.rightUniformSpace
        ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
    completeSpace_right_BISub p F ϖ
  letI : IsRingOfIntegralElements
      (ValuationSpectrum.ringPlus ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        : Subring ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :=
    isRingOfIntegralElements_BIPlusIn p F ϖ
  letI : IsStronglyNoetherian ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    isStronglyNoetherian_BISub p F ϖ h12 j n hbmem hb hexact
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

end FarguesFontaine

end
