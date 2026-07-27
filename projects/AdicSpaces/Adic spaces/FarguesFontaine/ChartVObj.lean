/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.ChartComparison
import «Adic spaces».StructureSheafStalks
import «Adic spaces».FarguesFontaine.IntervalSplitting

/-!
# The Fargues–Fontaine charts as objects of `𝒱` (D-ii-3 instantiation)

`chartVObj`: `Spa` of a Big-window chart of `𝒴` as an object of Wedhorn's
category `𝒱` — the generic stalk package (`spaVObj`, Wedhorn 8.14/8.20)
instantiated at the chart pair through the ID2 comparison: Tate via
`isTateRing_congr`, plus structure the transported `B^I`-unit ball,
sheafiness `isSheafy_presheafChart`.

The plus-reconciliation (canonical `completedPlusSubring` = transported
`BIPlusIn`) is the recorded follow-up; until it lands the chart `VObj`
carries the transported plus.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂}
  {hρ₂1 : ρ₂ < 1}

/-- The transported plus subring of a chart value (the `B^I`-unit ball through
the ID2 comparison). -/
noncomputable def chartPlus (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    ValuationSpectrum.PlusSubring (presheafValue (chartData p F ϖ 1 b a b)) :=
  ⟨(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map
    ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2).symm.toRingHom)⟩

/-- The chart value is Tate (named form of the ID2e transport). -/
noncomputable def chartTate (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    IsTateRing (presheafValue (chartData p F ϖ 1 b a b)) :=
  isTateRing_congr (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2).symm
    (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
    (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)

/-- **The chart `VObj`**: `Spa` of a Big-window chart of the Fargues–Fontaine
`𝒴`, as an object of Wedhorn's category `𝒱` — the structure sheaf of
topological rings with local stalks and stalk valuations, at the transported
(`B^I`-unit-ball) plus structure. -/
noncomputable def chartVObj (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    VObj :=
  letI := chartPlus p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  haveI hT := chartTate p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  haveI : IsHuberRing (presheafValue (chartData p F ϖ 1 b a b)) :=
    hT.toIsHuberRing
  letI : @CompleteSpace (presheafValue (chartData p F ϖ 1 b a b))
      (IsTopologicalAddGroup.rightUniformSpace
        (presheafValue (chartData p F ϖ 1 b a b))) :=
    completeSpace_right_presheafValue (chartData p F ϖ 1 b a b)
  haveI : IsRingOfIntegralElements
      (ValuationSpectrum.ringPlus (presheafValue (chartData p F ϖ 1 b a b))
        : Subring (presheafValue (chartData p F ϖ 1 b a b))) :=
    (isRingOfIntegralElements_BIPlusIn p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)).map
      (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
      (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2)
      (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2)
  haveI : ValuationSpectrum.IsSheafy
      (presheafValue (chartData p F ϖ 1 b a b)) :=
    isSheafy_presheafChart p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  spaVObj_of_isSheafy (presheafValue (chartData p F ϖ 1 b a b))


/-! ### The plus reconciliation, easy half: canonical ⊆ ball -/

/-- The forward comparison map is open (a ring equivalence with continuous
inverse). -/
theorem presheafChartRingEquivBISub_isOpenMap (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    IsOpenMap (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2) := by
  intro U hU
  rw [show (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2) '' U
    = (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1
      hexact2).symm ⁻¹' U from
    Equiv.image_eq_preimage_symm _ U]
  exact (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
    (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
    hexact1 hexact2).isOpen_preimage U hU

/-- **The easy half of the plus reconciliation** (Kedlaya Def 4.5, ⊆): the
canonical plus subring of a chart value lands in the transported unit ball —
canonical-plus elements are power-bounded (the ring-of-integral-elements
field), power-boundedness transports along the open comparison map, and the
ball is exactly the power-bounded subring of `B^I`. -/
theorem completedPlusSubring_le_chartPlus (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    (chartData p F ϖ 1 b a b).completedPlusSubring
      ≤ (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map
          ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
            (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
            hexact1 hexact2).symm.toRingHom) := by
  intro x hx
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have hIRIE := RationalLocData.presheafValuePlus_isRingOfIntegralElements
    (A := Ainf p F) (chartData p F ϖ 1 b a b)
  -- power-bounded in the chart value
  have hpb : TopologicalRing.IsPowerBounded x :=
    hIRIE.subset_powerBounded hx
  -- transport to `B^I` along the open comparison
  have hpbB : TopologicalRing.IsPowerBounded
      (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2 x) :=
    isPowerBounded_map_of_isOpenMap
      (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1
        hexact2).toRingHom
      (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2)
      (presheafChartRingEquivBISub_isOpenMap p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2)
      hpb
  -- the ball membership
  have hball : presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2 x ∈ BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
    rw [mem_BIPlusIn_iff]
    exact (isPowerBounded_iff_wI_le_one p F ϖ _).mp hpbB
  refine ⟨_, hball, ?_⟩
  exact (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1
    hexact2).symm_apply_apply x

end FarguesFontaine

end
