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


/-! ### The plus reconciliation, hard half — reduced to the dense level -/

/-- **The dense-level integrality claim** (Kedlaya Def 4.5, the substantive
half): a `Bloc` element with both window Gauss norms `≤ 1` maps into the
canonical plus subring of the chart value under the comparison. -/
def ChartDensePlus (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Prop :=
  ∀ h : Bloc p F ϖ, wLoc p F ϖ hρ₁0 hρ₁1 h ≤ 1 → wLoc p F ϖ hρ₂0 hρ₂1 h ≤ 1 →
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
      (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h)
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubring

/-- Ball-bounded `Bloc` approximants of a ball element. -/
theorem exists_ball_approx (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (hz : z ∈ BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) (n : ℕ) :
    ∃ h : Bloc p F ϖ,
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
        ((z : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h) ≤ (2 : NNReal)⁻¹ ^ n
      ∧ wLoc p F ϖ hρ₁0 hρ₁1 h ≤ 1 ∧ wLoc p F ϖ hρ₂0 hρ₂1 h ≤ 1 := by
  have hzcl : ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      ∈ closure ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := z.2
  have hpos : (0 : NNReal) < min ((2 : NNReal)⁻¹ ^ n) 1 :=
    lt_min (pow_pos (by norm_num) n) one_pos
  obtain ⟨w, hwball, hh, rfl⟩ := mem_closure_iff_nhds.mp hzcl _
    (wI_ball_mem_nhds p F (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) _ hpos)
  have hzb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) ≤ 1 :=
    (mem_BIPlusIn_iff p F ϖ).mp hz
  have hwb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
        - ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      ≤ min ((2 : NNReal)⁻¹ ^ n) 1 := hwball
  have hdiff : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh) ≤ min ((2 : NNReal)⁻¹ ^ n) 1 := by
    rw [show ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
        - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
      = -(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
        - ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) from by ring,
      wI_neg]
    exact hwb
  have hh1 : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh) ≤ 1 := by
    rw [show BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
        = -((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : _ × _))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh)
          + (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : _ × _)) from by ring]
    refine le_trans (wI_add_le p F _ _) (max_le ?_ hzb)
    rw [wI_neg]
    exact le_trans hdiff (min_le_right _ _)
  have hmax : max (Valued.v ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh).1))
      (Valued.v ((BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh).2)) ≤ 1 := hh1
  refine ⟨hh, le_trans hdiff (min_le_left _ _), ?_, ?_⟩
  · have h1 := le_trans (le_max_left _ _) hmax
    rwa [BIProd_fst, valued_BlocToHatK] at h1
  · have h2 := le_trans (le_max_right _ _) hmax
    rwa [BIProd_snd, valued_BlocToHatK] at h2

/-- **The hard half of the plus reconciliation, reduced to the dense level**:
given the dense-level integrality, the transported unit ball lies in the
canonical plus subring. -/
theorem chartPlus_le_completedPlusSubring_of_dense (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hdense : ChartDensePlus p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2) :
    (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map
        ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
          hexact1 hexact2).symm.toRingHom)
      ≤ (chartData p F ϖ 1 b a b).completedPlusSubring := by
  rintro _ ⟨z, hz, rfl⟩
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have hclosed : IsClosed
      ((chartData p F ϖ 1 b a b).completedPlusSubring
        : Set (presheafValue (chartData p F ϖ 1 b a b))) := by
    have hopen : IsOpen
        ((chartData p F ϖ 1 b a b).completedPlusSubring
          : Set (presheafValue (chartData p F ϖ 1 b a b))) :=
      (RationalLocData.presheafValuePlus_isRingOfIntegralElements
        (A := Ainf p F) (chartData p F ϖ 1 b a b)).isOpen
    exact AddSubgroup.isClosed_of_isOpen
      (chartData p F ϖ 1 b a b).completedPlusSubring.toAddSubgroup hopen
  choose hseq hball hw1 hw2 using exists_ball_approx p F ϖ
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) z hz
  -- convergence of the approximants to `z`
  have htend : Filter.Tendsto
      (fun n => blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n))
      Filter.atTop (nhds z) := by
    refine tendsto_subtype_rng.mpr ?_
    refine tendsto_BIProd_of_valued_le p F ϖ (ε := fun n => (2 : NNReal)⁻¹ ^ n)
      ?_ ?_ glueSeq_eps_tendsto
    · intro n
      have hmax : max
          (Valued.v ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1))
          (Valued.v ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).2))
          ≤ (2 : NNReal)⁻¹ ^ n := hball n
      have h1 := le_trans (le_max_left _ _) hmax
      rw [show ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1)
        = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).1
          - (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1 from rfl,
        Valuation.map_sub_swap, BIProd_fst] at h1
      exact h1
    · intro n
      have hmax : max
          (Valued.v ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1))
          (Valued.v ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
            - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).2))
          ≤ (2 : NNReal)⁻¹ ^ n := hball n
      have h2 := le_trans (le_max_right _ _) hmax
      rw [show ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).2)
        = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))).2
          - (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).2 from rfl,
        Valuation.map_sub_swap, BIProd_snd] at h2
      exact h2
  have hlim : Filter.Tendsto
      (fun n => (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2).symm
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)))
      Filter.atTop
      (nhds ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2).symm z)) :=
    ((presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2).tendsto _).comp htend
  exact hclosed.mem_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => hdense (hseq n) (hw1 n) (hw2 n))


/-! ### Dense-level monomial membership (ChartDensePlus bricks m1/m3) -/

/-- Divisibility in `O_F` from the valuation comparison: an element of value
at most `|ϖ|^j` is `ϖ^j` times an integral element. -/
theorem exists_eq_toOF_pow_mul (j : ℕ) (c : OF F)
    (hc : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j) :
    ∃ c' : OF F, c = (PseudoUniformizer.toOF F ϖ : OF F) ^ j * c' := by
  have hdvd := (perfectoidValuation_integers p F).dvd_of_le
    (x := c) (y := (PseudoUniformizer.toOF F ϖ : OF F) ^ j) ?_
  · obtain ⟨c', hc'⟩ := hdvd
    exact ⟨c', hc'⟩
  · show perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
      ≤ perfectoidValuation p F
        ((algebraMap ↥(powerBoundedSubring.toSubring F) F)
          ((PseudoUniformizer.toOF F ϖ : OF F) ^ j))
    rw [show ((algebraMap ↥(powerBoundedSubring.toSubring F) F) c)
        = (c : F) from rfl,
      show ((algebraMap ↥(powerBoundedSubring.toSubring F) F)
          ((PseudoUniformizer.toOF F ϖ : OF F) ^ j))
        = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j from by
        push_cast
        rfl,
      map_pow]
    exact hc

/-- **(m1) Negative-monomial membership**: a Teichmüller monomial `[c]/p^j`
whose coordinate satisfies the left-endpoint bound `|c| ≤ |ϖ|^j` is
`chartFracPi^j · [c']` and lies in the chart subring. -/
theorem teich_div_p_pow_mem_chartSubring (a b : ℕ) (j : ℕ) (c : OF F)
    (hc : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j) :
    algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c)
        * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ j
      ∈ Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) := by
  obtain ⟨c', rfl⟩ := exists_eq_toOF_pow_mul p F ϖ j c hc
  have hkey : algebraMap (Ainf p F) (Bloc p F ϖ)
      (WittVector.teichmuller p ((PseudoUniformizer.toOF F ϖ : OF F) ^ j * c'))
        * (↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ) ^ j
      = chartFracPi p F ϖ ^ j
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c') := by
    rw [map_mul (WittVector.teichmuller p), map_pow (WittVector.teichmuller p),
      map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
      map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)), chartFracPi, mul_pow]
    rw [show WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ : OF F)
      = teichPi p F ϖ from rfl]
    ring
  rw [hkey]
  refine mul_mem (pow_mem (Subring.subset_closure ?_) j)
    (Subring.subset_closure ?_)
  · exact Set.mem_union_right _ (Set.mem_insert _ _)
  · exact Set.mem_union_left _ ⟨_, rfl⟩

/-- **(m3) Positive-monomial `a`-th-power membership**: for a fraction
monomial `(p/[ϖ])^d·[c']` whose coordinate satisfies the right-endpoint bound
`|c'|^a ≤ |ϖ|^{d(a−b)}`, the `a`-th power is `chartFracP^d·[c'']` and lies in
the chart subring — the monic witness for its integrality. -/
theorem p_div_teich_pow_a_mem_chartSubring (a b d : ℕ) (hab : b ≤ a)
    (c' : OF F)
    (hc : perfectoidValuation p F ((c' : F)) ^ a
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (d * (a - b))) :
    (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ d
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')) ^ a
      ∈ Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b}) := by
  have hc' : perfectoidValuation p F (((c' ^ a : OF F)) : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (d * (a - b)) := by
    rw [show (((c' ^ a : OF F)) : F) = ((c' : F)) ^ a from by push_cast; rfl,
      map_pow]
    exact hc
  obtain ⟨c'', hc''⟩ := exists_eq_toOF_pow_mul p F ϖ (d * (a - b)) (c' ^ a) hc'
  -- atoms
  have hIT : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * (a - b))
      * algebraMap (Ainf p F) (Bloc p F ϖ)
        (teichPi p F ϖ) ^ (d * (a - b)) = 1 := by
    rw [← map_pow (AlocToBloc p F ϖ),
      ← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
    exact AlocToBloc_teichPiInv_mul p F ϖ (d * (a - b))
  have h1 : algebraMap (Ainf p F) (Bloc p F ϖ)
        (WittVector.teichmuller p c') ^ a
      = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (d * (a - b))
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c'') := by
    rw [← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
      ← map_pow (WittVector.teichmuller p), hc'',
      map_mul (WittVector.teichmuller p),
      map_pow (WittVector.teichmuller p),
      map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
      map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
    rfl
  have h2 : chartFracP p F ϖ a b
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b := by
    rw [chartFracP, map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  have hda : d * a = d * b + d * (a - b) := by
    have h : a = b + (a - b) := by omega
    calc d * a = d * (b + (a - b)) := by rw [← h]
      _ = d * b + d * (a - b) := by ring
  have hkey : (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ d
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c')) ^ a
      = chartFracP p F ϖ a b ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c'') := by
    calc (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ d
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c')) ^ a
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (d * a)
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c') ^ a := by
          rw [(show d * a = a * d from mul_comm d a), pow_mul, pow_mul]
          ring
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (d * a)
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
        * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (d * (a - b))
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c'')) := by
        rw [h1]
      _ = (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a) ^ d
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b) ^ d
        * ((AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * (a - b))
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (teichPi p F ϖ) ^ (d * (a - b)))
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c'')) := by
        rw [show AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
            = AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * b)
              * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * (a - b)) from by
          rw [← pow_add, ← hda]]
        ring
      _ = (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a) ^ d
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b) ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c'') := by
        rw [hIT, one_mul]
      _ = chartFracP p F ϖ a b ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c'') := by
        rw [h2, mul_pow]
  rw [hkey]
  refine mul_mem (pow_mem (Subring.subset_closure ?_) d)
    (Subring.subset_closure ?_)
  · exact Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
  · exact Set.mem_union_left _ ⟨_, rfl⟩


/-! ### Monomial-fraction zone lemmas (ChartDensePlus r4b, b = 1) -/

/-- The denominator element of the `k`-th monomial fraction. -/
def sPow (k : ℕ) : Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ) :=
  ⟨((p : Ainf p F) * teichPi p F ϖ) ^ k, k, rfl⟩

/-- **(M3'') Large-exponent monomials are chart-subring elements directly**
(`b = 1`): for `i ≥ ka + k`, the monomial fraction `p^i[c]/(p[ϖ])^k` is
`chartFracP^k` times an `A_inf`-image. -/
theorem mk_monomial_mem_of_large (a k i : ℕ) (hik : k * a + k ≤ i) (c : OF F) :
    IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      ∈ Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a 1}) := by
  have hsplit : i = k * a + (i - (k * a + k)) + k := by omega
  have hIT : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ k
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k = 1 := by
    rw [← map_pow (AlocToBloc p F ϖ),
      ← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
    exact AlocToBloc_teichPiInv_mul p F ϖ k
  have hfrac : chartFracP p F ϖ a 1
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) := by
    rw [chartFracP, map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)), pow_one]
  have hkey : IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      = chartFracP p F ϖ a 1 ^ k
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) ^ (i - (k * a + k)) * WittVector.teichmuller p c) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    calc (algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) ^ i * WittVector.teichmuller p c))
        = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F)) ^ (i - (k * a + k))
          * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ k
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c) := by
          rw [map_mul (algebraMap (Ainf p F) (Bloc p F ϖ))]
          rw [show ((p : Ainf p F) ^ i)
              = (p : Ainf p F) ^ (k * a) * (p : Ainf p F) ^ (i - (k * a + k))
                * (p : Ainf p F) ^ k from by
            conv_lhs => rw [hsplit]
            rw [pow_add, pow_add]]
          rw [map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F)) ^ (i - (k * a + k))
          * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ k
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c)
          * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ k
            * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k) := by
          rw [hIT, mul_one]
      _ = chartFracP p F ϖ a 1 ^ k
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            ((p : Ainf p F) ^ (i - (k * a + k)) * WittVector.teichmuller p c)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k) := by
          simp only [hfrac, mul_pow,
            map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
          generalize algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) = P
          generalize AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) = I
          generalize algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c) = C
          generalize algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) = T
          ring
  rw [hkey]
  refine mul_mem (pow_mem (Subring.subset_closure ?_) k)
    (Subring.subset_closure ?_)
  · exact Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
  · exact Set.mem_union_left _ ⟨_, rfl⟩

/-- **(M1'') Small-exponent monomials are chart-subring elements**: for
`i ≤ k` with the left-endpoint bound `|c| ≤ |ϖ|^{2k−i}`, the monomial
fraction `p^i[c]/(p[ϖ])^k` is an `m1`-form element. -/
theorem mk_monomial_mem_of_le (a k i : ℕ) (hik : i ≤ k) (c : OF F)
    (hc : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (2 * k - i)) :
    IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      ∈ Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a 1}) := by
  have hπpos : (0 : NNReal) < perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) := vpi_pos p F ϖ
  have hck : perfectoidValuation p F (c : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ k := by
    refine le_trans hc (pow_le_pow_of_le_one zero_le
      (perfectoidValuation_toOF_lt_one p F ϖ).le (by omega))
  obtain ⟨c', hc'eq⟩ := exists_eq_toOF_pow_mul p F ϖ k c hck
  have hc' : perfectoidValuation p F (c' : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (k - i) := by
    have hval : perfectoidValuation p F (c : F)
        = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k
          * perfectoidValuation p F (c' : F) := by
      rw [hc'eq]
      rw [show (((PseudoUniformizer.toOF F ϖ : OF F) ^ k * c' : OF F) : F)
          = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k * (c' : F) from by
        push_cast; rfl]
      rw [Valuation.map_mul, map_pow]
    have h2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ k * perfectoidValuation p F (c' : F)
        ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ k * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (k - i) := by
      rw [← hval, ← pow_add]
      rw [show k + (k - i) = 2 * k - i from by omega]
      exact hc
    exact le_of_mul_le_mul_left h2 (pow_pos hπpos k)
  have hcancel : ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
      * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k - i) = 1 := by
    have h := (isUnit_p_image p F ϖ).unit.inv_mul
    rw [(isUnit_p_image p F ϖ).unit_spec] at h
    calc ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k - i)
        = (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ))
          * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F))) ^ (k - i) :=
          (mul_pow _ _ _).symm
      _ = 1 := by rw [h, one_pow]
  have hkey : IsLocalization.mk' (Bloc p F ϖ)
      ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
        * ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i) := by
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    have hsplitp : (k : ℕ) = i + (k - i) := by omega
    calc (algebraMap (Ainf p F) (Bloc p F ϖ)
          ((p : Ainf p F) ^ i * WittVector.teichmuller p c))
        = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ i
          * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k
            * algebraMap (Ainf p F) (Bloc p F ϖ)
              (WittVector.teichmuller p c')) := by
          rw [hc'eq, map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_mul (WittVector.teichmuller p),
            map_pow (WittVector.teichmuller p),
            map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
          rfl
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
          * ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
          * (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k - i)
            * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ i
            * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k) := by
          rw [show algebraMap (Ainf p F) (Bloc p F ϖ)
              (WittVector.teichmuller p c')
              * ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
              * (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k - i)
                * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ i
                * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k)
            = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
              * (((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
                * algebraMap (Ainf p F) (Bloc p F ϖ)
                  ((p : Ainf p F)) ^ (k - i))
              * (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ i
                * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k)
            from by ring, hcancel, mul_one]
          ring
      _ = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
          * ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (((p : Ainf p F) * teichPi p F ϖ) ^ k) := by
          congr 1
          rw [map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
            map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)), mul_pow]
          rw [show algebraMap (Ainf p F) (Bloc p F ϖ)
              ((p : Ainf p F)) ^ (k - i)
              * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ i
            = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ k from by
            rw [← pow_add]
            congr 1
            omega]
  rw [hkey]
  exact teich_div_p_pow_mem_chartSubring p F ϖ a 1 (k - i) c' hc'

end FarguesFontaine

end
