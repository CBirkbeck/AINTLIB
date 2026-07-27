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

end FarguesFontaine

end
