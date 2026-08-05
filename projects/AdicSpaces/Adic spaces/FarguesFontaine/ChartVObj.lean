/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.ChartComparison
import «Adic spaces».StructureSheafStalks
import «Adic spaces».FarguesFontaine.IntervalSplitting
import «Adic spaces».FarguesFontaine.YPresheaf

/-!
# The Fargues–Fontaine charts as objects of `𝒱` (D-ii-3 instantiation)

`chartVObj`: `Spa` of a Big-window chart of `𝒴` as an object of Wedhorn's
category `𝒱` — the generic stalk package (`spaVObj`, Wedhorn 8.14/8.20)
instantiated at the chart pair through the ID2 comparison: Tate via
`isTateRing_congr`, plus structure the transported `B^I`-unit ball,
sheafiness `isSheafy_presheafChart`.

The plus-reconciliation is **proven** here: `chartPlus_eq_canonical`
(via `chartDensePlus_of_exact`, the dense-level integrality theorem) shows
the transported `B^I`-unit ball equals the canonical `completedPlusSubring`
at the `b = 1` window, so the chart `VObj`'s plus structure is canonical.
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
  have hT := isTateRing_presheafChart p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  have : IsHuberRing (presheafValue (chartData p F ϖ 1 b a b)) :=
    hT.toIsHuberRing
  letI : @CompleteSpace (presheafValue (chartData p F ϖ 1 b a b))
      (IsTopologicalAddGroup.rightUniformSpace
        (presheafValue (chartData p F ϖ 1 b a b))) :=
    completeSpace_right_presheafValue (chartData p F ϖ 1 b a b)
  have : IsRingOfIntegralElements
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
  have : ValuationSpectrum.IsSheafy
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
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
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
    rw [show ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
      hρ₂1))
        - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
      = -(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
        - ((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
          hρ₂1))) by ring,
      wI_neg]
    exact hwb
  have hh1 : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh) ≤ 1 := by
    rw [show BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh
        = -((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : _ × _))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 hh)
          + (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : _ × _)) by ring]
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

/-- The completed plus-subring of a chart datum is closed: it is open
(`presheafValuePlus_isRingOfIntegralElements`), and an open subgroup of a topological group is
closed. -/
private theorem isClosed_chartData_completedPlusSubring (a b : ℕ) :
    IsClosed ((chartData p F ϖ 1 b a b).completedPlusSubring
      : Set (presheafValue (chartData p F ϖ 1 b a b))) := by
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  exact AddSubgroup.isClosed_of_isOpen
    (chartData p F ϖ 1 b a b).completedPlusSubring.toAddSubgroup
    (RationalLocData.presheafValuePlus_isRingOfIntegralElements
      (A := Ainf p F) (chartData p F ϖ 1 b a b)).isOpen

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
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) := isAffinoidRing_Ainf p F
  have hclosed := isClosed_chartData_completedPlusSubring p F ϖ a b
  choose hseq hball hw1 hw2 using exists_ball_approx p F ϖ
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) z hz
  -- convergence of the approximants to `z`
  have htend : Filter.Tendsto (fun n => blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n))
      Filter.atTop (nhds z) := by
    refine tendsto_subtype_rng.mpr ?_
    refine tendsto_BIProd_of_valued_le p F ϖ (ε := fun n => (2 : NNReal)⁻¹ ^ n)
      ?_ ?_ glueSeq_eps_tendsto
    · intro n
      have h1 := le_trans (le_max_left _ _) (hball n)
      rw [show ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
        hρ₂1))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1)
        = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
          hρ₂1))).1
          - (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).1 from rfl,
        Valuation.map_sub_swap, BIProd_fst] at h1
      exact h1
    · intro n
      have h2 := le_trans (le_max_right _ _) (hball n)
      rw [show ((((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
        hρ₂1))
          - BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (hseq n)).2)
        = (((z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0
          hρ₂1))).2
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

omit [CharP F p] in
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
        = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ j by
        push_cast
        rfl,
      map_pow]
    exact hc

omit [CharP F p] in
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

/-- The `pow`-outside form of `AlocToBloc_teichPiInv_mul`: the two Teichmüller atoms are
mutually inverse in `Bloc`, with the exponent outside the ring maps. -/
private theorem AlocToBloc_teichPiInv_pow_mul (k : ℕ) :
    AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ k
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k = 1 := by
  rw [← map_pow (AlocToBloc p F ϖ), ← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  exact AlocToBloc_teichPiInv_mul p F ϖ k

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- Transport of the `OF F`-level factorisation `c' ^ a = ϖ ^ (d(a-b)) * c''` through the
Teichmüller lift and `algebraMap`. -/
private theorem teichmuller_pow_eq_teichPi_pow_mul {a b d : ℕ} {c' c'' : OF F}
    (hc'' : c' ^ a = (PseudoUniformizer.toOF F ϖ : OF F) ^ (d * (a - b)) * c'') :
    algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c') ^ a
      = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (d * (a - b))
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'') := by
  rw [← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
    ← map_pow (WittVector.teichmuller p), hc'',
    map_mul (WittVector.teichmuller p),
    map_pow (WittVector.teichmuller p),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
    map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  rfl

/-- **The chart-generator identity.** Once `c' ^ a` factors as `ϖ ^ (d(a-b)) * c''` in `OF F`,
the `a`-th power of the chart generator `p^d * (π⁻¹)^d * [c']` collapses to
`chartFracP a b ^ d * [c'']`. Extracted from `p_div_teich_pow_a_mem_chartSubring`, where it was
the whole algebraic content; what remains there is `Subring.closure` bookkeeping. -/
private theorem chartGen_pow_eq_chartFracP_pow_mul {a b d : ℕ} (hab : b ≤ a) {c' c'' : OF F}
    (hc'' : c' ^ a = (PseudoUniformizer.toOF F ϖ : OF F) ^ (d * (a - b)) * c'') :
    (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ d
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')) ^ a
      = chartFracP p F ϖ a b ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'') := by
  have hIT := AlocToBloc_teichPiInv_pow_mul p F ϖ (d * (a - b))
  have h1 := teichmuller_pow_eq_teichPi_pow_mul p F ϖ hc''
  have h2 : chartFracP p F ϖ a b
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b := by
    rw [chartFracP, map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  have hda : d * a = d * b + d * (a - b) := by
    have h : a = b + (a - b) := by omega
    calc d * a = d * (b + (a - b)) := by rw [← h]
      _ = d * b + d * (a - b) := by ring
  calc (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ d
      * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
      * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')) ^ a
    = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (d * a)
      * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c') ^ a := by
        rw [(show d * a = a * d from mul_comm d a), pow_mul, pow_mul]
        ring
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (d * a)
      * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
      * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (d * (a - b))
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'')) := by
      rw [h1]
    _ = (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a) ^ d
      * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b) ^ d
      * ((AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * (a - b))
        * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (d * (a - b)))
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'')) := by
      rw [show AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * a)
          = AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * b)
            * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ (d * (a - b)) by
        rw [← pow_add, ← hda]]
      ring
    _ = (algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a) ^ d
      * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ b) ^ d
      * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'') := by
      rw [hIT, one_mul]
    _ = chartFracP p F ϖ a b ^ d
      * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'') := by
      rw [h2, mul_pow]

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
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (d * (a - b)) := by
    rw [show (((c' ^ a : OF F)) : F) = ((c' : F)) ^ a by push_cast; rfl, map_pow]
    exact hc
  obtain ⟨c'', hc''⟩ := exists_eq_toOF_pow_mul p F ϖ (d * (a - b)) (c' ^ a) hc'
  rw [chartGen_pow_eq_chartFracP_pow_mul p F ϖ hab hc'']
  refine mul_mem (pow_mem (Subring.subset_closure ?_) d) (Subring.subset_closure ?_)
  · exact Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
  · exact Set.mem_union_left _ ⟨_, rfl⟩


/-! ### Monomial-fraction zone lemmas (ChartDensePlus r4b, b = 1) -/

/-- The denominator element of the `k`-th monomial fraction. -/
def sPow (k : ℕ) : Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ) :=
  ⟨((p : Ainf p F) * teichPi p F ϖ) ^ k, k, rfl⟩

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- The denominators multiply: `s^k` raised to `a` is `s^{k·a}`. -/
theorem sPow_pow (k a : ℕ) : (sPow p F ϖ k) ^ a = sPow p F ϖ (k * a) := by
  refine Subtype.ext ?_
  show (((p : Ainf p F) * teichPi p F ϖ) ^ k) ^ a
    = ((p : Ainf p F) * teichPi p F ϖ) ^ (k * a)
  rw [← pow_mul]

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- **Powers of a monomial fraction**: numerator and denominator both raise. Stated
here rather than at its first use because `RobbaPresentation` — which is downstream —
had the only named copy, forcing this file to inline it. -/
theorem mk'_sPow_pow (w : Ainf p F) (k a : ℕ) :
    (IsLocalization.mk' (Bloc p F ϖ) w (sPow p F ϖ k)) ^ a
      = IsLocalization.mk' (Bloc p F ϖ) (w ^ a) (sPow p F ϖ (k * a)) := by
  rw [← sPow_pow p F ϖ k a]
  exact (IsLocalization.mk'_pow _ _ a).symm

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- **Normal form for a large-exponent monomial fraction.** With `k*a + k ≤ i`, the
fraction `p^i[c]/(p[ϖ])^k` factors as `chartFracP^k` times an integral monomial. -/
private theorem mk_monomial_eq_chartFracP_pow_mul {a k i : ℕ} (c : OF F)
    (hsplit : i = k * a + (i - (k * a + k)) + k)
    (hIT : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ k
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ k = 1)
    (hfrac : chartFracP p F ϖ a 1
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) :
    IsLocalization.mk' (Bloc p F ϖ)
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
              * (p : Ainf p F) ^ k by
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
  have hkey := mk_monomial_eq_chartFracP_pow_mul p F ϖ c hsplit hIT hfrac
  rw [hkey]
  refine mul_mem (pow_mem (Subring.subset_closure ?_) k)
    (Subring.subset_closure ?_)
  · exact Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
  · exact Set.mem_union_left _ ⟨_, rfl⟩

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- The inverse of the image of `p` cancels its `n`-th power. -/
private theorem pInv_pow_mul_p_pow (n : ℕ) :
    ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ n
      * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ n = 1 := by
  have h := (isUnit_p_image p F ϖ).unit.inv_mul
  rw [(isUnit_p_image p F ϖ).unit_spec] at h
  rw [← mul_pow, h, one_pow]

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- **Normal form for a monomial fraction.** Once the numerator's Teichmüller
argument is written as `ϖ^k * c'`, the fraction `p^i[c]/(p[ϖ])^k` collapses to
`[c']` times a power of the inverse of the image of `p`. -/
private theorem mk_monomial_eq_teich_mul_pInv_pow {k i : ℕ} (hik : i ≤ k) {c c' : OF F}
    (hc'eq : c = (PseudoUniformizer.toOF F ϖ : OF F) ^ k * c') :
    IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i * WittVector.teichmuller p c) (sPow p F ϖ k)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c')
        * ((↑(isUnit_p_image p F ϖ).unit⁻¹ : Bloc p F ϖ)) ^ (k - i) := by
  rw [IsLocalization.mk'_eq_iff_eq_mul]
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
          by ring, pInv_pow_mul_p_pow p F ϖ (k - i), mul_one]
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
          = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ k by
          rw [← pow_add]
          congr 1
          omega]

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
          = ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ k * (c' : F) by
        push_cast; rfl]
      rw [Valuation.map_mul, map_pow]
    have h2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ k * perfectoidValuation p F (c' : F)
        ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ k * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (k - i) := by
      rw [← hval, ← pow_add]
      rw [show k + (k - i) = 2 * k - i by omega]
      exact hc
    exact le_of_mul_le_mul_left h2 (pow_pos hπpos k)
  rw [mk_monomial_eq_teich_mul_pInv_pow p F ϖ hik hc'eq]
  exact teich_div_p_pow_mem_chartSubring p F ϖ a 1 (k - i) c' hc'

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- The `a`-th power of the numerator splits off the `p`-powers and the balanced
Teichmüller factor supplied by `exists_eq_toOF_pow_mul`. -/
private theorem numerator_pow_factor (a k d : ℕ) (c c'' : OF F)
    (hc'' : (c ^ a : OF F) = (PseudoUniformizer.toOF F ϖ : OF F) ^ (k * a - d) * c'') :
    algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) ^ (k + d) * WittVector.teichmuller p c) ^ a)
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (a * d)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
        * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (k * a - d)
          * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'')) := by
  rw [mul_pow, ← pow_mul,
    ← map_pow (WittVector.teichmuller p), hc'',
    map_mul (WittVector.teichmuller p),
    map_pow (WittVector.teichmuller p),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
    map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)),
    map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  rw [show (k + d) * a = a * d + k * a by
    rw [add_mul]
    rw [show d * a = a * d from mul_comm d a]
    omega, pow_add]
  rw [show WittVector.teichmuller p
    (PseudoUniformizer.toOF F ϖ : OF F) = teichPi p F ϖ from rfl]

omit [IsTopologicalRing F] [UniformSpace F] [IsPerfectoidField p F] [CharP F p] in
/-- Regroup the factored numerator into `chartFracP ^ d` times the Teichmüller factor
times `alg (s ^ (k*a))`: the `teichPi`-powers split as `(k*a - d) + d`, and the rest
is `ring`. -/
private theorem chartFracP_pow_regroup (a k d : ℕ) (hd : d ≤ k * a) (c'' : OF F)
    (hfrac : chartFracP p F ϖ a 1
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ)) :
    algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (a * d)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
        * (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (k * a - d)
          * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c''))
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
          * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ d)
      = chartFracP p F ϖ a 1 ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ) (WittVector.teichmuller p c'')
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((((p : Ainf p F)) * teichPi p F ϖ) ^ (k * a)) := by
  simp only [hfrac, mul_pow,
    map_mul (algebraMap (Ainf p F) (Bloc p F ϖ)),
    map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
  rw [show algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (k * a)
    = algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ (k * a - d)
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ d by
    rw [← pow_add]
    congr 1
    omega]
  generalize (algebraMap (Ainf p F) (Bloc p F ϖ)) ((p : Ainf p F)) = P
  generalize AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) = I
  generalize (algebraMap (Ainf p F) (Bloc p F ϖ)) (WittVector.teichmuller p c'') = C
  generalize (algebraMap (Ainf p F) (Bloc p F ϖ)) (teichPi p F ϖ) = T
  ring

/-- **(M2'') Middle-zone monomials: the `a`-th power identity** (`b = 1`):
for `0 < d ≤ ka`, the `a`-th power of the monomial fraction
`p^{k+d}[c]/(p[ϖ])^k` with the right-endpoint bound `|c|^a ≤ |ϖ|^{ka−d}` is
`chartFracP^d` times a Teichmüller image — the monic witness for its
integrality over the chart subring. -/
theorem mk_monomial_pow_a_eq (a k d : ℕ) (hd : d ≤ k * a) (c : OF F)
    (hc : perfectoidValuation p F (c : F) ^ a
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (k * a - d)) :
    ∃ c'' : OF F,
      (IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ (k + d) * WittVector.teichmuller p c)
          (sPow p F ϖ k)) ^ a
        = chartFracP p F ϖ a 1 ^ d
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c'') := by
  have hc' : perfectoidValuation p F (((c ^ a : OF F)) : F)
      ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ (k * a - d) := by
    rw [show (((c ^ a : OF F)) : F) = ((c : F)) ^ a by push_cast; rfl,
      map_pow]
    exact hc
  obtain ⟨c'', hc''⟩ := exists_eq_toOF_pow_mul p F ϖ (k * a - d) (c ^ a) hc'
  refine ⟨c'', ?_⟩
  have hIT : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
      * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ d = 1 := by
    rw [← map_pow (AlocToBloc p F ϖ),
      ← map_pow (algebraMap (Ainf p F) (Bloc p F ϖ))]
    exact AlocToBloc_teichPiInv_mul p F ϖ d
  have hfrac : chartFracP p F ϖ a 1
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ a
        * AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) := by
    rw [chartFracP, map_pow (algebraMap (Ainf p F) (Bloc p F ϖ)), pow_one]
  -- both sides times `alg(s^{ka})` agree
  rw [mk'_sPow_pow p F ϖ ((p : Ainf p F) ^ (k + d) * WittVector.teichmuller p c) k a,
    IsLocalization.mk'_eq_iff_eq_mul]
  calc (algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) ^ (k + d) * WittVector.teichmuller p c) ^ a))
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (a * d)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
        * (algebraMap (Ainf p F) (Bloc p F ϖ)
            (teichPi p F ϖ) ^ (k * a - d)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c'')) :=
        numerator_pow_factor p F ϖ a k d c c'' hc''
    _ = algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (a * d)
        * algebraMap (Ainf p F) (Bloc p F ϖ) ((p : Ainf p F)) ^ (k * a)
        * (algebraMap (Ainf p F) (Bloc p F ϖ)
            (teichPi p F ϖ) ^ (k * a - d)
          * algebraMap (Ainf p F) (Bloc p F ϖ)
            (WittVector.teichmuller p c''))
        * (AlocToBloc p F ϖ (teichPiInvAloc p F ϖ) ^ d
          * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ) ^ d) := by
        rw [hIT, mul_one]
    _ = chartFracP p F ϖ a 1 ^ d
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          (WittVector.teichmuller p c'')
        * algebraMap (Ainf p F) (Bloc p F ϖ)
          ((((p : Ainf p F)) * teichPi p F ϖ) ^ (k * a)) :=
        chartFracP_pow_regroup p F ϖ a k d hd c'' hfrac


/-! ### The transport to the canonical plus subring (ChartDensePlus bricks) -/

/-- **The transport law**: the inverse comparison map carries the diagonal
image of a `Bloc` element to the completion-coe of its localization avatar. -/
theorem presheafChartRingEquivBISub_symm_blocToBI (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (h : Bloc p F ϖ) :
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h)
      = (chartData p F ϖ 1 b a b).coeRingHom
          ((blocEquivAwayChartS p F ϖ b hb).symm h) := by
  apply (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).injective
  rw [RingEquiv.apply_symm_apply]
  have hcmp : (chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
      ((chartData p F ϖ 1 b a b).coeRingHom
        ((blocEquivAwayChartS p F ϖ b hb).symm h))
      = chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) b hb ((blocEquivAwayChartS p F ϖ b hb).symm h) :=
    @AbstractCompletion.compare_coe _ (chartUniformity p F ϖ a b)
      (@UniformSpace.Completion.cPkg _ (chartUniformity p F ϖ a b))
      (chartBIPkg p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2)
      ((blocEquivAwayChartS p F ϖ b hb).symm h)
  have hfwd : (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
      ((chartData p F ϖ 1 b a b).coeRingHom
        ((blocEquivAwayChartS p F ϖ b hb).symm h))
      = chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) b hb ((blocEquivAwayChartS p F ϖ b hb).symm h) := by
    rw [show (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2)
        ((chartData p F ϖ 1 b a b).coeRingHom
          ((blocEquivAwayChartS p F ϖ b hb).symm h))
      = presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb (le_of_eq hexact1)
          (vpi_le_rho2_of_exact p F ϖ (hρ₁1 := hρ₁1) a b ha hb hab
            hexact1 hexact2)
          (rho1_pow_le_of_exact p F ϖ (hρ₁1 := hρ₁1) a b hab hexact1)
          (le_of_eq hexact2)
          ((chartData p F ϖ 1 b a b).coeRingHom
            ((blocEquivAwayChartS p F ϖ b hb).symm h)) from rfl]
    rw [congrFun (presheafChartToBI_eq_compare p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2) _]
    exact hcmp
  rw [hfwd]
  apply Subtype.ext
  show (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) h
    = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        (blocEquivAwayChartS p F ϖ b hb
          ((blocEquivAwayChartS p F ϖ b hb).symm h))
  rw [RingEquiv.apply_symm_apply]

/-- **The chart generators land in the localization plus-subring** under the
chart identification: `S ⊆ (A⁺[T/s])`-image. -/
theorem chartSubring_le_locPlusSubring_map (a b : ℕ) (hb : 0 < b) :
    Subring.closure
        (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
          ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})
      ≤ ((chartData p F ϖ 1 b a b).locPlusSubring).map
          (blocEquivAwayChartS p F ϖ b hb).toRingHom := by
  rw [Subring.closure_le]
  rintro x (⟨y, rfl⟩ | hx)
  · exact ⟨algebraMap (Ainf p F) (Localization.Away (chartS p F ϖ 1 b)) y,
      RationalLocData.algebraMap_Aplus_mem_locPlusSubring _
        (Subring.mem_top y),
      blocEquivAwayChartS_algebraMap p F ϖ b hb y⟩
  · rcases hx with rfl | hx
    · exact ⟨divByS (teichPi p F ϖ ^ (b + 1)) (chartS p F ϖ 1 b),
        RationalLocData.divByS_mem_locPlusSubring _
          (by rw [show (chartData p F ϖ 1 b a b).T = chartT p F ϖ a b
              from rfl, chartT]; simp),
        blocEquiv_divByS_teichPi p F ϖ b hb⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨divByS ((p : Ainf p F) ^ (a + 1)) (chartS p F ϖ 1 b),
        RationalLocData.divByS_mem_locPlusSubring _
          (by rw [show (chartData p F ϖ 1 b a b).T = chartT p F ϖ a b
              from rfl, chartT]; simp),
        blocEquiv_divByS_p p F ϖ a b hb⟩

/-- Chart-subring elements are carried into the completed plus-base. -/
theorem coeRingHom_mem_completedPlusSubringBase_of_mem (a b : ℕ) (hb : 0 < b)
    {h : Bloc p F ϖ}
    (hS : h ∈ Subring.closure
      (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
        ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})) :
    (chartData p F ϖ 1 b a b).coeRingHom
        ((blocEquivAwayChartS p F ϖ b hb).symm h)
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubringBase := by
  obtain ⟨w, hw, hweq⟩ := chartSubring_le_locPlusSubring_map p F ϖ a b hb hS
  have hsymm : (blocEquivAwayChartS p F ϖ b hb).symm h = w := by
    rw [← hweq]
    exact RingEquiv.symm_apply_apply _ w
  rw [hsymm]
  have hint : ∀ u, u ∈ (chartData p F ϖ 1 b a b).locPlusSubring →
      u ∈ (integralClosure ↥((chartData p F ϖ 1 b a b).locPlusSubring)
        (Localization.Away (chartData p F ϖ 1 b a b).s)).toSubring :=
    fun u hu => Subalgebra.mem_toSubring.mpr
      (show IsIntegral
          (↥((chartData p F ϖ 1 b a b).locPlusSubring)) u from
        isIntegral_algebraMap
          (x := (⟨u, hu⟩ : ↥((chartData p F ϖ 1 b a b).locPlusSubring))))
  exact Subring.le_topologicalClosure _ ⟨w, hint w hw, rfl⟩

/-- `S`-members transport into the canonical plus subring. -/
theorem symm_blocToBI_mem_completedPlusSubring_of_mem (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {h : Bloc p F ϖ}
    (hS : h ∈ Subring.closure
      (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
        ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})) :
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h)
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubring := by
  rw [presheafChartRingEquivBISub_symm_blocToBI p F ϖ a b ha hb hab
    hexact1 hexact2 h]
  exact RationalLocData.completedPlusSubringBase_le_completedPlusSubring _
    (coeRingHom_mem_completedPlusSubringBase_of_mem p F ϖ a b hb hS)

/-- Elements whose `n`-th power lies in `S` transport into the canonical plus
subring (monic integrality `X^n − s₀` over the base). -/
theorem symm_blocToBI_mem_completedPlusSubring_of_pow_mem (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    {n : ℕ} (hn : 0 < n) {h : Bloc p F ϖ}
    (hS : h ^ n ∈ Subring.closure
      (Set.range (algebraMap (Ainf p F) (Bloc p F ϖ))
        ∪ {chartFracPi p F ϖ, chartFracP p F ϖ a b})) :
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 h)
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubring := by
  rw [presheafChartRingEquivBISub_symm_blocToBI p F ϖ a b ha hb hab
    hexact1 hexact2 h]
  have hbase0 : (chartData p F ϖ 1 b a b).coeRingHom
      ((blocEquivAwayChartS p F ϖ b hb).symm (h ^ n))
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubringBase :=
    coeRingHom_mem_completedPlusSubringBase_of_mem p F ϖ a b hb hS
  have heq : (chartData p F ϖ 1 b a b).coeRingHom
      ((blocEquivAwayChartS p F ϖ b hb).symm h) ^ n
      = (chartData p F ϖ 1 b a b).coeRingHom
        ((blocEquivAwayChartS p F ϖ b hb).symm (h ^ n)) :=
    ((congrArg ((chartData p F ϖ 1 b a b).coeRingHom)
        (map_pow (blocEquivAwayChartS p F ϖ b hb).symm h n)).trans
      (map_pow ((chartData p F ϖ 1 b a b).coeRingHom) _ n)).symm
  have hbase : (chartData p F ϖ 1 b a b).coeRingHom
      ((blocEquivAwayChartS p F ϖ b hb).symm h) ^ n
      ∈ (chartData p F ϖ 1 b a b).completedPlusSubringBase := by
    rw [heq]
    exact hbase0
  refine Subalgebra.mem_toSubring.mpr (IsIntegral.of_pow hn ?_)
  exact show IsIntegral
      (↥((chartData p F ϖ 1 b a b).completedPlusSubringBase))
      ((chartData p F ϖ 1 b a b).coeRingHom
        ((blocEquivAwayChartS p F ϖ b hb).symm h) ^ n) from
    isIntegral_algebraMap
      (x := (⟨_, hbase⟩
        : ↥((chartData p F ϖ 1 b a b).completedPlusSubringBase)))

/-- **Zone dispatch** (`b = 1`): a monomial fraction `p^i[c]/(p[ϖ])^k` whose
coefficient obeys both window Gauss-term bounds transports into the canonical
plus subring — zone `i ≤ k` by `ϖ`-divisibility, zone `k < i ≤ k(a+1)` by
`a`-th-power integrality, zone `k(a+1) ≤ i` directly. -/
theorem monomial_symm_blocToBI_mem_completedPlusSubring (a : ℕ) (ha : 0 < a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ 1)
    (k i : ℕ) (c : OF F)
    (hc1 : ρ₁ ^ i * perfectoidValuation p F (c : F)
      ≤ (ρ₁ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)
    (hc2 : ρ₂ ^ i * perfectoidValuation p F (c : F)
      ≤ (ρ₂ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) :
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha hexact1 hexact2).symm
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ)
            ((p : Ainf p F) ^ i * WittVector.teichmuller p c)
            (sPow p F ϖ k)))
      ∈ (chartData p F ϖ 1 1 a 1).completedPlusSubring := by
  have hπ0 : (0 : NNReal) < perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) := vpi_pos p F ϖ
  by_cases hik : i ≤ k
  · -- zone M1
    refine symm_blocToBI_mem_completedPlusSubring_of_mem p F ϖ a 1 ha one_pos ha hexact1 hexact2 ?_
    refine mk_monomial_mem_of_le p F ϖ a k i hik c ?_
    rw [← hexact1] at hc1
    rw [show (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ i
        * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (2 * k - i) by
      rw [← sq, ← pow_mul, ← pow_add]
      congr 1
      omega] at hc1
    exact le_of_mul_le_mul_left hc1 (pow_pos hπ0 i)
  · by_cases hika : i ≤ k * a + k
    · -- zone M2: i = k + d with 0 < d ≤ ka
      have hd : i - k ≤ k * a := by omega
      have hca : perfectoidValuation p F (c : F) ^ a
          ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
            ^ (k * a - (i - k)) := by
        have hstep := pow_le_pow_left' hc2 a
        rw [show (ρ₂ ^ i * perfectoidValuation p F (c : F)) ^ a
            = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ i
              * perfectoidValuation p F (c : F) ^ a by
          rw [mul_pow, ← pow_mul, mul_comm i a, pow_mul, hexact2, pow_one]]
          at hstep
        rw [show ((ρ₂ * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k) ^ a
            = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ i
              * perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
                ^ (k * a - (i - k)) by
          rw [← pow_mul, mul_pow,
            show ρ₂ ^ (k * a) = (ρ₂ ^ a) ^ k by
              rw [← pow_mul, mul_comm a k],
            hexact2, pow_one, ← pow_add, ← pow_add]
          congr 1
          omega] at hstep
        exact le_of_mul_le_mul_left hstep (pow_pos hπ0 i)
      rw [show i = k + (i - k) by omega]
      obtain ⟨c'', hc''⟩ := mk_monomial_pow_a_eq p F ϖ a k (i - k) hd c hca
      refine symm_blocToBI_mem_completedPlusSubring_of_pow_mem p F ϖ a 1 ha
        one_pos ha hexact1 hexact2 ha ?_
      rw [hc'']
      refine mul_mem (pow_mem (Subring.subset_closure ?_) _) (Subring.subset_closure ?_)
      · exact Set.mem_union_right _ (Set.mem_insert_of_mem _ rfl)
      · exact Set.mem_union_left _ ⟨_, rfl⟩
    · -- zone M3
      refine symm_blocToBI_mem_completedPlusSubring_of_mem p F ϖ a 1 ha
        one_pos ha hexact1 hexact2 ?_
      exact mk_monomial_mem_of_large p F ϖ a k i (by omega) c


/-! ### The head/tail split and the dense-level integrality theorem -/

/-- The Gauss value of the denominator `(p[ϖ])^k`. -/
theorem gaussValue_sPow {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (k : ℕ) :
    gaussValue p F ρ ((sPow p F ϖ k : Ainf p F))
      = (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
  rw [show ((sPow p F ϖ k : Submonoid.powers
        ((p : Ainf p F) * teichPi p F ϖ)) : Ainf p F)
      = ((p : Ainf p F) * teichPi p F ϖ) ^ k from rfl]
  rw [show gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
      = gaussVal p F hρ0 hρ1 (((p : Ainf p F) * teichPi p F ϖ) ^ k) from
    (gaussVal_apply p F hρ0 hρ1 _).symm]
  rw [Valuation.map_pow, gaussVal_apply, gaussValue_p_teichPi p F ϖ hρ1]

/-- **Per-coefficient bound from the localized unit-ball condition**: if the
fraction `x/(p[ϖ])^k` has `wLoc ≤ 1`, every Gauss term of `x` is bounded by
the denominator's Gauss value. -/
theorem gaussTerm_le_of_wLoc_mk'_le_one {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x : Ainf p F) (k : ℕ)
    (hw : wLoc p F ϖ hρ0 hρ1
      (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)) ≤ 1) (i : ℕ) :
    ρ ^ i * perfectoidValuation p F ((teichCoeff p F x i : F))
      ≤ (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
  have hgv : gaussValue p F ρ x
      ≤ (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
    rw [wLoc_mk' p F ϖ hρ0 hρ1, gaussValue_sPow p F ϖ hρ0 hρ1 k] at hw
    have hB : ((ρ * perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k : NNReal) ≠ 0 :=
      (pow_pos (mul_pos hρ0 (vpi_pos p F ϖ)) k).ne'
    calc gaussValue p F ρ x
        = gaussValue p F ρ x
          * ((ρ * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)⁻¹
          * (ρ * perfectoidValuation p F
              ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := by
          rw [mul_assoc, inv_mul_cancel₀ hB, mul_one]
      _ ≤ 1 * (ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k :=
          mul_le_mul_left hw _
      _ = (ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k := one_mul _
  exact le_trans (le_ciSup (bddAbove_range_gaussTerm p F hρ1.le x) i) hgv

/-- **The head/tail split of a localized element** along a Teichmüller
truncation witness. -/
theorem mk'_sPow_split (x : Ainf p F) (k N : ℕ) (w : Ainf p F)
    (hw : x - ∑ i ∈ Finset.Iic N,
        WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i
      = (p : Ainf p F) ^ (N + 1) * w) :
    IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)
      = (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          (sPow p F ϖ k))
        + IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ (N + 1) * w)
            (sPow p F ϖ k) := by
  have hx : x = (∑ i ∈ Finset.Iic N,
      (p : Ainf p F) ^ i * WittVector.teichmuller p (teichCoeff p F x i))
      + (p : Ainf p F) ^ (N + 1) * w := by
    rw [show ∑ i ∈ Finset.Iic N,
        (p : Ainf p F) ^ i * WittVector.teichmuller p (teichCoeff p F x i)
      = ∑ i ∈ Finset.Iic N,
        WittVector.teichmuller p (teichCoeff p F x i) * (p : Ainf p F) ^ i
      from Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [← hw]
    ring
  rw [IsLocalization.mk'_eq_mul_mk'_one,
    show algebraMap (Ainf p F) (Bloc p F ϖ) x
      = algebraMap (Ainf p F) (Bloc p F ϖ)
        ((∑ i ∈ Finset.Iic N, (p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          + (p : Ainf p F) ^ (N + 1) * w) from
      congrArg _ hx,
    map_add, map_sum, add_mul, Finset.sum_mul]
  simp only [← IsLocalization.mk'_eq_mul_mk'_one]

/-- **The tail bound**: the localized `p^{N+1}`-tail has `wLoc` at most
`ρ^{N+1}` over the denominator's Gauss value. -/
theorem wLoc_mk'_tail_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (k N : ℕ) (w : Ainf p F) :
    wLoc p F ϖ hρ0 hρ1 (IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ (N + 1) * w) (sPow p F ϖ k))
      ≤ ρ ^ (N + 1)
        * (((ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)⁻¹) := by
  rw [wLoc_mk' p F ϖ hρ0 hρ1, gaussValue_sPow p F ϖ hρ0 hρ1 k]
  refine mul_le_mul_left ?_ _
  have hmul : gaussValue p F ρ ((p : Ainf p F) ^ (N + 1) * w)
      = ρ ^ (N + 1) * gaussValue p F ρ w := by
    rw [show gaussValue p F ρ ((p : Ainf p F) ^ (N + 1) * w)
        = gaussVal p F hρ0 hρ1 ((p : Ainf p F) ^ (N + 1) * w) from
      (gaussVal_apply p F hρ0 hρ1 _).symm]
    rw [Valuation.map_mul, gaussVal_p_pow p F hρ0 hρ1 (N + 1),
      gaussVal_apply]
  rw [hmul]
  calc ρ ^ (N + 1) * gaussValue p F ρ w
      ≤ ρ ^ (N + 1) * 1 :=
        mul_le_mul_right (gaussValue_le_one p F hρ1.le w) _
    _ = ρ ^ (N + 1) := mul_one _

/-- Difference of `hatK`-components across an additive split. -/
theorem valued_BlocToHatK_sub_of_add {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (g t f : Bloc p F ϖ) (hf : f = g + t) :
    Valued.v (BlocToHatK p F ϖ hρ0 hρ1 g - BlocToHatK p F ϖ hρ0 hρ1 f)
      = wLoc p F ϖ hρ0 hρ1 t := by
  rw [hf, map_add]
  rw [show BlocToHatK p F ϖ hρ0 hρ1 g
      - (BlocToHatK p F ϖ hρ0 hρ1 g + BlocToHatK p F ϖ hρ0 hρ1 t)
    = -(BlocToHatK p F ϖ hρ0 hρ1 t) by ring]
  rw [Valuation.map_neg]
  exact valued_BlocToHatK p F ϖ t

include hρ₁1 hρ₂1 in
/-- Geometric two-radius epsilon: `max (c₁ρ₁^N) (c₂ρ₂^N) → 0`. -/
theorem tendsto_max_const_mul_pow (c₁ c₂ : NNReal) :
    Filter.Tendsto (fun N : ℕ => max (c₁ * ρ₁ ^ N) (c₂ * ρ₂ ^ N))
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun N : ℕ => c₁ * ρ₁ ^ N)
      Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₁1).const_mul c₁
    simpa using this
  have h2 : Filter.Tendsto (fun N : ℕ => c₂ * ρ₂ ^ N)
      Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₂1).const_mul c₂
    simpa using this
  have := h1.max h2
  simpa using this

/-- The completed plus-subring of the chart datum is closed: it is an open additive
subgroup, and open subgroups are closed. -/
private theorem isClosed_completedPlusSubring (a : ℕ) :
    IsClosed ((chartData p F ϖ 1 1 a 1).completedPlusSubring
      : Set (presheafValue (chartData p F ϖ 1 1 a 1))) := by
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have hopen : IsOpen
      ((chartData p F ϖ 1 1 a 1).completedPlusSubring
        : Set (presheafValue (chartData p F ϖ 1 1 a 1))) :=
    (RationalLocData.presheafValuePlus_isRingOfIntegralElements
      (A := Ainf p F) (chartData p F ϖ 1 1 a 1)).isOpen
  exact AddSubgroup.isClosed_of_isOpen
    (chartData p F ϖ 1 1 a 1).completedPlusSubring.toAddSubgroup hopen

/-- The Teichmüller heads converge to the element itself in `B^I`: at each radius the
tail after `N` is a constant times `ρ^N`. -/
private theorem tendsto_blocToBI_teichmuller_heads (x : Ainf p F) (k : ℕ)
    (w : ℕ → Ainf p F)
    (hsplit : ∀ N, IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)
      = (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          (sPow p F ϖ k))
        + IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ (N + 1) * w N)
            (sPow p F ϖ k)) :
    Filter.Tendsto
      (fun N => blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          (sPow p F ϖ k)))
      Filter.atTop
      (nhds (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)))) := by
  have hpair : ((BlocToHatK p F ϖ hρ₁0 hρ₁1
        (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)),
      BlocToHatK p F ϖ hρ₂0 hρ₂1
        (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)))
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
          (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)) :=
    Prod.ext (BIProd_fst p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 _).symm
      (BIProd_snd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 _).symm
  refine tendsto_subtype_rng.mpr ?_
  show Filter.Tendsto
    (fun N => BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
        ((p : Ainf p F) ^ i
          * WittVector.teichmuller p (teichCoeff p F x i))
        (sPow p F ϖ k)))
    Filter.atTop
    (nhds (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k))))
  rw [← hpair]
  refine tendsto_BIProd_of_valued_le p F ϖ
    (ε := fun N => max
      ((ρ₁ * (((ρ₁ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)⁻¹)) * ρ₁ ^ N)
      ((ρ₂ * (((ρ₂ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ k)⁻¹)) * ρ₂ ^ N))
    ?_ ?_
    (tendsto_max_const_mul_pow (hρ₁1 := hρ₁1) (hρ₂1 := hρ₂1) _ _)
  · intro N
    rw [valued_BlocToHatK_sub_of_add p F ϖ hρ₁0 hρ₁1 _ _ _ (hsplit N)]
    refine le_trans (wLoc_mk'_tail_le p F ϖ hρ₁0 hρ₁1 k N (w N))
      (le_trans (le_of_eq (by ring)) (le_max_left _ _))
  · intro N
    rw [valued_BlocToHatK_sub_of_add p F ϖ hρ₂0 hρ₂1 _ _ _ (hsplit N)]
    refine le_trans (wLoc_mk'_tail_le p F ϖ hρ₂0 hρ₂1 k N (w N))
      (le_trans (le_of_eq (by ring)) (le_max_right _ _))


/-- **The dense-level integrality theorem** (`b = 1`, Kedlaya Def 4.5):
`ChartDensePlus` holds at the exact window — every `Bloc` element bounded in
both window Gauss norms transports into the canonical plus subring, by the
Teichmüller head/tail split and the three-zone dispatch. -/
theorem chartDensePlus_of_exact (a : ℕ) (ha : 0 < a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ 1) :
    ChartDensePlus p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) a 1 ha one_pos ha hexact1 hexact2 := by
  intro h hw1 hw2
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (S := Bloc p F ϖ) h
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
  have hs : s = sPow p F ϖ k := Subtype.ext hk.symm
  subst hs
  -- per-coefficient bounds at the two radii
  have hb1 := gaussTerm_le_of_wLoc_mk'_le_one p F ϖ hρ₁0 hρ₁1 x k hw1
  have hb2 := gaussTerm_le_of_wLoc_mk'_le_one p F ϖ hρ₂0 hρ₂1 x k hw2
  -- Teichmüller truncation witnesses
  choose w hwspec using fun N =>
    WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  have hsplit : ∀ N, IsLocalization.mk' (Bloc p F ϖ) x (sPow p F ϖ k)
      = (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          (sPow p F ϖ k))
        + IsLocalization.mk' (Bloc p F ϖ) ((p : Ainf p F) ^ (N + 1) * w N)
            (sPow p F ϖ k) :=
    fun N => mk'_sPow_split p F ϖ x k N (w N) (hwspec N)
  -- the closed target
  have hclosed := isClosed_completedPlusSubring p F ϖ a
  -- memberships of the heads
  have hmem : ∀ N, (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha
      hexact1 hexact2).symm
      (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (∑ i ∈ Finset.Iic N, IsLocalization.mk' (Bloc p F ϖ)
          ((p : Ainf p F) ^ i
            * WittVector.teichmuller p (teichCoeff p F x i))
          (sPow p F ϖ k)))
      ∈ (chartData p F ϖ 1 1 a 1).completedPlusSubring := by
    intro N
    rw [map_sum (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1),
      map_sum ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha
        hexact1 hexact2).symm)]
    exact sum_mem fun i _ =>
      monomial_symm_blocToBI_mem_completedPlusSubring p F ϖ a ha
        hexact1 hexact2 k i (teichCoeff p F x i) (hb1 i) (hb2 i)
  have htend := tendsto_blocToBI_teichmuller_heads p F ϖ (hρ₁0 := hρ₁0)
    (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) x k w hsplit
  have hlim := ((presheafChartRingEquivBISub_symm_continuous p F ϖ
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
    a 1 ha one_pos ha hexact1 hexact2).tendsto _).comp htend
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)


/-! ### The plus reconciliation (the equality) -/

/-- **The plus reconciliation** (Kedlaya Definition 4.5, `b = 1`): the
transported `B^I`-unit ball **equals** the canonical completed plus subring of
the chart value. The two inclusions are the power-boundedness transport and
the dense-level integrality theorem. -/
theorem chartPlus_map_eq_completedPlusSubring (a : ℕ) (ha : 0 < a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ 1) :
    (BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map
        ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha
          hexact1 hexact2).symm.toRingHom)
      = (chartData p F ϖ 1 1 a 1).completedPlusSubring :=
  le_antisymm
    (chartPlus_le_completedPlusSubring_of_dense p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha
      hexact1 hexact2
      (chartDensePlus_of_exact p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a ha hexact1 hexact2))
    (completedPlusSubring_le_chartPlus p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a 1 ha one_pos ha
      hexact1 hexact2)

/-- The chart `VObj`'s plus structure is the canonical one (`PlusSubring`
form of the reconciliation). -/
theorem chartPlus_eq_canonical (a : ℕ) (ha : 0 < a)
    (hexact1 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ 1) :
    (chartPlus p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) a 1 ha one_pos ha hexact1 hexact2).toSubring
      = (chartData p F ϖ 1 1 a 1).completedPlusSubring :=
  chartPlus_map_eq_completedPlusSubring p F ϖ (hρ₁0 := hρ₁0)
    (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a ha hexact1 hexact2

end FarguesFontaine

end
