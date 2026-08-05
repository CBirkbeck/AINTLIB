/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.SheafyBI
import «Adic spaces».FarguesFontaine.ChartData
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import «Adic spaces».RingEquivPresheafTransport
import «Adic spaces».SheafyRingEquivTransport

/-!
# The chart comparison map into `B^I` (ID2d, Kedlaya §4 / Wedhorn §8.1)

The finite-level comparison between the chart localization
`A_inf[1/(p[ϖ]^b)]` (with the Wedhorn rational-localization topology of the
chart datum) and the interval ring `B^I` at the exact chart interval
`I = [|ϖ|, |ϖ|^{b/a}]`:

* `FarguesFontaine.chartToBI` : the chart map corestricted to `B^I`;
* `FarguesFontaine.denseRange_chartToBI` : it has dense range (the closure of
  the image of `Bloc` is the definition of `B^I`);
* `FarguesFontaine.comap_nhds_zero_chartToBI` : the chart neighborhood filter
  is the comap of the `wI`-neighborhood filter (two-sided basis comparison:
  `exists_locNhd_le_ball` forward, `ball_le_locNhd` backward);
* `FarguesFontaine.isUniformInducing_chartToBI` : the chart map is uniformly
  inducing for the chart uniformity — the uniform-space heart of the
  identification `𝒪_Y(U) ≅ B^I`.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

/-- **`IsTateRing` transports along a bicontinuous ring equivalence.** -/
theorem isTateRing_congr {A B : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) [IsTateRing A] :
    IsTateRing B where
  exists_pairOfDefinition :=
    ⟨(IsHuberRing.exists_pairOfDefinition (A := A)).some.mapRingEquiv e he he'⟩
  exists_topologicallyNilpotent_unit := by
    obtain ⟨u, hu⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
    refine ⟨Units.map e.toRingHom.toMonoidHom u, ?_⟩
    have hfun : (fun n : ℕ =>
        ((Units.map e.toRingHom.toMonoidHom u : Bˣ) : B) ^ n)
        = fun n : ℕ => e ((u : A) ^ n) := by
      funext n
      rw [Units.coe_map, ← map_pow]
      rfl
    show Filter.Tendsto (fun n : ℕ =>
      ((Units.map e.toRingHom.toMonoidHom u : Bˣ) : B) ^ n) Filter.atTop (nhds 0)
    rw [hfun]
    have hcomp := (he.tendsto 0).comp hu
    rwa [map_zero] at hcomp

/-- The presheaf value is complete for the right uniformity of its additive
group (its canonical uniformity, rewritten). -/
theorem completeSpace_right_presheafValue {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (D : RationalLocData A) :
    @CompleteSpace (presheafValue D)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact inferInstance

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _

/-- The chart map lands in `B^I`. -/
theorem chartToBIProd_mem_BISub (b : ℕ) (hb : 0 < b)
    (z : Localization.Away (chartS p F ϖ 1 b)) :
    chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) b hb z
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 :=
  (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range.le_topologicalClosure
    ⟨blocEquivAwayChartS p F ϖ b hb z, rfl⟩

/-- **The chart map corestricted to `B^I`** (the finite-level comparison map). -/
noncomputable def chartToBI (b : ℕ) (hb : 0 < b) :
    Localization.Away (chartS p F ϖ 1 b)
      →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  (chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) b hb).codRestrict _
    (chartToBIProd_mem_BISub p F ϖ b hb)

@[simp]
theorem chartToBI_coe (b : ℕ) (hb : 0 < b)
    (z : Localization.Away (chartS p F ϖ 1 b)) :
    (↑(chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) b hb z)
      : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))
      = chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) b hb z := rfl

/-- **The chart map has dense range in `B^I`** (its closure is the definition of
`B^I`). -/
theorem denseRange_chartToBI (b : ℕ) (hb : 0 < b) :
    DenseRange (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) b hb) := by
  rw [DenseRange, dense_iff_closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have himg : (Subtype.val '' Set.range (chartToBI p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb))
      = Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
    ext w
    constructor
    · rintro ⟨-, ⟨z, rfl⟩, rfl⟩
      exact ⟨blocEquivAwayChartS p F ϖ b hb z, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) b hb ((blocEquivAwayChartS p F ϖ b hb).symm y),
        ⟨(blocEquivAwayChartS p F ϖ b hb).symm y, rfl⟩, by
          rw [chartToBI_coe]
          show BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
            (blocEquivAwayChartS p F ϖ b hb
              ((blocEquivAwayChartS p F ϖ b hb).symm y)) = _
          rw [RingEquiv.apply_symm_apply]⟩
  rw [himg]
  have hclos : closure (Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      = (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := rfl
  rw [hclos]
  ext w
  simp []


/-- The corestricted chart map is continuous at zero for the chart topology. -/
theorem tendsto_chartToBI (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Filter.Tendsto (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)
      (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0) := by
  rw [tendsto_subtype_rng]
  exact (tendsto_chartToBIProd_coe p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2).congr fun z => rfl

/-- The comap of the `B^I`-neighborhood filter along the chart map is at most the
chart-topology neighborhood filter (the reverse basis inclusion, filter form). -/
theorem comap_nhds_zero_chartToBI_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Filter.comap (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) (nhds 0)
      ≤ @nhds _ (chartTopology p F ϖ a b) 0 := by
  have hbasis : (@nhds _ (chartTopology p F ϖ a b) 0).HasBasis (fun _ : ℕ => True)
      (fun n => ((locNhd (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b) n
        : AddSubgroup (Localization.Away (chartS p F ϖ 1 b)))
        : Set (Localization.Away (chartS p F ϖ 1 b)))) := by
    show (@nhds _ ((chartData p F ϖ 1 b a b).topology) 0).HasBasis _ _
    exact (locBasis (podAinf p F ϖ) (chartT p F ϖ a b) (chartS p F ϖ 1 b)
      (chartData p F ϖ 1 b a b).hopen).hasBasis_nhds_zero
  refine hbasis.ge_iff.mpr fun n _ => ?_
  have hε : (0 : NNReal) < min ρ₁ ρ₂ ^ n * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
    have hπ0 : (0 : NNReal) < perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F) := hexact1 ▸ hρ₁0
    exact mul_pos (pow_pos (lt_min hρ₁0 hρ₂0) n) (pow_pos hπ0 b)
  refine Filter.mem_comap.mpr ⟨_, wI_ball_mem_nhds_BISub p F ϖ
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hε, ?_⟩
  intro z hz
  exact ball_le_locNhd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b n ha hb hexact1 hexact2 hz

/-- **The chart neighborhood filter is the comap of the `B^I` one** (two-sided
basis comparison, packaged). -/
theorem comap_nhds_zero_chartToBI (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Filter.comap (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) (nhds 0)
      = @nhds _ (chartTopology p F ϖ a b) 0 := by
  set vπ : NNReal :=
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hvπ
  have hπ1 : vπ ≤ ρ₁ := le_of_eq hexact1
  have hπ2 : vπ ≤ ρ₂ := by
    have hne : a * b ≠ 0 := by positivity
    refine le_of_pow_le_pow_left₀ hne zero_le ?_
    calc vπ ^ (a * b) ≤ vπ ^ (b * b) :=
          pow_le_pow_of_le_one zero_le (hexact1 ▸ hρ₁1.le)
            (Nat.mul_le_mul_right b hab)
      _ = (vπ ^ b) ^ b := by rw [← pow_mul]
      _ = (ρ₂ ^ a) ^ b := by rw [hexact2]
      _ = ρ₂ ^ (a * b) := by rw [← pow_mul]
  have hr1 : ρ₁ ^ a ≤ vπ ^ b := by
    rw [← hexact1]
    exact pow_le_pow_of_le_one zero_le (hexact1 ▸ hρ₁1.le) hab
  have hr2 : ρ₂ ^ a ≤ vπ ^ b := le_of_eq hexact2
  exact le_antisymm
    (comap_nhds_zero_chartToBI_le p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hexact1 hexact2)
    (Filter.tendsto_iff_comap.mp (tendsto_chartToBI p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2))

/-- **The chart map is (topologically) inducing** for the chart topology. -/
theorem isInducing_chartToBI (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    @Topology.IsInducing _ _ (chartTopology p F ϖ a b) _
      (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) := by
  letI : TopologicalSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartTopology p F ϖ a b
  refine ⟨IsTopologicalAddGroup.ext ?_ ?_ ?_⟩
  · exact @IsTopologicalRing.to_topologicalAddGroup _ _ (chartTopology p F ϖ a b)
      (chartTopologicalRing p F ϖ a b)
  · exact topologicalAddGroup_induced
      (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)
  · rw [@nhds_induced, map_zero,
      comap_nhds_zero_chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2]

/-- **The chart map is uniformly inducing** for the chart uniformity. -/
theorem isUniformInducing_chartToBI (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    @IsUniformInducing _ _ (chartUniformity p F ϖ a b) _
      (chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb) := by
  letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartUniformity p F ϖ a b
  have : IsUniformAddGroup (Localization.Away (chartS p F ϖ 1 b)) :=
    chartIsUniformAddGroup p F ϖ a b
  have : IsUniformAddGroup ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    isUniformAddGroup_BISub p F ϖ
  exact AddMonoidHom.isUniformInducing_of_isInducing
    (isInducing_chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2)

/-- The range of the chart map is the range of the diagonal `Bloc`-map. -/
theorem range_chartToBIProd (b : ℕ) (hb : 0 < b) :
    Set.range (⇑(chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb))
      = Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨blocEquivAwayChartS p F ϖ b hb z, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(blocEquivAwayChartS p F ϖ b hb).symm y, ?_⟩
    show BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (blocEquivAwayChartS p F ϖ b hb
        ((blocEquivAwayChartS p F ϖ b hb).symm y)) = _
    rw [RingEquiv.apply_symm_apply]

/-- The completion-level chart map lands in `B^I`. -/
theorem presheafChartToBIProd_mem_BISub (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (x : presheafValue (chartData p F ϖ 1 b a b)) :
    presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2 x
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartUniformity p F ϖ a b
  have hx : x ∈ closure (Set.range (⇑((chartData p F ϖ 1 b a b).coeRingHom))) := by
    have hdense : DenseRange (⇑((chartData p F ϖ 1 b a b).coeRingHom)) :=
      @UniformSpace.Completion.denseRange_coe _ (chartData p F ϖ 1 b a b).uniformSpace
    rw [hdense.closure_range]
    trivial
  have hcont : Continuous (presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2) :=
    UniformSpace.Completion.continuous_extension
  have himg := image_closure_subset_closure_image
    (f := ⇑(presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2))
    (s := Set.range (⇑((chartData p F ϖ 1 b a b).coeRingHom))) hcont
  have hmem := himg ⟨x, hx, rfl⟩
  have hcomp : (⇑(presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2))
        '' (Set.range (⇑((chartData p F ϖ 1 b a b).coeRingHom)))
      = Set.range (⇑(chartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb)) := by
    rw [← Set.range_comp]
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, (presheafChartToBIProd_coe p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2 z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (presheafChartToBIProd_coe p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2 z)⟩
  rw [hcomp, range_chartToBIProd p F ϖ b hb] at hmem
  exact hmem


include hρ₁0 hρ₁1 hρ₂0 hρ₂1 in
/-- **`B^I` as an abstract completion of the chart localization** (at the exact
chart interval). -/
noncomputable def chartBIPkg (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    @AbstractCompletion (Localization.Away (chartS p F ϖ 1 b))
      (chartUniformity p F ϖ a b) :=
  letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) :=
    chartUniformity p F ϖ a b
  { space := ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    coe := chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) b hb
    uniformStruct := inferInstance
    complete := (isComplete_BISub p F ϖ).completeSpace_coe
    separation := inferInstance
    isUniformInducing := isUniformInducing_chartToBI p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
    dense := denseRange_chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) b hb }

/-- **The uniform equivalence** `A_inf⟨T/s⟩ ≃ᵤ B^I` from the two abstract
completions of the chart localization. -/
noncomputable def chartCompletionUniformEquiv (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    presheafValue (chartData p F ϖ 1 b a b)
      ≃ᵤ ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  @AbstractCompletion.compareEquiv _ (chartUniformity p F ϖ a b)
    (@UniformSpace.Completion.cPkg _ (chartUniformity p F ϖ a b))
    (chartBIPkg p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2)


include hρ₁1 in
/-- At the exact chart interval, `|ϖ| ≤ ρ₂`. -/
theorem vpi_le_rho2_of_exact (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂ := by
  set vπ : NNReal :=
    perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hvπ
  have hne : a * b ≠ 0 := by positivity
  refine le_of_pow_le_pow_left₀ hne zero_le ?_
  calc vπ ^ (a * b) ≤ vπ ^ (b * b) :=
        pow_le_pow_of_le_one zero_le (hexact1 ▸ hρ₁1.le)
          (Nat.mul_le_mul_right b hab)
    _ = (vπ ^ b) ^ b := by rw [← pow_mul]
    _ = (ρ₂ ^ a) ^ b := by rw [hexact2]
    _ = ρ₂ ^ (a * b) := by rw [← pow_mul]

include hρ₁1 in
/-- At the exact chart interval, `ρ₁^a ≤ |ϖ|^b`. -/
theorem rho1_pow_le_of_exact (a b : ℕ) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁) :
    ρ₁ ^ a ≤ perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
  rw [← hexact1]
  exact pow_le_pow_of_le_one zero_le (hexact1 ▸ hρ₁1.le) hab

/-- **The completion-level chart map corestricted to `B^I`.** -/
noncomputable def presheafChartToBI (a b : ℕ) (hb : 0 < b)
    (hπ1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₁)
    (hπ2 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≤ ρ₂)
    (hr1 : ρ₁ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b)
    (hr2 : ρ₂ ^ a ≤ perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    presheafValue (chartData p F ϖ 1 b a b)
      →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  (presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2).codRestrict _
    (presheafChartToBIProd_mem_BISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb hπ1 hπ2 hr1 hr2)

/-- The corestricted completion-level chart map agrees with the abstract
comparison equivalence. -/
theorem presheafChartToBI_eq_compare (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    ⇑(presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) a b hb (le_of_eq hexact1)
        (vpi_le_rho2_of_exact p F ϖ (hρ₁1 := hρ₁1) a b ha hb hab hexact1 hexact2)
        (rho1_pow_le_of_exact p F ϖ (hρ₁1 := hρ₁1) a b hab hexact1)
        (le_of_eq hexact2))
      = ⇑(chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2) := by
  have hdense : DenseRange (⇑((chartData p F ϖ 1 b a b).coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ (chartData p F ϖ 1 b a b).uniformSpace
  refine hdense.equalizer ?_ ?_ (funext fun z => ?_)
  · exact Continuous.subtype_mk
      (@UniformSpace.Completion.continuous_extension _
        (chartData p F ϖ 1 b a b).uniformSpace _ _ _ _) _
  · exact (chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).continuous
  · apply Subtype.ext
    show presheafChartToBIProd p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb _ _ _ _
        ((chartData p F ϖ 1 b a b).coeRingHom z)
      = ↑((chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2)
        ((chartData p F ϖ 1 b a b).coeRingHom z))
    have hL := presheafChartToBIProd_coe p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb (le_of_eq hexact1)
      (vpi_le_rho2_of_exact p F ϖ (hρ₁1 := hρ₁1) a b ha hb hab hexact1 hexact2)
      (rho1_pow_le_of_exact p F ϖ (hρ₁1 := hρ₁1) a b hab hexact1)
      (le_of_eq hexact2) z
    have hcmp : (chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2)
        ((chartData p F ϖ 1 b a b).coeRingHom z)
        = chartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
            (hρ₂1 := hρ₂1) b hb z :=
      @AbstractCompletion.compare_coe _ (chartUniformity p F ϖ a b)
        (@UniformSpace.Completion.cPkg _ (chartUniformity p F ϖ a b))
        (chartBIPkg p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2) z
    rw [hL, hcmp]
    exact (chartToBI_coe p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) b hb z).symm


include hρ₁0 hρ₂0 in
/-- **ID2d — the comparison theorem**: the presheaf value of the chart datum is
canonically ring-isomorphic to `B^I` at the exact chart interval
(`𝒪_Y(U) ≅ B^I`, Kedlaya Lemma 4.9 case 3 over the `A_inf`-base). -/
noncomputable def presheafChartRingEquivBISub (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    presheafValue (chartData p F ϖ 1 b a b)
      ≃+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  toFun := presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) a b hb (le_of_eq hexact1)
    (vpi_le_rho2_of_exact p F ϖ (hρ₁1 := hρ₁1) a b ha hb hab hexact1 hexact2)
    (rho1_pow_le_of_exact p F ϖ (hρ₁1 := hρ₁1) a b hab hexact1)
    (le_of_eq hexact2)
  invFun := ⇑(chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
  left_inv x := by
    have h := congrFun (presheafChartToBI_eq_compare p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2) x
    show (chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm _ = x
    rw [h]
    exact UniformEquiv.symm_apply_apply _ x
  right_inv y := by
    have h := congrFun (presheafChartToBI_eq_compare p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
      ((chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
        (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm y)
    show presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) a b hb _ _ _ _ _ = y
    rw [h]
    exact UniformEquiv.apply_symm_apply _ y
  map_mul' x y := map_mul (presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb _ _ _ _) x y
  map_add' x y := map_add (presheafChartToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b hb _ _ _ _) x y

/-- The comparison equivalence is continuous. -/
theorem presheafChartRingEquivBISub_continuous (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Continuous (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2) :=
  Continuous.subtype_mk
    (@UniformSpace.Completion.continuous_extension _
      (chartData p F ϖ 1 b a b).uniformSpace _ _ _ _) _

/-- The inverse of the comparison equivalence is continuous. -/
theorem presheafChartRingEquivBISub_symm_continuous (a b : ℕ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    Continuous (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm :=
  (chartCompletionUniformEquiv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm.continuous

include hρ₁0 hρ₂0 in
/-- **ID2e — the chart presheaf value is sheafy**: transporting
`isSheafy_BISub` through the comparison isomorphism `𝒪_Y(U) ≅ B^I` at the
exact chart interval. The plus subring is the transported `B^{I,+}`-candidate
(the integral closure statement of §5 is not needed). -/
theorem isSheafy_presheafChart (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    letI : ValuationSpectrum.PlusSubring (presheafValue (chartData p F ϖ 1 b a b)) :=
      ⟨(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map
        ((presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
          hexact1 hexact2).symm.toRingHom)⟩
    letI : IsHuberRing (presheafValue (chartData p F ϖ 1 b a b)) :=
      (isTateRing_congr (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0)
        (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
        hexact1 hexact2).symm
        (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
          (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
          hexact1 hexact2)
        (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
          (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
          hexact1 hexact2)).toIsHuberRing
    letI : @CompleteSpace (presheafValue (chartData p F ϖ 1 b a b))
        (IsTopologicalAddGroup.rightUniformSpace
          (presheafValue (chartData p F ϖ 1 b a b))) :=
      completeSpace_right_presheafValue (chartData p F ϖ 1 b a b)
    letI : IsRingOfIntegralElements
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
    ValuationSpectrum.IsSheafy (presheafValue (chartData p F ϖ 1 b a b)) := by
  set e : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      ≃+* presheafValue (chartData p F ϖ 1 b a b) :=
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
    with hedef
  have he : Continuous e :=
    presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  have he' : Continuous e.symm :=
    presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2
  -- the A-side instance package
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
  -- sheafiness of `B^I` at `j = n = 1`
  have h12 : ρ₁ ≤ ρ₂ := hexact1 ▸ vpi_le_rho2_of_exact p F ϖ (hρ₁1 := hρ₁1)
    a b ha hb hab hexact1 hexact2
  have hexact' : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (1 * 1) = ρ₁ := by
    rw [one_mul, pow_one]
    exact hexact1
  have hbb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ 1) 1)) ≤ 1 := by
    refine wI_teichPowOverP_le_one p F ϖ h12 ?_
    rw [perfectoidValuation_pow_toOF p F ϖ]
    exact le_of_eq hexact'
  have : ValuationSpectrum.IsSheafy ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    isSheafy_BISub p F ϖ h12 1 1 (BIProd_mem_BISub p F ϖ _) hbb hexact'
  have : IsTateRing (presheafValue (chartData p F ϖ 1 b a b)) :=
    isTateRing_congr e he he'
  letI : ValuationSpectrum.PlusSubring (presheafValue (chartData p F ϖ 1 b a b)) :=
    ⟨(BIPlusIn p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).map e.toRingHom⟩
  letI : @CompleteSpace (presheafValue (chartData p F ϖ 1 b a b))
      (IsTopologicalAddGroup.rightUniformSpace
        (presheafValue (chartData p F ϖ 1 b a b))) :=
    completeSpace_right_presheafValue (chartData p F ϖ 1 b a b)
  letI : IsRingOfIntegralElements
      (ValuationSpectrum.ringPlus (presheafValue (chartData p F ϖ 1 b a b))
        : Subring (presheafValue (chartData p F ϖ 1 b a b))) :=
    (isRingOfIntegralElements_BIPlusIn p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)).map e he he'
  exact ValuationSpectrum.isSheafy_mapRingEquiv e he he' rfl

/-- The right endpoint of the `U₀`-chart interval: `|ϖ|^{b/a}` as an `NNReal`
power. -/
noncomputable def rhoRight (a b : ℕ) : NNReal :=
  perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
    ^ ((b : ℝ) / (a : ℝ))

theorem vpi_pos :
    0 < perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
  refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
  exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)

theorem rhoRight_pos (a b : ℕ) : 0 < rhoRight p F ϖ a b := by
  rw [rhoRight]
  exact NNReal.rpow_pos (vpi_pos p F ϖ)

theorem rhoRight_lt_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    rhoRight p F ϖ a b < 1 := by
  rw [rhoRight]
  refine NNReal.rpow_lt_one (perfectoidValuation_toOF_lt_one p F ϖ) ?_
  have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  positivity

/-- The exactness equation `ρ₂^a = |ϖ|^b` for the rpow right endpoint. -/
theorem rhoRight_pow_exact (a b : ℕ) (ha : 0 < a) :
    rhoRight p F ϖ a b ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
  rw [rhoRight, ← NNReal.rpow_natCast (_ ^ ((b : ℝ) / (a : ℝ))) a,
    ← NNReal.rpow_mul, div_mul_cancel₀, NNReal.rpow_natCast]
  exact_mod_cast ha.ne'


/-- Two is at most `p + 1` for a prime `p`. -/
theorem two_le_p_add_one : 2 ≤ p + 1 := by
  have := Nat.Prime.two_le (Fact.out : Nat.Prime p)
  omega

end FarguesFontaine

end
