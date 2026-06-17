/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.MeasureR.Toolbox

/-!
# Fubini for measures over the integer ring of a field

The "one checks" of RJW Rem 3.11 (TeX 910) over `R := integerRing K`: the two
iterated integrals of a continuous `F : C(X × Y, R)` against measures on `X`
and `Y` agree. Proved exactly as in the `ℤ_p`-layer
`PadicLFunctions/Measure/Fubini.lean`: approximate the curried map by a
locally constant map (the general ultrametric approximation lemma), collapse
both iterated integrals of the approximation to the same finite sum, and
control the error by `‖μ‖, ‖ν‖ ≤ 1`.
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable section

namespace MeasureR

/-- The inner integral `x ↦ ∫ F(x, y) dν(y)`, as a continuous map. -/
def innerInt [CompactSpace Y] (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) :
    C(X, integerRing K) :=
  ⟨fun x => ν (F.curry x), (MeasureR.continuous ν).comp (map_continuous F.curry)⟩

variable {p K}

omit [CompleteSpace K] in
@[simp]
lemma innerInt_apply [CompactSpace Y] (ν : MeasureR K Y) (F : C(X × Y, integerRing K))
    (x : X) : innerInt K ν F x = ν (F.curry x) := rfl

omit [CompleteSpace K] in
@[simp]
lemma innerInt_add [CompactSpace Y] (ν : MeasureR K Y) (F G : C(X × Y, integerRing K)) :
    innerInt K ν (F + G) = innerInt K ν F + innerInt K ν G :=
  ContinuousMap.ext fun x => by
    simp [show (F + G).curry x = F.curry x + G.curry x from rfl]

omit [CompleteSpace K] in
@[simp]
lemma innerInt_smul [CompactSpace Y] (c : integerRing K) (ν : MeasureR K Y)
    (F : C(X × Y, integerRing K)) :
    innerInt K ν (c • F) = c • innerInt K ν F :=
  ContinuousMap.ext fun x => by
    simp [show (c • F).curry x = c • F.curry x from rfl]

omit [CompleteSpace K] in
@[simp]
lemma innerInt_measure_add [CompactSpace Y] (ν₁ ν₂ : MeasureR K Y)
    (F : C(X × Y, integerRing K)) :
    innerInt K (ν₁ + ν₂) F = innerInt K ν₁ F + innerInt K ν₂ F :=
  ContinuousMap.ext fun _x => rfl

omit [CompleteSpace K] in
@[simp]
lemma innerInt_measure_zero [CompactSpace Y] (F : C(X × Y, integerRing K)) :
    innerInt K (0 : MeasureR K Y) F = 0 :=
  ContinuousMap.ext fun _x => rfl

omit [CompleteSpace K] in
/-- **Fubini over `R`** (RJW Rem 3.11, TeX 910): the iterated integrals agree. -/
theorem integral_swap [CompactSpace X] [CompactSpace Y]
    (μ : MeasureR K X) (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) :
    μ (innerInt K ν F) =
      ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩)) := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨Φ, hΦ⟩ := PadicMeasure.exists_locallyConstant_norm_sub_le' F.curry hε
  classical
  set R : Finset C(Y, integerRing K) := Φ.range_finite.toFinset
  have hmemR : ∀ x : X, Φ x ∈ R := fun x =>
    Φ.range_finite.mem_toFinset.2 ⟨x, rfl⟩
  set S : integerRing K := ∑ g ∈ R,
    μ (charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g)) * ν g with hSdef
  -- pointwise collapse: at `x` only the `g = Φ x` term survives
  have hcollapse : ∀ (x : X) (w : C(Y, integerRing K) → integerRing K),
      (∑ g ∈ R, charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g) x * w g)
        = w (Φ x) := by
    intro x w
    rw [Finset.sum_eq_single (Φ x)]
    · rw [show charFnCM K X (Φ.isLocallyConstant.isClopen_fiber (Φ x)) x = 1 from by
        simp only [charFnCM_apply,
          Set.indicator_of_mem (show x ∈ {y | Φ.toFun y = Φ x} from rfl), Pi.one_apply],
        one_mul]
    · intro g _ hgx
      rw [show charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g) x = 0 from by
        simp only [charFnCM_apply, Set.indicator_of_notMem
          (show x ∉ {y | Φ.toFun y = g} from fun hc => hgx hc.symm)],
        zero_mul]
    · intro hx
      exact absurd (hmemR x) hx
  -- LHS ≈ S
  have hL : dist (μ (innerInt K ν F)) S ≤ ε := by
    set mid₁ : C(X, integerRing K) := ∑ g ∈ R,
      ν g • charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g) with hmid
    have hμmid : μ mid₁ = S := by
      rw [hmid, map_sum, hSdef]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hbound : ‖innerInt K ν F - mid₁‖ ≤ ε := by
      rw [ContinuousMap.norm_le _ hε.le]
      intro x
      have hmidx : mid₁ x = ν (Φ x) := by
        rw [hmid]
        calc (∑ g ∈ R, ν g • charFnCM K X
              (Φ.isLocallyConstant.isClopen_fiber g)) x
            = ∑ g ∈ R, charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g) x * ν g := by
              simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
                Pi.smul_apply, smul_eq_mul]
              exact Finset.sum_congr rfl fun g _ => mul_comm _ _
          _ = ν (Φ x) := hcollapse x ⇑ν
      rw [ContinuousMap.sub_apply, innerInt_apply, hmidx, ← map_sub]
      exact le_trans (norm_apply_le ν _) (hΦ x)
    calc dist (μ (innerInt K ν F)) S = ‖μ (innerInt K ν F) - μ mid₁‖ := by
          rw [dist_eq_norm, hμmid]
      _ = ‖μ (innerInt K ν F - mid₁)‖ := by rw [map_sub]
      _ ≤ ‖innerInt K ν F - mid₁‖ := norm_apply_le μ _
      _ ≤ ε := hbound
  -- RHS ≈ S
  have hR : dist (ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩))) S ≤ ε := by
    set mid₂ : C(Y, integerRing K) := ∑ g ∈ R,
      μ (charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g)) • g with hmid
    have hνmid : ν mid₂ = S := by
      rw [hmid, map_sum, hSdef]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, smul_eq_mul]
    have hbound : ‖innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂‖
        ≤ ε := by
      rw [ContinuousMap.norm_le _ hε.le]
      intro y
      set col : C(X, integerRing K) :=
        ⟨fun x => Φ x y, (continuous_eval_const y).comp Φ.continuous⟩ with hcol
      have hmidy : mid₂ y = μ col := by
        rw [hmid]
        have hcolsum : col = ∑ g ∈ R,
            g y • charFnCM K X (Φ.isLocallyConstant.isClopen_fiber g) := by
          ext x
          simp only [hcol, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
            ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          exact congrArg Subtype.val (((Finset.sum_congr rfl fun g _ => mul_comm _ _).trans
            (hcollapse x fun g => g y)).symm)
        rw [hcolsum, map_sum]
        simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
      rw [ContinuousMap.sub_apply, innerInt_apply, hmidy, ← map_sub]
      refine le_trans (norm_apply_le μ _) ?_
      rw [ContinuousMap.norm_le _ hε.le]
      intro x
      calc ‖((F.comp ⟨Prod.swap, continuous_swap⟩).curry y - col) x‖
          = ‖(F.curry x - Φ x) y‖ := by
            simp [hcol, ContinuousMap.sub_apply]
        _ ≤ ‖F.curry x - Φ x‖ := ContinuousMap.norm_coe_le_norm _ y
        _ ≤ ε := hΦ x
    calc dist (ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩))) S
        = ‖ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩)) - ν mid₂‖ := by
          rw [dist_eq_norm, hνmid]
      _ = ‖ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂)‖ := by
          rw [map_sub]
      _ ≤ ‖innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂‖ :=
          norm_apply_le ν _
      _ ≤ ε := hbound
  calc dist (μ (innerInt K ν F)) (ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩)))
      ≤ max (dist (μ (innerInt K ν F)) S)
          (dist S (ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩)))) :=
        dist_triangle_max _ _ _
    _ ≤ ε := max_le hL (by rwa [dist_comm] at hR)

end MeasureR

end

end PadicLFunctions
