/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.Measure.UnitsZp
import PadicLFunctions.MeasureR.Toolbox

/-!
# Measures on the units over the integer ring of a field

RJW Rem 3.33 over `R := integerRing K`: the embedding
`ι : Λ_R(ℤ_p^×) → Λ_R(ℤ_p)` (pushforward along the unit inclusion), its
injectivity via extension by zero, and the identification of its image with
`ker ψ` (Cor 3.32). The units-geometry instances (`CompactSpace ℤ_[p]ˣ`,
total disconnectedness, `unitsValCM`, `unitsHomeo`) are coefficient-free and
reused from `PadicLFunctions/Measure/UnitsZp.lean`.
-/

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

namespace MeasureR

open Classical in
/-- Extension by zero: a continuous `R`-valued function on `ℤ_p^×` extends to
`ℤ_p` by `0` outside the clopen set of units. -/
def extendByZero : C(ℤ_[p]ˣ, integerRing K) →ₗ[integerRing K] C(ℤ_[p], integerRing K) where
  toFun g :=
    ⟨fun x => if h : IsUnit x then g h.unit else 0, by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : IsUnit x
      · refine ContinuousOn.continuousAt ?_
          ((PadicMeasure.isClopen_units p).isOpen.mem_nhds hx)
        rw [continuousOn_iff_continuous_restrict]
        have hres : Set.restrict {x : ℤ_[p] | IsUnit x}
              (fun x => if h : IsUnit x then g h.unit else 0)
            = ⇑g ∘ ⇑(PadicMeasure.unitsHomeo p).symm := by
          funext y
          rcases y with ⟨y, hy⟩
          have hy' : IsUnit y := hy
          simp only [Set.restrict_apply, Function.comp_apply, dif_pos hy']
          rfl
        rw [hres]
        exact (map_continuous g).comp (PadicMeasure.unitsHomeo p).symm.continuous
      · refine ContinuousOn.continuousAt ?_
          (((PadicMeasure.isClopen_units p).compl.isOpen).mem_nhds (by simpa using hx))
        refine ContinuousOn.congr (continuousOn_const (c := (0 : integerRing K)))
          (fun y hy => ?_)
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
        simp [dif_neg hy]⟩
  map_add' g₁ g₂ := by
    ext x
    by_cases hx : IsUnit x <;>
      simp [hx]
  map_smul' c g := by
    ext x
    by_cases hx : IsUnit x <;>
      simp [hx]

variable {p K}

open Classical in
omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
@[simp]
lemma extendByZero_coe_unit (g : C(ℤ_[p]ˣ, integerRing K)) (u : ℤ_[p]ˣ) :
    extendByZero p K g (u : ℤ_[p]) = g u := by
  have hx : IsUnit ((u : ℤ_[p])) := u.isUnit
  change (if h : IsUnit ((u : ℤ_[p])) then g h.unit else 0) = g u
  rw [dif_pos hx]
  congr 1
  exact Units.ext (IsUnit.unit_spec hx)

variable (p K)

/-- The embedding `ι : Λ_R(ℤ_p^×) → Λ_R(ℤ_p)` (RJW Rem 3.33, TeX 1170–1171). -/
def iota : MeasureR K ℤ_[p]ˣ →ₗ[integerRing K] MeasureR K ℤ_[p] :=
  pushforward K ℤ_[p]ˣ ℤ_[p] (PadicMeasure.unitsValCM p)

variable {p K}

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- Restriction of the zero-extension recovers the original function. -/
lemma extendByZero_comp_val (g : C(ℤ_[p]ˣ, integerRing K)) :
    (extendByZero p K g).comp (PadicMeasure.unitsValCM p) = g :=
  ContinuousMap.ext fun u => extendByZero_coe_unit g u

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `ι` is injective (RJW Rem 3.33: "we can identify `Λ(ℤ_p^×)` with its
image"). -/
theorem iota_injective : Function.Injective (iota p K) := by
  intro μ ν h
  refine LinearMap.ext fun g => ?_
  have happ := LinearMap.congr_fun h (extendByZero p K g)
  simpa only [iota, pushforward_apply, extendByZero_comp_val] using happ

omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- `Res_{ℤ_p^×} ∘ ι = ι` (RJW Rem 3.33). -/
theorem res_iota (μ : MeasureR K ℤ_[p]ˣ) :
    res p K (PadicMeasure.isClopen_units p) (iota p K μ) = iota p K μ := by
  refine LinearMap.ext fun f => ?_
  change μ ((charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f).comp
      (PadicMeasure.unitsValCM p)) = μ (f.comp (PadicMeasure.unitsValCM p))
  congr 1
  ext u
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply, charFnCM_apply,
    
    PadicMeasure.unitsValCM, ContinuousMap.coe_mk]
  rw [Set.indicator_of_mem (show ((u : ℤ_[p])) ∈ {x : ℤ_[p] | IsUnit x} from u.isUnit),
    Pi.one_apply, one_mul]

open Classical in
omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K] in
/-- Zero-extension of a restriction is cutting by the unit indicator. -/
lemma extendByZero_comp_unitsVal (f : C(ℤ_[p], integerRing K)) :
    extendByZero p K (f.comp (PadicMeasure.unitsValCM p))
      = charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f := by
  ext x
  refine congrArg Subtype.val ?_
  change (if h : IsUnit x then (f.comp (PadicMeasure.unitsValCM p)) h.unit else 0) = _
  by_cases hx : IsUnit x
  · rw [dif_pos hx]
    simp only [ContinuousMap.comp_apply, PadicMeasure.unitsValCM, ContinuousMap.coe_mk,
      ContinuousMap.mul_apply, charFnCM_apply, 
      ]
    rw [Set.indicator_of_mem (show x ∈ {y : ℤ_[p] | IsUnit y} from hx), Pi.one_apply,
      one_mul, IsUnit.unit_spec]
  · rw [dif_neg hx]
    simp only [ContinuousMap.mul_apply, charFnCM_apply, 
      ]
    rw [Set.indicator_of_notMem (show x ∉ {y : ℤ_[p] | IsUnit y} from hx), zero_mul]

/-- **The image of `ι` is `ker ψ`** (RJW Rem 3.33, TeX 1171–1172). -/
theorem mem_range_iota_iff (μ : MeasureR K ℤ_[p]) :
    μ ∈ Set.range (iota p K) ↔ psi p K μ = 0 := by
  constructor
  · rintro ⟨ν, rfl⟩
    rw [← isSupportedOn_units_iff_psi_eq_zero]
    exact res_iota ν
  · intro h
    refine ⟨μ.comp (extendByZero p K), ?_⟩
    refine LinearMap.ext fun f => ?_
    change μ (extendByZero p K (f.comp (PadicMeasure.unitsValCM p))) = μ f
    rw [extendByZero_comp_unitsVal]
    exact LinearMap.congr_fun ((isSupportedOn_units_iff_psi_eq_zero μ).2 h) f

end MeasureR

end

end PadicLFunctions
