import PadicLFunctions.Measure.Toolbox
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Measures on ℤ_p^×

RJW (arXiv:2309.15692) §3.5.4–3.5.5: the space `Λ(ℤ_p^×) = ℳ(ℤ_p^×, ℤ_p)` of measures
on the units, its embedding `ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p)`, and the identification of its
image with `ker ψ` (RJW Rem. 3.33, `not subalgebra`, TeX lines 1169–1176).

We work with the units type `ℤ_[p]ˣ` (with its standard topology from
`Topology.Algebra.Constructions`); the coercion `Units.val` is a closed embedding with
clopen range `{x | IsUnit x} = {x | ‖x‖ = 1}`.
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

private lemma isClosed_range_embedProduct :
    IsClosed (Set.range (Units.embedProduct ℤ_[p])) := by
  have hrange : Set.range (Units.embedProduct ℤ_[p])
      = {q : ℤ_[p] × ℤ_[p]ᵐᵒᵖ | q.1 * q.2.unop = 1} ∩
        {q : ℤ_[p] × ℤ_[p]ᵐᵒᵖ | q.2.unop * q.1 = 1} := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.mul_inv, u.inv_mul⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨q.1, q.2.unop, h1, h2⟩, by
        simp only [Units.embedProduct_apply]
        exact Prod.ext rfl (MulOpposite.unop_injective rfl)⟩
  rw [hrange]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
      continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst)
      continuous_const)

/-- `ℤ_[p]ˣ` is compact: it embeds as a closed subset of `ℤ_[p] × ℤ_[p]ᵐᵒᵖ`. Not in
mathlib (verified absent). -/
instance : CompactSpace ℤ_[p]ˣ := by
  refine ⟨(Units.isEmbedding_embedProduct.isCompact_iff).2 ?_⟩
  rw [Set.image_univ]
  exact (isClosed_range_embedProduct p).isCompact

instance : TotallyDisconnectedSpace ℤ_[p]ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph (M := ℤ_[p])).symm.isEmbedding.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- `ℤ_[p]ˣ` is totally disconnected (inherited through the embedding). -/
instance : TotallyDisconnectedSpace ℤ_[p]ˣ :=
  Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The coercion `ℤ_[p]ˣ → ℤ_[p]` as a continuous map. -/
def unitsValCM : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨fun u => (u : ℤ_[p]), Units.continuous_val⟩

/-- `ℤ_[p]ˣ` is homeomorphic to the (clopen) set of units of `ℤ_[p]`: a continuous
bijection from a compact space to a Hausdorff space is a homeomorphism. -/
noncomputable def unitsHomeo : ℤ_[p]ˣ ≃ₜ {x : ℤ_[p] | IsUnit x} :=
  Continuous.homeoOfEquivCompactToT2
    (f := { toFun := fun u => ⟨(u : ℤ_[p]), u.isUnit⟩
            invFun := fun y => y.2.unit
            left_inv := fun u => Units.ext (IsUnit.unit_spec u.isUnit)
            right_inv := fun y => Subtype.ext (IsUnit.unit_spec y.2) })
    (Units.continuous_val.subtype_mk _)

open Classical in
/-- Extension by zero: a continuous function on `ℤ_p^×` extends to `ℤ_p` by `0` outside
the (clopen) units. Auxiliary for surjectivity of restriction and injectivity of `ι`. -/
noncomputable def extendByZero : C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] C(ℤ_[p], ℤ_[p]) where
  toFun g :=
    ⟨fun x => if h : IsUnit x then g h.unit else 0, by
      rw [continuous_iff_continuousAt]
      intro x
      by_cases hx : IsUnit x
      · refine ContinuousOn.continuousAt ?_ ((isClopen_units p).isOpen.mem_nhds hx)
        rw [continuousOn_iff_continuous_restrict]
        have hres : Set.restrict {x : ℤ_[p] | IsUnit x}
              (fun x => if h : IsUnit x then g h.unit else 0)
            = ⇑g ∘ ⇑(unitsHomeo p).symm := by
          funext y
          rcases y with ⟨y, hy⟩
          have hy' : IsUnit y := hy
          simp only [Set.restrict_apply, Function.comp_apply, dif_pos hy']
          rfl
        rw [hres]
        exact (map_continuous g).comp (unitsHomeo p).symm.continuous
      · refine ContinuousOn.continuousAt ?_
          (((isClopen_units p).compl.isOpen).mem_nhds (by simpa using hx))
        refine ContinuousOn.congr (continuousOn_const (c := (0 : ℤ_[p]))) (fun y hy => ?_)
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

open Classical in
@[simp]
lemma extendByZero_coe_unit (g : C(ℤ_[p]ˣ, ℤ_[p])) (u : ℤ_[p]ˣ) :
    extendByZero p g (u : ℤ_[p]) = g u := by
  have hx : IsUnit ((u : ℤ_[p])) := u.isUnit
  change (if h : IsUnit ((u : ℤ_[p])) then g h.unit else 0) = g u
  rw [dif_pos hx]
  exact congrArg g (Units.ext (IsUnit.unit_spec hx))

/-- The embedding `ι : Λ(ℤ_p^×) → Λ(ℤ_p)`:
`∫_{ℤ_p} φ d(ιμ) = ∫_{ℤ_p^×} φ|_{ℤ_p^×} dμ`.

Source: RJW Rem. 3.33 (TeX lines 1170–1171). -/
noncomputable def iota : PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p] :=
  pushforward p (unitsValCM p)

/-- Restriction of the zero-extension recovers the original function. -/
lemma extendByZero_comp_val (g : C(ℤ_[p]ˣ, ℤ_[p])) :
    (extendByZero p g).comp (unitsValCM p) = g :=
  ContinuousMap.ext (extendByZero_coe_unit p g)

/-- `ι` is injective (restriction `C(ℤ_p, ℤ_p) → C(ℤ_p^×, ℤ_p)` is surjective, via
extension by zero). Source: RJW Rem. 3.33: "we can identify `Λ(ℤ_p^×)` with its
image". -/
theorem iota_injective : Function.Injective (iota p) := by
  intro μ ν h
  refine LinearMap.ext fun g => ?_
  simpa only [iota, pushforward_apply, extendByZero_comp_val] using
    LinearMap.congr_fun h (extendByZero p g)

/-- `Res_{ℤ_p^×} ∘ ι = ι`: the image of `ι` consists of measures supported on the
units. Source: RJW Rem. 3.33 ("`Res_{ℤ_p^×} ∘ ι` is the identity on `Λ(ℤ_p^×)`"). -/
theorem res_iota (μ : PadicMeasure p ℤ_[p]ˣ) :
    res p (isClopen_units p) (iota p μ) = iota p μ := by
  refine LinearMap.ext fun f => ?_
  change μ ((((LocallyConstant.charFn ℤ_[p] (isClopen_units p) : C(ℤ_[p], ℤ_[p])) * f)).comp
      (unitsValCM p)) = μ (f.comp (unitsValCM p))
  congr 1
  ext u
  simp only [ContinuousMap.comp_apply, ContinuousMap.mul_apply,
    LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn, unitsValCM,
    ContinuousMap.coe_mk,
    Set.indicator_of_mem (show ((u : ℤ_[p])) ∈ {x : ℤ_[p] | IsUnit x} from u.isUnit),
    Pi.one_apply, one_mul]

open Classical in
/-- Zero-extension of a restriction is cutting by the unit indicator. -/
lemma extendByZero_comp_unitsVal (f : C(ℤ_[p], ℤ_[p])) :
    extendByZero p (f.comp (unitsValCM p))
      = (LocallyConstant.charFn ℤ_[p] (isClopen_units p) : C(ℤ_[p], ℤ_[p])) * f := by
  ext x
  change (if h : IsUnit x then (f.comp (unitsValCM p)) h.unit else 0) = _
  by_cases hx : IsUnit x
  · simp only [dif_pos hx, ContinuousMap.comp_apply, unitsValCM, ContinuousMap.coe_mk,
      ContinuousMap.mul_apply, LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn,
      Set.indicator_of_mem (show x ∈ {y : ℤ_[p] | IsUnit y} from hx), Pi.one_apply, one_mul,
      IsUnit.unit_spec]
  · simp only [dif_neg hx, ContinuousMap.mul_apply, LocallyConstant.coe_continuousMap,
      LocallyConstant.coe_charFn,
      Set.indicator_of_notMem (show x ∉ {y : ℤ_[p] | IsUnit y} from hx), zero_mul]

/-- **The image of `ι` is `ker ψ`**: `μ ∈ range ι ↔ ψ(μ) = 0`.

Source: RJW Rem. 3.33 (TeX lines 1171–1172): "By Corollary 3.32, a measure
`μ ∈ Λ(ℤ_p)` lies in `Λ(ℤ_p^×)` if and only if `ψ(μ) = 0`." -/
theorem mem_range_iota_iff (μ : PadicMeasure p ℤ_[p]) :
    μ ∈ Set.range (iota p) ↔ psi p μ = 0 := by
  constructor
  · rintro ⟨ν, rfl⟩
    rw [← isSupportedOn_units_iff_psi_eq_zero]
    exact res_iota p ν
  · intro h
    refine ⟨μ.comp (extendByZero p), ?_⟩
    refine LinearMap.ext fun f => ?_
    change μ (extendByZero p (f.comp (unitsValCM p))) = μ f
    rw [extendByZero_comp_unitsVal]
    exact LinearMap.congr_fun ((isSupportedOn_units_iff_psi_eq_zero p μ).2 h) f

end PadicMeasure
