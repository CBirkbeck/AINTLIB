import PadicLFunctions.Measure.PseudoMeasure
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The measure algebra of a product with a finite factor  (CARRIER-BRIDGE step 2)

Let `Δ` be a *finite* commutative group (with the discrete topology) and `Y` a compact
commutative topological monoid.  This file proves the ring isomorphism

  `PadicMeasure p (Δ × Y)  ≃+*  MonoidAlgebra (PadicMeasure p Y) Δ`,

i.e. the measure algebra of the product `Δ × Y` is the group algebra over the measure
algebra of `Y` of the finite group `Δ`.  In the carrier bridge
`PadicMeasure(𝒢⁺) ≅ IwasawaAlgebraGroup`, `Δ` is the torsion part and `Y` the pro-cyclic
part of `𝒢⁺`.

The mathematics is the "slice" decomposition: because `Δ` is finite and discrete, a
continuous `g : Δ × Y → ℤ_p` is the same data as the `Δ`-indexed tuple of its slices
`g(δ, ·) : Y → ℤ_p` (`continuous_prod_of_discrete_left`).  Dualising and using that `Δ`
is finite, a measure on `Δ × Y` is the same data as a `Δ`-indexed tuple of measures on
`Y`, i.e. an element of `MonoidAlgebra (PadicMeasure p Y) Δ = (Δ →₀ PadicMeasure p Y)`.
The forward map sends `μ` to `∑_δ [δ] · μ_δ`, where the coefficient measure `μ_δ` is
`f ↦ μ (slice δ f)`.  The ring structures match because the convolution on
`PadicMeasure p (Δ × Y)` comes from the *product* monoid structure
`(δ, y)·(δ', y') = (δ·δ', y·y')`, which on group-algebra coordinates is exactly the
convolution of `MonoidAlgebra` on `Δ` with coefficient-convolution in `PadicMeasure p Y`.

## Main declarations

* `PadicMeasure.slice`: the inclusion `C(Y, ℤ_p) → C(Δ × Y, ℤ_p)` of the `δ`-slice.
* `PadicMeasure.coeff`: the `δ`-coefficient measure of a measure on `Δ × Y`.
* `PadicMeasure.finiteProductRingEquiv`:
  `PadicMeasure p (Δ × Y) ≃+* MonoidAlgebra (PadicMeasure p Y) Δ`.
-/

noncomputable section

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]
variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] [TopologicalSpace Δ] [DiscreteTopology Δ]
  [CommGroup Δ]
variable {Y : Type*} [TopologicalSpace Y] [CommMonoid Y] [ContinuousMul Y] [CompactSpace Y]

section slice

/-- The inclusion of a continuous function on `Y` into the `δ`-slice of `Δ × Y`:
`slice δ f` is the function `(δ', y) ↦ if δ' = δ then f y else 0`.  Continuous because
`Δ` is discrete. -/
def slice (δ : Δ) (f : C(Y, ℤ_[p])) : C(Δ × Y, ℤ_[p]) :=
  ⟨fun q => if q.1 = δ then f q.2 else 0,
    continuous_prod_of_discrete_left.2 fun a => by
      by_cases h : a = δ
      · simpa [h] using f.continuous
      · simpa [h] using continuous_const⟩

@[simp]
lemma slice_apply (δ : Δ) (f : C(Y, ℤ_[p])) (q : Δ × Y) :
    slice p δ f q = if q.1 = δ then f q.2 else 0 := rfl

lemma slice_apply_same (δ : Δ) (f : C(Y, ℤ_[p])) (y : Y) :
    slice p δ f (δ, y) = f y := by simp

lemma slice_apply_ne {δ δ' : Δ} (h : δ' ≠ δ) (f : C(Y, ℤ_[p])) (y : Y) :
    slice p δ f (δ', y) = 0 := by simp [h]

@[simp]
lemma slice_add (δ : Δ) (f g : C(Y, ℤ_[p])) :
    slice p δ (f + g) = slice p δ f + slice p δ g := by
  ext q; simp only [slice_apply, ContinuousMap.add_apply]; split <;> simp

@[simp]
lemma slice_smul (δ : Δ) (c : ℤ_[p]) (f : C(Y, ℤ_[p])) :
    slice p δ (c • f) = c • slice p δ f := by
  ext q; simp only [slice_apply, ContinuousMap.smul_apply, smul_eq_mul]; split <;> simp

/-- The slice inclusion as a `ℤ_[p]`-linear map. -/
def sliceLin (δ : Δ) : C(Y, ℤ_[p]) →ₗ[ℤ_[p]] C(Δ × Y, ℤ_[p]) where
  toFun := slice p δ
  map_add' := slice_add p δ
  map_smul' c f := slice_smul p δ c f

@[simp]
lemma sliceLin_apply (δ : Δ) (f : C(Y, ℤ_[p])) : sliceLin p δ f = slice p δ f := rfl

/-- **Reconstruction**: a continuous function on `Δ × Y` is the sum of its slices. -/
lemma sum_slice_curry (g : C(Δ × Y, ℤ_[p])) :
    (∑ δ : Δ, slice p δ (g.curry δ)) = g := by
  ext q
  obtain ⟨a, y⟩ := q
  rw [ContinuousMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single a]
  · simp [slice_apply]
  · intro δ _ hδa
    simp [slice_apply, Ne.symm hδa]
  · exact fun h => absurd (Finset.mem_univ _) h

end slice

section coeff

/-- The `δ`-coefficient measure of a measure on `Δ × Y`: `f ↦ μ (slice δ f)`.  This is
the measure on `Y` reading off the `δ`-component. -/
def coeff (δ : Δ) (μ : PadicMeasure p (Δ × Y)) : PadicMeasure p Y :=
  μ.comp (sliceLin p δ)

@[simp]
lemma coeff_apply (δ : Δ) (μ : PadicMeasure p (Δ × Y)) (f : C(Y, ℤ_[p])) :
    coeff p δ μ f = μ (slice p δ f) := rfl

@[simp]
lemma coeff_add (δ : Δ) (μ ν : PadicMeasure p (Δ × Y)) :
    coeff p δ (μ + ν) = coeff p δ μ + coeff p δ ν := rfl

@[simp]
lemma coeff_smul (δ : Δ) (c : ℤ_[p]) (μ : PadicMeasure p (Δ × Y)) :
    coeff p δ (c • μ) = c • coeff p δ μ := rfl

@[simp]
lemma coeff_dirac (δ : Δ) (a : Δ) (y : Y) :
    coeff p δ (dirac p (a, y)) = if a = δ then dirac p y else 0 := by
  ext f
  rw [coeff_apply, dirac_apply, slice_apply]
  split <;> simp_all

/-- **Fundamental slice decomposition of a measure**: evaluating `ν : PadicMeasure p (Δ × Y)`
on `h` is the sum over `Δ` of the coefficient measures applied to the slices `h(δ, ·)`. -/
lemma measure_eq_sum_coeff_curry (ν : PadicMeasure p (Δ × Y)) (h : C(Δ × Y, ℤ_[p])) :
    ν h = ∑ δ : Δ, (coeff p δ ν) (h.curry δ) := by
  conv_lhs => rw [← sum_slice_curry p h, map_sum]
  rfl

end coeff

section equiv

/-- The measure on `Δ × Y` reconstructed from a `Δ`-indexed tuple of measures on `Y`:
`g ↦ ∑_δ (F δ) (g(δ, ·))`.  This is the inverse direction of the carrier bridge. -/
def ofCoeff (F : MonoidAlgebra (PadicMeasure p Y) Δ) : PadicMeasure p (Δ × Y) where
  toFun g := ∑ δ : Δ, (F δ) (g.curry δ)
  map_add' g h := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [show (g + h).curry δ = g.curry δ + h.curry δ from ContinuousMap.ext fun y => rfl,
      map_add]
  map_smul' c g := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [show (c • g).curry δ = c • g.curry δ from ContinuousMap.ext fun y => rfl, map_smul]

@[simp]
lemma ofCoeff_apply (F : MonoidAlgebra (PadicMeasure p Y) Δ) (g : C(Δ × Y, ℤ_[p])) :
    ofCoeff p F g = ∑ δ : Δ, (F δ) (g.curry δ) := rfl

/-- **Per-coefficient convolution identity**: the `δ`-coefficient of the convolution
`μ * ν` on `Δ × Y` is the `Δ`-convolution of the coefficient measures,
`∑_{a} (coeff a μ) ⋆ (coeff (a⁻¹ δ) ν)`, the convolution `⋆` being on `PadicMeasure p Y`.
This is the ring-structure compatibility that makes the slice decomposition a ring iso. -/
lemma coeff_conv (δ : Δ) (μ ν : PadicMeasure p (Δ × Y)) :
    coeff p δ (μ * ν)
      = ∑ a : Δ, (coeff p a μ) * (coeff p (a⁻¹ * δ) ν) := by
  classical
  refine LinearMap.ext fun f => ?_
  -- abbreviation for the y-translate of `f`, as a continuous map on `Y`
  -- RHS first: each summand unfolds via `conv_mul_apply`
  rw [LinearMap.coe_sum, Finset.sum_apply]
  -- LHS: unfold coeff and convolution on `Δ × Y`
  rw [coeff_apply, conv_mul_apply]
  -- the inner integral against ν, evaluated at (a, y), is a Δ-sum of coefficient integrals
  have hinner : innerInt p ν ((slice p δ f).comp (mulCM₂ (Δ × Y)))
      = ∑ a : Δ, slice p a (innerInt p (coeff p (a⁻¹ * δ) ν) (f.comp (mulCM₂ Y))) := by
    refine ContinuousMap.ext fun q => ?_
    obtain ⟨a, y⟩ := q
    -- the doubly-curried function: `(curry (a,y)).curry a' = if a*a'=δ then z↦f(y*z) else 0`
    have hcurry : ∀ a' : Δ,
        (((slice p δ f).comp (mulCM₂ (Δ × Y))).curry (a, y)).curry a'
          = if a * a' = δ then (f.comp (mulCM₂ Y)).curry y else 0 := by
      intro a'
      by_cases hcond : a * a' = δ
      · rw [if_pos hcond]
        refine ContinuousMap.ext fun z => ?_
        simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply, mulCM₂,
          ContinuousMap.coe_mk, slice_apply, Prod.mk_mul_mk]
        rw [if_pos hcond]
      · rw [if_neg hcond]
        refine ContinuousMap.ext fun z => ?_
        simp only [ContinuousMap.curry_apply, ContinuousMap.comp_apply, mulCM₂,
          ContinuousMap.coe_mk, slice_apply, ContinuousMap.zero_apply, Prod.mk_mul_mk]
        rw [if_neg hcond]
    -- RHS at (a,y): only the `a' = a` slice survives
    rw [ContinuousMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single a]
    rotate_left
    · intro a' _ ha'a
      rw [slice_apply, if_neg (fun h => ha'a h.symm)]
    · exact fun h => absurd (Finset.mem_univ _) h
    rw [slice_apply, if_pos rfl, innerInt_apply]
    -- LHS at (a,y): only the `a' = a⁻¹δ` term survives
    rw [innerInt_apply, measure_eq_sum_coeff_curry p ν,
      Finset.sum_eq_single (a⁻¹ * δ)]
    · rw [hcurry (a⁻¹ * δ), if_pos (mul_inv_cancel_left a δ)]
    · intro a' _ ha'
      rw [hcurry a', if_neg (fun h => ha' (by rw [← h, inv_mul_cancel_left])), map_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hinner, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [conv_mul_apply]
  -- `μ (slice a g) = coeff a μ g`
  rfl

/-- The forward map: the measure `μ` on `Δ × Y` becomes the group-algebra element
`∑_δ [δ] · μ_δ`, where `μ_δ = coeff δ μ`. -/
def toCoeff (μ : PadicMeasure p (Δ × Y)) : MonoidAlgebra (PadicMeasure p Y) Δ :=
  ∑ δ : Δ, MonoidAlgebra.single δ (coeff p δ μ)

@[simp]
lemma toCoeff_apply_coeff (μ : PadicMeasure p (Δ × Y)) (δ : Δ) :
    (toCoeff p μ) δ = coeff p δ μ := by
  classical
  rw [toCoeff, show (∑ a : Δ, MonoidAlgebra.single a (coeff p a μ)) δ
      = ∑ a : Δ, (MonoidAlgebra.single a (coeff p a μ)) δ from
    map_sum (Finsupp.applyAddHom (M := PadicMeasure p Y) δ) _ _, Finset.sum_eq_single δ]
  · rw [MonoidAlgebra.single_apply, if_pos rfl]
  · intro a _ haδ
    rw [MonoidAlgebra.single_apply, if_neg haδ]
  · exact fun h => absurd (Finset.mem_univ _) h

lemma toCoeff_add (μ ν : PadicMeasure p (Δ × Y)) :
    toCoeff p (μ + ν) = toCoeff p μ + toCoeff p ν := by
  rw [toCoeff, toCoeff, toCoeff, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [coeff_add, MonoidAlgebra.single_add]

lemma toCoeff_smul (c : ℤ_[p]) (μ : PadicMeasure p (Δ × Y)) :
    toCoeff p (c • μ) = c • toCoeff p μ := by
  rw [toCoeff, toCoeff, Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [coeff_smul, MonoidAlgebra.smul_single]

lemma ofCoeff_toCoeff (μ : PadicMeasure p (Δ × Y)) : ofCoeff p (toCoeff p μ) = μ := by
  refine LinearMap.ext fun g => ?_
  rw [ofCoeff_apply]
  simp_rw [toCoeff_apply_coeff, coeff_apply]
  rw [← map_sum, sum_slice_curry]

lemma toCoeff_ofCoeff (F : MonoidAlgebra (PadicMeasure p Y) Δ) :
    toCoeff p (ofCoeff p F) = F := by
  classical
  -- compare coefficients
  refine Finsupp.ext fun δ => ?_
  rw [toCoeff_apply_coeff]
  refine LinearMap.ext fun f => ?_
  rw [coeff_apply, ofCoeff_apply, Finset.sum_eq_single δ]
  · rw [show (slice p δ f).curry δ = f from ContinuousMap.ext fun y => by
      rw [ContinuousMap.curry_apply, slice_apply_same]]
  · intro a _ haδ
    rw [show (slice p δ f).curry a = 0 from ContinuousMap.ext fun y => by
      rw [ContinuousMap.curry_apply, slice_apply_ne p haδ, ContinuousMap.zero_apply], map_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- **Module isomorphism**: `PadicMeasure p (Δ × Y) ≃ₗ[ℤ_[p]] MonoidAlgebra (PadicMeasure p Y) Δ`
via the slice decomposition. -/
def finiteProductLinearEquiv :
    PadicMeasure p (Δ × Y) ≃ₗ[ℤ_[p]] MonoidAlgebra (PadicMeasure p Y) Δ where
  toFun := toCoeff p
  map_add' := toCoeff_add p
  map_smul' := toCoeff_smul p
  invFun := ofCoeff p
  left_inv := ofCoeff_toCoeff p
  right_inv := toCoeff_ofCoeff p

@[simp]
lemma finiteProductLinearEquiv_apply (μ : PadicMeasure p (Δ × Y)) :
    finiteProductLinearEquiv p μ = toCoeff p μ := rfl

@[simp]
lemma finiteProductLinearEquiv_symm_apply (F : MonoidAlgebra (PadicMeasure p Y) Δ) :
    (finiteProductLinearEquiv p).symm F = ofCoeff p F := rfl

lemma toCoeff_one : toCoeff p (1 : PadicMeasure p (Δ × Y)) = 1 := by
  classical
  rw [conv_one_def, show (1 : Δ × Y) = ((1 : Δ), (1 : Y)) from rfl, toCoeff,
    Finset.sum_eq_single (1 : Δ)]
  · rw [coeff_dirac, if_pos rfl, MonoidAlgebra.one_def, conv_one_def]
  · intro a _ ha
    rw [coeff_dirac, if_neg (fun h => ha h.symm), MonoidAlgebra.single_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

lemma toCoeff_mul (μ ν : PadicMeasure p (Δ × Y)) :
    toCoeff p (μ * ν) = toCoeff p μ * toCoeff p ν := by
  classical
  -- expand the product of the two `single`-sums and reindex `b ↦ a⁻¹·g`
  rw [show toCoeff p μ * toCoeff p ν
      = ∑ a : Δ, ∑ b : Δ,
          MonoidAlgebra.single (a * b) (coeff p a μ * coeff p b ν) from by
    rw [toCoeff, toCoeff, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      MonoidAlgebra.single_mul_single a b _ _]
  calc toCoeff p (μ * ν)
      = ∑ g : Δ, MonoidAlgebra.single g (∑ a : Δ, coeff p a μ * coeff p (a⁻¹ * g) ν) := by
        rw [toCoeff]
        exact Finset.sum_congr rfl fun g _ => by rw [coeff_conv]
    _ = ∑ g : Δ, ∑ a : Δ,
          MonoidAlgebra.single g (coeff p a μ * coeff p (a⁻¹ * g) ν) := by
        exact Finset.sum_congr rfl fun g _ => map_sum (Finsupp.singleAddHom g) _ _
    _ = ∑ a : Δ, ∑ g : Δ,
          MonoidAlgebra.single g (coeff p a μ * coeff p (a⁻¹ * g) ν) := Finset.sum_comm
    _ = ∑ a : Δ, ∑ b : Δ,
          MonoidAlgebra.single (a * b) (coeff p a μ * coeff p b ν) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        refine (Fintype.sum_equiv (Equiv.mulLeft a)
          (fun b => MonoidAlgebra.single (a * b) (coeff p a μ * coeff p b ν))
          (fun g => MonoidAlgebra.single g (coeff p a μ * coeff p (a⁻¹ * g) ν))
          (fun b => ?_)).symm
        rw [show (Equiv.mulLeft a) b = a * b from rfl, inv_mul_cancel_left]

/-- **Ring isomorphism** (CARRIER-BRIDGE step 2):
`PadicMeasure p (Δ × Y)  ≃+*  MonoidAlgebra (PadicMeasure p Y) Δ` for `Δ` a finite
commutative group and `Y` a compact commutative topological monoid.  The forward map is
the slice decomposition `μ ↦ ∑_δ [δ] · (coeff δ μ)`; it respects convolution because the
group structure on `Δ × Y` is the product, and `map_one`/`map_mul` are
`toCoeff_one`/`toCoeff_mul`. -/
def finiteProductRingEquiv :
    PadicMeasure p (Δ × Y) ≃+* MonoidAlgebra (PadicMeasure p Y) Δ where
  __ := finiteProductLinearEquiv p
  map_mul' := toCoeff_mul p
  map_add' := toCoeff_add p

@[simp]
lemma finiteProductRingEquiv_apply (μ : PadicMeasure p (Δ × Y)) :
    finiteProductRingEquiv p μ = toCoeff p μ := rfl

@[simp]
lemma finiteProductRingEquiv_symm_apply (F : MonoidAlgebra (PadicMeasure p Y) Δ) :
    (finiteProductRingEquiv p).symm F = ofCoeff p F := rfl

/-- On Dirac measures the ring iso is the obvious thing: `δ_{(a,y)} ↦ [a] · δ_y`. -/
@[simp]
lemma finiteProductRingEquiv_dirac (a : Δ) (y : Y) :
    finiteProductRingEquiv p (dirac p (a, y))
      = MonoidAlgebra.single a (dirac p y) := by
  classical
  rw [finiteProductRingEquiv_apply, toCoeff, Finset.sum_eq_single a]
  · rw [coeff_dirac, if_pos rfl]
  · intro δ _ hδa
    rw [coeff_dirac, if_neg (fun h => hδa h.symm), MonoidAlgebra.single_zero]
  · exact fun h => absurd (Finset.mem_univ _) h

end equiv

end PadicMeasure
