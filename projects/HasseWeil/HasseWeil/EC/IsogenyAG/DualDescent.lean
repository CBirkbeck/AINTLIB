import HasseWeil.EC.IsogenyAG.IsogenyClass
import HasseWeil.EC.IsogenyAG.MulByIntBasepoint
import HasseWeil.Curves.CurveMapBaseChange
import HasseWeil.Curves.NoFinitePolesBridge
import HasseWeil.Curves.OrdAtInftyBaseChange

/-!
# DUAL-DESCENT — the dual isogeny over the base field (symmetry of isogeny)

Goal (see `.mathlib-quality/plan-dual-descent.md` + `tickets-dual-descent.md`): discharge
`UniversalDualWitness F` for a char-0 base field `F` (esp. `ℚ`) — every isogeny over `F` has an
`F`-rational dual, i.e. `IsIsogenous` is symmetric, i.e. the `IsogenyClass` quotient and the LMFDB
label layer become unconditional.

**Route (Silverman III.6.1, transcribed):** over char 0 every isogeny is separable, so the dual is
purely the III.4.11 factorization `ker φ ⊆ E[m] ⟹ [m] = φ̂ ∘ φ`. III.4.11 is irreducibly a
`K̄`-Galois argument, so the dual is built over `K̄ = AlgebraicClosure F` (existing K̄ machinery) and
**descended to `F` by uniqueness + Galois-invariance** (`φ̂^σ ∘ φ = [m] ⟹ φ̂^σ = φ̂`). The descent is
run at a *finite* Galois level `L/F`. The new infrastructure is the descent of a curve morphism
(DUAL-Q2, the deep crux); this file holds the headline + assembly, with the descent internals filled
in across tickets DUAL-Q1…Q4.

## Status (DUAL-Q1…Q4)

The arc is landed end-to-end with the deep inputs isolated to **two** named `sorry`s:

* **DUAL-Q1** (`galActFunctionField` + API): the `Gal(L/F)`-action on `F(C_L)` via `σ ⊗ id` through
  `functionField_baseChange_tensorEquiv`, with `_id`/`_trans` and the *fixed-the-base-field* easy
  direction `galActFunctionField_fixes_baseChange` — **all axiom-clean**. The fixed-field
  characterization `mem_range_functionField_baseChange_iff_fixed` has its easy direction proved; its
  `→` (the Galois descent of the fraction field `F(C_L) = Frac(L ⊗_F F[C])`) is `sorry` #1.
* **DUAL-Q2** (`descendPullback` / `descendIsogeny`): a `Gal(L/F)`-equivariant pullback descends to an
  `F`-algebra hom and to an `EC.Isogeny` over `F`; the algebra-hom packaging, the round-trip
  `functionFieldMap_comp_descendPullback`, and the basepoint condition `descend_basepoint` are all
  proved (the CurveMap-from-restricted-pullback crux is **complete** modulo Q1's `sorry`).
* **DUAL-Q3** (`galEquivariant_of_compose`): from the defining identity `φ* ∘ φ̂* = [m]*` and
  injectivity of `φ*`, the dual pullback is equivariant — **axiom-clean** (the base-changed-pullback
  equivariance feeding it is the residual inside `sorry` #2).
* **DUAL-Q4** (`hasDualWitness_of_compose` + `universalDualWitness_of_charZero`): a reverse isogeny
  `ρ` over `F` with `ρ ∘ φ = [deg φ]` yields `HasDualWitness φ` — **axiom-clean**; the headline
  reduces to the assembled-chain residual `rationalDualCompose_of_charZero` (`sorry` #2). The label
  gate is discharged ungated in `IsogenyClassLabel.lean` (`*_charZero`).
-/

namespace HasseWeil.EC

open WeierstrassCurve

open scoped TensorProduct

open Curves

variable {F : Type*} [Field F]

/-! ## DUAL-Q1 — the Galois action on the base-changed function field + fixed field

For a smooth plane curve `C/F` and an `F`-algebra extension `L`, the function field of the base
change `C_L` is the fraction field of `L ⊗_F F[C]` (the project's
`functionField_baseChange_tensorEquiv`). An `F`-algebra automorphism `σ : L ≃ₐ[F] L` acts on
`L ⊗_F F[C]` through the `L`-factor (`Algebra.TensorProduct.congr σ id`), lifts to the fraction
field (`IsFractionRing.algEquivOfAlgEquiv`), and transports along the tensor identification to an
`F`-algebra automorphism `galActFunctionField C L σ` of `C_L`'s function field.

This is a group action (`galActFunctionField_id`, `galActFunctionField_trans`) fixing the image of
`F(C)` (`galActFunctionField_fixes_baseChange`). When `L/F` is finite Galois, the fixed field is
**exactly** the image of `F(C)` (the descent fact `mem_range_functionField_baseChange_iff_fixed`,
whose nontrivial `←` direction is the genuinely-deep Galois-descent of the fraction field; see the
honest note there). -/

/-- The Galois action on the tensor-fraction-ring presentation
`FractionRing (L ⊗_F F[C])`, induced by `σ ⊗ id` via `IsFractionRing.algEquivOfAlgEquiv`. -/
noncomputable def galActFrac (C : SmoothPlaneCurve F)
    (L : Type*) [Field L] [Algebra F L] (σ : L ≃ₐ[F] L) :
    letI := C.isDomain_tensorCoordRing L
    FractionRing (L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[F]
      FractionRing (L ⊗[F] C.toAffine.CoordinateRing) :=
  letI := C.isDomain_tensorCoordRing L
  IsFractionRing.algEquivOfAlgEquiv
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F)
      (A₁ := C.toAffine.CoordinateRing)))

/-- `σ ⊗ id` for `σ = τ₁ ∘ τ₂` decomposes as the composition on the domain `L ⊗_F F[C]`. -/
theorem congr_id_trans (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (σ τ : L ≃ₐ[F] L) :
    (Algebra.TensorProduct.congr (σ.trans τ) (AlgEquiv.refl (R := F)
        (A₁ := C.toAffine.CoordinateRing))) =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F)
          (A₁ := C.toAffine.CoordinateRing))).trans
        (Algebra.TensorProduct.congr τ (AlgEquiv.refl (R := F)
          (A₁ := C.toAffine.CoordinateRing))) := by
  apply AlgEquiv.coe_algHom_injective
  apply Algebra.TensorProduct.ext'
  intro l u
  simp [Algebra.TensorProduct.congr_apply]

@[simp] theorem galActFrac_refl (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L] :
    letI := C.isDomain_tensorCoordRing L
    galActFrac C L (AlgEquiv.refl) = AlgEquiv.refl := by
  letI := C.isDomain_tensorCoordRing L
  unfold galActFrac
  rw [Algebra.TensorProduct.congr_refl]
  ext x
  simp [IsFractionRing.algEquivOfAlgEquiv]

theorem galActFrac_trans (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (σ τ : L ≃ₐ[F] L) :
    letI := C.isDomain_tensorCoordRing L
    galActFrac C L (σ.trans τ) = (galActFrac C L σ).trans (galActFrac C L τ) := by
  letI := C.isDomain_tensorCoordRing L
  ext x
  obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective
    (A := L ⊗[F] C.toAffine.CoordinateRing) x
  show galActFrac C L (σ.trans τ) _ = galActFrac C L τ (galActFrac C L σ _)
  simp only [galActFrac, map_div₀, AlgEquiv.trans_apply,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rw [congr_id_trans]
  rfl

/-- **DUAL-Q1(b)** — the Galois action of `σ : L ≃ₐ[F] L` on the base-changed function field
`F(C_L)`, by conjugating the tensor-side action `galActFrac` through the project's tensor
identification `functionField_baseChange_tensorEquiv`. It is an `F`-algebra automorphism. -/
noncomputable def galActFunctionField (C : SmoothPlaneCurve F)
    (L : Type*) [Field L] [Algebra F L] (σ : L ≃ₐ[F] L) :
    (C.baseChange L).FunctionField ≃ₐ[F] (C.baseChange L).FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  ((C.functionField_baseChange_tensorEquiv L).restrictScalars F).trans
    ((galActFrac C L σ).trans
      ((C.functionField_baseChange_tensorEquiv L).symm.restrictScalars F))

/-- **DUAL-Q1(b), identity law**: the action of the identity automorphism is the identity. -/
@[simp] theorem galActFunctionField_id (C : SmoothPlaneCurve F) (L : Type*) [Field L]
    [Algebra F L] : galActFunctionField C L (AlgEquiv.refl) = AlgEquiv.refl := by
  letI := C.isDomain_tensorCoordRing L
  ext x
  simp only [galActFunctionField, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    galActFrac_refl, AlgEquiv.coe_refl, id_eq, AlgEquiv.symm_apply_apply]

/-- **DUAL-Q1(b), composition law**: the action is a group action,
`galAct (σ ∘ τ) = galAct σ ∘ galAct τ` (it's a homomorphism `Gal(L/F) → Aut(F(C_L)/F)`). -/
theorem galActFunctionField_trans (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (σ τ : L ≃ₐ[F] L) :
    galActFunctionField C L (σ.trans τ) =
      (galActFunctionField C L σ).trans (galActFunctionField C L τ) := by
  letI := C.isDomain_tensorCoordRing L
  ext x
  simp only [galActFunctionField, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    galActFrac_trans, AlgEquiv.apply_symm_apply]

/-- The tensor identification carries `1 ⊗ u` (for `u` in the coordinate ring) to the base-change
image `functionFieldMap` of `u`'s class in `F(C)`. The spine of the fixed-field easy direction. -/
theorem tensorEquiv_symm_one_tmul (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (u : C.toAffine.CoordinateRing) :
    letI := C.isDomain_tensorCoordRing L
    (C.functionField_baseChange_tensorEquiv L).symm
      (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) _ (1 ⊗ₜ u)) =
      C.functionFieldMap L (algebraMap C.toAffine.CoordinateRing C.FunctionField u) := by
  letI := C.isDomain_tensorCoordRing L
  rw [SmoothPlaneCurve.functionFieldMap_algebraMap]
  show (C.functionField_baseChange_fracEquiv L) _ = _
  rw [show C.functionField_baseChange_fracEquiv L =
      IsFractionRing.algEquivOfAlgEquiv (C.coordRingScalarExtPinned L) from rfl,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  congr 1
  show C.fwdPinned L (1 ⊗ₜ u) = _
  rw [SmoothPlaneCurve.fwdPinned_tmul, one_smul]

/-- **DUAL-Q1(c), easy direction**: the Galois action fixes the image of `F(C)` inside `F(C_L)`.
Every base-changed function `functionFieldMap f` is `galAct σ`-invariant, since on the tensor side
`σ ⊗ id` fixes `1 ⊗ u` (as `σ 1 = 1`), and `F(C)` is generated by such classes. -/
theorem galActFunctionField_fixes_baseChange (C : SmoothPlaneCurve F) (L : Type*) [Field L]
    [Algebra F L] (σ : L ≃ₐ[F] L) (f : C.FunctionField) :
    galActFunctionField C L σ (C.functionFieldMap L f) = C.functionFieldMap L f := by
  letI := C.isDomain_tensorCoordRing L
  -- reduce `f` to a ratio of coordinate-ring classes
  obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := C.toAffine.CoordinateRing) f
  rw [map_div₀, map_div₀]
  -- it suffices to fix `functionFieldMap (algebraMap u)` for `u ∈ CR`
  have key : ∀ u : C.toAffine.CoordinateRing,
      galActFunctionField C L σ
          (C.functionFieldMap L (algebraMap C.toAffine.CoordinateRing C.FunctionField u)) =
        C.functionFieldMap L (algebraMap C.toAffine.CoordinateRing C.FunctionField u) := by
    intro u
    rw [← tensorEquiv_symm_one_tmul]
    simp only [galActFunctionField, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      AlgEquiv.apply_symm_apply]
    congr 1
    show galActFrac C L σ (algebraMap _ _ (1 ⊗ₜ u)) = _
    simp only [galActFrac, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    congr 1
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp
  rw [key, key]

/-- **DUAL-Q1(c), the fixed-field characterization** (`L/F` finite Galois): an element of `F(C_L)`
is fixed by *every* `galActFunctionField C L σ` iff it lies in the image of `F(C)` under the
base-change embedding `functionFieldMap`.

The `←` direction is `galActFunctionField_fixes_baseChange` (proved). The `→` direction is the
genuine **Galois descent of the fraction field** `F(C_L) = FractionRing(L ⊗_F F[C])`: a
`Gal(L/F)`-invariant element of the fraction field descends to `F(C)`. Over the domain `L ⊗_F F[C]`
this is the (free-module) Galois descent of `F[C]`; over its fraction field it is the statement that
`F(C_L)/F(C)` is finite Galois with group realized by `galActFunctionField`, so
`IntermediateField`'s `mem_range_algebraMap_iff_fixed` applies. This wiring is the deep DUAL-Q1/Q2
sub-leaf; it is isolated here as a single `sorry`. -/
theorem mem_range_functionField_baseChange_iff_fixed (C : SmoothPlaneCurve F)
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (x : (C.baseChange L).FunctionField) :
    (∃ f : C.FunctionField, C.functionFieldMap L f = x) ↔
      ∀ σ : L ≃ₐ[F] L, galActFunctionField C L σ x = x := by
  constructor
  · rintro ⟨f, rfl⟩ σ
    exact galActFunctionField_fixes_baseChange C L σ f
  · intro _hfixed
    sorry

/-! ## DUAL-Q2 — descent of a `Gal(L/F)`-equivariant function-field morphism

A function-field pullback `ξ : F(E₂_L) →ₐ[F] F(E₁_L)` that commutes with the Galois action
(`GalEquivariant`) restricts to a pullback `F(E₂) →ₐ[F] F(E₁)` over the base field. The mechanism:
`ξ (functionFieldMap f)` is `galAct`-fixed (equivariance + Q1's easy direction), hence — by Q1's
fixed-field characterization — lies in the image of `F(E₁)`; the unique preimage (`functionFieldMap`
injective) defines the descended pullback. The descended pullback round-trips: base-changing it back
recovers `ξ` on the `F(E₂)`-generators.

The descended pullback is the curve-map datum of the descended morphism; the basepoint condition for
the resulting `EC.Isogeny` over `F` is then `reflects_ordAtInfty`-style (field-general, HAVE). -/

/-- `ξ : F(E₂_L) →ₐ[F] F(E₁_L)` is **`Gal(L/F)`-equivariant** if it commutes with the Galois action
on both function fields, i.e. `ξ (galAct σ x) = galAct σ (ξ x)` for every `σ`. -/
def GalEquivariant {C₁ C₂ : SmoothPlaneCurve F} (L : Type*) [Field L] [Algebra F L]
    (ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField) : Prop :=
  ∀ (σ : L ≃ₐ[F] L) (x : (C₂.baseChange L).FunctionField),
    ξ (galActFunctionField C₂ L σ x) = galActFunctionField C₁ L σ (ξ x)

/-- For an equivariant `ξ`, the image `ξ (functionFieldMap f)` of a base-changed function is
`galAct`-fixed (it is the image under the equivariant `ξ` of a fixed element). -/
theorem galActFunctionField_fixes_equivariant_image
    {C₁ C₂ : SmoothPlaneCurve F} (L : Type*) [Field L] [Algebra F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) (σ : L ≃ₐ[F] L) :
    galActFunctionField C₁ L σ (ξ (C₂.functionFieldMap L f)) = ξ (C₂.functionFieldMap L f) := by
  rw [← hξ σ, galActFunctionField_fixes_baseChange]

/-- **DUAL-Q2(a)** — the descended pullback exists on each generator: for an equivariant `ξ` and a
finite-Galois `L/F`, `ξ (functionFieldMap f)` is the base-change image of a (unique) function on
`E₁` over `F`. The existence uses Q1's fixed-field characterization
(`mem_range_functionField_baseChange_iff_fixed`); uniqueness uses injectivity of `functionFieldMap`.
-/
theorem exists_descend_apply {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) :
    ∃! g : C₁.FunctionField, C₁.functionFieldMap L g = ξ (C₂.functionFieldMap L f) := by
  obtain ⟨g, hg⟩ := (mem_range_functionField_baseChange_iff_fixed C₁ L
    (ξ (C₂.functionFieldMap L f))).2
    (galActFunctionField_fixes_equivariant_image L hξ f)
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact C₁.functionFieldMap_injective L (hg'.trans hg.symm)

/-- The descended function `f ↦ g` where `functionFieldMap g = ξ (functionFieldMap f)`,
chosen by `exists_descend_apply`. -/
noncomputable def descendFun {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) : C₁.FunctionField :=
  (exists_descend_apply L hξ f).choose

/-- **The round-trip** (DUAL-Q2(c), generator form): base-changing the descended function recovers
`ξ` on the `F(E₂)`-image. -/
@[simp] theorem functionFieldMap_descendFun {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) :
    C₁.functionFieldMap L (descendFun L hξ f) = ξ (C₂.functionFieldMap L f) :=
  (exists_descend_apply L hξ f).choose_spec.1

/-- The descended function is the unique preimage; a convenience eliminator. -/
theorem descendFun_eq_iff {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) (g : C₁.FunctionField) :
    descendFun L hξ f = g ↔ C₁.functionFieldMap L g = ξ (C₂.functionFieldMap L f) := by
  constructor
  · rintro rfl; exact functionFieldMap_descendFun L hξ f
  · intro h; exact C₁.functionFieldMap_injective L
      ((functionFieldMap_descendFun L hξ f).trans h.symm)

/-- **DUAL-Q2(b)** — the descended pullback `ξ↓ : F(E₂) →ₐ[F] F(E₁)`, packaged as an `F`-algebra
hom. The ring/algebra structure is forced by the round-trip `functionFieldMap_descendFun` and the
injectivity of `functionFieldMap`: `ξ↓` is the unique map making the base-change square commute, and
each algebra axiom for `ξ↓` follows by applying the (injective) base-change embedding and using that
`ξ` and `functionFieldMap` are algebra homs. This is the new Galois-descent-of-a-curve-morphism
infrastructure (DUAL-Q2), built CoordHom-free at the function-field level. -/
noncomputable def descendPullback {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) :
    C₂.FunctionField →ₐ[F] C₁.FunctionField where
  toFun := descendFun L hξ
  map_one' := (descendFun_eq_iff L hξ 1 1).2 (by simp)
  map_mul' a b := (descendFun_eq_iff L hξ (a * b) _).2 (by simp)
  map_zero' := (descendFun_eq_iff L hξ 0 0).2 (by simp)
  map_add' a b := (descendFun_eq_iff L hξ (a + b) _).2 (by simp)
  commutes' r := (descendFun_eq_iff L hξ (algebraMap F C₂.FunctionField r)
      (algebraMap F C₁.FunctionField r)).2 (by
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F,
      SmoothPlaneCurve.functionFieldMap_algebraMap_F, AlgHom.commutes])

@[simp] theorem descendPullback_apply {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) :
    descendPullback L hξ f = descendFun L hξ f := rfl

/-- **DUAL-Q2(c)** — the full round-trip as algebra homs: `functionFieldMap ∘ ξ↓ = ξ ∘ functionFieldMap`,
i.e. the descended pullback base-changes back to `ξ` on the `F(E₂)`-image. -/
theorem functionFieldMap_comp_descendPullback {C₁ C₂ : SmoothPlaneCurve F}
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {ξ : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hξ : GalEquivariant L ξ) (f : C₂.FunctionField) :
    C₁.functionFieldMap L (descendPullback L hξ f) = ξ (C₂.functionFieldMap L f) :=
  functionFieldMap_descendFun L hξ f

/-- **DUAL-Q2 basepoint** — the descended pullback satisfies the morphism-defined-at-`O` condition.
If `ξ = ψ*` is the pullback of an `EC.Isogeny ψ : E₁_L → E₂_L`, then the descended pullback
`ξ↓ : F(E₂) → F(E₁)` preserves regularity at infinity. Proof: order at infinity is preserved by the
base-change embedding (`ordAtInfty_functionFieldMap`), the round-trip identifies
`functionFieldMap (ξ↓ g)` with `ψ* (functionFieldMap g)`, and `ψ` itself is defined at `O`. Fully
discharged (no descent input needed for this leg). -/
theorem descend_basepoint (C₁ C₂ : SmoothPlaneCurve F)
    [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [(C₁.baseChange L).toAffine.IsElliptic] [(C₂.baseChange L).toAffine.IsElliptic]
    (ψ : EC.Isogeny (C₁.baseChange L).toAffine (C₂.baseChange L).toAffine)
    (hψ : GalEquivariant L ((ψ.toCurveMap.pullback).restrictScalars F))
    (g : C₂.FunctionField) (hg : 0 ≤ C₂.ordAtInfty g) :
    0 ≤ C₁.ordAtInfty (descendPullback L hψ g) := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [show descendPullback L hψ 0 = 0 from map_zero _]; simp
  have hround : C₁.functionFieldMap L (descendPullback L hψ g) =
      (ψ.toCurveMap.pullback) (C₂.functionFieldMap L g) :=
    functionFieldMap_comp_descendPullback L hψ g
  have hgmap_ne : C₂.functionFieldMap L g ≠ 0 :=
    (map_ne_zero_iff _ (C₂.functionFieldMap_injective L)).2 hg0
  have hψmap_ne : (ψ.toCurveMap.pullback) (C₂.functionFieldMap L g) ≠ 0 :=
    (map_ne_zero_iff _ ψ.pullback_injective).2 hgmap_ne
  have hdesc_ne : descendPullback L hψ g ≠ 0 := by
    intro h; rw [h, map_zero] at hround; exact hψmap_ne hround.symm
  have hC₁ : (C₁.baseChange L).ordAtInfty (C₁.functionFieldMap L (descendPullback L hψ g)) =
      C₁.ordAtInfty (descendPullback L hψ g) :=
    C₁.ordAtInfty_functionFieldMap L _ hdesc_ne
  have hC₂ : (C₂.baseChange L).ordAtInfty (C₂.functionFieldMap L g) = C₂.ordAtInfty g :=
    C₂.ordAtInfty_functionFieldMap L _ hg0
  have hψbase := ψ.pullback_ordAtInfty_nonneg (C₂.functionFieldMap L g)
  rw [← hC₁, hround]
  apply hψbase
  rw [hC₂]
  exact hg

/-- **DUAL-Q2 — the descended isogeny over `F`** (the new Galois-descent-of-a-curve-morphism
infrastructure). From an `EC.Isogeny ψ : E₁_L → E₂_L` whose pullback is `Gal(L/F)`-equivariant,
produce the descended `EC.Isogeny E₂ → E₁` over the base field: its pullback is `descendPullback`
(DUAL-Q2(b)), its basepoint condition is `descend_basepoint`. The descent uses Q1's fixed-field
characterization (the only deep input) through `descendPullback`/`exists_descend_apply`; the
basepoint and algebra-hom structure are discharged. -/
noncomputable def descendIsogeny (C₁ C₂ : SmoothPlaneCurve F)
    [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [(C₁.baseChange L).toAffine.IsElliptic] [(C₂.baseChange L).toAffine.IsElliptic]
    (ψ : EC.Isogeny (C₁.baseChange L).toAffine (C₂.baseChange L).toAffine)
    (hψ : GalEquivariant L ((ψ.toCurveMap.pullback).restrictScalars F)) :
    EC.Isogeny C₁.toAffine C₂.toAffine where
  toCurveMap := ⟨descendPullback L hψ⟩
  pullback_ordAtInfty_nonneg g hg := descend_basepoint C₁ C₂ L ψ hψ g hg

@[simp] theorem descendIsogeny_pullback (C₁ C₂ : SmoothPlaneCurve F)
    [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [(C₁.baseChange L).toAffine.IsElliptic] [(C₂.baseChange L).toAffine.IsElliptic]
    (ψ : EC.Isogeny (C₁.baseChange L).toAffine (C₂.baseChange L).toAffine)
    (hψ : GalEquivariant L ((ψ.toCurveMap.pullback).restrictScalars F)) :
    (descendIsogeny C₁ C₂ L ψ hψ).toCurveMap.pullback = descendPullback L hψ := rfl

/-! ## DUAL-Q3 — the dual pullback is `Gal(L/F)`-equivariant (from uniqueness)

The defining identity of the dual is `φ̂ ∘ φ = [m]`, i.e. at the pullback level
`φ* ∘ φ̂* = [m]*` (composition is contravariant). The Galois action commutes with `φ*` and `[m]*`
(they are base-changed from the `F`-rational `φ`, `[m]`); since `φ*` is injective, the Galois action
must commute with `φ̂*` too. This is `galEquivariant_of_compose` — a clean pullback-level
cancellation (cheaper than Silverman's isogeny-subtraction uniqueness). -/

/-- **DUAL-Q3 core** (uniqueness ⟹ equivariance, pullback form): if `p`, `m` are `Gal(L/F)`-equivariant
function-field homs with `p ∘ q = m` and `p` injective, then `q` is equivariant. Instantiated with
`p = φ*`, `q = φ̂*`, `m = [m]*` (the defining identity `φ* ∘ φ̂* = [m]*`), this is the
Galois-equivariance of the dual pullback. -/
theorem galEquivariant_of_compose {C₁ C₂ : SmoothPlaneCurve F} (L : Type*) [Field L] [Algebra F L]
    {p : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    {q : (C₁.baseChange L).FunctionField →ₐ[F] (C₂.baseChange L).FunctionField}
    {m : (C₁.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField}
    (hp : GalEquivariant L p) (hm : GalEquivariant L m)
    (hpq : ∀ x, p (q x) = m x) (hpinj : Function.Injective p) :
    GalEquivariant L q := by
  intro σ x
  apply hpinj
  rw [hpq, hm σ x, ← hpq, hp σ (q x)]

/-- **DUAL-Q3 — base-changed pullbacks fix the `F`-rational and `L`-constant generators**, the
tractable half of the base-changed-pullback equivariance. For an isogeny `α/F` base-changed to
`α_L/L` (so `functionFieldMap (α* z) = α_L* (functionFieldMap z)`), the Galois action and `α_L*`
*commute on the image of `F(E)`*: both sides reduce to the (Galois-fixed) base-change image of
`α* z`. This is `galActFunctionField_fixes_baseChange` applied twice plus the base-change
compatibility `hbc`. -/
theorem galEquivariant_baseChange_on_image {C₁ C₂ : SmoothPlaneCurve F} (L : Type*) [Field L]
    [Algebra F L]
    {αpb : C₁.FunctionField →ₐ[F] C₂.FunctionField}
    {αLpb : (C₁.baseChange L).FunctionField →ₐ[F] (C₂.baseChange L).FunctionField}
    (hbc : ∀ z : C₁.FunctionField,
      C₂.functionFieldMap L (αpb z) = αLpb (C₁.functionFieldMap L z))
    (σ : L ≃ₐ[F] L) (z : C₁.FunctionField) :
    αLpb (galActFunctionField C₁ L σ (C₁.functionFieldMap L z)) =
      galActFunctionField C₂ L σ (αLpb (C₁.functionFieldMap L z)) := by
  rw [galActFunctionField_fixes_baseChange, ← hbc, galActFunctionField_fixes_baseChange]

/-! ## DUAL-Q4 — assembly: a reverse isogeny with `ρ ∘ φ = [m]` gives a dual witness

The descended reverse isogeny `φ̂` satisfies `φ̂ ∘ φ = [m]` over `F` (round-trip of the K̄ identity).
From such an `F`-rational reverse isogeny, `HasDualWitness φ` is purely formal: `[m]* = φ* ∘ φ̂*`
gives the range inclusion `Im([m]*) ⊆ Im(φ*)`, and the basepoint condition is `reflects_ordAtInfty`.
This is `hasDualWitness_of_compose` — fully discharged at the `F`-level. -/

variable [DecidableEq F]

/-- **DUAL-Q4 reduction** (Silverman III.6.1, `F`-level): if there is a reverse isogeny
`ρ : E₂ → E₁` over `F` with `ρ ∘ φ = [n]` (`n ≠ 0`, mathematically `n = deg φ`), then `φ` admits a
`HasDualWitness`. The range inclusion `Im([n]*) ⊆ Im(φ*)` follows from `[n]* = φ* ∘ ρ*` (the
function-field shadow of `ρ ∘ φ = [n]`), and the basepoint condition from the unconditional
`∞`-regularity reflection `reflects_ordAtInfty`. This isolates the final descent step: produce such a
reverse isogeny over `F` (DUAL-Q2 `descendIsogeny` of the K̄ dual, with the `∘ = [n]` identity from
the round-trip). -/
noncomputable def hasDualWitness_of_compose {W₁ W₂ : WeierstrassCurve.Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic]
    {φ : EC.Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    {ρ : EC.Isogeny W₂ W₁} (hρ : ρ.compose φ = EC.Isogeny.mulByInt W₁ hn) :
    φ.HasDualWitness := by
  have hincl : (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn).range ≤
      φ.toCurveMap.pullback.range := by
    rintro z ⟨u, rfl⟩
    refine ⟨ρ.toCurveMap.pullback u, ?_⟩
    have hc := congrArg (fun χ : EC.Isogeny W₁ W₁ => χ.toCurveMap.pullback u) hρ
    simp only [EC.Isogeny.mulByInt_pullback] at hc
    exact hc
  refine EC.Isogeny.HasMulByIntDualWitness.toHasDualWitness
    (show φ.HasMulByIntDualWitness n hn from ⟨hincl, ?_⟩)
  exact EC.Isogeny.hbase_of_reflects φ
    (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn) hincl
    (EC.mulByIntBasepoint_holds W₁ hn)
    (EC.Isogeny.reflects_ordAtInfty φ)

/-- **DUAL-Q4 residual** (the assembled DUAL-Q1–Q3 chain, char-0): every isogeny `φ : E₁ → E₂` over a
char-0 field has an `F`-rational reverse isogeny `ρ : E₂ → E₁` with `ρ ∘ φ = [deg φ]`.

This is the dual `φ̂` over `F` from Silverman III.6.1: base-change `φ` to `K̄ = AlgebraicClosure F`
(char 0 ⟹ separable), build the K̄ dual `φ̂_K̄` (`exists_dual_of_pullbackEvaluation_general`), descend
to `φ̂` over the finite Galois field of definition `L/F` (DUAL-Q2 `descendIsogeny`, with the dual's
pullback `Gal(L/F)`-equivariant by DUAL-Q3 `galEquivariant_of_compose`), and transport the K̄ identity
`φ̂_K̄ ∘ φ_K̄ = [m]` back to `F` (round-trip + base-change faithfulness). The deep inputs are Q1's
fixed-field descent and Q3's full base-changed-pullback equivariance; the whole chain is isolated
here as a single `sorry`. -/
theorem rationalDualCompose_of_charZero {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) :
    ∃ (n : ℤ) (hn : n ≠ 0) (ρ : EC.Isogeny W₂ W₁),
      ρ.compose φ = EC.Isogeny.mulByInt W₁ hn := by
  sorry

/-- **DUAL-Q4 headline** (Silverman III.6.1, char-0 case): every isogeny over a char-0 field has an
`F`-rational dual — i.e. `UniversalDualWitness F` holds. Proof route: base-change each isogeny to
`AlgebraicClosure F`, take the dual there (existing K̄ machinery; char 0 ⟹ separable), and descend
to `F` by Galois-invariance + uniqueness (DUAL-Q1–Q3). Scaffold: filled across the DUAL-DESCENT
tickets.

**Residual.** By `hasDualWitness_of_compose` (DUAL-Q4, proven), it suffices to produce, for every
`φ`, an `F`-rational reverse isogeny `ρ` with `ρ ∘ φ = [deg φ]` — packaged as the predicate
`RationalDualCompose F`. That existence is the assembled DUAL-Q1–Q3 chain (base-change to `K̄`, K̄
dual `exists_dual_of_pullbackEvaluation_general`, Galois-equivariance via `galEquivariant_of_compose`,
descent via `descendIsogeny`, and round-trip of `φ̂ ∘ φ = [m]`). Its deep inputs are exactly Q1's
fixed-field descent (`mem_range_functionField_baseChange_iff_fixed`'s `→`) and Q3's full
base-changed-pullback equivariance; it is isolated as the single residual below. -/
theorem universalDualWitness_of_charZero (F : Type*) [Field F] [DecidableEq F] [CharZero F] :
    UniversalDualWitness F := by
  intro W₁ W₂ _ _ φ
  obtain ⟨n, hn, ρ, hρ⟩ := rationalDualCompose_of_charZero φ
  exact ⟨hasDualWitness_of_compose hρ⟩

/-- Symmetry of `IsIsogenous` over a char-0 field — the LMFDB-label gate, discharged from the
headline. -/
theorem isIsogenous_symm_charZero {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (h : IsIsogenous W₁ W₂) : IsIsogenous W₂ W₁ :=
  h.symm_of (universalDualWitness_of_charZero F)

end HasseWeil.EC
