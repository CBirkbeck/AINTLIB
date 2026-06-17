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

The arc is landed end-to-end with the deep input now isolated to **one** named `sorry`:

* **DUAL-Q1** (`galActFunctionField` + API): the `Gal(L/F)`-action on `F(C_L)` via `σ ⊗ id` through
  `functionField_baseChange_tensorEquiv`, with `_id`/`_trans` and the *fixed-the-base-field* easy
  direction `galActFunctionField_fixes_baseChange` — **all axiom-clean**. The fixed-field
  characterization `mem_range_functionField_baseChange_iff_fixed` is **fully proved (both
  directions)**: its `→` is the self-contained Galois descent of the fraction field
  `F(C_L) = Frac(L ⊗_F F[C])` (ring descent `tensor_fixed_mem_range` + norm-denominator fraction lift
  `the_lift`), needing no base-change-of-`IsGalois` lemma.
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

/-! ### Galois descent of the fraction field (the `→` direction)

We discharge the descent `mem_range_functionField_baseChange_iff_fixed.mpr` self-contained at the
tensor level. The structure is the standard Galois descent of a vector space, lifted to fractions:

1. **Ring descent** (`tensor_fixed_mem_range`): for a free `F`-module `M` (here `F[C]`), a
   `Gal(L/F)`-fixed element of `L ⊗_F M` (for the action `σ ⊗ id`) lies in `1 ⊗ M`. Proof: choose an
   `F`-basis `b` of `M`; in the induced `L`-basis `1 ⊗ bᵢ` of `L ⊗_F M`, the action `σ ⊗ id` acts on
   the `L`-coordinates by `σ`, so each coordinate is `Gal`-fixed, hence in `F`
   (`IsGalois.mem_range_algebraMap_iff_fixed`); the element is then `1 ⊗ (∑ coord · bᵢ)`.
2. **Fraction lift** (`the_lift`): a `galActFrac`-fixed `y ∈ Frac(L ⊗_F F[C])` is `n/den` with `n`,
   `den` both `σ ⊗ id`-fixed in `L ⊗_F F[C]`. Proof: write `y = a/d`; take `den := ∏_σ (σ ⊗ id) d`
   (the norm; `Gal`-fixed by group translation) and `n := a · ∏_{σ≠1}(σ ⊗ id) d`; `n` is fixed
   because `algebraMap n = y · algebraMap den` is a product of fixed elements.
3. **Wiring**: transport `x` through `functionField_baseChange_tensorEquiv` and back via
   `tensorEquiv_symm_one_tmul`.

This avoids any base-change-of-`IsGalois` lemma (absent from mathlib) and stays within the explicit
`galActFrac`/`σ ⊗ id` action. -/

/-- The ring-level Galois action `σ ⊗ id` on `L ⊗_F F[C]` (the tensor side of `galActFrac`). -/
private noncomputable abbrev ringAct (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (σ : L ≃ₐ[F] L) :
    (L ⊗[F] C.toAffine.CoordinateRing) ≃ₐ[F] (L ⊗[F] C.toAffine.CoordinateRing) :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F) (A₁ := C.toAffine.CoordinateRing))

/-- Coordinate description of the `σ ⊗ id` action in the base-changed basis: the `i`-th `L`-coordinate
of `(σ ⊗ id) z` is `σ` of the `i`-th coordinate of `z`. Proven by tensor induction (the action is
`L`-semilinear with respect to `σ`). -/
private theorem repr_congr_apply (L : Type*) [Field L] [Algebra F L]
    (M : Type*) [AddCommGroup M] [Module F M] [Module.Free F M]
    (σ : L ≃ₐ[F] L) (z : L ⊗[F] M) (i : Module.Free.ChooseBasisIndex F M) :
    ((Module.Free.chooseBasis F M).baseChange L).repr
        ((TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl F M)) z) i
      = σ (((Module.Free.chooseBasis F M).baseChange L).repr z i) := by
  classical
  set b := Module.Free.chooseBasis F M
  set B := b.baseChange L
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul l m =>
      rw [TensorProduct.congr_tmul]
      simp only [AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply]
      rw [Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
        Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply, map_add, Finsupp.add_apply, map_add, hx, hy]

/-- **Ring descent** (free-module Galois descent): a `Gal(L/F)`-fixed element of `L ⊗_F M` (for the
`σ ⊗ id` action, `M` a free `F`-module) lies in the image of `1 ⊗ -`. -/
private theorem tensor_fixed_mem_range (L : Type*) [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (M : Type*) [AddCommGroup M] [Module F M] [Module.Free F M]
    (z : L ⊗[F] M)
    (hz : ∀ σ : L ≃ₐ[F] L,
      (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl F M)) z = z) :
    ∃ m : M, (1 : L) ⊗ₜ[F] m = z := by
  classical
  set b := Module.Free.chooseBasis F M with hb
  set B := b.baseChange L with hBdef
  set c : Module.Free.ChooseBasisIndex F M →₀ L := B.repr z with hc
  have hfix : ∀ i, ∀ σ : L ≃ₐ[F] L, σ (c i) = c i := by
    intro i σ
    have := repr_congr_apply L M σ z i
    rw [hz σ] at this
    exact this.symm
  have hrange : ∀ i, c i ∈ Set.range (algebraMap F L) := fun i =>
    (IsGalois.mem_range_algebraMap_iff_fixed (c i)).2 (hfix i)
  choose g hg using hrange
  set c' : Module.Free.ChooseBasisIndex F M →₀ F :=
    { support := c.support
      toFun := fun i => g i
      mem_support_toFun := by
        intro i
        rw [Finsupp.mem_support_iff]
        constructor
        · intro h hgi; apply h; rw [← hg i, hgi, map_zero]
        · intro h hci; apply h
          have : algebraMap F L (g i) = 0 := by rw [hg i, hci]
          exact (FaithfulSMul.algebraMap_injective F L) (by rw [this, map_zero]) } with hc'
  have hzc : B.repr z = c'.mapRange (algebraMap F L) (map_zero _) := by
    ext i; simp only [Finsupp.mapRange_apply]; show c i = algebraMap F L (g i); rw [hg i]
  refine ⟨Finsupp.linearCombination F b c', ?_⟩
  have hz2 : z = Finsupp.linearCombination L B (B.repr z) := (B.linearCombination_repr z).symm
  rw [hz2, hzc, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by intro i; simp)]
  rw [show ((1 : L) ⊗ₜ[F] c'.sum fun i a => a • b i)
      = (TensorProduct.mk F L M 1) (c'.sum fun i a => a • b i) from rfl]
  rw [Finsupp.sum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  show (TensorProduct.mk F L M 1) (c' i • b i) = (algebraMap F L (c' i)) • B i
  rw [TensorProduct.mk_apply, Module.Basis.baseChange_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]

/-- The algebra-side `σ ⊗ id` (`ringAct`) agrees with the linear-side `σ ⊗ id` as a function. -/
private theorem congr_alg_eq_lin (L : Type*) [Field L] [Algebra F L]
    (M : Type*) [CommRing M] [Algebra F M]
    (σ : L ≃ₐ[F] L) (z : L ⊗[F] M) :
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F) (A₁ := M))) z
      = (TensorProduct.congr σ.toLinearEquiv (LinearEquiv.refl F M)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul l m => rw [Algebra.TensorProduct.congr_apply]; simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Ring descent specialized to the coordinate ring and the `ringAct` (`σ ⊗ id`) action. -/
private theorem tensor_ringAct_fixed_mem_range (C : SmoothPlaneCurve F)
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (z : L ⊗[F] C.toAffine.CoordinateRing)
    (hz : ∀ σ : L ≃ₐ[F] L, ringAct C L σ z = z) :
    ∃ m : C.toAffine.CoordinateRing, (1 : L) ⊗ₜ[F] m = z := by
  apply tensor_fixed_mem_range L C.toAffine.CoordinateRing z
  intro σ
  rw [← congr_alg_eq_lin L C.toAffine.CoordinateRing σ z]
  exact hz σ

/-- `galActFrac` carries the `algebraMap` of a tensor element `b` to the `algebraMap` of `ringAct b`
(the defining compatibility of `IsFractionRing.algEquivOfAlgEquiv`). -/
private theorem galActFrac_algebraMap (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    (σ : L ≃ₐ[F] L) (b : L ⊗[F] C.toAffine.CoordinateRing) :
    letI := C.isDomain_tensorCoordRing L
    galActFrac C L σ (algebraMap (L ⊗[F] C.toAffine.CoordinateRing) _ b)
      = algebraMap _ _ (ringAct C L σ b) := by
  letI := C.isDomain_tensorCoordRing L
  unfold galActFrac ringAct
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]

/-- The norm `∏_σ (σ ⊗ id) d` is `Gal(L/F)`-fixed (group-translation invariance of the product). -/
private theorem norm_fixed (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (d : L ⊗[F] C.toAffine.CoordinateRing) (τ : L ≃ₐ[F] L) :
    ringAct C L τ (∏ σ : L ≃ₐ[F] L, ringAct C L σ d) = ∏ σ : L ≃ₐ[F] L, ringAct C L σ d := by
  classical
  unfold ringAct
  rw [map_prod]
  have step : ∀ σ : L ≃ₐ[F] L,
      (Algebra.TensorProduct.congr τ (AlgEquiv.refl (R := F)
          (A₁ := C.toAffine.CoordinateRing)))
        ((Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F)
          (A₁ := C.toAffine.CoordinateRing))) d)
      = (Algebra.TensorProduct.congr (σ.trans τ) (AlgEquiv.refl (R := F)
          (A₁ := C.toAffine.CoordinateRing))) d := by
    intro σ; rw [← AlgEquiv.trans_apply, ← congr_id_trans]
  simp_rw [step]
  rw [← Equiv.prod_comp (Equiv.mulLeft τ) (fun σ => (Algebra.TensorProduct.congr σ
      (AlgEquiv.refl (R := F) (A₁ := C.toAffine.CoordinateRing))) d)]
  rfl

/-- **Fraction lift**: a `galActFrac`-fixed element of `Frac(L ⊗_F F[C])` is a ratio `n/den` of two
`σ ⊗ id`-fixed elements of `L ⊗_F F[C]` (with `den ≠ 0`). The denominator is the norm of an arbitrary
denominator; the numerator is forced fixed by the fixed quotient. -/
private theorem the_lift (C : SmoothPlaneCurve F) (L : Type*) [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (y : letI := C.isDomain_tensorCoordRing L
         FractionRing (L ⊗[F] C.toAffine.CoordinateRing))
    (hy : letI := C.isDomain_tensorCoordRing L
          ∀ σ : L ≃ₐ[F] L, galActFrac C L σ y = y) :
    letI := C.isDomain_tensorCoordRing L
    ∃ n den : L ⊗[F] C.toAffine.CoordinateRing,
      (∀ σ, ringAct C L σ n = n) ∧ (∀ σ, ringAct C L σ den = den) ∧
      (algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
          (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) den ≠ 0) ∧
      y = algebraMap _ (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) n
          / algebraMap _ (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) den := by
  letI := C.isDomain_tensorCoordRing L
  classical
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective
    (A := L ⊗[F] C.toAffine.CoordinateRing) y
  set den := ∏ σ : L ≃ₐ[F] L, ringAct C L σ d with hden
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hden0B : den ≠ 0 := by
    rw [hden]; apply Finset.prod_ne_zero_iff.2; intro σ _ h
    exact hd0 ((ringAct C L σ).injective (by rw [h, map_zero]))
  have hdenmap0 : algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
      (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) den ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _
      (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)))).2 hden0B
  have hdmap0 : algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
      (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _
      (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)))).2 hd0
  set P := ∏ σ ∈ (Finset.univ.erase (1 : L ≃ₐ[F] L)), ringAct C L σ d with hP
  have hdenP : den = d * P := by
    rw [hden, hP, ← Finset.mul_prod_erase Finset.univ (fun σ => ringAct C L σ d)
      (Finset.mem_univ (1 : L ≃ₐ[F] L))]
    congr 1
    show (Algebra.TensorProduct.congr (1 : L ≃ₐ[F] L) (AlgEquiv.refl (R := F)
        (A₁ := C.toAffine.CoordinateRing))) d = d
    rw [show (1 : L ≃ₐ[F] L) = AlgEquiv.refl from rfl, Algebra.TensorProduct.congr_refl]
    rfl
  have hnmap : ∀ a' : L ⊗[F] C.toAffine.CoordinateRing,
      algebraMap (L ⊗[F] C.toAffine.CoordinateRing)
        (FractionRing (L ⊗[F] C.toAffine.CoordinateRing)) (a' * P)
      = (algebraMap _ _ a' / algebraMap _ _ d) * algebraMap _ _ den := by
    intro a'
    rw [hdenP, map_mul, map_mul]
    field_simp
  refine ⟨a * P, den, ?_, fun τ => norm_fixed C L d τ, hdenmap0,
    by rw [hnmap a, mul_div_assoc, div_self hdenmap0, mul_one]⟩
  intro τ
  apply IsFractionRing.injective (L ⊗[F] C.toAffine.CoordinateRing)
    (FractionRing (L ⊗[F] C.toAffine.CoordinateRing))
  rw [← galActFrac_algebraMap, hnmap a, map_mul, hy τ, galActFrac_algebraMap,
    norm_fixed C L d τ, ← hnmap]

/-- **DUAL-Q1(c), the fixed-field characterization** (`L/F` finite Galois): an element of `F(C_L)`
is fixed by *every* `galActFunctionField C L σ` iff it lies in the image of `F(C)` under the
base-change embedding `functionFieldMap`.

The `←` direction is `galActFunctionField_fixes_baseChange` (proved). The `→` direction is the
genuine **Galois descent of the fraction field** `F(C_L) = FractionRing(L ⊗_F F[C])`: a
`Gal(L/F)`-invariant element of the fraction field descends to `F(C)`. Over the domain `L ⊗_F F[C]`
this is the (free-module) Galois descent of `F[C]` (`tensor_fixed_mem_range`); the lift from the
domain to its fraction field is the norm-denominator trick (`the_lift`). The two are wired through
`functionField_baseChange_tensorEquiv`/`tensorEquiv_symm_one_tmul`; see the section above for the
self-contained development (no base-change-of-`IsGalois` lemma needed). -/
theorem mem_range_functionField_baseChange_iff_fixed (C : SmoothPlaneCurve F)
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (x : (C.baseChange L).FunctionField) :
    (∃ f : C.FunctionField, C.functionFieldMap L f = x) ↔
      ∀ σ : L ≃ₐ[F] L, galActFunctionField C L σ x = x := by
  constructor
  · rintro ⟨f, rfl⟩ σ
    exact galActFunctionField_fixes_baseChange C L σ f
  · intro hfixed
    letI := C.isDomain_tensorCoordRing L
    classical
    -- transport `x` to the tensor fraction field
    set y := (C.functionField_baseChange_tensorEquiv L) x with hy_def
    -- `y` is `galActFrac`-fixed
    have hyfix : ∀ σ : L ≃ₐ[F] L, galActFrac C L σ y = y := by
      intro σ
      have hx := hfixed σ
      have hrel : galActFunctionField C L σ x
          = (C.functionField_baseChange_tensorEquiv L).symm
              (galActFrac C L σ ((C.functionField_baseChange_tensorEquiv L) x)) := rfl
      rw [hrel] at hx
      apply (C.functionField_baseChange_tensorEquiv L).symm.injective
      rw [hx, hy_def, AlgEquiv.symm_apply_apply]
    -- fraction lift: `y = n / den` with `n`, `den` both `σ ⊗ id`-fixed
    obtain ⟨n, den, hnf, hdenf, _hdenne, hydiv⟩ := the_lift C L y hyfix
    -- ring descent: `n = 1 ⊗ mn`, `den = 1 ⊗ md`
    obtain ⟨mn, hmn⟩ := tensor_ringAct_fixed_mem_range C L n hnf
    obtain ⟨md, hmd⟩ := tensor_ringAct_fixed_mem_range C L den hdenf
    -- the descended function is `algebraMap mn / algebraMap md`
    refine ⟨algebraMap C.toAffine.CoordinateRing C.FunctionField mn
        / algebraMap C.toAffine.CoordinateRing C.FunctionField md, ?_⟩
    rw [map_div₀]
    have hx_eq : x = (C.functionField_baseChange_tensorEquiv L).symm y := by
      rw [hy_def, AlgEquiv.symm_apply_apply]
    rw [hx_eq, hydiv, map_div₀]
    congr 1
    · rw [← hmn, tensorEquiv_symm_one_tmul C L mn]
    · rw [← hmd, tensorEquiv_symm_one_tmul C L md]

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
