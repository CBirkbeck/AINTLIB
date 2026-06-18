import HasseWeil.EC.IsogenyAG.IsogenyClass
import HasseWeil.EC.IsogenyAG.MulByIntBasepoint
import HasseWeil.EC.IsogenyAG.TwistedFactorization
import HasseWeil.EC.IsogenyAG.BaseChange
import HasseWeil.EC.IsogenyAG.TwoCurveDualRange
import HasseWeil.EC.IsogenyAG.TwoCurveNormConorm
import HasseWeil.EC.IsogenyAG.TwoCurveGroupHom
import HasseWeil.EC.IsogenyKernelTwoCurve
import HasseWeil.WeilPairing.TwoCurveGenericCovariance
import HasseWeil.EC.IsogenyAG.TwoCurvePointImage
import HasseWeil.Curves.CurveMapBaseChange
import HasseWeil.Curves.NoFinitePolesBridge
import HasseWeil.Curves.OrdAtInftyBaseChange
import HasseWeil.Curves.OrdAtInftyRamification

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
  proved — **axiom-clean** (Q1's `sorry` is gone).
* **DUAL-Q3** (`galEquivariant_of_compose`): from the defining identity `φ* ∘ φ̂* = [m]*` and
  injectivity of `φ*`, the dual pullback is equivariant — **axiom-clean** (the full base-changed-pullback
  equivariance feeding it is one of the sub-gaps inside the single residual below).
* **DUAL-Q4** (`hasDualWitness_of_compose` + `universalDualWitness_of_charZero`): a reverse isogeny
  `ρ` over `F` with `ρ ∘ φ = [deg φ]` yields `HasDualWitness φ` — **axiom-clean**. The headline
  `rationalDualCompose_of_charZero` is now a **thin assembly** over its proven pieces:
  - `isSeparable_of_charZero` (char-0 ⟹ separable) — **proved, axiom-clean**;
  - `rationalDualCompose_of_hasMulByIntDualWitness` (from an `F`-rational `[n]`-witness, the reverse
    isogeny with `ρ ∘ φ = [n]` is purely formal) — **proved, axiom-clean**;
  - `hasMulByIntDualWitness_of_rangeIncl` (the basepoint leaf, `mulByIntBasepoint_holds` +
    `reflects_ordAtInfty`) — **proved**;
  and the range inclusion `Im([deg φ]*) ⊆ Im(φ*)` over `F` (`rationalRangeIncl_of_separable`), a thin
  consequence of the proven elementwise descent `rangeIncl_of_descentData` over the single named leaf
  `exists_descentData_of_separable`.

* **MOVE 1 — field-of-definition over `K̄` (this pass, axiom-clean)**: the descent's
  field-of-definition gap is now discharged inside `K̄ = AlgebraicClosure F`. In char 0 `K̄/F` is
  Galois (`instIsGalois_algebraicClosure`); a finite set of `K̄`-elements lies in a finite Galois
  intermediate field `L ⊆ K̄` (`exists_finiteGalois_fieldOfDefinition`, via mathlib's
  `FiniteGaloisIntermediateField.adjoin`); and `Gal(K̄/F)`-fixedness descends to `Gal(L/F)`-fixedness
  (`galFixed_of_galFixed_top`, via `AlgEquiv.restrictNormalHom_surjective`). The wrapper
  `someDescentData_of_overKbar` threads the (equal) universe. So the residual is no longer "field of
  definition".

* **TWO-CURVE BASE-CHANGE via `ofEquation` (this pass, axiom-clean)**: the `DescentData`'s two-curve
  base-change is now built CoordHom-free in the `TwoCurveBaseChange` namespace. The earlier framing —
  "`psiL = baseChangeAlgHom cd L` needs a `CoordHom` for `φ`, which a general `EC.Isogeny` lacks" — is
  superseded: `TwoCurveBaseChange.bcIsog` builds `φ_L : E₁_L → E₂_L` over a *general* finite `L`
  directly from the pullback generator images `functionFieldMap (φ^* x_gen₂/y_gen₂)` via the two-curve
  `EC.Isogeny.ofEquation` builder. The transcendence over a non-algebraically-closed `L` is supplied
  by `ordAtInfty_eq_zero_of_isAlgebraic_constants` (order `0` for elements algebraic over the constant
  field). This furnishes — all axiom-clean — `ψ_L` (`psiL`), `[m]_L*` (`mPbL`), the base-change
  naturalities (`psiL_nat`, `mPbL_nat`), `ψ_L`'s injectivity (`psiL_injective`), and `ψ_L`'s **full
  `Gal(L/F)`-equivariance** (`psiL_galEquivariant`, via the `σ`-semilinearity
  `galActFunctionField_algebraMap_L` + the base-`L` extensionality `ringHom_ext_baseL`). So
  `descentData_over_kbar_intermediate` is **sorry-free**, consuming a single isolated leaf.

  **The single remaining `sorry`** is now narrowed to exactly `twoCurveKbarRangeIncl_descended`: the
  **`L`-level two-curve `K̄`-dual range inclusion** `Im([deg φ]_L*) ⊆ Im(ψ_L)` over a concrete finite
  Galois `L ⊆ K̄`. This is Silverman III.6.1's deep input (`DualGaloisData.hincl`, via III.4.10c
  fixed-field) for a *two-curve* `φ_K̄ : E₁_K̄ → E₂_K̄`; the project's K̄-dual machinery
  (`exists_dual_of_pullbackEvaluation_general`) is endomorphism-only, so this inclusion is the
  irreducible remaining infrastructure. The factorization downstream of the inclusion
  (`CurveMap.factorThroughPullback`) is already axiom-clean. See the declaration (REVIEW-PENDING). The
  label gate is discharged ungated in `IsogenyClassLabel.lean` (`*_charZero`).
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

set_option synthInstance.maxHeartbeats 400000 in
-- Importing the two-curve fixed-field machinery (`TwoCurveDualRange`) transitively brings the
-- kernel-translation `MulSemiringAction` on `FunctionField` into scope, which expands instance
-- search through the `Submodule` lattice during this `AlgHom`-structure elaboration — the same
-- `synthInstance` pressure handled identically in `EC/KernelCountGeneral.lean`.
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
  map_one' := (descendFun_eq_iff L hξ 1 1).2 (by
    simp only [map_one])
  map_mul' a b := (descendFun_eq_iff L hξ (a * b) _).2 (by
    simp only [map_mul, functionFieldMap_descendFun])
  map_zero' := (descendFun_eq_iff L hξ 0 0).2 (by
    simp only [map_zero])
  map_add' a b := (descendFun_eq_iff L hξ (a + b) _).2 (by
    simp only [map_add, functionFieldMap_descendFun])
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

/-! ### The elementwise Galois descent of the range inclusion (route steps 2–4, proven)

The `F`-level range inclusion `Im([m]*) ⊆ Im(φ*)` is descended *elementwise* from a finite Galois
level `L/F`, exploiting the now-fully-proven DUAL-Q1 fixed-field characterization
(`mem_range_functionField_baseChange_iff_fixed`). The mechanism (Silverman III.6.1, descent half):

1. **(K̄/L input, isolated)** Over a finite Galois `L/F`, the `L`-base-change `ψ_L` of `φ*` (an
   `F`-algebra hom `F(C₂_L) → F(C₁_L)`, `Gal(L/F)`-equivariant, injective, natural with `φ*`) admits
   the `L`-level range inclusion `Im([m]_L*) ⊆ Im(ψ_L)`. (This is the two-curve `K̄` dual descended to
   `L`; it is the genuine deep residual — see `DescentData` below.)
2. **(proven here)** For `z = [m]_F* u`, naturality of `[m]` gives
   `functionFieldMap z = [m]_L* (functionFieldMap u) ∈ Im([m]_L*) ⊆ Im(ψ_L)`, so
   `functionFieldMap z = ψ_L ĝ` for some `ĝ ∈ F(C₂_L)`.
3. **(proven here)** `functionFieldMap z` is `Gal(L/F)`-fixed (it is a base-change image); `ψ_L` is
   equivariant and injective, so `ĝ` is `Gal(L/F)`-fixed.
4. **(proven here)** By DUAL-Q1 `ĝ = functionFieldMap g` for `g ∈ F(C₂)`; naturality
   `functionFieldMap (φ* g) = ψ_L (functionFieldMap g) = ψ_L ĝ = functionFieldMap z`, and
   injectivity of `functionFieldMap`, give `φ* g = z`. Hence `z ∈ Im(φ*)`.

`DescentData` packages the step-1 input; `rangeIncl_of_descentData` is the proven descent (steps
2–4). -/

/-- **The `K̄`/finite-Galois descent input** for the range inclusion `Im([m]*) ⊆ Im(φ*)` over `F`
(the isolated deep residual of Silverman III.6.1, descent half). For a curve map `φ* : F(C₂) → F(C₁)`
(the pullback of `φ : C₁ → C₂`) and a nonconstant endomorphism pullback `mPb : F(C₁) → F(C₁)`
(Silverman takes `mPb = [m]*`, `m = deg φ`), this bundles, over a *finite Galois* `L/F`:

* `psiL` — the `L`-base-change `ψ_L : F(C₂_L) → F(C₁_L)` of `φ*`;
* `mPbL` — the `L`-base-change `[m]_L* : F(C₁_L) → F(C₁_L)` of `mPb`;
* `hpsiL_equiv` — `ψ_L` is `Gal(L/F)`-equivariant;
* `hpsiL_inj` — `ψ_L` is injective (it is a base-changed field-pullback);
* `hpsiL_nat` — base-change naturality of `φ*`: `functionFieldMap ∘ φ* = ψ_L ∘ functionFieldMap`;
* `hmPbL_nat` — base-change naturality of `mPb`: `functionFieldMap ∘ mPb = mPb_L ∘ functionFieldMap`;
* `hLincl` — the **`L`-level range inclusion** `Im([m]_L*) ⊆ Im(ψ_L)` (the two-curve `K̄` dual,
  descended to `L`).

The two genuine mathlib gaps of Silverman III.6.1 (the general two-curve base-change of the isogeny
to `K̄`/`L`, and the field-of-definition reduction of the `K̄`-dual to a finite Galois `L/F`) are
exactly what is needed to *construct* this datum; everything downstream is proven
(`rangeIncl_of_descentData`). -/
structure DescentData {C₁ C₂ : SmoothPlaneCurve F}
    (φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField)
    (mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField)
    (L : Type*) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L] where
  /-- The `L`-base-change `ψ_L : F(C₂_L) → F(C₁_L)` of `φ*`. -/
  psiL : (C₂.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField
  /-- The `L`-base-change `[m]_L* : F(C₁_L) → F(C₁_L)` of `mPb = [m]*`. -/
  mPbL : (C₁.baseChange L).FunctionField →ₐ[F] (C₁.baseChange L).FunctionField
  /-- `ψ_L` is `Gal(L/F)`-equivariant. -/
  hpsiL_equiv : GalEquivariant L psiL
  /-- `ψ_L` is injective. -/
  hpsiL_inj : Function.Injective psiL
  /-- Base-change naturality of `φ*`. -/
  hpsiL_nat : ∀ g : C₂.FunctionField,
    C₁.functionFieldMap L (φPb g) = psiL (C₂.functionFieldMap L g)
  /-- Base-change naturality of `mPb = [m]*`. -/
  hmPbL_nat : ∀ u : C₁.FunctionField,
    C₁.functionFieldMap L (mPb u) = mPbL (C₁.functionFieldMap L u)
  /-- The `L`-level range inclusion `Im([m]_L*) ⊆ Im(ψ_L)` (the descended `K̄` dual). -/
  hLincl : mPbL.range ≤ psiL.range

omit [DecidableEq F] in
/-- **The elementwise Galois descent of the range inclusion** (Silverman III.6.1, descent half;
route steps 2–4, fully proven). From a `DescentData` over a finite Galois `L/F`, the `F`-level range
inclusion `Im(mPb) ⊆ Im(φ*)` follows. Axiom-clean: the only deep input is the `DescentData` (the
`L`-level range inclusion + the two-curve base-change naturality); the descent itself is the DUAL-Q1
fixed-field characterization plus injectivity. -/
theorem rangeIncl_of_descentData {C₁ C₂ : SmoothPlaneCurve F}
    {φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField}
    {mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField}
    {L : Type*} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (d : DescentData φPb mPb L) :
    mPb.range ≤ φPb.range := by
  rintro z ⟨u, rfl⟩
  -- Step 2: `functionFieldMap (mPb u)` lies in `Im([m]_L*) ⊆ Im(ψ_L)`.
  have hz_mem : C₁.functionFieldMap L (mPb u) ∈ d.psiL.range := by
    apply d.hLincl
    rw [d.hmPbL_nat u]
    exact ⟨C₁.functionFieldMap L u, rfl⟩
  obtain ⟨ĝ, hĝ⟩ := hz_mem
  -- normalise the witness to `AlgHom`-application form
  have hĝ' : d.psiL ĝ = C₁.functionFieldMap L (mPb u) := hĝ
  -- Step 3: `ĝ` is `Gal(L/F)`-fixed (since `ψ_L ĝ = functionFieldMap (mPb u)` is fixed and `ψ_L`
  -- is equivariant + injective).
  have hĝ_fixed : ∀ σ : L ≃ₐ[F] L, galActFunctionField C₂ L σ ĝ = ĝ := by
    intro σ
    apply d.hpsiL_inj
    rw [d.hpsiL_equiv σ ĝ, hĝ', galActFunctionField_fixes_baseChange]
  -- Step 4: by DUAL-Q1, `ĝ = functionFieldMap g` for `g ∈ F(C₂)`.
  obtain ⟨g, hg⟩ := (mem_range_functionField_baseChange_iff_fixed C₂ L ĝ).2 hĝ_fixed
  -- and `φ* g = mPb u` by injectivity of `functionFieldMap` and naturality.
  refine ⟨g, C₁.functionFieldMap_injective L ?_⟩
  show C₁.functionFieldMap L (φPb g) = C₁.functionFieldMap L (mPb u)
  rw [d.hpsiL_nat g, hg, hĝ']

/-- **A `DescentData` together with its finite Galois field of definition** — the existential
output of the isolated residual `exists_descentData_of_separable`, bundling `L` and its
`Field`/`Algebra`/`FiniteDimensional`/`IsGalois` instances as fields (so that `DescentData`'s
instance arguments are available when consuming it). -/
structure SomeDescentData.{w} {C₁ C₂ : SmoothPlaneCurve F}
    (φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField)
    (mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField) where
  /-- The finite Galois field of definition `L/F`. -/
  L : Type w
  /-- `L` is a field. -/
  [fieldL : Field L]
  /-- `L` is an `F`-algebra. -/
  [algL : Algebra F L]
  /-- `L/F` is finite. -/
  [finL : FiniteDimensional F L]
  /-- `L/F` is Galois. -/
  [galL : IsGalois F L]
  /-- The descent data over `L`. -/
  data : DescentData (C₁ := C₁) (C₂ := C₂) φPb mPb L

universe u

/-! ### MOVE 1 — the field-of-definition descent over `K̄ = AlgebraicClosure F`

The descent of the range inclusion runs over a *finite* Galois `L/F`, but the `K̄`-dual lives over
`K̄ = AlgebraicClosure F`, which is infinite. The bridge — "a finite collection of `K̄`-elements is
defined over a finite Galois subextension `L/F`" — is supplied by mathlib's
`FiniteGaloisIntermediateField.adjoin` (`FieldTheory/Galois/GaloisClosure.lean`): in a Galois
extension `K̄/F`, the normal closure of `F(s)` for a finite `s : Set K̄` is a finite Galois
intermediate field containing `s`. In characteristic zero `K̄/F` is Galois
(`instIsGalois_algebraicClosure`, from `IsAlgClosure.normal` + `IsAlgClosure.separable`).

The descent's Galois-invariance step needs "fixed by all of `Gal(K̄/F)` ⟹ fixed by all of
`Gal(L/F)`" for `x` in such an `L`; this is `galFixed_of_galFixed_top` (the surjectivity of
`AlgEquiv.restrictNormalHom` for the normal pair `L`, `K̄` plus the commutation
`AlgEquiv.restrictNormal_commutes`). These are the two reusable pieces of MOVE 1; they eliminate the
*field-of-definition* sub-gap, leaving the residual exactly the **two-curve base-change** leaf. -/

section FieldOfDefinition

variable {E : Type*} [Field E]

/-- **Characteristic zero ⟹ `K̄/F` is Galois.** For a char-0 field `F`, the algebraic closure
`K̄ = AlgebraicClosure F` is a Galois extension: it is normal (`IsAlgClosure.normal`) and separable
(`IsAlgClosure.separable`, char-0). Packaged as an instance so the field-of-definition API
(`FiniteGaloisIntermediateField.adjoin`, which requires `[IsGalois F K̄]`) is available. -/
instance instIsGalois_algebraicClosure [CharZero E] :
    IsGalois E (AlgebraicClosure E) := inferInstance

/-- **The abstract Galois-fixed descent** (the field-of-definition invariance step). For a normal
extension `K/F` and a normal intermediate field `L`, an element `x : L` whose image in `K` is fixed
by *every* `σ ∈ Gal(K/F)` is fixed by *every* `τ ∈ Gal(L/F)`. Proof: every `τ` lifts to some `σ` by
`AlgEquiv.restrictNormalHom_surjective` (both `L/F` and `K/F` normal), and
`AlgEquiv.restrictNormal_commutes` transports the fixed-ness down through the injective inclusion
`algebraMap L K`.

This is the order-theoretic heart of MOVE 1: it lets a `Gal(K̄/F)`-fixed function on the curve over a
finite Galois `L ⊆ K̄` be recognised as `Gal(L/F)`-fixed, which is the hypothesis of the proven
fixed-field characterization `mem_range_functionField_baseChange_iff_fixed`. -/
theorem galFixed_of_galFixed_top {K : Type*} [Field K] [Algebra E K] [Normal E K]
    (L : IntermediateField E K) [Normal E L] (x : L)
    (hx : ∀ σ : K ≃ₐ[E] K, σ (algebraMap L K x) = algebraMap L K x)
    (τ : L ≃ₐ[E] L) : τ x = x := by
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := K) τ
  apply (algebraMap L K).injective
  rw [show AlgEquiv.restrictNormalHom (F := E) L σ = σ.restrictNormal L from rfl,
    AlgEquiv.restrictNormal_commutes, hx]

/-- **The finite Galois field of definition of a finite set of `K̄`-elements** (MOVE 1). In char 0,
for a finite `s : Set K̄` there is a finite Galois extension `L/F` (concretely the normal closure of
`F(s)` inside `K̄`, `FiniteGaloisIntermediateField.adjoin`) containing `s` — so any datum built from
finitely many algebraic elements of `K̄` is defined over a *finite* Galois `L/F`. This discharges the
field-of-definition half of the descent: the (infinite) `K̄`-dual descends to a finite Galois `L`. -/
theorem exists_finiteGalois_fieldOfDefinition [CharZero E]
    (s : Set (AlgebraicClosure E)) (hs : s.Finite) :
    ∃ (L : IntermediateField E (AlgebraicClosure E)),
      FiniteDimensional E L ∧ IsGalois E L ∧ s ⊆ (L : Set (AlgebraicClosure E)) := by
  haveI : Finite s := hs
  refine ⟨(FiniteGaloisIntermediateField.adjoin E s).toIntermediateField,
    inferInstance, inferInstance, ?_⟩
  exact FiniteGaloisIntermediateField.subset_adjoin E s

end FieldOfDefinition

/-! ### MOVE 2 — the infinite-Galois tower descent `K̄ → F`

The descent of the range inclusion (`rangeIncl_of_descentData`) runs over a *finite* Galois `L/F`,
which forces the genuine geometric realization of `φ_L` over that `L` (the `twoCurveGeometricDualData`
leaf).  MOVE 2 supplies an alternative that descends the **`K̄`-direct** range inclusion
(`ecIsog_mulByInt_deg_rangeIncl_of_charZero`, over `K̄ = AlgebraicClosure F`) all the way to `F` in
one step, *bypassing* the finite-`L` geometric realization.

The new content is the **tower fact**: every element of `K̄ ⊗_F R` lives over a finite Galois
intermediate field `M ⊆ K̄` (`exists_finiteGalois_towerTensorIncl_range`), so a `Gal(K̄/F)`-fixed
element descends to `F` by reduction to the proven finite descent (`tensor_ringAct_fixed_mem_range`
+ `the_lift`).  Concretely this furnishes the **infinite-Galois fixed-field characterization**
`mem_range_functionField_baseChange_iff_fixed_kbar` (the `L = K̄` analogue of the finite
`mem_range_functionField_baseChange_iff_fixed`). -/

section TowerDescent

variable {F : Type u} [Field F]

/-- The `F`-algebra inclusion `M ⊗_F R → K̄ ⊗_F R` induced by `IntermediateField.val M : M →ₐ[F] K̄`
(`M ⊆ K̄ = AlgebraicClosure F` an intermediate field) tensored with the identity on `R`. -/
noncomputable def towerTensorIncl (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) :
    (M ⊗[F] R) →ₐ[F] (AlgebraicClosure F ⊗[F] R) :=
  Algebra.TensorProduct.map (M.val) (AlgHom.id F R)

@[simp] theorem towerTensorIncl_tmul (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) (m : M) (r : R) :
    towerTensorIncl R M (m ⊗ₜ[F] r) = (m : AlgebraicClosure F) ⊗ₜ[F] r :=
  Algebra.TensorProduct.map_tmul _ _ _ _

/-- `towerTensorIncl` is injective: it is `val M ⊗ id` with `val M` injective and everything flat
over the field `F`. -/
theorem towerTensorIncl_injective (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) :
    Function.Injective (towerTensorIncl R M) := by
  have hfun : ⇑(towerTensorIncl R M) =
      ⇑(TensorProduct.map (M.val.toLinearMap) (LinearMap.id (R := F) (M := R))) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m r => simp [towerTensorIncl_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hfun]
  exact TensorProduct.map_injective_of_flat_flat _ _
    (M.val.injective) Function.injective_id

/-- **Equivariance of the tower inclusion.** If `σ : K̄ ≃ₐ[F] K̄` restricts to `τ : M ≃ₐ[F] M`
(i.e. `σ (m : K̄) = (τ m : K̄)` for all `m ∈ M`), then `towerTensorIncl` intertwines the `σ ⊗ id`
action upstairs with the `τ ⊗ id` action downstairs. -/
theorem towerTensorIncl_congr (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F)) (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (τ : M ≃ₐ[F] M) (hστ : ∀ m : M, σ (m : AlgebraicClosure F) = (τ m : AlgebraicClosure F))
    (z : M ⊗[F] R) :
    towerTensorIncl R M
        ((Algebra.TensorProduct.congr τ (AlgEquiv.refl (R := F) (A₁ := R))) z) =
      (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := F) (A₁ := R)))
        (towerTensorIncl R M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m r =>
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
        towerTensorIncl_tmul, towerTensorIncl_tmul, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul]
      simp only [AlgEquiv.coe_refl, id_eq, AlgEquiv.coe_algHom]
      rw [hστ m]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- A finite-sum `∑_{p∈S} p.1 ⊗ p.2` of `K̄ ⊗ R` whose scalars all lie in `M` is the
`towerTensorIncl`-image of the corresponding sum over `M`. -/
private theorem towerTensorIncl_finset_sum_mem_range (R : Type*) [CommRing R] [Algebra F R]
    (M : IntermediateField F (AlgebraicClosure F))
    (S : Finset (AlgebraicClosure F × R)) (hmem : ∀ p ∈ S, p.1 ∈ M) :
    (S.sum fun p => p.1 ⊗ₜ[F] p.2) ∈ Set.range (towerTensorIncl R M) := by
  classical
  refine ⟨S.attach.sum fun p => (⟨p.1.1, hmem p.1 p.2⟩ : M) ⊗ₜ[F] p.1.2, ?_⟩
  rw [map_sum, ← Finset.sum_attach S (fun p => p.1 ⊗ₜ[F] p.2)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [towerTensorIncl_tmul]

/-- **The tensor tower fact** (char 0): every element of `K̄ ⊗_F R` (`K̄ = AlgebraicClosure F`) is the
image, under `towerTensorIncl`, of an element of `M ⊗_F R` for some *finite Galois* intermediate
field `M ⊆ K̄`. The finitely many `K̄`-scalars in a finite-sum representation lie in a finite Galois
`M` (`exists_finiteGalois_fieldOfDefinition`). -/
theorem exists_finiteGalois_towerTensorIncl_range [CharZero F]
    (R : Type*) [CommRing R] [Algebra F R] (z : AlgebraicClosure F ⊗[F] R) :
    ∃ (M : IntermediateField F (AlgebraicClosure F)),
      FiniteDimensional F M ∧ IsGalois F M ∧ z ∈ Set.range (towerTensorIncl R M) := by
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  obtain ⟨M, hMfin, hMgal, hMsub⟩ :=
    exists_finiteGalois_fieldOfDefinition (E := F) (↑(S.image Prod.fst) : Set (AlgebraicClosure F))
      (S.image Prod.fst).finite_toSet
  refine ⟨M, hMfin, hMgal, ?_⟩
  rw [hS]
  exact towerTensorIncl_finset_sum_mem_range R M S (fun p hp =>
    hMsub (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst hp)))

/-- **The tensor tower fact for a pair** (char 0): two elements `z₁ z₂ ∈ K̄ ⊗_F R` both live over a
*common* finite Galois intermediate field `M ⊆ K̄`. The scalars of finite-sum representations of
*both* `z₁` and `z₂` lie in one finite Galois `M`. -/
theorem exists_finiteGalois_towerTensorIncl_range₂ [CharZero F]
    (R : Type*) [CommRing R] [Algebra F R] (z₁ z₂ : AlgebraicClosure F ⊗[F] R) :
    ∃ (M : IntermediateField F (AlgebraicClosure F)),
      FiniteDimensional F M ∧ IsGalois F M ∧
        z₁ ∈ Set.range (towerTensorIncl R M) ∧ z₂ ∈ Set.range (towerTensorIncl R M) := by
  classical
  obtain ⟨S₁, hS₁⟩ := TensorProduct.exists_finset z₁
  obtain ⟨S₂, hS₂⟩ := TensorProduct.exists_finset z₂
  obtain ⟨M, hMfin, hMgal, hMsub⟩ :=
    exists_finiteGalois_fieldOfDefinition (E := F)
      (↑((S₁ ∪ S₂).image Prod.fst) : Set (AlgebraicClosure F))
      ((S₁ ∪ S₂).image Prod.fst).finite_toSet
  have hmem : ∀ (S : Finset (AlgebraicClosure F × R)), S ⊆ S₁ ∪ S₂ → ∀ p ∈ S, p.1 ∈ M := by
    intro S hsub p hp
    exact hMsub (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.fst (hsub hp)))
  refine ⟨M, hMfin, hMgal, ?_, ?_⟩
  · rw [hS₁]; exact towerTensorIncl_finset_sum_mem_range R M S₁ (hmem S₁ Finset.subset_union_left)
  · rw [hS₂]; exact towerTensorIncl_finset_sum_mem_range R M S₂ (hmem S₂ Finset.subset_union_right)


/-- The fraction-field inclusion `Frac(M ⊗_F F[C]) → Frac(K̄ ⊗_F F[C])` induced by the injective
ring hom `towerTensorIncl` (`M ⊆ K̄ = AlgebraicClosure F`). The codomain is the tensor-fraction
presentation of `(C.baseChange K̄).FunctionField` (via `functionField_baseChange_tensorEquiv`). -/
noncomputable def fracTowerIncl (C : SmoothPlaneCurve F)
    (M : IntermediateField F (AlgebraicClosure F)) :
    letI := C.isDomain_tensorCoordRing M
    letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
    FractionRing (M ⊗[F] C.toAffine.CoordinateRing) →+*
      FractionRing (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing) :=
  letI := C.isDomain_tensorCoordRing M
  letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
  IsFractionRing.map (B := AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing)
    (j := (towerTensorIncl C.toAffine.CoordinateRing M).toRingHom)
    (towerTensorIncl_injective C.toAffine.CoordinateRing M)

/-- `fracTowerIncl` carries `algebraMap b` to `algebraMap (towerTensorIncl b)`. -/
theorem fracTowerIncl_algebraMap (C : SmoothPlaneCurve F)
    (M : IntermediateField F (AlgebraicClosure F)) (b : M ⊗[F] C.toAffine.CoordinateRing) :
    letI := C.isDomain_tensorCoordRing M
    letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
    fracTowerIncl C M (algebraMap (M ⊗[F] C.toAffine.CoordinateRing) _ b) =
      algebraMap (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing) _
        (towerTensorIncl C.toAffine.CoordinateRing M b) := by
  letI := C.isDomain_tensorCoordRing M
  letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
  unfold fracTowerIncl
  exact IsLocalization.map_eq _ b

/-- `fracTowerIncl` is injective: its domain `FractionRing (M ⊗ F[C])` is a field, and every ring
hom out of a field is injective. -/
theorem fracTowerIncl_injective (C : SmoothPlaneCurve F)
    (M : IntermediateField F (AlgebraicClosure F)) :
    letI := C.isDomain_tensorCoordRing M
    letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
    Function.Injective (fracTowerIncl C M) := by
  letI := C.isDomain_tensorCoordRing M
  letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
  exact (fracTowerIncl C M).injective

/-- **Equivariance of `fracTowerIncl`.** If `σ : K̄ ≃ₐ[F] K̄` restricts to `τ : M ≃ₐ[F] M`, then
`fracTowerIncl` intertwines `galActFrac C M τ` (downstairs) with `galActFrac C K̄ σ` (upstairs). The
ring-hom equality is checked on the `algebraMap` images via `IsFractionRing.ringHom_ext`, where it
reduces to the ring-level `towerTensorIncl_congr`. -/
theorem fracTowerIncl_galActFrac (C : SmoothPlaneCurve F)
    (M : IntermediateField F (AlgebraicClosure F))
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (τ : M ≃ₐ[F] M)
    (hστ : ∀ m : M, σ (m : AlgebraicClosure F) = (τ m : AlgebraicClosure F))
    (y : letI := C.isDomain_tensorCoordRing M
         FractionRing (M ⊗[F] C.toAffine.CoordinateRing)) :
    letI := C.isDomain_tensorCoordRing M
    letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
    fracTowerIncl C M (galActFrac C M τ y) = galActFrac C (AlgebraicClosure F) σ (fracTowerIncl C M y) := by
  letI := C.isDomain_tensorCoordRing M
  letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
  -- the key compatibility on a single `algebraMap` image
  have key : ∀ b : M ⊗[F] C.toAffine.CoordinateRing,
      fracTowerIncl C M (galActFrac C M τ
          (algebraMap (M ⊗[F] C.toAffine.CoordinateRing) _ b)) =
        galActFrac C (AlgebraicClosure F) σ (fracTowerIncl C M
          (algebraMap (M ⊗[F] C.toAffine.CoordinateRing) _ b)) := by
    intro b
    rw [galActFrac_algebraMap, fracTowerIncl_algebraMap, fracTowerIncl_algebraMap,
      galActFrac_algebraMap]
    congr 1
    exact towerTensorIncl_congr C.toAffine.CoordinateRing M σ τ hστ b
  -- reduce `y` to a ratio of `algebraMap` images
  obtain ⟨a, d, -, rfl⟩ := IsFractionRing.div_surjective
    (A := M ⊗[F] C.toAffine.CoordinateRing) y
  rw [map_div₀, map_div₀, map_div₀, map_div₀, key a, key d]

/-- **The infinite-Galois fixed-field characterization** (`L = K̄ = AlgebraicClosure F`, char 0): an
element of the `K̄`-function field `(C.baseChange K̄).FunctionField` lies in the image of `F(C)` under
the base-change embedding `functionFieldMap` iff it is fixed by *every* `galActFunctionField C K̄ σ`.

This is the `L = K̄` analogue of the finite `mem_range_functionField_baseChange_iff_fixed`. The `←`
direction is the genuine **tower descent**: a `Gal(K̄/F)`-fixed `x` is transported to a `galActFrac`-
fixed `y` in the tensor fraction field; the (finitely many) `K̄`-scalars of `y`'s numerator and
denominator lie in a finite Galois `M ⊆ K̄` (`exists_finiteGalois_towerTensorIncl_range₂`), so
`y = fracTowerIncl y_M`; `y_M` is `Gal(M/F)`-fixed (`fracTowerIncl` equivariance + injectivity +
`restrictNormalHom_surjective`); the proven *finite* descent (`the_lift` +
`tensor_ringAct_fixed_mem_range`) at `M` writes `y_M` as a ratio of `1 ⊗ -` images, which
`towerTensorIncl` carries to `1 ⊗ -` upstairs — exhibiting `x` as a `functionFieldMap` image. -/
theorem mem_range_functionField_baseChange_iff_fixed_kbar [CharZero F] (C : SmoothPlaneCurve F)
    (x : (C.baseChange (AlgebraicClosure F)).FunctionField) :
    (∃ f : C.FunctionField, C.functionFieldMap (AlgebraicClosure F) f = x) ↔
      ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        galActFunctionField C (AlgebraicClosure F) σ x = x := by
  constructor
  · rintro ⟨f, rfl⟩ σ
    exact galActFunctionField_fixes_baseChange C (AlgebraicClosure F) σ f
  · intro hfixed
    letI := C.isDomain_tensorCoordRing (AlgebraicClosure F)
    classical
    -- transport `x` to the tensor fraction field; it is `galActFrac`-fixed
    set y := (C.functionField_baseChange_tensorEquiv (AlgebraicClosure F)) x with hy_def
    have hyfix : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, galActFrac C (AlgebraicClosure F) σ y = y := by
      intro σ
      have hx := hfixed σ
      have hrel : galActFunctionField C (AlgebraicClosure F) σ x
          = (C.functionField_baseChange_tensorEquiv (AlgebraicClosure F)).symm
              (galActFrac C (AlgebraicClosure F) σ ((C.functionField_baseChange_tensorEquiv (AlgebraicClosure F)) x)) := rfl
      rw [hrel] at hx
      apply (C.functionField_baseChange_tensorEquiv (AlgebraicClosure F)).symm.injective
      rw [hx, hy_def, AlgEquiv.symm_apply_apply]
    -- write `y = algebraMap a / algebraMap d`
    obtain ⟨a, d, hd, hydiv⟩ := IsFractionRing.div_surjective
      (A := AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing) y
    -- the scalars of `a`, `d` live over a common finite Galois `M ⊆ K̄`
    obtain ⟨M, hMfin, hMgal, ⟨aM, haM⟩, ⟨dM, hdM⟩⟩ :=
      exists_finiteGalois_towerTensorIncl_range₂ C.toAffine.CoordinateRing a d
    letI := hMfin
    letI := hMgal
    letI := C.isDomain_tensorCoordRing M
    haveI : Normal F M := IsGalois.to_normal
    -- the downstairs fraction `y_M = algebraMap aM / algebraMap dM`
    let yM : FractionRing (M ⊗[F] C.toAffine.CoordinateRing) :=
        algebraMap (M ⊗[F] C.toAffine.CoordinateRing)
            (FractionRing (M ⊗[F] C.toAffine.CoordinateRing)) aM
        / algebraMap (M ⊗[F] C.toAffine.CoordinateRing)
            (FractionRing (M ⊗[F] C.toAffine.CoordinateRing)) dM
    -- `fracTowerIncl y_M = y`
    have hymap : fracTowerIncl C M yM = y := by
      show fracTowerIncl C M (_ / _) = y
      rw [map_div₀, fracTowerIncl_algebraMap, fracTowerIncl_algebraMap, haM, hdM]
      rw [hydiv]
    -- `y_M` is `Gal(M/F)`-fixed: lift each `τ` to `σ ⊇ τ` and use `fracTowerIncl` equivariance
    have hyMfix : ∀ τ : M ≃ₐ[F] M, galActFrac C M τ yM = yM := by
      intro τ
      obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M)
        (E := AlgebraicClosure F) τ
      have hστ : ∀ m : M, σ (m : AlgebraicClosure F) = (τ m : AlgebraicClosure F) := by
        intro m
        have hc := (σ.restrictNormal_commutes M m).symm
        rw [show AlgEquiv.restrictNormalHom (F := F) M σ = σ.restrictNormal M from rfl] at hσ
        rw [hσ] at hc
        simpa using hc
      apply fracTowerIncl_injective C M
      rw [fracTowerIncl_galActFrac C M σ τ hστ, hymap, hyfix σ]
    -- finite descent at `M`: `y_M = algebraMap (1 ⊗ mn) / algebraMap (1 ⊗ md)`
    obtain ⟨n, den, hnf, hdenf, _hdenne, hyMdiv⟩ := the_lift C M yM hyMfix
    obtain ⟨mn, hmn⟩ := tensor_ringAct_fixed_mem_range C M n hnf
    obtain ⟨md, hmd⟩ := tensor_ringAct_fixed_mem_range C M den hdenf
    -- the descended function over `F`
    refine ⟨algebraMap C.toAffine.CoordinateRing C.FunctionField mn
        / algebraMap C.toAffine.CoordinateRing C.FunctionField md, ?_⟩
    rw [map_div₀]
    -- transport `x` back through the K̄ tensor equiv
    have hx_eq : x = (C.functionField_baseChange_tensorEquiv (AlgebraicClosure F)).symm y := by
      rw [hy_def, AlgEquiv.symm_apply_apply]
    -- `y = algebraMap (1⊗mn)/algebraMap (1⊗md)` upstairs (via fracTowerIncl `1⊗-` transport)
    have hy_final : y =
        algebraMap (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing)
            (FractionRing (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing))
            ((1 : AlgebraicClosure F) ⊗ₜ[F] mn)
        / algebraMap (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing)
            (FractionRing (AlgebraicClosure F ⊗[F] C.toAffine.CoordinateRing))
            ((1 : AlgebraicClosure F) ⊗ₜ[F] md) := by
      rw [← hymap, hyMdiv, map_div₀, fracTowerIncl_algebraMap, fracTowerIncl_algebraMap,
        ← hmn, ← hmd]
      rw [show towerTensorIncl C.toAffine.CoordinateRing M ((1 : M) ⊗ₜ[F] mn)
          = (1 : AlgebraicClosure F) ⊗ₜ[F] mn by rw [towerTensorIncl_tmul]; norm_num,
        show towerTensorIncl C.toAffine.CoordinateRing M ((1 : M) ⊗ₜ[F] md)
          = (1 : AlgebraicClosure F) ⊗ₜ[F] md by rw [towerTensorIncl_tmul]; norm_num]
    rw [hx_eq, hy_final, map_div₀]
    congr 1
    · rw [tensorEquiv_symm_one_tmul C (AlgebraicClosure F) mn]
    · rw [tensorEquiv_symm_one_tmul C (AlgebraicClosure F) md]

/-- **The `K̄`-direct elementwise descent of the range inclusion** (MOVE 2, the one-step analogue of
`rangeIncl_of_descentData`). From the `K̄`-base-changes `psiK = φ*_K̄` and `mPbK = [m]*_K̄` (their
naturalities, `psiK` `Gal(K̄/F)`-equivariant + injective) and the **`K̄`-level** range inclusion
`Im(mPbK) ⊆ Im(psiK)`, the `F`-level inclusion `Im(mPb) ⊆ Im(φ*)` follows.

Unlike `rangeIncl_of_descentData` (which descends from a *finite* Galois `L`), this descends straight
from `K̄ = AlgebraicClosure F`, using the tower fixed-field characterization
`mem_range_functionField_baseChange_iff_fixed_kbar`.  This removes the need for a finite-`L` geometric
realization: the `K̄`-level inclusion is the *fully proven* `ecIsog_mulByInt_deg_rangeIncl_of_charZero`. -/
theorem rangeIncl_of_descentData_kbar [CharZero F] {C₁ C₂ : SmoothPlaneCurve F}
    {φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField}
    {mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField}
    (psiK : (C₂.baseChange (AlgebraicClosure F)).FunctionField →ₐ[F]
      (C₁.baseChange (AlgebraicClosure F)).FunctionField)
    (mPbK : (C₁.baseChange (AlgebraicClosure F)).FunctionField →ₐ[F]
      (C₁.baseChange (AlgebraicClosure F)).FunctionField)
    (hpsiK_equiv : GalEquivariant (AlgebraicClosure F) psiK)
    (hpsiK_inj : Function.Injective psiK)
    (hpsiK_nat : ∀ g : C₂.FunctionField,
      C₁.functionFieldMap (AlgebraicClosure F) (φPb g) = psiK (C₂.functionFieldMap (AlgebraicClosure F) g))
    (hmPbK_nat : ∀ u : C₁.FunctionField,
      C₁.functionFieldMap (AlgebraicClosure F) (mPb u) = mPbK (C₁.functionFieldMap (AlgebraicClosure F) u))
    (hKincl : mPbK.range ≤ psiK.range) :
    mPb.range ≤ φPb.range := by
  rintro z ⟨u, rfl⟩
  -- `functionFieldMap (mPb u) ∈ Im(mPbK) ⊆ Im(psiK)`
  have hz_mem : C₁.functionFieldMap (AlgebraicClosure F) (mPb u) ∈ psiK.range := by
    apply hKincl
    rw [hmPbK_nat u]
    exact ⟨C₁.functionFieldMap (AlgebraicClosure F) u, rfl⟩
  obtain ⟨ĝ, hĝ⟩ := hz_mem
  have hĝ' : psiK ĝ = C₁.functionFieldMap (AlgebraicClosure F) (mPb u) := hĝ
  -- `ĝ` is `Gal(K̄/F)`-fixed (since `psiK ĝ` is a base-change image, `psiK` equivariant + injective)
  have hĝ_fixed : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      galActFunctionField C₂ (AlgebraicClosure F) σ ĝ = ĝ := by
    intro σ
    apply hpsiK_inj
    rw [hpsiK_equiv σ ĝ, hĝ', galActFunctionField_fixes_baseChange]
  -- by the tower fact, `ĝ = functionFieldMap g` for `g ∈ F(C₂)`
  obtain ⟨g, hg⟩ := (mem_range_functionField_baseChange_iff_fixed_kbar C₂ ĝ).2 hĝ_fixed
  -- and `φPb g = mPb u` by injectivity of `functionFieldMap` and naturality
  refine ⟨g, C₁.functionFieldMap_injective (AlgebraicClosure F) ?_⟩
  show C₁.functionFieldMap (AlgebraicClosure F) (φPb g) = C₁.functionFieldMap (AlgebraicClosure F) (mPb u)
  rw [hpsiK_nat g, hg, hĝ']

/-! ### The two-curve `K̄`-direct dual range inclusion over an alg-closed char-0 base

(Relocated from the former `TwoCurveKbarRangeIncl.lean`, an unimported leaf.) For a two-curve
`EC.Isogeny φ : E₁ → E₂` over `[IsAlgClosed F] [CharZero F]`, the Silverman III.6.1 range inclusion
`Im([deg φ]*) ⊆ Im(φ*)` holds — fully proven via the geometric realization + the two-curve
fixed-field range inclusion (`mulByInt_deg_rangeIncl_twoCurve`).  MOVE 2 feeds *this* `K̄`-direct
inclusion (no finite `L`) into `rangeIncl_of_descentData_kbar`. -/

/-- **Char-0 ⟹ separable, two-curve form** (for the Basic `HasseWeil.Isogeny`). -/
theorem Isogeny.isSeparable_of_charZero_twoCurve [CharZero F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
    (β : HasseWeil.Isogeny W₁.toAffine W₂.toAffine) : β.IsSeparable := by
  letI := β.toAlgebra
  haveI : CharZero W₂.toAffine.FunctionField :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F W₂.toAffine.FunctionField)
  haveI : Algebra.IsAlgebraic W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    ⟨fun z => HasseWeil.Isogeny.isAlgebraic_toAlgebra_twoCurve β z⟩
  exact (inferInstance :
    @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _ β.toAlgebra)

/-- **The Basic-`Isogeny` shell of an `EC.Isogeny`** over the alg-closed base. -/
noncomputable def ecShell [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic]
    [W₂.toAffine.IsElliptic] (φ : EC.Isogeny W₁.toAffine W₂.toAffine) :
    HasseWeil.Isogeny W₁.toAffine W₂.toAffine where
  pullback := φ.toCurveMap.pullback
  toAddMonoidHom := 0

@[simp] theorem ecShell_pullback [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic] (φ : EC.Isogeny W₁.toAffine W₂.toAffine) :
    (ecShell φ).pullback = φ.toCurveMap.pullback := rfl

/-- **Route A, step 1 — the two-curve `K̄`-dual range inclusion over an alg-closed char-0 base.** -/
theorem ecIsog_mulByInt_deg_rangeIncl_of_charZero [IsAlgClosed F] [CharZero F]
    [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
    (φ : EC.Isogeny W₁.toAffine W₂.toAffine)
    (hreg : ∀ f : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback f)) :
    (HasseWeil.mulByInt_pullbackAlgHom W₁.toAffine ((ecShell φ).degree : ℤ)
        (by exact_mod_cast (HasseWeil.Isogeny.degree_pos_twoCurve (ecShell φ)).ne')).range ≤
      φ.toCurveMap.pullback.range := by
  classical
  have h_pres : WeilPairing.PlaceRestrictionPreservesPrincipal (ecShell φ) :=
    WeilPairing.placeRestrictionPreservesPrincipal_of_separable_charZero (ecShell φ)
      (Isogeny.isSeparable_of_charZero_twoCurve (ecShell φ)) hreg
  have hgh := WeilPairing.placeRestrictionPointMap_add_of_preservesPrincipal (ecShell φ) h_pres
  set β := WeilPairing.placeRestrictionRealization (ecShell φ) hgh with hβ
  have hβpb : β.pullback = φ.toCurveMap.pullback :=
    WeilPairing.placeRestrictionRealization_pullback (ecShell φ) hgh
  have hβsep : β.IsSeparable := Isogeny.isSeparable_of_charZero_twoCurve β
  have hw := WeilPairing.pullbackEvaluation_twoCurve_placeRestrictionRealization (ecShell φ) hgh
  have hxy := fun k => WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β
    (WeilPairing.twoCurvePoleLocus_finite (ecShell φ)) hw k
  have hcard : Nat.card β.kernel = β.degree :=
    card_kernel_eq_degree_twoCurve β hβsep
      (WeilPairing.twoCurvePoleLocus_finite (ecShell φ)) hw
  have hincl := HasseWeil.Isogeny.mulByInt_deg_rangeIncl_twoCurve β hxy hcard
  rw [hβpb] at hincl
  exact hincl

end TowerDescent

/-- **A `DescentData` over a concrete finite Galois intermediate field of `K̄`** (MOVE 1's data
carrier). Bundles the concrete `L ⊆ K̄ = AlgebraicClosure F` (with its finite/Galois instances) and a
`DescentData` over it. Unlike `SomeDescentData` (which takes an abstract `L : Type w`), this fixes `L`
to be a *subfield of the algebraic closure* — exactly the shape MOVE 1's
`exists_finiteGalois_fieldOfDefinition` produces. -/
structure DescentDataOverKbar {F : Type u} [Field F] (C₁ C₂ : SmoothPlaneCurve F)
    (φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField)
    (mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField) where
  /-- The concrete finite Galois field of definition `L ⊆ K̄`. -/
  L : IntermediateField F (AlgebraicClosure F)
  /-- `L/F` is finite. -/
  [finL : FiniteDimensional F L]
  /-- `L/F` is Galois. -/
  [galL : IsGalois F L]
  /-- The descent data over `L`. -/
  data : DescentData (C₁ := C₁) (C₂ := C₂) φPb mPb L

/-- **MOVE 1 payoff — package a `DescentDataOverKbar` into `SomeDescentData`** (the universe-correct
field-of-definition wrapper). A finite Galois intermediate field `L ⊆ K̄ = AlgebraicClosure F` lives
in the *same* universe `u` as `F`, so a `DescentData` over it directly furnishes the
`SomeDescentData.{u, u}` demanded by `exists_descentData_of_separable`.

This makes the field-of-definition reduction **concrete and load-bearing**: the residual no longer has
to *exhibit* a finite Galois `L` from thin air — MOVE 1 supplies `L` as a subfield of `K̄`, and this
wrapper threads the universe. The only remaining obligation is the `DescentData` over `L` itself (the
two-curve base-change data). -/
noncomputable def someDescentData_of_overKbar {F : Type u} [Field F]
    {C₁ C₂ : SmoothPlaneCurve F}
    {φPb : C₂.FunctionField →ₐ[F] C₁.FunctionField}
    {mPb : C₁.FunctionField →ₐ[F] C₁.FunctionField}
    (d : DescentDataOverKbar C₁ C₂ φPb mPb) :
    SomeDescentData.{u, u} (C₁ := C₁) (C₂ := C₂) φPb mPb where
  L := d.L
  fieldL := inferInstance
  algL := inferInstance
  finL := d.finL
  galL := d.galL
  data := d.data

/-! ### TWO-CURVE BASE-CHANGE of an isogeny via `ofEquation` (the `DescentData` engine)

The single leaf `descentData_over_kbar_intermediate` needs the **two-curve** base-change of a
separable isogeny `φ : E₁ → E₂` over a *finite* Galois `L/F` (`L ⊆ K̄`). The project's
`EC.Isogeny.baseChangeIsogeny` (`BaseChange.lean`) is endomorphism-only *and* requires
`[IsAlgClosed L]`. We rebuild it CoordHom-free via the **`EC.Isogeny.ofEquation`** builder, which is
already two-curve: feed the generator images `functionFieldMap (φ^* x_gen₂)`, `functionFieldMap
(φ^* y_gen₂)` (which satisfy the base-changed Weierstrass equation of `E₂_L` over `L(E₁_L)`), their
even-negative order at infinity (the ramification formula transported through `functionFieldMap`),
and the transcendence over `L`.

The transcendence over a *general* `L` (not just algebraically closed) is the only new analytic
input: an element of `L(E₁_L)` *algebraic over the constant field `L`* has order `0` at infinity
(`ordAtInfty_eq_zero_of_isAlgebraic_constants`, the minimal-polynomial/ultrametric argument), which
contradicts the even-negative order of `functionFieldMap (φ^* x_gen₂)`. This sidesteps the
`IsAlgClosed`-dependence of `baseChangeXgen_transcendental`. -/

namespace TwoCurveBaseChange

open WeierstrassCurve Polynomial Curves

/-! #### `σ`-semilinearity of the Galois action over `L` (used for full equivariance)

These two facts about a *single* curve's base-changed function field are kept independent of the
two-curve data `W₁ W₂ φ`, so they apply at both `C₁` and `C₂`. -/

section Semilinear

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

/-- **`σ ⊗ id` (`ringAct`) on `L`-constants**: `(σ ⊗ id)(algebraMap L (L ⊗ CR) l) = algebraMap L
(L ⊗ CR) (σ l)` — the `σ`-semilinearity of the tensor-side Galois action over `L`. -/
theorem ringAct_algebraMap_L (C : SmoothPlaneCurve K) (σ : L ≃ₐ[K] L) (l : L) :
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := K) (A₁ := C.toAffine.CoordinateRing)))
      (algebraMap L (L ⊗[K] C.toAffine.CoordinateRing) l) =
      algebraMap L (L ⊗[K] C.toAffine.CoordinateRing) (σ l) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp

/-- **`σ`-semilinearity of the Galois action over `L`**: `galAct σ (algebraMap L F(C_L) l) =
algebraMap L F(C_L) (σ l)`. The `L`-constant analogue of `galActFunctionField_fixes_baseChange`
(which handles the `F(C)`-image). Proof: transport through the *`L`-linear*
`functionField_baseChange_tensorEquiv` to the tensor-fraction side, where the action is
`IsFractionRing.algEquivOfAlgEquiv (σ ⊗ id)` and `σ ⊗ id` is `σ`-semilinear on `L`-constants
(`ringAct_algebraMap_L`). -/
theorem galActFunctionField_algebraMap_L (C : SmoothPlaneCurve K) (σ : L ≃ₐ[K] L) (l : L) :
    galActFunctionField C L σ (algebraMap L (C.baseChange L).FunctionField l) =
      algebraMap L (C.baseChange L).FunctionField (σ l) := by
  letI := C.isDomain_tensorCoordRing L
  simp only [galActFunctionField, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  rw [show (C.functionField_baseChange_tensorEquiv L)
        (algebraMap L (C.baseChange L).FunctionField l) =
      algebraMap L (FractionRing (L ⊗[K] C.toAffine.CoordinateRing)) l from
    (C.functionField_baseChange_tensorEquiv L).commutes l]
  rw [IsScalarTower.algebraMap_apply L (L ⊗[K] C.toAffine.CoordinateRing)
    (FractionRing (L ⊗[K] C.toAffine.CoordinateRing)) l]
  rw [galActFrac_algebraMap]
  rw [show ringAct C L σ (algebraMap L (L ⊗[K] C.toAffine.CoordinateRing) l) =
      algebraMap L (L ⊗[K] C.toAffine.CoordinateRing) (σ l) from
    ringAct_algebraMap_L L C σ l]
  rw [← IsScalarTower.algebraMap_apply L (L ⊗[K] C.toAffine.CoordinateRing)
    (FractionRing (L ⊗[K] C.toAffine.CoordinateRing)) (σ l)]
  exact (C.functionField_baseChange_tensorEquiv L).symm.commutes (σ l)

end Semilinear

/-- **Order at infinity vanishes for elements algebraic over the constant field.** If
`u ∈ L(C)` is algebraic over the constant field `L`, then `ord_∞ u = 0`. (Minimal-polynomial /
ultrametric argument: `u^n = -(lower terms)`, every lower term `c_i u^i` has order `i·ord_∞ u`,
constants have order `0`, so a negative `ord_∞ u` makes the leading term dominate and the sum cannot
vanish; a positive `ord_∞ u` is ruled out by the same argument on `u⁻¹`.) This is the
constant-field analogue of `ordAtInfty_eq_zero_of_isAlgebraic`, needed so the two-curve base-change
works over a general finite `L` rather than only over `K̄`. -/
theorem ordAtInfty_eq_zero_of_isAlgebraic_constants {L : Type*} [Field L]
    (C : SmoothPlaneCurve L) {u : C.FunctionField} (hu : u ≠ 0) (halg : IsAlgebraic L u) :
    C.ordAtInfty u = ((0 : ℤ) : WithTop ℤ) := by
  have hcoe : ∀ (k : ℕ) (a : ℤ),
      k • ((a : ℤ) : WithTop ℤ) = (((k • a : ℤ)) : WithTop ℤ) := by
    intro k a
    induction k with
    | zero => simp
    | succ n ih => rw [succ_nsmul, succ_nsmul, ih, ← WithTop.coe_add]
  have key : ∀ {z : C.FunctionField}, z ≠ 0 → IsAlgebraic L z → 0 < C.ordAtInfty z → False := by
    intro z hz hzalg hpos
    have hint : IsIntegral L z := hzalg.isIntegral
    obtain ⟨a, ha⟩ : ∃ a : ℤ, C.ordAtInfty z = ((a : ℤ) : WithTop ℤ) := ⟨_, C.ordAtInfty_of_ne hz⟩
    have ha_pos : 0 < a := by rw [ha] at hpos; exact_mod_cast hpos
    set m : Polynomial L := minpoly L z with hm_def
    have hc0 : m.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hz
    have haev : (Polynomial.aeval z) m = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at haev
    have hconst : m.coeff 0 • (z ^ 0 : C.FunctionField) =
        algebraMap L C.FunctionField (m.coeff 0) := by rw [pow_zero, Algebra.smul_def, mul_one]
    have hkey : algebraMap L C.FunctionField (m.coeff 0) =
        -∑ i ∈ Finset.range m.natDegree, m.coeff (i + 1) • z ^ (i + 1) := by
      rw [← hconst]; exact eq_neg_of_add_eq_zero_right haev
    have hterm : ∀ i ∈ Finset.range m.natDegree,
        ((a : ℤ) : WithTop ℤ) ≤ C.ordAtInfty (m.coeff (i + 1) • z ^ (i + 1)) := by
      intro i _
      rcases eq_or_ne (m.coeff (i + 1)) 0 with hci | hci
      · rw [hci, zero_smul]; simp
      · have hci' : algebraMap L C.FunctionField (m.coeff (i + 1)) ≠ 0 :=
          (_root_.map_ne_zero _).mpr hci
        have hzpow : z ^ (i + 1) ≠ 0 := pow_ne_zero _ hz
        rw [Algebra.smul_def, C.ordAtInfty_mul hci' hzpow,
          C.ordAtInfty_algebraMap_F_nonzero hci, C.ordAtInfty_pow hz, ha,
          hcoe, zero_add, WithTop.coe_le_coe, nsmul_eq_mul]
        have hi : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
        push_cast; nlinarith
    have hsum : ((a : ℤ) : WithTop ℤ) ≤
        C.ordAtInfty (∑ i ∈ Finset.range m.natDegree, m.coeff (i + 1) • z ^ (i + 1)) :=
      SmoothPlaneCurve.le_ordAtInfty_sum _ _ hterm
    have h0 := C.ordAtInfty_algebraMap_F_nonzero hc0
    rw [hkey, C.ordAtInfty_neg] at h0
    rw [h0] at hsum
    have : (a : ℤ) ≤ 0 := by exact_mod_cast hsum
    omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ, C.ordAtInfty u = ((a : ℤ) : WithTop ℤ) := ⟨_, C.ordAtInfty_of_ne hu⟩
  rcases lt_trichotomy a 0 with hlt | heq | hgt
  · exfalso
    refine key (inv_ne_zero hu) halg.inv ?_
    rw [C.ordAtInfty_inv, ha, show -((a : ℤ) : WithTop ℤ) = (((-a : ℤ)) : WithTop ℤ) from rfl]
    exact_mod_cast Int.neg_pos.mpr hlt
  · rw [ha, heq]
  · exact (key hu halg (by rw [ha]; exact_mod_cast hgt)).elim

variable {K : Type*} [Field K] [DecidableEq K]
variable (W₁ W₂ : WeierstrassCurve K) [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]
variable (φ : EC.Isogeny W₁.toAffine W₂.toAffine)
variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]

/-- The image in `L(E₁_L)` of `φ^* x_gen₂` under `functionFieldMap : K(E₁) → L(E₁_L)`
(the two-curve `x_gen`-image of the base-changed isogeny). -/
noncomputable def bcXgen : (W₁.baseChange L).toAffine.FunctionField :=
  (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (φ.toCurveMap.pullback (x_gen W₂))

/-- The image in `L(E₁_L)` of `φ^* y_gen₂`. -/
noncomputable def bcYgen : (W₁.baseChange L).toAffine.FunctionField :=
  (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (φ.toCurveMap.pullback (y_gen W₂))

theorem bcXgen_ne_zero : bcXgen W₁ W₂ φ L ≠ 0 := fun h0 =>
  φ.toCurveMap.pullback_ne_zero (x_gen_ne_zero W₂)
    ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap_injective L
      (h0.trans (map_zero _).symm))

/-- The two-curve generator images satisfy the Weierstrass equation of `E₂_L` over `L(E₁_L)`:
apply `φ^*` to the generic equation of `W₂` (over `K(E₂)`), then push along
`functionFieldMap : K(E₁) → L(E₁_L)`. -/
theorem bc_equation :
    ((W₂.baseChange L).map
        (algebraMap L (W₁.baseChange L).toAffine.FunctionField)).toAffine.Equation
      (bcXgen W₁ W₂ φ L) (bcYgen W₁ W₂ φ L) := by
  have hK : (W₂.map (algebraMap K W₁.toAffine.FunctionField)).toAffine.Equation
      (φ.toCurveMap.pullback (x_gen W₂)) (φ.toCurveMap.pullback (y_gen W₂)) := by
    have h := WeierstrassCurve.Affine.Equation.map
      (f := (φ.toCurveMap.pullback : W₂.toAffine.FunctionField →+* W₁.toAffine.FunctionField))
      (generic_equation W₂)
    rwa [show (W_KE W₂).toAffine.map
        (φ.toCurveMap.pullback : W₂.toAffine.FunctionField →+* W₁.toAffine.FunctionField) =
        W₂.map (algebraMap K W₁.toAffine.FunctionField) from by
      show (W₂.map _).map _ = W₂.map _
      rw [WeierstrassCurve.map_map, AlgHom.comp_algebraMap]] at h
  have hpush := WeierstrassCurve.Affine.Equation.map
    (f := ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L :
      W₁.toAffine.FunctionField →+*
        ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField)) hK
  have hcurve : (W₂.map (algebraMap K W₁.toAffine.FunctionField)).toAffine.map
      ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L) =
      (W₂.baseChange L).map (algebraMap L (W₁.baseChange L).toAffine.FunctionField) := by
    show (W₂.map _).map _ = (W₂.map _).map _
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map]
    refine congrArg W₂.map ?_
    refine RingHom.ext fun a => ?_
    show (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
        (algebraMap K (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).FunctionField a) =
      algebraMap L (W₁.baseChange L).toAffine.FunctionField (algebraMap K L a)
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F (⟨W₁.toAffine⟩ : SmoothPlaneCurve K) L a]
    exact IsScalarTower.algebraMap_apply K L
      ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField a
  exact (congrArg (fun V : WeierstrassCurve ((W₁.baseChange L).toAffine.FunctionField) =>
    V.toAffine.Equation (bcXgen W₁ W₂ φ L) (bcYgen W₁ W₂ φ L)) hcurve).mp hpush

/-- The even-negative order at infinity of `bcXgen`: `ord_∞ = 2m` with `m ≤ -1`, from the two-curve
ramification formula `exists_pos_ramificationIdx_at_infinity` (`ord_∞(φ^* x_gen₂) = e • (-2)`)
transported through `functionFieldMap`. -/
theorem bc_ord :
    ∃ m : ℤ, m ≤ -1 ∧
      (W_smooth (W₁.baseChange L)).ordAtInfty (bcXgen W₁ W₂ φ L) = ((2 * m : ℤ) : WithTop ℤ) := by
  obtain ⟨e, he1, hform⟩ := EC.Isogeny.exists_pos_ramificationIdx_at_infinity φ
  refine ⟨-(e : ℤ), ?_, ?_⟩
  · have h1 : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he1
    omega
  have hnsmul : ∀ k : ℕ, k • ((-2 : ℤ) : WithTop ℤ) = ((2 * (-(k : ℤ)) : ℤ) : WithTop ℤ) := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [succ_nsmul, ih, ← WithTop.coe_add]
      exact WithTop.coe_inj.mpr (by push_cast; ring)
  have hKord : (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).ordAtInfty
      (φ.toCurveMap.pullback (x_gen W₂)) = ((2 * (-(e : ℤ)) : ℤ) : WithTop ℤ) := by
    have h := hform (x_gen W₂) (x_gen_ne_zero W₂)
    rw [show (⟨W₂.toAffine⟩ : SmoothPlaneCurve K).ordAtInfty (x_gen W₂) =
        ((-2 : ℤ) : WithTop ℤ) from ordAtInfty_x_gen W₂] at h
    rw [h]; exact hnsmul e
  have hne : φ.toCurveMap.pullback (x_gen W₂) ≠ 0 :=
    φ.toCurveMap.pullback_ne_zero (x_gen_ne_zero W₂)
  have htrans := SmoothPlaneCurve.ordAtInfty_functionFieldMap
    (⟨W₁.toAffine⟩ : SmoothPlaneCurve K) L (φ.toCurveMap.pullback (x_gen W₂)) hne
  exact htrans.trans hKord

/-- **Transcendence of `bcXgen` over the (general) constant field `L`.** No `IsAlgClosed`
hypothesis: an element algebraic over `L` would have order `0` at infinity
(`ordAtInfty_eq_zero_of_isAlgebraic_constants`), contradicting the even-negative `bc_ord`. -/
theorem bcXgen_transcendental : Transcendental L (bcXgen W₁ W₂ φ L) := by
  intro halg
  obtain ⟨m, hm, hord⟩ := bc_ord W₁ W₂ φ L
  have h0 := ordAtInfty_eq_zero_of_isAlgebraic_constants
    (W_smooth (W₁.baseChange L)) (bcXgen_ne_zero W₁ W₂ φ L) halg
  rw [h0] at hord
  have : (0 : ℤ) = 2 * m := WithTop.coe_inj.mp hord
  omega

/-- **The two-curve base-changed isogeny** `φ_L : E₁_L → E₂_L` (over a general finite/`L`-algebra
`L`, CoordHom-free), via `ofEquation`. Its pullback sends `x_gen (E₂_L) ↦ bcXgen`,
`y_gen (E₂_L) ↦ bcYgen`. -/
noncomputable def bcIsog :
    EC.Isogeny (W₁.baseChange L).toAffine (W₂.baseChange L).toAffine :=
  Isogeny.ofEquation (W₁.baseChange L) (W₂.baseChange L)
    (bcXgen W₁ W₂ φ L) (bcYgen W₁ W₂ φ L)
    (bc_equation W₁ W₂ φ L) (bcXgen_transcendental W₁ W₂ φ L)
    (Classical.choose_spec (bc_ord W₁ W₂ φ L)).1
    (Classical.choose_spec (bc_ord W₁ W₂ φ L)).2

theorem bcIsog_pullback_x_gen :
    (bcIsog W₁ W₂ φ L).toCurveMap.pullback (x_gen (W₂.baseChange L)) = bcXgen W₁ W₂ φ L :=
  HasseWeil.ofEquationPullback_x_gen (W₁.baseChange L) (W₂.baseChange L) (bcXgen W₁ W₂ φ L)
    (bcYgen W₁ W₂ φ L) (bc_equation W₁ W₂ φ L) (bcXgen_transcendental W₁ W₂ φ L)

theorem bcIsog_pullback_y_gen :
    (bcIsog W₁ W₂ φ L).toCurveMap.pullback (y_gen (W₂.baseChange L)) = bcYgen W₁ W₂ φ L :=
  HasseWeil.ofEquationPullback_y_gen (W₁.baseChange L) (W₂.baseChange L) (bcXgen W₁ W₂ φ L)
    (bcYgen W₁ W₂ φ L) (bc_equation W₁ W₂ φ L) (bcXgen_transcendental W₁ W₂ φ L)

/-- **Two-curve `AlgHom` extensionality on the generic coordinates.** A `K`-algebra hom out of
`K(E₂)` is determined by its values on `x_gen₂` and `y_gen₂`. -/
theorem algHom_ext_x_y_gen2 {A : Type*} [CommRing A] [Algebra K A]
    {ψ₁ ψ₂ : W₂.toAffine.FunctionField →ₐ[K] A}
    (hx : ψ₁ (x_gen W₂) = ψ₂ (x_gen W₂)) (hy : ψ₁ (y_gen W₂) = ψ₂ (y_gen W₂)) : ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W₂.toAffine.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ _ (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ _ (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ _ (AdjoinRoot.root W₂.toAffine.polynomial)) =
      ψ₂ (algebraMap _ _ (AdjoinRoot.root W₂.toAffine.polynomial))
    exact hy

/-- `functionFieldMap` carries `x_gen₂` to `x_gen (E₂_L)`. -/
theorem functionFieldMap_x_gen :
    (⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (x_gen W₂) =
      x_gen (W₂.baseChange L) := by
  rw [x_gen, SmoothPlaneCurve.functionFieldMap_algebraMap]
  show algebraMap _ _ ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
      (algebraMap (Polynomial K) W₂.toAffine.CoordinateRing Polynomial.X)) = _
  rw [SmoothPlaneCurve.coordRingMap_X]
  rfl

/-- `functionFieldMap` carries `y_gen₂` to `y_gen (E₂_L)`. -/
theorem functionFieldMap_y_gen :
    (⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (y_gen W₂) =
      y_gen (W₂.baseChange L) := by
  rw [y_gen, SmoothPlaneCurve.functionFieldMap_algebraMap]
  show algebraMap _ _ ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).coordRingMap L
      (AdjoinRoot.root W₂.toAffine.polynomial)) = _
  rw [SmoothPlaneCurve.coordRingMap_root]
  rfl

/-- **`ψ_L`** — the `F = K`-algebra-hom pullback of the two-curve base-changed isogeny, i.e. the
`L`-base-change of `φ^*` (`restrictScalars` to `K`). -/
noncomputable def psiL :
    ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField →ₐ[K]
      ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField :=
  ((bcIsog W₁ W₂ φ L).toCurveMap.pullback).restrictScalars K

/-- **Base-change naturality of `φ^*`**: `functionFieldMap ∘ φ^* = ψ_L ∘ functionFieldMap`. The two
sides are `K`-algebra homs `K(E₂) → L(E₁_L)` agreeing on `x_gen₂`, `y_gen₂`
(`bcIsog_pullback_x_gen`/`_y_gen` + `functionFieldMap_x_gen`/`_y_gen`). -/
theorem psiL_nat (g : (⟨W₂.toAffine⟩ : SmoothPlaneCurve K).FunctionField) :
    (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (φ.toCurveMap.pullback g) =
      psiL W₁ W₂ φ L ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L g) := by
  have heq : ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L).comp
        φ.toCurveMap.pullback =
      (psiL W₁ W₂ φ L).comp
        ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L) := by
    apply algHom_ext_x_y_gen2 W₂
    · show (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
          (φ.toCurveMap.pullback (x_gen W₂)) =
        psiL W₁ W₂ φ L ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (x_gen W₂))
      rw [functionFieldMap_x_gen]
      show _ = (bcIsog W₁ W₂ φ L).toCurveMap.pullback (x_gen (W₂.baseChange L))
      rw [bcIsog_pullback_x_gen]; rfl
    · show (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
          (φ.toCurveMap.pullback (y_gen W₂)) =
        psiL W₁ W₂ φ L ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (y_gen W₂))
      rw [functionFieldMap_y_gen]
      show _ = (bcIsog W₁ W₂ φ L).toCurveMap.pullback (y_gen (W₂.baseChange L))
      rw [bcIsog_pullback_y_gen]; rfl
  exact AlgHom.congr_fun heq g

/-- `ψ_L` is injective (it is an `F`-algebra hom between fields). -/
theorem psiL_injective : Function.Injective (psiL W₁ W₂ φ L) :=
  (psiL W₁ W₂ φ L).toRingHom.injective

/-- `ψ_L` is `L`-linear on constants: `ψ_L (algebraMap L _ l) = algebraMap L _ l`. It is the
`restrictScalars K` of the *`L`-algebra hom* `(bcIsog).pullback`, which fixes `L`-constants. -/
theorem psiL_algebraMap_L (l : L) :
    psiL W₁ W₂ φ L
        (algebraMap L ((⟨W₂.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField l) =
      algebraMap L ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField l :=
  (bcIsog W₁ W₂ φ L).toCurveMap.pullback.commutes l

/-! #### `mPbL` — the base change of `[deg φ]*` (an endomorphism), and its naturality -/

variable {n : ℤ}

/-- **`[m]_L*`** — the `L`-base-change of `[m]* = mulByInt_pullbackAlgHom` (the endomorphism case
`W₁ → W₁`), as `ψ_L` of the `EC.Isogeny.mulByInt` endomorphism. -/
noncomputable def mPbL (hn : n ≠ 0) :
    ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField →ₐ[K]
      ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).baseChange L).FunctionField :=
  psiL W₁ W₁ (EC.Isogeny.mulByInt W₁.toAffine hn) L

/-- **Base-change naturality of `[m]*`**: `functionFieldMap ∘ [m]* = [m]_L* ∘ functionFieldMap`. The
endomorphism shadow of `psiL_nat`, using `(mulByInt W hn).pullback = mulByInt_pullbackAlgHom`. -/
theorem mPbL_nat (hn : n ≠ 0) (u : (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).FunctionField) :
    (⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L
        (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn u) =
      mPbL W₁ L hn ((⟨W₁.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L u) := by
  have hpb : (EC.Isogeny.mulByInt W₁.toAffine hn).toCurveMap.pullback u =
      HasseWeil.mulByInt_pullbackAlgHom W₁ n hn u := rfl
  rw [← hpb]
  exact psiL_nat W₁ W₁ (EC.Isogeny.mulByInt W₁.toAffine hn) L u

/-! #### `Gal(L/F)`-equivariance of `ψ_L` (full, on all of `F(E₂_L)`)

`ψ_L` is `L`-linear (the `restrictScalars` of an `L`-algebra hom) and the Galois action is
`σ`-semilinear over `L` (`galActFunctionField_algebraMap_L`). The function field `F(E₂_L)` is
generated over `F` by the L-constants `algebraMap L _ l` together with the generic coordinates
`x_gen (E₂_L)`, `y_gen (E₂_L)` — which are themselves `functionFieldMap`-images
(`functionFieldMap_x_gen`/`_y_gen`), hence Galois-fixed. So equivariance reduces, via the base-`L`
ring-hom extensionality `ringHom_ext_baseL`, to the three generators: on L-constants it is the
semilinearity; on `x_gen`/`y_gen` both sides are the (Galois-fixed) `bcXgen`/`bcYgen`. -/

/-- **Base-`L` ring-hom extensionality** (the equivariance engine): a ring hom out of `F(E₂_L)`
(into any field) is determined by its values on the `L`-constants and the two generic coordinates of
`E₂_L`. Reduction: `IsFractionRing.div_surjective` (peel `Frac`), `AdjoinRoot.ringHom_ext` (peel
`AdjoinRoot`), `Polynomial.ringHom_ext` (peel `L[X]` into `C l` = L-constants and `X` = `x_gen`). -/
theorem ringHom_ext_baseL {A : Type*} [Field A]
    (ψ₁ ψ₂ : (W₂.baseChange L).toAffine.FunctionField →+* A)
    (hbase : ∀ l : L, ψ₁ (algebraMap L _ l) = ψ₂ (algebraMap L _ l))
    (hx : ψ₁ (x_gen (W₂.baseChange L)) = ψ₂ (x_gen (W₂.baseChange L)))
    (hy : ψ₁ (y_gen (W₂.baseChange L)) = ψ₂ (y_gen (W₂.baseChange L))) :
    ψ₁ = ψ₂ := by
  have hcomp : (ψ₁.comp (algebraMap (W₂.baseChange L).toAffine.CoordinateRing
        (W₂.baseChange L).toAffine.FunctionField)) =
      (ψ₂.comp (algebraMap (W₂.baseChange L).toAffine.CoordinateRing
        (W₂.baseChange L).toAffine.FunctionField)) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro l
        change ψ₁ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
            ((AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) (C l))) =
          ψ₂ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
            ((AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) (C l)))
        have hca : (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _)
            ((AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) (C l)) =
            algebraMap L (W₂.baseChange L).toAffine.FunctionField l := by
          rw [show (AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) (C l) =
              algebraMap L (W₂.baseChange L).toAffine.CoordinateRing l from rfl,
            ← IsScalarTower.algebraMap_apply]
        rw [hca]; exact hbase l
      · change ψ₁ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
            ((AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) X)) =
          ψ₂ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
            ((AdjoinRoot.of (W₂.baseChange L).toAffine.polynomial) X))
        exact hx
    · change ψ₁ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
          (AdjoinRoot.root (W₂.baseChange L).toAffine.polynomial)) =
        ψ₂ (algebraMap (W₂.baseChange L).toAffine.CoordinateRing _
          (AdjoinRoot.root (W₂.baseChange L).toAffine.polynomial))
      exact hy
  ext z
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective
    (A := (W₂.baseChange L).toAffine.CoordinateRing) z
  have ha := RingHom.congr_fun hcomp a
  have hbb := RingHom.congr_fun hcomp b
  simp only [RingHom.comp_apply] at ha hbb
  rw [map_div₀, map_div₀, ha, hbb]

/-- **`ψ_L` is `Gal(L/F)`-equivariant** (the full statement on all of `F(E₂_L)`). Reduce, via
`ringHom_ext_baseL`, to the three generators: on the `L`-constants `algebraMap L _ l` it is the
`σ`-semilinearity of the Galois action (`galActFunctionField_algebraMap_L`) matched against the
`L`-linearity of `ψ_L`; on `x_gen`/`y_gen` (which are `functionFieldMap`-images, so Galois-fixed via
`galActFunctionField_fixes_baseChange`) both sides are the (also Galois-fixed) `bcXgen`/`bcYgen`. -/
theorem psiL_galEquivariant : GalEquivariant L ((psiL W₁ W₂ φ L)) := by
  intro σ
  -- compare the two ring homs `x ↦ psiL (galAct σ x)` and `x ↦ galAct σ (psiL x)`
  have hfun : (psiL W₁ W₂ φ L).toRingHom.comp (galActFunctionField (⟨W₂.toAffine⟩) L σ).toRingHom =
      (galActFunctionField (⟨W₁.toAffine⟩) L σ).toRingHom.comp (psiL W₁ W₂ φ L).toRingHom := by
    apply ringHom_ext_baseL W₂ L
    · -- L-constants
      intro l
      show (psiL W₁ W₂ φ L) (galActFunctionField (⟨W₂.toAffine⟩) L σ
          (algebraMap L _ l)) =
        galActFunctionField (⟨W₁.toAffine⟩) L σ ((psiL W₁ W₂ φ L) (algebraMap L _ l))
      rw [galActFunctionField_algebraMap_L]
      rw [psiL_algebraMap_L, psiL_algebraMap_L, galActFunctionField_algebraMap_L]
    · -- x_gen of E₂_L : a functionFieldMap-image, hence Galois-fixed
      show (psiL W₁ W₂ φ L) (galActFunctionField (⟨W₂.toAffine⟩) L σ (x_gen (W₂.baseChange L))) =
        galActFunctionField (⟨W₁.toAffine⟩) L σ ((psiL W₁ W₂ φ L) (x_gen (W₂.baseChange L)))
      rw [← functionFieldMap_x_gen, galActFunctionField_fixes_baseChange,
        functionFieldMap_x_gen]
      show _ = galActFunctionField (⟨W₁.toAffine⟩) L σ
        ((bcIsog W₁ W₂ φ L).toCurveMap.pullback (x_gen (W₂.baseChange L)))
      rw [bcIsog_pullback_x_gen, bcXgen, galActFunctionField_fixes_baseChange]
      show (bcIsog W₁ W₂ φ L).toCurveMap.pullback (x_gen (W₂.baseChange L)) = _
      rw [bcIsog_pullback_x_gen]; rfl
    · -- y_gen of E₂_L
      show (psiL W₁ W₂ φ L) (galActFunctionField (⟨W₂.toAffine⟩) L σ (y_gen (W₂.baseChange L))) =
        galActFunctionField (⟨W₁.toAffine⟩) L σ ((psiL W₁ W₂ φ L) (y_gen (W₂.baseChange L)))
      rw [← functionFieldMap_y_gen, galActFunctionField_fixes_baseChange,
        functionFieldMap_y_gen]
      show _ = galActFunctionField (⟨W₁.toAffine⟩) L σ
        ((bcIsog W₁ W₂ φ L).toCurveMap.pullback (y_gen (W₂.baseChange L)))
      rw [bcIsog_pullback_y_gen, bcYgen, galActFunctionField_fixes_baseChange]
      show (bcIsog W₁ W₂ φ L).toCurveMap.pullback (y_gen (W₂.baseChange L)) = _
      rw [bcIsog_pullback_y_gen]; rfl
  intro x
  exact RingHom.congr_fun hfun x

end TwoCurveBaseChange

/-! ### The two-curve `DescentData` over a finite Galois `L ⊆ K̄`

With `TwoCurveBaseChange` supplying the CoordHom-free `ψ_L`/`[m]_L*` (via `ofEquation`), their
base-change naturalities, `ψ_L`'s injectivity, and `ψ_L`'s full `Gal(L/F)`-equivariance, the only
remaining content of `descentData_over_kbar_intermediate` is the **`L`-level range inclusion**
`Im([deg φ]_L*) ⊆ Im(ψ_L)` — the two-curve `K̄`-dual descended to a finite Galois `L`. That single
inclusion is isolated as `twoCurveKbarRangeIncl_descended`.

**OBSOLETE NOTE (pre-`TwoCurveBaseChange`):** the earlier framing required a `CoordHom` for `φ`
(`psiL = baseChangeAlgHom cd L`), which a general `EC.Isogeny` does not carry. That obstruction is now
gone — `ofEquation` builds `ψ_L` directly from the pullback generator images, no `CoordHom`.

**What is PROVEN around it (this pass):** the field-of-definition descent (MOVE 1 —
`instIsGalois_algebraicClosure`, `exists_finiteGalois_fieldOfDefinition`, `galFixed_of_galFixed_top`),
the universe-correct packaging (`someDescentData_of_overKbar`), the entire elementwise Galois descent
downstream (`rangeIncl_of_descentData`, DUAL-Q1 `mem_range_functionField_baseChange_iff_fixed`), and
**all six structural `DescentData` fields except `hLincl`** (the two-curve base-change
`TwoCurveBaseChange.{bcIsog, psiL, mPbL, psiL_nat, mPbL_nat, psiL_injective, psiL_galEquivariant}`). -/

/-- **The data carrier of the single residual leaf** — a concrete finite Galois `L ⊆ K̄` together
with the two-curve `K̄`-dual range inclusion `Im([deg φ]_L*) ⊆ Im(ψ_L)` over it. Bundles `L` and its
instances as *data* so the leaf can be consumed by the (data-valued)
`descentData_over_kbar_intermediate`. -/
private structure TwoCurveKbarRangeInclData {F : Type u} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) where
  /-- The concrete finite Galois field of definition `L ⊆ K̄`. -/
  L : IntermediateField F (AlgebraicClosure F)
  /-- `L/F` is finite. -/
  [finL : FiniteDimensional F L]
  /-- `L/F` is Galois. -/
  [galL : IsGalois F L]
  /-- A decidability instance on `L` (for the `ofEquation` construction). -/
  decL : DecidableEq L
  /-- The two-curve `K̄`-dual range inclusion over `L`. -/
  hLincl :
    letI := decL
    (TwoCurveBaseChange.mPbL W₁ L (n := (φ.degree : ℤ))
        (by exact_mod_cast φ.degree_pos'.ne')).range ≤
      (TwoCurveBaseChange.psiL W₁ W₂ φ L).range

/-- **The genuine two-curve geometric leaf** (Silverman III.4.10c, the *only* remaining
infrastructure after this pass).  Over a concrete finite Galois `L ⊆ K̄`, it packages a
points-bearing realization `βL : Basic.Isogeny (E₁_L) (E₂_L)` of the function-field base-change
`ψ_L = (bcIsog).pullback` together with the two genuinely-geometric facts of III.4.10c read for the
two-curve `βL`:

* `h_pbL` — `βL.pullback = ψ_L` (the points-bearing realization of `ψ_L`, as `L`-algebra homs;
  i.e. a point map for `bcIsog` over `L`).  For an `EC.Isogeny` built by `ofEquation` over `K̄ ⊇ L`
  this is exactly the affine-kernel / `PullbackEvaluation` point-map content;
* `h_xy_family` — the per-`βL` kernel-translation covariance on `x_gen₂`/`y_gen₂` (Silverman
  III.4.10b, the generic-point covariance for the two-curve `βL`);
* `h_card` — the cardinality match `#ker βL = deg βL` (Silverman III.4.10c, via the *two-curve*
  good-fibre count `Curves.LocalizedDictionary` — already two-curve — fed to the two-curve
  `card_kernel_eq_degree_of_separable_witness`);
* `h_mPbL` — the structural identification `[deg φ]_L* = [deg βL]_{E₁_L}*` (`mPbL` is the L-base
  change of `[deg φ]*` via `bcIsog`; matching it to the endomorphism `[deg βL]` over `E₁_L` and
  `deg βL = deg φ` is base-change-of-`mulByInt` + degree preservation, separable plumbing).

Everything else — the fixed-field equality `Fix(ker βL) = Im(βL*)`, the easy inclusion
`Im([m]*) ⊆ Fix(ker βL)`, and the assembled K̄-dual range inclusion
`Im([m]*) ⊆ Im(βL*)` — is **proven, two-curve, axiom-clean** in
`HasseWeil.Isogeny.mulByInt_deg_rangeIncl_twoCurve` (`EC/IsogenyAG/TwoCurveDualRange.lean`), built on
the two-curve fixed-field core `EC/IsogenyAG/TwoCurveFixedField.lean`. -/
private structure TwoCurveGeometricDualData {F : Type u} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) where
  /-- The concrete finite Galois field of definition `L ⊆ K̄`. -/
  L : IntermediateField F (AlgebraicClosure F)
  /-- `L/F` is finite. -/
  [finL : FiniteDimensional F L]
  /-- `L/F` is Galois. -/
  [galL : IsGalois F L]
  /-- A decidability instance on `L` (for the `ofEquation` construction). -/
  decL : DecidableEq L
  /-- The points-bearing realization of `ψ_L` over `L`. -/
  βL :
    letI := decL
    HasseWeil.Isogeny (W₁.baseChange L).toAffine (W₂.baseChange L).toAffine
  /-- `βL.pullback` is `ψ_L` (the `L`-algebra pullback of the base-changed isogeny). -/
  h_pbL :
    letI := decL
    βL.pullback = (TwoCurveBaseChange.bcIsog W₁ W₂ φ L).toCurveMap.pullback
  /-- The per-`βL` kernel-translation covariance (Silverman III.4.10b). -/
  h_xy_family :
    letI := decL
    ∀ k : βL.kernel,
      (HasseWeil.translateAlgEquivOfPoint (W₁.baseChange L) k.val
          (βL.pullback (HasseWeil.x_gen (W₂.baseChange L))) =
        βL.pullback (HasseWeil.x_gen (W₂.baseChange L))) ∧
      (HasseWeil.translateAlgEquivOfPoint (W₁.baseChange L) k.val
          (βL.pullback (HasseWeil.y_gen (W₂.baseChange L))) =
        βL.pullback (HasseWeil.y_gen (W₂.baseChange L)))
  /-- The cardinality match `#ker βL = deg βL` (Silverman III.4.10c). -/
  h_card :
    letI := decL
    Nat.card βL.kernel = βL.degree
  /-- `βL` has the same degree as `φ` (base-change preserves degree). -/
  h_deg :
    letI := decL
    βL.degree = φ.degree
  /-- `[deg φ]_L*` (the base-changed `mulByInt` pullback) is the source-`E₁_L` endomorphism
  `[deg βL]_{E₁_L}*` — the structural `mulByInt` base-change + degree-preservation identification. -/
  h_mPbL :
    letI := decL
    (TwoCurveBaseChange.mPbL W₁ L (n := (φ.degree : ℤ))
        (by exact_mod_cast φ.degree_pos'.ne') :
      (W₁.baseChange L).toAffine.FunctionField →ₐ[F] (W₁.baseChange L).toAffine.FunctionField) =
      (HasseWeil.mulByInt_pullbackAlgHom (W₁.baseChange L) (βL.degree : ℤ)
        (by exact_mod_cast (HasseWeil.Isogeny.degree_pos_twoCurve βL).ne')).restrictScalars F

/-- **The two-curve `K̄`-dual range inclusion, from the genuine geometric leaf.** Consuming the
`TwoCurveGeometricDualData` (the points-bearing realization + `xy_family` + `#ker = deg` + the two
structural identifications), the `L`-level inclusion `Im([deg φ]_L*) ⊆ Im(ψ_L)` is **proven** via the
two-curve fixed-field range inclusion `HasseWeil.Isogeny.mulByInt_deg_rangeIncl_twoCurve`. -/
private noncomputable def twoCurveKbarRangeInclData_of_geometric {F : Type u} [Field F]
    [DecidableEq F] [CharZero F] {W₁ W₂ : WeierstrassCurve.Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] {φ : EC.Isogeny W₁ W₂}
    (d : TwoCurveGeometricDualData φ) : TwoCurveKbarRangeInclData φ :=
  letI := d.finL
  letI := d.galL
  letI : DecidableEq d.L := d.decL
  { L := d.L
    finL := d.finL
    galL := d.galL
    decL := d.decL
    hLincl := by
      -- the two-curve fixed-field range inclusion for the points-bearing `βL`, over the base `L`
      have hincl := HasseWeil.Isogeny.mulByInt_deg_rangeIncl_twoCurve d.βL d.h_xy_family d.h_card
      -- elementwise (the `Subalgebra` ranges are over different base rings `F` vs `L`, but the
      -- underlying *sets* `{z | ∃ x, f x = z}` agree under `restrictScalars`)
      rintro z hz
      rw [AlgHom.mem_range] at hz
      obtain ⟨u, hu⟩ := hz
      -- rewrite `mPbL` to `[deg βL]_{E₁_L}*` (restrictScalars `F`) *pointwise*; the underlying
      -- function is the bare `mulByInt_pullbackAlgHom`, so `z` lies in its `L`-range
      have hu' : (HasseWeil.mulByInt_pullbackAlgHom (W₁.baseChange d.L) (d.βL.degree : ℤ)
          (by exact_mod_cast (HasseWeil.Isogeny.degree_pos_twoCurve d.βL).ne')) u = z := by
        rw [← hu]; exact (DFunLike.congr_fun d.h_mPbL u).symm
      have hzmemL : z ∈ (HasseWeil.mulByInt_pullbackAlgHom (W₁.baseChange d.L)
          (d.βL.degree : ℤ)
          (by exact_mod_cast (HasseWeil.Isogeny.degree_pos_twoCurve d.βL).ne')).range :=
        ⟨u, hu'⟩
      obtain ⟨w, hw⟩ := hincl hzmemL
      -- `z = βL.pullback w = ψ_L w`, so `z ∈ Im(ψ_L)`
      rw [AlgHom.mem_range]
      refine ⟨w, ?_⟩
      -- `ψ_L = (bcIsog).pullback.restrictScalars F`, applied is defeq to `(bcIsog).pullback w`;
      -- and `(bcIsog).pullback = βL.pullback` by `d.h_pbL`
      show (TwoCurveBaseChange.bcIsog W₁ W₂ φ d.L).toCurveMap.pullback w = z
      rw [← d.h_pbL]; exact hw }

/-- **The single residual leaf — the `L`-level two-curve `K̄`-dual range inclusion (REVIEW-PENDING),
narrowed to the genuine two-curve geometric data.** Produces a `TwoCurveKbarRangeInclData` from the
`TwoCurveGeometricDualData` leaf: a points-bearing realization of `ψ_L` over a finite Galois
`L ⊆ K̄`, with the two III.4.10c geometric facts (`xy_family`, `#ker = deg`) and the structural
`mulByInt` base-change identifications.

**This pass — the fixed-field route is now PROVEN two-curve.** The entire Silverman III.6.1 dual
range inclusion `Im([m]_K̄*) ⊆ Im(φ_K̄*)` for a *two-curve* `φ_K̄ : E₁_K̄ → E₂_K̄` is reduced to the
two genuine geometric facts (`xy_family`, `#ker = deg`) plus a points-bearing realization, via the
new two-curve fixed-field machinery (`EC/IsogenyAG/TwoCurveFixedField.lean`,
`EC/IsogenyAG/TwoCurveDualRange.lean`, all axiom-clean):

* the project's endo-only fixed-field chain (`pullback_fieldRange_eq_fixedField_general`,
  `fixedField_hfix_general`, `finrank_pullback_fieldRange_eq_degree`) is **successfully relaxed to
  two curves** — every step is source-natural (the kernel `ker φ ⊆ E₁` acts on `K(E₁)` by
  translation; the only cross-curve object is `φ.pullback`);
* the easy inclusion `Im([m]*) ⊆ Fix(ker φ)` (Lagrange `ker φ ⊆ E₁[m]` + the source-`E₁`
  endomorphism `[m]`-covariance) is **proven two-curve**;
* the two-curve `#ker = deg` reduces (`card_kernel_eq_degree_of_separable_witness`, already
  two-curve in `EC/IsogenyKernel.lean`) to the two-curve good-fibre count
  (`Curves.LocalizedDictionary`, already two-curve).

**The remaining `sorry` (`TwoCurveGeometricDualData`)** is exactly the genuinely cross-curve
generic-point machinery: a *point map* for the `ofEquation`-built `bcIsog` over `K̄` (the affine-kernel
`PullbackEvaluation` obstruction) and its generic-point covariance (`xy_family`) — i.e. relaxing
`mapTranslateGenericPoint_of_pullbackEvaluation` (`WeilPairing/GenericCovarianceGeneral.lean`) and the
kernel-translation torsor (`EC/SeparableKernelTorsor.lean`) to two curves, plus the structural
`mulByInt` base-change identifications.  This is the large multi-file generalization of the
cross-curve generic-point engine; it is isolated here as the named residual. -/
private noncomputable def twoCurveGeometricDualData {F : Type u} [Field F] [DecidableEq F]
    [CharZero F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    TwoCurveGeometricDualData φ :=
  sorry

/-- **The `L`-level two-curve `K̄`-dual range inclusion** — now a thin assembly over the proven
two-curve fixed-field route (`twoCurveKbarRangeInclData_of_geometric`) and the single genuine
geometric leaf (`twoCurveGeometricDualData`). -/
private noncomputable def twoCurveKbarRangeIncl_descended {F : Type u} [Field F] [DecidableEq F]
    [CharZero F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    TwoCurveKbarRangeInclData φ :=
  twoCurveKbarRangeInclData_of_geometric (twoCurveGeometricDualData φ hsep)

private noncomputable def descentData_over_kbar_intermediate {F : Type u} [Field F] [DecidableEq F]
    [CharZero F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    DescentDataOverKbar (⟨W₁⟩ : SmoothPlaneCurve F) ⟨W₂⟩ φ.toCurveMap.pullback
      (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast φ.degree_pos'.ne')) :=
  let d := twoCurveKbarRangeIncl_descended φ hsep
  letI := d.finL
  letI := d.galL
  letI : DecidableEq d.L := d.decL
  { L := d.L
    finL := d.finL
    galL := d.galL
    data :=
      { psiL := TwoCurveBaseChange.psiL W₁ W₂ φ d.L
        mPbL := TwoCurveBaseChange.mPbL W₁ d.L (n := (φ.degree : ℤ))
          (by exact_mod_cast φ.degree_pos'.ne')
        hpsiL_equiv := TwoCurveBaseChange.psiL_galEquivariant W₁ W₂ φ d.L
        hpsiL_inj := TwoCurveBaseChange.psiL_injective W₁ W₂ φ d.L
        hpsiL_nat := fun g => TwoCurveBaseChange.psiL_nat W₁ W₂ φ d.L g
        hmPbL_nat := fun u => TwoCurveBaseChange.mPbL_nat W₁ d.L
          (by exact_mod_cast φ.degree_pos'.ne') u
        hLincl := d.hLincl } }

/-- **The single isolated deep residual of Silverman III.6.1 (descent half), REVIEW-PENDING — now
narrowed to TWO-CURVE BASE-CHANGE only (the field-of-definition half is discharged by MOVE 1).** For
a separable isogeny `φ : E₁ → E₂` over `F`, there is a *finite Galois* extension `L/F` and a
`DescentData` for `φ*` and `[deg φ]*` over `L`: i.e. the two-curve base-change `ψ_L : F(E₂_L) →
F(E₁_L)` of `φ*` and the base-change `[deg φ]_L*` of `[deg φ]*`, with `ψ_L` equivariant/injective,
the base-change naturalities, and the `L`-level range inclusion `Im([deg φ]_L*) ⊆ Im(ψ_L)`.

**UPDATE (this pass): the two-curve base-change DATA is now PROVEN** — the structural `psiL`/`mPbL`
over a finite Galois `L`, their naturalities, `psiL`'s injectivity and full `Gal(L/F)`-equivariance
are all discharged in the `TwoCurveBaseChange` namespace (CoordHom-free, via `ofEquation`). Concretely:

* **Two-curve base-change** (DONE, axiom-clean): `TwoCurveBaseChange.bcIsog` builds `φ_L : E₁_L → E₂_L`
  over a *general* finite `L` (no `IsAlgClosed`, no `CoordHom`) via `EC.Isogeny.ofEquation` applied to
  the pullback generator images. `ψ_L` = `psiL`, `[m]_L*` = `mPbL`, with naturality (`psiL_nat`,
  `mPbL_nat`), injectivity (`psiL_injective`), and full `Gal(L/F)`-equivariance
  (`psiL_galEquivariant`).
* **`K̄`-dual range inclusion** (the L-level inclusion `Im([deg φ]_L*) ⊆ Im(ψ_L)`): **THIS is now the
  single irreducible leaf** (`twoCurveKbarRangeIncl_descended`). It is the two-curve `K̄`-dual
  `Im([m]_K̄*) ⊆ Im(φ_K̄*)` (Silverman III.6.1, `DualGaloisData.hincl`/III.4.10c) restricted to a
  finite Galois `L`. The `DualGaloisData` *structure* is two-curve, but its *constructors*
  (`exists_dual_of_pullbackEvaluation_general` etc.) are endomorphism-only — a two-curve `φ_K̄` has no
  codebase dual, so the `hfix` (III.4.10c fixed-field equality) for two curves is the genuine missing
  infrastructure. Once available, MOVE 1's `galFixed_of_galFixed_top` descends it from `K̄` to `L`.

**MOVE 1 discharges the field-of-definition gap.** The earlier "missing mathlib fact" — a datum over
`AlgebraicClosure F` is defined over a finite Galois subextension — is now supplied by
`exists_finiteGalois_fieldOfDefinition` (a finite set of `K̄`-elements lies in a finite Galois
`L ⊆ K̄`, via mathlib's `FiniteGaloisIntermediateField.adjoin`) together with `instIsGalois_algebraicClosure`
(char-0 ⟹ `K̄/F` Galois) and `galFixed_of_galFixed_top` (`Gal(K̄/F)`-fixed ⟹ `Gal(L/F)`-fixed). So
the residual is no longer "field of definition" — it is exactly the two-curve base-change data.

Everything downstream is proven: `rangeIncl_of_descentData` (the elementwise Galois descent, route
steps 2–4) turns this datum into the `F`-level range inclusion. See `tickets-dual-descent.md`. -/
private noncomputable def exists_descentData_of_separable {F : Type u} [Field F] [DecidableEq F]
    [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    SomeDescentData.{u, u} (C₁ := ⟨W₁⟩) (C₂ := ⟨W₂⟩) φ.toCurveMap.pullback
      (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast φ.degree_pos'.ne')) :=
  -- MOVE 1 (field-of-definition) is discharged: the finite Galois `L` is taken inside
  -- `K̄ = AlgebraicClosure F` (`instIsGalois_algebraicClosure` + `exists_finiteGalois_fieldOfDefinition`),
  -- and `someDescentData_of_overKbar` threads the universe.  The remaining content is the
  -- two-curve base-change `DescentData` over such a concrete `L ⊆ K̄` — the single irreducible leaf
  -- `descentData_over_kbar_intermediate` below.
  someDescentData_of_overKbar (descentData_over_kbar_intermediate φ hsep)

/-- **DUAL-Q4 deep residual** — the `K̄`-dual-plus-descent core (REVIEW-PENDING). For a **separable**
isogeny `φ : E₁ → E₂` over `F`, there is `n ≠ 0` (mathematically `n = deg φ`) and an `F`-rational
faithful `[n]`-witness `HasMulByIntDualWitness φ n hn`, i.e. `Im([n]*) ⊆ Im(φ*)` over `F`.

This is the genuinely-deep content of Silverman III.6.1, isolating the three known mathlib gaps of
the descent assembly:

1. **General two-curve base-change of an isogeny to `K̄`.** The project's
   `EC.Isogeny.baseChangeIsogeny` (`EC/IsogenyAG/BaseChange.lean`) is *endomorphism-only*
   (`W.baseChange L → W.baseChange L`); a general `φ : E₁ → E₂` over `F` needs the two-curve
   base-change `φ_K̄ : E₁_K̄ → E₂_K̄` with its `CoordHom` (`baseChangeXgen`/`baseChangeCoordHom`
   generalized to distinct source/target curves). **Missing:** the two-curve `baseChangeIsogeny`.

2. **Field of definition — DISCHARGED by MOVE 1.** The `K̄`-dual lives over `K̄ = AlgebraicClosure F`,
   which is *infinite*; descent requires it over a *finite* Galois `L/F`. This is now supplied by MOVE 1
   (`exists_finiteGalois_fieldOfDefinition` + `instIsGalois_algebraicClosure` + `galFixed_of_galFixed_top`,
   built on mathlib's `FiniteGaloisIntermediateField.adjoin` and `AlgEquiv.restrictNormalHom_surjective`).
   No longer a gap.

3. **Full base-changed-pullback equivariance.** `descendIsogeny` needs the `K̄`-dual's pullback
   `Gal(L/F)`-equivariant on *all* of `F(C_L)` (DUAL-Q3). `galEquivariant_of_compose` reduces this to
   the equivariance of `φ_L*` and `[n]_L*`; the latter is `galEquivariant_baseChange_on_image` *only
   on the image of `F(E)`* (the easy half). The full statement on all of `F(C_L)` is part of the
   two-curve base-change leaf (once `ψ_L` is the L-linear `baseChangeAlgHom`, equivariance is the
   semilinearity of `σ ⊗ id`).

Once available, the round-trip (`functionFieldMap_comp_descendPullback` + `functionFieldMap`
injectivity, with `Isogeny.mulByInt`/`compose` base-change faithfulness) transports the `K̄` identity
`(ρ_K̄ ∘ φ_K̄)* = [n]*` to this `F`-level range inclusion. See `tickets-dual-descent.md` DUAL-Q4.

Stated at `n = deg φ` (Silverman's value): the *basepoint* leaf of the dual witness is **not** part
of this residual — it is discharged unconditionally (`mulByIntBasepoint_holds` +
`Isogeny.reflects_ordAtInfty`) in `hasMulByIntDualWitness_of_rangeIncl` below. So the entire deep
content of Silverman III.6.1 over a char-0 base is exactly this one range inclusion.

**Decomposition status.** The monolithic range inclusion is a *thin* consequence of the proven
elementwise descent (`rangeIncl_of_descentData`, route steps 2–4 — axiom-clean) over the single named
leaf `descentData_over_kbar_intermediate` (the two-curve base-change `DescentData` over a concrete
finite Galois `L ⊆ K̄`). With MOVE 1 discharging the field-of-definition (gap 2) and the universe
packaging (`someDescentData_of_overKbar`), the leaf is now *only* the two-curve base-change DATA
(gap 1, with gap 3): the L-linear `ψ_L = baseChangeAlgHom` of a `CoordHom` for `φ`, `[m]_L*`, their
naturality/equivariance/injectivity, and the L-restricted `K̄`-dual range inclusion
`Im([m]_L*) ⊆ Im(ψ_L)`. -/
private theorem rationalRangeIncl_of_separable {F : Type u} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast φ.degree_pos'.ne')).range ≤ φ.toCurveMap.pullback.range := by
  have s : SomeDescentData.{u, u} (C₁ := ⟨W₁⟩) (C₂ := ⟨W₂⟩) φ.toCurveMap.pullback
      (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast φ.degree_pos'.ne')) := exists_descentData_of_separable φ hsep
  exact @rangeIncl_of_descentData F _ ⟨W₁⟩ ⟨W₂⟩ _ _ s.L s.fieldL s.algL s.finL s.galL s.data

/-- **The faithful `[deg φ]`-witness from the range inclusion** (the basepoint leaf, fully proved).
Given the deep range inclusion `Im([deg φ]*) ⊆ Im(φ*)` (`rationalRangeIncl_of_separable`), the
faithful dual witness `HasMulByIntDualWitness φ (deg φ)` is assembled: its basepoint field is the
unconditional `Isogeny.hbase_of_reflects` fed by `mulByIntBasepoint_holds` (the `[n]`-basepoint
theorem) and `Isogeny.reflects_ordAtInfty` (the `∞`-regularity reflection). No descent input. -/
private theorem hasMulByIntDualWitness_of_rangeIncl {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂)
    (hincl : (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
        (by exact_mod_cast φ.degree_pos'.ne')).range ≤ φ.toCurveMap.pullback.range) :
    φ.HasMulByIntDualWitness (φ.degree : ℤ) (by exact_mod_cast φ.degree_pos'.ne') where
  hincl := hincl
  hbase := EC.Isogeny.hbase_of_reflects φ
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (φ.degree : ℤ)
      (by exact_mod_cast φ.degree_pos'.ne')) hincl
    (EC.mulByIntBasepoint_holds W₁ (by exact_mod_cast φ.degree_pos'.ne'))
    (EC.Isogeny.reflects_ordAtInfty φ)

/-- **DUAL-Q4 deep residual, assembled** — the separable reverse-isogeny existence (Silverman
III.6.1, char-0 case): from the deep range inclusion (`rationalRangeIncl_of_separable`, the sole
remaining `sorry`) and the proved basepoint leaf (`hasMulByIntDualWitness_of_rangeIncl`), a
separable isogeny over a char-0 base admits an `F`-rational faithful `[deg φ]`-witness. -/
private theorem rationalReverseCompose_of_separable {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) (hsep : φ.IsSeparable) :
    ∃ (n : ℤ) (hn : n ≠ 0), φ.HasMulByIntDualWitness n hn :=
  ⟨(φ.degree : ℤ), by exact_mod_cast φ.degree_pos'.ne',
    hasMulByIntDualWitness_of_rangeIncl φ (rationalRangeIncl_of_separable φ hsep)⟩

/-! ### Char-0 separability and the `F`-level formal payoff

Two leaves of the assembly that are **fully provable at the base field** (no descent input):

* **Char-0 separability** (`isSeparable_of_charZero`): in characteristic zero every isogeny is
  separable, since the function-field extension `K(E₁)/φ*K(E₂)` is algebraic (hence integral) and
  `CharZero` (inherited from `F`), so mathlib's `Algebra.IsSeparable.of_integral` applies. This is
  the input that makes the `K̄` dual machinery (`dualGaloisData_of_pullbackEvaluation_general`,
  which requires `β.IsSeparable`) available over a char-0 base.

* **The formal compose payoff** (`rationalDualCompose_of_hasMulByIntDualWitness`): once an
  `F`-rational faithful `[n]`-witness `HasMulByIntDualWitness φ n hn` is in hand, the reverse isogeny
  `φ̂ = mulByIntDual w` satisfies `φ̂ ∘ φ = [n]` *purely formally* — `(φ̂ ∘ φ)* = [n]*` is
  `dualOfWitness_comp_pullback`, and `Isogeny.ext_toCurveMap`/`CurveMap.ext` turn pullback equality
  into isogeny equality. (This is the inline form of `Isogeny.mulByIntDual_compose`, which lives in
  the un-imported `MulByIntPullbackComp`.) Hence the whole headline reduces to producing such a
  witness — the genuinely-deep `K̄`-dual-plus-descent content, isolated in
  `rationalReverseCompose_of_separable` below. -/

/-- **Char-0 ⟹ separable** (Silverman III.4.5, characteristic-zero case). An isogeny over a
characteristic-zero field is separable: the function-field extension `K(E₁)/φ*K(E₂)` is
finite-dimensional and algebraic (`Isogeny.finiteDimensional_toAlgebra`), hence integral, and has
characteristic zero (inherited from `F`), so it is separable by `Algebra.IsSeparable.of_integral`.
Bridged to the EC-sense `IsSeparable` via `Isogeny.isSeparable_iff_algebra_isSeparable`. -/
theorem isSeparable_of_charZero [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) : φ.IsSeparable := by
  -- bridge the EC-sense (`inseparableDegree = 1`) to `Algebra.IsSeparable`
  rw [EC.Isogeny.isSeparable_iff_algebra_isSeparable]
  letI : Algebra W₂.FunctionField W₁.FunctionField := φ.toCurveMap.toAlgebra
  haveI : CharZero W₂.FunctionField :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F W₂.FunctionField)
  haveI : Algebra.IsAlgebraic W₂.FunctionField W₁.FunctionField :=
    ⟨fun z => Curves.CurveMap.isAlgebraic_toAlgebra φ.toCurveMap z⟩
  -- `Algebra.IsAlgebraic.isIntegral` (over a field) + `Algebra.IsSeparable.of_integral` (char 0)
  -- are both instances, so `Algebra.IsSeparable` is found by instance resolution.
  infer_instance

/-- **The formal compose payoff** (Silverman III.6.1 defining identity, isogeny form). From an
`F`-rational faithful `[n]`-witness for `φ`, the dual `mulByIntDual w` is a reverse isogeny
`E₂ → E₁` with `(mulByIntDual w) ∘ φ = [n]`. This is `dualOfWitness_comp_pullback` (the pullback
identity `(φ̂ ∘ φ)* = [n]*`) promoted to an isogeny equality via `Isogeny.ext_toCurveMap`/
`CurveMap.ext` — no descent input, the inline `Isogeny.mulByIntDual_compose`. -/
theorem rationalDualCompose_of_hasMulByIntDualWitness
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    {φ : EC.Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) :
    (EC.Isogeny.mulByIntDual w).compose φ = EC.Isogeny.mulByInt W₁ hn := by
  refine EC.Isogeny.ext_toCurveMap (Curves.CurveMap.ext (AlgHom.ext fun z => ?_))
  show φ.toCurveMap.pullback ((EC.Isogeny.mulByIntDual w).toCurveMap.pullback z) =
    (EC.Isogeny.mulByInt W₁ hn).toCurveMap.pullback z
  rw [EC.Isogeny.mulByInt_pullback]
  exact EC.Isogeny.mulByIntDual_comp_pullback w z

/-- **DUAL-Q4 residual** (the assembled DUAL-Q1–Q3 chain, char-0): every isogeny `φ : E₁ → E₂` over a
char-0 field has an `F`-rational reverse isogeny `ρ : E₂ → E₁` with `ρ ∘ φ = [deg φ]`.

This is the dual `φ̂` over `F` from Silverman III.6.1: base-change `φ` to `K̄ = AlgebraicClosure F`
(char 0 ⟹ separable, `isSeparable_of_charZero`), build the K̄ dual `φ̂_K̄`
(`exists_dual_of_pullbackEvaluation_general`), descend to `φ̂` over the finite Galois field of
definition `L/F` (DUAL-Q2 `descendIsogeny`, with the dual's pullback `Gal(L/F)`-equivariant by
DUAL-Q3 `galEquivariant_of_compose`), and transport the K̄ identity `φ̂_K̄ ∘ φ_K̄ = [m]` back to `F`
(round-trip + base-change faithfulness).

Reduced (this file) to the single named residual `rationalReverseCompose_of_separable`: produce, for
a **separable** isogeny over a char-0 field, an `F`-rational faithful `[n]`-witness. Everything
downstream — the reverse isogeny and the `∘ = [n]` identity — is the proven formal payoff
`rationalDualCompose_of_hasMulByIntDualWitness`. -/
theorem rationalDualCompose_of_charZero {F : Type*} [Field F] [DecidableEq F] [CharZero F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) :
    ∃ (n : ℤ) (hn : n ≠ 0) (ρ : EC.Isogeny W₂ W₁),
      ρ.compose φ = EC.Isogeny.mulByInt W₁ hn := by
  obtain ⟨n, hn, w⟩ := rationalReverseCompose_of_separable φ (isSeparable_of_charZero φ)
  exact ⟨n, hn, EC.Isogeny.mulByIntDual w, rationalDualCompose_of_hasMulByIntDualWitness w⟩

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
