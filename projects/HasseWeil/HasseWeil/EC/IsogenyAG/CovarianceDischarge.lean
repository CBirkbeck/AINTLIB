/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.DualAdditivity

/-!
# Discharging the `[n]`-pullback covariance for the `PullbackEvaluation` class

`EC/IsogenyAG/CanonicalDual.lean` carries **one** named hypothesis through the second
composition, the double dual and the composition reversal: the pullback covariance
`Isogeny.MulByIntPullbackCovariant φ n` (`[n]* ∘ φ* = φ* ∘ [n]*`, the function-field shadow
of Silverman III.4.8 `[n] ∘ φ = φ ∘ [n]`).  For an abstract `EC.Isogeny` it is the open
generic-point covariance leaf (DUAL-2).  This file **discharges it for the
`PullbackEvaluation` class** — every isogeny whose pullback is realised by a coherent
`Basic.Isogeny` carrying the cofinite pullback-evaluation witness of
`WeilPairing/GenericCovarianceGeneral.lean` — using the separation engine of
`EC/IsogenyAG/DualAdditivity.lean`.

## The route

Both sides of the covariance are the pullbacks of *composite* `Basic.Isogeny`s:

* `[n]* ∘ β*  = (β ∘ [n])*` — stored point map `P ↦ β(n • P)`;
* `β* ∘ [n]*  = ([n] ∘ β)*` — stored point map `P ↦ n • β(P)`.

The stored point maps agree **everywhere**, by `map_zsmul` — for the abstract interface the
group-law content of III.4.8 lives in the bundling of `toAddMonoidHom`, so no geometric
input is needed.  The separation engine (`Isogeny.pullback_eq_of_pointMap_eqOn_infinite`)
then forces the pullbacks to agree, provided the two composites carry pullback-evaluation
witnesses.  Those are built from two new reusable pieces:

1. **The `[n]`-witness** (`pullbackEvaluation_mulByInt`): away from the finite zero set of
   the division polynomial `ψ_n`, the point `n • P` is affine with coordinates
   `(φ_n(P)/ψ_n(P)², ω_n(P)/ψ_n(P)³)` (`zsmul_affine_point_eq_general`, the all-points
   division-polynomial evaluation over an arbitrary field), and the pulled-back generators
   `[n]^* x_gen = Φ_n/ΨSq_n`, `[n]^* y_gen = ω_n/ψ_n³` evaluate there to exactly these
   values (`evaluatesTo_algebraMap_mk` + the coordinate-ring identities `mk_φ`, `mk_ψ`,
   `mk_Ψ_sq`).
2. **Witnesses compose** (`PullbackEvaluation.comp`): the heart is the *evaluation
   transport* `PullbackEvaluation.pullback_evaluatesTo` — if `g` takes the value `c` at the
   image point `Q = β(P)`, then `β^* g` takes the value `c` at `P`.  Writing `g − c = a/b`
   with `a, b` in the coordinate ring and `b` not vanishing at `Q` (possible exactly
   because `g − c` lies in the local ring at `Q`,
   `mem_localRingAt_image_of_pointValuation_le_one`), this reduces to coordinate-ring
   elements, where it is a polynomial induction from the two generator evaluations of the
   witness.

## Main results

* `HasseWeil.zsmul_affine_point_eq_general` — the division-polynomial coordinates of
  `n • P` at any nonsingular point with `ψ_n(P) ≠ 0`, over **any** field (the
  base-field instance of `zsmul_affine_point_eq`, whose proof is field-generic).
* `WeilPairing.PullbackEvaluation.pullback_evaluatesTo` — evaluation transport along a
  witnessed pullback.
* `WeilPairing.PullbackEvaluation.comp` (+ `comp_bad_finite`) — witnesses compose.
* `WeilPairing.pullbackEvaluation_mulByInt` (+ `mulByIntSingular_finite`) — the
  `[n]`-witness with bad set `{ψ_n = 0}`.
* `WeilPairing.mulByInt_pullbackAlgHom_comm_of_pullbackEvaluation` — **the covariance at
  the Basic level**: `[n]*(β^* u) = β^*([n]* u)` for every witnessed `β`, over `K̄`.
* `EC.Isogeny.mulByIntPullbackCovariant_of_pullbackEvaluation` — **the main deliverable**:
  the class discharge of `MulByIntPullbackCovariant`.
* Hypothesis-free (`hcov`-free) forms of the `CanonicalDual.lean` corollaries for the
  class: `compose_mulByInt_of_pullbackEvaluation` (III.4.8 bundled),
  `compose_mulByIntDual_of_pullbackEvaluation` (III.6.2(a)),
  `HasMulByIntDualWitness.dual_of_pullbackEvaluation`,
  `mulByIntDual_mulByIntDual_of_pullbackEvaluation` (III.6.2(e)),
  `mulByIntDual_compose_reverse_of_pullbackEvaluation` (III.6.2(b)), and the canonical
  (`n = deg φ`) forms `compose_canonicalDual_of_pullbackEvaluation`,
  `canonicalDual_hasCanonicalDualWitness_of_pullbackEvaluation`,
  `canonicalDual_canonicalDual_of_pullbackEvaluation`,
  `canonicalDual_compose_reverse_of_pullbackEvaluation`.
* `EC.Isogeny.relativeFrobenius_mulByIntPullbackCovariant` — the **cross-curve**
  covariance of `Frob_{p^e} : E → E^{(p^e)}` against `[n]`, a *theorem* (no carried
  hypotheses, no algebraic closure): the division polynomials of the twist are the
  coefficient-twists of the originals, and the relative-Frobenius pullback is the
  `p^e`-th-power map.  Payoff: `relativeFrobenius_compose_relativeVerschiebungOf`
  (`Frob ∘ V̂ = [p^e]`, III.6.2(a)), `relativeVerschiebungOf_hasMulByIntDualWitness`, and
  `relativeVerschiebungOf_dual_eq_relativeFrobenius` — **the relative-Frobenius double
  dual `V̂^ = Frob`** (III.6.2(e)), the residual instantiation named in
  `CanonicalDual.lean`, with axiom-clean finite-base forms.

## Honest scoping

* The discharge is at the **endomorphism** level (`W.toAffine → W.toAffine`) over an
  **algebraically closed** base — the level at which `PullbackEvaluation` and the
  separation engine live.  The infinitude of `E(F̄)` (`smoothPoint_infinite`) is what makes
  the separation argument bite.
* The input is the per-isogeny coherence package `(β, h_pb, hw)`: a `Basic.Isogeny` with
  the same pullback as the `EC.Isogeny` and a cofinite pullback-evaluation witness.  This
  is the project's honest irreducible input for the abstract two-independent-fields
  interface (the same package consumed by `mapTranslateGenericPoint_of_pullbackEvaluation`
  and `dual_add_pullback`); for an isogeny with a `CoordHom` it holds with `bad = ∅`
  (`pullbackEvaluation_of_coordHom`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.4.2, III.4.8, III.6.1–III.6.2,
  II.1.2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

/-! ### The division-polynomial coordinates of `n • P` over an arbitrary field

`EC/GenericPointZsmul.lean` proves `zsmul_affine_point_eq` for points of the base-changed
curve `W_KE` over the function field; the proof is generic in the field, so we restate it
for an arbitrary `V : WeierstrassCurve F₀` — the instance we need is `V := W` itself,
evaluated at the (closed) smooth points of `E(F̄)`. -/

section ZsmulGeneral

variable {F₀ : Type*} [Field F₀] [DecidableEq F₀] (V : WeierstrassCurve F₀)

/-- **The division-polynomial coordinates of `n • P`** (Silverman III.4.2, all-points form,
arbitrary field): at any nonsingular `(x₀, y₀)` with `ψ_m(x₀, y₀) ≠ 0`, the point
`m • (x₀, y₀)` is affine with coordinates
`(φ_m(x₀,y₀)/ψ_m(x₀,y₀)², ω_m(x₀,y₀)/ψ_m(x₀,y₀)³)`.  Field-generic re-statement of
`zsmul_affine_point_eq` (whose proof never uses the function-field structure). -/
theorem zsmul_affine_point_eq_general (m : ℤ) {x₀ y₀ : F₀}
    (h_ns : V.toAffine.Nonsingular x₀ y₀)
    (h_ψ_ne : (V.ψ m).evalEval x₀ y₀ ≠ 0) :
    ∃ h_ns' : V.toAffine.Nonsingular
        ((V.φ m).evalEval x₀ y₀ / (V.ψ m).evalEval x₀ y₀ ^ 2)
        ((V.ω m).evalEval x₀ y₀ / (V.ψ m).evalEval x₀ y₀ ^ 3),
      m • Affine.Point.some x₀ y₀ h_ns =
        Affine.Point.some _ _ h_ns' := by
  have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := V) h_ns m
  have hZ : smulEval V x₀ y₀ m 2 ≠ 0 := h_ψ_ne
  have h_ns_smulEval :
      WeierstrassCurve.Jacobian.Nonsingular V.toJacobian (smulEval V x₀ y₀ m) := by
    have h_ns_jac := (m • WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some x₀ y₀ h_ns)).nonsingular
    change WeierstrassCurve.Jacobian.NonsingularLift _ _ at h_ns_jac
    rw [h_smulEval] at h_ns_jac
    exact h_ns_jac
  have h_ns_affine :
      V.toAffine.Nonsingular
        (smulEval V x₀ y₀ m 0 / smulEval V x₀ y₀ m 2 ^ 2)
        (smulEval V x₀ y₀ m 1 / smulEval V x₀ y₀ m 2 ^ 3) :=
    (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hZ).mp h_ns_smulEval
  refine ⟨h_ns_affine, ?_⟩
  have h_inv :
      WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V
        (WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x₀ y₀ h_ns)) =
      Affine.Point.some x₀ y₀ h_ns :=
    (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V).right_inv _
  have h_toAffine :
      m • Affine.Point.some x₀ y₀ h_ns =
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) := by
    have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V)
      m (WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some x₀ y₀ h_ns))
    rw [WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply] at h
    rw [show WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V
      (WeierstrassCurve.Jacobian.Point.fromAffine _) =
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (WeierstrassCurve.Jacobian.Point.fromAffine _) from rfl] at h
    have h2 : WeierstrassCurve.Jacobian.Point.toAffineLift
        (WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
        Affine.Point.some x₀ y₀ h_ns := by
      rw [← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
      exact h_inv
    rw [h2] at h
    exact h.symm
  rw [h_toAffine]
  have h_eq_lift :
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
      WeierstrassCurve.Jacobian.Point.toAffine V (smulEval V x₀ y₀ m) := by
    unfold WeierstrassCurve.Jacobian.Point.toAffineLift
    rw [h_smulEval]
    rfl
  rw [h_eq_lift, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero h_ns_smulEval hZ]
  rfl

end ZsmulGeneral

end HasseWeil

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

/-! ### Coordinate-ring elements evaluate -/

/-- **Coordinate-ring elements evaluate**: the function-field image of `mk p` takes the
value `p(P.x, P.y)` at every smooth `P`.  The residue computation of
`pullbackEvaluation_of_coordHom`, packaged with the value in `evalEval` form. -/
theorem evaluatesTo_algebraMap_mk (P : (W_smooth W).SmoothPoint)
    (p : Polynomial (Polynomial F)) :
    EvaluatesTo W P (algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial p))
      (p.evalEval P.x P.y) := by
  have h1 : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial p) =
      p.evalEval P.x P.y := (W_smooth W).evalAt_mk P p
  have h2 : (W_smooth W).evalAt P (algebraMap F W.toAffine.CoordinateRing
      (p.evalEval P.x P.y)) = p.evalEval P.x P.y := (W_smooth W).evalAt_algebraMap P _
  have hval : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial p -
      algebraMap F R (p.evalEval P.x P.y)) = 0 := by
    have h3 : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial p -
        algebraMap F R (p.evalEval P.x P.y)) =
        (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial p) -
        (W_smooth W).evalAt P (algebraMap F R (p.evalEval P.x P.y)) := map_sub _ _ _
    rw [h3, h1, h2, sub_self]
  have hmem : AdjoinRoot.mk W.toAffine.polynomial p -
      algebraMap F R (p.evalEval P.x P.y) ∈ (W_smooth W).maximalIdealAt P :=
    (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr hval
  have hrw : algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial p) -
      algebraMap F KE (p.evalEval P.x P.y) =
      algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial p -
        algebraMap F R (p.evalEval P.x P.y)) := by
    rw [IsScalarTower.algebraMap_apply F R KE (p.evalEval P.x P.y)]
    exact (map_sub (algebraMap R KE) _ _).symm
  unfold EvaluatesTo
  rw [hrw]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := W_smooth W) _ P).mpr hmem

/-- **The good-fraction representation of a local function** (curve-generic, to keep the
localization instances uniform): a function with `v_Q ≤ 1` is a quotient of coordinate-ring
elements whose denominator does not vanish at `Q`.  Lift to the local ring at `Q`
(`mem_localRingAt_image_of_pointValuation_le_one`) and clear the `mk'` denominator. -/
private theorem exists_mul_algebraMap_eq_of_pointValuation_le_one
    {C : SmoothPlaneCurve F} {Q : C.SmoothPoint} {h : C.FunctionField}
    (hh : C.pointValuation Q h ≤ 1) :
    ∃ a b : C.CoordinateRing, b ∉ C.maximalIdealAt Q ∧
      h * algebraMap C.CoordinateRing C.FunctionField b =
        algebraMap C.CoordinateRing C.FunctionField a := by
  obtain ⟨xL, hxL⟩ :=
    Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one h hh
  obtain ⟨a, s, hmk⟩ := IsLocalization.exists_mk'_eq (C.maximalIdealAt Q).primeCompl xL
  refine ⟨a, (s : C.CoordinateRing), s.prop, ?_⟩
  have h2 : algebraMap (C.localRingAt Q) C.FunctionField
        (IsLocalization.mk' (C.localRingAt Q) a s) *
      algebraMap (C.localRingAt Q) C.FunctionField
        (algebraMap C.CoordinateRing (C.localRingAt Q) (s : C.CoordinateRing)) =
      algebraMap (C.localRingAt Q) C.FunctionField
        (algebraMap C.CoordinateRing (C.localRingAt Q) a) :=
    (map_mul (algebraMap (C.localRingAt Q) C.FunctionField) _ _).symm.trans
      (congrArg (algebraMap (C.localRingAt Q) C.FunctionField)
        (IsLocalization.mk'_spec (C.localRingAt Q) a s))
  rw [hmk, hxL,
    ← IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q) C.FunctionField,
    ← IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt Q)
      C.FunctionField] at h2
  exact h2

/-! ### Evaluation transport along a witnessed pullback

The composition piece for `EvaluatesTo`: if the two pulled-back generators evaluate at `P`
to the coordinates of `Q`, then the pullback of *any* function with a value at `Q` takes
that value at `P`. -/

variable {W} in
/-- Polynomial core of the transport: from the two generator evaluations, the pullback of
every coordinate-ring element `mk p` evaluates at `P` to `p(Q.x, Q.y)`.  Double polynomial
induction through `EvaluatesTo` arithmetic. -/
private theorem pullback_mk_evaluatesTo {β : Isogeny W.toAffine W.toAffine}
    {P Q : (W_smooth W).SmoothPoint}
    (hx : EvaluatesTo W P (β.pullback (x_gen W)) Q.x)
    (hy : EvaluatesTo W P (β.pullback (y_gen W)) Q.y)
    (p : Polynomial (Polynomial F)) :
    EvaluatesTo W P (β.pullback (algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial p)))
      (p.evalEval Q.x Q.y) := by
  -- the generator atoms in `mk` form (definitional re-typing of the witness facts)
  have hxAtom : EvaluatesTo W P (β.pullback (algebraMap R KE
      (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X)))) Q.x := hx
  have hyAtom : EvaluatesTo W P (β.pullback (algebraMap R KE
      (AdjoinRoot.mk W.toAffine.polynomial Polynomial.X))) Q.y := hy
  induction p using Polynomial.induction_on with
  | C q =>
    rw [Polynomial.evalEval_C]
    induction q using Polynomial.induction_on with
    | C c =>
      have h1 : algebraMap R KE (AdjoinRoot.mk W.toAffine.polynomial
          (Polynomial.C (Polynomial.C c))) = algebraMap F KE c := by
        rw [show AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (Polynomial.C c)) =
          algebraMap F R c from rfl, ← IsScalarTower.algebraMap_apply F R KE]
      rw [Polynomial.eval_C, h1, β.pullback.commutes c]
      exact evaluatesTo_algebraMap P c
    | add q₁ q₂ ih₁ ih₂ =>
      simp only [map_add, Polynomial.eval_add] at ih₁ ih₂ ⊢
      exact ih₁.add ih₂
    | monomial k c ih =>
      rw [show (Polynomial.C c * Polynomial.X ^ (k + 1) : Polynomial F) =
        Polynomial.C c * Polynomial.X ^ k * Polynomial.X by rw [pow_succ, ← mul_assoc]]
      simp only [map_mul, Polynomial.eval_mul, Polynomial.eval_X] at ih ⊢
      exact ih.mul hxAtom
  | add p₁ p₂ ih₁ ih₂ =>
    simp only [map_add, Polynomial.evalEval_add] at ih₁ ih₂ ⊢
    exact ih₁.add ih₂
  | monomial k q ih =>
    rw [show (Polynomial.C q * Polynomial.X ^ (k + 1) : Polynomial (Polynomial F)) =
      Polynomial.C q * Polynomial.X ^ k * Polynomial.X by rw [pow_succ, ← mul_assoc]]
    simp only [map_mul, Polynomial.evalEval_mul, Polynomial.evalEval_X] at ih ⊢
    exact ih.mul hyAtom

variable {W} in
/-- **Evaluation transport along a witnessed pullback**: if the stored point map sends `P`
(good for the witness) to the smooth point `Q`, and `g` evaluates to `c` at `Q`, then
`β^* g` evaluates to `c` at `P`.

`g − c` lies in the local ring at `Q` (its valuation is `< 1`), so it is a quotient `a/b`
of coordinate-ring elements with `b(Q) ≠ 0` and `a(Q) = 0`
(`mem_localRingAt_image_of_pointValuation_le_one`); the polynomial core
`pullback_mk_evaluatesTo` evaluates the pullbacks of `a` and `b`, and `EvaluatesTo`
arithmetic finishes. -/
theorem PullbackEvaluation.pullback_evaluatesTo {β : Isogeny W.toAffine W.toAffine}
    {bad : Set (W_smooth W).SmoothPoint} (hw : PullbackEvaluation W β bad)
    {P Q : (W_smooth W).SmoothPoint} (hP : P ∉ bad)
    (hQ : β.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint)
    {g : KE} {c : F} (hg : EvaluatesTo W Q g c) :
    EvaluatesTo W P (β.pullback g) c := by
  classical
  obtain ⟨x', y', h', heq, hx, hy⟩ := hw P hP
  -- identify the witness coordinates with `Q`'s
  have hQ' : (WeierstrassCurve.Affine.Point.some Q.x Q.y Q.nonsingular :
      W.toAffine.Point) = WeierstrassCurve.Affine.Point.some x' y' h' :=
    hQ.symm.trans heq
  obtain ⟨hQx, hQy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hQ'
  have hxQ : EvaluatesTo W P (β.pullback (x_gen W)) Q.x := by rw [hQx]; exact hx
  have hyQ : EvaluatesTo W P (β.pullback (y_gen W)) Q.y := by rw [hQy]; exact hy
  -- coordinate-ring elements transport
  have key : ∀ z : R, EvaluatesTo W P (β.pullback (algebraMap R KE z))
      ((W_smooth W).evalAt Q z) := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    have hval : (W_smooth W).evalAt Q (AdjoinRoot.mk W.toAffine.polynomial p) =
        p.evalEval Q.x Q.y := (W_smooth W).evalAt_mk Q p
    rw [hval]
    exact pullback_mk_evaluatesTo hxQ hyQ p
  -- write `g − c` as a good fraction over the local ring at `Q`
  obtain ⟨a, b, hbm', hfrac'⟩ :=
    exists_mul_algebraMap_eq_of_pointValuation_le_one (C := W_smooth W)
      (h := g - algebraMap F KE c) (le_of_lt hg)
  have hsm : b ∉ (W_smooth W).maximalIdealAt Q := hbm'
  have hfrac : (g - algebraMap F KE c) * algebraMap R KE b = algebraMap R KE a := hfrac'
  have hsne0 : b ≠ 0 := fun hc ↦
    hsm (hc ▸ Ideal.zero_mem ((W_smooth W).maximalIdealAt Q))
  have hsKE : algebraMap R KE b ≠ 0 := fun hc ↦
    hsne0 (IsFractionRing.injective R KE (hc.trans (map_zero _).symm))
  have hsval : (W_smooth W).evalAt Q b ≠ 0 := fun hc ↦
    hsm ((W_smooth W).ker_evalAt Q ▸ RingHom.mem_ker.mpr hc)
  -- the numerator vanishes at `Q`
  have hav : (W_smooth W).pointValuation Q (algebraMap R KE a) < 1 := by
    calc (W_smooth W).pointValuation Q (algebraMap R KE a)
        = (W_smooth W).pointValuation Q ((g - algebraMap F KE c) *
            algebraMap R KE b) := by rw [hfrac]
      _ = (W_smooth W).pointValuation Q (g - algebraMap F KE c) *
            (W_smooth W).pointValuation Q (algebraMap R KE b) :=
          Valuation.map_mul _ _ _
      _ ≤ (W_smooth W).pointValuation Q (g - algebraMap F KE c) * 1 :=
          mul_le_mul' le_rfl ((W_smooth W).pointValuation_algebraMap_le_one b Q)
      _ = (W_smooth W).pointValuation Q (g - algebraMap F KE c) := mul_one _
      _ < 1 := hg
  have ham : a ∈ (W_smooth W).maximalIdealAt Q :=
    (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) a Q).mp hav
  have haval : (W_smooth W).evalAt Q a = 0 :=
    RingHom.mem_ker.mp ((W_smooth W).ker_evalAt Q ▸ ham)
  -- assemble: `β^*(g − c)` evaluates to `0`
  have hdivKE : g - algebraMap F KE c = algebraMap R KE a / algebraMap R KE b :=
    (eq_div_iff hsKE).mpr hfrac
  have hsub : EvaluatesTo W P (β.pullback (g - algebraMap F KE c)) 0 := by
    rw [hdivKE, map_div₀]
    have h := (key a).div (key b) hsval
    rwa [haval, zero_div] at h
  -- and `β^* g = β^*(g − c) + c`
  have hgsplit : β.pullback g =
      β.pullback (g - algebraMap F KE c) + algebraMap F KE c := by
    rw [map_sub, β.pullback.commutes c, sub_add_cancel]
  have h := hsub.add (evaluatesTo_algebraMap P c)
  rw [zero_add] at h
  rwa [← hgsplit] at h

/-! ### Pullback-evaluation witnesses compose -/

variable {W} in
/-- **Pullback-evaluation witnesses compose**: a witness for `β₁` and a witness for `β₂`
yield a witness for `β₁ ∘ β₂` (stored point map `P ↦ β₁(β₂ P)`), with bad set
`bad₂ ∪ β₂⁻¹(bad₁)`.  The pullback of the composite factors as `β₂^* ∘ β₁^*`, and the
evaluation transport moves `β₁`'s generator evaluations from `β₂(P)` to `P`. -/
theorem PullbackEvaluation.comp {β₁ β₂ : Isogeny W.toAffine W.toAffine}
    {bad₁ bad₂ : Set (W_smooth W).SmoothPoint}
    (hw₁ : PullbackEvaluation W β₁ bad₁) (hw₂ : PullbackEvaluation W β₂ bad₂) :
    PullbackEvaluation W (β₁.comp β₂)
      (bad₂ ∪ {P : (W_smooth W).SmoothPoint |
        ∃ Q ∈ bad₁, β₂.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint}) := by
  intro P hP
  have hP₂ : P ∉ bad₂ := fun hc ↦ hP (Set.mem_union_left _ hc)
  obtain ⟨x₂, y₂, h₂, heq₂, hx₂, hy₂⟩ := hw₂ P hP₂
  have heqQ : β₂.toAddMonoidHom P.toAffinePoint =
      (⟨x₂, y₂, h₂⟩ : (W_smooth W).SmoothPoint).toAffinePoint := heq₂
  have hQ₁ : (⟨x₂, y₂, h₂⟩ : (W_smooth W).SmoothPoint) ∉ bad₁ := fun hc ↦
    hP (Set.mem_union_right _ ⟨⟨x₂, y₂, h₂⟩, hc, heqQ⟩)
  obtain ⟨x₁, y₁, h₁, heq₁, hx₁, hy₁⟩ := hw₁ ⟨x₂, y₂, h₂⟩ hQ₁
  refine ⟨x₁, y₁, h₁, ?_, ?_, ?_⟩
  · change β₁.toAddMonoidHom (β₂.toAddMonoidHom P.toAffinePoint) = _
    rw [heqQ]
    exact heq₁
  · change EvaluatesTo W P (β₂.pullback (β₁.pullback (x_gen W))) x₁
    exact hw₂.pullback_evaluatesTo hP₂ heqQ hx₁
  · change EvaluatesTo W P (β₂.pullback (β₁.pullback (y_gen W))) y₁
    exact hw₂.pullback_evaluatesTo hP₂ heqQ hy₁

variable {W} in
/-- The composite bad set is finite: `bad₂` is finite and the `β₂`-preimage of the finite
`bad₁` is a finite union of fibres (`PullbackEvaluation.finite_fiber`). -/
theorem PullbackEvaluation.comp_bad_finite {β₂ : Isogeny W.toAffine W.toAffine}
    {bad₁ bad₂ : Set (W_smooth W).SmoothPoint} (hb₁ : bad₁.Finite) (hb₂ : bad₂.Finite)
    (hw₂ : PullbackEvaluation W β₂ bad₂) :
    (bad₂ ∪ {P : (W_smooth W).SmoothPoint |
      ∃ Q ∈ bad₁, β₂.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint}).Finite := by
  refine hb₂.union ?_
  have h : {P : (W_smooth W).SmoothPoint |
      ∃ Q ∈ bad₁, β₂.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint} =
      ⋃ Q ∈ bad₁, {P : (W_smooth W).SmoothPoint |
        β₂.toAddMonoidHom P.toAffinePoint = Q.toAffinePoint} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [h]
  exact hb₁.biUnion fun Q _ ↦ hw₂.finite_fiber hb₂ Q.toAffinePoint

/-! ### The `[n]`-witness: division polynomials evaluate the multiplication map -/

/-- The bad set of the `[n]`-witness: the zero locus of the division polynomial `ψ_n`
(containing the affine `n`-torsion, where `[n]^* x_gen` has poles). -/
def mulByIntSingular (n : ℤ) : Set (W_smooth W).SmoothPoint :=
  {P : (W_smooth W).SmoothPoint | (W.ψ n).evalEval P.x P.y = 0}

/-- The zero locus of `ψ_n` is finite for `n ≠ 0`: it sits inside the zero set of the
nonzero function `ψ_ff W n ∈ K(E)` (Silverman II.1.2, `finite_setOf_ord_P_nonzero`). -/
theorem mulByIntSingular_finite (n : ℤ) (hn : n ≠ 0) : (mulByIntSingular W n).Finite := by
  have hψff : ψ_ff W n ≠ 0 := ψ_ff_ne_zero W hn
  refine ((W_smooth W).finite_setOf_ord_P_nonzero hψff).subset ?_
  intro P hP
  simp only [mulByIntSingular, Set.mem_setOf_eq] at hP
  rw [Set.mem_setOf_eq]
  have h1 : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial (W.ψ n)) =
      (W.ψ n).evalEval P.x P.y := (W_smooth W).evalAt_mk P (W.ψ n)
  have hmem : AdjoinRoot.mk W.toAffine.polynomial (W.ψ n) ∈
      (W_smooth W).maximalIdealAt P :=
    (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr (h1.trans hP)
  have hval : (W_smooth W).pointValuation P (ψ_ff W n) < 1 :=
    (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) _ P).mpr hmem
  have h2 : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P (ψ_ff W n) :=
    (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (P := P) hψff).mpr hval
  intro h0
  rw [h0] at h2
  have h2' : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast h2
  exact absurd (WithTop.coe_le_coe.mp h2') (by norm_num)

/-- **The pullback-evaluation witness for `[n]`** (the all-points division-polynomial
evaluation): away from the zero locus of `ψ_n`, the stored point map computes
`n • P = (φ_n(P)/ψ_n(P)², ω_n(P)/ψ_n(P)³)` (`zsmul_affine_point_eq_general`), and the
pulled-back generators `[n]^* x_gen = Φ_n/ΨSq_n`, `[n]^* y_gen = ω_n/ψ_n³` evaluate at `P`
to exactly these coordinates — the `x`-side after the on-curve identities
`φ_n = Φ_n`, `ψ_n² = ΨSq_n` in the coordinate ring (`mk_φ`, `mk_ψ`, `mk_Ψ_sq`). -/
theorem pullbackEvaluation_mulByInt (n : ℤ) (hn : n ≠ 0) :
    PullbackEvaluation W (mulByInt W.toAffine n) (mulByIntSingular W n) := by
  intro P hP
  simp only [mulByIntSingular, Set.mem_setOf_eq] at hP
  have hψ : (W.ψ n).evalEval P.x P.y ≠ 0 := hP
  obtain ⟨h_ns', h_eq⟩ := zsmul_affine_point_eq_general W n P.nonsingular hψ
  -- the on-curve identities `φ_n = Φ_n` and `ψ_n² = ΨSq_n` at `P`
  have hφΦ : (W.φ n).evalEval P.x P.y = (W.Φ n).eval P.x := by
    have h1 : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial (W.φ n)) =
        (W.φ n).evalEval P.x P.y := (W_smooth W).evalAt_mk P (W.φ n)
    have h2 : (W_smooth W).evalAt P
        (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.Φ n))) =
        (Polynomial.C (W.Φ n)).evalEval P.x P.y := (W_smooth W).evalAt_mk P _
    have h3 : AdjoinRoot.mk W.toAffine.polynomial (W.φ n) =
        AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.Φ n)) :=
      WeierstrassCurve.Affine.CoordinateRing.mk_φ (W := W.toAffine) n
    rw [← h1, h3, h2, Polynomial.evalEval_C]
  have hψΨ : (W.ψ n).evalEval P.x P.y ^ 2 = (W.ΨSq n).eval P.x := by
    have h1 : (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial (W.ψ n)) =
        (W.ψ n).evalEval P.x P.y := (W_smooth W).evalAt_mk P (W.ψ n)
    have h2 : (W_smooth W).evalAt P
        (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.ΨSq n))) =
        (Polynomial.C (W.ΨSq n)).evalEval P.x P.y := (W_smooth W).evalAt_mk P _
    have h3 : AdjoinRoot.mk W.toAffine.polynomial (W.ψ n) ^ 2 =
        AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.ΨSq n)) := by
      have hψΨ' : AdjoinRoot.mk W.toAffine.polynomial (W.ψ n) =
          AdjoinRoot.mk W.toAffine.polynomial (W.Ψ n) :=
        WeierstrassCurve.Affine.CoordinateRing.mk_ψ (W := W.toAffine) n
      rw [hψΨ']
      exact WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq (W := W.toAffine) n
    calc (W.ψ n).evalEval P.x P.y ^ 2
        = (W_smooth W).evalAt P (AdjoinRoot.mk W.toAffine.polynomial (W.ψ n)) ^ 2 := by
          rw [h1]
      _ = (W_smooth W).evalAt P
            (AdjoinRoot.mk W.toAffine.polynomial (W.ψ n) ^ 2) := (map_pow _ _ _).symm
      _ = (W_smooth W).evalAt P
            (AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C (W.ΨSq n))) :=
          congrArg ((W_smooth W).evalAt P) h3
      _ = (W.ΨSq n).eval P.x := by rw [h2, Polynomial.evalEval_C]
  -- the four constituent evaluations
  have hΦev : EvaluatesTo W P (Φ_ff W n) ((W.Φ n).eval P.x) := by
    have h := evaluatesTo_algebraMap_mk W P (Polynomial.C (W.Φ n))
    rwa [Polynomial.evalEval_C] at h
  have hΨev : EvaluatesTo W P (ΨSq_ff W n) ((W.ΨSq n).eval P.x) := by
    have h := evaluatesTo_algebraMap_mk W P (Polynomial.C (W.ΨSq n))
    rwa [Polynomial.evalEval_C] at h
  have hωev : EvaluatesTo W P (ω_ff W n) ((W.ω n).evalEval P.x P.y) :=
    evaluatesTo_algebraMap_mk W P (W.ω n)
  have hψev : EvaluatesTo W P (ψ_ff W n) ((W.ψ n).evalEval P.x P.y) :=
    evaluatesTo_algebraMap_mk W P (W.ψ n)
  have hΨne : (W.ΨSq n).eval P.x ≠ 0 := by
    rw [← hψΨ]; exact pow_ne_zero 2 hψ
  -- the two coordinate evaluations
  have hxev : EvaluatesTo W P (mulByInt_x W n)
      ((W.φ n).evalEval P.x P.y / (W.ψ n).evalEval P.x P.y ^ 2) := by
    rw [hφΦ, hψΨ]
    exact hΦev.div hΨev hΨne
  have hyev : EvaluatesTo W P (mulByInt_y W n)
      ((W.ω n).evalEval P.x P.y / (W.ψ n).evalEval P.x P.y ^ 3) :=
    hωev.div (hψev.pow 3) (pow_ne_zero 3 hψ)
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn :=
    dif_neg hn
  refine ⟨_, _, h_ns', ?_, ?_, ?_⟩
  · change n • P.toAffinePoint = _
    rw [Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def]
    exact h_eq
  · rw [hpb, mulByInt_pullbackAlgHom_x_gen W n hn]
    exact hxev
  · rw [hpb, mulByInt_pullbackAlgHom_y_gen W n hn]
    exact hyev

/-! ### The covariance at the Basic level -/

/-- **The `[n]`-pullback covariance for the `PullbackEvaluation` class** (Silverman
III.4.8, function-field shadow), at the Basic level, over `K̄`:
`[n]*(β^* u) = β^*([n]* u)` for every witnessed `β`.

`[n]* ∘ β*` and `β* ∘ [n]*` are the pullbacks of `β ∘ [n]` and `[n] ∘ β`, whose stored
point maps agree everywhere by `map_zsmul`; the composites carry pullback-evaluation
witnesses (`PullbackEvaluation.comp` with the `[n]`-witness), and the separation engine
forces the pullbacks to agree on the infinite `E(F̄)`. -/
theorem mulByInt_pullbackAlgHom_comm_of_pullbackEvaluation [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine) {bad : Set (W_smooth W).SmoothPoint}
    (hbad : bad.Finite) (hw : PullbackEvaluation W β bad) (n : ℤ) (hn : n ≠ 0)
    (u : KE) :
    mulByInt_pullbackAlgHom W n hn (β.pullback u) =
      β.pullback (mulByInt_pullbackAlgHom W n hn u) := by
  classical
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn :=
    dif_neg hn
  have hwn : PullbackEvaluation W (mulByInt W.toAffine n) (mulByIntSingular W n) :=
    pullbackEvaluation_mulByInt W n hn
  have hbadn : (mulByIntSingular W n).Finite := mulByIntSingular_finite W n hn
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI : Infinite (W_smooth W).SmoothPoint := (W_smooth W).smoothPoint_infinite
  have heq : (β.comp (mulByInt W.toAffine n)).pullback =
      ((mulByInt W.toAffine n).comp β).pullback :=
    Isogeny.pullback_eq_of_pointMap_eqOn_infinite
      (PullbackEvaluation.comp_bad_finite hbad hbadn hwn)
      (PullbackEvaluation.comp_bad_finite hbadn hbad hw)
      (hw.comp hwn) (hwn.comp hw) Set.infinite_univ
      (fun P _ ↦ map_zsmul β.toAddMonoidHom n P.toAffinePoint)
  rw [← hpb]
  exact DFunLike.congr_fun heq u

end HasseWeil.WeilPairing

namespace HasseWeil.EC

open Curves HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

/-! ### The main deliverable: the class discharge of `MulByIntPullbackCovariant` -/

/-- **The class discharge of the `[n]`-pullback covariance** (Silverman III.4.8 for the
`PullbackEvaluation` class): an `EC.Isogeny` whose pullback is realised by a coherent
`Basic.Isogeny` `β` (same pullback, `h_pb`) carrying a cofinite pullback-evaluation
witness satisfies `MulByIntPullbackCovariant` for **every** `n ≠ 0`, over `K̄`.

This discharges the one named hypothesis of the canonical-dual machinery
(`CanonicalDual.lean`) for the class; the corollaries below restate the second
composition, the double dual and the composition reversal hypothesis-free. -/
theorem Isogeny.mulByIntPullbackCovariant_of_pullbackEvaluation
    (φE : Isogeny W.toAffine W.toAffine)
    (β : HasseWeil.Isogeny W.toAffine W.toAffine)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) (n : ℤ) (hn : n ≠ 0) :
    φE.MulByIntPullbackCovariant n hn := by
  intro u
  rw [h_pb]
  exact mulByInt_pullbackAlgHom_comm_of_pullbackEvaluation W β hbad hw n hn u

/-! ### Hypothesis-free canonical-dual corollaries for the class

Each statement below is the corresponding `CanonicalDual.lean` theorem with the carried
covariance `hcov` replaced by the coherence package `(β, h_pb, hbad, hw)`. -/

variable (φE : Isogeny W.toAffine W.toAffine)
  (β : HasseWeil.Isogeny W.toAffine W.toAffine)

/-- **`φ ∘ [n] = [n] ∘ φ` in fully bundled form** (Silverman III.4.8) for the
`PullbackEvaluation` class — hypothesis-free instance of
`compose_mulByInt_of_covariant`. -/
theorem Isogeny.compose_mulByInt_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) {n : ℤ} (hn : n ≠ 0) :
    φE.compose (Isogeny.mulByInt W.toAffine hn) =
      (Isogeny.mulByInt W.toAffine hn).compose φE :=
  Isogeny.compose_mulByInt_of_covariant
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)

/-- **The second composition `φ ∘ φ̂ = [n]`** (Silverman III.6.2(a)) for the
`PullbackEvaluation` class — `compose_mulByIntDual` with the covariance discharged. -/
theorem Isogeny.compose_mulByIntDual_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) {n : ℤ} {hn : n ≠ 0}
    (w : φE.HasMulByIntDualWitness n hn) :
    φE.compose (Isogeny.mulByIntDual w) = Isogeny.mulByInt W.toAffine hn :=
  Isogeny.compose_mulByIntDual w
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)

/-- **The dual carries the `[n]`-witness itself** (Silverman III.6.2 bookkeeping) for the
`PullbackEvaluation` class. -/
theorem Isogeny.HasMulByIntDualWitness.dual_of_pullbackEvaluation
    {n : ℤ} {hn : n ≠ 0} (w : φE.HasMulByIntDualWitness n hn)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) :
    (Isogeny.mulByIntDual w).HasMulByIntDualWitness n hn :=
  w.dual (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)

/-- **The double dual `φ̂̂ = φ`** (Silverman III.6.2(e)) for the `PullbackEvaluation`
class — `mulByIntDual_mulByIntDual` with the covariance discharged. -/
theorem Isogeny.mulByIntDual_mulByIntDual_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) {n : ℤ} {hn : n ≠ 0}
    (w : φE.HasMulByIntDualWitness n hn)
    (ŵ : (Isogeny.mulByIntDual w).HasMulByIntDualWitness n hn) :
    Isogeny.mulByIntDual ŵ = φE :=
  Isogeny.mulByIntDual_mulByIntDual w ŵ
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)

/-- **Duals reverse composition `(ψ∘φ)^ = φ̂ ∘ ψ̂`** (Silverman III.6.2(b)) for an inner
`φ` of the `PullbackEvaluation` class. -/
theorem Isogeny.mulByIntDual_compose_reverse_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad)
    {ψ : Isogeny W.toAffine W.toAffine} {n m : ℤ} {hn : n ≠ 0} {hm : m ≠ 0}
    (wψ : ψ.HasMulByIntDualWitness n hn) (wφ : φE.HasMulByIntDualWitness m hm) :
    Isogeny.mulByIntDual (wψ.compose wφ
        (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)) =
      (Isogeny.mulByIntDual wφ).compose (Isogeny.mulByIntDual wψ) :=
  Isogeny.mulByIntDual_compose_reverse wψ wφ
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw n hn)

/-- **The canonical second composition `φ ∘ φ̂ = [deg φ]`** (Silverman III.6.2(a)) for the
`PullbackEvaluation` class. -/
theorem Isogeny.compose_canonicalDual_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) (w : φE.HasCanonicalDualWitness) :
    φE.compose (φE.canonicalDual w) =
      Isogeny.mulByInt W.toAffine φE.intDegree_ne_zero :=
  φE.compose_canonicalDual w
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
      φE.intDegree_ne_zero)

/-- **The canonical dual carries a canonical witness** for the `PullbackEvaluation`
class. -/
theorem Isogeny.canonicalDual_hasCanonicalDualWitness_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) (w : φE.HasCanonicalDualWitness) :
    (φE.canonicalDual w).HasCanonicalDualWitness :=
  φE.canonicalDual_hasCanonicalDualWitness w
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
      φE.intDegree_ne_zero)

/-- **The canonical double dual `φ̂̂ = φ`** (Silverman III.6.2(e)) for the
`PullbackEvaluation` class — every hypothesis of `canonicalDual_canonicalDual` beyond the
witness and the coherence package is discharged. -/
theorem Isogeny.canonicalDual_canonicalDual_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad) (w : φE.HasCanonicalDualWitness) :
    (φE.canonicalDual w).canonicalDual
        (φE.canonicalDual_hasCanonicalDualWitness w
          (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
            φE.intDegree_ne_zero)) = φE :=
  φE.canonicalDual_canonicalDual w
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
      φE.intDegree_ne_zero)

/-- **Canonical duals reverse composition `(ψ∘φ)^ = φ̂ ∘ ψ̂`** (Silverman III.6.2(b),
canonical form) for an inner `φ` of the `PullbackEvaluation` class. -/
theorem Isogeny.canonicalDual_compose_reverse_of_pullbackEvaluation
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : PullbackEvaluation W β bad)
    {ψ : Isogeny W.toAffine W.toAffine}
    (wψ : ψ.HasCanonicalDualWitness) (wφ : φE.HasCanonicalDualWitness) :
    (ψ.compose φE).canonicalDual (wψ.compose wφ
        (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
          ψ.intDegree_ne_zero)) =
      (φE.canonicalDual wφ).compose (ψ.canonicalDual wψ) :=
  Isogeny.canonicalDual_compose_reverse wψ wφ
    (φE.mulByIntPullbackCovariant_of_pullbackEvaluation β h_pb hbad hw _
      ψ.intDegree_ne_zero)

end HasseWeil.EC

namespace HasseWeil.EC

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### The cross-curve covariance of the relative Frobenius (hypothesis-free)

`CanonicalDual.lean` names one further residual: the covariance of
`Frob_{p^e} : E → E^{(p^e)}` against `[p^e]` — "the compatibility of division polynomials
with the coefficient twist".  It is a **theorem**, by pure pullback computation: the
relative Frobenius pullback raises to the `p^e`-th power
(`relativeFrobenius_pullback_coordRingMap`), the division polynomials of the twist are the
coefficient-twists of the originals (`map_Φ`, `map_ΨSq`, `map_ψ`, `map_ω`), and `[n]*` is a
ring homomorphism — so both sides of the covariance compute to `(mulByInt_x E n)^{p^e}` /
`(mulByInt_y E n)^{p^e}` on the generators.  No separation engine, no algebraic closure,
**every** integer `n ≠ 0` at once. -/

section RelativeFrobeniusCovariance

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [ExpChar F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- `Frob_{p^e}^*` of the twisted `Φ_n`-function is the `p^e`-th power of the original. -/
private theorem relativeFrobenius_pullback_Φ_ff (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (Φ_ff (E.iterateFrobeniusTwist p e) n) = Φ_ff E n ^ p ^ e := by
  have hmapΦ : (E.iterateFrobeniusTwist p e).Φ n =
      (E.Φ n).map (iterateFrobenius F p e) :=
    WeierstrassCurve.map_Φ (W := E) (iterateFrobenius F p e) n
  have h1 : Φ_ff (E.iterateFrobeniusTwist p e) n =
      algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
          (algebraMap (Polynomial F) E.toAffine.CoordinateRing (E.Φ n))) := by
    unfold Φ_ff
    congr 1
    rw [show algebraMap (Polynomial F) E.toAffine.CoordinateRing (E.Φ n) =
      WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (Polynomial.C (E.Φ n)) from rfl,
      WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_C]
    exact congrArg
      (algebraMap (Polynomial F) (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing)
      hmapΦ
  rw [h1, relativeFrobenius_pullback_coordRingMap p E e]
  rfl

/-- `Frob_{p^e}^*` of the twisted `ΨSq_n`-function is the `p^e`-th power of the
original. -/
private theorem relativeFrobenius_pullback_ΨSq_ff (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (ΨSq_ff (E.iterateFrobeniusTwist p e) n) = ΨSq_ff E n ^ p ^ e := by
  have hmapΨ : (E.iterateFrobeniusTwist p e).ΨSq n =
      (E.ΨSq n).map (iterateFrobenius F p e) :=
    WeierstrassCurve.map_ΨSq (W := E) (iterateFrobenius F p e) n
  have h1 : ΨSq_ff (E.iterateFrobeniusTwist p e) n =
      algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
          (algebraMap (Polynomial F) E.toAffine.CoordinateRing (E.ΨSq n))) := by
    unfold ΨSq_ff
    congr 1
    rw [show algebraMap (Polynomial F) E.toAffine.CoordinateRing (E.ΨSq n) =
      WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine
        (Polynomial.C (E.ΨSq n)) from rfl,
      WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_C]
    exact congrArg
      (algebraMap (Polynomial F) (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing)
      hmapΨ
  rw [h1, relativeFrobenius_pullback_coordRingMap p E e]
  rfl

/-- `Frob_{p^e}^*` of the twisted `ψ_n`-function is the `p^e`-th power of the original. -/
private theorem relativeFrobenius_pullback_ψ_ff (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (ψ_ff (E.iterateFrobeniusTwist p e) n) = ψ_ff E n ^ p ^ e := by
  have hmapψ : (E.iterateFrobeniusTwist p e).ψ n =
      (E.ψ n).map (Polynomial.mapRingHom (iterateFrobenius F p e)) :=
    WeierstrassCurve.map_ψ (W := E) (iterateFrobenius F p e) n
  have h1 : ψ_ff (E.iterateFrobeniusTwist p e) n =
      algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
          (WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (E.ψ n))) := by
    unfold ψ_ff
    congr 1
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
    exact congrArg
      (WeierstrassCurve.Affine.CoordinateRing.mk
        (E.iterateFrobeniusTwist p e).toAffine) hmapψ
  rw [h1, relativeFrobenius_pullback_coordRingMap p E e]
  rfl

/-- `Frob_{p^e}^*` of the twisted `ω_n`-function is the `p^e`-th power of the original. -/
private theorem relativeFrobenius_pullback_ω_ff (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (ω_ff (E.iterateFrobeniusTwist p e) n) = ω_ff E n ^ p ^ e := by
  have hmapω : (E.iterateFrobeniusTwist p e).ω n =
      (E.ω n).map (Polynomial.mapRingHom (iterateFrobenius F p e)) :=
    WeierstrassCurve.map_ω (W := E) (iterateFrobenius F p e) n
  have h1 : ω_ff (E.iterateFrobeniusTwist p e) n =
      algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
          (WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (E.ω n))) := by
    unfold ω_ff
    congr 1
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk]
    exact congrArg
      (WeierstrassCurve.Affine.CoordinateRing.mk
        (E.iterateFrobeniusTwist p e).toAffine) hmapω
  rw [h1, relativeFrobenius_pullback_coordRingMap p E e]
  rfl

/-- `Frob_{p^e}^*` of the twisted `[n]`-`x`-coordinate is the `p^e`-th power of the original
`[n]`-`x`-coordinate: `Frob*(mulByInt_x E^{(p^e)} n) = (mulByInt_x E n)^{p^e}`.  Unfolding
`mulByInt_x = Φ_ff / ΨSq_ff` and pushing the pullback through the quotient reduces this to
`relativeFrobenius_pullback_Φ_ff` and `relativeFrobenius_pullback_ΨSq_ff`. -/
private theorem relativeFrobenius_pullback_mulByInt_x (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (mulByInt_x (E.iterateFrobeniusTwist p e) n) = mulByInt_x E n ^ p ^ e := by
  have hdiv : (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (Φ_ff (E.iterateFrobeniusTwist p e) n /
        ΨSq_ff (E.iterateFrobeniusTwist p e) n) =
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (Φ_ff (E.iterateFrobeniusTwist p e) n) /
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (ΨSq_ff (E.iterateFrobeniusTwist p e) n) := map_div₀ _ _ _
  rw [show mulByInt_x (E.iterateFrobeniusTwist p e) n =
      Φ_ff (E.iterateFrobeniusTwist p e) n /
        ΨSq_ff (E.iterateFrobeniusTwist p e) n from rfl,
    hdiv, relativeFrobenius_pullback_Φ_ff p E e n,
    relativeFrobenius_pullback_ΨSq_ff p E e n, ← div_pow]
  rfl

/-- `Frob_{p^e}^*` of the twisted `[n]`-`y`-coordinate is the `p^e`-th power of the original
`[n]`-`y`-coordinate: `Frob*(mulByInt_y E^{(p^e)} n) = (mulByInt_y E n)^{p^e}`.  Unfolding
`mulByInt_y = ω_ff / ψ_ff^3` and pushing the pullback through the quotient and the cube
reduces this to `relativeFrobenius_pullback_ω_ff` and `relativeFrobenius_pullback_ψ_ff`. -/
private theorem relativeFrobenius_pullback_mulByInt_y (e : ℕ) (n : ℤ) :
    (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (mulByInt_y (E.iterateFrobeniusTwist p e) n) = mulByInt_y E n ^ p ^ e := by
  have hdiv : (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (ω_ff (E.iterateFrobeniusTwist p e) n /
        ψ_ff (E.iterateFrobeniusTwist p e) n ^ 3) =
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (ω_ff (E.iterateFrobeniusTwist p e) n) /
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (ψ_ff (E.iterateFrobeniusTwist p e) n ^ 3) := map_div₀ _ _ _
  have hpow3 : (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (ψ_ff (E.iterateFrobeniusTwist p e) n ^ 3) =
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (ψ_ff (E.iterateFrobeniusTwist p e) n) ^ 3 := map_pow _ _ _
  rw [show mulByInt_y (E.iterateFrobeniusTwist p e) n =
      ω_ff (E.iterateFrobeniusTwist p e) n /
        ψ_ff (E.iterateFrobeniusTwist p e) n ^ 3 from rfl,
    hdiv, hpow3, relativeFrobenius_pullback_ω_ff p E e n,
    relativeFrobenius_pullback_ψ_ff p E e n, pow_right_comm, ← div_pow]
  rfl

/-- The `x`-generator instance of the relative-Frobenius `[n]`-pullback covariance: both sides
equal `(mulByInt_x E n)^{p^e}` — the left by `Frob* x_gen' = x_gen^{p^e}`, the ring-hom
power law and `mulByInt_pullbackAlgHom_x_gen`; the right by
`relativeFrobenius_pullback_mulByInt_x`. -/
private theorem relativeFrobenius_mulByIntPullbackCovariant_x_gen (e : ℕ) (n : ℤ)
    (hn : n ≠ 0) :
    HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn
        ((Isogeny.relativeFrobenius p E e).toCurveMap.pullback
          (x_gen (E.iterateFrobeniusTwist p e))) =
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (mulByInt_x (E.iterateFrobeniusTwist p e) n) := by
  have h1 : (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (x_gen (E.iterateFrobeniusTwist p e)) = x_gen E ^ p ^ e :=
    relativeFrobenius_pullback_x_gen p E e
  have h2 : HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (x_gen E ^ p ^ e) =
      HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (x_gen E) ^ p ^ e :=
    map_pow _ _ _
  have h3 : HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (x_gen E) =
      mulByInt_x E n := HasseWeil.mulByInt_pullbackAlgHom_x_gen E n hn
  rw [h1, h2, h3, relativeFrobenius_pullback_mulByInt_x]

/-- The `y`-generator instance of the relative-Frobenius `[n]`-pullback covariance: both sides
equal `(mulByInt_y E n)^{p^e}` — the left by `Frob* y_gen' = y_gen^{p^e}`, the ring-hom
power law and `mulByInt_pullbackAlgHom_y_gen`; the right by
`relativeFrobenius_pullback_mulByInt_y`. -/
private theorem relativeFrobenius_mulByIntPullbackCovariant_y_gen (e : ℕ) (n : ℤ)
    (hn : n ≠ 0) :
    HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn
        ((Isogeny.relativeFrobenius p E e).toCurveMap.pullback
          (y_gen (E.iterateFrobeniusTwist p e))) =
      (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
        (mulByInt_y (E.iterateFrobeniusTwist p e) n) := by
  have h1 : (Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (y_gen (E.iterateFrobeniusTwist p e)) = y_gen E ^ p ^ e :=
    relativeFrobenius_pullback_y_gen p E e
  have h2 : HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (y_gen E ^ p ^ e) =
      HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (y_gen E) ^ p ^ e :=
    map_pow _ _ _
  have h3 : HasseWeil.mulByInt_pullbackAlgHom E.toAffine n hn (y_gen E) =
      mulByInt_y E n := HasseWeil.mulByInt_pullbackAlgHom_y_gen E n hn
  rw [h1, h2, h3, relativeFrobenius_pullback_mulByInt_y]

/-- **The relative Frobenius satisfies the `[n]`-pullback covariance** (Silverman III.4.8
for `Frob_{p^e} : E → E^{(p^e)}`, the cross-curve case), unconditionally and for every
`n ≠ 0`: `[n]*_E ∘ Frob* = Frob* ∘ [n]*_{E^{(p^e)}}`.  On the generators both sides are
the `p^e`-th powers of the `[n]`-coordinates of `E` — the left by `Frob* x_gen' = x_gen^{p^e}`
and ring-hom arithmetic, the right by the division-polynomial twist-compatibility
(`relativeFrobenius_pullback_Φ_ff` and friends).  This discharges the covariance input of
the relative-Frobenius double dual named in `CanonicalDual.lean`. -/
theorem Isogeny.relativeFrobenius_mulByIntPullbackCovariant (e : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.relativeFrobenius p E e).MulByIntPullbackCovariant n hn :=
  Isogeny.mulByIntPullbackCovariant_of_x_y_gen _ n hn
    (relativeFrobenius_mulByIntPullbackCovariant_x_gen p E e n hn)
    (relativeFrobenius_mulByIntPullbackCovariant_y_gen p E e n hn)

end RelativeFrobeniusCovariance

/-! ### Payoff: the relative-Frobenius double dual `V̂ = Frob` (Silverman III.6.2(e))

The residual named in `CanonicalDual.lean` ("the relative Frobenius double dual is not
instantiated") is now discharged: the covariance is a theorem, so the second composition,
the dual witness of the relative Verschiebung, and the double dual all follow. -/

section RelativeFrobeniusDoubleDual

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
  [PerfectField F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- **The second composition for the relative Frobenius**: `Frob ∘ V̂ = [p^e]` on the
twist curve `E^{(p^e)}` (Silverman III.6.2(a)); the companion of
`relativeVerschiebungOf_compose_relativeFrobenius`.  Hypothesis-free beyond the
`[p]`-inseparability input: the covariance is a theorem. -/
theorem relativeFrobenius_compose_relativeVerschiebungOf
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (Isogeny.relativeFrobenius p E e).compose (relativeVerschiebungOf p E hinsep e) =
      Isogeny.mulByInt (E.iterateFrobeniusTwist p e).toAffine (intPPow_ne_zero p e) := by
  rw [relativeVerschiebungOf_eq_mulByIntDual p E hinsep e]
  exact Isogeny.compose_mulByIntDual (relativeFrobeniusMulByIntDualWitness p E hinsep e)
    (Isogeny.relativeFrobenius_mulByIntPullbackCovariant p E e _ (intPPow_ne_zero p e))

/-- **The relative Verschiebung carries the `[p^e]`-witness** — the witness through which
its dual is formed. -/
theorem relativeVerschiebungOf_hasMulByIntDualWitness
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (relativeVerschiebungOf p E hinsep e).HasMulByIntDualWitness ((p ^ e : ℕ) : ℤ)
      (intPPow_ne_zero p e) := by
  rw [relativeVerschiebungOf_eq_mulByIntDual p E hinsep e]
  exact (relativeFrobeniusMulByIntDualWitness p E hinsep e).dual
    (Isogeny.relativeFrobenius_mulByIntPullbackCovariant p E e _ (intPPow_ne_zero p e))

/-- **The relative-Frobenius double dual** `V̂_{p^e}^ = Frob_{p^e}` (Silverman III.6.2(e)
for the relative Frobenius) — the dual of the relative Verschiebung is the relative
Frobenius.  The residual instantiation named in `CanonicalDual.lean`, now hypothesis-free
beyond the `[p]`-inseparability input. -/
theorem relativeVerschiebungOf_dual_eq_relativeFrobenius
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    Isogeny.mulByIntDual (relativeVerschiebungOf_hasMulByIntDualWitness p E hinsep e) =
      Isogeny.relativeFrobenius p E e :=
  Isogeny.mulByIntDual_mulByIntDual (relativeFrobeniusMulByIntDualWitness p E hinsep e)
    (relativeVerschiebungOf_hasMulByIntDualWitness p E hinsep e)
    (Isogeny.relativeFrobenius_mulByIntPullbackCovariant p E e _ (intPPow_ne_zero p e))

/-- **`Frob ∘ V̂ = [p^e]` over a finite base** (axiom-clean instantiation). -/
theorem relativeFrobenius_compose_relativeVerschiebungFinite [Fintype F] (e : ℕ) :
    (Isogeny.relativeFrobenius p E e).compose (relativeVerschiebungFinite p E e) =
      Isogeny.mulByInt (E.iterateFrobeniusTwist p e).toAffine (intPPow_ne_zero p e) :=
  relativeFrobenius_compose_relativeVerschiebungOf p E
    (Isogeny.mulByInt_p_not_isSeparable_finite p E) e

-- `[Fintype F]` is genuinely required: the statement names the finite-base witness
-- `mulByInt_p_not_isSeparable_finite` (which carries it), but the witness sits in a
-- proof-irrelevant position, so the linter cannot see the dependence.
set_option linter.unusedFintypeInType false in
/-- **The relative-Frobenius double dual over a finite base** (axiom-clean
instantiation): `V̂^ = Frob` for the finite-base Verschiebung. -/
theorem relativeVerschiebungFinite_dual_eq_relativeFrobenius [Fintype F] (e : ℕ) :
    Isogeny.mulByIntDual (relativeVerschiebungOf_hasMulByIntDualWitness p E
        (Isogeny.mulByInt_p_not_isSeparable_finite p E) e) =
      Isogeny.relativeFrobenius p E e :=
  relativeVerschiebungOf_dual_eq_relativeFrobenius p E
    (Isogeny.mulByInt_p_not_isSeparable_finite p E) e

end RelativeFrobeniusDoubleDual

end HasseWeil.EC
