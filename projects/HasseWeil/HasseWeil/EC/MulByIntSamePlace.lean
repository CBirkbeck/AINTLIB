/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyOrdTransport
import HasseWeil.EC.MulByIntUnramified
import HasseWeil.EC.TranslateOrdInfty
import HasseWeil.WeilPairing.TorsionGeometric
import HasseWeil.WeilPairing.TorsionKernelRational

/-!
# The **(SamePlace)** fact for the multiplication isogeny `[ℓ]`

This file supplies the **`Valuation.IsEquiv`** ("same place / same valuation ring") input that the
axiom-clean glue `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`
(`HasseWeil/EC/IsogenyOrdTransport.lean`) consumes to upgrade to the value-precise order-transport
`ord_P (φ.pullback g) = ord_{φ(P)} g`.

For the isogeny `φ = [ℓ] = mulByInt W ℓ` and a smooth point `P` of `⟨W⟩` whose image
`Q = [ℓ]·P = (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint` is either an *affine* point or `O`, the
comap valuation `(pointValuation P).comap (mulByInt W ℓ).pullback.toRingHom` is `Valuation.IsEquiv`
to the place-valuation at `Q`:

* **affine image** `Q = some x y h_ns`: equivalent to `pointValuation ⟨x, y, h_ns⟩`;
* **infinity image** `Q = O`: equivalent to `ordAtInftyValuation`.

## Mathematical content (Silverman II.2.5 / III.4.10c)

`Valuation.IsEquiv v w` is, by `Valuation.isEquiv_of_val_le_one`, the statement
`∀ g, v g ≤ 1 ↔ w g ≤ 1`: the two valuations have the same valuation ring. Here this reads
```
[ℓ].pullback g  is regular at P   ⟺   g is regular at Q,
```
the **same-place** content of the morphism `[ℓ] : E → E` with `[ℓ](P) = Q`. The forward direction
(`g` regular at `Q` ⟹ `[ℓ]^*g` regular at `P`) is functoriality of a morphism (it pulls back
regular functions to regular functions, because `[ℓ]` maps `P ↦ Q`); the converse holds because
`[ℓ]` is dominant / a local homomorphism of the discrete valuation rings `O_Q → O_P` with positive
ramification index `e_P ≥ 1`. Crucially, **`IsEquiv` only needs `e_P ≥ 1` (ramification
positivity)** — the sharper `e_P = 1` (separability) is supplied *separately*, as the `ord = 1`
input to `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`.

## Status

The **affine-image** case (`mulByInt_samePlace_le_one_iff_affine`) is proven **sorry-free and
axiom-clean** (`[propext, Classical.choice, Quot.sound]`): its residue matching is supplied by the
affine specialisation `[ℓ]·P = (φ_ℓ(P)/ψ_ℓ(P)², ω_ℓ(P)/ψ_ℓ(P)³)` of the division-polynomial group
law (`zsmul_affine_point_eq_gen`), lifted to all of `K(E)` by the `IsLocalization`/DVR machinery.

The **infinity-image** case (`mulByInt_samePlace_le_one_iff_infty`) is the single residual `sorry`:
it is the *torsion-pole* transfer `ord_P (mulByInt_x ℓ) = -2`, `ord_P (mulByInt_y ℓ) = -3` (the
simple zeros of `ψ_ℓ` at the `ℓ`-torsion points), the same deep geometric kernel isolated as
`ord_P_mulByInt_pullback_eq_infty` in `HasseWeil/WeilPairing/DivisorPullback.lean`.

The `IsEquiv` packaging (`isEquiv_of_val_le_one`) and the `comap`-valuation forms are sorry-free
over these two residuals.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.5–2.6, III.4.10c.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

local notation "KE" => W.FunctionField

/-- For `P` with affine image `[ℓ]·P = some x y h_ns` (`ℓ ≠ 0`), the `ℓ`-th division polynomial
`ψ_ℓ` does not vanish at `(P.x, P.y)`, and the Jacobian division-polynomial coordinates of `[ℓ]·P`
agree with `(x, y)`: `x = φ_ℓ(P.x,P.y)/ψ_ℓ(P.x,P.y)²` and `y = ω_ℓ(P.x,P.y)/ψ_ℓ(P.x,P.y)³`. -/
private theorem mulByInt_coords_at_affine (ℓ : ℤ) (_hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (W.ψ ℓ).evalEval P.x P.y ≠ 0 ∧
      x = (W.φ ℓ).evalEval P.x P.y / (W.ψ ℓ).evalEval P.x P.y ^ 2 ∧
      y = (W.ω ℓ).evalEval P.x P.y / (W.ψ ℓ).evalEval P.x P.y ^ 3 := by
  -- `P.toAffinePoint = some P.x P.y P.nonsingular` and `[ℓ]·P = ℓ • P.toAffinePoint`.
  have hPns : W.Nonsingular P.x P.y := P.nonsingular
  rw [mulByInt_apply, SmoothPlaneCurve.SmoothPoint.toAffinePoint_def] at hQ
  -- `ψ_ℓ(P) ≠ 0`: else `ℓ • P` is at infinity, contradicting `hQ`.
  have hψ : (W.ψ ℓ).evalEval P.x P.y ≠ 0 := by
    intro hψ0
    -- The Jacobian `Z`-coordinate of `ℓ • fromAffine P` is `ψ_ℓ(P) = 0`, so its `toAffineLift`
    -- (which is `ℓ • some P.x P.y`) is the zero point — contradicting `hQ`.
    have hZ : smulEval W P.x P.y ℓ 2 = 0 := hψ0
    have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := W) hPns ℓ
    have h_toAffine :
        ℓ • Affine.Point.some P.x P.y hPns =
        WeierstrassCurve.Jacobian.Point.toAffineLift
          (ℓ • WeierstrassCurve.Jacobian.Point.fromAffine
            (Affine.Point.some P.x P.y hPns)) := by
      have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W)
        ℓ (WeierstrassCurve.Jacobian.Point.fromAffine (Affine.Point.some P.x P.y hPns))
      rw [WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply] at h
      rw [show WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W
        (WeierstrassCurve.Jacobian.Point.fromAffine _) =
        WeierstrassCurve.Jacobian.Point.toAffineLift
          (WeierstrassCurve.Jacobian.Point.fromAffine _) from rfl] at h
      have h2 : WeierstrassCurve.Jacobian.Point.toAffineLift
          (WeierstrassCurve.Jacobian.Point.fromAffine
            (Affine.Point.some P.x P.y hPns)) =
          Affine.Point.some P.x P.y hPns := by
        rw [← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
        exact (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv W).right_inv _
      rw [h2] at h
      exact h.symm
    have h_lift_zero :
        WeierstrassCurve.Jacobian.Point.toAffineLift
          (ℓ • WeierstrassCurve.Jacobian.Point.fromAffine
            (Affine.Point.some P.x P.y hPns)) = 0 := by
      unfold WeierstrassCurve.Jacobian.Point.toAffineLift
      rw [h_smulEval]
      exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero hZ
    rw [h_lift_zero] at h_toAffine
    exact Affine.Point.some_ne_zero h_ns (hQ.symm.trans h_toAffine)
  obtain ⟨h', heq⟩ := zsmul_affine_point_eq_gen W ℓ hPns hψ
  rw [hQ] at heq
  rw [Affine.Point.some.injEq] at heq
  exact ⟨hψ, heq.1, heq.2⟩

/-- **Univariate value bridge (abstract)**: if `u ∈ K(E)` is regular at `P` and `u ≡ a` modulo
`m_P` (i.e. `pointValuation P (u − a) < 1`), then for any `q : F[X]`,
`q(u) ≡ q(a)` modulo `m_P`. Polynomial induction on `q` via the strong triangle inequality. -/
private theorem pointValuation_aeval_sub_eval_lt_one
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {u : KE} {a : F}
    (hu_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P u ≤ 1)
    (hu : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (u - algebraMap F KE a) < 1)
    (q : Polynomial F) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (Polynomial.aeval u q - algebraMap F KE (q.eval a)) < 1 := by
  induction q using Polynomial.induction_on with
  | C c =>
    simpa only [Polynomial.aeval_C, Polynomial.eval_C, sub_self, map_zero] using zero_lt_one
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, map_add,
      show Polynomial.aeval u p + Polynomial.aeval u q -
          (algebraMap F KE (p.eval a) + algebraMap F KE (q.eval a)) =
        (Polynomial.aeval u p - algebraMap F KE (p.eval a)) +
          (Polynomial.aeval u q - algebraMap F KE (q.eval a)) from by ring]
    exact lt_of_le_of_lt (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt hp hq)
  | monomial n c ih =>
    -- `c·u^(n+1) − c·a^(n+1) = u·(c·u^n − c·a^n) + c·a^n·(u − a)`.
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    rw [show algebraMap F KE c * u ^ (n + 1) - algebraMap F KE (c * a ^ (n + 1)) =
          u * (algebraMap F KE c * u ^ n - algebraMap F KE (c * a ^ n)) +
            algebraMap F KE (c * a ^ n) * (u - algebraMap F KE a) from by
        push_cast [map_mul, map_pow]; ring]
    have ih' : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap F KE c * u ^ n - algebraMap F KE (c * a ^ n)) < 1 := by
      rwa [show algebraMap F KE c * u ^ n =
          Polynomial.aeval u (Polynomial.C c * Polynomial.X ^ n) from by
        rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X],
        show c * a ^ n = (Polynomial.C c * Polynomial.X ^ n).eval a from by
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]]
    refine lt_of_le_of_lt (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _) (max_lt ?_ ?_)
    · exact pointValuation_mul_lt_one_of_le_and_lt W P hu_le ih'
    · exact pointValuation_mul_lt_one_of_le_and_lt W P
        ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _) hu

/-- **Coordinate-ring residue bridge**: a coordinate-ring element `r` is congruent, modulo `m_P`,
to its value `evalAt P r` at `P` — i.e. `pointValuation P (algMap r − evalAt P r) < 1`.
Direct from `ker (evalAt P) = m_P`. -/
private theorem pointValuation_algebraMap_sub_evalAt_lt_one
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (r : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r -
          algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt P r)) < 1 := by
  -- `r − algMap_F (evalAt r)` lies in the maximal ideal at `P` (it is in `ker (evalAt P)`).
  have hmem : r - algebraMap F (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing
      ((⟨W⟩ : SmoothPlaneCurve F).evalAt P r) ∈ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := by
    rw [← (⟨W⟩ : SmoothPlaneCurve F).ker_evalAt P, RingHom.mem_ker, map_sub,
      (⟨W⟩ : SmoothPlaneCurve F).evalAt_algebraMap P, sub_self]
  have hlt := (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨W⟩ : SmoothPlaneCurve F))
    (r - algebraMap F (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing
      ((⟨W⟩ : SmoothPlaneCurve F).evalAt P r)) P).mpr hmem
  rwa [map_sub, ← IsScalarTower.algebraMap_apply F (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W⟩ : SmoothPlaneCurve F).FunctionField] at hlt

/-- `algebraMap (Polynomial F) K(E)` is evaluation of the polynomial at `x_gen`. -/
private theorem algebraMap_polynomial_eq_aeval_x_gen (p : Polynomial F) :
    algebraMap (Polynomial F) KE p = Polynomial.aeval (x_gen W) p := by
  rw [show x_gen W = algebraMap (Polynomial F) KE Polynomial.X from
      (IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing KE
        Polynomial.X).symm,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

/-- `Φ_ff W ℓ = (W.Φ ℓ)(x_gen)`. -/
private theorem Φ_ff_eq_aeval (ℓ : ℤ) :
    Φ_ff W ℓ = Polynomial.aeval (x_gen W) (W.Φ ℓ) := by
  rw [← algebraMap_polynomial_eq_aeval_x_gen, Φ_ff,
    IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing KE]

/-- `ΨSq_ff W ℓ = (W.ΨSq ℓ)(x_gen)`. -/
private theorem ΨSq_ff_eq_aeval (ℓ : ℤ) :
    ΨSq_ff W ℓ = Polynomial.aeval (x_gen W) (W.ΨSq ℓ) := by
  rw [← algebraMap_polynomial_eq_aeval_x_gen, ΨSq_ff,
    IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing KE]

/-- **The `x`-coordinate value bridge**: for affine image `[ℓ]·P = some x y h_ns`,
`mulByInt_x ℓ ≡ x` modulo `m_P`, i.e. `pointValuation P (mulByInt_x ℓ − x) < 1`. -/
private theorem pointValuation_mulByInt_x_sub_lt_one [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_x W ℓ - algebraMap F KE x) < 1 := by
  obtain ⟨hψ, hx, _⟩ := mulByInt_coords_at_affine (W := W) ℓ hℓ P h_ns hQ
  have heqn : W.toAffine.Equation P.x P.y := Affine.equation_iff_nonsingular.mpr P.nonsingular
  -- `ΨSq_ℓ(P.x) = ψ_ℓ(P)² ≠ 0` and `Φ_ℓ(P.x) = φ_ℓ(P)`, so `x = Φ_ℓ(P.x)/ΨSq_ℓ(P.x)`.
  have hΨSq : (W.ΨSq ℓ).eval P.x = (W.ψ ℓ).evalEval P.x P.y ^ 2 :=
    (WeierstrassCurve.evalEval_ψ_sq W heqn ℓ).symm
  have hΦ : (W.Φ ℓ).eval P.x = (W.φ ℓ).evalEval P.x P.y :=
    (WeierstrassCurve.evalEval_φ_eq_Φ W heqn ℓ).symm
  have hΨSq_ne : (W.ΨSq ℓ).eval P.x ≠ 0 := by rw [hΨSq]; exact pow_ne_zero 2 hψ
  have hx_eq : (W.Φ ℓ).eval P.x - x * (W.ΨSq ℓ).eval P.x = 0 := by
    rw [hΦ, hΨSq, hx, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), sub_self]
  -- `ΨSq_ff` is a unit at `P` (its residue `ΨSq_ℓ(P.x) ≠ 0`).
  have hΨSq_ff_ne : ΨSq_ff W ℓ ≠ 0 := ΨSq_ff_ne_zero W hℓ
  have hΨSq_unit : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (ΨSq_ff W ℓ) = 1 := by
    have hbridge : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (ΨSq_ff W ℓ - algebraMap F KE ((W.ΨSq ℓ).eval P.x)) < 1 := by
      rw [ΨSq_ff_eq_aeval]
      exact pointValuation_aeval_sub_eval_lt_one P (pointValuation_x_gen_le_one W P)
        (by rw [x_gen_sub_const_eq_algebraMap_XClass W P.x]
            exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
              (C := (⟨W⟩ : SmoothPlaneCurve F)) _ P).mpr (XClass_mem_maximalIdealAt W P P.x rfl))
        (W.ΨSq ℓ)
    -- residue of `ΨSq_ff` is the nonzero constant `ΨSq_ℓ(P.x)`, so `pointValuation = 1`.
    have hconst : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap F KE ((W.ΨSq ℓ).eval P.x)) = 1 :=
      pointValuation_algebraMap_F_eq_one_of_ne_zero W P hΨSq_ne
    have hsplit : ΨSq_ff W ℓ = (ΨSq_ff W ℓ - algebraMap F KE ((W.ΨSq ℓ).eval P.x)) +
        algebraMap F KE ((W.ΨSq ℓ).eval P.x) := by ring
    rw [hsplit, ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]; exact hbridge), hconst]
  -- `mulByInt_x ℓ − x = (Φ_ff − x·ΨSq_ff)/ΨSq_ff`; numerator `≡ 0`, denominator a unit.
  have hnum : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (Φ_ff W ℓ - algebraMap F KE x * ΨSq_ff W ℓ) < 1 := by
    rw [Φ_ff_eq_aeval, ΨSq_ff_eq_aeval,
      show Polynomial.aeval (x_gen W) (W.Φ ℓ) -
            algebraMap F KE x * Polynomial.aeval (x_gen W) (W.ΨSq ℓ) =
          Polynomial.aeval (x_gen W) (W.Φ ℓ - Polynomial.C x * W.ΨSq ℓ) -
            algebraMap F KE ((W.Φ ℓ - Polynomial.C x * W.ΨSq ℓ).eval P.x) from by
        rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, hx_eq, map_zero]; ring]
    exact pointValuation_aeval_sub_eval_lt_one P (pointValuation_x_gen_le_one W P)
      (by rw [x_gen_sub_const_eq_algebraMap_XClass W P.x]
          exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
            (C := (⟨W⟩ : SmoothPlaneCurve F)) _ P).mpr (XClass_mem_maximalIdealAt W P P.x rfl)) _
  -- Assemble: `mulByInt_x ℓ − x = (Φ_ff − x·ΨSq_ff) · ΨSq_ff⁻¹`.
  have hmx : mulByInt_x W ℓ - algebraMap F KE x =
      (Φ_ff W ℓ - algebraMap F KE x * ΨSq_ff W ℓ) * (ΨSq_ff W ℓ)⁻¹ := by
    rw [mulByInt_x, sub_mul, div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hΨSq_ff_ne, mul_one]
  rwa [hmx, map_mul, map_inv₀, hΨSq_unit, inv_one, mul_one]

/-- The `y`-coordinate numerator `ω_ff − y·ψ_ff³` vanishes modulo `m_P`, from the generator
residues `ω_ff ≡ ω_ℓ(P)`, `ψ_ff ≡ ψ_ℓ(P)` and the image coordinate relation `ω_ℓ(P) = y·ψ_ℓ(P)³`:
cube the `ψ`-residue (`q = X³` in the univariate bridge), then `ω_ff − y·ψ_ff³ =
(ω_ff − ω_ℓ(P)) − y·(ψ_ff³ − ψ_ℓ(P)³)` is a sum of two strict-`< 1` terms. -/
private theorem pointValuation_omega_sub_y_psiCubed_lt_one_aux [IsAlgClosed F] (ℓ : ℤ) {y : F}
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hωmem : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (ω_ff W ℓ - algebraMap F KE ((W.ω ℓ).evalEval P.x P.y)) < 1)
    (hψmem : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (ψ_ff W ℓ - algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) < 1)
    (hcoord : (W.ω ℓ).evalEval P.x P.y = y * (W.ψ ℓ).evalEval P.x P.y ^ 3) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (ω_ff W ℓ - algebraMap F KE y * ψ_ff W ℓ ^ 3) < 1 := by
  have hψ3 : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (ψ_ff W ℓ ^ 3 -
      (algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) ^ 3) < 1 := by
    have hreg : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (ψ_ff W ℓ) ≤ 1 := by
      rw [show ψ_ff W ℓ = (ψ_ff W ℓ - algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) +
          algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y) from by ring]
      exact pointValuation_add_le_one W P (le_of_lt hψmem)
        ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)
    have h := pointValuation_aeval_sub_eval_lt_one P hreg hψmem (Polynomial.X ^ 3)
    simpa only [map_pow, Polynomial.aeval_X, Polynomial.eval_pow, Polynomial.eval_X] using h
  rw [show ω_ff W ℓ - algebraMap F KE y * ψ_ff W ℓ ^ 3 =
      (ω_ff W ℓ - algebraMap F KE ((W.ω ℓ).evalEval P.x P.y)) -
        algebraMap F KE y *
          (ψ_ff W ℓ ^ 3 - (algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) ^ 3) from by
    rw [show algebraMap F KE ((W.ω ℓ).evalEval P.x P.y) =
        algebraMap F KE y * (algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) ^ 3 from by
      rw [hcoord, map_mul, map_pow]]
    ring]
  refine lt_of_le_of_lt (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_sub _ _)
    (max_lt hωmem ?_)
  exact pointValuation_mul_lt_one_of_le_and_lt W P
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P y) hψ3

/-- **The `y`-coordinate value bridge**: for affine image `[ℓ]·P = some x y h_ns`,
`mulByInt_y ℓ ≡ y` modulo `m_P`, i.e. `pointValuation P (mulByInt_y ℓ − y) < 1`. -/
private theorem pointValuation_mulByInt_y_sub_lt_one [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_y W ℓ - algebraMap F KE y) < 1 := by
  obtain ⟨hψ, _, hy⟩ := mulByInt_coords_at_affine (W := W) ℓ hℓ P h_ns hQ
  -- residues: `ω_ff ≡ ω_ℓ(P)`, `ψ_ff ≡ ψ_ℓ(P)` mod `m_P`; `ψ_ℓ(P) ≠ 0`.
  have hωmem : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (ω_ff W ℓ - algebraMap F KE ((W.ω ℓ).evalEval P.x P.y)) < 1 := by
    have h := pointValuation_algebraMap_sub_evalAt_lt_one P
      (Affine.CoordinateRing.mk W.toAffine (W.ω ℓ))
    rwa [Curves.SmoothPlaneCurve.evalAt_mk] at h
  have hψmem : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (ψ_ff W ℓ - algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) < 1 := by
    have h := pointValuation_algebraMap_sub_evalAt_lt_one P
      (Affine.CoordinateRing.mk W.toAffine (W.ψ ℓ))
    rwa [Curves.SmoothPlaneCurve.evalAt_mk] at h
  -- `ψ_ff` is a unit at `P` since its residue `ψ_ℓ(P) ≠ 0`.
  have hψ_ff_ne : ψ_ff W ℓ ≠ 0 := ψ_ff_ne_zero W hℓ
  have hψconst : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hψ
  have hψ_unit : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (ψ_ff W ℓ) = 1 := by
    have hsplit : ψ_ff W ℓ = (ψ_ff W ℓ - algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y)) +
        algebraMap F KE ((W.ψ ℓ).evalEval P.x P.y) := by ring
    rw [hsplit, ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hψconst]; exact hψmem), hψconst]
  -- `mulByInt_y ℓ − y = (ω_ff − y·ψ_ff³)/ψ_ff³`; numerator `≡ 0` (via the aux), denominator a unit.
  have hcoord : (W.ω ℓ).evalEval P.x P.y = y * (W.ψ ℓ).evalEval P.x P.y ^ 3 := by
    rw [hy, div_mul_cancel₀ _ (pow_ne_zero 3 hψ)]
  have hnum := pointValuation_omega_sub_y_psiCubed_lt_one_aux (W := W) ℓ P hωmem hψmem hcoord
  -- Assemble: `mulByInt_y ℓ − y = (ω_ff − y·ψ_ff³) · (ψ_ff³)⁻¹`.
  have hψ3_unit : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (ψ_ff W ℓ ^ 3) = 1 := by
    rw [map_pow, hψ_unit, one_pow]
  have hmy : mulByInt_y W ℓ - algebraMap F KE y =
      (ω_ff W ℓ - algebraMap F KE y * ψ_ff W ℓ ^ 3) * (ψ_ff W ℓ ^ 3)⁻¹ := by
    rw [mulByInt_y, sub_mul, div_eq_mul_inv, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 3 hψ_ff_ne), mul_one]
  rwa [hmy, map_mul, map_inv₀, hψ3_unit, inv_one, mul_one]

/-- **Bivariate value bridge**: if `u ≡ a` and `v ≡ b` modulo `m_P` (both `u, v` regular at `P`),
then `p(u, v) ≡ p(a, b)` modulo `m_P` for any bivariate `p : F[X][X]` (the coefficients pushed
through `algebraMap F K(E)`). Polynomial induction reducing to the two univariate bridges. -/
private theorem pointValuation_bivariate_bridge
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {u v : KE} {a b : F}
    (hu_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P u ≤ 1)
    (hu : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (u - algebraMap F KE a) < 1)
    (_hv_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P v ≤ 1)
    (hv : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (v - algebraMap F KE b) < 1)
    (p : Polynomial (Polynomial F)) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        ((p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
          algebraMap F KE (p.evalEval a b)) < 1 := by
  induction p using Polynomial.induction_on with
  | C q =>
    -- `evalEval u v (C q) = q(u)`; `(C q).evalEval a b = q.eval a`; univariate bridge in `u`.
    rw [Polynomial.map_C, Polynomial.evalEval_C, Polynomial.evalEval_C,
      show (Polynomial.mapRingHom (algebraMap F KE)) q = q.map (algebraMap F KE) from rfl,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact pointValuation_aeval_sub_eval_lt_one P hu_le hu q
  | add p₁ p₂ h₁ h₂ =>
    rw [Polynomial.map_add, Polynomial.evalEval_add, Polynomial.evalEval_add, map_add,
      show (p₁.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v +
            (p₂.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
            (algebraMap F KE (p₁.evalEval a b) + algebraMap F KE (p₂.evalEval a b)) =
          ((p₁.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
              algebraMap F KE (p₁.evalEval a b)) +
            ((p₂.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
              algebraMap F KE (p₂.evalEval a b)) from by ring]
    exact lt_of_le_of_lt (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt h₁ h₂)
  | monomial n q ih =>
    -- abbreviations for the degree-`n` evaluations.
    set Au : KE := (((Polynomial.C q) * Polynomial.X ^ n).map
      (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v with hAu
    set Ab : F := ((Polynomial.C q) * Polynomial.X ^ n).evalEval a b with hAb
    -- `(C q · X^(n+1))(u,v) = Au · v` and `(C q · X^(n+1))(a,b) = Ab · b`.
    have heval_u : (((Polynomial.C q) * Polynomial.X ^ (n + 1)).map
        (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v = Au * v := by
      rw [hAu, show (Polynomial.C q) * Polynomial.X ^ (n + 1) =
          ((Polynomial.C q) * Polynomial.X ^ n) * Polynomial.X from by ring,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.evalEval_mul, Polynomial.evalEval_X]
    have heval_ab : ((Polynomial.C q) * Polynomial.X ^ (n + 1)).evalEval a b = Ab * b := by
      rw [hAb, show (Polynomial.C q) * Polynomial.X ^ (n + 1) =
          ((Polynomial.C q) * Polynomial.X ^ n) * Polynomial.X from by ring,
        Polynomial.evalEval_mul, Polynomial.evalEval_X]
    have hAu_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P Au ≤ 1 := by
      have hAu_split : Au = (Au - algebraMap F KE Ab) + algebraMap F KE Ab := by ring
      rw [hAu_split]
      exact pointValuation_add_le_one W P (le_of_lt ih)
        ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)
    rw [heval_u, heval_ab,
      show Au * v - algebraMap F KE (Ab * b) =
          Au * (v - algebraMap F KE b) + algebraMap F KE b * (Au - algebraMap F KE Ab) from by
        push_cast [map_mul]; ring]
    refine lt_of_le_of_lt (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _) (max_lt ?_ ?_)
    · exact pointValuation_mul_lt_one_of_le_and_lt W P hAu_le hv
    · exact pointValuation_mul_lt_one_of_le_and_lt W P
        ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _) ih

/-- `[ℓ].pullback (algebraMap (mk p)) = p(mulByInt_x ℓ, mulByInt_y ℓ)` (coefficients pushed through
`algebraMap F K(E)`). The coordinate-ring comorphism of `[ℓ]` substitutes the division coordinate
functions for `(x_gen, y_gen)`. -/
private theorem mulByInt_pullback_algebraMap_mk_eq (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (p : Polynomial (Polynomial F)) :
    (mulByInt W ℓ).pullback
        (algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.mk W.toAffine p)) =
      (p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval
        (mulByInt_x W ℓ) (mulByInt_y W ℓ) := by
  rw [show (mulByInt W ℓ).pullback
        (algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.mk W.toAffine p)) =
      mulByInt_coordHom W ℓ hℓ (Affine.CoordinateRing.mk W.toAffine p) from by
    have h_pullback : (mulByInt W ℓ).pullback = mulByInt_pullbackAlgHom W ℓ hℓ := by
      unfold mulByInt; simp [hℓ]
    rw [h_pullback]; exact IsLocalization.lift_eq _ _]
  change AdjoinRoot.lift (mulByInt_xHom W ℓ) (mulByInt_y W ℓ) (mulByInt_weierstrass W ℓ hℓ) _ = _
  rw [AdjoinRoot.lift_mk]
  change p.eval₂ (Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W ℓ)) (mulByInt_y W ℓ) = _
  rw [Polynomial.eval₂_eval₂RingHom_apply]

/-- `mulByInt_x ℓ` is regular at `P` (affine image), from the `x`-coordinate value bridge. -/
private theorem pointValuation_mulByInt_x_le_one [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_x W ℓ) ≤ 1 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  rw [show mulByInt_x W ℓ = (mulByInt_x W ℓ - algebraMap F KE x) + algebraMap F KE x from by ring]
  exact pointValuation_add_le_one W P
    (le_of_lt (pointValuation_mulByInt_x_sub_lt_one ℓ hℓ0 P h_ns hQ))
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P x)

/-- `mulByInt_y ℓ` is regular at `P` (affine image), from the `y`-coordinate value bridge. -/
private theorem pointValuation_mulByInt_y_le_one [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_y W ℓ) ≤ 1 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  rw [show mulByInt_y W ℓ = (mulByInt_y W ℓ - algebraMap F KE y) + algebraMap F KE y from by ring]
  exact pointValuation_add_le_one W P
    (le_of_lt (pointValuation_mulByInt_y_sub_lt_one ℓ hℓ0 P h_ns hQ))
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P y)

/-- **Residue matching for coordinate-ring elements (affine image).** For affine image
`[ℓ]·P = some x y h_ns` and `r` a coordinate-ring element, `[ℓ]^*(algebraMap r) ≡ r(Q)` modulo
`m_P`, where `Q = ⟨x, y, h_ns⟩` and `r(Q) = evalAt Q r`. Built from the bivariate value bridge with
the two generator bridges. -/
private theorem pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    (r : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        ((mulByInt W ℓ).pullback
            (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) < 1 := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [mulByInt_pullback_algebraMap_mk_eq ℓ hℓ0 p,
    show (⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ (Affine.CoordinateRing.mk W.toAffine p) =
        p.evalEval x y from Curves.SmoothPlaneCurve.evalAt_mk _ _ _]
  exact pointValuation_bivariate_bridge P
    (pointValuation_mulByInt_x_le_one ℓ hℓ P h_ns hQ)
    (pointValuation_mulByInt_x_sub_lt_one ℓ hℓ0 P h_ns hQ)
    (pointValuation_mulByInt_y_le_one ℓ hℓ P h_ns hQ)
    (pointValuation_mulByInt_y_sub_lt_one ℓ hℓ0 P h_ns hQ) p

/-- **(A) Regularity:** `[ℓ]^*(algebraMap r)` is regular at `P` (affine image). -/
private theorem pointValuation_mulByInt_pullback_algebraMap_le_one [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    (r : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        ((mulByInt W ℓ).pullback
          (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) ≤ 1 := by
  rw [show (mulByInt W ℓ).pullback
        (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      ((mulByInt W ℓ).pullback
            (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring]
  exact pointValuation_add_le_one W P
    (le_of_lt (pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one ℓ hℓ P h_ns hQ r))
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)

/-- **(B′) Unit transfer:** for `r ∉ m_Q`, `[ℓ]^*(algebraMap r)` is a unit at `P`. -/
private theorem pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    {r : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∉ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        ((mulByInt W ℓ).pullback
          (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) = 1 := by
  have hrQ : (⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r ≠ 0 := fun h0 ↦
    hr (by rw [← (⟨W⟩ : SmoothPlaneCurve F).ker_evalAt ⟨x, y, h_ns⟩]; exact h0)
  have hconst : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hrQ
  rw [show (mulByInt W ℓ).pullback
        (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      ((mulByInt W ℓ).pullback
            (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring,
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]
          exact pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one ℓ hℓ P h_ns hQ r),
    hconst]

/-- **(B) Vanishing transfer:** for `r ∈ m_Q`, `[ℓ]^*(algebraMap r)` lies in `m_P` (strict). -/
private theorem pointValuation_mulByInt_pullback_algebraMap_lt_one_of_mem [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    {r : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∈ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P
        ((mulByInt W ℓ).pullback
          (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) < 1 := by
  have hrQ : (⟨W⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r = 0 := by
    rw [← RingHom.mem_ker, (⟨W⟩ : SmoothPlaneCurve F).ker_evalAt]; exact hr
  have h := pointValuation_mulByInt_pullback_algebraMap_sub_evalAt_lt_one ℓ hℓ P h_ns hQ r
  rwa [hrQ, map_zero, sub_zero] at h

/-- **Forward regularity transfer (≤ 1):** if `g` is regular at the affine image `Q`, so is
`[ℓ]^*g` at `P`. -/
private theorem pointValuation_mulByInt_pullback_le_one_of_le_one [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    {g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) ≤ 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr hg
  haveI : ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  have hg_eq : g = algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem ℓ hℓ P h_ns hQ hv_notMem,
    div_one]
  exact pointValuation_mulByInt_pullback_algebraMap_le_one ℓ hℓ P h_ns hQ u

/-- **Forward vanishing transfer (< 1):** if `g ∈ m_Q`, then `[ℓ]^*g ∈ m_P` (strict). -/
private theorem pointValuation_mulByInt_pullback_lt_one_of_lt_one [IsAlgClosed F]
    (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    {g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g < 1) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) < 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr (le_of_lt hg)
  haveI : ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  -- `pV Q (algMap v) = 1`, so `pV Q (algMap u) = pV Q g < 1`, giving `u ∈ m_Q`.
  have hv_unitQ : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
      (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _)) = 1 :=
    le_antisymm ((⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ _)
      (not_lt.mp (fun hlt ↦ hv_notMem
        ((Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := (⟨W⟩ : SmoothPlaneCurve F)) _ ⟨x, y, h_ns⟩).mp hlt)))
  have hu_mem : u ∈ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := by
    rw [← Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt]
    have : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
        (algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE u) =
        (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g := by
      rw [← h_lift, map_mul, hv_unitQ, mul_one]
    rw [this]; exact hg
  have hg_eq : g = algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pointValuation_mulByInt_pullback_algebraMap_eq_one_of_notMem ℓ hℓ P h_ns hQ hv_notMem,
    div_one]
  exact pointValuation_mulByInt_pullback_algebraMap_lt_one_of_mem ℓ hℓ P h_ns hQ hu_mem

/-- **Same-place regularity transfer, affine-image case.** For `φ = [ℓ]` and an affine smooth point
`P` whose image `[ℓ]·P` is the finite point `some x y h_ns`, the function `[ℓ].pullback g` is
regular at `P` iff `g` is regular at `⟨x, y, h_ns⟩` (`pointValuation ≤ 1` on both sides). -/
theorem mulByInt_samePlace_le_one_iff_affine [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns)
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) ≤ 1 ↔
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1 := by
  refine ⟨fun hP ↦ ?_, pointValuation_mulByInt_pullback_le_one_of_le_one ℓ hℓ P h_ns hQ⟩
  -- (⟹): contrapositive via `g⁻¹`.
  by_contra hQng
  rw [not_le] at hQng
  have hg_ne : g ≠ 0 := by
    rintro rfl; rw [map_zero] at hQng; exact absurd hQng (not_lt.mpr zero_le)
  -- `1 < pV Q g` ⟹ `pV Q g⁻¹ < 1`, so `[ℓ]^*(g⁻¹) ∈ m_P` (strict forward transfer).
  have hinvQ : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g⁻¹ < 1 := by
    rw [map_inv₀]
    exact (inv_lt_one₀ (lt_trans one_pos hQng)).mpr hQng
  have hPinv : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g⁻¹) < 1 :=
    pointValuation_mulByInt_pullback_lt_one_of_lt_one ℓ hℓ P h_ns hQ hinvQ
  -- but `[ℓ]^*g · [ℓ]^*(g⁻¹) = 1`, contradicting `pV P (φ^*g) ≤ 1 < pV P (φ^*g⁻¹)⁻¹`.
  have hmul : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) *
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hg_ne, map_one, map_one]
  -- `pV P (φ^*g) · pV P (φ^*g⁻¹) ≤ 1 · pV P (φ^*g⁻¹) < 1`, contradicting the product being `1`.
  have hlt1 : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) *
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g⁻¹) < 1 := by
    have hstep : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) *
        (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g⁻¹) ≤
        1 * (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g⁻¹) := by
      gcongr
    exact lt_of_le_of_lt hstep (by rw [one_mul]; exact hPinv)
  rw [hmul] at hlt1
  exact absurd hlt1 (lt_irrefl 1)

/-- `ord_∞ (algebraMap F KE c · f) ≥ n` when `ord_∞ f ≥ n` (constants are units at `∞`). -/
private theorem ord_algebraMap_mul_ge_aux' (c : F)
    {f : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} {n : WithTop ℤ}
    (hf : n ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f) :
    n ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (algebraMap F KE c * f) := by
  by_cases hc : c = 0
  · rw [hc, map_zero, zero_mul, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero]; exact le_top
  · by_cases hf0 : f = 0
    · rw [hf0, mul_zero, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero]; exact le_top
    · have hc_ne : algebraMap F KE c ≠ 0 :=
        fun h ↦ hc (FaithfulSMul.algebraMap_injective F _ (h.trans (map_zero _).symm))
      rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_mul hc_ne hf0,
        (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_algebraMap_F_nonzero hc, zero_add]
      exact hf

/-- `ord_∞(f + g) ≥ n` when both `ord_∞ f ≥ n`, `ord_∞ g ≥ n`. -/
private theorem ord_add_ge_of_both_ge_aux'
    {f g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField} {n : WithTop ℤ}
    (hf : n ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty f)
    (hg : n ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty g) :
    n ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (f + g) :=
  le_trans (le_min hf hg) ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_ge_min f g)

/-- `ord_∞` of the Weierstrass right-hand side `X³ + a₂X² + a₄X + a₆` at `X = mulByInt_x ℓ` is
`-6`: with `ord_∞ X = -2` the cubic `X³` strictly dominates (`-6 < -4 < -2 < 0`), so the leading
term wins each `ordAtInfty_add_eq_of_lt` step. -/
private theorem ordAtInfty_mulByInt_rhs_eq_neg_six_aux (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
        (mulByInt_x W ℓ ^ 3 + algebraMap F KE W.a₂ * mulByInt_x W ℓ ^ 2 +
          algebraMap F KE W.a₄ * mulByInt_x W ℓ + algebraMap F KE W.a₆) =
      ((-6 : ℤ) : WithTop ℤ) := by
  have hX_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ) =
      ((-2 : ℤ) : WithTop ℤ) := ordAtInfty_mulByInt_x W ℓ hℓ hℓF
  have hX_ne : mulByInt_x W ℓ ≠ 0 := mulByInt_x_ne_zero W ℓ hℓ
  have hX_cube : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ ^ 3) =
      ((-6 : ℤ) : WithTop ℤ) := (⟨W⟩ : SmoothPlaneCurve F).ord_pow_concrete hX_ne (-2) 3 hX_ord
  have h_a2X2 : ((-4 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (algebraMap F KE W.a₂ * mulByInt_x W ℓ ^ 2) :=
    ord_algebraMap_mul_ge_aux' W.a₂
      ((⟨W⟩ : SmoothPlaneCurve F).ord_pow_concrete hX_ne (-2) 2 hX_ord).symm.le
  have h_a4X : ((-2 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (algebraMap F KE W.a₄ * mulByInt_x W ℓ) :=
    ord_algebraMap_mul_ge_aux' W.a₄ hX_ord.symm.le
  have h_a6 : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (algebraMap F KE W.a₆) := by
    by_cases ha₆ : W.a₆ = 0
    · rw [ha₆, map_zero, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero]; exact le_top
    · rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_algebraMap_F_nonzero ha₆]
  have step1 : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_x W ℓ ^ 3 + algebraMap F KE W.a₂ * mulByInt_x W ℓ ^ 2) =
      ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt := lt_of_lt_of_le (show ((-6 : ℤ) : WithTop ℤ) < ((-4 : ℤ) : WithTop ℤ) from by
      exact_mod_cast (by lia : (-6 : ℤ) < -4)) h_a2X2
    rw [← hX_cube] at h_lt
    exact ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_eq_of_lt h_lt).trans hX_cube
  have step2 : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_x W ℓ ^ 3 + algebraMap F KE W.a₂ * mulByInt_x W ℓ ^ 2 +
        algebraMap F KE W.a₄ * mulByInt_x W ℓ) =
      ((-6 : ℤ) : WithTop ℤ) := by
    have h_lt := lt_of_lt_of_le (show ((-6 : ℤ) : WithTop ℤ) < ((-2 : ℤ) : WithTop ℤ) from by
      exact_mod_cast (by lia : (-6 : ℤ) < -2)) h_a4X
    rw [← step1] at h_lt
    exact ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_eq_of_lt h_lt).trans step1
  have h_lt := lt_of_lt_of_le (show ((-6 : ℤ) : WithTop ℤ) < (0 : WithTop ℤ) from by
    exact_mod_cast (by lia : (-6 : ℤ) < 0)) h_a6
  rw [← step2] at h_lt
  exact ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_eq_of_lt h_lt).trans step2

/-- Step (a) of `ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux`: writing `m = ord_∞ Y`, the
order of the standard-form LHS being `-6` forces `m ≤ -3` (else every term has order `≥ -4`). -/
private theorem ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux_m_le (ℓ : ℤ) (m : ℤ)
    (hm : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ) = ((m : ℤ) : WithTop ℤ))
    (h_xy_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ * mulByInt_y W ℓ) =
      (((-2 + m : ℤ)) : WithTop ℤ))
    (hY_sq_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) =
      ((2 * m : ℤ) : WithTop ℤ))
    (h_lhs_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_y W ℓ ^ 2 + algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ +
        algebraMap F KE W.a₃ * mulByInt_y W ℓ) = ((-6 : ℤ) : WithTop ℤ)) :
    m ≤ -3 := by
  have ha1xy : algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ =
      algebraMap F KE W.a₁ * (mulByInt_x W ℓ * mulByInt_y W ℓ) := by ring
  by_contra! h_not_le
  have h_lhs_ge : ((-4 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_y W ℓ ^ 2 + algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ +
        algebraMap F KE W.a₃ * mulByInt_y W ℓ) :=
    ord_add_ge_of_both_ge_aux' (ord_add_ge_of_both_ge_aux'
      (by rw [hY_sq_ord]; exact_mod_cast (by lia : (-4 : ℤ) ≤ 2 * m))
      (ha1xy ▸ ord_algebraMap_mul_ge_aux' W.a₁
        (by rw [h_xy_ord]; exact_mod_cast (by lia : (-4 : ℤ) ≤ -2 + m))))
      (ord_algebraMap_mul_ge_aux' W.a₃ (by rw [hm]; exact_mod_cast (by lia : (-4 : ℤ) ≤ m)))
  rw [h_lhs_ord] at h_lhs_ge
  exact absurd (by exact_mod_cast h_lhs_ge : (-4 : ℤ) ≤ -6) (by lia)

/-- Step (b) of `ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux`: once `m ≤ -3`, the `Y²` term
strictly dominates the other two LHS terms, so the standard-form LHS has the same order as `Y²`. -/
private theorem ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux_lhs_eq_sq (ℓ : ℤ) (m : ℤ)
    (hm : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ) = ((m : ℤ) : WithTop ℤ))
    (h_xy_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ * mulByInt_y W ℓ) =
      (((-2 + m : ℤ)) : WithTop ℤ))
    (hY_sq_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) =
      ((2 * m : ℤ) : WithTop ℤ))
    (h_m_le : m ≤ -3) :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_y W ℓ ^ 2 + algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ +
        algebraMap F KE W.a₃ * mulByInt_y W ℓ) =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) := by
  have ha1xy : algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ =
      algebraMap F KE W.a₁ * (mulByInt_x W ℓ * mulByInt_y W ℓ) := by ring
  have h_a1xy_gt : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) <
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
        (algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ) := by
    rw [hY_sq_ord, ha1xy]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge_aux' W.a₁ (le_of_eq h_xy_ord.symm))
    exact_mod_cast (by lia : (2 * m : ℤ) < -2 + m)
  have h_a3y_gt : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) <
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
        (algebraMap F KE W.a₃ * mulByInt_y W ℓ) := by
    rw [hY_sq_ord]
    refine lt_of_lt_of_le ?_ (ord_algebraMap_mul_ge_aux' W.a₃ (le_of_eq hm.symm))
    exact_mod_cast (by lia : (2 * m : ℤ) < m)
  have h_inner_eq := (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_eq_of_lt h_a1xy_gt
  exact ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_add_eq_of_lt (h_inner_eq ▸ h_a3y_gt)).trans h_inner_eq

/-- From `ord_∞(Y² + a₁XY + a₃Y) = -6` together with `ord_∞ X = -2` (`X = mulByInt_x ℓ`,
`Y = mulByInt_y ℓ`), conclude `ord_∞ Y = -3`. Writing `m := ord_∞ Y`, the cross term `a₁XY` and the
linear term `a₃Y` have order `≥ -2 + m` and `≥ m`; a lower bound forces `m ≤ -3`, after which `Y²`
strictly dominates and `ord_∞(LHS) = ord_∞(Y²) = 2m`, giving `2m = -6`. -/
private theorem ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux (ℓ : ℤ)
    (hX_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ) = ((-2 : ℤ) : WithTop ℤ))
    (hX_ne : mulByInt_x W ℓ ≠ 0)
    (h_lhs_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty
      (mulByInt_y W ℓ ^ 2 + algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ +
        algebraMap F KE W.a₃ * mulByInt_y W ℓ) = ((-6 : ℤ) : WithTop ℤ)) :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ) = ((-3 : ℤ) : WithTop ℤ) := by
  have hY_ne : mulByInt_y W ℓ ≠ 0 := by
    intro h
    rw [h] at h_lhs_ord
    simp only [ne_eq, zero_pow, mul_zero, add_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true] at h_lhs_ord
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_zero] at h_lhs_ord
    exact WithTop.top_ne_coe h_lhs_ord
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ) =
      ((m : ℤ) : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff _).not.mpr hY_ne)
    exact ⟨m, hm.symm⟩
  have hY_sq_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ ^ 2) =
      ((2 * m : ℤ) : WithTop ℤ) := (⟨W⟩ : SmoothPlaneCurve F).ord_pow_concrete hY_ne m 2 hm
  have h_xy_ord : (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_x W ℓ * mulByInt_y W ℓ) =
      (((-2 + m : ℤ)) : WithTop ℤ) := by
    refine ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_mul hX_ne hY_ne).trans ?_
    rw [hX_ord, hm]; push_cast; rfl
  have h_m_le :=
    ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux_m_le ℓ m hm h_xy_ord hY_sq_ord h_lhs_ord
  have h_outer_eq :=
    ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux_lhs_eq_sq ℓ m hm h_xy_ord hY_sq_ord h_m_le
  rw [h_outer_eq, hY_sq_ord] at h_lhs_ord
  have h_2m : (2 * m : ℤ) = -6 := by exact_mod_cast h_lhs_ord
  rw [hm]; exact_mod_cast (by lia : m = -3)

/-- **`ord_∞(mulByInt_y ℓ) = -3`** (field-general). From the curve equation
`Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` at `(mulByInt_x ℓ, mulByInt_y ℓ)` with
`ord_∞(mulByInt_x ℓ) = -2`: the RHS has `ord_∞ = -6` (`X³` dominates), forcing `2·ord_∞(Y) = -6`. -/
theorem ordAtInfty_mulByInt_y_eq_neg_three_general (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty (mulByInt_y W ℓ) = ((-3 : ℤ) : WithTop ℤ) := by
  have h_eq : mulByInt_y W ℓ ^ 2 +
        algebraMap F KE W.a₁ * mulByInt_x W ℓ * mulByInt_y W ℓ +
        algebraMap F KE W.a₃ * mulByInt_y W ℓ =
      mulByInt_x W ℓ ^ 3 +
        algebraMap F KE W.a₂ * mulByInt_x W ℓ ^ 2 +
        algebraMap F KE W.a₄ * mulByInt_x W ℓ +
        algebraMap F KE W.a₆ := by
    have h_alg := pullback_equation W (mulByInt W ℓ)
    have hx_pb : (mulByInt W ℓ).pullback (x_gen W) = mulByInt_x W ℓ :=
      mulByInt_pullback_x W ℓ hℓ
    have hy_pb : (mulByInt W ℓ).pullback (y_gen W) = mulByInt_y W ℓ :=
      mulByInt_pullback_y W ℓ hℓ
    rw [hx_pb, hy_pb] at h_alg
    rw [WeierstrassCurve.Affine.equation_iff] at h_alg
    exact h_alg
  exact ordAtInfty_mulByInt_y_of_lhs_eq_neg_six_aux (W := W) ℓ
    (ordAtInfty_mulByInt_x W ℓ hℓ hℓF) (mulByInt_x_ne_zero W ℓ hℓ)
    (h_eq ▸ ordAtInfty_mulByInt_rhs_eq_neg_six_aux (W := W) ℓ hℓ hℓF)

/-- `k = -P.toAffinePoint` lies in `ker[ℓ]` when `[ℓ]·P = O`. -/
private theorem mulByInt_neg_mem_kernel_of_torsion' (ℓ : ℤ)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point)) :
    -P.toAffinePoint ∈ (mulByInt W ℓ).kernel := by
  rw [HasseWeil.Isogeny.mem_kernel_iff, map_neg, hQ, neg_zero]

/-- **`ord_P (mulByInt_x ℓ) = -2` at an `ℓ`-torsion point `P`** (`[ℓ]·P = O`), via the
kernel-translation invariance of `mulByInt_x ℓ` and the translation order-transport
`ord_P (τ_{-P} g) = ord_∞ g`, transporting `ord_∞ (mulByInt_x ℓ) = -2` to `P`. -/
theorem ord_P_mulByInt_x_eq_neg_two_of_torsion (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_x W ℓ) = ((-2 : ℤ) : WithTop ℤ) := by
  set k : W.Point := -P.toAffinePoint with hk
  have hk_mem : k ∈ (mulByInt W ℓ).kernel := mulByInt_neg_mem_kernel_of_torsion' ℓ P hQ
  have h_zero : P.toAffinePoint + k = Affine.Point.zero := by rw [hk]; exact add_neg_cancel _
  have h_compat := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P k h_zero
  have h_inv : translateAlgEquivOfPoint W k (mulByInt_x W ℓ) = mulByInt_x W ℓ :=
    (WeilPairing.TorsionGeometric.hxy_mulByInt W ℓ hℓ ⟨k, hk_mem⟩).1
  exact (ord_P_eq_ordAtInfty_of_invariant_and_compatible W P k h_zero h_compat
    (mulByInt_x W ℓ) h_inv).trans (ordAtInfty_mulByInt_x W ℓ hℓ hℓF)

/-- **`ord_P (mulByInt_y ℓ) = -3` at an `ℓ`-torsion point `P`** (`[ℓ]·P = O`), via the same
transport route, using `ord_∞ (mulByInt_y ℓ) = -3`. -/
theorem ord_P_mulByInt_y_eq_neg_three_of_torsion (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point)) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_y W ℓ) = ((-3 : ℤ) : WithTop ℤ) := by
  set k : W.Point := -P.toAffinePoint with hk
  have hk_mem : k ∈ (mulByInt W ℓ).kernel := mulByInt_neg_mem_kernel_of_torsion' ℓ P hQ
  have h_zero : P.toAffinePoint + k = Affine.Point.zero := by rw [hk]; exact add_neg_cancel _
  have h_compat := isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W P k h_zero
  have h_inv : translateAlgEquivOfPoint W k (mulByInt_y W ℓ) = mulByInt_y W ℓ :=
    (WeilPairing.TorsionGeometric.hxy_mulByInt W ℓ hℓ ⟨k, hk_mem⟩).2
  exact (ord_P_eq_ordAtInfty_of_invariant_and_compatible W P k h_zero h_compat
    (mulByInt_y W ℓ) h_inv).trans (ordAtInfty_mulByInt_y_eq_neg_three_general ℓ hℓ hℓF)

/-- **Infinity comap identity for `[ℓ]`** (axiom-clean). `(pointValuation P).comap [ℓ].pullback =
ordAtInftyValuation` when `[ℓ]·P = O`. Proved via `eq_ordAtInftyValuation_of_x_y`: the comap sends
`x_gen ↦ exp 2`, `y_gen ↦ exp 3` (the torsion-pole orders) and fixes `F^×`. -/
theorem comap_pointValuation_mulByInt_eq_infty [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point)) :
    ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).comap (mulByInt W ℓ).pullback.toRingHom =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  set τ := (mulByInt W ℓ).pullback with hτ
  set w := ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).comap τ.toRingHom with hw
  have hw_apply : ∀ g, w g = (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (τ g) := fun g ↦
    Valuation.comap_apply _ _ _
  have hx : w (x_gen W) = WithZero.exp 2 := by
    rw [hw_apply, show τ (x_gen W) = mulByInt_x W ℓ from mulByInt_pullback_x W ℓ hℓ0,
      pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F)) (P := P)
        (mulByInt_x_ne_zero W ℓ hℓ0) (ord_P_mulByInt_x_eq_neg_two_of_torsion ℓ hℓ0 hℓ P hQ)]
    norm_num
  have hy : w (y_gen W) = WithZero.exp 3 := by
    have hy_ne : mulByInt_y W ℓ ≠ 0 := by
      intro h0
      have := ord_P_mulByInt_y_eq_neg_three_of_torsion (W := W) ℓ hℓ0 hℓ P hQ
      rw [h0, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero] at this
      exact WithTop.top_ne_coe this
    rw [hw_apply, show τ (y_gen W) = mulByInt_y W ℓ from mulByInt_pullback_y W ℓ hℓ0,
      pointValuation_eq_exp_neg_of_ord_P_eq (C := (⟨W⟩ : SmoothPlaneCurve F)) (P := P)
        hy_ne (ord_P_mulByInt_y_eq_neg_three_of_torsion ℓ hℓ0 hℓ P hQ)]
    norm_num
  have hc : ∀ c : F, c ≠ 0 → w (algebraMap F KE c) = 1 := fun c hc ↦ by
    rw [hw_apply, show τ (algebraMap F KE c) = algebraMap F KE c from τ.commutes c]
    exact pointValuation_algebraMap_F_eq_one_of_ne_zero W P hc
  exact eq_ordAtInftyValuation_of_x_y W w hx hy hc

/-- **Same-place regularity transfer, infinity-image case** (proven, axiom-clean). For `φ = [ℓ]`
and an affine smooth point `P` that is an `ℓ`-torsion point (`[ℓ]·P = O`), `[ℓ].pullback g` is
regular at `P` iff `g` is regular at `∞`. Read straight off the infinity comap identity
`comap_pointValuation_mulByInt_eq_infty`: `pointValuation P ([ℓ]^*g) = ordAtInftyValuation g`. -/
theorem mulByInt_samePlace_le_one_iff_infty [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point))
    (g : (⟨W⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) ≤ 1 ↔
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation g ≤ 1 := by
  have hval := comap_pointValuation_mulByInt_eq_infty (W := W) ℓ hℓ P hQ
  have h_at : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P ((mulByInt W ℓ).pullback g) =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation g := by
    have := congrFun (congrArg DFunLike.coe hval) g
    rwa [Valuation.comap_apply] at this
  rw [h_at]

/-- **(SamePlace), affine-image case.** The comap valuation
`(pointValuation P).comap [ℓ].pullback` is `Valuation.IsEquiv` to `pointValuation ⟨x,y,h_ns⟩` at the
affine image `[ℓ]·P = some x y h_ns`. Feeds `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. -/
theorem mulByInt_comap_pointValuation_isEquiv_affine [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).comap
        (mulByInt W ℓ).pullback.toRingHom).IsEquiv
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩) := by
  apply Valuation.isEquiv_of_val_le_one
  intro g
  rw [Valuation.comap_apply]
  exact mulByInt_samePlace_le_one_iff_affine (W := W) ℓ hℓ P h_ns hQ g

/-- **(SamePlace), infinity-image case.** The comap valuation
`(pointValuation P).comap [ℓ].pullback` is `Valuation.IsEquiv` to `ordAtInftyValuation` when
`[ℓ]·P = O`. Feeds `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. -/
theorem mulByInt_comap_pointValuation_isEquiv_infty [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = (0 : W.Point)) :
    (((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).comap
        (mulByInt W ℓ).pullback.toRingHom).IsEquiv
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation := by
  apply Valuation.isEquiv_of_val_le_one
  intro g
  rw [Valuation.comap_apply]
  exact mulByInt_samePlace_le_one_iff_infty (W := W) ℓ hℓ P hQ g

/-- **Separability-free `x`-residue for `[ℓ]`** (`ℓ ≠ 0` only): `[ℓ]^*x_gen ≡ x` modulo `m_P`. -/
theorem pointValuation_mulByInt_x_sub_lt_one_of_ne_zero [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_x W ℓ - algebraMap F KE x) < 1 :=
  pointValuation_mulByInt_x_sub_lt_one ℓ hℓ P h_ns hQ

/-- **Separability-free `y`-residue for `[ℓ]`** (`ℓ ≠ 0` only): `[ℓ]^*y_gen ≡ y` modulo `m_P`. -/
theorem pointValuation_mulByInt_y_sub_lt_one_of_ne_zero [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F} (h_ns : W.Nonsingular x y)
    (hQ : (mulByInt W ℓ).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (mulByInt_y W ℓ - algebraMap F KE y) < 1 :=
  pointValuation_mulByInt_y_sub_lt_one ℓ hℓ P h_ns hQ

end HasseWeil
