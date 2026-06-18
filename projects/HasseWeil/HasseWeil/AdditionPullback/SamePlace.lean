/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback
import HasseWeil.EC.DifferentialOrd
import HasseWeil.EC.MulByIntSamePlace
import HasseWeil.Hasse.OpenLemmaPrimitives

/-!
# The **(SamePlace)** fact for an addition-formula isogeny `α₁ + α₂` (`1 − π` case)

This file is the addition-formula analogue of `HasseWeil/EC/MulByIntSamePlace.lean`.  For the
genuine separable isogeny `1 − π = id + (−π)` — and more generally for any addition-formula isogeny
`addIsog hxy hinj` (the rational map `P ↦ α₁(P) + α₂(P)` on the function field, with the explicit
Weierstrass addition-formula comorphism `addPullbackAlgHomPair`) — it supplies the
**`Valuation.IsEquiv`** ("same place / same valuation ring") input that the axiom-clean glue
`comap_pointValuation_eq_of_isEquiv_of_ord_eq_one` (`EC/IsogenyOrdTransport.lean`) consumes to
upgrade to value-precise order-transport `ord_P ((α₁+α₂)^* g) = ord_{(α₁+α₂)(P)} g`.

## The centerpiece — `oneSub_coords_at_affine`

The division-polynomial coordinate specialisation `[ℓ]P = (φ_ℓ(P)/ψ_ℓ(P)², …)`
(`mulByInt_coords_at_affine`) is replaced by the **addition-formula closed-point specialisation**:
for a smooth point `P` whose image `(α₁+α₂)(P) = α₁(P) + α₂(P)` is the finite point `some x y h_ns`,
the addition-formula comorphism coordinates `addPullback_x_pair`, `addPullback_y_pair` are
congruent, modulo the maximal ideal `m_P`, to `x` and `y`.

The proof is the explicit Weierstrass addition formula: the addition-formula coordinates are
`addX (α₁^*x_gen) (α₂^*x_gen) L`, `addY (α₁^*x_gen) (α₂^*x_gen) (α₁^*y_gen) L` with
`L = slope (α₁^*x_gen) (α₂^*x_gen) (α₁^*y_gen) (α₂^*y_gen)`, and `α₁(P) + α₂(P)` has *exactly* those
coordinates evaluated at the closed-point residues of the four pullback generators (mathlib's
`Affine.Point.add_some` = `addX`/`addY` of the summand coordinates).  So given the per-summand
**closed-point residue witnesses** `α_i^* x_gen ≡ x_{α_i(P)}`, `α_i^* y_gen ≡ y_{α_i(P)}` modulo
`m_P` (the SamePlace content of the two *summands* `α₁`, `α₂`), the addition-formula coordinates
residue to the addition formula of the residues, which is the image `(x, y)`.

This is exactly the `mulByInt_coords_at_affine` content with the division-polynomial group law
replaced by the explicit addition formula.

## Status

* **`oneSub_coords_at_affine`** — the centerpiece, **sorry-free, axiom-clean**.  It takes the
  per-summand residue witnesses and an `AddNonInversePair` non-degeneracy as hypotheses (the honest
  reduction: for general `α₁, α₂` the summand residues are not derivable from the abstract `Isogeny`
  fields; for `α₁ = id`, `α₂ = −π` they are the Frobenius residues, supplied downstream).
* **`addIsog_samePlace_le_one_iff_affine`** / **`addIsog_comap_pointValuation_isEquiv_affine`** —
  the affine **SamePlace** transfer / `IsEquiv`, **sorry-free, axiom-clean**, built by the
  *verbatim* residue-matching chain of `MulByIntSamePlace.lean` (univariate/bivariate bridges →
  regularity / unit / vanishing transfer → the `g⁻¹` contrapositive) with
  `addPullback_x_pair`/`addPullback_y_pair` replacing the division coordinate functions.

The **e = 1** affine input and the assembled affine comap identity
`comap_pointValuation_oneSub_eq_affine` rest on the additional uniformizer-order datum; see the
final section.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.5–2.6, III.4.10c, III.2.3c.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-! ### Replicated value-bridge lemmas

The residue bridges of `MulByIntSamePlace.lean` (`pointValuation_aeval_sub_eval_lt_one`,
`pointValuation_algebraMap_sub_evalAt_lt_one`, `algebraMap_polynomial_eq_aeval_x_gen`,
`pointValuation_bivariate_bridge`) are `private` to that file.  They are entirely isogeny-agnostic —
pure residue facts in `K(E)` — so we re-state them here.  These are verbatim copies (no `[ℓ]` content).
-/

/-- **Univariate value bridge** (verbatim copy of the `private` `MulByIntSamePlace` lemma):
if `u` is regular at `P` and `u ≡ a` modulo `m_P`, then `q(u) ≡ q(a)` modulo `m_P`. -/
private theorem pV_aeval_sub_eval_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {u : KE} {a : F}
    (hu_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P u ≤ 1)
    (hu : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u - algebraMap F KE a) < 1)
    (q : Polynomial F) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (Polynomial.aeval u q - algebraMap F KE (q.eval a)) < 1 := by
  induction q using Polynomial.induction_on with
  | C c =>
    simp only [Polynomial.aeval_C, Polynomial.eval_C, sub_self, map_zero]
    exact zero_lt_one
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, map_add,
      show Polynomial.aeval u p + Polynomial.aeval u q -
          (algebraMap F KE (p.eval a) + algebraMap F KE (q.eval a)) =
        (Polynomial.aeval u p - algebraMap F KE (p.eval a)) +
          (Polynomial.aeval u q - algebraMap F KE (q.eval a)) from by ring]
    exact lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt hp hq)
  | monomial n c ih =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
    rw [show algebraMap F KE c * u ^ (n + 1) - algebraMap F KE (c * a ^ (n + 1)) =
          u * (algebraMap F KE c * u ^ n - algebraMap F KE (c * a ^ n)) +
            algebraMap F KE (c * a ^ n) * (u - algebraMap F KE a) from by
        push_cast [map_mul, map_pow]; ring]
    have ih' : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap F KE c * u ^ n - algebraMap F KE (c * a ^ n)) < 1 := by
      rw [show algebraMap F KE c * u ^ n =
          Polynomial.aeval u (Polynomial.C c * Polynomial.X ^ n) from by
        rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X],
        show c * a ^ n = (Polynomial.C c * Polynomial.X ^ n).eval a from by
        rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]]
      exact ih
    refine lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt ?_ ?_)
    · exact pointValuation_mul_lt_one_of_le_and_lt W P hu_le ih'
    · exact pointValuation_mul_lt_one_of_le_and_lt W P
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _) hu

/-- **Coordinate-ring residue bridge** (verbatim copy): a coordinate-ring element `r` is congruent,
modulo `m_P`, to its value `evalAt P r`. -/
private theorem pV_algebraMap_sub_evalAt_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint)
    (r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt P r)) < 1 := by
  have hmem : r - algebraMap F (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing
      ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt P r) ∈
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt P := by
    rw [← (⟨W.toAffine⟩ : SmoothPlaneCurve F).ker_evalAt P, RingHom.mem_ker, map_sub,
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt_algebraMap P, sub_self]
  have hlt := (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F))
    (r - algebraMap F (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing
      ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt P r)) P).mpr hmem
  rwa [map_sub, ← IsScalarTower.algebraMap_apply F (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField] at hlt

/-- **Bivariate value bridge** (verbatim copy): if `u ≡ a`, `v ≡ b` modulo `m_P` (both regular at
`P`), then `p(u, v) ≡ p(a, b)` modulo `m_P`. -/
private theorem pV_bivariate_bridge
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {u v : KE} {a b : F}
    (hu_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P u ≤ 1)
    (hu : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u - algebraMap F KE a) < 1)
    (_hv_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P v ≤ 1)
    (hv : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (v - algebraMap F KE b) < 1)
    (p : Polynomial (Polynomial F)) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        ((p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
          algebraMap F KE (p.evalEval a b)) < 1 := by
  induction p using Polynomial.induction_on with
  | C q =>
    rw [Polynomial.map_C, Polynomial.evalEval_C, Polynomial.evalEval_C,
      show (Polynomial.mapRingHom (algebraMap F KE)) q = q.map (algebraMap F KE) from rfl,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact pV_aeval_sub_eval_lt_one P hu_le hu q
  | add p₁ p₂ h₁ h₂ =>
    rw [Polynomial.map_add, Polynomial.evalEval_add, Polynomial.evalEval_add, map_add,
      show (p₁.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v +
            (p₂.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
            (algebraMap F KE (p₁.evalEval a b) + algebraMap F KE (p₂.evalEval a b)) =
          ((p₁.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
              algebraMap F KE (p₁.evalEval a b)) +
            ((p₂.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v -
              algebraMap F KE (p₂.evalEval a b)) from by ring]
    exact lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt h₁ h₂)
  | monomial n q ih =>
    set Au : KE := (((Polynomial.C q) * Polynomial.X ^ n).map
      (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v with hAu
    set Ab : F := ((Polynomial.C q) * Polynomial.X ^ n).evalEval a b with hAb
    have heval_u : (((Polynomial.C q) * Polynomial.X ^ (n + 1)).map
        (Polynomial.mapRingHom (algebraMap F KE))).evalEval u v = Au * v := by
      rw [hAu, show (Polynomial.C q) * Polynomial.X ^ (n + 1) =
          ((Polynomial.C q) * Polynomial.X ^ n) * Polynomial.X from by ring,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.evalEval_mul, Polynomial.evalEval_X]
    have heval_ab : ((Polynomial.C q) * Polynomial.X ^ (n + 1)).evalEval a b = Ab * b := by
      rw [hAb, show (Polynomial.C q) * Polynomial.X ^ (n + 1) =
          ((Polynomial.C q) * Polynomial.X ^ n) * Polynomial.X from by ring,
        Polynomial.evalEval_mul, Polynomial.evalEval_X]
    have hAu_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P Au ≤ 1 := by
      have hAu_split : Au = (Au - algebraMap F KE Ab) + algebraMap F KE Ab := by ring
      rw [hAu_split]
      exact pointValuation_add_le_one W P (le_of_lt ih)
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)
    rw [heval_u, heval_ab,
      show Au * v - algebraMap F KE (Ab * b) =
          Au * (v - algebraMap F KE b) + algebraMap F KE b * (Au - algebraMap F KE Ab) from by
        push_cast [map_mul]; ring]
    refine lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
      (max_lt ?_ ?_)
    · exact pointValuation_mul_lt_one_of_le_and_lt W P hAu_le hv
    · exact pointValuation_mul_lt_one_of_le_and_lt W P
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _) ih

/-! ### A small residue toolkit (`≡ mod m_P` is a ring congruence, units invert)

`u ≡ a mod m_P` is `pointValuation P (u − a) < 1`.  We package the facts that this congruence is
preserved by `+, −, *`, by squaring, and (for a *unit* residue `c ≠ 0`) by division.  These reduce
the addition-formula residue matching to the four generator residues, exactly as
`mulByInt_coords_at_affine` reduces to the division-coordinate residues.  We abbreviate
`pV P := pointValuation P`. -/

/-- Abbreviation: `resid P u a` means `u ≡ a` modulo `m_P`, i.e. `pV P (u − a) < 1`. -/
private abbrev resid (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) (u : KE) (a : F) : Prop :=
  (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u - algebraMap F KE a) < 1

/-- A residue `u ≡ a` makes `u` regular at `P`. -/
private theorem resid_le_one {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u : KE} {a : F}
    (h : resid P u a) : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P u ≤ 1 := by
  rw [show u = (u - algebraMap F KE a) + algebraMap F KE a from by ring]
  exact pointValuation_add_le_one W P (le_of_lt h)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P a)

/-- Residues add: `u ≡ a`, `v ≡ b` ⟹ `u + v ≡ a + b`. -/
private theorem resid_add {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u v : KE}
    {a b : F} (hu : resid P u a) (hv : resid P v b) : resid P (u + v) (a + b) := by
  change (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u + v - algebraMap F KE (a + b)) < 1
  rw [show u + v - algebraMap F KE (a + b) =
      (u - algebraMap F KE a) + (v - algebraMap F KE b) from by rw [map_add]; ring]
  exact lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
    (max_lt hu hv)

/-- Residues subtract: `u ≡ a`, `v ≡ b` ⟹ `u − v ≡ a − b`. -/
private theorem resid_sub {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u v : KE}
    {a b : F} (hu : resid P u a) (hv : resid P v b) : resid P (u - v) (a - b) := by
  change (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u - v - algebraMap F KE (a - b)) < 1
  rw [show u - v - algebraMap F KE (a - b) =
      (u - algebraMap F KE a) - (v - algebraMap F KE b) from by rw [map_sub]; ring]
  exact lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_sub _ _)
    (max_lt hu hv)

/-- Residues multiply: `u ≡ a`, `v ≡ b` ⟹ `u · v ≡ a · b`. -/
private theorem resid_mul {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u v : KE}
    {a b : F} (hu : resid P u a) (hv : resid P v b) : resid P (u * v) (a * b) := by
  have hu_le := resid_le_one hu
  change (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u * v - algebraMap F KE (a * b)) < 1
  rw [show u * v - algebraMap F KE (a * b) =
        u * (v - algebraMap F KE b) + algebraMap F KE b * (u - algebraMap F KE a) from by
      rw [map_mul]; ring]
  refine lt_of_le_of_lt (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add _ _)
    (max_lt ?_ ?_)
  · exact pointValuation_mul_lt_one_of_le_and_lt W P hu_le hv
  · exact pointValuation_mul_lt_one_of_le_and_lt W P
      ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P b) hu

/-- A scalar `algebraMap F KE c` residues to `c`. -/
private theorem resid_const (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) (c : F) :
    resid P (algebraMap F KE c) c := by
  unfold resid; rw [sub_self, map_zero]; exact zero_lt_one

/-- A residue `u ≡ a` with `a ≠ 0` makes `u` a unit at `P` (`pV P u = 1`). -/
private theorem resid_unit {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u : KE} {a : F}
    (h : resid P u a) (ha : a ≠ 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P u = 1 := by
  have hconst : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap F KE a) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P ha
  rw [show u = (u - algebraMap F KE a) + algebraMap F KE a from by ring,
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]; exact h), hconst]

/-- Residues divide by a *unit* residue: `u ≡ a`, `d ≡ c` with `c ≠ 0` ⟹ `u / d ≡ a / c`.
The denominator `d` is a unit at `P` (`pV P d = 1`), so dividing preserves the strict bound. -/
private theorem resid_div {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u d : KE}
    {a c : F} (hu : resid P u a) (hd : resid P d c) (hc : c ≠ 0) :
    resid P (u / d) (a / c) := by
  -- `d` is a unit at `P` (its residue `c ≠ 0`), hence nonzero.
  have hd_unit : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P d = 1 := resid_unit hd hc
  have hd_ne : d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hd_unit; exact zero_ne_one hd_unit
  have hcast_ne : algebraMap F KE c ≠ 0 :=
    fun h ↦ hc (FaithfulSMul.algebraMap_injective F KE (h.trans (map_zero _).symm))
  -- numerator `u·c − a·d` residues to `a·c − a·c = 0`.
  have hnum : resid P (u * algebraMap F KE c - algebraMap F KE a * d) (0 : F) := by
    have := resid_sub (resid_mul hu (resid_const P c)) (resid_mul (resid_const P a) hd)
    rwa [show a * c - a * c = (0 : F) from by ring] at this
  have hnum' : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
      (u * algebraMap F KE c - algebraMap F KE a * d) < 1 := by
    have := hnum; unfold resid at this; rwa [map_zero, sub_zero] at this
  have hid : u / d - algebraMap F KE (a / c) =
      (u * algebraMap F KE c - algebraMap F KE a * d) * (d * algebraMap F KE c)⁻¹ := by
    rw [map_div₀, div_sub_div _ _ hd_ne hcast_ne, mul_inv, div_eq_mul_inv]
    ring
  change (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (u / d - algebraMap F KE (a / c)) < 1
  rw [hid]
  -- the denominator `(d · c)⁻¹` is a unit (`pV = 1 ≤ 1`); multiply by the `< 1` numerator.
  have hc_unit : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap F KE c) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hc
  have hden_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
      ((d * algebraMap F KE c)⁻¹) ≤ 1 := by
    rw [map_inv₀, map_mul, hd_unit, one_mul, hc_unit, inv_one]
  rw [mul_comm]
  exact pointValuation_mul_lt_one_of_le_and_lt W P hden_le hnum'

/-- A residue squares: `u ≡ a` ⟹ `u² ≡ a²`. -/
private theorem resid_sq {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u : KE} {a : F}
    (hu : resid P u a) : resid P (u ^ 2) (a ^ 2) := by
  rw [show u ^ 2 = u * u from by ring, show a ^ 2 = a * a from by ring]
  exact resid_mul hu hu

/-- A residue raises to a natural power: `u ≡ a` ⟹ `u^n ≡ a^n`. -/
private theorem resid_pow {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {u : KE} {a : F}
    (hu : resid P u a) (n : ℕ) : resid P (u ^ n) (a ^ n) := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ]; exact resid_mul ih hu

/-- The generic `x`-coordinate residues to `P.x`: `x_gen ≡ P.x` modulo `m_P`. -/
private theorem resid_x_gen (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    resid P (x_gen W) P.x := by
  unfold resid
  rw [x_gen_sub_const_eq_algebraMap_XClass]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F)) _ P).mpr (XClass_mem_maximalIdealAt W P P.x rfl)

/-- The generic `y`-coordinate residues to `P.y`: `y_gen ≡ P.y` modulo `m_P`. -/
private theorem resid_y_gen (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    resid P (y_gen W) P.y := by
  have h := pV_algebraMap_sub_evalAt_lt_one P (Affine.CoordinateRing.mk W.toAffine Polynomial.X)
  -- `mk X = y_gen` and `evalAt P (mk X) = P.y`.
  rw [Curves.SmoothPlaneCurve.evalAt_mk] at h
  have hgen : algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.mk W.toAffine Polynomial.X)
      = y_gen W := rfl
  have hval : (Polynomial.X : Polynomial (Polynomial F)).evalEval P.x P.y = P.y := by
    simp [Polynomial.evalEval]
  rw [hgen, hval] at h
  exact h

/-! ### The addition-formula closed-point specialisation — `oneSub_coords_at_affine`

The centerpiece, the analogue of `mulByInt_coords_at_affine`.  We work in the **non-doubling case**
`α₁^*x_gen ≢ α₂^*x_gen` modulo `m_P` (i.e. the residues `x₁ ≠ x₂`), which is exactly the `1 − π`
situation (`x_gen ≢ π·x_gen`, their `∞`-orders differing).  There the slope is the secant
`(y₁ − y₂)/(x₁ − x₂)`, and the addition formula `addX`/`addY` are built from the four generators by
`+, −, *` and division by the unit `α₁^*x_gen − α₂^*x_gen`.  Feeding the four per-summand residues
through the residue toolkit, the addition-formula coordinates `addPullback_x_pair`,
`addPullback_y_pair` residue to the addition formula of the residues, which by mathlib's
`Affine.Point.add_some` is the image `α₁(P) + α₂(P)`. -/

variable {α₁ α₂ : Isogeny W.toAffine W.toAffine}

/-- **The slope residue** (non-doubling case).  If `α₁^*x_gen ≡ x₁`, `α₂^*x_gen ≡ x₂`,
`α₁^*y_gen ≡ y₁`, `α₂^*y_gen ≡ y₂` modulo `m_P` with `x₁ ≠ x₂`, then the addition-formula slope
`addSlopePair α₁ α₂` residues to the secant slope `slope x₁ x₂ y₁ y₂ = (y₁ − y₂)/(x₁ − x₂)`. -/
private theorem resid_addSlopePair
    {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {x₁ y₁ x₂ y₂ : F}
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁) (hy₂ : resid P (α₂.pullback (y_gen W)) y₂)
    (hx_ne : x₁ ≠ x₂) :
    resid P (addSlopePair α₁ α₂) (W.toAffine.slope x₁ x₂ y₁ y₂) := by
  -- the pullback-x's are distinct in `K(E)` (their residues `x₁ ≠ x₂` differ).
  have hpb_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W) := by
    intro h
    -- `α₁^*x − α₂^*x ≡ x₁ − x₂ ≠ 0`; but the difference is `0`, so `0` would be a unit at `P`.
    have hsub : resid P ((0 : KE)) (x₁ - x₂) := by
      have h0 := resid_sub hx₁ hx₂
      rwa [h, sub_self] at h0
    have hunit := resid_unit hsub (sub_ne_zero.mpr hx_ne)
    rw [map_zero] at hunit
    exact zero_ne_one hunit
  have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
    WeierstrassCurve.Affine.slope_of_X_ne hx_ne
  rw [hslope, addSlopePair_eq_of_x_ne hpb_ne]
  exact resid_div (resid_sub hy₁ hy₂) (resid_sub hx₁ hx₂) (sub_ne_zero.mpr hx_ne)

/-- Convenience: the constant coefficients `a₁, a₂` (as `K(E)`-elements) residue to themselves. -/
private theorem resid_a₁ (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) :
    resid P (algebraMap F KE W.toAffine.a₁) W.toAffine.a₁ := resid_const P _

/-- **The `x`-coordinate residue of the addition formula** (non-doubling case): under the four
generator residues with `x₁ ≠ x₂`, the addition-formula `x`-coordinate `addPullback_x_pair α₁ α₂`
residues to `addX x₁ x₂ (slope x₁ x₂ y₁ y₂)`, the `x`-coordinate of the secant addition formula. -/
private theorem resid_addPullback_x_pair
    {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {x₁ y₁ x₂ y₂ : F}
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁) (hy₂ : resid P (α₂.pullback (y_gen W)) y₂)
    (hx_ne : x₁ ≠ x₂) :
    resid P (addPullback_x_pair α₁ α₂)
      (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
  have hL := resid_addSlopePair hx₁ hx₂ hy₁ hy₂ hx_ne
  -- `addX X₁ X₂ ℓ = ℓ² + a₁·ℓ − a₂ − X₁ − X₂`.
  have ha₁ : (W_KE W).toAffine.a₁ = algebraMap F KE W.toAffine.a₁ := rfl
  have ha₂ : (W_KE W).toAffine.a₂ = algebraMap F KE W.toAffine.a₂ := rfl
  rw [show addPullback_x_pair α₁ α₂ =
      (addSlopePair α₁ α₂) ^ 2 + algebraMap F KE W.toAffine.a₁ * (addSlopePair α₁ α₂)
        - algebraMap F KE W.toAffine.a₂ - α₁.pullback (x_gen W) - α₂.pullback (x_gen W) from by
    unfold addPullback_x_pair WeierstrassCurve.Affine.addX
    rw [ha₁, ha₂]]
  rw [show W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      (W.toAffine.slope x₁ x₂ y₁ y₂) ^ 2 + W.toAffine.a₁ * (W.toAffine.slope x₁ x₂ y₁ y₂)
        - W.toAffine.a₂ - x₁ - x₂ from by unfold WeierstrassCurve.Affine.addX; ring]
  exact resid_sub (resid_sub (resid_sub
    (resid_add (resid_sq hL) (resid_mul (resid_a₁ P) hL)) (resid_const P _)) hx₁) hx₂

/-- **The `y`-coordinate residue of the addition formula** (non-doubling case): under the four
generator residues with `x₁ ≠ x₂`, the addition-formula `y`-coordinate `addPullback_y_pair α₁ α₂`
residues to `addY x₁ x₂ y₁ (slope x₁ x₂ y₁ y₂)`. -/
private theorem resid_addPullback_y_pair
    {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {x₁ y₁ x₂ y₂ : F}
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁) (hy₂ : resid P (α₂.pullback (y_gen W)) y₂)
    (hx_ne : x₁ ≠ x₂) :
    resid P (addPullback_y_pair α₁ α₂)
      (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) := by
  have hL := resid_addSlopePair hx₁ hx₂ hy₁ hy₂ hx_ne
  have hX := resid_addPullback_x_pair hx₁ hx₂ hy₁ hy₂ hx_ne
  -- `addY X₁ X₂ Y₁ ℓ = -(addX) - a₁·(addX) - a₃ - (ℓ·(addX − X₁) + Y₁)`  (negY of negAddY).
  -- Express both sides as polynomial combinations of the generator residues + addX residue.
  have ha₁ : (W_KE W).toAffine.a₁ = algebraMap F KE W.toAffine.a₁ := rfl
  have ha₃ : (W_KE W).toAffine.a₃ = algebraMap F KE W.toAffine.a₃ := rfl
  rw [show addPullback_y_pair α₁ α₂ =
      -((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W))
        - algebraMap F KE W.toAffine.a₁ * (addPullback_x_pair α₁ α₂)
        - algebraMap F KE W.toAffine.a₃ from by
    rw [show addPullback_y_pair α₁ α₂ =
        (W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
          ((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W)) from rfl]
    unfold WeierstrassCurve.Affine.negY
    rw [ha₁, ha₃]]
  rw [show W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂) =
      -((W.toAffine.slope x₁ x₂ y₁ y₂) *
              (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁) + y₁)
        - W.toAffine.a₁ * (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        - W.toAffine.a₃ from by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
      WeierstrassCurve.Affine.negAddY
    ring]
  -- `-u ≡ -a`: rewrite as `0 - u`.
  have hnegAddY : resid P
      (-((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W)))
      (-((W.toAffine.slope x₁ x₂ y₁ y₂) *
              (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) - x₁) + y₁)) := by
    have := resid_sub (resid_const P (0 : F))
      (resid_add (resid_mul hL (resid_sub hX hx₁)) hy₁)
    rwa [map_zero, zero_sub, zero_sub] at this
  exact resid_sub (resid_sub hnegAddY (resid_mul (resid_a₁ P) hX)) (resid_const P _)

/-! ### Slope-parametric residue arithmetic (covers the doubling/tangent case)

The two lemmas above derive the slope residue internally via the *secant* formula
(`resid_addSlopePair`, requiring `x₁ ≠ x₂`).  In the **doubling case** `x₁ = x₂` the `K(E)`-element
`addSlopePair α₁ α₂` is still the secant `(α₁^*y − α₂^*y)/(α₁^*x − α₂^*x)` (the pullbacks are distinct
in `K(E)`) but it residues to the *tangent* slope (an `L'Hôpital` limit), supplied externally.  We
therefore restate the `addX`/`addY` residue arithmetic taking the slope residue
`resid P (addSlopePair α₁ α₂) ℓ` as a hypothesis for an *arbitrary* `ℓ` — the residue arithmetic of
`addX`/`addY` is identical in both cases. -/

/-- **`x`-coordinate residue from a slope residue** (slope-parametric).  Given the slope residue
`addSlopePair α₁ α₂ ≡ ℓ` and the two `x`-generator residues, `addPullback_x_pair α₁ α₂` residues to
`addX x₁ x₂ ℓ`.  Covers the doubling case (`ℓ` = tangent slope). -/
private theorem resid_addPullback_x_pair_of_slope
    {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {x₁ x₂ ℓ : F}
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hL : resid P (addSlopePair α₁ α₂) ℓ) :
    resid P (addPullback_x_pair α₁ α₂) (W.toAffine.addX x₁ x₂ ℓ) := by
  have ha₁ : (W_KE W).toAffine.a₁ = algebraMap F KE W.toAffine.a₁ := rfl
  have ha₂ : (W_KE W).toAffine.a₂ = algebraMap F KE W.toAffine.a₂ := rfl
  rw [show addPullback_x_pair α₁ α₂ =
      (addSlopePair α₁ α₂) ^ 2 + algebraMap F KE W.toAffine.a₁ * (addSlopePair α₁ α₂)
        - algebraMap F KE W.toAffine.a₂ - α₁.pullback (x_gen W) - α₂.pullback (x_gen W) from by
    unfold addPullback_x_pair WeierstrassCurve.Affine.addX
    rw [ha₁, ha₂]]
  rw [show W.toAffine.addX x₁ x₂ ℓ =
      ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ from by
    unfold WeierstrassCurve.Affine.addX; ring]
  exact resid_sub (resid_sub (resid_sub
    (resid_add (resid_sq hL) (resid_mul (resid_a₁ P) hL)) (resid_const P _)) hx₁) hx₂

/-- **`y`-coordinate residue from a slope residue** (slope-parametric).  Given the slope residue
`addSlopePair α₁ α₂ ≡ ℓ`, the two `x`-generator residues, and the first `y`-generator residue,
`addPullback_y_pair α₁ α₂` residues to `addY x₁ x₂ y₁ ℓ`.  Covers the doubling case. -/
private theorem resid_addPullback_y_pair_of_slope
    {P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint} {x₁ y₁ x₂ ℓ : F}
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁)
    (hL : resid P (addSlopePair α₁ α₂) ℓ) :
    resid P (addPullback_y_pair α₁ α₂) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  have hX := resid_addPullback_x_pair_of_slope hx₁ hx₂ hL
  have ha₁ : (W_KE W).toAffine.a₁ = algebraMap F KE W.toAffine.a₁ := rfl
  have ha₃ : (W_KE W).toAffine.a₃ = algebraMap F KE W.toAffine.a₃ := rfl
  rw [show addPullback_y_pair α₁ α₂ =
      -((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W))
        - algebraMap F KE W.toAffine.a₁ * (addPullback_x_pair α₁ α₂)
        - algebraMap F KE W.toAffine.a₃ from by
    rw [show addPullback_y_pair α₁ α₂ =
        (W_KE W).toAffine.negY (addPullback_x_pair α₁ α₂)
          ((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W)) from rfl]
    unfold WeierstrassCurve.Affine.negY
    rw [ha₁, ha₃]]
  rw [show W.toAffine.addY x₁ x₂ y₁ ℓ =
      -(ℓ * (W.toAffine.addX x₁ x₂ ℓ - x₁) + y₁)
        - W.toAffine.a₁ * (W.toAffine.addX x₁ x₂ ℓ)
        - W.toAffine.a₃ from by
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
      WeierstrassCurve.Affine.negAddY
    ring]
  have hnegAddY : resid P
      (-((addSlopePair α₁ α₂) * (addPullback_x_pair α₁ α₂ - α₁.pullback (x_gen W))
            + α₁.pullback (y_gen W)))
      (-(ℓ * (W.toAffine.addX x₁ x₂ ℓ - x₁) + y₁)) := by
    have := resid_sub (resid_const P (0 : F))
      (resid_add (resid_mul hL (resid_sub hX hx₁)) hy₁)
    rwa [map_zero, zero_sub, zero_sub] at this
  exact resid_sub (resid_sub hnegAddY (resid_mul (resid_a₁ P) hX)) (resid_const P _)

/-- **The addition-formula closed-point specialisation** (`oneSub_coords_at_affine`, the centerpiece;
the analogue of `mulByInt_coords_at_affine`).

For the addition-formula isogeny `addIsog hxy hinj` (the rational map `P ↦ α₁(P) + α₂(P)` with the
explicit Weierstrass-addition comorphism), a smooth point `P` whose summand images are the finite
points `α₁(P) = some x₁ y₁`, `α₂(P) = some x₂ y₂` *in the non-doubling case* `x₁ ≠ x₂`, and the
**per-summand closed-point residue witnesses** `α_i^* x_gen ≡ x_i`, `α_i^* y_gen ≡ y_i` modulo `m_P`:
the addition-formula comorphism coordinates `addPullback_x_pair`, `addPullback_y_pair` are congruent,
modulo `m_P`, to the coordinates `(x, y)` of the image `(addIsog hxy hinj)(P) = α₁(P) + α₂(P)`.

This is the addition-formula replacement for the division-polynomial coordinate specialisation
`[ℓ]P = (φ_ℓ/ψ_ℓ², …)`: the image coordinates come from mathlib's `Affine.Point.add_some`
(`addX`/`addY` of the summand coordinates), and the comorphism coordinates residue to *exactly* those
`addX`/`addY` by the residue toolkit. -/
theorem oneSub_coords_at_affine
    {hxy : AddNonInversePair α₁ α₂} {hinj : Function.Injective (addCoordAlgHomPair hxy)}
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    {x₁ y₁ x₂ y₂ : F} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hα₁ : α₁.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₁ y₁ h₁)
    (hα₂ : α₂.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₂ y₂ h₂)
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁) (hy₂ : resid P (α₂.pullback (y_gen W)) y₂)
    (hx_ne : x₁ ≠ x₂)
    (hQ : (addIsog hxy hinj).toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    resid P (addPullback_x_pair α₁ α₂) x ∧ resid P (addPullback_y_pair α₁ α₂) y := by
  -- The image `(addIsog)(P) = α₁(P) + α₂(P) = some x₁ y₁ + some x₂ y₂`, and by `add_some`
  -- its coordinates are exactly `addX x₁ x₂ (slope ..)`, `addY x₁ x₂ y₁ (slope ..)`.
  have hsum : Affine.Point.some x y h_ns =
      Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ := by
    rw [← hQ, addIsog_toAddMonoidHom]
    show (α₁.toAddMonoidHom + α₂.toAddMonoidHom) P.toAffinePoint = _
    rw [AddMonoidHom.add_apply, hα₁, hα₂]
  -- non-inverse at the closed points: `x₁ ≠ x₂` rules out `x₁ = x₂ ∧ …`.
  have hxy_pts : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun h ↦ hx_ne h.1
  rw [Affine.Point.add_some hxy_pts, Affine.Point.some.injEq] at hsum
  -- `hsum.1 : x = addX x₁ x₂ (slope ..)`, `hsum.2 : y = addY x₁ x₂ y₁ (slope ..)`.
  obtain ⟨hxeq, hyeq⟩ := hsum
  refine ⟨?_, ?_⟩
  · rw [hxeq]
    exact resid_addPullback_x_pair hx₁ hx₂ hy₁ hy₂ hx_ne
  · rw [hyeq]
    exact resid_addPullback_y_pair hx₁ hx₂ hy₁ hy₂ hx_ne

/-! ### Residue matching for `(α₁+α₂)^*` on coordinate-ring elements

The verbatim transcription of `MulByIntSamePlace.lean`'s `pointValuation_mulByInt_pullback_algebraMap_*`
chain with the division coordinate functions replaced by `addPullback_x_pair`, `addPullback_y_pair`.
Throughout we *take as hypotheses* the two coordinate residues `addPullback_x_pair ≡ x`,
`addPullback_y_pair ≡ y` — these are the output of `oneSub_coords_at_affine`, the addition-formula
specialisation — so the chain is uniform in the isogeny and reduces the SamePlace transfer to that
single centerpiece. -/

section Transfer

variable {hxy : AddNonInversePair α₁ α₂} {hinj : Function.Injective (addCoordAlgHomPair hxy)}

/-- `(addIsog).pullback (algebraMap (mk p)) = p(addPullback_x_pair, addPullback_y_pair)` (coefficients
pushed through `algebraMap F K(E)`).  The coordinate-ring comorphism of `addIsog` substitutes the
addition-formula coordinate functions for `(x_gen, y_gen)` — the analogue of
`mulByInt_pullback_algebraMap_mk_eq`. -/
private theorem addIsog_pullback_algebraMap_mk_eq (p : Polynomial (Polynomial F)) :
    (addIsog hxy hinj).pullback
        (algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.mk W.toAffine p)) =
      (p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval
        (addPullback_x_pair α₁ α₂) (addPullback_y_pair α₁ α₂) := by
  rw [addIsog_pullback]
  unfold addPullbackAlgHomPair
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change (addCoordAlgHomPair hxy).toRingHom (Affine.CoordinateRing.mk W.toAffine p) = _
  change addCoordRingHomPair hxy (Affine.CoordinateRing.mk W.toAffine p) = _
  unfold addCoordRingHomPair
  rw [AdjoinRoot.lift_mk]
  change p.eval₂ (Polynomial.eval₂RingHom (algebraMap F KE) (addPullback_x_pair α₁ α₂))
      (addPullback_y_pair α₁ α₂) = _
  rw [Polynomial.eval₂_eval₂RingHom_apply]

/-- **Residue matching for coordinate-ring elements (affine image).** Given the coordinate residues
`addPullback_x_pair ≡ x`, `addPullback_y_pair ≡ y` (the `oneSub_coords_at_affine` output), for any
coordinate-ring element `r`, `(α₁+α₂)^*(algebraMap r) ≡ r(Q)` modulo `m_P`, where `Q = ⟨x, y, h_ns⟩`.
Built from the bivariate value bridge with the two coordinate residues. -/
private theorem pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    (r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        ((addIsog hxy hinj).pullback
            (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) < 1 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [addIsog_pullback_algebraMap_mk_eq p,
    show (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ (Affine.CoordinateRing.mk W.toAffine p)
        = p.evalEval x y from Curves.SmoothPlaneCurve.evalAt_mk _ _ _]
  exact pV_bivariate_bridge P (resid_le_one hx) hx (resid_le_one hy) hy p

/-- **(A) Regularity:** `(α₁+α₂)^*(algebraMap r)` is regular at `P` (affine image). -/
private theorem pV_addIsog_pullback_algebraMap_le_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    (r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        ((addIsog hxy hinj).pullback
          (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) ≤ 1 := by
  rw [show (addIsog hxy hinj).pullback
        (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      ((addIsog hxy hinj).pullback
            (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring]
  exact pointValuation_add_le_one W P
    (le_of_lt (pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one (hxy := hxy) (hinj := hinj)
      P h_ns hx hy r))
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)

/-- **(B′) Unit transfer:** for `r ∉ m_Q`, `(α₁+α₂)^*(algebraMap r)` is a unit at `P`. -/
private theorem pV_addIsog_pullback_algebraMap_eq_one_of_notMem
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    {r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∉ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        ((addIsog hxy hinj).pullback
          (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) = 1 := by
  have hrQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r ≠ 0 := fun h0 ↦
    hr (by rw [← (⟨W.toAffine⟩ : SmoothPlaneCurve F).ker_evalAt ⟨x, y, h_ns⟩]; exact h0)
  have hconst : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hrQ
  rw [show (addIsog hxy hinj).pullback
        (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      ((addIsog hxy hinj).pullback
            (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring,
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]
          exact pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one (hxy := hxy) (hinj := hinj)
            P h_ns hx hy r),
    hconst]

/-- **(B) Vanishing transfer:** for `r ∈ m_Q`, `(α₁+α₂)^*(algebraMap r)` lies in `m_P` (strict). -/
private theorem pV_addIsog_pullback_algebraMap_lt_one_of_mem
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    {r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∈ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        ((addIsog hxy hinj).pullback
          (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) < 1 := by
  have hrQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r = 0 := by
    rw [← RingHom.mem_ker, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ker_evalAt]; exact hr
  have h := pV_addIsog_pullback_algebraMap_sub_evalAt_lt_one (hxy := hxy) (hinj := hinj)
    P h_ns hx hy r
  rwa [hrQ, map_zero, sub_zero] at h

/-- **Forward regularity transfer (≤ 1):** if `g` is regular at the affine image `Q`, so is
`(α₁+α₂)^*g` at `P`.  Verbatim transcription of `pointValuation_mulByInt_pullback_le_one_of_le_one`
via the `IsLocalization.surj` decomposition `g = u/v` with `v ∉ m_Q`. -/
private theorem pV_addIsog_pullback_le_one_of_le_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    {g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) ≤ 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr hg
  haveI : ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W.toAffine⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  have hg_eq : g = algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pV_addIsog_pullback_algebraMap_eq_one_of_notMem (hxy := hxy) (hinj := hinj) P h_ns hx hy
      hv_notMem, div_one]
  exact pV_addIsog_pullback_algebraMap_le_one (hxy := hxy) (hinj := hinj) P h_ns hx hy u

/-- **Forward vanishing transfer (< 1):** if `g ∈ m_Q`, then `(α₁+α₂)^*g ∈ m_P` (strict). -/
private theorem pV_addIsog_pullback_lt_one_of_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    {g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g < 1) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) < 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr (le_of_lt hg)
  haveI : ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W.toAffine⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  have hv_unitQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
      (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _)) = 1 :=
    le_antisymm ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ _)
      (not_lt.mp (fun hlt ↦ hv_notMem
        ((Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F)) _ ⟨x, y, h_ns⟩).mp hlt)))
  have hu_mem : u ∈ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := by
    rw [← Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt]
    have : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
        (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g := by
      rw [← h_lift, map_mul, hv_unitQ, mul_one]
    rw [this]; exact hg
  have hg_eq : g = algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pV_addIsog_pullback_algebraMap_eq_one_of_notMem (hxy := hxy) (hinj := hinj) P h_ns hx hy
      hv_notMem, div_one]
  exact pV_addIsog_pullback_algebraMap_lt_one_of_mem (hxy := hxy) (hinj := hinj) P h_ns hx hy hu_mem

/-! ### The affine SamePlace transfer + `IsEquiv` -/

/-- **Same-place regularity transfer, affine-image case** (the `MulByIntSamePlace` analogue
`mulByInt_samePlace_le_one_iff_affine`).  For the addition-formula isogeny `addIsog hxy hinj` and a
smooth point `P` whose image `(α₁+α₂)(P)` is the finite point `some x y h_ns`, *given* the two
coordinate residues (the `oneSub_coords_at_affine` output), `(α₁+α₂).pullback g` is regular at `P` iff
`g` is regular at `⟨x, y, h_ns⟩`. -/
theorem addIsog_samePlace_le_one_iff_affine
    {hxy : AddNonInversePair α₁ α₂} {hinj : Function.Injective (addCoordAlgHomPair hxy)}
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    (g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) ≤ 1 ↔
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1 := by
  refine ⟨fun hP ↦ ?_,
    pV_addIsog_pullback_le_one_of_le_one (hxy := hxy) (hinj := hinj) P h_ns hx hy⟩
  -- (⟹): contrapositive via `g⁻¹`.
  by_contra hQng
  rw [not_le] at hQng
  have hg_ne : g ≠ 0 := by
    rintro rfl; rw [map_zero] at hQng; exact absurd hQng (not_lt.mpr zero_le)
  have hinvQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g⁻¹ < 1 := by
    rw [map_inv₀]
    exact (inv_lt_one₀ (lt_trans one_pos hQng)).mpr hQng
  have hPinv : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g⁻¹)
      < 1 := pV_addIsog_pullback_lt_one_of_lt_one (hxy := hxy) (hinj := hinj) P h_ns hx hy hinvQ
  have hmul : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) *
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hg_ne, map_one, map_one]
  have hlt1 : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) *
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g⁻¹) < 1 := by
    have hstep : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g) *
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g⁻¹) ≤
        1 * (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P ((addIsog hxy hinj).pullback g⁻¹) := by
      gcongr
    exact lt_of_le_of_lt hstep (by rw [one_mul]; exact hPinv)
  rw [hmul] at hlt1
  exact absurd hlt1 (lt_irrefl 1)

/-- **(SamePlace), affine-image case.** The comap valuation
`(pointValuation P).comap (addIsog).pullback` is `Valuation.IsEquiv` to `pointValuation ⟨x,y,h_ns⟩`
at the affine image `(α₁+α₂)(P) = some x y h_ns`, *given* the two coordinate residues.  Feeds
`comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. -/
theorem addIsog_comap_pointValuation_isEquiv_affine
    {hxy : AddNonInversePair α₁ α₂} {hinj : Function.Injective (addCoordAlgHomPair hxy)}
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y) :
    (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap
        (addIsog hxy hinj).pullback.toRingHom).IsEquiv
      ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩) := by
  apply Valuation.isEquiv_of_val_le_one
  intro g
  rw [Valuation.comap_apply]
  exact addIsog_samePlace_le_one_iff_affine (hxy := hxy) (hinj := hinj) P h_ns hx hy g

/-! ### The assembled affine comap identity (parametric on the `e = 1` uniformizer datum)

The verbatim `comap_pointValuation_mulByInt_eq_affine` assembly: combine the affine SamePlace
`IsEquiv` (proved above, axiom-clean) with the single **`e = 1`** uniformizer datum via the DVR glue
`comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`.  We isolate the `e = 1` datum as an explicit
hypothesis `he1` (the separability / unramifiedness content, Silverman III.4.10c — for `[ℓ]` it was
`ord_P_mulByInt_x_sub_const_eq_one`; for `1 − π` it is the corresponding addition-formula
uniformizer-order fact, the genuinely-deep local residual). -/

/-- **Affine comap identity for `addIsog`, parametric on `e = 1`** — the analogue of
`comap_pointValuation_mulByInt_eq_affine`.  Given the two coordinate residues (the
`oneSub_coords_at_affine` output) **and** the single `e = 1` uniformizer datum `he1`
(`ord_P ((α₁+α₂)^* (x_gen − x_Q)) = 1`, the unramifiedness of the separable isogeny), the comap
valuation `(pointValuation P).comap (α₁+α₂).pullback` equals `pointValuation ⟨x, y, h_ns⟩` outright. -/
theorem comap_pointValuation_addIsog_eq_affine_of_e_eq_one
    {hxy : AddNonInversePair α₁ α₂} {hinj : Function.Injective (addCoordAlgHomPair hxy)}
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (addPullback_x_pair α₁ α₂) x) (hy : resid P (addPullback_y_pair α₁ α₂) y)
    (he1 : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
      ((addIsog hxy hinj).pullback (x_gen W - algebraMap F KE x)) = ((1 : ℤ) : WithTop ℤ)) :
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap
        (addIsog hxy hinj).pullback.toRingHom =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ :=
  Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
    (⟨W.toAffine⟩ : SmoothPlaneCurve F) (addIsog hxy hinj).pullback.toRingHom P
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_surjective' ⟨x, y, h_ns⟩)
    (addIsog_comap_pointValuation_isEquiv_affine (hxy := hxy) (hinj := hinj) P h_ns hx hy) he1

end Transfer

/-! ### The same-place transfer + `e = 1` comap identity for a *general* isogeny

The `addIsog`-keyed transfer above is, at bottom, a fact about the two **generator pullbacks**
`α^*x_gen`, `α^*y_gen` of an isogeny `α` (since `addPullback_x_pair α₁ α₂ = (addIsog).pullback x_gen`,
`addPullbackAlgHomPair_x_gen_eq`).  This section restates it for an **arbitrary** isogeny `α`, keyed
on the two **generator residues** `α^*x_gen ≡ x`, `α^*y_gen ≡ y` modulo `m_P` — the form the
*concrete* base-changed `1 − π` over `K̄` needs (its pullback is opaque, not literally an `addIsog`
comorphism).  The companion `e = 1` datum is assembled from the residue (`ord_P ≥ 1`) and the general
differential bound `ord_P_isog_pullback_x_sub_const_le_one` (`ord_P ≤ 1`), so the final comap identity
carries **no** `he1`. -/

section IsogGeneral

variable {α : Isogeny W.toAffine W.toAffine}

/-- **Closed-point residue production for a general isogeny `α` from an addition decomposition** (the
`oneSub_coords_at_affine` bridge to a non-`addIsog` isogeny).  If `α`'s generator pullbacks coincide
with the addition-formula coordinates `addPullback_x_pair α₁ α₂`, `addPullback_y_pair α₁ α₂` of a pair
`(α₁, α₂)` (`hpb_x`, `hpb_y`) and `α`'s point-map image at `P` is the sum `α₁(P) + α₂(P)` (`hsum_pt`),
then — given the per-summand residues and the non-doubling `x₁ ≠ x₂` — the generator pullbacks of `α`
residue to the image coordinates `x`, `y`.

This is the form needed for the *concrete* base-changed `1 − π` over `K̄` (whose pullback is opaque,
not literally an `addIsog`): supply `hpb_x`/`hpb_y` (= the WallA pullback realisation) and the
per-summand Frobenius residues, and the closed-point residues `(1−π)^*x_gen ≡ x` follow. -/
theorem isog_coords_at_affine_of_decomp {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hpb_x : α.pullback (x_gen W) = addPullback_x_pair α₁ α₂)
    (hpb_y : α.pullback (y_gen W) = addPullback_y_pair α₁ α₂)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    {x₁ y₁ x₂ y₂ : F} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hα₁ : α₁.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₁ y₁ h₁)
    (hα₂ : α₂.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₂ y₂ h₂)
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁) (hy₂ : resid P (α₂.pullback (y_gen W)) y₂)
    (hx_ne : x₁ ≠ x₂)
    (hsum_pt : α.toAddMonoidHom P.toAffinePoint =
      Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂)
    (hQ : α.toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    resid P (α.pullback (x_gen W)) x ∧ resid P (α.pullback (y_gen W)) y := by
  -- `some x y = α(P) = some x₁ y₁ + some x₂ y₂`, so its coords are `addX`/`addY`.
  have hsum : Affine.Point.some x y h_ns =
      Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ := by rw [← hQ, hsum_pt]
  have hxy_pts : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun h ↦ hx_ne h.1
  rw [Affine.Point.add_some hxy_pts, Affine.Point.some.injEq] at hsum
  obtain ⟨hxeq, hyeq⟩ := hsum
  rw [hpb_x, hpb_y]
  refine ⟨?_, ?_⟩
  · rw [hxeq]; exact resid_addPullback_x_pair hx₁ hx₂ hy₁ hy₂ hx_ne
  · rw [hyeq]; exact resid_addPullback_y_pair hx₁ hx₂ hy₁ hy₂ hx_ne

/-- **Closed-point residue production for a general isogeny `α` from an addition decomposition,
slope-parametric (covers the doubling case).**  Identical to `isog_coords_at_affine_of_decomp` but
takes the slope residue `addSlopePair α₁ α₂ ≡ slope x₁ x₂ y₁ y₂` as an explicit hypothesis `hL` and
only the *non-inverse* condition `¬(x₁ = x₂ ∧ y₁ = negY x₂ y₂)` (not `x₁ ≠ x₂`).  This is the form the
*doubling* case `x₁ = x₂` of the concrete base-changed `1 − π` needs, where the `K(E)`-secant
`addSlopePair` residues to the *tangent* slope (supplied via `hL` from the invariant-differential
`L'Hôpital` argument). -/
theorem isog_coords_at_affine_of_decomp_slope {α₁ α₂ : Isogeny W.toAffine W.toAffine}
    (hpb_x : α.pullback (x_gen W) = addPullback_x_pair α₁ α₂)
    (hpb_y : α.pullback (y_gen W) = addPullback_y_pair α₁ α₂)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    {x₁ y₁ x₂ y₂ : F} {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂}
    (hα₁ : α₁.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₁ y₁ h₁)
    (hα₂ : α₂.toAddMonoidHom P.toAffinePoint = Affine.Point.some x₂ y₂ h₂)
    (hx₁ : resid P (α₁.pullback (x_gen W)) x₁) (hx₂ : resid P (α₂.pullback (x_gen W)) x₂)
    (hy₁ : resid P (α₁.pullback (y_gen W)) y₁)
    (hL : resid P (addSlopePair α₁ α₂) (W.toAffine.slope x₁ x₂ y₁ y₂))
    (hxy_pts : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂))
    (hsum_pt : α.toAddMonoidHom P.toAffinePoint =
      Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂)
    (hQ : α.toAddMonoidHom P.toAffinePoint = Affine.Point.some x y h_ns) :
    resid P (α.pullback (x_gen W)) x ∧ resid P (α.pullback (y_gen W)) y := by
  have hsum : Affine.Point.some x y h_ns =
      Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ := by rw [← hQ, hsum_pt]
  rw [Affine.Point.add_some hxy_pts, Affine.Point.some.injEq] at hsum
  obtain ⟨hxeq, hyeq⟩ := hsum
  rw [hpb_x, hpb_y]
  refine ⟨?_, ?_⟩
  · rw [hxeq]; exact resid_addPullback_x_pair_of_slope hx₁ hx₂ hL
  · rw [hyeq]; exact resid_addPullback_y_pair_of_slope hx₁ hx₂ hy₁ hL

/-- **General coordinate-ring comorphism.**  `α.pullback (algebraMap (mk p)) =
(p.map (algebraMap F K(E))).evalEval (α^*x_gen) (α^*y_gen)` — the isogeny-agnostic generalisation of
`addIsog_pullback_algebraMap_mk_eq`.  Proof: `algebraMap (mk p) = (p.map …).evalEval x_gen y_gen`
(`evalEval_xy_gen_eq_algebraMap_mk`), then push `α.pullback` (an `F`-algebra hom, fixing
`algebraMap F`) through `evalEval` via `map_mapRingHom_evalEval`. -/
theorem isog_pullback_algebraMap_mk_eq (p : Polynomial (Polynomial F)) :
    α.pullback (algebraMap W.toAffine.CoordinateRing KE (Affine.CoordinateRing.mk W.toAffine p)) =
      (p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval
        (α.pullback (x_gen W)) (α.pullback (y_gen W)) := by
  rw [← evalEval_xy_gen_eq_algebraMap_mk W p]
  have hqmap : (p.map (Polynomial.mapRingHom (algebraMap F KE))).map
      (Polynomial.mapRingHom (α.pullback : KE →+* KE)) =
      p.map (Polynomial.mapRingHom (algebraMap F KE)) := by
    rw [Polynomial.map_map (Polynomial.mapRingHom (algebraMap F KE))
        (Polynomial.mapRingHom (α.pullback : KE →+* KE)) p,
      Polynomial.mapRingHom_comp,
      show ((α.pullback : KE →+* KE)).comp (algebraMap F KE) = algebraMap F KE from
        α.pullback.comp_algebraMap]
  have key := Polynomial.map_mapRingHom_evalEval (f := (α.pullback : KE →+* KE))
    (p := p.map (Polynomial.mapRingHom (algebraMap F KE))) (x := x_gen W) (y := y_gen W)
  rw [hqmap] at key
  exact key.symm

/-- **Residue matching for coordinate-ring elements** (general isogeny, affine image).  Given the two
generator residues `α^*x_gen ≡ x`, `α^*y_gen ≡ y`, for any coordinate-ring `r`,
`α^*(algebraMap r) ≡ r(Q)` modulo `m_P` with `Q = ⟨x, y, h_ns⟩`.  Built from the bivariate value
bridge with the two generator residues. -/
private theorem pV_isog_pullback_algebraMap_sub_evalAt_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    (r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) < 1 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [isog_pullback_algebraMap_mk_eq p,
    show (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ (Affine.CoordinateRing.mk W.toAffine p)
        = p.evalEval x y from Curves.SmoothPlaneCurve.evalAt_mk _ _ _]
  exact pV_bivariate_bridge P (resid_le_one hx) hx (resid_le_one hy) hy p

/-- **(A) Regularity:** `α^*(algebraMap r)` is regular at `P` (affine image). -/
private theorem pV_isog_pullback_algebraMap_le_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    (r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) ≤ 1 := by
  rw [show α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring]
  exact pointValuation_add_le_one W P
    (le_of_lt (pV_isog_pullback_algebraMap_sub_evalAt_lt_one P h_ns hx hy r))
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_F_le_one P _)

/-- **(B′) Unit transfer:** for `r ∉ m_Q`, `α^*(algebraMap r)` is a unit at `P`. -/
private theorem pV_isog_pullback_algebraMap_eq_one_of_notMem
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    {r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∉ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) = 1 := by
  have hrQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r ≠ 0 := fun h0 ↦
    hr (by rw [← (⟨W.toAffine⟩ : SmoothPlaneCurve F).ker_evalAt ⟨x, y, h_ns⟩]; exact h0)
  have hconst : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
      (algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hrQ
  rw [show α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) =
      (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r) -
          algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r)) +
        algebraMap F KE ((⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r) from by ring,
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).map_add_eq_of_lt_right
      (by rw [hconst]
          exact pV_isog_pullback_algebraMap_sub_evalAt_lt_one P h_ns hx hy r),
    hconst]

/-- **(B) Vanishing transfer:** for `r ∈ m_Q`, `α^*(algebraMap r)` lies in `m_P` (strict). -/
private theorem pV_isog_pullback_algebraMap_lt_one_of_mem
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    {r : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing}
    (hr : r ∈ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P
        (α.pullback (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE r)) < 1 := by
  have hrQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).evalAt ⟨x, y, h_ns⟩ r = 0 := by
    rw [← RingHom.mem_ker, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ker_evalAt]; exact hr
  have h := pV_isog_pullback_algebraMap_sub_evalAt_lt_one P h_ns hx hy r
  rwa [hrQ, map_zero, sub_zero] at h

/-- **Forward regularity transfer (≤ 1):** if `g` is regular at the affine image `Q`, so is
`α^*g` at `P`. -/
private theorem pV_isog_pullback_le_one_of_le_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    {g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) ≤ 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr hg
  haveI : ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W.toAffine⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  have hg_eq : g = algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pV_isog_pullback_algebraMap_eq_one_of_notMem P h_ns hx hy hv_notMem, div_one]
  exact pV_isog_pullback_algebraMap_le_one P h_ns hx hy u

/-- **Forward vanishing transfer (< 1):** if `g ∈ m_Q`, then `α^*g ∈ m_P` (strict). -/
private theorem pV_isog_pullback_lt_one_of_lt_one
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    {g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField}
    (hg : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g < 1) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) < 1 := by
  obtain ⟨x_loc, hx_loc⟩ :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one g).mpr (le_of_lt hg)
  haveI : ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).IsPrime :=
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt_isMaximal ⟨x, y, h_ns⟩).isPrime
  obtain ⟨⟨u, v⟩, hv_eq⟩ := IsLocalization.surj
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩).primeCompl x_loc
  have h_lift : g * algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) =
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u := by
    have h_apply := congrArg
      (algebraMap ((⟨W.toAffine⟩ : SmoothPlaneCurve F).localRingAt ⟨x, y, h_ns⟩) KE) hv_eq
    rw [map_mul, hx_loc] at h_apply
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h_apply
  have hv_notMem : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ∉
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := v.2
  have hv_ne : (v : (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing) ≠ 0 :=
    fun h ↦ hv_notMem (h ▸ Submodule.zero_mem _)
  have h_alg_v_ne : algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE
      (v : _) ≠ 0 := fun h ↦ hv_ne ((IsFractionRing.injective _ _) (h.trans (map_zero _).symm))
  have hv_unitQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
      (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _)) = 1 :=
    le_antisymm ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ _)
      (not_lt.mp (fun hlt ↦ hv_notMem
        ((Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := (⟨W.toAffine⟩ : SmoothPlaneCurve F)) _ ⟨x, y, h_ns⟩).mp hlt)))
  have hu_mem : u ∈ (⟨W.toAffine⟩ : SmoothPlaneCurve F).maximalIdealAt ⟨x, y, h_ns⟩ := by
    rw [← Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt]
    have : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩
        (algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u) =
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g := by
      rw [← h_lift, map_mul, hv_unitQ, mul_one]
    rw [this]; exact hg
  have hg_eq : g = algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE u /
      algebraMap (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing KE (v : _) := by
    rw [eq_div_iff h_alg_v_ne]; exact h_lift
  rw [hg_eq, map_div₀, map_div₀,
    pV_isog_pullback_algebraMap_eq_one_of_notMem P h_ns hx hy hv_notMem, div_one]
  exact pV_isog_pullback_algebraMap_lt_one_of_mem P h_ns hx hy hu_mem

/-- **Same-place regularity transfer (general isogeny, affine image).**  For an isogeny `α` and a
smooth point `P` whose generator pullbacks residue to the image coordinates `α^*x_gen ≡ x`,
`α^*y_gen ≡ y`, `α.pullback g` is regular at `P` iff `g` is regular at `⟨x, y, h_ns⟩`. -/
theorem isog_samePlace_le_one_iff_affine
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    (g : (⟨W.toAffine⟩ : SmoothPlaneCurve F).FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) ≤ 1 ↔
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g ≤ 1 := by
  refine ⟨fun hP ↦ ?_, pV_isog_pullback_le_one_of_le_one P h_ns hx hy⟩
  by_contra hQng
  rw [not_le] at hQng
  have hg_ne : g ≠ 0 := by
    rintro rfl; rw [map_zero] at hQng; exact absurd hQng (not_lt.mpr zero_le)
  have hinvQ : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ g⁻¹ < 1 := by
    rw [map_inv₀]
    exact (inv_lt_one₀ (lt_trans one_pos hQng)).mpr hQng
  have hPinv : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g⁻¹)
      < 1 := pV_isog_pullback_lt_one_of_lt_one P h_ns hx hy hinvQ
  have hmul : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) *
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hg_ne, map_one, map_one]
  have hlt1 : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) *
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g⁻¹) < 1 := by
    have hstep : (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g) *
        (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g⁻¹) ≤
        1 * (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P (α.pullback g⁻¹) := by
      gcongr
    exact lt_of_le_of_lt hstep (by rw [one_mul]; exact hPinv)
  rw [hmul] at hlt1
  exact absurd hlt1 (lt_irrefl 1)

/-- **(SamePlace), general isogeny, affine-image case.** The comap valuation
`(pointValuation P).comap α.pullback` is `Valuation.IsEquiv` to `pointValuation ⟨x,y,h_ns⟩`, given the
two generator residues.  Feeds `comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`. -/
theorem isog_comap_pointValuation_isEquiv_affine
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y) :
    (((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap
        α.pullback.toRingHom).IsEquiv
      ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩) := by
  apply Valuation.isEquiv_of_val_le_one
  intro g
  rw [Valuation.comap_apply]
  exact isog_samePlace_le_one_iff_affine P h_ns hx hy g

/-! #### The general `e = 1` datum and the assembled affine comap identity (no `he1`)

The `e = 1` uniformizer-order fact `ord_P (α^*(x_gen − x_Q)) = 1` is now *derived* (not carried): the
two inequalities come from the residue (`ord_P ≥ 1`, the function vanishes at `P`) and the general
differential bound `ord_P_isog_pullback_x_sub_const_le_one` (`ord_P ≤ 1`, the characteristic-free
unramifiedness from `a_α ≠ 0` and `α^*u` a unit at `P`). -/

/-- **General `e = 1` (x-coordinate).**  For an isogeny `α` with separable invariant-differential
coefficient `a_α = omegaPullbackCoeff W α ≠ 0`, a smooth point `P` whose `x`-coordinate pullback
residues to `x` (`α^*x_gen ≡ x`), and `α^*u = alpha_star_u W α` a unit at `P` (the non-2-torsion-image
condition), the uniformizer pullback `α^*(x_gen − x_Q) = α^*x_gen − x_Q` has order exactly `1` at
`P`. -/
theorem ord_P_isog_pullback_x_sub_const_eq_one
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range) (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x : F}
    (hx : resid P (α.pullback (x_gen W)) x)
    (h_u : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (alpha_star_u W α) = 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
      (α.pullback (x_gen W) - algebraMap F KE x) = ((1 : ℤ) : WithTop ℤ) := by
  -- nonzero: `α^*x_gen − x_Q ≠ 0` since it vanishes at `P` but `α^*x_gen` is transcendental.
  have hf_ne : α.pullback (x_gen W) - algebraMap F KE x ≠ 0 := by
    intro h0
    -- `α^*x_gen = algebraMap x` would force `Dω (α^*x_gen) = 0`, contradicting the unit `α^*u·a_α`.
    have hDω : Dω W (α.pullback (x_gen W)) = alpha_star_u W α * omegaPullbackCoeff W α :=
      Dω_isog_pullback_x_gen W α
    rw [sub_eq_zero] at h0
    rw [h0, Dω_algebraMap] at hDω
    obtain ⟨c, hc⟩ := hcoeff
    have hc_ne : c ≠ 0 := fun h ↦ hcoeff_ne (by rw [h, map_zero] at hc; exact hc.symm)
    have hau_ne : alpha_star_u W α ≠ 0 := by
      intro h
      rw [h, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P_zero] at h_u
      exact (by simp : (⊤ : WithTop ℤ) ≠ 0) h_u
    exact (mul_ne_zero hau_ne hcoeff_ne) hDω.symm
  -- `ord_P ≥ 1` from the residue (the function lies in `m_P`).
  have h_ge : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (x_gen W) - algebraMap F KE x) := by
    have := ((⟨W.toAffine⟩ : SmoothPlaneCurve F).one_le_ord_P_iff_pointValuation_lt_one
      (P := P) hf_ne).mpr hx
    exact_mod_cast this
  -- `ord_P ≤ 1` from the differential bound.
  have h_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
      (α.pullback (x_gen W) - algebraMap F KE x) ≤ ((1 : ℤ) : WithTop ℤ) :=
    ord_P_isog_pullback_x_sub_const_le_one W α hcoeff hcoeff_ne P x hf_ne h_u
  exact le_antisymm h_le h_ge

/-- **The assembled affine comap identity for a general isogeny `α`, with `e = 1` derived (no
`he1`).**  For an isogeny `α` with separable coefficient `a_α ≠ 0`, given the two generator residues
and `α^*u` a unit at `P` (non-2-torsion image), the comap valuation
`(pointValuation P).comap α.pullback` equals `pointValuation ⟨x, y, h_ns⟩` outright.

This is the general form of the `affine` field of `ComapPointValuationWitness`, with the
unramifiedness `e = 1` *proved* from the invariant differential (Silverman III.4.10c / III.5.5), not
carried as a hypothesis. -/
theorem comap_pointValuation_isog_eq_affine
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range) (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    (h_u : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (alpha_star_u W α) = 0) :
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap α.pullback.toRingHom =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ :=
  Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
    (⟨W.toAffine⟩ : SmoothPlaneCurve F) α.pullback.toRingHom P
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_surjective' ⟨x, y, h_ns⟩)
    (isog_comap_pointValuation_isEquiv_affine P h_ns hx hy)
    (t := x_gen W - algebraMap F KE x)
    (by
      have heq : α.pullback.toRingHom (x_gen W - algebraMap F KE x) =
          α.pullback (x_gen W) - algebraMap F KE x := by
        change α.pullback (x_gen W - algebraMap F KE x) = _
        rw [map_sub, α.pullback.commutes]
      rw [heq]
      exact ord_P_isog_pullback_x_sub_const_eq_one hcoeff hcoeff_ne P hx h_u)

/-! #### The `y`-uniformizer comap identity (2-torsion image)

At a **2-torsion image** the differential denominator `α^*u` vanishes at `P`, so the `x`-uniformizer
`x_gen − x` is *not* unramified.  But the `y`-numerator `α^*ν` is then a unit at `P` (the other
partial of the nonsingular Weierstrass equation), so `y_gen − y` is the unramified `y`-uniformizer.
We assemble the comap identity through it, mirroring the `x`-route. -/

/-- **General `e = 1` (y-coordinate).**  For an isogeny `α` with separable coefficient `a_α ≠ 0`, a
smooth point `P` whose `y`-coordinate pullback residues to `y` (`α^*y_gen ≡ y`), and the pulled-back
`y`-numerator `α^*ν = 3(α^*x)²+2a₂(α^*x)+a₄−a₁(α^*y)` a unit at `P` (the 2-torsion-image condition),
the uniformizer pullback `α^*y_gen − y` has order exactly `1` at `P`. -/
theorem ord_P_isog_pullback_y_sub_const_eq_one
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range) (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {y : F}
    (hy : resid P (α.pullback (y_gen W)) y)
    (h_ν : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
        (3 * (α.pullback (x_gen W)) ^ 2 + 2 * algebraMap F KE W.toAffine.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.toAffine.a₄ - algebraMap F KE W.toAffine.a₁ * (α.pullback (y_gen W))) = 0) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
      (α.pullback (y_gen W) - algebraMap F KE y) = ((1 : ℤ) : WithTop ℤ) := by
  -- the `y`-numerator is nonzero (a unit at `P`, `ord_P = 0`).
  have hν_ne : (3 * (α.pullback (x_gen W)) ^ 2 +
      2 * algebraMap F KE W.toAffine.a₂ * (α.pullback (x_gen W)) +
      algebraMap F KE W.toAffine.a₄ - algebraMap F KE W.toAffine.a₁ * (α.pullback (y_gen W))) ≠ 0 := by
    intro h
    rw [h, (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P_zero] at h_ν
    exact (by simp : (⊤ : WithTop ℤ) ≠ 0) h_ν
  -- nonzero: `α^*y_gen − y ≠ 0` since `Dω(α^*y_gen) = α^*ν · a_α ≠ 0` but `Dω(algebraMap y) = 0`.
  have hf_ne : α.pullback (y_gen W) - algebraMap F KE y ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    have hzero : (0 : KE) =
        (3 * (α.pullback (x_gen W)) ^ 2 +
            2 * algebraMap F KE W.toAffine.a₂ * (α.pullback (x_gen W)) +
            algebraMap F KE W.toAffine.a₄ - algebraMap F KE W.toAffine.a₁ * (α.pullback (y_gen W))) *
          omegaPullbackCoeff W α := by
      rw [← Dω_algebraMap (a := y) W, ← h0]; exact Dω_isog_pullback_y_gen W α
    exact (mul_ne_zero hν_ne hcoeff_ne) hzero.symm
  -- `ord_P ≥ 1` from the residue (the function lies in `m_P`).
  have h_ge : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (y_gen W) - algebraMap F KE y) := by
    have := ((⟨W.toAffine⟩ : SmoothPlaneCurve F).one_le_ord_P_iff_pointValuation_lt_one
      (P := P) hf_ne).mpr hy
    exact_mod_cast this
  -- `ord_P ≤ 1` from the y-differential bound.
  have h_le : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
      (α.pullback (y_gen W) - algebraMap F KE y) ≤ ((1 : ℤ) : WithTop ℤ) :=
    ord_P_isog_pullback_y_sub_const_le_one W α hcoeff hcoeff_ne P y hf_ne h_ν
  exact le_antisymm h_le h_ge

/-- **The assembled affine comap identity for a general isogeny `α` via the `y`-uniformizer (2-torsion
image), with `e = 1` derived.**  For an isogeny `α` with separable coefficient `a_α ≠ 0`, given the
two generator residues and the pulled-back `y`-numerator `α^*ν` a unit at `P` (the 2-torsion-image
condition — automatic when `u(α(P)) = 0`), the comap valuation `(pointValuation P).comap α.pullback`
equals `pointValuation ⟨x, y, h_ns⟩` outright.

The `IsEquiv` (same-place) input is *identical* to the `x`-route; only the unramified uniformizer is
swapped from `x_gen − x` to `y_gen − y`. -/
theorem comap_pointValuation_isog_eq_affine_y
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range) (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W.toAffine⟩ : SmoothPlaneCurve F).SmoothPoint) {x y : F}
    (h_ns : W.toAffine.Nonsingular x y)
    (hx : resid P (α.pullback (x_gen W)) x) (hy : resid P (α.pullback (y_gen W)) y)
    (h_ν : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ord_P P
        (3 * (α.pullback (x_gen W)) ^ 2 + 2 * algebraMap F KE W.toAffine.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.toAffine.a₄ - algebraMap F KE W.toAffine.a₁ * (α.pullback (y_gen W))) = 0) :
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation P).comap α.pullback.toRingHom =
      (⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩ :=
  Curves.SmoothPlaneCurve.comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
    (⟨W.toAffine⟩ : SmoothPlaneCurve F) α.pullback.toRingHom P
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h_ns⟩)
    ((⟨W.toAffine⟩ : SmoothPlaneCurve F).pointValuation_surjective' ⟨x, y, h_ns⟩)
    (isog_comap_pointValuation_isEquiv_affine P h_ns hx hy)
    (t := y_gen W - algebraMap F KE y)
    (by
      have heq : α.pullback.toRingHom (y_gen W - algebraMap F KE y) =
          α.pullback (y_gen W) - algebraMap F KE y := by
        change α.pullback (y_gen W - algebraMap F KE y) = _
        rw [map_sub, α.pullback.commutes]
      rw [heq]
      exact ord_P_isog_pullback_y_sub_const_eq_one hcoeff hcoeff_ne P hy h_ν)

end IsogGeneral

end HasseWeil
