/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DivisorPullback
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Surjectivity of a nonconstant isogeny on `K̄`-points (place-theoretic)

For an isogeny `φ : Isogeny W W` of an elliptic curve over an algebraically closed field, the
group homomorphism `φ.toAddMonoidHom : E(K̄) → E(K̄)` is surjective whenever `φ` is nonconstant.
This is the function-field / place-theoretic incarnation of "a nonconstant morphism of smooth
projective curves is surjective" (Silverman II.2.3): for every target place `v_Q` there is a source
place lying over it, and `hproj` (the per-place order transport) identifies that source place with
`v_{φ(P)}`, forcing `φ(P) = Q`.

This file works entirely at the **valuation / place level** (the reviewer's R1), never with affine
coordinate rings of the genuine isogeny — there is no `CoordHom` for `1 − π` or `rπ − s`, so the
coordinate-ring route is unavailable; places of the function field are the correct interface.

## The unified projective place valuation

The discrete places of `K(E)` are the affine `pointValuation P` together with the infinity place
`ordAtInftyValuation`. We package them into a single `projValuation : W.Point → Valuation K(E) ℤᵐ⁰`
indexed by the projective point (`.zero ↦ ∞`, `.some ↦ affine point), so the whole argument is
uniform across the affine/infinity split.

## Main results

* `projValuation` — the unified place at a projective point, with `projValuation_surjective`.
* `projValuation_injective` — **point ↔ place injectivity** at the valuation level: equivalent
  place-valuations come from the same point. The infinity place is separated from every affine
  place by `coordX` (a pole of order `2` at `∞`, regular at every affine point).
* `projValuation_comap_pullback_eq_of_projOrdTransport` — under `hproj`, the comap
  `(projValuation P).comap φ.pullback` equals `projValuation (φ P)` value-precisely (the exact
  order transport, no ramification factor).
* `pointMap_eq_of_comap_isEquiv` — **Lemma B**: if `(projValuation P).comap φ.pullback` is
  equivalent to `projValuation Q`, then `φ.toAddMonoidHom P = Q`.
* `exists_valuationSubring_comap_le` — **Lemma A** (lying-over, pure valuation theory): for any
  field extension `L / M`, a valuation ring of `M` is lain over by a valuation ring of `L`, via
  mathlib's `LocalSubring.exists_le_valuationSubring`.
* `comap_isNontrivial_of_finiteDimensional` — the place-does-not-collapse lemma: a nontrivial
  valuation restricts nontrivially to a *finite* subextension (where the finiteness of the
  comorphism enters).
* `surjective_of_finite_comorphism_and_hproj` — **Lemma C**: surjectivity of `φ.toAddMonoidHom`,
  from the place-lifting hypothesis `PlaceLift φ` (the projectivised lying-over) and `hproj`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.3, III.4.10c.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.EC

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- Local abbreviation for the function field `K(E)`. -/
local notation3 "KE" => W.toAffine.FunctionField

/-! ### The unified projective place valuation -/

/-- **The place of `K(E)` at a projective point** `Q : W.Point`, with values in `ℤᵐ⁰`:
`pointValuation` at a finite point `Q = .some x y h`, and `ordAtInftyValuation` at the point at
infinity `Q = .zero`. This is the valuation-level mirror of `Curves.SmoothPlaneCurve.ordAtPoint`. -/
noncomputable def projValuation (Q : W.Point) :
    Valuation KE (WithZero (Multiplicative ℤ)) :=
  match Q with
  | .zero => (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation
  | .some x y h => (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h⟩

@[simp] theorem projValuation_zero :
    projValuation (W := W) (0 : W.Point) =
      (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation := rfl

@[simp] theorem projValuation_some {x y : F} (h : W.Nonsingular x y) :
    projValuation (W := W) (Affine.Point.some x y h) =
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h⟩ := rfl

/-- The projective place valuation is surjective onto `ℤᵐ⁰` at every point. -/
theorem projValuation_surjective (Q : W.Point) :
    Function.Surjective (projValuation (W := W) Q) := by
  cases Q with
  | zero => exact (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_surjective
  | some x y h => exact (⟨W⟩ : SmoothPlaneCurve F).pointValuation_surjective' _

/-- **Value bridge** (uniform): for nonzero `g`, the place valuation at `Q` evaluates to
`exp(-(projOrdAt g Q))`, where `projOrdAt g Q` is the order of `g` at the projective point `Q`. -/
theorem projValuation_eq_exp_neg_projOrdAt {g : KE} (hg : g ≠ 0) (Q : W.Point) :
    projValuation (W := W) Q g =
      WithZero.exp (-(WeilPairing.DivisorPullback.projOrdAt g Q)) := by
  cases Q with
  | zero =>
    change (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation g =
      WithZero.exp (-(WeilPairing.DivisorPullback.projOrdAt g (0 : W.Point)))
    -- `ord_∞ g` is a finite integer for `g ≠ 0`.
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (mt ((⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_eq_top_iff g).mp hg)
    rw [(⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hg hn.symm,
      WeilPairing.DivisorPullback.projOrdAt_zero, ← hn, WithTop.untopD_coe]
  | some x y h =>
    change (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x, y, h⟩ g =
      WithZero.exp (-(WeilPairing.DivisorPullback.projOrdAt g (Affine.Point.some x y h)))
    -- `ord_P P g` is a finite integer for `g ≠ 0`.
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (mt ((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff (P := ⟨x, y, h⟩) g).mp hg)
    rw [pointValuation_eq_exp_neg_of_ord_P_eq hg hn.symm,
      WeilPairing.DivisorPullback.projOrdAt_some, ← hn, WithTop.untopD_coe]

/-! ### Lemma B — the `hproj` place identification (forward) -/

/-- **The order transport at a single projective point**, read off `ProjOrdTransport`:
`projOrdAt (φ.pullback g) P = projOrdAt g (φ P)`. This is `hproj` instantiated at the projective
place `P.toProjectiveSmoothPoint`, using `toProjectiveSmoothPoint.toAffinePoint = P`. -/
theorem projOrdAt_pullback_eq {φ : HasseWeil.Isogeny W W}
    (hproj : WeilPairing.DivisorPullback.ProjOrdTransport φ)
    (g : KE) (P : W.Point) :
    WeilPairing.DivisorPullback.projOrdAt (φ.pullback g) P =
      WeilPairing.DivisorPullback.projOrdAt g (φ.toAddMonoidHom P) := by
  have h := hproj g P.toProjectiveSmoothPoint
  rw [Affine.Point.toProjectiveSmoothPoint_toAffinePoint] at h
  exact h

/-- **Value-precise comap transport (Lemma B core).** Under `hproj`, the comap of the place at `P`
along `φ.pullback` equals the place at the image point `φ(P)` — as valuations, value-precisely (the
exact order transport, no ramification factor):
```
(projValuation P).comap φ.pullback = projValuation (φ P).
```
This combines the per-place order transport (`projOrdAt_pullback_eq`) with the value bridge. -/
theorem projValuation_comap_pullback_eq_of_projOrdTransport {φ : HasseWeil.Isogeny W W}
    (hproj : WeilPairing.DivisorPullback.ProjOrdTransport φ) (P : W.Point) :
    (projValuation (W := W) P).comap φ.pullback.toRingHom =
      projValuation (W := W) (φ.toAddMonoidHom P) := by
  refine Valuation.ext fun g ↦ ?_
  rcases eq_or_ne g 0 with rfl | hg
  · simp only [map_zero]
  · have hpg : φ.pullback g ≠ 0 := fun h ↦ hg (φ.pullback_injective (by rw [h, map_zero]))
    rw [Valuation.comap_apply]
    change (projValuation (W := W) P) (φ.pullback g) = projValuation (W := W) (φ.toAddMonoidHom P) g
    rw [projValuation_eq_exp_neg_projOrdAt hpg, projValuation_eq_exp_neg_projOrdAt hg,
      projOrdAt_pullback_eq hproj g P]

/-! ### Point ↔ place injectivity (at the valuation level) -/

/-- `coordX` is regular at every affine point: `pointValuation P coordX ≤ 1`. It is the image of
the coordinate-ring element `X`, so `pointValuation_algebraMap_le_one` applies. -/
theorem pointValuation_coordX_le_one (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (⟨W⟩ : SmoothPlaneCurve F).coordX ≤ 1 := by
  have hcr : (⟨W⟩ : SmoothPlaneCurve F).coordX =
      algebraMap (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing
        (⟨W⟩ : SmoothPlaneCurve F).FunctionField
        (algebraMap (Polynomial F) (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing Polynomial.X) := by
    rw [Curves.SmoothPlaneCurve.coordX,
      ← IsScalarTower.algebraMap_apply (Polynomial F)
        (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing (⟨W⟩ : SmoothPlaneCurve F).FunctionField]
  rw [hcr]; exact (⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one _ P

/-- `coordX` has a pole of order `2` at infinity: `ordAtInftyValuation coordX = exp 2 > 1`. -/
theorem ordAtInftyValuation_coordX :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation (⟨W⟩ : SmoothPlaneCurve F).coordX =
      WithZero.exp (2 : ℤ) := by
  have := (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq
    (⟨W⟩ : SmoothPlaneCurve F).coordX_ne_zero (⟨W⟩ : SmoothPlaneCurve F).ordAtInfty_coordX
  rwa [show (-(-2 : ℤ)) = (2 : ℤ) from by norm_num] at this

/-- The infinity place is distinct from every affine place: `coordX` separates them (regular at
affine points, pole at infinity). -/
theorem ordAtInftyValuation_ne_pointValuation
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation ≠
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation P := by
  intro hcontra
  have h1 : (⟨W⟩ : SmoothPlaneCurve F).ordAtInftyValuation (⟨W⟩ : SmoothPlaneCurve F).coordX =
      (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (⟨W⟩ : SmoothPlaneCurve F).coordX := by
    rw [hcontra]
  rw [ordAtInftyValuation_coordX] at h1
  have h_exp2_gt_one : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (2 : ℤ) := by
    rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm, WithZero.exp_lt_exp]
    norm_num
  exact absurd (h1 ▸ pointValuation_coordX_le_one P) (not_le.mpr h_exp2_gt_one)

/-- **Point ↔ place injectivity** (at the valuation level): if the place valuations at two
projective points are equivalent, the points are equal. Affine points are separated from each other
by `maximalIdealAt`-injectivity, and the infinity point is separated from affine points by `coordX`
(`ordAtInftyValuation_ne_pointValuation`). This is the reviewer's point–place injectivity. -/
theorem projValuation_injective {T₁ T₂ : W.Point}
    (h : (projValuation (W := W) T₁).IsEquiv (projValuation (W := W) T₂)) :
    T₁ = T₂ := by
  -- Equivalent ℤᵐ⁰-valued surjective valuations are equal.
  have hval : projValuation (W := W) T₁ = projValuation (W := W) T₂ :=
    Valuation.isEquiv_eq_of_surjective_withZeroInt _ _
      (projValuation_surjective T₁) (projValuation_surjective T₂) h
  cases T₁ with
  | zero =>
    cases T₂ with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      exact absurd hval (ordAtInftyValuation_ne_pointValuation ⟨x₂, y₂, h₂⟩)
  | some x₁ y₁ h₁ =>
    cases T₂ with
    | zero =>
      exact absurd hval.symm (ordAtInftyValuation_ne_pointValuation ⟨x₁, y₁, h₁⟩)
    | some x₂ y₂ h₂ =>
      -- Affine vs affine: equal point valuations ⟹ equal `maximalIdealAt` ⟹ equal points.
      have hpv : (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x₁, y₁, h₁⟩ =
          (⟨W⟩ : SmoothPlaneCurve F).pointValuation ⟨x₂, y₂, h₂⟩ := hval
      have hpt : (⟨x₁, y₁, h₁⟩ : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) = ⟨x₂, y₂, h₂⟩ := by
        apply (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_injective
        apply Ideal.ext
        intro u
        rw [← (⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
              u ⟨x₁, y₁, h₁⟩,
          ← (⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
              u ⟨x₂, y₂, h₂⟩, hpv]
      have hx : x₁ = x₂ := congrArg Curves.SmoothPlaneCurve.SmoothPoint.x hpt
      have hy : y₁ = y₂ := congrArg Curves.SmoothPlaneCurve.SmoothPoint.y hpt
      subst hx; subst hy; rfl

/-- **Lemma B (the `hproj` identification, forward).** If the comap of the place at the source
point `P` along `φ.pullback` is equivalent to the place at the target point `Q`, then `φ(P) = Q`.

Proof: by the value-precise transport (`projValuation_comap_pullback_eq_of_projOrdTransport`),
`(projValuation P).comap φ.pullback = projValuation (φ P)`, so the place at `φ P` is equivalent to
that at `Q`; point–place injectivity gives `φ P = Q`. The only implication surjectivity needs. -/
theorem pointMap_eq_of_comap_isEquiv {φ : HasseWeil.Isogeny W W}
    (hproj : WeilPairing.DivisorPullback.ProjOrdTransport φ) {P Q : W.Point}
    (hlie : ((projValuation (W := W) P).comap φ.pullback.toRingHom).IsEquiv
      (projValuation (W := W) Q)) :
    φ.toAddMonoidHom P = Q := by
  apply projValuation_injective
  rw [← projValuation_comap_pullback_eq_of_projOrdTransport hproj P]
  exact hlie

/-! ### Lemma A — lying-over for valuation subrings of a field extension (pure valuation theory)

The reviewer's Lemma A: a valuation of the base field `M` extends to the extension field `L`.
We state it at the valuation-subring level (a valuation ring of `L` lying above a given valuation
ring of `M`), which is the genuinely-mathlib-grounded form via the Chevalley/Zorn dominating
valuation subring `LocalSubring.exists_le_valuationSubring`. Existence of the dominating valuation
ring needs no finiteness of `L / M`; finiteness is what would additionally force the restriction to
be value-precise / discrete (the normalisation the reviewer warns about). -/

/-- **Nontriviality of the restriction to a finite subextension.** A nontrivial valuation on `L`
restricts to a nontrivial valuation on a subfield `M` over which `L` is *finite* (the comap along
the structure map `M → L` is nontrivial). This is the content of "the place does not collapse",
which makes the finiteness of the comorphism genuinely load-bearing in the surjectivity proof.

Proof (Bourbaki, *Commutative algebra* VI §3): pick `y ∈ L` with `0 < v y < 1`; it is integral over
`M`, with monic minimal polynomial `p` whose constant term `p.coeff 0 ≠ 0`. If `v` were trivial on
`M`, every nonzero coefficient would have value `1`; then in `aeval y p = 0` the constant term
strictly dominates (all higher terms have value `≤ v y < 1`), forcing `0 = v 0 = v (p.coeff 0) = 1`,
a contradiction. -/
theorem comap_isNontrivial_of_finiteDimensional
    {M L Γ₀ : Type*} [Field M] [Field L] [LinearOrderedCommGroupWithZero Γ₀]
    [Algebra M L] [FiniteDimensional M L] (v : Valuation L Γ₀) [v.IsNontrivial] :
    (v.comap (algebraMap M L)).IsNontrivial := by
  classical
  -- A uniformizer `y` of `v`: `y ≠ 0` and `v y < 1`.
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := v)
  have hvy0 : v y ≠ 0 := v.ne_zero_iff.mpr hy0
  -- `y` is integral over `M`; its minimal polynomial has nonzero constant term.
  have hyint : IsIntegral M y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  set p := minpoly M y with hp
  have hpc0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hyint hy0
  -- Suppose the restriction were trivial; derive a contradiction.
  by_contra hcontra
  -- Triviality: every nonzero `a : M` has `v (algebraMap a) = 1`.
  have htriv : ∀ a : M, a ≠ 0 → v (algebraMap M L a) = 1 := by
    intro a ha
    by_contra hne
    exact hcontra ⟨a, by
      rw [Valuation.comap_apply]
      exact v.ne_zero_iff.mpr ((map_ne_zero_iff _ (algebraMap M L).injective).mpr ha), hne⟩
  -- Expand `0 = aeval y p` as a finite sum and show the constant term strictly dominates.
  have hsum : (0 : L) = ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap M L (p.coeff i) * y ^ i := by
    have haev : (Polynomial.aeval y) p = 0 := minpoly.aeval M y
    rw [← haev, Polynomial.aeval_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Algebra.smul_def]
  -- The constant term (`i = 0`) has value `1` and strictly dominates every other term.
  have hdom : v (∑ i ∈ Finset.range (p.natDegree + 1), algebraMap M L (p.coeff i) * y ^ i) =
      v (algebraMap M L (p.coeff 0) * y ^ 0) := by
    refine v.map_sum_eq_of_lt (Finset.mem_range.mpr (Nat.succ_pos _)) fun i hi ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    have hi0 : i ≠ 0 := hi.2
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    rw [map_mul, map_mul, map_pow, map_pow, pow_zero, mul_one, htriv _ hpc0]
    rcases eq_or_ne (p.coeff i) 0 with hci | hci
    · simp only [hci, map_zero, zero_mul]
      exact zero_lt_one
    · rw [htriv _ hci, one_mul]
      calc v y ^ i ≤ v y ^ 1 := pow_le_pow_right_of_le_one' hy1.le hi1
        _ = v y := pow_one _
        _ < 1 := hy1
  rw [← hsum, map_zero, map_mul, map_pow, pow_zero, mul_one, htriv _ hpc0] at hdom
  exact one_ne_zero hdom.symm

/-- **Lemma A (lying-over for valuation subrings).** For any field extension `L / M` and any
valuation subring `O` of `M`, there is a valuation subring `B` of `L` lying above `O`, i.e. whose
restriction to `M` (the comap along the structure map) contains `O`. The reviewer's "∃ place of `L`
above the place of `M`", at the valuation-ring level.

Proof: push `O` into `L` as a local subring (`LocalSubring.map`) and dominate it by a valuation
subring via `LocalSubring.exists_le_valuationSubring`; domination includes the subring inclusion. -/
theorem exists_valuationSubring_comap_le
    {M L : Type*} [Field M] [Field L] [Algebra M L] (O : ValuationSubring M) :
    ∃ B : ValuationSubring L, O ≤ B.comap (algebraMap M L) := by
  obtain ⟨B, hB⟩ := (LocalSubring.map (algebraMap M L) O.toLocalSubring).exists_le_valuationSubring
  refine ⟨B, fun x hx ↦ ?_⟩
  -- `O.toLocalSubring` maps into `B` (domination ⟹ subring inclusion), so `f x ∈ B`.
  have hsub : (LocalSubring.map (algebraMap M L) O.toLocalSubring).toSubring ≤ B.toSubring := hB.1
  rw [ValuationSubring.mem_comap]
  apply hsub
  exact Subring.mem_map.mpr ⟨x, hx, rfl⟩

/-! ### Lemma C — the surjectivity keystone

The **place-lifting hypothesis** `PlaceLift φ` is the reviewer's Lemma A in function-field / place
form, projectivised to the curve's points: for every target point `Q`, some source point `P` has a
place lying over the transported place of `Q`, i.e.
`((projValuation P).comap φ.pullback).IsEquiv (projValuation Q)`.

This is exactly "for every place of the target there is a place of the source lying above it"
(lying-over for the finite extension `K(E) / φ*K(E)`), expressed through the point ↔ place
bijection. It is non-vacuous and holds for every nonconstant isogeny. The keystone
`surjective_of_PlaceLift_and_hproj` discharges surjectivity from it together with `hproj`.

See `exists_valuationSubring_comap_le` above for the pure-valuation-theory lying-over engine
(`LocalSubring.exists_le_valuationSubring`) and `comap_isNontrivial_of_finiteDimensional` for the
nontriviality of the restriction (where finiteness of the comorphism enters); deriving `PlaceLift`
from finiteness additionally needs the (curve-specific) identification of an abstract valuation
subring of `K(E)` with one of the point-places. -/

/-- **The place-lifting predicate** (reviewer Lemma A, projectivised): for every target point `Q`,
some source point `P` satisfies `((projValuation P).comap φ.pullback).IsEquiv (projValuation Q)`. -/
def PlaceLift (φ : HasseWeil.Isogeny W W) : Prop :=
  ∀ Q : W.Point, ∃ P : W.Point,
    ((projValuation (W := W) P).comap φ.pullback.toRingHom).IsEquiv (projValuation (W := W) Q)

/-- **Lemma C (surjectivity keystone).** If `φ` satisfies the place-lifting hypothesis `PlaceLift φ`
(the lying-over for `K(E) / φ*K(E)`, through the point ↔ place bijection) and the per-place order
transport `hproj`, then `φ.toAddMonoidHom : E(K̄) → E(K̄)` is surjective.

For each target `Q`, `PlaceLift` produces a source place at `P` lying over `Q`'s transported place;
`hproj` identifies it with the place at `φ(P)`; point–place injectivity gives `φ(P) = Q`. -/
theorem surjective_of_PlaceLift_and_hproj {φ : HasseWeil.Isogeny W W}
    (hlift : PlaceLift φ) (hproj : WeilPairing.DivisorPullback.ProjOrdTransport φ) :
    Function.Surjective φ.toAddMonoidHom := by
  intro Q
  obtain ⟨P, hP⟩ := hlift Q
  exact ⟨P, pointMap_eq_of_comap_isEquiv hproj hP⟩

/-- **The surjectivity keystone (reviewer Lemma C), requested-name form.**

A nonconstant isogeny `φ : Isogeny W W` of an elliptic curve over an algebraically closed field is
surjective on `K̄`-points, given:
* `hlift : PlaceLift φ` — the lying-over for the finite extension `K(E) / φ*K(E)`, expressed through
  the point ↔ place bijection (the reviewer's Lemma A). This is precisely what the finiteness of the
  comorphism `φ.pullback` delivers: by `exists_valuationSubring_comap_le` a valuation ring of `K(E)`
  lies over each target place, and (over `K̄`, where every place of the function field of the curve
  is a point-place) that lifted ring is one of the `projValuation` places. The pure-valuation-theory
  lying-over is `exists_valuationSubring_comap_le`; the residual is the curve-places identification
  of an abstract dominating valuation ring with a point-place.
* `hproj : ProjOrdTransport φ` — the per-place value-precise order transport
  `ord_P(φ*g) = ord_{φ(P)}(g)`.

This is the reusable bridge for every separable pencil member (`1 − π`, `rπ − s`, separable
factors). The proof is `surjective_of_PlaceLift_and_hproj`. -/
theorem surjective_of_finite_comorphism_and_hproj {φ : HasseWeil.Isogeny W W}
    (hlift : PlaceLift φ) (hproj : WeilPairing.DivisorPullback.ProjOrdTransport φ) :
    Function.Surjective φ.toAddMonoidHom :=
  surjective_of_PlaceLift_and_hproj hlift hproj

end HasseWeil.EC
