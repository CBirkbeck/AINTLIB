/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.SeparableWitnesses
import HasseWeil.EC.IsogenyAG.DualGalois
import HasseWeil.Curves.GenericFiber

/-!
# The generic-point covariance `hgcomm` for a general isogeny (evaluation + separation)

This file closes the project's deepest *general* dual-side residual: the generic-point
commutation leaf

  `hgcomm : Point.map τ_S (g P_gen) = g P_gen + lift (β S)`   (`MapTranslateGenericPoint`),

for a **general** `Basic.Isogeny β` with the **canonical** geometric action
`g = Affine.Point.map β.pullback`, over an algebraically closed base.  Until now this leaf was
discharged only case-by-case (`[m]` via division polynomials, Frobenius via `q`-power
arithmetic); here it is proved from one precisely-scoped per-isogeny witness.

## The engine (`mapTranslateGenericPoint_of_pullbackEvaluation`)

The single irreducible input is the **cofinite pullback-evaluation witness**
(`PullbackEvaluation β bad`, `bad` finite): at every smooth point `P ∉ bad`, the stored point
map sends `P` to a *finite* point `(x', y')` and the pulled-back generators evaluate there,

  `(β^* x_gen)(P) = x' = x(β P)`,  `(β^* y_gen)(P) = y' = y(β P)`,

evaluation being the project's valuation idiom `v_P(f − c) < 1` (`EvaluatesTo`).  This is
exactly the statement "the stored `toAddMonoidHom` is the geometric realization of the stored
`pullback` at all but finitely many points" — the function-field ↔ point-map coherence that the
abstract two-independent-fields `Isogeny` interface cannot see.  Given it, the covariance is
**derived for every `S`** (not just kernel points) by the closed-point separation argument:

* `τ_S(β^* x_gen)` evaluates at `P` to `x(β(P + S))` — translation moves the evaluation point
  (`translate_ord_eq_all_nonzero`) and the witness evaluates at `P + S`;
* the explicit group-law coordinate `addX(β^* x_gen, x_T, slope)` of `g P_gen + lift (β S)`
  evaluates at `P` to `addX(x(βP), x_T, slope_F) = x(βP + βS)` — by `EvaluatesTo` arithmetic
  plus the *same* mathlib `add_some` formula over `F`;
* `x(β(P + S)) = x(βP + βS)` because the stored map is an `AddMonoidHom` — for the abstract
  interface the group-law content of Silverman III.4.8 lives in the bundling of
  `toAddMonoidHom`, so no further input is needed;
* two functions of `K(E)` agreeing at the (cofinitely many) good points are equal: a nonzero
  function has finitely many zeros (`finite_setOf_ord_P_nonzero`, Silverman II.1.2) while
  `E(F)` is infinite over `F = F̄` (`smoothPoint_infinite`).

The finitely many excluded points are: `bad`, the translate `P = −S`, points with
`P + S ∈ bad`, and the fibres of the stored map over `{βS, −βS}` (fibres are finite because
the witness forces the affine kernel into `bad`).

## The CoordHom discharge (`pullbackEvaluation_of_coordHom`)

For an `EC.Isogeny φ` with a coordinate-ring witness `cd : CoordHom` whose pullback and point
map agree with `β`'s, the witness holds with `bad = ∅`: `β^* x_gen = algebraMap (cd.toAlgHom X)`
(`cd.compat`) and the residue map at `P` sends `cd.toAlgHom X` to `x(toPointMap cd P)`
(`evalAt_toPointMap`), so the generator evaluations are exact, with no excluded points.  Note a
`CoordHom` forces the point map to send affine points to affine points (so `ker β = 0` in any
*consistent* instance); isogenies with nontrivial affine kernel must instead discharge
`PullbackEvaluation` with a nonempty `bad` (the kernel) from their residue computations — the
witness shape is chosen so the `1 − π` / `rπ − s` SamePlace machinery can feed it.

## Wiring

`xy_family_of_pullbackEvaluation` / `xy_family_of_coordHom` feed the discharged `hgcomm` into
`xy_family_of_genericPointCommutes` (`EC/IsogenyAG/DualGalois.lean`), the input of the dual
witness's Galois fixed-field data.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1.2, II.2.4(c), III.4.8, III.8.2.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

-- the `EvaluatesTo` block does not consume `[DecidableEq F]` or `W`'s instances in
-- types or proofs; the section variables are kept uniform for the engine below
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-! ### The evaluation relation `EvaluatesTo` and its arithmetic

`EvaluatesTo W P f c` says the rational function `f ∈ K(E)` takes the value `c ∈ F` at the
smooth point `P`, in the project's valuation idiom: `v_P(f − c) < 1` (i.e. `f − c` vanishes at
`P`).  This sidesteps partial evaluation maps entirely; the lemmas below make the relation
compatible with the field operations, which is all the group-law formulas need. -/

/-- `f ∈ K(E)` **evaluates to** `c ∈ F` at the smooth point `P`: `v_P(f − c) < 1`. -/
def EvaluatesTo (P : (W_smooth W).SmoothPoint) (f : KE) (c : F) : Prop :=
  (W_smooth W).pointValuation P (f - algebraMap F KE c) < 1

variable {W}

/-- Constants evaluate to themselves. -/
theorem evaluatesTo_algebraMap (P : (W_smooth W).SmoothPoint) (c : F) :
    EvaluatesTo W P (algebraMap F KE c) c := by
  unfold EvaluatesTo
  rw [sub_self]
  exact (Valuation.map_zero _).trans_lt zero_lt_one

/-- A function with a value at `P` is regular at `P`: `v_P f ≤ 1`. -/
theorem EvaluatesTo.pointValuation_le_one {P : (W_smooth W).SmoothPoint} {f : KE} {c : F}
    (h : EvaluatesTo W P f c) : (W_smooth W).pointValuation P f ≤ 1 := by
  have hf : f = (f - algebraMap F KE c) + algebraMap F KE c := by abel
  calc (W_smooth W).pointValuation P f
      = (W_smooth W).pointValuation P ((f - algebraMap F KE c) + algebraMap F KE c) := by
        rw [← hf]
    _ ≤ max ((W_smooth W).pointValuation P (f - algebraMap F KE c))
        ((W_smooth W).pointValuation P (algebraMap F KE c)) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le h.le ((W_smooth W).pointValuation_algebraMap_F_le_one P c)

/-- The value at `P` is unique. -/
theorem EvaluatesTo.unique {P : (W_smooth W).SmoothPoint} {f : KE} {c c' : F}
    (h : EvaluatesTo W P f c) (h' : EvaluatesTo W P f c') : c = c' := by
  by_contra hne
  have hsub : algebraMap F KE (c' - c) =
      (f - algebraMap F KE c) - (f - algebraMap F KE c') := by
    rw [map_sub]; abel
  have hlt : (W_smooth W).pointValuation P (algebraMap F KE (c' - c)) < 1 := by
    rw [hsub]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h')
  rw [pointValuation_algebraMap_F_eq_one_of_ne_zero W P (sub_ne_zero_of_ne (Ne.symm hne))]
    at hlt
  exact absurd hlt (lt_irrefl 1)

/-- Evaluation is additive. -/
theorem EvaluatesTo.add {P : (W_smooth W).SmoothPoint} {f g : KE} {c d : F}
    (hf : EvaluatesTo W P f c) (hg : EvaluatesTo W P g d) :
    EvaluatesTo W P (f + g) (c + d) := by
  have hrw : f + g - algebraMap F KE (c + d) =
      (f - algebraMap F KE c) + (g - algebraMap F KE d) := by
    rw [map_add]; abel
  unfold EvaluatesTo
  rw [hrw]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hf hg)

/-- Evaluation respects negation. -/
theorem EvaluatesTo.neg {P : (W_smooth W).SmoothPoint} {f : KE} {c : F}
    (hf : EvaluatesTo W P f c) : EvaluatesTo W P (-f) (-c) := by
  have hrw : -f - algebraMap F KE (-c) = -(f - algebraMap F KE c) := by
    rw [map_neg]; abel
  unfold EvaluatesTo
  rw [hrw]
  exact (Valuation.map_neg _ _).trans_lt hf

/-- Evaluation respects subtraction. -/
theorem EvaluatesTo.sub {P : (W_smooth W).SmoothPoint} {f g : KE} {c d : F}
    (hf : EvaluatesTo W P f c) (hg : EvaluatesTo W P g d) :
    EvaluatesTo W P (f - g) (c - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact hf.add hg.neg

/-- Evaluation is multiplicative. -/
theorem EvaluatesTo.mul {P : (W_smooth W).SmoothPoint} {f g : KE} {c d : F}
    (hf : EvaluatesTo W P f c) (hg : EvaluatesTo W P g d) :
    EvaluatesTo W P (f * g) (c * d) := by
  have hrw : f * g - algebraMap F KE (c * d) =
      f * (g - algebraMap F KE d) + (f - algebraMap F KE c) * algebraMap F KE d := by
    rw [map_mul]; ring
  unfold EvaluatesTo
  rw [hrw]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · calc (W_smooth W).pointValuation P (f * (g - algebraMap F KE d))
        = (W_smooth W).pointValuation P f *
          (W_smooth W).pointValuation P (g - algebraMap F KE d) := Valuation.map_mul _ _ _
      _ ≤ 1 * (W_smooth W).pointValuation P (g - algebraMap F KE d) :=
          mul_le_mul_left hf.pointValuation_le_one _
      _ < 1 := by rw [one_mul]; exact hg
  · calc (W_smooth W).pointValuation P ((f - algebraMap F KE c) * algebraMap F KE d)
        = (W_smooth W).pointValuation P (f - algebraMap F KE c) *
          (W_smooth W).pointValuation P (algebraMap F KE d) := Valuation.map_mul _ _ _
      _ ≤ (W_smooth W).pointValuation P (f - algebraMap F KE c) * 1 :=
          mul_le_mul_right ((W_smooth W).pointValuation_algebraMap_F_le_one P d) _
      _ < 1 := by rw [mul_one]; exact hf

/-- Evaluation respects powers. -/
theorem EvaluatesTo.pow {P : (W_smooth W).SmoothPoint} {f : KE} {c : F}
    (hf : EvaluatesTo W P f c) (n : ℕ) : EvaluatesTo W P (f ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using evaluatesTo_algebraMap P (1 : F)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hf

/-- A function with nonzero value at `P` is a `v_P`-unit: `v_P g = 1`. -/
theorem EvaluatesTo.pointValuation_eq_one {P : (W_smooth W).SmoothPoint} {g : KE} {d : F}
    (hg : EvaluatesTo W P g d) (hd : d ≠ 0) : (W_smooth W).pointValuation P g = 1 := by
  have hg' : g = (g - algebraMap F KE d) + algebraMap F KE d := by abel
  have h1 : (W_smooth W).pointValuation P (algebraMap F KE d) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P hd
  calc (W_smooth W).pointValuation P g
      = (W_smooth W).pointValuation P ((g - algebraMap F KE d) + algebraMap F KE d) := by
        rw [← hg']
    _ = (W_smooth W).pointValuation P (algebraMap F KE d) :=
        Valuation.map_add_eq_of_lt_right _ (by rw [h1]; exact hg)
    _ = 1 := h1

/-- Evaluation respects division when the denominator value is nonzero. -/
theorem EvaluatesTo.div {P : (W_smooth W).SmoothPoint} {f g : KE} {c d : F}
    (hf : EvaluatesTo W P f c) (hg : EvaluatesTo W P g d) (hd : d ≠ 0) :
    EvaluatesTo W P (f / g) (c / d) := by
  have hvg : (W_smooth W).pointValuation P g = 1 := hg.pointValuation_eq_one hd
  have hgne : g ≠ 0 := fun h0 ↦ by
    rw [h0] at hvg
    exact zero_ne_one ((Valuation.map_zero _).symm.trans hvg)
  have hdne : algebraMap F KE d ≠ 0 := fun h0 ↦ hd <|
    (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective F KE)).mp h0
  -- `f/g − c/d = N / (g·d)` with `N = (f − c)·d + c·(d − g)`.
  have hrw : f / g - algebraMap F KE (c / d) =
      ((f - algebraMap F KE c) * algebraMap F KE d +
        algebraMap F KE c * (algebraMap F KE d - g)) / (g * algebraMap F KE d) := by
    rw [map_div₀]
    field_simp
    ring
  have hden : (W_smooth W).pointValuation P (g * algebraMap F KE d) = 1 := by
    rw [show (W_smooth W).pointValuation P (g * algebraMap F KE d) =
        (W_smooth W).pointValuation P g *
          (W_smooth W).pointValuation P (algebraMap F KE d) from Valuation.map_mul _ _ _,
      hvg, pointValuation_algebraMap_F_eq_one_of_ne_zero W P hd, one_mul]
  unfold EvaluatesTo
  rw [hrw]
  rw [show (W_smooth W).pointValuation P
      (((f - algebraMap F KE c) * algebraMap F KE d +
        algebraMap F KE c * (algebraMap F KE d - g)) / (g * algebraMap F KE d)) =
      (W_smooth W).pointValuation P
        ((f - algebraMap F KE c) * algebraMap F KE d +
          algebraMap F KE c * (algebraMap F KE d - g)) /
        (W_smooth W).pointValuation P (g * algebraMap F KE d) from map_div₀ _ _ _]
  rw [hden, div_one]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · calc (W_smooth W).pointValuation P ((f - algebraMap F KE c) * algebraMap F KE d)
        = (W_smooth W).pointValuation P (f - algebraMap F KE c) *
          (W_smooth W).pointValuation P (algebraMap F KE d) := Valuation.map_mul _ _ _
      _ ≤ (W_smooth W).pointValuation P (f - algebraMap F KE c) * 1 :=
          mul_le_mul_right ((W_smooth W).pointValuation_algebraMap_F_le_one P d) _
      _ < 1 := by rw [mul_one]; exact hf
  · have hsub : (W_smooth W).pointValuation P (algebraMap F KE d - g) < 1 := by
      have hneg : algebraMap F KE d - g = -(g - algebraMap F KE d) := by abel
      rw [hneg]
      exact (Valuation.map_neg _ _).trans_lt hg
    calc (W_smooth W).pointValuation P (algebraMap F KE c * (algebraMap F KE d - g))
        = (W_smooth W).pointValuation P (algebraMap F KE c) *
          (W_smooth W).pointValuation P (algebraMap F KE d - g) := Valuation.map_mul _ _ _
      _ ≤ 1 * (W_smooth W).pointValuation P (algebraMap F KE d - g) :=
          mul_le_mul_left ((W_smooth W).pointValuation_algebraMap_F_le_one P c) _
      _ < 1 := by rw [one_mul]; exact hsub

/-! ### Separation: functions agreeing at cofinitely many points are equal

Silverman II.1.2 (`finite_setOf_ord_P_nonzero`) + infinitude of `E(F̄)`
(`smoothPoint_infinite`). -/

variable (W)

/-- **Separation**: two rational functions sharing a value at all points outside a finite set
are equal, over an algebraically closed base.  A nonzero difference would have finitely many
zeros (Silverman II.1.2), but it vanishes at the cofinitely many good points of the infinite
`E(F̄)`. -/
theorem eq_of_evaluatesTo_cofinite [IsAlgClosed F] {f g : KE}
    {badS : Set (W_smooth W).SmoothPoint} (hfin : badS.Finite)
    (h : ∀ P ∉ badS, ∃ c : F, EvaluatesTo W P f c ∧ EvaluatesTo W P g c) : f = g := by
  by_contra hne
  have hD : f - g ≠ 0 := sub_ne_zero_of_ne hne
  -- Every good point is a zero of `f − g`.
  have hzero : ∀ P ∉ badS, (W_smooth W).ord_P P (f - g) ≠ 0 := by
    intro P hP
    obtain ⟨c, hf, hg⟩ := h P hP
    have hval : (W_smooth W).pointValuation P (f - g) < 1 := by
      have hrw : f - g = (f - algebraMap F KE c) - (g - algebraMap F KE c) := by abel
      rw [hrw]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hf hg)
    have h1 : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P (f - g) :=
      (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one (P := P) hD).mpr hval
    intro h0
    rw [h0] at h1
    have h1' : ((1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := by exact_mod_cast h1
    exact absurd (WithTop.coe_le_coe.mp h1') (by norm_num)
  -- So the (infinite) complement of `badS` sits inside the finite zero set.
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI : Infinite (W_smooth W).SmoothPoint := (W_smooth W).smoothPoint_infinite
  have hinf : (Set.univ \ badS : Set (W_smooth W).SmoothPoint).Infinite :=
    Set.infinite_univ.sdiff hfin
  refine ((W_smooth W).finite_setOf_ord_P_nonzero hD).not_infinite (hinf.mono ?_)
  intro P hP
  exact hzero P hP.2

/-! ### Translation moves the evaluation point

The `EvaluatesTo` form of the shipped valuation transport `translate_ord_eq_all_nonzero`
(`EC/TranslateValuation.lean`): `(τ_S f)(P) = f(P + S)`. -/

/-- **Translation–evaluation**: if `f` evaluates to `c` at `P + S`, then `τ_S f` evaluates to
`c` at `P` (for affine `S` with `P + S` affine). -/
theorem evaluatesTo_translate (P : (W_smooth W).SmoothPoint)
    (xs ys : F) (hnsS : W.toAffine.Nonsingular xs ys)
    (h : (P.toAffinePoint +
      (Affine.Point.some xs ys hnsS : (W_smooth W).toAffine.Point)).IsSome)
    {f : KE} {c : F}
    (hev : EvaluatesTo W
      (P.translate_of_finite (Affine.Point.some xs ys hnsS : (W_smooth W).toAffine.Point) h)
      f c) :
    EvaluatesTo W P
      (translateAlgEquivOfPoint W (Affine.Point.some xs ys hnsS) f) c := by
  have hτ : translateAlgEquivOfPoint W (Affine.Point.some xs ys hnsS) f -
      algebraMap F KE c =
      translateAlgEquivOfPoint W (Affine.Point.some xs ys hnsS)
        (f - algebraMap F KE c) := by
    rw [map_sub]
    exact congrArg (_ - ·) (AlgEquiv.commutes _ c).symm
  by_cases h0 : f - algebraMap F KE c = 0
  · unfold EvaluatesTo
    rw [hτ, h0, map_zero]
    exact (Valuation.map_zero _).trans_lt zero_lt_one
  · have hτ0 : translateAlgEquivOfPoint W (Affine.Point.some xs ys hnsS)
        (f - algebraMap F KE c) ≠ 0 := fun hz ↦ h0 <|
      (translateAlgEquivOfPoint W (Affine.Point.some xs ys hnsS)).injective
        (hz.trans (map_zero _).symm)
    have hord := translate_ord_eq_all_nonzero W P xs ys hnsS h (f - algebraMap F KE c) h0
    have h1 : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P
        (P.translate_of_finite (Affine.Point.some xs ys hnsS) h)
        (f - algebraMap F KE c) :=
      (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
        (P := P.translate_of_finite (Affine.Point.some xs ys hnsS) h) h0).mpr hev
    unfold EvaluatesTo
    rw [hτ]
    exact (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (P := P) hτ0).mp (h1.trans_eq hord.symm)

/-! ### The cofinite pullback-evaluation witness

The single irreducible per-isogeny input: at cofinitely many `P`, the stored point map lands at
a finite point whose coordinates are the values of the pulled-back generators. -/

/-- **The cofinite pullback-evaluation witness** for a `Basic.Isogeny β` with excluded set
`bad`: at every smooth `P ∉ bad`, the stored point map sends `P` to a *finite* point `(x', y')`
and `β^* x_gen`, `β^* y_gen` evaluate at `P` to `x'`, `y'`.

This is "the stored `toAddMonoidHom` is the geometric realization of the stored `pullback` away
from `bad`" — the coherence between the two independent fields of the abstract `Isogeny`
interface, which is exactly what `hgcomm` cannot see abstractly.  For an isogeny with a
`CoordHom` it holds with `bad = ∅` (`pullbackEvaluation_of_coordHom`); for an isogeny with
affine kernel points, `bad` must contain the affine kernel (where `β^* x_gen` has poles). -/
def PullbackEvaluation (β : Isogeny W.toAffine W.toAffine)
    (bad : Set (W_smooth W).SmoothPoint) : Prop :=
  ∀ P : (W_smooth W).SmoothPoint, P ∉ bad →
    ∃ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
      β.toAddMonoidHom P.toAffinePoint = Affine.Point.some x' y' h' ∧
      EvaluatesTo W P (β.pullback (x_gen W)) x' ∧
      EvaluatesTo W P (β.pullback (y_gen W)) y'

variable {W}

/-- `toAffinePoint` is injective on smooth points. -/
private theorem toAffinePoint_injective :
    Function.Injective
      (fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint) := by
  intro P Q h
  simp only [Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def] at h
  obtain ⟨hx, hy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h
  cases P; cases Q
  simp_all

/-- All fibres of the stored point map over arbitrary points are finite, given the witness:
the affine kernel is trapped inside `bad`, and a fibre is a kernel coset. -/
theorem PullbackEvaluation.finite_fiber {β : Isogeny W.toAffine W.toAffine}
    {bad : Set (W_smooth W).SmoothPoint} (hw : PullbackEvaluation W β bad)
    (hbad : bad.Finite) (Q : W.toAffine.Point) :
    {P : (W_smooth W).SmoothPoint | β.toAddMonoidHom P.toAffinePoint = Q}.Finite := by
  -- the point-level kernel is finite: `0` plus the affine kernel, which lies inside `bad`.
  have hker : {R : W.toAffine.Point | β.toAddMonoidHom R = 0}.Finite := by
    refine (Set.Finite.insert (0 : W.toAffine.Point)
      ((hbad.image (fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint)))).subset ?_
    rintro (_ | ⟨x, y, hns⟩) hR
    · exact Set.mem_insert_iff.mpr (Or.inl WeierstrassCurve.Affine.Point.zero_def.symm)
    · refine Set.mem_insert_iff.mpr (Or.inr ⟨⟨x, y, hns⟩, ?_, rfl⟩)
      by_contra hnotbad
      obtain ⟨x', y', h', heq, -, -⟩ := hw ⟨x, y, hns⟩ hnotbad
      rw [Set.mem_setOf_eq] at hR
      have hcontra := WeierstrassCurve.Affine.Point.zero_def.symm.trans (hR.symm.trans heq)
      simp at hcontra
  -- a nonempty fibre injects into the kernel via subtraction of a base point.
  rcases Set.eq_empty_or_nonempty
    {P : (W_smooth W).SmoothPoint | β.toAddMonoidHom P.toAffinePoint = Q} with hemp | ⟨P₀, hP₀⟩
  · rw [hemp]; exact Set.finite_empty
  · refine Set.Finite.of_finite_image (f := fun P : (W_smooth W).SmoothPoint ↦
      P.toAffinePoint - P₀.toAffinePoint) ?_ ?_
    · refine hker.subset ?_
      rintro R ⟨P, hP, rfl⟩
      rw [Set.mem_setOf_eq] at hP hP₀ ⊢
      change β.toAddMonoidHom (P.toAffinePoint - P₀.toAffinePoint) = 0
      exact (map_sub β.toAddMonoidHom P.toAffinePoint P₀.toAffinePoint).trans
        (sub_eq_zero_of_eq (hP.trans hP₀.symm))
    · intro P _ P' _ hPP'
      exact toAffinePoint_injective (sub_left_injective (G := W.toAffine.Point) hPP')

/-- The pulled-back generator `β^* x_gen` is **not constant** (over an algebraically closed
base): otherwise the stored point map would send cofinitely many points into the two-point
locus `{x = c}`, contradicting fibre finiteness and the infinitude of `E(F̄)`. -/
theorem PullbackEvaluation.pullback_x_gen_ne_algebraMap [IsAlgClosed F]
    {β : Isogeny W.toAffine W.toAffine} {bad : Set (W_smooth W).SmoothPoint}
    (hw : PullbackEvaluation W β bad) (hbad : bad.Finite) (c : F) :
    β.pullback (x_gen W) ≠ algebraMap F KE c := by
  intro hconst
  haveI hEll : (W_smooth W).toAffine.IsElliptic := ‹W.toAffine.IsElliptic›
  haveI : Infinite (W_smooth W).SmoothPoint := (W_smooth W).smoothPoint_infinite
  -- a point with `x`-coordinate `c` exists over `F̄`.
  obtain ⟨Q₀, hQ₀x⟩ := (W_smooth W).exists_smoothPoint_of_x c
  -- every good point maps into `{Q₀, −Q₀}`.
  have hgood : ∀ P : (W_smooth W).SmoothPoint, P ∉ bad →
      β.toAddMonoidHom P.toAffinePoint =
        (Affine.Point.some Q₀.x Q₀.y Q₀.nonsingular : W.toAffine.Point) ∨
      β.toAddMonoidHom P.toAffinePoint =
        -(Affine.Point.some Q₀.x Q₀.y Q₀.nonsingular : W.toAffine.Point) := by
    intro P hP
    obtain ⟨x', y', h', heq, hx, -⟩ := hw P hP
    have hx' : x' = c := by
      have hc : EvaluatesTo W P (β.pullback (x_gen W)) c := by
        rw [hconst]; exact evaluatesTo_algebraMap P c
      exact hx.unique hc
    have hxQ : x' = Q₀.x := hx'.trans hQ₀x.symm
    have hYor := WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 Q₀.nonsingular.1 hxQ
    rcases hYor with hy | hy
    · left
      rw [heq]
      exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxQ, hy⟩
    · right
      rw [heq, HasseWeil.neg_some_eq_some W Q₀.x Q₀.y Q₀.nonsingular]
      exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxQ, hy⟩
  -- hence the whole (infinite) point set is covered by finitely many points.
  have hcover : (Set.univ : Set (W_smooth W).SmoothPoint) ⊆
      bad ∪ {P | β.toAddMonoidHom P.toAffinePoint =
          (Affine.Point.some Q₀.x Q₀.y Q₀.nonsingular : W.toAffine.Point)} ∪
        {P | β.toAddMonoidHom P.toAffinePoint =
          -(Affine.Point.some Q₀.x Q₀.y Q₀.nonsingular : W.toAffine.Point)} := by
    intro P _
    by_cases hP : P ∈ bad
    · exact Or.inl (Or.inl hP)
    · rcases hgood P hP with h1 | h1
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1
  exact Set.infinite_univ (((hbad.union
      (hw.finite_fiber hbad _)).union
      (hw.finite_fiber hbad _)).subset hcover)

/-! ### The engine -/

variable (W)

/-- **The generic-point covariance `hgcomm` for a general isogeny** (Silverman III.8.2,
generic-point form), from the cofinite pullback-evaluation witness, over an algebraically
closed base.  This discharges the leaf `MapTranslateGenericPoint` for the **canonical** action
`g = Affine.Point.map β.pullback`, for **every** `S` (not only kernel points), via the
evaluation + separation argument described in the module docstring. -/
theorem mapTranslateGenericPoint_of_pullbackEvaluation [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine) {bad : Set (W_smooth W).SmoothPoint}
    (hbad : bad.Finite) (hw : PullbackEvaluation W β bad) :
    MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback) := by
  intro S
  set Bx := β.pullback (x_gen W) with hBx
  set By := β.pullback (y_gen W) with hBy
  have hns1 : (W_KE W).toAffine.Nonsingular Bx By :=
    (WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
      β.pullback.injective (x_gen W) (y_gen W)).mpr (generic_nonsingular W)
  have hgen1 : WeierstrassCurve.Affine.Point.map (W' := W) β.pullback
      (HasseWeil.genericPoint W) = Affine.Point.some Bx By hns1 :=
    WeierstrassCurve.Affine.Point.map_some (f := β.pullback) (generic_nonsingular W)
  have hτns : (W_KE W).toAffine.Nonsingular
      ((translateAlgEquivOfPoint W S).toAlgHom Bx)
      ((translateAlgEquivOfPoint W S).toAlgHom By) :=
    (WeierstrassCurve.Affine.baseChange_nonsingular W.toAffine
      (translateAlgEquivOfPoint W S).toAlgHom.injective Bx By).mpr hns1
  have hτmap : WeierstrassCurve.Affine.Point.map (W' := W)
      (translateAlgEquivOfPoint W S).toAlgHom (Affine.Point.some Bx By hns1) =
      Affine.Point.some ((translateAlgEquivOfPoint W S).toAlgHom Bx)
        ((translateAlgEquivOfPoint W S).toAlgHom By) hτns :=
    WeierstrassCurve.Affine.Point.map_some
      (f := (translateAlgEquivOfPoint W S).toAlgHom) hns1
  -- The per-point evaluation facts, for affine `S`, packaged for the separation lemma.
  -- We first dispose of `S = 0`, where the translation is the identity.
  rcases S with _ | ⟨xs, ys, hnsS⟩
  · -- `S = 0`: `τ_0 = id` and `β 0 = 0`.
    have hβ0 : β.toAddMonoidHom Affine.Point.zero = 0 :=
      (congrArg β.toAddMonoidHom WeierstrassCurve.Affine.Point.zero_def.symm).trans
        (map_zero β.toAddMonoidHom)
    have hzero_add : Affine.Point.some Bx By hns1 =
        Affine.Point.some Bx By hns1 +
          HasseWeil.liftPointToKE W (β.toAddMonoidHom Affine.Point.zero) := by
      rw [hβ0, map_zero, add_zero]
    exact ((congrArg (WeierstrassCurve.Affine.Point.map (W' := W)
        (translateAlgEquivOfPoint W Affine.Point.zero).toAlgHom) hgen1).trans
      (hτmap.trans
        ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨rfl, rfl⟩))).trans
      (hzero_add.trans (congrArg
        (· + HasseWeil.liftPointToKE W (β.toAddMonoidHom Affine.Point.zero)) hgen1.symm))
  · -- `S = (xs, ys)` affine.  Assemble the finite bad set for the separation argument.
    set Sk : (W_smooth W).toAffine.Point := Affine.Point.some xs ys hnsS with hSk
    -- the two finite exclusion sets tied to the translation
    have hB2fin : {P : (W_smooth W).SmoothPoint |
        ¬(P.toAffinePoint + Sk).IsSome}.Finite := by
      refine (Set.Finite.preimage toAffinePoint_injective.injOn
        (Set.finite_singleton (-Sk))).subset ?_
      intro P hP
      rw [Set.mem_setOf_eq, WeierstrassCurve.Affine.Point.IsSome, not_not] at hP
      have : P.toAffinePoint = -Sk := by
        rw [eq_neg_iff_add_eq_zero, ← WeierstrassCurve.Affine.Point.zero_def] at *
        exact hP
      exact this
    have hB3fin : {P : (W_smooth W).SmoothPoint |
        ∃ h' : (P.toAffinePoint + Sk).IsSome,
          P.translate_of_finite Sk h' ∈ bad}.Finite := by
      refine (Set.Finite.preimage toAffinePoint_injective.injOn
        (((hbad.image (fun P : (W_smooth W).SmoothPoint ↦ P.toAffinePoint)).image
          (fun R ↦ R - Sk)))).subset ?_
      rintro P ⟨h', hmem⟩
      refine ⟨(P.translate_of_finite Sk h').toAffinePoint, ⟨_, hmem, rfl⟩, ?_⟩
      change (P.translate_of_finite Sk h').toAffinePoint - Sk = P.toAffinePoint
      rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint]
      exact add_sub_cancel_right _ _
    -- per-point evaluation data at a good point, shared by both `T`-branches
    have hkey : ∀ P : (W_smooth W).SmoothPoint, P ∉ bad →
        ∀ h' : (P.toAffinePoint + Sk).IsSome, P.translate_of_finite Sk h' ∉ bad →
        ∃ (xI yI : F) (hI : W.toAffine.Nonsingular xI yI),
          β.toAddMonoidHom P.toAffinePoint + β.toAddMonoidHom Sk =
            Affine.Point.some xI yI hI ∧
          EvaluatesTo W P (translateAlgEquivOfPoint W Sk Bx) xI ∧
          EvaluatesTo W P (translateAlgEquivOfPoint W Sk By) yI := by
      intro P hP h' hP'
      obtain ⟨xI, yI, hI, heqI, hxI, hyI⟩ := hw (P.translate_of_finite Sk h') hP'
      have hι : (P.translate_of_finite Sk h').toAffinePoint = P.toAffinePoint + Sk :=
        Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint P Sk h'
      have hβsum : β.toAddMonoidHom P.toAffinePoint + β.toAddMonoidHom Sk =
          Affine.Point.some xI yI hI :=
        (map_add β.toAddMonoidHom P.toAffinePoint Sk).symm.trans
          ((congrArg β.toAddMonoidHom hι).symm.trans heqI)
      exact ⟨xI, yI, hI, hβsum,
        evaluatesTo_translate W P xs ys hnsS h' hxI,
        evaluatesTo_translate W P xs ys hnsS h' hyI⟩
    -- Case split on the image `T = β S`.
    rcases hTeq : β.toAddMonoidHom Sk with _ | ⟨xT, yT, hT⟩
    · -- `T = 0`: the covariance degenerates to invariance of the two pulled-back generators.
      have hbadS : (bad ∪ {P : (W_smooth W).SmoothPoint | ¬(P.toAffinePoint + Sk).IsSome} ∪
          {P : (W_smooth W).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
            P.translate_of_finite Sk h' ∈ bad}).Finite :=
        (hbad.union hB2fin).union hB3fin
      have hcoords : ∀ P : (W_smooth W).SmoothPoint, P ∉ (bad ∪
          {P : (W_smooth W).SmoothPoint | ¬(P.toAffinePoint + Sk).IsSome} ∪
          {P : (W_smooth W).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
            P.translate_of_finite Sk h' ∈ bad}) →
          (∃ c, EvaluatesTo W P (translateAlgEquivOfPoint W Sk Bx) c ∧
            EvaluatesTo W P Bx c) ∧
          (∃ c, EvaluatesTo W P (translateAlgEquivOfPoint W Sk By) c ∧
            EvaluatesTo W P By c) := by
        intro P hP
        rw [Set.mem_union, Set.mem_union] at hP
        push Not at hP
        obtain ⟨⟨hP1, hP2⟩, hP3⟩ := hP
        rw [Set.mem_setOf_eq, not_not] at hP2
        rw [Set.mem_setOf_eq] at hP3
        push Not at hP3
        obtain ⟨xI, yI, hI, hβsum, hτx, hτy⟩ := hkey P hP1 hP2 (hP3 hP2)
        obtain ⟨xP, yP, hPns, heqP, hxP, hyP⟩ := hw P hP1
        -- `β P + 0 = β P`, so the image coordinates agree.
        rw [hTeq, ← WeierstrassCurve.Affine.Point.zero_def, add_zero, heqP] at hβsum
        obtain ⟨hxx, hyy⟩ :=
          (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hβsum
        exact ⟨⟨xI, hτx, hxx ▸ hxP⟩, ⟨yI, hτy, hyy ▸ hyP⟩⟩
      have hX0 : (translateAlgEquivOfPoint W Sk).toAlgHom Bx = Bx :=
        eq_of_evaluatesTo_cofinite W hbadS (fun P hP ↦ (hcoords P hP).1)
      have hY0 : (translateAlgEquivOfPoint W Sk).toAlgHom By = By :=
        eq_of_evaluatesTo_cofinite W hbadS (fun P hP ↦ (hcoords P hP).2)
      have hzero_add : Affine.Point.some Bx By hns1 =
          Affine.Point.some Bx By hns1 +
            HasseWeil.liftPointToKE W (β.toAddMonoidHom Sk) := by
        rw [hTeq, ← WeierstrassCurve.Affine.Point.zero_def, map_zero, add_zero]
      exact ((congrArg (WeierstrassCurve.Affine.Point.map (W' := W)
          (translateAlgEquivOfPoint W Sk).toAlgHom) hgen1).trans
        (hτmap.trans
          ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hX0, hY0⟩))).trans
        (hzero_add.trans (congrArg
          (· + HasseWeil.liftPointToKE W (β.toAddMonoidHom Sk)) hgen1.symm))
    · -- `T = (x_T, y_T)` affine: the genuine group-law case.
      have hne : Bx ≠ algebraMap F KE xT :=
        hw.pullback_x_gen_ne_algebraMap hbad xT
      have hTns' : (W_KE W).toAffine.Nonsingular (algebraMap F KE xT)
          (algebraMap F KE yT) :=
        (WeierstrassCurve.Affine.map_nonsingular W.toAffine
          (RingHom.injective (algebraMap F KE)) xT yT).mpr hT
      have hlift : HasseWeil.liftPointToKE W (β.toAddMonoidHom Sk) =
          Affine.Point.some (algebraMap F KE xT) (algebraMap F KE yT) hTns' := by
        rw [hTeq]
        exact HasseWeil.liftPointToKE_some W xT yT hT
      set ℓKE : KE := (By - algebraMap F KE yT) / (Bx - algebraMap F KE xT) with hℓKE
      have hns3 := WeierstrassCurve.Affine.nonsingular_add hns1 hTns' (fun hc ↦ hne hc.1)
      rw [WeierstrassCurve.Affine.slope_of_X_ne hne] at hns3
      have hadd : Affine.Point.some Bx By hns1 + Affine.Point.some (algebraMap F KE xT)
            (algebraMap F KE yT) hTns' =
          Affine.Point.some ((W_KE W).toAffine.addX Bx (algebraMap F KE xT) ℓKE)
            ((W_KE W).toAffine.addY Bx (algebraMap F KE xT) By ℓKE) hns3 := by
        rw [WeierstrassCurve.Affine.Point.add_some (fun hc ↦ hne hc.1)]
        exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
          ⟨by rw [WeierstrassCurve.Affine.slope_of_X_ne hne],
           by rw [WeierstrassCurve.Affine.slope_of_X_ne hne]⟩
      -- bad set: also exclude the fibres over `T` and `−T`
      have hbadS : (bad ∪ {P : (W_smooth W).SmoothPoint |
            ¬(P.toAffinePoint + Sk).IsSome} ∪
          {P : (W_smooth W).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
            P.translate_of_finite Sk h' ∈ bad} ∪
          {P : (W_smooth W).SmoothPoint |
            β.toAddMonoidHom P.toAffinePoint = Affine.Point.some xT yT hT} ∪
          {P : (W_smooth W).SmoothPoint |
            β.toAddMonoidHom P.toAffinePoint = -Affine.Point.some xT yT hT}).Finite :=
        (((hbad.union hB2fin).union hB3fin).union
          (hw.finite_fiber hbad _)).union (hw.finite_fiber hbad _)
      have hcoords : ∀ P : (W_smooth W).SmoothPoint, P ∉ (bad ∪
          {P : (W_smooth W).SmoothPoint | ¬(P.toAffinePoint + Sk).IsSome} ∪
          {P : (W_smooth W).SmoothPoint | ∃ h' : (P.toAffinePoint + Sk).IsSome,
            P.translate_of_finite Sk h' ∈ bad} ∪
          {P : (W_smooth W).SmoothPoint |
            β.toAddMonoidHom P.toAffinePoint = Affine.Point.some xT yT hT} ∪
          {P : (W_smooth W).SmoothPoint |
            β.toAddMonoidHom P.toAffinePoint = -Affine.Point.some xT yT hT}) →
          (∃ c, EvaluatesTo W P (translateAlgEquivOfPoint W Sk Bx) c ∧
            EvaluatesTo W P ((W_KE W).toAffine.addX Bx (algebraMap F KE xT) ℓKE) c) ∧
          (∃ c, EvaluatesTo W P (translateAlgEquivOfPoint W Sk By) c ∧
            EvaluatesTo W P ((W_KE W).toAffine.addY Bx (algebraMap F KE xT) By ℓKE) c) := by
        intro P hP
        simp only [Set.mem_union, not_or] at hP
        obtain ⟨⟨⟨⟨hP1, hP2⟩, hP3⟩, hP4⟩, hP5⟩ := hP
        rw [Set.mem_setOf_eq, not_not] at hP2
        rw [Set.mem_setOf_eq] at hP3 hP4 hP5
        push Not at hP3
        obtain ⟨xI, yI, hI, hβsum, hτx, hτy⟩ := hkey P hP1 hP2 (hP3 hP2)
        obtain ⟨xP, yP, hPns, heqP, hxP, hyP⟩ := hw P hP1
        -- the image is not `±T`, so its `x`-coordinate differs from `x_T`
        have hxPT : xP ≠ xT := by
          intro hxx
          rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hPns.1 hT.1 hxx with hyy | hyy
          · exact hP4 (heqP.trans
              ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩))
          · refine hP5 (heqP.trans ?_)
            rw [HasseWeil.neg_some_eq_some W xT yT hT]
            exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hxx, hyy⟩
        -- the F-level group law: `β P + T` in coordinates
        set ℓF : F := (yP - yT) / (xP - xT) with hℓF
        have hns3F := WeierstrassCurve.Affine.nonsingular_add hPns hT
          (fun hc ↦ hxPT hc.1)
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxPT] at hns3F
        have haddF : β.toAddMonoidHom P.toAffinePoint + β.toAddMonoidHom Sk =
            Affine.Point.some (W.toAffine.addX xP xT ℓF)
              (W.toAffine.addY xP xT yP ℓF) hns3F := by
          rw [heqP, hTeq, WeierstrassCurve.Affine.Point.add_some (fun hc ↦ hxPT hc.1)]
          exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
            ⟨by rw [WeierstrassCurve.Affine.slope_of_X_ne hxPT],
             by rw [WeierstrassCurve.Affine.slope_of_X_ne hxPT]⟩
        -- identify the witness coordinates with the group-law coordinates
        obtain ⟨hxx, hyy⟩ := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp
          (hβsum.symm.trans haddF)
        -- evaluation of the slope and the addition formulas
        have hxden : xP - xT ≠ 0 := sub_ne_zero_of_ne hxPT
        have hslope : EvaluatesTo W P ℓKE ℓF :=
          (hyP.sub (evaluatesTo_algebraMap P yT)).div
            (hxP.sub (evaluatesTo_algebraMap P xT)) hxden
        have haddXev : EvaluatesTo W P
            ((W_KE W).toAffine.addX Bx (algebraMap F KE xT) ℓKE)
            (W.toAffine.addX xP xT ℓF) :=
          ((((hslope.pow 2).add
            ((evaluatesTo_algebraMap P W.toAffine.a₁).mul hslope)).sub
            (evaluatesTo_algebraMap P W.toAffine.a₂)).sub hxP).sub
            (evaluatesTo_algebraMap P xT)
        have hnegAddYev : EvaluatesTo W P
            ((W_KE W).toAffine.negAddY Bx (algebraMap F KE xT) By ℓKE)
            (W.toAffine.negAddY xP xT yP ℓF) :=
          (hslope.mul (haddXev.sub hxP)).add hyP
        have haddYev : EvaluatesTo W P
            ((W_KE W).toAffine.addY Bx (algebraMap F KE xT) By ℓKE)
            (W.toAffine.addY xP xT yP ℓF) :=
          (hnegAddYev.neg.sub
            ((evaluatesTo_algebraMap P W.toAffine.a₁).mul haddXev)).sub
            (evaluatesTo_algebraMap P W.toAffine.a₃)
        exact ⟨⟨xI, hτx, hxx ▸ haddXev⟩, ⟨yI, hτy, hyy ▸ haddYev⟩⟩
      have hX : (translateAlgEquivOfPoint W Sk).toAlgHom Bx =
          (W_KE W).toAffine.addX Bx (algebraMap F KE xT) ℓKE :=
        eq_of_evaluatesTo_cofinite W hbadS (fun P hP ↦ (hcoords P hP).1)
      have hY : (translateAlgEquivOfPoint W Sk).toAlgHom By =
          (W_KE W).toAffine.addY Bx (algebraMap F KE xT) By ℓKE :=
        eq_of_evaluatesTo_cofinite W hbadS (fun P hP ↦ (hcoords P hP).2)
      exact ((congrArg (WeierstrassCurve.Affine.Point.map (W' := W)
          (translateAlgEquivOfPoint W Sk).toAlgHom) hgen1).trans
        (hτmap.trans
          ((WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hX, hY⟩))).trans
        (hadd.symm.trans (congrArg₂ (· + ·) hgen1.symm hlift.symm))

variable {W}

/-! ### The CoordHom discharge -/

variable (W)

/-- **A `CoordHom` discharges the witness with no excluded points**: for an `EC.Isogeny φ`
with coordinate-ring witness `cd`, whose pullback and point map agree with `β`'s, the
pullback-evaluation witness holds with `bad = ∅`.  The generator evaluations are the residue
coherence `evalAt_toPointMap` (`Curves/PointFunctor.lean`), and the image point is always
affine (the coordinate-ring comorphism has no poles). -/
theorem pullbackEvaluation_of_coordHom
    (φE : EC.Isogeny W.toAffine W.toAffine) (cd : φE.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φE.toPointMap cd P) :
    PullbackEvaluation W β ∅ := by
  intro P _
  -- the image point under the coordinate-ring point functor
  set Q : (W_smooth W).SmoothPoint := Curves.CurveMap.toPointMap cd P with hQ
  -- the value of the pulled-back coordinate functions at `P` is the coordinate of `Q`
  have hvalx : (W_smooth W).evalAt P
      (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) =
      Q.x := by
    have h1 := (Curves.CurveMap.evalAt_toPointMap cd P
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)).symm
    rw [Curves.CurveMap.evalAtPullback_apply] at h1
    refine h1.trans ?_
    rw [show algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C Polynomial.X) from rfl]
    exact (W_smooth W).evalAt_x Q
  have hvaly : (W_smooth W).evalAt P
      (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) = Q.y := by
    have h1 := (Curves.CurveMap.evalAt_toPointMap cd P
      (AdjoinRoot.root W.toAffine.polynomial)).symm
    rw [Curves.CurveMap.evalAtPullback_apply] at h1
    refine h1.trans ?_
    rw [show AdjoinRoot.root W.toAffine.polynomial =
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine Polynomial.X from rfl]
    exact (W_smooth W).evalAt_y Q
  refine ⟨Q.x, Q.y, Q.nonsingular, ?_, ?_, ?_⟩
  · -- the stored point map is the CoordHom point functor, which never escapes to `O`
    rw [h_hom]
    rfl
  · -- evaluation of `β^* x_gen` at `P`
    have hxgen : β.pullback (x_gen W) =
        algebraMap W.toAffine.CoordinateRing KE
          (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing
            Polynomial.X)) := by
      rw [← h_pb, x_gen]
      exact cd.compat _
    have h0 : (W_smooth W).evalAt P
        (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) -
          algebraMap F W.toAffine.CoordinateRing Q.x) = 0 :=
      (map_sub ((W_smooth W).evalAt P) _ _).trans
        (by rw [hvalx]
            exact sub_eq_zero_of_eq ((W_smooth W).evalAt_algebraMap P Q.x).symm)
    have hmem : cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing
        Polynomial.X) - algebraMap F W.toAffine.CoordinateRing Q.x ∈
        (W_smooth W).maximalIdealAt P :=
      (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr h0
    have hrw : β.pullback (x_gen W) - algebraMap F KE Q.x =
        algebraMap W.toAffine.CoordinateRing KE
          (cd.toAlgHom (algebraMap (Polynomial F) W.toAffine.CoordinateRing
            Polynomial.X) - algebraMap F W.toAffine.CoordinateRing Q.x) := by
      rw [map_sub, ← hxgen, ← IsScalarTower.algebraMap_apply]
    unfold EvaluatesTo
    rw [hrw]
    exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) _ P).mpr hmem
  · -- evaluation of `β^* y_gen` at `P`
    have hygen : β.pullback (y_gen W) =
        algebraMap W.toAffine.CoordinateRing KE
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial)) := by
      rw [← h_pb, y_gen]
      exact cd.compat _
    have h0 : (W_smooth W).evalAt P
        (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial) -
          algebraMap F W.toAffine.CoordinateRing Q.y) = 0 :=
      (map_sub ((W_smooth W).evalAt P) _ _).trans
        (by rw [hvaly]
            exact sub_eq_zero_of_eq ((W_smooth W).evalAt_algebraMap P Q.y).symm)
    have hmem : cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial) -
        algebraMap F W.toAffine.CoordinateRing Q.y ∈
        (W_smooth W).maximalIdealAt P :=
      (W_smooth W).ker_evalAt P ▸ RingHom.mem_ker.mpr h0
    have hrw : β.pullback (y_gen W) - algebraMap F KE Q.y =
        algebraMap W.toAffine.CoordinateRing KE
          (cd.toAlgHom (AdjoinRoot.root W.toAffine.polynomial) -
            algebraMap F W.toAffine.CoordinateRing Q.y) := by
      rw [map_sub, ← hygen, ← IsScalarTower.algebraMap_apply]
    unfold EvaluatesTo
    rw [hrw]
    exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) _ P).mpr hmem

/-- **`hgcomm` for any isogeny with a `CoordHom`** over an algebraically closed base: the
canonical-action generic-point covariance `MapTranslateGenericPoint`, with no per-`S` or
per-point hypotheses. -/
theorem mapTranslateGenericPoint_of_coordHom [IsAlgClosed F]
    (φE : EC.Isogeny W.toAffine W.toAffine) (cd : φE.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φE.toPointMap cd P) :
    MapTranslateGenericPoint W β
      (WeierstrassCurve.Affine.Point.map (W' := W) β.pullback) :=
  mapTranslateGenericPoint_of_pullbackEvaluation W β Set.finite_empty
    (pullbackEvaluation_of_coordHom W φE cd β h_pb h_hom)

/-! ### Wiring into the dual-witness Galois data -/

/-- **The `xy_family` covariance from the pullback-evaluation witness** (DUAL-2 wiring): the
translation-covariance input of `fixedField_hfix_of_xy_family_of_card` /
`dualGaloisData_of_basic_witnesses`, discharged for a general `β` from the cofinite
pullback-evaluation witness over an algebraically closed base. -/
theorem xy_family_of_pullbackEvaluation [IsAlgClosed F]
    (β : Isogeny W.toAffine W.toAffine) {bad : Set (W_smooth W).SmoothPoint}
    (hbad : bad.Finite) (hw : PullbackEvaluation W β bad) :
    ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) = β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) = β.pullback (y_gen W)) :=
  HasseWeil.xy_family_of_genericPointCommutes W β
    (mapTranslateGenericPoint_of_pullbackEvaluation W β hbad hw)

/-- **The `xy_family` covariance from a `CoordHom`** (DUAL-2 wiring, CoordHom instance). -/
theorem xy_family_of_coordHom [IsAlgClosed F]
    (φE : EC.Isogeny W.toAffine W.toAffine) (cd : φE.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φE.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φE.toPointMap cd P) :
    ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) = β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) = β.pullback (y_gen W)) :=
  HasseWeil.xy_family_of_genericPointCommutes W β
    (mapTranslateGenericPoint_of_coordHom W φE cd β h_pb h_hom)

end HasseWeil.WeilPairing
