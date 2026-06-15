import HasseWeil.Curves.PointFunctor
import HasseWeil.Curves.Valuation
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Ord-transport Step (A): smooth-point translation by a group element

For an elliptic curve `E` with group law on `Affine.Point`, a `SmoothPoint`
`P` and a group element `k : E.Point`, the translated point `P + k` lives
in `E.Point` (which includes the point at infinity `Point.zero`). When the
translate is non-zero (i.e., `P + k ≠ O`), it lifts back to a `SmoothPoint`
via the `Affine.Point.some` constructor.

This is the foundational primitive for the ord-transport identity
(Step B): `pointValuation P (τ_k f) = pointValuation (P + k) f`.

## Main definitions

* `Affine.Point.IsSome` — predicate "this point is not the identity".
* `SmoothPoint.translate_of_finite` — partial translation of a SmoothPoint
  by a group element, valid when the sum is non-zero.

## Multi-session arc

This is **Step (A)** of the ord-transport decomposition (~30-50 LOC).
Step (B) follows in subsequent sessions:
- `translateAlgEquivOfPoint_smul_pointValuation` — the substantive
  identity `pointValuation P (τ_k f) = pointValuation (P + k) f`.
- Step (C): bridge `ordAtInfty ↔ ord_P` at translated points (~50-100 LOC).
-/

namespace HasseWeil.Curves

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### `Affine.Point.IsSome` predicate

The "non-zero" predicate on `Affine.Point`, used to gate partial smooth-point
operations (e.g., translation, where the result might be the identity at
infinity rather than a finite smooth point). -/

/-- A point of `W.toAffine.Point` is **not the identity** (= not the point at
infinity). Used to gate operations that map to `SmoothPoint`. -/
def _root_.WeierstrassCurve.Affine.Point.IsSome
    {R : Type*} [CommRing R] {W : Affine R}
    (P : W.Point) : Prop :=
  P ≠ Affine.Point.zero

/-- `Point.some` always satisfies `IsSome`. -/
@[simp] theorem _root_.WeierstrassCurve.Affine.Point.some_isSome
    {R : Type*} [CommRing R] {W : Affine R}
    (x y : R) (h_ns : W.Nonsingular x y) :
    (Affine.Point.some x y h_ns : W.Point).IsSome := by
  unfold Affine.Point.IsSome
  intro h; nomatch h

/-- `Point.zero` does NOT satisfy `IsSome`. -/
theorem _root_.WeierstrassCurve.Affine.Point.zero_not_isSome
    {R : Type*} [CommRing R] {W : Affine R} :
    ¬ ((Affine.Point.zero : W.Point).IsSome) := by
  unfold Affine.Point.IsSome
  intro h; exact h rfl

/-! ### `SmoothPoint.translate_of_finite`

Partial translation: for a `SmoothPoint` `P` and group element `k : E.Point`,
when `P + k ≠ O` (the identity), the sum is of the form `Point.some xRes
yRes h_ns_Res` and lifts back to a `SmoothPoint`. -/

namespace SmoothPlaneCurve

variable {C : SmoothPlaneCurve F} [C.toAffine.IsElliptic]

/-- **Helper**: extract the `(x, y, h_ns)` data from a non-zero
`Affine.Point` via `Classical.choose`-style decomposition. Concretely
constructs the existential `∃ x y h_ns, P = some x y h_ns` from
`P.IsSome`. -/
private theorem _root_.WeierstrassCurve.Affine.Point.exists_some_of_isSome
    {R : Type*} [CommRing R] {W : Affine R} (P : W.Point)
    (h : P.IsSome) :
    ∃ x : R, ∃ y : R, ∃ h_ns : W.Nonsingular x y,
      P = Affine.Point.some x y h_ns := by
  cases P with
  | zero => exact absurd rfl h
  | some x y h_ns => exact ⟨x, y, h_ns, rfl⟩

/-- **Step (A) of the ord-transport arc**: translate a smooth point by a
group element, conditional on the sum being non-zero (= a finite point,
not the identity at infinity).

When `P.toAffinePoint + k ≠ Affine.Point.zero`, the sum is of the form
`Affine.Point.some xRes yRes h_ns_Res` and lifts to a `SmoothPoint`. -/
noncomputable def SmoothPoint.translate_of_finite
    (P : C.SmoothPoint) (k : C.toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    C.SmoothPoint :=
  let ex := Affine.Point.exists_some_of_isSome (P.toAffinePoint + k) h
  ⟨ex.choose, ex.choose_spec.choose, ex.choose_spec.choose_spec.choose⟩

/-- The `toAffinePoint` of the translated SmoothPoint is exactly `P + k`. -/
@[simp] theorem SmoothPoint.translate_of_finite_toAffinePoint
    (P : C.SmoothPoint) (k : C.toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    (P.translate_of_finite k h).toAffinePoint = P.toAffinePoint + k := by
  unfold SmoothPoint.translate_of_finite
  show Affine.Point.some _ _ _ = _
  set ex := Affine.Point.exists_some_of_isSome (P.toAffinePoint + k) h
  exact (ex.choose_spec.choose_spec.choose_spec).symm

/-- The x-coordinate of the translated SmoothPoint matches the
`Affine.Point.some` form of `P + k`. -/
theorem SmoothPoint.translate_of_finite_x
    (P : C.SmoothPoint) (k : C.toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    {x y : F} {h_ns : C.toAffine.Nonsingular x y}
    (hsum : P.toAffinePoint + k = Affine.Point.some x y h_ns) :
    (P.translate_of_finite k h).x = x := by
  have h_eq := P.translate_of_finite_toAffinePoint k h
  rw [hsum] at h_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_eq |>.1

/-- The y-coordinate of the translated SmoothPoint matches the
`Affine.Point.some` form of `P + k`. -/
theorem SmoothPoint.translate_of_finite_y
    (P : C.SmoothPoint) (k : C.toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome)
    {x y : F} {h_ns : C.toAffine.Nonsingular x y}
    (hsum : P.toAffinePoint + k = Affine.Point.some x y h_ns) :
    (P.translate_of_finite k h).y = y := by
  have h_eq := P.translate_of_finite_toAffinePoint k h
  rw [hsum] at h_eq
  exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_eq |>.2

/-! ### Specialisation: translation by zero

`translate_of_finite` at `k = Point.zero` is the identity on `SmoothPoint`. -/

/-- Translation by the identity element preserves the smooth point. -/
@[simp] theorem SmoothPoint.translate_of_finite_zero
    (P : C.SmoothPoint)
    (h : (P.toAffinePoint + (0 : C.toAffine.Point)).IsSome) :
    P.translate_of_finite (0 : C.toAffine.Point) h = P := by
  apply SmoothPoint.ext
  · -- x-coordinate
    have h_eq := P.translate_of_finite_toAffinePoint (0 : C.toAffine.Point) h
    rw [add_zero] at h_eq
    show (P.translate_of_finite _ h).x = P.x
    rw [SmoothPoint.toAffinePoint_def] at h_eq
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_eq |>.1
  · -- y-coordinate
    have h_eq := P.translate_of_finite_toAffinePoint (0 : C.toAffine.Point) h
    rw [add_zero] at h_eq
    show (P.translate_of_finite _ h).y = P.y
    rw [SmoothPoint.toAffinePoint_def] at h_eq
    exact (Affine.Point.some.injEq _ _ _ _ _ _).mp h_eq |>.2

/-! ### Step (B) — pointValuation transport under translation

The substantive identity for the ord-transport arc:
`pointValuation P (τ_k f) = pointValuation (P.translate_of_finite k h) f`

where `τ_k = translateAlgEquivOfPoint W k` is the function-field-level
translation (defined as an `AlgEquiv K(E) ≃ K(E)`), and the right-hand
side uses Step (A)'s `translate_of_finite` to lift the geometric
translation `P + k` back to a SmoothPoint.

**Mathematical content** (geometric formulation): under the AlgEquiv
`τ_k`, evaluation behaves as
```
(τ_k f)(P) = f(P + k)
```
so `f` vanishes at `P + k` iff `τ_k f` vanishes at `P`. At the
discrete-valuation level, this means `τ_k` transports the maximal
ideal at `P + k` to the maximal ideal at `P` (as ideals of K(E),
restricted via the local-ring structure).

**Substantive obligation** (reduced to maximal-ideal transport): the
claim `pointValuation P (τ_k f) = pointValuation (P + k) f` is
equivalent to `(pointValuation P).comap τ_k.toRingHom = pointValuation
(P + k)` (as Valuations on K(E)).

Two valuations on the same field are equal iff they assign the same
value to every element. For our discrete valuations from local rings
of smooth points, equality reduces to the maximal-ideal-transport
identity under `τ_k`.

**Status**: shipped as a `Conditional` witness-parametric form taking
the maximal-ideal-transport hypothesis as input. The substantive
discharge of the maximal-ideal transport (using Worker A's
`translateAlgEquivOfPoint` x_gen / y_gen action lemmas + the smooth-point
maximal-ideal structure from `Curves/Basic.lean:60`) is the next
piece of the multi-session arc — Step (B') under that decomposition. -/

namespace Conditional

variable (C : SmoothPlaneCurve F) [DecidableEq F]
  [C.toAffine.IsElliptic]

/-- **Step (B), Conditional form**: transport of `pointValuation` under
the function-field-level translation `τ_k = translateAlgEquivOfPoint W k`,
witness-parametric on the maximal-ideal-transport identity.

depends_on: T-POLE-DIVISOR-FALLBACK Step (A) (`translate_of_finite`)
consumes: maximal-ideal-transport at the smooth-point level
(reduced sub-piece for the substantive geometric content). -/
theorem pointValuation_translate_of_smul_eq_of_transport_witness
    {P : C.SmoothPoint} {k : C.toAffine.Point}
    {h : (P.toAffinePoint + k).IsSome}
    (τ_k : C.FunctionField ≃+* C.FunctionField)
    (f : C.FunctionField)
    (h_eq : (C.pointValuation P).comap τ_k.toRingHom f =
      C.pointValuation (P.translate_of_finite k h) f) :
    C.pointValuation P (τ_k f) =
      C.pointValuation (P.translate_of_finite k h) f := by
  -- `(comap τ_k v) f = v (τ_k f)` by definition of comap.
  -- So h_eq directly gives the goal.
  exact h_eq

/-! ### Step (B') — Valuation-level reductions

Step (B) Conditional consumes the maximal-ideal-transport identity in
**pointwise** form: `(pointValuation P).comap τ_k.toRingHom f =
pointValuation (P+k) f` for a fixed `f`. The substantive **geometric
content** — the obligation we want to reduce to a single named statement —
is the underlying **Valuation equality**:

```
(pointValuation P).comap τ_k.toRingHom = pointValuation (P+k)
    -- as Valuations on K(E)
```

This is a stronger form: it says the two Valuations on `K(E)` agree as
functions `K(E) → ℤᵐ⁰`. By `Valuation.ext`, it is equivalent to the
universally-quantified pointwise form.

Step (B') ships:
* The **upgrade** direction: a witness `∀ f, ...` ⟹ Valuation equality.
* The **downgrade** direction: a witness Valuation equality ⟹ `∀ f, ...`.
* A Valuation-level Conditional consumer specialised for the eventual
  application: takes the Valuation-level hypothesis and discharges the
  pointwise transport identity for any single `f`.

These three pieces cleanly decouple the structural reduction from the
substantive geometric content. The remaining obligation — proving the
Valuation equality for our specific `τ_k = translateAlgEquivOfPoint W
k.val` — is **Step (B'')** of the multi-session arc, and connects to
Worker A's `translateAlgEquivOfPoint` x_gen / y_gen action lemmas
(`Hasse/IsogOneSubXyFamily.lean:283-320`) plus the smooth-point
maximal-ideal structure (`Curves/Basic.lean:60`). -/

/-- **Step (B') upgrade direction**: a pointwise transport witness for all
`f` upgrades to a Valuation equality. Direct from `Valuation.ext`. -/
theorem comap_pointValuation_eq_of_pointwise_transport
    {P : C.SmoothPoint} {k : C.toAffine.Point}
    {h : (P.toAffinePoint + k).IsSome}
    (τ_k : C.FunctionField ≃+* C.FunctionField)
    (h_eq : ∀ f, (C.pointValuation P).comap τ_k.toRingHom f =
      C.pointValuation (P.translate_of_finite k h) f) :
    (C.pointValuation P).comap τ_k.toRingHom =
      C.pointValuation (P.translate_of_finite k h) :=
  Valuation.ext h_eq

/-- **Step (B') downgrade direction**: a Valuation equality gives the
pointwise transport identity at every `f`. Direct from `congrFun`. -/
theorem pointwise_transport_of_comap_pointValuation_eq
    {P : C.SmoothPoint} {k : C.toAffine.Point}
    {h : (P.toAffinePoint + k).IsSome}
    (τ_k : C.FunctionField ≃+* C.FunctionField)
    (h_val_eq : (C.pointValuation P).comap τ_k.toRingHom =
      C.pointValuation (P.translate_of_finite k h))
    (f : C.FunctionField) :
    (C.pointValuation P).comap τ_k.toRingHom f =
      C.pointValuation (P.translate_of_finite k h) f := by
  rw [h_val_eq]

/-- **Step (B'), Conditional Valuation form**: transport of `pointValuation`
under the function-field-level translation `τ_k`, witness-parametric on
the **Valuation equality** form of the maximal-ideal-transport identity.

This is the cleaner, stronger formulation of Step (B) Conditional: instead
of taking the pointwise hypothesis at a single `f`, it takes the Valuation
equality (one Valuation, no quantifier) and discharges the pointwise
transport identity for any `f`.

depends_on: T-POLE-DIVISOR-FALLBACK Step (A) (`translate_of_finite`)
consumes: Valuation equality `(pointValuation P).comap τ_k =
pointValuation (P+k)` at the smooth-point level (the substantive
geometric content, Step (B'')). -/
theorem pointValuation_translate_of_smul_eq_of_valuation_witness
    {P : C.SmoothPoint} {k : C.toAffine.Point}
    {h : (P.toAffinePoint + k).IsSome}
    (τ_k : C.FunctionField ≃+* C.FunctionField)
    (h_val_eq : (C.pointValuation P).comap τ_k.toRingHom =
      C.pointValuation (P.translate_of_finite k h))
    (f : C.FunctionField) :
    C.pointValuation P (τ_k f) =
      C.pointValuation (P.translate_of_finite k h) f := by
  exact pointValuation_translate_of_smul_eq_of_transport_witness C τ_k f
    (pointwise_transport_of_comap_pointValuation_eq C τ_k h_val_eq f)

/-! ### Step (B') Valuation base case at k = 0

The Valuation-level base case: at `k = 0` (and any τ_k that's the identity
ring iso on K(E)), the comap is just `Valuation.comap_id`, giving the
Valuation equality trivially.

Specialised below to `RingEquiv.refl`, which models `translateAlgEquivOfPoint
W 0 = AlgEquiv.refl` at the RingHom level. The full `translateAlgEquivOfPoint`-
specific instantiation lives at the EC layer (where the AlgEquiv
infrastructure resides). -/

/-- **Step (B') base case**: when `τ_k = RingEquiv.refl` (the trivial
translation), the Valuation equality is `Valuation.comap_id`. The
`P.translate_of_finite 0 h = P` reduction (Step (A)) closes the goal. -/
theorem comap_pointValuation_refl_eq
    (P : C.SmoothPoint)
    (h : (P.toAffinePoint + (0 : C.toAffine.Point)).IsSome) :
    (C.pointValuation P).comap (RingEquiv.refl C.FunctionField).toRingHom =
      C.pointValuation
        (P.translate_of_finite (0 : C.toAffine.Point) h) := by
  rw [SmoothPoint.translate_of_finite_zero]
  change (C.pointValuation P).comap (RingHom.id _) = C.pointValuation P
  exact Valuation.comap_id _

end Conditional

end SmoothPlaneCurve

end HasseWeil.Curves
