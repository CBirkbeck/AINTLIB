import HasseWeil.Curves.PointFunctor
import HasseWeil.Curves.Infinity
import HasseWeil.MulByIntPullback
import HasseWeil.FrobeniusIsogeny
import Mathlib.FieldTheory.Finite.Basic

/-!
# Isogenies between elliptic curves (algebro-geometric definition)

Following Silverman III.4, an isogeny `φ : E₁ → E₂` between elliptic curves is
a morphism of varieties satisfying `φ(O) = O`. We model this by extending the
`CurveMap` substrate (the function-field pullback) with one structural witness:

* a basepoint-preservation hypothesis stated at the level of the local ring at
  infinity, capturing "the morphism is defined at the basepoint" (regular
  functions at `∞` pull back to regular functions at `∞`).

The `AddMonoidHom` structure on points (Silverman III.4.8) is **not** stored as
data; it is a *theorem* about an isogeny. The `CoordHom` witness needed to
derive the points-functor is supplied as **separate data** (when available),
not as a structural field — this matches the Silverman-style design where some
isogenies (notably `[n]` for `n ≥ 2`) are projective morphisms whose
function-field pullback does not restrict to the affine coordinate ring (their
image of `x` has poles at the `n`-torsion).

## Main definitions

* `HasseWeil.EC.Isogeny` — the isogeny structure (function-field pullback +
  basepoint preservation).
* `HasseWeil.EC.Isogeny.toPointMap` — the induced map on `Affine.Point`,
  parametrized by an external `CoordHom` witness.
* `HasseWeil.EC.Isogeny.id`, `compose`, `frobenius`, `mulByInt` — the standard
  constructions, each with separately-defined `*CoordHom` witnesses where
  available.
* `HasseWeil.EC.Isogeny.degree`, `separableDegree`, `inseparableDegree`,
  `IsSeparable`, `IsPurelyInseparable` — inherited from `CurveMap`.

## Caveat on basepoint preservation

The current `pullback_ordAtInfty_nonneg` field captures "morphism is defined at
the basepoint" (regular functions pull back to regular functions). It does not
strictly capture `φ(O) = O` — that would require the strict-positive form
`0 < ord_∞ f → 0 < ord_∞ pullback f`. A future refinement may strengthen this.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4 (definition,
  Theorem III.4.8 on group-hom property)
-/

open WeierstrassCurve
open scoped Polynomial.Bivariate

namespace HasseWeil.EC

variable {F : Type*} [Field F]

/-! ### The Isogeny structure -/

/-- An isogeny `φ : E₁ → E₂` between elliptic Weierstrass curves over `F`. The
underlying datum is a `CurveMap` (function-field pullback) together with a
basepoint-defined-ness condition. The point map and coord-ring witness are
*not* part of the structure — they are supplied separately.

Reference: Silverman III.4 (definition). -/
structure Isogeny (W₁ W₂ : Affine F)
    [W₁.IsElliptic] [W₂.IsElliptic]
    extends Curves.CurveMap ⟨W₁⟩ ⟨W₂⟩ where
  /-- Basepoint preservation: the pullback of a function regular at infinity is
      regular at infinity (the morphism is defined at `O₁`). -/
  pullback_ordAtInfty_nonneg :
    ∀ f : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
        (toCurveMap.pullback f)

namespace Isogeny

variable {W₁ W₂ W₃ : Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- The pullback of an isogeny is injective. -/
theorem pullback_injective (φ : Isogeny W₁ W₂) :
    Function.Injective φ.toCurveMap.pullback :=
  φ.toCurveMap.pullback_injective

/-! ### Inherited degree API -/

/-- The degree of an isogeny: `[K(E₁) : φ*K(E₂)]`. Inherited from `CurveMap`. -/
noncomputable abbrev degree (φ : Isogeny W₁ W₂) : ℕ := φ.toCurveMap.degree

/-- The separable degree of an isogeny. Inherited from `CurveMap`. -/
noncomputable abbrev separableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  φ.toCurveMap.separableDegree

/-- The inseparable degree of an isogeny. Inherited from `CurveMap`. -/
noncomputable abbrev inseparableDegree (φ : Isogeny W₁ W₂) : ℕ :=
  φ.toCurveMap.inseparableDegree

/-- An isogeny is separable iff its inseparable degree is `1`. -/
abbrev IsSeparable (φ : Isogeny W₁ W₂) : Prop := φ.toCurveMap.IsSeparable

/-- An isogeny is purely inseparable iff its separable degree is `1`. -/
abbrev IsPurelyInseparable (φ : Isogeny W₁ W₂) : Prop :=
  φ.toCurveMap.IsPurelyInseparable

/-! ### The induced point map (parametrized by a coord-ring witness) -/

/-- The map of `F`-rational points `Affine.Point W₁ → Affine.Point W₂` induced
by an isogeny **together with** a coordinate-ring witness `coordHom`. The
basepoint at infinity (`Point.zero`) is sent to itself; a finite point
(`Point.some`) is mapped via the underlying `CurveMap.toPointMap`, then promoted
back via `SmoothPoint.toAffinePoint`. -/
noncomputable def toPointMap (φ : Isogeny W₁ W₂) (coordHom : φ.toCurveMap.CoordHom) :
    W₁.Point → W₂.Point
  | .zero => .zero
  | .some x y h =>
    (φ.toCurveMap.toPointMap coordHom ⟨x, y, h⟩).toAffinePoint

@[simp] theorem toPointMap_zero (φ : Isogeny W₁ W₂)
    (coordHom : φ.toCurveMap.CoordHom) :
    φ.toPointMap coordHom .zero = .zero := rfl

@[simp] theorem toPointMap_some (φ : Isogeny W₁ W₂)
    (coordHom : φ.toCurveMap.CoordHom)
    {x y : F} (h : W₁.Nonsingular x y) :
    φ.toPointMap coordHom (.some x y h) =
      (φ.toCurveMap.toPointMap coordHom ⟨x, y, h⟩).toAffinePoint := rfl

/-! ### Identity isogeny -/

/-- The identity isogeny on `W`: pullback is `AlgHom.id`, basepoint preservation
is trivial since the pullback fixes every function. -/
noncomputable def id (W : Affine F) [W.IsElliptic] : Isogeny W W where
  toCurveMap := Curves.CurveMap.id ⟨W⟩
  pullback_ordAtInfty_nonneg _ h := h

@[simp] theorem id_toCurveMap (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).toCurveMap = Curves.CurveMap.id ⟨W⟩ := rfl

/-- The natural coordinate-ring witness for the identity isogeny. -/
noncomputable def idCoordHom (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).toCurveMap.CoordHom :=
  Curves.CurveMap.CoordHom.id ⟨W⟩

/-- The identity isogeny is the identity on the basepoint. -/
@[simp] theorem id_toPointMap_zero (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).toPointMap (idCoordHom W) .zero = .zero := rfl

set_option maxHeartbeats 800000 in
/-- The identity isogeny is the identity on points: with the identity coord-ring
witness, `(Isogeny.id W).toPointMap` is the identity function on `W.Point`. -/
@[simp] theorem id_toPointMap (W : Affine F) [W.IsElliptic] (P : W.Point) :
    (Isogeny.id W).toPointMap (idCoordHom W) P = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    show ((Curves.CurveMap.toPointMap
      (Curves.CurveMap.CoordHom.id (⟨W⟩ : Curves.SmoothPlaneCurve F))
      (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve F).SmoothPoint)
      ).toAffinePoint : W.Point) = .some x y h
    rw [Curves.CurveMap.toPointMap_id]
    rfl

/-- The identity isogeny has degree `1`. -/
@[simp] theorem id_degree (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).degree = 1 :=
  Curves.CurveMap.degree_id ⟨W⟩

/-! ### Composition of isogenies -/

/-- Composition of isogenies `ψ ∘ φ : E₁ → E₃`. The pullback composes
contravariantly, the basepoint condition composes through both.

Named `compose` rather than `comp` to avoid clashing with `Function.comp`
during dot-notation resolution. -/
noncomputable def compose (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) : Isogeny W₁ W₃ where
  toCurveMap := ψ.toCurveMap.comp φ.toCurveMap
  pullback_ordAtInfty_nonneg := fun f h ↦
    φ.pullback_ordAtInfty_nonneg (ψ.toCurveMap.pullback f)
      (ψ.pullback_ordAtInfty_nonneg f h)

@[simp] theorem compose_toCurveMap (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.compose φ).toCurveMap = ψ.toCurveMap.comp φ.toCurveMap := rfl

/-- The natural coordinate-ring witness for the composition of two isogenies
each with their own coord-ring witnesses. -/
noncomputable def composeCoordHom {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (ψ_cd : ψ.toCurveMap.CoordHom) (φ_cd : φ.toCurveMap.CoordHom) :
    (ψ.compose φ).toCurveMap.CoordHom :=
  ψ_cd.comp φ_cd

/-- Composition of isogenies acts as composition on points (basepoint case). -/
@[simp] theorem compose_toPointMap_zero (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂)
    (ψ_cd : ψ.toCurveMap.CoordHom) (φ_cd : φ.toCurveMap.CoordHom) :
    (ψ.compose φ).toPointMap (composeCoordHom ψ_cd φ_cd) .zero =
      ψ.toPointMap ψ_cd (φ.toPointMap φ_cd .zero) := rfl

set_option maxHeartbeats 800000 in
/-- Composition of isogenies acts as composition on points (full version). -/
@[simp] theorem compose_toPointMap (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂)
    (ψ_cd : ψ.toCurveMap.CoordHom) (φ_cd : φ.toCurveMap.CoordHom) (P : W₁.Point) :
    (ψ.compose φ).toPointMap (composeCoordHom ψ_cd φ_cd) P =
      ψ.toPointMap ψ_cd (φ.toPointMap φ_cd P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    show ((ψ.toCurveMap.comp φ.toCurveMap).toPointMap (ψ_cd.comp φ_cd)
      (⟨x, y, h⟩ : (⟨W₁⟩ : Curves.SmoothPlaneCurve F).SmoothPoint)).toAffinePoint = _
    rw [Curves.CurveMap.toPointMap_comp]
    rfl

/-- **Degree multiplicativity**: `deg(ψ ∘ φ) = deg(φ) · deg(ψ)`. Follows from
the tower law for field extensions, inherited from `CurveMap.degree_comp`. -/
theorem compose_degree (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.compose φ).degree = φ.degree * ψ.degree :=
  Curves.CurveMap.degree_comp ψ.toCurveMap φ.toCurveMap

end Isogeny

/-! ### Group-homomorphism property of the induced point map (Silverman III.4.8)

`Add W.Point` requires `[DecidableEq F]`, so we open a fresh section with that
hypothesis. -/

namespace Isogeny

variable {W₁ W₂ W₃ : Affine F}
  [DecidableEq F] [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- **The group-homomorphism property** (Silverman III.4.8): the induced point
map of an isogeny respects addition. Stated parametrically over the coord-ring
witness, since `toPointMap` requires one. -/
def AddHomProperty (φ : Isogeny W₁ W₂) (coordHom : φ.toCurveMap.CoordHom) : Prop :=
  ∀ P Q : W₁.Point,
    φ.toPointMap coordHom (P + Q) =
      φ.toPointMap coordHom P + φ.toPointMap coordHom Q

/-- The bundled `AddMonoidHom` derived from an isogeny + coord witness +
proof of the group-hom property. -/
noncomputable def toAddMonoidHomOfWitness
    (φ : Isogeny W₁ W₂) (coordHom : φ.toCurveMap.CoordHom)
    (h : φ.AddHomProperty coordHom) :
    W₁.Point →+ W₂.Point where
  toFun := φ.toPointMap coordHom
  map_zero' := φ.toPointMap_zero coordHom
  map_add' := h

@[simp] theorem toAddMonoidHomOfWitness_apply
    (φ : Isogeny W₁ W₂) (coordHom : φ.toCurveMap.CoordHom)
    (h : φ.AddHomProperty coordHom) (P : W₁.Point) :
    φ.toAddMonoidHomOfWitness coordHom h P = φ.toPointMap coordHom P := rfl

/-- The identity isogeny satisfies the group-hom property (its `toPointMap` is
the identity, which is trivially a homomorphism). -/
theorem id_AddHomProperty (W : Affine F) [W.IsElliptic] :
    (Isogeny.id W).AddHomProperty (idCoordHom W) := by
  intro P Q
  simp [id_toPointMap]

/-- Composition of group-hom isogenies satisfies the group-hom property:
homomorphisms compose to homomorphisms. -/
theorem compose_AddHomProperty
    (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂)
    (ψ_cd : ψ.toCurveMap.CoordHom) (φ_cd : φ.toCurveMap.CoordHom)
    (hψ : ψ.AddHomProperty ψ_cd) (hφ : φ.AddHomProperty φ_cd) :
    (ψ.compose φ).AddHomProperty (composeCoordHom ψ_cd φ_cd) := by
  intro P Q
  rw [compose_toPointMap, compose_toPointMap, compose_toPointMap, hφ, hψ]

end Isogeny

/-! ### The Frobenius isogeny -/

section Frobenius

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
  (W : Affine K) [W.IsElliptic]

/-- The `q`-th power Frobenius isogeny on an elliptic curve over a finite field
`K` of size `q := #K`. Its pullback is `f ↦ f^q` on the function field. The
basepoint at infinity is preserved because `ord_∞` multiplies by `q` under
`f ↦ f^q`, taking nonnegative orders to nonnegative.
Reference: Silverman III.4.6. -/
noncomputable def Isogeny.frobenius : Isogeny W W where
  toCurveMap := { pullback := FiniteField.frobeniusAlgHom K W.FunctionField }
  pullback_ordAtInfty_nonneg := fun f h ↦ by
    change 0 ≤ (⟨W⟩ : Curves.SmoothPlaneCurve K).ordAtInfty
      (FiniteField.frobeniusAlgHom K W.FunctionField f)
    rw [show (FiniteField.frobeniusAlgHom K W.FunctionField) f =
      f ^ Fintype.card K from
      congr_fun (FiniteField.coe_frobeniusAlgHom (K := K)
        (R := W.FunctionField)) f]
    by_cases hf : f = 0
    · simp [hf]
    · rw [(⟨W⟩ : Curves.SmoothPlaneCurve K).ordAtInfty_pow hf]
      exact nsmul_nonneg h _

@[simp] theorem Isogeny.frobenius_pullback (f : W.FunctionField) :
    (Isogeny.frobenius W).toCurveMap.pullback f = f ^ Fintype.card K :=
  congr_fun (FiniteField.coe_frobeniusAlgHom (K := K) (R := W.FunctionField)) f

/-- The natural coordinate-ring witness for Frobenius: Frobenius `f ↦ f^q`
restricts to the coordinate ring (since `R^q ⊆ R` and the algebra map commutes
with powers). -/
noncomputable def Isogeny.frobeniusCoordHom :
    (Isogeny.frobenius W).toCurveMap.CoordHom where
  toAlgHom := FiniteField.frobeniusAlgHom K W.CoordinateRing
  compat := fun u ↦ by
    change FiniteField.frobeniusAlgHom K W.FunctionField
        (algebraMap W.CoordinateRing W.FunctionField u) =
      algebraMap W.CoordinateRing W.FunctionField
        (FiniteField.frobeniusAlgHom K W.CoordinateRing u)
    simp only [FiniteField.coe_frobeniusAlgHom, map_pow]

/-- The Frobenius isogeny has degree `q := #K`. Inherits from
`HasseWeil.frobenius_finrank_functionField`. Reference: Silverman III.4.6. -/
@[simp] theorem Isogeny.frobenius_degree :
    (Isogeny.frobenius W).degree = Fintype.card K :=
  HasseWeil.frobenius_finrank_functionField K W

/-- **Frobenius coordinate-evaluation step.** Evaluating a pulled-back
coordinate-ring element `r` through the Frobenius coordinate hom at a smooth
point `(x, y)` equals the `q`-th power (`q := #K`) of the plain evaluation:
Frobenius acts as `r ↦ r^q` on `W.CoordinateRing`, and `evalAt` is a ring hom,
so it commutes with the power. This is the common core of both the `x`- and
`y`-coordinate computations in `Isogeny.frobenius_toPointMap`. -/
private theorem Isogeny.frobenius_evalAtPullback {x y : K}
    (h : W.Nonsingular x y) (r : W.CoordinateRing) :
    Curves.CurveMap.evalAtPullback (Isogeny.frobeniusCoordHom W)
        (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve K).SmoothPoint) r =
      (Curves.SmoothPlaneCurve.evalAt (⟨W⟩ : Curves.SmoothPlaneCurve K)
        ⟨x, y, h⟩ r) ^ Fintype.card K := by
  rw [Curves.CurveMap.evalAtPullback_apply]
  change Curves.SmoothPlaneCurve.evalAt (⟨W⟩ : Curves.SmoothPlaneCurve K)
      ⟨x, y, h⟩ (FiniteField.frobeniusAlgHom K W.CoordinateRing r) = _
  rw [show (FiniteField.frobeniusAlgHom K W.CoordinateRing) r =
      r ^ Fintype.card K from
      congr_fun (FiniteField.coe_frobeniusAlgHom (K := K)
        (R := W.CoordinateRing)) r,
    map_pow]

set_option maxHeartbeats 800000 in
/-- The Frobenius isogeny acts as the **identity** on `K`-rational points: for
any `(x, y) ∈ W(K)`, Frobenius sends `(x, y) ↦ (x^q, y^q) = (x, y)` since
`x^q = x` for all `x ∈ K` by `FiniteField.pow_card`. The basepoint is
preserved by definition. -/
@[simp] theorem Isogeny.frobenius_toPointMap (P : W.Point) :
    (Isogeny.frobenius W).toPointMap (Isogeny.frobeniusCoordHom W) P = P := by
  cases P with
  | zero => rfl
  | some x y h =>
    show ((Curves.CurveMap.toPointMap
      (Isogeny.frobeniusCoordHom W)
      (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve K).SmoothPoint)
      ).toAffinePoint : W.Point) = .some x y h
    -- The SmoothPoint produced by toPointMap has coords (x^q, y^q), which equal
    -- (x, y) on K-rational points via pow_card.
    have h_sp_eq : Curves.CurveMap.toPointMap (Isogeny.frobeniusCoordHom W)
        (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve K).SmoothPoint) =
      ⟨x, y, h⟩ := by
      ext
      · -- x-coord: `(evalAt x)^q = x` by `evalAt_x` then `pow_card`.
        change Curves.CurveMap.evalAtPullback (Isogeny.frobeniusCoordHom W)
          (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve K).SmoothPoint)
          (WeierstrassCurve.Affine.CoordinateRing.mk W
            (Polynomial.C Polynomial.X)) = x
        rw [Isogeny.frobenius_evalAtPullback W h,
          Curves.SmoothPlaneCurve.evalAt_x, FiniteField.pow_card]
      · -- y-coord: `(evalAt y)^q = y` by `evalAt_y` then `pow_card`.
        change Curves.CurveMap.evalAtPullback (Isogeny.frobeniusCoordHom W)
          (⟨x, y, h⟩ : (⟨W⟩ : Curves.SmoothPlaneCurve K).SmoothPoint)
          (WeierstrassCurve.Affine.CoordinateRing.mk W Y) = y
        rw [Isogeny.frobenius_evalAtPullback W h,
          Curves.SmoothPlaneCurve.evalAt_y, FiniteField.pow_card]
    rw [h_sp_eq]
    rfl

/-- The Frobenius isogeny satisfies the group-hom property on `K`-rational
points: since its `toPointMap` is the identity (by `frobenius_toPointMap`), the
group-hom property is trivially satisfied. -/
theorem Isogeny.frobenius_AddHomProperty :
    (Isogeny.frobenius W).AddHomProperty (Isogeny.frobeniusCoordHom W) := by
  intro P Q
  simp [Isogeny.frobenius_toPointMap]

end Frobenius

/-! ### Multiplication-by-`n` isogeny

The endomorphism `[n] : E → E` is constructed via the function-field pullback
`mulByInt_pullbackAlgHom` from `HasseWeil/MulByIntPullback.lean` (built from
division polynomials).

The basepoint condition `pullback_ordAtInfty_nonneg` for `[n]` is genuinely
non-trivial — it requires the ramification-theoretic fact that
`ord_∞([n]*f) = e · ord_∞(f)` for some positive integer `e` (the local
ramification index of `[n]` at `O`). For now we expose this as an explicit
hypothesis (`mulByIntOfBasepoint`); a follow-up ticket will discharge it via
the existing `mulByInt_finrank` infrastructure or a dedicated valuation
extension argument.

Note that `[n]` does *not* admit a `coordHom` witness in the affine model —
its pullback of `x` is `Φ_n / Ψ_n²`, a fraction with poles at the
`n`-torsion. Hence `Isogeny.toPointMap` cannot be invoked for `mulByInt`
directly via the affine route; this is the design reason for separating
`coordHom` from the structure. -/

section MulByInt

-- `mulByInt_pullbackAlgHom` requires `[DecidableEq F]`; add it for this section.
variable [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- Predicate: the basepoint hypothesis for `mulByInt n` is the `ord_∞`-
nonneg-preserving condition on `mulByInt_pullbackAlgHom`. -/
abbrev MulByIntBasepoint {n : ℤ} (hn : n ≠ 0) : Prop :=
  ∀ f : (⟨W⟩ : Curves.SmoothPlaneCurve F).FunctionField,
    0 ≤ (⟨W⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
    0 ≤ (⟨W⟩ : Curves.SmoothPlaneCurve F).ordAtInfty
      (HasseWeil.mulByInt_pullbackAlgHom W n hn f)

/-- The multiplication-by-`n` isogeny for `n ≠ 0`, given a basepoint witness.
Builds an `Isogeny W W` whose function-field pullback is
`mulByInt_pullbackAlgHom W n hn`.

The basepoint witness `h_basepoint` discharges the `pullback_ordAtInfty_nonneg`
field. For separable `[n]` (n coprime to `char F`), `ord_∞` is preserved
exactly; for inseparable `[n]`, it scales by a positive integer; in both
cases the witness holds. -/
noncomputable def Isogeny.mulByIntOfBasepoint {n : ℤ} (hn : n ≠ 0)
    (h_basepoint : MulByIntBasepoint W hn) :
    Isogeny W W where
  toCurveMap := { pullback := HasseWeil.mulByInt_pullbackAlgHom W n hn }
  pullback_ordAtInfty_nonneg := h_basepoint

@[simp] theorem Isogeny.mulByIntOfBasepoint_pullback {n : ℤ} (hn : n ≠ 0)
    (h_basepoint : MulByIntBasepoint W hn) (f : W.FunctionField) :
    (Isogeny.mulByIntOfBasepoint W hn h_basepoint).toCurveMap.pullback f =
      HasseWeil.mulByInt_pullbackAlgHom W n hn f := rfl

end MulByInt

/-! ### Universal group-homomorphism property: bundled `WithHom` isogenies

This is the working framework for **Silverman III.4.8** (every isogeny is a
group homomorphism). Silverman's argument uses `Pic⁰(E) ≅ E` and the
contravariant functoriality of the Picard variety on morphisms; alternative
routes go via the formal group of `E` or direct addition-formula computation.

In our setup, the unconditional theorem is genuinely hard — it reduces to one
of those upstream infrastructures, none of which are fully in the project yet.
Instead, we package the **closure under standard constructions**: any isogeny
built from `id`, `compose`, and `frobenius` automatically carries an
`AddHomProperty`, hence a bundled `AddMonoidHom` on points.

The `WithHom` bundle below is the canonical recipient of these closure
operations. Future extensions (mulByInt, neg, dual, factor-through-Frobenius,
…) should provide their own `WithHom` instances by discharging the
`AddHomProperty` witness.

## Proof routes for the universal version

Silverman's three known routes for the universal Silverman III.4.8:

1. **Pic⁰ route** (Silverman III.4.8 proper). Uses
   `σ : Pic⁰(E) ≅ E` (Silverman III.3.4) — gated on `T-III-3-004` in this
   project. The induced pullback `φ_* : Pic⁰(E₁) → Pic⁰(E₂)` is a hom by
   functoriality, and the diagram with σ commutes when `φ(O) = O`.

2. **Formal-group route** (deformation argument). An isogeny pulls back to a
   formal-group hom on `Ê`. The hom property holds on the formal neighborhood
   of `O`, then extends to all of `E` by translation invariance and density.
   Requires the bridge `HasseWeil.Isogeny → HasseWeil.FormalGroupHom`, not yet
   built.

3. **Addition-formula route** (direct computation). Use the explicit
   `Affine.addX/addY` formulas; show that any `F`-algebra hom on `K(E)` that
   restricts to coord rings preserves these (an algebra-homs-respect-rational-
   functions argument). Requires `addPullbackAlgHom` from
   `HasseWeil/AdditionPullback.lean` (currently has 3 transcendence sorries).

All three reduce the universal claim to upstream infrastructure that is
modular: once any one route's gates are filled, `silvermanIII48_via_<route>`
can be added as a one-liner taking the upstream output as a witness. -/

namespace Isogeny

variable {W₁ W₂ W₃ : Affine F}
  [DecidableEq F] [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- An isogeny bundled with a coordinate-ring witness and a proof of the
group-homomorphism property. Every `WithHom` immediately yields an
`AddMonoidHom` on rational points via `toAddMonoidHom`. -/
structure WithHom (W₁ W₂ : Affine F)
    [W₁.IsElliptic] [W₂.IsElliptic] [DecidableEq F] where
  /-- The underlying isogeny. -/
  toIsogeny : Isogeny W₁ W₂
  /-- The coordinate-ring witness. -/
  coordHom : toIsogeny.toCurveMap.CoordHom
  /-- The group-homomorphism property, proven for this isogeny + witness. -/
  addHomProp : toIsogeny.AddHomProperty coordHom

namespace WithHom

/-- The bundled `AddMonoidHom` derived from a `WithHom`. -/
noncomputable def toAddMonoidHom (φ : WithHom W₁ W₂) : W₁.Point →+ W₂.Point :=
  φ.toIsogeny.toAddMonoidHomOfWitness φ.coordHom φ.addHomProp

@[simp] theorem toAddMonoidHom_apply (φ : WithHom W₁ W₂) (P : W₁.Point) :
    φ.toAddMonoidHom P = φ.toIsogeny.toPointMap φ.coordHom P := rfl

/-- The degree of a `WithHom` isogeny (inherited). -/
noncomputable abbrev degree (φ : WithHom W₁ W₂) : ℕ := φ.toIsogeny.degree

/-! #### Identity, composition -/

/-- The identity `WithHom`. -/
noncomputable def id (W : Affine F) [W.IsElliptic] : WithHom W W :=
  ⟨Isogeny.id W, idCoordHom W, id_AddHomProperty W⟩

@[simp] theorem id_toIsogeny (W : Affine F) [W.IsElliptic] :
    (WithHom.id W).toIsogeny = Isogeny.id W := rfl

@[simp] theorem id_coordHom_eq (W : Affine F) [W.IsElliptic] :
    (WithHom.id W).coordHom = idCoordHom W := rfl

/-- The identity `WithHom` is the identity on points. -/
@[simp] theorem id_toAddMonoidHom_apply (W : Affine F) [W.IsElliptic]
    (P : W.Point) : (WithHom.id W).toAddMonoidHom P = P := by
  show (Isogeny.id W).toPointMap (idCoordHom W) P = P
  exact Isogeny.id_toPointMap W P

/-- Composition of `WithHom` isogenies. -/
noncomputable def compose (ψ : WithHom W₂ W₃) (φ : WithHom W₁ W₂) :
    WithHom W₁ W₃ :=
  ⟨ψ.toIsogeny.compose φ.toIsogeny,
   composeCoordHom ψ.coordHom φ.coordHom,
   compose_AddHomProperty _ _ _ _ ψ.addHomProp φ.addHomProp⟩

@[simp] theorem compose_toIsogeny (ψ : WithHom W₂ W₃) (φ : WithHom W₁ W₂) :
    (ψ.compose φ).toIsogeny = ψ.toIsogeny.compose φ.toIsogeny := rfl

@[simp] theorem compose_coordHom_eq (ψ : WithHom W₂ W₃) (φ : WithHom W₁ W₂) :
    (ψ.compose φ).coordHom = composeCoordHom ψ.coordHom φ.coordHom := rfl

/-- Composition of `WithHom` acts as composition on the underlying point maps. -/
@[simp] theorem compose_toAddMonoidHom_apply
    (ψ : WithHom W₂ W₃) (φ : WithHom W₁ W₂) (P : W₁.Point) :
    (ψ.compose φ).toAddMonoidHom P =
      ψ.toAddMonoidHom (φ.toAddMonoidHom P) := by
  show (ψ.toIsogeny.compose φ.toIsogeny).toPointMap
      (composeCoordHom ψ.coordHom φ.coordHom) P =
    ψ.toIsogeny.toPointMap ψ.coordHom (φ.toIsogeny.toPointMap φ.coordHom P)
  exact Isogeny.compose_toPointMap _ _ _ _ P

/-- **Degree multiplicativity** for `WithHom`. -/
theorem compose_degree (ψ : WithHom W₂ W₃) (φ : WithHom W₁ W₂) :
    (ψ.compose φ).degree = φ.degree * ψ.degree :=
  Isogeny.compose_degree ψ.toIsogeny φ.toIsogeny

/-! #### Free corollaries from the `AddMonoidHom` packaging -/

/-- A `WithHom` isogeny preserves zero. -/
@[simp] theorem map_zero (φ : WithHom W₁ W₂) :
    φ.toAddMonoidHom 0 = 0 := φ.toAddMonoidHom.map_zero

/-- A `WithHom` isogeny preserves addition. -/
theorem map_add (φ : WithHom W₁ W₂) (P Q : W₁.Point) :
    φ.toAddMonoidHom (P + Q) = φ.toAddMonoidHom P + φ.toAddMonoidHom Q :=
  φ.toAddMonoidHom.map_add P Q

/-- A `WithHom` isogeny preserves negation. -/
theorem map_neg (φ : WithHom W₁ W₂) (P : W₁.Point) :
    φ.toAddMonoidHom (-P) = -φ.toAddMonoidHom P :=
  φ.toAddMonoidHom.map_neg P

/-- A `WithHom` isogeny preserves subtraction. -/
theorem map_sub (φ : WithHom W₁ W₂) (P Q : W₁.Point) :
    φ.toAddMonoidHom (P - Q) = φ.toAddMonoidHom P - φ.toAddMonoidHom Q :=
  φ.toAddMonoidHom.map_sub P Q

/-- A `WithHom` isogeny commutes with integer scalar multiplication. -/
theorem map_zsmul (φ : WithHom W₁ W₂) (n : ℤ) (P : W₁.Point) :
    φ.toAddMonoidHom (n • P) = n • φ.toAddMonoidHom P :=
  φ.toAddMonoidHom.map_zsmul n P

/-- A `WithHom` isogeny commutes with natural-number scalar multiplication. -/
theorem map_nsmul (φ : WithHom W₁ W₂) (n : ℕ) (P : W₁.Point) :
    φ.toAddMonoidHom (n • P) = n • φ.toAddMonoidHom P :=
  φ.toAddMonoidHom.map_nsmul n P

/-- Composing with the identity `WithHom` on the right preserves the
underlying point map. -/
@[simp] theorem id_compose_toAddMonoidHom (φ : WithHom W₁ W₂) (P : W₁.Point) :
    ((WithHom.id W₂).compose φ).toAddMonoidHom P = φ.toAddMonoidHom P := by
  rw [compose_toAddMonoidHom_apply, id_toAddMonoidHom_apply]

/-- Composing with the identity `WithHom` on the left preserves the underlying
point map. -/
@[simp] theorem compose_id_toAddMonoidHom (φ : WithHom W₁ W₂) (P : W₁.Point) :
    (φ.compose (WithHom.id W₁)).toAddMonoidHom P = φ.toAddMonoidHom P := by
  rw [compose_toAddMonoidHom_apply, id_toAddMonoidHom_apply]

end WithHom

end Isogeny

/-- The Frobenius isogeny as a bundled `WithHom`. (Lives in its own section
to capture the `Fintype K`, `DecidableEq K` typeclasses.) -/
noncomputable def Isogeny.WithHom.frobenius
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : Affine K) [W.IsElliptic] : Isogeny.WithHom W W :=
  ⟨Isogeny.frobenius W,
   Isogeny.frobeniusCoordHom W,
   Isogeny.frobenius_AddHomProperty W⟩

@[simp] theorem Isogeny.WithHom.frobenius_toIsogeny
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : Affine K) [W.IsElliptic] :
    (Isogeny.WithHom.frobenius W).toIsogeny = Isogeny.frobenius W := rfl

@[simp] theorem Isogeny.WithHom.frobenius_coordHom_eq
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : Affine K) [W.IsElliptic] :
    (Isogeny.WithHom.frobenius W).coordHom = Isogeny.frobeniusCoordHom W := rfl

/-- Frobenius as a `WithHom` is the identity on `K`-rational points. -/
@[simp] theorem Isogeny.WithHom.frobenius_toAddMonoidHom_apply
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : Affine K) [W.IsElliptic] (P : W.Point) :
    (Isogeny.WithHom.frobenius W).toAddMonoidHom P = P := by
  show (Isogeny.frobenius W).toPointMap (Isogeny.frobeniusCoordHom W) P = P
  exact Isogeny.frobenius_toPointMap W P

/-! ### Future extensions (mulByInt, neg, dual)

For each of the following, providing a `WithHom` instance requires both a
coord-ring lift (often non-trivial) and the `AddHomProperty` proof:

* `mulByInt n` for `n ≥ 2`: the affine coord-ring lift doesn't naturally
  exist (image of `x` is `Φₙ/Ψₙ²`, with poles at the `n`-torsion). Resolution
  requires a localization-based `CoordHom` or a projective coord model.

* `neg` (the `[-1]` isogeny): `(x, y) ↦ (x, -y - a₁x - a₃)`. Has a clean
  affine coord-ring lift via `Affine.negY`. The `AddHomProperty` is
  `-(P+Q) = -P + -Q`, which holds by `neg_add` on the abelian group `W.Point`.
  Construction is straightforward in principle but requires explicit
  `AlgHom` building from the negY formula on the function field.

* `dual α`: requires the existence-uniqueness of the dual isogeny
  (Silverman III.6.1), gated on either Pic⁰ or kernel/factorization
  infrastructure (`T-III-6-001` in the project ticket board). -/

end HasseWeil.EC
