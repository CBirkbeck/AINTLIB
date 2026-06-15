import HasseWeil.Curves.FrobeniusFixedLocus
import HasseWeil.EC.AffinePointMap
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric Frobenius on points over the algebraic closure (Route B, Step 2)

For a finite field `K` with `q = Fintype.card K` and a Weierstrass curve `W` over `K`,
base-changed to `L = AlgebraicClosure K`, this file builds the **geometric Frobenius**
endomorphism on the `L`-points,

```
geomFrobeniusPoint : (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point
```

acting as `(x, y) ↦ (x ^ q, y ^ q)` (and `0 ↦ 0`), via mathlib's `FiniteField.frobeniusAlgHom`
(`x ↦ x ^ q`, a `K`-algebra hom on `L`) transported to points by the project's
`HasseWeil.Affine.Point.map`. The codomain identification

```
(W.baseChange L).map (frobeniusAlgHom K L) = W.baseChange L
```

(`WeierstrassCurve.map_baseChange`, because the `q`-power map is a `K`-algebra hom and so
fixes the `algebraMap K L` image) makes this an *endomorphism* of the same point type.

It also packages the base-change inclusion of `K`-points

```
includePointBC : W.toAffine.Point →+ (W.baseChange L).toAffine.Point
```

via `HasseWeil.Affine.Point.map (algebraMap K L)`.

## Main result (Step 2 = S2)

* `HasseWeil.geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`:
  `geomFrobeniusPoint P = P ↔ P ∈ Set.range includePointBC`,
  the *point-level* fixed-locus theorem. Proof by cases on `P`:
  - `P = 0` is fixed and `0 = includePointBC 0`;
  - `P = (x, y)` is fixed iff `x ^ q = x ∧ y ^ q = y`, iff (by Step 1
    `frobenius_fixed_iff_mem_baseField`) both coordinates lie in `range (algebraMap K L)`,
    iff `P = includePointBC (x₀, y₀)`.

## Skeletons (S3/S4)

* `geomFrobeniusPoint_eq_includePoint_kernel` (S3): the forward inclusion `range includePointBC ⊆
  ker (id − geomFrobeniusPoint)` is `simp`; the statement here is the *equality* of
  `range includePointBC` with the fixed locus, which is exactly S2 repackaged for the
  `1 − π` kernel.  Stated and reduced to S2.
* `card_oneSubGeomFrobenius_kernel_eq_pointCount` (S4): `# ker(id − geomFrobeniusPoint) =
  pointCount W` — a `sorry` stub pending the `Fintype`/cardinality glue.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1.
* Step 1: `HasseWeil.frobenius_fixed_iff_mem_baseField` (`Curves/FrobeniusFixedLocus.lean`).
* mathlib: `FiniteField.frobeniusAlgHom`, `WeierstrassCurve.map_baseChange`,
  `WeierstrassCurve.Affine.Point.map`.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K)

local notation "L" => AlgebraicClosure K

noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

/-! ### The geometric Frobenius `K`-algebra hom and the codomain identification -/

/-- The geometric Frobenius `K`-algebra hom `x ↦ x ^ q` on `L = AlgebraicClosure K`,
as a ring hom. This is `FiniteField.frobeniusAlgHom K L`, coerced to a `RingHom`. -/
noncomputable def geomFrobRingHom : AlgebraicClosure K →+* AlgebraicClosure K :=
  (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom

@[simp] theorem geomFrobRingHom_apply (a : AlgebraicClosure K) :
    geomFrobRingHom (K := K) a = a ^ Fintype.card K := by
  show (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) a = a ^ Fintype.card K
  rw [FiniteField.coe_frobeniusAlgHom]

/-- **Codomain identification**: mapping the base-changed curve `W.baseChange L` over the
geometric Frobenius `q`-power `K`-algebra hom returns `W.baseChange L` itself.  Direct
from `WeierstrassCurve.map_baseChange` (the `q`-power map is a `K`-algebra hom, hence
fixes `algebraMap K L`). -/
@[simp] theorem map_geomFrob_baseChange_eq_self :
    (W.baseChange (AlgebraicClosure K)).map (geomFrobRingHom (K := K)) =
      W.baseChange (AlgebraicClosure K) := by
  show (W.baseChange (AlgebraicClosure K)).map
      (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom =
    W.baseChange (AlgebraicClosure K)
  rw [show (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).toRingHom =
      ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) :
        AlgebraicClosure K →ₐ[K] AlgebraicClosure K).toRingHom from rfl]
  rw [AlgHom.toRingHom_eq_coe]
  exact W.map_baseChange (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))

/-! ### Geometric Frobenius on points and the base-change inclusion -/

/-- The geometric Frobenius on `L`-points as a raw map: mathlib's
`WeierstrassCurve.Affine.Point.map` of the geometric Frobenius `K`-algebra hom
`frobeniusAlgHom K L : L →ₐ[K] L`.  Its codomain `W⟮L⟯ = Point (W.baseChange L)`
is **definitionally** `(W.baseChange L).toAffine.Point`, so no cast is needed.
This mirrors `frobeniusW_KE` in `Hasse/IsogOneSubXyFamily.lean`. -/
noncomputable def geomFrobeniusPointFun :
    (W.baseChange (AlgebraicClosure K)).toAffine.Point →
      (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))

@[simp] theorem geomFrobeniusPointFun_zero :
    geomFrobeniusPointFun W (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) = 0 := rfl

/-- **`geomFrobeniusPointFun` on `some`**: applies the geometric Frobenius `q`-power
to both coordinates.  Direct from `WeierstrassCurve.Affine.Point.map_some` together with
`FiniteField.coe_frobeniusAlgHom` (`frobeniusAlgHom = (· ^ q)`). -/
theorem geomFrobeniusPointFun_some {x y : AlgebraicClosure K}
    (h : (W.baseChange (AlgebraicClosure K)).toAffine.Nonsingular x y) :
    geomFrobeniusPointFun W (.some x y h) =
      .some
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x)
        ((FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) y)
        ((Affine.baseChange_nonsingular W.toAffine
          (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)).injective x y).mpr h) := by
  show WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) (.some x y h) = _
  exact WeierstrassCurve.Affine.Point.map_some
    (f := FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) h

/-- The base-change inclusion of `K`-points into `L`-points: `Affine.Point.map` of
`algebraMap K L`, with codomain re-typed via `WeierstrassCurve.map_id`-style identification
`(W.baseChange L) = (W.baseChange L)`.  Note `W.baseChange L = W.map (algebraMap K L)`
definitionally, so the codomain of `Affine.Point.map (algebraMap K L)` on
`W.toAffine.Point` is exactly `(W.baseChange L).toAffine.Point`. -/
noncomputable def includePointBC :
    W.toAffine.Point → (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  HasseWeil.Affine.Point.map (W := W) (algebraMap K (AlgebraicClosure K))
    (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K))

@[simp] theorem includePointBC_zero :
    includePointBC W (0 : W.toAffine.Point) = 0 := rfl

@[simp] theorem includePointBC_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    includePointBC W (.some x y h) =
      .some (algebraMap K (AlgebraicClosure K) x) (algebraMap K (AlgebraicClosure K) y)
        ((Affine.map_nonsingular W.toAffine
          (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) x y).mpr h) := rfl

/-- `includePointBC` is injective: it is `HasseWeil.Affine.Point.map` of the injective ring
hom `algebraMap K L`, and the constructor `some` is injective in its coordinates. -/
theorem includePointBC_injective : Function.Injective (includePointBC W) := by
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) hP
  · rfl
  · -- `includePointBC W 0 = 0`, `includePointBC W (some ..) = some ..` (both `rfl`):
    -- the hypothesis is `0 = some ..`, impossible.  `change` forces the definitional
    -- reduction of `includePointBC` on each constructor so `noConfusion` sees literals.
    change (Affine.Point.zero : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      = Affine.Point.some _ _ _ at hP
    exact absurd hP (by simp)
  · change (Affine.Point.some _ _ _ : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
      = Affine.Point.zero at hP
    exact absurd hP (by simp)
  · simp only [includePointBC_some, Affine.Point.some.injEq] at hP
    obtain ⟨hx, hy⟩ := hP
    have hx' : x₁ = x₂ := FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) hx
    have hy' : y₁ = y₂ := FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) hy
    subst hx' hy'
    rfl

/-! ### S2 — the point-level fixed-locus theorem

We work directly with the raw functions to keep the rewriting along
`map_geomFrob_baseChange_eq_self` explicit. The `0` case is reflexivity; the affine case
reduces, via `HasseWeil.Affine.Point.map_some` and `some.injEq`, to the conjunction
`x ^ q = x ∧ y ^ q = y`, which Step 1 (`frobenius_fixed_iff_mem_baseField`) turns into
membership of both coordinates in `range (algebraMap K L)`. -/

set_option maxHeartbeats 400000 in
/-- **S2 (point fixed-locus)**: a point `P` over the algebraic closure is fixed by the
geometric Frobenius iff it is the base-change inclusion of a `K`-rational point.

`geomFrobeniusPointFun P = P ↔ P ∈ Set.range (includePointBC W)`.

Proof by cases on `P`:
* `P = 0`: fixed, and `0 = includePointBC 0`.
* `P = some x y h`: `Frob P = P ↔ x ^ q = x ∧ y ^ q = y` (coordinatewise, by
  `Affine.Point.map_some` + `some.injEq`), and by Step 1 each coordinate is fixed iff it
  lies in `range (algebraMap K L)`; assembling the two `K`-rational coordinates back into a
  nonsingular `K`-point gives `P ∈ range includePointBC`.

  The coordinate algebra uses `WeierstrassCurve.Affine.map_nonsingular` (a *ring-hom*
  nonsingularity transfer, matching `includePointBC`'s own definition via
  `HasseWeil.Affine.Point.map`) rather than the AlgHom-based `baseChange_nonsingular`, which
  keeps the unifier off the doubly-base-changed curve term.

**PRECISE REMAINING GAP (mechanical, not mathematical).** All the substantive content is
in place — the codomain identification `map_geomFrob_baseChange_eq_self` (closed), Step 1
`frobenius_fixed_iff_mem_baseField` (closed), and the coordinate algebra
(`FiniteField.pow_card`, `baseChange_nonsingular`).  The only obstruction is transporting
the `Affine.Point.map` output across the **propositional** curve equality
`e : (W.baseChange L).map geomFrobRingHom = W.baseChange L` used in `geomFrobeniusPointFun`:
since `WeierstrassCurve.Affine.Point` is a structure *indexed by the curve term* and the two
sides of `e` are not definitionally equal (the LHS bakes in `(·^q) ∘ algebraMap`), `cases e`
/ `subst` fail ("dependent elimination failed").  Closing this needs an explicit
`Eq.rec`/`eqRec` transport lemma `geomFrobeniusPointFun_some` of the form
`geomFrobeniusPointFun W (.some x y h) = .some (x^q) (y^q) _`, proved by `Eq.mpr` rewriting
rather than `cases` — e.g. via a generic `Point.map` + `WeierstrassCurve.Affine.Point.map_some`
lemma stated with the codomain already rewritten by `congrArg (·.toAffine.Point) e`.
Alternatively, redefine `geomFrobeniusPointFun` to use mathlib's `Affine.Point.map`
(`Affine/Point.lean:793`) along the `K`-AlgHom `frobeniusAlgHom K L : L →ₐ[K] L`, whose
codomain `W'⟮L⟯ = Point (baseChange W' L)` is **definitionally** `(W.baseChange L).Point`
(no cast), mirroring `frobeniusW_KE` in `Hasse/IsogOneSubXyFamily.lean`. -/
theorem geomFrobeniusPoint_fixed_iff_mem_range_includePointBC
    (P : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    geomFrobeniusPointFun W P = P ↔ P ∈ Set.range (includePointBC W) := by
  rcases P with _ | ⟨x, y, h⟩
  · -- `P = 0`: fixed (`map_zero` is `rfl`), and `0 = includePointBC 0`.
    exact iff_of_true rfl ⟨0, includePointBC_zero W⟩
  · -- `P = some x y h`.  LHS reduces to `x ^ q = x ∧ y ^ q = y` (coordinatewise),
    -- each equivalent by Step 1 to membership in `range (algebraMap K L)`.
    rw [geomFrobeniusPointFun_some, Affine.Point.some.injEq]
    show (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) x = x ∧
        (FiniteField.frobeniusAlgHom K (AlgebraicClosure K)) y = y ↔ _
    rw [FiniteField.coe_frobeniusAlgHom]
    show x ^ Fintype.card K = x ∧ y ^ Fintype.card K = y ↔ _
    rw [frobenius_fixed_iff_mem_baseField, frobenius_fixed_iff_mem_baseField]
    constructor
    · -- both coordinates rational ⟹ `P` is the inclusion of a `K`-point.
      rintro ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩
      refine ⟨.some x₀ y₀ ?_, ?_⟩
      · exact (Affine.map_nonsingular W.toAffine
          (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)) x₀ y₀).mp h
      · rw [includePointBC_some]
    · -- `P` in the image ⟹ both coordinates rational.
      rintro ⟨Q, hQ⟩
      rcases Q with _ | ⟨x₀, y₀, h₀⟩
      · -- `includePointBC W 0 = 0` definitionally, contradicting `… = some …`.
        rw [show includePointBC W Affine.Point.zero
            = (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point) from rfl] at hQ
        exact absurd hQ (by simp)
      · rw [includePointBC_some] at hQ
        rw [Affine.Point.some.injEq] at hQ
        exact ⟨⟨x₀, hQ.1⟩, ⟨y₀, hQ.2⟩⟩

/-! ### S3 — kernel of `1 − π` over `L` = image of `E(K)`

Reviewer's cleanest target. The forward inclusion `range includePointBC ⊆
{P | geomFrobeniusPointFun P = P}` is the "rational ⇒ fixed" direction (a rational `P`
has `(1 − π)P = P − πP = P − P = 0`); the reverse is the substantive S2 content.  As an
*equality of sets* this is literally S2 (`geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`)
repackaged, so we state it that way and reduce to S2. -/

/-- **S3 (set form)**: the fixed locus of the geometric Frobenius equals the image of the
`K`-rational points.  This is S2 in `Set` form; once S2 is closed this is unconditional. -/
theorem fixedLocus_geomFrobenius_eq_range_includePointBC :
    {P : (W.baseChange (AlgebraicClosure K)).toAffine.Point | geomFrobeniusPointFun W P = P} =
      Set.range (includePointBC W) := by
  ext P
  exact geomFrobeniusPoint_fixed_iff_mem_range_includePointBC W P

/-! ### S4 — cardinality glue (skeleton)

The final glue: `# ker(id − geomFrobeniusPoint) = pointCount W`.  Once S2/S3 identify the
fixed locus with `range includePointBC`, and `includePointBC` is injective (it is
`Affine.Point.map` of an injective ring hom, see `WeierstrassCurve.Affine.Point.map_injective`),
the fixed locus is in bijection with `W.toAffine.Point`, whose cardinality is `pointCount W`.
Combined with the algebraic-closed fibre count
(`CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`) this yields
`deg(1 − π) = pointCount`.

Stated as a `sorry` stub with the intended signature; needs the `Fintype` instance on the
fixed locus / the bijection-to-`W.toAffine.Point` cardinality step. -/

/-- **S4 (cardinality, skeleton)**: the number of geometric-Frobenius-fixed `L`-points equals
the `K`-rational point count `Fintype.card W.toAffine.Point` (= `pointCount`).  Reduces to S3
(`fixedLocus … = range includePointBC`) plus injectivity of `includePointBC`; the
`Fintype`/`Nat.card` glue is the remaining gap. -/
theorem ncard_fixedLocus_geomFrobenius_eq_pointCount [Fintype W.toAffine.Point] :
    {P : (W.baseChange (AlgebraicClosure K)).toAffine.Point |
        geomFrobeniusPointFun W P = P}.ncard = Fintype.card W.toAffine.Point := by
  rw [fixedLocus_geomFrobenius_eq_range_includePointBC,
    Set.ncard_range_of_injective (includePointBC_injective W),
    Nat.card_eq_fintype_card]

/-! ### PRIORITY 1 — kernel of `id − geomFrobenius` over `L`

The geometric Frobenius on `L`-points is already mathlib's
`WeierstrassCurve.Affine.Point.map (frobeniusAlgHom K L)`, an `AddMonoidHom`
`(W.baseChange L)⟮L⟯ →+ (W.baseChange L)⟮L⟯` whose `.toFun` is definitionally
`geomFrobeniusPointFun W` (mirroring `frobeniusW_KE` in
`Hasse/IsogOneSubXyFamily.lean`). We bundle it, form `1 − π` as an
`AddMonoidHom`, and identify its kernel with the fixed locus. -/

/-- **Geometric Frobenius on `L`-points as an `AddMonoidHom`**: mathlib's
`Affine.Point.map (frobeniusAlgHom K L)`. Its `.toFun` is definitionally
`geomFrobeniusPointFun W`. -/
noncomputable def geomFrobeniusPoint :
    (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W)
    (FiniteField.frobeniusAlgHom K (AlgebraicClosure K))

@[simp] theorem geomFrobeniusPoint_apply
    (P : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    geomFrobeniusPoint W P = geomFrobeniusPointFun W P := rfl

/-- **`1 − π` on `L`-points as an `AddMonoidHom`**: the identity minus the
geometric Frobenius. Its group-kernel is the geometric-Frobenius fixed locus
(`ker_oneSubGeomFrobHom_eq_fixedLocus`). -/
noncomputable def oneSubGeomFrobHom :
    (W.baseChange (AlgebraicClosure K)).toAffine.Point →+
      (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  AddMonoidHom.id _ - geomFrobeniusPoint W

@[simp] theorem oneSubGeomFrobHom_apply
    (P : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    oneSubGeomFrobHom W P = P - geomFrobeniusPointFun W P := rfl

/-- **PRIORITY 1 (kernel = fixed locus)**: `P ∈ ker(id − geomFrob) ⟺
geomFrob P = P`. Direct from `sub_eq_zero`. -/
theorem ker_oneSubGeomFrobHom_eq_fixedLocus :
    ((oneSubGeomFrobHom W).ker : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point) =
      {P | geomFrobeniusPointFun W P = P} := by
  ext P
  rw [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_setOf_eq, oneSubGeomFrobHom_apply,
    sub_eq_zero, eq_comm]

/-- **PRIORITY 1 (cardinality)**: the geometric-Frobenius fixed locus, i.e.
`ker(id − geomFrob)`, has cardinality `pointCount W`. Composes
`ker_oneSubGeomFrobHom_eq_fixedLocus` with S4
(`ncard_fixedLocus_geomFrobenius_eq_pointCount`). -/
theorem ncard_ker_oneSubGeomFrobHom_eq_pointCount [Fintype W.toAffine.Point] :
    ((oneSubGeomFrobHom W).ker :
        Set (W.baseChange (AlgebraicClosure K)).toAffine.Point).ncard =
      Fintype.card W.toAffine.Point := by
  rw [ker_oneSubGeomFrobHom_eq_fixedLocus,
    ncard_fixedLocus_geomFrobenius_eq_pointCount]

end HasseWeil
