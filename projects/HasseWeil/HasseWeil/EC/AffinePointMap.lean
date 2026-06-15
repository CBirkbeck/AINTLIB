import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Functorial action of ring homs on `Affine.Point` (T-III-4-020b-2, Phase 0a)

For an injective ring homomorphism `f : R →+* S` and a Weierstrass curve `W`
over `R`, we build the natural map
`Affine.Point.map f : W.toAffine.Point → (W.map f).toAffine.Point`
which sends `zero` to `zero` and `some x y h` to `some (f x) (f y) _`.

mathlib provides `map_nonsingular` (`Affine/Basic.lean:278`) which shows that
nonsingularity of `(x, y)` transfers to nonsingularity of `(f x, f y)` on
`W.map f` under an injective `f`. We package this into the functorial
`Point.map`.

## Main definition

* `HasseWeil.Affine.Point.map` — the map `W.Point → (W.map f).Point` for an
  injective ring homomorphism `f : R →+* S`.

This is Phase 0a of T-III-4-020b-2. Phases 0b (`map_add`) and 0c (`map_zsmul`)
build the group-hom properties on top.

## References

* mathlib: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`
* Silverman, *The Arithmetic of Elliptic Curves*, III.4 (group law).
-/

open WeierstrassCurve

namespace HasseWeil.Affine.Point

variable {R S : Type*} [CommRing R] [CommRing S] {W : WeierstrassCurve R}
    (f : R →+* S) (hf : Function.Injective f)

/-- The natural map `W.toAffine.Point → (W.map f).toAffine.Point` induced by
    an injective ring homomorphism `f : R →+* S`. It sends `zero` to `zero`
    and `some x y h` to `some (f x) (f y) _`, using that nonsingularity
    transfers under an injective ring hom (mathlib's `map_nonsingular`). -/
noncomputable def map : W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h)

@[simp] theorem map_zero : map f hf (.zero : W.toAffine.Point) = .zero := rfl

@[simp] theorem map_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    map f hf (.some x y h) =
      .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h) :=
  rfl

end HasseWeil.Affine.Point

/-! ### Phase 0b: `Affine.Point.map` is additive

Here we restrict to ring homs between fields, since `Affine.Point` only has
`Add` over a field. Using mathlib's equivariance lemmas
(`Affine.map_negY`, `map_addX`, `map_addY`, `map_slope`) the case analysis
of `Point.add` goes through mechanically. -/

namespace HasseWeil.Affine.Point

variable {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    {W : WeierstrassCurve F} (f : F →+* F')

/-- `Point.map f` is additive on points over a field: it commutes with the
    group law. Case analysis on mathlib's `Point.add`:
    * `(0, P)`, `(P, 0)` : trivial via `map_zero`.
    * `some + some` with Y-cancellation : both sides are `0` (preserved under `f`).
    * `some + some` without Y-cancellation : both sides are `some (addX ...) (addY ...)`,
      and `f` commutes with `addX`, `addY`, `slope`, `negY` (mathlib equivariance). -/
theorem map_add (P Q : W.toAffine.Point) :
    map f f.injective (P + Q) = map f f.injective P + map f f.injective Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · change map f f.injective Q = (0 : (W.map f).toAffine.Point) + map f f.injective Q
    rw [zero_add]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · change map f f.injective (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) =
      map f f.injective (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) + 0
    rw [add_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have h_Y_eq_f : f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂) := by
      rw [hy, WeierstrassCurve.Affine.map_negY]
    rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
    change (0 : (W.map f).toAffine.Point) =
      map f f.injective (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
      map f f.injective (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    rw [map_some, map_some,
      WeierstrassCurve.Affine.Point.add_of_Y_eq (congr_arg f hx) h_Y_eq_f]
  · have hxy_f : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hfx, hfy⟩
      apply hxy
      refine ⟨f.injective hfx, f.injective ?_⟩
      rw [hfy, WeierstrassCurve.Affine.map_negY]
    rw [WeierstrassCurve.Affine.Point.add_some hxy]
    change map f f.injective (WeierstrassCurve.Affine.Point.some _ _ _) =
      map f f.injective (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) +
      map f f.injective (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    rw [map_some, map_some, map_some,
      WeierstrassCurve.Affine.Point.add_some hxy_f]
    congr 1
    · rw [WeierstrassCurve.Affine.map_slope, WeierstrassCurve.Affine.map_addX]
    · rw [WeierstrassCurve.Affine.map_slope, WeierstrassCurve.Affine.map_addY]

/-- `Point.map f` preserves negation: `-map f P = map f (-P)`. -/
theorem map_neg (P : W.toAffine.Point) :
    -map f f.injective P = map f f.injective (-P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · change WeierstrassCurve.Affine.Point.some _ _ _ =
      map f f.injective (WeierstrassCurve.Affine.Point.some _ _ _)
    rw [map_some]
    congr 1
    exact WeierstrassCurve.Affine.map_negY f x y

/-- `Point.map f` packaged as an `AddMonoidHom`. Uses `map_add` and `map_zero`
    to witness the additive structure. -/
noncomputable def mapAddMonoidHom :
    W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun := map f f.injective
  map_zero' := map_zero f f.injective
  map_add' := map_add f

/-- `Point.map f` commutes with integer scalar multiplication. Direct from
    `AddMonoidHom.map_zsmul` since `mapAddMonoidHom` is an `AddMonoidHom`. -/
theorem map_zsmul (n : ℤ) (P : W.toAffine.Point) :
    map f f.injective (n • P) = n • map f f.injective P :=
  (mapAddMonoidHom f).map_zsmul n P

end HasseWeil.Affine.Point
