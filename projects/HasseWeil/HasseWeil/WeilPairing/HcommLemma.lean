/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionGeometric
import HasseWeil.GapSpines

/-!
# The translation–isogeny pullback commutation (`hcomm`)

For a genuine isogeny `φ : E → E` and a point `S`, the function-field shadow of the group-law
commutation `φ ∘ (·+S) = (·+φS) ∘ φ`:

`τ_S ∘ φ* = φ* ∘ τ_{φS}`   (as `F`-algebra endomorphisms of `K(E)`),

equivalently, applied to any `g : K(E)`,

`τ_S (φ* g) = φ* (τ_{φS} g)`,

which is exactly the `hcomm` hypothesis consumed by `weilPairing_adjoint_picDual` /
`weilPairing_scaling` (`HasseWeil/WeilPairing/PairingAdjoint.lean`). Here `τ_P =
translateAlgEquivOfPoint W P` and `φ* = φ.pullback`, and `φS = φ.toAddMonoidHom S`.

## What genuineness gives, and the extra geometric input

`IsGenuineWith W φ g` (`HasseWeil/GapSpines.lean`) constrains the geometric action `g` of `φ` on
`K(E)`-points **only at the generic point**: `g (P_gen) = (φ* x_gen, φ* y_gen)`. Crucially the
function-field pullback `Point.map φ*` **fixes** lifted constant points (`φ*` fixes constants), so
`Point.map φ*` is *not* the geometric map `g` away from `P_gen`. Hence the commutation needs one
genuine geometric fact beyond `IsGenuineWith`: the point-level statement that
translating the image `g (P_gen)` by `S` adds the lift of `φS`,

`hgcomm : Point.map τ_S (g (P_gen)) = g (P_gen) + lift (φ.toAddMonoidHom S)`,

which is precisely `φ ∘ (·+S) = (·+φS) ∘ φ` read at the generic point. With these two inputs the
commutation is pure point bookkeeping: both `τ_S (φ* x_gen/y_gen)` and `φ* (τ_{φS} x_gen/y_gen)` are
the coordinates of `g (P_gen) + lift (φS)`, so the two `F`-algebra endos agree on the generators and
hence everywhere (`algHom_ext_x_y_gen`).

For `φ = [ℓ]` the witness is `g = (ℓ • ·)` and `φ.toAddMonoidHom S = ℓ • S`, and the `hgcomm` input
is automatic from `ℓ •`-linearity of `Point.map τ_S` — this is the shipped, hypothesis-free
`HasseWeil.ScratchCov.comm_algHom_mulByInt`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.8.2 (the translation covariance
behind the separable adjoint).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

set_option linter.unusedSectionVars false

/-- **The genuine bridge**: for an isogeny `φ` genuine with geometric action `g`, the function-field
pullback `Point.map φ*` agrees with `g` *at the generic point*. By definition `IsGenuineWith` gives
`g (P_gen) = some (φ* x_gen) (φ* y_gen)`, and `Point.map φ* (P_gen) = some (φ* x_gen) (φ* y_gen)` by
`Affine.Point.map_some`; the two `some`s have equal coordinates, hence are equal. -/
theorem map_pullback_genericPoint_of_isGenuineWith
    (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgen : IsGenuineWith W φ g) :
    WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback (HasseWeil.genericPoint W) =
      g (HasseWeil.genericPoint W) := by
  obtain ⟨X, Y, hns, hgP, hX, hY⟩ := hgen
  rw [hgP, HasseWeil.genericPoint_xOf_some]
  -- `Point.map φ* (some x_gen y_gen _) = some (φ* x_gen) (φ* y_gen) _`, matching `some X Y _`.
  refine (WeierstrassCurve.Affine.Point.map_some (f := φ.pullback) (generic_nonsingular W)).trans ?_
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hX.symm, hY.symm⟩

/-- **The translation–isogeny commutation at the generic point**: for `φ` genuine with action `g`
and the geometric point-commutation `hgcomm` (translating `g (P_gen)` by `S` adds `lift (φS)`),
`Point.map τ_S (Point.map φ* P_gen) = Point.map φ* (Point.map τ_{φS} P_gen)`.

Both sides equal `g (P_gen) + lift (φ.toAddMonoidHom S)`:
* LHS: `Point.map φ* P_gen = g (P_gen)` (genuine bridge), then `hgcomm`;
* RHS: `Point.map τ_{φS} P_gen = P_gen + lift (φS)` (master lemma), `Point.map φ*` is additive, and
  `Point.map φ*` fixes the lift `lift (φS)` (`φ*` fixes constants via `commutes`). -/
theorem hcomm_point_of_isGenuineWith
    (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
    (hgcomm : WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom (g (HasseWeil.genericPoint W)) =
      g (HasseWeil.genericPoint W) + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)) :
    WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback (HasseWeil.genericPoint W)) =
      WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback
        (WeierstrassCurve.Affine.Point.map (W' := W)
          (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S)).toAlgHom
          (HasseWeil.genericPoint W)) := by
  set φpb := WeierstrassCurve.Affine.Point.map (W' := W) φ.pullback with hφpb
  -- Common value `V := g (P_gen) + lift (φS)`.
  set V := g (HasseWeil.genericPoint W) + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S) with hV
  -- LHS: `Point.map τ_S (Point.map φ* P_gen) = Point.map τ_S (g P_gen) = V`.
  have hLHS : WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom (φpb (HasseWeil.genericPoint W)) = V := by
    rw [hφpb, map_pullback_genericPoint_of_isGenuineWith W φ hgen, hgcomm]
  -- RHS: `Point.map φ* (P_gen + lift (φS)) = Point.map φ* P_gen + Point.map φ* (lift (φS)) = V`.
  have hadd : φpb (HasseWeil.genericPoint W + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)) =
      φpb (HasseWeil.genericPoint W) +
        φpb (HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)) :=
    map_add φpb (HasseWeil.genericPoint W) (HasseWeil.liftPointToKE W (φ.toAddMonoidHom S))
  -- `Point.map φ*` fixes the lift of any constant point (`φ*` fixes constants via `commutes`).
  have hfix : φpb (HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)) =
      HasseWeil.liftPointToKE W (φ.toAddMonoidHom S) := by
    rcases h : φ.toAddMonoidHom S with _ | ⟨xk, yk, h_ns⟩
    · rw [hφpb]
      exact map_zero _
    · rw [hφpb, HasseWeil.liftPointToKE_some, HasseWeil.liftSomePoint]
      change Affine.Point.some (φ.pullback (algebraMap F KE xk))
        (φ.pullback (algebraMap F KE yk)) _ = _
      exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
        ⟨φ.pullback.commutes xk, φ.pullback.commutes yk⟩
  -- `Point.map φ* P_gen = g P_gen` (genuine bridge), packaged under `φpb`.
  have hbridge : φpb (HasseWeil.genericPoint W) = g (HasseWeil.genericPoint W) := by
    rw [hφpb]; exact map_pullback_genericPoint_of_isGenuineWith W φ hgen
  have hRHS : φpb (WeierstrassCurve.Affine.Point.map (W' := W)
          (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S)).toAlgHom
          (HasseWeil.genericPoint W)) = V := by
    rw [HasseWeil.translateAlgEquivOfPoint_map_genericPoint W (φ.toAddMonoidHom S), hadd, hfix,
      hbridge]
    exact hV.symm
  rw [hLHS, hRHS]

/-- **The translation–isogeny commutation, alg-hom form** (Silverman III.8.2): for `φ` genuine with
action `g` and the geometric point-commutation `hgcomm`, `τ_S ∘ φ* = φ* ∘ τ_{φS}` as `F`-algebra
endomorphisms of `K(E)`. By `algHom_ext_x_y_gen` this reduces to agreement on `x_gen, y_gen`, which
is the point identity `hcomm_point_of_isGenuineWith` read off in coordinates via `Point.map_map`. -/
theorem hcomm_algHom_of_isGenuineWith
    (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
    (hgcomm : WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom (g (HasseWeil.genericPoint W)) =
      g (HasseWeil.genericPoint W) + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S)) :
    (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom.comp φ.pullback =
      φ.pullback.comp
        (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S)).toAlgHom := by
  -- The point identity, rephrased via `map_map`.
  have hpt := hcomm_point_of_isGenuineWith W φ hgen S hgcomm
  rw [WeierstrassCurve.Affine.Point.map_map, WeierstrassCurve.Affine.Point.map_map] at hpt
  -- Read off coordinates: `Point.map f (some x_gen y_gen _) = some (f x_gen) (f y_gen) _` is `rfl`.
  rw [HasseWeil.genericPoint_xOf_some] at hpt
  obtain ⟨hx, hy⟩ := WeierstrassCurve.Affine.Point.some.inj hpt
  exact HasseWeil.algHom_ext_x_y_gen W hx hy

/-- **The translation–isogeny commutation, pointwise form** — exactly the `hcomm` hypothesis of
`weilPairing_adjoint_picDual` / `weilPairing_scaling`. For `φ` genuine with action `g` and the
geometric point-commutation `hgcomm`, for every `z : K(E)`:
`τ_S (φ* z) = φ* (τ_{φS} z)`. Pointwise shadow of `hcomm_algHom_of_isGenuineWith`. -/
theorem hcomm_of_isGenuineWith
    (φ : Isogeny W.toAffine W.toAffine)
    {g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point}
    (hgen : IsGenuineWith W φ g) (S : W.toAffine.Point)
    (hgcomm : WeierstrassCurve.Affine.Point.map (W' := W)
        (HasseWeil.translateAlgEquivOfPoint W S).toAlgHom (g (HasseWeil.genericPoint W)) =
      g (HasseWeil.genericPoint W) + HasseWeil.liftPointToKE W (φ.toAddMonoidHom S))
    (z : KE) :
    HasseWeil.translateAlgEquivOfPoint W S (φ.pullback z) =
      φ.pullback (HasseWeil.translateAlgEquivOfPoint W (φ.toAddMonoidHom S) z) := by
  have h := hcomm_algHom_of_isGenuineWith W φ hgen S hgcomm
  exact DFunLike.congr_fun h z

end HasseWeil.WeilPairing
