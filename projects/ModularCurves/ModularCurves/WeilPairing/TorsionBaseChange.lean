/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.MuNBaseChange

/-!
# The torsion algebra under base change of the field (WP-D3c-2c)

`muNCarrierBaseChange` (`WeilPairing/MuNBaseChange.lean`) transported the `μ_N` side of the
field-change comparison by reducing it to the explicit `AdjoinRoot` model. `E[N]` has no such
model, so its transport has to come from the cartesian square itself
(`torsion_baseChange_isPullback`, `EllipticCurve/TorsionFibre.lean`).

This file supplies the affineness that makes that possible: the torsion scheme of an elliptic
curve over an affine base is affine, so `Scheme.isoSpec` applies to all three corners of the
square and `AlgebraicGeometry.pullbackSpecIso` can be read off.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- **(WP-D3c-2c)** The `N`-torsion of an elliptic curve over an affine base is affine: its
structure morphism is finite (`torsionπ_isFinite`), hence affine. -/
instance isAffine_torsion [IsAffine S] : IsAffine (E.torsion N) :=
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  isAffine_of_isAffineHom (E.torsionπ N)

/-- **(WP-D3c-2c)** …and so is the torsion of a base change along a morphism from an affine
scheme, which is the other corner of `torsion_baseChange_isPullback`. -/
instance isAffine_torsion_baseChange {T : Scheme.{u}} [IsAffine T] (g : T ⟶ S) :
    IsAffine ((E.baseChange g).torsion N) :=
  haveI : IsFinite ((E.baseChange g).torsionπ N) := (E.baseChange g).torsionπ_isFinite N
  isAffine_of_isAffineHom ((E.baseChange g).torsionπ N)

/-- **(WP-D3c-2c)** The torsion base-change square, transported to `Spec`s of global-section
rings: every corner of `torsion_baseChange_isPullback` is affine, so `Scheme.isoSpec` carries
the cartesian square onto one whose four legs are `Spec.map` of ring maps.

All four commutation obligations of `IsPullback.of_iso` are the single lemma
`Scheme.isoSpec_hom_naturality`. -/
theorem isPullback_specMap_torsion_baseChange [IsAffine S] {T : Scheme.{u}} [IsAffine T]
    (g : T ⟶ S) :
    IsPullback (Spec.map ((E.torsionBaseChangeHom N g).appTop))
      (Spec.map (((E.baseChange g).torsionπ N).appTop))
      (Spec.map ((E.torsionπ N).appTop))
      (Spec.map (g.appTop)) :=
  (E.torsion_baseChange_isPullback N g).of_iso
    ((E.baseChange g).torsion N).isoSpec (E.torsion N).isoSpec T.isoSpec S.isoSpec
    (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
    (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm

end EllipticCurve

section Carrier

variable (k : Type u) [Field k] (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ)
  [NeZero N]

/-- The `k`-algebra structure that `finiteEtaleOfπ` installs on `Γ(E[N], ⊤)`, reconstructed by
the same expression so that it is usable outside that definition's scope — the exact analogue
of `muNCarrierAlgebra`. -/
@[reducible] noncomputable def torsionCarrierAlgebra :
    Algebra k Γ(E.torsion N, ⊤) :=
  (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop).hom).toAlgebra

attribute [local instance] torsionCarrierAlgebra

/-- **(WP-D3c-2c)** With that instance the algebra map *is* `ΓSpecIso.inv` followed by the
torsion's structure map — true by definition of `torsionCarrierAlgebra`, recorded so that
consumers need not unfold it. -/
theorem ofHom_algebraMap_torsionCarrier :
    CommRingCat.ofHom (algebraMap k Γ(E.torsion N, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E.torsionπ N).appTop :=
  rfl

/-- **(WP-D3c-2c)** …hence, after `Spec`, the leg that
`AlgebraicGeometry.pullbackSpecIso` expects at the `X`-corner factors through the
structure map of the torsion. -/
theorem specMap_ofHom_algebraMap_torsionCarrier :
    Spec.map (CommRingCat.ofHom (algebraMap k Γ(E.torsion N, ⊤))) =
      Spec.map ((E.torsionπ N).appTop) ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
  rw [ofHom_algebraMap_torsionCarrier, Spec.map_comp]

variable (k' : Type u) [Field k'] [Algebra k k']

attribute [local instance] torsionCarrierAlgebra

/-- **(WP-D3c-2c step 3b)** The torsion base-change square, with the two base corners written
as `Spec` of the *rings* rather than `Spec Γ(Spec _, ⊤)`.

A second `IsPullback.of_iso`, this time with `Scheme.isoSpec_Spec_inv` at the `Y`- and
`Z`-corners (`(Spec R).isoSpec.inv = Spec.map (ΓSpecIso R).inv`) — the shape
`AlgebraicGeometry.pullbackSpecIso` is stated in. -/
theorem isPullback_specMap_torsion_baseChange_algebraMap :
    IsPullback
      (Spec.map ((E.torsionBaseChangeHom N
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop))
      (Spec.map (((E.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).torsionπ N).appTop))
      (Spec.map ((E.torsionπ N).appTop))
      (Spec.map ((Spec.map (CommRingCat.ofHom (algebraMap k k'))).appTop)) :=
  E.isPullback_specMap_torsion_baseChange N (Spec.map (CommRingCat.ofHom (algebraMap k k')))

end Carrier

end ModularCurves
