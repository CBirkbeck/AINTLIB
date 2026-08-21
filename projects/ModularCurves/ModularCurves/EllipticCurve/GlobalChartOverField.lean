/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.InvariantDifferential

/-!
# Every elliptic curve over a field has a *global* Weierstrass chart (DS4 M1c-1)

The record `EllipticCurveGeom S` only asks for the local model *Zariski-locally on `S`*
(`LocallyWeierstrass`). Over `S = Spec k` with `k` a field this is no restriction: `Spec k`
is a one-point space, so the affine open produced by `localModel` is already `⊤` and the
chart is global.

* `localPresentationTop` — the resulting `LocalPresentation G ⟨⊤, _⟩`;
* `globalWeierstrassModel` — its Weierstrass curve over `Γ(Spec k, ⊤)`.

This is the input the field-level DS4 construction needs in order to run
`WeilPairing/FibrePointDict.lean`'s `chartAffinePointEquiv` at the geometric point of a
curve over `Spec k` — there is no chart to choose, the presentation covers everything.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace

namespace ModularCurves

variable {k : Type u} [Field k]

/-- Over `Spec k` (`k` a field) every open containing a point is everything: the space is a
single point. -/
theorem eq_top_of_mem_specField {U : (Spec (CommRingCat.of k)).Opens}
    {s : ↥(Spec (CommRingCat.of k))} (hs : s ∈ U) : U = ⊤ :=
  TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x =>
    (Subsingleton.elim x s : x = s) ▸ hs)

/-- **(DS4 M1c-1 ★)** Every geometric elliptic curve over `Spec k`, `k` a field, carries a
**global** Weierstrass presentation: the affine open supplied by the local-model field is
forced to be `⊤`, since `Spec k` is a one-point space. -/
theorem nonempty_localPresentation_top (G : EllipticCurveGeom (Spec (CommRingCat.of k))) :
    Nonempty (LocalPresentation G ⟨⊤, isAffineOpen_top _⟩) := by
  obtain ⟨U, hsU, W, hell, e, heπ, hez⟩ :=
    G.localModel (default : ↥(Spec (CommRingCat.of k)))
  have hU : U = (⟨⊤, isAffineOpen_top _⟩ : (Spec (CommRingCat.of k)).affineOpens) :=
    Subtype.ext (eq_top_of_mem_specField hsU)
  subst hU
  exact ⟨{ data := { W := W, elliptic := hell }
           chart := { e := e, compat_π := heπ, compat_zero := hez } }⟩

/-- **(DS4 M1c-1)** A choice of global Weierstrass presentation over a field. -/
noncomputable def localPresentationTop (G : EllipticCurveGeom (Spec (CommRingCat.of k))) :
    LocalPresentation G ⟨⊤, isAffineOpen_top _⟩ :=
  (nonempty_localPresentation_top G).some

/-- **(DS4 M1c-1)** The global Weierstrass model of an elliptic curve over a field, as a
Weierstrass curve over `Γ(Spec k, ⊤)`. -/
noncomputable def globalWeierstrassModel (G : EllipticCurveGeom (Spec (CommRingCat.of k))) :
    WeierstrassCurve Γ(Spec (CommRingCat.of k), (⊤ : (Spec (CommRingCat.of k)).Opens)) :=
  (localPresentationTop G).W

instance globalWeierstrassModel_isElliptic
    (G : EllipticCurveGeom (Spec (CommRingCat.of k))) :
    (globalWeierstrassModel G).IsElliptic :=
  (localPresentationTop G).elliptic

end ModularCurves
