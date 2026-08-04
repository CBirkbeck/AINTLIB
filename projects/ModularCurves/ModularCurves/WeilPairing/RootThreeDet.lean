/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree
import ModularCurves.Moduli.Bootstrap
import ModularCurves.WeilPairing.UniversalRootThree

/-!
# The `GL₂(ℤ/3)`-action on the level-three moduli object (WP-D3c-N3)

The last input of the DS4 construction (`nonempty_weilPairing_of_root_of_det`,
`WeilPairing/DetCocycle.lean`) is that the chosen root of unity transforms by `det` under a
change of trivialisation. At level three the root is the *explicit* element `e3Zeta`
(`WeilPairing/UniversalRootThree.lean`), so the statement becomes a concrete identity in
`E3ModuliRing R` — but it needs the `GL₂(ℤ/3)`-action on that ring, which is what this file
supplies.

Nothing new is constructed: `gammaFullNaiveGlAut` (`Moduli/Bootstrap.lean`) already gives
`GL₂(ℤ/N)` acting on the naive full-level *moduli problem*, and `universalE3Obj` represents
that problem at `N = 3`. Transporting an automorphism of a representable functor to its
representing object is `Functor.RepresentableBy.ofIso` followed by
`Functor.RepresentableBy.uniqueUpToIso`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace ModularCurves

variable (R : CommRingCat.{u})

/-- **(WP-D3c-N3)** The automorphism of the level-three moduli object induced by
`g ∈ GL₂(ℤ/3)`, obtained by transporting `gammaFullNaiveGlAut` through the representing
equivalence. -/
noncomputable def e3GlIso (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    universalE3Obj R ≅ universalE3Obj R :=
  (naiveLevelThreeRepresentableBy R hR hL hArb).uniqueUpToIso
    ((naiveLevelThreeRepresentableBy R hR hL hArb).ofIso (gammaFullNaiveGlAut R 3 g))

/-- **(WP-D3c-N3)** The induced automorphism of the level-three moduli **scheme**. -/
noncomputable def e3GlBaseIso (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Spec (CommRingCat.of (E3ModuliRing R)) ≅ Spec (CommRingCat.of (E3ModuliRing R)) where
  hom := (e3GlIso R hR hL hArb g).hom.baseHom
  inv := (e3GlIso R hR hL hArb g).inv.baseHom
  hom_inv_id := congrArg EllHom.baseHom (e3GlIso R hR hL hArb g).hom_inv_id
  inv_hom_id := congrArg EllHom.baseHom (e3GlIso R hR hL hArb g).inv_hom_id

/-- **(WP-D3c-N3)** …and hence of the ring `E3ModuliRing R`, read on global sections through
`Γ ∘ Spec`. This is the automorphism `σ_g` in which the determinant law
`σ_g (e3Zeta R) = e3Zeta R ^ (det g).val` is stated. -/
noncomputable def e3GlRingEquiv (hR : IsUnit (3 : R))
    (hL : (universalE3Obj R).curve.IsNaiveFullLevel 3
      (universalE3P R) (universalE3Q R))
    (hArb : ∀ (X : EllObj R) (L : X.curve.FullLevelPt 3), IsE3Datum X L)
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    E3ModuliRing R ≃+* E3ModuliRing R :=
  ((Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).symm ≪≫
      Scheme.Γ.mapIso (e3GlBaseIso R hR hL hArb g).op ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (E3ModuliRing R))).commRingCatIsoToRingEquiv

end ModularCurves
