/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# The equalizer of morphisms into an unramified scheme is open ([RIG-1b])

Mirror of mathlib's `isClosedImmersion_equalizer_ι_left` (Stacks 01KM: the equalizer of
two `S`-morphisms into a separated `S`-scheme is a closed immersion) with the separated
diagonal replaced by the OPEN diagonal of an unramified finite-type morphism
(`isOpenImmersion_diagonal`, Stacks 02GE): the equalizer of two `S`-morphisms into an
unramified finite-type `S`-scheme is an **open** immersion.

Consequence (`Over.hom_ext_of_unramified_of_surjective`): two `S`-morphisms into an
unramified finite-type `S`-scheme whose agreement locus meets every point of the source
are equal. This is the detection engine of [RIG-1]: an automorphism of an elliptic
curve agreeing with the identity on every geometric fibre of the (finite étale)
`N`-torsion agrees with it globally on `E[N]`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **(Stacks 02GE-flavoured mirror of 01KM)** The equalizer of two `S`-morphisms into an
unramified finite-type `S`-scheme is an open immersion. -/
instance isOpenImmersion_equalizer_ι_left {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsOpenImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

/-- **([RIG-1b] detection engine)** Two `S`-morphisms into an unramified finite-type
`S`-scheme whose equalizer meets every point of the source are equal: the equalizer is
an open immersion (`isOpenImmersion_equalizer_ι_left`) with full range, hence an
isomorphism, and cancelling it in `equalizer.condition` gives `f = g`. -/
theorem Over.hom_ext_of_unramified_of_surjective {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (hsurj : Function.Surjective (equalizer.ι f g).left.base) : f = g := by
  haveI : IsIso (equalizer.ι f g).left := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    refine TopologicalSpace.Opens.ext ?_
    exact Set.range_eq_univ.mpr hsurj
  haveI : IsIso ((CategoryTheory.Over.forget S).map (equalizer.ι f g)) :=
    inferInstanceAs (IsIso (equalizer.ι f g).left)
  haveI : IsIso (equalizer.ι f g) :=
    isIso_of_reflects_iso (equalizer.ι f g) (CategoryTheory.Over.forget S)
  exact (cancel_epi (equalizer.ι f g)).mp (equalizer.condition f g)

end AlgebraicGeometry
