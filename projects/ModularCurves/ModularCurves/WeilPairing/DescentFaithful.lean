/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import ModularCurves.WeilPairing.CharZeroAssembly

/-!
# Sections inject along a flat surjective cover (WP-C1)

Route A constructs the Weil pairing by descending an explicit determinant model along a
trivialising cover. Each of the eight DS4 specification theorems that `Y(ρ̄)` consumes is
then an equation **in `Γ(T, ⊤)`** — bilinearity, the symplectic formula, base-change
naturality — while the only place the pairing is computable is *on the cover*. This file
supplies the bridge: an equation between sections may be checked after restriction along a
flat surjective morphism.

The mechanism is entirely local. A flat morphism has flat stalk maps
(`AlgebraicGeometry.Flat.stalkMap`), a flat local homomorphism of local rings is faithfully
flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), and a faithfully flat ring map is
injective. Surjectivity of the underlying map then produces, for every point of the target,
a point of the source at which to test — so all germs of the difference vanish and the
sheaf axiom finishes.

Note that **no quasi-compactness is needed**: this is the germwise statement, not the
Amitsur equalizer. (The project's `ForMathlib/FaithfullyFlatEqualizer.lean` has the harder
half — the *image* of `Γ(T)` is the equalizer — which the descent construction itself uses;
here only injectivity is at stake.)

The mathlib proof of `AlgebraicGeometry.epi_of_flat_of_surjective` establishes the same
stalkwise injectivity en route to a statement about epimorphisms of schemes; that statement
does not give injectivity on sections, since `Γ` is not faithful.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace ModularCurves

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk maps of a flat morphism are injective: they are flat local homomorphisms of
local rings, hence faithfully flat. -/
theorem injective_stalkMap_of_flat [Flat f] (x : X) :
    Function.Injective (f.stalkMap x).hom := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency.types false in
/-- **(WP-C1)** Restriction along a flat surjective morphism is injective on sections over
any open of the target: two sections agreeing after pullback are equal.

This is what lets every `weilPairingEval` specification — an identity in `Γ(T, ⊤)` — be
verified on the trivialising cover, where the pairing is the explicit `ζ ^ det` formula. -/
theorem injective_app_of_flat_of_surjective [Flat f] [Surjective f] (U : Y.Opens) :
    Function.Injective (f.app U).hom := by
  intro s t hst
  refine TopCat.Presheaf.section_ext Y.sheaf U s t fun y hy => ?_
  obtain ⟨x, rfl⟩ := ‹Surjective f›.surj y
  -- `germ_stalkMap_apply` is applied as a term, not by `rw`: the sheaf-vs-presheaf
  -- spelling (`Y.sheaf.presheaf` from `section_ext` against `Y.presheaf` in the lemma)
  -- is definitional but not syntactic, so rewriting cannot see the pattern.
  refine injective_stalkMap_of_flat f x ?_
  exact (Scheme.Hom.germ_stalkMap_apply f U x hy s).trans
    ((congrArg (X.presheaf.germ (f ⁻¹ᵁ U) x hy).hom hst).trans
      (Scheme.Hom.germ_stalkMap_apply f U x hy t).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(WP-C1)** The global-sections form, which is the shape the DS4 specifications need:
`Γ(Y, ⊤) ⟶ Γ(X, ⊤)` is injective for `f` flat and surjective. -/
theorem injective_appTop_of_flat_of_surjective [Flat f] [Surjective f] :
    Function.Injective f.appTop.hom :=
  injective_app_of_flat_of_surjective f ⊤

set_option backward.isDefEq.respectTransparency.types false in
/-- **(WP-C1)** The form used at a `T`-point: an equation between global sections of `T` may
be checked after restriction along any flat surjective `q : T' ⟶ T`. Stated as an
`iff`-free implication because that is how the specification proofs consume it. -/
theorem eq_of_appTop_eq_of_flat_of_surjective [Flat f] [Surjective f]
    {s t : Γ(Y, (⊤ : Y.Opens))} (h : f.appTop.hom s = f.appTop.hom t) : s = t :=
  injective_appTop_of_flat_of_surjective f h

section BaseChange

variable {S S' T : Scheme.{u}} (p : S' ⟶ S) (g : T ⟶ S)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(WP-C1, the form the DS4 specifications consume)** A trivialising cover `p : S' ⟶ S`
of the base pulls back to a cover of any `S`-scheme `T`, along which sections of `T` still
inject. Every `weilPairingEval` identity lives in `Γ(T, ⊤)` for a varying `T`, so this — not
the cover of `S` itself — is the statement each specification proof calls. -/
theorem injective_appTop_pullback_of_flat_of_surjective [Flat p] [Surjective p] :
    Function.Injective (pullback.fst g p).appTop.hom :=
  injective_appTop_of_flat_of_surjective (pullback.fst g p)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(WP-C1)** The implication form: an identity between global sections of `T` holds as
soon as it holds after restriction to `T ×_S S'`. -/
theorem eq_of_pullback_appTop_eq [Flat p] [Surjective p]
    {s t : Γ(T, (⊤ : T.Opens))}
    (h : (pullback.fst g p).appTop.hom s = (pullback.fst g p).appTop.hom t) : s = t :=
  injective_appTop_pullback_of_flat_of_surjective p g h

end BaseChange

end ModularCurves
