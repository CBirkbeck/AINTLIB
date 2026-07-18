/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.Rigidity
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Rigidity / canonicity of the group law over an arbitrary base, via spreading out

`ModularCurves.EllipticCurve.Rigidity` proves the rigidity lemma (GIT Prop 6.1) and its
corollary `isMonHom_of_one_comp_eq'` (GIT Cor 6.4) — a pointed morphism of proper-flat-
`O`-connected group objects is a homomorphism — but only over a **locally noetherian** base
`S`. The noetherian hypothesis is genuinely used: the proof bottoms out at a Krull
intersection (`Ideal.iInf_pow_eq_bot_of_isLocalRing`, needing noetherian local stalks) to
upgrade "equality on every artinian thickening of a fibre" to "equality on an open
neighbourhood".

This file removes the noetherian hypothesis for morphisms **of finite presentation**, by
*spreading out* to the noetherian case. The mechanism is standard (EGA IV §8 / Stacks
"Limits of Schemes", tag `01YT`), and most of the machinery is already in mathlib
(`AffineTransitionLimit.lean`); the noetherian result is applied as a black box at a finite
stage.

## The reduction (source: Stacks "Limits of Schemes")

The headline conclusion `μ[A] ≫ f = tensorHom f f ≫ μ[G]` is an **equality of two
`S`-morphisms `A ⊗ A ⟶ G` into a separated target `G`**. Equality of morphisms is local on
the base and spreads out, so:

1. **`affineLocal`** — the equality is local on `S`: it holds iff it holds after base change
   to each affine open `Spec R ⊆ S` (`Gₐ = G ×ₛ Spec R ↪ G` is an open immersion, hence a
   monomorphism). Reduces to `S = Spec R` affine — which sidesteps the hard qcqs absolute
   noetherian approximation (Stacks `01ZA`), because for affine `S` one only needs the
   *elementary* fact that `R` is the filtered colimit of its finite-type-`ℤ` (noetherian)
   subalgebras.

2. **`Spec R = lim Spec Rⱼ`** over the directed system of finite-type-`ℤ` subalgebras `Rⱼ`,
   with affine transition maps and each `Spec Rⱼ` noetherian. (Ring-level colimit foundation:
   `Mathlib/Algebra/Category/Ring/FinitePresentation.lean`.)

3. **Descend the configuration** `(A, G, μ[A], μ[G], f, GrpObj, proper/flat/separated/lfp,
   O-connected)` to a finite noetherian stage `Spec Rⱼ` (Stacks `01ZM`(1),(2) — objects and
   morphisms of finite presentation descend; `081D` — their properties descend). *This is the
   only part not already in mathlib.*

4. **Apply the noetherian `isMonHom_of_one_comp_eq'`** at the noetherian stage `Spec Rⱼ`.

5. **Base change back** `Spec R → Spec Rⱼ` (functoriality; free) to obtain the equality over
   `Spec R`, hence — with step 1 — over `S`.

The load-bearing hypothesis is **finite presentation** of `A.hom` and `G.hom`: Stacks `01ZM`
is false without it. The noetherian version got local-finite-presentation for free from
noetherianness; here it must be assumed. In the intended application (`A = projModel`, an
elliptic-curve model cut out by explicit Weierstrass equations) it holds.

## Main result

* `isMonHom_of_one_comp_eq'_of_finitePresentation`: `isMonHom_of_one_comp_eq'` with
  `[IsLocallyNoetherian S]` replaced by `[LocallyOfFinitePresentation A.hom]` and
  `[LocallyOfFinitePresentation G.hom]`.

## References

* Mumford, *Geometric Invariant Theory*, Prop 6.1 / Cor 6.4 (the noetherian rigidity lemma).
* Stacks Project, "Limits of Schemes" (tag `01YT`): `01ZA` (absolute noetherian
  approximation), `01ZM` (descending relative objects, morphisms, and equalities of
  morphisms), `081D`/`081E`/`01ZP`/`01ZQ` (descending properties of morphisms), `01ZC`
  (finite presentation ⟺ `Hom`-sets commute with cofiltered limits).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- **(T-W7.8, GIT Cor 6.4 over an arbitrary base)** The pointed-morphism-of-group-objects
is-a-homomorphism theorem `isMonHom_of_one_comp_eq'`, with the locally-noetherian hypothesis
on the base removed in exchange for **finite presentation** of the structure morphisms.
Proved by spreading out to the noetherian case (see the module docstring). -/
theorem isMonHom_of_one_comp_eq'_of_finitePresentation {S : Scheme.{u}}
    {A G : Over S} [GrpObj A] [GrpObj G]
    [IsProper A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    (hO : UniversallyOConnected A.hom)
    [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    (f : A ⟶ G) (hη : η[A] ≫ f = η[G]) :
    μ[A] ≫ f = MonoidalCategory.tensorHom f f ≫ μ[G] := by
  sorry

end ModularCurves
