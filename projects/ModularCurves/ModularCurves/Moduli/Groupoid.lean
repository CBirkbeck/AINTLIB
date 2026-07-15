/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.EndomorphismDegree
import ModularCurves.Moduli.EllCategory

/-!
# Groupoid-valued moduli of elliptic curves

This file defines pointed morphisms between elliptic curves over a fixed base and their
isomorphism classes. It also proves that full level structures of level at least three kill
automorphisms.

## Main definitions

* `HomOver`: pointed morphisms of elliptic curves over a fixed base.
* `IsoClasses`: isomorphism classes of elliptic curves over a fixed base.

## Main results

* `aut_hom_eq_id_of_fullLevel`: an automorphism fixing a full level structure is the identity.
* `aut_trivial_of_fullLevel`: the corresponding automorphism is the identity isomorphism.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- A pointed morphism of elliptic curves over a fixed base scheme, not necessarily an
isomorphism. -/
@[ext]
structure HomOver (E E' : EllipticCurve S) where
  hom : E.E ⟶ E'.E
  over_w : hom ≫ E'.π = E.π
  zero_w : E.zero ≫ hom = E'.zero

/-- Elliptic curves over a fixed base scheme form a category under pointed morphisms. -/
instance : Category (EllipticCurve S) where
  Hom := HomOver
  id E := ⟨𝟙 E.E, Category.id_comp _, Category.comp_id _⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [Category.assoc, g.over_w, f.over_w],
    by rw [← Category.assoc, f.zero_w, g.zero_w]⟩

/-- Isomorphism classes of elliptic curves over a fixed base scheme. -/
def IsoClasses (S : Scheme.{u}) : Type (u + 1) :=
  Quotient (CategoryTheory.isIsomorphicSetoid (EllipticCurve S))

/-- **(T-G3h-hfix gate — finite-étale descent for `torsionι`; KM 2.3.2 + 2.7.2)** For
`N` invertible on `S`, an `S`-endomorphism `ψ` of `E.E` (`ψ ≫ π = π`) fixing the two
generators `P, Q` of a naive full level-`N` structure restricts to the **identity on the
`N`-torsion subscheme** `E[N]`:
`torsionι N ≫ ψ = torsionι N`. `ψ` fixes every combination `aP+bQ` (from `hP`, `hQ` and
additivity of a pointed endomorphism — the proven `endMonHom`/`endPostcomp_mul`), and by `hPQ`
those generate
`E[N]`; the passage from that generator agreement to the scheme-morphism identity is
**finite-étale descent** for `torsionι` (`E[N] → S` finite étale as `N` is invertible,
KM 2.3.2).

GATE: `E[N]` finite étale = Torsion.lean `BB-QF`/`BB-FLAT`. Full route analysis (three options via
mathlib `ext_of_isDominant_of_isSeparated'` / full-level trivialization / p2's
`torsionι_factors_iff`,
plus `torsionSubgroup`/`SchemeQuotient` reuse) in `.mathlib-quality/decomposition-g3-geometry.md`.
On discharge, `aut_trivial_of_fullLevel` becomes fully proven modulo the PIC0 data. -/
theorem torsionFixed_of_fixesLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N]
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (ψ : E.E ⟶ E.E) (hψ : ψ ≫ E.π = E.π)
    (hP : P.1 ≫ ψ = P.1) (hQ : Q.1 ≫ ψ = Q.1) :
    E.torsionι N ≫ ψ = E.torsionι N := sorry

/-- The underlying map of an automorphism fixing a full level structure of level at least three
is the identity. -/
theorem aut_hom_eq_id_of_fullLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e.hom.hom = 𝟙 E.E := by
  let ε : E.asOver ⟶ E.asOver := Over.homMk e.hom.hom e.hom.over_w
  haveI : IsIso ε := by
    refine ⟨⟨Over.homMk e.inv.hom e.inv.over_w, ?_, ?_⟩⟩
    · ext1
      exact congrArg HomOver.hom e.hom_inv_id
    · ext1
      exact congrArg HomOver.hom e.inv_hom_id
  exact congrArg CommaMorphism.left <|
    E.aut_endo_eq_one N (by exact_mod_cast hN) ε (E.endDeg_eq_one_of_isIso ε) <|
      E.torsionFixed_of_fixesLevel N hinv P Q hPQ e.hom.hom e.hom.over_w hP hQ

/-- An automorphism fixing a full level structure of level at least three is the identity
isomorphism. -/
theorem aut_trivial_of_fullLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e = Iso.refl E :=
  Iso.ext <| HomOver.ext <|
    aut_hom_eq_id_of_fullLevel N hN hinv E P Q hPQ e hP hQ

end EllipticCurve

end ModularCurves
