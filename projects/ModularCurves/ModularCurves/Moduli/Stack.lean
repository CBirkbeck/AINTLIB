import ModularCurves.Moduli.EllCategory
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# The stack of elliptic curves: descent statements (the "stack bridge")

Loeffler, remark after Def 3.7.1 (verbatim): *"The category `Ell/R` is `Sch/Y` for a `Y`
that does not exist. If the functor `S ↦ {ell. curves/S}` were representable by some
`(Y, E/Y)`, then the objects of `Ell/R` would be just maps `S → Y`. This is the idea of
stacks."*

Per the project's design decision (KM formalism + stack bridge), the working engine is
`Moduli/EllCategory.lean`; this file carries the honest stack-theoretic *statements*:

1. **fppf descent for elliptic curves** (`ellipticCurve_fppf_descent`) — effectivity of
   descent data, stated elementarily (no fibered-category packaging needed): elliptic
   curves glue along fppf covers. This is the mathematical content of "`M_ell` is an fppf
   stack"; with level structures it is what makes the moduli problems `P_H` fppf-sheaves.
   Source: KM 4.1 (implicit; they work fppf-locally throughout), SGA 1 VIII (descent of
   schemes along fppf morphisms, black box BB-DESC).

2. **The pseudofunctor packaging** (`T-E8`, statement deferred): assembling
   `S ↦ (groupoid of elliptic curves over S)` into a `Pseudofunctor` and proving
   `Pseudofunctor.IsStack` for the fppf topology, using mathlib's
   `CategoryTheory.Sites.Descent.IsStack`. Deferred because constructing the
   pseudofunctor (coherence data for pullback composition) is genuine infrastructure —
   ticket `T-E8` — and *no theorem of this project consumes it*; it is the
   promised bridge artifact, not load-bearing for `Y(ρ,p)`.

The fppf Grothendieck topology used below is obtained from mathlib's `fppfPrecoverage`.
-/

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

-- The fppf topology is mathlib's `AlgebraicGeometry.fppfTopology`
-- (`fppfPrecoverage.toGrothendieck`) — do not redefine it here.

/-- **(T-E10, fppf descent for elliptic curves — "M_ell is a stack", effectivity part)**
Let `f : T' ⟶ T` be a faithfully flat morphism of finite presentation, `E'` an elliptic
curve over `T'`, and suppose `E'` is equipped with a descent datum: an isomorphism between
its two pullbacks to `T' ×_T T'` satisfying the cocycle condition on `T' ×_T T' ×_T T'`.
Then `E'` descends: there is an elliptic curve `E/T` whose pullback to `T'` is isomorphic
to `E'` compatibly with the datum.

Stated here in existence form against the first pullback only (the full statement with
the cocycle condition needs the descent-data vocabulary of `T-E8`; this form is the
load-bearing consequence used by `T-E9`'s proof route). Black box BB-DESC (SGA 1 VIII;
fppf descent of quasi-projective schemes). -/
theorem ellipticCurve_fppf_descent {T T' : Scheme.{u}} (f : T' ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (E' : EllipticCurve T')
    (hdesc : ∃ e : (E'.baseChange (pullback.fst f f)).E ≅
        (E'.baseChange (pullback.snd f f)).E,
      e.hom ≫ (E'.baseChange (pullback.snd f f)).π =
        (E'.baseChange (pullback.fst f f)).π) :
    ∃ (E : EllipticCurve T) (e : (E.baseChange f).E ≅ E'.E),
      e.hom ≫ E'.π = (E.baseChange f).π := by sorry

/-- **(T-E11, separatedness half of "the moduli problems are fppf sheaves")** For a
relatively representable moduli problem `P`, sections of `P` are determined fppf-locally:
restriction along an fppf cover `f : T' ⟶ T` is injective on `P`-values. (The gluing half
needs the descent-data vocabulary of `T-E8` and is recorded there.) Source: KM 4.1–4.2
(fppf-local nature of the four basic problems); Loeffler Prop 3.8.2. -/
theorem moduliProblem_fppf_separated (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ T), Flat f → LocallyOfFinitePresentation f →
      Surjective f → ∀ (X : EllObj R) (g : T ⟶ X.base)
      (a b : P.obj (Opposite.op (X.pullbackAlong g))),
      P.map (X.pullbackAlongMap g f).op a = P.map (X.pullbackAlongMap g f).op b →
      a = b := by sorry

end ModularCurves
