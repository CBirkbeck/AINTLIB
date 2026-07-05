import ModularCurves.Moduli.EllCategory

/-!
# Groupoid-valued moduli (expert-review addition, Q7)

Reviewer (2026-07-05): *"do not make everything set-valued too early. Internally, keep
the groupoid-valued moduli problem `S ↦ groupoid of elliptic curves over S with level
structure`. Then specialize to a set-valued functor only after rigidification, e.g.
full level `N ≥ 3`, or after proving automorphisms are killed. This will save you pain
when you later touch `X₀(N)`, coarse moduli, or quotients."*

This file provides the groupoid layer: for a fixed base `S`, the groupoid of elliptic
curves over `S` (morphisms: pointed isomorphisms over `S`), and the specialisation
bridge — the set-valued problems of `Moduli/Representability.lean` are the iso-class
functors of groupoid-valued problems, legitimate exactly when automorphisms act freely
(rigidity). The full pseudofunctor packaging over the fppf site remains ticket `T-E8`
(non-load-bearing bridge, plan D3); *statements about small level* (`N ≤ 2`, `Γ₀`,
level 1) must be phrased against this groupoid layer, never against iso-classes.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- A morphism of elliptic curves over the *same* base: a morphism of total spaces
over `S` carrying zero to zero. (With the group structure, such a morphism is
automatically a homomorphism — rigidity; ticket `T-G2`.) -/
@[ext]
structure HomOver (E E' : EllipticCurve S) where
  hom : E.E ⟶ E'.E
  over_w : hom ≫ E'.π = E.π
  zero_w : E.zero ≫ hom = E'.zero

/-- Elliptic curves over `S` with pointed `S`-morphisms form a category; every
morphism is an isomorphism (`T-G1`), making it the **groupoid of elliptic curves
over `S`** — the value at `S` of the moduli *stack* of elliptic curves. -/
instance : Category (EllipticCurve S) where
  Hom := HomOver
  id E := ⟨𝟙 E.E, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [Category.assoc, g.over_w, f.over_w],
    by rw [← Category.assoc, f.zero_w, g.zero_w]⟩
  id_comp := by intros; ext; simp
  comp_id := by intros; ext; simp
  assoc := by intros; ext; simp [Category.assoc]

/-- **(T-G1)** Every pointed `S`-morphism of elliptic curves over `S` is an
isomorphism (an isogeny of degree 1; via rigidity/translation arguments — KM 2.4-
adjacent, ⧗KM). Upgrades the category above to a groupoid. -/
theorem isIso_homOver (E E' : EllipticCurve S) (f : E ⟶ E') : IsIso f := by sorry

/-- Isomorphism classes of elliptic curves over `S` — the set-valued shadow of the
groupoid. Set-valued moduli problems are only faithful to the geometry where
automorphisms act freely on the level data (rigidity); see
`ModuliProblem.Rigid`. -/
def IsoClasses (S : Scheme.{u}) : Type (u + 1) :=
  Quotient (⟨fun E E' : EllipticCurve S => Nonempty (E ≅ E'),
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩⟩ :
      Setoid (EllipticCurve S))

/-- **(T-G3 = rigidification bridge; Loeffler Prop 3.8.3 content for full level)**
For `N ≥ 3` and `N` invertible, an automorphism of an elliptic curve over `S` fixing a
naive full level-`N` structure is the identity — the groupoid of `(E, P, Q)` is
equivalent to a set, and the set-valued problem `gammaFullNaiveProblem` is the honest
one. (This is the statement that justifies ever leaving the groupoid world.) -/
theorem aut_trivial_of_fullLevel (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (f : E ⟶ E)
    (hP : P.1 ≫ f.hom = P.1) (hQ : Q.1 ≫ f.hom = Q.1) :
    f = 𝟙 E := by sorry

end EllipticCurve

end ModularCurves
