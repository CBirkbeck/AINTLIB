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
over `S` carrying zero to zero — a **pointed `S`-morphism**, NOT necessarily
invertible (`[2] : E ⟶ E` is one, of fibre degree 4, as is the zero morphism between
any two curves). The groupoid of the moduli stack is the **core** of this category
(its isomorphisms are exactly the pointed `S`-isomorphisms). With the group structure,
such a morphism is automatically a homomorphism — rigidity; ticket `T-G2`. -/
@[ext]
structure HomOver (E E' : EllipticCurve S) where
  hom : E.E ⟶ E'.E
  over_w : hom ≫ E'.π = E.π
  zero_w : E.zero ≫ hom = E'.zero

/-- Elliptic curves over `S` with pointed `S`-morphisms form a category. Its **core**
(the isomorphisms) is the groupoid of elliptic curves over `S` — the value at `S` of
the moduli *stack*. (The category itself is NOT a groupoid: `[2]` is a non-invertible
pointed endomorphism — adversarial pass 2026-07-06, which removed the former false
`T-G1` claim from here.) -/
instance : Category (EllipticCurve S) where
  Hom := HomOver
  id E := ⟨𝟙 E.E, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [Category.assoc, g.over_w, f.over_w],
    by rw [← Category.assoc, f.zero_w, g.zero_w]⟩
  id_comp := by intros; ext; simp
  comp_id := by intros; ext; simp
  assoc := by intros; ext; simp [Category.assoc]

-- (T-G1 DELETED, adversarial pass 2026-07-06.) The former claim "every pointed
-- `S`-morphism is an isomorphism" is FALSE — `[2] : E ⟶ E` is a pointed `S`-morphism
-- of fibre degree 4 — and no source states it (KM 2.4 is rigidity = hom-ness, not
-- invertibility). Groupoid semantics downstream must use isomorphisms (`≅`/`IsIso`)
-- explicitly; see `GammaHClasses` and `aut_trivial_of_fullLevel` for the repaired
-- consumers.

/-- Isomorphism classes of elliptic curves over `S` — the set-valued shadow of the
groupoid. Set-valued moduli problems are only faithful to the geometry where
automorphisms act freely on the level data (rigidity); see
`ModuliProblem.Rigid`. -/
def IsoClasses (S : Scheme.{u}) : Type (u + 1) :=
  Quotient (⟨fun E E' : EllipticCurve S => Nonempty (E ≅ E'),
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e ≪≫ e'⟩⟩⟩ :
      Setoid (EllipticCurve S))

/-- **(T-G3 = rigidification bridge; GME 2.6.4 Aut-computation, p. 151)**
For `N ≥ 3` and `N` invertible, an **automorphism** of an elliptic curve over `S`
fixing a naive full level-`N` structure is the identity — the groupoid of `(E, P, Q)`
is equivalent to a set, and the set-valued problem `gammaFullNaiveProblem` is the
honest one. (This is the statement that justifies ever leaving the groupoid world.)

ADVERSARIAL FIX (2026-07-06): the previous endomorphism form (`f : E ⟶ E`) was FALSE —
`[1+N]` fixes every level point (`(1+N)•P = P + N•P = P`) but has degree `(1+N)² > 1`.
GME's proof consumes `deg ε = 1`, i.e. `ε ∈ Aut` ("1 = deg ε = 1 + nTr(g) + n²deg g",
GME p. 151, quote in hand at decomposition-gme2 B9); the statement is now about
isomorphisms, exactly the quoted scope. -/
theorem aut_trivial_of_fullLevel (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e = Iso.refl E := by sorry

end EllipticCurve

end ModularCurves
