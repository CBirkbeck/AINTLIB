import ModularCurves.Moduli.EllCategory
import ModularCurves.Moduli.GammaH
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

1. **Torsor descent for rigidified curves** (`levelledCurve_descent_of_torsor`, the
   DEF-2 replacement, 2026-07-05): levelled elliptic curves descend along finite-group
   torsors — the form GME Lemma 2.6.7 actually uses, where Aut-triviality of the level
   makes the cocycle automatic. (The earlier cocycle-free fppf-descent statement was
   FALSE — sextic-twist obstruction — and was removed by the adversarial pass.)
   Source: GME Lemma 2.6.7 (p. 148); SGA 1 VIII via stream DESC.

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

/-- **(T-E10 v2, descent of rigidified curves along a finite-group torsor — the form
GME Lemma 2.6.7 actually uses; ADVERSARIAL FIX 2026-07-05, DEF-2)**

The previous cocycle-free fppf statement was rejected by the adversarial pass: a mere
isomorphism of the two pullbacks does NOT make a descent datum effective in general
(sextic-twist obstruction `H¹(G, μ₆) ≠ 0` for `j = 0`); SGA 1 VIII requires the
cocycle. In the rigidified situation the cocycle is automatic ("Since
`Aut_{E/S}(𝐄, φ_N) = {1_E}` … `θ(g) ∘ g^*θ(h) = θ(hg)`", GME p. 148), which is the
form the `Y(N)`-over-ℤ chain consumes:

Let `f : T' ⟶ T`, let `G` be a finite group acting on `T'` over `T` (via `σ`), with
the torsor condition: the canonical map `∐_G T' ⟶ T' ×_T T'`, `(g, t) ↦ (g·t, t)`,
is an isomorphism. Let `(E', L')` be an elliptic curve with (naive) full level-`N`
structure over `T'`, `N ≥ 3` invertible, such that for every `g ∈ G` the `g`-twist
`(E', L')` pulled along `σ g` is isomorphic to `(E', L')` in the levelled groupoid
(mere existence — no compatibility demanded). Then `(E', L')` descends: there is
`(E, L)` over `T` whose pullback along `f` is levelled-isomorphic to `(E', L')`.
General fppf-sheaf effectivity remains `T-E8` (mathlib `DescentData` packaging).
Source: GME Lemma 2.6.7 with proof (p. 148); black box BB-DESC retired to stream
DESC for this form (Galois/torsor case — AINTLIB Galois-descent engines apply). -/
theorem levelledCurve_descent_of_torsor {T T' : Scheme.{u}} (f : T' ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    (G : Type u) [Group G] [Finite G] (σ : G →* Aut (Over.mk f))
    (htorsor : IsIso ((Limits.Sigma.desc (fun g : G =>
      Limits.pullback.lift (f := f) (g := f) ((σ g).hom.left) (𝟙 T')
        (by rw [Category.id_comp]; exact Over.w (σ g).hom))) :
      (∐ fun _ : G => T') ⟶ Limits.pullback f f))
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (hinv : IsUnit (N : Γ(T', ⊤)))
    (E' : EllipticCurve T') (L' : E'.FullLevelPt N)
    (hdesc : ∀ g : G, Nonempty
      ((⟨E'.baseChange ((σ g).hom.left), EllipticCurve.FullLevelPt.pullAlong
          ((σ g).hom.left) L'⟩ : Σ E : EllipticCurve T', E.FullLevelPt N) ≅
        ⟨E', L'⟩)) :
    ∃ (E : EllipticCurve T) (L : E.FullLevelPt N), Nonempty
      ((⟨E.baseChange f, EllipticCurve.FullLevelPt.pullAlong f L⟩ :
          Σ E₀ : EllipticCurve T', E₀.FullLevelPt N) ≅ ⟨E', L'⟩) := by sorry

/-- **(T-E11, separatedness half of "the moduli problems are fppf sheaves")** For a
relatively representable moduli problem `P`, sections of `P` are determined fppf-locally:
restriction along an fppf cover `f : T' ⟶ T` is injective on `P`-values. (The gluing half
needs the descent-data vocabulary of `T-E8` and is recorded there.)

SOURCE STATUS (adversarial pass 2026-07-06): PENDING-SOURCE — KM 4.1–4.2 is not in
hand (Ch. 4 outside the preview) and Loeffler 3.8.2 does not state fppf-separatedness;
this is a formal lemma whose proof consumes (i) the `RelativelyRepresentable`
naturality clause and (ii) "fppf covers are epimorphisms of schemes" (subcanonicity,
SGA 1 VIII) — the latter is a mathlib-gap check for stream DESC. -/
theorem moduliProblem_fppf_separated (R : CommRingCat.{u}) (P : ModuliProblem R)
    (hP : P.RelativelyRepresentable) :
    ∀ {T T' : Scheme.{u}} (f : T' ⟶ T), Flat f → LocallyOfFinitePresentation f →
      Surjective f → ∀ (X : EllObj R) (g : T ⟶ X.base)
      (a b : P.obj (Opposite.op (X.pullbackAlong g))),
      P.map (X.pullbackAlongMap g f).op a = P.map (X.pullbackAlongMap g f).op b →
      a = b := by sorry

end ModularCurves
