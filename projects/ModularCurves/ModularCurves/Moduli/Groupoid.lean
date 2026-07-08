import ModularCurves.Moduli.EllCategory
import ModularCurves.EllipticCurve.EndomorphismDegree

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

-- **(T-G3a — engine core)** `gme_deg_trace_forces_zero` moved to
-- `EllipticCurve/EndomorphismDegree.lean` (its natural home: the pure ℤ-arithmetic core of the
-- degree computation), where it is consumed by `aut_endo_eq_one` — the End(E/S)-language assembly
-- of the whole rigidity computation. Close this box by importing that file and applying it through
-- the pointed/automorphism/level-structure bridges.

/-- **(T-G3h-hfix gate — finite-étale descent for `torsionι`; KM 2.3.2 + 2.7.2)** For `N` invertible
on `S`, an `S`-endomorphism `ψ` of `E.E` (`ψ ≫ π = π`) fixing the two generators `P, Q` of a naive
full level-`N` structure restricts to the **identity on the `N`-torsion subscheme** `E[N]`:
`torsionι N ≫ ψ = torsionι N`. `ψ` fixes every combination `aP+bQ` (from `hP`, `hQ` and additivity of
a pointed endomorphism — the proven `endMonHom`/`endPostcomp_mul`), and by `hPQ` those generate
`E[N]`; the passage from that generator agreement to the scheme-morphism identity is **finite-étale
descent** for `torsionι` (`E[N] → S` finite étale as `N` is invertible, KM 2.3.2).

GATE: `E[N]` finite étale = Torsion.lean `BB-QF`/`BB-FLAT`. Full route analysis (three options via
mathlib `ext_of_isDominant_of_isSeparated'` / full-level trivialization / p2's `torsionι_factors_iff`,
plus `torsionSubgroup`/`SchemeQuotient` reuse) in `.mathlib-quality/decomposition-g3-geometry.md`.
On discharge, `aut_trivial_of_fullLevel` becomes fully proven modulo the PIC0 data. -/
theorem torsionFixed_of_fixesLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N]
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (ψ : E.E ⟶ E.E) (hψ : ψ ≫ E.π = E.π)
    (hP : P.1 ≫ ψ = P.1) (hQ : Q.1 ≫ ψ = Q.1) :
    E.torsionι N ≫ ψ = E.torsionι N := sorry

/-- **(T-G3 core box — GME 2.6.4 scheme-morphism content; KM Ch. 2, do-not-formalize-from-
memory gate)** The geometric heart of `aut_trivial_of_fullLevel`, separated from the trivial
categorical wrapper: an automorphism `e` of `E/S` fixing a naive full level-`N` structure
(`N ≥ 3` invertible) has **underlying map** the identity `𝟙 E.E`. The statement is a clean
scheme-morphism equation (no `deg`/isogeny); only its *proof* is gated.

REDUCTION (the arithmetic glue `gme_deg_trace_forces_zero` above is the one non-gated piece):
`e.hom.hom` fixes `P, Q` (hyps `hP`/`hQ`); once it is additive on points — **T-G2** rigidity
(`isMonHom_of_one_comp_eq`, `EllipticCurve/Rigidity.lean`, sorried) — and `P, Q` generate
`E[N]` fibrewise (`IsNaiveFullLevel`), it fixes `E[N]`. Writing `ε = e.hom.hom` in `End(E/S)`,
`ε - 1` kills `E[N] = ker[N]`, so `ε = 1 + N•g` for some `g` (**T-G3d** divisibility). Then
`deg ε = 1` (automorphism) and the degree quadratic form `deg(1 + N•g) = 1 + N·tr g + N²·deg g`
(**T-G3b**) give `N·tr g + N²·deg g = 0`; with the Hasse/Cauchy–Schwarz bound `tr(g)² ≤ 4·deg g`
(**T-G3c**) and `N ≥ 3`, `gme_deg_trace_forces_zero` yields `deg g = 0`, hence `g = 0`
(positive-definiteness of `deg`) and `ε = 1`.

GATE: `End(E/S)`, `deg`, the dual isogeny (§B8) and the Hasse bound (§B9) are **KM Chapter 2** —
under the project's binding do-not-formalize-from-memory gate (tickets.md §"Do-not-formalize-
from-memory gate"); stated from the quotes in `.mathlib-quality/decomposition-gme2.md` §B8/§B9,
closed when the KM text lands. Sub-tickets T-G3b–T-G3e (board). -/
theorem aut_hom_eq_id_of_fullLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e.hom.hom = 𝟙 E.E := by
  -- Package the underlying automorphism as an `Over S`-endomorphism `ε` of `E`.
  let ε : E.asOver ⟶ E.asOver := Over.homMk e.hom.hom e.hom.over_w
  -- BRIDGE 1 (deg of an automorphism = 1; KM 2.7.1). `ε` is an iso in `Over S` (its inverse is the
  -- `Over`-package of `e.inv.hom`, and the two round-trips are `e.hom_inv_id`/`e.inv_hom_id` read on
  -- the `.hom` field), so `endDeg_eq_one_of_isIso` (deg multiplicative + `deg 𝟙 = 1` + `deg ≥ 0`)
  -- forces `deg ε = 1`.
  haveI : IsIso ε := by
    refine ⟨⟨Over.homMk e.inv.hom e.inv.over_w, ?_, ?_⟩⟩
    · ext1; exact congrArg HomOver.hom e.hom_inv_id
    · ext1; exact congrArg HomOver.hom e.inv_hom_id
  have hdeg : E.endDeg ε = 1 := E.endDeg_eq_one_of_isIso ε
  -- BRIDGE 2 (level structure → torsion fixing). `ε` fixes `P, Q` (`hP`, `hQ`); by T-G2 rigidity
  -- (`ε` pointed ⟹ additive) and `P, Q` generating `E[N] = ker[N]` fibrewise (`hPQ`,
  -- `IsNaiveFullLevel`), `ε` fixes the whole `N`-torsion subscheme.
  have hfix : E.torsionι N ≫ ε.left = E.torsionι N :=
    E.torsionFixed_of_fixesLevel N hinv P Q hPQ e.hom.hom e.hom.over_w hP hQ
  -- The arithmetic-geometric heart (KM 2.7.2(1)): a degree-1 endo fixing `E[N]` (`N ≥ 3`) is `𝟙`.
  have hone : ε = 𝟙 E.asOver := E.aut_endo_eq_one N (by exact_mod_cast hN) ε hdeg hfix
  -- Descend `ε = 𝟙 E.asOver` to the underlying scheme morphism `e.hom.hom = 𝟙 E.E`
  -- (`ε.left = e.hom.hom` and `(𝟙 E.asOver).left = 𝟙 E.E` both by `rfl`).
  exact congrArg CommaMorphism.left hone

/-- **(T-G3 = rigidification bridge; GME 2.6.4 Aut-computation, p. 151)**
For `N ≥ 3` and `N` invertible, an **automorphism** of an elliptic curve over `S`
fixing a naive full level-`N` structure is the identity — the groupoid of `(E, P, Q)`
is equivalent to a set, and the set-valued problem `gammaFullNaiveProblem` is the
honest one. (This is the statement that justifies ever leaving the groupoid world.)

ADVERSARIAL FIX (2026-07-06): the previous endomorphism form (`f : E ⟶ E`) was FALSE —
`[1+N]` fixes every level point (`(1+N)•P = P + N•P = P`) but has degree `(1+N)² > 1`.
GME's proof consumes `deg ε = 1`, i.e. `ε ∈ Aut` ("1 = deg ε = 1 + nTr(g) + n²deg g",
GME p. 151, quote in hand at decomposition-gme2 B9); the statement is now about
isomorphisms, exactly the quoted scope.

PROOF (2026-07-07): the iso/categorical layer is trivial plumbing — `HomOver.ext` uses only
the `hom` field (`over_w`/`zero_w` are `Prop`) and `(Iso.refl E).hom.hom = 𝟙 E.E` by `rfl`,
so `e = Iso.refl E` reduces to the scheme-morphism equation `aut_hom_eq_id_of_fullLevel`
(the GME 2.6.4 core; see its docstring for the gated reduction through `gme_deg_trace_forces_zero`). -/
theorem aut_trivial_of_fullLevel [IsLocallyNoetherian S] (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e = Iso.refl E := by
  refine Iso.ext (HomOver.ext ?_)
  exact aut_hom_eq_id_of_fullLevel N hN hinv E P Q hPQ e hP hQ

end EllipticCurve

end ModularCurves
