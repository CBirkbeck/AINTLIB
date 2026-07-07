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

/-- **(T-G3a — engine core; GME 2.6.4 arithmetic, p. 151)** The purely number-theoretic
heart of the automorphism-rigidity computation, abstracted from the elliptic-curve setup so
it is proved and reused independently of the (still-to-be-built) endomorphism-degree
infrastructure (`End(E/S)`, dual isogeny, Hasse bound — sub-tickets `T-G3b`–`T-G3e`).

Reading `d = deg g ≥ 0`, `t = tr g = ⟨1, g⟩` (the polar/trace form of the degree quadratic
form), `n = N ≥ 3`: GME's chain "`1 = deg ε = 1 + n·tr g + n²·deg g`" for an automorphism
`ε = 1 + n·g` gives the linear relation `hlin` (`n·t + n²·d = 0`), and the Hasse /
Cauchy–Schwarz discriminant bound `⟨1,g⟩² ≤ 4·deg g` gives `hbound` (`t² ≤ 4·d`). Together
with `n ≥ 3` these force `deg g = 0`, whence (by positive-definiteness of `deg`, supplied by
the caller) `g = 0` and `ε = 1`.

This is the step that makes `N ≥ 3` the sharp threshold: cancelling `n` gives `t = -n·d`, so
`n²·d² ≤ 4·d`, i.e. `d·(n²·d - 4) ≤ 0`; the only non-negative integer solution once `n² ≥ 9`
is `d = 0` (a positive `d ≥ 1` gives `n²·d - 4 ≥ 5 > 0`). Reused by `T-H5`. -/
theorem gme_deg_trace_forces_zero {n t d : ℤ} (hn : 3 ≤ n) (hd : 0 ≤ d)
    (hlin : n * t + n ^ 2 * d = 0) (hbound : t ^ 2 ≤ 4 * d) : d = 0 := by
  have hn0 : (0 : ℤ) < n := by linarith
  -- Cancel `n` from the linear relation: `t = -(n·d)`.
  have ht : t + n * d = 0 := by
    have key : n * (t + n * d) = 0 := by linear_combination hlin
    exact (mul_eq_zero.mp key).resolve_left (ne_of_gt hn0)
  have htd : t = -(n * d) := by linarith
  -- Feed `t = -(n·d)` into the discriminant bound: `n²·d² ≤ 4·d`.
  have hb2 : n ^ 2 * d ^ 2 ≤ 4 * d := by
    have h := hbound; rw [htd] at h; nlinarith [h]
  -- `n ≥ 3` and `d ≥ 0` (integer) force `d = 0`.
  by_contra hne
  have hd1 : 1 ≤ d := by omega
  nlinarith [hb2, mul_nonneg (by linarith : (0 : ℤ) ≤ n - 3) (by linarith : (0 : ℤ) ≤ n + 3),
    mul_nonneg hd (sub_nonneg.mpr hd1), hd1, sq_nonneg d]

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
theorem aut_hom_eq_id_of_fullLevel (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e.hom.hom = 𝟙 E.E := by sorry

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
theorem aut_trivial_of_fullLevel (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : NIsInvertible S N) (E : EllipticCurve S) (P Q : E.Section)
    (hPQ : E.IsNaiveFullLevel N P Q) (e : E ≅ E)
    (hP : P.1 ≫ e.hom.hom = P.1) (hQ : Q.1 ≫ e.hom.hom = Q.1) :
    e = Iso.refl E := by
  refine Iso.ext (HomOver.ext ?_)
  exact aut_hom_eq_id_of_fullLevel N hN hinv E P Q hPQ e hP hQ

end EllipticCurve

end ModularCurves
