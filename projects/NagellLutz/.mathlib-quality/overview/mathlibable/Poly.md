# /mathlibable report — `WeierstrassCurve.Universal.Poly`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz theorem; elliptic
> curves; division polynomials; elliptic divisibility sequences).
> Source: `projects/NagellLutz/LutzNagell/Universal.lean:94`.
> Build is stale locally — Phase 0 reasoned from source (the decl is a plain
> `abbrev` that trivially elaborates; no proof body to typecheck).

---

### Baseline (Phase 0)
- lake build:               (stale — not run; reasoned from source per task)
- decl `WeierstrassCurve.Universal.Poly`: ✓ resolved at `LutzNagell/Universal.lean:94`
- kind:                      `abbrev` (type abbreviation)
- has sorry:                 no
- module docstring summary:  Additions to `Affine.Point` + construction of the
  **universal Weierstrass curve** over `ℤ[A₁,A₂,A₃,A₄,A₆]` and the universal pointed
  elliptic curve over the fraction field of `ℤ[A₁,…,A₆,X,Y]/⟨P⟩`; specialization
  homomorphisms; the cusp curve `Y²=X³` used to prove non-vanishing of universal `ψₙ`.

True qualified name (VERIFIED from source): `WeierstrassCurve.Universal.Poly`
(inside `namespace WeierstrassCurve` → `namespace Universal`). Matches the prompt's parse.

---

### Statement (Phase 1)

`WeierstrassCurve.Universal.Poly` is a **type abbreviation**:

```lean
abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]
```

where `Coeff` is the five-element index type `{A₁, A₂, A₃, A₄, A₆}` and `[X][Y]` is
mathlib's `Polynomial.Bivariate` notation (`R[X][Y] = Polynomial (Polynomial R)`).
Spelled out, `Poly = ℤ[A₁,A₂,A₃,A₄,A₆][X][Y]`: the **bivariate polynomial ring over
the universal Weierstrass-coefficient ring**. It is the ambient ring carrying the
generic Weierstrass polynomial `P` (with the five coefficients as indeterminates `Aᵢ`
and the affine coordinates as `X, Y`). The "universal ring for *pointed* curves" is its
quotient `Universal.Ring = Poly/⟨P⟩`.

This is exactly the object mathlib's own DivisionPolynomial file *names informally* in
prose: `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]` (see Phase 5).

Variables / typeclasses involved (Lean side):
- none on the abbrev itself (it is a closed `Type`; `Coeff` is a fixed inductive).

Hypotheses (Lean side): none.

Conclusion (math): names the universal bivariate Weierstrass polynomial ring `ℤ[A₁..A₆][X,Y]`.
Conclusion (Lean): `Type` — n/a, this is a definition (type abbreviation).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: it is not a named mathematical structure in its own right, not a `## Main
results` entry, and not a person/place-named theorem. It is a one-line building-block
*type abbreviation* — the naming anchor for the `Universal` construction, but the
mathematical concept ("universal Weierstrass curve") lives in the *namespace as a whole*
(`curve`, `Ring`, `Field`, `polyToField`, …), not in `Poly` alone.

(Note: literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: **1** substantive line (`(MvPolynomial Coeff ℤ)[X][Y]`).
One-liner verdict: **ONE-LINER** (kind is `abbrev`).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | It is an `abbrev` (reducible) — it deliberately does *not* seal the body; downstream proofs unfold it freely. So this exemption does not apply. |
| Avoid typeclass diamonds         | partial  | A `CommRing Poly := Polynomial.commRing` instance is attached **explicitly** with the source comment `/- why is this not automatic ... -/`. The named anchor is the target that instance is registered against; without the name the instance has nowhere to land cleanly. Mild instance-resolution benefit, not a true diamond. |
| Mark semantic intent / API name  | **yes**  | `Poly` is the stable type the universal-curve API is phrased over: `polyToField : Poly →+* Field`, `curvePoly : WeierstrassCurve Poly`, `polyEval : Poly →+* R`, `ringEval_mk (p : Poly)`, `Poly.two_ne_zero`, the `CommRing Poly` instance — ~9 type-position uses inside the file. The name *is* the API surface. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (semantic-intent / API-name anchor; partial
diamond-avoidance). The exemption keeps a YES *possible*, but Phases 5–7 turn on
*packaging grain*, not on the one-liner test.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "universal Weierstrass curve over Z[a1,a2,a3,a4,a6] polynomial ring elliptic curve" | yes | `A = ℤ[a₁,a₂,a₃,a₄,a₆]` parametrises all Weierstrass curves; universal curve `ℰ → Spec(A)⁰` | Katz–Mazur (Princeton notes "Universal Weierstrass families"), Cremona's book ch.3, Sage/Magma docs. The *coefficient ring* `ℤ[a₁..a₆]` is the named classical object. |
| 2 | WebSearch (general form / the ω-motivation) | "universal elliptic curve ring of universal coefficients division polynomial omega well-defined characteristic 2" | yes | universal indeterminates `A₁..A₆`; `ωₙ` defined over the char-0 universal ring then specialised | arXiv 1303.5002 (coefficients of division polynomials), Sutherland 18.783 L#6, Sage `ell_generic`. Confirms `ℤ[A₁..A₆][X,Y]` is the standard home for the *generic* division polynomials. |
| 3 | WebSearch (named-after / aliases) | (covered by #1/#2) "universal Weierstrass family" / "ring of universal coefficients" | yes | same object; called "universal Weierstrass family", "generic Weierstrass curve", "ring of universal coefficients" | name varies; all denote `Spec ℤ[a₁..a₆]` and its base-changes. No separate name for the *bivariate* ring `·[X,Y]` — it is just "the polynomial ring over the universal ring". |
| 4 | ChatGPT MCP | (MCP down per task — fallback to #1–#3 + nLab) | n/a | — | Task notes ChatGPT MCP may be down; substituted extra WebSearch generality levels + nLab. Recorded n/a with reason. |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/` | n/a | (no references dir; no `refs/` store) | both absent — recorded n/a. |
| 6 | nLab | "elliptic curve", "Weierstrass curve", "moduli stack of elliptic curves" | yes | nLab/Wikipedia describe `M_Weier = Spec ℤ[a₁..a₆]` (the Weierstrass moduli/stack `ℳ_ell` quotient) | confirms the *curve/stack* is the named object; the ambient poly ring is implementation. |
| 7 | nCatLab (categorical) | n/a | n/a | — | not a categorical-structure question; the object is a concrete ring. |
| 8 | Stacks Project (alg geom) | "Weierstrass equation", "universal" | partial | Stacks has Weierstrass equations / the moduli of elliptic curves; no separately-named `ℤ[a₁..a₆][X,Y]` ring | the ambient bivariate ring is never separately named — it is written inline. |
| 9 | MathOverflow / MSE | "universal Weierstrass curve coefficient ring" | yes | confirms `ℤ[a₁..a₆]` standard; the `[X,Y]`-extension is ad hoc per author | consistent with #1–#3. |
| 10 | recent arXiv (≤5 yr) | "recurrence relation elliptic divisibility sequences" (arXiv 2102.07573), homogeneous division polynomials (1303.4327) | yes | use the generic/universal coefficient ring; spell the bivariate ring inline | no canonical *name* for `·[X,Y]`. |

### Literature summary (Phase 3)

Concept identified as: **the universal Weierstrass-coefficient ring** `ℤ[a₁,a₂,a₃,a₄,a₆]`
(a.k.a. universal Weierstrass family, ring of universal coefficients, generic Weierstrass
curve), and — for `Poly` specifically — its **bivariate polynomial ring** `ℤ[a₁..a₆][X,Y]`,
the ambient ring of the generic Weierstrass polynomial.

Sources agree on the standard form: **yes** for the coefficient ring `ℤ[a₁..a₆]` (universally
standard since Tate / Deuring; central in Katz–Mazur). For the *bivariate* ring `·[X,Y]`:
it is always *used* but essentially **never given its own name** in the literature — authors
write `ℤ[a₁..a₆][x,y]` (or `…[X,Y]`) inline. Mathlib's DivisionPolynomial docstring does the
same: it writes `𝓡[X, Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X, Y]` as informal prose, not as a Lean def.

Most general standard form: over `ℤ` (this is the point of universality — every concrete
curve over any base `R` is obtained by specialising `Aᵢ ↦ aᵢ ∈ R` via a ring hom). `Poly`'s
`ℤ`-base is therefore already maximally general.

Generality dimensions where the literature varies:
  - base ring of the indeterminates: always `ℤ` for the *universal* object (specialisation is downward).
  - whether the bivariate ring gets a name: ranges from "anonymous inline" (most texts, Stacks)
    to "informally named `𝓡[X,Y]`" (mathlib docstring). Never a formally-defined standalone object.

Disagreement with the literature: none — `Poly` is a faithful Lean realisation of the
standard `ℤ[a₁..a₆][X,Y]`.

---

### Generality analysis — `WeierstrassCurve.Universal.Poly`

Literature-standard form (from Phase 3): `ℤ[A₁,A₂,A₃,A₄,A₆][X, Y]`, base `ℤ`, two adjoined
coordinate variables.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | base of indeterminates | `ℤ` (`MvPolynomial Coeff ℤ`) | `ℤ` | NO | universality *requires* `ℤ` — it is the initial object; every base `R` specialises down via a unique ring hom. Generalising the base would destroy the universal property. |
| 2 | index of coefficients | `Coeff` = `{A₁..A₆}` (5 vars) | `a₁,a₂,a₃,a₄,a₆` (5 vars) | NO | the five Weierstrass coefficients are fixed by the equation `y²+a₁xy+a₃y=x³+a₂x²+a₄x+a₆`; this is the definition, not a tunable parameter. |
| 3 | coordinate variables | `[X][Y]` (iterated `Polynomial`) | `[X,Y]` | NO (this is the standard spelling) | mathlib's `Polynomial.Bivariate` `R[X][Y] := Polynomial (Polynomial R)` is the idiomatic bivariate ring; matches the literature. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for a *universal* object, `ℤ`-base + the five
fixed coefficients + two coordinate variables is precisely the right and only sensible form).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled-hypothesis preamble → typeclass? | no | — | no hypotheses; it is a closed type. |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic. |
| 3 | construct object → universal-property class? | **considered** | One could imagine characterising `ℤ[a₁..a₆][X,Y]` by its universal property (representing-object for "a Weierstrass curve + a point on the affine plane"). But mathlib's idiom for free/polynomial constructions is the explicit `MvPolynomial`/`Polynomial` term, exactly as here — and the file *does* expose the universal property operationally via `polyEval`/`specialize` (the specialisation ring homs). So the modern idiom is already the chosen one. | the file already provides the universal map `polyEval : Poly →+* R`. |
| 4 | set+closure-predicate → bundled substructure? | no | — | not a substructure. |
| 5 | field/metric-specific → weaken typeclass? | no | — | already over `ℤ`, the most general base. |
| 6 | 1-categorical → higher-categorical? | no | — | concrete ring; the moduli-*stack* refinement (`ℳ_ell`) is far beyond this building block and is not what `Poly` is. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive/monoid? | no | — | the `ℤ` base is forced by universality (Q1 row 1 above). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. `(MvPolynomial Coeff ℤ)[X][Y]` *is* the contemporary
mathlib spelling (uses `MvPolynomial` for the multivariate coefficient ring and the
`Polynomial.Bivariate` `[X][Y]` notation for the two coordinates). There is no cleaner
reorganisation that composes with more of mathlib; the universal-property "modernisation"
is already delivered by the surrounding `polyEval`/`specialize` API.

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Poly`  (kind = `abbrev` → Phase 4.5 runs)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | low | `Poly` is a plain iterated `Polynomial` over `MvPolynomial Coeff ℤ`; all algebraic instances come from mathlib's `Polynomial`/`MvPolynomial` instance graph. No second path to any common target. |
| 2 | Reducibility leak | low | As an `abbrev` it is `@[reducible]`, so the body `(MvPolynomial Coeff ℤ)[X][Y]` is exposed to defeq everywhere. For a *type* abbreviation this is the intended, harmless behaviour (it is how `R[X][Y]` itself behaves in mathlib). No non-trivial computation hidden behind it. |
| 3 | Non-canonical unfolding | low | `simp`/`rfl` see through to `Polynomial (Polynomial (MvPolynomial Coeff ℤ))` — expected and desired; the surrounding lemmas (`polyToField_apply`, `ringEval_mk`) rely on this transparency. |
| 4 | Instance priority collision | low | The one attached instance `CommRing Poly := Polynomial.commRing` exists *because* the reducible unfolding did not auto-trigger inference (source comment `/- why is this not automatic ... -/`). It restates the canonical `Polynomial.commRing`; no competing instance, hence no priority war — just a redundant-but-harmless re-registration. Worth a glance in any real PR. |
| 5 | Universe issues | none | everything is `Type` (`MvPolynomial Coeff ℤ : Type`, `Coeff : Type`); no universe polymorphism forced. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` introduced. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW**.
Top risks: none HIGH. The only wrinkle is the manually-supplied `CommRing Poly` instance
(row 4) standing in for an inference that "should" be automatic — a mild reducibility/
instance-resolution friction, not a diamond. (This friction is itself a small datum *for*
naming the type: the anchor gives the instance a place to live.)

---

### Mathlib search-status: `WeierstrassCurve.Universal.Poly`

[A] Lean-Finder        n/a (build stale — index/server not available this session)
[B] Loogle             n/a (build stale; substituted authoritative mathlib **source grep** below)
[C] LeanSearch         n/a (build stale)
[D] Grep mathlib src   "namespace Universal" / "inductive Coeff" / "MvPolynomial Coeff" /
                       "MvPolynomial …[X][Y]" / "ℤ[A₁..A₆]" / "universal ring" over
                       `.lake/packages/mathlib/Mathlib/`  → **no named object**; the ONLY hit
                       is `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:36`,
                       and it is **docstring prose**: "in the characteristic `0` universal ring
                       `𝓡[X, Y] := ℤ[A₁, A₂, A₃, A₄, A₆][X, Y]`" — not a Lean declaration.
[E] Name pattern       grep for `WeierstrassCurve.Universal` across mathlib → no hits.

Searched for both:
  - user's form `(MvPolynomial Coeff ℤ)[X][Y]` — not present as a named decl.
  - literature-standard `ℤ[A₁..A₆][X,Y]` / "universal ring 𝓡[X,Y]" — present only as
    informal docstring text in mathlib's DivisionPolynomial; never defined.

**Precedent for the *pattern* (important):** mathlib DOES name analogous "universal
polynomial-ring" abbreviations elsewhere:
  - `Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean:52` — `abbrev univ : Polynomial
    (MvPolynomial (n × n) R) := …` (the **universal characteristic polynomial**: a
    `Polynomial` over an `MvPolynomial` in the matrix entries — the *same shape* as `Poly`).
  - `Mathlib/RingTheory/Extension/Generators.lean:85` — `abbrev Ring (P) : Type := MvPolynomial ι R`.
So a one-line `abbrev` naming a universal polynomial ring is an *accepted mathlib idiom*;
the question is grain/packaging (Phase 7), not idiom-legitimacy.

Concluded: **not in mathlib** (no `Universal` Weierstrass namespace; the `𝓡[X,Y]` ring
exists only as docstring prose in `DivisionPolynomial/Basic.lean`). The building blocks
(`MvPolynomial`, `Polynomial.Bivariate` `[X][Y]`) are in mathlib; the *named* universal
ring is not.

---

### Call sites — `WeierstrassCurve.Universal.Poly`

Internal use count (within NagellLutz, NOT counting the declaring file): **0**
External-to-file callers of the **type** `Universal.Poly`: **0**
  (the only cross-file references to anything `Universal.Poly*` are to the *lemma*
   `Universal.Poly.two_ne_zero`, not to the type — see table.)
In-file (declaring `Universal.lean`) type-position uses of `Poly`: **~9** (heavy).

| Caller file:line | Usage pattern |
|------------------|---------------|
| `LutzNagell/Universal.lean:101` | `instance : CommRing Poly := Polynomial.commRing` (in-file) |
| `LutzNagell/Universal.lean:103` | `lemma Poly.two_ne_zero : (2 : Poly) ≠ 0` (in-file) |
| `LutzNagell/Universal.lean:108` | `def polyToField : Poly →+* Universal.Field` (in-file) |
| `LutzNagell/Universal.lean:167` | `abbrev curvePoly : WeierstrassCurve Poly := curve.baseChange Poly` (in-file) |
| `LutzNagell/Universal.lean:203` | `def polyEval : Poly →+* R := …` (in-file) |
| `LutzNagell/Universal.lean:206,110,220` | `(p : Poly)` argument positions (in-file) |
| `LutzNagell/DivisionPolynomialOmega.lean:119` | `Universal.Poly.two_ne_zero` (the **lemma**, not the type) |
| `HasseWeil/Auxiliary/DivisionPolynomial.lean:145` | `Universal.Poly.two_ne_zero` (the **lemma**, in HasseWeil's *own duplicate* copy) |

Inline-derivation grep (was `ℤ[a₁..a₆][X,Y]` re-derived elsewhere without `Poly`?):
  - **`HasseWeil/HasseWeil/Auxiliary/Universal.lean`** is a **verbatim duplicate** of this
    file (same author Junyan Xu; `inductive Coeff`, `def curve`, `abbrev Poly : Type :=
    (MvPolynomial Coeff ℤ)[X][Y]` at lines 76/87/97). So the construction — `Poly` included —
    exists in **two** project copies. This is a within-AINTLIB dedup signal, and it confirms
    `Poly` is shared infrastructure (two independent EC developments both need it).

What the pattern tells us: `Poly` is **not dead code** — it is the load-bearing type anchor
of the universal-curve API *within its file* and is duplicated across two projects. But it
has **0 uses as a type outside its own file**: consumers in other files only touch the
`Poly.two_ne_zero` lemma. So `Poly` lives and dies with the whole `Universal` namespace; it
is meaningless as a standalone export. → grain/packaging question (Phase 7).

---

### Composition check (Phase 6)

Can `Universal.Poly` be "derived from mathlib in ≤3 calls"?

`Poly` is a **type abbreviation**, not a proposition, so the composition test does not
apply in the usual sense. The only "composition" is *inlining* its body
`(MvPolynomial Coeff ℤ)[X][Y]` at every use site (the building blocks `MvPolynomial` and
`Polynomial.Bivariate`'s `[X][Y]` are both in mathlib).

Attempt 1: replace `Poly` everywhere by `(MvPolynomial Coeff ℤ)[X][Y]`.
  - Mathlib decls used: `MvPolynomial`, `Polynomial.Bivariate` (`R[X][Y]`).
  - Result: succeeds *mechanically* but is **anti-idiomatic** — it deletes the named API
    anchor that ~9 in-file declarations and the attached `CommRing Poly` instance are phrased
    over, and that mathlib itself names in analogous cases (`Matrix.Charpoly.univ`,
    `Generators.Ring`). Inlining a universal ring at every call site is exactly what the named
    `abbrev` exists to avoid.
  - Notes: this is "composable" only in the trivial sense that *every* type abbreviation is
    inlinable. Per the Phase-6 heuristics, a type-abbrev anchor with a Phase-2b semantic-intent
    exemption is NOT a NO-composable case — the name carries API value.

Conclusion: **NOT-COMPOSABLE** in the verdict-relevant sense (inlining a named universal-ring
abbreviation is not a "mathlib primitive composition" that obviates a contribution; it is a
de-naming that the surrounding API actively depends on).

---

## Verdict: `WeierstrassCurve.Universal.Poly`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the universal Weierstrass-coefficient ring `ℤ[a₁..a₆]` is a
  classical, standard, named object (Katz–Mazur, Cremona, Sage/Magma); its **bivariate**
  extension `ℤ[a₁..a₆][X,Y]` is universally *used* but essentially never *separately named* —
  mathlib's own DivisionPolynomial docstring writes it informally as `𝓡[X, Y]`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (the `ℤ`-base is forced by universality;
  the five coefficients + two coordinates are definitional). 4c: no modern-idiom improvement —
  this is already the idiomatic mathlib spelling.
- Diamond/defeq risk (Phase 4.5): **LOW** (only the manually-restated `CommRing Poly` instance
  is mildly notable; no diamond).
- Mathlib search (Phase 5): **not in mathlib** as a named object (only docstring prose in
  `DivisionPolynomial/Basic.lean:36`); a directly analogous *pattern* — naming a universal
  polynomial ring as a one-line `abbrev` — IS accepted in mathlib (`Matrix.Charpoly.univ`,
  `RingTheory.Extension.Generators.Ring`).
- Composition check (Phase 6): **NOT-COMPOSABLE** in the verdict sense (inlining the abbrev is
  a de-naming, not a primitive composition); call-sites show **0 external type uses** but ~9
  in-file uses and a **verbatim duplicate** in `HasseWeil/Auxiliary/Universal.lean`.

**Rationale (1–2 paragraphs):**

`Poly` is the *wrong grain* to ship to mathlib in isolation, and that is the whole difficulty.
On its own it is a one-line type abbreviation `ℤ[A₁..A₆][X,Y]` built entirely from existing
mathlib (`MvPolynomial` + `Polynomial.Bivariate`). It carries no mathematical content by
itself — yet it is not junk either: it is the load-bearing **API anchor** of Junyan Xu's
`Universal` Weierstrass-curve construction (it gets a Phase-2b semantic-intent exemption, has
~9 in-file type-position uses including an explicitly attached `CommRing Poly` instance, and is
duplicated verbatim across two projects, NagellLutz and HasseWeil). So "should mathlib have
`Poly`?" cannot be answered for `Poly` alone: it is answerable only as "should mathlib have the
whole `Universal` namespace (`Coeff`, `curve`, `Poly`, `Ring`, `Field`, `polyToField`,
`polyEval`, `specialize`, …)?" — and *that* is a genuine, mathlib-relevant object. Mathlib's
own DivisionPolynomial file already gestures at needing it: it writes
`𝓡[X, Y] := ℤ[A₁,A₂,A₃,A₄,A₆][X, Y]` in prose precisely to justify (informally) why `ωₙ` is
integral, a fact mathlib currently cannot state formally because the universal ring is not a
named object. There is even clean mathlib precedent for the *pattern* (`Matrix.Charpoly.univ`
names exactly this shape of universal polynomial ring as a one-line `abbrev`).

What blocks a self-resolved verdict is a cluster of **judgment/coordination calls the skill
cannot make alone**: (a) the PR grain — `Poly` only makes sense bundled with the rest of
`Universal`, so the real question is whether the *whole construction* is upstreamed, not this
line; (b) there are **two duplicate copies** in-repo, so before any mathlib move the AINTLIB
dedup must be resolved (which copy is canonical?); (c) whether mathlib wants this realised as a
concrete `abbrev` (matching `Matrix.Charpoly.univ`) or refactored to slot into the existing
`DivisionPolynomial` universal-ring narrative / the `WeierstrassCurve` namespace conventions
set by David Angdinata. These are taste + policy + repo-coordination decisions, which is exactly
what BORDERLINE is for. (Note: cost is *not* the blocker here — the build is trivial; the blocker
is grain and duplication.)

**Numbered questions (≤5):**

  1. **Grain.** `Poly` is meaningless standalone — it anchors the whole `Universal` namespace.
     Do you want to assess/upstream the **entire `Universal` Weierstrass-curve construction** as
     one unit (`Coeff`, `curve`, `Poly`, `Ring`, `Field`, `polyToField`, `polyEval`, `specialize`,
     `pointedCurve`, the cusp-curve machinery), rather than `Poly` in isolation? If yes, re-run
     `/mathlibable` on the namespace's *head* defs (`curve` first), treating `Poly` as INHERITED.
  2. **Duplication (AINTLIB-internal, must resolve first).** This file is **verbatim-duplicated**
     at `HasseWeil/HasseWeil/Auxiliary/Universal.lean` (same `Coeff`/`curve`/`Poly`). Before any
     mathlib consideration: which copy is canonical, and should the duplicate be replaced by an
     `import` of the other (a `/cleanup` dedup ticket on `main`)?
  3. **Mathlib fit.** Mathlib's `DivisionPolynomial/Basic.lean` already names this ring informally
     as `𝓡[X,Y] := ℤ[A₁..A₆][X,Y]` (docstring) to motivate `ωₙ`. Should the upstream target be a
     `Universal` namespace that *backs that prose with a real definition* (and would the EC
     maintainer, David Angdinata, want it integrated there)?
  4. **Realisation.** Mathlib precedent `Matrix.Charpoly.univ` names exactly this shape as a
     one-line `abbrev`. Is the concrete-`abbrev` realisation acceptable to you, or do you want a
     universal-property-based formulation (the file already exposes `polyEval`/`specialize` as the
     operational universal map)?

**Next action:** answer Q1–Q4. Most likely resolution: this is a **packaging** decision — assess
the `Universal` namespace as a unit with `curve`/`Ring`/`Field` as the head decls and `Poly` as an
INHERITED building block; resolve the NagellLutz↔HasseWeil duplication via a `main` cleanup ticket;
then, if upstreaming, propose a `WeierstrassCurve.Universal` namespace (concrete `abbrev`s, à la
`Matrix.Charpoly.univ`) that mathlib's DivisionPolynomial `ωₙ` narrative can be re-based onto.

---

## Next step

Answer the four numbered questions (grain / duplication / mathlib-fit / realisation), then
re-run `/mathlibable` on the `Universal` namespace head defs (`curve` first) with `Poly` treated
as an inherited anchor — `Poly` is not independently upstreamable, so a per-line verdict on it
is not actionable until the packaging + dedup calls are made.
