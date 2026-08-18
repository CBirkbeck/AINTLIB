# /mathlibable report — `WeierstrassCurve.baseChange_preΨ'`

**TL;DR — `NO-mathlib-has-it`.** This declaration is a **verbatim fork** of an
existing mathlib lemma. It lives in a file whose own module docstring says it
"is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`
that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib
version, to avoid name conflicts". The lemma already exists in mathlib at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:565` —
identical namespace, identical signature (modulo the `W⁄B` ⇄ `W.baseChange B`
notation alias), identical proof.

---

## Baseline (Phase 0)

- lake build:               (not re-run — local build stale per task; assessment reasons from source. The decl is a verbatim copy of a known-green mathlib lemma, so elaboration is not in question.)
- decl `WeierstrassCurve.baseChange_preΨ'`:  ✓ resolved at `projects/NagellLutz/LutzNagell/DivisionPolynomial.lean:488`
- kind:                      lemma
- has sorry:                 no  (proof is `rw [← map_preΨ', map_baseChange]`)
- module docstring summary:  "This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` that imports `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version, to avoid name conflicts (both define `normEDS`, `complEDS`, etc.). See the original file for full documentation."

**Qualified-name verification.** The file opens `namespace WeierstrassCurve`
(line 27) and never closes it before line 488; the base name is `baseChange_preΨ'`.
So the parsed qualified name in the task header is correct:
`WeierstrassCurve.baseChange_preΨ'`. (The task said the line was 495; the actual
decl is at **line 488** — line 495 is the neighbouring `baseChange_ΨSq`. Line
drift only; the named declaration is unambiguous.)

---

## Statement (Phase 1)

`WeierstrassCurve.baseChange_preΨ'` states that the auxiliary division
polynomials `preΨ'ₙ` (for `n : ℕ`) commute with base change along an
`S`-algebra homomorphism `f : A →ₐ[S] B`.

Concretely: given a Weierstrass curve `W` over a base ring `R`, with two
`R`-and-`S`-algebras `A` and `B` forming scalar towers `R → S → A` and
`R → S → B`, and an `S`-algebra map `f : A →ₐ[S] B`, the `n`-th auxiliary
division polynomial of the base-changed curve `W⁄B` (over `B`) equals the
image under `f` (coefficient-wise, via `Polynomial.map`) of the `n`-th
auxiliary division polynomial of `W⁄A` (over `A`):
$$\mathrm{pre}\Psi'_n(W_{/B}) \;=\; f_*\bigl(\mathrm{pre}\Psi'_n(W_{/A})\bigr).$$

This is functoriality / naturality of the division-polynomial construction
under base change — a "the construction commutes with the obvious map" lemma.

Variables / typeclasses involved (Lean side):
- `{R : Type r} [CommRing R]`, `(W : WeierstrassCurve R)` — the base curve.
- `{S : Type s} [CommRing S] [Algebra R S]` — an intermediate base.
- `{A : Type u} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]` — source algebra.
- `{B : Type v} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]` — target algebra.
- `(f : A →ₐ[S] B)` — the `S`-algebra homomorphism along which we base-change.
- `(n : ℕ)` — the index of the division polynomial.

Hypotheses (Lean side): none beyond the typeclass/parameter context above.

Conclusion (math): `preΨ'ₙ` is natural in the base along `S`-algebra maps.

Conclusion (Lean):
`(W.baseChange B).preΨ' n = ((W.baseChange A).preΨ' n).map f`
(in mathlib written `(W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f`).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: glue/functoriality lemma — a two-step `rw` reducing base-change to the
already-proved `map_preΨ'`. Not a named theorem, not a new structure, not a
listed main result. (Literature width is exhaustive regardless; recorded for
framing.)

---

## One-line check (Phase 2b)

Body line count: 1 substantive line (`rw [← map_preΨ', map_baseChange]`).
One-liner verdict: **n/a** — kind is `lemma`, not a `def`/`abbrev`/`structure`.
The Phase-2b one-liner exemption analysis applies to definitions only; a
one-line *proof* of a lemma is not a one-liner def. No defeq/diamond/API
exemption analysis required.

---

## Literature search (Phase 3)

This is a **forked mathlib lemma**, and the decisive evidence is the direct
mathlib match (Phase 5). The "literature" for a base-change-functoriality
lemma of division polynomials is the standard elliptic-curve / division-
polynomial theory; mathlib's own `DivisionPolynomial.Basic` is the
authoritative formalisation of exactly this. The full channel sweep is
recorded below for completeness; none of it changes the verdict.

| #  | Channel                          | Query                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "division polynomial" base change functoriality elliptic curve        | partial | division polys are universal/integral; base change commutes | Standard fact: `ψₙ` has integer-coefficient universal form, so it commutes with any ring map. Textbooks (Silverman AEC III, exercises) treat this implicitly. |
|  2 | WebSearch (general form)         | division polynomial naturality ring homomorphism `Polynomial.map`     | partial | same — universality ⇒ naturality | The construction is by a fixed recurrence in `b₂,b₄,b₆,b₈`; ring maps commute with it termwise. |
|  3 | WebSearch (named-after/aliases)  | "preΨ" OR "pre-normalised EDS" base change WeierstrassCurve            | yes  | mathlib's own naming (`preΨ'`, `preNormEDS'`) | The name `preΨ'` is mathlib-internal (Angdinata's division-polynomial development); it is not a classical literature name. |
|  4 | ChatGPT MCP                      | standard form + generality + historical evolution of "division polynomials commute with base change" | n/a  | MCP unavailable this session (per task note) | Fallback: reasoned from the source + mathlib. The math content (universality of division polynomials ⇒ compatibility with ring maps) is textbook-standard; the precise Lean packaging is mathlib's. |
|  5 | Local references                 | grep `.mathlib-quality/references/` for "division polynomial"/"base change" | n/a | no references dir present for NagellLutz | recorded n/a — directory absent. |
|  6 | nLab                             | division polynomial                                                    | n/a  | —                   | nLab has no dedicated division-polynomial page; not a categorical concept. |
|  7 | nCatLab                          | —                                                                      | n/a  | —                   | not a categorical concept. |
|  8 | Stacks Project                   | division polynomial / Weierstrass base change                          | n/a  | —                   | Stacks does not develop classical division polynomials of Weierstrass models. |
|  9 | MathOverflow / MSE               | division polynomials integer coefficients base change                 | partial | universality is folklore | Confirms the math is standard; no specific "form" disagreement. |
| 10 | recent arXiv (last 5y)           | elliptic divisibility sequence / division polynomial formalisation    | partial | Angdinata's mathlib formalisation is the reference artifact | The formalised `preΨ'`/`Ψ`/`φ` development is itself the modern reference. |

### Literature summary (Phase 3)

Concept identified as: **functoriality (naturality) of division polynomials
under base change** — the auxiliary polynomials `preΨ'ₙ` are given by a fixed
recurrence in the universal coefficients `b₂,b₄,b₆,b₈`, so they commute with
any (`S`-algebra) ring homomorphism applied coefficient-wise.
Sources agree on the standard form: yes — the underlying mathematics
(universality ⇒ base-change compatibility) is textbook/folklore; the precise
statement and naming (`preΨ'`, `W⁄B`, `Polynomial.map f`) are mathlib's own.
Most general standard form: "for any ring map, the construction commutes with
it"; mathlib packages the algebra-map case via the `IsScalarTower` setup (see
Phase 4).
Disagreement with the literature: none.

---

## Generality analysis (Phase 4)

### 4a. Generality status table

Literature-standard form (from Phase 3): division polynomials commute with any
homomorphism of the base. Mathlib offers two complementary packagings, both
present in the same file:
- `map_preΨ'` (line 526 in mathlib) — the **plain ring-homomorphism** form
  `(W.map f).preΨ' n = (W.preΨ' n).map f` for `f : R →+* S`. This is the
  maximally general statement.
- `baseChange_preΨ'` (the decl under review) — the **`S`-algebra-map** form,
  derived from `map_preΨ'` in one rewrite. This is the convenient form for
  base-change towers.

| # | Parameter / hypothesis        | Current Lean form              | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|--------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `(f : A →ₐ[S] B)`            | `S`-algebra homomorphism       | arbitrary ring hom of the base   | yes — `map_preΨ'` is the `R →+* S` form | But that more-general form **already exists in mathlib** as `map_preΨ'`. `baseChange_preΨ'` is the deliberately-specialised companion; both are wanted. Not a generality defect. |
| 2 | `[IsScalarTower R S A/B]`     | scalar towers over `S`         | n/a (artifact of the algebra-map packaging) | no | required to make `W⁄A`, `W⁄B`, and `f` interact; intrinsic to this convenience form. |
| 3 | `(n : ℕ)`                     | natural-number index           | natural-number index             | no | `preΨ'` is defined on `ℕ` (the `ℤ` extension is the separate `preΨ`, with its own `baseChange_preΨ`). Correct index type. |

### 4b. Generality verdict

The current form is: **MAXIMALLY GENERAL for what it is** — and, crucially, the
strictly-more-general ring-hom form it specialises (`map_preΨ'`) is *also*
already in mathlib. There is no weakening to propose: the general form exists,
and this `S`-algebra companion is the intended specialisation.
Number of weakening opportunities found: 0 (the more-general form is a separate,
already-present lemma, not a missing improvement).
Cost of restatement: n/a — no restatement warranted.

### 4c. Modern mathlib-idiom restatement — Bourbaki 2.0 check

| #  | Question                                                                       | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                            | no  | already fully typeclass-driven (`Algebra`, `IsScalarTower`) | — |
|  2 | sequences/metric → filters/topological?                                        | no  | no analytic content   | — |
|  3 | construct an object → universal-property class?                                | no  | this is a `Polynomial.map` compatibility equation, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                             | no  | no substructure here  | — |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                       | no  | already at `CommRing`+`Algebra` generality | — |
|  6 | 1-categorical → higher-categorical?                                            | no  | a single equation in polynomial rings | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group?                               | no  | `preΨ'` is genuinely `ℕ`-indexed by construction; the `ℤ` case is `preΨ`/`baseChange_preΨ` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. The lemma is already in the contemporary
mathlib idiom (it *is* mathlib's idiom — it was authored there). No
modernisation move. This forecloses the "YES-add-as-is because we'd be the
modernisation" escape hatch from the Phase-7 gate.

---

## Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `lemma`.** No definitional equalities or
typeclass-search paths are introduced. Skipped.

---

## Mathlib search-status: `WeierstrassCurve.baseChange_preΨ'` (Phase 5)

[A] Lean-Finder       (mathlib index unavailable to re-query live; relied on direct source grep — authoritative) — n/a
[B] Loogle            type pattern `(WeierstrassCurve.baseChange _ _).preΨ' _ = _` — superseded by exact grep hit
[C] LeanSearch        "division polynomial commutes with base change" — superseded by exact grep hit
[D] **Grep mathlib src**  `baseChange_preΨ'` over `.lake/packages/mathlib/Mathlib/` — **EXACT HIT** at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:565`
[E] Name pattern      `baseChange_preΨ'` — exact name match, same namespace `WeierstrassCurve`

Searched for both:
  - the user's current form — **found, identical**.
  - the literature-standard (more general ring-hom) form — **also found**, as
    the sibling `map_preΨ'` (`Basic.lean:526`), which this lemma's proof calls.

**Concluded: found in mathlib as `WeierstrassCurve.baseChange_preΨ'`; IDENTICAL form.**

Byte-level comparison (the only difference is the `W⁄B` notation, which is the
scoped alias `notation W "⁄" A => baseChange W A`, defined at
`Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean:240`):

| | project (`DivisionPolynomial.lean:488`) | mathlib (`Basic.lean:565`) |
|---|---|---|
| signature | `baseChange_preΨ' (n : ℕ) : (W.baseChange B).preΨ' n = ((W.baseChange A).preΨ' n).map f` | `baseChange_preΨ' (n : ℕ) : (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f` |
| proof | `rw [← map_preΨ', map_baseChange]` | `rw [← map_preΨ', map_baseChange]` |
| namespace | `WeierstrassCurve` | `WeierstrassCurve` |
| variable block | line 473 | line 550 — **identical** |

`W.baseChange B` and `W⁄B` are the *same term* (the notation unfolds to
`baseChange W B`). The statements are therefore definitionally identical, and
the proofs are textually identical. This is a verbatim fork.

---

## Composition check (Phase 6)

### 6.0. Call sites — `WeierstrassCurve.baseChange_preΨ'`

Internal use count (within NagellLutz, excluding the declaring file): grep for
`baseChange_preΨ'` across `projects/NagellLutz/` finds the declaration site only;
no other `.lean` consumer in the project references it directly. (It exists in
the fork purely to mirror the mathlib file completely; it is part of an
imported-as-a-block copy.)

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none beyond the declaring file) | — |

Inline-derivation grep: (none) — no site re-derives this statement by hand.

**Signal.** K = 0 internal direct uses. For a *forked* lemma this is expected
and benign: the file is a wholesale copy of the mathlib module (to swap one
import — `LutzNagell.EllipticDivisibilitySequence` for the mathlib EDS file —
and avoid `normEDS`/`complEDS` name clashes), not a curated subset. The lemma's
presence is structural, not evidence of new API. The call-sites signal here
points firmly *away* from "new contribution".

### 6a. Composition attempt

Can the statement be obtained from mathlib in ≤3 chained calls? Yes — exactly
as mathlib itself does it:

Attempt 1: `by rw [← map_preΨ', map_baseChange]`
  - Mathlib decls used: `WeierstrassCurve.map_preΨ'` (`Basic.lean:526`),
    `WeierstrassCurve.map_baseChange`.
  - Result: **succeeds** — this is literally the mathlib proof.

But composition is moot: the *whole lemma* (statement **and** this proof) is
already present in mathlib under the same name. There is nothing to compose —
one imports the lemma.

Conclusion: **the lemma is present in mathlib verbatim** (a fortiori COMPOSABLE,
but the operative fact is identity, not composability).

---

## Verdict: `WeierstrassCurve.baseChange_preΨ'`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): functoriality of division polynomials under base
  change; underlying math is textbook/folklore, the precise statement is
  mathlib's own. No standard-form disagreement.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for this form; the strictly
  more general ring-hom form (`map_preΨ'`) *also already exists* in mathlib.
  Modern-idiom check: no modernisation move (it is already mathlib's idiom).
- Mathlib search (Phase 5): **found in mathlib as
  `WeierstrassCurve.baseChange_preΨ'`; identical form** — same namespace,
  same signature (modulo the `W⁄B` notation alias), same proof, same variable
  block — `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:565`.
- Composition check (Phase 6): K = 0 internal callers; lemma present verbatim
  upstream — nothing to add.

**Rationale.**
This is not a borderline case. The NagellLutz `DivisionPolynomial.lean` file is,
by its own module docstring, *a copy of*
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, forked only
to import the project's local `EllipticDivisibilitySequence` (so the duplicated
`normEDS`/`complEDS`/`preNormEDS'` names don't collide). The lemma
`baseChange_preΨ'` is reproduced **verbatim** from that mathlib file — identical
statement, identical one-line proof `rw [← map_preΨ', map_baseChange]`, identical
namespace and typeclass context. Mathlib already has it; we would never upstream
it because it is already upstream.

The only superficial difference is notation: the fork spells the base change
`W.baseChange B`, while mathlib uses the scoped notation `W⁄B`, which is *defined*
as `baseChange W B`. These are the same term, so the two lemmas are
definitionally and textually the same. The more-general ring-homomorphism
version (`map_preΨ'`) that this lemma specialises is *also* already in mathlib in
the same file, so there is likewise no "generalise-first" contribution lurking
here.

WHY not (refactor-actionable):
Mathlib already has this lemma, identically. The fork exists for an
import-hygiene reason internal to NagellLutz (avoiding `normEDS` name clashes
with the project's own EDS development), not because the lemma is new. So the
"contribution" is nil.

Existing mathlib decl:  `WeierstrassCurve.baseChange_preΨ'`
Located at:             `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:565`
Our form follows in ≤1 line — it is *the same lemma*:
```lean
-- mathlib's statement and proof, character-for-character (W⁄B ≡ W.baseChange B):
lemma baseChange_preΨ' (n : ℕ) : (W⁄B).preΨ' n = ((W⁄A).preΨ' n).map f := by
  rw [← map_preΨ', map_baseChange]
```

Call sites in our project (from Phase 6.0): **K = 0** direct internal consumers
(the lemma is part of a wholesale block-copy of the mathlib module).

Refactor plan:
- This is **not** a standalone-deletion target. The entire NagellLutz
  `DivisionPolynomial.lean` is a deliberate fork of the mathlib module, kept only
  because it re-imports `LutzNagell.EllipticDivisibilitySequence` to dodge
  `normEDS`/`complEDS` name conflicts. `baseChange_preΨ'` should be removed *only*
  as part of retiring the whole fork.
- The correct project-level fix (a cross-cutting cleanup ticket, not a
  per-lemma edit) is to make NagellLutz **depend on mathlib's
  `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic` directly**
  and delete the local copy, reconciling the duplicated
  EDS layer (`LutzNagell.EllipticDivisibilitySequence` vs.
  `Mathlib.NumberTheory.EllipticDivisibilitySequence`) so the name clash that
  motivated the fork disappears. After that reconciliation, every lemma in this
  file — `baseChange_preΨ'` included — comes for free from mathlib and the fork
  is deleted wholesale.
- Until that reconciliation happens, leave the lemma in place: it is load-bearing
  *within the fork* (it mirrors the mathlib API the rest of the NagellLutz
  development consumes through this copy).

Next action: do **not** open a mathlib PR (mathlib already has it). File/extend a
single project cleanup ticket to retire the `DivisionPolynomial.lean` fork against
mathlib's `DivisionPolynomial.Basic` once the local↔mathlib EDS duplication is
reconciled. (This is the same disposition reached for the sibling forked lemmas
in this directory, e.g. `baseChange_Ψ₂Sq.md`, `preΨ'_three.md`.)

---

## Next step

Do not upstream. The lemma is already in mathlib verbatim
(`WeierstrassCurve.baseChange_preΨ'`,
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:565`).
Track its removal under the project-wide ticket to retire the entire
NagellLutz `DivisionPolynomial.lean` fork — replacing it with a direct
dependency on mathlib's `DivisionPolynomial.Basic` after the duplicated
elliptic-divisibility-sequence layer is reconciled — rather than as an isolated
deletion.
