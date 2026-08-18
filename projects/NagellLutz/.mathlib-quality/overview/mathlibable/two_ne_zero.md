# /mathlibable report — `WeierstrassCurve.Universal.Poly.two_ne_zero`

> Step-9 mathlibable assessment (NagellLutz project, Nagell–Lutz theorem track).
> Run date: 2026-06-22. Local build stale; verdict reasoned from source + mathlib
> source grep + WebSearch. ChatGPT MCP was down (documented fallback used).

---

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale, per task brief) — verdict reasoned from source
- decl `WeierstrassCurve.Universal.Poly.two_ne_zero`:  ✓ resolved at `projects/NagellLutz/LutzNagell/Universal.lean:103`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  "The universal elliptic curve" — sets up the universal Weierstrass curve over `MvPolynomial Coeff ℤ`, its coordinate ring, fraction field, and the polynomial ring `Poly := (MvPolynomial Coeff ℤ)[X][Y]` in seven variables.

**True qualified name (VERIFIED).** Namespace at line 103 is `WeierstrassCurve.Universal`
(opened at lines 69 + 75). `Poly` is an `abbrev` (line 94), NOT a namespace, so the
leading `Poly.` is part of the lemma name. Full name:
`WeierstrassCurve.Universal.Poly.two_ne_zero`. The parsed name in the task brief is correct.

---

### Statement (Phase 1)

`WeierstrassCurve.Universal.Poly.two_ne_zero` states: in the ring
`Poly := (MvPolynomial Coeff ℤ)[X][Y] = Polynomial (Polynomial (MvPolynomial Coeff ℤ))`
— the polynomial ring over ℤ in the seven variables `A₁,A₂,A₃,A₄,A₆,X,Y` — the element
`2` is nonzero.

In standard mathematics this is utterly elementary: a polynomial ring over a
characteristic-zero (indeed integral) base ring is again characteristic zero, so the
integer `2` maps to a nonzero element. It is a triviality used only as a side-condition
(`2 ∈ nonZeroDivisors`, `zero_pow two_ne_zero`, etc.) in the division-polynomial
machinery.

Variables / typeclasses involved (Lean side):
- `Coeff` — the fixed 5-element inductive type of Weierstrass coefficient labels (no typeclass).
- The ambient ring is the *concrete* type `Poly`; no generic typeclass parameters.

Hypotheses (Lean side): none.

Conclusion (math): `2 ≠ 0` in `ℤ[A₁,…,A₆][X][Y]`.
Conclusion (Lean): `(2 : Poly) ≠ 0`.

The proof body (one expression):
```lean
Polynomial.C_ne_zero.mpr <| Polynomial.C_ne_zero.mpr fun h ↦ two_ne_zero' (α := ℤ) <|
  MvPolynomial.C_injective _ _ <| by rwa [← MvPolynomial.C_0] at h
```
It manually pushes `2 = C (C (C 2))` down through the two `Polynomial.C` layers
(`C_ne_zero` twice) and the `MvPolynomial.C` layer (`C_injective`), bottoming out at
`(2 : ℤ) ≠ 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A hypothesis-free `≠`-fact about a concrete ring, used purely as a side-condition.
Not a named theorem, not a new structure, not a `## Main results` entry.

(Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` → the one-liner-definition check does
not apply (it targets one-line *definitions*, which are the mathlib-inclusion negative
signal). Recorded as **n/a — kind is lemma**. Note for framing: the *proof* is a single
expression, and the *statement* is a numeral-nonzero fact — both strong "this is generic
infrastructure, not project math" signals that feed Phase 6/7.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                         | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | `"2 ≠ 0" polynomial ring CharZero Lean mathlib nontrivial OfNat NeZero`                        | yes  | `NeZero.charZero` chain: `CharZero M → NeZero (n:M)`  | Confirms the `CharZero`→`NeZero`→`two_ne_zero` route is the standard mathlib idiom |
|  2 | WebSearch (general form)         | (same query, general angle) characteristic-zero of polynomial extensions                      | yes  | `CharZero R ⟹ CharZero R[X]` is standard             | Cyclotomic.Basic + CharZero.Defs hits corroborate |
|  3 | WebSearch (named-after/aliases)  | `mathlib WeierstrassCurve Universal elliptic curve universal polynomial ring division polynomial` | yes (context) | mathlib has `DivisionPolynomial.*`; **no `Universal` namespace** | The universal-curve construction itself is the project's own; the *numeral* lemma is generic |
|  4 | ChatGPT MCP                      | self-contained: does `two_ne_zero (α:=Poly)` follow from the 4-instance chain; any synth failure? | n/a  | — (server down)                                       | Codex MCP errored ("Codex failed"), as the task brief warned. Fallback: verified every instance directly in mathlib source (rows below) + precedent grep |
|  5 | Local references                 | `refs/NagellLutz/`, `.mathlib-quality/references/`                                             | n/a  | (no references dir present)                           | `refs/` absent on this checkout; `.mathlib-quality/` has only `overview/` |
|  6 | nLab                             | "characteristic of a polynomial ring"                                                         | n/a  | trivial textbook fact                                | nLab has no page for so elementary a statement; not a categorical concept |
|  7 | nCatLab (categorical)            | —                                                                                             | n/a  | —                                                    | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                             | n/a  | —                                                    | "2 ≠ 0 in a poly ring" is commutative-algebra trivia, not a Stacks-tag concept |
|  9 | MathOverflow / Math.SE           | characteristic of polynomial ring over char-0 ring                                            | n/a  | standard: char is preserved                          | folklore; `char R[X] = char R`; no research-level question |
| 10 | recent arXiv (last 5y)           | division polynomials Weierstrass formalization (1303.4327, ITP 2023, Mason–Stothers 2408.15180) | yes (context) | confirms univariate-universal-ring *approach*; no special "2≠0" lemma | the surrounding division-polynomial theory is in the literature; the numeral side-condition is not a named result anywhere |

The protocol passed: WebSearch ran 3 distinct generality levels; ChatGPT MCP was
*attempted* (errored — documented, with a concrete source-level fallback substituted);
local refs checked (absent); nLab / nCatLab / Stacks / MathOverflow / arXiv each
checked or `n/a` with a one-line reason.

### Literature summary (Phase 3)

Concept identified as: "`2 ≠ 0` in a polynomial ring over a characteristic-zero base"
— a special case of "polynomial extensions preserve characteristic zero", which is
textbook commutative algebra.
Sources agree on the standard form: yes — `char(R[X]) = char(R)`, hence `CharZero R ⟹ CharZero R[X]`,
and in any `CharZero` ring every positive-integer numeral is nonzero.
Most general standard form: in any `CharZero` (additive-monoid-with-one) ring, `(n : R) ≠ 0` for `n ≥ 1`.
Generality dimensions where the literature varies:
  - base ring: the relevant range is "any char-0 ring" (here ℤ); the lemma fixes the
    concrete tower `(MvPolynomial Coeff ℤ)[X][Y]`.
  - numeral: the literature statement is about *every* numeral; the lemma fixes `2`.
Disagreement with the literature: none. The lemma is a doubly-specialised instance of a
standard fact, proved without invoking the standard `CharZero` machinery.

---

### Generality analysis — `WeierstrassCurve.Universal.Poly.two_ne_zero`

Literature-standard form (from Phase 3): in any `[AddMonoidWithOne R] [CharZero R]`,
`(2 : R) ≠ 0` — which mathlib already packages as `two_ne_zero` given `[NeZero (2:R)]`,
and `NeZero (2:R)` is itself an instance from `CharZero R`.

| # | Parameter / hypothesis            | Current Lean form                         | Literature-standard form              | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-------------------------------------------|----------------------------------------|---------------------|----------------------------------|
| 1 | ambient ring                      | concrete `(MvPolynomial Coeff ℤ)[X][Y]`   | any `[CharZero R]` (or any `[NeZero (2:R)]`) | yes             | the proof uses nothing about the tower beyond "char 0 at the bottom, `C` injective up" — i.e. exactly `CharZero` of the whole ring |
| 2 | the numeral                       | fixed `2`                                 | any numeral `n ≥ 1`                    | yes (orthogonal)    | `three_ne_zero`, `four_ne_zero`, or general `NeZero (n:R)` cover the rest; not needed for this lemma's purpose |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a concrete-ring specialisation).
Number of weakening opportunities found: 2 (generalise the ring to `[CharZero R]`; the
numeral is orthogonal and irrelevant).
Proposed restatement: *there is nothing to restate for mathlib* — the maximally general
form (`two_ne_zero` over any `[OfNat α 2] [NeZero (2:α)]`, with `NeZero` supplied by
`CharZero`) **already exists in mathlib**. Generalising this project lemma would just
reproduce `two_ne_zero`. So the "generalise-first" target is not a new declaration; it is
the existing mathlib lemma. → this pushes the verdict to a NO bucket, not YES-but-generalise.
Cost of restatement: n/a (no restatement to ship).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" → typeclass?                                            | no       | already typeclass-driven in mathlib (`CharZero`/`NeZero`) | — |
|  2 | sequences/metric → filters/topology?                                    | no       | no analysis content | — |
|  3 | construction → universal-property class?                                | no       | it's a `≠`-proposition, nothing to characterise | — |
|  4 | set-with-closure → bundled substructure?                                | no       | — | — |
|  5 | vector-space/field-specific → weaken typeclass?                         | yes (already) | the mathlib form is already at `CharZero`/`NeZero` generality | the whole `NeZero`/`zero_pow`/`nonZeroDivisors` API |
|  6 | 1-categorical → higher-categorical?                                     | no       | — | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure?                   | yes      | drop the concrete tower; state over `[CharZero R]` — but that IS `two_ne_zero` | unifies with every `CharZero` ring |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no new one** — the modern, maximally-general mathlib idiom for
this fact already exists as `two_ne_zero` + the `CharZero ⟹ NeZero` instance. There is no
contemporary reformulation to add; the move is to *use* the existing idiom, not author a
new declaration. (Hence not a YES-but-generalise case: the general form is already in mathlib.)

---

### Diamond / defeq risk — `WeierstrassCurve.Universal.Poly.two_ne_zero`

n/a — declaration kind is `lemma` (a `Prop`; introduces no definitional equalities,
typeclass-search paths, coercions, or instances). Phase 4.5 skipped.

---

### Mathlib search-status: `WeierstrassCurve.Universal.Poly.two_ne_zero`

[A] Lean-Finder       n/a — index tool not reachable in this env; substituted by [D] grep over the pinned mathlib tree (authoritative)
[B] Loogle            pattern `(2 : ?R) ≠ 0` / `NeZero (2 : ?R)`   → mathlib `two_ne_zero` (`Algebra/NeZero.lean:36`) + `NeZero.charZero_ofNat` (`Algebra/CharZero/Defs.lean:122`)
[C] LeanSearch        "two is nonzero in a polynomial ring / characteristic zero" → same `two_ne_zero` + `CharZero` instances (corroborated via WebSearch rows 1–2)
[D] Grep mathlib src  `two_ne_zero`, `C_ne_zero`, `CharZero`, `namespace Universal` over `.lake/packages/mathlib/` → all building blocks found; **no `WeierstrassCurve.Universal` in mathlib**
[E] Name pattern      `Poly.two_ne_zero`, `Universal.Poly`, `WeierstrassCurve.Universal` → present ONLY in the project (and duplicated in HasseWeil); absent from mathlib

Searched for both:
  - the user's current form `(2 : Poly) ≠ 0` — **not** in mathlib as a named lemma (it's project-specific to a project-specific ring).
  - the literature-standard form — **in mathlib**: `two_ne_zero` over any `[OfNat α 2] [NeZero (2:α)]`, with `[NeZero (2:α)]` auto-derived from `[CharZero α]` via `NeZero.charZero_ofNat`, and `CharZero Poly` auto-derived by the instance tower below.

The exact mathlib building blocks (all verified in the pinned tree):
- `Mathlib/Algebra/Ring/Int/Defs.lean:53` — `instance instCharZero : CharZero ℤ`.
- `Mathlib/RingTheory/MvPolynomial/Basic.lean:67` — `instance [CharZero R] : CharZero (MvPolynomial σ R)`.
- `Mathlib/Algebra/Polynomial/Coeff.lean:372` — `instance charZero [CharZero R] : CharZero R[X]` (fires twice up the `[X][Y]` tower).
- `Mathlib/Algebra/CharZero/Defs.lean:122` — `instance charZero_ofNat [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M] : NeZero (OfNat.ofNat n : M)`.
- `Mathlib/Algebra/NeZero.lean:36` — `lemma two_ne_zero [OfNat α 2] [NeZero (2:α)] : (2:α) ≠ 0`.

Concluded: **found building blocks; a single mathlib call (`two_ne_zero`) yields our form
by instance resolution.** Since `Poly` is an `abbrev` (reducible) the entire `CharZero`
tower fires through it structurally; `two_ne_zero (α := Poly)` (or bare `two_ne_zero` at
the expected type) discharges the goal. This is NO-composable-from-mathlib (1 call, not even 3).

Note on `WeierstrassCurve.Universal` itself: this universal-pointed-curve construction is
**not** in mathlib (only `DivisionPolynomial.*` is). So the *surrounding development* is a
genuine project artifact — but THIS lemma is generic ring-theory trivia inside it, fully
replaceable by mathlib's `two_ne_zero`.

---

### Call sites — `WeierstrassCurve.Universal.Poly.two_ne_zero`

Internal use count (NagellLutz, excluding the declaring file): **1**
External-to-file callers: 1 distinct file.

| Caller file:line                                              | Usage pattern (one-line excerpt)                                   |
|--------------------------------------------------------------|---------------------------------------------------------------------|
| projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:119 | `(mem_nonZeroDivisors_of_ne_zero Universal.Poly.two_ne_zero)`     |

(The many other `two_ne_zero` occurrences in NagellLutz — `ZSMul.lean`, `EllipticDivisibilitySequence.lean`,
`LutzNagellTheorem/*.lean` — are the *unqualified mathlib* `two_ne_zero` resolving over
ℤ / fields / other rings, NOT this lemma. They were inspected and excluded.)

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - **Duplicate, not inline-rederivation:** `projects/HasseWeil/HasseWeil/Auxiliary/Universal.lean:106`
    contains a **byte-for-byte identical** `Poly.two_ne_zero` with the same proof. This is a
    cross-project fork duplicate (NagellLutz and HasseWeil both forked the universal-curve file).
    Used in HasseWeil at `Auxiliary/DivisionPolynomial.lean:145`.

Composability signal (per the Phase-6.0 table): K = 1 internal use, no inline re-derivation,
but a verbatim duplicate exists in a sibling project → "possibly the wrong abstraction /
should be inlined", reinforced by the fact that mathlib already has the result. Leans NO-composable.

---

### Composition check (Phase 6)

Can `WeierstrassCurve.Universal.Poly.two_ne_zero` be derived from mathlib in ≤3 chained calls?

Attempt 1: `two_ne_zero (α := Poly)`  — or, if the elaborator already knows the expected
type at the call site, bare `two_ne_zero`.
  - Mathlib decls used: `two_ne_zero` (+ instances `Polynomial.charZero` ×2, the
    `MvPolynomial` `CharZero` instance, `Int.instCharZero`, `NeZero.charZero_ofNat` — all
    resolved silently by typeclass synthesis, not counted as "calls").
  - Result: **succeeds**. `two_ne_zero` needs `[OfNat Poly 2]` (from the `CommRing`/`AtLeastTwo`
    ofNat instance) and `[NeZero (2 : Poly)]`; the latter is synthesised from `CharZero Poly`,
    which is `CharZero ((MvPolynomial Coeff ℤ)[X][Y])` built by iterating the two registered
    polynomial `CharZero` instances over `CharZero ℤ`. `Poly` is an `abbrev`, so synthesis
    sees through it.
  - Notes: This is a **single** mathlib call (term `two_ne_zero`), well within the ≤3 budget.

Caveat (honest): the file carries the comment `instance : CommRing Poly := Polynomial.commRing /- why is this not automatic ... -/`, signalling the author hit some synthesis friction
on this nested-`Polynomial`/bivariate-`Y` tower and may have hand-rolled `two_ne_zero` for
the same reason. Even in the worst case where bare `two_ne_zero` doesn't trigger the tower
search spontaneously, the explicit-type form `two_ne_zero (α := Poly)` (or
`two_ne_zero (α := (MvPolynomial Coeff ℤ)[X][Y])`) pins the type so synthesis only has to
walk the two structural `CharZero` instance steps — still one call, still ≤3. The
`CharZero` instances are keyed on `Polynomial _` / `MvPolynomial _ _` head symbols (unlike
the `CommRing` default that prompted the comment), so they fire structurally. This caveat
is a *robustness* note for the refactorer (ascribe the type if needed), not a barrier.

Conclusion: **COMPOSABLE** (1 mathlib call; ≤3 budget satisfied with room to spare).

---

## Verdict: `WeierstrassCurve.Universal.Poly.two_ne_zero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the fact is "char is preserved by polynomial extensions" — textbook; the modern mathlib idiom (`CharZero`→`NeZero`→`two_ne_zero`) already captures it.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — a doubly-specialised (fixed ring, fixed numeral) instance whose general form is *already in mathlib*, so it is NOT a YES-but-generalise (nothing new to add), it is a NO.
- Mathlib search (Phase 5): not present as a named lemma for this ring; all building blocks present; the standard general form `two_ne_zero` + the `CharZero` instance tower covers it.
- Composition check (Phase 6): COMPOSABLE — a single call `two_ne_zero (α := Poly)`.

**Rationale:**

`(2 : Poly) ≠ 0` is generic ring-theory trivia sitting inside a project-specific construction.
Mathlib already proves "2 is nonzero" for *every* characteristic-zero ring via `two_ne_zero`
together with the instance `NeZero.charZero_ofNat : [CharZero M] → NeZero (OfNat.ofNat n : M)`,
and it already knows `Poly = (MvPolynomial Coeff ℤ)[X][Y]` is characteristic zero by iterating
the two registered instances `Polynomial.charZero` and the `MvPolynomial` `CharZero` instance
over `Int.instCharZero`. Because `Poly` is a reducible `abbrev`, this whole tower fires by
instance synthesis, so the single term `two_ne_zero` (with the type pinned via `(α := Poly)`
if synthesis needs the nudge — see the Phase-6 caveat about the `CommRing` comment) closes the
goal. The hand-rolled proof — descending manually through `Polynomial.C_ne_zero` twice plus
`MvPolynomial.C_injective` — is exactly the kind of bespoke re-derivation mathlib's `CharZero`
machinery exists to make unnecessary; mathlib's own elliptic-curve files (e.g. `IsomOfJ.lean`)
already use bare `two_ne_zero` rather than `C_ne_zero` chains, which is direct precedent for the
idiomatic form.

This is *not* YES-but-generalise-first, because generalising the project lemma to its standard
form does not produce a new mathlib declaration — it produces `two_ne_zero`, which is already
there. The right action is to delete the local lemma and inline `two_ne_zero` at its sole call
site (and the duplicate's call site in HasseWeil). The surrounding `WeierstrassCurve.Universal`
development is itself a legitimate not-yet-in-mathlib artifact, but that is a separate question
from this one numeral lemma.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the form is a 1-call composition. The building blocks are:
- `two_ne_zero` (`Mathlib/Algebra/NeZero.lean:36`)
- instance `NeZero.charZero_ofNat` (`Mathlib/Algebra/CharZero/Defs.lean:122`)
- instance `Polynomial.charZero` (`Mathlib/Algebra/Polynomial/Coeff.lean:372`) — fires twice up `[X][Y]`
- instance `CharZero (MvPolynomial σ R)` (`Mathlib/RingTheory/MvPolynomial/Basic.lean:67`)
- instance `Int.instCharZero` (`Mathlib/Algebra/Ring/Int/Defs.lean:53`)

Mathlib building blocks (composition target): `two_ne_zero`.

Composition sketch (≤3 lines — in fact 1):
```lean
-- replaces the body of Poly.two_ne_zero entirely:
example : (2 : Poly) ≠ 0 := two_ne_zero
-- if instance synthesis needs the type pinned (cf. the `CommRing Poly` comment):
example : (2 : Poly) ≠ 0 := two_ne_zero (α := Poly)
```

Call sites in our project (from Phase 6.0):  K = 1 (NagellLutz) + 1 (HasseWeil duplicate).
Refactor plan:
  1. **NagellLutz** — at `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:119`,
     replace `Universal.Poly.two_ne_zero` with `two_ne_zero` (ascribe `(α := Universal.Poly)`
     only if the elaborator can't infer the type from `mem_nonZeroDivisors_of_ne_zero`'s
     expected argument). Then delete the lemma at `Universal.lean:103–105`.
  2. **HasseWeil** (cross-project — flag for the HasseWeil owner; do NOT touch from a NagellLutz
     dev branch): identical replacement at `Auxiliary/DivisionPolynomial.lean:145`, then delete
     the verbatim-duplicate lemma at `Auxiliary/Universal.lean:106–108`.
  3. Verify with `lake build`; the side-condition is `2 ∈ nonZeroDivisors _`, which
     `mem_nonZeroDivisors_of_ne_zero two_ne_zero` supplies unchanged.

Note: because this is a project-internal cleanup (delete-and-inline), it is a **/cleanup**
(dedup) action on `main`, not a mathlib PR. Nothing is upstreamed — mathlib already has it.

Next action: delete `WeierstrassCurve.Universal.Poly.two_ne_zero` from the project; inline
`two_ne_zero` at the call site(s). Coordinate the HasseWeil duplicate via a cross-project
cleanup ticket (the two forks should ultimately share one universal-curve file).

---

## Next step

Delete `WeierstrassCurve.Universal.Poly.two_ne_zero` from the project and inline mathlib's
`two_ne_zero` (type-ascribed if needed) at `DivisionPolynomialOmega.lean:119`; file a
cross-project cleanup ticket to do the same for the byte-identical HasseWeil duplicate at
`HasseWeil/Auxiliary/Universal.lean:106`.
