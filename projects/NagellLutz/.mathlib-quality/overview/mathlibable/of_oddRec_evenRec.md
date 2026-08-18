# /mathlibable report — `IsEllSequence.of_oddRec_evenRec`

**TL;DR — Verdict: `YES-add-as-is`.** This is a self-contained, named, capstone
result (the "term-by-term recurrences ⇒ full two-variable elliptic relation"
theorem, = Theorem 2.2 of Xu, *On Elliptic Sequences over Commutative Rings*,
arXiv:2604.05280, 2026). Mathlib does **not** have it (confirmed against both the
pinned mathlib and the live mathlib4 docs). Its form is already at maximal
generality (commutative ring + `W 1, W 2 ∈ R⁰`, the literature-standard
hypotheses). It is in fact part of an in-progress Xu–Angdinata mathlib PR; this
project file is that PR sitting ahead of the daily mathlib pin.

---

### Baseline (Phase 0)
- lake build:               ✗ NOT run (local build stale per task; reasoning from source — the
                            decl elaborates in the project and is consumed downstream, so it is real)
- decl `IsEllSequence.of_oddRec_evenRec`:
                            ✓ resolved at
                            `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:591`
                            (declared `theorem _root_.IsEllSequence.of_oddRec_evenRec`
                            inside `namespace EllSequence` → `section Perm`; the `_root_.`
                            escapes the `EllSequence` namespace, so the true qualified name is
                            **`IsEllSequence.of_oddRec_evenRec`** — NOT
                            `EllSequence.IsEllSequence.of_oddRec_evenRec`)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS); defines IsEllSequence /
                            IsDivSequence / normEDS and constructs normalised EDSs from initial
                            terms." Ward, *Memoir on Elliptic Divisibility Sequences*.

**Repo/fork context (decisive).** `projects/NagellLutz/.../EllipticDivisibilitySequence.lean`
(1667 lines) is a *forked, substantially expanded* version of
`Mathlib.NumberTheory.EllipticDivisibilitySequence` (pinned copy = 547 lines). The fork adds an
entire new namespace `EllSequence` (`addMulSub`, `rel₄`, `net` = Stange's elliptic-net relation,
`HaveSameParity₄`, `OddRec`, `EvenRec`, the permutation machinery `relFin4_perm`, and the two
capstones `rel₄_of_anti_oddRec_evenRec` and `IsEllSequence.of_oddRec_evenRec`). An identical copy
lives in `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` and a snapshot
in `...LutzNagell/EllipticDivisibilitySequenceOriginal.lean`.

---

### Statement (Phase 1)

`IsEllSequence.of_oddRec_evenRec` is a **theorem** stating:

> Let `R` be a commutative ring and `W : ℤ → R` a sequence that is **odd**
> (`W(−k) = −W(k)` for all `k`) with `W(0) = 0`. Suppose `W(1)` and `W(2)` are
> **non-zero-divisors** of `R`. Suppose `W` satisfies the **odd recurrence**
> `OddRec(m)` for every `m ≥ 2` and the **even recurrence** `EvenRec(m)` for every
> `m ≥ 3`, where
>   - `OddRec(m)`:  `W(2m+1)·W(1)³ = W(m+2)·W(m)³ − W(m−1)·W(m+1)³`
>   - `EvenRec(m)`: `W(2m)·W(2)·W(1)² = W(m)·(W(m−1)²·W(m+2) − W(m−2)·W(m+1)²)`
>
> Then `W` is an **elliptic sequence**: for all `m, n, r ∈ ℤ`,
>   `W(m+n)·W(m−n)·W(r)² = W(m+r)·W(m−r)·W(n)² − W(n+r)·W(n−r)·W(m)²`.

In words: the two *scalar, one-index* recurrences that define a normalised EDS
term-by-term (one for odd indices, one for even) are enough to force the full
*two-index* Ward elliptic relation everywhere. This is the algebraic crux that
makes `normEDS` an honest elliptic sequence.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — coefficient ring (commutative ring; **not** assumed a domain/field).
- `(W : ℤ → R)` — the sequence.

Hypotheses (Lean side; the accumulated `variable`/`include`s in `section Perm`):
- `(neg : ∀ k, W (-k) = -W k)` — `W` is an odd function.
- `(zero : W 0 = 0)` — vanishes at 0.
- `(one : W 1 ∈ R⁰)`, `(two : W 2 ∈ R⁰)` — `W 1`, `W 2` are non-zero-divisors (`R⁰ = nonZeroDivisors R`).
- `(oddRec : ∀ m ≥ 2, OddRec W m)`, `(evenRec : ∀ m ≥ 3, EvenRec W m)` — the two recurrences.

Conclusion (math): `W` is a Ward elliptic sequence (full bivariate relation holds for all integers).
Conclusion (Lean): `IsEllSequence W` (= `∀ m n r, Rel₃ W m n r`, with `Rel₃` the project's named
form of the inline mathlib relation).

Proof (Lean, 2 lines): `fun m n r ↦ by rw [rel₃_iff₄, rel₄_of_oddRec_evenRec neg zero one two
oddRec evenRec]; refine ⟨?_, ?_, ?_⟩ <;> simp only [negOnePow_two_mul, negOnePow_zero]`. I.e. it
reduces `Rel₃` to the four-index relation `rel₄ W (2m) (2n) (2r) 0 = 0` and discharges it with the
real workhorse `rel₄_of_oddRec_evenRec` (which itself rests on the antitone case
`rel₄_of_anti_oddRec_evenRec` + the `relFin4_perm` symmetry reduction). The two lines hide a deep
induction; this theorem is the clean public face of that development.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: A **main result** of the EDS development — the named theorem that "the defining recurrences
imply the elliptic relation" (Theorem 2.2 of Xu 2026). It produces the headline predicate
`IsEllSequence` and is the linchpin for `IsEllSequence.normEDS`. (Literature width is EXHAUSTIVE
regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (Although the proof
body is short, the one-liner heuristic targets definitions, not theorems. A 2-line proof of a
deep result is golf, not a triviality signal.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                 | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | Ward EDS recurrence implies elliptic relation `W(m+n)W(m-n)` two-variable proof                                        | yes  | Ward: `W₁=1 ⇒ W_{h-m}W_{h+m} = W_m²W_{h-1}W_{h+1} − W_{m-1}W_{m+1}W_h²` for `h ≥ m` | Wikipedia + Ward Memoir; this is exactly the "recurrence ⇔ relation" content |
|  2 | WebSearch (general form)         | elliptic divisibility sequence "elliptic net" Stange four-index relation rel4 division polynomial                      | yes  | Stange net relation `W(p+q+s)W(p−q)W(r+s)W(r) + (cyc) = 0`                            | = the project's `net`; arXiv:0710.1316 (Stange), edsformulary (Stange formulary) |
|  3 | WebSearch (named-after/aliases)  | Angdinata mathlib EDS formalization normEDS IsEllSequence Lean proof                                                   | yes  | confirms the mathlib `IsEllSequence` bare-formula def + that an Xu–Angdinata **PR** carries this | the searched snippet literally states the algebraic proof "for formalization in Lean … most results are in the pull request to Lean's Mathlib, in EllipticDivisibilitySequence.lean" |
|  4 | ChatGPT MCP                      | (full self-contained question on whether "term recurrences ⇒ full relation" is named/standard, its generality, proof, mathlib status) | n/a | — | **MCP DOWN** (Codex backend errored, as the task warned). Compensated with extra WebSearch/WebFetch channels below. |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                                                | n/a  | (directory absent; no `refs/NagellLutz/` store either)                               | recorded n/a — no PDFs available locally for this project |
|  6 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                                      | n/a  | nLab has no dedicated EDS/elliptic-net page                                           | not a category-theoretic concept; covered instead by Stange/Ward primary sources |
|  7 | nCatLab                          | —                                                                                                                     | n/a  | —                                                                                    | not a categorical concept |
|  8 | Stacks Project                   | —                                                                                                                     | n/a  | —                                                                                    | EDS/Ward recurrences are not in Stacks (not scheme-theoretic foundational material) |
|  9 | MathOverflow / Math.SE           | (covered transitively via WebSearch #1–#3 result sets)                                                                 | partial | Ward recurrence forms appear in MO/MSE answers reached via #1                       | no additional standard-form variant beyond Ward/Stange |
| 10 | recent arXiv (≤5 yr)             | "On Elliptic Sequences over Commutative Rings" — fetched arXiv:2604.05280 (abstract + body)                            | yes  | **Theorem 2.2**: the two recurrences (odd + even) ⇒ full elliptic relation, over **commutative rings**, with **non-zero-divisor** conditions on `W 1, W 2` | **Junyan Xu, Apr 7 2026.** Exact match to this Lean theorem incl. the `CommRing` + `R⁰` hypotheses; "standard EDSs are elliptic by purely algebraic methods" |

ChatGPT-MCP outage mitigation: ran two extra WebFetch passes (arXiv:2604.05280 abstract + PDF body,
and the live mathlib4 docs page) to recover both the standard-form/generality question (Q to the MCP
#1–#3) and the mathlib-status question (Q #4). Both were answered concretely; see Phase 5.

### Literature summary (Phase 3)

Concept identified as: the **"recurrence ⇒ elliptic relation" theorem** for elliptic (divisibility)
sequences — Ward's classical result that the single-index recurrences defining the sequence force the
full two-variable Ward relation; in modern commutative-ring generality this is **Theorem 2.2 of Xu,
*On Elliptic Sequences over Commutative Rings* (arXiv:2604.05280, 2026)**. The four-index relation
the proof goes through is **Stange's elliptic-net relation** (arXiv:0710.1316).

Sources agree on the standard form: **yes.** Ward (classical, over ℤ / with `W₁ = 1`) and Xu (modern,
over a commutative ring with `W 1, W 2` non-zero-divisors) state the same implication; Xu is the
explicit generalisation to commutative rings and is the direct source of this Lean formalization.

Most general standard form: over a **commutative ring** `R`, for an odd `W` with `W 0 = 0` and
`W 1, W 2 ∈ R⁰`, the two recurrences (odd for `m ≥ 2`, even for `m ≥ 3`) imply the full elliptic
relation. This is *exactly* the Lean statement.

Generality dimensions where the literature varies:
  - **coefficient ring**: classical Ward = ℤ (or a field, `W₁=1`); Xu/this Lean form = arbitrary
    commutative ring. The Lean form sits at the **most general** end.
  - **non-degeneracy hypothesis**: classical = `W₁ = 1` (and integral); Xu/Lean = `W 1, W 2 ∈ R⁰`
    (non-zero-divisors), which is the correct weakest hypothesis over a general commutative ring
    (you need to cancel `W 1`, `W 2` to run the recurrences, and "non-zero-divisor" is exactly
    "cancellable").

Disagreement with the literature: **none.** The Lean statement is the modern commutative-ring
form verbatim.

---

### Generality analysis — `IsEllSequence.of_oddRec_evenRec`

Literature-standard form (from Phase 3): over a commutative ring `R`, odd `W` with `W 0 = 0` and
`W 1, W 2 ∈ R⁰`, the odd+even recurrences ⇒ the full elliptic relation (Xu Thm 2.2).

| # | Parameter / hypothesis            | Current Lean form                      | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------|--------------------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`                    | commutative ring                       | commutative ring (Xu); ℤ/field (classical) | NO                  | Already the most general ground ring used in the literature. Commutativity is essential (the relation is a symmetric quartic identity); going to non-commutative is not a studied/meaningful generalisation. |
| 2 | `(one : W 1 ∈ R⁰)`, `(two : W 2 ∈ R⁰)` | `W 1, W 2` non-zero-divisors      | non-zero-divisors (Xu); `W₁ = 1` (classical) | NO (already weakest)| Non-zero-divisor is the precise hypothesis that lets you cancel `W 1`, `W 2` when deriving the relation; `W₁ = 1` is a *special case*. Cannot weaken further: with `W 1` a genuine zero-divisor the cancellation (and the conclusion) can fail. |
| 3 | `(neg : ∀ k, W (-k) = -W k)`      | `W` odd                                | odd (anti-symmetric sequence — Ward)        | NO                  | Oddness is part of the definition of a Ward two-sided elliptic sequence; the elliptic relation itself is only sensible for the antisymmetric extension. |
| 4 | `(zero : W 0 = 0)`                | `W 0 = 0`                              | `W 0 = 0` (Ward normalisation)              | NO                  | Standard normalisation; forced by oddness anyway (`W 0 = −W 0`) once `2` is cancellable, and needed for the `addMulSub_same` simplifications. |
| 5 | recurrence ranges `m ≥ 2` / `m ≥ 3` | as stated                          | same effective content                      | NO (already minimal)| These are the minimal index ranges that are not already trivially true; tightening would drop needed cases, loosening adds vacuous/redundant ones. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0.** Every hypothesis is either definitional (oddness,
`W 0 = 0`), already the weakest workable form (`W 1, W 2 ∈ R⁰` vs. the classical `W₁ = 1`), or the
most general ground ring (`CommRing`). The Lean statement *is* the modern literature-standard form
(Xu Thm 2.2).
Proposed restatement: none needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                              | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                   | no       | — | The hypotheses (`neg`, `zero`, recurrences) are genuine *propositional* facts about a specific `W`, not structure that should be a class. Bundling them as a class (`[IsNormalisedEDS W]`) would be premature; mathlib keeps `IsEllSequence` as a plain `Prop` and this theorem matches that style. |
|  2 | sequences/metric → filters/topological?                                                              | no       | — | Purely algebraic identity over a discrete index `ℤ`; no limiting/topological content. |
|  3 | construct an object → universal-property class?                                                      | no       | — | This is an implication between predicates, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                   | no       | — | No substructure here. |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                                             | no (already done) | — | Already at `CommRing`; this row's weakening is *already realised* (the whole point of Xu's paper vs. the classical field/ℤ statement). |
|  6 | 1-categorical → higher-categorical?                                                                  | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive group/monoid?                                              | no       | — | The index is intrinsically `ℤ` (two-sided antisymmetric sequence; `m ± n` halving and parity are essential). Generalising the index is not a meaningful move for EDS. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** The statement already embodies the one real modernisation move
that exists in this area — weakening the ground from a field/ℤ to an arbitrary commutative ring with
non-zero-divisor cancellation (exactly Xu's contribution). It uses mathlib's `nonZeroDivisors`
(`R⁰`) idiom and `Int.negOnePow` for parity, both contemporary. No further idiomatic restatement
improves organisation.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no new definitional equalities or typeclass-search paths
introduced). Skipped.

---

### Mathlib search-status: `IsEllSequence.of_oddRec_evenRec`

[A] Lean-Finder       — (offline; not available in this stale-build env)             n/a: index unavailable; compensated by [D]+[E]+live-docs
[B] Loogle            `IsEllSequence (_ : ℤ → _)` ; `?W (?m+?n) * ?W (?m-?n) * _ = _` — (needs build; not run) n/a: env stale; compensated by [D]+live-docs
[C] LeanSearch        "elliptic sequence from odd and even recurrence", "recurrence implies elliptic relation" via WebSearch #3 → hit the mathlib docs page only n/a as a live index; result folded into [D]
[D] Grep mathlib src  `of_oddRec_evenRec`, `OddRec|EvenRec`, `rel₄|addMulSub|def net|HaveSameParity`, `Rel₃`, `IsEllSequence` over `.lake/packages/mathlib/Mathlib/` — **`of_oddRec_evenRec`: 0 hits; `OddRec|EvenRec`: 0 (only `Mathlib.Data.Nat.EvenOddRec`, unrelated); `rel₄|addMulSub|net|HaveSameParity|Rel₃`: 0; `IsEllSequence`: present (bare-formula def, 547-line file)** | **hits: only `IsEllSequence`/`normEDS` family; the entire `EllSequence` machinery + `of_oddRec_evenRec` are ABSENT**
[E] Name pattern / live docs  Fetched live mathlib4 docs for `Mathlib.NumberTheory.EllipticDivisibilitySequence` — confirmed **none** of `of_oddRec_evenRec, OddRec, EvenRec, rel₄, addMulSub, net, Rel₃, HaveSameParity₄, "elliptic net"` appear; `IsEllSequence` is defined **directly via the formula** (no `Rel₃` wrapper) | authoritative: the published mathlib lacks this theorem and its scaffolding

Searched for both:
  - the user's current form (`IsEllSequence.of_oddRec_evenRec`) → not in mathlib.
  - the literature-standard form (Xu Thm 2.2 = the same thing) → not in mathlib.
  - the more-general predicate `IsEllSequence` itself → present, but only the *definition* and the
    `normEDS`/`preNormEDS` construction; the **bridge theorem from recurrences to the relation is
    missing**. (Mathlib's current `normEDS`-is-elliptic story does not exist there — the file stops
    at the divisibility/`map`/`smul` lemmas; the elliptic-relation proof is precisely what this PR
    adds.)

Concluded: **not in mathlib** (grep over the pinned mathlib + the live mathlib4 docs both exhausted;
the literature-standard form is identical and is itself an in-flight Xu–Angdinata PR, i.e. *headed
into* mathlib but not yet merged at this pin).

---

### Call sites — `IsEllSequence.of_oddRec_evenRec`

Internal use count (NagellLutz, excluding the declaring lines 570/584/591/592): **1**
External-to-file callers: shared verbatim into **HasseWeil** (separate project) + the `Original`
snapshot.

| Caller file:line                                                                 | Usage pattern (one-line excerpt)                                                              |
|----------------------------------------------------------------------------------|----------------------------------------------------------------------------------------------|
| `NagellLutz/.../EllipticDivisibilitySequence.lean:961`                           | `refine IsEllSequence.of_oddRec_evenRec (normEDS_neg _ _ _) (normEDS_zero _ _ _) …` — proves `normEDS` is elliptic |
| `HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:589`                  | identical `refine IsEllSequence.of_oddRec_evenRec (normEDS_neg …) (normEDS_zero …)` (cross-project copy of the same dev) |
| `NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:912`                   | identical (snapshot copy)                                                                     |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `of_oddRec_evenRec`?):
  - (none) — every consumer that needs "`normEDS` / this `W` is elliptic" routes through this theorem;
    no site re-runs the `rel₄_of_oddRec_evenRec` reduction by hand.

Signal: **K = 1 internal use, but it is the *critical capstone step*** — it is the sole route to
`IsEllSequence.normEDS_of_mem_nonZeroDivisors` (line 959) and thence `IsEllSequence.normEDS`
(line 1212), the headline "the canonical EDS is elliptic" result. Plus a verbatim cross-project copy
in HasseWeil. This is a real public-API result, not a one-off. (Low raw K is expected for a *named
top-level theorem*: it is consumed once to establish the main corollary, then the corollary is what
everything else uses — the same shape as any "main theorem → main corollary" pair.)

---

### Composition check (Phase 6)

Can `IsEllSequence.of_oddRec_evenRec` be derived from mathlib in ≤3 chained calls?

Attempt 1: find a mathlib lemma "recurrences ⇒ `IsEllSequence`" and apply it.
  - Mathlib decls used: none exist (Phase 5: the entire `EllSequence` machinery is absent).
  - Result: **fails.** There is nothing in mathlib that takes `OddRec`/`EvenRec`-shaped hypotheses
    (these predicates don't even exist upstream) to `IsEllSequence`.

Attempt 2: reconstruct inline from mathlib primitives (`ring`, parity, `nonZeroDivisors`).
  - The actual proof reduces `Rel₃` to `rel₄ W (2m) (2n) (2r) 0 = 0` (`rel₃_iff₄`) and discharges it
    via `rel₄_of_oddRec_evenRec`, which itself rests on `rel₄_of_anti_oddRec_evenRec` (a multi-case
    strong induction using `dMin`/`cMin`, `addMulSub_mem_nonZeroDivisors`, the transfer lemmas) plus
    the `relFin4_perm` symmetry reduction (a `Submonoid.closure_induction` over `Perm (Fin 4)`).
  - Result: **fails.** This is hundreds of lines of bespoke development, not a 1–3-call mathlib
    composition. None of the sub-steps are mathlib primitives.

Conclusion: **NOT-COMPOSABLE.** (Phase 7 therefore considers the YES verdicts.)

---

## Verdict: `IsEllSequence.of_oddRec_evenRec`

**Category:** **YES-add-as-is**

**Evidence:**
- Literature search (Phase 3): identified as the classical Ward "recurrence ⇒ elliptic relation"
  theorem, in its modern commutative-ring form = **Theorem 2.2, Xu, arXiv:2604.05280 (2026)**;
  sources agree on the form; the Lean statement matches the most general standard form verbatim.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakenings; `CommRing` + `W 1,W 2 ∈ R⁰`
  is the weakest workable hypothesis set — strictly more general than the classical field/`W₁=1`
  statement). Modern-idiom check: no further idiomatic restatement improves it.
- Mathlib search (Phase 5): **not in mathlib** — grep over the pinned mathlib AND the live mathlib4
  docs both confirm `of_oddRec_evenRec`, `OddRec`, `EvenRec`, `rel₄`, `net`, `Rel₃`,
  `HaveSameParity₄` are all absent; only the bare `IsEllSequence` def + `normEDS` construction exist
  upstream.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the proof is a deep multi-case induction over a
  permutation-symmetry reduction, not a ≤3-call mathlib composition.

**Rationale (1–2 paragraphs):**

This is a genuine, named, capstone theorem of the elliptic-divisibility-sequence theory: it is the
algebraic bridge proving that the two term-by-term recurrences defining a normalised EDS force the
full two-variable Ward elliptic relation. It is exactly Theorem 2.2 of Junyan Xu's 2026 paper *On
Elliptic Sequences over Commutative Rings* — and that paper states explicitly (and the web search
corroborated) that the development was written "for formalization in Lean … most results are in the
pull request to Lean's Mathlib, in EllipticDivisibilitySequence.lean," joint with David Kurniadi
Angdinata. In other words this file *is* an in-flight mathlib PR sitting ahead of the repo's mathlib
pin; the theorem is not merely mathlib-worthy, it is already on its way in. Both the pinned mathlib
and the live mathlib4 docs confirm it (and its entire `EllSequence` scaffolding) is currently
absent, so there is no duplication and nothing to specialise from.

The form is already at the correct, maximal generality: an arbitrary commutative ring with `W 1` and
`W 2` non-zero-divisors — the precise cancellation hypothesis, strictly generalising the classical
`W₁ = 1`-over-a-field statement — so YES-but-generalise-first does not apply (Phase 4b: MAXIMALLY
GENERAL; Phase 4c: no idiom move). It is not composable from mathlib primitives (Phase 6:
NOT-COMPOSABLE — the proof is a substantial induction). And it has a real consumer: it is the sole
route to `IsEllSequence.normEDS` (the canonical-EDS-is-elliptic headline), and is already shared
verbatim into a second project (HasseWeil). All gates for YES-add-as-is are satisfied.

**WHY add it (refactor-actionable):**
- **New mathematical content mathlib lacks:** the implication "`OddRec`(m≥2) ∧ `EvenRec`(m≥3) ⇒
  `IsEllSequence W`". Mathlib today *defines* `IsEllSequence` and *constructs* `normEDS`/`preNormEDS`
  but has **no proof that `normEDS` is elliptic** — the file stops at divisibility/`map`/`smul`. This
  theorem (plus its scaffolding `rel₄`, `net`, `OddRec`, `EvenRec`, `rel₄_of_anti_oddRec_evenRec`) is
  precisely the missing piece. Named gap: mathlib's `EllipticDivisibilitySequence.lean` advertises
  `normEDS` as "the canonical example of a normalised EDS" yet never establishes its defining
  elliptic property; this theorem closes that gap (the in-flight Xu–Angdinata PR is the mechanism).
- **Composes with mathlib's existing API:** once added, `IsEllSequence.smul`, `.map`,
  `IsEllDivSequence`, and the division-polynomial development (`Mathlib.AlgebraicGeometry.
  EllipticCurve.DivisionPolynomial.*`, which the NagellLutz project also forks) can finally invoke
  "`normEDS` is elliptic" — enabling the group-law / `n`-division-polynomial results that motivated
  the paper.

Proposed mathlib location:    `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the existing
                              file — this is an expansion of it, not a new file).
Proposed PR title:            "feat(NumberTheory): elliptic sequences over commutative rings — the
                              recurrences imply the elliptic relation" (the umbrella PR that adds the
                              `EllSequence` namespace + `IsEllSequence.of_oddRec_evenRec`).
PR grouping:                  **Ship as ONE PR with the whole `EllSequence` development** — at minimum
                              `addMulSub`, `rel₄`, `net`, `HaveSameParity₄`, `OddRec`, `EvenRec`,
                              `rel₃_iff₄`, the `Perm` symmetry lemmas, `rel₄_of_anti_oddRec_evenRec`
                              (already verdict YES-add-as-is), and this capstone. These are not
                              independently meaningful and the prior sibling assessments
                              (`OddRec` → YES, `rel₄_of_anti_oddRec_evenRec` → YES,
                              `rel₃_iff_oddRec` → BORDERLINE-as-internal-glue) confirm the grain: the
                              namespace goes up as a unit. This is in fact already the structure of
                              the upstream Xu–Angdinata PR.
Pre-PR checklist before opening:
  - [ ] Confirm against the actual open Xu–Angdinata mathlib PR (this may already be merged/under
        review upstream — coordinate rather than duplicate; the daily bump may bring it in).
  - [ ] `/generalise IsEllSequence.of_oddRec_evenRec` — confirm no further weakening (expected: none;
        Phase 4b already MAXIMALLY GENERAL).
  - [ ] `/cleanup EllipticDivisibilitySequence.lean` on the `EllSequence` block — style/naming audit
        before upstreaming.
  - [ ] Reviewer: whoever is handling the EDS/elliptic-curve area (Angdinata / Xu themselves).

---

## Next step

Confirm against the open Xu–Angdinata mathlib PR (this theorem is part of an in-flight upstreaming of
*On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280) — it may already be in review or
land via the daily mathlib bump; coordinate rather than open a duplicate. If not yet upstream, ship
the entire `EllSequence` namespace (with `OddRec`, `rel₄_of_anti_oddRec_evenRec`, etc. — all prior
YES-add-as-is) as one `feat(NumberTheory)` PR expanding
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, with this capstone as the headline. Run
`/generalise` then `/cleanup` on the block first.

Sources:
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Xu, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 (2026)](https://arxiv.org/abs/2604.05280)
- [Stange, *Elliptic nets and elliptic curves*, arXiv:0710.1316](https://arxiv.org/abs/0710.1316)
- [Stange, *Formulary for elliptic divisibility sequences and elliptic nets*](https://math.colorado.edu/~kstange/papers/edsformulary.pdf)
- [Mathlib.NumberTheory.EllipticDivisibilitySequence (live docs)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html)
