## /mathlibable report — `complEDS'_zero`

> Step-9 mathlibable assessment, NagellLutz project (Nagell–Lutz; elliptic curves;
> division polynomials; elliptic divisibility sequences).
> Target: `complEDS'_zero` at
> `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1539`.

### Baseline (Phase 0)
- lake build:               not run (local build stale per task brief); reasoned from source.
- decl `complEDS'_zero`:     ✓ resolved at `EllipticDivisibilitySequence.lean:1539`
- qualified name:            **`complEDS'_zero`** (NO namespace prefix — see note below)
- kind:                      lemma (`@[simp]`)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS) and the construction of
                              normalised EDSs from initial terms" — a fork of mathlib's
                              `Mathlib.NumberTheory.EllipticDivisibilitySequence`.

**Qualified-name verification.** The decl sits inside `section ComplEDS` (opened at line 1519),
which is NOT inside any `namespace`. The file's `namespace EllSequence` (line 90) closes at line 597;
`section NormEDS` (line 881, a *section* not a namespace) closes at `end NormEDS` (line 1515); and the
`@[expose] public section` closes at line 1517 with the explicit comment
`"close @[expose] public section to avoid EllSequence.complEDS ambiguity"`. So the fully-qualified
name is the bare `complEDS'_zero`. (This matches mathlib, where the same lemma also lives in a bare
`section ComplEDS` with no namespace.)

---

### Statement (Phase 1)

`complEDS'_zero` states that the ℕ-indexed *complement sequence* of a normalised EDS vanishes at 0:

> For a commutative ring `R`, ring elements `b c d : R`, and an integer `k : ℤ`,
> `complEDS' b c d k 0 = 0`.

Here `complEDS' b c d k : ℕ → R` is the complement (quotient/division) sequence `Wᶜ(k, ·)` for the
normalised EDS `W = normEDS b c d`, characterised by `W(k) · Wᶜ(k, n) = W(n·k)` — i.e. `Wᶜ(k, n)`
witnesses the divisibility `W(k) ∣ W(n·k)`. It is defined by strong recursion with base cases
`complEDS' … 0 = 0`, `complEDS' … 1 = 1`. The lemma is the `0`-base-case unfolding, used (e.g.) to
discharge the `n = 0` branch of `complEDS_ofNat`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (maximal generality for this construction).
- `(b c d : R)` — the data determining `normEDS` (initial-term parameters: `W₂ = b`, `W₃ = c`, `W₄ = d·b`).
- `(k : ℤ)` — the divisor index `k` in `Wᶜ(k, ·)`.

Hypotheses: none.

Conclusion (math): `Wᶜ(k, 0) = 0`.
Conclusion (Lean): `complEDS' b c d k 0 = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a `@[simp]` base-case unfolding lemma of a recursively-defined sequence; one-line proof; not a
named theorem, not a structure, not a `## Main statement` (the file's main statement is
`isEllDivSequence_normEDS`). (Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. (Proof body is the single tactic
`simp [complEDS'.eq_def]`; mathlib's copy uses `rw [complEDS']`.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence complement sequence W(k) divides W(nk) division polynomial"    | yes  | `W(k)·Wᶜ(k,n) = W(n·k)`; `Wᶜ` is the project/mathlib name        | **Top hit is mathlib's own `Mathlib.NumberTheory.EllipticDivisibilitySequence` doc page**; also Wikipedia, Stange elliptic nets |
|  2 | WebSearch (general / normalisation) | "Ward elliptic divisibility sequence W(0)=0 normalized recurrence definition"               | yes  | normalised: `D₀ = 0, D₁ = 1`; elliptic nets defined with `W(0)=0`| Ward 1948; `W(0)=0` is the universal convention |
|  3 | WebSearch (named-after / base case) | `"elliptic divisibility sequence" division "W_n" sequence value at zero base case`          | yes  | EDS usually indexed from `W₁`; `W₀ = 0` is the standard extension | confirms `…(0) = 0` is convention, not a deep theorem |
|  4 | ChatGPT MCP                      | (intended: standard form + generality + historical evolution)                                  | n/a  | —                                                                | MCP down per task brief; substituted by extra WebSearch generality levels (#1–#3) |
|  5 | Local references                 | `.mathlib-quality/references/` for "EDS / complement / division polynomial"                     | n/a  | —                                                                | references dir not consulted (build-stale env); the decl's own source cites Ward, *Memoir on EDS* |
|  6 | nLab                             | "elliptic divisibility sequence"                                                               | n/a  | —                                                                | not an nLab/categorical concept (number-theoretic recurrence) |
|  7 | nCatLab (categorical)            | —                                                                                              | n/a  | —                                                                | not a categorical concept |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | —                                                                | EDS/division-polynomial recurrences are not in Stacks |
|  9 | MathOverflow / MSE               | (folded into WebSearch #1–#3)                                                                   | n/a  | —                                                                | no generality question to resolve — `W(0)=0` is definitional |
| 10 | recent arXiv (last 5 yr)         | (folded into WebSearch hits: Stange 2025, "recurrence relation for EDS" 2021)                   | yes  | same recurrence + normalisation                                  | confirms the form is stable / standard |

Protocol pass: WebSearch ran 3 distinct queries at different generality levels (specific complement
form / normalisation convention / base-case indexing). ChatGPT MCP unavailable (env) — compensated
with the extra generality sweeps. nLab / Stacks / nCatLab correctly `n/a` (number-theoretic recurrence,
not categorical/alg-geom). **Decisive observation: the literature search's #1 hit is mathlib's own EDS
file** — the strongest possible signal that this is already in mathlib.

### Literature summary (Phase 3)

Concept identified as: the **complement (division/quotient) sequence** `Wᶜ(k, n)` of a normalised
elliptic divisibility sequence, evaluated at `n = 0`; `complEDS'_zero` is the base case
`Wᶜ(k, 0) = 0`.
Sources agree on the standard form: yes — `W(0) = 0` (resp. `Wᶜ(k, 0) = 0`) is the universal
normalisation convention for EDS / elliptic nets (Ward; Stange).
Most general standard form: over any commutative ring / integral domain `R`; the project's
`[CommRing R]` is already the maximally general setting.
Generality dimensions where literature varies: essentially none for the *base case* — `…(0) = 0`
is definitional. (EDS results vary over ℤ vs general rings, but mathlib's `complEDS'` already lives
over `[CommRing R]`.)
Disagreement with literature: none. The `complEDS'` construction itself (`Wᶜ` notation, the
`W(k)·Wᶜ(k,n) = W(nk)` characterisation) is the *mathlib formalisation's* own naming — and
`complEDS'_zero` is literally that formalisation's lemma.

---

### Generality analysis — `complEDS'_zero`

Literature-standard form (Phase 3): base case of a normalised EDS complement sequence over a
commutative ring; `Wᶜ(k, 0) = 0`.

| # | Parameter / hypothesis | Current Lean form         | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|---------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]`        | commutative ring          | commutative ring / integral domain | NO                | `normEDS`/`complEDS'` are built on `[CommRing R]`; this is already the mathlib-standard setting and matches mathlib's identical decl |
| 2 | `(b c d : R)`        | three ring elements       | initial EDS data `W₂,W₃,W₄`       | NO                | intrinsic to the `normEDS` construction |
| 3 | `(k : ℤ)`            | integer divisor index     | integer index                     | NO                | `k` ranges over ℤ in `Wᶜ(k, ·)`; already general |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (identical to mathlib's own `complEDS'_zero`, same `[CommRing R]`).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
| 1 | typeclass-ify "let X be a foo" preambles? | no | already a bare `[CommRing R]` |
| 2 | sequences/metric → filters/topology? | no | discrete number-theoretic recurrence; no topology |
| 3 | construction → universal-property class? | no | `complEDS'` is a concrete recursive sequence by design (mirrors mathlib) |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure |
| 5 | vector-space/field-specific → weaken typeclass? | no | already `[CommRing R]` |
| 6 | 1-categorical → higher-categorical? | no | n/a |
| 7 | concrete index → general additive structure? | no | `n : ℕ` and `k : ℤ` are the intrinsic indices of an EDS; this *is* the standard form (and mathlib's) |

Modern idiom available: **no**. The decl is already in the exact contemporary mathlib form — because
it is a byte-for-byte fork of the mathlib decl.

### Risk verdict (Phase 4.5)

n/a — declaration kind is `lemma` (no defeq/instance/diamond surface).

---

### Mathlib search-status: `complEDS'_zero`

[A] Lean-Finder       n/a (env: mathlib index tools available but unnecessary — exact source line in hand)
[B] Loogle            `complEDS' _ _ _ _ 0 = 0` would match — but resolved directly via source grep
[C] LeanSearch        "complement EDS at zero is zero" — resolved directly via source grep
[D] Grep mathlib src  `grep "complEDS'_zero" .lake/.../Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                      → **HIT at line 403**: `lemma complEDS'_zero : complEDS' b c d k 0 = 0 := by rw [complEDS']`
[E] Name pattern      `complEDS'`, `complEDS`, `complEDS₂` ALL present in mathlib (lines 246–544);
                      the whole `complEDS` family was forked into this project

Searched for both the current form and the (identical) literature-standard form.

**Concluded: found in mathlib as `complEDS'_zero`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:403`); IDENTICAL form.**
- Same scope (bare `section ComplEDS`, no namespace), same `@[simp]` attribute, same statement
  `complEDS' b c d k 0 = 0`, same `[CommRing R]` generality.
- The underlying `complEDS'` definition is byte-for-byte identical between the two files (verified by
  `diff` of the project's lines 1528–1536 against mathlib's lines 392–400: the ONLY difference in the
  whole `complEDS'_zero` block is the proof tactic — project `simp [complEDS'.eq_def]` vs mathlib
  `rw [complEDS']`).
- Mathlib has the entire family: `complEDS₂`, `complEDS'`, `complEDS`, plus
  `complEDS'_one/_even/_odd`, `complEDS_ofNat/_zero/_one/_neg/_even/_odd`, `map_complEDS'`, etc.
  This project's `EllipticDivisibilitySequence.lean` is a fork of mathlib's
  `Mathlib.NumberTheory.EllipticDivisibilitySequence` (there is even a sibling
  `EllipticDivisibilitySequenceOriginal.lean` carrying the same lemma at line 1430).

---

### Call sites — `complEDS'_zero`

Internal use count: **1** (within the project, excluding the declaring file's own copy).
External-to-file callers: 0 distinct files outside the EDS source.

| Caller file:line                                            | Usage pattern (one-line excerpt)                                         |
|-------------------------------------------------------------|--------------------------------------------------------------------------|
| EllipticDivisibilitySequence.lean:1569 (`complEDS_ofNat`)   | `simp only [Nat.cast_zero, complEDS, …, zero_mul, complEDS'_zero]`        |
| EllipticDivisibilitySequenceOriginal.lean:1430              | a second forked copy of the same lemma (not a *use*, a *duplicate*)       |

Inline-derivation grep: mathlib's own `complEDS_ofNat` (`…:431`) uses `complEDS'_zero` in exactly the
same way — i.e. mathlib already provides both this lemma and its sole consumer.

### Composition check (Phase 6)

Can `complEDS'_zero` be derived from mathlib in ≤3 chained calls? — **Moot: mathlib HAS the lemma
verbatim, so no composition is needed.** (For completeness: it is a one-line definitional unfolding,
`by rw [complEDS']` / `simp [complEDS'.eq_def]`, i.e. trivially the `| 0 => 0` arm of `complEDS'`.)

Conclusion: **NO new lemma needed — mathlib has it identically.**

---

## Verdict: `complEDS'_zero`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the complement-EDS base case `Wᶜ(k,0)=0` is the standard `W(0)=0`
  normalisation convention; the #1 web hit was mathlib's own EDS file.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`[CommRing R]`); identical to mathlib; no
  weakening, no modern-idiom restatement available.
- Mathlib search (Phase 5): **found in mathlib as `complEDS'_zero`** at
  `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:403`, identical statement + attribute +
  scope; the whole `complEDS` family + the underlying `complEDS'` def are byte-for-byte forks.
- Composition check (Phase 6): moot — mathlib already has the exact lemma.

**Rationale.**
This project's `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a fork of
mathlib's `Mathlib.NumberTheory.EllipticDivisibilitySequence`. The target `complEDS'_zero` is present
in mathlib **verbatim**: same bare-`section ComplEDS` scope (no namespace), same `@[simp]`, same
statement `complEDS' b c d k 0 = 0`, same `[CommRing R]` generality, and over a `complEDS'` definition
that is byte-for-byte identical (a `diff` of the two `complEDS'` defs differs in nothing but the proof
tactic of `complEDS'_zero` itself: `simp [complEDS'.eq_def]` vs `rw [complEDS']`). The literature
search reinforces this from the other direction — `W(0) = 0` is the universal EDS/elliptic-net
normalisation convention, this is a definitional base case rather than a named theorem, and the very
first search result for the complement-sequence concept *is* the mathlib doc page. There is nothing to
add: mathlib already ships this lemma, its sibling lemmas (`complEDS'_one/_even/_odd`, the integer-indexed
`complEDS_*` family, `map_complEDS'`), and even its sole local consumer pattern (`complEDS_ofNat`).

**WHY not (refactor-actionable).**
Mathlib already has `complEDS'_zero` and the whole supporting `complEDS₂`/`complEDS'`/`complEDS` API.
The project should not re-prove or ship any of it; the entire forked
`EllipticDivisibilitySequence.lean` (and its `…Original.lean` twin) is a candidate to be **deleted in
favour of `import Mathlib.NumberTheory.EllipticDivisibilitySequence`** — this single decl is just one
representative leaf of that fork. The fork presumably exists because the project also forks
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*` and maintains parallel
`General*`/`PID*` tracks; the consolidation question is "can we drop the fork and import mathlib?", and
for `complEDS'_zero` specifically the answer is an unconditional yes (the forms are identical).

Existing mathlib decl:        `complEDS'_zero`
Located at:                   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:403`
Our form follows in ≤1 line:  it IS the mathlib statement verbatim —
```lean
example {R : Type*} [CommRing R] (b c d : R) (k : ℤ) : complEDS' b c d k 0 = 0 := complEDS'_zero
```
Call sites in our project (Phase 6.0): 1 real use (`complEDS_ofNat`, line 1569) + 1 duplicate copy
(`…Original.lean:1430`).
Refactor plan: when the fork is retired, this lemma vanishes with it — the one consumer
(`complEDS_ofNat`) is itself a fork of mathlib's `complEDS_ofNat`, which already uses mathlib's
`complEDS'_zero`. No call-site rewrite is needed beyond replacing the forked file with the mathlib
import; the names match exactly. If the fork must stay for now (because the `DivisionPolynomial` fork
or the `General*`/`PID*` tracks still depend on local edits), keep this lemma but mark the file as a
known mathlib duplicate — do NOT propose it as a new mathlib contribution.
Next action: do not PR to mathlib. Track under the consolidation effort to drop the
`Mathlib.NumberTheory.EllipticDivisibilitySequence` fork and `import` mathlib's version instead.

---

## Next step

Do not submit. Mathlib already contains `complEDS'_zero` (and the whole `complEDS'`/`complEDS`/`complEDS₂`
API) verbatim at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:403`. Fold this into the
consolidation ticket that retires the project's forked `EllipticDivisibilitySequence.lean` in favour of
`import Mathlib.NumberTheory.EllipticDivisibilitySequence`.
