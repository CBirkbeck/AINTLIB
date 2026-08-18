# /mathlibable report — `universalNormEDS_mem_nonZeroDivisors`

### Baseline (Phase 0)
- lake build:               (not re-run — local build stale per task note; reasoned from source + mathlib src reads)
- decl `universalNormEDS_mem_nonZeroDivisors`: ✓ resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1257`
- **Qualified name (VERIFIED):** `universalNormEDS_mem_nonZeroDivisors` — **top-level, no namespace.**
  The enclosing `namespace EllSequence` (line 90) closes at line 597; `namespace IsEllSequence`
  (643) closes at 702; the inner `namespace EllSequence` blocks (1079, 1356) close at 1112 / 1431.
  Between line 1116 (`section Map`) and line 1261 there is **no `namespace`** — only `section`s.
  Confirmed by the sibling `def universalNormEDS` (line 1186), declared as plain `universalNormEDS`,
  not `EllSequence.universalNormEDS`. So the parsed name in the task is correct.
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS). This file is a **fork** that
  expands the upstream `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (which contains the
  `IsEllSequence`/`preNormEDS`/`normEDS` API but **none** of the `addMulSub`/`rel₄`, `compl₂EDS`,
  `universalNormEDS`, or `Param` machinery this fork adds).

---

### Statement (Phase 1)

`universalNormEDS_mem_nonZeroDivisors` states: for every nonzero integer `n`, the value of the
**universal normalised EDS** at `n` is a **non-zero-divisor** of the polynomial ring
`MvPolynomial Param ℤ`.

```lean
omit ellW ellU in
lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :
    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)
```

Project-local vocabulary (all absent from mathlib):
- `Param` (line 1178): `inductive Param : Type | B | C | D` — a 3-element index type for the three
  parameters `b, c, d` of a normalised EDS.
- `universalNormEDS` (line 1186): `noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ :=`
  `normEDS (X B) (X C) (X D)` — the normalised EDS with the three parameters replaced by the three
  polynomial generators `X B, X C, X D`. It is "universal" in that any concrete `normEDS b c d` is
  recovered by `aeval (Param.rec b c d)` (the `normEDS_eq_aeval` device, line 1188); this lets the
  fork reduce identities about `normEDS` to the single universal integral-domain case.
- `universalNormEDS_ne_zero` (line 1250): for `n ≠ 0`, `universalNormEDS n ≠ 0` (proved by
  specialising `aeval (Param.rec (2,3,2))`, where `normEDS 2 3 2 = id`, so `universalNormEDS n` maps
  to `(n : ℤ) ≠ 0`).
- `R⁰` notation (`open scoped nonZeroDivisors`, line 88) `= nonZeroDivisors R : Submonoid R`.

Variables / typeclasses: none beyond the ambient `MvPolynomial Param ℤ` (a fixed concrete ring).
`MvPolynomial Param ℤ` is an integral domain: `ℤ` is a domain and `MvPolynomial σ R` is
`NoZeroDivisors` whenever `R` is (`Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean:37–39`); the
instance resolves automatically, so the lemma needs no `NoZeroDivisors`/`Nontrivial` hypothesis.

Hypothesis: `hn : n ≠ 0`.
Conclusion (math): the universal normalised EDS value `universalNormEDS n` is a non-zero-divisor.
Conclusion (Lean): `universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰`.

Proof (verbatim, line 1259): `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)` — i.e.
"`universalNormEDS n ≠ 0` (the sibling lemma) ⟹ it is a non-zero-divisor (because the ambient ring
is a domain)." A **single** mathlib call applied to one project-local fact.

---

### Size classification (Phase 2a)

Verdict: SMALL.
Reason: a helper lemma — not a `def`/`class`/`structure`, not named after a person, not a
`## Main statement`. It is pure non-zero-divisor plumbing whose only job is to feed the `mem`
hypothesis of `normEDS_mul_complEDS_of_mem` (used once, line 1345). Proof is a single term.

### One-line check (Phase 2b)

Kind is `lemma`, not `def`/`abbrev`/`structure` — one-liner-def check is n/a. (For the record the
*proof* is a single application, a weak negative signal for independent mathlib inclusion.)

---

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific) | "universal normalised elliptic divisibility sequence MvPolynomial nonzero divisor formalization mathlib" | partial | mathlib `EllipticDivisibilitySequence` / `DivisionPolynomial` API; "polynomial-law / universal" formalization patterns | No literature result named "universal normEDS is a non-zero-divisor"; the construction is a Lean device, not a theorem with a name. |
| 2 | WebSearch (source paper) | "elliptic divisibility sequence over commutative rings universal normEDS Angdinata division polynomial nonzero" | yes | **arXiv 2604.05280** "On Elliptic Sequences over Commutative Rings" — explicitly: "an elliptic sequence is determined by 4 initial terms if `h₂h₁` is not a zero-divisor." | The exact source paper this fork formalizes. The "reduce to the universal MvPolynomial case" trick is its formalization method; the per-`n` non-zero-divisor statement is implementation glue. |
| 3 | WebSearch (named-after / aliases) | covered by #1/#2 (Ward "Memoir on EDS"; Stange "elliptic nets"; Wikipedia EDS) | yes | recurrence / divisibility relations; `hₙ ∣ hₘ` when `n ∣ m` | underlying objects standard; this closure lemma is not in the literature. |
| 4 | ChatGPT MCP | n/a — MCP reported down per task note; substituted by extra WebSearch (#2) targeting the source paper + reasoning from the one-line proof | n/a | — | the standard-form question is answered by the source paper (#2). |
| 5 | Local references | `.mathlib-quality/references/` empty; `refs/NagellLutz/` absent | n/a | — | recorded n/a. |
| 6 | nLab / nCatLab | "non-zero divisor", "elliptic divisibility sequence" | n/a | nLab has the general notion of (non-)zero-divisor; no EDS-universal page | the only general fact ("nonzero ⟹ non-zero-divisor in a domain") is folklore commutative algebra. |
| 7 | Stacks Project | "nonzerodivisor" / "domain" | folklore | in a domain every nonzero element is a non-zero-divisor (an integral domain has no zero-divisors by definition) | exactly mathlib's `mem_nonZeroDivisors_of_ne_zero`. |
| 8 | MathOverflow / MSE | "in an integral domain a nonzero element is a non-zero-divisor" | yes (folklore) | true by definition of integral domain / `NoZeroDivisors` | precisely what mathlib encodes. |
| 9 | recent arXiv (≤5y) | "elliptic sequences over commutative rings" (2026) | yes | arXiv 2604.05280 (same as #2) | confirms the whole `universalNormEDS` machinery is current-research / in-formalization, NOT yet upstream. |

### Literature summary (Phase 3)

Concept identified as: a **per-index non-zero-divisor statement for the universal normalised EDS** —
"the universal normalised EDS value at `n ≠ 0` is a non-zero-divisor of `MvPolynomial Param ℤ`."

The only genuinely mathematical fact involved is the folklore *"in an integral domain a nonzero
element is a non-zero-divisor"* (true by definition of `NoZeroDivisors`). Everything else
(`universalNormEDS`, `Param`, the `aeval (Param.rec …)` universal-reduction trick) is bespoke to the
source paper **arXiv 2604.05280** and its Lean formalization. The lemma *as stated* has **no
independent literature existence** — it only makes sense relative to the fork's `universalNormEDS`
definition.

Most general standard form: "In a `MonoidWithZero` with `NoZeroDivisors`, `x ≠ 0 → x ∈ M₀⁰`."
Mathlib already states this maximally generally (`mem_nonZeroDivisors_of_ne_zero`), and even gives the
`@[simp]` iff (`mem_nonZeroDivisors_iff_ne_zero`, with `[Nontrivial]`).

Generality dimensions where the literature varies: none relevant — the wrapping is fixed by the
specific universal-EDS construction. Disagreement with the literature: none.

---

### Generality analysis — `universalNormEDS_mem_nonZeroDivisors`

Literature-standard form (from Phase 3): the maximally-general fact is
`mem_nonZeroDivisors_of_ne_zero` for a `MonoidWithZero` + `NoZeroDivisors` — already in mathlib and
already maximal. This lemma is a **specialisation** of that to the single value `universalNormEDS n`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | ambient ring | fixed `MvPolynomial Param ℤ` (a domain) | any `MonoidWithZero` + `NoZeroDivisors` | yes (for the *core* fact) | but generalising the ring is meaningless without also generalising `universalNormEDS`, which is intrinsically valued in `MvPolynomial Param ℤ`. Not an independent weakening of *this* lemma. |
| 2 | `hn : n ≠ 0` | the exact input needed | the `x ≠ 0` premise of `mem_nonZeroDivisors_of_ne_zero` (via `universalNormEDS_ne_zero`) | NO | cannot be weakened: `universalNormEDS 0 = normEDS_zero = 0`, which is a zero-divisor. |

### Generality verdict (Phase 4b)

The current form is MAXIMALLY GENERAL *for what it states*: it is the tightest specialisation of the
already-maximal `mem_nonZeroDivisors_of_ne_zero`, composed with the sibling `universalNormEDS_ne_zero`.
It is **not** a candidate for weakening, because every weakening either is already provided by mathlib
(the core fact) or would require first upstreaming the `universalNormEDS`/`Param` machinery
(out of scope for this single lemma).
Number of weakening opportunities that apply to this lemma independently: 0. Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1 | typeclasses vs bundled hyps? | no | `_ ∈ R⁰` is already the canonical `nonZeroDivisors`-submonoid idiom. |
| 2 | set+closure-pred → bundled substructure? | already done | `R⁰ = nonZeroDivisors R : Submonoid R`. |
| 3 | construction → universal property? | no | finite/elementary; `universalNormEDS` *is* itself the "universal object" device, already idiomatic. |
| 4 | concrete ℤ index → general? | no | `universalNormEDS` is intrinsically ℤ-indexed. |

Modern idiom available: no. The lemma already uses the contemporary mathlib idiom (membership in the
`nonZeroDivisors` submonoid via `mem_nonZeroDivisors_of_ne_zero`). The only "modernisation" would be
to not have the wrapper and apply `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)`
inline — that is the Phase 6 composition point.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (Prop-valued; introduces no defeq or typeclass-search path).

---

### Mathlib search-status: `universalNormEDS_mem_nonZeroDivisors`

[A] Lean-Finder / LeanSearch  "universal normEDS non zero divisor", "nonzero element of a domain is a non-zero-divisor"
        — the *concept* hit is `mem_nonZeroDivisors_of_ne_zero` / `mem_nonZeroDivisors_iff_ne_zero`;
          no hit for `universalNormEDS` (not indexed; not in mathlib).
[B] Loogle   `_ ≠ 0 → _ ∈ nonZeroDivisors _`, `universalNormEDS`
        — for the core type the hits are `mem_nonZeroDivisors_of_ne_zero` and
          `mem_nonZeroDivisors_iff_ne_zero`; zero hits for `universalNormEDS`.
[C] Grep mathlib src (authoritative — actual files read):
        - `grep -rln "universalNormEDS"  .lake/packages/mathlib/Mathlib`  → **NONE** (anywhere).
        - `grep -rln "normEDS"           .lake/packages/mathlib/Mathlib`  → only the 3 standard files
          (`NumberTheory/EllipticDivisibilitySequence.lean`, `DivisionPolynomial/{Basic,Degree}.lean`),
          none of which define `universalNormEDS`, `Param`, or this lemma. The upstream EDS file's
          `normEDS` API differs from the fork's (upstream has `complEDS₂`; the fork has `compl₂EDS`).
        - `mem_nonZeroDivisors_of_ne_zero` → `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:208`
          (`[MonoidWithZero M₀] [NoZeroDivisors M₀]`, premise `x ≠ 0`).
        - `mem_nonZeroDivisors_iff_ne_zero` (`@[simp]`) → same file, line 212 (`[Nontrivial M₀]`):
          over a domain, `x ∈ M₀⁰ ↔ x ≠ 0` — so the wrapper is `universalNormEDS_ne_zero` modulo one
          `simp` lemma.
        - `MvPolynomial … NoZeroDivisors` instance → `Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean:37`.
[D] Name pattern   grep mathlib for `universalNormEDS` / `Param` / `universalNormEDS_mem_nonZeroDivisors`
        — none.

Searched for both:
  - the user's current form (`universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰`): **not in mathlib** —
    `universalNormEDS` and `Param` are fork-local and not upstreamed.
  - the literature-standard / core form ("nonzero ⟹ non-zero-divisor in a domain"): **IS in mathlib**
    as `mem_nonZeroDivisors_of_ne_zero` (and the `@[simp]` iff `mem_nonZeroDivisors_iff_ne_zero`).

Concluded: the exact lemma is "not in mathlib" only because its vocabulary (`universalNormEDS`,
`Param`) is fork-local; the mathematical core is fully available, and the composition is one call.

---

### Call sites — `universalNormEDS_mem_nonZeroDivisors`

Internal use count: 1 (within NagellLutz, excluding the declaring line).
External-to-file callers: 0 (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| EllipticDivisibilitySequence.lean:1345 | `(universalNormEDS_mem_nonZeroDivisors hm) n` — supplies the `mem` (`normEDS … m ∈ R⁰`) argument of `normEDS_mul_complEDS_of_mem` in the universal (`MvPolynomial Param ℤ`) case, inside the proof of `normEDS_mul_complEDS`. |

What the pattern tells you: K = 1 internal use. Its entire purpose is to discharge the `mem`
hypothesis of `normEDS_mul_complEDS_of_mem` when `b,c,d` are the polynomial generators — i.e. to make
the "reduce to the universal domain" trick go through. Genuine internal glue for the fork's own
machinery, with no consumer outside it.

---

### Composition check (Phase 6)

Can `universalNormEDS_mem_nonZeroDivisors` be derived in ≤3 chained calls from mathlib (+ the fork's
own `universalNormEDS_ne_zero`)?

Attempt 1 — the existing proof IS the composition (1 call):
```lean
mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)
```
- Mathlib decl used: `mem_nonZeroDivisors_of_ne_zero` (1×).
- Fork helper used: `universalNormEDS_ne_zero` (the `≠ 0` fact).
- Domain instance (`NoZeroDivisors (MvPolynomial Param ℤ)`) resolved automatically by mathlib.
- Result: succeeds in a single application.

Equivalently, by the `@[simp]` iff: `by simpa using universalNormEDS_ne_zero hn`
(via `mem_nonZeroDivisors_iff_ne_zero`).

Conclusion: **COMPOSABLE** (1 mathlib call). No new mathematical idea. The only reason mathlib alone
doesn't literally close it is that `universalNormEDS`/`Param` live in the fork, not mathlib — so the
lemma is inseparable from the fork's machinery and would travel with it, never stand alone.

---

## Verdict: `universalNormEDS_mem_nonZeroDivisors`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the only mathematical content is "in an integral domain a nonzero
  element is a non-zero-divisor" (folklore; true by definition of an integral domain). The
  `universalNormEDS`/`Param`/`aeval (Param.rec …)` universal-reduction machinery is bespoke to the
  source paper **arXiv 2604.05280** and its Lean formalization — not an independent literature result.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it states — the tightest specialisation of
  the already-maximal mathlib `mem_nonZeroDivisors_of_ne_zero`. No modern-idiom improvement (it already
  uses `nonZeroDivisors`-submonoid membership).
- Mathlib search (Phase 5): the building block `mem_nonZeroDivisors_of_ne_zero`
  (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:208`) is in mathlib — as is the stronger
  `@[simp]` iff `mem_nonZeroDivisors_iff_ne_zero` (line 212) and the domain instance for `MvPolynomial`
  (`Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean:37`). `universalNormEDS`/`Param` are **absent from
  all of mathlib** (`grep -rln "universalNormEDS"` → nothing).
- Composition check (Phase 6): COMPOSABLE in **one** mathlib call — the existing proof is exactly
  `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)`.

**Rationale:**

This lemma carries no mathematical content beyond "a nonzero element of an integral domain is a
non-zero-divisor," which mathlib already provides maximally generally
(`mem_nonZeroDivisors_of_ne_zero`, plus the `@[simp]` iff `mem_nonZeroDivisors_iff_ne_zero`). The
ambient ring `MvPolynomial Param ℤ` is a domain by automatic instance resolution, and the `≠ 0` fact
is the sibling `universalNormEDS_ne_zero`. Everything substantive here is fork-local packaging:
`universalNormEDS` (the normalised EDS over the universal polynomial generators `X B, X C, X D`) and
the `Param` index type are devices from the source paper (arXiv 2604.05280) used to reduce identities
to the universal integral-domain case — and they are **not in mathlib** (the upstream
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` has the `normEDS` API but none of the
`universalNormEDS`/`Param` machinery, and even its `compl`-API names differ). So the lemma cannot be
*independently* mathlib-able: it only makes sense relative to fork definitions that are not (yet)
upstream. It is glue whose sole job (line 1345) is to discharge the `mem` hypothesis of
`normEDS_mul_complEDS_of_mem` in the universal case.

This mirrors the disposition already recorded for the sibling wrapper
`EllSequence.addMulSub_mem_nonZeroDivisors` in this same project (also NO-composable-from-mathlib): a
thin `_mem_nonZeroDivisors` shim over a single mathlib non-zero-divisor primitive applied to
fork-local vocabulary.

**WHY not (refactor-actionable):**
Mathlib has the building block (`mem_nonZeroDivisors_of_ne_zero`); the user's form is a 1-call
composition of it with the fork's own `universalNormEDS_ne_zero`. No new lemma is warranted in mathlib
because (i) the content is `mem_nonZeroDivisors_of_ne_zero`, and (ii) the wrapper references fork-only
vocabulary (`universalNormEDS`, `Param`).

Mathlib building blocks:
- `mem_nonZeroDivisors_of_ne_zero` — `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:208`
- (alt.) `mem_nonZeroDivisors_iff_ne_zero` (`@[simp]`) — same file, line 212
- domain instance: `MvPolynomial …` `NoZeroDivisors` — `Mathlib/Algebra/MvPolynomial/NoZeroDivisors.lean:37`
- (fork-local, would-be-upstreamed-with-the-block) `universalNormEDS_ne_zero` (line 1250)

Composition sketch (the existing proof — 1 call):
```lean
example {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=
  mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hn)
```

Call sites in our project (from Phase 6.0): K = 1 (`EllipticDivisibilitySequence.lean:1345`).

Refactor plan:
- **Mathlib disposition:** none as a standalone lemma. Revisit only as part of upstreaming the entire
  `universalNormEDS`/`Param` "universal reduction" development (the natural PR grain — the arXiv
  2604.05280 formalization), where this would be a trivial 1-line helper.
- **Local option (optional):** the lemma is harmless to keep as a named helper; if desired it could be
  inlined at line 1345 as `mem_nonZeroDivisors_of_ne_zero (universalNormEDS_ne_zero hm)`. Given the one
  call site, keeping the named helper is fine — there is no dedup pressure here (unlike the triplicated
  `addMulSub` shim).

Next action: do NOT open a standalone mathlib PR. Keep as a local helper bundled with the
`universalNormEDS` machinery (or inline at the single call site, line 1345); it would only ever reach
mathlib as part of upstreaming that whole universal-reduction development, which is not yet upstream.

---

## Next step

Do not open a standalone mathlib PR. This is a 1-call composition of mathlib's
`mem_nonZeroDivisors_of_ne_zero` with the fork-local `universalNormEDS_ne_zero`, over fork-local
`universalNormEDS`/`Param` definitions that are not in mathlib. Retain it as a local helper (or inline
at the single call site, line 1345); it would only reach mathlib bundled with the whole
`universalNormEDS` universal-reduction machinery.
