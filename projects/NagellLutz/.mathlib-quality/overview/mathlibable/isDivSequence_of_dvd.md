# Mathlibable assessment — `IsEllSequence.isDivSequence_of_dvd`

**Verdict bucket:** `BORDERLINE-needs-human`

**One-line rationale:** Standard Ward result mathlib lists as an open TODO, but the
project redefines `IsDivSequence` ℤ-indexed (shadowing mathlib's ℕ-indexed def) and it
rests on a large un-upstreamed EDS API tower — both are maintainer calls.

---

### Baseline (Phase 0)

- lake build: not run (task: local build stale) — reasoned from source; the decl is `sorry`-free and elaborates in-project.
- decl `IsEllSequence.isDivSequence_of_dvd`: resolved at
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1450`.
- qualified name VERIFIED from source: the head is `lemma IsEllSequence.isDivSequence_of_dvd : IsDivSequence W := by`
  — the `IsEllSequence.` prefix is written explicitly, so the true qualified name is
  **`IsEllSequence.isDivSequence_of_dvd`** (matches the prompt's guess).
- kind: lemma (theorem). has sorry: no.
- module docstring summary: a **fork/extension** of `Mathlib.NumberTheory.EllipticDivisibilitySequence`
  that proves the EDS divisibility theory mathlib leaves as a TODO; it `_root_`-redefines
  `IsEllSequence`/`IsDivSequence`/`IsEllDivSequence` and builds the `normEDS` + complement/invariant apparatus.

---

### Statement (Phase 1)

> Let `R` be a commutative ring, `W : ℤ → R` an **elliptic sequence** (`IsEllSequence W`). Suppose
> `W 1 ∈ R⁰` and `W 2 ∈ R⁰` (non-zero-divisors) and the base divisibilities `W 1 ∣ W 2`, `W 1 ∣ W 3`,
> `W 2 ∣ W 4` hold. Then `W` is a **divisibility sequence**: `∀ m n : ℤ, m ∣ n → W m ∣ W n`.

This is Ward's classical theorem ("an EDS is a divisibility sequence") in its commutative-ring
generalisation — and note the conclusion uses the project's **ℤ-indexed** `IsDivSequence`.

Hypotheses (from the enclosing `section` + `section Divisibility`, after the `omit ellU one in`):
- `ellW : IsEllSequence W`
- `two : W 2 ∈ R⁰`
- `dvd₁₂ : W 1 ∣ W 2`, `dvd₁₃ : W 1 ∣ W 3`, `dvd₂₄ : W 2 ∣ W 4`
(`one : W 1 ∈ R⁰` is in scope but `omit`-ted here — `W 1 ∈ R⁰` is recovered inside `eq_normEDS_of_dvd`
from `W 1 ∣ W 2 ∈ R⁰`.)

Conclusion (Lean): `IsDivSequence W`, i.e. **the project's** `∀ m n : ℤ, m ∣ n → W m ∣ W n`.

Proof (3 substantive steps):
```lean
obtain ⟨b, c, d, h⟩ := ellW.eq_normEDS_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄  -- W = (W 1 * normEDS b c d ·)
intro m n hmn
rw [congr_fun h m, congr_fun h n]
exact mul_dvd_mul_left (W 1) (IsDivSequence.normEDS m n hmn)
```
Reduce an arbitrary elliptic sequence to a scalar multiple of `normEDS`; `normEDS` is a divisibility
sequence (`IsDivSequence.normEDS`); multiplying by the constant `W 1` preserves divisibility.

---

### Size classification (Phase 2a)

Verdict: **BIG** — a theorem essentially named after a person (Ward's divisibility theorem for EDS) and
the user-facing form of mathlib's Main-results TODO "prove that `normEDS` satisfies `IsEllDivSequence`".
(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `lemma` — n/a (the proof is a genuine 3-step tactic block, not a one-liner def).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form | Notes |
|----|---------|-------|------|---------------|-------|
| 1 | WebSearch (specific) | elliptic sequence is a divisibility sequence Ward proof normalised EDS base cases | yes | "n ∣ m ⟹ aₙ ∣ aₘ"; "W₂,W₃,W₄ with W₂W₃≠0 give an EDS iff W₂∣W₄" | Wikipedia EDS; Ward's induction; the `W₂∣W₄` base condition = `dvd₂₄` |
| 2 | WebSearch (general/strong) | elliptic divisibility sequence strong divisibility gcd Wm Wn Ward memoir | yes | strong-div `gcd(Wₘ,Wₙ)=W_{gcd}`; plain divisibility is the weaker classical fact | Ward, *Memoir on EDS*, Amer. J. Math. 70 (1948) 31–74 — canonical source |
| 3 | WebSearch (aliases/structure) | EDS determined by initial terms W2 W3 W4 … Silverman Stange | yes | EDS determined by W₁..W₄, W₁W₂W₃≠0 | Stange–Silverman; base data = the three `dvd` hypotheses |
| 4 | ChatGPT MCP | self-contained standardness + mathlib-status + ℤ-vs-ℕ query | n/a | — | MCP **down** in this env (Codex exec failed, ×3) — recorded n/a; covered by 1–3 + arXiv (#10) |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/` | n/a | — | dir absent (only `overview/`); module docstring cites Ward directly |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | not an nLab/categorical topic |
| 7 | nCatLab | — | n/a | — | not categorical |
| 8 | Stacks Project | — | n/a | — | arithmetic of integer sequences, not scheme theory |
| 9 | MathOverflow/MSE | (via general WebSearch) | yes | div + strong-div of EDS treated as standard, attributed to Ward | folklore-standard |
| 10 | recent arXiv (≤5 yr) | EDS / elliptic sequences over commutative rings | yes | **arXiv:2604.05280 "On Elliptic Sequences over Commutative Rings" (2026, J. Xu)** | THE source this fork formalises; exact CommRing + non-zero-divisor generality; treats the divisibility theory |

### Literature summary (Phase 3)

Concept: **Ward's theorem that an elliptic (divisibility) sequence is a divisibility sequence**,
`m ∣ n ⟹ Wₘ ∣ Wₙ`. Sources agree it is the foundational arithmetic fact about EDS.
Most general standard form: over a **commutative ring** with the non-vanishing hypotheses replaced by
**non-zero-divisor** (`∈ R⁰`) — exactly arXiv:2604.05280 (2026) and exactly what the project states.
Generality the literature varies on: base ring (ℤ classically → arbitrary CommRing now) and
≠0 vs non-zero-divisor; the project sits at the **most general** end on both. No disagreement.

---

### Generality analysis (Phase 4)

Literature-standard target: elliptic sequence over a CommRing, `W 2 ∈ R⁰`, three base divisibilities ⟹
divisibility sequence.

| # | Param / hyp | Current Lean form | Literature-standard | Weaker exists? | Reason |
|---|-------------|-------------------|---------------------|----------------|--------|
| 1 | `[CommRing R]` | commutative ring | CommRing (modern) / ℤ (classical) | NO | already the general modern setting; recursion needs comm. mult |
| 2 | `ellW : IsEllSequence W` | elliptic relation | same | NO | defining hypothesis |
| 3 | `two : W 2 ∈ R⁰` | non-zero-divisor | `≠0` over a domain; `∈ R⁰` over CommRing | NO | `∈ R⁰` IS the right CommRing weakening of `≠0`; maximal |
| 4 | `dvd₁₂,dvd₁₃,dvd₂₄` | three base divisibilities | the `(W₂,W₃,W₄)` base data | NO | minimal base cases the literature uses; removing any breaks the `normEDS` reduction |

**Generality verdict (4b): MAXIMALLY GENERAL** (0 weakening opportunities) **on the hypotheses**.
The only *narrower* sibling is the `normEDS`-specialised `isEllDivSequence_normEDS` — this lemma is
strictly more general and implies it.

**Modern-idiom (4c):** no topology/filter/universal-property/categorification move applies (it is a pure
arithmetic divisibility statement using mathlib's own predicates and `nonZeroDivisors`). **EXCEPT** the
conclusion's predicate: see the ℤ-vs-ℕ note below — the project uses a ℤ-indexed `IsDivSequence`, which
is arguably the *more uniform* idiom (matching the ℤ-indexed `IsEllSequence`) but **diverges from
mathlib's existing ℕ-indexed `IsDivSequence`**. That divergence is the heart of the BORDERLINE verdict.

---

### Diamond / defeq risk (Phase 4.5)

n/a — kind is `lemma`. (The *definition* `IsDivSequence` it concludes in is redefined by the project, but
that def is assessed separately; here the risk is the **name-collision / API-divergence** captured in
Phase 5 + the verdict, not a defeq/diamond issue.)

---

### Mathlib search-status (Phase 5)

[A] Lean-Finder / [B] Loogle / [C] LeanSearch: dedicated index tools not available in this env — n/a;
   substituted by an **authoritative grep of the pinned mathlib source** (stronger than the index).
[D] Grep mathlib src — `IsDivSequence`, `normEDS`, `isEllDivSequence_normEDS`, `IsEllDivSequence`:
   `IsDivSequence` occurs in **exactly one** mathlib file,
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (pin `09b373db`, dated **2026-06-21** —
   essentially today's mathlib, NOT a stale `d90090f`). That file:
     • defines `IsDivSequence W := ∀ m n : ℕ, m ∣ n → W m ∣ W n`  **(indices in ℕ)** — line 87–88,
     • proves only the trivial `id`/`smul` lemmas (stops at line 116),
     • lists as **open TODOs (lines 44–45)**: "prove that `normEDS` satisfies `IsEllDivSequence`" and
       "prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`".
   `normEDS` lives in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean`
   but **no divisibility lemma** is attached to it anywhere in mathlib.
[E] Name pattern — `isDivSequence_of_dvd`, `eq_normEDS_of_dvd`: **no hit** in mathlib (these names live
   only in the project forks).

Searched BOTH forms:
   • the user's ℤ-indexed form (`∀ m n : ℤ, …`): **not in mathlib**;
   • mathlib's own ℕ-indexed `IsDivSequence` for `normEDS` / a general EDS: **not proved — open TODO**.
Live cross-check: the public mathlib4 docs page for the module (newer than the local pin) still shows the
TODO and no proof.

**Conclusion: not in mathlib** (authoritative source grep + the narrower mathlib-form both exhausted; it
is an explicitly-flagged gap).

**Critical mismatch found:** mathlib's `IsDivSequence` is **ℕ-indexed**; the project has `_root_`-
redefined it **ℤ-indexed** (`projects/.../EllipticDivisibilitySequence.lean:602` —
`def IsDivSequence : Prop := ∀ m n : ℤ, m ∣ n → W m ∣ W n`), shadowing the mathlib def. (Same for the
project's `_root_.IsEllSequence` at line 135.) So the lemma's conclusion is **not the same `Prop`** as
mathlib's `IsDivSequence W` on a bare `W`.

---

### Call sites (Phase 6.0)

Internal use count (NagellLutz, excl. declaring line): **1**.

| Caller file:line | Usage |
|------------------|-------|
| `…/NagellLutz/…/EllipticDivisibilitySequence.lean:1458` | `⟨ellW, ellW.isDivSequence_of_dvd two dvd₁₂ dvd₁₃ dvd₂₄⟩` (inside `isEllDivSequence_of_dvd`) |

Inline-derivation / duplication grep: the **entire development is duplicated in HasseWeil**
(`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean` — `IsDivSequence.normEDS` at
:1018, `IsEllDivSequence.normEDS` at :1024). The companion `IsDivSequence.normEDS` is consumed at :1454.
So the divisibility theory IS used; `isDivSequence_of_dvd` is the general wrapper and
`isEllDivSequence_of_dvd` (its single caller) the `IsEllDivSequence` packaging. The cross-project
duplication is independent evidence that this theory "wants" to live upstream so both forks can drop it.

### Composition check (Phase 6a)

Can it be derived from **mathlib** in ≤3 chained calls?
- Step 1 needs `IsEllSequence.eq_normEDS_of_dvd` — **not in mathlib** (project-local; = mathlib TODO #2).
- Step 3 needs `IsDivSequence.normEDS` (`normEDS` is a div. sequence) — **not in mathlib** (= TODO #1),
  itself resting on `normEDS_mul_complEDS` ← `mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` and the
  universal-polynomial complement machinery (~hundreds of lines).
- `mul_dvd_mul_left` is in mathlib but is only the trivial last step.

**Conclusion: NOT-COMPOSABLE** from mathlib — the substance is an un-upstreamed EDS API tower.

---

## Verdict: `IsEllSequence.isDivSequence_of_dvd`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature (Phase 3): standard/classical — Ward 1948; CommRing form is current (arXiv:2604.05280, 2026).
- Generality (Phase 4): hypotheses MAXIMALLY GENERAL; but the *conclusion predicate* `IsDivSequence` is a
  project redefinition (ℤ-indexed) that diverges from mathlib's (ℕ-indexed).
- Mathlib search (Phase 5): not in mathlib — the exact result is an explicit open TODO; and the project's
  `IsDivSequence`/`IsEllSequence` shadow mathlib's defs with incompatible signatures.
- Composition (Phase 6): NOT-COMPOSABLE — rests on a large un-upstreamed apparatus.

**Rationale.**

Mathematically this is squarely in scope and genuinely missing from mathlib: it is exactly mathlib's
own TODO ("`normEDS` satisfies `IsEllDivSequence`") in a *more general* form (an arbitrary elliptic
sequence, not just `normEDS`), stated at the maximal CommRing + non-zero-divisor generality the modern
literature uses. If the only question were "is the theorem worth having", the answer would be YES.

But two facts make the *upstreaming decision* a human/maintainer call rather than a mechanical YES:

1. **The project redefines mathlib's API.** It `_root_`-shadows `IsDivSequence` (and `IsEllSequence`)
   with **ℤ-indexed** definitions (`∀ m n : ℤ, …`), whereas mathlib's `IsDivSequence` is **ℕ-indexed**
   (`∀ m n : ℕ, …`). For an actual elliptic sequence the two are mathematically equivalent — `W 0 = 0`
   and `W(−k) = −W(k)`, and `a ∣ b ↔ −a ∣ b ↔ a ∣ −b`, so the ℕ-form implies the ℤ-form and conversely
   — so neither is "more true". The ℤ-indexed form is arguably the *more uniform* library choice (it
   matches the already-ℤ-indexed `IsEllSequence`), and may well be an improvement mathlib should adopt.
   But changing `IsDivSequence` to ℤ-indexed is a **definitional change to mathlib's existing EDS API**
   (it would touch `isEllDivSequence_id`, the `smul` lemmas, and the stated TODOs), and shipping the
   lemma against mathlib's *current* ℕ-indexed def instead is a different (and slightly less uniform)
   statement. Which way to go is a mathlib-maintainer taste/policy decision the skill cannot make alone.

2. **It is the apex of a large un-upstreamed tower.** The proof depends on `eq_normEDS_of_dvd`
   (= TODO #2) and `IsDivSequence.normEDS` (= TODO #1), which in turn rest on the whole `EllSequence`
   complement / universal-`MvPolynomial` apparatus. Upstreaming this one lemma in isolation is
   impossible; it must come as a **coordinated multi-file PR that closes both TODOs**, whose grain,
   sequencing, and naming are human decisions. The fact that the same tower is **duplicated in
   NagellLutz and HasseWeil** means de-duplication must also be settled first.

So: clear YES on mathematical merit, but the indexing-convention divergence from mathlib's existing
`IsDivSequence` plus the coordinated-upstreaming scope make it BORDERLINE pending the questions below.

**Numbered questions for the human:**

1. Should mathlib's `IsDivSequence` be changed to the **ℤ-indexed** form (`∀ m n : ℤ, m ∣ n → W m ∣ W n`)
   to match the ℤ-indexed `IsEllSequence` — or should this lemma be **restated against mathlib's existing
   ℕ-indexed** `IsDivSequence`? (Determines whether this is a def-change PR or a re-statement.)
2. Is there appetite to upstream the **whole `normEDS`-is-an-EDS development at once** (closing the two
   `EllipticDivisibilitySequence.lean` TODOs, lines 44–45), i.e. `IsEllSequence.normEDS`,
   `IsDivSequence.normEDS`/`IsEllDivSequence.normEDS`, `eq_normEDS_of_dvd`/`eq_normEDS`, this lemma, plus
   the supporting `EllSequence`/complement substrate — as a coordinated PR series?
3. Before any PR, should the **duplicated NagellLutz vs HasseWeil** copies be merged into one canonical
   source (e.g. a `Common/` module) so the upstreamed version cleanly replaces both?
4. Has the upstream EDS author (recent committers to `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
   / the `DivisionPolynomial/` files, and the arXiv:2604.05280 author) already started this — to avoid a
   collision? (The result is on-record as a mathlib TODO, so an effort may be in flight.)

**Next action:** answer Q1–Q4; then either (YES-but-generalise/restate path) re-aim the lemma at the
chosen mathlib `IsDivSequence` convention and run `/generalise` + `/cleanup`, or (coordinated-upstream
path) scope the multi-file PR closing the two TODOs after de-duplicating the two forks. Re-run
`/mathlibable` once the indexing convention is fixed to convert this to a YES-* verdict.
