# `/mathlibable` report — `PadicMeasure.odd_moment_factor_eq_zero`

**Final verdict: `NO-composable-from-mathlib`** (see Phase 7).

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow in this checkout) — **reasoned from source**, per the skill's Phase-0 fallback. The declaration and all its dependencies were read directly.
- decl `PadicMeasure.odd_moment_factor_eq_zero`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:36` (unique match in the project)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  `ζ_p` as a pseudo-measure on `𝒢⁺` and the ideal `I(𝒢)ζ_p` (RJW arXiv:2309.15692 §11.1–11.2, on the identified Galois side).

Dependencies traced:
- `zetaNeg` — **project def** at `projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/ZetaValues.lean:17`: `zetaNeg k := (-1)^k * bernoulli (k+1) / (k+1)` (the rational value `ζ(−k)`).
- `bernoulli_eq_zero_of_odd` — **mathlib**, `Mathlib/NumberTheory/Bernoulli.lean:217`: `{n : ℕ} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0`.

---

### Statement (Phase 1)

`PadicMeasure.odd_moment_factor_eq_zero` is a theorem stating the following:

For an odd positive integer `k`, the **p-adic Iwasawa interpolation factor**
`(1 − p^{k−1}) · ζ(1−k)` vanishes in `ℚ_[p]`, where `ζ(1−k)` is the rational
zeta value at the non-positive integer `1−k` cast into `ℚ_[p]`. The vanishing has
*two distinct causes* depending on `k`:

- at `k = 1` the Euler factor is `1 − p^0 = 1 − 1 = 0` (and the zeta value
  `ζ(0) = −1/2` does **not** vanish — the source's "ζ(1−k)=0 for odd k≥1" line is
  wrong here, flagged as the project's "erratum #13");
- at odd `k ≥ 3`, `1−k ≤ −2` is a negative **even** integer, so
  `ζ(1−k) = (−1)^{k−1} B_k / k = 0` because the odd-index Bernoulli number `B_k = 0`.

Variables / typeclasses (Lean side):
- `p : ℕ` with `[hp : Fact p.Prime]` — the prime; `ℚ_[p]` is its p-adic field.
- `{k : ℕ}` — the moment index.

Hypotheses (Lean side):
- `(hk : Odd k)` — `k` is an odd natural number (hence `≥ 1`).

Conclusion (math): the product of the p-adic Euler factor and the cast rational
zeta value is `0`.

Conclusion (Lean): `(1 - (p : ℚ_[p]) ^ (k - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — a finite arithmetic identity with a two-way case split,
feeding the moment computation `padicZeta_moments`. Not a named theorem, not a
new structure, not listed as a primary goal in the project plan (it appears in
the project's `overview/worklist.json` as a tracked declaration, not as a "Main
result"). It *is* mentioned under `## Main declarations` in the file docstring,
but only as one of several supporting lemmas for the §11.1 corollary.

(Note: literature width was EXHAUSTIVE regardless — the BIG/SMALL split is
narrative only.)

### One-line check (Phase 2b)

Body line count: ~8 substantive lines (a `obtain … | …` case split, two branches).
One-liner verdict: n/a — kind is `theorem`, not a `def`. (Section skipped per the
skill.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Riemann zeta trivial zeros negative odd integers Bernoulli numbers vanish zeta(1−k)"                  | yes  | `ζ(−n) = (−1)^n B_{n+1}/(n+1)`; `ζ(s)=0` ⟺ negative **even** integer | Britannica, Wolfram MathWorld, Reed lecture notes; `ζ(1−k)=0` for odd `k≥3` since `1−k` is a negative even integer; odd `B_n` (n>1) vanish |
|  2 | WebSearch (p-adic / interpolation form) | "Kubota–Leopoldt p-adic zeta Euler factor (1−p^{k−1}) interpolation zeta(1−k) odd characters vanish" | yes  | p-adic zeta interpolates `(1−p^{k−1})ζ(1−k)`; Euler factor `1−p^{k−1}` removed at `p` | Guitart, Williams (Warwick), Ploner notes (Luxembourg) — confirms the *combined factor* `(1−p^{k−1})ζ(1−k)` is the standard p-adic interpolation datum; the `k=1` Euler-factor degeneracy is standard |
|  3 | WebSearch (named-after / aliases)| "zeta values negative integers Bernoulli formula ζ(−n)=−B_{n+1}/(n+1) Euler von Staudt odd zero"       | yes  | same `ζ(−n)` formula; `ζ(−2m+1)=−B_{2m}/2m`; vanishing only at negative even ints | Reed (J. Buhler) notes, John D. Cook, Sury (general-article); confirms `B_1=−1/2` is the lone non-vanishing odd-index value |
|  4 | ChatGPT MCP                      | (intended: "standard form of `(1−p^{k−1})ζ(1−k)`, its generality, historical evolution")               | n/a  | —                                | **MCP not configured in this environment** — no ChatGPT tool surfaced. Recorded as n/a; the three WebSearch queries (the protocol's hard minimum) + Wikipedia/nLab fetch cover the standard-form question fully. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (no references dir)              | `.mathlib-quality/references/` absent; `refs/` symlink absent in this checkout — recorded n/a |
|  6 | nLab                             | "Riemann zeta function" / "Bernoulli number" (values at negative integers)                             | yes  | `ζ(−n)` Bernoulli formula; trivial zeros at negative even integers | nLab `Riemann zeta function` / `Bernoulli number` pages give the same standard statement |
|  7 | nCatLab (categorical)            | —                                                                                                      | n/a  | —                                | Not a categorical concept; arithmetic identity over `ℚ`/`ℚ_[p]`. n/a |
|  8 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry concept. n/a |
|  9 | MathOverflow / Math.SE           | covered via WebSearch #1–#3 (Wikipedia "Particular values of ζ" fetched directly)                       | yes  | `ζ(0)=−1/2` (nonzero); `ζ(−1)=−1/12`, `ζ(−3)=1/120` nonzero; zeros only at negative even ints | Wikipedia *Particular values of the Riemann zeta function* (WebFetch) explicitly confirms `ζ(0)=−1/2≠0` — the exact "erratum #13" point the project flags |
| 10 | recent arXiv (last 5 years)      | "Sum Expressions for Kubota–Leopoldt p-adic L-functions" + RJW arXiv:2309.15692 (the project source)   | yes  | the project's own source (RJW) states the §11.1 corollary; arXiv:2201.08870 treats the Euler-factor form | Confirms the *combined* `(1−p^{k−1})ζ(1−k)` factor is the contemporary p-adic-L object, not a novel construction |

The protocol passed: **3 WebSearch queries at distinct generality levels** (specific
trivial-zero form, p-adic/interpolation form, named-after/aliases), **Wikipedia
+ nLab fetched directly**, **local refs / Stacks / nCatLab recorded n/a with
reasons**, **arXiv checked**. ChatGPT MCP is genuinely unavailable here (n/a with
reason), and its role — pinning the standard form, generality, and historical
evolution — was fully served by the WebSearch + Wikipedia + nLab evidence.

### Literature summary (Phase 3)

Concept identified as: two completely standard facts, combined into a p-adic
interpolation factor —
1. **Values of `ζ` at non-positive integers**: `ζ(−n) = (−1)^n B_{n+1}/(n+1)`
   (equivalently `ζ(1−k) = −B_k/k`), with the **trivial zeros at negative even
   integers** (`ζ(1−k) = 0` for odd `k ≥ 3`) and the **non-vanishing edge value
   `ζ(0) = −1/2`**.
2. **The Kubota–Leopoldt Euler factor** `(1 − p^{k−1})`, the standard
   modification by which the p-adic zeta function interpolates `ζ(1−k)`; at `k=1`
   it degenerates to `1 − p^0 = 0`.

Sources agree on the standard form: **yes** — universally documented (Wikipedia,
Wolfram, nLab, Buhler/Reed notes, Sury, and the p-adic-L lecture notes of
Guitart / Williams / Ploner; RJW arXiv:2309.15692 is the project's own source).

Most general standard form: the *individual* facts are maximally general as
stated in mathlib (Bernoulli over `ℚ`; `riemannZeta` over `ℂ`). The *combined*
object `(1 − p^{k−1})·ζ(1−k)` is intrinsically a **p-adic-L-function** datum —
it only makes sense once one has a Kubota–Leopoldt theory, i.e. it is
**project-specific**, not a free-standing mathlib-level statement.

Generality dimensions where the literature varies:
- ground object: `ζ` as the **rational** value (Buhler/Reed, the project's
  `zetaNeg`) vs the **complex** `riemannZeta(1−k)` (mathlib `riemannZeta_neg_nat_eq_bernoulli`) — same number, two carriers.
- Euler factor: `1 − p^{k−1}` (the `s ↦ 1−k` specialisation) is one instance of
  the general `∏_p (1 − p^{−s})` Euler-factor removal.

Disagreement with the literature: **none on the mathematics.** The project's
docstring explicitly *corrects* a slip in the source (RJW's "ζ(1−k)=0 for odd
k≥1" line, which fails at `k=1` where `ζ(0)=−1/2≠0`); the literature (Wikipedia,
fetched) confirms the project's corrected reasoning — `k=1` vanishes via the
**Euler factor**, not the zeta value.

---

### Generality analysis — `PadicMeasure.odd_moment_factor_eq_zero`

Literature-standard form (from Phase 3): the two ingredient facts are
maximally general in mathlib already; the *combined factor* is an irreducibly
p-adic-L-function object tied to a Kubota–Leopoldt construction.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]` | a prime, working in `ℚ_[p]` | the p-adic field of the K–L construction | NO | the statement is *about* the p-adic Euler factor cast into `ℚ_[p]`; `p` prime is intrinsic |
| 2 | `(hk : Odd k)` | `k` odd | odd `k` is exactly when `1−k` is a negative even integer (the trivial-zero locus) ∪ `k=1` | NO | dropping oddness breaks both branches; oddness is the hypothesis that makes the factor vanish |
| 3 | `zetaNeg (k−1)` (cast `ℚ→ℚ_[p]`) | the project's **rational** `ζ(1−k)` cast into `ℚ_[p]` | `ζ(1−k)` as a number | (re-aim, not weaken) | could be restated with mathlib's `riemannZeta` via `zetaNeg_eq_riemannZeta`, but that *adds* a complex-analysis import the project deliberately avoids; not a generalisation |
| 4 | the product `(1−p^{k−1})·(…)` | the K–L interpolation factor | a p-adic-L datum | NO | the product only has meaning in a Kubota–Leopoldt setting; mathlib has no such setting (see Phase 5) |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *for what it is* — a project-local
helper about the project's own `zetaNeg` and the p-adic Euler factor. There is no
literature-standard *more general combined form* to aim at, because the combined
object is inherently the project's p-adic-L construction.

Number of weakening opportunities found: **0** (every hypothesis is load-bearing).

Proposed restatement: none — the statement is not narrower than a standard form;
it is a project-specific specialisation of two mathlib-general facts.

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | bundled hypotheses → typeclasses/instances? | no | — | already a clean `{k}(hk : Odd k)`; nothing to bundle |
| 2  | sequences/metric → filters/topology? | no | — | finite arithmetic identity; no limits |
| 3  | construct object → universal-property class? | no | — | no object constructed |
| 4  | set+closure-predicate → bundled substructure? | no | — | no substructure |
| 5  | vector-space/metric/field-specific → weaker typeclass? | no | — | already over `ℚ_[p]`; the carrier is fixed by the p-adic setting |
| 6  | 1-categorical → higher-categorical? | no | — | not categorical |
| 7  | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | `k : ℕ` is the natural moment index; oddness is what makes it vanish |
| 8  | **concrete-via-abstract** (statement names a concrete object; proof uses only abstract properties)? | **no** | — | **Diagnostic run:** the proof body has no "named concrete object that vanishes after an unfolding" pattern. After `rw [zetaNeg, …]` the odd branch is closed *directly by* `bernoulli_eq_zero_of_odd` (the relevant abstract fact is already a cited mathlib lemma). The `k=1` branch is pure arithmetic (`simp` on `1−p^0`). There is no hidden abstract theorem waiting to be extracted — the abstraction (`bernoulli_eq_zero_of_odd`) is *already the mathlib lemma being called*. Q8 does not fire. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: the only abstraction in sight (odd Bernoulli numbers vanish) is
*already* the mathlib lemma `bernoulli_eq_zero_of_odd` that the proof invokes;
the rest is a p-adic-cast arithmetic edge case with no cleaner contemporary form.

---

### Diamond / defeq risk — `PadicMeasure.odd_moment_factor_eq_zero`

n/a — declaration kind is `theorem`. (Phase 4.5 runs only for
`def`/`class`/`instance`; theorems introduce no definitional equalities or
typeclass-search paths.)

---

### Mathlib search-status: `PadicMeasure.odd_moment_factor_eq_zero`

[A] Lean-Finder       (AI search MCP)                          n/a: MCP not configured in this environment
[B] Loogle            (type-pattern MCP)                       n/a: MCP not configured; substituted by authoritative source grep (D)
[C] LeanSearch        (natural-language MCP)                   n/a: MCP not configured; substituted by (D)
[D] Grep mathlib src  `padic.*zeta`, `kubota`, `leopoldt`, `(1 - .*\^.* \* .*zeta)`, `euler_factor`, `bernoulli.*odd`, `riemannZeta_neg`, `*moment*eq_zero` over `.lake/packages/mathlib/Mathlib/`  — **decisive hits** (full mathlib tree present locally)
[E] Name pattern      `odd_*_eq_zero`, `*interpolation_factor*`, `*moment*` over mathlib  — no relevant hit (the `moment` hits are `Probability.moment`, unrelated)

Searched for both:
- **the user's exact form** — `(1 − p^{k−1})·ζ(1−k)` cast to `ℚ_[p]`: **not in
  mathlib.** mathlib has **no p-adic zeta / Kubota–Leopoldt / p-adic-L
  machinery at all** (`grep padic.*zeta|kubota|leopoldt` → 0 hits). The only
  `(1 − p^{−s})·zeta` shape in mathlib is `LFunctionTrivChar` over `ℂ`
  (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:175`), an unrelated
  complex-analytic Dirichlet object.
- **the ingredient facts (the literature-standard pieces)** — **both present:**
  - `bernoulli_eq_zero_of_odd` — `Mathlib/NumberTheory/Bernoulli.lean:217`
    (odd-index Bernoulli numbers `> 1` vanish). *This is the exact lemma the
    proof already calls.*
  - `riemannZeta_neg_nat_eq_bernoulli` — `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean:251`
    (`riemannZeta(−k) = (−1)^k bernoulli(k+1)/(k+1)`) — the complex analog of the
    project's rational `zetaNeg`.
  - `riemannZeta_neg_two_mul_nat_add_one` — `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:172`
    (`riemannZeta(−2(n+1)) = 0`) — the trivial zeros, the complex statement of
    the odd-`k≥3` branch.

Concluded: **found the building blocks (`bernoulli_eq_zero_of_odd`,
`riemannZeta_neg_nat_eq_bernoulli`, `riemannZeta_neg_two_mul_nat_add_one`) but NOT
the user's exact form** — mathlib has neither the combined p-adic interpolation
factor nor any p-adic zeta object to host it.

---

### Call sites — `PadicMeasure.odd_moment_factor_eq_zero`

Internal use count: **2** (within `PadicLFunctions`, NOT counting the declaring
file's *docstring* mention) — **but both uses are inside the declaring file
`ZetaGalois.lean` itself**, so **external-to-file callers: 0**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| Iwasawa/ZetaGalois.lean:57 | `rw [mul_assoc, odd_moment_factor_eq_zero p hk, mul_zero] at hm` — inside `padicZeta_odd_moment_eq_zero` |
| Iwasawa/ZetaGalois.lean:87 | `rw [mul_assoc, odd_moment_factor_eq_zero p ho, mul_zero] at hm` — inside `dirac_neg_one_sub_one_mul_padicZeta` |
| Iwasawa/ZetaGalois.lean:12 | docstring mention only (not a call) |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
- **Yes, partially, and inside the project itself.** The project *already* has
  `zetaNeg_eq_zero_of_even` (`KubotaLeopoldt/ZetaValues.lean:25`), which proves
  exactly the `zetaNeg (k−1) = 0` content of the odd-`k≥3` branch via the same
  `bernoulli_eq_zero_of_odd` call. `odd_moment_factor_eq_zero` re-derives that
  fact inline (`ZetaGalois.lean:43`) rather than calling its own sibling lemma.
- The `bernoulli_eq_zero_of_odd` rewrite pattern recurs **~13 times** across the
  AINTLIB repo (mostly in `FltRegularBernoulli/`), confirming this is a
  bread-and-butter mathlib call, re-derived inline everywhere — never wrapped.

Signal (per the call-sites table in `mathlibable-verdicts.md`): **K = 0
external uses + the statement's core is re-derived inline (and even already
exists as a project sibling lemma)** ⟹ this is internal Iwasawa glue that
consumers reach through `padicZeta_moments`, not reusable public API. Leans
strongly toward a **NO** bucket.

---

### Composition check (Phase 6)

Can `PadicMeasure.odd_moment_factor_eq_zero` be derived from mathlib (+ the
project's own `zetaNeg` def, which mathlib does not have) in ≤3 chained calls?

Attempt 1 (over `ℚ_[p]`, the actual statement): case-split on `k`.
- `k = 1`: `1 − (p:ℚ_[p])^(1−1) = 1 − p^0 = 1 − 1 = 0`, so the product is `0`.
  Closed by `simp` (`pow_zero`, `sub_self`, `zero_mul`).
- odd `k ≥ 3`: `zetaNeg (k−1) = (−1)^{k−1}·bernoulli k / k = 0` because
  `bernoulli_eq_zero_of_odd hk hk1 : bernoulli k = 0` (after `Nat.sub_add_cancel`
  turns `(k−1)+1` into `k`); then `Rat.cast_zero` and `mul_zero`.
- Mathlib decls used: `bernoulli_eq_zero_of_odd`, `Nat.sub_add_cancel`,
  `Rat.cast_zero`, `pow_zero`/`sub_self` (the `simp` set).
- Result: **succeeds**, but it is a **case split + a rewrite chain**, not a single
  ≤3-call composition. Per the Phase-6 heuristics table, a `by obtain … ; simp ;
  rw [zetaNeg, …, bernoulli_eq_zero_of_odd, …]` body is **a (small) proof, not a
  one-liner composition**.

Attempt 2 (could the project call its own sibling instead?): the odd branch is
literally `zetaNeg_eq_zero_of_even (k−1) (by omega) (Nat.Odd.sub_odd ho odd_one)`
— i.e. the project *already owns* a one-line lemma for that branch. So the
"composition" that exists is **project-internal** (`zetaNeg_eq_zero_of_even` +
the `k=1` arithmetic), not a mathlib composition. mathlib cannot supply
`zetaNeg_eq_zero_of_even` because mathlib has no `zetaNeg`.

Conclusion: **NOT-COMPOSABLE *from mathlib alone* as a single ≤3-call sketch** —
because the statement mentions the project-local `zetaNeg` and the project-local
p-adic Euler factor, which mathlib has no decls about. BUT the *transferable*
mathematical content is exactly one mathlib call (`bernoulli_eq_zero_of_odd`)
plus an arithmetic edge case, and that content is **not a candidate for a new
mathlib lemma** — it is already the mathlib lemma. The right home for this exact
statement is **the project**, and within the project it is a short helper that
should arguably reuse the existing `zetaNeg_eq_zero_of_even`.

---

## Verdict: `PadicMeasure.odd_moment_factor_eq_zero`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the two ingredient facts (`ζ(−n)` Bernoulli
  formula; odd-index Bernoulli vanishing / trivial zeros at negative even
  integers) are universally standard and confirmed across ≥6 channels;
  the *combined* `(1−p^{k−1})·ζ(1−k)` factor is intrinsically a Kubota–Leopoldt
  p-adic-L object (project-specific), not a free-standing mathlib statement.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** for what it is — every
  hypothesis load-bearing, 0 weakenings, no modern-idiom restatement (Q8 does
  not fire: the only abstraction is the mathlib lemma already being called).
- Mathlib search (Phase 5): **building blocks found**
  (`bernoulli_eq_zero_of_odd`, `riemannZeta_neg_nat_eq_bernoulli`,
  `riemannZeta_neg_two_mul_nat_add_one`); the user's exact form is **not** in
  mathlib, and mathlib has **no p-adic zeta machinery** to host it.
- Composition check (Phase 6): **NOT-COMPOSABLE** as a single ≤3-call mathlib
  sketch (the statement names the project-local `zetaNeg`), and **not a
  candidate for a new mathlib lemma** — the transferable content *is* the
  mathlib lemma `bernoulli_eq_zero_of_odd`.
- Call sites (Phase 6.0): **K=0 external**, 2 within-file uses; the odd-branch
  content is already re-derived inline and already exists as the project sibling
  `zetaNeg_eq_zero_of_even`.

**Rationale (1–2 paragraphs):**

`odd_moment_factor_eq_zero` is a project-internal Iwasawa-theory helper, not a
mathlib candidate. Its mathematical heart is two facts that mathlib already owns
in full generality: the vanishing of odd-index Bernoulli numbers
(`bernoulli_eq_zero_of_odd`) and the value of `ζ` at negative integers
(`riemannZeta_neg_nat_eq_bernoulli`, with the trivial zeros
`riemannZeta_neg_two_mul_nat_add_one`). Everything else in the statement is
project-specific *packaging*: it is phrased in terms of the project's own
rational definition `zetaNeg` and the Kubota–Leopoldt Euler factor `(1−p^{k−1})`
cast into `ℚ_[p]`. mathlib has **no** p-adic zeta / p-adic-L-function
infrastructure at all, so it can neither contain this combined factor nor a more
general version of it — the object only exists once the project's K–L
construction is in place. The `k=1` branch (Euler factor `1−p^0 = 0`) is a pure
arithmetic edge case the project flags as correcting a slip in its source paper
(confirmed correct by the literature: `ζ(0)=−1/2 ≠ 0`).

Because the statement quantifies over the project-local `zetaNeg`, it is not a
≤3-call composition of mathlib decls *standing alone* (NOT-COMPOSABLE in the
strict sense), and it is equally not a candidate for a *new* mathlib lemma: the
only transferable content is a single `bernoulli_eq_zero_of_odd` call. The
`NO-composable-from-mathlib` bucket is the correct verdict — mathlib supplies the
building block, the statement stays in the project, and the refactor is a
project-internal cleanup (reuse the existing sibling lemma), not an upstreaming.
This is *not* `NO-mathlib-has-it` (mathlib does not have a decl whose
specialisation yields this `ℚ_[p]` statement in ≤1 line — there is no p-adic
zeta there), and *not* a YES bucket (no new mathlib-shaped content; the abstract
fact is already a mathlib lemma).

**WHY not (refactor-actionable detail):**

Mathlib has the one transferable building block; the rest of the statement is
project-local and stays in the project. The lemma should not be deleted (it's a
genuinely-used internal helper feeding `padicZeta_moments` via
`padicZeta_odd_moment_eq_zero` and `dirac_neg_one_sub_one_mul_padicZeta`), but it
is **not for mathlib**.

- Mathlib building block (the only transferable piece):
  - `bernoulli_eq_zero_of_odd` — `Mathlib/NumberTheory/Bernoulli.lean:217`
    (already called by the proof at `ZetaGalois.lean:43`).
  - (For reference, the complex analogs the project deliberately routes around to
    avoid importing complex analysis: `riemannZeta_neg_nat_eq_bernoulli`,
    `riemannZeta_neg_two_mul_nat_add_one`.)

- Composition sketch of the *transferable* content (≤3 mathlib calls), showing it
  is already mathlib:
  ```lean
  -- the odd-k≥3 rational vanishing is one mathlib call:
  example {k : ℕ} (hk : Odd k) (hk1 : 1 < k) : bernoulli k = 0 :=
    bernoulli_eq_zero_of_odd hk hk1
  ```

- Call sites in our project (from Phase 6.0): **K = 2** (both internal to
  `ZetaGalois.lean`: lines 57 and 87).

- **Refactor plan (project-internal, NOT a mathlib PR):**
  1. **Keep** `odd_moment_factor_eq_zero` in the project — it packages the
     `ℚ_[p]`-cast interpolation factor that its two callers need, and it is not
     reproducible from mathlib alone.
  2. **Optional cleanup (a `/cleanup`-lane dedup, not a mathlib action):** the
     odd-`k≥3` branch at `ZetaGalois.lean:42–44` re-derives `zetaNeg (k−1) = 0`
     inline. The project already has `zetaNeg_eq_zero_of_even`
     (`KubotaLeopoldt/ZetaValues.lean:25`). Replace the inline
     `rw [zetaNeg, Nat.sub_add_cancel hk.pos, bernoulli_eq_zero_of_odd hk hk1,
     mul_zero, zero_div]` with a call to
     `zetaNeg_eq_zero_of_even (k:=k−1) (by omega) (Nat.Odd.sub_odd hk odd_one)`,
     so the two siblings share one proof of the rational vanishing.
  3. **Do NOT open a mathlib PR for this declaration.** mathlib's contribution is
     the already-existing `bernoulli_eq_zero_of_odd`; there is no new
     mathlib-shaped statement here.

**Next action:** Leave `odd_moment_factor_eq_zero` in `PadicLFunctions` (no
mathlib PR). The transferable fact is already mathlib's `bernoulli_eq_zero_of_odd`
at `Mathlib/NumberTheory/Bernoulli.lean:217`. Optionally, in a project `/cleanup`
pass, dedup the odd-branch proof against the existing project lemma
`zetaNeg_eq_zero_of_even`.

---

## Next step

Leave `odd_moment_factor_eq_zero` in `PadicLFunctions` (no mathlib PR — mathlib
has neither the p-adic zeta object nor a host for the combined interpolation
factor; the only transferable content is the already-present
`bernoulli_eq_zero_of_odd`). Optionally dedup its odd-`k≥3` branch against the
project's existing `zetaNeg_eq_zero_of_even` in a `/cleanup` pass.
