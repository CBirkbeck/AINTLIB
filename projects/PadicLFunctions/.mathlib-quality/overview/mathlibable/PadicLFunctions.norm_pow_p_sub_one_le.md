# `/mathlibable` report — `PadicLFunctions.norm_pow_p_sub_one_le`

**Final verdict: `BORDERLINE-needs-human`** (the result is genuinely missing from
mathlib and not a cheap composition, but whether this single contraction-step
estimate ships on its own versus only as part of the whole p-adic-log-on-local-fields
framework is a judgment call for the maintainer — see Phase 7).

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (stale/slow per task note); reasoned from source
- decl `PadicLFunctions.norm_pow_p_sub_one_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:96`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the extended (Iwasawa-branch) p-adic logarithm `extLog` on rational-valuation elements of a complete ultrametric `ℚ_[p]`-algebra `L` (RJW §6, decomposition W6a); this file builds the convergence-ball / exp-ball machinery the construction needs

---

### Statement (Phase 1)

`PadicLFunctions.norm_pow_p_sub_one_le` is a theorem stating the following:

Let `L` be a complete ultrametrically-normed field that is a normed `ℚ_[p]`-algebra
(`p` prime). For any `w ∈ L` lying in the open unit ball around `1` (`‖w − 1‖ < 1`),
the p-th power `w^p` is **at least as close to `1`** as a sharp two-term bound allows:

  ‖w^p − 1‖ ≤ max( ‖w − 1‖^p , p⁻¹·‖w − 1‖ ).

This is the quantitative "raising a one-unit to the p-th power contracts it towards
1" estimate. Writing `t = w − 1` and expanding `w^p = (1 + t)^p = 1 + Σ_{i=1}^{p} C(p,i) t^i`,
the top term contributes `‖t‖^p` and every interior term `C(p,i) t^i` (for `0 < i < p`)
carries the divisibility `p ∣ C(p,i)`, so `‖C(p,i)‖ ≤ p⁻¹` and that term is bounded by
`p⁻¹·‖t‖`; the ultrametric max-inequality on the sum gives the stated maximum.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`
  — the ambient complete ultrametric `ℚ_[p]`-algebra. (`[CompleteSpace L]` is `omit`-ted
  for this lemma; it is not used here.)
- `w : L` — the one-unit-ish element.

Hypotheses (Lean side):
- `hw : ‖w − 1‖ < 1` — `w` lies in the open unit ball around `1`.

Conclusion (math): `‖w^p − 1‖ ≤ max(‖w−1‖^p, p⁻¹·‖w−1‖)`.

Conclusion (Lean): `‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a quantitative helper estimate ("W6a-a3" in the project's decomposition),
not a named theorem and not a `## Main results` headline; it is an intermediate
contraction bound feeding `exists_pPow_pow_inExpBall`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for
the report's framing.)

### One-line check (Phase 2b)

Body line count: ~25 substantive lines (binomial expansion + `Finset` ultrametric sum
bound + top-term/interior-term case split + divisibility argument).
One-liner verdict: **n/a — kind is theorem, not def.**

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                  | Hit? | Standard form found                                                                 | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm principal units p-th power closer to 1 ultrametric estimate norm"                                    | yes  | exp/log isometry on `‖x‖ < p^{−1/(p−1)}`; image of log on principal units (Iwasawa)  | arXiv 1904.09850 / 1907.06437; Conrad notes; Dion report — exactly this circle of ideas |
|  2 | WebSearch (general form)         | "'1+p' raising to p-th power valuation increases local field one-units convergence exponential logarithm"               | yes  | for `1`-units `1+b`, p-th-power valuation grows; `exp/log` iso on `U^{(n)}` for `n > e/(p−1)` | Cambridge Part III *Local Fields* (Johansson); MIT/Bai notes — the contraction step is the standard mechanism |
|  3 | WebSearch (named-after / aliases)| "binomial theorem p divides binomial coefficient norm bound (x−1)^p ultrametric p-adic power series log convergence"     | yes  | `p ∣ C(p,i)` for `0<i<p` (Kummer/standard); used to check p-adic convergence of `(1+x)^b` | Kummer's theorem (Wikipedia) is the arithmetic core; the norm estimate is the standard application |
|  4 | WebSearch (nLab/textbook sweep)  | "nLab p-adic exponential logarithm radius of convergence one-units local field"                                         | yes  | exp radius `p^{−1/(p−1)}`; log on `\|z−1\|<1`; `log(1+m_K)` is a `ℤ_p`-module           | PlanetMath, MIT `dav/exp.pdf`, Wikipedia "p-adic exponential", Chen REU, Cambridge `jat58/all.pdf` — unanimous |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/`                                               | n/a  | directory absent on this machine                                                     | `.mathlib-quality/references/` does not exist; `refs/` (local-only PDF store, gitignored) not present — recorded n/a |
|  6 | nLab                             | "p-adic exponential" page fetch + WebSearch sweep (#4)                                                                  | yes  | radius `p^{−1/(p−1)}`, log on the open unit ball — same standard picture              | direct page 404'd via fetcher; covered by the WebSearch sweep #4 which surfaced nLab-adjacent canonical sources |
|  7 | nCatLab (if categorical)         | —                                                                                                                      | n/a  | not a categorical concept                                                            | a quantitative norm estimate in a normed field; no categorical content |
|  8 | Stacks Project (if alg geom)     | —                                                                                                                      | n/a  | not a scheme-theoretic / algebraic-geometry concept                                  | pure p-adic functional analysis; Stacks has no analytic norm-estimate API |
|  9 | MathOverflow / Math.StackExchange| "valuation (1+x)^p minus 1 local field one units p-th power increases valuation exp log isomorphism"                     | no   | no single canonical thread surfaced                                                  | the estimate is a textbook exercise, too elementary to be a standalone MO question; the construction it feeds is in every local-fields course |
| 10 | recent arXiv (last 5 years)      | covered by #1 ("On the image of p-adic logarithm on principal units", arXiv 1904.09850 (2019), 1907.06437 (2023))       | yes  | modern treatments still use the exp/log iso on the convergence ball                  | the contraction step is assumed/used, not re-proved as a headline result |
| —  | ChatGPT MCP                      | (intended) "standard form + generality + historical evolution of the (1+x)^p contraction estimate"                      | n/a  | MCP tool not configured in this environment                                          | no `mcp__chatgpt`/`mcp__openai` tool present; compensated with an extra WebSearch (#4) + authoritative lecture-note/textbook sources |

The protocol passes: WebSearch ran **4** distinct queries across generality levels
(specific exp/log-on-units form; general valuation-grows form; the named arithmetic
core `p ∣ C(p,i)`; and a textbook/nLab sweep). Local references, nLab, nCatLab,
Stacks, MathOverflow, and recent arXiv were each checked or recorded `n/a` with a
reason. ChatGPT MCP is `n/a` (tool absent) — explicitly compensated.

### Literature summary (Phase 3)

Concept identified as: the **p-th-power contraction estimate for one-units**, the
quantitative engine behind the p-adic exponential/logarithm on the unit group of a
non-archimedean (local) field — i.e. that `(1+x)^p` lies strictly closer to `1` than
`1+x`, which is what drives one-units into the exp/log convergence ball of radius
`p^{−1/(p−1)}`.

Sources agree on the standard form: **yes**. Every treatment states the underlying
fact identically (in valuation form `v((1+x)^p − 1) ≥ min(p·v(x), v(p) + v(x))`, or in
norm form `‖(1+x)^p − 1‖ ≤ max(‖x‖^p, ‖p‖·‖x‖)` — these are the same statement, and
`‖p‖ = p⁻¹` for `ℚ_p` and its extensions, matching the Lean conclusion exactly).

Most general standard form: the estimate holds in **any** non-archimedean (ultrametric)
field/ring containing the relevant prime, for any element of the open unit ball around
`1`. The Lean form's hypotheses (`NormedField` + `IsUltrametricDist` + `NormedAlgebra ℚ_[p]`,
with `‖p‖ = p⁻¹`) are exactly this standard setting.

Generality dimensions where the literature varies:
- **Ambient object**: from `ℚ_p`/`ℂ_p` specifically, up to any complete ultrametric
  field, up to any non-archimedean normed ring. The most general is the normed-ring level;
  the local-field level is the textbook default.
- **Formulation**: valuation (`v`) vs. norm (`‖·‖`). Equivalent; mathlib's `IsUltrametricDist`
  norm form is the natural Lean idiom.

Disagreement with the literature: **none.** The Lean statement is the standard estimate,
phrased in the modern ultrametric-distance idiom. The only mismatch with "named theorem"
status is that the literature treats this as an *intermediate step*, not a headline named
result — relevant to the verdict (Phase 7), not to correctness.

---

### Generality analysis — `PadicLFunctions.norm_pow_p_sub_one_le`

Literature-standard form (from Phase 3): `‖(1+x)^p − 1‖ ≤ max(‖x‖^p, ‖p‖·‖x‖)` over any
complete non-archimedean field (or normed ring) where `‖p‖` is the residue prime's norm.

| # | Parameter / hypothesis             | Current Lean form                              | Literature-standard form              | Weaker form exists? | Reason it can / can't be weakened |
|---|------------------------------------|------------------------------------------------|----------------------------------------|---------------------|-----------------------------------|
| 1 | `[NormedField L]`                  | normed field                                   | non-archimedean field; often a normed *ring* suffices | maybe               | the proof uses `norm_mul` (multiplicative norm) and `Nat.cast`; a `NormedRing`/`NormedCommRing` with a submultiplicative norm *might* carry it, but `(p:ℝ)⁻¹ = ‖p‖` and the precise top-term equality `‖C(p,p)‖=1` lean on the field/`ℚ_p`-algebra structure — weakening is non-trivial, not mechanical |
| 2 | `[IsUltrametricDist L]`            | ultrametric (strong triangle)                  | ultrametric (essential)                | NO                  | the whole `norm_sum_le_of_forall_le_of_nonneg` step *is* the ultrametric inequality; cannot be removed |
| 3 | `[NormedAlgebra ℚ_[p] L]`          | normed `ℚ_[p]`-algebra                          | "field of residue char `p`"            | partially           | used only to pin `‖(p:L)‖ = p⁻¹` (via `norm_natCast_p`); the genuinely general hypothesis is "`‖(p:L)‖ ≤ p⁻¹`" (or `= p⁻¹`). Restating against a bare `‖(p:L)‖ ≤ p⁻¹` hypothesis would generalise away the `ℚ_[p]`-algebra assumption — a real, literature-supported weakening |
| 4 | `(hw : ‖w − 1‖ < 1)`               | open unit ball around `1`                       | `v(w−1) > 0`, i.e. `‖w−1‖ < 1`         | NO                  | this is the standard one-unit hypothesis; already maximally general |
| 5 | `[CompleteSpace L]`                | (omitted via `omit`)                            | not needed                             | already done        | correctly `omit`-ted — completeness is irrelevant to this finite estimate |

This is a literature-grounded weakening pass. The one substantive opportunity is axis
**#3**: the `[NormedAlgebra ℚ_[p] L]` assumption is used *only* to obtain `‖(p:L)‖ = p⁻¹`.
The literature-general statement needs only a bound on `‖(p:L)‖`, decoupling the lemma
from the `ℚ_[p]`-algebra layer (it would then apply to e.g. any ultrametric field of
residue characteristic `p`). Axis #1 (field → ring) is a further, harder weakening.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (mildly).
Number of weakening opportunities found: **K = 2** (one clean: axis #3; one harder:
axis #1).

Proposed restatement (clean weakening, axis #3) — decouple from `ℚ_[p]`-algebra:

```lean
theorem norm_pow_p_sub_one_le {L : Type*} [NormedField L] [IsUltrametricDist L]
    {p : ℕ} [Fact p.Prime] (hpL : ‖(p : L)‖ ≤ (p : ℝ)⁻¹)
    {w : L} (hw : ‖w - 1‖ < 1) :
    ‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖) := …
```

Cost of restatement: **CHEAP–MODERATE** — the proof body changes only by replacing the
`norm_natCast_p p` rewrite (which gives `‖(p:L)‖ = p⁻¹`) with the hypothesis `hpL`
(`≤ p⁻¹`); the `mul_le_of_le_one_right` step already tolerates a `≤` bound. Essentially
mechanical.

Per the skill's cost note: cost is NOT a verdict factor. This narrowing-vs-standard
finding is what makes `YES-add-as-is` unavailable (a YES would have to be
`YES-but-generalise-first`); it also feeds the BORDERLINE question about *which* form a
hypothetical mathlib contribution should take.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let L be a foo" preambles → typeclasses?                                                          | no       | —                      | already fully typeclass-based (`NormedField`/`IsUltrametricDist`/`NormedAlgebra`); nothing bundled to unbundle |
|  2 | sequences/metric → filters/topological?                                                           | no       | —                      | a single finite inequality; no limit/sequence content to filter-ise (the limit lives in the *consumer* `exists_pPow_pow_inExpBall`, not here) |
|  3 | construction → universal-property class?                                                          | no       | —                      | it's an estimate, not a construction |
|  4 | set-with-closure-predicate → bundled substructure?                                                | no       | —                      | no substructure; though note `InExpBall` (the consumer's object) *could* eventually be a bundled subgroup — out of scope for this lemma |
|  5 | vector-space/metric/field-specific → weaken to module/pseudometric/(semi)ring?                    | **yes**  | drop `NormedAlgebra ℚ_[p]` to a bare `‖(p:L)‖ ≤ p⁻¹` hypothesis (Phase 4b axis #3); possibly `NormedField`→`NormedCommRing` (axis #1) | the lemma would then apply to any ultrametric field of residue char `p`, not only `ℚ_[p]`-algebras — composes with mathlib's general `IsUltrametricDist` API rather than the project-local `ℚ_[p]`-algebra layer |
|  6 | 1-categorical → higher-categorical?                                                               | no       | —                      | no categorical content |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                  | no       | —                      | `p` is intrinsically the residue prime; the exponent must be exactly `p` for `dvd_choose_self` — not a free index to generalise |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild)** — same content as Phase 4b axis #3/#1.
- Proposed mathlib-idiomatic restatement: the `hpL : ‖(p:L)‖ ≤ (p:ℝ)⁻¹` form above
  (and, more ambitiously, over an ultrametric `NormedCommRing`).
- Cost: **CHEAP–MODERATE**.
- Mathlib downstream this enables: lifts the estimate out of the project's `ℚ_[p]`-algebra
  silo so it sits on mathlib's general `IsUltrametricDist` foundation, where it could feed
  *any* future p-adic exp/log development (`ℂ_p`, general local fields), not just this one.
- Real mathematical improvement (not just "looks cooler"): **yes** — it states the result
  at the generality the proof actually achieves (it never uses the `ℚ_[p]`-algebra structure
  beyond `‖p‖ = p⁻¹`), which is the honest mathlib form.

Because Phase 4c (and 4b) found a real, literature-supported weakening, the verdict gate
**forbids `YES-add-as-is`**: a positive verdict must be `YES-but-generalise-first`. This
is folded into the BORDERLINE synthesis (Phase 7).

---

### Diamond / defeq risk — `PadicLFunctions.norm_pow_p_sub_one_le`

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search
paths introduced). Phase 4.5 skipped.

---

### Mathlib search-status: `PadicLFunctions.norm_pow_p_sub_one_le`

[A] Lean-Finder       "norm of (1+x)^p−1 ultrametric bound" / "p-adic log convergence ball" — n/a: AI endpoint (LeanSearch UI) returned 404/405 to the fetcher (JS-gated app); substituted by the natural-language WebSearches in Phase 3 + Loogle [B]
[B] Loogle            `‖_ ^ _ - 1‖ ≤ _`  → 82 declarations mentioning the operators, **0 match**; `‖_ ^ _ - 1‖ ≤ max _ _` → 6 mentioned, **0 match**   → no hits
[C] LeanSearch        (same NL queries as [A])  → n/a: API endpoints 404/405 via fetcher; covered by Phase-3 WebSearch + local grep
[D] Grep mathlib src  `norm_pow.*sub_one`, `pow.*- 1.*max`, `def padicExp|padicLog`, `frobenius` in `Analysis/Normed/`, `Krasner.lean` body, `InExpBall`/`principalUnit`/`oneSubBall`  → **no hits** for the bound; **zero** p-adic exp/log defs anywhere in mathlib
[E] Name pattern      `norm_pow_p_sub_one`, `pow_p_sub_one`, `one_sub_pow`  → only `IsPrimitiveRoot.norm_pow_sub_one_*` (cyclotomic units; different statement, see below)  → no hits

Searched for both:
  - the user's current form (`ℚ_[p]`-algebra) — not present;
  - the literature-standard form (general ultrametric / `‖p‖`-bounded) — not present; and
  - the surrounding framework (p-adic log/exp, exp ball) — **entirely absent** from mathlib.

The nearest mathlib hits and why they are NOT this lemma:
- `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two` etc. (`Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean`): compute the *exact algebraic norm* `N(ζ^s − 1)` of cyclotomic units in number fields — a global field-norm value, not a generic ultrametric upper bound on `‖w^p − 1‖`. Different object, different conclusion.
- `Mathlib/Analysis/SpecialFunctions/Log/RpowTendsto.lean:30` (`‖p⁻¹·(x^p − 1) − log x‖ ≤ p·‖log x‖²`): an **Archimedean real** Taylor-remainder estimate for `x^p ≈ 1 + p log x`. Different (real, not p-adic; quadratic remainder, not a max-bound).
- `Mathlib/Analysis/Normed/Field/Krasner.lean`: Krasner's lemma only — two theorems, unrelated.

Building blocks the proof uses all exist in mathlib (used as *separate* lemmas, not composed):
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Nat.Prime.dvd_choose_self`
(`Mathlib/Data/Nat/Choose/Dvd.lean`), `add_pow`, `Nat.choose_self`, `pow_le_of_le_one`,
`pow_le_pow_left₀`, `IsUltrametricDist.norm_natCast_le_one`.

Concluded: **not in mathlib** (all methods exhausted, both forms, plus the entire
p-adic-log/exp framework is absent). Mathlib has the *atomic ingredients* but neither this
estimate nor the context it serves.

---

### Call sites — `PadicLFunctions.norm_pow_p_sub_one_le`

Internal use count: **K = 1**  (within the project, excluding the declaring line)
External-to-file callers: **0** distinct files (the one caller is in the same file)

| Caller file:line                                              | Usage pattern (one-line excerpt)                 |
|---------------------------------------------------------------|--------------------------------------------------|
| projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:145      | `have hstep := norm_pow_p_sub_one_le p hk1`      |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `norm_pow_p_sub_one_le`?):
  - (none) — no other site re-derives a `‖·^p − 1‖ ≤ max(…)` bound.

What the call-sites pattern tells you: **K = 1, no inline re-derivation.** Per the
Phase-6.0.1 table this leans toward NO-composable / "possibly the wrong abstraction —
could be inlined." BUT the single caller (`exists_pPow_pow_inExpBall`) uses it *inside an
induction step* where inlining a 25-line binomial estimate would bloat the proof badly —
so extraction is justified on readability grounds even at K = 1. The low call count is a
genuine signal that this is presently an internal stepping-stone, which is exactly the
tension the verdict must resolve (Phase 7).

### Composition check (Phase 6)

Can `norm_pow_p_sub_one_le` be derived from mathlib in ≤3 chained calls?

Attempt 1: `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (...) (fun i hi => ...)`
applied to the binomial expansion of `(1+t)^p`.
  - Mathlib decls used: `add_pow`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
    `Nat.Prime.dvd_choose_self`, `Nat.choose_self`, `pow_le_of_le_one`, `norm_natCast_p`.
  - Result: **fails** as a ≤3-call composition. It requires: (a) rewriting `w^p` as the
    binomial sum `Σ C(p,i) t^i` (a `rw [add_pow, Finset.sum_range_succ']; simp; ring`
    block — real rewriting), (b) the ultrametric sum bound, (c) a **case split** on the
    top term `i+1 = p` vs. interior terms, and (d) inside the interior case, the
    divisibility `p ∣ C(p,i+1)` plus a `calc` chain bounding `‖t‖^(i+1)·‖C‖ ≤ p⁻¹·‖t‖`.
    That is a ~25-line proof with a case analysis, not a 1–3-call chain.
  - Notes: per Phase 6b heuristics, "multiple `have`s with non-trivial reasoning + a
    `rw [...]; ring` block + a case split" = **a proof, not a composition.**

Attempt 2 (different angle — is there a single mathlib lemma + `.le`/`.trans`?):
  - No. Phase 5 found no mathlib lemma of this shape to chain off; the only `‖x^n−1‖`
    lemmas are the cyclotomic-norm and real-Taylor results, neither chainable here.

Conclusion: **NOT-COMPOSABLE.** The result needs a genuine ~25-line proof; mathlib's
primitives do not assemble it in ≤3 calls.

---

## Verdict: `PadicLFunctions.norm_pow_p_sub_one_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): unanimous — this is the standard p-th-power contraction
  estimate for one-units, the engine of the p-adic exp/log on local fields (Cambridge
  Part III, MIT/Conrad/PlanetMath notes, Iwasawa principal-units papers). Treated
  everywhere as an *intermediate step*, not a named headline theorem.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the
  `[NormedAlgebra ℚ_[p] L]` hypothesis is used only for `‖p‖ = p⁻¹`; the honest form needs
  only `‖(p:L)‖ ≤ p⁻¹` (Phase 4b axis #3, Phase 4c row 5). So a YES would have to be
  `YES-but-generalise-first`, never `YES-add-as-is`.
- Mathlib search (Phase 5): **not in mathlib** under either form; moreover mathlib has
  **no p-adic logarithm/exponential and no exp-ball framework at all** — the entire
  surrounding context is absent.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a real ~25-line proof, not a ≤3-call
  chain); K = 1 internal call site, no inline re-derivation elsewhere.

**Rationale:**

Three of the four signals point at "mathlib does not have this and cannot trivially get
it": the lemma is genuinely absent (Phase 5), genuinely non-trivial (Phase 6
NOT-COMPOSABLE), and sits on a standard, well-attested piece of mathematics (Phase 3).
That alone would normally argue for a YES bucket — and because Phase 4 found a real
generality gap, the YES bucket would specifically be `YES-but-generalise-first` (ship the
`‖(p:L)‖ ≤ p⁻¹` form, decoupled from `ℚ_[p]`-algebras).

But two facts make this a genuine judgment call rather than a self-resolving YES. **First**,
the literature treats this estimate as an *intermediate lemma inside the construction of
the p-adic exp/log on local fields* — never as a standalone named result. Mathlib has
**none** of that construction (zero `padicLog`/`padicExp` definitions, no exp-ball). So the
real question is not "is this lemma true and missing" (it is both) but "**is a lone
contraction-step estimate, divorced from the framework it serves, the right grain for a
mathlib PR — or should it land only as part of contributing the whole p-adic-log-on-
local-fields package (`InExpBall`, `padicLog`, the convergence theorem, this estimate, and
the iterate-into-the-ball lemma `exists_pPow_pow_inExpBall` together)?**" That is a
scope/packaging decision the skill cannot make alone: it depends on whether the maintainers
intend to upstream the p-adic-log framework at all, and at what granularity. **Second**, the
call-site evidence (K = 1, internal, no external consumers) is consistent with "currently
a private stepping-stone," which sharpens the same question. Per the skill's rules, when
the verdict hinges on packaging/scope judgment and project policy rather than on the
evidence, the honest bucket is BORDERLINE with the questions spelled out — not a
silently-chosen YES.

(Note: cost is **not** the reason for BORDERLINE — the generalisation is CHEAP–MODERATE,
and even if it were EXPENSIVE that would not downgrade the verdict. The BORDERLINE driver
is purely the framework-grain / upstreaming-scope judgment plus the audience-narrow,
K = 1 signal.)

**Numbered questions (for the maintainer):**

1. Do you intend to upstream the p-adic logarithm / exponential framework (`InExpBall`,
   `padicLog`, `padicExp`, the convergence/isometry theorems) to mathlib at all? If **no**,
   this estimate stays project-local and the verdict collapses to "keep as-is internally"
   (no mathlib action). If **yes**, go to Q2.

2. If upstreaming the framework: should `norm_pow_p_sub_one_le` be PR'd **as part of that
   bundle** (the natural grain — it is one lemma in the exp/log construction), or do you
   want it broken out as an independent general-ultrametric estimate first?

3. For a mathlib PR, ship the **generalised** form
   `(hpL : ‖(p:L)‖ ≤ (p:ℝ)⁻¹) → ‖w^p − 1‖ ≤ max (‖w−1‖^p) (p⁻¹·‖w−1‖)` (drops the
   `[NormedAlgebra ℚ_[p] L]` assumption per Phase 4b/4c)? This is CHEAP–MODERATE and is the
   honest generality of the proof. (Recommended yes.)

4. Should the further weakening `NormedField → NormedCommRing` (Phase 4b axis #1) be
   attempted as well, or is the field-level statement the right mathlib target? (This one
   is harder and may need proof adjustments.)

**Next action:** maintainer answers Q1–Q4. If Q1 = no → no mathlib action; keep the lemma
as the internal helper it is (it is correctly `omit`-ting `[CompleteSpace L]` and is cleanly
proved). If Q1 = yes → re-run `/mathlibable` (or proceed to `/generalise
PadicLFunctions.norm_pow_p_sub_one_le` to produce the `‖(p:L)‖ ≤ p⁻¹` form) and PR it,
most naturally **bundled** with the rest of the exp/log-on-local-fields development rather
than as a lone estimate.

---

## Next step

Maintainer answers the four questions above. The likely resolutions:
- **Framework not being upstreamed** → drop from mathlib consideration; keep project-local.
- **Framework upstreamed, bundled grain** → `YES-but-generalise-first` (generalise to the
  `‖(p:L)‖ ≤ p⁻¹` form via `/generalise`), shipped together with `InExpBall` / `padicLog` /
  `exists_pPow_pow_inExpBall` as one coherent p-adic-log PR series.
