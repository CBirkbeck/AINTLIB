# `/mathlibable` report — `PadicLFunctions.sigmaP_eq_of_not_dvd`

**Final verdict: `NO-composable-from-mathlib`.** The lemma states the trivial fact
that the prime-to-`p` divisor power sum `σ^p_k(n)` equals the full divisor power sum
`σ_k(n)` when `p ∤ n` (because then *every* divisor of `n` is automatically coprime to
`p`). Its proof is a 2-call composition of mathlib primitives
(`Finset.filter_true_of_mem` inside `Finset.sum_congr`) after unfolding the
project-local def `PadicLFunctions.sigmaP` and mathlib's `ArithmeticFunction.sigma_apply`.
It is a lemma *about a project-local definition that mathlib does not contain*, so it
cannot go to mathlib in its current form; the underlying composition is what any
future `sigmaP`-style API would inline at the call site. See the cross-link to the
parent `sigmaP` (BORDERLINE) below.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task note: build may be stale/slow)
- decl `PadicLFunctions.sigmaP_eq_of_not_dvd`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:47`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  RJW §8 complex side — the q-expansion of the p-stabilised Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`, and its coefficients via the prime-to-`p` divisor sum.

Dependency closure (read from source, not built):
- `PadicLFunctions.sigmaP` (def) — `EisensteinFamily.lean:62`:
  `sigmaP (k n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d), d ^ k`
- `ArithmeticFunction.sigma` (mathlib) — `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`:
  `σ k n = ∑ d ∈ divisors n, d ^ k`, with `sigma_apply : σ k n = ∑ d ∈ divisors n, d ^ k := rfl` (line 151).

---

### Statement (Phase 1)

`PadicLFunctions.sigmaP_eq_of_not_dvd` is a theorem stating the following:

> Let `p` be a prime and `n` a natural number with `p ∤ n`. Then for every exponent
> `k`, the sum of `k`-th powers of the divisors of `n` that are coprime to `p` equals
> the sum of `k`-th powers of *all* divisors of `n`. In symbols, `σ^p_k(n) = σ_k(n)`.

The content is entirely trivial: if `p ∤ n` then no divisor `d ∣ n` can be divisible
by `p` (else `p ∣ d ∣ n`), so the "prime-to-`p`" filter on `n.divisors` removes
nothing and the two sums are termwise identical.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (the `Fact` instance is `omit`-ted in this
  lemma; primality is not used, only the divisibility transitivity is).
- `n : ℕ` — the index of the divisor sum.
- `k : ℕ` — the power.

Hypotheses (Lean side):
- `(hn : ¬ (p : ℕ) ∣ n)` — `p` does not divide `n`. This is the only real hypothesis.

Conclusion (math): the restricted (prime-to-`p`) divisor power sum coincides with the
full divisor power sum.

Conclusion (Lean): `sigmaP p k n = ArithmeticFunction.sigma k n`.

Proof body (verbatim):
```lean
rw [sigmaP, ArithmeticFunction.sigma_apply]
refine Finset.sum_congr (Finset.filter_true_of_mem fun d hd hpd =>
  hn (hpd.trans (Nat.mem_divisors.1 hd).1)) fun _ _ => rfl
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a one-hypothesis helper lemma that equates a filtered divisor sum with
the full divisor sum — a corollary/specialisation, not a new structure, not a
named theorem, not a `## Main results` entry. (The parent *def* `sigmaP` was rated
SMALL-borderline-to-BIG; this lemma *about* it is unambiguously SMALL.)

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for the
report's framing only.)

### One-line check (Phase 2b)

Body line count: n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`.
One-liner verdict: n/a (kind is theorem/lemma, not def).

(The proof is two tactic lines; the one-liner *definition* check does not apply to
theorems. The proof's brevity is captured in Phase 6 as the composition sketch.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "divisor sum coprime to p equals full divisor sum when p does not divide n sigma_k" | partial | no *named* result; `σ_t` multiplicative; restricted divisor sums treated ad hoc | MathWorld DivisorFunction, arXiv survey 1106.4038 — confirm `σ_k(n)=Σ_{d∣n}d^k`, multiplicativity; no name for "prime-to-`p` sum = full sum on `p∤n`" |
| 2 | WebSearch (general / context form) | `"sigma" arithmetic function "prime to p" divisor sum p-stabilization Eisenstein series` | yes (context) | "prime-to-`p` divisor sum" appears in p-stabilisation of Eisenstein series; `σ_k` as Hecke eigenvalue | arXiv 1207.0198 / 2302.13009 (semi-ordinary p-stabilisation, Fourier coefficients); confirms the *object* is standard, the *coincidence on `p∤n`* is a one-line remark |
| 3 | WebSearch (most-general / mathlib mechanism) | "finset sum over subset equals full sum when predicate always true filter_true_of_mem" | yes | `s.filter p = s` when `∀ x ∈ s, p x`; `Finset.sum_subtype_of_mem` | the general fact IS the mathlib lemma `Finset.filter_true_of_mem`; this is the building block, not a number-theory theorem |
| 4 | WebSearch (named-after / restricted-sum aliases) | "restricted divisor sum sum of divisors not divisible by prime equals sigma when gcd one elementary" | partial | "restricted divisor function" = *proper* divisors (different); modular restricted sums `σ_{a,m}` exist | no source names "Σ_{d∣n, p∤d} dᵏ"; the `p∤n ⟹ =σ_k(n)` step is universally treated as obvious |
| 5 | ChatGPT MCP | (intended) "standard form + generality + historical evolution of the prime-to-`p` divisor sum and its coincidence with σ_k when p∤n" | n/a | — | `chatgpt-math` MCP server is configured but listed in `mcp-needs-auth-cache.json` and is NOT exposed as a callable tool this session (ToolSearch: no match). Compensated by 4 WebSearch queries at 4 generality levels (protocol minimum of 3 distinct levels met). |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | n/a | (directory absent) | `references/` does not exist for this project; `refs/` symlink also absent — recorded n/a |
| 7 | nLab | "divisor function sigma multiplicative arithmetic function" | no | nLab has no dedicated `σ_k` "prime-to-`p`" entry | nLab is not where elementary divisor-sum identities live; nothing relevant |
| 8 | nCatLab (categorical) | — | n/a | — | not a categorical concept (a finite arithmetic identity); nothing to categorify |
| 9 | Stacks Project (alg geom) | — | n/a | — | not an algebraic-geometry concept; Stacks has no elementary divisor-sum identities of this kind |
| 10 | MathOverflow / Math.StackExchange | folded into #1/#4 (restricted/coprime divisor sum, elementary) | partial | treated as immediate ("every divisor of `n` is coprime to `p`") | consistent: nobody states this as a lemma; it is a parenthetical in p-stabilisation computations |
| 11 | recent arXiv (last 5 yrs) | folded into #2 (p-stabilisation Eisenstein, Siegel) | yes (context) | the prime-to-`p` Fourier coefficient is standard in p-adic Eisenstein families | confirms the *use*, not a *name* for the `p∤n` coincidence |

### Literature summary (Phase 3)

Concept identified as: the **prime-to-`p` (restricted) divisor power sum** `σ^p_k(n) =
Σ_{0<d∣n, p∤d} dᵏ`, and the elementary fact that it **coincides with `σ_k(n)` exactly
when `p ∤ n`**.
Sources agree on the standard form: yes — `σ_k(n)=Σ_{d∣n}dᵏ` is universal; the
prime-to-`p` variant is a standard auxiliary in p-stabilisation / p-adic L-function
work (RJW = Rubin–type / the project's source; arXiv 1207.0198, 2302.13009 for
Siegel; classical for `GL₂`).
Most general standard form: for any `n` and exponent `k`, `Σ_{d∣n, p∤d} dᵏ = σ_k(n) −
pᵏ·σ_k(n/p)` when `p∣n` (the companion lemma `sigmaP_add_pow_mul_sigma_div` here), and
`= σ_k(n)` when `p∤n` (this lemma). The `p∤n` case is the degenerate, trivial half.
Generality dimensions where the literature varies:
  - exponent `k`: the literature states it for general `k` (and even complex `s`); the
    Lean form uses `k : ℕ`, matching the modular-forms application (`σ_{k−1}`).
  - the "prime-to-`p`" filter generalises to "prime-to-`m`" / "coprime to a fixed set",
    but the `p∤n ⟹ =σ_k(n)` coincidence is identical in content (vacuous filter).
Disagreement with the literature: none. The literature never *names* this identity; it
is the obvious half of the divisor-splitting used in p-stabilisation.

**Signal:** the literature returns the *object* (prime-to-`p` divisor sum) as standard
but returns **no named theorem** for the `p∤n` coincidence — it is universally a
one-line remark. That is a strong indicator this is composition-grade, not a
mathlib-worthy standalone result.

---

### Generality analysis — `PadicLFunctions.sigmaP_eq_of_not_dvd`

Literature-standard form (from Phase 3): for `p∤n`, `Σ_{d∣n, p∤d} dᵏ = σ_k(n)`, with `k`
an arbitrary exponent. The Lean form matches this exactly at `k : ℕ`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[Fact p.Prime]` (`omit`-ted) | `p` prime, but primality unused | `p` need only be a fixed natural ≥ 1 / any element | yes — already not used | The proof only needs `p ∣ d → p ∣ n` (transitivity) + `d ∣ n` from `mem_divisors`. Primality is irrelevant; the statement holds for **any** `p : ℕ` (indeed any `p` in any monoid with the divisor finset). The lemma already `omit`s `hp`. |
| 2 | `(hn : ¬ p ∣ n)` | `p` does not divide `n` | same | NO | This is the defining hypothesis; weakening it changes the statement (the `p∣n` case is the *companion* lemma, not this one). |
| 3 | `(k : ℕ)` exponent | `ℕ` power, summing `dᵏ` | the summand can be *any* function `f : ℕ → M`, `M` a commutative monoid | yes (trivially) | The proof never touches `dᵏ` specifically — it equates two sums over the same index set via `sum_congr ... rfl`. The genuinely general statement is `Σ_{d∈s.filter q} f d = Σ_{d∈s} f d` when `q` is vacuously true on `s` — which is *exactly* `Finset.filter_true_of_mem`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along axes 1 and 3), but the
"general form" it specialises to is **not a divisor-sum theorem at all** — it is the
plain `Finset` lemma `Finset.filter_true_of_mem`. There is no number-theoretic
generalisation worth a separate divisor-sum lemma; the maximally-general statement is
already in mathlib as a `Finset` primitive.
Number of weakening opportunities found: 2 (primality unused; exponent `k` is incidental).
Proposed restatement: none worth shipping — see Phase 6. The "generalisation" collapses
to `Finset.filter_true_of_mem`, which mathlib has.
Cost of restatement: CHEAP, but moot — the general form is a re-derivation of an
existing mathlib lemma, not a new contribution.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | the only typeclass (`Fact p.Prime`) is already omitted/unused |
| 2 | sequences/metric → filters/topology? | no | — | a finite arithmetic identity; no limits |
| 3 | construction → universal-property class? | no | — | nothing constructed |
| 4 | set-with-predicate → bundled substructure? | no | — | `Finset.filter` is already the right tool |
| 5 | vector-space/field-specific → module/(semi)ring? | partly | the summand `dᵏ` could be any `f : ℕ → M`; but that is `Finset.filter_true_of_mem`, not a new sigma lemma | no *new* downstream — the modernised form **is** the existing mathlib `Finset` lemma |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive/ordered? | partly | filter "prime-to-`p`" → "prime-to-`m`"/general predicate; but again that is `filter_true_of_mem` | no new downstream |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (in the sense that fires `YES-but-generalise-first`).
The honest "modernisation" of this lemma is to *stop having it* and call
`Finset.filter_true_of_mem` directly — i.e. the modern idiom is composition, which is
the Phase 6 / Phase 7 conclusion, not a new generalised declaration. There is no
mathematical-organisation improvement to be had by adding a generalised divisor-sum
lemma, because the general fact is the already-present `Finset` primitive.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equality or typeclass-search path
introduced).

---

### Mathlib search-status: `PadicLFunctions.sigmaP_eq_of_not_dvd`

[A] Lean-Finder — n/a: Lean-Finder MCP not available this session (no deferred tool). Compensated by [D]+[E] direct grep over the vendored mathlib tree at `.lake/packages/mathlib/`.
[B] Loogle — n/a: Loogle MCP not available this session. Type pattern reasoned by hand: the statement is `?f ?p ?k ?n = ArithmeticFunction.sigma ?k ?n` where `?f = PadicLFunctions.sigmaP` is **not a mathlib name**, so Loogle on the exact type is vacuous; the relevant Loogle-style query is `Finset.sum (Finset.filter _ _) _ = Finset.sum _ _`, whose hit is the building block `Finset.filter_true_of_mem` (found via [D]).
[C] LeanSearch — n/a: LeanSearch MCP not available this session. NL query "sum of k-th powers of divisors coprime to p equals sigma when p does not divide n" resolves, by [D]/[E], to: no mathlib decl (mathlib has no `sigmaP`).
[D] Grep mathlib src — terms tried: `sigmaP`, `coprimeSigma`, `sigma_coprime`, `primeToP`, `sigma.*not_dvd`, `divisors.*not_dvd`, `filter_true_of_mem`, `sum_filter_true`, `filter_eq_self` over `.lake/packages/mathlib/Mathlib/`. Results: (i) **no `def sigmaP`** or prime-to-`p` divisor sum anywhere (the only `sigmaP*` hits are `Equiv.sigmaPUnit`, `Homeomorph.sigmaProdDistrib` — sigma *types*, unrelated). (ii) `ArithmeticFunction.sigma`/`sigma_apply` at `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143,151`. (iii) building block `Finset.filter_true_of_mem` at `Mathlib/Data/Finset/Filter.lean:166` (`= filter_eq_self.2 h`), used in this exact `filter_true_of_mem fun _ hx => …` idiom across mathlib (e.g. `Mathlib/Order/Interval/Finset/Basic.lean:280`). (iv) `Nat.mem_divisors`/`dvd_of_mem_divisors` at `Mathlib/NumberTheory/Divisors.lean:108,114`; `dvd_trans`/`Dvd.dvd.trans` at `Mathlib/Algebra/Divisibility/Basic.lean:69,72`.
[E] Name pattern — `lean_local_search` not available; grepped `*_eq_of_not_dvd` in `Mathlib/NumberTheory/`: hits are `inertiaDeg_eq_of_not_dvd`, `ramificationIdx_eq_of_not_dvd` (cyclotomic ideals — different subject). **No** `sigma`/divisor-sum `*_eq_of_not_dvd`.

Searched for both:
  - the user's current form (`PadicLFunctions.sigmaP … = σ k n`) — impossible in mathlib: `sigmaP` is a project-local def mathlib does not contain.
  - the literature-standard / general form (`Σ_{d∈s.filter q} f d = Σ_{d∈s} f d` for vacuous `q`) — **present** as `Finset.filter_true_of_mem` (+ `Finset.sum_congr`).

Concluded: **not in mathlib as a divisor-sum statement** (all grep/name methods
exhausted; mathlib has no `sigmaP` def hence no lemma about it), **but the building
blocks are present** (`Finset.filter_true_of_mem`, `Finset.sum_congr`, `Nat.mem_divisors`,
`dvd_trans`) — composition would yield the form. This is the
`NO-composable-from-mathlib` signature.

---

### Call sites — `PadicLFunctions.sigmaP_eq_of_not_dvd`

Internal use count: **1** (within the `PadicLFunctions` project, NOT counting the
declaring line). Both project-wide occurrences of the name are the definition
(`EisensteinComplex.lean:47`) and the single use (`EisensteinComplex.lean:249`).
External-to-file callers: **0** distinct files (the one use is in the *same file*).
External-to-project callers: **0** (the FltRegularBernoulli "sigmaP" substring hits are
unrelated — that project has no `def sigmaP`; its matches are inside other identifiers).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:249` | `rw [sigmaP_eq_of_not_dvd p hndvd (k - 1)]` — the `p ∤ n` branch of the coefficient identity inside `hasSum_stabilisedEisenstein` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the
lemma?): (none) — the companion `p∣n` case uses the sibling lemma
`sigmaP_add_pow_mul_sigma_div`; no third re-derivation of "filter is vacuous" exists.

**Composability signal (per the Phase 6.0.1 table):** K = 1 internal use, in the
*same file*, no external/downstream consumers — "possibly the wrong abstraction; could
be inlined; lean toward NO-composable." The single call site is one `rw` step in a
larger proof; inlining the 2-call composition there is mechanical.

---

### Composition check (Phase 6)

Can `PadicLFunctions.sigmaP_eq_of_not_dvd` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the actual proof, lightly recast as a one-shot composition):
```lean
example {p n k : ℕ} (hn : ¬ (p : ℕ) ∣ n) :
    (∑ d ∈ n.divisors.filter (fun d => ¬ (p : ℕ) ∣ d), d ^ k)
      = ArithmeticFunction.sigma k n :=
  (Finset.sum_congr
    (Finset.filter_true_of_mem fun d hd hpd => hn (hpd.trans (Nat.mem_divisors.1 hd).1))
    fun _ _ => rfl).trans ArithmeticFunction.sigma_apply.symm
```
  - Mathlib decls used: `Finset.filter_true_of_mem`, `Finset.sum_congr`,
    `Nat.mem_divisors`, `Dvd.dvd.trans` (`dvd_trans`), `ArithmeticFunction.sigma_apply`.
  - Result: **succeeds**. After unfolding the *project-local* `sigmaP` (one `rw`), both
    sides are sums over `n.divisors`; `filter_true_of_mem` proves the filter is the
    identity (its hypothesis `∀ d ∈ n.divisors, ¬ p ∣ d` is discharged by
    `d ∣ n` + `dvd_trans` + `hn`), and `sum_congr … rfl` finishes.
  - Notes: the per-element proof `fun d hd hpd => hn (hpd.trans (Nat.mem_divisors.1 hd).1)`
    is a single composed term (no intermediate `have`s, no `rw`/`ring`/`aesop`), so by
    the Phase 6b heuristics this is a genuine composition (the
    `Foo.bar (Bar.baz hx)`/`.trans` rows), not a proof in disguise.

Conclusion: **COMPOSABLE** — 2 mathlib calls (`sum_congr ∘ filter_true_of_mem`) plus the
unavoidable unfolds of the project-local def and `sigma_apply`. The number-theoretic
content (≤1 step) is below mathlib's lemma-granularity bar.

---

## Verdict: `PadicLFunctions.sigmaP_eq_of_not_dvd`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the prime-to-`p` divisor sum is a standard *object* in
  p-stabilisation, but **no source names the `p∤n` coincidence** as a theorem — it is
  universally a one-line remark ("every divisor of `n` is coprime to `p`"). ≥4 WebSearch
  queries across 4 generality levels (protocol minimum met); ChatGPT MCP unavailable
  (recorded n/a with reason); nLab/Stacks/nCatLab n/a-with-reason; arXiv confirms the
  object's use, not a name for the identity.
- Generality analysis (Phase 4): **STRICTLY NARROWER** than the general fact — but the
  general fact is the plain `Finset` lemma `Finset.filter_true_of_mem`, not a
  divisor-sum theorem (Phase 4c: the honest "modernisation" is to call that primitive
  directly, i.e. composition).
- Mathlib search (Phase 5): not in mathlib as a divisor-sum statement (mathlib has no
  `sigmaP` def, so no lemma about it); **building blocks present** —
  `Finset.filter_true_of_mem`, `Finset.sum_congr`, `Nat.mem_divisors`, `dvd_trans`,
  `ArithmeticFunction.sigma_apply`.
- Composition check (Phase 6): **COMPOSABLE** in 2 mathlib calls (sketch above).

**Rationale:**

`sigmaP_eq_of_not_dvd` is the trivial half of a divisor-splitting: when `p ∤ n`, the
"prime-to-`p`" filter on `n.divisors` is vacuous (any `d ∣ n` with `p ∣ d` would force
`p ∣ n`), so the restricted sum equals the full sum termwise. The literature treats
this as self-evident and never assigns it a name, and mathlib already contains the
*maximally general* form of the underlying fact as the `Finset` primitive
`Finset.filter_true_of_mem` (`s.filter q = s` when `q` holds on all of `s`). The lemma's
own proof is exactly that primitive wrapped in `Finset.sum_congr` — a 2-call
composition with no rewriting/automation glue, sitting below mathlib's lemma-granularity
bar.

Crucially, the lemma is *about the project-local definition* `PadicLFunctions.sigmaP`,
which mathlib does not contain (and whose own `/mathlibable` verdict is
`BORDERLINE-needs-human` — see `PadicLFunctions.sigmaP.md`). A statement whose left-hand
side is a non-mathlib symbol cannot be added to mathlib as written; whether mathlib
"should have" anything like it is entirely downstream of whether `sigmaP` itself is
upstreamed. Even in the world where some `sigmaP`-analogue lands in mathlib, this
particular identity is a 2-line `filter_true_of_mem`/`sum_congr` corollary that would be
inlined or proved on the spot, not shipped as a standalone lemma. The single internal
call site (one `rw` in `hasSum_stabilisedEisenstein`) reinforces this: it is a local
proof step, not a reusable API surface (K = 1, same file, zero external consumers). This
is therefore neither `NO-mathlib-has-it` (mathlib has no `sigmaP` and so cannot "have
it"), nor a YES bucket (no novel mathlib-worthy content; the general fact is already a
`Finset` primitive), but `NO-composable-from-mathlib`.

**Refactor-actionable detail (NO-composable-from-mathlib):**

WHY not: mathlib has the building blocks; the lemma is a 1-step
`Finset.filter_true_of_mem` composition wrapped in `Finset.sum_congr`, applied after
unfolding the project-local `sigmaP`. No new mathlib lemma is justified — the general
statement (`filter` vacuous ⟹ sum unchanged) is *already* `Finset.filter_true_of_mem`.

Mathlib building blocks:
- `Finset.filter_true_of_mem` — `.lake/packages/mathlib/Mathlib/Data/Finset/Filter.lean:166`
- `Finset.sum_congr` — `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
- `Nat.mem_divisors` (`.1` gives `d ∣ n`) — `Mathlib/NumberTheory/Divisors.lean:108`
- `Dvd.dvd.trans` / `dvd_trans` — `Mathlib/Algebra/Divisibility/Basic.lean:69`
- `ArithmeticFunction.sigma_apply` — `Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:151`

Composition sketch (≤3 lines, this is essentially the existing proof body):
```lean
-- after `rw [sigmaP, ArithmeticFunction.sigma_apply]` to expose both sums:
Finset.sum_congr
  (Finset.filter_true_of_mem fun d hd hpd => hn (hpd.trans (Nat.mem_divisors.1 hd).1))
  fun _ _ => rfl
```

Call sites in our project (from Phase 6.0): K = 1
(`EisensteinComplex.lean:249`, inside `hasSum_stabilisedEisenstein`).

Refactor plan / scope note: this is a verdict about **mathlib-worthiness, not
project-local hygiene**. Within the project, `sigmaP_eq_of_not_dvd` is a perfectly
reasonable named helper that documents one half of the σ-splitting next to its sibling
`sigmaP_add_pow_mul_sigma_div`, and there is no obligation to inline it — keeping it is
fine for the AINTLIB library. The actionable conclusion for *mathlib* is simply: **do
not propose this lemma to mathlib**. If, hypothetically, one were minimising the
project's surface, the single call site at `EisensteinComplex.lean:249` could inline the
two-call composition above (after the local `rw [sigmaP, ArithmeticFunction.sigma_apply]`
already present in context). But the primary recommendation is "not a mathlib
candidate", with no required local change.

Next action (mathlib): none — exclude from mathlib upstreaming. The lemma stays
project-local. Its mathlib-worthiness is fully contingent on (and dominated by) the
`BORDERLINE` parent `PadicLFunctions.sigmaP`; if that def is ever upstreamed, this
identity is a trivial `filter_true_of_mem` corollary to inline at that point, not a
separate PR.

---

## Next step

Exclude `PadicLFunctions.sigmaP_eq_of_not_dvd` from mathlib upstreaming
(`NO-composable-from-mathlib`): mathlib already has the maximally-general fact as
`Finset.filter_true_of_mem`, and this lemma is a 2-call composition of it over a
project-local def (`sigmaP`) that mathlib does not contain. Keep it project-local (it is
a fine helper alongside `sigmaP_add_pow_mul_sigma_div`); no required code change. The
question is moot for mathlib until/unless the parent def `sigmaP` (verdict:
`BORDERLINE-needs-human`, see `PadicLFunctions.sigmaP.md`) is itself upstreamed.
