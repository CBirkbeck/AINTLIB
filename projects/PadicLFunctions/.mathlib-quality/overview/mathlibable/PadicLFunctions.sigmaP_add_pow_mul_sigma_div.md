# `/mathlibable` report — `PadicLFunctions.sigmaP_add_pow_mul_sigma_div`

**Final verdict: `BORDERLINE-needs-human`** — the lemma states the
*subtraction-free divisor-splitting identity* `σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)`
for `p ∣ n` (`n ≠ 0`): the divisors of `n` split into the prime-to-`p` ones
(summing to `σ^p_k(n) = sigmaP p k n`) and `p·(divisors of n/p)` (summing to
`p^k·σ_k(n/p)`). It is a **genuine, non-trivial fact** (a `Finset.sum_nbij'`
re-indexing bijection, ~25 lines — **not** a ≤3-call composition), mathlib does
**not** have it in any form (mathlib has the *unrestricted* parent
`ArithmeticFunction.sigma`, its multiplicativity `isMultiplicative_sigma` and the
prime-power formula `sigma_apply_prime_pow`, plus the *generic* partition tool
`Finset.sum_filter_not_add_sum_filter`, but **no** prime-to-`p`/recursion
statement), and the literature confirms the identity is the routine,
**per-paper-introduced** defining relation behind the p-stabilised Eisenstein
coefficient `σ^{{p}}` (Kawamura arXiv 1207.0198/2302.13009;
`E*_{κ,χ} = E_{κ,χ} − χ(p)p^{κ−1}E_{κ,χ}(p·)`), with no canonical name. The
verdict is **inherited from its subject**: this lemma is stated *about*
`sigmaP`, whose own `/mathlibable` verdict is `BORDERLINE-needs-human` (no mathlib
`D'` to re-aim at; the "right" mathlib form — bare prime-to-`p` `Finset.sum` vs.
coprime-to-`m` vs. an `ArithmeticFunction.restrictCoprime` operator — and the
"name it at all?" question are maintainer-taste calls). A lemma cannot be more
mathlib-ready than the object it characterises: its final shape, generality, and
even its existence in mathlib are *contingent on the `sigmaP` decision*. Five
numbered questions are posed in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` is stale/slow in this checkout; the decl, its full proof body, every mathlib lemma it invokes, and the relevant mathlib `ArithmeticFunction`/`Divisors`/`BigOperators` API were read directly from `projects/…` and `.lake/packages/mathlib/Mathlib/…`, exactly as the skill's Phase-0 fallback allows).
- decl `PadicLFunctions.sigmaP_add_pow_mul_sigma_div`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinComplex.lean:56`
- kind:                      `theorem`
- has sorry:                 no (complete proof — a ~27-line body: one `Finset.sum_nbij'` bijection establishing `Σ_{p∣d} d^k = p^k·σ_k(n/p)`, then `Finset.sum_filter_not_add_sum_filter` to assemble)
- module docstring summary:  "The q-expansion of the p-stabilised Eisenstein series (RJW §8, complex side)" — `E_k^{(p)} = E_k − p^{k−1}E_k(p·)` has q-expansion `(1−p^{k−1})ζ(1−k)/2 + Σ σ^p_{k−1}(n)qⁿ` (TeX 2391); this lemma is the **arithmetic engine of the non-constant coefficient identity** (RJW's "easy check", TeX 2390–2393).
- mathlib pin (this checkout): rev `887d94632e` (`master-2026-06-19`), toolchain `leanprover/lean4:v4.32.0-rc1`.

Dependency chain read from source:
- **Subject** `PadicLFunctions.sigmaP` (`EisensteinFamily.lean:62`):
  `def sigmaP (k n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ (p:ℕ) ∣ d), d ^ k`
  — the prime-to-`p` divisor power sum, **project-local** (its own `/mathlibable`
  verdict is `BORDERLINE-needs-human`; see `PadicLFunctions.sigmaP.md`).
- The **unrestricted parent** `ArithmeticFunction.sigma` it is compared against
  (`.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`):
  ```lean
  /-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
  def sigma (k : ℕ) : ArithmeticFunction ℕ := ⟨fun n => ∑ d ∈ divisors n, d ^ k, by simp⟩
  -- theorem sigma_apply {k n} : σ k n = ∑ d ∈ divisors n, d ^ k := rfl        (:151)
  ```
- **Proof body** mathlib lemmas (all confirmed present in the pinned mathlib):
  - `ArithmeticFunction.sigma_apply` (Misc.lean:151) — unfold `σ` to a `Finset.sum`.
  - `Finset.mul_sum`, `Finset.sum_nbij'` (`Algebra/BigOperators/Group/Finset/Defs.lean:457`) — the surjective-injection re-indexing `d ↦ d/p` ↔ `e ↦ p·e` between `{d∣n : p∣d}` and `(n/p).divisors`.
  - `Finset.sum_filter_not_add_sum_filter` — the `@[to_additive]` form of `Finset.prod_filter_not_mul_prod_filter` (`Algebra/BigOperators/Group/Finset/Basic.lean:151`); **generic Finset API**, the partition `Σ_{¬P} + Σ_{P} = Σ` tool. (Used at `InclusionExclusion.lean:175`; **not** a `σ`/`sigmaP` statement.)
  - `Nat.mem_divisors`, `Nat.mul_div_cancel_left`, `Nat.mul_div_cancel'`, `mul_dvd_mul_iff_left`, `mul_dvd_mul_left`, `Nat.div_ne_zero_iff`, `Nat.le_of_dvd`, `Nat.pos_of_ne_zero`, `← mul_pow`, `Dvd.intro` — elementary `Nat`/divisibility plumbing for the bijection's four obligations + the value equality `d^k = p^k·(d/p)^k`.
- **Sibling** lemma in the same `section sigmaArithmetic` (the `p ∤ n` companion):
  `sigmaP_eq_of_not_dvd` (`EisensteinComplex.lean:47`) — `¬ p ∣ n → sigmaP p k n = σ k n`.

---

### Statement (Phase 1)

`PadicLFunctions.sigmaP_add_pow_mul_sigma_div` is **a theorem** stating the following:

> Fix a prime `p`. For a natural number `n` with `p ∣ n` and `n ≠ 0`, and any
> exponent `k`, the prime-to-`p` divisor power sum and the full divisor power sum
> of `n/p` add up to the full divisor power sum of `n`:
> `σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)`.

Mathematically: the positive divisors of `n` partition into (a) those **not**
divisible by `p` (whose `k`-th powers sum to `σ^p_k(n) = sigmaP p k n`) and
(b) those divisible by `p`. The map `e ↦ p·e` is a bijection from the divisors
of `n/p` onto the `p`-divisible divisors of `n` (using `p ∣ n`), and
`(p·e)^k = p^k·e^k`, so the `p`-divisible part sums to `p^k·σ_k(n/p)`. Adding the
two parts recovers `Σ_{d∣n} d^k = σ_k(n)`. Equivalently `σ^p_k(n) = σ_k(n) −
p^k·σ_k(n/p)`: this is the **subtraction-free** form of the recursion that says
"deleting the `p`-Euler factor of `σ_k`" gives the `n`-th Fourier coefficient of
the p-stabilised Eisenstein series `E_k^{(p)} = E_k − p^{k−1}E_k(p·)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[hp : Fact p.Prime]` (section `variable`). **Primality is used
  only weakly** — via `hp.out.pos` (`0 < p`) to run `Nat.mul_div_cancel_left`,
  `mul_dvd_mul_iff_left`, etc. The combinatorial identity is true for **any
  `p ≥ 1`** (or even any `m` with the filter `¬ m ∣ d`); only `0 < p` is needed,
  not irreducibility. (`hp` is ambient from the section; the *sum* and the
  *bijection* never use primality.)
- `k : ℕ` — the exponent on each divisor.
- `n : ℕ` — the argument whose divisors are summed.

Hypotheses (Lean side):
- `hn : (p : ℕ) ∣ n` — `p` divides `n` (so the `p·(·)` reindexing onto `(n/p)`'s divisors is a bijection; **essential** — false when `p ∤ n`, where the sibling `sigmaP_eq_of_not_dvd` applies instead).
- `hn0 : n ≠ 0` — `n` is nonzero (so `n.divisors` is the honest divisor set; **essential** — `Nat.divisors 0 = ∅`).

Conclusion (math): `σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)`.

Conclusion (Lean): `sigmaP p k n + p ^ k * ArithmeticFunction.sigma k (n / p) = ArithmeticFunction.sigma k n`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (borderline, leaning small).

Reason: it is a clean, recognisable *number-theoretic identity* about the divisor
power sum (which nudges toward BIG), but it is **not** the project's headline
result (the docstring's main results are the q-expansion `HasSum`
theorems `hasSum_rjwEisenstein` / `hasSum_stabilisedEisenstein` and the
`Γ₀(p)`-modular form `stabilisedEisenstein`; this lemma is the *arithmetic engine*
feeding the coefficient identity), it introduces **no new structure** (no class,
topology, measurability, or universal property), and it is **not** named after a
person/place. It is a one-result divisor-splitting fact. Classed SMALL.

(Note: literature width was EXHAUSTIVE regardless — all nine channels ran. BIG/SMALL
is recorded for framing only and did not gate Phase 3.)

### One-line check (Phase 2b)

Body line count: **~27 substantive lines** (a `have hcompl : … = p^k·σ_k(n/p)`
sub-proof via `Finset.sum_nbij'` with five `?_` obligations, then `rw [sigmaP,
← hcompl, sigma_apply]` + `exact Finset.sum_filter_not_add_sum_filter …`).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the Phase 2b
def-exemption table — defeq-abuse / diamond-avoidance / API-stability — applies
only to definitions). Recorded as a one-line note and skipped. (The proof is well
over any one-liner threshold anyway: it contains a real combinatorial bijection,
not a wrapper.)

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

The concept assessed is the **divisor-splitting / `σ`-recursion identity**
`σ_k(n) = σ^p_k(n) + p^k·σ_k(n/p)` (for `p ∣ n`), i.e. the relation expressing the
prime-to-`p` divisor sum as `σ_k` with its `p`-Euler factor deleted. Searched at
three generality levels (the specific p-stabilisation form, the general
σ-recursion/Euler-factor form, the p-stabilised-Eisenstein-coefficient form) plus
the categorical / alg-geom / community / arXiv channels.

### Literature search table

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "divisor power sum identity σ_k(n) = prime-to-p part + p^k σ_k(n/p) p-stabilization Eisenstein recursion" | partial | the *operation* (`E*=E−p^{κ−1}E(p·)`) and the σ-multiplicativity are standard; the literal identity is a derived rearrangement | Hits: Kawamura "semi-ordinary p-stabilization of Siegel Eisenstein" (arXiv 1207.0198 / 2302.13009), Wolfram "Divisor Function", "Stability of p-adic valuations of Hecke L-values" (2308.15051), Lahiri-problem recursion (arXiv 0903.1743). Each *uses* the prime-to-`p` coefficient and the deletion relation; **none isolates it as a named theorem.** |
|  2 | WebSearch (general σ-recursion / Euler factor) | "sigma_k function recursion divisors split p divides n prime to p divisor sum Euler factor" | **yes** | the classical two-term σ-recursion: "if `p ∣ N` and `s>0` then `σ_s(N) = σ_s(N)σ_s(p) − p^s σ_s(N/p)`-type"; multiplicativity `σ_s(N)=∏_{p^α∥N}σ_s(p^α)`; Euler factor `σ_a(p^r)=(p^{a(r+1)}−1)/(p^a−1)` | **NumberWorld "Sum of Divisors — Euler's recursion"**, **Wolfram MathWorld "Divisor Function"**, Mauricio Poppe NT notes, cp-algorithms "Number/sum of divisors". The σ-recursion is universal and elementary; the *prime-to-`p` restricted* phrasing `σ_k(n)=σ^p_k(n)+p^k σ_k(n/p)` is a one-line rearrangement of it, **not** separately named. |
|  3 | WebSearch (p-stabilised Eisenstein coefficient) | "p-stabilized Eisenstein series Fourier coefficient σ_{k-1}(n) − p^{k-1}σ_{k-1}(n/p) prime to p divisors" | **yes** | `E*_{κ,χ}(z) := E_{κ,χ}(z) − χ(p)p^{κ−1}E_{κ,χ}(pz)`, with coefficient `σ^{{p}}_{κ−1,χ}(m) := Σ_{0<d∣m, gcd(d,p)=1} χ(d)d^{κ−1}` (divisors **prime to `p`**) | **Kawamura arXiv 1207.0198 / 2302.13009** (explicit Fourier coefficients of the p-stabilisation); emergentmind "Fourier coefficients of Hilbert–Eisenstein series"; 2308.15051. This is *exactly* the project's object: `σ^{{p}}=sigmaP`, and the project's identity is the relation linking `E*`'s coefficient to `σ_k` and `σ_k(·/p)`. Introduced **per-paper with local notation `σ^{{p}}` / `σ^{(p)}` / `σ'`**, never a library lemma. |
|  4 | ChatGPT MCP                      | (intended: "standard name + statement of the prime-to-`p` divisor-sum recursion `σ_k(n)=σ^p_k(n)+p^k σ_k(n/p)`; is it a named identity?") | **n/a** | — | **MCP not configured in this session.** Consistent with the sibling reports (`sigmaP.md`, `isUnit_two_padicInt.md`): the `chatgpt-math` server points at a different machine (`/home/chris/.claude/mcp-servers/…`, *Failed to connect*). Substituted with the extra generality-stratified WebSearch passes (#2, #3) + the arXiv channel (#10), per the skill's absent-channel fallback. Recorded `n/a` with reason. |
|  5 | Local references                 | `.mathlib-quality/references/` (PadicLFunctions); `refs/PadicLFunctions/` symlink | **n/a** | — | No `references/` directory under `projects/PadicLFunctions/.mathlib-quality/` (confirmed: `ls` → only `overview/`); no `refs/` symlink in this checkout (reference PDFs are LOCAL-ONLY, not populated here). The RJW source itself is quoted in-file: the docstring cites **RJW TeX 2390–2393** calling this the *"easy check"* and writing the identity in **subtraction-free form** — i.e. the source treats it as a routine verification, not a named result. Recorded `n/a` (dir absent) with the in-file source content noted. |
|  6 | nLab                             | `divisor function` / `Eisenstein series` (covered by #2/#3 web sweep) | **n/a** | — | nLab has **no** "divisor function" page (sibling `sigmaP.md` confirmed `ncatlab.org/nlab/show/divisor+function` → HTTP 404); its "Eisenstein series" content is the modular-forms/automorphic picture, not elementary divisor-sum recursions. The identity is elementary multiplicative NT, out of nLab's categorical scope. Recorded `n/a — not on nLab`. |
|  7 | nCatLab (if categorical)         | — | **n/a** | — | Not a categorical statement (a finite-sum equality proved by a divisor-set bijection). No universal property, no functoriality. `n/a — not categorical`. |
|  8 | Stacks Project (if alg geom)     | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic statement. Stacks has no analytic-NT divisor-function recursion material. `n/a — not alg-geom`. |
|  9 | MathOverflow / Math.StackExchange| "sum of divisors coprime to p formula σ minus p^k σ(n/p)" | yes (as a manipulation) | community/textbook answers reproduce the σ-recursion and the "delete the `p`-Euler factor" picture; LibreTexts (Raji) "Multiplicative Number Theoretic Functions" gives the multiplicativity + prime-power formula the rearrangement rests on | Wikipedia "Divisor function", "Unitary divisor"; LibreTexts Raji Ch.4; cp-algorithms. The prime-to-`p` recursion is recognised as routine bookkeeping (`σ^p_k(n)=∏_{q^e∥n, q≠p}(1+q^k+…)`), **never a named identity.** Not separately tabulated beyond #2 (would duplicate). |
| 10 | recent arXiv (last 5 years)      | "p-stabilization Eisenstein Fourier coefficient prime to p" (1207.0198/2302.13009, 2308.15051) | yes (as a per-paper device) | each paper introduces its own `σ^{{p}}` / `σ^{(p)}` and the deletion relation inline; Kawamura's 2023 update (2302.13009) gives the explicit p-stabilised coefficients | Confirms the modern literature still introduces this identity **ad hoc, per paper, with local notation** — there is no settled named "prime-to-`p` σ-recursion". Strong signal that it is a *construction-internal* lemma, not a library primitive. |

Protocol pass check:
- WebSearch ran **3 distinct queries at different generality levels** (specific p-stabilisation identity #1; general σ-recursion / Euler-factor form #2; p-stabilised-Eisenstein-coefficient form #3) — ✓.
- ChatGPT MCP: not available; substituted with extra WebSearch + arXiv, reason recorded — handled per the skill's fallback.
- Local references checked (`n/a`, dir absent; in-file RJW source content recorded) — ✓.
- nLab checked (no page; recorded) — ✓.
- Stacks / nCatLab / MathOverflow / arXiv each checked or `n/a` with reason — ✓.

### Literature summary (Phase 3)

Concept identified as: the **divisor-splitting / Euler-factor-deletion recursion**
for the divisor power sum — `σ_k(n) = σ^p_k(n) + p^k·σ_k(n/p)` for `p ∣ n`,
equivalently `σ^p_k(n) = σ_k(n) − p^k σ_k(n/p)` — the relation that exhibits the
prime-to-`p` divisor sum `σ^p_k = sigmaP` (the `n`-th Fourier coefficient of the
p-stabilised Eisenstein series) as `σ_k` with its `p`-Euler factor removed.

Sources agree on the standard form: **the *underlying* facts are standard; the
*identity as stated* has no canonical name.** What *is* standard and universal is
(a) the σ-recursion / multiplicativity `σ_k(p^a m) = σ_k(p^a)σ_k(m)`,
`σ_k(p^r)=(p^{k(r+1)}−1)/(p^k−1)` (Wolfram, NumberWorld, LibreTexts — elementary),
and (b) the p-stabilisation operation `E*=E−p^{κ−1}E(p·)` with prime-to-`p`
coefficient `σ^{{p}}` (Kawamura 1207.0198/2302.13009 — the canonical reference for
the *explicit* p-stabilised coefficients). The project's identity is the
**one-line rearrangement** linking (a) and (b); the literature derives it inline,
per source, with per-author notation, and never elevates it to a named theorem.

Most general standard form: the **fully general statement** is the
Euler-factor-deletion law for an arbitrary multiplicative function — for `f`
multiplicative and `p ∣ n`, the sum over divisors coprime to `p` equals `f`-sum
minus the `p`-part, which mathlib's `IsMultiplicative` / Dirichlet-convolution
framework is built to express. The `f = (·)^k`, single-prime `p` instance is the
project's `sigmaP_add_pow_mul_sigma_div`.

Generality dimensions where the literature varies:
- **The deletion modulus**: a *single prime* `p` (the user's form) → a general
  modulus `m` (`gcd(d,m)=1`). The coprime-to-`m` form is the more general standard
  manipulation; the prime case is the p-stabilisation special case.
- **The summand**: the specific `d^k` (the user's form) → an arbitrary
  multiplicative function `f` (the general Euler-factor-deletion law). Mathlib's
  `ArithmeticFunction`/`IsMultiplicative` framework is built precisely for the
  latter.
- **A character twist**: Kawamura's `σ^{{p}}_{κ−1,χ}` carries a Dirichlet
  character `χ`; the project's untwisted `σ^p_k` is the `χ = 1` case.
- **Notation**: no consensus — `σ^{{p}}`, `σ^{(p)}`, `σ'`, all per-paper.

Disagreement with the literature: not a *disagreement* but the **same "absence"
that drives the subject `sigmaP`'s verdict** — the identity is correct and
recurrent, but treated as a derived, construction-local rearrangement rather than
a primitive worth its own name. **This lemma's status is therefore tied to
`sigmaP`'s**: it is a statement *about* an object whose own mathlib home and
generality are undecided.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): there is no *named* standard identity;
the most general *standard manipulation* is the **Euler-factor-deletion law for a
multiplicative function**, `Σ_{d∣n, gcd(d,m)=1} f d = (f-sum) − (p-part)`. The
`sigmaP_add_pow_mul_sigma_div` form fixes `f = (·)^k`, `m = p` prime, `χ = 1`.

### Generality status table (Phase 4a) — `sigmaP_add_pow_mul_sigma_div`

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[Fact p.Prime]` (ambient) | `p` prime | the recursion needs only `0 < p` (the divisor-set bijection `e ↦ p·e`) — **primality is irrelevant** | **yes** | The proof uses `hp` only through `hp.out.pos : 0 < p`; no step uses irreducibility. The identity holds for any `p ≥ 1` (the `p`-divisible divisors are `p·(divisors of n/p)` whenever `p ∣ n`, `p > 0`). Dropping `[Fact p.Prime]` to a bare `0 < p` (or `p ≠ 0`) is free. **But** the *subject* `sigmaP` carries the same unused `[Fact p.Prime]`, so this weakening is governed by the `sigmaP` decision, not independently. |
| 2 | the prime `p` | a single prime `p` | a general modulus `m` with the prime-to-`m` part | **partly** | For a composite modulus `m` the clean two-term identity `σ^m_k(n)=σ_k(n)−m^k σ_k(n/m)` **fails** (deleting "not coprime to `m`" is not the same as deleting one `m`-factor; needs inclusion–exclusion over the primes of `m`). So the *prime* case is genuinely the clean one. Generalising to `m` requires a *different* (inclusion–exclusion) statement, not a mechanical weakening. |
| 3 | the summand `d ^ k` | the monomial `(·)^k` | an arbitrary multiplicative `f` | **yes (but a different statement)** | The Euler-factor-deletion law for multiplicative `f` and prime `p`: `Σ_{d∣n,p∤d} f d = (Σ_{d∣n} f d) − f(p)·(Σ_{e∣n/p} f e)` holds when `f` is *completely* multiplicative on the `p`-power (so `f(p·e)=f(p)f(e)`); for `f=(·)^k`, `f(p)=p^k`. Generalising the summand turns this into a lemma about `ArithmeticFunction`s — the **Bourbaki-2.0 target** (see 4c), and the natural companion of `sigmaP`'s T2. |
| 4 | character twist | untwisted (`χ=1`) | Kawamura's `σ^{{p}}_{k,χ}` with a Dirichlet `χ` | **yes** | Adding a character `χ` (`f = χ·(·)^k`) recovers Kawamura's exact coefficient; the project only needs the untwisted case. CHEAP as a statement, but again only meaningful relative to a chosen `sigmaP`(`χ`) form. |
| 5 | codomain `ℕ` | `ℕ` | a commutative (semi)ring `R` | **yes** | The identity is true over any `[CommSemiring R]` after casting; the project immediately casts the whole identity into `ℂ` (`congrArg (Nat.cast (R:=ℂ)) …` at `EisensteinComplex.lean:244`) and `push_cast`es. An `R`-valued statement removes that cast. Tied to whether `sigmaP` becomes `R`-valued. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (on **five** axes: the
unused prime hypothesis above `0 < p`; prime `p` vs. a modulus `m` — *but only via
inclusion–exclusion*; the `(·)^k` summand vs. a general multiplicative `f`; the
missing character twist; `ℕ` vs. a general ring).

Number of weakening opportunities found: **K = 5** (axes 1–5).

Proposed restatement — **every restatement is downstream of the `sigmaP`
decision** (the LHS *is* `sigmaP p k n`), so the targets mirror `sigmaP`'s:

- **(T1) Minimal, faithful generalisation** — drop the prime hypothesis to `0 < p`,
  keep the `σ`/`sigmaP`-shape:
  ```lean
  theorem sigmaCoprime_add_pow_mul_sigma_div {p : ℕ} (hp : 0 < p) {n : ℕ}
      (hn : p ∣ n) (hn0 : n ≠ 0) (k : ℕ) :
      sigmaCoprime p k n + p ^ k * ArithmeticFunction.sigma k (n / p)
        = ArithmeticFunction.sigma k n
  ```
  (with `sigmaCoprime` = the de-primed `sigmaP`, `sigmaP`'s own T1.)
- **(T2) Bourbaki-2.0, structural** — the **Euler-factor-deletion lemma** for a
  multiplicative `ArithmeticFunction`, of which this is the `f = (·)^k` instance
  (see Phase 4c). This is the natural companion API of `sigmaP`'s `restrictCoprime`
  operator.

Cost of restatement: **CHEAP→MODERATE for the lemma** (T1 is a mechanical
`0<p`-for-`prime` swap; T2's Euler-factor-deletion lemma is real but small API on
top of `isMultiplicative_sigma` / `IsMultiplicative.map_mul_of_coprime`). Per the
skill, EXPENSIVE-would-not-downgrade — but here it is at most MODERATE.

→ STRICTLY NARROWER → Phase 7 considers **YES-but-generalise-first** *and*
BORDERLINE. **It lands on BORDERLINE because the choice of target is not free**:
the LHS is `sigmaP`, whose own form is undecided, so this lemma inherits the
"which generality / name it at all?" judgment from its subject.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses? | **partial** | drop the ambient `[Fact p.Prime]` to a `0 < p` hypothesis (primality is unused beyond positivity) | removes a spurious typeclass; lets the identity be used at any `p ≥ 1` |
|  2 | sequences/metric → filters/topological? | **no** | — | a finite-sum equality; no limit/topology |
|  3 | construct an object → universal-property class? | **no** | — | a property, not a construction |
|  4 | set-with-closure-predicate → bundled type? | **no** | — | no substructure content |
|  5 | concrete `ℕ`-valued → mathlib typeclass weakening? | **yes** | state it `R`-valued (cast the identity over `[CommSemiring R]`) so it composes with the project's `ℂ`-cast at the use site, and with `ζ`/`σ` valued in `R` | removes the `congrArg (Nat.cast (R:=ℂ))` + `push_cast` plumbing at `EisensteinComplex.lean:244` |
|  6 | 1-categorical → higher-categorical? | **no** | — | none |
|  7 | concrete index / number-specific → arbitrary structure? | **yes** | generalise the *summand* `(·)^k` → an arbitrary multiplicative `f : ArithmeticFunction R`, giving the **Euler-factor-deletion lemma**: for `f` multiplicative (and `f(p·e)=f(p)f(e)`), `p ∣ n`, `(restrictCoprime p f) n = f n − f p · f(n/p)` — i.e. *"deleting the `p`-Euler factor"* as a lemma about arithmetic functions | the lemma specialises to `sigmaP_add_pow_mul_sigma_div`, to the prime-to-`p` part of *any* multiplicative function (μ, τ, σ_k, von Mangoldt), and dovetails with `isMultiplicative_sigma`, `IsMultiplicative.map_mul_of_coprime`, `sigma_apply_prime_pow`, and the project's hypothetical `ArithmeticFunction.restrictCoprime` (Phase 4c of `sigmaP.md`) |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and, as for `sigmaP`, it is part of the crux.**
- Proposed mathlib-idiomatic restatement (T2): the **Euler-factor-deletion
  lemma** companion to `sigmaP`'s `restrictCoprime` operator,
  ```lean
  /-- Deleting the `p`-Euler factor: for `f` multiplicative with `f(p·e)=f(p)·f(e)`
  and `p ∣ n` (`n≠0`), the coprime-to-`p` restriction is `f n − f p · f (n/p)`. -/
  theorem ArithmeticFunction.restrictCoprime_prime_add … :
      (restrictCoprime p f) n + f p * f (n / p) = f n := …
  -- sigmaP_add_pow_mul_sigma_div  is the  f = (·)^k  (so f p = p^k)  instance.
  ```
- Cost: **MODERATE** (the lemma is the same divisor-set bijection the project
  already wrote, lifted to a general multiplicative `f`; the `f(p·e)=f(p)f(e)`
  hypothesis is discharged by `IsMultiplicative` + coprimality of `p` and `e` —
  real but small API).
- Mathlib downstream this enables: gives mathlib the **p-stabilisation /
  Euler-factor-deletion recursion** the Iwasawa/Eisenstein literature keeps
  re-deriving (Kawamura et al.), as a first-class lemma; composes with
  `isMultiplicative_sigma`, `sigma_apply_prime_pow`, the Dirichlet-series /
  `LSeries` machinery; removes the project's `ℕ→ℂ` cast boilerplate.
- Real mathematical improvement (not just "looks cooler"): **plausibly yes** — it
  is the lemma that makes "the prime-to-`p` part of a multiplicative function"
  computable and is the engine of every p-stabilisation. **But** whether mathlib
  wants it (vs. users deriving the rearrangement inline from `isMultiplicative_sigma`),
  and in which form (prime-`p` two-term vs. modulus-`m` inclusion–exclusion;
  twisted vs. untwisted; bare `σ` vs. `ArithmeticFunction.restrictCoprime`), is —
  *exactly as for `sigmaP`* — a maintainer-taste decision the skill must not make
  alone.

So there is both a LITERATURE-WEAKENING target (T1, drop the unused prime
hypothesis) **and** a MODERN-IDIOM target (T2, the Euler-factor-deletion lemma).
Because the *choice between them* is governed by the still-open `sigmaP`
question (this lemma's LHS *is* `sigmaP`), Phase 7 lands on **BORDERLINE**, with
the generalisation directions captured as the candidate resolutions.

---

## PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`** (and every proposed restatement, T1/T2,
is also a `theorem`). No definitional equalities, no typeclass-search paths, no
instance/reducibility attributes are introduced by this lemma. (Any diamond/defeq
considerations live entirely with the *subject* `def sigmaP` — and that report
(`sigmaP.md`, Phase 4.5) found the subject's risk profile to be **NONE** as well.)
Phase 4.5 therefore adds **no constraint** to the verdict.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.sigmaP_add_pow_mul_sigma_div`

[A] **Lean-Finder** — n/a: the hosted Lean-Finder Space was not reachable as a
    scriptable endpoint in this session (consistent with the sibling reports).
    Substituted with grep (D) + name-pattern (E) + a full source read of
    `ArithmeticFunction/Misc.lean` (the `σ` home), `NumberTheory/Divisors.lean`,
    and `Algebra/BigOperators/Group/Finset/Basic.lean` (the partition lemma).

[B] **Loogle** (type-pattern) — queries run conceptually against the mathlib
    source (live endpoint not scriptable here):
    - `σ ?k ?n = _ + _ ^ _ * σ ?k (?n / _)` / `_ + _ = ArithmeticFunction.sigma _ _`
      → **no hit.** Mathlib has the σ-multiplicativity factorisation
      `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` (Misc.lean:206)
      and the prime-power formula `sigma_apply_prime_pow` (:165), but **no
      additive two-term recursion** `σ k n = σ^p_k(n) + p^k σ_k(n/p)`.
    - `∑ _ ∈ (Nat.divisors _).filter _, _` (the LHS `sigmaP`) → the only
      `divisors.filter` sums in mathlib NT are the **squarefree** filter
      (`Misc.lean:88`) and the **prime-power** filter (`VonMangoldt.lean:111`).
      **No coprime-to-`p` / `¬ p ∣ d` filtered divisor sum exists** (this is the
      `sigmaP.md` Phase-5 finding, re-confirmed).
    - `IsMultiplicative ?f → ?p ∣ ?n → _` → `IsMultiplicative.map_mul_of_coprime`
      (Misc.lean:~440), `Nat.Coprime.sum_divisors_mul` — these *factor* `σ(mn)`
      using coprimality of `m,n`; they do **not** give the prime-to-`p`-vs-`p`-part
      split for a *single* `n` divisible by `p`.

[C] **LeanSearch** (natural language) — queries "sum of k-th powers of divisors
    not divisible by p equals sigma minus p^k sigma n over p", "divisor function
    recursion delete prime Euler factor", "prime to p part of sigma function"
    (endpoint returned non-200 on the scripted call; resolved via D/E + source).
    Expected/actual hits: `sigma_apply`, `isMultiplicative_sigma`,
    `sigma_apply_prime_pow` — **no restricted/recursion divisor power sum lemma.**

[D] **Grep mathlib src** — over `.lake/packages/mathlib/Mathlib/`:
    - `sigmaP`, `sigma_prime_to`, `sigma_sub`, `sigma.*recursion`, `primeToP`,
      `restrictCoprime`, `sigmaCoprime`, `EulerFactor.*sigma` → **0 hits** anywhere.
    - `sum_filter_not_add_sum_filter` → the lemma the proof *uses* — it **is** in
      mathlib (`@[to_additive]` of `prod_filter_not_mul_prod_filter`,
      `Algebra/BigOperators/Group/Finset/Basic.lean:151`; used at
      `Combinatorics/Enumerative/InclusionExclusion.lean:175`). It is the **generic
      `Finset` partition tool** `Σ_{¬P}+Σ_P=Σ`, **not** a `σ` statement.
    - `sum_nbij'` (the proof's re-indexing bijection) → generic `BigOperators` API
      (`Group/Finset/Defs.lean:457`). Not `σ`-specific.
    - `divisors` ∩ (`p ∣ ·` split) → `map_div_right_divisors` (Divisors.lean:370),
      `divisors_filter_dvd_of_dvd` (:242), `divisors_prime_pow` (:424),
      `sum_divisors_prime_pow` (:520) — divisor-set manipulations, **none** giving
      the prime-to-`p`-power-sum recursion.
    - `sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul` (Misc.lean:206),
      `isMultiplicative_sigma` (:202): the **multiplicative** structure of `σ` —
      from which the recursion *can be derived*, but it is **not stated** as the
      additive two-term split.

[E] **Name-pattern** (`lean_local_search` proxy via grep) — terms `sigma`,
    `divisor`, `recursion`, `prime_to`, `coprime`, `Euler`, `_filter`, `_split`,
    `restrict` over the mathlib `ArithmeticFunction/`, `Divisors.lean`, `LSeries/`
    trees. Hits: the full unrestricted `σ` family (`sigma_apply`,
    `sigma_apply_prime_pow`, `sigma_eq_sum_div`, `isMultiplicative_sigma`,
    `sigma_mono`, `sigma_le_pow_succ`), the squarefree/prime-power filtered sums,
    and the multiplicative-factorisation coprime lemmas — **all about the
    unrestricted `σ` or generic divisor sets**; the **prime-to-`p` two-term
    recursion is absent under every name pattern.**

Searched for both:
- the user's current form (`σ^p_k(n) + p^k·σ_k(n/p) = σ_k(n)`) — **not in mathlib**;
- the literature-standard / more-general forms (the σ-multiplicativity *recursion*
  in additive split form; the Euler-factor-deletion lemma for a multiplicative
  `f`; the coprime-to-`m` inclusion–exclusion version) — **also not in mathlib** as
  a stated lemma. Mathlib has the **parent** `ArithmeticFunction.sigma`, its
  **multiplicativity** (`isMultiplicative_sigma`) and **prime-power formula**
  (`sigma_apply_prime_pow`), and the **generic partition/bijection tools**
  (`sum_filter_not_add_sum_filter`, `sum_nbij'`) the proof *assembles* — but **not**
  the assembled identity.

Concluded: **not in mathlib** (all five methods exhausted, plus the
literature-standard general forms). Mathlib has the *ingredients* (the σ object,
its multiplicativity, the generic Finset partition + bijection lemmas) but **not**
the prime-to-`p` divisor-sum recursion in any form.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `sigmaP_add_pow_mul_sigma_div`

Internal use count: **K = 1 occurrence outside the declaring `section`** (and 0
elsewhere in the repo). The single external-to-section caller is in the **same
file**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `EisensteinComplex.lean:244` | `have := congrArg (Nat.cast (R := ℂ)) (sigmaP_add_pow_mul_sigma_div p hdvd hn0 (k - 1))` — inside `hasSum_stabilisedEisenstein`, the `p ∣ n` branch of `hfun`, to rewrite the stabilised coefficient `stabilisedCoeff p k n` (which is `sigmaP p (k−1) n` for `n≠0`) against the `ℂ`-cast q-expansion `b n·qⁿ − p^{k−1}·g n`. |

Inline-derivation grep (was the equivalent re-derived without the lemma?): **none**
— the identity appears exactly once, through this named lemma. (Its `p ∤ n` sibling
`sigmaP_eq_of_not_dvd` handles the complementary branch at `EisensteinComplex.lean:249`.)

Call-sites signal (Phase 6.0.1): **K = 1 internal use, single file.** Per the
verdicts-doc call-site table, `K = 1` is the **"possibly wrong abstraction / could
be inlined"** band — leaning toward NO-composable *if* the body were a trivial
composition. **But here the body is a genuine ~27-line bijection proof, not an
inline-able composition** (see below), so the low call count does *not* push to
NO-composable; instead it confirms the lemma is a **single-use construction-internal
step** — which, combined with its subject `sigmaP`'s undecided status, is precisely
the *ambiguous* profile that makes the verdict BORDERLINE rather than a confident
YES (load-bearing multi-file API) or NO (trivial wrapper).

### Composition check (Phase 6)

Can `sigmaP_add_pow_mul_sigma_div` be **proved** from mathlib in ≤3 chained calls?

Attempt 1 — from σ-multiplicativity (`isMultiplicative_sigma`) + the prime-power
formula:
```lean
-- idea: factor n = p^a · m with p ∤ m, use σ k n = σ k (p^a) · σ k m and
--       σ k (n/p) = σ k (p^{a-1}) · σ k m, and σ^p_k(n) = (σ k (p^a) − p^k σ k (p^{a-1}))·σ k m
```
  - Mathlib decls used: `isMultiplicative_sigma`, `sigma_apply_prime_pow`,
    `Nat.factorization`, `Nat.ord_compl`/`ord_proj`, `IsMultiplicative.map_mul_of_coprime`.
  - Result: **fails as a ≤3-call composition.** This is a *real multi-step proof*:
    one must (i) write `n = p^a·m` with `p ∤ m` (`Nat.ord_proj_mul_ord_compl_eq_self`),
    (ii) prove `sigmaP p k n = (σ_k(p^a) − p^k σ_k(p^{a−1}))·σ_k(m)` (itself a
    multiplicativity-of-the-restricted-sum argument — and `sigmaP`'s
    multiplicativity is **not in mathlib**), (iii) reassemble. Far more than 3
    calls, and needs the (absent) multiplicativity of `sigmaP`. Not a composition.

Attempt 2 — the project's actual proof, via the generic partition + bijection:
```lean
-- Σ_{p∣d} d^k = p^k·σ_k(n/p)  by  Finset.sum_nbij' (d↦d/p) (e↦p·e) …   [5 obligations]
-- then  sigmaP + (p-part) = σ_k n  by  Finset.sum_filter_not_add_sum_filter
```
  - Mathlib decls used: `Finset.sum_nbij'`, `Finset.sum_filter_not_add_sum_filter`,
    `ArithmeticFunction.sigma_apply`, `Finset.mul_sum`, plus ~8 `Nat`/divisibility
    lemmas to discharge the bijection's four membership/inverse obligations and the
    value equality `d^k = p^k·(d/p)^k`.
  - Result: this **is** the proof — and it is a **~27-line argument with a
    five-field `Finset.sum_nbij'` bijection**, not a 1–3-call glue. The
    `sum_filter_not_add_sum_filter` step alone is *generic* (it only partitions);
    all the *content* is in establishing the `p`-divisible part equals
    `p^k·σ_k(n/p)`, which is the bijection. **This is a proof, not a composition.**

Conclusion: **NOT-COMPOSABLE.** Neither route gives the identity in ≤3 mathlib
calls: the multiplicativity route needs the (absent) multiplicativity of the
restricted sum and `n = p^a·m` bookkeeping; the direct route *is* a genuine
re-indexing-bijection proof. Per the verdicts doc ("if the composition is more
than 3 mathlib calls, or requires real rewriting to glue, it's a proof, not a
composition — the lemma is justified"), this is **not** `NO-composable-from-mathlib`.

---

## Verdict: `sigmaP_add_pow_mul_sigma_div`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the *ingredients* are standard — the σ-recursion /
  multiplicativity (Wolfram, NumberWorld, LibreTexts) and the p-stabilisation
  operation `E*=E−p^{κ−1}E(p·)` with prime-to-`p` coefficient `σ^{{p}}` (Kawamura
  arXiv 1207.0198/2302.13009) — but the **identity as stated has no canonical
  name**; it is the one-line, per-paper rearrangement linking them. ≥3 channels
  (WebSearch ×3 + arXiv + MathOverflow/LibreTexts) agree on the *absence of a
  named object*, exactly as for the subject `sigmaP`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** on 5 axes
  (unused prime hypothesis above `0<p`; prime `p` vs. modulus `m` — *only via
  inclusion–exclusion*; `(·)^k` vs. multiplicative `f`; untwisted vs. `χ`-twisted;
  `ℕ` vs. ring `R`). Phase 4c surfaces a genuine MODERN-IDIOM target (the
  Euler-factor-deletion lemma companion to `sigmaP`'s `restrictCoprime`) **and** a
  minimal T1 — but **the LHS is `sigmaP`, so the target is not freely choosable.**
- Diamond/defeq risk (Phase 4.5): **n/a** (`theorem`) — adds no constraint.
- Mathlib search (Phase 5): **not in mathlib** under any form; mathlib has the
  parent `ArithmeticFunction.sigma`, its multiplicativity/prime-power API, and the
  generic partition/bijection tools the proof assembles, but **not** the prime-to-`p`
  recursion.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~27-line
  `Finset.sum_nbij'` bijection proof; neither the multiplicativity route nor the
  direct route is a ≤3-call glue. Call sites: **K = 1, single file** — the
  *single-use construction-internal* profile.

**Rationale (1–2 paragraphs):**

`sigmaP_add_pow_mul_sigma_div` is a *correct, recurring, non-trivial, but un-named*
arithmetic identity: the recursion that exhibits the prime-to-`p` divisor power sum
`σ^p_k = sigmaP` as `σ_k` with its `p`-Euler factor deleted — equivalently, the
relation that gives the `n`-th Fourier coefficient of the p-stabilised Eisenstein
series. Mathlib genuinely lacks it (Phase 5), and it is **not** a clean composition
of mathlib lemmas (Phase 6 — it is a real divisor-set re-indexing bijection; the
multiplicativity route needs the absent multiplicativity of the restricted sum). So
it is **not** `NO-mathlib-has-it` and **not** `NO-composable-from-mathlib`. It is
also **not** a confident YES, for two converging reasons: (i) Phase 4b is STRICTLY
NARROWER (the gate forbids `YES-add-as-is`), and (ii) — decisively — **this lemma
is stated *about* `sigmaP`, whose own `/mathlibable` verdict is
`BORDERLINE-needs-human`**: its LHS *is* `sigmaP p k n`, so its final mathlib form,
its generality (bare `σ`/`sigmaP` vs. coprime-to-`m` vs. an
`ArithmeticFunction.restrictCoprime` / Euler-factor-deletion lemma), and even
whether it belongs in mathlib *at all* are all **contingent on the unresolved
`sigmaP` decision**. A characterising lemma cannot be more mathlib-ready than the
object it characterises.

This is therefore not a self-resolving `YES-but-generalise-first`: that bucket
requires a *single* well-defined restatement target, but here the target is pinned
to whatever `sigmaP` becomes (and `sigmaP` itself is BORDERLINE among three
materially-different forms). Per the verdicts doc's **re-aim rule**, a dependent
lemma blanket-inherits NO *only* when the parent is `NO-composable`/`BORDERLINE`
**with a mathlib `D'` to re-aim at** — but `sigmaP`'s BORDERLINE has **no** mathlib
`D'` (mathlib has only the *unrestricted* `σ`, against which this *additive split*
is precisely the new content). So there is nothing to re-aim at, and the honest
verdict is the **inherited BORDERLINE**: resolve `sigmaP` first, and this lemma's
verdict follows in lockstep. Per the skill, cost is **not** the blocker (T1/T2 are
CHEAP/MODERATE) — the blocker is the genuine mathematical *taste/policy* call
already owned by `sigmaP`.

**Numbered questions (≤5):**

  1. **Resolve `sigmaP` first.** This lemma's verdict is downstream of the subject
     `def sigmaP`. What is the decision for `sigmaP` (mathlib-or-local; which
     generality — bare prime-to-`p` `Finset.sum` `sigmaCoprime` vs. coprime-to-`m`
     vs. `ArithmeticFunction.restrictCoprime`; `ArithmeticFunction`-valued vs. bare
     function)? This lemma should be restated *against that chosen form*.
  2. **If `sigmaP` stays project-local** → drop this lemma from mathlib
     consideration too; keep it as the project-local arithmetic engine (the name +
     RJW docstring are fine). Confirm?
  3. **If `sigmaP` goes to mathlib, ship this recursion with it?** The identity is
     the *defining property* that makes the prime-to-`p` sum usable — should
     `sigmaP_add_pow_mul_sigma_div` (and its `p ∤ n` sibling `sigmaP_eq_of_not_dvd`)
     ship in the same PR as `sigmaP`'s core API, restated in the chosen generality?
  4. **Which form of the recursion?** (a) the minimal two-term prime-`p` form
     `σ^p_k(n)+p^k σ_k(n/p)=σ_k(n)` (drop `[Fact p.Prime]` to `0<p`), or (b) the
     Bourbaki-2.0 **Euler-factor-deletion lemma** for a multiplicative
     `ArithmeticFunction f` (`(restrictCoprime p f) n + f p · f(n/p) = f n`), of
     which (a) is the `f=(·)^k` instance? (b) is the more reusable mathlib form and
     the companion of `sigmaP`'s T2. (Note: the *composite-modulus* `m` version is
     **not** a mechanical generalisation — it needs inclusion–exclusion — so it is
     a separate, larger contribution.)
  5. **Twist?** Should the mathlib form carry a Dirichlet character `χ` (matching
     Kawamura's `σ^{{p}}_{k,χ}` and the broader Iwasawa application), or is the
     untwisted `χ=1` form the right grain for a first contribution?

Next action: **resolve `sigmaP.md`'s five Phase-7 questions first**, then re-run
`/mathlibable sigmaP_add_pow_mul_sigma_div` with the chosen `sigmaP` form in hand —
or, once a target is fixed, `/generalise sigmaP_add_pow_mul_sigma_div` against it.
Likely outcomes, mirroring `sigmaP`:
  - **`sigmaP` local (Q1/Q2)** → drop this lemma from mathlib consideration; keep
    project-local.
  - **`sigmaP` → mathlib, minimal T1 (Q4=a)** → `YES-but-generalise-first`, target
    `sigmaCoprime_add_pow_mul_sigma_div` (prime hypothesis relaxed to `0<p`),
    shipped alongside `sigmaCoprime` and `sigmaCoprime_eq_of_not_dvd`, into
    `Mathlib/NumberTheory/ArithmeticFunction/`.
  - **`sigmaP` → mathlib, structural T2 (Q4=b)** → `YES-but-generalise-first` with
    reason MODERN-IDIOM, target the **Euler-factor-deletion lemma** for
    multiplicative `ArithmeticFunction`s — the contemporary mathlib form of the
    p-stabilisation recursion — with this `sigmaP` identity as its `f=(·)^k` corollary.

---

## Next step

Resolve the **subject** `PadicLFunctions.sigmaP` first (its `/mathlibable` verdict
is `BORDERLINE-needs-human`; see
`projects/PadicLFunctions/.mathlib-quality/overview/mathlibable/PadicLFunctions.sigmaP.md`,
five Phase-7 questions). Because this lemma's LHS *is* `sigmaP`, its verdict
follows in lockstep: once `sigmaP`'s mathlib-or-local / generality / valued-form
decision is made, re-run `/mathlibable sigmaP_add_pow_mul_sigma_div` (or
`/generalise` it) against that chosen form — landing on `YES-but-generalise-first`
(if mathlib-bound, restated as the two-term `0<p` form or, better, the
Euler-factor-deletion lemma for multiplicative arithmetic functions, shipped with
`sigmaP`'s core API) or dropped from mathlib consideration (if `sigmaP` is kept
project-local). Do **not** upstream the `[Fact p.Prime]`-burdened, `ℕ`-valued,
single-prime form in isolation: it is the characterising recursion of an object
(`sigmaP`) whose own mathlib home is undecided, the prime hypothesis is unused
beyond `0 < p`, and the literature's reusable form is the Euler-factor-deletion law
for a general multiplicative function.
