# `/mathlibable` report — `PadicLFunctions.sub_one_mul_padicValNat_succ_le`

**Final verdict: `YES-but-generalise-first`.** The inequality
`(p−1)·v_p(n+1) ≤ n` is a genuine elementary gap in mathlib's `padicValNat`
API — mathlib has only `padicValNat_le_nat_log` (`v_p(n) ≤ log_p n`) for a
plain integer, and the whole `sub_one_mul_padicValNat_*` family is about
**factorials/binomials** (Legendre/Kummer), not single integers. The Lean
form is, however, **narrower than the natural mathlib statement** on two
mechanical axes (the `n+1` should be a plain `m`, and the `Fact p.Prime`
should weaken to `1 < p`). Generalise to `padicValNat`-of-a-single-`m` over
`1 < p`, then it is `YES-add-as-is`-grade. See Phase 7 for the restatement.

---

### Baseline (Phase 0)

- lake build:               build **not** re-run (per task note: stale/slow here); **reasoned from source**. The declaration and every dependency were read directly from the mathlib/project sources.
- decl `PadicLFunctions.sub_one_mul_padicValNat_succ_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:309`
- kind:                      theorem
- has sorry:                 no (self-contained proof, lines 309–321)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — defines `exp(x)=∑xⁿ/n!` / `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n`, proves convergence and isometry on the open ball `‖x‖ < p^{−1/(p−1)}`, and that `log` inverts `exp`. `sub_one_mul_padicValNat_succ_le` is the **valuation-growth estimate for the logarithm denominators**: `p^v ∣ n+1` plus Bernoulli gives `(p−1)·v_p(n+1) ≤ n`.

---

### Statement (Phase 1)

`sub_one_mul_padicValNat_succ_le` is a theorem stating the following:

> For a prime `p` and any natural number `n`, the `p`-adic valuation
> `v := v_p(n+1)` of the successor `n+1` satisfies the linear bound
> `(p−1)·v ≤ n`.

Equivalently, writing `m = n+1 ≥ 1`, this is `(p−1)·v_p(m) ≤ m−1`, i.e.
`v_p(m) ≤ (m−1)/(p−1)`. It is the integer-arithmetic, `Real.rpow`-free
sharpening of the textbook bound `v_p(m) ≤ log_p m`: where `log_p` only gives
`p^v ≤ m`, the Bernoulli inequality `p^v = (1+(p−1))^v ≥ 1 + v(p−1)` turns
`p^v ≤ m` into the *linear-in-`m`* estimate `1 + v(p−1) ≤ m`. This linear
form is precisely what powers the p-adic exp/log convergence radius
computations (the radius `p^{−1/(p−1)}` is the geometric statement of this
inequality).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the ambient prime. The proof uses only `hp.out.pos` / `hp.out.one_le` (i.e. `p ≥ 1`, more precisely `p ≥ 2` via the `-2 ≤ p−1` step); **primality is not actually needed** — `1 < p` suffices (see Phase 4).
- `(n : ℕ)` — the index; the lemma is about the successor `n+1`.
- The file's ambient `variable {L …} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` block is **not** in this lemma's signature — the statement is purely about `ℕ`.

Hypotheses (Lean side):
- none beyond `[Fact p.Prime]` and `(n : ℕ)`.

Conclusion (math): `(p−1)·v_p(n+1) ≤ n`.

Conclusion (Lean): `(p - 1) * padicValNat p (n + 1) ≤ n`.

Proof skeleton (lines 310–321): set `v := padicValNat p (n+1)`; `pow_padicValNat_dvd` + `Nat.le_of_dvd` give `p^v ≤ n+1`; `one_add_mul_le_pow (h2 : -2 ≤ (p:ℤ)−1) v` gives `1 + v(p−1) ≤ p^v` over `ℤ`; `linarith` closes `(p−1)v ≤ n`; `exact_mod_cast` back to `ℕ`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line elementary number-theoretic inequality used as an auxiliary denominator estimate; not a named theorem, not a project main result (the main results are `padicExp_add`, the isometry, and the exp/log inversion — this is plumbing for them).

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (For the record, the proof body is ~10 lines, not a one-liner.)

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic valuation inequality (p-1) v_p(n) ≤ n bound integer logarithm"                                  | partial | no *named* result; `v_p(σ(n)) ≤ ⌈log_p n⌉`-type bounds | confirms only the `log_p` family of bounds is "standard"; the `(p−1)v ≤ n−1` packaging is not named |
|  2 | WebSearch (general form / Bernoulli) | "p-adic valuation v_p(m) bound (p-1) v_p(m) less than m Bernoulli inequality p^v"                    | partial | a source states "`v_p(a(m)) > m/(p−1)`"-type bounds   | the `m/(p−1)` scale is exactly our bound; appears as auxiliary plumbing, not a named lemma |
|  3 | WebSearch (named-after / application) | "p-adic logarithm convergence radius valuation v_p(n) ≤ (n-1)/(p-1) ord_p denominator estimate"     | yes  | `1 ≤ p^{v_p(n)} ≤ n` ⇒ radius computations (MIT 18.785, UChicago REU/Strassman) | the estimate is the standard convergence-radius input for p-adic exp/log; stated inline, never named |
|  4 | WebSearch (mathlib-name)         | "mathlib Lean padicValNat le nat_log pow_log_le_self lemma valuation bound"                             | yes  | mathlib's `padicValNat_le_nat_log` (`v_p(n) ≤ log_p n`) | the ONLY plain-integer valuation upper bound mathlib ships; no `(p−1)`-multiplied form |
|  5 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the v_p(m) ≤ (m−1)/(p−1) estimate")   | n/a  | —                                                     | **n/a — ChatGPT MCP server present in config but unauthenticated** (`~/.claude/mcp-needs-auth-cache.json`; not in the live tool list), so not callable this session. Compensated with 4 WebSearch queries at distinct generality levels + Wikipedia + nLab. |
|  6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (directory absent)                                    | **n/a — no `references/` dir** for this project (only `overview/`); `refs/` is also absent in this checkout. Recorded as n/a per protocol. |
|  7 | nLab                             | `p-adic+exponential+map`                                                                                | n/a  | (page 404)                                            | nLab has no dedicated page; the p-adic exp/log is folklore-elementary, below nLab's abstraction threshold. |
|  8 | nCatLab (categorical)            | —                                                                                                       | n/a  | —                                                     | **n/a — not a categorical concept** (an arithmetic inequality on `ℕ`). |
|  9 | Stacks Project (alg geom)        | —                                                                                                       | n/a  | —                                                     | **n/a — not an algebraic-geometry concept**; Stacks has no elementary `padicVal` inequalities of this shape. |
| 10 | MathOverflow / Math.StackExchange | "p-adic valuation v_p(n) ≤ log_p(n) standard bound prime power dividing n"                             | yes  | `v_p(n) ≤ log_p n` ("follows from `n ≥ p^{v_p(n)}`") — Wikipedia *P-adic valuation* | the canonical reference statement; our linear `(p−1)v ≤ m−1` is the Bernoulli sharpening, not separately named |
| 11 | recent arXiv (last 5 yrs)        | "Bounds on the p-adic valuation of the factorial …" (arXiv:2408.00353) + Wolstenholme/harmonic-sum bounds | partial | factorial/harmonic-sum valuation bounds              | confirms current arXiv work on `v_p` bounds is about *factorials/special sequences*; the plain-integer `(p−1)v_p(m) ≤ m−1` is treated as trivial folklore, never the object of study |

#### Literature summary (Phase 3)

Concept identified as: the **elementary upper bound on the p-adic valuation of an integer** — canonically `v_p(m) ≤ log_p m` (Wikipedia, MathWorld, every p-adic-analysis course), and its Bernoulli-sharpened linear form `(p−1)·v_p(m) ≤ m−1` ⇔ `v_p(m) ≤ (m−1)/(p−1)`, which is the standard input to the **convergence radius of the p-adic exponential/logarithm** (Cassels §12, Washington §5.1, Koblitz, Neukirch; MIT 18.785 PSet, UChicago REU notes on Strassman's theorem).

Sources agree on the standard form: **yes** — the standard *named* statement is `v_p(m) ≤ log_p m` (Wikipedia, verbatim: "ν_p(n) ≤ log_p n … follows directly from n ≥ p^{ν_p(n)}"). The linear/`(p−1)`-scaled version is universally *used* but universally *unnamed* — it is treated as a one-line consequence.

Most general standard form: for any base `b ≥ 2` and `m ≥ 1`, `(b−1)·v_b(m) ≤ m−1` where `v_b` is the `b`-adic valuation. With `b` prime it is the p-adic case; primality is irrelevant to the inequality itself (only `b ≥ 2` matters, via Bernoulli on `b−1 ≥ 1`).

Generality dimensions where the literature varies:
  - **Index**: stated for a single integer `m ≥ 1`. The user's `n+1` is exactly `m ≥ 1` re-encoded as a successor — a *narrowing of presentation*, not of content.
  - **Base/primality**: the literature states it for a prime `p`, but the proof (and the most general true statement) needs only `p ≥ 2`. mathlib's `padicValNat_le_nat_log` already drops to `1 < b` implicitly via `Nat.log`.
  - **Form**: `≤ log_p m` (mathlib's current shape) vs. the linear `(p−1)v ≤ m−1` (sharper, `log`-free) — both standard; the linear one is what convergence proofs want.

Disagreement with the literature: **none**. The user's form is a correct, standard estimate; it is simply stated in the narrower `n+1` / `Fact p.Prime` presentation rather than the general `m ≥ 1` / `1 < p` one.

If the search returned nothing: it did not — but note the *named* result is `≤ log_p`, and the linear form is unnamed folklore. This pushes toward "real but small gap, state it in the general form", not toward a person-named theorem.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): for any `m ≥ 1` and base `b ≥ 2`, `(b−1)·v_b(m) ≤ m−1` (equivalently `v_b(m) ≤ (m−1)/(b−1)`).

#### Generality status table (Phase 4a)

| # | Parameter / hypothesis     | Current Lean form                       | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|-----------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `(n : ℕ)` via `(n + 1)`    | valuation of a **successor** `n+1`, bounded by `n` | valuation of any `m ≥ 1`, bounded by `m−1` | **yes** | The `n+1` encoding only exists to keep the RHS a clean `n` (no `Nat` subtraction). The general statement `1 ≤ m → (p−1)·v_p(m) ≤ m−1` is equally provable and strictly more applicable (consumers currently do `show (n−1)+1 = n` gymnastics, line 837, exactly because the lemma is in successor form). |
| 2 | `[hp : Fact p.Prime]`      | `p` prime                               | `b ≥ 2` (no primality)           | **yes** | Proof uses only `hp.out.pos` and `hp.out.one_le`; the Bernoulli step needs `−2 ≤ p−1` (i.e. `p ≥ 0`) and the `dvd`/`pow` step needs `p ≥ 1`. `padicValNat` is defined for any base. So `1 < p` (needed only so `v_p` is the genuine multiplicity, matching `padicValNat_le_nat_log`'s `Nat.log p` shape) suffices; `Fact p.Prime` is overkill. |
| 3 | conclusion in `ℕ`          | `(p - 1) * padicValNat p (n+1) ≤ n`     | same (ℕ is the right home)       | NO (already minimal) | ℕ is correct; no need for ℝ/ℤ. The internal `ℤ` cast in the proof is incidental. |

#### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **2** (successor-form index; primality hypothesis).

Proposed restatement:

```lean
theorem sub_one_mul_padicValNat_le {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    (p - 1) * padicValNat p m ≤ m - 1 := by
  sorry  -- same Bernoulli + pow_padicValNat_dvd proof; current proof survives with m = n+1
```

(The current `(n : ℕ)`-successor lemma is then the immediate corollary `m := n+1`,
which discharges `m - 1 = n` definitionally.)

Cost of restatement: **CHEAP** — mechanical. The existing proof transplants verbatim (`p^v ∣ m` from `pow_padicValNat_dvd`, `p^v ≤ m` from `Nat.le_of_dvd hm.pos'`, Bernoulli, `linarith`); only the `m ≥ 1` hypothesis is threaded in to license `m - 1`.

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently. (Also ran 4c below.)

#### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                | no       | —                      | The only hypothesis is `Fact p.Prime`; weakening it to `1 < p` (Phase 4a row 2) is a *generality* move, not an idiom move. |
|  2 | sequences/metric → filters/topological?                                                            | no       | —                      | Pure `ℕ` arithmetic; no limits or topology in the statement. |
|  3 | construct an object → universal-property class?                                                    | no       | —                      | No object is constructed; it's an inequality. |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | —                      | No subset/substructure here. |
|  5 | vector-space/metric/field-specific → weaker typeclass (module/(semi)ring)?                          | no       | —                      | Already on `ℕ`; nothing to weaken structurally beyond row-2 primality. |
|  6 | 1-categorical → higher/∞-categorical?                                                               | no       | —                      | n/a — elementary number theory. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid/ordered structure?                        | no (mostly) | (base `b` instead of prime `p` — covered by Phase 4a row 2) | The `padicValNat` base could be any `b ≥ 2`, but that is captured as the primality weakening in 4a, not a separate categorification. |

Modern idiom available: **no** (beyond the literature-weakening in 4a/4b).
One-line reason: this is a finite arithmetic inequality on `ℕ`; there is no sequence-to-filter, construction-to-universal-property, or categorification move. The *only* legitimate generalisation is the literature weakening (drop the successor encoding + drop primality to `1 < p`), already captured in Phase 4b.

→ The "generalise first" target is the **literature-weakened** form, with reason **LITERATURE-WEAKENING** (not MODERN-IDIOM).

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (no definitional equalities or typeclass-search paths introduced).

---

### PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.sub_one_mul_padicValNat_succ_le`

[A] Lean-Finder       (service not available in-session; substituted by exhaustive grep [D]+[E] over the pinned mathlib tree)   n/a: tool not callable; coverage via [D]/[E]
[B] Loogle            `(_ - 1) * padicValNat _ _ ≤ _`, `padicValNat _ _ ≤ _ - 1`   (service not callable in-session) — n/a: substituted by [D] type-shape grep, which is exhaustive over the source
[C] LeanSearch        "(p-1) times p-adic valuation of n at most n", "bound p-adic valuation single integer linear"   via WebSearch proxy (query #4) → only `padicValNat_le_nat_log` surfaced
[D] Grep mathlib src  `sub_one_mul_padicValNat`, `\(p - 1\) \* padicValNat`, `\(p - 1\) \* (Nat\.)?log`, `padicValNat p [a-z]` ∩ {≤,<} − {factorial,choose,digits}   → see below
[E] Name pattern      `padicValNat .* (succ|n \+ 1) .* le`, `mul.*padicValNat.*le` over `NumberTheory/Padics/` and `Data/Nat/Log.lean`   → see below

Searched for both:
  - **user's current form** `(p−1)·v_p(n+1) ≤ n` — **no hit**.
  - **literature-standard form** `(p−1)·v_p(m) ≤ m−1` / `v_p(m) ≤ log_p m` — found the *log* version only.

What mathlib **does** have (relevant decls, by qualified name):
- `padicValNat_le_nat_log` (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:467`): `padicValNat p n ≤ Nat.log p n`. **The only plain-integer valuation upper bound.** Does *not* give the `(p−1)`-multiplied linear form.
- `Nat.pow_log_le_self` (`Mathlib/Data/Nat/Log.lean:171`): `b ^ log b x ≤ x`. The `p^v ≤ m` half.
- `pow_padicValNat_dvd`, `padicValNat_dvd_iff_le` (`Basic.lean:428`): the `p^v ∣ m` half (used in the proof).
- `one_add_mul_le_pow` (`Mathlib/Algebra/Order/Ring/Pow.lean:100`): Bernoulli `1 + n·a ≤ (1+a)^n` (used in the proof).
- The `sub_one_mul_padicValNat_*` family (`Basic.lean:582,591,637,654`): **all about factorials/binomials** — Legendre `(p−1)v_p(n!) = n − s_p(n)`, the strict `(p−1)v_p(n!) < n`, and Kummer for `choose`. **None about a single plain integer.** `Mathlib/Data/Nat/Log.lean` (92 decls) has `pow_log_le_self`/`log_lt_self`/`log_le_self` but **no `(b−1)·log b n ≤ n` lemma**.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard `≤ log_p` form). The closest is `padicValNat_le_nat_log`, which is the `log`-form, *strictly weaker in shape* (gives `p^v ≤ m`, not the linear `(p−1)v ≤ m−1`); the `sub_one_mul_padicValNat_*` family is factorial-only. There is a real, narrow API gap.

---

### PHASE 6 — Composition check (+ call-sites)

#### Call sites — `PadicLFunctions.sub_one_mul_padicValNat_succ_le`

Internal use count: **2** (within `PadicLFunctions`, **not** counting the declaring line).
External-to-file callers: **0 distinct files** (both uses are inside the declaring file `PadicExp.lean`).

| Caller file:line                   | Usage pattern (one-line excerpt)                                      |
|------------------------------------|------------------------------------------------------------------------|
| `…/PadicExp.lean:341`              | `nlinarith [sub_one_mul_padicValNat_succ_le p n]` — inside `norm_succ_inv_smul_pow_le` (log-term decay bound) |
| `…/PadicExp.lean:836`              | `sub_one_mul_padicValNat_succ_le p (n - 1)` then `show (n-1)+1 = n` rewrite — inside `norm_natCast_inv_pow_le` (inverted Legendre bound for the log coefficients) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - **(none)** across the whole repo. `one_add_mul_le_pow` (the Bernoulli core) appears in the project only at `PadicExp.lean:315` — i.e. *inside this very lemma's proof*, nowhere else. So the estimate is centralised here, not duplicated.

Composability signal (per Phase 6.0.1): **K = 2 internal uses, no inline re-derivation.** Both consumers are the convergence-radius bounds for the p-adic log/exp denominators — the exact mathematical purpose. The line-836 caller even contorts (`(n-1)+1 = n`) to fit the successor form, which is direct evidence the *general* `m`-form would compose more cleanly. Signal: real (if small) API; the lemma is used, not dead — leans toward a YES-family verdict, modulo the generality fix.

#### Composition check (Phase 6)

Can `(p−1)·v_p(n+1) ≤ n` be derived from mathlib in ≤3 chained calls?

Attempt 1 (via `padicValNat_le_nat_log`):
  - `have h := padicValNat_le_nat_log (p:=p) (n+1)`  — gives `v ≤ Nat.log p (n+1)`.
  - To finish we'd need `(p−1) * Nat.log p (n+1) ≤ n`. **Mathlib has no such lemma** (Phase 5: `Data/Nat/Log.lean` has `pow_log_le_self`/`log_le_self`/`log_lt_self` but no `(b−1)·log b n ≤ n`). So this is not a finishing call — it bottoms out in a *missing* `Nat.log` Bernoulli bound that is itself the same non-trivial argument.
  - Result: **fails** (the multiply-by-`(p−1)` step is exactly the gap).

Attempt 2 (the actual proof — direct):
  - `Nat.le_of_dvd (n+1).succ_pos pow_padicValNat_dvd` ⇒ `p^v ≤ n+1` (1 call).
  - `one_add_mul_le_pow (show (-2:ℤ) ≤ p−1) v` ⇒ `1 + v(p−1) ≤ p^v` over ℤ (1 call).
  - `linarith` + `exact_mod_cast` to glue and return to ℕ (**real reasoning step**, not a composition).
  - Result: **partial / NOT a clean composition** — it is a 3-fact proof with a `linarith` join and a cast, i.e. a genuine (small) proof per the Phase-6 heuristics table (`have h; have h'; … exact` with non-trivial reasoning between = NO, not a composition).

Conclusion: **NOT-COMPOSABLE.** Mathlib's primitives (`pow_padicValNat_dvd`, `one_add_mul_le_pow`) are the *ingredients*, but assembling them into the linear bound requires a `linarith`/cast proof, not a ≤3-call chain. The would-be one-call route (`padicValNat_le_nat_log`) does not finish because the `(p−1)·log ≤ n` lemma it needs is itself missing from mathlib.

---

## Verdict: `PadicLFunctions.sub_one_mul_padicValNat_succ_le`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the estimate is standard/folklore in p-adic analysis; the *named* mathlib-and-Wikipedia statement is `v_p(m) ≤ log_p m`, and the linear `(p−1)v_p(m) ≤ m−1` is its (unnamed) Bernoulli sharpening, used for p-adic exp/log convergence radii. General form: any `m ≥ 1`, any base `b ≥ 2` — primality unused.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 2 weakenings (drop the `n+1` successor encoding to a free `m ≥ 1`; drop `Fact p.Prime` to `1 < p`). Modern-idiom (4c): none beyond this literature weakening (reason = LITERATURE-WEAKENING).
- Mathlib search (Phase 5): **not in mathlib** under either form. Only `padicValNat_le_nat_log` (log-form) exists for a plain integer; the `sub_one_mul_padicValNat_*` family is factorial/binomial-only.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the `log`-route is missing its own `(p−1)·log ≤ n` step, and the direct route is a `linarith`/cast proof, not a ≤3-call chain. K = 2 internal uses, no inline re-derivation.

**Rationale (1–2 paragraphs):**

This is a real, if small, gap in mathlib's elementary `padicValNat` API. Mathlib
deliberately ships the linear `(p−1)`-times-valuation identities for the
**factorial and binomial** cases (Legendre's `sub_one_mul_padicValNat_factorial`
and Kummer's `…_choose_eq_sub_sum_digits`, with the strict corollary
`sub_one_mul_padicValNat_factorial_lt_of_ne_zero : (p−1)·v_p(n!) < n`), but it
has **no** analogue for a *single integer* `m`: the only plain-integer bound is
`padicValNat_le_nat_log : v_p(m) ≤ log_p m`. That `log`-form does not compose to
the linear form a convergence proof actually needs — multiplying by `(p−1)`
requires `(p−1)·log_p m ≤ m−1`, which mathlib also lacks. So the result is
neither already-present (Phase 5: NO) nor a ≤3-call composition (Phase 6:
NOT-COMPOSABLE); it is a genuine lemma. The named gap: the symmetric companion
to `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, but for `padicValNat p m`
of a bare `m` — the elementary `v_p(m) ≤ (m−1)/(p−1)` estimate that every p-adic
exp/log convergence argument (Cassels §12, Washington §5.1, Koblitz, Neukirch)
silently uses.

It is **not** `YES-add-as-is` because Phase 4b found it strictly narrower than
the standard form on two mechanical axes: (i) the `n+1` successor encoding — a
presentation artifact whose only purpose is to make the RHS a subtraction-free
`n`, and which already forces a contortion at call-site `PadicExp.lean:836`
(`show (n-1)+1 = n`); and (ii) the `Fact p.Prime` hypothesis, which the proof
never uses (only `p ≥ 2` via the Bernoulli `−2 ≤ p−1` and the `dvd`/`pow`
steps). Mathlib's iron rule is to ship the general form, and here the
generalisation is **CHEAP** — the existing proof transplants verbatim onto
`{p} (hp : 1 < p) {m} (hm : 1 ≤ m) : (p−1)·v_p(m) ≤ m−1`, with the current
successor lemma falling out as the `m := n+1` corollary.

**Reason for the generalisation:**
- **LITERATURE-WEAKENING**: Phase 4b found the user's form strictly narrower than the literature-standard `m ≥ 1` / base-`b ≥ 2` statement (the successor encoding and the primality hypothesis are both removable).

**Proposed restatement:**
```lean
/-- For `1 < p` and `1 ≤ m`, the Bernoulli sharpening of `v_p(m) ≤ log_p m`:
`(p − 1) · v_p(m) ≤ m − 1`. The single-integer companion to mathlib's
factorial/binomial Legendre–Kummer identities (`sub_one_mul_padicValNat_factorial`). -/
theorem sub_one_mul_padicValNat_le {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 1 ≤ m) :
    (p - 1) * padicValNat p m ≤ m - 1 := by
  sorry  -- transplant of the current PadicExp.lean:310–321 proof:
         --   p^v ∣ m  (pow_padicValNat_dvd) ⇒ p^v ≤ m  (Nat.le_of_dvd hm.pos')
         --   1 + v(p-1) ≤ p^v  (one_add_mul_le_pow, needs only p ≥ 2)
         --   linarith ⇒ (p-1)·v ≤ m-1
```
(Then `sub_one_mul_padicValNat_succ_le p n` is exactly
`sub_one_mul_padicValNat_le hp (Nat.succ_pos n) ` specialised at `m := n+1`,
where `m - 1 = (n+1) - 1 = n` reduces definitionally.)

Estimated cost of regeneralisation: **CHEAP** (mechanical; the current proof survives unchanged modulo threading `hm`). Note: cost does not gate the verdict.

Mathlib downstream this enables:
- Drops cleanly beside `padicValNat_le_nat_log` and the `sub_one_mul_padicValNat_factorial` family in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`, completing the "(p−1)·valuation" picture (factorial ✓, binomial ✓, **single integer ✗→✓**).
- The bare-`m`, `1 < p` form composes with any p-adic convergence-radius argument (p-adic exp/log, formal-group logarithms — cf. the sibling HasseWeil `padicValNat_factorial_le`) without the successor gymnastics seen at `PadicExp.lean:836`.

Next action: run **`/generalise PadicLFunctions.sub_one_mul_padicValNat_succ_le`** (it will tension against the literature-standard `v_p(m) ≤ (m−1)/(p−1)` form from Phase 3 — there is no separate modern-idiom target). Land the generalised `sub_one_mul_padicValNat_le` first; keep `sub_one_mul_padicValNat_succ_le` as the local successor-corollary (or inline it at the 2 call sites). Then `/cleanup` the file and open a `feat(NumberTheory/Padics)` PR adding `sub_one_mul_padicValNat_le` next to the existing factorial Legendre lemmas.

---

## Next step

Run **`/generalise PadicLFunctions.sub_one_mul_padicValNat_succ_le`** to restate as
`sub_one_mul_padicValNat_le {p} (hp : 1 < p) {m} (hm : 1 ≤ m) : (p−1)·padicValNat p m ≤ m−1`
(dropping the successor encoding and the unused primality hypothesis), confirm the
existing proof transplants, then open a `feat(NumberTheory/Padics)` PR placing it
beside `padicValNat_le_nat_log` and the `sub_one_mul_padicValNat_factorial` family
in `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`. The current
successor-form lemma becomes the `m := n+1` corollary (or is inlined at its 2
call sites).
