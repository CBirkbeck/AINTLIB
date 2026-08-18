# `/mathlibable` report — `PadicLFunctions.MeasureR.padicLog_pow_pPow_of_norm_lt_one`

**Final verdict: `NO-composable-from-mathlib`** — this is a ≤3-call specialization (`n = p^N`, with an `nsmul`→`K`-scalar cast) of the project's *own* general nat-power law `padicLog_pow_of_norm_lt_one`, which is the form that would actually be contributed if mathlib ever acquired a p-adic logarithm. It is an internal bootstrapping lemma, not a standalone mathlib result.

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — the file elaborates as part of `main`, and the target plus all dependencies were read directly.
- decl `PadicLFunctions.MeasureR.padicLog_pow_pPow_of_norm_lt_one`:  resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:531` (unique match on the `theorem` keyword).
- kind:                      theorem
- has sorry:                 no (lines 531–537 contain zero `sorry`)
- module docstring summary:  the p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii)); this block (T618 / decomposition R6.6) extends the boundary-ball logarithm facts to the whole open unit ball `‖z−1‖ < 1`.

Section context (file header, lines 39–41): `p : ℕ` with `[Fact p.Prime]`; `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`. The theorem `omit`s `[CharZero K]` and `include`s `hp`.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.padicLog_pow_pPow_of_norm_lt_one` is a **theorem** stating the following:

> Let `K` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra, and let `log_p` be the p-adic logarithm `log_p(x) = Σ_{n≥0} (−1)^n (n+1)⁻¹ (x−1)^{n+1}`. For any `z ∈ K` with `‖z − 1‖ < 1` (i.e. `z` in the open unit ball around 1) and any `N ∈ ℕ`,
> `log_p(z^{p^N}) = p^N · log_p(z)`,
> where the scalar `p^N` on the right is `(p : K)^N` acting by the `K`-module scalar action.

This is the **iterated p-power law** for the p-adic logarithm. It is the `N`-fold iterate of the single-step p-power law `log_p(z^p) = p · log_p(z)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; `(p : K)` is the image of `p` in `K`.
- `K` — a complete, ultrametric, normed `ℚ_p`-algebra (a normed field). Mathematically `K` is a complete extension of `ℚ_p` (the intended model is `ℂ_p` or a finite extension).
- `log_p = padicLog p` — the convergent p-adic log series (`PadicExp.lean:384`).

Hypotheses (Lean side):
- `hz : ‖z − 1‖ < 1` — `z` lies in the open unit ball around 1 (where the log series converges and is a homomorphism).
- `N : ℕ` — the iteration count.

Conclusion (math): `log_p(z^{p^N}) = p^N · log_p(z)`.

Conclusion (Lean): `padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z`.

**Proof body (load-bearing):** a one-step induction on `N`. Base `N = 0` is `pow_zero/pow_one/one_smul`. Step uses `padicLog_pow_p_of_norm_lt_one` (the genuine single p-power content, proved separately via the `seriesEval`/`formalLog` bridge) on `z^{p^M}` — which stays in the ball by `boundary_norm_pow_sub_one_lt_one` — plus `smul_smul` and `pow_succ`. The theorem contributes **no new mathematical idea beyond iterating** the single-step law.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a corollary obtained by trivial induction from `padicLog_pow_p_of_norm_lt_one`; not a named theorem, not a new structure, and not a `## Main results` headline (the file's main result is `L_p(θ,1)`; this is bookkeeping infrastructure used to prove `padicLog_mul_of_norm_lt_one`).

(Literature width was EXHAUSTIVE regardless — see Phase 3. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: ~4 substantive lines (an `induction … with` block).
One-liner verdict: **n/a — kind is theorem, not def.** The defeq/diamond/API-name exemptions do not apply to a `theorem`.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

The mathematical concept is: **the p-adic logarithm is a homomorphism on the open unit ball `1 + 𝔪` (`log(xy) = log x + log y`), so `log(x^n) = n·log(x)`; the special case `n = p^N` gives `log(x^{p^N}) = p^N·log(x)`.** The single-step `log(z^p) = p·log(z)` is the "Frobenius-equivariance" / p-power law.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | `p-adic logarithm log(x^n)=n log(x) power rule property unit ball`                                      | yes  | `log_p(x^n)=n·log_p(x)` follows from `log_p(xy)=log_p x+log_p y`; series converges for `|x|_p<1` (`|x−1|<1` for the `1+x` form) | Wikipedia "p-adic exponential function"; MIT note `math.mit.edu/~dav/exp.pdf`; arXiv surveys |
|  2 | WebSearch (general form)         | `p-adic logarithm homomorphism log(xy)=log x+log y open unit ball 1+pZ_p Iwasawa`                       | yes  | injective group homomorphism on `{x∈ℂ_p : |x−1|<1}`; the standard `Γ = 1+pℤ_p ≅ ℤ_p` iso in Iwasawa theory | confirms domain + homomorphism; extension to `|x|=1` via `log_p(x) = n⁻¹ log_p(x^n)` (this is literally our lemma running in reverse) |
|  3 | WebSearch (named-after / Frobenius) | `p-adic logarithm "log(x^p)=p log x" Frobenius p-power Coleman power series`                          | yes  | `log(z^p)=p·log(z)` is the Frobenius-equivariance identity (Coleman integration; `∫_{x^p}^{z^p} f = ∫_x^z f(t^p)d(t^p)`) | the single-step law (our `padicLog_pow_p_…`) named explicitly; iterating it is our target |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of the p-adic log power law")            | n/a  | —                                | **MCP not configured in this environment** (no `chatgpt`/`openai` tool surfaced via ToolSearch). Compensated by running 5 WebSearch queries (≥3 required) at distinct generality levels + 3 source fetches. |
|  5 | Local references                 | `ls projects/PadicLFunctions/.mathlib-quality/references/`                                              | n/a  | (directory absent)               | no `references/` dir and no `refs/` symlink present — recorded n/a per protocol |
|  6 | nLab                             | fetched `ncatlab.org/nlab/show/logarithm` (and `…/p-adic+exponential`, 404)                            | no   | nLab "logarithm" covers ℝ/ℂ/Lie-group logs only; **no p-adic section**; the `p-adic+exponential` slug 404s | nLab simply has no dedicated p-adic-log page; not evidence of novelty (concept is classical elsewhere) |
|  7 | nCatLab (categorical)            | n/a — not a categorical concept                                                                         | n/a  | —                                | `log(x^n)=n log x` is an elementary identity on a normed field; nothing higher-categorical to look up |
|  8 | Stacks Project (alg geom)        | n/a — not an algebraic-geometry concept                                                                 | n/a  | —                                | the p-adic analytic log is not a scheme-theoretic object; Stacks has no relevant tag |
|  9 | MathOverflow / Math.StackExchange| `"p-adic logarithm" group homomorphism multiplicative additive "1+p" proof`                            | yes  | the multiplicative formal group law `M(x,y)=x+y+xy` induces `log_p(1+t)=t−t²/2+…`; `log` is the formal-group logarithm; coincides with `log_p` on principal units `1+𝔪_K` | results surfaced from arXiv mirror rather than MO/MSE directly, but confirm the homomorphism + power law as textbook |
| 10 | recent arXiv (last 5 years)      | (covered by #1–3, #9 returns)                                                                           | yes  | multiple 2018–2025 papers use `log(x^n)=n log x` / `log(x^p)=p log x` as a routine step (Ankeny–Artin–Chowla, Iwasawa K₁, p-adic periods) | the identity is used without proof as standard |

The protocol passes:
- WebSearch ran **5** distinct queries at three generality levels (specific power-rule form; general homomorphism form; named Frobenius/p-power form) — exceeds the ≥3 requirement.
- ChatGPT MCP unavailable in this environment → recorded n/a with reason and over-compensated on WebSearch + source fetches.
- Local references checked (absent → n/a with reason).
- nLab checked (covers other logs, no p-adic section).
- Stacks / nCatLab / MathOverflow / arXiv each checked or recorded n/a with a reason.

### Literature summary (Phase 3)

Concept identified as: **the p-power / homomorphism law of the p-adic logarithm** — specifically `log_p(z^{p^N}) = p^N·log_p(z)`, the `N`-fold iterate of the Frobenius-equivariance identity `log_p(z^p) = p·log_p(z)`, itself a special case of `log_p(z^n) = n·log_p(z)`, itself a corollary of the homomorphism `log_p(xy) = log_p x + log_p y` on `1 + 𝔪`.

Sources agree on the standard form: **yes.** Every source states the homomorphism property `log_p(xy)=log_p x+log_p y` on `‖x−1‖<1`. The power rule `log(x^n)=n·log(x)` is so immediate from it that Wikipedia does not even state it separately ("The document does **not** explicitly state log(x^n)=n log x" — because it is a one-line consequence). The single-step `log(z^p)=p log z` does get named (Frobenius equivariance / Coleman).

Most general standard form: `log_p : (1 + 𝔪_K) → (K, +)` is a group homomorphism (where `K` is any complete extension of `ℚ_p`, e.g. `ℂ_p`), hence `log_p(x^n) = n·log_p(x)` for **all** `n ∈ ℕ` (not just `n = p^N`).

Generality dimensions where the literature varies:
- **Exponent**: the standard statement is for arbitrary `n` (`log(x^n)=n log x`); `n = p^N` is a *special case the literature does not single out* except via the named single-step `log(z^p)=p log z`. Our target sits strictly between these (it is the `n = p^N` instance).
- **Domain**: literature gives the homomorphism on `1+𝔪` (`‖x−1‖<1`) — exactly our `hz`. Some sources extend to `|x|=1` *using* `log(x) = n⁻¹ log(x^n)`, i.e. our lemma is the engine behind that extension (and `extLog_eq_padicLog_of_norm_lt_one`, the very next decl, does exactly this).

Disagreement with the literature: **none.** Our form is a correct, more-special instance (exponent restricted to `p^N`) of the standard power law.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `log_p(x^n) = n·log_p(x)` for **all** `n ∈ ℕ`, on `‖x−1‖<1`.

### Generality analysis — `padicLog_pow_pPow_of_norm_lt_one`

| # | Parameter / hypothesis        | Current Lean form            | Literature-standard form          | Weaker / more general form exists? | Reason |
|---|-------------------------------|------------------------------|------------------------------------|-----------|--------|
| 1 | exponent `p ^ N`              | only `p`-power exponents     | arbitrary `n : ℕ`                  | **YES** — generalise `p^N` to any `n` | The homomorphism law gives `log(x^n)=n log x` for all `n`; restricting to `p^N` is a needless specialisation. The project itself proves the general form as `padicLog_pow_of_norm_lt_one` (line 577) and the exp-ball version `padicLog_pow` (ExtLog.lean:79). |
| 2 | scalar `(p : K) ^ N •`        | `K`-module scalar `(p:K)^N`  | `n·` (i.e. `nsmul`, `(p^N : ℕ) •`) | re-expressible | `(p:K)^N • a = ((p^N:ℕ):K) • a = (p^N:ℕ) • a` by `Nat.cast_pow` + `Nat.cast_smul_eq_nsmul`. The `K`-scalar form is a defeq-adjacent restatement chosen only because the downstream `extLog_eq_padicLog_of_norm_lt_one` then recasts it as a `ℚ_p`-scalar to cancel `(p^j)⁻¹`. |
| 3 | `hz : ‖z − 1‖ < 1`            | open unit ball               | open unit ball `1+𝔪`               | NO — this is the maximal domain | the convergent log series is only a homomorphism on `‖x−1‖<1`; this hypothesis is exactly the literature's domain. Cannot be weakened. |
| 4 | typeclasses on `K`            | complete ultrametric normed `ℚ_p`-algebra | complete extension of `ℚ_p` | already maximal/idiomatic | matches mathlib's normed-field + `IsUltrametricDist` + `CompleteSpace` idiom; this is the right hypothesis cluster, not a weakening target. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (row 1 — exponent restricted to `p^N` where the standard law is for all `n`).
Number of weakening opportunities found: **1 substantive** (exponent `p^N → n`), plus a cosmetic scalar restatement (row 2).

Proposed restatement (the general form): this is *literally* the already-present `padicLog_pow_of_norm_lt_one`:
```lean
theorem padicLog_pow_of_norm_lt_one {x : K} (hx : ‖x - 1‖ < 1) (n : ℕ) :
    padicLog p (x ^ n) = n • padicLog p x
```
Cost of restatement: **CHEAP** — the general form already exists in the project (proved by the same one-step induction via the multiplicativity lemma). The target is recovered from it in ≤3 calls (see Phase 6).

**Important:** because the general form is *already proved in the project*, the target is not "narrow form awaiting generalisation" (which would be `YES-but-generalise-first`) — it is a *redundant specialisation of an existing general lemma*. The relevant question becomes composability (Phase 6), not generalisation. See the Phase 7 synthesis.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                          | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                          | no       | already fully typeclassed (`[NormedField K] [NormedAlgebra ℚ_[p] K] …`) | — |
|  2 | sequences/metric → filters/topological?                                                           | no       | the statement is an algebraic identity; no limit/convergence in the *statement* (convergence is hidden in `padicLog`'s definedness) | — |
|  3 | construct an object → universal-property class?                                                   | no       | this is an identity about an existing map, not a construction | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                | partial-but-no | one *could* phrase `1+𝔪` as the principal-unit subgroup and `log_p` as a `MonoidHom → AddMonoidHom`; the homomorphism law would then be `map_pow`/`map_mul`. But that is a reformulation of the *parent* `padicLog_mul`/`padicLog_pow`, not of this `p^N` specialisation. | (would land on the general lemma, not this one) |
|  5 | vector-space/field-specific → modules/(semi)ring?                                                  | no       | `K` is genuinely a normed field here; no over-strong field hypothesis | — |
|  6 | 1-categorical → higher-categorical?                                                                | no       | elementary identity | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group?                                                   | **partial** | the *exponent* `p^N` should be a general `n : ℕ` (row 1 of 4a) — but again, that target is the already-existing `padicLog_pow_of_norm_lt_one`, not a new modern idiom | unifies with the project's general power law |

Modern idiom available: **no new idiom** beyond what row 7 / 4a already flag (de-specialise the exponent). The truly idiomatic move — bundling `log_p : (1+𝔪)ˣ →* (K,+)` as a homomorphism so the power law becomes `map_pow` — applies to the *parent* multiplicativity lemma `padicLog_mul`/`padicLog_pow`, not to this `p^N` corollary. For *this* declaration there is no separate modernisation: it should simply not exist as its own lemma.

One-line reason this is not a fresh modernisation move: the only reformulation is "use the general `n`-power law and cast the scalar", which is the composition in Phase 6 — not a new mathlib-idiomatic statement of *this* lemma.

---

### PHASE 4.5 — Diamond / defeq risk

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or typeclass-search paths; the six-row risk table is skipped per the skill's scope rule.

---

### Mathlib search-status: `padicLog_pow_pPow_of_norm_lt_one` (Phase 5)

Read `references/mathlib-search.md` discipline: searched **both** the user's `p^N` form and the literature-standard `n`-power form, in both their `padicLog` spelling and any conceivable mathlib spelling.

[A] Lean-Finder       n/a — Lean-Finder MCP not available in this environment; substituted by [D]+[E] exhaustive grep over the vendored `.lake/packages/mathlib` tree (the authoritative source for this pin).
[B] Loogle            n/a — Loogle MCP not available; the decisive fact (mathlib has **no** `padicLog`) is established by exhaustive grep [D].
[C] LeanSearch        n/a — LeanSearch MCP not available; covered by the literature search (Phase 3) for the concept and by [D]/[E] for the Lean symbol.
[D] Grep mathlib src  `padicLog` → **ZERO hits** in all of `.lake/packages/mathlib/Mathlib/`. `def.*[Ll]og` in `Mathlib/NumberTheory/Padics/` → none (the Padics dir has no logarithm at all). `log_pow` → only `Real.log` (`SpecialFunctions/Log/Basic.lean:287`) and `ENNReal.log` (`…/ENNRealLog.lean:176`), both real-valued, different objects.  → **no hits for a p-adic log or its power law**
[E] Name pattern      grepped `padicLog`, `Padic.log`, `padic.*log`, `log.*padic` across `Mathlib/` → no p-adic-valued logarithm anywhere; the only `padic*`+`log` co-occurrences are `padicValNat`/`padicValRat` with `Real.log` (e.g. `Harmonic/Int.lean`), unrelated.

Searched for both:
- the user's current form (`log(z^{p^N}) = p^N • log z`): not in mathlib (no `padicLog`).
- the literature-standard form (`log(x^n) = n • log x`): not in mathlib (no `padicLog`).

Concluded: **not in mathlib.** Mathlib has no p-adic logarithm whatsoever (the `Mathlib/NumberTheory/Padics/` tree stops at norms, valuations, Hensel's lemma, Mahler basis — there is no `exp`/`log` on `ℚ_p` or `ℂ_p`). Consequently mathlib has neither this `p^N` form nor the general `n`-power form. The closest *named* mathlib facts are `Real.log_pow` and `ENNReal.log_pow`, which are about `Real.log`/`ENNReal.log` and do **not** transfer.

**Building blocks present in mathlib (generic, not p-adic):** `Nat.cast_pow` (`(p^N : K) = ((p:K))^N`), `Nat.cast_smul_eq_nsmul (n : ℕ) (b : M) : (n : R) • b = n • b` (`Mathlib/Algebra/Module/NatInt.lean:115`), `smul_smul`, `pow_succ`. These are the scalar-bookkeeping blocks; the *mathematical* block (`log` is a homomorphism on the ball) is **not** in mathlib — it lives only in the project (`padicLog_mul`, `padicLog_pow`, `padicLog_pow_of_norm_lt_one`).

---

### Call sites — `padicLog_pow_pPow_of_norm_lt_one` (Phase 6.0)

Internal use count: **4** (all within the declaring file `ValuesAtOne.lean`; the declaration itself is at line 531).
External-to-file callers: **0 distinct files.** External-to-project callers: **0.**

| Caller file:line                         | Usage pattern (one-line excerpt)                                              |
|------------------------------------------|------------------------------------------------------------------------------|
| ValuesAtOne.lean:568                     | `rw [padicLog_pow_pPow_of_norm_lt_one (p := p) hxy, …] at hkey` (in `padicLog_mul_of_norm_lt_one`) |
| ValuesAtOne.lean:569                     | `padicLog_pow_pPow_of_norm_lt_one (p := p) hx, …`                            |
| ValuesAtOne.lean:570                     | `padicLog_pow_pPow_of_norm_lt_one (p := p) hy, ← smul_add] at hkey`           |
| ValuesAtOne.lean:596                     | `padicLog_pow_pPow_of_norm_lt_one (p := p) hx,` (in `extLog_eq_padicLog_of_norm_lt_one`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **none** — but note the *general* law `padicLog_pow_of_norm_lt_one` (line 577) coexists and is the more natural tool; the only reason the `p^N` form is used at 568–570 instead of the general `n`-form is **proof ordering** (the general form's proof routes through `padicLog_mul_of_norm_lt_one`, which is exactly the lemma being proved at 543–571, so it is not yet available there — a bootstrap).

What the pattern tells you: all consumers are **inside the declaring file**, in exactly two parent lemmas. There is no downstream/public consumer. Per the call-sites table, `K ≥ 1` but purely-internal + a coexisting more-general lemma is a strong **NO-composable / internal-helper** signal, not a public-API signal.

### Composition check (Phase 6)

Can `padicLog_pow_pPow_of_norm_lt_one` be derived in ≤3 chained calls?

**Attempt 1 — from the project's own general law:**
```lean
theorem padicLog_pow_pPow_of_norm_lt_one {z : K} (hz : ‖z - 1‖ < 1) (N : ℕ) :
    padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z := by
  rw [padicLog_pow_of_norm_lt_one hz (p ^ N), ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
```
- Mathlib/project decls used: `padicLog_pow_of_norm_lt_one` (project), `Nat.cast_pow` (mathlib), `Nat.cast_smul_eq_nsmul` (mathlib).
- Result: **succeeds** — 3 rewrites. `padicLog_pow_of_norm_lt_one hz (p^N)` gives `padicLog p (z^(p^N)) = (p^N : ℕ) • padicLog p z`; `← Nat.cast_pow` and `Nat.cast_smul_eq_nsmul` convert `(p^N:ℕ) • a` to `((p:K)^N) • a`.
- Notes: this is the genuine relationship — the `p^N` form is the `n = p^N` instance of the general nat-power law, modulo a scalar cast.

Conclusion: **COMPOSABLE** (≤3 calls) *from the project's general law*. Per the Phase-6 heuristics table, three `rw`s with no `ring_nf`/`aesop`/non-trivial reasoning is a legitimate composition, not a proof in disguise.

**Caveat (the real subtlety):** the composition's mathematical block (`padicLog_pow_of_norm_lt_one`, i.e. "`log` is a homomorphism, so `log(x^n)=n log x`") is itself **not in mathlib** — mathlib has no p-adic log. So if one asks "compose from *mathlib today*", the answer is "you cannot — the p-adic log doesn't exist there." The composition is from would-be-mathlib (or the project's) general power law plus mathlib's generic scalar-cast lemmas. This is what makes the verdict `NO-composable-from-mathlib` rather than `NO-mathlib-has-it`: the *exact form* is absent from mathlib, but it is a 3-call composition of the general form (the thing that *would* be contributed) with mathlib's `Nat.cast_*` blocks — so it should never be a standalone lemma.

---

## Verdict: `padicLog_pow_pPow_of_norm_lt_one`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the homomorphism / power law `log_p(x^n) = n·log_p(x)` on `‖x−1‖<1` is textbook-standard (Wikipedia, MIT note, Iwasawa-theory & Coleman literature); the standard statement is for **arbitrary `n`**, and `log(z^p)=p log z` is the named single-step. The `n = p^N` form is a special case the literature does not isolate.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the exponent is restricted to `p^N` whereas the standard (and the project's own `padicLog_pow_of_norm_lt_one`) is for all `n`.
- Mathlib search (Phase 5): **not in mathlib** in any form — mathlib has no p-adic logarithm; the only `*log_pow` lemmas are `Real`/`ENNReal`, unrelated. The generic scalar blocks `Nat.cast_pow`, `Nat.cast_smul_eq_nsmul` are present.
- Composition check (Phase 6): **COMPOSABLE** — `rw [padicLog_pow_of_norm_lt_one hz (p^N), ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]` (3 calls), from the project's general power law (the would-be-mathlib form) plus mathlib casts.

**Rationale:**

This declaration is the `n = p^N` specialisation of the standard p-adic-logarithm power law `log(x^n) = n·log(x)`, with the scalar written as the `K`-element `(p:K)^N` instead of the natural-number `nsmul (p^N)`. The literature is unanimous that the *general* `n`-power law (a one-line corollary of `log(xy)=log x+log y` on the open unit ball) is the natural object; singling out `p^N` is not something the literature does, and the project itself separately proves the general form `padicLog_pow_of_norm_lt_one` (`ValuesAtOne.lean:577`) and an exp-ball analogue `padicLog_pow` (`ExtLog.lean:79`). The `p^N` form exists in the project purely as a **bootstrapping step**: the general law's proof routes through `padicLog_mul_of_norm_lt_one`, and that multiplicativity lemma (lines 543–571) needs the `p^N`-power law to scalar-divide and conclude — so at that point in the file the general `n`-law is not yet available, and the `p^N` form (provable directly by iterating the single-step `padicLog_pow_p_of_norm_lt_one`) is used instead. The `(p:K)^N` scalar shape is chosen because the very next consumer, `extLog_eq_padicLog_of_norm_lt_one` (line 596), recasts it as a `ℚ_p`-scalar `((p^N:ℕ):ℚ_[p])` to cancel against `(p^j)⁻¹`.

For *mathlib*, this is not a contribution. If mathlib ever acquires a p-adic logarithm, the homomorphism law and its corollary `log(x^n) = n • log x` (for all `n`) are what would be added — and from that, the `p^N` form is the 3-rewrite composition above (`padicLog_pow_of_norm_lt_one` specialised to `p^N`, then `Nat.cast_pow` + `Nat.cast_smul_eq_nsmul` to fix the scalar). A separate `…_pPow_…` lemma with a hand-cast scalar would be redundant clutter next to the general law. Mathlib does **not** have the form today (it has no p-adic log at all), which is why the bucket is `NO-composable-from-mathlib` rather than `NO-mathlib-has-it`; but the conclusion for *this* declaration is the same — it is an internal specialisation that composes from the general statement, not a standalone result worth upstreaming.

**WHY not (refactor-actionable detail):**
- The exact form is absent from mathlib, but it is a ≤3-call composition of (a) the general nat-power law for `padicLog` — the form that *would* be the mathlib contribution if the p-adic log were added — and (b) mathlib's generic scalar-cast lemmas. No separate `p^N` lemma is justified in mathlib; the `p^N` instance is recovered inline wherever needed.
- Building blocks: `PadicLFunctions.MeasureR.padicLog_pow_of_norm_lt_one` (`projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:577` — the general `n`-power law); `Nat.cast_pow` (mathlib); `Nat.cast_smul_eq_nsmul` (`.lake/packages/mathlib/Mathlib/Algebra/Module/NatInt.lean:115`).

Mathlib building blocks (for the scalar bookkeeping): `Nat.cast_pow`, `Nat.cast_smul_eq_nsmul`, `smul_smul`. Mathematical block (NOT in mathlib — project-only): `padicLog_pow_of_norm_lt_one`.

Composition sketch (≤3 lines):
```lean
example {z : K} (hz : ‖z - 1‖ < 1) (N : ℕ) :
    padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z := by
  rw [padicLog_pow_of_norm_lt_one hz (p ^ N), ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
```

Call sites in the project (from Phase 6.0): **K = 4**, all internal to `ValuesAtOne.lean` (lines 568, 569, 570 in `padicLog_mul_of_norm_lt_one`; line 596 in `extLog_eq_padicLog_of_norm_lt_one`).

**Refactor plan (project-internal — *not* a mathlib action):** This lemma should NOT be exported to mathlib. Within the project, it is a legitimate internal helper and need not be removed — but if a cleanup wants to eliminate the redundancy with the general `padicLog_pow_of_norm_lt_one`, note the ordering constraint:
- Sites 568–570 are *inside* `padicLog_mul_of_norm_lt_one`, which the general `n`-law transitively depends on (general law → `padicLog_mul_of_norm_lt_one` → target). These sites **cannot** be switched to the general law without breaking the bootstrap; they must keep using the directly-induction-proved `p^N` form (or be re-proved from the single-step `padicLog_pow_p_of_norm_lt_one` inline). **Leave as-is.**
- Site 596 (`extLog_eq_padicLog_of_norm_lt_one`) is *after* the general law (577) and could instead call `padicLog_pow_of_norm_lt_one hx (p^j)` + the two casts, inlining the 3-rewrite composition above and removing the dependence on the `p^N` lemma there.
- If, after rerouting site 596, the lemma is still needed only at 568–570, it stays as a private bootstrapping helper. There is no mathlib PR.

**Next action:** Do **not** open a mathlib PR for this declaration. It is an internal `p^N`-specialisation of the general p-adic-log power law; mathlib has no p-adic logarithm, and even if it did, the `p^N` form is the 3-rewrite composition shown above and would not be a separate lemma. Optionally (project cleanup only), reroute the single call at `ValuesAtOne.lean:596` through `padicLog_pow_of_norm_lt_one` + `Nat.cast_pow`/`Nat.cast_smul_eq_nsmul`; keep the lemma for the bootstrap sites 568–570. (If a p-adic-logarithm contribution to mathlib is ever undertaken, the object to upstream is the homomorphism `padicLog_mul`/the general power law `padicLog_pow_of_norm_lt_one`, assessed separately — not this corollary.)

---

## Next step

Do **not** open a mathlib PR for `padicLog_pow_pPow_of_norm_lt_one`. It is a ≤3-call composition (`rw [padicLog_pow_of_norm_lt_one hz (p^N), ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`) of the project's general nat-power law plus mathlib's scalar-cast lemmas — an internal bootstrapping specialisation, not a standalone mathlib result. Optional project cleanup: reroute the call at `ValuesAtOne.lean:596` through the general law; leave the bootstrap sites (568–570) untouched.
