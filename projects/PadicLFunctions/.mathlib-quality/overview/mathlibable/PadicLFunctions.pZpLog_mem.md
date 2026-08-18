# `/mathlibable` report — `PadicLFunctions.pZpLog_mem`

**Final verdict: `BORDERLINE-needs-human`**

This is the **log-image half** of the classical exp/log isomorphism of principal units —
"for odd `p`, `log` maps `1 + pℤ_p` onto `pℤ_p`" (K. Conrad *Strassmann's theorem and an
application* / *Infinite series in p-adic fields* / PlanetMath / Wikipedia / Washington
*Cyclotomic Fields* §5.1 / Cassels §12 / RJW Lem 5.14 / arXiv 1904.09850, 1907.06437,
2601.18187). It is true, textbook-standard, genuinely missing from mathlib, proved
sorry-free, and — unlike its bypassed exp sibling — **genuinely load-bearing (K = 3 call
sites)**. But it is a statement **about a project-only `def`** (`pZpLog`, the junk-totalised
integral logarithm `ℤ_[p] → ℤ_[p]`, itself `BORDERLINE`) whose two substantive proof inputs
are **project** lemmas mathlib lacks (`norm_padicLog`, the isometry, `YES-but-generalise-first`;
`coe_norm_le_inv_of_mem_span`, the norm bound, `NO-composable-from-mathlib`). Mathlib has **no
p-adic logarithm of any kind**. So neither NO bucket is groundable, and the YES bucket cannot
be committed without the human upstreaming decision that governs the whole nonarchimedean
exp/log development. Hence BORDERLINE — consistent with its exp sibling `pZpExp_sub_one_mem`
(which explicitly states this lemma "is in the identical situation"), the def `pZpLog`, and
`pZpLog_coe`, all `BORDERLINE`.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1094` (kind: `theorem`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task's BUILD NOTE — the build is stale/slow here; Phase 0 source-fallback used). The file is part of `main`, is committed-clean, contains **0 `sorry`/`admit`** (whole-file grep returns nothing), and the target plus its full dependency chain (`pZpLog`, `pZpLog_coe`, `norm_padicLog`, `inExpBall_of_mem_span`, `coe_norm_le_inv_of_mem_span`, `PadicInt.norm_def`/`norm_le_pow_iff_mem_span_pow`) were read directly from `PadicExp.lean`. Baseline commit `d71766e`.
- decl `PadicLFunctions.pZpLog_mem`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1094`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field and is an isometry there; for odd `p` the ball contains `pℤ_p`; the logarithm `log(1+y)=Σ(-1)^{n+1}yⁿ/n` converges for `‖y‖<1` and inverts `exp` on the matched balls; realises `x^s := exp(s·log x)`, agreeing with the character `PadicInt.onePAdicPow`. Cites Cassels §12 and Washington, *Introduction to Cyclotomic Fields* §5.1.

---

### Statement (Phase 1)

`pZpLog_mem` is a **theorem** stating the following:

> Let `p` be an **odd** prime. For every `x ∈ 1 + pℤ_p` (i.e. `x − 1 ∈ Ideal.span {p}`, the
> maximal ideal of `ℤ_p`), the integral p-adic logarithm `pZpLog p x ∈ ℤ_[p]` satisfies
> `pZpLog p x ∈ pℤ_p`.

Mathematically this is the **domain→codomain (image) half** of the classical statement "for
`p ≠ 2`, `log` maps `1 + pℤ_p` *into* (in fact *onto*) `pℤ_p`" — the inverse direction of the
isomorphism `pℤ_p ≅ 1 + pℤ_p` (Washington §5.1, Cassels §12, RJW Lem 5.14). The crux is the
**isometry** `‖log x‖ = ‖x − 1‖` on the convergence ball (K. Conrad: the linear term of
`log x = (x−1) − (x−1)²/2 + …` dominates p-adically), combined with `‖x − 1‖ ≤ p⁻¹` for
`x ∈ 1 + pℤ_p`. Together `‖log x‖ = ‖x − 1‖ ≤ p⁻¹`, i.e. `log x ∈ pℤ_p`. Here `pZpLog` is the
*junk-totalised integral* logarithm: `pZpLog p x := ⟨log x, _⟩ ∈ ℤ_[p]` when `‖log x‖ ≤ 1`, else
`0`; on `1 + pℤ_p` (odd `p`) it always takes the true branch (`pZpLog_coe`), so the statement is
the genuine "log lands in `pℤ_p`".

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- (No general `L`: the statement lives entirely at `L = ℚ_p` / `ℤ_p`, because `pZpLog : ℤ_[p] → ℤ_[p]` is `ℚ_p`-specific — it depends on `PadicInt`'s `Subtype` packaging, `PadicInt.norm_def`, and span/valuation API. The four `omit … in` lines around `pZpLog_coe`/`pZpLog_mem` drop `[NormedAlgebra ℚ_[p] L]` etc., confirming this object lives at `L = ℚ_p`.)

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — odd prime (so the `r = 1` isomorphism `1+pℤ_p ≅ pℤ_p` holds; the `p = 2` case is genuinely false — see Phase 3/4).
- `{x : ℤ_[p]}` with `hx : x − 1 ∈ Ideal.span {(p : ℤ_[p])}` — i.e. `x ∈ 1 + pℤ_p`.

Conclusion (math): for odd `p`, the integral logarithm of a principal unit `≡ 1 (mod p)` lands in `pℤ_p`; equivalently `log` maps `1 + pℤ_p` into the maximal ideal `pℤ_p`.

Conclusion (Lean): `pZpLog p x ∈ Ideal.span {(p : ℤ_[p])}`.

**Proof shape (load-bearing for the verdict).** A single rewrite chain ending in one project lemma:

```lean
theorem pZpLog_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpLog p x ∈ Ideal.span {(p : ℤ_[p])} := by
  have hxsub : ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, PadicInt.coe_one]
  have hball : InExpBall p ((x : ℚ_[p]) - 1) := by
    rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx
  rw [← pow_one (p : ℤ_[p]), ← PadicInt.norm_le_pow_iff_mem_span_pow _ 1,
    PadicInt.norm_def, pZpLog_coe p hp2 hx, norm_padicLog (L := ℚ_[p]) p hball,
    hxsub, zpow_neg, Nat.cast_one, zpow_one]
  exact coe_norm_le_inv_of_mem_span p hx
```

It rewrites `_ ∈ span {p}` to a norm bound via mathlib's `PadicInt.norm_le_pow_iff_mem_span_pow`,
unfolds the integral log to the analytic `padicLog` on the true branch (`pZpLog_coe`), applies the
**isometry** `norm_padicLog` to turn `‖log x‖` into `‖x − 1‖`, and discharges `‖x − 1‖ ≤ p⁻¹` with
`coe_norm_le_inv_of_mem_span`. The only non-trivial mathematical inputs are the two **project**
lemmas `norm_padicLog` (the isometry on the ball) and `coe_norm_le_inv_of_mem_span` (the norm
bound on `pℤ_p`); everything else is `PadicInt` plumbing and `zpow` arithmetic. This is the exact
structural mirror of the exp sibling `pZpExp_sub_one_mem` (`:1062`), with `log`/`norm_padicLog` in
place of `exp − 1`/`norm_padicExp_sub_one`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent caveat).
Reason: as a *declaration* it is an integrality corollary — a short rewrite chain, not a `def`,
structure, or main result, and it is **not** named after a person. *However*, it is the Lean
realisation of a famous textbook clause (the "log maps `1+pℤ_p` into `pℤ_p`" inverse half of the
exp/log isomorphism, Washington §5.1 / Cassels §12 / RJW Lem 5.14) and sits on top of a
genuinely-missing-from-mathlib BIG object — the project's integral logarithm `pZpLog` (and the
analytic `padicLog` underneath, `YES-but-generalise-first`). So while the *declaration* is SMALL,
its mathlib fate is inherited from the BIG development it certifies.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only — it does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check is **n/a** (one-line note).
The body is a multi-step rewrite chain, not a one-expression delegation in any case; for theorems
the relevant analogue is Phase 6 (composability), handled below.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm maps 1+pℤ_p into pℤ_p principal units odd prime log(x) ≡ 0 mod p"                     | yes  | for `p > 2`, the image of `pℤ_p` (i.e. of `1+pℤ_p`) under `log_p` **is `pℤ_p`**; `log_p(1+x)=x−x²/2+x³/3−…` converges for `x∈𝔪_K`; the linear term dominates so `‖log x‖=‖x−1‖` | arXiv 1904.09850 / 1907.06437 ("On the image of p-adic logarithm on principal units"); the `r=1`, `e=1` case of the general `log_p:1+𝔪^r ≅ 𝔪^r` |
|  2 | WebSearch (general form: the iso) | "p-adic exp log isomorphism 1+pℤ_p pℤ_p Washington cyclotomic fields Cassels local fields odd prime"    | yes  | for `p≠2`, `pℤ_p ≅ 1+pℤ_p` via exp/log; `log_p` induces an iso `1+𝔪_K^r → 𝔪_K^r` **iff `r > e/(p−1)`** (`e` = ramification index); `log_p(zw)=log_p z + log_p w` | Washington *Introduction to Cyclotomic Fields* §5.1; J. Thorne / K. Conrad Cambridge notes; Sharifi AWS 2018 — the iso of principal units is unanimous |
|  3 | WebSearch (named-after / aliases / the isometry) | "Keith Conrad p-adic logarithm isometry |log(1+y)|=|y| converges disk p-adic fields"                  | yes  | `log(1+x)` converges on `‖x‖<1`; **for `y∈pℤ_p`, `|log(1+y)|_p=|y|_p`** (the isometry); `log` inverts `exp` on the matched balls | K. Conrad `strassmannapplication.pdf` (states the isometry on `y∈pℤ_p` verbatim) and `infseriespadic.pdf`; this isometry **is** the project's `norm_padicLog` |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + history of `log` mapping `1+pℤ_p` into `pℤ_p` for odd `p`, and the `p=2` failure") | n/a  | —                                | ChatGPT/OpenAI MCP server **not configured** in this environment (deferred-tool search exposes no `mcp__chatgpt`/`openai` tool; `/setup-chatgpt` not run; the surfaced MCP tools are Asana/Atlassian/etc. auth only). Recorded n/a with reason. The 3 WebSearch queries + Wikipedia + PlanetMath + the module's own citations (RJW, Cassels §12, Washington §5.1) more than cover the standard-form question; the verdict does not hinge on this channel. (Same as the sibling reports.) |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories confirmed absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic logarithm / exponential / convergence radius / image on principal units                          | partial | nLab has no standalone p-adic-logarithm page; the general nonarch-analytic picture routes through the `valuation` page. PlanetMath ("p-adic exponential and p-adic logarithm") gives the clean statement: `log_p` defined for `|x−1|_p<1`, inverse of `exp_p`, `log_p(zw)=log_p z+log_p w` | not a categorical concept; nLab has no "log(1+pℤ_p) = pℤ_p" lemma. PlanetMath substitutes as the encyclopaedic source |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (an integrality congruence `log x ≡ 0 mod p` for a concrete series on a subgroup of `ℤ_p`). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic-series integrality on `ℤ_p`; no scheme/sheaf content). |
|  9 | MathOverflow / Math.StackExchange| "p-adic logarithm 1+pℤ_p isomorphic pℤ_p odd prime; p=2 fails 2-adic log principal units"                | yes  | community/expository consensus: for `p≠2`, `log: 1+pℤ_p → pℤ_p` is a (topological) iso; **for `p=2` the `r=1` map `1+𝔪_K→𝔪_K` is NOT an iso** (one needs `1+4ℤ_2≅4ℤ_2`) | Gupta (UChicago REU 2018) "The p-adic integers, analytically and algebraically"; Chen (UChicago REU 2018); Matt Baker blog — matches the target incl. the `hp2:p≠2` exclusion |
| 10 | recent arXiv (last 5 years)      | image of p-adic log on principal units / iso `1+𝔪^r ≅ 𝔪^r`, `r>e/(p−1)`, ramification index (2024–2026) | yes  | arXiv 2601.18187 (Jan 2026, "On the Image of the p-adic Logarithm on Annuli of Principal Units"), 1907.06437v5 (2023), 1904.09850 reuse the classical iso + isometry verbatim; the precise image for `e ≥ p−1` is an active question | confirms no modern reformulation supersedes the classical statement; the `r=1, e=1` case (this target) is the elementary, settled one |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (the specific
"log maps `1+pℤ_p` into/onto `pℤ_p` / `log x ≡ 0 mod p`" image fact / the general exp–log iso
`pℤ_p ≅ 1+pℤ_p`, with the `r>e/(p−1)` threshold / the named "isometry `|log(1+y)|=|y|`, K. Conrad");
ChatGPT MCP recorded n/a with reason (server absent); local references recorded n/a with reason (no
dir); nLab checked (routes through PlanetMath); nCatLab / Stacks recorded n/a with reason;
MathOverflow/expository and recent arXiv each checked.

### Literature summary (Phase 3)

Concept identified as: **"the p-adic logarithm maps `1 + pℤ_p` into `pℤ_p` for odd `p`"** —
equivalently `log x ≡ 0 (mod p)` for `x ≡ 1 (mod p)`, the **inverse / log-image half** of the
exp–log isomorphism `pℤ_p ≅ 1 + pℤ_p` (`p ≠ 2`). The mechanism is the **isometry**
`|log x|_p = |x−1|_p` on the convergence ball (K. Conrad): the linear term of
`log x = (x−1) − (x−1)²/2 + …` dominates p-adically.

Sources agree on the standard form: **yes, unanimously.** Wikipedia, K. Conrad
`strassmannapplication.pdf` + `infseriespadic.pdf`, PlanetMath, the UChicago REU notes (Gupta,
Chen), J. Thorne / Cambridge notes, Sharifi AWS, Washington §5.1, Cassels §12, and arXiv
1904.09850 / 1907.06437 / 2601.18187 all state: *for `p ≠ 2`, `log` maps `1+pℤ_p` (iso-)onto `pℤ_p`*
(and `exp` inverts it), giving the iso of principal units; *for `p = 2` the `r=1` level fails*. The
reasoning is invariably `|log x|=|x−1|` plus `|x−1| ≤ 1/p < p^{-1/(p-1)}`. This is **exactly** the
project's internal proof (`norm_padicLog` + `coe_norm_le_inv_of_mem_span`).

Most general standard form: over **any complete discretely-valued nonarch field `K ⊇ ℚ_p`** with
ring of integers `𝒪_K`, maximal ideal `𝔪_K`, ramification index `e`, `log_p` induces an
**isomorphism** `1 + 𝔪_K^r ≅ 𝔪_K^r` for every `r > e/(p−1)`. The *specific* "`1+pℤ_p` on `ℤ_[p]`"
packaging here is the classical `K = ℚ_p` (`e = 1`), `r = 1` case — which holds **iff `p` is odd**
(`r=1 > 1/(p−1) ⟺ p−1>1 ⟺ p>2`), *precisely* the `hp2 : p ≠ 2` hypothesis. **The target is stated
only at `ℤ_[p]` / `ℚ_[p]`** — see Phase 4. Note the *isometry* underneath (`norm_padicLog`) **is**
already stated at general `L` in the project; only this integral wrapper is `ℚ_p`-specific.

Generality dimensions where the literature varies:
- **Base field / ring**: `ℤ_p` (this theorem) → the ring of integers `𝒪_K` of any complete nonarch field `K`, with `𝔪_K^r` in place of `pℤ_p`. The literature states the general-`𝒪_K` version (and the precise threshold `r > e/(p−1)`); the target picks the `K=ℚ_p`, `e=1`, `r=1` instance.
- **Conclusion strength**: the literature gives the full **iso** `1+𝔪^r ≅ 𝔪^r` (both directions + bijectivity); the target is only the log-image membership half (the exp direction is the sibling `pZpExp_sub_one_mem`; bijectivity is the round-trip `padicExp_padicLog`/`padicLog_padicExp`, which the project also has).
- **Packaging**: the literature ultimately bundles both directions into the iso of principal units `pℤ_p ≃ 1+pℤ_p`; the target is one membership fact feeding that bundle.

Disagreement with the literature: **none.** The target is a faithful, correctly-hypothesised
(`p ≠ 2`) Lean rendering of the standard "`log` maps `1+pℤ_p` into `pℤ_p`" fact, *specialised to
`ℚ_p`* and phrased via the junk-totalised integral logarithm `pZpLog`.

---

### Generality analysis — `pZpLog_mem`

Literature-standard form (from Phase 3): over the ring of integers `𝒪_K` of any complete nonarch
field `K ⊇ ℚ_p` with maximal ideal `𝔪_K` and ramification index `e`, `log_p` induces an iso
`1 + 𝔪_K^r ≅ 𝔪_K^r` for `r > e/(p−1)` — in particular `log x ∈ 𝔪_K^r` for `x ∈ 1+𝔪_K^r`. The
classical case is `K = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`, `e = 1`, `r = 1` (valid iff `p` odd).

| # | Parameter / hypothesis                | Current Lean form                | Literature-standard form      | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------------|-------------------------------|---------------------|---------------------------------|
| 1 | base ring fixed to `ℤ_[p]` (`pZpLog : ℤ_[p] → ℤ_[p]`) | integral log on `ℤ_[p]`, value in `ℤ_[p]` | `log x ∈ 𝔪_K^r ⊆ 𝒪_K`, `𝒪_K` ring of ints of any complete nonarch `K ⊇ ℚ_p`, `r>e/(p−1)` | **yes** (in principle) | the underlying *isometry* `norm_padicLog` already runs at abstract `L`; but the *integral* statement is built on `pZpLog`, a `ℚ_p`-specific junk-totalised `Subtype` def using `PadicInt`'s `‖·‖≤1` certificate and span API. A general-`𝒪_K` version needs (i) a general "integral log" on a DVR and (ii) a general `𝔪_K^r ⊆ log-ball` lemma with the `r>e/(p−1)` threshold — real new infrastructure, not a rewrite. |
| 2 | `hp2 : p ≠ 2`                        | `p ≠ 2`                          | `r > e/(p−1)`, here `1 > 1/(p−1)` ⟺ `p > 2` | **NO**              | essential: the `p = 2`, `r=1` statement is **false** (the `r=1` map `1+2ℤ_2 → 2ℤ_2` is not an iso; one needs `1+4ℤ_2≅4ℤ_2`). The hypothesis is exactly the `r=1`-validity threshold. |
| 3 | `hx : x − 1 ∈ Ideal.span {(p)}`      | `x ∈ 1+pℤ_p`                    | `x ∈ 1+𝔪_K^r`                 | NO (within `ℤ_[p]`) | `pℤ_p` *is* the maximal ideal of `ℤ_p` (`PadicInt.maximalIdeal_eq_span_p`); within the `ℚ_p` instance, `r=1`, this is the largest set on which the inclusion holds via this route. |
| 4 | conclusion `pZpLog p x ∈ span {p}`   | `log x ≡ 0 (mod p)`            | `log x ∈ 𝔪_K^r`               | NO                  | matches the natural p-adic integrality statement (the log-image half of the iso). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD — but in a *specialisation* sense, not a
weakening-of-hypotheses sense.** The literature/general form runs over `𝒪_K`-of-any-complete-nonarch-`K`
with the threshold `r > e/(p−1)`; the target hard-codes `K = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`, `e=1`, `r=1`.
The odd-`p` and membership hypotheses are *exactly right* (row 2 cannot be weakened; the `p=2`, `r=1`
case is genuinely false).
Number of *hypothesis*-weakening opportunities found: **0** (hypotheses are sharp).
Number of *base-ring generalisation* opportunities: **1** (the `𝒪_K`-of-`K` version with the `r>e/(p−1)` threshold, row 1).
Proposed restatement (if pursued as a mathlib contribution): the abstract version, "for `K ⊇ ℚ_p`
complete nonarch with ramification index `e`, the integral log on `𝒪_K` maps `1+𝔪_K^r` into `𝔪_K^r`
when `r > e/(p−1)`". Its isometry half is already `norm_padicLog` (general `L`); the
*integral-image* packaging needs a general "integral log on a DVR" plus a general
`𝔪_K^r ⊆ log-ball` lemma (not the `PadicInt`-specific `inExpBall_of_mem_span` /
`coe_norm_le_inv_of_mem_span`).
Cost of restatement: **MODERATE–EXPENSIVE** (a general integral-log construction + DVR
maximal-ideal-in-ball lemma is new work; the isometry engine already generalises).

Crucially, this Phase-4 finding is **subordinate to** the development's verdict: the whole `pZpLog`
/ `padicLog` machinery is governed by an upstreaming decision (`padicLog` → `YES-but-generalise-first`;
`norm_padicLog` → `YES-but-generalise-first`; the integral wrapper `pZpLog` → `BORDERLINE`), so
"which generality to state this integral fact at" is itself part of that deferred design question,
not a self-resolving downgrade. Per the Bourbaki-2.0 guidance, the MODERATE–EXPENSIVE cost does
**not** by itself downgrade the verdict.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | the hypotheses are already a `≠` + a membership; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | the underlying convergence/isometry is already filter-based (via `norm_padicLog` ← `summable_padicLog_terms`); the integrality statement is the right discrete `_ ∈ span {p}` packaging |
|  3 | construct an object → universal-property class?                                                            | **yes**  | the mathlib-idiomatic object is the exp/log **isomorphism `(1 + pℤ_p) ≃ pℤ_p`** (a bundled `MulEquiv`/group iso of principal units onto the additive ideal / `AddEquiv`), of which this membership is the *well-definedness of the forward (log) map* ("log lands in `pℤ_p`"). Mathlib would likely want the bundled iso with this as a private well-definedness step | the bundled iso composes with mathlib's `Units` / `IsUnit` / principal-unit and group API — but this is a property of the *whole development*, not this corollary; it reinforces that the corollary should not travel alone |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | `pℤ_p` is already `Ideal.span {p}` / the maximal ideal; `1+pℤ_p` is the natural coset; bundled |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | yes      | the `ℚ_p`/`ℤ_p` hard-coding could be a general complete-nonarch-`K`-with-ring-of-integers statement with the `r>e/(p−1)` threshold (Phase 4b row 1) — but `pZpLog` itself is `ℚ_p`-specific; generalising is development-level work | a general-`𝒪_K` version would unify with the abstract `L`-API the project already has for the isometry — again a *development*-level point |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | no free index here; `p` is the fixed prime |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this corollary's* signature as a standalone). The two real
organisational levers — (3) bundle the exp–log `1+pℤ_p ≃ pℤ_p` iso of principal units, with this
membership as the log map's private well-definedness step, and (5) state it over a general ring of
integers `𝒪_K` with the `r>e/(p−1)` threshold — are both properties of the **surrounding p-adic-log
development**, not of this single integrality corollary. They are the *development's* design
questions. One-line reason this corollary is not itself a modernisation move: it is a concrete
integrality statement already in idiomatic `_ ∈ Ideal.span {p}` form; the only modernisation choices
live one (or two) layers up, in the `pZpLog` / `padicLog` / `summable_padicLog_terms` upstreaming
decision.

---

### Diamond / defeq risk — `pZpLog_mem`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`. The
*def* it is about, `pZpLog`, carries its own Phase-4.5 assessment in `PadicLFunctions.pZpLog.md` —
junk-totalised `dite` on a `Subtype` membership certificate — but that is a separate declaration,
not the target here.)

---

### Mathlib search-status: `pZpLog_mem`

[A] Lean-Finder       "p-adic log lands in pZp", "log x ≡ 0 mod p integral logarithm", "log maps 1+pZp into pZp"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D), plus reading the candidate decls' actual statements.
[B] Loogle            `_ - 1 ∈ Ideal.span {↑p} → _ ∈ Ideal.span {↑p}`, `pZpLog _ _ ∈ _`, `p ≠ 2 → _ - 1 ∈ Ideal.span {↑p} → _ ∈ Ideal.span {↑p}`   no hit: `pZpLog` is project-only (no such constant in mathlib); the generic shape `x − 1 ∈ I → f x ∈ I` has no p-adic-log instance in mathlib (there is no `padicLog`/`pZpLog` to key on).
[C] LeanSearch        "p-adic logarithm maps 1 + p Z_p into p Z_p", "integral logarithm congruent to 0 mod p", "log of principal unit in maximal ideal"   no p-adic hit: surfaces the real/complex `Real.log`/`Complex.log` and `Polynomial`-formal-log families only; nothing nonarchimedean, nothing about `1+pℤ_p`/`pℤ_p` / principal units of `ℤ_p`.
[D] Grep mathlib src  `grep -rniE "def padicLog|p-adic log|log.*span|principal unit|onePAdicPow"` over `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/` and `Analysis/`   **NO p-adic log anywhere** in mathlib (confirmed: whole-tree grep for `padicLog`/`def padicLog` returns nothing; no `pZpLog`, no `onePAdicPow`, no "log maps into `pℤ_p`"). `PadicIntegers.lean` has only the *infrastructure* this proof uses: `norm_le_pow_iff_mem_span_pow` (L466), `norm_def` (L191), `coe_sub` (L109), `coe_one` (L112), `maximalIdeal_eq_span_p` (L506). The only `Log` in `RingTheory/PowerSeries/Log` (imported by this file) is the *purely formal* `PowerSeries.log` — no convergence, no analytic evaluation, no integrality.
[E] Name pattern      `pZpLog`, `padicLog`, `log_mem_span`, `log_mem_maximalIdeal`, `onePAdicPow`   `pZpLog` / `padicLog` / `onePAdicPow` do **not** exist in mathlib (all are project-only, in `PadicExp.lean` / `Interpolation/Branches.lean`). No `log_mem_span`-style lemma about p-adic integers exists.

Searched for both:
- the user's current form (`pZpLog p x ∈ pℤ_p` for `x ∈ 1+pℤ_p`, `p ≠ 2`) — **not** in mathlib (the constant `pZpLog` does not exist there).
- the literature-standard / general form ("`log` maps `1+𝔪_K^r` into `𝔪_K^r` for `r>e/(p−1)`" over a complete nonarch field's ring of integers, and the real/complex `Log` families) — mathlib has neither the p-adic statement nor any nonarchimedean (integral) logarithm to state it about.

**Why nothing in mathlib settles this.** There is simply **no p-adic logarithm in mathlib** — not
the analytic `padicLog`, not the integral `pZpLog`, only the formal `PowerSeries.log` (no
convergence/evaluation) — so there is no constant to make the "`log x ∈ pℤ_p`" statement *about*,
and a fortiori no mathlib lemma asserting it. The real/complex `Log` families are the wrong regime
(archimedean; an isometry `‖log x‖=‖x−1‖` and an image landing in `pℤ_p` are *non*archimedean
phenomena). The genuine mathlib pieces in the dependency chain are only the `PadicInt` plumbing
lemmas (`norm_le_pow_iff_mem_span_pow`, `norm_def`, `coe_sub`, `coe_one`); the two mathematically
substantive inputs — `norm_padicLog` (the isometry, itself `YES-but-generalise-first`) and
`coe_norm_le_inv_of_mem_span` (the norm bound, itself `NO-composable-from-mathlib`) — are
**project** lemmas, not mathlib.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard general form).
And — the decisive structural point — its two substantive building blocks are themselves *not* in
mathlib (one `YES-but-generalise-first`, one `NO-composable`), and the def it certifies (`pZpLog`,
`BORDERLINE`) is project-only.

---

### Call sites — `pZpLog_mem`

Internal use count: **3** (within the project, NOT counting the declaring theorem)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`, 2 sites) + the declaring file (`PadicExp.lean`, 1 site)

| Caller file:line               | Usage pattern (one-line excerpt)                                                              |
|--------------------------------|-----------------------------------------------------------------------------------------------|
| ResidueZeta.lean:107           | `have hℓmem : ℓ ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hy` — inside `norm_onePAdicPow_sub_one` (the character is a norm isometry in the exponent: `‖y^t−1‖=‖t‖·‖y−1‖`) |
| ResidueZeta.lean:239           | `pZpLog_mem p hp2 (PadicInt.angleUnit_sub_one_mem p u)` — inside `tendsto_sub_one_mul_zetaPBranch` (residue/limit of the branch zeta) |
| PadicExp.lean:1115             | `have hℓmem : ℓ ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hx` — inside `padicExp_smul_padicLog_eq_onePAdicPow` (the `x^s=exp(s·log x)` bridge, RJW Lem 5.14 second half) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - **(none)** — every place that needs "`log x ∈ pℤ_p`" (or, immediately downstream,
    "`t · log x ∈ pℤ_p`" via `Ideal.mul_mem_left`) calls `pZpLog_mem` rather than re-deriving the
    norm bound inline. This is the **opposite** of its exp sibling `pZpExp_sub_one_mem` (K = 0,
    bypassed). The integrality membership is genuinely consumed as named API here.

What the call-sites pattern tells you: **K = 3 internal uses, no inline re-derivation, including 2
uses in a *different* file** (`ResidueZeta.lean`). Per the Phase-6 signal table, `K ≥ 3` internal
uses with consumers depending on it (and cross-file use) is a **YES-leaning** composability signal —
this is real, load-bearing project API, not a thin unused certificate. It feeds the load-bearing
exponent-isometry `norm_onePAdicPow_sub_one` and the residue-zeta limit `tendsto_sub_one_mul_zetaPBranch`,
both of which are core to the residue-zeta development. This is the **sharpest single contrast** with
the exp sibling and is what keeps the YES bucket in play (rather than the NO-leaning the sibling
got from `K = 0`).

---

### Composition check (Phase 6)

Can `pZpLog_mem` be derived **from mathlib** in ≤3 chained calls?

Attempt 1: a mathlib "log maps `1+𝔪` into `𝔪`" lemma applied to `x ∈ 1+pℤ_p`.
  - Mathlib decls used: (none exist).
  - Result: **fails** — mathlib has no p-adic logarithm at all (Phase 5), so there is no such lemma
    and no constant `pZpLog`/`padicLog` to invoke. This is a missing *whole development*, not a missing call.

Attempt 2: the project's actual body — `rw […, pZpLog_coe …, norm_padicLog …, …]; exact coe_norm_le_inv_of_mem_span …`.
  - Decls used: mathlib `PadicInt.{norm_le_pow_iff_mem_span_pow, norm_def, coe_sub, coe_one}` + `zpow_*`
    plumbing; **project** `pZpLog_coe`, `norm_padicLog`, `inExpBall_of_mem_span`,
    `coe_norm_le_inv_of_mem_span`.
  - Result: **this is a clean rewrite chain — but its two mathematically substantive steps are
    PROJECT lemmas, not mathlib.** `norm_padicLog` is the genuine isometry (itself
    `YES-but-generalise-first`, built on `summable_padicLog_terms`); `coe_norm_le_inv_of_mem_span` is
    `NO-composable-from-mathlib`; `pZpLog_coe` and `inExpBall_of_mem_span` are project lemmas too. So
    the composition does **not** discharge the theorem from *mathlib* building blocks.

Attempt 3: assemble from mathlib's genuine primitives only (`PadicInt.norm_le_pow_iff_mem_span_pow` +
the formal `PowerSeries.log` / real-complex `Log` API + valuation lemmas).
  - Result: **fails** — `PowerSeries.log` is purely formal (no convergence/evaluation); the
    archimedean `Real.log`/`Complex.log` are the wrong regime (they give neither `‖log x‖=‖x−1‖`
    p-adically nor convergence-on-`1+pℤ_p`). Reconstructing the isometry is exactly re-proving
    `norm_padicLog` (a multi-lemma nonarchimedean argument). Not a ≤3-call composition.

Conclusion: **NOT-COMPOSABLE *from mathlib*.** The theorem is a tidy rewrite chain, but its two
substantive inputs are project lemmas (one `YES-but-generalise-first`, one `NO-composable`) about a
project-only def mathlib lacks entirely. Assembling it from mathlib's actual primitives would
require first building the whole nonarchimedean log development. This rules out
`NO-composable-from-mathlib` (which requires composition from *mathlib* decls in ≤3 calls). It
equally rules out `NO-mathlib-has-it` (Phase 5: no p-adic log in mathlib).

---

## Verdict: `pZpLog_mem`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** a textbook-standard fact — "for odd `p`, `log` maps
  `1+pℤ_p` (iso-)onto `pℤ_p`" (`log x ≡ 0 mod p`), the log-image half of the exp–log iso of principal
  units `pℤ_p ≅ 1+pℤ_p` (K. Conrad `strassmannapplication.pdf`/`infseriespadic.pdf`, PlanetMath,
  Wikipedia, Washington §5.1, Cassels §12, RJW Lem 5.14, arXiv 1904.09850/1907.06437/2601.18187).
  Sources unanimous, including the sharp `p ≠ 2` distinction (the `r=1` map fails at `p=2`; it is the
  exact validity threshold `r>e/(p−1)`). The mechanism `|log x|=|x−1|` is precisely the project's
  `norm_padicLog`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** in the *specialisation* sense —
  hypotheses are sharp (`p ≠ 2` cannot be dropped; the `p=2`, `r=1` claim is false), but the theorem
  is hard-coded to `K = ℚ_p` / `ℤ_p` (`e=1`, `r=1`) whereas the standard fact holds over `𝒪_K` of any
  complete nonarch field with the threshold `r>e/(p−1)`. Modern-idiom (4c): the real organisational
  moves (general-`𝒪_K` version; bundle the exp–log iso of principal units) are *development*-level,
  not this corollary's. Cost MODERATE–EXPENSIVE — which, per Bourbaki-2.0, does not by itself downgrade.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic log at all (analytic or integral); only
  the formal `PowerSeries.log`; the constant `pZpLog` is project-only; and the two substantive
  building blocks are themselves missing from mathlib (`norm_padicLog` `YES-but-generalise-first`,
  `coe_norm_le_inv_of_mem_span` `NO-composable`). Only `PadicInt` plumbing lemmas are genuine mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the body is a rewrite chain whose
  substantive steps are *project* lemmas about a project-only def; from mathlib's real primitives it
  is a whole-development reconstruction.
- Call sites (Phase 6.0): **K = 3**, no inline re-derivation, **2 of them cross-file** in
  `ResidueZeta.lean` (`norm_onePAdicPow_sub_one`, `tendsto_sub_one_mul_zetaPBranch`) + 1 in the
  declaring file (`padicExp_smul_padicLog_eq_onePAdicPow`). YES-leaning composability signal — this
  is genuinely load-bearing project API (the decisive contrast with the K=0, bypassed exp sibling).

**Rationale (why BORDERLINE — not YES, not NO):**

This theorem sits at the same intersection of pulls that made its exp sibling
`pZpExp_sub_one_mem`, the def `pZpLog`, and `pZpLog_coe` all BORDERLINE — which is the textbook
trigger for this verdict. On one side, it is a *true, named, textbook-standard,
genuinely-missing-from-mathlib* p-adic fact with sharp hypotheses (the `p ≠ 2` exclusion is real and
correct — it is exactly the `r > e/(p−1)` validity threshold at `e=1, r=1`), proved sorry-free, **and
it is genuinely load-bearing** (K = 3, including two cross-file consumers in the residue-zeta
development). That profile pulls strongly toward a YES bucket — more strongly than the exp sibling,
whose K = 0 pulled it toward NO. On the other side, **as a declaration it is a thin integrality
certificate about a project-only `def`** (`pZpLog`, the junk-totalised integral logarithm `ℤ_[p] →
ℤ_[p]` that mathlib has no analogue of, itself `BORDERLINE`), it adds **no new analysis** (its only
substantive inputs are the already-assessed project lemmas `norm_padicLog`, itself
`YES-but-generalise-first`, and `coe_norm_le_inv_of_mem_span`, itself `NO-composable`). And it is
decisively **not** `NO-mathlib-has-it` (mathlib has no p-adic log of any kind — only the formal
`PowerSeries.log` — and the substantive building blocks are absent; Phase 5) and **not**
`NO-composable-from-mathlib` (the composition is from *project* lemmas about a project def, not
mathlib; from mathlib it is a whole-development reconstruction; Phase 6). So neither NO bucket is
groundable in the evidence.

What actually decides this theorem's mathlib fate is **not** anything intrinsic to it — it is the
*same* upstreaming decision that governs the def it certifies (`pZpLog` → `BORDERLINE`) and the
development underneath it (`padicLog` → `YES-but-generalise-first`; `norm_padicLog` →
`YES-but-generalise-first`; `summable_padicLog_terms` → also a development-level call). Mathlib has
**no** nonarchimedean logarithm development. If the project upstreams that development as a unit, then
the natural mathlib form of *this* fact is the **general-`𝒪_K`** statement ("for `r > e/(p−1)`, `log`
maps `1+𝔪_K^r` into `𝔪_K^r`"), almost certainly bundled into the exp–log iso of principal units
`1+pℤ_p ≃ pℤ_p` as the log map's private well-definedness step (Phase 4c row 3) — so the right move
would be to *generalise-and-absorb* this into that PR, not ship the `ℚ_p`-hard-coded `pZpLog` wrapper
verbatim. If the project keeps the development local, this stays a load-bearing project-internal lemma
(K = 3) that need not go to mathlib at all. Because the high call-site count makes the YES pull real
here (it is not a candidate for dropping/inlining, unlike the exp sibling), the human question is
genuinely "ship the development (and at what generality / folded into which bundled iso)?" — not "is
this worth keeping?". The skill cannot choose between "upstream the whole exp/log development (and
restate this generally / fold it into the iso)" and "keep local" without the human; per the
anti-pattern guidance, a whole-development / EXPENSIVE-generalisation tradeoff is itself a BORDERLINE
question, not a self-resolving downgrade.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exp/log development** to mathlib
   as a unit (the analytic `padicLog`/`padicExp`, the convergence engines
   `summable_padicLog_terms`/`summable_padicExp_terms`, the isometries `norm_padicLog`/`norm_padicExp_sub_one`,
   the integral `pZpLog`/`pZpExp`, and the exp–log isomorphism of principal units `pℤ_p ≅ 1+pℤ_p`)?
   This theorem is the *log-image / forward-map well-definedness* fact of that development and should
   travel with it (most likely **generalised** / **folded into the iso**, see Q2–Q3), not alone.
   (Same governing question as for `pZpLog`, `padicLog`, `norm_padicLog`, and the exp sibling
   `pZpExp_sub_one_mem`.)
2. If yes to (1): should the mathlib statement be the **general** form — "for a complete
   nonarchimedean field `K ⊇ ℚ_p` with ramification index `e`, the integral logarithm maps `1+𝔪_K^r`
   into `𝔪_K^r` whenever `r > e/(p−1)`" (which needs a general integral-log construction + a general
   `𝔪_K^r ⊆ log-ball` lemma; the isometry half is already `norm_padicLog`) — rather than the
   `ℚ_p`-hard-coded `pZpLog`/`pℤ_p`/`r=1` wrapper this theorem is? (Cost MODERATE–EXPENSIVE; per the
   Bourbaki-2.0 guidance, cost does not by itself downgrade the verdict.)
3. If yes to (1): should this integrality fact be exposed as a standalone lemma at all, or only as a
   **private well-definedness step inside the bundled exp–log isomorphism** `(1 + pℤ_p) ≃ pℤ_p`
   (`MulEquiv`/group iso of principal units onto the additive ideal; Phase 4c row 3)? Mathlib would
   likely prefer the bundled iso as the public API, with "log lands in `pℤ_p`" internal to its
   construction. (Note: unlike the exp sibling, this lemma is *actually used* K = 3 times, so a
   project-local named lemma is justified regardless of the mathlib packaging choice.)
4. For consistency: should `pZpLog_mem` and its exp sibling `pZpExp_sub_one_mem` be resolved
   **together** (they are the two halves of the same iso)? The exp sibling is currently bypassed
   (K = 0) and a drop/inline candidate; this one is load-bearing (K = 3). If you upstream the
   development, both become well-definedness steps of the bundled iso and the K-asymmetry stops
   mattering; if you keep local, this one stays and the exp one might be inlined.

**Next action:** user answers the questions; re-run `/mathlibable pZpLog_mem` — preferably
**together with `/mathlibable PadicLFunctions.pZpLog`, `/mathlibable PadicLFunctions.norm_padicLog`,
`/mathlibable PadicLFunctions.padicLog`, and the exp halves `/mathlibable pZpExp_sub_one_mem` /
`PadicLFunctions.pZpExp`**, since this corollary's verdict is entirely governed by the (BIG,
multi-decl) upstreaming decision on the p-adic exp/log development it certifies. Likely resolutions:
  - "Upstream the nonarchimedean exp/log development" → this fact ships **as the general-`𝒪_K`
    statement (Q2), or as the log map's private well-definedness step in the bundled exp–log iso
    `1+pℤ_p ≃ pℤ_p` (Q3)** — i.e. effectively `YES-but-generalise-first` *folded into* the development
    PR, **not** as this verbatim `pZpLog` wrapper.
  - "Keep project-local" → drop from mathlib consideration; but **keep the lemma** (K = 3, load-bearing
    — do not inline it, in contrast to the bypassed exp sibling).

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable pZpLog_mem` — preferably
alongside `/mathlibable PadicLFunctions.pZpLog`, `/mathlibable PadicLFunctions.norm_padicLog`,
`/mathlibable PadicLFunctions.padicLog`, and the exp halves `/mathlibable pZpExp_sub_one_mem` /
`PadicLFunctions.pZpExp`, since this corollary's mathlib fate is governed by the (BIG, multi-decl)
upstreaming decision on the p-adic exp/log development (the def `pZpLog` it certifies, the isometry
`norm_padicLog`, and the principal-units iso `1+pℤ_p ≃ pℤ_p`) — to resolve to either
`YES-but-generalise-first` (folded into the nonarchimedean exp/log development PR as the general-`𝒪_K`
statement / the log map's well-definedness step in the bundled exp–log iso) or drop-from-mathlib-
consideration (but **keep** as a load-bearing project-internal lemma, K = 3).
