# `/mathlibable` report — `PadicLFunctions.pZpExp_sub_one_mem`

**Final verdict: `BORDERLINE-needs-human`**

This is a true, textbook-standard (K. Conrad *Infinite series in p-adic fields* / MIT
`exp.pdf` / Wikipedia "P-adic exponential function" / RJW Lem 5.14 / Washington §5.1 /
Cassels §12), genuinely-missing-from-mathlib p-adic fact — the *integral image-half* of
"for odd `p`, `exp` maps `pℤ_p` into the principal units `1 + pℤ_p`" — proved sorry-free.
But (a) it is a statement **about a project-only `def`** (`pZpExp`, the junk-totalised
integral exponential `ℤ_[p] → ℤ_[p]`) that mathlib does not have; (b) it has **zero call
sites** and is bypassed; and (c) its proof bottoms out on two *project* lemmas
(`norm_padicExp_sub_one`, itself `BORDERLINE`, and `coe_norm_le_inv_of_mem_span`, itself
`NO-composable-from-mathlib`), so mathlib has neither the statement nor its building blocks
in usable form. Its mathlib fate is therefore governed by the **same** human upstreaming
decision that governs the whole nonarchimedean exp/log development — exactly the situation
that makes a verdict a judgment call. Hence BORDERLINE, consistent with its siblings
`padicExp_converges_on_pZp` and `norm_padicExp_sub_one`.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1062` (kind: `theorem`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task's BUILD NOTE — the build is stale/slow here; Phase 0 source-fallback used). The file is part of `main` and elaborates; the target and its full dependency chain were read directly from `PadicExp.lean`. Baseline commit `d71766e`.
- decl `PadicLFunctions.pZpExp_sub_one_mem`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1062`
- kind:                      theorem
- has sorry:                 no (grep for `sorry`/`admit` over the whole file returns nothing)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=Σ xⁿ/n!` converges on the open ball `‖x‖ < p^{-1/(p-1)}` of a nonarchimedean complete normed `ℚ_p`-algebra field and is an isometry there; for odd `p` the ball contains `pℤ_p`; the log inverts it on the matched balls; realises `x^s := exp(s·log x)`, agreeing with the character `PadicInt.onePAdicPow`. Cites Cassels §12 and Washington, *Introduction to Cyclotomic Fields* §5.1.

---

### Statement (Phase 1)

`pZpExp_sub_one_mem` is a **theorem** stating the following:

> Let `p` be an **odd** prime. For every `x ∈ pℤ_p` (the maximal ideal `Ideal.span {p}` of `ℤ_p`),
> the integral p-adic exponential `pZpExp p x ∈ ℤ_[p]` satisfies `pZpExp p x − 1 ∈ pℤ_p`.

Mathematically this is the **integral image-half** of the classical statement "for `p ≠ 2`,
`exp` maps `pℤ_p` *into* `1 + pℤ_p` (the principal units of `ℤ_p`)" — the codomain half of the
isomorphism `pℤ_p ≅ 1 + pℤ_p` (Washington §5.1, Cassels §12, RJW Lem 5.14). The crux is the
**isometry** `‖exp(x) − 1‖ = ‖x‖` on the convergence ball (K. Conrad: the linear term of
`exp(x) − 1 = x + Σ_{n≥2} xⁿ/n!` dominates p-adically), combined with `‖x‖ ≤ p⁻¹` for
`x ∈ pℤ_p`. Together `‖exp(x) − 1‖ = ‖x‖ ≤ p⁻¹`, i.e. `exp(x) − 1 ∈ pℤ_p`. Here `pZpExp` is
the *junk-totalised integral* exponential: `pZpExp p x := ⟨exp x, _⟩ ∈ ℤ_[p]` when
`‖exp x‖ ≤ 1`, else `1`; on `pℤ_p` (odd `p`) it always takes the true branch (`pZpExp_coe`),
so the statement is the genuine "exp lands in `1 + pℤ_p`".

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- (No general `L`: the statement lives entirely at `L = ℚ_p` / `ℤ_p`, because `pZpExp : ℤ_[p] → ℤ_[p]` is `ℚ_p`-specific — it depends on `PadicInt`'s `Subtype` and span/valuation API.)

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — odd prime (so `pℤ_p` fits in the convergence ball; the `p = 2` failure is real — `exp` diverges on `2ℤ_2`).
- `{x : ℤ_[p]}` with `hx : x ∈ Ideal.span {(p : ℤ_[p])}` — i.e. `x ∈ pℤ_p`.

Conclusion (math): for odd `p`, the integral exponential of an element of `pℤ_p` is `≡ 1 (mod p)`; equivalently `exp` maps `pℤ_p` into the principal units `1 + pℤ_p`.

Conclusion (Lean): `pZpExp p x - 1 ∈ Ideal.span {(p : ℤ_[p])}`.

**Proof shape (load-bearing for the verdict).** A single rewrite chain ending in one
project lemma:

```lean
theorem pZpExp_sub_one_mem (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpExp p x - 1 ∈ Ideal.span {(p : ℤ_[p])} := by
  rw [← pow_one (p : ℤ_[p]), ← PadicInt.norm_le_pow_iff_mem_span_pow _ 1,
    PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one, pZpExp_coe p hp2 hx,
    norm_padicExp_sub_one (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx),
    zpow_neg, Nat.cast_one, zpow_one]
  exact coe_norm_le_inv_of_mem_span p hx
```

It rewrites `_ ∈ span {p}` to a norm bound via mathlib's `PadicInt.norm_le_pow_iff_mem_span_pow`,
pushes the coercion to `ℚ_[p]` (`norm_def`, `coe_sub`, `coe_one`), unfolds the integral exp to
the analytic `padicExp` on the true branch (`pZpExp_coe`), applies the **isometry**
`norm_padicExp_sub_one` to turn `‖exp x − 1‖` into `‖x‖`, and discharges `‖x‖ ≤ p⁻¹` with
`coe_norm_le_inv_of_mem_span`. The only non-trivial mathematical inputs are the two **project**
lemmas `norm_padicExp_sub_one` (the isometry on the ball) and `coe_norm_le_inv_of_mem_span` (the
norm bound on `pℤ_p`); everything else is `PadicInt` plumbing and `zpow` arithmetic.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent caveat).
Reason: as a *declaration* it is an integrality corollary — a short rewrite chain, not a `def`,
structure, or main result, and it is **not** named after a person. *However*, it is the Lean
realisation of a famous textbook clause (the "exp maps `pℤ_p` into `1+pℤ_p`" half of the exp/log
isomorphism, Washington §5.1 / Cassels §12 / RJW Lem 5.14) and it sits on top of a
genuinely-missing-from-mathlib BIG object — the project's integral exponential `pZpExp` (and the
analytic `padicExp` underneath). So while the *declaration* is SMALL, its mathlib fate is
inherited from the BIG development it certifies.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-liner check is **n/a** (one-line note).
The body is a multi-step rewrite chain, not a one-expression delegation in any case; for theorems
the relevant analogue is Phase 6 (composability), handled below.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic exponential maps pℤ_p into 1 + pℤ_p principal units odd prime exp(x) ≡ 1 mod p"                 | yes  | for `x` in the exp ball, `|exp(x)−1|_p = |x|_p`; image of exp is the ball of valuative radius `1/(p-1)` around `1`; for odd `p`, `exp(pℤ_p) ⊆ 1+pℤ_p` | K. Conrad *Infinite series in p-adic fields*; PlanetMath "p-adic exponential and logarithm"; Jack Thorne / K. Conrad notes; Leiden Ch.8; Gupta (UChicago REU) — the `|exp(x)−1|=|x|` isometry is stated verbatim and is exactly the codomain half of the iso |
|  2 | WebSearch (general form: the iso) | "p-adic exp log isomorphism 1 + pℤ_p principal units Washington cyclotomic fields Cassels local fields" | yes  | for `p ≠ 2`, `pℤ_p ≅ 1+pℤ_p` via exp/log; `log` is an isometry from the additive ball to the multiplicative ball `1+y`, `|y|<p^{-1/(p-1)}`; iso of principal units | Washington *Introduction to Cyclotomic Fields*; arXiv 1904.09850 "image of p-adic logarithm on principal units"; Sharifi AWS notes — "exp maps into `1+pℤ_p`" is the inverse direction, unanimous |
|  3 | WebSearch (named-after / aliases / the isometry) | "Keith Conrad p-adic exponential isometry |exp(x)−1|=|x| converges disk infinite series p-adic fields"  | yes  | exp converges on `‖x‖<p^{-1/(p-1)}`; **the linear term of `exp(x)−1` dominates p-adically, so `|exp(x)−1|=|x|`**; image = open ball of valuative radius `1/(p-1)` around `1` | K. Conrad `infseriespadic.pdf`; MIT `exp.pdf` "Exponential and logarithm in p-adic fields"; Wikipedia "P-adic exponential function" — this isometry IS the project's `norm_padicExp_sub_one`, and the target is its integral specialisation |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + history of `exp` mapping `pℤ_p` into `1+pℤ_p` for odd `p`, and the `p=2` failure") | n/a  | —                                | ChatGPT MCP server **not configured** in this environment (deferred-tool search exposes no `mcp__chatgpt`/`openai` tool; `/setup-chatgpt` not run). Recorded n/a with reason. The 3 WebSearch queries + Wikipedia + the module's own citations (RJW, Cassels §12, Washington §5.1) more than cover the standard-form question; the verdict does not hinge on this channel. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` symlink) | both directories confirmed absent on this machine — recorded n/a. The module docstring's inline citations (RJW TeX 1892–1897 "as stated"; Cassels §12; Washington §5.1) serve as the literature anchor. |
|  6 | nLab                             | p-adic exponential / convergence valuative radius / image ball around `1`                                | partial | nLab has no standalone p-adic-exponential page; routes through the general `valuation` page. The general nonarch-analytic picture (convergence on valuative radius `1/(p-1)`, image a ball around `1`) is consistent with #1–#3 | not a categorical concept; nLab has no "exp(pℤ_p) ⊆ 1+pℤ_p" lemma |
|  7 | nCatLab (if categorical)         | —                                                                                                       | n/a  | —                                | not a categorical concept (an integrality congruence `exp(x) ≡ 1 mod p` for a concrete series on a subgroup of `ℤ_p`). |
|  8 | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | —                                | not an algebraic-geometry concept (analytic-series integrality on `ℤ_p`; no scheme/sheaf content). |
|  9 | MathOverflow / Math.StackExchange| "p-adic exp converges on pℤ_p; image in 1+pℤ_p; p=2 vs odd p"                                            | yes  | community consensus: for `p ≠ 2`, `exp: pℤ_p → 1+pℤ_p` is a (topological) iso onto principal units; the 2-adic exp does **not** converge on `2ℤ_2` | matches the target incl. the `hp2 : p ≠ 2` exclusion; textbook-standard, never disputed |
| 10 | recent arXiv (last 5 years)      | image of p-adic logarithm on principal units / p-adic exponentiation                                     | partial | arXiv 1904.09850, 1907.06437 (image of the `p`-adic / `2`-adic log on principal units), 2602.16433 (Hensel minimality, p-adic exponentiation) reuse the classical radius + the `exp(pℤ_p) ⊆ 1+pℤ_p` inclusion verbatim | confirms no modern reformulation supersedes the classical statement; it is used as a known fact |

The protocol passed: WebSearch ran **3** distinct queries at three generality levels (the specific
"exp maps `pℤ_p` into `1+pℤ_p` / `exp(x) ≡ 1 mod p`" image-inclusion / the general exp–log iso
`pℤ_p ≅ 1+pℤ_p` of principal units it is half of / the named "isometry `|exp(x)−1|=|x|`, K. Conrad");
ChatGPT MCP recorded n/a with reason (server absent); local references recorded n/a with reason (no
dir); nLab checked; nCatLab / Stacks recorded n/a with reason; MathOverflow and recent arXiv each
checked.

### Literature summary (Phase 3)

Concept identified as: **"the p-adic exponential maps `pℤ_p` into `1 + pℤ_p` for odd `p`"** —
equivalently `exp(x) ≡ 1 (mod p)` for `x ∈ pℤ_p`, the **codomain / image half** of the exp–log
isomorphism `pℤ_p ≅ 1 + pℤ_p` (`p ≠ 2`). The mechanism is the **isometry** `|exp(x)−1|_p = |x|_p`
on the convergence ball (K. Conrad): the linear term of `exp(x)−1 = x + Σ_{n≥2} xⁿ/n!` dominates
p-adically.

Sources agree on the standard form: **yes, unanimously.** Wikipedia, K. Conrad
`infseriespadic.pdf`, the MIT note `exp.pdf`, Jack Thorne / Cambridge notes, PlanetMath, Leiden
Ch.8, Washington §5.1, and MathOverflow all state: *for `p ≠ 2`, `exp` maps `pℤ_p` into `1+pℤ_p`*
(and `log` inverts it), giving the iso of principal units; *for `p = 2` it fails on `2ℤ_2`*. The
reasoning is invariably `|exp(x)−1|=|x|` plus `|x| ≤ 1/p < p^{-1/(p-1)}`. This is **exactly** the
project's internal proof (`norm_padicExp_sub_one` + `coe_norm_le_inv_of_mem_span`).

Most general standard form: over **any complete nonarchimedean field `L ⊇ ℚ_p`**, `exp` maps the
maximal ideal `𝔪` of its ring of integers `𝒪` into `1 + 𝔪` (for odd residue characteristic). The
*specific* "`pℤ_p` on `ℤ_[p]`" packaging here is the classical `ℚ_p` case. **The target is stated
only at `ℤ_[p]` / `ℚ_[p]`** — see Phase 4. Note the *isometry* underneath (`norm_padicExp_sub_one`)
**is** already stated at general `L` in the project; only this integral wrapper is `ℚ_p`-specific.

Generality dimensions where the literature varies:
- **Base field / ring**: `ℤ_p` (this theorem) → the ring of integers `𝒪` of any complete nonarch
  field, with maximal ideal `𝔪` in place of `pℤ_p`. The literature states the general-`𝒪` version
  too; the target picks the `ℚ_p` instance.
- **Conclusion strength**: the literature pairs this with the matching log direction (the full iso);
  the target is only the exp-image half (the inverse, log-image, is the sibling `pZpLog_mem`).
- **Packaging**: the literature ultimately bundles both directions into the iso of principal units
  `pℤ_p ≃ 1+pℤ_p`; the target is one membership fact feeding that bundle.

Disagreement with the literature: **none.** The target is a faithful, correctly-hypothesised
(`p ≠ 2`) Lean rendering of the standard "`exp` maps `pℤ_p` into `1+pℤ_p`" fact, *specialised to
`ℚ_p`* and phrased via the junk-totalised integral exponential `pZpExp`.

---

### Generality analysis — `pZpExp_sub_one_mem`

Literature-standard form (from Phase 3): over the ring of integers `𝒪` of any complete nonarch
field `L ⊇ ℚ_p` with maximal ideal `𝔪`, for `p` odd, `exp(x) − 1 ∈ 𝔪` for every `x ∈ 𝔪` (because
`|exp(x)−1|=|x| ≤` the uniformiser norm). The classical case is `L = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`.

| # | Parameter / hypothesis                | Current Lean form                | Literature-standard form      | Weaker form exists? | Reason it can/can't be weakened |
|---|---------------------------------------|----------------------------------|-------------------------------|---------------------|---------------------------------|
| 1 | base ring fixed to `ℤ_[p]` (`pZpExp : ℤ_[p] → ℤ_[p]`) | integral exp on `ℤ_[p]`, value in `ℤ_[p]` | `exp(x)−1 ∈ 𝔪 ⊆ 𝒪`, `𝒪` ring of ints of any complete nonarch `L ⊇ ℚ_p` | **yes** (in principle) | the underlying *isometry* `norm_padicExp_sub_one` already runs at abstract `L`; but the *integral* statement is built on `pZpExp`, a `ℚ_p`-specific junk-totalised `Subtype` def using `PadicInt`'s `‖·‖≤1` certificate and span API. A general-`𝒪` version needs (i) a general "integral exp" on a DVR and (ii) a general `𝔪 ⊆ exp-ball` lemma — real new infrastructure, not a rewrite. |
| 2 | `hp2 : p ≠ 2`                        | `p ≠ 2`                          | `p ≠ 2` (odd `p`)             | **NO**              | essential: the `p = 2` statement is **false** (`exp` diverges on `2ℤ_2`; the image claim fails). The hypothesis is exactly right. |
| 3 | `hx : x ∈ Ideal.span {(p)}`          | `x ∈ pℤ_p`                       | `x ∈ 𝔪` (maximal ideal)       | NO (within `ℤ_[p]`) | `pℤ_p` *is* the maximal ideal of `ℤ_p` (`PadicInt.maximalIdeal_eq_span_p`); within the `ℚ_p` instance this is already the largest set on which the inclusion is asserted via this route. |
| 4 | conclusion `pZpExp p x − 1 ∈ span {p}` | `exp(x) ≡ 1 (mod p)`            | `exp(x)−1 ∈ 𝔪`                | NO                  | matches the natural p-adic integrality statement (the codomain half of the iso). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD — but in a *specialisation* sense, not a
weakening-of-hypotheses sense.** The literature/general form runs over `𝒪`-of-any-complete-nonarch-`L`;
the target hard-codes `L = ℚ_p`, `𝒪 = ℤ_p`, `𝔪 = pℤ_p`. The odd-`p` and membership hypotheses are
*exactly right* (row 2 cannot be weakened; the `p=2` case is genuinely false).
Number of *hypothesis*-weakening opportunities found: **0** (hypotheses are sharp).
Number of *base-ring generalisation* opportunities: **1** (the `𝒪`-of-`L` version, row 1).
Proposed restatement (if pursued as a mathlib contribution): the abstract version, "for `L ⊇ ℚ_p`
complete nonarch of odd residue char, an integral exp on `𝒪` maps `𝔪` into `1+𝔪`". Its isometry
half is already `norm_padicExp_sub_one` (general `L`); the *integral-codomain* packaging needs a
general "integral exp on a DVR" plus a general `𝔪 ⊆ ball` lemma (not the `PadicInt`-specific
`inExpBall_of_mem_span` / `coe_norm_le_inv_of_mem_span`).
Cost of restatement: **MODERATE–EXPENSIVE** (a general integral-exp construction + DVR
maximal-ideal-in-ball lemma is new work; the isometry engine already generalises).

Crucially, this Phase-4 finding is **subordinate to** the development's verdict: the whole `pZpExp`
/ `padicExp` machinery is governed by an upstreaming decision (`padicExp` → `NO-mathlib-has-it`
with the surrounding *theorems* flagged as the real missing API; `norm_padicExp_sub_one` →
`BORDERLINE`), so "which generality to state this integral fact at" is itself part of that deferred
design question, not a self-resolving downgrade.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|---------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | the hypotheses are already a `≠` + a membership; nothing to bundle |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | — | the underlying convergence/isometry is already filter-based (via `norm_padicExp_sub_one` ← `summable_padicExp_terms`); the integrality statement is the right discrete `_ ∈ span {p}` packaging |
|  3 | construct an object → universal-property class?                                                            | **yes**  | the mathlib-idiomatic object is the exp/log **isomorphism `pℤ_p ≃ (1 + pℤ_p)`** (a bundled `MulEquiv`/group iso of principal units / `AddEquiv`), of which this membership is the *codomain* sub-fact ("exp lands in `1+pℤ_p`"). Mathlib would likely want the bundled iso with this as a private well-definedness step | the bundled iso composes with mathlib's `Units` / `IsUnit` / principal-unit and group API — but this is a property of the *whole development*, not this corollary; it reinforces that the corollary should not travel alone |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | `pℤ_p` is already `Ideal.span {p}` / the maximal ideal; `1+pℤ_p` is the natural coset; bundled |
|  5 | field-specific → weaken typeclass hierarchy?                                                               | yes      | the `ℚ_p`/`ℤ_p` hard-coding could be a general complete-nonarch-`L`-with-ring-of-integers statement (Phase 4b row 1) — but `pZpExp` itself is `ℚ_p`-specific; generalising is development-level work | a general-`𝒪` version would unify with the abstract `L`-API the project already has for the isometry — again a *development*-level point |
|  6 | 1-categorical → higher-categorical?                                                                        | no       | — | n/a |
|  7 | concrete index ℕ/ℤ/ℝ → arbitrary additive structure?                                                      | no       | — | no free index here; `p` is the fixed prime |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this corollary's* signature as a standalone). The two real
organisational levers — (3) bundle the exp–log `pℤ_p ≃ 1+pℤ_p` iso of principal units, with this
membership as a private well-definedness step, and (5) state it over a general ring of integers
`𝒪` — are both properties of the **surrounding p-adic-exp development**, not of this single
integrality corollary. They are the *development's* design questions. One-line reason this corollary
is not itself a modernisation move: it is a concrete integrality statement already in idiomatic
`_ ∈ Ideal.span {p}` form; the only modernisation choices live one (or two) layers up, in the
`pZpExp` / `padicExp` / `summable_padicExp_terms` upstreaming decision.

---

### Diamond / defeq risk — `pZpExp_sub_one_mem`

**n/a — declaration kind is `theorem`.** (Phase 4.5 runs only for `def`/`class`/`instance`. The
*def* it is about, `pZpExp`, would carry its own Phase-4.5 assessment — junk-totalised `dite` on a
`Subtype` membership certificate — but that is a separate declaration, not the target here.)

---

### Mathlib search-status: `pZpExp_sub_one_mem`

[A] Lean-Finder       "p-adic exp lands in 1+pZp", "exp x ≡ 1 mod p integral exponential"   n/a: Lean-Finder web UI not callable in this environment — substituted with exhaustive grep over the mathlib tree (method D), plus reading the candidate decls' actual statements.
[B] Loogle            `_ ∈ Ideal.span {↑p} → _ - 1 ∈ Ideal.span {↑p}`, `pZpExp _ _ - 1 ∈ _`, `p ≠ 2 → _ ∈ Ideal.span {↑p} → _ - 1 ∈ Ideal.span {↑p}`   no hit: `pZpExp` is project-only (no such constant in mathlib); the generic shape `x ∈ I → f x − 1 ∈ I` has no p-adic-exp instance in mathlib (there is no `padicExp`/`pZpExp` to key on).
[C] LeanSearch        "p-adic exponential maps p Z_p into 1 + p Z_p", "integral exponential congruent to 1 mod p"   no p-adic hit: surfaces the archimedean `NormedSpace.exp*` family only; nothing nonarchimedean, nothing about `1+pℤ_p` / principal units of `ℤ_p`.
[D] Grep mathlib src  `grep -rniE "def padicExp|p-adic exponential|exp.*span|sub_one.*span|principal unit|onePAdicPow"` over `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/` and `Analysis/`   **NO p-adic exp anywhere** in `Mathlib/NumberTheory/Padics/` (confirmed: no `padicExp`, no `pZpExp`, no `onePAdicPow`, no "exp maps into `1+pℤ_p`"). `PadicIntegers.lean` has only the *infrastructure* this proof uses: `norm_le_pow_iff_mem_span_pow` (L466), `norm_def` (L191), `coe_sub` (L109), `coe_one` (L112), `maximalIdeal_eq_span_p` (L506). The archimedean `NormedSpace.exp` lives in `Analysis/`.
[E] Name pattern      `pZpExp`, `padicExp`, `exp_sub_one_mem`, `exp_mem_one_add`, `onePAdicPow`   `pZpExp` / `padicExp` / `onePAdicPow` do **not** exist in mathlib (all are project-only, in `PadicExp.lean` / `Interpolation/Branches.lean`). No `exp_sub_one_mem`-style lemma about p-adic integers exists.

Searched for both:
- the user's current form (`pZpExp p x − 1 ∈ pℤ_p` for `x ∈ pℤ_p`, `p ≠ 2`) — **not** in mathlib (the constant `pZpExp` does not exist there).
- the literature-standard / general form ("`exp` maps the maximal ideal `𝔪` of a complete nonarch
  field's ring of integers into `1+𝔪`", and the archimedean `NormedSpace.exp` family) — mathlib has
  neither the p-adic statement nor any nonarchimedean integral exponential to state it about.

**Why nothing in mathlib settles this.** There is simply **no p-adic exponential in mathlib** — not
the analytic `padicExp`, not the integral `pZpExp` — so there is no constant to make the
"`exp(x) − 1 ∈ pℤ_p`" statement *about*, and a fortiori no mathlib lemma asserting it. The
archimedean `NormedSpace.exp` is the wrong regime (unconditional convergence; an exp landing in
`1 + 𝔪` is a *non*archimedean phenomenon). The genuine mathlib pieces in the dependency chain are
only the `PadicInt` plumbing lemmas (`norm_le_pow_iff_mem_span_pow`, `norm_def`, `coe_sub`,
`coe_one`); the two mathematically substantive inputs — `norm_padicExp_sub_one` (the isometry, itself
`BORDERLINE`) and `coe_norm_le_inv_of_mem_span` (the norm bound, itself `NO-composable-from-mathlib`)
— are **project** lemmas, not mathlib.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard general form).
And — the decisive structural point — its two substantive building blocks are themselves *not* in
mathlib (one `BORDERLINE`, one `NO-composable`), and the def it certifies (`pZpExp`) is project-only.

---

### Call sites — `pZpExp_sub_one_mem`

Internal use count: **0** (within the project, NOT counting the declaring theorem)
External-to-file callers: **0 distinct files**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none)           | the qualified name `pZpExp_sub_one_mem` appears **only** at its own definition (`PadicExp.lean:1062`); a repo-wide grep across all `projects/**/*.lean` returns no other occurrence |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?):
  - **Effectively yes, by sibling.** The downstream consumer that actually needs "the integral exp of
    `s · log x` lands in `1+pℤ_p`", namely `padicExp_smul_padicLog_eq_onePAdicPow` (`PadicExp.lean:1111`)
    and its supporting `change ((pZpExp p (t*ℓ):ℤ_[p]):ℚ_[p]) = padicExp …` block (L1118–1155), routes
    through `pZpExp_coe` (the *coe* lemma) and `Ideal.mul_mem_left` on `pZpLog_mem` directly — it does
    **not** call `pZpExp_sub_one_mem`. The integrality membership fact this theorem packages is thus
    obtained, where needed, from the underlying `pZpExp_coe` + norm lemmas inline, bypassing this named
    wrapper. The companion `pZpLog_mem` (the log-image half, `:1094`) is in the identical situation.

What the call-sites pattern tells you: **K = 0 internal uses, and the membership wrapper is bypassed.**
Per the Phase-6 signal table, `K = 0` for a thin certificate whose content is otherwise reached via the
sibling `pZpExp_coe` is a **NO-leaning** signal — the named theorem currently earns its keep only as a
*human-readable milestone* ("exp lands in `1+pℤ_p`", the codomain half of RJW Lem 5.14's iso), not as
load-bearing API. (Same profile as `padicExp_converges_on_pZp`, K=0; sharp contrast with the genuinely
load-bearing `summable_padicExp_terms`/`norm_padicExp_sub_one`, which have many call sites.)

---

### Composition check (Phase 6)

Can `pZpExp_sub_one_mem` be derived **from mathlib** in ≤3 chained calls?

Attempt 1: a mathlib "exp maps into `1+𝔪`" lemma applied to `x ∈ pℤ_p`.
  - Mathlib decls used: (none exist).
  - Result: **fails** — mathlib has no p-adic exponential at all (Phase 5), so there is no such lemma
    and no constant `pZpExp`/`padicExp` to invoke. This is a missing *whole development*, not a missing
    call.

Attempt 2: the project's actual body — `rw [… , pZpExp_coe …, norm_padicExp_sub_one …, …]; exact coe_norm_le_inv_of_mem_span …`.
  - Decls used: mathlib `PadicInt.{norm_le_pow_iff_mem_span_pow, norm_def, coe_sub, coe_one}` + `zpow_*`
    plumbing; **project** `pZpExp_coe`, `norm_padicExp_sub_one`, `inExpBall_of_mem_span`,
    `coe_norm_le_inv_of_mem_span`.
  - Result: **this is a clean rewrite chain — but its two mathematically substantive steps are
    PROJECT lemmas, not mathlib.** `norm_padicExp_sub_one` is the genuine isometry (itself `BORDERLINE`,
    built on `summable_padicExp_terms`); `coe_norm_le_inv_of_mem_span` is `NO-composable-from-mathlib`;
    `pZpExp_coe` and `inExpBall_of_mem_span` are project lemmas too. So the composition does **not**
    discharge the theorem from *mathlib* building blocks.

Attempt 3: assemble from mathlib's genuine primitives only (`PadicInt.norm_le_pow_iff_mem_span_pow` +
the archimedean `NormedSpace.exp` API + valuation lemmas).
  - Result: **fails** — the archimedean `NormedSpace.exp` is the wrong regime (it does not give
    `‖exp x − 1‖ = ‖x‖` p-adically, nor convergence-on-`pℤ_p`); reconstructing the isometry is exactly
    re-proving `norm_padicExp_sub_one` (a multi-lemma nonarchimedean argument). Not a ≤3-call
    composition.

Conclusion: **NOT-COMPOSABLE *from mathlib*.** The theorem is a tidy rewrite chain, but its two
substantive inputs are project lemmas (one `BORDERLINE`, one `NO-composable`) about a project-only def
mathlib lacks entirely. Assembling it from mathlib's actual primitives would require first building the
whole nonarchimedean exp development. This rules out `NO-composable-from-mathlib` (which requires
composition from *mathlib* decls in ≤3 calls). It equally rules out `NO-mathlib-has-it` (Phase 5: no
p-adic exp in mathlib).

---

## Verdict: `pZpExp_sub_one_mem`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the target **is** a textbook-standard fact — "for odd `p`, `exp` maps
  `pℤ_p` into `1+pℤ_p`" (`exp(x) ≡ 1 mod p`), the codomain half of the exp–log iso of principal units
  `pℤ_p ≅ 1+pℤ_p` (K. Conrad, MIT note, Wikipedia, Washington §5.1, Cassels §12, RJW Lem 5.14).
  Sources unanimous, including the sharp `p ≠ 2` distinction (`exp` diverges on `2ℤ_2`). The
  mechanism `|exp(x)−1|=|x|` is precisely the project's `norm_padicExp_sub_one`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** in the *specialisation* sense —
  hypotheses are sharp (`p ≠ 2` cannot be dropped; the `p=2` claim is false), but the theorem is
  hard-coded to `L = ℚ_p` / `ℤ_p` whereas the standard fact holds over the ring of integers of any
  complete nonarch field. Modern-idiom (4c): the real organisational moves (general-`𝒪` version; bundle
  the exp–log iso of principal units) are *development*-level, not this corollary's.
- Mathlib search (Phase 5): **not in mathlib** — no p-adic exp at all (analytic or integral); the
  constant `pZpExp` is project-only; and the two substantive building blocks are themselves missing
  (`norm_padicExp_sub_one` `BORDERLINE`, `coe_norm_le_inv_of_mem_span` `NO-composable`). Only `PadicInt`
  plumbing lemmas are genuine mathlib.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the body is a rewrite chain whose
  substantive steps are *project* lemmas about a project-only def; from mathlib's real primitives it is
  a whole-development reconstruction.
- Call sites (Phase 6.0): **K = 0**, and the membership wrapper is **bypassed** (consumers route
  through the sibling `pZpExp_coe`). NO-leaning composability signal *locally*.

**Rationale (why BORDERLINE — not YES, not NO):**

This theorem sits at the same intersection of pulls that made its siblings (`padicExp_converges_on_pZp`,
`norm_padicExp_sub_one`) BORDERLINE, which is the textbook trigger for this verdict. On one side, it is
a *true, named, textbook-standard, genuinely-missing-from-mathlib* p-adic fact with sharp hypotheses
(the `p ≠ 2` exclusion is real and correct), proved sorry-free — that profile pulls toward a YES bucket.
On the other side, **as a declaration it is a thin integrality certificate about a project-only `def`**
(`pZpExp`, the junk-totalised integral exponential `ℤ_[p] → ℤ_[p]` that mathlib has no analogue of), it
adds **no new analysis** (its only substantive inputs are the already-assessed project lemmas
`norm_padicExp_sub_one` and `coe_norm_le_inv_of_mem_span`), it has **zero call sites**, and the content
it packages is reached via the sibling `pZpExp_coe` at the one place it would matter
(`padicExp_smul_padicLog_eq_onePAdicPow`). Those facts pull toward NO. But it is decisively **not**
`NO-mathlib-has-it` (mathlib has no p-adic exp of any kind, and the substantive building blocks are
absent — Phase 5) and **not** `NO-composable-from-mathlib` (the composition is from *project* lemmas
about a project def, not mathlib; from mathlib it is a whole-development reconstruction — Phase 6). So
neither NO bucket is groundable in the evidence either.

What actually decides this theorem's mathlib fate is **not** anything intrinsic to it — it is the *same*
upstreaming decision that governs the def it certifies (`pZpExp`) and the development underneath it
(`padicExp` → `NO-mathlib-has-it` with the surrounding theorems flagged as the real missing API;
`norm_padicExp_sub_one` → `BORDERLINE`; `summable_padicExp_terms` → `BORDERLINE`). Mathlib has **no**
nonarchimedean exponential development. If the project upstreams that development as a unit, then the
natural mathlib form of *this* fact is the **general-`𝒪`** statement ("for odd residue characteristic,
`exp` maps the maximal ideal `𝔪` into `1+𝔪`"), almost certainly bundled into the exp–log iso of
principal units `𝔪 ≃ 1+𝔪` as a private well-definedness step (Phase 4c row 3) — so the right move would
be to *generalise-and-absorb* this into that PR, not ship the `ℚ_p`-hard-coded `pZpExp` wrapper
verbatim. If the project keeps the development local, this is a (currently bypassed, K=0) human-readable
milestone that need not go to mathlib at all — and may even be inlinable. The skill cannot choose
between "upstream the whole exp/log development (and restate this generally / fold it into the iso)" and
"keep local" without the human; per the anti-pattern guidance, a whole-development /
EXPENSIVE-generalisation tradeoff is itself a BORDERLINE question, not a self-resolving downgrade.

**Numbered questions (≤5):**

1. Do you intend to upstream the project's p-adic / nonarchimedean **exp/log development** to mathlib as
   a unit (the analytic `padicExp`, the convergence engine `summable_padicExp_terms`, the isometry
   `norm_padicExp_sub_one`, the integral `pZpExp`/`pZpLog`, and the exp–log isomorphism of principal
   units `pℤ_p ≅ 1+pℤ_p`)? This theorem is a *codomain-half membership* fact of that development and
   should travel with it (most likely **generalised** / **folded into the iso**, see Q2–Q3), not alone.
   (Same governing question as for `padicExp`, `summable_padicExp_terms`, `norm_padicExp_sub_one`.)
2. If yes to (1): should the mathlib statement be the **general** form — "for a complete nonarchimedean
   field `L ⊇ ℚ_p` of odd residue characteristic, the integral exponential maps the maximal ideal `𝔪`
   of its ring of integers into `1+𝔪`" (which needs a general integral-exp construction + a general
   `𝔪 ⊆ exp-ball` lemma; the isometry half is already `norm_padicExp_sub_one`) — rather than the
   `ℚ_p`-hard-coded `pZpExp`/`pℤ_p` wrapper this theorem is? (Cost MODERATE–EXPENSIVE; per the
   Bourbaki-2.0 guidance, cost does not by itself downgrade the verdict.)
3. If yes to (1): should this integrality fact be exposed as a standalone lemma at all, or only as a
   **private well-definedness step inside the bundled exp–log isomorphism** `pℤ_p ≃ (1 + pℤ_p)`
   (`MulEquiv`/group iso of principal units; Phase 4c row 3)? Mathlib would likely prefer the bundled
   iso as the public API, with "exp lands in `1+pℤ_p`" internal to its construction.
4. Given that this wrapper currently has **K = 0** call sites and its content is reached via the sibling
   `pZpExp_coe` at the one downstream site (`padicExp_smul_padicLog_eq_onePAdicPow`): even setting
   mathlib aside, do you want to keep it as a named project-local milestone ("exp maps `pℤ_p` into
   `1+pℤ_p`", paired with `pZpLog_mem`), or inline/drop it? (If you drop it, the mathlib question is
   moot; if you keep it, it stays a project-local readability anchor.)

**Next action:** user answers the questions; re-run `/mathlibable pZpExp_sub_one_mem` — preferably
**together with `/mathlibable PadicLFunctions.pZpExp`, `/mathlibable norm_padicExp_sub_one`, and
`/mathlibable PadicLFunctions.padicExp`**, since this corollary's verdict is entirely governed by the
(BIG, multi-decl) upstreaming decision on the p-adic exp/log development it certifies. Likely
resolutions:
  - "Upstream the nonarchimedean exp/log development" → this fact ships **as the general-`𝒪` statement
    (Q2), or as a private well-definedness step in the bundled exp–log iso (Q3)** — i.e. effectively
    `YES-but-generalise-first` *folded into* the development PR, **not** as this verbatim `pZpExp`
    wrapper.
  - "Keep project-local" → drop from mathlib consideration; and consider inlining the wrapper (Q4) since
    it has no consumers.

---

## Next step

User answers the four numbered questions above; re-run `/mathlibable pZpExp_sub_one_mem` — preferably
alongside `/mathlibable PadicLFunctions.pZpExp`, `/mathlibable norm_padicExp_sub_one`, and
`/mathlibable PadicLFunctions.padicExp`, since this corollary's mathlib fate is governed by the (BIG,
multi-decl) upstreaming decision on the p-adic exp/log development (the def `pZpExp` it certifies, the
isometry, and the principal-units iso) — to resolve to either `YES-but-generalise-first` (folded into
the nonarchimedean exp/log development PR as the general-`𝒪` statement / a step in the bundled exp–log
iso `pℤ_p ≃ 1+pℤ_p`) or drop-from-consideration (keep — or inline — as a project-local milestone).
