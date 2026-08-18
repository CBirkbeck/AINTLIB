# `/mathlibable` report — `PadicLFunctions.norm_padicLog`

**Final verdict: `YES-but-generalise-first`** (reason: **LITERATURE-WEAKENING** — the result is
textbook-standard, named in the literature, and entirely missing from mathlib, but the Lean form
is keyed to a `ℚ_[p]`-algebra with `ℚ_[p]`-pulled coefficients/valuation and is stated on the
*exponential* ball, whereas the literature-standard isometry `|log(1+x)| = |x|` is over **any**
complete nonarchimedean field. This is the **log-side twin** of `norm_padicExp_sub_padicExp` —
which this project's own ledger already verdicted `YES-but-generalise-first` for the identical
reason — and is governed by the `YES-but-generalise-first` verdict on the `padicLog` def it is
about.)

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task BUILD NOTE); **reasoned from source** — Phase-0 fallback. Verified the pinned mathlib tree (`.lake/packages/mathlib`, rev `005f0aa67b69`, `v4.32.0-rc1`) contains the two ultrametric lemmas the proof calls — they are the `@[to_additive]` duals of `IsUltrametricDist.norm_mul_eq_max_of_norm_ne_norm` (`Mathlib/Analysis/Normed/Group/Ultra.lean:96`) and `IsUltrametricDist.norm_tprod_le_of_forall_le` (`…/Ultra.lean:342`), auto-generated as `norm_add_eq_max_of_norm_ne_norm` / `norm_tsum_le_of_forall_le`. The decl elaborates as part of `main`.
- decl `PadicLFunctions.norm_padicLog`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:417`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` converges and is an **isometry** on the open ball `‖x‖ < p^{−1/(p−1)}`; `log(1+y)=∑(−1)^{n+1}yⁿ/n` converges for `‖y‖<1` and **inverts** `exp` on the matched balls; realises RJW Lemma 5.14 (TeX 1892–1897, citing Cassels §12; cross-ref Washington §5.1).

---

### Statement (Phase 1)

`norm_padicLog` is a theorem stating the following:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra. For `x ∈ L`
> with `x − 1` in the **open** convergence ball of the `p`-adic exponential
> (`‖x − 1‖^{p−1} < p⁻¹`, i.e. `‖x − 1‖ < p^{−1/(p−1)}`), the `p`-adic logarithm
> `log x = ∑_{n≥0} (−1)ⁿ (n+1)⁻¹ (x−1)^{n+1}` is **norm-preserving on its leading term**:
> `‖log x‖ = ‖x − 1‖`.

This is the headline **isometry / norm-preservation** fact for the `p`-adic logarithm: on the
ball the higher-order terms of the series are *strictly* dominated by the linear term `x − 1`
(supplied by the companion lemma `norm_succ_inv_smul_pow_lt`, `PadicExp.lean:396`), so by the
ultrametric "norm of a sum equals the max when the maxes differ"
(`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) the linear term controls the whole norm.
In valuation language it is the classical `v(log(1+y)) = v(y)`. It is the **log-side companion**
of the exp isometry `norm_padicExp_sub_one` (`‖exp x − 1‖ = ‖x‖`) and `norm_padicExp_sub_padicExp`
(`‖exp x − exp y‖ = ‖x − y‖`), and it is exactly what makes `exp`/`log` mutually-inverse
isometries between the matched balls (RJW Lem 5.14).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `{L : Type*}`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]`, `[CompleteSpace L]` — a complete nonarchimedean normed field that is a `ℚ_[p]`-algebra. (Completeness is genuinely used: the proof splits the `tsum` via `Summable.tsum_eq_zero_add` and bounds the tail, both of which need the series to converge.)
- `{x : L}` — the argument of the logarithm.

Hypotheses (Lean side):
- `(hx : InExpBall p (x − 1))` — i.e. `‖x − 1‖^{p−1} < p⁻¹`; `x − 1` lies in the open *exponential* ball (note: strictly smaller than the logarithm's own convergence ball `‖x − 1‖ < 1`).

Conclusion (math): `‖log x‖ = ‖x − 1‖` (the `p`-adic logarithm preserves the norm of its argument's "distance from 1").

Conclusion (Lean): `‖padicLog p x‖ = ‖x - 1‖`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG/SMALL — recorded BIG for framing).
Reason: it is not *itself* a person-named theorem, but it is a **headline property of a named
analytic object** (the `p`-adic logarithm) and one of the explicitly listed payoffs of the file's
RJW-Lem-5.14 development (`exp`/`log` are mutually-inverse **isometries**). It is the log-side
analog of `norm_padicExp_sub_padicExp`, which the project's overview classified BIG. It is a
genuine theorem about a classical object, virtually guaranteed to be in the literature in some
form — and it is (Conrad Thm; Cassels §12; Washington §5.1).

(Note: literature width was EXHAUSTIVE regardless — all nine channels run below. BIG/SMALL is for
the report's framing only; it does not gate Phase 3.)

### One-line check (Phase 2b)

Body line count: ~43 substantive lines (`rcases` on `x = 1`; `Summable.tsum_eq_zero_add` to peel
the `n = 0` linear term; a ~30-line `htail` block bounding the tail `tsum` strictly below
`‖x − 1‖` via a `Finset.sup'` split at `N` + `IsUltrametricDist.norm_tsum_le_of_forall_le`; then
`norm_add_eq_max_of_norm_ne_norm` + `max_eq_left`).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** The defeq/diamond/API one-liner
exemptions apply only to definitions; this is a proposition with a substantial proof.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form: log isometry on ball) | "p-adic logarithm isometry norm preserving convergence ball log(x) = norm x−1" | **yes** | "log_G and exp_G are isometries on B(0;R) for sufficiently small R"; "log_{E,P} is an isometry, mapping D⁺→D⁺" | Direct hit. Montreal `Appendix16.pdf` (16.6 power-series convergence & the p-adic log), Cambridge `jat58/all.pdf`, Leiden `dio15-8.pdf`. The isometry / norm-preservation of the p-adic log on its ball is treated as standard. |
| 2 | WebSearch (valuation / general form) | "p-adic logarithm v(log(1+x)) = v(x) valuation preserving for v(x) large nonarchimedean" | **yes** | `log_p x = −∑ xⁿ/n` for `\|x\|_p<1`; isometry for `v(x)` large; `v_p(a+b) ≥ min(v_p a, v_p b)` ultrametric regime | Kedlaya `18.787`, MIT `18.782` LectureNotes5, Cambridge notes. Confirms the valuation-form `v(log(1+x)) = v(x)` is the standard companion and that the ambient is a general nonarchimedean field. |
| 3 | WebSearch (named-source / aliases: exp/log isometry, Cassels/Washington/Robert) | "Robert 'Course in p-adic Analysis' logarithm exponential isometry open ball valuation 1/(p−1)" + "Conrad 'Infinite series in p-adic fields' p-adic logarithm isometry \|log x\|=\|x−1\| complete nonarchimedean" | **yes** | **Conrad: "For x in B(0, p^{−1/(p−1)}), \|log_p(1+x)\|_p = \|x\|_p"**; log is an isometry between the matched additive/principal-unit balls; Robert *A Course in p-adic Analysis* Ch. 4 ("The Exponential and Logarithm") | **Verbatim match for our exact statement.** Keith Conrad *Infinite Series in p-adic Fields* (`kconrad.../infseriespadic.pdf`); Robert GTM 198 Ch. 4; ProofWiki book page. Conrad develops it over "a field K complete w.r.t. a nontrivial nonarchimedean absolute value, such as Qp" — the general-field generality. This is the **same source** the sibling exp-isometry report cites (Conrad Thm 4.5). |
| 4 | ChatGPT MCP | (MCP server `chatgpt-math` **failed to connect** in this environment — configured for `/home/chris/…`, not this machine) — substituted by the targeted WebSearch queries #1–#3, which explicitly requested the standard form, its generality, the named classical sources (Conrad/Cassels/Robert/Washington), and the historical lineage | yes | as #1–#3 | n/a for the MCP tool itself; recorded as substituted. The substitutes covered the MCP brief: "standard form + generality + classical source + historical evolution." |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and the `refs/` symlink | **n/a** | (no `references/` dir under `.mathlib-quality/`; `refs/` symlink absent in this checkout — PDFs are local-only and not present here) | Recorded n/a per protocol. The project's `worklist.json` / module docstring labels the cluster **R5.E** and cites RJW Lem 5.14, Cassels §12, Washington §5.1. |
| 6 | nLab | `ncatlab.org/nlab/show/p-adic+number` (+ p-adic logarithm) | **n/a** | nLab `p-adic number` is a foundational entry on non-archimedean analytic geometry; **no dedicated p-adic-logarithm/isometry page** | Consistent with the sibling exp-isometry report (nLab has no standalone p-adic-exp/log entry; the concept lives under classical p-adic-analysis references, not a categorical nLab page). |
| 7 | nCatLab (categorical) | — | **n/a** | not a categorical concept | A metric equality `‖·‖ = ‖·‖` for a concrete analytic function; nothing categorical to phrase. |
| 8 | Stacks Project | — | **n/a** | not an algebraic-geometry concept | The p-adic-log isometry is nonarchimedean analysis, not scheme theory. (A brief look confirms Stacks has no analytic p-adic exp/log.) |
| 9 | MathOverflow / Math.StackExchange | "p-adic logarithm 'strictly isometric' OR 'norm-preserving' '\|log(x)\|=\|x−1\|' leading-term ultrametric proof" | **yes** | "log₂ is an isometry from 1+4ℤ₂ to 4ℤ₂"; for elements in the right domain the log is norm-preserving | Surfaced via Uchicago REU `Chen,Yuchen.pdf` (Strassman), `numberanalytics` ultrametric guide; the isometry is uncontested textbook material — no MO-specific subtlety. |
| 10 | recent arXiv (last 5 years) | "Hensel minimality, p-adic exponentiation and Tate uniformization" (arXiv 2602.16433); "A P-adic class formula for Anderson t-modules" (2504.03430) | **yes** | "On Cp, exp converges on the open ball of valuative radius 1/(p−1) around 0, image precisely the open ball of radius 1/(p−1) around 1, with exp a **bijection** between these balls" | The exp/log **bijection of matched balls** (of which our `‖log x‖ = ‖x−1‖` isometry is the metric content) is still the standard tool in current p-adic work — no modern restatement of *this* norm identity. |

**Protocol pass check:** WebSearch ran **≥3 distinct queries** at three generality levels (specific
isometry form #1; valuation/general-field form #2; named-classical-source form #3, which hit
Conrad's `|log_p(1+x)| = |x|` **verbatim**). ChatGPT MCP unavailable (failed to connect) →
explicitly substituted. Local refs checked (n/a, absent). nLab checked. nCatLab / Stacks recorded
n/a with reasons. MathOverflow covered (#9). Recent arXiv (2602.16433, 2504.03430) checked. All
nine channels addressed.

### Literature summary (Phase 3)

Concept identified as: **the isometry / norm-preservation of the `p`-adic logarithm on its
convergence ball** — `|log_p(1+x)|_p = |x|_p` for `x ∈ B(0, p^{−1/(p−1)})` (equivalently
`v(log(1+x)) = v(x)`), the metric content of the `exp`/`log` bijection of matched balls.
Sources agree on the standard form: **yes** — stated essentially verbatim by Keith Conrad
*Infinite Series in p-adic Fields* ("`|log_p(1+x)|_p = |x|_p` for x in B(0, p^{−1/(p−1)})"),
Robert *A Course in p-adic Analysis* Ch. 4, the Montreal/Cambridge/MIT/Kedlaya lecture notes,
Cassels *Local Fields* §12, Washington §5.1. It is textbook, uncontested.
Most general standard form: `‖log(1+y)‖ = ‖y‖` for `y` in the open ball `‖y‖ < p^{−1/(p−1)}`,
over **any field complete w.r.t. a nontrivial nonarchimedean absolute value** (Conrad's exact
hypothesis cluster) — `ℚ_p`, `ℂ_p`, finite extensions, etc.
Generality dimensions where the literature varies:
  - **Ambient field**: Conrad states it over an arbitrary complete nonarchimedean field `K`; many sources specialise to `ℚ_p`/`ℂ_p`. The literature standard is the *general field*. The project's form keys it to a `ℚ_[p]`-**algebra** `L` — narrower than "any complete nonarchimedean field" (see Phase 4).
  - **Convergence ball stated**: the isometry holds on the **exp ball** `‖y‖ < p^{−1/(p−1)}` (where both `exp` and `log` are isometries and mutually inverse) — this matches the project's `InExpBall` hypothesis exactly. (The log *series itself* converges on the larger `‖y‖<1`, but the **isometry** is an exp-ball statement, so the hypothesis is correct here.)
  - **Encoding**: literature uses valuations / `Real.rpow` radius `p^{−1/(p−1)}`; the project uses the rpow-free `‖·‖^{p−1} < p⁻¹` packaging (`InExpBall p (x−1)`) for ultrametric `pow`-monotonicity.
Disagreement with the literature: **none.** The mathematics is exactly the standard log isometry;
the project re-packages it rpow-free and keyed to a `ℚ_[p]`-algebra rather than a bare complete
nonarchimedean field.

---

### Generality analysis — `norm_padicLog`

Literature-standard form (from Phase 3): `‖log(1+y)‖ = ‖y‖` for `‖y‖ < p^{−1/(p−1)}` over a field
`K` complete w.r.t. a nontrivial nonarchimedean absolute value (Conrad) — i.e. **any** complete
nonarchimedean field, not specifically a `ℚ_[p]`-algebra.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `p : ℕ`, `[Fact p.Prime]` | a rational prime | a rational prime | NO | The radius `p^{−1/(p−1)}` and the per-term Legendre/valuation bound are intrinsically about a prime `p`. |
| 2 | `[NormedAlgebra ℚ_[p] L]` (+ coefficients pulled through `ℚ_[p]`: `((n:ℚ_[p])+1)⁻¹ • …`) | `L` is a normed `ℚ_[p]`-**algebra**; the rational coefficients `1/(n+1)` and the `‖·‖`-bound on them are taken in `ℚ_[p]` (the proof of `norm_succ_inv_smul_pow_le` uses `Padic.norm_eq_zpow_neg_valuation` / `Padic.valuation_natCast` on `ℚ_[p]`) | a complete nonarchimedean **char-0 field** `K` (so `1/(n+1) ∈ K`); the per-term bound `‖(n+1)⁻¹‖ ≤ pⁿ` from how `p` sits in `K` | **YES** | This is the **literature-weakening axis** (identical to the def `padicLog` and the exp-twin `norm_padicExp_sub_padicExp`). Conrad states it over any complete nonarchimedean field, never restricting to `ℚ_[p]`-algebras. The proof's only genuinely `ℚ_[p]`-keyed step is the coefficient-norm bound `‖((n:ℚ_[p])+1)‖ ≥ p^{−vₚ(n+1)}`, which must instead be derived from a residue-characteristic-`p` input on `K` (e.g. `‖(p:K)‖ = p⁻¹`, or that `‖·‖` restricts to `\|·\|_p` on `ℚ`). The *isometry core* (strict tail-domination + strong triangle equality) is already field-internal. |
| 3 | `[NormedField L]`, `[IsUltrametricDist L]` | complete ultrametric normed field | complete nonarchimedean field | NO (already general) | Ultrametricity is used essentially (`norm_add_eq_max_of_norm_ne_norm`, `norm_tsum_le_of_forall_le`); a normed field is the right ambient. This is *not* a narrowing. |
| 4 | `[CompleteSpace L]` | complete | usually assumed (so the series / `tsum` exists) | NO | Genuinely used: `Summable.tsum_eq_zero_add` to split the linear term and the tail-`tsum` bound both need convergence. Cannot be dropped here (unlike the per-term helper, which omits it). |
| 5 | `(hx : InExpBall p (x − 1))` | open **exp** ball `‖x−1‖^{p−1} < p⁻¹` | open ball `‖y‖ < p^{−1/(p−1)}` | NO (this is the right ball **for the isometry**) | The **isometry** `‖log x‖ = ‖x−1‖` is an exp-ball statement (where strict tail-domination holds); the hypothesis is correct as stated. (The log *series* converges on the larger `‖x−1‖<1`, but the multiplicativity/norm laws on that larger ball are *separate* lemmas — see Phase 4c.) The only re-encoding is `‖·‖^{p−1}<p⁻¹` ↔ `Real.rpow`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **1** (row 2 — the `[NormedAlgebra ℚ_[p] L]` keying with
`ℚ_[p]`-pulled coefficients; the literature states the isometry over *any* complete nonarchimedean
char-0 field). Rows 3–5 are already at the right generality (ultrametricity, completeness, and the
exp-ball hypothesis are all correct / used).
Proposed restatement (matching the `padicLog`-def and exp-twin generalisations already on file):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- (generalised `padicLog` over a complete nonarchimedean char-0 field, with the rational
coefficients taken in `K`) -/
noncomputable def padicLog' (x : K) : K :=
  ∑' n : ℕ, (-1 : K) ^ n * ((n + 1 : K)⁻¹ * (x - 1) ^ (n + 1))

/-- Conrad: `‖log(1+y)‖ = ‖y‖` on the exp ball, over any complete nonarchimedean char-0 field. -/
theorem norm_padicLog' (p : ℕ) [Fact p.Prime] {x : K}
    (hp : ‖(p : K)‖ = (p : ℝ)⁻¹)            -- the residue-char-p input replacing the ℚ_[p]-algebra
    (hx : ‖x - 1‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖padicLog' x‖ = ‖x - 1‖ := by
  sorry  -- isometry core (strict tail-domination + strong-triangle equality) is field-internal;
         -- only the coefficient-norm bound `‖(n+1)⁻¹‖ ≤ pⁿ` must be re-derived from `hp`
         -- instead of `Padic.norm_eq_zpow_neg_valuation` on ℚ_[p].
```

Cost of restatement: **MODERATE** — the isometry argument (peel the linear term; every higher term
strictly smaller via `norm_succ_inv_smul_pow_lt`; ultrametric tail bound; strong-triangle equality)
is already field-internal; the *only* rerouting is establishing the per-term coefficient bound
`‖((n:K)+1)⁻¹‖ ≤ pⁿ` (currently via `Padic.valuation` on `ℚ_[p]`) from a residue-char-`p`
hypothesis on `K`. Exactly the same MODERATE rerouting the sibling `norm_padicExp_sub_padicExp`
report estimated. **Cost does NOT downgrade the verdict** (mathlib ships the right form).

STRICTLY NARROWER → Phase 7 considers `YES-but-generalise-first` prominently. Then 4c (below).

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partial | `[IsUltrametricDist L]`, `[CompleteSpace L]` are already typeclasses; the one bundled-strengthening is `[NormedAlgebra ℚ_[p] L]`, which 4a row 2 proposes to replace with a residue-char-`p` hypothesis on `K` | a `ℚ_p`-algebra-free statement composes with **any** complete nonarchimedean field (`ℂ_p`, finite extensions) without re-instantiating the algebra |
| 2 | sequences/metric → filters/topology? | no | the statement is already a clean metric equality `‖·‖ = ‖·‖`; the *proof* already uses `Tendsto … atTop` / `Filter.eventually_atTop` and `IsUltrametricDist.norm_tsum_le_of_forall_le`. No idiom gap. | — |
| 3 | construct an object → universal-property class? | no | `log` is an honest analytic function (a `tsum`); there is no universal property to phrase the *isometry* by. | — |
| 4 | set+closure-predicate → bundled substructure? | no | `InExpBall` is a `Prop` membership in an open ball — the right shape for a hypothesis (not a structure carrying API). | — |
| 5 | vector-space/metric/field-specific → weaken typeclass? | **yes (= 4a row 2)** | drop `[NormedAlgebra ℚ_[p] L]`; state over a complete nonarchimedean `[CharZero K]` field with a residue-char-`p` input | full reuse across complete-nonarch fields; aligns with mathlib's "facts about a power series live over its coefficient field" convention |
| 6 | 1-categorical → higher-categorical? | no | not categorical. | — |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | the only index is `n : ℕ` summing the series; intrinsic. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it **coincides with the literature-weakening of 4a/4b** (drop
the `ℚ_[p]`-algebra packaging; state the isometry over a complete nonarchimedean char-0 field `K`
itself). It is **not an additional independent modernisation**.
  - Proposed mathlib-idiomatic restatement: as the `norm_padicLog'` block in 4b.
  - Cost: **MODERATE** (as 4b).
  - Mathlib downstream this enables: the isometry then applies verbatim to `ℂ_p` and every complete
    nonarchimedean extension of `ℚ_p` (where dragging in `[NormedAlgebra ℚ_[p] L]` is awkward);
    it is the missing nonarchimedean partner to `NormedSpace.exp`; and it composes with the
    generalised `padicLog` def (itself `YES-but-generalise-first` on file).
  - Real mathematical improvement (not just "looks cooler"): the result becomes usable across the
    whole `ℂ_p` / finite-extension regime without re-instantiating a `ℚ_[p]`-algebra structure —
    the exact reuse the project itself needs (it calls `norm_padicLog (L := ℚ_[p])` everywhere,
    but the isometry is field-intrinsic).

Because 4c coincides with the 4b literature-weakening, Phase 7's reason is **LITERATURE-WEAKENING**
(with MODERN-IDIOM noted as the same direction, not independent).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (introduces no definitional equalities or typeclass-search
paths). (The companion `def padicLog` gets its own assessment — already on file as
`YES-but-generalise-first`; this report is scoped to the theorem.)

---

### Mathlib search-status: `norm_padicLog`

```
[A] Lean-Finder       "p-adic logarithm isometry", "‖log x‖ = ‖x − 1‖ p-adic"   n/a: Lean-Finder web service not reachable from this sandboxed environment — substituted by [D] grep + [E] name-pattern over the pinned mathlib tree (rev 005f0aa67b69).
[B] Loogle            `‖padicLog _‖ = ‖_ - 1‖`, `‖_‖ = ‖_ - 1‖` with log, `‖tsum _‖ = ‖_‖`   n/a: Loogle not callable here — substituted by [D] type-shape grep below.
[C] LeanSearch        "p-adic logarithm is an isometry", "norm of p-adic log equals norm of x minus one"   n/a: LeanSearch not callable here — substituted by the EXHAUSTIVE Phase-3 NL web search + [D]/[E].
[D] Grep mathlib src  Terms: "padicLog", "Padic.log", "PadicInt.log", "p-adic logarithm",
                      "norm_log", "log.*isometr", "nonarchimedean.*log", "expSeries", "padicExp".
                      → NO HITS for any p-adic / nonarchimedean logarithm or exponential.
                      Mathlib has only the *formal* power series `PowerSeries.log`
                      (Mathlib/RingTheory/PowerSeries/Log.lean:42) — a `PowerSeries A`, NOT an
                      analytic sum / `tsum` in a normed field, and with no norm/isometry content —
                      and the *archimedean* `Real.log`/`Complex.log`/`NormedSpace.exp`, none of
                      which is an isometry. There is no `Analysis/.../Padics/.../Log` file at all.
[E] Name pattern      lean_local_search not callable; grep `def padicLog|theorem.*padicLog|
                      Padic.log|norm.*padicLog|nonarch.*log` over mathlib → 0 hits. Confirmed.
                      (The leanprover-community p-adics theory page and the mathlib4 docs index
                      list only PadicVal / PadicIntegers / PadicNumbers / PadicNorm / Hensel /
                      MahlerBasis — no PadicLog / p-adic exp module. Verified via the public docs.)
```

Searched for both:
  - the user's current form (`‖padicLog p x‖ = ‖x − 1‖` over a `ℚ_[p]`-algebra) — **absent**;
  - the literature-standard general form (`‖log(1+y)‖ = ‖y‖` over any complete nonarchimedean field) — **also absent**. Mathlib has neither the specialisation nor the general form.

Concluded: **"not in mathlib (all available methods exhausted, plus the literature-standard general
form)."** Mathlib has **no** nonarchimedean / p-adic logarithm of any kind — only the formal
`PowerSeries.log` (no analytic sum, no norm content) and the archimedean `Real.log`/`Complex.log`
(not isometries). The entire supporting API — `padicLog`, `InExpBall`, `summable_padicLog_terms`,
`norm_succ_inv_smul_pow_lt`, this isometry, the inverse identities `padicExp_padicLog` /
`padicLog_padicExp` — is genuinely absent. (Cross-repo note: within AINTLIB, the *def* `padicLog`
is **duplicated** — `BernoulliRegular.FLT37.PadicL.padicLog : ℚ_[p] → ℚ_[p]` re-implements the same
Iwasawa series over concrete `ℚ_[p]`, but **without** any `norm_padicLog`/isometry lemma. So this
isometry is unique even within the repo.)

---

### Call sites — `norm_padicLog`

Internal use count: **K = 5** (within `PadicLFunctions`, not counting the declaration at
`PadicExp.lean:417`).
External-to-file callers: **1 distinct other file** (`ResidueZeta.lean`); the other 3 are within
`PadicExp.lean`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:978` | `rw [InExpBall, ha, norm_padicLog p hx]; exact hx` — inside `padicLog_mul`, to show `a = log x` lands back in the exp ball (`‖a‖ = ‖x−1‖ < radius`), so `exp(a+b)` is defined |
| `PadicExp.lean:979` | `rw [InExpBall, hb, norm_padicLog p hy]; exact hy` — same, for `b = log y` |
| `PadicExp.lean:1089` | `rw [norm_padicLog (L := ℚ_[p]) p hball, hxsub]` — in the `xˢ := exp(s·log x)` / `onePAdicPow` agreement chain (the file's RJW-5.14 payoff), bounding `‖log x‖` |
| `ResidueZeta.lean:121` | `rw [hℓ, PadicInt.norm_def, pZpLog_coe p hp2 hy, norm_padicLog (L := ℚ_[p]) p hball, …]` — computing `‖log_p y‖` in the residue-zeta / `pZpLog` development |
| `ResidueZeta.lean:1102` (`:1102` cluster) | `PadicInt.norm_def, pZpLog_coe p hp2 hx, norm_padicLog (L := ℚ_[p]) p hball, …` — same `pZpLog` norm computation |

Inline-derivation grep (was `‖log x‖ = ‖x−1‖` re-derived elsewhere without using `norm_padicLog`?):
  - (none) — no other site re-proves the log isometry by hand. Every consumer routes through this
    lemma. (The structurally analogous *helper* `norm_succ_inv_smul_pow_lt` proves the per-term
    strict bound, not the isometry; this lemma is the unique home of `‖log x‖ = ‖x−1‖`.)

Signal: **K = 5 internal uses across 2 files, all load-bearing, no inline re-derivation.** Two
distinct downstream payoffs depend on it essentially: the multiplicativity `padicLog_mul` (needs
`log x`, `log y` back in the ball) and the `onePAdicPow` character agreement (RJW Lem 5.14), plus
the `ResidueZeta`/`pZpLog` norm computations. Per the Phase-6.0.1 table, **K ≥ 3 internal uses with
no inline re-derivation → real API; consumers depend on it → leans YES-family.**

---

### Composition check (Phase 6)

Can `norm_padicLog` be derived from mathlib in ≤3 chained calls?

Attempt 1 — any mathlib p-adic-log / isometry lemma.
  - Mathlib decls available: `PowerSeries.log` (formal, no norm), `Real.log` / `Complex.log` (archimedean, not isometries), `NormedSpace.exp` (archimedean). **None p-adic / nonarchimedean.**
  - Result: **fails** — there is no p-adic `log` in mathlib to call, and the archimedean logs/exps are provably *not* isometries, so nothing specialises.

Attempt 2 — assemble from the strong triangle inequality + the ultrametric tsum bound.
  - Mathlib decls: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `Summable.tsum_eq_zero_add`, `Finset.le_sup'`/`Finset.sup'_lt_iff`, plus the **project-local** `summable_padicLog_terms` and `norm_succ_inv_smul_pow_lt`.
  - Result: **fails as a composition.** The actual proof (lines 417–459) is a genuine ~43-line argument: `rcases` the trivial `x=1` case; peel the linear term via `Summable.tsum_eq_zero_add`; prove the tail `tsum` is *strictly* below `‖x−1‖` by an `eventually`/`Finset.sup'` split at an index `N` (so it is `< ‖x−1‖/2` past `N` and `≤` the finite `sup'` before, both `< ‖x−1‖`) fed into `norm_tsum_le_of_forall_le`; then `norm_add_eq_max_of_norm_ne_norm` + `max_eq_left`. This is far more than 3 calls, uses `set`/`obtain`/`refine` with non-trivial reasoning between, and crucially routes through **two project-local lemmas absent from mathlib** (`summable_padicLog_terms`, `norm_succ_inv_smul_pow_lt`). By the Phase-6 heuristics ("multiple `have`s with non-trivial reasoning / `rw […]` chains are a proof, not glue"), this is **irreducibly a proof**.

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib lacks both the object (`padicLog`) and any
near-composition; the isometry is a real theorem requiring the full nonarchimedean tail-domination
argument, and even that routes through project-local summability/per-term lemmas that are
themselves absent from mathlib.

---

## Verdict: `norm_padicLog`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): **EXACT verbatim match** — Keith Conrad *Infinite Series in p-adic Fields*: "for x in B(0, p^{−1/(p−1)}), `|log_p(1+x)|_p = |x|_p`"; also Robert GTM 198 Ch. 4, Cassels §12, Washington §5.1, the Montreal/Cambridge/MIT/Kedlaya notes. Standard form is over **any** field complete w.r.t. a nontrivial nonarchimedean absolute value. Textbook, uncontested.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 1 axis: the Lean form bundles `[NormedAlgebra ℚ_[p] L]` and pulls the rational coefficients / their norm bound through `ℚ_[p]` (`Padic.norm_eq_zpow_neg_valuation`), whereas the literature states the isometry over the complete nonarchimedean char-0 field itself. Phase 4c agrees (the modern-idiom move *is* this same weakening). MODERATE cost.
- Mathlib search (Phase 5): **not in mathlib** under either the user's or the general form; mathlib has no p-adic / nonarchimedean logarithm at all (only the formal `PowerSeries.log` with no norm content, and the archimedean `Real.log`/`Complex.log`, which are not isometries).
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~43-line ultrametric proof; no mathlib object to specialise, no ≤3-call route, and it routes through project-local `summable_padicLog_terms` + `norm_succ_inv_smul_pow_lt`.
- Call sites (Phase 6.0): **K = 5** across 2 files, all load-bearing (`padicLog_mul`, the `onePAdicPow`/RJW-5.14 agreement, the `ResidueZeta`/`pZpLog` norm computations), no inline re-derivation → real API.

**Rationale (1–2 paragraphs):**

This is a textbook-canonical theorem — the **norm-preservation / isometry of the `p`-adic
logarithm**, written `|log_p(1+x)|_p = |x|_p` essentially verbatim in Keith Conrad's *Infinite
Series in p-adic Fields* (the very source the sibling exp-isometry report cites), and in Robert
Ch. 4 / Cassels §12 / Washington §5.1 — that mathlib is **entirely missing**. Mathlib has no
p-adic / nonarchimedean logarithm of any kind: only the *formal* series `PowerSeries.log` (no
analytic sum, no norm content) and the *archimedean* `Real.log` / `Complex.log` (which are not
isometries — the opposite regime). So the whole `PadicExp.lean` exp/log cluster, this isometry
included, fills a long-standing named gap (a developed p-adic exp/log API has been absent since
the Lean 3 → Lean 4 port; cf. the 2023 "Formalization of p-adic L-functions in Lean 3" predecessor
of this project). It is decidedly **not** any NO bucket: Phase 5 found no analogue (the only
`*_log` decls are formal or archimedean), and Phase 6 shows it is NOT-COMPOSABLE (a real ~43-line
ultrametric proof routing through two project-local lemmas mathlib also lacks). It has genuine API
weight (K = 5 load-bearing consumers across two files, no inline re-derivation).

The reason the verdict is **`YES-but-generalise-first`** rather than `YES-add-as-is` is purely the
Phase-4b finding (the verdict gate *requires* this downgrade when a known weakening exists): the
statement is keyed to a `ℚ_[p]`-**algebra** `L` with the rational coefficients `1/(n+1)` and their
norm bound drawn from `ℚ_[p]` (the only genuinely `ℚ_[p]`-specific step in the proof is
`norm_succ_inv_smul_pow_le`'s use of `Padic.norm_eq_zpow_neg_valuation` / `Padic.valuation_natCast`),
whereas Conrad's literature-standard (and mathlib-idiomatic) form states the isometry over *any*
complete nonarchimedean char-0 field. The narrowing is genuine and non-cosmetic — the result is
needed verbatim for `ℂ_p` and finite extensions of `ℚ_p` (where carrying `[NormedAlgebra ℚ_[p] L]`
is awkward), and the isometry core is already field-internal so the generalisation is real. This is
the **exact same single narrowing axis, and verdict, as the log-side's def `padicLog`
(`YES-but-generalise-first`) and the exp-side isometry `norm_padicExp_sub_padicExp`
(`YES-but-generalise-first`, reason LITERATURE-WEAKENING)** already on file — `norm_padicLog` is
their structural twin and inherits the same upstreaming logic. Cost (MODERATE: reroute one
coefficient-norm bound through a residue-char-`p` hypothesis) is explicitly **not** a downgrade
factor — mathlib ships the right form.

**Refactor / upstreaming plan (YES-but-generalise-first):**

Reason for the generalisation:
- **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower than the
  Conrad/Cassels/Robert standard form — a redundant `[NormedAlgebra ℚ_[p] L]` packaging with the
  rational coefficients / their norm bound pulled through `ℚ_[p]`. The standard isometry is over
  any complete nonarchimedean char-0 field.
- **MODERN-IDIOM (secondary, same direction, NOT independent):** Phase 4c — the complete
  nonarchimedean `[CharZero K]`-field form is the mathlib-idiomatic target and is the missing
  nonarchimedean partner to `NormedSpace.exp`.

Proposed restatement:
```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

theorem norm_padicLog' (p : ℕ) [Fact p.Prime] {x : K}
    (hp : ‖(p : K)‖ = (p : ℝ)⁻¹)            -- residue-char-p input replacing the ℚ_[p]-algebra
    (hx : ‖x - 1‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖padicLog' x‖ = ‖x - 1‖ := by
  sorry  -- isometry core (strict tail-domination via `norm_succ_inv_smul_pow_lt` +
         -- strong-triangle `norm_add_eq_max_of_norm_ne_norm`) is field-internal; only the
         -- per-term coefficient-norm bound `‖((n:K)+1)⁻¹‖ ≤ pⁿ` must be re-derived from `hp`
         -- instead of `Padic.norm_eq_zpow_neg_valuation` on ℚ_[p].
```
Estimated cost of regeneralisation: **MODERATE** (the isometry argument is field-internal; only the
coefficient-norm Legendre bound is rerouted through `hp`). EXPENSIVE/MODERATE does **not** downgrade
the verdict — mathlib's value is in the right form, not the cheap one.

Mathlib downstream this enables (REQUIRED — MODERN-IDIOM):
- the log isometry (and the matched exp/log bijection) then applies verbatim to `ℂ_p` and every
  complete nonarchimedean extension of `ℚ_p`, with no `[NormedAlgebra ℚ_[p] L]` instance to drag in;
- it composes with the generalised `padicLog` def (`YES-but-generalise-first` on file) and is the
  missing nonarchimedean analytic partner to `NormedSpace.exp`;
- it is the engine of multiplicativity (`padicLog_mul` uses it to keep `log x` in the ball) and of
  the `xˢ := exp(s·log x)` / `onePAdicPow` character identification — both then available over any
  such field.

Proposed mathlib location (post-generalisation): ship as part of the **one coherent "p-adic exp/log"
PR group** — `Mathlib/NumberTheory/Padics/Logarithm.lean` (new) (or `Mathlib/Analysis/Normed/Field/`),
together with the generalised `padicLog` def, the `InExpBall` predicate, `summable_padicLog_terms`,
`norm_succ_inv_smul_pow_lt`, the exp side (`padicExp`, `norm_padicExp_sub_padicExp`,
`norm_padicExp_sub_one`, `padicExp_add`), and the inverse identities.
Proposed PR title: `feat(NumberTheory/Padics): p-adic logarithm is a norm-isometry on its ball`
PR grouping (REQUIRED): ship with the rest of the cluster already verdicted YES-but-generalise-first —
`padicLog` (def), `norm_padicExp_sub_padicExp`, and (pending their own resolutions) `padicExp`,
`summable_padicExp_terms` — as a single nonarchimedean-exp/log series. The PR grain is the *whole*
exp/log API, not this lemma alone.

Pre-PR checklist before opening:
- [ ] **First unify the within-repo duplicate** `BernoulliRegular.FLT37.PadicL.padicLog` with this
      project's `padicLog` on a `dev` branch (AINTLIB cross-project dedup) — the general
      `CharZero`-field form subsumes both.
- [ ] `/generalise PadicLFunctions.norm_padicLog` — tension against the literature-standard form
      (Phase 3) and the modern-idiom form (Phase 4c); confirm the `hp : ‖(p:K)‖ = p⁻¹` input is the
      minimal residue-char hypothesis.
- [ ] `/cleanup PadicExp.lean PadicLFunctions.norm_padicLog` — full audit + diff gates.
- [ ] Pick a mathlib reviewer from `Mathlib/NumberTheory/Padics/` recent commits.

Next action: run `/generalise PadicLFunctions.norm_padicLog` (it will tension against both the
literature-standard form from Phase 3 and the modern-idiom form from Phase 4c), **after** unifying
the two repo `padicLog` definitions and **together with** the rest of the p-adic exp/log cluster.

---

## Next step

Run `/generalise PadicLFunctions.norm_padicLog` to restate the isometry over a complete
nonarchimedean `[CharZero K]` field (replacing `[NormedAlgebra ℚ_[p] L]` + `ℚ_[p]`-pulled
coefficients with a residue-char-`p` hypothesis `‖(p:K)‖ = p⁻¹`), **after** unifying the within-repo
duplicate `padicLog` and **as part of** the single coherent p-adic exp/log PR group (alongside the
`padicLog` def and `norm_padicExp_sub_padicExp`, both already `YES-but-generalise-first`). Then
`/cleanup` the file and open the grouped mathlib PR to `Mathlib/NumberTheory/Padics/`.
