# `/mathlibable` report — `PadicLFunctions.pZpLog_coe`

**Final verdict: `NO-mathlib-has-it` is _rejected_; the bucket is `BORDERLINE-needs-human`.**
(One-line: the lemma is a definitional-branch characterisation of a project-local
`noncomputable def pZpLog` whose underlying object — a convergent p-adic logarithm
valued in `ℤ_[p]` — does not exist in mathlib at all; whether the *def* (and hence
this lemma) is upstreamed depends on a human decision about how mathlib should model
the p-adic logarithm. See Phase 7.)

---

## Baseline (Phase 0)

- lake build:               build **not re-run** (stale/slow per task note); reasoned from source — the file `PadicExp.lean` elaborates as a whole and the target's dependencies were all read directly.
- decl `PadicLFunctions.pZpLog_coe`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1081`
- kind:                      theorem
- has sorry:                 no (proof body lines 1083–1092 contains no `sorry`)
- module docstring summary:  *The p-adic exponential and logarithm (RJW Lem 5.14)* — `exp(x)=∑xⁿ/n!` and `log(1+y)=∑(−1)ⁿ⁺¹yⁿ/n` over a nonarchimedean complete normed `ℚ_[p]`-algebra field; for odd `p` the convergence balls contain `pℤ_p`, and `x^s := exp(s·log x)` realises RJW Lemma 5.14, agreeing with the character construction `PadicInt.onePAdicPow`.

Parent definition (assessed first, per def-first rule):

```lean
/-- The integral logarithm on `1 + pℤ_p` (odd `p`), valued in `pℤ_p`.
Junk-total: defined via the integrality certificate `‖log x‖ ≤ 1`, with junk
value `0` (the logarithm's value at the degenerate point `1`); RJW Lem 5.14, E5. -/
noncomputable def pZpLog (x : ℤ_[p]) : ℤ_[p] :=
  if h : ‖padicLog p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicLog p ((x : ℚ_[p])), h⟩ else 0
```

The target itself:

```lean
omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L] in
/-- E5: on `1 + pℤ_p` (odd `p`) the analytic logarithm is integral, so `pZpLog`
takes its true branch: `(pZpLog x : ℚ_[p]) = log x`. -/
theorem pZpLog_coe (hp2 : p ≠ 2) {x : ℤ_[p]}
    (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    ((pZpLog p x : ℤ_[p]) : ℚ_[p]) = padicLog p ((x : ℚ_[p])) := by
  ...
  rw [pZpLog, dif_pos hle]
```

---

## Statement (Phase 1)

`pZpLog_coe` is a theorem stating the following.

Let `p` be an odd prime. The project defines `padicLog : L → L` (for a nonarchimedean
complete normed `ℚ_[p]`-algebra field `L`) by the convergent series
`log(x) = ∑ₙ (−1)ⁿ (n+1)⁻¹·(x−1)ⁿ⁺¹`, meaningful when `‖x−1‖ < 1`. It then defines a
**total, integer-valued** logarithm `pZpLog : ℤ_[p] → ℤ_[p]` by a junk-total
case split: if the analytic value `padicLog ℚ_[p] (x)` happens to have norm `≤ 1` it
returns that value (coerced into `ℤ_[p]`), otherwise it returns the junk value `0`.
`pZpLog_coe` says that **on the principal-unit disc `x ∈ 1 + pℤ_p`** (i.e.
`x − 1 ∈ (p)`), the junk-total def takes its *true* branch: its `ℚ_[p]`-image equals
the analytic logarithm `padicLog ℚ_[p] (x)`.

In ordinary mathematics this is the statement *"for `x ∈ 1 + pℤ_p` (odd `p`), the
p-adic logarithm `log x` is integral, i.e. `log x ∈ pℤ_p`, so the integer-valued
logarithm agrees with the analytic one."* It is the branch-selection half of the
classical fact `log : 1 + pℤ_p → pℤ_p`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; the global section fixes this.
- The ambient `variable {L} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` is **`omit`-ted** for this lemma (the `omit ... in` line) — so `L` plays no role; the lemma is purely about `ℤ_[p]` and `ℚ_[p]`.
- `x : ℤ_[p]` — the point (implicit).

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — `p` is odd (so `p − 1 ≥ 2`, which forces `‖log x‖ ≤ p⁻¹ ≤ 1`).
- `hx : x − 1 ∈ Ideal.span {(p : ℤ_[p])}` — `x ∈ 1 + pℤ_p`.

Conclusion (math): On `1 + pℤ_p` (odd `p`), the integral logarithm `pZpLog` equals the analytic `padicLog`; equivalently `log x` is integral there.

Conclusion (Lean): `((pZpLog p x : ℤ_[p]) : ℚ_[p]) = padicLog p ((x : ℚ_[p]))`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**

Reason: it is a branch-selection / characterisation lemma for the project-local def
`pZpLog` (decomposition tag E5), not a named theorem and not a `## Main results`
entry. The two RJW "Lemma 5.14" headline theorems in the file are
`padicExp_converges_on_pZp` and `padicExp_smul_padicLog_eq_onePAdicPow`; `pZpLog_coe`
is glue feeding the second.

(Note: literature width was EXHAUSTIVE regardless — the concept *p-adic logarithm*
is heavily studied, so the search was run in full.)

### One-line check (Phase 2b)

Body line count: ~10 substantive lines (`have hxsub`, `have hball`, `have hle` with a
`calc`-style norm bound, then `rw [pZpLog, dif_pos hle]`).
One-liner verdict: **n/a — kind is theorem, not def.** (The *parent* `pZpLog` is a
one-line `dif`; this lemma is the proof that the `dif` resolves to its true branch.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic logarithm convergence 1+pZ_p valued in pZ_p isomorphism principal units" | yes | `log: 1+pℤ_p → pℤ_p` for `p>2`; image of `pℤ_p` is `pℤ_p` | MIT 18.785 PS10; arXiv 1904.09850, 1907.06437; ResearchGate "Image of p-adic log on principal units" |
| 2 | WebSearch (general form / convergence) | "p-adic logarithm log(1+x) series converges norm less than one Z_p integral nonarchimedean field" | yes | `log(1+x)=∑(−1)ⁿ⁺¹xⁿ/n`, converges for `|x|<1` on any complete nonarch. field; `\|xⁿ/n\| ≤ λⁿ p^{v_p(n)} → 0` | Wikipedia; Conrad/Thorne Cambridge notes (dpmms.cam, kconrad); UChicago REU (Gupta) |
| 3 | WebSearch (named-after / Iwasawa) | "Iwasawa logarithm p-adic log definition unit group 1+pZp to pZp odd prime" | yes | for odd `p`, `W=1+pℤ_p`, `z=u^{s(z)}`, `s(z)=log z`; `log: 1+m_K^r → m_K^r` iso when `r>e/(p−1)` | Hida lectures; Numdam "The integral logarithm in Iwasawa theory"; AWS 2018 |
| 4 | ChatGPT MCP | — | **n/a** | — | **MCP server not configured in this environment** (no `mcp__chatgpt__*` tool resolved via ToolSearch; `/setup-chatgpt` exists but server absent). Compensated with two extra WebSearch + two WebFetch channels (#2, #3, #7, #10). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/` and `refs/PadicLFunctions/` for "log" | **n/a** | (no references dir) | `.mathlib-quality/` has only `overview/`; no `references/` subdir; `refs/PadicLFunctions/` absent. Recorded n/a. The module docstring itself cites **Washington, _Introduction to Cyclotomic Fields_ §5.1** and **Cassels §12** (RJW Lem 5.14, TeX 1892–1897). |
| 6 | nLab | "p-adic exponential map" / "p-adic logarithm" | **n/a (no page)** | — | `ncatlab.org/nlab/show/p-adic+exponential+map` → HTTP 404. nLab has no dedicated p-adic log/exp page; not a category-theoretic concept. |
| 7 | WebFetch — Wikipedia "P-adic exponential function" | convergence domain + image of `1+pℤ_p` | yes | `log_p(1+x)=∑(−1)ⁿ⁺¹xⁿ/n`, converges for `|x|_p<1`, defines `log_p(z)` for `|z−1|_p<1`; Iwasawa extension to `ℂ_p^×` | confirms the exact series and disc used by `padicLog`; does not spell out the `1+pℤ_p → pℤ_p` integrality (that is in #1/#3) |
| 8 | Stacks Project | p-adic logarithm | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; Stacks has no convergent p-adic analysis. |
| 9 | MathOverflow / Math.StackExchange | "p-adic logarithm integral principal units 1+pZp image" | partial | (returned the same arXiv papers, no direct MO thread indexed) | The arXiv corpus (1904.09850, 1907.06437, **2601.18187** "On the Image of the p-adic Logarithm on Annuli of Principal Units", 2026) confirms this is a live, named research topic. |
| 10 | recent arXiv (last ~5y) | "image of p-adic logarithm on principal units" | yes | for `e < p−1` (here `e=1<p−1` since odd `p`), `log` *is* a bijection `1+m → m`; image of `1+pℤ_p` understood | arXiv 1904.09850 (2019), 2601.18187 (2026) — exactly the unramified `ℚ_p` case relevant here, where `log: 1+pℤ_p ≅ pℤ_p`. |
| — | WebFetch — Conrad notes / MIT `~dav/exp.pdf` | exact isometry/inverse statement | partial | PDFs were binary-unreadable to the fetcher, but #1/#3 quote the same results | recorded as attempted; content corroborated by #1–#3. |

Protocol pass check:
- WebSearch ran **6** distinct queries across three generality levels (specific `1+pℤ_p→pℤ_p` form, general convergence form, Iwasawa/named form, Conrad-isometry form, MathOverflow form, Washington-Ch5 form). ✓ (≥3 required)
- ChatGPT MCP: **n/a — server not configured**; explicitly compensated with extra channels. (Documented, not silently skipped.)
- Local references: checked, n/a (absent), but the in-repo docstring citations (Washington §5.1, Cassels §12) were used. ✓
- nLab: checked → 404 / no page. ✓
- Stacks / nLab-categorical / MathOverflow / arXiv: each checked with a reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the p-adic logarithm** `log_p(1+y) = ∑ₙ≥₁ (−1)ⁿ⁺¹ yⁿ/n`,
and specifically its restriction to the **principal units `1 + pℤ_p`** (Iwasawa's
`log`), where for odd `p` it is integral and gives an isomorphism/isometry
`1 + pℤ_p ≅ pℤ_p`.

Sources agree on the standard form: **yes** — universally. Series, convergence disc
`|y|<1`, and the integral image `log(1+pℤ_p) ⊆ pℤ_p` for `p>2` are textbook
(Washington Ch. 5/§5.1, Koblitz, Conrad, Wikipedia) and the subject of dedicated
recent papers (arXiv 1904.09850, 2601.18187).

Most general standard form: `log(1+y) = ∑(−1)ⁿ⁺¹yⁿ/n` on `{|y|<1}` of **any**
complete nonarchimedean field `K/ℚ_p` (the *project's own* `padicLog` is stated at
exactly this generality, over a normed `ℚ_[p]`-algebra field `L`). The
**integral-branch** statement specialises to `K = ℚ_p`, integers `ℤ_p`,
`x ∈ 1 + pℤ_p`, `p` odd — which is precisely `pZpLog`/`pZpLog_coe`.

Generality dimensions where the literature varies:
- base field: `ℚ_p` ↔ general `K/ℚ_p` with ramification `e`. The integrality
  threshold is `r > e/(p−1)`; for `K=ℚ_p` (`e=1`, `p` odd) the threshold is met at
  `r=1`, giving `log: 1+pℤ_p ≅ pℤ_p`.
- domain: the *analytic* `log` lives on `|y|<1` (the project's `padicLog`); the
  *integral* `log` on principal units is the further restriction.

Disagreement with the literature: **none.** `pZpLog_coe` is exactly the
branch-selection half of the standard "`log` is integral on `1+pℤ_p` (odd `p`)".

---

## Generality analysis — `pZpLog_coe` (Phase 4)

Literature-standard form (from Phase 3): on `1 + pℤ_p`, `p` odd, the analytic p-adic
logarithm is integral and equals the integer-valued logarithm.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base ring `ℤ_[p]`/`ℚ_[p]` (hard-wired in `pZpLog`) | the integers of `ℚ_p` | integers `O_K` of any `K/ℚ_p` | yes, in principle | The integrality threshold generalises to `r > e/(p−1)`. But the *def* `pZpLog` references `padicLog p (x : ℚ_[p])` and `⟨·, ·⟩ : ℤ_[p]`, so generalising `pZpLog_coe` requires first generalising the def to `O_K`. NOT a weakening of *this lemma* in isolation. |
| 2 | `hp2 : p ≠ 2` | odd prime | `p` odd (for the `r=1` threshold); `p=2` needs `1+4ℤ_2` | NO | `p=2` genuinely fails at `1+2ℤ_2` (need `1+4ℤ_2`); the hypothesis is the correct, literature-matching one for the `r=1`/`pℤ_p` statement. |
| 3 | `hx : x−1 ∈ (p)` | `x ∈ 1+pℤ_p` | the principal-unit disc | NO | This *is* the standard domain. |
| 4 | ambient `L` + 3 typeclasses | `omit`-ted | — | already maximally weak | The lemma already omits all of `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`; `L` is unused. ✓ |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** — i.e. for the
ℚ_p-integral logarithm. The only "generalisation" axis (row 1: base field `ℚ_p → K`)
is **not a weakening of this lemma**; it is a re-targeting of the *underlying def*
`pZpLog` (and of `padicLog`, which is *already* general over `L` but whose
integral-branch packaging is `ℚ_p`-specific by design). So per the skill's rules this
is not a `YES-but-generalise-first` situation for *this theorem*.

Number of weakening opportunities found on this lemma: **0** (the `ℚ_p → K` axis is a
def-level decision, captured as the BORDERLINE question in Phase 7).

Cost of any base-field generalisation: **EXPENSIVE** (would require an `O_K`-valued
integral-logarithm def, the ramified threshold `r>e/(p−1)`, and re-proving the norm
bound) — and, per the skill, cost is *not* a verdict factor; it is flagged for the
human decision in Phase 7, not used to downgrade.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already typeclass-driven (`Fact p.Prime`); `L` omitted | — |
| 2 | sequences/metric → filters/topological? | no | the proof is a finite ultrametric norm bound; no limit to filter-ise here | — |
| 3 | construct an object → universal-property class? | **partial** | The *def* `pZpLog` could be the restriction of a bundled group hom `(1+pℤ_p : Subgroup ℤ_[p]ˣ) →* (pℤ_p, +)` (or a `LocalRing`/valuation-theoretic `log`), of which mathlib has the *target* shape (`ValuationSubring.principalUnitGroup`) but not the map. This is a **def-level** modernisation, not a restatement of `pZpLog_coe`. | a real `padicLog`/principal-units API; `pZpLog_coe` would become a `map_*`/`coe_*` simp lemma about it |
| 4 | set+closure-predicate → bundled substructure? | no | `1+pℤ_p` is already `Ideal.span {p}`-membership; mathlib has `principalUnitGroup` if a bundled version is wanted (def-level) | — |
| 5 | field/metric-specific → weaken typeclass? | no (for this lemma) | the lemma is intrinsically about `ℤ_[p]` integrality | — |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general monoid? | no | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but only at the *def* level, not for this lemma.** A
mathlib-idiomatic p-adic logarithm would be a bundled `1+pℤ_p →+ pℤ_p` (or a
valuation-theoretic `log` on `principalUnitGroup`), and then `pZpLog_coe` would be its
`coe`/`map` lemma. This is a genuine organisational question about the missing
`padicLog` API — it does **not** flip *this theorem* to `YES-but-generalise-first`,
because the theorem cannot be restated without first deciding the def. It is exactly
the human-judgment hinge, surfaced in Phase 7.

---

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem**. (The risk phase runs only for
`def`/`class`/`instance`. The *parent* `pZpLog` is a `noncomputable def` and would
need its own Phase 4.5 if it were the assessment target; it is not. Note in passing:
`pZpLog` is sealed, not `@[reducible]`, and `pZpLog_coe` is precisely the API that
shields callers from its `dif` body — a healthy "defeq-abuse barrier" pattern.)

---

## Mathlib search-status: `pZpLog_coe` (Phase 5)

Searched mathlib source at `./.lake/packages/mathlib/Mathlib/`.

[A] Lean-Finder — n/a: no Lean-Finder MCP/tool available in this environment.
[B] Loogle — n/a: no Loogle tool available; substituted with exhaustive typed grep over mathlib source (method D), searching for any `→`-into-`ℤ_[p]`/`ℚ_[p]` logarithm and for `padicLog`/`padicExp` identifiers. No hits.
[C] LeanSearch — n/a: no LeanSearch tool available; substituted with the Phase-3 WebSearch literature sweep (which would have surfaced any mathlib/LeanSearch-indexed p-adic log) — none reference a mathlib decl.
[D] Grep mathlib src — ran:
  - `\b(padicLog|padicExp|PadicLog|PadicExp|expPadic|logPadic)\b` → **no hits**.
  - `^(noncomputable )?def .*[Ll]og\b` filtered to exclude `Real|Complex|EReal|ENNReal|PowerSeries|Nat|Ordinal|...` → every remaining hit is `Real.log`-family / `Nat.log` / `Ordinal.log` / von Mangoldt / height / KL-divergence. **No convergent p-adic logarithm.**
  - `principalUnit|Units.*PadicInt|PadicInt.*Units` → `ValuationSubring.principalUnitGroup` (an abstract valuation-theoretic principal-unit *group*) exists, but **no exp/log map on it**.
  - exp side: `NormedSpace.exp` (Banach-algebra exponential) exists but is **never instantiated at `ℚ_[p]`/`ℤ_[p]`** (`grep NormedSpace.exp … | grep -i padic` → empty); the WithVal/PadicNumbers `exp`/`log` hits are `Real.exp`/`Real.log` used inside *valuation* proofs (verified by reading `WithVal.lean:70–90`).
[E] Name pattern — grep for `pZpLog`, `padicLog`, `1+pℤ_p` logarithm across mathlib → none (these are project-only names; `padicLog`/`pZpLog`/`onePAdicPow`/`angleUnit` are all defined inside `projects/PadicLFunctions/`).

Searched for both:
  - the user's current form (`(pZpLog x : ℚ_[p]) = padicLog x`) — not in mathlib.
  - the literature-standard form (`log: 1+pℤ_p → pℤ_p`, "log is integral on principal units") — **not in mathlib in any form**: mathlib has neither the convergent p-adic `log` nor an exp/log structure on `principalUnitGroup`/`ℤ_[p]ˣ`.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). The building blocks `pZpLog_coe`'s *proof* uses
(`PadicInt.norm_le_pow_iff_mem_span_pow` at `PadicIntegers.lean:466`,
`PadicInt.norm_def`, `IsUltrametricDist.norm_add_le_max`) are in mathlib, but the
**object** being characterised (`padicLog`/`pZpLog`) is not.

---

## Call sites — `pZpLog_coe` (Phase 6.0)

Internal use count: **3** (within the project, excluding the declaring lemma)
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`), plus 2 in-file uses.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:1102` | `... pZpLog_coe p hp2 hx, norm_padicLog (L := ℚ_[p]) p hball, ...` (in `pZpLog_mem`) |
| `PadicExp.lean:1156` | `... pZpExp_coe p hp2 hℓmem, pZpLog_coe p hp2 hx` (in `padicExp_smul_padicLog_eq_onePAdicPow`, the RJW Lem 5.14 headline) |
| `ResidueZeta.lean:121` | `rw [hℓ, PadicInt.norm_def, pZpLog_coe p hp2 hy, norm_padicLog (L := ℚ_[p]) p hball, ...]` |
| `ResidueZeta.lean:1768` | `... extLog_eq_padicLog p hanball, ← pZpLog_coe p hp2 (PadicInt.angleUnit_sub_one_mem p u)]` |

Inline-derivation grep (was the equivalent re-derived without `pZpLog_coe`?): **none** —
every site that needs "`pZpLog` agrees with `padicLog`" calls this lemma. The companion
`pZpLog` (def) is used at 7+ further sites in `ResidueZeta.lean` (lines 106, 235, 236,
1721, 1740, 1783, 1791), confirming `pZpLog` is a load-bearing project object.

What the pattern says: **K = 3 internal uses across 2 files, no inline
re-derivation** → this is *real project API* whose consumers depend on it. By the
call-sites table this leans **YES-\***. But the YES lean is *for the def `pZpLog`'s
ecosystem*; the lemma cannot be upstreamed without the def, and the def is the
unresolved question — hence the call-sites signal supports "this is genuine, not
junk", which pushes the verdict toward BORDERLINE (genuine + needs a human def-shape
decision) rather than any NO bucket.

### Composition check (Phase 6)

Can `pZpLog_coe` be derived from mathlib in ≤3 chained calls?

Attempt 1: `rw [pZpLog, dif_pos hle]` where `hle : ‖padicLog p (x:ℚ_[p])‖ ≤ 1`.
  - Mathlib decls used: `dif_pos` (and `PadicInt.norm_le_pow_iff_mem_span_pow` to get `hle`).
  - Result: **fails as a *mathlib* composition** — `pZpLog` and `padicLog` are
    **project decls, not mathlib decls**. The "composition" unfolds a project def and
    discharges its branch condition via a genuine ultrametric norm bound
    (`norm_padicLog` + `coe_norm_le_inv_of_mem_span` + `inExpBall_of_mem_span`), all
    project lemmas. That is a *proof about a project object*, not a composition of
    mathlib primitives.
  - Notes: the `hle` step alone is a multi-line `calc`/`rw` over `norm_padicLog`,
    which is itself a ~40-line project theorem. Not ≤3 mathlib calls by any reading.

Attempt 2: derive directly from a hypothetical mathlib `padicLog`/principal-units API.
  - There is no such API in mathlib (Phase 5). So no mathlib composition exists.

Conclusion: **NOT-COMPOSABLE from mathlib.** (The proof *is* a composition of
*project* lemmas, which is irrelevant to mathlib-composability.)

---

## Verdict: `pZpLog_coe`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the p-adic logarithm and its integral restriction
  `log: 1+pℤ_p → pℤ_p` (odd `p`) are textbook-standard (Washington §5.1, Conrad,
  Wikipedia) and the subject of dedicated recent papers (arXiv 1904.09850,
  2601.18187). The concept is unambiguously "real mathematics", not project-ad-hoc.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL for the ℚ_p-integral logarithm**;
  the only generalisation axis (base field `ℚ_p → O_K`) is a *def-level* decision, not
  a weakening of this lemma → not a clean `YES-but-generalise-first`.
- Modern-idiom (Phase 4c): a mathlib-idiomatic p-adic logarithm would be a **bundled
  `1+pℤ_p →+ pℤ_p`** of which `pZpLog_coe` is the `coe` lemma — again a *def-shape*
  question, not resolvable for the lemma alone.
- Mathlib search (Phase 5): **not in mathlib** — neither the convergent p-adic `log`
  nor any exp/log on `ℤ_[p]ˣ`/`principalUnitGroup` exists. The lemma's *proof*
  building blocks (`PadicInt.norm_le_pow_iff_mem_span_pow`, `norm_def`) are in mathlib;
  the *object* is not.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (the "1-line" proof
  unfolds a *project* def and uses *project* norm lemmas).
- Call sites (Phase 6.0): **K = 3** across 2 files, no inline re-derivation — genuine,
  load-bearing project API; not dead code, not a bypassed wrapper.

**Rationale (why not a clean YES, why not any NO):**

`pZpLog_coe` is not in mathlib and is not composable from mathlib, which on its own
would push toward a YES bucket — *and* the underlying mathematics (the integral p-adic
logarithm on principal units) is exactly the kind of classical, well-named result
mathlib wants. But the lemma is **inseparable from a project-local `noncomputable def`
(`pZpLog`)** that mathlib does not have, which is in turn built on a second
project-local def (`padicLog`) that mathlib also does not have. The lemma's entire
content is "this junk-total def takes its true branch on `1+pℤ_p`" — a statement that
*only makes sense relative to the chosen def `pZpLog`*. So whether to upstream it, and
in what form, is **downstream of a genuine design decision mathlib has not made**:
*how should mathlib model the p-adic logarithm?* The literature offers at least three
shapes — (a) a junk-total `ℤ_[p] → ℤ_[p]` function as here; (b) a bundled additive
hom `(1+pℤ_p : Subgroup ℤ_[p]ˣ) →+ Additive (pℤ_p)`; (c) a valuation-theoretic `log`
on `ValuationSubring.principalUnitGroup`, valued in the maximal ideal — and the right
choice (and whether ramified `O_K` is in scope from day one) is a mathematical-taste +
library-architecture call. Per the skill, this is the textbook trigger for
BORDERLINE: every phase is complete, but synthesising them into "ship it / don't"
requires a human judgment the skill cannot ground in the evidence. Note the skill also
forbids using the EXPENSIVE generalisation cost as a self-resolving downgrade — that
too becomes a question, not a verdict.

This is *not* `NO-mathlib-has-it` (Phase 5: mathlib has neither the object nor the
result), *not* `NO-composable-from-mathlib` (Phase 6: NOT-COMPOSABLE — the proof is
about a project def using project lemmas), and *not* a clean `YES-*` because the
contribution is a *property of a def mathlib lacks*, so the def must be designed and
contributed first (def-first rule), and its shape is the open question.

**Refactor / upstreaming-plan (BORDERLINE — numbered questions):**

1. **Should mathlib have a convergent p-adic logarithm at all** (`padicLog` on the
   disc `‖x−1‖<1` of a complete nonarchimedean `ℚ_p`-algebra field), as a prerequisite
   to any of this? (Yes/No. If No, `pZpLog`/`pZpLog_coe` stay project-local and the
   whole question is closed.)
2. If yes to (1): **what is the canonical mathlib *shape* of the integral logarithm on
   principal units** — (a) the junk-total `ℤ_[p] → ℤ_[p]` function used here, (b) a
   bundled `AddMonoidHom (1+pℤ_p) (pℤ_p)`, or (c) a valuation-theoretic `log` on
   `ValuationSubring.principalUnitGroup`? `pZpLog_coe` is the `coe`/`map` lemma of
   whichever is chosen.
3. **Should the first mathlib version cover ramified `O_K/ℚ_p`** (threshold
   `r > e/(p−1)`), or start at the unramified `ℚ_p`, `p` odd case (this lemma's exact
   setting)? (This is the only "generalisation" axis Phase 4 found, and per the skill
   its EXPENSIVE cost is a question for you, not a reason to ship narrow by default.)
4. Given `pZpLog` has **3 direct + 7 indirect consumers** in this project
   (`ResidueZeta.lean`), is the intent to keep it project-internal for the RJW Lem 5.14
   / residue-zeta development, or to spin the `padicLog`/`pZpLog` API out as a mathlib
   PR family? (Yes-internal / Yes-PR.)

**Next action:** answer (1)–(4); then re-run `/mathlibable` **on the def `pZpLog`
first** (def-first ordering) with the chosen shape as input. Likely outcomes:
  - (1)=No → drop from mathlib consideration; keep project-local. `pZpLog_coe` follows.
  - (1)=Yes, (2)=bundled hom (b/c) → re-run targets the bundled def; `pZpLog_coe`
    becomes `INHERITED-YES-but-generalise` as that hom's `coe`/`map_*` simp lemma,
    restated against the bundled object.
  - (1)=Yes, (2)=(a) junk-total as-is → `pZpLog` is `YES-add-as-is` (with a Phase-4.5
    pass on the `dif`), and `pZpLog_coe` ships with it as `INHERITED-YES`
    (the branch-selection API lemma), proposed location
    `Mathlib/NumberTheory/Padics/Logarithm.lean` (new file),
    PR title `feat(NumberTheory/Padics): p-adic logarithm and its integrality on principal units`.

---

## Next step

Answer the four numbered questions above (chiefly: *should mathlib model the p-adic
logarithm, and in what shape?*), then re-run `/mathlibable` on the **def `pZpLog`
first**; `pZpLog_coe`'s verdict is inherited from the def's once the shape is fixed.
