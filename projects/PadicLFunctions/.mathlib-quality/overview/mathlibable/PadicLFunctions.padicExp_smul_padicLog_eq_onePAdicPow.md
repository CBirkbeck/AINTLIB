# `/mathlibable` report — `PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow`

Mode A, full 10-phase workflow, exhaustive 9-channel literature sweep.
`--refs=/Users/mcu22seu/.claude/plugins/cache/mathlib-quality-plugins/mathlib-quality/0.50.0/skills/mathlib-quality/references`

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — Phase 0 fallback). Declaration and all dependencies read directly from source.
- decl `PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow`: ✓ resolved, unique, at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1111`
- kind:                      theorem
- has sorry:                 no (proof is complete: builds a bespoke `AddChar κ`, proves continuity + value-at-1, invokes uniqueness)
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp`/`log` on the matched balls of a nonarchimedean complete normed `ℚ_[p]`-algebra field; for `s ∈ ℤ_p`, `x ∈ 1+pℤ_p`, defines `x^s := exp(s·log x)` and identifies it with `PadicInt.onePAdicPow`.

---

### Statement (Phase 1)

`padicExp_smul_padicLog_eq_onePAdicPow` is a **theorem** stating the following:

> Fix an odd prime `p` and `x ∈ 1 + pℤ_p` (i.e. `x − 1 ∈ pℤ_p`). The project's
> integral analytic power `s ↦ exp(s·log x)` — packaged as the `ℤ_p`-valued
> map `s ↦ pZpExp p (s · pZpLog p x)` — coincides, for every `s ∈ ℤ_p`, with the
> Mahler-series continuous additive character `PadicInt.onePAdicPow p x hx`.

In words: the **two project constructions** of `x^s` agree pointwise. One is
analytic (the truncated/junk-totalised exp/log series `pZpExp`, `pZpLog`); the
other, `onePAdicPow`, is the unique continuous additive character `ℤ_p → ℤ_p`
sending `1 ↦ x` (a thin wrapper over mathlib's `PadicInt.addChar_of_value_at_one`).
The proof packages `s ↦ pZpExp p (s·ℓ)` (where `ℓ = pZpLog p x`) as an honest
`AddChar`, proves it is continuous (Lipschitz-1) and takes value `x` at `1`, then
invokes mathlib's uniqueness lemma `PadicInt.eq_addChar_of_value_at_one`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `x : ℤ_[p]` (implicit) — the base, a principal unit.
- `s : ℤ_[p]` — the exponent.

Hypotheses (Lean side):
- `hp2 : p ≠ 2` — oddness (needed so `pℤ_p` lies inside the exp/log convergence ball).
- `hx : x − 1 ∈ Ideal.span {(p : ℤ_[p])}` — `x ∈ 1 + pℤ_p`; doubles as the witness that `onePAdicPow p x hx` is well-defined.

Conclusion (math): `exp(s·log x) = x^s` where the right side is the canonical continuous character — i.e. the analytic and character constructions of the p-adic power agree.

Conclusion (Lean): `pZpExp p (s * pZpLog p x) = PadicInt.onePAdicPow p x hx s` (an equality in `ℤ_[p]`).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (a glue/bridge identification between two already-defined project constructions).
Reason: not a new structure, not a person/place-named theorem; it is a "two constructions agree" lemma whose *only* job is to let the analytic norm-API and the character-API be used interchangeably downstream. The substantive math (exp/log convergence and inversion) lives in its dependencies (`padicExp_padicLog`, `pZpExp_coe`, `pZpLog_coe`), not here.

(Literature width is EXHAUSTIVE regardless; BIG/SMALL is recorded for framing.)

### One-line check (Phase 2b)

Body line count: ~50 substantive lines.
One-liner verdict: **n/a** — kind is `theorem`, not `def`. (For the record the proof is long and non-trivial: a full `AddChar` construction + Lipschitz continuity + uniqueness invocation. Nothing one-line about it.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|----------------------|-------|
| 1 | WebSearch (specific form) | "p-adic power x^s exp(s log x) equals continuous character 1+pZp uniqueness" | partial | `x^s := exp(s·log x)`; characters of `1+pℤ_p` are `y ↦ exp(s·log y)`; uniqueness under restriction | Davis–Wan, Gupta REU, K. Conrad. Literature defines the power *one* way (exp/log); no named "two-constructions-agree" theorem. |
| 2 | WebSearch (general form) | "continuous additive character Z_p unique determined value at 1 Mahler series p-adic interpolation" | yes | Continuous functions on `ℤ_p` ↔ Mahler series (coeffs → 0); characters determined by value at 1 | Mahler's theorem (Wikipedia); de Shalit, "Mahler bases and elementary p-adic analysis". This is exactly mathlib's `addChar_of_value_at_one` setting. |
| 3 | WebSearch (named-after / aliases) | "p-adic exponentiation principal units x^s ZZ_p well-defined exp log Washington cyclotomic fields" | yes | `α^x := exp(x·log α)` for `|α−1|≤p^{-1}`, has expected properties | Wikipedia "p-adic exponential function"; Washington §5.1; Leiden notes ch.8; MIT 18.785 PS10. The *definition* is standard; agreement with a Mahler-character is not a stated theorem. |
| 4 | ChatGPT MCP | (would ask: "standard def of `x^s` on `1+pℤ_p`; is the agreement of `exp(s·log x)` with the Mahler-series / value-at-1 character a named theorem? historical evolution?") | n/a | — | ChatGPT MCP not configured in this environment (no `mcp__chatgpt*` tool); recorded n/a and compensated with extra WebSearch generality levels (rows 1–3, 11) + nLab + arXiv reads. |
| 5 | Local references | grep `.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | — | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor a `refs/` store exists in this checkout (refs are local-only and gitignored). Recorded n/a. Project source-citations (RJW Lem 5.14 TeX 1892–1894; Washington §5.1; Cassels §12) are taken from the module/decl docstrings instead. |
| 6 | nLab | "p-adic number" (exp/log power; characters of `ℤ_p` by value at 1) | no | — | nLab's `p-adic number` page covers construction/valuation/Pontryagin duality but **neither** the analytic exp/log power **nor** the Mahler-character-by-value-at-1; the agreement statement is absent. |
| 7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept (a pointwise equality of two concrete `ℤ_p`-valued functions). |
| 8 | Stacks Project (if alg geom) | — | n/a | — | Not an algebraic-geometry concept (p-adic analysis on `ℤ_p`, no schemes/sites). |
| 9 | MathOverflow / Math.StackExchange | "two constructions p-adic power function agree uniqueness continuous homomorphism Z_p Iwasawa" | partial | Iwasawa-algebra two-descriptions `ℤ_p[[T]] ≅ ℤ_p[[Γ]]` agree via uniqueness of continuous homs | Closest analog is the Iwasawa-algebra "two pictures agree by continuity+density" pattern, **not** this exp-vs-Mahler statement. Confirms the *method* (uniqueness of continuous characters) is folklore; the specific lemma is not named. |
| 10 | recent arXiv (last 5 yrs) | "addChar_of_value_at_one onePAdicPow p-adic exponential Lean mathlib" | no | — | arXiv 2504.03430, 2106.09315 etc. are about p-adic exp/log *applications*; none states the exp-vs-character agreement. Mathlib's own `AddChar` file (Loeffler 2025) is the only formalised home of the character side. |
| 11 | WebSearch (Lean/mathlib status) | "mathlib p-adic exponential logarithm Z_p addChar_of_value_at_one onePAdicPow Lean" | no | — | mathlib4 docs / community p-adics page confirm mathlib has `padicValNat`, `PadicInt`, `addChar_of_value_at_one`, but **no p-adic analytic exp/log** — so no exp-vs-character bridge can exist upstream. |

The protocol passes: WebSearch ran ≥3 distinct queries at three generality levels (specific power form / general Mahler-character form / named-textbook exponentiation), plus a Lean-status query; nLab checked (no hit); Stacks/nCatLab recorded n/a with reason; MathOverflow + arXiv checked; local refs n/a with reason; ChatGPT MCP n/a (unavailable) with explicit compensation.

### Literature summary (Phase 3)

Concept identified as: the **p-adic power / exponentiation** `x^s = exp(s·log x)` on principal units `1+pℤ_p`, and (separately) the characterisation of continuous additive characters of `ℤ_p` by their value at `1` (Mahler-series picture).

Sources agree on the standard form: **yes** for each *ingredient* separately —
(a) `x^s := exp(s·log x)` is *the* textbook definition of the p-adic power (Washington §5.1, Wikipedia, Gupta REU, Leiden notes), and (b) continuous characters of `ℤ_p` ↔ Mahler series / value-at-1 (Mahler's theorem; de Shalit; mathlib's `continuousAddCharEquiv`).

Most general standard form: there is **no literature theorem that states the agreement of these two constructions**, because the literature builds the p-adic power *only* via exp/log. The Mahler-series / value-at-1 construction of the same character is a formalisation-driven alternative (it exists in mathlib precisely because `addChar_of_value_at_one` is the mathlib-canonical way to build the character without first developing exp/log). The "agreement" is the folklore consequence of *uniqueness of continuous characters with a given value at 1* — a method the Iwasawa-algebra literature uses routinely (row 9), but not packaged as this lemma.

Generality dimensions where the literature varies:
- base ring: literature states the power over any complete nonarch. field of residue char `p`; this theorem is `ℤ_p`-only (forced — `onePAdicPow` and mathlib's `addChar_of_value_at_one` are `ℤ_p`-domain by construction).
- definition route: literature = exp/log only; mathlib = Mahler series. This theorem is precisely the *junction* of the two routes.

Disagreement with the literature: none — but the key takeaway is that **the statement is project-internal connective tissue between two specific Lean constructions**, not a transcription of a named literature result.

---

### Generality analysis (Phase 4)

Literature-standard form (from Phase 3): there is no single literature-standard form of *this equation*; the relevant standard objects are (i) the analytic power `exp(s·log x)` and (ii) the value-at-1 character. The theorem's content is "(i) = (ii) at `ℤ_p`".

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|----------------------------------|
| 1 | base ring `ℤ_[p]` (both sides) | `ℤ_p`-valued, `ℤ_p`-domain character | abstract complete nonarch. field for the analytic side | NO (for *this* statement) | The RHS `onePAdicPow`/`addChar_of_value_at_one` is intrinsically `ℤ_p`-domain (Mahler basis of `C(ℤ_p, R)`); the equation only typechecks at `ℤ_p`. Generalising the analytic side alone changes which theorem this is. |
| 2 | `hp2 : p ≠ 2` | odd `p` | exp/log ball contains `pℤ_p` iff `p` odd (`p=2` needs `4ℤ_2`) | NO | Genuinely needed: for `p=2` the exp/log series do not converge on all of `pℤ_2`, so the analytic side `pZpExp/pZpLog` is not the right object there. Sharp. |
| 3 | `hx : x − 1 ∈ pℤ_p` | `x ∈ 1+pℤ_p` | principal units `1+𝔪` | NO | This *is* the maximal domain on which both sides are defined; it is also the well-definedness witness for `onePAdicPow`. |
| 4 | RHS `pZpExp`/`pZpLog` (the junk-total `dite` analytic forms) | project-private scaffolding | genuine `padicExp`/`padicLog` | yes (idiom) | The cleaner statement uses the *honest* `padicExp`/`padicLog` (already in the file) rather than the integral junk-total `pZpExp`/`pZpLog`; see 4c. But that is a re-statement of a *different* equation, not a weakening of this one. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** *as a statement about these specific objects* (no hypothesis can be weakened — `p≠2` and `x∈1+pℤ_p` are both sharp; the base ring is forced to `ℤ_p` by the RHS). Number of weakening opportunities found: 0.
Proposed restatement: none at the *generality* axis.
Cost of restatement: n/a.

Note: MAXIMALLY-GENERAL here does **not** push the verdict toward YES — the binding issue is not generality but *what the objects are* (project-private scaffolding on both sides), surfaced by 4c.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Hypotheses are already a clean membership + parity; nothing to typeclass-ify. |
| 2 | sequences/metric → filters/topological? | no | — | Proof already uses the filter/`Tendsto` + Lipschitz/continuity idiom (and mathlib's `eq_addChar_of_value_at_one`). |
| 3 | construct an object where a universal-property class would characterise it? | **yes** | The RHS is *already* the universal object (the unique continuous char with value `x` at 1, i.e. mathlib's `continuousAddCharEquiv`). The mathlib-idiomatic statement of "the analytic power = the canonical char" should be phrased against the **honest** `padicExp`/`padicLog` (not the junk-total `pZpExp`/`pZpLog`), e.g. `(↑(onePAdicPow p x hx s) : ℚ_[p]) = padicExp p (s • padicLog p x)`. | Lets the equation be consumed without ever mentioning the `dite`-guarded scaffolding; composes with the honest `padicExp_add`/`norm_padicExp_*`/`padicExp_padicLog` API. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure here. |
| 5 | vector-space/metric/field-specific → weaken typeclass? | no | — | Forced to `ℤ_p` (row 1 of 4a). |
| 6 | 1-categorical → higher-categorical? | no | — | A pointwise equality of `ℤ_p`-valued functions. |
| 7 | concrete index ℕ/ℤ/ℝ → arbitrary monoid/group? | no | — | Exponent already ranges over all of `ℤ_p`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild)**.
- Proposed mathlib-idiomatic restatement: state the agreement against the *honest* `padicExp`/`padicLog` and the mathlib character `addChar_of_value_at_one` directly, e.g.
  `((PadicInt.addChar_of_value_at_one (x-1) h) s : ℚ_[p]) = padicExp p (s • padicLog p x)`,
  eliminating the junk-total `pZpExp`/`pZpLog` and the project-private `onePAdicPow` wrapper.
- Cost: MODERATE (the honest-vs-junk-total bridge lemmas `pZpExp_coe`/`pZpLog_coe` already exist; re-routing the proof through them is mechanical).
- Mathlib downstream this enables: the statement would then be about *only* mathlib-canonical objects (mathlib's `addChar_of_value_at_one` + a hypothetical upstreamed `padicExp`/`padicLog`), so it could ship as the "exp/log realises the canonical character" companion lemma alongside an upstreamed p-adic exp/log file.
- Real mathematical improvement: yes — it removes two layers of Lean scaffolding (the junk-total totalisation and the `onePAdicPow` thin wrapper) and states the genuine mathematical fact directly.

**Crucial caveat.** The modern-idiom restatement is **blocked on prerequisites that are not yet in mathlib**: it presupposes an upstreamed p-adic `padicExp`/`padicLog` (mathlib has *none* — Phase 5). Until that exists, the modern-idiom form cannot be stated in mathlib at all. So 4c does not, by itself, make this a clean YES-but-generalise-first; it identifies the *eventual* mathlib form but the actual mathlib-readiness is gated on the whole p-adic exp/log development landing first. This pushes the decision into a sequencing/scope judgement — see Phase 7.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow` (Phase 5)

[A] Lean-Finder       n/a — tool not reachable in this environment; compensated with [D]+[E] full grep over the vendored mathlib tree + WebSearch row 11.
[B] Loogle            (pattern: a p-adic exp/log = AddChar equality) — n/a/no: no `padicExp`/`padicLog` symbol exists in mathlib to form such a pattern against (confirmed by [D]); a Loogle type-pattern is vacuous.
[C] LeanSearch        "p-adic power equals continuous character exp log" — no hits (interface returned no theorem matches; corroborated by [D]).
[D] Grep mathlib src  `padicExp|padicLog|onePAdicPow|smul_padicLog|exp.*log.*char` over `.lake/packages/mathlib/Mathlib/` — **no hits** for any p-adic analytic exp/log or this bridge. Only adjacent hits: `DirichletCharacter.LSeries_eulerProduct_exp_log` (complex L-series, unrelated) and the *character side* `Mathlib/NumberTheory/Padics/AddChar.lean` (`addChar_of_value_at_one`, `eq_addChar_of_value_at_one`, `continuousAddCharEquiv`).
[E] Name pattern      grep for `eq_addChar_of_value_at_one` and exp↔char bridges across mathlib + project — mathlib has the *uniqueness lemma* this proof consumes, but **no** exp/log instance of it. Within the project, this theorem is the **only** exp↔character bridge (the other three `eq_addChar_of_value_at_one` uses in `Branches.lean` prove multiplicativity and the `p−1`-torsion lemma — different statements).

Searched for both:
  - the user's current form (`pZpExp (s·pZpLog x) = onePAdicPow … s`) — not in mathlib.
  - the literature-standard/honest form (`exp(s·log x) = canonical character`) — not in mathlib, because mathlib has **no p-adic exp/log at all**.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard/modern-idiom form). Mathlib has exactly the **right half** of the equation — David Loeffler's `PadicInt.addChar_of_value_at_one` / `eq_addChar_of_value_at_one` / `continuousAddCharEquiv` (`Mathlib/NumberTheory/Padics/AddChar.lean`, 2025), which `onePAdicPow` wraps — but the **left half** (the analytic p-adic exp/log) is entirely absent, so the bridge cannot exist upstream today.

---

### Call sites — `PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow` (Phase 6.0)

Internal use count: **3** (in `ResidueZeta.lean`, all external to the declaring file `PadicExp.lean`).
External-to-file callers: 1 distinct file (`ResidueZeta.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| ResidueZeta.lean:110 | `rw [← padicExp_smul_padicLog_eq_onePAdicPow p hp2 hy t, …]` — rewrite `‖onePAdicPow … t − 1‖` into the analytic `‖pZpExp(t·ℓ) − 1‖` to apply `norm_padicExp_sub_one` (proves `‖y^t−1‖ = ‖t‖·‖y−1‖`). |
| ResidueZeta.lean:254 | `rw […, ← padicExp_smul_padicLog_eq_onePAdicPow p hp2 (angleUnit_sub_one_mem …) (1−s), pZpExp_coe …]` — convert the branch-character `onePAdicPow` form into the analytic form inside a squeezing/continuity argument. |
| ResidueZeta.lean:1724 | `have hbridge := padicExp_smul_padicLog_eq_onePAdicPow p hp2 (angleUnit_sub_one_mem …) 1; rw [onePAdicPow_apply_one, hL, mul_zero] at hbridge` — uses `⟨u⟩ = exp(1·log⟨u⟩) = exp 0 = 1` to derive `log⟨u⟩ ≠ 0`. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this theorem?): **none** — there is no second exp↔character bridge in the project; this is the sole junction.

What the pattern tells you: **K = 3 internal uses, no inline re-derivation** → real internal API; consumers genuinely depend on it. *However*, every use is `rw [← …]`/`have … rw …` — the theorem is used purely as **connective tissue to swap between the project's own two constructions** (analytic `pZpExp` ↔ character `onePAdicPow`), never to export a standalone fact. The downstream value is internal plumbing, not a public-facing result.

### Composition check (Phase 6)

Can `padicExp_smul_padicLog_eq_onePAdicPow` be derived from mathlib in ≤3 chained calls? **No.** The proof:
1. builds a bespoke `AddChar ℤ_[p] ℤ_[p]`, `κ : t ↦ pZpExp p (t·ℓ)`, proving `map_zero_eq_one'` and `map_add_eq_mul'` (the latter via `padicExp_add` on the analytic side, through `pZpExp_coe`);
2. proves `κ` continuous via `LipschitzWith 1` (using `norm_padicExp_sub_padicExp` and the integrality bound `‖ℓ‖ ≤ 1`);
3. proves `κ 1 = x` via `padicExp_padicLog` (the analytic inversion `exp(log x) = x`);
4. invokes mathlib's uniqueness `PadicInt.eq_addChar_of_value_at_one` to conclude `κ = onePAdicPow …`, then `DFunLike.congr_fun` at `s`.

Attempt 1 (compose from mathlib alone): impossible — steps 1–3 all consume **project-only** analytic facts (`pZpExp_coe`, `padicExp_add`, `norm_padicExp_sub_padicExp`, `padicExp_padicLog`) that have no mathlib counterpart (Phase 5). Mathlib supplies only step 4's uniqueness lemma.
Result: fails.

Conclusion: **NOT-COMPOSABLE** (from mathlib). It is a genuine ~50-line proof whose load-bearing ingredients are the project's absent-from-mathlib p-adic exp/log API.

---

## Verdict: `PadicLFunctions.padicExp_smul_padicLog_eq_onePAdicPow`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): each *ingredient* is standard (the power `x^s := exp(s·log x)`; characters of `ℤ_p` by value at 1 / Mahler series), but **the agreement of the two constructions is not a named literature theorem** — the literature builds the power only via exp/log; the Mahler-character route and the agreement are formalisation-driven, the agreement being the folklore "uniqueness of continuous characters" consequence (Iwasawa-algebra two-pictures pattern, row 9).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** as a statement about these objects (0 weakenings; `p≠2`, `x∈1+pℤ_p`, base `ℤ_p` all sharp). Phase 4c found a *mild* modern-idiom form (state against honest `padicExp`/`padicLog` + mathlib's `addChar_of_value_at_one`, dropping the junk-total `pZpExp`/`pZpLog` and the `onePAdicPow` wrapper), but it is **blocked on an upstreamed p-adic exp/log that mathlib does not have**.
- Mathlib search (Phase 5): **not in mathlib**. Mathlib has the **character half** (`PadicInt.addChar_of_value_at_one`, `eq_addChar_of_value_at_one`, `continuousAddCharEquiv` — Loeffler 2025) that `onePAdicPow` wraps, but **no p-adic analytic exp/log** at all, so the bridge cannot exist upstream today.
- Composition check (Phase 6): **NOT-COMPOSABLE** from mathlib (3 real internal consumers, no inline re-derivation, but every consumer uses it as `rw`-glue between the project's own two constructions; the proof depends on project-only exp/log API).

**Rationale (1–2 paragraphs):**

Two facts pull against each other and the resolution is a scope/sequencing call only the maintainer can make — exactly the `pZpExp` situation, of which this theorem is the *named* bridge. On one side, the mathematics is real and genuinely missing from mathlib: that the analytic p-adic power `exp(s·log x)` equals the canonical continuous character `x^s` is the natural capstone of a p-adic exp/log development, it is NOT composable from mathlib (Phase 6), and mathlib lacks the entire analytic half (Phase 5). So a flat NO-mathlib-has-it / NO-composable is wrong. On the other side, the *specific Lean declaration* is **project-internal connective tissue, stated against two layers of project-private scaffolding on each side**: the RHS `onePAdicPow` is a thin wrapper over mathlib's `addChar_of_value_at_one` (the sibling report `norm_onePAdicPow_sub_one` already flagged this and was ruled YES-but-generalise-first precisely to re-aim off the wrapper), and the LHS `pZpExp`/`pZpLog` are `dite`-guarded junk-total totalisations whose own report (`pZpExp`) was ruled BORDERLINE because a mathlib reviewer would demand a bundled/honest form. All three call sites use this theorem only as `rw [← …]` glue to convert between those two scaffolds — there is no standalone exported fact. A mathlib reviewer would therefore not take *this* statement; they would want the honest form `(↑(addChar_of_value_at_one (x−1) h) s : ℚ_[p]) = padicExp p (s • padicLog p x)` — which (Phase 4c) **cannot even be stated in mathlib until an honest p-adic `padicExp`/`padicLog` is upstreamed first**. So the verdict turns entirely on a maintainer decision about the p-adic exp/log upstreaming programme and what shape the bridge should take — not on anything the evidence can settle. Hence BORDERLINE.

**Refactor-actionable detail — numbered questions (≤5):**

1. Is the p-adic exp/log development (`padicExp`, `padicLog`, and their inversion `padicExp_padicLog` — already ruled YES-add-as-is) going to be upstreamed to mathlib as a new `Mathlib/NumberTheory/Padics/Exponential.lean`? **If no**, this bridge stays project-local (the honest mathlib form is unstateable) → effectively NO-for-mathlib, keep as internal glue. **If yes**, proceed to Q2.
2. Assuming exp/log is upstreamed: should the *companion bridge* shipped to mathlib be stated against the honest `padicExp`/`padicLog` + mathlib's `addChar_of_value_at_one` (the Phase-4c form), dropping both the junk-total `pZpExp`/`pZpLog` and the project wrapper `onePAdicPow`? (Recommended — that is the only mathlib-acceptable shape.)
3. The RHS wrapper `onePAdicPow` is the sticking point shared with `norm_onePAdicPow_sub_one` (YES-but-generalise-first, re-aim off the wrapper). Do you want a single coordinated PR that (a) upstreams exp/log, (b) ships `onePAdicPow`-free restatements of *both* this bridge and the norm lemma against mathlib's `addChar_of_value_at_one`? (If yes, this decl ships as part of that batch in restated form — i.e. it becomes a `YES-but-generalise-first` contingent on Q1.)
4. If exp/log is NOT upstreamed but you still want *something* here: is the junk-total `pZpExp`/`pZpLog` form acceptable as permanent project-internal API, or should it be refactored to the honest `padicExp`/`padicLog` form even project-locally (which would also simplify the three `ResidueZeta.lean` call sites)?

Next action: the maintainer answers Q1–Q4. Likely outcomes:
  - Q1 = no → **drop from mathlib consideration**; keep as project-internal glue (rename/document as such). The substantive mathlib contribution is the *exp/log API itself*, already captured by the `padicExp_padicLog` YES-add-as-is verdict.
  - Q1 = yes + Q2/Q3 = honest restatement → **flips to `YES-but-generalise-first`**: re-run `/generalise` to restate as the `onePAdicPow`-free, junk-total-free bridge against mathlib's `addChar_of_value_at_one` + the upstreamed `padicExp`/`padicLog`, and ship it in the exp/log PR batch.

---

## Next step

Maintainer answers Q1–Q4 above; re-run `/mathlibable` (or `/generalise` if Q1=yes and the honest restatement is wanted) to resolve. The verdict is gated on the p-adic exp/log upstreaming decision and the shape of the bridge — a scope/sequencing judgement the evidence cannot make. If exp/log is not going upstream, this is effectively a NO (project-internal glue between two scaffolds); if it is, this becomes a YES-but-generalise-first stated against mathlib's `addChar_of_value_at_one` and the honest `padicExp`/`padicLog`, shipped in the same batch.
