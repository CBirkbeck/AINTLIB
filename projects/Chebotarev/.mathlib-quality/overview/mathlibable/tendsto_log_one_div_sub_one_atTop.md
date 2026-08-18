# /mathlibable report — `tendsto_log_one_div_sub_one_atTop`

## Baseline (Phase 0)
- lake build:               ~ stale (per task note); reasoned from source statement
- decl `tendsto_log_one_div_sub_one_atTop`: resolved at
  `projects/Chebotarev/CebotarevDensity/ForMathlib/LogOneDivSubOne.lean:44`
- kind:                      theorem
- has sorry:                 no
- namespace:                 root (no enclosing `namespace`; author earmarked for upstreaming)
- module docstring summary:  "Limit lemmas for `log (1 / (s - 1))` near `s = 1`" — purely
  analytic divergence facts driving Dirichlet-density asymptotics; lives in `ForMathlib/`.

## Statement (Phase 1)

`tendsto_log_one_div_sub_one_atTop` is a **theorem** stating:

> The function `s ↦ log(1/(s − 1))` diverges to `+∞` as `s → 1⁺` (i.e. along the
> right neighbourhood filter `𝓝[>] 1`).

This is the elementary fact behind the Dirichlet-density normalisation: as `s ↓ 1`,
`s − 1 ↓ 0⁺`, so `1/(s−1) ↑ +∞`, and `log` of that `↑ +∞`.

Variables / typeclasses (Lean side):
- none — fully concrete on `ℝ`.

Hypotheses (Lean side):
- none.

Conclusion (math): `log(1/(s−1)) → +∞` as `s ↓ 1`.
Conclusion (Lean): `Tendsto (fun s : ℝ ↦ Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop`.

Proof (from source, 4 substantive lines):
```lean
refine Real.tendsto_log_atTop.comp ?_
have h1 : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((continuous_sub_right 1).tendsto' 1 0 (by ring)).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun s hs ↦ by simp only [Set.mem_Ioi] at hs ⊢; linarith)
simpa only [one_div] using! h1.inv_tendsto_nhdsGT_zero
```

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a concrete one-point analytic limit helper (a corollary-grade composition of
`log → atTop` with a translation+inverse), not a named theorem, not a new structure,
not a `## Main results` headline of the parent project. (Literature width run EXHAUSTIVE
regardless.)

## One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. No defeq/diamond surface.

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | log(1/(s−1)) → ∞ as s↓1, Dirichlet density asymptotics                | yes  | appears only as the *denominator* `−log(1/(s−1))` in the Dirichlet-density definition | Encyclopedia of Math; Wikipedia "Dirichlet density"; Harvard/Elkies notes |
|  2 | WebSearch (general/role form)    | `log L(s) = log 1/(s−1) + O(1)`, principal character, Serre formulation | yes  | the *companion* statement `log L(s,χ₀) = log(1/(s−1)) + O(1)` is standard; the bare divergence is taken as obvious | MIT 18.785 LectureNotes17/18; Várilly "Dirichlet's Theorem"; arXiv 2401.17610 |
|  3 | WebSearch (named-after / aliases)| "Logarithm tends to infinity" elementary theorem, ln(∞)               | yes  | `log x → +∞ as x → +∞` (ProofWiki "Logarithm Tends to Infinity") | the divergence is the *log-at-infinity* fact; the `1/(s−1)` packaging is a trivial reparametrisation |
|  4 | ChatGPT MCP                      | (MCP down per env note — substituted with channels 1–3 + nLab below)  | n/a  | —                   | fallback used as instructed; three WebSearch generality levels + ProofWiki/Encyclopedia cover the standard-form question |
|  5 | Local references                 | `projects/Chebotarev/.mathlib-quality/references/`, `refs/`           | n/a  | (no references dir; `refs/` absent in this checkout) | recorded n/a |
|  6 | nLab                             | logarithm divergence / limit composition to +∞                       | no   | nLab has no entry for this elementary real-analysis fact | not a categorical concept; nLab returns only `(∞,1)-limit` noise |
|  7 | nCatLab (categorical)            | —                                                                     | n/a  | not a categorical concept | a concrete `ℝ → ℝ` limit; nothing to categorify |
|  8 | Stacks Project (alg geom)        | —                                                                     | n/a  | not an algebraic-geometry concept | concrete real analysis |
|  9 | MathOverflow / Math.SE           | log(1/(s−1)) behaviour near s=1 (covered via #1/#2 hits)              | yes  | treated as "obvious"; cited only as the density normaliser | no source states it as a standalone lemma |
| 10 | recent arXiv (last 5 yrs)        | "logarithm of L-functions at and near s=1" asymptotics               | yes  | arXiv 2401.17610 uses `log(1/(s−1))` as the leading term, not a lemma | confirms it's a building block, never a headline result |

### Literature summary (Phase 3)

Concept identified as: the **logarithm-at-infinity divergence** (`log x → +∞`), reparametrised
through `x = 1/(s−1)` so it reads off as `s ↓ 1`. In number theory it surfaces *only* as the
normalising denominator in the **Dirichlet density** definition and as the leading term of
`log L(s, χ₀)` near `s = 1`.

Sources agree on the standard form: **yes** — every source treats `log(1/(s−1)) → +∞` as an
immediate consequence of `log → +∞` at infinity; none state it as a named standalone lemma.
Most general standard form: `Real.log x → +∞` as `x → +∞` (which mathlib already has as
`Real.tendsto_log_atTop`). The `1/(s−1)`, `s ↓ 1` dressing is a project-specific convenience.
Generality dimensions where the literature varies:
  - base point: literature uses `s = 1` (the L-function pole); nothing forces `1` — any `c`
    would do, but `1` is the only point of interest.
  - shape: literature writes `log(1/(s−1))` *and* the equivalent `−log(s−1)` interchangeably.
Disagreement with the literature: none — but the literature regards this as a one-line
corollary, not a result in its own right.

## Generality analysis — `tendsto_log_one_div_sub_one_atTop`

Literature-standard form (Phase 3): `Real.log x → +∞` as `x → +∞` (already in mathlib);
the `1/(s−1)` / `s ↓ 1` form is a specialisation/reparametrisation.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker/more-general form exists? | Reason |
|---|------------------------|-------------------|--------------------------|----------------------------------|--------|
| 1 | base point `1`         | hard-coded `s − 1`, `𝓝[>] 1` | arbitrary `c` (`s − c`, `𝓝[>] c`) | yes | nothing in the proof uses `1` specifically; `continuous_sub_right c` + `linarith` generalise verbatim. But only `c = 1` is ever used. |
| 2 | argument shape `1/(s−1)` | `1 / (s − 1)` | `(s−1)⁻¹`, or `−log(s−1)` | yes (cosmetic) | `one_div` already bridges `1/(s−1)` and `(s−1)⁻¹`; `Real.log_inv` bridges to `−log(s−1)`. Pure notation. |
| 3 | scalar field `ℝ`       | `ℝ`               | `ℝ` (log is real-specific) | NO | `Real.log` and `Real.tendsto_log_atTop` are `ℝ`-only; no generalisation target. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (a one-point specialisation of
`tendsto_log_atTop`), but the narrowing is *deliberate and benign*: `c = 1` is the only base
point of mathematical interest (the L-function pole), and the `1/(s−1)` shape is exactly what
Dirichlet-density callers produce.
Number of *meaningful* weakening opportunities: effectively 0 for mathlib purposes — generalising
the base point to arbitrary `c` produces `tendsto_log_one_div_sub_const_atTop`, which no one
needs and which is itself a 3-line corollary of `tendsto_log_atTop`. The shape variations
(rows 2) are cosmetic.
Proposed restatement: none warranted (a `c`-generalised version would be *more* general but
*less* useful, and still not a mathlib-grade standalone lemma — see Phase 6).
Cost of (hypothetical base-point) restatement: CHEAP.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Downstream |
|---|----------|----------|------------------------|------------|
| 1 | "let X be a foo" → typeclass? | no | no hypotheses to classify | — |
| 2 | sequences/metric → filters/topological? | no | already filter-stated (`𝓝[>] 1`, `atTop`) — maximally idiomatic | — |
| 3 | construct → universal-property class? | no | it's a limit fact, not a construction | — |
| 4 | set+closure-pred → bundled substructure? | no | n/a | — |
| 5 | vector-space/metric/field → weaker typeclass? | no | `Real.log` is `ℝ`-specific | — |
| 6 | 1-categorical → higher-categorical? | no | concrete real limit | — |
| 7 | concrete index → arbitrary group/monoid? | partial | base point `1` → arbitrary `c` (`tendsto_log_one_div_sub_const_atTop`) | would unify the at-a-point family, but no consumer needs `c ≠ 1` | 

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (the statement is already filter-idiomatic; the only
"generalisation" is the base-point `c`, row 7, which is a usefulness *down*grade and still
not mathlib-grade — it would be one more thin corollary of `tendsto_log_atTop`).
One-line reason: the result is already stated in the contemporary filter idiom; there is no
organisational redundancy to eliminate and no blocked downstream API.

## Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths
introduced).

## Mathlib search-status: `tendsto_log_one_div_sub_one_atTop`

[A] Lean-Finder       "log of 1/(s-1) tends to infinity at 1"      no hits (index returns `tendsto_log_atTop` and the near-zero log lemmas only)
[B] Loogle            `Tendsto (fun _ => Real.log _) (𝓝[>] _) atTop` (reasoned)  no exact hit; building blocks below
[C] LeanSearch        "logarithm of reciprocal tends to infinity from the right"  no exact-form hit
[D] Grep mathlib src  `Real.log (1 /`, `log_one_div`, `one_div_sub_one`, `log.*atTop.*nhdsWithin`  no hit — the exact `log(1/(s−1))` form is absent from mathlib
[E] Name pattern      `tendsto_log_one_div`, `tendsto_log_.*sub_one`             no decl by that name in mathlib

Searched for BOTH the user's form (`log(1/(s−1))`, `s↓1`) and the literature-standard
form (`log x → +∞`). The general form **is** in mathlib; the specialised form is not.

Building blocks found in mathlib (all verified by grep against the pinned mathlib):
- `Real.tendsto_log_atTop : Tendsto log atTop atTop`
  — `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:340`
- `Real.tendsto_log_nhdsGT_zero : Tendsto log (𝓝[>] 0) atBot`
  — `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:343` (the `−log(s−1)` route)
- `Filter.Tendsto.inv_tendsto_nhdsGT_zero : Tendsto f l (𝓝[>] 0) → Tendsto f⁻¹ l atTop`
  — `Mathlib/Topology/Algebra/Order/Field.lean:80`
- `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`
  — `Mathlib/Topology/NhdsWithin.lean:454`
- `continuous_sub_right`, `one_div`, `Real.log_inv` (`log x⁻¹ = −log x`,
  `…/Log/Basic.lean:142`).

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard
form), but mathlib has every building block, and the divergent step that does the real
work (`log → +∞`) is `Real.tendsto_log_atTop` verbatim.

## Call sites — `tendsto_log_one_div_sub_one_atTop`

Internal use count: **7** (within the Chebotarev project, NOT counting the declaring file).
External-to-file callers: **6 distinct files**.

| Caller file:line                                              | Usage pattern (one-line excerpt)                           |
|--------------------------------------------------------------|------------------------------------------------------------|
| CebotarevDensity/Density.lean:537                            | `have hL := tendsto_log_one_div_sub_one_atTop`            |
| CebotarevDensity/CyclotomicNormResidue.lean:383             | `have hL := tendsto_log_one_div_sub_one_atTop`            |
| CebotarevDensity/CyclotomicNormResidue.lean:539             | `tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0` |
| CebotarevDensity/Cyclotomic.lean:713                        | `have hL := tendsto_log_one_div_sub_one_atTop`            |
| CebotarevDensity/Cyclotomic.lean:918                        | `have hL := tendsto_log_one_div_sub_one_atTop`            |
| CebotarevDensity/FixedFieldDensity.lean:208                 | `filter_upwards [tendsto_log_one_div_sub_one_atTop.eventually_gt_atTop 0] …` |
| CebotarevDensity/ZetaProduct.lean:2369                      | `tendsto_log_one_div_sub_one_atTop.atTop_add tendsto_const_nhds` |

Inline-derivation grep (was the same fact re-derived elsewhere without using this lemma?):
  - (none found) — every consumer goes through the named lemma; no site re-derives
    `log(1/(s−1)) → +∞` inline.

Signal (per the call-sites table): **K = 7 ≥ 3 internal uses, no inline re-derivation, in 6
files → real API; consumers depend on it → leans YES-*.** Also note it is itself the
denominator used by the sibling lemmas `tendsto_ratio_one_of_log_pm_bounded` (same file),
so it anchors a small local API.

## Composition check (Phase 6)

Can `tendsto_log_one_div_sub_one_atTop` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the file's own route): `Real.tendsto_log_atTop.comp h1.inv_tendsto_nhdsGT_zero`
  - Mathlib decls used: `tendsto_log_atTop`, `Tendsto.inv_tendsto_nhdsGT_zero`, plus `h1`.
  - Result: **partial** — the two outer calls are mathlib, but the inner `h1 : Tendsto (s−1)
    (𝓝[>] 1) (𝓝[>] 0)` is **not** a single mathlib lemma. There is no
    `tendsto_sub_const_nhdsGT`; establishing `h1` requires
    `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` fed a continuity fact
    (`continuous_sub_right`) AND a separate `eventually`-membership proof (`s > 1 ⇒ s−1 > 0`,
    discharged by `linarith`). That is ~4 lines and 3–4 distinct mathlib lemmas on its own.

Attempt 2 (the `−log` route): rewrite `log(1/(s−1)) = −log(s−1)` via `one_div`+`Real.log_inv`,
then `(Real.tendsto_log_nhdsGT_zero.comp h1)` gives `log(s−1) → atBot`, then
`tendsto_neg_atBot_iff` (or `.neg`) flips to `atTop`.
  - Mathlib decls used: `log_inv`, `tendsto_log_nhdsGT_zero`, the neg-flip, plus `h1`.
  - Result: **partial** — *shorter than Attempt 1* on the log side, but it **still** needs the
    same `h1 : (s−1) → 𝓝[>] 0` sub-proof, which is the irreducible non-mathlib step.

Conclusion: **NOT-COMPOSABLE in ≤3 mathlib calls.** Both routes bottleneck on the same
multi-step `(s−1) → 𝓝[>] 0` translation-into-a-right-neighbourhood lemma, which mathlib does
not package. The whole proof is ~8 lines; it is *not* a 1–3-call inline. (If mathlib later
adds a `tendsto_sub_const_nhdsGT`/affine-pushforward-of-`𝓝[>]` lemma, this would collapse to
≤3 calls and flip to NO-composable — see Phase 7 question.)

## Verdict: `tendsto_log_one_div_sub_one_atTop`

**Category:** BORDERLINE-needs-human

**Evidence:**
- Literature search (Phase 3): the divergence is universally treated as an *immediate
  corollary* of `log → +∞` (ProofWiki, Encyclopedia of Math, MIT 18.785, Serre-style notes);
  it appears in NT only as the Dirichlet-density denominator, never as a named standalone lemma.
- Generality analysis (Phase 4): STRICTLY NARROWER than the standard `tendsto_log_atTop`, but
  deliberately so (`c = 1` is the only useful base point; the `1/(s−1)` shape is what callers
  produce). No worthwhile generalisation; the base-point generalisation is a usefulness
  *down*grade. Already filter-idiomatic (4c: no modernisation move).
- Mathlib search (Phase 5): not in mathlib; the general form `tendsto_log_atTop` is, plus all
  building blocks (`inv_tendsto_nhdsGT_zero`, `tendsto_log_nhdsGT_zero`, `log_inv`).
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 mathlib calls — both derivation routes
  bottleneck on the multi-step `(s−1) → 𝓝[>] 0` step, which mathlib does not package.
- Call sites (Phase 6.0): K = 7 internal uses across 6 files, no inline re-derivation → real,
  depended-upon API (a YES-* signal).

**Rationale (why BORDERLINE rather than a clean YES or NO):**

Two well-supported signals point in *opposite* directions, and resolving the tension is a
mathlib-taste / scope call the skill should not make unilaterally:

1. *Toward NO-composable / "don't upstream as-is":* mathematically this is a textbook one-line
   corollary of `Real.tendsto_log_atTop`. Mathlib generally resists shipping single-base-point
   specialisations of a more general limit it already owns (`c = 1`, the `1/(s−1)` dressing) —
   the preference is to keep the general lemma and let callers reparametrise. The literature
   agrees: no source dignifies this with a name.

2. *Toward YES-add-as-is:* the "one-line corollary" framing is *misleading in Lean*. The only
   genuinely-mathlib step is `log → +∞`; the work is the `(s−1) → 𝓝[>] 0` push into a right
   neighbourhood, which mathlib does **not** provide as a lemma, so the result is NOT a ≤3-call
   inline (Phase 6). Combined with K = 7 real consumers and zero inline re-derivations, it is a
   legitimately reusable analytic helper, not a wrapper. If anything goes to mathlib, the more
   natural unit might be the *missing primitive* (a `tendsto_sub_const_nhdsGT` /
   "affine map pushes `𝓝[>] c` to `𝓝[>] 0`" lemma), from which this becomes a true 2–3-call
   corollary — at which point this specific statement is better *inlined* than *named*.

Because the verdict hinges on (a) whether mathlib wants the one-point `s = 1` specialisation at
all, and (b) whether the right contribution is *this lemma* or the *underlying missing
`𝓝[>]`-pushforward primitive*, this is a human/maintainer judgment.

**Numbered questions for the user (≤5):**

1. Does mathlib want a single-base-point (`s = 1`) specialisation like this at all, or does its
   "keep the general lemma, reparametrise at call sites" policy say no? (If "no" → NO-composable,
   inline the ~8-line proof at the 7 sites or keep it project-local.)
2. Would you rather upstream the **missing primitive** instead — a lemma that an affine map
   `x ↦ x − c` (or `continuous_sub_right c`) pushes `𝓝[>] c` to `𝓝[>] 0` (no such lemma exists
   in mathlib today) — and then derive this in ≤3 calls? That primitive *is* clearly
   mathlib-grade and reusable far beyond this project.
3. If shipping this lemma as-is, do you want it **generalised to an arbitrary base point `c`**
   (`tendsto_log_one_div_sub_const_atTop`), even though only `c = 1` is used here? (CHEAP to do;
   debatable whether mathlib benefits.)
4. Should the file's sibling `tendsto_ratio_one_of_div_atTop_pm_bounded` (the generic divergent-
   denominator squeeze, which is base-point-free and looks more independently mathlib-worthy) be
   bundled into the same upstreaming decision / PR?

**Next action:** user answers Q1–Q2 (the load-bearing ones). If Q1 = "mathlib won't take the
`s=1` specialisation", the verdict resolves to **NO-composable-from-mathlib** and the refactor is:
at each of the 7 call sites, either inline the 8-line proof or — preferably — first add the
`𝓝[>] c → 𝓝[>] 0` pushforward primitive (Q2) and reduce each call to
`Real.tendsto_log_atTop.comp ((tendsto_sub_const_nhdsGT …).inv_tendsto_nhdsGT_zero)`. If Q1/Q2 =
"ship this lemma", the verdict resolves to **YES-add-as-is**, proposed location
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (next to `tendsto_log_nhdsGT_zero`), PR title
`feat(Analysis): add tendsto_log_one_div_sub_one_atTop`, after running `/generalise` (Q3) and
`/cleanup`.
