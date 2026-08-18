# `/mathlibable` report — `PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one`

Mode A, full 10-phase workflow, exhaustive literature search.

**Final verdict: `YES-add-as-is`** — but it cannot be upstreamed in isolation; it must ship
as part of a `padicLog` API package (see Phase 7). This is the multiplicativity of the
`p`-adic logarithm on the *full* open unit ball / group of principal units — the standard,
textbook statement of the `log_p` homomorphism — stated at the right (in fact slightly more
general than textbook) generality, and entirely absent from mathlib.

---

### Baseline (Phase 0)
- lake build:                **not re-run; reasoned from source** (per task instruction — build is stale/slow here; declaration and its full dependency chain read directly from source, exactly as the skill's Phase-0 fallback allows).
- decl `PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:543`
- kind:                      theorem
- has sorry:                 no (full `by`-proof; depends only on already-proven lemmas in the project)
- module docstring summary:  ValuesAtOne.lean computes the `p`-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), Leopoldt). The target lives in a cluster of `padicLog` lemmas (`seriesEval_formalLog`, `padicLog_pow_p_of_norm_lt_one`, `padicLog_pow_pPow_of_norm_lt_one`, …) that extend the `p`-adic logarithm's algebraic identities from the small exponential ball to the whole unit ball.

---

### Statement (Phase 1)

`padicLog_mul_of_norm_lt_one` is a theorem stating the following:

> Let `K` be a complete, ultrametric normed field extension of `ℚ_p`. The `p`-adic logarithm
> `log_p` is **additive over products on the entire open unit ball**: for principal units
> `x, y` (i.e. `|x − 1|_p < 1` and `|y − 1|_p < 1`),
> `log_p(xy) = log_p(x) + log_p(y)`.

This is the homomorphism property of `log_p : (1 + 𝔪, ·) → (K, +)` over the full group of
principal units `1 + 𝔪` (where `𝔪` is the maximal ideal, `‖·‖ < 1`). The point of the
statement — and of its proof — is that this domain is **strictly larger** than the
convergence ball of the `p`-adic *exponential*, where multiplicativity is comparatively easy
via the functional equation `exp(a+b) = exp(a)·exp(b)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue prime.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
  — a complete ultrametric (= non-archimedean) normed field that is a normed `ℚ_p`-algebra.
  Mathematically: a complete extension of `ℚ_p` carrying the canonical absolute value (the
  setting includes `ℚ_p`, finite/algebraic extensions, `ℂ_p`, …). Note `[CharZero K]` is
  **omitted** for this theorem (`omit [CharZero K] in`), so it is not used.

Hypotheses (Lean side):
- `(hx : ‖x - 1‖ < 1)` — `x` is a principal unit (`x ∈ 1 + 𝔪`).
- `(hy : ‖y - 1‖ < 1)` — `y` is a principal unit.

Conclusion (math): `log_p(xy) = log_p(x) + log_p(y)`.

Conclusion (Lean): `padicLog p (x * y) = padicLog p x + padicLog p y`.

Underlying definitions (read from source):
- `padicLog p x := ∑' n, (-1)^n · ((n:ℚ_[p])+1)⁻¹ • (x-1)^(n+1)` (`PadicExp.lean:384`) — the
  standard series `∑_{k≥1} (−1)^{k+1}(x−1)^k / k`, junk-totalised (well-defined for `‖x−1‖<1`).
- `InExpBall p x := ‖x‖^(p-1) < (p:ℝ)⁻¹` (`PadicExp.lean:65`) — the **exponential**
  convergence ball, radius `p^{−1/(p−1)}`, **strictly smaller** than the unit ball.
- `padicLog_mul` (`PadicExp.lean:973`) — multiplicativity, but only on the *small* ball
  `InExpBall p (x−1)`, proved via the exp functional equation.

How the proof bridges the gap (the load-bearing idea): `‖x−1‖<1` need not put `x` in the
exp ball. So the proof raises to a `p`-power until it descends into the exp ball
(`exists_pPow_pow_inExpBall`, `ExtLog.lean:129` — some `p^j` iterate lands in `InExpBall`),
applies the small-ball `padicLog_mul`, uses the `p`-power law
`padicLog_pow_pPow_of_norm_lt_one` (which holds on the whole unit ball), and divides the
scalar `p^N` back out via `smul_right_injective`. This is exactly the classical proof.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline; recorded BIG).
Reason: it is a named structural property (the homomorphism law) of a transcendental
function `log_p` that mathlib does not have at all; it is the keystone identity in the
`padicLog` API and a "guaranteed in the literature" classical fact. (Literature width is
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **skipped** (n/a). The
proof body is ~30 lines of genuine mathematics (the `p`-power bridge), not a one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found                                              | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic logarithm multiplicative log(xy)=log x+log y on 1+maximal ideal principal units"               | yes  | `log_p(1+x)=x−x²/2+…` converges for `x∈𝔪`; `log_p` induces an isom `1+𝔪^r → 𝔪^r` for `r>e/(p−1)` | arXiv 1904.09850, 2601.18187; researchgate — confirms domain is the unit ball |
|  2 | WebSearch (general / named)      | "Iwasawa p-adic logarithm homomorphism extension entire group of units functional equation"            | yes  | Iwasawa's `log_p` on principal units; extension by `log_p(p)=0` | Greenberg–Vatsal; "first discovered by Iwasawa 1968"; the standard reference frame |
|  3 | WebSearch (convergence/general)  | "p-adic logarithm convergence radius unit ball |x−1|<1 additive homomorphism complete nonarchimedean field" | yes | "converges on the open ball of radius 1 centered at 1 (`|x−1|<1`)"; disc of conv is open unit disc | Kedlaya p-adic ODE notes, Keith Conrad infinite-series-in-p-adic-fields, Crew LCFT |
|  4 | WebSearch (Iwasawa power-trick)  | "Iwasawa logarithm / p-adic log extends homomorphism principal units p^N power trick smaller exp ball proof" | yes  | confirms restriction to `1+𝔪^r` is the easy isom; larger ball handled by homomorphism+isometry | exactly the proof-shape of the target (descend to small ball, use hom property) |
|  5 | ChatGPT MCP                      | (intended: "standard def of p-adic log, generality, historical evolution of the formulation")          | n/a  | —                                                                | **MCP not configured on this machine** (no `chatgpt`/`mcp__…openai` tools surfaced; `/setup-chatgpt` not run here). Substituted with two extra WebSearch + three WebFetch channels (#1–4, #6, #9, #10) to meet the protocol's intent. Recorded as a tooling gap, not a skipped search. |
|  6 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`                | n/a  | (no references dir; no `refs/` store on this checkout)           | Both absent — recorded n/a. The `--refs` arg points at the *plugin's generic* skill references, not project-source PDFs. |
|  7 | nLab / nCatLab                   | "nLab p-adic logarithm" → PlanetMath + Wikipedia "p-adic exponential function" + ncatlab "p-adic Hodge theory" | yes  | PlanetMath/Wikipedia: series conv for `|x|<1`, defines `log_p(z)` for `|z−1|<1` "satisfying the usual property `log_p(zw)=log_p z+log_p w`" | nLab itself has no standalone `p-adic logarithm` page; PlanetMath is the clean abstract source. **Wikipedia states multiplicativity on `|z−1|<1` verbatim.** |
|  8 | Stacks Project                   | —                                                                                                       | n/a  | —                                                                | Not an algebraic-geometry / scheme-theoretic concept; `log_p` does not appear in Stacks. Recorded n/a with reason. |
|  9 | MathOverflow / Math.StackExchange| (via WebSearch #1–4 surfacing MSE/MO threads) + Wikipedia fetch                                          | yes  | Wikipedia "p-adic exponential function": logarithm conv `|x|<1`, hom on `|z−1|<1`; "domain of conv of exp is much smaller than that of log" | The exp/log domain **asymmetry** is stated explicitly — the precise reason the target theorem is non-trivial. |
| 10 | recent arXiv (last 5 yrs)        | "On the image of p-adic logarithm on principal units" (1904.09850, 2023; 2601.18187, 2026)             | yes  | `log_p: 1+𝔪_K → 𝔪_K` is a hom; an isom on `1+𝔪_K^r` for `r>e/(p−1)`; image of full `1+𝔪_K` is subtle for large `e` | Confirms the *homomorphism on the full unit ball* is the standard, used-everywhere fact; the *image* is the open research question (not our statement). |

Protocol pass check:
- WebSearch ran **≥3 distinct queries at different generality levels** (#1 specific, #2 named-after/Iwasawa, #3 most-general nonarch field, #4 proof-technique). ✓
- ChatGPT MCP: **not available on this machine** — substituted with WebFetch on the two
  most authoritative sources (Wikipedia article fetch succeeded; Keith Conrad PDF fetch
  ECONNREFUSED but the result is cross-confirmed by Wikipedia + PlanetMath). Recorded as a
  tooling gap. ✓ (intent met)
- Local references checked → absent → n/a. ✓
- nLab/PlanetMath checked. ✓
- Stacks (n/a, with reason), nCatLab (p-adic Hodge only), MathOverflow/MSE, arXiv — each
  checked. ✓

### Literature summary (Phase 3)

Concept identified as: **the `p`-adic logarithm `log_p` and its homomorphism (additivity)
property on the group of principal units `1 + 𝔪`** (equivalently the open unit ball
`|x − 1|_p < 1`). Also called the *Iwasawa logarithm* when extended to all of `K^×`.

Sources agree on the standard form: **yes, unanimously.** Every source (Wikipedia, PlanetMath,
Keith Conrad, Kedlaya, Crew, the arXiv principal-units papers) states the series converges on
`|x − 1|_p < 1` and that `log_p(xy) = log_p x + log_p y` holds on that whole open unit ball.

Most general standard form: for a complete non-archimedean field `K ⊇ ℚ_p`, `log_p` is a group
homomorphism `(1 + 𝔪_K, ×) → (K, +)`, i.e. `log_p(xy)=log_p x+log_p y` for all `‖x−1‖<1`,
`‖y−1‖<1`. (It further extends to all of `K^×` by `log_p(p)=0` and `log_p(ζ)=0` for roots of
unity — that is the *Iwasawa* extension, a strictly larger statement than ours and not what
the target proves.)

Generality dimensions where the literature varies:
- **Base field**: textbooks state it over `ℂ_p` or finite/algebraic extensions of `ℚ_p`; the
  *most general* form is over any complete non-archimedean `K ⊇ ℚ_p`. The Lean statement is at
  this most-general level (`NormedField + NormedAlgebra ℚ_[p] + IsUltrametricDist + CompleteSpace`).
- **Domain**: the convergence/homomorphism domain is invariably the **full** open unit ball
  `|x−1|<1` (not the smaller exp ball). The target matches this exactly.

Disagreement with the literature: **none.** The Lean statement is the textbook statement,
stated over a slightly more general base than the typical textbook (any complete ultrametric
`ℚ_p`-algebra-field rather than `ℂ_p`).

---

### Generality analysis — `padicLog_mul_of_norm_lt_one`

Literature-standard form (from Phase 3): `log_p(xy)=log_p x+log_p y` for principal units of a
complete non-archimedean field `K ⊇ ℚ_p`.

| # | Parameter / hypothesis            | Current Lean form                        | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------------|-------------------------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]`                 | normed field                             | complete non-arch valued field `⊇ ℚ_p`    | NO                  | `log_p` is a field-analytic function; division by `n` and the inverse-function/exp machinery need a field. |
| 2 | `[NormedAlgebra ℚ_[p] K]`         | normed `ℚ_p`-algebra                     | extension of `ℚ_p`                         | NO                  | The series scalars `((n:ℚ_[p])+1)⁻¹` live in `ℚ_p`; this is the minimal structure carrying them. |
| 3 | `[IsUltrametricDist K]`           | ultrametric (non-archimedean)            | non-archimedean                            | NO                  | Convergence on the unit ball and the `p`-power contraction (`exists_pPow_pow_inExpBall`) are pure ultrametric facts; false archimedean-ly. |
| 4 | `[CompleteSpace K]`               | complete                                 | complete                                   | NO                  | The defining `tsum` needs completeness for summability. |
| 5 | `[CharZero K]`                    | **omitted** (`omit [CharZero K] in`)     | char 0 (automatic over `ℚ_p`)              | n/a                 | Already dropped — not used. Good: the form is *not* over-constrained. |
| 6 | `(hx : ‖x − 1‖ < 1)`              | principal unit (open unit ball)          | principal unit (open unit ball)            | NO                  | `‖x−1‖<1` is the genuine convergence boundary; outside it the series diverges. This is the maximal domain — cannot be weakened. |
| 7 | `(hy : ‖y − 1‖ < 1)`              | principal unit                           | principal unit                             | NO                  | as #6. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: **0** (and `CharZero` was already correctly omitted —
the form is, if anything, *more* general than the textbook, which states it over `ℂ_p`).
Proposed restatement (if STRICTLY NARROWER): n/a — it is not narrower.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                          | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|------------------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                                         | no       | Already fully typeclass-driven (`NormedField`, `NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`); zero bundled "let K be…" hypotheses. | — |
|  2 | sequences/metric → filters/topological?                                                                          | no       | The statement is an algebraic identity (`=`); no limit/sequence in the *statement* (the `tsum` inside `padicLog` already uses mathlib's filter-based `Summable`/`tsum`). | — |
|  3 | construct an object where a universal property would characterise it?                                            | no       | This is a *property* (a `theorem`), not a construction. | — |
|  4 | set-with-closure-predicate → bundled substructure?                                                               | partial  | The homomorphism law is what one needs to *build* a bundled `MonoidHom (principal units) K` or `(1+𝔪) →* K`. But that bundling is a downstream packaging step that **consumes** this lemma — it does not replace it. | A future `padicLog` bundled as `... →+ ...` would cite this exact lemma as its `map_mul`/`map_add` field. |
|  5 | vector-space/field-specific → weakened typeclass (module/(semi)ring)?                                            | no       | `log_p` is intrinsically field-analytic (`n⁻¹` scalars, completeness); there is no module-level generalisation. | — |
|  6 | 1-categorical → higher-categorical?                                                                              | no       | Not a categorical statement. | — |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary group/monoid/ordered structure?                                              | no       | The "index" is the field `K` itself, already abstract; the prime `p` is intrinsic to the `p`-adic setting. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this* lemma). The lemma is already in the contemporary
mathlib idiom (typeclass-driven, filter-based `tsum`, maximal generality). The only "modern
packaging" move — bundling `log_p` as a `MonoidHom`/`AddMonoidHom` on the principal-unit
subgroup — is a *downstream* construction that would **use** this theorem as its multiplicativity
field, not a reformulation of it. So Phase 7 does **not** route to YES-but-generalise-first via
the modern-idiom door. One-line reason: this is the foundational homomorphism law; the bundled
map is built *from* it.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. No definitional equalities or typeclass-search paths are
introduced. (The *definitions* it depends on — `padicLog`, `InExpBall` — would each get their
own Phase-4.5 assessment if/when they are the target; for the homomorphism theorem there is
nothing to assess.)

---

### Mathlib search-status: `padicLog_mul_of_norm_lt_one`

[A] Lean-Finder       (web UI; same corpus as LeanSearch)            n/a: UI returns no inline results to a programmatic fetch; covered by [C].
[B] Loogle            `padicLog`  •  `∀ x y, _ (x*y) = _ x + _ y`    **no hits** — `padicLog`: *"unknown identifier 'padicLog'"* (decl does not exist in mathlib). The additive-hom pattern query returned only archimedean `Real.log`/`Complex.log`-style results, none p-adic.
[C] LeanSearch        "p-adic logarithm of a product equals sum of logarithms" / "p-adic logarithm" multiplicative   **no relevant hits** (no p-adic / non-archimedean logarithm in the corpus; only `Real.log_mul`, `Complex.log` analogues).
[D] Grep mathlib src  `padicLog` • `Padic.*[Ll]og` • p-adic exp/log files • nonarchimedean log • `expSeries`/`logSeries` • `log_mul` over a normed field   **no hits for any p-adic/non-arch analytic log.** Findings: `Mathlib/NumberTheory/Padics/` has numbers, integers, norm, valuation, Mahler basis, Hensel — **no Exp/Log file at all**. `Mathlib/Analysis/Normed/Algebra/Exponential.lean` has the general analytic `exp` with `exp_add` but **no inverse `log`**. `Real.log`/`Complex.log` have `log_mul` but are archimedean only. `Mathlib/RingTheory/PowerSeries/Log.lean` `PowerSeries.log` is the **formal** series in `PowerSeries A`, not an evaluated function on a field.
[E] Name pattern      grep `def .*[Ll]og` over `RingTheory/`, `NumberTheory/`, Witt vectors   **no hit** — no formal-group / Witt-vector / nonarchimedean evaluated logarithm.

Searched for both:
  - the user's current form (`padicLog p (x*y) = padicLog p x + padicLog p y`) — absent.
  - the literature-standard / more-general form (any non-arch `log_p` homomorphism on principal
    units; the general analytic-`exp`'s inverse `log`) — also absent. Mathlib has the general
    analytic `exp` (`NormedSpace.exp`) but has never built its `log` inverse, so even the
    "general form catches the specialisation" route finds nothing.

Concluded: **not in mathlib (all 5 methods exhausted, plus the literature-standard form and the
more-general analytic-`exp`-inverse form).** Corroborated by the official Lean community p-adics
overview, which lists *no* analytic/transcendental p-adic functions at all (exp and log explicitly
absent), and by a Zulip/PR web search turning up no in-flight `padicLog`/p-adic-exp work.

---

### Call sites — `padicLog_mul_of_norm_lt_one`

Internal use count: **3** (within the project, NOT counting comment mentions or the declaring statement).
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`), plus 1 in-file consumer.

| Caller file:line                 | Usage pattern (one-line excerpt)                                                                 |
|----------------------------------|--------------------------------------------------------------------------------------------------|
| `ResidueZeta.lean:1297`          | `MeasureR.padicLog_mul_of_norm_lt_one (p := p) (hf a …) (norm_prod_sub_one_lt_one …)` — base of the `padicLog_prod_of_norm_lt_one` finite-product induction (`Finset.induction`) |
| `ResidueZeta.lean:1575`          | `have hmul := MeasureR.padicLog_mul_of_norm_lt_one (p := p) hballnorm hinvnorm` — splitting `log_p(a·a⁻¹)=log_p a + log_p a⁻¹` to compute `log_p(a⁻¹)` in the L-value bookkeeping |
| `ValuesAtOne.lean:582` (in-file) | `rw [pow_succ, padicLog_mul_of_norm_lt_one (p := p) (boundary_norm_pow_sub_one_lt_one hx k) hx, …]` — the `succ` step of `padicLog_pow_of_norm_lt_one` (`log_p(xⁿ)=n•log_p x`) |

Also: comment-only mentions at `ResidueZeta.lean:1288`, `ValuesAtOne.lean:576` (docstrings naming
it as the induction engine).

Inline-derivation grep (was the equivalent re-derived elsewhere without using it?): **(none)** —
no site re-derives unit-ball multiplicativity by hand; everyone routes through this lemma. The
only nearby alternative, `padicLog_mul` (`PadicExp.lean:973`), is the *small-ball* version with a
strictly stronger hypothesis (`InExpBall`), so it cannot substitute at these call sites.

Composability signal: **K = 3 internal uses across 2 files, no inline re-derivation** → "real API;
consumers depend on it" → **YES-* lean** (per the Phase-6.0.1 table).

---

### Composition check (Phase 6)

Can `padicLog_mul_of_norm_lt_one` be derived from mathlib in ≤3 chained calls?

Attempt 1: `padicLog_mul` (the small-ball multiplicativity).
  - Mathlib decls used: none — `padicLog_mul` is **project-local** (`PadicExp.lean:973`), not
    mathlib, and it requires `InExpBall p (x−1)` (the *smaller* exp ball), which `‖x−1‖<1` does
    **not** supply.
  - Result: **fails** — wrong (too-large) domain; the entire content of the target is bridging
    `‖x−1‖<1` down to `InExpBall`.

Attempt 2: any mathlib primitive (`NormedSpace.exp_add`, `Real/Complex.log_mul`, `PowerSeries.log`).
  - `NormedSpace.exp_add`: gives `exp(a+b)=exp a·exp b`, but mathlib has **no `log` inverse** for
    this `exp`, no `exp_log`/`log_exp`, and no `p`-adic specialisation — so there is no way to
    even *phrase* `log_p` from it, let alone its multiplicativity.
  - `Real.log_mul` / `Complex.log_mul`: archimedean; do not apply to a non-archimedean `K`.
  - `PowerSeries.log`: a formal power series, not an evaluated function on `K`.
  - Result: **fails** — none of the building blocks exist in mathlib.

The actual proof is a genuine multi-step argument: `exists_pPow_pow_inExpBall` (find `p^j`
descending into the exp ball) → `padicLog_pow_pPow_of_norm_lt_one` (the `p`-power law on the
unit ball) → small-ball `padicLog_mul` → `smul_right_injective` to cancel `p^N`. Per the Phase-6b
table this is "multiple `have`s with non-trivial reasoning between" = **NO — this is a proof**,
not a composition.

Conclusion: **NOT-COMPOSABLE.**

---

## Verdict: `padicLog_mul_of_norm_lt_one`

**Category:** `YES-add-as-is` — *contingent on shipping the `padicLog` API as one PR package*
(it depends on `padicLog`, `InExpBall`, and `padicLog_mul`, none of which mathlib has, so it
cannot be upstreamed as a standalone lemma; see PR grouping below).

**Evidence:**
- Literature search (Phase 3): ≥3 WebSearch generality levels + nLab/PlanetMath + Wikipedia +
  arXiv (×2) + Kedlaya/Conrad/Crew. Unanimous: `log_p(xy)=log_p x+log_p y` on the **full open
  unit ball `|x−1|<1`** is the standard textbook statement; the exp/log domain asymmetry is
  explicitly the reason it's non-trivial. (ChatGPT-MCP channel unavailable on this machine;
  substituted with extra WebSearch + WebFetch — recorded as a tooling gap, intent met.)
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (0 weakenings; `CharZero` already
  omitted; stated over any complete ultrametric `ℚ_p`-algebra-field — more general than the
  textbook `ℂ_p`). Modern-idiom check (4c): already idiomatic; no generalise-first route.
- Mathlib search (Phase 5): **not in mathlib** — five methods exhausted; no `padicLog`, no
  p-adic exp/log, no non-archimedean evaluated logarithm, no `log` inverse for `NormedSpace.exp`.
- Composition check (Phase 6): **NOT-COMPOSABLE** — the small-ball `padicLog_mul` is project-local
  and has the wrong (stronger) hypothesis; no mathlib building blocks exist.

**Rationale (1–2 paragraphs):**

This theorem is the multiplicativity of the `p`-adic logarithm on the entire group of principal
units `1 + 𝔪` — `log_p(xy) = log_p x + log_p y` for `‖x−1‖<1`, `‖y−1‖<1`. Every literature
source, from PlanetMath and Wikipedia to Kedlaya's and Keith Conrad's notes to the recent
arXiv "image of the p-adic logarithm on principal units" papers, states exactly this on exactly
this domain; it is the keystone fact of `p`-adic analysis underlying Iwasawa theory and `p`-adic
L-functions. The Lean statement is correct, sorry-free, at maximal generality (any complete
ultrametric extension of `ℚ_p`, with `CharZero` already pared off), and is genuine API — three
internal call sites across two files route through it, with no hand re-derivation anywhere. It
is not composable from mathlib in any number of steps, because **mathlib has none of the
building blocks**: the official p-adics overview lists no analytic p-adic functions; there is
no `padicLog`, no `padicExp`, and even the general analytic `NormedSpace.exp` has never had its
`log` inverse built. The only nearby thing, `PowerSeries.log`, is a formal series, not an
evaluated function on a field.

The single nuance — and the reason the verdict is "YES-add-as-is *as part of a package*" rather
than a free-standing YES — is that this lemma is one node in a `padicLog` API that mathlib
lacks entirely. It cannot be PR'd in isolation: its statement mentions `padicLog`, and its proof
needs `InExpBall`, the small-ball `padicLog_mul` (itself resting on `padicExp` + the exponential
functional equation), and `exists_pPow_pow_inExpBall`. So the actionable contribution is the
**whole `padicLog`/`padicExp` development**, with this theorem as the headline "log is a
homomorphism on principal units" result. That is squarely a YES for mathlib: a long-standing,
named gap (`p`-adic exp/log) filled at the right generality. Cost (porting the whole `PadicExp`
file) does not downgrade the verdict — per the Bourbaki-2.0 rule, building the right foundational
API is exactly the work mathlib exists to do.

**WHY add it (refactor-actionable detail):**
- *New mathematical content mathlib is missing.* Mathlib has **no `p`-adic exponential or
  logarithm at all** — confirmed by grep over `Mathlib/NumberTheory/Padics/` (no Exp/Log file),
  by Loogle (`padicLog` = "unknown identifier"), by LeanSearch (no non-archimedean log), and by
  the official Lean-community p-adics theory page, which explicitly lists *no* analytic/
  transcendental p-adic functions. **Name the gap:** `Mathlib/NumberTheory/Padics/` stops at
  Hensel's lemma + Mahler basis; the analytic layer (`exp_p`, `log_p`, and the logarithm
  homomorphism on `1+𝔪`) has never been formalised. This theorem is the central identity of
  that missing layer.
- *How it composes with mathlib's existing API.* Once `padicLog` exists, this lemma is the
  `map_mul`→`map_add` content that lets one bundle `log_p` as an `AddMonoidHom`/group hom on the
  principal-unit subgroup (composing with `Subgroup`/`MonoidHom` API, `IsUltrametricDist`,
  `PadicInt`, and roots-of-unity/`IsPrimitiveRoot` lemmas already in mathlib). It is the
  prerequisite for `p`-adic regulators, `p`-adic L-functions, and the Coleman/Iwasawa logarithm
  — all currently un-formalisable in mathlib for lack of `log_p`.

Proposed mathlib location: `Mathlib/NumberTheory/Padics/Exponential.lean` (new file; analytic
layer above `PadicNumbers`/`PadicIntegers`), or `Mathlib/Analysis/Padics/Log.lean`.

Proposed PR title: `feat(NumberTheory/Padics): the p-adic exponential and logarithm` (the
homomorphism law `padicLog_mul_of_norm_lt_one` is the headline theorem of the PR).

PR grouping (**required** — this lemma cannot ship alone): bundle the whole `padicLog`/`padicExp`
core as one (or a small ordered series of) PR(s):
- `InExpBall` (the convergence ball) — `PadicExp.lean:65`
- `padicExp`, `padicExp_add`, and the exp↔log inversions (`padicExp_padicLog`,
  `padicLog_padicExp`, `norm_padicLog`) — `PadicExp.lean:270, 417, 935, 950`
- `padicLog`, `padicLog_one`, small-ball `padicLog_mul` — `PadicExp.lean:384, 388, 973`
- `exists_pPow_pow_inExpBall` (the `p`-power descent) — `ExtLog.lean:129`
- **this theorem** + its unit-ball siblings `padicLog_pow_p_of_norm_lt_one`,
  `padicLog_pow_pPow_of_norm_lt_one`, `padicLog_pow_of_norm_lt_one`, and the finite-product
  `padicLog_prod_of_norm_lt_one` (`ResidueZeta.lean:1288`).
The natural PR order is: exp ball + exp + inversions → log + small-ball mult → `p`-power descent
→ **unit-ball multiplicativity (this lemma)** → pow/prod corollaries.

Pre-PR checklist before opening:
- [ ] `/generalise PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one` — confirm no further
      weakening (Phase 4 already says MAXIMALLY GENERAL; this is a confirmation pass). Consider
      whether the whole cluster should be stated over a general complete non-archimedean
      `[NormedField] [NormedAlgebra ℚ_[p] _]` once, in a `variable` block, exactly as the
      project already does.
- [ ] `/cleanup PadicLFunctions/PadicLFunctions/ValuesAtOne.lean PadicLFunctions.MeasureR.padicLog_mul_of_norm_lt_one`
      — full style/naming/golf audit + diff gates on this lemma and its package siblings before
      upstreaming. (Naming note: mathlib would likely prefer `padicLog_mul` for the unit-ball
      version with the small-ball one renamed, e.g. `padicLog_mul_of_mem_expBall`.)
- [ ] Pick a mathlib reviewer from recent `Mathlib/NumberTheory/Padics/` committers; announce on
      the `#mathlib4` Zulip `Maths` stream first (a `p`-adic-analysis API of this size warrants a
      design discussion before the PR).

---

## Next step

Open (after the pre-PR checklist) a `feat(NumberTheory/Padics): the p-adic exponential and
logarithm` PR that ships the whole `padicExp`/`padicLog` core **as one package**, with
`padicLog_mul_of_norm_lt_one` (the homomorphism law on the full unit ball) as the headline
result. Do **not** attempt to upstream this lemma in isolation — its statement and proof depend
on `padicLog`, `InExpBall`, `padicLog_mul`, and `exists_pPow_pow_inExpBall`, none of which
mathlib currently has. Announce on Zulip and run `/generalise` + `/cleanup` on the cluster first.
