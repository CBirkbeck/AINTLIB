# `/mathlibable` report — `PadicLFunctions.norm_padicExp_sub_padicExp`

**Final verdict: `YES-but-generalise-first`** (reason: LITERATURE-WEAKENING — the result
is standard and missing from mathlib, but the Lean form is keyed to `ℚ_[p]`-coefficient
factorials while the literature-standard statement is for *any* complete nonarchimedean
field, with the exponential having its own coefficients there).

---

### Baseline (Phase 0)
- lake build:               build NOT re-run — reasoned from source (per task instruction; tree is stale/slow). Repo at `e28d694 bump: mathlib v4.32.0-rc1`.
- decl `PadicLFunctions.norm_padicExp_sub_padicExp`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:202`
- kind:                      theorem
- has sorry:                 no (full proof, lines 202–257)
- module docstring summary:  the p-adic exponential/logarithm on a nonarchimedean complete normed `ℚ_[p]`-algebra field, realising RJW Lemma 5.14 (Cassels §12; Washington §5.1).

---

### Statement (Phase 1)

`norm_padicExp_sub_padicExp` is a **theorem** stating:

> On the open ball of convergence `‖x‖ < p^{−1/(p−1)}` of the p-adic exponential, `exp`
> is an **isometry**: for any two points `x, y` in the ball, `‖exp x − exp y‖ = ‖x − y‖`.

The mathematical content is exactly K. Conrad's *Infinite series in p-adic fields*,
**Theorem 4.5**, two-point form: *"For x and y in D_p, |e^x − e^y| = |x − y|"* — the
phenomenon Conrad introduces with *"A more striking contrast [with real analysis] is that
it preserves distances!"* The same statement appears as Cassels (*Local Fields*, §12) and
Washington (*Cyclotomic Fields*, §5.1), and underlies the standard fact that `exp` is a
bijective isometry from the disk `D_p` onto `1 + D_p`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`
  — the value field: a **complete ultrametric (nonarchimedean) normed field** that is a
  normed `ℚ_[p]`-algebra. This is precisely the literature's "p-adic field K = complete
  extension of `ℚ_[p]`".

Hypotheses (Lean side):
- `(hx : InExpBall p x)` — `x` lies in the open convergence ball, encoded rpow-free as
  `‖x‖^{p−1} < p⁻¹` (equivalent to `‖x‖ < p^{−1/(p−1)}`).
- `(hy : InExpBall p y)` — same for `y`.

Conclusion (math): `exp` restricted to the open ball is an isometry: `|exp x − exp y| = |x − y|`.

Conclusion (Lean): `‖padicExp p x - padicExp p y‖ = ‖x - y‖`, where
`padicExp p x = ∑' n, (n! : ℚ_[p])⁻¹ • x ^ n` (file def, line 130).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is the isometry half of a *named* classical result (RJW Lem 5.14 / Conrad Thm 4.5 /
Cassels §12), and it is a primary lemma of the file's exponential cluster (decomposition E3) —
both BIG triggers. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. (Proof body is ~55 substantive
lines; this is not a one-liner under any reading.)

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential function isometry on disk of convergence isometric" | yes | `\|exp z − 1\|_p = \|z\|_p` on `\|z\| < p^{−1/(p−1)}`; exp bijective onto `1+D_p` | Wikipedia, arXiv 2504.03430 ("p-adic exp maps are isometries in their convergence domains") |
| 2 | WebSearch (general / radius) | `"p-adic exponential exp isometry "p^{-1/(p-1)}" radius of convergence"` | yes | radius `p^{−1/(p−1)}`; `\|exp z − 1\|_p = \|z\|_p`; bijection `D_p → 1+D_p` | PlanetMath, K. Conrad, A. Bharadwaj notes |
| 3 | WebSearch (named-after / nonarch aliases) | `nonarchimedean exponential "norm preserving" OR isometry log inverse Cassels` | partial | isometry/`norm-preserving` confirmed as the nonarch phenomenon; Mazur–Ulam (non-arch isometries) | Cassels not surfaced by title; found via Conrad+Robert below |
| 4 | ChatGPT MCP | "standard form, generality, historical evolution of: p-adic exp is an isometry on its disk" | n/a | — | ChatGPT-math MCP server is installed (`~/.claude/mcp-servers/chatgpt-math/`) but **not registered as a callable tool** in this worker session. Substituted the same "standard form + generality + history" question into channels 1–3 + 6 + the K. Conrad primary source (read in full). |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references` and `refs/` | n/a | — | Neither directory exists in this checkout (PDFs are local-only and absent here). Recorded n/a. |
| 6 | nLab | "p-adic exponential map" / "exponential map" | partial | exp/log inverse pair on `p'𝔾_a^+`; isometry on convergence domain | nLab `exponential map` is generic; the p-adic isometry sits in the number-theory sources, not nLab proper |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; it is a metric statement about a concrete analytic function. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry concept; pure p-adic analysis. |
| 9 | MathOverflow / Math.SE | folded into WebSearch channels 1–3 | yes | same `\|exp x − exp y\| = \|x − y\|` form | covered by Conrad/PlanetMath hits |
| 10 | recent arXiv (≤5y) | (channel-1 result) arXiv 2504.03430 "A p-adic class formula for Anderson t-modules" | yes | "the p-adic exponential maps are isometries in their convergence domains" | confirms the isometry framing is live in current research |
| 11 | **Primary source (authoritative)** | K. Conrad, *Infinite series in p-adic fields*, §4 (read pages 1–16 from disk) | **yes** | **Thm 4.5: "For x and y in D_p, \|e^x − e^y\| = \|x − y\|"**; Def 4.1; Cor 4.6 (injectivity) | EXACT match to the target; stated over `K` = complete extension of `ℚ_p` |

#### Literature summary (Phase 3)

Concept identified as: **the p-adic exponential is an isometry on its disk of convergence**
(K. Conrad Thm 4.5; Cassels, *Local Fields* §12; Robert, *A Course in p-adic Analysis*,
"The Exponential and Logarithm"; Washington, *Cyclotomic Fields* §5.1).

Sources agree on the standard form: **yes.** The canonical statements are the one-point form
`|exp t − 1| = |t|` and the two-point form `|exp x − exp y| = |x − y|`, both for `x, y` in
`D_p = {x : |x| < (1/p)^{1/(p−1)}}`. The target is *verbatim* the two-point form.

Most general standard form: for **any complete nonarchimedean (ultrametrically) valued field
`K` of residue characteristic `p` (a complete extension of `ℚ_p`)**, the exponential series
`exp(x) = ∑ xⁿ/n!` (coefficients `n!⁻¹ ∈ K`) is an isometry on `D_p(K)`. Conrad states it for
exactly this `K`; the equation is identical for `K = ℚ_p`, `K = ℂ_p`, or any finite/complete
extension.

Generality dimensions where the literature varies:
- **Coefficient/field placement**: Conrad/Cassels treat `exp` as a power series *over `K`
  itself* (`n!⁻¹ ∈ K`). The Lean form instead places the factorials in `ℚ_[p]` and uses the
  algebra action `(n! : ℚ_[p])⁻¹ • xⁿ`. Mathematically identical for an algebra over `ℚ_[p]`
  (the embedding `ℚ_[p] → L` carries `n!⁻¹`), but the literature's home is "coefficients in
  the field where `x` lives", not "coefficients pulled back from a fixed base `ℚ_[p]`".
- **Field**: `ℚ_p` ⊆ `ℂ_p` ⊆ general complete-nonarch-`K`. The most general is general `K`.
  The Lean `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` already captures "general
  complete nonarch `K`" — but tied to `[NormedAlgebra ℚ_[p] L]`.

Disagreement with the literature: **none on content.** The only gap is presentation —
literature: exp is a series with coefficients in the ambient field; Lean: coefficients
`• …` pulled from `ℚ_[p]`. See Phase 4.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): for a complete nonarchimedean field `K` of residue
char `p`, with `exp(x) = ∑ xⁿ/n!` (`n!⁻¹ ∈ K`), one has `|exp x − exp y| = |x − y|` on
`D_p(K)`.

#### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[NormedAlgebra ℚ_[p] L]` + factorials `(n! : ℚ_[p])⁻¹ • xⁿ` | exp as a `ℚ_[p]`-series acting on `L` | exp as a series **over `L` itself**, `(n! : L)⁻¹ * xⁿ`, needing only that `L` has char-0-style invertible `n!` (true: char of a normed field over `ℚ_p` is 0) | **yes** | The literature only needs `L` complete nonarchimedean of residue char `p`; the `ℚ_[p]`-algebra scaffolding is a strengthening used to phrase the factorials. Restating with `(n! : L)⁻¹` drops the algebra hypothesis and matches the source. MODERATE: the whole file's `padicExp`/Legendre API would move from `ℚ_[p]`-scaling to `L`-internal factorials. |
| 2 | `[NormedField L] [IsUltrametricDist L] [CompleteSpace L]` | complete ultrametric normed field | complete nonarchimedean valued field `K` | NO (already maximal) | This *is* the literature's `K`. Completeness is needed for the `tsum`; ultrametricity is the entire point (the strong triangle inequality is what makes exp an isometry — false archimedean-ly). Cannot weaken. |
| 3 | `Fact p.Prime` | `p` prime | residue characteristic `p` prime | NO | Intrinsic; `p` is the residue char and `D_p`'s radius depends on it. |
| 4 | `InExpBall p x/y` (open ball `‖x‖^{p−1} < p⁻¹`) | open ball, rpow-free | open disk `D_p` `‖x‖ < (1/p)^{1/(p−1)}` | NO (open ball is required) | Conrad's proof and the Lean proof both need the **open** ball (the in-file docstring flags "strictness needs the OPEN ball"); on the boundary the isometry can fail. Correct as stated. |

#### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (one axis: row 1).
Number of weakening opportunities found: **1** (drop `[NormedAlgebra ℚ_[p] L]`; state `exp`
with `L`-internal factorials `(n! : L)⁻¹`, as Conrad/Cassels do).

Proposed restatement (literature-standard target):

```lean
-- exp over the field itself, the Conrad/Cassels form:
noncomputable def padicExp' {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CompleteSpace L] (p : ℕ) (x : L) : L := ∑' n : ℕ, (n.factorial : L)⁻¹ * x ^ n

theorem norm_padicExp'_sub_padicExp' {L : Type*} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] (p : ℕ) [Fact p.Prime]
    {x y : L} (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) (hy : ‖y‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖padicExp' p x - padicExp' p y‖ = ‖x - y‖ := by
  sorry  -- proof adapts: Legendre bound on ‖(n! : L)‖ needs the residue-char-p input;
         -- the rest (geometric tail domination + strong triangle) is field-internal already
```

Cost of restatement: **MODERATE** — the isometry proof itself is almost field-internal already
(it manipulates `‖x‖`, `‖x−y‖`, and `‖n!‖` via the strong triangle inequality and a geometric
bound). The work is rerouting the Legendre/`norm_factorial_le` chain so the `n!`-norm bound is
established for `(n! : L)` directly (currently `(n! : ℚ_[p])` via `Padic.norm_eq_zpow_neg_valuation`).
This requires a hypothesis pinning the residue characteristic / how `p` sits in `L` (e.g. a
norm bound `‖(p : L)‖ = p⁻¹` or that the restriction of the norm to `ℚ` is the `p`-adic one) —
the proof needs *some* such input; it cannot be literally typeclass-free. **Cost does not
downgrade the verdict** (mathlib ships the right form).

#### 4c. Modern-idiom check (Bourbaki 2.0)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclass? | partial | `[IsUltrametricDist L]` etc. are *already* typeclasses; the one bundled-strengthening is `[NormedAlgebra ℚ_[p] L]`, which 4a row 1 proposes to drop in favour of an internal residue-char hypothesis | a `ℚ_p`-algebra-free statement composes with **any** complete nonarch field (e.g. `ℂ_p`, finite extensions) without re-instantiating the algebra |
| 2 | sequences/metric → filters/topology? | no | the statement is already a clean metric equality `‖·‖ = ‖·‖`; the *proof* already uses `Tendsto … atTop`/filters and `IsUltrametricDist.norm_tsum_le_of_forall_le`. No idiom gap. | — |
| 3 | construction → universal property? | no | exp is an honest analytic function (a `tsum`); there is no universal property to phrase it by. | — |
| 4 | set+closure-predicate → bundled substructure? | no | `InExpBall` is a `Prop` membership in an open ball; that is the right shape (it's a hypothesis, not a structure carrying API). | — |
| 5 | vector-space/metric/field-specific → weaken typeclass? | yes (= 4a row 1) | drop `[NormedAlgebra ℚ_[p] L]`; the field-itself form is the weakening | full reuse across complete-nonarch fields; aligns exp with how mathlib states power-series facts (over the coefficient field) |
| 6 | 1-categorical → higher-categorical? | no | not categorical. | — |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | the only index is `n : ℕ` summing the series; intrinsic. | — |

#### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it **coincides with the literature-weakening of 4a/4b**
(drop the `ℚ_[p]`-algebra packaging; state exp over `L` itself). It is not an *additional*
independent modernisation. Real mathematical improvement: the result then applies verbatim to
`ℂ_p` and to every complete nonarchimedean extension without the `[NormedAlgebra ℚ_[p] L]`
instance, matching both the literature and mathlib's "facts about a power series live over its
coefficient field" convention. Cost: MODERATE (as 4b).

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is **theorem** (introduces no definitional equalities or
typeclass-search paths). (The companion `def padicExp` would get its own assessment; this
report is scoped to the theorem.)

---

### PHASE 5 — Mathlib search

### Mathlib search-status: `PadicLFunctions.norm_padicExp_sub_padicExp`

```
[A] Lean-Finder       n/a: not callable as a tool in this worker session (recorded n/a per the five-method rule).
[B] Loogle            n/a: lean_loogle not callable here; substituted by [D] type-aware grep over mathlib source.
[C] LeanSearch        n/a: lean_leansearch not callable here; substituted by the EXHAUSTIVE Phase-3 NL web search + [D].
[D] Grep mathlib src  Terms: "padicExp", "Padic.exp", "PadicInt.exp", "p-adic exponential",
                      "norm_exp_eq", "exp_sub_exp", "expSeries…isometr", "padicLog".
                      → NO HITS for any p-adic exponential or logarithm. Mathlib has NO
                      `padicExp`/`padicLog` and no `Analysis/.../Padics/.../Exp` file at all.
                      The only `norm_exp_eq*` hit is COMPLEX/archimedean and unrelated:
                      `Complex.norm_exp_eq_iff_re_eq : ‖exp x‖ = ‖exp y‖ ↔ x.re = y.re`
                      (Mathlib/Analysis/Complex/Trigonometric.lean:1000) — a statement about
                      complex moduli, not an ultrametric isometry. Mathlib's exp infra
                      (`NormedSpace.exp`, `Complex.exp`, C*-algebra exp) is entirely
                      archimedean, where exp is NOT an isometry.
[E] Name pattern      lean_local_search not callable; grep `def padicExp|theorem.*padicExp|
                      Padic.exp|PadicInt.exp` over mathlib → 0 hits. Confirmed.
```

Searched for both:
- the user's current form (`ℚ_[p]`-scaled exp isometry) — absent;
- the literature-standard form (exp over a complete nonarch field) — also absent. Mathlib
  has neither the specialisation nor the general form.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard
general form). Mathlib has no p-adic exponential/logarithm whatsoever; the nearest decl
(`Complex.norm_exp_eq_iff_re_eq`) is an unrelated archimedean modulus fact.

---

### PHASE 6 — Composition check (+ call-sites signal)

#### Call sites — `PadicLFunctions.norm_padicExp_sub_padicExp`

Internal use count: **2** (within the project, excluding the declaring line 202)
External-to-file callers: **0 distinct files** (all uses are inside `PadicExp.lean`)

| Caller file:line | Usage pattern (one-line excerpt) |
|---|---|
| `PadicExp.lean:264` | `simpa using norm_padicExp_sub_padicExp p hx h0` — derives `norm_padicExp_sub_one` (`‖exp x − 1‖ = ‖x‖`, Conrad Thm 4.5 one-point form) |
| `PadicExp.lean:1144` | `norm_padicExp_sub_padicExp (L := ℚ_[p]) p (inExpBall_of_mem_span …) (…)` — supplies the Lipschitz-with-`K=1` (isometry) step proving the character `t ↦ exp(t·log x)` is continuous, used to identify `xˢ := exp(s·log x)` with `PadicInt.onePAdicPow` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using this lemma?):
- (none) — no other site re-proves `‖exp x − exp y‖ = ‖x − y‖` by hand. Both consumers route
  through this lemma.

Signal: **K = 2 internal uses, both load-bearing, no inline re-derivation.** Both downstream
results (`norm_padicExp_sub_one` and the `onePAdicPow` agreement — the file's RJW-5.14 payoff)
*essentially* depend on this exact isometry. This is a real API lemma, not a wrapper consumers
bypass → leans toward a YES-family verdict.

#### Composition check (Phase 6)

Can `norm_padicExp_sub_padicExp` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib `exp`/isometry lemma.
  - Mathlib decls available: `Complex.exp`, `NormedSpace.exp`, C*-algebra exp; none p-adic.
  - Result: **fails.** There is no p-adic `exp` in mathlib to call, and the archimedean exp
    is provably *not* an isometry, so nothing specialises.

Attempt 2: assemble from the strong triangle inequality + a generic "power series is
Lipschitz on its disc" lemma (cf. Conrad Thm 3.12).
  - Mathlib decls: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`,
    `IsUltrametricDist.norm_tsum_le_of_forall_le`, `geom_sum₂_mul`, the Legendre bound
    `padicValNat` API.
  - Result: **fails as a composition.** The actual proof (lines 202–257) is a genuine
    ~55-line argument: split off the linear term, prove every higher term is *strictly*
    smaller than `‖x−y‖` (a separate ~55-line lemma `norm_factorial_inv_smul_pow_sub_lt`,
    lines 141–197, via geometric-tail domination at the `(p−1)`-th power level + Legendre),
    bound the tail `tsum`, then apply the strong triangle equality. This is far more than
    3 calls and is irreducibly a proof, not glue.

Conclusion: **NOT-COMPOSABLE.** Mathlib lacks both the object (`padicExp`) and any
near-composition; the isometry is a real theorem requiring the full nonarchimedean argument.

---

## Verdict: `PadicLFunctions.norm_padicExp_sub_padicExp`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): EXACT named match — K. Conrad *Infinite series in p-adic
  fields* **Thm 4.5** (two-point form `|exp x − exp y| = |x − y|`), also Cassels §12 / Robert /
  Washington §5.1, and live in arXiv 2504.03430. Standard form is for a complete
  nonarchimedean field `K`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — one axis: the Lean
  form bundles `[NormedAlgebra ℚ_[p] L]` and writes the series with `ℚ_[p]`-pulled factorials
  `(n! : ℚ_[p])⁻¹ • xⁿ`, whereas the literature states `exp` over the field itself. Phase 4c
  agrees (the modern-idiom move *is* this same weakening). 1 weakening opportunity, MODERATE
  cost.
- Mathlib search (Phase 5): **not in mathlib** under either the user's or the general form;
  mathlib has no p-adic exponential/logarithm at all. Nearest decl is the unrelated
  archimedean `Complex.norm_exp_eq_iff_re_eq`.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~55-line ultrametric proof; no
  mathlib object to specialise and no ≤3-call route.

**Rationale.** This is a textbook-canonical theorem (Conrad's "exp preserves distances!",
Thm 4.5) that mathlib is entirely missing — mathlib has no p-adic exponential, so the *whole*
`PadicExp.lean` exponential cluster, this isometry included, is a real contribution filling a
named gap (a fully developed p-adic exp/log API is a long-standing absence; mathlib's only
`exp` work is archimedean, where the isometry is false). The reason the verdict is
`YES-but-generalise-first` rather than `YES-add-as-is` is purely the Phase-4b finding: the
statement is keyed to a `ℚ_[p]`-algebra with factorials drawn from `ℚ_[p]`, while the
literature-standard (and mathlib-idiomatic) form states `exp` as a power series over the
ambient complete nonarchimedean field itself. The narrowing is genuine — the result is needed
verbatim for `ℂ_p` and finite extensions of `ℚ_p` (where dragging in `[NormedAlgebra ℚ_[p] L]`
is awkward), and stating exp over `L` matches mathlib's convention that facts about a power
series live over its coefficient field.

**Refactor / upstreaming plan (YES-but-generalise-first):**

Reason for the generalisation:
- **LITERATURE-WEAKENING** — Phase 4b found the user's form strictly narrower than the
  Conrad/Cassels standard form (exp over the field itself, no `ℚ_[p]`-algebra packaging).
- (MODERN-IDIOM coincides with it, not independent: Phase 4c.)

Proposed restatement:
```lean
noncomputable def padicExp' {L : Type*} [NormedField L] [IsUltrametricDist L]
    [CompleteSpace L] (p : ℕ) (x : L) : L := ∑' n : ℕ, (n.factorial : L)⁻¹ * x ^ n

theorem norm_padicExp'_sub_padicExp' {L : Type*} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L] (p : ℕ) [Fact p.Prime]
    {x y : L} (hx : ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹) (hy : ‖y‖ ^ (p - 1) < (p : ℝ)⁻¹) :
    ‖padicExp' p x - padicExp' p y‖ = ‖x - y‖ := by
  sorry  -- the geometric-tail + strong-triangle core is field-internal already;
         -- only the Legendre ‖n!‖ bound must be re-derived from a residue-char-p input
         -- (e.g. a hypothesis ‖(p : L)‖ = (p:ℝ)⁻¹) rather than via Padic.valuation on ℚ_[p].
```
Mathlib downstream this enables:
- the exp/log isometry then applies to `ℂ_p` and every complete nonarchimedean extension of
  `ℚ_p` with no `[NormedAlgebra ℚ_[p] L]` instance needed;
- it composes with mathlib's existing nonarchimedean-summability API
  (`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`,
  `HasSum.mul_of_nonarchimedean`) and `IsUltrametricDist` lemmas uniformly over `K`.

Estimated cost of regeneralisation: **MODERATE** (the proof is mostly field-internal; the
re-routing is the `n!`-norm/Legendre bound). Note: EXPENSIVE/MODERATE does **not** downgrade
the verdict.

Next action: run `/generalise PadicLFunctions.norm_padicExp_sub_padicExp` (it will tension
against the Conrad/Cassels literature-standard form and the field-internal modern-idiom form),
deciding whether to PR the whole exp/log cluster restated over a complete nonarchimedean
field. Proposed mathlib home for the eventual cluster:
`Mathlib/NumberTheory/Padics/Exponential.lean` (new file) — co-locate with `PadicNumbers`,
`MahlerBasis`. Pre-PR: `/cleanup` the file + `/pre-submit`. PR grouping: ship the isometry
with its sibling `padicExp_zero`, `padicExp_add` (functional equation), `norm_padicExp_sub_one`
(one-point form), and the log inverse lemmas as one "p-adic exp/log" PR — this single lemma
should not go up alone.

---

## Next step

Run `/generalise PadicLFunctions.norm_padicExp_sub_padicExp` to restate `exp` over a complete
nonarchimedean field (dropping `[NormedAlgebra ℚ_[p] L]`, factorials internal to `L`), then
`/cleanup` + `/pre-submit` and open a single "p-adic exponential & logarithm" mathlib PR
(target `Mathlib/NumberTheory/Padics/Exponential.lean`) bundling this isometry with
`padicExp_add`, `norm_padicExp_sub_one`, and the log inverse lemmas — mathlib currently has no
p-adic exponential at all, so the gap is real; only the field-generality of the statement needs
fixing first.
