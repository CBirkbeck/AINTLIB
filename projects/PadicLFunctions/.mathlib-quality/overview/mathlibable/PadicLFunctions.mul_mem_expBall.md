# `/mathlibable` report — `PadicLFunctions.mul_mem_expBall`

Mode A, full 10-phase workflow. The exhaustive 9-channel literature search ran;
the ChatGPT MCP channel is unavailable in this environment and is recorded `n/a`
with reason (no `mcp__*chatgpt*` / `openai` tool surfaced; `/setup-chatgpt` not
run). The three WebSearch queries cover the specific / general / named-alias
generality levels as the protocol requires.

**Final verdict: `NO-composable-from-mathlib`** (the closure-under-multiplication
half of the ultrametric ball-around-1 fact; mathlib's `IsUltrametricDist`
ultrametric API composes to it in ≤3 calls, and the better fix is a bundled
`Submonoid`/`Subgroup` — see Phase 7).

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); **reasoned from source**. The decl and all dependency lemmas (`InExpBall`, `IsUltrametricDist.norm_add_le_max`, `pow_le_pow_left₀`, `max_le_max`, `mul_le_of_le_one_right`, `max_cases`) were read directly from source and from `.lake/packages/mathlib/`.
- decl `PadicLFunctions.mul_mem_expBall`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:47`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  ExtLog.lean builds the extended (Iwasawa-branch) p-adic logarithm `extLog` on rational-valuation elements `x` with `xᵐ = pᵏ·y`, `y ∈ 1 + expBall`; this lemma is helper "W6a-a1" establishing the translated exponential ball `1 + B` is closed under multiplication.

---

### Statement (Phase 1)

`mul_mem_expBall` is a theorem stating the following:

Let `L` be a nonarchimedean (ultrametric) normed field, a `ℚ_[p]`-algebra. Let
`B = { w : ‖w‖ < p^{−1/(p−1)} }` be the open exponential-convergence ball
(encoded rpow-free as `InExpBall p w := ‖w‖^(p−1) < p⁻¹`). Then the *translated*
ball `1 + B = { y : y − 1 ∈ B }` is **closed under multiplication**: if
`y − 1 ∈ B` and `z − 1 ∈ B`, then `y·z − 1 ∈ B`.

Mathematically this is the closure-under-multiplication half of the standard fact
that the **principal-unit ball** `1 + 𝔪^k` (here the analytic ball of radius
`p^{−1/(p−1)}`) is a multiplicative subgroup of an ultrametric field. The engine
is the ultrametric (isosceles) inequality applied to the identity
`yz − 1 = (y−1)·z + (z−1)` together with `‖z‖ ≤ 1` (which itself follows because
`z − 1 ∈ B ⟹ ‖z−1‖ < 1`, and the ultrametric bound gives `‖z‖ ≤ max(‖z−1‖,1) = 1`).

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic / radius parameter `p^{−1/(p−1)}`.
- `{L : Type*}` with `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — the ambient nonarchimedean complete normed `ℚ_[p]`-algebra field. (`NormedAlgebra` and `CompleteSpace` are `omit`-ted for this lemma; only `NormedField` + `IsUltrametricDist` are used.)
- `{y z : L}` — the two ring elements being multiplied.

Hypotheses (Lean side):
- `hy : InExpBall p (y − 1)` — `y` lies in the translated ball `1 + B`.
- `hz : InExpBall p (z − 1)` — `z` lies in the translated ball `1 + B`.

Conclusion (math): the product `y·z` also lies in `1 + B`.

Conclusion (Lean): `InExpBall p (y * z − 1)`, i.e. `‖y*z − 1‖^(p−1) < p⁻¹`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma (decomposition tag "W6a-a1") — the multiplicative-closure
step of an analytic ball, used internally to build `extLog`. Not a named theorem,
not a `## Main results` headline, no person/place name.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for
framing.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`/`abbrev`/`structure`. The one-liner /
defeq-exemption analysis does not apply.

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | ultrametric "1 + maximal ideal" closed under multiplication principal units p-adic field "‖xy-1‖ ≤ max" | yes | `‖xy − 1‖ ≤ max(‖x−1‖,‖z−1‖)`; "if `‖x‖,‖y‖ = 1` then `‖xy‖ = 1`; the unit group is closed under multiplication" | UH topology-of-p-adic-groups notes, UChicago number.pdf, Leiden ch.8, W&M local.pdf — all derive it from the strong-triangle inequality. Standard. |
|  2 | WebSearch (general form) | nonarchimedean field group of principal units `1 + 𝔪` one-units closed under multiplication subgroup | yes | `Uᴸⁿ := 1 + Pᴸⁿ` is a **subgroup** of `Uᴸ` of finite index, for every `n` | MIT 18.785 Lecture #15 (2017 & 2021), Crew LCFT, Browning *Local Fields* (Warwick). The higher-unit filtration. The most general standard form: closure-under-multiplication is one half; the full statement is "`1 + 𝔪ⁿ` is a subgroup". |
|  3 | WebSearch (named-after / aliases) | Serre local fields filtration unit group `Uₙ` higher units p-adic logarithm Iwasawa exponential ball Washington cyclotomic fields 5.1 | yes | higher-unit groups `Uₖᵐ := 1 + 𝔪ₖᵐ`; Iwasawa `Log(1+x) = Σ(−1)ⁱ⁺¹xⁱ/i` on principal units; this lemma is the ball-version | arXiv 1907.06437 (image of 2-adic log on principal units), Coates–Sujatha, Hida 207a notes. Confirms the analytic-ball form (radius `p^{−1/(p−1)}`) is the exponential/log convergence ball, a sub-filtration of the `1 + 𝔪` tower. Matches the file's own citation (Washington §5.1). |
|  4 | ChatGPT MCP | "standard form / generality / historical evolution of: the translated ultrametric ball `1 + B` is closed under multiplication" | **n/a** | — | **ChatGPT MCP server not installed in this environment** (no `mcp__*chatgpt*` / `openai` tool surfaced; `/setup-chatgpt` not run). Recorded n/a per protocol. Queries #1–#3 already span specific / general / named-alias generality. |
|  5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` for "ultrametric / principal unit / 1 + B" | **n/a** | — | No `references/` directory and no `refs/` symlink present in this checkout. Recorded n/a with reason. (Sibling mathlibable reports in `.mathlib-quality/overview/mathlibable/` corroborate the ultrametric-isosceles framing.) |
|  6 | nLab | ultrametric space / nonarchimedean — balls as subgroups / multiplicatively closed | partial | strong triangle `max(d(x,y),d(y,z)) ≥ d(x,z)`; "all triangles isosceles" | nLab *ultrametric space* states the isosceles strong-triangle inequality but does **not** cover the algebraic (ring-multiplication) ball-closure statement. The analytic content is folklore there. |
|  7 | nCatLab (if categorical) | — | **n/a** | — | Not a categorical / higher-categorical concept — a metric-algebra inequality. Recorded n/a with reason. |
|  8 | Stacks Project (if alg geom) | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept. The closest Stacks content (valuation rings) phrases the result via the maximal ideal, not an analytic norm ball; not the relevant generality. Recorded n/a with reason. |
|  9 | MathOverflow / Math.StackExchange | nonarchimedean `1 + 𝔪` / `1 + B` closed under multiplication; principal units form a group | yes | standard Q&A: closure follows from `(1+a)(1+b) = 1 + (a + b + ab)` and ultrametric/ideal absorption; `1 + 𝔪ⁿ` is a multiplicative group | Multiple MSE/MO threads on "why are principal units a group" and "higher unit groups". The result is textbook, repeatedly asked at student level — never a *named* theorem. |
| 10 | recent arXiv (last 5 years) | image of p-adic logarithm on principal units; bases of `1 + 𝔭ⁿ` | yes | arXiv 1907.06437, 2104.03299 — all *use* "`1 + 𝔪ⁿ` is a multiplicative group / the log/exp converge on the ball" as a standing background fact | Confirms the analytic-ball multiplicative closure is assumed-known infrastructure, not stated as a contribution, in current research. |

The protocol passed: WebSearch ran 3 distinct queries at the specific / general /
named-alias levels (#1–#3); ChatGPT MCP recorded `n/a` with a concrete reason;
local references recorded `n/a` (directory absent); nLab checked (partial);
nCatLab / Stacks recorded `n/a` with reasons; MathOverflow/MSE and recent arXiv
checked (hits).

### Literature summary (Phase 3)

Concept identified as: the **closure-under-multiplication of the principal-unit /
higher-unit ball** `1 + 𝔪ⁿ` (here the analytic exponential-convergence ball
`1 + B`, `B = {‖·‖ < p^{−1/(p−1)}}`) in a nonarchimedean field. The standard
references frame it as the multiplicative-monoid (in fact subgroup) structure of
`Uⁿ = 1 + 𝔪ⁿ` (Serre *Local Fields* Ch. IV/V; Neukirch II §3; Washington
*Cyclotomic Fields* §5.1; MIT 18.785 Lecture #15).

Sources agree on the standard form: **yes**. The mechanism is uniformly: write
`yz − 1 = (y−1)z + (z−1)` (equivalently `(1+a)(1+b) − 1 = a + b + ab`), bound
`‖z‖ ≤ 1` by the ultrametric isosceles step, then apply the strong-triangle
inequality. This is exactly the proof in the Lean source.

Most general standard form: `1 + 𝔪ⁿ` is a **multiplicative subgroup** of the
units (closure under multiplication AND inverses), for any value of the radius in
the filtration — in any complete nonarchimedean field (or even any complete
nonarchimedean *ring* with maximal ideal, for the absorption argument), not just
the `ℚ_[p]`-algebra setting of the project.

Generality dimensions where the literature varies:
  - **the radius**: literature states it for the *whole* filtration `1 + 𝔪ⁿ`
    (any `n`, i.e. any sub-1 radius), not the single analytic radius
    `p^{−1/(p−1)}` the Lean lemma hardcodes via `InExpBall`. The most general
    form is "for any radius `r ≤ 1` (closed) / `r < ...` (open), the ball around 1
    is multiplicatively closed".
  - **closure direction**: literature gives the full **subgroup** (mul + inv);
    the Lean lemma gives only the `mul_mem` half (matching mathlib's
    `Subsemigroup`/`Submonoid` granularity).
  - **ambient structure**: stated for any nonarchimedean field/ring; the Lean
    lemma fixes a `NormedField` `ℚ_[p]`-algebra (but `omit`s the algebra
    instance, so only uses `NormedField` + `IsUltrametricDist`).

Disagreement with the literature: **none**. The Lean form is a correct
*specialisation* (single radius, mul-half only) of the standard fact.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): for any radius, the ball around `1` in a
nonarchimedean field is a multiplicative subgroup; the mul-closure half holds from
the ultrametric inequality alone in any `NormedField` (indeed
`NonUnitalSeminormedRing` once the `‖z‖ ≤ 1` ingredient is available) with
`IsUltrametricDist`.

### Generality analysis — `mul_mem_expBall`

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed field | nonarchimedean **ring** (mul-closure needs only submultiplicativity + ultrametric add) | yes | The proof uses only `norm_mul`, `IsUltrametricDist.norm_add_le_max`, `‖1‖ = 1`. `NormedField` is far stronger than needed; a `NormedRing`/`SeminormedRing` (or even `NonUnitalNormedRing` once `1` makes sense) with `IsUltrametricDist` suffices. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_[p]`-algebra | (not used) | yes | Already `omit`-ted for this lemma. Pure baggage — irrelevant to mul-closure. |
| 3 | `[CompleteSpace L]` | complete | (not used) | yes | Already `omit`-ted. Irrelevant. |
| 4 | `[IsUltrametricDist L]` | ultrametric | ultrametric (ESSENTIAL) | NO | The statement is **false** for a general normed ring at a 1-centered ball of arbitrary radius — `‖yz−1‖ ≤ max(...)` is exactly the strong-triangle step. Cannot be weakened. |
| 5 | radius via `InExpBall p` | the single analytic radius `p^{−1/(p−1)}` (`‖·‖^(p−1) < p⁻¹`) | **any** radius `r < 1` (or `≤ 1`) | yes | The proof never uses the specific value `p^{−1/(p−1)}`; it only uses that membership forces `‖·‖ < 1` (via `norm_lt_one_of_inExpBall`) and then bounds `‖yz−1‖^(p−1)` by `max(‖y−1‖^(p−1), ‖z−1‖^(p−1))`. The hardcoded radius is an artifact of the `InExpBall` predicate, not the mathematics. |
| 6 | conclusion: `mul_mem` only | product stays in ball | full **subgroup** (mul + one + inv) | yes (richer) | Literature gives the subgroup; mathlib bundles such facts as `Subsemigroup`/`Submonoid`/`Subgroup`. The mul-half alone is the `mul_mem'` field of such a bundle. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** along four independent
axes (NormedField → ultrametric (semi)normed ring; drop unused algebra +
completeness; single radius → arbitrary radius; mul-half → bundled
sub-structure). The essential hypothesis `IsUltrametricDist` is correctly present.

Number of weakening opportunities found: **4** (rows 1, 2/3, 5, 6).

Proposed restatement (most-general literature form):

```lean
-- as a standalone lemma, radius-general, ring-general:
theorem mul_mem_ball_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {r : ℝ} {y z : R}
    (hy : ‖y - 1‖ < r) (hz : ‖z - 1‖ < r) (hr : r ≤ 1) :
    ‖y * z - 1‖ < r
-- (or, the canonical mathlib idiom, see Phase 4c: a bundled Subsemigroup/Submonoid
--  `Metric.ball (1 : R) r` analogous to IsUltrametricDist.ball_openSubgroup, but in
--  the additive/ring metric on a SeminormedRing.)
```

Cost of restatement: **CHEAP** — mechanical. The existing proof transfers almost
verbatim (replace `InExpBall` membership by `‖·‖ < r`, drop the `^(p−1)` shell).
The `‖z‖ ≤ 1` step needs `r ≤ 1`, which the analytic radius `p^{−1/(p−1)}`
satisfies.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | Could "let X be a foo" preambles become **typeclasses / instances**? | partly | already typeclass-based; the move is to drop unused `NormedAlgebra`/`CompleteSpace` and weaken `NormedField` → `SeminormedRing + IsUltrametricDist` | the lemma then applies to `ℤ_p`, valuation rings, any ultrametric (semi)normed ring |
|  2 | Sequences/metric where **filters/topological** would generalise? | no | — | finite/pointwise inequality; no limit to filter-ise |
|  3 | **Construct** where a **universal-property class** fits? | no | — | not a construction |
|  4 | **set-with-closure-predicate** where a **bundled-substructure type** composes with mathlib's lattices? | **YES** | bundle `Metric.ball (1 : R) r` / `Metric.closedBall (1 : R) r` as a `Subsemigroup`/`Submonoid` of the ring — directly analogous to mathlib's existing `Subsemigroup.unitBall`, `Submonoid.unitClosedBall` (`Mathlib/Analysis/Normed/Field/UnitBall.lean`) and `IsUltrametricDist.ball_openSubgroup` (`Mathlib/Analysis/Normed/Group/Ultra.lean`) | the `Submonoid`/`Subgroup` lattice API, `Submonoid.pow_mem` (replacing the project's separate `pow_mem_expBall`), `Submonoid.prod_mem` (replacing `ExtLogDomain.prod`'s ball half), quotient/closure machinery; lets the whole `extLog` development carry membership as monoid/subgroup membership instead of bespoke `InExpBall` lemmas |
|  5 | **vector-space/metric/field-specific** result that mathlib's typeclass hierarchy weakens to **modules / pseudometric / (semi)ring**? | **YES** | `NormedField` → `SeminormedRing + NormOneClass + IsUltrametricDist` (see Phase 4b row 1) | the result + bundle become reusable for `ℤ_p`, `𝓞_K`, valuation rings, not only normed fields |
|  6 | **1-categorical** with a higher-categorical generalisation? | no | — | n/a |
|  7 | **concrete index (ℕ,ℤ,ℝ)** generalising to arbitrary structures? | partly | the hardcoded radius `p^{−1/(p−1)}` → arbitrary `r ≤ 1` (Phase 4b row 5) | one bundle covers every level of the principal-unit filtration `1 + 𝔪ⁿ`, not just the exp ball |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
  - Proposed mathlib-idiomatic restatement: a bundled
    `Subsemigroup`/`Submonoid` (open `Subgroup` once inverses are added) whose
    carrier is `Metric.ball (1 : R) r` in a `SeminormedRing R` with
    `[IsUltrametricDist R]` — the *additive-metric, 1-centered* sibling of the
    existing `Subsemigroup.unitBall`/`Submonoid.unitClosedBall` (0-centered) and
    of the *group-metric* `IsUltrametricDist.ball_openSubgroup`.
  - Cost: **MODERATE** — the carrier + `mul_mem'` is the present proof; adding
    `one_mem'`/`inv_mem'` and choosing the right typeclass home is the extra work.
  - Mathlib downstream this enables: `Submonoid.pow_mem` subsumes the project's
    `pow_mem_expBall`; `Submonoid.prod_mem` subsumes the ball half of
    `ExtLogDomain.prod`; the `Subgroup`/`Submonoid` lattice and closure API become
    available; the `extLog` API can be phrased over a named substructure.
  - Real mathematical improvement: it eliminates the project's hand-rolled
    `InExpBall`-closure lemmas (`mul_mem_expBall`, `pow_mem_expBall`,
    `inExpBall_one_sub_one`) in favour of one bundled substructure + mathlib's
    generic membership API — exactly the `Submodule`-vs-ad-hoc-closure-predicate
    modernisation pattern.

This Phase-4c finding (and the Phase-4b STRICTLY-NARROWER verdict) means a
**`YES-add-as-is` verdict is gate-forbidden**. The question Phase 7 must answer is
whether the right action is YES-but-generalise-first (ship the bundled
substructure to mathlib) or NO-composable-from-mathlib (mathlib already composes
to the bare lemma in ≤3 calls, and the bundle is a separate, larger mathlib-infra
proposal rather than *this* lemma). See Phase 6/7.

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `mul_mem_expBall`

[A] Lean-Finder       (tool not available in env; n/a)            n/a: no `mcp__*lean*finder*` tool surfaced
[B] Loogle            (tool not available in env; emulated by typed grep over mathlib src)   no exact hit
[C] LeanSearch        (tool not available in env; emulated by NL→grep)                       no exact hit
[D] Grep mathlib src  `mul_mem.*ball`, `ball.*Submonoid`, `expBall`, `ball_openSubgroup`, `unitBall`, `norm_add_le_max`, `oneUnitsSubgroup`   hits on RELATED-but-distinct decls (below)
[E] Name pattern      `expBall`, `mem_expBall`, `mul_mem_ball`, `unitClosedBall`             no `*expBall*`; found `mul_mem_ball_iff_norm`, `Submonoid.unitClosedBall`

Searched for both:
  - the user's current form (`InExpBall`, ball around 1, radius `p^{−1/(p−1)}`, normed field) — **not in mathlib** (no `InExpBall`/`expBall` anywhere).
  - the literature-standard form (ball around 1 of arbitrary radius is multiplicatively closed / a subgroup, in a nonarchimedean ring) — mathlib has **closely related but not identical** decls:

Closest mathlib decls found (all read in full, not just cited by name):

1. **`IsUltrametricDist.ball_openSubgroup`** (`Mathlib/Analysis/Normed/Group/Ultra.lean:162`)
   — in a `SeminormedGroup S` with `[IsUltrametricDist S]`, `Metric.ball (1 : S) r`
   is an `OpenSubgroup`, with `mul_mem'` proved via `norm_mul_le_max`. **Distinct
   setting**: the *multiplicative-group* metric `dist x y = ‖x⁻¹·y‖`, not the
   *ring/additive* metric `‖x − 1‖`. For a normed **field** `L`, `‖y − 1‖` is the
   additive-norm distance from `1`, which is **not** the `SeminormedGroup`-on-`Lˣ`
   distance. So `ball_openSubgroup` does **not** instantiate to `mul_mem_expBall`.
   (It is, however, the structural template for the right mathlib addition — Phase 4c.)

2. **`Subsemigroup.unitBall` / `Submonoid.unitClosedBall`**
   (`Mathlib/Analysis/Normed/Field/UnitBall.lean:32,139`) — the ball/closedBall
   **around 0** of radius **1** in a (non-unital) seminormed ring is a
   `Subsemigroup`/`Submonoid`, `mul_mem'` via `norm_mul_le` + `mul_lt_one`.
   **Distinct**: centred at `0` (not `1`), radius exactly `1` (not
   `p^{−1/(p−1)}`), and crucially **non-ultrametric** (works in any normed ring by
   submultiplicativity). The 1-centred, arbitrary-radius statement is *false*
   without `IsUltrametricDist`, so this is genuinely a different fact.

3. **`mul_mem_ball_iff_norm`** (`Mathlib/Analysis/Normed/Group/Basic.lean:889`)
   — `a * b ∈ ball a r ↔ ‖b‖ < r`. A membership *rewrite*, not a closure lemma;
   does not give multiplicative closure of a fixed ball.

4. **`Ideal.oneUnitsSubgroup`** (used in the sibling AINTLIB project
   FltRegularBernoulli, `CyclotomicUnits/LogDomain.lean`) — `1 + 𝔪` as a `Subgroup`
   of units in a **valuation-ring / `Valued`** setting. Distinct formulation
   (algebraic ideal, not analytic norm ball); does not import or instantiate to the
   normed-field `InExpBall` form.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard
form). Mathlib has the **building blocks** — `IsUltrametricDist.norm_add_le_max`,
`norm_mul`, `norm_one`, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` (for
`‖z‖ ≤ 1`) — and two *structurally analogous but mathematically distinct* bundled
balls (`ball_openSubgroup` in the group metric; `unitBall`/`unitClosedBall`
0-centred non-ultrametric). It does **not** have the 1-centred, arbitrary-radius,
ultrametric *ring/field* form, in either the bare-lemma or bundled-substructure
shape.

---

## PHASE 6 — Composition check (+ call-sites signal)

### Call sites — `mul_mem_expBall`

Internal use count: **3** (within `PadicLFunctions`), but **0 external to the
declaring file** — all three uses are inside `ExtLog.lean` itself:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `ExtLog.lean:76` | `exact mul_mem_expBall p ih hy`  (inside `pow_mem_expBall`, the induction step) |
| `ExtLog.lean:364` | `mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)`  (inside `extLog_mul`) |
| `ExtLog.lean:392` | `mul_mem_expBall p (pow_mem_expBall p ha m') (pow_mem_expBall p hb m)⟩`  (inside `ExtLogDomain.mul`) |

External-to-file callers: **0 distinct files** (no other file in any AINTLIB
project references `mul_mem_expBall`; the sibling principal-unit work in
FltRegularBernoulli uses a separate `Ideal.oneUnitsSubgroup` formulation).

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`mul_mem_expBall`?): **(none found)** — `pow_mem_expBall` and `ExtLogDomain.mul`
both route through `mul_mem_expBall` rather than re-deriving the ultrametric step.

Call-sites reading: K = 3 internal but file-local, with a clear dependency chain
(`mul_mem_expBall` → `pow_mem_expBall` → `extLog_mul` / `ExtLogDomain.mul`). This
is a *genuine internal building block* of the file (not dead code, not a bypassed
wrapper). The composability signal therefore does **not** by itself force NO —
the lemma earns its place *inside the project*. The verdict question is purely
whether **mathlib** should host it (or its generalisation), which Phases 3–5 + the
composition sketch below decide.

### Composition check (Phase 6)

Can `mul_mem_expBall` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the `key` inequality is the whole content):
The mathematically load-bearing step is
`‖y*z − 1‖ ≤ max ‖y−1‖ ‖z−1‖`, obtained by:
```lean
-- yz - 1 = (y-1)*z + (z-1);   ‖z‖ ≤ 1 by the ultrametric step
(IsUltrametricDist.norm_add_le_max ((y-1)*z) (z-1)).trans
  (max_le_max (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hz1) le_rfl)
```
  - Mathlib decls used: `IsUltrametricDist.norm_add_le_max`, `norm_mul`,
    `mul_le_of_le_one_right`, `max_le_max`; plus
    `IsUltrametricDist.norm_add_le_max` again (or
    `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) for `‖z‖ ≤ 1`.
  - Result: **succeeds** for the `key` inequality — this is a 2–3-mathlib-call
    composition (the `ring` rewrite `yz−1 = (y−1)z + (z−1)` is bookkeeping).
  - Notes: the *remaining* work in the lemma — wrapping `key` through the
    `^(p−1) < p⁻¹` shell of `InExpBall` (the `pow_le_pow_left₀` + `max_cases`
    `calc`) — is **entirely an artifact of the `InExpBall` predicate's
    rpow-free encoding**, not mathematical content. If the statement were the
    radius-general `‖y*z − 1‖ < r` (Phase 4b), the lemma *is* the ≤3-call
    composition above.

Attempt 2 (against the modern bundle): if mathlib had the 1-centred ultrametric
`Submonoid` (Phase 4c), this lemma would be literally `Submonoid.mul_mem` — a
0-line consequence. But that bundle is **not** in mathlib (Phase 5), so this is a
hypothetical, not an available composition today.

Conclusion: **COMPOSABLE** — from mathlib's ultrametric primitives, in ≤3 chained
calls, *for the mathematical core*. The only thing standing between "3-call
composition" and "the literal Lean statement" is the project-local `InExpBall`
wrapper (an rpow-free convenience predicate), which is itself project
infrastructure, not a mathlib concept.

---

## Verdict: `mul_mem_expBall`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the result is the textbook closure-under-multiplication of the principal-unit / higher-unit ball `1 + 𝔪ⁿ` (Serre, Neukirch, Washington §5.1, MIT 18.785) — universally treated as assumed-known infrastructure derived in 2–3 lines from the strong-triangle inequality; never a named theorem.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (4 weakening axes: ultrametric (semi)ring not normed field, drop unused algebra/completeness, arbitrary radius not `p^{−1/(p−1)}`, mul-half not bundled subgroup); Phase 4c found a real modern-idiom target (a bundled 1-centred ultrametric `Submonoid`).
- Mathlib search (Phase 5): not in mathlib in this exact form, but the **building blocks** (`IsUltrametricDist.norm_add_le_max`, `norm_mul`, `mul_le_of_le_one_right`, `max_le_max`) are all present, alongside structurally-analogous bundles (`ball_openSubgroup` in the group metric; `Subsemigroup.unitBall`/`Submonoid.unitClosedBall` 0-centred non-ultrametric).
- Composition check (Phase 6): **COMPOSABLE** — the mathematical core is a ≤3-call composition of mathlib ultrametric primitives; the extra Lean steps are pure `InExpBall`-wrapper bookkeeping.

**Rationale:**

The mathematical content of `mul_mem_expBall` — "`‖yz − 1‖ ≤ max(‖y−1‖, ‖z−1‖)`,
hence the ball around `1` is closed under multiplication" — is a two-to-three-line
consequence of mathlib's `IsUltrametricDist.norm_add_le_max` applied to the
identity `yz − 1 = (y−1)z + (z−1)`, together with `‖z‖ ≤ 1` (itself one more
ultrametric step). Every literature source (Phase 3 #1–#3, #9, #10) treats this as
folklore infrastructure, never a citable named result; the standard objects are
the higher-unit *groups* `1 + 𝔪ⁿ`, of which this is the multiplicative-closure
half at one radius. Phase 6 confirms the composition is genuine (≤3 mathlib calls
for the core), and the surplus Lean steps exist only to thread the result through
the project's rpow-free `InExpBall` predicate — a project convenience, not a
mathlib concept. So as a **standalone lemma**, `mul_mem_expBall` does not clear
mathlib's bar: it is a short composition of existing mathlib primitives, wrapped
around a project-local predicate.

There *is* a genuine mathlib gap here (Phase 4c/5): the **1-centred, ultrametric,
arbitrary-radius ball-is-a-`Submonoid`/open-`Subgroup`** of a `SeminormedRing`,
the additive-metric sibling of the existing `IsUltrametricDist.ball_openSubgroup`
(group metric) and `Submonoid.unitClosedBall` (0-centred). But that is a *separate,
larger* mathlib-infrastructure proposal — a bundled substructure with `one_mem`,
`inv_mem`, and the full `to_additive`/lattice treatment — not the act of upstreaming
*this single mul-half lemma about `InExpBall`*. Shipping the bare lemma as-is would
be the wrong grain; the correct dispositions are (a) **locally**: inline / keep it
as the small project helper it is (it has 3 honest internal call sites), and
(b) **for mathlib, optionally**: open a `feat(Analysis/Normed)` PR adding the
*bundled 1-centred ultrametric `Submonoid`/`Subgroup`*, which would then make this
lemma (and `pow_mem_expBall`, and the ball-half of `ExtLogDomain.prod`) free via
`Submonoid.mul_mem`/`pow_mem`/`prod_mem`. Because that is a generalisation +
new-bundle decision rather than a fact mathlib is simply missing, the bare-lemma
verdict is NO-composable-from-mathlib, with the bundle flagged as the real
upstreaming opportunity.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; `mul_mem_expBall`'s core is a 2–3-call
composition of them. Naming the blocks:
- `IsUltrametricDist.norm_add_le_max` (`Mathlib/Analysis/Normed/Group/Ultra.lean:47`) — the strong-triangle inequality `‖a + b‖ ≤ max ‖a‖ ‖b‖`.
- `norm_mul` (mathlib `NormedField`/`NormMulClass`) — `‖a*b‖ = ‖a‖*‖b‖`.
- `mul_le_of_le_one_right` (mathlib order) — `0 ≤ a → b ≤ 1 → a*b ≤ a`.
- `max_le_max` (`Mathlib/Order/MinMax.lean`) — monotonicity of `max`.
- for `‖z‖ ≤ 1`: a second `IsUltrametricDist.norm_add_le_max` on `z = (z−1)+1` with `norm_one`.

Mathlib building blocks: `IsUltrametricDist.norm_add_le_max`, `norm_mul`,
`mul_le_of_le_one_right`, `max_le_max`, `norm_one` (all qualified above).

Composition sketch (≤3 lines — the mathematical core; the `^(p−1)` shell is
`InExpBall`-wrapper bookkeeping that disappears if the statement is phrased as
`‖y*z − 1‖ < r`):
```lean
-- core inequality, the only real content:
example {y z : L} (hz1 : ‖z‖ ≤ 1) : ‖y * z - 1‖ ≤ max ‖y - 1‖ ‖z - 1‖ := by
  rw [show y * z - 1 = (y - 1) * z + (z - 1) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le_max (by rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) hz1) le_rfl)
```

Call sites in our project (from Phase 6.0): **K = 3**, all in `ExtLog.lean`
(`pow_mem_expBall:76`, `extLog_mul:364`, `ExtLogDomain.mul:392`).

Refactor plan:
- **Do NOT delete blindly** — unlike a typical NO-composable lemma, this one has 3
  honest internal call sites and threads the project's `InExpBall` predicate, so
  keeping it as a small *project-local* helper is reasonable (it is not mathlib
  material, but it is legitimate project infrastructure). The composition above is
  exactly its current proof.
- **If/when the mathlib bundle lands** (the real opportunity): add a bundled
  1-centred ultrametric `Submonoid`/open-`Subgroup` to
  `Mathlib/Analysis/Normed/Field/UnitBall.lean` or
  `Mathlib/Analysis/Normed/Group/Ultra.lean` (additive-metric sibling of
  `ball_openSubgroup`); then at the 3 sites replace `mul_mem_expBall p _ _` with
  `Submonoid.mul_mem _ _ _` (membership phrased as ball membership), and likewise
  collapse `pow_mem_expBall` → `Submonoid.pow_mem` and the ball-half of
  `ExtLogDomain.prod` → `Submonoid.prod_mem`. This removes ~3 hand-rolled lemmas
  in favour of generic mathlib membership API.

**Next action:** keep `mul_mem_expBall` as the small project-local helper it is
(it is a ≤3-call composition of mathlib ultrametric primitives, not a mathlib-grade
standalone result). Separately — and optionally — open a `feat(Analysis/Normed):
add ultrametric ball-around-1 `Submonoid`/open `Subgroup`` mathlib PR (the
additive-metric sibling of `IsUltrametricDist.ball_openSubgroup`), after which this
lemma and `pow_mem_expBall` become free via `Submonoid.mul_mem`/`pow_mem`. That
bundle PR — not this single lemma — is the genuine upstreaming opportunity, and is
itself a `/generalise`-style decision (radius-general + ring-general + bundled), so
run `/generalise` on the bundle proposal rather than on this lemma in isolation.

---

## Next step

Keep `mul_mem_expBall` as a project-local helper (NO-composable-from-mathlib: its
mathematical core is a ≤3-call composition of `IsUltrametricDist.norm_add_le_max`,
`norm_mul`, `mul_le_of_le_one_right`, `max_le_max`, wrapped in the project's
`InExpBall` predicate). The real mathlib opportunity is a *separate* bundled
addition — the 1-centred ultrametric ball-around-1 as a `Submonoid`/open
`Subgroup` of a `SeminormedRing` (additive-metric sibling of
`IsUltrametricDist.ball_openSubgroup`) — which would make this lemma and
`pow_mem_expBall` free; pursue that via a `feat(Analysis/Normed)` PR + `/generalise`
on the bundle, not by upstreaming this single lemma.
