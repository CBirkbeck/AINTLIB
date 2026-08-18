# `/mathlibable` report — `PadicLFunctions.padicExp_add`

**Final verdict: `BORDERLINE-needs-human`.**

The mathematics of `padicExp_add` (the exponential functional equation on the
convergence ball) is *not* nonarchimedean-specific: mathlib already proves it
abstractly for any commutative Banach algebra over a characteristic-zero normed
field as `NormedSpace.exp_add_of_mem_ball`, and the project's `padicExp` is
definitionally mathlib's `NormedSpace.exp` (`exp_eq_tsum ℚ_[p]`). What is
*missing* from mathlib is the single bridge `InExpBall p x → x ∈ Metric.eball 0
(expSeries ℚ_[p] L).radius`, i.e. a lower bound `p^{-1/(p-1)} ≤ (expSeries ℚ_[p]
L).radius` on the p-adic radius — `expSeries_radius_eq_top` is archimedean-only.
Whether the right mathlib contribution is `padicExp_add` *as stated* or the
p-adic-radius lemma + a recast against `NormedSpace.exp` (after which `padicExp_add`
becomes a clean specialisation) is a judgment call. This matches the verdict on
its closest structural sibling, `summable_padicExp_terms` (also BORDERLINE for
the identical reason).

---

### Baseline (Phase 0)
- lake build:                build not re-run (stale/slow per task note); reasoned from source — all dependencies read directly.
- decl `PadicLFunctions.padicExp_add`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:270`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑ xⁿ/n!` on the open ball `‖x‖ < p^{−1/(p−1)}` of a nonarchimedean complete normed `ℚ_[p]`-algebra field, isometry there; `log(1+y)` inverts it.

---

### Statement (Phase 1)

`PadicLFunctions.padicExp_add` is a theorem stating the **exponential functional
equation on the convergence ball**: for `x, y` in the open ball
`‖·‖^{p−1} < p⁻¹` (i.e. `‖·‖ < p^{−1/(p−1)}`) of a complete ultrametric normed
`ℚ_[p]`-algebra field `L`,
`exp(x + y) = exp(x) · exp(y)`, where `exp(z) = ∑'ₙ (n!)⁻¹ · zⁿ`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `L : Type*`, `[NormedField L]` — codomain; a normed (hence commutative) field.
- `[NormedAlgebra ℚ_[p] L]` — `L` is a normed `ℚ_[p]`-algebra (gives `(n! : ℚ_[p])⁻¹ • -` meaning).
- `[IsUltrametricDist L]` — the norm is nonarchimedean (the strong triangle inequality).
- `[CompleteSpace L]` — completeness (so the defining `tsum` converges).

Hypotheses (Lean side):
- `(hx : InExpBall p x)` — `‖x‖^{p−1} < p⁻¹`, i.e. `x` is in the open convergence ball.
- `(hy : InExpBall p y)` — `‖y‖^{p−1} < p⁻¹`, i.e. `y` is in the open convergence ball.

Conclusion (math): The p-adic exponential is multiplicative on its convergence ball: `expₚ(x+y) = expₚ(x)·expₚ(y)`.

Conclusion (Lean): `padicExp p (x + y) = padicExp p x * padicExp p y`.

Proof shape: `Summable` of both series (`summable_padicExp_terms`), summability of
the product family over `ℕ × ℕ` via `HasSum.mul_of_nonarchimedean` (the
*unconditional/nonarchimedean* Cauchy product — NOT norm-summable Cauchy products),
then `tsum_mul_tsum_eq_tsum_sum_antidiagonal` + `add_pow` + the binomial
identity `(n!)⁻¹·C(n,k) = (k!)⁻¹·((n−k)!)⁻¹`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (leaning structural).
Reason: It is a named property of the `padicExp` def (the additivity/group-homomorphism
law), not itself a new structure. It *is* part of RJW Lemma 5.14, the file's main result
cluster (R5.E), so it is structurally important within the project — but as a single
declaration it is a standard property-lemma, not a new mathematical object. The
companion def `padicExp` and predicate `InExpBall` are the BIG decls; this is a lemma about them.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~30 substantive lines (double-series rearrangement + binomial identity).
One-liner verdict: **n/a — kind is `theorem`, not a `def`.** Check skipped.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential function functional equation exp(x+y)=exp(x)exp(y) convergence radius" | yes | `expₚ(z+w)=expₚ(z)expₚ(w)` for `\|z\|,\|w\| < p^{−1/(p−1)}`; radius `R=p^{−1/(p−1)}<1` | Wikipedia "P-adic exponential function", PlanetMath, Keith Conrad "Infinite series in p-adic fields" |
| 2 | WebSearch (general / radius) | "p-adic exponential radius of convergence p^{-1/(p-1)} nonarchimedean Banach algebra" | yes | radius `=(limsup\|1/n!\|_p)⁻¹ = p^{−1/(p−1)}`; nonarchimedean completion is a Banach space | Conrad notes; Robert *A Course in p-adic Analysis*; AMS Trans 333(2) |
| 3 | WebSearch (most-general form) | "exponential function topological ring exp(x+y)=exp(x)exp(y) power series identity general" | yes | additivity is the defining homomorphism property of the formal exp; holds wherever both series converge | exponential rings (PJM 113-1); general power-series additivity |
| 4 | ChatGPT MCP | (asking standard form + generality + historical evolution) | n/a | — | **ChatGPT MCP not configured in this environment** (`/setup-chatgpt` not run); recorded n/a. Compensated by 3 WebSearch tiers + nLab + Wikipedia primary-source fetch. |
| 5 | Local references | `projects/PadicLFunctions/.mathlib-quality/references/` and top-level `refs/` | n/a | (no references dir; no `refs/` symlink) | both directories absent — recorded n/a per protocol |
| 6 | nLab | "p-adic exponential map nonarchimedean" | yes | p-adic analogue of classical exp; converges on a restricted disc; inverse = p-adic log; in rigid-group / nonarchimedean-analytic-geometry settings exp of a rigid group | `ncatlab.org/nlab/show/exponential+map`, `…/p-adic+number`; confirms the abstract concept |
| 7 | nCatLab (categorical) | (same as #6) | partial | exp as map of rigid/formal groups | not a 1-categorical universal-property object; the additivity is the group-homomorphism law of the formal group `exp: 𝔾ₐ → 𝔾ₘ` on the disc |
| 8 | Stacks Project (alg geom) | — | n/a | — | not an algebraic-geometry/scheme-theoretic statement; the convergent p-adic exp lives in rigid/nonarchimedean analysis, not in the Stacks scope |
| 9 | MathOverflow / Math.SE | (covered by #1–#3 surfacing MIT 18.785 PS10, UChicago REU Strassman notes) | yes | same standard form; both args must lie in the ball | MIT 18.785 problem sets, Y. Chen REU "p-adics, Hensel, Strassman" |
| 10 | recent arXiv (last 5y) | "p-adic exponential radius / Berkovich / overconvergent" | yes (context) | radius-of-convergence of p-adic differential equations; Artin–Hasse / overconvergent variants | arXiv 2106.09315 (fast eval), 2509.26295 (p-adic Gamma), 1108.1633 — confirm the object is live & standard |

**Primary-source confirmation (Wikipedia fetch):** *"If z and w are both in the
radius of convergence for expₚ, then their sum is too and we have the usual
addition formula: expₚ(z+w) = expₚ(z)expₚ(w),"* on `|z|_p < p^{−1/(p−1)}`. This is
**verbatim the statement of `padicExp_add`**, including the both-args-in-the-ball
hypothesis.

### Literature summary (Phase 3)

Concept identified as: **the p-adic exponential function** and its **functional
equation (additivity / addition formula) on the convergence disc**.
Sources agree on the standard form: **yes** — definition `expₚ(x)=∑ xⁿ/n!`, radius
`p^{−1/(p−1)}`, additivity holds when both arguments lie in the open ball. Universal
across Wikipedia, PlanetMath, Conrad, Cassels (§12, cited in the docstring), Washington
(*Cyclotomic Fields* §5.1), Robert.
Most general standard form: **for a complete nonarchimedean field (or normed algebra
over one) of residue characteristic `p`, `expₚ(x+y)=expₚ(x)expₚ(y)` for `x,y` in the
open ball of radius `p^{−1/(p−1)}`.** Abstractly, additivity is the homomorphism law
of the formal-group exp and holds in any Banach algebra over a char-0 normed field
on the joint domain of convergence (this is the mathlib-relevant generality).
Generality dimensions where the literature varies:
  - **base field/algebra**: `ℚ_[p]` itself ⟶ any complete nonarchimedean normed field ⟶ (mathlib) any commutative Banach algebra over a char-0 normed field. The most general is the Banach-algebra form, which subsumes the p-adic one.
  - **commutativity**: in a *commutative* algebra additivity is unconditional; in noncommutative algebras it needs `Commute x y` (mathlib's `exp_add_of_commute_of_mem_ball`).
Disagreement with the literature: **none.** The Lean statement matches the standard
form exactly, including the both-args-in-ball hypothesis.

---

### Generality analysis — `PadicLFunctions.padicExp_add` (Phase 4)

Literature-standard form (from Phase 3): `expₚ(x+y)=expₚ(x)expₚ(y)` for `x,y` in the
open ball `‖·‖ < p^{−1/(p−1)}` of a complete nonarchimedean normed field/algebra;
abstractly, the Banach-algebra additivity on the joint disc of convergence.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | normed (comm.) field | complete nonarchimedean field, or (mathlib) commutative Banach algebra | partial | mathlib's `exp_add_of_mem_ball` needs only `[NormedCommRing 𝔸]+[CompleteSpace]` (no division); `exp_add_of_commute_of_mem_ball` drops commutativity for `Commute x y`. Field is a needless restriction at the *abstract* level. |
| 2 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_[p]`-algebra | char-0 normed-field algebra | partial | only used to give `(n!)⁻¹` meaning + `CharZero`; mathlib's `NormedSpace.exp` fixes the scalar field to `ℚ` and recovers any `CharZero` base via `exp_eq_tsum`. The `ℚ_[p]` choice is a specialisation. |
| 3 | `[IsUltrametricDist L]` | nonarchimedean | (abstract) **not needed** for additivity | yes | **Additivity does NOT need ultrametricity.** It holds in any commutative Banach algebra over a char-0 field. The ultrametric is needed for the *summability* of the product family via `HasSum.mul_of_nonarchimedean`, but mathlib derives the same additivity archimedean-ly via norm-summable Cauchy products. So ultrametricity is a proof convenience, not a hypothesis the statement needs. |
| 4 | `[CompleteSpace L]` | complete | complete | NO | genuinely needed: the `tsum` must converge. |
| 5 | `InExpBall p x/y` (`‖·‖^{p−1}<p⁻¹`) | bespoke concrete predicate | `x ∈ Metric.eball 0 (expSeries ℚ_[p] L).radius` | yes (idiom) | the mathlib idiom is eball-of-radius membership; `InExpBall` is a concrete characterisation of that ball. Equivalent **iff** `(expSeries ℚ_[p] L).radius = p^{−1/(p−1)}`, which mathlib cannot currently express (radius uncomputed p-adically). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (rows 1–3, 5).
Number of weakening opportunities found: K = 4 (field→comm-ring; `ℚ_[p]`→char-0 scalar;
drop `IsUltrametricDist` from the *statement*; `InExpBall`→eball idiom).

Proposed restatement (toward the mathlib-abstract form): there is *no new abstract
statement to make* — the maximally general additivity already exists in mathlib as
`NormedSpace.exp_add_of_mem_ball` / `exp_add_of_commute_of_mem_ball`. The
project-relevant restatement is to **re-aim `padicExp_add` at `NormedSpace.exp`**:

```lean
-- after a (missing) p-adic radius lemma `padic_expSeries_radius_ge`:
example {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_mem_ball
    (padic_inExpBall_mem_eball p hx) (padic_inExpBall_mem_eball p hy)
-- and `padicExp p = NormedSpace.exp` by `NormedSpace.exp_eq_tsum ℚ_[p]`.
```

Cost of restatement: **MODERATE** — the additivity itself is then one mathlib call,
but it is *gated* on a genuinely new lemma `p^{−1/(p−1)} ≤ (expSeries ℚ_[p] L).radius`
(a real radius computation mathlib lacks), plus the `padicExp = NormedSpace.exp`
identification (CHEAP, via `exp_eq_tsum`).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | already fully typeclass-based | — |
| 2 | sequences/metric → filters/topological? | no | proof already uses `Summable`/`HasSum` (filter-based) | — |
| 3 | construct an object where a universal property would characterise it? | partial | the additivity *is* the homomorphism law of the formal-group exp `𝔾ₐ→𝔾ₘ`; mathlib's `NormedSpace.exp` already packages this | re-aiming at `NormedSpace.exp` gives `exp_neg`, `isUnit_exp`, `map_exp`, the `Invertible (exp x)` instance, … for free |
| 4 | set-with-closure-predicate → bundled substructure? | no | n/a | — |
| 5 | field/metric-specific → weaken typeclass hierarchy? | **yes** | restate against `NormedSpace.exp` over a commutative Banach algebra + `x ∈ Metric.eball 0 (expSeries ℚ_[p] L).radius`; this is **the** modernisation lever | the entire `NormedSpace.exp` API (`exp_add_of_mem_ball`, `exp_neg_of_mem_ball`, `invertibleExpOfMemBall`, `map_exp_of_mem_ball`, `exp_sum_of_commute`) composes once the p-adic radius is computed |
| 6 | 1-categorical → higher/∞-categorical? | no | n/a | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → general additive structure? | no | the index is already `ℕ` for the series; the *domain* generalisation is row 5 | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes.**
  - Proposed mathlib-idiomatic restatement: recast `padicExp` as `NormedSpace.exp`
    (`exp_eq_tsum ℚ_[p]`) and `InExpBall` membership as
    `x ∈ Metric.eball 0 (expSeries ℚ_[p] L).radius`; then additivity is
    `NormedSpace.exp_add_of_mem_ball`.
  - Cost: **MODERATE** — gated on the missing radius lemma (see 4b).
  - Mathlib downstream this enables: the full `NormedSpace.exp` `_of_mem_ball` API
    (additivity, negation/inverse, `IsUnit`, ring-hom naturality, finite sums) becomes
    directly usable for the p-adic exp, eliminating the project's parallel re-derivation.
  - Real mathematical improvement: it eliminates a redundancy — `padicExp_add` is the
    `ℚ_[p]`-specialisation of an existing mathlib theorem, and the *only* genuinely new
    content is the p-adic radius lower bound (which `InExpBall` currently stands in for).

**The honesty bar:** the improvement is concrete (it makes the whole `_of_mem_ball`
family apply), not cosmetic. But it is *blocked* on a real lemma mathlib lacks, so this
is not a free mechanical win — hence the verdict is a judgment call (Phase 7), not an
automatic YES-but-generalise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equality / typeclass-search path introduced).

---

### Mathlib search-status: `PadicLFunctions.padicExp_add` (Phase 5)

[A] Lean-Finder — n/a: external service not reachable in this environment; substituted by exhaustive `grep` over the vendored `.lake/packages/mathlib` tree (decisive here, since the candidate decl is found and read directly).
[B] Loogle — n/a (external); pattern `exp (_ + _) = exp _ * exp _` is realised by the grep hits below.
[C] LeanSearch — n/a (external); the natural-language target "p-adic exponential additivity / exp of a sum on the convergence ball" — the grep over mathlib's `Analysis/Normed/Algebra/Exponential.lean` resolves it.
[D] Grep mathlib src — terms `exp_add`, `exp_add_of_mem_ball`, `exp_add_of_commute_of_mem_ball`, `expSeries`, `exp_eq_tsum`, `padic.*exp`, `mul_of_nonarchimedean`, `expSeries.*radius`, `ContinuousSMul ℚ.*Padic` — **multiple decisive hits** (see below).
[E] Name pattern — `padicExp_add` qualified name: **no** mathlib decl (mathlib has no p-adic exp at all; the only `Padic`+`exp` hits are `WithZero.exp`, the valuation exponential — unrelated).

Searched for both:
  - the user's current form (`padicExp p (x+y) = padicExp p x * padicExp p y`) — **not in mathlib** (no p-adic exp).
  - the literature-standard / abstract form — **mathlib HAS it**:
    - `NormedSpace.exp_add_of_mem_ball` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:437`) — `[NormedCommRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] [CharZero 𝕂]`, `exp (x+y) = exp x * exp y` for `x,y ∈ Metric.eball 0 (expSeries 𝕂 𝔸).radius`.
    - `NormedSpace.exp_add_of_commute_of_mem_ball` (`…:338`) — noncommutative version with `Commute x y`.
    - `NormedSpace.exp_eq_tsum` (`…:163`, `[CharZero 𝕂]`): `exp = fun x => ∑'ₙ (n!⁻¹ : 𝕂) • xⁿ` — for `𝕂 = ℚ_[p]` this is **exactly** the project's `padicExp` definition.

**Decisive negative on the bridge:** mathlib's only radius computation is
`NormedSpace.expSeries_radius_eq_top` (`…:451`), which requires `[ContinuousSMul ℚ 𝕂]`
and whose proof uses `tendsto_inv_atTop_nhds_zero_nat` — itself requiring
`[ContinuousSMul ℚ≥0 𝕜]` (`Mathlib/Analysis/SpecificLimits/Basic.lean:44`). For
`𝕂 = ℚ_[p]` the ratio `‖(n+1)⁻¹‖_p = p^{v_p(n+1)}` is **unbounded**, so neither the
hypothesis nor the conclusion can hold — and indeed **no `ContinuousSMul ℚ ℚ_[p]` /
`ContinuousSMul ℚ≥0 ℚ_[p]` instance exists in mathlib** (verified by grep, empty).
Hence `expSeries_radius_eq_top` *cannot fire* for `ℚ_[p]`, and mathlib has **no** way
to compute or lower-bound `(expSeries ℚ_[p] L).radius`. The project's `InExpBall`
(`‖x‖^{p−1} < p⁻¹`) is precisely the missing radius characterisation.

Concluded: **"found the abstract form in mathlib (`NormedSpace.exp_add_of_mem_ball`),
applicable to `ℚ_[p]`-algebras, and `padicExp = NormedSpace.exp` via `exp_eq_tsum`;
BUT the hypothesis bridge `InExpBall p x → x ∈ Metric.eball 0 (expSeries ℚ_[p] L).radius`
is NOT in mathlib (the p-adic radius is uncomputed; `expSeries_radius_eq_top` is
archimedean-only) and is not in the project either."**

---

### Call sites — `PadicLFunctions.padicExp_add` (Phase 6.0)

Internal use count: **K = 2** (within the project, excluding the declaring line 270).
External-to-file callers: **0 distinct files** (both uses are elsewhere in `PadicExp.lean`, in *different declarations*).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| PadicExp.lean:990 | `rw [show x*y = padicExp p (a+b) by rw [padicExp_add p hballa hballb, …]` — inside `padicLog_mul` (the `log(xy)=log x+log y` proof) |
| PadicExp.lean:1132 | `padicExp_add (L := ℚ_[p]) p (inExpBall_of_mem_span …) (inExpBall_of_mem_span …)` — building the `AddChar ℤ_[p] ℤ_[p]` `map_add_eq_mul'` field (the multiplicativity of `t ↦ exp(t·ℓ)`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `padicExp_add`?): **(none)** — both consumers route through `padicExp_add`; the lemma is the single source of the multiplicativity fact in the file.

**Composability signal:** K = 2 internal uses (`1 < K < 3`), no inline re-derivation,
both in genuinely different downstream constructions (the log homomorphism law and an
additive-character construction). This is real internal API — a load-bearing step in
the project's RJW Lem 5.14 cluster — but with no external-to-file or downstream-library
consumers yet, it does not by itself force a YES.

### Composition check (Phase 6)

Can `padicExp_add` be derived from mathlib in ≤3 chained calls?

Attempt 1 (direct specialisation of `exp_add_of_mem_ball`):
```lean
example {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) :
    padicExp p (x+y) = padicExp p x * padicExp p y := by
  rw [show padicExp p = NormedSpace.exp from funext fun z => by
        rw [padicExp, NormedSpace.exp_eq_tsum ℚ_[p]]]   -- bridge 1 (CHEAP, exists)
  exact NormedSpace.exp_add_of_mem_ball
        (?mem x hx) (?mem y hy)                          -- bridge 2 (MISSING)
```
  - Mathlib decls used: `NormedSpace.exp_eq_tsum`, `NormedSpace.exp_add_of_mem_ball`.
  - Result: **fails / partial** — the goal `?mem : InExpBall p x → x ∈ Metric.eball 0 (expSeries ℚ_[p] L).radius` is **unprovable from mathlib** (the p-adic radius is uncomputed; `expSeries_radius_eq_top` needs the absent `ContinuousSMul ℚ ℚ_[p]`). This bridge is itself a new lemma (`p^{−1/(p−1)} ≤ radius`), i.e. real new content, not a composition step.
  - Notes: bridge 1 is genuine and cheap; bridge 2 is the blocker.

Attempt 2 (status quo — no mathlib `exp`): the project proves additivity from first
principles via `HasSum.mul_of_nonarchimedean` + `tsum_mul_tsum_eq_tsum_sum_antidiagonal`
+ `add_pow` + the binomial identity. That is a genuine ~30-line proof, **not** a
composition.

Conclusion: **NOT-COMPOSABLE.** The abstract result exists, but specialising it to the
p-adic ball requires a new radius lemma mathlib lacks; without that, the only route is
the project's full proof. This is more than 3 mathlib calls and includes new content,
so it fails the composition heuristics.

---

## Verdict: `PadicLFunctions.padicExp_add`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): standard object, confirmed across ≥6 channels; Wikipedia gives the **verbatim** statement (additivity on the joint ball `‖·‖<p^{−1/(p−1)}`). The Lean form matches exactly.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the abstract additivity needs neither a field nor ultrametricity; mathlib's commutative-Banach-algebra form (`exp_add_of_mem_ball`) subsumes it. Modern idiom available (Phase 4c): recast against `NormedSpace.exp`, gated on a missing p-adic radius lemma.
- Mathlib search (Phase 5): the **abstract form is in mathlib** (`NormedSpace.exp_add_of_mem_ball`, applicable to `ℚ_[p]`-algebras) and `padicExp = NormedSpace.exp` via `exp_eq_tsum`; **but** the hypothesis bridge `InExpBall → eball` is absent (p-adic radius uncomputed; `expSeries_radius_eq_top` is archimedean-only — `ContinuousSMul ℚ ℚ_[p]` does not exist).
- Composition check (Phase 6): **NOT-COMPOSABLE** — bridge 2 (`p^{−1/(p−1)} ≤ radius`) is a new lemma, not a ≤3-call composition.

**Rationale:**

This decl sits exactly on the seam between three buckets, and the choice between
them is a genuine judgment call — which is what BORDERLINE is for. (i) It is *not*
plain `NO-mathlib-has-it`: although `NormedSpace.exp_add_of_mem_ball` is the abstract
theorem and `padicExp` *is* `NormedSpace.exp`, the user's form does **not** follow in
≤1 line, because the hypothesis `InExpBall p x` cannot be converted to `eball`
membership without a p-adic radius lemma mathlib lacks. (ii) It is *not* clean
`NO-composable-from-mathlib`: the missing bridge is itself new mathematical content (a
radius computation), so the "composition" is really "prove a new lemma, then compose",
which the Phase-6 heuristics explicitly reject. (iii) It is *not* a confident
`YES-add-as-is` / `YES-but-generalise-first` either: the additivity *as a theorem* is
already mathlib's, just stated more generally; the only genuinely novel piece is the
radius lower bound, and whether the project should (a) PR the radius lemma + recast
`padicExp` onto `NormedSpace.exp` (after which `padicExp_add` evaporates into a
one-liner and should NOT be PR'd separately), or (b) PR a p-adic `exp` additivity
lemma as a convenience wrapper, or (c) keep it project-local — is precisely the human
decision.

This verdict is consistent with the project's own def-first assessments, which I am
bound to respect: **`padicExp` → `NO-mathlib-has-it`** (it is `NormedSpace.exp`),
**`InExpBall` → mathlib idiom is `eball`-of-radius but the p-adic radius is
uncomputed**, and the structurally identical sibling **`summable_padicExp_terms` →
`BORDERLINE-needs-human`** for the same "abstract form exists, p-adic-radius bridge
missing, recast-vs-keep is a human call" reason. `padicExp_add` is the additivity
analogue of `summable_padicExp_terms` and inherits the same situation. (Note the
contrast with the sibling `norm_padicExp_sub_padicExp`, the *isometry*, which was
`YES-but-generalise-first`: the isometry is genuinely nonarchimedean-only and has **no**
mathlib analog, whereas additivity *does*.)

**Numbered questions (≤5):**

1. **Recast or keep?** Do you want to upstream the p-adic exponential by *recasting
   it onto mathlib's `NormedSpace.exp`* (PR the missing radius lemma
   `p^{−1/(p−1)} ≤ (expSeries ℚ_[p] L).radius`, then get additivity from
   `NormedSpace.exp_add_of_mem_ball` for free), or *keep `padicExp` as a standalone
   project def* with its own additivity lemma? (The former makes `padicExp_add` a
   one-liner that should NOT be PR'd separately.)
2. **Is the radius lemma the real target?** If recasting (Q1=recast): the genuinely
   mathlib-worthy contribution is the radius bound + a `padicExp = NormedSpace.exp`
   simp-lemma, *not* `padicExp_add` itself. Do you agree the upstreaming effort should
   be aimed there (and `padicExp_add` is then redundant)?
3. **Scope of the wrapper.** If keeping standalone (Q1=keep): should the additivity be
   stated for `ℚ_[p]`-algebra *fields* (current), or weakened to the mathlib-abstract
   commutative-Banach-algebra setting with `Commute`/`NormedCommRing` (dropping the
   needless field + ultrametric-from-statement assumptions, matching
   `exp_add_of_commute_of_mem_ball`)?
4. **Audience.** Is the p-adic `exp` development intended for downstream
   (mathlib/other-project) consumers, or is it internal scaffolding for RJW Lem 5.14
   in this project? (Currently K=2 internal, 0 external — internal-only would argue for
   keeping it project-local until the radius lemma lands.)

**Next action:** user answers Q1–Q4; then re-run `/mathlibable PadicLFunctions.padicExp_add`
(or `/generalise` if Q1=keep + Q3=weaken). Most likely resolutions:
  - Q1=recast → the verdict on `padicExp_add` collapses to **NO-composable-from-mathlib**
    (one-liner via `exp_add_of_mem_ball` once the radius lemma exists); the *radius lemma*
    becomes a fresh `YES-add-as-is` target.
  - Q1=keep + Q3=weaken → **YES-but-generalise-first** (restate against
    `NormedCommRing`/`Commute`, dropping field + statement-level ultrametricity).
  - Q4=internal-only → drop from mathlib consideration; keep project-local.

---

## Next step

User answers the four numbered questions above; then re-run
`/mathlibable PadicLFunctions.padicExp_add`. The pivotal decision is Q1
(recast onto `NormedSpace.exp` vs. keep standalone): recasting redirects the
upstreaming effort to the missing p-adic-radius lemma and makes `padicExp_add`
itself a redundant one-liner; keeping standalone points to `/generalise` for the
commutative-Banach-algebra weakening.
