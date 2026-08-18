# `/mathlibable` report — `PadicLFunctions.padicLog`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)
- lake build:               build **not re-run** (stale/slow per task note); reasoned from source — target file is committed-clean, contains **0 `sorry`/`admit`**, and the surrounding API (incl. `padicLog_eq_tsum_coeff`, `padicExp_padicLog`, `padicLog_padicExp`, `norm_padicLog`) all elaborate against the def as written.
- decl `PadicLFunctions.padicLog`:   ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:384`
- kind:                      `def` (plain `noncomputable def`; **not** `@[reducible]`, sealed)
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!` on the open ball `‖x‖<p^{−1/(p−1)}` of a nonarchimedean complete normed `ℚ_[p]`-algebra field, an isometry there; `log(1+y)=∑(−1)^{n+1}yⁿ/n` converges for `‖y‖<1` and inverts `exp` on matched balls (citing Cassels §12, Washington §5.1).

---

### Statement (Phase 1)

`PadicLFunctions.padicLog` is **a definition of the `p`-adic (Iwasawa) logarithm** as a convergent power series:

> For `x` in a complete nonarchimedean normed `ℚ_[p]`-algebra field `L`,
> `log_p x := ∑_{n≥0} (−1)^n · (n+1)⁻¹ · (x−1)^{n+1} = ∑_{m≥1} (−1)^{m+1} (x−1)^m / m`,
> the standard series `log(1+y) = y − y²/2 + y³/3 − ⋯` evaluated at `y = x−1`. As a `tsum` it is **junk-total**: it returns the genuine logarithm where the family is summable and `0` (mathlib's `tsum` convention) elsewhere. The intended domain of meaning is the open unit ball `‖x−1‖ < 1`.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the prime; the scalars `(n+1)⁻¹` are taken in `ℚ_[p]`.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra (e.g. `ℚ_[p]`, finite extensions, `ℂ_[p]`).

Hypotheses (Lean side):
- none on the def itself (junk-total). The meaning lemmas (`norm_padicLog`, `padicExp_padicLog`, …) carry `InExpBall p (x−1)`, i.e. `‖x−1‖^{p−1} < p⁻¹`.

Conclusion (math): the p-adic logarithm of `x`.
Conclusion (Lean): `L` (kind is `def`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: introduces a **named mathematical object** (the p-adic logarithm function), is a primary deliverable of the file (RJW Lemma 5.14: "The p-adic exponential and logarithm"), and is a named classical analytic function (Iwasawa `log_p`) essentially guaranteed to be in the literature.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is narrative framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`∑' n : ℕ, (-1)^n * (((n:ℚ_[p])+1)⁻¹ • (x-1)^(n+1))`).
One-liner verdict: **ONE-LINER** (kind is `def`; body is a single `tsum`).

| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse                | yes      | The def is sealed (no `@[reducible]`). Downstream proofs `unfold` it explicitly via `rw [padicLog]` (e.g. `padicLog_one`, `norm_padicLog`, `padicLog_eq_tsum_coeff` at PadicExp.lean:389/424/892) and the `seriesEval`↔`padicLog` bridges in `ValuesAtOne.lean`; an exposed body would let `simp`/unification rewrite the `tsum` unpredictably. |
| Avoid typeclass diamonds         | no       | No `Mul`/`Zero`/`AddCommMonoid` instance is anchored on this def. |
| Mark semantic intent / API name  | yes      | `padicLog` is the public API name on which `ExtLog`, `ResidueZeta`, `ValuesAtOne`, `FormalPsi` all depend (≈109 references across 4 files); the multiplicativity / power / norm API is all phrased in terms of this name. |

Conclusion: **ONE-LINER WITH-EXEMPTION** — a `tsum`-bodied analytic function with a sealed body and a real API surface. The one-liner signal does **not** bias toward NO here.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic logarithm definition log_p(x)=∑(-1)^{n+1}(x-1)^n/n convergence` | yes | `log_p(1+x)=∑_{n≥1}(-1)^{n+1}xⁿ/n`, converges `\|x\|_p<1` | PlanetMath; Wikipedia "p-adic exponential function"; UMontréal Appendix 16.6; Keith Conrad notes — series is exactly the target. |
| 2 | WebSearch (general form) | `p-adic logarithm general nonarchimedean complete field Banach algebra Iwasawa log_p domain of convergence` | yes | analytic on `1+pℤ_p`; the log map `1+J → J` for ideals `J`; convergence `\|x\|_p<1` | arXiv:1907.06437, math/0512015; the multiplicative log on principal units. General nonarchimedean / Banach-algebra phrasing is standard in Iwasawa theory and non-archimedean Lie theory. |
| 3 | WebSearch (named-after / aliases) | `Iwasawa logarithm p-adic isometry exp inverse Washington cyclotomic fields chapter 5` | yes | "Iwasawa `log_p`" with `log_p(p)=0` extension; isomorphism principal units → ideal; inverse to `exp_p` | Hida UCLA Lec1; Wikipedia Ferrero–Washington; confirms the name "Iwasawa logarithm" and the exp-inverse / isometry role on matched balls. |
| 4 | ChatGPT MCP | (MCP unavailable in this environment) | n/a | — | ChatGPT MCP not configured here. **Compensated** by an extra primary-source `WebFetch` of Wikipedia (row 11) and reading the in-repo Washington/Cassels-cited docstring; the standard-form + historical-evolution question is answered by rows 1–3, 9, 11. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | n/a | (no references dir; no `refs/` symlink) | Both absent — recorded n/a per protocol. The module docstring itself cites RJW Lem 5.14, Cassels §12, Washington §5.1. |
| 6 | nLab | `p-adic exponential logarithm nonarchimedean Banach` | partial | "p-adic exp has inverse the p-adic logarithm; converges `\|x\|_p<1`; `log_p(zw)=log_p z+log_p w`" | nLab "p-adic number"; also surfaced MIT `dav/exp.pdf` "Exponential and logarithm in p-adic fields" and World Scientific "Logarithm and exponential in a p-adic field". |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; nLab entry (row 6) is the relevant one. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; the p-adic log is an analytic function on a normed field. |
| 9 | MathOverflow / Math.StackExchange | `p-adic logarithm general complete nonarchimedean field algebra convergence ball maximal generality` | yes | bounds `\|log(1+a)\|_p`; disc of convergence is the open unit ball `\|x\|_p<1` over a complete nonarchimedean field | Achinger non-arch geometry notes; Cambridge/Thorne `p-adic analysis` notes; Conrad. Confirms the maximally-general domain `‖x−1‖<1`. |
| 10 | recent arXiv (last 5 yr) | (rows 1–3, 9) | yes | "On the bases of the image of 2-adic logarithm on principal units" (arXiv:1907.06437, 2023); Ankeny–Artin–Chowla congruence papers (2024) | Active modern use; same definition and `‖·‖<1` domain. |
| 11 | Wikipedia primary fetch | `WebFetch en.wikipedia.org/wiki/P-adic_exponential_function` | yes | `log_p(1+x)=∑(-1)^{n+1}xⁿ/n`, converges `\|x−1\|_p<1`; extends to all of `ℂ_p^×` via `w=pʳ·ζ·z`; `exp_p∘log_p=id`, `log_p∘exp_p=id`; multiplicative; "Iwasawa logarithm" = the `log_p(p)=0` choice | Confirms domain, inverse relation, isometry, and the standard extension. States it over `ℂ_p` and "p-adic fields", not restricted to `ℚ_p`. |

The protocol passed: WebSearch ran 3 distinct generality levels (rows 1–3) plus arXiv (10) and a primary fetch (11); local refs checked (absent, n/a); nLab checked (6); Stacks/nCatLab/MathOverflow each adjudicated (8/7/9). ChatGPT MCP is genuinely unavailable in this sandbox — recorded n/a with the compensating primary-source fetch noted.

### Literature summary (Phase 3)

Concept identified as: the **`p`-adic logarithm** / **Iwasawa logarithm `log_p`**.
Sources agree on the standard form: **yes** — `log_p x = ∑_{n≥1} (−1)^{n+1}(x−1)ⁿ/n`, the series `log(1+y)` at `y=x−1`. This is exactly the target body (reindexed to start at `n=0`), and exactly `PowerSeries.log` evaluated at `x−1` (the repo proves this in `padicLog_eq_tsum_coeff`).
Most general standard form: the function on `{x : ‖x−1‖ < 1}` of **any complete nonarchimedean field** (ℚ_p, finite/infinite extensions, ℂ_p), with a further extension to all of `K^×` via `log_p(p)=0`; over Banach algebras the same series defines `log(1+y)` on the open unit ball.
Generality dimensions where the literature varies:
  - **Base ring**: ℚ_p ⊂ finite extensions ⊂ ℂ_p ⊂ arbitrary complete nonarchimedean field ⊂ (nonarchimedean) Banach algebra. The most general is "complete nonarchimedean field / Banach algebra"; the literature does **not** require it to be a `ℚ_[p]`-algebra specifically — only `CharZero` / a `ℚ`-algebra is needed to form the rational coefficients `1/n`.
  - **Domain**: the convergence ball is the **open unit ball `‖x−1‖<1`** (Wikipedia, Conrad, MathOverflow all agree). The exp ball `‖x−1‖<p^{−1/(p−1)}` is *strictly smaller* and is **not** the natural/standard domain of the logarithm — it is where exp and log are mutually inverse isometries.
Disagreement with the literature: the user's Lean form is correct but **narrower than standard on two axes** (base-ring assumption + meaning-domain) — see Phase 4.

---

### Generality analysis — `PadicLFunctions.padicLog`

Literature-standard form (from Phase 3): `log_p : K → K` on a **complete nonarchimedean field `K` of characteristic 0** (or a nonarchimedean `ℚ`-/`CharZero`-Banach algebra), `log_p x = ∑_{m≥1}(−1)^{m+1}(x−1)ᵐ/m`, with natural domain the open unit ball `‖x−1‖<1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` + scalars `((n:ℚ_[p])+1)⁻¹` | `L` is a normed `ℚ_[p]`-algebra; the `1/(n+1)` lives in `ℚ_[p]` and is scalar-multiplied in | `K` is a `CharZero` complete nonarchimedean field; `1/m ∈ K` directly | **yes** | The literature never asks the log's base field to be a `ℚ_[p]`-algebra — only that `1/m` makes sense (`CharZero`/`Algebra ℚ`). The `• ` through `ℚ_[p]` is an artefact of the project living over `ℚ_[p]`; the standard def writes `(x−1)ᵐ/m` with `/` in `K`. |
| 2 | `[IsUltrametricDist L]` + `[CompleteSpace L]` | complete ultrametric normed field | complete nonarchimedean field | NO | Genuinely needed: summability of the family is exactly the nonarchimedean `cofinite → 0` criterion (the proof uses `summable_iff_tendsto_cofinite_zero`). This is the right hypothesis. |
| 3 | `[NormedField L]` | a field | a field (could be a `NormedRing`/Banach algebra for the `log(1+·)` version) | yes (mild) | The classical p-adic `log_p` is on a field; the Banach-algebra `log(1+y)` generalisation exists but is a different headline object. For the "p-adic logarithm" the field form is the standard target; the algebra form is a separate, optional generalisation. |
| 4 | meaning-domain `InExpBall p (x−1)` (`‖x−1‖^{p−1}<p⁻¹`) carried by the API lemmas | exp ball `‖x−1‖<p^{−1/(p−1)}` | the open unit ball `‖x−1‖<1` | **yes** | The summand `(−1)^{m+1}(x−1)ᵐ/m` tends to `0` p-adically for the *whole* `‖x−1‖<1` (since `‖1/m‖ ≤ p^{v_p(m)}` grows only polynomially while `‖x−1‖ᵐ` decays geometrically). The def itself is junk-total so it already *evaluates* on all of `‖x−1‖<1`; what is narrower than standard is the **API**: convergence/`norm`/inverse lemmas are stated on the smaller exp ball, not on the standard log ball. (`ValuesAtOne.lean` already proves multiplicativity etc. on the full `‖z−1‖<1` ball — so the project knows the bigger ball is the right one.) |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: K = 3 (rows 1, 3, 4; row 2 is already optimal)

Proposed restatement (the literature-standard target):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- The `p`-adic (Iwasawa) logarithm `log_p x = ∑_{m≥1} (−1)^{m+1}(x−1)ᵐ/m`,
junk-total, meaningful on the open unit ball `‖x−1‖<1`. -/
noncomputable def padicLog (x : K) : K :=
  ∑' m : ℕ, (-1 : K) ^ m * ((m + 1 : K)⁻¹ * (x - 1) ^ (m + 1))
```

with the convergence / `norm` / `exp`-inverse / multiplicativity API restated on `‖x−1‖<1` (the standard domain) rather than the exp ball. Note the prime `p` is **no longer a parameter of the bare def** — the literature log is a single function; `p` only enters through the summability proof (where the residue characteristic governs `v_p(m)`), so it can be recovered as `Fact p.Prime` on the *lemmas*, or via the ambient nonarchimedean field's residue characteristic.

Cost of restatement: **MODERATE** — the def is a mechanical rewrite (`• ` over `ℚ_[p]` → `*` in `K`; drop `NormedAlgebra ℚ_[p] L`), but re-proving the summability/`norm`/inverse API on the full `‖x−1‖<1` ball (not just the exp ball) requires real work: the current `summable_padicLog_terms` proof keys off `InExpBall`, and the inverse lemmas `padicExp_padicLog`/`padicLog_padicExp` legitimately need the *exp* ball (that is where the two are mutually inverse). The honest split is: `padicLog` + its summability/`norm`/multiplicativity belong on `‖x−1‖<1`; the exp-inverse identities stay on the matched exp balls.

EXPENSIVE/MODERATE does not downgrade the verdict — it informs sequencing, not the bucket.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preamble → typeclass? | partial | already typeclass-based; the only change is `NormedAlgebra ℚ_[p] L` → `CharZero K` (row 1 of 4a) | composes with all of mathlib's `CharZero` nonarchimedean-field API rather than only `ℚ_[p]`-algebras |
| 2 | sequences/metric → filters/topological? | no | the `tsum`/`Summable` formulation is already the filter-based (`cofinite → 𝓝 0`) one — `summable_iff_tendsto_cofinite_zero` is exactly the nonarchimedean filter criterion | n/a (already idiomatic) |
| 3 | construct object → universal property class? | no | a logarithm is a constructed analytic function, not characterised by a universal property; the natural mathlib idiom *is* "evaluate the formal `PowerSeries.log`", which the repo already exposes via `padicLog_eq_tsum_coeff` | n/a |
| 4 | set-with-closure-pred → bundled substructure? | no | no substructure here | n/a |
| 5 | vector-space/field-specific → weaken to module/ring? | **yes** | the `log(1+y)` series makes sense in any `CharZero` nonarchimedean **Banach algebra**, not just a field; mathlib's `NormedSpace.exp` is exactly such a Banach-algebra-level object | a Banach-algebra `padicLog`/`log(1+·)` would pair with `NormedSpace.exp` and serve matrix/operator p-adic logs — but this is a *bigger* generalisation than "the p-adic logarithm" and is optional |
| 6 | 1-categorical → higher-categorical? | no | not categorical | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | index is ℕ (series index); intrinsic | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild — same direction as Phase 4b)**
  - Proposed mathlib-idiomatic restatement: the `CharZero` complete-nonarchimedean-field form of Phase 4b (drop the `ℚ_[p]`-algebra assumption; coefficients `1/m` in `K`). The further Banach-algebra `log(1+·)` form (row 5) is a *separate, larger* contribution that should pair with `NormedSpace.exp`, not block the field-level p-adic log.
  - Cost: CHEAP for the field-level restatement (def is mechanical); the Banach-algebra version is MODERATE–EXPENSIVE and out of scope for a first PR.
  - Mathlib downstream this enables: the field-level form composes with mathlib's general `CharZero`/nonarchimedean-field API and with `PowerSeries.log` (already the bridge); it is the missing analytic partner to `NormedSpace.exp` in the nonarchimedean regime.
  - Real mathematical improvement: removes the gratuitous `ℚ_[p]`-algebra restriction so the *one* p-adic logarithm serves ℚ_p, ℂ_p, and all complete nonarchimedean char-0 fields uniformly — and states the API on the correct (larger) convergence ball `‖x−1‖<1`.

Phase 4c reinforces Phase 4b: the right mathlib target is the `CharZero`-field form on `‖x−1‖<1`, not the `ℚ_[p]`-algebra form on the exp ball.

---

### Diamond / defeq risk — `PadicLFunctions.padicLog`

(`def`, so Phase 4.5 runs. Probes reasoned from source — build not re-run.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `padicLog` returns a bare element of `L`; it anchors no instance and is not used in any instance head. No search path is steered by it. |
| 2 | Reducibility leak | **none** | Plain `noncomputable def`, **not** `@[reducible]`. The body is a `tsum` (non-trivial); sealing it is correct and intentional (Phase 2b exemption 1). Downstream unfolds explicitly with `rw [padicLog]`. |
| 3 | Non-canonical unfolding | **low** | `rfl`/`simp` will not unfold a sealed `tsum` def spontaneously; the only `simp` lemma is `@[simp] padicLog_one` (a value lemma, safe). No surprising reduction. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | `L : Type*` and the result is `L`; no universe annotation forced; no polymorphic call-site breakage. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort`; `padicLog` is an ordinary function, not a bundled coercible type. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**
Top risks: none HIGH.
Recommended mitigations: none required. (The sealed non-reducible `tsum` def is exactly the mathlib-safe pattern.)

---

### Mathlib search-status: `PadicLFunctions.padicLog`

[A] Lean-Finder       — n/a: Lean-Finder MCP not available in this environment.
[B] Loogle            `(_ : ℚ_[_]) → ℚ_[_]` log-shaped; `∑' _, _ • (_ - 1) ^ _` — n/a: `lean_loogle` MCP not available; substituted by exhaustive source grep (D) over the actual pinned mathlib.
[C] LeanSearch        "p-adic logarithm", "logarithm power series normed field" — n/a: `lean_leansearch` MCP not available; substituted by literature channels (Phase 3) + source grep.
[D] Grep mathlib src  `def.*[Pp]adic.*(Log\|Exp)`, `padicLog`, `PadicInt\.(log\|exp)`, `Padic\.(log\|exp)`, `noncomputable def .*[Ll]og` under `Analysis/Normed/`, `expSeries`, `PowerSeries.log` — **executed in full** on `.lake/packages/mathlib/`.   **no hit** for any p-adic exp/log and **no hit** for any analytic `log` on a normed ring/algebra.
[E] Name pattern      `padicLog`, `padicExp`, `Padic.*log`, `expSeries`, `NormedSpace.exp` — only `NormedSpace.exp` (archimedean, radius ∞) and `PowerSeries.log` (formal, no evaluation) exist.

Searched for both:
  - the user's current form (`ℚ_[p]`-algebra, exp ball): **not in mathlib**.
  - the literature-standard form (complete nonarchimedean char-0 field, `‖x−1‖<1`): **not in mathlib**.

Closest existing mathlib objects (all confirmed *not* the same):
  - `NormedSpace.exp 𝕂 𝔸` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`) — the analytic exponential, but `expSeries_radius_eq_top` ⇒ radius `∞`, i.e. the **archimedean** exp; it has **no companion `log`**, and over a p-adic Banach algebra it does not converge on the relevant set. Not the p-adic exp/log.
  - `PowerSeries.log A` (`Mathlib/RingTheory/PowerSeries/Log.lean`) — the **formal** power series `∑(-1)^{n+1}/n·Xⁿ`; purely algebraic, **no convergence / no analytic evaluation**. The target precisely *evaluates* this series p-adically (`padicLog_eq_tsum_coeff`), so `PowerSeries.log` is a *building block*, not the analytic function.
  - `Real.log`, `Complex.log` — real/complex; unrelated.

Concluded: **not in mathlib** (all available methods exhausted: source grep run in full for both the user's form and the literature-standard form; semantic MCP search tools genuinely unavailable and recorded n/a). Mathlib has the *formal* `PowerSeries.log` and the *archimedean* `NormedSpace.exp`, but **no p-adic / nonarchimedean analytic logarithm or exponential of any kind**.

---

### Call sites — `PadicLFunctions.padicLog`

Internal use count: **K ≈ 109** references across **4 distinct files** (within the `PadicLFunctions` project, excluding the declaring file `PadicExp.lean`).
External-to-file callers: **4 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicLFunctions/ResidueZeta.lean` (43 refs) | `padicExp_smul_padicLog_eq_onePAdicPow`, `padicLog_prod_of_norm_lt_one`, `map_padicLog`, `seriesEval … = padicLog p (1 + …)` |
| `PadicLFunctions/ValuesAtOne.lean` (44 refs) | `padicLog_pow_p_of_norm_lt_one`, `padicLog_mul_of_norm_lt_one`, `padicLog_pow_of_norm_lt_one`, `extLog_eq_padicLog_of_norm_lt_one`, `seriesEval (formalLog K) (z-1) = padicLog p z` |
| `PadicLFunctions/ExtLog.lean` (21 refs) | `extLog x := m⁻¹ • padicLog y`, `padicLog_pow`, `extLog_eq_padicLog` — `extLog` is *built on* `padicLog` |
| `PadicLFunctions/MeasureR/FormalPsi.lean` (1 ref) | series-side of `padicLog (1 + ·)` |

Inline-derivation grep (was the equivalent re-derived without using `padicLog`?):
  - **Within `PadicLFunctions`: none** — every consumer goes through `padicLog`.
  - **Cross-project (separate def, NOT a call site of the target):** `BernoulliRegular.FLT37.PadicL.padicLog : ℚ_[p] → ℚ_[p]` (`projects/FltRegularBernoulli/.../PadicLog.lean:52`) is an **independent re-implementation** of the *same* mathematical function (`∑ (-1)^{n+1}(x−1)ⁿ/n`), specialised to `ℚ_[p]`. This is a within-repo duplication, surfaced here because it must be unified before any mathlib PR (see Phase 7 next-action).

Call-sites signal: **K ≫ 3, no inline re-derivation inside the project → real API; consumers depend on it → strong YES-* lean.** The cross-project duplicate strengthens the case that *a single, general* `padicLog` is wanted.

---

### Composition check (Phase 6)

Can `PadicLFunctions.padicLog` be derived from mathlib in ≤3 chained calls?

Attempt 1: `fun x => PowerSeries.eval₂ … (PowerSeries.log ℚ_[p]) (x-1)` — evaluate the formal log series.
  - Mathlib decls used: `PowerSeries.log`.
  - Result: **fails** — mathlib `PowerSeries` has **no p-adic / analytic evaluation map** that sums the series in a complete nonarchimedean field. `PowerSeries.log` is purely formal; turning it into a convergent `tsum` is precisely the missing content (the repo spends `summable_padicLog_terms` + `padicLog_eq_tsum_coeff` doing exactly this). Not a composition.

Attempt 2: reuse `NormedSpace.exp`/its inverse.
  - Mathlib decls used: `NormedSpace.exp`.
  - Result: **fails** — `NormedSpace.exp` is the archimedean (radius ∞) exponential and has no `log`; it is the wrong object in the nonarchimedean regime.

Attempt 3: write the `tsum` directly inline at call sites.
  - Result: this is just re-inlining the definition's body (one substantive line) at ~109 sites in 4 files — which is the opposite of composition and is precisely what a named def with a sealed body + Phase-2b API exemption exists to prevent. Not a NO-composable case.

Conclusion: **NOT-COMPOSABLE.** Mathlib's `PowerSeries.log` is a building block for the *formal* series, but the analytic summation on a complete nonarchimedean field is genuinely new content, not a 1–3 call mathlib composition.

---

## Verdict: `PadicLFunctions.padicLog`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the **p-adic / Iwasawa logarithm `log_p`**, standard form `∑_{m≥1}(−1)^{m+1}(x−1)ᵐ/m`, natural domain `‖x−1‖<1`, stated over arbitrary complete nonarchimedean char-0 fields (ℚ_p, ℂ_p, …) — the user's form is correct but narrower (carries a redundant `ℚ_[p]`-algebra assumption; API stated on the smaller exp ball).
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 weakening opportunities (drop `NormedAlgebra ℚ_[p]` for `CharZero`; coefficients `1/m` in `K`; state convergence/`norm`/multiplicativity API on the standard `‖x−1‖<1` ball). Phase 4c agrees (same direction; the `CharZero`-field form is the idiomatic target).
- Mathlib search (Phase 5): **not in mathlib** under either form; mathlib has only the *formal* `PowerSeries.log` and the *archimedean* `NormedSpace.exp` — no nonarchimedean analytic exp/log of any kind.
- Composition check (Phase 6): **NOT-COMPOSABLE** — analytic summation of the formal log series in a complete nonarchimedean field is genuinely new content.

**Rationale (1–2 paragraphs):**

The p-adic logarithm is a genuinely missing, classical, heavily-used object: mathlib has the formal series `PowerSeries.log` and the archimedean Banach-algebra `NormedSpace.exp` (radius ∞), but **nothing** that sums a logarithm series in the nonarchimedean regime. The target supplies exactly that — and the project already proves the full ecosystem around it (`norm_padicLog` isometry on the exp ball, `padicExp_padicLog`/`padicLog_padicExp` inverse identities, multiplicativity `padicLog_mul`, the `p`-power law, and the `PowerSeries.log`-evaluation bridge), with ≈109 consumers across `ResidueZeta`, `ValuesAtOne`, `ExtLog`, `FormalPsi`. That is a real API, not a wrapper. The verdict is **not** `YES-add-as-is` because Phase 4b found the form **strictly narrower than the literature standard** in two concrete, non-cosmetic ways: (1) it gratuitously assumes `[NormedAlgebra ℚ_[p] L]` and takes the rational coefficients `1/(n+1)` through `ℚ_[p]`, whereas the standard p-adic logarithm needs only a complete nonarchimedean **char-0 field** (`1/m ∈ K`) — the literature states it over ℂ_p and arbitrary such fields, never restricting to ℚ_p-algebras; and (2) its convergence/`norm`/inverse **API is phrased on the exp ball `‖x−1‖<p^{−1/(p−1)}`, strictly smaller than the logarithm's true convergence ball `‖x−1‖<1`** — and the project itself already proves the key laws on the full `‖z−1‖<1` ball in `ValuesAtOne.lean`, confirming the bigger ball is the right home. Per the skill's gate, a known weakening forces `YES-but-generalise-first`, not `YES-add-as-is`; and cost (the API re-proof on the larger ball is MODERATE) is explicitly **not** a downgrade factor.

One further blocker that the generalisation must resolve first: there is a **within-repo duplicate**, `BernoulliRegular.FLT37.PadicL.padicLog : ℚ_[p] → ℚ_[p]` — the *same* Iwasawa `log_p`, independently re-implemented over concrete `ℚ_[p]`. Before any mathlib PR these two must be unified into the single general `padicLog` (the AINTLIB cross-project dedup that `main`-cleanup exists to do). The general `CharZero`-field form proposed below subsumes both.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower than the literature-standard form — redundant `ℚ_[p]`-algebra assumption and an API stated on the exp ball rather than the standard `‖x−1‖<1` ball.
  - **MODERN-IDIOM (secondary, same direction):** Phase 4c — the `CharZero` complete-nonarchimedean-field form is the mathlib-idiomatic target and is the missing nonarchimedean partner to `NormedSpace.exp`.

  Proposed restatement:
  ```lean
  variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

  /-- The `p`-adic (Iwasawa) logarithm `log_p x = ∑_{m≥1} (−1)^{m+1}(x−1)ᵐ/m`,
  junk-total, meaningful on the open unit ball `‖x−1‖ < 1`. -/
  noncomputable def padicLog (x : K) : K :=
    ∑' m : ℕ, (-1 : K) ^ m * ((m + 1 : K)⁻¹ * (x - 1) ^ (m + 1))
  ```
  with `Summable`/`norm_padicLog`/multiplicativity API re-stated on `‖x−1‖<1`, and the exp-inverse identities kept on the matched exp balls (where they genuinely hold).

  Estimated cost of regeneralisation: **MODERATE** (def is mechanical; re-proving summability/`norm`/multiplicativity on the larger `‖x−1‖<1` ball is real but is exactly the work the project already did once in `ValuesAtOne.lean`). EXPENSIVE/MODERATE does **not** downgrade the verdict.

  Mathlib downstream this enables:
  - the single general `padicLog` serves ℚ_p, finite extensions, and ℂ_p uniformly (subsuming the duplicate `BernoulliRegular.FLT37.PadicL.padicLog`);
  - it composes with `PowerSeries.log` (the formal series it evaluates) and is the missing nonarchimedean analytic partner to `NormedSpace.exp`;
  - stating the API on `‖x−1‖<1` unblocks all multiplicativity/`p`-power lemmas (`padicLog_mul_of_norm_lt_one`, `padicLog_pow_of_norm_lt_one`) at their natural domain rather than the artificially small exp ball.

  Proposed mathlib location (post-generalisation): `Mathlib/NumberTheory/Padics/Logarithm.lean` (new), or `Mathlib/Analysis/Normed/Field/PadicLog.lean`, shipped together with the p-adic `exp` and the `InExpBall` predicate as one coherent "p-adic exp/log" PR group.

  Next action: **run `/generalise PadicLFunctions.padicLog`** (it will tension against both the literature-standard form from Phase 3 and the modern-idiom form from Phase 4c), **after** first unifying the two repo `padicLog` definitions on a `dev` branch. Then `/cleanup` the file and open the mathlib PR (grouped with `padicExp`).

---

## Next step

Run `/generalise PadicLFunctions.padicLog` to restate it over a complete nonarchimedean `CharZero` field `K` (dropping the `[NormedAlgebra ℚ_[p] L]` assumption and taking `1/m ∈ K`), with the convergence / `norm` / multiplicativity API moved onto the standard log convergence ball `‖x−1‖<1` (keeping the exp-inverse identities on the matched exp balls). First unify the within-repo duplicate `BernoulliRegular.FLT37.PadicL.padicLog` into this single general definition. Then `/cleanup` and open a mathlib PR grouping `padicExp` + `padicLog` + `InExpBall` as one coherent "p-adic exponential and logarithm" contribution.
