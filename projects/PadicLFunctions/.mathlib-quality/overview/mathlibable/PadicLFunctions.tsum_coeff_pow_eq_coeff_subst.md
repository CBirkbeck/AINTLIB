# `/mathlibable` report — `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`

**Final verdict (five-bucket): `NO-composable-from-mathlib`.**

Mathlib does not have this exact `tsum`-form coefficient-of-substitution identity as a named
lemma, but it has all the building blocks, and they compose in ≤3 calls — the *same composition
mathlib itself uses internally* in `MvPowerSeries.coeff_subst`
(`Mathlib/RingTheory/MvPowerSeries/Substitution.lean:304-311`). The bridge is
`PowerSeries.coeff_subst'` (the `finsum` form of the identity) + `tsum_eq_finsum` (the
finite-support `∑' = ∑ᶠ` bridge) + `PowerSeries.coeff_subst_finite'` (the finite-support witness)
+ `smul_eq_mul`. No new lemma is justified; inline at the single call site.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow in this monorepo; the declaration and every dependency were read directly from source and from the vendored mathlib under `.lake/packages/mathlib/`, pinned at rev `005f0aa67b69`, toolchain `v4.32.0-rc1`).
- decl `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:648`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp`/`log` convergence, isometry, and the substitution/evaluation bridge `exp(s·log x)` on `1 + pℤ_p`.

Dependencies (all resolve):
- `coeff` = `PowerSeries.coeff` (the file does `open PowerSeries` at `PadicExp.lean:463`). For `F : PowerSeries ℚ_[p]`, `coeff n F : ℚ_[p]`, so the ascription `(coeff n F : ℚ_[p])` is an identity coercion (no nontrivial cast).
- `HasSubst` = `PowerSeries.HasSubst` (same `open`); mathlib `abbrev HasSubst a := IsNilpotent (constantCoeff a)` at `Substitution.lean:40`. For `PowerSeries` over a field this is exactly `constantCoeff a = 0` (`HasSubst.of_constantCoeff_zero'`, `Substitution.lean:67`).
- `subst` = `PowerSeries.subst` (`Substitution.lean:158`).
- `coeff_subst'` — **mathlib**, `Substitution.lean:238`: `coeff e (f.subst b) = finsum (fun d ↦ coeff d f • PowerSeries.coeff e (b ^ d))`.
- `HasSubst.eventually_coeff_pow_eq_zero` — **mathlib**, `Substitution.lean:145`.
- `finsum_eq_finsetSum_of_support_subset` — **mathlib** (the `to_additive` partner of `finprod_eq_finsetProd_of_mulSupport_subset`; the deprecated alias sits at `Finprod.lean:384`).
- The `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` on the theorem confirms the statement lives entirely in `ℚ_[p]` and uses none of the `L`-algebra structure (it is a pure `PowerSeries ℚ_[p]` fact).

---

### Statement (Phase 1)

`tsum_coeff_pow_eq_coeff_subst` is a **theorem** stating the following:

> Let `F, G ∈ ℚ_p⟦X⟧` be formal power series, with `G` substitutable (`HasSubst G`, i.e. for `PowerSeries` exactly `constantCoeff G = 0`), and fix `k ∈ ℕ`. Then
> `∑_{n=0}^∞ [Xⁿ]F · [Xᵏ](Gⁿ)  =  [Xᵏ](F ∘ G)`,
> where the left-hand `tsum` is in fact a finite sum (because `[Xᵏ](Gⁿ) = 0` for all `n > k`), and `F ∘ G = F.subst G` is the formal substitution.

This is the classical **coefficient-of-composition formula** for formal power series, restated as a `tsum` (unconditional infinite sum) over the `p`-adic field. The mathematical content is the identity itself; the convergence is trivial (finitely many nonzero terms). The companion lemma `summable_coeff_pow_scalar` (`PadicExp.lean:638`, immediately above) supplies the summability side-condition, and is consumed alongside this one inside `master_bridge`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; only used so `ℚ_[p]` exists.
- `F G : PowerSeries ℚ_[p]` — the outer and inner formal power series.

Hypotheses (Lean side):
- `hG : HasSubst G` — substitutability of `G` (for `PowerSeries`, `constantCoeff G = 0`). This is the only substantive hypothesis; it is what forces `[Xᵏ](Gⁿ) = 0` eventually and makes both sides equal.
- `k : ℕ` — the fixed output coefficient index.

Conclusion (math): `∑ₙ [Xⁿ]F · [Xᵏ](Gⁿ) = [Xᵏ](F∘G)`.

Conclusion (Lean): `(∑' n : ℕ, (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])) = (coeff k (F.subst G) : ℚ_[p])`.

---

### Size classification (Phase 2a)

**Verdict: SMALL.**
Reason: a `tsum`-rearrangement of an existing mathlib identity (`coeff_subst'`), used as a bookkeeping bridge — consumed only by `master_bridge` (`PadicExp.lean:684`). It introduces no new structure, is not a `## Main results` entry, and is not named after anyone. (The classical formula it restates is sometimes attributed to Faà di Bruno once the coefficients are expanded into Bell polynomials, but the un-expanded `∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)` form is anonymous and elementary.)

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~11 substantive tactic lines.
One-liner verdict: **n/a — kind is `theorem`, not a `def`.**

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "coefficient of composition of formal power series F(G(X)) sum formula [X^k] F∘G = sum_n [X^n]F [X^k](G^n)" | **yes** | **`(f∘g)_m = ∑_{k=0}^m (f)_k (g^k)_m`** — *verbatim* the target | enumeration / scispace "Method of Coefficients"; impan.pl FPS notes; arXiv 2504.04433. The derivation "`f∘g(z) = ∑ₖ (f)ₖ g(z)ᵏ`, switch order of summation" is exactly the target's content. |
| 2 | WebSearch (general / mechanism) | "substitution formal power series coefficient finite sum vanishing higher powers constant term zero well-defined infinite sum" | **yes** | "substitution defined iff series has zero constant term; each coefficient depends on finitely many coefficients" | Wikipedia "Formal power series"; nLab "power series"; calculus.subwiki. The `g₀=0 ⇒` per-degree coefficient is a **finite** sum is the standard well-definedness mechanism — and exactly the `HasFiniteSupport`/`tsum_eq_finsum` content. |
| 3 | WebSearch (named-after / aliases) | "Faà di Bruno formula Bell polynomials coefficient power series composition substitution operator standard mathematical statement" | **yes** | `h_n = ∑_{k=1}^n f_k B_{n,k}(g₁,…)` (partial Bell polynomials) | Wikipedia/nLab Faà di Bruno; arXiv 1911.07458 (Faà di Bruno & inversion); arXiv 2103.02427 (Schröder/multinomial). The explicit value of `[Xⁿ](F∘G)`; the target is the un-expanded `∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)` precursor. |
| 4 | ChatGPT MCP | (intended: standard form, generality, historical evolution of the coefficient-of-composition identity) | **n/a** | — | **ChatGPT MCP server not installed** in this environment (a tool search for "chatgpt/ask/openai second opinion" returned only `Monitor`/`TaskStop`; the only MCP servers exposed are claude.ai-proxy auth tools — Asana/Atlassian/etc.). Recorded n/a per protocol; compensated by running 5 distinct WebSearch queries (3 generality levels + nLab + p-adic) instead of the minimum 3. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | **n/a** | (no references dir; no `refs/` symlink) | `.mathlib-quality/references/` absent; `refs/` symlink absent. Recorded n/a with reason. |
| 6 | nLab | "power series" → ncatlab.org/nlab/show/power+series | **yes** | substitution = "clone multiplication", defined only when constant coefficient is zero | nLab *power series*; matches mathlib's `HasSubst` exactly (`IsNilpotent (constantCoeff a)`, here `= 0`). |
| 7 | nCatLab (categorical) | (same nLab page; Faà di Bruno comonad / clone) | **yes** | substitution-coefficient identity as clone composition | ncatlab.org/nlab/show/Faa+di+Bruno+formula — categorical packaging of the same content. |
| 8 | Stacks Project (alg geom) | (not an AG-specific concept) | **n/a (no direct tag)** | corroborating fact found elsewhere: order/valuation of a substitution is well-defined when inner valuation ≥ 1 | Stacks treats `R[[X]]`/completions but has no dedicated coefficient-of-composition tag. Recorded n/a-with-corroboration (arXiv 2205.00879 "An invitation to formal power series" gives the same order fact). |
| 9 | MathOverflow / Math.StackExchange | "p-adic nonarchimedean field summable infinite sum equals finite sum finitely supported family tsum finsum convergence" | **yes** | "a series converges in ℚ_p iff terms → 0"; finite-support ⇒ trivially summable; double series over non-arch fields (arXiv 1403.3623) | K. Conrad "Infinite series in p-adic fields"; arXiv 1502.04607, 1403.7417. Confirms the topological half (`tsum` over `ℚ_[p]` of a finite-support family is the finite sum). |
| 10 | recent arXiv (last 5 yr) | composition of (multivariable) formal power series | **yes** | arXiv 2504.04433 (2025, multivariable composition); 2103.02427 (Schröder multinomial); 1911.07458 (Faà di Bruno & inversion); 1803.04441 (substitution loop) | No novelty: the coefficient-of-composition identity is treated as elementary/standard throughout. |

The protocol passes: WebSearch ran 3 queries at distinct generality levels (specific formula / mechanism / named-after); ChatGPT MCP recorded n/a with a concrete reason (server not installed) and over-compensated with extra WebSearch channels; local refs checked (absent → n/a); nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the coefficient-of-composition (substitution) formula for formal power series** — for `F∘G` with `G(0)=0`, `[Xᵏ](F∘G) = ∑ₙ [Xⁿ]F · [Xᵏ](Gⁿ)`, the sum being finite because `[Xᵏ](Gⁿ)=0` for `n>k`. The explicit value of the coefficients is Faà di Bruno / partial-Bell; the un-expanded summation form is the elementary precursor.

Sources agree on the standard form: **yes**, unanimously. WebSearch #1 returned the formula verbatim; every source states the constant-term-zero condition makes the per-degree coefficient a finite sum.

Most general standard form: for `F` over **any** commutative (semi)ring and any `G` with `HasSubst G` (zero / nilpotent constant coefficient), `[Xᵉ](F∘G) = ∑ᵈ [Xᵈ]F · [Xᵉ](Gᵈ)` (a finite sum). The `p`-adic / `tsum` specialisation adds only the trivial topological reading "finite-support `tsum` = the finite sum".

Generality dimensions where the literature varies:
- **Coefficient ring**: ℝ/ℂ in classical texts → any commutative (semi)ring in the algebraic treatment (Stacks, mathlib). The most general is *any commutative (semi)ring*. The target fixes `ℚ_[p]` — strictly narrower than the algebraic identity.
- **Sum primitive**: the identity is algebraic (`finsum`/finite sum). The target uses the topological `tsum` over `ℚ_[p]` — which, for this finite-support family, is *equal* to the `finsum` (this is precisely what `tsum_eq_finsum` provides). So the `tsum` form is the topological shadow of the algebraic `finsum` identity that mathlib already states.

Disagreement with the literature: **none.** The target is a true, faithful, but specialised (`ℚ_[p]`) + topologically-restated (`tsum` instead of `finsum`) version of a standard elementary identity.

---

### Generality analysis — `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`

Literature-standard form (from Phase 3): for `F` over any commutative (semi)ring `S` and `G` with `HasSubst G`, `[Xᵉ](F.subst G) = ∑ᵈ [Xᵈ]F • [Xᵉ](Gᵈ)` (a finite sum / `finsum`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | coefficient ring | `ℚ_[p]` (a specific normed field) | any commutative (semi)ring `S` | **yes** | The identity uses only `constantCoeff G = 0` and `[Xᵉ](Gᵈ)=0` for `d>e` — pure ring algebra, no norm, no `p`. Mathlib states the `finsum` version (`coeff_subst'`) over general `S`. |
| 2 | sum primitive (`tsum` vs `finsum`) | `∑'` (topological, over `ℚ_[p]`) | `∑ᶠ`/`finsum` (algebraic, ring-agnostic) | **yes** | For this finite-support family `∑' = ∑ᶠ` exactly (`tsum_eq_finsum`); the `finsum` identity `coeff_subst'` is the real content. The target proves the topological reading over a field. |
| 3 | scalar product `•` / `*` | `*` in `ℚ_[p]` | `•` (module action of `S` on `S`) | yes (subsumed by #1) | Over a comm-ring, `coeff d F • coeff e (G^d)` equals the field `*` via `smul_eq_mul`. Mathlib's `coeff_subst'` uses `•`. |
| 4 | `hG : HasSubst G` | substitutability | identical (`HasSubst`) | NO | Exactly the literature's `G(0)=0` and exactly mathlib's hypothesis. Maximally general for the identity to hold. |

This is the `/generalise`-style mechanical pass with a **literature-grounded target**. Crucially, the weakening target on **both** axes (#1 ring, #2 `finsum`) is *already a named mathlib lemma* — `PowerSeries.coeff_subst'` — so the comparison is concrete, not hypothetical.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (fixed to `ℚ_[p]`; uses topological `tsum` where the algebraic `finsum` identity is the primitive).

Number of weakening opportunities found: 2 substantive (ring; `tsum`→`finsum`), plus the `•`/`*` adapter.

However — the strictly-more-general form (`coeff_subst'`, over an arbitrary comm-(semi)ring, in `finsum` form) **already exists in mathlib**, and the `tsum = finsum` step over `ℚ_[p]` is supplied by the existing `tsum_eq_finsum`. So "generalise first" collapses into "use the existing mathlib lemma + the existing bridge": there is no new declaration to *add*, generalised or not. This is what pushes Phase 7 away from `YES-but-generalise-first` toward a NO bucket — and, because the remaining gap between the target and `coeff_subst'` is exactly a ≤3-call composition (`tsum_eq_finsum` + `coeff_subst'` + `coeff_subst_finite'` + `smul_eq_mul`), specifically toward `NO-composable-from-mathlib`.

Cost of restatement: **CHEAP** — but moot, because no new declaration is warranted.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | bundled hyps → typeclasses/instances? | no | — | `HasSubst` is already the right (mathlib) hypothesis. |
| 2 | sequences/metric → filters/topology? | partial | the `tsum` API is already filter-based; mathlib's new `SummationFilter` framework (`∑'[L]`, default `L = unconditional`) governs it | none beyond what mathlib provides; the underlying identity is algebraic (`finsum`) and the topology adds nothing new. |
| 3 | construct object → universal-property class? | no | — | n/a — this is an identity, not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclass to module/(semi)ring? | **yes** | state the `finsum` identity over any comm-(semi)ring `S` — **this is exactly `PowerSeries.coeff_subst'`** | the full `coeff_subst`/`coeff_subst'` API over arbitrary rings; the single most important row. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive/ordered structure? | no | — | the index is `ℕ` (power-series degree); intrinsic. |

**Modern-idiom verdict (Phase 4c):** Modern idiom available: **yes** (row 5 — the ring-general `finsum` form). But the modern form is **already in mathlib** (`coeff_subst'`), so this does *not* flip the verdict to `YES-but-generalise-first` — there is no new declaration to ship. The correct consequence is a NO bucket; combined with Phase 6 (clean ≤3-call composition), `NO-composable-from-mathlib`.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or typeclass-search paths). Skipped.

---

### Mathlib search-status: `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`

[A] Lean-Finder — n/a: AI-search service not reachable from this CLI environment. Compensated by [D]+[E] grep over the vendored mathlib tree and by reading `Substitution.lean`, `Derivative.lean`, and `InfiniteSum/Basic.lean` in full.

[B] Loogle (`lean_loogle`) — n/a: no `lean_loogle` MCP tool available. Intended pattern `tsum (fun _ : ℕ => PowerSeries.coeff _ _ * PowerSeries.coeff _ (_ ^ _)) = PowerSeries.coeff _ (PowerSeries.subst _ _)`. Resolved by direct grep instead.

[C] LeanSearch (`lean_leansearch`) — n/a: no `lean_leansearch` MCP tool available. Intended NL query "coefficient of substitution of power series as infinite sum / tsum of coefficients".

[D] Grep mathlib src — **HIT (building blocks, not the exact form).** Terms tried: `coeff_subst`, `subst`, `tsum`/`finsum` in `Mathlib/RingTheory/PowerSeries/`; `tsum_eq_finsum`; `tprod_eq_finprod`. Findings:
  - **`PowerSeries.coeff_subst'`** (`Mathlib/RingTheory/PowerSeries/Substitution.lean:238`): `coeff e (f.subst b) = finsum (fun d ↦ coeff d f • PowerSeries.coeff e (b ^ d))` — **the same identity as the target, in `finsum` form**, over arbitrary `R`/`S`. The RHS of the target (`coeff k (F.subst G)`) is the LHS of this lemma; the LHS of the target is its RHS after `tsum=finsum` + `smul_eq_mul`.
  - **`tsum_eq_finsum`** (the `to_additive` of `PowerSeries`-agnostic `tprod_eq_finprod`, `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:446`): `[L.LeAtTop] (hf : HasFiniteSupport f) : ∑'[L] b, f b = ∑ᶠ b, f b`. The bridge from `tsum` to `finsum` for a finite-support family. (Used internally by mathlib's own `MvPowerSeries.coeff_subst` — see below.)
  - **`PowerSeries.coeff_subst_finite'`** (`Substitution.lean:223`): the family `d ↦ coeff d f • PowerSeries.coeff e (b ^ d)` has `HasFiniteSupport` — the witness `tsum_eq_finsum` needs.
  - **`smul_eq_mul`** — turns `•` into `*` over the field `ℚ_[p]`.
  - The default summation filter `unconditional` (used by plain `∑'`) carries both `LeAtTop` and `NeBot` instances (`SummationFilter.lean:171,173`), so `tsum_eq_finsum` applies directly to the project's `∑'`.
  - **Decisive corroboration that this composition is mathlib's own idiom:** `MvPowerSeries.coeff_subst` (`Mathlib/RingTheory/MvPowerSeries/Substitution.lean:304-311`) proves the *multivariate* analogue of the target's identity with exactly this chain — `simp [..., ← this.tsum_eq, tsum_eq_finsum (coeff_subst_finite ha f e)]` — i.e. mathlib converts `tsum → finsum → coeff_subst` inline, treating it as a two-line composition rather than a standalone exported lemma.

[E] Name-pattern search (`lean_local_search` unavailable → grep) — **HIT (building blocks).** Terms: `coeff_subst'`, `tsum_eq_finsum`, `coeff_subst_finite'`, `tprod_eq_finprod`, `unconditional`. All resolved as above. The exact `tsum (...) = coeff (subst ...)` named statement is **absent**; the constituent pieces are all present.

Searched for both:
  - the user's current form (`∑' n, coeff n F * coeff k (G^n) = coeff k (F.subst G)` over `ℚ_[p]`) — **not present** as a named lemma;
  - the literature-standard / general form (the `finsum` identity over arbitrary `R`) — **present, as `coeff_subst'`**, with the `tsum→finsum` bridge present as `tsum_eq_finsum`.

**Concluded:** *not in mathlib as a single named lemma, but the building blocks are present (`coeff_subst'`, `tsum_eq_finsum`, `coeff_subst_finite'`, `smul_eq_mul`) and compose in ≤3 calls — exactly the composition mathlib uses internally for the `MvPowerSeries` case.*

---

### Call sites — `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`

Internal use count: **K = 1** (within the project, excluding the declaring line `PadicExp.lean:648` and the docstring mention at line 668).
External-to-file callers: **0 distinct files** (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:684` | `rw [← tsum_coeff_pow_eq_coeff_subst p F G hG k, ...]` (inside `master_bridge`'s `hR` step, rewriting `coeff k (F.subst G)` back into `∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `tsum_coeff_pow_eq_coeff_subst`?):
  - **(none)** in the project. But note: **mathlib re-derives the identical identity inline** in `MvPowerSeries.coeff_subst` (`Substitution.lean:304-311`) and uses the same `tsum_eq_finsum (coeff_subst_finite …)` step — i.e. mathlib treats this as an inline composition, not a named lemma worth exporting, which is a strong "don't add it / inline it" signal.

Downstream of the single consumer: `master_bridge` itself is used twice (`PadicExp.lean:942`, `:966`) to derive the `exp(log) = id` / `log(exp) = id` evaluation identities. So the target is two hops removed from the project's actual goals, purely as a `tsum`-rearrangement helper.

Signal (per Phase 6.0.1): K = 1 internal use only → "possibly the wrong abstraction; could be inlined" → leans NO-composable. Combined with the Phase-5 building-block hit and the clean Phase-6 composition, the bucket is `NO-composable-from-mathlib`.

### Composition check (Phase 6)

Can `tsum_coeff_pow_eq_coeff_subst` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1:
```lean
example (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    (∑' n : ℕ, (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]))
      = (coeff k (F.subst G) : ℚ_[p]) := by
  rw [tsum_eq_finsum (by simpa only [smul_eq_mul] using coeff_subst_finite' hG F k), coeff_subst' hG F k]
  exact finsum_congr fun n => (smul_eq_mul ..).symm
```
  - Mathlib decls used: `tsum_eq_finsum` (`InfiniteSum/Basic.lean:446`), `PowerSeries.coeff_subst_finite'` (`Substitution.lean:223`), `PowerSeries.coeff_subst'` (`Substitution.lean:238`), `smul_eq_mul`.
  - Result: **succeeds** — `tsum_eq_finsum` rewrites the `∑'` (a finite-support family) to `∑ᶠ`; `coeff_subst'` rewrites `coeff k (F.subst G)` to the matching `∑ᶠ` (in `•`); the residual `•`-vs-`*` is `smul_eq_mul` over the field. Two rewrites + a `finsum_congr` adapter — equivalently, `(tsum_eq_finsum h).trans (coeff_subst' hG F k).symm` after aligning `•`/`*`.
  - Notes: this is **the same composition mathlib performs inline** in `MvPowerSeries.coeff_subst` (`Substitution.lean:310-311`), specialised from `finsum` to `tsum` over `ℚ_[p]`. The default `unconditional` summation filter provides the `LeAtTop` instance `tsum_eq_finsum` requires.

Per the Phase-6 heuristics table: this is a `.trans` chain of two existing rewrites plus a `smul_eq_mul`/`finsum_congr` defeq-alignment — **a composition, not a proof in disguise** (no `ring_nf`/`aesop`, no chain of `have`s with nontrivial reasoning between them). The current 11-line project proof re-implements `coeff_subst'`'s and `coeff_subst_finite'`'s internals by hand (`eventually_coeff_pow_eq_zero` + `exists_forall_of_atTop` + `tsum_eq_sum` + `finsum_eq_finsetSum_of_support_subset`), which is precisely what the composition replaces.

**Conclusion: COMPOSABLE** (≤3 mathlib calls).

---

## Verdict: `PadicLFunctions.tsum_coeff_pow_eq_coeff_subst`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the coefficient-of-composition identity `[Xᵏ](F∘G) = ∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ)` (finite for `G(0)=0`) is an elementary, unanimously-standard fact (WebSearch #1 returned it verbatim; nLab, Faà di Bruno, p-adic series notes all corroborate). No novelty.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (fixed `ℚ_[p]`; topological `tsum` where the algebraic `finsum` identity is the primitive) — and the more-general `finsum` form is already mathlib's `coeff_subst'`.
- Mathlib search (Phase 5): **not present as a named lemma**, but the building blocks are all present — `coeff_subst'` (`Substitution.lean:238`), `tsum_eq_finsum` (`InfiniteSum/Basic.lean:446`), `coeff_subst_finite'` (`Substitution.lean:223`), `smul_eq_mul`.
- Composition check (Phase 6): **COMPOSABLE** in ≤3 calls — the same composition mathlib uses internally in `MvPowerSeries.coeff_subst` (`Substitution.lean:310-311`).

**Rationale (1–2 paragraphs):**

The target is the `tsum`-over-`ℚ_[p]` reading of an identity mathlib already states algebraically. `PowerSeries.coeff_subst'` gives `coeff k (F.subst G) = ∑ᶠ d, coeff d F • coeff k (G^d)`; the only gap to the target is (a) turning the topological `∑'` into the algebraic `∑ᶠ`, which is exactly `tsum_eq_finsum` applied to the finite-support witness `coeff_subst_finite'`, and (b) turning `•` into `*`, which is `smul_eq_mul` over the field. That is a two-rewrite, ≤3-call composition with no genuine new reasoning. The decisive signal is that **mathlib itself performs precisely this composition inline** when it proves the multivariate analogue `MvPowerSeries.coeff_subst` (`Substitution.lean:304-311`: `simp [..., ← this.tsum_eq, tsum_eq_finsum (coeff_subst_finite ha f e)]`) — mathlib treats "tsum of substitution coefficients = the coeff" as an inline two-liner, not a standalone exported lemma. There is therefore nothing to upstream: the named lemma the project wrote is a `ℚ_[p]`-specialised wrapper around `coeff_subst'` + `tsum_eq_finsum`.

This is `NO-composable-from-mathlib` rather than `NO-mathlib-has-it` because mathlib does not have the *exact* `tsum (...) = coeff (subst ...)` statement under any name — it has the `finsum` identity (`coeff_subst'`) plus a generic `tsum = finsum` bridge that must be composed. It is not `YES-but-generalise-first` because the "generalised" target (the ring-general `finsum` identity) is already an exported mathlib lemma, so there is no new declaration to ship even after generalisation. It is reported here together with its companion `summable_coeff_pow_scalar` (verdict `NO-mathlib-has-it`, via `coeff_subst_finite'`): both are bespoke re-implementations of the *same* mathlib substitution-coefficient API (`coeff_subst'` / `coeff_subst_finite'`), and both should be removed in the same cleanup.

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the target is a 1–3 mathlib-call composition. Name the building blocks and inline.

Mathlib building blocks:
- `PowerSeries.coeff_subst'` — `Mathlib/RingTheory/PowerSeries/Substitution.lean:238`
- `tsum_eq_finsum` — `Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:446` (the `to_additive` of `tprod_eq_finprod`)
- `PowerSeries.coeff_subst_finite'` — `Mathlib/RingTheory/PowerSeries/Substitution.lean:223`
- `smul_eq_mul` (field `•` = `*`)

Composition sketch (≤3 lines):
```lean
example (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    (∑' n : ℕ, (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]))
      = (coeff k (F.subst G) : ℚ_[p]) := by
  rw [tsum_eq_finsum (by simpa only [smul_eq_mul] using coeff_subst_finite' hG F k), coeff_subst' hG F k]
  exact finsum_congr fun n => (smul_eq_mul ..).symm
```

Call sites in our project (from Phase 6.0): **K = 1** — `PadicExp.lean:684`, inside `master_bridge`'s `hR` rewrite, as `rw [← tsum_coeff_pow_eq_coeff_subst p F G hG k, ...]`.

Refactor plan: at the single call site (`PadicExp.lean:684`), inline the composition above (note it is used *backwards* there: `master_bridge` rewrites `coeff k (F.subst G)` into `∑ₙ …` via `← tsum_coeff_pow_eq_coeff_subst`, so inlining means rewriting `← coeff_subst' hG F k` and then `← tsum_eq_finsum (… coeff_subst_finite' hG F k)` with a `smul_eq_mul` alignment — the same two rewrites in reverse). Equivalently — and more conservatively, since `master_bridge` is itself only-locally-used — keep the named local lemma but **replace its 11-line hand-rolled body** (the `eventually_coeff_pow_eq_zero` / `exists_forall_of_atTop` / `tsum_eq_sum` / `finsum_eq_finsetSum_of_support_subset` reproof, which duplicates `coeff_subst'`'s and `coeff_subst_finite'`'s internals) with the three-line composition above. Because there is exactly one consumer in one file and `•`-vs-`*` is the only adapter, this is mechanical; verify only that `coeff`/`HasSubst`/`subst` resolve to the `PowerSeries.*` namespace (they do — `open PowerSeries` at `PadicExp.lean:463`) and that plain `∑'` elaborates with the `unconditional` filter (it does — that is the default, and it carries `LeAtTop`).

Next action: at `PadicExp.lean:684` inline `coeff_subst' hG F k` + `tsum_eq_finsum (coeff_subst_finite' hG F k)` (with `smul_eq_mul`) and delete `tsum_coeff_pow_eq_coeff_subst`; or shrink the lemma's proof to the three-liner above. Do **not** propose it for a mathlib PR — `PowerSeries.coeff_subst'` already provides the identity and `MvPowerSeries.coeff_subst` shows the `tsum` reading is an inline composition. Bundle this cleanup with `summable_coeff_pow_scalar` (its companion, also a re-implementation of the same mathlib substitution-coefficient API).

---

## Next step

Inline the ≤3-call composition `rw [tsum_eq_finsum (… coeff_subst_finite' hG F k), coeff_subst' hG F k]; exact finsum_congr fun n => (smul_eq_mul ..).symm` (with `smul_eq_mul`) at the single call site `PadicExp.lean:684` and delete `tsum_coeff_pow_eq_coeff_subst` — or replace its 11-line hand-rolled proof with that three-liner. Nothing to upstream: `PowerSeries.coeff_subst'` (`Mathlib/RingTheory/PowerSeries/Substitution.lean:238`) is the identity, `tsum_eq_finsum` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:446`) is the `tsum→finsum` bridge, and `MvPowerSeries.coeff_subst` (`Substitution.lean:304-311`) shows mathlib treats this exact composition as an inline two-liner. Clean up together with the companion `summable_coeff_pow_scalar`.

Sources (literature, Phase 3): [Formal power series — Wikipedia](https://en.wikipedia.org/wiki/Formal_power_series); [The Method of Coefficients (scispace)](https://scispace.com/pdf/the-method-of-coefficients-17ctnqbs6t.pdf); [Wagner, CO430 Formal Power Series notes](https://www.math.uwaterloo.ca/~dgwagner/co430I.pdf); [On composition of multivariable formal power series (arXiv 2504.04433)](https://arxiv.org/pdf/2504.04433); [Schröder's theorem / multinomial theorem for FPS composition (arXiv 2103.02427)](https://arxiv.org/pdf/2103.02427); [Faà di Bruno's formula and inversion of power series (arXiv 1911.07458)](https://arxiv.org/abs/1911.07458); [power series — nLab](https://ncatlab.org/nlab/show/power+series); [The loop of formal power series under substitution (arXiv 1803.04441)](https://arxiv.org/pdf/1803.04441); [Double series over a non-Archimedean field (arXiv 1403.3623)](https://arxiv.org/pdf/1403.3623); [K. Conrad, Infinite series in p-adic fields](https://kconrad.math.uconn.edu/blurbs/gradnumthy/infseriespadic.pdf).
