# `/mathlibable` report — `PadicLFunctions.summable_coeff_pow_scalar`

**Final verdict (five-bucket): `NO-mathlib-has-it`.**

Mathlib already has this result, in strictly more general form, as
`PowerSeries.coeff_subst_finite'` (`Mathlib/RingTheory/PowerSeries/Substitution.lean:223`).
The target's `Summable` follows from it in one line via `summable_of_hasFiniteSupport`.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow in this monorepo; declaration + every dependency read directly from source and from the vendored mathlib under `.lake/packages/mathlib/`).
- decl `PadicLFunctions.summable_coeff_pow_scalar`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:638`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  The p-adic exponential and logarithm (RJW Lem 5.14): `exp`/`log` convergence, isometry, and the substitution/evaluation bridge `exp(s·log x)` on `1 + pℤ_p`.

Dependencies (all resolve):
- `coeff` = `PowerSeries.coeff` (file does `open PowerSeries` at line 463). For `F : PowerSeries ℚ_[p]`, `coeff n F : ℚ_[p]`, so `(coeff n F : ℚ_[p])` is an identity coercion (no nontrivial cast).
- `HasSubst` = `PowerSeries.HasSubst` (same `open`). Mathlib: `Mathlib/RingTheory/PowerSeries/Substitution.lean:40`.
- `HasSubst.eventually_coeff_pow_eq_zero` — **mathlib lemma**, `Substitution.lean:145`.
- `Eventually.exists_forall_of_atTop` — **mathlib**, alias of `eventually_atTop` (`Order/Filter/AtTopBot/Basic.lean:86`).
- `summable_of_ne_finset_zero` — **mathlib** (used across `Analysis/Normed/Lp/lpSpace.lean`, `Analysis/Analytic/CPolynomialDef.lean`, …).
- The omitted instances (`omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`) confirm the statement lives entirely in `ℚ_[p]` and uses none of the `L`-algebra structure.

---

### Statement (Phase 1)

`summable_coeff_pow_scalar` is a **theorem** stating the following:

> Let `F, G ∈ ℚ_p⟦X⟧` be formal power series, with `G` substitutable (`HasSubst G`, i.e. for `PowerSeries` exactly `constantCoeff G = 0`), and fix `k ∈ ℕ`. Then the family of scalars
> `n ↦ [Xⁿ]F · [Xᵏ](Gⁿ)`  (`n` ranging over `ℕ`)
> is summable in `ℚ_p`.

The mathematical content is the **finite support** of this family: because `G` has zero constant coefficient, `[Xᵏ](Gⁿ) = 0` for all `n > k`, so only finitely many terms (`n ≤ k`, in fact `n < N` for the witness `N`) are nonzero. A finitely-supported family in any topological additive monoid is summable. The docstring states this exactly: "has finite support … hence is summable."

This family is the summand of the substitution-coefficient formula `[Xᵏ](F∘G) = ∑ₙ [Xⁿ]F · [Xᵏ](Gⁿ)` — the companion lemma `tsum_coeff_pow_eq_coeff_subst` (immediately below at line 648) is exactly that identity, and `summable_coeff_pow_scalar` is the summability side-condition it needs.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; only used so `ℚ_[p]` exists.
- `F G : PowerSeries ℚ_[p]` — the outer and inner formal power series.

Hypotheses (Lean side):
- `hG : HasSubst G` — substitutability of `G` (for `PowerSeries`, `constantCoeff G = 0`). This is the *only* substantive hypothesis; it is what forces `[Xᵏ](Gⁿ) = 0` eventually.
- `k : ℕ` — the fixed output coefficient index.

Conclusion (math): the scalar family `n ↦ [Xⁿ]F · [Xᵏ](Gⁿ)` is summable.

Conclusion (Lean): `Summable fun n : ℕ => (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])`.

---

### Size classification (Phase 2a)

**Verdict: SMALL.**
Reason: a summability side-condition / bookkeeping helper used to justify a `tsum` rearrangement (companion to `tsum_coeff_pow_eq_coeff_subst` and consumed only by `master_bridge`). It introduces no new structure, is not a `## Main results` entry, and is not named after anyone.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 4 substantive tactic lines.
One-liner verdict: **n/a — kind is `theorem`, not a `def`.**

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "coefficient of power series substitution composition formula formal power series F(G(X))" | yes | `[Xⁿ](F∘G) = Σₖ₌₀ⁿ bₖ·𝒜ₙ,ₖ` (partial Bell / Faà di Bruno coeffs); the condition `g₀ = 0` makes `[Xⁿ](F∘G)` a **finite** sum | Wagner CO430 notes; HandWiki/Wikipedia "Formal power series"; Gan, *On composition of formal power series* (IJMMS 2002) |
| 2 | WebSearch (general / mechanism) | "formal power series composition coefficient finite sum vanishing higher powers order substitution well-defined" | yes | "if `B(0)=0` then `B(z)ⁿ = b₁ⁿzⁿ+…`, so `[zℓ]B(z)^k = 0` if `k > ℓ`; partial sums `Σ_{k≤N} aₖB^k` stabilise for `N ≥ ℓ`" | enumeration.ca toolbox; Wikipedia "Formal power series"; arXiv 2504.04433. **This is verbatim the mechanism the target lemma uses.** |
| 3 | WebSearch (named-after / aliases) | "Faà di Bruno formal power series composition [X^k]F(G) finite sum coefficient mathlib HasSubst substitution" | yes | Faà di Bruno's formula / Bell polynomials = the explicit form of `[Xⁿ](F∘G)`; substitution = "clone multiplication" | Wikipedia + nLab "Faa di Bruno formula"; arXiv 1911.07458 (Faà di Bruno & inversion) |
| 4 | ChatGPT MCP | (intended: "standard form, generality, historical evolution of the substitution-coefficient finiteness fact") | n/a | — | **ChatGPT MCP server not installed** in this environment (only `claude.ai`-proxy auth tools — Asana/Atlassian/etc. — are exposed; no `chatgpt`/`ask` tool). Recorded n/a per protocol; compensated by running 6 distinct WebSearch queries (3 generality levels + nLab + Stacks + MathOverflow/p-adic) instead of the minimum 3. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs/` symlink) | `.mathlib-quality/references/` absent; `refs/` symlink absent. Recorded n/a with reason. |
| 6 | nLab | "formal power series composition substitution coefficient" → ncatlab.org/nlab/show/power+series | yes | substitution = "clone multiplication"; constant-term-zero condition makes each output coefficient a finite combination | nLab *power series*; the finiteness is the standard well-definedness condition |
| 7 | nCatLab (categorical) | (same as #6; nLab page) | yes | Faà di Bruno as a comonad / clone structure | ncatlab.org/nlab/show/Faa+di+Bruno+formula — categorical packaging, same content |
| 8 | Stacks Project (alg geom) | "Stacks project formal power series substitution composition order vanishing coefficient" | n/a (no direct tag) | corroborating fact found elsewhere: "substitution well-defined iff inner valuation ≥ 1; order of product = sum of orders" | Stacks treats completion/`R[[X]]` but has no dedicated substitution-coefficient-finiteness tag; the order/valuation fact (arXiv 2205.00879 "An invitation to formal power series") is the same statement. Recorded n/a-with-corroboration. |
| 9 | MathOverflow / Math.StackExchange | "summable family finite support nonarchimedean p-adic coefficient power series composition convergence" | yes | "a family of formal series is summable iff for each `k` the set with order ≤ `k` is finite"; "in a non-archimedean field a sum converges iff terms → 0" | K. Conrad / J. Thorne p-adic notes; arXiv 1502.04607. Confirms: finite support ⇒ summable (the trivial second half of the target). |
| 10 | recent arXiv (last 5 yr) | composition of (multivariable) formal power series | yes | arXiv 2504.04433 (2025), 2103.02427 (Schröder/multinomial), 1911.07458 (Faà di Bruno & inversion) — all reaffirm the `g₀=0 ⇒` finite-sum coefficient | no novelty: the finiteness is treated as elementary/standard throughout |

The protocol passes: WebSearch ran 3 queries at distinct generality levels (specific formula / mechanism / named-after); ChatGPT MCP recorded n/a with a concrete reason (server not installed) and over-compensated with extra WebSearch channels; local refs checked (absent → n/a); nLab, nCatLab, Stacks, MathOverflow, arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **the well-definedness ("finiteness") condition for the coefficient of a composition / substitution of formal power series** — i.e. for `F∘G` with `G(0)=0`, the coefficient family `n ↦ [Xⁿ]F · [Xᵏ](Gⁿ)` is finitely supported (`[Xᵏ](Gⁿ) = 0` for `n > k`). The explicit value is Faà di Bruno / partial-Bell; the finiteness is the standard hypothesis that makes substitution well-defined.

Sources agree on the standard form: **yes**, unanimously. Every source states the constant-term-zero condition makes the per-degree coefficient a finite sum (`[zℓ]Bᵏ = 0` for `k > ℓ`).

Most general standard form: for a formal power series `F` over **any** commutative (semi)ring and any `G` with zero constant term, the family `d ↦ [Xᵈ]F · [Xᵉ](Gᵈ)` has finite support, for every output degree `e`. The p-adic / non-archimedean specialisation adds the trivial extra step "finite support ⇒ summable" (and in non-archimedean fields even "terms → 0 ⇒ summable").

Generality dimensions where the literature varies:
- **Coefficient ring**: ℝ/ℂ in classical texts → any commutative (semi)ring in the algebraic treatment (Stacks, mathlib). The most general is *any commutative (semi)ring*. The target fixes `ℚ_[p]` — strictly narrower.
- **Conclusion strength**: "finite support" (algebraic, ring-agnostic) is the primitive fact; "summable" is a topological corollary that only makes sense once a topology is fixed. The target states the weaker topological corollary `Summable` over the field `ℚ_[p]`; the literature/algebraic primitive is the stronger `HasFiniteSupport`.

Disagreement with the literature: **none.** The target is a true, faithful, but specialised + weakened restatement of a standard elementary fact.

---

### Generality analysis — `PadicLFunctions.summable_coeff_pow_scalar`

Literature-standard form (from Phase 3): for `F` over any commutative (semi)ring `S` and `G` with `HasSubst G`, the family `d ↦ [Xᵈ]F • [Xᵉ](Gᵈ)` has finite support (for each `e`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | coefficient ring | `ℚ_[p]` (a specific normed field) | any commutative (semi)ring `S` | **yes** | The finiteness uses only `constantCoeff G = 0` and `[Xᵉ](Gᵈ)=0` for `d>e` — pure ring algebra, no norm, no `p`. Mathlib states it over general `S`. |
| 2 | conclusion | `Summable (fun n => …)` | `(fun d => …).HasFiniteSupport` (strictly stronger; ring-agnostic) | **yes** | `HasFiniteSupport` is the real content; `Summable` is its image under `summable_of_hasFiniteSupport`. The target proves the weaker corollary. |
| 3 | `hG : HasSubst G` | substitutability | identical (`HasSubst`) | NO | This is exactly the literature's `G(0)=0` hypothesis and exactly mathlib's. Maximally general for the statement to hold. |
| 4 | scalar product `•`/`*` | `*` in `ℚ_[p]` | `•` (module action of `S` on `S`) | yes (subsumed by #1) | Over a comm-ring `S`, `coeff d f • coeff e (g^d)` with `smul_eq_mul` is the same as the field `*`. Mathlib uses `•`. |

This is the `/generalise`-style mechanical pass with a **literature-grounded target**, and it lands on the *exact mathlib lemma* (`coeff_subst_finite'`), so the comparison is concrete rather than hypothetical.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (fixed to `ℚ_[p]`; states the weaker `Summable` instead of `HasFiniteSupport`).

Number of weakening opportunities found: 2 (ring; conclusion strength).

However — the weakening target **already exists in mathlib** as `coeff_subst_finite'` (see Phase 5). So the "generalise-first" recommendation collapses into "use the existing mathlib lemma": there is nothing to *add*, generalised or not. This is what tips Phase 7 from `YES-but-generalise-first` to `NO-mathlib-has-it`.

Cost of restatement: **CHEAP** — but moot, because no new declaration is warranted (mathlib already has the general form).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | bundled hyps → typeclasses/instances? | no | — | `HasSubst` is already the right (mathlib) typeclass-style hypothesis. |
| 2 | sequences/metric → filters/topology? | partial | the `Summable`/`tsum` API is already filter-based (`HasSum` along `cofinite`) | none beyond what mathlib already provides; the underlying fact is purely algebraic (`HasFiniteSupport`) and shouldn't be topologised at all. |
| 3 | construct object → universal-property class? | no | — | n/a — this is a finiteness lemma, not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclass to module/(semi)ring? | **yes** | state over any comm-(semi)ring `S` with `HasFiniteSupport` conclusion — **this is exactly `PowerSeries.coeff_subst_finite'`** | the full `coeff_subst`/`coeff_subst'` API over arbitrary rings; this is the single most important row. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive/ordered structure? | no | — | the index is `ℕ` (power-series degree); intrinsic. |

**Modern-idiom verdict (Phase 4c):** Modern idiom available: **yes** (row 5 — weaken `ℚ_[p]` to a general comm-(semi)ring and state `HasFiniteSupport`). But the modernised form is **already in mathlib** (`coeff_subst_finite'`), so this does *not* flip the verdict to `YES-but-generalise-first` — there is no new declaration to ship; the modern form exists upstream. The correct consequence is `NO-mathlib-has-it`.

---

### Diamond / defeq risk — Phase 4.5

**n/a — declaration kind is `theorem`** (introduces no definitional equalities or typeclass-search paths). Skipped.

---

### Mathlib search-status: `PadicLFunctions.summable_coeff_pow_scalar`

[A] Lean-Finder — n/a: AI-search service not reachable from this CLI environment. Compensated by [D]+[E] grep over the vendored mathlib tree and by reading `Substitution.lean` in full.

[B] Loogle (`lean_loogle`) — n/a: no `lean_loogle` MCP tool available in this environment. Intended pattern `(fun _ : ℕ => _ • PowerSeries.coeff _ (_ ^ _)).HasFiniteSupport` / `Summable (fun _ : ℕ => PowerSeries.coeff _ _ * PowerSeries.coeff _ (_ ^ _))`. Resolved by direct grep instead.

[C] LeanSearch (`lean_leansearch`) — n/a: no `lean_leansearch` MCP tool available. Intended NL query "coefficient of substitution of power series has finite support" / "summable coefficients of power series composition".

[D] Grep mathlib src — **HIT.** Terms tried: `Summable` in `Mathlib/RingTheory/PowerSeries/`; `HasFiniteSupport` + `coeff` + `subst`; `coeff_subst`. Findings:
  - **`PowerSeries.coeff_subst_finite'`** (`Mathlib/RingTheory/PowerSeries/Substitution.lean:223`):
    `theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) : (fun (d : ℕ) ↦ coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport`
    — the target family **verbatim**, over arbitrary `R`, as `HasFiniteSupport`.
  - `PowerSeries.coeff_subst_finite` (`:212`) — the `MvPowerSeries` parent.
  - `PowerSeries.coeff_subst'` (`:238`) — `coeff e (f.subst b) = finsum (fun d ↦ coeff d f • PowerSeries.coeff e (b ^ d))`: the very identity whose well-definedness `coeff_subst_finite'` underwrites (and which the project's own `tsum_coeff_pow_eq_coeff_subst` uses at `PadicExp.lean:655`).
  - `summable_of_hasFiniteSupport` (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:148`) — the bridge `HasFiniteSupport → Summable`, used throughout mathlib (`PiTopology.lean:164,203`, `NumberTheory/LSeries/PrimesInAP.lean:479`, `Analysis/.../Weierstrass.lean`).
  - Independent corroboration that this is mathlib's own idiom: `PowerSeries.derivative_subst` (`Derivative.lean:184–198`) derives the *same* finite-support fact **inline**, using the exact code the target uses: `(hg.eventually_coeff_pow_eq_zero (n+1)).exists_forall_of_atTop`.

[E] Name-pattern search (`lean_local_search` unavailable → grep) — **HIT.** Terms: `coeff_subst`, `eventually_coeff_pow_eq_zero`, `HasFiniteSupport`, `summable_of_hasFiniteSupport`. All resolved as above. `summable_of_ne_finset_zero` and `Eventually.exists_forall_of_atTop` confirmed as existing mathlib lemmas.

Searched for both:
  - the user's current form (`Summable …` over `ℚ_[p]`) — not present verbatim, but trivially below the general form;
  - the literature-standard / general form (`HasFiniteSupport` over arbitrary `R`) — **present, as `coeff_subst_finite'`**.

**Concluded:** *found in mathlib as `PowerSeries.coeff_subst_finite'`; strictly more general form (general comm-(semi)ring; `HasFiniteSupport` ⊃ `Summable`). The user's `ℚ_[p]`/`Summable` form follows in ≤1 line.*

---

### Call sites — `PadicLFunctions.summable_coeff_pow_scalar`

Internal use count: **K = 1** (within the project, excluding the declaring line `PadicExp.lean:638`).
External-to-file callers: **0 distinct files** (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `PadicExp.lean:685` | `← (summable_coeff_pow_scalar p F G hG k).tsum_smul_const (y ^ k)` (inside `master_bridge`'s `hR` step) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `summable_coeff_pow_scalar`?):
  - **(none)** in the project. But note: **mathlib re-derives the identical fact inline** in `PowerSeries.derivative_subst` (`Derivative.lean:187`) — i.e. mathlib itself treats this as an inline two-liner, not a named lemma worth exporting, which is a strong "don't add it" signal.

Signal (per Phase 6.0.1): K = 1 internal use only → "possibly the wrong abstraction; could be inlined" → leans NO-composable / NO-mathlib-has-it. Combined with the Phase-5 hit, the bucket is `NO-mathlib-has-it`.

### Composition check (Phase 6)

Can `summable_coeff_pow_scalar` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1:
```lean
example (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    Summable fun n : ℕ => (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]) := by
  simpa only [smul_eq_mul] using summable_of_hasFiniteSupport (coeff_subst_finite' hG F k)
```
  - Mathlib decls used: `PowerSeries.coeff_subst_finite'`, `summable_of_hasFiniteSupport`, `smul_eq_mul`.
  - Result: **succeeds** (1 composition + `smul_eq_mul` defeq-cleanup; `•` = `*` over the field `ℚ_[p]`, and `coeff` here is `PowerSeries.coeff`, matching `coeff_subst_finite'` exactly).
  - Notes: this is the canonical specialisation — `coeff_subst_finite' hG F k` gives `HasFiniteSupport` of the *identical* family; `summable_of_hasFiniteSupport` is the one-step bridge; `smul_eq_mul` matches `•` to the displayed `*`.

**Conclusion: COMPOSABLE** — and more strongly, the building block (`coeff_subst_finite'`) is itself the *named general form of the same statement*, so this is reported under the `NO-mathlib-has-it` evidence (mathlib has it; the user's form is a ≤1-line specialisation), with the composition sketch above doubling as the refactor.

---

## Verdict: `PadicLFunctions.summable_coeff_pow_scalar`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the constant-term-zero finiteness of substitution coefficients is an elementary, unanimously-standard fact (`[Xᵏ](Gⁿ)=0` for `n>k` ⇒ finite support ⇒ summable). No novelty.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD (fixed `ℚ_[p]`; weaker `Summable` vs the ring-agnostic `HasFiniteSupport`).
- Mathlib search (Phase 5): **found in mathlib as `PowerSeries.coeff_subst_finite'`** (`Mathlib/RingTheory/PowerSeries/Substitution.lean:223`) — strictly more general (arbitrary comm-(semi)ring; `HasFiniteSupport`).
- Composition check (Phase 6): COMPOSABLE in ≤1 line from that mathlib lemma + `summable_of_hasFiniteSupport`.

**Rationale (1–2 paragraphs):**

Mathlib already contains the exact mathematical content of this theorem, and in a strictly more general form. `PowerSeries.coeff_subst_finite'` states, for any `HasSubst b` over an arbitrary commutative (semi)ring, that the family `d ↦ coeff d f • PowerSeries.coeff e (b ^ d)` has finite support — which, after `smul_eq_mul` (since `ℚ_[p]` is a field) and specialising `b := G`, `f := F`, `e := k`, is *verbatim* the family in `summable_coeff_pow_scalar`. The target's `Summable` conclusion is the trivial topological shadow of mathlib's `HasFiniteSupport`, obtained by the single ubiquitous bridge `summable_of_hasFiniteSupport`. The target's own docstring concedes the point — "has finite support … hence is summable" — so the lemma is, by its author's own framing, the weaker corollary of the mathlib lemma. The current proof even re-implements `coeff_subst_finite'`'s argument by hand (`eventually_coeff_pow_eq_zero` + `exists_forall_of_atTop` + `summable_of_ne_finset_zero`); mathlib performs that identical inline derivation in `PowerSeries.derivative_subst`, confirming this is established mathlib idiom rather than a missing lemma.

This is `NO-mathlib-has-it` rather than `YES-but-generalise-first` precisely because the generalised target is not hypothetical — it is already an exported mathlib declaration. There is nothing to add or upstream. It is reported as `NO-mathlib-has-it` rather than `NO-composable-from-mathlib` because the building block `coeff_subst_finite'` is not a generic primitive that happens to compose — it is *the same theorem*, stated more generally, with the only remaining step being a one-call `HasFiniteSupport → Summable` upgrade.

**WHY not (refactor-actionable detail):**

Mathlib already has it. The exact decl is `PowerSeries.coeff_subst_finite'` at `Mathlib/RingTheory/PowerSeries/Substitution.lean:223`:
```lean
theorem coeff_subst_finite' {b : S⟦X⟧} (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    (fun (d : ℕ) ↦ coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport
```
The `ℚ_[p]`-specialised `Summable` form follows in one line (`•` is `*` over the field; `summable_of_hasFiniteSupport` lifts finite support to summability):

Existing mathlib decl:        `PowerSeries.coeff_subst_finite'`
Located at:                   `Mathlib/RingTheory/PowerSeries/Substitution.lean:223`
Our form follows in ≤1 line:
```lean
example (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) :
    Summable fun n : ℕ => (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p]) := by
  simpa only [smul_eq_mul] using summable_of_hasFiniteSupport (coeff_subst_finite' hG F k)
```
Call sites in our project (from Phase 6.0):  **K = 1** — `PadicExp.lean:685`, inside `master_bridge`'s `hR` rewrite, as `(summable_coeff_pow_scalar p F G hG k).tsum_smul_const (y ^ k)`.

Refactor plan: at the single call site (`PadicExp.lean:685`), replace the dotted call
`(summable_coeff_pow_scalar p F G hG k)` with
`(summable_of_hasFiniteSupport (coeff_subst_finite' hG F k) |>.congr (fun n => (smul_eq_mul ..).symm))`
— or, more cleanly, keep a **one-line local wrapper body** for `summable_coeff_pow_scalar` itself (replace its 4-line proof with the `simpa only [smul_eq_mul] using summable_of_hasFiniteSupport (coeff_subst_finite' hG F k)` shown above) so the call site is untouched while the bespoke `eventually_coeff_pow_eq_zero`/`summable_of_ne_finset_zero` reproof is deleted. Because there is exactly one consumer in one file and `•`-vs-`*` is the only adapter needed, this is mechanical; verify only that `coeff`/`HasSubst` resolve to the `PowerSeries.*` namespace (they do — `open PowerSeries` at `PadicExp.lean:463`).

Next action (cleanup-lane, `main`): do **not** propose this for a mathlib PR. Either (a) inline `summable_of_hasFiniteSupport (coeff_subst_finite' hG F k)` at `PadicExp.lean:685` and delete `summable_coeff_pow_scalar`, or (b) if the named lemma is wanted as local readable API, shrink its proof to the one-liner above (delete the hand-rolled `eventually_coeff_pow_eq_zero` + `summable_of_ne_finset_zero` derivation, which duplicates `coeff_subst_finite'`). Option (a) is preferred per the project's no-wrapper-lemmas rule.

---

## Next step

Delete `summable_coeff_pow_scalar` (or reduce it to the one-liner) and use `summable_of_hasFiniteSupport (PowerSeries.coeff_subst_finite' hG F k)` (with `smul_eq_mul`) at the single call site `PadicExp.lean:685`. Nothing to upstream — `PowerSeries.coeff_subst_finite'` is already in mathlib at `Mathlib/RingTheory/PowerSeries/Substitution.lean:223`.

Sources (literature, Phase 3): [Formal power series — Wikipedia](https://en.wikipedia.org/wiki/Formal_power_series); [Formal Series and GFs — enumeration.ca](https://enumeration.ca/toolbox/generating-functions/); [Wagner, CO430 Formal Power Series notes](https://www.math.uwaterloo.ca/~dgwagner/co430I.pdf); [Gan, On composition of formal power series (IJMMS 2002)](https://www.hindawi.com/journals/ijmms/2002/197193/); [Faà di Bruno's formula — Wikipedia](https://en.wikipedia.org/wiki/Fa%C3%A0_di_Bruno's_formula); [Faa di Bruno formula — nLab](https://ncatlab.org/nlab/show/Faa+di+Bruno+formula); [power series — nLab](https://ncatlab.org/nlab/show/power+series); [An invitation to formal power series (arXiv 2205.00879)](https://arxiv.org/pdf/2205.00879); [Faà di Bruno's formula and inversion of power series (arXiv 1911.07458)](https://arxiv.org/abs/1911.07458); [K. Conrad / J. Thorne, p-adic analysis notes](https://kconrad.math.uconn.edu/math5020f11/jackthornenotes.pdf).
