## /mathlibable report — `Chebotarev.contDiff_expMapBasis`

### Baseline (Phase 0)
- lake build:               ⚠ not run (environment build is stale; per the task brief, reasoned from source — the decl elaborates as part of the green `main` tree)
- decl `Chebotarev.contDiff_expMapBasis`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:126`
- qualified name:           `Chebotarev.contDiff_expMapBasis` (file opens `namespace Chebotarev` at line 79; parser-supplied `Chebotarev.contDiff_expMapBasis` is CORRECT)
- kind:                     theorem
- has sorry:                no
- module docstring summary: Lipschitz parametrization of the frontier of `normLeOne K` — the Gun–Ramaré–Sivaraman boundary-cell input for the effective lattice-point count. This is a `ForMathlib/` helper file.

### Statement (Phase 1)

`Chebotarev.contDiff_expMapBasis` asserts that the underlying function of mathlib's
`NumberField.mixedEmbedding.fundamentalCone.expMapBasis` (an `OpenPartialHomeomorph (realSpace K) (realSpace K)`)
is continuously differentiable of order 1 (`C¹`) as a map `realSpace K → realSpace K`.

Concretely, `expMapBasis x = exp(x w₀) · (w ↦ ∏_{i ≠ w₀} w(η_i)^{x_i})`, where the `η_i = fundSystem K (equivFinRank.symm i)`
are the fundamental units and `w(η_i) > 0` are their images at the infinite place `w`
(`expMapBasis_apply'`). The theorem says this map is `C¹` on all of `realSpace K`.

Variables / typeclasses (Lean side):
- `K : Type*`, `[Field K]`, `[NumberField K]` — a number field. Required: `expMapBasis` is only defined for number fields (it is built from `fundSystem`, `regulator`, `InfinitePlace`).

Hypotheses: none.

Conclusion (math): `expMapBasis : realSpace K → realSpace K` is `C¹` (indeed `C^∞`, but only `C¹` is asserted/needed).
Conclusion (Lean): `ContDiff ℝ 1 (⇑(expMapBasis (K := K)))`.

Proof (3 lines): rewrite `⇑expMapBasis` to the explicit formula via `funext expMapBasis_apply'`,
then `fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')`. The discharger
supplies the `rpow` side-condition "base ≠ 0" (the place value `w(η_i)` is positive, hence nonzero).

### Size classification (Phase 2a)

Verdict: SMALL
Reason: A regularity helper lemma (`ContDiff` of an existing mathlib map). Not a named theorem, not a
new structure, not a project main result. It is plumbing that feeds `contDiff_faceMapZero` /
`contDiff_faceMapSide`, which in turn feed the Lipschitz cover. (Note: literature width is EXHAUSTIVE
regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. The one-liner negative signal does not apply
to lemmas. (The proof is a 3-line tactic block, not a one-line definition body.)

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | smoothness of `x ↦ exp(x)·∏|η_i|^{x_i}` number field NormLeOne mixed embedding Gun–Ramaré–Sivaraman    | no   | —                                | The map `expMapBasis` is a mathlib-internal object specific to the `NormLeOne` fundamental-cone proof; not a named classical concept. Returned only unrelated analytic NT papers. |
|  2 | WebSearch (general form)         | mathlib NumberField mixedEmbedding expMapBasis NormLeOne                                                | yes  | (mathlib docs)                   | Confirms `expMapBasis`/`expMap` are defined only in `Mathlib/.../CanonicalEmbedding/NormLeOne.lean`; no `ContDiff` lemma surfaced in the docs. |
|  3 | WebSearch (named-after/aliases)  | (covered by #1: "expMap" / "exp map basis" + Lipschitz boundary) — no classical alias exists           | n/a  | —                                | This is not a named operator; the underlying smoothness fact ("a finite product of real powers of positive smooth functions times an exponential is `C^∞`") is a routine calculus fact, not a citable theorem. |
|  4 | ChatGPT MCP                      | "standard generality of: a finite product of `f(x)^{g(x)}` with `f>0` smooth is smooth; is `C¹` the right bar?" | n/a  | —                                | MCP unavailable in this environment (per task brief). Substituted: the underlying fact is the elementary "smoothness of `rpow` with positive base", which mathlib already packages as `ContDiff.rpow` (see Phase 5). The standard form would be the `C^∞` (`ContDiff ℝ ⊤`) statement, of which `C¹` is a trivial specialisation. |
|  5 | Local references                 | grep `.mathlib-quality/references/`                                                                     | n/a  | —                                | Directory absent (`projects/Chebotarev/.mathlib-quality/references/` does not exist). Recorded n/a. |
|  6 | nLab                             | "exp map" / "smooth map number field" — not a categorical/nLab concept                                 | n/a  | —                                | Not an nLab-style abstract-nonsense concept; n/a with reason. |
|  7 | nCatLab                          | —                                                                                                      | n/a  | —                                | Not categorical; n/a. |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry concept (real-analytic regularity of a specific arithmetic map); n/a. |
|  9 | MathOverflow / Math.SE           | smoothness of `∏ a_i^{x_i} · e^{x}` / regularity of exp-of-log-lattice parametrization                  | no   | —                                | The fact is too elementary to have a dedicated MO/SE thread; it is "obvious by the chain rule" to a working analyst. |
| 10 | recent arXiv (last 5 years)      | Gun–Ramaré–Sivaraman "Counting ideals in ray classes"; Debaene; Widmer boundary cells                  | partial | the Lipschitz-boundary *method* | The cited literature (GRS §3.3, Debaene, Widmer/Lang GTM 110) uses the smoothness of this parametrization implicitly as a step toward the Lipschitz boundary cover, but states no `ContDiff` lemma — they go straight to "the boundary is Lipschitz-parametrizable". The `C¹` step is a private intermediate, not a headline result. |

### Literature summary (Phase 3)

Concept identified as: regularity (`C¹`/`C^∞`) of `expMapBasis`, a mathlib-internal real-analytic
parametrization of the norm-1 fundamental cone. The *underlying* mathematical content is the
elementary calculus fact "a finite product of real powers `f(x)^{g(x)}` of positive smooth functions,
scaled by `exp`, is smooth", which mathlib already abstracts as `ContDiff.rpow` + `Real.contDiff_exp`
+ `contDiff_finset_prod'`.
Sources agree on the standard form: yes (trivially) — the standard statement of such a regularity
fact is the maximal `C^∞` version; `C¹` is a specialisation chosen here only because that is the bar
`ContDiff.locallyLipschitz` needs.
Most general standard form: `ContDiff ℝ ⊤ (⇑expMapBasis)` (i.e. `C^∞`), since every ingredient
(`exp`, `rpow` with positive base, finite products, scalar mult) is `C^∞`.
Generality dimensions where the literature varies:
  - Smoothness order: literature/mathlib idiom would state `C^∞` (`⊤`); the project states `C¹` (`1`).
    The `C^∞` form implies the `C¹` form in one call (`.of_le le_top`).
Disagreement with the literature: none — the project's `C¹` is a deliberate (and weaker than maximal)
specialisation of the natural `C^∞` fact. This is the one generality lever (see Phase 4).

### Generality analysis — `Chebotarev.contDiff_expMapBasis`

Literature-standard form (from Phase 3): `ContDiff ℝ ⊤ (⇑expMapBasis)` — the map is `C^∞`, not merely `C¹`.

| # | Parameter / hypothesis            | Current Lean form                  | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|------------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | smoothness order `1`              | `ContDiff ℝ 1 (⇑expMapBasis)`      | `ContDiff ℝ ⊤ (⇑expMapBasis)`    | YES (strengthen to ⊤) | Every ingredient is `C^∞`; the identical `fun_prop`-style proof yields `⊤` with no extra work. The `1` is an under-statement. |
| 2 | `[Field K] [NumberField K]`       | number field                       | number field                     | NO                  | `expMapBasis` is *defined* only for number fields (uses `fundSystem`, `InfinitePlace`, `regulator`). Cannot be weakened — the object does not exist otherwise. |
| 3 | scalar field `ℝ`                  | `ℝ`-`ContDiff`                     | `ℝ` (real-analytic domain)        | NO                  | `realSpace K = InfinitePlace K → ℝ` is a real vector space and `Real.exp`/`Real.rpow` are real maps; `ℝ` is the only sensible base field. |

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (one lever: smoothness order `1` vs `⊤`).
Number of weakening/strengthening opportunities found: 1 (strengthen `1` → `⊤`).
Proposed restatement:

```lean
theorem contDiff_expMapBasis : ContDiff ℝ ⊤ (⇑(expMapBasis (K := K)))
```

(The existing proof body — `rw [funext expMapBasis_apply']; fun_prop (disch := …)` — closes the `⊤`
goal verbatim, since `Real.contDiff_exp`, `ContDiff.rpow`, `contDiff_finset_prod'`, `ContDiff.smul`,
`contDiff_apply` are all `WithTop ℕ∞`-polymorphic and `@[fun_prop]`-tagged at `⊤`.)
Cost of restatement: CHEAP — same proof; downstream consumers that need `C¹` get it via `.of_le le_top`.

If MAXIMALLY GENERAL — no. STRICTLY NARROWER → Phase 7 considers YES-but-generalise-first prominently.
But see Phase 6: the more decisive question is whether mathlib should host this *at all* given it is a
1-call companion to the existing `hasFDerivAt_expMapBasis`.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses?                                                                | no       | — | No bundled-hypothesis preamble; the only hypotheses are the `NumberField` typeclasses, already idiomatic. |
|  2 | sequences/metric → filters/topology?                                                                     | no       | — | Already a topological/`ContDiff` statement. |
|  3 | construct object → universal-property class?                                                             | no       | — | This is a property of an existing object, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                       | no       | — | n/a. |
|  5 | vector-space/metric/field-specific → weaken typeclasses?                                                 | no       | — | `realSpace K` is a concrete pi-type over `ℝ`; no hierarchy to weaken. |
|  6 | 1-categorical → higher-categorical?                                                                      | no       | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                          | partial  | smoothness order `1`→`⊤` (the only "index" here is the differentiability order) | The `⊤` form is the genuinely-idiomatic mathlib statement of a smoothness lemma; `C¹` reads as an artificial cap. This duplicates the Phase-4b lever, not a new one. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: yes, but it is exactly the Phase-4b strengthening (state `ContDiff ℝ ⊤`), not a
structurally different reformulation. Mathlib's house style for "map is smooth" lemmas is the
`WithTop ℕ∞`-polymorphic `{n : WithTop ℕ∞} → ContDiff ℝ n f` or the maximal `ContDiff ℝ ⊤ f`; a
hard-coded `1` is the non-idiomatic choice.
  - Proposed mathlib-idiomatic restatement: `theorem contDiff_expMapBasis {n : WithTop ℕ∞} : ContDiff ℝ n (⇑(expMapBasis (K := K)))` (fully order-polymorphic — the most mathlib-idiomatic; specialises to `1` and `⊤` for free).
  - Cost: CHEAP (the `fun_prop`/`rpow` building blocks are themselves `{n}`-polymorphic).
  - Mathlib downstream this enables: any consumer needing `C^k` for `k > 1` (e.g. a future change-of-variables / Jacobian-regularity argument on the cone) gets it directly; the `C¹` consumers (`ContDiff.locallyLipschitz`) are unaffected.
  - Real mathematical improvement: yes — it removes an artificial regularity cap on a reusable lemma; not abstraction-for-its-own-sake.

### Mathlib search-status: `Chebotarev.contDiff_expMapBasis`

[A] Lean-Finder       n/a — MCP/index tools unavailable in this stale-build environment.
[B] Loogle            n/a — index tool unavailable. Substituted with grep over the mathlib source tree (method [D]), which is authoritative for "does mathlib have this exact decl".
[C] LeanSearch        n/a — index tool unavailable.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/`:
      - `contDiff.*expMap` / `ContDiff.*expMapBasis` → NO HITS (mathlib has no `ContDiff` lemma for `expMap`, `expMap_single`, or `expMapBasis`).
      - `expMapBasis` in mathlib → defined in `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:465`; the file's *derivative* API is `fderiv_expMapBasis` (abbrev, l.576) and `hasFDerivAt_expMapBasis` (l.580) — i.e. **differentiability with an explicit derivative formula, but NOT `ContDiff`**. Likewise `hasFDerivAt_expMap` (l.314), `hasDerivAt_expMap_single` (l.232).
      - building blocks present: `Real.contDiff_exp` (ExpDeriv.lean:271), `ContDiff.rpow` (Pow/Deriv.lean:621), `contDiff_finset_prod'` (ContDiff/Operations.lean:490 region), `ContDiff.smul` (Operations.lean:574), `contDiff_apply` (Operations.lean:145), `contDiff_pi` (Operations.lean:112) — all `@[fun_prop]`.
[E] Name pattern      Grep `contDiff_expMapBasis` across mathlib → NO HITS. The name is original to this project.

Searched for both:
  - the user's current form (`ContDiff ℝ 1 expMapBasis`) → not in mathlib.
  - the literature-standard `C^∞` form (`ContDiff ℝ ⊤ expMapBasis`) → not in mathlib either.

Concluded: not in mathlib as a packaged `ContDiff` lemma (all available methods exhausted, both forms).
**BUT** mathlib has the full `HasFDerivAt`/`fderiv` derivative API for this exact map
(`hasFDerivAt_expMapBasis` + the explicit `fderiv_expMapBasis`), and all the `fun_prop` building blocks
for a one-shot `ContDiff` proof.

### Call sites — `Chebotarev.contDiff_expMapBasis`

Internal use count: 2  (within the project, NOT counting the declaring file) → actually **0 external-to-file**: both uses are inside the declaring file `NormLeOneLipschitz.lean`.
External-to-file callers: 0 distinct files.

| Caller file:line                         | Usage pattern (one-line excerpt)                                      |
|------------------------------------------|-----------------------------------------------------------------------|
| NormLeOneLipschitz.lean:153 (same file)  | `(contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ …)` — in `contDiff_faceMapZero` |
| NormLeOneLipschitz.lean:161 (same file)  | `(contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp …)` — in `contDiff_faceMapSide` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `contDiff_expMapBasis`?): (none — it is the single source of the `C¹`-of-`expMapBasis` fact in the project.)

Call-sites signal: K = 2 *but both in the declaring file* → by the skill's table this is the "K = 1
internal use only / wrong-abstraction" neighbourhood: the lemma exists purely to factor a sub-step of
two sibling lemmas in the same file. It is NOT an externally-depended API surface. This *weakens* the
case for shipping it standalone and *strengthens* "compose it where needed" — UNLESS mathlib itself
would want the named `C¹`/`C^∞` companion next to `hasFDerivAt_expMapBasis` (it plausibly would; see
Phase 7).

### Composition check (Phase 6)

Can `contDiff_expMapBasis` be derived from mathlib in ≤3 chained calls?

Attempt 1 — via the existing mathlib derivative API (`hasFDerivAt_expMapBasis`):
  `ContDiff ℝ 1 f` from `∀ x, HasFDerivAt f (D x) x` requires *additionally* that `x ↦ D x` is
  continuous (`contDiff_one_iff_fderiv` / `ContDiff.of_continuous_fderiv`-style). Mathlib gives
  `hasFDerivAt_expMapBasis` but **no lemma that `x ↦ fderiv_expMapBasis K x` is continuous** — that
  continuity is itself a non-trivial fact (the derivative involves `expMap_single x · (mult)⁻¹`, i.e.
  another `exp`, so proving its continuity is comparable work to the `ContDiff` proof itself).
  Result: FAILS as a ≤3-call composition. The `HasFDerivAt` route does not shortcut to `ContDiff`.

Attempt 2 — direct, via the `fun_prop` building blocks (the project's actual proof):
  ```lean
  rw [show ⇑expMapBasis = fun x ↦ Real.exp (x w₀) • fun w ↦ ∏ i, w (fundSystem K (equivFinRank.symm i)) ^ x i
        from funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')
  ```
  This is `Real.contDiff_exp` ∘ `contDiff_apply` (for `exp(x w₀)`), `ContDiff.smul`, and
  `contDiff_finset_prod'` of `ContDiff.rpow (contDiff_const) (contDiff_apply …) (base ≠ 0)`.
  Counting "mathlib calls": the *automation* (`fun_prop`) hides ~5–6 distinct lemma applications, AND
  the proof is gated on a **mandatory non-`fun_prop` rewrite** `funext expMapBasis_apply'` (mathlib
  `fun_prop` cannot see through `⇑expMapBasis = expMap ∘ equivFunL.symm`, built from
  `OpenPartialHomeomorph.pi`/`expMap_single`, to the smooth-combinator form). So it is NOT a clean
  1–3 named-call inline: it needs the structural `expMapBasis_apply'` unfolding plus a custom
  positivity discharger.
  Result: PARTIAL — composable in spirit (all blocks exist), but the necessary `expMapBasis_apply'`
  rewrite + `disch` make it a genuine ~3-line proof, not a one-liner you would want duplicated at every
  call site.

Conclusion: NOT-COMPOSABLE in the strict ≤3-named-call sense. The result is a small but real proof
(rewrite-then-`fun_prop`-with-discharger), and it is the natural `ContDiff` companion to mathlib's own
`hasFDerivAt_expMapBasis`.

## Verdict: `Chebotarev.contDiff_expMapBasis`

**Category:** YES-but-generalise-first

**Evidence:**
- Literature search (Phase 3): the underlying fact is the elementary "smooth `rpow` with positive base"; mathlib already abstracts it (`ContDiff.rpow`), but states no `ContDiff` for `expMapBasis`. The natural/idiomatic form is `C^∞`, not `C¹`.
- Generality analysis (Phase 4): STRICTLY NARROWER — the smoothness order is hard-capped at `1`; the identical proof yields `⊤` (Phase 4b lever) and the idiomatic form is order-polymorphic `{n : WithTop ℕ∞}` (Phase 4c).
- Mathlib search (Phase 5): not in mathlib (both `C¹` and `C^∞` forms); but mathlib *does* own this exact map and its `hasFDerivAt`/`fderiv` API in `NormLeOne.lean`, with a visible gap where the `ContDiff` companion should sit.
- Composition check (Phase 6): NOT-COMPOSABLE in ≤3 named calls (the `hasFDerivAt` route needs the missing continuity-of-`fderiv`; the direct route needs the `expMapBasis_apply'` rewrite + a custom discharger).

**Rationale:**

Mathlib defines `expMapBasis` and proves its differentiability with an explicit derivative
(`hasFDerivAt_expMapBasis`, `fderiv_expMapBasis`) in
`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`, but stops short of the `ContDiff`
("`C^k`") statement. The project's lemma fills exactly that gap, and it is not a free composition: the
`HasFDerivAt`-everywhere fact does not upgrade to `ContDiff 1` without separately proving the derivative
map `x ↦ fderiv_expMapBasis K x` is continuous (a fact mathlib does not provide and which is comparable
work), and the direct `fun_prop` proof is gated on the structural rewrite `funext expMapBasis_apply'`
plus a positivity discharger — a genuine ~3-line proof, not a one-liner to inline at call sites. So this
belongs in mathlib, sitting right next to `hasFDerivAt_expMapBasis`.

It should be **generalised before upstreaming**: the statement hard-codes smoothness order `1`, but
every ingredient (`Real.contDiff_exp`, `ContDiff.rpow` with positive base, `contDiff_finset_prod'`,
`ContDiff.smul`) is `C^∞` and `WithTop ℕ∞`-polymorphic, so the *same proof* discharges the maximal form.
Mathlib's house style for smoothness lemmas is the order-polymorphic `{n : WithTop ℕ∞} → ContDiff ℝ n f`
(or at least `ContDiff ℝ ⊤ f`); the `C¹` cap is an under-statement that the local consumers
(`contDiff_faceMapZero`/`contDiff_faceMapSide`, which only need `C¹`) happen not to expose. Shipping the
polymorphic/`⊤` form costs nothing and future-proofs any later Jacobian/change-of-variables regularity
work on the fundamental cone (the same file already computes `abs_det_fderiv_expMapBasis`, a natural
neighbour for higher-order smoothness).

**Reason for the generalisation:**
  - LITERATURE-WEAKENING: Phase 4b found the user's form (`ContDiff ℝ 1`) strictly narrower than the natural/maximal form (`ContDiff ℝ ⊤`).
  - MODERN-IDIOM (Bourbaki 2.0): Phase 4c — mathlib's idiom for smoothness lemmas is order-polymorphic `{n : WithTop ℕ∞}`; the hard-coded `1` is non-idiomatic.

**Proposed restatement:**
```lean
-- Most idiomatic (order-polymorphic); specialises to `1`, `⊤` for free:
theorem contDiff_expMapBasis {n : WithTop ℕ∞} :
    ContDiff ℝ n (⇑(expMapBasis (K := K))) := by
  classical
  rw [show ⇑(expMapBasis (K := K)) = fun x : realSpace K ↦
      Real.exp (x w₀) • fun w : InfinitePlace K ↦
        ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i from
    funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')
-- (or, if the polymorphic form trips `fun_prop`, state `ContDiff ℝ ⊤ …` and let consumers use `.of_le le_top`.)
```
Estimated cost of regeneralisation: CHEAP — the existing proof body is expected to close the
order-polymorphic goal unchanged (all building blocks are `{n : WithTop ℕ∞}`-polymorphic). If
`fun_prop` instantiates `n` awkwardly, fall back to the `⊤` form; still CHEAP.
Note: EXPENSIVE would not downgrade the verdict, but this is CHEAP.

Mathlib downstream this enables:
  - sits as the `ContDiff` companion to `hasFDerivAt_expMapBasis` / `fderiv_expMapBasis` in `NormLeOne.lean`;
  - higher-order (`C^k`, `k > 1`) consumers — e.g. future Jacobian-regularity / smooth change-of-variables on the norm-1 cone (the file already has `abs_det_fderiv_expMapBasis`) — get smoothness directly instead of re-deriving it;
  - the local `C¹` consumers (`contDiff_faceMapZero`, `contDiff_faceMapSide`, via `ContDiff.locallyLipschitz`) are unchanged (they read off `n = 1`).

Proposed mathlib location: `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`
(immediately after `hasFDerivAt_expMapBasis`, in the `expMapBasis` section).
Proposed PR title: "feat(NumberTheory): `expMapBasis` is smooth (`ContDiff`)"
PR grouping: ship together with the analogous (and equally-missing) `contDiff_expMap` /
`contDiff_expMap_single`, which the same building blocks prove and which would naturally accompany
`hasFDerivAt_expMap` / `hasDerivAt_expMap_single`. (These are mathlib-side decls, so the PR adds all
three `ContDiff` lemmas next to their existing `HasFDerivAt` siblings.)

Next action: run `/generalise Chebotarev.contDiff_expMapBasis` (tension `C¹` vs the order-polymorphic
`{n}` / `⊤` target from Phases 4b/4c, confirm the proof survives), then upstream as the `ContDiff`
companion to `hasFDerivAt_expMapBasis`.

---

## Next step

Run `/generalise Chebotarev.contDiff_expMapBasis` to lift `ContDiff ℝ 1` to the order-polymorphic
`{n : WithTop ℕ∞}` (or `⊤`) form, verify the existing `rw … ; fun_prop (disch := …)` proof still
closes, then open a mathlib PR adding it (and the analogous `contDiff_expMap` / `contDiff_expMap_single`)
beside the existing `hasFDerivAt_expMapBasis` in `NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean`.
