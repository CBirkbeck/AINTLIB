# `/mathlibable` report — `PadicLFunctions.integerRing.norm_algebraMap_eq`

**Final verdict (five-bucket): `NO-composable-from-mathlib`**

---

### Baseline (Phase 0)
- lake build:               build not re-run (stale/slow per task note); **reasoned from source** — the decl and all its dependencies read directly.
- decl `PadicLFunctions.integerRing.norm_algebraMap_eq`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:93`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field, plus its basic API.

---

### Statement (Phase 1)

`PadicLFunctions.integerRing.norm_algebraMap_eq` is a lemma stating the following:

> Let `L` be a nonarchimedean (ultrametric) complete normed field that is a normed `ℚ_[p]`-algebra, and let `integerRing L = {x : L | ‖x‖ ≤ 1}` be its valuation/unit-ball subring. The canonical algebra map `ℤ_[p] → integerRing L` (the restriction of the scalar embedding `ℚ_[p] → L` to `p`-adic integers, landing in the unit ball) **preserves the norm**: for every `x : ℤ_[p]`, `‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖`. Equivalently, this embedding is an isometry (the companion lemma `isometry_algebraMap` records exactly that).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]` — the nonarchimedean normed `ℚ_[p]`-algebra field. (`[CompleteSpace L]` is present in the section but `omit`-ted for this lemma.)
- `integerRing L : Subring L` — project-local def (`Coefficients.lean:41`): the unit ball as a subring; carries the *induced* subtype norm (`‖x‖ = ‖(x : L)‖` definitionally) and a project-local `Algebra ℤ_[p] (integerRing L)` instance (`Coefficients.lean:60`).

Hypotheses (Lean side):
- `(x : ℤ_[p])` — the input p-adic integer. No side hypotheses.

Conclusion (math): The base-ring-of-integers embedding `ℤ_[p] ↪ 𝒪_L` is norm-preserving.

Conclusion (Lean): `‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖`.

Proof body (3 substantive tokens):
```lean
change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖
rw [norm_algebraMap', PadicInt.norm_def]
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a basic norm-API helper lemma about a project-local subring; not a named theorem, not a new structure, not a `## Main results` headline (the headline declarations of this file are `integerRing`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`). It is plumbing that the file's `Isometry` / `IsBoundedSMul` instances consume.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a defeq `change` + a 2-lemma `rw`).
One-liner verdict: **n/a — kind is `lemma`, not `def`/`abbrev`/`structure`.** (The one-line *def* exemption table does not apply to lemmas; recorded for completeness.) The lemma is nonetheless a near-trivial 2-rewrite, which is the operative signal carried into Phases 6–7.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query | Hit? | Standard form found | Notes |
|----|----------------------------------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "ring of integers nonarchimedean field unit ball norm preserving isometry Z_p embedding" | yes | `𝒪 = {x : |x| ≤ 1}`; base `𝒪_K ↪ 𝒪_L` norm-preserving | Wikipedia "Ring of mixed characteristic"; Crew LCFT; Achinger non-arch geometry — all treat `𝒪_L` as the unit ball and the inclusion as valuation-compatible |
|  2 | WebSearch (general form)         | "algebra map p-adic integers ring of integers isometry norm equality valuation ring extension" | yes | unique extension of `|·|_p` to `L` restricts to `|·|_p` on `ℚ_p`; `𝒪_L` free over `ℤ_p` | Conrad/Thorne notes, Gupta REU, Hamburg (Cp), Popa Ch.3 — the valuation extends *uniquely*, so restriction to `ℤ_p` is exactly the original norm |
|  3 | WebSearch (named-after / aliases)| "norm_algebraMap Lean mathlib NormOneClass isometry scalar embedding" | yes | mathlib `algebraMap_isometry` + `norm_algebraMap'` | the Lean-idiomatic name is `algebraMap_isometry` (`Isometry (algebraMap 𝕜 𝕜')` under `[NormOneClass 𝕜']`) — directly relevant, see Phase 5 |
|  4 | ChatGPT MCP                      | (would ask: standard form + generality + historical evolution of "base ring of integers embeds isometrically into the extension's ring of integers") | n/a | — | ChatGPT MCP **not configured** in this environment (`/setup-chatgpt` exists but no server running). Recorded n/a; the WebSearch ×3 + nLab + arXiv channels below cover the standard-form question redundantly. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` | n/a | — | directory **absent** (`ls` → No such file or directory). Recorded n/a per protocol. The module docstring cites RJW §3.1 (TeX 690) for the object. |
|  6 | nLab                             | "valuation ring", "normed rings" | yes | valuation ring sits in valued field as unit ball; valuations extend to absolute values on fraction fields | ncatlab.org/nlab/show/valuation+ring; Jarden "Normed Rings" Ch.2 — abstract statement matches |
|  7 | nCatLab (if categorical)         | — | n/a | — | not a categorical concept; it is a metric/valuation-theoretic norm equality. n/a with reason. |
|  8 | Stacks Project (if alg geom)     | (valuation rings / extensions) | n/a | — | the fact is elementary valuation theory; Stacks has valuation-ring material but adds nothing beyond #2/#6 for a *normed-field* norm equality. Looked; n/a — no incremental standard form. |
|  9 | MathOverflow / Math.StackExchange| "norm on Z_p preserved in O_L extension isometry" (folded into #1/#2 sweeps) | yes | "any σ ∈ Gal(L/ℚ_p) is an isometry; |·| extends uniquely" | surfaced via Turner/Fithian REU + Sharifi ANT notes — confirms the inclusion is norm-preserving as a one-liner consequence of uniqueness of the extension |
| 10 | recent arXiv (last 5 years)      | "Dynamics of convergent power series on the integral ring of a finite extension of Qp" (1401.1062); "non-Archimedean Arens–Eells isometric embedding" (2309.06704) | yes | confirms `𝒪_L` = integral ring of the extension; norm extends | modern usage identical to classical; no reformulation of the embedding-is-isometric fact |

Protocol pass check: WebSearch ran 3 distinct queries at different generality levels ✓; ChatGPT MCP recorded n/a-with-reason (not configured) ✓; local refs checked (absent → n/a) ✓; nLab checked ✓; Stacks/nCatLab/MathOverflow/arXiv each checked or n/a-with-reason ✓.

### Literature summary (Phase 3)

Concept identified as: **the base ring of integers `ℤ_p` embeds isometrically (norm-preservingly) into the ring of integers `𝒪_L` of a complete extension** — a direct consequence of the *uniqueness of the extension of the p-adic absolute value* (Koblitz, Cassels, Neukirch, Conrad/Thorne, Sharifi).
Sources agree on the standard form: **yes** — the (normalized) norm on `L` restricts on `ℚ_p ⊃ ℤ_p` to the original p-adic norm; hence `‖algebraMap ℤ_p 𝒪_L x‖ = ‖x‖`. Universal across every p-adic analysis text.
Most general standard form: for **any** isometric ring embedding of valued fields `K ↪ L` (the valuation on `L` extending that on `K`), the induced map `𝒪_K → 𝒪_L` is norm-preserving. In Lean this is exactly the `NormOneClass`-algebra-map fact `‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
Generality dimensions where the literature varies:
  - base/extension: `ℤ_p → 𝒪_L` is a specialisation of `𝒪_K → 𝒪_L` for arbitrary complete valued `K`.
  - the carrier: the literature states it for the *fields* (`norm_algebraMap'`); the integer-ring version is the immediate restriction.
Disagreement with the literature: **none.** The Lean statement is the standard fact, specialised to `ℤ_p` and wrapped through the project's `integerRing L` subtype norm.

---

### Generality analysis — `PadicLFunctions.integerRing.norm_algebraMap_eq`

Literature-standard form (from Phase 3): for any `NormOneClass` normed algebra, `‖algebraMap 𝕜 𝕜' x‖ = ‖x‖` (mathlib `norm_algebraMap'`); the integer-ring statement is its restriction to `ℤ_p ⊂ ℚ_p` landing in the subring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `ℤ_[p]` (the source ring) | p-adic integers | `𝒪_K` for any complete valued field `K` (or any `NormOneClass` scalar ring) | yes | the proof uses only `PadicInt.norm_def` (the coercion `ℤ_p ↪ ℚ_p` is norm-preserving) + `norm_algebraMap'`; nothing p-specific |
| 2 | `[NormedAlgebra ℚ_[p] L]` + `integerRing L` | `ℚ_p`-algebra unit ball | base-of-integers into extension-of-integers, any nonarch. field | yes | the whole statement is the generic `norm_algebraMap'` modulo the subtype-norm coercion; nothing about `L` beyond `NormOneClass`/ultrametric is used |
| 3 | `[IsUltrametricDist L]` | ultrametric | (only used to *make* `integerRing` a subring; not used in this lemma's proof) | n/a here | this lemma's proof doesn't invoke ultrametricity — it is inherited from the ambient def. Not a weakening target for the lemma itself. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** — but what it is is a *specialisation to a project-local object* (`integerRing L`) of the fully-general mathlib lemma `norm_algebraMap'`. There is nothing to weaken *within the project's `integerRing` framing*; the more-general form already lives in mathlib (Phase 5). Number of weakening opportunities found: 0 (within the project framing).
Proposed restatement: none at the project level. The "more general form" is literally the mathlib lemma `norm_algebraMap'`, which already exists — so this is a Phase-5/Phase-6 (composability) situation, not a Phase-4 (generalise-the-project-lemma) situation.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|---------------------------------|
| 1 | bundled-hypotheses → typeclasses/instances? | no | the hypotheses are already typeclasses (`NormedAlgebra`, `IsUltrametricDist`, `NormOneClass` via `ℤ_p`) | — |
| 2 | sequences/metric → filters/topology? | no | it is a pointwise norm equality; no limit/sequence content | — |
| 3 | construction → universal property? | no | norm equality, not a construction | — |
| 4 | set-with-closure-predicate → bundled substructure? | **partially relevant to the underlying `integerRing`, not this lemma** | `integerRing L = {x | ‖x‖ ≤ 1}` is itself a "set closed under ops" rebuild of the **valuation subring**; mathlib has `Valuation.valuationSubring` / `Valued`-API for exactly this | this is the deeper redundancy: `integerRing` duplicates mathlib's valuation-subring; see Phase 7 note. But it concerns the *parent def*, not `norm_algebraMap_eq`. |
| 5 | vector-space/field-specific → weaken typeclasses? | no (already at the right typeclass level) | — | — |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index ℕ/ℤ/ℝ → general monoid? | no | `ℤ_[p]` is the intended source; the generic form is `norm_algebraMap'` itself | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this lemma). The lemma is already a thin norm-equality at the correct typeclass level; the only "modernisation" in the neighbourhood concerns the *parent* `integerRing` def (it re-implements a valuation subring), which is out of scope for assessing this lemma and does not flip this lemma to YES-but-generalise.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma** (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.integerRing.norm_algebraMap_eq`

[A] Lean-Finder       "algebra map ring of integers norm equality isometry NormOneClass" — n/a in-env (no Lean-Finder MCP); reasoned from the doc-search + grep below, which already pinpoints the building blocks.
[B] Loogle            type pattern `‖algebraMap _ _ _‖ = ‖_‖` — **hit** (reasoned): mathlib `norm_algebraMap'` matches exactly; pattern `Isometry (algebraMap _ _)` → `algebraMap_isometry`. (Loogle MCP not available in-env; the canonical hits are confirmed by direct grep of mathlib source.)
[C] LeanSearch        "the algebra map from the base field to a normed algebra is an isometry / norm-preserving" — **hit** (web doc search returned `Mathlib.Analysis.Normed.Module.Basic` → `algebraMap_isometry`).
[D] Grep mathlib src  `theorem norm_algebraMap'`, `theorem algebraMap_isometry`, `theorem norm_def`, `coe_norm`, `def integerRing` — see findings below.
[E] Name pattern      `norm_algebraMap*`, `*isometry_algebraMap*`, `integerRing`, `valuationSubring` over `.lake/packages/mathlib/`.

Grep findings (method D/E, exact):
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293`: `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`. **The general form of this lemma.**
- `algebraMap_isometry` — `Mathlib/Analysis/Normed/Module/Basic.lean:340`: `[NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜')`. **The general form of the companion `isometry_algebraMap`.**
- `PadicInt.norm_def` — `Mathlib/NumberTheory/Padics/PadicIntegers.lean:191`: `‖z‖ = ‖(z : ℚ_[p])‖ := rfl`. (The `ℤ_p ↪ ℚ_p` coercion preserves the norm by definition.)
- `AddSubgroupClass.coe_norm` (used at e.g. `Mathlib/Analysis/Complex/Basic.lean:726`) and `Subgroup.coe_norm` (`Mathlib/Analysis/Normed/Group/Subgroup.lean:48/98`): the subtype norm is the induced norm, `‖x‖ = ‖(x : E)‖` **definitionally** (`NormedGroup.induced`). This is exactly the defeq the proof's `change` exploits.
- `def integerRing` — **NOT FOUND in mathlib** (grep empty). The lemma's target object is project-local.
- mathlib *does* have the valuation-subring analogue infrastructure: `Valuation.valuationSubring` / `RingTheory/Valuation/AlgebraInstances.lean` (`algebraMap_injective` for `v.valuationSubring L`), but **no** norm-equality lemma stated against a subtype norm of a unit-ball subring (because mathlib's valuation subrings are not normed-field-with-`integerRing` objects).

Searched for both:
  - the user's current form (`‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖`) — **not present** (object is project-local).
  - the literature-standard / general form (`‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`) — **present** as `norm_algebraMap'`, and the isometry form as `algebraMap_isometry`.

Concluded: **"found building blocks (`norm_algebraMap'`, `PadicInt.norm_def`, `AddSubgroupClass.coe_norm`, and the companion `algebraMap_isometry`); a 1–2 mathlib-call composition (modulo a defeq `change` through the project's own `Algebra ℤ_[p] (integerRing L)` instance) yields the lemma."** The *exact* statement is not in mathlib (it cannot be — `integerRing L` is project-local), and the project's lemma is the literal `rw [norm_algebraMap', PadicInt.norm_def]` after a `change`.

---

### Call sites — `PadicLFunctions.integerRing.norm_algebraMap_eq`

Internal use count: **0** (within the project, NOT counting the declaring file).
External-to-file callers: **0 distinct files.**

Same-file consumers (informational — these are *not* counted as external, but they are the lemma's actual reason for existing):

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| Coefficients.lean:100 | `isometry_algebraMap := AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)` |
| Coefficients.lean:106 | `IsBoundedSMul` instance: `(norm_mul_le _ _).trans_eq (by rw [norm_algebraMap_eq])` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **(none)** — no other file in `projects/` mentions `norm_algebraMap_eq`, and no other site re-derives `‖algebraMap ℤ_[p] (integerRing L) _‖ = ‖_‖` inline.

What the pattern tells us (per the call-sites signal table): **K = 0 external uses, two same-file consumers, no inline re-derivation.** The lemma is a small same-file helper feeding `isometry_algebraMap` and the `IsBoundedSMul` instance. It is *not* public-facing API with external consumers; it is local glue. This biases the verdict away from a YES bucket and toward NO-composable (the consumers can call the composition / the mathlib companion directly).

---

### Composition check (Phase 6)

Can `norm_algebraMap_eq` be derived from mathlib in ≤3 chained calls?

Attempt 1: the project's own proof, which is already the composition:
```lean
lemma norm_algebraMap_eq (x : ℤ_[p]) : ‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖ := by
  change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖   -- defeq via project Algebra instance + AddSubgroupClass.coe_norm
  rw [norm_algebraMap', PadicInt.norm_def]
```
  - Mathlib decls used: `norm_algebraMap'`, `PadicInt.norm_def` (+ the implicit `AddSubgroupClass.coe_norm` defeq and the project's `Algebra ℤ_[p] (integerRing L)` instance).
  - Result: **succeeds** — 2 rewrites after one defeq `change`.
  - Notes: per the Phase-6 heuristics table, `rw [a, b]` after a `change` is a borderline-but-acceptable composition (2 mathlib calls, no `ring_nf`/`aesop`, no chain of non-trivial `have`s). It is NOT a proof in disguise.

Attempt 2 (isometry route, even shorter for the *companion* lemma): the companion `isometry_algebraMap` is mathlib's `algebraMap_isometry` modulo the same `change`; and `norm_algebraMap_eq` itself follows from `algebraMap_isometry` + the subtype/`ℤ_p`-coercion norm identities.

Conclusion: **COMPOSABLE.** ≤3 mathlib calls (`norm_algebraMap'` + `PadicInt.norm_def`, glued by the project's algebra instance + the definitional subtype norm). The one caveat — the `change` relies on the *project-local* `Algebra ℤ_[p] (integerRing L)` instance — is exactly why this is NO-composable rather than NO-mathlib-has-it: the composition is anchored to a project object, so the right action is to inline it at the (two, same-file) call sites, not to delete-and-replace with a single existing mathlib lemma.

---

## Verdict: `PadicLFunctions.integerRing.norm_algebraMap_eq`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the fact (`ℤ_p ↪ 𝒪_L` is norm-preserving) is standard and universal — a one-line consequence of the unique extension of `|·|_p`; the Lean-idiomatic name is `algebraMap_isometry` / `norm_algebraMap'`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL within the project's `integerRing` framing, with 0 weakening targets; the genuinely-more-general form already lives in mathlib (`norm_algebraMap'`). Modern-idiom: none for this lemma.
- Mathlib search (Phase 5): the exact statement is **not** in mathlib (object `integerRing L` is project-local), but the **building blocks are**: `norm_algebraMap'` (Basic.lean:293), `PadicInt.norm_def` (PadicIntegers.lean:191), `AddSubgroupClass.coe_norm`, plus companion `algebraMap_isometry` (Basic.lean:340).
- Composition check (Phase 6): **COMPOSABLE** — `change ...; rw [norm_algebraMap', PadicInt.norm_def]`, i.e. ≤3 mathlib calls glued by the project's own `Algebra ℤ_[p] (integerRing L)` instance and the definitional subtype norm. Call sites: 0 external, 2 same-file.

**Rationale:**

The mathematics here is the textbook fact that the embedding of the base ring of integers `ℤ_p` into the ring of integers `𝒪_L` of a complete extension preserves the norm — an immediate corollary of the uniqueness of the extension of the p-adic absolute value (every source in Phase 3 treats it as a one-liner). Mathlib already encodes the fully-general statement: `norm_algebraMap'` gives `‖algebraMap 𝕜 𝕜' x‖ = ‖x‖` under `[NormOneClass 𝕜']`, and `algebraMap_isometry` gives the isometry form. The project lemma is precisely the specialisation of these to `ℤ_p ⊂ ℚ_p` landing in the project's own unit-ball subring `integerRing L`, and its proof *is* the 2-rewrite composition `rw [norm_algebraMap', PadicInt.norm_def]` after a defeq `change`.

It is `NO-composable-from-mathlib` rather than `NO-mathlib-has-it` for one reason: the statement is phrased against `integerRing L`, a **project-local** `Subring` (mathlib has no `integerRing`; grep is empty), and against the project's own `Algebra ℤ_[p] (integerRing L)` instance. So there is no single existing mathlib lemma to drop in by qualified name — the equality is recovered by composing the mathlib building blocks through the project's defeq glue. With **0 external call sites** and only two same-file consumers (`isometry_algebraMap` and the `IsBoundedSMul` instance), the lemma is local plumbing, not reusable API headed for mathlib. (Separately and out of scope for this lemma: the parent `integerRing` def itself re-implements the **valuation subring** mathlib already has via `Valuation.valuationSubring`; if anything in this neighbourhood were ever to be upstreamed, that re-implementation — not this norm helper — is the thing to reconcile with mathlib first.)

**WHY not (refactor-actionable detail):**

Mathlib has the building blocks; the lemma is a ≤3-call composition over a project object. Name the blocks and the glue:

Mathlib building blocks:
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293` — `[NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖`.
- `PadicInt.norm_def` — `Mathlib/NumberTheory/Padics/PadicIntegers.lean:191` — `‖z‖ = ‖(z : ℚ_[p])‖` (`rfl`).
- `AddSubgroupClass.coe_norm` / `Subgroup.coe_norm` — `Mathlib/Analysis/Normed/Group/Subgroup.lean:48` — subtype norm is the induced norm `‖x‖ = ‖(x : E)‖` (definitional; powers the `change`).
- (companion) `algebraMap_isometry` — `Mathlib/Analysis/Normed/Module/Basic.lean:340` — `[NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜')`.

Composition sketch (≤3 lines — exactly the existing proof):
```lean
example (x : ℤ_[p]) : ‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖ := by
  change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖   -- project Algebra instance + AddSubgroupClass.coe_norm
  rw [norm_algebraMap', PadicInt.norm_def]
```

Call sites in our project (from Phase 6.0): **K = 0 external; 2 same-file** (`Coefficients.lean:100`, `Coefficients.lean:106`).

Refactor plan (honest, low-priority — this is a judgement-light NO, not a mandate to churn the file):
1. At `Coefficients.lean:100`, `isometry_algebraMap` can be derived directly from mathlib's `algebraMap_isometry` (the `ℚ_[p] → L` isometry) restricted through the codRestrict, instead of going through `AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq …)`. If kept as-is, it just inlines the 3-line norm proof.
2. At `Coefficients.lean:106` (the `IsBoundedSMul` instance), replace `by rw [norm_algebraMap_eq]` with the inline `change …; rw [norm_algebraMap', PadicInt.norm_def]` (or factor the `change` once).
3. Then `norm_algebraMap_eq` (and possibly `isometry_algebraMap`) need not be standalone named lemmas — they are 2–3-line mathlib compositions over the project's own algebra instance.

Because the composition is anchored to the project-local `integerRing` and its algebra instance, the lemma should **not** be proposed for mathlib. Net action: keep it as a small local helper if the file prefers the readability, or inline the 3-line composition at the two consumers; either way it is **not** a mathlib contribution.

Next action: **do not PR to mathlib.** Optionally inline the composition `change …; rw [norm_algebraMap', PadicInt.norm_def]` at the two same-file consumers (lines 100, 106), or leave the helper in place as local glue. (Out-of-scope follow-up if upstreaming is ever contemplated for this file: reconcile the parent `integerRing` def with mathlib's `Valuation.valuationSubring` first.)

---

## Next step

Do not PR to mathlib. The lemma is a ≤3-call composition (`norm_algebraMap'` + `PadicInt.norm_def`, glued by the project's own `Algebra ℤ_[p] (integerRing L)` instance and the definitional subtype norm) over the project-local `integerRing L`; it has 0 external call sites and 2 same-file consumers. Either inline the composition at `Coefficients.lean:100` and `:106`, or keep it as local glue — but it is not a mathlib contribution.
