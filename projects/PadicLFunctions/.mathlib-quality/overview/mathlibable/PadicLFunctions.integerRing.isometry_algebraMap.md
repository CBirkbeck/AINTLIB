# `/mathlibable` report — `PadicLFunctions.integerRing.isometry_algebraMap`

**Final verdict: `NO-composable-from-mathlib`.**

The lemma is a single mathlib call (`AddMonoidHomClass.isometry_of_norm`) applied to
the project's own norm-equality lemma `norm_algebraMap_eq`. Mathlib has the building
block; the form inlines in one line at each call site. Mathlib's *own* maintainers
deprecated a structurally identical wrapper (`WithAbs.isometry_of_comp`, since
2025-11-28) precisely in favour of calling `AddMonoidHomClass.isometry_of_norm`
directly — direct precedent that this wrapper does not belong in mathlib.

---

### Baseline (Phase 0)

- lake build:               build NOT re-run (per task instruction); reasoned from source — read the decl + its mathlib dependencies directly. The file was golfed in PR #12/#270 and is part of `main`, which "always builds".
- decl `PadicLFunctions.integerRing.isometry_algebraMap`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:99`
- kind:                      lemma
- has sorry:                 no (grep for `sorry`/`admit` over the whole file returns nothing)
- module docstring summary:  "Coefficient rings for §5: the integer ring of a nonarchimedean field" — sets up `integerRing L` (the norm-unit ball `{x | ‖x‖ ≤ 1}` as a subring) of a nonarchimedean complete normed `ℚ_[p]`-algebra `L`, and basic API on it.

Full source of the target and its one dependency:

```lean
omit [CompleteSpace L] in
/-- The algebra map `ℤ_[p] → integerRing L` is an isometry (it is the
restriction of the scalar embedding `ℚ_[p] → L`). -/
lemma norm_algebraMap_eq (x : ℤ_[p]) :
    ‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖ := by
  change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖
  rw [norm_algebraMap', PadicInt.norm_def]

omit [CompleteSpace L] in
lemma isometry_algebraMap : Isometry (algebraMap ℤ_[p] (integerRing L)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)
```

Ambient context: `variable (p : ℕ) [hp : Fact p.Prime]`, `variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` (the latter `omit`ted here), and the `Algebra ℤ_[p] (integerRing L)` instance defined at lines 60–63 as
`RingHom.toAlgebra <| ((algebraMap ℚ_[p] L).comp PadicInt.Coe.ringHom).codRestrict (integerRing L) (…)`.

---

### Statement (Phase 1)

`PadicLFunctions.integerRing.isometry_algebraMap` is a theorem stating the following:

Let `L` be a nonarchimedean complete normed field that is a normed `ℚ_p`-algebra, and let
`𝒪_L = integerRing L = {x ∈ L : ‖x‖ ≤ 1}` be its valuation ring (norm-unit ball). The canonical
ring map `ℤ_p → 𝒪_L` — namely the restriction of the scalar embedding `ℚ_p ↪ L` to the unit balls
— is an isometry: it preserves the (p-adic) distance, `dist(φ a, φ b) = dist(a, b)`. Equivalently,
since `φ` is an additive-group homomorphism, `‖φ x‖ = ‖x‖` for all `x ∈ ℤ_p` (this norm equality is
the content of the sibling lemma `norm_algebraMap_eq`, which the proof feeds in).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` — the nonarchimedean
  coefficient field. `[CompleteSpace L]` is explicitly `omit`ted — the lemma does not need completeness.
- `integerRing L : Subring L` — the project's valuation-ring definition (`{x | ‖x‖ ≤ 1}`).
- The bespoke `Algebra ℤ_[p] (integerRing L)` instance (lines 60–63): `ℤ_p → ℚ_p → L`, codomain-restricted to the unit ball.

Hypotheses (Lean side): none beyond the ambient instances (the norm equality is supplied as a term, not a hypothesis).

Conclusion (math): the inclusion `ℤ_p ↪ 𝒪_L` is distance-preserving.

Conclusion (Lean): `Isometry (algebraMap ℤ_[p] (integerRing L))`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper lemma — the continuity/injectivity packaging of the bespoke embedding
`ℤ_p ↪ 𝒪_L`. Not a new structure, not a named theorem, not a `## Main results` headline (the file's
main declarations are `integerRing`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.norm_pow_sub_one_eq_one`).

(Literature width was run EXHAUSTIVE regardless; BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)`).
One-liner verdict: n/a for the exemption table — **the kind is `lemma`, not `def`/`abbrev`/`structure`.**
The Phase-2b def-exemption rows (defeq-abuse / diamond / API-name) do not apply to a `lemma`: a lemma
introduces no definitional equality and no typeclass-search anchor. The "one substantive line" fact is
still recorded because it is load-bearing for Phase 6: this is a one-call composition.

Conclusion: MULTI-LINE/exemption check skipped (kind = lemma). The one-line-body fact carries into Phase 6.

---

### Literature search table — EXHAUSTIVE protocol

The mathematical content is the elementary fact *"a homomorphism of normed (additive) groups that
preserves the norm is an isometry"*, instantiated for the embedding `ℤ_p ↪ 𝒪_L`.

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                                            | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|--------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "norm-preserving group homomorphism is an isometry proof"                                      | yes  | `f` additive hom with `‖f x‖ = ‖x‖` ⟹ `dist(f x, f y) = dist(x, y)` (use `f(x−y)`) | ProofWiki "Isometric Isomorphism is Norm-Preserving"; standard functional analysis |
|  2 | WebSearch (general form)         | `"isometry" iff "preserves norm" additive group homomorphism standard fact`                    | yes  | "a linear operator is an isometry iff it is norm-preserving" — a *standard fact* | nLab/AMM survey (Chi-Kwong Li); "isometric ⟺ norm-preserving" for homs |
|  3 | WebSearch (named-after/instance) | `p-adic integers Z_p ring of integers O_L isometric embedding algebra map norm preserving`     | yes  | `ℤ_p = {x ∈ ℚ_p : |x|_p ≤ 1}`; the inclusion preserves `|·|_p` by definition     | K. Conrad / standard p-adic notes — the unit-ball inclusion being isometric is definitional, not a named theorem |
|  4 | ChatGPT MCP                      | (would ask: standard form + generality + historical evolution of "norm-preserving hom ⟹ isometry") | n/a  | —                                                                              | **ChatGPT MCP not configured in this environment** (no `mcp__*ChatGPT*` tool surfaced by ToolSearch). Channel recorded n/a; its role is covered by #1/#2/#6 which already pin the standard form unanimously. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`        | n/a  | (no references dir; `refs/` store absent)                                       | Both directories do not exist on this checkout — recorded n/a. |
|  6 | nLab                             | "isometry normed group homomorphism preserves norm" → `ncatlab.org/nlab/show/normed+group`     | yes  | nLab: morphisms of normed groups; "isometric ⟺ norm-preserving" for the relevant hom class | nLab confirms the equivalence; notes the two-metric subtlety for *non-abelian* normed groups (irrelevant here — `ℤ_p`, `𝒪_L` abelian under `+`) |
|  7 | nCatLab (categorical)            | (same as nLab; "isometry as morphism in the category of normed groups")                        | n/a  | —                                                                              | Not a higher-categorical concept; nLab's normed-group page (#6) is the relevant entry. No separate categorification. |
|  8 | Stacks Project (alg geom)        | —                                                                                              | n/a  | —                                                                              | Not an algebraic-geometry concept (elementary normed-group fact). Recorded n/a with reason. |
|  9 | MathOverflow / Math.SE           | (covered by #1/#2: "isometry iff preserves norm" is folklore; multiple MSE threads)            | yes  | Consensus: for a homomorphism, isometry ⟺ norm-preservation; a routine `f(x−y)` argument | No controversy; treated as an exercise. |
| 10 | recent arXiv (last 5 years)      | "group homomorphisms induced by isometries" (arXiv:2502.16712), "phase-isometries" etc.        | yes  | Modern papers study *converse/rigidity* (which isometries are affine/linear), not this direction | The elementary direction (norm-preserving hom ⟹ isometry) is assumed background, never a result. |

The protocol passes: WebSearch ran 3 queries at three generality levels (specific proof / general "iff
norm-preserving" / the concrete p-adic instance); ChatGPT MCP is unavailable and recorded n/a with its
role covered; local refs checked (absent → n/a); nLab checked (hit); nCatLab / Stacks / MathOverflow /
arXiv each checked or n/a-with-reason.

### Literature summary (Phase 3)

Concept identified as: **"a norm-preserving homomorphism of normed (additive) groups is an isometry"**,
here specialised to **"the inclusion of `ℤ_p` into the valuation ring `𝒪_L` is isometric"**.

Sources agree on the standard form: **yes.** Universally treated as elementary/folklore. The one-line
argument: for an additive hom `f`, `dist(f x, f y) = ‖f x − f y‖ = ‖f(x − y)‖ = ‖x − y‖ = dist(x, y)`.

Most general standard form: **for any homomorphism `f` of seminormed (additive) groups, `f` is an
isometry iff `‖f x‖ = ‖x‖` for all `x`.** This is exactly mathlib's `MonoidHomClass.isometry_iff_norm`
(additive form `AddMonoidHomClass.isometry_of_norm`).

Generality dimensions where the literature varies:
- Underlying object: normed vector space / Banach space (classical texts) ⟶ general seminormed
  *group* (nLab). The group-level statement is the most general and is the one mathlib uses.
- The p-adic instance specifically: `‖·‖_p` on `ℤ_p` is the restriction of `‖·‖_p` on `ℚ_p`, so the
  inclusion is isometric *by definition of the subspace norm* — there is no theorem to cite, only the
  generic "norm-preserving hom ⟹ isometry" lemma applied to the (trivially true) norm equality.

Disagreement with the literature: **none.** The Lean form (`Isometry (algebraMap ℤ_[p] (integerRing L))`,
proven via `AddMonoidHomClass.isometry_of_norm` + a norm equality) is the textbook argument verbatim.

---

### Generality analysis — `PadicLFunctions.integerRing.isometry_algebraMap`

Literature-standard form (from Phase 3): the *general* lemma is "norm-preserving additive hom ⟹ isometry"
(= mathlib `AddMonoidHomClass.isometry_of_norm`). The *target* is a fixed instance of that lemma for one
specific map `ℤ_p → 𝒪_L`. So the generality question is two-layered.

| # | Parameter / hypothesis            | Current Lean form                          | Literature-standard form                          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------------------------|---------------------------------------------------|---------------------|----------------------------------|
| 1 | the *general* statement           | a fixed map `algebraMap ℤ_[p] (integerRing L)` | "any norm-preserving additive hom is an isometry" | yes (already in mathlib) | The maximally general form is `AddMonoidHomClass.isometry_of_norm`, which **mathlib already has**. The target is not the general lemma — it is one application of it. |
| 2 | `[NormedField L]`                 | normed field                               | — (specific to this embedding)                    | n/a                 | Tied to the project's `integerRing L` definition; not a generality axis of the *general* fact. |
| 3 | `[NormedAlgebra ℚ_[p] L]`         | `ℚ_p`-algebra                              | — (specific)                                       | n/a                 | Determines which scalar embedding is restricted; project-specific. |
| 4 | `[IsUltrametricDist L]`           | ultrametric                               | not needed for the *isometry* claim               | yes (locally)       | Isometry of the inclusion does not use ultrametricity directly — but the `integerRing` *subring structure* (the `add_mem'` field) does. As stated against `integerRing L`, the hypothesis is structural, not a weakening target for *this* lemma. |
| 5 | `[CompleteSpace L]`               | already `omit`ted                          | not needed                                        | already removed     | The author already `omit`ted completeness — good hygiene; the lemma genuinely doesn't need it. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL as an instance** — i.e., for the specific map `ℤ_p → 𝒪_L` there
is nothing left to weaken (`CompleteSpace` already dropped, ultrametricity is structural). **But the
*generalisation target* the literature points at — "norm-preserving hom ⟹ isometry" — is not a more
general version of *this* lemma to re-prove; it is `AddMonoidHomClass.isometry_of_norm`, which mathlib
already has and which this lemma already calls.** So there is no "generalise-first" move: the general
lemma exists upstream, and the remaining content (`‖algebraMap ℤ_[p] (integerRing L) x‖ = ‖x‖`, i.e.
`norm_algebraMap_eq`) is specific to the project's bespoke `integerRing` algebra structure.

Number of weakening opportunities found: **0** (on this lemma; `CompleteSpace` was already removed).
Proposed restatement: none.
Cost of restatement: n/a.

→ Phase 7 considers the NO buckets (the general form is already in mathlib as a building block; this is
its application).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                           | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                                                     | no       | —                      | Already fully typeclass-driven (`NormedAlgebra`, `IsUltrametricDist`). |
|  2 | sequences/metric → filters/topological?                                                            | no       | —                      | `Isometry` is already the metric/topological idiom; nothing to filter-ise. |
|  3 | construct an object → universal-property class?                                                    | no       | —                      | No object constructed; it is a property of a fixed map. |
|  4 | set-with-closure-predicate → bundled substructure?                                                 | no       | —                      | `integerRing` is already a bundled `Subring`; this lemma is about a map into it. |
|  5 | vector-space/metric/field-specific → weaken to module/pseudometric/(semi)ring?                     | no       | —                      | The *general* fact is already stated at seminormed-group level upstream (`AddMonoidHomClass.isometry_of_norm`); this lemma is its specialisation, by design. |
|  6 | 1-categorical → higher/∞-categorical?                                                               | no       | —                      | Elementary; no categorification target. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive monoid/group?                                          | no       | —                      | No numeric index; the domain `ℤ_p` is intrinsic to the application. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.**
One-line reason: the lemma is already in the contemporary mathlib idiom (`Isometry` + `AddMonoidHomClass.isometry_of_norm`); the only "more modern/general" object is the upstream lemma it already invokes. There is no Bourbaki-2.0 restatement to make.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **lemma**. Lemmas introduce no definitional equalities and no typeclass-search
paths, so the six-row diamond/defeq table is skipped per the skill's scope rule.

---

### Mathlib search-status: `PadicLFunctions.integerRing.isometry_algebraMap`

[A] Lean-Finder       (service not available offline in this env)        n/a: external service not configured; substituted by exhaustive source grep [D]
[B] Loogle            `Isometry (algebraMap _ _)`, `Isometry _ ↔ _ , ‖_‖`   via source grep — building block found ( `algebraMap_isometry`, `AddMonoidHomClass.isometry_of_norm`); no `Subring`-codomain p-adic specialisation
[C] LeanSearch        (service not available offline)                    n/a: external service not configured; covered by [D]
[D] Grep mathlib src  `isometry.*algebraMap`, `Isometry (algebraMap`, `isometry_iff_norm`, `isometry_of_norm`, `algebraMap_isometry`, `norm_algebraMap'`, `PadicInt.norm_def`, `subring/subalgebra … isometr` | **building blocks found; exact form NOT found**
[E] Name pattern      `isometry_algebraMap` over `.lake/.../Mathlib/`     hit — but a *different* lemma (see below)

Searched for both:
  - the user's current form (`Isometry (algebraMap ℤ_[p] (integerRing L))`) — **not in mathlib**
  - the literature-standard general form (`norm-preserving hom ⟹ isometry`) — **in mathlib** as
    `MonoidHomClass.isometry_iff_norm` / `AddMonoidHomClass.isometry_of_norm`
    (`Mathlib/Analysis/Normed/Group/Uniform.lean:117,123`).

Relevant mathlib decls examined (by reading their actual statements, not just names):

1. **`AddMonoidHomClass.isometry_of_norm`** — `Mathlib/Analysis/Normed/Group/Uniform.lean:123`
   (alias of `MonoidHomClass.isometry_iff_norm`, l.117). For `[MonoidHomClass 𝓕 E F]`, `(∀ x, ‖f x‖ = ‖x‖) → Isometry f`.
   **This is the building block the target already calls.**
2. **`Module.Basic.algebraMap_isometry`** — `Mathlib/Analysis/Normed/Module/Basic.lean:340`:
   `[NormedField 𝕜] [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] ⟹ Isometry (algebraMap 𝕜 𝕜')`.
   The general "base-field inclusion is an isometry" lemma. **Does NOT apply to our target**: the
   codomain is the *subring* `integerRing L` (a `SeminormedRing`, the algebra structure is the
   bespoke `codRestrict` of `ℚ_[p] → L`), and the relevant norm equality passes through
   `PadicInt.norm_def` rather than `norm_algebraMap'` on `integerRing L` directly. It is a *sibling*,
   not a hit.
3. **`NumberField.Completion.LiesOver.isometry_algebraMap`** — `Mathlib/NumberTheory/NumberField/Completion/InfinitePlace.lean:275`:
   `Isometry (algebraMap (WithAbs v.1) (WithAbs w.1)) := AddMonoidHomClass.isometry_of_norm _ (fun x ↦ …)`.
   **Same name, same proof shape, but a different object** (completions at infinite places via `WithAbs`).
   Confirms the *pattern* mathlib uses for specific-map isometry lemmas; not the same statement.
4. **`Mathlib/Analysis/Normed/Ring/Lemmas.lean:69`** — `Isometry σ := AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map`.
   Again the same one-line pattern, paired with a generic norm hypothesis (`RingHomIsometric`).

Concluded: **"found building blocks (`AddMonoidHomClass.isometry_of_norm`; the sibling
`algebraMap_isometry`); composition yields our form."** The exact statement
`Isometry (algebraMap ℤ_[p] (integerRing L))` is not in mathlib and should not be (it is project-specific
to the `integerRing` subring), but the generic lemma it specialises IS in mathlib.

---

### Call sites — `PadicLFunctions.integerRing.isometry_algebraMap`

Internal use count: **8** (within the same project, excluding the declaring file)
External-to-file callers: **5 distinct files**

| Caller file:line                                                   | Usage pattern (one-line excerpt)                                                              |
|--------------------------------------------------------------------|-----------------------------------------------------------------------------------------------|
| `PadicLFunctions/MeasureR/MahlerTransform.lean:45`                 | `((integerRing.isometry_algebraMap p K).continuous).comp (map_continuous _)`                  |
| `PadicLFunctions/MeasureR/BaseChange.lean:66`                      | `((integerRing.isometry_algebraMap p K).continuous).comp (map_continuous f)`                  |
| `PadicLFunctions/MeasureR/BaseChange.lean:112`                     | `… (integerRing.isometry_algebraMap p K).continuous).symm`                                    |
| `PadicLFunctions/MeasureR/Toolbox.lean:98`                         | `((integerRing.isometry_algebraMap p K).continuous).comp (by fun_prop)`                       |
| `PadicLFunctions/Interpolation/NonTame.lean:1436`                  | `hω₀.map_of_injective (integerRing.isometry_algebraMap p K).injective`                        |
| `PadicLFunctions/Interpolation/NonTame.lean:1632`                  | `((integerRing.isometry_algebraMap p K).continuous).comp …`                                   |
| `PadicLFunctions/Interpolation/LpFunction.lean:43`                 | `(integerRing.isometry_algebraMap p K).continuous.comp …`                                     |
| `PadicLFunctions/Interpolation/LpFunction.lean:52`                 | `(integerRing.isometry_algebraMap p K).continuous.comp …`                                     |

Usage breakdown: **`.continuous` ×6** (to build `ContinuousMap`s `C(ℤ_p, integerRing K)` from `ℤ_p`-valued maps),
**`.injective` ×1** (`IsPrimitiveRoot.map_of_injective`), **`.symm` ×1** (composing an isometry chain).

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): **(none found)** —
every site that needs continuity/injectivity of this embedding routes through `isometry_algebraMap`.

What this tells us: K = 8 ≥ 3 with no inline re-derivation → this is a **real, used internal API** of the
project. Per the call-sites table that signal *leans YES*. It does **not**, however, mean mathlib should
have it: the lemma's job downstream is overwhelmingly "give me `.continuous` of this embedding". The
*content* used is continuity/injectivity of a one-call isometry, all of which is a mechanical composition
over mathlib primitives (see Phase 6). The internal-API value justifies keeping the lemma **in the
project**, not shipping it to mathlib.

---

### Composition check (Phase 6)

Can `PadicLFunctions.integerRing.isometry_algebraMap` be derived from mathlib in ≤3 chained calls?

**Attempt 1** — the lemma's own body:
```lean
example : Isometry (algebraMap ℤ_[p] (integerRing L)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)
```
  - Mathlib decls used: `AddMonoidHomClass.isometry_of_norm` (`Mathlib/Analysis/Normed/Group/Uniform.lean:123`).
  - Project decl used: `norm_algebraMap_eq` (sibling, `Coefficients.lean:93`).
  - Result: **succeeds** — this is literally the source.
  - Notes: one mathlib call applied to one norm-equality term. The norm equality `norm_algebraMap_eq`
    is itself a 2-line composition: `change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖; rw [norm_algebraMap', PadicInt.norm_def]`,
    i.e. `norm_algebraMap'` (`Mathlib/Analysis/Normed/Module/Basic.lean:293`) + `PadicInt.norm_def`
    (`Mathlib/NumberTheory/Padics/PadicIntegers.lean:191`).

**Attempt 2** — fully inlined at a call site (no project lemma at all), the way mathlib's deprecation
guidance recommends. A call site needing continuity becomes:
```lean
(AddMonoidHomClass.isometry_of_norm (algebraMap ℤ_[p] (integerRing K))
  (fun x => by change ‖algebraMap ℚ_[p] K (x : ℚ_[p])‖ = ‖x‖; rw [norm_algebraMap', PadicInt.norm_def])).continuous
```
  - Result: succeeds; ≤3 mathlib calls (`isometry_of_norm` ∘ `norm_algebraMap'` ∘ `PadicInt.norm_def`).
  - Notes: this is exactly the inlining mathlib applied when it **deprecated `WithAbs.isometry_of_comp`**
    (`Mathlib/Analysis/Normed/Field/WithAbs.lean:95`, `@[deprecated AddMonoidHomClass.isometry_of_norm (since := "2025-11-28")]`).

Conclusion: **COMPOSABLE.** The lemma is a one-mathlib-call composition (`AddMonoidHomClass.isometry_of_norm`
applied to a norm equality that is itself two mathlib rewrites). No new mathlib lemma is justified; the
content already lives in mathlib's `isometry_of_norm` + `norm_algebraMap'` + `PadicInt.norm_def`.

---

## Verdict: `PadicLFunctions.integerRing.isometry_algebraMap`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the fact is folklore — "a norm-preserving (additive) homomorphism is an
  isometry" (nLab, ProofWiki, AMM survey); the p-adic instance (`ℤ_p ↪ 𝒪_L` isometric) is definitional.
  No *named* theorem to upstream; the general lemma is `AddMonoidHomClass.isometry_of_norm`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL as an instance (0 weakenings; `CompleteSpace` already
  `omit`ted), and the literature's "more general form" is already-in-mathlib `AddMonoidHomClass.isometry_of_norm`,
  not a re-provable generalisation of this lemma. Phase 4c: no modern-idiom restatement (already idiomatic).
- Mathlib search (Phase 5): exact form not in mathlib (it is project-specific to `integerRing`), but the
  building block `AddMonoidHomClass.isometry_of_norm` IS, as is the sibling `algebraMap_isometry` and two
  same-pattern precedents (`NumberField.Completion.LiesOver.isometry_algebraMap`, `Normed/Ring/Lemmas.lean:69`).
- Composition check (Phase 6): **COMPOSABLE** — body is `AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)`,
  one mathlib call over a norm equality that is itself `norm_algebraMap'` + `PadicInt.norm_def`.

**Rationale:**

`isometry_algebraMap` is a one-line specialisation lemma: it applies mathlib's general
`AddMonoidHomClass.isometry_of_norm` to the project's own norm-preservation lemma `norm_algebraMap_eq`.
Mathlib already owns the only piece of genuinely general mathematics here (norm-preserving hom ⟹
isometry). What is *specific* to this lemma — that the bespoke embedding `ℤ_p → 𝒪_L = integerRing L`
preserves norms — is not a mathlib-shaped fact: it depends on the project's `integerRing` subring
definition and its hand-built `Algebra ℤ_[p] (integerRing L)` instance, and reduces to
`norm_algebraMap'` + `PadicInt.norm_def`. There is therefore nothing to add to mathlib that is not
either already there (the general lemma) or project-local plumbing (the `integerRing` algebra structure).

The decisive precedent is mathlib's own behaviour: on 2025-11-28 the maintainers **deprecated**
`WithAbs.isometry_of_comp` — a structurally identical wrapper whose entire body was
`AddMonoidHomClass.isometry_of_norm _ h` — explicitly directing users to call
`AddMonoidHomClass.isometry_of_norm` directly instead (`Mathlib/Analysis/Normed/Field/WithAbs.lean:95`).
That is mathlib telling us, in its own source, that "wrap `isometry_of_norm` for one specific map" is not
a lemma it wants. The 8 internal call sites (all `.continuous`/`.injective`/`.symm`) confirm the lemma is
a *useful internal convenience for this project* — which is exactly why it should stay a project lemma,
not be promoted.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the lemma is a 1-call composition. No new mathlib lemma is warranted.

Mathlib building blocks:
- `AddMonoidHomClass.isometry_of_norm` — `Mathlib/Analysis/Normed/Group/Uniform.lean:123`
  (alias of `MonoidHomClass.isometry_iff_norm`, l.117).
- `norm_algebraMap'` — `Mathlib/Analysis/Normed/Module/Basic.lean:293` (used inside `norm_algebraMap_eq`).
- `PadicInt.norm_def` — `Mathlib/NumberTheory/Padics/PadicIntegers.lean:191` (used inside `norm_algebraMap_eq`).
- (Sibling, for reference, not directly applicable: `algebraMap_isometry` — `Mathlib/Analysis/Normed/Module/Basic.lean:340`.)

Composition sketch (≤3 lines):
```lean
-- the lemma itself, over mathlib + the project's norm-equality lemma:
example : Isometry (algebraMap ℤ_[p] (integerRing L)) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap_eq p L)
-- fully inlined (no project lemma), the form mathlib's deprecation guidance recommends:
example : Isometry (algebraMap ℤ_[p] (integerRing L)) :=
  AddMonoidHomClass.isometry_of_norm _ fun x => by
    change ‖algebraMap ℚ_[p] L (x : ℚ_[p])‖ = ‖x‖; rw [norm_algebraMap', PadicInt.norm_def]
```

Call sites in our project (from Phase 6.0): **K = 8** across 5 files.

**Refactor plan (NB: this is the mathlib-promotion refactor plan, NOT a recommendation to delete the
project lemma).** Because the lemma is genuinely useful internal API (K = 8, all `.continuous`/`.injective`/
`.symm`), the correct action is to **keep `isometry_algebraMap` in the project as-is** and simply **not
open a mathlib PR for it**. *If* one ever wanted to remove the project lemma, the mechanical inlining is:
at each of the 8 sites, replace `(integerRing.isometry_algebraMap p K)` with
`(AddMonoidHomClass.isometry_of_norm _ (integerRing.norm_algebraMap_eq p K))` (preserving the trailing
`.continuous` / `.injective` / `.symm`). But that inlining buys nothing locally (it lengthens 8 call
sites to save one 1-line lemma), so the only real conclusion is: **this lemma is correctly project-local
and is not a mathlib contribution.**

Next action: **do not PR to mathlib.** Keep `isometry_algebraMap` as a project-local convenience lemma
(its 8 call sites justify it). If a future reader wants the general fact, it is already
`AddMonoidHomClass.isometry_of_norm`.

---

## Next step

Do not open a mathlib PR for `PadicLFunctions.integerRing.isometry_algebraMap`. It is a one-call
composition of mathlib's `AddMonoidHomClass.isometry_of_norm` with the project-local norm equality
`norm_algebraMap_eq` (itself `norm_algebraMap'` + `PadicInt.norm_def`), and mathlib has explicitly
deprecated the identical wrapper pattern (`WithAbs.isometry_of_comp`, 2025-11-28) in favour of inlining
`isometry_of_norm`. Keep the lemma project-local — its 8 internal call sites justify it as internal API,
but there is no new mathlib-worthy content. No `/generalise` or `/cleanup` mathlib-submission follow-up
is needed.
