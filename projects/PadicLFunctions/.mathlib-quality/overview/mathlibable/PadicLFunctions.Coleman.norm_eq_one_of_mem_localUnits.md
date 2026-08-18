# `/mathlibable` report — `PadicLFunctions.Coleman.norm_eq_one_of_mem_localUnits`

**Final verdict: `NO-composable-from-mathlib`** (mathlib has the building blocks; the result is a ≤3-call composition of the multiplicative norm — and mathlib additionally has the packaged form for the valuation-ring-unit framing).

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); reasoned from source — the decl and all its dependencies were read directly.
- decl `PadicLFunctions.Coleman.norm_eq_one_of_mem_localUnits`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:61`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Local unit groups of the cyclotomic tower (RJW §9) — `𝒰_n = 𝒪_{K_n}^×`, principal units `𝒰_{n,1}`, the `ℤ_p`-power structure on principal units, and the norm-compatible inverse systems `𝒰_∞`.

---

### Statement (Phase 1)

`norm_eq_one_of_mem_localUnits` is a theorem stating the following:

> Let `F = ℂ_[p]` be the field of `p`-adic complex numbers (mathlib's `PadicComplex p`), a complete non-archimedean normed field with a **multiplicative** absolute value `‖·‖`. Let `O = O p n ⊆ F` be its (relative) unit-ball subring — `O p n = (K p n).toSubring ⊓ integerRing ℂ_[p]`, where `integerRing ℂ_[p] = {x | ‖x‖ ≤ 1}` is the closed-unit-ball valuation ring. If `u` is a unit of `F` (`u : ℂ_[p]ˣ`) such that both `u` and `u⁻¹` lie in `O p n` (i.e. `u ∈ localUnits p n`), then `‖u‖ = 1`.

In valuation-theoretic terms: **a unit of the valuation ring (an element `x` with `x` and `x⁻¹` both of norm `≤ 1`) has norm exactly `1`.** This is one direction of the textbook characterisation `O^× = {x ∈ F : ‖x‖ = 1}`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime; fixes the field `ℂ_[p]`.
- `n : ℕ` — the tower level; only enters through `O p n` and plays **no role** in the proof (the proof uses only `O p n ⊆ {‖·‖ ≤ 1}` via `Subring.mem_inf … .2`).
- `u : ℂ_[p]ˣ` — a multiplicative unit of the field `ℂ_[p]`.

Hypotheses (Lean side):
- `hu : u ∈ localUnits p n` — unfolds (by `mem_localUnits_iff`, `:= Iff.rfl`) to `(u : ℂ_[p]) ∈ O p n ∧ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ∈ O p n`. The proof only consumes the norm-bound second component of each `Subring.mem_inf`, i.e. `‖u‖ ≤ 1` and `‖u⁻¹‖ ≤ 1`.

Conclusion (math): `‖u‖ = 1`.

Conclusion (Lean): `‖(u : ℂ_[p])‖ = 1`.

Proof body (3 substantive steps): extract `‖u‖ ≤ 1` and `‖u⁻¹‖ ≤ 1` from the two `Subring.mem_inf … .2`; prove `‖u‖ · ‖u⁻¹‖ = 1` via `← norm_mul`, `Units.mul_inv`, `norm_one`; close with `nlinarith` from the two `≤ 1` bounds and the product `= 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma feeding the `localUnitsOne` subgroup construction and the residue-field map; not a named theorem, not a new structure, not a project main result.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines.
One-liner verdict: n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The Phase-2b def-only exemption machinery does not apply.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "non-archimedean absolute value unit of valuation ring has norm one — element and inverse both norm ≤ 1" | yes | `O^× = {x ∈ F : ‖x‖ = 1}`; equivalently `x, x⁻¹ ∈ O ⇔ ‖x‖ = 1` | Stanford (Conrad) "Some basics concerning absolute values"; nLab "absolute value"; MathWorld "Non-Archimedean Valuation". Unanimous, textbook. |
| 2 | WebSearch (general form) | "multiplicative absolute value valuation ring unit group elements of value exactly 1 definition" | yes | `A^× = {x ∈ K : |x| = 1}`, the kernel of `K^× → Γ` (value group) | MIT 18.785 LectureNotes1; PlanetMath "valuation ring of a field"; nLab "valuation ring"; TU-Berlin valuation notes. The unit group is precisely the norm/valuation-`1` locus. |
| 3 | WebSearch (named-after / aliases) | "valuation ring units characterization v(x)=0; v(x) and v(1/x) nonnegative; p-adic" | yes | `U = {a ∈ V : v(a) = 0}`; from `v(a)+v(a⁻¹)=v(1)=0`, `a` is a unit iff `v(a)=0` | MIT 18.785 (2017) LectureNotes1; Kuhlmann *Valued Fields* Ch. 4 (`fvkuhlmann.de/bookch4.pdf`); Chaiser "Valuation Rings". Exactly the `‖u‖≤1 ∧ ‖u⁻¹‖≤1 ⟹ ‖u‖=1` argument. |
| 4 | ChatGPT MCP | (intended: "standard form of the unit-group characterisation of a valuation ring, generality, historical evolution") | n/a | — | ChatGPT MCP not configured in this environment (`mcp-needs-auth-cache.json`; no live endpoint). Compensated by 3 independent WebSearch channels + nLab + arXiv below, which already give unanimous agreement. |
| 5 | Local references | grep `.mathlib-quality/references/` for "valuation"/"unit" | n/a | — | No `references/` PDFs present for this project's mathlibable subtree; recorded n/a. The RJW source (TeX 2474) calls these "`𝒰_n = 𝒪_{K_n}^×`", confirming the object is exactly the valuation-ring unit group. |
| 6 | nLab | "valuation ring" → units | yes | "`x/y` is a unit of `O`: `x/y` and `y/x` belong to `O`" | nLab `valuation+ring` states the unit characterisation **verbatim** as the bilateral-membership condition — identical to the Lean hypothesis `u ∈ O ∧ u⁻¹ ∈ O`. |
| 7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept; it is an elementary valuation-theory fact. nLab (row 6) already covers it. |
| 8 | Stacks Project (if alg geom) | "valuation ring units" | n/a | (standard) | Stacks (Tag 00I8 ff.) defines valuation rings and their units identically (`x ∈ A` or `x⁻¹ ∈ A` for the field of fractions); not specific to algebraic geometry, so recorded n/a for "novelty" purposes — it merely re-confirms the standard form. |
| 9 | MathOverflow / Math.StackExchange | "units of valuation ring norm 1" generality | yes | Folklore: `|u|=1 ⇔ u ∈ O^×`; standard exercise | Recurs as a standard exercise; no novelty. Confirms the statement is considered too elementary to merit a named result. |
| 10 | recent arXiv (last 5 years) | "non-archimedean field valuation ring unit norm 1" | yes | Used as a background fact, never as a result | e.g. arXiv:2405.19270 (Adele-ring local compactness, Lean formalisation), arXiv:1910.05934 (Adic Spaces), arXiv:2304.09266 (perfectoid/Berkovich): all *use* `O^× = {‖·‖=1}` as a triviality, none state it as a theorem. |

Mathlib-search hosted tools attempted in this phase too (cross-referenced into Phase 5): Loogle returned **no results** for the inequality pattern `‖_‖ ≤ 1 → ‖_⁻¹‖ ≤ 1 → ‖_‖ = 1`; LeanSearch hosted API endpoints returned HTTP 404/405 (UI/endpoint changed) and are recorded n/a there.

### Literature summary (Phase 3)

Concept identified as: **the unit group of a valuation ring / unit ball of a non-archimedean (multiplicative) absolute value** — `O^× = {x ∈ F : ‖x‖ = 1}`. The target is the (forward) implication `x, x⁻¹ ∈ O ⟹ ‖x‖ = 1`.

Sources agree on the standard form: **yes** — unanimously (Conrad, MIT 18.785, Kuhlmann Ch. 4, nLab, PlanetMath, Stacks, MathWorld). The bilateral-membership phrasing in the Lean statement matches nLab's verbatim.

Most general standard form: For **any** field `F` with a multiplicative absolute value / Krull valuation `v` (not merely non-archimedean, not merely rank-one, not merely `ℂ_[p]`), the units of the valuation ring `O = {x : v(x) ≤ 1}` are exactly `{x : v(x) = 1}`; equivalently `x, x⁻¹ ∈ O ⇒ v(x) = 1`. The fact requires only that `v` is **multiplicative** (`v(xy) = v(x)v(y)`) and `v(1) = 1`; ultrametricity and the specific field `ℂ_[p]` are irrelevant to it.

Generality dimensions where the literature varies:
- **Field**: `ℂ_[p]` (current) → any normed field → any field with a (Krull) valuation. The literature standard is the last; the current is a maximally-special case.
- **Codomain of the absolute value**: `ℝ≥0` (rank-one / normed) → any `LinearOrderedCommGroupWithZero` (general Krull valuation). Mathlib's `Valuation.Integers` machinery already lives at the general `Γ₀` level.

Disagreement with the literature: none on content. The literature states this at vastly greater generality than the `ℂ_[p]`-specific Lean form, and treats it as a definition/triviality rather than a theorem.

---

### Generality analysis — `norm_eq_one_of_mem_localUnits`

Literature-standard form (from Phase 3): for any field `F` with a multiplicative valuation `v`, a unit of the valuation ring has value `1`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | Field `ℂ_[p]` | the `p`-adic complex numbers | any field with a multiplicative valuation `v` | yes (drastically) | Proof uses only `norm_mul`, `norm_one`, `Units.mul_inv`, `norm_nonneg` — i.e. that `‖·‖` is a multiplicative non-negative ring norm. Nothing `p`-adic, nothing about `ℂ_[p]`, no ultrametric inequality. |
| 2 | Subring `O p n` | relative unit ball `K_n.toSubring ⊓ integerRing ℂ_[p]` | the full valuation ring `O = {‖·‖ ≤ 1}` | yes | Only `O p n ⊆ {‖·‖ ≤ 1}` is used (`Subring.mem_inf … .2`). The `K_n.toSubring` factor and the level `n` are inert. The natural statement drops both. |
| 3 | Unit `u : ℂ_[p]ˣ` + `u, u⁻¹ ∈ O` | field unit, both in `O` | element with `‖x‖ ≤ 1 ∧ ‖x⁻¹‖ ≤ 1` (no separate `IsUnit` needed once `x ≠ 0`) | yes | The hypothesis is exactly the two norm bounds; bundling them as `u ∈ localUnits p n` is project packaging, not mathematical content. Mathlib's idiom is `Valued.integer 𝒪[K]` with `(u : 𝒪[K]ˣ)`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (massively — specialised to `ℂ_[p]` and to a relative tower subring, when the fact is field-and-valuation-agnostic). However, this does **not** push the verdict to `YES-but-generalise-first`, because Phase 5 finds the general form *already in mathlib* (and Phase 6 finds the specific form composable). Generality here is the reason it is **redundant**, not the reason to upstream a generalisation.

Number of weakening opportunities found: 3 (field, subring, hypothesis-bundling).

Proposed restatement (for completeness — but mathlib already has it, see Phase 5): for a normed field `K`, `‖u‖ ≤ 1 → ‖u⁻¹‖ ≤ 1 → ‖u‖ = 1` (`u ≠ 0`); equivalently `Valued.integer.norm_unit`/`isUnit_iff_norm_eq_one`.

Cost of restatement: CHEAP — but moot, since the general statement is not a contribution (mathlib has it).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let X be a foo" preambles → typeclasses/instances? | no | — | The hypotheses are already typeclass-driven (`NormedField`); nothing to bundle. |
| 2 | Sequences/metric → filters/topology? | no | — | No limit/convergence content; it is a single algebraic identity on norms. |
| 3 | Construction → universal-property class? | no | — | No object is constructed. |
| 4 | Set-with-closure-predicate → bundled substructure? | partially | Use mathlib's `Valued.integer 𝒪[K]` (already a bundled `Valuation.integer`) instead of the project's ad-hoc `integerRing L := {‖·‖ ≤ 1}` | This is a comment on the *parent* `integerRing`/`O` defs, not on this lemma; the lemma itself inherits whatever the unit-ball is. Mathlib already bundles it as `𝒪[K]`. |
| 5 | Vector-space/field-specific → weaken typeclass to module/(semi)ring? | yes (subsumed by 4a row 1) | Any field with a multiplicative valuation | Mathlib's `Valuation.Integers` lives at `LinearOrderedCommGroupWithZero Γ₀` generality already. |
| 6 | 1-categorical → higher-categorical? | no | — | Not categorical. |
| 7 | Concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure? | no | — | The level `n` is inert, not an index being summed/iterated over. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this lemma as a contribution). The only "modernisation" is to use mathlib's existing bundled valuation-ring `𝒪[K]` and its existing `norm_unit`/`isUnit_iff_norm_eq_one` lemmas — i.e. to *consume* mathlib, not to add a modernised version. There is no new mathlib-idiomatic statement here that mathlib lacks. One-line reason: the contemporary mathlib form of this fact already exists (`Valued.integer.isUnit_iff_norm_eq_one`), so there is nothing to upstream as a "modern idiom".

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `norm_eq_one_of_mem_localUnits`

[A] Lean-Finder       "unit of valuation ring norm 1"; "valued integer unit norm" — n/a: hosted Lean-Finder UI not reachable as a fetchable JSON endpoint in this environment. Compensated by [B]/[D]/[E] below, which located the packaged mathlib lemmas directly.
[B] Loogle            `‖_‖ ≤ 1 → ‖_⁻¹‖ ≤ 1 → ‖_‖ = 1` (via loogle.lean-lang.org/json) — **no hits** for the bare inequality pattern (it is not stated this way in mathlib). The fact lives under the *valuation-ring-unit* packaging instead (found via [D]).
[C] LeanSearch        "norm of element and its inverse both ≤ 1 implies norm = 1"; "unit of valuation ring has norm one" — n/a: leansearch.net `/search` and `/api/search` endpoints returned HTTP 405/404 (endpoint changed). Compensated by [D].
[D] Grep mathlib src  `norm_eq_one`, `norm_unit`, `isUnit.*norm`, `Valuation.*unit`, `integer.*norm` over `.lake/packages/mathlib/` — **HITS** (the packaged form):
  - `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:57` — `Valued.integer.norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1`
  - `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:53` — `Valued.integer.norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1`
  - `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:60` — `Valued.integer.isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1`
  - `Mathlib/RingTheory/Valuation/Integers.lean:168` — `Valuation.Integers.valuation_unit (hv : Integers v O) (x : Oˣ) : v (algebraMap O F x) = 1` (the general `Γ₀`-valued form)
  - `Mathlib/RingTheory/Valuation/Integers.lean:160` — `Valuation.Integers.isUnit_iff_valuation_eq_one` (general form)
  - Building blocks for the composition: `Mathlib/Analysis/Normed/Field/Basic.lean` — `norm_mul`/multiplicativity via `NormedDivisionRing`, `norm_inv:74`, `NormedDivisionRing.to_normOneClass:62` (`norm_one`); `Units.mul_inv`.
[E] Name pattern      `norm_eq_one`, `norm_unit`, `isUnit_iff_norm` — HITS as in [D]; also confirmed `Valued.integer.mem_iff : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1` (`LocallyCompact.lean:47`), so the project's `integerRing L = {‖·‖ ≤ 1}` is definitionally mathlib's `𝒪[K]`.

Searched for both:
  - the user's current form (`ℂ_[p]`, relative `O p n`, field unit with both-in-ring) — not present verbatim (it is project-specific packaging);
  - the literature-standard form (unit of the valuation ring has norm/value 1) — **present**, both as the norm-phrased `Valued.integer.norm_unit` / `isUnit_iff_norm_eq_one` and as the general valuation-phrased `Valuation.Integers.valuation_unit`.

Concluded:
  - **found building blocks** (`norm_mul`, `norm_one`, `Units.mul_inv`, `norm_nonneg`) — a ≤3-call composition yields our exact form;
  - **and additionally** found the packaged general result in mathlib (`Valued.integer.norm_unit` / `isUnit_iff_norm_eq_one`; general `Valuation.Integers.valuation_unit`). The packaged form is stated for `𝒪[K]ˣ` (units *of the valuation ring*), whereas the target's hypothesis is a *field* unit with `u, u⁻¹` separately in the ring — so applying the packaged form needs a small repackaging, while the building-block composition matches the target hypothesis directly. Either route is ≤3 lines and adds no new content.

---

### Call sites — `norm_eq_one_of_mem_localUnits`

Internal use count: **4** (within the project, excluding the declaring line `LocalUnits.lean:61`).
External-to-file callers: **1** distinct other file (`Iwasawa/ResidueField.lean`); 2 further uses are inside the declaring file itself (`LocalUnits.lean`, in `localUnitsOne`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `Iwasawa/LocalUnits.lean:79` | `rw [norm_mul, norm_eq_one_of_mem_localUnits p hu.1, one_mul]` (in `localUnitsOne.mul_mem'`) |
| `Iwasawa/LocalUnits.lean:93` | `norm_eq_one_of_mem_localUnits p ((localUnits p n).inv_mem hu.1), one_mul, norm_sub_rev]` (in `localUnitsOne.inv_mem'`) |
| `Iwasawa/ResidueField.lean:163` | `have hcnorm : ‖c‖ = 1 := norm_eq_one_of_mem_localUnits p ((mem_localUnits_iff p).2 ⟨u.mem (n+1), …⟩)` |
| `Iwasawa/ResidueField.lean:281` | `have hcnorm : ‖c‖ = 1 := norm_eq_one_of_mem_localUnits p ((mem_localUnits_iff p).2 ⟨u.mem n, …⟩)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): the 4 sites all *use* the lemma; no competing inline `nlinarith`/`norm_mul` re-derivation of "norm = 1 from both norms ≤ 1" was found elsewhere. (All ResidueField uses construct the `localUnits` membership from `NormCompatUnits.mem`/`inv_mem`, i.e. "`u` and `u⁻¹` both in `O p n`" — exactly the target hypothesis.)

What the pattern tells you: `K = 4` internal uses, no inline re-derivation → this is a **real, used project-internal helper** (a genuine API node for the cyclotomic-tower development). The call-sites signal therefore confirms the lemma earns its keep *inside the project*; it does **not** signal mathlib-worthiness, because the content it packages is the textbook valuation-ring-unit fact (Phase 3) that mathlib already provides (Phase 5). The right outcome is: keep it as a thin project-local convenience over a mathlib composition — not upstream it.

---

### Composition check (Phase 6)

Can `norm_eq_one_of_mem_localUnits` be derived from mathlib in ≤3 chained calls?

Attempt 1 (matches the existing proof — building-block composition):
```lean
example {u : ℂ_[p]ˣ} (h1 : ‖(u : ℂ_[p])‖ ≤ 1) (h2 : ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ ≤ 1) :
    ‖(u : ℂ_[p])‖ = 1 := by
  have hprod : ‖(u : ℂ_[p])‖ * ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  nlinarith [norm_nonneg (u : ℂ_[p]), norm_nonneg ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])]
```
  - Mathlib decls used: `norm_mul`, `Units.mul_inv`, `norm_one`, `norm_nonneg` (+ `nlinarith` to glue `a·b=1, a≤1, b≤1 ⊢ a=1`).
  - Result: **succeeds** — this is verbatim the current proof body, modulo extracting `h1`/`h2` from `Subring.mem_inf … .2`.
  - Notes: the glue is one `nlinarith` over an equality and two inequalities (or a two-step `le_antisymm`: `‖u‖ ≤ 1` and, from `‖u‖ = (‖u⁻¹‖)⁻¹ ≥ 1` since `‖u⁻¹‖ ≤ 1`, `1 ≤ ‖u‖`). Per the Phase-6 heuristics this is the "trivial composition / borderline real-proof" line; either way it carries **no novel mathematical content** and stays firmly in a NO bucket.

Attempt 2 (packaged route, via mathlib's valuation-ring units):
```lean
-- transport u : ℂ_[p]ˣ with u,u⁻¹ ∈ {‖·‖≤1} to a unit of 𝒪_ℂ_[p] = Valued.integer,
-- then apply Valued.integer.norm_unit
```
  - Mathlib decls used: `Valued.integer.mem_iff`, `Valued.integer.norm_unit` (or `isUnit_iff_norm_eq_one`).
  - Result: **succeeds in principle** but needs a small repackaging (build `𝒪_ℂ_[p]ˣ` from the field unit + both norm bounds), so it is *more* work than Attempt 1 for the same conclusion.

Conclusion: **COMPOSABLE** (Attempt 1, ≤3 mathlib calls + trivial arithmetic glue). The composition is exactly the existing proof.

---

## Verdict: `norm_eq_one_of_mem_localUnits`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): unanimous, textbook — the unit group of a valuation ring is `{‖·‖ = 1}`; nLab states the bilateral-membership form (`x, x⁻¹ ∈ O`) verbatim. Treated everywhere as a definition/triviality, never as a named theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER than the literature/mathlib form (specialised to `ℂ_[p]` and a relative tower subring), with `n` inert — but generality here is the reason it is *redundant*, not a reason to upstream a generalisation (Phase 5 finds the general form already in mathlib). Modern-idiom (4c): no new idiom to add.
- Mathlib search (Phase 5): found the building blocks (`norm_mul`, `norm_one`, `Units.mul_inv`, `norm_nonneg`) **and** the packaged general result (`Valued.integer.norm_unit` / `isUnit_iff_norm_eq_one` at `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean`; general `Valuation.Integers.valuation_unit`). The project's `integerRing L = {‖·‖ ≤ 1}` is definitionally mathlib's `𝒪[K]` (`Valued.integer.mem_iff`).
- Composition check (Phase 6): COMPOSABLE — a ≤3-call composition (verbatim the existing proof) yields the exact statement.

**Rationale:**

This lemma is the forward half of the single most basic fact in valuation theory — a unit of the valuation ring (an `x` with `x` and `x⁻¹` both of norm `≤ 1`) has norm exactly `1`. Every literature channel (Conrad, MIT 18.785, Kuhlmann Ch. 4, nLab, PlanetMath, Stacks, MathWorld) states it as a *definition* of the unit group `O^× = {‖·‖ = 1}`, not as a theorem; nLab even writes the bilateral-membership hypothesis identically to the Lean statement. The proof uses nothing `p`-adic and nothing about `ℂ_[p]` — only that `‖·‖` is a multiplicative non-negative ring norm — so the `ℂ_[p]`/`O p n`/level-`n` packaging is project bookkeeping with no mathematical content of its own.

Mathlib already covers both routes. The exact form is a ≤3-call composition of `norm_mul`, `Units.mul_inv`, `norm_one`, `norm_nonneg` (which *is* the current proof body), and mathlib additionally ships the packaged general statement `Valued.integer.norm_unit` / `isUnit_iff_norm_eq_one` (norm-phrased) and `Valuation.Integers.valuation_unit` (general `Γ₀`-valued), with `Valued.integer.mem_iff` identifying the project's `integerRing` with mathlib's `𝒪[K]`. There is therefore no new lemma to upstream: this belongs to the NO family. Between the two NO buckets, `NO-composable-from-mathlib` is the right one — the target's hypothesis is a *field* unit with `u, u⁻¹` separately in the ball (matching the composition directly), whereas the mathlib-packaged `NO-mathlib-has-it` route (`norm_unit`) is stated for `𝒪[K]ˣ` and would need a small repackaging at the boundary; the cleanest action is to inline the 3-line composition.

**WHY not (refactor-actionable):** Mathlib has the building blocks; the user's form is a ≤3 mathlib-call composition, and that composition is literally the lemma's own proof. No new lemma is justified for mathlib. Inside the project, the lemma is *used* (4 call sites, no inline re-derivation), so it is a reasonable project-local convenience — but it is **not a mathlib contribution**.

Mathlib building blocks:
- `norm_mul` — multiplicativity of the norm on a `NormedDivisionRing`/`NormedField` (`ℂ_[p]` is `NormedField`, `Mathlib/NumberTheory/Padics/Complex.lean:184`).
- `Units.mul_inv` — `↑u * ↑u⁻¹ = 1` for `u : Mˣ` (`Mathlib/Algebra/Group/Units/Defs.lean`).
- `norm_one` — via `NormedDivisionRing.to_normOneClass` (`Mathlib/Analysis/Normed/Field/Basic.lean:62`).
- `norm_nonneg` — `Mathlib/Analysis/Normed/Group/Basic.lean`.
- (Packaged alternatives, if the `𝒪[K]ˣ` framing is preferred at a call site: `Valued.integer.norm_unit` / `Valued.integer.isUnit_iff_norm_eq_one`, `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean:57,60`.)

Composition sketch (≤3 lines — verbatim the current proof, after extracting the two norm bounds from `Subring.mem_inf … .2`):
```lean
example {u : ℂ_[p]ˣ} (h1 : ‖(u : ℂ_[p])‖ ≤ 1) (h2 : ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ ≤ 1) :
    ‖(u : ℂ_[p])‖ = 1 := by
  have hprod : ‖(u : ℂ_[p])‖ * ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  nlinarith [norm_nonneg (u : ℂ_[p]), norm_nonneg ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])]
```

Call sites in our project (from Phase 6.0): **K = 4** (`LocalUnits.lean:79`, `LocalUnits.lean:93`, `ResidueField.lean:163`, `ResidueField.lean:281`).

Refactor plan (mathlib-facing): **do not upstream this lemma.** It is not a mathlib gap — mathlib has both the composition primitives and the packaged `Valued.integer.norm_unit`. No PR. For the project itself, the lemma may be kept as-is (a used, 3-line convenience), or, if a `/cleanup` pass wants to remove the wrapper, inline the composition above at the 4 call sites (each site already has `‖u‖ ≤ 1`/`‖u⁻¹‖ ≤ 1` available through `Subring.mem_inf … .2` from the `localUnits`/`NormCompatUnits` membership). Note the argument flow differs slightly per site: the `LocalUnits.lean` sites already feed `hu.1`/`(localUnits p n).inv_mem hu.1`; the `ResidueField.lean` sites construct membership from `u.mem`/`u.inv_mem`.

Next action: **No mathlib PR.** Keep the lemma project-local (it is used and harmless), or inline the ≤3-line composition at the 4 call sites if a cleanup pass prefers to drop the wrapper. Either way, this declaration is not a candidate for mathlib.

---

## Next step

No mathlib PR. This is the textbook valuation-ring-unit fact, already a ≤3-call composition of mathlib's multiplicative-norm primitives (and additionally packaged in mathlib as `Valued.integer.norm_unit` / `isUnit_iff_norm_eq_one`). Keep it as a project-local convenience (4 internal call sites, no inline re-derivation), or inline the composition at those sites during cleanup — do not upstream it.
