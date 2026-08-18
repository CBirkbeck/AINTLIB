# `/mathlibable` report — `PadicLFunctions.Coleman.localUnitsOne`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final verdict: `NO-composable-from-mathlib`** — `localUnitsOne p n` is the principal
(1-)unit group `𝒰_{n,1} = 1 + 𝔭_n` of the local cyclotomic field `K_n`, the standard,
textbook object (Serre *Local Fields* Ch. IV; the bottom `U⁽¹⁾` of the filtration
`U⁽ⁱ⁾ = 1 + 𝔪ⁱ`). Mathlib carries this concept as `ValuationSubring.principalUnitGroup`,
and `ℂ_[p]` carries the `Valued ℂ_[p] ℝ≥0` structure whose `Valued.v.valuationSubring`
has carrier `{x | ‖x‖ ≤ 1}` and `principalUnitGroup` carrier `{u : ℂ_[p]ˣ | ‖u−1‖ < 1}` —
exactly the norm half of this def. The target is the 2-subgroup intersection
`localUnits p n ⊓ (Valued.v.valuationSubring).principalUnitGroup` embedded in `ℂ_[p]ˣ`.
No new mathlib lemma is justified: mathlib supplies the building block, the project's
own `localUnits` (= `𝒪_{K_n}ˣ`, itself not a standalone mathlib object) supplies the
subfield-relativization, and the composition is mechanical. This matches the house
verdict on the entire sibling family (`cycloClosureOne`, `cycloClosurePlus`,
`cycloClosureOnePlus`, … all `NO-composable-from-mathlib`).

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build stale/slow per task instruction); **reasoned from source** — the declaration, its full proof body, every in-file dependency (`localUnits`, `mem_localUnits_iff`, `norm_eq_one_of_mem_localUnits`, `mem_localUnitsOne_iff`), and the upstream definitions (`O`, `K`, `zetaSys`, `integerRing`) were read directly from `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean`, `…/Coleman/Tower.lean`, `…/Coefficients.lean`, plus the relevant mathlib sources under `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean` and `…/NumberTheory/Padics/Complex.lean`.
- decl `PadicLFunctions.Coleman.localUnitsOne`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:71`
- kind:                      `def` (constructs a `Subgroup ℂ_[p]ˣ` via the `where` builder)
- has sorry:                 no (whole file is `sorry`-free; the `def` is fully proved)
- module docstring summary:  Local unit groups of the cyclotomic tower (RJW §9, TeX 2471–2505): `𝒰_n = 𝒪_{K_n}ˣ`, the principal units `𝒰_{n,1}`, the `+`-subfield `K_n⁺`, the `ℤ_p`-power structure on principal units, and the towers `𝒰_{∞,1}`, `𝒰⁺_{∞,1}`. The congruence `u ≡ 1 (mod 𝔭_n)` is rendered as `‖u−1‖ < 1`.

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.localUnitsOne p n` is **a definition** of the following object:

> Let `p` be a prime and `n : ℕ`, and work inside `ℂ_[p]` (mathlib's `PadicComplex p`,
> the completed algebraic closure of `ℚ_p`, a complete nonarchimedean/ultrametric field).
> Let `K_n = ℚ_p(ξ_{p^n})` be the local cyclotomic field (`K p n : IntermediateField ℚ_[p] ℂ_[p]`)
> with ring of integers `𝒪_n = O p n = K_n.toSubring ⊓ integerRing ℂ_[p]` (the norm-unit
> ball of `K_n`) and maximal ideal `𝔭_n` (the open unit ball, `‖·‖ < 1`). Let
> `𝒰_n = 𝒪_{K_n}ˣ = localUnits p n` be the units of `𝒪_n`, realised as a subgroup of `ℂ_[p]ˣ`.
> Then `localUnitsOne p n = 𝒰_{n,1}` is the **group of principal units (1-units)** of `K_n`:
> the units of `𝒪_n` congruent to `1` modulo `𝔭_n`, i.e. `{u ∈ 𝒰_n : ‖u − 1‖ < 1}`.

In standard local-field notation this is `U⁽¹⁾(K_n) = U_1(K_n) = 1 + 𝔭_n`, the bottom of
the decreasing filtration `U⁽ⁱ⁾ = 1 + 𝔭ⁿ` of the unit group `𝒪_{K_n}ˣ`.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — the residue characteristic; fixes the ambient `ℂ_[p]`.
- `(n : ℕ)` — the tower level; selects the cyclotomic field `K_n = ℚ_p(ξ_{p^n})`.
- Ambient field `ℂ_[p]` carries `NontriviallyNormedField`, `IsUltrametricDist`, and `Valued ℂ_[p] ℝ≥0`; the norm is the project's `‖·‖`.

Hypotheses (Lean side): none beyond the parameters — it is an unconditional `Subgroup`.

Carrier (math): `{u : ℂ_[p]ˣ | u ∈ localUnits p n ∧ ‖(u : ℂ_[p]) − 1‖ < 1}`.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` (the four `Subgroup` fields are discharged: `mul_mem'`
via `(uv) − 1 = u(v−1) + (u−1)` + ultrametric + `‖u‖ = 1` on units; `one_mem'` since
`‖1−1‖ = 0 < 1`; `inv_mem'` via `u⁻¹ − 1 = u⁻¹(1−u)` + `‖u⁻¹‖ = 1`).

---

## Size classification (Phase 2a)

**Verdict: BIG.** It is a `def` introducing a **named mathematical structure** — the
principal-unit subgroup `𝒰_{n,1}` — which is a textbook concept (Serre, Neukirch,
Fesenko–Vostokov) and a primary §9/§11 object of the project's Iwasawa-main-conjecture
development (it carries its own `ℤ_p`-module structure further down the file).

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

---

## One-line check (Phase 2b)

Body line count: the `where` builder spans ~24 lines (the carrier is one set-builder line,
but the three group-closure obligations are substantive non-trivial proofs).
One-liner verdict: **MULTI-LINE** — the carrier predicate is one line, but the def bundles
three proved `Subgroup` closure fields (the `mul_mem'` proof uses the ultrametric inequality
and `norm_eq_one_of_mem_localUnits`; the `inv_mem'` proof uses `field_simp` + `norm_sub_rev`).
This is a bundled structure, not a one-line alias. The Phase-2b exemption table is therefore
**not applicable** (it fires only for genuine one-liners).

Conclusion: MULTI-LINE.

---

## PHASE 3 — Literature search (EXHAUSTIVE protocol)

### Literature search table

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `principal units 1-units local field definition u ≡ 1 mod maximal ideal valuation` | yes | `U⁽¹⁾ = 1 + 𝔪 = {u ∈ 𝒪ˣ : u ≡ 1 (mod 𝔪)}` | Wikipedia "Local field"; Berkeley/Cambridge "Local Fields" notes — `U⁽ⁿ⁾ = 1 + 𝔪ⁿ`, `U⁽¹⁾` *is* the principal units |
| 2 | WebSearch (general form / filtration) | `"principal units" group local field "U^(1)" filtration units higher unit groups Serre Local Fields` | yes | decreasing filtration `U⁽ⁱ⁾ = 1 + 𝔪ⁱ` of `𝒪ˣ`, `U⁽¹⁾` at the bottom | Fesenko–Vostokov *Local Fields and Their Extensions*; Springer "Filtration of the group of principal units …"; Serre *Local Fields* Ch. IV is the canonical reference |
| 3 | WebSearch (Iwasawa / Coleman aliases) | `one-units principal units cyclotomic Z_p extension Coleman power series Iwasawa theory local units` | yes | `𝒰_{n,1}` = norm-compatible 1-units in the `ℤ_p`-cyclotomic tower | arXiv:2309.15692 (the project's RJW source, "An introduction to p-adic L-functions"); jtnb "Semi-local units modulo cyclotomic units"; confirms the exact `𝒰_{n,1}`/`𝒰_{∞,1}` usage |
| 4 | WebSearch (ultrametric / Lubin–Tate) | `principal unit group ultrametric non-archimedean ‖u-1‖ < 1 subgroup units complete valued field Lubin-Tate` | yes | `K* ⊇ 𝒪* ⊇ U₁(K) = 1 + 𝔪 = {principal units}` (splits as topological groups) | Williams–Wüthrich "Local Fields" notes (Nottingham); confirms the `‖u−1‖ < 1` rendering equals `u ∈ 1 + 𝔪` for a complete DVR / valued field |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs/` symlink present in this checkout) | recorded n/a — neither directory exists |
| 6 | nLab | `nLab "group of units" principal units local ring filtration 1 + maximal ideal` | yes | `1 → 1 + 𝔪 → A* → (A/𝔪)* → 1`; the subgroup `1 + 𝔪` = principal units; filtration `{1 + 𝔪ⁱ}` with vector-space quotients | nLab "local ring"; confirms `1 + 𝔪` as the kernel of reduction to the residue field — exactly mathlib's `principalUnitGroupEquiv` |
| 7 | nCatLab (if categorical) | (same nLab corpus) | n/a | — | not a categorical concept beyond the residue-reduction exact sequence already captured in #6 |
| 8 | Stacks Project (if alg geom) | — | n/a | — | this is local-field / valuation-theory, not scheme-theoretic algebraic geometry; the relevant statement is the unit-group filtration of a DVR, covered by #1–#4, #6 |
| 9 | MathOverflow / Math.StackExchange | covered by the "filtration of units" / "principal units" hits in #1–#2 | yes | same `U⁽ⁿ⁾ = 1 + 𝔪ⁿ` filtration | standard MO/MSE answers reproduce Serre Ch. IV; nothing new beyond #1–#4 |
| 10 | recent arXiv (last 5 years) | within #3's results | yes | `𝒰_{n,1}`, `𝒰_{∞,1}` in cyclotomic Iwasawa theory | arXiv:2309.15692 (RJW, the project's own source) and arXiv:1511.04922 (Coates–Wiles / Lubin–Tate Iwasawa cohomology) both use the principal-unit tower |

ChatGPT MCP: **n/a — not available in this environment** (the deferred-tool surface exposed
no ChatGPT/OpenAI MCP tool; only `WebSearch`/`WebFetch`/`Monitor`/`TaskStop` resolved). The
four WebSearch channels at three generality levels + nLab + arXiv fully establish the standard
form, so the protocol's substantive requirement (standard form, generality, historical
evolution) is met without it. (The concept dates to Hensel/Hasse and is canonical since
Serre's *Corps Locaux*, 1962 — no formulational drift.)

### Literature summary (Phase 3)

Concept identified as: the **group of principal units** / **1-units** of a local (complete
discretely-valued, or here complete nonarchimedean) field, `U⁽¹⁾(K) = U_1(K) = 1 + 𝔪`, the
bottom term of the standard decreasing unit filtration `U⁽ⁿ⁾(K) = 1 + 𝔪ⁿ`. In the project's
Iwasawa setting it is `𝒰_{n,1}` (RJW arXiv:2309.15692 §9/§11, Eq. `eq:U1`, TeX 2494).

Sources agree on the standard form: **yes** — universally `{u ∈ 𝒪ˣ : u ≡ 1 (mod 𝔪)}`,
equivalently `{u ∈ 𝒪ˣ : v(u−1) ≥ 1}`, equivalently (for the rank-one / normed case)
`{u : Kˣ : ‖u − 1‖ < 1}` (the `‖u−1‖ < 1` rendering = `v(u−1) < 1` = "in the maximal ideal").

Most general standard form: for **any** valued field (or, with `v(u−1) < 1`, any field with a
valuation / nonarchimedean absolute value), the principal-unit group is `{u ∈ Kˣ : v(u−1) < 1}`,
and it is automatically a subgroup of `𝒪ˣ` (the `‖u−1‖<1`/`v(u−1)<1` condition forces
`‖u‖ = v(u) = 1`). It is the kernel of the reduction map `𝒪ˣ → (𝒪/𝔪)ˣ`.

Generality dimensions where the literature varies:
- **Base ring:** complete DVR (Serre) → general valuation ring / `ValuationSubring` (mathlib's
  framing) → rank-one / normed nonarchimedean field (the project's `ℂ_[p]` framing). The most
  general is the valuation-ring framing; the normed framing is the rank-one special case.
- **Ambient vs. relative:** principal units of `K` itself (`1 + 𝔪_K`) vs. principal units of a
  *subfield* `K_n ⊆ ℂ_[p]` tracked inside the larger field's units `ℂ_[p]ˣ`. The literature
  states the absolute case; the project deliberately uses the relative/embedded case so the whole
  cyclotomic tower lives in one ambient field `ℂ_[p]`.

Disagreement with the literature: **none** — the project's `‖u−1‖ < 1` is the standard 1-unit
condition; the only non-standard choice is the *embedded/relativized* presentation (subgroup of
`ℂ_[p]ˣ` carrying a `K_n`-membership conjunct), which is a formalization-design choice, not a
mathematical disagreement.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `principalUnitGroup(K) = {u ∈ Kˣ : v(u−1) < 1}`, the
kernel of `𝒪ˣ ↠ (𝒪/𝔪)ˣ`, stated over a valuation ring / `ValuationSubring`. Mathlib's exact
realization: `ValuationSubring.principalUnitGroup : Subgroup Kˣ`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | Ambient field `ℂ_[p]` | a single fixed `p`-adic complex field | any valued / rank-one normed field `K` | yes | the def uses only: `ℂ_[p]ˣ`, the ultrametric norm, `‖u‖ = 1` on units, `O p n` membership. Nothing is `ℂ_[p]`-specific except the *choice* of subfield `K_n`. Over an abstract `[Field K] [Valued K Γ₀]` the same construction is `(some ValuationSubring).principalUnitGroup`. |
| 2 | The conjunct `u ∈ localUnits p n` | `u, u⁻¹ ∈ O p n` (i.e. `u ∈ 𝒪_{K_n}ˣ`) | (no separate conjunct in the literature form) | yes — **redundant in the absolute case** | mathlib's `principal_units_le_units` proves `principalUnitGroup ≤ unitGroup` automatically: `v(u−1) < 1 ⟹ v(u) = 1`. In the *absolute* `K_n` case the `localUnits` conjunct is redundant. It is *not* redundant here only because the def lives in `ℂ_[p]ˣ` and uses `O_n` to pin down the **subfield** `K_n` (membership `u ∈ K_n`), which the norm condition alone cannot do. |
| 3 | The condition `‖u − 1‖ < 1` | ambient `ℂ_[p]`-norm | `v(u − 1) < 1`, `v` = valuation | equivalent (not weaker) | `norm_eq_norm` (`Mathlib/NumberTheory/Padics/Complex.lean:218`) gives `‖x‖ = Valued.v.norm x`; the `Valued ℂ_[p] ℝ≥0` valuation and the norm are interchangeable. So this matches the standard form exactly via a defeq/`simp` bridge. |
| 4 | The level `n` / subfield `K_n` | `K p n = ℚ_p(ξ_{p^n})` | any subfield / sub-DVR | yes (trivially) | `localUnitsOne` is parametric in `n`; the construction is uniform in the chosen `IntermediateField`. The cyclotomic specialization is project content, not a generality limit. |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (it specializes the abstract
principal-unit-group construction to `ℂ_[p]` + the subfield `K_n`, and carries one conjunct
that is redundant in the absolute literature form).

Number of weakening opportunities found: **2 substantive** (abstract the ambient field; drop the
redundant unit-conjunct in the absolute form — or recognise it as the `localUnits ⊓ principalUnitGroup`
intersection).

Proposed restatement (abstract, literature-standard): over `[Field K] [Valued K Γ₀]`, the
1-unit group **is already mathlib's** `(Valued.v.valuationSubring).principalUnitGroup` (for the
absolute case), and for a sub-DVR `𝒪' ⊆ K` it is `(𝒪' as ValuationSubring).principalUnitGroup`.

Cost of restatement to the abstract form: **MODERATE** — see Phase 6; mathlib already has the
abstract object, so the "restatement" is really a re-expression as `localUnits ⊓ (mathlib decl)`
rather than a fresh generalisation. (Per the skill, cost does not by itself change the bucket.)

### 4c. Modern mathlib-idiom restatement — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | yes | replace the hand-rolled `O p n`/`localUnits`/norm-condition stack with mathlib's `ValuationSubring` + `principalUnitGroup` API; give `K_n` (or `𝒪_n`) its `ValuationSubring ℂ_[p]`/`ValuationSubring K_n` | unlocks `principalUnitGroupEquiv` (1-units ≅ ker of residue reduction), `principalUnitGroup_le_principalUnitGroup`, the order embedding, and `quotientUnitGroupEquivResidueFieldUnits` |
| 2 | sequences/metric → filters/topological? | no | — | the def is purely algebraic (a subgroup); no convergence content here (that lives in `zpPow`, a different decl) |
| 3 | construct an object where a universal-property class would characterise it? | partial | `principalUnitGroup` is already characterised universally as `ker(𝒪ˣ → (𝒪/𝔪)ˣ)` (`principalUnitGroupEquiv`); the project's def is the explicit `{‖u−1‖<1}` construction | re-aiming at the kernel form composes with residue-field machinery |
| 4 | set-with-closure-predicate → bundled-substructure type? | yes | the project already uses the bundled `Subgroup` type (good); the deeper move is to source it from `ValuationSubring`, the bundled valuation-ring type, rather than the ad-hoc `Subring` `integerRing` | `ValuationSubring` lattice/order API, `principalUnitGroupOrderEmbedding` |
| 5 | vector-space/metric/field-specific → weaker typeclass? | yes | `ℂ_[p]` + `‖·‖` → `[Field K] [Valued K Γ₀]` (rank-one is a special case of general `Γ₀`-valued) | the entire `ValuationSubring` API is already at this generality in mathlib |
| 6 | 1-categorical → higher-categorical? | no | — | no categorification relevant to a unit subgroup |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | the index `n` already ranges over `ℕ` uniformly; no further index-generalisation is meaningful (it indexes the tower) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — mathlib's `ValuationSubring.principalUnitGroup` (with `ℂ_[p]`'s
`Valued.v.valuationSubring`) is the contemporary, API-rich formulation of the same object.

- Proposed mathlib-idiomatic restatement (absolute case, what mathlib already has):
  `(Valued.v.valuationSubring : ValuationSubring ℂ_[p]).principalUnitGroup : Subgroup ℂ_[p]ˣ`
  whose carrier is `{u | ‖u−1‖ < 1}` (via `norm_eq_norm`).
- Cost: **MODERATE** — the *absolute* 1-units of `ℂ_[p]` are immediate; the project's
  *subfield-relativized* `𝒰_{n,1}` then equals `localUnits p n ⊓` that group.
- Mathlib downstream this enables: `principalUnitGroupEquiv` (the residue-field-reduction kernel),
  `principalUnitGroup_le_principalUnitGroup`, the order embedding `principalUnitGroupOrderEmbedding`,
  `quotientUnitGroupEquivResidueFieldUnits`.
- Real mathematical improvement: it would connect `𝒰_{n,1}` to the residue-field exact sequence
  `1 → 𝒰_{n,1} → 𝒪_{K_n}ˣ → 𝕜ˣ → 1` for free, instead of re-deriving 1-unit facts by hand.

**Honesty bar.** The modernisation is real but its *target object already lives in mathlib*
(`principalUnitGroup`). So the contribution is **not** a new mathlib def — it is the recognition
that the project should *consume* `principalUnitGroup` (the `NO-composable` refactor), not that
mathlib is missing the principal-unit-group concept. This is precisely why the verdict is a NO
bucket, not `YES-but-generalise-first`: there is nothing new to upstream; mathlib has the concept,
and the project's job is to express its relativized form as a composition over it.

---

## PHASE 4.5 — Diamond / defeq risk assessment (`def`)

`localUnitsOne` is a `def` producing a `Subgroup ℂ_[p]ˣ`, carrying **no** attributes
(`@[simp]`/`@[reducible]`/`instance`), **no** `CoeFun`/`CoeSort`, and **no** typeclass output.
It is a plain bundled `Subgroup` value.

### 4.5a. Risk table

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | the output is data (`Subgroup ℂ_[p]ˣ`), not an instance; no typeclass-search path is created |
| 2 | Reducibility leak | none | not `@[reducible]`; the body is a `where` record, sealed — downstream code goes through `mem_localUnitsOne_iff` (the project provides it), not raw unfolding |
| 3 | Non-canonical unfolding | none | `mem_localUnitsOne_iff` is `Iff.rfl`, the intended membership API; no surprising `simp`/`rfl` behaviour observed in the 7 consumer files |
| 4 | Instance priority collision | n/a | not an `instance` |
| 5 | Universe-polymorphism issues | none | everything is at `Type 0` (`ℂ_[p]` is a fixed type); no universe variables |
| 6 | Coercion ambiguity | none | the only coercion is the standard `Subgroup ℂ_[p]ˣ → Set ℂ_[p]ˣ`; no competing `Coe` introduced |

### 4.5b. Risk verdict

Overall risk: **NONE.** No HIGH rows. (Were this ever upstreamed it would be a clean `Subgroup`
def, but per Phases 5–6 it should instead be re-expressed over mathlib's `principalUnitGroup`, so
the risk question is moot.)

---

## PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.Coleman.localUnitsOne`

- **[A] Lean-Finder** — **n/a: not available in this environment** (no Lean-Finder MCP tool surfaced). Substituted by authoritative grep over the pinned mathlib source (method D).
- **[B] Loogle** (`lean_loogle`) — **n/a: not available in this environment** (no Loogle MCP tool surfaced). Intended type-pattern query would have been `Subgroup _ˣ` with a `‖· - 1‖ < 1` / `Valuation.lt 1` body. Substituted by method D.
- **[C] LeanSearch** (`lean_leansearch`) — **n/a: not available in this environment** (no LeanSearch MCP tool surfaced). Intended NL query: "principal unit group / one-units / units congruent to 1 mod maximal ideal". Substituted by method D.
- **[D] Grep mathlib src** — terms tried: `principal.?unit`, `oneUnit`, `higherUnit`, `‖.*- 1‖ < 1`, `valuationSubring`, `Valued.*Cp`, `NormedField.*ValuationSubring`. **HITS** — `ValuationSubring.principalUnitGroup` (`.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean:634`) with full API (`mem_principalUnitGroup_iff:657`, `principal_units_le_units:653`, `principalUnitGroupEquiv:699`, order embedding `:683`, `quotientUnitGroupEquivResidueFieldUnits`); and `Valued ℂ_[p] ℝ≥0` + `norm_eq_norm` (`.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:206,218`), giving `Valued.v.valuationSubring : ValuationSubring ℂ_[p]` with carrier `{x | ‖x‖ ≤ 1}` (`Topology/Algebra/Valued/ValuationTopology.lean:321`).
- **[E] Name pattern** (`lean_local_search`) — **n/a: not available**; substituted by grep over project + mathlib for `localUnitsOne`, `principalUnit`, `oneUnit` — confirmed no project/mathlib clash on the name and located the mathlib `principalUnitGroup` family.

Searched for both:
- the user's current form (`{u ∈ 𝒰_n : ‖u−1‖ < 1}` embedded in `ℂ_[p]ˣ`) — no exact mathlib decl;
- the literature-standard form (`principalUnitGroup` of a `ValuationSubring`) — **present in mathlib**.

Concluded: **found the building blocks** — `ValuationSubring.principalUnitGroup` +
`ℂ_[p]`'s `Valued.v.valuationSubring` + `norm_eq_norm` give the *absolute* 1-units of `ℂ_[p]`
(`{u : ℂ_[p]ˣ | ‖u−1‖ < 1}`) exactly; the project's `localUnits p n` (= `𝒪_{K_n}ˣ`, itself a
project def with no standalone mathlib counterpart) supplies the subfield-relativization. The
project does **not** equip `ℂ_[p]`/`K_n` with the `ValuationSubring` framing (it uses a hand-rolled
`Subring integerRing`), so the exact `localUnitsOne` object is **not** literally in mathlib — but
it is a thin composition over a mathlib building block.

---

## PHASE 6 — Composition check (+ call-sites signal)

### 6.0. Call sites — `PadicLFunctions.Coleman.localUnitsOne`

Internal use count: **K ≈ 50** (occurrences of `localUnitsOne` outside the declaring file
`Iwasawa/LocalUnits.lean`; ~108 total, 58 in the declaring file).
External-to-file callers: **7 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `Iwasawa/CyclotomicUnits.lean:219` | `cycloClosure p n ⊓ localUnitsOne p n` (defines `cycloClosureOne`) |
| `Iwasawa/CyclotomicUnits.lean:553` | `zetaSysU p hn ∈ localUnitsOne p n` (the cyclotomic generator is a 1-unit) |
| `Iwasawa/CyclotomicUnits.lean:674` | `(hg : g ∈ localUnitsOne p n) (hgpow : g ^ (p−1) ∈ cycloClosureOne p n)` |
| `Iwasawa/ResidueField.lean:343` | `(mem_localUnitsOne_iff (p := p)).2 ⟨_, _⟩` |
| `IwasawaProof/Generators.lean:866,1019,1594,1729,1748` | repeated `g ∈ localUnitsOne p n` membership in the generator/`wGamma` construction |
| `IwasawaProof/FundamentalSequence.lean:812,1179` | `(mem_localUnitsOne_iff (p := p)).1/.2 …` in the fundamental-sequence proof |
| `IwasawaProof/GaloisAction.lean:423` | `(hu : u ∈ localUnitsOne p n)` — hypothesis of `mem_localUnitsOnePlus_iff_galAut_fixed` |
| `IwasawaProof/Main.lean:527,622,729,752` | `localUnitsOnePlus = localUnitsOne ⊓ localUnitsPlus`; `u.elems n ∈ localUnitsOne p n` |
| `Coleman/ColContinuity.lean:819,837,874` | `isClosed_localUnitsOne`; intersecting the cyclotomic closure with `localUnitsOne` |

Inline-derivation grep (was the equivalent re-derived elsewhere without `localUnitsOne`?):
**(none)** — every consumer goes through `localUnitsOne`/`mem_localUnitsOne_iff`; no file re-spells
`{u | u ∈ localUnits p n ∧ ‖u−1‖ < 1}` inline.

**Signal:** K ≫ 3 internal uses across 7 files, no inline re-derivation → this is **real,
load-bearing project API** (it is `𝒰_{n,1}`, a central object of the whole Iwasawa development;
it even carries a `ℤ_p`-`Module` structure further down `LocalUnits.lean`). The call-site pattern
alone leans YES-*; the verdict is nonetheless NO-composable because the object is the embedded
shadow of a mathlib concept (see below), exactly as for the sibling family.

### 6a. Composition attempt

Can `localUnitsOne p n` be derived from mathlib in ≤3 chained calls?

**Attempt 1** (absolute 1-units of `ℂ_[p]`, then intersect with `localUnits`):
```lean
-- 𝒰_{n,1} = 𝒰_n  ⊓  {u : ℂ_[p]ˣ | ‖u−1‖<1}, the latter = principalUnitGroup of ℂ_[p]'s valuation ring
localUnits p n ⊓ (Valued.v.valuationSubring : ValuationSubring ℂ_[p]).principalUnitGroup
```
- Mathlib decls used: `ValuationSubring.principalUnitGroup`, `Valued.v.valuationSubring`,
  `PadicComplex.norm_eq_norm` (norm = valuation bridge).
- Result: **partial** — the *set* is right, but matching the carrier requires rewriting
  `‖u−1‖ < 1` to `Valued.v ((u:ℂ_[p])−1) < 1` via `norm_eq_norm` (a non-`rfl` bridge), and the
  left conjunct `localUnits p n` is a **project** def, not mathlib. So this is a composition over a
  *mathlib building block plus a project def*, not over mathlib alone.

**Attempt 2** (literal mathlib hit for the whole object): would require `K_n` to carry a
`ValuationSubring K_n` and to state `𝒰_{n,1}` in `K_nˣ` as `(𝒪_{K_n}).principalUnitGroup`. The
project has neither the `ValuationSubring` instance nor the `K_nˣ` framing (it works in `ℂ_[p]ˣ`).
- Result: **fails** as a literal hit — no `≤1-line` `example : localUnitsOne … := mathlib_call`
  exists, because the subfield-relativized, `ℂ_[p]ˣ`-embedded object is genuinely not a single
  mathlib decl.

**Conclusion: NO-composable-from-mathlib (building-block composition).** Mathlib supplies the
principal-unit-group *building block* (`ValuationSubring.principalUnitGroup` over
`Valued.v.valuationSubring`); the target is `localUnits p n ⊓ <that block>` modulo the
`norm_eq_norm` bridge. The composition uses one mathlib building block + one project def + one
norm/valuation rewrite — a thin, mechanical assembly, not a new theorem and not a literal mathlib
object. This is the same shape, and the same bucket, as the sibling subgroup defs
(`cycloClosureOne`, `cycloClosurePlus`, `cycloClosureOnePlus`).

### 6b. Composition heuristics check
`Foo ⊓ Bar.principalUnitGroup` modulo a single `norm_eq_norm` rewrite sits in the "≤3 mathlib calls
+ a definitional bridge" band, not the "`rw [...]; ring_nf; aesop` proof in disguise" band — so it is
genuinely a composition. The only reason it is not `NO-mathlib-has-it` is that the left factor
(`localUnits`) is a project def and the relativization is real content.

---

## Verdict: `PadicLFunctions.Coleman.localUnitsOne`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the object is the **group of principal units / 1-units**
  `U⁽¹⁾(K_n) = 1 + 𝔭_n` (Serre Ch. IV; Fesenko–Vostokov; arXiv:2309.15692 §9/§11 `𝒰_{n,1}`) —
  a completely standard, canonical object, agreed across all four WebSearch channels + nLab + arXiv.
- Generality analysis (Phase 4): STRICTLY NARROWER THAN STANDARD — it specializes the abstract
  principal-unit-group construction to `ℂ_[p]` + the subfield `K_n` and carries a unit-conjunct
  redundant in the absolute case. Phase 4c: a modern mathlib idiom exists (`principalUnitGroup`),
  but **its target object already lives in mathlib**, so this is a consumption/refactor story, not
  an upstreaming story.
- Mathlib search (Phase 5): found the **building block** `ValuationSubring.principalUnitGroup`
  (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:634`) + `ℂ_[p]`'s `Valued.v.valuationSubring`
  + `norm_eq_norm` — gives the absolute 1-units of `ℂ_[p]` exactly; the exact subfield-relativized
  `localUnitsOne` is not a single mathlib decl.
- Composition check (Phase 6): **COMPOSABLE** as `localUnits p n ⊓ (Valued.v.valuationSubring).principalUnitGroup`
  (modulo the `norm_eq_norm` bridge) — a thin building-block composition, not a new lemma.

**Rationale (1–2 paragraphs):**

`localUnitsOne p n` is the principal-unit group `𝒰_{n,1}` of the local cyclotomic field `K_n` —
the textbook 1-unit group `1 + 𝔭_n`, the bottom of the standard unit filtration. Mathlib carries
exactly this concept as `ValuationSubring.principalUnitGroup`, defined as `{u : Kˣ | v(u−1) < 1}`
with the full surrounding API (it proves the units-containment automatically, identifies the group
with the kernel of reduction to the residue field, and gives the order embedding). Moreover `ℂ_[p]`
already has a `Valued ℂ_[p] ℝ≥0` instance whose `Valued.v.valuationSubring` is the norm-unit ball and
whose `principalUnitGroup` carrier is precisely `{u : ℂ_[p]ˣ | ‖u−1‖ < 1}` (the norm and valuation
agree, `PadicComplex.norm_eq_norm`). So the `‖u−1‖<1` half of this def is a literal mathlib object,
and the whole def is the intersection of the project's own `localUnits p n` (= `𝒪_{K_n}ˣ`) with that
mathlib group.

No new mathlib lemma is warranted. Mathlib is not missing the principal-unit-group concept; the
project simply re-derives the 1-unit condition by hand instead of consuming
`ValuationSubring.principalUnitGroup`. The remaining content beyond the mathlib block — the
subfield-`K_n`-relativization carried via `localUnits`/`O_n`, and the deliberate choice to embed the
tower in the single ambient field `ℂ_[p]ˣ` — is genuine **project formalization design**, not
upstreamable mathematics, and it is exactly why this is `NO-composable-from-mathlib` rather than
`NO-mathlib-has-it` (no `≤1-line` literal mathlib derivation of the embedded relativized object
exists) and not `YES-*` (there is nothing new to add to mathlib). This is consistent with the house
verdict on the entire sibling family of embedded `ℂ_[p]ˣ` unit subgroups (`cycloClosureOne`,
`cycloClosurePlus`, `cycloClosureOnePlus`, `cycloTower1`: all `NO-composable-from-mathlib`; the
analogous `globalUnits`: `NO-mathlib-has-it`).

**WHY not (refactor-actionable detail):**
- Mathlib has the building block: `ValuationSubring.principalUnitGroup`
  (`.lake/packages/mathlib/Mathlib/RingTheory/Valuation/ValuationSubring.lean:634`, with
  `mem_principalUnitGroup_iff:657`, `principal_units_le_units:653`, `principalUnitGroupEquiv:699`),
  together with `ℂ_[p]`'s valuation/norm infrastructure
  (`Valued ℂ_[p] ℝ≥0` and `PadicComplex.norm_eq_norm`, `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:218`)
  and `Valued.v.valuationSubring` (`Mathlib/Topology/Algebra/Valued/ValuationTopology.lean:321`).
- Mathlib building blocks: `ValuationSubring.principalUnitGroup`, `Valued.v.valuationSubring`,
  `PadicComplex.norm_eq_norm`; plus the project's own `localUnits p n` (no mathlib counterpart) for
  the subfield factor.

Composition sketch (≤3 lines, modulo the norm↔valuation bridge):
```lean
-- 𝒰_{n,1}  =  𝒰_n  ⊓  (1-units of ℂ_[p])
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    localUnitsOne p n
      = localUnits p n ⊓ (Valued.v.valuationSubring : ValuationSubring ℂ_[p]).principalUnitGroup := by
  ext u
  simp only [mem_localUnitsOne_iff, Subgroup.mem_inf,
    ValuationSubring.mem_principalUnitGroup_iff, ← PadicComplex.norm_eq_norm, Valued.v.norm_lt_one_iff]
  -- the right conjuncts coincide: ‖u−1‖ < 1  ↔  v(u−1) < 1
```

Call sites in our project (from Phase 6.0): **K ≈ 50 across 7 files** — this is heavily used,
load-bearing project API.

**Refactor plan (project-internal, NOT a deletion).** Because `localUnitsOne` is genuine,
load-bearing project API (50 uses, 7 files, plus a `ℤ_p`-module structure on it) and its content is
the *subfield-relativized* `𝒰_{n,1}`, the actionable refactor is **not** to delete it and inline a
mathlib call at every site. Instead:
1. Keep the def name `localUnitsOne` (the API anchor 7 files depend on), but **re-source its
   `‖u−1‖<1` half from mathlib**: either redefine `localUnitsOne p n := localUnits p n ⊓ (Valued.v.valuationSubring).principalUnitGroup`,
   or add the `simp`-lemma `localUnitsOne_eq_inf_principalUnitGroup` (the sketch above) so the
   project can transport mathlib's principal-unit API (residue-field reduction kernel, order facts)
   onto `𝒰_{n,1}` instead of re-deriving 1-unit closure by hand.
2. This is a single-file change in `Iwasawa/LocalUnits.lean`; the 7 consumer files are unaffected
   (they go through `mem_localUnitsOne_iff`, which stays `Iff.rfl` either way).
3. **Do NOT** PR `localUnitsOne` to mathlib — mathlib already has the principal-unit-group concept;
   the embedded/relativized presentation is project-specific.

Next action: leave `localUnitsOne` in the project; optionally land the project-internal refactor in
(1) to consume `ValuationSubring.principalUnitGroup`. Nothing to upstream.

---

## Next step

Leave `localUnitsOne` in the project (do not upstream — mathlib has the principal-unit-group concept
via `ValuationSubring.principalUnitGroup`). Optionally refactor `Iwasawa/LocalUnits.lean` so that
`localUnitsOne`'s `‖u−1‖<1` half is sourced from `(Valued.v.valuationSubring).principalUnitGroup`
(add `localUnitsOne_eq_inf_principalUnitGroup`), unlocking mathlib's residue-field-reduction kernel
and order API for `𝒰_{n,1}` instead of the hand-rolled 1-unit lemmas. The 7 downstream files are
untouched (they use `mem_localUnitsOne_iff`).
