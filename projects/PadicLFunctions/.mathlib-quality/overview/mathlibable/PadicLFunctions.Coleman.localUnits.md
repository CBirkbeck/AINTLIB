# `/mathlibable` report — `PadicLFunctions.Coleman.localUnits`

**Final verdict: `NO-mathlib-has-it`** (mathlib has the abstract object
`ValuationSubring.unitGroup A : Subgroup Kˣ` — the unit group `𝒪_K^×` of a
valuation subring — with a 73-lemma API; the project's `localUnits p n` is that
object for the valuation ring `𝒪_{K_n}` of the local field `K_n`, deliberately
re-presented as a subgroup of `ℂ_[p]ˣ`. The embedding is a project-architecture
choice, not a mathlib gap.)

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build stale/slow per task instructions); **reasoned from source** — Phase 0 fallback. `LocalUnits.lean` and its dependency chain (`O`, `K`, `integerRing`, `ℂ_[p] = PadicComplex`, `zetaSys`) are all `sorry`-free and resolve.
- decl `PadicLFunctions.Coleman.localUnits`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/LocalUnits.lean:39`
- kind:                      `def` (a bundled `Subgroup ℂ_[p]ˣ` via the `where` anonymous-constructor syntax)
- has sorry:                 no (whole file: 0 `sorry`/`admit`)
- module docstring summary:  Local unit groups of the cyclotomic tower (RJW §9, TeX 2471–2505): `𝒰_n = 𝒪_{K_n}^×`, the principal units `𝒰_{n,1}`, the `+`-variants, and the norm-compatible towers `𝒰_∞`, all realised inside `ℂ_[p]`.

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.localUnits p n` is **a definition** of the following:

Let `p` be a prime and `n : ℕ`. Inside `ℂ_[p]` (mathlib's `PadicComplex p`, the
completion of an algebraic closure of `ℚ_p`), let `K_n = ℚ_p(μ_{p^n})` be the
local cyclotomic field, realised as the intermediate field
`K p n = ℚ_p⟮zetaSys p n⟯ : IntermediateField ℚ_[p] ℂ_[p]`, and let
`O_n = 𝒪_{K_n}` be its ring of integers, realised as the subring
`O p n = (K p n).toSubring ⊓ integerRing ℂ_[p]` (elements of `ℂ_[p]` that lie in
`K_n` **and** have norm `≤ 1`). Then `localUnits p n` is the **group of local
units `𝒰_n = 𝒪_{K_n}^×`** — the unit group of the ring of integers of the local
field `K_n` — presented as the subgroup of `ℂ_[p]ˣ` consisting of those units `u`
such that both `(u : ℂ_[p]) ∈ O_n` and `(u⁻¹ : ℂ_[p]) ∈ O_n`. Requiring a unit
*and its inverse* to lie in `O_n` is exactly the condition that `u` is a unit of
the ring `O_n` (a nonarchimedean integer ring, so this is equivalent to
`‖u‖ = 1`, cf. `norm_eq_one_of_mem_localUnits` in the same file).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (fixed at file scope).
- `n : ℕ` — the cyclotomic level (the field is `ℚ_p(μ_{p^n})`).
- ambient: `ℂ_[p]` = `PadicComplex p` (a complete, ultrametric-normed, algebraically closed `ℚ_[p]`-algebra).

Hypotheses (Lean side): none beyond the typeclasses; this is a plain `def`.

Carrier (math): `{ u ∈ ℂ_[p]ˣ : (u : ℂ_[p]) ∈ O_n ∧ (u⁻¹ : ℂ_[p]) ∈ O_n }`, with
the three `Subgroup` axioms discharged from `mul_mem`/`one_mem`/`mul_inv_rev` on
the subring `O_n`.

Conclusion (math): `localUnits p n = 𝒪_{K_n}^×`, the local unit group of `K_n`,
sitting inside `ℂ_[p]ˣ`.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` — n/a (definition, not a proposition).

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a `def` of a *named mathematical structure* — the local-unit group
`𝒪_{K_n}^×` of a `p`-adic local field — and it is foundational scaffolding for a
`## Main results`-level development (it is the `⊓`-factor of `cycloClosure`, RJW
TeX 3090, and the target of `globalUnits_le_localUnits`, RJW TeX 3084). Unit
groups of rings of integers of local fields are textbook objects (Neukirch,
Serre *Local Fields*, de Shalit), so they are essentially guaranteed to be in or
near the literature and mathlib.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.)

---

## One-line check (Phase 2b)

Body line count: ~15 substantive lines (a bundled `Subgroup` with a `carrier`
set-builder plus three non-trivial membership proofs `mul_mem'`/`one_mem'`/`inv_mem'`).
One-liner verdict: **MULTI-LINE**. The Phase-2b one-liner exemption analysis is
not triggered; this is a substantive bundled `def`, not a one-line alias.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "local units p-adic field ring of integers unit group U_n cyclotomic tower Iwasawa theory definition" | yes | `U_n` = principal units of `ℚ_p(ζ_{p^{n+1}})`; the (full) local units `𝒰_n = 𝒪_{K_n}^×` | Wikipedia *Iwasawa algebra*; arXiv:1907.06437 (2-adic log on principal units); the `U_n` of cyclotomic local fields is the central Iwasawa-theory object (Coates–Wiles, Coleman) |
| 2 | WebSearch (general/most-general form) | "unit group ring of integers local field finite extension Q_p definition O_K^times maximal order" | yes | for `F/ℚ_p`: `𝒪_F^× = 𝔲_F^0`; higher unit groups `U_F^r := 1 + 𝔪^r 𝒪_F`; decomposition `F^× ≅ π^ℤ × μ_{q−1} × U_F^1` | **MIT 18.785 Lecture 24** (local class field theory) + W&M "Local fields and p-adic groups" notes — the maximally general standard form is "any finite extension `F/ℚ_p`" (indeed any local/complete-DVR field) |
| 3 | WebSearch (named-after / aliases) | "principal units local field 1+m higher unit groups filtration U^(n) nonarchimedean valuation ring standard" | yes | `U_L^n := 1 + P_L^n` (principal units of level `n`); `U_L^i = 1 + 𝔪_L^i` give a clopen neighbourhood base of `1`; `U_L^0 = 𝒪_L^×` | Kedlaya CFT §4.4 (ramification filtration); Springer "Filtration of the group of principal units"; the `𝒰_n`/`𝒰_{n,1}` split is exactly `U^0`/`U^1` |
| 4 | WebSearch (the source-context form) | "Rubin Euler systems / de Shalit Iwasawa theory of elliptic curves local units U_n principal units norm-compatible cyclotomic" | yes | de Shalit, *Iwasawa theory of elliptic curves with CM* (1987) — "formal groups and local units"; Rubin, "Local units, elliptic units, Heegner points…" (Invent. 1987) | confirms the *norm-compatible system of local units* `𝒰_∞ = lim←_n 𝒰_n` (the file's `NormCompatUnits` / `unitsTower1`) is the standard Coleman/de Shalit/Coates–Wiles setup |
| 5 | ChatGPT MCP | "standard definition of the local units `𝒪_{K_n}^×` and principal units `1+𝔭_n` of a p-adic cyclotomic field, generality, historical evolution" | n/a | — | **ChatGPT MCP server not configured** in this environment (only Asana/Atlassian/Box/Canva/Figma/HubSpot/Intercom/Linear/Notion/monday MCP servers present, all unauthenticated). Recorded n/a; compensated with deeper WebSearch (#1–4) + WebFetch (#6) + exhaustive mathlib grep (Phase 5 [D]). |
| 6 | nLab | "ring of integers" (non-archimedean local field) | partial | "Given a local non-archimedean field `F`, its ring of integers `𝒪_F` is the subring of elements of norm `≤ 1`." | https://ncatlab.org/nlab/show/ring+of+integers — confirms the `𝒪_F = {‖·‖ ≤ 1}` anchor (exactly the project's `integerRing`/`O_n`), but does not separately name `𝒪_F^×`/principal units. |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; the universal property of `𝒪_F` is "valuation ring / maximal order", already covered by #6 + the mathlib `ValuationSubring` API. No higher-categorical form. |
| 8 | Stacks Project | "valuation ring units / ring of integers of a local field" | n/a | (valuation rings are in Stacks, but `𝒪_F^×` of a p-adic field is not an alg-geom-specific object) | Recorded n/a — local-field unit groups are number theory; the valuation-ring primitive is generic commutative algebra mathlib already carries (`ValuationSubring`). |
| 9 | MathOverflow / Math.SE | "structure of the unit group of a local field, principal units 1+m" | yes (folded into #2/#3) | uniform: `𝒪_F^× = μ_{q−1} × (1 + 𝔪)`, with `1 + 𝔪` the principal units | the standard structure theorem; consistent with #2/#3. No new variant. |
| 10 | recent arXiv (last 5 yr) | the source: RJW arXiv:2309.15692 §9 (TeX 2471–2505) | yes | `𝒰_n = 𝒪_{K_n}^×`, `𝒰_{n,1} = {u : u ≡ 1 mod 𝔭_n}`, `𝒰_∞ = lim← 𝒰_n` | RJW, *An introduction to p-adic L-functions* — the project's reference. The file docstring cites "RJW TeX 2474" for `𝒰_n`; arXiv:1907.06437 is a fresh (2019) instance of the same `U_n`. |

### Literature summary (Phase 3)

Concept identified as: **the group of local units `𝒪_{K_n}^×` (notation `𝒰_n`,
`U_{K_n}^0`, `𝔲_{K_n}^0`) of the ring of integers of a p-adic local field** —
here the cyclotomic local field `K_n = ℚ_p(μ_{p^n})`. Its principal-unit
subgroup `𝒰_{n,1} = 1 + 𝔭_n` (`localUnitsOne`) is the level-1 piece of the
standard higher-unit filtration `U_L^i = 1 + 𝔪^i`. The norm-compatible inverse
limit `𝒰_∞ = lim←_n 𝒰_n` (`NormCompatUnits`/`unitsTower1`) is the Coleman /
de Shalit / Coates–Wiles object.

Sources agree on the standard form: **yes.** Uniformly, for a local field `L`,
`𝒪_L^× = {u ∈ 𝒪_L : u⁻¹ ∈ 𝒪_L} = {x ∈ Lˣ : v(x) = 1} = {‖x‖ = 1}`, with
`𝒪_L = {‖·‖ ≤ 1}` the valuation ring. The project's two carrier conditions
(`u ∈ O_n` and `u⁻¹ ∈ O_n`) are a literal transcription of "`u` is a unit of
`𝒪_{K_n}`", with `K = K_n` *realised inside `ℂ_[p]`* (so "`∈ 𝒪_{K_n}`" splits
into "`∈ K_n`" + "`‖·‖ ≤ 1`").

Most general standard form: the unit group of the valuation ring of an arbitrary
nonarchimedean valued field (equivalently `(𝒪_L)ˣ` for `L` a local field /
complete DVR field). Mathlib's exact abstract object is
`ValuationSubring.unitGroup`.

Generality dimensions where the literature varies:
- base field: cyclotomic `ℚ_p(μ_{p^n})` (the file) ⊂ any finite extension `F/ℚ_p`
  ⊂ any local field ⊂ any nonarchimedean valued field (the maximal standard form,
  = mathlib's `ValuationSubring K` for any `K`).
- ambient realisation: *abstract* (`𝒪_L^×` as a `Subgroup Lˣ`, the universal
  literature/mathlib choice) vs. *embedded in a fixed completion* `ℂ_[p]` (the
  file's project-specific choice — RJW's "everything inside `ℂ_p`" convention,
  decomposition replan R10.1/R11.7).

Disagreement with the literature: **none mathematically.** The only divergence is
*presentation*: the literature/mathlib state `𝒪_L^×` as a subgroup of `Lˣ`; the
file embeds it as a subgroup of `ℂ_[p]ˣ` and re-derives "is in `𝒪_{K_n}`" from
"`∈ K_n` ∧ `‖·‖ ≤ 1`".

If the literature search had returned nothing, that would have signalled a
too-narrow object — but it did not: the concept is textbook-central. So the
"literature-absence ⇒ BORDERLINE" branch does **not** apply here.

---

## Generality analysis — `localUnits` (Phase 4)

Literature-standard form (from Phase 3): the unit group `(𝒪_L)ˣ` of the valuation
ring `𝒪_L` of a nonarchimedean valued field `L` (mathlib's
`ValuationSubring.unitGroup`).

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field | `K_n = ℚ_p(μ_{p^n})` (cyclotomic, via `K p n`) | any local field / nonarch. valued field `L` | yes | nothing in the *definition* uses cyclotomicity; `𝒪_L^×` makes sense for any valued field. Mathlib's `ValuationSubring.unitGroup` is exactly this maximal form. |
| 2 | ambient ring | embedded in `ℂ_[p]`; "`∈ 𝒪_{K_n}`" = "`∈ K p n` ∧ `‖·‖ ≤ 1`" | abstract `𝒪_L = ValuationSubring`/valuation ring of `L` | yes (and is the *idiomatic* form) | the `ℂ_[p]` embedding is a project convenience, not a mathematical necessity; the abstract `unitGroup` lives in `Lˣ`, dropping the ambient field. |
| 3 | unit condition split | two conditions `u ∈ O_n` **and** `u⁻¹ ∈ O_n` | one condition: `A.valuation x = 1` (membership of a *unit* in the valuation subring already forces the inverse) | yes | in the abstract form a single "`v(x) = 1`" subsumes both; the split exists only because the file works with `ℂ_[p]ˣ`, not `(𝒪_{K_n})ˣ`. (The file's own `norm_eq_one_of_mem_localUnits` proves the equivalence.) |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only, and
embedded in `ℂ_[p]` rather than abstract). However — and this is the decisive
point — the strictly-more-general *and* idiomatic form is **already in mathlib**
as `ValuationSubring.unitGroup A : Subgroup Kˣ` (see Phase 5). So this is **not**
a "generalise-then-PR" situation; the generalised form is not a gap. Number of
weakening opportunities found: 3 (rows above), **all of which land on an object
mathlib already has** (`unitGroup`, with `principalUnitGroup` covering the
`localUnitsOne` companion).

Proposed restatement (for the record, = the existing mathlib object):
`(𝒪_{K_n}).unitGroup : Subgroup K_nˣ` where `𝒪_{K_n} : ValuationSubring K_n` is
the valuation ring of `K_n` (then transported into `ℂ_[p]ˣ` if the project still
wants the embedded view).

Cost of restatement: n/a — it would be deleting the project def in favour of a
mathlib def, not re-proving a generalisation. Bridging the *embedded* form used
in this project to the abstract form is real work (the project never equips `K_n`
with a `Valued`/`ValuationSubring` structure — `O p n` is a hand-built
`Subring ℂ_[p]`), but that bridge is a project-internal refactor, not a mathlib
contribution — see Phase 7.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | yes | equip `K_n` with `[Valued K_n …]`/its `ValuationSubring`, then use `.unitGroup` instead of a hand-rolled `ℂ_[p]ˣ` subgroup | the whole `ValuationSubring` unit API (order embeddings, residue-field maps, `principalUnitGroupEquiv`) |
| 2 | sequences/metric → filters/topological? | no | — | the *def itself* has no convergence content; it is purely algebraic. (Topology enters only in the companion `isClosed_localUnits`, which is separate.) |
| 3 | construct an object → universal-property class? | yes | `ValuationSubring K` *is* the universal (valuation-ring) characterisation; `.unitGroup` is its unit group | composes with `IsLocalRing.ResidueField`, `principalUnitGroup`, the valuation lattice |
| 4 | set-with-closure-predicate → bundled-substructure type? | yes (already half-done) | the file already bundles a `Subgroup`; the idiomatic target derives it from a bundled `ValuationSubring`, so the `Subgroup`/lattice ops compose with the valuation-subring lattice (`unitGroup_le_unitGroup` ↔ `A ≤ B`) | the `ValuationSubring K ↪o Subgroup Kˣ` order embedding, `eq_iff_unitGroup` |
| 5 | field/metric-specific → weaken typeclasses? | yes | drop `ℂ_[p]` entirely; `unitGroup` needs only a `ValuationSubring` of *any* field `K` | works for every valued field uniformly; no scalar-tower assumptions |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no (the `n` indexes the *field* in the tower, not an algebraic structure to generalise) | — | the `n`-tower is intrinsic to Iwasawa theory; not a spurious concrete index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, and it is **already realised in mathlib** as
`ValuationSubring.unitGroup` (+ `principalUnitGroup`). Crucially this does **not**
flip the verdict to YES-but-generalise-first: the modern/general form is not a
missing contribution to build — it *exists in mathlib* with a 73-lemma API in
`Mathlib/RingTheory/Valuation/ValuationSubring.lean`. Hence the modern-idiom
finding *reinforces* `NO-mathlib-has-it`; it does not create a YES.
Real mathematical improvement of the idiomatic form: it unlocks the entire
`ValuationSubring` unit ecosystem (the `unitGroup`/`principalUnitGroup` order
embeddings, the residue-field unit map, `principalUnitGroupEquiv`) for free —
none of which the bespoke `ℂ_[p]ˣ`-subgroup can reach without re-proving.

---

## Diamond / defeq risk — `localUnits` (Phase 4.5)

(`def`, so the phase runs. It is a *plain* `def` returning a `Subgroup`, not an
`instance`/`class`/coercion.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | it is a `def` returning a `Subgroup`, not an `instance`; it participates in no typeclass-search path. |
| 2 | Reducibility leak | none | no `@[reducible]`; sealed bundled `Subgroup`, exposed only through `SetLike` membership + the hand-written `mem_localUnits_iff`. |
| 3 | Non-canonical unfolding | low | `mem_localUnits_iff` (`:= Iff.rfl`) unfolds `· ∈ localUnits p n` to the two carrier conditions; this is the intended API and is unsurprising. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types concrete (`ℂ_[p]ˣ`, `ℕ`); no universe variables. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`; the only coercion is the standard `Subgroup → Set` from `SetLike`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** Top risks: none. (Recorded for completeness; the verdict
is a NO bucket, so the risk does not gate it.)

---

## Mathlib search-status: `localUnits` (Phase 5)

[A] Lean-Finder       (web service) — **n/a: endpoint not reachable from this environment**; conceptual phrasing folded into [C]/[D]. The object is the well-known `ValuationSubring.unitGroup`, confirmed by grep [D].
[B] Loogle            (`lean_loogle` MCP) — **n/a: no Lean MCP search tool present in this environment** (deferred-tool search returned none). Type-pattern intent `Subgroup (Units ?K)` cut out by a valuation/integrality covered via grep [D].
[C] LeanSearch        (`lean_leansearch` MCP) — **n/a: no Lean MCP search tool present**; `LeanSearchClient` package is vendored but the live JSON endpoint is not callable here. NL intent "unit group of the ring of integers / valuation subring of a local field" resolved directly via grep [D].
[D] Grep mathlib src  `unitGroup`, `principalUnitGroup`, `Subgroup .*ˣ`, `ValuationSubring`, `PadicComplexInt`, `localUnits`/`principalUnits`, `LocalField` over `.lake/packages/mathlib/Mathlib/` — see hits below.
[E] Name pattern      grep `localUnits`/`principalUnits` over all of mathlib → `principalUnitGroup`/`principal_units_le_units` in `ValuationSubring.lean`; **no decl named `localUnits`**; no `LocalField` class in this pin.

Searched for both:
- the user's current form (embedded `Subgroup ℂ_[p]ˣ` cut out by `∈ O_n` for the
  *subring* `O_n = K_n.toSubring ⊓ integerRing`) — **not in mathlib** (no decl
  cuts a `Subgroup ℂ_[p]ˣ` out by membership in a subfield's integer ring; this
  embedded presentation is project-specific).
- the literature-standard / abstract form (`(𝒪_L)ˣ` for a valued field `L`) —
  **in mathlib**, with rich API:
  - `ValuationSubring.unitGroup A : Subgroup Kˣ` (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:492`), with `mem_unitGroup_iff : x ∈ A.unitGroup ↔ A.valuation x = 1`, `unitGroupMulEquiv : A.unitGroup ≃* Aˣ` (so it literally *is* the units of the integer ring), the order embedding `unitGroup_le_unitGroup`/`eq_iff_unitGroup`, and `unitGroupToResidueFieldUnits`.
  - `ValuationSubring.principalUnitGroup A : Subgroup Kˣ` (`:634`), carrier `{x | A.valuation (x − 1) < 1}` — **exactly** the project's `localUnitsOne` companion (`‖u − 1‖ < 1`), with `principal_units_le_units`, `mem_principalUnitGroup_iff`, the order embedding, and `principalUnitGroupEquiv` to the kernel of the residue map. (73 `unitGroup`/`principalUnitGroup` lemmas in that one file.)
  - Mathlib's own `ℂ_[p]` integer ring `𝓞_ℂ_[p] = PadicComplexInt p` (`Mathlib/NumberTheory/Padics/Complex.lean:251`) is itself a `ValuationSubring ℂ_[p]`, so `(𝓞_ℂ_[p]).unitGroup` already exists — **but it is NOT `localUnits p n`** (it is the unit group of the *whole* `ℂ_[p]`-valuation ring: every norm-1 unit of `ℂ_[p]`, not just those in the subfield `K_n`).
  - Nearest *S-unit* analogue: `Set.unit S K : Subgroup Kˣ` (`Mathlib/RingTheory/DedekindDomain/SInteger.lean:108`) with `Set.unitEquivUnitsInteger` — but that is S-arithmetic of a Dedekind fraction field, not the single-place local unit group.
  - **No `LocalField` class** and **no `localUnits`-by-name** decl exist in this mathlib pin.

Concluded: **"found in mathlib as `ValuationSubring.unitGroup` (with `principalUnitGroup` for the `localUnitsOne` companion); strictly more general (any valued field) and idiomatic; the project's `localUnits p n` is the same mathematical object — `(𝒪_{K_n})ˣ` — re-presented as a subgroup of `ℂ_[p]ˣ`."** The project's *exact embedded form* is not in mathlib (correctly — the embedding is a project-local device; the general form is what mathlib carries). The form does **not** follow from the mathlib decl in a literal ≤1 line (see Phase 6 + the Phase-7 caveat): bridging requires equipping `K_n` with a `ValuationSubring` and transporting along `K_n ↪ ℂ_[p]`.

---

## Call sites — `localUnits` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file
`Iwasawa/LocalUnits.lean`): **5 real code uses across 2 files** (plus 1
docstring mention in a third).

External-to-file callers: **2 files in code** (`Iwasawa/CyclotomicUnits.lean`,
`Coleman/ColContinuity.lean`); 1 docstring-only file (`IwasawaProof/GaloisAction.lean`).

| Caller file:line | Usage pattern (one-line excerpt) | Code or comment? |
|------------------|----------------------------------|------------------|
| Iwasawa/CyclotomicUnits.lean:157 | `theorem globalUnits_le_localUnits (n : ℕ) : globalUnits p n ≤ localUnits p n` | **code** (statement: the RJW TeX 3084 inclusion) |
| Iwasawa/CyclotomicUnits.lean:211 | `cycloClosure := (cycloUnits p n).topologicalClosure ⊓ localUnits p n` | **code** (the `⊓`-factor that makes the closure "local") |
| Iwasawa/CyclotomicUnits.lean:479 | `have hmemloc : (cyclo p ha hp2).elems n ∈ localUnits p n := …` | **code** (membership in the milestone `cyclo_mem_cycloTower1`) |
| Coleman/ColContinuity.lean:809 | `theorem isClosed_localUnits (n : ℕ) : IsClosed (localUnits p n : Set ℂ_[p]ˣ)` | **code** (topological API about `localUnits`) |
| Coleman/ColContinuity.lean:821, 837 | `… ∩ (localUnits p n : Set ℂ_[p]ˣ) …` in `isClosed_localUnitsOne`/`isClosed_cycloClosureOne` | **code** (consumes `isClosed_localUnits`) |
| IwasawaProof/GaloisAction.lean:421 | `` `localUnits` + `(u : ℂ_[p]) ∈ K_n⁺`) `` | **comment** (docstring) |

(Inside the declaring file there are a further 9 uses: `mem_localUnits_iff`,
`norm_eq_one_of_mem_localUnits`, `localUnitsOne`, `localUnitsPlus`, `O`-membership,
etc.)

Inline-derivation grep (was `𝒪_{K_n}^×` re-derived elsewhere without
`localUnits`?): **none found** — the project consistently routes the local-unit
notion through `localUnits`; the abstract `ValuationSubring.unitGroup` is not used
anywhere in the project (the project never equips `K_n` with a `ValuationSubring`).

What the pattern tells us: **K ≥ 3 external-to-file code uses, no inline
re-derivation** → this is a *real, load-bearing intra-project API*: `localUnits`
is the `⊓`-factor of `cycloClosure` (RJW TeX 3090), the target of
`globalUnits_le_localUnits` (TeX 3084), and the subject of its own topological
lemma `isClosed_localUnits` consumed by two further closedness results. It is not
dead code and not a bypassed wrapper. By the Phase-6.0.1 table this is normally a
"YES-* lean", **but** it is outweighed here by Phase 5: mathlib already owns the
*object* (`ValuationSubring.unitGroup`), strictly more general. The heavy internal
use therefore argues for keeping `localUnits` *as a project-local def* (it earns
its place in the development), not for upstreaming the embedded presentation.

### Composition check (Phase 6)

Can `localUnits` be *defined* by composing mathlib primitives in ≤3 calls?

Attempt 1: take `(𝒪_{K_n}).unitGroup` and transport along `K_n ↪ ℂ_[p]`.
  - Mathlib decls used: `ValuationSubring.unitGroup`, `Units.map`, `Subgroup.map`, plus a `Valued`/`ValuationSubring` structure on `K_n`.
  - Result: **fails as a ≤3-call composition.** The project never equips `K_n` with a `Valued K_n` instance or a `ValuationSubring K_n` (`O p n` is a hand-built `Subring ℂ_[p]`, not a `ValuationSubring`). One must (a) put the valuation/`ValuationSubring` on `K_n`, (b) take `.unitGroup`, (c) push through `Units.map` along the algebra embedding `K_n ↪ ℂ_[p]`, (d) prove the image equals the two-condition carrier. That is real bridging infrastructure, not a one-liner.
  - Notes: this is exactly why the project chose the embedded form — the bridge is non-trivial, so it defined the subgroup directly in `ℂ_[p]ˣ`. (Identical situation to the sibling `globalUnits`.)

Attempt 2: use mathlib's own `(𝓞_ℂ_[p]).unitGroup` (`𝓞_ℂ_[p]` *is* a `ValuationSubring ℂ_[p]`) and intersect with "value in `K_n`".
  - Mathlib decls used: `(PadicComplexInt p).unitGroup`, `⊓`, a `Subgroup ℂ_[p]ˣ` cut out by `(u : ℂ_[p]) ∈ K p n` and `(u⁻¹ : ℂ_[p]) ∈ K p n`.
  - Result: **partial / fails** — `(𝓞_ℂ_[p]).unitGroup = {u : ℂ_[p]ˣ | ‖u‖ = 1}` is the *right* norm-≤1 part, but cutting down to "value lies in the subfield `K_n`" is not a single mathlib call (there is no off-the-shelf "units valued in a given intermediate field" subgroup), and one still has to relate `‖u‖=1` to `u, u⁻¹ ∈ O_n`. More than 3 calls and involves the `O = K.toSubring ⊓ integerRing` bookkeeping. Not a clean composition.

Conclusion: **NOT-COMPOSABLE** as a ≤3-call mathlib composition *in the embedded
form*. (This rules out `NO-composable-from-mathlib`. The right NO bucket is
`NO-mathlib-has-it`: mathlib has the *object* `ValuationSubring.unitGroup`; what is
"not composable" is only the project's deliberate `ℂ_[p]`-embedded
re-presentation of it.)

---

## Verdict: `localUnits` (Phase 7)

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is the local unit group `𝒪_{K_n}^×`
  (`𝒰_n`, `U_{K_n}^0`) of the ring of integers of a p-adic local field — fully
  standard (MIT 18.785 LCFT, Kedlaya CFT, Neukirch/Serre, de Shalit, Rubin); the
  file's two carrier conditions are a literal transcription of "`u` is a unit of
  `𝒪_{K_n}`", and the source paper (arXiv:2309.15692 §9) uses exactly the
  `𝒰_n = 𝒪_{K_n}^×` notation. `localUnitsOne` matches the standard principal-unit
  filtration `U^1 = 1 + 𝔪`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only,
  embedded in `ℂ_[p]`), with the strictly-more-general *and* idiomatic form —
  `ValuationSubring.unitGroup` — **already present in mathlib**. Phase 4c confirms
  the modern idiom is the existing mathlib object, so the finding reinforces NO
  (it does not create a YES-but-generalise-first).
- Mathlib search (Phase 5): found in mathlib as **`ValuationSubring.unitGroup`**
  (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:492`), strictly more
  general and idiomatic, with `unitGroupMulEquiv : A.unitGroup ≃* Aˣ` (it *is* the
  units of the integer ring) and a 73-lemma API; the principal-unit companion
  `localUnitsOne` is mathlib's **`ValuationSubring.principalUnitGroup`** (`:634`,
  carrier `{x | A.valuation (x−1) < 1}`). The project's embedded form has **no**
  mathlib counterpart by name (and shouldn't).
- Composition check (Phase 6): NOT-COMPOSABLE in ≤3 calls (so not the `composable`
  bucket); call sites — K ≥ 3 external-to-file **code** uses, no inline
  re-derivation (real intra-project API, but the *object* is upstream already).

**Rationale.**
The mathematics here is a textbook object: `localUnits p n` is `𝒪_{K_n}^×`, the
unit group of the ring of integers of the p-adic cyclotomic local field
`K_n = ℚ_p(μ_{p^n})`. Mathlib already owns this object in its maximally general,
idiomatic form — `ValuationSubring.unitGroup A : Subgroup Kˣ` for *any* valuation
subring `A` of *any* field `K`, with `unitGroupMulEquiv : A.unitGroup ≃* Aˣ`
witnessing that it is literally the units of the integer ring, plus the
order-embedding, residue-field, and `principalUnitGroup` API (73 lemmas). The
companion principal-unit group `localUnitsOne` (carrier `‖u − 1‖ < 1`) is
mathlib's `ValuationSubring.principalUnitGroup` (carrier `A.valuation (x−1) < 1`)
on the nose. The project's declaration is the *same* object, deliberately
re-presented as a subgroup of `ℂ_[p]ˣ` (the "everything inside `ℂ_p`" convention
of RJW / decomposition replan R10.1/R11.7) so that global units `𝒱_n`, local
units `𝒰_n`, the cyclotomic closures `𝒞_n`, and the norm-compatible tower `𝒰_∞`
all live in **one** ambient group `ℂ_[p]ˣ`, and inclusions like
`globalUnits_le_localUnits` (TeX 3084) and `cycloClosure = closure ⊓ localUnits`
(TeX 3090) are literally `Subgroup ℂ_[p]ˣ` statements. That embedding is a sound
*project* engineering choice — and unlike its sibling `globalUnits`, `localUnits`
has substantial real intra-project use (the `⊓`-factor of `cycloClosure`, the
target of the TeX-3084 inclusion, the subject of `isClosed_localUnits`). But it is
**not** a mathlib contribution: it is neither more general than
`ValuationSubring.unitGroup` nor a missing idiom — it is a specialisation of a
thing mathlib has, wrapped in a project-local ambient. Adding the `ℂ_[p]`-embedded
form to mathlib would duplicate `unitGroup` in a strictly less general, less
reusable shape (no order embedding to the valuation-subring lattice, no
residue-field map, no `principalUnitGroupEquiv`), which is exactly what mathlib's
"one general form" rule forbids.

The one honest caveat — and why the `ℂ_[p]`-embedded design is a project-local
matter rather than a mechanical delete-and-replace — is that the user's form does
**not** follow from `ValuationSubring.unitGroup` in a literal ≤1 line: the project
never equips `K_n` with a `Valued`/`ValuationSubring` structure (`O p n` is a
hand-built `Subring ℂ_[p]`), so bridging "subgroup of `ℂ_[p]ˣ` cut out by
`∈ O_n`" to "`(𝒪_{K_n}).unitGroup` transported along `K_n ↪ ℂ_[p]`" needs the
valuation-subring structure on `K_n` plus an image/injectivity argument (Phase 6,
Attempt 1). That bridge is genuine work, but it is *project-internal refactoring
infrastructure*, not new mathematics for mathlib — the destination object already
exists upstream.

**WHY not (refactor-actionable).** Mathlib already has the result as
`ValuationSubring.unitGroup` — the unit group of a valuation subring, with
`A.unitGroup ≃* Aˣ` (so it *is* `𝒪^×`) — and the principal-unit companion
`ValuationSubring.principalUnitGroup`. The project's `localUnits p n` equals the
image of `(𝒪_{K_n}).unitGroup` under the field embedding `K_n ↪ ℂ_[p]`
(concretely, the two carrier conditions `(u : ℂ_[p]) ∈ O_n`, `(u⁻¹ : ℂ_[p]) ∈ O_n`
say exactly "`u` is the image of a unit of `𝒪_{K_n}`").

Existing mathlib decl:        `ValuationSubring.unitGroup` (companion: `ValuationSubring.principalUnitGroup`)
Located at:                   `Mathlib/RingTheory/Valuation/ValuationSubring.lean:492` (principal: `:634`)
                              (mathlib also has `𝓞_ℂ_[p] = PadicComplexInt p : ValuationSubring ℂ_[p]`,
                              `Mathlib/NumberTheory/Padics/Complex.lean:251`, but its `.unitGroup`
                              is the unit group of the *whole* `ℂ_[p]`-valuation ring, **not** `localUnits p n`)
Relationship (NOT a literal ≤1-line specialisation — see caveat above):
```lean
-- conceptually: localUnits p n = image of (𝒪_{K_n}).unitGroup under K_n ↪ ℂ_[p]
-- u ∈ localUnits p n  ↔  ∃ w : (𝒪_{K_n})ˣ, embedding (w : K_n) = (u : ℂ_[p])
-- bridging this requires a Valued/ValuationSubring structure on K_n,
-- the AlgHom K_n →ₐ[ℚ_p] ℂ_[p], and a Units.map/Subgroup.map image argument.
```
Call sites in the project (from Phase 6.0): **5 external-to-file code uses across
2 files** (`globalUnits_le_localUnits`, `cycloClosure`, the `cyclo_*` milestone
membership, `isClosed_localUnits` + its 2 consumers) plus 1 docstring mention; a
further 9 uses inside the declaring file.

Refactor plan (project-internal — this is **not** a mathlib PR; it is a "should
the project keep its own embedded def?" decision; treat the rows below as cleanup
options, gated on the architecture question in the next paragraph):
- Option A (minimal — **recommended** for a WIP Iwasawa development): **keep
  `localUnits` as a project-local def**, but add a docstring cross-reference to
  `ValuationSubring.unitGroup`/`principalUnitGroup` and, when convenient, a
  bridging lemma exhibiting `localUnits p n` as the `Units.map`/`Subgroup.map`
  image of `(𝒪_{K_n}).unitGroup`, so the project can borrow mathlib's
  unit-group/residue-field/order-embedding API. Do **not** PR the embedded def.
  (Because `localUnits` is genuinely load-bearing at ≥5 call sites, deleting it
  outright is *not* advisable — Option A, not a delete-and-inline, is the right
  cleanup.)
- Option B (full upstream alignment): refactor the `Iwasawa/`+`Coleman/` tower to
  equip `K_n` with its `ValuationSubring` and work with the abstract
  `(𝒪_{K_n}).unitGroup`, embedding into `ℂ_[p]ˣ` only where the *p-adic topology*
  is genuinely needed (the closures `𝒞_n`, `isClosed_localUnits`). This is the
  "Bourbaki 2.0" form but is a substantial project refactor touching all ~5+9
  call sites, not a one-liner.

Next action: do **not** open a mathlib PR for `localUnits` (mathlib has
`ValuationSubring.unitGroup` + `principalUnitGroup`). Keep it project-local
(Option A) with a docstring/bridging-lemma link to the mathlib objects. Reserve
mathlib-upstreaming effort for the file's genuinely p-adic results — the
`zpPow` / `addChar_of_value_at_one` `ℤ_p`-power machinery and
`localUnitsOneModule` (the `ℤ_p`-module structure on principal units) are the more
plausible upstream candidates, not this unit-group `def`.

> Borderline note (not the verdict, but flagged for the maintainer): the *only*
> thing keeping this from a frictionless `NO-mathlib-has-it` is the
> `ℂ_[p]`-embedding, which is a deliberate project-architecture decision shared
> with `globalUnits`/`cycloUnits`/`cycloClosure`. If the project ever decides the
> tower should be built on abstract `ValuationSubring.unitGroup` + a topology only
> at the closure step, the embedded `localUnits` becomes a thin transported image
> and Option B applies. That architecture call is the maintainer's, not the
> skill's — but it does not change the bucket: in *either* architecture the object
> itself is one mathlib already has.

---

## Next step

Do **not** open a mathlib PR for `localUnits` — mathlib already has the unit group
of the ring of integers (valuation subring) of a field as
`ValuationSubring.unitGroup` (with `unitGroupMulEquiv : A.unitGroup ≃* Aˣ`), and
the principal-unit companion of `localUnitsOne` as
`ValuationSubring.principalUnitGroup`; both are strictly more general and carry a
73-lemma API. Keep `localUnits p n` as a project-local definition — the
`ℂ_[p]`-embedded presentation is intentional and genuinely load-bearing *within*
this Iwasawa development (≥5 external-to-file call sites: the `⊓`-factor of
`cycloClosure`, the target of `globalUnits_le_localUnits`, and the subject of
`isClosed_localUnits`) — ideally with a docstring/bridging-lemma link to
`ValuationSubring.unitGroup` so the project can reuse mathlib's unit-group API.
Reserve mathlib-upstreaming effort for the file's genuinely p-adic results (the
`zpPow` `ℤ_p`-power machinery, `localUnitsOneModule`), not this unit-group `def`.
