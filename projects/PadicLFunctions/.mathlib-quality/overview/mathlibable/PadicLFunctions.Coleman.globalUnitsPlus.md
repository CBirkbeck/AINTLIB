# `/mathlibable` report — `PadicLFunctions.Coleman.globalUnitsPlus`

**Final verdict: `NO-mathlib-has-it`** (mathlib has the abstract object `(𝓞 K⁺)ˣ` /
`NumberField.CMExtension.realUnits`; the project's declaration is a project-specific
`ℂ_[p]`-embedded re-presentation of it, and it is presently used **nowhere** —
K = 0 call sites, including its own declaring file).

Mode A, full 10-phase workflow, exhaustive literature sweep.

---

## Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task BUILD NOTE); **reasoned from source** — Phase 0 fallback. The declaration and its whole file are `sorry`-free; the dependency chain (`globalUnits`, `FglobalPlus`, `Fglobal`, `zetaSys`, `ℂ_[p] = PadicComplex`, `IntermediateField`, `IsIntegral`) all resolves.
- decl `PadicLFunctions.Coleman.globalUnitsPlus`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:125`
- kind:                      `def` (`noncomputable def`; a bundled `Subgroup ℂ_[p]ˣ` via `where` anonymous-constructor syntax)
- has sorry:                 no (whole file: 0 `sorry`/`admit`)
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW arXiv:2309.15692 §11.3 + §9 notation), all realised **inside `ℂ_[p]`** (decomposition replan R11.7).

Dependencies read from source:
- `globalUnits p n` (`CyclotomicUnits.lean:106`) = `𝒱_n = O_{F_n}^×`, the global units (value in `Fglobal`, integral over `ℤ` with integral inverse). Sibling verdict on file: **`NO-mathlib-has-it`** (mathlib's `(𝓞 K)ˣ`).
- `FglobalPlus p n` (`CyclotomicUnits.lean:47`) = `F_n⁺ = ℚ⟮ξ + ξ⁻¹⟯`, the maximal totally real subfield, by its concrete generator. Sibling verdict on file: **`BORDERLINE-needs-human`** (mathlib's intrinsic `maximalRealSubfield`, inapplicable p-adically).

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.globalUnitsPlus p n` is **a definition** of the following:

Let `p` be a prime and `n : ℕ`. Inside the field `ℂ_[p]` of `p`-adic complex numbers
(mathlib's `PadicComplex p`), let `F_n = ℚ(μ_{p^n})` be the cyclotomic number field and
`F_n⁺ = ℚ(ξ_{p^n} + ξ_{p^n}⁻¹)` its **maximal totally real subfield**. Then
`globalUnitsPlus p n` is the **plus part of the global units**,
`𝒱_n⁺ = 𝒪_{F_n⁺}^×` — the unit group of the ring of integers of `F_n⁺` —
presented as the subgroup of `ℂ_[p]ˣ` consisting of the units `u` such that (i) `u ∈ 𝒱_n`
(i.e. `u ∈ F_n`, `u` integral over `ℤ`, `u⁻¹` integral over `ℤ`) **and** (ii) the value `u`
lies in the real subfield `F_n⁺`. Conditions (i)+(ii) say exactly that `u` is a unit of
`O_{F_n}` that lands in `F_n⁺`, i.e. a unit of `O_{F_n⁺} = O_{F_n} ∩ F_n⁺`.

In RJW (arXiv:2309.15692, TeX 2472) this is the `X⁺`-construction `𝒱_n⁺ = 𝒪_{F_n⁺}^×`,
the totally-real ("plus") part of the global unit group that, with the cyclotomic plus units
`𝒟_n⁺`, carries the class-number index `h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]` (Washington Thm 8.2, the
deferral noted in the module docstring TeX 3072).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (file scope).
- `n : ℕ` — the cyclotomic level (`F_n = ℚ(μ_{p^n})`).
- ambient: `ℂ_[p] = PadicComplex p` (normed, valued, algebraically closed field).

Hypotheses (Lean side): none beyond the typeclasses; this is a plain `def`.

Carrier (math): `{ u ∈ ℂ_[p]ˣ : u ∈ globalUnits p n ∧ (u : ℂ_[p]) ∈ FglobalPlus p n }`,
with the three `Subgroup` axioms (`mul_mem'`, `one_mem'`, `inv_mem'`) discharged from
`mul_mem`/`globalUnits.inv_mem` and `IntermediateField.mul_mem`/`one_mem`/`inv_mem`.

Conclusion (math): `globalUnitsPlus p n = 𝒱_n⁺ = O_{F_n⁺}^×`, the unit group of the ring
of integers of the maximal real subfield of `F_n`.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` — n/a (definition, not a proposition).

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a `def` of a *named mathematical structure* — the plus part `𝒱_n⁺ = O_{F_n⁺}^×`
of the global units of a number field, a textbook Iwasawa-theory object (Washington Ch. 8;
the `E_n⁺` / "real units" of the cyclotomic tower). Unit groups of rings of integers — and
their plus parts — are essentially guaranteed to be in or near the literature and mathlib.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.)

---

## One-line check (Phase 2b)

Body line count: ~13 substantive lines (a bundled `Subgroup` with a `carrier` set-builder
plus three proof fields `mul_mem'`/`one_mem'`/`inv_mem'`).
One-liner verdict: **MULTI-LINE** (a bundled structure with three non-trivial membership
proofs). The Phase-2b one-liner exemption analysis is therefore not triggered; this is a
substantive `def`, not a one-line alias. (Note for Phase 7: although MULTI-LINE in *body*,
mathematically it is the conjunction `globalUnits ⊓ FglobalPlus-membership` — see the
composition check, Phase 6.)

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "unit group ring of integers maximal real subfield cyclotomic field O_{K^+}^times definition Washington Iwasawa" | yes | `O_{K⁺}^* `, `K⁺ = ℚ(ζ+ζ⁻¹)`, `O_{K⁺} = ℤ[ζ+ζ⁻¹]`; real cyclotomic units have finite index = `h_n⁺` | Wikipedia *Cyclotomic unit*; LTCC ANT lecture notes; arXiv:2504.05159, 2311.16870; confirms `O_{K⁺}^*` is the standard "real unit group" |
| 2 | WebSearch (named-after / aliases / "plus part") | "\"real units\" \"totally real subfield\" cyclotomic field unit group E_n^+ Iwasawa theory plus part Washington chapter 8" | yes | `K_N⁺ = ℚ(ζ_N+ζ_N⁻¹)`; **every unit `u ∈ K_N` is `ζ_N^i · v` with `v ∈ K_N⁺`** (the unit group is generated, up to roots of unity, by the real units); index of real cyclotomic units = `h_N⁺` | arXiv:2311.16870, 2009.00213, 1809.02185 (signature ranks), Cambridge note on `h⁺` — the "plus part of the units" is the standard Iwasawa-theory object |
| 3 | WebSearch (mathlib-form / general) | "mathlib NumberField RingOfIntegers units maximalRealSubfield totally real number field unit group" | yes | `(𝓞 K)ˣ`, totally-real subfield `K⁺`, real units subgroup; Dirichlet's unit theorem | mathlib4 docs `NumberField.Units.*`; Wikipedia *Totally real number field* — points straight at mathlib's `(𝓞 K⁺)ˣ` / CM `realUnits` (see Phase 5) |
| 4 | ChatGPT MCP | (intended: "standard def of the unit group of the maximal real subfield of a cyclotomic field; its generality; historical evolution") | n/a | — | **ChatGPT MCP server not installed** in this environment (ToolSearch for an ask-gpt/chatgpt tool returned only Monitor/TaskStop). Compensated with extra WebSearch (#1–3) + WebFetch (#9) + grep over local mathlib (Phase 5 method D). Recorded n/a per skill fallback. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (no references dir; no `refs/`) | Neither directory exists in this checkout. Source paper is arXiv:2309.15692 (RJW), cited throughout the module docstrings (TeX 2472 for `𝒱_n⁺`). |
| 6 | nLab | "cyclotomic field" (real subfield / unit group) | partial | nLab confirms `ℚ[cos 2π/n]` is the largest real subfield (from the `FglobalPlus` sweep); the *unit group of that subfield* is not separately elaborated on nLab | https://ncatlab.org/nlab/show/cyclotomic+field — stub; the real subfield is named, its unit group is not given a dedicated nLab entry (standard but not categorical) |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept; `O_{K⁺}^*` is the unit group of a maximal order, with no universal-property formulation beyond "units of the integral closure", already covered by #1/#3. |
| 8 | Stacks Project | "ring of integers / units / real subfield" | n/a | (integral closure is in Stacks, but `O_{K⁺}^*` of a number field's real subfield is not an alg-geom-specific concept) | Recorded n/a — number-field real-unit groups are number theory, not the Stacks scope; the integral-closure primitive is generic commutative algebra mathlib already has. |
| 9 | MathOverflow / Math.SE / Wikipedia *Cyclotomic unit* (WebFetch) | definition of `O_{K⁺}^*`; how real cyclotomic units sit inside it; the index = `h_n⁺` | yes | "The index of this subgroup of **real cyclotomic units** … within the **full real unit group** is equal to the class number of the maximal real subfield." | https://en.wikipedia.org/wiki/Cyclotomic_unit — directly confirms `𝒟_n⁺ ⊆ 𝒱_n⁺` with index `h_n⁺`, exactly the file's `cycloUnitsPlus ⊆ globalUnitsPlus` story (RJW TeX 3072) |
| 10 | recent arXiv (last 5 yr) | (returned by #1/#2) | yes | `K_n⁺ = ℚ(ζ_n+ζ_n⁻¹)`, real unit group used as-is | arXiv:2504.05159 (2025), 2311.16870, 2009.00213 ("Class group of real cyclotomic fields") — the real unit group `O_{K⁺}^*` is live, current convention |

### Literature summary (Phase 3)

Concept identified as: **the plus part of the global unit group of a cyclotomic field —
`𝒱_n⁺ = O_{F_n⁺}^*`, the unit group of the ring of integers of the maximal totally real
subfield `F_n⁺ = ℚ(ξ+ξ⁻¹)`** (a.k.a. the "real units" `E_n⁺`). This is one of the central
objects of Iwasawa theory: the cyclotomic plus units `𝒟_n⁺` sit inside it with index the
plus class number `h_n⁺` (Wikipedia #9, RJW TeX 3072 / Washington Thm 8.2), and every unit
of `F_n` is a root of unity times a real unit (#2).

Sources agree on the standard form: **yes.** Uniformly `O_{K⁺}^* = (units of O_{K⁺})`
with `O_{K⁺} = ℤ[ζ+ζ⁻¹] = O_K ∩ K⁺`. The project's two carrier conditions
(`u ∈ globalUnits` = `u ∈ O_{F_n}^*`, and `(u:ℂ_[p]) ∈ FglobalPlus` = `u ∈ F_n⁺`) are a
literal transcription of "`u` is a unit of `O_{F_n}` lying in `F_n⁺`" = "`u ∈ O_{F_n⁺}^*`",
just realized inside `ℂ_[p]`.

Most general standard form: the unit group `(𝓞 K⁺)ˣ` of the ring of integers of the
maximal totally real subfield `K⁺` of an arbitrary CM number field `K` (mathlib's exact
abstract object — see Phase 5), equivalently the image `realUnits K ≤ (𝓞 K)ˣ`.

Generality dimensions where the literature varies:
- base field: cyclotomic `ℚ(μ_{p^n})` (the file) ⊂ any CM number field `K` (the maximal
  standard form, where "maximal real subfield" is defined) ⊂ any number field (where the
  totally-real part is taken).
- ambient realization: *abstract* (`(𝓞 K⁺)ˣ`, the universal literature/mathlib choice) vs.
  *embedded in a fixed completion* `ℂ_[p]` (the file's project-specific choice).
- presentation of "real": *intrinsic* (fixed field of complex conjugation, needs `K →+* ℂ`)
  vs. *concrete generator* (`ℚ(ξ+ξ⁻¹)`, the only form available in `ℂ_p`).

Disagreement with the literature: **none mathematically.** The only divergence is
*presentation*: the literature/mathlib state `(𝓞 K⁺)ˣ` abstractly (with the real subfield
via complex conjugation); the file embeds it in `ℂ_[p]` and re-derives membership from
`u ∈ globalUnits ∧ u ∈ FglobalPlus`.

---

## Generality analysis — `globalUnitsPlus` (Phase 4)

Literature-standard form (from Phase 3): the unit group `(𝓞 K⁺)ˣ` of the ring of integers
of the maximal totally real subfield `K⁺` of a (CM) number field `K`; equivalently the
subgroup `realUnits K ≤ (𝓞 K)ˣ`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field | `F_n = ℚ(μ_{p^n})` (cyclotomic), plus part via `FglobalPlus` | any CM number field `K` with `K⁺ = maximalRealSubfield K` | yes | nothing in the *definition* uses cyclotomicity; `O_{K⁺}^*` makes sense for any CM field. Mathlib's `(𝓞 K⁺)ˣ` / `realUnits K` is exactly this maximal form, and `IsCyclotomicExtension.Rat.isCMField` (`CMField.lean:566`) makes it apply to `F_n` for `p^n>2`. |
| 2 | ambient ring | embedded in `ℂ_[p]`; carrier = `globalUnits ⊓ {u : u ∈ FglobalPlus}` | abstract `(𝓞 K⁺)ˣ` (units of `integralClosure ℤ K⁺`) | yes (and is the *idiomatic* form) | the `ℂ_[p]` embedding is a project convenience, not a mathematical necessity; `(𝓞 K⁺)ˣ` / `realUnits K` drop the ambient field entirely. |
| 3 | "real" presentation | concrete generator `FglobalPlus = ℚ⟮ξ+ξ⁻¹⟯` | intrinsic `maximalRealSubfield` (fixed field of conjugation) | yes (abstractly) | the concrete generator is forced *only* by the `ℂ_p` ambient (no conjugation there); abstractly the intrinsic form is the idiom. This is the one axis where the project genuinely cannot reach the mathlib idiom (no `→ℂ`). |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only, embedded in
`ℂ_[p]`, concrete-generator "real"). However — the key point, identical to the parent
`globalUnits` — the strictly-more-general *and* idiomatic form is **already in mathlib**:
`(𝓞 K⁺)ˣ` for `K⁺ = NumberField.maximalRealSubfield K`, and its image
`NumberField.CMExtension.realUnits K ≤ (𝓞 K)ˣ` (see Phase 5). So this is **not** a
"generalise-then-PR" situation; the generalised form is not a gap. Number of weakening
opportunities found: 3 (rows above), **all of which land on an object mathlib already has**.

Proposed restatement (for the record, = the existing mathlib object): `(𝓞 K⁺)ˣ` where
`K⁺ = NumberField.maximalRealSubfield K`, for `K` a CM number field; equivalently
`NumberField.CMExtension.realUnits K : Subgroup (𝓞 K)ˣ`.

Cost of restatement: n/a — it would be deleting the project def in favour of a mathlib def,
not re-proving a generalisation. Bridging the *embedded* `ℂ_[p]`-form to the abstract form
is real project-internal work (an `AlgHom F_n⁺ → ℂ_[p]` + `Units.map`/image argument), but
that bridge is a project refactor, not a mathlib contribution — see Phase 7.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partially | use `[NumberField K]` (CM) + `(𝓞 K⁺)ˣ` / `realUnits K` instead of a hand-rolled embedded subgroup | the entire `NumberField.Units` + `CMExtension` API (Dirichlet, torsion, regulator, `indexRealUnits`) |
| 2 | sequences/metric → filters/topological? | no | — | the def has no convergence content; it is purely algebraic. |
| 3 | construct an object → universal-property class? | yes | `K⁺ = maximalRealSubfield K` already *is* the universal (maximal totally real subfield, `IsTotallyReal.le_maximalRealSubfield`) characterization; `(𝓞 K⁺)ˣ` is its unit group | composes with `IsCMField`, `equivMaximalRealSubfield`, `IsIntegralClosure`, the regulator/index theorems |
| 4 | set-with-closure-predicate → bundled-substructure type? | yes (already half-done) | the file already bundles a `Subgroup`; the idiomatic target bundles the *ring* (`𝓞 K⁺`) and takes its units, or uses `realUnits K`, so `Subgroup`/lattice ops compose with the whole CM-field stack | `Subgroup` lattice, `realUnits ⊔ torsion`, the `indexRealUnits` quotient |
| 5 | field/metric-specific → weaken typeclasses? | yes | drop `ℂ_[p]` entirely; `(𝓞 K⁺)ˣ` / `realUnits K` need only `[IsCMField K]` (auto for cyclotomic) | scalar-tower-independent; works for every CM field uniformly |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no (the `n` indexes the *field*, not an algebraic structure to generalise) | — | the `n`-tower is intrinsic to Iwasawa theory; not a spurious concrete index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, and it is **already realized in mathlib** —
`(𝓞 K⁺)ˣ` (`K⁺ = NumberField.maximalRealSubfield K`) and its in-`(𝓞 K)ˣ` image
`NumberField.CMExtension.realUnits K`, with the full Hasse-unit-index API
(`indexRealUnits_eq_one_or_two`, `regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv`).
Crucially, this does **not** flip the verdict to YES-but-generalise-first: the modern/general
form is not a missing contribution we should build — it *exists in mathlib*. Hence the
modern-idiom finding **reinforces `NO-mathlib-has-it`**; it does not create a YES.
Real mathematical improvement of the idiomatic form: it unlocks the whole CM-unit ecosystem
(real units, the index `Q = [E:WE⁺] ∈ {1,2}`, the regulator ratio — RJW's `Q`-index, TeX
2498ff) for free — none of which the embedded `ℂ_[p]ˣ`-subgroup form can reach.

> Why this resolves more cleanly than the `FglobalPlus` BORDERLINE: for `FglobalPlus`,
> mathlib's only matching object was the *field* `maximalRealSubfield`, which is intrinsic
> (needs `→ℂ`) and so *inapplicable* p-adically with no bridge lemma — three legitimately
> different upstream targets, a genuine taste call. Here the object is the **unit group**,
> and mathlib carries it as a concrete *subgroup* (`realUnits K`) and as `(𝓞 K⁺)ˣ`, the
> direct general analogue of this very `def` (cf. the parent `globalUnits → (𝓞 K)ˣ`,
> which likewise resolved to NO-mathlib-has-it). The p-adic-ambient mismatch is the same
> project-architecture matter as for the parent — it makes the *bridge* nontrivial, not the
> *bucket* ambiguous.

---

## Diamond / defeq risk — `globalUnitsPlus` (Phase 4.5)

(`def`, so the phase runs. It is a *plain* `def` returning a `Subgroup`, not an
`instance`/`class`/coercion.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | it is a `def` returning a `Subgroup`, not an `instance`; participates in no typeclass-search path. |
| 2 | Reducibility leak | none | no `@[reducible]`; a sealed bundled `Subgroup`, exposed only through `SetLike` membership. |
| 3 | Non-canonical unfolding | low | `simp` will unfold `· ∈ globalUnitsPlus p n` to the two carrier conjuncts via the auto-generated `mem` simp-lemma; intended API, unsurprising. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types concrete (`ℂ_[p]ˣ`, `ℕ`); no universe variables. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`; only the standard `Subgroup → Set` from `SetLike`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** Top risks: none. (This matters only if the verdict were a YES
bucket; it is not. Recorded for completeness — the def would be infrastructure-safe to ship.)

---

## Mathlib search-status: `globalUnitsPlus` (Phase 5)

[A] Lean-Finder       (web service) — **n/a in this environment** (no `lean_finder` MCP tool present); folded into the conceptual phrasing of [C]; the object is the well-known `(𝓞 K⁺)ˣ` / `realUnits`, confirmed directly via grep [D].
[B] Loogle (`lean_loogle`) — **n/a in this environment** (no Loogle MCP tool present). Type-pattern that would be tried: `Subgroup (Units _)` / `Subgroup ((RingOfIntegers _)ˣ)`; the relevant hit (`CMExtension.realUnits : Subgroup (𝓞 K)ˣ`) is found by grep [D] instead.
[C] LeanSearch (`lean_leansearch`) — **n/a in this environment** (no LeanSearch MCP tool present). NL query that would be tried: "unit group of the ring of integers of the maximal real subfield" / "real units of a CM field"; the object is `(𝓞 K⁺)ˣ` / `NumberField.CMExtension.realUnits`, confirmed via [D].
[D] Grep mathlib src — `maximalRealSubfield`, `realUnits`, `indexRealUnits`, `IsCMField`, `(𝓞 .*⁺)ˣ`, `RingOfIntegers.*totallyReal`, `isCMField` over `.lake/packages/mathlib/Mathlib/` — **rich hits, see below**.
[E] Name pattern (`lean_local_search`) — **n/a in this environment** (no `lean_local_search` MCP tool present). Grep over mathlib for `globalUnitsPlus` → **0 hits** (no decl by this name); by-name hits for `realUnits`, `maximalRealSubfield`, `indexRealUnits`.

Searched for both:
- the user's current form (embedded `Subgroup ℂ_[p]ˣ` = `globalUnits ⊓ {u ∈ FglobalPlus}`) — **not in mathlib** (no `globalUnitsPlus`; no units-of-real-subfield-as-`Lˣ`-subgroup over an arbitrary completion).
- the literature-standard / abstract form (`(𝓞 K⁺)ˣ` / real units of a CM field) — **in mathlib**, with rich API:
  - `NumberField.maximalRealSubfield K : Subfield K` — the maximal real subfield (`Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean:125`), notation `K⁺`, with `IsTotallyReal.le_maximalRealSubfield` (universal property).
  - `(𝓞 K⁺)ˣ` — units of its ring of integers — appears directly in `Mathlib/NumberTheory/NumberField/CMField.lean` (e.g. `mem_realUnits_iff`: `u ∈ realUnits K ↔ ∃ v : (𝓞 K⁺)ˣ, algebraMap (𝓞 K⁺) (𝓞 K) v = u`, line 273–275).
  - `NumberField.CMExtension.realUnits K : Subgroup (𝓞 K)ˣ` (`CMField.lean:270`) = the image of `(𝓞 K⁺)ˣ` inside `(𝓞 K)ˣ` — the **direct abstract analogue of `globalUnitsPlus`** (a subgroup of the big unit group cut out by "comes from the real subfield"; mirrors the project's `globalUnitsPlus ≤ globalUnits`).
  - Hasse-unit-index API: `indexRealUnits := (realUnits K ⊔ torsion K).index` (`CMField.lean:359`), `indexRealUnits_eq_one_or_two` (`:375`), `indexRealUnits_eq_two_iff` (`:387`), `regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv` (`:441`) — exactly RJW's `Q`-index machinery (TeX 2498ff).
  - Applicability to *this* field family: `IsCyclotomicExtension.Rat.isCMField` (`CMField.lean:566`) — "a nontrivial cyclotomic extension of ℚ is CM" — so for `p^n > 2` all the above applies verbatim to `F_n = ℚ(μ_{p^n})`, with `F_n⁺ = maximalRealSubfield F_n`.
  - Cyclotomic-unit *facts* (not the group): `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean`.

Concluded: **"found in mathlib as `(NumberField.RingOfIntegers (NumberField.maximalRealSubfield K))ˣ` (i.e. `(𝓞 K⁺)ˣ`), and as the subgroup `NumberField.CMExtension.realUnits K : Subgroup (𝓞 K)ˣ`; strictly more general (any CM number field, applicable to `F_n` via `isCMField`) and idiomatic; the project's `globalUnitsPlus p n` is the same mathematical object (`𝒱_n⁺ = O_{F_n⁺}^*`) re-presented as a subgroup of `ℂ_[p]ˣ`."** The project's *exact embedded form* is not in mathlib (correctly — the embedding is a project-local device, and the general form is what mathlib carries).

---

## Call sites — `globalUnitsPlus` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file): **0.**
External-to-file callers: **0 files.**
**Total occurrences of the name `globalUnitsPlus` in the entire project: 1 — the
definition line itself (`CyclotomicUnits.lean:125`).** No call site anywhere, including
inside its own declaring file. (Verified: `grep -rnE "globalUnitsPlus" projects/ --include="*.lean"` returns exactly one line.)

| Caller file:line | Usage pattern (one-line excerpt) | Code or comment? |
|------------------|----------------------------------|------------------|
| (none) | — | — |

Inline-derivation grep (was `O_{F_n⁺}^*` / `𝒱_n⁺` re-derived elsewhere without `globalUnitsPlus`?):
**(none found).** The plus-part global units are *not* reconstructed under another name. By
contrast the sibling `cycloUnitsPlus` (`𝒟_n⁺`, the same `where`-pattern one decl below) has
**~10** uses, and `FglobalPlus`/`localUnitsPlus` are heavily used (~18 / several) — so the
absence of *any* `globalUnitsPlus` consumer is specific to this decl, not a grep artifact.

What the pattern tells us (per 6.0.1): **K = 0 internal uses, no inline re-derivation.**
This is the "dead code? / brand-new + unused?" cell. Read against the development: the file's
*used* objects are `globalUnits` (the `⊓`-factor of `cycloUnits`), `FglobalPlus`, `cycloUnits`,
`cycloUnitsPlus`, `cycloClosure*`, and the milestone `cyclo_*` lemmas; `globalUnitsPlus`
(`𝒱_n⁺`) is the RJW-faithful "`X⁺` of `𝒱_n`" companion to `cycloUnitsPlus` (`𝒟_n⁺`), defined
for completeness of the §11.3 notation block (it would be the home of the deferred index
`h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]`, TeX 3072, which the module docstring explicitly records as
permanently deferred). So it is a *notation-completeness* definition with no current
consumer — which sharply weakens any case for shipping it and **reinforces NO**.

### Composition check (Phase 6)

Two questions: (a) can the *object* be obtained from mathlib in ≤3 calls (the
mathlib-composition bucket); (b) can the *def* be obtained from existing **project**
primitives as a cheap `⊓` (the in-project "don't need a bespoke `where`" signal).

**(a) Mathlib composition.**

Attempt 1: take `(𝓞 F_n⁺)ˣ` (or `realUnits F_n`) and transport along `F_n⁺ ↪ ℂ_[p]`.
  - Mathlib decls used: `NumberField.maximalRealSubfield`, `NumberField.RingOfIntegers`, `NumberField.CMExtension.realUnits`, `Units.map`, an `AlgHom F_n⁺ → ℂ_[p]` / `Subgroup.map`.
  - Result: **fails as a ≤3-call composition.** As for the parent `globalUnits`, there is no off-the-shelf `AlgHom F_n⁺ →ₐ[ℚ] ℂ_[p]` packaged here; one must exhibit the embedding as an algebra map, push the unit group through `Units.map`, and prove the image equals the two-condition carrier. Real bridging infrastructure (an `IsIntegralClosure`/embedding transport + image/injectivity argument), not a one-liner. Additionally the mathlib objects use the *intrinsic* real subfield (`→ℂ` conjugation), absent in `ℂ_p` — so even the source object needs the concrete-generator re-presentation first.
  - Notes: this is exactly why the project chose the embedded form.

Conclusion (a): **NOT-COMPOSABLE** as a ≤3-call mathlib composition *in the embedded form*.
(This rules out `NO-composable-from-mathlib` *via mathlib*. The right NO bucket is
`NO-mathlib-has-it`: mathlib has the *object* `(𝓞 K⁺)ˣ` / `realUnits`; what is "not
composable" is only the project's deliberate `ℂ_[p]`-embedded re-presentation.)

**(b) In-project `⊓` (recorded for the maintainer, not bucket-deciding).**
The carrier `{u | u ∈ globalUnits p n ∧ (u : ℂ_[p]) ∈ FglobalPlus p n}` is exactly
`globalUnits p n ⊓ (FglobalPlus p n comap'd to ℂ_[p]ˣ along the unit-value hom)`. The
project already writes the *analogous* lattice forms with `⊓` (e.g.
`cycloClosurePlus = cycloClosure ⊓ localUnitsPlus`, `localUnitsOnePlus = localUnitsOne ⊓ localUnitsPlus`).
The reason `globalUnitsPlus` (like its twin `cycloUnitsPlus`) is a bespoke `where` rather
than `globalUnits ⊓ (…)` is that there is **no named subgroup for "units in `FglobalPlus`"** —
`localUnitsPlus` uses the *local* field `KPlus`, not `FglobalPlus`. So even within the
project the bespoke form is not a literal `⊓` of two *existing named* subgroups; it would
need a small "`FglobalPlus`-as-unit-subgroup" comap def first. This is a cleanup/uniformity
note, **not** a `NO-composable-from-mathlib` trigger (that bucket is about *mathlib*
primitives), and it does not change the verdict.

---

## Verdict: `globalUnitsPlus` (Phase 7)

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is the **plus part of the global unit group**,
  `𝒱_n⁺ = O_{F_n⁺}^*`, the unit group of the ring of integers of the maximal totally real
  subfield — fully standard (Wikipedia, LTCC notes, Washington Ch. 8, recent arXiv); the
  file's two carrier conditions are a literal transcription, and RJW (arXiv:2309.15692,
  TeX 2472) uses exactly the `𝒱_n⁺ = O_{F_n⁺}^×` notation. The companion index
  `h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]` (TeX 3072 / Wikipedia #9) is the canonical use of this object.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only,
  embedded in `ℂ_[p]`, concrete-generator "real"), with the strictly-more-general *and*
  idiomatic form — `(𝓞 K⁺)ˣ` / `realUnits K` — **already present in mathlib**. Phase 4c
  confirms the modern idiom is the existing mathlib object, so the finding reinforces NO (it
  does not create a YES-but-generalise-first).
- Mathlib search (Phase 5): found in mathlib as **`(NumberField.RingOfIntegers (NumberField.maximalRealSubfield K))ˣ`** (`= (𝓞 K⁺)ˣ`) and as **`NumberField.CMExtension.realUnits K : Subgroup (𝓞 K)ˣ`**, more general and idiomatic, with the full Hasse-unit-index / regulator API; applicable to `F_n` via `IsCyclotomicExtension.Rat.isCMField`. The project's embedded form has **no** mathlib counterpart by name (and shouldn't).
- Composition check (Phase 6): NOT-COMPOSABLE in ≤3 mathlib calls (so not the `composable`
  bucket). Call sites: **K = 0 everywhere, including the declaring file** — the strongest
  possible "not pulling its weight" signal.

**Rationale.**
The mathematics here is a textbook Iwasawa-theory object: `globalUnitsPlus p n` is
`𝒱_n⁺ = O_{F_n⁺}^*`, the unit group of the ring of integers of the maximal totally real
subfield of the cyclotomic field `F_n = ℚ(μ_{p^n})`. Mathlib already owns this object in its
maximally general, idiomatic form. For a CM field `K`, mathlib has the maximal real subfield
`K⁺ = NumberField.maximalRealSubfield K`, its ring-of-integers unit group `(𝓞 K⁺)ˣ`, and —
most pointedly — the subgroup `NumberField.CMExtension.realUnits K ≤ (𝓞 K)ˣ` (the image of
`(𝓞 K⁺)ˣ` inside the full unit group), which is the *direct abstract analogue* of this very
`def` (`globalUnitsPlus ≤ globalUnits` is mathlib's `realUnits K ≤ (𝓞 K)ˣ`). It even ships
the full Hasse-unit-index machinery `indexRealUnits ∈ {1,2}` and the regulator ratio — RJW's
`Q`-index — and `IsCyclotomicExtension.Rat.isCMField` makes all of it apply directly to
`F_n` for `p^n>2`. The project's declaration is the *same* object, deliberately re-presented
as a subgroup of `ℂ_[p]ˣ` (the "everything inside `ℂ_p`" convention of RJW / replan R11.7)
so that `𝒱_n⁺`, `𝒱_n`, and the local units `𝒰_n` live in one ambient group. That embedding
is a sound *project* engineering choice, but it is **not** a mathlib contribution: it is
neither more general than `(𝓞 K⁺)ˣ`/`realUnits` nor a missing idiom — it is a specialization
of an object mathlib has, wrapped in a project-local ambient. Adding the `ℂ_[p]`-embedded
form to mathlib would duplicate `realUnits`/`(𝓞 K⁺)ˣ` in a strictly less general, less
reusable shape, exactly what mathlib's "one general form" rule forbids.

This lands on `NO-mathlib-has-it` rather than the `BORDERLINE` of its field-sibling
`FglobalPlus` for two compounding reasons. First, the object in question is the **unit
group**, which mathlib carries cleanly *as a subgroup* (`realUnits`) and as `(𝓞 K⁺)ˣ` —
unlike the *field* `FglobalPlus`, whose only mathlib match (`maximalRealSubfield`) is
intrinsic-only and p-adically inapplicable with no bridge lemma, leaving three legitimately
different upstream targets. Here there is one clear upstream object and one clear relationship
(`globalUnitsPlus = realUnits transported to ℂ_[p]`), matching the parent `globalUnits →
(𝓞 K)ˣ` resolution. Second — and decisively for the inclusion question — the decl is used
**nowhere**: it is a notation-completeness companion to `cycloUnitsPlus` (`𝒟_n⁺`), the
intended home of the *deferred* index `h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]` (TeX 3072, permanently deferred
per the module docstring). A wholly-unused specialization of an object mathlib already has, in
a less general form, has no case for upstreaming.

The one honest caveat (same as the parent `globalUnits`, and why this is a project-local
matter rather than a mechanical delete-and-replace): the user's form does **not** follow from
`(𝓞 F_n⁺)ˣ` / `realUnits F_n` in a literal ≤1 line — bridging "subgroup of `ℂ_[p]ˣ` cut out
by `u ∈ globalUnits ∧ u ∈ FglobalPlus`" to "the real units of `F_n` transported along
`F_n⁺ ↪ ℂ_[p]`" needs the algebra embedding plus an image/injectivity argument, and the
*concrete-generator* presentation of `F_n⁺` because `ℂ_p` has no complex conjugation. That
bridge is genuine work, but it is *project-internal refactoring infrastructure*, not new
mathematics for mathlib — the destination object already exists upstream.

**WHY not (refactor-actionable).** Mathlib already has the result as the real units of a CM
field: `(𝓞 K⁺)ˣ` with `K⁺ = NumberField.maximalRealSubfield K`, and the subgroup
`NumberField.CMExtension.realUnits K : Subgroup (𝓞 K)ˣ` = image of `(𝓞 K⁺)ˣ` in `(𝓞 K)ˣ`
(with `mem_realUnits_iff`). The project's `globalUnitsPlus p n` is the image of
`realUnits F_n` (equivalently of `(𝓞 F_n⁺)ˣ`) under the field embedding `F_n⁺ ↪ ℂ_[p]`:
the two carrier conditions `u ∈ globalUnits p n` and `(u:ℂ_[p]) ∈ FglobalPlus p n` say
exactly "`u` is the image of a unit of `O_{F_n}` lying in `F_n⁺`" = "`u` is the image of a
unit of `O_{F_n⁺}`".

Existing mathlib decl:        `NumberField.CMExtension.realUnits` (and `(𝓞 (maximalRealSubfield K))ˣ`)
Located at:                   `Mathlib/NumberTheory/NumberField/CMField.lean:270`
                              (`maximalRealSubfield`: `Mathlib/NumberTheory/NumberField/InfinitePlace/TotallyRealComplex.lean:125`;
                              index API: `CMField.lean:359,375,387,441`;
                              cyclotomic⇒CM: `IsCyclotomicExtension.Rat.isCMField`, `CMField.lean:566`)
Relationship (NOT a literal ≤1-line specialization — see caveat above):
```lean
-- conceptually: globalUnitsPlus p n = image of realUnits F_n (= image of (𝓞 F_n⁺)ˣ) under F_n⁺ ↪ ℂ_[p]
-- u ∈ globalUnitsPlus p n  ↔  ∃ w : (𝓞 (maximalRealSubfield F_n))ˣ, embedding (w) = (u : ℂ_[p])
-- bridging needs the AlgHom F_n⁺ →ₐ[ℚ] ℂ_[p], a Units.map/Subgroup.map image argument,
-- and the concrete-generator presentation of F_n⁺ (ℂ_p has no complex conjugation).
```
Call sites in the project (from Phase 6.0): **0 — the name appears only on its own definition
line.** (Contrast: `cycloUnitsPlus`, the twin one decl below, has ~10.)

Refactor plan (project-internal — this is **not** a mathlib PR; with K = 0 it is in fact a
"should the project even keep this def?" question):
- Option A (delete — recommended unless `h_n⁺` work is imminent): **remove `globalUnitsPlus`**.
  It has no consumers; it is unused notation-completeness scaffolding for the permanently-deferred
  index `h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]`. Deleting it costs nothing (no call sites to update) and removes
  a redundant specialization of `realUnits`/`(𝓞 K⁺)ˣ`. If/when the deferred index is revisited,
  reintroduce it then (or define it directly against mathlib's `realUnits`).
- Option B (keep + cross-reference): **keep `globalUnitsPlus` as project-local scaffolding** for
  the §11.3 notation block, but add a docstring cross-reference to `(𝓞 K⁺)ˣ` /
  `NumberField.CMExtension.realUnits` and, when convenient, a bridging lemma
  `globalUnitsPlus p n = (realUnits F_n).map (Units.map embedding)` so the project can borrow
  mathlib's index/regulator API for the eventual `h_n⁺` statement. Do **not** PR the embedded def.
- Either way: do **not** open a mathlib PR for `globalUnitsPlus` — mathlib has `(𝓞 K⁺)ˣ` /
  `realUnits`, strictly more general and with the full CM-unit/index/regulator API.

Next action: do **not** open a mathlib PR for `globalUnitsPlus`. Treat it as a project cleanup
item — prefer **Option A (delete the unused def)**; reserve mathlib-upstreaming effort for the
file's genuinely p-adic results (e.g. `norm_le_one_of_isIntegral_int`, the `ℂ_[p]`/`zpPow`
machinery), not this unit-group definition.

---

## Next step

Do **not** open a mathlib PR for `globalUnitsPlus` — mathlib already has the plus part of the
unit group of a CM number field as `(𝓞 (NumberField.maximalRealSubfield K))ˣ` and as the
subgroup `NumberField.CMExtension.realUnits K ≤ (𝓞 K)ˣ`, strictly more general (applicable to
`F_n` via `IsCyclotomicExtension.Rat.isCMField`) and with the full Hasse-unit-index and
regulator API. Because the def is presently **unused** (K = 0 call sites anywhere, including its
own file), treat it as a project cleanup item: prefer deleting it (Option A) and reintroducing
against mathlib's `realUnits` only when the deferred index `h_n⁺ = [𝒱_n⁺ : 𝒟_n⁺]` (RJW TeX 3072)
is actually developed; otherwise keep it project-local with a docstring/bridging-lemma link to
`realUnits` (Option B). Upstream effort from this file belongs to its p-adic-specific results,
not this unit-group `def`.
