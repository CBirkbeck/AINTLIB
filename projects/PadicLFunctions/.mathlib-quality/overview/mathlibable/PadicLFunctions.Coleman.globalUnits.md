# `/mathlibable` report — `PadicLFunctions.Coleman.globalUnits`

**Final verdict: `NO-mathlib-has-it`** (mathlib has the abstract object `(𝓞 F_n)ˣ`;
the project's declaration is a project-specific re-presentation of it embedded in `ℂ_[p]`).

---

## Baseline (Phase 0)

- lake build:               not re-run (build stale/slow per task instructions); **reasoned from source** — Phase 0 fallback. The declaration and its whole file are `sorry`-free and the dependency chain (`Fglobal`, `zetaSys`, `ℂ_[p] = PadicComplex`, `IsIntegral`) all resolves.
- decl `PadicLFunctions.Coleman.globalUnits`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:106`
- kind:                      `def` (a bundled `Subgroup ℂ_[p]ˣ` via the `where` anonymous-constructor syntax)
- has sorry:                 no (whole file: 0 `sorry`/`admit`)
- module docstring summary:  Cyclotomic units: the global modules `𝒟_n` and their local closures `𝒞` (RJW arXiv:2309.15692 §11.3 + §9 notation), all realized **inside `ℂ_[p]`** (decomposition replan R11.7).

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.globalUnits p n` is **a definition** of the following:

Let `p` be a prime and `n : ℕ`. Inside the field `ℂ_[p]` of `p`-adic complex
numbers (mathlib's `PadicComplex p`, the completion of an algebraic closure of
`ℚ_p`), let `F_n = ℚ(μ_{p^n})` be the cyclotomic number field, realized as the
intermediate field `Fglobal p n = ℚ⟮zetaSys p n⟯ : IntermediateField ℚ ℂ_[p]`.
Then `globalUnits p n` is the **group of global units `𝒱_n = O_{F_n}^×`** — the
unit group of the ring of integers of `F_n` — presented as the subgroup of
`ℂ_[p]ˣ` consisting of those units `u` such that (i) the value `u` lies in `F_n`,
(ii) `u` is integral over `ℤ`, and (iii) `u⁻¹` is integral over `ℤ`. Conditions
(i)–(iii) say exactly that `u` is an element of the integral closure of `ℤ` in
`F_n` whose inverse is too — i.e. a unit of `O_{F_n} = integralClosure ℤ F_n`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime (fixed at file scope).
- `n : ℕ` — the cyclotomic level (the field is `ℚ(μ_{p^n})`).
- ambient: `ℂ_[p]` = `PadicComplex p` (normed, valued, algebraically closed field).

Hypotheses (Lean side): none beyond the typeclasses; this is a plain `def`.

Carrier (math): `{ u ∈ ℂ_[p]ˣ : (u : ℂ_[p]) ∈ F_n ∧ IsIntegral ℤ (u:ℂ_[p]) ∧ IsIntegral ℤ (u⁻¹:ℂ_[p]) }`,
with the three `Subgroup` axioms (`mul_mem'`, `one_mem'`, `inv_mem'`) discharged
from `mul_mem`/`IntermediateField.inv_mem` and `IsIntegral.mul`/`isIntegral_one`.

Conclusion (math): `globalUnits p n = O_{F_n}^×`, the global unit group of `F_n`.

Conclusion (Lean): `Subgroup ℂ_[p]ˣ` — n/a (definition, not a proposition).

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a `def` of a *named mathematical structure* — the global-unit group
`O_{F_n}^×` of a number field — and it is foundational scaffolding for a `## Main
results`-level development (the milestone `cyclo_mem_cycloTower1`, RJW TeX 3084).
Unit groups of rings of integers are textbook objects (Washington, Neukirch),
so they are essentially guaranteed to be in or near the literature and mathlib.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL only frames the report.)

---

## One-line check (Phase 2b)

Body line count: ~15 substantive lines (a bundled `Subgroup` with a `carrier`
set-builder plus three proof fields `mul_mem'`/`one_mem'`/`inv_mem'`).
One-liner verdict: **MULTI-LINE** (a bundled structure with three non-trivial
membership proofs). The Phase-2b one-liner exemption analysis is therefore not
triggered; this is a substantive `def`, not a one-line alias.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "global units ring of integers number field cyclotomic field O_K^× definition" | yes | `O_K^× = {invertible elements of O_K}`, `O_K = ℤ[ζ_n]` for `K=ℚ(ζ_n)` | Wikipedia *Cyclotomic unit*, Conrad's cyclotomic-integers handout, leanprover-community blog "ring of integers of a cyclotomic field" |
| 2 | WebSearch (general form) | "\"unit group\" \"ring of integers\" number field standard definition integral closure invertible elements O_K star" | yes | `O_K^× := {u ∈ O_K | ∃ u⁻¹ ∈ O_K, u·u⁻¹ = 1}`, `O_K = integral closure of ℤ in K` | Wikipedia *Ring of integers*, *S-unit*, *Fundamental unit*; the maximally general form is "any number field / global field" |
| 3 | WebSearch (named-after / aliases) | "cyclotomic units global units E_n unit group cyclotomic field Iwasawa theory Washington" | yes | `E_n = O_{F_n}^×` ⊇ cyclotomic units `C_n` (finite index) | Washington, *Introduction to Cyclotomic Fields*; Hida lecture notes; the `E_n`/`𝒱_n` (global) vs `C_n`/`𝒟_n` (cyclotomic) split is the standard Iwasawa-theory setup — exactly the file's `globalUnits` ⊇ `cycloUnits` |
| 4 | WebSearch (C_p-embedded form) | "unit group ring of integers embedded in C_p p-adic complex numbers local units Coleman map Iwasawa" | yes | (the SOURCE paper) | top hit is **arXiv:2309.15692** = RJW, *An introduction to p-adic L-functions* — the project's reference; the `𝒱_n`/`𝒞_n` notation and the C_p ambient are this paper's |
| 5 | ChatGPT MCP | "standard definition of global units O_K^× of a (cyclotomic) number field, its generality, historical evolution" | n/a | — | **ChatGPT MCP server not configured** in this environment (only Asana/Atlassian/etc. MCP servers present). Recorded n/a; compensated with deeper WebSearch (#1–4) + WebFetch (#6, #9). |
| 6 | nLab | "ring of integers" | yes | `O_K` = algebraic integers in `K` = integral closure of `ℤ`; "ring of integers is a Dedekind domain"; units are the invertibles | https://ncatlab.org/nlab/show/ring+of+integers — confirms the maximally general anchor: integral closure, any number field / non-archimedean local field |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; the universal property of `O_K` is "maximal order / integral closure", already covered by #6. No extra higher-categorical form. |
| 8 | Stacks Project | "ring of integers / integral closure units" | n/a | (integral closure is in Stacks, but `O_K^×` of a number field is not an alg-geom-specific concept) | Recorded n/a — number-field unit groups are number theory, not the Stacks scope; the integral-closure primitive is generic commutative algebra mathlib already has. |
| 9 | MathOverflow / Math.SE / Wikipedia *Cyclotomic unit* (WebFetch) | definition of `O_K^×` and how cyclotomic units sit inside it; generality | yes | "cyclotomic units form a subgroup of finite index in the group of units of a cyclotomic field"; full `O_K^×` defined via Dirichlet's unit theorem | https://en.wikipedia.org/wiki/Cyclotomic_unit — confirms the global-unit group is the standard ambient and cyclotomic units a finite-index subgroup |
| 10 | recent arXiv (last 5 yr) | (the source) arXiv:2309.15692 §9/§11.3 | yes | `𝒱_n = O_{F_n}^×`, `𝒟_n` cyclotomic, `𝒞_n` p-adic closure inside `𝒰_n ⊆ ℂ_p` | RJW. PDF is binary-compressed so a verbatim TeX quote was not machine-extractable, but the file docstring cites "RJW TeX 2472" for `𝒱_n` and #4 confirms the paper identity. |

### Literature summary (Phase 3)

Concept identified as: **the group of global units `O_K^×` (a.k.a. `E_n`, here
`𝒱_n`) of the ring of integers of a number field** — specialized to the
cyclotomic field `F_n = ℚ(μ_{p^n})`. In the Iwasawa-theory tower this is the
*global* unit group, and the *cyclotomic* units `𝒟_n` form a finite-index
subgroup of it (the `𝒱_n ⊇ 𝒟_n` of the file).

Sources agree on the standard form: **yes.** Uniformly,
`O_K^× = {u : K | u ∈ O_K ∧ u⁻¹ ∈ O_K}` with `O_K = integralClosure ℤ K`. The
project's three carrier conditions (`∈ Fglobal`, `IsIntegral ℤ u`, `IsIntegral ℤ u⁻¹`)
are a literal transcription of this, just with `K = F_n` *realized inside `ℂ_[p]`*
(so "`∈ O_{F_n}`" is split into "`∈ F_n`" + "integral over `ℤ`").

Most general standard form: the unit group `(𝓞 K)ˣ` of the ring of integers of an
arbitrary number field `K` (mathlib's exact abstract object).

Generality dimensions where the literature varies:
- base field: cyclotomic `ℚ(μ_{p^n})` (the file) ⊂ any number field (the maximal
  standard form) ⊂ any global field / fraction field of a Dedekind domain.
- ambient realization: *abstract* (`O_K` as `integralClosure ℤ K`, the universal
  literature/mathlib choice) vs. *embedded in a fixed completion* `ℂ_[p]` (the
  file's project-specific choice, RJW's "everything inside `ℂ_p`" convention).

Disagreement with the literature: **none mathematically.** The only divergence is
*presentation*: the literature/mathlib state `O_K^×` abstractly; the file embeds
it in `ℂ_[p]` and re-derives "is in `O_{F_n}`" from "`∈ F_n` ∧ `ℤ`-integral".

---

## Generality analysis — `globalUnits` (Phase 4)

Literature-standard form (from Phase 3): the unit group `(𝓞 K)ˣ` of the ring of
integers `𝓞 K = integralClosure ℤ K` of an arbitrary number field `K`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field | `F_n = ℚ(μ_{p^n})` (cyclotomic, via `Fglobal p n`) | any number field `K` | yes | nothing in the *definition* uses cyclotomicity; `O_K^×` makes sense for any number field. Mathlib's `(𝓞 K)ˣ` is exactly this maximal form. |
| 2 | ambient ring | embedded in `ℂ_[p]`; "`∈ O_{F_n}`" = "`∈ Fglobal` ∧ `IsIntegral ℤ`" | abstract `O_K = integralClosure ℤ K` | yes (and is the *idiomatic* form) | the C_p embedding is a project convenience, not a mathematical necessity; the abstract `(𝓞 K)ˣ` drops the ambient field entirely. |
| 3 | integrality split | two conditions `IsIntegral ℤ u` **and** `IsIntegral ℤ u⁻¹` | one condition: `u ∈ (𝓞 K)ˣ` (membership of a *unit* in the integral closure already forces both) | yes | in the abstract form a single "`u` is a unit of `𝓞 K`" subsumes both; the split exists only because the file works with `ℂ_[p]ˣ`, not `(𝓞 F_n)ˣ`. |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only, and
embedded in `ℂ_[p]` rather than abstract). However — and this is the key point —
the strictly-more-general *and* idiomatic form is **already in mathlib** as
`(𝓞 K)ˣ` (see Phase 5). So this is not a "generalise-then-PR" situation; the
generalised form is not a gap. Number of weakening opportunities found: 3 (rows
above), **all of which land on an object mathlib already has**.

Proposed restatement (for the record, = the existing mathlib object):
`(NumberField.RingOfIntegers K)ˣ` for `K` a number field, i.e. `(𝓞 K)ˣ`.

Cost of restatement: n/a — it would be deleting the project def in favour of a
mathlib def, not re-proving a generalisation. (Bridging the *embedded* form used
in this project to the abstract form is real work, but that bridge is a project-
internal refactor, not a mathlib contribution — see Phase 7.)

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partially | use `[NumberField K]` + `(𝓞 K)ˣ` instead of a hand-rolled embedded subgroup | the entire `NumberField.Units` API (Dirichlet, torsion, regulator, complex embeddings) |
| 2 | sequences/metric → filters/topological? | no | — | the def has no convergence content; it is purely algebraic. |
| 3 | construct an object → universal-property class? | yes | `O_K = integralClosure ℤ K` already *is* the universal (maximal-order / integral-closure) characterization; `(𝓞 K)ˣ` is its unit group | composes with `IsIntegralClosure`, `IsDedekindDomain`, localization API |
| 4 | set-with-closure-predicate → bundled-substructure type? | yes (already half-done) | the file already bundles a `Subgroup`; the idiomatic target bundles the *ring* (`𝓞 K`) and takes its units, so `Subgroup`/lattice ops compose with the whole ring-of-integers stack | `Subalgebra`/`Subgroup` lattice, quotients, `Set.unit`/`Set.integer` S-arithmetic |
| 5 | field/metric-specific → weaken typeclasses? | yes | drop `ℂ_[p]` entirely; `(𝓞 K)ˣ` needs only `[NumberField K]` | scalar-tower-independent; works for every number field uniformly |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no (the `n` indexes the *field*, not an algebraic structure to generalise) | — | the `n`-tower is intrinsic to Iwasawa theory; not a spurious concrete index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, and it is **already realized in mathlib** as
`(𝓞 K)ˣ` (`NumberField.RingOfIntegers` + its units API). Crucially, this does
**not** flip the verdict to YES-but-generalise-first: the modern/general form is
not a missing contribution we should build — it *exists in mathlib*. Hence the
modern-idiom finding *reinforces* `NO-mathlib-has-it`, it does not create a YES.
Real mathematical improvement of the idiomatic form: it unlocks the full
`NumberField.Units` ecosystem (Dirichlet's unit theorem, torsion, regulator) for
free — none of which the embedded `ℂ_[p]ˣ`-subgroup form can reach.

---

## Diamond / defeq risk — `globalUnits` (Phase 4.5)

(`def`, so the phase runs. It is a *plain* `def`, not an `instance`/`class`/coercion.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | it is a `def` returning a `Subgroup`, not an `instance`; it participates in no typeclass-search path. |
| 2 | Reducibility leak | none | no `@[reducible]`; it is a sealed bundled `Subgroup`, exposed only through `SetLike` membership. |
| 3 | Non-canonical unfolding | low | `simp` will unfold `· ∈ globalUnits p n` to the three carrier conditions via the auto-generated `mem` simp-lemma; this is the intended API and is unsurprising. |
| 4 | Instance priority collision | none | not an `instance`. |
| 5 | Universe-polymorphism issues | none | all types are concrete (`ℂ_[p]ˣ`, `ℕ`); no universe variables. |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort`; the only coercion is the standard `Subgroup → Set` from `SetLike`. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE.** Top risks: none. (This row matters only if the verdict
were a YES bucket; it is not. Recorded for completeness.)

---

## Mathlib search-status: `globalUnits` (Phase 5)

[A] Lean-Finder       (web service; queried via the conceptual phrasing of [C]) — folded into [C], no distinct hit beyond `(𝓞 K)ˣ`
[B] Loogle            `Subgroup (Units _)` → returns `Units.posSubgroup`, `rootsOfUnity`, `Unitization.unitsFstOne`, … (no integrality/ring-of-integers unit-group hit); `IntermediateField, IsIntegral, Subgroup` → **"Found 0 declarations"**; `Subgroup Units , IsIntegral` → type error (no hit)
[C] LeanSearch        "unit group of the ring of integers of a number field" → endpoint 404 on the JSON API this run; the object is nonetheless the well-known `(𝓞 K)ˣ` (`NumberField.Units.*`), confirmed directly via grep [D]
[D] Grep mathlib src  `RingOfIntegers`, `(𝓞 K)ˣ`, `integralClosure`, `Subgroup .*ˣ`, `globalUnits`, `PadicComplex.*unit` over `.lake/packages/mathlib/Mathlib/` — see hits below
[E] Name pattern      grep `globalUnits` over all of mathlib → **0 hits** (no decl by this name); `Set.unit`/`Set.integer` (S-units), `NumberField.Units.torsion`, etc. found by name

Searched for both:
- the user's current form (embedded `Subgroup ℂ_[p]ˣ` via `IntermediateField` + `IsIntegral`) — **not in mathlib** (Loogle: 0 decls combining those three; grep: no `globalUnits`, no units-of-integral-closure-as-`Lˣ`-subgroup).
- the literature-standard / abstract form (`(𝓞 K)ˣ` for a number field) — **in mathlib**, with rich API:
  - `NumberField.RingOfIntegers K = integralClosure ℤ K` (`Mathlib/NumberTheory/NumberField/Basic.lean:100`), notation `𝓞 K`.
  - `(𝓞 K)ˣ` with `NumberField.isUnit_iff_norm`, `NumberField.Units.torsion`, `torsionOrder`, complex embeddings, and **Dirichlet's unit theorem** + **regulator** (`Mathlib/NumberTheory/NumberField/Units/Basic.lean`, `…/DirichletTheorem.lean`, `…/Regulator.lean`).
  - For the *cyclotomic* base specifically: `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton` and `IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow` give `𝓞 (CyclotomicField (p^k) ℚ) ≃ ℤ[ζ]` (`Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`).
  - Cyclotomic-unit *facts* (not the group): `Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` (`IsPrimitiveRoot.geom_sum_isUnit`, `associated_sub_one_pow_sub_one_of_coprime`, …).
  - Nearest *subgroup-of-`Kˣ`* analog: `Set.unit S K : Subgroup Kˣ` (S-units) + `Set.unitEquivUnitsInteger : S.unit K ≃* (S.integer K)ˣ` (`Mathlib/RingTheory/DedekindDomain/SInteger.lean:108,124`) — but only for `K` = fraction field of a Dedekind domain, via *valuation*, not the C_p-embedded *integrality* form.

Concluded: **"found in mathlib as `(NumberField.RingOfIntegers K)ˣ` (i.e. `(𝓞 K)ˣ`); strictly more general (any number field) and idiomatic; the project's `globalUnits p n` is the same mathematical object (`O_{F_n}^×`) re-presented as a subgroup of `ℂ_[p]ˣ`."** The project's *exact embedded form* is not in mathlib (correctly — the embedding is a project-local device, and the general form is what mathlib carries).

---

## Call sites — `globalUnits` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring file): **0
real code uses.**
External-to-file callers: 1 file (`IwasawaProof/Generators.lean`) — but **all 3
matches there are in comments / docstrings, not code.**

| Caller file:line | Usage pattern (one-line excerpt) | Code or comment? |
|------------------|----------------------------------|------------------|
| IwasawaProof/Generators.lean:214 | `-- membership in 𝒟_n = closure(cycloGenSet) ⊓ globalUnits` | **comment** |
| IwasawaProof/Generators.lean:268 | `-- −1 ∈ 𝒟_n = closure(cycloGenSet) ⊓ globalUnits` | **comment** |
| IwasawaProof/Generators.lean:1484 | `` `globalUnits`-preservation `galAut_mem_Fglobal`/… `` (docstring) | **comment** |

Real code uses, by contrast, are concentrated **inside the declaring file**
(`Iwasawa/CyclotomicUnits.lean`): `globalUnitsPlus` (carrier built on it, line 126,
136), `globalUnits_le_localUnits` (157), `cycloUnits := closure … ⊓ globalUnits p n`
(183), `cycloUnits_le_globalUnits` (201), `cyclo_elems_mem_globalUnits` (406, 408),
`cyclo_elems_mem_cycloUnits` (425), `cyclo_mem_cycloTower1` (480). So it is genuine
*intra-file* API — `globalUnits` is the `⊓`-factor that makes `cycloUnits` "global"
and the target of `globalUnits_le_localUnits` (RJW TeX 3084) — but it has **no
consumer outside its own file**.

Inline-derivation grep (was `O_{F_n}^×` re-derived elsewhere without `globalUnits`?):
(none found) — the abstract `(𝓞 F_n)ˣ` is not used anywhere in the project; the
project consistently works with this embedded form.

What the pattern tells us: K = 0 external code uses, **but** the def is a real
load-bearing `⊓`-factor *inside* its file (it is not dead code, and not a bypassed
wrapper). This is the "foundational building block of one self-contained
development" pattern: it earns its place *in the project*, but the absence of any
cross-file/cross-project consumer — combined with mathlib already owning the
general object — means it is not pulling its weight as a *mathlib* contribution in
this embedded form.

### Composition check (Phase 6)

Can `globalUnits` be *defined* by composing mathlib primitives in ≤3 calls?

Attempt 1: take `(𝓞 F_n)ˣ` and transport along the field embedding `F_n ↪ ℂ_[p]`.
  - Mathlib decls used: `NumberField.RingOfIntegers`, `Units.map`, an `AlgHom F_n → ℂ_[p]` / `Subgroup.map`.
  - Result: **fails as a ≤3-call composition.** There is no off-the-shelf `AlgHom F_n →ₐ[ℚ] ℂ_[p]` packaged here; one must (a) exhibit the embedding `Fglobal p n ↪ ℂ_[p]` as an algebra map, (b) push `(𝓞 F_n)ˣ` through `Units.map`, and (c) prove the image equals the three-condition carrier. That is real bridging infrastructure (an `IsIntegralClosure` transport + an injectivity/image argument), not a one-liner.
  - Notes: this is exactly why the project chose the embedded form — the bridge is non-trivial, so it defined the subgroup directly in `ℂ_[p]ˣ`.

Attempt 2: build it directly from `Set.unit`/`Set.integer` (S-units of a Dedekind domain).
  - Mathlib decls used: `Set.unit`, `Set.integer`, `IsDedekindDomain.integer_empty`.
  - Result: **fails** — `Set.unit S K` lives in `Kˣ` for `K` = fraction field of the Dedekind domain and is defined by *valuation* `v(x)=1`, not by the `IsIntegral ℤ`/`ℂ_[p]`-membership conditions used here. Not directly composable into the file's `ℂ_[p]ˣ` subgroup.

Conclusion: **NOT-COMPOSABLE** as a ≤3-call mathlib composition *in the embedded
form*. (This rules out `NO-composable-from-mathlib`. The right NO bucket is
`NO-mathlib-has-it`: mathlib has the *object* `(𝓞 K)ˣ`; what is "not composable"
is only the project's deliberate C_p-embedded re-presentation of it.)

---

## Verdict: `globalUnits` (Phase 7)

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the concept is the global unit group `O_K^×` of the
  ring of integers of a number field — fully standard (Washington/Neukirch/Wikipedia/nLab);
  the file's three carrier conditions are a literal transcription of `O_{F_n}^×`,
  and the source paper (arXiv:2309.15692) uses exactly the `𝒱_n = O_{F_n}^×` notation.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only,
  embedded in `ℂ_[p]`), with the strictly-more-general *and* idiomatic form —
  `(𝓞 K)ˣ` — **already present in mathlib**. Phase 4c confirms the modern idiom
  is the existing mathlib object, so the finding reinforces NO (it does not create
  a YES-but-generalise-first).
- Mathlib search (Phase 5): found in mathlib as **`(NumberField.RingOfIntegers K)ˣ`**
  (`= (𝓞 K)ˣ`), more general and idiomatic, with the full Dirichlet/torsion/regulator
  unit API; cyclotomic specialization available via `IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow`.
  The project's embedded form has **no** mathlib counterpart by name (and shouldn't).
- Composition check (Phase 6): NOT-COMPOSABLE in ≤3 calls (so not the `composable`
  bucket); call sites — K = 0 external code uses (the 3 `Generators.lean` hits are
  comments), real uses are intra-file only.

**Rationale.**
The mathematics here is a textbook object: `globalUnits p n` is `O_{F_n}^×`, the
unit group of the ring of integers of the cyclotomic number field `F_n = ℚ(μ_{p^n})`.
Mathlib already owns this object in its maximally general, idiomatic form —
`(𝓞 K)ˣ` for any number field `K` (`NumberField.RingOfIntegers` = `integralClosure ℤ K`,
with `(𝓞 K)ˣ` carrying Dirichlet's unit theorem, torsion, the regulator, and
complex-embedding API), plus the cyclotomic identification
`𝓞 (CyclotomicField (p^k) ℚ) ≃ ℤ[ζ]`. The project's declaration is the *same*
object, deliberately re-presented as a subgroup of `ℂ_[p]ˣ` (the "everything inside
`ℂ_p`" convention of RJW / decomposition replan R11.7) so that global units `𝒱_n`
and local units `𝒰_n` live in one ambient group and `globalUnits_le_localUnits`
(RJW TeX 3084) is literally a `Subgroup ℂ_[p]ˣ` inclusion. That embedding is a
sound *project* engineering choice, but it is **not** a mathlib contribution: it is
neither more general than `(𝓞 K)ˣ` nor a missing idiom — it is a specialization of
a thing mathlib has, wrapped in a project-local ambient. Adding the C_p-embedded
form to mathlib would duplicate `(𝓞 K)ˣ` in a strictly less general, less reusable
shape (no Dirichlet, no regulator, no scalar-tower freedom), which is exactly what
mathlib's "one general form" rule forbids.

The one honest caveat — and why the C_p-embedded design is a project-local matter
rather than a mechanical delete-and-replace — is that the user's form does **not**
follow from `(𝓞 F_n)ˣ` in a literal ≤1 line: bridging "subgroup of `ℂ_[p]ˣ` cut out
by `∈ Fglobal` + `IsIntegral ℤ`" to "`(𝓞 F_n)ˣ` transported along `F_n ↪ ℂ_[p]`"
needs the algebra embedding plus an image/injectivity argument (Phase 6, Attempt 1).
That bridge is genuine work, but it is *project-internal refactoring infrastructure*,
not new mathematics for mathlib — the destination object already exists upstream.

**WHY not (refactor-actionable).** Mathlib already has the result as
`(NumberField.RingOfIntegers F_n)ˣ`, i.e. `(𝓞 F_n)ˣ`, the unit group of
`integralClosure ℤ F_n`. The project's `globalUnits p n` equals the image of this
group under the field embedding `F_n ↪ ℂ_[p]` (concretely, the three carrier
conditions `∈ Fglobal p n`, `IsIntegral ℤ u`, `IsIntegral ℤ u⁻¹` say exactly "`u`
is the image of a unit of `O_{F_n}`").

Existing mathlib decl:        `NumberField.RingOfIntegers` → `(𝓞 K)ˣ`
Located at:                   `Mathlib/NumberTheory/NumberField/Basic.lean:100`
                              (units API: `Mathlib/NumberTheory/NumberField/Units/Basic.lean`;
                              cyclotomic bridge: `IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow`,
                              `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean`)
Relationship (NOT a literal ≤1-line specialization — see caveat above):
```lean
-- conceptually: globalUnits p n = (the image of (𝓞 F_n)ˣ under F_n ↪ ℂ_[p])
-- u ∈ globalUnits p n  ↔  ∃ w : (𝓞 F_n)ˣ, embedding (w : F_n) = (u : ℂ_[p])
-- bridging this requires the AlgHom F_n →ₐ[ℚ] ℂ_[p] and a Units.map/Subgroup.map image argument.
```
Call sites in the project (from Phase 6.0): **0 external** (3 comment-only mentions
in `Generators.lean`); all real uses are intra-file (`cycloUnits`, `globalUnitsPlus`,
`globalUnits_le_localUnits`, the `cyclo_*` milestone lemmas).

Refactor plan (project-internal — this is **not** a mathlib PR, it is a "should the
project keep its own embedded def?" decision; treat the rows below as the cleanup
options, gated on the BORDERLINE-style question in the next paragraph):
- Option A (minimal — recommended for a WIP Iwasawa development): **keep
  `globalUnits` as a project-local def**, but add a docstring cross-reference to
  `(𝓞 K)ˣ` and, when convenient, a bridging lemma
  `globalUnits p n = ((𝓞 (Fglobal p n))ˣ).map (Units.map embedding)` so the project
  can borrow mathlib's Dirichlet/regulator API. Do **not** PR the embedded def.
- Option B (full upstream alignment): refactor the whole `Iwasawa/` tower to work
  with abstract `(𝓞 F_n)ˣ` and an embedding into `ℂ_[p]` only where the *p-adic
  topology* is genuinely needed (the local closures `𝒞_n`), replacing the embedded
  `globalUnits` at its ~8 intra-file uses with the bridged mathlib object. This is
  the "Bourbaki 2.0" form but is a substantial project refactor, not a one-liner.

Next action: do **not** open a mathlib PR for `globalUnits` (mathlib has `(𝓞 K)ˣ`).
Keep it project-local (Option A), and if upstreaming anything from this file, the
candidates are the *p-adic-specific* results (`norm_le_one_of_isIntegral_int`, the
`ℂ_[p]`/`zpPow` machinery), not this unit-group definition.

> Borderline note (not the verdict, but flagged for the maintainer): the *only*
> thing keeping this from a frictionless `NO-mathlib-has-it` is the C_p-embedding,
> which is a deliberate project-architecture decision. If the project ever decides
> the Iwasawa tower should be built on abstract `(𝓞 F_n)ˣ` + a topology only at the
> closure step, the embedded `globalUnits` becomes pure redundancy and Option B
> applies. That architecture call is the maintainer's, not the skill's — but it does
> not change the bucket: in *either* architecture the object itself is one mathlib
> already has.

---

## Next step

Do **not** open a mathlib PR for `globalUnits` — mathlib already has the global
unit group of a number field's ring of integers as `(NumberField.RingOfIntegers K)ˣ`
(`= (𝓞 K)ˣ`), strictly more general and with the full Dirichlet/torsion/regulator
API. Keep `globalUnits p n` as a project-local definition (the `ℂ_[p]`-embedded
presentation is intentional and load-bearing *within* this Iwasawa development),
ideally with a docstring/bridging-lemma link to `(𝓞 K)ˣ` so the project can reuse
mathlib's unit-group API. Reserve mathlib-upstreaming effort for the file's genuinely
p-adic results (e.g. `norm_le_one_of_isIntegral_int`), not this unit-group `def`.
