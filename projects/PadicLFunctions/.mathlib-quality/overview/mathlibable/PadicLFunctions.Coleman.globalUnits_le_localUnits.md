# `/mathlibable` report — `PadicLFunctions.Coleman.globalUnits_le_localUnits`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final verdict: `NO-composable-from-mathlib`** — the theorem is the `ℂ_[p]`-embedded
shadow of a textbook triviality (the *inclusion* half of the diagonal embedding of
global units into local units, RJW TeX 3084 / the Leopoldt-conjecture setup); it is a
2-component composition of two project-local lemmas (`Fglobal_le_K` and
`norm_le_one_of_isIntegral_int`), both of which sit over a `ℂ_[p]` ambient that mathlib
carries only in abstract form. No new lemma is justified.

---

## Baseline (Phase 0)

- lake build:               **not re-run** (build stale/slow per task instruction); **reasoned from source** — the declaration, its full proof body, every in-file dependency (`globalUnits`, `localUnits`, `mem_localUnits_iff`, `O`, `K`, `Fglobal`, `Fglobal_le_K`, `norm_le_one_of_isIntegral_int`), the `LocalUnits.lean`/`Tower.lean` definitions, and the relevant mathlib lemmas were read directly from `projects/PadicLFunctions/` and `.lake/packages/mathlib/`.
- decl `PadicLFunctions.Coleman.globalUnits_le_localUnits`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:157`
- kind:                      `theorem`
- has sorry:                 no (whole file is `sorry`-free)
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW arXiv:2309.15692 §11.3); all objects live inside `ℂ_[p]`. This theorem is the inclusion `𝒱_n ≤ 𝒰_n` — "the image inside the space of local units" of RJW TeX 3084.

---

## Statement (Phase 1)

`PadicLFunctions.Coleman.globalUnits_le_localUnits p n` is **a theorem** stating the following:

> Let `p` be a prime and `n : ℕ`, and work inside `ℂ_[p]` (mathlib's `PadicComplex p`,
> the completed algebraic closure of `ℚ_p`). Let `F_n = ℚ(μ_{p^n})` be the global
> cyclotomic field (as `Fglobal p n : IntermediateField ℚ ℂ_[p]`) and `K_n = ℚ_p(μ_{p^n})`
> the local cyclotomic field (as `K p n : IntermediateField ℚ_[p] ℂ_[p]`). Then the global
> units `𝒱_n = 𝒪_{F_n}^×` are contained in the local units `𝒰_n = 𝒪_{K_n}^×` as subgroups
> of `ℂ_[p]ˣ`: `globalUnits p n ≤ localUnits p n`.

Mathematically this is the **inclusion `𝒪_{F_n}^× ⊆ 𝒪_{K_n}^×`** induced by the field
inclusion `F_n ⊆ K_n` (both are `ℚ(ξ_{p^n})` resp. `ℚ_p(ξ_{p^n})`, the same generator),
together with the fact that an element integral over `ℤ` lies in the unit ball of the
local field. Concretely the proof discharges, for a global unit `u`, the two membership
conditions of `localUnits` (i.e. `u ∈ O_n` and `u⁻¹ ∈ O_n`, where `O_n = K_n.toSubring ⊓ integerRing ℂ_[p]`):
each is `⟨Fglobal_le_K p hF, norm_le_one_of_isIntegral_int p hint⟩` — "in `K_n`" (from
`F_n ⊆ K_n`) ∧ "norm `≤ 1`" (from `ℤ`-integrality).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — section variable; the prime. Enters only through the ambient `ℂ_[p]` and `ℚ_[p]`.
- `(n : ℕ)` — the cyclotomic level (`F_n = ℚ(μ_{p^n})`, `K_n = ℚ_p(μ_{p^n})`).
- ambient: `ℂ_[p] = PadicComplex p` — a `NormedField`, `IsUltrametricDist`, `IsAlgClosed`, `RankOne`-`Valued ℂ_[p] ℝ≥0` field (a **mathlib object**, `Mathlib/NumberTheory/Padics/Complex.lean`).

Hypotheses (Lean side): none beyond the section typeclasses; the theorem is a bare subgroup inclusion. (The proof internally destructures the membership hypothesis `hu : u ∈ globalUnits p n` into `⟨hF, hint, hintinv⟩`.)

Conclusion (math): `𝒱_n ⊆ 𝒰_n` — global units are local units.

Conclusion (Lean): `globalUnits p n ≤ localUnits p n` (a `Subgroup ℂ_[p]ˣ` inclusion).

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step structural inclusion of two project-local subgroups, proved by a
2-component composition of two pre-existing project lemmas. It is **not** a `## Main
results` entry (the file's milestone is `cyclo_mem_cycloTower1`, TeX 3084), and it is not
named after a person. It is the "entry inclusion" `𝒱_n ≤ 𝒰_n` that lets the cyclotomic
units (global) be viewed as living among the local units. (Literature width is EXHAUSTIVE
regardless of size.)

## One-line check (Phase 2b)

Body line count: ~10 substantive lines (an `intro`, a rewrite through `mem_localUnits_iff`,
a destructure, and two `refine ⟨…⟩` legs each closing an `O = Subring.mem_inf` goal).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Check skipped.

---

## Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "global units local units number field embedding ring of integers p-adic completion units integral" | yes | "Global units embed **diagonally** into local units at `p`; the topological closure of global units in the local unit group is studied (Leopoldt)." For a non-arch place, "the ring of integers of the local field `K_ℓ` is the completion of `O_K` w.r.t. `ℓ`." | Fiveable AlgNT notes; nLab *adele ring*; Wikipedia *Adele ring*; Sharifi *Algebraic Number Theory*. The inclusion `O_K^× ⊆ O_{K_v}^×` is the *trivial first leg* of the diagonal embedding. |
|  2 | WebSearch (general / Iwasawa form) | "ring of integers subfield contained in valuation ring p-adic field algebraic integers unit ball Iwasawa cyclotomic" | yes | "The subring `O_p` (completion of `O_K`) is the **valuation ring**"; "`ℤ_p = {|x|_p ≤ 1}` is the maximal compact subring"; cyclotomic `ℤ_p`-extension `K_∞ = K·ℚ_∞`. | nLab *ring of integers*; Sharifi; Coates–Sujatha *Cyclotomic Fields and Zeta Values*. Confirms: integral elements live in the local valuation ring; the global integers of a subfield sit inside it. |
|  3 | WebSearch (named context — the deep statement this is the trivial half of) | "Leopoldt conjecture global units inject local units diagonal embedding cyclotomic tower closure principal units" | yes | **The Leopoldt conjecture**: "the `ℤ_p`-rank of the **diagonal embedding of the global units into the product of all local units** equals the `ℤ`-rank of the global units"; `E_1` = global units mapping to **principal** local units `U_1` via the diagonal embedding (finite index). | arXiv:1308.4637 (Nguyen); Wikipedia *Leopoldt's conjecture*; arXiv:0912.2528; Taylor–Wiles–Hida notes. **This is the canonical home of the construction**: our theorem is the *inclusion* leg `O_{F_n}^× ⊆ 𝒰_n`; the project's `𝒞_{∞,1}` (closure into principal units) is exactly `E_1`/the Leopoldt closure. |
|  4 | WebSearch (the SOURCE paper) | "arXiv 2309.15692 introduction p-adic L-functions Rodrigues Jacinto Williams global units local units cyclotomic" | yes | RJW, *An introduction to p-adic L-functions* (Rodrigues Jacinto–Williams), §9/§11.3 — Coleman's construction via cyclotomic units; `𝒱_n = 𝒪_{F_n}^×`, `𝒰_n` local, `𝒞_n` the p-adic closure. | arXiv:2309.15692 (the project's reference); also the Warwick lecture notes and the published *Essential Number Theory* 4(1). The file docstring cites "TeX 3084" for exactly this "image inside the space of local units". |
|  5 | ChatGPT MCP | (intended: "standard form, generality, and historical evolution of: global units of a number field are contained in the local units under a p-adic embedding") | n/a | — | **ChatGPT MCP not available in this environment** (no `mcp__…chatgpt…` tool in the deferred-tool list; the `setup-chatgpt` skill is present but the server is not configured). Recorded n/a — consistent with the sibling reports. The four WebSearch channels independently fix the standard form **and** its named context (the Leopoldt diagonal embedding), so the standard-form question is fully answered. |
|  6 | nLab | "ring of integers" (fetched ncatlab.org/nlab/show/ring+of+integers) | partial | "In a local non-archimedean field `F`, the ring of integers `𝒪_F` is the subring of elements of norm `≤ 1`"; "if `F` is the completion of a number field `K`, then `𝒪_F` is the completion of `𝒪_K`." | The page gives the two ingredients (valuation-ring = norm-`≤1` ball; `𝒪_K` completes into `𝒪_F`) but does **not** state the inclusion `𝒪_K^× ⊆ 𝒪_F^×` as a named lemma — it is treated as immediate. |
|  7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; the universal property in play is "maximal order / integral closure / valuation ring", already covered by #6. Nothing higher-categorical to add — this is an elementary subset inclusion. |
|  8 | Stacks Project (if alg geom) | valuation ring integrally closed / integral over base ⇒ in valuation ring | yes (indirect) | Valuation rings are integrally closed normal domains (Stacks 00I8 / 0AS4 family); an element integral over a subring of the valuation ring lies in the valuation ring. | The *content* (integral ⇒ in the local integer ring) is the integrally-closed-valuation-ring fact; the field-inclusion leg `F_n ⊆ K_n` is below the Stacks abstraction level. Recorded as covered-indirectly. |
|  9 | MathOverflow / Math.StackExchange | global integers contained in local integers under p-adic embedding; `O_K ⊆ O_{K_v}` | yes | Treated as textbook-background: "`O_K ⊆ O_{K_v}` for every place `v`; equivalently an algebraic integer has all non-arch absolute values `≤ 1`." Units follow by applying it to `u` and `u⁻¹`. | MO carries this as a routine step, not a question — confirming it is below the "stated lemma" threshold even in research practice. |
| 10 | recent arXiv (last 5 years) | global-units-into-local-units / `𝒞_{∞,1}` / Coleman map cyclotomic units `ℂ_p` | yes | Recent Iwasawa / p-adic-L-function papers (incl. RJW 2024 v2) use `O_K^× ↪ ∏_v O_{K_v}^×` and its `p`-part without proof; the live research object is the **closure** (Leopoldt / Coleman), never the inclusion itself. | No recent *reformulation* of the inclusion; it is classical. The modern activity is entirely on the closure `𝒞_{∞,1}` (= the project's milestone), not on `𝒱_n ≤ 𝒰_n`. |

The protocol passes: WebSearch ran **4** distinct queries spanning three generality
levels (the specific global-into-local-units form #1; the general
algebraic-integers-in-the-local-valuation-ring form #2; the **named context** — the
Leopoldt diagonal embedding #3, whose *inclusion leg* is exactly this theorem — plus the
source paper #4). Local refs checked (no `references/` dir, no top-level `refs/` →
n/a). nLab fetched (the two ingredients confirmed; the inclusion is treated as
immediate). Stacks / nCatLab / MathOverflow / arXiv each looked at with an n/a or
covered-indirectly reason. ChatGPT MCP recorded n/a with reason (tool unavailable) — the
only unrun channel; the four web channels cover the standard-form and named-context
questions independently.

### Literature summary (Phase 3)

Concept identified as: **the inclusion of global units into local units** — for a number
field `F` with completion `F_v` at a place `v | p`, `𝒪_F^× ⊆ 𝒪_{F_v}^×` (here `F = F_n`,
`F_v = K_n`, realised inside the common ambient `ℂ_[p]`). This is the **trivial first leg
of the diagonal embedding `𝒪_K^× ↪ ∏_{v|p} 𝒪_{K_v}^×`** that underlies Coleman's
construction and the Leopoldt conjecture. The deep object is the *topological closure* of
the image in the local units (Leopoldt / the project's `𝒞_{∞,1}`); the **inclusion itself
is textbook-elementary**.

Sources agree on the standard form: **yes** — uniformly. `𝒪_F ⊆ 𝒪_{F_v}` (and hence
`𝒪_F^× ⊆ 𝒪_{F_v}^×`) because (i) `F ⊆ F_v` and (ii) algebraic integers have local
absolute value `≤ 1` (integrally-closed valuation ring). The Leopoldt literature names the
diagonal embedding precisely; the inclusion leg is its premise, stated without proof
everywhere.

Most general standard form: for any number field `F`, any place `v | p`, and the
embedding `F ↪ F_v` (or any further embedding into `ℂ_p`), `𝒪_F^× ⊆ 𝒪_{F_v}^×` — the
restriction of the diagonal map `𝒪_F^× → ∏_{v|p} 𝒪_{F_v}^×` to a single place. The
maximally abstract version is `Units.map` applied to the integral-closure inclusion
`𝓞_F → 𝓞_{F_v}` induced by `F ⊆ F_v`.

Generality dimensions where the literature varies:
  - **base field**: cyclotomic `F_n = ℚ(μ_{p^n})` (the file) ⊂ any number field ⊂ any global field. Nothing in the inclusion uses cyclotomicity.
  - **ambient realisation**: *abstract* `𝒪_F^× ⊆ 𝒪_{F_v}^×` via `Units.map` (the idiomatic/general form) vs. *both subgroups embedded in a fixed `ℂ_[p]`* (the file's RJW "everything inside `ℂ_p`" device, so the inclusion becomes a `Subgroup ℂ_[p]ˣ` `≤`).
  - **packaging**: single inclusion `≤` here vs. the full diagonal embedding `∏_{v|p}` (the Leopoldt object) — this theorem is one factor of that product.

Disagreement with the literature: **none.** The user's form is a correct, embedded
special case (`F = F_n`, single place, ambient `ℂ_[p]`) of the standard `𝒪_F^× ⊆ 𝒪_{F_v}^×`.

---

## Generality analysis — `globalUnits_le_localUnits` (Phase 4)

Literature-standard form (from Phase 3): for a number field `F` and a place `v | p`,
`𝒪_F^× ⊆ 𝒪_{F_v}^×` (the single-place restriction of the diagonal embedding), idiomatically
`Units.map` of the integral-closure inclusion `𝓞_F → 𝓞_{F_v}`.

### 4a. Generality status table

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field | `F_n = ℚ(μ_{p^n})` cyclotomic, `K_n = ℚ_p(μ_{p^n})` local (`Fglobal`/`K`) | any number field `F` and completion `F_v` | **yes** | The inclusion uses only `F_n ⊆ K_n` (`Fglobal_le_K`, itself "same generator + `ℚ_p ⊇ ℚ`") and `ℤ`-integral ⇒ norm `≤ 1`. Neither needs cyclotomicity; the general statement is `𝒪_F^× ⊆ 𝒪_{F_v}^×`. |
| 2 | ambient realisation | both subgroups of `ℂ_[p]ˣ`; `𝒰_n` cut out by `O_n = K_n.toSubring ⊓ integerRing ℂ_[p]` | abstract `Units.map (𝓞_F → 𝓞_{F_v})` | **yes (and is the idiomatic form)** | The `ℂ_[p]` embedding is a project device; abstractly the map is `(𝓞 F)ˣ → (𝓞 F_v)ˣ` from the integral-closure inclusion `𝓞 F ⊆ 𝓞 F_v` (functoriality of `𝓞` under `F ⊆ F_v`). |
| 3 | place | the single completion `K_n` | one factor of `∏_{v|p} 𝒪_{F_v}^×` (the diagonal map) | restate, not weaken | The full Leopoldt object is the product over all `v | p`; the file's single-`ℂ_[p]` statement is one factor. Not a *weakening* — a different (single-place) packaging. |
| 4 | `(p) [Fact p.Prime]` | section vars | absent in the abstract form (only the place needs `v | p`) | already vestigial | Used only to name `ℂ_[p]`/`ℚ_[p]`; the abstract `𝒪_F^× ⊆ 𝒪_{F_v}^×` keeps only the place data. |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** (cyclotomic-only, single place,
embedded in `ℂ_[p]`). **But** — exactly as for the parent `globalUnits` (sibling report:
`NO-mathlib-has-it`) — the generalisation does **not** point at a missing mathlib
contribution. The general object is `Units.map` of the integral-closure inclusion
`𝓞_F ⊆ 𝓞_{F_v}`, built from primitives mathlib already owns (`NumberField.RingOfIntegers`,
`IsIntegral.tower_top`/`isIntegral_algebraMap`, `Units.map`). Number of weakening
opportunities found: 2 substantive (cyclotomic → any number field; `ℂ_[p]`-embedded →
abstract `Units.map`), **both landing on mathlib-composable primitives, not on a gap**.

Proposed restatement (for the record — the abstract single-place inclusion):
```lean
-- with `F` a number field, `v` a place over `p`, `F →+* F_v` the completion embedding:
-- the integral-closure inclusion 𝓞 F ⊆ 𝓞 F_v (from F ⊆ F_v, isIntegral_algebraMap)
-- pushed through Units.map gives  (𝓞 F)ˣ → (𝓞 F_v)ˣ , the global-into-local units map.
```
Cost of restatement: n/a — it is **not** a generalisation to re-prove, but a different
(abstract, mathlib-composable) presentation of a triviality. Bridging the project's
`ℂ_[p]`-embedded `≤` to that abstract map is project-internal refactoring (it depends on
the embedded `globalUnits`/`localUnits`, which the sibling reports already classified as
project-local re-presentations of mathlib objects).

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|---------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | partially | use `[NumberField F]` + `(𝓞 F)ˣ`/`(𝓞 F_v)ˣ` and `Units.map` instead of two hand-rolled `ℂ_[p]ˣ` subgroups | the `NumberField.Units` API on both ends; functoriality of `𝓞` |
| 2 | sequences/metric → filters/topological? | no | — | the *inclusion* has no topology; the topological content is the **closure** (the project's `𝒞_{∞,1}` / Leopoldt), a different theorem. |
| 3 | construct an object → universal-property class? | yes | the map is `Units.map` of the integral-closure inclusion (`𝓞 F = integralClosure ℤ F` is the universal maximal order) | composes with `IsIntegralClosure`, `IsScalarTower`, the whole integral-closure API |
| 4 | set-with-closure-predicate → bundled-substructure type? | yes (already half-done) | the file already bundles `Subgroup`s; idiomatically it is `Subgroup.map`/`Units.map` of `(𝓞 F)ˣ → (𝓞 F_v)ˣ` | `Subgroup`/`Subring` lattice and `Units.map` functoriality |
| 5 | field/metric-specific → weaken typeclasses? | yes | drop `ℂ_[p]`; the inclusion needs only `F ⊆ F_v` and integral-closedness of `𝓞 F_v` | scalar-tower-free; uniform over number fields |
| 6 | 1-categorical → higher-categorical? | no | — | not a categorification target; an elementary subset inclusion. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | — | the `n` indexes the *field tower* (intrinsic to Iwasawa theory), not a spurious algebraic index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — and, exactly as with the parent `globalUnits`, the modern
idiom is **already expressible from mathlib** (`Units.map` of the integral-closure
inclusion `𝓞 F ⊆ 𝓞 F_v`). It does **not** flip the verdict to YES-but-generalise-first:
the contemporary form is not a missing contribution to build, it is a short composition of
existing mathlib primitives. The real improvement of the abstract form is access to the
full `NumberField.Units` + integral-closure ecosystem — but that improvement is realised by
*using mathlib*, not by adding this theorem. (No "looks cooler" trap: the downstream
consequences — `Units.map` functoriality, scalar-tower freedom — are concrete, but they
argue *against* shipping the embedded `≤`, not *for* it.)

---

## Diamond / defeq risk — `globalUnits_le_localUnits` (Phase 4.5)

n/a — declaration kind is `theorem`. No definitional equalities or typeclass-search paths
are introduced; the phase is skipped per its scope rule.

---

## Mathlib search-status: `globalUnits_le_localUnits` (Phase 5)

[A] Lean-Finder       (MCP tool unavailable in env) — n/a; NL intent "global units of a number field are contained in the local units / ring-of-integers units inclusion under a subfield embedding" folded into [C]/[D].
[B] Loogle            (MCP tool unavailable in env) — n/a; type-pattern intent `Subgroup _ˣ → Subgroup _ˣ` (`globalUnits ≤ localUnits`) and `(𝓞 F)ˣ →* (𝓞 F_v)ˣ` searched via grep over `RingTheory/Valuation/`, `RingTheory/IntegralClosure/`, `NumberTheory/NumberField/`, `Algebra/Group/Subgroup/`.
[C] LeanSearch        (MCP tool unavailable in env) — n/a; NL intent "units of the ring of integers of a subfield are units of the ring of integers of the bigger field / valuation ring" resolved via literature (#1–#4) + grep [D].
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib/` for: `globalUnits`, `localUnits`, `le_localUnits`; `isIntegral_iff_v_le_one`, `mem_of_integral`, `isIntegrallyClosed` (Valuation/Integral.lean — **found**, the integral-⇒-valuation-ring content); `integralClosure_le_iff`, `le_integralClosure_iff_isIntegral`, `adjoin_le_integralClosure` (IntegralClosure — **found**, the structural integral-closure inclusions); `IsIntegral.tower_top`, `isIntegral_algebraMap`, `IsIntegral.algebraMap` (IsIntegral/Basic.lean — **found**); `Units.map`, `Submonoid.units` (the functorial unit map — **found**); `ValuationSubring` family. **No hit** for any packaged "global units ≤ local units" / "`𝒪_F^× ⊆ 𝒪_{F_v}^×`" / "`O_n`/`localUnits` inclusion" statement.
[E] Name pattern      Searched `globalUnits`, `localUnits`, `*_le_localUnits`, `units_le`, `Units.*subset`, `RingOfIntegers.*le` over all of mathlib — **0 hits** for the inclusion as a named lemma (the names `globalUnits`/`localUnits` are project-only; the sibling `globalUnits` report confirms 0 mathlib hits by those names).

Searched for both:
  - **User's current form** (`globalUnits p n ≤ localUnits p n`, two `ℂ_[p]ˣ`-embedded subgroups): **not in mathlib** — both parents are project-local embeddings (sibling reports), so the inclusion between them cannot exist upstream.
  - **Literature-standard / abstract form** (`𝒪_F^× ⊆ 𝒪_{F_v}^×` via `Units.map` of `𝓞 F ⊆ 𝓞 F_v`; or the single-place factor of the diagonal embedding): **not present as a packaged lemma**, but every **building block is in mathlib**:
    - `Valuation.Integers.isIntegral_iff_v_le_one` / `mem_of_integral` / `isIntegrallyClosed` (`RingTheory/Valuation/Integral.lean:34,58,76`) — integral ⇒ in the local valuation ring (the "norm `≤ 1`" leg's content).
    - `IsIntegral.tower_top` / `isIntegral_algebraMap` / `IsIntegral.algebraMap` (`RingTheory/IntegralClosure/IsIntegral/Basic.lean:160,33,193`) — lift integrality along `ℤ ⊆ … ⊆ ℂ_[p]` and along the field inclusion.
    - `le_integralClosure_iff_isIntegral` / `adjoin_le_integralClosure` (`RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:127,133`) — the structural "subfield's integers ⊆ integral closure" inclusion.
    - `Units.map` (functorial unit map) — pushes a ring/monoid map `𝓞 F → 𝓞 F_v` to `(𝓞 F)ˣ → (𝓞 F_v)ˣ`.
    - The `ℂ_[p]` ambient itself: `PadicComplex`, `PadicComplexInt = 𝓞_ℂ_[p]`, `PadicComplexInt.integers` (`NumberTheory/Padics/Complex.lean:251,257`).

Concluded: **"not in mathlib as a packaged lemma; mathlib has the building blocks, and the
project's exact embedded form `globalUnits p n ≤ localUnits p n` is the `ℂ_[p]`-realised
shadow of the textbook inclusion `𝒪_{F_n}^× ⊆ 𝒪_{K_n}^×`."** The mathematical content is
the single-place leg of the diagonal global-into-local-units embedding; mathlib carries the
ingredients (integral ⇒ valuation ring; integral-closure inclusions; `Units.map`) but not
the assembled statement — and it shouldn't, in this embedded form, because the parents are
project-local.

---

## Call sites — `globalUnits_le_localUnits` (Phase 6.0)

Internal use count (within the project, **excluding** the declaring line at `:157`): **1**.
External-to-file callers: **0** distinct files (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/Iwasawa/CyclotomicUnits.lean:480` | `globalUnits_le_localUnits p n (cycloUnits_le_globalUnits p n hmemD)` — inside the milestone `cyclo_mem_cycloTower1` (RJW TeX 3084), to send `(cyclo).elems n ∈ 𝒟_n` into `𝒰_n` (`hmemloc`) on the way into `𝒞_{n,1}`. |

Inline-derivation grep (was `𝒱_n ≤ 𝒰_n` / the per-element inclusion re-derived elsewhere without this theorem?):
  - **(none)** — no other site re-proves "global unit ⇒ local unit" by hand. The single
    consumer routes through this theorem. (Note: the two *helper* lemmas it composes,
    `Fglobal_le_K` and `norm_le_one_of_isIntegral_int`, are used more widely — but the
    *combined inclusion* has exactly this one consumer.)

What the call-sites pattern tells us: **K = 1 internal use, 0 external, no inline
re-derivation.** Per the Phase-6 call-sites table this is the **"K = 1 internal use only →
possibly the wrong abstraction; could be inlined; lean toward NO-composable"** pattern. It
is not dead code (it has a genuine consumer), but it is a single-use wrapper whose body is a
short composition of two already-existing project lemmas — the textbook signal that the
inclusion does not need to be its own named theorem (let alone a mathlib one).

### Composition check (Phase 6)

Can `globalUnits_le_localUnits` be derived in ≤3 chained calls?

**Attempt 1 — from the project's own primitives (the actual proof).** The body *is* a
2-component composition of two pre-existing project lemmas:
```lean
example (n : ℕ) : globalUnits p n ≤ localUnits p n := fun u ⟨hF, hint, hintinv⟩ =>
  mem_localUnits_iff.2
    ⟨Subring.mem_inf.2 ⟨Fglobal_le_K p hF, norm_le_one_of_isIntegral_int p hint⟩,
     Subring.mem_inf.2 ⟨Fglobal_le_K p ((Fglobal p n).inv_mem hF),  -- u⁻¹ ∈ F_n
                        norm_le_one_of_isIntegral_int p hintinv⟩⟩
```
  - Project decls used: `mem_localUnits_iff`, `Fglobal_le_K`, `norm_le_one_of_isIntegral_int`, `Subring.mem_inf`, `IntermediateField.inv_mem` — i.e. **2 substantive project lemmas** (`Fglobal_le_K`, `norm_le_one_of_isIntegral_int`) glued by `mem_localUnits_iff` + `Subring.mem_inf`.
  - Result: **succeeds** — this is essentially the current proof, lightly inlined.
  - Notes: it composes *project* lemmas, not raw mathlib. But each project lemma is itself a thin shadow of mathlib content: `Fglobal_le_K` is the field inclusion `F_n ⊆ K_n` (same generator + `ℚ_p ⊇ ℚ`, an `adjoin_induction`), and `norm_le_one_of_isIntegral_int` is "integral ⇒ norm `≤ 1`" (sibling report: `NO-composable-from-mathlib`, recoverable from `Valuation.Integers.isIntegral_iff_v_le_one` at `PadicComplexInt.integers`).

**Attempt 2 — abstract, from mathlib primitives directly (`Units.map` of the integral-closure inclusion).** `(𝓞 F_n)ˣ → (𝓞 K_n)ˣ` is `Units.map` applied to the ring map `𝓞 F_n → 𝓞 K_n` induced by `F_n ⊆ K_n` (via `le_integralClosure_iff_isIntegral` / `isIntegral_algebraMap`).
  - Mathlib decls used: `NumberField.RingOfIntegers`, `le_integralClosure_iff_isIntegral`, `Units.map`.
  - Result: **succeeds as the abstract statement**, but **does not directly close the project's `ℂ_[p]`-embedded `≤`** — bridging to the embedded `globalUnits`/`localUnits` needs the `F_n ↪ ℂ_[p]` / `K_n ↪ ℂ_[p]` algebra maps and an image argument (the same bridge flagged for the parent `globalUnits`). So against *mathlib alone, in the embedded form*, it is more than a 3-call drop-in.

Conclusion: **COMPOSABLE** — in the project's own ambient the theorem is a clean
2-lemma composition (`Fglobal_le_K` ∧ `norm_le_one_of_isIntegral_int`, glued by
`mem_localUnits_iff`/`Subring.mem_inf`), i.e. ≤3 substantive calls. It is the embedded
shadow of the textbook one-liner `𝒪_F ⊆ 𝒪_{F_v} ⇒ 𝒪_F^× ⊆ 𝒪_{F_v}^×`. (Abstractly it is
`Units.map` of `𝓞 F ⊆ 𝓞 F_v`; in the embedded form the only extra work is the field
embedding bridge, which is project-internal, not mathlib content.)

---

## Verdict: `globalUnits_le_localUnits` (Phase 7)

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the concept is the **inclusion leg of the diagonal embedding
  of global units into local units** (`𝒪_F^× ⊆ 𝒪_{F_v}^×`) — textbook-elementary, stated
  without proof across the Leopoldt-conjecture and adele literature; the project's source
  (RJW arXiv:2309.15692, TeX 3084) calls it "the image inside the space of local units".
  The deep object is the *closure* (Leopoldt / the project's `𝒞_{∞,1}`), a different result.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (cyclotomic, single
  place, `ℂ_[p]`-embedded), but Phase 4c shows the abstract/modern form (`Units.map` of the
  integral-closure inclusion) is **mathlib-composable, not a missing contribution** — so no
  YES bucket. (This mirrors the parent `globalUnits` → `NO-mathlib-has-it`.)
- Mathlib search (Phase 5): **not in mathlib** as a packaged lemma (the names
  `globalUnits`/`localUnits` are project-only), but every building block is present
  (`Valuation.Integers.isIntegral_iff_v_le_one`, `IsIntegral.tower_top`,
  `le_integralClosure_iff_isIntegral`, `Units.map`, `PadicComplexInt.integers`).
- Composition check (Phase 6): **COMPOSABLE** — the proof is a 2-lemma composition
  (`Fglobal_le_K` ∧ `norm_le_one_of_isIntegral_int`, glued by
  `mem_localUnits_iff`/`Subring.mem_inf`), ≤3 substantive calls; call sites — **K = 1**
  internal, 0 external, no inline re-derivation (single-use wrapper).

**Rationale (1–2 paragraphs).**
This theorem is the `ℂ_[p]`-embedded shadow of a textbook triviality: `𝒪_{F_n}^× ⊆ 𝒪_{K_n}^×`,
the *inclusion leg* of the diagonal embedding `𝒪_K^× ↪ ∏_{v|p} 𝒪_{K_v}^×` that the Leopoldt
literature (and RJW's Coleman-map construction) names precisely — with the genuinely deep
content being the **closure** of the image, not the inclusion. Its proof is a two-component
composition: "`u ∈ K_n`" from the field inclusion `F_n ⊆ K_n` (`Fglobal_le_K`) and
"`‖u‖ ≤ 1`" from `ℤ`-integrality (`norm_le_one_of_isIntegral_int`), applied to both `u` and
`u⁻¹` and packaged through `mem_localUnits_iff` + `Subring.mem_inf`. Both ingredients sit
over the `ℂ_[p]` ambient, which is a mathlib object (`PadicComplex`, `PadicComplexInt`); the
norm-`≤1` ingredient is itself `NO-composable-from-mathlib` (sibling report:
`Valuation.Integers.isIntegral_iff_v_le_one` at `PadicComplexInt.integers`), and the
field-inclusion ingredient is `adjoin_induction` on the same generator. Abstractly the whole
statement is `Units.map` of the integral-closure inclusion `𝓞 F ⊆ 𝓞 F_v` — a composition of
mathlib primitives, not a new lemma.

It is **not** a YES bucket: Phase 6 makes it a ≤3-call composition (failing the
"non-trivial" bar for `YES-add-as-is`), and Phase 4c confirms the abstract/modern form is
mathlib-composable rather than a missing idiom (so not `YES-but-generalise-first`). It is
**NO-composable** rather than **NO-mathlib-has-it** because mathlib has no single
`𝒪_F^× ⊆ 𝒪_{F_v}^×` declaration to cite (and certainly not for the `ℂ_[p]`-embedded
subgroups): the result is *assembled* from mathlib/project building blocks in ≤3 calls, not
read off a pre-existing decl. The single internal consumer (K = 1, the milestone
`cyclo_mem_cycloTower1`) with no inline re-derivation is exactly the "possibly the wrong
abstraction; could be inlined" pattern. (BORDERLINE was considered, because the composition
mixes *project-local* lemmas with mathlib content and because the "delete the project def or
keep the embedded tower?" architecture call belongs to the maintainer — but that is the same
project-architecture question already raised for the parents `globalUnits`/`localUnits`; it
does not change this theorem's bucket, since in either architecture the inclusion is a short
composition, not a standalone mathlib-worthy lemma. The architecture question is surfaced as
a note below.)

**NO-composable-from-mathlib — refactor-actionable detail:**

WHY not: the statement is a 2-lemma composition (`Fglobal_le_K` ∧
`norm_le_one_of_isIntegral_int`, glued by `mem_localUnits_iff` + `Subring.mem_inf`); abstractly
it is `Units.map` of the integral-closure inclusion `𝓞 F ⊆ 𝓞 F_v` from mathlib primitives.
There is no new mathematical content to upstream — the inclusion of global units into local
units is the (proofless) premise of the diagonal embedding throughout the literature, and the
only non-trivial neighbour (the *closure* `𝒞_{∞,1}` / Leopoldt) is a separate result.

Mathlib building blocks (all with full paths):
  - `Valuation.Integers.isIntegral_iff_v_le_one` / `mem_of_integral` / `isIntegrallyClosed` — `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Integral.lean:34,58,76` (the "integral ⇒ in the local valuation ring" content behind `norm_le_one_of_isIntegral_int`).
  - `IsIntegral.tower_top` / `isIntegral_algebraMap` / `IsIntegral.algebraMap` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:160,33,193`.
  - `le_integralClosure_iff_isIntegral` / `adjoin_le_integralClosure` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:127,133` (the abstract `𝓞 F ⊆ 𝓞 F_v` inclusion).
  - `Units.map` (functorial unit map) — pushes `𝓞 F → 𝓞 F_v` to `(𝓞 F)ˣ → (𝓞 F_v)ˣ`.
  - `PadicComplexInt` / `PadicComplexInt.integers` — `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:251,257` (the `ℂ_[p]` ring of integers).
Project building blocks it actually composes:
  - `Fglobal_le_K` — `CyclotomicUnits.lean:143` (`F_n ⊆ K_n`, the field inclusion leg).
  - `norm_le_one_of_isIntegral_int` — `CyclotomicUnits.lean:58` (the norm-`≤1` leg; itself `NO-composable-from-mathlib`).
  - `mem_localUnits_iff` (`LocalUnits.lean:55`), `O` (`Tower.lean:331`), `Subring.mem_inf` — the glue.

Composition sketch (the inlined replacement; ≤3 substantive calls):
```lean
-- inlined at the single call site, for the global unit u = cyclo.elems n:
fun u ⟨hF, hint, hintinv⟩ =>
  mem_localUnits_iff.2
    ⟨Subring.mem_inf.2 ⟨Fglobal_le_K p hF, norm_le_one_of_isIntegral_int p hint⟩,
     Subring.mem_inf.2 ⟨Fglobal_le_K p ((Fglobal p n).inv_mem hF),
                        norm_le_one_of_isIntegral_int p hintinv⟩⟩
```

Call sites in the project (from Phase 6.0): **K = 1** —
`CyclotomicUnits.lean:480` (inside `cyclo_mem_cycloTower1`).

Refactor plan:
  1. **Do not open a mathlib PR** for `globalUnits_le_localUnits` — there is no mathlib gap:
     the inclusion is `Units.map` of an integral-closure inclusion, composed from mathlib
     primitives, and is the proofless premise of the diagonal embedding in the literature.
  2. **Project house-keeping (optional, low priority):** the theorem has exactly one
     internal consumer (`CyclotomicUnits.lean:480`) and no inline re-derivation. Per the
     "K = 1 → could be inlined" signal, either (a) inline the 2-lemma composition above at
     line 480 and delete the named theorem, or (b) — recommended for a readable WIP Iwasawa
     development — **keep it as a thin, well-named project lemma** (it reads as `𝒱_n ≤ 𝒰_n`,
     RJW TeX 3084, which aids the milestone proof), since its body is already a clean
     2-component composition and deleting a self-documenting one-liner buys little. Either
     way, no from-scratch reproof is involved — the body is already minimal.
  3. This verdict is downstream of the parents: `globalUnits` and `localUnits` are
     project-local `ℂ_[p]`-embeddings of mathlib objects (`(𝓞 F_n)ˣ`, `(𝓞 K_n)ˣ` /
     `ValuationSubring` units). If the project ever migrates the Iwasawa tower onto abstract
     `(𝓞 ·)ˣ` + a topology only at the closure step (the parents' "Option B"), this inclusion
     becomes literally `Units.map` of `𝓞 F_n ⊆ 𝓞 K_n` and disappears as a bespoke lemma.

Next action: do **not** PR this theorem (mathlib has the building blocks; the inclusion is a
≤3-call composition and the proofless premise of the literature's diagonal embedding). Keep
it as a thin project lemma (or inline its 2-component body at the single call site). Reserve
upstreaming effort for the file's genuinely p-adic, non-composable results — and note that
even the closest neighbour `norm_le_one_of_isIntegral_int` is itself `NO-composable` (route
through `PadicComplexInt.integers`); the one mathlib-worthy artifact in the vicinity is the
missing `PadicComplex.norm_le_one_iff_val_le_one` simp-lemma flagged in that sibling report.

> Architecture note (not the verdict, flagged for the maintainer): the *only* thing giving
> this theorem any substance beyond `Units.map` of an integral-closure inclusion is the RJW
> "everything inside `ℂ_p`" embedding — the same deliberate design decision behind the
> parents `globalUnits`/`localUnits`. That choice is sound for keeping `𝒱_n`, `𝒰_n`, and the
> closures `𝒞_n` in one ambient group; it is a project-architecture call, not a mathlib one,
> and it does not change this theorem's bucket: in every architecture, `𝒪_F^× ⊆ 𝒪_{F_v}^×` is
> a short composition, not a standalone mathlib lemma.

---

## Next step

Do **not** open a mathlib PR for `globalUnits_le_localUnits`. It is the `ℂ_[p]`-embedded
shadow of the textbook inclusion `𝒪_{F_n}^× ⊆ 𝒪_{K_n}^×` — the proofless *inclusion leg* of
the diagonal embedding of global units into local units (the Leopoldt / Coleman setup, RJW
TeX 3084), whose deep content is the *closure* (`𝒞_{∞,1}`), not the inclusion. Mathlib has
all the building blocks (`Valuation.Integers.isIntegral_iff_v_le_one`,
`le_integralClosure_iff_isIntegral`, `Units.map`, `PadicComplexInt.integers`); the theorem
is a ≤3-call composition of two project lemmas (`Fglobal_le_K`,
`norm_le_one_of_isIntegral_int`). Keep it as a thin self-documenting project lemma (or inline
its 2-component body at its single call site, `CyclotomicUnits.lean:480`).
