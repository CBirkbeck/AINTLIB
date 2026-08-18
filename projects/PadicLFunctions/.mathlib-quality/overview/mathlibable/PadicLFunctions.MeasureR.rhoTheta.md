# /mathlibable report — `PadicLFunctions.MeasureR.rhoTheta`

**Final verdict: `NO-composable-from-mathlib`** — `rhoTheta` is a single-substantive-line
composition `iota ( twist(χ, μ̃_η) ∘ extendByZero ∘ mulLeft(x⁻¹) )` of *project-internal* operations
on the *project-internal* measure type `MeasureR K ℤ_[p]` (the χ-twisted, units-pushed analogue of
RJW's `ζ_η = x⁻¹·Res_{ℤ_p^×}(μ_η)`). It has **zero external call sites** (used 38× but only inside
its own declaring file `ValuesAtOne.lean`), and every operation it composes except `LinearMap.mulLeft`
is a project decl — the underlying RJW §3–§6 p-adic-measure / Iwasawa-algebra-as-measures layer
(`MeasureR`, `iota`, `twist`, `muEtaCleared`, `extendByZero`, `invUnitsCM`, `DirichletCharacter.toContinuousMapZp`)
does **not** exist in mathlib. So `rhoTheta` is not a shippable standalone object; the right action
is to keep it project-local. This mirrors the sibling `rhoA` verdict (`NO-composable-from-mathlib`).

---

### Baseline (Phase 0)
- lake build:                 **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.MeasureR.rhoTheta`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:290`
- kind:                       `def` (`noncomputable`)
- has sorry:                  no (body is a single composition; `ValuesAtOne.lean` has **0** `sorry`/`admit`)
- module docstring summary:   "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)"
  — Leopoldt's formula `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)` for
  `θ = χη` non-trivial, via the distribution-free formal-power-series route (the explicit
  antiderivative `F̃_θ`, the genuine measure `ρ_θ`, and the `ψ`-collapse / `c↦pc` bookkeeping).

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.rhoTheta` is **a definition** of the following p-adic measure (an element of
the coefficient-extended Iwasawa algebra over the integer ring `𝒪_K := integerRing K`).

For a coefficient field `K` (a complete ultrametric `ℚ_p`-Banach field, `ℂ_p` in the intended
application), a tame Dirichlet character `η` of conductor `D` with `p ∤ D`, a chosen primitive `D`-th
root of unity `ζ ∈ 𝒪_K`, and a wild character `χ` of conductor `p^n`, the object
`rhoTheta p K η hζ hD χ` is the **genuine numerator measure**

  ρ_θ  :=  x⁻¹ · Res_{ℤ_p^×}( μ_θ )   ∈  Λ_{𝒪_K}(ℤ_p) = MeasureR K ℤ_[p],

where `μ_θ` is the `χ`-twist of the (Gauss-cleared) η-measure `μ̃_η` (RJW §5.2's `muEtaCleared`). It is
built exactly as the §5 `zetaEtaCleared` pattern (`ζ_η = x⁻¹·Res_{ℤ_p^×}(μ_η)`, RJW TeX 1866–1868)
applied to the χ-twisted measure and then **pushed forward** from `ℤ_p^×` to `ℤ_p` along the unit
inclusion `ι` (RJW Rem 3.33). Concretely the body integrates `g` by pairing the `x⁻¹·g`-on-units
(extended by zero off the units) against `μ_θ`:

```lean
noncomputable def rhoTheta {D : ℕ} [NeZero D]
    (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D)
    {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    MeasureR K ℤ_[p] :=
  iota p K
    ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp
      ((extendByZero p K).comp
        (LinearMap.mulLeft (integerRing K) (invUnitsCM p K))))
```

It is the object whose Mahler transform (`mahlerK p K (rhoTheta …)`) is differentiated in §6.2 to
extract the constant coefficient feeding Leopoldt's `L_p(θ,1)` formula.

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the prime.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
  (and `[CharZero K]` in the enclosing section) — the coefficient field. These analytic instances
  are genuinely needed *here*: the target type `MeasureR K ℤ_[p] = C(ℤ_p, 𝒪_K) →ₗ[𝒪_K] 𝒪_K` and the
  whole `iota`/`twist`/`muEtaCleared` substrate require the complete-ultrametric-Banach structure
  (`𝒪_K := integerRing K` is the unit ball; the Mahler `RingEquiv` underlying the layer needs
  completeness).
- `D : ℕ` with `[NeZero D]`, `η : DirichletCharacter (integerRing K) D` — the tame conductor + character.
- `ζ : integerRing K`, `hζ : IsPrimitiveRoot ζ D`, `hD : ¬ p ∣ D` — primitive `D`-th root of unity
  (the cyclotomic data of the tame part) and the tame–wild coprimality.
- `n : ℕ`, `χ : DirichletCharacter (integerRing K) (p ^ n)` — the wild (`p`-power conductor) character.

Hypotheses (Lean side): no *propositional* hypothesis is used in the body beyond `hζ`/`hD` flowing
into `muEtaCleared` (which only consumes them as data/side-conditions). It is a plain composition.

Conclusion (math): the §6.2 χ-twisted numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_θ)` — an element of the
coefficient-extended Iwasawa algebra `Λ_{𝒪_K}(ℤ_p)`.

Conclusion (Lean): `MeasureR K ℤ_[p]` — n/a, it is a definition.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a *bookkeeping intermediate* — the genuine numerator measure `ρ_θ`, an internal object of the
§6.2 `L_p(θ,1)` value computation. It is not a named theorem, not a new mathematical *structure* (it
is an inhabitant of the already-defined type `MeasureR K ℤ_[p]`, not a new type/class), and not the
`## Main results` headline (the headline of the file is Leopoldt's `L_p(θ,1)` formula, RJW Thm
6.1(ii) — not `ρ_θ` itself). The "P6-p4" tag in the docstring marks it as a *step* in the project's
P6 decomposition cluster, not a goal. (Note: a person/place-named theorem — Leopoldt — *is* nearby in
the file, but `rhoTheta` is the construction-internal measure feeding it, not the named theorem.)

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** — `iota p K ((twist …).comp ((extendByZero …).comp (mulLeft …)))`.
One-liner verdict: **ONE-LINER** (a single nested-composition expression; the visual line wrapping is
formatting only).

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | Downstream proofs in the same file *unfold* `rhoTheta` immediately and deliberately — e.g. `ValuesAtOne.lean:350` `rw [cmul_apply, rhoTheta, iota, pushforward_apply]` and `:402` `rw [rhoTheta, iota, pushforward_apply]`. The def is a freely-unfolded abbreviation for the composition, not a sealed barrier preventing unfolding; no `@[reducible]`. |
| Avoid typeclass diamonds          | no       | Returns an inhabitant of the existing type `MeasureR K ℤ_[p]` (an `abbrev` for a `LinearMap`); introduces no instance and no typeclass-search target. |
| Mark semantic intent / API name   | partial  | It does give the recurring composite measure `ρ_θ` a readable name used 38× *within the file* (lines 308–1793). But — exactly as with the sibling `rhoA` — the benefit is **intra-file only**: no external consumer (Phase 6, K = 0 external), so it does not name an *external* consumer that depends on a stable name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the "semantic name" benefit is intra-file readability
only and does not meet the Phase-2b bar of naming an external consumer depending on a stable name).
Phase 7 is therefore biased toward a NO bucket — consistent with the Phase-6 call-sites finding
(K = 0 external) and the Phase-6 composition finding (COMPOSABLE).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic L-function L_p(theta,1) Leopoldt formula Dirichlet character measure x^{-1} restriction units Gauss sum logarithm` | **yes** | Leopoldt: values of the p-adic L-function of a non-trivial Dirichlet character are `−(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ θ⁻¹(c)·log_p(1−ζ^c)` — logarithms of cyclotomic units (an early p-adic Beilinson case). The interpolating *measure* `μ` (with `∫χ x^k = L(χ,1−k)`) and its `x⁻¹·Res_{units}` numerator are construction-internal steps. | Top hits: RJW arXiv:2309.15692 (= Essential Number Theory 4(1), 2025, msp); C. Williams' Warwick lecture notes; Koblitz; "Sum expressions for Kubota–Leopoldt" (arXiv:2201.08870). Confirms Leopoldt's `L_p(θ,1)` formula is canonical and exactly what §6.2 proves. |
| 2 | WebSearch (general form / framework) | `Iwasawa algebra p-adic measures continuous functions Z_p topological dual Mahler transform power series` | **yes** | `M(ℤ_p, 𝒪_L) = Hom_cts(C(ℤ_p,𝒪_L), 𝒪_L)` (the 𝒪_L-linear topological dual of continuous functions) ≅ `Λ(ℤ_p) ≅ 𝒪_L[[T]]` via the Mahler/Iwasawa transform; for a profinite abelian `X`, `Meas(X,R) ≅ R[[X]]`. | de Shalit "Mahler bases…" (JTNB 10.5802/jtnb.955); Williams notes; "p-adic moments of L-functions" (arXiv:2507.01836). **The framework `rhoTheta` lives in (`MeasureR K ℤ_[p]` = dual of `C(ℤ_p,𝒪_K)`) is exactly this classical object** — strictly more general than the χ-twisted composite. |
| 3 | WebSearch (named-after / aliases — source paper) | `Rodrigues Jacinto Williams "introduction to p-adic L-functions" arXiv 2309.15692 twisted measure zeta_eta x inverse restriction units` | **yes** | **RJW = J. Rodrigues Jacinto & C. Williams, "An introduction to p-adic L-functions", arXiv:2309.15692 (v2, 19 Dec 2024); Essential Number Theory 4(1), 2025.** Three constructions of `ζ_p` (measure / Coleman-cyclotomic-units / Iwasawa); §5–§6 build the twisted `L_p(θ,s)` and the `s=1` value. | The χ-twist of `μ_η` and the `x⁻¹·Res_{units}` operation are *steps* in §5–§6 of this source, not separately-named objects. The project cites it as RJW (matches sibling `rhoA.md`'s identification). |
| 4 | ChatGPT MCP | (standard-form + generality + historical-evolution prompt) | n/a | — | **ChatGPT MCP server not available/authenticated in this environment** (no ChatGPT tool surfaced; consistent with sibling `rhoA.md`). Compensated with extra WebSearch (#1–#3, #5, #9, #10) and the source paper / its msp + Warwick mirrors (the authoritative channel here). |
| 5 | Local references | grep `.mathlib-quality/references/` for "L_p(θ,1)"/"zeta_eta"/"numerator"/"restriction" | n/a | — | `projects/PadicLFunctions/.mathlib-quality/references/` **does not exist**; no `refs/` symlink; no `*.tex`/`*.bib`/`*.pdf` in the project. Recorded n/a (same as `rhoA.md`). |
| 6 | nLab | `Iwasawa algebra` (`https://ncatlab.org/nlab/show/Iwasawa+algebra`) | **partial** | Confirms `Λ(ℤ_p) ≅ ℤ_p[[T]]` (= completed group ring). Page is brief; does **not** mention the measure-as-dual interpretation, the Mahler transform, p-adic L-functions, or restriction-to-units. | The abstract `Λ(ℤ_p) ≅ 𝒪[[T]]` (the substrate of `MeasureR`/`mahlerK`) is standard; the *measure/numerator* layer is below nLab's coverage. |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept (a concrete element of a concrete dual module); no higher-categorical statement applies. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry concept; Stacks has no "χ-twisted p-adic numerator measure". |
| 9 | MathOverflow / Math.SE | (folded into #1–#3, #6 — Iwasawa-algebra / p-adic-measure / Leopoldt threads) | **partial** | Same as #1/#2/#6: `R[[T]]`-as-measures, the `x⁻¹·Res_{units}` twist, and Leopoldt's `L_p(θ,1)` formula are routine in Iwasawa-theory discussion | No dedicated treatment of a named "ρ_θ"; it is construction-internal. |
| 10 | recent arXiv (Lean formalisation + framework) | `mathlib Lean p-adic L-function Iwasawa algebra measure Z_p formalization Kubota Leopoldt` ; `Sum Expressions for Kubota–Leopoldt p-adic L-functions` | **yes** | A. Narayanan, "Formalization of p-adic L-functions in Lean 3" (arXiv:2302.14491): `L_p` via the **Bernoulli measure** and Iwasawa-theoretic integral, in **mathlib 3** — **not present in current mathlib4** (the `NumberTheory/Padics/` dir confirms). "Sum expressions…" (arXiv:2201.08870) gives Leopoldt-type sums by computing periods of measures. | **Decisive double-confirmation:** (a) the value `L_p(θ,1)` and its measure-period derivation are standard; (b) the entire p-adic-L-function-as-measures *substrate* is **absent from mathlib4** (a prior formalisation existed only in the now-retired Lean 3 mathlib). |

### Literature summary (Phase 3)

Concept identified as: the **χ-twisted, units-pushed genuine numerator measure**
`ρ_θ = ι( x⁻¹·Res_{ℤ_p^×}(μ_θ) )` with `μ_θ` the χ-twist of `μ̃_η`, an internal object of
**RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692 / Essential Number Theory 4(1), 2025) §5–§6.2**'s
measure-theoretic computation of the value `L_p(θ,1)` (Leopoldt's formula). It is the χ-twisted
analogue of RJW's `ζ_η = x⁻¹·Res_{ℤ_p^×}(μ_η)` (TeX 1866–1868, the project's `zetaEtaCleared`),
post-composed with the units→`ℤ_p` pushforward `ι` (RJW Rem 3.33). It is assembled from standard
*operations* on p-adic measures: the χ-twist (`twist`, RJW eq:twist-by-chi), the `x⁻¹`-multiplication
+ extend-by-zero (`mulLeft invUnitsCM` then `extendByZero`, the §5 `zetaEtaCleared` pattern), and the
units pushforward (`iota`).

Sources agree on the standard form: **yes** for the ambient *framework* — `Λ(ℤ_p) ≅ 𝒪[[T]]` =
`𝒪`-valued measures = `𝒪`-linear topological dual of `C(ℤ_p,𝒪)` (Mahler/Iwasawa; de Shalit, Williams),
and Leopoldt's `L_p(θ,1)` formula is canonical. **But** the composite `ρ_θ` itself is **not a
separately-named object** in any source — it is bookkeeping inside one computation (the §6.2 value of
`L_p(θ,1)`).

Most general standard form: there is no "more general ρ_θ" in the literature to aim at — the
generality lives in the *primitives* (measures on a profinite group valued in any p-adic coefficient
ring, the χ-twist, restriction, pushforward), all upstream of this particular composite.

Generality dimensions where the literature varies:
  - profinite base group: `ℤ_p` (target) and `ℤ_p^×` (source of `iota`) here; the framework allows
    any profinite `Z`.
  - coefficient ring: `𝒪_K` for `K` a complete ultrametric `ℚ_p`-Banach field here; the framework
    allows any p-adic coefficient ring `A ⊇ ℤ_p`.
  - These are dimensions of the *primitives* (`MeasureR`/`iota`/`twist`/`muEtaCleared`), not of `rhoTheta`.

Disagreement with the literature: none — the literature simply does not isolate `ρ_θ` as an object;
it is a step. (Treating "the source doesn't name it" as a signal: this is a construction-internal
composite, not a standalone contribution — see Phase 7.)

---

### Generality analysis — `PadicLFunctions.MeasureR.rhoTheta`

Literature-standard form (Phase 3): there is no separately-named standard `ρ_θ`. The relevant
generality lives entirely in the *primitives* (`iota`/`twist`/`muEtaCleared`/`extendByZero`/`invUnitsCM`),
which are themselves project decls, not in this composite. So "compare to the literature-standard form"
reduces to: *is each input operation applied at the right generality, and is the composite the right
thing to name?*

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` | normed field | coefficient field of the Banach / Iwasawa-algebra layer | **NO** | Genuinely used: `MeasureR K ℤ_[p]`, `iota`, `twist`, `muEtaCleared` all require the field/Banach structure (`𝒪_K := integerRing K` = unit ball; the Mahler `RingEquiv` underlying the layer needs it). |
| 2 | `[NormedAlgebra ℚ_[p] K]` | `ℚ_p`-Banach algebra | needed for the `ℤ_p → 𝒪_K` structure map (extend-by-zero, twist) | **NO** | `invUnitsCM`/`twist`/`muEtaCleared` are built through `algebraMap ℤ_[p] (integerRing K)`; the `ℚ_p`-algebra structure is essential. |
| 3 | `[IsUltrametricDist K]` | ultrametric | needed (`integerRing K` = unit ball; nonarch. integrality) | **NO** | The whole `MeasureR`/`integerRing K` layer (`𝒪_K`-valued measures, automatic boundedness) is nonarchimedean by construction. |
| 4 | `[CompleteSpace K]` | complete | needed (Mahler/`muEtaCleared` `RingEquiv` ≅ power series requires completeness) | **NO** | Completeness underlies `mahlerRingEquiv` (defining `muEtaCleared`) and the Mahler identification used throughout the layer. |
| 5 | `η`, `χ` Dirichlet characters; `ζ`/`hζ`/`hD` | tame char of conductor `D`, wild char of conductor `p^n`, primitive root, `p∤D` | the standing §5.2 hypotheses (`θ = χη`, `η` primitive tame, `χ` of `p`-power conductor) | **NO** | These are exactly RJW's §5.2 standing hypotheses for the twisted L-function; not over-specialisations but the defining data of `θ`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it is — a composite of fixed project primitives
over the natural coefficient field, with the source's own standing character data). Like the sibling
`rhoA`, **every** analytic hypothesis on `rhoTheta` is genuinely used by the `MeasureR`/`iota`/`twist`/
`muEtaCleared` substrate. There are **no weakening opportunities** internal to `rhoTheta`.
Number of weakening opportunities found: **K = 0.**
Proposed restatement: none (no weaker form makes sense for this composite).
Cost of restatement: n/a.

**Important caveat (drives the verdict away from YES).** "MAXIMALLY GENERAL" here is *not* an argument
for `YES-add-as-is`. The generality is fine, but the object is a **thin composition of project-local
operations on a project-local type** with **zero external consumers** (Phase 6). MAXIMALLY-GENERAL +
COMPOSABLE + K=0-external → NO-composable, not YES (cf. Phase 6 heuristics and the verdicts reference:
"K = 1/0 internal-only use ⇒ lean NO-composable").

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclasses? | no | already fully typeclass-based (`[NormedField K]` …); characters are bundled (`DirichletCharacter`) | — |
| 2 | sequences/metric → filters/topology? | no | it is an algebraic element of a dual module; no sequential/metric limit in the def | — |
| 3 | construct object → universal-property class? | no | it is an explicit composite of four maps (`iota`, `twist`, `extendByZero`, `mulLeft`), not a universal object | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | the field/Banach hypotheses are genuinely required by the measure substrate (Phase 4b rows 1–4); nothing to weaken | — |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `D`/`n` are the natural conductors of `η`/`χ`; the base group `ℤ_p`/`ℤ_p^×` is the source's, not a generalisation axis | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** `rhoTheta` is already a contemporary, typeclass-based composite at the
right generality. There is no "let's filter-ise / categorify / weaken-typeclass" move that improves it
— and the only modernisation that *would* matter (formalising the whole RJW §3–§6 p-adic-measure layer
idiomatically) is upstream of `rhoTheta` and is precisely the work the project is doing, not a property
of this one-line composite. One-line reason: this is a construction-internal composition of already-
idiomatic project primitives; there is nothing to modernise about the composition itself.

---

### Diamond / defeq risk — `PadicLFunctions.MeasureR.rhoTheta`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Produces an inhabitant of the existing type `MeasureR K ℤ_[p]` (an `abbrev` for a `LinearMap`); introduces no instance, so nothing new for typeclass search to disambiguate. |
| 2 | Reducibility leak | none | Plain `noncomputable def`, not `@[reducible]`/`abbrev`; the body is exposed only via explicit `rw [rhoTheta, iota, …]` (e.g. `ValuesAtOne.lean:350`, `:402`). |
| 3 | Non-canonical unfolding | low | No `@[simp]`; `simp` will not unfold it; the in-file proofs unfold deliberately. No surprise. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `K : Type*`, `ℤ_[p] : Type`; `MeasureR K ℤ_[p]` is monomorphic in the relevant universes; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort` introduced (it is a `def`, not a coercion); `MeasureR` already carries the `LinearMap` `FunLike`, unchanged here. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none.
Recommended mitigations: none required. (Risk is irrelevant to the final NO verdict anyway — NO
buckets do not add the def to mathlib.)

---

### Mathlib search-status: `PadicLFunctions.MeasureR.rhoTheta`

[A] Lean-Finder        n/a: LSP/MCP Lean-Finder not available in this environment (recorded n/a per
                       `mathlib-search.md`); compensated by [D] grep over mathlib source + [B-as-grep].
[B] Loogle             type-pattern `(C(ℤ_[p], _) →ₗ[_] _)` arising as a χ-twisted, units-pushed
                       numerator measure — n/a (LSP unavailable); emulated via source grep [D]. **No
                       hit**: mathlib has no "measure = `𝒪`-linear functional on `C(ℤ_p,𝒪)`"
                       construction at all (only the *space* `C(ℤ_p,_)` and Mahler's basis on it).
[C] LeanSearch         "p-adic L-function value at 1 twisted measure x⁻¹ restriction to units pushforward
                       coefficient field" — n/a (LSP unavailable); covered by WebSearch #1/#2/#3/#10 +
                       [D].
[D] Grep mathlib src   Over `…/packages/mathlib/Mathlib/` (verified directory
                       `…/aintlib-adic-spaces/.lake/packages/mathlib/Mathlib`):
                       • project names `MeasureR` / `muEtaCleared` / `zetaEtaCleared` / `rhoTheta` /
                         `toContinuousMapZp` → **no hit** (all project-only).
                       • `Leopoldt` / `Kubota` / `Coleman` / `p-adic L-function` / `padicLFunction` /
                         `p-adic measure` / `pseudo-measure` → **no hit** anywhere in
                         `NumberTheory/` (the only `Leopoldt`/`Kubota` string in mathlib is none; the
                         Lean-3 formalisation of these never landed in mathlib4).
                       • `NumberTheory/Padics/` directory = `AddChar`, `Complex`, `Hensel`,
                         **`MahlerBasis`**, `PadicIntegers`, `PadicNorm`, `PadicNumbers`, `PadicVal`,
                         `ProperSpace`, `RingHoms`, `ValuativeRel`, `WithVal` — i.e. the *analytic
                         primitives one layer down* (Mahler's theorem / orthonormal basis of
                         `C(ℤ_p)`, the binomial-ring structure), but **no measure (dual) theory**,
                         no `iota`/`twist`/`baseChange`/`muEtaCleared`.
                       • `MahlerMeasure.lean` exists but is the **height/Mahler-measure of polynomials**
                         (unrelated to the Mahler *transform* of p-adic measures).
                       Mathlib **does** have `LinearMap.mulLeft` (`Algebra/Algebra/Bilinear.lean`) and
                       `DirichletCharacter` / `GaussSum` (`NumberTheory/`), but those are individual
                       primitives — not the composite, and not the measure layer it acts on.
[E] Name pattern       grep for `rhoTheta`/`numerator`/`zetaEta`/`MeasureR`/`twist.*Measure` in mathlib —
                       **no hit**. Nothing named like a χ-twisted, units-pushed p-adic numerator measure.

Searched for both:
  - the user's current form (`ι( x⁻¹·Res_{units}(twist_χ μ̃_η) )` as an `𝒪_K`-valued measure on ℤ_p)
    — **not in mathlib**;
  - the literature/framework form (Iwasawa algebra `Λ(ℤ_p) ≅ 𝒪[[T]]` as the dual of `C(ℤ_p,𝒪)`, with
    the χ-twist / restriction / pushforward operations) — **the *framework* itself is absent from
    mathlib4** (mathlib has Mahler's theorem on `C(ℤ_p)` and the binomial-ring structure on ℤ_p, but
    no p-adic-measure / Iwasawa-algebra-as-measures construction, hence no twist/restriction/
    pushforward of such measures and no `muEtaCleared`).

Concluded: **not in mathlib (all methods exhausted, both the composite form and the framework form).**
Moreover the *building blocks of the composition are themselves project decls* — mathlib provides
nothing closer than the one-layer-down analytic primitives (Mahler basis, ℤ_p binomial ring) plus the
generic `LinearMap.mulLeft`; the entire §3–§6 measure layer (and only then `rhoTheta`) would have to
be built first.

---

### Call sites — `PadicLFunctions.MeasureR.rhoTheta`

Internal use count (within project, **excluding** the declaring file): **K = 0.**
External-to-file callers: **0 distinct files.**

A repo-wide word-boundary grep for `\brhoTheta\b` over `projects/**/*.lean` returns matches **only** in
`projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean` (the declaring file). No other file — in
PadicLFunctions or any sibling project (HasseWeil, Adic spaces, etc.) — references `rhoTheta`. The two
files that `import PadicLFunctions.ValuesAtOne` (`PadicLFunctions.lean` aggregator, `ResidueZeta.lean`)
do **not** use `rhoTheta`.

In-file uses (declaring file `ValuesAtOne.lean`): **38 occurrences** across the §6.2 value computation,
lines 308–1793. The full local API *about* `rhoTheta` also lives entirely in this one file:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none outside `ValuesAtOne.lean`) | — |

In-file consumers (for completeness — all in `ValuesAtOne.lean`):
| `ValuesAtOne.lean:304` | `theorem psi_rhoTheta … : MeasureR.psi p K (rhoTheta …) = 0` (ρ_θ supported on units) |
| `ValuesAtOne.lean:335` | `theorem one_add_mul_derivative_mahlerK_rhoTheta …` (`∂𝓐(ρ_θ) = (1−φψ)F_θ`) |
| `ValuesAtOne.lean:390` | `private theorem zetaEtaCleared_one_eq_rhoTheta_mass …` |
| `ValuesAtOne.lean:767` | `theorem p_mul_constantCoeff_mahlerK_rhoTheta …` (feeds the `(ψF̃_θ)(0)` value) |
| `ValuesAtOne.lean:350,402,…` | `rw […, rhoTheta, iota, pushforward_apply]` — the def is unfolded to its composition |

Inline-derivation grep (was the equivalent re-derived elsewhere without `rhoTheta`?): **none.** No
other file re-derives `ι(twist_χ(μ̃_η) ∘ extendByZero ∘ mulLeft(x⁻¹))`; the composite appears only
inside this file, where it is deliberately named once and unfolded as needed.

What the pattern tells us: **K = 0 external uses, confined to a single declaring file, with its entire
lemma API also confined to that file** → this is an *intra-file naming convenience* for a
construction-internal composite (Phase-6 heuristic: "K = 0 internal-to-other-files / used only in its
own file ⇒ lean NO-composable"). Combined with ONE-LINER-WITHOUT-EXEMPTION (Phase 2b) and COMPOSABLE
(below), every signal points to NO-composable.

---

### Composition check (Phase 6)

Can `PadicLFunctions.MeasureR.rhoTheta` be obtained in ≤3 chained calls? **Yes — it *is* a small
nested composition, by definition.**

**Attempt 1 — the definition itself (one `iota` applied to a `.comp ∘ .comp` of three maps).**
```lean
example {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    rhoTheta p K η hζ hD χ
      = iota p K
          ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp
            ((extendByZero p K).comp
              (LinearMap.mulLeft (integerRing K) (invUnitsCM p K)))) := rfl
```
Decls used (each a function application / `LinearMap.comp`, no intervening reasoning):
`MeasureR.iota`, `MeasureR.twist`, `MeasureR.muEtaCleared`, `DirichletCharacter.toContinuousMapZp`,
`MeasureR.extendByZero`, `LinearMap.mulLeft`, `MeasureR.invUnitsCM`. Per the Phase-6 heuristics table
this is the canonical *composable* pattern (nested single applications, `rfl`-true), **not** a proof
in disguise (no `have`-chains, no `rw`/`ring_nf`/`aesop`). Result: **succeeds** (it is literally the
body). Note this is the χ-twisted analogue of the project's own `zetaEtaCleared` (the `ζ_η` units-level
measure), post-composed with `iota`.

**Caveat that *strengthens* the NO verdict.** Of the seven decls in the composition, **only
`LinearMap.mulLeft` is a mathlib decl**; the other six (`iota`, `twist`, `muEtaCleared`,
`toContinuousMapZp`, `extendByZero`, `invUnitsCM`) and the ambient type `MeasureR` are **project
decls** — mathlib has none of them. So the standard `NO-composable-from-mathlib` reading ("inline a
mathlib composition at the call sites") becomes the even-stronger statement: there is **no mathlib
composition to ship at all**, and no new mathlib lemma is warranted, because the entire substrate
(`MeasureR`/`iota`/`twist`/`muEtaCleared`/`extendByZero`/`invUnitsCM`) is upstream project material
absent from mathlib. `rhoTheta` is a name for a project-internal composite; the actionable mathlib
conclusion is simply *not mathlib-bound*.

Conclusion: **COMPOSABLE** (a small nested composition; six of its seven building blocks are project
primitives, the seventh is a generic mathlib linear map).

---

## Verdict: `PadicLFunctions.MeasureR.rhoTheta`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): identified as RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692 /
  Essential Number Theory 4(1), 2025) §5–§6.2's **χ-twisted, units-pushed numerator measure**
  `ρ_θ = ι(x⁻¹·Res_{ℤ_p^×}(μ_θ))` — a construction-internal step (not a separately-named standard
  object) in the measure-theoretic computation of the value `L_p(θ,1)` (Leopoldt's formula). The
  ambient framework (`Λ(ℤ_p)` = measures = dual of `C(ℤ_p,𝒪)`, Mahler ≅ power series) is classical
  (de Shalit, Williams notes), but it lives one layer down in the *primitives*, and `rhoTheta` is the
  χ-twisted analogue of the project's own `zetaEtaCleared`.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (K = 0 weakenings — all analytic hypotheses
  genuinely used by `MeasureR`/`iota`/`twist`/`muEtaCleared`); modern-idiom **none** — but MAXIMALLY-
  GENERAL here does *not* imply YES, because the object is a thin composition with zero external
  consumers.
- Mathlib search (Phase 5): **not in mathlib**, under both the composite form *and* the framework
  form; mathlib has only the one-layer-down analytic primitives (Mahler basis, ℤ_p binomial ring) and
  the generic `LinearMap.mulLeft`, not the p-adic-measure / Iwasawa-algebra-as-measures layer, hence
  no `iota`/`twist`/`muEtaCleared`/`extendByZero`/`invUnitsCM`. (A Lean-3 formalisation of p-adic
  L-functions existed (Narayanan, arXiv:2302.14491) but never landed in mathlib4.)
- Composition check (Phase 6): **COMPOSABLE** — `rhoTheta` is *by definition* the nested composition
  `iota (twist(χ, μ̃_η) ∘ extendByZero ∘ mulLeft(x⁻¹))`; six of its seven building blocks are project
  decls.

**Rationale.**
`rhoTheta` is a single-substantive-line `noncomputable def` that names the genuine numerator measure
`ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` for the twisted character `θ = χη`: it χ-twists the §5.2 η-measure
`μ̃_η` (`twist χ (muEtaCleared …)`), multiplies by `x⁻¹` and extends by zero off the units
(`extendByZero ∘ mulLeft invUnitsCM` — the §5 `zetaEtaCleared` pattern), and pushes forward from
`ℤ_p^×` to `ℤ_p` (`iota`, RJW Rem 3.33). It is used **only inside its declaring file**
(`ValuesAtOne.lean`, 38×, K = 0 external callers), its entire lemma API (`psi_rhoTheta`,
`one_add_mul_derivative_mahlerK_rhoTheta`, `p_mul_constantCoeff_mahlerK_rhoTheta`,
`zetaEtaCleared_one_eq_rhoTheta_mass`) is in that same file, and the literature confirms it is a *step*
in RJW's §6.2 value computation rather than a separately-named object. Crucially, six of the seven
operations it composes are **project primitives that mathlib does not have** — mathlib's p-adic content
stops at Mahler's theorem on `C(ℤ_p)` and the binomial-ring structure on ℤ_p; there is no
`MeasureR`/`iota`/`twist`/`muEtaCleared` measure theory (the only p-adic-L-function formalisation,
Narayanan's, was Lean-3 and never landed in mathlib4). So the question "should mathlib have `rhoTheta`?"
is moot at this level: one would first have to upstream the entire RJW §3–§6 measure-theoretic layer,
after which `rhoTheta` would *still* be a one-line composition not worth a standalone def. Every signal
— ONE-LINER-WITHOUT-EXEMPTION (Phase 2b), K = 0 external (Phase 6), COMPOSABLE in nested calls (Phase
6), and "construction-internal, unnamed in the source" (Phase 3) — converges on NO-composable, exactly
as for the sibling `rhoA`.

**WHY not (refactor-actionable):**
Mathlib has *no* building blocks for `rhoTheta` except the generic `LinearMap.mulLeft`; `rhoTheta`'s
content is a nested composition of **project** decls. No new lemma — and certainly no standalone mathlib
def — is warranted. The composition is the def body itself.

Mathlib building blocks (only one — the rest are **project** decls, none in mathlib):
- `LinearMap.mulLeft` — `Mathlib/Algebra/Algebra/Bilinear.lean` (the algebra-bilinear left-multiplication
  linear map; the one mathlib primitive used).

Project building blocks (none in mathlib):
- `MeasureR.iota` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/UnitsZp.lean:83`
  (`pushforward K ℤ_[p]ˣ ℤ_[p] (PadicMeasure.unitsValCM p)`, the `ℤ_p^×↪ℤ_p` pushforward, RJW Rem 3.33).
- `MeasureR.twist` — `projects/PadicLFunctions/PadicLFunctions/Interpolation/Twist.lean:38`
  (`cmul p K g μ`, the character-twist `(twist g μ)(f) = μ(g·f)`, RJW eq:twist-by-chi).
- `MeasureR.muEtaCleared` — `projects/PadicLFunctions/PadicLFunctions/Interpolation/NonTame.lean:77`
  (the Gauss-cleared η-measure `μ̃_η`, RJW §5.2).
- `MeasureR.extendByZero` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/UnitsZp.lean:33`
  (extension by zero `C(ℤ_p^×,𝒪_K) → C(ℤ_p,𝒪_K)` off the clopen units).
- `MeasureR.invUnitsCM` — `projects/PadicLFunctions/PadicLFunctions/Interpolation/LpFunction.lean:41`
  (`x ↦ x⁻¹` on `ℤ_p^×`, valued in `𝒪_K`).
- `DirichletCharacter.toContinuousMapZp` — project decl (the χ-extension to `C(ℤ_p,𝒪_K)`); **not** in
  mathlib (grep over mathlib returns nothing).
- ambient type `MeasureR K ℤ_[p] = C(ℤ_p,𝒪_K) →ₗ[𝒪_K] 𝒪_K` —
  `projects/PadicLFunctions/PadicLFunctions/MeasureR/Basic.lean:50`.

(For context — the closest *mathlib* material, one layer below the substrate, is
`Mathlib/NumberTheory/Padics/MahlerBasis.lean` (Mahler's theorem / orthonormal basis of `C(ℤ_p)`) and
the binomial-ring instance on `ℤ_[p]`; plus `Mathlib/NumberTheory/GaussSum.lean` and
`Mathlib/NumberTheory/DirichletCharacter/` for the character/Gauss-sum side. None is a measure
construction.)

Composition sketch (= the def body; `rfl`-true):
```lean
example {D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K}
    (hζ : IsPrimitiveRoot ζ D) (hD : ¬ (p : ℕ) ∣ D) {n : ℕ}
    (χ : DirichletCharacter (integerRing K) (p ^ n)) :
    rhoTheta p K η hζ hD χ
      = iota p K ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp
          ((extendByZero p K).comp (LinearMap.mulLeft (integerRing K) (invUnitsCM p K)))) := rfl
```

Call sites in our project (from Phase 6): **K = 0 external; 38 internal** to `ValuesAtOne.lean`.
Refactor plan: **mathlib action = none — do NOT submit `rhoTheta` to mathlib.** Because it has zero
external consumers and six of its seven building blocks are project-local (`MeasureR`/`iota`/`twist`/
`muEtaCleared`/`extendByZero`/`invUnitsCM`/`toContinuousMapZp`), no cross-file refactor is needed: keep
`rhoTheta` as a project-local `noncomputable def` in `ValuesAtOne.lean`, where it is a legitimate
intra-file naming convenience for the §6.2 `L_p(θ,1)` computation. If one *wanted* to eliminate the
name for hygiene, the 38 in-file uses could be re-expressed as the inline composition
`iota p K ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp ((extendByZero p K).comp (LinearMap.mulLeft (integerRing K) (invUnitsCM p K))))`
(the verb-for-verb body) — but there is no obligation, and the name genuinely aids readability of the
long §6.2 proof (and matches the `ρ_θ` notation of the source). The mathlibability conclusion is simply:
**not mathlib-bound** (composable from project primitives; the underlying measure layer is absent from
mathlib4).

**Note on the rejected alternatives.**
- *Not `BORDERLINE`.* One might ask "is the §6.2 numerator measure a reusable object mathlib should have
  a canonical form for?" — but that is a question about the *primitives* (`MeasureR`/`iota`/`twist`/
  `muEtaCleared`/the whole p-adic-measure layer), not about this composite. `rhoTheta` itself is
  unambiguously a construction-internal composition with zero external use; no human judgment is needed
  to see it should not be a standalone mathlib def. (The genuine upstreaming question — "should mathlib
  gain a p-adic-measure / Iwasawa-algebra-as-measures theory and a p-adic L-function?" — belongs to those
  base decls, if/when they are individually assessed.)
- *Not `YES-add-as-is`* despite Phase 4b = MAXIMALLY GENERAL: maximal generality is necessary but not
  sufficient; the verdicts reference and Phase-6 heuristics are explicit that a MAXIMALLY-GENERAL but
  COMPOSABLE, K = 0-external, one-liner-without-exemption composite is NO-composable, not YES.
- *Not `NO-mathlib-has-it`*: Phase 5 found nothing in mathlib (neither the composite nor the framework),
  so the NO-mathlib-has-it gate (which requires citing an existing mathlib decl) does not apply.

---

## Next step

Keep `PadicLFunctions.MeasureR.rhoTheta` as a project-local `noncomputable def` in `ValuesAtOne.lean`;
**do not open a mathlib PR for it.** It is the nested composition
`iota p K ((twist p K χ.toContinuousMapZp (muEtaCleared p K η hζ hD)).comp ((extendByZero p K).comp (LinearMap.mulLeft (integerRing K) (invUnitsCM p K))))`
— a construction-internal naming convenience (the χ-twisted, units-pushed numerator measure
`ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)`) for the §6.2 Leopoldt-value `L_p(θ,1)` computation, with zero external
call sites and a substrate (`MeasureR`/`iota`/`twist`/`muEtaCleared`/`extendByZero`/`invUnitsCM`/
`toContinuousMapZp`) that is entirely project-local and absent from mathlib4. No mathlib-side refactor
is required; optional in-file hygiene could inline the composition at its 38 uses, but the name aids
readability and there is no mathlib-quality obligation to remove it. (Any future mathlib upstreaming
effort belongs to the underlying p-adic-measure primitives, assessed individually — not to this
composite.)
