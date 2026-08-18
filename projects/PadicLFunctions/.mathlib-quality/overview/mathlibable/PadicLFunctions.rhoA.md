# /mathlibable report — `PadicLFunctions.rhoA`

**Final verdict: `NO-composable-from-mathlib`** (a 3-call composition
`baseChange ∘ iota ∘ zetaNum` of three *project-internal* operations on
project-internal measure types; zero external call sites; the underlying
RJW §3–§4 measure-theoretic layer — `PadicMeasure`, `MeasureR`, `iota`,
`zetaNum`, `baseChange` — does **not** exist in mathlib, so `rhoA` is not a
shippable standalone object and the right action is to keep it project-local).

---

### Baseline (Phase 0)
- lake build:                **build not re-run** (stale/slow per task note) — **reasoned from source**
- decl `PadicLFunctions.rhoA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:651`
- kind:                       `def` (`noncomputable`)
- has sorry:                  no (the body is a single composition; `ResidueZeta.lean` has 0 `sorry`/`admit`)
- module docstring summary:   "The residue of ζ_p at s = 1 (RJW §7, TeX 2181–2360)" — continuity/pole
  of `ζ_{p,i}` at `s=1` and the residue `1 − p⁻¹`, via the §6 c₀-design applied to the explicit
  antiderivative `F̃_a`, run in a field `K ⊇ ℚ_p(μ_p)` (ℂ_p) and descended by injectivity.

---

### Statement (Phase 1)

`PadicLFunctions.rhoA` is **a definition** of the following p-adic measure (an element of the
coefficient-extended Iwasawa algebra).

For a natural number `a` and a coefficient field `K` (a complete ultrametric `ℚ_p`-Banach field,
ℂ_p in the intended application), `rhoA p K a` is the **numerator measure**
`x⁻¹ · Res_{ℤ_p^×}(μ_a)` of RJW Def. 4.10 (`PadicMeasure.zetaNum p a`, a measure on `ℤ_p^×`),
*pushed forward* from `ℤ_p^×` to `ℤ_p` along the inclusion of units (`PadicMeasure.iota`, RJW
Rem. 3.33), and then *base-changed* from the `ℤ_p`-coefficient layer to the `integerRing K`-layer
(`MeasureR.baseChange`, the §5 widening / decomposition W4):

  ρ_a  :=  baseChange_K ( ι ( x⁻¹ · Res_{ℤ_p^×}(μ_a) ) )   ∈  Λ_{𝒪_K}(ℤ_p).

Concretely it lives in `MeasureR K ℤ_[p] = C(ℤ_p, 𝒪_K) →ₗ[𝒪_K] 𝒪_K`, the `𝒪_K`-valued measures
on `ℤ_p`. It is the object whose Mahler transform (`mahlerK p K (rhoA p K a)`) is differentiated
in §7 to extract the constant coefficient `∫ x⁻¹ μ_a = −(1−p⁻¹)·log_p(a)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ` with `[Fact p.Prime]` — the prime.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
  (and `[CharZero K]` in the enclosing `section mass`) — the coefficient field for the §5/§7
  base-change. The four analytic instances are genuinely needed *here* (unlike for `uA`): the
  target type `MeasureR K ℤ_[p]` and `baseChange` both require the complete-ultrametric-Banach
  structure (the Mahler `RingEquiv` underlying `baseChange` only exists over such `K`).
- `a : ℕ` — the index of the measure family `μ_a` (RJW §4; `μ_a` interpolates `(1−a^{...})ζ`).

Hypotheses (Lean side): none on the `def` (it is a plain composition; junk values flow from `a=0`).

Conclusion (math): the §4 numerator measure base-changed to `K` — an element of the
coefficient-extended Iwasawa algebra `Λ_{𝒪_K}(ℤ_p)`.

Conclusion (Lean): `MeasureR K ℤ_[p]` — n/a, it is a definition.

Body (one substantive line):
```lean
noncomputable def rhoA (a : ℕ) : MeasureR K ℤ_[p] :=
  MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a *bookkeeping intermediate* — the base-changed numerator measure, an internal object of
the §7 residue computation. It is not a named theorem, not a new mathematical *structure* (it is an
element of an already-defined type `MeasureR K ℤ_[p]`, not a new type/class), and not a
`## Main results` headline (the headline of the file is the residue/continuity of `zetaPBranch`,
RJW Thm 7.1, not `ρ_a`). The "R7.5a" tag in the docstring marks it as a *step* in the project's
decomposition, not a goal.

(Literature width is EXHAUSTIVE regardless — recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`baseChange p K (iota p (zetaNum p a))`).
One-liner verdict: **ONE-LINER**.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | Downstream proofs (`psi_rhoA`, `one_add_mul_derivative_mahlerK_rhoA`, `constantCoeff_mahlerK_rhoA`) all *unfold* `rhoA` immediately (e.g. line 697 `rw [..., rhoA, ← MeasureR.baseChange_res, ...]`; line 1645 `rw [..., rhoA]`). The def is used as a freely-unfolded abbreviation for the composition, not as a sealed barrier preventing unfolding. |
| Avoid typeclass diamonds          | no       | Returns an inhabitant of the existing type `MeasureR K ℤ_[p]`; introduces no instance and no typeclass-search target. |
| Mark semantic intent / API name   | partial  | It does give the recurring composite measure `ρ_a` a readable name used ~30× *within the file* (lines 696–1645). But — exactly as with the sibling `uA` — the benefit is **intra-file only** (no external consumer; see Phase 6); it does not name an *external* consumer that depends on a stable name. |

Conclusion: **ONE-LINER WITHOUT-EXEMPTION** (the "semantic name" benefit is intra-file readability
only and does not meet the Phase-2b bar of naming an external consumer depending on a stable name).
Phase 7 is therefore biased toward a NO bucket — consistent with the Phase-6 call-sites finding
(K = 0 external) and the Phase-6 composition finding (COMPOSABLE).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic measure numerator x^{-1} restriction units Z_p Iwasawa algebra Kubota-Leopoldt zeta function` | **yes** | The Kubota–Leopoldt p-adic L-function is the unique pseudo-measure ζ_p on ℤ_p^× with `∫ x^k = (1−p^{k−1})ζ(1−k)`; its *numerator* is the `x⁻¹`-twisted restriction of the interpolating measure | Top hits: RJW arXiv:2309.15692; C. Williams' Warwick notes; Coates (Astérisque). The `x⁻¹·Res_{units}` numerator is a construction *internal* to building ζ_p — not a separately-named standalone object. |
| 2 | WebSearch (general form / base change) | `base change p-adic measure Iwasawa algebra coefficient field scalar extension Lambda algebra` | partial | `Λ ⊆ A` coefficient-extension of the Iwasawa algebra; base-changing distributions to a larger ring `A` (e.g. for supersingular/distribution algebras `Λ_∞`) | The *general principle* (base-change Λ(Z) to a larger coefficient ring) is standard; no source names a "ρ_a" object. The §5 widening to `𝒪_K` is the project's own packaging. |
| 3 | WebSearch (named-after / aliases — Mahler transform) | `Mahler transform p-adic measure power series isomorphism Lambda algebra Z_p continuous functions restriction units` | **yes** | Mahler transform = `𝒪_L`-algebra isomorphism `Λ(ℤ_p) ≅ 𝒪_L[[T]]`; `R[ℤ_p]` is the R-linear topological dual of `C(ℤ_p,ℤ_p)` | de Shalit "Mahler bases…" (J. Théor. Nombres Bordeaux); Williams' notes. Confirms the *framework* (`PadicMeasure`/`MeasureR` = dual of `C(ℤ_p,𝒪)`, Mahler ≅ power series) is classical and standard. Restriction-to-units and `x⁻¹`-twist are routine measure operations, unnamed individually. |
| 4 | ChatGPT MCP | (standard-form + historical-evolution prompt) | n/a | — | **ChatGPT MCP server not available/authenticated in this environment** (`~/.claude/mcp-needs-auth-cache.json` present; no ChatGPT tool surfaced). Compensated with extra WebSearch (#1–#3, #5, #9) and the **source paper itself** (#10), the authoritative channel here. |
| 5 | Local references | `grep .mathlib-quality/references/` for "numerator"/"residue"/"base change" | n/a | — | `projects/PadicLFunctions/.mathlib-quality/references/` does not exist; no `refs/` symlink; no `*.tex`/`*.bib`/`*.pdf` in the project. Recorded n/a (same as sibling `uA.md`). |
| 6 | nLab | `Iwasawa algebra p-adic measures continuous functions Z_p completed group ring` | **yes** | Λ(G) = `lim Zp[G/H]`; for `G = ℤ_p`, `Λ(G) ≅ Zp[[T]]`; `R[ℤ_p]` = R-valued measures = R-linear dual of `C(ℤ_p,ℤ_p)`; continuous `φ : Z → R` extends to `Λ → R` ("integrate against a measure") | Wikipedia "Iwasawa algebra" + Cambridge (S. Wadsley) lecture notes confirm the abstract statement: **the measure framework `rhoA` lives in is exactly Λ(ℤ_p) ⊗ coefficients**, classical and standard. No nLab/encyclopedia entry for a "numerator measure ρ_a". |
| 7 | nCatLab (categorical) | — | n/a | — | Not a categorical concept (a concrete element of a concrete dual module); no higher-categorical statement applies. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry concept; Stacks has no "p-adic numerator measure". |
| 9 | MathOverflow / Math.SE | (folded into #1–#3, #6 — Iwasawa-algebra / p-adic-measure threads) | partial | Same as #1/#6: `R[[T]]`-as-measures and `x⁻¹·Res_{units}` are routine in Iwasawa-theory discussion | No dedicated treatment of a named "ρ_a"; it is construction-internal. |
| 10 | **Source paper (arXiv)** | identify "RJW"; locate the §4 numerator + §7 residue | **yes** | **RJW = Rodrigues Jacinto–Williams, "An introduction to p-adic L-functions", arXiv:2309.15692** (also Essential Number Theory 4(1), 2025). §4 builds the numerator `x⁻¹·Res_{ℤ_p^×}(μ_a)` of the p-adic zeta function (the project cites it as RJW Def. 4.10, TeX 1561); §7 (Thm 7.1) computes the residue at `s=1` as `1−p⁻¹`. | **Decisive.** The abstract (fetched) confirms the three constructions of ζ_p (measure-theoretic / Coleman / Iwasawa). `μ_a`, its `x⁻¹·Res_{units}` numerator, and `ι` are *steps* in RJW's measure-theoretic construction; the base-change to `K ⊇ ℚ_p(μ_p)` is the project's own §5 widening + §7 descent device. No standalone named "ρ_a" in the source. |

### Literature summary (Phase 3)

Concept identified as: the **base-changed numerator measure** `ρ_a = baseChange_K( ι( x⁻¹·Res_{ℤ_p^×}(μ_a) ) )`,
an internal object of **RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692) §4/§7**'s
measure-theoretic construction of the Kubota–Leopoldt p-adic zeta function and its residue at
`s=1`. It is assembled from three standard *operations* on p-adic measures: the `x⁻¹`-twist and
restriction-to-units (`zetaNum`, RJW Def. 4.10), the units→`ℤ_p` pushforward (`iota`, RJW
Rem. 3.33), and the coefficient base-change `Λ(ℤ_p) → Λ_{𝒪_K}(ℤ_p)` (the §5 widening / Mahler-
coefficient scalar extension, decomposition W4).

Sources agree on the standard form: **yes** for the ambient *framework* — Λ(ℤ_p) ≅ `𝒪[[T]]` =
`𝒪`-valued measures = `𝒪`-linear dual of `C(ℤ_p,𝒪)` (Mahler), with base-change to a larger
coefficient ring a routine move (Iwasawa-theory standard). **But** the composite `ρ_a` itself is
**not a separately-named object** in any source — it is bookkeeping inside one proof (the §7
residue computation).

Most general standard form: there is no "more general ρ_a" in the literature to aim at — the
generality lives in the *primitives* (measures on a profinite group `Z` valued in any p-adic
coefficient ring `A`, with base-change `Λ(Z) → A`-extensions), all of which are upstream of this
particular composite.

Generality dimensions where the literature varies:
  - profinite base group: `ℤ_p` here; the framework allows any profinite `Z` (e.g. `ℤ_p^×`, `ℤ_p^n`).
  - coefficient ring: `𝒪_K` for `K` a complete ultrametric `ℚ_p`-Banach field here; the framework
    allows any p-adic coefficient ring `A ⊇ ℤ_p` (incl. distribution algebras `Λ_∞`).
  - These are dimensions of the *primitives* (`PadicMeasure`/`MeasureR`/`baseChange`), not of `rhoA`.

Disagreement with the literature: none — the literature simply does not isolate `ρ_a` as an object;
it is a step. (Treating "the source doesn't name it" as a signal: this is a construction-internal
composite, not a standalone contribution — see Phase 7.)

---

### Generality analysis — `PadicLFunctions.rhoA`

Literature-standard form (Phase 3): there is no separately-named standard `ρ_a`. The relevant
generality lives entirely in the *primitives* (`zetaNum`/`iota`/`baseChange`), which are themselves
project decls, not in this composite. So the "compare to the literature-standard form" exercise
reduces to: *is each input operation applied at the right generality, and is the composite the
right thing to name?*

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedField K]` | normed field | (coefficient field of the Banach/Iwasawa-algebra base-change) | **NO** | Genuinely used: `MeasureR K ℤ_[p]` and `MeasureR.baseChange` both require the field/Banach structure; the Mahler `RingEquiv` defining `baseChange` only exists over such `K`. (Contrast `uA`, where these were dead weight on a coefficient formula.) |
| 2 | `[NormedAlgebra ℚ_[p] K]` | `ℚ_p`-Banach algebra | needed for `baseChange` (the algebra map `ℤ_[p] → 𝒪_K`) | **NO** | `baseChange` is literally built from `algebraMap ℤ_[p] (integerRing K)` under Mahler; the `ℚ_p`-algebra structure is essential. |
| 3 | `[IsUltrametricDist K]` | ultrametric | needed (`integerRing K` = unit ball; nonarch. integrality) | **NO** | The whole `MeasureR`/`integerRing K` layer (`𝒪_K`-valued measures, automatic boundedness) is nonarchimedean by construction. |
| 4 | `[CompleteSpace K]` | complete | needed (Mahler `RingEquiv` ≅ power series requires completeness) | **NO** | Completeness is used to identify `MeasureR K ℤ_[p]` with `𝒪_K[[T]]` via Mahler, which `baseChange` relies on. |
| 5 | `a : ℕ` | natural index | the index of the measure family `μ_a` (RJW §4) | **NO** | `μ_a`/`zetaNum`/`muAUnits` are indexed by `a : ℕ` throughout the project's §4 layer; this is the natural index, not an over-specialisation. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for what it is — a composite of fixed project
primitives over the natural coefficient field). Unlike the sibling `uA` (which carried four
dead-weight analytic instances on a pure coefficient formula), **every** hypothesis on `rhoA` is
genuinely used by `MeasureR.baseChange`/`MeasureR K ℤ_[p]`. There are **no weakening opportunities**
internal to `rhoA`.
Number of weakening opportunities found: **K = 0.**
Proposed restatement: none (no weaker form makes sense for this composite).
Cost of restatement: n/a.

**Important caveat (drives the verdict away from YES).** "MAXIMALLY GENERAL" here is *not* an
argument for `YES-add-as-is`. The generality is fine, but the object is a **thin composition of
three project-local operations on project-local types** with **zero external consumers** (Phase 6).
MAXIMALLY-GENERAL + COMPOSABLE + K=0-external → NO-composable, not YES (cf. Phase 6 heuristics and
the verdicts reference: "K = 1/0 internal-only use ⇒ lean NO-composable").

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" → typeclasses? | no | already fully typeclass-based (`[NormedField K]` …) | — |
| 2 | sequences/metric → filters/topology? | no | it is an algebraic element of a dual module; no sequential/metric limit in the def | — |
| 3 | construct object → universal-property class? | no | it is an explicit composite of three maps, not a universal object | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure | — |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | no | the field/Banach hypotheses are genuinely required by `baseChange` (Phase 4b rows 1–4); nothing to weaken | — |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index → arbitrary monoid/group? | no | `a : ℕ` is the natural index of the `μ_a` family; not a generalisation axis (the family itself is `ℕ`-indexed in the source) | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** `rhoA` is already a contemporary, typeclass-based composite at the
right generality. There is no "let's filter-ise / categorify / weaken-typeclass" move that improves
it — and crucially, the only modernisation that *would* matter (formalising the whole RJW §3–§4
p-adic-measure layer idiomatically) is upstream of `rhoA` and is precisely the work the project is
doing, not a property of this one-line composite. One-line reason: this is a construction-internal
composition of already-idiomatic project primitives; there is nothing to modernise about the
composition itself.

---

### Diamond / defeq risk — `PadicLFunctions.rhoA`

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | none | Produces an inhabitant of the existing type `MeasureR K ℤ_[p]` (an `abbrev` for a `LinearMap`); introduces no instance, so nothing new for typeclass search to disambiguate. |
| 2 | Reducibility leak | none | Plain `noncomputable def`, not `@[reducible]`/`abbrev`; the body (`baseChange ∘ iota ∘ zetaNum`) is exposed only via explicit `rw [rhoA]` (e.g. lines 697, 1645). |
| 3 | Non-canonical unfolding | low | No `@[simp]`; `simp` will not unfold it; proofs unfold deliberately. No surprise. |
| 4 | Instance priority collision | none | Not an `instance`. |
| 5 | Universe-polymorphism issues | none | `K : Type*`, `ℤ_[p] : Type`; `MeasureR K ℤ_[p]` is monomorphic in the relevant universes; no forced annotation. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort` introduced (it is a `def`, not a coercion); `MeasureR` already carries the `LinearMap` `FunLike`, unchanged here. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE**
Top risks: none.
Recommended mitigations: none required. (Risk is irrelevant to the final NO verdict anyway — NO
buckets do not add the def to mathlib.)

---

### Mathlib search-status: `PadicLFunctions.rhoA`

[A] Lean-Finder        n/a: LSP/MCP Lean-Finder not available in this environment (recorded n/a per
                       `mathlib-search.md`); compensated by [D] grep over mathlib source + [B-as-grep].
[B] Loogle             type-pattern `(C(ℤ_[p], _) →ₗ[_] _)` arising from a `baseChange`/pushforward of a
                       units-measure — n/a (LSP unavailable); emulated via source grep [D]. **No hit**:
                       mathlib has no "measure = `𝒪`-linear functional on `C(ℤ_p,𝒪)`" construction at all.
[C] LeanSearch         "p-adic measure numerator x⁻¹ restriction to units base changed to coefficient
                       field" — n/a (LSP unavailable); covered by WebSearch #1/#3/#6 (literature) + [D].
[D] Grep mathlib src   Over `.lake/packages/mathlib/Mathlib/`:
                       • `PadicMeasure` / `Iwasawa.*measure` / `p-adic measure` → **no hit** (`Iwasawa.lean`
                         is *group-action* Iwasawa decomposition, unrelated; no measure-on-ℤ_p layer).
                       • `def baseChange`/`scalarExtension`/`extendScalars` *of a measure or functional* →
                         **no hit** (`extendScalars` exists only for field-extension `rank`/`relrank`).
                       • `WeakDual`/`C(_, _) →ₗ[_] _` measure → only `WeakDual.characterSpace` (Gelfand
                         duality, complex/normed-algebra) — **not** the p-adic-measure dual; no base-change.
                       • `zetaNum`/`MeasureR`/`iota` (units→ℤ_p pushforward of a measure) → **no hit**.
                       Mathlib *does* have the analytic primitives one layer down — `ℤ_[p]` as a binomial
                       ring + `Mathlib/NumberTheory/Padics/MahlerBasis.lean` (Mahler's theorem / orthonormal
                       basis of `C(ℤ_p)`) — but **not** the measure (dual) theory, nor `baseChange`, nor
                       `zetaNum`, nor `iota`.
[E] Name pattern       grep for `rhoA`/`numerator`/`zetaNum`/`MeasureR`/`baseChange.*Measure` in mathlib —
                       **no hit**. Nothing named like a base-changed p-adic numerator measure.

Searched for both:
  - the user's current form (`baseChange_K(ι(x⁻¹·Res_{units}(μ_a)))` as an `𝒪_K`-valued measure on ℤ_p)
    — **not in mathlib**;
  - the literature/framework form (Iwasawa algebra Λ(ℤ_p) ≅ `𝒪[[T]]` as the dual of `C(ℤ_p,𝒪)`, with
    coefficient base-change) — **the *framework* itself is absent from mathlib** (mathlib has Mahler's
    theorem on `C(ℤ_p)` and the binomial-ring structure on ℤ_p, but no p-adic measure / Iwasawa-algebra-
    as-measures construction, and hence no base-change of such measures).

Concluded: **not in mathlib (all methods exhausted, both the composite form and the framework form).**
Moreover the *building blocks of the composition are themselves project decls, not mathlib decls* —
mathlib provides nothing closer than the one-layer-down analytic primitives (Mahler basis, ℤ_p
binomial ring), from which the entire §3–§4 measure layer (and only then `rhoA`) would have to be built.

---

### Call sites — `PadicLFunctions.rhoA`

Internal use count (within project, **excluding** the declaring file): **K = 0.**
External-to-file callers: **0 distinct files.**

A repo-wide word-boundary grep for `\brhoA\b` over `projects/**/*.lean` returns matches **only** in
`projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean` (the declaring file). No other file —
in PadicLFunctions or any sibling project (HasseWeil, etc.) — references `rhoA`.

In-file uses (declaring file `ResidueZeta.lean`): ~30 occurrences across the §7 residue computation,
lines 696–1645. The full local API *about* `rhoA` also lives entirely in this one file:

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none outside `ResidueZeta.lean`) | — |

In-file consumers (for completeness — all in `ResidueZeta.lean`):
| `ResidueZeta.lean:696` | `theorem psi_rhoA … : MeasureR.psi p K (rhoA p K a) = 0` (ρ_a supported on units) |
| `ResidueZeta.lean:703` | `theorem one_add_mul_derivative_mahlerK_rhoA …` (∂𝓐(ρ_a) = 𝓐(Res_units μ_a)) |
| `ResidueZeta.lean:913` | `theorem p_mul_constantCoeff_mahlerK_rhoA …` |
| `ResidueZeta.lean:1587` | `theorem constantCoeff_mahlerK_rhoA …` (the `∫x⁻¹μ_a = −(1−p⁻¹)log_p a` payoff) |
| `ResidueZeta.lean:1640` | `private theorem constantCoeff_mahlerK_rhoA_eq_algebraMap …` |
| `ResidueZeta.lean:697,716,…,1645` | `rw [..., rhoA, ...]` — the def is unfolded to its composition |

Inline-derivation grep (was the equivalent re-derived elsewhere without `rhoA`?): **none.** No other
file re-derives `baseChange(ι(zetaNum …))`; the composite appears only inside this file, where it is
deliberately named once and unfolded as needed.

What the pattern tells us: **K = 0 external uses, confined to a single declaring file, with its
entire lemma API also confined to that file** → this is an *intra-file naming convenience* for a
construction-internal composite (Phase-6 heuristic: "K = 0 internal-to-other-files / used only in its
own file ⇒ lean NO-composable"). Combined with ONE-LINER-WITHOUT-EXEMPTION (Phase 2b) and COMPOSABLE
(below), every signal points to NO-composable.

---

### Composition check (Phase 6)

Can `PadicLFunctions.rhoA` be obtained in ≤3 chained calls? **Yes — it *is* a 3-call composition,
by definition.**

**Attempt 1 — the definition itself (3 single-call applications).**
```lean
example (a : ℕ) :
    rhoA p K a = MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a)) := rfl
```
Decls used (each a single function application, no intervening reasoning):
`PadicMeasure.zetaNum` → `PadicMeasure.iota` → `MeasureR.baseChange`.
Per the Phase-6 heuristics table this is the canonical *composable* pattern
(`Foo.bar (Bar.baz (Quux.zog x))` — three nested single calls, `rfl`-true), **not** a proof in
disguise (no `have`-chains, no `rw`/`ring_nf`/`aesop`). Result: **succeeds** (it is literally the body).

**Caveat that *strengthens* the NO verdict.** The three building blocks
(`zetaNum`, `iota`, `baseChange`) are **project decls, not mathlib decls** — mathlib has none of
them. So the standard `NO-composable-from-mathlib` reading ("inline a mathlib composition at the call
sites") becomes the even-stronger statement: there is **no mathlib composition to ship at all**, and
no new mathlib lemma is warranted, because the entire substrate (`PadicMeasure`/`MeasureR`/`iota`/
`zetaNum`/`baseChange`) is upstream project material that is not in mathlib. `rhoA` is a name for a
project-internal composite; the actionable mathlib conclusion is simply *not mathlib-bound*.

Conclusion: **COMPOSABLE** (a 3-call nested composition; the building blocks are project primitives).

---

## Verdict: `PadicLFunctions.rhoA`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): identified as RJW (Rodrigues Jacinto–Williams, arXiv:2309.15692)
  §4/§7's **base-changed numerator measure** `ρ_a = baseChange_K(ι(x⁻¹·Res_{ℤ_p^×}(μ_a)))` — a
  construction-internal step (not a separately-named standard object) in the measure-theoretic build
  of the Kubota–Leopoldt p-adic zeta function and its `s=1` residue. The ambient framework (Λ(ℤ_p) =
  measures = dual of `C(ℤ_p,𝒪)`, Mahler ≅ power series, coefficient base-change) is classical, but it
  lives one layer down in the *primitives*.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** (K = 0 weakenings — all hypotheses genuinely
  used by `baseChange`); modern-idiom **none** — but MAXIMALLY-GENERAL here does *not* imply YES,
  because the object is a thin composition with zero external consumers.
- Mathlib search (Phase 5): **not in mathlib**, under both the composite form *and* the framework form;
  mathlib has only the one-layer-down analytic primitives (Mahler basis, ℤ_p binomial ring), not the
  p-adic-measure / Iwasawa-algebra-as-measures layer, hence no `baseChange`/`iota`/`zetaNum`.
- Composition check (Phase 6): **COMPOSABLE** — `rhoA` is *by definition* the 3-call nested
  composition `baseChange (iota (zetaNum a))`; the building blocks are project decls.

**Rationale.**
`rhoA` is a one-line `noncomputable def` that names the composite `baseChange ∘ iota ∘ zetaNum`: the
§4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)` (RJW Def. 4.10), pushed from `ℤ_p^×` to `ℤ_p` (RJW
Rem. 3.33), and base-changed to the coefficient field `K` (the project's §5 widening). It is used
**only inside its declaring file** (`ResidueZeta.lean`, ~30×, K = 0 external callers), its entire
lemma API (`psi_rhoA`, `one_add_mul_derivative_mahlerK_rhoA`, `constantCoeff_mahlerK_rhoA`, …) is in
that same file, and the literature confirms it is a *step* in RJW's construction rather than a
separately-named object. Crucially, the three operations it composes are **project primitives that
mathlib does not have** — mathlib's p-adic content stops at Mahler's theorem on `C(ℤ_p)` and the
binomial-ring structure on ℤ_p; there is no `PadicMeasure`/`MeasureR` dual theory, no `iota`, no
`zetaNum`, no `baseChange`. So the question "should mathlib have `rhoA`?" is moot at this level: one
would first have to upstream the entire RJW §3–§5 measure-theoretic layer, after which `rhoA` would
*still* be a 3-line composition not worth a standalone def. Every signal — ONE-LINER-WITHOUT-EXEMPTION
(Phase 2b), K = 0 external (Phase 6), COMPOSABLE in 3 nested calls (Phase 6), and "construction-
internal, unnamed in the source" (Phase 3) — converges on NO-composable.

**WHY not (refactor-actionable):**
Mathlib has *no* building blocks for `rhoA` (the substrate is project-only); `rhoA`'s content is a
3-call composition of **project** decls. No new lemma — and certainly no standalone mathlib def — is
warranted. The composition is the def body itself.

Building blocks (all **project** decls — none in mathlib):
- `PadicMeasure.zetaNum` — `projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/ZetaP.lean:74`
  (`unitsCmul p (invCM p) (muAUnits p a)`, the `x⁻¹·Res_{units}` numerator, RJW Def. 4.10).
- `PadicMeasure.iota` — `projects/PadicLFunctions/PadicLFunctions/Measure/UnitsZp.lean:121`
  (`pushforward p (unitsValCM p)`, the `ℤ_p^×↪ℤ_p` pushforward, RJW Rem. 3.33).
- `MeasureR.baseChange` — `projects/PadicLFunctions/PadicLFunctions/MeasureR/BaseChange.lean:39`
  (the Mahler-coefficient scalar extension `Λ(ℤ_p) → Λ_{𝒪_K}(ℤ_p)`, decomposition W4).

(For context — the closest *mathlib* material, one layer below the substrate, is
`Mathlib/NumberTheory/Padics/MahlerBasis.lean` (Mahler's theorem / orthonormal basis of `C(ℤ_p)`) and
the binomial-ring instance on `ℤ_[p]` — neither is a measure construction.)

Composition sketch (= the def body; `rfl`-true):
```lean
example (a : ℕ) :
    rhoA p K a = MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a)) := rfl
```

Call sites in our project (from Phase 6): **K = 0 external; ~30 internal** to `ResidueZeta.lean`.
Refactor plan: **mathlib action = none — do NOT submit `rhoA` to mathlib.** Because it has zero
external consumers and its building blocks are all project-local, no cross-file refactor is needed:
keep `rhoA` as a project-local `noncomputable def` in `ResidueZeta.lean`, where it is a legitimate
intra-file naming convenience for the §7 residue computation. If one *wanted* to eliminate the name
for hygiene, the ~30 in-file uses could be re-expressed as the inline composition
`MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))` (the verb-for-verb body) —
but there is no obligation, and the name genuinely aids readability of the long §7 proof. The
mathlibability conclusion is simply: **not mathlib-bound** (composable from project primitives;
underlying measure layer absent from mathlib).

**Note on the rejected alternatives.**
- *Not `BORDERLINE`.* One might ask "is the §4 numerator measure a reusable object mathlib should
  have a canonical form for?" — but that is a question about the *primitives* (`zetaNum`/`iota`/
  `baseChange`/the whole `PadicMeasure` layer), not about this 3-call composite. `rhoA` itself is
  unambiguously a construction-internal composition with zero external use; no human judgment is
  needed to see it should not be a standalone mathlib def. (The genuine upstreaming question — "should
  mathlib gain a p-adic-measure / Iwasawa-algebra-as-measures theory?" — belongs to those base decls,
  if/when they are individually assessed.)
- *Not `YES-add-as-is`* despite Phase 4b = MAXIMALLY GENERAL: maximal generality is necessary but not
  sufficient; the verdicts reference and Phase-6 heuristics are explicit that a MAXIMALLY-GENERAL but
  COMPOSABLE, K = 0-external, one-liner-without-exemption composite is NO-composable, not YES.
- *Not `NO-mathlib-has-it`*: Phase 5 found nothing in mathlib (neither the composite nor the
  framework), so the NO-mathlib-has-it gate (which requires citing an existing mathlib decl) does not
  apply.

---

## Next step

Keep `PadicLFunctions.rhoA` as a project-local `noncomputable def` in `ResidueZeta.lean`; **do not
open a mathlib PR for it.** It is the 3-call composition `MeasureR.baseChange p K (PadicMeasure.iota
p (PadicMeasure.zetaNum p a))` — a construction-internal naming convenience for the §7 residue
computation, with zero external call sites and a substrate (`PadicMeasure`/`MeasureR`/`iota`/
`zetaNum`/`baseChange`) that is entirely project-local and absent from mathlib. No mathlib-side
refactor is required; optional in-file hygiene could inline the composition at its ~30 uses, but the
name aids readability and there is no mathlib-quality obligation to remove it. (Any future mathlib
upstreaming effort belongs to the underlying p-adic-measure primitives, assessed individually — not
to this composite.)
