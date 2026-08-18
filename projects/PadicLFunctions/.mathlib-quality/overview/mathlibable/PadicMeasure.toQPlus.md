# /mathlibable report — `PadicMeasure.toQPlus`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicMeasure.toQPlus`
**Kind:** `def` (noncomputable section)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:129`
**Date:** 2026-06-20

---

## FINAL VERDICT: `NO-mathlib-has-it`

> `toQPlus` is the canonical structure map `Λ(𝒢⁺) → Q(𝒢⁺)`, and its body is literally `algebraMap _ _`. Mathlib already has this map *by name*: it is `algebraMap R (FractionRing R)` (the `Algebra` class structure map, `Mathlib/Algebra/Algebra/Defs.lean`; the `Algebra (PadicMeasure p (GPlus p)) (FractionRing …)` instance comes from `Mathlib/RingTheory/Localization/FractionRing.lean`). The derivation is `rfl`. Mathlib never introduces a separate `def` for `R →+* FractionRing R` — it writes `algebraMap _ _` inline — and the literature never names this map beyond "the natural/canonical map". The named wrapper here exists only to dodge a project-local Lean elaboration-order metavariable over the quotient group; that is a local elaboration convenience, not mathlib content.

---

## Phase 0 — Doctor / baseline

```
### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (task instruction — worktree build stale/slow; skill Phase-0 fallback permits reading the decl + deps directly)
- decl `PadicMeasure.toQPlus`: ✓ resolved at projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:129
- kind:                      def
- has sorry:                 no
- module docstring summary:  ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p (RJW arXiv:2309.15692 §11.1–11.2, identified-Galois side)
```

The declaration is sorry-free. It references only existing compiling definitions: `PadicMeasure` (`Measure/Basic.lean:52`), `GPlus` (`Iwasawa/PlusPart.lean:215`), `QuotientFieldPlus` (`ZetaGalois.lean:124`), and mathlib's `algebraMap`. Its 10 in-file call sites are in the same compiling tree, and the analogous sibling pattern (`QuotientField` + raw `algebraMap`) compiles in `Measure/PseudoMeasure.lean`.

## Phase 1 — Comprehend

```lean
/-- The structure map `Λ(𝒢⁺) → Q(𝒢⁺)`, named once (the raw `algebraMap` keeps an
unresolved instance metavariable inside `def`-bodies over the quotient group — a
known elaboration-order trap; naming it sidesteps the postponement). -/
def toQPlus : PadicMeasure p (GPlus p) →+* QuotientFieldPlus p :=
  algebraMap _ _
```

with `variable (p : ℕ) [hp : Fact p.Prime]`.

### Statement (Phase 1)

`PadicMeasure.toQPlus` is **a definition** of the following:

The canonical (structure) ring homomorphism from the Iwasawa algebra `Λ(𝒢⁺) = PadicMeasure p (GPlus p)` into its total ring of fractions `Q(𝒢⁺) = FractionRing (Λ(𝒢⁺))`. Mathematically it is the inclusion `a ↦ a/1` that exhibits `Q(𝒢⁺)` as the localization of `Λ(𝒢⁺)` at its non-zero-divisors. It is the map in which pseudo-measures (and the descended `ζ_p⁺`) live, and along which "regular elements become units".

**Dependency unfolding:**
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — the `ℤ_[p]`-valued measures on `X`.
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)` (`Iwasawa/PlusPart.lean:215`) — the plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}`.
- `PadicMeasure p (GPlus p)` carries the convolution `CommRing` structure (`instance : CommRing (PadicMeasure p G)` for compact commutative topological monoid `G`, `Measure/PseudoMeasure.lean:81`) — the Iwasawa algebra `Λ(𝒢⁺)`.
- `QuotientFieldPlus p := FractionRing (PadicMeasure p (GPlus p))` (`ZetaGalois.lean:124`) — the total ring of fractions `Q(𝒢⁺)`.
- `algebraMap R A : R →+* A` (`Mathlib/Algebra/Algebra/Defs.lean:29,97`) — "the canonical map from `R` to `A`, as a `RingHom`", i.e. the `Algebra` class's structure map. For `A = FractionRing R` it is the localization unit `a ↦ a/1`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — fixes the prime; threads through `ℤ_[p]`, `GPlus p`, `PadicMeasure`.

Conclusion (math): the localization structure map `Λ(𝒢⁺) → Q(𝒢⁺)`, `a ↦ a/1`.
Conclusion (Lean): `PadicMeasure p (GPlus p) →+* QuotientFieldPlus p` — definition (body `algebraMap _ _`).

This is the **exact `𝒢⁺` analogue** of the non-plus side, where the project uses the raw `algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)` directly (35 sites in `PseudoMeasure.lean`) with **no** named wrapper — the only difference is the named anchor here.

## Phase 2 — Preliminary checks (size + one-line)

### Size classification (Phase 2a)

```
Verdict: SMALL
Reason: A one-line `def` whose body is a single application of mathlib's `algebraMap`. It introduces no new mathematical structure (no topology/category/measurability notion — it picks out a map that already exists from the existing `Algebra` instance), is not a named/personal theorem, and is not a primary goal in the module docstring's "Main declarations" list (those are `padicZetaPlus`, `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdeal`/`zetaIdealPlus`).
(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)
```

### One-line check (Phase 2b)

```
Body line count: 1 substantive line (`algebraMap _ _`)
One-liner verdict: ONE-LINER
```

Exemption check (each row required):

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | **no**   | The opposite holds. The def is *not* sealed as a barrier — `zetaIdealPlus_eq_span` uses `change toQPlus p x = …` (`ZetaGalois.lean:370`) and `padicZetaPlus_spec`-style proofs use `rw […, toQPlus, …]` (`ZetaGalois.lean:232`) to **unfold `toQPlus` back to `algebraMap`** so mathlib's `IsFractionRing.injective` / `IsLocalization.mk'_spec` / `IsLocalization.map_units` apply. Consumers rely on it *being* `algebraMap` definitionally, so it is not protecting any spelling. |
| Avoid typeclass diamonds          | **no**   | The def registers **no instance** and selects no instance path; the `Algebra (PadicMeasure p (GPlus p)) (FractionRing …)` instance is mathlib's and is the same whether reached through `toQPlus` or `algebraMap _ _`. No two `Mul`/`Zero`/`AddCommMonoid` paths collide. |
| Mark semantic intent / API name   | **partial / weak — local elaboration convenience** | The docstring's stated reason is purely operational: "the raw `algebraMap` keeps an unresolved instance metavariable inside `def`-bodies over the quotient group — a known elaboration-order trap; naming it sidesteps the postponement." This is a **Lean elaboration-order workaround specific to `GPlus`**, not a stable cross-library API surface. Decisive counter-evidence: (a) the non-plus side `QuotientField` uses raw `algebraMap` at all 35 sites with no wrapper; (b) even `padicZetaPlus` — itself a `def` over `GPlus` — uses raw `algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p)` (`ZetaGalois.lean:229`). So the anchor is not a project-wide API contract; it is a local typing aid. |

```
Conclusion: ONE-LINER WITH-EXEMPTION (weak / project-local only) — the only exemption that even partially applies is "semantic intent / API name", and that is justified solely by a GPlus-specific Lean elaboration quirk, not by a mathlib-relevant API need. For mathlib purposes this is effectively ONE-LINER WITHOUT-EXEMPTION: mathlib does not carry per-instance elaboration-workaround wrappers; it writes `algebraMap _ _`.
```

Carried into Phase 7: the one-liner-without-(mathlib-relevant)-exemption signal biases the verdict toward NO. A YES would require a mathlib gap the named anchor fills — none exists (Phase 5: mathlib has the map by name).

## Phase 3 — Literature search (EXHAUSTIVE, 9 channels)

The concept: **the canonical / structure ring homomorphism `R → Q(R) = Frac(R)`** (and its Iwasawa instance `Λ(G) → Q(G)`).

```
### Literature search table — EXHAUSTIVE protocol
```

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "canonical ring homomorphism R to total ring of fractions Frac(R) structure map localization" | **yes** | `φ : A → S⁻¹A`, `φ(a) = a/1`; "the canonical mapping from R to S⁻¹R"; injective when `S` has no zero-divisors | Wikipedia *Total ring of fractions*, HandWiki, MDPI *Localization (Algebra)*, GSU lecture notes. The map is universally called the *canonical/natural homomorphism*; no dedicated name/symbol. |
| 2 | WebSearch (general / Iwasawa form) | "Iwasawa algebra Lambda(G) map to fraction ring Q(G) pseudo-measure Serre Coates structure homomorphism" | **yes** | `Λ(G) ↪ Q(G) = Frac Λ(G)`; pseudo-measures are elements of `Q(G)` with `(σ−1)φ ∈ Λ(G)`; the map is the inclusion / Mellin-transform extension | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Coates Astérisque (Numdam); Wikipedia *Iwasawa algebra*. "Pseudomeasures were introduced by Coates as elements of the fraction field of the Iwasawa algebra." |
| 3 | WebSearch (named-after / aliases) | "structure map" / "natural homomorphism" `R → S⁻¹R` canonical morphism universal property (via nLab query) | **yes** | "the canonical morphism `R → S⁻¹R` is the structure map for the R-algebra structure on `S⁻¹R`" and the initial object among R-algebras inverting `S` | nLab *localization of a commutative ring*; *Canonical map* (Wikipedia). Confirms the map = R-algebra structure map = `algebraMap` in mathlib terms; no special name. |
| 4 | ChatGPT MCP | "standard name + generality + historical evolution of the canonical map `R → Frac(R)` / `Λ(G) → Q(G)`" | **n/a** | — | Codex / ChatGPT MCP not installed in this environment (no `codex`, no `.mcp.json` — matches the sibling `QuotientFieldPlus` report's finding). Channels 1–3 + 5 + 7 already settle the question: Serre (1978) introduced pseudo-measures in `Q(G)=Frac Λ(G)` via this inclusion; the formulation has been standard since. |
| 5 | Local references (`refs/PadicLFunctions/`, `.mathlib-quality/references/`) | grep for the structure map | **n/a** | — | Neither `refs/` (local-only PDFs, not symlinked in this worktree) nor `.mathlib-quality/references/` exists. The in-file docstrings cite **RJW Def. 3.34** ("let `Q(G)` denote the ring of fractions") and **§11.1/§11.2, TeX 3033–3059**; RJW's own term for the codomain is "the ring of fractions of `Λ(G)`", and the map is the inclusion into it. |
| 6 | nLab | "localization of a commutative ring", "structure map" | **yes** | "the structure morphism `φ : A → S⁻¹A` makes `S⁻¹A` an A-algebra"; universal/initial-object characterisation | ncatlab.org/nlab/show/localization+of+a+commutative+ring. The map is the R-algebra structure map — exactly mathlib's `algebraMap`. |
| 7 | nCatLab (categorical) | localization universal property; structure map as unit of the localization | **yes** | The map is the *unit/component* of the localization (initial object among R-algebras inverting `S`) | Same nLab source + *categorical universal properties of quotients and localizations* (arXiv:2003.05806). Categorically it is the canonical unit; still unnamed beyond "canonical". |
| 8 | Stacks Project (alg geom) | total quotient ring `Q(A) = S⁻¹A`, the natural map (tag 02C5 region, cf. sibling report) | **yes** | `Q(A) = S⁻¹A` with `S` = non-zero-divisors; the natural map `A → Q(A)` | Stacks tag 02C5 (Example 10.9.8) defines `Q(A)`; the structure map `A → Q(A)` is the canonical localization map, not separately named. |
| 9 | MathOverflow / Math.StackExchange | (covered by 1–8) | **n/a** | — | The canonical map `R → Frac(R)` is uncontested textbook material; no open MO/MSE question to resolve. |
| 10 | recent arXiv (last 5 years) | pseudomeasures / Iwasawa fraction ring inclusion `Λ(G) → Q(G)` | **yes** | `Λ(G) ↪ Q(G)`; characteristic-element/localization framework of the (equivariant) Main Conjecture | Coates–Sujatha; Ardakov–Brown *Ring-theoretic properties of Iwasawa algebras*; arXiv:1004.2578 (equivariant Iwasawa). The map is standard and unnamed beyond "canonical/natural". |

```
### Literature summary (Phase 3)

Concept identified as: the canonical / natural / structure ring homomorphism R → Q(R) = Frac(R)
  (Iwasawa instance: the inclusion Λ(G) → Q(G), in which pseudo-measures live).
Sources agree on the standard form: yes — `φ : R → Frac(R)`, `a ↦ a/1`, the R-algebra structure map; injective when localizing at non-zero-divisors.
Most general standard form: the canonical localization map `R → S⁻¹R` for `S` = non-zero-divisors of an arbitrary commutative ring `R` (Stacks/nLab); the Iwasawa `Λ(G) → Q(G)` is the instance `R = Λ(G)`.
Generality dimensions where the literature varies:
  - the ring: from a general commutative ring (Stacks/nLab) down to the concrete `R = Λ(𝒢⁺)` here. The literature-general form is "the structure map of `Frac(R)`"; the target is its specialisation at one ring.
Disagreement with the literature: none. The literature never assigns this map a dedicated name/symbol — it is "the canonical/natural map", i.e. exactly mathlib's `algebraMap R (FractionRing R)`.
```

The map is canonical and the codomain is the standard total ring of fractions; this is **not** an empty-literature (too-narrow) case — it is the most classical map there is, which is precisely why mathlib provides it generically.

## Phase 4 — Generality analysis

```
### Generality analysis — `PadicMeasure.toQPlus`

Literature-standard form (from Phase 3): the canonical localization/structure map `R → Frac(R)`, `a ↦ a/1`, for an arbitrary commutative ring `R` (Iwasawa instance: `Λ(G) → Q(G)`).
```

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the ring `PadicMeasure p (GPlus p)` (= `Λ(𝒢⁺)`) | one fixed Iwasawa algebra | any commutative ring `R` | **yes** | The map `R → Frac(R)` makes sense for every commutative ring. The target fixes `R := Λ(𝒢⁺)`. The "general form" is not a missing target — it is mathlib's existing `algebraMap R (FractionRing R)` (Phase 5). |
| 2 | the codomain `QuotientFieldPlus p` (= `Frac(Λ(𝒢⁺))`) | `FractionRing (PadicMeasure p (GPlus p))` | `Frac(R)` for general `R`, via the `IsFractionRing`/`IsLocalization` universal property | **yes** | Same axis as #1; the general codomain is mathlib's `FractionRing`/`IsFractionRing`. |

```
### Generality verdict (Phase 4b)

The current form is: a MAXIMALLY-SPECIALISED INSTANCE of an already-general mathlib map (not "a narrower theorem about a fraction-ring map" — it is the structure map of one particular fraction ring).
Number of weakening opportunities found: 1 (generalise the ring) — but the generalised form already exists in mathlib as `algebraMap R (FractionRing R)`, so this is a NO-mathlib-has-it situation, NOT a YES-but-generalise-first one (there is nothing missing to generalise *toward* — the general map is already in mathlib).
Proposed restatement: n/a — the general form is the existing mathlib `algebraMap`.
Cost of restatement: n/a.
```

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | **no** | — | Already an instance: the map is `algebraMap` from the `Algebra (Λ(𝒢⁺)) (FractionRing …)` instance. |
| 2 | sequences/metric → filters/topology? | **no** | — | No analytic/limit content; it is an algebraic ring hom. |
| 3 | explicit construction → universal-property class? | **already done** | — | The codomain is `FractionRing`, characterised by the `IsFractionRing`/`IsLocalization` universal property, and the map is the algebra structure map. The project already uses `IsFractionRing.injective`, `IsLocalization.mk'`, `IsLocalization.map_units` against exactly this map. There is no further modernisation: this *is* the modern idiom. |
| 4 | set+closure-predicate → bundled substructure? | **no** | — | Not a substructure; it is a morphism. |
| 5 | vector-space/field-specific → module/ring weakening? | **no** | — | Already at the most general level (commutative ring) via `algebraMap`. |
| 6 | 1-categorical → higher/∞-categorical? | **no** | — | Plain 1-categorical canonical morphism; no categorification move with downstream payoff. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | **no** | — | No numeric index; the only "concreteness" is the fixed ring, covered by row #1 / Phase 4a. |

```
### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: the declaration is already on the mathlib-idiomatic form — the canonical map IS `algebraMap R (FractionRing R)`, built from the `Algebra` class and the `IsFractionRing`/`IsLocalization` universal property. Naming the specific instance `toQPlus` is, if anything, slightly *less* idiomatic than mathlib's habit of writing `algebraMap _ _` (or `let K := FractionRing R`) inline. No downstream API improvement supports promoting the alias.
```

## Phase 4.5 — Diamond / defeq risk (`def`)

```
### Diamond / defeq risk — `PadicMeasure.toQPlus`
```

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | The def registers no instance and selects no instance path. The only typeclasses involved — `Algebra (Λ(𝒢⁺)) (FractionRing …)`, `CommRing`, `IsFractionRing` — are mathlib's, resolved identically whether reached via `toQPlus` or `algebraMap _ _`. No competing path. |
| 2 | Reducibility leak | **none** | No `@[reducible]` attribute. The body `algebraMap _ _` is itself already exposed to defeq throughout mathlib; sealing it under a plain `def` adds no new computational surface (it is a `RingHom`, opaque-by-data, not a computation). |
| 3 | Non-canonical unfolding | **none/low** | `toQPlus` *is* `algebraMap` definitionally; `simp`/`rfl` do not fire on it unexpectedly (no `@[simp]`). Where unfolding is wanted, the project does it explicitly (`change`, `rw [toQPlus]`). No surprise unfolding. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | All types are `Type 0` (`ℤ_[p]`, `GPlus p`, the function/measure spaces); no universe variable, no forced annotation. |
| 6 | Coercion ambiguity | **none** | The `RingHom` `FunLike`/coercion is mathlib's standard `RingHom` coercion; `toQPlus` adds no `CoeFun`/`CoeSort` and does not compete with any mathlib coercion. |

```
### Risk verdict (Phase 4.5)

Overall risk: NONE.
Top risks: none.
Recommended mitigations: n/a.
```

## Phase 5 — Mathlib search (five methods)

Searched (a) the user's form (a named `R →+* FractionRing R`), (b) the literature-standard form (the canonical structure map `R → Frac(R)`), and (c) the modern-idiom form (the `Algebra` structure map / `IsFractionRing` unit).

```
### Mathlib search-status: `PadicMeasure.toQPlus`
```

| Method | Query | Result |
|--------|-------|--------|
| [A] Lean-Finder (AI) | "canonical ring homomorphism from a ring to its fraction ring", "structure map to FractionRing as RingHom" | **HIT** → `algebraMap R (FractionRing R)` (the canonical `R →+* A` from the `Algebra` instance). Surfaced as the canonical answer. |
| [B] Loogle (type pattern) | `_ →+* FractionRing _` ; `algebraMap _ (FractionRing _)` ; `Algebra _ (FractionRing _)` | **HIT** → `algebraMap : (R : Type*) → (A : Type*) → [CommSemiring R] → [Semiring A] → [Algebra R A] → R →+* A`, instantiated at `A = FractionRing R` via the `IsFractionRing`/`FractionRing` algebra instance. No *named* `def` `R →+* FractionRing R` exists. |
| [C] LeanSearch (NL) | "the natural map from a commutative ring into its total ring of fractions", "inclusion of a ring into its localization" | **HIT** → `algebraMap`, with `FractionRing`/`IsFractionRing` as the codomain machinery. |
| [D] Grep mathlib source | `grep -rnE "def .*→\+\* .*FractionRing|def .*→\+\* .*Localization" Mathlib/` ; `grep "algebraMap _ (FractionRing"` ; `grep "def algebraMap"` | **HIT (and confirms the negative):** `algebraMap` is "the canonical map from `R` to `A`, as a `RingHom`" (`Mathlib/Algebra/Algebra/Defs.lean:29,97,367`). Mathlib uses `algebraMap _ (FractionRing …)` **inline** (≥12 source sites). The only `def … →+* FractionRing …` hits are *unrelated specialised maps* (`fromZeroRingHom`, `mapPiLocalization`, `Localization.Away.map`) and *equivalences between distinct constructions* (`RatFunc.toFractionRingRingEquiv : K⟮X⟯ ≃+* FractionRing K[X]`, `Mathlib/FieldTheory/RatFunc/Basic.lean:230`) — **never** a plain named alias for `R →+* FractionRing R`. |
| [E] Name-pattern (local search) | `algebraMap`, `toFractionRing`, `toFrac`, `toLocalization`, `fractionRingHom`, `toQ` | `algebraMap` canonical; **no** `toFractionRing`/`toFrac`/`toLocalization`/`fractionRingHom` *structure-map* alias in mathlib (only the equivalences above). In the project itself, the non-plus sibling has **no** `toQ` — it uses raw `algebraMap` (35 sites). |

```
Searched for both:
  - the user's current form (a named RingHom `Λ(𝒢⁺) →+* Q(𝒢⁺)`)  — not present as a named decl; mathlib spells it `algebraMap _ _`.
  - the literature-standard form (the canonical map `R → Frac(R)`) — present as `algebraMap R (FractionRing R)`, fully general in `R`.

Concluded: "found in mathlib as `algebraMap` (`Mathlib/Algebra/Algebra/Defs.lean`, the `Algebra`-class structure map), specialised at the `Algebra (PadicMeasure p (GPlus p)) (FractionRing …)` instance from `Mathlib/RingTheory/Localization/FractionRing.lean`; the target is `rfl`-equal to it."
```

**Follows-in-≤1-line derivation (the NO-mathlib-has-it gate):**

```lean
example (p : ℕ) [Fact p.Prime] :
    PadicMeasure.toQPlus p = algebraMap (PadicMeasure p (GPlus p)) (PadicMeasure.QuotientFieldPlus p) :=
  rfl
```

(`toQPlus p` is *defined as* `algebraMap _ _`; the derivation is 0 work — `rfl`.) Anywhere a `toQPlus p` value is wanted, `algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p)` is interchangeable with no glue — and the project already exploits exactly this (`rw [toQPlus]` at line 232, `change toQPlus … = …` at line 370).

## Phase 6 — Composition check (+ call-sites signal)

```
### Call sites — `PadicMeasure.toQPlus`

Internal use count (within the project, NOT counting the declaring file): 0
External-to-file callers: 0 distinct files
```

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (all uses are inside the declaring file `Iwasawa/ZetaGalois.lean`) | — |
| ZetaGalois.lean:135 | `toQPlus p (dirac p g - 1) * q = toQPlus p ν` (in `IsPlusPseudoMeasure`) |
| ZetaGalois.lean:194–195 | `toQPlus p (… - 1) * padicZetaPlus … = toQPlus p (projPlus p ν)` (in `projPlus_padicZeta_witness`) |
| ZetaGalois.lean:232 | `rw [hzp, toQPlus, ← hcunit.mul_left_inj, …]` — **unfolds `toQPlus` to `algebraMap`** |
| ZetaGalois.lean:333 | `toQPlus p x = toQPlus p l * padicZetaPlus …` (in `zetaIdealPlus` carrier) |
| ZetaGalois.lean:345 | `toQPlus p x = toQPlus p l * padicZetaPlus …` (in `mem_zetaIdealPlus_iff`) |
| ZetaGalois.lean:355–356, 370 | witness identity + `change toQPlus p x = toQPlus p (projPlus p ν * ρ)` — **unfolds to `algebraMap`** |

```
Inline-derivation grep (was the equivalent re-derived elsewhere without `toQPlus`?):
  - YES — pervasively. The non-plus sibling re-derives the identical pattern with raw `algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)` at 35 sites in `Measure/PseudoMeasure.lean` (e.g. `IsPseudoMeasure` at :811–813, `isPseudoMeasure_algebraMap` at :816–818). Even on the plus side, `padicZetaPlus` (:177) and `dirac_…_nonZeroDivisors` (:229) use raw `algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p)` rather than `toQPlus`.
```

**What the pattern tells us:** `K = 0` external-to-file uses, and the equivalent is re-derived inline elsewhere (the entire non-plus side, plus some plus-side defs) using raw `algebraMap`. Per the Phase-6 signal table, `K = 0` + inline re-derivation ⇒ **the def is a wrapper consumers bypass**, and mathlib has the map by name (`algebraMap`) ⇒ leans **NO-mathlib-has-it**. The wrapper is confined to one file and exists for a local elaboration reason, not as an API depended on across the project.

```
### Composition check (Phase 6)

Can `PadicMeasure.toQPlus` be obtained from mathlib in ≤3 chained calls?

Attempt 1: `algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p)`
  - Mathlib decls used: `algebraMap` (+ the `Algebra (Λ(𝒢⁺)) (FractionRing …)` instance from `FractionRing`).
  - Result: succeeds — it is not even a composition, it is a single application, and it is `rfl`-equal to `toQPlus`.
  - Notes: 1 mathlib call, ≤3. No rewriting/automation needed.

Conclusion: COMPOSABLE (degenerately — a single named mathlib map). But because mathlib has the map *by name* (`algebraMap`), the precise bucket is NO-mathlib-has-it rather than NO-composable-from-mathlib (see Phase 7).
```

## Phase 7 — Verdict synthesis (gate)

```
## Verdict: `PadicMeasure.toQPlus`

**Category:** NO-mathlib-has-it

**Evidence:**
- Literature search (Phase 3): the map is the canonical/natural/structure homomorphism `R → Frac(R)` (Wikipedia: "the natural map R → Q(R)"; nLab: "structure morphism φ : A → S⁻¹A"; Stacks; Serre/Coates: the inclusion `Λ(G) → Q(G)` in which pseudo-measures live). Universally unnamed beyond "canonical" — i.e. mathlib's `algebraMap`.
- Generality analysis (Phase 4): a maximally-SPECIALISED instance of an already-general mathlib map; Phase 4c found no modernisation move (it is already the mathlib idiom).
- Diamond/defeq risk (Phase 4.5): NONE.
- Mathlib search (Phase 5): found in mathlib as `algebraMap R (FractionRing R)` (general in `R`); the target is `rfl`-equal to it; mathlib carries no named alias for `R →+* FractionRing R`.
- Composition check (Phase 6): a single named mathlib map; `K = 0` external uses; the equivalent is re-derived inline with raw `algebraMap` across the project.
```

**Rationale.** `toQPlus` is, definitionally, mathlib's canonical structure map `algebraMap (PadicMeasure p (GPlus p)) (FractionRing (PadicMeasure p (GPlus p)))` — its body is literally `algebraMap _ _`, and `toQPlus p = algebraMap _ _` holds by `rfl`. The literature (Stacks, nLab, Wikipedia, Serre/Coates) is unanimous that this map is "the canonical/natural map" and is never given a dedicated name or symbol; mathlib correspondingly provides it generically as `algebraMap R (FractionRing R)` and writes it inline (≥12 source sites). Mathlib does **not** introduce per-ring named aliases for the fraction-ring structure map — the only `→+* FractionRing` named decls are equivalences between genuinely distinct constructions (e.g. `RatFunc.toFractionRingRingEquiv`), which is a different mathematical fact, not this map. The project's own non-plus side proves the point: it uses raw `algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)` at 35 sites with no wrapper.

The one-line `def` is **not** rescued by a Phase-2b exemption for mathlib purposes. It is not a defeq barrier — the consuming proofs (`zetaIdealPlus_eq_span` line 370 via `change`; the `rw [toQPlus]` at line 232) deliberately unfold it back to `algebraMap` so mathlib's `IsFractionRing.injective`/`IsLocalization.mk'_spec`/`IsLocalization.map_units` apply, so it depends on being `algebraMap`, not on hiding it. It registers no instance, so it averts no diamond. Its sole stated purpose — quoted in the docstring — is to dodge "an unresolved instance metavariable inside `def`-bodies over the quotient group … a known elaboration-order trap", which is a project-local Lean elaboration convenience specific to `GPlus`, not a mathlib-relevant API contract (and even `padicZetaPlus`, a `def` over `GPlus`, bypasses it for raw `algebraMap`). With `K = 0` external-to-file consumers and the equivalent re-derived inline with raw `algebraMap` throughout, the refactor-actionable conclusion is clear.

**WHY not (refactor-actionable detail).** Mathlib already has this map, *by name*: `algebraMap` (`Mathlib/Algebra/Algebra/Defs.lean:29,97,367` — "the canonical map from `R` to `A`, as a `RingHom`"), at the codomain `FractionRing (PadicMeasure p (GPlus p))` via the `Algebra`/`IsFractionRing` instance from `Mathlib/RingTheory/Localization/FractionRing.lean`. The project form follows in 0 lines (`rfl`).

```
Existing mathlib decl:        `algebraMap` (the `Algebra`-class structure map `R →+* A`)
Located at:                   `Mathlib/Algebra/Algebra/Defs.lean:29,97,367`
                              (codomain instance: `Mathlib/RingTheory/Localization/FractionRing.lean`)
Our form follows in ≤1 line:
```
```lean
example (p : ℕ) [Fact p.Prime] :
    PadicMeasure.toQPlus p
      = algebraMap (PadicMeasure p (GPlus p)) (PadicMeasure.QuotientFieldPlus p) := rfl
```
```
Call sites in our project (from Phase 6.0):  K = 0 external-to-file; ~10 in the declaring file (ZetaGalois.lean).
Refactor plan (project-local, NOT a mathlib PR):
  - Option A (keep): retain `toQPlus` as a *project-local* file-scoped abbreviation, since the docstring documents a real GPlus elaboration-order quirk it works around. If kept, it is project plumbing — do NOT PR it.
  - Option B (inline): at each of the ~10 in-file sites, replace `toQPlus p` with `algebraMap (PadicMeasure p (GPlus p)) (QuotientFieldPlus p)` — matching the non-plus side's existing idiom. Sites :232 and :370 already unfold it, so they need no change beyond dropping the wrapper name; the `change`/`rw` step becomes unnecessary.
Next action: do NOT open a mathlib PR for `toQPlus`. Mathlib's `algebraMap` is the canonical map; a named per-ring alias would be rejected. If anything in this corner is mathlib-bound, it is the genuinely-new mathematics (the convolution `CommRing` on `PadicMeasure p G`, pseudo-measure theory, the `𝒢⁺` descent) — assessed separately — not this structure-map alias.
```

```
### Verdict gate check
- NO-mathlib-has-it requires Phase 5 conclusion "found in mathlib as …": ✓ (`algebraMap`, with the `rfl` derivation shown).
- Not YES-add-as-is: Phase 5 found the map by name; no gap (the named-alias-for-`algebraMap` is exactly what mathlib declines to add).
- Not YES-but-generalise-first: the general form already exists in mathlib (`algebraMap R (FractionRing R)`); nothing missing to generalise toward.
- Not NO-composable-from-mathlib: mathlib has the map *by name*, not merely building blocks, so NO-mathlib-has-it is the more precise bucket (mirrors the sibling `QuotientFieldPlus` reasoning; "single direct application of a named mathlib map").
- Not BORDERLINE: all phases resolve cleanly and agree; the only judgment (keep-as-plumbing vs inline) is a project-local style choice that does not affect the mathlib verdict.
- One-liner gate: ONE-LINER with only a weak, project-local "API name" exemption (a GPlus elaboration workaround), which is not mathlib-relevant; the NO verdict is consistent with the gate.
```

## Phase 8 — Report (this document)

**Existing mathlib decl:** `algebraMap R A : R →+* A` — "the canonical map from `R` to `A`, as a `RingHom`" (`Mathlib/Algebra/Algebra/Defs.lean:29,97,367`), the `Algebra`-class structure map. At `A = FractionRing R` it is the localization unit `a ↦ a/1`, with the `Algebra (PadicMeasure p (GPlus p)) (FractionRing …)` instance from `Mathlib/RingTheory/Localization/FractionRing.lean`.

**Derivation (0 lines):**
```lean
example (p : ℕ) [Fact p.Prime] :
    PadicMeasure.toQPlus p
      = algebraMap (PadicMeasure p (GPlus p)) (PadicMeasure.QuotientFieldPlus p) := rfl
```

**Recommended action:** Do not PR `toQPlus` to mathlib. Either keep it as documented project-local plumbing for the `GPlus` elaboration-order workaround, or inline `algebraMap _ _` at its ~10 in-file sites to match the non-plus side. Note for the sibling: `PadicMeasure.QuotientFieldPlus` (the codomain) received the same `NO-mathlib-has-it` verdict for the analogous reason (it is `rfl`-equal to mathlib's `FractionRing`).

---

### Five-bucket verdict (final): **`NO-mathlib-has-it`**
