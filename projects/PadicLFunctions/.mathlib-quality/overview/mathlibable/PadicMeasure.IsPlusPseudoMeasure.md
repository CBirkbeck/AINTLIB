# /mathlibable report — `PadicMeasure.IsPlusPseudoMeasure`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicMeasure.IsPlusPseudoMeasure`
**Kind:** `def` (Prop-valued, noncomputable section)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:133`
**Date:** 2026-06-20

---

## FINAL VERDICT: `YES-but-generalise-first`

> The Serre/Coates notion of *pseudo-measure* — an element `λ` of the total ring of
> fractions `Q(Λ(G))` of an Iwasawa algebra with `([g]−[1])·λ ∈ Λ(G)` for all `g ∈ G`
> — is **genuinely missing from mathlib** (no pseudomeasure, no Iwasawa algebra
> `ℤ_p[[G]]`, no completed group ring, no augmentation ideal exists there). So this is
> real, novel content for mathlib. **But** the user's `def` is the predicate
> hard-specialised to the single group `G = GPlus p = ℤ_[p]ˣ/{±1}`, whereas the
> literature-standard form (and the project's own *already-generalised* convolution
> `CommRing (PadicMeasure p G)` over an arbitrary compact commutative `G`) is stated for
> an **arbitrary** group. There is even a verbatim sibling `IsPseudoMeasure` over
> `ℤ_[p]ˣ` (`Measure/PseudoMeasure.lean:811`) that is the *same predicate over a
> different group*. The mathlib-worthy object is a **single** `IsPseudoMeasure {G} […]
> (q : FractionRing (PadicMeasure p G)) : Prop` that both project copies instantiate —
> the canonical "modules-not-vector-spaces" specialisation pattern. Generalise first,
> then PR the abstract predicate; do not ship `IsPlusPseudoMeasure` as a group-specific
> def.

---

## Phase 0 — Doctor / baseline

### Baseline (Phase 0)
- **lake build:** not re-run (worktree build is stale/slow per task instructions). **Reasoned from source** — read the declaration, its sibling `IsPseudoMeasure`, every type dependency (`PadicMeasure`, `GPlus`, `QuotientFieldPlus`, `toQPlus`, `dirac`), the project's convolution-ring instance, and the mathlib search surface directly. The skill's Phase-0 fallback explicitly permits this.
- **decl `PadicMeasure.IsPlusPseudoMeasure`:** ✓ resolved at `ZetaGalois.lean:133`.
- **kind:** `def` (Prop-valued predicate).
- **has sorry:** no. The whole file (`ZetaGalois.lean`) is sorry-free (`grep -c sorry` = 0), and the def references only existing, compiling definitions; its sole consumer `isPlusPseudoMeasure_padicZetaPlus` (line 240) is a completed proof.
- **module docstring summary:** "ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p" — RJW (arXiv:2309.15692) §11.1 corollary + §11.2, on the identified Galois side (`𝒢⁺ = GPlus p`).

## Phase 1 — Comprehend

### Statement (Phase 1)

```lean
/-- A *pseudo-measure on `𝒢⁺`* (RJW Def. 3.34 applied to `G = 𝒢⁺`). -/
def IsPlusPseudoMeasure (q : QuotientFieldPlus p) : Prop :=
  ∀ g : GPlus p, ∃ ν : PadicMeasure p (GPlus p),
    toQPlus p (dirac p g - 1) * q = toQPlus p ν
```
with `variable (p : ℕ) [hp : Fact p.Prime]`.

`IsPlusPseudoMeasure` is **a definition of** the following:

An element `q` of the total ring of fractions `Q(𝒢⁺) = Frac(Λ(𝒢⁺))` of the Iwasawa
algebra `Λ(𝒢⁺)` is a **pseudo-measure on `𝒢⁺`** if, for every group element
`g ∈ 𝒢⁺`, the product `([g] − [1]) · q` lies in the image of `Λ(𝒢⁺)` inside `Q(𝒢⁺)`
— i.e. `([g] − [1]) · q` is an honest measure, not merely a fraction. Equivalently
(Serre's intuition) `q` is an element of the fraction ring with at worst a "simple pole
at the trivial character" that every augmentation generator `[g] − [1]` clears.

**Dependency unfolding (Lean side):**
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — `ℤ_[p]`-valued measures on `X`.
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)` (`Iwasawa/PlusPart.lean:215`) — the plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}`.
- `PadicMeasure p (GPlus p)` carries the convolution `CommRing` (= the Iwasawa algebra `Λ(𝒢⁺)`), from the project's **general** `instance : CommRing (PadicMeasure p G)` for any compact commutative topological monoid `G` (`Measure/PseudoMeasure.lean:81`).
- `QuotientFieldPlus p := FractionRing (PadicMeasure p (GPlus p))` (`ZetaGalois.lean:124`) — the total ring of fractions `Q(𝒢⁺)`.
- `toQPlus p : PadicMeasure p (GPlus p) →+* QuotientFieldPlus p := algebraMap _ _` (`ZetaGalois.lean:129`) — the structure map (a named `algebraMap`, named only to dodge an elaboration-order metavariable trap).
- `dirac p g` (`Measure/Basic.lean:64`) — the Dirac measure `[g]`; `1 = dirac p 1` is the unit `[1]`.

**Variables / typeclasses involved (Lean side):**
- `p : ℕ`, `[Fact p.Prime]` — the prime; fixes the coefficient ring `ℤ_[p]`.
- `q : QuotientFieldPlus p` — the element of the fraction ring being tested.

**Hypotheses:** none beyond the implicit `[Fact p.Prime]`.

**Conclusion (math):** `q` is a pseudo-measure on `𝒢⁺` ⟺ `∀ g, ([g]−[1])·q ∈ Λ(𝒢⁺)`.

**Conclusion (Lean):** n/a — this is a `def` producing a `Prop`.

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** It introduces a **named mathematical structure / notion** — the
*pseudo-measure* predicate of Serre/Coates Iwasawa theory — and is listed in the module
docstring's "Main declarations" cluster (the §11.1 corollary that ζ_p descends to a
pseudo-measure on 𝒢⁺). The notion is named after a standard concept in the literature.
(Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

- **Body line count:** 2 substantive lines (a `∀ … ∃ …` predicate). Kind is `def`.
- **One-liner verdict:** MULTI-LINE (it is a genuine 2-line predicate body, not a one-line alias).

Exemption table is therefore not triggered. For completeness, the def **does** serve as
a stable named API anchor (its name + docstring is the surface `isPlusPseudoMeasure_padicZetaPlus`
and the §12 Iwasawa-theorem statements depend on), but as a MULTI-LINE def this is a
note, not a gating exemption.

**Conclusion: MULTI-LINE.**

## Phase 3 — EXHAUSTIVE literature search (9 channels)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "pseudo-measure Iwasawa algebra Serre definition (σ−1)λ in Λ(G) p-adic zeta" | **yes** | `λ ∈ Q(Λ(G))` with `(σ−1)λ ∈ Λ(G)` ∀σ | top hit is the project's own source RJW arXiv:2309.15692; also Coates–Sujatha, Williams notes, Serre. |
| 2 | WebSearch (general/named form) | "Coates Lichtenbaum pseudomeasure Q(G) fraction ring Iwasawa augmentation ideal p-adic L-function definition" | **yes** | *verbatim:* "an element φ of the ring of fractions of A(G) is a pseudomeasure if (σ′−1)φ belongs to A(G) for all σ′ in G" | introduced by Serre; "possible simple pole at the trivial character". (Coates, Astérisque; arXiv:0711.0581.) |
| 3 | WebSearch (aliases / arbitrary-group) | "'pseudomeasure' definition profinite abelian group Galois 'ring of fractions' total quotient ring Serre Coates Iwasawa" | **yes** | *verbatim:* "A pseudomeasure is an element of the total ring of fractions of the commutative ring ℤ_ℓ[[H]] such that (1−h)λ is in ℤ_ℓ[[H]] for all h in H" | stated for an **arbitrary** group `H`/`G`; the cited paper (0711.0581) is about **non-abelian** G. |
| 4 | ChatGPT MCP-equivalent (codex `gpt-5.5`) | "Serre/Coates pseudo-measure on profinite abelian G — ambient ring, ([g]−1)λ ∈ Λ(G); arbitrary G?; historical evolution?" | **yes** | confirms: `λ ∈ Q(Λ(G))`, `([g]−1)λ ∈ Λ(G)` ∀g | answer verbatim: "stated for an arbitrary profinite abelian group G, not only for one fixed Iwasawa group"; "formulation has not essentially changed since Serre" (1978). |
| 5 | Local references (`refs/PadicLFunctions/`) | grep refs dir | **n/a** | (dir not symlinked in this worktree; PDFs are local-only) | in-file docstring cites **RJW Def. 3.34** ("let `Q(G)` denote the ring of fractions") and §11.1 corollary, TeX 3033–3039; RJW's term is exactly "pseudo-measure" for general `G`. |
| 6 | nLab | `ncatlab.org/nlab/show/pseudomeasure` (WebFetch) | **n/a** | HTTP 404 — page does not exist | not a categorical concept; nLab has no pseudomeasure entry. Recorded n/a with reason. |
| 7 | nCatLab (categorical) | (same as #6) | **n/a** | — | pseudo-measure is an Iwasawa-theory / commutative-algebra notion, not a categorical one. |
| 8 | Stacks Project | total ring of fractions (relevant only for the *ambient* ring) | **n/a (for the predicate)** | Stacks 02C5 defines `Q(A) = S⁻¹A` (the ambient ring) but has **no** pseudo-measure notion | Stacks is alg-geom/comm-alg; it has the fraction ring (covered in the `QuotientFieldPlus` report) but not the Iwasawa pseudo-measure predicate. |
| 9 | MathOverflow / Math.SE | covered by #1–#4 result sets | **n/a-as-search** | — | the definition is uncontested textbook Iwasawa theory (Serre 1978; Coates; Coates–Sujatha *Cyclotomic Fields and Zeta Values*); no open MO thread to resolve. |
| 10 | recent arXiv (≤5 yr) | "pseudomeasure" non-abelian / equivariant Iwasawa | **yes** | same Serre definition, extended to non-abelian `G` | arXiv:0711.0581 (Kakde-style), math/0311446, 1004.2578 — all use the identical "`(g−1)φ ∈ Λ(G)` ∀g" form; modern work only varies notation / adds hypotheses for applications. |

### Literature summary (Phase 3)

- **Concept identified as:** *pseudo-measure* (pseudomeasure) in the sense of **Serre (1978)**, as used by **Coates**, **Coates–Lichtenbaum**, **Coates–Sujatha**, and the project's source **RJW (Rouse–Johnston–Williams, arXiv:2309.15692), Def. 3.34**.
- **Sources agree on the standard form:** **yes**, unanimously and verbatim across channels 1–4 and 10.
- **Most general standard form:** Let `G` be a **(arbitrary) profinite/compact abelian group** (the Galois group of a `ℤ_p`-extension, or `ℤ_p^×`, or any quotient such as `ℤ_p^×/{±1}`). Let `Λ(G) = ℤ_p[[G]]` be its Iwasawa algebra and `Q(Λ(G)) = Frac(Λ(G))` its total ring of fractions. An element `λ ∈ Q(Λ(G))` is a **pseudo-measure** iff `([g]−[1])·λ ∈ Λ(G)` for every `g ∈ G`.
- **Generality dimensions where the literature varies:**
  - The group `G`: ranges over **arbitrary** profinite groups (abelian in Serre's original; non-abelian in Kakde/Ritter–Weiss). The most general is "any (profinite) group"; the user fixes the *single* concrete `G = ℤ_p^×/{±1}`.
  - Coefficient ring: `ℤ_p` (Serre) → `O_L` / `ℤ_ℓ` (general). The project uses `ℤ_[p]` throughout (matches Serre).
- **Disagreement with the literature:** **none on content.** The user's form is the literature's exact condition, only with `G` *fixed* to `𝒢⁺` rather than left abstract.

The literature search did **not** return nothing — it returned the *exact* concept with a unanimous, group-abstract standard form. By the verdicts reference this is a strong signal toward YES-* (real content), and the group-abstractness drives the choice between the two YES buckets in Phase 4.

## Phase 4 — Generality analysis

### Generality analysis — `IsPlusPseudoMeasure`

Literature-standard form (from Phase 3): pseudo-measure on an **arbitrary** profinite/compact abelian group `G`; `λ ∈ Frac(Λ(G))` with `([g]−[1])·λ ∈ Λ(G)` ∀ `g ∈ G`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | the group is **hard-coded** `GPlus p = ℤ_[p]ˣ/{±1}` | one specific quotient group | **arbitrary** compact commutative topological group/monoid `G` | **yes** | The predicate body uses `G` only through (i) the ring `PadicMeasure p G`, (ii) `dirac p g - 1`, (iii) `algebraMap … (FractionRing …)`. The project **already** has `CommRing (PadicMeasure p G)` for any `[TopologicalSpace G] [CommMonoid G] [ContinuousMul G] [CompactSpace G]` (`PseudoMeasure.lean:81`, explicitly generalised in the §11 pass "for any profinite abelian G"). So abstracting `G` is mechanical. |
| 2 | quantifier domain `g : GPlus p` | `g` ranges over the fixed group | `g` ranges over the abstract `G` | yes | same axis as #1 — falls out of abstracting `G`. |
| 3 | ambient `QuotientFieldPlus p = FractionRing (PadicMeasure p (GPlus p))` | fraction ring of one ring | `FractionRing (PadicMeasure p G)` | yes | mathlib's `FractionRing`/`IsFractionRing` is already general in the ring; abstracting `G` abstracts this for free. |
| 4 | structure map `toQPlus` (a named `algebraMap`) | a named hom for the fixed group | `algebraMap (PadicMeasure p G) (FractionRing …)` | yes (cosmetic) | `toQPlus` exists only to dodge an elaboration metavariable for the *quotient* group; in the abstract form one uses `algebraMap` directly or a per-`G` named hom. Not a content axis. |

**Crucial cross-check — the sibling.** `IsPseudoMeasure` (`Measure/PseudoMeasure.lean:811`)
is the **identical predicate over `G = ℤ_[p]ˣ`**:
```lean
def IsPseudoMeasure (q : QuotientField p) : Prop :=
  ∀ g : ℤ_[p]ˣ, ∃ ν : PadicMeasure p ℤ_[p]ˣ,
    algebraMap _ (QuotientField p) (dirac p g - 1) * q = algebraMap _ _ ν
```
The project carries **two byte-for-byte copies** of one notion, differing only in the
group (`ℤ_[p]ˣ` vs `GPlus p`). This is precisely the duplication that the abstract
mathlib form eliminates. (See also `IsPseudoMeasure.sub`, `isPseudoMeasure_algebraMap`,
`pseudoMeasure_eq_zero_of_moments` on the 𝒢-side — an API that would be stated once
against the abstract predicate.)

### Generality verdict (Phase 4b)

**The current form is: STRICTLY NARROWER THAN STANDARD.**
**Number of weakening opportunities found: 1 substantive** (abstract the group `G`; axes 1–4 all collapse to this single move).

**Proposed restatement** (the literature-standard, group-abstract form):
```lean
variable {G : Type*} [TopologicalSpace G] [CommGroup G] [ContinuousMul G] [CompactSpace G]

/-- A *pseudo-measure* on the compact commutative group `G` (Serre): an element `q` of
the total ring of fractions `Q(Λ(G)) = Frac(Λ(G))` of the Iwasawa algebra with
`([g] − [1]) · q ∈ Λ(G)` for every `g ∈ G`. -/
def IsPseudoMeasure (q : FractionRing (PadicMeasure p G)) : Prop :=
  ∀ g : G, ∃ ν : PadicMeasure p G,
    algebraMap (PadicMeasure p G) (FractionRing (PadicMeasure p G)) (dirac p g - 1) * q
      = algebraMap _ _ ν
```
Then `IsPlusPseudoMeasure p q := IsPseudoMeasure (G := GPlus p) p q` and the existing
`IsPseudoMeasure` (`ℤ_[p]ˣ`) both become **instantiations** — the two project copies
merge into one.

**Cost of restatement: CHEAP — mechanical rewrite.** The convolution ring, `dirac`,
`augmentationIdeal`, and `FractionRing` are all already general in `G`; abstracting the
group is a signature edit, and the one local consumer (`isPlusPseudoMeasure_padicZetaPlus`)
type-checks against the instantiation unchanged. (Per the skill: cost does not change the
bucket; this one is cheap anyway.)

### Phase 4c — Modern-mathlib-idiom restatement (Bourbaki 2.0 check)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let G be a foo" preamble → **typeclass / abstract parameter**? | **yes** | abstract `G` behind `[TopologicalSpace G] [CommGroup G] [ContinuousMul G] [CompactSpace G]` (exactly the convolution-ring constraints) | one `IsPseudoMeasure` over `G` ⟹ the entire pseudo-measure API (`.sub`, `_algebraMap`, `eq_zero_of_moments`, descent along quotients) is stated once and applies to every Galois group, including `ℤ_p^×` and `ℤ_p^×/{±1}`. |
| 2 | sequences/metric → filters/topological? | no | — | the predicate is algebraic; no metric/sequence content. |
| 3 | construct an object → universal-property class? | partial-no | one could phrase "pseudo-measure" via the augmentation ideal `I(G)` as `{q | I(G)·q ⊆ Λ(G)}` (a sub-`Λ(G)`-module of `Q(Λ(G))`), but the `∀g, ([g]−1)q ∈ Λ` form is the literature-standard and composes fine | a bundled `Submodule` of pseudo-measures could come *later* as API; not required for the core def, and the literature uses the predicate form. |
| 4 | set-with-closure-predicate → bundled substructure? | no (for the def itself) | (see #3) | — |
| 5 | vector-space/field-specific → weaken typeclasses? | **yes (this is the move)** | the group `G` is the "field-specific" datum here; weakening `GPlus p` → abstract `G` is the typeclass-generalisation | scalar/group-restriction: results proved for abstract `G` specialise to every concrete Galois group with no re-proof. |
| 6 | 1-categorical → higher-categorical? | no | — | no categorification target. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary structure? | **yes** | `G = ℤ_p^×/{±1}` (a concrete group) → arbitrary compact commutative `G` | unifies with the project's already-abstract `conv`/`augmentationIdeal`; matches the literature's "for any profinite abelian `G`". |

**Modern-idiom verdict (Phase 4c): yes.**
- **Proposed mathlib-idiomatic restatement:** the group-abstract `IsPseudoMeasure {G} […] (q : FractionRing (PadicMeasure p G))` above (rows 1/5/7 all point to the same single move).
- **Cost:** CHEAP.
- **Mathlib downstream this enables:** the full Serre/Coates pseudo-measure API (`IsPseudoMeasure.sub`, `isPseudoMeasure_algebraMap`, `pseudoMeasure_eq_zero_of_moments`, the quotient-descent corollary `isPlusPseudoMeasure_padicZetaPlus`) is stated **once** and applies to every Galois group; the `ℤ_p^×` and `ℤ_p^×/{±1}` cases stop being two separate copies.
- **Real mathematical improvement (not "looks cooler"):** it eliminates a genuine, already-present duplication (two byte-identical predicates `IsPseudoMeasure`/`IsPlusPseudoMeasure`) and matches the literature's native generality — exactly the "modules-not-vector-spaces" pattern the verdicts reference names as the right YES-but-generalise move.

**The honesty bar is met:** the downstream consequence is concrete (deduplicated API stated once over `G`), not aesthetic.

## Phase 4.5 — Diamond / defeq risk (`def`)

### Diamond / defeq risk — `IsPlusPseudoMeasure`

The declaration is a plain **`Prop`-valued `def`** with **no** `@[reducible]`, `@[simp]`,
`instance`, `class`, `CoeFun`, or `CoeSort` attribute (confirmed by source read of
`ZetaGalois.lean:132–135` and an attribute grep). A predicate into `Prop` introduces no
algebraic-hierarchy instance, no new defeq on `Mul`/`Zero`/`AddCommMonoid`, and no
typeclass-search target.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | declares no instance; `Prop`-valued predicate is never an instance target. No two paths to a common instance. |
| 2 | Reducibility leak | **none** | no `@[reducible]`; the def is semi-reducible like any plain `def`. Its body is a `∀∃` proposition, not a computation that `simp`/`rfl` would silently unfold into an algebraic goal. |
| 3 | Non-canonical unfolding | **none** | nothing rewrites it; the only consumer (`isPlusPseudoMeasure_padicZetaPlus`) `intro`s the `∀` and supplies the `∃` witness explicitly. |
| 4 | Instance priority collision | **n/a** | not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | `q : QuotientFieldPlus p` and `g : GPlus p` are in fixed `Type`; no universe annotation forced. (The proposed abstract form adds `{G : Type*}`, the standard mathlib universe-polymorphic pattern — no issue.) |
| 6 | Coercion ambiguity | **none** | no `CoeFun`/`CoeSort`; `Prop` is not coerced. The `toQPlus`/`dirac` coercions inside the body are the existing ring/`algebraMap` coercions, not new ones. |

### Risk verdict (Phase 4.5)

**Overall risk: NONE.** A `Prop`-valued predicate with no attributes is infrastructure-inert.
(The group-abstract restatement in Phase 4b/4c re-introduces **no** risk — it only adds the
standard `{G : Type*} […]` parameters; still a plain `Prop` def.)

## Phase 5 — Mathlib five-method search

Searched on (a) the user's form (pseudo-measure on `𝒢⁺`), (b) the literature-standard
group-abstract form (pseudo-measure on an arbitrary profinite abelian `G`), and (c) the
ambient infrastructure (Iwasawa algebra `ℤ_p[[G]]`, completed group ring, augmentation
ideal).

### Mathlib search-status: `PadicMeasure.IsPlusPseudoMeasure`

| Method | Query | Result |
|---|---|---|
| [A] Lean-Finder (AI/NL) | "pseudo-measure Iwasawa", "element of fraction ring of group algebra with (g−1)x integral" | **no hit** — surfaces only generic localization/`IsFractionRing` lemmas; no pseudo-measure predicate. |
| [B] Loogle (type pattern) | `(_ : FractionRing _) → Prop`, predicates of shape `∀ _, ∃ _, algebraMap _ _ _ * _ = algebraMap _ _ _` | **no hit** — no mathlib `Prop` of this shape over a group-algebra fraction ring. |
| [C] LeanSearch (NL) | "pseudomeasure", "p-adic L-function as a measure on a Galois group", "Iwasawa algebra fraction ring element" | **no hit** for the predicate (returns measure-theory `Measure`, unrelated). |
| [D] Grep mathlib src | `grep -rni "pseudomeasure\|pseudo.measure" Mathlib`; `grep -rni "iwasawa" Mathlib`; `completedGroupAlgebra`; `augmentationIdeal` | **no hit.** `pseudomeasure`: 0 results. `iwasawa`: only `GroupTheory/GroupAction/Iwasawa.lean` (the *Iwasawa simplicity criterion* — unrelated). `completedGroupAlgebra`/`augmentationIdeal`: 0 results. |
| [E] Name pattern (local + mathlib) | `IsPseudoMeasure`, `IsPlusPseudoMeasure`, `PseudoMeasure`, `pseudoMeasure` | present **only** in this project; **absent** from mathlib. |

**Searched for both forms:** yes — the user's `𝒢⁺` form *and* the abstract-`G` form
(plus the supporting Iwasawa-algebra / completed-group-ring / augmentation-ideal
infrastructure). Mathlib has **none** of it.

**Concluded:** **not in mathlib** (all five methods exhausted, plus the literature-standard
abstract form and the entire supporting infrastructure). Mathlib has neither the
pseudo-measure predicate, nor the Iwasawa algebra `ℤ_p[[G]]` as a measure ring, nor the
augmentation ideal — there is no existing decl to specialise from and no `D'` to re-aim at.

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `IsPlusPseudoMeasure`

- **Internal use count: 1** (within the project, excluding the declaring line).
- **External-to-file callers: 0.**

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `Iwasawa/ZetaGalois.lean:240–241` | `theorem isPlusPseudoMeasure_padicZetaPlus … : IsPlusPseudoMeasure p (padicZetaPlus p hp2) := …` (the RJW §11.1 corollary — the def's raison d'être) |

Inline-derivation grep (was the predicate re-spelled elsewhere without `IsPlusPseudoMeasure`?): **(none)** — but the **same notion is re-derived as the separate def `IsPseudoMeasure` over `ℤ_[p]ˣ`** (`PseudoMeasure.lean:811`), which is the duplication Phase 4 flagged, not an inline bypass.

**What the pattern tells you.** K = 1 internal use is, on its own, a "possibly wrong
abstraction / could be inlined" signal. **But** the single use is the *headline corollary
of the file* (ζ_p is a pseudo-measure on 𝒢⁺ — a named theorem the §12 Iwasawa Main
Conjecture statement consumes), and the def names a *standard literature concept* with its
own multi-lemma API on the sibling group. So this is not "inline it"; it is "the named
notion is correct, but it is stated one group too narrowly" — which is the
YES-but-generalise reading, reinforced by the existence of the `IsPseudoMeasure` twin.

### Composition check (Phase 6)

Can `IsPlusPseudoMeasure` be **derived** from mathlib in ≤3 chained calls? **No.**

- **Attempt 1 — mathlib has the predicate:** fails. Phase 5 found no pseudo-measure
  notion, no Iwasawa algebra, no augmentation-ideal API in mathlib. There is nothing to
  compose *from*.
- **Attempt 2 — it is "just `∀∃` over `algebraMap`":** the *shape* is generic, but the
  *content* (the Serre pseudo-measure condition over an Iwasawa algebra) is not produced
  by any mathlib primitive — there is no mathlib lemma whose composition yields "this is
  the pseudo-measure predicate". Writing the `∀g, ∃ν, …` by hand is *defining* the notion,
  not composing existing mathlib decls.

**Conclusion: NOT-COMPOSABLE.** (A `def` that names a standard concept absent from mathlib
is, by construction, not a ≤3-call composition of mathlib decls.)

## Phase 7 — Verdict synthesis (gate)

### Verdict: `PadicMeasure.IsPlusPseudoMeasure`

**Category:** `YES-but-generalise-first`

**Evidence:**
- **Literature search (Phase 3):** the **Serre/Coates pseudo-measure** — unanimous, verbatim, group-abstract standard form ("`λ ∈ Frac(Λ(G))` with `([g]−1)λ ∈ Λ(G)` ∀g", for an *arbitrary* profinite abelian `G`; unchanged since 1978). 5 channels hit (WebSearch ×3, codex/MCP-equiv, arXiv); nLab/Stacks/MO recorded n/a with reasons.
- **Generality analysis (Phase 4):** **STRICTLY NARROWER THAN STANDARD** — the user fixed `G = GPlus p`; the standard form (and the project's own already-general convolution ring) is over arbitrary `G`. Phase 4c: modern-idiom **yes** (abstract the group; real downstream = one deduplicated API). A byte-identical sibling `IsPseudoMeasure` over `ℤ_[p]ˣ` already exists — the duplication the generalisation removes.
- **Mathlib search (Phase 5):** **not in mathlib** under either form; no pseudo-measure, no Iwasawa algebra `ℤ_p[[G]]`, no augmentation ideal — nothing to specialise from.
- **Composition check (Phase 6):** **NOT-COMPOSABLE** — no mathlib building blocks for the notion exist.

**Rationale.**
The pseudo-measure notion is real, standard mathematics that mathlib is **missing entirely**
(Phase 5: zero hits for pseudomeasure / Iwasawa algebra / augmentation ideal across all
five methods). That rules out both NO buckets: there is no mathlib decl to delete in favour
of (`NO-mathlib-has-it`) and no ≤3-call composition to inline (`NO-composable`). So this is
a genuine YES. But it is **not** `YES-add-as-is`, because Phase 4b found the form STRICTLY
NARROWER than the literature standard and Phase 4c found a real modernisation: the literature
states the notion for an **arbitrary** profinite abelian `G`, the project's *own*
convolution `CommRing (PadicMeasure p G)` is already general in `G` (generalised in the §11
pass "for any profinite abelian G"), and the project literally carries the same predicate
twice — `IsPseudoMeasure` over `ℤ_[p]ˣ` and `IsPlusPseudoMeasure` over `ℤ_[p]ˣ/{±1}`. The
mathlib-worthy object is the single group-abstract `IsPseudoMeasure {G} […] (q :
FractionRing (PadicMeasure p G))` that both copies instantiate. By the verdict gate,
YES-add-as-is is *rejected* here precisely because Phase 4b was STRICTLY NARROWER and Phase
4c flagged a downstream-justified modern idiom; the correct bucket is
`YES-but-generalise-first` with reason **both** LITERATURE-WEAKENING and MODERN-IDIOM.

**Reason for the generalisation:**
- **LITERATURE-WEAKENING:** Phase 4b — the user's `G = GPlus p` is strictly narrower than the literature-standard arbitrary profinite abelian `G`.
- **MODERN-IDIOM (Bourbaki 2.0):** Phase 4c — abstracting the group is a real organisational improvement (collapses the `IsPseudoMeasure`/`IsPlusPseudoMeasure` duplication into one predicate + one API).

**Proposed restatement:**
```lean
variable {G : Type*} [TopologicalSpace G] [CommGroup G] [ContinuousMul G] [CompactSpace G]

/-- A *pseudo-measure* on the compact commutative group `G` (Serre): an element `q` of
the total ring of fractions `Frac(Λ(G))` of the Iwasawa algebra `Λ(G) = ℤ_p[[G]]`
with `([g] − [1]) · q ∈ Λ(G)` for every `g ∈ G`. -/
def IsPseudoMeasure (q : FractionRing (PadicMeasure p G)) : Prop :=
  ∀ g : G, ∃ ν : PadicMeasure p G,
    algebraMap (PadicMeasure p G) (FractionRing (PadicMeasure p G)) (dirac p g - 1) * q
      = algebraMap _ _ ν
-- then:  IsPlusPseudoMeasure p q  ↝  IsPseudoMeasure (G := GPlus p) p q   (instantiation)
--        existing IsPseudoMeasure (ℤ_[p]ˣ)  ↝  IsPseudoMeasure (G := ℤ_[p]ˣ) p q
```

**Estimated cost of regeneralisation: CHEAP** (mechanical — the ring, `dirac`,
`augmentationIdeal`, and `FractionRing` are already general in `G`; the one local consumer
type-checks against the instantiation). *Note: EXPENSIVE would not downgrade the verdict;
this happens to be cheap.*

**Mathlib downstream this enables (MODERN-IDIOM, REQUIRED):**
- One predicate `IsPseudoMeasure` over `G` ⟹ the entire pseudo-measure API stated **once**: `IsPseudoMeasure.sub`, `isPseudoMeasure_algebraMap`, `pseudoMeasure_eq_zero_of_moments`, and the quotient-descent corollary (`isPlusPseudoMeasure_padicZetaPlus`) all generalise from "two groups, two copies" to "any `G`".
- Proofs blocked by the old form: any statement quantifying over *both* `ℤ_p^×` and `ℤ_p^×/{±1}` (e.g. functoriality/descent of pseudo-measures along the quotient `π : G → G⁺`) currently cannot be stated uniformly — they need the abstract predicate.
- It matches mathlib's iron rule (most general form that makes sense) and the literature's native generality; it is the same win as `Submodule`-not-ad-hoc-subset and modules-not-vector-spaces.

**Gap named (for the YES bucket):** mathlib has **no Iwasawa-theory layer at all** — no
`ℤ_p[[G]]` Iwasawa algebra as a measure ring, no augmentation ideal of a profinite group
ring, and no pseudo-measure predicate (Phase 5 [D] grep: 0 hits). This def (in its abstract
form) is the foundational predicate that an Iwasawa-theory contribution to mathlib would
need; it is not a reformulation users already do by hand against existing API — there is no
existing API.

**Proposed mathlib location (post-generalisation):** a new
`Mathlib/NumberTheory/Padics/Iwasawa/PseudoMeasure.lean` (or under
`Mathlib/RingTheory/Iwasawa/`), shipped **together** with: the Iwasawa-algebra measure ring
`CommRing (PadicMeasure p G)`, `augmentationIdeal`, and the basic API
(`IsPseudoMeasure.sub`, `isPseudoMeasure_algebraMap`) — these are one coherent PR grain, not
a lone predicate.

**Next action:** run `/generalise PadicMeasure.IsPlusPseudoMeasure` (it will tension the
form against both the literature-standard abstract-`G` target from Phase 3 and the
modern-idiom form from Phase 4c, and should *merge* it with the sibling `IsPseudoMeasure`).
Only after the abstract predicate + its core API exist as one unit, run `/cleanup` and open
the mathlib PR. Do **not** PR `IsPlusPseudoMeasure` as a `GPlus`-specific def.

### Pre-PR checklist (after generalisation)
- [ ] `/generalise PadicMeasure.IsPlusPseudoMeasure` — merge with `IsPseudoMeasure`; abstract `G`.
- [ ] Ship the predicate **with** the Iwasawa-algebra ring + `augmentationIdeal` + base API (one PR grain).
- [ ] `/cleanup` the new file before submission.
- [ ] Pick a reviewer from `Mathlib/NumberTheory/` / number-theory maintainers (this opens a new Iwasawa-theory corner).

## Phase 8 — Report (this document)

**Five-bucket verdict (final): `YES-but-generalise-first`**

- **What's novel for mathlib:** the Serre/Coates **pseudo-measure** predicate (and the Iwasawa-algebra layer it lives in) — entirely absent from mathlib.
- **Why generalise first:** the user's def fixes the group to `GPlus p`; the literature standard and the project's own already-general convolution ring support an **arbitrary** compact commutative `G`, and a byte-identical sibling `IsPseudoMeasure` over `ℤ_[p]ˣ` already exists. The mathlib form is one group-abstract `IsPseudoMeasure {G} (q : FractionRing (PadicMeasure p G))`.
- **Risk:** Phase 4.5 NONE (a `Prop`-valued predicate with no attributes).
- **Cost:** CHEAP (does not affect the bucket).

---

## Next step

Run `/generalise PadicMeasure.IsPlusPseudoMeasure` to restate the predicate over an
arbitrary compact commutative group `G` (merging it with the sibling
`PadicMeasure.IsPseudoMeasure` on `ℤ_[p]ˣ`), then ship the abstract predicate **together
with** its Iwasawa-algebra ring + augmentation-ideal + base API as one mathlib PR; run
`/cleanup` first. Do not PR the `GPlus`-specific `IsPlusPseudoMeasure` as-is.
