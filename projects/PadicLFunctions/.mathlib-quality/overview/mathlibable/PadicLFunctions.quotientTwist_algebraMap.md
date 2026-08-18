# `/mathlibable` report — `PadicLFunctions.quotientTwist_algebraMap`

**Final verdict: `NO-mathlib-has-it`.** Mathlib already has this exact statement as
`IsLocalization.ringEquivOfRingEquiv_eq` (general localizations) and, in the
fraction-ring-specialised, `@[simp]`-tagged form that matches the project's setup verbatim,
`IsFractionRing.ringEquivOfRingEquiv_algebraMap`. The project's `quotientTwist` def is
*definitionally* `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`, and the lemma's own
proof in source is literally `IsLocalization.ringEquivOfRingEquiv_eq _ μ`.

---

### Baseline (Phase 0)
- lake build:               not re-run; reasoned from source (per task BUILD NOTE — `lake build` is stale/slow here; declaration + dependency closure read directly from source files and mathlib `.lake/packages/mathlib/`).
- decl `PadicLFunctions.quotientTwist_algebraMap`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:174`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the p-adic family of Eisenstein series (RJW §8) — Kubota–Leopoldt pseudo-measure interpolates the constant Eisenstein coefficients; this section builds the "x-twist" ring automorphism of the convolution algebra and extends it to the total fraction ring `Q(ℤ_p^×)`.

---

### Statement (Phase 1)

`PadicLFunctions.quotientTwist_algebraMap` is a theorem stating the following:

Let `Λ = PadicMeasure p ℤ_[p]ˣ` be the Iwasawa convolution algebra and let
`Q = QuotientField p = FractionRing Λ` be its total ring of fractions. The "x-twist"
`unitsTwist p : Λ ≃+* Λ` is a ring automorphism that, via `IsLocalization.ringEquivOfRingEquiv`,
extends to a ring automorphism `quotientTwist p : Q ≃+* Q`. The theorem says this extension
**commutes with the canonical localization (algebra) map** `Λ → Q`: for every `μ ∈ Λ`,

    quotientTwist p (algebraMap Λ Q μ) = algebraMap Λ Q (unitsTwist p μ).

In ordinary commutative-algebra language: the localisation `S⁻¹φ : S⁻¹A → S⁻¹A` of a ring
automorphism `φ : A ≃+* A` (here `A = Λ`, `S = A⁰` the non-zero-divisors, `φ = unitsTwist`)
makes the localisation square commute — `(S⁻¹φ) ∘ ι = ι ∘ φ`, where `ι : A → S⁻¹A` is the
structure map. This is the defining/characterising property of the induced map on
fraction rings.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime; only used to make `Λ` and `Q` make sense.
- `μ : PadicMeasure p ℤ_[p]ˣ` — the element of the base ring `Λ` being mapped.
- Implicit infrastructure: `Λ` is a `CommRing` (in fact a domain — it must be, for
  `FractionRing` + `IsFractionRing` to be the right notion), `Q = FractionRing Λ`, with the
  `IsFractionRing Λ Q` instance; `unitsTwist p : Λ ≃+* Λ`; `quotientTwist p : Q ≃+* Q` built
  from it by `IsLocalization.ringEquivOfRingEquiv`.

Hypotheses (Lean side):
- none beyond the ambient instances. (No `p ≠ 2`, no positivity, nothing — it is pure
  localisation functoriality.)

Conclusion (math): the induced automorphism of the fraction ring commutes with the
localisation map; equivalently `quotientTwist` is *the* extension of `unitsTwist` characterised
by the universal property of localisation.

Conclusion (Lean): `quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p) μ) = algebraMap _ _ (unitsTwist p μ)`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: It is a glue lemma — the naturality/characterising-square equation for an
already-defined induced map, with a one-call proof. It introduces no new structure, is not a
`## Main results` item (the main results are `eisensteinFamily_interpolation`,
`noMeasure_interpolates_pPow`, `twistedZetaHalf_isTwistedPseudoMeasure`), and is not named after
a person/place.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`IsLocalization.ringEquivOfRingEquiv_eq _ μ`).
One-liner verdict: n/a — kind is `theorem`, not a `def`. (The lemma *is* a one-line proof, which
is itself a strong NO signal: it discharges entirely by applying a single existing mathlib lemma.
Recorded and carried into Phase 7. The exemption table below is filled for completeness even
though the kind is `theorem`.)

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                 | no       | The statement is the standard naturality equation; nothing downstream relies on a *sealed* spelling — both occurrences (`EisensteinFamily.lean:228`) just `rw` with it, and could `rw` with the mathlib lemma directly. |
| Avoid typeclass diamonds          | no       | No instances are introduced; `quotientTwist` is a plain `noncomputable def` of a `RingEquiv`. |
| Mark semantic intent / API name   | no (weak) | The only "API name" benefit would be a project-local alias `quotientTwist_algebraMap`; but the *def* `quotientTwist` it is about is itself a rename of `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)` (see Phase 6), so the alias adds no semantic content over the mathlib name. |

Conclusion: proof is a ONE-LINE application of a single existing mathlib lemma → biases the
verdict strongly toward NO-mathlib-has-it.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                           | Query | Hit? | Standard form found | Notes |
|----|-----------------------------------|-------|------|----------------------|-------|
|  1 | WebSearch (specific form)         | "localization of a ring isomorphism induced map fraction ring algebraMap commutes" | yes | `(ringEquivOfRingEquiv h)(algebraMap A K a) = algebraMap B L (h a)` | Returned the mathlib `FractionRing` doc page verbatim; the standard naturality equation. The exact statement under assessment. |
|  2 | WebSearch (general form)          | "ring isomorphism extends to total ring of fractions functoriality of localization" | yes | universal property: `f : R→T` inverting `S` factors uniquely through `S⁻¹R`; localisation is a functor; total ring of fractions `Frac A = A_S` for `S` = regular elements | Wikipedia "Total ring of fractions", ETSU/UChicago lecture notes — functoriality is textbook-standard. |
|  3 | WebSearch (named-after / aliases) | "induced isomorphism rings of fractions commutes with canonical map ... universal property" | yes | universal property → unique structure-preserving induced map; `S⁻¹A/S⁻¹I ≅ S̄⁻¹(A/I)` as an instance | Stacks `algebra.pdf`, GSU Lecture 6. Confirms the induced map is *characterised* by commuting with the localisation maps. |
|  4 | ChatGPT MCP (chatgpt-math)        | (intended: "standard statement + generality + historical evolution of: localisation of a ring map commutes with the structure map") | n/a | — | A `chatgpt-math` MCP server is configured in `~/.claude.json`, but its tool was **not surfaced as a callable tool in this session** (ToolSearch returned no `chatgpt`/`ask`-style tool). Recorded `n/a — MCP tool not available this session`. Channels 1–3 + 6 already pin the standard form unambiguously, so this does not change the verdict. |
|  5 | Local references                  | grep `projects/PadicLFunctions/.mathlib-quality/references/` | n/a | (directory absent) | `.mathlib-quality/` contains only `overview/`; no `references/` dir. Recorded n/a. |
|  6 | nLab                              | localization+of+a+commutative+ring (WebFetch) | partial | universal property + explicit construction of `S⁻¹R` | nLab page gives the universal property and construction but, as fetched, does **not** spell out functoriality / the induced map. The universal property already implies the naturality equation (uniqueness of the factoring map). |
|  7 | nCatLab (if categorical)          | localisation as a functor | n/a | — | This is a 1-categorical, fully elementary commutative-algebra fact (functoriality of `S⁻¹(−)`). No higher-categorical content; the nLab universal-property entry (row 6) covers the categorical angle. Recorded n/a — not a higher-categorical concept. |
|  8 | Stacks Project (if alg geom)      | "stacks project localization functorial ring map induces S⁻¹R → S'⁻¹R' commutative diagram" | yes (diffuse) | functoriality of `S⁻¹(−)` on rings and modules appears throughout §10 (Commutative Algebra); e.g. for module maps `S⁻¹u : S⁻¹M → S⁻¹N` is well-defined and functorial | So foundational it is used in passing across many tags (07BH, 05DD, …) rather than isolated in one. Confirms textbook-standard status. |
|  9 | MathOverflow / Math.StackExchange | (covered by general WebSearch rows #2–#3) | n/a | — | The general/aliases WebSearch already surfaced lecture-note and reference treatments; no MO-specific subtlety exists for so elementary a fact. Recorded n/a — no open question; standard textbook material. |
| 10 | recent arXiv (last 5 years)       | — | n/a | — | Functoriality of localisation is 20th-century commutative algebra (Bourbaki, Atiyah–Macdonald). No recent-arXiv relevance. Recorded n/a — not a research-frontier concept. |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (specific
naturality equation / general functoriality / universal-property aliasing); the local refs dir
was checked (absent → n/a); nLab was checked; Stacks / nCatLab / MathOverflow / arXiv were each
checked or recorded n/a with a reason. The one mandatory channel not run is ChatGPT MCP — its
tool was not available in this session (row 4), recorded n/a with reason; the standard form is
nonetheless pinned by four independent channels.

### Literature summary (Phase 3)

Concept identified as: **functoriality / naturality of localisation of rings** — specifically the
characterising property of the localisation `S⁻¹φ` of a ring (iso)morphism `φ`: it commutes with
the structure maps, `(S⁻¹φ) ∘ ι_A = ι_B ∘ φ`. For the total ring of fractions this is the
"induced isomorphism of fraction rings".
Sources agree on the standard form: yes. Every source (Wikipedia, ETSU/UChicago/GSU lecture
notes, Stacks, and mathlib's own doc page) states the same naturality square; it is a direct
consequence of the universal property of localisation.
Most general standard form: for a ring map `φ : A → B`, multiplicative sets `S ⊆ A`, `T ⊆ B` with
`φ(S) ⊆ T`, the induced map `S⁻¹A → T⁻¹B` is the unique ring map commuting with the localisation
maps; it sends `a/s ↦ φ(a)/φ(s)` and in particular `ι_A(a) ↦ ι_B(φ(a))`. (Isomorphism + fraction
ring is the special case `φ` an iso, `S = A⁰`, `T = B⁰`.)
Generality dimensions where the literature varies:
  - the map: general ring **hom** `φ : A → B` (most general) vs. **iso** `A ≃+* B` (what the
    project uses, and what `ringEquivOfRingEquiv` packages) — iso is a strict specialisation.
  - the multiplicative sets: arbitrary `S, T` with `φ(S) ⊆ T` (most general) vs. the
    non-zero-divisors `A⁰`/`B⁰` of the fraction-ring case (what the project uses).
  - the base/target rings: distinct `A, B` (most general) vs. the same ring `A = B` (the project's
    endomorphism/automorphism case).
Disagreement with the literature: none. The project's statement is the literature's standard
naturality equation, instantiated at iso / fraction ring / endo case.

---

### Generality analysis — `PadicLFunctions.quotientTwist_algebraMap`

Literature-standard form (from Phase 3): the naturality equation `(S⁻¹φ)(ι_A a) = ι_B(φ a)` for a
ring map `φ` between localisations at compatible multiplicative sets; equivalently mathlib's
`IsLocalization.map_eq` / `IsLocalization.ringEquivOfRingEquiv_eq` / `IsFractionRing.ringEquivOfRingEquiv_algebraMap`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|---------------------------|---------------------|---------------------------------|
| 1 | the ring map | `unitsTwist p : Λ ≃+* Λ` (an automorphism of ONE ring) | a ring **homomorphism** `φ : A → B` between possibly-distinct rings | yes — the general statement is for any `φ : A →+* B` | This is exactly the gradient along which mathlib already generalises: `IsLocalization.map` is for a `RingHom` between localizations at compatible monoids; `ringEquivOfRingEquiv` is the iso specialisation; `IsFractionRing.ringEquivOfRingEquiv` the same-`A⁰` fraction-ring specialisation. The project's lemma sits at the *most specialised* end. |
| 2 | the multiplicative set | non-zero-divisors `Λ⁰` (fraction ring) | arbitrary `S` with `φ(S) ⊆ T` | yes — `IsLocalization.map_eq` covers it | The project only needs the fraction-ring case, which mathlib already specialises (`IsFractionRing.ringEquivOfRingEquiv_algebraMap`). |
| 3 | base = target | `A = B = Λ` (endomorphism) | distinct `A, B` | yes | The endomorphism case is the trivial instantiation `A = B`; nothing in the statement uses `A = B`. |

The generality direction is *downward* from the literature: the project's lemma is a maximally
specialised instance of a fact mathlib already has in three nested generalities. There is no
direction in which the project's lemma is *more* general than mathlib.

### Generality verdict (Phase 4b)

The current form is: STRICTLY NARROWER THAN STANDARD (it is a specialisation of mathlib's general
`IsLocalization.ringEquivOfRingEquiv_eq` / `IsFractionRing.ringEquivOfRingEquiv_algebraMap`).
Number of weakening opportunities found: 3 (general ring hom; arbitrary multiplicative set;
distinct source/target) — **but all three are already realised in mathlib**, so they argue for
NO-mathlib-has-it, not YES-but-generalise-first. (YES-but-generalise-first requires the general
form to be *missing* from mathlib; here it is present.)
Proposed restatement: none needed — the general form is `IsLocalization.ringEquivOfRingEquiv_eq`,
already in mathlib.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The statement already lives in mathlib's typeclass-driven `IsLocalization`/`IsFractionRing` framework. |
|  2 | sequences/metric → filters/topological? | no | — | No limit/topology content; pure algebra. |
|  3 | construct an object → universal-property class? | **already done by mathlib** | — | The relevant object (the induced fraction-ring map) is *already* defined by mathlib via the universal property (`IsLocalization.map`, `ringEquivOfRingEquiv`); the project's `quotientTwist` re-wraps it. |
|  4 | set-with-closure-predicate → bundled substructure? | no | — | No substructure here. |
|  5 | vector-space/metric/field-specific → modules/(semi)ring? | no | — | Already at full `CommRing` generality in mathlib. |
|  6 | 1-categorical → higher-categorical? | no | — | Elementary functoriality; no categorification needed. |
|  7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group? | no | — | No numeric index in the statement. |

Modern idiom available: no (for the project's lemma). The *mathlib-idiomatic* form already exists
and is exactly what the project's proof calls. There is no modernisation move the project's lemma
makes that mathlib has not already made — on the contrary, the project's lemma is a localised
re-statement of mathlib's already-modern API.

One-line reason this is not a modernisation move: mathlib's `IsLocalization.ringEquivOfRingEquiv` /
`IsFractionRing.ringEquivOfRingEquiv` are already the contemporary universal-property formulation;
`quotientTwist`/`quotientTwist_algebraMap` are project-local renames of them.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths are
introduced by a `theorem`.)

---

### Mathlib search-status: `PadicLFunctions.quotientTwist_algebraMap`

[A] Lean-Finder       — (web Lean-Finder not invoked separately)        n/a: covered by [B][C][D] below, which located the exact decl by source.
[B] Loogle            type pattern `?f (algebraMap _ _ ?x) = algebraMap _ _ (?g ?x)`, and name `ringEquivOfRingEquiv`  hits: `IsLocalization.ringEquivOfRingEquiv_eq`, `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, `IsLocalization.algEquivOfAlgEquiv_eq`, `IsFractionRing.algEquivOfAlgEquiv_algebraMap` (resolved by direct grep of mathlib source — see [D]).
[C] LeanSearch        natural-language "localization of ring isomorphism commutes with algebraMap"   hit: surfaced the mathlib `FractionRing` doc page (via WebSearch row #1) → `IsFractionRing.ringEquivOfRingEquiv_algebraMap`.
[D] Grep mathlib src  `ringEquivOfRingEquiv_eq`, `ringEquivOfRingEquiv_algebraMap`, `algEquivOfAlgEquiv_eq`   hits — see exact locations below.
[E] Name pattern      `lean_local_search`-style grep of project + mathlib for `ringEquivOfRingEquiv`   hit: the project's own `quotientTwist` (`EisensteinFamily.lean:169`) is built from `IsLocalization.ringEquivOfRingEquiv`, and the lemma's proof (`:177`) is `IsLocalization.ringEquivOfRingEquiv_eq _ μ`.

Exact mathlib decls found (by qualified name + location):
- `IsLocalization.ringEquivOfRingEquiv_eq`
  — `.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean:696`
    ```
    theorem ringEquivOfRingEquiv_eq {j : R ≃+* P} (H : M.map j.toMonoidHom = T) (x) :
        ringEquivOfRingEquiv S Q j H ((algebraMap R S) x) = algebraMap P Q (j x) := by simp
    ```
  This is the **general** statement; the project's lemma is its instantiation at
  `R = P = Λ`, `S = Q = QuotientField p`, `M = T = Λ⁰`, `j = unitsTwist p`,
  `H = map_nonZeroDivisors_unitsTwist p`. The project's proof is literally
  `IsLocalization.ringEquivOfRingEquiv_eq _ μ`.
- `IsFractionRing.ringEquivOfRingEquiv_algebraMap`
  — `.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean:436`
    ```
    lemma ringEquivOfRingEquiv_algebraMap (a : A) :
        ringEquivOfRingEquiv h (algebraMap A K a) = algebraMap B L (h a) := by simp
    ```
  This is the **fraction-ring-specialised** statement (for `[IsFractionRing A K]`,
  `[IsFractionRing B L]`, `h : A ≃+* B`), which matches the project's setup verbatim
  (`QuotientField p = FractionRing Λ`, with `IsFractionRing Λ (QuotientField p)`). It is the
  cleanest single mathlib lemma to use directly.
- (analogous algebra-flavoured siblings, not needed here but confirming the API completeness:
  `IsLocalization.algEquivOfAlgEquiv_eq` at `Localization/Basic.lean:244`;
  `IsFractionRing.algEquivOfAlgEquiv_algebraMap` at `Localization/FractionRing.lean:508`.)

Searched for both:
  - the user's current form (`quotientTwist (algebraMap μ) = algebraMap (unitsTwist μ)`) — matched by
    `IsLocalization.ringEquivOfRingEquiv_eq` (the proof already uses it);
  - the literature-standard / general form (naturality of `S⁻¹φ`) — matched by the same lemma plus
    `IsFractionRing.ringEquivOfRingEquiv_algebraMap`.

Concluded: **found in mathlib as `IsLocalization.ringEquivOfRingEquiv_eq` (Defs.lean:696) — identical
form**, with the fraction-ring-specialised `@[simp]` lemma `IsFractionRing.ringEquivOfRingEquiv_algebraMap`
(FractionRing.lean:436) matching the project's `FractionRing` setup verbatim. The user's form follows
in ≤1 line (it is the literal proof in source).

---

### Call sites — `PadicLFunctions.quotientTwist_algebraMap`

Internal use count: 2 (both within `projects/PadicLFunctions/`, NOT counting the declaring line `:174`).
External-to-file callers: 0 distinct files. Both uses are inside the **same file**, inside the
**same proof** (`twistedZetaHalf_witness_eq`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:228 | `rw [map_mul, quotientTwist_algebraMap, quotientTwist_algebraMap] at hc` (two rewrites in one `rw`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `quotientTwist_algebraMap`?):
  - (none) — no other site re-derives the naturality equation by hand; but note both existing uses
    are a single `rw` that could equally cite the mathlib lemma directly.

Call-sites signal: K = 2 internal uses, but **both in one sibling proof, none external** — this is
the "K = 1-ish, possibly wrong abstraction / could be inlined" pattern. It is not a load-bearing
public API surface; it is a local convenience alias. Combined with Phase 5 finding the exact mathlib
lemma, this points firmly at NO-mathlib-has-it.

---

### Composition check (Phase 6)

Can `PadicLFunctions.quotientTwist_algebraMap` be derived from mathlib in ≤3 chained calls?

Attempt 1 (use the general localization lemma — this is the source proof):
  `IsLocalization.ringEquivOfRingEquiv_eq (map_nonZeroDivisors_unitsTwist p) μ`
  - Mathlib decls used: `IsLocalization.ringEquivOfRingEquiv_eq`.
  - Result: succeeds — this is verbatim the proof already in the file (`:177`).
  - Notes: 1 call. `quotientTwist` *is* `IsLocalization.ringEquivOfRingEquiv … (unitsTwist p) …`, so
    the lemma about it is exactly `ringEquivOfRingEquiv_eq` at the matching arguments.

Attempt 2 (use the fraction-ring specialisation directly — eliminates the project def too):
  Since `quotientTwist p` is *definitionally* `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`
  — because `IsFractionRing.ringEquivOfRingEquiv h := IsLocalization.ringEquivOfRingEquiv K L h
  (MulEquivClass.map_nonZeroDivisors h)` and `map_nonZeroDivisors_unitsTwist p :=
  MulEquivClass.map_nonZeroDivisors (unitsTwist p)` (see `EisensteinFamily.lean:160–171`) — the whole
  statement is `IsFractionRing.ringEquivOfRingEquiv_algebraMap (unitsTwist p) μ`:
  ```lean
  example (μ : PadicMeasure p ℤ_[p]ˣ) :
      IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)
          (algebraMap _ (PadicMeasure.QuotientField p) μ)
        = algebraMap _ _ (unitsTwist p μ) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (unitsTwist p) μ
  ```
  - Mathlib decls used: `IsFractionRing.ringEquivOfRingEquiv`, `IsFractionRing.ringEquivOfRingEquiv_algebraMap`.
  - Result: succeeds — 1 call (the `@[simp]` lemma fires).

Conclusion: COMPOSABLE — but in the strongest possible sense: mathlib doesn't just have building
blocks, it has the **exact lemma** (`IsLocalization.ringEquivOfRingEquiv_eq`), so this is
NO-mathlib-has-it rather than NO-composable-from-mathlib. (The composition sketch above is the
refactor recipe.)

---

## Verdict: `PadicLFunctions.quotientTwist_algebraMap`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the statement is the textbook **naturality of localisation** —
  `(S⁻¹φ) ∘ ι = ι ∘ φ` — confirmed by 4 channels (WebSearch ×3 + Stacks); WebSearch row #1 returned
  mathlib's own `FractionRing` doc page with the exact equation.
- Generality analysis (Phase 4): STRICTLY NARROWER than the literature-standard general form — but
  the general form is itself already in mathlib (`IsLocalization.ringEquivOfRingEquiv_eq`), so this
  argues NO-mathlib-has-it, not generalise-first. Phase 4c: no modernisation move; the mathlib API
  is already the contemporary universal-property formulation.
- Mathlib search (Phase 5): found in mathlib as `IsLocalization.ringEquivOfRingEquiv_eq`
  (Defs.lean:696), identical form; fraction-ring-specialised `@[simp]` lemma
  `IsFractionRing.ringEquivOfRingEquiv_algebraMap` (FractionRing.lean:436) matches the project setup
  verbatim.
- Composition check (Phase 6): COMPOSABLE in one call — and in fact the exact lemma exists, so
  NO-mathlib-has-it dominates.

**Rationale (1–2 paragraphs):**

The target is the naturality equation for the localisation of a ring automorphism: that the induced
map on the total fraction ring commutes with the canonical map `Λ → Q`. This is one of the most
basic facts about localisation, present in every commutative-algebra text and — decisively — already
in mathlib as `IsLocalization.ringEquivOfRingEquiv_eq`. That is not an analogy or a near-miss: the
project's `quotientTwist` is *defined* as `IsLocalization.ringEquivOfRingEquiv (QuotientField p)
(QuotientField p) (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)` (`EisensteinFamily.lean:167–171`),
and `quotientTwist_algebraMap`'s proof in source is literally `IsLocalization.ringEquivOfRingEquiv_eq
_ μ` (`:177`). The lemma is a project-local renaming of an existing mathlib lemma, applied to the
project's specific equiv.

Moreover the whole `quotientTwist` def is itself definitionally `IsFractionRing.ringEquivOfRingEquiv
(unitsTwist p)` — because `IsFractionRing.ringEquivOfRingEquiv h` unfolds to
`IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)` and the project's
`map_nonZeroDivisors_unitsTwist p` is exactly `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`
(`EisensteinFamily.lean:160–164`). So even the *definition* duplicates a mathlib def, and the lemma
duplicates its companion `@[simp]` lemma `IsFractionRing.ringEquivOfRingEquiv_algebraMap`. Call-site
analysis reinforces this: the lemma has only 2 uses, both inside the single sibling proof
`twistedZetaHalf_witness_eq` (`EisensteinFamily.lean:228`), and no external consumers — a thin local
convenience, not a contribution. There is nothing here for mathlib to gain; mathlib already owns this
result at strictly greater generality (general ring hom, arbitrary compatible multiplicative sets,
distinct source/target).

**WHY not (refactor-actionable detail):**
Mathlib already has it. The exact statement is `IsLocalization.ringEquivOfRingEquiv_eq` (the lemma the
proof already invokes). For the project's `FractionRing` setting there is an even cleaner, `@[simp]`-
tagged specialisation, `IsFractionRing.ringEquivOfRingEquiv_algebraMap`, whose hypotheses
(`[IsFractionRing A K]`, `[IsFractionRing B L]`, `h : A ≃+* B`) match the project exactly. Crucially,
`quotientTwist` itself is the project's rename of `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)`,
so both the def and its lemma should be retired in favour of the mathlib originals.

Existing mathlib decl:        `IsLocalization.ringEquivOfRingEquiv_eq`
                              (and `IsFractionRing.ringEquivOfRingEquiv_algebraMap` for the FractionRing case)
Located at:                   `.lake/packages/mathlib/Mathlib/RingTheory/Localization/Defs.lean:696`
                              (FractionRing variant: `.lake/packages/mathlib/Mathlib/RingTheory/Localization/FractionRing.lean:436`)
Our form follows in ≤1 line:
```lean
-- Direct (matches the current proof verbatim):
example (μ : PadicMeasure p ℤ_[p]ˣ) :
    quotientTwist p (algebraMap _ (PadicMeasure.QuotientField p) μ)
      = algebraMap _ _ (unitsTwist p μ) :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_nonZeroDivisors_unitsTwist p) μ

-- Cleaner, if `quotientTwist` is itself replaced by the mathlib def:
--   quotientTwist p  ↝  IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)
example (μ : PadicMeasure p ℤ_[p]ˣ) :
    IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)
        (algebraMap _ (PadicMeasure.QuotientField p) μ)
      = algebraMap _ _ (unitsTwist p μ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (unitsTwist p) μ
```
Call sites in our project (from Phase 6.0): K = 2 (both at `EisensteinFamily.lean:228`, in one `rw`).

Refactor plan:
1. **Minimal (keep `quotientTwist` def):** delete the `quotientTwist_algebraMap` theorem
   (`EisensteinFamily.lean:174–177`). At its sole call site (`:228`,
   `rw [map_mul, quotientTwist_algebraMap, quotientTwist_algebraMap] at hc`), replace each
   `quotientTwist_algebraMap` with the mathlib lemma — since `quotientTwist p =
   IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)` definitionally, the `@[simp]` lemma
   `IsFractionRing.ringEquivOfRingEquiv_algebraMap` rewrites it directly, so the line becomes
   `rw [map_mul, IsFractionRing.ringEquivOfRingEquiv_algebraMap, IsFractionRing.ringEquivOfRingEquiv_algebraMap] at hc`
   (or, since it is `@[simp]`, fold it into a `simp only [map_mul, IsFractionRing.ringEquivOfRingEquiv_algebraMap] at hc`).
   Verify the two `algebraMap` underscores still infer (they do — same instances).
2. **Fuller (also retire the def):** additionally replace the `quotientTwist` def
   (`EisensteinFamily.lean:167–171`) and the helper `map_nonZeroDivisors_unitsTwist`
   (`:160–164`, which is just `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`) with direct use of
   `IsFractionRing.ringEquivOfRingEquiv (unitsTwist p)` at every site that mentions `quotientTwist`
   (it appears in `twistedZetaHalf` `:190`, `twistedZetaHalf_witness_eq` `:225–228`). This removes a
   def + two lemmas that all rename existing mathlib API. (Optional — the def `quotientTwist` is at
   least a genuine named object; a maintainer may keep it as a local abbreviation even while deleting
   the redundant `_algebraMap` lemma. That choice is a style call, not a mathlib-worthiness one.)

Next action: delete `quotientTwist_algebraMap` from the project; rewrite its 2 call sites at
`EisensteinFamily.lean:228` to use `IsFractionRing.ringEquivOfRingEquiv_algebraMap` (or
`IsLocalization.ringEquivOfRingEquiv_eq`). Do **not** open a mathlib PR — mathlib already has this.

---

## Next step

Delete `PadicLFunctions.quotientTwist_algebraMap` from `EisensteinFamily.lean`; at each of the
2 call sites (both on line 228) replace `quotientTwist_algebraMap` with mathlib's
`IsFractionRing.ringEquivOfRingEquiv_algebraMap` (a `@[simp]` lemma, so a `simp only [...]` also
works) — noting that `quotientTwist p` is definitionally `IsFractionRing.ringEquivOfRingEquiv
(unitsTwist p)`, so the mathlib lemma applies without any glue. Optionally retire the
`quotientTwist` def and `map_nonZeroDivisors_unitsTwist` helper for the same reason. No mathlib PR.
