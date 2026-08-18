# /mathlibable report — `PadicMeasure.QuotientFieldPlus`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicMeasure.QuotientFieldPlus`
**Kind:** `abbrev` (noncomputable section)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:124`
**Date:** 2026-06-18

---

## FINAL VERDICT: `NO-mathlib-has-it`

> Mathlib already has the construction as `FractionRing` (`abbrev FractionRing R := Localization (nonZeroDivisors R)`, `Mathlib/RingTheory/Localization/FractionRing.lean:686`), whose own docstring names it the *total fraction ring*. The target **is** `FractionRing (PadicMeasure p (GPlus p))` — a zero-argument application — so the project alias unfolds to the mathlib decl in **0 lines**. It is project-local convenience notation, not new mathlib content.

---

## Phase 0 — Doctor / baseline

- **Build:** not re-run (worktree build is stale/slow per task instructions). **Reasoned from source** — read the declaration, its sibling, its type dependencies, and the mathlib `FractionRing` definition directly. The skill's Phase-0 fallback explicitly permits this.
- The declaration is sorry-free and references only existing, compiling definitions (`FractionRing`, `PadicMeasure`, `GPlus`). The sibling `QuotientField` (same shape) and all 9 internal call sites of `QuotientFieldPlus` are in the same compiling tree.

## Phase 1 — Comprehend

```lean
/-- The total fraction ring `Q(𝒢⁺)` of the Iwasawa algebra `Λ(𝒢⁺)`. -/
abbrev QuotientFieldPlus := FractionRing (PadicMeasure p (GPlus p))
```

with `variable (p : ℕ) [hp : Fact p.Prime]`.

**Dependency unfolding:**
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`) — the `ℤ_[p]`-valued measures on `X`.
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)` (`Iwasawa/PlusPart.lean:215`) — the plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}`.
- `PadicMeasure p (GPlus p)` carries the convolution `CommRing` structure (general `instance : CommRing (PadicMeasure p G)` for any compact commutative topological monoid `G`, `Measure/PseudoMeasure.lean:81`) — i.e. the Iwasawa algebra `Λ(𝒢⁺)`.
- `FractionRing R := Localization (nonZeroDivisors R)` (mathlib) — the total ring of fractions.

So `QuotientFieldPlus p` is **definitionally** the total ring of fractions `Q(𝒢⁺) = Frac(Λ(𝒢⁺))`. Mathematically this is the Serre/Coates ambient ring in which pseudo-measures (and the descended `ζ_p⁺`) live. It is the exact analogue of the sibling `QuotientField := FractionRing (PadicMeasure p ℤ_[p]ˣ)` (`Measure/PseudoMeasure.lean:804`), just with the group `ℤ_[p]ˣ` replaced by `GPlus p`.

## Phase 2 — Preliminary BIG/SMALL + one-line check

- **SMALL.** A one-line `abbrev` that is a single, zero-argument application of an existing mathlib constructor to a specific ring.
- **One-line / defeq-abuse exemption:** does NOT apply. The exemptions cover defs that exist to *avoid* a diamond or stabilise an API across a defeq. This abbrev declares **no instance** and introduces no new defeq surface; it is plain notation for `FractionRing (…)`. The sibling `toQPlus` (a named `algebraMap`) carries the elaboration-order note, not `QuotientFieldPlus` itself.
- Preliminary lean: SMALL + trivial application ⟹ strong prior toward NO-mathlib-has-it; proceed to confirm via literature + mathlib search.

## Phase 3 — EXHAUSTIVE literature search (9 channels)

| # | Channel | Query / target | Result |
|---|---|---|---|
| 1 | WebSearch | "total ring of fractions / total quotient ring of a commutative ring definition" | **HIT.** Total quotient ring = localization of `R` at its regular (non-zero-divisor) elements; standard generalisation of the fraction field to rings with zero divisors. (Wikipedia, ProofWiki, PlanetMath, HandWiki.) |
| 2 | WebSearch | "pseudo-measure Iwasawa algebra total ring of fractions Q(G) Coates Lichtenbaum p-adic L-function" | **HIT.** `Q(G)` = fraction ring of the Iwasawa algebra `Λ(G)`; a pseudo-measure is `φ ∈ Q(G)` with `(σ−1)φ ∈ Λ(G)` for all `σ` (Serre). Coates/Wiles/Coates–Lichtenbaum framework. (Coates–Sujatha; Williams notes; arXiv:0711.0581.) |
| 3 | WebSearch | "Iwasawa algebra Λ(G) localization nonzerodivisors fraction ring zeta pseudomeasure" | **HIT.** `Λ(G)` is the p-adic group-algebra inverse limit; fraction ring obtained by localizing at (Ore set of) non-zero-divisors. (Wikipedia "Iwasawa algebra"; Sharifi notes; arXiv:math/0311446.) |
| 4 | nLab / nCatLab | "total quotient ring localization nonzerodivisors" | **HIT.** Total ring of fractions `S⁻¹R`, `S` = non-zero-divisors; natural map `R → S⁻¹R` injective; every element a zero-divisor or a unit. (ncatlab noncommutative-localization; standard refs.) |
| 5 | Stacks Project | tag 02C5 (`WebFetch`) | **HIT, verbatim.** Example 10.9.8: *"Let `S = {f ∈ A ∣ f is not a zerodivisor in A}`. … the ring `Q(A) = S⁻¹A` is called either the total quotient ring, or the total ring of fractions of `A`."* |
| 6 | MathOverflow / Math.SE | (covered by channels 1–5 result sets; total-quotient-ring is textbook, no contested MO thread needed) | n/a-as-search: concept is uncontested textbook material; no open question to resolve. |
| 7 | arXiv | pseudomeasures / Iwasawa fraction ring (arXiv:0711.0581, math/0311446, 0802.2272 surfaced in channels 2–3) | **HIT.** `Q(G)`/`Λ(G)_S` is the standard object across noncommutative + classical Iwasawa theory. |
| 8 | Local refs (`refs/PadicLFunctions/`) | RJW arXiv:2309.15692 (the project's source) | `n/a`: `refs/` is not symlinked in this worktree (local-only PDFs). The in-file docstrings cite **RJW Def. 3.34** ("let `Q(G)` denote the ring of fractions") and **§11.1/§11.2, TeX 3033–3059** for the `𝒢⁺` descent — the source's own term for this object is exactly "ring of fractions of `Λ(G)`". |
| 9 | ChatGPT MCP (historical-formulation question) | — | `n/a`: Codex/ChatGPT MCP not installed in this environment (`codex not found`, no `.mcp.json`). Literature channels 1–7 already settle the historical formulation: Serre (1978, "Sur le résidu de la fonction zêta p-adique") introduced pseudo-measures in `Q(G) = Frac Λ(G)`; the formulation has been standard ever since. |

**Phase 3 conclusion (literature-standard form):** The object is the **total ring of fractions `Q(R) = Frac(R)` of a commutative ring `R`** (Stacks 02C5; Serre/Coates in the Iwasawa specialisation). The literature-standard form is *maximally general in the ring* — it is defined for an arbitrary commutative ring, and the Iwasawa usage is the instance `R = Λ(G)`. The target's form (`R = Λ(𝒢⁺)`) is a **specific instance** of that general object, not a general statement about it.

## Phase 4 — Generality analysis vs literature

The literature-standard object `Frac(R)` is defined for **any** commutative ring `R`. The target fixes `R := PadicMeasure p (GPlus p)`, a single concrete ring. Hence the target is a **maximally-specialised instance** of the general construction — it is not "a narrower theorem about fraction rings", it is "the fraction ring of one particular ring". There is no weakening axis to pursue on the target itself: the only generalisation is "take `Frac` of an arbitrary ring", which is precisely the mathlib decl `FractionRing`. So this is not a `YES-but-generalise-first` situation — the general form is not a missing target, it already exists in mathlib (Phase 5).

### Phase 4c — Modern-mathlib-idiom restatement (Bourbaki 2.0 check)

Is there a contemporary mathlib re-statement of *this object* with real downstream consequences? **No.** The modern-idiom form of "total ring of fractions of `R`" already IS the mathlib idiom: the bundled `FractionRing R` type together with the `IsFractionRing R K` typeclass / universal property (`Mathlib/RingTheory/Localization/FractionRing.lean`). The project is already on the modern idiom — it uses `FractionRing`, `IsFractionRing.injective`, `IsLocalization.mk'`, `IsLocalization.map_units`, and `algebraMap … (FractionRing …)`. There is no further modernisation move available; naming the specific instance `QuotientFieldPlus` is, if anything, slightly *less* idiomatic than mathlib's own habit of inlining `let K := FractionRing A` (dozens of mathlib sites do exactly this, e.g. `NumberField/ExistsRamified.lean:55`, `FieldTheory/KummerExtension.lean:89`). No downstream consequence supports promoting the alias.

## Phase 5 — Diamond / defeq risk (def/abbrev)

- `QuotientFieldPlus` is an `abbrev` that **declares no instances** and adds no fields. It transparently inherits the full `FractionRing` instance tower (`Field`, `CommRing`, `Algebra R (FractionRing R)`, `IsFractionRing`, …). Because nothing new is registered, there is **no diamond and no defeq hazard**: any instance resolved through `QuotientFieldPlus p` is *the same* instance resolved through `FractionRing (PadicMeasure p (GPlus p))`.
- The required `CommRing (PadicMeasure p (GPlus p))` comes from the project's general `instance : CommRing (PadicMeasure p G)` (compact commutative topological monoid `G`), independent of this alias.
- **Diamond/defeq risk: NONE.**

## Phase 5 (search) — Mathlib five-method search

Searched on (a) the user's form, (b) the literature-standard form "total ring of fractions of a commutative ring", and (c) the modern-idiom form.

| Method | Query | Result |
|---|---|---|
| A — Lean-Finder (AI) | "total ring of fractions of a commutative ring", "field of fractions localization at non zero divisors" | **HIT** → `FractionRing` / `IsFractionRing`. (Type/NL search; surfaced as canonical answer.) |
| B — Loogle (type pattern) | `Localization (nonZeroDivisors _)` ; `IsFractionRing _ _` | **HIT** → `FractionRing R := Localization (nonZeroDivisors R)`; `IsFractionRing R K`. |
| C — LeanSearch (NL) | "total quotient ring of a commutative ring", "fraction ring of a ring with zero divisors" | **HIT** → `FractionRing`, with docstring "also known as the total fraction ring of R". |
| D — Grep mathlib source | `grep -rn "^abbrev FractionRing" .lake/packages/mathlib/…` and `:= FractionRing ` usages | **HIT** → `Mathlib/RingTheory/Localization/FractionRing.lean:686`; dozens of `let K := FractionRing A` instance sites (mathlib's own idiom is to inline, not to alias). |
| E — Name-pattern (local search) | `FractionRing`, `totalFractionRing`, `TotalFractionRing`, `totalQuotient`, `QuotientField` | `FractionRing` present and canonical; **no** `totalFractionRing`/`TotalFractionRing`/`totalQuotient` named alias exists in mathlib — confirming mathlib does NOT introduce a separate name for the total-fraction-ring instance, it just applies `FractionRing`. |

**Phase 5 conclusion:** Mathlib has the exact construction as `FractionRing`
(`Mathlib/RingTheory/Localization/FractionRing.lean:686`):

```lean
/-- ... In this generality, this construction is also known as the *total fraction ring* of `R`. -/
abbrev FractionRing := Localization (nonZeroDivisors R)
```

This is identical (definitionally) to the target after substituting `R := PadicMeasure p (GPlus p)`.

**Follows-in-≤1-line derivation (the NO-mathlib-has-it gate):**

```lean
example : PadicMeasure.QuotientFieldPlus p = FractionRing (PadicMeasure p (GPlus p)) := rfl
```

(`QuotientFieldPlus p` is *defined as* the RHS; the derivation is 0 work — it is `rfl`.) Anywhere a `QuotientFieldPlus p` value/type is wanted, `FractionRing (PadicMeasure p (GPlus p))` is interchangeable with no glue.

## Phase 6 — Composition check (and call-sites signal)

- **Composition:** trivially COMPOSABLE in the strongest sense — it is not even a composition, it is one application: `FractionRing (PadicMeasure p (GPlus p))`. 1 mathlib call, ≤3. No rewriting/automation needed.
- **Call-sites signal (`grep QuotientFieldPlus`):** 9 internal uses, ALL within `Iwasawa/ZetaGalois.lean` (`toQPlus`, `IsPlusPseudoMeasure`, `padicZetaPlus`, the `IsLocalization.mk'` / `IsLocalization.map_units` / `IsFractionRing.injective` calls). Zero external consumers. This is a **single-file convenience alias** — exactly the profile of "notation that should not be promoted to mathlib": consumers outside the file would write `FractionRing (PadicMeasure p (GPlus p))` (or `let K := …`) directly, per mathlib's own idiom.

## Phase 7 — Verdict synthesis (gate)

- Phase 3 (≥3 + Stacks-verbatim + arXiv): the object is the **classical total ring of fractions**, general in the ring; the Iwasawa `Q(𝒢⁺)` is the instance `R = Λ(𝒢⁺)`.
- Phase 4: target is a maximally-*specialised* instance, not a narrower theorem; no weakening axis on the target. Phase 4c: already on the mathlib idiom; no modernisation move with downstream consequences.
- Phase 5 (five methods, all attempted): mathlib has the general construction as `FractionRing`; the target is `rfl`-equal to it; no separate mathlib alias exists for the specific instance (mathlib inlines it).
- Phase 6: it is a 1-call application with zero external consumers.

These all point to one bucket. The target is not novel content; mathlib's `FractionRing` *is* it. The project-local `abbrev` is justified **as project notation** (mirrors `QuotientField`, keeps `Q(𝒢⁺)` readable), but it does not belong in mathlib — mathlib would not add a named alias for `FractionRing (PadicMeasure p (GPlus p))` any more than it added one for `FractionRing (MvPolynomial ι F)`.

- Not `YES-add-as-is` (no novel content; Phase 5 found the exact thing).
- Not `YES-but-generalise-first` (the generalisation IS the existing mathlib `FractionRing`; nothing to PR).
- Not `NO-composable-from-mathlib` (it is not even a composition — it is a single direct application; and `NO-mathlib-has-it` is the more precise bucket since mathlib has the construction *by name*).
- Not `BORDERLINE` (no judgment call; all phases resolve cleanly and agree).

**Verdict: `NO-mathlib-has-it`.**

## Phase 8 — Report (this document)

**Existing mathlib decl:** `FractionRing` — `abbrev FractionRing (R) [CommRing R] := Localization (nonZeroDivisors R)`, `Mathlib/RingTheory/Localization/FractionRing.lean:686` (docstring: "also known as the *total fraction ring* of `R`"). Universal-property interface: `IsFractionRing` (same file, line 53).

**Derivation (0 lines):**
```lean
example : PadicMeasure.QuotientFieldPlus p = FractionRing (PadicMeasure p (GPlus p)) := rfl
```

**Recommended action (project-local, NOT a mathlib PR):**
- Keep `QuotientFieldPlus` as project-local notation if desired (it mirrors `QuotientField` and reads as `Q(𝒢⁺)`), **OR** inline `FractionRing (PadicMeasure p (GPlus p))` at its 9 call sites per mathlib's own `let K := FractionRing …` idiom. Either is fine for the project; neither is a mathlib contribution.
- Do **not** open a mathlib PR for this declaration. If anything from this corner is mathlib-bound, it is the *new mathematics* (the convolution `CommRing` on `PadicMeasure p G`, the pseudo-measure theory, the `𝒢⁺` descent) — assessed separately — not the fraction-ring alias.

**Note for the sibling:** `PadicMeasure.QuotientField` (`Measure/PseudoMeasure.lean:804`) is the identical pattern (`FractionRing (PadicMeasure p ℤ_[p]ˣ)`) and gets the **same** `NO-mathlib-has-it` verdict by the same argument.

---

### Five-bucket verdict (final): **`NO-mathlib-has-it`**
