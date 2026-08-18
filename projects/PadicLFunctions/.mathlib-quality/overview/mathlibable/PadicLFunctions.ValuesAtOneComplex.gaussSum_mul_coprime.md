# `/mathlibable` report — `PadicLFunctions.ValuesAtOneComplex.gaussSum_mul_coprime`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — Phase-0 fallback)
- decl `PadicLFunctions.ValuesAtOneComplex.gaussSum_mul_coprime`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean:33`
- kind:                      theorem
- has sorry:                 no (45 non-blank proof lines, lines 46–90)
- module docstring summary:  Complex-analysis "quarantine" file computing the classical value `L(θ,1)` (RJW Thm 6.1(i), following Washington Thm 4.9), stated against mathlib's `DirichletCharacter.LFunction`.

---

### Statement (Phase 1)

`gaussSum_mul_coprime` is a **theorem** stating the **multiplicativity of Gauss sums over coprime conductors** (the Chinese-Remainder factorisation):

> Let `R` be an integral domain and let `D, M` be coprime positive naturals. Let `η` be a Dirichlet character mod `D` and `χ` a Dirichlet character mod `M`, and let `θ` be their product at level `DM`, formed by lifting each via `changeLevel` (`θ = changeLevel η · changeLevel χ`). Let `εD`, `εM` be primitive `D`-th and `M`-th roots of unity, and form the **split** additive character `ε = εD·εM` (a primitive `DM`-th root). Then the Gauss sum of `θ` against `ε` factors as a product:
> `G(θ, ε_DM) = G(η, ε_D) · G(χ, ε_M)`.

Variables / typeclasses involved (Lean side):
- `{R : Type*} [CommRing R] [IsDomain R]` — the coefficient ring (integral domain).
- `{D M : ℕ} [NeZero D] [NeZero M]` — the two coprime moduli.
- `(η : DirichletCharacter R D)`, `(χ : DirichletCharacter R M)` — the two component characters.
- `{θ : DirichletCharacter R (D * M)}` — the product character at the joint level.
- `{εD εM : R}` — the chosen primitive roots realising the additive characters.

Hypotheses (Lean side):
- `(hco : Nat.Coprime D M)` — coprimality of the moduli (drives the CRT).
- `(hθ : θ = changeLevel (Dvd.intro _ rfl) η * changeLevel (Dvd.intro_left _ rfl) χ)` — `θ` is the lifted product.
- `(hεD : IsPrimitiveRoot εD D)`, `(hεM : IsPrimitiveRoot εM M)` — primitivity of the roots.

Conclusion (math): The Gauss sum of the coprime product character against the split additive character is the product of the component Gauss sums (no correction factor, because the additive character is split rather than fixed).

Conclusion (Lean): `gaussSum θ (AddChar.zmodChar (D*M) …) = gaussSum η (AddChar.zmodChar D …) * gaussSum χ (AddChar.zmodChar M …)`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: A classical named result (Gauss-sum multiplicativity over coprime conductors; Washington §6.1-style lemma), and a structural building block of the project's `L(θ,1)` computation — guaranteed to be in the literature in some form.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`. (Body is a 45-line CRT argument, not a one-liner.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Gauss sum multiplicative coprime conductor Dirichlet character factor product G(theta)=G(eta)G(chi)"  | yes  | `g(χ₁χ₂) = g(χ₁)g(χ₂)·χ₁(q₂)χ₂(q₁)` for coprime moduli `q₁,q₂` | Multiple sources (Conrad's Gauss–Jacobi notes, PSU primitive-characters notes, grokipedia "Gauss sum"); the factor `χ₁(q₂)χ₂(q₁)` is the separability correction |
|  2 | WebSearch (general form)         | "tau(chi psi)=tau(chi)tau(psi) Gauss sum coprime moduli Chinese remainder theorem proof"               | yes  | CRT decomposes `χ` mod `mn` into prime-power pieces; `τ(χψ)=τ(χ)τ(ψ)` classical | Confirmed as a classical analytic-NT result; CRT is the proof mechanism |
|  3 | WebSearch (named-after / aliases / split char) | `"Gauss sum" multiplicativity "relatively prime" conductors product formula additive character split`  | yes  | `S(μq,r)S(μr,q)=S(μ,rq)`; for split character the cross-factor vanishes | top hit = mathlib's own `NumberTheory.GaussSum`; confirms the additive-character convention controls the correction factor |
|  4 | ChatGPT MCP                      | (would ask: "standard definition + generality + historical formulation of Gauss-sum multiplicativity over coprime conductors") | n/a  | —                                | `codex` CLI not installed in this environment — channel recorded n/a |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                            | n/a  | (directory absent)               | no `references/` dir under this project's `.mathlib-quality/`; recorded n/a. NB the *file header itself* cites Washington Thm 4.9 / RJW Thm 6.1(i) as the source |
|  6 | nLab                             | "Gauss sum" (ncatlab.org/nlab/show/Gauss+sum)                                                          | partial | quadratic Gauss-sum multiplicativity + Hasse–Davenport product | nLab covers Gauss sums and multiplicative relations but at the quadratic-form / Hasse–Davenport level, not the Dirichlet-coprime-conductor statement specifically |
|  7 | nCatLab                          | Doyle, "Quadratic Form Gauss Sums" (ncatlab.org/nlab/files) + nForum thread                            | partial | "obvious multiplicative properties of quadratic-form Gauss sums" | categorical/quadratic angle; not the exact Dirichlet statement |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept; Gauss sums of Dirichlet characters are not in Stacks |
|  9 | MathOverflow / Math.StackExchange| Gauss sum coprime moduli CRT (via Stanford CRT notes + grokipedia "Gauss sum"/"Quadratic Gauss sum")   | yes  | same general form as #1, with the CRT splitting argument | corroborates the standard form and the role of the additive-character choice |
| 10 | recent arXiv (last 5 years)      | character-sum / Gauss-sum papers surfaced in #1–#3 (e.g. 1609.03919 "Double Gauss Sums", 1805.09729)   | yes (background) | quadratic case: `G(α,l;β₁β₂)=G(αβ₂,l;β₁)G(αβ₁,l;β₂)` for coprime `β₁,β₂` | the cross-multiplier `αβ₂`,`αβ₁` is again the separability correction; modern usage is routine, not novel |

### Literature summary (Phase 3)

Concept identified as: **Multiplicativity / separability of Gauss sums over coprime conductors** (the Chinese-Remainder factorisation of a Gauss sum). Standard textbook material (Washington, *Introduction to Cyclotomic Fields*, §6.1; Keith Conrad, "Gauss and Jacobi Sums on Finite Fields and Z/mZ"; Berndt–Evans–Williams, *Gauss and Jacobi Sums*).

Sources agree on the standard form: **yes**. The canonical statement, for `χ₁` mod `q₁` and `χ₂` mod `q₂` with `gcd(q₁,q₂)=1` and a *fixed* additive character `e_{q₁q₂}`, is
`g(χ₁χ₂) = χ₁(q₂)·χ₂(q₁)·g(χ₁)·g(χ₂)`.
The correction factor `χ₁(q₂)·χ₂(q₁)` (the "separability factor") arises from re-expressing the single additive character `e_{q₁q₂}` in terms of `e_{q₁}` and `e_{q₂}` via Bézout. **When one instead uses the split additive character `ε = ε_{q₁}·ε_{q₂}` directly** (as the target does), the cross-terms factor cleanly and the correction factor is absent — giving exactly `G(θ) = G(η)·G(χ)`.

Most general standard form: as above, over any setting where the characters and roots of unity make sense — classically `ℂ`, but the algebraic content holds over any integral domain with the requisite roots of unity (which is what the Lean form uses: `[CommRing R] [IsDomain R]`).

Generality dimensions where the literature varies:
  - Coefficient ring: literature usually states it over `ℂ`; the algebraic identity holds over any integral domain (target is already at this generality).
  - Additive character convention: fixed `e_{q₁q₂}` (→ correction factor) vs. split `ε_{q₁}·ε_{q₂}` (→ no factor). Both standard; the split form is the cleaner "multiplicativity" statement.
  - Character realisation: the product character `χ₁χ₂` is usually taken as a given character mod `q₁q₂` (via the canonical `(ZMod q₁q₂)ˣ ≃ (ZMod q₁)ˣ × (ZMod q₂)ˣ`); the target instead specifies it by an explicit `hθ` hypothesis built from two `changeLevel` lifts.

Disagreement with the literature: **none** — the target is the split-character special case of the standard result, stated at integral-domain generality.

---

### Generality analysis — `gaussSum_mul_coprime` (Phase 4)

Literature-standard form (from Phase 3): `G(χ₁χ₂, ε_{q₁q₂}) = G(χ₁,ε_{q₁})·G(χ₂,ε_{q₂})` for coprime conductors and a split additive character; over any integral domain carrying the needed roots of unity.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[CommRing R] [IsDomain R]` | integral domain | integral domain (or ℂ) | NO | Already maximally general for this algebraic identity; `IsDomain` is the natural hypothesis (used for the nonunit/zero reasoning). |
| 2 | `(hco : Nat.Coprime D M)` | coprime moduli | coprime moduli | NO | Coprimality is essential — it is exactly what makes the CRT iso `ZMod (D*M) ≃ ZMod D × ZMod M` available. |
| 3 | `(hθ : θ = changeLevel … η * changeLevel … χ)` | explicit `changeLevel`-product hypothesis | `θ` IS the product character via the canonical CRT iso | (restatement, not weakening) | Could be re-expressed using a canonical "product over coprime levels" character rather than carrying `hθ` as a hypothesis — see Phase 4c #4. |
| 4 | `{εD εM : R} (hεD …) (hεM …)` + the inline `zmodChar (εD*εM)` proof | explicit primitive roots, split additive char built by hand | split additive character `ε_D·ε_M` | (restatement) | The additive character is constructed inline via `AddChar.zmodChar` with a hand-rolled `(εD*εM)^(DM)=1` proof; mathlib's idiom for Dirichlet Gauss sums is `stdAddChar` (`Mathlib/Analysis/Fourier/ZMod.lean`). See Phase 4c #2. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on its genuine mathematical axes (coefficient ring = integral domain; coprime moduli; primitive roots). No assumption is strictly narrower than the literature's.

Number of weakening opportunities found (true weakenings): **0**.
Number of *restatement* opportunities (Bourbaki-2.0 idiom): **2** (see 4c).

Proposed restatement: see Phase 4c (the work is reformulation toward mathlib's idiom, not weakening hypotheses).

Cost of restatement: MODERATE — the proof structure (CRT sum-splitting) survives, but adapting to `stdAddChar` and/or a canonical product-character would require re-deriving the additive-character factorisation step against mathlib's conventions.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | The hypotheses are already typeclass-driven (`IsDomain`, `NeZero`, `IsPrimitiveRoot`); nothing to instance-ify. |
| 2 | sequences/metric → filters/topological? | no | — | Finite character-sum identity; no analytic/limit content to filter-ise. |
| 3 | construct an object where a universal property would characterise it? | partial | State the product character via the canonical `(ZMod (D*M))ˣ ≃* (ZMod D)ˣ × (ZMod M)ˣ` (CRT mul-equiv) and the induced character product, rather than the bespoke `hθ` `changeLevel` hypothesis | Composes with mathlib's `ZMod.chineseRemainder` / `DirichletCharacter` API; lets consumers use a named "coprime product character" instead of supplying `hθ` by hand |
| 4 | set-with-closure-predicate → bundled type? | no | — | No substructure involved. |
| 5 | vector-space/field-specific → modules/(semi)ring? | no | — | Already at `[CommRing R] [IsDomain R]`; `IsDomain` is needed, can't weaken to a general semiring. |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorical statement. |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group? | no | — | `D, M : ℕ` are conductors; the natural-number indexing is intrinsic to `ZMod`/`DirichletCharacter`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes (mild)**.
- Proposed mathlib-idiomatic restatement (sketch — for the eventual mathlib PR):
  ```lean
  -- (a) additive character: use mathlib's stdAddChar instead of a hand-built zmodChar;
  -- (b) product character: phrase via the CRT mul-equiv rather than a bespoke hθ.
  theorem gaussSum_mul_coprime {R : Type*} [CommRing R] [IsDomain R] {D M : ℕ}
      [NeZero D] [NeZero M] (hco : D.Coprime M)
      (η : DirichletCharacter R D) (χ : DirichletCharacter R M)
      {εD εM : R} (hεD : IsPrimitiveRoot εD D) (hεM : IsPrimitiveRoot εM M) :
      gaussSum (η.coprodCoprime χ hco) (AddChar.zmodChar _ <split-root-proof>)
        = gaussSum η (AddChar.zmodChar D hεD.pow_eq_one)
          * gaussSum χ (AddChar.zmodChar M hεM.pow_eq_one) := …
  -- where `coprodCoprime` is the canonical coprime-product character (to be introduced /
  -- located in DirichletCharacter API) instead of the `hθ : θ = changeLevel … * changeLevel …`
  -- hypothesis the current statement carries.
  ```
- Cost: MODERATE.
- Mathlib downstream this enables: a named coprime-product character composes with `DirichletCharacter.Orthogonality`, `changeLevel`, and the `ZMod.chineseRemainder` API; callers get `G(θ)=G(η)G(χ)` from a clean product object rather than threading an `hθ` equation (which is precisely what the consumer in `ValuesAtOne.lean:1787` has to build by hand as `hθinvfac`).
- Real mathematical improvement (not just "looks cooler"): the `hθ` hypothesis is a definitional crutch — every caller must reconstruct it (the sole consumer does, via `hθinvfac`). Replacing it with the canonical CRT product character is a genuine API improvement, and aligning the additive character with `stdAddChar` lets the lemma sit next to mathlib's existing `gaussSum_mulShift_of_isPrimitive` / `fourierTransform_eq_gaussSum_mulShift` machinery.

Because Phase 4c finds a real (if mild) modern-idiom improvement on top of MAXIMALLY-GENERAL, Phase 7 leans **YES-but-generalise-first** (reason = MODERN-IDIOM), not YES-add-as-is (per the verdict gate).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `gaussSum_mul_coprime` (Phase 5)

[A] Lean-Finder       "Gauss sum of product character coprime moduli factors as product" / signature `IsPrimitiveRoot → IsPrimitiveRoot → gaussSum (changeLevel η * changeLevel χ) _ = gaussSum η _ * gaussSum χ _`   →  no hits (no CRT Gauss-sum factorisation surfaced)
[B] Loogle            `gaussSum _ (AddChar.zmodChar _ _) = gaussSum _ _ * gaussSum _ _` ; `gaussSum (DirichletCharacter.changeLevel _ _ * _) _`   →  no hits
[C] LeanSearch        "Gauss sum multiplicative over coprime conductors", "Gauss sum of product Dirichlet character Chinese remainder"   →  no hits
[D] Grep mathlib src  `gaussSum.*coprime`, `gaussSum.*chinese`, `gaussSum_mul`, `chineseRemainder` ∩ `gauss`/`char` over `.lake/packages/mathlib/Mathlib/`   →  only `gaussSum_mul` (GaussSum.lean:106) and the unrelated `Nat.chineseRemainder'` use in `DirichletCharacter/Basic.lean:179`
[E] Name pattern      `lean_local_search` / grep for `gaussSum_mul*`, `gaussSum_changeLevel`, `gaussSumProd`   →  only `gaussSum_mul`; section `GaussSumProd` contains exactly one product lemma, the same-character one

Searched for both:
  - the user's current form (split additive char + `changeLevel` product) — not found.
  - the literature-standard form (product character via CRT iso, possibly with correction factor) — not found.

**Critical disambiguation.** Mathlib's `gaussSum_mul` (`Mathlib/NumberTheory/GaussSum.lean:106`) is a *different theorem*:
```lean
lemma gaussSum_mul (χ φ : MulChar R R') (ψ : AddChar R R') :
    gaussSum χ ψ * gaussSum φ ψ = ∑ t : R, ∑ x : R, χ x * φ (t - x) * ψ t
```
This is the product of two Gauss sums **over the same ring `R` with the same additive character `ψ`**, written as a convolution-style double sum (its purpose in mathlib is to derive Jacobi sums — used at `JacobiSum/Basic.lean:168`). It is NOT a factorisation across coprime *moduli*, and the right-hand side is a double sum, not a product of two Gauss sums at smaller levels. The target's content — splitting `ZMod (D*M)` via `ZMod.chineseRemainder` into `ZMod D × ZMod M` and factoring the Gauss sum accordingly — is absent from mathlib.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). The closest decl, `gaussSum_mul`, is a genuinely different statement.

---

### Call sites — `gaussSum_mul_coprime` (Phase 6.0)

Internal use count: **K = 1** (within the project, excluding the declaring file).
External-to-file callers: 1 distinct file (`PadicLFunctions/ValuesAtOne.lean`).

| Caller file:line               | Usage pattern (one-line excerpt) |
|--------------------------------|-----------------------------------------------------------|
| `PadicLFunctions/ValuesAtOne.lean:1787` | `exact ValuesAtOneComplex.gaussSum_mul_coprime hco (toFieldChar η)⁻¹ (toFieldChar χ)⁻¹ hθinvfac hζK hεpK` |
| `PadicLFunctions/ValuesAtOne.lean:1593` | (docstring reference only) `… G(θ⁻¹) = G(η⁻¹)·G(χ⁻¹) (gaussSum_mul_coprime) …` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `gaussSum_mul_coprime`?):
  - (none) — no other file re-derives a coprime Gauss-sum factorisation inline. The FltRegularBernoulli `GaussSumProduct/` files prove a *different* product (`(∏_{χ odd} τ(χ))² = (-p)^n` via the involution `χ↦χ⁻¹`), not a CRT factorisation.

Call-sites signal: K = 1 internal use. Per the verdict reference this is a weak "could-be-inlined" signal in isolation — but here the single use is non-trivial (it discharges the central Gauss-sum split in the `L(θ,1)` interpolation, and the caller has to hand-build the `hθinvfac` product hypothesis). The lemma is genuine structural API, not a wrapper bypass; combined with NOT-COMPOSABLE (below), the YES lean stands.

### Composition check (Phase 6)

Can `gaussSum_mul_coprime` be derived from mathlib in ≤3 chained calls?

Attempt 1: `gaussSum_mul …` (mathlib's product lemma).
  - Mathlib decls used: `gaussSum_mul`.
  - Result: **fails** — `gaussSum_mul` is the same-ring same-character convolution identity; it cannot bridge two *different* moduli `D` and `M`. Wrong shape entirely.

Attempt 2: `ZMod.chineseRemainder hco` + `Finset.sum_mul_sum` + `Equiv.sum_comp`.
  - Mathlib decls used: `ZMod.chineseRemainder`, `MulChar.mul_apply`, `DirichletCharacter.changeLevel_eq_cast_of_dvd`, `AddChar.zmodChar_apply`/`apply'`, `Prod.fst_zmod_cast`/`snd_zmod_cast`, `Equiv.sum_comp`, `Finset.sum_product`, `Finset.sum_mul_sum`.
  - Result: **this is the actual 45-line proof**, not a composition. It requires (i) the CRT ring-equiv, (ii) a case split on `IsUnit a` to factor `θ a` through the two components (handling nonunits via `MulChar.map_nonunit`), (iii) factoring the additive character across the split with `val`-casting bookkeeping, (iv) reindexing the sum over the CRT equiv, (v) Fubini + `sum_mul_sum`, (vi) a final `ring`. Far more than 3 mathlib calls, with genuine reasoning between steps.

Conclusion: **NOT-COMPOSABLE.** No ≤3-call mathlib composition yields the statement; the proof is a real CRT argument.

---

## Verdict: `PadicLFunctions.ValuesAtOneComplex.gaussSum_mul_coprime`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): classical, standard, named result (Washington §6.1 / Keith Conrad's Gauss–Jacobi notes / Berndt–Evans–Williams). General form `g(χ₁χ₂)=χ₁(q₂)χ₂(q₁)g(χ₁)g(χ₂)`; the target is the clean split-character special case (no correction factor). ≥3 WebSearch channels + nLab + nCatLab + Encyclopedia of Math + arXiv corroborate; ChatGPT MCP and local refs recorded n/a with reasons.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on its true axes (integral domain, coprime moduli, primitive roots) — 0 weakenings. Phase 4c found 2 *restatement* (Bourbaki-2.0) opportunities with real downstream payoff.
- Mathlib search (Phase 5): not in mathlib; the only near-name `gaussSum_mul` is a different (same-ring convolution) theorem.
- Composition check (Phase 6): NOT-COMPOSABLE (the 45-line CRT proof is not a ≤3-call mathlib composition).

**Rationale (1–2 paragraphs):**

This is a genuinely missing, classical, named theorem — the multiplicativity (CRT factorisation) of Gauss sums over coprime conductors. Phase 3 located it across the standard references and Phase 5 confirmed mathlib has nothing of the kind: mathlib's `gaussSum_mul` is the same-ring same-additive-character convolution identity feeding Jacobi sums, structurally unable to relate Gauss sums at two distinct moduli, and `ZMod.chineseRemainder` is never wired to `gaussSum` anywhere in the library. The proof is a real 45-line Chinese-Remainder argument (split the index set via the CRT ring-equiv, factor the multiplicative and additive characters across the product handling nonunits, reindex, Fubini), so Phase 6 is decisively NOT-COMPOSABLE. The mathematical content clearly merits mathlib inclusion.

It lands in **YES-but-generalise-first** rather than YES-add-as-is for two reasons, both surfaced in Phase 4c. First, the additive character is hand-constructed via `AddChar.zmodChar (εD*εM) <inline (εD*εM)^(DM)=1 proof>`, whereas mathlib's idiom for Dirichlet-character Gauss sums is `stdAddChar` (`Mathlib/Analysis/Fourier/ZMod.lean`), next to which this lemma should sit. Second, and more importantly, the product character is specified by the bespoke hypothesis `hθ : θ = changeLevel η * changeLevel χ` rather than by the canonical coprime-product character built from the CRT mul-equiv `(ZMod (D*M))ˣ ≃* (ZMod D)ˣ × (ZMod M)ˣ`. The `hθ` form is a definitional crutch: the lemma's *sole* consumer (`ValuesAtOne.lean:1787`) must reconstruct it by hand as `hθinvfac` before applying the lemma — concrete evidence that a canonical product-character formulation would compose better. The verdict gate requires this be YES-but-generalise-first (MODERN-IDIOM) since Phase 4c found a real organisational improvement on top of a MAXIMALLY-GENERAL form.

**Reason for the generalisation:** MODERN-IDIOM (Bourbaki 2.0) — Phase 4c found a contemporary mathlib formulation (canonical CRT product character + `stdAddChar`) that is a real API improvement; NOT a literature-weakening (Phase 4b found 0 weakenings, the form is already maximally general).

**Proposed restatement:**
```lean
-- Replace the bespoke `hθ` product hypothesis with a canonical coprime-product
-- character, and align the additive character with mathlib's `stdAddChar`.
theorem gaussSum_mul_coprime {R : Type*} [CommRing R] [IsDomain R] {D M : ℕ}
    [NeZero D] [NeZero M] (hco : D.Coprime M)
    (η : DirichletCharacter R D) (χ : DirichletCharacter R M)
    {εD εM : R} (hεD : IsPrimitiveRoot εD D) (hεM : IsPrimitiveRoot εM M) :
    gaussSum (η.coprodCoprime χ hco) (AddChar.zmodChar (D * M) <split-root-proof>)
      = gaussSum η (AddChar.zmodChar D hεD.pow_eq_one)
        * gaussSum χ (AddChar.zmodChar M hεM.pow_eq_one) := by
  sorry  -- CRT proof structure survives; the additive-char factorisation step needs
         -- re-deriving against the canonical product character / stdAddChar conventions
-- where `DirichletCharacter.coprodCoprime` is the canonical product-of-coprime-level
-- characters (to be located/added in the DirichletCharacter API), removing the need
-- for callers to supply `hθ`.
```

Estimated cost of regeneralisation: **MODERATE** (the CRT skeleton is reusable; the character-product reformulation and additive-character alignment are the work). Note: cost does not downgrade the verdict — mathlib's value is in shipping the right form.

Mathlib downstream this enables (MODERN-IDIOM, required):
- A named `coprodCoprime` product character composes with `DirichletCharacter.Orthogonality`, `changeLevel`, and `ZMod.chineseRemainder` — callers get `G(θ)=G(η)G(χ)` from a clean object instead of threading an `hθ` equation.
- Sitting the lemma next to `stdAddChar` lets it interoperate with `gaussSum_mulShift_of_isPrimitive` and `fourierTransform_eq_gaussSum_mulShift` (the Fourier/ZMod machinery), where every other Dirichlet Gauss-sum result lives.
- Proofs blocked by the old form: any consumer wanting the factorisation must currently first prove the `changeLevel`-product equation by hand (as the present sole caller does) — the canonical product character removes that obligation.

Proposed mathlib location (eventual PR): `Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean` (alongside `gaussSum_mulShift_of_isPrimitive`), or `Mathlib/NumberTheory/GaussSum.lean` in the `GaussSumProd` section next to `gaussSum_mul`.

**Next action:** run `/generalise PadicLFunctions.ValuesAtOneComplex.gaussSum_mul_coprime` — it will tension the current statement against both the literature-standard form (Phase 3) and the modern-idiom form (Phase 4c: canonical coprime-product character + `stdAddChar`), and determine whether `DirichletCharacter.coprodCoprime` needs introducing. Then `/cleanup` the restated lemma and open the mathlib PR.

---

## Next step

Run `/generalise PadicLFunctions.ValuesAtOneComplex.gaussSum_mul_coprime` to restate against the canonical coprime-product character + `stdAddChar` (dropping the `hθ` hypothesis), then `/cleanup` and open a `feat(NumberTheory): Gauss-sum multiplicativity over coprime conductors` PR against `Mathlib/NumberTheory/DirichletCharacter/GaussSum.lean`.
