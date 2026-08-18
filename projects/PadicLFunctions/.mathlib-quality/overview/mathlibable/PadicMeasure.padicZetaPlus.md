# /mathlibable report — `PadicMeasure.padicZetaPlus`

**Mode:** A (single declaration, full 10-phase workflow with exhaustive 9-channel literature search)
**Target:** `PadicMeasure.padicZetaPlus`
**Kind:** `def` (noncomputable section)
**Source:** `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:177`
**Date:** 2026-06-20

---

## FINAL VERDICT: `BORDERLINE-needs-human`

> `padicZetaPlus` is **ζ_p⁺**, the descent of the Kubota–Leopoldt p-adic zeta function to
> the plus-part Galois group `𝒢⁺ = ℤ_p^×/{±1}` — the *object* of **RJW Corollary 7.6 /
> TeX 3033** ("the p-adic zeta function is a pseudo-measure on `G⁺`"). The literature is
> unanimous and the construction is real, standard Iwasawa theory; mathlib has **none** of
> the surrounding apparatus (no p-adic zeta, no pseudo-measure, no Iwasawa algebra
> `ℤ_p[[G]]`, no augmentation ideal — Phase 5 grep: 0 hits). So it is **not**
> `NO-mathlib-has-it`. It is **not** `NO-composable-from-mathlib` either: the only mathlib
> primitive in the body is `IsLocalization.mk'`; the numerator `projPlus (zetaNum a)` and
> denominator `[ā]−[1]` are deeply project-specific (built from `padicZeta`'s entire
> construction + the `projPlus` pushforward), not a ≤3-call composition of mathlib decls.
> But it is **not cleanly `YES-*` either**, for two reasons the skill cannot resolve
> alone: (1) the literature does **not** treat the plus-part descent as a *separately
> named object* — Williams/RJW and the codex channel agree it is "the even/plus part of
> ζ_p", a *corollary* (Cor 7.6), not a new function symbol; whether mathlib should have a
> standalone `padicZetaPlus` `def` vs. deriving "the plus component" from `padicZeta` is a
> taste call; and (2) `padicZetaPlus` sits at the **top of a tall, entirely-missing
> mathlib tower** (`padicZeta` → `zetaNum`/`muAUnits` → Iwasawa-algebra convolution ring →
> pseudo-measure predicate, the last of which is itself `YES-but-generalise-first`, not
> yet shipped) — so the right grain, generality, and even existence of this single `def`
> as a mathlib contribution depend on design decisions about that whole corner that a
> human maintainer must make. Numbered questions below.

---

## Phase 0 — Doctor / baseline

### Baseline (Phase 0)
- **lake build:** **not re-run** (worktree build is stale/slow per task instructions); **reasoned from source** — read the declaration, its un-quotiented parent `padicZeta`, every type/term dependency (`PadicMeasure`, `GPlus`, `QuotientFieldPlus`, `toQPlus`, `zetaNum`, `projPlus`, `IsLocalization.mk'`, `dirac_mk_sub_one_mem_nonZeroDivisors`, `exists_nat_topological_generator`), the two sibling `/mathlibable` reports in this directory (`IsPlusPseudoMeasure`, `QuotientFieldPlus`), and the mathlib + literature search surfaces directly. The skill's Phase-0 fallback explicitly permits this.
- **decl `PadicMeasure.padicZetaPlus`:** ✓ resolved at `ZetaGalois.lean:177`.
- **kind:** `def` (noncomputable; produces a value in `QuotientFieldPlus p`).
- **has sorry:** **no.** The whole file `ZetaGalois.lean` is sorry-free (`grep -c sorry` = 0); the body references only existing, compiling definitions, and its consumers (`projPlus_padicZeta_witness`, `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdealPlus`, `zetaIdealPlus_eq_span`) are completed proofs.
- **module docstring summary:** "ζ_p as a pseudo-measure on 𝒢⁺ and the ideal I(𝒢)ζ_p" — RJW (arXiv:2309.15692) §11.1 corollary + §11.2, on the identified Galois side (`𝒢⁺ = GPlus p`).

## Phase 1 — Comprehend

### Statement (Phase 1)

```lean
/-- **ζ_p as a pseudo-measure on 𝒢⁺** (the object of RJW's corollary, TeX 3033):
`ζ_p⁺ := π_*(x⁻¹ Res μ_a) / ([ā]−[1])`, for the same packed integer topological
generator `a` as `padicZeta`. -/
def padicZetaPlus (hp2 : p ≠ 2) : QuotientFieldPlus p :=
  IsLocalization.mk' (QuotientFieldPlus p)
    (projPlus p (zetaNum p (exists_nat_topological_generator p hp2).choose))
    (⟨dirac p (QuotientGroup.mk
        ((exists_nat_topological_generator p hp2).choose_spec.choose) : GPlus p) - 1,
      dirac_mk_sub_one_mem_nonZeroDivisors p hp2 (…)⟩ :
      nonZeroDivisors (PadicMeasure p (GPlus p)))
```
with `variable (p : ℕ) [hp : Fact p.Prime]`.

`padicZetaPlus` is **a definition of** the following object:

The **p-adic zeta function descended to the plus-part Galois group** `𝒢⁺ = ℤ_p^×/{±1}`,
i.e. the element `ζ_p⁺ ∈ Q(𝒢⁺) = Frac(Λ(𝒢⁺))` given as the localization fraction
`π_*(x⁻¹ · Res_{ℤ_p^×} μ_a) / ([ā] − [1])`, where `a` is a fixed integer topological
generator of `ℤ_p^×`, `μ_a` is the associated p-adic measure, `x⁻¹ Res μ_a` is the
numerator of the Kubota–Leopoldt p-adic zeta function (`zetaNum a`), `π_*` is the
pushforward along the quotient `ℤ_p^× → ℤ_p^×/{±1}`, and `[ā] − [1]` is the image
augmentation generator in `Λ(𝒢⁺)`. It is exactly `padicZeta` with **numerator pushed
forward by `projPlus`** and **denominator descended to `𝒢⁺`** (same `IsLocalization.mk'`
shape — see the structural parallel in Phase 6). By RJW Cor. 7.6 it is a *pseudo-measure*
on `𝒢⁺`, and it interpolates the even values `ζ(1−k)` (`k` even), the odd ones having
vanished by complex conjugation (this file's `padicZeta_odd_moment_eq_zero` /
`dirac_neg_one_sub_one_mul_padicZeta`).

**Dependency unfolding (Lean side):**
- `padicZeta (hp2) : QuotientField p := IsLocalization.mk' (QuotientField p) (zetaNum p a) ⟨[a]−1, …⟩` (`KubotaLeopoldt/ZetaP.lean:252`, **RJW Def. 4.10**) — the un-quotiented Kubota–Leopoldt p-adic zeta function. `padicZetaPlus` is its `projPlus`-image.
- `zetaNum p a := unitsCmul p (invCM p) (muAUnits p a)` (`ZetaP.lean:74`) — the numerator `x⁻¹ Res_{ℤ_p^×} μ_a` (a `PadicMeasure p ℤ_[p]ˣ`).
- `projPlus p : PadicMeasure p ℤ_[p]ˣ →+* PadicMeasure p (GPlus p)` (`Iwasawa/PlusPart.lean:224`) — the pushforward `π_*` along the quotient map (a ring hom; RJW TeX 3012).
- `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)` (`PlusPart.lean:215`) — the plus-part Galois group `𝒢⁺`.
- `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` (`Measure/Basic.lean:52`); `PadicMeasure p (GPlus p)` carries the convolution `CommRing` = Iwasawa algebra `Λ(𝒢⁺)`.
- `QuotientFieldPlus p := FractionRing (PadicMeasure p (GPlus p))` (`ZetaGalois.lean:124`) — `= Q(𝒢⁺)` (sibling report: this alias is `NO-mathlib-has-it`, i.e. mathlib's `FractionRing`).
- `IsLocalization.mk' (S) (x) (y)` (mathlib, `RingTheory/Localization/Defs.lean:253`) — the localization fraction `x/y`. The **only** mathlib primitive in the body.
- `dirac_mk_sub_one_mem_nonZeroDivisors` (`ZetaGalois.lean:140`) — the regularity-transport lemma proving `[ā]−1` is a non-zero-divisor in `Λ(𝒢⁺)` (so the fraction is well-defined). Project lemma.
- `exists_nat_topological_generator` (`ZetaP.lean:124`) — supplies the integer topological generator `a` (its `.choose`).

**Variables / typeclasses involved (Lean side):**
- `p : ℕ`, `[Fact p.Prime]` — the prime; fixes `ℤ_[p]`.
- `(hp2 : p ≠ 2)` — needed so `ℤ_p^×` has a (procyclic) topological generator and so `2` is invertible (the `±1` decomposition).

**Hypotheses:** `hp2 : p ≠ 2` only.

**Conclusion (math):** the element `ζ_p⁺ ∈ Q(𝒢⁺)`.

**Conclusion (Lean):** n/a — this is a `def` producing a value of type `QuotientFieldPlus p`.

## Phase 2 — Preliminary checks

### Size classification (Phase 2a)

**Verdict: BIG.** It is a **main declaration of the file** — listed in the module docstring's "Main declarations" cluster as "`PadicMeasure.padicZetaPlus` + `isPlusPseudoMeasure_padicZetaPlus`: the corollary of RJW TeX 3033 — ζ_p descends to a pseudo-measure on 𝒢⁺". It defines a *named mathematical object* (the plus-part p-adic zeta function), the p-adic analogue of a zeta function, which is squarely "a theorem/construction named after a concept that is guaranteed to be near the literature". (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

- **Body line count:** ~9 lines (a single `IsLocalization.mk'` application, but with a substantial bundled non-zero-divisor witness term). Effectively **one substantive expression** (`mk' S num ⟨den, proof⟩`).
- **One-liner verdict:** borderline ONE-LINER (it is morally one `mk'` application). Treat as **ONE-LINER** and run the exemption check, since the whole body is a single localization fraction.

| Exemption | Applies? | Evidence |
|---|---|---|
| Avoid defeq abuse | **yes (mild)** | The body is sealed as a `def` (no `@[reducible]`) so the `mk'` does not unfold spontaneously; downstream proofs (`projPlus_padicZeta_witness`) explicitly `rw [hzp]`/`rfl`-expose it only when wanted (`hzp : padicZetaPlus … = IsLocalization.mk' … c := rfl`, line 227). The seal keeps `padicZetaPlus` from being silently rewritten as the raw `mk'`. |
| Avoid typeclass diamonds | no | introduces no instance; the `CommRing (PadicMeasure p (GPlus p))` it relies on is supplied independently. |
| Mark semantic intent / API name | **yes** | The name `ζ_p⁺` *is* the API surface: `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdealPlus`, and `zetaIdealPlus_eq_span` (the §11.2 ideal / §12 Iwasawa-Main-Conjecture board) all consume it by name; re-implementing the descent behind the same name would not break those consumers. |

**Conclusion: ONE-LINER WITH-EXEMPTION** (defeq-seal + named-API-anchor). The one-line shape therefore does **not** bias toward NO; the def's name is load-bearing for the file's headline theorems. (This is unlike the sibling `QuotientFieldPlus`, a pure notational alias with no exemption.)

## Phase 3 — EXHAUSTIVE literature search (9 channels)

| # | Channel | Query | Hit? | Standard form found | Notes |
|---|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic zeta function Kubota–Leopoldt as pseudo-measure element of fraction ring Iwasawa algebra Q(G) Serre Coates" | **yes** | ζ_p is a **pseudomeasure**; "the Kubota–Leopoldt p-adic L-function … is a pseudomeasure"; described measure-theoretically and via Iwasawa's algebraic construction over `Λ(G)` | top hit is the project's own source **Williams, arXiv:2309.15692**; also MSP ENT intro, Ahilado notes. |
| 2 | WebSearch (descent / plus part) | "p-adic zeta function pseudo-measure on Galois group ℤ_p^× descent plus part totally real Iwasawa main conjecture" | **yes** | "the p-adic zeta function can be reformulated as a **pseudo-measure on the Galois group Γ ≅ ℤ_p^×** … a central idea in Iwasawa theory"; "measures ↔ elements of the Iwasawa algebra" | arXiv:0711.0581 (non-abelian pseudomeasures), arXiv:2310.04385 (totally real torsion congruences); confirms the descent context. |
| 3 | WebSearch (odd characters vanish / aliases) | "p-adic L-function descends pseudo-measure quotient Galois group complex conjugation odd characters vanish 'plus part'" | **yes** | "a p-adic L-function **vanishes identically on the subspace parametrising odd characters**"; "p-adic L-functions should be **pseudo-measures on Gal(K^{ab,p}/K)**" | the odd-vanishing = the exact c-invariance that *causes* the plus-part descent; framing is pseudo-measure on an arbitrary abelian Galois group. |
| 4 | ChatGPT-equivalent (codex `gpt-5.5`, read-only, no tools) | "Is the DESCENT of the p-adic zeta pseudo-measure to the plus-part `G⁺ = ℤ_p^×/{±1}` a STANDARD NAMED object? most general form? formalized?" | **yes** | *verbatim:* "Usually this is **not given a separate standard name** as a new object. It is the **even/plus part of the Kubota–Leopoldt p-adic zeta function**, or the **plus component of Serre's p-adic pseudomeasure** … still a Serre/Kubota–Leopoldt pseudomeasure in the total fraction ring of the plus Iwasawa algebra." | also: most general form is **not** just `ℤ_p^×` — Serre & **Deligne–Ribet** state pseudomeasures for **abelian Galois groups over totally real fields**; "**not** … formalized in mathlib, nor … in another proof assistant." |
| 5 | Local references (`refs/PadicLFunctions/`, `.mathlib-quality/references/`) | grep for the source | **n/a** | (neither dir present in this worktree — `references/` absent, `refs/` not symlinked; `*.pdf` is local-only by repo policy) | **but** the source PDF (Williams = arXiv:2309.15692, the project's RJW) was fetched and read directly: see channel 6-equivalent below; in-file docstrings cite **RJW Cor. of TeX 3033** for exactly this object. |
| 6 | nLab / nCatLab | `ncatlab.org/nlab/show/p-adic+L-function` (WebFetch) | **n/a** | HTTP 404 — page does not exist | the p-adic zeta / pseudo-measure is an Iwasawa-theory / commutative-algebra notion, not a categorical one; nLab has no entry. Recorded n/a with reason. |
| 7 | **Source PDF read (Williams / RJW, arXiv:2309.15692)** | `pdftotext` + grep "pseudo-measure" → §3.3, §7.2.1 | **yes, verbatim** | **Def. 3.7:** "Let `G` be an abelian profinite group … `Q(G)` … fraction field of `Λ(G)`. A pseudo-measure on `G` is an element `λ ∈ Q(G)` such that `([g]−[1])λ ∈ Λ(G)` for all `g ∈ G`." **Prop. 3.10:** `ζ_p := x⁻¹ Res μ_a / θ_a ∈ Q(ℤ_p^×)`. **§7.2.1 "Passing to G⁺" + Cor. 7.6:** "ζ_p actually descends to a pseudo-measure on `G⁺`"; "**The p-adic zeta function is a pseudo-measure on `G⁺`.**" | the **exact** source for `padicZetaPlus`: Cor 7.6 is `isPlusPseudoMeasure_padicZetaPlus`; the descent is via Lemmas 7.3–7.5 (the `±1` idempotents, `Λ(G)⁺ ≅ Λ(G⁺)`, odd-moments-vanish). The descent is presented as a **corollary**, *not* a separately-named function. |
| 8 | Stacks Project | total ring of fractions (tag 02C5) — relevant only for the *ambient* ring | **n/a (for ζ_p⁺)** | Stacks has `Q(A)=S⁻¹A` (covered in the `QuotientFieldPlus` sibling report) but **no** p-adic zeta / pseudo-measure | Stacks is alg-geom/comm-alg; it has the fraction ring, not the Iwasawa p-adic L-function. |
| 9 | MathOverflow / Math.SE | covered by channels 1–4 result sets | **n/a-as-search** | — | the construction is uncontested textbook Iwasawa theory (Serre 1978; Coates; Coates–Sujatha; Williams/RJW); no open MO thread to resolve. |
| 10 | recent arXiv (≤5 yr) + prior-formalization sweep | "formalization Kubota–Leopoldt p-adic L-function Lean mathlib Iwasawa pseudo-measure" | **yes** | **arXiv:2302.14491** (Narayanan, "Formalization of p-adic L-functions in Lean 3") — defines the p-adic L-function as an **integral against the Bernoulli measure** (interpolation), **NOT** as a pseudo-measure / fraction-ring element, and with **no plus-part descent**; **Lean 3 only**, standalone repo `laughinggas/p-adic-L-functions`, **never ported to mathlib** | different *formulation* (analytic interpolation, not algebraic pseudo-measure) and not in current mathlib. Confirms the algebraic/Iwasawa form (this project's) is unformalized in mathlib. |

### Literature summary (Phase 3)

- **Concept identified as:** the **plus part / even component of the Kubota–Leopoldt p-adic zeta function** — i.e. **ζ_p descended to `𝒢⁺ = ℤ_p^×/{±1}`**, an element of `Q(𝒢⁺) = Frac(Λ(𝒢⁺))` that is a *pseudo-measure* (Serre/Coates). Source: **Williams/RJW Cor. 7.6 (= TeX 3033)**, on the back of Serre (1978), Coates, Deligne–Ribet.
- **Sources agree on the standard form:** **yes**, unanimously — the descent exists and is a pseudo-measure on `𝒢⁺`; the construction is `mk'`-of-the-pushed-forward-numerator over the descended augmentation generator.
- **Is it a separately-named object?** **No.** Channels 4 and 7 are explicit: the literature treats this as "the even/plus part of ζ_p" / "the plus component of Serre's pseudomeasure" — a **corollary** (ζ_p descends), not a new named function. The named content is the *theorem* `isPlusPseudoMeasure_padicZetaPlus` (Cor 7.6); `padicZetaPlus` is the project's *name for the witnessing element*.
- **Most general standard form:** pseudomeasures are stated by **Serre & Deligne–Ribet for arbitrary abelian Galois groups over totally real fields** (and non-abelian extensions by Kakde/Ritter–Weiss); the Kubota–Leopoldt ζ_p is the special case for `ℚ` (group `ℤ_p^×`), and ζ_p⁺ its plus quotient. So the *ambient* notion is far more general than `𝒢⁺`.
- **Generality dimensions where the literature varies:** the group (`ℤ_p^×/{±1}` here → arbitrary abelian profinite Galois group of a totally real field, in the literature); the base field (`ℚ` here → arbitrary totally real field). The construction itself (`mk'` of a measure numerator over an augmentation generator) is the standard recipe.
- **Disagreement with the literature:** **none on content.** The user's object is exactly the literature's "ζ_p on `𝒢⁺`". The only tension is *packaging*: the literature names the *theorem* (descent), not the *element*.
- **Mathlib presence:** **none.** No p-adic zeta, no Kubota–Leopoldt, no pseudo-measure, no Iwasawa algebra `ℤ_p[[G]]` (Phase 5). The single prior formalization (arXiv:2302.14491) uses a different (Bernoulli-measure-interpolation) formulation in Lean 3, never upstreamed.

The literature search returned the **exact** object with a unanimous standard form — a strong signal of *real content* — but flagged it as a *corollary*, not a separately-named function, and embedded in a far more general (totally-real-field) pseudomeasure framework. Both facts feed the Phase 7 judgment.

## Phase 4 — Generality analysis

### Generality analysis — `padicZetaPlus`

Literature-standard form (from Phase 3): ζ_p⁺ = the plus-part descent of the Kubota–Leopoldt p-adic zeta function, a pseudo-measure on `𝒢⁺`; ambient notion generalises to abelian Galois groups of totally real fields.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker / more-general form exists? | Reason it can/can't be generalised |
|---|------------------------|-------------------|--------------------------|-----------------------------------|-------------------------------------|
| 1 | the group is hard-coded `GPlus p = ℤ_p^×/{±1}` | one specific quotient group | ζ_p⁺ over `ℤ_p^×/{±1}` (the literature object for `ℚ`); ambient pseudomeasures over **arbitrary** abelian Galois groups of totally real fields | **conceptually yes** for the *ambient framework*, but **NOT for ζ_p⁺ as a single object** | ζ_p⁺ is *intrinsically* about `ℚ` and its plus-part. The construction does **not** abstract to an arbitrary group without first having (a) a general p-adic-zeta/L-function for that group and (b) the corresponding measure numerator — i.e. the Deligne–Ribet construction, which is **far more than a signature edit** (it needs the totally-real p-adic L-function, absent from both project and mathlib). |
| 2 | base field implicitly `ℚ` | `ℚ` (ζ interpolates `ζ(1−k)`) | arbitrary totally real `F` (interpolating `ζ_F` / `L(χ,1−k)`) | yes, in principle | EXPENSIVE — needs Deligne–Ribet / the totally-real Iwasawa Main Conjecture inputs; entirely new math, not in scope here. |
| 3 | numerator `projPlus (zetaNum a)` | the specific `x⁻¹ Res μ_a` pushed forward | the standard ζ_p numerator | NO | this *is* the standard recipe; no weaker form. |
| 4 | denominator `[ā]−[1]`, choice of generator `a` | a fixed topological generator | independence-of-`a` is a theorem (Williams Prop 3.10(i)) | n/a (well-definedness, not generality) | the def fixes a `.choose` generator; independence is a separate lemma — a *cleanup/packaging* point, not a generality axis. |

**Crucial cross-reference — the siblings in this directory:**
- `IsPlusPseudoMeasure` (the *predicate* ζ_p⁺ satisfies) → verdict **`YES-but-generalise-first`**: the pseudo-measure predicate is missing from mathlib and should be stated for an **arbitrary** compact commutative `G` (merging with the `ℤ_[p]ˣ` twin `IsPseudoMeasure`). **`padicZetaPlus` lives *inside* the fraction ring that predicate ranges over.**
- `QuotientFieldPlus` (the *ambient ring* `Q(𝒢⁺)`) → verdict **`NO-mathlib-has-it`** (it is mathlib's `FractionRing`).

So the generality story for ζ_p⁺ is *split*: the **ambient ring** is mathlib's (general), the **predicate** wants generalising (and is `YES-but-generalise`), but **the element ζ_p⁺ itself is irreducibly about `ℚ` / its plus-part** — its "generalisation" is not a signature edit but the entire Deligne–Ribet totally-real construction.

### Generality verdict (Phase 4b)

**The current form is: NOT STRAIGHTFORWARDLY ON A GENERALITY AXIS.** Unlike a lemma with weakenable hypotheses, ζ_p⁺ is a *specific named object*; its only "more general form" (totally-real Deligne–Ribet pseudomeasures) is **a different, much larger construction (EXPENSIVE, new math, absent from project & mathlib)**, not a mechanical weakening of this `def`. Within the project's `ℚ`-scope, the object is already at its natural specificity.

**Number of mechanical weakening opportunities found: 0** (the generality lives in the *ambient predicate* `IsPlusPseudoMeasure`, separately assessed, not in this element).

Per the skill's cost rule: an EXPENSIVE generalisation would *not* by itself downgrade a YES — but here the situation is subtler than cost. The "generalisation" (totally-real fields) yields a **different object**, so this is not a `YES-but-generalise-first` of *this* def; it is a question about whether mathlib wants the `ℚ`-specific object at all, which is a human call (Phase 7).

### Phase 4c — Modern-mathlib-idiom restatement (Bourbaki 2.0 check)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let G be a foo" preamble → typeclass / abstract parameter? | **partial** | the *predicate* `IsPlusPseudoMeasure` should abstract `G` (its own `YES-but-generalise` report) — but **ζ_p⁺ the element cannot**, since it is the descent of a `ℚ`-specific function | abstracting the predicate is the win; the element stays concrete. |
| 2 | sequences/metric → filters/topological? | no | — | the object is algebraic (a localization fraction). |
| 3 | construct an object → universal-property class? | **partial-no** | one *could* characterise ζ_p⁺ by its interpolation property (Williams Prop 3.10(ii): `∫ x^k ζ_p⁺ = (1−p^{k−1})ζ(1−k)`, k even) rather than by the explicit `mk'` — a "values determine it" universal property (Williams Lemma 3.8) | a property-characterised ζ_p⁺ would compose with future interpolation API, BUT the explicit construction is also standard and needed for the ideal computations (`zetaIdealPlus_eq_span`). Both have a place; not a clear modernisation. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | — |
| 5 | field-specific → weaken typeclasses? | no (for the element) | — | the "field" here is the base number field `ℚ`; weakening it = totally-real Deligne–Ribet = different object, not a typeclass weakening. |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index → arbitrary structure? | no (for the element) | — | ζ_p⁺ is one object, not indexed. |

**Modern-idiom verdict (Phase 4c): no decisive modernisation of *this def*.** The available "modern" moves attach to *neighbours* (generalise the **predicate** `IsPlusPseudoMeasure`; possibly characterise ζ_p⁺ by interpolation) — not to `padicZetaPlus` as written. The explicit `IsLocalization.mk'` construction is already the mathlib idiom for "an element of a localization given by numerator/denominator" (mathlib uses exactly `mk' (FractionRing R) x ⟨y,hy⟩`, e.g. `ClassGroup/Basic.lean:141`, `RatFunc/Defs.lean:154`). One-line reason it's not a modernisation move: the def is already on the mathlib localization idiom; its genuine open question is *packaging/scope*, not idiom.

## Phase 4.5 — Diamond / defeq risk (`def`)

### Diamond / defeq risk — `padicZetaPlus`

`padicZetaPlus` is a plain **value-level `def`** (an element of `QuotientFieldPlus p`), with **no** `@[reducible]`, `@[simp]`, `instance`, `class`, `CoeFun`, or `CoeSort` attribute (confirmed by source read of `ZetaGalois.lean:174–186` and the attribute-free declaration head). It is not a type, not a structure, not an instance.

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | declares no instance; a value in `QuotientFieldPlus p` is never an instance target. The `CommRing (PadicMeasure p (GPlus p))` / `FractionRing` instances it *uses* come from elsewhere and are unaffected. |
| 2 | Reducibility leak | **none/low** | no `@[reducible]`; semi-reducible like any `def`. Its body is a single `IsLocalization.mk'` term, not a computation `simp` would silently expand; one downstream proof deliberately exposes it via `rfl` (`hzp`, line 227) only when wanted. |
| 3 | Non-canonical unfolding | **none** | consumers reference it by name and unfold it explicitly (the `hzp : … = mk' … := rfl` pattern); nothing rewrites it implicitly. |
| 4 | Instance priority collision | **n/a** | not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | everything is in fixed `Type 0` (`ℤ_[p]`, `GPlus p`, `QuotientFieldPlus p`); no universe annotation forced. |
| 6 | Coercion ambiguity | **none** | no `CoeFun`/`CoeSort`; the coercions in the body (`algebraMap`/`mk'`, `QuotientGroup.mk`) are existing ones. |

### Risk verdict (Phase 4.5)

**Overall risk: NONE.** A value-level `def` built from `IsLocalization.mk'` with no attributes is infrastructure-inert. (The risk profile does not affect the BORDERLINE verdict, which rests on packaging/scope, not on defeq hazards.)

## Phase 5 — Mathlib five-method search

Searched on (a) the user's form (ζ_p⁺ on `𝒢⁺`), (b) the literature-standard ambient objects (Kubota–Leopoldt ζ_p; Serre/Deligne–Ribet pseudomeasure of a totally-real field), and (c) the supporting infrastructure (Iwasawa algebra `ℤ_p[[G]]`, augmentation ideal, the `mk'`-of-measure-numerator construction).

### Mathlib search-status: `PadicMeasure.padicZetaPlus`

| Method | Query | Result |
|---|---|---|
| [A] Lean-Finder (AI/NL) | "p-adic zeta function as element of fraction ring of Iwasawa algebra", "Kubota–Leopoldt p-adic L-function pseudo-measure", "plus part of p-adic zeta" | **no hit** — surfaces only generic localization / `IsLocalization.mk'` lemmas and the *complex* zeta/L-functions; no p-adic zeta object. |
| [B] Loogle (type pattern) | values of shape `IsLocalization.mk' (FractionRing (… measure ring …)) _ _`; defs producing `FractionRing _` from a group-algebra measure | **no hit** — mathlib uses `mk' (FractionRing R) …` (RatFunc, ClassGroup) but **never** over a p-adic-measure / Iwasawa-algebra ring; no p-adic zeta element. |
| [C] LeanSearch (NL) | "p-adic zeta function", "Kubota–Leopoldt", "p-adic L-function as a measure / pseudo-measure on a Galois group" | **no hit** for the p-adic object (returns complex `riemannZeta`, `LSeries`, Hurwitz zeta — all archimedean). |
| [D] Grep mathlib src | `grep -rni "kubota\|padicZeta\|pseudomeasure\|padicLFunction\|p_adic_L" Mathlib` ; `iwasawa` ; `completedGroupAlgebra` ; `augmentationIdeal` ; `find … NumberTheory -iname '*Iwasawa*\|*Kubota*\|*padicL*'` | **0 hits** for all p-adic-L / pseudomeasure / Kubota / Iwasawa-algebra terms. `NumberTheory/` has only the **complex** zeta/L-function files (`RiemannZeta`, `HurwitzZeta*`, `LSeries/*`, `ZetaValues`, `ArithmeticFunction/LFunction`) and `GroupTheory/.../Iwasawa.lean` is the **Iwasawa simplicity criterion** (unrelated group theory). |
| [E] Name pattern (local + mathlib) | `padicZeta`, `padicZetaPlus`, `zetaP`, `padicL`, `pAdicL` | present **only** in this project; **absent** from mathlib. |

**Searched for both forms:** yes — the user's `𝒢⁺` form, the un-quotiented `ℤ_p^×` form (`padicZeta`), the general totally-real pseudomeasure, **and** the prior Lean-3 formalization's Bernoulli-interpolation form. Current mathlib has **none** of them.

**Concluded:** **not in mathlib** (all five methods exhausted, plus the literature-standard ambient forms and the prior-art Lean-3 formulation). Mathlib has neither ζ_p, nor ζ_p⁺, nor the pseudo-measure predicate, nor the Iwasawa algebra `ℤ_p[[G]]` as a measure ring, nor the augmentation ideal. **There is no existing decl to specialise from (`NO-mathlib-has-it` is excluded) and no `D'` to re-aim at.**

## Phase 6 — Composition check (+ call-sites signal)

### Call sites — `padicZetaPlus`

- **Internal use count (within project, excluding declaring file): 0.**
- **External-to-file callers: 0.** Every reference is **inside** the declaring file `Iwasawa/ZetaGalois.lean` (the docstring + 4 substantive uses).
- **In-file uses: 4 substantive**, all by the file's own headline results:

| Caller (in declaring file) | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `ZetaGalois.lean:194, 226–227` | `projPlus_padicZeta_witness … : toQPlus … * padicZetaPlus p hp2 = toQPlus … (projPlus p ν)` (the descent-compatibility lemma; `hzp : padicZetaPlus … = mk' … := rfl`) |
| `ZetaGalois.lean:240–241` | `isPlusPseudoMeasure_padicZetaPlus … : IsPlusPseudoMeasure p (padicZetaPlus p hp2)` — **RJW Cor. 7.6, the def's raison d'être** |
| `ZetaGalois.lean:333, 345` | `zetaIdealPlus … := {x | … toQPlus p x = toQPlus p l * padicZetaPlus p hp2}` (the ideal `I(𝒢⁺)ζ_p`) |
| `ZetaGalois.lean:355` | `zetaIdealPlus_eq_span … : … * padicZetaPlus p hp2 = toQPlus p (projPlus p ν)` (the `Ideal.span` description) |

Inline-derivation grep (was ζ_p⁺ re-built elsewhere without `padicZetaPlus`?): **(none)** — no other site re-derives the descent inline.

**What the pattern tells you.** External-to-file `K = 0`, but the in-file uses are **the file's main theorems** (Cor 7.6, the §11.2 ideal, the §12 Iwasawa-Main-Conjecture board). This is *not* the "dead code / wrong abstraction" `K = 0` profile — it is "a brand-new headline object whose consumers are its own corollaries, in a fresh corner of the project." The signal is **neither clearly YES (no downstream library depends on it yet) nor clearly NO (it is the named object of a real theorem)** — reinforcing BORDERLINE.

### Composition check (Phase 6)

Can `padicZetaPlus` be **derived** from mathlib in ≤3 chained calls? **No.**

- **Attempt 1 — mathlib has the object:** fails. Phase 5: no p-adic zeta / pseudo-measure / Iwasawa algebra in mathlib. Nothing to compose *from*.
- **Attempt 2 — "it is just `IsLocalization.mk' S num den`":** the *shape* is a single mathlib call, but the **arguments are not mathlib objects**: the numerator `projPlus p (zetaNum p a)` is built from `zetaNum` (= `unitsCmul (invCM) (muAUnits a)`, project) pushed through `projPlus` (project ring hom), and the denominator's non-zero-divisor proof is `dirac_mk_sub_one_mem_nonZeroDivisors` (a non-trivial project lemma whose proof goes through the plus/minus-part decomposition). So writing the `mk'` is **defining ζ_p⁺ in terms of the project's own ζ-machinery**, not composing *mathlib* decls. There is no `mathlib_call1 (mathlib_call2 …)` of ≤3 that yields it.
- **Attempt 3 — derive from the un-quotiented `padicZeta`:** ζ_p⁺ is *morally* `projPlus`-of-`padicZeta`, but `projPlus` acts on `PadicMeasure`, not on the fraction ring, and pushing a fraction forward needs the witness theory (`projPlus_padicZeta_witness`) — again project code, not a mathlib composition.

**Conclusion: NOT-COMPOSABLE (from mathlib).** ζ_p⁺ is a `def` whose every non-trivial ingredient (`zetaNum`, `projPlus`, the regularity lemma, `padicZeta`) is project-specific and absent from mathlib. This **excludes `NO-composable-from-mathlib`.**

## Phase 7 — Verdict synthesis (gate)

### Verdict: `PadicMeasure.padicZetaPlus`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- **Literature search (Phase 3):** the object is **ζ_p⁺ = the plus-part descent of the Kubota–Leopoldt p-adic zeta function** (Williams/RJW **Cor. 7.6 / §7.2.1**, read verbatim from the source PDF; Serre/Coates/Deligne–Ribet lineage). Real, standard Iwasawa theory — but the literature treats it as **a corollary ("ζ_p descends"), not a separately-named function**, and embeds it in a far more general (arbitrary abelian Galois group of a totally real field) pseudomeasure framework. 5+ channels hit; Stacks/nLab n/a with reasons; the source PDF read directly.
- **Generality analysis (Phase 4):** the element is **irreducibly `ℚ`-/plus-part-specific**; its only "more general form" is the Deligne–Ribet totally-real construction — a *different, EXPENSIVE, new-math* object, not a mechanical weakening of this `def`. The generality that *can* be improved lives in the **neighbouring predicate** `IsPlusPseudoMeasure` (separately `YES-but-generalise-first`), not here. Phase 4c: no decisive modernisation of this def (already on the `mk'` idiom).
- **Mathlib search (Phase 5):** **not in mathlib** under any form — no p-adic zeta, no pseudo-measure, no Iwasawa algebra, no augmentation ideal. The one prior formalization (arXiv:2302.14491, Lean 3) uses a different Bernoulli-interpolation formulation and was never upstreamed. **Excludes `NO-mathlib-has-it`.**
- **Composition check (Phase 6):** **NOT-COMPOSABLE** from mathlib — every ingredient (`zetaNum`, `projPlus`, `padicZeta`, the regularity lemma) is project-specific. **Excludes `NO-composable-from-mathlib`.** Call sites: external-to-file `K = 0`, in-file uses are the file's own headline corollaries — a brand-new-object profile, not dead code.

**Rationale (why BORDERLINE, not a YES).**
Two of the five buckets are firmly **out**: mathlib has none of this (so not `NO-mathlib-has-it`), and the def is not a ≤3-call composition of mathlib primitives (so not `NO-composable-from-mathlib`). The genuine question is between a YES bucket and BORDERLINE, and the skill's own anti-patterns push to BORDERLINE here, for reasons it cannot resolve by evidence alone:

1. **The literature does not name this object — it names the *theorem*.** Channels 4 and 7 are explicit and agree: ζ_p⁺ is "the even/plus part of ζ_p" / "the plus component of Serre's pseudomeasure", introduced as **Corollary 7.6 ("ζ_p descends to a pseudo-measure on G⁺")**, *not* as a new function symbol. Mathlib's habit for "the named theorem is the content, the witnessing element is incidental" varies — sometimes the element gets a `def` (e.g. `riemannZeta`), sometimes it is left inline / derived. Whether mathlib wants a standalone `padicZetaPlus` `def` vs. obtaining "the plus component" by applying a (future, abstract) descent operation to `padicZeta` is a **packaging/taste call**.

2. **ζ_p⁺ sits atop a tall, entirely-missing mathlib tower whose design is unsettled.** It depends on `padicZeta` (itself unassessed/un-upstreamed) → `zetaNum`/`muAUnits` → the convolution Iwasawa-algebra `CommRing (PadicMeasure p G)` → the pseudo-measure predicate `IsPlusPseudoMeasure` (which is `YES-but-generalise-first`, i.e. *should be reshaped before* anything built on it is upstreamed) → the `QuotientFieldPlus` ambient ring (`NO-mathlib-has-it`). The **right generality, the right base layer, and even whether the `ℚ`-specific ζ_p⁺ (vs. a general totally-real pseudomeasure) is the object mathlib wants** are all decisions about that whole corner. Shipping the leaf `def` before the foundation is designed would be premature — but the leaf is also genuinely novel, so it is not a NO. That tension is exactly what BORDERLINE is for.

3. **Cost is *not* the reason for BORDERLINE** (the gate forbids "too expensive ⇒ downgrade"). The Deligne–Ribet generalisation being EXPENSIVE does not drive this verdict; rather, that generalisation produces a *different object*, leaving open whether mathlib wants *this* (`ℚ`, plus-part) one as a named def — a genuine judgment, not a cost dodge.

The skill must **not** silently pick `YES-add-as-is` (Phase 4 found the generality lives in neighbours and the literature does not name the element) nor `YES-but-generalise-first` (the "generalisation" is a different, much larger object, not a restatement of *this* def), nor a NO bucket (excluded above). The honest output is BORDERLINE with the design questions surfaced.

**Numbered questions (≤5):**

1. **Scope of mathlib's p-adic-L corner.** Do you intend to upstream the **whole** Iwasawa/p-adic-L apparatus (`padicZeta`, the convolution Iwasawa algebra `CommRing (PadicMeasure p G)`, the pseudo-measure predicate, the `𝒢⁺` descent) as a new mathlib corner — in which case `padicZetaPlus` ships *as part of that coherent PR series* — or is this corner staying project-local (in which case `padicZetaPlus` is not a mathlib candidate at all)?

2. **Named element vs. derived corollary.** The literature (Williams/RJW Cor. 7.6) names the *theorem* "ζ_p descends to a pseudo-measure on `G⁺`", not the *element*. Do you want mathlib to carry a standalone `padicZetaPlus` `def`, or to obtain "the plus component" by applying a general **descent/pushforward operation on pseudo-measures** (`π_* : Q(Λ(G)) ⇢ Q(Λ(G⁺))`) to `padicZeta` — which would make `padicZetaPlus` a derived term, not a primitive def, and would itself be more reusable?

3. **Sequencing behind the predicate.** The neighbouring `IsPlusPseudoMeasure` is `YES-but-generalise-first` (it should be merged with the `ℤ_[p]ˣ` twin into one abstract `IsPseudoMeasure {G} …` before upstreaming). Should `padicZetaPlus` be (re)assessed for mathlib **only after** that abstract predicate + the Iwasawa-algebra base layer land, since its right home and statement depend on them?

4. **`ℚ`-specific vs. totally-real.** The maximally-general literature object is the **Serre/Deligne–Ribet pseudomeasure of an arbitrary totally real field** (this `padicZetaPlus` is the `ℚ` case). Is the long-term mathlib target the general totally-real pseudomeasure (with ζ_p⁺ as the `F = ℚ` specialisation), or is the `ℚ`-only Kubota–Leopoldt object itself a worthwhile standalone mathlib contribution?

5. **Well-definedness packaging.** The def fixes a `.choose` topological generator `a`; independence-of-`a` is a separate theorem (Williams Prop 3.10(i)). For a mathlib def, would you want ζ_p⁺ characterised by its **interpolation property** (`∫ x^k = (1−p^{k−1})ζ(1−k)`, k even) / a universal property instead of the explicit `mk'` with a chosen generator — i.e. is the explicit construction or the property-characterisation the intended mathlib API?

**Next action:** answer the questions (especially Q1–Q2: is the whole corner upstream-bound, and is ζ_p⁺ a named def or a derived term?), then re-run `/mathlibable PadicMeasure.padicZetaPlus`. **Likely resolutions:**
- *Corner stays project-local* (Q1 = no) → drop from mathlib consideration; `padicZetaPlus` is correct project-internal API as-is.
- *Corner is upstream-bound + ζ_p⁺ wanted as a named def* (Q1 = yes, Q2 = named) → flips to **`YES-add-as-is`**, shipped *as part of the Iwasawa-theory PR series*, **after** the abstract pseudo-measure predicate + Iwasawa-algebra base layer (Q3), with the gap named as "mathlib has no p-adic zeta / Iwasawa-algebra layer at all".
- *Corner upstream-bound but ζ_p⁺ should be a derived term* (Q2 = derived) → the mathlib contribution is the **general descent operation on pseudo-measures**, not `padicZetaPlus`; re-aim the assessment there.

### Phase 7 gate check
- Not `YES-add-as-is`: Phase 4 found no mechanical generality on the element and the literature does not name it; the YES hinges on unsettled design (Q1–Q4). ✓ correctly withheld.
- Not `YES-but-generalise-first`: the "more general form" (Deligne–Ribet, totally real) is a **different, larger object**, not a restatement of this `def`; the generalisable neighbour is the *predicate*, assessed separately. ✓ correctly withheld.
- Not `NO-mathlib-has-it`: Phase 5 conclusion was "not in mathlib" (not "found in mathlib as …"). ✓
- Not `NO-composable-from-mathlib`: Phase 6 conclusion was NOT-COMPOSABLE. ✓
- `BORDERLINE` requires numbered questions: **5 provided, each answerable.** ✓
- Cost is **not** cited as the reason (the gate's forbidden downgrade): the reason is design/packaging + the missing foundation, not expense. ✓

## Phase 8 — Report (this document)

**Five-bucket verdict (final): `BORDERLINE-needs-human`**

- **What's (potentially) novel for mathlib:** **ζ_p⁺**, the plus-part descent of the Kubota–Leopoldt p-adic zeta function (RJW/Williams Cor. 7.6) — and the entire Iwasawa/p-adic-L apparatus it sits on — is **absent from mathlib** (the sole prior formalization, arXiv:2302.14491, used a different Lean-3 Bernoulli-interpolation formulation, never upstreamed).
- **Why not a clean YES:** (1) the literature names the *theorem* (ζ_p descends), not the *element*, so a standalone `def` is a packaging/taste call; (2) ζ_p⁺ tops a tall missing-mathlib tower whose base predicate is itself `YES-but-generalise-first` and whose design (general totally-real pseudomeasure vs. `ℚ`-specific object; named def vs. derived term) is unsettled.
- **Why not a NO:** mathlib has none of this (`NO-mathlib-has-it` excluded) and the def's ingredients are all project-specific, not a ≤3-call mathlib composition (`NO-composable-from-mathlib` excluded).
- **Risk:** Phase 4.5 NONE (a value-level `def` from `IsLocalization.mk'`, no attributes).

---

## Next step

Answer the 5 numbered questions in Phase 7 — above all **Q1 (is the whole Iwasawa/p-adic-L
corner upstream-bound, or project-local?)** and **Q2 (does mathlib want a standalone
`padicZetaPlus` def, or "the plus component" derived via a general pseudo-measure descent
operation applied to `padicZeta`?)** — then re-run `/mathlibable PadicMeasure.padicZetaPlus`.
If the corner is project-local, drop it from mathlib consideration (it is correct internal
API). If it is upstream-bound and ζ_p⁺ is wanted as a named object, the verdict flips to
`YES-add-as-is`, shipped as part of the Iwasawa-theory PR series **after** the abstract
pseudo-measure predicate (`IsPlusPseudoMeasure`'s `YES-but-generalise-first`) and the
Iwasawa-algebra base layer land first.
