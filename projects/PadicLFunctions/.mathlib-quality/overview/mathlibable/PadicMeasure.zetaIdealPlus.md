# `/mathlibable` report — `PadicMeasure.zetaIdealPlus`

**Final verdict: `BORDERLINE-needs-human`.**

`zetaIdealPlus` is the ideal **`I(𝒢⁺)ζ_p`** of the *even-part* cyclotomic Iwasawa
algebra `Λ(𝒢⁺)` — the right-hand side of Iwasawa's Main Conjecture on the totally-real
(plus) side (RJW arXiv:2309.15692 §11.2, Proposition TeX 3052–3057; Coates–Sujatha Ch. 4).
The source paper states this object in the *same sentence* as its `𝒢`-side twin: "`I(Γ)ζ_p`
is an ideal in `Λ(Γ)`, **and similarly `I(Γ⁺)ζ_p` is an ideal in `Λ(Γ⁺)`**." The concept is
impeccably standard and *nothing* of it is in mathlib. But it cannot be shipped "as is": (a)
it is the **literal second instantiation** of the identical construction already present in
the file as `zetaIdeal` — the single strongest signal that the mathlib-worthy unit is the
*abstracted* `(G, q)` form, not two near-identical copies; and (b) like its twin it sits atop
a five-deep tower of equally-standard, equally-**absent** prerequisites (`PadicMeasure` =
Iwasawa algebra of measures, `QuotientFieldPlus`, `IsPlusPseudoMeasure`, `augmentationIdeal`,
`padicZetaPlus`, all built over the absent `GPlus`). The generality / packaging / naming /
audience calls the skill cannot resolve alone are spelled out as numbered questions in Phase 7.

This verdict is **consistent with the sibling assessment** `PadicMeasure.zetaIdeal`
(`BORDERLINE-needs-human`), of which this declaration is the deliberate even-part analogue.

---

### Baseline (Phase 0)

- lake build:               **build not re-run** (stale/slow per task instruction); **reasoned from source** — Phase-0 fallback. The decl and its full dependency chain (`augmentationIdeal`, `toQPlus`, `padicZetaPlus`, `GPlus`, `PadicMeasure`, `projPlus`, the `zetaIdeal` twin) were read directly from source.
- decl `PadicMeasure.zetaIdealPlus`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/ZetaGalois.lean:331`
- kind:                      `def` (a bundled `Ideal (PadicMeasure p (GPlus p))` — fields `carrier`/`add_mem'`/`zero_mem'`/`smul_mem'`)
- has sorry:                 no (the def and its companions `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span` are all sorry-free)
- module docstring summary:  ζ_p as a pseudo-measure on 𝒢⁺ and the ideals `I(𝒢)ζ_p`, `I(𝒢⁺)ζ_p` (RJW arXiv:2309.15692 §11.1–11.2, on the identified Galois side `𝒢⁺ = GPlus p`). `zetaIdeal`/`zetaIdealPlus` are both listed among the file's **Main declarations**.

---

### Statement (Phase 1)

`PadicMeasure.zetaIdealPlus` is **a definition of the ideal `I(𝒢⁺)ζ_p`** of the *even-part*
cyclotomic Iwasawa algebra `Λ(𝒢⁺) = Λ(ℤ_p^× / ⟨-1⟩)`:

> Let `𝒢 = ℤ_p^×` be the cyclotomic Galois group and `𝒢⁺ = 𝒢 / {±1}` its maximal quotient on
> which complex conjugation acts trivially (the "even" / totally-real part; in Lean
> `GPlus p := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)`). Let `Λ(𝒢⁺)` be the Iwasawa algebra
> of `𝒢⁺` (realised concretely as the algebra of `ℤ_p`-valued measures
> `C(𝒢⁺, ℤ_p) →ₗ[ℤ_p] ℤ_p`, RJW Def. 3.6), `Q(𝒢⁺)` its total ring of fractions (`FractionRing`,
> RJW Def. 3.34), `I(𝒢⁺) = ker(deg)` its augmentation ideal (RJW Def. 3.37), and
> `ζ_p⁺ ∈ Q(𝒢⁺)` the descent of the Kubota–Leopoldt p-adic zeta pseudo-measure to `𝒢⁺` (RJW
> Cor. TeX 3033). Then
> `I(𝒢⁺)ζ_p := { x ∈ Λ(𝒢⁺) : x = λ·ζ_p⁺ in Q(𝒢⁺) for some λ ∈ I(𝒢⁺) }`
> is an ideal of `Λ(𝒢⁺)`. (The plus-pseudo-measure property — `([ḡ]−[1])·ζ_p⁺ ∈ Λ(𝒢⁺)` for all
> `ḡ ∈ 𝒢⁺`, proved as `isPlusPseudoMeasure_padicZetaPlus` — is what makes the products land back
> in `Λ(𝒢⁺)`; the augmentation-ideal/ring structure makes the set an ideal.)

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `hp2 : p ≠ 2` — odd prime (essential: `ℤ_p^×` needs a topological generator; enters only via `padicZetaPlus p hp2`).
- implicit: the existing `CommRing (PadicMeasure p (GPlus p))` instance (Iwasawa-algebra ring structure over the even part) and the `FractionRing`/`IsFractionRing` structure on `QuotientFieldPlus p`, accessed through the named ring hom `toQPlus p`.

Hypotheses (Lean side): none beyond `hp2`. The carrier is the membership predicate
`∃ l ∈ augmentationIdeal p (G := GPlus p), toQPlus p x = toQPlus p l * padicZetaPlus p hp2`.

Conclusion (math): `I(𝒢⁺)ζ_p` is an ideal of the even-part Iwasawa algebra `Λ(𝒢⁺)`.

Conclusion (Lean): `Ideal (PadicMeasure p (GPlus p))` — n/a, this is a definition (the four `Ideal` fields).

**Relation to the `𝒢`-side twin.** `zetaIdealPlus` is byte-for-byte the same construction as
`zetaIdeal` (lines 254–265 of the same file) with three substitutions: the group `ℤ_[p]ˣ ↦ GPlus p`,
the structure map `algebraMap … (QuotientField p) ↦ toQPlus p` (which is *definitionally* `algebraMap …
(QuotientFieldPlus p)`, see Phase 4.5), and the pseudo-measure `padicZeta ↦ padicZetaPlus`. The three
closure proofs (`add_mem'`, `zero_mem'`, `smul_mem'`) are *character-identical* between the two defs.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: It is a **main declaration** of its file (named in the module docstring's "Main
declarations"), and it is the **right-hand side object of Iwasawa's Main Conjecture** on the
even/plus side — a named theorem-of-a-person construction. Both BIG triggers fire.

(Literature width was EXHAUSTIVE regardless. BIG is recorded for framing.)

### One-line check (Phase 2b)

Body line count: ~11 substantive lines (a four-field `Ideal where …` bundle with three proved
closure obligations).
One-liner verdict: **MULTI-LINE** — it bundles a `Set`-comprehension carrier with three
nontrivial membership proofs (`add_mem'`, `zero_mem'`, `smul_mem'`). Phase 2b exemption analysis
skipped (not a one-liner).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | Iwasawa main conjecture even part `I(Γ⁺)ζ_p` ideal Λ plus part p-adic zeta pseudo-measure              | yes  | `I(Γ⁺)ζ_p` = RHS of the main conjecture on the **even/plus** side; "characteristic ideal of `X_∞^(i)` for odd `i`" ↔ Kubota–Leopoldt `L_p` | **Surfaced the source paper itself, arXiv:2309.15692** ("An introduction to p-adic L-functions"), plus nLab Iwasawa theory and Grokipedia main-conjecture article. The even/odd ("plus/minus") decomposition is exactly the `𝒢⁺` setting. |
|  2 | WebSearch (descent / even part)  | p-adic zeta pseudo-measure descends to even part Galois group quotient Iwasawa algebra ideal Coates Sujatha | yes  | Galois descent of a pseudo-measure to a quotient group; `ζ_p` realised inside `Λ` via distributions/measures | **Coates–Sujatha *Cyclotomic Fields and Zeta Values*** (the canonical book, Ch. 4) surfaced directly, plus Greenberg/Iwasawa descent framing. Confirms "pseudo-measure on a larger group descends to a quotient" — the `π_*` of `zetaIdealPlus`. |
|  3 | WebSearch (general form)         | "pseudo-measure" total ring of fractions Iwasawa algebra augmentation ideal `I(G)` zeta ideal definition profinite group | yes  | "An element of the total fraction ring of [the measure algebra of] a profinite group is a **pseudo-measure**"; "`I(G)` = **kernel of the canonical homomorphism** from the Iwasawa algebra"; "`Λ(G)` = inverse limit of group rings" | Ardakov *IwasawaSurvey*, Ouyang *Introduction to Iwasawa Theory*, Timmins *Augmented Iwasawa Algebras*, Wikipedia *Iwasawa algebra*. The **general-`G`** definition of pseudo-measure + augmentation ideal is confirmed verbatim. |
|  4 | ChatGPT MCP                      | (would ask: standard form of `I(G⁺)ζ_p` on the even part, generality over `G`, historical evolution)   | n/a  | —                                | **MCP not configured in this environment** (ToolSearch for a ChatGPT / second-opinion tool returned *No matching deferred tools*). Compensated with extra WebSearch queries (#1–#3, #9, #10) + a source-HTML fetch attempt (#5 row in audit note). Same limitation recorded in the sibling `zetaIdeal` report. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/`               | n/a  | (no references dir)              | Neither `…/.mathlib-quality/references/` nor `refs/` exists in this checkout (verified by `ls`). Recorded n/a. The file's own docstrings cite RJW arXiv:2309.15692 with precise TeX line numbers (§11.2, TeX 3052–3057; corollary TeX 3033 for the descent), serving as the in-repo source anchor. |
|  6 | nLab                             | `ncatlab.org/nlab/show/Iwasawa+theory` — fetched and read                                              | no   | — (general prose only)           | nLab has "Iwasawa theory" / "Iwasawa Main Conjecture" prose (mentions "a power series `g_i`" and "Kubota–Leopoldt p-adic zeta function") but **no** dedicated `I(G)ζ_p` / `I(G⁺)ζ_p` / pseudo-measure-ideal definition. Confirmed by direct WebFetch of the page. |
|  7 | nCatLab (if categorical)         | —                                                                                                      | n/a  | —                                | Not a categorical concept — it is an ideal in a specific complete group algebra over the even part. n/a with reason. |
|  8 | Stacks Project (if alg geom)     | Iwasawa algebra pseudo-measure characteristic ideal even part                                          | n/a  | —                                | Not an algebraic-geometry/scheme-theoretic concept; it is analytic/Iwasawa number theory. Stacks has no Iwasawa-theory chapter. n/a with reason. |
|  9 | MathOverflow / Math.StackExchange| pseudo-measure descends quotient group total fraction ring `I(G)` zeta ideal (covered by #2/#3 hits)   | yes  | "pseudo-measure = element of the total ring of fractions; `ζ_p` ↔ moments; `I(G)` = augmentation ideal; descent to a quotient is by pushforward" | Folded into queries #2/#3, which returned the survey/lecture-note corpus (Ardakov, Ouyang, Coates–Sujatha) confirming the framework and the well-definedness intuition (it is an ideal *because* `([ḡ]−1)ζ_p⁺ ∈ Λ(𝒢⁺)`). |
| 10 | recent arXiv (last 5 years)      | 2023–2024 p-adic L-function pseudo-measure even part Galois group ideal Iwasawa algebra main conjecture | yes  | same form, active modern use     | arXiv:2309.15692 (2023, the source); arXiv:2208.06777 (2024, Mazur–Wiles method, relative-primality of elements in the Iwasawa algebra); arXiv:2407.06983 (2024, Artin-motive main conjecture). The even/plus-part ideal framework is current, not historical-only. |

Source-fetch attempts (recorded for audit): the HTML source of arXiv:2309.15692
(`arxiv.org/html/2309.15692v2`) was fetched but **exceeded WebFetch's 10 MB content limit**
(the paper is long). nLab `Iwasawa+theory` *was* successfully fetched and read (row #6). The
verbatim plus-part statement quoted in the Literature summary below comes from the search
engine's extraction of arXiv:2309.15692 as recorded in the sibling `zetaIdeal` assessment
(same source, same sentence), and is independently corroborated by the file's own docstrings
which cite TeX 3052–3057.

### Literature summary (Phase 3)

Concept identified as: **`I(𝒢⁺)ζ_p`** — "the ideal of the *even-part* Iwasawa algebra `Λ(𝒢⁺)`
generated by the augmentation ideal times the descended p-adic zeta pseudo-measure"; the
**right-hand side of Iwasawa's Main Conjecture on the totally-real / plus side**. It is the
"similarly" twin of `I(𝒢)ζ_p`. Equivalent names: "the ζ_p⁺-ideal", "the plus-part
characteristic-ideal side".
Sources agree on the standard form: **yes** — RJW arXiv:2309.15692 (§11.2, the Proposition at
TeX 3052, whose statement is "`I(Γ)ζ_p` is an ideal in `Λ(Γ)`, **and similarly `I(Γ⁺)ζ_p` is
an ideal in `Λ(Γ⁺)`**"), Coates–Sujatha *Cyclotomic Fields and Zeta Values* (Ch. 4), Ardakov's
*IwasawaSurvey*, Ouyang's lecture notes. The construction is uniform: take `λ` in the
augmentation ideal `I(𝒢⁺)`, multiply by the (descended) pseudo-measure `ζ_p⁺` in the total
fraction ring; the products lie in `Λ(𝒢⁺)` and form an ideal.
Most general standard form: for **any** profinite group `G` admitting a pseudo-measure
`ζ ∈ Q(G)`, the set `I(G)·ζ` is an ideal of `Λ(G)`. The cyclotomic `G = ℤ_p^×` and its even
quotient `G⁺ = ℤ_p^× / {±1}` are the two principal instances — and the project realises **both**.
Generality dimensions where the literature varies:
  - **the group `G`**: from the concrete even quotient `𝒢⁺` (this def) and `𝒢` (the twin) to an
    arbitrary profinite group `G`. The Lean def fixes `G = GPlus p`; the literature's general
    statement is "any `G` with a pseudo-measure". The fact that the project **already has both
    `zetaIdeal` (over `𝒢`) and `zetaIdealPlus` (over `𝒢⁺`)** is decisive evidence the general-`G`
    form is the natural mathlib target.
  - **the pseudo-measure `ζ`**: from the descended Kubota–Leopoldt `ζ_p⁺` to an arbitrary
    pseudo-measure `q ∈ Q(G)`. The construction `I(G)·q` makes sense for any pseudo-measure.
Disagreement with the literature: **none**. The Lean form is a faithful, correctly-stated
specialisation of the standard `I(G⁺)ζ_p`, on exactly the even part the source names.

---

### Generality analysis — `PadicMeasure.zetaIdealPlus`

Literature-standard form (from Phase 3): for any profinite `G` and any pseudo-measure
`q ∈ Q(G)`, the set `{x ∈ Λ(G) : algebraMap x = algebraMap l · q, some l ∈ I(G)}` is an ideal
of `Λ(G)`. The two headline instances are `G = 𝒢` (`q = ζ_p`) and `G = 𝒢⁺` (`q = ζ_p⁺`) — the
latter is this declaration.

| # | Parameter / hypothesis                  | Current Lean form                | Literature-standard form         | Weaker form exists? | Reason it can/can't be weakened   |
|---|-----------------------------------------|----------------------------------|----------------------------------|---------------------|------------------------------------|
| 1 | group `= GPlus p` (hard-wired)          | the even part `𝒢⁺`               | arbitrary profinite `G`          | **yes** (in principle) | The closure proofs use only: `toQPlus` (= `algebraMap`) is a ring hom, `augmentationIdeal` is an ideal, and `padicZetaPlus` is a fixed element of `Q(𝒢⁺)`. **Nothing** uses `G = 𝒢⁺` specifically — so the *ideal-construction* generalises to any `(G, q)`. **Stronger evidence than for the twin:** the project *already* instantiates this construction at a *second* group, so the general form is not hypothetical — it is demanded by the existing duplication. BUT every prerequisite (`PadicMeasure (GPlus p)`, `QuotientFieldPlus`, `augmentationIdeal`, the plus-pseudo-measure) is itself project-local; see Phase 5. |
| 2 | pseudo-measure `= padicZetaPlus p hp2`  | the descended `ζ_p⁺`             | arbitrary pseudo-measure `q ∈ Q(G)` | **yes**          | Same: the four ideal axioms never use any property of `ζ_p⁺` beyond "it is a fixed element of `Q(𝒢⁺)`". A general `def pseudoMeasureIdeal (I : Ideal Λ) (q : Q) : Ideal Λ` specialises to this. (The fact that products land in `Λ(𝒢⁺)` — the plus-pseudo-measure property `isPlusPseudoMeasure_padicZetaPlus` — is *not* part of the carrier statement; the carrier is a pure pre-image condition, so even non-pseudo-measures give *an* ideal.) |
| 3 | `hp2 : p ≠ 2`                            | odd prime                        | inherited from `padicZetaPlus`   | **no** (genuinely) | `hp2` enters *only* through `padicZetaPlus p hp2`; the ideal construction does not need it. Not a weakening target — it is the existence hypothesis for `ζ_p⁺` (and `ζ_p`) itself. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (two real specialisation axes: the
group `G`, fixed here to `𝒢⁺`; and the pseudo-measure `q`, fixed to `ζ_p⁺`).
Number of weakening opportunities found: K = 2 (group `G`; pseudo-measure `q`).
Proposed restatement (the literature-standard / mathlib-idiomatic target — *identical* to the one
proposed for the `zetaIdeal` twin, which is the whole point):

```lean
/-- The ideal `I·q` of an Iwasawa-algebra-like ring `Λ` generated by a fixed element `q`
of its total fraction ring `Q`, against a fixed "augmentation" ideal `I ≤ Λ`. -/
def pseudoMeasureIdeal {Λ : Type*} [CommRing Λ] {Q : Type*} [CommRing Q] [Algebra Λ Q]
    (I : Ideal Λ) (q : Q) : Ideal Λ where
  carrier := {x | ∃ l ∈ I, algebraMap Λ Q x = algebraMap Λ Q l * q}
  …   -- the three closure proofs are verbatim the current ones (shared with `zetaIdeal`)
-- then BOTH:
--   zetaIdeal     p hp2 := pseudoMeasureIdeal (augmentationIdeal p (G := ℤ_[p]ˣ))  (padicZeta     p hp2)
--   zetaIdealPlus p hp2 := pseudoMeasureIdeal (augmentationIdeal p (G := GPlus p)) (padicZetaPlus p hp2)
```

Cost of restatement: **CHEAP** as a mechanical Lean rewrite (the proofs are literally unchanged
and are *already* duplicated between `zetaIdeal` and `zetaIdealPlus`). The *expensive* part is
not this def — it is that `Λ(G)`, `Q(G)`, `I(G)`, and `ζ_p`/`ζ_p⁺` would all have to exist in
mathlib first (Phase 5). **Cost does not change the verdict** (Bourbaki-2.0 rule), but it bears
on sequencing and on the human judgment in Phase 7.

→ STRICTLY NARROWER routes Phase 7 to consider `YES-but-generalise-first`. But see Phase 5 /
Phase 7: the generalisation target is itself entirely missing from mathlib, which is what tips
the synthesis to BORDERLINE rather than a clean YES-but-generalise.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | bundled-hypothesis "let `G⁺` be a profinite group / let `q` be a pseudo-measure" → typeclasses? | **partly** | abstract over `[CommRing Λ] [Algebra Λ Q]` + an ideal `I` and element `q` (row above). A `class IsPseudoMeasure`/`IsIwasawaAlgebra` could carry the structure. | composes the ideal with any commutative-ring localization, not just even-part measures |
|  2 | sequences/metric → filters/topological? | **no** | — | no convergence/limit content here; it is a pure algebraic ideal. |
|  3 | explicit construction → universal-property class? | **no** | — | already the canonical "elements that become `I·q` in the fraction ring"; no missing universal property. |
|  4 | set-with-closure-predicate → bundled-substructure type? | **no (already bundled)** | — | it *is* a bundled `Ideal` (mathlib's `Submodule`-based ideal type). Composes with `Ideal.span`, `Ideal.Quotient`, `Ideal.map` — all of which the call sites use heavily (`zetaIdealPlus_eq_span`, `Λ(𝒢⁺) ⧸ zetaIdealPlus`, `.map projPlus`). |
|  5 | field/metric-specific → weaken typeclass to module/ring? | **yes** (= Phase-4b rows 1–2) | abstract `Λ(𝒢⁺)` to a general `CommRing`/`Algebra` pair | full `Ideal`/`IsLocalization` API on the abstract ring |
|  6 | 1-categorical → higher-categorical? | **no** | — | not a categorical statement. |
|  7 | concrete index (`GPlus p`) → arbitrary group/monoid? | **yes** (= Phase-4b row 1) | replace `GPlus p` by a general profinite `G` | **unifies `zetaIdeal` and `zetaIdealPlus` into one `def`** — this declaration *is* the duplication that the abstraction would remove |

```
Modern idiom available: yes (a single abstract `pseudoMeasureIdeal (I : Ideal Λ) (q : Q)`)
  - Proposed restatement: the `pseudoMeasureIdeal` def in Phase 4b.
  - Cost: CHEAP mechanically; EXPENSIVE in prerequisites (the whole Iwasawa-algebra tower over GPlus).
  - Mathlib downstream this enables: unifies `zetaIdeal` (over 𝒢) + `zetaIdealPlus` (over 𝒢⁺) —
    currently two character-identical defs — and composes with `Ideal.span`, `Ideal.map`,
    `Ideal.Quotient` exactly as the 19 call sites of `zetaIdealPlus` (and ~34 of `zetaIdeal`) use them.
  - Real mathematical improvement: removes the project's *own* duplication. `zetaIdealPlus` is the
    living proof that the abstraction is warranted — it is the second copy. That is genuine
    organisation, not abstraction-for-its-own-sake.
```

**Honesty note.** The `pseudoMeasureIdeal` abstraction is mathematically real here in a way it
only *anticipated* for the twin: `zetaIdealPlus` is the concrete second instance, so the
de-duplication is not speculative. Yet the abstraction is also so general that it is nearly
content-free on its own (any element of any fraction ring against any ideal gives an ideal —
close to `Ideal.comap` of a scaled coset; see Phase 6). The *mathematical* object worth having
in mathlib is the **specific** `I(𝒢⁺)ζ_p` *together with its theorems* (`zetaIdealPlus_eq_span`,
the main-conjecture quotient `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, the descent `projPlus_zetaIdeal_le_zetaIdealPlus`),
and those require `ζ_p⁺` and `Λ(𝒢⁺)` to exist. This tension is exactly the human judgment Phase 7
surfaces.

---

### Diamond / defeq risk — `PadicMeasure.zetaIdealPlus`

`zetaIdealPlus` is a `def` producing a **bundled `Ideal`** (a term of an existing structure
type), **not** a `class`, `instance`, `abbrev`, or coercion. It registers no typeclass instance
and creates no new typeclass-search target. The probes below are therefore mostly
n/a-by-construction, but each row is checked. (Reasoned from source; no `#synth`/`rfl` probe run
because the build was not re-run — see Baseline — but the structural facts below are visible
directly in the source.)

| # | Risk                          | Verdict   | Evidence / rationale                                                |
|---|-------------------------------|-----------|---------------------------------------------------------------------|
| 1 | Typeclass diamond            | none      | Not an instance. It is a plain `def : Ideal …`. No instance-resolution path is added; consumers refer to it by name (`zetaIdealPlus p hp2`), not by typeclass search. |
| 2 | Reducibility leak            | none      | Not `@[reducible]`; sealed `noncomputable` def (inside `noncomputable section`). Body is a structure literal — even if unfolded, defeq-checking sees only the four fields. `mem_zetaIdealPlus_iff` is proved by `Iff.rfl`, confirming the carrier is the obvious set with no surprising reduction. |
| 3 | Non-canonical unfolding      | none      | `mem_zetaIdealPlus_iff := Iff.rfl` shows membership unfolds exactly to the intended `∃ l ∈ I(𝒢⁺), …`. Call sites use it through the `Ideal` API (`mem_map_iff_of_surjective`, `Quotient.mk`, `span`), never by unfolding. One subtlety: the carrier uses `toQPlus p` rather than `algebraMap` directly — `toQPlus` is a *named* `def` for `algebraMap … (QuotientFieldPlus p)`, introduced deliberately (its docstring: "the raw `algebraMap` keeps an unresolved instance metavariable inside `def`-bodies over the quotient group — a known elaboration-order trap; naming it sidesteps the postponement"). This is itself a defeq-management choice and works correctly here; it does not leak. |
| 4 | Instance priority collision  | n/a       | Not an instance — no priority. |
| 5 | Universe-polymorphism issues | none      | All types are monomorphic (`Type 0`: `PadicMeasure p (GPlus p)`, `QuotientFieldPlus p`). No universe variable introduced or forced. |
| 6 | Coercion ambiguity           | none      | No `CoeFun`/`CoeSort` defined. The only coercion in use is the standard `Ideal → Set` (`SetLike`) and `Λ(𝒢⁺) ↠ Λ(𝒢⁺)/I` (`Ideal.Quotient.mk`) — both mathlib's existing machinery; no competition. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE** (a bundled `Ideal`, not an instance/coercion/reducible def).
Top risks: none.
Recommended mitigations: none required. (Were the `pseudoMeasureIdeal` generalisation from Phase
4c pursued, it would also be a plain `def`, re-introducing no risk. Note the `toQPlus`-vs-raw-
`algebraMap` choice is a *helpful* defeq barrier, not a risk.)

---

### Mathlib search-status: `PadicMeasure.zetaIdealPlus`

[A] Lean-Finder       n/a — Lean-Finder MCP not configured in this environment (ToolSearch found no such tool).
[B] Loogle            n/a — `lean_loogle` MCP not configured in this environment (ToolSearch found no such tool).
[C] LeanSearch        n/a — `lean_leansearch` MCP not configured in this environment (ToolSearch found no such tool).
[D] Grep mathlib src  Ran over the full `.lake/packages/mathlib/Mathlib/` tree (the authoritative method here):
    - `pseudoMeasure` / `pseudo-measure` / `PseudoMeasure` → **0 hits** (no pseudo-measure concept, plus-part or otherwise).
    - `padicZeta` / `KubotaLeopoldt` / `Kubota` → **0 hits** (no p-adic zeta function, no `padicZetaPlus`).
    - `Iwasawa` → 4 files, **all unrelated**: `GroupTheory/GroupAction/Iwasawa.lean` is the *Iwasawa criterion / IwasawaStructure* for group simplicity; the others (`Alternating/Simple`, `Projectivization/PSL/Stabilizer`, `GeneralLinearGroup/Basic`) merely reference it. **No Iwasawa algebra.**
    - `augmentationIdeal` / `AugmentationIdeal` → **0 hits** in the group/measure-algebra sense (mathlib's only nearby `RingTheory/Ideal/IsAugmentation.lean` is the general-algebra splitting notion `A = R ⊕ I`, not `ker(deg)` of a group algebra).
    - `GPlus` / `QuotientFieldPlus` → **0 hits** (no even-part Galois group, no total fraction ring of an even-part measure algebra).
[E] Name pattern      n/a — `lean_local_search` MCP not configured; substituted by the grep name-patterns under [D] (`*augmentation*`, `*Iwasawa*`, `*Zeta*`, `*pseudoMeasure*`, `*GPlus*`, `*QuotientFieldPlus*`).

Searched for both:
  - the user's current form (`I(𝒢⁺)ζ_p` over the even part) — absent.
  - the literature-standard / general form (`I(G)·q` for a pseudo-measure `q ∈ Q(G)` over an
    Iwasawa algebra `Λ(G)`, and the abstract `pseudoMeasureIdeal (I : Ideal Λ) (q : Q)`) — absent.
    The abstract version's *building blocks* (`Ideal`, `Algebra`, `IsLocalization`, `Ideal.comap`)
    exist, but the assembled construction does not (see Phase 6).

Concluded: **not in mathlib** (method D exhausted over the full source; the A/B/C/E MCP-backed
methods are not configured in this environment and are recorded n/a with reason). Decisively,
**every prerequisite is also absent**: no Iwasawa algebra of measures, no even-part Galois group
`GPlus`, no total-fraction-ring (plus-)pseudo-measure framework, no augmentation ideal in this
sense, no Kubota–Leopoldt `ζ_p` and no descent `ζ_p⁺`. `zetaIdealPlus` cannot be a
specialisation of anything mathlib currently has.

---

### Call sites — `PadicMeasure.zetaIdealPlus`

Internal use count: **K = 19 lines** (within the project, NOT counting the declaring file), all
concentrated in the project's headline theorem file — a load-bearing definition on the even side.
External-to-file callers: **1 distinct file** — `IwasawaProof/Main.lean` (the Iwasawa Main
Conjecture proof). The declaring file itself adds `mem_zetaIdealPlus_iff` (`Iff.rfl`) and
`zetaIdealPlus_eq_span`.

| Caller file:line                              | Usage pattern (one-line excerpt)                                                       |
|-----------------------------------------------|----------------------------------------------------------------------------------------|
| IwasawaProof/Main.lean:631–632                | `zetaIdealPlus_eq_map_projPlus`: `PadicMeasure.zetaIdealPlus p hp2 = …` (descent identity) |
| IwasawaProof/Main.lean:646                    | `rw [PadicMeasure.zetaIdealPlus_eq_span p hp2 hb_gen hν, …]`                            |
| IwasawaProof/Main.lean:652–655                | `projPlus_zetaIdeal_le_zetaIdealPlus`: `PadicMeasure.projPlus p μ ∈ … zetaIdealPlus p hp2` |
| IwasawaProof/Main.lean:664                    | `PadicMeasure p (PadicMeasure.GPlus p) ⧸ PadicMeasure.zetaIdealPlus p hp2` (the **plus-side main-conjecture quotient** `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`) |
| IwasawaProof/Main.lean:666,678                | `Ideal.Quotient.mk (PadicMeasure.zetaIdealPlus p hp2) (PadicMeasure.projPlus p (Col p u))` |
| IwasawaProof/Main.lean:693                    | `… ⧸ PadicMeasure.zetaIdealPlus p hp2` (target of the descent isomorphism)             |
| IwasawaProof/Main.lean:704                    | `Ideal.Quotient.eq_zero_iff_mem.2 (projPlus_zetaIdeal_le_zetaIdealPlus p hp2 hmem)`    |
| IwasawaProof/Main.lean:798,801,839            | `… ∈ PadicMeasure.zetaIdealPlus p hp2`; `Ideal.mem_map_iff_of_surjective`              |
| IwasawaProof/Main.lean:893                    | `… ⧸ PadicMeasure.zetaIdealPlus p hp2` (final descent statement)                        |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `zetaIdealPlus`?):
  - (none) — every site goes through the named `zetaIdealPlus`; there is no inline re-derivation.

What the call-sites pattern tells us: K ≥ 3 internal uses, all in the project's headline
even-side main-conjecture argument, with **zero** inline re-derivation → this is **real,
depended-upon API**. The call-site signal points firmly to a **YES-\*** bucket *on the merits of
the object*. It does **not**, by itself, resolve the generality/prerequisite/duplication
questions — which is why the final verdict is BORDERLINE rather than NO. (Fewer call sites than
the twin `zetaIdeal` (~34), as expected: the plus side is the smaller half of the descent.)

### Composition check (Phase 6)

Can `zetaIdealPlus` be derived from mathlib in ≤3 chained calls?

Attempt 1 (abstract `pseudoMeasureIdeal` as a mathlib composition): is
`{x | ∃ l ∈ I, algebraMap x = algebraMap l * q}` expressible as e.g.
`(I.map (algebraMap Λ Q) * q-stuff).comap (algebraMap Λ Q)` or similar?
  - Mathlib decls that would be involved: `Ideal.map`, `Ideal.comap`, `Submodule.span`,
    scalar-multiplication of a submodule by a fixed element.
  - Result: **fails** — there is no single mathlib operation "ideal `I` of `Λ`, scaled by a
    *fixed element `q` of the fraction ring `Q`*, then pulled back to `Λ`". `q` is not an element
    of `Λ`, so `I * (q)` is not an ideal operation inside `Λ`; the pull-back of the `Q`-submodule
    `algebraMap(I)·q` along `algebraMap` is exactly what the four hand-written closure proofs
    establish, and assembling it from `Ideal.comap` + a `q`-scaled submodule would need several
    lemmas (and a `Submodule Q Q` scalar action), well over 3 calls.
  - Notes: even the *abstract* generalised def is not a clean ≤3-call mathlib composition.

Attempt 2 (the concrete `zetaIdealPlus` itself): impossible to compose — its very type mentions
`PadicMeasure (GPlus p)`, `QuotientFieldPlus`, `augmentationIdeal`, `padicZetaPlus`, **none of
which exist in mathlib** (Phase 5). There is nothing to compose *from*.

Attempt 3 (compose from the `𝒢`-side twin `zetaIdeal` via `projPlus`): the project proves
`zetaIdealPlus = (zetaIdeal).map projPlus`-style identities (`zetaIdealPlus_eq_map_projPlus`),
but `zetaIdeal` is *itself* not in mathlib, and the equality is a **theorem with a real proof**
(it goes through `zetaIdealPlus_eq_span` + surjectivity of `projPlus`), not a ≤3-call
composition. So this does not make `zetaIdealPlus` mathlib-composable either.

Conclusion: **NOT-COMPOSABLE.** (The concrete object's building blocks are entirely absent from
mathlib; the abstract form is >3 calls; and the relation to the twin is a proved theorem, not a
composition.)

---

## Verdict: `PadicMeasure.zetaIdealPlus`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the concept `I(𝒢⁺)ζ_p` is **canonical** — the RHS of Iwasawa's
  Main Conjecture on the even/plus side (Coates–Sujatha Ch. 4; RJW arXiv:2309.15692 §11.2,
  Prop. TeX 3052, which states it in the *same sentence* as the `𝒢`-side twin: "`I(Γ)ζ_p` is an
  ideal in `Λ(Γ)`, **and similarly `I(Γ⁺)ζ_p` is an ideal in `Λ(Γ⁺)`**"). The Lean form matches
  the standard form exactly, specialised to the even part `G⁺ = ℤ_p^× / {±1}`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — two specialisation axes
  (the group `G`, fixed to `𝒢⁺`; the pseudo-measure `q`, fixed to `ζ_p⁺`). Phase 4c offers a
  CHEAP-to-write abstract `pseudoMeasureIdeal` that would de-duplicate `zetaIdeal`/`zetaIdealPlus`
  — and `zetaIdealPlus` is the *concrete proof* that the duplication exists.
- Mathlib search (Phase 5): **not in mathlib** — and crucially **no prerequisite is either**
  (no Iwasawa algebra, no `GPlus`, no (plus-)pseudo-measure framework, no augmentation-of-measure
  -algebra ideal, no `ζ_p`/`ζ_p⁺`). Method D (full-source grep) exhausted; A/B/C/E MCPs n/a.
- Composition check (Phase 6): **NOT-COMPOSABLE** (no building blocks in mathlib; abstract form
  >3 calls; the relation to the twin is a proved theorem, not a composition).
- Risk (Phase 4.5): **NONE** (a bundled `Ideal`, not an instance/coercion).
- Call sites (Phase 6.0): **K = 19**, one external file (`IwasawaProof/Main.lean`), zero inline
  re-derivation — real, load-bearing API on the even side.

**Rationale.**
This is the situation the rubric reserves for BORDERLINE: every *individual* phase points toward
"novel and worth having", yet **synthesising them requires judgment the skill cannot ground in the
evidence** — and the synthesis is *more* clear-cut toward "abstract first" than for the twin,
because `zetaIdealPlus` is the literal second copy of `zetaIdeal`. On the merits, `I(𝒢⁺)ζ_p` is a
genuinely standard, genuinely-missing, genuinely-used object — the even-side right-hand side of
Iwasawa's Main Conjecture, with 19 dependent call sites in the headline proof, not composable, no
defeq risk. Those facts alone read as a YES. But two things block a clean YES, and neither is mine
to decide.

First, **generality and duplication**: Phase 4 found the Lean form strictly narrower than the
literature standard (fixed group `𝒢⁺`, fixed pseudo-measure `ζ_p⁺`), and — unlike for the twin,
where the second instance was only *anticipated* — here the second instance **is this very
declaration**. `zetaIdeal` (over `𝒢`) and `zetaIdealPlus` (over `𝒢⁺`) are character-identical
constructions differing only in the group and the pseudo-measure; their three closure proofs are
byte-for-byte the same. Shipping *both* to mathlib as separate defs would be exactly the kind of
duplication mathlib rejects. Under the rubric this pushes hard toward `YES-but-generalise-first`
with the abstract `pseudoMeasureIdeal (I, q)` as the target. Second, and decisively, **the
generalisation target is itself entirely absent from mathlib**: there is no Iwasawa algebra of
measures, no even-part Galois group, no total-fraction-ring pseudo-measure, no augmentation ideal
in this sense, and no Kubota–Leopoldt zeta function. So `zetaIdealPlus` is not a leaf one
upstreams in isolation — it is one capstone of a five-deep tower of equally-novel prerequisites,
and the meaningful mathlib contribution is "the whole Iwasawa-algebra / pseudo-measure framework
(with the general `(G, q)` ideal construction specialising to *both* `𝒢` and `𝒢⁺`)", not "this one
even-side ideal". Whether to abstract the bare ideal-construction (nearly content-free on its own —
Phase 6 shows even the abstract form is non-trivial to compose, but it is close to a generic
pre-image-of-a-scaled-submodule) versus to upstream the specific `I(G)ζ_p`/`I(G⁺)ζ_p` together with
their theorems (`zetaIdealPlus_eq_span`, the plus-side main-conjecture quotient `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`,
the descent `projPlus_zetaIdeal_le_zetaIdealPlus`) is a genuine taste/scope call. The rubric is
explicit that "too expensive to do the general form, so ship the narrow one" is itself a BORDERLINE
question for the user, not a self-resolving downgrade — precisely the corner we are in. The
project-specific name (vs. a mathlib convention) and the audience (currently internal to one
Iwasawa-theory formalisation, no downstream-library consumers) reinforce BORDERLINE. **Consistency:**
the sibling `zetaIdeal` received `BORDERLINE-needs-human` for the same reasons, as did the
deep-tower main-result objects `twistedZetaHalf` and `isPlusPseudoMeasure_padicZetaPlus` in this
project; `zetaIdealPlus` is the even-part analogue of `zetaIdeal` and must land in the same bucket.

**Refactor-actionable next step.** This is *not* a delete-and-inline (NO) case — keep
`zetaIdealPlus` exactly where it is; it is correct, sorry-free, well-named for the project, and
depended upon by 19 sites in the main proof. The action is to answer the scoping questions below;
the most likely resolution is `YES-but-generalise-first` — abstract `zetaIdeal` **and**
`zetaIdealPlus` into a single `pseudoMeasureIdeal (I, q)` and ship it as part of an Iwasawa-algebra
framework PR series — but that depends on a decision to upstream the *whole tower*, which is the
user's call. **This decl should be assessed and shipped *together with* `zetaIdeal`**, not separately
(see Q5).

**Numbered questions (≤5):**

1. **Upstreaming scope.** Is the plan to upstream the *entire* Kubota–Leopoldt / Iwasawa-algebra-of
   -measures / pseudo-measure framework to mathlib (`PadicMeasure`, `GPlus`, `QuotientFieldPlus`,
   `IsPlusPseudoMeasure`, `augmentationIdeal`, `padicZetaPlus`)? If **no**, then `zetaIdealPlus`
   cannot go to mathlib at all (its type mentions five absent prerequisites) → it stays
   project-local and drops out of mathlib consideration. If **yes**, proceed to Q2.

2. **Generality / de-duplication.** When the framework is upstreamed, should `zetaIdeal` and
   `zetaIdealPlus` be **merged** into one abstract `pseudoMeasureIdeal (I : Ideal Λ) (q : Q)` (Phase
   4c — CHEAP to write, and `zetaIdealPlus` is the living proof the duplication is real), with the
   two named ideals as one-line specialisations? Or should the cyclotomic and even-part ideals each
   be their own named object? (Mathlib's iron rule strongly favours the merge.)

3. **Right grain.** Is the mathlib-worthy unit the *bare ideal construction* (`pseudoMeasureIdeal`,
   which on its own is close to a generic pre-image-of-a-scaled-submodule and may be too thin), or
   the *named `I(G⁺)ζ_p` packaged with its theorems* (`zetaIdealPlus_eq_span`, the plus-side
   quotient `Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, the descent `projPlus_zetaIdeal_le_zetaIdealPlus`)? The latter is the
   real mathematical content but is inseparable from `ζ_p⁺` and `Λ(𝒢⁺)`.

4. **Audience / naming.** `zetaIdealPlus` currently has only in-project consumers (no downstream
   library). For mathlib, would it be renamed to a convention-compliant form (e.g.
   `Iwasawa.zetaIdealPlus` / the abstract `pseudoMeasureIdeal`), and is the audience broad enough to
   justify inclusion now versus after the surrounding framework lands?

5. **Bundling with the twin.** Should `zetaIdealPlus` be evaluated and PR'd **as one unit with
   `zetaIdeal`** (they are the same construction over `𝒢` and `𝒢⁺`, and the project relates them via
   `zetaIdealPlus_eq_map_projPlus`)? Assessing or upstreaming either in isolation invites exactly
   the duplication mathlib forbids.

Next action: user answers the questions; re-run `/mathlibable PadicMeasure.zetaIdealPlus` (jointly
with `PadicMeasure.zetaIdeal`) once the `G`-generality (Q2) and packaging (Q3) are chosen. Most
likely landing if Q1 = yes: `YES-but-generalise-first` — a single abstract `pseudoMeasureIdeal`
subsuming both ideals, shipped with the Iwasawa-algebra framework. If Q1 = no: drop from mathlib
consideration; keep project-local under its current name (do not delete or inline — it is correct
and load-bearing).

---

## Next step

User answers the five numbered questions above, **treating `zetaIdealPlus` and `zetaIdeal` as one
unit** (Q5). If the Iwasawa-algebra / pseudo-measure framework is being upstreamed (Q1 = yes),
re-run `/mathlibable` on the pair after deciding the generality (Q2) and grain (Q3) — the expected
resolution is `YES-but-generalise-first`: merge `zetaIdeal` + `zetaIdealPlus` into one abstract
`pseudoMeasureIdeal (I, q)` via `/generalise`, then ship as part of the framework PR series. If the
framework is **not** going to mathlib (Q1 = no), `zetaIdealPlus` drops out of mathlib consideration
and remains project-local under its current name. In all cases, leave the declaration in the project
untouched.
