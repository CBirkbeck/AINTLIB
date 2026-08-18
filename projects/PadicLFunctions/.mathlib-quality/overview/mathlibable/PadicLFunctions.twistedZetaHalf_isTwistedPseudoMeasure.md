# `/mathlibable` report — `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-19. Verdict at the bottom.

**Final verdict: `BORDERLINE-needs-human`.**

> The mathematics — a **pseudo-measure** in the sense of Coates–Serre (an element `q`
> of the total fraction ring `Q(G)` of the Iwasawa algebra with `([g]−[1])·q ∈ Λ(G)`
> for all `g`), here in the x-**twisted** form `(g·[g]−[1])·A₀ ∈ Λ(ℤ_p^×)` that the
> Λ-adic Eisenstein family forces (RJW Def 3.34 + the project's **erratum #11**) — is
> **classical and canonical**. But this specific Lean theorem is stated **entirely over a
> project-local tower** (`PadicMeasure`, the Iwasawa algebra `Λ(ℤ_p^×)`, its fraction ring
> `Q(ℤ_p^×)`, `IsPseudoMeasure`, `padicZeta`, the twist `quotientTwist`/`unitsTwist`,
> `twistedZetaHalf`), **none of which is in mathlib**. So the four mechanical buckets all
> fail their gates (mathlib has nothing to specialise from; nothing to compose from; the
> statement cannot be shipped ahead of its whole foundation). Whether that foundation should
> go to mathlib at all, and whether this *deliberately weakened, family-specific* "twisted
> pseudo-measure" lemma (`K = 0` consumers — it documents erratum #11 rather than feeding any
> proof) deserves a mathlib home, are taste/policy judgments the skill cannot ground in the
> evidence. Numbered questions for the user are in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task BUILD NOTE
  — `lake build` is stale/slow in this checkout; `projects/PadicLFunctions/.lake/build` is
  absent and the workspace `.lake/packages/mathlib` is dated 2026-06-17). The declaration and
  its full dependency chain were read directly from source, exactly as the skill's Phase-0
  fallback allows.
- decl `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:246`
- kind:                      theorem
- has sorry:                 **no** — `grep -nE "sorry|admit"` over `EisensteinFamily.lean`
  returns nothing; the declaration and every dependency (`twistedZetaHalf`, `padicZeta`,
  `padicZeta_isPseudoMeasure`, `quotientTwist`, `unitsTwist`, `QuotientField`, `PadicMeasure`,
  `IsPseudoMeasure`) are complete, sorry-free proofs/definitions.
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8, TeX 2361–2446)."
  The Kubota–Leopoldt pseudo-measure interpolates the constant coefficients of the p-stabilised
  Eisenstein series `E_k^{(p)}`; the non-constant coefficients are divisor-sum Dirac measures
  `A_n`. The file records two deviations from the source, the relevant one being **erratum #11**
  (the corrected form of RJW Theorem 2403(a) — see Phase 1).

```lean
/-- R8 (replan R8.1, **erratum #11**): the corrected form of RJW TeX 2403(a).
The notes claim `A₀ = x·ζ_p/2` is a pseudo-measure; with Def 3.34 this is
false (the pole of `x·ζ_p` sits at the character `x⁻¹`, not at the trivial
character — see `.mathlib-quality/errata.md` #11). What holds, and what the
family needs, is the x-twisted analogue: `(g·[g] − [1])·A₀ ∈ Λ(ℤ_p^×)` for
every `g`. -/
theorem twistedZetaHalf_isTwistedPseudoMeasure (hp2 : p ≠ 2) (g : ℤ_[p]ˣ) :
    ∃ ν : PadicMeasure p ℤ_[p]ˣ,
      algebraMap _ (PadicMeasure.QuotientField p)
          ((g : ℤ_[p]) • PadicMeasure.dirac p g - 1)
        * twistedZetaHalf p hp2 = algebraMap _ _ ν := by
  obtain ⟨νg, hνg⟩ := PadicMeasure.padicZeta_isPseudoMeasure p hp2 g
  exact ⟨_, twistedZetaHalf_witness_eq p hp2 g νg hνg⟩
```

(Note: `.mathlib-quality/errata.md` referenced in the docstring does not exist on disk in this
checkout — the errata are carried inline in the docstrings. This does not affect the assessment.)

---

### Statement (Phase 1)

`PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure` is **a theorem** stating the following.

Let `p` be an odd prime (`p ≠ 2`) and let `g ∈ ℤ_p^×`. Write `A₀ = twistedZetaHalf = x·ζ_p/2`
for the constant coefficient of the Λ-adic Eisenstein family — the x-twist of the
Kubota–Leopoldt p-adic zeta pseudo-measure `ζ_p`, halved — viewed inside the total fraction
ring `Q(ℤ_p^×) = Frac(Λ(ℤ_p^×))` of the Iwasawa algebra. Then there exists an honest measure
`ν ∈ Λ(ℤ_p^×)` (a `ℤ_[p]`-linear functional on `C(ℤ_p^×, ℤ_[p])`) such that

  `(g·[g] − [1]) · A₀ = ν` in `Q(ℤ_p^×)`,

i.e. **multiplying `A₀` by the twisted group-ring element `g·[g] − [1]` clears the denominator
and lands back in `Λ(ℤ_p^×)`.** This is the x-twisted analogue of the *pseudo-measure* property
(RJW Def 3.34: `λ ∈ Q(G)` is a pseudo-measure iff `([g]−[1])·λ ∈ Λ(G)` for all `g`).

The crucial mathematical subtlety — recorded as the project's **erratum #11** — is that `A₀`
is **NOT** an honest pseudo-measure: the source (RJW Theorem 2403(a)) claims it is, but with the
source's own Def 3.34 that is false, because the pole of `x·ζ_p` sits at the character `x⁻¹`, not
at the trivial character. The element `[g]−[1]` does *not* clear it; the **twisted** element
`g·[g]−[1] = τ([g]−[1])` (where `τ` is the x-twist) does. So this theorem is the deliberately
*weakened, twist-corrected* statement — exactly what the Eisenstein family construction needs and
nothing more.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `hp2 : p ≠ 2` — oddness; needed because `A₀` contains the factor `½ = (2:ℤ_[p])⁻¹`, a unit
  only for odd `p` (`isUnit_two_padicInt`).
- `g : ℤ_[p]ˣ` — the unit at which the (twisted) augmentation element is taken.

Hypotheses (Lean side): `hp2 : p ≠ 2` only (beyond the ambient `Fact p.Prime`).

Conclusion (math): the twisted augmentation element `g·[g]−[1]` clears `A₀`'s denominator —
`A₀` is a *twisted* pseudo-measure.

Conclusion (Lean):
`∃ ν : PadicMeasure p ℤ_[p]ˣ, algebraMap _ (QuotientField p) ((g:ℤ_[p]) • dirac p g - 1) * twistedZetaHalf p hp2 = algebraMap _ _ ν`.

**Objects this statement is built from (all project-local; none in mathlib):**

| Symbol | Where | What it is | In mathlib? |
|---|---|---|---|
| `PadicMeasure p X := C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` | `Measure/Basic.lean:52` | p-adic measures = `ℤ_[p]`-linear functionals on `C(X,ℤ_[p])` (RJW Def 3.6) | **No** |
| `QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` | `Measure/PseudoMeasure.lean:804` | total fraction ring `Q(ℤ_p^×)` of `Λ(ℤ_p^×)` (RJW Def 3.34) | **No** |
| `IsPseudoMeasure q := ∀g, ∃ν, ([g]−1)·q = ν` | `Measure/PseudoMeasure.lean:811` | the pseudo-measure predicate (RJW Def 3.34) | **No** |
| `dirac p g` | `Measure/Basic.lean:64` | the functional `f ↦ f g`; here `[g]` in the group ring | **No** (the linear-functional encoding) |
| `padicZeta p hp2` | `KubotaLeopoldt/ZetaP.lean:252` | Kubota–Leopoldt p-adic zeta `ζ_p` (RJW Def 4.10) | **No** |
| `padicZeta_isPseudoMeasure` | `KubotaLeopoldt/ZetaP.lean:269` | `ζ_p` is a pseudo-measure (RJW Prop 4.11) — the input this proof consumes | **No** |
| `unitsTwist` / `quotientTwist` | `EisensteinFamily.lean:115/167` | x-twist `[g]↦g·[g]` on `Λ`, as `≃+*` / extended to `Q` | **No** |
| `twistedZetaHalf` | `EisensteinFamily.lean:186` | `A₀ = x·ζ_p/2` (the def this theorem is about) | **No** |

The only mathlib pieces touched are *generic* infrastructure: `ℤ_[p]` (`Mathlib/NumberTheory/Padics/`),
`FractionRing`/`IsLocalization`/`algebraMap` (`Mathlib/RingTheory/Localization/`), `•`, `LinearMap`.

Proof body (2 lines): `obtain ⟨νg, hνg⟩ := padicZeta_isPseudoMeasure p hp2 g` gives the *honest*
(untwisted) pseudo-measure witness for `ζ_p` at `g`; then the helper `twistedZetaHalf_witness_eq`
(`EisensteinFamily.lean:214`) transports it through the x-twist to a witness for the twisted form
on `A₀ = x·ζ_p/2`. The mathematical work lives in that helper (and in `padicZeta_isPseudoMeasure`);
this theorem is the clean public-facing existential wrapper.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline BIG/SMALL — recorded BIG for framing).
Reason: it is named after the **erratum #11** correction of a *named source theorem* (RJW TeX
2403(a)), and it is the realization of the canonical Coates–Serre **pseudo-measure** property —
both signals of "near the literature in some form". It is not a person-named theorem and is short,
but it is not a mere helper either; it is the corrected statement of a headline source claim. (As a
proof *about* the family it is also fairly close to SMALL — a single-`g` existence wrapper. The
classification does not gate anything; the literature width was EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.**
(The one-line-def exemption analysis applies only to `def`/`abbrev`/`structure`; for a proof the
section is skipped. The 2-line proof is noted for the call-sites / composition discussion, not as a
def-inclusion signal.)

---

### Literature search table — EXHAUSTIVE protocol

The mathematical concept is the **pseudo-measure** (Coates–Serre): an element of the total fraction
ring of the Iwasawa algebra annihilated *into* `Λ` by the augmentation-type elements `[g]−[1]` — and
its x-**twisted** variant forced by erratum #11. The project objects (`twistedZetaHalf`, `padicZeta`,
`QuotientField`, the twist) are searched as context.

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `"pseudo-measure" p-adic L-function "([g]-[1])" Iwasawa algebra regular augmentation ideal definition` | yes | a pseudo-measure is an element `λ` of `Frac(Λ)` with `([g]−1)·λ ∈ Λ` ∀g | Coates' definition; the RJW notes (arXiv:2309.15692) + Williams' lecture notes are the exact source; the `[g]−1` augmentation elements are the standard "regular" annihilators. |
| 2 | WebSearch (general form) | `pseudo-measure Iwasawa algebra p-adic zeta function total fraction ring Lambda(Z_p^times) definition Coates Wiles` | yes | "Pseudomeasures were introduced by J. Coates as elements of the **fraction field of the Iwasawa algebra**; defined by their Mellin transform, extended by universality from `Λ=ℤ_p[[T]]` to the whole fraction field" | Coates–Sujatha *Cyclotomic Fields and Zeta Values*; `ζ_p` is a pseudo-measure on `Γ ≅ ℤ_p^×`. The "extend by universality to the fraction field" is **exactly** the project's `Q(ℤ_p^×) = Frac(Λ)` + `IsLocalization` framing. |
| 3 | WebSearch (named-after / Serre form) | `Serre pseudo-measure p-adic zeta function group ring fraction field augmentation Q(G) Lambda` | yes | "Serre's p-adic zeta pseudomeasure … the p-adic analogue of `ζ_K(s)` should be a **pseudo-measure** on `Gal(K_{ab,p}/K)`" | Confirms the Serre/Coates lineage and the `Q(G)` (fraction ring of the group/Iwasawa algebra) home. The notation `Q(G)` matches RJW Def 3.34 verbatim. |
| 4 | WebSearch (twist-specific, erratum #11) | `Lambda-adic Eisenstein family constant term x times zeta_p twist not a pseudo-measure pole trivial character Rodrigues Jacinto Williams` | partial | Serre bootstrap: interpolating the **non-constant** Eisenstein coefficients forces the **constant term** = (a twist of) `ζ_p`; the constant term is "a measure = element of the Iwasawa algebra" | Located the source (RJW arXiv:2309.15692, ESSENTIAL NUMBER THEORY 2025) and the standard bootstrap, but **no source crystallises the "twisted pseudo-measure / `g·[g]−1`" correction as a named object** — consistent with this being the project's erratum #11, a local correction of RJW Thm 2403(a). |
| 5 | ChatGPT MCP | (intended: standard definition + generality + historical evolution of "pseudo-measure") | n/a | — | **ChatGPT MCP not configured** this session (`~/.claude` has no chatgpt MCP entry; no `.mcp.json`). Substituted extra WebSearch/WebFetch depth (rows 1–4, 6, 9, 10) per the skill's MCP-absent fallback. The historical question ("introduced by Coates; Serre lineage; extend-by-universality") was answered by rows 1–3. |
| 6 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | n/a | (both directories absent) | No project references dir; no `refs/` PDFs present (the `ln -s ../AINTLIB/refs refs` symlink is not set up in this checkout). The source paper (RJW arXiv:2309.15692, Def 3.34) is cited inline in the docstrings. Recorded n/a with reason. |
| 7 | nLab | WebSearch/knowledge: nLab "pseudomeasure" / "p-adic L-function" | partial | nLab discusses p-adic L-functions and the Iwasawa Main Conjecture, but has **no dedicated "pseudo-measure" page** isolating the `([g]−1)·λ ∈ Λ` definition | The abstract definition lives in Coates–Wiles / Coates–Sujatha and the RJW notes, not nLab. The categorical content (fraction ring of a group algebra) is generic. |
| 8 | nCatLab / Stacks Project | — | n/a | — | **Not a categorical concept** (no universal property beyond `IsLocalization`, already mathlib-idiomatic) and **not an algebraic-geometry concept** — Stacks has no Iwasawa-algebra / p-adic-L content. Recorded n/a with reasons. |
| 9 | MathOverflow / Math.StackExchange | "pseudomeasure Iwasawa algebra fraction field" (via rows 1–3 result sets) | yes | recurring confirmation that a pseudo-measure is "an element of `Frac(Λ)` killed into `Λ` by augmentation elements; `ζ_p` is the canonical example" | The "non-abelian pseudomeasures" literature (arXiv:0711.0581) generalises the same `([g]−1)`-annihilator definition to non-commutative `Λ` — confirming the definition is *the* standard one. |
| 10 | recent arXiv (last ≤5 years) | `Lean mathlib formalization Kubota-Leopoldt p-adic L-function pseudo-measure Iwasawa algebra` + `Rodrigues Jacinto Williams ... arXiv 2309.15692` | yes | RJW arXiv:2309.15692 §3.34 (pseudo-measure) + §8 (Eisenstein family); Narayanan arXiv:2302.14491 (the **only** Lean p-adic-L formalization) | RJW is the **exact source** (Def 3.34 + Thm 2403(a)). Narayanan's is **Lean 3, standalone** (`github.com/laughinggas/p-adic-L-functions`), **never upstreamed to mathlib**, and per WebFetch of the PDF **does not even use the pseudo-measure-as-fraction-ring formalism** — it builds p-adic L-functions via distributions/measures on `ℤ_p`. So there is *no* prior pseudo-measure formalization anywhere, let alone in mathlib. |

The protocol passed: WebSearch ran 4 distinct queries spanning the specific form (row 1), the
most-general/origin form (row 2), the named-after/Serre form (row 3), and the twist-specific
erratum context (row 4); the ChatGPT MCP row is honestly recorded n/a (tool unavailable) with the
fallback substitution noted; local references checked (absent → n/a with reason); nLab checked
(partial — no dedicated page); nCatLab/Stacks recorded n/a with reasons; MathOverflow/SE perspective
captured (row 9); recent arXiv located the exact source paper *and* the (Lean-3, non-mathlib) prior
formalization (row 10).

### Literature summary (Phase 3)

Concept identified as: the **pseudo-measure** of Coates–Serre — an element `λ` of the total
fraction ring `Q(G) = Frac(Λ(G))` of the Iwasawa algebra `Λ(G)` such that `([g]−[1])·λ ∈ Λ(G)`
for every `g ∈ G` — specialised to `G = ℤ_p^×` and `λ = A₀ = x·ζ_p/2`, and **twisted** by the
x-twist `τ` so that the annihilating element is `g·[g]−[1] = τ([g]−[1])` (erratum #11).

Sources agree on the standard form: **yes** for the pseudo-measure definition itself (Coates;
Serre; Coates–Sujatha; RJW Def 3.34; non-abelian generalisations arXiv:0711.0581 all use the same
`([g]−[1])`-annihilator condition over `Frac(Λ)`). The **twisted** variant `(g·[g]−[1])·A₀ ∈ Λ` is
**not** a separately named literature object — it is the project's deliberate, correct weakening of
RJW Thm 2403(a) (erratum #11), needed because `A₀` is provably *not* an honest pseudo-measure.

Most general standard form: for a profinite abelian group `G` and `λ ∈ Q(G) = Frac(Λ(G))`,
`λ` is a pseudo-measure iff `([g]−[1])·λ ∈ Λ(G)` for all `g ∈ G` (Coates). `ζ_p` is the canonical
example. The declaration is the case `G = ℤ_p^×`, `λ = A₀`, with the augmentation element
**pre-composed with the x-twist**.

Generality dimensions where the literature varies:
- **The group `G`.** Most general: any profinite abelian (or even non-commutative, arXiv:0711.0581)
  group. Here `G = ℤ_p^×` is fixed.
- **Coefficients.** Most general: `𝒪_L`-valued measures (RJW §5). The project fixes `𝒪 = ℤ_[p]`
  and **explicitly defers** the general-`𝒪_L` case (`Measure/Basic.lean` docstring).
- **Annihilating element.** Standard: the augmentation elements `[g]−[1]`. Here: the **twisted**
  `g·[g]−[1]` — a project-specific (erratum #11) variant, not a literature-standard form.

Disagreement with the literature: the source (RJW Thm 2403(a)) **claims** `A₀` is a pseudo-measure;
the project shows (erratum #11) it is not, and proves the corrected twisted statement instead. This
theorem *is* the project's documented correction — it agrees with the *mathematics* (pseudo-measures
à la Coates) while correcting the source's specific over-claim.

If the literature search had returned nothing, that would signal "too narrow for mathlib"; here the
underlying pseudo-measure concept is firmly canonical, but the **specific twisted, single-coefficient,
project-corrected form** is bespoke — which is the tension Phase 7 resolves.

---

### Generality analysis — `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

Literature-standard form (from Phase 3): `λ ∈ Q(G)` is a pseudo-measure iff `([g]−[1])·λ ∈ Λ(G)`
∀g (Coates). The mathlib-idiomatic packaging of "λ is a pseudo-measure" is precisely the project's
own `IsPseudoMeasure` predicate (`Measure/PseudoMeasure.lean:811`) — already a clean bundled `Prop`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | the object `twistedZetaHalf p hp2` | the single coefficient `A₀ = x·ζ_p/2` | a general element `λ ∈ Q(G)` | NO (for this lemma) | The statement is *about this specific `A₀`*; "generalising the object" means proving a `IsTwistedPseudoMeasure`-style predicate for arbitrary `λ`, which is a *different* (more abstract) lemma, not a weakening of this one. The mathematical content here is that *`A₀`* (a twist of `ζ_p`) has the property. |
| 2 | the annihilating element `g·[g]−1` | the **twisted** augmentation element `τ([g]−1)` | the standard `[g]−1` | NO (mathematically forced) | erratum #11: `[g]−1` does **not** clear `A₀` (its pole is at `x⁻¹`); only the twisted `g·[g]−1` does. The twist is not an arbitrary narrowing — it is exactly what makes the statement *true*. Cannot be weakened to the untwisted form (it would be false). |
| 3 | the single `g` vs "∀g (predicate form)" | one `g` (a per-`g` existence) | `IsPseudoMeasure`-style `∀g` predicate | yes (cosmetic) | One could bundle as `∀g, ∃ν, …` — but that is exactly the shape of the existing `IsPseudoMeasure` predicate; the *twisted* analogue predicate is not defined in the project. This is a packaging choice (one `g` vs a bundled predicate), not a mathematical generalisation. See Phase 4c row 4. |
| 4 | coefficient ring `ℤ_[p]` (via `hp2`, the `½`) | p-adic integers; odd `p` | `𝒪_L`-valued (RJW §5) | yes (deferred) | The `p ≠ 2` hypothesis is forced by the `½` in `A₀`; the general-`𝒪_L` coefficient case is **deferred project infrastructure** (`Measure/Basic.lean` docstring), not a weakening available *now*. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** — it is the correct, mathematically
forced statement about *this* object. The "generalisations" on offer are not weakenings of this
lemma: row 1 (arbitrary `λ`) and row 3 (bundled `∀g` predicate) are *different, more abstract
declarations* — and, decisively, any such abstraction is still stated over the **project-local,
non-mathlib** `Q(ℤ_p^×)`/`PadicMeasure`/twist framework, so it does not yield a mathlib-worthy
statement either (same obstruction as Phase 5/6). Row 2 (the twist) is mathematically forced and
cannot be removed. Row 4 (`𝒪_L`) is a real future direction the project defers.

Number of weakening opportunities found: **0** that yield a *mathlib-worthy* statement (the two
"abstraction" directions produce different decls over a non-mathlib type; the coefficient direction
is deferred infrastructure).

Proposed restatement: **none.** (A bundled "twisted pseudo-measure" predicate over `Q(ℤ_p^×)` would
be a reasonable *project* refactor — see Phase 4c row 4 / Phase 7 Q2 — but it is not a mathlib
contribution, because `Q(ℤ_p^×)` is itself not in mathlib.)

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | no | — | Hypotheses are already minimal (`Fact p.Prime`, `p ≠ 2`); nothing to typeclass-ify. |
| 2 | sequences/metric → filters/topological? | no | — | No limit/convergence notion; this is an algebraic "clears the denominator" statement in a fraction ring. |
| 3 | construct an object where a universal-property class would characterise it? | no (already done) | — | The fraction ring is already `FractionRing`/`IsLocalization` (a universal property); the twist is already `IsLocalization.ringEquivOfRingEquiv`. The infrastructure is *already* mathlib-idiomatic. |
| 4 | set-with-closure-predicate → bundled-substructure type? **(or: bundle as a `Prop` predicate)** | partial | a `IsTwistedPseudoMeasure (q : Q(ℤ_p^×)) := ∀g, ∃ν, (g·[g]−1)·q = ν` predicate, mirroring the existing `IsPseudoMeasure` | This is the natural **project** idiom (bundle the `∀g` per-element form as a predicate, as `IsPseudoMeasure` already does). But the predicate is over `Q(ℤ_p^×)`, a **non-mathlib** type — no mathlib downstream. Flagged as a *project* refactor (Phase 7 Q2), **not** a mathlib modernisation. |
| 5 | vector-space/metric/field-specific → weaken to modules/(semi)ring? | partial | re-aim at an abstract pseudo-measure over `Frac(Λ(G))` for a general group ring `Λ(G) = MonoidAlgebra ℤ_[p] G` | This *is* the genuinely general/mathlib-shaped idea — but it requires first defining "Iwasawa algebra = `MonoidAlgebra`/completed group ring" and "pseudo-measure over its fraction ring" **as a new mathlib framework**. That is a large foundational move, not a restatement of this lemma. Flagged, not recommended here. |
| 6 | 1-categorical → higher/∞-categorical? | no | — | Not categorical beyond the generic localisation universal property. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive groups/monoids? | partial | `ℤ_p^×` → arbitrary profinite abelian `G` (matches the literature's full generality) | Again a *new framework* (pseudo-measures over general `Frac(Λ(G))`), not a weakening of this concrete lemma; no mathlib downstream until that framework exists. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a mathlib contribution).
Reason: every abstraction on offer (a bundled twisted-pseudo-measure predicate, row 4; an abstract
pseudo-measure over a general group-ring fraction field, rows 5/7) is stated over the project's
`Q(ℤ_p^×)`/`PadicMeasure`/Iwasawa-algebra framework, which is **not in mathlib**. The infrastructure
this lemma uses (`FractionRing`, `IsLocalization`, `IsLocalization.ringEquivOfRingEquiv` for the
twist, a bundled `≃+*`) is *already* in mathlib-idiomatic shape. There is no contemporary mathlib
idiom that turns *this* lemma into a better *mathlib* lemma; the only "modernisations" would require
first upstreaming a whole pseudo-measure / Iwasawa-algebra framework — a separate, much larger
question (Phase 7).

---

### Diamond / defeq risk — `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search paths are
introduced by a proof; Phase 4.5 is skipped per the skill's scope rule.)

### Risk verdict (Phase 4.5)

Overall risk: **n/a (theorem)**.

---

### Mathlib search-status: `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

[A] Lean-Finder — n/a: no Lean MCP / Lean-Finder configured this session. Substituted by
    authoritative direct mathlib-source grep [D] + name-pattern [E] over the local pinned mathlib
    (`.lake/packages/mathlib`, 2026-06-17) + the concept-level web search (Phase 3).
[B] Loogle (type-pattern) — n/a: no Lean MCP this session. The type `∃ ν, algebraMap … * (twist of
    ζ_p) = algebraMap ν` over the project's `QuotientField`/`PadicMeasure` is not expressible
    against mathlib types (those types do not exist in mathlib), so a Loogle type-pattern query has
    no mathlib target by construction. Substituted by [D]/[E].
[C] LeanSearch (NL) — n/a: no Lean MCP this session. The NL concept ("a twist of the p-adic zeta
    pseudo-measure becomes an honest measure after multiplying by `g·[g]−1`") is covered by the
    Phase-3 literature search + the greps below.
[D] Grep mathlib src — terms tried: `pseudo.?measure`, `pseudoMeasure`, `PseudoMeasure`, `kubota`,
    `leopoldt`, `padicLFunction`, `p.adic.zeta`, `IwasawaAlgebra`, `padicZeta`, `twistedZeta`,
    `unitsCmul`, `unitsPowCM`, `augmentationIdeal`, `FractionRing.*MonoidAlgebra`,
    `MonoidAlgebra.*FractionRing`, `dirac.*sub.*one`. **0 hits** for every pseudo-measure /
    Kubota–Leopoldt / Iwasawa-algebra / project-object term.
[E] Name pattern — `*iwasawa*` in mathlib resolves to **only**
    `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` (the **Iwasawa decomposition of a group action** —
    an entirely unrelated concept). `twistedZetaHalf`, `IsPseudoMeasure`, `QuotientField`,
    `PadicMeasure` exist **only** in this project; zero mathlib hits.

Searched for both:
- the user's current form (the twisted pseudo-measure statement over `Q(ℤ_p^×)`) — **no mathlib hit**
  (the objects are project-local).
- the literature-standard form (pseudo-measure à la Coates: `([g]−1)·λ ∈ Λ`) — **no mathlib hit**.
  Mathlib has **no** Iwasawa algebra (as a completed group ring / `MonoidAlgebra` fraction field),
  **no** pseudo-measure predicate, **no** Kubota–Leopoldt p-adic L-function, **no** p-adic zeta.
  The *only* Lean formalization of p-adic L-functions (Narayanan, arXiv:2302.14491) is **Lean 3,
  standalone (`github.com/laughinggas/p-adic-L-functions`), never upstreamed to mathlib**, and per
  the PDF does **not** use the pseudo-measure-as-fraction-ring formalism at all.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form).
There is no mathlib decl over these objects, hence no candidate to specialise from and no ≤1-line
derivation possible — **NOT `NO-mathlib-has-it`**.

---

### Call sites — `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

Internal use count: **K = 0** (within the project, NOT counting the declaring line). A
project-wide grep for `twistedZetaHalf_isTwistedPseudoMeasure` returns **only the declaration
line** (`EisensteinFamily.lean:246`) — no other `.lean` file, and not even elsewhere within
`EisensteinFamily.lean`. In particular the main result `eisensteinFamily_interpolation` does **not**
consume it (it uses `twistedZetaHalf_moments`, via the witness `ν`, instead).

External-to-file callers: **0 distinct files**.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| (none) | — the theorem has no consumers anywhere in the project |

Inline-derivation grep (was the same `(g·[g]−1)·A₀ ∈ Λ` statement re-derived elsewhere without
calling this theorem?): **(none)** — the only place the twisted-clearing statement is established is
the helper `twistedZetaHalf_witness_eq` (`EisensteinFamily.lean:214`, used by *this* theorem and by
`twistedZetaHalf_moments`); no site re-derives this existential by hand.

What this tells us (per the Phase-6.0.1 signal table): **`K = 0` internal uses with no inline
re-derivation** → the row is *"Dead code? Brand new + unused so far?"* → **Junk OR genuinely-new
(BORDERLINE)**. Here it is clearly *not* junk: it is the deliberate, documented realization of the
project's **erratum #11** (the corrected form of RJW Thm 2403(a)) — a *documentation/verification*
theorem stating that `A₀` satisfies the corrected (twisted) pseudo-measure property. It is "the
mathematically correct claim the source got wrong", proved and recorded, rather than a building
block other proofs invoke. That is a legitimate reason for `K = 0`, but it sharpens the
packaging question (does mathlib want this specific corrected, family-specific statement?) toward
the human.

### Composition check (Phase 6)

Can `twistedZetaHalf_isTwistedPseudoMeasure` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: express via a mathlib pseudo-measure / Iwasawa-algebra API.
  - Mathlib decls used: — (none exist).
  - Result: **fails** — the statement names `twistedZetaHalf`, `QuotientField`, `PadicMeasure`,
    `dirac`, none of which is in mathlib. The statement is not even *expressible* against mathlib
    types. A "composition" would first require *defining* the entire framework.

Attempt 2: reproduce the actual 2-line proof.
  - Project decls used: `padicZeta_isPseudoMeasure` (the pseudo-measure property of `ζ_p`) +
    `twistedZetaHalf_witness_eq` (transport through the x-twist).
  - Mathlib content of those: generic `algebraMap`/`map_mul`/`ring`/`IsLocalization` plumbing —
    but the *substance* (`padicZeta` is a pseudo-measure; the twist sends the witness correctly) is
    **project-local** and absent from mathlib. So this is not "compose mathlib primitives to get our
    form"; it is "our form is a 2-line wrapper *over project objects* (`padicZeta_isPseudoMeasure`,
    `twistedZetaHalf_witness_eq`) that themselves encode the real, non-mathlib mathematics".

Conclusion: **NOT-COMPOSABLE from mathlib.** Mathlib does not contain the objects the statement
names; the proof's mathlib content is generic ring/localisation plumbing, and the substance is
project-local. This cannot be inlined into mathlib at all (the call site — were there one — would
live in a project-specific construction). **NOT `NO-composable-from-mathlib`.**

---

## Verdict: `PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the underlying concept — **pseudo-measure** à la Coates–Serre, an
  element of `Frac(Λ(G))` with `([g]−1)·λ ∈ Λ(G)`, with `ζ_p` the canonical example — is **canonical**
  (Coates; Serre; Coates–Sujatha; RJW Def 3.34; non-abelian generalisations arXiv:0711.0581). The
  **twisted** single-`g` form `(g·[g]−1)·A₀ ∈ Λ` of *this* theorem is **not** a separately named
  literature object: it is the project's **erratum #11** correction of RJW Thm 2403(a) (the source
  wrongly claims `A₀` is an honest pseudo-measure; the pole sits at `x⁻¹`, so only the twisted
  augmentation element clears it).
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is — the twist (row 2) is
  mathematically forced (untwisting makes it false); the "abstraction" directions (arbitrary `λ`;
  bundled predicate; general group-ring fraction field) are *different, more abstract decls* and all
  still over a **non-mathlib** framework; the `𝒪_L` coefficient generality is deferred project
  infrastructure. Modern-idiom (Phase 4c): none for a *mathlib* contribution (every abstraction is
  over the project's non-mathlib `Q(ℤ_p^×)`).
- Mathlib search (Phase 5): **not in mathlib** — zero hits for pseudo-measure / Kubota–Leopoldt /
  Iwasawa algebra / `padicZeta` / the project objects; mathlib's only `Iwasawa.lean` is the
  unrelated group-action decomposition; the sole Lean p-adic-L formalization (Narayanan) is Lean 3,
  standalone, never upstreamed, and doesn't use this formalism.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the statement names objects mathlib
  lacks; the proof's mathlib content is generic plumbing only. Call-sites: **K = 0** (no consumers
  anywhere; it documents erratum #11 rather than feeding any proof), no inline re-derivation.

**Rationale (why BORDERLINE, not a clean bucket):**

`twistedZetaHalf_isTwistedPseudoMeasure` is the correct, deliberately-corrected (erratum #11)
statement that the Eisenstein family's constant coefficient `A₀ = x·ζ_p/2` is an x-**twisted**
pseudo-measure — i.e. `(g·[g]−1)·A₀ ∈ Λ(ℤ_p^×)` for every `g`. The *concept* it instantiates
(pseudo-measures of Coates–Serre over the fraction ring of the Iwasawa algebra) is firmly
canonical. But the theorem is stated **entirely over objects that exist only in this project**:
the linear-functional p-adic measure `PadicMeasure = C(ℤ_p^×, ℤ_[p]) →ₗ ℤ_[p]` (RJW Def 3.6), the
Iwasawa algebra `Λ(ℤ_p^×)` and its total fraction ring `Q(ℤ_p^×) = FractionRing(…)` (Def 3.34), the
Kubota–Leopoldt `padicZeta` (Def 4.10), the x-twist `quotientTwist`/`unitsTwist`, and the def
`twistedZetaHalf` — **none of which is in mathlib** (Phase 5: 0 hits; the only prior Lean p-adic-L
work is Lean 3 and standalone). This makes the four mechanical buckets all fail their gates:
**`NO-mathlib-has-it`** is wrong (Phase 5 found no decl over these objects, and there is no ≤1-line
specialisation because there is no mathlib object to specialise from); **`NO-composable-from-mathlib`**
is wrong (Phase 6 is NOT-COMPOSABLE — the building blocks themselves are absent from mathlib, so this
cannot be inlined into mathlib at all); **`YES-add-as-is`** / **`YES-but-generalise-first`** are both
premature, because shipping *this theorem* to mathlib is meaningless without first upstreaming the
entire pseudo-measure / Iwasawa-algebra / `padicZeta` framework it is stated over — a separate,
large, design-laden decision (the linear-functional `PadicMeasure` vs mathlib's
`MeasureTheory.Measure`; "Iwasawa algebra = completed group ring / `MonoidAlgebra`"; the RJW
`𝒪_L`-coefficient generality the project itself defers; whether a `IsTwistedPseudoMeasure` predicate
should exist). The decisive question — *should that whole framework go to mathlib, and in what form?* —
is exactly the mathematical-taste / project-policy call the skill must not make alone. Compounding
this, the call-sites signal (`K = 0`, no consumers, no inline re-derivation) shows this is a
*documentation/verification* theorem recording the erratum #11 correction, not a reusable API hub —
which, absent a decision to upstream the framework, leans toward "keep project-local". This matches
the verdicts already reached for the parent def `twistedZetaHalf` and the sibling
`divisorMeasure_moment` (both `BORDERLINE-needs-human` for the same framework-absence reason).

**Numbered questions (≤5):**

1. **Foundation-first.** This theorem cannot reach mathlib before its whole tower — the
   linear-functional p-adic measures `PadicMeasure p X`, the Iwasawa algebra `Λ(ℤ_p^×)` + total
   fraction ring `Q(ℤ_p^×)`, the `IsPseudoMeasure` formalism, `padicZeta`, the x-twist — is
   upstreamed. Is upstreaming that **foundation** (especially "Iwasawa algebra = completed group
   ring / fraction field, with pseudo-measures") a goal? If **no**, this theorem stays project-local
   and the assessment ends as "keep". If **yes**, it ships *with* that framework, not on its own.
2. **Predicate vs per-`g` form.** The project already bundles the *untwisted* pseudo-measure as the
   `Prop` predicate `IsPseudoMeasure`. Would you like a parallel bundled `IsTwistedPseudoMeasure`
   (or, better, a *general* `IsPseudoMeasureWrt (e : Λ → Λ)` parametrised by the augmentation
   automorphism) so that this theorem becomes `IsTwistedPseudoMeasure (twistedZetaHalf …)` rather
   than a bespoke single-`g` existential? (This is a **project** refactor; it does not by itself make
   it mathlib-bound, since `Q(ℤ_p^×)` is project-local.)
3. **Which object is the real mathlib target?** Given `K = 0`, is the mathlib-worthy headline the
   *p-adic zeta* `padicZeta` (and its honest pseudo-measure property `padicZeta_isPseudoMeasure`),
   or the *family* `eisensteinFamily` + its interpolation theorem — rather than this twist-corrected
   constant-coefficient lemma in isolation? The honest, un-twisted pseudo-measure statement
   (`padicZeta_isPseudoMeasure`) is the literature-standard one; the twisted form here is the
   project's erratum-driven variant.
4. **Erratum-#11 framing.** This theorem's entire point is that `A₀` is *not* an honest
   pseudo-measure (the source's Thm 2403(a) is wrong) — only its *twist* lands in `Λ`. Is recording
   that corrected, family-specific "twisted pseudo-measure" statement something a future mathlib
   contribution would want as-is, or would mathlib prefer to expose only the honest pseudo-measure
   `x·ζ_p` / `ζ_p` and apply the twist/half at the family-assembly site (leaving this lemma as
   internal bookkeeping)?

**Next action:** user answers questions 1–4; re-run
`/mathlibable PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure` to resolve. Likely outcomes:
- Q1 = no (framework stays project-local) → drop from independent mathlib consideration; keep
  project-local as the erratum-#11 record. Nothing to PR.
- Q1 = yes + Q3 → padicZeta/family → still keep *this* twist-corrected lemma project-local; the
  mathlib contribution is the framework + the *honest* pseudo-measure (`padicZeta_isPseudoMeasure`),
  with the twist applied downstream. Optionally adopt the Q2 predicate as a project tidy-up first.
- Q1 = yes + Q4 = mathlib wants the twisted form too → it ships as one (small) lemma within the much
  larger framework upstreaming, after a `/generalise` pass (bundle the predicate per Q2, and confirm
  the `𝒪_L`-coefficient generality direction the project defers).

---

## Next step

User answers questions 1–4 above; re-run
`/mathlibable PadicLFunctions.twistedZetaHalf_isTwistedPseudoMeasure` to resolve the verdict. (Or
commit directly: the most likely resolution — given the `K = 0` call sites, the fact that this is the
erratum-#11 *correction* of a source claim rather than a reusable building block, and that every
object it names is project-local — is to **keep it in the project**, and consider upstreaming only the
*generic* Iwasawa-algebra / pseudo-measure framework, in its general `𝒪_L` form and with the honest
(un-twisted) pseudo-measure as the named object, as a separate, much larger effort.)

---

### Sources (Phase 3)
- https://arxiv.org/abs/2309.15692 / https://arxiv.org/pdf/2309.15692 — Rodrigues Jacinto–Williams, *An introduction to p-adic L-functions* (the **exact source**: pseudo-measure Def 3.34; Eisenstein family §8; Thm 2403(a) corrected by erratum #11)
- https://msp.org/ent/2025/4-1/ent-v4-n1-p03-p.pdf — same, *Essential Number Theory* 2025 published version
- https://www.math.mcgill.ca/darmon/courses/16-17/gs/Coates-Sujatha.pdf — Coates–Sujatha, *Cyclotomic Fields and Zeta Values* (pseudo-measures introduced by Coates as elements of the fraction field of the Iwasawa algebra; `ζ_p` the canonical example)
- https://warwick.ac.uk/fac/sci/maths/people/staff/cwilliams/lecturenotes/lecture_notes_part_i.pdf — Williams, lecture notes on p-adic L-functions (pseudo-measure definition, `([g]−1)`-annihilator)
- https://arxiv.org/pdf/0711.0581 — *Non-abelian pseudomeasures and congruences between abelian Iwasawa L-functions* (the same `([g]−1)`-annihilator definition generalised to non-commutative `Λ` — confirms it is the standard definition)
- https://arxiv.org/pdf/2302.14491 — Narayanan, *Formalization of p-adic L-functions in Lean 3* (the **only** prior Lean formalization — Lean 3, standalone, never upstreamed to mathlib; does **not** use the pseudo-measure-as-fraction-ring formalism)
- https://arxiv.org/pdf/1204.3878 — Hida-style *Analytic constructions of p-adic L-functions and Eisenstein series* (the Eisenstein-family bootstrap context)
- https://ahilado.wordpress.com/2020/11/30/iwasawa-theory-p-adic-l-functions-and-p-adic-modular-forms/ — constant term of the p-adic Eisenstein family = element of the Iwasawa algebra (Serre bootstrap, plain-language)
