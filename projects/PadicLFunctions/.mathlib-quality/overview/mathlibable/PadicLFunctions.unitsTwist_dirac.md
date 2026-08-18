# `/mathlibable` report — `PadicLFunctions.unitsTwist_dirac`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-19. Verdict at the bottom.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `.lake/build` artifacts stale; mathlib present at `.lake/packages/mathlib`). The declaration and every dependency (`unitsTwist`, `PadicMeasure`, `dirac`, `unitsCmul`, `unitsPowCM`) were read directly from source.
- decl `PadicLFunctions.unitsTwist_dirac`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:147`
- kind:                      theorem
- has sorry:                 no (the whole file is sorry-free; `grep` for `sorry`/`admit` returns nothing)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — bundles the Kubota–Leopoldt pseudo-measure (constant coefficient) and divisor-sums of Dirac measures (higher coefficients) into the Λ-adic Eisenstein family `𝐄`. The x-twist `τ : [g] ↦ g·[g]` is realised as a ring automorphism of the convolution algebra.

---

### Statement (Phase 1)

`PadicLFunctions.unitsTwist_dirac` is **a theorem** stating the following:

The **x-twist** operator `τ` sends a Dirac point mass to a scaled Dirac point mass:

  `τ(δ_g)  =  (g : ℤ_p) · δ_g`   for every unit `g ∈ ℤ_p^×`.

Here `τ = unitsTwist` is the operator on p-adic measures (`ℤ_p`-linear functionals on
`C(ℤ_p^×, ℤ_p)`) defined by `(τμ)(f) = μ(x·f)`, where `x` is the continuous function
`u ↦ (u : ℤ_p)` (the unit-inclusion `ℤ_p^× ↪ ℤ_p`, internally `unitsPowCM p 1`). The
statement evaluates `τ` on the Dirac measure `δ_g` (the functional `f ↦ f(g)`) and says
the result is the functional `δ_g` scaled by the scalar `(g : ℤ_p)`.

The mathematical content is the **multiplication-operator/eigenvector property of a point
mass**: multiplying a measure by a function `g` rescales the Dirac mass at `a` by the value
`g(a)`, i.e. `g·δ_a = g(a)·δ_a`. Here the "function" is `x` (the unit-inclusion) and the
support point is `g`, so the scalar is `(g : ℤ_p)`. In the Iwasawa-algebra picture this is
the statement that the x-twist multiplies the group-like element `[g]` by its own image
`g`. It is the computational core of "the twist sends Diracs to scaled Diracs" (RJW
arXiv:2309.15692, around TeX 2376 "viewing `d` as an element of `ℤ_p^×`" and TeX 2411–2413).

One-line proof (read from source): `LinearMap.ext`, then unfold both sides to
`(x·f)(g) = g·f(g)` via `unitsCmul_apply`, `dirac_apply`, `LinearMap.smul_apply`,
`ContinuousMap.mul_apply`, `smul_eq_mul`, finishing with `simp [unitsPowCM]` (which
evaluates `x(g) = (g : ℤ_p)^1 = (g : ℤ_p)`).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `g : ℤ_[p]ˣ` — the unit at which the Dirac mass is supported.

Hypotheses (Lean side): none (beyond the ambient `Fact p.Prime`). Notably no `p ≠ 2`.

Conclusion (math): the x-twist of the Dirac measure at `g` equals `(g : ℤ_p)` times that
Dirac measure.

Conclusion (Lean): `unitsTwist p (PadicMeasure.dirac p g) = (g : ℤ_[p]) • PadicMeasure.dirac p g`
— an equality in `PadicMeasure p ℤ_[p]ˣ = C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-screen computational lemma about the bespoke `unitsTwist` operator acting on a
Dirac measure; it is an API fact feeding the `unitsTwist`/`twistedZetaHalf` development, not
a named theorem and not a new structure. It is *not* listed under `## Main results`; the file's
main result is `eisensteinFamily_interpolation`.

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only;
it does not gate which channels Phase 3 runs.)

### One-line check (Phase 2b)

Body line count: 7 substantive lines (a `LinearMap.ext`, a `change`, a multi-lemma `rw`, a
`congr 1`, and a closing `simp`). Kind is **theorem**, not a `def`/`abbrev`/`structure`.

One-liner verdict: **n/a — kind is `theorem`.** The one-liner exemption machinery applies to
definitions; this is a lemma, so the section is skipped. (For the record: even as prose the
"def-vs-multiline" question is moot — there is no definitional body to inline.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "multiplication operator on measures sends Dirac delta to scaled Dirac (M_g δ_a = g(a) δ_a)"            | yes  | `M_g δ_a = g(a) δ_a` / `x·δ(x−a)=a·δ(x−a)` | Confirmed as the eigenvalue property of the Dirac mass under a multiplication operator; Wikipedia *Position operator*, *Dirac delta function* |
|  2 | WebSearch (general form)         | "multiplication by function operator on measures eigenvalue Dirac mass distribution theory ... standard"| yes  | `g(x)·δ(x) = g(0)·δ(x)`; sifting `∫ f dδ_a = f(a)` | The point mass is the eigenfunction of multiplication; standard distribution-theory fact |
|  3 | WebSearch (named-after / aliases / Iwasawa)| "Iwasawa algebra Z_p[[Z_p^*]] twist by character group-like element δ_g multiplication by x"  | yes  | group elements embed as group-like elements (Diracs); twisting by a character is the relevant op | arXiv:1512.07814 (twists of Iwasawa modules), Wikipedia *Iwasawa algebra* — confirms the Iwasawa-side vocabulary (group-like / Dirac / twist) but not this exact eigenvector identity as a named lemma |
|  4 | ChatGPT MCP                      | (would ask: "standard form + generality + historical evolution of `g·δ_a = g(a)·δ_a`")                 | n/a  | —                                | **n/a — no ChatGPT/OpenAI MCP server is configured in this environment** (`~/.claude.json` has no `chatgpt`/`openai` connector). Compensated by extra WebSearch + nLab + arXiv channels (#1,#2,#5,#6,#9,#10). |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` ; `refs/PadicLFunctions/`                  | n/a  | (no references dir; `refs/` symlink absent) | dir absent — recorded n/a. The primary source is identified anyway: RJW arXiv:2309.15692 (cited throughout the file's docstrings). |
|  6 | nLab                             | "Dirac measure" / "group algebra Dirac measure point mass" (`ncatlab.org/nlab/show/Dirac+measure`)     | yes  | sifting property `∫ f dδ_x = f(x)`; Dirac measures are the unit of the measure/probability monads; group `δ` picks out value at identity | nLab states the sifting property and the group-algebra-unit role; does not state the multiply-by-function = scale identity verbatim |
|  7 | nCatLab (if categorical)         | (same nLab "Dirac measure" page; monad-unit framing)                                                   | n/a  | —                                | n/a — not a categorical concept beyond the monad-unit remark already captured in #6; no extra higher-categorical form exists for this scalar identity |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                | n/a — not an algebraic-geometry concept (a functional-analytic / measure-theoretic identity on a profinite group) |
|  9 | MathOverflow / Math.StackExchange| "multiplication operator measure functional Dirac delta scaled by value support point eigen"           | yes  | multiplication operator `T_f φ = f·φ`; `δ(αx)=|α|^{-n}δ(x)` scaling; point mass eigenvector framing | No single canonical MO thread for this exact statement — it is regarded as elementary/folklore, which is itself the signal: it is a textbook computation, not a citable named theorem |
| 10 | recent arXiv (last 5 years)      | "Rodrigues Jacinto Williams introduction p-adic L-functions Dirac measure cmul twist x-twist Eisenstein"| yes  | RJW *An introduction to p-adic L-functions*, arXiv:2309.15692 (Essential Number Theory 2025); Warwick lecture notes | The project's primary source. Treats p-adic measures as the continuous dual, Dirac measures (Ex. 3.7), `cmul` (eq. 4.11), and the x-twist on the Eisenstein family (§8). The lemma is the elementary `cmul`-on-Dirac computation behind that material. |

Protocol pass check:
- WebSearch ran 3 distinct queries at different generality levels (specific eigenvector form #1, general distribution-theory form #2, Iwasawa-algebra/named-context form #3). ✓
- ChatGPT MCP: **not available** — recorded n/a with the concrete reason (no connector configured) and compensated with two extra WebSearch channels and the nLab + arXiv reads. ✓ (documented gap, not a silent skip)
- Local references checked (absent → n/a with reason); the source paper is still pinned (RJW arXiv:2309.15692). ✓
- nLab checked (Dirac measure page; sifting + monad-unit). ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **eigenvector / scaling property of a Dirac point mass under a
multiplication operator** — `M_g δ_a = g(a)·δ_a` (equivalently the distributional
`g·δ_a = g(a)·δ_a`, the multiplicative form of the sifting property `∫ f dδ_a = f(a)`). In the
Iwasawa-algebra dialect: a **twist** of the **group-like element** `[g]` (a Dirac mass) by the
function `x` multiplies it by its own value `g`.

Sources agree on the standard form: **yes** — the eigenvector/scaling identity is uniformly
elementary across distribution theory (Wikipedia, nLab, physics/MO references) and matches the
project's source (RJW, who phrase it via `cmul`/`unitsCmul`).

Most general standard form: for a measure/distribution `μ`, a continuous function `g`, and the
Dirac mass `δ_a`, `g·δ_a = g(a)·δ_a` (and more generally `M_g` acts on any point mass by the
value at the support point). Our lemma is the **`g := x` (unit-inclusion), `a := g`**
specialisation, in the **p-adic continuous-dual** model `C(ℤ_p^×, ℤ_p) →ₗ ℤ_p`.

Generality dimensions where the literature varies:
- **The multiplying function**: literature uses an arbitrary `g`; our lemma fixes `g = x`
  (`unitsPowCM p 1`). A general `unitsCmul g (dirac a) = g(a) • dirac a` lemma would cover all of
  it — but that general lemma is *also* about the bespoke `PadicMeasure`/`unitsCmul`, so the
  generalisation does not move the result toward mathlib.
- **The coefficient ring / base object**: literature ranges over real/complex measures,
  distributions, abstract group algebras `R[[G]]`. Our object is the specific
  `ℤ_p`-valued continuous dual of `C(ℤ_p^×, ℤ_p)`.

Disagreement with the literature: **none** — the identity is exactly the standard one; only the
ambient object (`PadicMeasure`) is project-specific.

**Key Phase-3 finding that drives the verdict:** the *mathematical content* is textbook/folklore
(an eigenvector identity for point masses), but it is expressed entirely in **project-bespoke
vocabulary** (`unitsTwist`, `unitsCmul`, `PadicMeasure.dirac`, `unitsPowCM`) that the literature
does not name and — crucially (Phase 5) — that mathlib does not have.

---

### Generality analysis — `PadicLFunctions.unitsTwist_dirac` (Phase 4)

Literature-standard form (from Phase 3): `g·δ_a = g(a)·δ_a` for an arbitrary continuous
function `g` and point mass `δ_a`.

| # | Parameter / hypothesis            | Current Lean form                          | Literature-standard form                    | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|--------------------------------------------|---------------------------------------------|---------------------|---------------------------------|
| 1 | the twisting operator `unitsTwist` (= `unitsCmul (unitsPowCM p 1)`) | twist by the specific function `x` | twist/multiply by an **arbitrary** continuous `g` | yes (mechanically) | The proof never uses anything special about `x` beyond `(x·f)(g) = x(g)·f(g)`; the general statement is `unitsCmul g (dirac a) = (g a) • dirac a`. **But** `unitsCmul` is itself project-bespoke — see Phase 4b. |
| 2 | base object `PadicMeasure p ℤ_[p]ˣ` (`C(ℤ_p^×,ℤ_p) →ₗ ℤ_p`) | the project's p-adic continuous dual | any module of measures/distributions / group algebra `R[[G]]` | NO (in practice) | Weakening the base object means leaving the project's `PadicMeasure` type entirely — i.e. it is the same question as "should `PadicMeasure` be in mathlib?", a structure-level decision, not a parameter weakening of *this lemma*. |
| 3 | `g : ℤ_[p]ˣ` | a unit | an arbitrary point of the support space | already the natural index | The lemma quantifies over all `g` already; no narrowing present. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (along axis #1: the twisting function is
fixed to `x` rather than arbitrary `g`).
Number of weakening opportunities found: **1** (generalise `unitsTwist`-on-Dirac to
`unitsCmul g`-on-Dirac).

Proposed restatement (the literature-general form, *stated in the project's own vocabulary*):

```lean
theorem unitsCmul_dirac (g : C(ℤ_[p]ˣ, ℤ_[p])) (a : ℤ_[p]ˣ) :
    PadicMeasure.unitsCmul p g (PadicMeasure.dirac p a) = (g a) • PadicMeasure.dirac p a := by
  refine LinearMap.ext fun f => ?_
  rw [PadicMeasure.unitsCmul_apply, PadicMeasure.dirac_apply, LinearMap.smul_apply,
    PadicMeasure.dirac_apply, ContinuousMap.mul_apply, smul_eq_mul]
-- then `unitsTwist_dirac` becomes `unitsCmul_dirac p (unitsPowCM p 1) g` + `simp [unitsPowCM]`.
```

Cost of restatement: **CHEAP** — the proof is the same `ext`+unfold and would in fact be shorter
(no `unitsPowCM` evaluation step). However — **and this is decisive** — the generalised statement
is *still about the bespoke `PadicMeasure`/`unitsCmul`*, which Phase 5 confirms is **not in
mathlib**. So the generalisation is a good **intra-project** refactor (it belongs to the project's
`PadicMeasure` API as `unitsCmul_dirac`, and `unitsTwist_dirac` should arguably be derived from
it) but it does **not** turn this into a mathlib-shippable result. The generalisation does not
change the mathlib verdict; it changes where the lemma should sit *within the project*.

Because the weakening is CHEAP and the target is the literature-standard form, the *naive* reading
points at YES-but-generalise-first — but the gate forbids that here, because Phase 5 shows the
generalised form is **also** not a mathlib object (it is about `PadicMeasure`/`unitsCmul`), so
"generalise then PR to mathlib" is not actionable. The real question is upstream (Phase 7).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|---------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                      | no       | —                      | already typeclass-driven (`Fact p.Prime`, `ℤ_[p]`-linearity); nothing to bundle |
|  2 | sequences/metric notions → filters/topological notions?                                                 | no       | —                      | a pointwise algebraic identity; no limits/sequences present |
|  3 | a **construction** where a **universal-property class** would characterise it?                          | partial  | the underlying object `PadicMeasure` could be characterised as the continuous dual; but that is about the *type*, not this lemma | would be a `PadicMeasure`-level redesign, not this lemma |
|  4 | set-with-closure-predicate → bundled-substructure type?                                                  | no       | —                      | no substructure here |
|  5 | vector-space/metric/field-specific → modules/(semi)ring weakening?                                       | no       | —                      | already module-theoretic over `ℤ_[p]` |
|  6 | 1-categorical statement with a higher/∞-categorical generalisation mathlib is moving toward?             | no       | —                      | none — scalar identity on point masses |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive groups/monoids/ordered structures?                          | partial  | the support space `ℤ_p^×` and coefficient `ℤ_p` could be abstracted to a profinite group + `𝒪_L` (RJW's general coefficient case) | this is the *general `PadicMeasure`* programme (the file docstring defers it to "§5 development pass"), again a type-level move |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for *this lemma as a mathlib target*).
One-line reason: every "modernisation" lever here (#3, #7) is about the **underlying object**
`PadicMeasure` (whether it is the continuous dual, over which coefficient ring, on which profinite
group) — i.e. a decision about a *structure* that mathlib does not yet have. There is no contemporary
mathlib reformulation of *this scalar identity* that composes with existing mathlib API, because the
object it lives on is absent from mathlib. The identity itself is already in its natural idiomatic
form. (This is exactly the Bourbaki-2.0 "the right target is a different/more-general type" situation
— but the more-general type is still not in mathlib, so it does not flip the verdict to a YES.)

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities and no
typeclass-search paths, so the six-row risk table is skipped.

---

### Mathlib search-status: `PadicLFunctions.unitsTwist_dirac` (Phase 5)

Five-method search per `references/mathlib-search.md`. Methods A/B/C/E (Lean-Finder / Loogle /
LeanSearch / lean_local_search) require the Lean MCP search tools, which are **not loaded in this
workflow environment**; they are recorded `n/a` with that reason and **substituted by an exhaustive
grep over the full mathlib source tree** (method D, available at `.lake/packages/mathlib/Mathlib`)
**plus the WebSearch hits from Phase 3**, which independently surfaced the relevant mathlib doc page
`Mathlib/MeasureTheory/Measure/Dirac.html`. Both the user's form and the literature-standard form
were searched.

```
[A] Lean-Finder       —                                            n/a: Lean MCP search tools not available in this environment (substituted by D + Phase-3 WebSearch)
[B] Loogle            (would try: `unitsCmul _ (dirac _) = _ • dirac _`)   n/a: Lean MCP search tools not available (substituted by D)
[C] LeanSearch        (would try: "twist of a Dirac measure is a scaled Dirac")  n/a: Lean MCP search tools not available (substituted by D)
[D] Grep mathlib src  `PadicMeasure`; `IwasawaAlgebra`; `unitsCmul`; `unitsPowCM`; `invCM`; `divisorMeasure`; `withDensity.*dirac`; `smul_dirac`; `dirac_smul`; `MonoidAlgebra.*single.*smul`; `measure.*convolution`  →
                        • `PadicMeasure` / p-adic-measure-as-continuous-dual / `IwasawaAlgebra`: **no hits** — the object does not exist in mathlib.
                        • `unitsCmul` / `unitsPowCM` / `invCM` / `divisorMeasure` / the convolution algebra on functionals: **no hits** — the twist operator and its ingredients are entirely project-local. (The only `mulLeft`+`ContinuousMap` hits — `Topology/Algebra/Monoid.lean`, `RepresentationTheory/Continuous/Basic.lean` — are unrelated: composition with left-translation on the *group*, not multiplying a *functional* by a function.)
                        • Closest "scale a Dirac by a value" lemmas: `MeasureTheory.Measure.sum_smul_dirac`, `…sum_smul_dirac_singleton`, `…dirac_withDensity'` (`Mathlib/MeasureTheory/Measure/{Dirac,WithDensity}.lean`) and `MonoidAlgebra.smul_single'` (`Mathlib/Algebra/MonoidAlgebra/Defs.lean:296`).
[E] Name pattern      (would try: `unitsTwist`, `twist_dirac`, `cmul_dirac`)   n/a: lean_local_search tool not available (substituted by D's name-substring greps, which are empty for these)
```

Searched for both:
  - the user's current form (`unitsTwist (dirac g) = (g:ℤ_p) • dirac g`) — no hit (the operator is project-local);
  - the literature-standard form (`g·δ_a = g(a)·δ_a` for arbitrary `g`) — present in mathlib **only for fundamentally different objects** (see below), never for the project's continuous-dual `PadicMeasure`.

Why the closest hits are **not** matches (read the actual statements):
- `MeasureTheory.Measure.dirac` is a **`Measure`** — an `ℝ≥0∞`-valued countably-additive set
  function. The project's `PadicMeasure.dirac` is a **continuous `ℤ_p`-linear functional**
  (`C(ℤ_p^×,ℤ_p) →ₗ[ℤ_p] ℤ_p`), the p-adic *distribution* sense. The two `dirac`s are different
  objects on different categories. Mathlib's `sum_smul_dirac : μ = Σ μ{a} • dirac a` is a
  *decomposition-of-a-measure* statement, **not** "multiply a distribution by a function and get a
  scaled point mass". `dirac_withDensity'` is about `withDensity` of an `ℝ≥0∞`-density on a
  `Measure`, again not our operator.
- `MonoidAlgebra.smul_single' : r' • single m r = single m (r' * r)` is the *group-algebra*
  analogue of scaling a basis element, but `MonoidAlgebra R G` is the `Finsupp`-based group **ring**,
  not the continuous dual; and it scales by a *ring scalar* `r'`, not by *evaluating a function at the
  support point*. It does not state `g·δ_a = g(a)·δ_a`.

Concluded: **not in mathlib** (all available methods exhausted — D over the entire mathlib tree, plus
Phase-3 WebSearch which surfaced the mathlib Dirac doc page — under both the user's form and the
literature-standard form). The lemma is about an **object** (`PadicMeasure` + `unitsTwist`/`unitsCmul`)
that **mathlib does not contain at all**; mathlib's superficially-similar `dirac`-scaling lemmas live
on different objects and state different facts.

---

### Call sites — `PadicLFunctions.unitsTwist_dirac` (Phase 6.0)

Internal use count: **1** (within the project, not counting the declaring file's own statement)
External-to-file callers: **0 distinct files** (the one use is in the same file, `EisensteinFamily.lean`)

| Caller file:line                | Usage pattern (one-line excerpt)                                              |
|---------------------------------|-------------------------------------------------------------------------------|
| EisensteinFamily.lean:224       | `rw [map_sub, unitsTwist_dirac, map_one]` — inside `twistedZetaHalf_witness_eq`, rewriting `unitsTwist p (dirac p g - 1)` to `(g:ℤ_p) • dirac p g - 1` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `unitsTwist_dirac`?):
  - (none) — `grep` for hand-written `unitsCmul p (unitsPowCM p 1) (dirac p …)` outside the declaring
    file returns nothing. The lemma is the single canonical statement of this fact in the project.

What the call-sites pattern tells you: **K = 1 internal use, no inline re-derivation.** Per the
Phase-6 signal table this is the "K = 1 — possibly the wrong abstraction / could be inlined; lean
toward NO-composable" row. But here the single consumer (`twistedZetaHalf_witness_eq`, in turn used by
the erratum-#11 `twistedZetaHalf_isTwistedPseudoMeasure` and the moments lemma) is a genuine,
load-bearing step: it converts the *additive* twist of `δ_g − 1` into the *multiplicative* form
`(g:ℤ_p)•δ_g − 1` that the pseudo-measure witness needs. So it is not dead code; it is a small but
necessary piece of the family's `A₀` API.

### Composition check (Phase 6)

Can `unitsTwist_dirac` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: there is **nothing in mathlib to compose** — `unitsTwist`, `unitsCmul`,
`PadicMeasure.dirac`, and `unitsPowCM` are all project-local definitions absent from mathlib (Phase 5).
The proof is necessarily a `LinearMap.ext` against the *project's* definitions
(`unitsCmul_apply`, `dirac_apply`, `LinearMap.smul_apply`, `ContinuousMap.mul_apply`,
`smul_eq_mul`, `simp [unitsPowCM]`).
  - Mathlib decls used: only generic `LinearMap`/`ContinuousMap` plumbing
    (`LinearMap.ext`, `LinearMap.smul_apply`, `ContinuousMap.mul_apply`, `smul_eq_mul`) — these glue
    the project lemmas together; they are not a *mathlib statement of this fact*.
  - Result: **fails** as a "mathlib composition" — there is no mathlib lemma about `PadicMeasure`
    to chain.

Attempt 2 (composition *within the project*, for completeness): the lemma is essentially the
`g = unitsPowCM p 1` specialisation of the (not-yet-existing) project lemma `unitsCmul_dirac`
(Phase 4b). Within the project it would be `unitsCmul_dirac p (unitsPowCM p 1) g` + `simp [unitsPowCM]`
— a clean 1-call project composition. But that is composition from *project* primitives, not mathlib
primitives.

Conclusion: **NOT-COMPOSABLE (from mathlib).** Mathlib has neither the exact form nor the building
blocks (the building blocks are `PadicMeasure`-level and project-local). It *is* composable from a
slightly more general *project* lemma — which is the intra-project refactoring note above, not a
mathlib composition.

---

## Verdict: `PadicLFunctions.unitsTwist_dirac`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the identity `g·δ_a = g(a)·δ_a` (multiplication operator scales a
  point mass by its value at the support point) is **standard and elementary** across distribution
  theory / measure theory (Wikipedia, nLab, MO) and is the `cmul`-on-Dirac computation in the project's
  source RJW arXiv:2309.15692. But it is folklore-level, not a citably *named* theorem, and the project
  expresses it in bespoke vocabulary (`unitsTwist`/`unitsCmul`).
- Generality analysis (Phase 4): **STRICTLY NARROWER** than the literature form (the twisting function
  is fixed to `x`); the CHEAP generalisation `unitsCmul_dirac` is still about the bespoke
  `PadicMeasure`/`unitsCmul`, so it improves the *project* API but is not a mathlib target. Modern-idiom
  check: **no** contemporary mathlib reformulation of *this lemma* exists, because the levers all act on
  the underlying object, not the statement.
- Mathlib search (Phase 5): **not in mathlib** under either form. The object `PadicMeasure` (continuous
  dual of `C(ℤ_p^×,ℤ_p)`) and the twist operator are entirely absent; mathlib's `Measure.dirac`-scaling
  lemmas and `MonoidAlgebra.smul_single'` live on *different objects* and state *different facts*.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (no mathlib building blocks for
  `PadicMeasure`); K = 1 internal consumer, no inline re-derivation, load-bearing within the `A₀` API.

**Rationale.**
This is a small, correct, sorry-free computational lemma whose *mathematical content* is textbook
(an eigenvector/scaling identity for a Dirac point mass) but whose *entire vocabulary* —
`unitsTwist`, `unitsCmul`, `PadicMeasure.dirac`, `unitsPowCM` — is **project-local and absent from
mathlib**. It is therefore neither `NO-mathlib-has-it` (mathlib has no statement of this fact about
this object — its `Measure.dirac` lemmas are about a different object and say something different) nor
`NO-composable-from-mathlib` (mathlib has no `PadicMeasure`-level building blocks to compose; the only
composition available is from a *project* lemma). It is not `YES-add-as-is`/`YES-but-generalise-first`
in any *actionable* sense either: the gate forbids a YES because the result — even after the CHEAP
literature-general weakening to `unitsCmul_dirac` — is still a fact about a bespoke object that mathlib
does not contain, so "open a mathlib PR for `unitsTwist_dirac`" is not a meaningful next step in
isolation.

The verdict therefore hinges on **one upstream judgment the skill cannot make alone**: *is the
underlying object `PadicMeasure` (and its convolution algebra / `unitsCmul` twist) destined for
mathlib?* If yes, then this lemma (in its generalised `unitsCmul_dirac` form) ships **as part of that
`PadicMeasure` API**, and the verdict becomes YES-but-generalise-first *contingent on* the object
landing. If no — if `PadicMeasure` stays a project-internal model for the RJW development — then this
lemma is correctly project-local and should *not* be a standalone mathlib PR. This is exactly the
situation of the sibling lemmas `divisorMeasure_moment` and `divisorMeasure` in the same file, which
were both assessed `BORDERLINE-needs-human` for the same upstream reason. The numbered questions below
surface that single decision.

**Refactor-actionable bar — BORDERLINE-needs-human.**

Numbered questions (≤5):

1. **Is the object `PadicMeasure p X = C(X, ℤ_p) →ₗ[ℤ_p] ℤ_p` (the p-adic continuous dual, with its
   convolution `CommRing` structure) intended for upstreaming to mathlib**, or is it a project-internal
   model for the Kubota–Leopoldt / RJW development? (mathlib currently has *no* such object — Phase 5.)
   *This single answer determines the bucket.*

2. If `PadicMeasure` **is** mathlib-bound: should this lemma be generalised first to the
   literature-standard `unitsCmul_dirac (g : C(ℤ_p^×,ℤ_p)) (a) : unitsCmul g (dirac a) = (g a) • dirac a`
   (CHEAP — same proof, shorter; Phase 4b), with `unitsTwist_dirac` derived from it, and shipped as part
   of the `PadicMeasure` API? (Recommended if the answer to #1 is yes.)

3. If `PadicMeasure` is **not** mathlib-bound: confirm this lemma stays project-local — in which case the
   only remaining (intra-project) action is the optional refactor in #2 (introduce `unitsCmul_dirac` in
   the `PadicMeasure`/`ZetaP` API and reduce `unitsTwist_dirac` to it), purely for internal consistency,
   not for mathlib.

4. (Naming, only if #1 is yes) The name `unitsTwist` is RJW/project-specific. Would the general
   `PadicMeasure` API prefer the function-agnostic `PadicMeasure.unitsCmul_dirac` (or a `dirac`-eigenvector
   name) over a `unitsTwist`-suffixed lemma, so the mathlib statement is about `unitsCmul` rather than the
   bespoke `unitsTwist` automorphism?

Next action: user answers question #1 (the load-bearing one); re-run `/mathlibable
PadicLFunctions.unitsTwist_dirac` to resolve. Likely outcomes:
  - `PadicMeasure` is project-internal → drop from mathlib consideration; optionally do the intra-project
    `unitsCmul_dirac` refactor (#2/#3).
  - `PadicMeasure` is mathlib-bound → flips to **YES-but-generalise-first** (generalise to
    `unitsCmul_dirac` per #2), shipped *with* the `PadicMeasure`/`dirac`/`unitsCmul` API as one upstreaming
    effort — not as a standalone lemma PR.

---

## Next step

User answers question #1 — *is `PadicMeasure` (the p-adic continuous dual + its convolution algebra)
destined for mathlib?* — then re-run `/mathlibable PadicLFunctions.unitsTwist_dirac`. If yes, generalise
to `unitsCmul_dirac` (CHEAP) and ship it with the `PadicMeasure` API (YES-but-generalise-first); if no,
keep it project-local and optionally introduce `unitsCmul_dirac` internally and reduce this lemma to it.
