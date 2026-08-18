# `/mathlibable` report — `PadicLFunctions.divisorMeasure_moment`

> Mode A — full 10-phase workflow with the exhaustive 9-channel literature search.
> Run date: 2026-06-19. Verdict at the bottom.

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — `.lake/build` artifacts dated 2026-06-17, stale; mathlib present at `.lake/packages/mathlib`). The declaration and every dependency were read directly from source.
- decl `PadicLFunctions.divisorMeasure_moment`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:74`
- kind:                      theorem
- has sorry:                 no (the whole file is sorry-free; `grep` for `sorry`/`admit` returns nothing)
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — the Kubota–Leopoldt pseudo-measure interpolates the constant coefficients of the p-stabilised Eisenstein series; the non-constant coefficients are interpolated by divisor-sums of Dirac measures `A_n`.

---

### Statement (Phase 1)

`PadicLFunctions.divisorMeasure_moment` is **a theorem** stating the following:

For a prime `p`, natural numbers `n` and `k`, the `k`-th moment of the divisor-sum
measure `A_n` is the prime-to-`p` divisor power sum `σ^p_k(n)`. Concretely, writing
`A_n = Σ_{0<d∣n, p∤d} δ_d` for the finite sum of Dirac point masses at the units
`d ∈ ℤ_p^×` (over prime-to-`p` divisors `d` of `n`), and integrating the monomial
`x ↦ x^k` against it,

  `∫_{ℤ_p^×} x^k · A_n  =  Σ_{0<d∣n, p∤d} d^k  =  σ^p_k(n) ∈ ℤ_p`.

The mathematical content is the **sifting/moment property of a finite combination of
Dirac measures**: `∫ x^k dδ_d = d^k`, summed over the index set. It is the `n`-th
non-constant coefficient identity in RJW's Λ-adic Eisenstein family theorem
(arXiv:2309.15692, TeX line 2413), used to match the family's moments to the
coefficients of the p-stabilised Eisenstein series.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `n k : ℕ` — the index `n` of the coefficient and the moment exponent `k`.

Hypotheses (Lean side): none (beyond the ambient `Fact p.Prime`).

Conclusion (math): the `k`-th moment of the divisor-sum-of-Diracs measure equals the
prime-to-`p` divisor power sum `σ^p_k(n)`.

Conclusion (Lean):
`divisorMeasure p n (PadicMeasure.unitsPowCM p k) = ((sigmaP p k n : ℕ) : ℤ_[p])`.

**Objects this statement is built from (all project-local):**
- `PadicMeasure p X` — an **`abbrev`** for `C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, the
  *linear-functional* notion of a p-adic measure (RJW Def. 3.6;
  `projects/PadicLFunctions/PadicLFunctions/Measure/Basic.lean:52`). This is the
  Iwasawa-theory "measure = bounded linear functional on continuous functions"
  convention, **not** mathlib's `MeasureTheory.Measure`.
- `PadicMeasure.dirac p x` — the functional `f ↦ f x` (`Measure/Basic.lean:64`);
  `dirac_apply` is `rfl`.
- `PadicMeasure.unitsPowCM p k` — the continuous map `u ↦ (u : ℤ_[p])^k` on `ℤ_[p]ˣ`
  (`Measure/PseudoMeasure.lean:650`).
- `divisorMeasure p n` — `Σ_{0<d∣n, p∤d} dirac p (unitOfNat p d)`
  (`EisensteinFamily.lean:68`).
- `sigmaP p k n` — `Σ_{0<d∣n, p∤d} d^k`, the prime-to-`p` divisor power sum
  (`EisensteinFamily.lean:62`).
- `unitOfNat p d` — `d` viewed in `ℤ_[p]ˣ` (junk `1` when `p ∣ d`)
  (`EisensteinFamily.lean:53`).

Proof body (6 lines): unfold `divisorMeasure`, push the functional through the finite
sum (`LinearMap.coe_sum`, `Finset.sum_apply`), unfold `sigmaP` and `Nat.cast_sum`, then
on each summand `dirac_apply` reduces to `((unitOfNat p d : ℤ_[p]) )^k = (d^k : ℤ_[p])`,
closed by `unitOfNat_coe` + `Nat.cast_pow`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/glue lemma — the per-coefficient moment computation for one object in
the family construction. Not a named theorem, not a new structure; it is one of the two
coefficientwise inputs to the main result `eisensteinFamily_interpolation`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for the
report's framing.)

### One-line check (Phase 2b)

Body line count: 6 substantive lines.
One-liner verdict: **n/a — kind is `theorem`, not `def`.**
(The one-line def exemption analysis does not apply to a proof; the section is skipped.)

---

### Literature search table — EXHAUSTIVE protocol

The mathematical concept is the **moment of a Dirac measure** (the sifting property),
applied to a finite linear combination. The specialised objects (`divisorMeasure`,
`sigmaP`, RJW's linear-functional measures) are searched as the project context.

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "moment of Dirac measure monomial integral x^k delta_a equals a^k point mass"                          | yes  | `∫ x^k dδ_a = a^k`; `[δ_x]_m = x^m`                  | arXiv 1611.02208 states moments of a Dirac measure are powers of the atom; Wikipedia "Dirac delta function". Textbook-fundamental. |
|  2 | WebSearch (general form)         | "integral of function against Dirac measure delta_a equals f(a) sifting property linear functional finite sum" | yes  | `∫ f dδ_a = f(a)` (sifting property)                 | MathWorld "Sifting Property"; LibreTexts §9.4. The most general form: integral of *any* test function against a point mass evaluates it. Our `x^k` is the special case `f = (·)^k`. |
|  3 | WebSearch (named-after / aliases)| "prime-to-p divisor power sum sigma_k^{(p)} p-stabilized Eisenstein series constant coefficient"        | partial | `σ_k` divisor sums; p-stabilised Eisenstein constant terms | arXiv 1207.0198, 1103.2806 — p-stabilised Eisenstein series and their (constant) Fourier coefficients are standard; the *prime-to-p restricted* divisor sum `σ^p_k` appears as bookkeeping inside such constructions, not as a universally-named object. |
|  4 | ChatGPT MCP                      | (intended: "standard definition + generality + historical evolution of the moment of a Dirac measure") | n/a  | —                                                    | **ChatGPT MCP not configured** on this machine (`~/.claude` has no chatgpt entry; no `.mcp.json`). Substituted extra WebSearch + WebFetch depth (rows 1–2, 6, 9–10) per the skill's MCP-absent fallback. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                           | n/a  | (directory absent)                                   | No project references dir; no `refs/PadicLFunctions/` PDFs present. Recorded n/a. The source paper (RJW arXiv:2309.15692) is cited inline in the docstrings (TeX 2413). |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/Dirac+measure`                                                         | yes  | `∫ f dδ_x = f(x)`                                    | nLab "Dirac measure": mass concentrated at one point; integral picks out `f(x)`. Confirms the sifting property as the abstract form. |
|  7 | nCatLab (if categorical)         | (covered by nLab Dirac-measure page; the moment of a point mass is not a higher-categorical concept)   | n/a  | —                                                    | Not a categorical concept. nLab page (row 6) is the relevant abstract source; no extra nCatLab entry needed. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                      | n/a  | —                                                    | Not an algebraic-geometry concept (p-adic measure moments / divisor power sums). |
|  9 | MathOverflow / Math.StackExchange| sifting property of the Dirac delta as a linear functional (via row 2 results)                          | yes  | `δ_a` is the evaluation functional `f ↦ f(a)`        | The "linear functional perspective" (δ = evaluation functional) returned in row 2's results — exactly the project's `PadicMeasure.dirac` (`f ↦ f x`, `rfl`). |
| 10 | recent arXiv (last 5 years)      | "Rodrigues Jacinto Williams introduction to p-adic L-functions arXiv 2309.15692 Eisenstein family divisor measures"   | yes  | RJW §8: family `𝐄 = Σ A_n qⁿ`, `A_n = Σ_{0<d∣n,p∤d} δ_d`, moment `= σ^p_k(n)` | arXiv:2309.15692 (also Essential Number Theory 2025). This is the **exact source** of the declaration (TeX 2411–2413). Confirms `A_n` and the moment identity are the source's own bookkeeping objects, used to interpolate the p-stabilised Eisenstein family. |

The protocol passed: WebSearch ran 3 distinct generality levels (rows 1–3); the ChatGPT
MCP row is honestly recorded n/a (tool unavailable) with the fallback substitution noted;
local refs checked (absent → n/a with reason); nLab checked (hit); nCatLab/Stacks
recorded n/a with reasons; MathOverflow/SE perspective captured (row 9); recent arXiv
located the exact source paper (row 10).

### Literature summary (Phase 3)

Concept identified as: **the moment of a Dirac measure** — equivalently the *sifting
property* of a point mass / the fact that a Dirac is the *evaluation functional*
`f ↦ f(a)` — applied to a **finite linear combination of Diracs** indexed by the
prime-to-`p` divisors of `n`, with test function `x^k`.

Sources agree on the standard form: **yes**. `∫ f dδ_a = f(a)` is textbook-universal
(Wikipedia, MathWorld, LibreTexts, nLab). For monomials this gives `∫ x^k dδ_a = a^k`
(arXiv 1611.02208). Summing over a finite index set is immediate by linearity.

Most general standard form: for a measure space and a point mass `δ_a`, and *any*
integrable test function `f`, `∫ f dδ_a = f(a)`; for a finite sum `Σ_i c_i δ_{a_i}`,
`∫ f d(Σ c_i δ_{a_i}) = Σ c_i f(a_i)`. The declaration is the special case
`c_i = 1`, `f = x^k`, index set = prime-to-`p` divisors of `n`, atoms `= unitOfNat p d`.

Generality dimensions where the literature varies:
- **Notion of "measure".** Classical/mathlib analysis: countably-additive measure on a
  σ-algebra, integral via `MeasureTheory.integral`. RJW / Iwasawa theory (this project):
  a *measure is a bounded `ℤ_[p]`-linear functional* on `C(X, ℤ_[p])` — the continuous
  dual. Under the linear-functional definition the moment identity is **definitional**
  (`dirac_apply` is `rfl`); the "integral" is just function application.
- **Test function.** Most general: any test function `f`; here `f = unitsPowCM p k`
  (the monomial). The monomial restriction is what makes the right-hand side a *power
  sum* rather than a generic sum of evaluations.
- **Divisor sum.** Most general: the full `σ_k(n) = Σ_{d∣n} d^k` (mathlib's
  `ArithmeticFunction.sigma`). Here it is the **prime-to-`p` restricted** `σ^p_k(n)`,
  a project-bespoke variant (the project relates the two in
  `EisensteinComplex.lean:sigmaP_eq_of_not_dvd` / `sigmaP_add_pow_mul_sigma_div`).

Disagreement with the literature: **none**. The declaration is a faithful, correct
specialisation of the sifting property to the RJW Eisenstein-family setting. It is not a
re-statement of a universally-named theorem; it is project bookkeeping that *instantiates*
a textbook fact for project-specific objects.

---

### Generality analysis — `PadicLFunctions.divisorMeasure_moment`

Literature-standard form (from Phase 3): `∫ f d(Σ_i c_i δ_{a_i}) = Σ_i c_i f(a_i)`, in
particular `∫ x^k d(Σ_i δ_{a_i}) = Σ_i a_i^k`.

| # | Parameter / hypothesis            | Current Lean form                                  | Literature-standard form                         | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|----------------------------------------------------|--------------------------------------------------|---------------------|---------------------------------|
| 1 | the measure `divisorMeasure p n`  | a specific finite sum of project `dirac`s          | any finite sum `Σ c_i δ_{a_i}` of point masses   | yes (in principle)  | The identity holds for *any* finite combination of Diracs against any test function — but the general statement is about a *generic* sum, which is just `LinearMap.coe_sum` + `Finset.sum_apply` + `dirac_apply`. There is no project-specific content there to upstream; see Phase 6. |
| 2 | test function `unitsPowCM p k`    | the monomial `u ↦ u^k`                             | any continuous test function `f`                 | yes                 | The monomial restriction is essential to producing a *power sum* on the RHS; the generic-`f` form is again just `dirac_apply` summed (no new content). |
| 3 | the right-hand side `sigmaP p k n`| prime-to-`p` divisor power sum                      | full divisor power sum `σ_k` (mathlib has it)    | NO (different object)| `sigmaP` is genuinely the prime-to-`p` variant required by the p-stabilisation; it is *not* a weakening of `ArithmeticFunction.sigma` but a different (filtered) object the project defines and relates to `σ_k` elsewhere. |
| 4 | coefficient ring `ℤ_[p]` / `ℤ_[p]ˣ`| p-adic integers / their units                       | the source's `𝒪_L`-valued measures (RJW §5)     | yes (deferred)      | The project explicitly defers the general-`𝒪_L` coefficient case to a later development pass (`Measure/Basic.lean` docstring). Not a weakening available *now* without that infrastructure. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for what it is** — i.e., it is the correct
specialisation; the only "weakenings" (rows 1–2) replace project-specific objects with
generic ones, at which point the statement is no longer about the Eisenstein family and
is a trivial application of `dirac_apply` + linearity (Phase 6 shows this is a ≤3-call
composition). Row 3 is not a weakening (different object). Row 4 is a real future
direction but requires infrastructure the project deliberately defers.

Number of weakening opportunities found: 0 that yield a *mathlib-worthy* statement (the
two "abstract" weakenings collapse to a trivial composition; the coefficient weakening is
deferred project infrastructure, not a regeneralisation of *this lemma*).

Proposed restatement: none. (The abstract "moment of a finite sum of Diracs against a
test function" statement is not a useful mathlib lemma over the project's
linear-functional `PadicMeasure`, because that `PadicMeasure` type is itself not in
mathlib — see Phase 5/6.)

Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                        | no       | —                      | The hypotheses are already minimal (`Fact p.Prime`); nothing to typeclass-ify. |
|  2 | sequences/metric → filters/topological?                                                   | no       | —                      | No limit/convergence notion here; it is a finite-sum algebraic identity. |
|  3 | construct an object where a universal-property class would characterise it?               | no       | —                      | No object is being constructed; this is an evaluation identity. |
|  4 | set-with-closure-predicate → bundled-substructure type?                                    | no       | —                      | No substructure involved. |
|  5 | vector-space/metric/field-specific → weaken to modules/pseudometric/(semi)ring?           | partial  | (would re-aim at the *abstract* "moment of `Σ c_i δ_{a_i}`" over a generic linear-functional dual) | This is the row-1/row-2 abstraction of Phase 4a; but the target type (continuous-dual "measures") is not a mathlib concept, so there is no mathlib downstream — it would be a *new framework*, not a restatement of this lemma. Flagged, not recommended. |
|  6 | 1-categorical → higher/∞-categorical?                                                       | no       | —                      | Not categorical. |
|  7 | concrete index (ℕ, ℤ, ℝ) → arbitrary additive groups/monoids/ordered structures?          | no       | —                      | The index set (prime-to-`p` divisors of `n`) and exponent `k` are intrinsically arithmetic; generalising them removes the content. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for a mathlib contribution).
Reason: the only abstraction on offer (row 5 — "moment of a generic finite sum of
evaluation functionals") is stated over the project's linear-functional `PadicMeasure`
type, which is itself not in mathlib. There is no contemporary mathlib idiom that turns
*this* lemma into a better mathlib lemma; the abstraction would require first upstreaming
a whole "p-adic measure = continuous dual" framework — a separate, much larger question
(see Phase 7 questions).

---

### Diamond / defeq risk — `PadicLFunctions.divisorMeasure_moment`

**n/a — declaration kind is `theorem`.** (No definitional equalities or typeclass-search
paths are introduced by a proof; Phase 4.5 is skipped per the skill's scope rule.)

### Risk verdict (Phase 4.5)

Overall risk: **n/a (theorem)**.

---

### Mathlib search-status: `PadicLFunctions.divisorMeasure_moment`

[A] Lean-Finder       — (server not invoked; substituted by direct mathlib-source grep [D] + name-pattern [E], which are authoritative on the local pinned mathlib).  n/a: tool not configured this session.
[B] Loogle (type-pattern) — searched `.lake/packages/mathlib` for the proof's mathlib lemmas and for any "moment of a sum of point masses on a linear-functional dual" pattern.  no hit on the *combined* form.
[C] LeanSearch (NL)   — concept "integral of monomial against a sum of Dirac measures equals divisor power sum" — covered by the literature search (Phase 3) + grep below.  n/a: server not configured; substituted by [D]/[E].
[D] Grep mathlib src  — terms tried: `dirac_apply`, `integral_dirac`, `sum_dirac`, `moment.*dirac`, `monomial.*moment`, `LinearMap.coe_sum`, `sigma`, `ArithmeticFunction.sigma`.  hits found, but for *different* objects (see below).
[E] Name pattern      — `divisorMeasure`, `unitsPowCM`, `sigmaP`, `PadicMeasure` — exist **only** in this project; zero mathlib hits.

Searched for both:
- the user's current form (project objects) — **no mathlib hit** (the objects are project-local).
- the literature-standard form (`∫ f dδ_a = f(a)` / moment of a Dirac) — mathlib has the
  **measure-theoretic** version, in an orthogonal sense:
  - `MeasureTheory.integral_dirac` / `integral_dirac'`
    (`Mathlib/MeasureTheory/VectorMeasure/Integral.lean:654,670`):
    `∫ x, f x ∂(Measure.dirac a) = f a` — but for `MeasureTheory.Measure.dirac` over a
    `MeasurableSpace`, **not** the project's linear-functional `PadicMeasure.dirac`
    (`f ↦ f x`, defined as `rfl`). These are *different mathematical encodings* of the
    same idea; the project's `dirac_apply` (`Measure/Basic.lean:70`) already *is* the
    sifting lemma for its own type.
  - `Measure.sum_dirac` / `binomial_eq_sum_dirac` / `integral_sum_dirac`
    (`Mathlib/Probability/Distributions/*`): sums of `MeasureTheory.Measure.dirac`s —
    again the measure-theoretic encoding, not the continuous-dual one.
  - `ArithmeticFunction.sigma k n = ∑ d ∈ divisors n, d^k`
    (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:143`): mathlib has the **full**
    divisor power sum, but **not** the prime-to-`p` restricted `sigmaP`. The project
    itself bridges the two (`EisensteinComplex.lean`), confirming `sigmaP ∉ mathlib`.
  - The generic plumbing lemmas the proof uses (`LinearMap.coe_sum` at
    `Algebra/Module/Submodule/LinearMap.lean:273`, `Finset.sum_apply`, `Nat.cast_sum`,
    `Nat.cast_pow`) **are** in mathlib — but they are generic, not this statement.

Concluded: **not in mathlib** (all available methods exhausted, plus the
literature-standard form). Mathlib has (i) the *measure-theoretic* sifting property for
its own `Measure.dirac`, and (ii) the *full* divisor power sum `ArithmeticFunction.sigma`,
but **neither** the project's continuous-dual `PadicMeasure.dirac`/`divisorMeasure`, nor
the prime-to-`p` `sigmaP`, nor this moment identity stated over them.

---

### Call sites — `PadicLFunctions.divisorMeasure_moment`

Internal use count: **K = 1** (within the project, NOT counting the declaring file's own
statement). The single use is at
`projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:399`, inside the main
result `eisensteinFamily_interpolation`.
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                          |
|--------------------------------|-----------------------------------------------------------|
| EisensteinFamily.lean:399      | `rw [divisorMeasure_moment, stabilisedCoeff, if_neg hn]`  |

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`divisorMeasure_moment`?): **(none)** — no other site computes a moment of
`divisorMeasure` by hand.

What this tells us: `K = 1` internal use, same file, no external consumers, no inline
re-derivation. This is a *single-use helper extracted from one proof* — a classic
"could-be-inlined" signal that leans the verdict away from a standalone mathlib
contribution. It is not dead code (it feeds the main theorem) and it is not a widely-used
API (no `K ≥ 3`, no downstream library).

### Composition check (Phase 6)

Can `divisorMeasure_moment` be derived from **mathlib** in ≤3 chained calls?

Attempt 1: rewrite the statement using mathlib's `MeasureTheory.integral_dirac` +
`Measure.sum_dirac`.
  - Mathlib decls used: `MeasureTheory.integral_dirac`, `Measure.sum_dirac`,
    `ArithmeticFunction.sigma`.
  - Result: **fails** — the statement is not even *expressible* via these: the LHS
    `divisorMeasure p n (unitsPowCM p k)` is *function application of a `ℤ_[p]`-linear
    functional*, not `MeasureTheory.integral … ∂(Measure.dirac …)`. There is no mathlib
    coercion from the project's `PadicMeasure` (a `LinearMap`) to `MeasureTheory.Measure`.
    A "composition" would first require *defining* `divisorMeasure`, `unitsPowCM`,
    `sigmaP` — i.e. it presupposes the project's objects, which are not in mathlib.

Attempt 2: derive it generically from `LinearMap.coe_sum` + `Finset.sum_apply` +
`dirac_apply`.
  - Mathlib decls used: `LinearMap.coe_sum`, `Finset.sum_apply`, `Nat.cast_sum`,
    `Nat.cast_pow`.
  - Result: **partial / not a mathlib composition.** This is exactly the actual 6-line
    proof. But it crucially also uses two **project** lemmas — `PadicMeasure.dirac_apply`
    and `unitOfNat_coe` — and the project definitions `divisorMeasure`/`sigmaP`. Stripped
    of the project objects there is no statement left. So this is not "compose mathlib
    primitives to get our form"; it is "our form is a short proof *over project objects*
    using generic plumbing".

Conclusion: **NOT-COMPOSABLE from mathlib** (in the sense relevant to a mathlib verdict).
Mathlib does not contain the objects the statement names; the proof's mathlib content is
generic linearity/cast plumbing, and the substance is project-local. This is *not* a
1–3-call inlining of mathlib decls at a call site — it cannot be inlined into mathlib at
all, because the call site lives in a project-specific construction.

---

## Verdict: `PadicLFunctions.divisorMeasure_moment`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the underlying fact (moment/sifting property of a Dirac,
  `∫ x^k dδ_a = a^k`) is textbook-universal (Wikipedia, MathWorld, nLab, arXiv 1611.02208);
  the *exact declaration* is RJW arXiv:2309.15692 §8 TeX 2413, project bookkeeping for the
  Λ-adic Eisenstein family. No universally-named theorem corresponds to it; `sigmaP` is a
  project-bespoke prime-to-`p` divisor sum.
- Generality analysis (Phase 4): MAXIMALLY GENERAL for what it is — the only abstractions
  collapse to a trivial linearity composition over a *non-mathlib* type; row-3 `sigmaP` is
  a different object, not a weakening; the general-`𝒪_L` coefficient case is deferred
  project infrastructure. Modern-idiom: none for a mathlib contribution.
- Mathlib search (Phase 5): not in mathlib. Mathlib has the *orthogonal* measure-theoretic
  sifting property (`MeasureTheory.integral_dirac`) and the *full* divisor sum
  (`ArithmeticFunction.sigma`), but neither the continuous-dual `PadicMeasure`/`divisorMeasure`
  nor `sigmaP` nor this identity over them.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib — the statement names objects
  mathlib lacks; the proof's mathlib content is generic plumbing only.

**Rationale (why BORDERLINE, not a clean bucket):**

`divisorMeasure_moment` is a correct, faithful specialisation of a textbook fact (Dirac
moments) to objects that exist **only in this project**: the linear-functional notion of a
p-adic measure (`PadicMeasure = C(X, ℤ_[p]) →ₗ ℤ_[p]`, RJW Def. 3.6), the divisor-sum-of-
Diracs `divisorMeasure`, and the prime-to-`p` divisor power sum `sigmaP`. None of these
three objects is in mathlib. So the four "mechanical" buckets all fail their gates:
**NO-mathlib-has-it** is wrong (Phase 5 found no decl over these objects — mathlib's
`integral_dirac`/`sigma` are different encodings/objects, and there is no ≤1-line
specialisation because there is no coercion between the encodings); **NO-composable-from-
mathlib** is wrong (Phase 6 is NOT-COMPOSABLE — you cannot inline this into mathlib, the
objects do not exist there); **YES-add-as-is** / **YES-but-generalise-first** are both
premature, because shipping *this lemma* to mathlib is meaningless without first upstreaming
the entire "p-adic measure = continuous dual" framework it is stated over — a separate,
large, design-laden decision (point-set vs. mathlib's `MeasureTheory.Measure`, the RJW
`𝒪_L`-coefficient generality the project itself defers, naming, whether the divisor-sum
measures and `sigmaP` deserve mathlib homes). The decisive question — *should the underlying
RJW measure framework go to mathlib at all, and in what form?* — is exactly the
mathematical-taste / project-policy call the skill must not make alone. Compounding this,
the call-sites signal (`K = 1`, single-file, no external consumers, no inline re-derivation)
says this particular lemma is a *single-use helper extracted from one proof*, which on its
own leans toward "keep project-local / inline", not "upstream".

**Numbered questions (≤5):**

1. Is the linear-functional p-adic measure framework (`PadicMeasure p X = C(X, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`,
   `PadicMeasure.dirac`, pushforward, the `Λ(ℤ_p^×)` convolution algebra) something you
   intend to upstream to mathlib as a *new framework* (distinct from mathlib's
   `MeasureTheory.Measure`)? If **no**, then `divisorMeasure_moment` stays project-local
   and this assessment ends as "keep" — there is nothing to PR. If **yes**, this lemma
   becomes a small API lemma that ships *with* that framework, not on its own.
2. If the framework is upstreamed: should the prime-to-`p` divisor-sum measure
   `divisorMeasure` and the prime-to-`p` power sum `sigmaP` be mathlib objects, or are they
   intrinsically tied to *this* Eisenstein-family construction (i.e. project bookkeeping)?
   Mathlib already has `ArithmeticFunction.sigma`; would mathlib want a `sigmaP`/prime-to-`p`
   restricted variant as a first-class arithmetic function?
3. The source explicitly defers the general-`𝒪_L`-valued measure case (RJW §5;
   `Measure/Basic.lean` docstring). Should any mathlib contribution wait for that
   generality (so the framework is added once, in its general form) rather than the
   `𝒪 = ℤ_[p]` special case?
4. Given `K = 1` internal use and no external consumers, is `divisorMeasure_moment`
   intended as reusable API, or is it acceptable to **inline** its 6-line proof into
   `eisensteinFamily_interpolation` (the only caller) and drop the standalone lemma — which
   would be the natural call if it is *not* destined for mathlib?

**Next action:** user answers questions 1–4; re-run `/mathlibable PadicLFunctions.divisorMeasure_moment`
to resolve. Likely outcomes:
- Q1 = no (framework stays project-local) → drop from mathlib consideration; optionally
  inline per Q4. The lemma is correct and well-named; nothing to PR.
- Q1 = yes, Q2 = `divisorMeasure`/`sigmaP` are project-specific → still keep *this* lemma
  project-local; only the generic framework + a *generic* "moment of a finite sum of
  Diracs" lemma would be the mathlib contribution (a different, more abstract decl than
  this one).
- Q1 = yes, Q3 = wait for `𝒪_L` generality → defer; revisit after the §5 development pass.

---

## Next step

User answers questions 1–4 above; re-run `/mathlibable PadicLFunctions.divisorMeasure_moment`
to resolve the verdict. (Or commit directly: the most likely resolution — given the
single-use call site and the fact that the objects this lemma names are project-local — is
to keep `divisorMeasure_moment` in the project, and consider upstreaming only the
*generic* p-adic-measure framework, in its general `𝒪_L` form, as a separate larger effort.)
