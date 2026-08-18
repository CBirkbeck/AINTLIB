# `/mathlibable` report — `PadicLFunctions.psi_rhoA`

**Final verdict: `BORDERLINE-needs-human`** (full reasoning in Phase 7).

---

### Baseline (Phase 0)

- lake build:               build not re-run; reasoned from source (per task instruction — build stale/slow here; Phase 0 fallback used)
- decl `PadicLFunctions.psi_rhoA`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean:696`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The residue of ζ_p at s = 1 (RJW §7)" — the analytic-number-theory core of the Kubota–Leopoldt p-adic zeta function near s = 1.

The declaration head:

```lean
omit [CharZero K] in
/-- R7.5b: `ρ_a` is supported on the units. -/
theorem psi_rhoA (a : ℕ) : MeasureR.psi p K (rhoA p K a) = 0 := by
  rw [← MeasureR.isSupportedOn_units_iff_psi_eq_zero, MeasureR.IsSupportedOn, rhoA,
    ← MeasureR.baseChange_res, PadicMeasure.res_iota]
```

Ambient context (`section mass`, `ResidueZeta.lean:432`):
`variable (p : ℕ) [hp : Fact p.Prime]` and
`variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
— with `CharZero K` `omit`-ted for this theorem.

---

### Statement (Phase 1)

`PadicLFunctions.psi_rhoA` is a theorem stating the following:

> Let `K` be a complete nonarchimedean (ultrametric) normed field that is a `ℚ_p`-algebra, with ring of integers `R = integerRing K`. For each natural number `a`, the `R`-valued p-adic measure `ρ_a` on `ℤ_p` is **supported on the units `ℤ_p^×`**; equivalently the ψ-operator annihilates it: `ψ(ρ_a) = 0`.

Here `ρ_a` (`PadicLFunctions.rhoA`, `ResidueZeta.lean:651`) is the §4 *numerator measure* `x⁻¹·Res_{ℤ_p^×}(μ_a)`, concretely defined as the base change to `K` of the `ℤ_p`-level inclusion of `zetaNum a`:

```lean
noncomputable def rhoA (a : ℕ) : MeasureR K ℤ_[p] :=
  MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))
```

where `PadicMeasure.zetaNum p a : PadicMeasure p ℤ_[p]ˣ` is the (unit-living) zeta numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)`, and `μ_a` is the classical Kubota–Leopoldt measure attached to `f_a(t) = 1/(eᵗ−1) − a/(e^{at}−1)`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]` — a complete ultrametric `ℚ_p`-field (the coefficient field; in the project's residue computation eventually `ℂ_p ⊇ ℚ_p(μ_p)`). `[CharZero K]` is present in the section but omitted from this theorem (not needed).
- `a : ℕ` — the auxiliary integer of the Kubota–Leopoldt construction (the `(1 − a)`-twist parameter).

Hypotheses (Lean side): none beyond the typeclasses (a is unconstrained; for the interesting case `gcd(a,p)=1` but the support fact holds for all `a`).

Conclusion (math): the numerator measure `ρ_a` is concentrated on `ℤ_p^×`.

Conclusion (Lean): `MeasureR.psi p K (rhoA p K a) = 0` (an equality of `R`-valued measures, i.e. of elements of `C(ℤ_p, R) →ₗ[R] R`).

Underlying objects (all project-defined, in `PadicLFunctions/MeasureR/*` and `PadicLFunctions/Measure/*`):
- `MeasureR K X := C(X, integerRing K) →ₗ[integerRing K] integerRing K` (`MeasureR/Basic.lean:50`) — an `R`-valued measure as an `R`-linear functional on continuous `R`-valued functions (RJW Def 3.6). This is an Iwasawa-algebra element in functional disguise.
- `MeasureR.psi` (`MeasureR/Toolbox.lean:154`) — the ψ-operator (RJW §3.5.5), the coefficient-free digit shift of the `ℤ_p`-layer.
- `MeasureR.iota` / `PadicMeasure.iota` (`MeasureR/UnitsZp.lean:83`, `Measure/UnitsZp.lean:121`) — the inclusion `Λ(ℤ_p^×) ↪ Λ(ℤ_p)`, pushforward along `ℤ_p^× ↪ ℤ_p`.
- `MeasureR.baseChange` (`MeasureR/BaseChange.lean:39`) — the ring map `PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p]` extending coefficients from `ℤ_p` to `R`.
- `MeasureR.res` / `IsSupportedOn` (`MeasureR/Toolbox.lean:133`, `:137`) — restriction of a measure to a clopen by multiplication by the clopen's characteristic function; "supported on U" means `Res_U μ = μ`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step corollary lemma (a "rhoA-is-unit-supported" bookkeeping fact, docstring tag "R7.5b"). It is not a `def`/`class`/`structure`, not named after a person/place, and not a primary `## Main results` goal — the §7 main results are the analyticity/pole/residue statements of Theorem 7.1; `psi_rhoA` is an intermediate step toward the mass computation. Its proof is a 2-line `rw` chain that applies the *general* project lemmas (`isSupportedOn_units_iff_psi_eq_zero`, `baseChange_res`, `res_iota`) to the *specific* measure `ρ_a`.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL is recorded only for framing.)

### One-line check (Phase 2b)

Body line count: n/a — kind is `theorem`, not `def`/`abbrev`/`structure`. (For the record, the proof body is a single `rw […]` tactic block of ~2 lines; this reinforces the "thin corollary" reading but the one-liner *def* gate does not apply to theorems.)

One-liner verdict: n/a (kind is theorem).

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "p-adic measure supported on units operator psi kernel Iwasawa algebra distribution"                   | yes  | ψ-operator on the Iwasawa algebra of measures; measures = elements of `ℤ_p[[Γ]]`; supported-on-units structure | confirms the φ/ψ + measure-on-`ℤ_p^×` framework is classical (Coleman/Coates–Wiles); no *named* "ψρ_a=0" lemma |
|  2 | WebSearch (operator form)        | "psi operator measure ring of integers Z_p units Coleman map kernel image iota restriction"             | yes  | ψ is the canonical left inverse of φ (=mult-by-p pushforward); ker ψ ↔ Euler-system / cyclotomic-unit eigenspaces; ι = inclusion of measures on `ℤ_p^×` | Coleman/Coates–Wiles, "Combinatorial Congruences and ψ-Operators" (arXiv math/0508159); exactly the φ/ψ/ι setup of the project |
|  3 | WebSearch (general/abstract form)| "phi psi operators Iwasawa algebra Z_p^times pushforward multiplication by p distribution supported units" | yes  | Dwork: `ψ(∑aₙzⁿ)=∑a_{pn}zⁿ`, left inverse of `φ: z↦zᵖ`; `ψ∘z(d/dz)=p·z(d/dz)∘ψ`; Λ=ℤ_p[[Γ]] | the φ/ψ commutation + measure↔power-series dictionary is textbook; matches `psiSeries`, `shiftDiv` in the project |
|  4 | WebSearch (named construction)   | "Kubota-Leopoldt p-adic zeta measure mu_a numerator supported on units restriction Z_p^times Iwasawa"   | yes  | μ_a with `f_a(t)=1/(eᵗ−1)−a/(e^{at}−1)`; restriction `μ_z^{(p)}` of μ to `ℤ_p^×`; `F_z^{(p)}(T)=1/(1−z(1+T)) − 1/(1−zᵖ(1+T)ᵖ)` | Loeffler–Zerbes "An introduction to p-adic L-functions" (arXiv 2309.15692); Coates Bourbaki (numdam SB_1988-1989__31__33); **this is exactly ρ_a's parent construction** |
|  5 | ChatGPT MCP                      | (intended: "standard form of 'a p-adic measure is supported on the units iff ψμ=0', its generality, historical evolution") | n/a  | —                                | **ChatGPT MCP server not installed in this environment** (no `openai`/`chatgpt` tool surfaced; only auth stubs). Compensated with 6 WebSearch queries at 4 generality levels + 2 nLab fetches. |
|  6 | Local references                 | `ls .mathlib-quality/references/` and `refs/` symlink                                                   | n/a  | (directory absent)               | No `.mathlib-quality/references/` dir and no `refs/` symlink in the checkout — recorded `n/a`. |
|  7 | nLab                             | WebFetch `ncatlab.org/nlab/show/Iwasawa+algebra`                                                        | yes  | "the completed group ring `ℤ_p[[Γ]] ≅ ℤ_p[[T]]`" | **stub** — defines the Iwasawa algebra only; no measure interpretation, no φ/ψ, no support characterization. |
|  8 | nCatLab (categorical)            | WebFetch `ncatlab.org/nlab/show/p-adic+L-function`                                                      | n/a  | (HTTP 404)                       | Page does not exist; this is not a categorical concept anyway (analytic number theory). |
|  9 | Stacks Project (alg geom)        | —                                                                                                      | n/a  | —                                | Not an algebraic-geometry concept — p-adic measures / Iwasawa theory are not in Stacks' scope. |
| 10 | MathOverflow / Math.StackExchange| "measure on Z_p restriction to units … supported on … injection measures on units Iwasawa"             | n/a  | —                                | `mathoverflow.net` is blocked for the search user-agent (API 400); the four arXiv/textbook hits above already pin the standard form. |
| 11 | recent arXiv (last 5 years)      | (covered by #1–#4: arXiv 2101.01879, 2109.13218, 2309.15692, math/0508159 surfaced)                     | yes  | same φ/ψ/ι + μ_a framework        | The framework is stable and classical; recent arXiv reproduces it (Loeffler–Zerbes 2023 notes). |

### Literature summary (Phase 3)

Concept identified as: the **ψ-operator on the Iwasawa algebra of p-adic measures**, and specifically the classical fact that a p-adic measure on `ℤ_p` is **supported on `ℤ_p^×` iff `ψμ = 0`** (equivalently iff it lies in the image of the inclusion `ι : Λ(ℤ_p^×) ↪ Λ(ℤ_p)`). In the project this is the *general* theorem `isSupportedOn_units_iff_psi_eq_zero` / `mem_range_iota_iff` (RJW Cor 3.32 / Rem 3.33). The target `psi_rhoA` is the *application* of that general fact to the single zeta-numerator measure `ρ_a`.

Sources agree on the standard form: **yes**. φ = pushforward by mult-by-p, ψ = its left inverse (digit shift `∑aₙ ↦ ∑a_{pn}`), `ψφ = id`, `φψ = Res_{pℤ_p}`, `Res_{ℤ_p^×} = 1 − φψ`, ker ψ = image of ι = unit-supported measures. This is uniform across Coleman, Coates–Wiles, Lang's *Cyclotomic Fields*, Washington's *Cyclotomic Fields* (Ch. 12 "Measures and Distributions"), and the modern Loeffler–Zerbes notes.

Most general standard form: the *general* characterization "`μ` supported on `ℤ_p^×` ⟺ `ψμ = 0` ⟺ `μ ∈ range ι`" — a structural theorem about the Iwasawa algebra, true for *every* measure, with no reference to ζ or to `ρ_a` in particular.

Generality dimensions where the literature varies:
  - coefficient ring: `ℤ_p` (classical) → any complete nonarchimedean `ℚ_p`-algebra `R` (the project's `MeasureR`, the §5 widening). The project already takes the more general `R` here.
  - the object the support fact is applied to: the literature states the *general* characterization, then derives unit-support of specific measures (the zeta numerator, cyclotomic-unit measures, …) as one-line corollaries — it does **not** single out "`ψρ_a = 0`" as a named result.

Disagreement with the literature: **none on content**. The mismatch is one of *granularity*: `psi_rhoA` is a specialisation of the general (literature-standard) characterization to one bespoke measure `ρ_a`, which the literature treats as an immediate corollary rather than a theorem worth a name.

If the literature search had returned nothing this would itself signal "too narrow". It did not return nothing — but what it returned is the **general** theorem and the **general** μ_a/zeta construction, not a `psi_rhoA`-shaped statement. That is the central tension for the verdict.

---

### Generality analysis — `PadicLFunctions.psi_rhoA` (Phase 4)

Literature-standard form (from Phase 3): the structural characterization
`(μ supported on ℤ_p^×) ↔ ψμ = 0 ↔ μ ∈ range ι`, for an arbitrary measure `μ` over an arbitrary complete nonarchimedean coefficient ring.

| # | Parameter / hypothesis                | Current Lean form          | Literature-standard form    | Weaker form exists? | Reason it can/can't be weakened   |
|---|---------------------------------------|----------------------------|------------------------------|---------------------|------------------------------------|
| 1 | the measure `rhoA p K a`              | one *specific* measure `baseChange(ι(zetaNum a))` | an *arbitrary* `μ ∈ range ι` | **yes** | The conclusion `ψμ = 0` holds for *every* `μ` in the image of `ι`, not just `ρ_a`. The genuinely-general statement is `mem_range_iota_iff` (already in the project, `MeasureR/UnitsZp.lean:140`). `ρ_a` is unit-supported *because* it is `baseChange ∘ ι` of something — so the relevant general fact is "anything `baseChange`-from-`ι` is unit-supported", i.e. `baseChange_res` + `res_iota`, both already general. |
| 2 | `[NormedAlgebra ℚ_[p] K]`, `[IsUltrametricDist K]`, `[CompleteSpace K]` | complete ultrametric `ℚ_p`-field | nonarchimedean field with integer ring | borderline | These are the standing assumptions of the whole `MeasureR` layer; the support fact itself uses only the algebraic structure (`res_iota` is proved with `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`). So the *abstract* fact is even more general than this section's typeclasses — but that generality already lives in the general lemmas, not here. |
| 3 | `a : ℕ`                               | unconstrained natural        | the construction parameter   | NO (already maximal) | The support fact holds for all `a` (no coprimality needed); the statement is already as general in `a` as it can be. The narrowness is not in `a` — it is in fixing the *whole measure* to be `ρ_a`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in a degenerate way. The narrowing is not "a hypothesis that should be weakened by one typeclass"; it is that the statement is an *instance* (the measure `ρ_a` is a fixed concrete object) of a *general structural theorem* that the project already proves separately (`mem_range_iota_iff` / `isSupportedOn_units_iff_psi_eq_zero` + `res_iota`). The "more general form" is not a re-typeclassed `psi_rhoA`; it is the already-existing general lemma, of which `psi_rhoA` is a 2-line corollary.

Number of weakening opportunities found: 1 substantive (generalise the *object* `ρ_a` to "any `baseChange`-of-`ι` measure", which is precisely the content of the existing general lemmas — i.e. there is nothing new to prove; the general result already exists in the project).

Proposed restatement: not applicable as a *new* statement — the maximally-general form is the **already-present** `MeasureR.isSupportedOn_units_iff_psi_eq_zero` (`MeasureR/Toolbox.lean:276`) together with `MeasureR.res_iota` (`MeasureR/UnitsZp.lean:105`) and `MeasureR.baseChange_res` (`MeasureR/BaseChange.lean:175`). `psi_rhoA` adds no generality over these.

Cost of restatement: CHEAP (it is literally the 2-line proof body already present) — but this does not produce a *new* mathlib-worthy statement; it points back at the general lemmas.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" → typeclass/instance? | no | The hypotheses are already typeclasses (`NormedAlgebra`, `IsUltrametricDist`, …); nothing bundled to unbundle. | — |
|  2 | sequences/metric → filters/topological? | no | No limit/convergence content here; this is a purely algebraic identity of functionals. | — |
|  3 | construct an object → universal-property class? | partial (but already done by the project) | The "supported on units" notion is already characterised by a universal/structural property: `μ ∈ range ι ↔ ψμ = 0` (`mem_range_iota_iff`). `psi_rhoA` is a *consumer* of that characterisation, not a place to introduce a new one. | the project already gets the range/kernel characterisation; `psi_rhoA` just applies it |
|  4 | set-with-closure-predicate → bundled substructure? | no | `IsSupportedOn` is a `Prop` on measures; no lattice of supports is in play for this corollary. | — |
|  5 | vector-space/field-specific → weaken typeclasses? | no (already general in `R`) | The `MeasureR` layer is already the `R`-coefficient generalisation of the `ℤ_p`-only `PadicMeasure` layer. | — |
|  6 | 1-categorical → higher-categorical? | no | Not a categorical statement. | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary monoid/group? | no | `a : ℕ` is the construction's parameter, not an index to abstract; the support fact is already uniform in `a`. | — |

Modern idiom available: **no** (for `psi_rhoA` itself). One-line reason: the modern, structural form of this mathematics — "kernel of ψ = image of ι = unit-supported measures" — already exists in the project as a *general* theorem (`mem_range_iota_iff` / `isSupportedOn_units_iff_psi_eq_zero`); `psi_rhoA` is a downstream application of it, not a candidate modernisation in its own right.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (No definitional equalities or typeclass-search paths are introduced.)

---

### Mathlib search-status: `PadicLFunctions.psi_rhoA` (Phase 5)

Five-method search (read `references/mathlib-search.md`; mathlib source tree present at `.lake/packages/mathlib/Mathlib`, so methods D/E were run directly against source — the most reliable signal here):

[A] Lean-Finder       (web service; not reachable from this sandboxed worker) — n/a: relied on the local mathlib grep (D/E), which is authoritative for "does the decl/infrastructure exist".
[B] Loogle            type-pattern `C(_, _) →ₗ[_] _` for "measure as functional", `_ = 0` ψ-annihilation — n/a (no network from worker); D/E cover the existence question directly.
[C] LeanSearch        NL: "p-adic measure supported on units", "psi operator kernel measure" — n/a (no network); D/E cover it.
[D] Grep mathlib src  `Iwasawa`, `PadicMeasure`/`padicMeasure`/`p-adic measure`/`p-adic distribution`, `IsSupportedOn`/`supported on`, `KubotaLeopoldt`/`p-adic L-function`/`p-adic zeta`, `psi`/`psiSeries`/`shiftDiv`, `baseChange.*measure`, `zetaNum`/`rhoA`, `mahlerTransform` — **no relevant hits**.
[E] Name pattern      grep for `psi_rhoA`, `rhoA`, `zetaNum`, `MeasureR`, `mahlerTransform`, `isSupportedOn_units_iff_psi_eq_zero` across `Mathlib/` — **no hits**.

What the grep found, and why each is irrelevant:
- `Mathlib/GroupTheory/GroupAction/Iwasawa.lean` — the **Iwasawa decomposition / Iwasawa's lemma on group actions** (simplicity of groups), *not* the Iwasawa algebra of measures. Unrelated.
- `nLab Iwasawa+algebra` (external) confirms mathlib's lack: the only "Iwasawa algebra" notion is `ℤ_p[[Γ]]` as a completed group ring; mathlib does not even build that as a measure algebra.
- `IsSupportedOn`/"supported on" hits (`Prokhorov.lean`, `StronglyMeasurable/*`, bump functions, filters) — the `MeasureTheory`/`Filter` notions of support of a *Bochner/Lebesgue measure or a function*, a completely different object from "a `C(X,R)→ₗR` functional fixed by multiplication by a clopen indicator".
- `Mahler` hits (`MahlerMeasure.lean`, `MahlerBasis.lean`, `Padics/AddChar.lean`) — the **Mahler measure (height) of a polynomial** and the **Mahler basis of `C(ℤ_p, ℚ_p)`**; neither is the project's `mahlerTransform` of a p-adic measure.
- `psi` hit (`Chebyshev.lean`) — the second Chebyshev function ψ(x) in analytic number theory; unrelated to the digit-shift operator.
- `res`/restriction hits (`MeasureTheory/Measure/Restrict.lean`, `Trim.lean`) — restriction of a *Bochner/Lebesgue measure to a measurable set*, not multiplication of a functional by a clopen characteristic function.

Searched for both:
  - the user's current form (`ψ(ρ_a)=0` for the specific zeta-numerator measure): **absent** — `ρ_a`, `zetaNum`, `μ_a` and the entire Kubota–Leopoldt apparatus are not in mathlib.
  - the literature-standard form (`μ supported on ℤ_p^× ⟺ ψμ=0 ⟺ μ∈range ι`, for arbitrary `μ`): **also absent** — mathlib has neither the ψ-operator on measures, nor `iota`, nor `MeasureR`/`PadicMeasure`, nor the notion of a measure being "supported on a clopen" in this functional-analytic sense.

Concluded: **not in mathlib** (all methods exhausted, plus the literature-standard general form). Mathlib does **not** even contain the *building blocks* (`MeasureR`, ψ, `iota`, `baseChange`, `zetaNum`) from which `ψ(ρ_a)=0` could be composed — every ingredient is project-defined. mathlib's p-adic analysis presently stops at `PadicInt`, the Mahler basis, p-adic add-characters, and `ℂ_p`; it has no theory of p-adic measures / the Iwasawa algebra of measures / p-adic L-functions.

---

### Call sites — `PadicLFunctions.psi_rhoA` (Phase 6.0)

Internal use count: **K = 1** (within the project; one use, and it is in the *declaring file*).
External-to-file callers: **0 distinct files**.

| Caller file:line               | Usage pattern (one-line excerpt)                                            |
|--------------------------------|------------------------------------------------------------------------------|
| ResidueZeta.lean:1020          | `rw [sum_seriesEval_mahlerK (p := p) hξ (rhoA p K a), psi_rhoA]` (then `simp [mahlerK]`) |

Inline-derivation grep (was `ψ(ρ_a)=0` re-derived elsewhere without `psi_rhoA`?): **(none)** — the only place that needs it uses `psi_rhoA`. The fact is not silently re-proved at any other site.

What the pattern tells us: **K = 1, in-file only.** Per the Phase-6 signal table this is "possibly the wrong abstraction — could be inlined; lean toward NO-composable". It is genuine load-bearing API for exactly one downstream step (making the `𝓐_ρ`-sum over the p-th roots of unity vanish in the c₀-mass computation, `ResidueZeta.lean:1018–1021`), but there is precisely one consumer and it lives in the same file as the definition.

### Composition check (Phase 6)

The relevant composition question for `/mathlibable` is "can **mathlib's** primitives compose to give this in ≤3 calls?" — and the answer is decisively **no**, because mathlib has none of the primitives (`MeasureR`, ψ, `iota`, `baseChange`). So there is no mathlib composition to inline.

For completeness, the *project-internal* composition (which is what the proof already is) is:

Attempt 1: `rw [← isSupportedOn_units_iff_psi_eq_zero, IsSupportedOn, rhoA, ← baseChange_res, res_iota]`
  - Project decls used: `MeasureR.isSupportedOn_units_iff_psi_eq_zero`, `MeasureR.IsSupportedOn`, `rhoA`, `MeasureR.baseChange_res`, `PadicMeasure.res_iota`.
  - Mathlib decls used: **none**.
  - Result: succeeds (2-line proof in the source).
  - Notes: this is a clean ≤3-rewrite composition of *project* lemmas. It is exactly the kind of "thin corollary of the general lemma applied to a specific object" that `/mathlibable` flags as NO-composable *when the building blocks are in mathlib*. Here the building blocks are in the **project**, not mathlib — so the corollary is composable-from-the-project, and the question of mathlib-worthiness shifts entirely onto whether the *general framework* (not this corollary) should be upstreamed.

Conclusion: **NOT-COMPOSABLE from mathlib** (mathlib lacks every primitive). Composable trivially from *project* lemmas — which is the decisive observation for the verdict.

---

## Verdict: `PadicLFunctions.psi_rhoA`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the ψ-operator on the Iwasawa algebra of measures and the characterization "supported on `ℤ_p^×` ⟺ ψμ=0 ⟺ μ∈range ι" are firmly classical (Coleman, Coates–Wiles, Washington Ch. 12, Loeffler–Zerbes notes). But the literature states the **general** theorem and derives unit-support of specific measures as one-line corollaries; it gives no named "`ψρ_a=0`" result. The μ_a / zeta-numerator construction underlying `ρ_a` is exactly the classical Kubota–Leopoldt one.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD**, degenerately — `psi_rhoA` is an *instance* (fixed concrete measure `ρ_a`) of the project's own general theorem `mem_range_iota_iff` / `isSupportedOn_units_iff_psi_eq_zero`. Phase 4c found no modern-idiom improvement *for the corollary itself*; the structural form already exists as the general lemma.
- Mathlib search (Phase 5): **not in mathlib, and not composable from mathlib** — mathlib has *no* theory of p-adic measures / the Iwasawa algebra of measures / the ψ-operator / `iota` / p-adic L-functions. Every ingredient (`MeasureR`, `PadicMeasure`, `psi`, `baseChange`, `zetaNum`, `rhoA`) is project-defined. The `Iwasawa.lean`, `Mahler*`, `Restrict.lean`, `Chebyshev.lean` hits are all unrelated namesakes.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib**; composable in 2 lines from *project* lemmas. Call sites: **K = 1**, in the declaring file only, no external consumers, no inline re-derivations.

**Rationale (synthesis):**

This declaration sits at the intersection of two findings that pull in opposite directions, which is exactly what makes it BORDERLINE rather than a clean YES or NO.

On one hand, `psi_rhoA` is *not itself* a mathlib candidate: it is a `SMALL`, two-line `rw` corollary that applies a *general* structural theorem (`isSupportedOn_units_iff_psi_eq_zero`, plus `baseChange_res` and `res_iota`) to one bespoke measure `ρ_a`, has a single in-file consumer, and is strictly narrower than the literature-standard form (which is the general "ψμ=0 ⟺ unit-supported" characterization, of which this is an instance). By every local signal — granularity, call-site count, "corollary of a general lemma" shape — it is the kind of thing that, *if the general lemma were in mathlib*, would be NO-composable-from-mathlib (just apply the general lemma at the one call site).

On the other hand, the standard NO buckets are unavailable on their own terms, and that is decisive. `NO-mathlib-has-it` fails the verdict gate: Phase 5's conclusion is "not in mathlib", not "found in mathlib as X" — there is no mathlib decl to cite. `NO-composable-from-mathlib` also fails its gate: Phase 6 concluded NOT-COMPOSABLE *from mathlib* (mathlib lacks `MeasureR`, ψ, `iota`, `baseChange` entirely), so there is no ≤3-line mathlib composition to inline at the call site. The composition that does exist is from *project* lemmas, which is not what that bucket means. And `YES-*` is wrong too: this specific corollary is strictly narrower than the literature standard (so not `YES-add-as-is`), yet the "more general form" is not a re-typeclassed `psi_rhoA` to hand to `/generalise` — it is the project's *already-existing* general lemma, so there is no new statement to propose (so not `YES-but-generalise-first` in the usual sense either).

The genuine question is therefore one the skill cannot resolve from evidence alone: **the entire surrounding framework — `PadicMeasure` / `MeasureR`, the φ/ψ operators, `iota`, `baseChange`, the Iwasawa algebra of measures, and the Kubota–Leopoldt zeta apparatus — is absent from mathlib, and whether any of it (and at what grain) should be upstreamed is a large project-policy and mathematical-taste call.** `psi_rhoA` itself is a leaf corollary that should never be upstreamed in isolation; but it is a leaf of a tree whose *trunk* (the general `isSupportedOn_units_iff_psi_eq_zero` / `mem_range_iota_iff` characterization, and the `MeasureR`/ψ infrastructure beneath it) is exactly the sort of foundational p-adic-measure theory mathlib currently lacks and might want. That is a decision for the maintainer, not the skill.

**Refactor-actionable detail / numbered questions (≤5):**

1. **Framework scope.** Is the AINTLIB plan to eventually upstream the p-adic-measure / Iwasawa-algebra infrastructure (`MeasureR`, `PadicMeasure`, the φ/ψ operators, `iota`, `baseChange`) to mathlib, or to keep it project-local as scaffolding for the residue/L-function results? (If project-local → `psi_rhoA` is correctly a private-ish in-file corollary and drops out of mathlib consideration entirely.)

2. **Right grain for the trunk.** If yes to (1): the mathlib-worthy statement is the **general** characterization `MeasureR.isSupportedOn_units_iff_psi_eq_zero` (= RJW Cor 3.32) together with `MeasureR.mem_range_iota_iff` (= RJW Rem 3.33), *not* `psi_rhoA`. Should the next `/mathlibable` runs target those general lemmas (and the `MeasureR` def itself) rather than this corollary?

3. **Coefficient generality.** The general lemmas are proved with `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]` — i.e. they hold over an arbitrary nonarchimedean field with integer ring. For an eventual mathlib statement, is the intended generality "arbitrary complete nonarchimedean `ℚ_p`-algebra" (the `MeasureR` layer) or the `ℤ_p`-only `PadicMeasure` layer, or both linked by `baseChange`? (Mathlib would want the most general — the `MeasureR` layer.)

4. **Inline the corollary.** Independent of (1)–(3): `psi_rhoA` has exactly one consumer (`ResidueZeta.lean:1020`) and a 2-line proof. Would you prefer to keep it as a named in-file lemma (current state — fine for a dev branch), or inline `rw [← isSupportedOn_units_iff_psi_eq_zero, IsSupportedOn, rhoA, ← baseChange_res, res_iota]` at that one call site? (No mathlib bearing either way; purely project hygiene.)

Next action: the maintainer answers (1)–(3) to fix the upstreaming policy; the practical conclusion for **`psi_rhoA` specifically is "do not upstream this corollary"** under any answer — it is a leaf application. If the framework *is* slated for mathlib, re-run `/mathlibable` on `MeasureR.isSupportedOn_units_iff_psi_eq_zero`, `MeasureR.mem_range_iota_iff`, and the `MeasureR` definition (the trunk), which are the genuine candidates.

---

## Next step

Maintainer answers questions 1–3 to set the p-adic-measure-framework upstreaming policy. Regardless of the answer, `psi_rhoA` itself stays project-local (a one-step, single-consumer corollary of the general unit-support characterization); it is not upstreamed in isolation. If the framework is destined for mathlib, the real `/mathlibable` targets are the *general* lemmas `MeasureR.isSupportedOn_units_iff_psi_eq_zero` and `MeasureR.mem_range_iota_iff` (RJW 3.32/3.33) and the `MeasureR` measure type — not this corollary. Optionally (question 4), inline the 2-line proof at its single call site (`ResidueZeta.lean:1020`).
