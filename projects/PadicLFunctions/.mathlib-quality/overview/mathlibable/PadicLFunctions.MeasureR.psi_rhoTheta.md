# `/mathlibable` report — `PadicLFunctions.MeasureR.psi_rhoTheta`

**Final verdict: `NO-composable-from-mathlib`** (a one-line specialisation of the
project-local theorem `mem_range_iota_iff`; inline it at its single call site).

---

### Baseline (Phase 0)
- lake build:               not re-run (stale/slow per task BUILD NOTE) — **reasoned from source**.
- decl `PadicLFunctions.MeasureR.psi_rhoTheta`: ✓ resolved at
  `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:304`.
- kind:                      theorem
- has sorry:                 no (target body, `rhoTheta`, and `mem_range_iota_iff` all sorry-free;
  `ValuesAtOne.lean` total `sorry` count = 0).
- module docstring summary:  "The p-adic value `L_p(θ,1)` (RJW §6.2, Thm 6.1(ii), decomposition P6)" —
  Leopoldt's formula for `L_p(θ,1)` via the distribution-free antiderivative route.

---

### Statement (Phase 1)

`PadicLFunctions.MeasureR.psi_rhoTheta` is a **theorem** stating the following:

> Let `K` be a complete nonarchimedean (ultrametric) normed field that is a normed
> `ℚ_p`-algebra, with integer ring `R = integerRing K`. Let `η` be a Dirichlet
> character mod `D` valued in `R`, with `D` prime to `p` and `ζ` a primitive `D`-th
> root of unity in `R`, and let `χ` be a Dirichlet character mod `pⁿ` valued in `R`.
> Form the genuine `R`-valued measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` on `ℤ_p` (the
> object `rhoTheta`). Then the operator `ψ` annihilates it: `ψ(ρ_θ) = 0`.

This is the statement "`ρ_θ` is supported on the units of `ℤ_p`", expressed via the
RJW operator `ψ` (the digit-shift / Frobenius-trace operator on `R`-valued measures,
satisfying `φ∘ψ = Res_{pℤ_p}` and `Res_{ℤ_p^×} = 1 − φ∘ψ`). A measure is supported on
`ℤ_p^×` exactly when `ψ` kills it (RJW Cor 3.32).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `K`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
  ( `[CharZero K]` is `omit`-ted) — the coefficient field; `integerRing K` is its valuation ring.
- `D : ℕ`, `[NeZero D]` — the tame conductor; `η : DirichletCharacter (integerRing K) D`.
- `ζ : integerRing K`, `hζ : IsPrimitiveRoot ζ D`; `hD : ¬ (p:ℕ) ∣ D` — tame data, prime to `p`.
- `n : ℕ`, `χ : DirichletCharacter (integerRing K) (p ^ n)` — the wild ( `p`-power) character.

Hypotheses (Lean side): the standing `§5.2` data above; none is used beyond constructing `ρ_θ`.

Conclusion (math): the measure `ρ_θ` is supported on the units, i.e. `ψ(ρ_θ) = 0`.

Conclusion (Lean): `MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0`.

**Proof body (verbatim — load-bearing for the verdict):**
```lean
theorem psi_rhoTheta … :
    MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 :=
  -- `ρ_θ` is in the image of `ι`, whose range is `ker ψ` (RJW Rem 3.33)
  (mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩
```
The proof is a **single term**: `rhoTheta` is *by definition* `iota p K (…)`, hence trivially in
`Set.range (iota p K)`, and the project-local equivalence `mem_range_iota_iff`
(`μ ∈ range (iota) ↔ ψ μ = 0`) converts membership to `ψ μ = 0`. The witness `⟨_, rfl⟩`
exploits that `rhoTheta` is literally an `iota`-application (`rfl`).

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line corollary — a specialisation of `mem_range_iota_iff` to the single
measure `ρ_θ`. Not a new structure, not named after a person/place, not a `## Main results`
headline (it is decomposition step "P6-p5", a bookkeeping lemma feeding `LpFunction_one`).

(Literature width is EXHAUSTIVE regardless; BIG/SMALL is for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (a single term-mode expression).
One-liner verdict: **n/a — kind is `theorem`, not `def`** (the def one-liner exemption table
applies to `def`/`abbrev`/`structure`, not to theorems). Noted for framing: this is a
one-term *proof*, which is itself a strong "this is a thin wrapper, consider inlining" signal —
carried into Phase 6 / Phase 7.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic measure supported on units psi operator kernel Iwasawa algebra image iota" | yes | distributions/measures supported on `ℤ_p^×` are the relevant subspace; "W-valued measures are supported on `ℤ_p^×`"; "when `l` is prime to `p`, `ψ_l` is supported on the units" | Greenberg–Vatsal *Iwasawa theory for Artin reps*; the *Iwasawa Algebras and p-adic Measures* survey (Springer). The supported-on-units ⟺ ψ-kills-it dictionary is standard. |
| 2 | WebSearch (general form) | "Coleman map psi operator measures Z_p^times kernel trace operator p-adic L-function" | yes | ψ is Coleman's trace operator; the unit-supported measures are exactly its kernel; distributions on `ℤ_p^×` ↔ analytic functions (Mellin) | Williams, *Intro to p-adic L-functions* (Warwick LTCC notes); arXiv:2309.15692; Coleman-map literature. |
| 3 | WebSearch (named-after / aliases) | "measure supported on units iff psi equals zero distributions Z_p Mazur Mellin transform restriction Frobenius" | yes | **"The Mellin transform realises a bijection between distributions supported in `ℤ_p^×` and analytic functions, while distributions supported in `pℤ_p` have zero Mellin transform."** | Schneider–Teitelbaum *p-adic Fourier theory* (arXiv:math/0102012); Zagier Mellin appendix. This is the exact dual fact: `Res_{pℤ_p} = φ∘ψ`, so `ψμ=0 ⟺ supported on units`. |
| 4 | ChatGPT MCP | — | **n/a** | — | **No ChatGPT/codex MCP tool is configured in this environment** (tool search surfaced none). Per the skill's documented fallback ("falls back to WebSearch + … nLab/Stacks"), compensated with an extra WebSearch generality level (#3) + a 4th NL search (#10) + nLab fetch (#6). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | — | Neither directory exists (`.mathlib-quality/references/` absent; `refs/` symlink absent). The docstrings cite "RJW" (a Rubin/de-Shalit–style lecture-note source) with TeX line numbers, but the PDF is not present locally. |
| 6 | nLab | `ncatlab.org/nlab/show/Iwasawa+algebra` (fetched) | no | only "completed group ring `ℤ_p[[Γ]] ≅ ℤ_p[[T]]`" | nLab's Iwasawa-algebra page has no operator/measure content; ψ / unit-support not discussed. |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept — it is a concrete statement about one functional on `C(ℤ_p, R)`. No higher-categorical formulation applies. |
| 8 | Stacks Project | concept scan | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; Stacks has no p-adic-measure / Iwasawa-algebra operator theory. |
| 9 | MathOverflow / Math.SE | covered transitively by #1–#3 result sets | yes | confirms the supported-on-units ⟺ `ψ=0` folklore | the dictionary appears repeatedly in MO answers on Coleman maps / Perrin-Riou theory. |
| 10 | recent arXiv (≤5 yrs) | "mathlib4 p-adic L-function measure Iwasawa algebra formalization Dirichlet character measure Z_p" | yes | Narayanan, *Formalization of p-adic L-functions in Lean 3* (arXiv:2302.14491) — builds its **own** measure theory on `ℤ_p` (not upstreamed); arXiv:2309.15692 (Loeffler–Zerbes-style notes) | Confirms even formalised p-adic-L work keeps a bespoke measure layer; no mathlib measure-on-`ℤ_p` exists. |

### Literature summary (Phase 3)

Concept identified as: **"a `p`-adic measure is supported on `ℤ_p^×` iff the (Coleman/Frobenius-trace)
operator `ψ` annihilates it"**, equivalently "`Res_{ℤ_p^×} = 1 − φ∘ψ`, and `Res_{pℤ_p} = φ∘ψ`".
Sources agree on the standard form: **yes** — the supported-on-units ⟺ `ψ = 0` dictionary
(and its Mellin-transform dual) is textbook p-adic L-function machinery.

Most general standard form: *the general theorem* is "ψ kills exactly the unit-supported
measures" (the RJW `Cor 3.32` / `Rem 3.33` package, already present in the project as
`isSupportedOn_units_iff_psi_eq_zero` and `mem_range_iota_iff`).

**Crucial distinction:** the literature standard form is the **general** equivalence. The target
`psi_rhoTheta` is **not** that equivalence — it is its application to **one specific measure
`ρ_θ`** that is, by construction, in the image of `iota`. The literature has nothing to say
about `ρ_θ` as an object: `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` is a project-specific bookkeeping
measure built for the Leopoldt `L_p(θ,1)` computation (RJW §6.2). So the literature confirms
the *ambient theory* is standard, but the *specific declaration* is a bespoke corollary.

Generality dimensions where the literature varies: coefficient ring (`ℤ_p` vs a general
nonarch. valuation ring `R` — the project's `integerRing K` widening is the more general one);
group (`ℤ_p^×` vs Lubin–Tate `𝒪^×` extensions). These vary the *general* theorem, not this corollary.

Disagreement with the literature: **none** — but the literature target is the *general* `ψ`-kernel
theorem, of which this is a trivial instance.

---

### Generality analysis — `PadicLFunctions.MeasureR.psi_rhoTheta` (Phase 4)

Literature-standard form (from Phase 3): the general equivalence `ψ μ = 0 ↔ μ` supported on
`ℤ_p^×` (already in the project as `mem_range_iota_iff` / `isSupportedOn_units_iff_psi_eq_zero`).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `K`, `[NormedAlgebra ℚ_[p] K]`, `[IsUltrametricDist K]`, `[CompleteSpace K]` | complete ultrametric `ℚ_p`-algebra | general nonarch. coefficient ring `R` | already general | the project's `MeasureR` layer is the `R`-valued widening (the *more* general framework); nothing to weaken. |
| 2 | `η, ζ, hζ, hD, χ` (the tame+wild Dirichlet data) | full standing `§5.2` data | — | **YES — all of it is dead weight for this conclusion** | none of `η, ζ, hζ, hD, χ` is *used* by the proof; they exist only to *name* `ρ_θ`. The actual content is "`iota`-image ⊆ `ker ψ`", which needs none of them. |
| 3 | the conclusion is about `rhoTheta` specifically | `ψ (rhoTheta …) = 0` | `ψ μ = 0` for any `μ ∈ range iota` | **YES** | the general statement is `mem_range_iota_iff` itself; `psi_rhoTheta` is its specialisation at one `μ`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — but in the degenerate sense that it
is a *specialisation* of an already-existing project-local general theorem
(`mem_range_iota_iff`), not a weakening of a missing mathlib general form. The "more general
form" is *not missing*: it is `mem_range_iota_iff`, sitting in
`MeasureR/UnitsZp.lean:140`. Number of weakening opportunities: the entire `η/ζ/χ` hypothesis
block + the specialisation-to-`ρ_θ` (the result *is* the general theorem applied once).
Proposed restatement: there is no useful more-general *mathlib-bound* restatement — the general
statement already exists in-project. Cost of "restatement" (= using the general lemma directly):
**CHEAP — it is one mathlib-style `.mp ⟨_, rfl⟩` call**, which is exactly the current proof.

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream |
|---|----------|----------|------------------------|--------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | the hypotheses are already typeclasses/data; the issue is they are *unused*, not un-bundled. | — |
| 2 | sequences/metric → filters/topology? | no | no limits/sequences here; it is a single equation between functionals. | — |
| 3 | construct an object → universal property? | no | nothing is constructed; `ρ_θ` is defined elsewhere. | — |
| 4 | set-with-closure-predicate → bundled substructure? | partially (ambient) | `IsSupportedOn`/`ker ψ` could be a `Submodule` (`ψ.ker`); but that is a remark about the *framework*, not this corollary. | the framework already uses `Set.range (iota)` and `LinearMap`; the ker could be `(psi).ker` — a framework-level improvement, not this lemma's. |
| 5 | vector-space/field-specific → modules/semiring? | no | already at the general `R = integerRing K` level. | — |
| 6 | 1-categorical → higher-categorical? | no | not categorical. | — |
| 7 | concrete index `(ℕ,ℤ,ℝ)` → groups/monoids? | no | the indices (`D`, `pⁿ`) are intrinsic to the Dirichlet-character setup. | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this declaration). One-line reason: `psi_rhoTheta` is a thin
*application* of an existing general lemma; the only idiom improvements (e.g. expose `ker ψ` as a
`Submodule`) are properties of the *framework* (`psi`, `iota`), not of this corollary — and the
framework itself is entirely project-local with no mathlib presence.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`** (no definitional equalities or typeclass-search paths
are introduced). Skipped.

---

### Mathlib search-status: `PadicLFunctions.MeasureR.psi_rhoTheta` (Phase 5)

Searched for **both** the user's form (`ψ(ρ_θ)=0`) **and** the literature-standard general form
("measure supported on units ⟺ ψ = 0", and any p-adic-measure / Coleman-ψ / Iwasawa-algebra
operator API).

```
[A] Lean-Finder       — (no Lean-Finder MCP in env)         n/a: tool unavailable; covered by [C]/[D]
[B] Loogle            "psi"; PadicInt.units,_=0             no hits relevant — of 298 "psi"-named
                                                            mathlib decls, ALL are PSigma /
                                                            Classical.epsilon / parser / convex-
                                                            geometry (SOppSide); none concern
                                                            p-adic measures. The `PadicInt.units,_=0`
                                                            query returned "unknown identifier"
                                                            (no such measure-operator API exists).
[C] LeanSearch        NL: "measure supported on units psi   GET endpoint returned HTTP 405; result
                       operator = 0 p-adic"                 obtained instead via [B]+[D]+web (#10):
                                                            no mathlib p-adic-measure layer exists.
[D] Grep mathlib src  iwasawa / padic.?measure / coleman /  `Iwasawa.lean` = group-action Iwasawa
                       mahler / MeasureR / isSupportedOn /  decomposition (UNRELATED). No
                       psi-operator / restriction-measure   `PadicMeasure`, no `MeasureR`, no
                       (over .lake/packages/mathlib)        `coleman`, no measure-on-`ℤ_p`-as-
                                                            functional. `MahlerBasis.lean` is the
                                                            Mahler basis of `C(ℤ_p,E)` (adjacent
                                                            infra) but has no measures/ψ.
[E] Name pattern      rhoTheta / iota / psi / mahlerK       only in the project tree; nothing in
                                                            mathlib.
```

Concluded: **"not in mathlib (all methods exhausted, plus the literature-standard general
form)."** Mathlib has **none** of the prerequisite objects — no `R`-valued (or `ℤ_p`-valued)
measure type as a `C(X,R) →ₗ R` functional, no `ψ`/`φ` operators, no `iota`, no `Res`, no
`rhoTheta`, no Mahler transform of measures. The formalised p-adic-L work that *does* exist
(Narayanan, Lean 3, arXiv:2302.14491) is a separate project that builds its own measure theory
and was never upstreamed. **Therefore `NO-mathlib-has-it` is impossible** (mathlib has neither
the statement nor any general form of it).

---

### Call sites — `PadicLFunctions.MeasureR.psi_rhoTheta` (Phase 6.0)

Internal use count: **K = 1** (within the project, excluding the declaring lines).
External-to-file callers: **0 distinct files** (the one use is in the *same* file, `ValuesAtOne.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:919` | `rw [sum_seriesEval_mahlerK (p := p) hξ (rhoTheta p K η hζ hD χ), psi_rhoTheta hζ hD χ]` |
| `…/ValuesAtOne.lean:752` | (docstring/comment mention only — "by `sum_seriesEval_mahlerK` + `psi_rhoTheta` pins `c₀`") |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `psi_rhoTheta`?):
- A sibling lemma `psi_rhoA` (`ResidueZeta.lean:696`) proves the analogous `ψ(ρ_a)=0` for the
  residue-zeta measure via `isSupportedOn_units_iff_psi_eq_zero` directly — i.e. the *same pattern*
  is re-derived for a *different* measure, confirming this is a one-off "support on units" wrapper
  per measure, not a reusable API.

**Call-sites signal:** `K = 1` internal use, **0** external, in the same file → the
classic "K = 1 → possibly the wrong abstraction; could be inlined" pattern (per the Phase-6.0
heuristics table). It exists purely to be `rw`-rewritten once inside `sum_seriesEval_Ftilde` /
`LpFunction_one`.

### Composition check (Phase 6)

Can `psi_rhoTheta` be derived in ≤3 chained calls?

Attempt 1 (from the project's own primitives — its actual proof):
`(mem_range_iota_iff (rhoTheta …)).mp ⟨_, rfl⟩`
  - Decls used: `mem_range_iota_iff` (project), `rfl`. **1 call.**
  - Result: **succeeds** — it is the literal proof body.

Attempt 2 (could it be done from **mathlib** primitives instead?):
  - **No.** Mathlib has no `iota`, no `psi`, no `MeasureR`. There is no mathlib lemma to chain.
  - Result: **fails** — mathlib supplies none of the building blocks.

Conclusion: **COMPOSABLE — but from the *project's own* `mem_range_iota_iff`, not from mathlib.**
The composition sketch is the existing 1-line proof: `(mem_range_iota_iff _).mp ⟨_, rfl⟩`. Since
`rhoTheta` is definitionally `iota(…)`, range-membership is `⟨_, rfl⟩` and the project-local
equivalence finishes it.

---

## Verdict: `PadicLFunctions.MeasureR.psi_rhoTheta`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the *general* "supported-on-units ⟺ ψ = 0" dictionary is standard
  (Schneider–Teitelbaum, Williams, Greenberg–Vatsal); but this declaration is its trivial
  application to the bespoke measure `ρ_θ`, which the literature does not name.
- Generality analysis (Phase 4): STRICTLY NARROWER — a specialisation of the already-existing
  project-local general lemma `mem_range_iota_iff`; the `η/ζ/χ` hypotheses are unused. No modern
  idiom applies to the corollary itself.
- Mathlib search (Phase 5): NOT in mathlib, and **no general form is in mathlib either** — mathlib
  has none of `MeasureR` / `psi` / `iota` / `rhoTheta` (the 298 "psi" decls are all unrelated).
- Composition check (Phase 6): COMPOSABLE in 1 line — `(mem_range_iota_iff _).mp ⟨_, rfl⟩` — from a
  **project-local** building block, not a mathlib one.

**Rationale:**

`psi_rhoTheta` is a one-term corollary whose entire content is "the specific measure `ρ_θ`, which
is *by construction* `iota(…)`, lies in `range iota = ker ψ`." Every object in its statement —
`MeasureR`, `psi`, `rhoTheta`, `iota`, `DirichletCharacter (integerRing K)` — is part of the
project's bespoke RJW-§3/§6 p-adic-measure framework, of which **mathlib contains nothing**
(Phase 5 exhausted Loogle, a mathlib-source grep, and the web; the only formalised p-adic-L
measure theory, Narayanan's Lean 3 work, is a separate non-upstreamed project). So neither YES
bucket nor `NO-mathlib-has-it` can apply: mathlib has neither this statement nor any general form
to specialise from. What *does* apply is that the result is a **trivial composition** — its proof
is the single term `(mem_range_iota_iff (rhoTheta …)).mp ⟨_, rfl⟩`, and the call-site evidence
(K = 1 internal use, 0 external, same file; the same pattern re-derived ad hoc for the sibling
measure `ρ_a` in `psi_rhoA`) confirms it is a per-measure wrapper that consumers rewrite once, not
a reusable API. The building block (`mem_range_iota_iff`) is the genuinely-reusable statement and
is project-local. Hence `NO-composable-from-mathlib`, understood as "do not ship this corollary —
it is a 1-line composition of an existing (here, project-local) lemma and should be inlined at its
one call site." The general lemma `mem_range_iota_iff` is the right granularity to keep; `psi_rhoTheta`
is not its own mathlib-worthy unit.

**Refactor-actionable section (NO-composable-from-mathlib):**

WHY not (refactor-actionable):
- The result is a 1-call specialisation of `mem_range_iota_iff` at the measure `ρ_θ` (which is
  definitionally an `iota`-image, so the range-membership witness is `⟨_, rfl⟩`). No new
  mathematical content over `mem_range_iota_iff`. Mathlib has none of the supporting objects, so
  this cannot be upstreamed in any form; within the project it is a thin wrapper.

Building blocks (the genuinely reusable statement — **project-local**, not mathlib, since mathlib
has no p-adic-measure layer):
- `PadicLFunctions.MeasureR.mem_range_iota_iff`
  (`projects/PadicLFunctions/PadicLFunctions/MeasureR/UnitsZp.lean:140`):
  `μ ∈ Set.range (iota p K) ↔ psi p K μ = 0`.
- `PadicLFunctions.MeasureR.rhoTheta` is defined as `iota p K (…)`
  (`ValuesAtOne.lean:290`), so `⟨_, rfl⟩ : rhoTheta … ∈ Set.range (iota p K)`.

Composition sketch (≤3 lines — identical to the present body):
```lean
example : MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 :=
  (mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩
```

Call sites in our project (from Phase 6.0): **K = 1** (`ValuesAtOne.lean:919`).

Refactor plan: at the single call site (`ValuesAtOne.lean:919`, inside `sum_seriesEval_Ftilde`),
replace the rewrite term `psi_rhoTheta hζ hD χ` with the inlined composition
`(mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩` (or, since `rw` wants an equation,
keep a local `have hψ : MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0 :=
(mem_range_iota_iff _).mp ⟨_, rfl⟩` immediately before the rewrite). Then delete the standalone
`psi_rhoTheta` theorem. Note: this is a **project-internal cleanup recommendation**, not a mathlib
action — there is no mathlib target. (The reusable lemma `mem_range_iota_iff` stays; it is the
correct-granularity statement, and is itself separately worth a `/mathlibable` pass only if/when a
p-adic-measure layer is ever proposed for mathlib.)

Next action: **No mathlib PR.** Optionally, as project cleanup, inline the 1-line composition at
`ValuesAtOne.lean:919` and delete `psi_rhoTheta`. Keep `mem_range_iota_iff` as the genuine API.

---

## Next step

No mathlib PR. As an optional project-internal cleanup, inline
`(mem_range_iota_iff (rhoTheta p K η hζ hD χ)).mp ⟨_, rfl⟩` at the single call site
(`projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:919`) and delete the standalone
`psi_rhoTheta` theorem; retain `mem_range_iota_iff` as the reusable statement.
