# /mathlibable report — `Chebotarev.exists_phase_mem_Icc_mul_exp`

### Baseline (Phase 0)
- lake build:               not re-run (env note: local build stale; reasoning from source — declaration is sorry-free and elaborated in the committed file)
- decl `Chebotarev.exists_phase_mem_Icc_mul_exp`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:422`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` for the effective lattice-point count (Gun–Ramaré–Sivaraman); this file is an author-earmarked `ForMathlib/` helper bundle.
- namespace:                 `Chebotarev` (opened line 79, closed line 673); qualified name **confirmed** `Chebotarev.exists_phase_mem_Icc_mul_exp`.

---

### Statement (Phase 1)

`exists_phase_mem_Icc_mul_exp` states the **polar parametrization of a complex number by a phase in the unit interval**: for every `z : ℂ` there is a real `θ ∈ [0,1]` with

  `(‖z‖ : ℂ) · exp((2π·θ − π)·i) = z`.

The witness is `θ = (arg z + π) / (2π)`. It lands in `[0,1]` because `arg z ∈ (−π, π]`. The phase identity holds because the affine substitution `2π·θ − π = arg z` turns the claimed exponential into the standard polar form `‖z‖ · exp(arg z · i) = z`.

Mathematically this is the **principal-argument polar decomposition `z = ‖z‖ e^{i arg z}`, re-coordinatised** so the angle is reported as a number in `[0,1]` via the affine bijection `arg ↦ (arg + π)/(2π)` carrying `(−π, π] → (0, 1]` (extended to the closed `[0,1]`).

Variables / typeclasses involved (Lean side):
- `z : ℂ` — the complex number being decomposed. No typeclass parameters; everything is over the fixed field `ℂ`.

Hypotheses (Lean side): none.

Conclusion (math): every `z ∈ ℂ` is `‖z‖ · exp((2πθ − π)i)` for some `θ ∈ [0,1]`.
Conclusion (Lean): `∃ θ : ℝ, θ ∈ Icc (0:ℝ) 1 ∧ (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z`.

---

### Size classification (Phase 2a)

Verdict: SMALL
Reason: a helper existence-lemma (polar form, reparametrised) feeding one internal consumer; not a named theorem, not a new structure, not a `## Main results` entry.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (it is a `theorem`, not a `def`).
One-liner verdict: n/a — kind is `theorem`. The defeq/diamond/API-name exemptions do not apply to propositions.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found              | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "polar decomposition complex number z = \|z\| exp(i arg z) argument in (-pi, pi] standard form" | yes  | `z = ‖z‖ e^{iθ}`, θ = principal arg, range `(−π,π]` | LibreTexts / Wikipedia / GeeksforGeeks all give `z = re^{iθ}`, `r=‖z‖`, `θ=arg z`. Range conventions `(−π,π]` or `[0,2π)`. No source rescales the angle to `[0,1]`. |
|  2 | WebSearch (mathlib form)         | "mathlib4 Complex.norm_mul_exp_arg_mul_I polar form exists argument unit interval"              | yes  | `↑‖x‖ * exp(↑x.arg * I) = x` (`norm_mul_exp_arg_mul_I`); `arg ∈ Ioc(-π,π]` (`arg_mem_Ioc`) | mathlib's polar form is **equational, not existential**; angle is `arg`, range `(−π,π]`. Confirms the `[0,1]`-rescaled existential is NOT a mathlib/literature idiom. |
|  3 | WebSearch (named-after / aliases)| (covered by #1) "polar form / phase / principal argument" common aliases                        | yes  | same as #1; also "phasor" `e^{iφ}` in EE | The `(2πθ − π)` map is a bespoke `[0,1]`→`[−π,π]` cube-coordinate, not a named transform. |
|  4 | ChatGPT MCP                      | (unavailable in this environment — fallback per task note)                                      | n/a  | —                                | MCP down; compensated by 3 WebSearch queries + direct mathlib-source reading (the authoritative channel for "is the standard form already there"). |
|  5 | Local references                 | `refs/Chebotarev/` (gitignored PDFs) — Gun–Ramaré–Sivaraman §3.3, Widmer GTM 110               | n/a  | not separately readable here     | The cited source uses polar/Lipschitz boundary parametrization; the `[0,1]` cube coordinatisation is an implementation choice of the formalisation, not a theorem stated in the paper. |
|  6 | nLab                             | "polar form complex number" / "argument (complex analysis)"                                    | n/a  | standard `z=re^{iθ}`             | nLab has no special abstract form beyond #1; not a categorical concept. |
|  7 | nCatLab                          | —                                                                                              | n/a  | not a categorical concept        | polar form of a scalar; nothing higher-categorical. |
|  8 | Stacks Project                   | —                                                                                              | n/a  | not an algebraic-geometry concept | complex-analytic scalar identity. |
|  9 | MathOverflow / Math.StackExchange| "principal argument range polar form existence"                                                | n/a  | standard; range `(−π,π]` debated  | The only "research" angle is the range convention, already settled in #1/#2. |
| 10 | recent arXiv (last 5 years)      | "polar form complex" + reparametrisation                                                        | n/a  | nothing newer than the classical identity | This is 19th-century complex analysis; no modern reformulation. |

The protocol passed: WebSearch ran 3 distinct queries at different generality levels (literature-standard, mathlib-specific, aliases); local refs and nLab/Stacks/MathOverflow/arXiv each checked or `n/a` with reason; ChatGPT MCP recorded `n/a` (environment-down) and compensated by reading mathlib source directly.

### Literature summary (Phase 3)

Concept identified as: **polar form / polar decomposition of a complex number** (`z = ‖z‖ e^{i arg z}`), here re-coordinatised to report the phase as a parameter in `[0,1]`.
Sources agree on the standard form: yes — `z = ‖z‖ e^{iθ}`, `θ = arg z`. The only variation is the angle range convention (`(−π,π]` principal vs `[0,2π)`).
Most general standard form: every `z` in a field/algebra with a `‖·‖` and an `arg` satisfies `z = ‖z‖ e^{i arg z}`; in mathlib this is exactly `Complex.norm_mul_exp_arg_mul_I` together with `Complex.arg_mem_Ioc` for the range.
Generality dimensions where the literature varies:
  - angle range: `(−π,π]` (principal, mathlib's choice) vs `[0,2π)` vs — here — the bespoke affine image `[0,1]`. None is "more general"; they are coordinate choices.
  - ambient object: scalar `ℂ` only. No literature generalises this particular *existential-over-`[0,1]`* statement to other structures.
Disagreement with the literature: the literature/mathlib state the polar form **equationally** with the angle equal to `arg z` in `(−π,π]`; the Chebotarev lemma states it **existentially** with the angle rescaled into `[0,1]` (the cube coordinate). That `[0,1]` rescaling is a formalisation-local convenience, not a standard mathematical form.

---

### Generality analysis — `Chebotarev.exists_phase_mem_Icc_mul_exp`

Literature-standard form (from Phase 3): `Complex.norm_mul_exp_arg_mul_I : ‖x‖ * exp (arg x * I) = x`, with `Complex.arg_mem_Ioc : arg z ∈ Ioc (-π) π`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `z : ℂ`                | concrete field `ℂ` | concrete `ℂ` (polar form is `ℂ`-specific via `arg`) | NO | `arg` and this polar form are defined only for `ℂ`; no typeclass abstraction in mathlib to weaken to. Not a generality defect. |
| 2 | phase coordinate `θ ∈ Icc 0 1` (existential), phase `exp((2πθ−π)i)` | `[0,1]`-rescaled existential | `arg z ∈ Ioc(-π,π]`, phase `exp(arg z · i)` (equational) | the statement is *less* canonical, not less general | The `[0,1]` reparametrisation is a **specialisation/re-coordinatisation** of the standard equational polar form, chosen to match the unit-cube `[0,1]^{r-1}` coordinates of the Lipschitz cover. It is strictly more bespoke than mathlib's form. |

### Generality verdict (Phase 4b)

The current form is: NOT the maximally-canonical form — it is a re-coordinatised SPECIALISATION of mathlib's equational polar form (`norm_mul_exp_arg_mul_I` + `arg_mem_Ioc`).
Number of weakening opportunities found: 0 in the typeclass sense (it is `ℂ`-specific by nature). But the existential `[0,1]`-phase shape is not a generalisation candidate for mathlib — it is a downstream convenience derived from primitives mathlib already has.
Proposed restatement: n/a for a generalisation. The relevant observation for the verdict is that the statement is a thin existential wrapper over `norm_mul_exp_arg_mul_I`, not a new theorem.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | bundled hypotheses → typeclasses? | no | no "let X be a foo" preamble; `z : ℂ` only | — |
| 2 | sequences/metric → filters/topology? | no | a pointwise algebraic identity; no limit content | — |
| 3 | construct object → universal-property class? | no | nothing to characterise universally | — |
| 4 | set+closure-predicate → bundled substructure? | no | not a substructure statement | — |
| 5 | vector-space/field-specific → weaker typeclass? | no | `arg`/polar form is intrinsically `ℂ`; mathlib has no abstraction to weaken into | — |
| 6 | 1-categorical → higher-categorical? | no | a scalar identity | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | the only "index" is the `[0,1]` phase coordinate, which is the bespoke choice, not a generalisation target | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no.
One-line reason: this is the classical complex polar form; mathlib already states it in its idiomatic equational form (`norm_mul_exp_arg_mul_I`). The `[0,1]`-rescaled existential is a *less* idiomatic, project-local re-coordinatisation — moving toward it would be a de-modernisation.

---

### Diamond / defeq risk — n/a

n/a — declaration kind is `theorem` (no definitional equalities or instance-search paths introduced).

---

### Mathlib search-status: `Chebotarev.exists_phase_mem_Icc_mul_exp`

[A] Lean-Finder       (index tool unavailable in this environment)     n/a: reason — lean_leansearch/loogle MCP not resolvable here (per task note); substituted by authoritative mathlib-source grep below.
[B] Loogle            (index tool unavailable)                          n/a: reason — same; the type pattern `∃ θ, θ ∈ Icc 0 1 ∧ ‖z‖ * exp((2πθ−π)i) = z` is bespoke and would not match a mathlib decl anyway (confirmed by [D]/[E]).
[C] LeanSearch        (index tool unavailable)                          n/a: reason — same; NL query "polar form exists phase unit interval" — covered by WebSearch #2 which surfaced the mathlib docs (only equational forms).
[D] Grep mathlib src  `norm_mul_exp_arg_mul_I`, `norm_mul_cos_add_sin_mul_I`, `arg_le_pi`, `neg_pi_lt_arg`, `arg_mem_Ioc`, `∃.*(exp\|arg).*(Icc\|Ico\|Ioc\|Ioo)`, `exists.*phase`, `polarCoord`  | hits on the **equational** polar forms + range lemmas; **zero** hits on any existential `[0,1]`/interval phase lemma.
[E] Name pattern      `exists_phase`, `exists_.*arg`, `polarCoord` over `Analysis/SpecialFunctions/Complex/` and `NumberTheory/.../CanonicalEmbedding/` | no existential-phase lemma; `mixedEmbedding.polarCoord` / `polarCoordReal` exist but are change-of-variable homeomorphisms (for integration), not this pointwise existential.

Searched for both:
  - the user's current form (existential, phase in `[0,1]`) — **not in mathlib**.
  - the literature-standard form (equational, angle `arg z ∈ (−π,π]`) — **IS in mathlib**:
    - `Complex.norm_mul_exp_arg_mul_I` — `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:56` — `‖x‖ * exp (arg x * I) = x`.
    - `Complex.arg_mem_Ioc` — `Arg.lean:136` — `arg z ∈ Set.Ioc (-π) π`; with corollaries `Complex.arg_le_pi` (`:155`) and `Complex.neg_pi_lt_arg` (`:158`).

Concluded: **found the building blocks** (`Complex.norm_mul_exp_arg_mul_I`, `Complex.arg_le_pi`, `Complex.neg_pi_lt_arg`); the user's `[0,1]`-rescaled existential form is **not** in mathlib but is a short composition of these. (The proof body in fact already *is* this composition.)

---

### Call sites — `Chebotarev.exists_phase_mem_Icc_mul_exp`

Internal use count: 1 (within the Chebotarev project, NOT counting the declaring file's own statement line).
External-to-file callers: 1 file — the same file, `NormLeOneLipschitz.lean` (no other project/file uses it).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| NormLeOneLipschitz.lean:564 | `choose θ hθmem hθeq using fun w ↦ exists_phase_mem_Icc_mul_exp (x.2 w)` (in `mem_iUnion_image_liftToMixed_of_eq`, to read the phases off the complex coordinates of `x`) |

(Line 557 is only a docstring mention.)

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?): (none) — the only polar-phase extraction in the file goes through this lemma.

Call-sites signal: K = 1 internal use, single consumer, in the same file. Per the Phase 6 table this leans toward NO-composable (possibly the wrong abstraction / inlinable) — it exists purely to feed the one `choose` in `mem_iUnion_image_liftToMixed_of_eq`.

---

### Composition check (Phase 6)

Can `exists_phase_mem_Icc_mul_exp` be derived from mathlib in ≤3 chained calls?

Attempt 1: provide the explicit witness and discharge with mathlib primitives.
```lean
example (z : ℂ) :
    ∃ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 ∧
      (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z :=
  ⟨(z.arg + Real.pi) / (2 * Real.pi),
   ⟨by positivity-style: div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) (by positivity),
    by rw [div_le_one (by positivity)]; linarith [Complex.arg_le_pi z]⟩,
   by -- the phase exponent (2π·θ − π) equals arg z by field_simp/ring, then:
      simpa using Complex.norm_mul_exp_arg_mul_I z⟩
```
  - Mathlib decls used: `Complex.neg_pi_lt_arg`, `Complex.arg_le_pi` (equivalently `Complex.arg_mem_Ioc`), `Complex.norm_mul_exp_arg_mul_I`. Plus generic `linarith`/`field_simp`/`positivity` glue.
  - Result: succeeds — this is precisely the committed proof (lines 425–436), which is exactly: pick `θ = (arg z + π)/(2π)`; bounds from `neg_pi_lt_arg` + `arg_le_pi`; equation by rewriting `2πθ − π = arg z` (a `field_simp; ring` step) and applying `norm_mul_exp_arg_mul_I`.
  - Notes: the existential + the affine `[0,1]` reparametrisation are the only "new" content, and both are trivial bookkeeping around the one substantive mathlib lemma `norm_mul_exp_arg_mul_I`.

Conclusion: **COMPOSABLE** — 3 mathlib calls (`neg_pi_lt_arg`, `arg_le_pi`, `norm_mul_exp_arg_mul_I`) with `linarith`/`field_simp` glue. No new mathematical idea; the "phase in `[0,1]`" shape is a project-local coordinate convenience.

Composition-heuristic check: the witness-provision + `simpa using norm_mul_exp_arg_mul_I` is a one-real-lemma application wrapped in arithmetic glue (`field_simp; ring` to reconcile `2πθ − π = arg z`, `linarith` for the interval). The arithmetic is bookkeeping, not a second mathematical step — this is the "single substantive call + glue" case, which the heuristics count as composable, not a disguised proof.

---

## Verdict: `Chebotarev.exists_phase_mem_Icc_mul_exp`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the concept is the classical complex polar form `z = ‖z‖ e^{i arg z}`; mathlib states it equationally as `Complex.norm_mul_exp_arg_mul_I` with range `Complex.arg_mem_Ioc`. The `[0,1]`-rescaled *existential* is a bespoke coordinate convenience, not a standard or more-general statement.
- Generality analysis (Phase 4): the form is `ℂ`-specific by nature (no typeclass weakening possible) and the `[0,1]` phase shape is a *specialisation/re-coordinatisation* of mathlib's polar form, not a generalisation target; no modern idiom available (4c all `no`).
- Mathlib search (Phase 5): not in mathlib as-is, but the building blocks are — `Complex.norm_mul_exp_arg_mul_I`, `Complex.arg_le_pi`, `Complex.neg_pi_lt_arg` (= `Complex.arg_mem_Ioc`).
- Composition check (Phase 6): COMPOSABLE in 3 mathlib calls + arithmetic glue; the committed proof *is* that composition.

**Rationale:**

This lemma is the standard complex polar decomposition with the angle re-reported as a parameter in `[0,1]` (via `arg ↦ (arg+π)/(2π)`) so it lines up with the unit-cube `[0,1]^{r-1}` coordinates of the Lipschitz frontier cover. Mathlib already owns the entire mathematical content: `Complex.norm_mul_exp_arg_mul_I` gives `‖z‖·exp(arg z·i) = z`, and `Complex.arg_mem_Ioc` (hence `arg_le_pi` / `neg_pi_lt_arg`) gives the range that places `(arg z + π)/(2π)` in `[0,1]`. Producing the existential from these is a `⟨witness, linarith-bounds, simpa using norm_mul_exp_arg_mul_I⟩` composition — exactly what lines 425–436 do. There is no missing mathlib API and no more-general true statement to upstream: the only thing the lemma adds is the project's `[0,1]` cube-coordinate convention, which is meaningless outside this Lipschitz-cover construction. With a single internal caller (the `choose` at line 564) and no inline re-derivation elsewhere, this is a thin convenience wrapper, not a mathlib contribution.

**WHY not (refactor-actionable):**
Mathlib has the building blocks (`Complex.norm_mul_exp_arg_mul_I` + `Complex.arg_le_pi` + `Complex.neg_pi_lt_arg`); the lemma is a ≤3-call composition whose only extra content is the bespoke `[0,1]` phase coordinate. There is no general/canonical statement here that mathlib lacks — the `(2πθ − π)` rescaling is intrinsic to the cube parametrisation and does not generalise. So this does not belong in mathlib in any form; it should stay a project-local helper (or be inlined).

Mathlib building blocks:
- `Complex.norm_mul_exp_arg_mul_I` — `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:56` — `‖x‖ * exp (arg x * I) = x`
- `Complex.arg_le_pi` — `Arg.lean:155` — `arg x ≤ π`
- `Complex.neg_pi_lt_arg` — `Arg.lean:158` — `-π < arg x`
  (both packaged as `Complex.arg_mem_Ioc` — `Arg.lean:136` — `arg z ∈ Ioc (-π) π`)

Composition sketch (≤3 mathlib calls + glue):
```lean
example (z : ℂ) :
    ∃ θ : ℝ, θ ∈ Set.Icc (0:ℝ) 1 ∧
      (‖z‖ : ℂ) * Complex.exp ((2 * Real.pi * θ - Real.pi) * Complex.I) = z :=
  ⟨(z.arg + Real.pi) / (2 * Real.pi),
   ⟨div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) (by positivity),
    (div_le_one (by positivity)).2 (by linarith [Complex.arg_le_pi z])⟩,
   by rw [show ((2:ℂ)*Real.pi*(((z.arg+Real.pi)/(2*Real.pi):ℝ):ℂ) - Real.pi)
            = ((z.arg : ℝ) : ℂ) by push_cast; field_simp; ring]
      simpa using Complex.norm_mul_exp_arg_mul_I z⟩
```

Call sites in our project (from Phase 6.0): K = 1 (`NormLeOneLipschitz.lean:564`).

**Refactor plan (project-local — note the AINTLIB caveat below):**
The single consumer is the `choose θ hθmem hθeq using fun w ↦ exists_phase_mem_Icc_mul_exp (x.2 w)` at line 564. Two acceptable resolutions, neither of which is a mathlib PR:
1. Keep the lemma as a project-local helper (it has a meaningful name and a clear docstring, and the `[0,1]` convention recurs across this file's cube machinery — `liftToMixed`, `mixedCubeEquiv`). This is the pragmatic choice; the lemma is *correct and useful locally*, just not mathlib-shaped.
2. If inlining is preferred, replace line 564's `exists_phase_mem_Icc_mul_exp (x.2 w)` with the 3-call composition above (it returns the same `∃ θ ∈ Icc 0 1, …` triple, so `choose` still binds `θ`, `hθmem`, `hθeq` unchanged). Verify the `push_cast; field_simp; ring` step discharges the exponent rewrite under the project's mathlib pin.

**Next action:** do **not** open a mathlib PR. This is `ForMathlib/`-earmarked but the assessment says the earmark is a false positive for *this* declaration — the content is already in mathlib (`norm_mul_exp_arg_mul_I` + `arg_mem_Ioc`); only the bespoke `[0,1]` phase coordinate is local. Either retain it as a private/project helper or inline the composition at the one call site. (Note: per AINTLIB CLAUDE.md, statement-changing refactors are `lane:generalise`/producer work, not casual edits — if inlined, that is a cleanup-lane change that must keep `main` green with `#print axioms` unchanged.)

---

## Next step

Do not submit to mathlib. The mathematical content is `Complex.norm_mul_exp_arg_mul_I` + `Complex.arg_mem_Ioc`, already in mathlib; the lemma adds only a project-local `[0,1]` cube-coordinate reparametrisation with a single internal caller. Keep it as a Chebotarev-local helper, or inline the ≤3-call composition (sketch above) at `NormLeOneLipschitz.lean:564`.
