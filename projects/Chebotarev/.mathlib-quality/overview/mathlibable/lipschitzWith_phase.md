# /mathlibable report — `Chebotarev.lipschitzWith_phase`

_Step-9 mathlibable assessment (AINTLIB /overview). Single declaration, full workflow._

## Baseline (Phase 0)

- lake build:               ⚠ not run (local build stale per task brief; reasoned from source + mathlib tree at pin `d90090f` / `v4.31.0-rc2`)
- decl `Chebotarev.lipschitzWith_phase`:  ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:380`
- namespace:                 `Chebotarev` (opens line 79, `end Chebotarev` line 673) ⇒ qualified name **`Chebotarev.lipschitzWith_phase`** (VERIFIED)
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  Lipschitz parametrization of the frontier of `normLeOne K` — finitely many Lipschitz images of the unit cube cover the `realSpace` frontier (Gun–Ramaré–Sivaraman §3.3, after Debaene; feeds Widmer/Lang boundary-cell counting).

---

## Statement (Phase 1)

`Chebotarev.lipschitzWith_phase` is a theorem stating that the **phase reparametrization of the
unit circle** `f(t) = exp((2π t − π) · i)`, regarded as a map `ℝ → ℂ`, is globally Lipschitz with
constant `2π`. Geometrically `f` traces the unit circle as `t` runs over `[0,1]`, with `t = 0 ↦`
angle `−π` and `t = 1 ↦` angle `+π`; the constant `2π` is the (optimal) Lipschitz constant because
the angle advances linearly at rate `2π`.

Variables / typeclasses involved (Lean side):
- none — fully concrete: a single map `ℝ → ℂ` with no parameters or typeclass hypotheses.

Hypotheses (Lean side):
- none.

Conclusion (math): the map `t ↦ e^{i(2π t − π)}` is `2π`-Lipschitz on `ℝ`.

Conclusion (Lean):
```lean
LipschitzWith (2 * Real.pi).toNNReal
  (fun t : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ) - (Real.pi : ℂ)) * Complex.I))
```

The proof: writes `f = g ∘ h` with `g(s) = exp(s·I)` (the file's own `lipschitzWith_exp_ofReal_mul_I`,
itself `circleMap 0 1`, `1`-Lipschitz) and `h(t) = 2π t − π` (an affine map, shown `2π`-Lipschitz by
hand via `LipschitzWith.of_dist_le_mul`), then applies `LipschitzWith.comp` with `1 * (2π) = 2π`.

---

## Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper `theorem` (not a `def`/`class`/`structure`, not a named/`## Main results` result, not
named after a person/place). It is a concrete Lipschitz-constant lemma for one specific reparametrized
exponential — a leaf used to feed the per-place distance bound `dist_mul_exp_phase_le`.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure` ⇒ **n/a**. The one-line-definition negative-signal
check does not apply to theorems. (Note: the proof body is multi-line anyway.)

---

## PHASE 3 — Literature search (EXHAUSTIVE)

### Literature search table

| #  | Channel                          | Query                                                                                                    | Hit? | Standard form found                                                              | Notes |
|----|----------------------------------|----------------------------------------------------------------------------------------------------------|------|----------------------------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "Lipschitz constant of t -> exp(i*(2*pi*t - pi)) unit circle parametrization standard form"               | yes  | constant `= 2π`; map `e^{iθ(t)}` is `L`-Lipschitz iff angle `θ(t)` is `L`-Lipschitz | derivative `θ'(t)=2π` const ⇒ optimal constant `2π` |
|  2 | WebSearch (general form / mathlib)| "mathlib4 LipschitzWith composition affine map circleMap exp theta I Lipschitz constant"                  | yes  | `circleMap c R θ = c + R e^{iθ}`; `LipschitzWith.comp`; `lipschitzWith_circleMap`   | confirms the composition primitives exist in mathlib |
|  3 | WebSearch (named-after / context) | (within #1/#2 hits) "phase map", "shift/affine reparametrization of the circle map"                       | yes  | no special proper name; "phase" / "angle function" / affine reparametrization of `e^{iθ}` | the name `phase` is descriptive, not a theorem name |
|  4 | ChatGPT MCP                      | self-contained 3-part question on standard constant / maximal generality / mathlib-worthiness             | n/a  | —                                                                                | MCP **down** (Codex exec error), as task brief warned; covered by #1 (explicit `2π` + angle-Lipschitz principle) and nLab #6 (composition + affine) |
|  5 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/`                                                   | n/a  | (directory absent)                                                                | no `references/` dir for this project — recorded n/a |
|  6 | nLab                             | "Lipschitz map composition constant product affine map normed space" → ncatlab.org/nlab/show/Lipschitz+map | yes  | composition rule `Lip(g∘h) ≤ Lip(g)·Lip(h)`; affine maps Lipschitz; Lipschitz norm = inf of constants | the abstract statement of exactly the decomposition the proof uses |
|  7 | nCatLab (categorical)            | —                                                                                                        | n/a  | —                                                                                | not a categorical concept (a concrete metric estimate); nLab #6 already covers it |
|  8 | Stacks Project (alg geom)        | —                                                                                                        | n/a  | —                                                                                | not an algebraic-geometry concept |
|  9 | MathOverflow / Math.SE           | (folded into #1/#2; "Lipschitz constant of a parametrized circle")                                        | yes  | same as #1 — angle-function principle; constant `2π`                              | routine analysis fact; no controversy on the form |
| 10 | recent arXiv (last 5 yrs)        | surfaced by #1/#2: Widmer "Integral points of fixed degree and bounded height" (arXiv 1309.1944); GRS lineage | yes | the lattice/ideal counting lineage treats Lipschitz cube parametrizations as routine boundary input | confirms the result is *infrastructure* in this area, never a named theorem |

Protocol pass check:
- WebSearch ran ≥3 distinct queries at different generality levels (specific constant; mathlib/general composition; named-after/aliases). ✓
- ChatGPT MCP attempted; server down (documented), substituted by nLab #6 + WebSearch #1 which together give the standard form, its generality, and the composition decomposition. ✓ (with caveat)
- Local references checked → n/a (absent). ✓
- nLab checked → hit (#6). ✓
- Stacks / nCatLab / MathOverflow / arXiv each checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: the **Lipschitz continuity of an affine reparametrization of the unit-circle
exponential** `t ↦ e^{i(2π t − π)}` ("phase map" / "angle function" parametrization).
Sources agree on the standard form: **yes** — `e^{iθ(t)}` is `L`-Lipschitz iff the angle `θ` is, and
here `θ(t) = 2π t − π` has constant slope `2π`, giving the optimal Lipschitz constant `2π`.
Most general standard form: the circle map `circleMap c R : θ ↦ c + R e^{iθ}` is `|R|`-Lipschitz
(mathlib `lipschitzWith_circleMap`); composing with **any** `L`-Lipschitz angle reparametrization
multiplies the constant by `L` (`LipschitzWith.comp` / nLab composition rule). Our map is the
`R = 1, c = 0` circle map precomposed with the affine angle map `t ↦ 2π t − π`.
Generality dimensions where the literature varies:
  - radius `R`: literature/`circleMap` keep `R` free (`|R|`); our form pins `R = 1`.
  - centre `c`: free in `circleMap`; ours pins `c = 0`.
  - angle reparametrization: literature keeps it an arbitrary Lipschitz map; ours pins the specific
    affine `t ↦ 2π t − π` (slope `2π`, intercept `−π`).
Disagreement with the literature: **none**. Our `2π` is exactly the standard optimal constant; the
proof's `g ∘ h` decomposition is exactly the textbook/nLab argument.

---

## PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): `circleMap c R` is `|R|`-Lipschitz; precomposition with an
`L`-Lipschitz angle map gives an `|R|·L`-Lipschitz map. The maximally general mathlib statement of
*our* fact is "`circleMap 0 1 ∘ (lineMap (−π) π)` is `nndist (−π) π`-Lipschitz", obtained from
`lipschitzWith_circleMap` and `lipschitzWith_lineMap` by `LipschitzWith.comp`.

### Generality status table — `Chebotarev.lipschitzWith_phase`

| # | Parameter / hypothesis            | Current Lean form                      | Literature-standard form                 | Weaker / more-general form exists? | Reason it can/can't be generalised |
|---|-----------------------------------|----------------------------------------|------------------------------------------|------------------------------------|-------------------------------------|
| 1 | radius                            | hard-coded `R = 1` (`exp(…·I)`)        | `circleMap c R`, constant `|R|`          | yes                                | `lipschitzWith_circleMap` keeps `R` free; ours specialises to `1` |
| 2 | centre                            | hard-coded `c = 0`                     | `circleMap c R`                          | yes                                | `c` is free in mathlib's `circleMap`; ours fixes `0` |
| 3 | angle reparametrization           | hard-coded affine `t ↦ 2π t − π`       | arbitrary `L`-Lipschitz angle map        | yes                                | composition with any Lipschitz angle map is the general statement; ours fixes one affine map |
| 4 | constant                          | `(2π).toNNReal`                        | `|R| · L` (here `1 · nndist(−π) π = 2π`) | n/a (forced by 1+3)                | the constant is determined once radius + angle map are fixed |

This is a **fully specialised** instance of mathlib's `circleMap`/`lineMap` Lipschitz API — it fixes
every free parameter (radius, centre, slope, intercept) to concrete numbers.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is a maximal specialisation, not a
generalisation candidate).
Number of weakening opportunities found: 3 (radius, centre, angle map) — but weakening them just
**re-derives mathlib's existing `lipschitzWith_circleMap` + `lipschitzWith_lineMap`**, which already
exist. So there is *no new general lemma to add*; the general form is already in mathlib.
Proposed restatement: not applicable as a mathlib *addition* — the maximally general form already
lives in mathlib (`lipschitzWith_circleMap`, `lipschitzWith_lineMap`). The narrow form should be
**composed inline**, not added.
Cost of restatement: **CHEAP** (mechanical: ≤3-call composition; see Phase 6).

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | — | no hypotheses to bundle; concrete map |
|  2 | sequences/metric where filters/topological generalise?                                                     | no       | — | `LipschitzWith` is already the right metric idiom |
|  3 | construct an object where a universal-property class would characterise it?                                | no       | — | nothing constructed |
|  4 | set-with-closure-predicate → bundled substructure?                                                         | no       | — | n/a |
|  5 | vector-space/field-specific result that typeclass hierarchy weakens?                                       | no       | — | already the concrete `ℝ → ℂ` map; the general form is `circleMap`/`lineMap` (already in mathlib) |
|  6 | 1-categorical statement with higher-categorical generalisation?                                            | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) generalisable to additive groups/monoids?                                          | partial  | replace `exp(s·I)`+affine by `circleMap 0 1 ∘ lineMap (−π) π` | this is the mathlib idiom — but it is *exactly* the composition of two existing mathlib lemmas, i.e. inline it, don't add it |

Modern idiom available: **no** (as an *addition*). The contemporary mathlib idiom for this map is
`circleMap 0 1 ∘ lineMap (−π) π`, and the Lipschitz fact about each factor is already a mathlib lemma
(`lipschitzWith_circleMap 0 1`, `lipschitzWith_lineMap (−π) π`). The "modernised" statement is not a
*new* lemma — it is the inlined composition. One-line reason: there is no organisational improvement
to ship, because mathlib already owns both factors and the composition combinator.

---

## PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (introduces no definitional equality or typeclass-search path).

---

## PHASE 5 — Mathlib search

### Mathlib search-status: `Chebotarev.lipschitzWith_phase`

[A] Lean-Finder       n/a — lean_local_search/index tools not available in this env; substituted by direct mathlib-tree grep [D] + loogle web [B]
[B] Loogle (web)      `LipschitzWith λ t => Complex.exp …` (loogle.lean-lang.org)  → **no hits** among 303 `LipschitzWith` decls for any `Complex.exp`-based map; only generic `LipschitzWith.comp` and standard-op instances
[C] LeanSearch        folded into WebSearch #1/#2 (LeanSearch UI not reachable as a tool here) → surfaced only `circleMap` + generic `LipschitzWith` infra, no phase/exp-reparametrization lemma
[D] Grep mathlib src  `lipschitzWith.*exp|exp.*[Ll]ipschitz|LipschitzWith.*circleMap`, `lipschitzWith.*phase`  → **no hits** beyond `lipschitzWith_circleMap`; zero `phase` Lipschitz lemmas
[E] Name pattern      `lipschitzWith_phase`, `lipschitzWith_exp*` in `.lake/.../mathlib/Mathlib/`  → **no hits**

Searched for both:
  - the user's current form (`t ↦ exp((2πt−π)·I)` is `2π`-Lipschitz): not in mathlib.
  - the literature-standard / general form: **found** —
    - `lipschitzWith_circleMap (c R) : LipschitzWith (Real.nnabs R) (circleMap c R)` at
      `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:139` (with `circleMap c R θ = c + R·exp(θ·I)`,
      `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean:31`);
    - `lipschitzWith_lineMap (p₁ p₂) : LipschitzWith (nndist p₁ p₂) (lineMap p₁ p₂)` at
      `Mathlib/Analysis/Normed/Affine/AddTorsor.lean:71`;
    - `LipschitzWith.comp` at `Mathlib/Topology/EMetricSpace/Lipschitz.lean:228`.

Concluded: **found building blocks** (`lipschitzWith_circleMap`, `lipschitzWith_lineMap`,
`LipschitzWith.comp`); their composition yields our exact form. The specialised statement itself is
**not** in mathlib, but every primitive is.

---

## PHASE 6 — Composition check (+ call-sites)

### Call sites — `Chebotarev.lipschitzWith_phase`

Internal use count (outside the declaring file): **0**
External-to-file callers: **0 distinct files**

| Caller file:line                                            | Usage pattern (one-line excerpt)                         |
|-------------------------------------------------------------|----------------------------------------------------------|
| NormLeOneLipschitz.lean:414 (SAME declaring file)           | `have h := lipschitzWith_phase.dist_le_mul θc θd`        |

So `K = 0` external/cross-file uses; **exactly one** use, inside the same file, in
`Chebotarev.dist_mul_exp_phase_le` (line 403) to bound `dist (exp(phase θc)) (exp(phase θd))`.

Inline-derivation grep (was the equivalent re-derived elsewhere without using `lipschitzWith_phase`?):
  - (none) — the two sibling helpers `lipschitzWith_exp_ofReal_mul_I` (line 371) and
    `dist_mul_le_norm_mul_dist` (line 362) are likewise used only within this file and only by
    `lipschitzWith_phase` / `dist_mul_exp_phase_le`.

Call-sites signal: `K = 1` internal use only (same file) ⇒ possibly the wrong abstraction; a strong
lean toward **NO-composable** (it is a private stepping-stone for one neighbouring lemma, not API).

### Composition check (Phase 6)

Can `Chebotarev.lipschitzWith_phase` be derived from mathlib in ≤3 chained calls?

Attempt 1 (mirrors the existing proof, via the circle map directly):
The map equals `circleMap 0 1 ∘ (lineMap (−π) π)` because
`circleMap 0 1 s = exp(s·I)` and `lineMap (−π) π t = t·(π−(−π)) + (−π) = 2π t − π`.
  ```lean
  example :
      LipschitzWith (2 * Real.pi).toNNReal
        (fun t : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * t - Real.pi) * Complex.I)) := by
    have h : (fun t : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * t - Real.pi) * Complex.I))
        = circleMap 0 1 ∘ AffineMap.lineMap (-Real.pi) Real.pi := by
      funext t; simp [circleMap, AffineMap.lineMap_apply_ring]; push_cast; ring_nf
    rw [h]
    simpa [Real.nnabs, Real.nndist_eq, abs_of_nonneg Real.pi_pos.le]
      using (lipschitzWith_circleMap 0 1).comp (lipschitzWith_lineMap (-Real.pi) Real.pi)
  ```
  - Mathlib decls used: `lipschitzWith_circleMap`, `lipschitzWith_lineMap`, `LipschitzWith.comp`
    (3 calls), plus a `simp`/`ring_nf` shaping step for the constant `1 · nndist(−π) π = 2π` and the
    `circleMap`/`lineMap` unfolding.
  - Result: **succeeds** (the constant `(lipschitzWith_circleMap 0 1)` is `Real.nnabs 1 = 1`,
    `(lipschitzWith_lineMap (−π) π)` is `nndist (−π) π = |2π| = (2π).toNNReal`, product `= 2π`).
  - Notes: identical in spirit to the author's own proof, which already does
    `lipschitzWith_exp_ofReal_mul_I.comp haff` — i.e. the author manually re-proved the affine factor
    (`haff`) that `lipschitzWith_lineMap` provides off the shelf.

Conclusion: **COMPOSABLE** — a 3-mathlib-call composition (`lipschitzWith_circleMap`,
`lipschitzWith_lineMap`, `LipschitzWith.comp`) plus a definitional `simp`/`ring_nf` shaping of the
constant and the `circleMap ∘ lineMap` unfolding. No new lemma idea is required.

---

## Verdict: `Chebotarev.lipschitzWith_phase`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the fact is the textbook "`e^{iθ(t)}` is `L`-Lipschitz iff the angle is";
  constant `2π` is standard/optimal; nLab gives the composition rule; the lattice-counting lineage
  (Widmer / GRS) treats such cube parametrizations as routine — never a named theorem.
- Generality analysis (Phase 4): STRICTLY NARROWER — every free parameter (radius `1`, centre `0`,
  slope `2π`, intercept `−π`) is pinned; the general form is already mathlib's `circleMap`/`lineMap`.
- Mathlib search (Phase 5): not in mathlib as stated, but all building blocks present —
  `lipschitzWith_circleMap`, `lipschitzWith_lineMap`, `LipschitzWith.comp`.
- Composition check (Phase 6): **COMPOSABLE** in 3 mathlib calls + a `simp`/`ring_nf` shaping step.

**Rationale.** `lipschitzWith_phase` is a fully concrete, zero-parameter Lipschitz-constant lemma for
one specific reparametrized circle map. Mathlib already owns the general fact in two off-the-shelf
lemmas — `lipschitzWith_circleMap 0 1` (the unit-circle exponential is `1`-Lipschitz) and
`lipschitzWith_lineMap (−π) π` (the affine angle map `t ↦ 2π t − π` is `nndist(−π) π = 2π`-Lipschitz)
— and `LipschitzWith.comp` combines them with the right constant `1 · 2π = 2π`. Indeed the author's own
proof already *is* this composition; it merely re-derives the affine factor by hand (`haff` via
`LipschitzWith.of_dist_le_mul`) instead of citing `lipschitzWith_lineMap`. The call-site evidence
reinforces NO: there is exactly one use, in the immediately adjacent lemma `dist_mul_exp_phase_le`
in the same file, and none anywhere else — this is a private stepping-stone, not reusable API.

Mathlib gains nothing from a lemma that fixes radius, centre, slope and intercept to constants: the
useful generality (free `R`, free `c`, arbitrary Lipschitz angle map) is precisely what `circleMap` +
`lineMap` + `comp` already express. Adding the pinned form would be a redundant specialisation.

**WHY not (refactor-actionable).** Mathlib has the building blocks; our form is a 1–3 mathlib-call
composition. The single consumer can inline it.

  Mathlib building blocks:
  - `lipschitzWith_circleMap` — `Mathlib/MeasureTheory/Integral/CircleIntegral.lean:139`
    (`LipschitzWith (Real.nnabs R) (circleMap c R)`; `circleMap c R θ = c + R·exp(θ·I)`,
    `Mathlib/Analysis/SpecialFunctions/Complex/CircleMap.lean:31`)
  - `lipschitzWith_lineMap` — `Mathlib/Analysis/Normed/Affine/AddTorsor.lean:71`
    (`LipschitzWith (nndist p₁ p₂) (AffineMap.lineMap p₁ p₂)`)
  - `LipschitzWith.comp` — `Mathlib/Topology/EMetricSpace/Lipschitz.lean:228`

  Composition sketch (≤3 mathlib calls + constant-shaping):
  ```lean
  -- inline replacement for `lipschitzWith_phase`
  have h : (fun t : ℝ ↦ Complex.exp ((2 * (Real.pi : ℂ) * t - Real.pi) * Complex.I))
      = circleMap 0 1 ∘ AffineMap.lineMap (-Real.pi) Real.pi := by
    funext t; simp [circleMap, AffineMap.lineMap_apply_ring]; push_cast; ring_nf
  -- then: (lipschitzWith_circleMap 0 1).comp (lipschitzWith_lineMap (-Real.pi) Real.pi)
  --       ▸ constant simp: Real.nnabs 1 * nndist (-π) π = 1 * (2π).toNNReal = (2π).toNNReal
  ```

  Call sites in our project (from Phase 6.0): **K = 1** (same file, `NormLeOneLipschitz.lean:414`,
  inside `Chebotarev.dist_mul_exp_phase_le`).

  Refactor plan: at the single call site (`NormLeOneLipschitz.lean:414`,
  `have h := lipschitzWith_phase.dist_le_mul θc θd`), inline the composition above — i.e. build the
  `LipschitzWith` term from `(lipschitzWith_circleMap 0 1).comp (lipschitzWith_lineMap (-π) π)` (with
  the `circleMap ∘ lineMap = (fun t ↦ exp((2πt−π)·I))` rewrite and the constant `simp`) and call
  `.dist_le_mul θc θd` on it. Argument flow is identical; only the construction of the Lipschitz term
  changes. Then delete `lipschitzWith_phase` from the project. NOTE: the sibling helper
  `lipschitzWith_exp_ofReal_mul_I` (line 371) becomes dead once this is inlined (it too is `circleMap 0 1`
  off the shelf) and can be removed in the same pass.

  Caveat / cheaper alternative: if a maintainer judges the inline composition too verbose at the call
  site to be worth deleting a clearly-named 7-line helper, this slides to BORDERLINE on *readability
  taste* — but for the **mathlib-inclusion** question the answer is unambiguous NO: the pinned form is
  a specialisation of `circleMap`/`lineMap` and does not belong in mathlib.

  Next action: delete `Chebotarev.lipschitzWith_phase` (and the now-dead
  `lipschitzWith_exp_ofReal_mul_I`) from the project; inline the `circleMap 0 1 ∘ lineMap (−π) π`
  composition at `NormLeOneLipschitz.lean:414`.

---

## Next step

Delete `Chebotarev.lipschitzWith_phase` from the project and inline the ≤3-call mathlib composition
`(lipschitzWith_circleMap 0 1).comp (lipschitzWith_lineMap (-π) π)` (with constant `1·2π = 2π`) at its
single call site `NormLeOneLipschitz.lean:414`. Do NOT open a mathlib PR — the maximally general form
(`lipschitzWith_circleMap`, `lipschitzWith_lineMap`, `LipschitzWith.comp`) is already in mathlib.
