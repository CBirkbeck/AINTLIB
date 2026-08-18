# Mathlibable assessment: `WeierstrassCurve.Universal.polyEval_cusp_ψ`

**Verdict: NO-composable-from-mathlib** (precisely: *does not belong in mathlib — it is a
project-local aggregator of this project's own forked/scaffolding API, the "degenerate-fibre"
witness for universal `ψₙ` non-vanishing; keep it local*).

- **Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.polyEval_cusp_ψ`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:114`
- **Date:** 2026-06-22
- **Assessor run:** `/overview` Step-9 mathlibable, NagellLutz project.

> Qualified name VERIFIED. At line 114 the namespace stack is `namespace WeierstrassCurve`
> (opened ZSMul.lean:76) → `namespace Universal` (opened ZSMul.lean:86), with only
> `noncomputable section` + `variable`/`open` in between (sections do not contribute to the
> name). So the fully-qualified name is **`WeierstrassCurve.Universal.polyEval_cusp_ψ`** —
> exactly the parsed name in the prompt.

---

## 1. Exact statement and proof (from source)

```lean
lemma polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]
```

with `{n : ℤ}` a section variable (ZSMul.lean:97).

**What it says.** Evaluate the **universal** `n`-th division polynomial `curve.ψ n` (a polynomial
in `ℤ[A₁,…,A₆,X,Y]`) by the evaluation homomorphism `polyEval cusp 1 1`, which specialises the
universal coefficients to those of the **cusp** curve `Y²=X³` (`cusp = ⟨0,0,0,0,0⟩`) and then sets
`(X,Y) = (1,1)`. The result is the integer `n`. In words: **the division polynomial `ψₙ`,
evaluated on the cuspidal cubic at the point `(1,1)`, equals `n`** — the classical *degenerate /
trivial* elliptic divisibility sequence `Wₙ = n` (Ward's singular case).

**How the proof works.** `curve.ψ n = normEDS curve.ψ₂ (C curve.Ψ₃) (C curve.preΨ₄) n`
(`ψ` unfolds; `map_normEDS` pushes `polyEval` through the EDS recursion). The three companion
value lemmas give the seed terms *on the cusp at `(1,1)`*:
`cusp_ψ₂ : cusp.ψ₂ = 2*Y`, `cusp_Ψ₃ : cusp.Ψ₃ = 3*X⁴`, `cusp_preΨ₄ : cusp.preΨ₄ = 2*X⁶`, which at
`(X,Y)=(1,1)` evaluate to `(2,3,2)`. Then `normEDS_two_three_two : normEDS (2:ℤ) 3 2 = id`
collapses the whole sequence to the identity, giving `ψₙ(1,1) = n`.

## 2. Definitions involved (all project-local; none in mathlib)

| object | what it is | mathlib? |
|---|---|---|
| `cusp` | `def cusp : Affine ℤ := ⟨0,0,0,0,0⟩` — the cuspidal cubic `Y²=X³` (`Universal.lean:180`) | **NO** (mathlib "cusp" = modular forms only) |
| `polyEval W x y` | `eval₂RingHom (eval₂RingHom W.specialize x) y : Poly →+* R` (`Universal.lean:203`) — evaluate a universal `ℤ[A₁,…,A₆,X,Y]`-polynomial at `(x,y)` after specialising coefficients to `W` | **NO** (no `Universal`/`specialize`/`polyEval` in mathlib) |
| `curve.ψ n` | the **universal** division polynomial over `Poly = ℤ[A₁,…,A₆,X,Y]` (`curve := Affine (MvPolynomial Coeff ℤ)`, `Universal.lean:84`); `ψ := normEDS …` (`DivisionPolynomial.lean:324`) | **NO** universal form; the *per-curve* `WeierstrassCurve.ψ` IS in mathlib (`DivisionPolynomial/Basic.lean:401`) |
| `cusp_ψ₂ / cusp_Ψ₃ / cusp_preΨ₄` | the three seed-value lemmas on the cusp (`ZSMul.lean:110–112`) | **NO** — sibling reports each ruled **NO-composable-from-mathlib** |
| `normEDS_two_three_two` | `normEDS (2:ℤ) 3 2 = id` (`EllipticDivisibilitySequence.lean:1234`) | **NO** — ruled **NO-mathlib-has-it** (pending upstream PR #13782) |

So the statement is phrased entirely in objects that **do not exist in mathlib**.

## 3. Role in the project

`polyEval_cusp_ψ` is the **keystone** of the project's bespoke *degenerate-fibre* technique for
proving the **universal non-vanishing** of the division polynomial. It is consumed by:

- `polyEval_cusp_φ` / `polyEval_cusp_ψc` / `polyEval_cusp_ω` (ZSMul.lean:118/122/126) — the sister
  cusp-evaluation values `φ→1, ψc→2, ω→1`;
- **`ψᵤ_ne_zero`** (ZSMul.lean:142): `ψᵤ n ≠ 0` for `n ≠ 0`. Proof: if `ψᵤ n = 0` in the universal
  field, push it through `ringEval cusp_equation_one_one` to land in `ℤ`, where
  `polyEval_cusp_ψ` rewrites the image to `n`; so `n = 0`. This is the *whole point* of the cusp
  machinery — it gives universal non-vanishing "for free" by exhibiting a single specialisation
  (the cusp at `(1,1)`) on which `ψₙ = n ≠ 0`.

`ψᵤ_ne_zero` in turn underpins the entire `Universal.Jacobian` / `Universal.Affine`
`zsmul = division-polynomial-evaluation` formula (`zsmul_eq_smulEval`), the main result of the
file (ZSMul.lean docstring, lines 49–53). So this lemma is load-bearing scaffolding, *internal to
the project's proof architecture*.

## 4. Literature search (Phase 3)

- The fact that the EDS attached to a point degenerates to the **trivial sequence `Wₙ = n`** on a
  **singular (cuspidal) cubic** is classical — Ward, *Memoir on Elliptic Divisibility Sequences*:
  "up to equivalence a singular sequence is either the trivial sequence `Wₙ = n` or a Lucas
  sequence." The smooth locus of `Y²=X³` is `≅ 𝔾ₐ` (the additive group), on which the
  multiplication-by-`n` "division polynomial" reads off `n`. See the EDS literature
  (arXiv:2102.07573, arXiv:1909.12654, arXiv:1801.02664) and Wikipedia "Elliptic divisibility
  sequence."
- A targeted web search ("EDS on cuspidal cubic `Y²=X³`, `ψₙ = n`, singular case") confirms the
  standard sources treat the singular curve only as a **boundary example**, never a named numbered
  theorem; the surveyed papers state the division-polynomial / EDS theory for **non-singular**
  Weierstrass curves and do not record the cusp specialisation as a quotable result.
- The specific Lean phrasing — "`polyEval cusp 1 1 (curve.ψ n) = n`", i.e. an evaluation of the
  *universal* division polynomial via the *universal-ring specialisation homomorphism* at the cusp
  — is a formalisation device, not a literature statement.

**Phase-3 conclusion:** the underlying *mathematics* (degenerate EDS `= n` on the cusp) is
classical-but-unnamed; the *statement as written* is project-specific plumbing.

## 5. Mathlib search — five methods (Phase 5)

Pinned mathlib (this repo's `.lake/packages/mathlib`). **Present/absent dominated by authoritative
source reads** (the `lean_loogle`/`lean_leansearch` index MCP was not reachable in this
environment; the direct source reads below settle a present/absent question definitively).

1. **Direct source read — universal/cusp machinery.** `grep -rln "namespace Universal|def polyEval|
   polyEval_cusp|cusp_ψ"` over `Mathlib/AlgebraicGeometry/EllipticCurve/` and
   `Mathlib/NumberTheory/` → **zero hits** (the lone match was `NumberTheory/Chebyshev.lean`, a
   false positive on `= n`). Mathlib has **no** `Universal` namespace for Weierstrass curves, **no**
   `specialize`/`polyEval`, **no** universal division polynomial, and **no** cusp curve.
2. **Division-polynomial dir.** `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean` define the
   **per-curve** `WeierstrassCurve.ψ` (`Basic.lean:401`, `:= normEDS …`) and `ψ₂` (`:113`). There is
   **no** evaluation-on-a-specific-curve lemma, and **no** singular/cusp instance.
3. **Cusp / singular cubic.** `grep` for `cusp`, `Y²=X³`, `⟨0,0,0,0,0⟩`, `cuspidal`, `singular
   cubic` over `Mathlib/` → only the **modular-forms** `cuspFunction`/`Cusps` family. Mathlib's
   elliptic-curve API deliberately excludes `Δ=0`, so there is no object for this lemma to attach to
   (consistent with the sibling `cusp.md` and `cusp_ψ₂.md` reports).
4. **EDS `= id` / `= n` shape.** `grep` for `two_three_two`, `normEDS .* = id`, `= n` EDS evaluations
   over the EDS file → none; `normEDS_two_three_two` itself is fork-only (NO-mathlib-has-it). No
   `normEDS … = id` equation exists in current mathlib.
5. **Consumer/duplication check.** The only sibling copy of this technique repo-wide is the
   HasseWeil fork of the same EDS/division-polynomial author lineage; there is no independent
   mathlib analogue. No mathlib lemma states "division polynomial evaluated on a (cusp) curve = n."

**Phase-5 conclusion:** neither this lemma nor any of its constituent objects (`Universal`,
`polyEval`, universal `curve.ψ`, `cusp`, `normEDS … = id`) is in mathlib. The only mathlib object in
the neighbourhood is the *per-curve* `WeierstrassCurve.ψ`, which the project **forks** into a
universal version this lemma evaluates.

## 6. Generality analysis (Phase 4)

**Maximally specialised** — and not in the direction of a mathlib lemma. Three independent pins:
(i) the curve is the fixed singular cubic `cusp` (not a variable curve); (ii) the point is the fixed
`(1,1)`; (iii) the base is `ℤ`. There is no "weaker-hypothesis" or "more-general" restatement to
upstream: the honest "general parent" of this statement is the *universal division polynomial*
machinery (`polyEval` + `curve.ψ` + `ringEval`), which is **itself project-specific scaffolding not
in mathlib**, not a more-general mathlib lemma waiting to be stated. (Contrast `cusp` the *def*,
whose general form `cusp (R) [CommRing R]` IS a sensible mathlib addition — that generality belongs
to the parent `def cusp`, not to this evaluation lemma, and travels with it.)

## 7. Composition check — can ≤3 mathlib calls give it? (Phase 6)

**No, not from current mathlib.** This lemma is an **aggregator** of project-local helpers:

```text
polyEval_cusp_ψ
  ├── ψ (unfold)                       ─ project def (forked universal ψ)
  ├── map_normEDS                      ─ EDS homomorphism lemma (fork/PR #13782 surface)
  ├── evalEval_ψ₂ / Ψ₃ / preΨ₄         ─ project lemmas (polyEval ↔ evalEval bridge)
  ├── cusp_ψ₂ / cusp_Ψ₃ / cusp_preΨ₄   ─ project lemmas (each NO-composable-from-mathlib)
  └── normEDS_two_three_two            ─ project lemma (NO-mathlib-has-it; linchpin
                                          IsEllSequence.ext not in current mathlib)
```

Every non-trivial ingredient is project-local or fork-only:
- the *subject* `polyEval cusp 1 1 (curve.ψ n)` is built from `polyEval` (no mathlib analogue) and
  the **universal** `curve.ψ` (no mathlib analogue);
- `normEDS_two_three_two` rests on `IsEllSequence.ext`, which is **not** in current mathlib (it is
  in flight via mathlib PR #13782); without it, collapsing `normEDS 2 3 2` to `id` is a
  `normEDSRec` strong induction, far beyond a 3-call composition;
- the three `cusp_*` seed lemmas were each independently classified NO-composable-from-mathlib.

So there is **no** ≤3-call route from *current* mathlib primitives — those primitives (universal
ring, `polyEval`, universal `ψ`, cusp curve, `normEDS … = id`) **do not exist upstream**. Hence
"NO-composable" here means decisively *does not belong in mathlib*: it is a local theorem of the
project's own API, exactly as its three building-block siblings are.

---

## Verdict: `WeierstrassCurve.Universal.polyEval_cusp_ψ`

**Category: NO-composable-from-mathlib**

**Evidence:**
- **Literature (3):** the degenerate EDS `Wₙ = n` on the cuspidal cubic `Y²=X³` is classical (Ward;
  smooth locus `≅ 𝔾ₐ`) but recorded only as a *boundary example*, never a named theorem; the
  *universal-ring evaluation* phrasing is a formalisation device.
- **Mathlib (5):** **absent** — no `Universal` namespace, no `polyEval`/`specialize`, no universal
  division polynomial, no `cusp` curve, no `normEDS … = id`. Only the *per-curve*
  `WeierstrassCurve.ψ` (`DivisionPolynomial/Basic.lean:401`) exists, which the project **forks**.
- **Generality (4):** maximally specialised (fixed cusp, fixed `(1,1)`, base `ℤ`); its "general
  parent" is the project's own universal-division-polynomial scaffolding, not a missing mathlib
  lemma.
- **Composition (6):** **not** a ≤3-call composition from current mathlib — it aggregates
  `polyEval` + universal `curve.ψ` + the three `cusp_*` value lemmas (each NO-composable) +
  `normEDS_two_three_two` (NO-mathlib-has-it; linchpin `IsEllSequence.ext` not yet upstream). None
  of these primitives is in mathlib.

**Rationale.** `polyEval_cusp_ψ` is the keystone of this project's bespoke *degenerate-fibre*
technique: it specialises the **universal** division polynomial to the singular cubic `Y²=X³` at
`(1,1)` to read off `ψₙ = n`, which immediately yields the universal non-vanishing `ψᵤ_ne_zero`
(the engine behind the file's main `zsmul = division-polynomial-evaluation` formula). It is stated
entirely in terms of objects with **no mathlib analogue** (`polyEval`, `specialize`, the universal
`curve.ψ`, the `cusp` curve), and its proof aggregates five project-local helpers — three of which
(`cusp_ψ₂/Ψ₃/preΨ₄`) were each ruled NO-composable-from-mathlib, plus `normEDS_two_three_two` whose
own linchpin (`IsEllSequence.ext`) is not in current mathlib. This is precisely the situation of its
three building-block siblings: bespoke witnesses in *this* project's universal-`ψₙ`-non-vanishing
argument, correct to keep as tidy project-local helpers, with no place in mathlib as written.

**WHY not the neighbours:**
- **NOT YES-add-as-is / YES-but-generalise-first** — there is nothing general here to ship: the
  statement names project-only objects (`polyEval`, universal `ψ`, `cusp`) with no mathlib home, and
  its honest "generalisation" is the project's universal-division-polynomial scaffolding, not a
  standalone mathlib result. (The generalisable unit nearby is the *def* `cusp` → `cusp (R)`, which
  is handled in `cusp.md`; it travels with that def, not this lemma.)
- **NOT NO-mathlib-has-it** — mathlib has neither this lemma nor any of its constituent objects
  (verified by exhaustive source reads); the only mathlib object in the vicinity is the per-curve
  `WeierstrassCurve.ψ`, which is *forked* here, not reused, and does not state any cusp evaluation.
- **NOT BORDERLINE** — the role (local scaffolding), the all-project-local dependency set, and the
  sibling precedent (`cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄` → all NO-composable-from-mathlib) make the
  classification unambiguous.

**Next action (refactor-actionable):** **keep** `WeierstrassCurve.Universal.polyEval_cusp_ψ` as
project-local scaffolding for the universal-`ψₙ`-non-vanishing argument. **Do not delete and do not
inline** — it is a named intermediate consumed by `polyEval_cusp_φ/ψc/ω` and `ψᵤ_ne_zero`, and
inlining the `rw […]; simp […]` chain at those call sites would be strictly worse. **No mathlib
PR.** If/when the `cusp` curve (general `cusp (R)`) and the EDS uniqueness layer
(`IsEllSequence.ext`, via mathlib PR #13782) land upstream, the *building blocks* become mathlib —
but this evaluation lemma, phrased over the project's `polyEval`/universal-`ψ` machinery, remains a
local consequence of that machinery and stays in the project.

Mathlib building blocks (per-curve only; the universal/cusp layer is project-local):
`WeierstrassCurve.ψ` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:401`),
`WeierstrassCurve.ψ₂` (`…/DivisionPolynomial/Basic.lean:113`),
`WeierstrassCurve.normEDS` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`).

### Cross-references (sibling verdicts in this project)
- `cusp_ψ₂` → NO-composable-from-mathlib (building block)
- `cusp_Ψ₃` → NO-mathlib-has-it / scaffolding (building block)
- `cusp_preΨ₄` → scaffolding (building block)
- `cusp` (the def) → YES-but-generalise-first (`cusp (R) [CommRing R]`)
- `polyEval` (the def) → project-local; not in mathlib
- `normEDS_two_three_two` → NO-mathlib-has-it (pending mathlib PR #13782)

### Sources
- [A recurrence relation for elliptic divisibility sequences](https://arxiv.org/pdf/2102.07573)
- [Sequences associated to elliptic curves](https://arxiv.org/pdf/1909.12654)
- [On Division Polynomial PIT and Supersingularity](https://arxiv.org/pdf/1801.02664)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- mathlib PR #13782 (EDS uniqueness layer; `IsEllSequence.ext`), via arXiv:2604.05280.
