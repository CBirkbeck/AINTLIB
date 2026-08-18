# Mathlibable assessment: `WeierstrassCurve.Universal.polyEval_cusp_φ`

**Verdict: NO-composable-from-mathlib** (precisely: *does not belong in mathlib — it is a
project-local one-line corollary of `polyEval_cusp_ψ` over this project's own forked/scaffolding
universal-division-polynomial API; the "degenerate-fibre" witness for universal `φₙ`
non-vanishing; keep it local*).

- **Qualified name (VERIFIED from source):** `WeierstrassCurve.Universal.polyEval_cusp_φ`
- **Location:** `projects/NagellLutz/LutzNagell/ZSMul.lean:118`
- **Date:** 2026-06-22
- **Assessor run:** `/overview` Step-9 mathlibable, NagellLutz project.

> Qualified name VERIFIED. At line 118 the namespace stack is `namespace WeierstrassCurve`
> (opened ZSMul.lean:76) → `namespace Universal` (opened ZSMul.lean:86), with only
> `noncomputable section` + `variable`/`open` in between (sections do not contribute to the
> name). So the fully-qualified name is **`WeierstrassCurve.Universal.polyEval_cusp_φ`** —
> exactly the parsed name in the prompt.

---

## 1. Exact statement and proof (from source)

```lean
lemma polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring
```

with `{n : ℤ}` a section variable (ZSMul.lean:97).

**What it says.** Evaluate the **universal** `n`-th auxiliary division polynomial `curve.φ n` (the
bivariate polynomial `φₙ = C X · ψₙ² − ψₙ₊₁ · ψₙ₋₁` over `ℤ[A₁,…,A₆,X,Y]`) by the evaluation
homomorphism `polyEval cusp 1 1`, which specialises the universal coefficients to those of the
**cusp** curve `Y²=X³` (`cusp = ⟨0,0,0,0,0⟩`) and then sets `(X,Y) = (1,1)`. The result is `1`. In
words: **the auxiliary division polynomial `φₙ`, evaluated on the cuspidal cubic at the point
`(1,1)`, equals `1` for every integer `n`.**

**How the proof works — a one-line corollary of `polyEval_cusp_ψ`.** Unfold
`curve.φ n = C X · (curve.ψ n)² − curve.ψ (n+1) · curve.ψ (n−1)` and push `polyEval` through the
ring structure (`map_sub/map_mul/map_pow`). The companion lemma `polyEval_cusp_ψ` (ZSMul.lean:114)
rewrites every `polyEval cusp 1 1 (curve.ψ k)` to the integer `k`, and `polyEval … (C X)`/`(X)`
evaluate to `1` (the `X`-coordinate is `1`). What remains is the integer arithmetic
`1 · n² − (n+1) · (n−1) = n² − (n² − 1) = 1`, closed by `ring`. So the entire mathematical content
is the **trivial algebraic identity** `n² − (n²−1) = 1` applied on top of `ψₙ(cusp,1,1) = n`.

This is the classical fact that the polynomial pair `(φₙ, ψₙ)` has leading behaviour `(x^{n²}, …)`
with `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁`; on the trivial EDS `Wₙ = n` (the cusp's degenerate sequence) it
collapses to the constant `1`.

## 2. Definitions involved (all project-local; none in mathlib)

| object | what it is | mathlib? |
|---|---|---|
| `cusp` | `def cusp : Affine ℤ := ⟨0,0,0,0,0⟩` — the cuspidal cubic `Y²=X³` (`Universal.lean:180`) | **NO** (mathlib "cusp" = modular forms only) |
| `polyEval W x y` | `eval₂RingHom (eval₂RingHom W.specialize x) y : Poly →+* R` (`Universal.lean:203`) — evaluate a universal `ℤ[A₁,…,A₆,X,Y]`-polynomial at `(x,y)` after specialising coefficients to `W` | **NO** (no `Universal`/`specialize`/`polyEval` in mathlib) |
| `curve.φ n` | the **universal** auxiliary division polynomial over `Poly = ℤ[A₁,…,A₆,X,Y]` (`curve := Affine (MvPolynomial Coeff ℤ)`, `Universal.lean:84`); `φ := C X * ψ n ^ 2 - ψ (n+1) * ψ (n-1)` (`DivisionPolynomial.lean:371`) | **NO** universal form; the *per-curve* `WeierstrassCurve.φ` IS in mathlib (`DivisionPolynomial/Basic.lean:448`, identical body) |
| `curve.ψ n` | the **universal** division polynomial; `ψ := normEDS …` | **NO** universal form; per-curve `WeierstrassCurve.ψ` is in mathlib (`DivisionPolynomial/Basic.lean:401`) |
| `polyEval_cusp_ψ` | the sister lemma `polyEval cusp 1 1 (curve.ψ n) = n` (`ZSMul.lean:114`) | **NO** — sibling report ruled **NO-composable-from-mathlib** |

So the statement is phrased entirely in objects that **do not exist in mathlib**.

## 3. Role in the project

`polyEval_cusp_φ` is one of the four sister **cusp-evaluation value** lemmas
(`φ→1, ψ→n, ψc→2, ω→1`, ZSMul.lean:114/118/122/126) that implement the project's bespoke
*degenerate-fibre* technique for proving **universal non-vanishing** of the division polynomials. It
is consumed by exactly one downstream result:

- **`polyToField_φ_ne_zero`** (ZSMul.lean:148): `polyToField (curve.φ n) ≠ 0` in the universal
  field. Proof: if `polyToField (curve.φ n) = 0`, push it through `ringEval cusp_equation_one_one`
  to land in `ℤ`, where `polyEval_cusp_φ` rewrites the image to `1`; so `1 = 0`, contradiction. This
  is the *whole point* of the cusp machinery — it gives universal non-vanishing of `φₙ` "for free"
  by exhibiting a single specialisation (the cusp at `(1,1)`) on which `φₙ = 1 ≠ 0`.

`polyToField_φ_ne_zero` (together with the parallel `ψᵤ_ne_zero`) underpins the affine
multiplication formula `n • (X,Y) = (φₙ/ψₙ² , ωₙ/ψₙ³)` and the main `zsmul = smulEval` result of the
file (ZSMul.lean docstring, lines 9–14, 49–58). So this lemma is load-bearing scaffolding, *internal
to the project's proof architecture*.

## 4. Literature search (Phase 3)

- The defining identity `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁` and the fact that `(φₙ, ψₙ²)` give the
  multiplication-by-`n` `x`-coordinate (`x([n]P) = φₙ/ψₙ²`) is classical (Silverman, *Arithmetic of
  Elliptic Curves*, Exercise 3.7; standard division-polynomial references). On a **singular
  (cuspidal) cubic** `Y²=X³` the attached EDS degenerates to the **trivial sequence `Wₙ = n`**
  (Ward, *Memoir on Elliptic Divisibility Sequences*: a singular sequence is, up to equivalence, the
  trivial sequence `Wₙ = n` or a Lucas sequence). The smooth locus of `Y²=X³` is `≅ 𝔾ₐ` (the
  additive group), on which the multiplication formula trivialises and `φₙ` becomes constant `= 1`.
- A targeted web search ("division polynomial `φₙ` on cuspidal cubic `Y²=X³`", "EDS singular case,
  `ψₙ = n`, `φₙ`") confirms the standard sources treat the singular curve only as a **boundary
  example**, never as a named numbered theorem; the surveyed papers (arXiv:2102.07573,
  arXiv:1801.02664, arXiv:1108.3051, arXiv:1107.0506) state division-polynomial / EDS theory for
  **non-singular** Weierstrass curves and do not record the cusp specialisation of `φₙ` as a quotable
  result.
- The specific Lean phrasing — "`polyEval cusp 1 1 (curve.φ n) = 1`", i.e. an evaluation of the
  *universal* auxiliary division polynomial via the *universal-ring specialisation homomorphism* at
  the cusp — is a formalisation device, not a literature statement. Mathematically it is the
  one-liner `1·n² − (n+1)(n−1) = 1` on top of the (also-unnamed) `ψₙ(cusp,1,1) = n`.

**Phase-3 conclusion:** the underlying *mathematics* (degenerate EDS on the cusp making `φₙ = 1`) is
classical-but-unnamed; the *statement as written* is project-specific plumbing, and the *content* is
a trivial corollary of the sister `ψ`-value.

## 5. Mathlib search — five methods (Phase 5)

Pinned mathlib (this repo's `.lake/packages/mathlib`, rev `09b373db6e24`). **Present/absent
dominated by authoritative source reads** (the `lean_loogle`/`lean_leansearch` index MCP was not
reachable in this environment; the direct source reads below settle a present/absent question
definitively).

1. **Direct source read — universal/cusp machinery.** `grep -rln "namespace Universal|def polyEval|
   polyEval_cusp|def cusp|specialize"` over `Mathlib/AlgebraicGeometry/EllipticCurve/` → **zero
   hits** (the `Universal`/`cusp` matches are all in `Mathlib/NumberTheory/ModularForms/*` and
   `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`, false positives). Mathlib has **no**
   `Universal` namespace for Weierstrass curves, **no** `specialize`/`polyEval`, **no** universal
   division polynomial, and **no** cusp curve.
2. **Division-polynomial dir.** `Mathlib/.../DivisionPolynomial/{Basic,Degree}.lean` define the
   **per-curve** `WeierstrassCurve.φ` (`Basic.lean:448`, body identical to the project's
   `DivisionPolynomial.lean:371`) and `WeierstrassCurve.ψ` (`Basic.lean:401`). There is **no**
   `φ_ne_zero`/`coeff_φ`/`natDegree_φ`-style lemma, **no** evaluation-on-a-specific-curve lemma, and
   **no** singular/cusp instance (`grep "φ_ne_zero|φ.*ne_zero|coeff_φ|natDegree_φ"` → none).
3. **Cusp / singular cubic.** `grep` for `def cusp`, `Y²=X³`, `⟨0,0,0,0,0⟩`, `cuspidal`, `singular
   cubic` over `Mathlib/` → only the **modular-forms** `cuspFunction`/`Cusps` family. Mathlib's
   elliptic-curve API deliberately excludes `Δ=0`, so there is no object for this lemma to attach to
   (consistent with sibling `cusp.md` / `cusp_ψ₂.md` reports).
4. **`φₙ = 1` / `φ` evaluation shape.** `grep` for `φ .* = 1`, `eval.*φ`, `φ.*cusp` over the EDS and
   division-polynomial files → none. No mathlib lemma evaluates `φₙ` at a point or on a specific
   curve.
5. **Consumer/duplication check.** The only sibling copy of this technique repo-wide is the
   HasseWeil fork of the same EDS/division-polynomial author lineage (Angdinata/Xu); there is no
   independent mathlib analogue. No mathlib lemma states "auxiliary division polynomial evaluated on
   a (cusp) curve = 1."

**Phase-5 conclusion:** neither this lemma nor any of its constituent objects (`Universal`,
`polyEval`, universal `curve.φ`/`curve.ψ`, `cusp`) is in mathlib. The only mathlib object in the
neighbourhood is the *per-curve* `WeierstrassCurve.φ` (identical definition), which the project
**forks** into a universal version this lemma evaluates.

## 6. Generality analysis (Phase 4)

**Maximally specialised** — and not in the direction of a mathlib lemma. Three independent pins:
(i) the curve is the fixed singular cubic `cusp` (not a variable curve); (ii) the point is the fixed
`(1,1)`; (iii) the base is `ℤ`. There is no "weaker-hypothesis" or "more-general" restatement to
upstream: the honest "general parent" of this statement is the *universal auxiliary
division-polynomial* machinery (`polyEval` + `curve.φ` + `curve.ψ` + `ringEval`), which is **itself
project-specific scaffolding not in mathlib**, not a more-general mathlib lemma waiting to be stated.
(Contrast `cusp` the *def*, whose general form `cusp (R) [CommRing R]` IS a sensible mathlib
addition — that generality belongs to the parent `def cusp`, not to this evaluation lemma, and
travels with it.)

## 7. Composition check — can ≤3 mathlib calls give it? (Phase 6)

**No, not from current mathlib.** This lemma is a **one-line corollary** of a project-local lemma
that is itself an aggregator:

```text
polyEval_cusp_φ
  ├── φ (unfold)            ─ project def (forked universal φ; = C X·ψ² − ψ₊·ψ₋)
  ├── map_sub/map_mul/map_pow ─ generic ring-hom lemmas (mathlib ✓)
  ├── polyEval_cusp_ψ       ─ project lemma (NO-composable-from-mathlib) — supplies ψₖ ↦ k
  ├── polyEval / eval₂ lemmas ─ project def + generic Polynomial.eval₂ API (supply X ↦ 1)
  └── ring                  ─ closes  1·n² − (n+1)(n−1) = 1
```

The *only* mathematically substantive ingredient is `polyEval_cusp_ψ`, which is **project-local**
and was independently classified **NO-composable-from-mathlib** (it forks the universal `ψ`, the
`cusp` curve, `polyEval`/`specialize`, and rests on `normEDS_two_three_two` → `IsEllSequence.ext`,
not in current mathlib). Everything above `polyEval_cusp_ψ` is the trivial polynomial identity
`n² − (n²−1) = 1`.

So the *subject* `polyEval cusp 1 1 (curve.φ n)` is built from `polyEval` (no mathlib analogue) and
the **universal** `curve.φ`/`curve.ψ` (no mathlib analogue); and the *proof's* one non-generic step
is a NO-composable project lemma. There is therefore **no** ≤3-call route from *current* mathlib
primitives — those primitives (universal ring, `polyEval`, universal `φ`/`ψ`, cusp curve) **do not
exist upstream**. Hence "NO-composable" here means decisively *does not belong in mathlib*: it is a
local theorem of the project's own API, exactly as its keystone sibling `polyEval_cusp_ψ` is.

---

## Verdict: `WeierstrassCurve.Universal.polyEval_cusp_φ`

**Category: NO-composable-from-mathlib**

**Evidence:**
- **Literature (3):** the defining identity `φₙ = xψₙ² − ψₙ₊₁ψₙ₋₁` and `x([n]P)=φₙ/ψₙ²` are classical
  (Silverman); on the cuspidal cubic `Y²=X³` the EDS degenerates (`Wₙ=n`, smooth locus `≅ 𝔾ₐ`),
  making `φₙ ≡ 1` — but this is recorded only as a *boundary example*, never a named theorem, and the
  *universal-ring evaluation* phrasing is a formalisation device whose content is the one-liner
  `n² − (n²−1) = 1`.
- **Mathlib (5):** **absent** — no `Universal` namespace, no `polyEval`/`specialize`, no universal
  division polynomial, no `cusp` curve, no `φ`-evaluation/`φ_ne_zero` lemma. Only the *per-curve*
  `WeierstrassCurve.φ` (`DivisionPolynomial/Basic.lean:448`, identical body) and `WeierstrassCurve.ψ`
  exist, which the project **forks**.
- **Generality (4):** maximally specialised (fixed cusp, fixed `(1,1)`, base `ℤ`); its "general
  parent" is the project's own universal-division-polynomial scaffolding, not a missing mathlib
  lemma.
- **Composition (6):** **not** a ≤3-call composition from current mathlib — it is a one-line
  corollary (`ring` over `1·n² − (n+1)(n−1) = 1`) of the project-local `polyEval_cusp_ψ`
  (NO-composable-from-mathlib), stated over `polyEval` + universal `curve.φ`/`curve.ψ`, none of which
  is in mathlib.

**Rationale.** `polyEval_cusp_φ` is a sister *cusp-evaluation value* lemma in this project's bespoke
*degenerate-fibre* technique: it specialises the **universal** auxiliary division polynomial to the
singular cubic `Y²=X³` at `(1,1)` to read off `φₙ = 1`, which immediately yields the universal
non-vanishing `polyToField_φ_ne_zero` (one of the two engines behind the file's main
`zsmul = division-polynomial-evaluation` formula). Mathematically its content is the **trivial
identity** `n² − (n²−1) = 1` layered on top of the (also project-local) `ψₙ(cusp,1,1) = n`. It is
stated entirely in terms of objects with **no mathlib analogue** (`polyEval`, `specialize`, the
universal `curve.φ`/`curve.ψ`, the `cusp` curve), and its only substantive dependency,
`polyEval_cusp_ψ`, was itself ruled NO-composable-from-mathlib. This is precisely the situation of
its keystone sibling: a bespoke witness in *this* project's universal-`φₙ`/`ψₙ`-non-vanishing
argument, correct to keep as a tidy project-local helper, with no place in mathlib as written.

**WHY not the neighbours:**
- **NOT YES-add-as-is / YES-but-generalise-first** — there is nothing general here to ship: the
  statement names project-only objects (`polyEval`, universal `φ`/`ψ`, `cusp`) with no mathlib home,
  and its honest "generalisation" is the project's universal-division-polynomial scaffolding, not a
  standalone mathlib result. (The generalisable unit nearby is the *def* `cusp` → `cusp (R)`, handled
  in `cusp.md`; it travels with that def, not this lemma.)
- **NOT NO-mathlib-has-it** — mathlib has neither this lemma nor any of its constituent objects
  (verified by exhaustive source reads); the only mathlib objects in the vicinity are the per-curve
  `WeierstrassCurve.φ`/`ψ`, which are *forked* here, not reused, and state no cusp evaluation.
- **NOT BORDERLINE** — the role (local scaffolding), the all-project-local dependency set, the
  triviality of the marginal content (`n² − (n²−1) = 1`), and the keystone-sibling precedent
  (`polyEval_cusp_ψ` → NO-composable-from-mathlib) make the classification unambiguous.

**Next action (refactor-actionable):** **keep** `WeierstrassCurve.Universal.polyEval_cusp_φ` as
project-local scaffolding for the universal-`φₙ`-non-vanishing argument. **Do not delete and do not
inline** — it is a named intermediate consumed by `polyToField_φ_ne_zero`, and inlining the
`simp_rw […]; simp only […]; ring` chain at that call site would be strictly worse. **No mathlib
PR.** If/when the `cusp` curve (general `cusp (R)`) and the EDS uniqueness layer
(`IsEllSequence.ext`, via mathlib PR #13782, behind the sibling `polyEval_cusp_ψ`) land upstream,
the *building blocks* become mathlib — but this evaluation lemma, phrased over the project's
`polyEval`/universal-`φ`/`ψ` machinery, remains a local consequence of that machinery and stays in
the project.

Mathlib building blocks (per-curve only; the universal/cusp layer is project-local):
`WeierstrassCurve.φ` (`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:448`),
`WeierstrassCurve.ψ` (`…/DivisionPolynomial/Basic.lean:401`),
`WeierstrassCurve.normEDS` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:289`).

### Cross-references (sibling verdicts in this project)
- `polyEval_cusp_ψ` → NO-composable-from-mathlib (the keystone this lemma is a one-liner over)
- `polyEval_cusp_ψc` → (sister cusp-value lemma; same degenerate-fibre technique)
- `polyEval_cusp_ω` → (sister cusp-value lemma; same technique)
- `cusp_ψ₂` / `cusp_Ψ₃` / `cusp_preΨ₄` → NO-composable / scaffolding (building blocks of `polyEval_cusp_ψ`)
- `cusp` (the def) → YES-but-generalise-first (`cusp (R) [CommRing R]`)
- `polyEval` (the def) → project-local; not in mathlib
- `normEDS_two_three_two` → NO-mathlib-has-it (pending mathlib PR #13782)

### Sources
- [A recurrence relation for elliptic divisibility sequences](https://arxiv.org/pdf/2102.07573)
- [On Division Polynomial PIT and Supersingularity](https://arxiv.org/pdf/1801.02664)
- [Integral points on elliptic curves and explicit valuations of division polynomials](https://arxiv.org/pdf/1108.3051)
- [A mean value formula for elliptic curves](https://arxiv.org/pdf/1107.0506)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- J. Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), §III + Exercise 3.7 (division polynomials, `x([n]P)=φₙ/ψₙ²`).
- mathlib PR #13782 (EDS uniqueness layer; `IsEllSequence.ext`), via arXiv:2604.05280.
