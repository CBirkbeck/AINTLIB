# Mathlibable assessment: `WeierstrassCurve.Universal.polyEval_cusp_ω`

> Qualified name **verified from source**. The lemma sits at
> `projects/NagellLutz/LutzNagell/ZSMul.lean:126`, inside `namespace WeierstrassCurve`
> (opened line 76) → `namespace Universal` (opened line 86); the `namespace Affine` block does
> not start until line 157. Hence the full name is **`WeierstrassCurve.Universal.polyEval_cusp_ω`**
> (the parsed name in the prompt was correct).

## The declaration

```lean
lemma polyEval_cusp_ω : polyEval cusp 1 1 (curve.ω n) = 1 := by
  have := congr(polyEval cusp 1 1 $(curve.two_mul_ω n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this
```

Ingredients (all **project-local** in this fork):
- `cusp` — the **singular cubic** `Y² = X³` over ℤ, defined at
  `projects/NagellLutz/LutzNagell/Universal.lean:180`:
  `def cusp : Affine ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }` (the record `⟨0,0,0,0,0⟩`).
- `curve.ω n` — the **universal ω-division polynomial**, `WeierstrassCurve.ω` applied to the
  universal curve `Universal.curve` over `ℤ[A₁,…,A₆]`. `ω` is defined in the fork at
  `projects/NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:74` (the `Y`-coordinate numerator in
  `[n]P = (φₙ/ψₙ², ωₙ/ψₙ³)`).
- `polyEval cusp 1 1` — the project's **evaluation homomorphism** `Universal.Poly →+* ℤ`
  (`Universal.lean:203`): specialise the universal coefficients `Aᵢ ↦ cusp.aᵢ = 0`, then evaluate the
  remaining bivariate polynomial at `(X, Y) = (1, 1)`.
- `curve.two_mul_ω n` — the `ω` spec lemma `2·ωₙ = ψcₙ − a₁φₙψₙ − a₃ψₙ³`
  (`DivisionPolynomialOmega.lean:89`), specialised by `congr(…)` and combined with
  `polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2` (`ZSMul.lean:122`).

**Mathematical content.** Evaluating the universal ω-division polynomial on the **cuspidal cubic
`Y²=X³` at the point `(1,1)`** gives the constant `1`, for every `n : ℤ`. The proof reads off
`2·ωₙ(1,1) = ψcₙ(1,1) − a₁φₙψₙ − a₃ψₙ³`; on the cusp `a₁=a₃=0`, and `ψcₙ(1,1)=2`
(`polyEval_cusp_ψc`), so `2·ωₙ(1,1) = 2`, i.e. `ωₙ(1,1) = 1`. This is the **ω-row of the cusp
value table**

  `ψₙ(1,1) = n`  (`polyEval_cusp_ψ`, ZSMul.lean:114)
  `φₙ(1,1) = 1`  (`polyEval_cusp_φ`, ZSMul.lean:118)
  `ψcₙ(1,1) = 2` (`polyEval_cusp_ψc`, ZSMul.lean:122)
  `ωₙ(1,1) = 1`  (`polyEval_cusp_ω`, ZSMul.lean:126 — **this decl**)

— the instance, over the cusp, of the classical **degeneration "the EDS of the cuspidal cubic is the
trivial linear sequence `Wₙ = n`"**. On the smooth locus of `Y²=X³` (parametrised by the additive
group `𝔾ₐ`), `ψₙ` linearises to `n`, and the numerators `φₙ, ωₙ` collapse to `1`, consistent with
`[n]P = (φ/ψ², ω/ψ³)` reducing to `[n]·(1,1) = (1/n², 1/n³)` on the additive line.

## Role in the project

The four cusp-value lemmas exist to power the project's **degenerate-fibre non-vanishing argument**:
to prove the *universal* `ψₙ` is non-zero for `n ≠ 0` (`ψᵤ_ne_zero`, ZSMul.lean:142) and the
*universal* `φₙ` is non-zero (`polyToField_φ_ne_zero`, ZSMul.lean:148), one maps the universal ring
to ℤ through the cusp specialisation `ringEval cusp_equation_one_one` and reads off `ψₙ ↦ n ≠ 0`,
`φₙ ↦ 1 ≠ 0`. The `ψ`-row (`polyEval_cusp_ψ`) and the `φ`-row (`polyEval_cusp_φ`) are the
**load-bearing** members; `ψc` (`polyEval_cusp_ψc`) is an intermediate used *inside the proof of
`polyEval_cusp_ω`*.

**Call sites of `polyEval_cusp_ω`: ZERO.** Confirmed by
`grep -rn "polyEval_cusp_ω" projects/ --include="*.lean"` — the only two hits are the *declarations
themselves* (NagellLutz `ZSMul.lean:126`; the verbatim duplicate in HasseWeil
`Auxiliary/DivisionPolynomial.lean:202`). Nothing in either project consumes it. It is the
**completeness companion** that finishes the cusp value table (so the table reads uniformly
`ψ,φ,ψc,ω = n,1,2,1`), not a lemma any downstream proof needs. (Contrast: `polyEval_cusp_ψ` is used
at ZSMul.lean:119,145; `polyEval_cusp_φ` at ZSMul.lean:151.)

K (internal consumers) = 0. K (cross-project consumers) = 0. The decl is duplicated across two NT
projects but used by neither.

## (3) Literature search

| # | Channel | Query | Hit? | Finding |
|---|---------|-------|------|---------|
| 1 | WebSearch | "ω division polynomial evaluated at cusp Y²=X³ value singular cubic" | partial | Division polynomials are defined for cubic curves **including singular ones** (`y²=x³`); `[n]P=(φₙ/Ψₙ², ωₙ/Ψₙ³)` is the standard form with `ωₙ` the `Y`-numerator. No source states "ωₙ(1,1)=1 on the cusp" as a named result. |
| 2 | WebSearch | "EDS cuspidal cubic Y²=X³ Wₙ=n degenerate fiber specialization" | yes | The degeneration of an EDS over the **cuspidal fibre `y²=x³`** to the trivial linear sequence is documented (level structures over degenerate fibres, sign-of-EDS papers). This is the *general phenomenon* of which `ψₙ(1,1)=n`, `ωₙ(1,1)=1` are instances. |
| 3 | Silverman AEC | "The Division Polynomials" / Exercise 3.7 | n/a (known) | `ωₙ` is the standard `Y`-coordinate numerator; the cusp evaluation is an elementary substitution, not an exercise-named identity. |
| 4 | ChatGPT MCP | (self-contained question on whether the cusp value is a named theorem) | n/a | MCP unavailable this session (Codex stdin error, per task brief). Reasoned from sources + sibling verdicts instead. |
| 5 | Local references | `.mathlib-quality/references/`, `refs/` | n/a | directories absent in this project. |
| 6 | nLab / Stacks | "division polynomial", "elliptic divisibility sequence", "cuspidal cubic" | n/a | no dedicated `ωₙ`/cusp-evaluation page; these are computational objects outside the categorical/scheme-theoretic write-ups. |

**Literature summary.** Concept identified: the **ω-division polynomial `ωₙ`** specialised to the
**cuspidal cubic** and evaluated at a smooth-locus point. The *general* framework
(`[n]P=(φ/ψ², ω/ψ³)`; EDS-of-the-cusp `= Wₙ=n`) is standard; the **specific value `ωₙ(1,1)=1` on
`Y²=X³`** is an elementary computation named by **no source**. There is no "more general standard
form" to upstream here — the only generalisation of this value lemma is the general formula for `ωₙ`
itself (the `WeierstrassCurve.ω` TODO; see `two_mul_ω.md`), which this lemma merely *evaluates*.

## (5) Mathlib search (five methods)

Searched for both (a) the **specific** cusp-ω value and (b) any general parent.

| Method | Query | Result |
|--------|-------|--------|
| [A] Lean-Finder / leansearch | "omega division polynomial value at cusp Y²=X³ equals 1" | no hits (mathlib index has no such statement; reasoned from source). |
| [B] Loogle | `WeierstrassCurve.ω`, `polyEval _ _ _ (_ .ω _) = 1` | **no hits** — `WeierstrassCurve.ω` is **undefined in mathlib** (it is a TODO), so neither the object nor any evaluation lemma exists. |
| [C] LeanSearch | "division polynomial cuspidal cubic value" | no hits. |
| [D] Grep mathlib src | `polyEval`, `def cusp`/`abbrev cusp`/`structure cusp`, `cuspidalCubic`, `nodalCubic`, `Y ^ 2 = X ^ 3`, `normEDS_two_three_two`, `compl₂EDS_two_three_two` over `.lake/packages/mathlib/Mathlib/` | **no hits.** No `polyEval` homomorphism, **no `cusp` curve object**, no cusp-value EDS lemma, no `…_two_three_two` building block in mathlib. |
| [E] Name pattern | `cusp` / `singular` in `Mathlib/AlgebraicGeometry/EllipticCurve/` | the **only** matches are prose comments (`Weierstrass.lean:16,129` — "nonsingular Weierstrass curve", "the cubic curve … is singular"). Mathlib's word "cusp" elsewhere is the **modular-forms** sense (`Analysis/Complex/Periodic.lean`, `ModularForms/Cusps.lean`). |

**Decisive mathlib evidence.**
- `WeierstrassCurve.ω` is an **explicit TODO** in
  `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71` ("TODO: the bivariate
  polynomials `ωₙ`.") and `:83`. The object this lemma evaluates **does not exist upstream**.
- Mathlib has **no `cusp` / singular-cubic object**. Its elliptic-curve API is built around
  *nonsingular* Weierstrass curves (`Weierstrass.lean:16`); `Y²=X³` is singular and deliberately out
  of scope, so there is **nothing for a cusp-value lemma to attach to**.
- The proof's building blocks (`polyEval`, `specialize`, `cusp`, `ψc`, `compl₂EDS_two_three_two`) are
  **all project-forked**, absent from mathlib.

Concluded: **not in mathlib** — neither the value nor the `ω`/`cusp`/`polyEval` apparatus it is built
from. This is the same situation as the siblings `cusp_ψ₂` and `cusp_equation_one_one` (both
`NO-composable-from-mathlib`).

## Generality analysis

The lemma is **MAXIMALLY SPECIALISED** — a single numeric value (`= 1`) at **one fixed singular
curve** (`Y²=X³`) and **one fixed point** (`(1,1)`). This is the *opposite* of a generalisation
target; there is no weaker-hypothesis or more-general restatement to upstream.

| # | Parameter | Current form | More-general form | Weaken? | Reason |
|---|-----------|--------------|-------------------|---------|--------|
| 1 | the curve | fixed cusp `⟨0,0,0,0,0⟩` | arbitrary `WeierstrassCurve R` | NO | the value `=1` is *specific to the cusp*; over a general curve `ωₙ(x,y)` is not constant. Generalising the curve gives the **`ω` def + `two_mul_ω` spec**, which is the *separate* `WeierstrassCurve.ω` TODO (see `two_mul_ω.md`), not this value lemma. |
| 2 | the point | fixed `(1,1)` | arbitrary `(x,y)` | NO | `(1,1)` is the chosen smooth-locus rational point of the cusp; the value depends on it. |
| 3 | the value | constant `1` | — | n/a | `1` is the degenerate value; not a parametric statement. |
| 4 | index `n : ℤ` | already `∀ n : ℤ` | — | already maximal | the only universally-quantified slot is already as general as it can be. |

The "general parent" — the formula for `ωₙ` over an arbitrary curve — **is** the `WeierstrassCurve.ω`
development (`def ω`, `ω_spec`, `two_mul_ω`), already assessed `YES-add-as-is` in `two_mul_ω.md`.
`polyEval_cusp_ω` is just the **evaluation of that object on the degenerate fibre**, with nothing of
its own to generalise.

## (6) Composition check

**Can it be derived from *current* mathlib in ≤3 calls?** No — three of its four ingredients
(`curve.ω`, `cusp`, `polyEval`) **do not exist in mathlib**, so there is nothing upstream to compose
against. In the strict "current mathlib" sense it is `NOT-COMPOSABLE`, for the same reason
`two_mul_ω` is: its subject `ω` is itself an unimplemented TODO.

**But** — and this is what places it in the *composable* bucket rather than a `YES` bucket — once the
`ω`/`cusp`/`polyEval` apparatus is present (i.e. *within this project*, or after the `ω` TODO is
discharged upstream), the lemma is a **one-shot computation**, not a result anyone re-states:

```lean
-- the project's own proof IS the composition (3 short steps):
have := congr(polyEval cusp 1 1 $(curve.two_mul_ω n))   -- specialise the ω spec
simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this  -- a₁=a₃=0, ψc↦2
simpa [cusp, polyEval, specialize, curve] using this    -- ⇒ 2·ω(1,1)=2 ⇒ ω(1,1)=1
```

It composes `two_mul_ω` (the `ω` spec) with `polyEval_cusp_ψc` (the cusp `ψc`-value) and the cusp's
zero coefficients — a `congr` + two `simp`s. So: **COMPOSABLE** as soon as the `ω` machinery exists;
it is a derived value, never a standalone lemma worth its own upstream identity.

---

## Verdict: `WeierstrassCurve.Universal.polyEval_cusp_ω`

**Category:** NO-composable-from-mathlib

**Evidence:**
- **Literature (3):** the general frame (`[n]P=(φ/ψ², ω/ψ³)`; EDS-of-the-cuspidal-cubic `= Wₙ=n`) is
  standard, but the **specific value `ωₙ(1,1)=1` on `Y²=X³`** is an elementary computation named by no
  source.
- **Mathlib (5):** **not present** — `WeierstrassCurve.ω` is a documented **TODO**
  (`DivisionPolynomial/Basic.lean:71,83`), mathlib has **no `cusp`/singular-cubic object** (its EC API
  is nonsingular-only; "cusp" there = modular forms), and the `polyEval`/`compl₂EDS_two_three_two`
  building blocks are project-forked.
- **Generality (4):** **MAXIMALLY SPECIALISED** (one singular curve, one point, constant value);
  nothing to generalise — its general parent *is* the separate `WeierstrassCurve.ω` development
  (`two_mul_ω.md`, `YES-add-as-is`).
- **Composition (6):** once `ω`/`cusp`/`polyEval` exist, it is a `congr` + two `simp`s composing
  `two_mul_ω` with `polyEval_cusp_ψc` and `a₁=a₃=0` — a derived value, not a standalone result.
- **Usage:** **ZERO consumers** in either NagellLutz or HasseWeil (only the two verbatim
  declarations); it is the completeness companion of the cusp value table, not a load-bearing lemma.

**Rationale.**
`polyEval_cusp_ω` is project-local scaffolding, not a mathlib candidate. It records one numeric value
— the universal ω-division polynomial, specialised to the cuspidal cubic `Y²=X³` and evaluated at the
smooth-locus point `(1,1)`, equals `1` — the ω-row of this project's bespoke "cusp value table"
(`ψ,φ,ψc,ω = n,1,2,1`) that drives the **degenerate-fibre proof that the universal `ψₙ` is
non-zero**. Mathlib owns neither the value nor the objects it is built from: `WeierstrassCurve.ω` is
an explicit TODO, and mathlib has no notion of a singular "cusp curve" (`Y²=X³` is excluded from the
nonsingular-only EC API; mathlib's "cusp" is the modular-forms sense). This is exactly the standing
of the siblings `cusp_ψ₂` and `cusp_equation_one_one`, both ruled `NO-composable-from-mathlib`: a
bespoke witness in *this* project's universal-non-vanishing argument, derivable in a `congr`+`simp`
once the `ω` apparatus is in scope, and used by **no downstream proof** (its raw call count is zero in
both NT projects).

It is **not** `NO-mathlib-has-it` (mathlib has neither the value nor the `ω`/`cusp`/`polyEval`
objects), and **not** a `YES` bucket (a degenerate numeric instance at one curve/point is not reusable
general content — the reusable content is the *general* `ω` formula, assessed separately in
`two_mul_ω.md`). It lands in `NO-composable-from-mathlib`: it does **not belong in mathlib**; it
should remain a private/local helper.

**WHY not (refactor-actionable):** the reusable building block to upstream is the **general**
`WeierstrassCurve.ω` family — `def ω`, `ω_spec`, `two_mul_ω` (discharging the `ωₙ` TODO at
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71,83`; see `two_mul_ω.md`,
`YES-add-as-is`). `polyEval_cusp_ω` is a ≤3-step evaluation of that family on the cusp; no separate
mathlib lemma is implied.

**Caveat for the refactor — keep, but consider whether even the project needs it.** Unlike its
load-bearing siblings `polyEval_cusp_ψ`/`polyEval_cusp_φ` (consumed by `ψᵤ_ne_zero` /
`polyToField_φ_ne_zero`), `polyEval_cusp_ω` has **zero consumers**. It is a tidy completeness
companion finishing the cusp value table, and as such is reasonable to keep as a named local helper
(it reads uniformly alongside `ψ`/`φ`/`ψc`). But if a future cleanup wants to trim dead API, this
(and the equally-unused `polyEval_cusp_ψc`, which however *is* used inside this very proof) are the
candidates — a *project* decision, not a mathlib one. Either way it does **not** go to mathlib.

**Next action:** keep `WeierstrassCurve.Universal.polyEval_cusp_ω` as project-local scaffolding for
the degenerate-fibre argument (or drop it as unused API at the project's discretion). **No mathlib
PR.** The mathlib-bound work in this neighbourhood is the general `WeierstrassCurve.ω` bundle tracked
by `two_mul_ω.md`.

Mathlib building blocks (for the general parent, not this value):
`WeierstrassCurve.ψ`, `WeierstrassCurve.φ`
(`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean`), and the EDS complement API
`complEDS₂` / `normEDS_mul_complEDS₂`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`) — with `WeierstrassCurve.ω` itself still a
TODO (`DivisionPolynomial/Basic.lean:71,83`).

### Sources
- [Sequences associated to elliptic curves (arXiv:1909.12654)](https://arxiv.org/pdf/1909.12654)
- [p-adic properties of division polynomials and elliptic divisibility sequences (arXiv:math/0404412)](https://arxiv.org/pdf/math/0404412)
- [Level structures on the Weierstrass family of cubics (arXiv:math/0512117)](https://arxiv.org/pdf/math/0512117)
- [The sign of an elliptic divisibility sequence (arXiv:math/0402415)](https://arxiv.org/abs/math/0402415)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- mathlib `DivisionPolynomial/Basic.lean` (the `ωₙ` TODO, lines 30, 71, 83) and `Weierstrass.lean`
  (nonsingular-only EC API, lines 16, 129) — local pin `.lake/packages/mathlib`.
- Sibling assessments: `two_mul_ω.md` (`YES-add-as-is`), `cusp_ψ₂.md` / `cusp_equation_one_one.md`
  (`NO-composable-from-mathlib`).
