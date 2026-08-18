# Mathlibable assessment — `WeierstrassCurve.Universal.polyEval_cusp_ψc`

**Verdict: NO-composable-from-mathlib** (internal computation lemma; built entirely on
project-private scaffolding, not literature-standard, not a reusable mathlib API target).

---

## 1. The declaration

File: `projects/NagellLutz/LutzNagell/ZSMul.lean:122`
Qualified name (verified from source): **`WeierstrassCurve.Universal.polyEval_cusp_ψc`**
(open namespaces at that line: `WeierstrassCurve` → `noncomputable section` → `Universal`; the
inner `Affine`/`Jacobian` namespaces open only later at lines 157/395).

```lean
lemma polyEval_cusp_ψc : polyEval cusp 1 1 (curve.ψc n) = 2 := by
  rw [ψc, map_compl₂EDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, compl₂EDS_two_three_two]
```

with implicit `n : ℤ` (from `variable {m n : ℤ}` at line 97).

### What it says, mathematically

`cusp` is the singular Weierstrass curve `y² = x³` over `ℤ` (`a₁=…=a₆=0`,
`Universal.lean:180`). `curve` is the **universal** Weierstrass curve over
`MvPolynomial Coeff ℤ = ℤ[A₁,A₂,A₃,A₄,A₆]` (`Universal.lean:84`).
`polyEval W x y : ℤ[A₁..A₆][X][Y] →+* R` (`Universal.lean:203`) is the ring hom that
specialises the universal coefficients to those of `W` and then evaluates `X ↦ x`, `Y ↦ y`.
`curve.ψc n` is the universal **complement division polynomial**
`ψc := compl₂EDS ψ₂ (C Ψ₃) (C preΨ₄)` — the witness of `ψ(n) ∣ ψ(2n)`
(`DivisionPolynomialOmega.lean:51`; `ψc_spec`: `W.ψ n * W.ψc n = W.ψ (2*n)`).

The lemma evaluates the universal `ψc n` at the cusp curve, point `(1,1)`, and gets the
**constant `2`**, independent of `n`. Reason: for the cusp at `(1,1)` the seed values are
`ψ₂ = 2`, `Ψ₃ = 3`, `preΨ₄ = 2` (`cusp_ψ₂`/`cusp_Ψ₃`/`cusp_preΨ₄`, lines 110-112), so the EDS
becomes the identity sequence `ψ(n) = n` and its `2n`-complement
`compl₂EDS 2 3 2 n` is constantly `2` (`compl₂EDS_two_three_two`, `EllipticDivisibilitySequence.lean:1241`,
proved from `normEDS_mul_compl₂EDS` + `normEDS_two_three_two` since `n·2 = 2n`).

### Role in the development

One of a tight family `polyEval_cusp_ψ` (=`n`), `_φ` (=`1`), `_ψc` (=`2`), `_ω` (=`1`)
(lines 114-129). `_ψc` directly feeds `polyEval_cusp_ω` (line 126-129, via `two_mul_ω`) and the
cusp serves as the **char-0 reduction witness** that the universal `ψ`/`φ` are nonzero in the
universal field (`ψᵤ_ne_zero`, `polyToField_φ_ne_zero`, lines 142-152) — the nonvanishing engine
behind the whole multiplication-by-`n` formula `WeierstrassCurve.zsmul_eq_smulEval`.

## 2. Literature search

WebSearch on EDS / division-polynomial / cusp-specialisation and on universal-Weierstrass /
Nagell-Lutz integrality returned the expected background corpus (Ward EDS; Stange; Ayad/Cheon-Hahn
valuations of division polynomials; Alpoge "Nagell-Lutz, quickly"; arXiv:1303.4327 homogeneous
universal division polynomials in `ℤ[a₁..a₆][x,y,z]`) but **nothing** matching this statement. No
source names a "value of the EDS complement at the cusp" fact. The universal-curve-as-a-point
technique exists in the literature, but "specialise `ψc` to `y²=x³` at `(1,1)`, get `2`" is not a
quotable theorem — it is an artefact of this particular Lean proof architecture.

## 3. Mathlib search (five methods)

Searched the pinned mathlib at `.lake/packages/mathlib` (the elliptic-curve / EDS sources).
**Every primitive in the statement is project-private:**

| symbol | in mathlib? | evidence |
|---|---|---|
| `compl₂EDS`, `compl₂EDSAux` | **NO** | `grep` of `Mathlib/` empty; project added it to its **forked** `EllipticDivisibilitySequence.lean` (header: same author, D. K. Angdinata) |
| `WeierstrassCurve.ψc` | **NO** | mathlib `DivisionPolynomial/{Basic,Degree}.lean` only; `DivisionPolynomialOmega.lean` header: *"extends the division polynomial development from mathlib with the `ω` family … the complement `ψc` …"* |
| `Universal.curve`, `Universal.polyEval`, `specialize`, `Universal.Field`, `Universal.Ring` | **NO** | no `namespace Universal` / `def polyEval` / `def specialize` under `Mathlib/AlgebraicGeometry/EllipticCurve/` |
| `cusp` (singular Weierstrass `y²=x³`) | **NO** | the only `cusp` hits in mathlib are modular-forms cusps of `ℍ` (`ModularForms/Cusps.lean` etc.) — unrelated |
| `compl₂EDS_two_three_two`, `normEDS_two_three_two` | **NO** | not in mathlib |

So the lemma cannot "already be in mathlib": it is not even **statable** in mathlib without first
upstreaming `compl₂EDS`, `ψc`, and the entire `Universal`/`cusp` apparatus. (The prompt's hypothesis
"this decl may already be in mathlib via the forked tracks" is therefore refuted — mathlib has the
`ψ/φ/ω`-less core only; `ψc` and the universal machinery are net-new here.)

## 4. Generality analysis

The statement is maximally **specialised**, not general: fixed curve (`cusp`), fixed point
`(1,1)`, fixed output `2`. Its only "variable" is `n`, and the result is constant in `n`. It is a
closed numeric evaluation, not an API surface. There is no more-general true statement worth
upstreaming here other than the genuinely reusable building block it rests on,
`compl₂EDS_two_three_two` — and even that is itself a one-off specialisation
(`compl₂EDS 2 3 2 = const 2`).

## 5. Composition check (≤ 3 mathlib calls?)

Not applicable in the literal sense — the supporting lemmas are project-local, not mathlib. But the
proof is exactly a 2-step composition over **project** API: rewrite `ψc`→`compl₂EDS` and push the
specialisation through (`map_compl₂EDS`, `evalEval_ψ₂/Ψ₃/preΨ₄`, the three `cusp_*` seed values),
then `compl₂EDS_two_three_two` closes it. Given the project's own `compl₂EDS_two_three_two` and the
`cusp_*` seeds, this lemma is a 5-line `rw`+`simp` — i.e. trivially composable from material the
project already has. It carries no standalone mathematical weight.

## 6. Verdict

**NO-composable-from-mathlib.**

- It is **not in mathlib** and is **not statable** in mathlib (depends on `compl₂EDS`, `ψc`,
  `Universal.curve/polyEval/Field`, `cusp` — all project-private extensions/forks).
- It is **not a literature-standard result** — no source states it; it is an internal computation.
- It is **trivially composable** (2-line `rw` + `simp` + one helper `compl₂EDS_two_three_two`) from
  the project's own seed lemmas, so it has no reusable-API value to upstream on its own.

### What *could* plausibly be mathlib-bound (not this lemma)

If anything from this neighbourhood is upstreamed, it is the **infrastructure**, not this
evaluation: the `compl₂EDS` complement + `normEDS_mul_compl₂EDS` (`ψ(n) ∣ ψ(2n)` witness) and the
`ω` division-polynomial family, which genuinely fill a gap in mathlib's `DivisionPolynomial`
development. Those are the real mathlibable candidates (assess them separately). `polyEval_cusp_ψc`
itself would ride along only as a private proof detail of `zsmul_eq_smulEval`, never as a named
mathlib lemma.
