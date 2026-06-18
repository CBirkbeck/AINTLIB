# Inventory: ./HasseWeil/FormalGroupCorrespondence.lean

**File**: `HasseWeil/FormalGroupCorrespondence.lean`
**Lines**: 1–309 (309 total; ~220 code lines)
**Imports**: `HasseWeil.Auxiliary.DivisionPolynomial`, `HasseWeil.FormalGroupAssoc`, `HasseWeil.InvariantDifferential`, `Mathlib.RingTheory.Kaehler.Basic`, `Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition`, `Mathlib.LinearAlgebra.Basis.VectorSpace`

**Summary**: Establishes two results connecting the formal group of an elliptic curve to its algebraic geometry: (1) the Kähler differential module Ω[K(E)/F] is 1-dimensional over K(E) (Silverman III.1.5), and (2) the formal group multiplication-by-m series has linear coefficient m (Silverman IV.2.3a). Contains 4 declarations (all theorems), 0 instances, 0 defs, 0 sorries. `kaehler_rank_one` is a key API declaration used heavily by other files. The section on Frobenius pullback (`FrobeniusPullback`) was deliberately deleted; a comment at lines 302–307 documents its removal.

---

## Section `OmegaOneDim`

Variable context: `(E : Affine F) [E.IsElliptic]`

---

### `theorem kaehler_rank_one`

- **Type**:
  ```
  kaehler_rank_one : Module.finrank E.FunctionField (KaehlerDifferential F E.FunctionField) = 1
  ```
- **What**: Proves that the module of Kähler differentials Ω[K(E)/F] has rank 1 as a K(E)-vector space. Equivalently, every differential is a K(E)-multiple of the invariant differential ω = dx/(2y+a₁x+a₃).
- **How**: Shows that the span of ω equals ⊤ by a 5-step induction: (1) D(xⁿ) ∈ span{D(x)} by Leibniz + induction; (2) D(p(x)) ∈ span{D(x)} for p ∈ F[X] by `Polynomial.induction_on'`; (3) D(y) ∈ span{D(x)} via the Weierstrass relation differentiated by Leibniz and the non-vanishing `denom_ne_zero E`; (4) D(r) for r ∈ CoordinateRing via `Affine.CoordinateRing.exists_smul_basis_eq`; (5) D(f) for f ∈ K(E) via `IsFractionRing.div_surjective` + Leibniz for D(b⁻¹). The generator witness uses `invariantDifferential_ne_zero E` and `finrank_eq_one_iff'`.
- **Hypotheses**: E is an affine elliptic curve over a field F with `DecidableEq F`.
- **Uses from project**: `invariantDifferential` (InvariantDifferential.lean), `invariantDifferential_ne_zero` (InvariantDifferential.lean), `denom_ne_zero` (InvariantDifferential.lean), `Affine.CoordinateRing.exists_smul_basis_eq` (project utility).
- **Used by**: unused in this file; used by `PullbackCoeff.lean`, `OmegaPullbackCoeff.lean`, `GapQfKernel.lean`, `EC/DifferentialOrd.lean`, `Curves/Differentials.lean` (key API).
- **Visibility**: public
- **Lines**: 61–217 (proof ~157 lines)
- **Notes**: `set_option maxHeartbeats 1600000` (value 1600000) — NO-COMMENT (no justification). Proof is **157 lines**, the longest in the file. This is a substantial Kähler differential argument; no sorry, but the heartbeat increase is significant and unexplained.

---

## Section `MulByMFormal`

Variable context: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic]`

---

### `theorem formalMulByInt_linear_coeff`

- **Type**:
  ```
  formalMulByInt_linear_coeff (m : ℤ) : formalMulByInt_coeff W.toAffine m 1 = (m : F)
  ```
- **What**: The degree-1 coefficient of the formal group power series [m]_F(T) equals m (as an element of F).
- **How**: Directly by `simp [formalMulByInt_coeff]`; the result follows definitionally from how `formalMulByInt_coeff` is defined in `FormalGroupAssoc.lean`.
- **Hypotheses**: W is a Weierstrass curve over F with IsElliptic.
- **Uses from project**: `formalMulByInt_coeff` (FormalGroupAssoc.lean).
- **Used by**: `pullback_coeff_eq_formal_coeff_mulByInt` (this file).
- **Visibility**: public
- **Lines**: 235–237 (proof 1 line)
- **Notes**: Essentially a restatement/renaming of a result already in `FormalGroupAssoc.lean` (line 110–111 there proves the same thing). Possible duplication with `FormalGroupAssoc`.

---

### `theorem formalMulByInt_const_zero`

- **Type**:
  ```
  formalMulByInt_const_zero (m : ℤ) : formalMulByInt_coeff W.toAffine m 0 = 0
  ```
- **What**: The constant term (degree-0 coefficient) of the formal group power series [m]_F(T) is 0; the series has no constant term, i.e., [m]_F(0) = 0.
- **How**: Directly by `simp [formalMulByInt_coeff]`.
- **Hypotheses**: W is a Weierstrass curve over F with IsElliptic.
- **Uses from project**: `formalMulByInt_coeff` (FormalGroupAssoc.lean).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 240–242 (proof 1 line)
- **Notes**: Not referenced in any other file in the project (dead-code candidate externally).

---

## Section `Correspondence`

Variable context: `(W : WeierstrassCurve F) [W.toAffine.IsElliptic]`

---

### `theorem pullback_coeff_eq_formal_coeff_mulByInt`

- **Type**:
  ```
  pullback_coeff_eq_formal_coeff_mulByInt (m : ℤ) : formalMulByInt_coeff W.toAffine m 1 = (m : F)
  ```
- **What**: States (redundantly) that the linear formal-group coefficient of [m] equals m, presented as "the formal ↔ curve correspondence" for the pullback coefficient. This is the same statement as `formalMulByInt_linear_coeff`.
- **How**: Direct application of `formalMulByInt_linear_coeff W m`.
- **Hypotheses**: W is a Weierstrass curve over F with IsElliptic.
- **Uses from project**: `formalMulByInt_linear_coeff` (this file).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 280–284 (proof 1 line)
- **Notes**: This declaration is **identical in statement** to `formalMulByInt_linear_coeff`; its entire proof is just a call to that lemma. It appears to be a documentation/alias placeholder — the docstring frames it as the "formal ↔ curve correspondence theorem" but adds no mathematical content beyond the prior lemma. Dead-code candidate both within file and externally.

---

## Cross-Reference Summary

| Declaration | Used by (this file) | Used by (other files) |
|---|---|---|
| `kaehler_rank_one` | none | PullbackCoeff, OmegaPullbackCoeff, GapQfKernel, EC/DifferentialOrd, Curves/Differentials |
| `formalMulByInt_linear_coeff` | `pullback_coeff_eq_formal_coeff_mulByInt` | none found |
| `formalMulByInt_const_zero` | none | none found |
| `pullback_coeff_eq_formal_coeff_mulByInt` | none | none found |

## Deleted Content

Lines 302–307 document the deliberate deletion of a `FrobeniusPullback` section containing two vacuous `True := trivial` placeholders (`frobenius_pullback_coeff_zero`, `one_sub_frobenius_pullback_coeff_one`). The real results live in `OmegaPullbackCoeff.lean`.
