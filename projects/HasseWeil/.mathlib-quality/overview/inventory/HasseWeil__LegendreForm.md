# Inventory: ./HasseWeil/LegendreForm.lean

**File**: `HasseWeil/LegendreForm.lean`
**Lines**: 1–208
**Module docstring**: Legendre normal form for elliptic curves over algebraically closed fields of characteristic ≠ 2.

---

## Declarations

### `def legendreCurve`
- **Type**: `(l : F) : WeierstrassCurve F`
- **What**: Defines the Weierstrass curve `a₁=0, a₂=−(1+l), a₃=0, a₄=l, a₆=0`, i.e. `Y²=X(X−1)(X−l)`.
- **How**: Direct record construction; no proof content.
- **Hypotheses**: `F` a field.
- **Uses from project**: none
- **Used by**: `legendreCurve_a₁`, `legendreCurve_a₂`, `legendreCurve_a₃`, `legendreCurve_a₄`, `legendreCurve_a₆`, `legendreCurve_isCharNeTwoNF`, `legendreCurve_Δ`, `legendreCurve_Δ_ne_zero_iff`, `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero`, `exists_legendreCurve_iso`
- **Visibility**: public
- **Lines**: 41–42, proof length: 1
- **Notes**: Core definition.

---

### `theorem legendreCurve_a₁`
- **Type**: `(l : F) : (legendreCurve l).a₁ = 0`
- **What**: The first Weierstrass coefficient of the Legendre curve is 0.
- **How**: `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero` (via `@[simp]`)
- **Visibility**: public (`@[simp]`)
- **Lines**: 44–45, proof length: 1
- **Notes**: simp lemma.

---

### `theorem legendreCurve_a₂`
- **Type**: `(l : F) : (legendreCurve l).a₂ = -(1 + l)`
- **What**: The second Weierstrass coefficient of the Legendre curve is `−(1+l)`.
- **How**: `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: `legendreCurve_Δ`
- **Visibility**: public (`@[simp]`)
- **Lines**: 47–48, proof length: 1
- **Notes**: simp lemma.

---

### `theorem legendreCurve_a₃`
- **Type**: `(l : F) : (legendreCurve l).a₃ = 0`
- **What**: The third Weierstrass coefficient of the Legendre curve is 0.
- **How**: `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero` (via `@[simp]`)
- **Visibility**: public (`@[simp]`)
- **Lines**: 50–51, proof length: 1
- **Notes**: simp lemma.

---

### `theorem legendreCurve_a₄`
- **Type**: `(l : F) : (legendreCurve l).a₄ = l`
- **What**: The fourth Weierstrass coefficient of the Legendre curve is `l`.
- **How**: `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: `legendreCurve_Δ`
- **Visibility**: public (`@[simp]`)
- **Lines**: 53–54, proof length: 1
- **Notes**: simp lemma.

---

### `theorem legendreCurve_a₆`
- **Type**: `(l : F) : (legendreCurve l).a₆ = 0`
- **What**: The sixth Weierstrass coefficient of the Legendre curve is 0.
- **How**: `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: `legendreCurve_Δ`
- **Visibility**: public (`@[simp]`)
- **Lines**: 56–57, proof length: 1
- **Notes**: simp lemma.

---

### `instance legendreCurve_isCharNeTwoNF`
- **Type**: `(l : F) : (legendreCurve l).IsCharNeTwoNF`
- **What**: Witnesses that the Legendre curve already satisfies the char ≠ 2 normal form conditions (`a₁=0, a₃=0`).
- **How**: Constructor `⟨rfl, rfl⟩`; the two conditions hold by `rfl`.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`
- **Used by**: unused in file (exported for external use)
- **Visibility**: public
- **Lines**: 59–60, proof length: 1
- **Notes**: Provides `IsCharNeTwoNF` instance; unused inside this file.

---

### `theorem legendreCurve_Δ`
- **Type**: `(l : F) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2`
- **What**: Computes the discriminant of the Legendre curve explicitly.
- **How**: `simp only [Δ_of_isCharNeTwoNF, legendreCurve_a₂, legendreCurve_a₄, legendreCurve_a₆]` then `ring`. Uses the mathlib lemma `Δ_of_isCharNeTwoNF` which gives `Δ` in terms of `a₂, a₄, a₆` for a curve in char ≠ 2 NF.
- **Hypotheses**: `F` a field.
- **Uses from project**: `legendreCurve`, `legendreCurve_a₂`, `legendreCurve_a₄`, `legendreCurve_a₆`
- **Used by**: `legendreCurve_Δ_ne_zero_iff`
- **Visibility**: public
- **Lines**: 63–66, proof length: 3
- **Notes**: None.

---

### `theorem legendreCurve_Δ_ne_zero_iff`
- **Type**: `[NeZero (2 : F)] (l : F) : (legendreCurve l).Δ ≠ 0 ↔ l ≠ 0 ∧ l ≠ 1`
- **What**: Characterises when the Legendre curve is non-singular: exactly when `l ≠ 0` and `l ≠ 1`.
- **How**: Rewrites using `legendreCurve_Δ`, then separately proves `16 ≠ 0` in char ≠ 2 (via `2^4`), and handles each direction by `mul_ne_zero` / `pow_ne_zero` / contradiction.
- **Hypotheses**: `F` a field of characteristic ≠ 2 (witnessed by `[NeZero (2 : F)]`).
- **Uses from project**: `legendreCurve_Δ`
- **Used by**: unused in file (exported as the main non-singularity criterion)
- **Visibility**: public
- **Lines**: 69–81, proof length: 12
- **Notes**: None.

---

### `private theorem exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero`
- **Type**: `(W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharNeTwoNF] (ha₆ : W.a₆ = 0) : ∃ l, l ≠ 0 ∧ l ≠ 1 ∧ ∃ C : VariableChange F, (C • W).IsElliptic ∧ C • W = legendreCurve l`
- **What**: Core helper: given a char ≠ 2 NF elliptic curve with constant term `a₆=0` (so `Y²=X³+a₂X²+a₄X`), produces a Legendre parameter `l` and a variable change putting the curve in Legendre form. This implements the second half of Silverman III.1.7.
- **How**: Uses `IsAlgClosed.exists_root` to extract a root `e₂` of the quadratic `X²+a₂X+a₄` (= the factored RHS), sets `e₃=−a₂−e₂`, forms `l=e₃/e₂`. Then uses `IsAlgClosed.exists_eq_mul_self` to extract `u` with `u²=e₂`, forms the variable change `C₂=⟨u,0,0,0⟩`, and verifies all five `a_i` fields of `C₂•W` equal those of `legendreCurve l` using `ha₁, ha₃` (the NF conditions) plus `linear_combination`, `field_simp`, `ring`. Non-singularity of `C₂•W` is deduced from `variableChange_Δ` and `W.isUnit_Δ`.
- **Hypotheses**: `F` algebraically closed, `W` a char ≠ 2 NF elliptic curve with `a₆=0`. Note the `[IsAlgClosed F]` instance is inherited from the outer section, but `[NeZero (2 : F)]` is `omit`-ted via `omit [NeZero (2 : F)] in`.
- **Uses from project**: `legendreCurve`, `legendreCurve_a₁` (via simp/ring), `legendreCurve_a₃` (via simp/ring)
- **Used by**: `exists_legendreCurve_iso`
- **Visibility**: private
- **Lines**: 92–154, proof length: 63
- **Notes**: Proof > 30 lines. Structured manipulation of variable changes for the Weierstrass model.

---

### `theorem exists_legendreCurve_iso`
- **Type**: `(E : WeierstrassCurve F) [E.IsElliptic] : ∃ l, l ≠ 0 ∧ l ≠ 1 ∧ ∃ C : VariableChange F, (C • E).IsElliptic ∧ C • E = legendreCurve l`
- **What**: Every elliptic curve over an algebraically closed field of characteristic ≠ 2 is isomorphic (via a variable change) to a Legendre curve. This is Silverman III.1.7.
- **How**: (1) Converts `E` to char ≠ 2 NF via `E.toCharNeTwoNF` (mathlib). (2) Uses `IsAlgClosed.exists_root` to find a root `e₁` of the cubic `X³+a₂X²+a₄X+a₆`, then translates `X↦X+e₁` via `⟨1,e₁,0,0⟩` to kill the constant term. (3) Applies the private helper `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero`. (4) Reassembles the composed variable change `C₂ * ⟨1,e₁,0,0⟩ * E.toCharNeTwoNF` using `mul_smul`.
- **Hypotheses**: `F` algebraically closed of characteristic ≠ 2.
- **Uses from project**: `legendreCurve`, `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero`
- **Used by**: unused in file (main exported result)
- **Visibility**: public
- **Lines**: 164–203, proof length: 40
- **Notes**: Proof > 30 lines. Main theorem, corresponds to Silverman III.1.7.

---

## Summary

| Declaration | Kind | Lines |
|---|---|---|
| `legendreCurve` | def | 41–42 |
| `legendreCurve_a₁` | theorem | 44–45 |
| `legendreCurve_a₂` | theorem | 47–48 |
| `legendreCurve_a₃` | theorem | 50–51 |
| `legendreCurve_a₄` | theorem | 53–54 |
| `legendreCurve_a₆` | theorem | 56–57 |
| `legendreCurve_isCharNeTwoNF` | instance | 59–60 |
| `legendreCurve_Δ` | theorem | 63–66 |
| `legendreCurve_Δ_ne_zero_iff` | theorem | 69–81 |
| `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero` | theorem (private) | 92–154 |
| `exists_legendreCurve_iso` | theorem | 164–203 |

**Total declarations**: 11 (1 def, 9 theorems, 1 instance)

**No `sorry`s. No `set_option maxHeartbeats`.**

**Key API** (used by 3+ others in file): `legendreCurve` (used by 10 declarations).

**Unused in file** (dead-code candidates for this file; all likely used externally): `legendreCurve_isCharNeTwoNF`, `legendreCurve_Δ_ne_zero_iff`, `exists_legendreCurve_iso`.

**Long proofs (>30 lines)**: `exists_legendreCurve_of_charNeTwoNF_a₆_eq_zero` (~63 lines), `exists_legendreCurve_iso` (~40 lines).
