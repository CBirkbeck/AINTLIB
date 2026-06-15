# Inventory: ./HasseWeil/WeilPairing/Constancy.lean

File: `HasseWeil/WeilPairing/Constancy.lean`
Lines: 193
Module: `HasseWeil.WeilPairing` (namespace `HasseWeil.WeilPairing`)
Imports: `HasseWeil.Curves.ProjectiveDivisor`, `HasseWeil.Curves.NoFinitePolesBridge`, `HasseWeil.Curves.Divisors`

**Purpose.** Ships the "constant-function" step of the Weil pairing construction: a function on a
projective elliptic curve with trivial divisor is a scalar (algebraic Liouville / Silverman II.1.2),
and derives from it the pairing-value scalar `c`, the `μ_ℓ` membership, and the bilinearity engines.

---

## Declarations

### `theorem const_of_projectiveDivisorOf_eq_zero`
- **Type**: `[IsAlgClosed F] [W.IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] (f : FF) (hf : f ≠ 0) (hdiv : CR.projectiveDivisorOf f = 0) : ∃ c : F, f = algebraMap F FF c`
  where `CR = (⟨W⟩ : SmoothPlaneCurve F).CoordinateRing`, `FF = ...FunctionField`.
- **What**: If a nonzero element of the function field of an elliptic curve over an algebraically closed field has trivial projective divisor (no zeros or poles, including at infinity), it is a constant (in the base field `F`). This is the projective Liouville theorem, Silverman II.1.2.
- **How**: Uses `projectiveDivisorOf_apply_affine` and `projectiveDivisorOf_apply_infinity` to convert the zero-divisor hypothesis into `ord_P f ≥ 0` at every smooth point and `ordAtInfty f ≥ 0`. Then applies `const_of_valuation_le_one_of_ordAtInfty_nonneg` (algebraic Liouville); surjectivity `smoothPointToHeightOne_surjective` covers all height-1 primes; `pointValuation_eq_heightOneValuation` identifies the point valuation with the height-1 valuation; `pointValuation_le_one_of_ord_nonneg` finishes.
- **Hypotheses**: `F` algebraically closed, `W` elliptic, coordinate ring Dedekind and integrally closed, `f ≠ 0`, trivial projective divisor.
- **Uses from project**: `projectiveDivisorOf_apply_affine`, `projectiveDivisorOf_apply_infinity`, `ord_P_eq_top_iff`, `ordAtInfty_eq_top_iff`, `const_of_valuation_le_one_of_ordAtInfty_nonneg`, `smoothPointToHeightOne_surjective`, `pointValuation_eq_heightOneValuation`, `pointValuation_le_one_of_ord_nonneg`
- **Used by**: `const_unit_of_projectiveDivisorOf_eq_zero` (this file); also used heavily in `PairingProps.lean`, `HfactLemma.lean`, `SeparableScaling.lean`, `FrobeniusDivisorGalois.lean` (other files)
- **Visibility**: public
- **Lines**: 35–66, proof ~27 lines (L41–L66)
- **Notes**: `set_option maxHeartbeats 1600000` on this declaration (comment: "The `(⟨W⟩ : SmoothPlaneCurve F)` curve coercion makes instance/`whnf` elaboration heavy."). Proof is just under 30 lines.

---

### `theorem const_unit_of_projectiveDivisorOf_eq_zero`
- **Type**: `[IsAlgClosed F] [W.IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] (f : FF) (hf : f ≠ 0) (hdiv : CR.projectiveDivisorOf f = 0) : ∃ c : F, c ≠ 0 ∧ f = algebraMap F FF c`
- **What**: Refines `const_of_projectiveDivisorOf_eq_zero` to produce a **nonzero** scalar: if `f` has trivial divisor and is nonzero, the constant `c` satisfies `c ≠ 0`.
- **How**: Calls `const_of_projectiveDivisorOf_eq_zero` to obtain `c`, then shows `c ≠ 0` by contradiction: `c = 0` would give `f = algebraMap 0 = 0`, contradicting `hf`.
- **Hypotheses**: Same as `const_of_projectiveDivisorOf_eq_zero`.
- **Uses from project**: `const_of_projectiveDivisorOf_eq_zero` (this file)
- **Used by**: `pairing_const_of_transport` (this file); heavily used across `HfactLemma.lean`, `SeparableScaling.lean`, `FrobeniusDivisorGalois.lean`, `PairingProps.lean`
- **Visibility**: public
- **Lines**: 72–82, proof ~5 lines
- **Notes**: Simple wrapper/refinement. The most widely-used export of this file across the project.

---

### `theorem pairing_const_of_transport`
- **Type**: `[IsAlgClosed F] [W.IsElliptic] [IsDedekindDomain CR] [IsIntegrallyClosed CR] (τ : FF ≃+* FF) (g : FF) (hg : g ≠ 0) (htransport : projectiveDivisorOf (τ g / g) = 0) : ∃ c : F, c ≠ 0 ∧ τ g = algebraMap F FF c * g`
- **What**: The key pairing step: if an automorphism `τ` of the function field (e.g., translation by `S ∈ E[ℓ]`) satisfies `div(τg/g) = 0`, then `τg = c·g` for a nonzero scalar `c`. This is the Weil pairing value `e_ℓ(S,T) = c`.
- **How**: Notes `τg ≠ 0` from injectivity; applies `const_unit_of_projectiveDivisorOf_eq_zero` to `τg/g`; converts `c = τg/g` to `τg = c·g` via `div_eq_iff`.
- **Hypotheses**: Same algebraic-closed/elliptic/Dedekind/integrally-closed hypotheses; `g ≠ 0`; transport hypothesis `div(τg/g) = 0`.
- **Uses from project**: `const_unit_of_projectiveDivisorOf_eq_zero` (this file)
- **Used by**: unused within this file; used in `Pairing.lean` (definition of `weilPairing`) and referenced/documented in `DivisorTranslate.lean`
- **Visibility**: public
- **Lines**: 89–100, proof ~4 lines
- **Notes**: Core bridge to `Pairing.lean`. No `sorry`.

---

### `theorem pairing_const_pow_eq_one`
- **Type**: `(τ : FF ≃+* FF) (g : FF) (hg : g ≠ 0) (ℓ : ℕ) {c : F} (hc : τ g = algebraMap F FF c * g) (hfix : τ (g ^ ℓ) = g ^ ℓ) : c ^ ℓ = 1`
- **What**: If `τg = c·g` and `τ` fixes `g^ℓ`, then `c^ℓ = 1`. This is the `μ_ℓ`-membership step of the Weil pairing: `e_ℓ(S,T)` is an `ℓ`-th root of unity, using the fact that `g^ℓ = f_T ∘ [ℓ]` is fixed by `τ_S` when `ℓ·S = O`.
- **How**: Computes `τ(g^ℓ) = (τg)^ℓ = (c·g)^ℓ = c^ℓ·g^ℓ` via `map_pow`; since `hfix` says `τ(g^ℓ) = g^ℓ`, we get `g^ℓ = c^ℓ·g^ℓ`; cancels `g^ℓ ≠ 0` via `mul_right_cancel₀`; injectivity of `algebraMap` gives `c^ℓ = 1`.
- **Hypotheses**: `g ≠ 0`, pairing relation `τg = c·g`, and the fix-condition `τ(g^ℓ) = g^ℓ`.
- **Uses from project**: none (uses only mathlib: `map_pow`, `mul_right_cancel₀`, `algebraMap.injective`)
- **Used by**: unused within this file; used in `Pairing.lean` (noted in MEMORY)
- **Visibility**: public
- **Lines**: 106–124, proof ~13 lines
- **Notes**: No `sorry`. Does not require the algebraically-closed/Dedekind hypotheses — fully general. This lemma is now superseded in `Pairing.lean` by the bilinearity route (the MEMORY notes `pairing_const_pow_eq_one` in Constancy is kept but `weilPairing_pow_eq_one` now uses a different route).

---

### `theorem pairing_const_mul`
- **Type**: `(τ₁ τ₂ τ₁₂ : FF ≃+* FF) (g : FF) (hg : g ≠ 0) {c₁ c₂ c₁₂ : F} (hτ₁F : τ₁ fixes algebraMap scalars) (hcomp : τ₁₂ = τ₁ ∘ τ₂) (hc₁ : τ₁ g = c₁·g) (hc₂ : τ₂ g = c₂·g) (hc₁₂ : τ₁₂ g = c₁₂·g) : c₁₂ = c₁ * c₂`
- **What**: If translations compose (`τ_{S₁+S₂} = τ_{S₁} ∘ τ_{S₂}`) and the individual pairing scalars are `c₁, c₂`, the composed scalar is `c₁₂ = c₁·c₂`. This is the first-slot bilinearity engine.
- **How**: Computes `τ₁₂ g = τ₁(τ₂ g) = τ₁(c₂·g) = c₂·τ₁(g) = c₂·c₁·g` (using that `τ₁` fixes scalar `c₂ ∈ F`); equates with `c₁₂·g` and cancels `g ≠ 0` + injectivity of `algebraMap`.
- **Hypotheses**: `g ≠ 0`, three pairing scalar relations, composition identity for the automorphisms, `τ₁` fixes `F`-scalars.
- **Uses from project**: none (pure ring arithmetic)
- **Used by**: unused within this file; used in `Pairing.lean` (`weilPairing_mul_left`)
- **Visibility**: public
- **Lines**: 130–146, proof ~7 lines
- **Notes**: No `sorry`. Parametric — takes three *separate* automorphisms, making it reusable for any translation-like action.

---

### `theorem pairing_const_mul_invariant_factor`
- **Type**: `(τ : FF ≃+* FF) (g₁ g₂ g₁₂ u : FF) (hg₁₂ : g₁₂ ≠ 0) {c c₁ c₂ c₁₂ : F} (hτF : τ fixes F-scalars) (hτu : τ u = u) (hfact : g₁₂ = c·(g₁·g₂·u)) (hc₁ : τ g₁ = c₁·g₁) (hc₂ : τ g₂ = c₂·g₂) (hc₁₂ : τ g₁₂ = c₁₂·g₁₂) : c₁₂ = c₁ * c₂`
- **What**: Second-slot bilinearity engine: given three Weil functions `g₁ = g_{T₁}`, `g₂ = g_{T₂}`, `g₁₂ = g_{T₁+T₂}` related by a divisor-pullback factorization `g₁₂ = c·g₁·g₂·u` (where `u` is a covariant factor fixed by `τ`), the pairing value for `T₁+T₂` equals the product of those for `T₁` and `T₂`.
- **How**: Applies `τ` to the factorization `hfact`, substitutes the scalar relations `hc₁, hc₂` and `hτu`/`hτF` to get `τ g₁₂ = (c₁·c₂)·g₁₂`; equates with `hc₁₂`; cancels `g₁₂ ≠ 0` + injectivity of `algebraMap`.
- **Hypotheses**: `g₁₂ ≠ 0`, factorization identity, `τ` fixes `F`-scalars, `τ` fixes `u`, three scalar relations.
- **Uses from project**: none (pure ring arithmetic)
- **Used by**: unused within this file; used in `PairingProps.lean` (`weilPairing_mul_right`)
- **Visibility**: public
- **Lines**: 157–178, proof ~9 lines
- **Notes**: No `sorry`. This is the slot-2 counterpart of `pairing_const_mul`, covering the harder case where the three functions are different (depending on the second argument `T`).

---

### `theorem pairing_const_refl`
- **Type**: `(g : FF) (hg : g ≠ 0) {c : F} (hc : g = algebraMap F FF c * g) : c = 1`
- **What**: If `g = c·g` (i.e., `τ_O g = g` for translation by `O = identity`), then `c = 1`. This is the `e_ℓ(O,T) = 1` triviality step.
- **How**: Rewrites `1·g = c·g` and cancels `g ≠ 0` via `mul_right_cancel₀`; injectivity of `algebraMap` gives `c = 1`.
- **Hypotheses**: `g ≠ 0`, scalar relation `g = c·g`.
- **Uses from project**: none
- **Used by**: unused within this file; used in `Pairing.lean` (`weilPairing_refl_left`) and `PairingProps.lean`
- **Visibility**: public
- **Lines**: 183–191, proof ~5 lines
- **Notes**: No `sorry`. Fully general (no algebraically-closed/elliptic hypotheses).

---

## Cross-file usage summary

| Declaration | Used by (other files) |
|---|---|
| `const_of_projectiveDivisorOf_eq_zero` | `PairingProps.lean`, (via `const_unit_...`) |
| `const_unit_of_projectiveDivisorOf_eq_zero` | `HfactLemma.lean` (×2), `FrobeniusDivisorGalois.lean`, `PairingProps.lean` (×2), `SeparableScaling.lean` (×3) |
| `pairing_const_of_transport` | `Pairing.lean` (×2), `DivisorTranslate.lean` (documented) |
| `pairing_const_pow_eq_one` | `Pairing.lean` (historical; now superseded by bilinearity route) |
| `pairing_const_mul` | `Pairing.lean` (`weilPairing_mul_left`) |
| `pairing_const_mul_invariant_factor` | `PairingProps.lean` (`weilPairing_mul_right`) |
| `pairing_const_refl` | `Pairing.lean` (`weilPairing_refl_left`), `PairingProps.lean` |

## File-level notes

- `set_option maxHeartbeats 1600000` applies to `const_of_projectiveDivisorOf_eq_zero` only (with explanatory comment about `SmoothPlaneCurve` coercion whnf overhead).
- `set_option linter.unusedSectionVars false`, `linter.unusedDecidableInType false`, `linter.style.longLine false` are set globally in the file (not per declaration).
- No `sorry` in any declaration body.
- No proofs exceed 30 lines.
- The file has 7 declarations, all theorems (no defs, no instances, no abbreviations).
- `const_unit_of_projectiveDivisorOf_eq_zero` is the most widely used export (6+ call sites across the project).
- `pairing_const_pow_eq_one` may be dead code within `Pairing.lean`'s current proof strategy (the MEMORY notes the bilinearity route now drives `weilPairing_pow_eq_one` instead), but it is kept.
