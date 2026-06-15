# Inventory: ./HasseWeil/WeilPairing/PairingAdjoint.lean

**File**: `HasseWeil/WeilPairing/PairingAdjoint.lean`
**Imports**: `HasseWeil.WeilPairing.PairingProps`, `HasseWeil.Pic0.PicDual`
**Namespace**: `HasseWeil.WeilPairing`
**Total declarations**: 7 (all theorems, 0 defs, 0 instances)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Section `SecondSlot` — Bilinearity in the second slot

---

### `theorem weilPairing_congr_right`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) {S T T' : W.toAffine.Point} (hS : ℓ • S = 0) (hT : ℓ • T = 0) (hT' : ℓ • T' = 0) (h : T = T') → weilPairing W ℓ hℓ S T hS hT = weilPairing W ℓ hℓ S T' hS hT'`
- **What**: The Weil pairing value `e_ℓ(S, T)` is independent of which proof of `ℓ • T = 0` is used; equal second arguments give equal pairing values.
- **How**: Pure proof irrelevance — `subst h; rfl` suffices since after substituting `T' = T` the two expressions are definitionally equal.
- **Hypotheses**: `F` algebraically closed, `W` an elliptic curve, `ℓ • T = 0`.
- **Uses from project**: `weilPairing` (from `PairingProps`).
- **Used by**: `weilPairing_refl_right` (L103), `weilPairing_nsmul_right` (L121, L127), `weilPairing_scaling` (L287).
- **Visibility**: public
- **Lines**: 89–93; proof length: 1 line
- **Notes**: None.

---

### `theorem weilPairing_refl_right`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S : W.toAffine.Point) (hS : ℓ • S = 0) (h0 : ℓ • (0 : W.toAffine.Point) = 0) → weilPairing W ℓ hℓ S 0 hS h0 = 1`
- **What**: The Weil pairing is trivial in the second slot at the identity: `e_ℓ(S, O) = 1`.
- **How**: Uses slot-2 bilinearity `weilPairing_mul_right` with `T₁ = T₂ = O` to get `e_ℓ(S,O) = e_ℓ(S,O)·e_ℓ(S,O)`, then cancels using `weilPairing_ne_zero` and `mul_right_cancel₀`.
- **Hypotheses**: `F` algebraically closed.
- **Uses from project**: `weilPairing_mul_right` (PairingProps), `weilPairing_ne_zero` (PairingProps), `weilPairing_congr_right` (this file).
- **Used by**: `weilPairing_nsmul_right` (L123).
- **Visibility**: public
- **Lines**: 98–106; proof length: 7 lines
- **Notes**: None.

---

### `theorem smul_nsmul_eq_zero_right`

- **Type**: `(ℓ : ℤ) (T : W.toAffine.Point) (hT : ℓ • T = 0) (n : ℕ) → ℓ • (n • T) = 0`
- **What**: Torsion closure under natural-number scalar multiples: if `ℓ • T = 0` then `ℓ • (n • T) = 0` for all `n : ℕ` (the scalars commute).
- **How**: `rw [smul_comm, hT, smul_zero]` — rewriting with commutativity of integer and natural scalar actions.
- **Hypotheses**: `ℓ • T = 0`.
- **Uses from project**: none (pure `smul_comm` / `smul_zero` from mathlib).
- **Used by**: `weilPairing_nsmul_right` (L125), `weilPairing_scaling` (L285).
- **Visibility**: public
- **Lines**: 109–111; proof length: 1 line
- **Notes**: None.

---

### `theorem weilPairing_nsmul_right`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) (n : ℕ) (h_ns : ℓ • (n • T) = 0) → weilPairing W ℓ hℓ S (n • T) hS h_ns = (weilPairing W ℓ hℓ S T hS hT) ^ n`
- **What**: Power form of second-slot bilinearity: `e_ℓ(S, n • T) = e_ℓ(S, T)^n` for `n : ℕ`.
- **How**: Induction on `n`; base via `weilPairing_refl_right` (after `congr_right`); inductive step rewrites `succ_nsmul`, applies `weilPairing_mul_right` (slot-2 bilinearity), the IH, and `pow_succ`.
- **Hypotheses**: `F` algebraically closed.
- **Uses from project**: `weilPairing_congr_right` (this file), `weilPairing_refl_right` (this file), `smul_nsmul_eq_zero_right` (this file), `weilPairing_mul_right` (PairingProps).
- **Used by**: `weilPairing_scaling` (L290).
- **Visibility**: public
- **Lines**: 115–128; proof length: 13 lines
- **Notes**: None.

---

## Section `Adjoint` — The separable adjoint (Silverman III.8.2)

---

### `theorem weilPairing_adjoint_core`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (φ : Isogeny W.toAffine W.toAffine) (S T U : W.toAffine.Point) (hS hT hU : ...) (hφS : ℓ • φ.toAddMonoidHom S = 0) (hcomm : translateAlgEquivOfPoint W S (φ.pullback gT) = φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S) gT)) {c : F} {k : KE} (hfact : φ.pullback gT = algebraMap F KE c * (gU * (mulByInt W.toAffine ℓ).pullback k)) → weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT = weilPairing W ℓ hℓ S U hS hU`
- **What**: The core separable adjoint: given translation covariance (`hcomm`) and a divisor factorisation (`hfact`) of `φ^* g_T`, proves `e_ℓ(φS, T) = e_ℓ(S, U)` (the abstract version with `U` standing in for `φ̂T`).
- **How**: Evaluates `τ_S^*(φ^* g_T)` two ways: via `hcomm` + `weilPairing_translate` (evaluation 1 = `e_ℓ(φS,T) · φ^* g_T`) and via `hfact` + `translate_pullback_fixed` + `weilPairing_translate` (evaluation 2 = `e_ℓ(S,U) · φ^* g_T`). Cancels the common factor `φ^* g_T ≠ 0` (using `φ.pullback_injective` + `weilFunction_ne_zero`) and injects via `(algebraMap F KE).injective`.
- **Hypotheses**: `F` algebraically closed, the two geometric witnesses `hcomm` and `hfact` must be supplied per isogeny.
- **Uses from project**: `weilFunction_ne_zero` (PairingProps), `weilFunction` (PairingProps), `Isogeny.pullback_injective`, `weilPairing_translate` (PairingProps), `translate_pullback_fixed` (PairingProps), `translateAlgEquivOfPoint`, `mulByInt`, `weilPairing` (PairingProps).
- **Used by**: `weilPairing_adjoint_picDual` (L229), and directly by external files (`SeparableScaling.lean`, `FrobeniusGalois.lean`, `HfactLemma.lean`).
- **Visibility**: public
- **Lines**: 163–200; proof length: 37 lines
- **Notes**: Proof exceeds 30 lines (37 lines). This is the key reusable engine consumed by all adjoint/scaling results in the project.

---

### `theorem weilPairing_adjoint_picDual`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (φ : Isogeny W.toAffine W.toAffine) (ch : φ.CoordHom) (hinj : Function.Injective ch.toAlgHom) (hfin : ...) (S T : W.toAffine.Point) (hS hT : ...) (hφS : ...) (hcomm : ...) {c : F} {k : KE} (hfact : ...) → weilPairing W ℓ hℓ (φ.toAddMonoidHom S) T hφS hT = weilPairing W ℓ hℓ S ((φ.picDual ch hinj hfin) T) hS (...)`
- **What**: The separable adjoint instantiated with `picDual`: `e_ℓ(φS, T) = e_ℓ(S, φ̂T)` where `φ̂ = picDual φ`, for a separable isogeny with `CoordHom` data.
- **How**: Directly applies `weilPairing_adjoint_core` with `U := (φ.picDual ch hinj hfin) T`; the torsion condition on `φ̂T` is discharged by `map_zsmul + hT + map_zero` (using that `picDual φ` is a group hom).
- **Hypotheses**: Same as `weilPairing_adjoint_core` plus `CoordHom` data (`ch`, `hinj`, `hfin`) for the `picDual`.
- **Uses from project**: `weilPairing_adjoint_core` (this file), `Isogeny.picDual` (PicDual).
- **Used by**: `weilPairing_scaling` (L282), and externally by `HfactLemma.lean`.
- **Visibility**: public
- **Lines**: 212–230; proof length: 1 line (term-mode)
- **Notes**: Thin wrapper over `weilPairing_adjoint_core` — main value is fixing `U := picDual φ T` and discharging the torsion side condition.

---

## Section `Scaling` — The symplectic scaling (Silverman III.8.6.1)

---

### `theorem weilPairing_scaling`

- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (φ : Isogeny W.toAffine W.toAffine) (ch : φ.CoordHom) (hinj : ...) (hfin : ...) (S T : W.toAffine.Point) (hS hT hφS hφT : ...) (hcomm : ...) {c : F} {k : KE} (hfact : ...) (hdual : ∀ P, (φ.picDual ch hinj hfin) (φ.toAddMonoidHom P) = (φ.degree : ℤ) • P) → weilPairing W ℓ hℓ (φ.toAddMonoidHom S) (φ.toAddMonoidHom T) hφS hφT = weilPairing W ℓ hℓ S T hS hT ^ φ.degree`
- **What**: The symplectic scaling of the Weil pairing: `e_ℓ(φS, φT) = e_ℓ(S, T)^(deg φ)`, the per-isogeny identity that forces `det(φ|E[ℓ]) = deg φ`.
- **How**: Three steps: (1) apply `weilPairing_adjoint_picDual` at `T := φT` to get `e_ℓ(φS, φT) = e_ℓ(S, φ̂(φT))`; (2) rewrite `φ̂(φT) = (deg φ)·T` using `hdual` + `natCast_zsmul`, via `weilPairing_congr_right`; (3) apply `weilPairing_nsmul_right` (the `ℕ`-smul power law).
- **Hypotheses**: `F` algebraically closed, `CoordHom` data, geometric witnesses `hcomm` and `hfact` (adjoint witnesses at `φT`), and the dual relation `hdual : picDual φ (φ P) = (deg φ : ℤ) • P`.
- **Uses from project**: `weilPairing_adjoint_picDual` (this file), `weilPairing_congr_right` (this file), `smul_nsmul_eq_zero_right` (this file), `weilPairing_nsmul_right` (this file), `natCast_zsmul`.
- **Used by**: unused in this file; consumed externally (see `SeparableScaling.lean`, `FrobMatrixData.lean`, `HasseAssembly.lean`).
- **Visibility**: public
- **Lines**: 258–290; proof length: 32 lines
- **Notes**: Proof is just over 30 lines (32 lines). Consumes `sorryAx` transitively via `weilPairing_mul_right` (slot-2 bilinearity, upstream sorry in `DivisorPullback`) — not from this file itself.

---

## Cross-reference summary

### Key API from this file (used by 3+ other declarations in this file)

- `weilPairing_congr_right` — used by `weilPairing_refl_right`, `weilPairing_nsmul_right`, `weilPairing_scaling` (3 callers)
- `smul_nsmul_eq_zero_right` — used by `weilPairing_nsmul_right`, `weilPairing_scaling` (2 callers in file); note also used 3+ times externally
- `weilPairing_adjoint_core` — used by `weilPairing_adjoint_picDual`, `weilPairing_scaling` (indirectly via picDual wrapper); extensively used externally

### Declarations unused within this file (dead-code candidates within file; all used externally)

- `weilPairing_congr_right` — used within file (3 callers above), and externally by `FrobeniusGalois.lean`, `SeparableScaling.lean`
- `weilPairing_refl_right` — used within file by `weilPairing_nsmul_right`
- `smul_nsmul_eq_zero_right` — used within file and externally by `FrobeniusGalois.lean`, `SeparableScaling.lean`
- `weilPairing_nsmul_right` — used within file by `weilPairing_scaling`, and externally by `SeparableScaling.lean`, `FrobeniusGalois.lean`
- `weilPairing_adjoint_core` — used within file by `weilPairing_adjoint_picDual`, externally by `SeparableScaling.lean` (multiple), `FrobeniusGalois.lean`, `HfactLemma.lean`
- `weilPairing_adjoint_picDual` — used within file by `weilPairing_scaling`, externally by `HfactLemma.lean`
- `weilPairing_scaling` — NOT used within this file; consumed externally by `SeparableScaling.lean` (docstring/comments), `FrobMatrixData.lean`, `HasseAssembly.lean`, `DetDeg.lean`

### Declarations not referenced by anything else in this file

- `weilPairing_scaling` (leaf declaration — its callers are all in other files)
