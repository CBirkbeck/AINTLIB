# Inventory: ./HasseWeil/EC/MulByIntComp.lean

**File**: `HasseWeil/EC/MulByIntComp.lean`
**Import**: `HasseWeil.EC.MulByIntBaseCase`
**Total declarations**: 11 (all theorems)
**Sorries**: none
**`set_option maxHeartbeats`**: none

---

## Overview

This file develops the composition law for multiplication-by-integer isogenies,
`[m].comp [n] = [m*n]`, targeting Silverman III.4.2. It handles identity cases
unconditionally, provides a witness-parametric form for the general case
(reducing to a pullback identity on generators), and proves the `[-1]` case
of the x-coordinate composition identity as a concrete instance.

---

## Declarations

---

### `theorem mulByInt_comp_mulByInt_one_right`

- **Type**: `(m : ℤ) : (mulByInt W.toAffine m).comp (mulByInt W.toAffine 1) = mulByInt W.toAffine m`
- **What**: Proves `[m] ∘ [1] = [m]` as isogenies: composing any `[m]` with the identity isogeny `[1]` on the right gives back `[m]`.
- **How**: Unfolds `Isogeny.comp` to its constructor `Isogeny.mk`, then rewrites the pullback component using `mulByInt_one_pullback_eq_id` (so `[1].pullback = id`) and `AlgHom.id_comp`, and the hom component by unfolding scalar multiplication to reduce to `simp`.
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (from `MulByIntBaseCase`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 51–65, proof body ~13 lines
- **Notes**: None notable.

---

### `theorem mulByInt_one_comp_mulByInt_left`

- **Type**: `(m : ℤ) : (mulByInt W.toAffine 1).comp (mulByInt W.toAffine m) = mulByInt W.toAffine m`
- **What**: Proves `[1] ∘ [m] = [m]` as isogenies: composing the identity isogeny `[1]` on the left with `[m]` gives `[m]`.
- **How**: Same structure as `mulByInt_comp_mulByInt_one_right`, using `mulByInt_one_pullback_eq_id` with `AlgHom.comp_id` (right identity this time) and `simp` for the hom component.
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (from `MulByIntBaseCase`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 69–83, proof body ~13 lines
- **Notes**: Parallel structure to `mulByInt_comp_mulByInt_one_right`; the two could be merged but are kept separate for clarity.

---

### `theorem mulByInt_comp_toAddMonoidHom`

- **Type**: `(m n : ℤ) : ((mulByInt W.toAffine m).comp (mulByInt W.toAffine n)).toAddMonoidHom = (mulByInt W.toAffine (m * n)).toAddMonoidHom`
- **What**: The point-level composition of `[m]` and `[n]` equals `[m*n]` at the additive group level: `m•(n•P) = (m*n)•P` for all points `P`.
- **How**: Reduces by `ext P` to the scalar-multiplication identity `m•(n•P) = (m*n)•P`, which is `← mul_smul` in Lean.
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: none (pure mathlib `mul_smul`).
- **Used by**: `mulByInt_comp_eq_mul_of_pullback_witness` (line 113).
- **Visibility**: public
- **Lines**: 89–94, proof body ~3 lines
- **Notes**: Unconditional; the easiest result in the file.

---

### `theorem mulByInt_comp_eq_mul_of_pullback_witness`

- **Type**: `(m n : ℤ) (h_pb : (mulByInt W.toAffine n).pullback.comp (mulByInt W.toAffine m).pullback = (mulByInt W.toAffine (m * n)).pullback) : (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) = mulByInt W.toAffine (m * n)`
- **What**: Given the pullback-level composition identity as a hypothesis, concludes the full isogeny equality `[m] ∘ [n] = [m*n]`. This is the main witness-parametric reduction: the hard pullback identity is separated from the assembly.
- **How**: Unfolds `Isogeny.comp` constructor, applies `mulByInt_comp_toAddMonoidHom` for the hom half, then rewrites with the hypothesis `h_pb` and the hom identity.
- **Hypotheses**: `W` an elliptic curve; the pullback-composition identity `h_pb`.
- **Uses from project**: `mulByInt_comp_toAddMonoidHom` (this file, line 113).
- **Used by**: `mulByInt_comp_eq_mul_of_generator_witness` (line 144).
- **Visibility**: public
- **Lines**: 107–117, proof body ~6 lines
- **Notes**: Main API result; the hypothesis `h_pb` is discharged by T-III-4-020b in downstream work.

---

### `theorem mulByInt_comp_eq_mul_of_generator_witness`

- **Type**: `(m n : ℤ) (_hm : m ≠ 0) (_hn : n ≠ 0) (hmn : m * n ≠ 0) (h_x : ...) (h_y : ...) : (mulByInt W.toAffine m).comp (mulByInt W.toAffine n) = mulByInt W.toAffine (m * n)`
- **What**: Given that the composed pullback sends `x_gen` to `mulByInt_x W (m*n)` and `y_gen` to `mulByInt_y W (m*n)`, concludes the full isogeny equality. This reduces the isogeny equality to generator-level data.
- **How**: Applies `mulByInt_comp_eq_mul_of_pullback_witness` after using `mulByInt_pullback_unique` (from `MulByIntBaseCase`) to promote the generator witnesses to a full pullback identity.
- **Hypotheses**: `W` an elliptic curve; `m, n, m*n ≠ 0`; the two generator witnesses `h_x`, `h_y`.
- **Uses from project**: `mulByInt_comp_eq_mul_of_pullback_witness` (this file), `mulByInt_pullback_unique` (from `MulByIntBaseCase`).
- **Used by**: Used by `GenericPointZsmul.lean` (external); unused in this file.
- **Visibility**: public
- **Lines**: 134–146, proof body ~4 lines
- **Notes**: The two hypotheses `_hm` and `_hn` are named with leading underscore, suggesting they may actually only be used implicitly (they serve as side conditions for `mulByInt_pullback_unique`).

---

### `@[simp] theorem mulByInt_x_neg`

- **Type**: `(n : ℤ) : mulByInt_x W (-n) = mulByInt_x W n`
- **What**: The rational x-coordinate image of `[-n]` equals that of `[n]`: the division-polynomial ratio `Φ_n/ΨSq_n` is invariant under negation of `n`, reflecting the fact that `Φ(-n) = Φ(n)` and `ΨSq(-n) = ΨSq(n)`.
- **How**: Unfolds `mulByInt_x`, `Φ_ff`, `ΨSq_ff`, then applies `WeierstrassCurve.Φ_neg` and `WeierstrassCurve.ΨSq_neg` (mathlib division polynomial parity lemmas).
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: none (references `Φ_ff`, `ΨSq_ff` which are project-local definitions, and mathlib's `WeierstrassCurve.Φ_neg`, `ΨSq_neg`).
- **Used by**: `mulByInt_pullback_x_neg_one` (line 173), `mulByInt_comp_pullback_x_neg_one` (lines 190, 191). Heavily used externally (multiple files).
- **Visibility**: public, `@[simp]`
- **Lines**: 155–157, proof body ~2 lines
- **Notes**: Marked `@[simp]`; a key symmetry lemma used across many downstream files.

---

### `theorem mulByInt_pullback_x_neg_one`

- **Type**: `(mulByInt W.toAffine (-1)).pullback (x_gen W) = x_gen W`
- **What**: The `[-1]`-pullback fixes `x_gen`: pulling back the generic x-coordinate through `[-1]` gives `x_gen` itself.
- **How**: Applies `mulByInt_pullback_x` to reduce the pullback to `mulByInt_x W (-1)`, then uses `mulByInt_x_neg` to identify it as `mulByInt_x W 1`, then `mulByInt_x_one` to identify it as `x_gen`.
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: `mulByInt_pullback_x` (from `MulByIntBaseCase`), `mulByInt_x_neg` (this file), `mulByInt_x_one` (from `MulByIntBaseCase`).
- **Used by**: `mulByInt_comp_pullback_x_neg_one_neg_one` (line 223). Heavily used externally (multiple files including `Differential.lean`, `Frobenius.lean`).
- **Visibility**: public
- **Lines**: 168–174, proof body ~5 lines
- **Notes**: A core infrastructure lemma; highly referenced externally despite being only used once within this file.

---

### `theorem mulByInt_comp_pullback_x_neg_one`

- **Type**: `(n : ℤ) (hn : n ≠ 0) : (mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine n).pullback (x_gen W)) = mulByInt_x W (n * -1)`
- **What**: The composition of `[-1]`-pullback with `[n]`-pullback sends `x_gen` to `mulByInt_x W (n * -1)`: a concrete x-coordinate composition identity for the `[-1]·[n]` case.
- **How**: First computes the inner pullback via `mulByInt_pullback_x`, giving `mulByInt_x W n`. Then applies `mulByInt_pullback_mulByInt_x` with `m = -1` to compute the outer pullback as a `Φ`-`eval₂` expression, simplifies via `mulByInt_x_neg` and `mulByInt_x_one`. The tail of the proof establishes that `eval₂ (algebraMap F KE) (x_gen W) p = algebraMap (Polynomial F) KE p` via an `aeval`-algebraMap chain using `IsScalarTower.algebraMap_apply`.
- **Hypotheses**: `W` an elliptic curve over `F`; `n ≠ 0`.
- **Uses from project**: `mulByInt_pullback_x` (from `MulByIntBaseCase`), `mulByInt_pullback_mulByInt_x` (from `MulByIntBaseCase`), `mulByInt_x_neg` (this file), `mulByInt_x_one` (from `MulByIntBaseCase`), `x_gen` (project definition).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 180–213, proof body ~31 lines
- **Notes**: Proof is **31 lines** (just over the 30-line threshold). The tail of the proof (lines 193–213) contains an algebraMap tower commutation argument that could potentially be extracted as a lemma. No sorry, no maxHeartbeats.

---

### `theorem mulByInt_comp_pullback_x_neg_one_neg_one`

- **Type**: `(mulByInt W.toAffine (-1)).pullback ((mulByInt W.toAffine (-1)).pullback (x_gen W)) = mulByInt_x W ((-1 : ℤ) * -1)`
- **What**: The double `[-1]`-pullback on `x_gen` matches `mulByInt_x W ((-1)*(-1)) = mulByInt_x W 1 = x_gen`. A concrete instance of the composition identity.
- **How**: Applies `mulByInt_pullback_x_neg_one` twice to reduce both pullbacks to `x_gen`, then identifies with `mulByInt_x W 1` via `mulByInt_x_one`.
- **Hypotheses**: `W` an elliptic curve over `F`.
- **Uses from project**: `mulByInt_pullback_x_neg_one` (this file), `mulByInt_x_one` (from `MulByIntBaseCase`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 219–225, proof body ~4 lines
- **Notes**: Appears to be a specimen/example instance rather than a reused infrastructure lemma; likely unused in other files too.

---

### `theorem mulByInt_comp_pullback_x_one_right`

- **Type**: `(m : ℤ) (hm : m ≠ 0) : (mulByInt W.toAffine 1).pullback ((mulByInt W.toAffine m).pullback (x_gen W)) = mulByInt_x W (m * 1)`
- **What**: The `[1]`-pullback followed by `[m]`-pullback sends `x_gen` to `mulByInt_x W (m * 1) = mulByInt_x W m`. Another concrete composition identity instance.
- **How**: Reduces `m * 1 = m` via `mul_one`, applies `mulByInt_one_pullback_eq_id` to eliminate the outer `[1]`-pullback, then uses `mulByInt_pullback_x` for the remaining `[m]`-pullback.
- **Hypotheses**: `W` an elliptic curve over `F`; `m ≠ 0`.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (from `MulByIntBaseCase`), `mulByInt_pullback_x` (from `MulByIntBaseCase`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 229–239, proof body ~8 lines
- **Notes**: Appears to be a scaffolding/example instance; likely used externally for the composition T-III-4-020b driver.

---

### `theorem mulByInt_comp_pullback_x_one_left`

- **Type**: `(n : ℤ) (hn : n ≠ 0) : (mulByInt W.toAffine n).pullback ((mulByInt W.toAffine 1).pullback (x_gen W)) = mulByInt_x W (1 * n)`
- **What**: The `[n]`-pullback followed by `[1]`-pullback sends `x_gen` to `mulByInt_x W (1 * n) = mulByInt_x W n`. Symmetric companion to `mulByInt_comp_pullback_x_one_right`.
- **How**: Reduces `1 * n = n` via `one_mul`, applies `mulByInt_one_pullback_eq_id` to eliminate the inner `[1]`-pullback, then uses `mulByInt_pullback_x` for the `[n]`-pullback.
- **Hypotheses**: `W` an elliptic curve over `F`; `n ≠ 0`.
- **Uses from project**: `mulByInt_one_pullback_eq_id` (from `MulByIntBaseCase`), `mulByInt_pullback_x` (from `MulByIntBaseCase`).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 244–254, proof body ~8 lines
- **Notes**: Symmetric companion to `mulByInt_comp_pullback_x_one_right`; same scaffolding status.

---

## Summary statistics

| Metric | Count |
|---|---|
| Total declarations | 11 |
| Theorems/lemmas | 11 |
| Defs | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 1 (`mulByInt_comp_pullback_x_neg_one`, 31 lines) |
| Unused in file | 8 |

## Key observations

- `mulByInt_x_neg` is marked `@[simp]` and used in 2 proof bodies within the file; it is the most-referenced declaration within the file.
- `mulByInt_comp_toAddMonoidHom` and `mulByInt_comp_eq_mul_of_pullback_witness` form a two-step chain culminating in `mulByInt_comp_eq_mul_of_generator_witness`, which is the main external API used by `GenericPointZsmul.lean`.
- `mulByInt_pullback_x_neg_one` is a key external API used in many downstream files (`Differential.lean`, `Frobenius.lean`, `SilvermanIV14.lean`, etc.) despite only being used once within this file.
- The last four theorems (`mulByInt_comp_pullback_x_neg_one`, `*_neg_one_neg_one`, `*_one_right`, `*_one_left`) appear to be concrete scaffolding instances for T-III-4-020b rather than reused API — none of them are referenced within the file.
