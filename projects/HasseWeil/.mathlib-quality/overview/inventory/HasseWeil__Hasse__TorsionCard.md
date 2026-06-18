# Inventory: ./HasseWeil/Hasse/TorsionCard.lean

**File summary**: 71 lines, 2 public theorems, 0 instances, 0 defs. No `sorry`, no `set_option maxHeartbeats`. This is a thin glue file closing Silverman III.6.4(a) in witness-parametric form.

---

### `theorem torsionSubgroup_card_of_witness`

- **Type**:
  ```
  (m : ℤ) (hm : m ≠ 0)
  (h_ker_deg : Nat.card (mulByInt W.toAffine m).kernel =
    (mulByInt W.toAffine m).degree) :
  (Nat.card W.toAffine[m] : ℤ) = m ^ 2
  ```
- **What**: Given the witness `#ker [m] = deg [m]`, proves `#E[m] = m²` as integers (Silverman III.6.4(a)).
- **How**: Rewrites via the definitional equality `E[m] = ker [m]`, applies `mulByInt_degree` (from `HasseWeil.Basic`) to evaluate `deg [m] = (m²).toNat`, then uses `Int.toNat_of_nonneg (sq_nonneg _)` to lift from `ℕ` to `ℤ`.
- **Hypotheses**: `W` is an elliptic curve over a field `F`; `m ≠ 0 : ℤ`; caller supplies the kernel-degree equality.
- **Uses from project**: `mulByInt_degree` (HasseWeil.Basic)
- **Used by**: `torsionSubgroup_card_of_separable_witness` (this file); `HasseWeil.WeilPairing.TorsionGeometric` (external); `HasseWeil.WeilPairing.TorsionSeparable` (external, via the separable wrapper).
- **Visibility**: public
- **Lines**: 42–49, proof length ~4 lines
- **Notes**: none

---

### `theorem torsionSubgroup_card_of_separable_witness`

- **Type**:
  ```
  (m : ℤ) (hm : m ≠ 0)
  [Finite (mulByInt W.toAffine m).kernel]
  (h_sep : (mulByInt W.toAffine m).IsSeparable)
  (h_fin_dim : FiniteDimensional W.toAffine.FunctionField
    (mulByInt W.toAffine m).toAlgebra.toModule)
  (h_fiber_witness : ∃ P₀, Nat.card {P // φ P = φ P₀} = φ.sepDegree) :
  (Nat.card W.toAffine[m] : ℤ) = m ^ 2
  ```
- **What**: A stronger witness-parametric form of III.6.4(a) that accepts separability + a fiber-count witness instead of the raw kernel-degree equality; reduces to `torsionSubgroup_card_of_witness` via `Isogeny.card_kernel_eq_degree_of_separable_witness`.
- **How**: Delegates directly to `torsionSubgroup_card_of_witness`, supplying the kernel-degree equality produced by `Isogeny.card_kernel_eq_degree_of_separable_witness` from `HasseWeil.EC.IsogenyKernel`. That theorem in turn uses `fiber_card_eq_sepDegree_of_witness` + `isSeparable_iff_sepDegree_eq_degree`.
- **Hypotheses**: `W` elliptic over `F`; `m ≠ 0 : ℤ`; `[m]` has finite kernel; `[m]` is separable; `W.toAffine.FunctionField` is finite-dimensional over itself as `[m].toAlgebra`-module; a fiber-cardinality witness exists.
- **Uses from project**: `torsionSubgroup_card_of_witness` (this file); `Isogeny.card_kernel_eq_degree_of_separable_witness` (HasseWeil.EC.IsogenyKernel)
- **Used by**: `HasseWeil.WeilPairing.TorsionSeparable` (external caller, confirmed by grep)
- **Visibility**: public
- **Lines**: 54–68, proof length ~4 lines (term-mode)
- **Notes**: none

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 2 |
| Defs | 0 |
| Lemmas/theorems | 2 |
| Instances | 0 |
| Sorries | none |
| `set_option maxHeartbeats` | none |
| Long proofs (>30 lines) | none |
| Unused in file | none (both are called externally; `torsionSubgroup_card_of_separable_witness` also calls `torsionSubgroup_card_of_witness`) |
| Key API | `torsionSubgroup_card_of_witness` (used by the second theorem + 2 external files) |
