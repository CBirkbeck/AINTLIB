# Inventory: ./HasseWeil/Hasse/OneSubFrobenius.lean

**File summary**: 113 lines, 2 public theorems, 0 defs, 0 instances, 0 sorries.
Thin specialisation layer: both theorems delegate almost immediately to generic
witness-parametric lemmas from `Separability.lean`, `PointFix.lean`, and `IsogenyKernel.lean`,
pinning the abstract isogeny argument to the concrete `isogOneSub_negFrobenius W hq`.

---

## Imports

```
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.Hasse.Separability
import HasseWeil.Hasse.PointFix
```

---

## Declarations

### `theorem isogOneSub_negFrobenius_isSeparable_of_witnesses`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
  (hq : 2 ≤ Fintype.card K)
  (h_coeff : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1)
  (h_sep_iff : (isogOneSub_negFrobenius W hq).IsSeparable ↔
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ≠ 0) :
  (isogOneSub_negFrobenius W hq).IsSeparable
  ```
- **What**: Proves that the concrete `isogOneSub_negFrobenius` endomorphism (id minus
  Frobenius, built in `AdditionPullback/Frobenius.lean`) is separable, given: (1) its
  omega-pullback coefficient equals 1, and (2) the differential separability criterion
  (IsSeparable iff that coefficient is nonzero).
- **How**: One-line delegation to `oneSubFrobenius_isSeparable_of_witness` from
  `Hasse/Separability.lean`, which converts the `h_coeff = 1` hypothesis into `≠ 0`
  and applies `h_sep_iff.mpr`.
- **Hypotheses**: K is a finite field with at least 2 elements; omega-pullback coefficient
  of the isogeny equals 1 (Silverman III.5.5 input); differential separability criterion
  holds as a biconditional.
- **Uses from project**:
  - `isogOneSub_negFrobenius` (`AdditionPullback/Frobenius.lean`)
  - `omegaPullbackCoeff` (`Hasse/Separability.lean` / earlier file)
  - `oneSubFrobenius_isSeparable_of_witness` (`Hasse/Separability.lean`)
- **Used by**: `AdditionPullback/Differential.lean` (called at lines 142 and 460); not
  referenced anywhere else in this file.
- **Visibility**: public
- **Lines**: 53–61, proof length 1 line (term-mode)
- **Notes**: None; no `sorry`, no `maxHeartbeats`, trivially short proof.

---

### `theorem isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses`

- **Type**:
  ```
  (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
  (hq : 2 ≤ Fintype.card K)
  (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
  (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
    W.toAffine.FunctionField _ _
    (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
  (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
    Nat.card {P : W.toAffine.Point //
        (isogOneSub_negFrobenius W hq).toAddMonoidHom P =
          (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀} =
      (isogOneSub_negFrobenius W hq).sepDegree)
  [Finite (isogOneSub_negFrobenius W hq).kernel] :
  (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine
  ```
- **What**: Establishes that the separable degree of `isogOneSub_negFrobenius` equals
  the point count `#E(F_q)`, by composing three equalities:
  `sepDegree = degree` (from separability + finite-dimensionality),
  `#ker = degree` (T-III-4-015 fiber witness form),
  and `#ker = pointCount` (the rational-point kernel equals the full point group).
- **How**: Three named `have` steps:
  1. `h_sd_eq_deg`: applies `Isogeny.isSeparable_iff_sepDegree_eq_degree` (from
     `EC/IsogenyKernel.lean:346`) with `h_pc_fin` and `h_pc_sep`.
  2. `h_ker_eq_deg`: applies `Isogeny.card_kernel_eq_degree_of_separable_witness`
     (from `EC/IsogenyKernel.lean:419`) with the three witnesses.
  3. `h_ker_eq_pc`: applies `kernel_eq_top_of_hom_eq_id_sub_frobenius` (from
     `Hasse/PointFix.lean`) with `rfl` (the isogeny's `toAddMonoidHom` is definitionally
     `id − π`), then `AddSubgroup.card_top` + `Nat.card_eq_fintype_card`.
  Final `rw` chains all three.
- **Hypotheses**: K is a finite field; W.toAffine.Point is Fintype; the isogeny is
  separable; the function-field module is finite-dimensional over itself (Witness #2);
  there exists a fiber of cardinality = sepDegree (T-III-4-012 fiber witness);
  the kernel is Finite.
- **Uses from project**:
  - `isogOneSub_negFrobenius` (`AdditionPullback/Frobenius.lean`)
  - `Isogeny.isSeparable_iff_sepDegree_eq_degree` (`EC/IsogenyKernel.lean:346`)
  - `Isogeny.card_kernel_eq_degree_of_separable_witness` (`EC/IsogenyKernel.lean:419`)
  - `kernel_eq_top_of_hom_eq_id_sub_frobenius` (`Hasse/PointFix.lean`)
  - `pointCount` (`Hasse/PointFix.lean` or earlier)
- **Used by**: `AdditionPullback/Differential.lean` (line 479); `Hasse/HoleE.lean` (line
  182); not referenced again within this file.
- **Visibility**: public
- **Lines**: 80–111, proof length ~18 lines (tactic mode)
- **Notes**: Proof is 18 lines; not longer than 30 lines. No `sorry`, no `maxHeartbeats`.
  The `rfl` passed to `kernel_eq_top_of_hom_eq_id_sub_frobenius` is load-bearing: it
  asserts the concrete isogeny's hom definitionally equals `id − frobenius`, which is
  satisfied by construction of `isogOneSub_negFrobenius`.

---

## Cross-reference summary

| Declaration | Uses from project | Used by (in file) |
|---|---|---|
| `isogOneSub_negFrobenius_isSeparable_of_witnesses` | `isogOneSub_negFrobenius`, `omegaPullbackCoeff`, `oneSubFrobenius_isSeparable_of_witness` | — (no in-file callers) |
| `isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses` | `isogOneSub_negFrobenius`, `Isogeny.isSeparable_iff_sepDegree_eq_degree`, `Isogeny.card_kernel_eq_degree_of_separable_witness`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`, `pointCount` | — (no in-file callers) |

Both declarations are leaf specialisations; neither is called by the other. All callers
are in other files (`AdditionPullback/Differential.lean`, `Hasse/HoleE.lean`).

## Key API

No declaration in this file is used by 3 or more other declarations within the file (only 2 declarations exist, each used by zero in-file callers).

## set_option maxHeartbeats

None.

## Long proofs (>30 lines)

None.

## Sorries

None.
