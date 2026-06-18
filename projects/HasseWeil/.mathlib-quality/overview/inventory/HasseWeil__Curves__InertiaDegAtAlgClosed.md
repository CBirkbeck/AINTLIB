# Inventory: ./HasseWeil/Curves/InertiaDegAtAlgClosed.lean

**File**: `HasseWeil/Curves/InertiaDegAtAlgClosed.lean`
**Module header**: "Inertia degree = 1 at smooth points over algebraically closed base (Piece 9)"
**Status note in file**: Partial. Full `inertiaDeg = 1` closure blocked on a `Module.Finite (C₂.CR/Q) (C₁.CR/P)` instance-search issue.

---

## Declarations

### `theorem residue_algebraMap_surjective_of_isAlgClosed`

- **Type**:
  ```
  [IsAlgClosed F]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra F A] [Algebra F B] [IsScalarTower F A B]
  (hFA : Function.Bijective (algebraMap F A))
  (hFB : Function.Bijective (algebraMap F B)) :
  Function.Surjective (algebraMap A B)
  ```
- **What**: If F is algebraically closed and both A and B are isomorphic to F as F-algebras (via bijective algebraMap), then the induced algebra map A → B is surjective. Intended application: both residue fields C₁.CR/P and C₂.CR/Q are ≃ F (since F is algebraically closed and the points are maximal), so the residue-field map is surjective.
- **How**: Given b : B, use surjectivity of algebraMap F B (hFB.2) to lift b to some c : F, then map c via F → A and use `IsScalarTower.algebraMap_apply` to show the image equals b.
- **Hypotheses**: F algebraically closed; A and B both admit bijective algebra maps from F; scalar tower F → A → B.
- **Uses from project**: None (fully general abstract algebra).
- **Used by**: `residue_finrank_le_one_of_surjective` does NOT call this; neither declaration calls the other. Both are unused within this file.
- **Visibility**: public
- **Lines**: 42–53; proof length ~6 lines.
- **Notes**: No sorry. No set_option. Not referenced by any other declaration in this file. Likely intended to feed a downstream `inertiaDeg = 1` proof not yet written in this file (per the module docstring). The variables `C₁ C₂ : SmoothPlaneCurve F` declared at the top of the namespace are not actually used by this theorem (it is stated for abstract A, B).

---

### `theorem residue_finrank_le_one_of_surjective`

- **Type**:
  ```
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [StrongRankCondition A] [Nontrivial B]
  (h_surj : Function.Surjective (algebraMap A B)) :
  Module.finrank A B ≤ 1
  ```
- **What**: If the algebra map A → B is surjective and A satisfies the strong rank condition, then B has finrank ≤ 1 as an A-module. This is the algebraic ingredient showing inertiaDeg ≤ 1 once surjectivity of the residue-field map is known.
- **How**: Applies mathlib's `finrank_le_one` with spanning vector `1 : B`: for any w : B, use surjectivity to find c : A with `algebraMap A B c = w`, then rewrite using `Algebra.smul_def` and `mul_one`.
- **Hypotheses**: Algebra map A → B is surjective; A satisfies StrongRankCondition; B is nontrivial.
- **Uses from project**: None.
- **Used by**: Unused within this file.
- **Visibility**: public
- **Lines**: 60–69; proof length ~6 lines.
- **Notes**: No sorry. No set_option. Calls mathlib's `finrank_le_one`. Not referenced by any other declaration in this file. The file's docstring explains the full `inertiaDeg = 1` combination is blocked on a `Module.Finite` instance search issue.

---

## File-level observations

- **Total declarations**: 2 theorems.
- **Sorry**: none.
- **`set_option maxHeartbeats`**: none.
- **Long proofs (>30 lines)**: none (both proofs are ~6 lines each).
- **Unused within file**: both declarations (`residue_algebraMap_surjective_of_isAlgClosed`, `residue_finrank_le_one_of_surjective`) — neither is called by the other or by any other declaration in the file.
- **Key API**: none (no declaration is used by 3+ others in this file).
- **Cross-file usage**: grep found no references in other project files (both declarations appear to be dead code at this stage, awaiting the downstream `inertiaDeg = 1` assembly).
- **Notable**: The file is explicitly described as "partial" in its module docstring. The variables `C₁ C₂ : SmoothPlaneCurve F` are declared in the `variable` block but neither theorem uses them — both theorems are stated abstractly for generic commutative rings A, B. The `/-! ### Progress note -/` section (lines 71–91) is a doc-comment, not a declaration.
