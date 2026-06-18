# Inventory: ./HasseWeil/KernelDegree.lean

**File**: `HasseWeil/KernelDegree.lean`
**Imports**: `HasseWeil.Ramification`, `Mathlib.FieldTheory.Finite.Basic`
**Imported by**: No Lean file in the project imports this module (entirely unimported).

---

## Summary

Three declarations across two sections. Section `FrobeniusId` proves that the Frobenius algebra homomorphism is the identity on `F_q`. Section `FiberSize` constructs the fiber-kernel bijection for group homomorphisms and derives the equal-cardinality corollary.

No `sorry`, no `set_option maxHeartbeats`, no proofs longer than 30 lines.

All three declarations appear to be dead code within the project: the file is never imported by any other Lean file, and similarly-named but distinct versions of `fiberEquivKer` and `card_fiber_eq_card_ker` live in `HasseWeil/WeilPairing/Fiber.lean` and `HasseWeil/EC/IsogenyKernel.lean`. There is a migration ticket `T-MIGRATE-014` proposing to move this content to `HasseWeil/EC/IsogenyFactor.lean`.

---

## Declarations

### `theorem frobeniusAlgHom_eq_id`

- **Type**: `{K : Type*} [Field K] [Fintype K] → frobeniusAlgHom K K = AlgHom.id K K`
- **What**: Proves that the Frobenius `AlgHom` (the ring map `a ↦ a^q`) is equal to the identity on `F_q` itself, because every element satisfies `a^q = a` in a finite field of order `q`.
- **How**: `AlgHom.ext` reduces to checking pointwise equality; `simp [pow_card]` closes the goal using `FiniteField.pow_card : a ^ Fintype.card K = a`.
- **Hypotheses**: `K` is a field, finite (Fintype), no `DecidableEq` needed (omitted via `omit`).
- **Uses from project**: none (pure mathlib).
- **Used by**: unused in file; no other file imports `KernelDegree.lean`.
- **Visibility**: public
- **Lines**: 39–43, proof length 3 lines
- **Notes**: none

---

### `noncomputable def fiberEquivKer`

- **Type**: `(φ : G →+ H) → (Q : H) → (P₀ : G) → (hP₀ : φ P₀ = Q) → {P : G // φ P = Q} ≃ φ.ker`
  where `G H` are `AddCommGroup`, `G` is `Fintype`, both have `DecidableEq`.
- **What**: Constructs an explicit equivalence between the fiber `φ⁻¹(Q)` and the kernel `ker(φ)`, given a chosen preimage `P₀` of `Q`. The bijection sends `P ↦ P − P₀` (with inverse `K ↦ K + P₀`).
- **How**: Direct `Equiv` construction; `toFun`/`invFun` are defined by translation; `left_inv`/`right_inv` by `simp`; membership in `ker` is checked via `AddMonoidHom.mem_ker` and `map_sub`.
- **Hypotheses**: `G`, `H` finite abelian groups (with `DecidableEq`); a chosen preimage `P₀` of `Q` under `φ`.
- **Uses from project**: none.
- **Used by**: `card_fiber_eq_card_ker` (within this file).
- **Visibility**: public
- **Lines**: 61–68, proof/body length 8 lines
- **Notes**: Suspected duplication — a structurally identical `fiberEquivKer` for `W.Point →+` lives in `HasseWeil/WeilPairing/Fiber.lean:29`, and `fiberEquivKernel` in `HasseWeil/EC/IsogenyKernel.lean:252` serves the same role for isogenies.

---

### `theorem card_fiber_eq_card_ker`

- **Type**: `(φ : G →+ H) → (Q : H) → (hQ : Q ∈ Set.range φ) → Fintype.card {P : G // φ P = Q} = Fintype.card φ.ker`
- **What**: For any group homomorphism φ between finite abelian groups, the cardinality of every fiber over a point in the image equals the cardinality of the kernel.
- **How**: Destructs `hQ` to get an explicit preimage `P₀`, then applies `Fintype.card_congr (fiberEquivKer φ Q P₀ hP₀)`.
- **Hypotheses**: `G` finite, `H` abelian group (no `DecidableEq G` needed, omitted via `omit`); `Q` in the image of `φ`.
- **Uses from project**: `fiberEquivKer` (in this file).
- **Used by**: unused in file (no callers within file; file is unimported).
- **Visibility**: public
- **Lines**: 73–76, proof length 3 lines
- **Notes**: none
