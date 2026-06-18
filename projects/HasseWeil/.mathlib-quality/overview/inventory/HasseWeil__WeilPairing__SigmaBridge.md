# Inventory: ./HasseWeil/WeilPairing/SigmaBridge.lean

**File purpose**: The **σ-bridge** (Silverman III.6.1(b)): `σ(f*((Q)) − f*((O))) = (#ker f) · P₀` for any
`P₀` with `f P₀ = Q`, where `σ = projectiveDivisorSum` (the Abel–Jacobi group-sum map). Pure group
theory over the kernel coset — reindexes the fibre sum by the kernel and reads off the difference. This
is the geometric heart of the dual: for separable `f` (`#ker f = deg f`), the RHS is `[deg f] P₀ = f̂(Q)`.
The bridge feeds (i) the Weil-function existence criterion (`WeilFunction.lean`) and (ii) the
divisor-class form `PicDualDivisorClass` (`PicDualDivisorClassLemma.lean` / `SeparableScaling.lean`).

**Imports**: `HasseWeil.WeilPairing.Pullback`

**Total declarations**: 2 top-level `theorem` (grep-confirmed). The task's "2/3" ratio counts a third
node at finer granularity (a section-variable / the `set_option` node); **both top-level theorems are LIVE.**

**Options set**: `linter.unusedSectionVars false`.

**Variables**: `{F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]`.

---

## Declarations

### `theorem fiber_sum_eq_ker_sum`
- **Type**: `(f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point} (hP₀ : f P₀ = Q) : (∑ P : {P // f P = Q}, P.val) = ∑ T : f.ker, (P₀ + (T : W.Point))` (under the `Fintype.ofFinite` instances)
- **What**: reindexes the fibre sum over the kernel coset: `Σ_{fP=Q} P = Σ_{T∈ker} (P₀ + T)`.
- **How**: `Fintype.sum_equiv (fiberEquivKer f hP₀)` mapping `P ↦ P.val` to `T ↦ P₀ + T`; the pointwise
  goal is closed by `simp only [fiberEquivKer, Equiv.coe_fn_mk]; abel`.
- **Hypotheses**: `Finite f.ker`, a preimage `hP₀ : f P₀ = Q`. Carries two local `Fintype.ofFinite`
  instances (the fibre and the kernel).
- **Uses from project**: `fiberEquivKer` (`WeilPairing/Fiber.lean:29`), `fiber_finite`
  (`WeilPairing/Fiber.lean:37`).
- **Used by**: `sigma_pullbackDiv_sub` (this file, L42–43). **No external consumers** — it is a private-in-spirit
  helper for the next theorem.
- **Visibility**: public (but effectively internal).
- **Lines**: 21–31, proof ~6 lines.
- **LIVE (internally).** Notes: could be marked `private` since nothing outside the file uses it (minor
  cleanup — see below).

---

### `theorem sigma_pullbackDiv_sub`
- **Type**: `(f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point} (hP₀ : f P₀ = Q) : projectiveDivisorSum W (pullbackDiv f h Q) − projectiveDivisorSum W (pullbackDiv f h 0) = Nat.card f.ker • P₀`
- **What**: **the σ-bridge (Silverman III.6.1(b))** — `σ(f*((Q)) − f*((O))) = (#ker f) · P₀`.
- **How**: `projectiveDivisorSum_pullbackDiv` at `Q` and `0`; `fiber_sum_eq_ker_sum` (twice, at `Q` and at
  `0` via `f 0 = 0`); then `simp only [zero_add, Finset.sum_add_distrib, Finset.sum_const,
  Finset.card_univ, ← Nat.card_eq_fintype_card]; abel`.
- **Hypotheses**: `Finite f.ker`, a preimage `hP₀`. Carries a local `Fintype f.ker` instance.
- **Uses from project**: `projectiveDivisorSum` (`Curves/PicZero.lean`), `pullbackDiv`
  (`WeilPairing/Pullback.lean:34`), `projectiveDivisorSum_pullbackDiv` (`Pullback.lean:50`),
  `fiber_sum_eq_ker_sum` (this file).
- **Used by**: **externally** `WeilFunction.lean:132` (real `rw` use; the Weil-function existence criterion)
  and `PicDualDivisorClassLemma.lean:124` (real use, inside `sigma_pullbackDivisor_kappaDivisor`).
  Doc-referenced from `SeparableScaling.lean` and `OneSubDualDivisor.lean` (the σ-machinery).
- **Visibility**: public.
- **Lines**: 35–46, proof ~6 lines.
- **LIVE.** **Key API** of the file.

---

## File Summary

- **Role in proof**: The single load-bearing primitive `sigma_pullbackDiv_sub` is the group-theoretic
  kernel of the dual-isogeny / σ-identity machinery on Route 2A. It is consumed by both the Weil-function
  existence criterion and the `PicDualDivisorClass`-discharge layer (which in turn feeds the separable
  Weil-pairing adjoint and the per-`ℓ` scaling leaves).
- **(a) Dead/unused declarations**: none. `fiber_sum_eq_ker_sum` has no *external* consumer but is used
  internally — not dead.
- **(b) Scratch/superseded sub-routes**: none. Small, focused, on the active route.
- **(c) Hand-rolled vs mathlib**: builds on the project's own `pullbackDiv` / `projectiveDivisorSum` /
  `fiberEquivKer` (the project's Abel–Jacobi divisor API). The reindexing uses mathlib's
  `Fintype.sum_equiv` directly — appropriate.
- **(d) Moral duplication**: note `fiberEquivKer` is defined **twice** in the project —
  `KernelDegree.lean:61` (general groups `G → H`) and `WeilPairing/Fiber.lean:29` (specialized to
  `W.Point`). This file uses the `Fiber.lean` one. Flagged as a cross-file duplicate to consider unifying
  (the `KernelDegree` version is the general one; `Fiber.lean` could re-export it).
- **(e) Under-general statements**: `sigma_pullbackDiv_sub` is already stated for a general
  `AddMonoidHom f : W.Point →+ W.Point` (not just isogenies), which is the right generality.
- **Cleanup flags**:
  - Mark `fiber_sum_eq_ker_sum` `private` (no external use).
  - No `sorry`, no `maxHeartbeats` in the file. Both proofs short (≤6 lines).
