# Inventory: ./HasseWeil/WeilPairing/Pullback.lean

**File purpose**: Defines the **multiplicity-free geometric divisor pullback** `f*((Q)) = Σ_{fP=Q} (P)` for a separable point-map endomorphism `f` (étale fibres, multiplicity `1`) — the keystone object of Route 2A, used both by the Weil-pairing construction (`div g = [ℓ]^*(T) − [ℓ]^*(O)`) and by the separable adjoint. Ships the definition plus its **degree** `deg(f*((Q))) = #ker f` (Silverman III.4.10c, separable case) and the start of the `σ`-bridge `σ(f*((Q))) = Σ_{fP=Q} P`. Foundational — `pullbackDiv` is referenced by ~16 files across the Weil-pairing development.

**Imports**: `HasseWeil.WeilPairing.Fiber`, `HasseWeil.Curves.PicZero`

**Total declarations**: 4 (3 `theorem`, 1 `noncomputable def`)

**Module options**: `set_option linter.unusedSectionVars false`. No `sorry`, no `maxHeartbeats`.

**Standing hypotheses** (whole file): `{F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]`. (Note: `W` here is an `Affine F`, not a `WeierstrassCurve F` — the affine model directly.)

---

## Declarations

### `theorem degree_single`
- **Type**: `(P : Curves.ProjectiveSmoothPoint (⟨W⟩ : Curves.SmoothPlaneCurve F)) (n : ℤ) : Curves.ProjectiveDivisor.degree (Finsupp.single P n) = n`
- **What**: The degree of a single projective place `(P)` with multiplicity `n` equals `n`.
- **How**: Unfolds `Curves.ProjectiveDivisor.degree` and applies `Finsupp.sum_single_index` (with the zero-coefficient base case `rfl`).
- **Hypotheses**: none beyond `{F}`, `{W}` (the `[DecidableEq F]` and `[W.IsElliptic]` instances are `omit`ted).
- **Uses from project**: `Curves.ProjectiveDivisor.degree` (Curves)
- **Used by (within file)**: `degree_pullbackDiv`. **Used by (project)**: `OneSubDualDivisor`, `WeilFunction`, `PairingProps` (a general single-place-degree lemma).
- **Visibility**: public
- **Lines**: 25–31 (with `omit`), proof length: 2 lines
- **Notes**: This is the **canonical** `degree_single` for projective divisors — defined only here, reused by 3+ files. No duplicate elsewhere in the project.

### `noncomputable def pullbackDiv`
- **Type**: `(f : W.Point →+ W.Point) (h : Finite f.ker) (Q : W.Point) : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F)`
- **What**: **The multiplicity-free geometric pullback divisor** `f*((Q)) = Σ_{fP=Q} (P)`, the formal sum over the (finite) fibre with each point carrying multiplicity `1`.
- **How**: Installs `Fintype {P // f P = Q}` from `fiber_finite f h Q`, then sums `Finsupp.single P.val.toProjectiveSmoothPoint 1` over the fibre.
- **Hypotheses**: `f` an additive endomorphism of `W.Point` with finite kernel; `Q : W.Point`.
- **Uses from project**: `fiber_finite` (Fiber), `Affine.Point.toProjectiveSmoothPoint`
- **Used by (within file)**: `degree_pullbackDiv`, `projectiveDivisorSum_pullbackDiv`. **Used by (project)**: ~16 files (the central pullback-divisor object: `WeilFunction`, `Pairing` (via that), `PairingNondeg`, `PairingProps`, `DivisorPullback`, `SigmaBridge`, `FrobMatrixData`, `SeparableScaling`, `HfactLemma`, `PencilCovariance`, `OneSub*`, `Frobenius*`, …).
- **Visibility**: public
- **Lines**: 34–37, proof length: ~3 lines (def body)
- **Notes**: The keystone definition of the file (and of Route 2A's divisor machinery).

### `theorem degree_pullbackDiv`
- **Type**: `(f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point} (hP₀ : f P₀ = Q) : (pullbackDiv f h Q).degree = Nat.card f.ker`
- **What**: **Degree of the mult-1 pullback** (Silverman III.4.10c, separable): `deg(f*((Q))) = #ker f`.
- **How**: Pushes `degree` through the fibre sum (`degreeHom`, `map_sum`, `degree_single`), reducing to `#fibre` (`Finset.sum_const`/`Finset.card_univ`); then `fiber_card_eq_ker_card f hP₀` identifies `#fibre = #ker f` (using the existence of one preimage `P₀`).
- **Hypotheses**: `f` with finite kernel; a witness `P₀` with `f P₀ = Q` (so the fibre is nonempty, a torsor under `ker f`).
- **Uses from project**: `pullbackDiv` (this file), `Curves.ProjectiveDivisor.degreeHom_apply`, `degree_single` (this file), `fiber_card_eq_ker_card` (Fiber)
- **Used by (within file)**: none. **Used by (project)**: `OneSubDualDivisor`, `WeilFunction` (`pullbackDiv_sub_isPrincipal`), `PicDualDivisorClassLemma`, `SeparableTransportBridge`, `SeparableScaling`.
- **Visibility**: public
- **Lines**: 40–46, proof length: ~5 lines

### `theorem projectiveDivisorSum_pullbackDiv`
- **Type**: `(f : W.Point →+ W.Point) (h : Finite f.ker) (Q : W.Point) : Curves.projectiveDivisorSum W (pullbackDiv f h Q) = ∑ P : {P // f P = Q}, P.val`
- **What**: **The `σ`-section of the pullback divisor**: `σ(f*((Q))) = Σ_{fP=Q} P` (the group sum of the fibre). The start of the III.6.1(b) `σ`-bridge.
- **How**: Pushes `projectiveDivisorSum` through the fibre sum (`projectiveDivisorSumHom`, `map_sum`), then per-place `projectiveDivisorSum_single` + `one_zsmul` + the round-trip `toProjectiveSmoothPoint_toAffinePoint`.
- **Hypotheses**: `f` with finite kernel; `Q : W.Point`.
- **Uses from project**: `pullbackDiv` (this file), `Curves.projectiveDivisorSum`/`projectiveDivisorSumHom_apply`/`projectiveDivisorSum_single` (Curves), `Affine.Point.toProjectiveSmoothPoint_toAffinePoint`
- **Used by (within file)**: none. **Used by (project)**: `SigmaBridge` (`sigma_pullbackDiv_sub`).
- **Visibility**: public
- **Lines**: 50–57, proof length: ~5 lines

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `degree_single` | `degree_pullbackDiv` (+ project: OneSubDualDivisor, WeilFunction, PairingProps) |
| `pullbackDiv` | `degree_pullbackDiv`, `projectiveDivisorSum_pullbackDiv` (+ ~16 project files) |
| `degree_pullbackDiv` | (project: OneSubDualDivisor, WeilFunction, PicDualDivisorClassLemma, SeparableTransportBridge, SeparableScaling) |
| `projectiveDivisorSum_pullbackDiv` | (project: SigmaBridge) |

**Key API** (live spine): `pullbackDiv` (the central object), `degree_pullbackDiv`, `degree_single`, `projectiveDivisorSum_pullbackDiv` — all four are exported and consumed elsewhere.

## Notes / cleanup analysis

- **(a) Unused within file**: `degree_pullbackDiv` and `projectiveDivisorSum_pullbackDiv` are not used by later declarations *in this file*, but both are exported and used elsewhere — not dead.
- **(b)** No scratch/superseded content. The file is small (59 lines) and entirely live.
- **(c) mathlib-fit**: `pullbackDiv` is a bespoke fibre-sum divisor; mathlib has no direct off-the-shelf "multiplicity-free pullback of a divisor under an isogeny" (this is genuinely project-specific algebraic geometry). Uses mathlib's `Finsupp`/`Fintype`/`Finset.sum` correctly. `degree_single` reduces to `Finsupp.sum_single_index` — appropriately thin.
- **(d) Duplication**: confirmed there is exactly one `degree_single` in the project (here); it is correctly shared, not duplicated.
- **(e) Generalisation**: `degree_single` and the two divisor-section lemmas already use only `AddMonoidHom` + `Finite ker` + the projective-divisor API; they are stated at a natural generality (any additive endomorphism with finite kernel, not specialised to `[ℓ]` or Frobenius). Good.
- **No `sorry`, no `maxHeartbeats`, no proof >30 lines.**
