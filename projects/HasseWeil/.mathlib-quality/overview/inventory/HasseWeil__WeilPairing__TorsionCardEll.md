# Inventory: ./HasseWeil/WeilPairing/TorsionCardEll.lean

**File purpose**: The thin **assembly** of `#E[ℓ]=ℓ²` from the separable-kernel-torsor capstone `HasseWeil.card_kernel_eq_degree_of_separable_concrete` (`SeparableKernelTorsor.lean`) instantiated at `φ = mulByInt W.toAffine ℓ`, wiring together the three `[ℓ]`-specific geometric discharges (`hxy`/`hcov`, `h_normal`, `hdesc`) and the unconditional separability `mulByInt_isSeparable`.

**Imports**: `HasseWeil.WeilPairing.TorsionGeometric`, `HasseWeil.WeilPairing.TorsionKernelRational`

**Namespace**: `HasseWeil.WeilPairing.TorsionGeometric` (re-opens `HasseWeil`). **Section variables**: `{F} [Field F] [DecidableEq F] (W) [W.toAffine.IsElliptic]`.

**Total declarations**: 2 public `theorem`. **No `sorry`, no `set_option`.**

---

## Declarations

### `theorem card_torsion_ell_of_discharges`
- **What**: `(#E[ℓ] : ℤ) = ℓ²` given the three `[ℓ]` geometric discharges as explicit hypotheses: `hxy` (addition-formula coordinate translation-invariance), `h_normal` (normality of `K(E)/[ℓ]*K(E)`), and `hdesc` (the generic-point descent torsor). Separability is supplied internally.
- **How**: derives `ℓ≠0` from `(ℓ:F)≠0`, feeds `mulByInt_isSeparable`, `hcov_mulByInt_of_xy W ℓ hℓ0 hxy`, `h_normal`, `hdesc` into `card_kernel_eq_degree_of_separable_concrete` to get `#ker[ℓ]=deg[ℓ]`, then `card_torsion_ell_of_ker_deg` (which evaluates `deg[ℓ]=ℓ²`).
- **Hypotheses**: `(ℓ:ℤ)`, `hℓ:(ℓ:F)≠0`, plus `hxy`, `h_normal`, `hdesc` (the literal statements of `hxy_mulByInt`/`h_normal_mulByInt`/`hdesc_mulByInt`).
- **Uses from project**: `mulByInt`, `card_kernel_eq_degree_of_separable_concrete`, `mulByInt_isSeparable`, `hcov_mulByInt_of_xy`, `card_torsion_ell_of_ker_deg`, `translateAlgEquivOfPoint`, `mulByInt_x/y`, `liftPointToKE`, `genericPoint{,Act}`.
- **Used by (in file)**: `card_torsion_ell`.
- **Visibility**: public. **Lines**: 43–63 (≈8-line proof).

### `theorem card_torsion_ell` (Silverman III.6.4(a))  ★ live API — the headline of the cluster
- **What**: `(#E[ℓ] : ℤ) = ℓ²` over an algebraically closed `F`, for `(ℓ:F)≠0` (i.e. `ℓ≠p`).
- **How**: discharges the three hypotheses of `card_torsion_ell_of_discharges` with the concrete `hxy_mulByInt`, `h_normal_mulByInt`, `hdesc_mulByInt`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ:ℤ)`, `hℓ:(ℓ:F)≠0`.
- **Uses from project**: `card_torsion_ell_of_discharges`, `hxy_mulByInt`, `h_normal_mulByInt`, `hdesc_mulByInt`.
- **Used by (in file)**: none.
- **Used by (external)**: `WeilPairing/Pairing.lean` (the `#E[ℓ]=ℓ²` and `#E[ℓ²]=ℓ⁴` annihilation/cardinality inputs to the pairing construction). Also re-exported indirectly through `TorsionModule.lean`.
- **Visibility**: public. **Lines**: 71–77 (≈4-line proof).

---

## File Summary

**Role in cluster**: The **capstone-instantiation glue**. It is where the abstract `card_kernel_eq_degree_of_separable_concrete` meets the four `[ℓ]`-specific facts, producing the single externally-consumed cardinality theorem `card_torsion_ell`.

**Live spine**: `card_torsion_ell` is the cluster's main exported result. `card_torsion_ell_of_discharges` is the parametric form (terminal in-file, but a clean seam if one ever wants the bound from alternative discharges).

**Cleanup findings**:
- (a) **Unused-in-file**: none.
- (b) No scratch/superseded content — this file is already minimal.
- (c) **No hand-rolling**: it correctly delegates everything; `#E[ℓ]` is the project's `torsionSubgroup`-based `W.toAffine[ℓ]` (the `Nat.card` form), and the module structure is deferred to `TorsionModule.lean`.
- (d) **Moral duplication**: `card_torsion_ell_of_discharges` re-spells the full `hxy`/`h_normal`/`hdesc` types inline (≈12 lines of hypothesis signature) that are *identical* to the conclusions of `hxy_mulByInt`/`h_normal_mulByInt`/`hdesc_mulByInt`. This is unavoidable for a parametric statement but is a readability cost; a shared `structure EllDischarges` bundling the three would de-duplicate the signature here and in `PairingNondeg.lean` (which independently re-derives the same three).
- **`sorry`/heartbeats**: none.
