# Inventory: ./HasseWeil/WeilPairing/TorsionGeometric.lean

**File purpose**: Discharges, over a **general** field `F` (used at `F = K̄`), the two parametric inputs to the separable-kernel-torsor capstone for `φ = [ℓ] = mulByInt W.toAffine ℓ`, plus the separability of `[ℓ]`. Phase A re-derives the Route-B ω-coefficient chain `omegaPullbackCoeff [ℓ] = ℓ` field-generally (the `RouteBInduction.lean` / `SilvermanIV14.lean` content is `[Fintype K]`-scoped but mathematically finite-field-free) ⟹ `[ℓ]` separable. Phase B reduces the covariance hypothesis `hcov [ℓ]` to two concrete coordinate-translation facts (`hxy_mulByInt`). Phase C is the trivial assembly `#ker[ℓ]=deg[ℓ] ⟹ #E[ℓ]=ℓ²`.

**Imports**: `HasseWeil.RouteBInduction`, `HasseWeil.EC.SeparableKernelTorsor`, `HasseWeil.Hasse.TorsionCard`, `HasseWeil.Curves.Differentials`, `Mathlib.FieldTheory.IsAlgClosed.Basic`

**Namespace**: `HasseWeil.WeilPairing.TorsionGeometric`. **Section variables**: `{F} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.toAffine.IsElliptic]`. Local notation `KE := FunctionField`, `R := CoordinateRing`.

**Total declarations**: 26 theorems (no `def`/`instance`). All public. **No `sorry` anywhere** (not even in comments).

---

## Declarations

### `theorem weierstrassEqn_KE`
- **Type**: the Weierstrass equation `y_gen² + a₁ x_gen y_gen + a₃ y_gen = x_gen³ + a₂ x_gen² + a₄ x_gen + a₆` in `K(E)`.
- **What**: The defining curve equation holds for the generic-point coordinates `x_gen, y_gen` viewed in the function field, with the `aᵢ` pushed in via `algebraMap F KE`.
- **How**: Takes `generic_equation W` (the equation at the generic point) and rewrites through `(W_KE W).toAffine.equation_iff` to peel the `Equation` predicate into the literal polynomial identity.
- **Hypotheses**: section only.
- **Uses from project**: `generic_equation`, `W_KE`, `x_gen`, `y_gen`.
- **Used by (in file)**: `kaehlerD_weierstrassEqn`.
- **Visibility**: public. **Lines**: 53–60 (3-line proof).

### `theorem kaehlerD_weierstrassEqn`
- **What**: Applies the Kähler differential `D F KE` to both sides of `weierstrassEqn_KE`, giving `D(LHS)=D(RHS)` in `Ω[K(E)/F]`.
- **How**: `congrArg (KaehlerDifferential.D F KE)` applied to `weierstrassEqn_KE`.
- **Uses from project**: `weierstrassEqn_KE`, `W_KE`, `x_gen`, `y_gen`.
- **Used by (in file)**: `kaehler_curve_eqn`.
- **Visibility**: public. **Lines**: 63–70 (term proof).

### `theorem kaehlerD_y_gen_sq` / `kaehlerD_x_gen_sq` / `kaehlerD_x_gen_cube`
- **What**: Leibniz expansions `D(y²)=y·Dy+y·Dy`, `D(x²)=x·Dx+x·Dx`, `D(x³)=x²·Dx+x·D(x²)`.
- **How**: `pow_two` (resp. a `ring` rewrite `x³=x²·x`) then `(D F KE).leibniz`.
- **Uses from project**: `x_gen`, `y_gen`.
- **Used by (in file)**: LHS/RHS D-expansion lemmas and `kaehler_curve_eqn`.
- **Visibility**: public. **Lines**: 73–92 (1–2 lines each).

### `theorem kaehlerD_weierstrass_LHS` / `kaehlerD_weierstrass_RHS`
- **What**: Full `D`-expansions of the two sides of the Weierstrass equation into `Dx`/`Dy` combinations with `algebraMap`-constant coefficients.
- **How**: Repeated `map_add`, the `pow`/`sq`/`cube` lemmas above, `(D F KE).leibniz` on each product, and `(D F KE).map_algebraMap` to kill `D(aᵢ)=0`, finishing with `simp [smul_zero, add_zero]`.
- **Uses from project**: `kaehlerD_{y,x}_gen_sq`, `kaehlerD_x_gen_cube`, `x_gen`, `y_gen`, `W_KE`.
- **Used by (in file)**: `kaehler_curve_eqn`.
- **Visibility**: public. **Lines**: 95–133 (≈9 / ≈9 lines).

### `theorem kaehler_curve_eqn`
- **What**: The substantive Kähler identity `(a₃ + 2y + a₁x)·Dy = (3x² + 2a₂x + a₄ − a₁y)·Dx` in `Ω[K(E)/F]` (the differential of the curve relation).
- **How**: Rewrites `2y`, `3x²`, `2a₂x` into sums to use `add_smul`/`sub_smul`, substitutes the LHS/RHS D-expansions into `kaehlerD_weierstrassEqn`, normalises with `smul_add`/`← mul_smul`, and closes with `linear_combination (norm := abel) h_eq`.
- **Uses from project**: `kaehlerD_weierstrassEqn`, `kaehlerD_weierstrass_LHS/RHS`, `x_gen`, `y_gen`, `W_KE`.
- **Used by (in file)**: `kaehlerD_y_gen_eq_num_smul_omega`, `kaehlerD_alpha_pullback_y_eq_smul_omega`.
- **Visibility**: public. **Lines**: 137–156 (>15-line proof).

### `theorem kaehlerD_x_gen_eq_u_smul_omega` (RB-ω1)
- **What**: `D(x_gen) = u_gen • ω` where `ω = invariantDifferential` (the invariant differential is `u⁻¹·D(x)`).
- **How**: rewrites `ω` by its definition `u⁻¹•D(x)`, then `smul_smul` + `mul_inv_cancel₀ (u_gen_ne_zero W)`.
- **Uses from project**: `u_gen`, `u_gen_ne_zero`, `x_gen`, `invariantDifferential`.
- **Used by (in file)**: `kaehlerD_alpha_pullback_x_eq_smul_omega`, `kaehlerD_addPullback_x_eq_one_add_smul_omega`.
- **Used by (external)**: `EC/DifferentialOrd.lean`.
- **Visibility**: public. **Lines**: 159–164.

### `theorem kaehlerD_y_gen_eq_num_smul_omega` (RB-ω2)
- **What**: `D(y_gen) = (3x²+2a₂x+a₄−a₁y) • ω`.
- **How**: From `kaehler_curve_eqn`, identifies the coefficient `a₃+2y+a₁x` as `u_gen` (a `ring` `show`), then multiplies through by `u_gen` using `kaehlerD_x_gen_eq_u_smul_omega` + `smul_comm`, and cancels by `smul_right_injective _ (u_gen_ne_zero W)`.
- **Uses from project**: `kaehler_curve_eqn`, `u_gen`, `u_gen_ne_zero`, `kaehlerD_x_gen_eq_u_smul_omega`, `invariantDifferential`, `x_gen`, `y_gen`.
- **Used by (in file)**: `kaehlerD_addPullback_x_eq_one_add_smul_omega`.
- **Used by (external)**: `EC/DifferentialOrd.lean`.
- **Visibility**: public. **Lines**: 167–184.

### `theorem kaehlerD_alpha_pullback_x_eq_smul_omega` (RB-ω3a)
- **What**: For an arbitrary endo-isogeny `α`, `D(α*x) = (α*u · a_α) • ω` where `a_α = omegaPullbackCoeff W α`.
- **How**: Uses `alpha_star_u_ne 0` (via `alpha_star_u_eq` + `pullback_injective`), the spec `omegaPullbackCoeff_spec` for `α*x`, then `smul_smul` + `mul_inv_cancel₀`.
- **Hypotheses**: `(α : Isogeny W.toAffine W.toAffine)`.
- **Uses from project**: `alpha_star_u`, `alpha_star_u_eq`, `omegaPullbackCoeff`, `omegaPullbackCoeff_spec`, `Isogeny.pullback_injective`, `invariantDifferential`, `x_gen`.
- **Used by (in file)**: `kaehlerD_alpha_pullback_y_eq_smul_omega`, `kaehlerD_addPullback_x_eq_one_add_smul_omega`.
- **Used by (external)**: `EC/DifferentialOrd.lean`.
- **Visibility**: public. **Lines**: 187–198.

### `theorem kaehlerD_alpha_pullback_y_eq_smul_omega` (RB-ω3b)
- **What**: `D(α*y) = ((3(α*x)²+2a₂(α*x)+a₄−a₁(α*y))·a_α) • ω`.
- **How**: Pulls `kaehler_curve_eqn` through `α` via `Isogeny.pullbackKaehler` (`_smul_KE`, `_D`), identifies the pulled-back coefficient as `alpha_star_u` (`hC`) and numerator (`hN`), substitutes `kaehlerD_alpha_pullback_x_eq_smul_omega`, then cancels by `smul_right_injective` + `ring`.
- **Uses from project**: `kaehler_curve_eqn`, `Isogeny.pullbackKaehler{,_D,_smul_KE}`, `alpha_star_u{,_eq}`, `kaehlerD_alpha_pullback_x_eq_smul_omega`, `omegaPullbackCoeff`, `x_gen`, `y_gen`.
- **Used by (external)**: `EC/DifferentialOrd.lean`.
- **Visibility**: public. **Lines**: 201–234 (>30-line proof).

### `theorem kaehlerD_addSlope_general` (Route B core III.5.2)
- **What**: Cleared differential of the addition slope: for `x_gen ≠ α*x_gen`, `Den²·D(slope) = Den·(Dy−D(α*y)) − N·(Dx−D(α*x))` with `N = y−α*y`, `Den = x−α*x`.
- **How**: writes `slope = N/Den` via `slope_of_X_ne`, applies `D.leibniz_div`, then clears `Den²·Den⁻²=1`.
- **Hypotheses**: `α`, `h_ne : x_gen ≠ α.pullback (x_gen)`.
- **Uses from project**: `addSlope`, `W_KE`, `x_gen`, `y_gen`, `Isogeny.pullback`.
- **Used by (in file)**: `kaehlerD_addPullback_x_general_cleared`.
- **Visibility**: public. **Lines**: 238–260.

### `theorem kaehlerD_addPullback_x_general` (III.5.2)
- **What**: `D(addPullback_x) = (2·slope + a₁)·D(slope) − Dx − D(α*x)`.
- **How**: unfolds `addPullback_x`, distributes `D` over the slope polynomial, `D.leibniz`/`D.leibniz_pow`, kills `D(aᵢ)`, then a `Nat`→`KE` scalar-cast `show` to match `2•`.
- **Uses from project**: `addPullback_x`, `addSlope`, `W_KE`, `x_gen`, `Isogeny.pullback`.
- **Used by (in file)**: `kaehlerD_addPullback_x_general_cleared`.
- **Visibility**: public. **Lines**: 264–288.

### `theorem kaehlerD_addPullback_x_general_cleared`
- **What**: `Den²·D(addPullback_x)` written purely in `Dx,Dy,D(α*x),D(α*y)` (slope eliminated).
- **How**: rewrites `kaehlerD_addPullback_x_general`, distributes `smul_sub`, reorders with `mul_comm`/`← smul_smul`, then substitutes `kaehlerD_addSlope_general`.
- **Hypotheses**: `α`, `h_ne`.
- **Uses from project**: `kaehlerD_addPullback_x_general`, `kaehlerD_addSlope_general`, `addSlope`, `x_gen`, `y_gen`.
- **Used by (in file)**: `kaehlerD_addPullback_x_eq_one_add_smul_omega`.
- **Visibility**: public. **Lines**: 291–310.

### `theorem kaehlerD_addPullback_x_eq_one_add_smul_omega` (RB-ω4, the III.5.2 ring collapse)
- **What**: `D(addPullback_x) = (2·addPullback_y + a₁·addPullback_x + a₃) · (1 + a_α) • ω`. This is the chord-recurrence engine: pulling back along `α` adds `1` to the ω-coefficient.
- **How**: substitutes the four `kaehlerD_*_eq_*_omega` lemmas into `..._cleared`, cancels `Den²` via `smul_right_injective`, then a huge `field_simp` + `linear_combination` against the generic equation (`hP = generic_equation`) and the pulled-back equation (`hαP = pullback_equation`).
- **Hypotheses**: `α`, `h_ne`. **`set_option maxHeartbeats 4000000`**, **`set_option linter.unusedSimpArgs false`**.
- **Uses from project**: `addPullback_x/y`, `addSlope`, `kaehlerD_x_gen_eq_u_smul_omega`, `kaehlerD_y_gen_eq_num_smul_omega`, `kaehlerD_alpha_pullback_{x,y}_eq_smul_omega`, `kaehlerD_addPullback_x_general_cleared`, `u_gen`, `alpha_star_u`, `generic_equation`, `pullback_equation`, `omegaPullbackCoeff`, `W_KE`.
- **Used by (in file)**: `omegaCoeff_mulByInt_succ`.
- **Visibility**: public. **Lines**: 318–360 (>30-line proof). **NOTE: 4M heartbeats — the heaviest proof in the cluster.**

### `theorem omegaCoeff_mulByInt_succ` (RB chord step)
- **What**: For `k ≥ 2`, `a_{[k+1]} = 1 + a_{[k]}` (ω-coefficient recurrence).
- **How**: Establishes `x_gen ≠ [k]*x_gen` (`mulByInt_x_ne_mulByInt_x`), uses the addition-formula identification `addPullback_xy_mulByInt_eq_succ` (`[k+1] = [k] ⊕ id` at coordinate level), `alpha_star_u_mulByInt`, then `omegaPullbackCoeff_unique` against `kaehlerD_addPullback_x_eq_one_add_smul_omega`.
- **Hypotheses**: `(k : ℤ)`, `2 ≤ k`.
- **Uses from project**: `omegaPullbackCoeff{,_unique,_spec}`, `mulByInt{,_x,_x_one,_x_ne_mulByInt_x,_pullback_x}`, `addPullback_xy_mulByInt_eq_succ`, `addPullback_x/y`, `alpha_star_u{,_eq,_mulByInt}`, `kaehlerD_addPullback_x_eq_one_add_smul_omega`, `x_gen`, `W_KE`.
- **Used by (in file)**: `omegaCoeff_mulByInt_ge_two`.
- **Visibility**: public. **Lines**: 365–398 (>30-line proof).

### `theorem omegaCoeff_mulByInt_ge_two` / `omegaCoeff_mulByInt_pos` / `omegaCoeff_mulByInt_neg`
- **What**: `a_{[n]} = (n : K(E))` for `n ≥ 2` (induction), then `n ≥ 1` (handle `n=1` via `mulByInt_one_eq_id`/`omegaPullbackCoeff_id`), then `a_{[-n]} = -a_{[n]}` for `n ≠ 0`.
- **How**: `_ge_two` is `Int.le_induction` with base `omegaPullbackCoeff_mulByInt_two` and step `omegaCoeff_mulByInt_succ`; `_neg` uses `mulByInt_{x,y}_neg`, `alpha_star_u_mulByInt`, `negY`, and `omegaPullbackCoeff_unique`.
- **Uses from project**: `omegaPullbackCoeff{,_id,_unique,_spec,_mulByInt_two}`, `mulByInt{,_one_eq_id,_x_neg,_y_neg,_pullback_x}`, `alpha_star_u_mulByInt`, `W_KE`.
- **Used by (in file)**: `omegaCoeff_mulByInt`.
- **Visibility**: public. **Lines**: 401–439.

### `theorem omegaCoeff_mulByInt` (Silverman III.5.3, field-general)
- **What**: `omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n` for all `n ≠ 0` — the Fintype-free restatement of `omegaPullbackCoeff_mulByInt_routeB`.
- **How**: case split on sign; positive case = `_pos`, negative via `_neg` + `_pos` + cast bookkeeping.
- **Hypotheses**: `(n : ℤ)`, `n ≠ 0`.
- **Uses from project**: `omegaPullbackCoeff`, `mulByInt`, `omegaCoeff_mulByInt_{pos,neg}`.
- **Used by (in file)**: `mulByInt_isSeparable`.
- **Used by (external)**: `EC/MulByIntUnramified.lean`, `EC/DifferentialOrd.lean`, `EC/WronskianGeneral.lean`.
- **Visibility**: public. **Lines**: 443–450.

### `theorem mulByInt_isSeparable` (Silverman III.5.4, field-general)  ★ live API
- **What**: `[ℓ] = mulByInt W.toAffine ℓ` is separable when `(ℓ : F) ≠ 0`. The finite-field-free replacement for the shipped `[Finite K]`-scoped `TorsionSeparable.mulByInt_isSeparable`.
- **How**: rewrites the criterion `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim` (finite-dimensionality from `isogeny_finiteDimensional`), then `omegaCoeff_mulByInt` reduces the ω-coefficient to `(ℓ : F)`, nonzero by `hℓ`.
- **Hypotheses**: `(ℓ : ℤ)`, `hℓ : (ℓ : F) ≠ 0`.
- **Uses from project**: `mulByInt`, `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`, `isogeny_finiteDimensional`, `omegaCoeff_mulByInt`.
- **Used by (in file)**: none.
- **Used by (external)**: `WeilPairing/PairingNondeg.lean`, `WeilPairing/TorsionSeparable.lean`.
- **Visibility**: public. **Lines**: 457–463.

### `theorem hcov_of_xy` (field-general hcov reducer)
- **What**: If `τ_k` fixes `φ*x_gen` and `φ*y_gen`, it fixes `φ*z` for all `z : K(E)`.
- **How**: applies the field-general `algHom_ext_x_y_gen` to the two AlgHoms `τ_k ∘ φ.pullback` and `φ.pullback`, then `congrFun`.
- **Hypotheses**: `(φ : Isogeny …)`, `(k : Point)`, `h_x`, `h_y`.
- **Uses from project**: `translateAlgEquivOfPoint`, `algHom_ext_x_y_gen`, `Isogeny.pullback`, `x_gen`, `y_gen`.
- **Used by (in file)**: `hcov_mulByInt_of_xy`.
- **Visibility**: public. **Lines**: 476–484. **NOTE**: the field-general analogue of (and replacement for) the `[Fintype F]`-scoped `translateAlgEquivOfPoint_pullback_invariance_of_xy` (`PointFix.lean`).

### `theorem hxy_mulByInt` (Silverman III.4.10c / addition formula)  ★ live API
- **What**: For every `k ∈ ker[ℓ]`, `τ_k` fixes the ℓ-division coordinate functions `mulByInt_x ℓ` and `mulByInt_y ℓ` (the function-field shadow of `[ℓ]∘(·+k) = [ℓ]` since `[ℓ]k=O`).
- **How**: works at the generic point: `m = Point.map τ_k`. Uses `m.map_zsmul`, the Phase-1 master lemma `translateAlgEquivOfPoint_map_genericPoint` (`m P_gen = P_gen + lift k`), and `ℓ•lift k = lift(ℓ•k) = 0` (from kernel membership via `Isogeny.mem_kernel_iff` + `mulByInt_apply`). Rewrites `ℓ•P_gen` via `zsmul_genericPoint_eq` (= `some (mulByInt_x ℓ)(mulByInt_y ℓ)`), realigning the `DecidableEq K(E)` instance with `Subsingleton.elim`, then `Point.map_some` + `Point.some.inj` reads off the two coordinate equalities.
- **Hypotheses**: `(ℓ : ℤ)`, `hℓ : ℓ ≠ 0`. **`set_option maxHeartbeats 1600000`**.
- **Uses from project**: `mulByInt{,_x,_y,_apply}`, `translateAlgEquivOfPoint`, `zsmul_genericPoint_eq`, `genericPoint`, `liftPointToKE`, `translateAlgEquivOfPoint_map_genericPoint`, `Isogeny.mem_kernel_iff`, `instDecidableEqFunctionField`.
- **Used by (in file)**: none.
- **Used by (external)**: `EC/MulByIntUnramified.lean`, `EC/MulByIntSamePlace.lean`, `WeilPairing/OneSubInftyResidues.lean`, `WeilPairing/PairingNondeg.lean`, `WeilPairing/PairingProps.lean`, and (via `TorsionCardEll.card_torsion_ell`).
- **Visibility**: public. **Lines**: 504–542 (>30-line proof).

### `theorem hcov_mulByInt_of_xy`  ★ live API
- **What**: Produces the capstone's `hcov [ℓ]` (`∀ k∈ker, ∀ z, τ_k(φ*z)=φ*z`) from the two `hxy` facts.
- **How**: `hcov_of_xy` per kernel point, discharging the two generator goals with `mulByInt_pullback_x/y` and the supplied `hxy`.
- **Hypotheses**: `(ℓ : ℤ)`, `hℓ : ℓ ≠ 0`, `hxy` (the `hxy_mulByInt` statement).
- **Uses from project**: `hcov_of_xy`, `mulByInt{,_pullback_x,_pullback_y}`, `translateAlgEquivOfPoint`, `x_gen`, `y_gen`, `Isogeny.pullback`.
- **Used by (in file)**: none.
- **Used by (external)**: `WeilPairing/PairingProps.lean`, `WeilPairing/PairingNondeg.lean`, and `TorsionCardEll.card_torsion_ell_of_discharges`.
- **Visibility**: public. **Lines**: 549–564.

### `theorem card_torsion_ell_of_ker_deg` (Phase C assembly)
- **What**: From `#ker[ℓ] = deg[ℓ]`, conclude `(#E[ℓ] : ℤ) = ℓ²`.
- **How**: one-liner delegating to `HasseWeil.torsionSubgroup_card_of_witness` (`Hasse/TorsionCard.lean`, which knows `deg[ℓ]=ℓ²`).
- **Hypotheses**: `(ℓ : ℤ)`, `hℓ : ℓ ≠ 0`, `h_ker_deg`.
- **Uses from project**: `mulByInt`, `torsionSubgroup_card_of_witness`.
- **Used by (in file)**: none.
- **Used by (external)**: via `TorsionCardEll.card_torsion_ell_of_discharges` (internal to that file; not referenced elsewhere directly).
- **Visibility**: public. **Lines**: 569–572 (term proof).

---

## File Summary

**Role in cluster**: This is the **`[ℓ]`-specialisation layer** of the `#E[ℓ]=ℓ²` proof. It supplies three of the four inputs to the separable-kernel-torsor capstone `card_kernel_eq_degree_of_separable_concrete` (consumed in `TorsionCardEll.lean`): separability (`mulByInt_isSeparable`) and covariance (`hcov_mulByInt_of_xy` via `hxy_mulByInt`); the remaining two (`hdesc`, `h_normal`) live in `TorsionKernelRational.lean`.

**Live spine (used downstream)**: `mulByInt_isSeparable`, `hxy_mulByInt`, `hcov_mulByInt_of_xy`, `omegaCoeff_mulByInt`, and the four `kaehlerD_*_eq_*_omega` ω-lemmas (`x_gen`, `y_gen`, `alpha_pullback_x`, `alpha_pullback_y`). These are consumed across `EC/MulByInt*`, `EC/DifferentialOrd`, `EC/WronskianGeneral`, and the `WeilPairing/Pairing*` files.

**Cleanup findings**:
- (a) **Unused-in-file but live externally**: the four `kaehlerD_*_eq_*_omega` lemmas and `omegaCoeff_mulByInt` have no in-file consumer beyond the chord chain but are imported by `EC/DifferentialOrd.lean` etc. `hcov_of_xy`/`hxy_mulByInt`/`hcov_mulByInt_of_xy`/`card_torsion_ell_of_ker_deg` are terminal here (consumed only via the sibling `TorsionCardEll`/`PairingNondeg`). Nothing is dead.
- (b) **Intermediate Kähler ladder** (`weierstrassEqn_KE` … `kaehlerD_weierstrass_RHS`, `kaehlerD_addSlope/addPullback_*`) are single-use scaffolding for the two headline ω-lemmas — candidates for `private` (none are referenced outside this file), which would shrink the public surface by ~12 names.
- (c) **Moral duplication with `RouteBInduction.lean`/`SilvermanIV14.lean`**: this entire Phase A is, by the file's own docstring, a `K→F` re-statement of those `[Fintype K]`-scoped files. The honest fix is to delete the `[Fintype K]` section variable upstream and reuse, rather than maintain two copies of the III.5.2/III.5.3 chord recurrence. This is the single largest consolidation opportunity in the cluster (~15 lemmas duplicated).
- (d) Same pattern for `hcov_of_xy` vs `translateAlgEquivOfPoint_pullback_invariance_of_xy` (`PointFix.lean`) — two copies of one extensionality fact, differing only by a finiteness hypothesis.
- **Heartbeats**: two raised proofs (`kaehlerD_addPullback_x_eq_one_add_smul_omega` at **4M**, `hxy_mulByInt` at 1.6M). The 4M proof is `field_simp`+`linear_combination` heavy; worth a decomposition pass.
- **`sorry`**: none.
