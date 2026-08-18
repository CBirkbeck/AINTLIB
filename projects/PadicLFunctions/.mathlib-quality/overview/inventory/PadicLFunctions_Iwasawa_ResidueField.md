# Inventory: PadicLFunctions/Iwasawa/ResidueField.lean

File concerns the residue field of `𝒪_n = O p n` (always `𝔽_p` since `K_n/ℚ_p` is totally ramified), norm-residue compatibility, the `ℤ_p`-residue of tower units, the Teichmüller `NormCompatUnits` system `ω(b)`, and the §12.1 Teichmüller split `𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}`.

---

### theorem prod_sub_one_lt_one
- Type: `{ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (hle : ∀ i ∈ s, ‖f i‖ ≤ 1) (hone : ∀ i ∈ s, ‖f i - 1‖ < 1) : ‖(∏ i ∈ s, f i) - 1‖ < 1`
- What: A finite product of `ℂ_p`-elements that are each norm-`≤ 1` and each within distance `< 1` of `1` is itself within distance `< 1` of `1`.
- How: `Finset.induction` on `s`; the insert step rewrites `f a * P - 1 = f a * (P - 1) + (f a - 1)` and bounds via the ultrametric `IsUltrametricDist.norm_add_le_max` with `max_lt`, using `norm_mul` and `mul_le_mul_of_nonneg_right` for the product term.
- Hypotheses: each factor has norm `≤ 1`; each factor is a principal unit (`‖f i − 1‖ < 1`).
- Uses from project: []
- Used by: `norm_levelNorm_sub_one_lt_one`
- Visibility: private
- Lines: 43–59 (proof ~14 lines)
- Notes: none

### def restrictAbsES
- Type: `{n : ℕ} : AbsoluteValue (IntermediateField.extendScalars (K_le_succ p n)) ℝ` (via `where`: `toFun z := ‖(z : ℂ_[p])‖`)
- What: The absolute value on the intermediate field `extendScalars (K_le_succ p n)` (i.e. `K_{n+1}` viewed over `K_n`) given by the ambient `ℂ_p`-norm of the coercion.
- How: Bundles `toFun := ‖(·:ℂ_[p])‖` into `AbsoluteValue`; multiplicativity via `push_cast`/`norm_mul`, nonnegativity via `norm_nonneg`, definiteness via `norm_eq_zero` + cast injectivity, triangle via `norm_add_le`.
- Hypotheses: a level `n` (implicit); relies on `K_le_succ p n : K p n ≤ K p (n+1)` for `extendScalars`.
- Uses from project: `K_le_succ`
- Used by: `norm_coe_eq_spectralNorm_ES`
- Visibility: private
- Lines: 61–68 (proof ~7 lines bundled)
- Notes: none

### theorem norm_coe_eq_spectralNorm_ES
- Type: `{n : ℕ} (z : IntermediateField.extendScalars (K_le_succ p n)) : ‖(z : ℂ_[p])‖ = spectralNorm ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) z`
- What: On `extendScalars (K_le_succ p n)` the ambient `ℂ_p`-norm of the coercion equals the spectral norm over `ℚ_p`.
- How: Supplies `FiniteDimensional ℚ_[p] _` via `finiteDimensional_K p (n+1)`, then invokes `spectralNorm_unique_field_norm_ext` with the bundled `restrictAbsES`; the side goal that the abs value restricts to `ℚ_p`'s norm is closed by rewriting `algebraMap` through `IntermediateField.algebraMap_apply` and `simp`.
- Hypotheses: a level `n`; finite-dimensionality of `K_{n+1}/ℚ_p`.
- Uses from project: `K_le_succ`, `finiteDimensional_K`, `restrictAbsES`
- Used by: `norm_algEquiv_ES`
- Visibility: private
- Lines: 70–83 (proof ~8 lines)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`

### theorem norm_algEquiv_ES
- Type: `{n : ℕ} (σ : extendScalars (K_le_succ p n) ≃ₐ[ℚ_[p]] extendScalars (K_le_succ p n)) (z : …) : ‖(σ z : ℂ_[p])‖ = ‖(z : ℂ_[p])‖`
- What: Every `ℚ_p`-algebra automorphism of `K_{n+1}` is an isometry for the ambient `ℂ_p`-norm.
- How: Rewrites both sides via `norm_coe_eq_spectralNorm_ES`, unfolds `spectralNorm`, and applies `minpoly.algEquiv_eq σ z` (an automorphism preserves the minimal polynomial, hence the spectral norm).
- Hypotheses: a level `n`; `σ` a `ℚ_p`-algebra automorphism of the extension.
- Uses from project: `K_le_succ`, `norm_coe_eq_spectralNorm_ES`
- Used by: `norm_levelNorm_sub_one_lt_one`
- Visibility: private
- Lines: 85–94 (proof ~2 lines)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`

### theorem norm_levelNorm_sub_one_lt_one
- Type: `{n : ℕ} {w : ℂ_[p]} (hw : w ∈ K p (n + 1)) (hwone : ‖w - 1‖ < 1) : ‖levelNorm p n w - 1‖ < 1`
- What: Norm-residue compatibility — the relative norm `N_{n+1,n}` of a principal unit is principal: if `‖w−1‖<1` then `‖N(w)−1‖<1`.
- How: Sets up the Galois tower (`finiteDimensional_K`, `isGalois_K`, `IsGalois.tower_top_of_isGalois`), shows `‖w‖=1` via ultrametric squeeze, expands the norm as `Algebra.norm_eq_prod_automorphisms (K p n) W` and coerces to `ℂ_p` via `levelNorm_apply`/`IntermediateField.coe_prod`, then closes by `prod_sub_one_lt_one` whose two side conditions use `norm_algEquiv_ES` on `σ.restrictScalars ℚ_[p]`.
- Hypotheses: `w ∈ K_{n+1}`; `w` a principal unit (`‖w−1‖<1`). `p` need not be odd here.
- Uses from project: `K_le_succ`, `finiteDimensional_K`, `isGalois_K`, `K`, `levelNorm`, `levelNorm_apply`, `prod_sub_one_lt_one`, `norm_algEquiv_ES`
- Used by: `toZMod_residueZp_succ`
- Visibility: public
- Lines: 99–144 (proof ~40 lines)
- Notes: long(30-50); `set_option synthInstance.maxHeartbeats 1000000`

### def residueZp
- Type: `(u : NormCompatUnits p) (n : ℕ) (hn : 1 ≤ n) : ℤ_[p]`
- What: The `ℤ_p`-residue of `u.elems n`: the chosen `a` with `‖u.elems n − toCp a‖ ≤ ‖π_n‖`, extracted via `exists_residue_pi`.
- How: `.choose` of `exists_residue_pi p hn …` applied to the membership facts `(Subring.mem_inf.1 (u.mem n)).1/.2` (the `K_n`-membership and norm-`≤1` parts).
- Hypotheses: `u` a norm-compatible tower-unit system; level `n ≥ 1`.
- Uses from project: `NormCompatUnits`, `exists_residue_pi`
- Used by: `residueZp_spec`, `toZMod_residueZp_succ`, `toZMod_residueZp_eq_one`, `norm_residueZp`, `teichUnit`, `norm_elems_sub_omega_lt_one`
- Visibility: private
- Lines: 146–147 (proof n/a, def)
- Notes: none

### theorem residueZp_spec
- Type: `(u : NormCompatUnits p) (n : ℕ) (hn : 1 ≤ n) : ‖(u.elems n : ℂ_[p]) - toCp p (residueZp p u n hn)‖ ≤ ‖pi p n‖`
- What: The defining property of `residueZp`: `u.elems n` is within `‖π_n‖` of `toCp(residueZp u n)`.
- How: `.choose_spec` of the same `exists_residue_pi` application.
- Hypotheses: `u` a tower-unit system; level `n ≥ 1`.
- Uses from project: `NormCompatUnits`, `residueZp`, `toCp`, `pi`, `exists_residue_pi`
- Used by: `toZMod_residueZp_succ`, `norm_residueZp`, `norm_elems_sub_omega_lt_one`
- Visibility: private
- Lines: 149–152 (proof n/a, term-mode)
- Notes: none

### theorem toZMod_residueZp_succ
- Type: `(u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) (hn1 : 1 ≤ n + 1) : PadicInt.toZMod (residueZp p u (n + 1) hn1) = PadicInt.toZMod (residueZp p u n hn)`
- What: One constancy step: the mod-`p` residue of the level-`(n+1)` Teichmüller residue equals that of the level-`n` residue.
- How: Writes `c = u.elems (n+1)`, factors `c = toCp a₁ · w` with `w` principal, computes `levelNorm p n c = (toCp a₁)^p · levelNorm p n w` via `levelNorm_mul` + `levelNorm_const_eq_pow`; combines with `compat`, `norm_levelNorm_sub_one_lt_one` and `norm_pi_lt_one` to get `‖a₀ − a₁^p‖ < 1`, lifts to the maximal ideal (`PadicInt.maximalIdeal_eq_span_p`, `PadicInt.ker_toZMod`), and finishes with `ZMod.pow_card` (Fermat `a^p ≡ a`).
- Hypotheses: `u` a tower-unit system; `n ≥ 1` (so `n+1 ≥ 2`); requires `p` odd implicitly via `levelNorm_const_eq_pow`.
- Uses from project: `NormCompatUnits`, `residueZp`, `residueZp_spec`, `toCp`, `K`, `O`, `pi`, `norm_pi_lt_one`, `norm_eq_one_of_mem_localUnits`, `mem_localUnits_iff`, `levelNorm`, `levelNorm_mul`, `levelNorm_const_eq_pow`, `norm_levelNorm_sub_one_lt_one`, `norm_toCp`
- Used by: `toZMod_residueZp_eq_one`
- Visibility: private
- Lines: 154–215 (proof ~60 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem toZMod_residueZp_eq_one
- Type: `(u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) : PadicInt.toZMod (residueZp p u n hn) = PadicInt.toZMod (residueZp p u 1 (le_refl 1))`
- What: Norm-residue constancy: `toZMod(residueZp u n)` is constant for all `n ≥ 1`, equal to its value at `n = 1`.
- How: Induction on `n`; in the successor case splits on `1 < m+1` vs `m+1 ≤ 1`, applying `toZMod_residueZp_succ` then the IH for the former, and `congr 1` at the base `m = 0`.
- Hypotheses: `u` a tower-unit system; `n ≥ 1`.
- Uses from project: `NormCompatUnits`, `residueZp`, `toZMod_residueZp_succ`
- Used by: `norm_elems_sub_omega_lt_one`
- Visibility: private
- Lines: 217–228 (proof ~8 lines)
- Notes: none

### def omegaNCU
- Type: `(b : ℤ_[p]ˣ) : NormCompatUnits p` (via `where` with fields `elems`, `mem`, `inv_mem`, `compat`)
- What: The constant Teichmüller `NormCompatUnits` system `ω(b)`: every level is `toCp(teichmuller b)` as a unit, parallel to `FundamentalSequence.teichNCU`.
- How: `elems` = `Units.map (toCp p)` of the Teichmüller unit `(isUnit_teichmullerFun p b).unit`; `mem`/`inv_mem` via `Subring.mem_inf` (membership in `K_n` by `algebraMap_mem`, norm-`≤1` by `norm_toCp` + `PadicInt.norm_le_one`); `compat` via `levelNorm_const_eq_pow` then collapsing `t^p = t^{p-1}·t = t` using `teichmullerFun_pow_card_sub_one`.
- Hypotheses: a unit `b : ℤ_[p]ˣ`.
- Uses from project: `NormCompatUnits`, `toCp`, `O`, `K`, `levelNorm`, `levelNorm_const_eq_pow`, `norm_toCp`
- Used by: `omegaNCU_torsion`, `omegaNCU_elems`, `normCompat_eq_teichmuller_mul_principal`
- Visibility: public
- Lines: 230–263 (proof ~30 lines bundled across 4 fields)
- Notes: none (largest field proof < 20 lines)

### theorem omegaNCU_torsion
- Type: `(b : ℤ_[p]ˣ) (n : ℕ) : (omegaNCU p b).elems n ^ (p - 1) = 1`
- What: `ω(b)` is `(p−1)`-torsion at every level.
- How: `Units.ext`, push to `ℂ_p`-value `(toCp (teichmuller b))^(p-1)`, then `map_pow` + `PadicInt.teichmullerFun_pow_card_sub_one`.
- Hypotheses: a unit `b`; any level `n`.
- Uses from project: `omegaNCU`, `toCp`
- Used by: `normCompat_eq_teichmuller_mul_principal`
- Visibility: public
- Lines: 265–270 (proof ~4 lines)
- Notes: none

### theorem omegaNCU_elems
- Type: `(b : ℤ_[p]ˣ) (n : ℕ) : ((omegaNCU p b).elems n : ℂ_[p]) = toCp p (PadicInt.teichmullerFun p (b : ℤ_[p]))`
- What: The `ℂ_p`-value of `ω(b)` at any level is `toCp(teichmuller b)`.
- How: Unfolds the `elems` field (`change`) and rewrites `IsUnit.unit_spec`.
- Hypotheses: a unit `b`; any level `n`.
- Uses from project: `omegaNCU`, `toCp`
- Used by: `normCompat_eq_teichmuller_mul_principal`
- Visibility: public
- Lines: 272–276 (proof ~2 lines)
- Notes: none

### theorem norm_residueZp
- Type: `(u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) : ‖residueZp p u n hn‖ = 1`
- What: The `ℤ_p`-residue of a tower unit is itself a unit (`ℤ_p`-norm `= 1`).
- How: `u.elems n` has norm `1` (it lies in `localUnits`); `residueZp` is within `< 1` of it (`residueZp_spec` + `norm_pi_lt_one`); the ultrametric `norm_add_le_max` squeeze forces `‖toCp(residueZp)‖ = 1`, hence `‖residueZp‖ = 1` via `norm_toCp`.
- Hypotheses: `u` a tower-unit system; level `n ≥ 1`.
- Uses from project: `NormCompatUnits`, `residueZp`, `residueZp_spec`, `toCp`, `norm_toCp`, `norm_eq_one_of_mem_localUnits`, `mem_localUnits_iff`, `norm_pi_lt_one`
- Used by: `teichUnit`
- Visibility: private
- Lines: 278–292 (proof ~14 lines)
- Notes: none

### def teichUnit
- Type: `(u : NormCompatUnits p) : ℤ_[p]ˣ`
- What: The level-`1` residue `residueZp u 1` packaged as a `ℤ_p`-unit (the residue Teichmüller lift `b`).
- How: `.unit` of `PadicInt.isUnit_iff.2 (norm_residueZp p u (le_refl 1))`.
- Hypotheses: `u` a tower-unit system.
- Uses from project: `NormCompatUnits`, `residueZp` (implicitly via `norm_residueZp`), `norm_residueZp`
- Used by: `teichUnit_val`, `norm_elems_sub_omega_lt_one`, `normCompat_eq_teichmuller_mul_principal`
- Visibility: private
- Lines: 294–295 (proof n/a, def)
- Notes: none

### theorem teichUnit_val
- Type: `(u : NormCompatUnits p) : (teichUnit p u : ℤ_[p]) = residueZp p u 1 (le_refl 1)`
- What: The underlying `ℤ_p`-element of `teichUnit u` is the level-`1` residue.
- How: `IsUnit.unit_spec`.
- Hypotheses: `u` a tower-unit system.
- Uses from project: `NormCompatUnits`, `teichUnit`, `residueZp`
- Used by: `norm_elems_sub_omega_lt_one`
- Visibility: private
- Lines: 297–298 (proof n/a, term-mode)
- Notes: none

### theorem norm_elems_sub_omega_lt_one
- Type: `(u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) : ‖(u.elems n : ℂ_[p]) - toCp p (PadicInt.teichmullerFun p (teichUnit p u : ℤ_[p]))‖ < 1`
- What: At every level `n ≥ 1`, `u.elems n` is within `< 1` of the constant Teichmüller value `toCp(teichmuller b)` (`b = teichUnit u`), the principal-part estimate.
- How: `u.elems n` is `< 1` from `toCp a₀` (`residueZp_spec`); `toZMod a₀ = toZMod b` (`toZMod_residueZp_eq_one` + `teichUnit_val`) gives equal Teichmüller lifts, and `toCp a₀` is `< 1` from `toCp(teichmuller b)` via `teichmullerFun_sub_self_mem`; combine by ultrametric `max_lt`.
- Hypotheses: `u` a tower-unit system; level `n ≥ 1`.
- Uses from project: `NormCompatUnits`, `residueZp`, `residueZp_spec`, `teichUnit`, `teichUnit_val`, `toZMod_residueZp_eq_one`, `toCp`, `norm_toCp`, `norm_pi_lt_one`
- Used by: `normCompat_eq_teichmuller_mul_principal`
- Visibility: private
- Lines: 300–320 (proof ~20 lines)
- Notes: none

### theorem normCompat_eq_teichmuller_mul_principal
- Type: `(u : NormCompatUnits p) : ∃ v w : NormCompatUnits p, w ∈ unitsTower1 p ∧ (∀ n, (v.elems n) ^ (p - 1) = 1) ∧ u = v * w`
- What: RJW §12.1 Teichmüller split `𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}`: every tower unit `u` factors as `u = v·w` with `v = ω(b)` `(p−1)`-torsion (`b = residueZp u 1`) and `w` principal (`∈ unitsTower1`).
- How: Take `v = omegaNCU p (teichUnit p u)`, `w = v⁻¹·u`; torsion of `v` is `omegaNCU_torsion`; membership `w ∈ unitsTower1` reduces via `mem_localUnitsOne_iff`/`mem_localUnits_iff` to `‖ζ⁻¹·u.elems n − 1‖ < 1` (with `ζ = toCp(teichmuller b)`, `‖ζ‖=1`), discharged by `norm_elems_sub_omega_lt_one`; the equation `u = v·w` by `mul_inv_cancel`.
- Hypotheses: `u` a tower-unit system.
- Uses from project: `NormCompatUnits`, `unitsTower1`, `teichUnit`, `omegaNCU`, `omegaNCU_torsion`, `omegaNCU_elems`, `toCp`, `norm_toCp`, `norm_elems_sub_omega_lt_one`, `mem_localUnitsOne_iff`, `mem_localUnits_iff`
- Used by: unused in file
- Visibility: public
- Lines: 322–351 (proof ~26 lines)
- Notes: none

---

## File Summary

- **Total declarations: 16** — 4 defs (`restrictAbsES`, `residueZp`, `omegaNCU`, `teichUnit`) / 11 lemmas+theorems (`prod_sub_one_lt_one`, `norm_coe_eq_spectralNorm_ES`, `norm_algEquiv_ES`, `norm_levelNorm_sub_one_lt_one`, `residueZp_spec`, `toZMod_residueZp_succ`, `toZMod_residueZp_eq_one`, `omegaNCU_torsion`, `omegaNCU_elems`, `norm_residueZp`, `teichUnit_val`, `norm_elems_sub_omega_lt_one`, `normCompat_eq_teichmuller_mul_principal` — note 13 theorem-kind, count given as defs+theorems = 4+12=16) / 0 instances.
  - Correction for clarity: 4 defs + 12 lemmas/theorems + 0 instances = 16 decls.
- **Key API (used by ≥3 in file):** `residueZp` (used by 6); `residueZp_spec` (used by 3 directly, more transitively). Project-external heavy hitters referenced repeatedly: `toCp`, `norm_toCp`, `levelNorm`, `K`, `K_le_succ`.
- **Unused in file (terminal/public exports):** `norm_levelNorm_sub_one_lt_one` (re-exported API), `omegaNCU_elems` (used only inside the final theorem — actually used), `normCompat_eq_teichmuller_mul_principal` (the file's top-level deliverable, no in-file consumer). Truly unused-in-file: `normCompat_eq_teichmuller_mul_principal`. All other private decls are consumed internally.
- **Decls with `sorry`: none.**
- **`set_option` present:** `synthInstance.maxHeartbeats 1000000` on three decls — `norm_coe_eq_spectralNorm_ES`, `norm_algEquiv_ES`, `norm_levelNorm_sub_one_lt_one`.
- **Proofs > 50 lines (count: 1):** `toZMod_residueZp_succ` (~60 lines, lines 154–215) — flagged OVER-50, needs `/decompose-proof`.
- **Proofs 30–50 lines (count: 1):** `norm_levelNorm_sub_one_lt_one` (~40 lines, lines 99–144). (`omegaNCU` spans ~30 lines but split across 4 independent `where`-field proofs, none individually long.)
