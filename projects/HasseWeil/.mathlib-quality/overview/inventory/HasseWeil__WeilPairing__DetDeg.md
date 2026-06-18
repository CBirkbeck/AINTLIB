# Inventory: ./HasseWeil/WeilPairing/DetDeg.lean

**File purpose**: DET-DEG capstone (Silverman III.8.6): builds the additive symplectic form `omegaForm` from the Weil pairing via discrete logarithm, proves it alternating/nondegenerate/scaling, then derives `det(ρ_ℓ ψ) = deg ψ` and packages per-ℓ Frobenius determinant data for the Hasse-bound assembly.

**Namespace**: `HasseWeil.WeilPairing.TorsionGeometric`

**Imports**: `PairingAdjoint`, `PairingNondeg`, `Representation`, `RootsOfUnity`, `PairingDet`, `Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed`

---

## Section `AdditiveForm`

### `theorem zsmul_eq_zero_of_mem_torsion`
- **Type**: `(S : W.toAffine[((ℓ : ℕ) : ℤ)]) → ((ℓ : ℕ) : ℤ) • S.val = 0`
- **What**: A point of the ℓ-torsion subgroup `E[ℓ]` (expressed as the subgroup killed by `(ℓ:ℤ)`) has `(ℓ:ℤ)•S = 0`. Torsion bookkeeping lemma.
- **How**: Directly from `mem_torsionSubgroup` (project).
- **Hypotheses**: `W` an elliptic Weierstrass curve over `F`; `ℓ` prime.
- **Uses from project**: `mem_torsionSubgroup`
- **Used by**: `pairingRou`, `pairingRou_mul_left`, `pairingRou_mul_right`, `pairingRou_self`, `pairingRou_scaling`, `omegaForm_scaling`, `omegaForm_nondegenerate`, `linearMap_det_torsionRestrict_eq`, `det_rhoEll_eq_degree`, `WeilScales`, `frob_det_data_of_weil_scaling`, `frob_det_residual_of_weil_scaling`
- **Visibility**: public
- **Lines**: 75–76, proof length 1 line
- **Notes**: Used extensively as boilerplate throughout the file (key API).

---

### `noncomputable def pairingRou`
- **Type**: `(S T : W.toAffine[((ℓ : ℕ) : ℤ)]) → rootsOfUnity ℓ F`
- **What**: Packages the Weil pairing value `e_ℓ(S,T)` as an element of `μ_ℓ = rootsOfUnity ℓ F`, using the fact that `e_ℓ(S,T)^ℓ = 1` (`weilPairing_pow_eq_one`).
- **How**: Calls `rootsOfUnity.mkOfPowEq` with the nonzero `weilPairing` value and the `weilPairing_pow_eq_one` proof (after a `simpa` to match `ℕ` vs `ℤ.natAbs`).
- **Hypotheses**: `[IsAlgClosed F]`, `hℓF : (ℓ : F) ≠ 0`
- **Uses from project**: `weilPairing`, `weilPairing_pow_eq_one`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `pairingRou_coe`, `pairingRou_mul_left`, `pairingRou_mul_right`, `pairingRou_self`, `pairingRou_scaling`, `omegaFun`, `omegaForm_antisymm`
- **Visibility**: public
- **Lines**: 87–94, proof ~6 lines
- **Notes**: None.

---

### `theorem pairingRou_coe`
- **Type**: `((pairingRou W ℓ hℓF S T : Fˣ) : F) = weilPairing W ((ℓ : ℕ) : ℤ) ... S.val T.val ...`
- **What**: The underlying `F`-value of `pairingRou S T` equals the Weil pairing `e_ℓ(S,T)`.
- **How**: `rfl` after setting `NeZero ℓ`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `pairingRou`, `weilPairing`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `pairingRou_mul_left`, `pairingRou_mul_right`, `pairingRou_self`, `pairingRou_scaling`, `omegaForm_antisymm`, `omegaForm_nondegenerate`
- **Visibility**: public
- **Lines**: 97–102, proof 2 lines
- **Notes**: None.

---

### `theorem pairingRou_mul_left`
- **Type**: `pairingRou W ℓ hℓF (S₁ + S₂) T = pairingRou W ℓ hℓF S₁ T * pairingRou W ℓ hℓF S₂ T`
- **What**: `μ_ℓ`-valued Weil pairing is multiplicative (bimultiplicative) in the first slot.
- **How**: Reduces via `pairingRou_coe` to the `weilPairing_mul_left` statement on raw field values.
- **Hypotheses**: `hℓF`
- **Uses from project**: `pairingRou_coe`, `weilPairing_mul_left`
- **Used by**: `omegaFun_add_left`
- **Visibility**: public
- **Lines**: 105–109, proof 4 lines
- **Notes**: None.

---

### `theorem pairingRou_mul_right`
- **Type**: `pairingRou W ℓ hℓF S (T₁ + T₂) = pairingRou W ℓ hℓF S T₁ * pairingRou W ℓ hℓF S T₂`
- **What**: `μ_ℓ`-valued Weil pairing is multiplicative in the second slot.
- **How**: Same pattern as `pairingRou_mul_left`, using `weilPairing_mul_right`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `pairingRou_coe`, `weilPairing_mul_right`
- **Used by**: `omegaFun_add_right`
- **Visibility**: public
- **Lines**: 112–116, proof 4 lines
- **Notes**: None.

---

### `noncomputable def primRou`
- **Type**: `Fˣ` (a unit of `F`)
- **What**: A primitive `ℓ`-th root of unity in `Fˣ`, chosen from `HasEnoughRootsOfUnity` (which holds since `F` is algebraically closed and `(ℓ:F) ≠ 0`).
- **How**: Extracts via `HasEnoughRootsOfUnity.exists_primitiveRoot` and `.isUnit`.
- **Hypotheses**: `[IsAlgClosed F]`, `hℓF`
- **Uses from project**: (none; uses Mathlib `HasEnoughRootsOfUnity`)
- **Used by**: `primRou_isPrimitiveRoot`, `logRou`
- **Visibility**: public
- **Lines**: 125–129, def body 4 lines
- **Notes**: `omit [DecidableEq F] in` applied to the next theorem.

---

### `theorem primRou_isPrimitiveRoot`
- **Type**: `IsPrimitiveRoot (primRou (F := F) ℓ hℓF) ℓ`
- **What**: The chosen unit `primRou` is actually a primitive `ℓ`-th root of unity.
- **How**: Directly from `HasEnoughRootsOfUnity.exists_primitiveRoot ... .isUnit_unit`.
- **Hypotheses**: `hℓF` (but `omit [DecidableEq F]`)
- **Uses from project**: `primRou`
- **Used by**: `logRou`, `omegaForm_nondegenerate`
- **Visibility**: public
- **Lines**: 132–135, proof 3 lines
- **Notes**: Uses `omit [DecidableEq F] in` — DecidableEq not needed.

---

### `noncomputable def logRou`
- **Type**: `Additive (rootsOfUnity ℓ F) →+ ZMod ℓ`
- **What**: The discrete logarithm map `μ_ℓ → ℤ/ℓ` with respect to the chosen primitive root, as an additive group homomorphism (via the canonical `AddEquiv` `rootsOfUnity_addEquiv_zmod`).
- **How**: Takes the `AddEquiv.toAddMonoidHom` of `rootsOfUnity_addEquiv_zmod` applied to `primRou_isPrimitiveRoot`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `primRou_isPrimitiveRoot`
- **Used by**: `logRou_mul`, `omegaFun`, `omegaForm_nondegenerate`
- **Visibility**: public
- **Lines**: 139–141, def body 2 lines
- **Notes**: None.

---

### `theorem logRou_mul`
- **Type**: `logRou ℓ hℓF (Additive.ofMul (a * b)) = logRou ℓ hℓF (Additive.ofMul a) + logRou ℓ hℓF (Additive.ofMul b)`
- **What**: The discrete log sends multiplication to addition: `log(ζ₁·ζ₂) = log ζ₁ + log ζ₂`.
- **How**: `← map_add`, then `rfl` (additive group homomorphism).
- **Hypotheses**: `hℓF`
- **Uses from project**: `logRou`
- **Used by**: `omegaFun_add_left`, `omegaFun_add_right`, `omegaForm_antisymm`
- **Visibility**: public
- **Lines**: 144–148, proof 3 lines
- **Notes**: None.

---

### `noncomputable def omegaFun`
- **Type**: `(S T : W.toAffine[((ℓ : ℕ) : ℤ)]) → ZMod ℓ`
- **What**: The discrete-log Weil pairing `ω(S,T) = log e_ℓ(S,T) ∈ ZMod ℓ`; the additive version of the multiplicative Weil pairing.
- **How**: Defined as `logRou ℓ hℓF (Additive.ofMul (pairingRou W ℓ hℓF S T))`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `logRou`, `pairingRou`
- **Used by**: `omegaFun_add_left`, `omegaFun_add_right`, `omegaRightHom`, `omegaRightLin_apply`, `omegaForm_apply`, `omegaForm_self`, `omegaForm_nondegenerate`, `pairingRou_scaling`, `omegaForm_antisymm`
- **Visibility**: public
- **Lines**: 156–157, def body 1 line
- **Notes**: Central intermediate definition; key API node.

---

### `theorem omegaFun_add_left`
- **Type**: `omegaFun W ℓ hℓF (S₁ + S₂) T = omegaFun W ℓ hℓF S₁ T + omegaFun W ℓ hℓF S₂ T`
- **What**: `omegaFun` is additive in the first slot.
- **How**: Unfolds `omegaFun`, then applies `pairingRou_mul_left` and `logRou_mul`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaFun`, `pairingRou_mul_left`, `logRou_mul`
- **Used by**: `omegaLeftHom`, `omegaForm` (via `omegaLeftHom`)
- **Visibility**: public
- **Lines**: 159–162, proof 3 lines
- **Notes**: None.

---

### `theorem omegaFun_add_right`
- **Type**: `omegaFun W ℓ hℓF S (T₁ + T₂) = omegaFun W ℓ hℓF S T₁ + omegaFun W ℓ hℓF S T₂`
- **What**: `omegaFun` is additive in the second slot.
- **How**: Same pattern: `pairingRou_mul_right` and `logRou_mul`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaFun`, `pairingRou_mul_right`, `logRou_mul`
- **Used by**: `omegaRightHom`
- **Visibility**: public
- **Lines**: 164–167, proof 3 lines
- **Notes**: None.

---

### `noncomputable def omegaRightHom`
- **Type**: `(S : W.toAffine[((ℓ : ℕ) : ℤ)]) → (W.toAffine[((ℓ : ℕ) : ℤ)] →+ ZMod ℓ)`
- **What**: For fixed `S`, the additive group homomorphism `T ↦ ω(S,T)`.
- **How**: Defines `map_zero'` via `omegaFun_add_right` (add 0+0, then `linear_combination`); `map_add'` = `omegaFun_add_right`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaFun`, `omegaFun_add_right`
- **Used by**: `omegaRightLin`
- **Visibility**: public
- **Lines**: 170–177, def body 7 lines
- **Notes**: None.

---

### `noncomputable def omegaRightLin`
- **Type**: `(S : W.toAffine[((ℓ : ℕ) : ℤ)]) → (W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ)`
- **What**: For fixed `S`, the `ZMod ℓ`-linear map `T ↦ ω(S,T)`, obtained from the additive hom by `AddMonoidHom.toZModLinearMap`.
- **How**: `(omegaRightHom W ℓ hℓF S).toZModLinearMap ℓ`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaRightHom`
- **Used by**: `omegaRightLin_apply`, `omegaLeftHom`, `omegaForm`
- **Visibility**: public
- **Lines**: 180–182, def body 2 lines
- **Notes**: None.

---

### `@[simp] theorem omegaRightLin_apply`
- **Type**: `omegaRightLin W ℓ hℓF S T = omegaFun W ℓ hℓF S T`
- **What**: `omegaRightLin` applied to `T` equals `omegaFun S T`.
- **How**: `rfl`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaRightLin`, `omegaFun`
- **Used by**: `omegaLeftHom`, `omegaForm_apply`
- **Visibility**: public (`@[simp]`)
- **Lines**: 184–185, proof 1 line
- **Notes**: None.

---

### `noncomputable def omegaLeftHom`
- **Type**: `W.toAffine[((ℓ : ℕ) : ℤ)] →+ (W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ)`
- **What**: The additive group homomorphism `S ↦ (T ↦ ω(S,T))` into the linear dual space.
- **How**: `map_zero'` uses `omegaFun_add_left` at `(0,0,T)` + `linear_combination`; `map_add'` uses `omegaFun_add_left` via `omegaRightLin_apply`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaFun_add_left`, `omegaRightLin`, `omegaRightLin_apply`
- **Used by**: `omegaForm`
- **Visibility**: public
- **Lines**: 188–200, def body 12 lines
- **Notes**: None.

---

### `noncomputable def omegaForm`
- **Type**: `W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] (W.toAffine[((ℓ : ℕ) : ℤ)] →ₗ[ZMod ℓ] ZMod ℓ)`
- **What**: **The additive symplectic form ω** on `E[ℓ]`: the `ZMod ℓ`-bilinear form obtained as the discrete log of the Weil pairing.
- **How**: `(omegaLeftHom W ℓ hℓF).toZModLinearMap ℓ`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaLeftHom`
- **Used by**: `omegaForm_apply`, `omegaForm_self`, `omegaForm_nondegenerate`, `omegaForm_scaling`, `omegaForm_antisymm`, `omegaForm_gram_ne_zero`, `linearMap_det_torsionRestrict_eq`
- **Visibility**: public
- **Lines**: 206–209, def body 2 lines
- **Notes**: Key API — referenced by `linearMap_det_torsionRestrict_eq` as the symplectic form passed to `det_eq_of_alternating_scaling`.

---

### `@[simp] theorem omegaForm_apply`
- **Type**: `omegaForm W ℓ hℓF S T = omegaFun W ℓ hℓF S T`
- **What**: `omegaForm` applied to `(S, T)` equals `omegaFun S T`.
- **How**: `rfl`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaForm`, `omegaFun`
- **Used by**: `omegaForm_self`, `omegaForm_scaling`, `omegaForm_antisymm`, `omegaForm_nondegenerate`, `omegaForm_gram_ne_zero`
- **Visibility**: public (`@[simp]`)
- **Lines**: 211–212, proof 1 line
- **Notes**: None.

---

### `theorem pairingRou_self`
- **Type**: `pairingRou W ℓ hℓF T T = 1`
- **What**: `e_ℓ(T,T) = 1` lifted to `μ_ℓ`, from `weilPairing_self`.
- **How**: Reduces to `F`-value equality via `pairingRou_coe` and applies `weilPairing_self`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `pairingRou_coe`, `weilPairing_self`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `omegaForm_self`
- **Visibility**: public
- **Lines**: 217–223, proof 6 lines
- **Notes**: None.

---

### `theorem omegaForm_self`
- **Type**: `omegaForm W ℓ hℓF T T = 0`
- **What**: **ω is alternating**: `ω(T,T) = 0`, the discrete log of `weilPairing_self` (`e_ℓ(T,T)=1`).
- **How**: `omegaForm_apply` + unfolds `omegaFun` + `pairingRou_self` + `map_zero`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaForm_apply`, `omegaFun`, `pairingRou_self`
- **Used by**: `linearMap_det_torsionRestrict_eq`
- **Visibility**: public
- **Lines**: 226–231, proof 5 lines
- **Notes**: None.

---

### `theorem omegaForm_nondegenerate`
- **Type**: `(∀ S, omegaForm W ℓ hℓF S T = 0) → T = 0`
- **What**: **ω is nondegenerate** in the second slot: if `ω(S,T) = 0` for all `S ∈ E[ℓ]`, then `T = 0`. Uses injectivity of `logRou` at 0 and `weilPairing_nondegenerate`.
- **How**: Injectivity of `rootsOfUnity_addEquiv_zmod` converts `logRou = 0` to `pairingRou = 1`; then `pairingRou_coe` converts to the raw pairing = 1; then `weilPairing_nondegenerate` gives `T.val = 0`; `Subtype.ext` concludes.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaForm_apply`, `omegaFun`, `logRou`, `pairingRou`, `pairingRou_coe`, `primRou_isPrimitiveRoot`, `weilPairing_nondegenerate`, `zsmul_eq_zero_of_mem_torsion`, `mem_torsionSubgroup`
- **Used by**: `omegaForm_gram_ne_zero`
- **Visibility**: public
- **Lines**: 236–266, proof 30 lines
- **Notes**: Proof is exactly 30 lines (borderline); involves careful `Additive.ofMul`/`toMul` coercions.

---

### `theorem pairingRou_scaling`
- **Type**: `pairingRou W ℓ hℓF (torsionRestrict W ℓ ψ S) (torsionRestrict W ℓ ψ T) = pairingRou W ℓ hℓF S T ^ d`
- **What**: If `e_ℓ(ψS, ψT) = e_ℓ(S,T)^d`, then `pairingRou(ψS, ψT) = pairingRou(S,T)^d` as roots of unity.
- **How**: Reduces via `pairingRou_coe` to the given hypothesis `hsc` on raw pairing values; uses `SubmonoidClass.coe_pow`/`Units.val_pow_eq_pow_val`.
- **Hypotheses**: `hℓF`; an `AddMonoidHom ψ`; the multiplicative scaling hypothesis `hsc`
- **Uses from project**: `pairingRou_coe`, `pairingRou`, `torsionRestrict`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `omegaForm_scaling`
- **Visibility**: public
- **Lines**: 276–288, proof 6 lines
- **Notes**: None.

---

### `theorem omegaForm_scaling`
- **Type**: `omegaForm W ℓ hℓF (torsionRestrict W ℓ ψ S) (torsionRestrict W ℓ ψ T) = (d : ZMod ℓ) * omegaForm W ℓ hℓF S T`
- **What**: **The additive scaling**: if `e_ℓ(ψS,ψT) = e_ℓ(S,T)^d`, then `ω(ψS,ψT) = d·ω(S,T)`. The discrete log converts `^d` to `·d`.
- **How**: `pairingRou_scaling` gives `pairingRou(ψS,ψT) = pairingRou(S,T)^d`; `Additive.ofMul (p^d) = d • Additive.ofMul p` (by `rfl`); `map_nsmul` propagates through `logRou`; `nsmul_eq_mul` converts.
- **Hypotheses**: `hℓF`; the scaling hypothesis `hsc`
- **Uses from project**: `omegaForm_apply`, `omegaFun`, `pairingRou_scaling`
- **Used by**: `linearMap_det_torsionRestrict_eq`
- **Visibility**: public
- **Lines**: 292–307, proof 15 lines
- **Notes**: None.

---

### `theorem omegaForm_antisymm`
- **Type**: `omegaForm W ℓ hℓF S T + omegaForm W ℓ hℓF T S = 0`
- **What**: **ω is antisymmetric**: `ω(S,T) + ω(T,S) = 0`, the log of `weilPairing_antisymm` (`e_ℓ(S,T)·e_ℓ(T,S)=1`).
- **How**: Combines `logRou_mul` with `weilPairing_antisymm` to show `pairingRou S T * pairingRou T S = 1`, then the log of 1 is 0.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaForm_apply`, `omegaFun`, `logRou_mul`, `pairingRou`, `pairingRou_coe`, `weilPairing_antisymm`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `omegaForm_gram_ne_zero`
- **Visibility**: public
- **Lines**: 313–324, proof 11 lines
- **Notes**: None.

---

### `theorem omegaForm_gram_ne_zero`
- **Type**: `omegaForm W ℓ hℓF (torsion_ell_basis W ℓ hℓF 0) (torsion_ell_basis W ℓ hℓF 1) ≠ 0`
- **What**: The `(0,1)` Gram entry of `ω` on the symplectic basis is nonzero, establishing that `ω` is non-degenerate on the basis.
- **How**: Assumes it is 0, derives `ω(b 0, b 1) = ω(b 1, b 0) = 0` via alternating and antisymmetry (`omegaForm_self`, `omegaForm_antisymm`), then `ω(·, b 1)` vanishes on all of `E[ℓ]` by linearity in slot 1 and the basis span, so `omegaForm_nondegenerate` forces `b 1 = 0`, contradicting `torsion_ell_basis.ne_zero`.
- **Hypotheses**: `hℓF`
- **Uses from project**: `omegaForm_apply`, `omegaForm_self`, `omegaForm_antisymm`, `omegaForm_nondegenerate`, `torsion_ell_basis`
- **Used by**: `linearMap_det_torsionRestrict_eq`
- **Visibility**: public
- **Lines**: 330–352, proof 22 lines
- **Notes**: None.

---

## Section `DetDeg`

### `theorem linearMap_det_torsionRestrict_eq`
- **Type**: `(hsc : ∀ S T, e_ℓ(ψS,ψT)=e_ℓ(S,T)^d) → LinearMap.det (torsionRestrict W ℓ ψ) = (d : ZMod ℓ)`
- **What**: **DET-DEG (module form)** (Silverman III.8.6): the determinant of any `ψ` on `E[ℓ]` (as a linear endomorphism of the `ZMod ℓ`-module `E[ℓ]`) equals `d` mod `ℓ`, given the Weil-pairing scaling by `d`.
- **How**: Calls `HasseWeil.WeilPairing.det_eq_of_alternating_scaling` (from `PairingDet`) with the basis `torsion_ell_basis`, the form `omegaForm`, the alternating property `omegaForm_self`, the nondegeneracy on the basis `omegaForm_gram_ne_zero`, the restricted endomorphism `torsionRestrict W ℓ ψ`, and the additive scaling `omegaForm_scaling` per pair.
- **Hypotheses**: `hℓF`; the pairing scaling hypothesis `hsc`
- **Uses from project**: `torsion_ell_basis`, `omegaForm`, `omegaForm_self`, `omegaForm_gram_ne_zero`, `torsionRestrict`, `omegaForm_scaling`, `zsmul_eq_zero_of_mem_torsion`, `det_eq_of_alternating_scaling` (from `PairingDet`)
- **Used by**: `det_rhoEll_eq_degree`
- **Visibility**: public
- **Lines**: 369–380, proof 4 lines
- **Notes**: None.

---

### `theorem det_rhoEll_eq_degree`
- **Type**: `(hsc : ∀ S T, e_ℓ(ψS,ψT)=e_ℓ(S,T)^d) → (rhoEll W ℓ hℓF ψ).det = (d : ZMod ℓ)`
- **What**: **DET-DEG (matrix form)**: the matrix determinant of the ρ_ℓ-representation of `ψ` equals the degree `d` mod `ℓ`. Bridges from `LinearMap.det` to the matrix `rhoEll`.
- **How**: Rewrites via `rhoEll_det` (connecting `rhoEll` determinant to `LinearMap.det`), then applies `linearMap_det_torsionRestrict_eq`.
- **Hypotheses**: `hℓF`; the pairing scaling hypothesis `hsc`
- **Uses from project**: `rhoEll`, `rhoEll_det`, `linearMap_det_torsionRestrict_eq`
- **Used by**: `frob_det_data_of_weil_scaling`
- **Visibility**: public
- **Lines**: 384–393, proof 3 lines
- **Notes**: None.

---

## Section `RingHom`

### `theorem rhoEll_sub`
- **Type**: `rhoEll W ℓ hℓF (ψ₁ - ψ₂) = rhoEll W ℓ hℓF ψ₁ - rhoEll W ℓ hℓF ψ₂`
- **What**: `ρ_ℓ` respects subtraction: the matrix of the difference isogeny is the difference of matrices.
- **How**: Three `rhoEll` rewrites; `torsionRestrict` distributes over subtraction definitionally; `map_sub` on `LinearMap.toMatrix`.
- **Hypotheses**: None beyond the ambient variables.
- **Uses from project**: `rhoEll`, `torsionRestrict`
- **Used by**: `one_sub_rhoEll`, `smul_rhoEll_sub`
- **Visibility**: public
- **Lines**: 402–406, proof 4 lines
- **Notes**: No `hℓF` needed (outside `include hℓF`).

---

### `theorem rhoEll_zsmul`
- **Type**: `rhoEll W ℓ hℓF (n • ψ) = (n : ZMod ℓ) • rhoEll W ℓ hℓF ψ`
- **What**: `ρ_ℓ(n•ψ) = (n mod ℓ)·ρ_ℓ(ψ)`: the `ℤ`-scalar reduces mod `ℓ` in the matrix.
- **How**: `torsionRestrict` distributes `n •` definitionally; `map_zsmul` on `LinearMap.toMatrix`; `Int.cast_smul_eq_zsmul`.
- **Hypotheses**: None beyond the ambient variables.
- **Uses from project**: `rhoEll`, `torsionRestrict`
- **Used by**: `smul_rhoEll_sub`
- **Visibility**: public
- **Lines**: 409–413, proof 4 lines
- **Notes**: None.

---

### `theorem one_sub_rhoEll`
- **Type**: `1 - rhoEll W ℓ hℓF πhom = rhoEll W ℓ hℓF (AddMonoidHom.id W.toAffine.Point - πhom)`
- **What**: `ρ_ℓ(id − π) = I − ρ_ℓ(π)`: the matrix of the isogeny `1−π` is `1 − M`.
- **How**: `rhoEll_sub` + `rhoEll_id`.
- **Hypotheses**: None beyond the ambient variables.
- **Uses from project**: `rhoEll_sub`, `rhoEll_id`
- **Used by**: `frob_det_data_of_weil_scaling`
- **Visibility**: public
- **Lines**: 416–418, proof 2 lines
- **Notes**: None.

---

### `theorem smul_rhoEll_sub`
- **Type**: `(r : ZMod ℓ) • rhoEll W ℓ hℓF πhom - (s : ZMod ℓ) • 1 = rhoEll W ℓ hℓF (r • πhom - s • AddMonoidHom.id ...)`
- **What**: `ρ_ℓ(rπ − s·id) = r·ρ_ℓ(π) − s·I`: the matrix of the Frobenius pencil `rπ − s` is the linear combination of `M` and the identity matrix.
- **How**: `rhoEll_sub` + two `rhoEll_zsmul` + `rhoEll_id`.
- **Hypotheses**: None beyond the ambient variables.
- **Uses from project**: `rhoEll_sub`, `rhoEll_zsmul`, `rhoEll_id`
- **Used by**: `frob_det_data_of_weil_scaling`
- **Visibility**: public
- **Lines**: 421–424, proof 2 lines
- **Notes**: None.

---

## Section `Assembly`

### `def WeilScales`
- **Type**: `(ψ : W.toAffine.Point →+ W.toAffine.Point) → (d : ℕ) → Prop`
- **What**: The predicate `WeilScales ψ d` asserting `e_ℓ(ψS, ψT) = e_ℓ(S,T)^d` for all torsion `S, T ∈ E[ℓ]`. The standard interface between the isogeny scaling facts and the DET-DEG theorem.
- **How**: Definitional; unpacks the `weilPairing` statement with appropriate torsion proofs via `zsmul_eq_zero_of_mem_torsion`.
- **Hypotheses**: `hℓF` (via `include hℓF`)
- **Uses from project**: `weilPairing`, `zsmul_eq_zero_of_mem_torsion`
- **Used by**: `frob_det_data_of_weil_scaling`, `frob_det_residual_of_weil_scaling`; also extensively used outside this file (by `FrobMatrixData`, `SeparableScaling`, `SeparableTransportBridge`, `FrobeniusGalois`, etc.)
- **Visibility**: public
- **Lines**: 442–449, def body (no proof)
- **Notes**: Key API — used by many external files.

---

### `theorem frob_det_data_of_weil_scaling`
- **Type**: Given `WeilScales πhom dπ`, `WeilScales (id − πhom) d1`, `WeilScales (r•πhom − s•id) drs` ⟹ `M.det = dπ ∧ (1−M).det = d1 ∧ (r•M − s•1).det = drs` (all in `ZMod ℓ`)
- **What**: **The three Frobenius det facts**: packages the three DET-DEG conclusions for the Frobenius pencil `{π, 1−π, rπ−s}` into a triple.
- **How**: Three applications of `det_rhoEll_eq_degree`, with `one_sub_rhoEll` and `smul_rhoEll_sub` as rewrite steps (using `▸`).
- **Hypotheses**: `hℓF`; three `WeilScales` hypotheses
- **Uses from project**: `det_rhoEll_eq_degree`, `one_sub_rhoEll`, `smul_rhoEll_sub`, `rhoEll`, `WeilScales`
- **Used by**: `frob_det_residual_of_weil_scaling`
- **Visibility**: public
- **Lines**: 456–466, proof 4 lines
- **Notes**: None.

---

### `theorem frob_det_residual_of_weil_scaling`
- **Type**: Given integer equalities `dπ = q`, `d1 = q+1−t`, `drs = Dν` and three `WeilScales` hypotheses, produces `∃ M : Matrix (Fin 2) (Fin 2) (ZMod ℓ), M.det = q ∧ (1−M).det = q+1−t ∧ (r•M − s•1).det = Dν` (in `ZMod ℓ`).
- **What**: **The per-ℓ Frobenius determinant residual** (Silverman III.8.6/V.2.3.1): the existential form consumed by `Reduction.deg_eq_of_frob_det_data` / `Assembly.qf_nonneg_of_frob_det_residual` in the Hasse bound assembly.
- **How**: Applies `frob_det_data_of_weil_scaling` to get the triple, then supplies `rhoEll W ℓ hℓF πhom` as the witness; casts between `ℕ` and `ℤ` via `push_cast; ring`.
- **Hypotheses**: `hℓF`; integer equalities `hqd`, `h1d`, `hDd`; three `WeilScales` hypotheses
- **Uses from project**: `frob_det_data_of_weil_scaling`, `rhoEll`, `WeilScales`
- **Used by**: `FrobMatrixData.lean` (external — key consumer)
- **Visibility**: public
- **Lines**: 476–489, proof 12 lines
- **Notes**: The main output theorem of the file; its `∃ M ...` form is exactly what `FrobMatrixData.frob_matrix_data_of_baseChange` calls.

---

## Summary table

| Name | Kind | Lines | Sorries |
|---|---|---|---|
| `zsmul_eq_zero_of_mem_torsion` | theorem | 75–76 | 0 |
| `pairingRou` | noncomputable def | 87–94 | 0 |
| `pairingRou_coe` | theorem | 97–102 | 0 |
| `pairingRou_mul_left` | theorem | 105–109 | 0 |
| `pairingRou_mul_right` | theorem | 112–116 | 0 |
| `primRou` | noncomputable def | 125–129 | 0 |
| `primRou_isPrimitiveRoot` | theorem | 132–135 | 0 |
| `logRou` | noncomputable def | 139–141 | 0 |
| `logRou_mul` | theorem | 144–148 | 0 |
| `omegaFun` | noncomputable def | 156–157 | 0 |
| `omegaFun_add_left` | theorem | 159–162 | 0 |
| `omegaFun_add_right` | theorem | 164–167 | 0 |
| `omegaRightHom` | noncomputable def | 170–177 | 0 |
| `omegaRightLin` | noncomputable def | 180–182 | 0 |
| `omegaRightLin_apply` | theorem | 184–185 | 0 |
| `omegaLeftHom` | noncomputable def | 188–200 | 0 |
| `omegaForm` | noncomputable def | 206–209 | 0 |
| `omegaForm_apply` | theorem | 211–212 | 0 |
| `pairingRou_self` | theorem | 217–223 | 0 |
| `omegaForm_self` | theorem | 226–231 | 0 |
| `omegaForm_nondegenerate` | theorem | 236–266 | 0 |
| `pairingRou_scaling` | theorem | 276–288 | 0 |
| `omegaForm_scaling` | theorem | 292–307 | 0 |
| `omegaForm_antisymm` | theorem | 313–324 | 0 |
| `omegaForm_gram_ne_zero` | theorem | 330–352 | 0 |
| `linearMap_det_torsionRestrict_eq` | theorem | 369–380 | 0 |
| `det_rhoEll_eq_degree` | theorem | 384–393 | 0 |
| `rhoEll_sub` | theorem | 402–406 | 0 |
| `rhoEll_zsmul` | theorem | 409–413 | 0 |
| `one_sub_rhoEll` | theorem | 416–418 | 0 |
| `smul_rhoEll_sub` | theorem | 421–424 | 0 |
| `WeilScales` | def | 442–449 | 0 |
| `frob_det_data_of_weil_scaling` | theorem | 456–466 | 0 |
| `frob_det_residual_of_weil_scaling` | theorem | 476–489 | 0 |

**Totals**: 34 declarations (11 defs, 23 theorems, 0 instances), 0 sorries.

**Key API** (used by 3+ others in file): `zsmul_eq_zero_of_mem_torsion` (used by ~10), `omegaFun` (used by ~8), `omegaForm` (used by ~8), `pairingRou_coe` (used by ~5), `omegaForm_apply` (used by ~6), `WeilScales` (used by 3 in file + many external).

**Long proofs** (>30 lines): none strictly (longest is `omegaForm_nondegenerate` at exactly 30 lines).

**Unused in file**: `pairingRou_mul_left`, `pairingRou_mul_right`, `logRou_mul`, `omegaFun_add_left`, `omegaFun_add_right`, `omegaRightHom`, `omegaRightLin`, `omegaRightLin_apply`, `omegaLeftHom`, `omegaForm_antisymm`, `primRou`, `primRou_isPrimitiveRoot` — these are all used indirectly (as intermediate steps in `omegaForm`'s construction) or are potentially public API. Declarations used only as building blocks in the construction chain but not by the section-level theorems: `pairingRou_mul_left`/`right`, `omegaFun_add_left`/`right`, etc.

**No `set_option maxHeartbeats` in file.**
