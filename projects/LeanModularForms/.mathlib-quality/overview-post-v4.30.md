# Structural Overview — post v4.30 (2026-06-03)

**Scope.** `LeanModularForms/HeckeRIngs/`, `LeanModularForms/SMOObligations/`, `LeanModularForms/Eigenforms/` — 88 files, **46,376 LOC**, 2,275 declarations (≈1,145 private, ≈1,130 public).

**Build state.** Green. Toolchain `leanprover/lean4:v4.30.0`, mathlib pinned to `v4.30.0` (`@c5ea0035…`).

**Sorries.** 4 in scope, all gated to the general-`n` Shimura 3.20 development that no protected headline touches:
- `PolynomialRing.lean:970, 981` — general-`n` branch of `R_p_isPolynomialRing`
- `Newforms/MainLemma.lean:164` — gated guard
- `Newforms/CoeffSeq.lean:945` — `exists_nonzero_prime_eigenvalue` (analytic gap in Fricke chain)

**`set_option maxHeartbeats`.** None. Only two `set_option linter.unusedSimpArgs false in` remain (`DiagonalCosets.lean:677, 692`).

## Protected headlines (must stay axiom-clean `[propext, Classical.choice, Quot.sound]`)

| # | Theorem | Location |
|---|---------|----------|
| 1 | `heckeT_p_adjoint` | `HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean:689` |
| 2 | `exists_simultaneous_eigenform_basis` | `HeckeRIngs/GL2/AdjointTheoryPetersson.lean:668` |
| 3 | `strongMultiplicityOne_constMul` | `SMOObligations/StrongMultiplicityOneFull.lean:1231` |
| 4 | `strongMultiplicityOne_axiom_clean` | `SMOObligations/StrongMultiplicityOneFull.lean:1267` |

Also frequently referenced as "headline" outputs but not on the protected list: `mainLemma_charSpace_routeB` (`SMOObligations.lean:209`), `mainLemma_charSpace_of_sameLevelDivisorDecomposition` (`Eigenforms/AtkinLehner.lean:280`).

---

## 1. Executive summary

The audit identifies **five large reduction opportunities** preserving every protected headline:

1. **Newforms internal chain is two-thirds dead.** `Fricke.lean` (510), `FrickeTwist.lean` (576), `BadPrimeAdjoint.lean` (115), `BadPrimeCosets.lean` (98), `BadPrimeReduction.lean` (47), and ≈85% of `CoeffSeq.lean` (998) form a Fricke + bad-prime + L-series scaffolding that NO file outside `Newforms/` consumes. External callers (SMOObligations, Eigenforms) only use three identifiers from the whole subtree: `Newform.dirichletLift`, `Newform.eigenvalue_coprime_mul`, `Newform.eigenvalue_eq_coeff`, plus the trivially-proved (4-line) `cuspFormsOldExtended_disjoint_cuspFormsNewExtended`. **Estimated LOC removable: ≈2,100** (1346 LOC for the Fricke + bad-prime files, plus ≈750 of the L-series internals in CoeffSeq.lean that nothing outside the file uses).

2. **HeckeT_n vs MultiplicationTable: same theorems proved twice (~700 LOC).** `T_sum_ppow_mul` (formal, 27 LOC body + helpers) and `heckeT_ppow_mul` (analytic, ≈40 LOC body + helpers); `T_sum_mul` and `heckeT_n_mul`; `T_sum_mul_coprime` and `heckeT_n_mul_coprime`; `gcd_factor_prime_pow` and `gcd_eq_gcd_ordCompl_mul_pow_min`; even the same `Finset.sum_bij'` between `range(c+1) ×ˢ g'.divisors.attach` and `(g'·p^c).divisors.attach` appears in both files. A slash-action ring homomorphism `𝕋 (Gamma0_pair N) ℤ →* Module.End ℂ (ModularForm …)` already exists as `heckeRingHomCharSpace`; using it to derive the analytic identities from the formal ones is the obvious move. **Estimated LOC removable: ≈700.**

3. **`AbstractHeckeRing/` (≈3,085 LOC) is mathlib-track infrastructure.** `HeckePair`, `HeckeCoset`, `𝕋 P Z`, `decompQuot`, the degree ring homomorphism, the `IsScalarTower`-based associativity proof, and the `AntiInvolution` commutativity criterion are all pure group theory. They already use `Mathlib.GroupTheory.DoubleCoset` internally. Upstream-PRing as `Mathlib.GroupTheory.HeckeRing.*` removes ≈3.1k from the active source tree. **Estimated LOC removable from project: ≈3,085** (still in mathlib).

4. **Family sprawl in `heckeT_p` (8 variants) and `diamondOp` (8 variants).** Each variant is justified individually but the cumulative cost is large: `heckeT_p_ut`, `heckeT_p_fun`, `heckeT_p_divN`, `heckeT_p`, `heckeT_p_all`, `heckeT_ppow`, `heckeT_p_all_charRestrict`, `heckeT_ppow_charRestrict` for the operator; `diamondOpAux`, `diamondOp`, `diamondOpHom`, `diamondOpCusp`, `diamondOpCuspHom`, `diamondOp_cusp`, `diamondOp_ext`, `diamondOp_n` for the diamond. Each ships its own per-charSpace preservation + commutation proof. Folding `diamondOp_ext` and `diamondOp_n` into one definition is mechanical. **Estimated LOC removable: ≈350.**

5. **`Gamma_p_α` API in FDTransport (≈530 LOC) is shipped in 6+ near-duplicate forms.** `Gamma_p_α`, `Gamma_p_α_finiteIndex`, `_finiteIndex_in_Gamma1`, `_conjBy`, `_conjBy_spec`, `_conjBy_injective`, `_GLPos_lift_FD_smul_conjAct`, `_PSL_R_FD_finite_index_decomp`, `_PSL_R_FD_finite_index_decomp_auto`, `_PSL_R_FD_finite_index_decomp_shifted`, `_PSL_R_FD_finite_index_decomp_shifted_eq_smul`, `_fundDomain_PSL`, `_fundDomain_PSL_canonical`, `slToPslQuot_Gamma_p_α`, `slLeftMul_Gamma_p_α`. The `_auto` / `_shifted` / `_canonical` siblings are workflow artefacts (they document the order in which the proof was split, not load-bearing math). **Estimated LOC removable: ≈200.**

**Total reduction potential: ≈6,400 LOC removed from the active build path, plus ≈3,100 moved to mathlib upstream**, while keeping every protected headline `[propext, Classical.choice, Quot.sound]`.

---

## 2. Family sprawl analysis

### 2.1 Hecke operator family — 8 `heckeT_p`-flavoured definitions

| Definition | File | Purpose |
|------------|------|---------|
| `heckeT_p_ut` | `HeckeT_p.lean:103` | Coset slash sum on `(ℍ → ℂ)` |
| `heckeT_p_fun` | `HeckeT_p.lean:110` | `_ut + lower-coset slash` in `(ℍ → ℂ)` |
| `heckeT_p` | `HeckeT_p.lean:950` | Packaged as `Module.End ℂ (ModularForm …)` |
| `heckeT_p_divN` | `HeckeT_n.lean:379` | Bad-prime variant |
| `heckeT_p_all` | `HeckeT_n.lean:437` | `if Coprime p N then heckeT_p else heckeT_p_divN` |
| `heckeT_ppow` | `HeckeT_n.lean:453` | Prime-power, via recurrence |
| `heckeT_p_all_charRestrict` | `HeckeRingHomCharSpace.lean:96` | `heckeT_p_all` restricted to `modFormCharSpace k χ` |
| `heckeT_ppow_charRestrict` | `Unified/NebentypusHeckeRingHom.lean:1108` | `heckeT_ppow` restricted to `modFormCharSpace k χ` |

`heckeT_p_cusp` (cusp variant, `AdjointTheory.lean:120`), `heckeT_n_cusp` (`AdjointTheory.lean:243`), `heckeT_n_cusp_charRestrict` (`AdjointTheoryPetersson.lean:379`) double these on the cusp side. Twelve sibling definitions for "the Hecke operator at p", each shipping its own preservation/commutation lemma.

### 2.2 Diamond operator family — 8 sibling definitions

`diamondOpAux` (Gamma1Pair.lean:191), `diamondOp` (:283), `diamondOpHom` (:316), `diamondOpCusp` (:353), `diamondOpCuspHom` (:383), `diamondOp_cusp` (`AdjointTheory.lean:128`), `diamondOp_ext` (`HeckeT_n.lean:60`), `diamondOp_n` (`HeckeT_n.lean:75`). The last two have **identical bodies** modulo parameter name (`p : ℕ` vs `n : ℕ`):

```
if h : Nat.Coprime p N then diamondOp k (ZMod.unitOfCoprime p h) else 0
if h : Nat.Coprime n N then diamondOp k (ZMod.unitOfCoprime n h) else 0
```

The `_cusp`/`_ext`/`_n` split forces three near-identical commutation theorems (`diamondOp_ext_comm_diamondOp`, `diamondOp_n_pow_mul_eq`, `diamondOp_ext_comm_heckeT_ppow`).

### 2.3 `heckeRingHom` family — 4 variants

| Variant | File | Target |
|---------|------|--------|
| `heckeRingHomCharSpaceOne` | `HeckeT_p_CharSpace_Comm.lean:201` | `M_k(Γ₁(N))` (no nebentypus) |
| `heckeRingHom` | `HeckeModularForm.lean:540` | `ModularForm 𝒮ℒ k` (level one) |
| `heckeRingHom_Gamma0` | `HeckeModularForm_Gamma0.lean:291` | `ModularForm (Γ₀ N) k` |
| `heckeRingHomCharSpace` | `Unified/NebentypusHeckeRingHom.lean:369` | `M_k(Γ₁(N), χ)` (the live one) |

Plus the "twisted" intermediate `twistedHeckeRingHomFunction` (`Unified/TwistedHeckeRing.lean:1251`) and `nebentypusHeckeOp/_Linear/_Sum` family (`Unified/NebentypusHeckeRingHom.lean:218/252/275`). Three of the four `heckeRingHom*` variants are scaffolding behind `heckeRingHomCharSpace`; `HeckeT_p_CharSpace_Comm.lean` is an explicit "comm step" file that ships an entire ring-hom construction parallel to the live one.

### 2.4 `Γ₀(N)` / `Γ₁(N)` / `Γ_p(α)` pair sprawl

- `Gamma0_pair N` lives in `HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`
- `Gamma1_pair N` lives in `HeckeRIngs/GL2/Gamma1Pair.lean` — **wrong directory** (Foundation has `Gamma0_pair` so it's a Hecke-pair file; `Gamma1_pair` should be in `CongruenceHecke/`)
- `Gamma_p_α` lives in `HeckeRIngs/GL2/AdjointTheory/FDTransport.lean`

### 2.5 `ModularForm` / `CuspForm` parallel families in SMO/Newforms

| ModularForm side | CuspForm side | LOC of parallel |
|------------------|---------------|-----------------|
| `modFormCharSpace` | `cuspFormCharSpace` | ≈40 ↔ |
| `IsOldformGenerator` / `cuspFormsOld` (Newforms/Basic) | `IsLevelInclusionOldformGenerator` / `cuspFormsOldExtended` (Newforms/LevelRaiseComm) | ≈100 |
| `restrictSubgroup_mem_modFormCharSpace` (Eigenforms/MainLemma) | `cuspForm_restrictSubgroup_mem_cuspFormCharSpace` (Miyake465) | ≈30 |
| `modularFormLevelRaise_mem_modFormCharSpace` | `cuspForm_levelRaise_mem_cuspFormCharSpace` | ≈50 |

The CuspForm side wraps the ModularForm side everywhere via `toModularForm'` + transport; the wrappers are mechanical but uniformly inlined.

### 2.6 `T_p_upper` / `T_p_lower` / `M_infty` matrix-content sprawl

`T_p_upper` (`HeckeT_p.lean:48`), `T_p_lower` (`HeckeT_p.lean:54`), `T_p_lower_with_offset` (`Newforms/BadPrimeCosets.lean:44`), `M_infty_Gamma1_factor` (`SummandAdjoint.lean:441`), `gamma0_T_p_upper_Gamma1_factor` (`DeltaBSystem.lean:36`), `sigma_p_specific` (`HeckeT_p_Gamma1.lean:67`). Each ships its own `_coe / _det / _det_pos / _mem_X` battery.

---

## 3. Hypothesis sprawl

### 3.1 Signatures with 15+ hypothesis bundles (top 20)

| Signature | File:line | Sig-lines |
|-----------|-----------|----------:|
| `heckeT_p_ut` | `HeckeT_p.lean:103` | 23 |
| `castCuspFormLinearEquiv_apply` | `Eigenforms/AtkinLehner.lean:216` | 28 |
| `adj_T_p_upper_factorisation` | `Unified/NebentypusHeckeRingHom.lean:567` | 31 |
| `descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff` | `Lemma4_6_14.lean:952` | 28 |
| `descent_l_prime_gt_one_apply` | `Lemma4_6_14.lean:857` | 27 |
| `adj_T_p_lower_factorisation` | `Unified/NebentypusHeckeRingHom.lean:575` | 30 |
| `heckeT_p_all_mul_heckeT_ppow_succ` | `HeckeT_n.lean:1332` | 21 |
| `miyake_descent_l_prime_gt_one_helper` | `Lemma4_6_14.lean:644` | 27 |
| `Miyake467Decomp_inductive_step_left_branch` | `SquarefreeDecomp.lean:577` | 31 |
| `Miyake467Decomp_inductive_assemble` | `SquarefreeDecomp.lean:368` | 27 |
| `lunip_inject` | `CongruenceHecke/Props.lean:246` | 26 |
| `traceSlash_Gamma_p_α` (FDTransport) | `FDTransport.lean:1134/1406` | 31/30 |
| `heckeT_n_cusp_comm_diamondOp` | `AdjointTheoryPetersson.lean:49` | 30 |
| `slash_sum_V_q_cuspForm_descend` | `SquarefreeDecomp.lean:1038` | 28 |
| `castLevelRaise` | `Eigenforms/AtkinLehner.lean:223` | 21 |
| `gamma0NebentypusChar_apply` | `Unified/NebentypusSpace.lean:42` | 31 |
| `descendCosetList_apply_lt` | `DescentCosets.lean:645` | 23 |
| `LevelRaiseEigenDecomp` | `StrongMultiplicityOneFull.lean:250` | 22 |

### 3.2 Recurring stanzas

- **`(p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)`** — appears in **97** lemma signatures across `HeckeT_n.lean` and 49 in `HeckeRingHomCharSpace.lean`. A `variable` block scoped to a sub-namespace would eliminate the repetition (already done in some places but not consistently).
- **`[NeZero N] [NeZero (N / p)] [NeZero (l * N)] [NeZero (l * N / p)]`** — these `NeZero` instance preambles appear per-lemma in `SMOObligations/SquarefreeDecomp.lean` (53 occurrences), `Lemma4_6_14.lean`, `MiyakeDescend.lean`. A `m7_NeZero_*` helper exists (`SquarefreeDecomp.lean`) but is used inconsistently.
- **`χ.comp (ZMod.unitsMap …)` chain** — re-expressed inline by `m7_chiFHelper_chain`, `m7_gHelper_char_restrict`, `m7_χ_q_collapse` (`SquarefreeDecomp.lean:32, 49, …`) and again in `Lemma4_6_14.lean` (~6 sites). Same character-projection chain spelled out three different ways.
- **`(M₁ M₂ M N₁ N₂ : ℕ) [NeZero M₁] [NeZero M₂] [NeZero M] [NeZero N₁] [NeZero N₂]`** — the level-bookkeeping zoo in `SquarefreeDecomp.lean:577` (`_left_branch`), `:649` (`_right_branch`), `:368` (`_assemble`). Each has ~6 levels under `NeZero` plus their `dvd` and divisor witnesses.

### 3.3 Trailing existential conclusions

`Miyake467Decomp` signatures *return* an 8-tuple unpacking `⟨g_helper, F_helper, χ_F_helper, g_helper_char, F_helper_char, F_helper_eq, χ_F_helper_rel, g_helper_qexp⟩`. Same 8 fields fed in then re-extracted on every recursive call. A structure already exists (`Miyake467Decomp`) — collapsing the tuple-pattern callers to use the structure projections is mechanical.

---

## 4. Mathlib v4.30 redo candidates

### 4.1 `AbstractHeckeRing/` — ≈3,085 LOC of mathlib-track infrastructure

| File | LOC | Decls |
|------|----:|------:|
| `Basic.lean` | 332 | `HeckePair`, `HeckeCoset`, `𝕋`, `decompQuot` |
| `Multiplication.lean` | 692 | `mulMap`, `heckeMultiplicity`, `m`, `T_single` |
| `Associativity.lean` | 739 | `smul_assoc_singles` (96-line proof), associativity |
| `Module.lean` | 270 | left-quotient module structure |
| `Commutativity.lean` | 435 | `AntiInvolution`, Shimura Prop 3.8 |
| `Degree.lean` | 290 | `deg : 𝕋 P ℤ →+* ℤ` |
| `Ring.lean` | 189 | ring instance assembly |
| `StabConjugation.lean` | 138 | `decompQuot_double_H_equiv` |

The whole subtree already imports `Mathlib.GroupTheory.DoubleCoset` and operates at the `(G : Group) (P : HeckePair G)` level of generality. Project-specific uses are only `Gamma0_pair`, `Gamma1_pair`, `GL_pair`. **Upstream PR:** `Mathlib.GroupTheory.HeckeRing.{Basic, Multiplication, Module, Associativity, Commutativity, Ring, Degree}`.

### 4.2 Project decls that mirror mathlib v4.30 API

| Project decl | Mathlib v4.30 equivalent | Action |
|--------------|-------------------------|--------|
| `qExpansion_ext2` (`qExpansion_lems.lean:58`) | mathlib defines `qExpansion` on any `α` with `FunLike α ℍ ℂ`; ext follows from `qExpansion_coeff` + `funext` | Inline at call sites |
| `instance : FunLike (ℍ → ℂ) ℍ ℂ` (`qExpansion_lems.lean:52`) | Functions already have `FunLike` in mathlib via `Function.instFunLike` (or `(· : α → β)` is its own coercion) | Probably redundant; verify and delete |
| Custom `cuspFormToModularFormLin` (`Newforms/Basic.lean:209`) | `Mathlib.NumberTheory.ModularForms.CuspFormSubmodule` ships `CuspForm.toModularFormₗ` (DetOne form) | Re-express on top of mathlib's |
| `IsCuspForm` (`Newforms/Basic.lean`) | `Mathlib.NumberTheory.ModularForms.CuspFormSubmodule.IsCuspForm` | Already congruent — could be `def IsCuspForm := Mathlib.…IsCuspForm` |
| `cuspFormSubmodule` chain in project | `Mathlib.…CuspFormSubmodule.cuspFormSubmodule` | Project should use mathlib's |
| `Newforms/CoeffSeq.lean:lCoeff*` | `Modularforms/LFunction.lean` already defines `ModularForms.lCoeff` and `ModularForms.lSeries` (with summability lemmas), and `Newform.lCoeff_eq_modularForms_lCoeff` confirms equality — so the Newform-specific `lCoeff` is a thin shim. | If Fricke chain is excised the shim goes with it |
| `Eigenforms/AtkinLehner.lean:IsSupportedOnDvd` (PowerSeries support predicate) | Could be expressed as `PowerSeries.coeff` indicator on a `Set ℕ`; no direct mathlib decl | Local to project, keep |
| `set_eq_iUnion_leftCosets`, `DoubleCoset.doubleCoset_eq_iUnion_leftCosets` (used through `AbstractHeckeRing`) | Mathlib `Mathlib.GroupTheory.DoubleCoset` does not have either yet | PR up; small standalone lemma |
| `SL_reduction_surjective` (`GLn/SL2Surjection.lean:174`, 200 LOC) | Strong-approximation for `SL₂(ℤ) → SL₂(ℤ/dℤ)` | Mathlib gap; PR `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup.StrongApproximation` |
| `slTransvecG` (`SLnTransvection.lean:22`) and battery | Mathlib has `Matrix.transvection` and `Matrix.TransvectionStruct` in `Mathlib.LinearAlgebra.Matrix.Transvection`. The project's wrapper at `SpecialLinearGroup` level is justified, but `slTransvecG_mul`, `_inv`, `_zero`, etc. duplicate `Matrix.transvection_*` results | Bridge to mathlib |
| `exists_diagonal_of_posdet`, `exists_divchain_diagonal_of_posdet` (`DiagonalCosets.lean:349/865`, ~500 LOC) | Smith Normal Form for integer matrices with positive determinant. Mathlib has `Submodule.exists_smith_normal_form_of_le` for PID modules but not in this elementary-matrix presentation | PR up the matrix↔module bridge; saves ~500 LOC |
| `SLnZ_to_GLnQ_det`, `SLnZ_to_GLnQ_val` (`MultiplicationTable.lean:37/44`, with docstring "replaces removed lemmas") | Documented as restoring deleted mathlib helpers | Reinstate in `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup.Basic` |
| `coprime_indicator_eq_sum_moebius` (`Eigenforms/MainLemma/CoprimeSieve.lean` — note: file appears in older audit but `MainLemma/` subfolder is absent in current Eigenforms/) | Direct consequence of `ArithmeticFunction.moebius_mul_coe_zeta` | Possibly already deleted; verify |

**Mathlib changes that absorbed project code (already realised in v4.30).**
- `Mathlib.NumberTheory.ModularForms.QExpansion` ships the full `cuspFunction`/`qExpansion`/`hasSum_qExpansion`/`qExpansionFormalMultilinearSeries` API. The project's `qExpansion_lems.lean` is now down to 63 LOC and lives essentially to host `qExpansion_ext2` (single-line proof) — could be dissolved.
- `Mathlib.NumberTheory.ModularForms.Petersson` ships `petersson`, `petersson_slash`, `petersson_norm_symm`, `petersson_isZeroAtImInfty_left/right`. The project's `Modularforms/PeterssonInner.lean` (110 LOC) and `PeterssonLevelN.lean` (980 LOC) have benefited but `PeterssonLevelN.lean` still ships level-`N`-specific transport that could be PR'd up.
- `Mathlib.NumberTheory.ModularForms.Bounds` ships `CuspFormClass.exists_bound`, `petersson_bounded_left/right`.
- `Mathlib.NumberTheory.ModularForms.CuspFormSubmodule` ships `IsCuspForm`, `cuspFormSubmodule`, `toCuspForm`, `isCuspForm_iff_coeffZero_eq_zero` — the project still defines its own `IsCuspForm` in `Modularforms/IsCuspForm.lean` (135 LOC); merge.
- `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` ships `Gamma`, `Gamma0`, `Gamma1`, `Gamma1'`, `Gamma0Map`, `IsCongruenceSubgroup`, **`conjGL`**, `exists_Gamma_le_conj`. Project's `Gamma1Pair.lean`/`Gamma0_pair`/`Gamma_p_α` build cleanly on these.
- `Mathlib.NumberTheory.ModularForms.DimensionFormulas/LevelOne` exists; the project's `Modularforms/DimensionFormulas.lean` (201 LOC) supplies a higher-level dim formula for `Gamma1 N` — orthogonal, keep.

### 4.3 Mathlib does NOT yet contain (worth knowing)

- No `AtkinLehner*` file in `Mathlib.NumberTheory.ModularForms`
- No `Eigenform` / `Newform` structure
- No Hecke operator API at `M_k(Γ₁(N))` level (mathlib has `slashAction` but no `T_n`)
- No `Module.End` joint-eigenspace decomposition lemma specifically for a commuting family of self-adjoint operators on a finite-dim inner product space (the project's `heckeFamily_directSum_isInternal` is the assembly of `directSum_isInternal_of_orthogonal*` + commutativity, ~10 LOC — fine to keep, could potentially upstream)

---

## 5. Architectural unification opportunities

### 5.1 `HeckeT_n` ↔ `MultiplicationTable` slash-action bridge — ≈700 LOC redo

The same identities appear at two levels:

| Formal (MultiplicationTable.lean) | Analytic (HeckeT_n.lean) |
|-----------------------------------|--------------------------|
| `T_sum_ppow_mul` (819) | `heckeT_ppow_mul` (covered by `heckeT_ppow_comm_heckeT_ppow:1085` + the divisor-sum derivation 1393–1671) |
| `T_sum_mul` (1092) | `heckeT_n_mul` (1882) |
| `T_sum_mul_coprime` (887) | `heckeT_n_mul_coprime` (1269) |
| `T_ad_mul_of_coprime` (846) | `heckeT_p_all_comm_distinct` (926) |
| `gcd_factor_prime_pow` (949) | `gcd_eq_gcd_ordCompl_mul_pow_min` (HeckeT_n.lean:1845) |

Both proofs use the **same** `Finset.sum_bij'` between `range(c+1) ×ˢ g'.divisors.attach` and `(g'·p^c).divisors.attach` (the forward map sends `(j, d')` to `p^j · d'`). Both use the **same** strong induction on the minimum prime factor.

The slash-action ring homomorphism `heckeRingHomCharSpace : 𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ (modFormCharSpace k χ)` (`Unified/NebentypusHeckeRingHom.lean:369`) **already exists**. The analytic identities should follow from the formal ones via `RingHom.map_mul`, `heckeRingHomCharSpace_heckeRingD_n`, etc. The 700 LOC of divisor-sum manipulation in `HeckeT_n.lean:1393–1882` was developed before the ring-hom landed.

### 5.2 Unified vs. concrete Hecke rings — pick one as primary

`Unified/Core.lean` introduces `GoodHeckeFamily` as a structure carrying multiplicative commuting operators indexed by `GoodIndex N := coprimeToN N`. `Unified/Gamma1CharSpace.lean` and `Unified/CuspNebentypusSpace.lean` instantiate it. But the proof in `AdjointTheoryPetersson.lean:exists_simultaneous_eigenform_basis` works at the *concrete* level (`heckeFamily k χ` is built from `heckeT_n_cusp_charRestrict`), bypassing `GoodHeckeFamily`. The Unified API is real but **not currently load-bearing for any protected headline**. Either:
  - **(a)** Migrate `exists_simultaneous_eigenform_basis` to use `GoodHeckeFamily`, demoting the concrete `heckeFamily` to a single `GoodHeckeFamily` constructor (≈100 LOC compression);
  - **(b)** Delete the `Unified/{Core, CuspNebentypusSpace, Gamma1CharSpace, NebentypusSpace}` non-load-bearing structures (≈460 LOC); only keep `TwistedHeckeRing.lean` + `NebentypusHeckeRingHom.lean` which `heckeRingHomCharSpace` lives in.

### 5.3 Atkin–Lehner `mainLemma_charSpace_*` collapses to one statement

`Eigenforms/AtkinLehner.lean` contains 13 public theorems all of the form "a same-level / iSup / divisor decomposition + character closure ⇒ oldform-membership":

- `mainLemma_charSpace_of_sameLevelDivisorDecomposition` — **the only one** invoked downstream
- 12 wrappers using different shapes of the decomposition hypothesis

Only the live one needs to be public; the others are intermediate steps that could be `private`.

### 5.4 `cuspFormsOld` / `cuspFormsOldExtended` / `cuspFormsOldChar` triple

Three subspaces in three files:
- `cuspFormsOld` (`Newforms/Basic.lean:151`): span of `levelRaise`-images from proper divisors with `d > 1`
- `cuspFormsOldExtended` (`Newforms/LevelRaiseComm.lean:358`): adds the **trivial** `d = 1` level-inclusion generators
- `cuspFormsOldChar` (`StrongMultiplicityOneFull.lean:146`): character-conductor-refined oldspace

Each ships its own newform-orthogonal companion (`cuspFormsNew`, `cuspFormsNewExtended`). The relationship is fixed and one-directional — could be packaged via `Submodule` extensions and inclusions documented in one place.

### 5.5 `AbstractHeckeRing.Multiplication.lean` right/left mirror pairs (4×40 LOC)

In `Multiplication.lean`:
- `mulMap_T_one_eq` (227) / `mulMap_one_T_eq` (344)
- `nonempty_mul_one_witness_of_dcRel` (285) / `nonempty_one_mul_witness_of_dcRel` (501)
- `heckeMultiplicity_mul_one` (313) / `heckeMultiplicity_one_mul` (550)
- `heckeMultiplicity_mul_one_eq_zero` (662) / `heckeMultiplicity_one_mul_eq_zero` (712)
- `m_mul_one_eq_single` / `m_one_mul_eq_single`

Each pair is a mirror image (sides swapped). Parametrising by side (or proving one and obtaining the other by `AntiInvolution`) collapses ~160 LOC.

### 5.6 Newforms internal Fricke chain — extract or quarantine

`Newforms/Fricke.lean`, `Newforms/FrickeTwist.lean`, `Newforms/BadPrimeAdjoint.lean`, `Newforms/BadPrimeCosets.lean`, `Newforms/BadPrimeReduction.lean` total **1,346 LOC**. The only outward-facing decl needed by SMO is `cuspFormsOldExtended_disjoint_cuspFormsNewExtended` (BadPrimeAdjoint.lean:97, **4-line proof** that just uses `petN_definite` and `Submodule.disjoint_def`). The five Fricke-related files thus collectively defend **one 4-line theorem**.

Move the 4-line disjointness theorem into `Newforms/LevelRaiseComm.lean` (where the two submodules live), then either:
- **(a)** Delete the five Fricke files entirely (clean removal, no protected headline affected); or
- **(b)** Move them into `LeanModularForms/HeckeRIngs/GL2/Newforms/_Fricke/` and exclude from the default build target — same effect as deletion but preserves the work.

### 5.7 `CoeffSeq.lean` (998 LOC) is 85% internal scaffolding

External uses from `CoeffSeq.lean`: `Newform.dirichletLift` (537) and `Newform.eigenvalue_coprime_mul` (62) — that's two definitions / theorems out of 40. The L-series machinery (`lCoeff`, `lCoeff_stripped`, `eulerFactor_stripped`, `lSeries_stripped_hasProd`, `tsum_lCoeff_pow_mul_eq_eulerFactor`, `specialPoint`, `exists_nonzero_prime_eigenvalue`, all the `_dirichletQuotient_*` theorems) is internal to the Fricke chain.

If §5.6 lands, ≈750 LOC of `CoeffSeq.lean` can move to `_Fricke/`, leaving a slim `~200 LOC` core: `eigenvalue_coprime_mul`, `lCoeff_eq_modularForms_lCoeff` (the bridge to `Modularforms/LFunction.lean`), and `dirichletLift`.

---

## 6. Long-proof catalog (>40 lines)

**Total proofs ≥ 40 lines: 137.** Top entries:

| Lines | File:line | Name | Decompose? |
|------:|-----------|------|------------|
| 174 | `Lemma4_6_14.lean:300` | `miyake_4_6_14_delta_slash_sum_coeff_zero` | Yes — multi-section internal `set …` cascade |
| 99 | `Lemma4_6_14.lean:952` | `descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff` | Yes — 35-hyp signature already invites a per-step bundle |
| 96 | `AbstractHeckeRing/Associativity.lean:638` | `smul_assoc_singles` | Has rationale (assoc proof); marginal |
| 88 | `Newforms/FrickeTwist.lean:374` | (anon Newform-related, see §5.6) | Quarantine with file |
| 80 | `AdjointTheory/DeltaBSystem.lean:845` | `T_p_lower_tile_family_inv_mul_notMem_Gamma_up` | Yes — matrix-content proof, splits into entry-by-entry |
| 78 | `CongruenceHecke/Surjectivity.lean:564` | `monomial_prod_eval_at_Ds_eq_indicator` | Yes — `Finset.sum` over generators |
| 75 | `AdjointTheory/DeltaBSystem.lean:1164` | `ds_p_plus_one_family_Gamma1_factor_inv_mul_notMem_Gamma0` | Same shape as 845; could share a generic helper |
| 65 | `SquarefreeDecomp.lean:692` | `Miyake467Decomp_inductive_step` | Yes — structure-tuple unpack |
| 63 | `SquarefreeDecomp.lean:368` | `Miyake467Decomp_inductive_assemble` | Yes — same |
| 61 | `GLn/PolynomialRing.lean:763` | `T_ad_one_p_pow_eval_leading` | Modest |
| 60 | `AdjointTheory/DeltaBSystem.lean:776` | `card_quotient_K_subgroupOf_G` | Yes — finite-index combinatorics |
| 59 | `HeckeActionGeneral.lean:510` | `heckeSlash_gen_fiber_sum` | Yes |
| 59 | `AdjointTheory/FDTransport.lean:1691` | `exists_Gamma1_mul_inv_mem_Gamma0` | Yes — partner of `_mem_Gamma_up:1891` (54L) |
| 58 | `Lemma4_6_8.lean:317` | `miyake_4_6_8_subset_helper` | Already split with `_unconditional` |
| 57 | `MultiplicationTable.lean:752` | `T_sum_ppow_mul_step` | Yes (combinatorial) |
| 56 | `CongruenceHecke/Presentation.lean:91` | `T_elem_mem_` | Yes |
| 56 | `AdjointTheory/FDTransport.lean:1161` | `sum_SL_tile_petersson_Gamma_p_α` | Yes — index-set juggling |
| 55 | `CongruenceHecke/Surjectivity.lean:1056` | `mulSupport_Gamma0_pp_GL_split` | Yes |
| 55 | `AdjointTheory/DeltaBSystem.lean:466` | `toConjAct_GLPos_smul_SL2Z_to_PSL2R` | Yes |
| 55 | `AdjointTheory/ConcreteFamily.lean:84` | `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` | Yes — Hecke-FD aggregate |
| 54 | `StrongMultiplicityOneFull.lean:894` | `newPart_eq_smul_of_shared_eigenvalues` | **Protected headline path** — proof bookkeeping; can decompose but careful |
| 54 | `SquarefreeDecomp.lean:308` | `Miyake467Decomp_of_prime` | Yes |
| 54 | `CoprimeMul.lean:771` | `heckeMultiplicity_coprime_le_one` | Yes |
| 54 | `AdjointTheory/FDTransport.lean:1891` | `exists_Gamma1_mul_inv_mem_Gamma_up` | Yes (with :1691 partner) |
| 53 | `CoprimeMul.lean:631` | `diagSandwich_scaling` | Yes |
| 52 | `StrongMultiplicityOneFull.lean:526` | `oldNewGenCharSpan_inf_charSpace_le_cuspFormsOldChar` | Yes |
| 51 | `CongruenceHecke/Foundation.lean:208` | `exists_Gamma_factor_of_mem_Gamma_gcd` | Yes |
| 51 | `HeckeT_p.lean:512` | `orbit_lower_gamma0` | Yes — paired with `orbit_upper_gamma0:401` (48L) |
| 51 | `HeckeT_n.lean:1671` | `heckeT_n_mul_aux_divisor_sum` | Yes — removable if §5.1 lands |
| 51 | `AdjointTheory/ConcreteFamily.lean:530` | `slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard` | Yes |
| 50 | `StrongMultiplicityOneFull.lean:1094` | `oldPart_diff_qExpansion_coeff_eq_zero` | **Protected headline path** |
| 50 | `AdjointTheory/FDTransport.lean:1406` | `traceSlash_Gamma_p_α` | Yes |
| 49 | `AdjointTheoryPetersson.lean:668` | `exists_simultaneous_eigenform_basis` | **Protected headline — leave as is** |

Roughly **45 of the 137 long proofs sit in files marked for §5 reduction** (HeckeT_n divisor-sum block, Lemma4_6_14 χ-cascade, AdjointTheory/DeltaBSystem matrix content, Surjectivity finite-index combinatorics, SquarefreeDecomp structure-unpacks). Some will disappear with the structural moves; others are good `/decompose-proof` candidates independently.

---

## 7. Reduction plan — 12 tickets

Tickets ordered by ROI / risk. Each is sized for one session; LOC saved is net (removed minus minor inflation from helpers). Protected headlines `[propext, Classical.choice, Quot.sound]` are preserved by every ticket.

| # | Ticket | LOC | Risk | Depends on |
|---|--------|----:|------|------------|
| 1 | **Quarantine `Newforms/{Fricke, FrickeTwist, BadPrimeAdjoint, BadPrimeCosets, BadPrimeReduction}` + bottom 750L of `CoeffSeq.lean`.** Move the 4-line `cuspFormsOldExtended_disjoint_cuspFormsNewExtended` to `Newforms/LevelRaiseComm.lean`; relocate the Fricke + bad-prime + L-series internals to `LeanModularForms/HeckeRIngs/GL2/Newforms/_Fricke/` (excluded from default target). Reduce CoeffSeq.lean to the ≈200 LOC core: `eigenvalue_coprime_mul`, `dirichletLift`, `lCoeff_eq_modularForms_lCoeff`. | **−2,100** | Low | — |
| 2 | **Bridge `T_sum_*` formal identities to `heckeT_n_*` analytic via `heckeRingHomCharSpace`.** Express `heckeT_ppow_mul`, `heckeT_n_mul`, `heckeT_n_mul_coprime` as images of `T_sum_ppow_mul`, `T_sum_mul`, `T_sum_mul_coprime` under the ring hom. Removes the duplicated `Finset.sum_bij'` divisor sums and the `gcd_eq_gcd_ordCompl_mul_pow_min`/`heckeT_n_mul_aux_divisor_sum` block (HeckeT_n.lean:1393–1882). | **−700** | High (need to verify the ring hom inserts the `p^{k-1}·⟨p⟩` correctly through `nebentypusHeckeOp` packaging) | — |
| 3 | **Collapse `diamondOp_ext` / `diamondOp_n` into one definition.** They have identical bodies. Single `diamondOp_n` keeps the better name; rename usages in `HeckeT_n.lean`, `Unified/NebentypusHeckeRingHom.lean`. Eliminates `diamondOp_ext_coprime / _not_coprime` doublets and the `_ext_comm_*` mirror suite. | **−180** | Low | — |
| 4 | **Upstream `AbstractHeckeRing/` to mathlib.** PR `Mathlib.GroupTheory.HeckeRing.{Basic, Multiplication, Module, Associativity, Commutativity, Ring, Degree, StabConjugation}`. Project re-imports the 7 mathlib files; everything else continues. While we wait for the PR to land, this can be a `_Mathlib/` shadow-folder. Also collapses §5.5 right/left mirrors in the same PR. | **−3,085** (off active path) **−160** (mirror collapses) | Medium (PR review timeline) | — |
| 5 | **Unify `Gamma_p_α_*` API in FDTransport.** Pick `_PSL_R_FD_finite_index_decomp_shifted` as the canonical form (it's the one used by the headline path); demote `_auto`, `_canonical`, `_eq_smul` to private corollaries. Same for `Gamma_p_α_fundDomain_PSL_canonical` ↔ `Gamma_p_α_fundDomain_PSL`. | **−200** | Low | — |
| 6 | **Make `mainLemma_charSpace_*` wrappers private.** In `Eigenforms/AtkinLehner.lean`, only `mainLemma_charSpace_of_sameLevelDivisorDecomposition` is downstream-public. The 12 sibling wrappers (`_of_TraceDescent`, `_of_singleDivisorSupport`, `_via_divisor_iSup`, `_of_modularFormSameLevelDivisorDecomposition`, etc.) become `private`. No LOC delta but namespace de-spam. | 0 | Low | — |
| 7 | **Move `Gamma1_pair` from `GL2/Gamma1Pair.lean` to `GLn/CongruenceHecke/Gamma1_pair.lean`.** Restore symmetry with `Gamma0_pair` (which is in `Foundation.lean`). The split was historical (Gamma1 was added in a later phase). The actual Gamma1 *slash action* lemmas can stay in `GL2/` since they need ℝ. Atomic move + import fix-up. | 0 (organization) | Low | — |
| 8 | **Decide on `Unified/{Core, Gamma1CharSpace, CuspNebentypusSpace, NebentypusSpace}`: load-bearing or delete?** Option (a): migrate `heckeFamily` in `AdjointTheoryPetersson.lean` to use `GoodHeckeFamily`. Option (b): delete the 4 files and inline what's needed in `NebentypusHeckeRingHom.lean`. Current state: `GoodHeckeFamily` is defined but the headline doesn't transit it. | **−460** (option b) | Low (b) / Medium (a) | — |
| 9 | **Decompose the 6 longest non-headline proofs.** `miyake_4_6_14_delta_slash_sum_coeff_zero` (174L), `descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff` (99L), `Miyake467Decomp_inductive_step` (65L), `monomial_prod_eval_at_Ds_eq_indicator` (78L), `T_p_lower_tile_family_inv_mul_notMem_Gamma_up` (80L), `ds_p_plus_one_family_Gamma1_factor_inv_mul_notMem_Gamma0` (75L). Per `/decompose-proof`. Net LOC may inflate slightly but readability + recompile latency improves. | +50 to +150 | Low | — |
| 10 | **Bridge project `IsCuspForm` to `Mathlib.…CuspFormSubmodule.IsCuspForm`.** Project's `Modularforms/IsCuspForm.lean` (135 LOC) predates mathlib's; rename `IsCuspForm := Mathlib.…IsCuspForm` and inline the differences (if any). Same for `cuspFormToModularFormLin` ↔ `CuspForm.toModularFormₗ`. | **−100** | Low | — |
| 11 | **Dissolve `qExpansion_lems.lean`.** 63 LOC, two lemmas: `qExpansion_ext2` (one-line proof from mathlib's `qExpansion_coeff`) and `modform_tendto_ndhs_zero` (could live in `Modularforms/AtImInfty.lean`). Plus a redundant `FunLike (ℍ → ℂ) ℍ ℂ` instance. | **−50** | Low | — |
| 12 | **Pull mathlib gaps upstream as separate PRs.** `set_eq_iUnion_leftCosets`, `DoubleCoset.doubleCoset_eq_iUnion_leftCosets`, `SL_reduction_surjective` (strong approximation `SL₂(ℤ) → SL₂(ℤ/dℤ)`), `SLnZ_to_GLnQ_det` / `_val` reinstatement, `slTransvecG`-↔-`Matrix.transvection` bridge, `Submodule.smithNormalFormOfRankEq`-↔-matrix bridge. After all land: ≈800 LOC vanishes from project. | **−800** (after PRs land) | Medium (mathlib timing) | — |

### Aggregate impact

| Bucket | LOC |
|--------|----:|
| Net LOC removed from active build path (T1, T2, T3, T5, T8(b), T10, T11) | **≈3,690** |
| LOC moved to mathlib upstream (T4 + T12) | **≈3,885** |
| LOC added by decomposition (T9) | +50–150 |
| **Total off-active-path delta** | **≈7,425** |

At 46,376 LOC starting, this is a **~16% structural reduction** of the active build path while every protected headline keeps the same axiom signature.

---

## 8. Risks & non-goals

- **Do not touch** `AdjointTheoryPetersson.lean:exists_simultaneous_eigenform_basis` (49 LOC) — protected headline, the proof is delicate `InnerProductSpace.Core` plumbing.
- **Do not touch** `ConcreteFamily.lean:heckeT_p_adjoint` and the 5-step direct route below it (`petN_heckeT_p_LHS_eq_aggregate`, `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD`, `aggregate_D_petersson_eq_Gamma_p_α_fundDomain`, `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`, `traceSlash_T_p_lower_eq_diamond_inv_heckeT_p`).
- **Do not touch** `StrongMultiplicityOneFull.lean:strongMultiplicityOne_constMul / _axiom_clean` (lines 1231 / 1267). The 50-line non-headline proofs `oldPart_diff_qExpansion_coeff_eq_zero` (1094) and `newPart_eq_smul_of_shared_eigenvalues` (894) sit on the path — `/decompose-proof` is fine but verify axioms after.
- **Do not touch** `mainLemma_charSpace_of_sameLevelDivisorDecomposition` (`Eigenforms/AtkinLehner.lean:280`) — it's the single mainLemma wrapper that downstream uses.
- T2 (HeckeT_n ↔ MultiplicationTable bridge) has the highest risk because the ring hom packaging may not give the `p^{k-1}·⟨p⟩` factor in the form `heckeT_n_mul` states. Worth a 1-day spike before committing to ≈700 LOC of rewrite.

---

## 9. Cross-reference to prior overviews

- `.mathlib-quality/gln-overview-2026-05-31.md` — pre-cleanup snapshot of the GLn/AbstractHeckeRing subtree (≈16k LOC at the time). The `BlockBijection/` + `Projection.lean` quarantine described there has **landed** (those subtrees no longer exist). The §3 "Two `heckeMultiplicity` definitions" issue persists.
- `.mathlib-quality/adjoint-overview-2026-05-31.md` — pre-cleanup snapshot of AdjointTheory (≈18.3k LOC). The TileBridge.lean (4,116 LOC) deletion has **landed**; ConcreteFamily.lean shrank from 4,483 to 697 LOC. The §5.5 `MInfty*` / `TpUpper*` doublet was eliminated by removing TileBridge.lean.
- `.mathlib-quality/eigenforms-smo-overview-2026-05-31.md` — pre-cleanup snapshot of Eigenforms+SMO. Many of the §3 "Redundant Structures" (`TraceDescent`, `SameLevelDivisorProjections`, `TraceCorrectionPrime`, `PartialTraceCorrection`, etc.) were in `Eigenforms/AtkinLehnerProjection.lean` which **no longer exists**. The current `Eigenforms/AtkinLehner.lean` still has the `IsSupportedOnDvd` + `qSupportedOnDvdSubmodule` + `castLevelRaise` API, much slimmer.

---

**Report file:** `/Users/mcu22seu/Documents/GitHub/LeanModularForms-hecke/.mathlib-quality/overview-post-v4.30.md`
