# Inventory: ./HasseWeil/WeilPairing/OneSubAffineResidues.lean

**File**: `HasseWeil/WeilPairing/OneSubAffineResidues.lean`  
**Lines**: 1342  
**Total declarations**: 30 (1 noncomputable local instance + 1 noncomputable def + 2 simp theorems + 26 theorems)  
**No sorry** anywhere in the file.  
**One `set_option maxHeartbeats`**: line 675, value 8000000, for `oneSub_addSlopePair_resid_doubling`.

---

## LIVE / DEAD classification (verified against the proof DAG of `hasse_bound_unconditional`)

Per the verified dependency analysis the file is **32/34 live** (the "34" = 32 named decls + the
local instance + section context). **Exactly 2 declarations are DEAD / SUPERSEDED:**

| Declaration | Status | Reason |
|---|---|---|
| `comap_pointValuation_oneSub_eq_affine_nondoubling` (L1248) | **DEAD** | Conditional (non-doubling, non-2-torsion) variant. Referenced ONLY at its own def line + one docstring mention (L50); **superseded by the UNCONDITIONAL `comap_pointValuation_oneSub_eq_affine`** (L1295). No real consumer anywhere in the repo. |
| `oneSub_alpha_star_u_ord_eq_zero` (L1038) | **DEAD** | The non-`_of_residues` unit variant. Its ONLY consumer is the dead `comap_pointValuation_oneSub_eq_affine_nondoubling` (L1269); **superseded by `oneSub_alpha_star_u_ord_eq_zero_of_residues`** (which serves both doubling and non-doubling). |

All other declarations are **LIVE**: either they feed the live capstone
`comap_pointValuation_oneSub_eq_affine` (the `affine` field of `OneSubProjOrdTransport`'s
`comapPointValuationWitness_oneSub`, on the live leaf-2 path
`oneSubFrobeniusScaling_holds → … → ComapPointValuationWitness`), **or** they are re-used externally
by `PencilComapWitnesses.lean` (the live leaf-3 path): the entire `residPV_*` calculus,
`residPV_x_gen`, `residPV_unit`, `frobeniusHomBaseChange_apply_some`, `W_KE_map_functionFieldMap`,
`addSlopePair_id_negFrobBaseChange`, `oneSub_addSlopePair_resid_doubling`,
`oneSub_two_residues_nondoubling`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, and
`negFrobBaseChange`. (`comap_pointValuation_oneSub_eq_affine` is itself "unused in this file" but is a
live cross-file capstone — see its entry.)

## Cross-cutting cleanup findings

- **Separability detection is hand-rolled, NOT mathlib `Algebra.IsSeparable`.** The `e = 1` /
  separability input fed to `comap_pointValuation_isog_eq_affine(_y)` is the invariant-differential
  coefficient condition `omegaPullbackCoeff (1 − π)_{K̄} ≠ 0`
  (`omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero` / `_mem_range`).
- **Order-transport uses the project's own valuation layer**, not `IsDedekindDomain.HeightOneSpectrum`
  directly: `SmoothPlaneCurve.pointValuation` / `ord_P` / `ordAtInftyValuation` + mathlib `Valuation.comap`.
  (`IsDedekindDomain` appears only as an instance requirement upstream.)
- **PRIME DE-DUPLICATION TARGET — the `residPV_*` residue calculus.** `residPV_mul/pow/const/sub/add/
  neg/le_one/unit` + `residPV_x_gen` are **curve-generic** (no `1 − π` content) but live in this
  `1 − π`-specific file, advertised as a "public re-derivation of the `SamePlace` residue toolkit".
  `PencilComapWitnesses.lean` references this file's symbols **47×** and ALSO re-proves its own
  `resid_x_gen_of_comap`/`resid_y_gen_of_comap`. Extract `residPV_*` into a shared
  `WeilPairing/Residues.lean` consumed by both the OneSub and Pencil leaves.
- **Mirrored additive-pullback machinery.** `negFrobBaseChange` + `addSlopePair_id_negFrobBaseChange`
  + `addPullback_{x,y}_pair_id_negFrobBaseChange` + `oneSub_pullback_{x,y}_gen_eq_addPullback_*` is the
  `1 − π` instance of a generic "additive pullback decomposition + base-change naturality" pattern
  that the pencil leaf re-implements with its own `(rπ − s)` summands — candidate for a single
  summand-parametric `addPullback_pair_baseChange` naturality lemma.

---

## Module-level context

The file proves the closed-point generator residues of the concrete base-changed `1 − π` isogeny over `K̄` and assembles the full unconditional affine comap-valuation identity. It works over a finite field `K` with a fixed prime `p` and `r` such that `#K = p^r`, and over `AlgebraicClosure K`. The decisive trick is building a **bespoke** `−π` summand `negFrobBaseChange` with a transparent pullback (via `baseChangePullback (negFrobeniusIsog W).pullback`), sidestepping the opaque `frobeniusIsog_baseChange_charP_pow`.

---

## Local instance

### `noncomputable local instance instDecEqACOSAR`
- **Type**: `DecidableEq (AlgebraicClosure K)`
- **What**: Provides classical decidable equality on the algebraic closure of `K`.
- **How**: `Classical.decEq _`
- **Hypotheses**: None beyond `K : Type*` being a field.
- **Uses from project**: none
- **Used by**: implicitly throughout the file (avoids instance inference gaps)
- **Visibility**: private (local instance)
- **Lines**: 83 (1 line)
- **Notes**: Standard classical workaround for `AlgebraicClosure`.

---

## Declarations

### `noncomputable def negFrobBaseChange`
- **Type**: `HasseWeil.Isogeny (W.baseChange (AlgebraicClosure K)).toAffine (W.baseChange (AlgebraicClosure K)).toAffine`
- **What**: The bespoke `−π` summand isogeny `α₂` over `K̄`, with pullback `baseChangePullback (negFrobeniusIsog W).pullback` and point map `−frobeniusHomBaseChange`.
- **How**: `Isogeny.mkBaseChange` with the negated Frobenius point map.
- **Hypotheses**: `W : WeierstrassCurve K`, `[W.toAffine.IsElliptic]`, `p r` prime/char data.
- **Uses from project**: `baseChangePullback`, `HasseWeil.negFrobeniusIsog`, `frobeniusHomBaseChange`
- **Used by**: `negFrobBaseChange_pullback`, `negFrobBaseChange_toAddMonoidHom`, `negFrobBaseChange_pullback_functionFieldMap`, `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, `negFrobBaseChange_apply_some`, and all downstream theorems
- **Visibility**: public
- **Lines**: 95–101 (7 lines def)
- **Notes**: Key architectural choice — explicit pullback avoids whnf-timeout from opaque `frobeniusIsog_baseChange_charP_pow` base change.

---

### `@[simp] theorem negFrobBaseChange_pullback`
- **Type**: `(negFrobBaseChange W p r).pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) (AlgebraicClosure K) (HasseWeil.negFrobeniusIsog W).pullback`
- **What**: The pullback of `negFrobBaseChange` is definitionally the base-change pullback.
- **How**: `Isogeny.mkBaseChange_pullback`.
- **Hypotheses**: Same as `negFrobBaseChange`.
- **Uses from project**: `Isogeny.mkBaseChange_pullback`
- **Used by**: `negFrobBaseChange_pullback_functionFieldMap`
- **Visibility**: public (`@[simp]`)
- **Lines**: 103–107 (5 lines)
- **Notes**: `simp` lemma; needed for `rw` in `negFrobBaseChange_pullback_functionFieldMap`.

---

### `@[simp] theorem negFrobBaseChange_toAddMonoidHom`
- **Type**: `(negFrobBaseChange W p r).toAddMonoidHom = -frobeniusHomBaseChange W p r (AlgebraicClosure K)`
- **What**: The point map of `negFrobBaseChange` is the negated Frobenius point map.
- **How**: `Isogeny.mkBaseChange_toAddMonoidHom`.
- **Hypotheses**: Same as `negFrobBaseChange`.
- **Uses from project**: `Isogeny.mkBaseChange_toAddMonoidHom`, `frobeniusHomBaseChange`
- **Used by**: `negFrobBaseChange_apply_some`, `oneSub_two_residues_nondoubling`, `oneSub_frob_eq_neg_at_doubling`, `oneSub_two_residues_doubling`
- **Visibility**: public (`@[simp]`)
- **Lines**: 109–112 (4 lines)
- **Notes**: `simp` lemma.

---

### `theorem negFrobBaseChange_pullback_functionFieldMap`
- **Type**: For `z : W.toAffine.FunctionField`, `(negFrobBaseChange W p r).pullback (functionFieldMap z) = functionFieldMap ((negFrobeniusIsog W).pullback z)`
- **What**: The WallA naturality: `α₂^*` commutes with the function-field inclusion `functionFieldMap`.
- **How**: `rw [negFrobBaseChange_pullback]` then `baseChangePullback_functionFieldMap`.
- **Hypotheses**: Same context.
- **Uses from project**: `negFrobBaseChange_pullback`, `IsogenyBaseChangeConcrete.baseChangePullback_functionFieldMap`
- **Used by**: `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, `addSlopePair_id_negFrobBaseChange`, `addPullback_x_pair_id_negFrobBaseChange`, `addPullback_y_pair_id_negFrobBaseChange`
- **Visibility**: public
- **Lines**: 117–125 (9 lines)
- **Notes**: Core "WallA" naturality fact; used 7 times in the file.

---

### `theorem negFrobBaseChange_pullback_x_gen`
- **Type**: `(negFrobBaseChange W p r).pullback (x_gen (W.baseChange (AlgebraicClosure K))) = x_gen (W.baseChange (AlgebraicClosure K)) ^ Fintype.card K`
- **What**: `α₂^* x_gen = x_gen^q` over `K̄` (the `x`-generator residues to its `q`-th power).
- **How**: Chains `negFrobBaseChange_pullback_functionFieldMap` + `functionFieldMap_x_gen` + `negFrobeniusIsog_pullback_x_gen` + `frobeniusIsog_pullback_apply` + `map_pow`.
- **Hypotheses**: Same context.
- **Uses from project**: `negFrobBaseChange_pullback_functionFieldMap`, `IsogenyBaseChangeConcrete.functionFieldMap_x_gen`, `HasseWeil.negFrobeniusIsog_pullback_x_gen`, `HasseWeil.frobeniusIsog_pullback_apply`
- **Used by**: `oneSub_two_residues_nondoubling` (via `residPV_pow`), `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 127–141 (15 lines)
- **Notes**: Proof length ~15 lines.

---

### `theorem negFrobBaseChange_pullback_y_gen`
- **Type**: `(negFrobBaseChange W p r).pullback (y_gen (W.baseChange (AlgebraicClosure K))) = -(y_gen^q) - algebraMap K̄ a₁ * x_gen^q - algebraMap K̄ a₃`
- **What**: `α₂^* y_gen = −y_gen^q − a₁·x_gen^q − a₃` over `K̄`.
- **How**: Uses `negFrobBaseChange_pullback_functionFieldMap`, `negFrobeniusIsog_pullback_y_gen`, `frobeniusIsog_pullback_apply`, and `IsScalarTower.algebraMap_apply` for the base-field coefficient bridges.
- **Hypotheses**: Same context.
- **Uses from project**: `negFrobBaseChange_pullback_functionFieldMap`, `IsogenyBaseChangeConcrete.functionFieldMap_x_gen/y_gen`, `IsogenyBaseChangeConcrete.functionFieldMap_algebraMap_F`, `HasseWeil.negFrobeniusIsog_pullback_y_gen`, `HasseWeil.frobeniusIsog_pullback_apply`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 148–191 (44 lines proof, ~52 total)
- **Notes**: Long proof (~44 lines) due to coefficient bridge setup for `a₁`, `a₃`; used by 3+ downstream theorems.

---

### `theorem W_KE_map_functionFieldMap`
- **Type**: `(W_KE W).map (functionFieldMap (AlgebraicClosure K)) = W_KE (W.baseChange (AlgebraicClosure K))`
- **What**: The curve `W_KE W` base-changes along `functionFieldMap` to `W_KE (W.baseChange K̄)`.
- **How**: `WeierstrassCurve.ext` + `functionFieldMap_algebraMap_F` + `IsScalarTower.algebraMap_apply`; uses that ring homs `functionFieldMap ∘ algebraMap K K(E)` and `algebraMap K K̄(E)` agree.
- **Hypotheses**: Same context.
- **Uses from project**: `SmoothPlaneCurve.functionFieldMap_algebraMap_F`, `W_KE`
- **Used by**: `addSlopePair_id_negFrobBaseChange`, `addPullback_x_pair_id_negFrobBaseChange`, `addPullback_y_pair_id_negFrobBaseChange`
- **Visibility**: public
- **Lines**: 200–213 (14 lines)
- **Notes**: Used 7 times in the file as the "curve-map" building block.

---

### `theorem addSlopePair_id_negFrobBaseChange`
- **Type**: `addSlopePair (Isogeny.id (W.baseChange K̄).toAffine) (negFrobBaseChange W p r) = functionFieldMap (addSlopePair (Isogeny.id W.toAffine) (negFrobeniusIsog W))`
- **What**: The slope of the base-changed `(id, α₂)`-pair equals the function-field base change of the `K`-level slope.
- **How**: `map_slope` (naturality of slope under ring hom) applied after rewriting to `W_KE_map_functionFieldMap` form and using `negFrobBaseChange_pullback_functionFieldMap`.
- **Hypotheses**: Same context.
- **Uses from project**: `addSlopePair`, `negFrobBaseChange_pullback_functionFieldMap`, `W_KE_map_functionFieldMap`, `WeierstrassCurve.Affine.map_slope`
- **Used by**: `addPullback_x_pair_id_negFrobBaseChange`, `addPullback_y_pair_id_negFrobBaseChange`
- **Visibility**: public
- **Lines**: 219–244 (26 lines)
- **Notes**: Key intermediate; used by 4 callers.

---

### `theorem addPullback_x_pair_id_negFrobBaseChange`
- **Type**: `addPullback_x_pair (Isogeny.id (W.baseChange K̄).toAffine) (negFrobBaseChange W p r) = functionFieldMap (addPullback_x_pair (Isogeny.id W.toAffine) (negFrobeniusIsog W))`
- **What**: The `x`-addition formula of the base-changed pair equals the function-field base change of the `K`-level `x`-addition formula.
- **How**: `map_addX` (naturality of `x`-addition under ring hom) + `addSlopePair_id_negFrobBaseChange` + `W_KE_map_functionFieldMap`.
- **Hypotheses**: Same context.
- **Uses from project**: `addPullback_x_pair`, `addSlopePair_id_negFrobBaseChange`, `negFrobBaseChange_pullback_functionFieldMap`, `W_KE_map_functionFieldMap`, `WeierstrassCurve.Affine.map_addX`
- **Used by**: `oneSub_pullback_x_gen_eq_addPullback_x_pair`, `oneSub_two_residues_nondoubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 250–266 (17 lines)
- **Notes**: Used 4 times.

---

### `theorem addPullback_y_pair_id_negFrobBaseChange`
- **Type**: `addPullback_y_pair (id) (negFrobBaseChange W p r) = functionFieldMap (addPullback_y_pair (id) (negFrobeniusIsog W))`
- **What**: The `y`-analogue of `addPullback_x_pair_id_negFrobBaseChange`, using `map_addY`.
- **How**: `map_addY` + `addSlopePair_id_negFrobBaseChange` + `W_KE_map_functionFieldMap` + generator naturalities.
- **Hypotheses**: Same context.
- **Uses from project**: `addPullback_y_pair`, `addSlopePair_id_negFrobBaseChange`, `negFrobBaseChange_pullback_functionFieldMap`, `W_KE_map_functionFieldMap`, `WeierstrassCurve.Affine.map_addY`
- **Used by**: `oneSub_pullback_y_gen_eq_addPullback_y_pair`, `oneSub_two_residues_nondoubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 270–292 (23 lines)
- **Notes**: Used 4 times.

---

### `theorem oneSub_pullback_x_gen_eq_addPullback_x_pair`
- **Type**: `(oneSubFrobeniusIsogBaseChange …).pullback (x_gen (W.baseChange K̄)) = addPullback_x_pair (id) (negFrobBaseChange W p r)`
- **What**: The `x`-generator pullback of `(1−π)_{K̄}` equals the `x`-addition-formula expression with summands `id` and `α₂`.
- **How**: `oneSubFrobeniusIsogBaseChange_pullback`, `oneSubFrobeniusPullback_L_x_gen`, `oneSub_pullback_x_gen_eq`, `addPullback_x_pair_id`, `addPullback_x_pair_id_negFrobBaseChange`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_pullback`, `IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_x_gen`, `oneSub_pullback_x_gen_eq`, `addPullback_x_pair_id`, `addPullback_x_pair_id_negFrobBaseChange`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 304–313 (10 lines)
- **Notes**: None.

---

### `theorem oneSub_pullback_y_gen_eq_addPullback_y_pair`
- **Type**: `(oneSubFrobeniusIsogBaseChange …).pullback (y_gen (W.baseChange K̄)) = addPullback_y_pair (id) (negFrobBaseChange W p r)`
- **What**: The `y`-analogue of `oneSub_pullback_x_gen_eq_addPullback_x_pair`.
- **How**: Same chain as the `x` version with `y`-analogues.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`.
- **Uses from project**: `oneSubFrobeniusIsogBaseChange_pullback`, `IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_y_gen`, `oneSub_pullback_y_gen_eq`, `addPullback_y_pair_id`, `addPullback_y_pair_id_negFrobBaseChange`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 318–327 (10 lines)
- **Notes**: None.

---

### `theorem residPV_x_gen`
- **Type**: `pointValuation P (x_gen (W.baseChange K̄) - algebraMap K̄ … P.x) < 1`
- **What**: The generic `x`-coordinate residues to `P.x` modulo the maximal ideal at `P`.
- **How**: `x_gen_sub_const_eq_algebraMap_XClass` + `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt` + `XClass_mem_maximalIdealAt`.
- **Hypotheses**: `P` a smooth point of `E_{K̄}`.
- **Uses from project**: `HasseWeil.x_gen_sub_const_eq_algebraMap_XClass`, `Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`, `HasseWeil.XClass_mem_maximalIdealAt`
- **Used by**: `residPV_pow` (via calls), `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling`, and more (8 direct call sites)
- **Visibility**: public
- **Lines**: 333–339 (7 lines)
- **Notes**: Fundamental building block; used 8+ times in the file.

---

### `theorem residPV_le_one`
- **Type**: If `pV P (u − algebraMap a) < 1` then `pV P u ≤ 1`.
- **What**: A residue `u ≡ a` implies `u` is regular at `P` (valuation ≤ 1).
- **How**: Rewrites `u = (u − algebraMap a) + algebraMap a`, uses `pointValuation_add_le_one` and `pointValuation_algebraMap_F_le_one`.
- **Hypotheses**: residue hypothesis.
- **Uses from project**: `pointValuation_add_le_one`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `residPV_mul`
- **Visibility**: public
- **Lines**: 342–352 (11 lines)
- **Notes**: Helper for `residPV_mul`.

---

### `theorem residPV_mul`
- **Type**: If `u ≡ a` and `v ≡ b` then `u·v ≡ a·b` (modulo `m_P`).
- **What**: Residues multiply: the product formula for residues at a point.
- **How**: Splits `u·v − a·b = u·(v−b) + b·(u−a)`, applies `pointValuation_mul_lt_one_of_le_and_lt` twice, then `map_add` + `max_lt`.
- **Hypotheses**: Two residue hypotheses.
- **Uses from project**: `residPV_le_one`, `pointValuation_mul_lt_one_of_le_and_lt`, `SmoothPlaneCurve.pointValuation_algebraMap_F_le_one`
- **Used by**: `residPV_pow`, and extensively in `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling`, `oneSub_alpha_star_u_ord_eq_zero`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, `oneSub_alpha_star_polyX_ord_eq_zero_of_residues` (15 call sites)
- **Visibility**: public
- **Lines**: 355–374 (20 lines)
- **Notes**: Core arithmetic for the residue toolkit; used 15 times.

---

### `theorem residPV_pow`
- **Type**: If `u ≡ a` then `u^n ≡ a^n`.
- **What**: Residues raise to natural-number powers (by induction on `n`).
- **How**: Induction; base `pow_zero` + `map_zero`; step `residPV_mul`.
- **Hypotheses**: Residue hypothesis, `n : ℕ`.
- **Uses from project**: `residPV_mul`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling` (12 call sites)
- **Visibility**: public
- **Lines**: 377–387 (11 lines)
- **Notes**: Used 12 times.

---

### `theorem residPV_const`
- **Type**: `pV P (algebraMap c − algebraMap c) < 1`
- **What**: A scalar `algebraMap c` residues to itself (trivially `= 0`).
- **How**: `sub_self` + `map_zero` + `zero_lt_one`.
- **Hypotheses**: `c : AlgebraicClosure K`.
- **Uses from project**: none
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling`, `oneSub_alpha_star_u_ord_eq_zero`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, `oneSub_alpha_star_polyX_ord_eq_zero_of_residues` (27 call sites)
- **Visibility**: public
- **Lines**: 390–395 (6 lines)
- **Notes**: Most-used helper; 27 call sites.

---

### `theorem residPV_sub`
- **Type**: If `u ≡ a` and `v ≡ b` then `u − v ≡ a − b`.
- **What**: Residues subtract.
- **How**: Rewrites `u − v − (a−b) = (u−a) − (v−b)`, applies `map_sub` + `max_lt`.
- **Hypotheses**: Two residue hypotheses.
- **Uses from project**: none (uses `Valuation.map_sub` which is mathlib)
- **Used by**: `residPV_neg`, and widely (10 call sites)
- **Visibility**: public
- **Lines**: 398–415 (18 lines)
- **Notes**: Used 10 times.

---

### `theorem residPV_add`
- **Type**: If `u ≡ a` and `v ≡ b` then `u + v ≡ a + b`.
- **What**: Residues add.
- **How**: Rewrites `u + v − (a+b) = (u−a) + (v−b)`, applies `map_add` + `max_lt`.
- **Hypotheses**: Two residue hypotheses.
- **Uses from project**: none
- **Used by**: `oneSub_alpha_star_u_ord_eq_zero`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, `oneSub_alpha_star_polyX_ord_eq_zero_of_residues` (6 call sites)
- **Visibility**: public
- **Lines**: 418–435 (18 lines)
- **Notes**: Used 6 times.

---

### `theorem residPV_neg`
- **Type**: If `u ≡ a` then `−u ≡ −a`.
- **What**: Residues negate.
- **How**: Uses `residPV_sub` with `0` (via a `pV(0 − 0) < 1` auxiliary).
- **Hypotheses**: Residue hypothesis.
- **Uses from project**: `residPV_sub`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_addSlopePair_resid_doubling`, `oneSub_two_residues_doubling` (4 call sites)
- **Visibility**: public
- **Lines**: 438–454 (17 lines)
- **Notes**: Used 4 times.

---

### `theorem frobeniusHomBaseChange_apply_some`
- **Type**: For a nonsingular `(x, y)`, `frobeniusHomBaseChange W p r K̄ (some x y h) = some (frobeniusAlgHom x) (frobeniusAlgHom y) _`
- **What**: The geometric Frobenius point map sends `(x, y)` to `(x^q, y^q)` (as a `some` affine point).
- **How**: `frobeniusHomBaseChange_eq_geomFrobeniusPoint`, `geomFrobeniusPoint_apply`, `geomFrobeniusPointFun_some`.
- **Hypotheses**: Nonsingularity of `(x, y)` over `W.baseChange K̄`.
- **Uses from project**: `frobeniusHomBaseChange_eq_geomFrobeniusPoint`, `geomFrobeniusPoint_apply`, `geomFrobeniusPointFun_some`
- **Used by**: `negFrobBaseChange_apply_some`
- **Visibility**: public
- **Lines**: 462–472 (11 lines)
- **Notes**: None.

---

### `theorem negFrobBaseChange_apply_some`
- **Type**: `(negFrobBaseChange W p r).toAddMonoidHom (some x y h) = some (frobeniusAlgHom x) (negY (frobeniusAlgHom x) (frobeniusAlgHom y)) _`
- **What**: The `α₂ = negFrobBaseChange` point map sends `(x, y)` to `(x^q, negY(x^q, y^q))` — i.e., `−π̄(P)`.
- **How**: `negFrobBaseChange_toAddMonoidHom`, `AddMonoidHom.neg_apply`, `frobeniusHomBaseChange_apply_some`, `Affine.Point.neg_some`.
- **Hypotheses**: Nonsingularity of `(x, y)`.
- **Uses from project**: `negFrobBaseChange_toAddMonoidHom`, `frobeniusHomBaseChange_apply_some`
- **Used by**: `oneSub_two_residues_nondoubling`, `oneSub_frob_eq_neg_at_doubling`, `oneSub_two_residues_doubling` (4 call sites)
- **Visibility**: public
- **Lines**: 478–491 (14 lines)
- **Notes**: Used 4 times.

---

### `theorem oneSub_two_residues_nondoubling`
- **Type**: For `P` smooth with `(1−π)P = some x y` finite and `P.x ≠ P.x^q` (non-doubling), the two residues `(1−π)^*x_gen ≡ x` and `(1−π)^*y_gen ≡ y` hold.
- **What**: The two generator residues for `(1−π)_{K̄}` in the secant (non-doubling) case.
- **How**: Assembles per-summand residues for `id` (via `residPV_x_gen`, `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`) and `α₂` (via `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, residue toolkit), then feeds into `isog_coords_at_affine_of_decomp` with decomposition `oneSub_pullback_x_gen_eq_addPullback_x_pair` and point-map decomposition.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`, `P` smooth, `P.x ≠ P.x^q`, affine image `hQ`.
- **Uses from project**: `residPV_x_gen`, `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, `negFrobBaseChange_apply_some`, `oneSub_pullback_x_gen_eq_addPullback_x_pair`, `oneSub_pullback_y_gen_eq_addPullback_y_pair`, `residPV_pow`, `residPV_const`, `residPV_sub`, `residPV_neg`, `residPV_mul`, `isog_coords_at_affine_of_decomp`, `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`
- **Used by**: `oneSub_alpha_star_u_ord_eq_zero`, `comap_pointValuation_oneSub_eq_affine_nondoubling`, `comap_pointValuation_oneSub_eq_affine`
- **Visibility**: public
- **Lines**: 505–588 (84 lines proof)
- **Notes**: Long proof (84 lines); the substantive base-change-naturality content of the non-doubling secant case.

---

### `theorem residPV_unit`
- **Type**: If `u ≡ a` and `a ≠ 0` then `pV P u = 1`.
- **What**: A residue to a nonzero scalar makes the element a unit at `P`.
- **How**: `pointValuation_algebraMap_F_eq_one_of_ne_zero` for the constant part; then `map_add_eq_of_lt_right` to combine.
- **Hypotheses**: Residue hypothesis + `a ≠ 0`.
- **Uses from project**: `pointValuation_algebraMap_F_eq_one_of_ne_zero`
- **Used by**: `oneSub_addSlopePair_resid_doubling`, `oneSub_alpha_star_u_ord_eq_zero`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, `oneSub_alpha_star_polyX_ord_eq_zero_of_residues` (5 call sites)
- **Visibility**: public
- **Lines**: 591–605 (15 lines)
- **Notes**: Used 5 times.

---

### `theorem oneSub_frob_eq_neg_at_doubling`
- **Type**: In the doubling case `P.x = P.x^q` with `(1−π)P = some x y` affine, the Frobenius acts as `−1`: `frobeniusAlgHom P.y = negY P.x P.y` and `P.y ≠ frobeniusAlgHom P.y`.
- **What**: In the doubling case, `πP = −P` and `P` is non-2-torsion.
- **How**: Uses `Y_eq_of_X_eq` (two solutions of the Weierstrass equation over `x`) to get two cases; rules out `πP = P` by showing `(1−π)P = O` (contradiction with the affine image `hQ`); deduces `πP = −P` and `P` is non-2-torsion.
- **Hypotheses**: `hq`, `P`, `hx_eq : P.x = P.x^q`, affine image `hQ`.
- **Uses from project**: `negFrobBaseChange_apply_some`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `negFrobBaseChange_toAddMonoidHom`, `WeierstrassCurve.Affine.Y_eq_of_X_eq`, `WeierstrassCurve.Affine.Point.neg_some`, `WeierstrassCurve.Affine.negY_negY`
- **Used by**: `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 619–671 (53 lines)
- **Notes**: Proof ~53 lines; the case analysis that pins down doubling behavior.

---

### `theorem oneSub_addSlopePair_resid_doubling` *(set_option maxHeartbeats 8000000)*
- **Type**: In the doubling case (`P.x = P.x^q`, `π̄(P) = −P`, `P` non-2-torsion), `addSlopePair (id) (negFrobBaseChange) ≡ ν(P)/u(P)` at `P`.
- **What**: The invariant-differential L'Hôpital slope residue: in the doubling case the secant slope (which is a ratio with vanishing numerator and denominator at `P`) residues to the tangent slope `ν(P)/u(P)`.
- **How**: Sets `f := x_gen − x_gen^q` (uniformizer; `Dω f = u_gen` a unit by `Dω_pow` + char-`p` vanishing), `g := y_gen − α₂^*y_gen`, `φ := g − λ·f`. Shows `ord_P f = 1` (from `Dω_u` = unit), `ord_P φ ≥ 2` via `two_le_ord_P_of_Dω_vanishes_of_uniformizer`, then `addSlopePair − λ = φ/f` has `ord_P ≥ 1`.
- **Hypotheses**: `hq`, `P`, `hx_eq`, `hfrobneg`, `huP : 2P.y + a₁P.x + a₃ ≠ 0`.
- **Uses from project**: `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, `HasseWeil.ordAtInfty_x_gen`, `HasseWeil.ordAtInfty_x_gen_pow`, `Dω_pow`, `Dω_sub`, `Dω_x_gen`, `Dω_y_gen`, `Dω_neg`, `Dω_mul`, `Dω_algebraMap`, `HasseWeil.u_gen_ne_zero`, `HasseWeil.u_gen`, `one_le_ord_P_Dω_of_two_le`, `two_le_ord_P_of_Dω_vanishes_of_uniformizer`, `addSlopePair_eq_of_x_ne`, `residPV_x_gen`, `residPV_pow`, `residPV_const`, `residPV_sub`, `residPV_neg`, `residPV_mul`, `residPV_add`, `residPV_unit`
- **Used by**: `oneSub_two_residues_doubling`
- **Visibility**: public
- **Lines**: 687–911 (225 lines proof)
- **Notes**: **Longest proof** (225 lines); `set_option maxHeartbeats 8000000` at line 675, NO justifying comment in the source. Implements the invariant-differential L'Hôpital argument.

---

### `theorem oneSub_two_residues_doubling`
- **Type**: For `P` smooth with `(1−π)P = some x y` finite and `P.x = P.x^q` (doubling), the two generator residues hold.
- **What**: The two generator residues for `(1−π)_{K̄}` in the tangent (doubling) case.
- **How**: Calls `oneSub_frob_eq_neg_at_doubling` to deduce `π̄(P) = −P` and non-2-torsion; assembles per-summand residues; obtains the slope residue `oneSub_addSlopePair_resid_doubling`; feeds into `isog_coords_at_affine_of_decomp_slope`.
- **Hypotheses**: `hq`, `P`, `hx_eq : P.x = P.x^q`, affine image `hQ`.
- **Uses from project**: `oneSub_frob_eq_neg_at_doubling`, `negFrobBaseChange_apply_some`, `oneSub_pullback_x_gen_eq_addPullback_x_pair`, `oneSub_pullback_y_gen_eq_addPullback_y_pair`, `negFrobBaseChange_pullback_x_gen`, `negFrobBaseChange_pullback_y_gen`, `residPV_x_gen`, `residPV_pow`, `residPV_const`, `residPV_sub`, `residPV_neg`, `residPV_mul`, `oneSub_addSlopePair_resid_doubling`, `isog_coords_at_affine_of_decomp_slope`, `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`, `oneSubFrobeniusIsogBaseChange_toAddMonoidHom`, `negFrobBaseChange_toAddMonoidHom`
- **Used by**: `comap_pointValuation_oneSub_eq_affine`
- **Visibility**: public
- **Lines**: 925–1027 (103 lines proof)
- **Notes**: Long proof (103 lines).

---

### `theorem oneSub_alpha_star_u_ord_eq_zero`
- **Type**: For `P` non-doubling with non-2-torsion image `(1−π)P = some x y`, `ord_P (α^*u_gen) = 0`.
- **What**: The pulled-back invariant-differential denominator is a unit at `P` (uses the non-doubling hypothesis directly).
- **How**: Calls `oneSub_two_residues_nondoubling` for the two residues, then computes the residue of `alpha_star_u` via residue toolkit (`residPV_const`, `residPV_mul`, `residPV_add`), concludes unit via `residPV_unit`, then `ord_P_eq_zero_iff_pointValuation_eq_one`.
- **Hypotheses**: `hq`, `P`, `hx_ne`, `h2tor`, affine image `hQ`.
- **Uses from project**: `oneSub_two_residues_nondoubling`, `alpha_star_u_eq`, `residPV_const`, `residPV_mul`, `residPV_add`, `residPV_unit`, `Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `comap_pointValuation_oneSub_eq_affine_nondoubling`
- **Visibility**: public
- **Lines**: 1038–1085 (48 lines)
- **Notes**: Long proof (48 lines).

---

### `theorem oneSub_alpha_star_u_ord_eq_zero_of_residues`
- **Type**: Same conclusion as `oneSub_alpha_star_u_ord_eq_zero` but takes the two residues `hx`, `hy` directly (works for both doubling and non-doubling cases).
- **What**: Unit at `P` from abstract residue inputs; the version that feeds into both branches of the final unconditional theorem.
- **How**: Same argument as `oneSub_alpha_star_u_ord_eq_zero` but without calling the residue-generation theorem.
- **Hypotheses**: `hq`, `P`, `hx` (residue), `hy` (residue), `h2tor`.
- **Uses from project**: `alpha_star_u_eq`, `residPV_const`, `residPV_mul`, `residPV_add`, `residPV_unit`, `Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `comap_pointValuation_oneSub_eq_affine`
- **Visibility**: public
- **Lines**: 1090–1143 (54 lines)
- **Notes**: Long proof (54 lines); duplication of logic with `oneSub_alpha_star_u_ord_eq_zero` (same body except for the input origin).

---

### `theorem oneSub_alpha_star_polyX_ord_eq_zero_of_residues`
- **Type**: For a 2-torsion image (`2y + a₁x + a₃ = 0`) with residues `hx`, `hy`, `ord_P ((1−π)^*ν) = 0` where `ν` is the `y`-partial numerator `3x²+2a₂x+a₄−a₁y`.
- **What**: The pulled-back `y`-partial-numerator is a unit at `P` when the image is 2-torsion (needed for the `y`-uniformizer branch).
- **How**: Shows `ν(Q) = 3x²+2a₂x+a₄−a₁y ≠ 0` using `nonsingular_iff'` (both partials can't vanish for a nonsingular point); then residues the pulled-back polynomial to `ν(Q)` via the toolkit; concludes unit via `residPV_unit` + `ord_P_eq_zero_iff_pointValuation_eq_one`.
- **Hypotheses**: `hq`, `P`, `h_ns`, `hx`, `hy`, `h2tor : 2y + a₁x + a₃ = 0`.
- **Uses from project**: `residPV_const`, `residPV_mul`, `residPV_pow`, `residPV_add`, `residPV_sub`, `residPV_unit`, `WeierstrassCurve.Affine.nonsingular_iff'`, `Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `comap_pointValuation_oneSub_eq_affine`
- **Visibility**: public
- **Lines**: 1151–1227 (77 lines)
- **Notes**: Long proof (77 lines); the 2-torsion-image `y`-uniformizer unit.

---

### `theorem comap_pointValuation_oneSub_eq_affine_nondoubling`
- **Type**: For `P` non-doubling with non-2-torsion image `(1−π)P = some x y`, `(pV P).comap (1−π)^* = pV ⟨x,y,h_ns⟩`.
- **What**: The affine comap-valuation identity for `(1−π)_{K̄}` at a non-doubling, non-2-torsion image; `e = 1` derived, CoordHom-free, no carried `hcoeff_mem`.
- **How**: Obtains the two residues from `oneSub_two_residues_nondoubling`; calls `comap_pointValuation_isog_eq_affine` with the omega-coefficient value lemmas `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range` and `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero`, and `oneSub_alpha_star_u_ord_eq_zero` for the unit.
- **Hypotheses**: `hq`, `P`, `hx_ne`, `h2tor`, affine image `hQ`.
- **Uses from project**: `oneSub_two_residues_nondoubling`, `comap_pointValuation_isog_eq_affine`, `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range`, `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero`, `oneSub_alpha_star_u_ord_eq_zero`
- **Used by**: (unused in this file — called from other files)
- **Visibility**: public
- **Lines**: 1248–1269 (22 lines)
- **Notes**: The restricted (non-doubling, non-2-torsion) capstone. Not used inside this file.

---

### `theorem comap_pointValuation_oneSub_eq_affine`
- **Type**: For every `P` smooth with `(1−π)P = some x y` affine (no non-doubling/non-2-torsion hypotheses), `(pV P).comap (1−π)^* = pV ⟨x,y,h_ns⟩`.
- **What**: The **unconditional** affine comap-valuation identity for `(1−π)_{K̄}` — all four sub-cases (doubling/non-doubling) × (2-torsion/non-2-torsion image) handled.
- **How**: Cases on `P.x = P.x^q` (doubling/non-doubling) to get the two residues; then cases on `2y + a₁x + a₃ = 0` (2-torsion/non-2-torsion image) to invoke `comap_pointValuation_isog_eq_affine` (x-uniformizer) or `comap_pointValuation_isog_eq_affine_y` (y-uniformizer), with omega-coefficient lemmas and unit lemmas `oneSub_alpha_star_u_ord_eq_zero_of_residues` / `oneSub_alpha_star_polyX_ord_eq_zero_of_residues`.
- **Hypotheses**: `hq`, `P`, `h_ns`, affine image `hQ`.
- **Uses from project**: `oneSub_two_residues_nondoubling`, `oneSub_two_residues_doubling`, `comap_pointValuation_isog_eq_affine`, `comap_pointValuation_isog_eq_affine_y`, `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range`, `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero`, `oneSub_alpha_star_u_ord_eq_zero_of_residues`, `oneSub_alpha_star_polyX_ord_eq_zero_of_residues`
- **Used by**: (unused in this file — the universal capstone, consumed by other files)
- **Visibility**: public
- **Lines**: 1295–1341 (47 lines)
- **Notes**: Main theorem; long proof (47 lines); not used inside this file.

---

## Summary table

| # | Kind | Name | Lines |
|---|------|------|-------|
| 1 | local instance | `instDecEqACOSAR` | 83 |
| 2 | noncomputable def | `negFrobBaseChange` | 95–101 |
| 3 | @[simp] theorem | `negFrobBaseChange_pullback` | 103–107 |
| 4 | @[simp] theorem | `negFrobBaseChange_toAddMonoidHom` | 109–112 |
| 5 | theorem | `negFrobBaseChange_pullback_functionFieldMap` | 117–125 |
| 6 | theorem | `negFrobBaseChange_pullback_x_gen` | 127–141 |
| 7 | theorem | `negFrobBaseChange_pullback_y_gen` | 148–191 |
| 8 | theorem | `W_KE_map_functionFieldMap` | 200–213 |
| 9 | theorem | `addSlopePair_id_negFrobBaseChange` | 219–244 |
| 10 | theorem | `addPullback_x_pair_id_negFrobBaseChange` | 250–266 |
| 11 | theorem | `addPullback_y_pair_id_negFrobBaseChange` | 270–292 |
| 12 | theorem | `oneSub_pullback_x_gen_eq_addPullback_x_pair` | 304–313 |
| 13 | theorem | `oneSub_pullback_y_gen_eq_addPullback_y_pair` | 318–327 |
| 14 | theorem | `residPV_x_gen` | 333–339 |
| 15 | theorem | `residPV_le_one` | 342–352 |
| 16 | theorem | `residPV_mul` | 355–374 |
| 17 | theorem | `residPV_pow` | 377–387 |
| 18 | theorem | `residPV_const` | 390–395 |
| 19 | theorem | `residPV_sub` | 398–415 |
| 20 | theorem | `residPV_add` | 418–435 |
| 21 | theorem | `residPV_neg` | 438–454 |
| 22 | theorem | `frobeniusHomBaseChange_apply_some` | 462–472 |
| 23 | theorem | `negFrobBaseChange_apply_some` | 478–491 |
| 24 | theorem | `oneSub_two_residues_nondoubling` | 505–588 |
| 25 | theorem | `residPV_unit` | 591–605 |
| 26 | theorem | `oneSub_frob_eq_neg_at_doubling` | 619–671 |
| 27 | theorem | `oneSub_addSlopePair_resid_doubling` | 687–911 |
| 28 | theorem | `oneSub_two_residues_doubling` | 925–1027 |
| 29 | theorem | `oneSub_alpha_star_u_ord_eq_zero` | 1038–1085 |
| 30 | theorem | `oneSub_alpha_star_u_ord_eq_zero_of_residues` | 1090–1143 |
| 31 | theorem | `oneSub_alpha_star_polyX_ord_eq_zero_of_residues` | 1151–1227 |
| 32 | theorem | `comap_pointValuation_oneSub_eq_affine_nondoubling` | 1248–1269 |
| 33 | theorem | `comap_pointValuation_oneSub_eq_affine` | 1295–1341 |
