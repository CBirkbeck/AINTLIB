# Inventory: ./HasseWeil/Pic0/RouteCTheoremOfSquare.lean

**File**: `HasseWeil/Pic0/RouteCTheoremOfSquare.lean`
**Total lines**: 696
**Imports**: `HasseWeil.Pic0.RouteCGeometric`, `HasseWeil.Pic0.RouteCAdditivity`
**Namespace**: `HasseWeil.Pic0.RouteCTheoremOfSquare` (two separate `namespace`/`end` blocks, with a section about Phase 3 reopening)
**Total declarations**: 15 (all `theorem`)
**Sorries**: none
**set_option maxHeartbeats**: none

---

## Summary

This file is the "theorem-of-the-square" layer of Route C for Silverman III.6.2(c) dual additivity. It reduces the abstract `picDual(α₁ ⊞ α₂) = picDual α₁ + picDual α₂` (`hadd`) first to a class-group product identity (`hmul`), then unfolds `classMap` to the `mk0`/`Ideal.map` level (diamond-free), and ships the ideal-level pullback-as-divisor factorisation (Silverman III.6.2(b)). It is entirely sorry-free with no `set_option maxHeartbeats`.

---

## Declarations

### `theorem toClassEquiv'_picDual_add`
- **Type**: Given isogenies `α₁`, `α₂` with CoordHom witnesses, for any point `P`, transporting `(picDual α₁ + picDual α₂) P` through `κ = toClassEquiv'` gives `ofMul (classMap_{α₁}(κP) * classMap_{α₂}(κP))`.
- **What**: Computes `κ((picDual α₁ + picDual α₂) P)` as the product of the two individual class-group images. Engine lemma for Phase 1.
- **How**: Rewrites using `AddMonoidHom.add_apply`, `map_add`, then applies `HasseWeil.Isogeny.picDual_apply` twice and cancels `κ ∘ κ⁻¹` via `apply_symm_apply`. Final step is `rfl`.
- **Hypotheses**: Three CoordHom witnesses (one for each of `α₁`, `α₂`) with injectivity and module-finiteness.
- **Uses from project**: `HasseWeil.Isogeny.picDual_apply`, `WeierstrassCurve.Affine.Point.toClassEquiv'`
- **Used by**: `picDual_add_iff_classMap_mul` (called at lines 207, 215)
- **Visibility**: public
- **Lines**: 135–155; proof body 149–155 (7 lines)
- **Notes**: None

---

### `theorem toClassEquiv'_picDual`
- **Type**: For a single isogeny `α` with CoordHom witness, transporting `picDual α P` through `κ` gives `ofMul (classMap_α(κP))`.
- **What**: Single-map version of `toClassEquiv'_picDual_add`; transports one `picDual` application through `κ`. Used to handle the left side of the iff.
- **How**: Direct `rw` using `HasseWeil.Isogeny.picDual_apply` and `apply_symm_apply`; 2-step rewrite.
- **Hypotheses**: CoordHom witness `ch` for `α` with injectivity and module-finiteness.
- **Uses from project**: `HasseWeil.Isogeny.picDual_apply`, `WeierstrassCurve.Affine.Point.toClassEquiv'`
- **Used by**: `picDual_add_iff_classMap_mul` (lines 207, 215)
- **Visibility**: public
- **Lines**: 159–169; proof body 167–169 (3 lines)
- **Notes**: None

---

### `theorem picDual_add_iff_classMap_mul`
- **Type**: Biconditional: `picDual α = picDual α₁ + picDual α₂` (as AddMonoidHom) iff `∀ c : ClassGroup R, classMap_α c = classMap_{α₁} c * classMap_{α₂} c`. Three isogenies `α, α₁, α₂` each with their CoordHom witnesses.
- **What**: The Phase 1 structural transport equivalence. The point-map dual-additivity `hadd` is equivalent to the class-group product identity (the theorem-of-the-square at the Pic⁰ level). Pure κ-conjugation argument.
- **How**: Forward direction: evaluates `hadd` at `P = κ⁻¹(ofMul c)`, applies `toClassEquiv'_picDual` and `toClassEquiv'_picDual_add`, then uses `Additive.ofMul.injective`. Backward direction: proves pointwise via `toClassEquiv'_picDual`, `toClassEquiv'_picDual_add`, the hypothesis `hmul`, and injectivity of `toClassEquiv'`.
- **Hypotheses**: Three CoordHom witnesses (one per isogeny), each injective and module-finite.
- **Uses from project**: `toClassEquiv'_picDual`, `toClassEquiv'_picDual_add`
- **Used by**: `picDual_add_of_classMap_mul` (line 234)
- **Visibility**: public
- **Lines**: 189–216; proof body 201–216 (16 lines)
- **Notes**: Core equivalence lemma of Phase 1; called by exactly 1 declaration in file (`picDual_add_of_classMap_mul`).

---

### `theorem picDual_add_of_classMap_mul`
- **Type**: Implication: given `∀ c, classMap_α c = classMap_{α₁} c * classMap_{α₂} c`, conclude `picDual α = picDual α₁ + picDual α₂`.
- **What**: The forward consumer of Phase 1: from the class-group product identity, derives the point-map `hadd`. The clean hand-off point for the divisor/Abel argument.
- **How**: One-liner applying `(picDual_add_iff_classMap_mul …).mpr hmul`.
- **Hypotheses**: Three CoordHom witnesses; the class-group product identity `hmul` as hypothesis.
- **Uses from project**: `picDual_add_iff_classMap_mul`
- **Used by**: `picDual_add_of_classMap_mulHom` (line 252), `picDual_eq_rV_sub_s_of_classMap_mul` (line 462), `htrace_dual_of_classMap_mul` (line 491)
- **Visibility**: public
- **Lines**: 222–234; proof body 234 (1 line)
- **Notes**: Used by 3 other declarations — qualifies as key API.

---

### `theorem picDual_add_of_classMap_mulHom`
- **Type**: Same conclusion as `picDual_add_of_classMap_mul` but takes the class-group identity as a MonoidHom equation `classMap_α = classMap_{α₁} * classMap_{α₂}` (rather than pointwise).
- **What**: MonoidHom-equation variant of `picDual_add_of_classMap_mul`, the most natural statement for the theorem of the square.
- **How**: `refine picDual_add_of_classMap_mul … (fun c => ?_); rw [hmul]; rfl` — reduces to the pointwise version then uses `rfl` for the function application.
- **Hypotheses**: Three CoordHom witnesses; the MonoidHom equation `hmul`.
- **Uses from project**: `picDual_add_of_classMap_mul`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 241–253; proof body 251–253 (3 lines)
- **Notes**: Only called by 0 declarations within this file (dead-code candidate in file; may be used externally).

---

### `theorem map_comorphism_mem_nonZeroDivisors`
- **Type**: For an isogeny `α` with injective CoordHom `ch` and any `I ∈ (Ideal R)⁰`, the extended ideal `Ideal.map ch.toAlgHom.toRingHom I` also lies in `(Ideal R)⁰`.
- **What**: The nonzero-ideal-extension lemma: an injective comorphism maps nonzero ideals to nonzero ideals. Carried side condition for the `mk0` unfolding of `classMap`.
- **How**: Rewrites membership as `≠ 0`, applies `Ideal.map_eq_bot_iff_of_injective` using injectivity of `ch.toAlgHom.toRingHom`, then closes with `I.2`.
- **Hypotheses**: Injective comorphism `ch`; `I` a nonzero ideal.
- **Uses from project**: `Isogeny.CoordHom` (field access)
- **Used by**: `classMap_mk0_eq` (line 304), `classMap_toClass_some_eq_map` (lines 336, 340 implicitly via struct), `classMap_mul_of_ideal_class_mul` (lines 370, 372, 374)
- **Visibility**: public
- **Lines**: 278–288; proof body 283–288 (6 lines)
- **Notes**: Used by 3+ declarations — qualifies as key API.

---

### `theorem classMap_mk0_eq`
- **Type**: For `α` with CoordHom `ch` (injective, module-finite), `classMap_α (mk0 I) = mk0 ⟨Ideal.map ch.toAlgHom.toRingHom I, …⟩`.
- **What**: Computes `classMap` on an integral representative `mk0 I` as the class of the extended ideal. The diamond-free `mk0`/`Ideal.map` unfolding, fixing the instance via `letI := ch.toAlgebra`.
- **How**: Fixes algebra instance with `letI`/`haveI`, casts to `HasseWeil.ClassGroup.map`, applies `HasseWeil.ClassGroup.map_mk0`, then closes with `rfl`.
- **Hypotheses**: CoordHom witness injective and module-finite; `ch.isTorsionFree hinj` for torsion-freeness.
- **Uses from project**: `HasseWeil.ClassGroup.map_mk0`, `Isogeny.CoordHom.isTorsionFree`
- **Used by**: `classMap_toClass_some_eq_map` (doc only), `classMap_mul_of_ideal_class_mul` (lines 380–381)
- **Visibility**: public
- **Lines**: 297–310; proof body 304–310 (7 lines)
- **Notes**: Used by 2 declarations via direct call in proofs.

---

### `theorem classMap_toClass_some_eq_map`
- **Type**: For a finite point `Q = (x,y)` with nonsingularity `h` and `XYIdeal ∈ (Ideal R)⁰`, `classMap_α(κ Q).toMul = mk0 ⟨Ideal.map ch.toAlgHom XYIdeal, …⟩`.
- **What**: Identifies `classMap_α(κ Q)` with the class of the extended maximal ideal at `Q`. The concrete left-hand side of the theorem-of-the-square identity (Silverman III.6.2(b)).
- **How**: Fixes algebra instances, then rewrites using `toClassEquiv'_apply`, `toClass_some`, `mk0_eq_mk_XYIdeal'`, then casts and applies `ClassGroup.map_mk0` followed by `rfl`.
- **Hypotheses**: Injective, module-finite CoordHom; nonsingular point; ideal membership for the XYIdeal.
- **Uses from project**: `WeierstrassCurve.Affine.Point.toClassEquiv'_apply`, `WeierstrassCurve.Affine.Point.toClass_some`, `WeierstrassCurve.Affine.Point.mk0_eq_mk_XYIdeal'`, `HasseWeil.ClassGroup.map_mk0`, `map_comorphism_mem_nonZeroDivisors`
- **Used by**: unused in file (mentioned in doc comments only; no proof calls it)
- **Visibility**: public
- **Lines**: 324–346; proof body 337–346 (10 lines)
- **Notes**: Dead-code candidate within file; intended for future Abel argument.

---

### `theorem classMap_mul_of_ideal_class_mul`
- **Type**: Given the per-representative ideal-class product identity `hideal : ∀ I ∈ (Ideal R)⁰, [map α* I] = [map α₁* I] * [map α₂* I]`, concludes the abstract `hmul : ∀ c, classMap_α c = classMap_{α₁} c * classMap_{α₂} c`.
- **What**: Reduces the abstract MonoidHom identity to the concrete ideal-class product identity (diamond-free), by using `ClassGroup.mk0_surjective` to pick a representative and `classMap_mk0_eq` for each of the three terms.
- **How**: `obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c`, then `rw [classMap_mk0_eq …, classMap_mk0_eq …, classMap_mk0_eq …]` three times (each under its own instance), then `exact hideal I`.
- **Hypotheses**: Three CoordHom witnesses; the per-representative identity `hideal`.
- **Uses from project**: `classMap_mk0_eq`, `map_comorphism_mem_nonZeroDivisors`
- **Used by**: unused in file (mentioned only in doc comments)
- **Visibility**: public
- **Lines**: 360–382; proof body 377–382 (6 lines)
- **Notes**: Dead-code candidate within file; intended to bridge to future Abel proof.

---

### `theorem classMap_mul_of_point`
- **Type**: Given the per-point class identity `hpoint : ∀ Q : E.Point, classMap_α(κQ) = classMap_{α₁}(κQ) * classMap_{α₂}(κQ)`, concludes `hmul`.
- **What**: Reduces `hmul` to its restriction to point classes, using surjectivity of `κ = toClassEquiv'`. Every `c : ClassGroup R` equals `κ Q` for some point `Q`, so the per-point statement suffices.
- **How**: `obtain ⟨Q, hQ⟩ := toClassEquiv'.surjective (ofMul c)`, derives `(κ Q).toMul = c`, rewrites using it, then applies `hpoint Q`.
- **Hypotheses**: Three CoordHom witnesses; per-point identity `hpoint`.
- **Uses from project**: `WeierstrassCurve.Affine.Point.toClassEquiv'` (surjectivity)
- **Used by**: unused in file (mentioned only in doc comments)
- **Visibility**: public
- **Lines**: 396–420; proof body 412–420 (9 lines)
- **Notes**: Dead-code candidate within file; structural reduction intended for future use.

---

### `theorem picDual_eq_rV_sub_s_of_classMap_mul`
- **Type**: Given `hmul` (the theorem-of-the-square class-group identity), `hdual₁ : picDual α₁ = r • V`, `hdual₂ : picDual α₂ = -(s • id)`, conclude `picDual α = r • V - s • id`.
- **What**: Phase 2 assembly: derives the III.6.2(c) dual value `picDual α = r·V − s·id` from `hmul` and the two pre-shipped seeds, by composing Phase 1 with the `RouteCAdditivity` engine.
- **How**: Single application of `RouteCAdditivity.picDual_eq_rV_sub_s_of_additive`, passing `picDual_add_of_classMap_mul … hmul` as the additivity argument.
- **Hypotheses**: Three CoordHom witnesses; `hmul`; seed hypotheses `hdual₁`, `hdual₂`; integer parameters `r, s`.
- **Uses from project**: `RouteCAdditivity.picDual_eq_rV_sub_s_of_additive`, `picDual_add_of_classMap_mul`
- **Used by**: unused in file (no call site in proofs)
- **Visibility**: public
- **Lines**: 445–462; proof body 459–462 (4 lines)
- **Notes**: Dead-code candidate within file; the Phase 2 abstract form, instantiated by `htrace_dual_of_classMap_mul`.

---

### `theorem htrace_dual_of_classMap_mul`
- **Type**: Given `hmul`, `hdual₁`, `hdual₂`, `hbeta : α.toAddMonoidHom = r • π - s • id`, `hsum : π + V = [t]`, conclude `α.toAddMonoidHom + picDual α = (mulByInt E (r*t - 2*s)).toAddMonoidHom`.
- **What**: The III.8 trace form of Phase 2: derives `α + α̂ = [r·t − 2s]` from `hmul` and the seeds. This is the exact input `htrace_dual` that `RouteCGeometric` needs.
- **How**: Single application of `RouteCAdditivity.htrace_dual_of_picDual_additive`, passing `picDual_add_of_classMap_mul … hmul` as the additivity argument.
- **Hypotheses**: Three CoordHom witnesses; `hmul`; shape `hbeta`; trace relation `hsum`; seeds `hdual₁`, `hdual₂`.
- **Uses from project**: `RouteCAdditivity.htrace_dual_of_picDual_additive`, `picDual_add_of_classMap_mul`
- **Used by**: `htrace_dual_genuineIsogSmulSub_of_classMap_mul` (line 692)
- **Visibility**: public
- **Lines**: 471–491; proof body 488–491 (4 lines)
- **Notes**: None

---

### `theorem xyIdeal_isMaximal`
- **Type**: For a nonsingular point `(x,y)` on `E`, the ideal `XYIdeal E x (C y)` is maximal.
- **What**: Helper: the maximal ideal at a smooth affine point is indeed maximal (its quotient is the residue field `F`). Used as a side condition for the Dedekind factorisation theorem.
- **How**: Applies `Ideal.Quotient.maximal_of_isField`, using that `quotientXYIdealEquiv h.1` gives a field isomorphism.
- **Hypotheses**: Nonsingularity `h`; `[DecidableEq F]` and `[E.IsElliptic]` omitted (marked `omit`).
- **Uses from project**: `WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv`
- **Used by**: `map_xyIdeal_eq_prod_primesOver` (lines 542, 553)
- **Visibility**: public
- **Lines**: 508–515 (with `omit … in` prefix at 508); proof body 512–515 (4 lines)
- **Notes**: `omit [DecidableEq F] [E.IsElliptic] in` annotation to drop unneeded instances.

---

### `theorem map_xyIdeal_eq_prod_primesOver`
- **Type**: For a finite point `(x,y)` with injective module-finite CoordHom `ch` and `XYIdeal ∈ (Ideal R)⁰`, `Ideal.map ch.toAlgHom (XYIdeal E x (C y)) = ∏ P ∈ primesOver …, P ^ (ramificationIdx …)`.
- **What**: Step 1 of the theorem-of-the-square (Silverman III.6.2(b), ideal level): the extended maximal ideal factors over the fibre primes with ramification index exponents. The ideal incarnation of `φ*((Q)) = ∑_{αP=Q} e_φ(P)(P)`.
- **How**: Fixes algebra instances with `letI`/`haveI`, derives integrality from `Algebra.IsIntegral.of_finite`, uses `xyIdeal_isMaximal` for the maximality condition, and closes with `Ideal.map_algebraMap_eq_finset_prod_pow`.
- **Hypotheses**: Injective module-finite CoordHom; nonsingular point; nonzero ideal membership.
- **Uses from project**: `xyIdeal_isMaximal`, `Isogeny.CoordHom.isTorsionFree`
- **Used by**: unused in file (mentioned only in doc comments and the module residual discussion)
- **Visibility**: public
- **Lines**: 531–557; proof body 548–557 (10 lines)
- **Notes**: Dead-code candidate within file; axiom-clean step-1 infrastructure for the eventual Abel argument.

---

### `theorem htrace_dual_genuineIsogSmulSub_of_classMap_mul`
- **Type**: For the concrete Route-C setup `α = genuineIsogSmulSub W r s …`, `α₁ = (frobeniusIsog W).zsmul r`, `α₂ = mulByInt W.toAffine (-s)`, with their respective CoordHom witnesses and hypotheses `h_sum_trace`, `hdual₁`, `hdual₂`, `hmul`, concludes the III.8 trace relation `α.toAddMonoidHom + picDual α = (mulByInt W.toAffine (r*t - 2*s)).toAddMonoidHom`.
- **What**: Phase 3: instantiates Phase 2 at the concrete Frobenius-pencil decomposition. Produces the exact `htrace_dual` input consumed by `RouteCGeometric.picDual_smulSub_eq_rV_sub_s` — the Route-C drop-in replacement.
- **How**: Proves `hbeta` (the `r·π − s` shape) via `rw [genuineIsogSmulSub_toAddMonoidHom]` followed by `ext P` + `simp` + `neg_smul`/`sub_eq_add_neg`; then applies `htrace_dual_of_classMap_mul` with all collected hypotheses.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K`; `r, s : ℤ` with `r ≠ 0`, `s ≠ 0`, `r ≠ 0` in `K`, `s ≠ 0` in `K`; isogeny `V`; three CoordHom witnesses; `h_sum_trace`; `hdual₁`, `hdual₂`; `hmul`.
- **Uses from project**: `genuineIsogSmulSub`, `genuineIsogSmulSub_toAddMonoidHom`, `frobeniusIsog`, `mulByInt`, `isogTrace`, `isogOneSub_negFrobenius`, `htrace_dual_of_classMap_mul`
- **Used by**: unused in file (leaf declaration; consumed by `RouteCGeometric` externally)
- **Visibility**: public
- **Lines**: 653–695; proof body 683–695 (13 lines)
- **Notes**: Proof >30 lines? No — 13 lines. Leaf of this file; all hypotheses are carried explicitly.

---

## Cross-Reference Summary

| Declaration | Referenced by (within file) |
|---|---|
| `toClassEquiv'_picDual_add` | `picDual_add_iff_classMap_mul` (×2) |
| `toClassEquiv'_picDual` | `picDual_add_iff_classMap_mul` (×2) |
| `picDual_add_iff_classMap_mul` | `picDual_add_of_classMap_mul` (×1) |
| `picDual_add_of_classMap_mul` | `picDual_add_of_classMap_mulHom`, `picDual_eq_rV_sub_s_of_classMap_mul`, `htrace_dual_of_classMap_mul` (×3) |
| `map_comorphism_mem_nonZeroDivisors` | `classMap_mk0_eq`, `classMap_toClass_some_eq_map`, `classMap_mul_of_ideal_class_mul` (×3+) |
| `classMap_mk0_eq` | `classMap_mul_of_ideal_class_mul` (×3 calls) |
| `classMap_toClass_some_eq_map` | doc only |
| `classMap_mul_of_ideal_class_mul` | doc only |
| `classMap_mul_of_point` | doc only |
| `picDual_eq_rV_sub_s_of_classMap_mul` | none |
| `htrace_dual_of_classMap_mul` | `htrace_dual_genuineIsogSmulSub_of_classMap_mul` (×1) |
| `xyIdeal_isMaximal` | `map_xyIdeal_eq_prod_primesOver` (×2) |
| `map_xyIdeal_eq_prod_primesOver` | doc only |
| `htrace_dual_genuineIsogSmulSub_of_classMap_mul` | none (leaf) |

**Key API** (used by 3+ other declarations in file): `picDual_add_of_classMap_mul`, `map_comorphism_mem_nonZeroDivisors`

**Dead-code candidates in file** (no proof-level callers within file): `picDual_add_of_classMap_mulHom`, `classMap_toClass_some_eq_map`, `classMap_mul_of_ideal_class_mul`, `classMap_mul_of_point`, `picDual_eq_rV_sub_s_of_classMap_mul`, `map_xyIdeal_eq_prod_primesOver`, `htrace_dual_genuineIsogSmulSub_of_classMap_mul`

**Long proofs (>30 lines)**: none

**Sorries**: none

**set_option maxHeartbeats**: none
