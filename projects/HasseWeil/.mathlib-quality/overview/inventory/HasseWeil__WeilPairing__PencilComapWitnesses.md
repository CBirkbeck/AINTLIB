# Inventory: ./HasseWeil/WeilPairing/PencilComapWitnesses.lean

**File purpose**: The `rπ − s` analogue of the leaf-2 closers (`OneSubInftyResidues` + `OneSubAffineResidues` + `OneSubProjOrdTransport`). It assembles the three fields of `ComapPointValuationWitness (W.baseChange K̄) (rπ − s)_{K̄}` for the canonical base-changed pullback `pencilBaseChangePullback`, builds the degree-match-free comap bundle `PencilScalingComapDataCard`, and closes **leaf 3** of the Hasse-bound scaling: `pencilScaling_holds_coprime` (the axiom-clean leaf, consumed by `HasseBound.lean`).

**Imports**: `HasseWeil.WeilPairing.PencilComapScaling`, `HasseWeil.WeilPairing.OneSubInftyResidues`, `HasseWeil.WeilPairing.WallAGenericRealization`, `HasseWeil.WeilPairing.SeparableWitnesses`, `HasseWeil.EC.SeparableKernelTorsor`

**Total declarations**: 77 (`theorem`s, 4 `noncomputable def`, 2 simp `theorem` for `rFrobBaseChange`, 1 local `instance`) — counting the named top-level declarations; the two `rFrobBaseChange_pullback`/`_toAddMonoidHom` simp lemmas at L633/639 are included.

**Contains the project's ONLY `sorry`** at **line 2285** (in `pencilScalingComapDataCard_pDvdR`, a DEAD declaration — see below).

---

## LIVE / DEAD verdict at a glance

The live root is `pencilScaling_holds_coprime` (L2360). The live closure (verified by reading every proof body in the chain) is:

```
pencilScaling_holds_coprime
 ├ pencilJunkPullback, pencilKerCard_pullback_indep
 └ pencilScalingComapDataCard_canonical
    ├ comapPointValuationWitness_pencil
    │  ├ comap_pointValuation_pencil_eq_affine
    │  │  ├ pencil_two_residues ── isog_resid_at_affine_of_hgcomm_hinfty
    │  │  │                          ├ ord_P_isog_pullback_eq_ordAtInfty_translate
    │  │  │                          └ ordAtInfty_translate_eq_ord_P_some
    │  │  ├ omegaPullbackCoeff_pencil_mem_range / _ne_zero ── omegaPullbackCoeff_pencil
    │  │  ├ alpha_star_u_ord_eq_zero_of_residues
    │  │  ├ alpha_star_polyX_ord_eq_zero_of_residues
    │  │  └ inftyOrdTransport_pencil ── ordAtInfty_pencil_pullback_x/y_gen
    │  │                                  ├ pencilBaseChangePullback_x/y_gen ── genuineIsogSmulSub_pullback_x/y_gen
    │  │                                  └ ordAtInfty_genuineIsogSmulSub_pullback_x/y_gen ── genuineIsogSmulSub_pullback_x/y_gen
    │  └ comap_pointValuation_pencil_eq_infty ── ordAtInfty_pencil_pullback_x/y_gen, pencil_hcov_kernel
    └ pencilIsogBaseChange_finiteKer ── pencil_hcov_kernel
```

The **decisive fact**: `pencil_two_residues` (L2032, LIVE) closes the two generator residues via the **transport-to-`O`** lemma `isog_resid_at_affine_of_hgcomm_hinfty` (canonical covariance + `∞`-order-transport) with **no addition-formula case split**. This makes the entire `rFrobBaseChange` addition-summand apparatus (L461–956) and the secant/doubling/`O`-summand case-splitters DEAD.

**DEAD declaration set** (exact, with line ranges):
- The `rFrobBaseChange` summand machinery, L625–956: `rFrobBaseChange` (625), `rFrobBaseChange_pullback` (633), `rFrobBaseChange_toAddMonoidHom` (639), `rFrobBaseChange_pullback_functionFieldMap` (644), `addSlopePair_rFrob_mulByInt` (658), `addPullback_x_pair_rFrob_mulByInt` (679), `addPullback_y_pair_rFrob_mulByInt` (696), `zsmul_frobeniusIsog_pullback_x_gen` (719), `zsmul_frobeniusIsog_pullback_y_gen` (725), `rFrobBaseChange_pullback_x_gen` (731), `rFrobBaseChange_pullback_y_gen` (742), `card_eq_zero_in_functionField` (754), `Dω_rFrobBaseChange_pullback_x_gen` (774), `Dω_rFrobBaseChange_pullback_y_gen` (782), `rFrobBaseChange_apply` (790), `rFrobBaseChange_resid_xy` (806), `rFrobBaseChange_resid_xy_of_ne_zero` (847), `rFrobBaseChange_apply_some` (942).
- The division-poly base-change transports, L475–616 (consumed ONLY by the dead `rFrobBaseChange`/`mulByInt_baseChange` chain): `coordRingMap_algebraMap_Φ` (475), `coordRingMap_algebraMap_ΨSq` (491), `coordRingMap_mk_ψ` (507), `coordRingMap_mk_ω` (518), `functionFieldMap_Φ_ff` (529), `functionFieldMap_ΨSq_ff` (538), `functionFieldMap_ψ_ff` (547), `functionFieldMap_ω_ff` (556), `functionFieldMap_mulByInt_x` (565), `functionFieldMap_mulByInt_y` (574), `mulByInt_baseChange_pullback_x_gen` (584), `mulByInt_baseChange_pullback_y_gen` (602).
- The pullback/point-map decomposition + secant/doubling residue branches, L902–1606, 1869–2025: `pencil_pullback_x_gen_eq_addPullback_x_pair` (902), `pencil_pullback_y_gen_eq_addPullback_y_pair` (914), `pencil_toAddMonoidHom_decomp` (927), `pencil_two_residues_secant` (963), `alpha_star_polyX_ord_eq_zero_of_residues` is **LIVE** (used by eq_affine), `addSlopePair_resid_tangent_of_DωLeft_zero` (1206), `pencil_two_residues_doubling` (1423), `ord_P_isog_pullback_eq_of_comap` (1822), `ord_P_translate_neg_eq_ordAtInfty` (1844), `ordAtInfty_isog_pullback_x_y_of_comap_at_point` (1869), `pencil_two_residues_summand_infty` (1941), `pencil_two_residues_nonsecant` (1982).
- The comap→residue bridges + `[−s']` residue (consumed only by the dead secant/doubling chain): `resid_x_gen_of_comap` (349), `resid_y_gen_of_comap` (389), `mulByInt_neg_resid_xy` (430).
- The off-domain / superseded `_sep` bundle chain, L2160–2348: `pencilIsogBaseChange_rZero_eq_mulByInt` (2160), `mapTranslateGenericPoint_mulByInt_canonical` (2183), `pencilScalingComapDataCard_rZero` (2217), **`pencilScalingComapDataCard_pDvdR` (2282, the `sorry`)**, `pencilScalingComapDataCard_sep` (2290), `pencilScaling_holds` (2330).

**The `sorry`** (L2285) lives in `pencilScalingComapDataCard_pDvdR`, which is reached only from `pencilScalingComapDataCard_sep` → `pencilScaling_holds`. `pencilScaling_holds` has NO consumer anywhere in the project. So the `sorry` is **off the axiom-clean main-theorem path** — `HasseBound.lean` consumes `pencilScaling_holds_coprime`, which routes through `pencilScalingComapDataCard_canonical` and never touches `_pDvdR`.

---

## Declarations

### `theorem genuineIsogSmulSub_pullback_x_gen` — **LIVE**
- **Type**: `(r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0) (hrK : (r:K)≠0) (hsK : (s:K)≠0) : (genuineIsogSmulSub W r s …).pullback (x_gen W) = addPullback_x_pair ((frobeniusIsog W).zsmul r) (mulByInt W.toAffine (-s))`
- **What**: K-level identity: the genuine `rπ − s` pullback on `x_gen` is the addition-formula `x`-coordinate of the summand pair `(r·π, [−s])`.
- **How**: `unfold genuineIsogSmulSub`, `rw [addIsog_pullback]`, then `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq`.
- **Hypotheses**: `r,s ≠ 0`, `(r:K),(s:K) ≠ 0`; `K` finite elliptic.
- **Uses from project**: `genuineIsogSmulSub`, `addPullback_x_pair`, `frobeniusIsog`, `mulByInt`, `OpenLemmaPrimitives.addPullbackAlgHomPair_x_gen_eq`
- **Used by**: `pencilBaseChangePullback_x_gen` (171), `ordAtInfty_genuineIsogSmulSub_pullback_x_gen` (138)
- **Visibility**: public — **Lines**: 120–126
- **Notes**: Live via two independent live consumers.

### `theorem genuineIsogSmulSub_pullback_y_gen` — **LIVE**
- **Type / What**: `y`-analogue of the previous; `= addPullback_y_pair (r·π) [−s]`.
- **How**: same shape (`addPullbackAlgHomPair_y_gen_eq`).
- **Uses from project**: `genuineIsogSmulSub`, `addPullback_y_pair`, `OpenLemmaPrimitives.addPullbackAlgHomPair_y_gen_eq`
- **Used by**: `pencilBaseChangePullback_y_gen` (183), `ordAtInfty_genuineIsogSmulSub_pullback_y_gen` (146)
- **Visibility**: public — **Lines**: 129–135

### `theorem ordAtInfty_genuineIsogSmulSub_pullback_x_gen` — **LIVE**
- **What**: K-level `ord_∞((rπ−s)^K.pullback x_gen) = −2`.
- **How**: `rw [genuineIsogSmulSub_pullback_x_gen]`, then `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg` (the K-level `−2` pole, from `AdditionPullback/Frobenius.lean`).
- **Uses from project**: `genuineIsogSmulSub_pullback_x_gen` (this file), `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`, `W_smooth`
- **Used by**: `ordAtInfty_pencil_pullback_x_gen` (197)
- **Visibility**: public — **Lines**: 138–143

### `theorem ordAtInfty_genuineIsogSmulSub_pullback_y_gen` — **LIVE**
- **What**: K-level `ord_∞(… y_gen) = −3`.
- **How**: `rw [genuineIsogSmulSub_pullback_y_gen]`, then `ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg`.
- **Uses from project**: `genuineIsogSmulSub_pullback_y_gen` (this file), `ord_addPullback_y_pair_zsmul_frobenius_mulByInt_neg`
- **Used by**: `ordAtInfty_pencil_pullback_y_gen` (216)
- **Visibility**: public — **Lines**: 146–151

### `theorem pencilBaseChangePullback_x_gen` — **LIVE**
- **What**: G-004 square (CoordHom-free): `pencilBaseChangePullback x_gen^{K̄} = functionFieldMap ((rπ−s)^K.pullback x_gen^K)`.
- **How**: `rw [pencilBaseChangePullback, ← functionFieldMap_x_gen]`, then `baseChangePullback_functionFieldMap`.
- **Hypotheses**: `r',s' ≠ 0`, `(r':K),(s':K) ≠ 0`.
- **Uses from project**: `pencilBaseChangePullback` (def, PencilSeparable), `functionFieldMap_x_gen`, `genuineIsogSmulSub`, `baseChangePullback_functionFieldMap`
- **Used by**: `ordAtInfty_pencil_pullback_x_gen` (197), `pencil_pullback_x_gen_eq_addPullback_x_pair` (902, DEAD)
- **Visibility**: public — **Lines**: 171–179

### `theorem pencilBaseChangePullback_y_gen` — **LIVE**
- **What / How**: `y`-analogue (`functionFieldMap_y_gen`, `baseChangePullback_functionFieldMap`).
- **Used by**: `ordAtInfty_pencil_pullback_y_gen` (216), `pencil_pullback_y_gen_eq_addPullback_y_pair` (914, DEAD)
- **Visibility**: public — **Lines**: 183–191

### `theorem ordAtInfty_pencil_pullback_x_gen` — **LIVE**
- **What**: `ord_∞^{K̄}((rπ−s)_{K̄}^* x_gen) = −2` (pole order 2 at `O` over `K̄`).
- **How**: `rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_x_gen]`, then transport `ordAtInftyBaseChange_holds` fed the K-level `−2` order; non-`⊤` side-goal via `ordAtInfty_eq_top_iff` + `WithTop.top_ne_coe`.
- **Uses from project**: `ordAtInftyBaseChange_holds`, `pencilIsogBaseChange_pullback` (PencilDualDivisor), `pencilBaseChangePullback_x_gen`/`ordAtInfty_genuineIsogSmulSub_pullback_x_gen` (this file)
- **Used by**: `inftyOrdTransport_pencil` (282), `comap_pointValuation_pencil_eq_infty` (316)
- **Visibility**: public — **Lines**: 197–211

### `theorem ordAtInfty_pencil_pullback_y_gen` — **LIVE**
- **What / How**: `y`-analogue, `= −3`.
- **Uses from project**: same as above with the `y` lemmas.
- **Used by**: `inftyOrdTransport_pencil` (282), `comap_pointValuation_pencil_eq_infty` (316)
- **Visibility**: public — **Lines**: 216–230

### `theorem omegaPullbackCoeff_pencil` — **LIVE**
- **What**: `omegaPullbackCoeff (rπ−s)_{K̄} = algebraMap (algebraMap (−s'))` (the III.5.2 differential-additivity value transported by base change).
- **How**: `rw [omegaPullbackCoeff_baseChangePullback, genuineIsogSmulSub_omegaPullbackCoeff, functionFieldMap_algebraMap_F]`, then `IsScalarTower.algebraMap_apply`.
- **Uses from project**: `omegaPullbackCoeff_baseChangePullback`, `genuineIsogSmulSub_omegaPullbackCoeff`, `Curves.SmoothPlaneCurve.functionFieldMap_algebraMap_F`, `pencilIsogBaseChange_pullback`
- **Used by**: `omegaPullbackCoeff_pencil_mem_range` (259), `omegaPullbackCoeff_pencil_ne_zero` (270)
- **Visibility**: public — **Lines**: 240–256

### `theorem omegaPullbackCoeff_pencil_mem_range` — **LIVE**
- **What**: `omegaPullbackCoeff (rπ−s)_{K̄} ∈ range (algebraMap K̄ K(E_{K̄}))` (constancy datum).
- **How**: `rw [omegaPullbackCoeff_pencil]`, then `⟨_, rfl⟩`.
- **Uses from project**: `omegaPullbackCoeff_pencil` (this file)
- **Used by**: `comap_pointValuation_pencil_eq_affine` (2061)
- **Visibility**: public — **Lines**: 259–267

### `theorem omegaPullbackCoeff_pencil_ne_zero` — **LIVE**
- **What**: `omegaPullbackCoeff (rπ−s)_{K̄} ≠ 0` (separability datum: `p∤s' ⟹ −s'≠0`).
- **How**: `rw [omegaPullbackCoeff_pencil, map_eq_zero, map_eq_zero]`, then `neg_ne_zero.mpr hsK`.
- **Uses from project**: `omegaPullbackCoeff_pencil` (this file)
- **Used by**: `comap_pointValuation_pencil_eq_affine` (2061)
- **Visibility**: public — **Lines**: 270–276

### `theorem inftyOrdTransport_pencil` — **LIVE**
- **What**: `InftyOrdTransport (rπ−s)_{K̄}` — the `infinity` field of the comap witness.
- **How**: `inftyOrdTransport_of_ordAtInfty_x_y` (field-general pinning) applied to the two `K̄` orders `−2`, `−3`.
- **Uses from project**: `DivisorPullback.inftyOrdTransport_of_ordAtInfty_x_y`, `ordAtInfty_pencil_pullback_x_gen`/`_y_gen` (this file), `pencilIsogBaseChange`
- **Used by**: `comapPointValuationWitness_pencil` (2095), `comap_pointValuation_pencil_eq_infty` (316), `pencil_two_residues` (2032), `comap_pointValuation_pencil_eq_affine` (2061), `pencil_two_residues_summand_infty` (1941, DEAD)
- **Visibility**: public — **Lines**: 282–291
- **Notes**: A key load-bearing leaf (5 internal references).

### `theorem pencil_hcov_kernel` — **LIVE**
- **What**: kernel-translation invariance (III.4.10c): for `k ∈ ker(rπ−s)`, `τ_k` fixes the pullback range.
- **How**: `hcov_of_mapTranslateGenericPoint_canonical` fed the proved Wall A `mapTranslateGenericPoint_pencil_canonical` (PencilCovariance).
- **Uses from project**: `hcov_of_mapTranslateGenericPoint_canonical`, `mapTranslateGenericPoint_pencil_canonical` (PencilCovariance), `pencilIsogBaseChange`, `translateAlgEquivOfPoint`
- **Used by**: `pencilIsogBaseChange_finiteKer` (2118), `comap_pointValuation_pencil_eq_infty` (316)
- **Visibility**: public — **Lines**: 297–310
- **Notes**: Supplies the only `hcov` input to the trace-free finite-kernel route.

### `theorem comap_pointValuation_pencil_eq_infty` — **LIVE**
- **What**: the `affineToInfty` field — the infinity comap identity at a smooth `P` whose image is `O`.
- **How**: `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` (field-general translation-invariance trick) fed the two `∞`-orders and `pencil_hcov_kernel`.
- **Uses from project**: `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`, `ordAtInfty_pencil_pullback_x/y_gen`, `pencil_hcov_kernel` (this file)
- **Used by**: `comapPointValuationWitness_pencil` (2095)
- **Visibility**: public — **Lines**: 316–336

### `theorem resid_x_gen_of_comap` — **DEAD**
- **What**: comap → `x`-generator residue: from an affine-image comap identity for any isogeny `α`, `α^* x_gen ≡ x` mod `m_P`.
- **How**: apply comap to `x_gen − x ∈ m_Q`, push `α^*` through subtraction (`α.pullback.commutes`), `x_gen_sub_const_eq_algebraMap_XClass`, `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`.
- **Uses from project**: `Valuation.comap_apply`, `x_gen_sub_const_eq_algebraMap_XClass`, `XClass_mem_maximalIdealAt`, `pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt`
- **Used by**: `mulByInt_neg_resid_xy` (456), `rFrobBaseChange_resid_xy` (832) — both DEAD
- **Visibility**: public — **Lines**: 349–386
- **Notes**: A reusable, general, well-written bridge — but only consumed by the dead secant residue chain. **Candidate to keep** if a future re-route to the addition-formula residues is wanted; otherwise dead.

### `theorem resid_y_gen_of_comap` — **DEAD**
- **What / How**: `y`-analogue of `resid_x_gen_of_comap`; ends with `pointValuation_y_gen_sub_const_lt_one_at_smoothPoint`.
- **Used by**: `mulByInt_neg_resid_xy` (458), `rFrobBaseChange_resid_xy` (834) — both DEAD
- **Visibility**: public — **Lines**: 389–424

### `theorem mulByInt_neg_resid_xy` — **DEAD**
- **What**: the `[−s']` per-summand residues (`x` and `y`) at the `[−s']`-image `some x₂ y₂`.
- **How**: `comap_pointValuation_mulByInt_eq_affine` + the two comap→residue bridges.
- **Uses from project**: `comap_pointValuation_mulByInt_eq_affine`, `resid_x_gen_of_comap`, `resid_y_gen_of_comap` (this file)
- **Used by**: `pencil_two_residues_secant` (1000), `pencil_two_residues_doubling` (1513) — both DEAD
- **Visibility**: public — **Lines**: 430–459

### `theorem coordRingMap_algebraMap_Φ` — **DEAD**
- **What**: `coordRingMap` sends `algebraMap (W.Φ m)` to the base-changed `Φ m`.
- **How**: `CoordinateRing.map_mk` + `Polynomial.map_C` + `WeierstrassCurve.map_Φ`.
- **Uses from project**: `WeierstrassCurve.Affine.CoordinateRing.map_mk`, `WeierstrassCurve.map_Φ`
- **Used by**: `functionFieldMap_Φ_ff` (529) — DEAD
- **Visibility**: public — **Lines**: 475–488

### `theorem coordRingMap_algebraMap_ΨSq` — **DEAD**
- **What / How**: as above for `ΨSq` (`WeierstrassCurve.map_ΨSq`).
- **Used by**: `functionFieldMap_ΨSq_ff` (538) — DEAD
- **Visibility**: public — **Lines**: 491–504

### `theorem coordRingMap_mk_ψ` — **DEAD**
- **What / How**: `coordRingMap (mk (W.ψ m)) = mk (ψ m)_{K̄}` via `CoordinateRing.map_mk` + `WeierstrassCurve.map_ψ`.
- **Used by**: `functionFieldMap_ψ_ff` (547) — DEAD
- **Visibility**: public — **Lines**: 507–515

### `theorem coordRingMap_mk_ω` — **DEAD**
- **What / How**: as above for `ω` (`WeierstrassCurve.map_ω`).
- **Used by**: `functionFieldMap_ω_ff` (556) — DEAD
- **Visibility**: public — **Lines**: 518–526

### `theorem functionFieldMap_Φ_ff` / `_ΨSq_ff` / `_ψ_ff` / `_ω_ff` — **DEAD** (group)
- **What**: transport of `Φ_ff`/`ΨSq_ff`/`ψ_ff`/`ω_ff` under `functionFieldMap`.
- **How**: each `rw [<ff-def>, functionFieldMap_algebraMap, coordRingMap_…]; rfl`.
- **Uses from project**: `HasseWeil.Φ_ff`/`ΨSq_ff`/`ψ_ff`/`ω_ff`, `SmoothPlaneCurve.functionFieldMap_algebraMap`, the corresponding `coordRingMap_…` (this file)
- **Used by**: `functionFieldMap_mulByInt_x` (565), `functionFieldMap_mulByInt_y` (574) — DEAD
- **Visibility**: public — **Lines**: 529–562

### `theorem functionFieldMap_mulByInt_x` / `_y` — **DEAD**
- **What**: `functionFieldMap (mulByInt_x/y W m) = mulByInt_x/y (E_{K̄}) m`.
- **How**: `rw [mulByInt_x, map_div₀, functionFieldMap_Φ_ff, functionFieldMap_ΨSq_ff]` (resp. `_ω_ff`, `_ψ_ff`).
- **Used by**: `mulByInt_baseChange_pullback_x_gen`/`_y_gen` (584/602) — DEAD
- **Visibility**: public — **Lines**: 565–580

### `theorem mulByInt_baseChange_pullback_x_gen` / `_y_gen` — **DEAD**
- **What**: the linchpin mulByInt base-change naturality `(mulByInt^{K̄} m)^* x_gen = functionFieldMap((mulByInt^K m)^* x_gen)`.
- **How**: `rw [mulByInt_pullback_x, functionFieldMap_mulByInt_x]` etc.
- **Uses from project**: `mulByInt_pullback_x/y`, `functionFieldMap_mulByInt_x/y` (this file)
- **Used by**: `addSlopePair_rFrob_mulByInt` (664), `addPullback_x/y_pair_rFrob_mulByInt` (685/702), `rFrobBaseChange_pullback_x/y_gen` (735/746) — all DEAD
- **Visibility**: public — **Lines**: 584–616
- **Notes**: Memory flags `(mulByInt ℓ).CoordHom` as IMPOSSIBLE; this is the CoordHom-FREE workaround built for the dead secant route.

### `noncomputable def rFrobBaseChange` — **DEAD**
- **Type**: `(r' : ℤ) : Isogeny (E_{K̄}) (E_{K̄})`
- **What**: the bespoke `r·π̄` summand isogeny; pullback the transparent base change of `((frobeniusIsog W).zsmul r').pullback`, point map `r'•π̄`.
- **How**: `Isogeny.mkBaseChange` of those two data.
- **Uses from project**: `Isogeny.mkBaseChange`, `baseChangePullback`, `frobeniusIsog`, `frobeniusHomBaseChange`
- **Used by**: the entire dead secant/doubling residue apparatus
- **Visibility**: public — **Lines**: 625–631

### `@[simp] theorem rFrobBaseChange_pullback` / `rFrobBaseChange_toAddMonoidHom` — **DEAD**
- **What**: the two structure-field unfoldings of `rFrobBaseChange`.
- **How**: `Isogeny.mkBaseChange_pullback`/`_toAddMonoidHom`.
- **Used by**: `rFrobBaseChange_pullback_functionFieldMap` (649), `rFrobBaseChange_apply` (794), `pencil_toAddMonoidHom_decomp` (934) — all DEAD
- **Visibility**: public — **Lines**: 633–642

### `theorem rFrobBaseChange_pullback_functionFieldMap` — **DEAD**
- **What**: `(rFrobBaseChange r')^*(functionFieldMap z) = functionFieldMap(((frobeniusIsog).zsmul r')^* z)`.
- **How**: `rw [rFrobBaseChange_pullback]`, `baseChangePullback_functionFieldMap`.
- **Used by**: `addSlopePair_rFrob_mulByInt`, `addPullback_x/y_pair_rFrob_mulByInt`, `rFrobBaseChange_pullback_x/y_gen` — all DEAD
- **Visibility**: public — **Lines**: 644–652

### `theorem addSlopePair_rFrob_mulByInt` — **DEAD**
- **What**: `addSlopePair (rFrob) ([−s']) = functionFieldMap(addSlopePair^K ((zsmul r')) ([−s']))`.
- **How**: `rw [addSlopePair]` ×2, mulByInt + rFrob naturalities, `Affine.map_slope`.
- **Uses from project**: `addSlopePair`, `mulByInt_baseChange_pullback_x/y_gen`, `functionFieldMap_x/y_gen`, `rFrobBaseChange_pullback_functionFieldMap`, `W_KE_map_functionFieldMap`, `Affine.map_slope`
- **Used by**: `addPullback_x/y_pair_rFrob_mulByInt` (684/701) — DEAD
- **Visibility**: public — **Lines**: 658–676

### `theorem addPullback_x_pair_rFrob_mulByInt` / `_y_pair_…` — **DEAD**
- **What**: base-change of `addPullback_x/y_pair (rFrob) ([−s'])` through `functionFieldMap`.
- **How**: `rw [addPullback_x_pair, addSlopePair_rFrob_mulByInt, …]`, `Affine.map_addX` (resp. `map_addY`).
- **Used by**: `pencil_pullback_x/y_gen_eq_addPullback_x/y_pair` (911/923) — DEAD
- **Visibility**: public — **Lines**: 679–713

### `theorem zsmul_frobeniusIsog_pullback_x_gen` / `_y_gen` — **DEAD**
- **What**: K-level `((frobeniusIsog).zsmul r')^* gen = ((mulByInt r')^* gen)^q`.
- **How**: `rw [Isogeny.zsmul, Isogeny.comp_algebraMap_eq, frobeniusIsog_pullback_apply]`.
- **Used by**: `rFrobBaseChange_pullback_x/y_gen` (737/748) — DEAD
- **Visibility**: public — **Lines**: 719–728

### `theorem rFrobBaseChange_pullback_x_gen` / `_y_gen` — **DEAD**
- **What**: `(rFrobBaseChange r')^* gen^{K̄} = ((mulByInt^{K̄} r')^* gen)^q`.
- **How**: mulByInt naturality + `rFrobBaseChange_pullback_functionFieldMap` + `zsmul_frobeniusIsog_pullback_x/y_gen` + `map_pow`.
- **Used by**: `Dω_rFrobBaseChange_pullback_x/y_gen`, `rFrobBaseChange_resid_xy(_of_ne_zero)` — all DEAD
- **Visibility**: public — **Lines**: 731–750

### `theorem card_eq_zero_in_functionField` — **DEAD**
- **What**: `(card K : K(E_{K̄})) = 0` (char `p`, `q = p^r`).
- **How**: `charP_of_injective_algebraMap` twice + `CharP.cast_eq_zero_iff` + `dvd_pow_self`.
- **Used by**: `Dω_rFrobBaseChange_pullback_x/y_gen` (778/786) — DEAD
- **Visibility**: public — **Lines**: 754–771

### `theorem Dω_rFrobBaseChange_pullback_x_gen` / `_y_gen` — **DEAD**
- **What**: `Dω((rFrobBaseChange r')^* gen) = 0` (the Frobenius `q`-power kills the `ω`-derivative).
- **How**: `rw [rFrobBaseChange_pullback_x_gen, Dω_pow, card_eq_zero_in_functionField, zero_mul, zero_mul]`.
- **Used by**: `addSlopePair_resid_tangent_of_DωLeft_zero` (1556/1557, DEAD)
- **Visibility**: public — **Lines**: 774–787

### `theorem rFrobBaseChange_apply` — **DEAD**
- **What**: `(rFrobBaseChange r') Q = π̄([r'] Q)`.
- **How**: `rw [rFrobBaseChange_toAddMonoidHom, AddMonoidHom.smul_apply, mulByInt_apply, map_zsmul]`.
- **Used by**: `rFrobBaseChange_apply_some` (955) — DEAD
- **Visibility**: public — **Lines**: 790–795

### `theorem rFrobBaseChange_resid_xy` — **DEAD**
- **What**: the `r·π̄` per-summand residues (separable form, `(r':K)≠0`): generators residue to `x₁^q, y₁^q`.
- **How**: `comap_pointValuation_mulByInt_eq_affine` + the comap→residue bridges + `residPV_pow`.
- **Uses from project**: `comap_pointValuation_mulByInt_eq_affine`, `resid_x/y_gen_of_comap`, `rFrobBaseChange_pullback_x/y_gen`, `residPV_pow` (this file + project)
- **Used by**: `pencil_two_residues_secant` (999), `pencil_two_residues_doubling` (1512) — DEAD
- **Visibility**: public — **Lines**: 806–840

### `theorem rFrobBaseChange_resid_xy_of_ne_zero` — **DEAD**
- **What**: the separability-FREE (`r'≠0` only) version of the `r·π̄` residues; the `[r']`-residue from the *geometric* `pointValuation_mulByInt_x/y_sub_lt_one_of_ne_zero`. Designed as the `p∣r'` linchpin.
- **How**: geometric value bridges + `residPV_pow`.
- **Uses from project**: `pointValuation_mulByInt_x/y_sub_lt_one_of_ne_zero`, `mulByInt_pullback_x/y`, `rFrobBaseChange_pullback_x/y_gen`, `residPV_pow`
- **Used by**: NONE (orphan; was intended for `pencilScalingComapDataCard_pDvdR`, never wired)
- **Visibility**: public — **Lines**: 847–895
- **Notes**: Completely unreferenced even within the dead subtree.

### `theorem pencil_pullback_x_gen_eq_addPullback_x_pair` / `_y_gen_…` — **DEAD**
- **What**: `(rπ−s)^* gen = addPullback_x/y_pair (rFrobBaseChange r') ([−s'])`.
- **How**: `rw [pencilIsogBaseChange_pullback, pencilBaseChangePullback_x/y_gen, genuineIsogSmulSub_pullback_x/y_gen, ← addPullback_x/y_pair_rFrob_mulByInt]`.
- **Used by**: `pencil_two_residues_secant` (1018/1019), `pencil_two_residues_doubling` (1585/1586) — DEAD
- **Visibility**: public — **Lines**: 902–923

### `theorem pencil_toAddMonoidHom_decomp` — **DEAD**
- **What**: point-map decomposition `(rπ−s)P = (rFrobBaseChange r')P + ([−s'])P`.
- **How**: `rw [pencilIsogBaseChange_toAddMonoidHom, rFrobBaseChange_toAddMonoidHom, AddMonoidHom.sub_apply, …, neg_smul, sub_eq_add_neg]`.
- **Used by**: `pencil_two_residues_secant` (1006), `pencil_two_residues_doubling` (1466) — DEAD
- **Visibility**: public — **Lines**: 927–936

### `theorem rFrobBaseChange_apply_some` — **DEAD**
- **What**: `(rFrobBaseChange r')` on the `[r']`-image `some xr yr` gives `some (xr^q) (yr^q)` (via `frobeniusAlgHom`).
- **How**: `rw [rFrobBaseChange_apply, hQr, frobeniusHomBaseChange_apply_some]`.
- **Used by**: `pencil_two_residues_secant` (997), `pencil_two_residues_doubling` (1460) — DEAD
- **Visibility**: public — **Lines**: 942–955

### `theorem pencil_two_residues_secant` — **DEAD**
- **What**: the two generator residues at a non-doubling affine image (secant branch), via `isog_coords_at_affine_of_decomp` with the summand pair `(rFrobBaseChange r', [−s'])`.
- **How**: assemble `rFrobBaseChange_apply_some`, the two summand residues, `pencil_toAddMonoidHom_decomp`, then `isog_coords_at_affine_of_decomp`.
- **Uses from project**: `rFrobBaseChange_apply_some`, `rFrobBaseChange_resid_xy`, `mulByInt_neg_resid_xy`, `pencil_toAddMonoidHom_decomp`, `pencil_pullback_x/y_gen_eq_addPullback_x/y_pair`, `isog_coords_at_affine_of_decomp`, `FiniteField.coe_frobeniusAlgHom`
- **Used by**: NONE (orphan — `pencil_two_residues_nonsecant` does NOT call it; it inlines the secant case into the doubling/`O` split)
- **Visibility**: public — **Lines**: 963–1020
- **Notes**: Fully orphaned dead leaf.

### `theorem alpha_star_u_ord_eq_zero_of_residues` — **LIVE**
- **What**: general `e=1` (non-2-torsion image): for any isogeny `α` whose generators residue to `x,y` at `P` with `2y+a₁x+a₃ ≠ 0`, the differential denominator `α^*u` is a unit at `P` (`ord_P = 0`).
- **How**: `alpha_star_u_eq` + `residPV_const`/`_add`/`_mul` to residue `α^*u ≡ 2y+a₁x+a₃`, then `residPV_unit`, then `ord_P_eq_zero_iff_pointValuation_eq_one`.
- **Uses from project**: `alpha_star_u`, `alpha_star_u_eq`, `u_gen`, `residPV_const/add/mul/unit`, `ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `comap_pointValuation_pencil_eq_affine` (2087, LIVE); also `pencil_two_residues_doubling` (1544, DEAD)
- **Visibility**: public — **Lines**: 1079–1126
- **Notes**: LIVE via eq_affine. The `α`-agnostic form is reused in both the live and dead consumers.

### `theorem alpha_star_polyX_ord_eq_zero_of_residues` — **LIVE**
- **What**: general `e=1` (2-torsion image): the `y`-numerator `α^*ν` (the `3x²+2a₂x+a₄−a₁y` polynomial) is a unit at `P`.
- **How**: nonsingularity ⟹ `ν(Q)≠0`; residue `α^*ν ≡ ν(Q)` via `residPV_*`; `residPV_unit`; `ord_P_eq_zero_iff_pointValuation_eq_one`.
- **Uses from project**: `Affine.nonsingular_iff'`, `residPV_const/add/sub/mul/pow/unit`, `ord_P_eq_zero_iff_pointValuation_eq_one`
- **Used by**: `comap_pointValuation_pencil_eq_affine` (2082, LIVE)
- **Visibility**: public — **Lines**: 1129–1191
- **Notes**: LIVE (only consumer is the live eq_affine, 2-torsion branch).

### `theorem addSlopePair_resid_tangent_of_DωLeft_zero` — **DEAD**
- **What**: the L'Hôpital tangent-slope residue for the doubling case where the *first* summand `α₁` is differential-vanishing (Frobenius-composed). `addSlopePair − λ` has `ord_P ≥ 1`.
- **How**: invariant-differential L'Hôpital argument (`set_option maxHeartbeats 8000000`).
- **Uses from project**: `Dω`, `residPV_*`, the invariant-differential machinery; `Dω_rFrobBaseChange_pullback_x/y_gen` (via the doubling caller)
- **Used by**: `pencil_two_residues_doubling` (1554) — DEAD
- **Visibility**: public — **Lines**: 1206–~1421 (the longest proof in the file)
- **Notes**: Comment at L1069/2031 records this branch historically carried `sorryAx`; it is now `sorry`-free but DEAD (bypassed by transport-to-`O`).

### `theorem pencil_two_residues_doubling` — **DEAD**
- **What**: the doubling/tangent branch of the two-residue case-split (both summands affine, `frob xr = xs`).
- **How**: `rFrobBaseChange_apply_some` + `pencil_toAddMonoidHom_decomp` + `addSlopePair_resid_tangent_of_DωLeft_zero` + `alpha_star_*` + the addition-pullback decompositions.
- **Uses from project**: `rFrobBaseChange_apply_some`, `pencil_toAddMonoidHom_decomp`, `addSlopePair_resid_tangent_of_DωLeft_zero`, `Dω_rFrobBaseChange_pullback_x/y_gen`, `mulByInt_neg_resid_xy`, `pencil_pullback_x/y_gen_eq_addPullback_x/y_pair`
- **Used by**: `pencil_two_residues_nonsecant` (2025) — DEAD
- **Visibility**: public — **Lines**: 1423–~1606

### `theorem ordAtInfty_translate_eq_ord_P_some` — **LIVE**
- **What**: `ord_∞(τ_R w) = ord_P ⟨xR,yR⟩ w` for finite `R = some xR yR`, `w ≠ 0`.
- **How**: `ordProj_translate_infinity` at `infinity`, `ordProj_infinity`, `placeTranslate_infinity`.
- **Uses from project**: `ordProj_translate_infinity`, `ordProj_infinity`, `placeTranslate_infinity`
- **Used by**: `isog_resid_at_affine_of_hgcomm_hinfty` (1674)
- **Visibility**: public — **Lines**: 1607–1621

### `theorem ord_P_isog_pullback_eq_ordAtInfty_translate` — **LIVE**
- **What**: the transport-to-`O` identity `ord_P P (φ^*w) = ord_∞(φ^*(τ_R w))` where `R = φP` finite.
- **How**: translation covariance `hcomm_of_mapTranslateGenericPoint_canonical` at `S = −P`, `translateAlgEquivOfPoint_add_apply`, the `∞`-target transport `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint` (at `P + (−P) = O`).
- **Uses from project**: `hcomm_of_mapTranslateGenericPoint_canonical`, `translateAlgEquivOfPoint_add_apply`, `isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint`
- **Used by**: `isog_resid_at_affine_of_hgcomm_hinfty` (1719), `ordAtInfty_isog_pullback_x_y_of_comap_at_point` (1895, DEAD)
- **Visibility**: public — **Lines**: 1627–1667
- **Notes**: A general, isogeny-agnostic transport lemma — the heart of the live affine-residue route.

### `theorem isog_resid_at_affine_of_hgcomm_hinfty` — **LIVE**
- **What**: the transport-to-`O` affine residue: for ANY isogeny `φ` over `K̄` with canonical covariance `hgcomm` and `InftyOrdTransport hinfty`, at a smooth `P` with affine image `φP = some x y`, both generators residue to `x,y` mod `m_P`. **No addition-formula decomposition** — covers the `O`-summand degeneracy uniformly.
- **How**: a generic single-generator `step` (using `ord_P_isog_pullback_eq_ordAtInfty_translate`, `InftyOrdTransport`, `ordAtInfty_translate_eq_ord_P_some`, and `x_gen − x ∈ m_R`), applied to both generators.
- **Hypotheses**: `hgcomm`, `hinfty`, smooth `P`, affine image `hQ`.
- **Uses from project**: `ord_P_isog_pullback_eq_ordAtInfty_translate`, `ordAtInfty_translate_eq_ord_P_some` (this file), `InftyOrdTransport`, `translateAlgEquivOfPoint`, `Isogeny.pullback_injective`
- **Used by**: `pencil_two_residues` (2054, LIVE), `pencil_two_residues_summand_infty` (1969, DEAD)
- **Visibility**: public — **Lines**: 1674–~1821
- **Notes**: **The key innovation that retires the entire addition-formula residue apparatus.** Long proof; load-bearing.

### `theorem ord_P_isog_pullback_eq_of_comap` — **DEAD**
- **What**: `ord_P P (φ^*v) = ord_P ⟨xR,yR⟩ v` from a full affine comap identity.
- **How**: `congrFun (congrArg DFunLike.coe hcomap)`, `Valuation.comap_apply`, unfold `ord_P`.
- **Used by**: `ordAtInfty_isog_pullback_x_y_of_comap_at_point` (1906) — DEAD
- **Visibility**: public — **Lines**: 1822–1840

### `theorem ord_P_translate_neg_eq_ordAtInfty` — **DEAD**
- **What**: `ord_R(τ_{−R} gen) = ord_∞ gen` for finite `R`, `gen ≠ 0`.
- **How**: `ordProj_translate` at `affine R`, `S = −R`; `placeTranslate_affine`, `add_neg_cancel`.
- **Used by**: `ordAtInfty_isog_pullback_x_y_of_comap_at_point` (1909) — DEAD
- **Visibility**: public — **Lines**: 1844–1863

### `theorem ordAtInfty_isog_pullback_x_y_of_comap_at_point` — **DEAD**
- **What**: Route-C keystone: the two `∞`-orders `−2`, `−3` of `φ^* x/y_gen` from the affine comap at a single finite-image point (intended for the `p∣r'` separable member).
- **How**: single-generator `step` via transport-to-`O` + `ord_P_isog_pullback_eq_of_comap` + `ord_P_translate_neg_eq_ordAtInfty`; then `ordAtInfty_x/y_gen`.
- **Uses from project**: `ord_P_isog_pullback_eq_ordAtInfty_translate`, `translateAlgEquivOfPoint_add_apply`, `ord_P_isog_pullback_eq_of_comap`, `ord_P_translate_neg_eq_ordAtInfty`, `ordAtInfty_x/y_gen`
- **Used by**: NONE (orphan; was the planned ingredient to close the `_pDvdR` `sorry`)
- **Visibility**: public — **Lines**: 1869–1915
- **Notes**: Dead because `pencilScalingComapDataCard_pDvdR` (its target) is off the bound path.

### `theorem pencil_two_residues_summand_infty` — **DEAD**
- **What**: the two pencil generator residues when one addition summand is `O`.
- **How**: directly `isog_resid_at_affine_of_hgcomm_hinfty` (the `hinfty` hypothesis is *unused*).
- **Uses from project**: `isog_resid_at_affine_of_hgcomm_hinfty`, `mapTranslateGenericPoint_pencil_canonical`, `inftyOrdTransport_pencil`
- **Used by**: `pencil_two_residues_nonsecant` (2016/2020) — DEAD
- **Visibility**: public — **Lines**: 1941–1974
- **Notes**: A pencil-specialised wrapper of `isog_resid_at_affine_of_hgcomm_hinfty`; superseded by the more direct `pencil_two_residues`.

### `theorem pencil_two_residues_nonsecant` — **DEAD**
- **What**: the case-splitter for the non-secant cases (one summand `O` → `_summand_infty`; both affine + `frob xr = xs` → `_doubling`).
- **How**: `rcases` on the two summand images, dispatch.
- **Uses from project**: `pencil_two_residues_summand_infty`, `pencil_two_residues_doubling` (this file)
- **Used by**: NONE (orphan)
- **Visibility**: public — **Lines**: 1982–2025

### `theorem pencil_two_residues` — **LIVE**
- **What**: the two pencil generator residues at any affine image, uniformly via transport-to-`O` (no case split).
- **How**: directly `isog_resid_at_affine_of_hgcomm_hinfty` fed `mapTranslateGenericPoint_pencil_canonical` and `inftyOrdTransport_pencil`.
- **Uses from project**: `isog_resid_at_affine_of_hgcomm_hinfty` (this file), `mapTranslateGenericPoint_pencil_canonical` (PencilCovariance), `inftyOrdTransport_pencil` (this file)
- **Used by**: `comap_pointValuation_pencil_eq_affine` (2075)
- **Visibility**: public — **Lines**: 2032–2059
- **Notes**: **This is what makes the secant/doubling/`_nonsecant`/`_summand_infty` branches dead.** Note it does NOT use `hr/hs/hrK/hsK` substantively beyond constructing the pencil — could in principle be stated more generally.

### `theorem comap_pointValuation_pencil_eq_affine` — **LIVE**
- **What**: the `affine` field — the unconditional affine-image comap identity at every smooth `P` with affine image `(rπ−s)P = some x y`.
- **How**: `obtain ⟨hx,hy⟩ := pencil_two_residues`; case-split `2y+a₁x+a₃ = 0`; the headline `comap_pointValuation_isog_eq_affine_y` (2-torsion) / `comap_pointValuation_isog_eq_affine` (non-2-torsion) fed the omega datum, the two residues, and `alpha_star_polyX/u_ord_eq_zero_of_residues`.
- **Uses from project**: `pencil_two_residues`, `omegaPullbackCoeff_pencil_mem_range`/`_ne_zero`, `alpha_star_u_ord_eq_zero_of_residues`, `alpha_star_polyX_ord_eq_zero_of_residues` (this file); `comap_pointValuation_isog_eq_affine(_y)` (AdditionPullback/SamePlace)
- **Used by**: `comapPointValuationWitness_pencil` (2095)
- **Visibility**: public — **Lines**: 2061–2087
- **Notes**: Axiom-clean. The substantive `affine` content of the leaf-3 comap witness.

### `theorem comapPointValuationWitness_pencil` — **LIVE**
- **What**: the assembled `ComapPointValuationWitness (rπ−s)_{K̄}` (all three fields).
- **How**: structure with `affine := comap_…_eq_affine`, `affineToInfty := comap_…_eq_infty`, `infinity := inftyOrdTransport_pencil`.
- **Uses from project**: `comap_pointValuation_pencil_eq_affine`, `comap_pointValuation_pencil_eq_infty`, `inftyOrdTransport_pencil` (this file)
- **Used by**: `pencilScalingComapDataCard_canonical` (2132)
- **Visibility**: public — **Lines**: 2095–2103

### `theorem pencilIsogBaseChange_finiteKer` — **LIVE**
- **What**: `Finite (ker (rπ−s)_{K̄})`, via the **trace-free / dual-free** route `HasseWeil.finite_kernel_of_hcov` (Silverman III.4.10a/c).
- **How**: `finite_kernel_of_hcov` fed only the kernel-translation covariance `pencil_hcov_kernel`.
- **Uses from project**: `HasseWeil.finite_kernel_of_hcov`, `pencil_hcov_kernel` (this file), `pencilIsogBaseChange`, `pencilBaseChangePullback`
- **Used by**: `pencilScalingComapDataCard_canonical` (2138)
- **Visibility**: public — **Lines**: 2118–2125
- **Notes**: Deliberately sidesteps the Frobenius-dual route (`ker ⊆ E[(rπ̂−s)∘(rπ−s)]`), which is a genuine wall over `K̄` (no `V̄`, no char-poly). Supplies the `finiteKer` field directly, so the degree match `#ker = deg` is never needed on the live path.

### `noncomputable def pencilScalingComapDataCard_canonical` — **LIVE** (key API)
- **Type**: `(r' s' : ℤ) (hr : r' ≠ 0) (hs : s' ≠ 0) (hrK) (hsK) : PencilScalingComapDataCard W p r r' s'`
- **What**: the degree-match-free comap bundle for the canonical pullback on the genuine locus (`p∤r', s'`). The single object the axiom-clean leaf is built from.
- **How**: structure with `pullback_L := pencilBaseChangePullback`, `hgcomm := pencilScalingComapData_hgcomm_canonical`, `hcomap := comapPointValuationWitness_pencil`, `finiteKer := pencilIsogBaseChange_finiteKer`.
- **Uses from project**: `pencilBaseChangePullback` (PencilSeparable), `pencilScalingComapData_hgcomm_canonical` (PencilComapScaling), `comapPointValuationWitness_pencil`, `pencilIsogBaseChange_finiteKer` (this file)
- **Used by**: `pencilScaling_holds_coprime` (2377, LIVE), `pencilScalingComapDataCard_sep` (2302, DEAD)
- **Visibility**: public — **Lines**: 2132–2138
- **Notes**: **The reviewer-endorsed canonical bundle**; carries NO `p∣r'` sorry (unlike `_pDvdR`).

### `theorem pencilIsogBaseChange_rZero_eq_mulByInt` — **DEAD**
- **What**: for `r' = 0`, `pencilIsogBaseChange 0 s' (mulByInt(−s'))^* = mulByInt (−s')` as isogenies.
- **How**: prove the hom field equals `[−s'].toAddMonoidHom`, then structure eta `show … = _; rw`.
- **Uses from project**: `pencilIsogBaseChange_toAddMonoidHom`, `mulByInt`
- **Used by**: `pencilScalingComapDataCard_rZero` (2223/2226/2230) — DEAD
- **Visibility**: public — **Lines**: 2160–2176

### `theorem mapTranslateGenericPoint_mulByInt_canonical` — **DEAD**
- **What**: the canonical-action `[m]` generic-point covariance over `K̄` (converts the `zsmulPointHom` action to the `Point.map [m]^*` action).
- **How**: build `IsGenuineWith [m] (zsmulPointHom m)`, then `mapTranslateGenericPoint_canonical_of_genuine` fed `mapTranslateGenericPoint_mulByInt` (PencilCovariance).
- **Uses from project**: `zsmul_genericPoint_eq`, `mulByInt_x/y`, `mulByInt_pullback_x/y`, `zsmulPointHom`, `mapTranslateGenericPoint_canonical_of_genuine`, `mapTranslateGenericPoint_mulByInt` (PencilCovariance)
- **Used by**: `pencilScalingComapDataCard_rZero` (2224/2233) — DEAD
- **Visibility**: public — **Lines**: 2183–2207

### `noncomputable def pencilScalingComapDataCard_rZero` — **DEAD**
- **Type**: `(s' : ℤ) (hsbar : ((-s':ℤ):K̄) ≠ 0) : PencilScalingComapDataCard W p r 0 s'`
- **What**: the `r' = 0` comap bundle (pure `[−s']` member), identifying the whole isogeny with `mulByInt (−s')` and using the proved `comapPointValuationWitness_mulByInt`.
- **How**: `rw [pencilIsogBaseChange_rZero_eq_mulByInt]` in each field; `comapPointValuationWitness_mulByInt`, `mapTranslateGenericPoint_mulByInt_canonical`, `finite_kernel_of_hcov`.
- **Uses from project**: `pencilIsogBaseChange_rZero_eq_mulByInt`, `mapTranslateGenericPoint_mulByInt_canonical` (this file), `DivisorPullback.comapPointValuationWitness_mulByInt`, `finite_kernel_of_hcov`, `hcov_of_mapTranslateGenericPoint_canonical`
- **Used by**: `pencilScalingComapDataCard_sep` (2294) — DEAD
- **Visibility**: public — **Lines**: 2217–2235

### `noncomputable def pencilScalingComapDataCard_pDvdR` — **DEAD** ⚠️ **CONTAINS THE PROJECT'S ONLY `sorry`**
- **Type**: `(r' s' : ℤ) (hr : r' ≠ 0) (hrK0 : (r':K) = 0) (hsK : (s':K) ≠ 0) : PencilScalingComapDataCard W p r r' s'`
- **What**: the `p∣r'` separable comap bundle — the off-domain case `(r':K)=0` for which the canonical construction is unavailable.
- **How**: `:= by sorry` (line **2285**).
- **The `sorry` (L2285)**: the irreducible obstruction is the infinity order-transport / exact `∞`-orders `−2`, `−3` for the *inseparable* `[r']` summand. The 40-line docstring (L2237–2281) records the verified analysis (asymmetric summand pole orders ⟹ unique strictly-dominant term ⟹ `ord_∞ = −2` exactly) and that closing it needs the inseparable division-polynomial pole computation.
- **Used by**: `pencilScalingComapDataCard_sep` (2301) — DEAD
- **Visibility**: public — **Lines**: 2282–2285
- **Notes**: **DEAD with respect to the axiom-clean main theorem.** The bound consumes `pencilScaling_holds_coprime` → `_canonical`, which never invokes `_sep`/`_pDvdR`. This `sorry` could be deleted (with `_sep`, `_rZero`, `pencilScaling_holds`) without touching the proven bound.

### `noncomputable def pencilScalingComapDataCard_sep` — **DEAD**
- **Type**: `(r' s' : ℤ) (hsK : (s':K) ≠ 0) : PencilScalingComapDataCard W p r r' s'`
- **What**: the bundle for ANY separable `(r',s')` (`p∤s'`), case-splitting `r'=0` / `(r':K)=0` / canonical.
- **How**: `by_cases hr0`/`hrK`; dispatch to `_rZero` / `_pDvdR` (the `sorry`) / `_canonical`.
- **Uses from project**: `pencilScalingComapDataCard_rZero`, `pencilScalingComapDataCard_pDvdR`, `pencilScalingComapDataCard_canonical` (this file)
- **Used by**: `pencilScaling_holds` (2342) — DEAD
- **Visibility**: public — **Lines**: 2290–2303
- **Notes**: The `p∤s'`-only bundle (broader than coprime). Transitively `sorry`-tainted via `_pDvdR`. Superseded by the direct use of `_canonical` in `pencilScaling_holds_coprime`.

### `noncomputable def pencilJunkPullback` — **LIVE**
- **Type**: `ℤ → ℤ → (K(E_{K̄}) →ₐ K(E_{K̄}))`
- **What**: a total junk pullback (`fun _ _ => AlgHom.id`), used only to *state* the pullback-independent `pencilKerCard` exponent.
- **How**: `fun _ _ => AlgHom.id …`.
- **Uses from project**: none (mathlib `AlgHom.id`)
- **Used by**: `pencilScaling_holds` (2332, DEAD), `pencilScaling_holds_coprime` (2362, LIVE), `HasseBound.lean` (L73/75)
- **Visibility**: public — **Lines**: 2307–2310

### `theorem pencilKerCard_pullback_indep` — **LIVE**
- **What**: `#ker(rπ−s)_{K̄}` is independent of the chosen base-changed pullback (the kernel is read off `toAddMonoidHom = r'·π̄ − s'·id`).
- **How**: `rw [pencilIsogBaseChange_toAddMonoidHom, pencilIsogBaseChange_toAddMonoidHom]`.
- **Uses from project**: `pencilIsogBaseChange_toAddMonoidHom` (PencilDualDivisor)
- **Used by**: `pencilScaling_holds` (2347, DEAD), `pencilScaling_holds_coprime` (2383, LIVE)
- **Visibility**: public — **Lines**: 2314–2319
- **Notes**: Bridges the junk-pullback exponent to the canonical-bundle kernel.

### `theorem pencilScaling_holds` — **DEAD** (superseded)
- **What**: leaf 3 of `FrobBaseChangeScalings` (the `p∤s'`-only form), `e_ℓ(…)` scaling with the `pencilKerCard` exponent for every separable `(r',s')`.
- **How**: `intro`; derive `(s':K)≠0` from `p∤s'`; `pencilScaling_one_of_comapData_card` fed `pencilScalingComapDataCard_sep`; rewrite the `pencilKerCard.toNat` to the bundle kernel via `pencilKerCard_pullback_indep`.
- **Uses from project**: `pencilScaling_one_of_comapData_card` (PencilComapScaling), `pencilScalingComapDataCard_sep` (this file, **`sorry`-tainted**), `pencilKerCard`, `pencilKerCard_pullback_indep`
- **Used by**: NONE in the project
- **Visibility**: public — **Lines**: 2330–2348
- **Notes**: **Superseded by `pencilScaling_holds_coprime`.** Carries `sorryAx` (via `_sep` → `_pDvdR`). The `PencilScaling` (vs `PencilScalingCoprime`) it produces feeds the dead `FrobBaseChangeScalings`/`hasse_bound_unconditional_of_baseChange_scalings` (the non-coprime capstone, also not on the proven path).

### `theorem pencilScaling_holds_coprime` — **LIVE** (the leaf-3 root)
- **What**: leaf 3 of `FrobBaseChangeScalingsCoprime` — the **axiom-clean** Weil-pairing scaling `e_ℓ((r·π̄−s·id)S, (r·π̄−s·id)T) = e_ℓ(S,T)^{#ker(rπ−s)_{K̄}}` on `E_{K̄}[ℓ]`, requested only on the genuine locus `p∤r' ∧ p∤s'`.
- **How**: `intro r' s' hpr hps ℓ …`; derive `(r':K),(s':K) ≠ 0`, `r',s' ≠ 0`; `pencilScaling_one_of_comapData_card` fed `pencilScalingComapDataCard_canonical` (NO `p∣r'` input); rewrite the `pencilKerCard.toNat` via `pencilKerCard_pullback_indep`.
- **Hypotheses (as `PencilScalingCoprime`)**: `¬ p∣r'`, `¬ p∣s'`, prime `ℓ`, `ℓ≠p`, `(ℓ:K̄)≠0`.
- **Uses from project**: `pencilScaling_one_of_comapData_card` (PencilComapScaling), `pencilScalingComapDataCard_canonical`, `pencilJunkPullback`, `pencilKerCard`, `pencilKerCard_pullback_indep` (this file), `CharP.intCast_eq_zero_iff`
- **Used by**: `HasseBound.lean` (L85 — the axiom-clean capstone)
- **Visibility**: public — **Lines**: 2360–2384
- **Notes**: **The sole live exported scaling.** By restricting to `p∤r'` it routes through `_canonical` and drops the inseparable `p∣r'` gap (`_pDvdR`'s `sorry`) entirely.

### `noncomputable local instance instDecEqACPCW : DecidableEq (AlgebraicClosure K)` — **LIVE**
- **What / How**: `Classical.decEq _`.
- **Used by**: everything in the `BaseChange` section mentioning `K̄`.
- **Visibility**: local — **Lines**: 163

---

## File Summary

- **Live declarations** (on the `pencilScaling_holds_coprime` path): `pencilScaling_holds_coprime`, `pencilScalingComapDataCard_canonical`, `pencilJunkPullback`, `pencilKerCard_pullback_indep`, `comapPointValuationWitness_pencil`, `pencilIsogBaseChange_finiteKer`, `comap_pointValuation_pencil_eq_affine`, `comap_pointValuation_pencil_eq_infty`, `inftyOrdTransport_pencil`, `pencil_hcov_kernel`, `pencil_two_residues`, `isog_resid_at_affine_of_hgcomm_hinfty`, `ord_P_isog_pullback_eq_ordAtInfty_translate`, `ordAtInfty_translate_eq_ord_P_some`, `alpha_star_u_ord_eq_zero_of_residues`, `alpha_star_polyX_ord_eq_zero_of_residues`, `omegaPullbackCoeff_pencil(_mem_range/_ne_zero)`, `ordAtInfty_pencil_pullback_x/y_gen`, `pencilBaseChangePullback_x/y_gen`, `ordAtInfty_genuineIsogSmulSub_pullback_x/y_gen`, `genuineIsogSmulSub_pullback_x/y_gen`, `instDecEqACPCW`. **(≈26 live.)**
- **Dead/superseded declarations** (≈51): the **rFrobBaseChange addition-formula apparatus** L475–956 (division-poly transports + `rFrobBaseChange` + addition naturalities + decompositions + the two summand residues), the **secant/doubling residue branches** (`pencil_two_residues_secant`, `_doubling`, `_nonsecant`, `_summand_infty`, `addSlopePair_resid_tangent_of_DωLeft_zero`), the **comap→residue bridges** (`resid_x/y_gen_of_comap`, `mulByInt_neg_resid_xy`), the **Route-C `∞`-order keystone** (`ordAtInfty_isog_pullback_x_y_of_comap_at_point`, `ord_P_isog_pullback_eq_of_comap`, `ord_P_translate_neg_eq_ordAtInfty`), and the **off-domain `_sep` chain** (`pencilIsogBaseChange_rZero_eq_mulByInt`, `mapTranslateGenericPoint_mulByInt_canonical`, `pencilScalingComapDataCard_rZero`, `pencilScalingComapDataCard_pDvdR`, `pencilScalingComapDataCard_sep`, `pencilScaling_holds`).
- **The `sorry`**: line **2285**, in the DEAD `pencilScalingComapDataCard_pDvdR`. Off the axiom-clean bound path.
- **Hand-rolled constructions**: `rFrobBaseChange` (a bespoke `mkBaseChange` isogeny, dead); `pencilJunkPullback` (a junk `AlgHom.id`, live, used only to state a pullback-independent exponent). The transport-to-`O` lemmas (`ord_P_isog_pullback_eq_ordAtInfty_translate`, `isog_resid_at_affine_of_hgcomm_hinfty`) are hand-built but general and live.
- **Duplication**: massive — the dead secant/doubling residue route (L349–1606) and the dead `_sep` bundle (L2160–2348) are an entire parallel implementation of the affine comap and the per-pair bundle that the live transport-to-`O` route (`pencil_two_residues`) and the live `_canonical` bundle replace. `pencil_two_residues_summand_infty` is a near-duplicate of `pencil_two_residues` (both wrap `isog_resid_at_affine_of_hgcomm_hinfty`). The `coprime` vs `_sep`/`_pDvdR` split is the headline coprime-vs-non-coprime duplication.
- **Under-general statements**: `pencil_two_residues` (and `isog_resid_at_affine_of_hgcomm_hinfty`'s pencil wrappers) are stated for the specific pencil but the proof is isogeny-agnostic — the live content is already general in `isog_resid_at_affine_of_hgcomm_hinfty`. `alpha_star_u/polyX_ord_eq_zero_of_residues` are already general (`α`-agnostic) and could move to a shared file.
- **Cleanup recommendation**: delete the entire dead secant/doubling/rFrobBaseChange apparatus (L349–1606, ~1260 lines) and the off-domain `_sep`/`_pDvdR`/`_rZero` chain + `pencilScaling_holds` (L2160–2348, incl. the only `sorry`). This would shrink the file from 2388 to ≈650 lines and remove the project's last `sorry` from the source tree. Keep `alpha_star_*` (move to a shared residue file), the transport-to-`O` lemmas, the infinity/omega leaves, and the `_canonical`/`pencilScaling_holds_coprime` live spine.
- **`set_option`**: file-level lint suppressions (unusedSectionVars, unusedDecidableInType, unusedFintypeInType, style.longLine); one `set_option maxHeartbeats 8000000 in` at L1205 (on the DEAD `addSlopePair_resid_tangent_of_DωLeft_zero`).
