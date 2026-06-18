# Inventory: ./HasseWeil/Pic0/RouteCGeometric.lean

**File overview**: 869 lines, 14 theorems, 0 defs, 0 instances. No `sorry`, no `set_option maxHeartbeats`.
Ships the geometric half of Route C for the Hasse bound: "zsmul-injectivity over E(F̄)" (TARGET 1) and
a family of `deg(rπ − s) = N` assembly theorems at successively reduced residual lists (v1 through
hpicval_discharged), together with three non-circular picDual seeds and two qf_nonneg corollaries.

---

## Declarations

---

### `theorem mulByInt_pointMap_injective_of_geometric`

- **Type**:
  ```
  {G : Type*} [AddCommGroup G] [Infinite G]
  (htor : ∀ k : ℤ, k ≠ 0 → Finite {P : G // k • P = 0})
  {m n : ℤ} (h : ∀ P : G, m • P = n • P) : m = n
  ```
- **What**: For an infinite additive commutative group whose every nonzero torsion subgroup is finite,
  equality of `zsmul`-maps pointwise forces equality of the integer scalars.
- **How**: Contrapositive: if `m ≠ n` set `k = m − n ≠ 0`; the map `P ↦ ⟨P, hkill P⟩` injects `G`
  into the (finite) `k`-torsion subtype, giving `Finite G` via `Finite.of_injective`, contradicting
  `Infinite G` via `not_finite`.
- **Hypotheses**: `G` infinite additive group; all nonzero torsion subgroups `{P // k • P = 0}` finite.
- **Uses from project**: none
- **Used by**: `mulByInt_pointMap_injective_of_infinite_point` (line 112)
- **Visibility**: public
- **Lines**: 71–90 (proof: 76–90, ~14 lines)
- **Notes**: Abstract, axiom-clean, self-contained. The crux of Route C.

---

### `theorem mulByInt_pointMap_injective_of_infinite_point`

- **Type**:
  ```
  {F : Type*} [Field F] [DecidableEq F]
  (E : WeierstrassCurve.Affine F) [E.IsElliptic] [Infinite E.Point]
  (htor : ∀ k : ℤ, k ≠ 0 → Finite (E[k] : AddSubgroup E.Point))
  {m n : ℤ}
  (h : ∀ P : E.Point,
    (mulByInt E m).toAddMonoidHom P = (mulByInt E n).toAddMonoidHom P) : m = n
  ```
- **What**: EC specialisation: for an elliptic curve with infinite point group and finite nonzero
  torsion subgroups, `mulByInt` point maps separate integer scalars.
- **How**: Applies `mulByInt_pointMap_injective_of_geometric` after packaging `htor` via an equivalence
  between `(E[k] : AddSubgroup)` and the subtype `{P // k • P = 0}` (using `mem_torsionSubgroup`),
  then unfolds `mulByInt_apply`.
- **Hypotheses**: Elliptic curve over a field; point group infinite; all nonzero torsion subgroups finite
  (Silverman III.4.10a).
- **Uses from project**: `mulByInt_pointMap_injective_of_geometric`, `mem_torsionSubgroup`, `mulByInt_apply`
- **Used by**: `hgeom_of_infinite_point` (line 745)
- **Visibility**: public
- **Lines**: 102–127 (proof: 109–127, ~18 lines)
- **Notes**: None.

---

### `theorem picDual_eq_of_degree_eq`

- **Type**: Given `β : Isogeny W.toAffine W.toAffine` with `CoordHom` data `ch`/`hinj`/`hfin`/`hnat`,
  surjectivity of `picDual` and `β`, scalar tower data `(S, S')` with `hSR`/`hS'FF`, an integer `d`
  with `β.degree = d`, and `δ` satisfying `δ ∘ β = [d]`, concludes `β.picDual ch hinj hfin = δ`.
- **What**: A thin wrapper re-exporting `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`
  with an explicit integer degree `d` supplied independently of the push-pull chain.
- **How**: Direct delegation to `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`.
- **Hypotheses**: Full CoordHom + naturality + surjectivity data; scalar tower data; explicit degree
  and composition-identity for candidate δ.
- **Uses from project**: `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`
- **Used by**: unused in file (seeds for external callers)
- **Visibility**: public
- **Lines**: 180–203 (proof: 201–203, 3 lines — single delegation)
- **Notes**: API adapter; effectively a re-export with a cleaner degree parameter.

---

### `theorem picDual_frobenius_eq_verschiebung`

- **Type**: For `(frobeniusIsog W)` with its CoordHom data, and `V : Isogeny` satisfying
  `IsDualOf W.toAffine V (frobeniusIsog W)`, concludes
  `(frobeniusIsog W).picDual chπ hinjπ hfinπ = V.toAddMonoidHom`.
- **What**: Non-circular seed: `picDual(π) = V` (Verschiebung) using the III.6.1(a) uniqueness
  criterion from the dual composition `V ∘ π = [deg π]` and the shipped degree `frobeniusIsog_degree`.
- **How**: Extracts `V.toAddMonoidHom.comp (frobeniusIsog W).toAddMonoidHom = [deg π]` from `IsDualOf`
  via `congrArg Isogeny.toAddMonoidHom h_isDual.1`, then delegates to
  `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_degree`.
- **Hypotheses**: CoordHom + naturality + surjectivity data for Frobenius; scalar tower data;
  `IsDualOf` dual relation.
- **Uses from project**: `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_degree`, `IsDualOf`,
  `frobeniusIsog`, `Isogeny.comp_toAddMonoidHom`
- **Used by**: unused in file (seed for external callers)
- **Visibility**: public (`omit [Fintype W.toAffine.Point]`)
- **Lines**: 211–238 (proof: 232–238, ~7 lines)
- **Notes**: Non-circular (degree obtained from `frobeniusIsog_degree`, not from the conclusion).

---

### `theorem picDual_mulByInt_eq_self`

- **Type**: For `n : ℤ` with `n ≠ 0` and CoordHom data for `mulByInt W.toAffine n`, concludes
  `(mulByInt W.toAffine n).picDual chn hinjn hfinn = (mulByInt W.toAffine n).toAddMonoidHom`.
- **What**: Non-circular seed: `picDual([n]) = [n]` (scalar self-duality, Silverman III.6.2(b)/(d))
  using `deg [n] = n²` and `[n] ∘ [n] = [n²]`.
- **How**: Uses `mulByInt_comp_eq_mul` to get `[n] ∘ [n] = [n·n]`; computes `hdeg` via
  `mulByInt_degree` and `Int.toNat_of_nonneg`; delegates to
  `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`.
- **Hypotheses**: `n ≠ 0`; CoordHom + naturality + surjectivity for `mulByInt W n`; scalar tower.
- **Uses from project**: `mulByInt_comp_eq_mul`, `mulByInt_degree`, `Isogeny.comp_toAddMonoidHom`,
  `Isogeny.picDual_eq_of_comp_toAddMonoidHom_eq_of_degree_eq`
- **Used by**: unused in file (seed for external callers)
- **Visibility**: public (`omit [Fintype K] [Fintype W.toAffine.Point]`)
- **Lines**: 245–276 (proof: 265–276, ~12 lines)
- **Notes**: Non-circular. The `Int.toNat_of_nonneg` + `ring` step handles the degree coercion.

---

### `theorem degree_eq_N_via_picDual_geometric`

- **Type**: For `W` over finite field `K`, integers `r, s ≠ 0` with `r, s ≠ 0` in `K`, Verschiebung
  `V`, dual `β_dual` with Vieta data, CoordHom data for `β = genuineIsogSmulSub W r s …`,
  naturality + picDual surjectivity, `hdual_hom` (additivity output), scalar tower data, and
  `hgeom` (pointwise geometric injectivity), concludes:
  `((genuineIsogSmulSub W r s …).degree : ℤ) = q·r² − t·r·s + s²`.
- **What**: Main Route C theorem: `deg(rπ − s) = N` assembled from push-pull + dual additivity +
  Vieta at the point-map level, collapsed to an integer equality by the geometric injectivity `hgeom`.
- **How**: Combines push-pull via `Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree` (after
  rewriting by `hdual_hom`), Vieta via `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, and equates
  the two `mulByInt` maps via `h_pushpull.symm.trans h_vieta`, then applies `hgeom` via
  `DFunLike.congr_fun`.
- **Hypotheses**: `2 ≤ #K`; `r, s ≠ 0`; `r, s ≠ 0` in K; `IsDualOf V π`; sum-trace identity;
  `h_beta_dual_hom`; full CoordHom + naturality + picDual-surjectivity for `β`; scalar tower;
  `hdual_hom` (additivity); `hgeom`.
- **Uses from project**: `Isogeny.picDual_comp_toAddMonoidHom_of_surjective_degree`,
  `genuine_dual_comp_toAddMonoidHom_eq_mulByInt`, `Isogeny.comp_toAddMonoidHom`, `genuineIsogSmulSub`,
  `frobeniusIsog`, `isogTrace`, `isogOneSub_negFrobenius`, `mulByInt`
- **Used by**: `degree_eq_N_via_picDual_geometric_v2` (line 527), `qf_nonneg_generic_via_picDual_geometric` (line 650)
- **Visibility**: public
- **Lines**: 300–366 (proof: 339–366, ~28 lines)
- **Notes**: Proof slightly under 30 lines. No sorry, no maxHeartbeats. The central Route C assembly.

---

### `theorem hpoint_of_toPointMap_compat`

- **Type**: For `α : Isogeny E E` with CoordHom `ch`, a `CurveMap φ` with CoordHom `coordHom`,
  `hcoord : coordHom.toAlgHom = ch.toAlgHom`, and `hcompat` (point-map identification at every
  rational point), proves the `hpoint` obligation: for all `x y h hcomap`,
  `toClassEquiv'(α.toAddMonoidHom(some x y h)) = Additive.ofMul (ClassGroup.mk0 ⟨comap, hcomap⟩)`.
- **What**: Bridges the `Isogeny` point map to the `CurveMap.toPointMap` via `toClass_toPointMap`,
  converting a concrete point-map identification `hcompat` into the κ-class `comap`-form equality
  needed by the naturality machinery.
- **How**: Uses `hcoord` to rewrite the `comap` nonzero condition `hne`, then applies
  `WeierstrassCurve.Affine.Point.toClassEquiv'_apply` + `HasseWeil.Curves.CurveMap.toClass_toPointMap`
  after rewriting the point via `hcompat`; closes by `congrArg` + `Subtype.ext` for ideal equality.
- **Hypotheses**: `hcoord` identifying the two algebra homs; `hcompat` giving the point-map
  identification at rational points; the `comap`-nonzero condition `hcomap` (supplied by the caller).
- **Uses from project**: `HasseWeil.Curves.CurveMap.toClass_toPointMap`,
  `WeierstrassCurve.Affine.Point.toClassEquiv'_apply`, `HasseWeil.Curves.SmoothPlaneCurve.maximalIdealAt`
- **Used by**: `degree_eq_N_via_picDual_geometric_v3` (line 601)
- **Visibility**: public
- **Lines**: 416–456 (proof: 435–456, ~22 lines)
- **Notes**: Bridges the `Isogeny`/`CurveMap` interface gap; the `hcoord` and `hcompat` pair
  is the precise residual for genuine isogenies.

---

### `theorem degree_eq_N_via_picDual_geometric_v2`

- **Type**: As `degree_eq_N_via_picDual_geometric` but replacing `hnat` with `hpoint` (base-change
  III.3.4 comap agreement) and `hdual_hom` with `hpicval` (III.6.2(c) additivity output
  `picDual(β) = rV − s·id`).
- **What**: Reduced-residual version: discharges `hnat` via `Isogeny.naturality_of_coordHom` from
  `hpoint`, and discharges `hdual_hom` from `hpicval` by composition, then delegates to `_v1`.
- **How**: `hnat` from `Isogeny.naturality_of_coordHom ch hinj hfin hpoint`;
  `hdual_hom` from `h_beta_dual_hom.trans hpicval.symm`; delegates to
  `degree_eq_N_via_picDual_geometric`.
- **Hypotheses**: Same as v1 minus `hnat`/`hdual_hom`, replaced by `hpoint` and `hpicval`.
- **Uses from project**: `Isogeny.naturality_of_coordHom`, `degree_eq_N_via_picDual_geometric`,
  `genuineIsogSmulSub`, `frobeniusIsog`, `isogTrace`, `isogOneSub_negFrobenius`
- **Used by**: `degree_eq_N_via_picDual_geometric_v3` (line 603),
  `qf_nonneg_generic_via_picDual_geometric_v2` (line 707),
  `degree_eq_N_via_picDual_geometric_hpicval_discharged` (line 866)
- **Visibility**: public
- **Lines**: 469–528 (proof: 519–528, ~10 lines)
- **Notes**: Key intermediate in the residual-reduction chain; called by 3 other declarations in this file.

---

### `theorem degree_eq_N_via_picDual_geometric_v3`

- **Type**: As v2 but replaces the opaque `hpoint` residual with `(coordHom, hcoord, hcompat)` —
  the `CurveMap` witness and point-map identification.
- **What**: Further reduction: `hpoint` is discharged from `hpoint_of_toPointMap_compat`, with the
  remaining genuine residual being the per-isogeny `toAddMonoidHom` ↔ `CurveMap.toPointMap` agreement.
- **How**: Calls `hpoint_of_toPointMap_compat` to obtain `hpoint`, then delegates to
  `degree_eq_N_via_picDual_geometric_v2`.
- **Hypotheses**: Same as v2 minus `hpoint`, replaced by `{φ, coordHom, hcoord, hcompat}`.
- **Uses from project**: `hpoint_of_toPointMap_compat`, `degree_eq_N_via_picDual_geometric_v2`,
  `genuineIsogSmulSub`, `frobeniusIsog`, `isogTrace`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 553–604 (proof: 599–604, ~6 lines)
- **Notes**: Orthogonal reduction to `_hpicval_discharged`; these two compose fully.

---

### `theorem qf_nonneg_generic_via_picDual_geometric`

- **Type**: Same hypotheses as `degree_eq_N_via_picDual_geometric`; concludes
  `0 ≤ q·r² − t·r·s + s²`.
- **What**: Route C `qf_nonneg` corollary: combines `degree_eq_N_via_picDual_geometric` with
  `Int.natCast_nonneg` to get non-negativity of the degree `N`.
- **How**: `rw [← degree_eq_N_via_picDual_geometric ...]` reduces to `0 ≤ (isogeny.degree : ℤ)`,
  closed by `Int.natCast_nonneg`.
- **Hypotheses**: Identical to `degree_eq_N_via_picDual_geometric`.
- **Uses from project**: `degree_eq_N_via_picDual_geometric`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 614–652 (proof: 648–652, ~5 lines)
- **Notes**: The Leaf-1 conclusion in Route C for `qf_nonneg`.

---

### `theorem qf_nonneg_generic_via_picDual_geometric_v2`

- **Type**: Same hypotheses as `degree_eq_N_via_picDual_geometric_v2`; concludes
  `0 ≤ q·r² − t·r·s + s²`.
- **What**: Route C v2 `qf_nonneg` corollary using the reduced-residual `_v2` assembly.
- **How**: `rw [← degree_eq_N_via_picDual_geometric_v2 ...]` + `Int.natCast_nonneg`.
- **Hypotheses**: Identical to `degree_eq_N_via_picDual_geometric_v2`.
- **Uses from project**: `degree_eq_N_via_picDual_geometric_v2`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 661–709 (proof: 706–709, ~4 lines)
- **Notes**: The v2 Leaf-1 conclusion; shorter residual list than v1.

---

### `theorem hgeom_of_infinite_point`

- **Type**: Under `[Infinite W.toAffine.Point]` and `htor : ∀ k ≠ 0, Finite (torsionSubgroup W k)`,
  proves the `hgeom` shape needed by `degree_eq_N_via_picDual_geometric`.
- **What**: Shows the geometric-injectivity hypothesis `hgeom` is supplied by TARGET 1 when the
  point group is infinite and torsion is finite — confirming the Route C residual is exactly the
  base-change geometric injectivity.
- **How**: Single-line term: `fun {m n} h => mulByInt_pointMap_injective_of_infinite_point W.toAffine htor h`.
- **Hypotheses**: `[Infinite W.toAffine.Point]`; finite nonzero torsion subgroups.
- **Uses from project**: `mulByInt_pointMap_injective_of_infinite_point`, `HasseWeil.torsionSubgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 737–745 (term proof, 1 line)
- **Notes**: Connector closing the "Phase 3" loop.

---

### `theorem picDual_smulSub_eq_rV_sub_s`

- **Type**: For `genuineIsogSmulSub W r s …` with CoordHom data, the sum-trace identity, and
  the III.8 trace relation `htrace_dual : β + picDual(β) = [r·t − 2s]`, concludes
  `picDual(β) = r·V − s·id`.
- **What**: Discharges `hpicval` from the single irreducible Silverman III.8 trace relation for the
  whole `rπ − s`, non-circularly, via `Isogeny.picDual_eq_smul_sub_of_sum_trace`.
- **How**: First proves `hbeta : β.toAddMonoidHom = r•(frobeniusIsog).toAddMonoidHom − s•id` by
  rewriting via `genuineIsogSmulSub_toAddMonoidHom` and `simp`/`rw [neg_smul, sub_eq_add_neg]`;
  then applies `Isogeny.picDual_eq_smul_sub_of_sum_trace`.
- **Hypotheses**: CoordHom + injectivity + finiteness for `genuineIsogSmulSub`; sum-trace identity
  for `π + V`; III.8 trace `htrace_dual` for `β`.
- **Uses from project**: `genuineIsogSmulSub_toAddMonoidHom`, `Isogeny.picDual_eq_smul_sub_of_sum_trace`,
  `frobeniusIsog`, `isogTrace`, `isogOneSub_negFrobenius`, `Isogeny.zsmul_apply`, `mulByInt_apply`
- **Used by**: `degree_eq_N_via_picDual_geometric_hpicval_discharged` (line 865)
- **Visibility**: public
- **Lines**: 770–799 (proof: 789–799, ~11 lines)
- **Notes**: The `simp`/`rw` rewrites `neg_smul` and `sub_eq_add_neg` for the functional form.

---

### `theorem degree_eq_N_via_picDual_geometric_hpicval_discharged`

- **Type**: As v2 but replaces `hpicval` with `htrace_dual` (the III.8/III.6.2(c) trace relation
  for the whole `β = rπ − s`). Concludes `(β.degree : ℤ) = q·r² − t·r·s + s²`.
- **What**: Further reduction of v2: `hpicval` discharged from `picDual_smulSub_eq_rV_sub_s`, leaving
  `htrace_dual` as the single irreducible dual-additivity residual.
- **How**: Applies `picDual_smulSub_eq_rV_sub_s` to obtain `hpicval`, then delegates to
  `degree_eq_N_via_picDual_geometric_v2`.
- **Hypotheses**: Same as v2 minus `hpicval`, replaced by `htrace_dual`.
- **Uses from project**: `picDual_smulSub_eq_rV_sub_s`, `degree_eq_N_via_picDual_geometric_v2`,
  `genuineIsogSmulSub`, `frobeniusIsog`, `isogTrace`, `isogOneSub_negFrobenius`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 811–867 (proof: 861–867, ~7 lines)
- **Notes**: Orthogonal to v3 (which discharges `hpoint` instead); the two reductions compose.

---

## Summary table

| Declaration | Lines | Proof lines | Sorry | Callers in file |
|---|---|---|---|---|
| `mulByInt_pointMap_injective_of_geometric` | 71–90 | 14 | no | 1 |
| `mulByInt_pointMap_injective_of_infinite_point` | 102–127 | 18 | no | 1 |
| `picDual_eq_of_degree_eq` | 180–203 | 3 | no | 0 |
| `picDual_frobenius_eq_verschiebung` | 211–238 | 7 | no | 0 |
| `picDual_mulByInt_eq_self` | 245–276 | 12 | no | 0 |
| `degree_eq_N_via_picDual_geometric` | 300–366 | 28 | no | 2 |
| `hpoint_of_toPointMap_compat` | 416–456 | 22 | no | 1 |
| `degree_eq_N_via_picDual_geometric_v2` | 469–528 | 10 | no | 3 |
| `degree_eq_N_via_picDual_geometric_v3` | 553–604 | 6 | no | 0 |
| `qf_nonneg_generic_via_picDual_geometric` | 614–652 | 5 | no | 0 |
| `qf_nonneg_generic_via_picDual_geometric_v2` | 661–709 | 4 | no | 0 |
| `hgeom_of_infinite_point` | 737–745 | 1 | no | 0 |
| `picDual_smulSub_eq_rV_sub_s` | 770–799 | 11 | no | 1 |
| `degree_eq_N_via_picDual_geometric_hpicval_discharged` | 811–867 | 7 | no | 0 |
