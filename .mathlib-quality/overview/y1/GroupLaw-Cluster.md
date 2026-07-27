# /overview Phase-1 inventory — GroupLaw cluster (Y1)

Date: 2026-07-12. Branch: `main` (aintlib-main worktree). Scope: 7 files under
`projects/ModularCurves/ModularCurves/EllipticCurve/`:

| # | File | Lines |
|---|------|-------|
| 1 | GroupLaw.lean | 410 |
| 2 | GroupLawAxioms.lean | 1344 |
| 3 | MulByHomFlat.lean | 50 |
| 4 | MulByHomSmooth.lean | 234 |
| 5 | MulByHomEtale.lean | 90 |
| 6 | NegModelBaseChange.lean | 103 |
| 7 | TorsionUnramifiedFibre.lean | 1462 |

Cluster-internal import edges: `MulByHomFlat → GroupLaw`; `GroupLawAxioms → NegModelBaseChange`
(+ `AdditionSpecPoints`); `MulByHomSmooth → KernelDivisibilityGlue → {KernelDivisibilityChart,
MulByHomFlat}`; `MulByHomEtale → {MulByHomUnramified → TorsionUnramifiedFibre, MulByHomQuasiFinite,
MulByHomSmooth}`. `NegModelBaseChange → GroupLawConstruction`.

Field legend per declaration: **Type / What / How / Hypotheses / Uses(project) / UsedBy(cluster) /
Vis / Lines / Notes**. "UsedBy(cluster)" = by-name references inside the 7 files above only.
CODE-sorry = a literal `sorry` term in the declaration body.

---

## 1. GroupLaw.lean (410 lines)

Module: the **working record** `EllipticCurve S` = geometric record + group-object structure
(design per expert review 2026-07-05, KM 1.4.1). Imports: `EllipticCurve.Basic`,
mathlib `Monoidal.Cartesian.{Grp,Over}`, `ForMathlib.FunctorMapZpow`, `ForMathlib.OverPullbackMul`,
mathlib `AlgebraicGeometry.Group.Smooth`. Namespace `ModularCurves.EllipticCurve` (record at
`ModularCurves`). Local instances: `Over.cartesianMonoidalCategory`, `Over.braidedCategory`.

### `EllipticCurve` (structure)
- **Type**: structure (extends `EllipticCurveGeom S`, Basic.lean:445)
- **What**: elliptic curve over `S` with commutative group-scheme structure; fields `grp : GrpObj (Over.mk π)`, `comm : IsCommMonObj (Over.mk π)`, `one_eq_zero : (η[Over.mk π]).left = (𝟙_ (Over S)).hom ≫ zero` (unit = zero section).
- **How**: data record; no proof.
- **Hypotheses**: `S : Scheme.{u}`.
- **Uses(project)**: `EllipticCurveGeom` (Basic.lean).
- **UsedBy(cluster)**: every file except NegModelBaseChange/GroupLawAxioms (those work at the Weierstrass-model level); the `E : EllipticCurve S` variable of MulByHomFlat/Smooth/Etale/TorsionUnramifiedFibre.
- **Vis**: public. **Lines**: 52–60 (9).
- **Notes**: mathematically-redundant data; canonicity deferred to `abelEnrichment_*` (both sorried).

### `asOver`
- **Type**: noncomputable abbrev
- **What**: `E/S` as `Over.mk E.π : Over S`.
- **How**: `Over.mk`.
- **Hypotheses**: `E : EllipticCurve S`.
- **Uses(project)**: —.
- **UsedBy(cluster)**: in-file (16 refs); TorsionUnramifiedFibre (`μ[F.asOver]`, `E.asOver.hom` legs).
- **Vis**: public. **Lines**: 67 (1).

### `grpObj` / `isCommMonObj` (instances)
- **Type**: noncomputable instance / instance
- **What**: register `E.grp` as `GrpObj E.asOver` and `E.comm` as `IsCommMonObj E.asOver` for TC.
- **How**: field projections.
- **Hypotheses**: `E`.
- **Uses(project)**: the record fields.
- **UsedBy(cluster)**: TC-resolution everywhere `Hom.group`/`Hom.commGroup`/`μ[E.asOver]` appears (in-file, TorsionUnramifiedFibre, MulByHomSmooth via `Point` group).
- **Vis**: public. **Lines**: 69 (1) / 71 (1).

### `abelEnrichment_exists` **(CODE-sorry)**
- **Type**: theorem (T-A6b)
- **What**: every `G : EllipticCurveGeom S` admits an enrichment `E : EllipticCurve S` with `E.toEllipticCurveGeom = G` (Abel/KM 2.1.2).
- **How**: `by sorry` — the deferred purity/comparison project (named black boxes fixed in header: coherent-base-change, relative-duality-genus-one, relative-Picard, Poincare, Abel-isomorphism, group-law-from-Abel).
- **Hypotheses**: `G : EllipticCurveGeom S`.
- **Uses(project)**: statement only: `EllipticCurveGeom`, the record.
- **UsedBy(cluster)**: none (consumers outside cluster: ModelRecord, ModelGroupUniq, GroupLawDescent, Rigidity, YOneAssembly).
- **Vis**: public. **Lines**: 75–76 (2).
- **Notes**: **CODE-sorry carrier #1** (GroupLaw.lean:76). ⧗KM-gate on KM 2.1–2.3.

### `abelEnrichment_unique` **(CODE-sorry)**
- **Type**: theorem (T-A6c)
- **What**: two working records with equal geometry are equal (`E = E'`).
- **How**: `by sorry` — same deferred project (rigidity route).
- **Hypotheses**: `E E' : EllipticCurve S`, `h : E.toEllipticCurveGeom = E'.toEllipticCurveGeom`.
- **Uses(project)**: record only.
- **UsedBy(cluster)**: none (same outside consumers as above).
- **Vis**: public. **Lines**: 80–81 (2).
- **Notes**: **CODE-sorry carrier #2** (GroupLaw.lean:81).

### `mulBy`
- **Type**: noncomputable def
- **What**: `[n] : E.asOver ⟶ E.asOver`, the `n`-th zpower of `𝟙` in `Hom.group` (KM 2.3).
- **How**: `letI := Hom.group; (𝟙 E.asOver) ^ n`.
- **Hypotheses**: `n : ℤ`.
- **Uses(project)**: `grpObj` (for `Hom.group`).
- **UsedBy(cluster)**: in-file (`mulByHom`, `mulBy_baseChange`); MulByHomSmooth/Etale via `mulByHom`.
- **Vis**: public. **Lines**: 86–88 (3).

### `mulByHom`
- **Type**: noncomputable abbrev
- **What**: underlying scheme morphism `(E.mulBy n).left : E.E ⟶ E.E`.
- **How**: `.left`.
- **Hypotheses**: `n : ℤ`.
- **Uses(project)**: `mulBy`.
- **UsedBy(cluster)**: MulByHomSmooth (all three theorems), MulByHomEtale (`mulBy_etale'`, `mulByHom_formallyUnramified''`), in-file base-change lemmas.
- **Vis**: public. **Lines**: 91 (1).

### `mulByHom_π`
- **Type**: theorem, `@[simp]`
- **What**: `[n] ≫ π = π`.
- **How**: `Over.w (E.mulBy n)`.
- **Hypotheses**: `n : ℤ`.
- **Uses(project)**: `mulBy`.
- **UsedBy(cluster)**: MulByHomSmooth (`formallySmooth_mulByHom_appLE` chart triangle, `mulByHom_smooth_of_nIsInvertible` chart selection); no by-name in-file use (simp export).
- **Vis**: public. **Lines**: 93–95 (3).

### `Point`
- **Type**: abbrev (Type)
- **What**: `T`-points of `E/S` along `g : T ⟶ S`: `{h : T ⟶ E.E // h ≫ E.π = g}` (Loeffler §3.3).
- **How**: subtype.
- **Hypotheses**: `g : T ⟶ S`.
- **Uses(project)**: —.
- **UsedBy(cluster)**: MulByHomFlat (`KernelNDivisible`), MulByHomSmooth, TorsionUnramifiedFibre (pervasive).
- **Vis**: public. **Lines**: 99–100 (2).

### `zeroPoint`
- **Type**: def
- **What**: the zero `T`-point `⟨g ≫ E.zero, _⟩`.
- **How**: `zero_π` rewriting.
- **Hypotheses**: `g`.
- **Uses(project)**: geometric record fields.
- **UsedBy(cluster)**: **none** (in-file count 1 = declaration only; outside cluster: YOneAtlasClassify `zeroPoint_eq_zero`, WeilPairing).
- **Vis**: public. **Lines**: 103–104 (2).
- **Notes**: the group-`0` used everywhere else comes from `pointAddCommGroup`; `point_zero_val` (TorsionFibre.lean:254) is the bridge.

### `pointEquivOverHom`
- **Type**: noncomputable def (Equiv)
- **What**: `E.Point g ≃ (Over.mk g ⟶ E.asOver)`.
- **How**: `Over.homMk` / `.left`; inverses by `rfl`/`ext`.
- **Hypotheses**: `g`.
- **Uses(project)**: —.
- **UsedBy(cluster)**: in-file (`pointAddCommGroup`, smul spec, base-change add), TorsionUnramifiedFibre (`pointEquivOverHom_sub/_restrict`, pairing lemmas).
- **Vis**: public. **Lines**: 107–112 (6).

### `pointAddCommGroup`
- **Type**: noncomputable instance
- **What**: `AddCommGroup (E.Point g)`, transported from `Hom.commGroup` through `pointEquivOverHom ∘ Additive.ofMul`.
- **How**: `Equiv.addCommGroup` transport.
- **Hypotheses**: `g`.
- **Uses(project)**: `pointEquivOverHom`, `isCommMonObj` (for `Hom.commGroup`).
- **UsedBy(cluster)**: MulByHomFlat (the `•`/`0` in `KernelNDivisible`), MulByHomSmooth (point arithmetic of the (LIFT) argument), TorsionUnramifiedFibre (everything).
- **Vis**: public. **Lines**: 117–120 (4).

### `pointEquivOverHom_add`
- **Type**: theorem
- **What**: the transport spec — `equiv (P+Q) = equiv P * equiv Q` in `Hom.commGroup`.
- **How**: `rfl`.
- **Hypotheses**: `P Q : E.Point g`.
- **Uses(project)**: the two above.
- **UsedBy(cluster)**: in-file (`pointBaseChangeFun_add` ×2); TorsionUnramifiedFibre (`point_add_val_mu`).
- **Vis**: public. **Lines**: 124–127 (4).

### `point_smul_eq_comp_mulBy`
- **Type**: theorem (T-A6d, specification)
- **What**: `(n • P).1 = P.1 ≫ E.mulByHom n` — point-level and morphism-level `[n]` agree.
- **How**: `GrpObj.comp_zpow` + `congrArg CommaMorphism.left`; named lemma: **`GrpObj.comp_zpow`**.
- **Hypotheses**: `n : ℤ`, `P : E.Point g`.
- **Uses(project)**: `pointEquivOverHom`, `mulBy(_Hom)`.
- **UsedBy(cluster)**: in-file (`Point.asSection_zsmul` ×4), MulByHomSmooth (×3 in the (LIFT) argument).
- **Vis**: public. **Lines**: 132–141 (10).

### `Point.restrict`
- **Type**: def
- **What**: functorial restriction of a point along `k : T' ⟶ T` (precompose).
- **How**: associativity rewrite.
- **Hypotheses**: `k`, `P : E.Point g`.
- **Uses(project)**: —.
- **UsedBy(cluster)**: MulByHomFlat (`KernelNDivisible`), MulByHomSmooth (defect reduction), TorsionUnramifiedFibre (`restrict_*` API + core theorems). No other in-file use.
- **Vis**: public. **Lines**: 144–146 (3).

### `baseChange`
- **Type**: noncomputable def (T-A5)
- **What**: the working record base-changed along `g : T ⟶ S`: total space `pullback E.π g`, group structure `Over.grpObjMkPullbackSnd`, commutativity + `one_eq_zero` re-proved.
- **How**: geometry Props by `MorphismProperty.pullback_snd` + **`smoothOfRelativeDimension_isStableUnderBaseChange`**; `localModel.baseChange`; group by **`Over.grpObjMkPullbackSnd`** / **`Over.isCommMonObj_mk_pullbackSnd`** (ForMathlib/OverPullbackMul); `one_eq_zero` by `pullback.hom_ext` + `Over.grpObjMkPullbackSnd_one` + a `Functor.LaxMonoidal.ε`-calc (both legs).
- **Hypotheses**: `g : T ⟶ S`.
- **Uses(project)**: `EllipticCurveGeom.localModel.baseChange` (Basic), ForMathlib/OverPullbackMul.
- **UsedBy(cluster)**: in-file (all `mulByHom_baseChange*`, `asSection`, `baseChangeEquiv`); MulByHomEtale + TorsionUnramifiedFibre (`E.baseChange (S.fromSpecResidueField y)`).
- **Vis**: public. **Lines**: 152–198 (47). **Proof >30 lines.**
- **Notes**: semireducible `def` — the source of the kabstract/transparency wall documented at `Point.asSection_zsmul`.

### `mulBy_baseChange`
- **Type**: theorem (T-D6a-ii)
- **What**: `(E.baseChange g).mulBy n = (Over.pullback g).map (E.mulBy n)`.
- **How**: **`Functor.map_zpow'`** (ForMathlib/FunctorMapZpow) + `Functor.map_id` + `rfl`.
- **Hypotheses**: `g`, `n`.
- **Uses(project)**: ForMathlib/FunctorMapZpow, `baseChange`.
- **UsedBy(cluster)**: in-file (`mulByHom_baseChange`).
- **Vis**: public. **Lines**: 209–213 (5).

### `mulByHom_baseChange`
- **Type**: theorem
- **What**: `.left` of the above in explicit `pullback.lift` form.
- **How**: `congrArg CommaMorphism.left` of `mulBy_baseChange`.
- **Hypotheses**: `g`, `n`.
- **Uses(project)**: `mulBy_baseChange`.
- **UsedBy(cluster)**: in-file (`_fst`, `_snd`).
- **Vis**: public. **Lines**: 217–222 (6).

### `mulByHom_baseChange_fst` / `mulByHom_baseChange_snd`
- **Type**: lemmas, `@[reassoc (attr := simp)]`
- **What**: the two projection identities of the base-changed `[n]`.
- **How**: `mulByHom_baseChange` + `pullback.lift_fst/snd`.
- **Hypotheses**: `g`, `n`.
- **Uses(project)**: `mulByHom_baseChange`.
- **UsedBy(cluster)**: in-file (`Point.asSection_zsmul`).
- **Vis**: public. **Lines**: 224–228 (5) / 230–233 (4).

### `Point.asSection`
- **Type**: noncomputable def
- **What**: a point of `E` over `g` as a section (`Point (𝟙 T)`) of `E.baseChange g`.
- **How**: `pullback.lift P.1 (𝟙 T)`.
- **Hypotheses**: `g`, `P`.
- **Uses(project)**: `baseChange`.
- **UsedBy(cluster)**: in-file (`asSection_*`); outside cluster: YOneTatePoint, YOneAssembly, YFullRoute, Moduli.
- **Vis**: public. **Lines**: 237–240 (4).

### `Point.asSection_coe`
- **Type**: lemma, `@[simp]`
- **What**: unfolds `asSection`'s value.
- **How**: `rfl`.
- **UsedBy(cluster)**: none in-file (simp export; count 1).
- **Vis**: public. **Lines**: 242–245 (4).

### `Point.asSection_val_fst` / `Point.asSection_val_snd`
- **Type**: lemmas, `@[reassoc (attr := simp)]`
- **What**: projections of the section (`= P.1` / `= 𝟙 T`).
- **How**: `pullback.lift_fst/snd`.
- **UsedBy(cluster)**: in-file (`asSection_zsmul` ×4).
- **Vis**: public. **Lines**: 247–250 (4) / 252–255 (4).

### `Point.asSection_zsmul`
- **Type**: theorem (T-D6a-ii final ingredient)
- **What**: `asSection (n • P) = n • asSection P` — the section dictionary is `ℤ`-equivariant.
- **How**: deliberately **term-mode** (`Eq.trans`/`congrArg`/`Category.assoc` chains): `Subtype.ext (pullback.hom_ext _ _)`, both legs via **`point_smul_eq_comp_mulBy`** (on `E` and on `E.baseChange g`) + `mulByHom_baseChange_fst/snd` + `asSection_val_fst/snd`.
- **Hypotheses**: `g`, `n`, `P`.
- **Uses(project)**: the five lemmas just named.
- **UsedBy(cluster)**: none in-file; outside: Tate-point/Assembly layer.
- **Vis**: public. **Lines**: 268–300 (33). **Proof >30 lines.**
- **Notes**: header documents the semireducible-`baseChange` kabstract wall and the term-mode-as-probe doctrine (PROVEN 2026-07-07, axiom-clean).

### `pointBaseChangeFun`
- **Type**: private noncomputable def
- **What**: forward map of the base-change point dictionary: `x ↦ ⟨x.1 ≫ pullback.fst, _⟩ : E.Point (t ≫ σ)`.
- **How**: term-mode `pullback.condition` chain.
- **Hypotheses**: `σ : T ⟶ S`, `t : T' ⟶ T`.
- **Uses(project)**: `baseChange`.
- **UsedBy(cluster)**: in-file (`pointBaseChangeFun_add`, `baseChangeEquiv`).
- **Vis**: **private**. **Lines**: 303–309 (7).

### `pointBaseChangeFun_add`
- **Type**: private lemma
- **What**: additivity of the forward map.
- **How**: all term-mode; both sums written via **`pointEquivOverHom_add`** as `lift … ≫ μ.left`; comparison lift matched by **`Over.tensorObj_ext`** (ForMathlib/OverPullbackMul) and closed by **`Over.grpObjMkPullbackSnd_mul_left_fst`** (the projection intertwines the pullback multiplication).
- **Hypotheses**: `σ`, `t`, `x y : (E.baseChange σ).Point t`.
- **Uses(project)**: `pointEquivOverHom_add`, ForMathlib/OverPullbackMul (`tensorObj_ext`, `grpObjMkPullbackSnd_mul_left_fst`).
- **UsedBy(cluster)**: in-file (`baseChangeEquiv.map_add'`).
- **Vis**: **private**. **Lines**: 311–385 (75). **Proof >30 lines.**

### `Point.baseChangeEquiv`
- **Type**: noncomputable def (`≃+`) (T-H2b)
- **What**: additive base-change dictionary `(E.baseChange σ).Point t ≃+ E.Point (t ≫ σ)`.
- **How**: forward = `pointBaseChangeFun`; inverse = `pullback.lift y.1 t`; inverses by `pullback.hom_ext`/`lift_fst`; additivity = `pointBaseChangeFun_add`.
- **Hypotheses**: `σ`, `t`.
- **Uses(project)**: the two privates.
- **UsedBy(cluster)**: none in-file beyond `_apply_coe`; outside: MulByHomQuasiFinite, ModelRecord, KernelDivisibilityGlue (the BB-QF transport pattern).
- **Vis**: public. **Lines**: 392–401 (10).

### `Point.baseChangeEquiv_apply_coe`
- **Type**: lemma, `@[simp]`
- **What**: value of the forward map.
- **How**: `rfl`.
- **UsedBy(cluster)**: none in-file (simp export).
- **Vis**: public. **Lines**: 403–406 (4).

---

## 2. GroupLawAxioms.lean (1344 lines)

Module: **T-G — the five monoid/group axioms for `mulOver`** for every elliptic Weierstrass curve
over every ring, by universality-by-instantiation: T-G1 instance pack at the ULift atlas →
T-G3 atlas equations by field-points extensionality → T-G4 base-change transport → T-G5 `Over`
statements. Imports: `AdditionSpecPoints`, `NegModelBaseChange` (in-cluster),
mathlib `ProjectiveSpectrum.Proper`. Namespace `ModularCurves`. Local instances:
`MvPolynomial.gradedAlgebra`, Over monoidal pair.

### T-G1 instance pack (16 instances, lines 44–144)

#### `instance : IsNoetherianRing WeierstrassAtlasRing`
- **Type**: instance (anonymous). **What**: `ℤ[a₁..a₆][Δ⁻¹]` noetherian. **How**: `IsLocalization.isNoetherianRing` at `Submonoid.powers universalWeierstrass.Δ`. **Uses(project)**: `WeierstrassAtlasRing`, `universalWeierstrass` (AdditionBaseChange.lean). **UsedBy(cluster)**: TC for the next instance. **Vis**: public. **Lines**: 44–46 (3).

#### `instance : IsNoetherianRing WeierstrassAtlasRingU.{u}`
- **Type**: instance (anonymous). **What**: universe-`u` ULift atlas ring noetherian. **How**: `isNoetherianRing_of_ringEquiv` along `ULift.ringEquiv.symm`. **UsedBy(cluster)**: TC (`IsLocallyNoetherian` below → `isIntegral_of_isLocallyNoetherian`). **Vis**: public. **Lines**: 49–51 (3).

#### `isIntegral_projModel_u`
- **Type**: instance (T-W7.0e-proj at universe `u`)
- **What**: `IsIntegral (projModel W)` for `W` over any *field* in any universe.
- **How**: **`AlgebraicGeometry.Proj.isIntegral_of_isDomain`**; witness `X 0` homogeneous of degree 1 nonzero mod `projIdeal` by a total-degree contradiction (`MvPolynomial.totalDegree_le_of_dvd_of_isDomain`, `projective_polynomial_isHomogeneous`, `projIdeal_toIdeal`, `omega`).
- **Hypotheses**: `K` field, `W : WeierstrassCurve K`.
- **Uses(project)**: `projModel`, `projIdeal(_toIdeal)`, `quotientGrading`, `mk_mem_quotientGrading`, `projective_polynomial_isHomogeneous` (WeierstrassModel.lean).
- **UsedBy(cluster)**: in-file (`geometricallyIntegral_universalCurveπU`).
- **Vis**: public instance. **Lines**: 56–74 (19).
- **Notes**: universe-polymorphic restatement of `isIntegral_projModel`; docstring says proof is verbatim.

#### `isSeparated_projModel`
- **Type**: instance. **What**: `(projModel W).IsSeparated` for any `W` over any `R` (it is a `Proj`). **How**: `inferInstanceAs` on `Proj (quotientGrading (projIdeal W))`. **UsedBy(cluster)**: TC only — the `haveI hsep` in the atlas equations resolve through it; no by-name use. **Vis**: public instance. **Lines**: 77–79 (3).

#### `instance : SmoothOfRelativeDimension 1 (projModelπ universalWeierstrassLocU)` / `instance : Smooth (…)`
- **Type**: instances (anonymous). **What**: universal curve smooth (of rel. dim 1) over the atlas. **How**: `projModel_smooth` (WeierstrassModel) / `SmoothOfRelativeDimension.smooth`. **UsedBy(cluster)**: TC for `GeometricallyIntegral`→`IsIntegral` chain. **Vis**: public. **Lines**: 82–83 (2) / 85–86 (2).

#### `geometricallyIntegral_universalCurveπU`
- **Type**: instance (T-W7.0e crux at universe `u`)
- **What**: `GeometricallyIntegral (projModelπ universalWeierstrassLocU.{u})`.
- **How**: `geometricallyIntegral_iff` + `geometrically_iff_of_isClosedUnderIsomorphisms`; each geometric fibre identified with `projModel (W.map …)` by **`isPullback_projModelBaseChange`** (AdditionBaseChange), integral by `isIntegral_projModel_u`, transported by `ObjectProperty.prop_of_iso`.
- **Hypotheses**: none (fixed universal curve).
- **Uses(project)**: `universalWeierstrassLocU`, `isPullback_projModelBaseChange` (AdditionBaseChange), `isIntegral_projModel_u`.
- **UsedBy(cluster)**: TC only (feeds `IsIntegral` instance below); count 1.
- **Vis**: public instance. **Lines**: 91–103 (13).

#### remaining 9 anonymous instances (lines 106–144)
- **Type**: instances. **What**: `IsIntegral (projModel U)` (via `GeometricallyIntegral.isIntegral_of_isLocallyNoetherian`), `IsLocallyNoetherian` (via `LocallyOfFiniteType.isLocallyNoetherian`), `IsReduced (projModel U)`, then `IsIntegral`/`IsReduced` for the fibre square (n = 2) and both associativity spellings of the fibre cube (n = 3, `snd`- and `fst`-associated). **How**: all `inferInstance` off mathlib's integrality-of-pullback machinery once the base instances exist. **UsedBy(cluster)**: TC — these are exactly the `IsReduced`/`IsSeparated` side conditions of `hom_ext_of_forall_specPoint` at each fibre power in the atlas equations. **Vis**: public. **Lines**: 106–108, 111–112, 114, 118–119, 121–122, 125–128, 131–134, 136–139, 141–144.
- **Notes**: this is "the 0e instance pack"; the fibre-cube spellings are duplicated per associativity orientation deliberately.

### T-G2/T-G3 — atlas equations (lines 154–589, section `AtlasEquations`)

#### `mulModelHom_comm_atlas`
- **Type**: theorem (T-G3-comm)
- **What**: `pullbackSymmetry.hom ≫ mulModelHom 𝕌 = mulModelHom 𝕌` at the universe-`u` atlas (raw scheme level).
- **How**: **`hom_ext_of_forall_specPoint`** (PointsDictionary) on field points; canonical algebra from `Spec.preimage` of the structure composite; both sides evaluated by **`mulModelHom_specPoints`** (AdditionSpecPoints ×2, arguments swapped); closed by `add_comm` on `Affine.Point` + injectivity of `projModelPointsEquiv`; `pullback.hom_ext` bookkeeping for the symmetric lift.
- **Hypotheses**: none (fixed atlas).
- **Uses(project)**: PointsDictionary (`hom_ext_of_forall_specPoint`, `projModelPointsEquiv`), AdditionSpecPoints (`mulModelHom_specPoints`), AdditionChartGlobal (`mulModelHom`), T-G1 pack (TC).
- **UsedBy(cluster)**: in-file (`mulOver_comm_atlas`, `mulModelHom_comm`).
- **Vis**: public. **Lines**: 158–199 (42). **Proof >30 lines.**

#### `mulOver_assoc_atlas`
- **Type**: theorem (T-G3-assoc)
- **What**: associativity as the monoid-object equation at the atlas, `Over (Spec 𝕌)` level.
- **How**: `Over.OverMorphism.ext`; `hom_ext_of_forall_specPoint` on the fibre cube (`IsReduced` from the T-G1 pack via `inferInstanceAs` at the `fst`-associated spelling); three legs `hπ₁ hπ₂ hπ₃` normalized by `pullback.condition`; four **`mulModelHom_specPoints`** invocations (P₁₂, P₂₃, then the two nested sums); closed by `add_assoc` + `projModelPointsEquiv` injectivity; both sides collapsed to `pullback.lift … ≫ mulModelHom` via **`Over.associator_hom_left_snd_fst/…_snd_snd/…_fst`** and `Over.whiskerLeft_left_fst/snd`, `Over.whiskerRight_left_fst/snd` (ForMathlib/OverPullbackMul).
- **Hypotheses**: none.
- **Uses(project)**: as above + `mulModelHom_π` (AdditionChartGlobal).
- **UsedBy(cluster)**: in-file (`mulOver_assoc_of_map` raw).
- **Vis**: public. **Lines**: 204–366 (163). **Proof >30 lines** (longest in file).

#### `mulOver_comm_atlas`
- **Type**: theorem (T-G3-comm, Over level)
- **What**: braided commutativity equation at the atlas.
- **How**: wrapper: `Over.OverMorphism.ext` + `Over.braiding_hom_left` + `mulOver_left` + `mulModelHom_comm_atlas`.
- **UsedBy(cluster)**: **none** (count 1 — the general `mulOver_comm` goes through `mulModelHom_comm` instead).
- **Vis**: public. **Lines**: 370–374 (5).
- **Notes**: dead wrapper kept as the atlas-level record; dedup candidate.

#### `oneOver_mulOver_atlas`
- **Type**: theorem (T-G3-one-mul)
- **What**: left unit law at the atlas.
- **How**: `hom_ext_of_forall_specPoint`; `IsReduced` of the unit-tensor transported across the left unitor by `ObjectProperty.prop_of_iso`; zero leg evaluated by **`projModelPointsEquiv_zero`** (PointsDictionary) + `projModelZero_projModelπ` (WeierstrassModel); `mulModelHom_specPoints` + `zero_add`.
- **Hypotheses**: none.
- **Uses(project)**: `oneOver(_left)` (GroupLawConstruction), `projModelZero(_projModelπ)`, PointsDictionary, AdditionSpecPoints.
- **UsedBy(cluster)**: **none** (count 1 — general left unit derived by braiding from the right unit).
- **Vis**: public. **Lines**: 377–448 (72). **Proof >30 lines.**
- **Notes**: unused 72-line proof; candidate for deletion or for re-routing `oneOver_mulOver` through it.

#### `mulOver_oneOver_atlas`
- **Type**: theorem (T-G3-mul-one)
- **What**: right unit law at the atlas.
- **How**: mirror of the previous (`add_zero`, `Over.rightUnitor_hom_left`, `Over.whiskerLeft_left_fst/snd`).
- **UsedBy(cluster)**: in-file (`mulOver_oneOver_of_map` raw).
- **Vis**: public. **Lines**: 451–527 (77). **Proof >30 lines.**

#### `invOver_mulOver_atlas`
- **Type**: theorem (T-G3-inv)
- **What**: left inverse law at the atlas: `lift (invOver) 𝟙 ≫ mulOver = toUnit ≫ oneOver`.
- **How**: `hom_ext_of_forall_specPoint`; **`negModelHom_specPoints`** (GroupLawConstruction/AdditionSpecPoints layer) + `neg_add_cancel` + `projModelPointsEquiv_zero`; `negModelHom_π`, `invOver_left`, `Over.toUnit_left`, `Over.lift_left`.
- **Hypotheses**: none.
- **Uses(project)**: `invOver(_left)`, `negModelHom(_π)`, `negModelHom_specPoints`, PointsDictionary pack.
- **UsedBy(cluster)**: in-file (`invOver_mulOver_of_map` raw).
- **Vis**: public. **Lines**: 530–587 (58). **Proof >30 lines.**

### T-G4 transport (lines 591–1342, section `Transport`; `variable {R} [CommRing R]`)

#### `modelOver_hom` / `modelOver_left`
- **Type**: lemmas, `@[simp]` (T-G4 helpers)
- **What**: `(modelOver W).hom = projModelπ W`, `(modelOver W).left = projModel W`, keyed on the folded abbrev.
- **How**: `rfl`.
- **UsedBy(cluster)**: in-file (`modelOver_hom` ×3 proofs, `modelOver_left` in `mulOver_oneOver_of_map` simp set).
- **Vis**: public. **Lines**: 598 (1) / 601 (1).

#### `projModelZero_baseChangeOf`
- **Type**: lemma (T-G4 helper)
- **What**: of-form base-change naturality of the zero section (eqToHom-free wrapper of `projModelZero_baseChange`).
- **How**: `subst h` + `eqToHom_refl` + **`projModelZero_baseChange`** (WeierstrassModel).
- **Hypotheses**: `f : U →+* R`, `h : W₀.map f = W`.
- **Uses(project)**: `projModelBaseChangeOf` (AdditionBaseChange), `projModelZero_baseChange`.
- **UsedBy(cluster)**: in-file (unit-law and inverse-law transports, ×3).
- **Vis**: public. **Lines**: 606–613 (8).

#### `mulModelHom_comm`
- **Type**: theorem (T-G4-comm-raw)
- **What**: commutativity of `mulModelHom W` for every elliptic `W` over every `R`.
- **How**: transport: rewrite the atlas equation via `mulModelHom_universalWeierstrassLocU`; base-change square by **`mulModelHomBC_baseChange`** (AdditionSpecPoints); symmetry-vs-`pullbackMapBaseChangeOf` naturality by `pullback.hom_ext` simp; assemble by **`(isPullback_projModelBaseChangeOf …).hom_ext`** with π-leg via `mulModelHom_π` + `pullback.condition`.
- **Hypotheses**: `W : WeierstrassCurve R` `[W.IsElliptic]`.
- **Uses(project)**: AdditionBaseChange (`classifyRingHomU`, `universalWeierstrassLocU_map_classifyRingHomU`, `pullbackMapBaseChangeOf`, `isPullback_projModelBaseChangeOf`), AdditionSpecPoints.
- **UsedBy(cluster)**: in-file (`mulOver_comm`).
- **Vis**: public. **Lines**: 617–654 (38). **Proof >30 lines.**

#### `mulOver_comm`
- **Type**: theorem (T-W7.0g-comm) — **one of the five deliverables**
- **What**: braided commutativity in `Over (Spec R)` for every elliptic `W`/every `R`.
- **How**: `Over.OverMorphism.ext` + `Over.braiding_hom_left` + `mulModelHom_comm`.
- **UsedBy(cluster)**: in-file (`oneOver_mulOver`); outside: ModelRecord/GroupLawDescent (record assembly).
- **Vis**: public. **Lines**: 658–662 (5).

#### `modelOver_hom_baseChangeOf` (e₂)
- **Type**: private lemma. **What**: single-factor base-change compatibility over `Spec`. **How**: `modelOver_hom` + `.w` of `isPullback_projModelBaseChangeOf`. **UsedBy(cluster)**: in-file (`tripleMapBaseChangeOf`). **Vis**: private. **Lines**: 666–674 (9).

#### `tensorObj_hom_baseChangeOf` (e₁)
- **Type**: private lemma. **What**: tensor-square structure map commutes with the fibre-square base change (banked plan `docs/tg4/mulOver_assoc.plan.md`). **How**: `Over.tensorObj_hom` + calc chain on `pullback.fst`; inline `erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst]`. **UsedBy(cluster)**: in-file (`tripleMapBaseChangeOf`). **Vis**: private. **Lines**: 678–725 (48). **Proof >30 lines.**

#### `pullbackMapBaseChangeOf_fst` / `pullbackMapBaseChangeOf_snd`
- **Type**: private lemmas. **What**: fibre-square base change projects to single base change. **How**: `erw [pullbackMapBaseChangeOf, pullback.map, pullback.lift_fst/snd]`. **UsedBy(cluster)**: **none** (count 1 each — superseded by `pairMapBaseChangeOf_fst/snd` in the Over spelling). **Vis**: private. **Lines**: 728–738 (11) / 741–751 (11).
- **Notes**: dead private lemmas; deletion candidates.

#### `tripleMapBaseChangeOf`
- **Type**: private noncomputable def. **What**: the triple-tensor base-change comparison morphism, hoisted top-level so its `pullback.map` obligations (e₁/e₂) elaborate once outside the tensor-heavy contexts (whnf-timeout sidestep). **How**: `pullback.map` with `tensorObj_hom_baseChangeOf` + `modelOver_hom_baseChangeOf` as the commuting squares. **UsedBy(cluster)**: in-file (assoc transport chain, ~24 refs). **Vis**: private. **Lines**: 756–774 (19).

#### `tripleMapBaseChangeOf_fst` / `tripleMapBaseChangeOf_snd`
- **Type**: private lemmas. **What**: standard-spelled triple projections. **How**: `(limit.lift_π _ _).trans rfl`. **UsedBy(cluster)**: **none** (exclusive counts 1 — the primed Over-spelled variants are what the proofs use). **Vis**: private. **Lines**: 777–788 (12) / 791–802 (12).
- **Notes**: dead; deletion candidates.

#### `pairMapBaseChangeOf` (+ `_fst`, `_snd`)
- **Type**: private noncomputable def + 2 lemmas. **What**: fibre-square base change retyped at the Over-monoidal tensor (v10.132 spelling discipline), with its projections. **How**: definitional retype of `pullbackMapBaseChangeOf`; projections `(limit.lift_π _ _).trans rfl`. **UsedBy(cluster)**: in-file (assoc transport, ~19/4/4 refs). **Vis**: private. **Lines**: 807–811 (5), 813–819 (7), 821–827 (7).

#### `tripleMapBaseChangeOf_fst'` / `tripleMapBaseChangeOf_snd'`
- **Type**: private lemmas. **What**: triple projections, `pairMapBaseChangeOf`/Over-spelled. **How**: `(limit.lift_π _ _).trans rfl`. **UsedBy(cluster)**: in-file (×3/×2). **Vis**: private. **Lines**: 830–837 (8) / 840–848 (9).

#### `mulOver_left_baseChangeOf`
- **Type**: private lemma. **What**: `(mulOver (𝕌.map f)).left` intertwines the base change (Over spelling of `hbc`). **How**: **`mulModelHom_map_eq_BC`** + **`mulModelHomBC_baseChange`** (AdditionSpecPoints) + `mulOver_left`/`mulModelHom_universalWeierstrassLocU`. **UsedBy(cluster)**: in-file (×4: assoc legs, whiskerLeft naturality). **Vis**: private. **Lines**: 851–869 (19).

#### `assocSnd_pairMap_baseChangeOf`
- **Type**: private lemma. **What**: `α.hom.left ≫ snd`-composite intertwines the base changes (the `mid` bridge). **How**: `pullback.hom_ext`; term-mode `congrArg`/`Category.assoc` chains on `pairMapBaseChangeOf_fst/snd`, **`Over.associator_hom_left_snd_fst(_assoc)`**, `tripleMapBaseChangeOf_fst'/snd'`. **UsedBy(cluster)**: in-file (`assoc_whiskerLeft_baseChangeOf`). **Vis**: private. **Lines**: 873–921 (49). **Proof >30 lines.**

#### `whiskerLeftMul_fst_f/_U`, `whiskerLeftMul_snd_f/_U`, `assocMul_fst_f/_U`
- **Type**: 6 private lemmas. **What**: instantiations of `Over.whiskerLeft_left_fst/snd` and `Over.associator_hom_left_fst` at the mapped curve (`_f`) and the atlas (`_U`) — named so the big term proofs never re-elaborate the Over-monoidal statements inline. **How**: direct `exact` of the ForMathlib/OverPullbackMul lemmas. **UsedBy(cluster)**: in-file (×1 each, in `assoc_whiskerLeft_baseChangeOf`). **Vis**: private. **Lines**: 923–929, 931–936, 938–945, 947–953, 955–962, 964–970.

#### `assoc_whiskerLeft_baseChangeOf`
- **Type**: private lemma. **What**: base-change naturality of `α ≫ (mo ◁ mulOver)`, Over-spelled — the ◁-side of the assoc transport. **How**: `pullback.hom_ext`; fst leg via `assocMul_fst_f/U` + `whiskerLeftMul_fst_f/U` + `pairMapBaseChangeOf_fst` + `tripleMapBaseChangeOf_fst'`; snd leg via `whiskerLeftMul_snd_f/U` + **`mulOver_left_baseChangeOf`** + `assocSnd_pairMap_baseChangeOf`; all term-mode `refine (…).trans ?_` chains. **UsedBy(cluster)**: in-file (`mulOver_assoc_of_map` hR). **Vis**: private. **Lines**: 974–1026 (53). **Proof >30 lines.**

#### `mulOver_assoc_of_map`
- **Type**: theorem (T-W7.0g-assoc·of_map)
- **What**: associativity at the base-changed universal curve `𝕌.map f` — the hard T-G4 transport (option (b) of the banked plan).
- **How**: `Over.OverMorphism.ext`; `raw` = `.left` of **`mulOver_assoc_atlas`**; `hL` (▷-side naturality) by `pullback.hom_ext` on `pairMapBaseChangeOf_fst/snd` + `Over.whiskerRight_left_fst/snd` + `mulOver_left_baseChangeOf` + `tripleMapBaseChangeOf_fst'/snd'`; `hR` = `assoc_whiskerLeft_baseChangeOf`; assembled by **`(isPullback_projModelBaseChangeOf …).hom_ext`**, snd-leg structural via `Over.w`.
- **Hypotheses**: `f : 𝕌 →+* R`, `[(𝕌.map f).IsElliptic]`.
- **Uses(project)**: everything above + AdditionBaseChange.
- **UsedBy(cluster)**: in-file (`mulOver_assoc_of_eq`).
- **Vis**: public. **Lines**: 1034–1130 (97). **Proof >30 lines.**
- **Notes**: never constructs an inline triple `pullback.map`, never crosses the Over-vs-standard instance seam inside a tactic goal (plan discipline).

#### `mulOver_assoc_of_eq` / `mulOver_assoc`
- **Type**: theorems (·of_eq / T-W7.0g-assoc) — **deliverable**
- **What**: associativity at any `W` presented as a base change; then for every elliptic `W` via `classifyRingHomU W`.
- **How**: `subst h` → `of_map`; instantiation with **`universalWeierstrassLocU_map_classifyRingHomU`**.
- **UsedBy(cluster)**: `of_eq` in-file only; `mulOver_assoc` outside cluster (ModelRecord, GroupLawDescent, GroupScheme record assembly).
- **Vis**: public. **Lines**: 1134–1140 (7) / 1143–1147 (5).

#### `mulOver_oneOver_of_map`
- **Type**: theorem (T-W7.0g-mul-one·of_map)
- **What**: right unit law at `𝕌.map f` — "the hard proof; every general `W` reduces to it by subst".
- **How**: `raw` from **`mulOver_oneOver_atlas`**; `hbc` via `mulModelHom_map_eq_BC` + `mulModelHomBC_baseChange`; whisker naturality `hnat` by `erw [pullback.map_comp, pullback.map_comp]` (Over-monoidal vs standard `HasPullback` agree by proof irrelevance) + **`projModelZero_baseChangeOf`**; assembly by `isPullback….hom_ext` (fst-leg `erw … pullback.lift_fst; rfl`, π-leg by `Over.w`).
- **Hypotheses**: `f`, `[(𝕌.map f).IsElliptic]`.
- **UsedBy(cluster)**: in-file (`mulOver_oneOver_of_eq`).
- **Vis**: public. **Lines**: 1154–1216 (63). **Proof >30 lines.**

#### `mulOver_oneOver_of_eq` / `mulOver_oneOver`
- **Type**: theorems — **deliverable** (T-W7.0g-mul-one)
- **What**: right unit law for every elliptic `W`/every `R`.
- **How**: `subst`; `classifyRingHomU`.
- **UsedBy(cluster)**: `mulOver_oneOver` in-file (`oneOver_mulOver`); outside: record assembly.
- **Vis**: public. **Lines**: 1220–1224 (5) / 1228–1230 (3).

#### `oneOver_mulOver`
- **Type**: theorem (T-W7.0g-one-mul) — **deliverable**
- **What**: left unit law, derived (not transported).
- **How**: `← mulOver_comm`, `BraidedCategory.braiding_naturality_left`, `mulOver_oneOver`, **`braiding_rightUnitor`** — halves the unit-law work.
- **UsedBy(cluster)**: none in-cluster; outside: record assembly.
- **Vis**: public. **Lines**: 1235–1238 (4).

#### `invOver_mulOver_of_map`
- **Type**: theorem (T-W7.0g-inv-law·of_map)
- **What**: left inverse law at `𝕌.map f`.
- **How**: `raw` from **`invOver_mulOver_atlas`**; `hnat` has single-object domain so reduces by `pullback.hom_ext` to **`negModelHom_baseChange`** (NegModelBaseChange — the in-cluster input, "beastmode-A's") on the fst-leg and triviality on snd; fst assembly-leg via the base-change square `.w` + `projModelZero_baseChangeOf` calc; π-leg `Over.w`.
- **Hypotheses**: `f`, `[(𝕌.map f).IsElliptic]`.
- **Uses(project)**: NegModelBaseChange (in-cluster), AdditionSpecPoints, AdditionBaseChange, GroupLawConstruction (`invOver_left`).
- **UsedBy(cluster)**: in-file (`invOver_mulOver_of_eq`).
- **Vis**: public. **Lines**: 1245–1326 (82). **Proof >30 lines.**

#### `invOver_mulOver_of_eq` / `invOver_mulOver`
- **Type**: theorems — **deliverable** (T-W7.0g-inv-law)
- **What**: the left inverse law for every elliptic `W`/every `R`.
- **How**: `subst`; `classifyRingHomU`.
- **UsedBy(cluster)**: none in-cluster; outside: ModelRecord/GroupLawDescent/PatchHopf/SubgroupGroupObject.
- **Vis**: public. **Lines**: 1330–1334 (5) / 1338–1340 (3).

---

## 3. MulByHomFlat.lean (50 lines)

Module: **BB-FLAT funnel** (route (G), board v10.147) — defines the single funneled hypothesis for
`[N]`-flatness. Imports: `GroupLaw` (in-cluster). Namespace `ModularCurves.EllipticCurve`.

### `KernelNDivisible`
- **Type**: def (Prop)
- **What**: `∀` affine square-zero thickening `Spec(A'/I) ⊆ Spec A'` over `S` (`I² = ⊥`) and every `ε ∈ E(A')` restricting to `0` on the thickening, `∃ δ` also restricting to `0` with `N • δ = ε` — the square-zero point-kernels are `N`-divisible (Lie-theoretic content of `d[N] = N·`).
- **How**: definition; quantifies over `A' : CommRingCat.{u}`, `I : Ideal A'`, `b' : Spec A' ⟶ S`, `ε : E.Point b'` with `Point.restrict E (Spec.map (ofHom (Ideal.Quotient.mk I))) ε = 0`.
- **Hypotheses**: `E : EllipticCurve S`, `N : ℕ`.
- **Uses(project)**: `Point`, `Point.restrict`, `pointAddCommGroup` (GroupLaw).
- **UsedBy(cluster)**: MulByHomSmooth (through the statement of `kernelNDivisible_of_nIsInvertible`, KernelDivisibilityGlue.lean:380). Outside cluster: KernelDivisibilityChart/Glue (the N5 discharge).
- **Vis**: public. **Lines**: 40–46 (7).
- **Notes**: no sorry in this file; the header narrates the (then-open) discharge route. Header references `mulByHom_flat_of_kernelNDivisible` which does **not exist** under that name — the actual chain is `kernelNDivisible_of_nIsInvertible` (Glue) → `mulByHom_smooth/flat_of_nIsInvertible` (MulByHomSmooth); doc-drift cleanup item.

---

## 4. MulByHomSmooth.lean (234 lines)

Module: **N6 — smoothness (hence flatness) of `[N]` for `N` invertible** (BB-FLAT route (G)
closure) by the infinitesimal-lifting translation. Imports: `KernelDivisibilityGlue` (which pulls
in MulByHomFlat + GroupLaw). Namespace `ModularCurves.EllipticCurve`, `noncomputable section`.

### `formallySmooth_mulByHom_appLE`
- **Type**: theorem (N6 core, the (LIFT) argument)
- **What**: for `N` invertible and a compatible affine chart triple `W ⊆ S`, `U ⊆ π⁻¹W`, `V ⊆ [N]⁻¹U`, the chart ring map `Γ(U) ⟶ Γ(V)` of `[N]` is `FormallySmooth`.
- **How** (150 lines): chart triangle `π♯ = π♯ ≫ [N]♯` via `Scheme.Hom.appLE_comp_appLE` + a `rintro rfl` congruence `key`; `π`-formal smoothness from **`E.π.smooth_appLE`** (`RingHom.smooth_def`); reduce to `Algebra.FormallySmooth.of_comp_surjective`; lift the test map through **`Algebra.FormallySmooth.comp_surjective`** for `Γ(W) ⟶ Γ(V)`; geometrize to points `y`, `x̃` over `Spec B` via **`IsAffineOpen.SpecMap_appLE_fromSpec`**; defect `ε := Py − N•Pxt` is a square-zero kernel element (`restrict_sub`, `point_smul_eq_comp_mulBy`); divided by **`kernelNDivisible_of_nIsInvertible`** (KernelDivisibilityGlue, N5); corrected lift `Px := Pxt + δ`; lands in `V` because square-zero thickenings are surjective on `Spec` (`range_comap_of_surjective` + `Ideal.mk_ker` + `mem_of_pow_mem`); re-algebraize by `IsOpenImmersion.lift(_fac)` + `Spec.map_surjective/injective` + `cancel_mono hU.fromSpec`.
- **Hypotheses**: `N : ℕ`, `h : NIsInvertible S N`, `hW/hU/hV : IsAffineOpen`, `hUW : U ≤ π⁻¹W`, `hVU : V ≤ [N]⁻¹U`.
- **Uses(project)**: GroupLaw (`mulByHom(_π)`, `Point`, `Point.restrict`, `point_smul_eq_comp_mulBy`), TorsionUnramifiedFibre (`restrict_sub`, `restrict_add` — relocated Point API), KernelDivisibilityGlue (`kernelNDivisible_of_nIsInvertible`), Torsion (`NIsInvertible`).
- **UsedBy(cluster)**: in-file (`mulByHom_smooth_of_nIsInvertible`).
- **Vis**: public. **Lines**: 45–194 (150). **Proof >30 lines** (longest in file).

### `mulByHom_smooth_of_nIsInvertible`
- **Type**: theorem (N6)
- **What**: `Smooth (E.mulByHom N)` for `N` invertible on `S`.
- **How**: **`IsZariskiLocalAtSource.iff_exists_resLE`**; choose charts `W, U, V` by `isBasis_affineOpens.exists_subset_of_mem_open` (three times, threading `mulByHom_π`); reduce to the ring level by `HasRingHomProperty.iff_of_isAffine (P := @Smooth)` + `arrowResLEAppIso` + `RingHom.Smooth.propertyIsLocal.respectsIso`; `RingHom.smooth_def` splits into `formallySmooth_mulByHom_appLE` + `finitePresentation_appLE` (from **`mulByHom_locallyOfFinitePresentation`**, Torsion.lean).
- **Hypotheses**: `N`, `h : NIsInvertible S N`.
- **Uses(project)**: previous theorem; Torsion.lean.
- **UsedBy(cluster)**: in-file (`mulByHom_flat_of_nIsInvertible`).
- **Vis**: public. **Lines**: 198–223 (26).

### `mulByHom_flat_of_nIsInvertible`
- **Type**: theorem (BB-FLAT, invertible case — route (G) closed)
- **What**: `Flat (E.mulByHom N)` for `N` invertible.
- **How**: `haveI` smooth; `infer_instance` (smooth ⟹ flat).
- **Hypotheses**: `N`, `h`.
- **UsedBy(cluster)**: MulByHomEtale (`mulBy_etale'`).
- **Vis**: public. **Lines**: 227–230 (4).

---

## 5. MulByHomEtale.lean (90 lines)

Module: **étaleness of `[N]` and of the torsion, rewired through the PROVEN invertible-case
quasi-finiteness** — primed variants of the `MulByHomUnramified.lean` chain, kept in a separate
file so the HasseWeil/IsoTransport import closure of the quasi-finiteness proof stays out of
sibling-lane files. Imports: `MulByHomUnramified`, `MulByHomQuasiFinite`, `MulByHomSmooth`
(in-cluster). Namespace `ModularCurves.EllipticCurve`.

### `formallyUnramified_torsionπ_of_nIsInvertible'`
- **Type**: theorem (L-BC, proven-finiteness variant — Y1-CLOSER L3)
- **What**: `FormallyUnramified (E.torsionπ N)` for `N` invertible on `S`, with finiteness supplied by `torsionπ_isFinite_of_nIsInvertible`.
- **How**: `N = 0` case via **`isEmpty_of_nIsInvertible_zero`** (Torsion.lean:203); else **`FormallyUnramified.of_finite_fiberToSpecResidueField`** (ForMathlib/FormallyUnramifiedFibre) over each residue fibre; fibre = base-changed torsion by **`torsion_baseChange_isPullback`** (TorsionFibre) matched against `IsPullback.of_hasPullback` via `isoIsPullback_hom_snd` + `MorphismProperty.cancel_left_of_respectsIso`; field case by **`formallyUnramified_torsionπ_of_isUnit`** + `nIsInvertible_residueField` (TorsionUnramifiedFibre, in-cluster).
- **Hypotheses**: `N`, `h : NIsInvertible S N`.
- **Uses(project)**: MulByHomQuasiFinite (`torsionπ_isFinite_of_nIsInvertible`), TorsionUnramifiedFibre, TorsionFibre, ForMathlib/FormallyUnramifiedFibre, GroupLaw (`baseChange`).
- **UsedBy(cluster)**: in-file (`mulByHom_formallyUnramified''`).
- **Vis**: public. **Lines**: 37–59 (23).
- **Notes**: proof body is a near-verbatim copy of `formallyUnramified_torsionπ_of_nIsInvertible` (TorsionUnramifiedFibre:1434) with only the finiteness `haveI` swapped — flagged dedup candidate (factor over the finiteness hypothesis).

### `mulByHom_formallyUnramified''`
- **Type**: theorem (BB-DIFF master, proven-finiteness variant)
- **What**: `FormallyUnramified (E.mulByHom N)` for `N` invertible.
- **How**: **`formallyUnramified_mulByHom_of_torsionπ`** (MulByHomUnramified) applied to the primed torsion result.
- **UsedBy(cluster)**: in-file (`mulBy_etale'`).
- **Vis**: public. **Lines**: 63–66 (4).
- **Notes**: double-primed name = third variant in the family; naming cleanup once the sorried originals retire.

### `mulBy_etale'`
- **Type**: theorem (T-B5, proven-finiteness variant)
- **What**: `Etale (E.mulByHom N)` for `N` invertible — all inputs proven.
- **How**: `N = 0` empty-base case; else `haveI` flat (**`mulByHom_flat_of_nIsInvertible`**, in-cluster), unramified (`mulByHom_formallyUnramified''`), finite presentation (`mulByHom_locallyOfFinitePresentation`); close by **`Etale.of_formallyUnramified_of_flat`** (ForMathlib/InvariantTorsor).
- **Hypotheses**: `N`, `h`.
- **UsedBy(cluster)**: in-file (`torsionπ_etale'`).
- **Vis**: public. **Lines**: 70–80 (11).
- **Notes**: header: once BB-FLAT landed (it has), the `Y₁(N)` MASTER closes at `{propext, Classical.choice, Quot.sound}` through this theorem.

### `torsionπ_etale'`
- **Type**: theorem (T-B5′, proven-finiteness variant)
- **What**: `Etale (E.torsionπ N)` for `N` invertible.
- **How**: `MorphismProperty.pullback_snd` of `mulBy_etale'` (torsion is the pullback of `[N]` along the zero section).
- **UsedBy(cluster)**: none in-cluster (terminal deliverable; consumed by the Y1 assembly outside).
- **Vis**: public. **Lines**: 83–86 (4).

---

## 6. NegModelBaseChange.lean (103 lines)

Module: **base-change naturality of negation on the projective Weierstrass model** (T-W7.0b-BC),
mirroring `projModelZero_baseChange`; feeds the `invOver` T-G4 transport. Imports:
`GroupLawConstruction`. Namespace `ModularCurves`; local instance `MvPolynomial.gradedAlgebra`.
`variable {R R' : Type u} [CommRing R] [CommRing R']`.

### `Proj_map_congr`
- **Type**: private lemma
- **What**: equal graded homomorphisms give equal `Proj.map`s (irrelevant-ideal hypotheses are propositions).
- **How**: `subst h; rfl`.
- **Hypotheses**: graded rings `𝒜, ℬ`, `h : f = g`, both irrelevance conditions.
- **Uses(project)**: none (generic).
- **UsedBy(cluster)**: in-file (`negModelHom_baseChange`).
- **Vis**: **private**. **Lines**: 38–44 (7).
- **Notes**: explicitly a **local copy of the same-named private helper in GroupLawConstruction** — dedup candidate (hoist to a shared file, e.g. ForMathlib/GradedQuotient).

### `negVec_map`
- **Type**: lemma
- **What**: `negVec (W.map f) i = MvPolynomial.map f (negVec W i)` — the negation substitution vector base-changes coefficientwise.
- **How**: `fin_cases i` + `simp [negVec, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, sub_eq_add_neg]`.
- **Hypotheses**: `f : R →+* R'`, `W`, `i : Fin 3`.
- **Uses(project)**: `negVec` (GroupLawConstruction).
- **UsedBy(cluster)**: in-file (`aeval_negVec_map`).
- **Vis**: public. **Lines**: 50–53 (4).

### `aeval_negVec_map`
- **Type**: lemma
- **What**: the negation substitution commutes with coefficient base change on all of `R[X,Y,Z]`.
- **How**: `MvPolynomial.induction_on` (C/add/mul_X); `negVec_map` in the `mul_X` case.
- **Hypotheses**: `f`, `W`, `p : MvPolynomial (Fin 3) R`.
- **UsedBy(cluster)**: in-file (`negGradedQuot_comp_baseChangeGradedHom`).
- **Vis**: public. **Lines**: 56–63 (8).

### `negGradedQuot_comp_baseChangeGradedHom`
- **Type**: lemma
- **What**: the graded negation endomorphism commutes with the graded base-change homomorphism on the quotient graded ring.
- **How**: `GradedRingHom.ext` + `Ideal.Quotient.mk_surjective`; three instances of **`quotientGradingMap_mk`** (ForMathlib/GradedQuotient) unfolding `baseChangeGradedHom`/`negGradedQuot` on representatives (`mvMapGraded`, `negGradedPoly(_comap)`, `projIdeal_le_comap`); close with `aeval_negVec_map`.
- **Hypotheses**: `f`, `W`.
- **Uses(project)**: GroupLawConstruction (`negGradedQuot`, `negGradedPoly(_comap)`), WeierstrassModel (`baseChangeGradedHom`, `projIdeal(_le_comap)`), ForMathlib/GradedQuotient (`quotientGradingMap_mk`, `mvMapGraded`).
- **UsedBy(cluster)**: in-file (`negModelHom_baseChange`).
- **Vis**: public. **Lines**: 66–89 (24).

### `negModelHom_baseChange`
- **Type**: theorem (T-W7.0b-BC) — **the file's deliverable**
- **What**: `negModelHom (W.map f) ≫ projModelBaseChange f W = projModelBaseChange f W ≫ negModelHom W`.
- **How**: unfold both sides to `Proj.map` (`negModelHom`, `projModelBaseChange` = `Proj.map (baseChangeGradedHom …)`); `← Proj.map_comp` twice; **`Proj_map_congr`** on `negGradedQuot_comp_baseChangeGradedHom`.
- **Hypotheses**: `f`, `W` (no `IsElliptic` needed).
- **Uses(project)**: GroupLawConstruction (`negModelHom`), WeierstrassModel (`projModelBaseChange`, `baseChangeGradedHom_irrelevant_le`).
- **UsedBy(cluster)**: **GroupLawAxioms** (`invOver_mulOver_of_map` hnat fst-leg) — the advertised consumer (c5β's T-G4).
- **Vis**: public. **Lines**: 94–101 (8).

---

## 7. TorsionUnramifiedFibre.lean (1462 lines)

Module: **L-BC — `E[N] ⟶ S` formally unramified for `N` invertible** (BB-DIFF fibre leg;
board v10.123/124). Fibre-level core = augmentation-ideal rigidity of torsion (KM 2.3.1 in
infinitesimal form, no invariant differentials): a pure-algebra layer (`pairLift_key`), a
scheme layer (chart comorphisms, the affine Künneth box, `pointSharp_add`), then the three
public theorems. Also hosts three `Point`-restriction lemmas relocated byte-identically from
`MulByHomUnramified.lean` (which imports this file). Imports: `TorsionFibre`,
`ForMathlib.FormallyUnramifiedFibre`, `ForMathlib.NilpotentKerSpecMap`, `GroupScheme.PatchHopf`,
mathlib `Morphisms.FormallyUnramified`. Namespace `ModularCurves.EllipticCurve`.

### Relocated Point API (public, lines 49–67)

#### `pointEquivOverHom_sub`
- **Type**: theorem. **What**: `equiv (P − Q) = equiv P / equiv Q` in `Hom.commGroup` (companion of `pointEquivOverHom_add`). **How**: `rfl`. **Uses(project)**: GroupLaw. **UsedBy(cluster)**: in-file (`restrict_sub`). **Vis**: public. **Lines**: 49–52 (4).

#### `pointEquivOverHom_restrict`
- **Type**: theorem. **What**: restriction corresponds to precomposition by `Over.homMk k` under the dictionary. **How**: `Over.OverMorphism.ext` + simp + `rfl`. **UsedBy(cluster)**: in-file (`restrict_sub`). **Vis**: public. **Lines**: 56–61 (6).

#### `restrict_sub`
- **Type**: theorem. **What**: `Point.restrict` is a homomorphism on subtraction. **How**: injectivity of `pointEquivOverHom` + the two previous + **`GrpObj.comp_div`**. **UsedBy(cluster)**: **MulByHomSmooth** (defect computation) + in-file (`restrict_add`, core theorems). **Vis**: public. **Lines**: 64–67 (4).

### section `AugmentationAlgebra` (pure algebra over abstract `k'`, lines 69–173, all private)

#### `axisL` / `axisR` / `foldε`
- **Type**: private noncomputable defs. **What**: axis restrictions `C ⊗[k'] C →ₐ C` (`c⊗c' ↦ ε(c)·c'` / `c·ε(c')`) and the double augmentation `C ⊗ C →ₐ k'`. **How**: `Algebra.TensorProduct.lift` with `Commute.all`. **Hypotheses**: `ε : C →ₐ[k'] k'`. **UsedBy(cluster)**: in-file only (whole augmentation layer). **Vis**: private. **Lines**: 87–89 / 92–94 / 97–98.

#### `axisL_tmul` / `axisR_tmul` / `foldε_tmul`
- **Type**: `@[simp]` private lemmas. **What**: values on pure tensors. **How**: simp/`Algebra.ofId_apply`. **UsedBy(cluster)**: in-file (key identity, spec laws, tail). **Vis**: private. **Lines**: 100–102 / 104–106 / 108–110.

#### `pairLift_key`
- **Type**: private theorem — **the key identity**
- **What**: modulo `I·I = 0`, `lift p₁ p₂ x = p₂(axisL x) + p₁(axisR x) − alg(foldε x)` for `p₁,p₂` `I`-close to the augmentation.
- **How**: `TensorProduct.induction_on`; pure-tensor case: the difference is `(p₁c − alg εc)(p₂c′ − alg εc′) ∈ I·I = 0` — closed by `ring_nf` + **`linear_combination`**.
- **Hypotheses**: `h₁ h₂ : ∀ c, pᵢ c − alg (ε c) ∈ I`; `hII : ∀ a∈I, ∀ b∈I, a*b = 0`.
- **UsedBy(cluster)**: in-file (`pairLift_eq_zero_of_axes`, `pointSharp_add` 6c).
- **Vis**: private. **Lines**: 114–131 (18).
- **Notes**: "the 𝔴-operator computation that replaces every flatness/splitting argument".

#### `foldε_eq_axisL` / `foldε_eq_axisR`
- **Type**: private theorems. **What**: `foldε = ε ∘ axisL = ε ∘ axisR`. **How**: tensor induction. **UsedBy(cluster)**: in-file (units/prime-comap arguments ×4 each). **Vis**: private. **Lines**: 134–139 / 155–160.

#### `tensor_ringHom_ext`
- **Type**: private theorem. **What**: ring maps out of `A ⊗[k'] B` agree if they agree on both inclusions. **How**: induction + `Algebra.TensorProduct.tmul_mul_tmul`. **UsedBy(cluster)**: in-file (`pairBox_boxIso_eq_specMap`). **Vis**: private. **Lines**: 142–152 (11).

#### `pairLift_eq_zero_of_axes`
- **Type**: private theorem — **the final kill**. **What**: if both axis restrictions of `x` vanish, the pair-lift of `x` vanishes. **How**: `pairLift_key` + `foldε_eq_axisL` + `ring`. **UsedBy(cluster)**: in-file (`pointSharp_add_tail`). **Vis**: private. **Lines**: 163–171 (9).

### section `AugmentationScheme` (lines 175–1276)

#### `restrict_zero` / `restrict_add`
- **Type**: public theorems. **What**: `Point.restrict` sends `0 ↦ 0` and is additive. **How**: `point_zero_val` (TorsionFibre.lean:254) / `abel`-trick through `restrict_sub`. **UsedBy(cluster)**: **MulByHomSmooth** (`restrict_add` in the corrected lift) + in-file (`point_eq_zero…` induction). Outside: KernelDivisibilityChart, GammaHRepresentability, PatchHopf, DeligneOrder. **Vis**: public. **Lines**: 188–192 (5) / 195–199 (5).

#### `point_add_val_mu`
- **Type**: public theorem. **What**: `(P+Q).1 = (lift (equiv P) (equiv Q)).left ≫ μ.left` — the `Hom.commGroup` multiplication made explicit. **How**: `pointEquivOverHom_add` + `Over.comp_left`. **UsedBy(cluster)**: in-file (axis laws, `pointSharp_add` 6b). Outside: KernelDivisibilityChart, MulByHomUnramified. **Vis**: public. **Lines**: 204–210 (7).

#### `point_pair_left_fst` / `point_pair_left_snd`
- **Type**: public theorems. **What**: projections of the point pairing. **How**: `Over.comp_left` + `lift_fst/snd`. **UsedBy(cluster)**: in-file (`pairing_eq_pairBox`). **Vis**: public. **Lines**: 213–217 / 220–224 (5 each).

Context for the rest of the section: `variable {k} [Field k] {F : EllipticCurve (Spec (of k))} {R S' : CommRingCat} {φ : R ⟶ S'}`.

#### `specMap_base_surjective`
- **Type**: private theorem. **What**: `Spec` of a surjection with square-zero kernel is surjective on points. **How**: **`range_comap_of_surjective`** + primes contain nilpotents (`mem_of_pow_mem`). **UsedBy(cluster)**: in-file (`range_base_subset_of_reduction`). **Vis**: private. **Lines**: 230–246 (17).

#### `range_base_subset_of_reduction`
- **Type**: private theorem. **What**: every kernel-of-reduction point lands topologically in the zero point's chart. **How**: surjectivity + rewrite along `hred`. **UsedBy(cluster)**: in-file (`point_eq_zero…`). **Vis**: private. **Lines**: 249–259 (11).

#### `pointSharp`
- **Type**: private noncomputable def — **the central gadget**
- **What**: the chart comorphism `Γ(F.E, U) ⟶ R` of a chart-supported morphism `w : Spec R ⟶ F.E`: `w.appLE U ⊤ ≫ ΓSpecIso.hom`.
- **UsedBy(cluster)**: in-file (~30 sites).
- **Vis**: private. **Lines**: 262–264 (3).

#### `eq_of_pointSharp_eq`
- **Type**: private theorem. **What**: chart-supported morphisms are determined by their chart comorphism. **How**: **`IsAffineOpen.SpecMap_appLE_fromSpec`** recovery + `fromSpec_top` + `cancel_epi isoSpec.inv`. **UsedBy(cluster)**: in-file (`point_eq_zero…` conclusion). **Vis**: private. **Lines**: 268–280 (13).

#### `specMap_zero_appLE_fromSpec` / `specMap_π_appLE_fromSpec`
- **Type**: private theorems. **What**: `Spec`-shadows of the zero section / structure morphism through the chart. **How**: `SpecMap_appLE_fromSpec`. **UsedBy(cluster)**: **none — declared and never referenced** (counts 1; chunk-(i) identities superseded by the `appLE_congr_hom` route). **Vis**: private. **Lines**: 296–300 (5) / 303–306 (4).
- **Notes**: dead private lemmas; deletion candidates.

#### `tautPoint`
- **Type**: private noncomputable def. **What**: `hU.fromSpec` as a point of `E` over its own π-composite. **UsedBy(cluster)**: in-file (axis laws). **Vis**: private. **Lines**: 310–312 (3).

#### `zero_pairing_mul` / `pairing_zero_mul`
- **Type**: private theorems — **the two axis laws, value form**. **What**: pairing zero with the tautological point (either order) and multiplying is `fromSpec` — value shadows of `0+X=X` / `X+0=X`. **How**: `point_add_val_mu` + `zero_add`/`add_zero`. **UsedBy(cluster)**: in-file (`axisL_spec_law`/`axisR_spec_law`). **Vis**: private. **Lines**: 316–322 / 325–331 (7 each).

#### `pointSharp_congr`
- **Type**: private theorem. **What**: `pointSharp` depends only on the morphism (`subst`-transport of the range hypothesis). **How**: `subst h; rfl`. **UsedBy(cluster)**: in-file (×8). **Vis**: private. **Lines**: 334–337 (4).

#### `pointSharp_zero_point`
- **Type**: private theorem. **What**: chart evaluation of the zero point = augmentation followed by `t`-comorphism. **How**: `point_zero_val` (TorsionFibre) + **`Scheme.Hom.appLE_comp_appLE`**. **UsedBy(cluster)**: in-file (`pointSharp_zero_taut`, close/scale/final steps). **Vis**: private. **Lines**: 341–354 (14).

#### `pointSharp_comp_π`
- **Type**: private theorem. **What**: chart evaluation restricted along `π` is the `t`-comorphism (the `commutes'` of the AlgHom packaging). **How**: `appLE_comp_appLE` + **`FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom`** (GroupScheme) on `P.2`. **UsedBy(cluster)**: in-file (6a AlgHoms, final calc). **Vis**: private. **Lines**: 357–363 (7).

#### `zero_appLE_π_appLE`
- **Type**: private theorem. **What**: `ζ ∘ π♯ = id` — the augmentation retracts the structure map (Γ-dual of `zero ≫ π = 𝟙`). **How**: `appLE_comp_appLE` + `appLE_congr_hom F.zero_π` + `AffineChartPatch.appLE_id`. **UsedBy(cluster)**: in-file (`chartAug.commutes'`, final calc). **Vis**: private. **Lines**: 366–373 (8).

### section `Box` (lines 376–1274; `variable {U : (F.E).Opens}`)

#### `chartAlgebra` (local instance) / `chartAlgebra_ofHom`
- **Type**: private noncomputable local instance / private theorem. **What**: `Γ(Spec k,⊤)`-algebra structure on `Γ(F.E,U)` via `π.appLE`, and its `ofHom` characterization. **UsedBy(cluster)**: in-file (`boxIso`). **Vis**: private (instance is `local`). **Lines**: 381–383 / 385–387 (3 each).

#### `boxIso`
- **Type**: private noncomputable def — **the affine Künneth box**. **What**: `pullback (π.resLE ⊤ U) (π.resLE ⊤ U) ≅ Spec (Γ(U) ⊗ Γ(U))`. **How**: **`patchKunneth`** (GroupScheme/PatchKunneth.lean, via the PatchHopf import; NEW-HOPF layer). **UsedBy(cluster)**: in-file (pair identification, spec laws, `q`). **Vis**: private. **Lines**: 391–394 (4).

#### `boxι`
- **Type**: private noncomputable def. **What**: the box's inclusion into the fibre square `pullback F.π F.π`. **How**: `pullback.map` on `U.ι` legs (`Scheme.Hom.resLE_comp_ι`). **UsedBy(cluster)**: in-file (~10 refs). **Vis**: private. **Lines**: 397–401 (5).

#### `liftU` / `liftU_ι`
- **Type**: private noncomputable def / theorem. **What**: factorisation of a chart-supported morphism through the open `U`, and its defining triangle. **How**: `IsOpenImmersion.lift(_fac)` + `Scheme.Opens.range_ι`. **UsedBy(cluster)**: in-file (`pairBox`, correspondence). **Vis**: private. **Lines**: 404–409 (6) / 411–413 (3).

#### `liftU_toSpecΓ`
- **Type**: private theorem — **the chart correspondence**. **What**: `liftU hw ≫ U.toSpecΓ = Spec.map (pointSharp w hw)`. **How**: `SpecMap_appLE_fromSpec` + `isoSpec` bookkeeping + **`Scheme.isoSpec_Spec_hom`** + `Spec.map_comp`. **UsedBy(cluster)**: in-file (both Künneth legs). **Vis**: private. **Lines**: 417–437 (21).

#### `pairBox` (+ `pairBox_fst`, `pairBox_snd`)
- **Type**: private noncomputable def + 2 theorems. **What**: the pairing of two chart-supported points as a morphism into the box, with projections. **How**: `pullback.lift (liftU hp) (liftU hq)` (compatibility over `⊤.ι`); `lift_fst/snd`. **UsedBy(cluster)**: in-file. **Vis**: private. **Lines**: 440–447 (8), 449–452, 454–457.

#### `pairing_eq_pairBox`
- **Type**: private theorem. **What**: the `Hom.commGroup` pairing = box pairing ≫ box inclusion. **How**: `pullback.hom_ext` on `point_pair_left_fst/snd` vs `pairBox_fst/snd ≫ liftU_ι`. **UsedBy(cluster)**: in-file (spec laws, `hsum`). **Vis**: private. **Lines**: 460–476 (17).

#### `pairBox_boxIso_includeLeft` / `pairBox_boxIso_includeRight`
- **Type**: private theorems. **What**: the two Künneth legs of the pairing are `Spec (pointSharp Pᵢ)`. **How**: **`patchKunneth_hom_comp_includeLeft/Right`** (PatchKunneth) + `pairBox_fst/snd` + `liftU_toSpecΓ`. **UsedBy(cluster)**: in-file (`pairBox_boxIso_eq_specMap`). **Vis**: private. **Lines**: 479–487 (9) / 490–499 (10).

#### `pointSharp_fromSpec` (TAUT-SHARP)
- **Type**: private theorem. **What**: chart comorphism of `fromSpec` is `𝟙 Γ(F.E,U)`. **How**: `appLE_congr_hom` on `fromSpec = isoSpec.inv ≫ U.ι`, `AffineChartPatch.ι_appLE_top`/`appLE_top_top`, `isoSpec_hom` + **`Scheme.Opens.toSpecΓ_appTop`** + `topIso` juggling. **UsedBy(cluster)**: in-file (spec laws, tail). **Vis**: private. **Lines**: 502–522 (21).

#### `pointSharp_zero_taut` (TAUT-ZERO)
- **Type**: private theorem. **What**: chart comorphism of the zero point over the tautological base = `ζ ≫ π♯`. **How**: `pointSharp_zero_point` + `appLE_comp_appLE` + `pointSharp_fromSpec`. **UsedBy(cluster)**: in-file (both spec laws). **Vis**: private. **Lines**: 526–543 (18).

#### `pairBox_boxIso_eq_specMap`
- **Type**: private theorem. **What**: the Künneth identification of the pairing in map form — instance-free: target ring map characterised by its two inclusion legs. **How**: `Spec.map_preimage` + `Spec.map_injective` + **`tensor_ringHom_ext`** with legs `pairBox_boxIso_includeLeft/Right`. **UsedBy(cluster)**: in-file (spec laws, 6b `hid`). **Vis**: private. **Lines**: 547–578 (32). **Proof >30 lines** (with statement).

#### `chartAug`
- **Type**: private noncomputable def. **What**: the augmentation `ε' : Γ(F.E,U) →ₐ[Γ(Spec k,⊤)] Γ(Spec k,⊤)` from `F.zero.appLE`, `commutes' := zero_appLE_π_appLE`. **UsedBy(cluster)**: in-file (everywhere in the tail; the `ε'` of the algebra layer instantiated). **Vis**: private. **Lines**: 581–585 (5).

#### `axisL_spec_law` / `axisR_spec_law`
- **Type**: private theorems — **the axis laws, `Spec` form**. **What**: `Spec (axisL/axisR (chartAug)) ≫ boxIso.inv ≫ boxι ≫ μ.left = hU.fromSpec` (geometric content of `0+X=X` / `X+0=X`). **How**: `pairBox_boxIso_eq_specMap` at (0, taut) / (taut, 0) with legs by **`pointSharp_zero_taut`** and **`pointSharp_fromSpec`**; then `pairing_eq_pairBox`.symm + `zero_pairing_mul`/`pairing_zero_mul`. **UsedBy(cluster)**: in-file (6d `hqp`, tail hypotheses ×2 each). **Vis**: private. **Lines**: 590–614 (25) / 617–641 (25).

#### `pointSharp_specMap_comp`
- **Type**: private theorem. **What**: `(Spec.map g ≫ v)♯ = v♯ ≫ g` — chart evaluation of a `Spec`-precomposition. **How**: **`Scheme.ΓSpecIso_naturality`** + `appLE_top_top` + `appLE_comp_appLE`. **UsedBy(cluster)**: in-file (tail 6f/6g ×3). **Vis**: private. **Lines**: 644–654 (11).

#### `specMap_square_comp`
- **Type**: private theorem. **What**: `Spec` of a commuting `CommRingCat` square composed with a classified base leg — abstract objects, no localization unfolds. **How**: `Spec.map_comp` rewriting. **UsedBy(cluster)**: in-file (`epsHalf_exists`). **Vis**: private. **Lines**: 658–662 (5).

#### `AugLocPackage` (structure)
- **Type**: private structure — **the opacity firewall**
- **What**: the two localizations (at the double-augmentation prime of the box ring, and at the augmentation prime of the chart ring) exported as OPAQUE `CommRingCat` objects (`L`, `LεL`, `LεR`) with exactly the 12 fields the tail consumes (`algL`, `φL`, `aL/aR`, `hφLalg`, `hrangeL`, `hsurj`, `haLalg/haRalg`, `hkerLεL/hkerLεR`, `haxSpecL/haxSpecR`).
- **How**: data record. **Hypotheses**: `hU`, `heU`, `[Algebra Γ(Spec k,⊤) R]`, primality of both kernels, `pT`, `q`.
- **UsedBy(cluster)**: in-file (`augLocPackage_exists`, `pointSharp_add_tail`).
- **Vis**: private. **Lines**: 669–698 (30).
- **Notes**: "the tail's `pointSharp` elaborations then never unfold a localization — the whnf wall of the ledger stops at the fvars." Performance architecture, not mathematics.

#### `EpsHalf` (structure)
- **Type**: private structure. **What**: one axis-side of the chart-prime localization data (fields `Lε`, `algLε`, `a`, `halg`, `hker'`, `hspec`). **UsedBy(cluster)**: in-file (`epsHalf_exists` → `augLocPackage_exists`). **Vis**: private. **Lines**: 701–718 (18).

#### `epsHalf_square`
- **Type**: private theorem. **What**: the commuting square of the axis localization map (own heartbeat budget). **How**: **`IsLocalization.map_comp`** + `CommRingCat.ofHom_comp`. **UsedBy(cluster)**: in-file (`epsHalf_exists`). **Vis**: private. **Lines**: 721–749 (29).

#### `epsHalf_exists`
- **Type**: private theorem. **What**: constructor of one axis-side (generic in the axis map): `Nonempty (EpsHalf …)`. **How**: instantiate at `Localization.AtPrime (ker ε')`; fields by **`IsLocalization.map_eq`**, **`IsLocalization.map_eq_zero_iff`**, `specMap_square_comp (epsHalf_square …)`. **UsedBy(cluster)**: in-file (`augLocPackage_exists` ×2). **Vis**: private. **Lines**: 752–776 (25).

#### `augLocPackage_exists`
- **Type**: private theorem. **What**: constructor of the localization package — "every localization unfolding happens here, in a small context". **How**: `L := Localization.AtPrime (ker (foldε ε'))`; `φL := IsLocalization.lift hunits`; range fact by **`PrimeSpectrum.le_iff_specializes`** + `Specializes.mem_open`; prime-compatibility of both axes via `foldε_eq_axisL/R`; assemble two `epsHalf_exists`; surjectivity by `IsLocalization.surj`. **Hypotheses**: `hunits` (pair-lift units off the prime), `hqp`, both axis `Spec` laws. **UsedBy(cluster)**: in-file (`pointSharp_add_tail`). **Vis**: private. **Lines**: 780–841 (62). **Proof >30 lines.**

#### `pointSharp_add_tail`
- **Type**: private theorem — **the hoisted tail (6e′–6g)**
- **What**: standalone final segment of `pointSharp_add`: given the package hypotheses (5 morphism-level facts + closeness + units + identification), `(P₁+P₂)♯ f = P₁♯ f + P₂♯ f` for `f` in the augmentation ideal.
- **How**: 6f — factor the sum's evaluation through the localization (`pointSharp_specMap_comp`, `pointSharp_congr`); 6g — the defect `a := ψ′f − algL(f⊗1) − algL(1⊗f)` is killed by both axis maps (`haLalg/haRalg` + `axisL_tmul` + `hεf`); clear denominators by `pkg.hsurj`; kill numerator via `hkerLεL/R` units and the `(1⊗u)(v⊗1)`-trick (**`linear_combination`**); **`pairLift_eq_zero_of_axes`** gives `pT y′ = 0`; unit-cancel (`IsUnit.mul_right_eq_zero` ×3) gives `φL a = 0`; unwind by `hidL/hidR`.
- **Hypotheses**: 17 explicit hypotheses (the box geometry enters only through `hsum`, `haxLq`, `haxRq`, `hidL`, `hidR`, `hqp`).
- **UsedBy(cluster)**: in-file (`pointSharp_add`).
- **Vis**: private. **Lines**: 846–1013 (168). **Proof >30 lines.**
- **Notes**: hoisted so the localization `set`s run against a small context — "the inline form blows the whnf budget".

#### `pointSharp_add`
- **Type**: private theorem — **additivity of the chart evaluation on kernel-of-reduction points (the geometric heart)**
- **What**: for `P₁ P₂` reducing to zero along square-zero `φ` and `f` in the augmentation ideal, `(P₁+P₂)♯ f = P₁♯f + P₂♯f`.
- **How**: 6a — algebra package (`p₁ p₂` AlgHoms via `pointSharp_comp_π`; `pT := lift p₁ p₂`; `I := ker φ`; H-φ collapse `hφsharp` via `appLE_congr_hom` + `ΓSpecIso_naturality`; closeness `hclose` via `pointSharp_zero_point`); 6b — the sum through the box (**`pairBox_boxIso_eq_specMap`**, `point_add_val_mu`, `pairing_eq_pairBox`, `Algebra.TensorProduct.lift_comp_includeLeft/Right`); 6c — units off the augmentation prime (**`pairLift_key`**, `Function.Injective.isDomain` across `ΓSpecIso`, `RingHom.ker_isPrime`, **`IsNilpotent.isUnit_add_left_of_commute`**); 6d — the prime lands in the chart (`PrimeSpectrum.ext` comap computation + **`axisL_spec_law`**); tail — `pointSharp_add_tail`.
- **Hypotheses**: `hU`, `heU`, `hφ` surjective, `hφ2 : ker² = ⊥`, both restriction hypotheses, four range hypotheses, `hf : ζ f = 0`.
- **UsedBy(cluster)**: in-file (`point_eq_zero…` scaling induction).
- **Vis**: private. **Lines**: 1019–1272 (254, incl. the 64-line execution-ledger comment 1031–1094). **Proof >30 lines** (largest in cluster).
- **Notes**: the retained EXECUTION LEDGER documents the original 0–6g plan including superseded stalk-based routes (6e/6f germ arguments) — cleanup candidate: compress the ledger to the executed 6a–6d+tail plan.

#### `point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero`
- **Type**: public theorem — **L-BC core: augmentation-ideal rigidity of torsion** (KM 2.3.1 p. 74, infinitesimal form)
- **What**: over a field `k`, `D ∈ F.Point t` with (i) `restrict (Spec.map φ) D = 0` for square-zero `φ : R ↠ S'` and (ii) `N • D = 0` with `N ∈ k˟`, is `0`. No invariant differentials, no degree counts.
- **How**: chart `U` at the zero section (`Unique (PrimeSpectrum k)` + `isBasis_affineOpens`); all `n • D` reduce to zero (induction with `restrict_add`) hence land in `U` (**`range_base_subset_of_reduction`**); scaling `hscale : (n•D)♯f = n • (D♯f)` on the augmentation ideal by induction with **`pointSharp_add`**; `N`-kill: `N` unit in `Γ(Spec k,⊤)` and in `R` (`isUnit_map`, `map_natCast`), so `D♯` vanishes on the augmentation ideal; conclude `D♯ = 0♯` by decomposing `c = π♯(ζc) + (c − π♯(ζc))` (`pointSharp_comp_π`, `zero_appLE_π_appLE`) and **`eq_of_pointSharp_eq`**.
- **Hypotheses**: `F` over `Spec k` field; `φ` surjective, `ker φ ² = ⊥`; `D`; `hres`; `hN : IsUnit (N : k)`; `hND`.
- **Uses(project)**: everything above + TorsionFibre (`point_zero_val`).
- **UsedBy(cluster)**: in-file (`formallyUnramified_torsionπ_of_isUnit`).
- **Vis**: public. **Lines**: 1285–1385 (101). **Proof >30 lines.**

#### `formallyUnramified_torsionπ_of_isUnit`
- **Type**: public theorem (L-B, field case)
- **What**: over a field with `N` invertible, `E[N] ⟶ Spec k` is formally unramified.
- **How**: **`FormallyUnramified.of_hom_ext`** (ForMathlib/FormallyUnramifiedFibre): two lifts differ by an `N`-torsion point reducing to zero — via **`torsionPointsEquiv`** (Torsion.lean) + `Submodule.mem_torsionBy_iff`; killed by `point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero`.
- **Hypotheses**: `F`, `N`, `hN : IsUnit (N : k)`.
- **Uses(project)**: Torsion (`torsionπ`, `torsionι`, `torsionPointsEquiv`), ForMathlib/FormallyUnramifiedFibre, the core theorem.
- **UsedBy(cluster)**: in-file (`formallyUnramified_torsionπ_of_nIsInvertible`); **MulByHomEtale** (primed variant).
- **Vis**: public. **Lines**: 1391–1419 (29).

#### `nIsInvertible_residueField`
- **Type**: public theorem. **What**: `NIsInvertible X N` ⟹ `IsUnit (N : κ(x))` for every `x`. **How**: `germ ⊤ x ≫ residue` + `isUnit_map` + `map_natCast`. **Uses(project)**: Torsion (`NIsInvertible`). **UsedBy(cluster)**: in-file + **MulByHomEtale**. **Vis**: public. **Lines**: 1422–1426 (5).
- **Notes**: stated for general `X : Scheme` — general-purpose; candidate to move next to `NIsInvertible` (Torsion.lean).

#### `formallyUnramified_torsionπ_of_nIsInvertible`
- **Type**: public theorem (**L-BC = the arithmetic input of BB-DIFF**)
- **What**: `N` invertible on `S` ⟹ `FormallyUnramified (E.torsionπ N)`.
- **How**: `N = 0` empty case (`isEmpty_of_nIsInvertible_zero`); else `haveI := E.torsionπ_isFinite N` (Torsion — the **sorried-in-general** finiteness box BB-QF lives behind this name) + **`FormallyUnramified.of_finite_fiberToSpecResidueField`** (T-DISC); each fibre identified with the base-changed torsion by **`torsion_baseChange_isPullback`** (TorsionFibre) + `isoIsPullback_hom_snd` + `cancel_left_of_respectsIso`; field case + `nIsInvertible_residueField`.
- **Hypotheses**: `E`, `N`, `h : NIsInvertible S N`.
- **Uses(project)**: Torsion, TorsionFibre, ForMathlib/FormallyUnramifiedFibre, GroupLaw (`baseChange`).
- **UsedBy(cluster)**: none by name in-cluster (MulByHomEtale re-proves it as the primed variant with the *proven* finiteness input).
- **Vis**: public. **Lines**: 1434–1458 (25).
- **Notes**: axiom-hygiene: this unprimed version inherits whatever `torsionπ_isFinite` depends on; the primed MulByHomEtale version is the clean-axiom route. Dedup candidate (factor both over a `[IsFinite (torsionπ N)]`-style hypothesis).

---
---

# File Summaries

### File Summary — GroupLaw.lean
- **Totals**: 410 lines; 30 declarations = 1 structure (`EllipticCurve`), 3 abbrevs (`asOver`, `mulByHom`, `Point`), 3 instances (`grpObj`, `isCommMonObj`, `pointAddCommGroup`), 5 defs (`mulBy`, `zeroPoint`, `pointEquivOverHom`, `Point.restrict`, `baseChange`, `Point.asSection`, `Point.baseChangeEquiv`, private `pointBaseChangeFun` — 8 counting all), 15 theorems/lemmas (incl. 2 sorried, 1 private).
- **Key API**: the working record `EllipticCurve S` (grp/comm/one_eq_zero); `mulBy`/`mulByHom` + spec `point_smul_eq_comp_mulBy`; `Point g` + `pointAddCommGroup` + `pointEquivOverHom`; `baseChange` (T-A5) + `mulBy_baseChange` (T-D6a-ii) + `Point.asSection(_zsmul)` + `Point.baseChangeEquiv` (T-H2b, `≃+`).
- **Unused-in-file**: `zeroPoint` (also unused in cluster; outside consumers YOneAtlasClassify/WeilPairing), `abelEnrichment_exists`, `abelEnrichment_unique`, `mulByHom_π` (simp-only export; by-name consumer MulByHomSmooth), `Point.restrict` (consumers MulByHomFlat/Smooth/TorsionUnramifiedFibre), `Point.asSection_coe`, `Point.asSection_zsmul`, `Point.baseChangeEquiv(_apply_coe)` (all exported API with outside-cluster consumers).
- **CODE-sorry**: 2 — `abelEnrichment_exists` (:76) and `abelEnrichment_unique` (:81), both `by sorry`, the deferred Abel/purity canonicity project (T-A6b/T-A6c); the record's only WIP.
- **set_option**: none.
- **Proofs >30 lines**: `baseChange` (47, mostly the `one_eq_zero` field), `Point.asSection_zsmul` (33, deliberate term-mode), private `pointBaseChangeFun_add` (75, term-mode).
- **Private/public**: 28 public + 2 private (`pointBaseChangeFun`, `pointBaseChangeFun_add`).

### File Summary — GroupLawAxioms.lean
- **Totals**: 1344 lines; 58 declarations = 16 instances (12 anonymous; T-G1 pack), 2 private noncomputable defs (`tripleMapBaseChangeOf`, `pairMapBaseChangeOf`), 40 theorems/lemmas. Sections: `AtlasEquations` (T-G2/G3), `Transport` (T-G4/G5).
- **Key API**: the five group-law deliverables for every elliptic `W` over every `R` — `mulOver_assoc`, `mulOver_comm`, `mulOver_oneOver`, `oneOver_mulOver`, `invOver_mulOver` (+ raw `mulModelHom_comm`); the T-G1 integrality/separatedness instance pack at the ULift atlas (feeds `hom_ext_of_forall_specPoint`); T-G4 helpers `modelOver_hom/left`, `projModelZero_baseChangeOf`.
- **Unused-in-file**: `mulOver_comm_atlas` (5-line dead wrapper), `oneOver_mulOver_atlas` (72-line proof, dead — general left unit is derived by braiding instead), private `pullbackMapBaseChangeOf_fst/_snd` and unprimed `tripleMapBaseChangeOf_fst/_snd` (superseded by primed/Over-spelled variants); `isSeparated_projModel`, `geometricallyIntegral_universalCurveπU` and the anonymous instances have no by-name uses (TC-resolution only, by design).
- **CODE-sorry**: none.
- **set_option**: none.
- **Proofs >30 lines** (12): `mulOver_assoc_atlas` (163), `mulOver_assoc_of_map` (97), `invOver_mulOver_of_map` (82), `mulOver_oneOver_atlas` (77), `oneOver_mulOver_atlas` (72), `mulOver_oneOver_of_map` (63), `invOver_mulOver_atlas` (58), `assoc_whiskerLeft_baseChangeOf` (53), `assocSnd_pairMap_baseChangeOf` (49), `tensorObj_hom_baseChangeOf` (48), `mulModelHom_comm_atlas` (42), `mulModelHom_comm` (38). Heavy verbose-spelling duplication (`universalWeierstrassLocU.{u}` written out hundreds of times) — golf/abbreviation candidate.
- **Private/public**: 37 public + 21 private (the whole T-G4 base-change-naturality helper layer: `modelOver_hom_baseChangeOf`, `tensorObj_hom_baseChangeOf`, `pullbackMapBaseChangeOf_fst/snd`, `tripleMapBaseChangeOf`(+4 projections), `pairMapBaseChangeOf`(+2), `mulOver_left_baseChangeOf`, `assocSnd_pairMap_baseChangeOf`, 6 whisker/associator instantiations, `assoc_whiskerLeft_baseChangeOf`).

### File Summary — MulByHomFlat.lean
- **Totals**: 50 lines; 1 declaration — the def `KernelNDivisible` (Prop).
- **Key API**: `KernelNDivisible N` — the single funneled hypothesis of BB-FLAT route (G): square-zero point-kernels `ker(E(A') → E(A'/I))` are `N`-divisible.
- **Unused-in-file**: n/a (single declaration). Cluster consumer: MulByHomSmooth via `kernelNDivisible_of_nIsInvertible` (KernelDivisibilityGlue.lean:380, the N5 discharge); outside: KernelDivisibilityChart/Glue.
- **CODE-sorry**: none (the header narrates the then-open discharge, but the file carries no sorry).
- **set_option**: none.
- **Proofs >30 lines**: none.
- **Private/public**: 1 public, 0 private.
- **Note**: header references `mulByHom_flat_of_kernelNDivisible`, a name that never materialized (the chain landed as `mulByHom_smooth/flat_of_nIsInvertible`); doc-drift fix.

### File Summary — MulByHomSmooth.lean
- **Totals**: 234 lines; 3 declarations, all public theorems (`noncomputable section`).
- **Key API**: `mulByHom_flat_of_nIsInvertible` (BB-FLAT closed, route (G)) ← `mulByHom_smooth_of_nIsInvertible` (N6) ← `formallySmooth_mulByHom_appLE` (the (LIFT) core: infinitesimal lifting for `[N]` from smoothness of `E/S` + `KernelNDivisible`).
- **Unused-in-file**: none (linear chain); cluster consumer of the flat result: MulByHomEtale (`mulBy_etale'`).
- **CODE-sorry**: none.
- **set_option**: none.
- **Proofs >30 lines**: `formallySmooth_mulByHom_appLE` (150 — geometrize / lift / divide-defect / correct / re-algebraize; decomposition candidate: the square-zero-thickening-is-surjective-on-Spec block and the re-algebraization block are self-contained).
- **Private/public**: 3 public, 0 private.

### File Summary — MulByHomEtale.lean
- **Totals**: 90 lines; 4 declarations, all public theorems.
- **Key API**: `mulBy_etale'` (T-B5: `[N]` étale, all inputs proven) and `torsionπ_etale'` (T-B5′: `E[N] ⟶ S` étale) for `N` invertible — the Y1-CLOSER endpoints; plus the proven-finiteness rewires `formallyUnramified_torsionπ_of_nIsInvertible'` and `mulByHom_formallyUnramified''`.
- **Unused-in-file**: `torsionπ_etale'` (terminal deliverable; consumed outside the cluster by the Y1 assembly).
- **CODE-sorry**: none.
- **set_option**: none.
- **Proofs >30 lines**: none (longest 23).
- **Private/public**: 4 public, 0 private.
- **Notes**: exists as a separate file purely to quarantine the HasseWeil/IsoTransport import closure of `torsionπ_isFinite_of_nIsInvertible`. `formallyUnramified_torsionπ_of_nIsInvertible'` duplicates the body of the unprimed TorsionUnramifiedFibre theorem with one `haveI` swapped — factor-over-finiteness dedup candidate; primed/double-primed naming to be resolved when the sorried originals retire.

### File Summary — NegModelBaseChange.lean
- **Totals**: 103 lines; 5 declarations = 4 lemmas + 1 theorem (1 private).
- **Key API**: `negModelHom_baseChange` (T-W7.0b-BC): negation on the projective Weierstrass model is natural in the base ring — consumed by GroupLawAxioms' `invOver_mulOver_of_map` (the T-G4 inverse-law transport). Supporting chain: `negVec_map` → `aeval_negVec_map` → `negGradedQuot_comp_baseChangeGradedHom`.
- **Unused-in-file**: none (linear chain; `negModelHom_baseChange` consumed in-cluster by GroupLawAxioms).
- **CODE-sorry**: none.
- **set_option**: none.
- **Proofs >30 lines**: none (longest 24).
- **Private/public**: 4 public + 1 private (`Proj_map_congr` — an explicit local copy of the same-named private helper in GroupLawConstruction.lean; hoist-and-dedup candidate).

### File Summary — TorsionUnramifiedFibre.lean
- **Totals**: 1462 lines; 64 declarations = 2 private structures (`AugLocPackage`, `EpsHalf`), 10 private noncomputable defs (`axisL`, `axisR`, `foldε`, `pointSharp`, `tautPoint`, `boxIso`, `boxι`, `liftU`, `pairBox`, `chartAug`), 1 private local instance (`chartAlgebra`), 51 theorems/lemmas. Three layers: relocated public Point API (8), pure-algebra augmentation layer (11, all private), scheme/box layer (33, all private), public heads (4).
- **Key API** (public, 12): `formallyUnramified_torsionπ_of_nIsInvertible` (L-BC, the BB-DIFF arithmetic input), `formallyUnramified_torsionπ_of_isUnit` (field case), `point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero` (the augmentation-ideal rigidity core, KM 2.3.1 without differentials), `nIsInvertible_residueField`; plus the relocated Point-arithmetic lemmas `pointEquivOverHom_sub/_restrict`, `restrict_sub/_zero/_add`, `point_add_val_mu`, `point_pair_left_fst/snd` (consumed by MulByHomSmooth in-cluster and by KernelDivisibilityChart/MulByHomUnramified/PatchHopf/DeligneOrder outside).
- **Unused-in-file**: private `specMap_zero_appLE_fromSpec` (:296) and `specMap_π_appLE_fromSpec` (:303) — declared, never referenced (superseded chunk-(i) identities); deletion candidates. All other privates are consumed on the `pointSharp_add` spine.
- **CODE-sorry**: none (the fibre leg is fully proven; the general-`S` head still *inherits* the BB-QF box through `torsionπ_isFinite` from Torsion.lean — an import-level, not in-file, sorry dependency).
- **set_option**: none (heartbeat management is done structurally instead: hoisted tail, opaque `AugLocPackage`/`EpsHalf` localization firewalls, per-constructor "own heartbeat budget" lemmas).
- **Proofs >30 lines**: `pointSharp_add` (254 incl. the 64-line retained EXECUTION LEDGER comment — compress candidate), `pointSharp_add_tail` (168), `point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero` (101), `augLocPackage_exists` (62), `pairBox_boxIso_eq_specMap` (32).
- **Private/public**: 12 public + 52 private.
- **Notes**: stray sibling artifacts `TorsionUnramifiedFibre.lean.full`, `.tail2`, `.tailbody` sit in the same directory (editor/session leftovers, not built) — removal candidates for cleanup.
