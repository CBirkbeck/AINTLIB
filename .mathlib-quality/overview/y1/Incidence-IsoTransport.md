# Phase-1 inventory — LevelStructure/Incidence.lean + LevelStructure/IsoTransport.lean

Overview pass (y1). Files read in full on `main` at
`/Users/mcu22seu/Documents/GitHub/aintlib-main`.

- `projects/ModularCurves/ModularCurves/LevelStructure/Incidence.lean` — 2,753 lines, 144 declarations (106 private / 38 public). The Cartier-incidence representability block (KM 1.3–1.6): vanishing ideals of sections/submodules, the `vanishingLocus` of an ideal sheaf on a finite-locally-free cover, the incidence loci `D' ≤ D` / `D = D'` (KM 1.3.4/1.3.5), the subgroup-divisor locus (KM 1.3.7), and the exact-order (T-D17) and full-level (T-D18) loci.
- `projects/ModularCurves/ModularCurves/LevelStructure/IsoTransport.lean` — 308 lines, 20 declarations (all public). The divisor apparatus transported along a pointed multiplication-compatible isomorphism of elliptic curves (the T-H8a iso-leg), hypothesis-funneled on `hη`/`hμ`.

Project-file tags used in "Uses from project":
`[GroupLaw]` = EllipticCurve/GroupLaw.lean · `[EC.Basic]` = EllipticCurve/Basic.lean (EllipticCurveGeom fields `E`, `π`, `zero`, `zero_π`, `smooth`) · `[Torsion]` = EllipticCurve/Torsion.lean · `[CartierDiv]` = LevelStructure/CartierDivisor.lean · `[LS.Basic]` = LevelStructure/Basic.lean · `[ExactOrder]` = LevelStructure/ExactOrder.lean · `[ForMathlib]` = ForMathlib/IdealSheafComapMul.lean · `(in-file)` = same file.

Verified: `RelEffCartierDiv.IsSubgroup` is defined in ExactOrder.lean:91; `torsionIdeal` in LS.Basic:79; `comap_prod`/`exists_factor_comap_iff` in ForMathlib/IdealSheafComapMul.lean:265/273. `ker_fst_of_isClosedImmersion`, `finite_app`, `Over.μ_pullback_left_fst_fst'/snd'`, `Hom.commGroup`/`Hom.group`/`Hom.one_def`/`Hom.mul_def`, `GrpObj.comp_zpow`, `Scheme.Hom.ker_comp`, `le_ofIdeals_iff`, `comapIso`, `exists_free_localizedModule_powers` are all **mathlib** (checked in `.lake/packages/mathlib`).

---

## File 1: IsoTransport.lean (308 lines)

### `AlgebraicGeometry.Scheme.IdealSheafData.map_hom_eq_comap_inv`
- **Type**: lemma
- **What**: For an isomorphism of schemes `φ : X ≅ Y`, `I.map φ.hom = I.comap φ.inv` for any ideal sheaf `I`.
- **How**: Antisymmetry; `≤` by comap-ing `comap_map_le` along `φ.inv` and cancelling `φ.inv_hom_id` with `comap_comp`/`comap_id`; `≥` via the `map ⊣ comap` Galois connection `map_gc`.
- **Hypotheses**: `φ : X ≅ Y`, `I : X.IdealSheafData`.
- **Uses from project**: [] (mathlib only; generic ideal-sheaf transport).
- **Used by**: `ker_comp_iso`, `torsionIdeal_eq_comap` (in-file).
- **Visibility**: public
- **Lines**: 57–67
- **Notes**: Lives in the `AlgebraicGeometry.Scheme.IdealSheafData` namespace — a ForMathlib-style generic lemma parked in a project file; upstream/move candidate.

### `AlgebraicGeometry.Scheme.Hom.ker_comp_iso`
- **Type**: lemma (`_root_`-qualified)
- **What**: `ker (z ≫ φ.hom) = (ker z).comap φ.inv` for `φ` an isomorphism.
- **How**: `Scheme.Hom.ker_comp` (mathlib) then `map_hom_eq_comap_inv`.
- **Hypotheses**: `z : T ⟶ X`, `φ : X ≅ Y`.
- **Uses from project**: (in-file) `map_hom_eq_comap_inv`.
- **Used by**: `sectionsDivisor_pointMap_ideal` (in-file).
- **Visibility**: public
- **Lines**: 69–74
- **Notes**: generic; upstream candidate.

### `AlgebraicGeometry.Scheme.Hom.ker_iso_comp`
- **Type**: lemma (`_root_`-qualified)
- **What**: Precomposition with an isomorphism `τ` does not change the kernel ideal sheaf: `ker (τ ≫ f) = ker f`.
- **How**: `Scheme.Hom.ker_comp`, `ker_eq_bot_of_isIso`, `map_bot` (all mathlib).
- **Hypotheses**: `[IsIso τ]`.
- **Uses from project**: [].
- **Used by**: `torsionIdeal_eq_comap` (in-file).
- **Visibility**: public
- **Lines**: 76–79
- **Notes**: generic; upstream candidate.

### `ModularCurves.EllipticCurve.one_comp_monHom`
- **Type**: lemma
- **What**: Postcomposition with a pointed morphism `e : E.asOver ⟶ E'.asOver` preserves the `Hom`-group unit: `(1 : A ⟶ E.asOver) ≫ e = 1`.
- **How**: Unfold `Hom.one_def` (mathlib Cartesian/Mon) and rewrite with `hη`.
- **Hypotheses**: `hη : η[E.asOver] ≫ e = η[E'.asOver]`; `A : Over S`.
- **Uses from project**: `EllipticCurve.asOver`, `grp` MonObj instance [GroupLaw].
- **Used by**: [] (unused within these two files).
- **Visibility**: public
- **Lines**: 97–100
- **Notes**: UNUSED in-file — completeness companion of `mul_comp_monHom`; presumably for downstream T-W7a consumers.

### `ModularCurves.EllipticCurve.mul_comp_monHom`
- **Type**: lemma
- **What**: Postcomposition with a multiplication-compatible morphism is multiplicative on `Hom`-groups: `(f * g) ≫ e = (f ≫ e) * (g ≫ e)`.
- **How**: `Hom.mul_def` + `hμ` + `lift_map` (mathlib CartesianMonoidalCategory).
- **Hypotheses**: `hμ : μ[E.asOver] ≫ e = tensorHom e e ≫ μ[E'.asOver]`.
- **Uses from project**: `asOver` [GroupLaw].
- **Used by**: `zpow_comp_monHom`, `pointMapOfHom_add` (in-file).
- **Visibility**: public
- **Lines**: 102–108

### `ModularCurves.EllipticCurve.zpow_comp_monHom`
- **Type**: lemma
- **What**: Postcomposition preserves `Hom`-group integer powers: `(f ^ n) ≫ e = (f ≫ e) ^ n`.
- **How**: Package postcomposition as a `MonoidHom.mk'` from `mul_comp_monHom` and apply `map_zpow`.
- **Hypotheses**: `hμ`; `n : ℤ`.
- **Uses from project**: (in-file) `mul_comp_monHom`; `asOver` [GroupLaw].
- **Used by**: `mulBy_comp_monHom` (in-file).
- **Visibility**: public
- **Lines**: 110–117

### `ModularCurves.EllipticCurve.mulBy_comp_monHom`
- **Type**: lemma
- **What**: The `[n]`-intertwining at `Over S` level: `E.mulBy n ≫ e = e ≫ E'.mulBy n`.
- **How**: Both sides are `e ^ n` in the `Hom`-group: LHS by `zpow_comp_monHom` (needs `hμ`), RHS by mathlib `GrpObj.comp_zpow` (free precomposition).
- **Hypotheses**: `hμ`; `n : ℤ`.
- **Uses from project**: (in-file) `zpow_comp_monHom`; `EllipticCurve.mulBy` [GroupLaw].
- **Used by**: `mulByHom_comp_monHom` (in-file).
- **Visibility**: public
- **Lines**: 119–127

### `ModularCurves.EllipticCurve.mulByHom_comp_monHom`
- **Type**: lemma
- **What**: Scheme-level `[n]`-intertwining: `E.mulByHom n ≫ e.left = e.left ≫ E'.mulByHom n`.
- **How**: `congrArg CommaMorphism.left` on `mulBy_comp_monHom`, unpacked with `Over.comp_left`.
- **Hypotheses**: `hμ`; `n : ℤ`.
- **Uses from project**: (in-file) `mulBy_comp_monHom`; `mulByHom`, `mulBy` [GroupLaw].
- **Used by**: `torsionIdeal_eq_comap` (in-file).
- **Visibility**: public
- **Lines**: 129–135

### `ModularCurves.EllipticCurve.zero_comp_monHom`
- **Type**: lemma
- **What**: Scheme-level pointedness: `E.zero ≫ e.left = E'.zero`.
- **How**: Take `.left` of `hη`, rewrite both units to zero sections via `E.one_eq_zero`/`E'.one_eq_zero`, cancel the epi `𝟙 S`.
- **Hypotheses**: `hη`.
- **Uses from project**: `zero` [EC.Basic], `one_eq_zero` [GroupLaw].
- **Used by**: `torsionIdeal_eq_comap` (in-file).
- **Visibility**: public
- **Lines**: 137–145

### `ModularCurves.EllipticCurve.pointMapOfHom`
- **Type**: noncomputable def
- **What**: Image of a `T`-point under a morphism of curves: `E.Point g → E'.Point g`, `P ↦ P.1 ≫ e.left`.
- **How**: Subtype constructor; over-`S` condition via `Over.w e`.
- **Hypotheses**: `e : E.asOver ⟶ E'.asOver`, `g : T ⟶ S`.
- **Uses from project**: `EllipticCurve.Point` [GroupLaw].
- **Used by**: `pointMapOfHom_coe`, `pointMapOfHom_add`, `pointAddEquiv`, `sectionsDivisor_pointMap_ideal`, `Section.HasExactOrder.pointMap` (in-file).
- **Visibility**: public
- **Lines**: 154–158
- **Notes**: key API of the file (5 in-file users).

### `ModularCurves.EllipticCurve.pointMapOfHom_coe`
- **Type**: @[simp] lemma
- **What**: `(pointMapOfHom e P : T ⟶ E'.E) = P.1 ≫ e.left`.
- **How**: `rfl`.
- **Hypotheses**: —
- **Uses from project**: (in-file) `pointMapOfHom`.
- **Used by**: [] (unused within these files; simp-normal-form lemma).
- **Visibility**: public
- **Lines**: 160–162

### `ModularCurves.EllipticCurve.iso_hom_left_inv_left`
- **Type**: lemma
- **What**: `e.hom.left ≫ e.inv.left = 𝟙 E.E` for an `Over`-isomorphism `e`.
- **How**: `congrArg CommaMorphism.left e.hom_inv_id` unpacked with `Over.comp_left`/`Over.id_left`.
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`.
- **Uses from project**: `asOver` [GroupLaw], `E` field [EC.Basic].
- **Used by**: `pointAddEquiv`, `schemeIsoOfOverIso` (in-file).
- **Visibility**: public
- **Lines**: 164–168

### `ModularCurves.EllipticCurve.iso_inv_left_hom_left`
- **Type**: lemma
- **What**: The other-order composite: `e.inv.left ≫ e.hom.left = 𝟙 E'.E`.
- **How**: as above, from `e.inv_hom_id`.
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`.
- **Uses from project**: `asOver` [GroupLaw].
- **Used by**: `pointAddEquiv`, `schemeIsoOfOverIso` (in-file).
- **Visibility**: public
- **Lines**: 170–174

### `ModularCurves.EllipticCurve.pointMapOfHom_add`
- **Type**: lemma
- **What**: `pointMapOfHom e` is additive on `T`-points when `e` is multiplication-compatible.
- **How**: Transport through the group isomorphism `pointEquivOverHom` (inject via `(E'.pointEquivOverHom g).injective`), rewrite with `pointEquivOverHom_add` on both sides, close with `mul_comp_monHom`; `Hom.commGroup` instances installed by `letI`.
- **Hypotheses**: `hμ`; `P Q : E.Point g`.
- **Uses from project**: (in-file) `pointMapOfHom`, `mul_comp_monHom`; `pointEquivOverHom`, `pointEquivOverHom_add`, `Point` add-group [GroupLaw].
- **Used by**: `pointAddEquiv` (in-file).
- **Visibility**: public
- **Lines**: 176–189
- **Notes**: the `transportSection_add_of_isMonHom` pattern at an arbitrary base point.

### `ModularCurves.EllipticCurve.pointAddEquiv`
- **Type**: @[simps -fullyApplied apply] noncomputable def
- **What**: The additive equivalence `E.Point g ≃+ E'.Point g` induced by a pointed multiplication-compatible isomorphism, at every base point `g : T ⟶ S`.
- **How**: `toFun`/`invFun` are `pointMapOfHom e.hom`/`e.inv`; inverse laws by `iso_hom_left_inv_left`/`iso_inv_left_hom_left` + `Subtype.ext`; additivity is `pointMapOfHom_add`.
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`, `hμ`.
- **Uses from project**: (in-file) `pointMapOfHom`, `pointMapOfHom_add`, `iso_hom_left_inv_left`, `iso_inv_left_hom_left`; `Point` [GroupLaw].
- **Used by**: `IsSubgroup.of_ideal_comap`, `Section.HasExactOrder.pointMap` (in-file).
- **Visibility**: public
- **Lines**: 191–206
- **Notes**: headline point-level result of the file.

### `ModularCurves.EllipticCurve.schemeIsoOfOverIso`
- **Type**: @[simps] noncomputable def
- **What**: The scheme-level isomorphism `E.E ≅ E'.E` underlying an `Over`-isomorphism of curves.
- **How**: components `e.hom.left`/`e.inv.left`; laws are `iso_hom_left_inv_left`/`iso_inv_left_hom_left`.
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`.
- **Uses from project**: (in-file) `iso_hom_left_inv_left`, `iso_inv_left_hom_left`.
- **Used by**: `sectionsDivisor_pointMap_ideal`, `torsionIdeal_eq_comap` (in-file).
- **Visibility**: public
- **Lines**: 217–223

### `ModularCurves.EllipticCurve.sectionsDivisor_pointMap_ideal`
- **Type**: lemma
- **What**: The sections-divisor of the transported family `i ↦ pointMapOfHom e.hom (P i)` has ideal `= (sectionsDivisor E.π P).ideal.comap e.inv.left`.
- **How**: Unfold `RelEffCartierDiv.sectionsDivisor` on both sides via `dif_pos` (feeding `IsSeparated` + `E.smooth`), push `comap` through the finite product with `Scheme.IdealSheafData.comap_prod` [ForMathlib], and match factors by `Scheme.Hom.ker_comp_iso` at `schemeIsoOfOverIso e` (`Finset.prod_congr`).
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`, `P : Fin n → E.Point (𝟙 S)`.
- **Uses from project**: (in-file) `pointMapOfHom`, `schemeIsoOfOverIso`, `Scheme.Hom.ker_comp_iso`; `RelEffCartierDiv.sectionsDivisor` [CartierDiv], `smooth`/`π` [EC.Basic], `Scheme.IdealSheafData.comap_prod` [ForMathlib].
- **Used by**: `Section.HasExactOrder.pointMap` (in-file).
- **Visibility**: public
- **Lines**: 225–241
- **Notes**: unfolds the `dif_pos` branch of `sectionsDivisor` — brittle against changes to that definition.

### `ModularCurves.EllipticCurve.torsionIdeal_eq_comap`
- **Type**: lemma
- **What**: `E'.torsionIdeal N = (E.torsionIdeal N).comap e.inv.left`: the `N`-torsion ideal transports along a pointed multiplication-compatible isomorphism.
- **How**: Reduce comap-along-inv to map-along-hom (`map_hom_eq_comap_inv`); both torsion ideals are kernels of `torsionι` (definition [LS.Basic]); match the two kernel pullbacks with `pullback.map` built from the `[N]`-intertwining `mulByHom_comp_monHom` (hsq) and pointedness `zero_comp_monHom` (hz); that comparison map is an iso (`pullback.map_isIso`, mathlib), so `Scheme.Hom.ker_iso_comp` finishes.
- **Hypotheses**: `e : E.asOver ≅ E'.asOver`, `hη`, `hμ`, `N : ℕ`.
- **Uses from project**: (in-file) `schemeIsoOfOverIso`, `map_hom_eq_comap_inv`, `mulByHom_comp_monHom`, `zero_comp_monHom`, `Scheme.Hom.ker_iso_comp`; `torsionIdeal` [LS.Basic], `torsionι` [Torsion], `mulByHom` [GroupLaw], `zero` [EC.Basic].
- **Used by**: [] (unused within these files — terminal API for the T-H8a Drinfeld `map` membership).
- **Visibility**: public
- **Lines**: 243–269
- **Notes**: proof 19 lines; listed in "Main results".

### `ModularCurves.RelEffCartierDiv.IsSubgroup.of_ideal_comap`
- **Type**: lemma (`_root_`-qualified into `RelEffCartierDiv.IsSubgroup` namespace)
- **What**: If `D'.ideal = D.ideal.comap e.inv.left` and `D` is a subgroup divisor of `E`, then `D'` is a subgroup divisor of `E'`.
- **How**: At each `g : T ⟶ S`, pull the witnessing `AddSubgroup` back along `(pointAddEquiv e hμ g).symm`; membership dictionary via `Scheme.IdealSheafData.exists_factor_comap_iff` [ForMathlib].
- **Hypotheses**: `e`, `hμ`, `hI : D'.ideal = D.ideal.comap e.inv.left`, `hD : D.IsSubgroup E`.
- **Uses from project**: (in-file) `pointAddEquiv`; `RelEffCartierDiv` [CartierDiv], `RelEffCartierDiv.IsSubgroup` [ExactOrder], `exists_factor_comap_iff` [ForMathlib].
- **Used by**: `Section.HasExactOrder.pointMap` (in-file).
- **Visibility**: public
- **Lines**: 271–286
- **Notes**: pointedness (`hη`) not needed.

### `ModularCurves.EllipticCurve.Section.HasExactOrder.pointMap`
- **Type**: theorem
- **What**: **Exact order transports along a multiplication-compatible isomorphism** (IsGammaOne iso-leg): if `P` has exact order `N` on `E`, then `pointMapOfHom e.hom P` has exact order `N` on `E'`.
- **How**: Unfold `HasExactOrder` to `IsSubgroup` of the order divisor; apply `IsSubgroup.of_ideal_comap`; the required ideal identity comes from rewriting `orderDivisor` as a `sectionsDivisor` of the multiples, commuting `pointMapOfHom` past `zsmul` via `map_zsmul (pointAddEquiv e hμ (𝟙 S))`, and closing with `sectionsDivisor_pointMap_ideal`.
- **Hypotheses**: `e`, `hμ`, `P : E.Section`, `[NeZero N]`, `h : P.HasExactOrder E N`.
- **Uses from project**: (in-file) `pointMapOfHom`, `pointAddEquiv`, `IsSubgroup.of_ideal_comap`, `sectionsDivisor_pointMap_ideal`; `Section.HasExactOrder`, `Section.orderDivisor`, `Section` [ExactOrder].
- **Used by**: [] (terminal API).
- **Visibility**: public
- **Lines**: 288–302
- **Notes**: module docstring advertises this as `Section.HasExactOrder.comp_iso` — **name mismatch** between doc ("Main results" bullet) and the actual declaration name `pointMap`.

---

## File 2: Incidence.lean (2,753 lines)

### `ModularCurves.sectionVanishingIdeal`
- **Type**: def
- **What**: The vanishing ideal of `σ : M` in an `R`-module: `Ideal.span (range fun φ : Dual R M => φ σ)`. `V(·) ⊆ Spec R` is the zero locus of the section; junk-`⊥` for modules with trivial dual.
- **How**: —
- **Hypotheses**: `(R M)` explicit; `[CommRing R] [AddCommGroup M] [Module R M]`.
- **Uses from project**: [].
- **Used by**: `sectionVanishingIdeal_eq_span_coord`, `_eq_span_coord_coord`, `submoduleVanishingIdeal`, `sectionVanishingIdeal_le_submoduleVanishingIdeal`, `sectionVanishingIdeal_fg`, `submoduleVanishingIdeal_fg`, `vanishingLocusAux_svi_le_ker_iff`, `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: public
- **Lines**: 60–61
- **Notes**: key API (8 in-file users). KM 1.3.5 engine.

### `ModularCurves.sectionVanishingIdeal_eq_span_coord`
- **Type**: theorem — (T-D13, basis form)
- **What**: For a basis `b` of `M`, the vanishing ideal of `σ` is spanned by the coordinates `b.coord i σ` alone.
- **How**: `Submodule.span_eq_span` in both directions; any `φ σ` expands as `∑ i ∈ (b.repr σ).support, b.repr σ i * φ (b i)` via `b.linearCombination_repr` and lands in the coordinate span.
- **Hypotheses**: `b : Module.Basis ι R M`, `σ : M`.
- **Uses from project**: (in-file) `sectionVanishingIdeal`.
- **Used by**: `sectionVanishingIdeal_eq_span_coord_coord`, `vanishingLocusAux_svi_le_ker_iff` (in-file).
- **Visibility**: public
- **Lines**: 71–78
- **Notes**: docstring records the 2026-07-06 ADVERSARIAL FIX replacing a tautological ∀-functional form.

### `ModularCurves.sectionVanishingIdeal_eq_span_coord_coord`
- **Type**: theorem — (T-D27, tower descent)
- **What**: For `M` a `B`-module over an `R`-algebra `B` (scalar tower), the `R`-vanishing ideal is spanned by `R`-coordinates of `B`-coordinates (KM 1.3.7's `(deg D)²`-equations descent from `W = D ×_S D`).
- **How**: One-liner: apply `sectionVanishingIdeal_eq_span_coord` to the composite basis `c.smulTower b` (mathlib).
- **Hypotheses**: `[Algebra R B] [Module B M] [IsScalarTower R B M]`, bases `c : Basis κ R B`, `b : Basis ι B M`.
- **Uses from project**: (in-file) `sectionVanishingIdeal_eq_span_coord`.
- **Used by**: [] (unused within these files).
- **Visibility**: public
- **Lines**: 85–89
- **Notes**: UNUSED in-file — the vanishing-locus development went through the basis-free `submoduleVanishingIdeal` route instead; dead-code / doc-value check.

### `ModularCurves.forall_one_tmul_eq_zero_iff_span_coord_le_ker`
- **Type**: theorem — (T-D14c, base-change vanishing bridge)
- **What**: For a free `R`-algebra `B` with basis `b` and elements `g : κ → B`: all `1 ⊗ₜ g j` vanish in `A ⊗[R] B` iff the ideal of all coordinates `b.coord i (g j)` lies in `ker (algebraMap R A)`.
- **How**: Read coordinates of the base-changed tensor through `Module.Basis.baseChange_repr_tmul` (mathlib); forward by `congrArg` of the repr, backward by injectivity of `(b.baseChange A).repr` and `Finsupp.ext`. 14-line proof.
- **Hypotheses**: `[CommRing A] [CommRing B] [Algebra R A] [Algebra R B]`, `b : Basis ι R B`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_svi_le_ker_iff` (in-file).
- **Visibility**: public
- **Lines**: 97–116

### `ModularCurves.submoduleVanishingIdeal`
- **Type**: def
- **What**: Vanishing ideal of a submodule `J ≤ M`: `⨆ g : J, sectionVanishingIdeal R M g` — the basis-free global form of KM 1.3.4's coordinates that makes the incidence locus glue.
- **How**: —
- **Hypotheses**: `(R M)` explicit, `J : Submodule R M`.
- **Uses from project**: (in-file) `sectionVanishingIdeal`.
- **Used by**: `sectionVanishingIdeal_le_submoduleVanishingIdeal`, `apply_mem_submoduleVanishingIdeal`, `submoduleVanishingIdeal_fg`, `submoduleVanishingIdeal_localized`, `vanishingLocus`, `vanishingLocusAux_ideal_le_ker`, `vanishingLocus_subschemeι_lfp` (in-file).
- **Visibility**: public
- **Lines**: 130–131
- **Notes**: key API (7 in-file users).

### `ModularCurves.sectionVanishingIdeal_le_submoduleVanishingIdeal`
- **Type**: theorem
- **What**: `g ∈ J ⟹ sectionVanishingIdeal R M g ≤ submoduleVanishingIdeal R M J`.
- **How**: `le_iSup` at `⟨g, hg⟩`.
- **Hypotheses**: `hg : g ∈ J`.
- **Uses from project**: (in-file) `sectionVanishingIdeal`, `submoduleVanishingIdeal`.
- **Used by**: `apply_mem_submoduleVanishingIdeal`, `submoduleVanishingIdeal_fg`, `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: public
- **Lines**: 133–136
- **Notes**: key API (3 users).

### `ModularCurves.apply_mem_submoduleVanishingIdeal`
- **Type**: theorem
- **What**: `g ∈ J ⟹ φ g ∈ submoduleVanishingIdeal R M J` for every functional `φ`.
- **How**: previous lemma + `Ideal.subset_span`.
- **Hypotheses**: `hg : g ∈ J`, `φ : Dual R M`.
- **Uses from project**: (in-file) `sectionVanishingIdeal_le_submoduleVanishingIdeal`.
- **Used by**: `submoduleVanishingIdeal_localized` (in-file, twice).
- **Visibility**: public
- **Lines**: 138–140

### `ModularCurves.sectionVanishingIdeal_fg`
- **Type**: theorem — ([T-SG3-LFP-1])
- **What**: Over a finite projective module, the vanishing ideal of a section is finitely generated (generated by the `n` free coordinates after splitting off `R^n`).
- **How**: Split via `Module.Finite.exists_fin'` + `Module.projective_lifting_property` (section `s` of the surjection `p`); generators are `s σ i`; the reverse inclusion expands `φ σ = ∑ i, s σ i * (φ ∘ p)(δᵢ)` by `LinearMap.pi_apply_eq_sum_univ`. 21-line proof.
- **Hypotheses**: `[Module.Finite R M] [Module.Projective R M]`.
- **Uses from project**: (in-file) `sectionVanishingIdeal`.
- **Used by**: `submoduleVanishingIdeal_fg` (in-file).
- **Visibility**: public
- **Lines**: 146–168
- **Notes**: `classical` in proof.

### `ModularCurves.submoduleVanishingIdeal_fg`
- **Type**: theorem — ([T-SG3-LFP-2])
- **What**: Over a finite projective module, the vanishing ideal of a f.g. submodule is f.g. (finite sup of the generators' vanishing ideals).
- **How**: Key claim: `submoduleVanishingIdeal = tset.sup (sectionVanishingIdeal · )` for a generating finset, proven by `Submodule.span_induction` on span membership (values of functionals are ideal-stable under `+`, `•`); then `Finset.induction_on` with `Submodule.FG.sup` and `sectionVanishingIdeal_fg`.
- **Hypotheses**: `[Module.Finite R M] [Module.Projective R M]`, `hJ : J.FG`.
- **Uses from project**: (in-file) `submoduleVanishingIdeal`, `sectionVanishingIdeal`, `sectionVanishingIdeal_le_submoduleVanishingIdeal`, `sectionVanishingIdeal_fg`.
- **Used by**: `vanishingLocus_subschemeι_lfp` (in-file).
- **Visibility**: public
- **Lines**: 173–210
- **Notes**: **proof 36 lines (>30)**; `classical`.

### `ModularCurves.submoduleVanishingIdeal_localized`
- **Type**: theorem — (T-D14c-0, gluing keystone)
- **What**: For `M` finitely presented, `(submoduleVanishingIdeal R M J).map (algebraMap R Rₛ) = submoduleVanishingIdeal Rₛ Nₛ (J.localized' Rₛ S f)` — vanishing ideals commute with localization.
- **How**: `≤`: functionals extend along localization by `IsLocalizedModule.mapExtendScalars` (uses `Module.FinitePresentation.isLocalizedModule_mapExtendScalars`, mathlib); `≥`: clear denominators with `IsLocalizedModule.surj` and `IsLocalization.map_units` (`Ideal.unit_mul_mem_iff_mem`), landing in the image by `apply_mem_submoduleVanishingIdeal`. Proof exactly 30 lines.
- **Hypotheses**: `S : Submonoid R`, `[IsLocalization S Rₛ]`, `f : M →ₗ[R] Nₛ` `[IsLocalizedModule S f]`, `[Module.FinitePresentation R M]`.
- **Uses from project**: (in-file) `submoduleVanishingIdeal`, `apply_mem_submoduleVanishingIdeal`.
- **Used by**: `vanishingLocus` (in-file).
- **Visibility**: public
- **Lines**: 217–252
- **Notes**: borderline-long proof (30 lines).

### `ModularCurves.localized'_restrictScalars_eq_restrictScalars_map`
- **Type**: theorem
- **What**: Tower version of `Ideal.localized'_eq_map`: `Submodule.localized' Rf S (toAlgHom R A Af) (J.restrictScalars R) = (J.map (algebraMap A Af)).restrictScalars Rf`.
- **How**: `ext` + `Submodule.mem_localized'` vs `IsLocalization.mem_map_algebraMap_iff`; both directions clear denominators with `mk'_cancel'` / `mk'_eq_iff`. 18-line proof.
- **Hypotheses**: two-ring tower `R → Rf`, `A → Af` with `[IsLocalization S Rf]`, `[IsLocalization (algebraMapSubmonoid A S) Af]`, `[IsLocalizedModule S (toAlgHom R A Af).toLinearMap]`.
- **Uses from project**: [].
- **Used by**: `vanishingLocus` (in-file).
- **Visibility**: public
- **Lines**: 258–286
- **Notes**: generic commutative algebra; upstream candidate.

### `ModularCurves.lfp_subschemeι_of_fg_cover`
- **Type**: theorem — ([T-SG3-LFP-3], cover form)
- **What**: If the ideal sheaf of a closed subscheme is f.g. on each member of one affine cover, then `Z.subschemeι` is locally of finite presentation.
- **How**: `IsZariskiLocalAtTarget.of_iSup_eq_top`; over each affine, rewrite the restricted morphism ring-map through `HasRingHomProperty.iff_of_isAffine` + `resLE`/`appLE` shuffles, then `RingHom.FinitePresentation.of_surjective` with the surjection `Z.subschemeι.app` and kernel `Z.ideal` (`Scheme.Hom.ker_apply`, `ker_subschemeι`). 15-line proof.
- **Hypotheses**: `U : ι → S.affineOpens`, `hU : ⨆ i, (U i).1 = ⊤`, `h : ∀ i, (Z.ideal (U i)).FG`.
- **Uses from project**: [].
- **Used by**: `lfp_subschemeι_of_fg` (in-file).
- **Visibility**: public
- **Lines**: 295–313

### `ModularCurves.lfp_subschemeι_of_fg`
- **Type**: theorem — ([T-SG3-LFP-3])
- **What**: All-affines form: ideal f.g. on every affine ⟹ `subschemeι` lfp.
- **How**: previous with the tautological cover (`iSup_affineOpens_eq_top`).
- **Hypotheses**: `h : ∀ U : S.affineOpens, (Z.ideal U).FG`.
- **Uses from project**: (in-file) `lfp_subschemeι_of_fg_cover`.
- **Used by**: `vanishingLocus_subschemeι_lfp` (in-file).
- **Visibility**: public
- **Lines**: 317–320

### `ModularCurves.affinePreimage`
- **Type**: def
- **What**: The preimage `p ⁻¹ᵁ U` of an affine open under a finite (hence affine) morphism, packaged as an affine open.
- **How**: `U.2.preimage p`.
- **Hypotheses**: section variables `p : W ⟶ S` `[IsFinite p] [Flat p] [LocallyOfFinitePresentation p]`.
- **Uses from project**: [].
- **Used by**: `vanishingLocus_subschemeι_lfp` (in-file).
- **Visibility**: public
- **Lines**: 329–330
- **Notes**: `vanishingLocus` itself re-spells the same subtype literally (`⟨p ⁻¹ᵁ U.1, U.2.preimage p⟩`) instead of using this def — consistency cleanup.

### `ModularCurves.vanishingLocus`
- **Type**: noncomputable def — (T-D14c-1)
- **What**: The vanishing locus on `S` of an ideal sheaf `E` on `W` finite locally free over `S`: over affine `U`, the ideal is `submoduleVanishingIdeal Γ(S,U) Γ(W,p⁻¹U) (E.ideal(p⁻¹U)).restrictScalars`. KM 1.3.4's "simultaneous vanishing of coordinates", basis-free.
- **How**: The `map_ideal_basicOpen` compatibility field is a 57-line proof: install algebra towers with `RingHom.algebraMap_toAlgebra` + `Scheme.Hom.appLE` simp identities; get `Module.FinitePresentation` from `p.finite_app` + `HasRingHomProperty.appLE @LocallyOfFinitePresentation`; identify `Γ(W, p⁻¹D(f))` as the localized module via `IsAffineOpen.isLocalization_of_eq_basicOpen` + `Submonoid.map_powers`; then apply `submoduleVanishingIdeal_localized` and rewrite by `localized'_restrictScalars_eq_restrictScalars_map` + `E.map_ideal'`.
- **Hypotheses**: section variables (`p` finite flat lfp), `E : W.IdealSheafData`.
- **Uses from project**: (in-file) `submoduleVanishingIdeal`, `submoduleVanishingIdeal_localized`, `localized'_restrictScalars_eq_restrictScalars_map`.
- **Used by**: `vanishingLocusAux_ideal_le_ker`, `vanishingLocusAux_le_tker`, `vanishingLocus_le_ker_iff`, `vanishingLocus_subschemeι_lfp`, `exists_incidenceLocusLE`, `subgroupLocusAux_Z3` (+ `subgroupLocusAux_Z3_le_ker_iff` via `show`) (in-file).
- **Visibility**: public
- **Lines**: 338–399
- **Notes**: **field proof 57 lines (>30)**; key API (6+ users); central construction of the file.

### `ModularCurves.exists_affineOpen_mem_free`
- **Type**: theorem — (T-D14c-i, free cover)
- **What**: A finite flat finitely-presented morphism has free pushforward sections over an affine neighbourhood of every point.
- **How**: Start from any affine `U₀ ∋ s` (`isBasis_affineOpens`); `Γ(W,p⁻¹U₀)` is finite flat f.p. over `Γ(S,U₀)` (via `finite_app`, `HasRingHomProperty.appLE`); free over the local ring at `s` by `Module.free_of_flat_of_isLocalRing`; spread to a basic open `D(r)` by `Module.FinitePresentation.exists_free_localizedModule_powers` (mathlib); membership via `fromSpec_preimage_basicOpen`/`fromSpec_primeIdealOf`; finally transport freeness along the canonical `IsLocalizedModule.iso` composed with `IsLocalization.algEquiv`, packaged as a semilinear equiv for `Module.Free.iff_of_equiv` (with `RingHomInvPair.of_ringEquiv`).
- **Hypotheses**: section variables; `s : S`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: public
- **Lines**: 404–496
- **Notes**: **proof 89 lines (>30)**. Near-duplicate of `vanishingLocusAux_exists_basicOpen_free` (see below) — consolidation target.

### `ModularCurves.le_ker_iff_forall`
- **Type**: theorem
- **What**: `I ≤ f.ker ↔ ∀ U affine, I.ideal U ≤ RingHom.ker (f.app U)` — pointwise over all affines, no quasi-compactness.
- **How**: exactly mathlib `Scheme.IdealSheafData.le_ofIdeals_iff` (`ker` is an `ofIdeals`-closure).
- **Hypotheses**: `I : Y.IdealSheafData`, `f : X ⟶ Y`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_ideal_le_ker`, `vanishingLocusAux_le_tker`, `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: public
- **Lines**: 500–502
- **Notes**: key API (3 users); thin alias over mathlib.

### `ModularCurves.vanishingLocusAux_section_eq_zero`
- **Type**: private theorem
- **What**: A section over `U₀` vanishing near every point of `U₀` is zero (sheaf-injectivity workhorse).
- **How**: `choose` the neighbourhoods, apply `X.sheaf.eq_of_locally_eq'` against `0`.
- **Hypotheses**: `h : ∀ q ∈ U₀, ∃ V ≤ U₀, q ∈ V ∧ x|_V = 0`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_ideal_le_ker`, `vanishingLocusAux_le_tker`, `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: private
- **Lines**: 506–517
- **Notes**: key aux (3 users).

### `ModularCurves.vanishingLocusAux_svi_le_ker_iff`
- **Type**: private theorem
- **What**: Algebraic core over a free piece: `sectionVanishingIdeal R A a ≤ ker (algebraMap R C) ↔ 1 ⊗ₜ a = 0` in `C ⊗[R] A`.
- **How**: The `PUnit`-instance of `forall_one_tmul_eq_zero_iff_span_coord_le_ker` at `Module.Free.chooseBasis`, after rewriting with `sectionVanishingIdeal_eq_span_coord`; 12-line proof shuffling the two span presentations.
- **Hypotheses**: `[Module.Free R A]`, `a : A`.
- **Uses from project**: (in-file) `forall_one_tmul_eq_zero_iff_span_coord_le_ker`, `sectionVanishingIdeal_eq_span_coord`, `sectionVanishingIdeal`.
- **Used by**: `vanishingLocusAux_ideal_le_ker`, `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: private
- **Lines**: 524–539

### `ModularCurves.vanishingLocusAux_exists_basicOpen_free`
- **Type**: private theorem
- **What**: Basic-open refinement of `exists_affineOpen_mem_free`: inside a *fixed* affine `U` and around `s ∈ U` there is `r : Γ(S,U)` with `s ∈ D(r)` and free sections over `D(r)`.
- **How**: Same argument as `exists_affineOpen_mem_free` verbatim (docstring says "Same proof, but keeping the ambient affine `U` fixed"): `Module.free_of_flat_of_isLocalRing`, `Module.FinitePresentation.exists_free_localizedModule_powers`, transport along `IsLocalizedModule.iso`/`IsLocalization.algEquiv` via `Module.Free.iff_of_equiv`.
- **Hypotheses**: section variables; `U : S.affineOpens`, `hs : s ∈ U.1`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_le_tker` (in-file).
- **Visibility**: private
- **Lines**: 545–636
- **Notes**: **proof ~87 lines (>30)**; ~90 lines duplicated with `exists_affineOpen_mem_free` — prime decompose/dedup target (extract the shared "freeness spreads to a basic open + transport" core).

### `ModularCurves.vanishingLocusAux_appLE_top`
- **Type**: private theorem
- **What**: `f.appLE ⊤ ⊤ e = f.appTop`.
- **How**: `Scheme.Hom.appLE_eq_app`.
- **Hypotheses**: `e : ⊤ ≤ f ⁻¹ᵁ ⊤`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_one_tmul_eq_zero` (in-file).
- **Visibility**: private
- **Lines**: 639–642

### `ModularCurves.vanishingLocusAux_appLE_snd_eq_zero`
- **Type**: private theorem
- **What**: "Algebra ⇒ geometry": if `a : Γ(W,D)` dies in `Γ(T,V) ⊗ Γ(W,D)`, its pullback to the piece `fst⁻¹V ⊓ snd⁻¹D` of `T ×ₛ W` vanishes.
- **How**: Pure naturality — the coordinate ring of the piece receives `Algebra.TensorProduct.productMap` of the two `IsScalarTower.toAlgHom`s (towers installed via `Scheme.Hom.appLE_comp_appLE` + `pullback.condition`); apply it to `h` and simplify `productMap_apply_tmul`. 27-line proof.
- **Hypotheses**: `omit [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]`; `eV : V ≤ t⁻¹U`, `eD : D ≤ p⁻¹U`, `h : 1 ⊗ₜ a = 0`.
- **Uses from project**: [].
- **Used by**: `vanishingLocusAux_le_ker_snd` (in-file).
- **Visibility**: private
- **Lines**: 651–685

### `ModularCurves.vanishingLocusAux_one_tmul_eq_zero`
- **Type**: private theorem
- **What**: "Geometry ⇒ algebra": if the pullback of `a : Γ(W,p⁻¹U)` to `fst⁻¹V ⊆ T ×ₛ W` vanishes, then `1 ⊗ₜ a = 0` in `Γ(T,V) ⊗ Γ(W,p⁻¹U)`.
- **How**: Genuinely uses the pullback square: build `θ : Spec (Γ(T,V) ⊗ Γ(W,p⁻¹U)) ⟶ T ×ₛ W` by `pullback.lift` of the two `fromSpec`-legs (commutativity via `IsAffineOpen.SpecMap_appLE_fromSpec`); the key computation `appLE ≫ θ.appLE ≫ ΓSpecIso.hom = includeRight` recovers the tensor (`Scheme.ΓSpecIso_naturality`, `vanishingLocusAux_appLE_top`); evaluate at `a`.
- **Hypotheses**: `eV`, `e'`, `h : ((pullback.snd t p).appLE …) a = 0`.
- **Uses from project**: (in-file) `vanishingLocusAux_appLE_top`.
- **Used by**: `vanishingLocusAux_ideal_le_ker` (in-file).
- **Visibility**: private
- **Lines**: 694–736
- **Notes**: **proof 35 lines (>30)**.

### `ModularCurves.vanishingLocusAux_ideal_le_ker`
- **Type**: private theorem
- **What**: Direction "⇐" over a *free* chart: `E ≤ (pullback.snd t p).ker` ⟹ `(vanishingLocus p E).ideal U ≤ ker (t.app U)` when the sections over `U` are free.
- **How**: For each generator `g` and each point `q` of `t⁻¹U`, pick an affine `V ∋ q`; `g` dies on the base change (`le_ker_iff_forall` on `hE`), so `1 ⊗ₜ g = 0` by `vanishingLocusAux_one_tmul_eq_zero`, so the vanishing ideal is killed by `vanishingLocusAux_svi_le_ker_iff`; glue by `vanishingLocusAux_section_eq_zero`. 28-line proof.
- **Hypotheses**: `omit [Flat p]`; `hE`, `hfree`.
- **Uses from project**: (in-file) `vanishingLocus`, `submoduleVanishingIdeal` (via `show`), `le_ker_iff_forall`, `vanishingLocusAux_section_eq_zero`, `vanishingLocusAux_one_tmul_eq_zero`, `vanishingLocusAux_svi_le_ker_iff`.
- **Used by**: `vanishingLocusAux_le_tker` (in-file).
- **Visibility**: private
- **Lines**: 742–774

### `ModularCurves.vanishingLocusAux_le_tker`
- **Type**: private theorem
- **What**: Direction "⇐" of the universal property: `E ≤ (pullback.snd t p).ker ⟹ vanishingLocus p E ≤ t.ker` (arbitrary affines).
- **How**: Reduce an arbitrary affine `U` to a free basic open `D(r)` (`vanishingLocusAux_exists_basicOpen_free`) using quasi-coherence `(vanishingLocus p E).map_ideal`; apply the free-chart case `vanishingLocusAux_ideal_le_ker`; glue with `vanishingLocusAux_section_eq_zero` and `Scheme.Hom.map_appLE`. 25-line proof.
- **Hypotheses**: `hE : E ≤ (pullback.snd t p).ker`.
- **Uses from project**: (in-file) `le_ker_iff_forall`, `vanishingLocusAux_section_eq_zero`, `vanishingLocusAux_exists_basicOpen_free`, `vanishingLocus`, `vanishingLocusAux_ideal_le_ker`.
- **Used by**: `vanishingLocus_le_ker_iff` (in-file).
- **Visibility**: private
- **Lines**: 779–805

### `ModularCurves.vanishingLocusAux_le_ker_snd`
- **Type**: private theorem
- **What**: Direction "⇒": `vanishingLocus p E ≤ t.ker ⟹ E ≤ (pullback.snd t p).ker`.
- **How**: For a section `g` of `E.ideal Vw` and a point `q` of the fibre product: choose the free chart `U ∋ p(snd q)` (`exists_affineOpen_mem_free`), refine to a basic open `D(f) ⊆ Vw ⊓ p⁻¹U` (`IsAffineOpen.exists_basicOpen_le`) and an affine `V ∋ fst q` in `t⁻¹U`; every generator of `E.ideal (p⁻¹U)` dies in `Γ(T,V) ⊗ Γ(W,D(f))` (via `sectionVanishingIdeal_le_submoduleVanishingIdeal` + `vanishingLocusAux_svi_le_ker_iff` + `Algebra.TensorProduct.map`); `g|_{D(f)}` is a combination (`E.map_ideal` + `Submodule.span_induction`); push into the fibre-product piece with `vanishingLocusAux_appLE_snd_eq_zero`; glue with `vanishingLocusAux_section_eq_zero`.
- **Hypotheses**: `hZ : vanishingLocus p E ≤ t.ker`.
- **Uses from project**: (in-file) `le_ker_iff_forall`, `vanishingLocusAux_section_eq_zero`, `exists_affineOpen_mem_free`, `sectionVanishingIdeal_le_submoduleVanishingIdeal`, `sectionVanishingIdeal`, `vanishingLocusAux_svi_le_ker_iff`, `vanishingLocusAux_appLE_snd_eq_zero`.
- **Used by**: `vanishingLocus_le_ker_iff` (in-file).
- **Visibility**: private
- **Lines**: 813–900
- **Notes**: **proof 86 lines (>30)**; the hardest glue of the T-D14c block.

### `ModularCurves.vanishingLocus_le_ker_iff`
- **Type**: theorem — (T-D14c-2, universal property)
- **What**: `vanishingLocus p E ≤ t.ker ↔ E.comap (pullback.snd t p) = ⊥`: `T → S` kills the vanishing locus iff `E` pulls back to zero on the base change. The whole content of KM 1.3.4.
- **How**: Galois reduction `(map_gc _).l_eq_bot` + `map_bot`, then the two aux directions `vanishingLocusAux_le_ker_snd` / `vanishingLocusAux_le_tker`.
- **Hypotheses**: section variables; `t : T ⟶ S`.
- **Uses from project**: (in-file) `vanishingLocus`, `vanishingLocusAux_le_ker_snd`, `vanishingLocusAux_le_tker`.
- **Used by**: `exists_incidenceLocusLE`, `subgroupLocusAux_Z3_le_ker_iff` (in-file).
- **Visibility**: public
- **Lines**: 907–912
- **Notes**: headline of the VanishingLocus section.

### `ModularCurves.vanishingLocus_subschemeι_lfp`
- **Type**: theorem — ([T-SG3-LFP-4a])
- **What**: If `E` is affine-locally f.g. on `W`, then `(vanishingLocus p E).subschemeι` is locally of finite presentation ("defined locally by finitely many equations").
- **How**: Via `lfp_subschemeι_of_fg`; over each affine, `Γ(W,p⁻¹U)` is finite projective over `Γ(S,U)` (`finite_app`, `HasRingHomProperty.appLE @Flat`, `Module.Flat.projective_of_finitePresentation`), the restricted ideal is a finite module by `Module.Finite.trans`, so `submoduleVanishingIdeal_fg` applies. 25-line proof.
- **Hypotheses**: `hE : ∀ U : W.affineOpens, (E.ideal U).FG`.
- **Uses from project**: (in-file) `lfp_subschemeι_of_fg`, `vanishingLocus`, `submoduleVanishingIdeal`, `submoduleVanishingIdeal_fg`, `affinePreimage`.
- **Used by**: [] (unused within these files).
- **Visibility**: public
- **Lines**: 917–943
- **Notes**: UNUSED in-file — the KM "finitely many equations" clause, awaiting downstream lfp consumers (e.g. representability-by-lfp-subscheme statements).

### `ModularCurves.RelEffCartierDiv.IsSubdivisor`
- **Type**: def
- **What**: `D' ≤ D` for effective divisors: the closed subscheme of `D'` factors through that of `D` (over `C`).
- **How**: `∃ j, j ≫ D.ideal.subschemeι = D'.ideal.subschemeι`.
- **Hypotheses**: `D' D : RelEffCartierDiv π`.
- **Uses from project**: `RelEffCartierDiv` [CartierDiv].
- **Used by**: `isSubdivisor_iff_le`, `exists_incidenceLocusLE`, `exists_incidenceLocusEQ`, `subgroupLocusAux_Z3W_spec`, `subgroupLocusAux_Z1_iff`, `subgroupLocusAux_Z2_iff`, `subgroupLocusAux_Z3_le_ker_iff` (in-file).
- **Visibility**: public
- **Lines**: 959–961
- **Notes**: key API (7 users).

### `ModularCurves.RelEffCartierDiv.isSubdivisor_iff_le`
- **Type**: theorem — (T-D14a)
- **What**: `IsSubdivisor D' D ↔ D.ideal ≤ D'.ideal` (KM 1.3.1's `I(D) ⊆ I(D')` dictionary).
- **How**: Forward: `j.le_ker_comp` + `ker_subschemeι` twice; backward: `Scheme.IdealSheafData.inclusion` + `inclusion_subschemeι` (mathlib).
- **Hypotheses**: `D' D : RelEffCartierDiv π`.
- **Uses from project**: (in-file) `IsSubdivisor`; `RelEffCartierDiv` [CartierDiv].
- **Used by**: `exists_incidenceLocusLE`, `subgroupLocusAux_Z1_iff`, `subgroupLocusAux_Z2_iff`, `subgroupLocusAux_Z3_le_ker_iff`, `exists_fullLevelLocus` (in-file).
- **Visibility**: public
- **Lines**: 966–974
- **Notes**: key API (5 users).

### `ModularCurves.exists_factor_subschemeι_iff`
- **Type**: theorem (`_root_`) — (T-D14a′)
- **What**: `(∃ h, h ≫ Z.subschemeι = t) ↔ Z ≤ t.ker` — object-level unpacking of mathlib's `kerAdjunction` in the form the incidence loci consume.
- **How**: Forward: `h.le_ker_comp`; backward: factor through the scheme-theoretic image via `t.toImage ≫ inclusion hZ` (`Scheme.Hom.toImage_imageι`).
- **Hypotheses**: `Z : S.IdealSheafData`, `t : T ⟶ S`.
- **Uses from project**: [].
- **Used by**: `exists_incidenceLocusLE`, `exists_incidenceLocusEQ`, `subgroupLocusAux_factors_iff`, `exists_subgroupLocus` (in-file).
- **Visibility**: public
- **Lines**: 980–989
- **Notes**: key API (4 users).

### `ModularCurves.RelEffCartierDiv.incidenceAux_comap_eq_bot_iff`
- **Type**: private theorem
- **What**: For `e : X ≅ Y` with `e.hom ≫ g = f`: `I.comap f = ⊥ ↔ I.comap g = ⊥` — aligns two fibre-product presentations of `D'_T`.
- **How**: rewrite `g = e.inv ≫ f`, `comap_comp` + `comap_bot`.
- **Hypotheses**: `hfg : e.hom ≫ g = f`.
- **Uses from project**: [].
- **Used by**: `exists_incidenceLocusLE` (in-file).
- **Visibility**: private
- **Lines**: 994–1002

### `ModularCurves.RelEffCartierDiv.exists_incidenceLocusLE`
- **Type**: theorem — (T-D14 = KM 1.3.4, incidence `≤`)
- **What**: For a separated smooth relative curve and effective divisors `D, D'` (`D'` finite/flat/lfp), there is `Z : S.IdealSheafData` with: `t` factors through `Z.subscheme` iff `D'_T ≤ D_T`, for all `t : T ⟶ S`.
- **How**: Witness `Z := vanishingLocus (D'.ideal.subschemeι ≫ π) (D.ideal.comap D'.ideal.subschemeι)`. Rewrite the factoring by `exists_factor_subschemeι_iff` + `vanishingLocus_le_ker_iff`, the subdivisor relation by `isSubdivisor_iff_le` + `baseChange_ideal`; a Galois step (`map_gc.l_eq_bot`, `ker_fst_of_isClosedImmersion`) converts `≤` into `comap ⊥`-vanishing on the base-changed `D'`; finally align the two fibre products by `pullbackSymmetry ≪≫ pullbackRightPullbackFstIso ≪≫ pullbackSymmetry` via `incidenceAux_comap_eq_bot_iff`. 20-line proof.
- **Hypotheses**: `[IsSeparated π]`, `hsm : SmoothOfRelativeDimension 1 π`, `D D'`.
- **Uses from project**: (in-file) `vanishingLocus`, `vanishingLocus_le_ker_iff`, `exists_factor_subschemeι_iff`, `IsSubdivisor`, `isSubdivisor_iff_le`, `incidenceAux_comap_eq_bot_iff`; `RelEffCartierDiv` fields `finite`/`flat`/`lfp`, `RelEffCartierDiv.baseChange`, `baseChange_ideal` [CartierDiv].
- **Used by**: `exists_incidenceLocusEQ`, `subgroupLocusAux_Z3W` (`choose`), `subgroupLocusAux_Z3W_spec` (`choose_spec`), `exists_subgroupLocus` (in-file).
- **Visibility**: public
- **Lines**: 1008–1032
- **Notes**: key API (4 users); `hsm` is *unused* in the proof body (only the instances are used) — signature-tightening candidate (or it is intentional interface uniformity).

### `ModularCurves.RelEffCartierDiv.exists_incidenceLocusEQ`
- **Type**: theorem — (T-D15 = KM 1.3.5, incidence `=`)
- **What**: Universal closed subscheme for `D_T = D'_T` (both inequalities).
- **How**: `Z₁ ⊔ Z₂` of the two `exists_incidenceLocusLE` loci; `sup_le_iff` after `exists_factor_subschemeι_iff` three times.
- **Hypotheses**: `[IsSeparated π]`, `hsm`, `D D'`.
- **Uses from project**: (in-file) `exists_incidenceLocusLE`, `exists_factor_subschemeι_iff`, `IsSubdivisor`; `RelEffCartierDiv.baseChange` [CartierDiv].
- **Used by**: `exists_fullLevelLocus` (in-file).
- **Visibility**: public
- **Lines**: 1036–1046

### `ModularCurves.subgroupLocusAux_le_ker_iff`
- **Type**: private theorem
- **What**: `I ≤ f.ker ↔ I.comap f = ⊥` (Tier-0 comap/ker dictionary).
- **How**: `(map_gc f).l_eq_bot` + `map_bot`.
- **Hypotheses**: —
- **Uses from project**: [].
- **Used by**: `subgroupLocusAux_factors_iff`, `subgroupLocusAux_Z1_iff`, `subgroupLocusAux_Z3_le_ker_iff`, `subgroupLocusAux_P₁_factors`, `subgroupLocusAux_P₂_factors`, `subgroupLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 1052–1054
- **Notes**: key aux (6 users); same content as the Galois step inside `vanishingLocus_le_ker_iff` — micro-dedup possible.

### `ModularCurves.subgroupLocusAux_factors_iff`
- **Type**: private theorem
- **What**: `(∃ h, h ≫ I.subschemeι = x) ↔ I.comap x = ⊥`.
- **How**: `exists_factor_subschemeι_iff` + `subgroupLocusAux_le_ker_iff`.
- **Hypotheses**: —
- **Uses from project**: (in-file) `exists_factor_subschemeι_iff`, `subgroupLocusAux_le_ker_iff`.
- **Used by**: `subgroupLocusAux_Z3_le_ker_iff`, `subgroupLocusAux_isSubgroup_iff`, `exactOrderLocusAux_factor_iff` (in-file).
- **Visibility**: private
- **Lines**: 1056–1059
- **Notes**: key aux (3 users).

### `ModularCurves.subgroupLocusAux_zero_val`
- **Type**: private theorem
- **What**: `((0 : F.Point g) : T' ⟶ F.E) = g ≫ F.zero` (Tier-1 point value of zero).
- **How**: Unfold the `Point` zero through `MonObj.one` + `toUnit`, rewrite with `F.one_eq_zero`.
- **Hypotheses**: `F : EllipticCurve B`, `g : T' ⟶ B`.
- **Uses from project**: `EllipticCurve.Point` 0 [GroupLaw], `grp`, `one_eq_zero` [GroupLaw], `zero` [EC.Basic].
- **Used by**: `subgroupLocusAux_zero_valT` (in-file).
- **Visibility**: private
- **Lines**: 1064–1072

### `ModularCurves.subgroupLocusAux_neg_val`
- **Type**: private theorem
- **What**: `((-P) : T' ⟶ F.E) = P ≫ F.mulByHom (-1)`.
- **How**: `-P = (-1) • P` (`neg_one_zsmul`) + `F.point_smul_eq_comp_mulBy`.
- **Hypotheses**: `P : F.Point g`.
- **Uses from project**: `point_smul_eq_comp_mulBy`, `mulByHom` [GroupLaw].
- **Used by**: `subgroupLocusAux_neg_valT` (in-file).
- **Visibility**: private
- **Lines**: 1074–1078

### `ModularCurves.subgroupLocusAux_mu`
- **Type**: private noncomputable def
- **What**: The multiplication of the group scheme as a raw morphism `pullback F.π F.π ⟶ F.E`.
- **How**: `(MonObj.mul (X := F.asOver)).left` under the local `Over.cartesianMonoidalCategory` instance.
- **Hypotheses**: `F : EllipticCurve B`.
- **Uses from project**: `asOver`, `grp` [GroupLaw].
- **Used by**: `subgroupLocusAux_mu_w`, `subgroupLocusAux_point_add_val`, `subgroupLocusAux_add_comp`, `subgroupLocusAux_muT`, `subgroupLocusAux_mu_map_cond`, `subgroupLocusAux_mu_fst` (in-file).
- **Visibility**: private
- **Lines**: 1082–1085
- **Notes**: key aux (6 users).

### `ModularCurves.subgroupLocusAux_mu_w`
- **Type**: private theorem
- **What**: `μ ≫ F.π = fst ≫ F.π` (the multiplication is over `B`).
- **How**: `Over.w`.
- **Uses from project**: (in-file) `subgroupLocusAux_mu`.
- **Used by**: `subgroupLocusAux_mu_map_cond` (in-file).
- **Visibility**: private
- **Lines**: 1087–1090

### `ModularCurves.subgroupLocusAux_point_add_val`
- **Type**: private theorem
- **What**: `((P + Q) : T' ⟶ F.E) = pullback.lift P Q _ ≫ μ` — the raw value of point addition.
- **How**: `rfl` (definitional unfolding of the `Point` group structure).
- **Hypotheses**: `P Q : F.Point g`.
- **Uses from project**: (in-file) `subgroupLocusAux_mu`; `Point` addition [GroupLaw].
- **Used by**: `subgroupLocusAux_add_comp`, `subgroupLocusAux_add_fst` (in-file).
- **Visibility**: private
- **Lines**: 1092–1096
- **Notes**: defeq-sensitive `rfl` — pins the `Point`-addition implementation.

### `ModularCurves.subgroupLocusAux_add_comp`
- **Type**: private theorem
- **What**: Point addition commutes with precomposition by `k : T' ⟶ T` (targets specified by values, to allow propositionally-equal bases).
- **How**: Both sides are `lift ≫ μ`; `pullback.hom_ext` on the lifts using `hP`, `hQ`.
- **Hypotheses**: `hP : P'.val = k ≫ P.val`, `hQ : Q'.val = k ≫ Q.val`.
- **Uses from project**: (in-file) `subgroupLocusAux_point_add_val`, `subgroupLocusAux_mu`.
- **Used by**: `subgroupLocusAux_isSubgroup_iff`, `exactOrderLocusAux_toE_add_eq`, `fullLevelLocusAux_pair_fst`, `fullLevelLocusAux_match` (in-file).
- **Visibility**: private
- **Lines**: 1100–1109
- **Notes**: key aux (4 users) — the base-change bridge for addition.

### `ModularCurves.subgroupLocusAux_val`
- **Type**: def (public)
- **What**: The value of a point of the base-changed curve, typed at the **raw pullback**: `(E.baseChange t).Point g → (T' ⟶ pullback E.π t)`, `P ↦ P.1`.
- **How**: projection.
- **Hypotheses**: `E : EllipticCurve S`, `t : T ⟶ S`, `g : T' ⟶ T`.
- **Uses from project**: `EllipticCurve.baseChange`, `Point` [GroupLaw].
- **Used by**: ~24 declarations across Tiers 2–7 (`val_snd`, `zero_valT`, `neg_valT`, `point_add_valT`, `val_fst_π`, `add_fst`, `pairPt_val_fst`, `pairPt_mem`, `isSubgroup_iff`, `val_isClosedImmersion`, `val_smul(_fst/_asSection_fst)`, `toE'`, `toE`, `val_fst_snd`, `pt_ext'`, `pt_ext`, `match`, `phi_toE`, `factor_iff`, `fullLevel pair_fst/match/P1`, …).
- **Visibility**: public
- **Lines**: 1119–1120
- **Notes**: THE workhorse of the raw-typed discipline (most-used decl in the file). Public despite `Aux` name — naming cleanup candidate if externals consume it.

### `ModularCurves.subgroupLocusAux_val_snd`
- **Type**: theorem (public)
- **What**: `val P ≫ pullback.snd E.π t = g`.
- **How**: `P.2`.
- **Uses from project**: (in-file) `subgroupLocusAux_val`.
- **Used by**: `val_fst_π`, `point_add_valT`, `val_isClosedImmersion`, `pt_ext'`, `pt_ext`, `val_fst_snd` (proof), `factor_iff`, `fullLevelLocusAux_P1` (in-file; ≈8 users).
- **Visibility**: public
- **Lines**: 1122–1124
- **Notes**: key API.

### `ModularCurves.subgroupLocusAux_muT`
- **Type**: private noncomputable def
- **What**: Multiplication of the base-changed curve at the raw pullback spelling.
- **How**: `subgroupLocusAux_mu (E.baseChange t)`.
- **Uses from project**: (in-file) `subgroupLocusAux_mu`; `baseChange` [GroupLaw].
- **Used by**: `point_add_valT`, `mu_fst` (in-file).
- **Visibility**: private
- **Lines**: 1127–1129

### `ModularCurves.subgroupLocusAux_zeroT`
- **Type**: private noncomputable def
- **What**: Zero section of the base-changed curve, raw spelling: `T ⟶ pullback E.π t`.
- **How**: `(E.baseChange t).zero`.
- **Uses from project**: `baseChange` [GroupLaw], `zero` [EC.Basic].
- **Used by**: `zero_valT`, `Z1_iff`, `isSubgroup_iff`, `exactOrderLocusAux_zeroT_fst`, `exactOrderLocusAux_toE_zero` (in-file; 5 users).
- **Visibility**: private
- **Lines**: 1132–1134

### `ModularCurves.subgroupLocusAux_negT`
- **Type**: private noncomputable def
- **What**: Inversion on the base-changed curve, raw spelling.
- **How**: `(E.baseChange t).mulByHom (-1)`.
- **Uses from project**: `baseChange`, `mulByHom` [GroupLaw].
- **Used by**: `neg_valT`, `negT_fst`, `invD_baseChange`, `Z2_iff`, `isSubgroup_iff` (in-file; 5 users).
- **Visibility**: private
- **Lines**: 1137–1139

### `ModularCurves.subgroupLocusAux_zero_valT`
- **Type**: private theorem
- **What**: `val (0) = g ≫ zeroT` at the raw spelling.
- **How**: definitional cast of `subgroupLocusAux_zero_val (E.baseChange t)`.
- **Uses from project**: (in-file) `subgroupLocusAux_zero_val`, `subgroupLocusAux_zeroT`, `subgroupLocusAux_val`.
- **Used by**: `isSubgroup_iff`, `toE'_zero`, `toE_zero` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1141–1145

### `ModularCurves.subgroupLocusAux_neg_valT`
- **Type**: private theorem
- **What**: `val (-P) = val P ≫ negT`.
- **How**: cast of `subgroupLocusAux_neg_val (E.baseChange t)`.
- **Uses from project**: (in-file) `subgroupLocusAux_neg_val`, `subgroupLocusAux_negT`, `subgroupLocusAux_val`.
- **Used by**: `isSubgroup_iff`, `toE'_neg`, `toE_neg` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1147–1151

### `ModularCurves.subgroupLocusAux_negT_fst`
- **Type**: private theorem
- **What**: `negT ≫ fst = fst ≫ E.mulByHom (-1)` — inversion projects to inversion.
- **How**: `E.mulByHom_baseChange_fst t (-1)` [GroupLaw].
- **Uses from project**: (in-file) `subgroupLocusAux_negT`; `mulByHom_baseChange_fst` [GroupLaw].
- **Used by**: `invD_baseChange`, `toE'_neg`, `toE_neg` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1153–1157

### `ModularCurves.subgroupLocusAux_point_add_valT`
- **Type**: private theorem
- **What**: Raw value of addition on the base-changed curve: `val (P+Q) = lift (val P) (val Q) _ ≫ muT`.
- **How**: `rfl` (defeq with `point_add_val`).
- **Uses from project**: (in-file) `subgroupLocusAux_val`, `subgroupLocusAux_val_snd`, `subgroupLocusAux_muT`.
- **Used by**: `subgroupLocusAux_add_fst` (in-file).
- **Visibility**: private
- **Lines**: 1159–1164

### `ModularCurves.subgroupLocusAux_val_fst_π`
- **Type**: private theorem
- **What**: `(val P ≫ fst) ≫ E.π = g ≫ t` — the projected value lies over `g ≫ t`.
- **How**: `pullback.condition` + `val_snd`.
- **Uses from project**: (in-file) `subgroupLocusAux_val`, `subgroupLocusAux_val_snd`.
- **Used by**: `add_fst` (statement), `isSubgroup_iff`, `toE'_pi`, `toE_add` (in-file; 4 users).
- **Visibility**: private
- **Lines**: 1166–1169

### `ModularCurves.subgroupLocusAux_mu_map_cond`
- **Type**: private theorem
- **What**: Pullback-square condition `(fst ≫ μ) ≫ E.π = snd ≫ t` for the `pullback (fst ≫ π) t` presentation.
- **How**: `subgroupLocusAux_mu_w` + `pullback.condition`.
- **Uses from project**: (in-file) `subgroupLocusAux_mu`, `subgroupLocusAux_mu_w`.
- **Used by**: `subgroupLocusAux_mu_fst` (in-file).
- **Visibility**: private
- **Lines**: 1171–1176

### `ModularCurves.subgroupLocusAux_mu_fst_cond`
- **Type**: private theorem
- **What**: The two projected legs of a pair on the base-changed curve agree over `S`.
- **How**: `pullback.condition` twice.
- **Uses from project**: [].
- **Used by**: `subgroupLocusAux_mu_fst` (in-file).
- **Visibility**: private
- **Lines**: 1178–1185

### `ModularCurves.subgroupLocusAux_mu_fst`
- **Type**: private theorem
- **What**: `muT ≫ fst = lift (fst ≫ fst) (snd ≫ fst) _ ≫ mu` — base-changed multiplication projects to multiplication on projected pairs.
- **How**: Exhibits `muT` as `L ≫ lift (fst ≫ μ) snd` where `L = (Functor.LaxMonoidal.μ (Over.pullback t) …).left`, then `pullback.hom_ext` with mathlib `Over.μ_pullback_left_fst_fst'` / `Over.μ_pullback_left_fst_snd'`. 19-line proof.
- **Hypotheses**: —
- **Uses from project**: (in-file) `subgroupLocusAux_muT`, `subgroupLocusAux_mu`, `subgroupLocusAux_mu_map_cond`, `subgroupLocusAux_mu_fst_cond`; `baseChange` [GroupLaw].
- **Used by**: `subgroupLocusAux_add_fst` (in-file).
- **Visibility**: private
- **Lines**: 1189–1214
- **Notes**: the structural heart of the curve-crossing bridge (`obtain ⟨L, …⟩ := ⟨…, rfl, rfl⟩` defeq-pinning idiom).

### `ModularCurves.subgroupLocusAux_add_fst`
- **Type**: private theorem
- **What**: **Curve-crossing bridge**: `val (P + Q) ≫ fst = (⟨val P ≫ fst⟩ + ⟨val Q ≫ fst⟩ : E.Point (g ≫ t)).val`.
- **How**: rewrite both additions raw (`point_add_valT`, `point_add_val`), then `mu_fst` and `pullback.hom_ext`.
- **Hypotheses**: `P Q : (E.baseChange t).Point g`.
- **Uses from project**: (in-file) `subgroupLocusAux_val`, `subgroupLocusAux_point_add_valT`, `subgroupLocusAux_point_add_val`, `subgroupLocusAux_mu_fst`, `subgroupLocusAux_val_fst_π`.
- **Used by**: `isSubgroup_iff`, `toE'_add`, `toE_add` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1218–1229

### `ModularCurves.subgroupLocusAux_mulBy_comp`
- **Type**: private theorem
- **What**: `F.mulBy m ≫ F.mulBy n = F.mulBy (m * n)`.
- **How**: both are `𝟙 ^ (…)` in the `Hom`-group (`CategoryTheory.Hom.group`, mathlib); `GrpObj.comp_zpow` + `zpow_mul`.
- **Uses from project**: `mulBy` [GroupLaw].
- **Used by**: `mulByHom_neg_one_involutive` (in-file).
- **Visibility**: private
- **Lines**: 1233–1239

### `ModularCurves.subgroupLocusAux_mulByHom_neg_one_involutive`
- **Type**: private theorem
- **What**: `F.mulByHom (-1) ≫ F.mulByHom (-1) = 𝟙 F.E` — inversion is an involution.
- **How**: `mulBy_comp` at `(-1)·(-1)=1` plus `mulBy 1 = 𝟙` (`zpow_one`), take `.left`.
- **Uses from project**: (in-file) `subgroupLocusAux_mulBy_comp`; `mulBy`, `mulByHom` [GroupLaw].
- **Used by**: `isIso_mulByHom_neg_one` (in-file).
- **Visibility**: private
- **Lines**: 1241–1250

### `ModularCurves.subgroupLocusAux_isIso_mulByHom_neg_one`
- **Type**: private theorem (an `IsIso` construction)
- **What**: `IsIso (F.mulByHom (-1))`.
- **How**: self-inverse witness from the involutivity.
- **Uses from project**: (in-file) `subgroupLocusAux_mulByHom_neg_one_involutive`.
- **Used by**: `subgroupLocusAux_invD_prop` (in-file).
- **Visibility**: private
- **Lines**: 1252–1255

### `ModularCurves.subgroupLocusAux_invD_prop`
- **Type**: private theorem
- **What**: Iso-invariant morphism properties transfer from `D → S` to `inv*D → S`: `P (D.subschemeι ≫ π) → P ((D.ideal.comap [−1]).subschemeι ≫ π)`.
- **How**: `(D.ideal.comapIso [−1]).hom ≫ pullback.snd ≫ (…)` presentation via `Scheme.IdealSheafData.comapIso_hom_fst` (mathlib); pullback of the iso `[−1]` is iso; cancel twice with `MorphismProperty.cancel_left_of_respectsIso`. 13-line proof.
- **Hypotheses**: `P : MorphismProperty` `[P.RespectsIso]`, `hD : P (D.ideal.subschemeι ≫ E.π)`.
- **Uses from project**: (in-file) `subgroupLocusAux_isIso_mulByHom_neg_one`; `RelEffCartierDiv` [CartierDiv], `mulByHom`, `mulByHom_π` [GroupLaw].
- **Used by**: `subgroupLocusAux_invD` (×3 fields) (in-file).
- **Visibility**: private
- **Lines**: 1257–1273

### `ModularCurves.subgroupLocusAux_invD`
- **Type**: private noncomputable def
- **What**: KM 1.3.7's `inv*(D)`: the divisor with ideal `D.ideal.comap (E.mulByHom (-1))`, finite/flat/lfp by `invD_prop`.
- **How**: structure literal.
- **Uses from project**: (in-file) `subgroupLocusAux_invD_prop`; `RelEffCartierDiv` [CartierDiv], `mulByHom` [GroupLaw].
- **Used by**: `invD_baseChange`, `Z2_iff`, `exists_subgroupLocus` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1276–1281

### `ModularCurves.subgroupLocusAux_invD_baseChange`
- **Type**: private theorem
- **What**: `((invD E D).baseChange t).ideal = ((D.baseChange t).ideal).comap negT` — the inverse divisor base-changes to the pullback along base-changed inversion.
- **How**: two `baseChange_ideal` unfoldings, `comap_comp` both ways, `negT_fst`.
- **Uses from project**: (in-file) `subgroupLocusAux_invD`, `subgroupLocusAux_negT`, `subgroupLocusAux_negT_fst`; `RelEffCartierDiv.baseChange_ideal` [CartierDiv].
- **Used by**: `subgroupLocusAux_Z2_iff` (in-file).
- **Visibility**: private
- **Lines**: 1285–1292

### `ModularCurves.subgroupLocusAux_W`
- **Type**: private noncomputable def
- **What**: KM 1.3.7's `W = D ×_S D` (fibre product of `D → S` with itself).
- **How**: `pullback (D.ideal.subschemeι ≫ E.π) (…)`.
- **Uses from project**: `RelEffCartierDiv` [CartierDiv].
- **Used by**: `q`, `P₁`, `P₂`, `sigma`, `Z3W`, `isSubgroup_iff` (in-file; 5+ users).
- **Visibility**: private
- **Lines**: 1295–1297

### `ModularCurves.subgroupLocusAux_q`
- **Type**: private noncomputable def
- **What**: The finite locally free structure map `q : W ⟶ S` (first projection followed by `D → S`).
- **How**: composite.
- **Uses from project**: (in-file) `subgroupLocusAux_W`; `RelEffCartierDiv` [CartierDiv].
- **Used by**: ~15 declarations (`P₁`, `P₂`, `sum`, `sumDiv`, `Z3W`, `Z3W_spec`, `q_finite/flat/lfp`, `Z3`, `sigma(_snd/_fst)`, `Z3_le_ker_iff`, `pairPt(_val_fst/_mem)`, `isSubgroup_iff`).
- **Visibility**: private
- **Lines**: 1300–1303
- **Notes**: key aux.

### `ModularCurves.subgroupLocusAux_P₁` / `subgroupLocusAux_P₂`
- **Type**: private noncomputable defs
- **What**: The two tautological points of `E` over `W` (first/second projection composed with `D ↪ E`).
- **How**: subtype constructors; `P₂` needs `pullback.condition.symm`.
- **Uses from project**: (in-file) `subgroupLocusAux_q`, `subgroupLocusAux_W`; `Point` [GroupLaw], `RelEffCartierDiv` [CartierDiv].
- **Used by**: `sum`, `P₁_factors`/`P₂_factors`, `isSubgroup_iff` (3 users each).
- **Visibility**: private
- **Lines**: 1306–1309 / 1312–1315

### `ModularCurves.subgroupLocusAux_sum`
- **Type**: private noncomputable def
- **What**: KM 1.3.7's `m(P₁,P₂)`: the sum of the tautological pair in `E.Point q`.
- **How**: `P₁ + P₂`.
- **Uses from project**: (in-file) `subgroupLocusAux_P₁`, `subgroupLocusAux_P₂`; `Point` add [GroupLaw].
- **Used by**: `sumDiv`, `sigma`, `sigma_fst`, `Z3_le_ker_iff`, `isSubgroup_iff` (in-file; 5 users).
- **Visibility**: private
- **Lines**: 1318–1320

### `ModularCurves.subgroupLocusAux_sumDiv`
- **Type**: private noncomputable def
- **What**: The divisor `[m(P₁,P₂)]` in the base-changed curve over `W`.
- **How**: `RelEffCartierDiv.sectionDivisor` at `(sum).asSection`.
- **Uses from project**: (in-file) `subgroupLocusAux_sum`, `subgroupLocusAux_q`; `sectionDivisor` [CartierDiv], `Point.asSection` [GroupLaw], `baseChange` [GroupLaw].
- **Used by**: `Z3W`, `Z3W_spec`, `Z3_le_ker_iff` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1323–1328

### `ModularCurves.subgroupLocusAux_Z3W`
- **Type**: private noncomputable def
- **What**: KM 1.3.7's third locus upstairs: the incidence locus of `[m(P₁,P₂)] ≤ D_W` over `W`, extracted by `choose`.
- **How**: `(exists_incidenceLocusLE …).choose`.
- **Uses from project**: (in-file) `exists_incidenceLocusLE`, `subgroupLocusAux_sumDiv`, `subgroupLocusAux_q`; `baseChange`+`smooth` [GroupLaw/EC.Basic], `RelEffCartierDiv.baseChange` [CartierDiv].
- **Used by**: `Z3W_spec`, `Z3`, `Z3_le_ker_iff` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1332–1335
- **Notes**: `choose` on an existential — the locus is opaque data; fine for an existence theorem file.

### `ModularCurves.subgroupLocusAux_Z3W_spec`
- **Type**: private theorem
- **What**: The `choose_spec` of `Z3W`: factoring through `Z3W` ⇔ `IsSubdivisor` after base change by `w`.
- **How**: `choose_spec`.
- **Uses from project**: (in-file) `subgroupLocusAux_Z3W`, `exists_incidenceLocusLE`, `IsSubdivisor`; `RelEffCartierDiv.baseChange` [CartierDiv].
- **Used by**: `subgroupLocusAux_Z3_le_ker_iff` (in-file).
- **Visibility**: private
- **Lines**: 1337–1344

### `ModularCurves.subgroupLocusAux_q_finite` / `_q_flat` / `_q_lfp`
- **Type**: private theorems
- **What**: `q : W ⟶ S` is finite / flat / lfp.
- **How**: `MorphismProperty.comp_mem` + `pullback_fst` from `D.finite`/`D.flat`/`D.lfp`.
- **Uses from project**: (in-file) `subgroupLocusAux_q`; `RelEffCartierDiv` fields [CartierDiv].
- **Used by**: `subgroupLocusAux_Z3`, `subgroupLocusAux_Z3_le_ker_iff` (2 users each).
- **Visibility**: private
- **Lines**: 1346–1349 / 1351–1354 / 1356–1359

### `ModularCurves.subgroupLocusAux_Z3`
- **Type**: private noncomputable def
- **What**: KM 1.3.7's third locus on `S`: `vanishingLocus q Z3W` — the `(deg D)²`-coordinates descent of `Z3W`.
- **How**: instances installed by `haveI` from `q_finite/flat/lfp`.
- **Uses from project**: (in-file) `vanishingLocus`, `subgroupLocusAux_q`, `subgroupLocusAux_Z3W`, `q_finite`, `q_flat`, `q_lfp`.
- **Used by**: `Z3_le_ker_iff`, `exists_subgroupLocus` (in-file).
- **Visibility**: private
- **Lines**: 1362–1367

### `ModularCurves.subgroupLocusAux_Z1_iff`
- **Type**: private theorem
- **What**: Condition (1): `[e]_T ≤ D_T ↔ (D_T).ideal.comap zeroT = ⊥` — the zero section factors through `D_T`.
- **How**: `isSubdivisor_iff_le`; identify the base-changed section divisor's ideal with `ker zeroT` via `RelEffCartierDiv.ker_sectionBaseChange` [CartierDiv]; finish with `subgroupLocusAux_le_ker_iff`.
- **Hypotheses**: `E`, `D`, `t`.
- **Uses from project**: (in-file) `IsSubdivisor`, `isSubdivisor_iff_le`, `subgroupLocusAux_zeroT`, `subgroupLocusAux_le_ker_iff`; `sectionDivisor`, `baseChange_ideal`, `ker_sectionBaseChange` [CartierDiv], `zero`, `zero_π` [EC.Basic].
- **Used by**: `exists_subgroupLocus` (in-file).
- **Visibility**: private
- **Lines**: 1373–1386

### `ModularCurves.subgroupLocusAux_Z2_iff`
- **Type**: private theorem
- **What**: Condition (2): `D_T ≤ (inv*D)_T ↔ (D_T).ideal.comap negT ≤ (D_T).ideal`.
- **How**: `isSubdivisor_iff_le` + `invD_baseChange`.
- **Uses from project**: (in-file) `IsSubdivisor`, `isSubdivisor_iff_le`, `subgroupLocusAux_invD`, `subgroupLocusAux_invD_baseChange`, `subgroupLocusAux_negT`; `RelEffCartierDiv.baseChange` [CartierDiv].
- **Used by**: `exists_subgroupLocus` (in-file).
- **Visibility**: private
- **Lines**: 1390–1396

### `ModularCurves.subgroupLocusAux_sigma`
- **Type**: private noncomputable def
- **What**: The tautological sum as a raw section `W ⟶ pullback E.π q`.
- **How**: `(asSection E q sum).1`.
- **Uses from project**: (in-file) `subgroupLocusAux_W`, `subgroupLocusAux_q`, `subgroupLocusAux_sum`; `Point.asSection` [GroupLaw].
- **Used by**: `sigma_snd`, `sigma_fst`, `Z3_le_ker_iff` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1400–1403

### `ModularCurves.subgroupLocusAux_sigma_snd`
- **Type**: private theorem
- **What**: `sigma ≫ snd = 𝟙 W` (it is a section).
- **How**: `.2` of `asSection`.
- **Uses from project**: (in-file) `subgroupLocusAux_sigma`; `Point.asSection` [GroupLaw].
- **Used by**: `subgroupLocusAux_Z3_le_ker_iff` (in-file, multiple sites).
- **Visibility**: private
- **Lines**: 1405–1409

### `ModularCurves.subgroupLocusAux_sigma_fst`
- **Type**: private theorem
- **What**: `sigma ≫ fst = (sum).val`.
- **How**: `Point.asSection_val_fst` [GroupLaw].
- **Uses from project**: (in-file) `subgroupLocusAux_sigma`, `subgroupLocusAux_sum`; `asSection_val_fst` [GroupLaw].
- **Used by**: `subgroupLocusAux_Z3_le_ker_iff` (in-file).
- **Visibility**: private
- **Lines**: 1411–1415

### `ModularCurves.subgroupLocusAux_Z3_le_ker_iff`
- **Type**: private theorem
- **What**: Condition (3) in normal form: `Z3 ≤ t.ker ↔ D.ideal.comap (snd ≫ sum.val) = ⊥` over `T ×_S W`.
- **How**: Unfold `Z3` and apply `vanishingLocus_le_ker_iff`; convert to the factoring form via `subgroupLocusAux_factors_iff` and `Z3W_spec` + `isSubdivisor_iff_le`; identify the base-changed sum divisor's ideal with the kernel of the lifted section (`hσ`, via `baseChange_ideal` + `ker_sectionBaseChange` at `sigma`); collapse the double comap along `pullback.lift` with `comap_comp`/`lift_fst`/`sigma_fst` (`hcomp`).
- **Hypotheses**: `E`, `D`, `t`.
- **Uses from project**: (in-file) `subgroupLocusAux_Z3`, `vanishingLocus_le_ker_iff`, `subgroupLocusAux_factors_iff`, `subgroupLocusAux_Z3W_spec`, `isSubdivisor_iff_le`, `subgroupLocusAux_sumDiv`, `subgroupLocusAux_sigma(_snd/_fst)`, `subgroupLocusAux_le_ker_iff`, `q_finite/flat/lfp`, `subgroupLocusAux_sum`; `baseChange_ideal`, `ker_sectionBaseChange` [CartierDiv], `baseChange` [GroupLaw].
- **Used by**: `exists_subgroupLocus` (in-file).
- **Visibility**: private
- **Lines**: 1419–1471
- **Notes**: **proof 48 lines (>30)**; repeated verbatim `pullback.lift … (by rw [...])` sub-terms (3×) — golf/`set` candidate.

### `ModularCurves.subgroupLocusAux_pairPt`
- **Type**: private noncomputable def
- **What**: Base-change of a point of `E` over `W` to a point of `E ×_S T` over `T ×_S W` (the universal-pair transport).
- **How**: `pullback.lift (snd ≫ P.1) fst` with `P.2` + `pullback.condition`.
- **Uses from project**: (in-file) `subgroupLocusAux_q`; `baseChange`, `Point` [GroupLaw].
- **Used by**: `pairPt_val_fst`, `pairPt_mem`, `isSubgroup_iff` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1476–1483

### `ModularCurves.subgroupLocusAux_pairPt_val_fst`
- **Type**: private theorem
- **What**: `val (pairPt P) ≫ fst = snd ≫ P.1`.
- **How**: `pullback.lift_fst`.
- **Uses from project**: (in-file) `subgroupLocusAux_val`, `subgroupLocusAux_pairPt`.
- **Used by**: `pairPt_mem`, `isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 1485–1490

### `ModularCurves.subgroupLocusAux_pairPt_mem`
- **Type**: private theorem
- **What**: If `D.ideal.comap P.1 = ⊥` then the base-changed point kills `(D_T).ideal` too.
- **How**: `baseChange_ideal` + `comap_comp` + `pairPt_val_fst`.
- **Uses from project**: (in-file) `subgroupLocusAux_pairPt(_val_fst)`, `subgroupLocusAux_val`; `baseChange_ideal` [CartierDiv].
- **Used by**: `subgroupLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 1494–1501

### `ModularCurves.subgroupLocusAux_P₁_factors` / `_P₂_factors`
- **Type**: private theorems
- **What**: The tautological points factor through `D`: `D.ideal.comap Pᵢ.1 = ⊥`.
- **How**: `D.ideal.comap subschemeι = ⊥` from `ker_subschemeι` via `subgroupLocusAux_le_ker_iff`, then `comap_comp`.
- **Uses from project**: (in-file) `subgroupLocusAux_le_ker_iff`, `subgroupLocusAux_P₁`/`_P₂`.
- **Used by**: `subgroupLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 1503–1512 / 1514–1523

### `ModularCurves.subgroupLocusAux_isSubgroup_iff`
- **Type**: private theorem
- **What**: **The KM 1.3.6 ⇔ 1.3.7 dictionary at `t`**: `(D_T).IsSubgroup (E_T)` ⇔ (1) zero factors, (2) stability under inversion, (3) the tautological sum factors over `T ×_S W`.
- **How**: Forward: instantiate the `IsSubgroup` witness at `𝟙 T` (zero via `zero_valT`), at the universal point `(D_T).subschemeι` (negation via `neg_valT` + `ker_subschemeι`), and at the universal pair over `pullback.fst t q` (addition: `pairPt` of `P₁`,`P₂` are members by `pairPt_mem` + `Pᵢ_factors`; `add_mem`; project with `add_fst`/`add_comp`). Backward: define `H := {P | (D_T).ideal.comap (val P) = ⊥}` as an `AddSubgroup`; closure under `+` via the classifying map `c := pullback.lift hp hq` to `W` and condition (3); zero/neg from (1)/(2) with `comap_mono`; the membership dictionary is `subgroupLocusAux_factors_iff`.
- **Hypotheses**: `E`, `D`, `t`.
- **Uses from project**: (in-file) `subgroupLocusAux_{zeroT,negT,val,val_snd,zero_valT,neg_valT,factors_iff,le_ker_iff,pairPt,pairPt_mem,pairPt_val_fst,P₁,P₂,P₁_factors,P₂_factors,add_fst,add_comp,val_fst_π,sum,W,q}`; `RelEffCartierDiv.IsSubgroup` [ExactOrder], `baseChange_ideal` [CartierDiv], `baseChange`/`Point` [GroupLaw].
- **Used by**: `exists_subgroupLocus` (in-file).
- **Visibility**: private
- **Lines**: 1529–1652
- **Notes**: **proof 117 lines (>30)** — largest proof in the subgroup block; clear two-way structure, decompose candidate (each direction ≈ standalone lemma).

### `ModularCurves.exists_subgroupLocus`
- **Type**: theorem — (T-D16 = KM 1.3.7)
- **What**: For `E/S` elliptic and `D` an effective divisor in `E/S`, there is a closed subscheme `Z ⊆ S` universal for "`D` is a subgroup" (cut by `1 + deg D + (deg D)²` equations), compatible with base change.
- **How**: `Z := Z₁ ⊔ Z₂ ⊔ Z₃` where `Z₁`/`Z₂` are `exists_incidenceLocusLE` at `([e], D)` and `(inv*D, D)` and `Z₃ = subgroupLocusAux_Z3`; assemble with `sup_le_iff` + `exists_factor_subschemeι_iff`, then `Z1_iff`, `Z2_iff`, `Z3_le_ker_iff`, `isSubgroup_iff`, `and_assoc`. 10-line proof.
- **Hypotheses**: `E : EllipticCurve S`, `D : RelEffCartierDiv E.π`.
- **Uses from project**: (in-file) `exists_incidenceLocusLE`, `subgroupLocusAux_invD`, `subgroupLocusAux_Z3`, `exists_factor_subschemeι_iff`, `subgroupLocusAux_Z1_iff`, `subgroupLocusAux_Z2_iff`, `subgroupLocusAux_Z3_le_ker_iff`, `subgroupLocusAux_isSubgroup_iff`; `sectionDivisor` [CartierDiv], `zero`/`zero_π`/`smooth` [EC.Basic], `RelEffCartierDiv.IsSubgroup` [ExactOrder].
- **Used by**: `exists_exactOrderLocus_section`, `exists_exactOrderLocus` (in-file).
- **Visibility**: public
- **Lines**: 1659–1672
- **Notes**: headline KM 1.3.7.

### `ModularCurves.exists_exactOrderLocus_section`
- **Type**: theorem — (T-D33)
- **What**: For `P ∈ E(S)` and `N`, a closed subscheme `Z ⊆ S` universal for "`P|_T` has exact order `N` on `E ×_S T`".
- **How**: `exists_subgroupLocus` at the order divisor `Σₐ[aP]`, then rewrite the base-changed order divisor with `Section.orderDivisor_baseChange` [ExactOrder]; `HasExactOrder` unfolds by `show` to `IsSubgroup` of the order divisor. 7-line proof.
- **Hypotheses**: `P : E.Section`, `[NeZero N]`.
- **Uses from project**: (in-file) `exists_subgroupLocus`; `Section.orderDivisor`, `Section.HasExactOrder`, `Section.orderDivisor_baseChange`, `Section`, `Point.pull` [ExactOrder], `Point.asSection`, `baseChange` [GroupLaw].
- **Used by**: [] (unused within these files).
- **Visibility**: public
- **Lines**: 1680–1692
- **Notes**: terminal public API (Γ₁ section-level locus).

### `ModularCurves.exactOrderLocusAux_ker_eq_of_comp`
- **Type**: private theorem
- **What**: Two morphisms that factor through each other have equal kernel ideal sheaves.
- **How**: antisymmetry from `Scheme.Hom.le_ker_comp` twice.
- **Hypotheses**: `h₁ : d₁ ≫ f₂ = f₁`, `h₂ : d₂ ≫ f₁ = f₂`.
- **Uses from project**: [].
- **Used by**: `exactOrderLocusAux_ker_comap_eq`, `fullLevelLocusAux_torsionIdeal_baseChange` (in-file).
- **Visibility**: private
- **Lines**: 1703–1710

### `ModularCurves.exactOrderLocusAux_ker_comap_eq`
- **Type**: theorem (public)
- **What**: **Two-sided kernel–comap comparison**: for closed-immersion sections `W` (of `C×B/B`) and `V` (of `C×T/T`) matched along `c : T ⟶ B`, and points `z, w` with matched first legs, `W.ker.comap z = V.ker.comap w`. The value-level engine of the KM 1.6.2–1.6.5 bookkeeping.
- **How**: Reduce both kernels to `pullback.fst`-kernels via `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` (mathlib); compute the second legs of the two pullbacks (`hzW`, `hwV` calc chains from `hWsnd`/`hVsnd`); build mutually-factoring morphisms of the two pullbacks with `pullback.lift` (`hc₁`, `hc₂`, using `hm`, `hzw`); conclude by `exactOrderLocusAux_ker_eq_of_comp`.
- **Hypotheses**: `hWc hVc : IsClosedImmersion`, `hWsnd`, `hVsnd`, `hm` (matching along `c`), `hz`, `hw`, `hzw`.
- **Uses from project**: (in-file) `exactOrderLocusAux_ker_eq_of_comp`.
- **Used by**: `exactOrderLocusAux_factor_iff`, `fullLevelLocusAux_P1` (in-file).
- **Visibility**: public
- **Lines**: 1717–1761
- **Notes**: **proof 36 lines (>30)**; deliberately public "engine" despite `Aux` name.

### `ModularCurves.exactOrderLocusAux_val_isClosedImmersion`
- **Type**: theorem (public)
- **What**: Sections (`g = 𝟙 T`) of the base-changed curve are closed immersions, raw spelling.
- **How**: `val R ≫ snd = 𝟙` is a closed immersion; cancel by `IsClosedImmersion.of_comp` against the separated `(E.baseChange t).π`.
- **Hypotheses**: `R : (E.baseChange t).Point (𝟙 T)`.
- **Uses from project**: (in-file) `subgroupLocusAux_val`, `subgroupLocusAux_val_snd`; `baseChange` [GroupLaw].
- **Used by**: `exactOrderLocusAux_factor_iff`, `fullLevelLocusAux_P1` (in-file).
- **Visibility**: public
- **Lines**: 1764–1772

### `ModularCurves.exactOrderLocusAux_zeroT_fst`
- **Type**: private theorem
- **What**: `zeroT ≫ fst = t ≫ E.zero` — the base-changed zero section projects to the zero section.
- **How**: `pullback.lift_fst` (defeq of `(E.baseChange t).zero`).
- **Uses from project**: (in-file) `subgroupLocusAux_zeroT`; `baseChange` zero [GroupLaw].
- **Used by**: `toE'_zero`, `toE_zero`, `fullLevelLocusAux_torsionIdeal_baseChange` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1775–1777

### `ModularCurves.exactOrderLocusAux_val_smul`
- **Type**: private theorem
- **What**: `val (m • R) = val R ≫ (E.baseChange t).mulByHom m` — scalar multiplication at raw spelling.
- **How**: `(E.baseChange t).point_smul_eq_comp_mulBy` [GroupLaw].
- **Uses from project**: (in-file) `subgroupLocusAux_val`; `point_smul_eq_comp_mulBy`, `mulByHom`, `baseChange` [GroupLaw].
- **Used by**: `exactOrderLocusAux_val_smul_fst` (in-file).
- **Visibility**: private
- **Lines**: 1780–1784

### `ModularCurves.exactOrderLocusAux_val_smul_fst`
- **Type**: private theorem
- **What**: `val (m • R) ≫ fst = (val R ≫ fst) ≫ E.mulByHom m`.
- **How**: `val_smul` + `mulByHom_baseChange_fst` via explicit calc (12 lines; congrArg-style, avoids `rw`-motive issues).
- **Uses from project**: (in-file) `exactOrderLocusAux_val_smul`, `subgroupLocusAux_val`; `mulByHom_baseChange_fst` [GroupLaw].
- **Used by**: `exactOrderLocusAux_val_smul_asSection_fst` (in-file).
- **Visibility**: private
- **Lines**: 1787–1802

### `ModularCurves.exactOrderLocusAux_val_smul_asSection_fst`
- **Type**: theorem (public)
- **What**: `val (m • asSection P) ≫ fst = P.1 ≫ E.mulByHom m`.
- **How**: previous + `pullback.lift_fst` for `asSection`.
- **Uses from project**: (in-file) `exactOrderLocusAux_val_smul_fst`, `subgroupLocusAux_val`; `Point.asSection` [GroupLaw].
- **Used by**: `exactOrderLocusAux_match`, `fullLevelLocusAux_pair_fst`, `fullLevelLocusAux_killed` (in-file; 3 users).
- **Visibility**: public
- **Lines**: 1805–1811

### `ModularCurves.exactOrderLocusAux_toE'`
- **Type**: private noncomputable def
- **What**: The `E`-value of a point of the (singly) base-changed curve: `val A ≫ fst : T' ⟶ E.E`.
- **How**: composite.
- **Uses from project**: (in-file) `subgroupLocusAux_val`.
- **Used by**: ~12 declarations (`toE'_pi/_zero/_neg/_add`, `pt_ext'`, `toE_zero_eq`, `toE_neg_eq`, `toE_add_eq`, `phi`, `phi_toE`, `psi_toE'`, `fullLevelLocusAux_pair_fst`).
- **Visibility**: private
- **Lines**: 1814–1816
- **Notes**: key aux.

### `ModularCurves.exactOrderLocusAux_toE'_pi`
- **Type**: private theorem
- **What**: `toE' A ≫ E.π = g ≫ t`.
- **How**: `subgroupLocusAux_val_fst_π`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'`, `subgroupLocusAux_val_fst_π`.
- **Used by**: `toE'_add` (statement), `phi`, `toE_add_eq`, `fullLevelLocusAux_pair_fst` (in-file; 4 users).
- **Visibility**: private
- **Lines**: 1818–1821

### `ModularCurves.exactOrderLocusAux_toE'_zero`
- **Type**: private theorem
- **What**: `toE' 0 = g ≫ t ≫ E.zero`.
- **How**: `zero_valT` + `zeroT_fst`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'`, `subgroupLocusAux_zero_valT`, `exactOrderLocusAux_zeroT_fst`.
- **Used by**: `toE_zero_eq`, `fullLevelLocusAux_killed` (in-file).
- **Visibility**: private
- **Lines**: 1823–1828

### `ModularCurves.exactOrderLocusAux_toE'_neg`
- **Type**: private theorem
- **What**: `toE' (-A) = toE' A ≫ E.mulByHom (-1)`.
- **How**: `neg_valT` + `negT_fst`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'`, `subgroupLocusAux_neg_valT`, `subgroupLocusAux_negT_fst`; `mulByHom` [GroupLaw].
- **Used by**: `toE_neg_eq`, `phi_neg`, `psi_neg` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1830–1837

### `ModularCurves.exactOrderLocusAux_toE'_add`
- **Type**: private theorem
- **What**: `toE' (A + B)` is the value of the sum of the two projected `E`-points.
- **How**: exactly `subgroupLocusAux_add_fst`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'(_pi)`, `subgroupLocusAux_add_fst`.
- **Used by**: `toE_add_eq`, `fullLevelLocusAux_pair_fst` (in-file).
- **Visibility**: private
- **Lines**: 1839–1845

### `ModularCurves.exactOrderLocusAux_pt_ext'`
- **Type**: private theorem
- **What**: Points of the base-changed curve are determined by their `E`-values (`toE'` injective at fixed `g`).
- **How**: `Subtype.ext` + `pullback.hom_ext` (second legs both `g` by `val_snd`).
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'`, `subgroupLocusAux_val(_snd)`.
- **Used by**: `psi_zero`, `psi_neg`, `psi_add`, `fullLevelLocusAux_killed` (in-file; 4 users).
- **Visibility**: private
- **Lines**: 1848–1854

### `ModularCurves.exactOrderLocusAux_orderDivisor_ideal`
- **Type**: private theorem
- **What**: Generic unfolding: `(orderDivisor F σ N).ideal = ∏ₐ ker ((a+1) • σ).1`.
- **How**: unfold `orderDivisor` → `sectionsDivisor`, `dif_pos ⟨inferInstance, F.smooth⟩`.
- **Uses from project**: `Section.orderDivisor` [ExactOrder], `sectionsDivisor` [CartierDiv], `smooth` [EC.Basic].
- **Used by**: `exactOrderLocusAux_factor_iff` (in-file).
- **Visibility**: private
- **Lines**: 1857–1863
- **Notes**: same `dif_pos` unfolding as IsoTransport's `sectionsDivisor_pointMap_ideal` and `fullLevelLocusAux_sectionsDivisor_ideal` — three copies of this unfolding across the two files; a `sectionsDivisor_ideal`-style simp lemma in CartierDivisor.lean would kill all three.

### `ModularCurves.exactOrderLocusAux_toE`
- **Type**: private noncomputable def
- **What**: `E`-value of a point of the **doubly** base-changed curve over `E[N]`: `(val Q ≫ fst) ≫ fst`.
- **How**: composite.
- **Uses from project**: (in-file) `subgroupLocusAux_val`; `torsion`, `torsionπ` [Torsion], `baseChange` [GroupLaw].
- **Used by**: ~10 declarations (`toE_pi/_zero/_neg/_add`, `toE_zero_eq/_neg_eq/_add_eq`, `pt_ext`, `phi_toE`, `psi`, `psi_toE'`).
- **Visibility**: private
- **Lines**: 1866–1870
- **Notes**: key aux.

### `ModularCurves.exactOrderLocusAux_val_fst_snd`
- **Type**: private theorem
- **What**: The middle leg of a doubly-base-changed point lies over `g ≫ c`.
- **How**: `pullback.condition` + `val_snd` (the middle projection is `(E.baseChange (E.torsionπ N)).π` by defeq).
- **Uses from project**: (in-file) `subgroupLocusAux_val(_snd)`; `torsionπ` [Torsion].
- **Used by**: `toE_pi`, `pt_ext`, `factor_iff` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1873–1883

### `ModularCurves.exactOrderLocusAux_toE_pi`
- **Type**: private theorem
- **What**: `toE Q ≫ E.π = (g ≫ c) ≫ E.torsionπ N`.
- **How**: 15-line calc through `pullback.condition` and `val_fst_snd`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE`, `exactOrderLocusAux_val_fst_snd`; `torsionπ` [Torsion].
- **Used by**: `toE_add` (statement), `toE_add_eq`, `psi` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1885–1903

### `ModularCurves.exactOrderLocusAux_toE_zero`
- **Type**: private theorem
- **What**: `toE 0 = (g ≫ c) ≫ E.torsionπ N ≫ E.zero`.
- **How**: chains `zero_valT` on the inner curve, `zeroT_fst` twice (for `E.baseChange (torsionπ)` and for `E`), by explicit `e1/e2/e3`, `h1/h2/h3` congrArg-assoc steps.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE`, `subgroupLocusAux_val`, `subgroupLocusAux_zero_valT`, `subgroupLocusAux_zeroT`, `exactOrderLocusAux_zeroT_fst`; `torsionπ` [Torsion].
- **Used by**: `exactOrderLocusAux_toE_zero_eq` (in-file).
- **Visibility**: private
- **Lines**: 1905–1941
- **Notes**: **proof 32 lines (>30)** — pure associativity bookkeeping; golf candidate (`simp only [Category.assoc, …]`).

### `ModularCurves.exactOrderLocusAux_toE_zero_eq`
- **Type**: private theorem
- **What**: Matched zero values: `toE' 0 = toE 0` under `hct : c ≫ torsionπ = t`.
- **How**: `toE'_zero` + `toE_zero` + `hct`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'(_zero)`, `exactOrderLocusAux_toE(_zero)`; `torsionπ` [Torsion].
- **Used by**: `phi_zero`, `psi_zero` (in-file).
- **Visibility**: private
- **Lines**: 1944–1951

### `ModularCurves.exactOrderLocusAux_toE_neg`
- **Type**: private theorem
- **What**: `toE (-Q) = toE Q ≫ E.mulByHom (-1)`.
- **How**: `neg_valT` + `negT_fst` on the inner curve, then `mulByHom_baseChange_fst` on the outer; 28-line congrArg/calc.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE`, `subgroupLocusAux_neg_valT`, `subgroupLocusAux_negT_fst`; `mulByHom_baseChange_fst`, `mulByHom` [GroupLaw], `torsionπ` [Torsion].
- **Used by**: `toE_neg_eq`, `phi_neg`, `psi_neg` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 1953–1985

### `ModularCurves.exactOrderLocusAux_toE_neg_eq`
- **Type**: private theorem
- **What**: Matched values are preserved by negation: `toE' A = toE Q ⟹ toE' (-A) = toE (-Q)`.
- **How**: `toE'_neg` + `toE_neg` + `hm`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'_neg`, `exactOrderLocusAux_toE_neg`.
- **Used by**: [] — **UNUSED in-file** (`phi_neg`/`psi_neg` inline the same rewrite instead).
- **Visibility**: private
- **Lines**: 1988–1994
- **Notes**: dead private lemma — delete or use in `phi_neg`/`psi_neg`.

### `ModularCurves.exactOrderLocusAux_toE_add`
- **Type**: private theorem
- **What**: `toE (Q + Q')` is the value of the sum of the two matched `E`-points.
- **How**: apply `subgroupLocusAux_add_fst` on the inner curve, project, and apply `subgroupLocusAux_add_fst` again on `E`; 13-line proof.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE(_pi)`, `subgroupLocusAux_add_fst`, `subgroupLocusAux_val(_fst_π)`; `torsionπ` [Torsion].
- **Used by**: `exactOrderLocusAux_toE_add_eq` (in-file).
- **Visibility**: private
- **Lines**: 1996–2015

### `ModularCurves.exactOrderLocusAux_toE_add_eq`
- **Type**: private theorem
- **What**: Matched values preserved by addition across the two curves.
- **How**: `toE'_add` + `toE_add`, then `subgroupLocusAux_add_comp` at `k = 𝟙 T'` matches the two `E.Point` sums; 13-line proof.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'(_add/_pi)`, `exactOrderLocusAux_toE(_add/_pi)`, `subgroupLocusAux_add_comp`.
- **Used by**: `phi_add`, `psi_add` (in-file).
- **Visibility**: private
- **Lines**: 2018–2037

### `ModularCurves.exactOrderLocusAux_pt_ext`
- **Type**: private theorem
- **What**: Points of the doubly-base-changed curve are determined by their `E`-values.
- **How**: `Subtype.ext` + nested `pullback.hom_ext`; the middle legs agree by `val_fst_snd`, the bottom by `val_snd`. 10-line proof.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE`, `subgroupLocusAux_val(_snd)`, `exactOrderLocusAux_val_fst_snd`; `torsionπ` [Torsion].
- **Used by**: `phi_zero`, `phi_neg`, `phi_add` (in-file; 3 users).
- **Visibility**: private
- **Lines**: 2040–2053

### `ModularCurves.exactOrderLocusAux_match`
- **Type**: private theorem
- **What**: The universal (`⟨torsionι, torsionι_π⟩` over `E[N]`) and classified (`P` over `T`) order-divisor sections have matched values along `c`: `c ≫ val (m • asSection u) ≫ fst = val (m • asSection P) ≫ fst`.
- **How**: `val_smul_asSection_fst` on both sides + `hcP`.
- **Hypotheses**: `hcP : c ≫ E.torsionι N = P.1`.
- **Uses from project**: (in-file) `exactOrderLocusAux_val_smul_asSection_fst`, `subgroupLocusAux_val`; `torsionι`, `torsionι_π` [Torsion], `Point.asSection`, `mulByHom` [GroupLaw].
- **Used by**: `exactOrderLocusAux_factor_iff` (in-file).
- **Visibility**: private
- **Lines**: 2057–2067

### `ModularCurves.exactOrderLocusAux_phi`
- **Type**: private noncomputable def
- **What**: Transport of a point of `E ×_S T` to the doubly-base-changed curve over `E[N]` (along `hct : c ≫ torsionπ = t`).
- **How**: nested `pullback.lift` of `toE' A` and `g ≫ c`.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'(_pi)`; `torsionπ` [Torsion], `baseChange`, `Point` [GroupLaw].
- **Used by**: `phi_toE`, `phi_zero`, `phi_neg`, `phi_add`, `exactOrderLocusAux_isSubgroup_iff` (in-file; 5 users).
- **Visibility**: private
- **Lines**: 2070–2078

### `ModularCurves.exactOrderLocusAux_phi_toE`
- **Type**: private theorem
- **What**: `toE (phi A) = toE' A`.
- **How**: two `pullback.lift_fst`s (11-line proof with an inline `show`+`rw`).
- **Uses from project**: (in-file) `exactOrderLocusAux_phi`, `exactOrderLocusAux_toE`, `exactOrderLocusAux_toE'`, `subgroupLocusAux_val`.
- **Used by**: `phi_zero`, `phi_neg`, `phi_add`, `exactOrderLocusAux_isSubgroup_iff` (in-file; 4 users).
- **Visibility**: private
- **Lines**: 2080–2095

### `ModularCurves.exactOrderLocusAux_phi_zero` / `_phi_neg` / `_phi_add`
- **Type**: private theorems
- **What**: `phi` is additive/preserves 0 and negation (a group homomorphism pointwise).
- **How**: inject via `pt_ext`, rewrite with `phi_toE` and the matched-value lemmas `toE_zero_eq` / `toE'_neg`+`toE_neg` / `toE_add_eq`.
- **Uses from project**: (in-file) `exactOrderLocusAux_pt_ext`, `phi_toE`, `toE_zero_eq`/`toE'_neg`+`toE_neg`/`toE_add_eq`.
- **Used by**: `exactOrderLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 2097–2102 / 2104–2110 / 2112–2120

### `ModularCurves.exactOrderLocusAux_psi`
- **Type**: private noncomputable def
- **What**: Transport back: doubly-base-changed point ↦ point of `E ×_S T`.
- **How**: `pullback.lift (toE Q) g` (condition via `toE_pi` + `hct`).
- **Uses from project**: (in-file) `exactOrderLocusAux_toE(_pi)`; `baseChange` [GroupLaw].
- **Used by**: `psi_toE'`, `psi_zero`, `psi_neg`, `psi_add`, `exactOrderLocusAux_isSubgroup_iff` (in-file; 5 users).
- **Visibility**: private
- **Lines**: 2123–2128

### `ModularCurves.exactOrderLocusAux_psi_toE'`
- **Type**: private theorem
- **What**: `toE' (psi Q) = toE Q`.
- **How**: `pullback.lift_fst`.
- **Uses from project**: (in-file) `exactOrderLocusAux_psi`, `toE'`, `toE`.
- **Used by**: `psi_zero`, `psi_neg`, `psi_add`, `exactOrderLocusAux_isSubgroup_iff` (in-file; 4 users).
- **Visibility**: private
- **Lines**: 2130–2135

### `ModularCurves.exactOrderLocusAux_psi_zero` / `_psi_neg` / `_psi_add`
- **Type**: private theorems
- **What**: `psi` preserves 0, negation, addition.
- **How**: inject via `pt_ext'`, rewrite with `psi_toE'` and the matched-value lemmas.
- **Uses from project**: (in-file) `exactOrderLocusAux_pt_ext'`, `psi_toE'`, `toE_zero_eq`/`toE_neg`+`toE'_neg`/`toE_add_eq`.
- **Used by**: `exactOrderLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 2137–2143 / 2145–2151 / 2153–2161

### `ModularCurves.exactOrderLocusAux_factor_iff`
- **Type**: private theorem
- **What**: **Factorization dictionary**: `Q.1` factors through the base-changed universal order divisor over `E[N]` iff the matched `A.1` factors through the `t`-level order divisor.
- **How**: Reduce both sides to `comap = ⊥` (`subgroupLocusAux_factors_iff`); key ideal identity: unfold both order divisors to `∏ ker` (`orderDivisor_ideal`), push `comap` through with `Scheme.IdealSheafData.comap_prod` [ForMathlib], and compare factor-by-factor with `exactOrderLocusAux_ker_comap_eq`, fed by `val_isClosedImmersion`, `val_snd`, `match`, `val_fst_snd`, and `hm`. 29-line proof.
- **Hypotheses**: `hcP : c ≫ torsionι = P.1`; `hm : toE' A = toE Q`.
- **Uses from project**: (in-file) `subgroupLocusAux_factors_iff`, `exactOrderLocusAux_orderDivisor_ideal`, `exactOrderLocusAux_ker_comap_eq`, `exactOrderLocusAux_val_isClosedImmersion`, `subgroupLocusAux_val(_snd)`, `exactOrderLocusAux_match`, `exactOrderLocusAux_val_fst_snd`; `baseChange_ideal` [CartierDiv], `comap_prod` [ForMathlib], `Section.orderDivisor` [ExactOrder], `Point.asSection` [GroupLaw], `torsionι(_π)` [Torsion].
- **Used by**: `exactOrderLocusAux_isSubgroup_iff` (in-file).
- **Visibility**: private
- **Lines**: 2166–2210
- **Notes**: statement itself is 16 lines (two giant existentials) — statement-level abbreviation candidate.

### `ModularCurves.exactOrderLocusAux_isSubgroup_iff`
- **Type**: private theorem
- **What**: **IsSubgroup transport (KM 1.6.4 bookkeeping)**: the base-changed universal order divisor over `E[N]` is a subgroup iff the `t`-level order divisor is.
- **How**: In each direction transport the witnessing `AddSubgroup` through `phi` (resp. `psi`) — carrier is the preimage; closure by `phi_add/zero/neg` (resp. `psi_*`); the membership dictionary is `exactOrderLocusAux_factor_iff` with the matched value `phi_toE` (resp. `psi_toE'`).
- **Hypotheses**: `hct : c ≫ torsionπ = t`, `hcP : c ≫ torsionι = P.1`.
- **Uses from project**: (in-file) `exactOrderLocusAux_phi(_toE/_zero/_neg/_add)`, `exactOrderLocusAux_psi(_toE'/_zero/_neg/_add)`, `exactOrderLocusAux_factor_iff`; `RelEffCartierDiv.IsSubgroup` [ExactOrder], `Section.orderDivisor` [ExactOrder], `Point.asSection` [GroupLaw], `torsionι(_π)`, `torsionπ` [Torsion], `RelEffCartierDiv.baseChange` [CartierDiv].
- **Used by**: `exists_exactOrderLocus` (in-file).
- **Visibility**: private
- **Lines**: 2214–2261
- **Notes**: **proof 39 lines (>30)**; the two directions are verbatim-symmetric — decompose/abstraction candidate (a "transport IsSubgroup along a pointwise group iso with factor dictionary" helper).

### `ModularCurves.exists_exactOrderLocus`
- **Type**: theorem — (T-D17 = KM 1.6 for `A = ℤ/N`)
- **What**: There is a closed subscheme of `E[N]` universal for "the killed point has exact order `N`": for `P` with `P.1 ≫ [N] = t ≫ 0`, the classifying map `pointToTorsion P hP` factors through `Z` iff `asSection P` has exact order `N` on `E ×_S T`.
- **How**: Apply `exists_subgroupLocus` to the universal order divisor `Σₐ [a·P_univ]` over `E[N]` (with `P_univ = ⟨torsionι, torsionι_π⟩`), then translate with `exactOrderLocusAux_isSubgroup_iff` at `c = pointToTorsion P hP` (specs `pointToTorsion_torsionπ/_torsionι`). 8-line proof.
- **Hypotheses**: `[NeZero N]`; per-`T`: `P : E.Point t`, `hP` (killed by `N`).
- **Uses from project**: (in-file) `exists_subgroupLocus`, `exactOrderLocusAux_isSubgroup_iff`; `Section.orderDivisor`, `Section.HasExactOrder` [ExactOrder], `Point.asSection`, `mulByHom` [GroupLaw], `torsion`, `torsionι(_π)`, `pointToTorsion(_torsionπ/_torsionι)` [Torsion], `zero` [EC.Basic].
- **Used by**: [] (unused within these files).
- **Visibility**: public
- **Lines**: 2269–2281
- **Notes**: terminal deliverable (KM 1.6.1-style bootstrap).

### `ModularCurves.fullLevelLocusAux_torsionπ_lfp`
- **Type**: private theorem
- **What**: `E[N] ⟶ S` is locally of finite presentation.
- **How**: base change (`MorphismProperty.pullback_snd`) of `mulByHom_locallyOfFinitePresentation` [Torsion].
- **Uses from project**: `torsionπ`, `mulByHom_locallyOfFinitePresentation` [Torsion].
- **Used by**: `fullLevelLocusAux_torsionDivisor` (in-file).
- **Visibility**: private
- **Lines**: 2287–2289

### `ModularCurves.fullLevelLocusAux_torsionDivisor_prop`
- **Type**: private theorem
- **What**: Iso-invariant properties transfer from `torsionπ` to `(torsionIdeal N).subschemeι ≫ π`.
- **How**: `torsionIdeal_subscheme` [LS.Basic] gives the identifying iso `e`; `torsionι_π`; cancel with `cancel_left_of_respectsIso`.
- **Uses from project**: `torsionIdeal`, `torsionIdeal_subscheme` [LS.Basic], `torsionι_π` [Torsion].
- **Used by**: `fullLevelLocusAux_torsionDivisor` (×3) (in-file).
- **Visibility**: private
- **Lines**: 2291–2298

### `ModularCurves.fullLevelLocusAux_torsionDivisor`
- **Type**: private noncomputable def
- **What**: `E[N]` as a relative effective Cartier divisor in `E/S` (ideal = `torsionIdeal N`) — the ambient divisor of the full-level condition.
- **How**: fields by `torsionDivisor_prop` at `torsionπ_isFinite` / `torsionπ_flat` / `torsionπ_lfp`.
- **Uses from project**: (in-file) `fullLevelLocusAux_torsionDivisor_prop`, `fullLevelLocusAux_torsionπ_lfp`; `RelEffCartierDiv` [CartierDiv], `torsionIdeal` [LS.Basic], `torsionπ_isFinite`, `torsionπ_flat` [Torsion].
- **Used by**: `fullLevelLocusAux_P2`, `exists_fullLevelLocus` (in-file).
- **Visibility**: private
- **Lines**: 2302–2308
- **Notes**: `[NeZero N]` required (for finiteness).

### `ModularCurves.fullLevelLocusAux_torsionIdeal_baseChange`
- **Type**: private theorem
- **What**: **`E[N]`-formation commutes with base change at the ideal-sheaf level**: `(E ×_S Y).torsionIdeal N = (E.torsionIdeal N).comap (pullback.fst E.π s)`.
- **How**: RHS is `ker (pullback.fst (fst) (torsionι))` by `ker_fst_of_isClosedImmersion` (using `torsionι_isClosedImmersion`); build mutually-inverse-up-to-factoring comparison morphisms between `(E×Y)[N]` and `(E×Y) ×_E E[N]` with `pullback.lift` (`hκ` from `mulByHom_baseChange_fst` + `pullback.condition` + `zeroT_fst`); verify the second lift's condition by two giant leg computations (`l1…l10`, `m1…m6`, `r1…r3`, `s1…s2` with `mulByHom_baseChange_snd`, `zero_π`); close with `exactOrderLocusAux_ker_eq_of_comp`.
- **Hypotheses**: `E`, `N`, `s : Y ⟶ S`.
- **Uses from project**: (in-file) `exactOrderLocusAux_ker_eq_of_comp`, `exactOrderLocusAux_zeroT_fst`; `torsionIdeal` [LS.Basic], `torsionι(_π)`, `torsionι_isClosedImmersion`, `torsionπ` [Torsion], `mulByHom_baseChange_fst/_snd`, `baseChange` [GroupLaw], `zero_π` [EC.Basic].
- **Used by**: `fullLevelLocusAux_P2` (in-file).
- **Visibility**: private
- **Lines**: 2312–2468
- **Notes**: **proof ≈152 lines (>30) — the longest proof in the file**, entirely hand-rolled `congrArg`/`Category.assoc` chains with no `simp`/`calc` compression; top decompose+golf target (each leg computation is an extractable lemma).

### `ModularCurves.fullLevelLocusAux_u₁` / `fullLevelLocusAux_u₂`
- **Type**: private noncomputable defs
- **What**: The two tautological killed points of `E` over `E[N] ×_S E[N]` (first/second projection composed with `torsionι`).
- **How**: subtype constructors via `torsionι_π` (+ `pullback.condition` for `u₂`).
- **Uses from project**: `Point` [GroupLaw], `torsionπ`, `torsionι(_π)` [Torsion].
- **Used by**: `fullLevelLocusAux_match`, `fullLevelLocusAux_P1`, `exists_fullLevelLocus` (in-file; 3 users each).
- **Visibility**: private
- **Lines**: 2471–2474 / 2477–2481

### `ModularCurves.fullLevelLocusAux_sectionsDivisor_ideal`
- **Type**: theorem (public)
- **What**: Generic unfolding: `(sectionsDivisor F.π P).ideal = ∏ᵢ ker (P i).1`.
- **How**: unfold + `dif_pos ⟨inferInstance, F.smooth⟩`.
- **Uses from project**: `sectionsDivisor` [CartierDiv], `smooth` [EC.Basic].
- **Used by**: `fullLevelLocusAux_P1` (in-file).
- **Visibility**: public
- **Lines**: 2484–2488
- **Notes**: third copy of the `dif_pos` sectionsDivisor unfolding (see `exactOrderLocusAux_orderDivisor_ideal` note).

### `ModularCurves.fullLevelLocusAux_comp_mulByHom_pi`
- **Type**: private theorem
- **What**: `(P.1 ≫ [m]) ≫ E.π = 𝟙 T ≫ t` — multiples of points stay over the base.
- **How**: `mulByHom_π` + `P.2`.
- **Uses from project**: `mulByHom(_π)` [GroupLaw].
- **Used by**: `fullLevelLocusAux_pair_fst` (statement+proof), `fullLevelLocusAux_match` (in-file).
- **Visibility**: private
- **Lines**: 2490–2493

### `ModularCurves.fullLevelLocusAux_pair_fst`
- **Type**: private theorem
- **What**: The value of `m₁•asSection P + m₂•asSection Q` projected to `E` is the sum of `⟨P.1 ≫ [m₁]⟩ + ⟨Q.1 ≫ [m₂]⟩` in `E.Point (𝟙 T ≫ t)`.
- **How**: `toE'_add` then `subgroupLocusAux_add_comp` at `k = 𝟙 T`, legs by `val_smul_asSection_fst`. 19-line proof.
- **Uses from project**: (in-file) `exactOrderLocusAux_toE'_add(_pi)`, `subgroupLocusAux_add_comp`, `exactOrderLocusAux_val_smul_asSection_fst`, `fullLevelLocusAux_comp_mulByHom_pi`, `subgroupLocusAux_val`; `Point.asSection`, `mulByHom` [GroupLaw].
- **Used by**: `fullLevelLocusAux_match` (in-file).
- **Visibility**: private
- **Lines**: 2497–2522

### `ModularCurves.fullLevelLocusAux_match`
- **Type**: private theorem
- **What**: Universal and classified level-pair combinations have matched values along the classifying map `cc : T ⟶ E[N] ×_S E[N]`.
- **How**: `pair_fst` on both sides, then `subgroupLocusAux_add_comp` at `k = cc` with legs `hccP`/`hccQ` reassociated. 20-line proof.
- **Hypotheses**: `hccP : cc ≫ (fst ≫ torsionι) = P.1`, `hccQ : cc ≫ (snd ≫ torsionι) = Q.1`.
- **Uses from project**: (in-file) `fullLevelLocusAux_pair_fst`, `subgroupLocusAux_add_comp`, `fullLevelLocusAux_comp_mulByHom_pi`, `fullLevelLocusAux_u₁`, `fullLevelLocusAux_u₂`, `subgroupLocusAux_val`; `torsionπ`, `torsionι` [Torsion], `Point.asSection`, `mulByHom` [GroupLaw].
- **Used by**: `fullLevelLocusAux_P1` (in-file).
- **Visibility**: private
- **Lines**: 2526–2562

### `ModularCurves.fullLevelLocusAux_theta`
- **Type**: noncomputable def (public)
- **What**: The comparison morphism `pullback π t ⟶ pullback π b` over a factorization `c ≫ b = t`.
- **How**: `pullback.lift fst (snd ≫ c)`.
- **Hypotheses**: `hct : c ≫ b = t`.
- **Uses from project**: [].
- **Used by**: `theta_fst`, `theta_snd`, `comap_iff`, `P1`, `P2` (in-file; 5 users).
- **Visibility**: public
- **Lines**: 2565–2569
- **Notes**: generic pullback-pasting gadget; key aux, could live in a ForMathlib pullback file.

### `ModularCurves.fullLevelLocusAux_theta_fst` / `_theta_snd`
- **Type**: theorems (public)
- **What**: `θ ≫ fst = fst` and `θ ≫ snd = snd ≫ c`.
- **How**: `pullback.lift_fst/_snd`.
- **Uses from project**: (in-file) `fullLevelLocusAux_theta`.
- **Used by**: `comap_iff`, `P1`, `P2` (in-file; 3 / 2–3 users).
- **Visibility**: public
- **Lines**: 2571–2574 / 2576–2579

### `ModularCurves.fullLevelLocusAux_comap_iff`
- **Type**: theorem (public)
- **What**: **Comap-transport along the pasting comparison**: equality of comaps along `pullback.fst (snd π b) c` ⇔ equality of comaps along `θ` on `pullback π t`.
- **How**: exhibit each of the two comparison maps as a factor of the other (`hΨΘ` via `pullback.hom_ext`, `hhom` via `lift_fst`) and rewrite with `comap_comp` in both directions. 19-line proof.
- **Hypotheses**: `hct : c ≫ b = t`; `A B' : (pullback π b).IdealSheafData`.
- **Uses from project**: (in-file) `fullLevelLocusAux_theta(_fst/_snd)`.
- **Used by**: `exists_fullLevelLocus` (in-file).
- **Visibility**: public
- **Lines**: 2584–2608

### `ModularCurves.fullLevelLocusAux_P1`
- **Type**: private theorem
- **What**: **(P1)** The base-changed universal pair divisor (over `E[N]×E[N]`, indexed by `i : Fin (N²)` with coefficients `i % N`, `i / N`) pulls back along `θ` to the `t`-level pair divisor's ideal.
- **How**: Unfold both `sectionsDivisor` ideals (`fullLevelLocusAux_sectionsDivisor_ideal`), push comap through the product (`comap_prod` [ForMathlib]), and identify factors with `exactOrderLocusAux_ker_comap_eq`, fed by `val_isClosedImmersion`, `val_snd`, `fullLevelLocusAux_match`, `theta_snd/_fst`, at `w = 𝟙` (`comap_id`). 24-line proof (statement 24 more).
- **Hypotheses**: `hcct`, `hccP`, `hccQ` (classifying data of `(P,Q)`).
- **Uses from project**: (in-file) `exactOrderLocusAux_ker_comap_eq`, `fullLevelLocusAux_sectionsDivisor_ideal`, `exactOrderLocusAux_val_isClosedImmersion`, `subgroupLocusAux_val(_snd)`, `fullLevelLocusAux_match`, `fullLevelLocusAux_theta(_fst/_snd)`, `fullLevelLocusAux_u₁/u₂`; `sectionsDivisor` [CartierDiv], `comap_prod` [ForMathlib], `Point.asSection`, `baseChange` [GroupLaw], `torsionπ` [Torsion].
- **Used by**: `exists_fullLevelLocus` (in-file).
- **Visibility**: private
- **Lines**: 2612–2659

### `ModularCurves.fullLevelLocusAux_P2`
- **Type**: private theorem
- **What**: **(P2)** The base-changed universal torsion divisor pulls back along `θ` to the `t`-level torsion ideal.
- **How**: two applications of `fullLevelLocusAux_torsionIdeal_baseChange` (once at `b`, once at `t`) glued by `comap_comp` and `theta_fst`; explicit `e1/e2/e3` congrArg chain. 19-line proof.
- **Hypotheses**: `[NeZero N]`, `hcct`.
- **Uses from project**: (in-file) `fullLevelLocusAux_torsionDivisor`, `fullLevelLocusAux_torsionIdeal_baseChange`, `fullLevelLocusAux_theta(_fst)`; `torsionIdeal` [LS.Basic], `baseChange` [GroupLaw], `torsionπ` [Torsion].
- **Used by**: `exists_fullLevelLocus` (in-file).
- **Visibility**: private
- **Lines**: 2663–2688

### `ModularCurves.fullLevelLocusAux_killed`
- **Type**: private theorem
- **What**: A morphism-level killed point gives a group-theoretically killed section: `P.1 ≫ [N] = t ≫ 0 ⟹ (N : ℤ) • asSection P = 0`.
- **How**: inject via `pt_ext'`; `toE'` of both sides computed by `val_smul_asSection_fst` and `toE'_zero`.
- **Uses from project**: (in-file) `exactOrderLocusAux_pt_ext'`, `exactOrderLocusAux_toE'_zero`, `exactOrderLocusAux_val_smul_asSection_fst`; `Point.asSection`, `mulByHom` [GroupLaw], `zero` [EC.Basic].
- **Used by**: `exists_fullLevelLocus` (×2) (in-file).
- **Visibility**: private
- **Lines**: 2691–2697

### `ModularCurves.exists_fullLevelLocus`
- **Type**: theorem — (T-D18 = KM 1.5–1.6 for `A = (ℤ/N)²`)
- **What**: There is a closed subscheme of `E[N] ×_S E[N]` universal for "the killed pair `(P,Q)` is a Drinfeld full level-`N` structure": the lift `pullback.lift (pointToTorsion P hP) (pointToTorsion Q hQ)` factors through `Z` iff `(E ×_S T).IsFullLevel N (asSection P) (asSection Q)`.
- **How**: Apply `exists_incidenceLocusEQ` to the universal pair divisor (sections `(i%N)•u₁ + (i/N)•u₂`, `i : Fin (N²)`) vs the universal torsion divisor over `E[N]×E[N]`; the classifying data `hcct/hccP/hccQ` come from `pointToTorsion_torsionπ/_torsionι` + `pullback.lift_fst/snd`; rewrite double-`IsSubdivisor` as ideal equality (`isSubdivisor_iff_le`, `le_antisymm_iff`, `baseChange_ideal`); transport along `θ` (`fullLevelLocusAux_comap_iff`) and evaluate both sides by **P1** and **P2**; the two killedness conjuncts of `IsFullLevel` are discharged by `fullLevelLocusAux_killed` (`and_iff_right`). 38-line proof.
- **Hypotheses**: `[NeZero N]`; per-`T`: `P Q : E.Point t` with `hP hQ` killed by `N`.
- **Uses from project**: (in-file) `exists_incidenceLocusEQ`, `fullLevelLocusAux_u₁/u₂`, `fullLevelLocusAux_torsionDivisor`, `isSubdivisor_iff_le`, `fullLevelLocusAux_comap_iff`, `fullLevelLocusAux_P1`, `fullLevelLocusAux_P2`, `fullLevelLocusAux_killed`; `IsFullLevel` [LS.Basic], `sectionsDivisor`, `baseChange_ideal` [CartierDiv], `Point.asSection`, `mulByHom`, `baseChange` [GroupLaw], `torsionπ`, `pointToTorsion(_torsionπ/_torsionι)` [Torsion], `zero`, `smooth` [EC.Basic].
- **Used by**: [] (unused within these files).
- **Visibility**: public
- **Lines**: 2703–2749
- **Notes**: **proof 38 lines (>30)**; terminal deliverable — with the Weil-pairing decomposition this is the relative representability of `[Γ(N)]` (Loeffler Prop 3.8.2).

---

### File Summary — `projects/ModularCurves/ModularCurves/LevelStructure/IsoTransport.lean`

- **Totals**: 308 lines; 20 declarations (17 lemmas/theorems, 3 noncomputable defs — `pointMapOfHom`, `pointAddEquiv`, `schemeIsoOfOverIso`). Namespaces: 3 decls in `AlgebraicGeometry.Scheme.IdealSheafData`/`Scheme.Hom` (generic ideal-sheaf transport), 17 in `ModularCurves.EllipticCurve` (2 of them `_root_`-qualified: `RelEffCartierDiv.IsSubgroup.of_ideal_comap`; `Scheme.Hom.ker_comp_iso`/`ker_iso_comp` also `_root_`). Sorry-free by design (hypothesis-funneled on `hη`/`hμ`).
- **Key API (3+ in-file users)**: `pointMapOfHom` (5 users). Near-key (2 users each): `map_hom_eq_comap_inv`, `mul_comp_monHom`, `iso_hom_left_inv_left`, `iso_inv_left_hom_left`, `pointAddEquiv`, `schemeIsoOfOverIso`. Cross-file: the file's terminal results (`torsionIdeal_eq_comap`, `IsSubgroup.of_ideal_comap`, `HasExactOrder.pointMap`, `pointAddEquiv`) are the T-H8a iso-leg API for the Drinfeld functor laws.
- **Unused-in-file**: `one_comp_monHom` (completeness companion, no consumer here), `pointMapOfHom_coe` (@[simp] normal form), `torsionIdeal_eq_comap` (terminal), `Section.HasExactOrder.pointMap` (terminal).
- **CODE-sorry**: none (the word appears once in the module docstring, prose only).
- **set_option**: none. (File-level `attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory` at lines 48–49.)
- **Proofs >30 lines**: none (longest: `torsionIdeal_eq_comap`, 19-line proof).
- **Private/public**: 0 private / 20 public.
- **Other notes**: (1) module-docstring "Main results" advertises `Section.HasExactOrder.comp_iso` but the theorem is named `...pointMap` — doc/name mismatch. (2) The three `Scheme.IdealSheafData`/`Scheme.Hom` lemmas at the top are generic mathlib-shaped transport lemmas (upstream candidates). (3) `sectionsDivisor_pointMap_ideal` unfolds `sectionsDivisor` via `dif_pos` — shares this brittleness with two Incidence.lean lemmas (see below).

### File Summary — `projects/ModularCurves/ModularCurves/LevelStructure/Incidence.lean`

- **Totals**: 2,753 lines; 144 declarations = 118 theorems/lemmas + 26 defs (of which 21 noncomputable). 106 private / 38 public. Organized as: ZeroLocus (vanishing ideals, 4 decls) → SubmoduleVanishing (7) → lfp-of-fg (2) → VanishingLocus (15, KM 1.3.4 engine) → Incidence (`IsSubdivisor` + KM 1.3.4/1.3.5 loci, 6) → subgroupLocus Tiers 0–5 (52, KM 1.3.6⇔1.3.7 + T-D16/T-D33) → exactOrderLocus Tier 6 (38, T-D17) → fullLevelLocus Tier 7 (18, T-D18). No copyright header (starts at `import` — inconsistent with IsoTransport.lean).
- **Key API (3+ in-file users)**: `subgroupLocusAux_val` (~24 users — the raw-typed workhorse), `subgroupLocusAux_q` (~15), `exactOrderLocusAux_toE'` (~12), `exactOrderLocusAux_toE` (~10), `sectionVanishingIdeal` (8), `subgroupLocusAux_val_snd` (8), `submoduleVanishingIdeal` (7), `IsSubdivisor` (7), `vanishingLocus` (6), `subgroupLocusAux_le_ker_iff` (6), `subgroupLocusAux_mu` (6), `isSubdivisor_iff_le` (5), `subgroupLocusAux_{W,sum,zeroT,negT}` (5 each), `exactOrderLocusAux_{phi,psi}` (5 each), `fullLevelLocusAux_theta` (5), `exists_factor_subschemeι_iff` (4), `exists_incidenceLocusLE` (4), `subgroupLocusAux_{add_comp,val_fst_π}` (4 each), `exactOrderLocusAux_{toE'_pi,pt_ext',phi_toE,psi_toE'}` (4 each), plus ~15 more at exactly 3 (`le_ker_iff_forall`, `vanishingLocusAux_section_eq_zero`, `sectionVanishingIdeal_le_submoduleVanishingIdeal`, `subgroupLocusAux_{factors_iff,invD,P₁,P₂,sumDiv,Z3W,sigma,pairPt,zero_valT,neg_valT,negT_fst,add_fst}`, `exactOrderLocusAux_{zeroT_fst,val_fst_snd,toE_pi,toE'_neg,toE_neg,pt_ext,val_smul_asSection_fst}`, `fullLevelLocusAux_{u₁,u₂,theta_fst}`).
- **Unused-in-file**: `sectionVanishingIdeal_eq_span_coord_coord` (T-D27 — no consumer anywhere in these files), `vanishingLocus_subschemeι_lfp` (T-SG3-LFP-4a — lfp clause awaiting consumers), `exactOrderLocusAux_toE_neg_eq` (dead private lemma — `phi_neg`/`psi_neg` inline the rewrite), and the three terminal deliverables `exists_exactOrderLocus_section` (T-D33), `exists_exactOrderLocus` (T-D17), `exists_fullLevelLocus` (T-D18).
- **CODE-sorry**: none.
- **set_option**: none.
- **Proofs >30 lines** (13): `submoduleVanishingIdeal_fg` (36), `vanishingLocus` (`map_ideal_basicOpen` field, 57), `exists_affineOpen_mem_free` (89), `vanishingLocusAux_exists_basicOpen_free` (~87 — near-verbatim duplicate of the previous), `vanishingLocusAux_one_tmul_eq_zero` (35), `vanishingLocusAux_le_ker_snd` (86), `subgroupLocusAux_Z3_le_ker_iff` (48), `subgroupLocusAux_isSubgroup_iff` (117), `exactOrderLocusAux_ker_comap_eq` (36), `exactOrderLocusAux_toE_zero` (32), `exactOrderLocusAux_isSubgroup_iff` (39), `fullLevelLocusAux_torsionIdeal_baseChange` (~152 — longest; pure assoc-shuffling), `exists_fullLevelLocus` (38). Borderline at 29–30: `submoduleVanishingIdeal_localized` (30), `exactOrderLocusAux_factor_iff` (29), `exactOrderLocusAux_toE_neg` (28).
- **Private/public**: 106 private / 38 public. Public list: the ZeroLocus/SubmoduleVanishing layer (11), `lfp_subschemeι_of_fg(_cover)` (2), `affinePreimage`, `vanishingLocus`, `exists_affineOpen_mem_free`, `le_ker_iff_forall`, `vanishingLocus_le_ker_iff`, `vanishingLocus_subschemeι_lfp`, `IsSubdivisor`, `isSubdivisor_iff_le`, `exists_factor_subschemeι_iff`, `exists_incidenceLocusLE`, `exists_incidenceLocusEQ`, `exists_subgroupLocus`, `exists_exactOrderLocus_section`, `exists_exactOrderLocus`, `exists_fullLevelLocus`, and 10 `Aux`-named-but-public helpers (`subgroupLocusAux_val(_snd)`, `exactOrderLocusAux_ker_comap_eq`, `exactOrderLocusAux_val_isClosedImmersion`, `exactOrderLocusAux_val_smul_asSection_fst`, `fullLevelLocusAux_sectionsDivisor_ideal`, `fullLevelLocusAux_theta(_fst/_snd)`, `fullLevelLocusAux_comap_iff`) — rename-or-privatize candidates depending on external consumers.
- **Other notes / consolidation leads**: (1) **~90-line duplication** `exists_affineOpen_mem_free` ↔ `vanishingLocusAux_exists_basicOpen_free` (docstring admits "same proof"); extract the shared free-spreading core. (2) Three copies of the `sectionsDivisor`-`dif_pos` unfolding across the two files (`exactOrderLocusAux_orderDivisor_ideal`, `fullLevelLocusAux_sectionsDivisor_ideal`, IsoTransport's `sectionsDivisor_pointMap_ideal`) — a public `sectionsDivisor_ideal` lemma in CartierDivisor.lean would remove all three. (3) `fullLevelLocusAux_torsionIdeal_baseChange` (152 lines) and `exactOrderLocusAux_toE_zero`/`_toE_neg` are pure associativity chains written `congrArg`-by-`congrArg` (per the Tier-2 "raw-typed" discipline to dodge `rw`-motive traps) — golf with `simp only [Category.assoc, pullback.lift_fst/snd, …]` or extraction. (4) `subgroupLocusAux_le_ker_iff` duplicates the Galois step already inside `vanishingLocus_le_ker_iff` proof. (5) `affinePreimage` defined but the same subtype is re-spelled literally inside `vanishingLocus`. (6) `hsm : SmoothOfRelativeDimension 1 π` is passed to `exists_incidenceLocusLE`/`EQ` but never used in their proofs (instances suffice) — signature audit. (7) `RelEffCartierDiv.baseChange` note at lines 953–954 records the 2026-07-06 move to CartierDivisor.lean.
