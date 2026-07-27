# Inventory: `projects/ModularCurves/ModularCurves/ModularCurve/YOneAtlasClassify.lean`

Phase-1 /overview inventory. File: 5,905 lines, module docstring "The Y₁ Tate-atlas classifying
clause: local algebra" — the NEW-ATLAS workspace for the classifying part of `exists_tatePoint`
(Loeffler Cor 3.3.5). Imports: `ModularCurves.ModularCurve.YOneAssembly`,
`ModularCurves.Moduli.QuotientProblem`, `ModularCurves.EllipticCurve.Comparison`.
`attribute [local instance] MvPolynomial.gradedAlgebra` (line 16). Everything in
`namespace ModularCurves`. No `sorry` anywhere (verified by grep). No `set_option` anywhere.

Notation used below: Γ(U) abbreviates `↑Γ(Y.base, D.U.1)`; "atlas ring" = `tateRingOver R`
(imported); "atlas" = `tateBase R`; "universal Tate curve" = `tateCurveLocOver R`;
"the marking" = `tateP0mor R` / `tateMarkedPoint R` (all imported from YOneAssembly).

---

## Section `RelativeTateRing` (lines 22–736)

### `noncomputable def tateRingOverLift`
- **Type**: `(R : CommRingCat) {A} [CommRing A] [Algebra R A] (α β : A) (hΔ : IsUnit (((tateCurveOver R).map (eval₂Hom (algebraMap R A) (if i = 0 then α else β))).Δ)) : tateRingOver R →+* A`
- **What**: The relative Tate-ring map attached to coefficients (α, β) over an R-algebra: the universal map out of the localization of R[A,B] away from the Tate discriminant.
- **Hypotheses**: The Tate-normal discriminant of the specialised curve is a unit.
- **Uses from project**: `tateRingOver`, `tateCurveOver` (imported); mathlib `IsLocalization.Away.lift`, `WeierstrassCurve.map_Δ`.
- **Used by**: `tateRingOverLift_X_zero/_X_one`, `tateRingOverAlgLift`, `tateRingOver_algHom_eq_lift`, `tateCurveLocOver_map_tateRingOverLift`, `tateRingOverLiftOfTateNormal`.
- **Visibility**: public
- **Lines**: 29–36 (term-mode, 8 lines)
- **Notes**: —

### `theorem tateRingOverLift_X_zero`
- **Type**: `tateRingOverLift R α β hΔ (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (X 0)) = α`
- **What**: The lift sends the first universal Tate coordinate to α.
- **Hypotheses**: as `tateRingOverLift`.
- **Uses from project**: `tateRingOverLift`, `tateRingOver`, `tateCurveOver`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 38–44 (proof 2 lines)
- **Notes**: @[simp]

### `theorem tateRingOverLift_X_one`
- **Type**: symmetric statement for `X 1` ↦ β.
- **What**: The lift sends the second universal Tate coordinate to β.
- **Hypotheses**: as `tateRingOverLift`.
- **Uses from project**: `tateRingOverLift`, `tateRingOver`, `tateCurveOver`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 46–52 (proof 2 lines)
- **Notes**: @[simp]

### `noncomputable def tateRingOverAlgLift`
- **Type**: same data as `tateRingOverLift`, bundled as `tateRingOver R →ₐ[R] A`
- **What**: The relative Tate-ring lift as an R-algebra map (the form used by affine maps over Spec R).
- **Hypotheses**: discriminant unit condition.
- **Uses from project**: `tateRingOverLift`, `tateRingOver`, `tateCurveOver`.
- **Used by**: `tateRingOverAlgLift_X_zero/_X_one`, `tateRingOver_algHom_eq_algLift`, `tateBaseSpecMapOfCoeffs`, `tateBaseMapOfGlobalCoeffs_ext`, `tateBaseSpecMapOfCoeffs_tateStructMap`, `tateCurveLocOver_map_tateRingOverAlgLift`, `tateRingOverAlgLiftOfTateNormal`.
- **Visibility**: public
- **Lines**: 56–64 (structure instance, 9 lines)
- **Notes**: —

### `theorem tateRingOverAlgLift_X_zero`
- **Type**: `tateRingOverAlgLift R α β hΔ (algebraMap … (X 0)) = α`
- **What**: Algebra-map version of the first coordinate computation.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOverAlgLift`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 66–72 (proof 2 lines)
- **Notes**: @[simp]

### `theorem tateRingOverAlgLift_X_one`
- **Type**: `tateRingOverAlgLift R α β hΔ (algebraMap … (X 1)) = β`
- **What**: Algebra-map version of the second coordinate computation.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOverAlgLift`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 74–80 (proof 2 lines)
- **Notes**: @[simp]

### `theorem tateRingOver_algHom_ext`
- **Type**: `(φ ψ : tateRingOver R →ₐ[R] A) → φ (X 0) = ψ (X 0) → φ (X 1) = ψ (X 1) → φ = ψ` (coordinates via `algebraMap (MvPolynomial (Fin 2) R)`)
- **What**: Two R-algebra maps out of the atlas ring agree once they agree on the two Tate coordinates — the ring-level overlap-uniqueness handle.
- **How**: Reduces along `IsLocalization.ringHom_ext (Submonoid.powers (tateCurveOver R).Δ)` then `MvPolynomial.ringHom_ext`, using `AlgHom.commutes` on constants and `fin_cases` on the two variables.
- **Hypotheses**: agreement on both coordinates.
- **Uses from project**: `tateRingOver`, `tateCurveOver`.
- **Used by**: `tateRingOver_algHom_eq_algLift`, `tateBaseSpecMap_ext`, `tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`, `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `projTateMap_map_tate`.
- **Visibility**: public
- **Lines**: 85–103 (proof ~13 lines)
- **Notes**: —

### `theorem tateRingOver_algHom_eq_lift`
- **Type**: an algebra map φ with prescribed coordinate values α, β equals `tateRingOverLift R α β hΔ` (as a ring hom)
- **What**: The relative Tate-ring lift is the unique R-algebra map with the prescribed Tate coordinates.
- **How**: `IsLocalization.ringHom_ext` + `MvPolynomial.ringHom_ext`, constants via `φ.commutes`, variables via `fin_cases` and the hypotheses.
- **Hypotheses**: hΔ unit condition; h0/h1 coordinate values.
- **Uses from project**: `tateRingOverLift`, `tateRingOver`, `tateCurveOver`.
- **Used by**: unused in file (mentioned only in the docstring of `tateRingOver_algHom_eq_algLift`).
- **Visibility**: public
- **Lines**: 108–123 (proof ~10 lines)
- **Notes**: —

### `theorem tateRingOver_algHom_eq_algLift`
- **Type**: same as previous but concluding `φ = tateRingOverAlgLift R α β hΔ` as algebra maps
- **What**: Algebra-map version of the uniqueness of the lift.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOver_algHom_ext`, `tateRingOverAlgLift`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 126–134 (proof 4 lines)
- **Notes**: —

### `noncomputable def tateBaseSpecMap`
- **Type**: `(φ : tateRingOver R →ₐ[R] A) : Spec (.of A) ⟶ tateBase R`
- **What**: The affine scheme map to the relative Tate atlas induced by an algebra map out of the atlas ring (`Spec.map` of φ).
- **Hypotheses**: none beyond the algebra structure.
- **Uses from project**: `tateRingOver`, `tateBase`.
- **Used by**: `tateBaseSpecMapOfCoeffs`, `tateBaseSpecMap_ext`, `tateBaseSpecMap_tateStructMap`, `tateBaseSpecMapOfTateNormal`, `tateBaseSpecMapOfPoint`, `tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`.
- **Visibility**: public
- **Lines**: 138–140
- **Notes**: —

### `noncomputable def tateBaseSpecMapOfCoeffs`
- **Type**: `(α β : A) (hΔ : …) : Spec (.of A) ⟶ tateBase R`
- **What**: The affine map to the atlas classified by coefficients (α, β).
- **Hypotheses**: hΔ unit condition.
- **Uses from project**: `tateBaseSpecMap`, `tateRingOverAlgLift`.
- **Used by**: `tateBaseSpecMapOfCoeffs_tateStructMap`, `tateBaseMapOfGlobalCoeffs`, `tateBaseMapOfGlobalCoeffs_ext`.
- **Visibility**: public
- **Lines**: 143–147
- **Notes**: —

### `theorem tateBaseSpecMap_ext`
- **Type**: `tateBaseSpecMap R φ = tateBaseSpecMap R ψ` given coordinate agreement of φ, ψ
- **What**: Equality of affine maps into the atlas reduces to equality of the two Tate coordinates.
- **Hypotheses**: h0, h1 coordinate agreement.
- **Uses from project**: `tateRingOver_algHom_ext`, `tateBaseSpecMap`.
- **Used by**: `tateBaseMapOfGlobalCoeffs_ext`, `tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`.
- **Visibility**: public
- **Lines**: 151–157 (proof 1 line)
- **Notes**: —

### `theorem tateBaseSpecMap_tateStructMap`
- **Type**: `tateBaseSpecMap R φ ≫ tateStructMap R = Spec.map (ofHom (algebraMap R A))`
- **What**: The affine map induced by an atlas algebra map lies over Spec R.
- **How**: unfolds both maps, `Spec.map_comp` and `RingHom.ext` via `φ.commutes`.
- **Hypotheses**: none extra.
- **Uses from project**: `tateBaseSpecMap`, `tateStructMap` (imported).
- **Used by**: `tateBaseSpecMapOfCoeffs_tateStructMap`, `tateBaseSpecMapOfTateNormal_tateStructMap`, `tateBaseSpecMapOfPoint_tateStructMap`.
- **Visibility**: public
- **Lines**: 161–167 (proof 4 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfCoeffs_tateStructMap`
- **Type**: coefficient version of the previous statement
- **What**: The coefficient-classifying affine map lies over Spec R.
- **Hypotheses**: hΔ.
- **Uses from project**: `tateBaseSpecMap_tateStructMap`, `tateRingOverAlgLift`.
- **Used by**: `tateBaseMapOfGlobalCoeffs_tateStructMap`.
- **Visibility**: public
- **Lines**: 170–175 (term proof)
- **Notes**: —

### `noncomputable def tateBaseMapOfGlobalCoeffs`
- **Type**: `(S : Scheme) [Algebra R Γ(S,⊤)] (α β : Γ(S,⊤)) (hΔ : …) : S ⟶ tateBase R`
- **What**: The global classifying map to the atlas attached to global Tate coefficients, i.e. `S.toSpecΓ ≫ tateBaseSpecMapOfCoeffs`.
- **Hypotheses**: hΔ on global sections.
- **Uses from project**: `tateBaseSpecMapOfCoeffs`, `tateBase`, `tateCurveOver`.
- **Used by**: `tateBaseMapOfGlobalCoeffs_ext`, `tateBaseMapOfGlobalCoeffs_tateStructMap`, `tateBaseMapOfGlobalCoeffs_base_w`, `EllObj.tateBaseMapOfGlobalCoeffs`.
- **Visibility**: public
- **Lines**: 182–186
- **Notes**: —

### `theorem tateBaseMapOfGlobalCoeffs_ext`
- **Type**: equal coefficient pairs (α,β) = (α',β') give equal global maps
- **What**: Global maps built from equal global coefficients are equal (the affine uniqueness check after sheaf gluing).
- **How**: unfolds to `tateBaseSpecMap_ext` on the two `tateRingOverAlgLift`s and closes with simp.
- **Hypotheses**: hΔ, hΔ', hα : α = α', hβ : β = β'.
- **Uses from project**: `tateBaseSpecMap_ext`, `tateRingOverAlgLift`, `tateBaseMapOfGlobalCoeffs`, `tateBaseSpecMapOfCoeffs`.
- **Used by**: `EllObj.tateBaseMapOfGlobalCoeffs_ext`.
- **Visibility**: public
- **Lines**: 191–203 (proof 6 lines)
- **Notes**: —

### `theorem tateBaseMapOfGlobalCoeffs_tateStructMap`
- **Type**: `tateBaseMapOfGlobalCoeffs R S α β hΔ ≫ tateStructMap R = S.toSpecΓ ≫ Spec.map (ofHom (algebraMap R Γ(S,⊤)))`
- **What**: The global coefficient map is compatible with the structure map to Spec R.
- **Hypotheses**: hΔ.
- **Uses from project**: `tateBaseMapOfGlobalCoeffs`, `tateBaseSpecMapOfCoeffs_tateStructMap`, `tateStructMap`.
- **Used by**: `tateBaseMapOfGlobalCoeffs_base_w`.
- **Visibility**: public
- **Lines**: 207–213 (proof 2 lines)
- **Notes**: —

### `noncomputable def EllObj.structAlgebra`
- **Type**: `(Y : EllObj R) : Algebra R Γ(Y.base, ⊤)`
- **What**: The R-algebra on global functions induced by an Ell/R object's structure morphism (via `ΓSpecIso` and `appTop`).
- **Hypotheses**: none.
- **Uses from project**: `EllObj` (imported).
- **Used by**: `EllObj.structAlgebra_algebraMap`, and as `letI` in `EllObj.tateBaseMapOfGlobalCoeffs`, `EllObj.tateBaseMapOfGlobalCoeffs_base_w/_ext`, `EllObj.tateClassifyingHomOfGlobalCoeffs` + its lemmas (16 dot-notation uses).
- **Visibility**: public
- **Lines**: 216–218
- **Notes**: @[reducible]

### `theorem EllObj.structAlgebra_algebraMap`
- **Type**: with `structAlgebra` installed, `algebraMap R Γ(Y.base,⊤) = ((Scheme.ΓSpecIso R).inv ≫ Y.structMap.appTop).hom`
- **What**: The defining equation of the induced algebra (rfl).
- **Hypotheses**: none.
- **Uses from project**: `EllObj.structAlgebra`.
- **Used by**: `EllObj.tateBaseMapOfGlobalCoeffs_base_w`.
- **Visibility**: public
- **Lines**: 220–224 (rfl)
- **Notes**: —

### `theorem EllObj.toSpecΓ_algebraMap_eq_structMap`
- **Type**: if the algebra on Γ(Y.base,⊤) is the induced one, then `Y.base.toSpecΓ ≫ Spec.map (algebraMap …) = Y.structMap`
- **What**: The ΓSpec adjunction pins the structure morphism against the induced algebra.
- **How**: rewrites with `Spec.map_comp` and mathlib's `Scheme.toSpecΓ_naturality`, closing with `toSpecΓ_SpecMap_ΓSpecIso_inv`.
- **Hypotheses**: halg (the algebra equals the induced one).
- **Uses from project**: `EllObj`.
- **Used by**: `tateBaseMapOfGlobalCoeffs_base_w`.
- **Visibility**: public
- **Lines**: 228–240 (proof ~8 lines)
- **Notes**: —

### `theorem tateBaseMapOfGlobalCoeffs_base_w`
- **Type**: `tateBaseMapOfGlobalCoeffs R Y.base α β hΔ ≫ tateStructMap R = Y.structMap` under halg
- **What**: The global coefficient map gives the correct Ell/R base component when the algebra comes from the structure map.
- **Hypotheses**: halg; hΔ.
- **Uses from project**: `tateBaseMapOfGlobalCoeffs_tateStructMap`, `EllObj.toSpecΓ_algebraMap_eq_structMap`.
- **Used by**: `EllObj.tateBaseMapOfGlobalCoeffs_base_w`.
- **Visibility**: public
- **Lines**: 244–254 (proof 2 lines)
- **Notes**: —

### `noncomputable def EllObj.tateBaseMapOfGlobalCoeffs`
- **Type**: `(Y : EllObj R) (α β : Γ(Y.base,⊤)) (hΔ : letI := Y.structAlgebra; …) : Y.base ⟶ tateBase R`
- **What**: The base map to the atlas attached to global coefficients on an Ell/R object (installs `structAlgebra` and delegates).
- **Hypotheses**: hΔ under the induced algebra.
- **Uses from project**: `EllObj.structAlgebra`, `ModularCurves.tateBaseMapOfGlobalCoeffs`.
- **Used by**: `EllObj.tateBaseMapOfGlobalCoeffs_base_w/_ext`, `EllObj.tateClassifyingHomOfGlobalCoeffs` and its three lemmas.
- **Visibility**: public
- **Lines**: 257–264
- **Notes**: —

### `theorem EllObj.tateBaseMapOfGlobalCoeffs_base_w`
- **Type**: `EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ ≫ tateStructMap R = Y.structMap`
- **What**: The Ell-object global-coefficient base map lies over the structure map.
- **Hypotheses**: hΔ.
- **Uses from project**: `ModularCurves.tateBaseMapOfGlobalCoeffs_base_w`, `EllObj.structAlgebra_algebraMap`.
- **Used by**: `EllObj.tateClassifyingHomOfGlobalCoeffs`.
- **Visibility**: public
- **Lines**: 266–275 (proof 3 lines)
- **Notes**: @[simp]

### `theorem EllObj.tateBaseMapOfGlobalCoeffs_ext`
- **Type**: coefficientwise congruence for `EllObj.tateBaseMapOfGlobalCoeffs`
- **What**: Equal global coefficients give equal Ell-object base maps.
- **Hypotheses**: hΔ, hΔ', hα, hβ.
- **Uses from project**: `ModularCurves.tateBaseMapOfGlobalCoeffs_ext`, `EllObj.structAlgebra`.
- **Used by**: `EllObj.tateClassifyingHomOfGlobalCoeffs_ext`.
- **Visibility**: public
- **Lines**: 277–289 (proof 2 lines)
- **Notes**: —

### `noncomputable def EllObj.tateBaseMapOfOpenCover`
- **Type**: `(𝒰 : Y.base.OpenCover) (g : ∀ i, 𝒰.X i ⟶ tateBase R) (hcompat : pullback-compatibility) : Y.base ⟶ tateBase R`
- **What**: Glue local maps to the atlas base along an open cover of the Ell-object base (via `𝒰.glueMorphisms`).
- **Hypotheses**: hcompat on overlaps.
- **Uses from project**: `tateBase`; mathlib `Scheme.Cover.glueMorphisms`.
- **Used by**: `EllObj.ι_tateBaseMapOfOpenCover`, `EllObj.tateBaseMapOfOpenCover_base_w/_ext`, `EllObj.tateClassifyingHomOfOpenCover` family, `MarkedChartData.gluedBaseMap`.
- **Visibility**: public
- **Lines**: 292–298
- **Notes**: —

### `theorem EllObj.ι_tateBaseMapOfOpenCover`
- **Type**: `𝒰.f i ≫ tateBaseMapOfOpenCover … = g i`
- **What**: The glued base map restricts to the given local maps.
- **Hypotheses**: hcompat.
- **Uses from project**: `EllObj.tateBaseMapOfOpenCover`.
- **Used by**: `EllObj.tateBaseMapOfOpenCover_base_w`, `EllObj.tateBaseMapOfOpenCover_ext`, `MarkedChartData.ι_gluedBaseMap`.
- **Visibility**: public
- **Lines**: 300–308 (term proof)
- **Notes**: @[reassoc (attr := simp)]

### `theorem EllObj.tateBaseMapOfOpenCover_base_w`
- **Type**: if each local map lies over Spec R (hover), the glued map lies over Y.structMap
- **What**: Over-Spec R property is glued along the cover.
- **Hypotheses**: hcompat, hover.
- **Uses from project**: `EllObj.tateBaseMapOfOpenCover`, `EllObj.ι_tateBaseMapOfOpenCover`, `tateStructMap`.
- **Used by**: `EllObj.tateClassifyingHomOfOpenCover`, `MarkedChartData.gluedBaseMap_over`.
- **Visibility**: public
- **Lines**: 311–321 (proof 4 lines)
- **Notes**: @[simp]

### `theorem EllObj.tateBaseMapOfOpenCover_ext`
- **Type**: pointwise-equal local families glue to equal maps
- **What**: Extensionality of the glued base map in the local family.
- **Hypotheses**: hcompat, hcompat', hg : ∀ i, g i = g' i.
- **Uses from project**: `EllObj.tateBaseMapOfOpenCover`, `EllObj.ι_tateBaseMapOfOpenCover`.
- **Used by**: `EllObj.tateClassifyingHomOfOpenCover_ext`.
- **Visibility**: public
- **Lines**: 323–336 (proof 4 lines)
- **Notes**: —

### `noncomputable def EllObj.tateClassifyingHom`
- **Type**: `(baseMap : Y.base ⟶ tateBase R) (base_w) (top : Y.curve.E ⟶ (tateUniversal R).E) (isPullback : IsPullback top Y.curve.π (tateUniversal R).π baseMap) (zero_w) : Y ⟶ tateEllObj R`
- **What**: Build an Ell/R morphism into the Tate object from a base map and a cartesian pointed top map — the assembly constructor for classifying morphisms.
- **Hypotheses**: base_w over Spec R, cartesianness, zero-compatibility.
- **Uses from project**: `tateBase`, `tateUniversal`, `tateEllObj`, `tateStructMap` (all imported), `EllHom` fields.
- **Used by**: `EllObj.tateClassifyingHom_baseHom/_top/_ext`, `EllObj.tateClassifyingHomOfGlobalCoeffs`, `EllObj.tateClassifyingHomOfOpenCover`, `EllObj.tateClassifyingHom_pullSection_top/_pullSection_eq/_existsUnique_of_components`, `MarkedChartData.gluedHom`.
- **Visibility**: public
- **Lines**: 340–353 (structure instance, simpa discharges)
- **Notes**: —

### `theorem EllObj.tateClassifyingHom_baseHom`
- **Type**: `(tateClassifyingHom …).baseHom = baseMap`
- **What**: Component computation (rfl).
- **Hypotheses**: constructor arguments.
- **Uses from project**: `EllObj.tateClassifyingHom`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 355–363 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHom_top`
- **Type**: `(tateClassifyingHom …).top = top`
- **What**: Component computation (rfl).
- **Hypotheses**: constructor arguments.
- **Uses from project**: `EllObj.tateClassifyingHom`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 365–372 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHom_ext`
- **Type**: two `tateClassifyingHom`s with equal baseMap and top are equal
- **What**: Extensionality via `EllHom.ext`.
- **Hypotheses**: hbase, htop.
- **Uses from project**: `EllObj.tateClassifyingHom`, `EllHom.ext` (imported).
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 374–386 (term proof)
- **Notes**: —

### `noncomputable def EllObj.tateClassifyingHomOfGlobalCoeffs`
- **Type**: classifying hom whose base map is `EllObj.tateBaseMapOfGlobalCoeffs R Y α β hΔ`
- **What**: The classifying morphism into tateEllObj after local Tate coefficients have glued to global sections.
- **Hypotheses**: hΔ, isPullback, zero_w for the coefficient base map.
- **Uses from project**: `EllObj.tateClassifyingHom`, `EllObj.tateBaseMapOfGlobalCoeffs`, `EllObj.tateBaseMapOfGlobalCoeffs_base_w`, `tateUniversal`, `tateEllObj`.
- **Used by**: its own three lemmas (`_baseHom`, `_top`, `_ext`) only.
- **Visibility**: public
- **Lines**: 390–402
- **Notes**: —

### `theorem EllObj.tateClassifyingHomOfGlobalCoeffs_baseHom`
- **Type**: baseHom computation (rfl)
- **What**: The base component is the global-coefficient map.
- **Hypotheses**: constructor arguments.
- **Uses from project**: `EllObj.tateClassifyingHomOfGlobalCoeffs`, `EllObj.tateBaseMapOfGlobalCoeffs`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 404–417 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHomOfGlobalCoeffs_top`
- **Type**: top computation (rfl)
- **What**: The top component is the given top map.
- **Hypotheses**: constructor arguments.
- **Uses from project**: `EllObj.tateClassifyingHomOfGlobalCoeffs`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 419–432 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHomOfGlobalCoeffs_ext`
- **Type**: congruence in (α, β, top)
- **What**: Classifying homs of equal coefficients and tops are equal.
- **Hypotheses**: hα, hβ, htop plus both squares' data.
- **Uses from project**: `EllHom.ext`, `EllObj.tateBaseMapOfGlobalCoeffs_ext`, `EllObj.tateClassifyingHomOfGlobalCoeffs`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 434–454 (term proof)
- **Notes**: —

### `noncomputable def EllObj.tateClassifyingHomOfOpenCover`
- **Type**: classifying hom whose base map is `EllObj.tateBaseMapOfOpenCover R Y 𝒰 g hcompat`
- **What**: The classifying morphism into tateEllObj from a Tate-base map glued over an open cover.
- **Hypotheses**: hcompat, hover, isPullback, zero_w.
- **Uses from project**: `EllObj.tateClassifyingHom`, `EllObj.tateBaseMapOfOpenCover`, `EllObj.tateBaseMapOfOpenCover_base_w`.
- **Used by**: its own three lemmas only.
- **Visibility**: public
- **Lines**: 458–472
- **Notes**: —

### `theorem EllObj.tateClassifyingHomOfOpenCover_baseHom`
- **Type**: baseHom computation (rfl)
- **What**: Base component is the glued cover map.
- **Hypotheses**: constructor data.
- **Uses from project**: `EllObj.tateClassifyingHomOfOpenCover`, `EllObj.tateBaseMapOfOpenCover`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 474–489 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHomOfOpenCover_top`
- **Type**: top computation (rfl)
- **What**: Top component is the given top map.
- **Hypotheses**: constructor data.
- **Uses from project**: `EllObj.tateClassifyingHomOfOpenCover`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 491–506 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHomOfOpenCover_ext`
- **Type**: congruence in (g, top)
- **What**: Cover-glued classifying homs of pointwise-equal local families and equal tops agree.
- **Hypotheses**: hg, htop plus both squares' data.
- **Uses from project**: `EllHom.ext`, `EllObj.tateBaseMapOfOpenCover_ext`, `EllObj.tateClassifyingHomOfOpenCover`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 508–531 (term proof)
- **Notes**: —

### `theorem EllObj.tateClassifyingHom_pullSection_top`
- **Type**: `(EllHom.pullSection R (tateClassifyingHom …) P₀).1 ≫ top = baseMap ≫ P₀.1`
- **What**: The pulled section of a classifying hom composes with top as the base map composes with the universal section.
- **Hypotheses**: constructor data, P₀ a section of tateUniversal.
- **Uses from project**: `EllHom.pullSection` (imported), `EllObj.tateClassifyingHom`; `IsPullback.lift_fst`.
- **Used by**: unused in file (leaf @[reassoc simp]).
- **Visibility**: public
- **Lines**: 533–545 (proof 2 lines)
- **Notes**: @[reassoc (attr := simp)]

### `theorem EllObj.tateClassifyingHom_pullSection_eq`
- **Type**: if `P.1 ≫ top = baseMap ≫ P₀.1` then `EllHom.pullSection R (tateClassifyingHom …) P₀ = P`
- **What**: The classifying hom pulls the universal section back to a prescribed section — the existence-side computation.
- **How**: `Subtype.ext` + `IsPullback.hom_ext` of the hom's own square, using `lift_fst` and the section property.
- **Hypotheses**: hP compatibility of P with top over P₀.
- **Uses from project**: `EllHom.pullSection`, `EllObj.tateClassifyingHom`, `tateEllObj`.
- **Used by**: `EllObj.tateClassifyingHom_existsUnique_of_components`, `MarkedChartData.gluedHom_pullSection`.
- **Visibility**: public
- **Lines**: 547–563 (proof ~8 lines)
- **Notes**: —

### `theorem EllObj.tateClassifyingHom_existsUnique_of_components`
- **Type**: given the square data, a section P with hP, and huniq (any f with pullSection f P₀ = P has the same components), conclude `∃! f : Y ⟶ tateEllObj R, EllHom.pullSection R f P₀ = P`
- **What**: Packaging of the classifying clause: component-uniqueness upgrades the constructed hom to the unique classifying hom.
- **Hypotheses**: base_w, isPullback, zero_w, hP, huniq.
- **Uses from project**: `EllObj.tateClassifyingHom`, `EllObj.tateClassifyingHom_pullSection_eq`, `EllHom.ext`, `EllHom.pullSection`.
- **Used by**: `MarkedChartData.tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 565–582 (proof ~7 lines)
- **Notes**: —

### `noncomputable def EllObj.tateClassifyingHomOfPullbackMap`
- **Type**: `(baseMap : Y.base ⟶ tateBase R) (v : Y ⟶ (tateEllObj R).pullbackAlong baseMap) : Y ⟶ tateEllObj R`
- **What**: The Tate classifying morphism in tautological pullback shape (`v ≫ pullbackAlongπ`) — the QuotientProblem/pullbackAlong reuse path (v10.89).
- **Hypotheses**: none.
- **Uses from project**: `EllObj.pullbackAlong`, `EllObj.pullbackAlongπ` (imported from Moduli.QuotientProblem), `tateEllObj`.
- **Used by**: `_baseHom`, `_baseHom_of_base_id`, `_toPullbackAlong`, `toPullbackAlong_tateClassifyingHomOfPullbackMap`, `_pullSection`.
- **Visibility**: public
- **Lines**: 586–590
- **Notes**: —

### `theorem EllObj.tateClassifyingHomOfPullbackMap_baseHom`
- **Type**: `(tateClassifyingHomOfPullbackMap …).baseHom = v.baseHom ≫ baseMap` (rfl)
- **What**: Base component of the pullback-shaped classifying hom.
- **Hypotheses**: none.
- **Uses from project**: `EllObj.tateClassifyingHomOfPullbackMap`.
- **Used by**: `EllObj.tateClassifyingHomOfPullbackMap_baseHom_of_base_id`.
- **Visibility**: public
- **Lines**: 592–598 (rfl)
- **Notes**: @[simp]

### `theorem EllObj.tateClassifyingHomOfPullbackMap_baseHom_of_base_id`
- **Type**: if `v.baseHom = 𝟙` then the classifying hom's base is `baseMap`
- **What**: Base computation when v is base-identity.
- **Hypotheses**: hv.
- **Uses from project**: `EllObj.tateClassifyingHomOfPullbackMap_baseHom`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 600–607 (proof 4 lines)
- **Notes**: —

### `theorem EllObj.tatePullbackAlong_hom_ext`
- **Type**: maps into `(tateEllObj R).pullbackAlong baseMap` are equal given equal projections and base homs
- **What**: Extensionality into the Tate pullback via `homPullbackAlongEquiv` injectivity.
- **Hypotheses**: hproj, hbase.
- **Uses from project**: `EllObj.homPullbackAlongEquiv`, `EllObj.pullbackAlongπ` (imported), `tateEllObj`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 611–619 (proof 3 lines)
- **Notes**: —

### `theorem EllObj.tateClassifyingHomOfPullbackMap_toPullbackAlong`
- **Type**: `tateClassifyingHomOfPullbackMap R Y f.baseHom (toPullbackAlong f) = f`
- **What**: Round-trip: the pullback-shaped constructor inverts `toPullbackAlong`.
- **Hypotheses**: none.
- **Uses from project**: `EllObj.toPullbackAlong`, `EllObj.toPullbackAlong_pullbackAlongπ` (imported), `EllObj.tateClassifyingHomOfPullbackMap`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 621–625 (proof 1 line)
- **Notes**: @[simp]

### `theorem EllObj.toPullbackAlong_tateClassifyingHomOfPullbackMap`
- **Type**: other round-trip through `pullbackAlongMap`
- **What**: `toPullbackAlong` of the constructed hom returns v (up to pullbackAlongMap).
- **Hypotheses**: none.
- **Uses from project**: `EllObj.toPullbackAlong_pullbackAlongMap`, `EllObj.pullbackAlongMap` (imported), `EllObj.tateClassifyingHomOfPullbackMap`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 627–632 (term proof)
- **Notes**: —

### `theorem EllObj.tateClassifyingHomOfPullbackMap_pullSection`
- **Type**: pullSection of the composite = iterated pullSection
- **What**: Pulling a universal section along the pullback-shaped hom factors through the pullback projection.
- **Hypotheses**: none.
- **Uses from project**: `EllHom.pullSection_comp` (imported), `EllObj.tateClassifyingHomOfPullbackMap`, `EllObj.pullbackAlongπ`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 634–641 (term proof)
- **Notes**: —

### `theorem tateCurveLocOver_map_tateRingOverLift`
- **Type**: `(tateCurveLocOver R).map (tateRingOverLift R α β hΔ) = (tateCurveOver R).map (eval₂Hom … (α,β))`
- **What**: Specialising the universal Tate curve by the ring lift recovers the Tate-normal curve with coefficients (α, β).
- **Hypotheses**: hΔ.
- **Uses from project**: `tateCurveLocOver` (imported), `tateRingOverLift`, `tateCurveOver`; mathlib `WeierstrassCurve.map_map`.
- **Used by**: `tateCurveLocOver_map_tateRingOverAlgLift`.
- **Visibility**: public
- **Lines**: 645–651 (proof 1 line)
- **Notes**: —

### `theorem tateCurveLocOver_map_tateRingOverAlgLift`
- **Type**: algebra-map version of the previous
- **What**: Same computation for the bundled algebra lift.
- **Hypotheses**: hΔ.
- **Uses from project**: `tateCurveLocOver_map_tateRingOverLift`, `tateRingOverAlgLift`.
- **Used by**: `tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal`.
- **Visibility**: public
- **Lines**: 654–660 (term proof)
- **Notes**: —

### `theorem tateCurveOver_map_tateNormal_coeffs`
- **Type**: `(hW : W.IsTateNormal) → (tateCurveOver R).map (eval₂Hom … (W.a₁, W.a₂)) = W`
- **What**: A Tate-normal curve over an R-algebra is exactly the specialisation of the universal curve at its own a₁, a₂.
- **Hypotheses**: W Tate-normal (a₃ = a₄ = a₆ = 0 encoded in `IsTateNormal`).
- **Uses from project**: `tateCurveOver`, `tateCurve` (imported), `IsTateNormal` (imported).
- **Used by**: `tateRingOverLiftOfTateNormal`, `tateRingOverAlgLiftOfTateNormal`, `tateCurveLocOver_map_tateRingOverLiftOfTateNormal`, `tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal`.
- **Visibility**: public
- **Lines**: 664–668 (proof 1 line, ext+simp)
- **Notes**: —

### `noncomputable def tateRingOverLiftOfTateNormal`
- **Type**: `(W : WeierstrassCurve A) [W.IsElliptic] (hW : W.IsTateNormal) : tateRingOver R →+* A`
- **What**: The atlas-ring map attached to an elliptic Tate-normal curve (lift at (a₁, a₂); discriminant unit from ellipticity).
- **Hypotheses**: W elliptic and Tate-normal.
- **Uses from project**: `tateRingOverLift`, `tateCurveOver_map_tateNormal_coeffs`; mathlib `WeierstrassCurve.isUnit_Δ`.
- **Used by**: `tateRingOverLiftOfTateNormal_X_zero/_X_one`, `tateCurveLocOver_map_tateRingOverLiftOfTateNormal`, `tateRingOverLiftOfPoint`.
- **Visibility**: public
- **Lines**: 671–675
- **Notes**: —

### `noncomputable def tateRingOverAlgLiftOfTateNormal`
- **Type**: algebra-map version, `tateRingOver R →ₐ[R] A`
- **What**: The atlas R-algebra map attached to an elliptic Tate-normal curve.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOverAlgLift`, `tateCurveOver_map_tateNormal_coeffs`.
- **Used by**: `tateRingOverAlgLiftOfTateNormal_X_zero/_X_one`, `tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal`, `tateRingOverAlgLiftOfPoint`, `tateBaseSpecMapOfTateNormal`, `tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`, `tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`.
- **Visibility**: public
- **Lines**: 678–682
- **Notes**: —

### `theorem tateRingOverLiftOfTateNormal_X_zero`
- **Type**: value at X 0 is W.a₁
- **What**: Coordinate computation for the Tate-normal lift.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverLiftOfTateNormal`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 684–689 (proof 1 line)
- **Notes**: @[simp]

### `theorem tateRingOverLiftOfTateNormal_X_one`
- **Type**: value at X 1 is W.a₂
- **What**: Coordinate computation.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverLiftOfTateNormal`.
- **Used by**: unused in file (leaf @[simp]; may fire via simp).
- **Visibility**: public
- **Lines**: 691–696 (proof 1 line)
- **Notes**: @[simp]

### `theorem tateRingOverAlgLiftOfTateNormal_X_zero`
- **Type**: value at X 0 is W.a₁ (alg version)
- **What**: Coordinate computation.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: unused in file by name (@[simp]; fires in `simpa [tateRingOverAlgLiftOfTateNormal]` calls at 843–844).
- **Visibility**: public
- **Lines**: 698–703 (proof 1 line)
- **Notes**: @[simp]

### `theorem tateRingOverAlgLiftOfTateNormal_X_one`
- **Type**: value at X 1 is W.a₂ (alg version)
- **What**: Coordinate computation.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: unused in file by name (@[simp]).
- **Visibility**: public
- **Lines**: 705–710 (proof 1 line)
- **Notes**: @[simp]

### `theorem tateCurveLocOver_map_tateRingOverLiftOfTateNormal`
- **Type**: `(tateCurveLocOver R).map (tateRingOverLiftOfTateNormal R W hW) = W`
- **What**: Specialising the universal Tate curve by the Tate-normal map recovers the curve — the self-recovery equation.
- **How**: `WeierstrassCurve.map_map`, identifies the composite ring hom with the eval₂Hom, then `tateCurveOver_map_tateNormal_coeffs`.
- **Hypotheses**: W elliptic Tate-normal.
- **Uses from project**: `tateCurveLocOver`, `tateRingOverLiftOfTateNormal`, `tateRingOverLift`, `tateCurveOver_map_tateNormal_coeffs`.
- **Used by**: `tateCurveLocOver_map_tateRingOverLiftOfPoint`.
- **Visibility**: public
- **Lines**: 714–726 (proof ~10 lines)
- **Notes**: —

### `theorem tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal`
- **Type**: algebra-map version of the previous
- **What**: Same self-recovery through the bundled lift.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOverAlgLiftOfTateNormal`, `tateCurveLocOver_map_tateRingOverAlgLift`, `tateCurveOver_map_tateNormal_coeffs`.
- **Used by**: `tateCurveLocOver_map_tateRingOverAlgLiftOfPoint`.
- **Visibility**: public
- **Lines**: 729–734 (proof 3 lines)
- **Notes**: —

---

## Section `LocalNormalisation` (lines 738–937)

### `noncomputable def tateNormalVariableChange`
- **Type**: `(W : WeierstrassCurve A) [W.IsElliptic] (x y : A) (hxy : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) : WeierstrassCurve.VariableChange A`
- **What**: The T-E1 normalising variable change for a pointed affine chart of nowhere order ≤ 3 (choice from the T-E1 existence-and-uniqueness theorem).
- **Hypotheses**: W elliptic; (x,y) on the curve; ψ₂ψ₃-value a unit (`NowhereOrderLEThree`).
- **Uses from project**: `exists_unique_variableChange_isTateNormal` (imported T-E1), `NowhereOrderLEThree` (imported).
- **Used by**: pervasive — `tateNormalVariableChange_isTateNormal/_r/_t/_unique`, `tateRingOverLiftOfPoint`, `tateRingOverAlgLiftOfPoint`, all `…OfPoint` lemmas, `tateNormalVariableChange_mul`, `_map`, `_smul_map`, `_congr`, `projTateMap_unfold`, `projModelBaseChange_projTateMap`, `projTateMap_map_tate`, `tateBaseSpecMapOfPoint_inducedPt` (109 name occurrences).
- **Visibility**: public
- **Lines**: 743–746
- **Notes**: —

### `theorem tateNormalVariableChange_isTateNormal`
- **Type**: `((tateNormalVariableChange W x y hxy hord) • W).IsTateNormal`
- **What**: The chosen change puts W into Tate normal form (choose_spec).
- **Hypotheses**: as constructor.
- **Uses from project**: `exists_unique_variableChange_isTateNormal`, `tateNormalVariableChange`.
- **Used by**: `tateRingOverLiftOfPoint`, `tateRingOverAlgLiftOfPoint`, `tateBaseSpecMap_eq_tateBaseSpecMapOfPoint`, `tateCurveLocOver_map_tateRingOverLiftOfPoint`, `tateCurveLocOver_map_tateRingOverAlgLiftOfPoint`, `tateNormalVariableChange_mul`, `tateNormalVariableChange_map`.
- **Visibility**: public
- **Lines**: 748–751 (term proof)
- **Notes**: —

### `theorem tateNormalVariableChange_r`
- **Type**: `(tateNormalVariableChange W x y hxy hord).r = x`
- **What**: The chosen change translates x to the origin.
- **Hypotheses**: as constructor.
- **Uses from project**: `exists_unique_variableChange_isTateNormal`.
- **Used by**: `tateNormalVariableChange_mul`, `markedPointNormalised_coords`.
- **Visibility**: public
- **Lines**: 753–757
- **Notes**: @[simp]

### `theorem tateNormalVariableChange_t`
- **Type**: `(tateNormalVariableChange W x y hxy hord).t = y`
- **What**: The chosen change translates y to the origin.
- **Hypotheses**: as constructor.
- **Uses from project**: `exists_unique_variableChange_isTateNormal`.
- **Used by**: `tateNormalVariableChange_mul`, `markedPointNormalised_coords`.
- **Visibility**: public
- **Lines**: 759–763
- **Notes**: @[simp]

### `theorem tateNormalVariableChange_unique`
- **Type**: any C with `(C • W).IsTateNormal ∧ C.r = x ∧ C.t = y` equals `tateNormalVariableChange W x y hxy hord`
- **What**: T-E1 uniqueness clause, extracted.
- **Hypotheses**: hC.
- **Uses from project**: `exists_unique_variableChange_isTateNormal`.
- **Used by**: `tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`, `tateNormalVariableChange_mul`, `tateNormalVariableChange_map`, `projTateMap_map_tate`, `tateBaseSpecMapOfPoint_inducedPt`.
- **Visibility**: public
- **Lines**: 765–770 (term proof)
- **Notes**: —

### `noncomputable def tateRingOverLiftOfPoint`
- **Type**: `(W …) (x y) (hxy) (hord) : tateRingOver R →+* A`
- **What**: The local map to the atlas from a pointed Weierstrass chart: first T-E1 normalise, then the Tate-normal lift.
- **Hypotheses**: elliptic, on-curve, nowhere order ≤ 3.
- **Uses from project**: `tateRingOverLiftOfTateNormal`, `tateNormalVariableChange`, `tateNormalVariableChange_isTateNormal`.
- **Used by**: `tateCurveLocOver_map_tateRingOverLiftOfPoint`, `tateRingOverLiftOfPoint_comp`, `tateBaseSpecMapOfPoint_naturality` (via show), `tateRingOverLiftOfPoint_congr`, `projModelBaseChange_projTateMap`.
- **Visibility**: public
- **Lines**: 776–780
- **Notes**: —

### `noncomputable def tateRingOverAlgLiftOfPoint`
- **Type**: bundled `tateRingOver R →ₐ[R] A` version
- **What**: The local atlas R-algebra map from a pointed chart.
- **Hypotheses**: as above.
- **Uses from project**: `tateRingOverAlgLiftOfTateNormal`, `tateNormalVariableChange`, `tateNormalVariableChange_isTateNormal`.
- **Used by**: `tateRingOverAlgLiftOfPoint_X_zero/_X_one`, `tateBaseSpecMapOfPoint`, `tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`, `tateCurveLocOver_map_tateRingOverAlgLiftOfPoint`, `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `tateCurveLocOver_map_marked`, `tateNormalIso`, `projTateMap` and every clause of the projTateMap package, `tateRingOverLiftOfPoint_comp`, `projTateMap_map_tate` (87 occurrences).
- **Visibility**: public
- **Lines**: 783–787
- **Notes**: —

### `theorem tateRingOverAlgLiftOfPoint_X_zero`
- **Type**: value at X 0 is `((tateNormalVariableChange …) • W).a₁`
- **What**: The pointed atlas map classifies the normal form's a₁.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverAlgLiftOfPoint`.
- **Used by**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `tateRingOverLiftOfPoint_comp`, `projTateMap_map_tate`.
- **Visibility**: public
- **Lines**: 789–795 (proof 1 line)
- **Notes**: @[simp]

### `theorem tateRingOverAlgLiftOfPoint_X_one`
- **Type**: value at X 1 is the normal form's a₂
- **What**: Second coordinate computation.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateRingOverAlgLiftOfPoint`.
- **Used by**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `tateRingOverLiftOfPoint_comp`, `projTateMap_map_tate`.
- **Visibility**: public
- **Lines**: 797–803 (proof 1 line)
- **Notes**: @[simp]

### `noncomputable def tateBaseSpecMapOfTateNormal`
- **Type**: `(hW : W.IsTateNormal) : Spec (.of A) ⟶ tateBase R`
- **What**: The affine atlas map attached to a Tate-normal curve.
- **Hypotheses**: elliptic, Tate-normal.
- **Uses from project**: `tateBaseSpecMap`, `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: `tateBaseSpecMapOfTateNormal_tateStructMap`, `tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`, `tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange`, `tateBaseSpecMapOfTateNormal_eq_of_variableChanges`.
- **Visibility**: public
- **Lines**: 806–808
- **Notes**: —

### `noncomputable def tateBaseSpecMapOfPoint`
- **Type**: `(W) (x y) (hxy) (hord) : Spec (.of A) ⟶ tateBase R`
- **What**: The affine atlas map attached to a pointed chart after T-E1 normalisation — the local classifying base map in Spec form.
- **Hypotheses**: as `tateRingOverAlgLiftOfPoint`.
- **Uses from project**: `tateBaseSpecMap`, `tateRingOverAlgLiftOfPoint`.
- **Used by**: `tateBaseSpecMapOfPoint_tateStructMap`, `tateBaseSpecMap_eq_tateBaseSpecMapOfPoint`, `tateBaseSpecMapOfPoint_eq_of_pointedIso`, `projTateMap_π/_isPullback/_zero/_marking`, `tateBaseSpecMapOfPoint_naturality/_congr`, `MarkedChartData.baseMap`, the overlap-agreement theorems, `tateBaseSpecMapOfPoint_inducedPt` (39 occurrences).
- **Visibility**: public
- **Lines**: 812–815
- **Notes**: —

### `theorem tateBaseSpecMapOfTateNormal_tateStructMap`
- **Type**: the Tate-normal chart map lies over Spec R
- **What**: Over-Spec R property of the Tate-normal affine map.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateBaseSpecMap_tateStructMap`, `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 818–822 (term proof)
- **Notes**: —

### `theorem tateBaseSpecMapOfPoint_tateStructMap`
- **Type**: the pointed chart map lies over Spec R
- **What**: Over-Spec R property of the pointed affine map.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateBaseSpecMap_tateStructMap`, `tateRingOverAlgLiftOfPoint`.
- **Used by**: `MarkedChartData.baseMap_over`.
- **Visibility**: public
- **Lines**: 825–829 (term proof)
- **Notes**: —

### `theorem tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`
- **Type**: a map with the Tate-normal coordinates (a₁, a₂) equals the Tate-normal chart map
- **What**: Rigidity of affine atlas maps at Tate-normal coefficients.
- **Hypotheses**: h0, h1 coordinate agreement, hW.
- **Uses from project**: `tateBaseSpecMap_ext`, `tateBaseSpecMapOfTateNormal`, `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: `tateBaseSpecMap_eq_tateBaseSpecMapOfPoint`, `tateBaseSpecMapOfPoint_inducedPt`.
- **Visibility**: public
- **Lines**: 833–844 (proof 4 lines)
- **Notes**: —

### `theorem tateBaseSpecMap_eq_tateBaseSpecMapOfPoint`
- **Type**: a map with the normalised coordinates equals the pointed chart map
- **What**: Pointed version of the rigidity statement.
- **Hypotheses**: h0, h1 at the T-E1-normalised coefficients.
- **Uses from project**: `tateBaseSpecMap_eq_tateBaseSpecMapOfTateNormal`, `tateBaseSpecMapOfPoint`, `tateRingOverAlgLiftOfPoint`, `tateNormalVariableChange(_isTateNormal)`.
- **Used by**: `tateBaseSpecMapOfPoint_inducedPt`.
- **Visibility**: public
- **Lines**: 848–859 (proof 4 lines)
- **Notes**: —

### `theorem tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`
- **Type**: for any C with `(C•W).IsTateNormal ∧ C.r = x ∧ C.t = y`, `tateRingOverAlgLiftOfTateNormal R (C•W) hC.1 = tateRingOverAlgLiftOfPoint R W x y hxy hord`
- **What**: Any normalising change induces the same atlas algebra map as the chosen T-E1 one (via T-E1 uniqueness).
- **Hypotheses**: hC.
- **Uses from project**: `tateNormalVariableChange_unique`, `tateRingOver_algHom_ext`, `tateRingOverAlgLiftOfPoint`, `tateRingOverAlgLiftOfTateNormal`.
- **Used by**: `tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange`, `tateRingOverAlgLiftOfTateNormal_eq_of_variableChanges`.
- **Visibility**: public
- **Lines**: 863–873 (proof 5 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange`
- **Type**: Spec version of the previous
- **What**: Any normalising change gives the pointed affine atlas map.
- **Hypotheses**: hC.
- **Uses from project**: the previous theorem, `tateBaseSpecMapOfTateNormal`, `tateBaseSpecMapOfPoint`.
- **Used by**: `tateBaseSpecMapOfTateNormal_eq_of_variableChanges`.
- **Visibility**: public
- **Lines**: 877–886 (proof 3 lines)
- **Notes**: —

### `theorem tateRingOverAlgLiftOfTateNormal_eq_of_variableChanges`
- **Type**: two normalising changes C, C' for the same pointed chart give equal atlas algebra maps
- **What**: Well-definedness of the atlas map in the choice of normalising change.
- **Hypotheses**: hC, hC'.
- **Uses from project**: `tateRingOverAlgLiftOfTateNormal_eq_tateRingOverAlgLiftOfPoint_of_variableChange`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 890–901 (proof 4 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfTateNormal_eq_of_variableChanges`
- **Type**: Spec version of the previous
- **What**: Well-definedness of the affine atlas map in the normalising change.
- **Hypotheses**: hC, hC'.
- **Uses from project**: `tateBaseSpecMapOfTateNormal_eq_tateBaseSpecMapOfPoint_of_variableChange`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 905–916 (proof 4 lines)
- **Notes**: —

### `theorem tateCurveLocOver_map_tateRingOverLiftOfPoint`
- **Type**: `(tateCurveLocOver R).map (tateRingOverLiftOfPoint …) = (tateNormalVariableChange …) • W`
- **What**: The local atlas map classifies the T-E1 normal form of the pointed chart.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateCurveLocOver_map_tateRingOverLiftOfTateNormal`, `tateNormalVariableChange(_isTateNormal)`, `tateRingOverLiftOfPoint`.
- **Used by**: unused in file (mentioned only in the docstring of the AlgLift version).
- **Visibility**: public
- **Lines**: 919–925 (term proof)
- **Notes**: —

### `theorem tateCurveLocOver_map_tateRingOverAlgLiftOfPoint`
- **Type**: algebra-map version of the previous
- **What**: Specialisation of the universal curve at the pointed atlas map is the T-E1 normal form.
- **Hypotheses**: as constructor.
- **Uses from project**: `tateCurveLocOver_map_tateRingOverAlgLiftOfTateNormal`, `tateNormalVariableChange(_isTateNormal)`, `tateRingOverAlgLiftOfPoint`.
- **Used by**: `tateCurveLocOver_map_marked`.
- **Visibility**: public
- **Lines**: 928–935 (term proof)
- **Notes**: —

---

## Section `PointedComparison` (lines 939–962)

### `theorem atlasLocalPointedIso_exists_variableChange`
- **Type**: a pointed isomorphism `e : projModel W ≅ projModel W'` respecting π and zero comes from a variable change: `∃ C, ∃ hW : C • W' = W, e.hom = eqToHom … ≫ (projModelVCIso C W').hom`
- **What**: Atlas-local restatement of T-W7.1b (pointed isos of projective Weierstrass models are variable changes) — a re-export.
- **Hypotheses**: heπ, hez pointedness.
- **Uses from project**: `pointedIso_exists_variableChange` (imported), `projModel`, `projModelπ`, `projModelZero`, `projModelVCIso` (imported).
- **Used by**: unused in file (the file calls the imported `pointedIso_exists_variableChange` directly).
- **Visibility**: public
- **Lines**: 946–952 (term proof)
- **Notes**: —

### `theorem atlasLocal_projModelVCIso_injective`
- **Type**: `projModelVCIso` is injective in the variable change (pinned pointed iso ⇒ equal changes)
- **What**: Atlas-local restatement of T-W7 faithfulness — a re-export.
- **Hypotheses**: hW, h.
- **Uses from project**: `projModelVCIso_injective` (imported), `projModelVCIso`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 956–960 (term proof)
- **Notes**: —

---

## Section `OrderDictionary` (lines 964–1123) — B2-ii ring core

### `lemma two_zsmul_some_eq_zero_of_ψ₂_eq_zero`
- **Type**: over a field F, `(hns : Nonsingular x y) → W.ψ₂.evalEval x y = 0 → (2 : ℤ) • some x y hns = 0`
- **What**: Vanishing of ψ₂ at an affine point makes it 2-torsion (y = negY, point equals its own negative). Converse of the vendored `twiceNeZero_of_isUnit`.
- **Hypotheses**: field F, DecidableEq F, nonsingularity, h2.
- **Uses from project**: none in-project (mathlib `WeierstrassCurve.ψ₂`, `Affine.evalEval_polynomialY`, `Affine.negY`, `Affine.Point.add_self_of_Y_eq`).
- **Used by**: `nowhereOrderLEThree_of_forall_geom`.
- **Visibility**: public
- **Lines**: 980–988 (proof ~8 lines)
- **Notes**: —

### `lemma three_zsmul_some_eq_zero_of_Ψ₃_eq_zero`
- **Type**: `(hns) → y ≠ negY x y → W.Ψ₃.eval x = 0 → (3 : ℤ) • some x y hns = 0`
- **What**: Vanishing of the 3-division polynomial at a non-2-torsion affine point makes it 3-torsion: doubling fixes x, so 2P = ±P, and 2P = P is excluded.
- **How**: Uses the project bridge `Ψ₃_eval_X` (on `Affine.Point`), the slope/doubling formulas (`Affine.slope_of_Y_ne`, `Affine.addX`, `Affine.Point.add_self_of_Y_ne`), `X_eq_iff` to split 2P = ±P, and `linear_combination`/`field_simp` algebra; the 2P = P branch is killed by `some_ne_zero`.
- **Hypotheses**: field, nonsingular, hy2 (not 2-torsion), h3.
- **Uses from project**: `Ψ₃_eval_X` (project bridge on Affine.Point, imported), `Affine.Point.X_some/Y_some/pX/pY` (project/vendored).
- **Used by**: `nowhereOrderLEThree_of_forall_geom`.
- **Visibility**: public
- **Lines**: 993–1045 (proof ~50 lines)
- **Notes**: proof >30 lines

### `theorem nowhereOrderLEThree_of_forall_geom`
- **Type**: `(W : WeierstrassCurve A) [W.IsElliptic] (x y) (hxy) → (∀ (k) [Field k] [DecidableEq k] [IsAlgClosed k] [Algebra A k] (hns), ∀ a, 0 < a → a ≤ 3 → (a:ℤ) • some (map x) (map y) hns ≠ 0) → NowhereOrderLEThree W x y`
- **What**: **B2-ii order ⇒ unit criterion**: if no multiple a•P (0 < a ≤ 3) dies at any geometric point of Spec A, the ψ₂ψ₃-value at (x,y) is a unit — the input hypothesis of T-E1.
- **How**: Contrapositive: a non-unit lies in a maximal ideal m; over k = AlgebraicClosure (A ⧸ m) the product `(Ψ 2).evalEval · (Ψ 3).evalEval` vanishes (`Ideal.exists_le_maximal`, `Ideal.Quotient.eq_zero_iff_mem`); base-change transfers Equation/Nonsingular; `mul_eq_zero` splits into the ψ₂ and Ψ₃ cases, discharged by the two lemmas above.
- **Hypotheses**: elliptic, on-curve, the geometric non-vanishing quantifier.
- **Uses from project**: `NowhereOrderLEThree`, `two_zsmul_some_eq_zero_of_ψ₂_eq_zero`, `three_zsmul_some_eq_zero_of_Ψ₃_eq_zero`; mathlib `WeierstrassCurve.Ψ_two/Ψ_three/map_Ψ₃`, `Affine.equation_iff(_nonsingular)`, `AlgebraicClosure`.
- **Used by**: `MarkedChartData.pt_hord`.
- **Visibility**: public
- **Lines**: 1055–1121 (proof ~59 lines)
- **Notes**: proof >30 lines; `classical` used

---

## Section `ZChartSection` (lines 1125–1326) — B2-i

### `theorem inZChart_of_forall_ne_zero`
- **Type**: `(g : SpecPoints (projModel W) (projModelπ W) K) → (∀ (k) [Field k] (t : Spec k ⟶ Spec K), t ≫ g.1 ≠ (t ≫ Spec.map (algebraMap A K)) ≫ projModelZero W) → InZChart W g`
- **What**: A K-point of the projective model never hitting the zero section at any field point factors through the Z-chart (Loeffler's affine-point extraction).
- **How**: For each point p of Spec K, tests with the residue-field point `fromSpecResidueField`; if p were outside the basic open, `specPoint_eq_zero_of_not_inZ` (imported) would make the composite the zero point, contradicting h; then `IsOpenImmersion.lift` against `Proj.awayι` using `Proj.opensRange_awayι`.
- **Hypotheses**: the fibrewise non-zero condition h.
- **Uses from project**: `SpecPoints`, `InZChart`, `projModel`, `projModelπ`, `projModelZero`, `quotientGrading`, `quotientGradingHom`, `projIdeal`, `mk_X_mem_quotientGrading_one`, `specPoint_eq_zero_of_not_inZ` (all imported).
- **Used by**: `MarkedChartData.pt_inZChart`.
- **Visibility**: public
- **Lines**: 1142–1201 (proof ~56 lines)
- **Notes**: proof >30 lines

### `noncomputable def zChartHom`
- **Type**: `(g : SpecPoints …) (hZ : InZChart W g) : HomogeneousLocalization.Away (quotientGrading (projIdeal W)) (X 2) →+* K`
- **What**: The chart-ring homomorphism attached to a Z-chart K-point (first component of `chartHomEquiv`).
- **Hypotheses**: hZ.
- **Uses from project**: `chartHomEquiv` (imported), `InZChart`, `SpecPoints`, `quotientGrading(Hom)`, `projIdeal`.
- **Used by**: `zChartHom_compat`, `Spec_map_zChartHom_awayι`, `zChartHom_unique`, `zChartEval`, `zChartEval_algebraMap`, `zChartEval_pointedIso`, `zChartHom_specPointComp`, `zChartHom_tateP0SpecPoint(+_isLocalizationElem)`, `zChartHom_specPointBaseChange`, `inZChart_specPointPointedIso`, `pt_hord`, `fibrePt_inZChart`, `chartSolution_val` (49 occurrences).
- **Visibility**: public
- **Lines**: 1206–1210
- **Notes**: —

### `theorem zChartHom_compat`
- **Type**: `(zChartHom W g hZ).comp (fromZero ∘ gradeZeroRingEquiv) = algebraMap A K`
- **What**: The chart-ring homomorphism is A-compatible (second component of chartHomEquiv).
- **Hypotheses**: hZ.
- **Uses from project**: `chartHomEquiv`, `gradeZeroRingEquiv` (imported), `quotientGrading`.
- **Used by**: `zChartEval_algebraMap`.
- **Visibility**: public
- **Lines**: 1213–1220 (term proof)
- **Notes**: —

### `theorem Spec_map_zChartHom_awayι`
- **Type**: `Spec.map (ofHom (zChartHom W g hZ)) ≫ Proj.awayι … (X 2) … = g.1`
- **What**: **The factoring equation**: Spec of the chart-ring hom composed with the chart inclusion recovers the point; everything else follows from this by faithfulness of Spec and monicity of awayι.
- **Hypotheses**: hZ.
- **Uses from project**: `chartHomEquiv`, `mk_X_mem_quotientGrading_one`, `zChartHom`.
- **Used by**: `zChartHom_unique`, `zChartEval_pointedIso`, `zChartHom_specPointComp`, `specPoint_ext_of_zChartEval`, `inZChart_specPointBaseChange`, `zChartHom_specPointBaseChange`, `inZChart_specPointPointedIso`, `pt_hord`, `fibrePt_inZChart` (11 occurrences).
- **Visibility**: public
- **Lines**: 1225–1232 (proof 2 lines)
- **Notes**: —

### `theorem zChartHom_unique`
- **Type**: any χ satisfying the factoring equation equals `zChartHom W g hZ`
- **What**: The chart-ring hom is the unique one factoring the point through the chart.
- **How**: cancel_mono against `Spec_map_zChartHom_awayι`, then `Spec.map_injective`.
- **Hypotheses**: hχ (factoring equation for χ).
- **Uses from project**: `Spec_map_zChartHom_awayι`, `zChartHom`.
- **Used by**: `zChartEval_pointedIso`, `zChartHom_specPointComp`, `zChartHom_tateP0SpecPoint`, `zChartHom_specPointBaseChange`.
- **Visibility**: public
- **Lines**: 1235–1247 (proof 4 lines)
- **Notes**: —

### `noncomputable def zChartEval`
- **Type**: `(g) (hZ) : W.toAffine.CoordinateRing →+* K`
- **What**: The evaluation homomorphism out of the affine coordinate ring attached to a Z-chart point (`zChartHom` conjugated by `chartZRingEquiv`), with coordX ↦ x, coordY ↦ y.
- **Hypotheses**: hZ.
- **Uses from project**: `zChartHom`, `chartZRingEquiv` (imported).
- **Used by**: pervasive — every coordinate-evaluation statement in the file (337 occurrences): `zChartEval_algebraMap/_equation/_equation_self/_coordX/_coordY/_pointedIso/_specPointComp/_specPointBaseChange_*/_eqToHom_point/_congr/_fibrePt_*`, the ENGINE theorems, `pt_hord`, `markedPointNormalised_coords`, `projTateMap*`, `inducedPt_coordX/Y`, etc.
- **Visibility**: public
- **Lines**: 1251–1255
- **Notes**: —

### `theorem zChartEval_algebraMap`
- **Type**: `zChartEval W g hZ (algebraMap A (CoordinateRing) r) = algebraMap A K r`
- **What**: The evaluation is A-algebra compatible.
- **How**: routes through `chartZRingEquiv_fromZero` and `zChartHom_compat`.
- **Hypotheses**: hZ.
- **Uses from project**: `chartZRingEquiv(_fromZero)`, `HomogeneousLocalization.fromZeroRingHom` (mathlib), `algebraMapGradeZero` (imported), `zChartHom_compat`.
- **Used by**: `zChartEval_equation`, `zChartEval_coords_of_pointedIso`, `coordRingHom_ext`-consumers (`specPoint_ext_of_zChartEval`), `markedPointNormalised_coords`.
- **Visibility**: public
- **Lines**: 1258–1269 (proof ~9 lines)
- **Notes**: —

### `theorem zChartEval_equation`
- **Type**: `(W.baseChange K).toAffine.Equation (zChartEval W g hZ (coordX W)) (zChartEval W g hZ (coordY W))`
- **What**: The coordinates extracted from a Z-chart point satisfy the Weierstrass equation of the base-changed curve.
- **How**: The relation `mk W.polynomial = 0` (AdjoinRoot.mk_self) is pushed through the evaluation; constants are computed via `zChartEval_algebraMap`; `Affine.equation_iff` + `linear_combination` closes.
- **Hypotheses**: hZ.
- **Uses from project**: `zChartEval`, `zChartEval_algebraMap`, `coordX`, `coordY` (imported).
- **Used by**: `zChartEval_equation_self`.
- **Visibility**: public
- **Lines**: 1273–1315 (proof ~40 lines)
- **Notes**: proof >30 lines

### `theorem zChartEval_equation_self`
- **Type**: over the base ring itself: `W'.toAffine.Equation (zChartEval W' g hZ (coordX W')) (zChartEval W' g hZ (coordY W'))`
- **What**: Restatement of `zChartEval_equation` at K = A' keeping downstream `Equation` slots typed (baseChange A' = W' definitionally).
- **Hypotheses**: hZ.
- **Uses from project**: `zChartEval_equation`.
- **Used by**: pervasive (201 occurrences) — every `…OfPoint`-instantiation at a chart point: the ENGINE theorems, `projTateMap` package, `MarkedChartData.baseMap/topMap/pt_hord`, overlap/gluing/induced-chart theorems.
- **Visibility**: public
- **Lines**: 1320–1324 (term proof)
- **Notes**: —

---

## Section `MarkedChartComparison` (lines 1328–1614) — B2-iii/iv ENGINE (base)

### `noncomputable def pointedIsoAwayHom`
- **Type**: `(ε : projModel W₁ ≅ projModel W₂) (hez) : CommRingCat.of (Away … W₂ …) ⟶ CommRingCat.of (Away … W₁ …)`
- **What**: The Z-chart ring morphism induced by a pointed isomorphism of models: `pointedIsoΓ` conjugated by the two `basicOpenIsoAway` identifications.
- **Hypotheses**: hez (zero-compatibility).
- **Uses from project**: `pointedIsoΓ` (imported), `Proj.basicOpenIsoAway`, `quotientGrading(Hom)`, `projIdeal`, `mk_X_mem_quotientGrading_one`.
- **Used by**: `Spec_map_pointedIsoAwayHom_awayι`, `zChartEval_pointedIso`, `inZChart_specPointPointedIso`.
- **Visibility**: public
- **Lines**: 1343–1356
- **Notes**: —

### `theorem Spec_map_pointedIsoAwayHom_awayι`
- **Type**: `Spec.map (pointedIsoAwayHom ε hez) ≫ awayι(W₂) = awayι(W₁) ≫ ε.hom`
- **What**: **The chart square of a pointed isomorphism**: Spec of the induced chart-ring morphism intertwines the two chart inclusions with ε.
- **How**: Starts from mathlib's `IsAffineOpen.SpecMap_appLE_fromSpec` applied to ε.hom on the two basic opens, rewrites `appLE` to `pointedIsoΓ` via the imported `appLE_zChart_eq_pointedIsoΓ` and `Proj_fromSpec_awayToSection_awayι`, then unpacks the `basicOpenIsoAway` composition and cancels hom/inv.
- **Hypotheses**: hez.
- **Uses from project**: `appLE_zChart_eq_pointedIsoΓ`, `Proj_fromSpec_awayToSection_awayι`, `pointedIso_preimage_zChart` (all imported), `pointedIsoAwayHom`, `Proj.basicOpenIsoAway`, `mk_X_mem_quotientGrading_one`.
- **Used by**: `zChartEval_pointedIso`, `inZChart_specPointPointedIso`.
- **Visibility**: public
- **Lines**: 1360–1436 (proof ~68 lines)
- **Notes**: proof >30 lines

### `theorem zChartEval_pointedIso`
- **Type**: for pointed ε carrying g₁ to g₂: `zChartEval W₂ g₂ hZ₂ a = zChartEval W₁ g₁ hZ₁ (pointedIsoCoordEquiv ε heπ hez a)`
- **What**: Transport of chart evaluation along a pointed isomorphism: evaluation on the target is evaluation on the source after the induced coordinate-ring isomorphism.
- **How**: Identifies the target chart hom as `pointedIsoAwayHom ≫ zChartHom` via `zChartHom_unique` and the chart square; then matches with `pointedIsoCoordEquiv_sections` through `chartZSectionsRingEquiv` and `basicOpenIsoAway.commRingCatIsoToRingEquiv`.
- **Hypotheses**: heπ, hez, hZ₁, hZ₂, hsec (g₁ ≫ ε.hom = g₂).
- **Uses from project**: `Spec_map_pointedIsoAwayHom_awayι`, `zChartHom_unique`, `Spec_map_zChartHom_awayι`, `pointedIsoCoordEquiv(_sections)` (imported), `chartZSectionsRingEquiv` (imported), `chartZRingEquiv`, `pointedIsoAwayHom`, `pointedIsoΓ`.
- **Used by**: `zChartEval_coords_of_pointedIso`, `markedPointNormalised_coords`.
- **Visibility**: public
- **Lines**: 1443–1483 (proof ~32 lines)
- **Notes**: proof >30 lines

### `theorem tateNormalVariableChange_mul`
- **Type**: with marked coordinates related by C and `C • W₂ = W₁`: `tateNormalVariableChange(W₁) * C = tateNormalVariableChange(W₂)`
- **What**: **ENGINE core**: the composite of W₁'s T-E1 normalisation with the comparison change is W₂'s normalisation, by T-E1 uniqueness.
- **How**: Applies `tateNormalVariableChange_unique` to the product, checking IsTateNormal via `mul_smul`+hC, and the r/t components via `tateNormalVariableChange_r/_t` plus `ring` on the transform equations hx, hy.
- **Hypotheses**: hZ₁, hZ₂, hord₁, hord₂, hC, hx, hy (VariableChange coordinate transforms).
- **Uses from project**: `tateNormalVariableChange(_unique/_isTateNormal/_r/_t)`, `zChartEval_equation_self`, `zChartEval`, `coordX/coordY`.
- **Used by**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `projTateMap_eq_of_pointedIso` (twice).
- **Visibility**: public
- **Lines**: 1489–1522 (proof ~17 lines; statement large)
- **Notes**: —

### `theorem zChartEval_coords_of_pointedIso`
- **Type**: for a marked pointed iso with T-W7 data (C, hC, hεhom): the two coordinate evaluations transform by the variable-change formulas (x ↦ u²x + r, y ↦ u³y + su²x + t)
- **What**: The coordinate transform of a marked pointed isomorphism, in the components of its T-W7 variable change.
- **How**: `zChartEval_pointedIso` at coordX/coordY, then rewrites through `transport_general`, `bridge_coordX/Y`, and the `coordRingCongr` simp lemmas, finishing with `zChartEval_algebraMap`.
- **Hypotheses**: heπ, hez, hZ₁, hZ₂, hsec, hC, hεhom.
- **Uses from project**: `zChartEval_pointedIso`, `transport_general`, `bridge_coordX`, `bridge_coordY`, `coordRingCongr_algebraMap(_mul_coordX/_mul_coordY)` (all imported), `projModelVCIso(_π/_zero)` (imported), `zChartEval_algebraMap`.
- **Used by**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 1526–1554 (proof ~14 lines)
- **Notes**: —

### `theorem tateRingOverAlgLiftOfPoint_eq_of_pointedIso`
- **Type**: two marked Z-chart data over the same ring linked by a marked pointed iso induce the **same** atlas algebra map
- **What**: **ENGINE, base half — Loeffler's overlap uniqueness**: T-W7 change composed with the source's T-E1 normalisation is a normalisation of the target, so the two Tate normal forms agree.
- **How**: `pointedIso_exists_variableChange` extracts C; `zChartEval_coords_of_pointedIso` gives the transforms; `tateNormalVariableChange_mul` composes; conclude with `tateRingOver_algHom_ext` on coordinates via `congrArg a₁/a₂` of the equal normal forms.
- **Hypotheses**: heπ, hez, hZ₁, hZ₂, hsec, hord₁, hord₂.
- **Uses from project**: `pointedIso_exists_variableChange` (imported), `zChartEval_coords_of_pointedIso`, `tateNormalVariableChange_mul`, `tateRingOver_algHom_ext`, `tateRingOverAlgLiftOfPoint(_X_zero/_X_one)`.
- **Used by**: `tateBaseSpecMapOfPoint_eq_of_pointedIso`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 1561–1589 (proof ~14 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfPoint_eq_of_pointedIso`
- **Type**: Spec-level form: the two pointed charts induce the same affine atlas map
- **What**: The affine Spec form of the base-half ENGINE.
- **Hypotheses**: as previous.
- **Uses from project**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `tateBaseSpecMapOfPoint`.
- **Used by**: `MarkedChartData.tateBaseSpecMapOfPoint_fibrePt_agree`, `MarkedChartData.sameU_tateBaseSpecMapOfPoint_agree`.
- **Visibility**: public
- **Lines**: 1593–1612 (proof 5 lines)
- **Notes**: —

---

## Section `ZChartNaturality` (lines 1616–1747)

### `noncomputable def specPointComp`
- **Type**: `(g : SpecPoints … K) (ψ : K →+* K') (hψ : ψ.comp (algebraMap A K) = algebraMap A K') : SpecPoints … K'`
- **What**: Compose a K-point with Spec of an A-compatible ring map.
- **Hypotheses**: hψ.
- **Uses from project**: `SpecPoints`, `projModel(π)`.
- **Used by**: `inZChart_specPointComp`, `zChartHom_specPointComp`, `zChartEval_specPointComp`, `projTateMap_marking`, `pt_hord`, `specPointBaseChange_fibrePt`, `specPointBaseChange_inducedPt`.
- **Visibility**: public
- **Lines**: 1629–1633
- **Notes**: —

### `theorem inZChart_specPointComp`
- **Type**: `InZChart W g → InZChart W (specPointComp W g ψ hψ)`
- **What**: Composition with a ring map preserves the Z-chart.
- **Hypotheses**: hZ, hψ.
- **Uses from project**: `InZChart`, `specPointComp`.
- **Used by**: `zChartHom_specPointComp`, `zChartEval_specPointComp` statements, `projTateMap_marking`, `pt_hord`, `fibrePt` lemmas, `inducedPt_coordX/Y` (11 occurrences).
- **Visibility**: public
- **Lines**: 1636–1640 (proof 2 lines)
- **Notes**: —

### `theorem zChartHom_specPointComp`
- **Type**: `zChartHom (specPointComp …) … = ψ.comp (zChartHom W g hZ)`
- **What**: The chart-ring hom of a composed point is the composition.
- **Hypotheses**: hZ, hψ.
- **Uses from project**: `zChartHom_unique`, `Spec_map_zChartHom_awayι`, `specPointComp`.
- **Used by**: `zChartEval_specPointComp`.
- **Visibility**: public
- **Lines**: 1643–1652 (proof 5 lines)
- **Notes**: —

### `theorem zChartEval_specPointComp`
- **Type**: `zChartEval (specPointComp …) … a = ψ (zChartEval W g hZ a)`
- **What**: The coordinate evaluation of a composed point is the composed evaluation.
- **Hypotheses**: hZ, hψ.
- **Uses from project**: `zChartHom_specPointComp`, `chartZRingEquiv`.
- **Used by**: `projTateMap_marking`, `pt_hord` (hevalX/hevalY), `zChartEval_fibrePt_coordX/Y`, `inducedPt_coordX/Y` (9 occurrences).
- **Visibility**: public
- **Lines**: 1655–1663 (proof 3 lines)
- **Notes**: —

### `theorem zChartEval_coordX`
- **Type**: `zChartEval W g hZ (coordX W) = zChartHom W g hZ (isLocalizationElem (X 2) (X 0))`
- **What**: The x-evaluation is the chart-ring hom at X₀/X₂.
- **Hypotheses**: hZ.
- **Uses from project**: `chartZRingEquiv_x` (imported), `coordX`, `HomogeneousLocalization.Away.isLocalizationElem`, `mk_X_mem_quotientGrading_one`.
- **Used by**: `zChartEval_tateP0SpecPoint_coordX`, `zChartEval_specPointBaseChange_coordX`, `chartSolution_zero_eq_eval`.
- **Visibility**: public
- **Lines**: 1666–1674 (proof 4 lines)
- **Notes**: —

### `theorem zChartEval_coordY`
- **Type**: y-analogue at X₁/X₂
- **What**: The y-evaluation is the chart-ring hom at X₁/X₂.
- **Hypotheses**: hZ.
- **Uses from project**: `chartZRingEquiv_y` (imported), `coordY`.
- **Used by**: `zChartEval_tateP0SpecPoint_coordY`, `zChartEval_specPointBaseChange_coordY`, `chartSolution_one_eq_eval`.
- **Visibility**: public
- **Lines**: 1677–1685 (proof 4 lines)
- **Notes**: —

### `theorem coordRingHom_ext`
- **Type**: `(φ ψ : W.toAffine.CoordinateRing →+* K)` agreeing on algebraMap-constants, coordX and coordY are equal
- **What**: An A-compatible hom out of the affine coordinate ring is determined by its values on coordX and coordY ({1, y} is a basis over R[x]).
- **How**: Reduces constants to `AdjoinRoot.of`-images, handles polynomials by `Polynomial.induction_on`, then decomposes an arbitrary element by mathlib's `Affine.CoordinateRing.exists_smul_basis_eq` and `CoordinateRing.smul`.
- **Hypotheses**: halg, hX, hY.
- **Uses from project**: `coordX`, `coordY` (imported); mathlib CoordinateRing basis API.
- **Used by**: `specPoint_ext_of_zChartEval`.
- **Visibility**: public
- **Lines**: 1687–1721 (proof ~28 lines; `omit` header at 1687)
- **Notes**: —

### `theorem specPoint_ext_of_zChartEval`
- **Type**: two Z-chart K-points with equal coordX/coordY evaluations are equal
- **What**: **Extensionality for Z-chart points** — evaluations pin the point.
- **How**: `coordRingHom_ext` gives equal evaluations, transported to equal chart homs via `chartZRingEquiv`, then both points are recovered from `Spec_map_zChartHom_awayι`.
- **Hypotheses**: hZ, hZ', hX, hY.
- **Uses from project**: `coordRingHom_ext`, `zChartEval_algebraMap`, `chartZRingEquiv`, `Spec_map_zChartHom_awayι`, `zChartHom`, `zChartEval`.
- **Used by**: `projTateMap_marking`, `projTateMap_eq_of_pointedIso` (hmp).
- **Visibility**: public
- **Lines**: 1725–1745 (proof ~17 lines)
- **Notes**: —

---

## Section `TateMarkedChart` (lines 1749–1824)

### `noncomputable def tateP0SpecPoint`
- **Type**: `SpecPoints (projModel (tateCurveLocOver R)) (projModelπ (tateCurveLocOver R)) (tateRingOver R)`
- **What**: The atlas marked point (0,0) as a Z-chart point of the universal Tate model over the atlas ring itself.
- **Hypotheses**: none.
- **Uses from project**: `tateP0mor`, `tateP0mor_π` (imported), `tateCurveLocOver`, `tateRingOver`, `SpecPoints`.
- **Used by**: `tateP0SpecPoint_inZChart`, `zChartHom_tateP0SpecPoint(+_isLocalizationElem)`, `zChartEval_tateP0SpecPoint_coordX/Y`, `projTateMap_marking`, `specPointBaseChange_inducedPt`, `inducedPt_coordX/Y` (13 occurrences).
- **Visibility**: public
- **Lines**: 1757–1761
- **Notes**: —

### `theorem tateP0mor_fac`
- **Type**: `tateP0mor R = Spec.map (ofHom ((chartSolutionsEquiv …).symm (tateP0sol R)).1) ≫ Proj.awayι … (X 2) …`
- **What**: `tateP0mor` factors through the Z-chart via the (0,0)-solution homomorphism (public replay of the [Y1-vi] factorisation).
- **Hypotheses**: none.
- **Uses from project**: `tateP0mor`, `tateP0sol`, `chartSolutionsEquiv`, `chartHomEquiv(_symm_coe)` (all imported), `tateCurveLocOver`, `tateRingOver`.
- **Used by**: `tateP0SpecPoint_inZChart`, `zChartHom_tateP0SpecPoint`.
- **Visibility**: public
- **Lines**: 1765–1775 (proof ~7 lines)
- **Notes**: —

### `theorem tateP0SpecPoint_inZChart`
- **Type**: `InZChart (tateCurveLocOver R) (tateP0SpecPoint R)`
- **What**: The marked point lies in the Z-chart.
- **Hypotheses**: none.
- **Uses from project**: `tateP0mor_fac`, `chartSolutionsEquiv`, `tateP0sol`, `InZChart`.
- **Used by**: `zChartHom_tateP0SpecPoint(+_isLocalizationElem)`, `zChartEval_tateP0SpecPoint_coordX/Y`, `projTateMap_marking`, `inducedPt_coordX/Y` (13 occurrences).
- **Visibility**: public
- **Lines**: 1778–1781 (term proof)
- **Notes**: —

### `theorem zChartHom_tateP0SpecPoint`
- **Type**: `zChartHom … (tateP0SpecPoint R) … = ((chartSolutionsEquiv …).symm (tateP0sol R)).1`
- **What**: The chart-ring hom of the marked point is the (0,0)-solution homomorphism.
- **Hypotheses**: none.
- **Uses from project**: `zChartHom_unique`, `tateP0mor_fac`, `chartSolutionsEquiv`, `tateP0sol`.
- **Used by**: `zChartHom_tateP0SpecPoint_isLocalizationElem`.
- **Visibility**: public
- **Lines**: 1784–1788 (term proof)
- **Notes**: —

### `theorem zChartHom_tateP0SpecPoint_isLocalizationElem`
- **Type**: for j ≠ 2, the chart hom of the marked point kills `isLocalizationElem (X 2) (X j)`
- **What**: The marked point's chart coordinates vanish (tateP0sol = (0,0)).
- **How**: `zChartHom_tateP0SpecPoint` then `chartCoordEquiv_mk_X` and `Equiv.apply_symm_apply` on `chartSolutionsEquiv`.
- **Hypotheses**: j ≠ 2.
- **Uses from project**: `zChartHom_tateP0SpecPoint`, `chartCoordEquiv(_mk_X)`, `chartSolutionsEquiv`, `tateP0sol`, `mk_X_mem_quotientGrading_one`.
- **Used by**: `zChartEval_tateP0SpecPoint_coordX`, `zChartEval_tateP0SpecPoint_coordY`.
- **Visibility**: public
- **Lines**: 1791–1808 (proof ~14 lines)
- **Notes**: —

### `theorem zChartEval_tateP0SpecPoint_coordX`
- **Type**: `zChartEval … (coordX (tateCurveLocOver R)) = 0`
- **What**: The marked point's x-evaluation is 0.
- **Hypotheses**: none.
- **Uses from project**: `zChartEval_coordX`, `zChartHom_tateP0SpecPoint_isLocalizationElem`.
- **Used by**: `projTateMap_marking`, `inducedPt_coordX`.
- **Visibility**: public
- **Lines**: 1811–1815 (proof 2 lines)
- **Notes**: —

### `theorem zChartEval_tateP0SpecPoint_coordY`
- **Type**: y-analogue = 0
- **What**: The marked point's y-evaluation is 0.
- **Hypotheses**: none.
- **Uses from project**: `zChartEval_coordY`, `zChartHom_tateP0SpecPoint_isLocalizationElem`.
- **Used by**: `projTateMap_marking`, `inducedPt_coordY`.
- **Visibility**: public
- **Lines**: 1818–1822 (proof 2 lines)
- **Notes**: —

---

## Section `BaseChangeChart` (lines 1826–2003)

### `theorem Spec_map_awayCongr_awayι`
- **Type**: for graded 𝒜 and s = t in 𝒜 1: `Spec.map (ofHom (awayCongr h).toRingHom) ≫ Proj.awayι 𝒜 s hs one_pos = Proj.awayι 𝒜 t (h ▸ hs) one_pos`
- **What**: `awayι` transports along an equality of the localized elements (public generic replica of the `awayι_awayCongr_local` pattern).
- **Hypotheses**: h : s = t, hs.
- **Uses from project**: `awayCongr`, `awayCongr_rfl` (imported).
- **Used by**: `awayι_projModelBaseChange`, `inZChart_of_comp_baseChange`.
- **Visibility**: public
- **Lines**: 1839–1847 (proof 4 lines, subst)
- **Notes**: —

### `theorem awayCongr_baseChangeMap_isLocalizationElem`
- **Type**: the chart transport of `projModelBaseChange` sends `Xⱼ/X₂` to `Xⱼ/X₂` of the mapped curve
- **What**: The base-change graded map fixes the localization coordinates.
- **How**: Rewrites both sides as `HomogeneousLocalization.Away.mk` presentations, pushes through `Away.map_mk` and `awayCongr_mk`, compares `val`s with `baseChangeGradedHom_mk_X`.
- **Hypotheses**: j : Fin 3.
- **Uses from project**: `awayCongr(_mk)`, `baseChangeGradedHom(_mk_X)` (imported), `HomogeneousLocalization.Away.map/mk/isLocalizationElem`, `mk_X_mem_quotientGrading_one`, `quotientGrading(Hom)`, `projIdeal`.
- **Used by**: `zChartEval_specPointBaseChange_coordX`, `zChartEval_specPointBaseChange_coordY`.
- **Visibility**: public
- **Lines**: 1853–1882 (proof ~21 lines)
- **Notes**: —

### `noncomputable def specPointBaseChange`
- **Type**: `(g : SpecPoints (projModel (W.map (algebraMap A B))) … K) : SpecPoints (projModel W) (projModelπ W) K`
- **What**: Push a Z-chart point of the base-changed model down to the original model (compose with `projModelBaseChange`).
- **Hypotheses**: `IsScalarTower A B K`.
- **Uses from project**: `projModelBaseChange(_π)` (imported), `SpecPoints`.
- **Used by**: `inZChart_specPointBaseChange`, `zChartHom_specPointBaseChange`, `zChartEval_specPointBaseChange_coordX/Y`, `projTateMap_marking`, `pt_hord`, `specPointBaseChange_fibrePt`, `specPointBaseChange_inducedPt`.
- **Visibility**: public
- **Lines**: 1887–1893
- **Notes**: —

### `theorem awayι_projModelBaseChange`
- **Type**: `awayι(mapped model) ≫ projModelBaseChange = Spec.map (ofHom (awayCongr∘Away.map)) ≫ awayι(W)`
- **What**: The assembled chart square: the Z-chart inclusion of the base-changed model composed with the base-change morphism factors through the original Z-chart.
- **How**: From `(isPullback_projModelBaseChange_chart W 2).w` (imported), corrected by `Spec_map_awayCongr_awayι`.
- **Hypotheses**: none extra.
- **Uses from project**: `isPullback_projModelBaseChange_chart` (imported), `Spec_map_awayCongr_awayι`, `awayCongr`, `baseChangeGradedHom(_mk_X)`, `HomogeneousLocalization.Away.map`.
- **Used by**: `inZChart_specPointBaseChange`, `zChartHom_specPointBaseChange`.
- **Visibility**: public
- **Lines**: 1897–1924 (proof ~14 lines)
- **Notes**: —

### `theorem inZChart_specPointBaseChange`
- **Type**: `InZChart (W.map …) g → InZChart W (specPointBaseChange W g)`
- **What**: Base change preserves the Z-chart.
- **Hypotheses**: hZ.
- **Uses from project**: `awayι_projModelBaseChange`, `Spec_map_zChartHom_awayι`, `zChartHom`, `specPointBaseChange`.
- **Used by**: `zChartHom_specPointBaseChange`, `zChartEval_specPointBaseChange_coordX/Y` statements, `pt_hord`, `fibrePt` lemmas, `inducedPt` lemmas (11 occurrences).
- **Visibility**: public
- **Lines**: 1927–1940 (proof ~9 lines)
- **Notes**: —

### `theorem zChartHom_specPointBaseChange`
- **Type**: chart hom of the pushed point = chart hom of g ∘ (awayCongr ∘ Away.map)
- **What**: The chart-ring homomorphism of a base-changed point.
- **How**: `zChartHom_unique` against the factoring built from `awayι_projModelBaseChange` and `Spec_map_zChartHom_awayι`.
- **Hypotheses**: hZ.
- **Uses from project**: `zChartHom_unique`, `awayι_projModelBaseChange`, `Spec_map_zChartHom_awayι`, `awayCongr`, `baseChangeGradedHom`.
- **Used by**: `zChartEval_specPointBaseChange_coordX`, `zChartEval_specPointBaseChange_coordY`.
- **Visibility**: public
- **Lines**: 1943–1967 (proof ~14 lines)
- **Notes**: —

### `theorem zChartEval_specPointBaseChange_coordX`
- **Type**: `zChartEval W (specPointBaseChange W g) … (coordX W) = zChartEval (W.map …) g hZ (coordX (W.map …))`
- **What**: Base change leaves the x-evaluation unchanged.
- **Hypotheses**: hZ.
- **Uses from project**: `zChartEval_coordX`, `zChartHom_specPointBaseChange`, `awayCongr_baseChangeMap_isLocalizationElem`.
- **Used by**: `projTateMap_marking`, `pt_hord`, `zChartEval_fibrePt_coordX`, `inducedPt_coordX`.
- **Visibility**: public
- **Lines**: 1970–1984 (proof ~8 lines)
- **Notes**: —

### `theorem zChartEval_specPointBaseChange_coordY`
- **Type**: y-analogue
- **What**: Base change leaves the y-evaluation unchanged.
- **Hypotheses**: hZ.
- **Uses from project**: `zChartEval_coordY`, `zChartHom_specPointBaseChange`, `awayCongr_baseChangeMap_isLocalizationElem`.
- **Used by**: `projTateMap_marking`, `pt_hord`, `zChartEval_fibrePt_coordY`, `inducedPt_coordY`.
- **Visibility**: public
- **Lines**: 1987–2001 (proof ~8 lines)
- **Notes**: —

---

## Section `ProjTateMap` (lines 2005–2186)

### `noncomputable def specPointPointedIso`
- **Type**: `(ε : projModel W₁ ≅ projModel W₂) (heπ) (g : SpecPoints W₁ K) : SpecPoints W₂ K`
- **What**: Transport of a point along a pointed isomorphism of models (g.1 ≫ ε.hom).
- **Hypotheses**: heπ.
- **Uses from project**: `SpecPoints`, `projModel(π)`.
- **Used by**: `inZChart_specPointPointedIso`, `markedPointNormalised`, `zChartEval_eqToHom_point`, `projTateMap_eq_of_pointedIso` (hmp).
- **Visibility**: public
- **Lines**: 2017–2023
- **Notes**: —

### `theorem inZChart_specPointPointedIso`
- **Type**: pointed isos preserve the Z-chart
- **What**: The transported point is in the Z-chart, witnessed through `pointedIsoAwayHom`.
- **Hypotheses**: heπ, hez, hZ.
- **Uses from project**: `pointedIsoAwayHom`, `Spec_map_pointedIsoAwayHom_awayι`, `Spec_map_zChartHom_awayι`, `zChartHom`.
- **Used by**: `markedPointNormalised_inZChart`, `projTateMap_eq_of_pointedIso` (hZT).
- **Visibility**: public
- **Lines**: 2026–2037 (proof ~6 lines)
- **Notes**: —

### `theorem tateCurveLocOver_map_marked`
- **Type**: `(tateCurveLocOver R).map (tateRingOverAlgLiftOfPoint R W (evals) …) = (tateNormalVariableChange …) • W`
- **What**: The specialisation of the universal Tate curve at the marked chart's atlas map is the T-E1 normal form of the chart.
- **Hypotheses**: R-algebra A, W elliptic, g in Z-chart, hord.
- **Uses from project**: `tateCurveLocOver_map_tateRingOverAlgLiftOfPoint`, `zChartEval_equation_self`, `tateRingOverAlgLiftOfPoint`.
- **Used by**: `tateNormalIso(_hom/_π/_zero)`, `markedPointNormalised_coords`, `projTateMap_unfold`, `projModelBaseChange_projTateMap`, `projTateMap_eq_of_pointedIso` (26 occurrences).
- **Visibility**: public
- **Lines**: 2046–2051 (term proof)
- **Notes**: —

### `noncomputable def tateNormalIso`
- **Type**: `projModel ((tateCurveLocOver R).map (atlas map)) ≅ projModel W`
- **What**: The normalising pointed isomorphism from the specialised universal Tate model onto the chart's model (eqToIso ∘ projModelVCIso).
- **Hypotheses**: chart data (g, hZ, hord).
- **Uses from project**: `tateCurveLocOver_map_marked`, `projModelVCIso` (imported), `tateNormalVariableChange`, `projModel`.
- **Used by**: `tateNormalIso_hom/_π/_zero/_zero_inv/_inv_π`, `markedPointNormalised(_sec/_inZChart/_coords)`, `projTateMap`, `projTateMap_isPullback/_zero/_marking`, `projTateMap_eq_of_pointedIso` (30 occurrences).
- **Visibility**: public
- **Lines**: 2055–2060
- **Notes**: —

### `theorem tateNormalIso_hom`
- **Type**: `(tateNormalIso …).hom = eqToHom … ≫ (projModelVCIso …).hom`
- **What**: The hom of the normalising iso in `transport_general` shape.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso`, `projModelVCIso`, `tateCurveLocOver_map_marked`.
- **Used by**: `tateNormalIso_π`, `tateNormalIso_zero`, `markedPointNormalised_coords`.
- **Visibility**: public
- **Lines**: 2063–2068 (proof 1 line)
- **Notes**: —

### `theorem eqToHom_projModelπ`
- **Type**: `eqToHom (congrArg projModel h) ≫ projModelπ V₂ = projModelπ V₁` for h : V₁ = V₂
- **What**: eqToHom transport of the structure morphism along a curve equality.
- **Hypotheses**: h.
- **Uses from project**: `projModel(π)`.
- **Used by**: `tateNormalIso_π`, `eqToIso_projModelπ`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2071–2073 (subst; simp)
- **Notes**: —

### `theorem eqToHom_projModelZero`
- **Type**: `projModelZero V₁ ≫ eqToHom … = projModelZero V₂`
- **What**: eqToHom transport of the zero section along a curve equality.
- **Hypotheses**: h.
- **Uses from project**: `projModelZero`.
- **Used by**: `tateNormalIso_zero`, `eqToIso_projModelZero`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2076–2078 (subst; simp)
- **Notes**: —

### `theorem tateNormalIso_π`
- **Type**: `(tateNormalIso …).hom ≫ projModelπ W = projModelπ (specialised model)`
- **What**: The normalising iso respects structure morphisms.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso_hom`, `projModelVCIso_π` (imported), `eqToHom_projModelπ`, `tateCurveLocOver_map_marked`.
- **Used by**: `markedPointNormalised`, `markedPointNormalised_inZChart`, `markedPointNormalised_coords`, `tateNormalIso_inv_π`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2081–2087 (proof 2 lines)
- **Notes**: —

### `theorem tateNormalIso_zero`
- **Type**: `projModelZero (specialised model) ≫ (tateNormalIso …).hom = projModelZero W`
- **What**: The normalising iso respects zero sections.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso_hom`, `eqToHom_projModelZero`, `projModelVCIso_zero` (imported), `tateCurveLocOver_map_marked`.
- **Used by**: `tateNormalIso_zero_inv`, `markedPointNormalised_coords`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2090–2096 (proof 2 lines)
- **Notes**: —

### `noncomputable def markedPointNormalised`
- **Type**: the marked point g transported into the specialised Tate model (via `(tateNormalIso …).symm`)
- **What**: The marked point, normalised into the specialised universal model.
- **Hypotheses**: chart data.
- **Uses from project**: `specPointPointedIso`, `tateNormalIso(_π)`.
- **Used by**: `markedPointNormalised_sec/_inZChart/_coords`, `projTateMap_marking`, `projTateMap_eq_of_pointedIso` (17 occurrences).
- **Visibility**: public
- **Lines**: 2099–2107
- **Notes**: —

### `theorem markedPointNormalised_sec`
- **Type**: `(markedPointNormalised …).1 ≫ (tateNormalIso …).hom = g.1`
- **What**: The normalised point returns to the marking through the normalising iso.
- **Hypotheses**: chart data.
- **Uses from project**: `markedPointNormalised`, `tateNormalIso`.
- **Used by**: `markedPointNormalised_coords`, `projTateMap_eq_of_pointedIso` (hχsec).
- **Visibility**: public
- **Lines**: 2110–2113 (proof 2 lines)
- **Notes**: —

### `theorem tateNormalIso_zero_inv`
- **Type**: `projModelZero W ≫ (tateNormalIso …).inv = projModelZero (specialised model)`
- **What**: Zero section respects the inverse normalising iso.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso_zero`.
- **Used by**: `markedPointNormalised_inZChart`, `projTateMap_zero`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2116–2122 (proof 2 lines)
- **Notes**: —

### `theorem markedPointNormalised_inZChart`
- **Type**: the normalised marked point is in the Z-chart
- **What**: Z-chart membership through `inZChart_specPointPointedIso` for the inverse iso.
- **Hypotheses**: chart data.
- **Uses from project**: `inZChart_specPointPointedIso`, `tateNormalIso(_π/_zero_inv)`, `markedPointNormalised`.
- **Used by**: `markedPointNormalised_coords`, `projTateMap_marking`, `projTateMap_eq_of_pointedIso` (13 occurrences).
- **Visibility**: public
- **Lines**: 2125–2132 (term proof)
- **Notes**: —

### `theorem markedPointNormalised_coords`
- **Type**: both coordinate evaluations of the normalised marked point are 0
- **What**: The normalised marking has coordinates (0,0) — the source-side marking pin.
- **How**: `zChartEval_pointedIso` along `tateNormalIso` at coordX/coordY, rewritten through `transport_general` + `bridge_coordX/Y` + `coordRingCongr` lemmas; `tateNormalVariableChange_r/_t` make the transforms `u²·x + x`-shaped, and `Units.mul_right_eq_zero` cancels the unit powers.
- **Hypotheses**: chart data.
- **Uses from project**: `zChartEval_pointedIso`, `tateNormalIso(_π/_zero/_hom)`, `markedPointNormalised(_sec/_inZChart)`, `transport_general`, `bridge_coordX/Y`, `coordRingCongr_algebraMap(_mul_coordX/_mul_coordY)`, `projModelVCIso(_π/_zero)`, `tateNormalVariableChange_r/_t`, `zChartEval_algebraMap`, `tateCurveLocOver_map_marked`.
- **Used by**: `projTateMap_marking`, `projTateMap_eq_of_pointedIso` (hmp).
- **Visibility**: public
- **Lines**: 2135–2184 (proof ~39 lines)
- **Notes**: proof >30 lines

---

## Section `ProjTateMapAssembly` (lines 2188–2297)

### `noncomputable def projTateMap`
- **Type**: `projModel W ⟶ projModel (tateCurveLocOver R)` from marked chart data (R, W, g, hZ, hord)
- **What**: The classifying morphism of a marked chart into the universal Tate model: `(tateNormalIso …).inv ≫ projModelBaseChange (atlas map) (tateCurveLocOver R)`.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso`, `projModelBaseChange` (imported), `tateRingOverAlgLiftOfPoint`, `zChartEval_equation_self`, `tateCurveLocOver`.
- **Used by**: `projTateMap_π/_isPullback/_zero/_marking/_unfold/_eq_of_pointedIso/_map_tate/_inducedPt`, `MarkedChartData.topMap`, `projModelBaseChange_projTateMap`, `fibreMap_topMap(_agree)`, `sameU_projTateMap_agree` (24 occurrences).
- **Visibility**: public
- **Lines**: 2199–2203
- **Notes**: —

### `theorem tateNormalIso_inv_π`
- **Type**: `(tateNormalIso …).inv ≫ projModelπ (specialised model) = projModelπ W`
- **What**: The inverse normalising iso respects structure morphisms.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso_π`.
- **Used by**: `projTateMap_π`, `projTateMap_isPullback`, `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2206–2210 (proof 1 line)
- **Notes**: —

### `theorem projTateMap_π`
- **Type**: `projTateMap … ≫ projModelπ (tateCurveLocOver R) = projModelπ W ≫ tateBaseSpecMapOfPoint …`
- **What**: The classifying morphism lies over the affine atlas map.
- **Hypotheses**: chart data.
- **Uses from project**: `projModelBaseChange_π`, `tateNormalIso_inv_π`, `tateBaseSpecMapOfPoint`, `projTateMap`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 2213–2219 (proof 3 lines)
- **Notes**: —

### `theorem projTateMap_isPullback`
- **Type**: `IsPullback (projTateMap …) (projModelπ W) (projModelπ (tateCurveLocOver R)) (tateBaseSpecMapOfPoint …)`
- **What**: The classifying square is cartesian.
- **How**: Pastes the iso square for `tateNormalIso.inv` (`IsPullback.of_horiz_isIso`) horizontally with the imported base-change cartesian square `isPullback_projModelBaseChange`.
- **Hypotheses**: chart data; installs the atlas-algebra `letI`.
- **Uses from project**: `isPullback_projModelBaseChange` (imported), `tateNormalIso_inv_π`, `projModelBaseChange`, `tateBaseSpecMapOfPoint`, `tateRingOverAlgLiftOfPoint`.
- **Used by**: `MarkedChartData.topMap_isPullback`.
- **Visibility**: public
- **Lines**: 2222–2248 (proof ~24 lines)
- **Notes**: —

### `theorem projTateMap_zero`
- **Type**: `projModelZero W ≫ projTateMap … = tateBaseSpecMapOfPoint … ≫ projModelZero (tateCurveLocOver R)`
- **What**: The classifying morphism is pointed.
- **Hypotheses**: chart data.
- **Uses from project**: `tateNormalIso_zero_inv`, `projModelZero_baseChange` (imported), `tateBaseSpecMapOfPoint`.
- **Used by**: `MarkedChartData.topMap_zero`.
- **Visibility**: public
- **Lines**: 2251–2260 (proof ~5 lines)
- **Notes**: —

### `theorem projTateMap_marking`
- **Type**: `g.1 ≫ projTateMap … = tateBaseSpecMapOfPoint … ≫ tateP0mor R`
- **What**: **The marking compatibility**: the classifying morphism carries the chart marking to the atlas marking (0,0).
- **How**: Both sides are Z-chart points of `tateCurveLocOver` over A with coordinates (0,0): the left is `specPointBaseChange (markedPointNormalised …)` (coords 0 by `markedPointNormalised_coords` + `zChartEval_specPointBaseChange_*`), the right is `specPointComp tateP0SpecPoint` (coords 0 by `zChartEval_tateP0SpecPoint_*`); `specPoint_ext_of_zChartEval` identifies them.
- **Hypotheses**: chart data.
- **Uses from project**: `specPoint_ext_of_zChartEval`, `specPointBaseChange`, `markedPointNormalised(_inZChart/_coords)`, `specPointComp`, `tateP0SpecPoint(_inZChart)`, `inZChart_specPointBaseChange`, `inZChart_specPointComp`, `zChartEval_specPointBaseChange_coordX/Y`, `zChartEval_specPointComp`, `zChartEval_tateP0SpecPoint_coordX/Y`, `tateP0mor`, `tateBaseSpecMapOfPoint`.
- **Used by**: `MarkedChartData.topMap_marking`.
- **Visibility**: public
- **Lines**: 2264–2295 (proof ~28 lines)
- **Notes**: —

---

## Section `ProjTateMapComparison` (lines 2299–2454) — ENGINE (top half)

### `theorem eqToIso_projModelπ`
- **Type**: `(eqToIso (congrArg projModel h)).hom ≫ projModelπ V₂ = projModelπ V₁`
- **What**: eqToIso transport of the structure morphism.
- **Hypotheses**: h : V₁ = V₂.
- **Uses from project**: `eqToHom_projModelπ`.
- **Used by**: `zChartEval_eqToHom_point` (statement), `projTateMap_eq_of_pointedIso` (hmp/hZT).
- **Visibility**: public
- **Lines**: 2311–2314 (proof 2 lines)
- **Notes**: —

### `theorem eqToIso_projModelZero`
- **Type**: zero-section analogue
- **What**: eqToIso transport of the zero section.
- **Hypotheses**: h.
- **Uses from project**: `eqToHom_projModelZero`.
- **Used by**: `projTateMap_eq_of_pointedIso` (hZT).
- **Visibility**: public
- **Lines**: 2317–2320 (proof 2 lines)
- **Notes**: —

### `theorem zChartEval_eqToHom_point`
- **Type**: transporting a Z-chart point along a curve equality preserves evaluations up to `coordRingCongr h.symm`
- **What**: Chart-evaluation transport along `eqToIso`-transported points.
- **How**: subst h; shows the transported point is g itself (eqToHom_refl) and uses `coordRingCongr_refl_apply`.
- **Hypotheses**: h, hZ, hZ'.
- **Uses from project**: `specPointPointedIso`, `eqToIso_projModelπ`, `coordRingCongr(_refl_apply)` (imported), `zChartEval`.
- **Used by**: `projTateMap_eq_of_pointedIso` (hmp, twice).
- **Visibility**: public
- **Lines**: 2323–2341 (proof ~13 lines)
- **Notes**: —

### `theorem eqToHom_projModelBaseChange`
- **Type**: `eqToHom (congrArg (projModel ∘ W.map ·) h) ≫ projModelBaseChange f₂ W = projModelBaseChange f₁ W` for h : f₁ = f₂
- **What**: eqToHom transport of the base-change morphism along an equality of ring maps.
- **Hypotheses**: h.
- **Uses from project**: `projModelBaseChange`.
- **Used by**: `projTateMap_eq_of_pointedIso`.
- **Visibility**: public
- **Lines**: 2344–2349 (subst proof)
- **Notes**: —

### `theorem projTateMap_eq_of_pointedIso`
- **Type**: for a marked pointed iso ε (heπ, hez, hsec): `ε.hom ≫ projTateMap R W₂ g₂ hZ₂ hord₂ = projTateMap R W₁ g₁ hZ₁ hord₁`
- **What**: **ENGINE, top half**: the classifying model morphisms of two marked charts linked by a marked pointed iso agree.
- **How**: The base half gives equal atlas maps (hφ); builds the canonical comparison χ = (tateNormalIso₁)⁻¹ ≫ eqToIso ≫ tateNormalIso₂, proves it pointed and marking-carrying (via `specPoint_ext_of_zChartEval` on the two normalised markings with `zChartEval_eqToHom_point` + `markedPointNormalised_coords`); both ε and χ are variable changes (`pointedIso_exists_variableChange`), and `tateNormalVariableChange_mul` applied to each forces C = C' by `mul_left_cancel`, hence ε.hom = χ.hom; conclude by unfolding both projTateMaps and cancelling with `eqToHom_projModelBaseChange`.
- **Hypotheses**: heπ, hez, hsec, hord₁, hord₂ (include heπ hez hsec).
- **Uses from project**: `tateRingOverAlgLiftOfPoint_eq_of_pointedIso`, `tateNormalIso(_π/_zero/_zero_inv/_inv_π)`, `eqToHom_projModelπ/Zero`, `specPointPointedIso`, `inZChart_specPointPointedIso`, `eqToIso_projModelπ/Zero`, `zChartEval_eqToHom_point`, `coordRingCongr_coordX/Y` (imported), `markedPointNormalised(_sec/_inZChart/_coords)`, `specPoint_ext_of_zChartEval`, `pointedIso_exists_variableChange`, `zChartEval_coords_of_pointedIso`, `tateNormalVariableChange_mul`, `eqToHom_projModelBaseChange`, `projModelBaseChange`, `tateCurveLocOver_map_marked`.
- **Used by**: `MarkedChartData.fibreMap_topMap_agree`, `MarkedChartData.sameU_projTateMap_agree`.
- **Visibility**: public
- **Lines**: 2365–2452 (proof ~84 lines)
- **Notes**: proof >30 lines

---

## Section `ChartPackaging` (lines 2456–2602)

### `theorem EllipticCurve.zeroPoint_eq_zero`
- **Type**: `(E : EllipticCurve S) (g : T ⟶ S) : E.zeroPoint g = 0`
- **What**: The zero point is the group zero of `E.Point g` (unwinds the `pointAddCommGroup` transport and `one_eq_zero`).
- **Hypotheses**: none.
- **Uses from project**: `EllipticCurve.zeroPoint`, `Hom.commGroup`, `one_eq_zero` (imported from EllipticCurve development); monoidal `η[E.asOver]`.
- **Used by**: `MarkedChartData.pull_eq_zero_of_pt_eq_zero`.
- **Visibility**: public
- **Lines**: 2477–2486 (proof ~8 lines)
- **Notes**: in `namespace EllipticCurve`; section has local `Over.cartesianMonoidalCategory/braidedCategory` instances

### `structure MarkedChartData`
- **Type**: `(R : CommRingCat) (Y : EllObj R)` with fields `U : Y.base.affineOpens`, `W : WeierstrassCurve Γ(U)`, `hell : W.IsElliptic`, `e : pullback Y.curve.π U.1.ι ≅ projModel W`, `heπ`, `hez`
- **What**: One `LocallyWeierstrass` chart of the curve of an Ell/R object: an affine open with a pointed Weierstrass trivialisation of the restricted curve (v10.109 recipe step 1).
- **Hypotheses**: heπ (π-compatibility with isoSpec), hez (zero-section compatibility).
- **Uses from project**: `EllObj`, `projModel(π)`, `projModelZero`.
- **Used by**: everything in `namespace MarkedChartData` (55+ occurrences); `attribute [instance] MarkedChartData.hell` at 2510.
- **Visibility**: public
- **Lines**: 2494–2508 (+2510 attribute)
- **Notes**: —

### `theorem MarkedChartData.exists_mem`
- **Type**: `(Y : EllObj R) (s : Y.base) : ∃ D : MarkedChartData R Y, s ∈ D.U.1`
- **What**: Every point of the base lies in some marked chart (repackages `Y.curve.localModel`).
- **Hypotheses**: none.
- **Uses from project**: `MarkedChartData`, `EllipticCurveGeom.localModel` (imported field).
- **Used by**: `chartAt`, `chartAt_mem`.
- **Visibility**: public
- **Lines**: 2517–2520 (proof 2 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.restrictSection`
- **Type**: `(P : Y.curve.Section) : D.U.1.toScheme ⟶ pullback Y.curve.π D.U.1.ι`
- **What**: The restriction of a section of Y.curve to the chart, as a section of the restricted curve (pullback.lift of U.ι ≫ P.1 and 𝟙).
- **Hypotheses**: none.
- **Uses from project**: `EllipticCurve.Section` (imported).
- **Used by**: `pt`, `pull_eq_zero_of_pt_eq_zero`, `fibreSection_comp_bc`, `topMap_marking`, `gluedTopMap_marking`, `inducedPt_comp_bc`, `chart_baseMap_eq/chart_topMap_eq` (27 occurrences).
- **Visibility**: public
- **Lines**: 2526–2529
- **Notes**: —

### `noncomputable def MarkedChartData.pt`
- **Type**: `(P : Y.curve.Section) : SpecPoints (projModel D.W) (projModelπ D.W) Γ(U)`
- **What**: The section, read in the chart as a Γ(U)-point of the Weierstrass model (isoSpec.inv ≫ restrictSection ≫ e.hom).
- **Hypotheses**: none.
- **Uses from project**: `restrictSection`, `SpecPoints`, `MarkedChartData.heπ`.
- **Used by**: pervasive in the MarkedChartData development (358 occurrences of `pt`): `pt_coe`, `pt_inZChart`, `pt_hord`, `baseMap`, `topMap`, `fibrePt` bridges, overlap/gluing/pin theorems.
- **Visibility**: public
- **Lines**: 2532–2539
- **Notes**: —

### `theorem MarkedChartData.pt_coe`
- **Type**: `(D.pt P).1 = D.U.2.isoSpec.inv ≫ D.restrictSection P ≫ D.e.hom` (rfl)
- **What**: Unfolding equation for the chart point.
- **Hypotheses**: none.
- **Uses from project**: `pt`, `restrictSection`.
- **Used by**: `pull_eq_zero_of_pt_eq_zero`, `fibreSection_comp_bc`, `topMap_marking`, `chart_baseMap_eq`, `chart_topMap_eq` (8 occurrences).
- **Visibility**: public
- **Lines**: 2541–2543 (rfl)
- **Notes**: @[simp]

### `noncomputable def MarkedChartData.geomPt`
- **Type**: `(t : Spec k ⟶ Spec Γ(U)) : Spec k ⟶ Y.base`
- **What**: The geometric point of the base attached to a point of the chart ring (t ≫ isoSpec.inv ≫ U.ι).
- **Hypotheses**: none.
- **Uses from project**: `MarkedChartData`.
- **Used by**: `pull_eq_zero_of_pt_eq_zero`, `pt_inZChart`, `fibreMap`, `fibreSection`, `fibreChartIso` chain, overlap-agreement theorems, `test_baseMap_agree`, `test_topMap_agree` (159 occurrences).
- **Visibility**: public
- **Lines**: 2546–2549
- **Notes**: —

### `theorem MarkedChartData.pull_eq_zero_of_pt_eq_zero`
- **Type**: `(t : Spec k ⟶ Spec Γ(U))` field point with `t ≫ (D.pt P).1 = t ≫ projModelZero D.W` implies `EllipticCurve.Point.pull Y.curve (D.geomPt t) P = 0`
- **What**: **Unwinding**: if a field point of the chart hits the model zero, the pulled section is the zero point on the base.
- **How**: Rewrites the zero side through D.hez, cancels the mono e.hom, projects with pullback.fst, and concludes with `zeroPoint_eq_zero` and Subtype.ext.
- **Hypotheses**: Field k, heq.
- **Uses from project**: `pt_coe`, `MarkedChartData.hez`, `EllipticCurve.Point.pull` (imported), `EllipticCurve.zeroPoint_eq_zero`, `geomPt`.
- **Used by**: `pt_inZChart`.
- **Visibility**: public
- **Lines**: 2553–2575 (proof ~19 lines)
- **Notes**: —

### `theorem MarkedChartData.pt_inZChart`
- **Type**: `Y.curve.NowhereGeomOrderLEThree P → InZChart D.W (D.pt P)`
- **What**: **B1 fibre bridge**: a nowhere-small-order section lies in the Z-chart of every marked chart.
- **How**: `inZChart_of_forall_ne_zero` reduces to field points; pushing to the algebraic closure, a zero hit would give `pull P = 0` by `pull_eq_zero_of_pt_eq_zero`, contradicting `hP … 1` (a = 1 case of NowhereGeomOrderLEThree).
- **Hypotheses**: hP.
- **Uses from project**: `inZChart_of_forall_ne_zero`, `pull_eq_zero_of_pt_eq_zero`, `geomPt`, `NowhereGeomOrderLEThree` (imported).
- **Used by**: pervasive (421 occurrences of `pt_inZChart`): `pt_hord`, `baseMap`, `topMap`, `fibrePt` lemmas, overlap/gluing/pin theorems.
- **Visibility**: public
- **Lines**: 2579–2598 (proof ~17 lines)
- **Notes**: —

---

## Section `FibreBridges` (lines 2604–2771)

### `noncomputable def pullbackChartIso`
- **Type**: `(hsq : IsPullback top q (projModelπ W) (Spec.map (algebraMap A B))) : F ≅ projModel (W.map (algebraMap A B))`
- **What**: A cartesian square over Spec of the algebra map presents its source as the model of the base-changed curve (`isoIsPullback` against `isPullback_projModelBaseChange`).
- **Hypotheses**: hsq.
- **Uses from project**: `isPullback_projModelBaseChange` (imported), `projModel(π)`.
- **Used by**: `pullbackChartIso_hom_bc/_hom_π/_zero`, `fibreChartIso`, `inducedChart` (13 occurrences).
- **Visibility**: public
- **Lines**: 2628–2629
- **Notes**: —

### `theorem pullbackChartIso_hom_bc`
- **Type**: `(pullbackChartIso W hsq).hom ≫ projModelBaseChange (algebraMap A B) W = top`
- **What**: First projection equation of the comparison iso.
- **Hypotheses**: hsq.
- **Uses from project**: `pullbackChartIso`, `isPullback_projModelBaseChange`, `projModelBaseChange`.
- **Used by**: `pullbackChartIso_zero`, `fibreSection_comp_bc`, `fibreMap_topMap`, `inducedPt_comp_bc`, `chart_topMap_eq` (6 occurrences).
- **Visibility**: public
- **Lines**: 2631–2634 (term proof)
- **Notes**: @[reassoc (attr := simp)]

### `theorem pullbackChartIso_hom_π`
- **Type**: `(pullbackChartIso W hsq).hom ≫ projModelπ (W.map …) = q`
- **What**: Second projection equation.
- **Hypotheses**: hsq.
- **Uses from project**: `pullbackChartIso`, `isPullback_projModelBaseChange`.
- **Used by**: `pullbackChartIso_zero`, `fibreCurveIso_π`, `fibrePt`, `fibreModelIso_π`, `inducedChart` (heπ field), `chart_baseMap_eq/chart_topMap_eq` (9 occurrences).
- **Visibility**: public
- **Lines**: 2636–2639 (term proof)
- **Notes**: @[reassoc (attr := simp)]

### `theorem pullbackChartIso_zero`
- **Type**: given a zero-compatible splitting zF of the square, `zF ≫ (pullbackChartIso W hsq).hom = projModelZero (W.map …)`
- **What**: The chart iso is pointed.
- **How**: `(isPullback_projModelBaseChange W).hom_ext` on both projections using `projModelZero_baseChange` and `projModelZero_projModelπ`.
- **Hypotheses**: hzq, hztop.
- **Uses from project**: `isPullback_projModelBaseChange`, `pullbackChartIso_hom_bc/_hom_π`, `projModelZero_baseChange`, `projModelZero_projModelπ` (imported).
- **Used by**: `fibre_zero_comp`, `inducedChart` (hez field).
- **Visibility**: public
- **Lines**: 2642–2650 (proof ~6 lines)
- **Notes**: —

### `theorem inZChart_of_comp_baseChange`
- **Type**: a point of the base-changed model whose composite with `projModelBaseChange` factors through the Z-chart of W is itself in the Z-chart
- **What**: The chart square is cartesian, so Z-chart membership descends along base change.
- **How**: Lifts against `isPullback_projModelBaseChange_chart` and corrects by `Spec_map_awayCongr_awayι` with `(baseChangeGradedHom_mk_X W 2).symm`.
- **Hypotheses**: hfac (the factoring).
- **Uses from project**: `isPullback_projModelBaseChange_chart` (imported), `Spec_map_awayCongr_awayι`, `awayCongr`, `baseChangeGradedHom_mk_X`, `InZChart`.
- **Used by**: `pt_hord` (hZfin), `fibrePt_inZChart`.
- **Visibility**: public
- **Lines**: 2654–2674 (proof ~11 lines)
- **Notes**: —

### `noncomputable def sectionMapIso`
- **Type**: `(E₁ E₂ : EllipticCurve T) (iso : E₁.E ≅ E₂.E) (hπ) (s : E₁.Section) : E₂.Section`
- **What**: Transport of sections along a pointed isomorphism of elliptic curves over the same base.
- **Hypotheses**: hπ.
- **Uses from project**: `EllipticCurve.Section`.
- **Used by**: `sectionMapIso_injective`, `sectionMapIso_add`, `sectionMapIsoHom`, `pt_hord` (s₁).
- **Visibility**: public
- **Lines**: 2685–2686
- **Notes**: —

### `theorem sectionMapIso_injective`
- **Type**: `Function.Injective (sectionMapIso E₁ E₂ iso hπ)`
- **What**: Section transport along an iso is injective (compose with iso.inv).
- **Hypotheses**: none extra.
- **Uses from project**: `sectionMapIso`.
- **Used by**: `pt_hord` (hfs0).
- **Visibility**: public
- **Lines**: 2688–2692 (proof 4 lines)
- **Notes**: —

### `theorem sectionMapIso_add`
- **Type**: `[IsLocallyNoetherian T] → sectionMapIso … (s + s') = sectionMapIso … s + sectionMapIso … s'`
- **What**: **GME Cor 2.2.5 for a raw pointed iso**: section transport along a pointed isomorphism is additive.
- **How**: Builds the Over-category hom f from iso; `isMonHom_of_one_comp_eq'` (imported PullSectionAdd engine, needs properness/flatness/universal O-connectedness/separatedness instances, smoothness via `SmoothOfRelativeDimension.smooth`) shows f is a monoid hom; then transports `pointEquivOverHom_add` along the lift/tensorHom calculus.
- **Hypotheses**: hπ, hz, IsLocallyNoetherian T.
- **Uses from project**: `isMonHom_of_one_comp_eq'` (imported), `EllipticCurve.pointEquivOverHom(_add)` (imported), `toEllipticCurveGeom.universallyOConnected` (imported), `one_eq_zero`, `sectionMapIso`, `EllipticCurve.asOver`.
- **Used by**: `sectionMapIsoHom`.
- **Visibility**: public
- **Lines**: 2696–2749 (proof ~48 lines)
- **Notes**: proof >30 lines

### `noncomputable def sectionMapIsoHom`
- **Type**: `[IsLocallyNoetherian T] : E₁.Section →+ E₂.Section`
- **What**: The additive bundle of the section transport.
- **Hypotheses**: hπ, hz.
- **Uses from project**: `sectionMapIso(_add)`.
- **Used by**: `pt_hord` (hfs0).
- **Visibility**: public
- **Lines**: 2752–2753
- **Notes**: —

### `noncomputable def EllipticCurve.pointCongr`
- **Type**: `(h : g₁ = g₂) : E.Point g₁ ≃+ E.Point g₂`
- **What**: Points over equal base morphisms, additively (h ▸ AddEquiv.refl).
- **Hypotheses**: h.
- **Uses from project**: `EllipticCurve.Point`.
- **Used by**: `EllipticCurve.pointCongr_coe`, `fibreSection`, `pt_hord` (sk, hs₁0, hpull0), `fibreSection_coe` (18 dot-notation occurrences).
- **Visibility**: public
- **Lines**: 2762–2763
- **Notes**: —

### `theorem EllipticCurve.pointCongr_coe`
- **Type**: `(E.pointCongr h P).1 = P.1`
- **What**: The transport does not change the underlying morphism.
- **Hypotheses**: h.
- **Uses from project**: `EllipticCurve.pointCongr`.
- **Used by**: `fibreSection_coe`, `pt_hord` (hgfin1, h3).
- **Visibility**: public
- **Lines**: 2765–2767 (subst; rfl)
- **Notes**: @[simp]

---

## Section `FibreGeometry` (lines 2773–2953)

### `noncomputable abbrev MarkedChartData.specPt`
- **Type**: `(k) [CommRing k] [Algebra Γ(U) k] : Spec (.of k) ⟶ Spec (.of Γ(U))`
- **What**: The Spec point of the chart ring attached to a chart-ring algebra k.
- **Hypotheses**: algebra structure.
- **Uses from project**: `MarkedChartData`.
- **Used by**: pervasive (182 occurrences): `fibreMap`, `fibreTop`, `fibreChartIso`, `fibreSection`, `pt_hord`, `fibrePt` lemmas, overlap-agreement, `test_baseMap_agree`, `test_topMap_agree`.
- **Visibility**: public
- **Lines**: 2788–2790
- **Notes**: abbrev

### `noncomputable def MarkedChartData.fibreMap`
- **Type**: `pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ pullback Y.curve.π D.U.1.ι`
- **What**: The comparison from the fibre pullback to the chart pullback (pullback.map over specPt ≫ isoSpec.inv).
- **Hypotheses**: none.
- **Uses from project**: `geomPt`, `specPt`.
- **Used by**: `fibreMap_isPullback`, `fibreTop`, `fibre_zero_comp`, `fibreSection_comp_bc`, `fibreMap_topMap(_agree)`, `test_topMap_agree` (37 occurrences).
- **Visibility**: public
- **Lines**: 2793–2797
- **Notes**: —

### `theorem MarkedChartData.fibreMap_isPullback`
- **Type**: `IsPullback (D.fibreMap k) (pullback.snd …) (pullback.snd …) (D.specPt k ≫ D.U.2.isoSpec.inv)`
- **What**: The comparison square over the chart inclusion is cartesian (pullback-of-pullback via `IsPullback.of_right`).
- **Hypotheses**: none.
- **Uses from project**: `fibreMap`, `geomPt`, `specPt`.
- **Used by**: `fibreTop_isPullback`.
- **Visibility**: public
- **Lines**: 2800–2809 (proof ~7 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.fibreTop`
- **Type**: `pullback Y.curve.π (D.geomPt (D.specPt k)) ⟶ projModel D.W`
- **What**: The fibre presented over the chart model (fibreMap ≫ e.hom).
- **Hypotheses**: none.
- **Uses from project**: `fibreMap`.
- **Used by**: `fibreTop_isPullback`.
- **Visibility**: public
- **Lines**: 2812–2814
- **Notes**: —

### `theorem MarkedChartData.fibreTop_isPullback`
- **Type**: `IsPullback (D.fibreTop k) (pullback.snd …) (projModelπ D.W) (D.specPt k)`
- **What**: The fibre square over the chart model is cartesian (paste fibreMap square with the trivialisation iso square).
- **Hypotheses**: none.
- **Uses from project**: `fibreMap_isPullback`, `MarkedChartData.heπ`, `fibreTop`.
- **Used by**: `fibreChartIso`, `fibre_zero_comp`, `fibreSection_comp_bc`, `fibreCurveIso_π`, `fibrePt`, `fibreModelIso_π/_zero`, `fibreMap_topMap` (9 occurrences).
- **Visibility**: public
- **Lines**: 2817–2825 (proof ~6 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.fibreChartIso`
- **Type**: `pullback Y.curve.π (D.geomPt (D.specPt k)) ≅ projModel (D.W.map (algebraMap Γ(U) k))`
- **What**: The fibre of the curve as the model of the base-changed chart curve (pullbackChartIso at the fibre square).
- **Hypotheses**: none.
- **Uses from project**: `pullbackChartIso`, `fibreTop_isPullback`.
- **Used by**: `fibre_zero_comp`, `fibreCurveIso`, `fibreSection_comp_bc`, `pt_hord`, `fibrePt`, `fibreModelIso`, `fibrePt_fibreModelIso` (38 occurrences).
- **Visibility**: public
- **Lines**: 2828–2831
- **Notes**: —

### `theorem MarkedChartData.fibre_zero_comp`
- **Type**: `(Y.curve.baseChange (D.geomPt (D.specPt k))).zero ≫ (D.fibreChartIso k).hom = projModelZero (D.W.map …)`
- **What**: The zero section of the fibre curve, in chart coordinates.
- **How**: `pullbackChartIso_zero` with the zero lift; the zero lift composed through fibreMap is identified by `pullback.hom_ext` with the D.hez witness.
- **Hypotheses**: none.
- **Uses from project**: `pullbackChartIso_zero`, `fibreTop_isPullback`, `fibreMap`, `MarkedChartData.hez`, `geomPt`, `specPt`, `EllipticCurve.baseChange` (imported).
- **Used by**: `fibreCurveIso_zero`, `fibreModelIso_zero` (h1).
- **Visibility**: public
- **Lines**: 2834–2860 (proof ~23 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.fibreSection`
- **Type**: `(P : Y.curve.Section) : (Y.curve.baseChange (D.geomPt (D.specPt k))).Section`
- **What**: The pulled section, as a section of the fibre curve (via `baseChangeEquiv.symm` and `pointCongr`).
- **Hypotheses**: none.
- **Uses from project**: `EllipticCurve.Point.baseChangeEquiv` (imported), `EllipticCurve.pointCongr`, `EllipticCurve.Point.pull` (imported), `geomPt`, `specPt`.
- **Used by**: `fibreSection_coe`, `fibreSection_comp_bc`, `pt_hord`, `fibrePt`, `fibrePt_fibreModelIso` (47 occurrences).
- **Visibility**: public
- **Lines**: 2863–2867
- **Notes**: —

### `theorem MarkedChartData.fibreSection_coe`
- **Type**: `(D.fibreSection k P).1 = pullback.lift ((D.geomPt (D.specPt k)) ≫ P.1) (𝟙 _) …`
- **What**: The underlying morphism of the fibre section is the canonical lift.
- **How**: Unfolds the AddEquiv round-trip (`baseChangeEquiv_apply_coe`, `pointCongr_coe`), then `pullback.hom_ext`.
- **Hypotheses**: none.
- **Uses from project**: `fibreSection`, `EllipticCurve.Point.baseChangeEquiv_apply_coe` (imported), `EllipticCurve.pointCongr_coe`.
- **Used by**: `fibreSection_comp_bc` (hfs1), `fibrePt_fibreModelIso` (hfs).
- **Visibility**: public
- **Lines**: 2870–2885 (proof ~12 lines)
- **Notes**: —

### `theorem MarkedChartData.fibreSection_comp_bc`
- **Type**: `(D.fibreSection k P).1 ≫ (D.fibreChartIso k).hom ≫ projModelBaseChange … D.W = D.specPt k ≫ (D.pt P).1`
- **What**: **The value chase**: the fibre section, read through the fibre chart and base change, is the chart point composed at the geometric point.
- **How**: `pullbackChartIso_hom_bc` turns the left side into `fibreSection ≫ fibreMap ≫ e.hom`; a `pullback.hom_ext` calc (using `fibreSection_coe`, `fibreMap` lift equations and `restrictSection` equations) identifies `fibreSection ≫ fibreMap = (specPt ≫ isoSpec.inv) ≫ restrictSection P`; conclude with `pt_coe`.
- **Hypotheses**: none.
- **Uses from project**: `pullbackChartIso_hom_bc`, `fibreTop_isPullback`, `fibreSection(_coe)`, `fibreMap`, `restrictSection`, `pt_coe`, `geomPt`, `specPt`, `projModelBaseChange`.
- **Used by**: `pt_hord` (hcomp), `fibrePt_comp_bc`.
- **Visibility**: public
- **Lines**: 2889–2949 (proof ~57 lines)
- **Notes**: proof >30 lines (long explicit calc chains)

---

## Section `FibreEnrichment` (lines 2955–3230)

### `theorem eqToGeom_π'`
- **Type**: `(h : G₁ = G₂) : G₁.π = eqToHom (congrArg EllipticCurveGeom.E h) ≫ G₂.π`
- **What**: eqToHom transport of the structure morphism along a geometric-record equality.
- **Hypotheses**: h.
- **Uses from project**: `EllipticCurveGeom` (imported).
- **Used by**: `fibreCurve_π_eq`.
- **Visibility**: public
- **Lines**: 2960–2962 (subst; simp)
- **Notes**: —

### `theorem eqToGeom_zero'`
- **Type**: `G₁.zero = G₂.zero ≫ eqToHom ….symm`
- **What**: eqToHom transport of the zero section along a geometric-record equality.
- **Hypotheses**: h.
- **Uses from project**: `EllipticCurveGeom`.
- **Used by**: `fibreCurve_zero_eq`, `gluedTopMapEll_zero`, `inducedChart` (hz).
- **Visibility**: public
- **Lines**: 2965–2967 (subst; simp)
- **Notes**: —

### `noncomputable def affinePointCongr`
- **Type**: `(h : V₁ = V₂) : V₁.toAffine.Point ≃+ V₂.toAffine.Point`
- **What**: Affine points over equal curves, additively (h ▸ AddEquiv.refl).
- **Hypotheses**: field k, DecidableEq k.
- **Uses from project**: none (mathlib Affine.Point).
- **Used by**: `affinePointCongr_some`, `pt_hord` (hcontra2).
- **Visibility**: public
- **Lines**: 2970–2972
- **Notes**: —

### `theorem affinePointCongr_some`
- **Type**: `affinePointCongr h (some x y hns) = some x y (h ▸ hns)`
- **What**: The congruence fixes affine coordinates.
- **Hypotheses**: h.
- **Uses from project**: `affinePointCongr`.
- **Used by**: `pt_hord` (hcontra2).
- **Visibility**: public
- **Lines**: 2974–2978 (subst; rfl)
- **Notes**: —

### `theorem zChartEval_congr`
- **Type**: `(h : g = g') → zChartEval W g hZ a = zChartEval W g' hZ' a`
- **What**: Chart evaluation only depends on the point (proof-irrelevance across InZChart witnesses).
- **Hypotheses**: h.
- **Uses from project**: `zChartEval`, `SpecPoints`, `InZChart`.
- **Used by**: `pt_hord` (hevalX/hevalY), `zChartEval_fibrePt_coordX/Y`, `inducedPt_coordX/Y` (7 occurrences).
- **Visibility**: public
- **Lines**: 2981–2985 (subst; rfl)
- **Notes**: —

### `theorem chartSolution_val`
- **Type**: `(chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j = zChartHom W g hZ (chartCoordEquiv W 2 (mk (X j)))` (rfl)
- **What**: The chart-solution coordinates are the chart-ring hom at the chart coordinates (over any ring).
- **Hypotheses**: j ≠ 2.
- **Uses from project**: `chartSolutionsEquiv`, `chartHomEquiv`, `chartCoordEquiv` (imported), `zChartHom`.
- **Used by**: `chartSolution_zero_eq_eval`, `chartSolution_one_eq_eval`.
- **Visibility**: public
- **Lines**: 2989–2995 (rfl)
- **Notes**: —

### `theorem chartSolution_zero_eq_eval`
- **Type**: the chart-solution x-coordinate is the coordX-evaluation
- **What**: Aligns `chartSolutionsEquiv` coordinates with `zChartEval`.
- **Hypotheses**: hZ.
- **Uses from project**: `chartSolution_val`, `zChartEval_coordX`, `chartCoordEquiv_mk_X` (imported).
- **Used by**: `pt_hord` (hval).
- **Visibility**: public
- **Lines**: 2998–3005 (proof 3 lines)
- **Notes**: —

### `theorem chartSolution_one_eq_eval`
- **Type**: y-analogue
- **What**: Aligns the second coordinate.
- **Hypotheses**: hZ.
- **Uses from project**: `chartSolution_val`, `zChartEval_coordY`, `chartCoordEquiv_mk_X`.
- **Used by**: `pt_hord` (hval).
- **Visibility**: public
- **Lines**: 3008–3015 (proof 3 lines)
- **Notes**: —

### `instance (unnamed): (D.W.map (algebraMap Γ(U) k)).IsElliptic`
- **Type**: `(D.W.map (algebraMap ↑Γ(Y.base, D.U.1) k)).IsElliptic`
- **What**: Registers ellipticity of the base-changed chart curve (defeq repackaging via `inferInstanceAs`, sourced from `MarkedChartData.hell` + mathlib's map instance).
- **Hypotheses**: D, k with algebra.
- **Uses from project**: `MarkedChartData.hell` (instance attribute).
- **Used by**: implicitly by every declaration about `D.W.map (algebraMap Γ(U) k)` (fibreCurve, fibrePt, etc.).
- **Visibility**: public (instance)
- **Lines**: 3022–3023
- **Notes**: —

### `noncomputable def MarkedChartData.fibreGeom`
- **Type**: `EllipticCurveGeom (Spec (.of k))`
- **What**: The geometric record of the fibre model: E = projModel of the mapped curve with its π, zero, smoothness, properness, and locallyWeierstrass fields.
- **Hypotheses**: none.
- **Uses from project**: `projModel(π)`, `projModelZero`, `projModelZero_projModelπ`, `projModel_smooth`, `projModelπ_isProper`, `projModel_locallyWeierstrass` (all imported).
- **Used by**: `fibreCurve_geom` (statement).
- **Visibility**: public
- **Lines**: 3026–3033
- **Notes**: —

### `noncomputable def MarkedChartData.fibreCurve`
- **Type**: `EllipticCurve (Spec (.of k))`
- **What**: The fibre working record: the mulOver-based model record `modelEllipticCurve` of the mapped chart curve (Y1-CLOSER S3 — the [T-A6b] gate is no longer on this trail).
- **Hypotheses**: none.
- **Uses from project**: `modelEllipticCurve` (imported).
- **Used by**: `fibreCurve_geom/_E_eq/_π_eq/_zero_eq/_hz`, `fibreCurveIso(_π/_zero)`, `pt_hord` (20 occurrences).
- **Visibility**: public
- **Lines**: 3038–3039
- **Notes**: —

### `theorem MarkedChartData.fibreCurve_geom`
- **Type**: `(D.fibreCurve k).toEllipticCurveGeom = D.fibreGeom k` (rfl)
- **What**: **Opaque interface** for the fibre record: its geometry is the fibre model.
- **Hypotheses**: none.
- **Uses from project**: `fibreCurve`, `fibreGeom`.
- **Used by**: `fibreCurve_E_eq`, `fibreCurve_π_eq`, `fibreCurve_zero_eq`.
- **Visibility**: public
- **Lines**: 3042–3043 (rfl)
- **Notes**: —

### `theorem MarkedChartData.fibreCurve_E_eq`
- **Type**: `(D.fibreCurve k).E = projModel (D.W.map …)`
- **What**: Total-space equation of the fibre record.
- **Hypotheses**: none.
- **Uses from project**: `fibreCurve_geom`.
- **Used by**: `fibreCurve_π_eq/_zero_eq/_hz`, `fibreCurveIso`, `pt_hord` (11 occurrences).
- **Visibility**: public
- **Lines**: 3045–3047 (term proof)
- **Notes**: —

### `theorem MarkedChartData.fibreCurve_π_eq`
- **Type**: `(D.fibreCurve k).π = eqToHom (fibreCurve_E_eq) ≫ projModelπ (D.W.map …)`
- **What**: π-equation of the fibre record.
- **Hypotheses**: none.
- **Uses from project**: `eqToGeom_π'`, `fibreCurve_geom`.
- **Used by**: `fibreCurveIso_π`, `pt_hord` (gfin, hval, hsk0).
- **Visibility**: public
- **Lines**: 3049–3051 (term proof)
- **Notes**: —

### `theorem MarkedChartData.fibreCurve_zero_eq`
- **Type**: `(D.fibreCurve k).zero = projModelZero (D.W.map …) ≫ eqToHom ….symm`
- **What**: Zero-section equation of the fibre record.
- **Hypotheses**: none.
- **Uses from project**: `eqToGeom_zero'`, `fibreCurve_geom`.
- **Used by**: `fibreCurve_hz`, `fibreCurveIso_zero`.
- **Visibility**: public
- **Lines**: 3053–3056 (term proof)
- **Notes**: —

### `theorem MarkedChartData.fibreCurve_hz`
- **Type**: `(D.fibreCurve k).zero ≫ eqToHom (fibreCurve_E_eq) = projModelZero (D.W.map …)`
- **What**: The zero pin of the fibre record (the hz hypothesis of `geomFibrePointAddEquiv`, B2 EVENT #3).
- **Hypotheses**: none.
- **Uses from project**: `fibreCurve_zero_eq`.
- **Used by**: `pt_hord` (hval, hsk0).
- **Visibility**: public
- **Lines**: 3060–3062 (proof 2 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.fibreCurveIso`
- **Type**: `(Y.curve.baseChange (D.geomPt (D.specPt k))).E ≅ (D.fibreCurve k).E`
- **What**: The pointed comparison from the curve fibre onto the fibre record's total space (fibreChartIso ≪≫ eqToIso).
- **Hypotheses**: none.
- **Uses from project**: `fibreChartIso`, `fibreCurve_E_eq`.
- **Used by**: `fibreCurveIso_π/_zero`, `pt_hord` (s₁, hgfin1, hfs0).
- **Visibility**: public
- **Lines**: 3065–3067
- **Notes**: —

### `theorem MarkedChartData.fibreCurveIso_π`
- **Type**: `(D.fibreCurveIso k).hom ≫ (D.fibreCurve k).π = (Y.curve.baseChange …).π`
- **What**: The comparison respects structure maps.
- **Hypotheses**: none.
- **Uses from project**: `fibreCurve_π_eq`, `pullbackChartIso_hom_π`, `fibreTop_isPullback`, `fibreCurveIso`.
- **Used by**: `pt_hord` (s₁, hfs0).
- **Visibility**: public
- **Lines**: 3069–3073 (proof 3 lines)
- **Notes**: —

### `theorem MarkedChartData.fibreCurveIso_zero`
- **Type**: `(Y.curve.baseChange …).zero ≫ (D.fibreCurveIso k).hom = (D.fibreCurve k).zero`
- **What**: The comparison respects zero sections.
- **Hypotheses**: none.
- **Uses from project**: `fibre_zero_comp`, `fibreCurve_zero_eq`, `fibreCurveIso`.
- **Used by**: `pt_hord` (hfs0, via sectionMapIsoHom).
- **Visibility**: public
- **Lines**: 3075–3079 (proof 3 lines)
- **Notes**: —

### `theorem MarkedChartData.pt_hord`
- **Type**: `(hP : Y.curve.NowhereGeomOrderLEThree P) → NowhereOrderLEThree D.W (zChartEval … coordX) (zChartEval … coordY)`
- **What**: **B2-ii fibre bridge ([T-A6b]+[T-B6′])**: a nowhere-small-order section satisfies the T-E1 order hypothesis in every marked chart — a dying small multiple of the chart coordinates at a geometric point would transport to a dying small multiple of the pulled section.
- **How**: Enters through `nowhereOrderLEThree_of_forall_geom`; at a geometric point k, builds the section chain s₁ = `sectionMapIso` of `fibreSection`, its point sk via `pointCongr`, its model point gfin via the imported `pointSpecPointsEquiv`; shows gfin is in the Z-chart (`inZChart_of_comp_baseChange`, using `fibreSection_comp_bc`) with evaluations the algebra images (`zChartEval_specPointBaseChange_*`, `zChartEval_congr`, `zChartEval_specPointComp`); identifies the transported point with the marked affine point via `geomFibrePointAddEquiv_apply` + `projModelPointsEquiv_some` + `chartSolution_*_eq_eval`; then transports `(a:ℤ)•(affine point) = 0` backwards through the additive chain (affinePointCongr, geomFibrePointAddEquiv, pointCongr, sectionMapIsoHom, baseChangeEquiv, pointCongr) to contradict hP.
- **Hypotheses**: hP.
- **Uses from project**: `nowhereOrderLEThree_of_forall_geom`, `zChartEval_equation_self`, `sectionMapIso(_injective)`, `sectionMapIsoHom`, `fibreCurve(_π_eq/_E_eq/_hz)`, `fibreCurveIso(_π/_zero)`, `fibreSection(_comp_bc)`, `EllipticCurve.pointCongr(_coe)`, `EllipticCurve.geomPoint`, `EllipticCurve.pointSpecPointsEquiv`, `EllipticCurve.geomFibrePointAddEquiv(_apply)`, `projModelPointsEquiv_some` (imported), `inZChart_of_comp_baseChange`, `zChartHom`, `Spec_map_zChartHom_awayι`, `specPointBaseChange`, `specPointComp`, `zChartEval_specPointBaseChange_coordX/Y`, `zChartEval_congr`, `zChartEval_specPointComp`, `chartSolution_zero/one_eq_eval`, `affinePointCongr(_some)`, `EllipticCurve.Point.baseChangeEquiv`, `EllipticCurve.Point.pull`, `pt`, `pt_inZChart`, `geomPt`, `specPt`.
- **Used by**: `baseMap`, `topMap`, and every downstream `…(D.pt_hord P hP)` slot (132 occurrences).
- **Visibility**: public
- **Lines**: 3085–3226 (proof ~137 lines)
- **Notes**: proof >30 lines (longest proof in file); `classical`

---

## Section `LocalClassifyingData` (lines 3232–3285)

### `noncomputable def MarkedChartData.baseMap`
- **Type**: `[Algebra R Γ(U)] (P) (hP) : D.U.1.toScheme ⟶ tateBase R`
- **What**: The local Tate-base map of a marked chart: isoSpec.hom ≫ tateBaseSpecMapOfPoint at the chart point.
- **Hypotheses**: Algebra R Γ(U); hP.
- **Uses from project**: `tateBaseSpecMapOfPoint`, `zChartEval_equation_self`, `pt(_inZChart/_hord)`.
- **Used by**: `topMap_isPullback/_zero/_marking`, `baseMap_over`, `coverBaseMap`, `gluedTopMap_π/_zero/_marking/_isPullback`, `chart_baseMap_eq`.
- **Visibility**: public
- **Lines**: 3248–3250
- **Notes**: —

### `noncomputable def MarkedChartData.topMap`
- **Type**: `pullback Y.curve.π D.U.1.ι ⟶ projModel (tateCurveLocOver R)`
- **What**: The local top map of a marked chart: e.hom ≫ projTateMap at the chart point.
- **Hypotheses**: Algebra R Γ(U); hP.
- **Uses from project**: `projTateMap`, `pt(_inZChart/_hord)`.
- **Used by**: `topMap_isPullback/_zero/_marking`, `fibreMap_topMap(_agree)`, `test_topMap_agree`, `coverTopMap`, glued clauses, `chart_topMap_eq` (22 occurrences).
- **Visibility**: public
- **Lines**: 3253–3254
- **Notes**: —

### `theorem MarkedChartData.topMap_isPullback`
- **Type**: `IsPullback (D.topMap P hP) (pullback.snd …) (projModelπ (tateCurveLocOver R)) (D.baseMap P hP)`
- **What**: The local square is cartesian (paste the trivialisation iso square with `projTateMap_isPullback`).
- **Hypotheses**: as constructors.
- **Uses from project**: `projTateMap_isPullback`, `MarkedChartData.heπ`, `topMap`, `baseMap`.
- **Used by**: `gluedTopMap_π` (h2), `gluedTopMap_isPullback` (htop).
- **Visibility**: public
- **Lines**: 3257–3261 (term proof)
- **Notes**: —

### `theorem MarkedChartData.topMap_zero`
- **Type**: `(zero lift) ≫ D.topMap P hP = D.baseMap P hP ≫ projModelZero (tateCurveLocOver R)`
- **What**: The local square is pointed.
- **Hypotheses**: as constructors.
- **Uses from project**: `MarkedChartData.hez`, `projTateMap_zero`, `topMap`, `baseMap`.
- **Used by**: `gluedTopMap_zero`.
- **Visibility**: public
- **Lines**: 3264–3272 (proof ~6 lines)
- **Notes**: —

### `theorem MarkedChartData.topMap_marking`
- **Type**: `D.restrictSection P ≫ D.topMap P hP = D.baseMap P hP ≫ tateP0mor R`
- **What**: The local square carries the section to the atlas marking.
- **Hypotheses**: as constructors.
- **Uses from project**: `pt_coe`, `projTateMap_marking`, `restrictSection`, `topMap`, `baseMap`, `tateP0mor`.
- **Used by**: `gluedTopMap_marking`.
- **Visibility**: public
- **Lines**: 3275–3281 (proof ~5 lines)
- **Notes**: —

---

## Section `TateAtlasNaturality` (lines 3287–3403)

### `theorem _root_.WeierstrassCurve.IsTateNormal.map`
- **Type**: `(hW : W.IsTateNormal) → (W.map ψ).IsTateNormal`
- **What**: Tate-normality is preserved by ring maps.
- **Hypotheses**: hW.
- **Uses from project**: `IsTateNormal` (imported).
- **Used by**: `tateNormalVariableChange_map` (via `.map`), `tateCurveLocOver_isTateNormal`, `projTateMap_map_tate` (htn), `tateBaseSpecMapOfPoint_inducedPt` (htn) — all by dot notation.
- **Visibility**: public (declared `_root_`)
- **Lines**: 3299–3303 (proof 3 lines)
- **Notes**: —

### `theorem NowhereOrderLEThree.map`
- **Type**: `NowhereOrderLEThree W x y → NowhereOrderLEThree (W.map ψ) (ψ x) (ψ y)`
- **What**: The nowhere-small-order condition is preserved by ring maps (the ψ₂·Ψ₃ value maps to the image, IsUnit.map).
- **Hypotheses**: hord.
- **Uses from project**: `NowhereOrderLEThree`; mathlib `WeierstrassCurve.map_Ψ`, `Polynomial.map_mapRingHom_evalEval`.
- **Used by**: `MarkedChartData.fibrePt_hord` (dot notation).
- **Visibility**: public
- **Lines**: 3306–3315 (proof ~7 lines)
- **Notes**: —

### `theorem tateNormalVariableChange_map`
- **Type**: `(tateNormalVariableChange W x y hxy hord).map ψ = tateNormalVariableChange (W.map ψ) (ψ x) (ψ y) hxy' hord'`
- **What**: T-E1 normalisation is natural in the chart ring.
- **Hypotheses**: both ellipticity instances, hxy/hord and their images.
- **Uses from project**: `tateNormalVariableChange(_unique/_isTateNormal)`, `IsTateNormal.map`; mathlib `WeierstrassCurve.map_variableChange`.
- **Used by**: `tateNormalVariableChange_smul_map`, `projModelBaseChange_projTateMap` (hC).
- **Visibility**: public
- **Lines**: 3318–3328 (proof ~4 lines)
- **Notes**: —

### `theorem tateNormalVariableChange_smul_map`
- **Type**: `tateNormalVariableChange (W.map ψ) … • (W.map ψ) = ((tateNormalVariableChange W …) • W).map ψ`
- **What**: The T-E1 normalised curve is natural in the chart ring.
- **Hypotheses**: as previous.
- **Uses from project**: `tateNormalVariableChange_map`.
- **Used by**: `tateRingOverLiftOfPoint_comp` (twice).
- **Visibility**: public
- **Lines**: 3331–3339 (proof 2 lines)
- **Notes**: —

### `theorem tateRingOverLiftOfPoint_comp`
- **Type**: `ψ.comp (tateRingOverLiftOfPoint R W x y hxy hord) = tateRingOverLiftOfPoint R (W.map ψ) (ψ x) (ψ y) hxy' hord'`
- **What**: The pointed atlas ring map is natural in the chart ring.
- **How**: `IsLocalization.ringHom_ext` + `MvPolynomial.ringHom_ext`; constants via `AlgHom.commutes` and hψ, coordinates via `tateRingOverAlgLiftOfPoint_X_zero/_X_one` and `tateNormalVariableChange_smul_map`.
- **Hypotheses**: hψ tower; both charts' hypotheses.
- **Uses from project**: `tateCurveOver`, `tateRingOverAlgLiftOfPoint(_X_zero/_X_one)`, `tateNormalVariableChange_smul_map`, `tateRingOverLiftOfPoint`.
- **Used by**: `tateBaseSpecMapOfPoint_naturality`, `projModelBaseChange_projTateMap` (hL).
- **Visibility**: public
- **Lines**: 3342–3374 (proof ~24 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfPoint_naturality`
- **Type**: `Spec.map (ofHom ψ) ≫ tateBaseSpecMapOfPoint R W … = tateBaseSpecMapOfPoint R (W.map ψ) …`
- **What**: **Affine naturality of the classifying base map** under change of chart ring.
- **Hypotheses**: hψ tower; chart hypotheses on both sides.
- **Uses from project**: `tateRingOverLiftOfPoint_comp`, `tateBaseSpecMapOfPoint`, `tateRingOverLiftOfPoint`.
- **Used by**: `specPt_tateBaseSpecMapOfPoint_agree` (twice).
- **Visibility**: public
- **Lines**: 3378–3390 (proof ~5 lines)
- **Notes**: —

### `theorem tateBaseSpecMapOfPoint_congr`
- **Type**: `x = x' → y = y' → tateBaseSpecMapOfPoint R W x y … = tateBaseSpecMapOfPoint R W x' y' …`
- **What**: Congruence of the pointed atlas map in the marked point.
- **Hypotheses**: hx, hy.
- **Uses from project**: `tateBaseSpecMapOfPoint`.
- **Used by**: `specPt_tateBaseSpecMapOfPoint_agree` (twice).
- **Visibility**: public
- **Lines**: 3393–3401 (subst; rfl)
- **Notes**: —

---

## Section `ChartAlgebra` (lines 3405–3447)

### `noncomputable def MarkedChartData.chartAlgebra`
- **Type**: `Algebra R Γ(U)`
- **What**: The chart ring as an R-algebra through the structure morphism (ΓSpecIso.inv ≫ structMap.appLE).
- **Hypotheses**: none.
- **Uses from project**: `MarkedChartData`, `EllObj.structMap`.
- **Used by**: `chartAlgebra_compatible`; installed via `letI` in `coverBaseMap`, `coverBaseMap_compat`, `gluedBaseMap_over`, `coverTopMap`, `coverTopMap_compat`, glued clauses, `components_unique` (17 occurrences).
- **Visibility**: public
- **Lines**: 3414–3416
- **Notes**: @[reducible]

### `theorem MarkedChartData.chartAlgebra_compatible`
- **Type**: with chartAlgebra installed: `D.U.2.isoSpec.hom ≫ Spec.map (ofHom (algebraMap R Γ(U))) = D.U.1.ι ≫ Y.structMap`
- **What**: The defining compatibility of chartAlgebra with the structure morphism.
- **How**: `IsAffineOpen.SpecMap_appLE_fromSpec` plus `fromSpec_top`/`isoSpec` bookkeeping.
- **Hypotheses**: none.
- **Uses from project**: `chartAlgebra`, `EllObj`.
- **Used by**: `coverBaseMap_compat`, `gluedBaseMap_over`, `coverTopMap_compat`, `components_unique` (as halg argument; 8 occurrences).
- **Visibility**: public
- **Lines**: 3419–3433 (proof ~11 lines)
- **Notes**: —

### `theorem MarkedChartData.baseMap_over`
- **Type**: `[Algebra R Γ(U)] (halg …) : D.baseMap P hP ≫ tateStructMap R = D.U.1.ι ≫ Y.structMap`
- **What**: With the structure algebra, the local classifying base map lies over Spec R relative to the chart inclusion.
- **Hypotheses**: halg.
- **Uses from project**: `baseMap`, `tateBaseSpecMapOfPoint_tateStructMap`, `tateStructMap`.
- **Used by**: `gluedBaseMap_over`.
- **Visibility**: public
- **Lines**: 3437–3443 (proof 2 lines)
- **Notes**: —

---

## Section `FibrePoint` (lines 3449–3558)

### `theorem algebraMap_comp_algebraMap_self`
- **Type**: `(algebraMap A k).comp (algebraMap A A) = algebraMap A k`
- **What**: Composing with the identity algebra map is the algebra map.
- **Hypotheses**: none.
- **Uses from project**: none (mathlib).
- **Used by**: `specPointBaseChange_fibrePt`, `specPointBaseChange_inducedPt` (as the hψ argument).
- **Visibility**: public
- **Lines**: 3459–3462 (proof 1 line)
- **Notes**: —

### `noncomputable def MarkedChartData.fibrePt`
- **Type**: `(P : Y.curve.Section) : SpecPoints (projModel (D.W.map (algebraMap Γ(U) k))) … k`
- **What**: The restricted section as a Spec-point of the fibre model over any chart-ring algebra k (not just fields) — the affine test-point interface.
- **Hypotheses**: none.
- **Uses from project**: `fibreSection`, `fibreChartIso`, `pullbackChartIso_hom_π`, `fibreTop_isPullback`, `SpecPoints`.
- **Used by**: `fibrePt_comp_bc/_inZChart`, `specPointBaseChange_fibrePt`, `zChartEval_fibrePt_coordX/Y`, `fibrePt_hord`, `fibrePt_fibreModelIso`, `tateBaseSpecMapOfPoint_fibrePt_agree`, `projModelBaseChange_projTateMap`, `fibreMap_topMap(_agree)` (86 occurrences).
- **Visibility**: public
- **Lines**: 3470–3483
- **Notes**: —

### `theorem MarkedChartData.fibrePt_comp_bc`
- **Type**: `(D.fibrePt k P).1 ≫ projModelBaseChange … D.W = D.specPt k ≫ (D.pt P).1`
- **What**: The fibre point maps to the chart point at the algebra point (value chase in SpecPoints form).
- **Hypotheses**: none.
- **Uses from project**: `fibreSection_comp_bc`, `fibrePt`, `projModelBaseChange`.
- **Used by**: `fibrePt_inZChart`, `specPointBaseChange_fibrePt`.
- **Visibility**: public
- **Lines**: 3487–3492 (proof 3 lines)
- **Notes**: —

### `theorem MarkedChartData.fibrePt_inZChart`
- **Type**: `InZChart D.W (D.pt P) → InZChart (D.W.map …) (D.fibrePt k P)`
- **What**: The fibre point lies in the Z-chart.
- **Hypotheses**: hZ.
- **Uses from project**: `inZChart_of_comp_baseChange`, `zChartHom`, `Spec_map_zChartHom_awayι`, `fibrePt_comp_bc`.
- **Used by**: `zChartEval_fibrePt_coordX/Y`, `fibrePt_hord`, `tateBaseSpecMapOfPoint_fibrePt_agree`, `specPt_tateBaseSpecMapOfPoint_agree`, `projModelBaseChange_projTateMap`, `fibreMap_topMap(_agree)` (81 occurrences).
- **Visibility**: public
- **Lines**: 3495–3505 (proof ~7 lines)
- **Notes**: —

### `theorem MarkedChartData.specPointBaseChange_fibrePt`
- **Type**: `specPointBaseChange D.W (D.fibrePt k P) = specPointComp D.W (D.pt P) (algebraMap Γ(U) k) …`
- **What**: The base-changed fibre point is the composed chart point.
- **Hypotheses**: none.
- **Uses from project**: `specPointBaseChange`, `specPointComp`, `fibrePt_comp_bc`, `algebraMap_comp_algebraMap_self`.
- **Used by**: `zChartEval_fibrePt_coordX`, `zChartEval_fibrePt_coordY`.
- **Visibility**: public
- **Lines**: 3508–3515 (proof 4 lines)
- **Notes**: —

### `theorem MarkedChartData.zChartEval_fibrePt_coordX`
- **Type**: `zChartEval (D.W.map …) (D.fibrePt k P) … coordX = algebraMap Γ(U) k (zChartEval D.W (D.pt P) hZ coordX)`
- **What**: The fibre point evaluates to the algebra image of the chart evaluation (x-side).
- **Hypotheses**: hZ.
- **Uses from project**: `zChartEval_specPointBaseChange_coordX`, `zChartEval_congr`, `specPointBaseChange_fibrePt`, `inZChart_specPointBaseChange`, `inZChart_specPointComp`, `zChartEval_specPointComp`.
- **Used by**: `fibrePt_hord`, `specPt_tateBaseSpecMapOfPoint_agree` (hx₁/hx₂), `projModelBaseChange_projTateMap` (hx).
- **Visibility**: public
- **Lines**: 3518–3528 (proof ~7 lines)
- **Notes**: —

### `theorem MarkedChartData.zChartEval_fibrePt_coordY`
- **Type**: y-analogue
- **What**: Fibre-point evaluation, y-side.
- **Hypotheses**: hZ.
- **Uses from project**: as x-side with `zChartEval_specPointBaseChange_coordY`.
- **Used by**: `fibrePt_hord`, `specPt_tateBaseSpecMapOfPoint_agree`, `projModelBaseChange_projTateMap`.
- **Visibility**: public
- **Lines**: 3531–3541 (proof ~7 lines)
- **Notes**: —

### `theorem MarkedChartData.fibrePt_hord`
- **Type**: `NowhereOrderLEThree (D.W.map …) (evals of fibrePt)` from hP
- **What**: The fibre point inherits the nowhere-small-order condition (rewrite evaluations to algebra images, apply `NowhereOrderLEThree.map`).
- **Hypotheses**: hP.
- **Uses from project**: `zChartEval_fibrePt_coordX/Y`, `pt_hord`, `NowhereOrderLEThree.map`, `pt_inZChart`.
- **Used by**: `tateBaseSpecMapOfPoint_fibrePt_agree`, `specPt_tateBaseSpecMapOfPoint_agree`, `projModelBaseChange_projTateMap`, `fibreMap_topMap(_agree)` (39 occurrences).
- **Visibility**: public
- **Lines**: 3544–3554 (proof 4 lines)
- **Notes**: —

---

## Section `OverlapAgreement` (lines 3560–3837)

### `noncomputable def MarkedChartData.fibreModelIso`
- **Type**: `(D₁ D₂ : MarkedChartData R Y) (k) (hgeom : D₁.geomPt (D₁.specPt k) = D₂.geomPt (D₂.specPt k)) : projModel (D₁.W.map …) ≅ projModel (D₂.W.map …)`
- **What**: The two fibre models over an agreeing test point are canonically isomorphic (fibreChartIso₁.symm ≪≫ pullback.congrHom ≪≫ fibreChartIso₂).
- **Hypotheses**: hgeom.
- **Uses from project**: `fibreChartIso`.
- **Used by**: `fibreModelIso_π/_zero`, `fibrePt_fibreModelIso`, `tateBaseSpecMapOfPoint_fibrePt_agree`, `fibreMap_topMap_agree` (12 occurrences).
- **Visibility**: public
- **Lines**: 3576–3579
- **Notes**: —

### `theorem MarkedChartData.fibreModelIso_π`
- **Type**: `(fibreModelIso …).hom ≫ projModelπ (D₂-side) = projModelπ (D₁-side)`
- **What**: The fibre-model comparison respects structure maps.
- **How**: three-step composition through `pullbackChartIso_hom_π` on both sides and `pullback.congrHom_hom` lift equations.
- **Hypotheses**: hgeom.
- **Uses from project**: `pullbackChartIso_hom_π`, `fibreTop_isPullback`, `fibreModelIso`, `fibreChartIso`.
- **Used by**: `tateBaseSpecMapOfPoint_fibrePt_agree`, `fibreMap_topMap_agree`.
- **Visibility**: public
- **Lines**: 3582–3603 (proof ~18 lines)
- **Notes**: —

### `theorem MarkedChartData.fibreModelIso_zero`
- **Type**: `projModelZero (D₁-side) ≫ (fibreModelIso …).hom = projModelZero (D₂-side)`
- **What**: The fibre-model comparison is pointed.
- **How**: `fibre_zero_comp` on both charts; the middle `pullback.congrHom` step carries the base-changed zero to the base-changed zero by a `pullback.hom_ext` calc (explicit lift-projection computations).
- **Hypotheses**: hgeom.
- **Uses from project**: `fibre_zero_comp`, `fibreChartIso`, `geomPt`, `specPt`, `fibreModelIso`.
- **Used by**: `tateBaseSpecMapOfPoint_fibrePt_agree`, `fibreMap_topMap_agree`.
- **Visibility**: public
- **Lines**: 3606–3674 (proof ~65 lines)
- **Notes**: proof >30 lines (long explicit calc)

### `theorem MarkedChartData.fibrePt_fibreModelIso`
- **Type**: `(D₁.fibrePt k P).1 ≫ (fibreModelIso …).hom = (D₂.fibrePt k P).1`
- **What**: The fibre-model comparison carries the first fibre point to the second.
- **How**: `fibreSection_coe` on both sides; a `pullback.hom_ext` calc shows `fibreSection₁ ≫ congrHom = fibreSection₂`; conclude by cancelling `fibreChartIso₁.hom ≫ inv`.
- **Hypotheses**: hgeom.
- **Uses from project**: `fibrePt`, `fibreSection(_coe)`, `fibreChartIso`, `fibreModelIso`, `geomPt`, `specPt`.
- **Used by**: `tateBaseSpecMapOfPoint_fibrePt_agree`, `fibreMap_topMap_agree`.
- **Visibility**: public
- **Lines**: 3677–3734 (proof ~54 lines)
- **Notes**: proof >30 lines (long explicit calc)

### `theorem MarkedChartData.tateBaseSpecMapOfPoint_fibrePt_agree`
- **Type**: `[Algebra R k]` (hgeom, P, hP): the two fibre points' pointed atlas maps agree
- **What**: **Overlap agreement of the pointed atlas maps** through the comparison ENGINE with fibreModelIso data.
- **Hypotheses**: hgeom, hP.
- **Uses from project**: `tateBaseSpecMapOfPoint_eq_of_pointedIso`, `fibreModelIso(_π/_zero)`, `fibrePt(_inZChart/_hord)`, `fibrePt_fibreModelIso`, `zChartEval_equation_self`, `pt_inZChart`.
- **Used by**: `specPt_tateBaseSpecMapOfPoint_agree`.
- **Visibility**: public
- **Lines**: 3736–3757 (term proof)
- **Notes**: —

### `theorem MarkedChartData.specPt_tateBaseSpecMapOfPoint_agree`
- **Type**: `[Algebra R k]` with towers htower₁, htower₂: `D₁.specPt k ≫ (D₁'s pointed atlas map) = D₂.specPt k ≫ (D₂'s pointed atlas map)`
- **What**: **The local classifying base maps agree on affine test points of the overlap.**
- **How**: A five-step calc: naturality (`tateBaseSpecMapOfPoint_naturality`) turns each side into the fibre-point atlas map (using `zChartEval_fibrePt_coordX/Y` and `tateBaseSpecMapOfPoint_congr` to fix the marked points), then `tateBaseSpecMapOfPoint_fibrePt_agree` bridges the middle.
- **Hypotheses**: hgeom, htower₁, htower₂, hP.
- **Uses from project**: `zChartEval_fibrePt_coordX/Y`, `zChartEval_equation_self`, `fibrePt(_inZChart/_hord)`, `tateBaseSpecMapOfPoint_naturality`, `tateBaseSpecMapOfPoint_congr`, `tateBaseSpecMapOfPoint_fibrePt_agree`, `pt(_inZChart/_hord)`.
- **Used by**: `test_baseMap_agree`.
- **Visibility**: public
- **Lines**: 3759–3833 (proof ~61 lines)
- **Notes**: proof >30 lines

---

## Section `ExistenceGlue` (lines 3839–4039)

### `theorem MarkedChartData.test_baseMap_agree`
- **Type**: for two charts with structure algebras (halg₁, halg₂), test maps c₁, c₂ into the chart rings with agreeing base composites (hcc): `c₁ ≫ (D₁'s pointed atlas map) = c₂ ≫ (D₂'s pointed atlas map)`
- **What**: **Test-point agreement of the local classifying base maps** in instance-free form: builds the algebras from `Spec.preimage` of the test maps and invokes the overlap agreement.
- **How**: `letI` installs algebras from `Spec.preimage c₁/c₂`; identifies `specPt = cᵢ` (`Spec.map_preimage`); the tower for D₂ is derived by `Spec.map_injective` from the geometric agreement hcc against the halg equations; concludes with `specPt_tateBaseSpecMapOfPoint_agree`.
- **Hypotheses**: halg₁, halg₂, hcc, hP.
- **Uses from project**: `specPt_tateBaseSpecMapOfPoint_agree`, `specPt`, `geomPt`, `tateBaseSpecMapOfPoint`, `zChartEval_equation_self`, `pt(_inZChart/_hord)`.
- **Used by**: `coverBaseMap_compat`.
- **Visibility**: public
- **Lines**: 3853–3923 (proof ~53 lines)
- **Notes**: proof >30 lines

### `noncomputable def MarkedChartData.chartAt`
- **Type**: `(Y) (s : Y.base) : MarkedChartData R Y`
- **What**: The chart at a point of the base (choice from `exists_mem`).
- **Hypotheses**: none.
- **Uses from project**: `exists_mem`.
- **Used by**: pervasive (280 occurrences): `chartAt_mem`, `chartCover(_f)`, `coverBaseMap(_compat)`, `gluedBaseMap(_over)`, `curveCover`, `coverTopMap(_compat)`, glued clauses, `components_unique`.
- **Visibility**: public
- **Lines**: 3927–3928
- **Notes**: —

### `theorem MarkedChartData.chartAt_mem`
- **Type**: `s ∈ (chartAt Y s).U.1`
- **What**: The chosen chart contains its point.
- **Hypotheses**: none.
- **Uses from project**: `exists_mem`, `chartAt`.
- **Used by**: `chartCover` (covers field).
- **Visibility**: public
- **Lines**: 3930–3931 (term proof)
- **Notes**: —

### `noncomputable def MarkedChartData.chartCover`
- **Type**: `(Y) : Y.base.OpenCover`
- **What**: The open cover of the base by marked charts (`Scheme.Cover.mkOfCovers` indexed by the points of the base).
- **Hypotheses**: none.
- **Uses from project**: `chartAt(_mem)`.
- **Used by**: `chartCover_f`, `coverBaseMap_compat`, `gluedBaseMap` (via `EllObj.tateBaseMapOfOpenCover`), `gluedTopMap_zero/_marking`, `gluedTopMap_isPullback`, `curveCover`, `components_unique` (56 occurrences).
- **Visibility**: public
- **Lines**: 3935–3939
- **Notes**: —

### `theorem MarkedChartData.chartCover_f`
- **Type**: `(chartCover Y).f s = (chartAt Y s).U.1.ι` (rfl)
- **What**: The cover maps are the chart inclusions.
- **Hypotheses**: none.
- **Uses from project**: `chartCover`, `chartAt`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 3941–3942 (rfl)
- **Notes**: @[simp]

### `noncomputable def MarkedChartData.coverBaseMap`
- **Type**: `(P) (hP) (s) : (chartCover Y).X s ⟶ tateBase R`
- **What**: The local classifying base maps of the chart cover (chartAlgebra installed, then `baseMap`).
- **Hypotheses**: hP.
- **Uses from project**: `chartAt`, `chartAlgebra`, `baseMap`.
- **Used by**: `coverBaseMap_compat`, `gluedBaseMap`, `ι_gluedBaseMap`, `gluedBaseMap_over`.
- **Visibility**: public
- **Lines**: 3945–3948
- **Notes**: —

### `theorem MarkedChartData.coverBaseMap_compat`
- **Type**: overlap compatibility `pullback.fst ≫ coverBaseMap i = pullback.snd ≫ coverBaseMap j`
- **What**: **Overlap compatibility** of the local classifying base maps.
- **How**: Checks over the affine cover of the pullback; cancel `isoSpec.inv` epi; the geometric agreement hcc is assembled from `pullback.condition` by a calc; concludes with `test_baseMap_agree` at Γ(V,⊤).
- **Hypotheses**: hP.
- **Uses from project**: `test_baseMap_agree`, `chartAt`, `chartAlgebra(_compatible)`, `chartCover`, `coverBaseMap`, `baseMap`, `tateBaseSpecMapOfPoint`, `zChartEval_equation_self`, `pt(_inZChart/_hord)`.
- **Used by**: `gluedBaseMap`, `ι_gluedBaseMap`, `gluedBaseMap_over`.
- **Visibility**: public
- **Lines**: 3951–4013 (proof ~59 lines)
- **Notes**: proof >30 lines

### `noncomputable def MarkedChartData.gluedBaseMap`
- **Type**: `(P) (hP) : Y.base ⟶ tateBase R`
- **What**: **The glued classifying base map**, via `EllObj.tateBaseMapOfOpenCover` on the chart cover.
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.tateBaseMapOfOpenCover`, `chartCover`, `coverBaseMap(_compat)`.
- **Used by**: `ι_gluedBaseMap`, `gluedBaseMap_over`, `gluedTopMap_π/_zero/_marking/_isPullback`, `gluedTopMapEll_*`, `gluedHom(_baseHom/_pullSection)`, `components_unique`, `tateMarkedPoint_classifies` (79 occurrences).
- **Visibility**: public
- **Lines**: 4016–4019
- **Notes**: —

### `theorem MarkedChartData.ι_gluedBaseMap`
- **Type**: `(chartAt Y s).U.1.ι ≫ gluedBaseMap P hP = coverBaseMap P hP s`
- **What**: Restriction of the glued base map to a chart.
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.ι_tateBaseMapOfOpenCover`, `gluedBaseMap`, `coverBaseMap`.
- **Used by**: `gluedTopMap_π/_zero/_marking`, `gluedTopMap_isPullback` (hW), `components_unique`.
- **Visibility**: public
- **Lines**: 4021–4026 (term proof)
- **Notes**: @[reassoc (attr := simp)]

### `theorem MarkedChartData.gluedBaseMap_over`
- **Type**: `gluedBaseMap P hP ≫ tateStructMap R = Y.structMap`
- **What**: The glued base map lies over Spec R.
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.tateBaseMapOfOpenCover_base_w`, `chartAlgebra(_compatible)`, `baseMap_over`, `chartAt`, `coverBaseMap(_compat)`.
- **Used by**: `gluedHom`, `gluedHom_pullSection`, `tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 4029–4035 (proof ~5 lines)
- **Notes**: —

---

## Section `BaseChangeComp` (lines 4041–4098)

### `private lemma projMapTransportHeq`
- **Type**: transport of `Proj.map g hg` along an equality of target curves given HEq of the graded homs
- **What**: HEq-transport lemma for Proj.map used to compare graded maps into models of equal curves.
- **Hypotheses**: e : V' = V, hgg : HEq g g'.
- **Uses from project**: `projModel`, `projIdeal`, `quotientGrading`, `GradedRingHom` (imported), `Proj.map` (project/mathlib Proj API).
- **Used by**: `projModelBaseChange_comp_eqToHom`.
- **Visibility**: private
- **Lines**: 4049–4060 (subst proof)
- **Notes**: —

### `private lemma gradedHomHeq`
- **Type**: pointwise HEq of graded homs into equal curves' gradings gives HEq of the homs
- **What**: HEq-extensionality for `GradedRingHom` under a curve equality.
- **Hypotheses**: e : V = V', h pointwise.
- **Uses from project**: `GradedRingHom`, `quotientGrading`, `projIdeal`.
- **Used by**: `projModelBaseChange_comp_eqToHom`.
- **Visibility**: private
- **Lines**: 4062–4069 (subst proof)
- **Notes**: —

### `private lemma mkHeq`
- **Type**: `HEq (Ideal.Quotient.mk (projIdeal V).toIdeal q) (Ideal.Quotient.mk (projIdeal V').toIdeal q)` for V = V'
- **What**: HEq of quotient classes across a curve equality.
- **Hypotheses**: e.
- **Uses from project**: `projIdeal`.
- **Used by**: `projModelBaseChange_comp_eqToHom`.
- **Visibility**: private
- **Lines**: 4071–4075 (subst; rfl)
- **Notes**: —

### `theorem projModelBaseChange_comp_eqToHom`
- **Type**: `projModelBaseChange ψ (W.map φ) ≫ projModelBaseChange φ W = eqToHom (congrArg projModel (map_map W φ ψ)) ≫ projModelBaseChange (ψ.comp φ) W`
- **What**: **Model base changes compose** along ring maps, up to the canonical identification of the doubly-mapped curve.
- **How**: `Proj.map_comp` then `projMapTransportHeq` with `gradedHomHeq`/`mkHeq` reducing to `MvPolynomial.map_map` on quotient generators of `baseChangeGradedHom`.
- **Hypotheses**: none.
- **Uses from project**: `projModelBaseChange`, `baseChangeGradedHom`, `quotientGradingMap_mk` (imported), `projMapTransportHeq`, `gradedHomHeq`, `mkHeq`.
- **Used by**: `projModelBaseChange_projTateMap` (hcomp).
- **Visibility**: public
- **Lines**: 4078–4096 (proof ~13 lines)
- **Notes**: —

---

## Section `TopNaturality` (lines 4100–4271)

### `theorem tateNormalVariableChange_congr`
- **Type**: congruence of `tateNormalVariableChange` in the marked point (x₁,y₁) = (x₂,y₂)
- **What**: Proof-irrelevant congruence for the normalising change.
- **Hypotheses**: hx, hy.
- **Uses from project**: `tateNormalVariableChange`.
- **Used by**: `projModelBaseChange_projTateMap` (hC).
- **Visibility**: public
- **Lines**: 4109–4117 (subst; rfl)
- **Notes**: —

### `theorem tateRingOverLiftOfPoint_congr`
- **Type**: congruence of `tateRingOverLiftOfPoint` in the marked point
- **What**: Proof-irrelevant congruence for the pointed atlas ring map.
- **Hypotheses**: hx, hy.
- **Uses from project**: `tateRingOverLiftOfPoint`.
- **Used by**: `projModelBaseChange_projTateMap` (hL).
- **Visibility**: public
- **Lines**: 4120–4129 (subst; rfl)
- **Notes**: —

### `private lemma projModelBaseChange_eqToHom`
- **Type**: `projModelBaseChange ψ V₂ ≫ eqToHom … = eqToHom … ≫ projModelBaseChange ψ V₁` for V₁ = V₂
- **What**: eqToHom slides across projModelBaseChange under a curve equality.
- **Hypotheses**: h.
- **Uses from project**: `projModelBaseChange`, `projModel`.
- **Used by**: `projModelBaseChange_projTateMap` (hslide).
- **Visibility**: private
- **Lines**: 4131–4137 (subst proof)
- **Notes**: —

### `private lemma projModelVCIso_inv_congr`
- **Type**: `(projModelVCIso C₁ W).inv = (projModelVCIso C₂ W).inv ≫ eqToHom …` for C₁ = C₂
- **What**: Congruence of the variable-change iso inverse in the change.
- **Hypotheses**: h.
- **Uses from project**: `projModelVCIso`, `projModel`.
- **Used by**: `projModelBaseChange_projTateMap` (hinvC), `projTateMap_map_tate` (hinv1).
- **Visibility**: private
- **Lines**: 4139–4144 (subst proof)
- **Notes**: —

### `private lemma projModelBaseChange_ringHom_congr`
- **Type**: `projModelBaseChange ρ₁ W = eqToHom … ≫ projModelBaseChange ρ₂ W` for ρ₁ = ρ₂
- **What**: Congruence of the base-change morphism in the ring map.
- **Hypotheses**: h.
- **Uses from project**: `projModelBaseChange`, `projModel`.
- **Used by**: `projModelBaseChange_projTateMap` (hbcL), `projTateMap_map_tate` (hbcL).
- **Visibility**: private
- **Lines**: 4146–4150 (subst proof)
- **Notes**: —

### `theorem projTateMap_unfold`
- **Type**: `projTateMap R W g hZ hord = (projModelVCIso …).inv ≫ eqToHom ….symm ≫ projModelBaseChange (atlas map) (tateCurveLocOver R)`
- **What**: The classifying top map, unfolded to its canonical three-factor composite.
- **Hypotheses**: chart data.
- **Uses from project**: `projTateMap`, `tateNormalIso`, `projModelVCIso`, `tateCurveLocOver_map_marked`, `tateRingOverAlgLiftOfPoint`, `zChartEval_equation_self`.
- **Used by**: `projModelBaseChange_projTateMap` (twice), `projTateMap_map_tate`.
- **Visibility**: public
- **Lines**: 4153–4165 (proof 1 line)
- **Notes**: —

### `theorem MarkedChartData.projModelBaseChange_projTateMap`
- **Type**: `projModelBaseChange (algebraMap Γ(U) k) D.W ≫ projTateMap R D.W (D.pt P) … = projTateMap R (D.W.map …) (D.fibrePt k P) …`
- **What**: **Naturality of the classifying top map**: base-changing the chart model and classifying at the fibre point agrees with classifying at the chart point and base-changing.
- **How**: (F2) `tateNormalVariableChange_congr` + `tateNormalVariableChange_map` align the two T-E1 normalisations; (F3) `tateRingOverLiftOfPoint_congr` + `tateRingOverLiftOfPoint_comp` align the atlas ring maps; (G1) `projModelVCIso_map` (imported T-W7.0h) moves the base change past the VC iso; both projTateMaps are unfolded (`projTateMap_unfold`), an epi `projModelVCIso.hom` is cancelled, and a long eqToHom-calculus calc (using `projModelBaseChange_eqToHom`, `projModelBaseChange_comp_eqToHom`, `projModelBaseChange_ringHom_congr`, `projModelVCIso_inv_congr`) closes the diagram.
- **Hypotheses**: htower, hP.
- **Uses from project**: `zChartEval_fibrePt_coordX/Y`, `zChartEval_equation_self`, `fibrePt(_inZChart/_hord)`, `tateNormalVariableChange_congr/_map`, `tateRingOverLiftOfPoint_congr/_comp`, `projModelVCIso_map` (imported), `projTateMap_unfold`, `projModelBaseChange_eqToHom`, `projModelBaseChange_comp_eqToHom`, `projModelBaseChange_ringHom_congr`, `projModelVCIso_inv_congr`, `tateCurveLocOver_map_marked`, `pt(_inZChart/_hord)`.
- **Used by**: `fibreMap_topMap`.
- **Visibility**: public
- **Lines**: 4175–4268 (proof ~86 lines)
- **Notes**: proof >30 lines; contains machine-length lines (up to ~3,780 chars, lines 4225–4264) — the eqToHom-calculus calc is written with fully elaborated terms

---

## Section `TopRestriction` (lines 4273–4523)

### `theorem MarkedChartData.fibreMap_topMap`
- **Type**: `D.fibreMap k ≫ D.topMap P hP = (D.fibreChartIso k).hom ≫ projTateMap R (D.W.map …) (D.fibrePt k P) …`
- **What**: **Fibre restriction of the local classifying top map**: over an affine test point the top map computes the classifying map of the fibre model at the fibre point.
- **How**: `pullbackChartIso_hom_bc` rewrites `fibreMap ≫ e.hom` as `fibreChartIso.hom ≫ projModelBaseChange`, then step-1 naturality `projModelBaseChange_projTateMap`.
- **Hypotheses**: htower, hP.
- **Uses from project**: `pullbackChartIso_hom_bc`, `fibreTop_isPullback`, `topMap`, `projModelBaseChange_projTateMap`, `fibreChartIso`, `fibrePt(_inZChart/_hord)`, `projTateMap`.
- **Used by**: `fibreMap_topMap_agree` (twice).
- **Visibility**: public
- **Lines**: 4295–4312 (proof ~10 lines)
- **Notes**: —

### `theorem MarkedChartData.fibreMap_topMap_agree`
- **Type**: `D₁.fibreMap k ≫ D₁.topMap P hP = (pullback.congrHom rfl hgeom).hom ≫ D₂.fibreMap k ≫ D₂.topMap P hP`
- **What**: **Overlap agreement of the fibre restrictions of the local classifying top maps**, through the comparison ENGINE with fibreModelIso data.
- **How**: `fibreMap_topMap` on both charts, then `projTateMap_eq_of_pointedIso` at `fibreModelIso` (with its π/zero/point clauses), and iso cancellation.
- **Hypotheses**: htower₁, htower₂, hgeom, hP.
- **Uses from project**: `fibreMap_topMap`, `projTateMap_eq_of_pointedIso`, `fibreModelIso(_π/_zero)`, `fibrePt(_inZChart/_hord)`, `fibrePt_fibreModelIso`, `pt_inZChart`.
- **Used by**: `test_topMap_agree`.
- **Visibility**: public
- **Lines**: 4324–4350 (proof ~18 lines)
- **Notes**: —

### `theorem MarkedChartData.test_topMap_agree`
- **Type**: instance-free test form: for T ⟶ Spec k with v₁, v₂ into the two chart pullbacks compatible over agreeing test points (hv₁, hv₂) and equal E-composites (hE): `v₁ ≫ D₁.topMap P hP = v₂ ≫ D₂.topMap P hP`
- **What**: **Test-point agreement of the local classifying top maps** — the input to the morphism-extension over the E-cover.
- **How**: Installs algebras from `Spec.preimage c₁/c₂` (as in test_baseMap_agree, deriving htower₂ by Spec-injectivity); factors v₁ through the fibre pullback via ρ = pullback.lift, checks ρ ≫ fibreMap = v₁ and (ρ ≫ congrHom) ≫ fibreMap₂ = v₂ by pullback.hom_ext calcs, then rewrites along `fibreMap_topMap_agree`.
- **Hypotheses**: halg₁, halg₂, hcc, hP, hv₁, hv₂, hE.
- **Uses from project**: `fibreMap_topMap_agree`, `fibreMap`, `specPt`, `geomPt`, `topMap`.
- **Used by**: `coverTopMap_compat`.
- **Visibility**: public
- **Lines**: 4357–4519 (proof ~145 lines)
- **Notes**: proof >30 lines (second-longest proof in file)

---

## Section `TopGlue` (lines 4525–4723)

### `noncomputable def MarkedChartData.curveCover`
- **Type**: `(Y) : Y.curve.E.OpenCover`
- **What**: The open cover of the curve total space by the chart pullbacks (`Scheme.Cover.copy` of `(chartCover Y).pullback₁ Y.curve.π` with transparent fields).
- **Hypotheses**: none.
- **Uses from project**: `chartCover`, `chartAt`.
- **Used by**: `gluedTopMap`, `ι_gluedTopMap`, `gluedTopMap_π`, `components_unique`.
- **Visibility**: public
- **Lines**: 4546–4550
- **Notes**: —

### `noncomputable def MarkedChartData.coverTopMap`
- **Type**: `(P) (hP) (s) : pullback Y.curve.π (chartAt Y s).U.1.ι ⟶ projModel (tateCurveLocOver R)`
- **What**: The local classifying top maps of the curve cover (chartAlgebra installed, then topMap).
- **Hypotheses**: hP.
- **Uses from project**: `chartAt`, `chartAlgebra`, `topMap`.
- **Used by**: `coverTopMap_compat`, `gluedTopMap`, `ι_gluedTopMap`, `gluedTopMap_π/_zero/_marking`, `gluedTopMap_isPullback` (13 occurrences).
- **Visibility**: public
- **Lines**: 4553–4557
- **Notes**: —

### `theorem MarkedChartData.coverTopMap_compat`
- **Type**: overlap compatibility of `coverTopMap` on `pullback (fst π U_i.ι) (fst π U_j.ι)`
- **What**: **Overlap compatibility** of the local classifying top maps.
- **How**: Builds the comparison g from the curve overlap to the base overlap (pullback.lift with a condition assembled from `pullback.condition`s); checks over the affine cover of the base overlap pulled back along g (`Scheme.Cover.hom_ext (𝒱.pullback₁ g)`); each check is `test_topMap_agree` with hv₁/hv₂/hE verified by long pullback-projection calcs.
- **Hypotheses**: hP.
- **Uses from project**: `test_topMap_agree`, `chartAt`, `chartAlgebra(_compatible)`, `coverTopMap`, `topMap`.
- **Used by**: `gluedTopMap`, `ι_gluedTopMap`.
- **Visibility**: public
- **Lines**: 4560–4704 (proof ~140 lines)
- **Notes**: proof >30 lines

### `noncomputable def MarkedChartData.gluedTopMap`
- **Type**: `(P) (hP) : Y.curve.E ⟶ projModel (tateCurveLocOver R)`
- **What**: **The glued classifying top map** over the curve cover.
- **Hypotheses**: hP.
- **Uses from project**: `curveCover`, `coverTopMap(_compat)`; mathlib `glueMorphisms`.
- **Used by**: `ι_gluedTopMap`, `gluedTopMap_π/_zero/_marking/_isPullback`, `gluedTopMapEll_*`, `gluedHom(_top/_pullSection)`, `components_unique`, `tateMarkedPoint_classifies` (33 occurrences).
- **Visibility**: public
- **Lines**: 4707–4711
- **Notes**: —

### `theorem MarkedChartData.ι_gluedTopMap`
- **Type**: `pullback.fst Y.curve.π (chartAt Y s).U.1.ι ≫ gluedTopMap P hP = coverTopMap P hP s`
- **What**: Restriction of the glued top map to a chart pullback.
- **Hypotheses**: hP.
- **Uses from project**: `curveCover`, `coverTopMap(_compat)`, `gluedTopMap`, `chartAt`.
- **Used by**: `gluedTopMap_π/_zero/_marking`, `gluedTopMap_isPullback`, `components_unique`.
- **Visibility**: public
- **Lines**: 4713–4719 (term proof)
- **Notes**: @[reassoc (attr := simp)]

---

## Section `GluedClauses` (lines 4725–5023)

### `theorem MarkedChartData.gluedTopMap_π`
- **Type**: `gluedTopMap P hP ≫ projModelπ (tateCurveLocOver R) = Y.curve.π ≫ gluedBaseMap P hP`
- **What**: The glued square commutes.
- **How**: `Scheme.Cover.hom_ext (curveCover Y)`; per chart, `ι_gluedTopMap` + `(topMap_isPullback).w` + `pullback.condition` + `ι_gluedBaseMap`.
- **Hypotheses**: hP.
- **Uses from project**: `ι_gluedTopMap`, `topMap_isPullback`, `ι_gluedBaseMap`, `curveCover`, `coverTopMap`, `chartAt`, `chartAlgebra`, `baseMap`.
- **Used by**: `gluedTopMap_isPullback` (χ), `gluedTopMapEll_isPullback` (implicitly via gluedTopMap_isPullback).
- **Visibility**: public
- **Lines**: 4739–4765 (proof ~23 lines)
- **Notes**: —

### `theorem MarkedChartData.gluedTopMap_zero`
- **Type**: `Y.curve.zero ≫ gluedTopMap P hP = gluedBaseMap P hP ≫ projModelZero (tateCurveLocOver R)`
- **What**: The glued square is pointed.
- **How**: `Scheme.Cover.hom_ext (chartCover Y)`; per chart, factor the zero through the pullback lift, `ι_gluedTopMap`, `topMap_zero`, `ι_gluedBaseMap` in a calc.
- **Hypotheses**: hP.
- **Uses from project**: `ι_gluedTopMap`, `topMap_zero`, `ι_gluedBaseMap`, `chartCover`, `chartAt`, `chartAlgebra`, `coverTopMap`, `baseMap`.
- **Used by**: `gluedTopMapEll_zero`.
- **Visibility**: public
- **Lines**: 4768–4803 (proof ~33 lines)
- **Notes**: proof >30 lines

### `theorem MarkedChartData.gluedTopMap_marking`
- **Type**: `P.1 ≫ gluedTopMap P hP = gluedBaseMap P hP ≫ tateP0mor R`
- **What**: The glued square carries the section to the atlas marking.
- **How**: `Scheme.Cover.hom_ext (chartCover Y)`; per chart, `restrictSection` projection + `ι_gluedTopMap` + `topMap_marking` + `ι_gluedBaseMap` in a calc.
- **Hypotheses**: hP.
- **Uses from project**: `restrictSection`, `ι_gluedTopMap`, `topMap_marking`, `ι_gluedBaseMap`, `chartCover`, `chartAt`, `chartAlgebra`, `tateP0mor`.
- **Used by**: `gluedHom_pullSection`, `tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 4806–4831 (proof ~23 lines)
- **Notes**: —

### `theorem MarkedChartData.gluedTopMap_isPullback`
- **Type**: `IsPullback (gluedTopMap P hP) Y.curve.π (projModelπ (tateCurveLocOver R)) (gluedBaseMap P hP)`
- **What**: **The glued square is cartesian**: the comparison χ into the pullback is an isomorphism chart-locally, and being an isomorphism is Zariski-local on the target.
- **How**: χ = pullback.lift(gluedTopMap, Y.curve.π); for each chart s, the piece comparison `pullback.snd χ (…)` is identified (hkey, by a two-level `pullback.hom_ext` with long calcs) with τ.hom ≫ σ.hom, where σ = `isoIsPullback` of `topMap_isPullback` against the pasted W-piece square hW, and τ = `isoIsPullback` of the pasted Q-side square — hence iso; `IsZariskiLocalAtTarget.of_openCover` (isomorphisms property) over `(chartCover Y).pullback₁` gives IsIso χ; `IsPullback.of_iso_pullback` concludes.
- **Hypotheses**: hP.
- **Uses from project**: `gluedTopMap(_π)`, `gluedBaseMap`, `ι_gluedBaseMap`, `ι_gluedTopMap`, `topMap_isPullback`, `chartAt`, `chartAlgebra`, `chartCover`, `coverTopMap`, `baseMap`, `topMap`.
- **Used by**: `gluedTopMapEll_isPullback`.
- **Visibility**: public
- **Lines**: 4836–5019 (proof ~180 lines)
- **Notes**: proof >30 lines (longest single proof block in file)

---

## Section `GluedHom` (lines 5025–5090)

### `theorem MarkedChartData.gluedTopMapEll_isPullback`
- **Type**: `IsPullback (gluedTopMap P hP ≫ eqToHom (tateUniversal_E_eq R).symm) Y.curve.π ((tateUniversal R).π) (gluedBaseMap P hP)`
- **What**: The glued cartesian square, transported across the tateUniversal bridge.
- **Hypotheses**: hP.
- **Uses from project**: `gluedTopMap_isPullback`, `tateUniversal_E_eq`, `tateUniversal_eqToHom_π` (imported), `tateUniversal`, `gluedBaseMap`.
- **Used by**: `gluedHom`, `gluedHom_pullSection`, `tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 5038–5047 (proof ~7 lines)
- **Notes**: —

### `theorem MarkedChartData.gluedTopMapEll_zero`
- **Type**: `Y.curve.zero ≫ (gluedTopMap P hP ≫ eqToHom …) = gluedBaseMap P hP ≫ (tateUniversal R).zero`
- **What**: The glued pointedness across the bridge.
- **Hypotheses**: hP.
- **Uses from project**: `eqToGeom_zero'`, `tateUniversal_geom` (imported), `gluedTopMap_zero`.
- **Used by**: `gluedHom`, `gluedHom_pullSection`, `tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 5050–5057 (proof ~4 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.gluedHom`
- **Type**: `(P) (hP) : Y ⟶ tateEllObj R`
- **What**: **The classifying Ell/R morphism** of a nowhere-small-order section, assembled by `EllObj.tateClassifyingHom` from the glued data.
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.tateClassifyingHom`, `gluedBaseMap(_over)`, `gluedTopMap`, `tateUniversal_E_eq`, `gluedTopMapEll_isPullback`, `gluedTopMapEll_zero`.
- **Used by**: `gluedHom_baseHom/_top/_pullSection`.
- **Visibility**: public
- **Lines**: 5060–5064
- **Notes**: —

### `theorem MarkedChartData.gluedHom_baseHom`
- **Type**: `(gluedHom P hP).baseHom = gluedBaseMap P hP` (rfl)
- **What**: Base component of the glued hom.
- **Hypotheses**: hP.
- **Uses from project**: `gluedHom`, `gluedBaseMap`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 5066–5068 (rfl)
- **Notes**: @[simp]

### `theorem MarkedChartData.gluedHom_top`
- **Type**: `(gluedHom P hP).top = gluedTopMap P hP ≫ eqToHom …` (rfl)
- **What**: Top component of the glued hom.
- **Hypotheses**: hP.
- **Uses from project**: `gluedHom`, `gluedTopMap`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 5070–5072 (rfl)
- **Notes**: @[simp]

### `theorem MarkedChartData.gluedHom_pullSection`
- **Type**: `EllHom.pullSection R (gluedHom P hP) (tateMarkedPoint R) = P`
- **What**: **The existence half of the classifying clause**: pulling the marked point back along the glued morphism recovers the section.
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.tateClassifyingHom_pullSection_eq`, `gluedBaseMap(_over)`, `gluedTopMap(_marking)`, `gluedTopMapEll_isPullback/_zero`, `tateMarkedPoint`, `tateP0mor`, `tateUniversal_E_eq`, `EllHom.pullSection`.
- **Used by**: unused in file (consumed by the downstream `exists_tatePoint` assembly).
- **Visibility**: public
- **Lines**: 5076–5086 (proof ~8 lines)
- **Notes**: —

---

## Section `SelfClassification` (lines 5092–5227)

### `private lemma projModelVCIso_hom_congrC`
- **Type**: `(projModelVCIso C₁ W).hom = eqToHom … ≫ (projModelVCIso C₂ W).hom` for C₁ = C₂
- **What**: Congruence of the VC iso hom in the change.
- **Hypotheses**: h.
- **Uses from project**: `projModelVCIso`, `projModel`.
- **Used by**: unused in file (dead private lemma).
- **Visibility**: private
- **Lines**: 5103–5109 (subst proof)
- **Notes**: dead code candidate

### `private lemma projModelVCIso_hom_congrW`
- **Type**: `(projModelVCIso C V).hom = eqToHom … ≫ (projModelVCIso C V').hom ≫ eqToHom …` for V = V'
- **What**: Congruence of the VC iso hom in the curve.
- **Hypotheses**: h.
- **Uses from project**: `projModelVCIso`, `projModel`.
- **Used by**: unused in file (dead private lemma).
- **Visibility**: private
- **Lines**: 5111–5118 (subst proof)
- **Notes**: dead code candidate. Comment block at 5120–5123 records that `projModelVCIso_one` was RELOCATED-BY-DEDUP (v10.118-Y1 merge) to `EllipticCurve/ModelVariableChange.lean`.

### `theorem tateCurveLocOver_a₁`
- **Type**: `(tateCurveLocOver R).a₁ = algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R) (X 0)`
- **What**: The atlas curve coefficient a₁ is the first universal coefficient.
- **Hypotheses**: none.
- **Uses from project**: `tateCurveLocOver`, `tateCurveOver`, `tateCurve`, `tateRingOver`.
- **Used by**: `projTateMap_map_tate`, `tateBaseSpecMapOfPoint_inducedPt`.
- **Visibility**: public
- **Lines**: 5126–5130 (proof 2 lines)
- **Notes**: —

### `theorem tateCurveLocOver_a₂`
- **Type**: a₂-analogue at X 1
- **What**: The atlas curve coefficient a₂ is the second universal coefficient.
- **Hypotheses**: none.
- **Uses from project**: as a₁.
- **Used by**: `projTateMap_map_tate`, `tateBaseSpecMapOfPoint_inducedPt`.
- **Visibility**: public
- **Lines**: 5133–5137 (proof 2 lines)
- **Notes**: —

### `theorem tateCurveOver_isTateNormal`
- **Type**: `(tateCurveOver R).IsTateNormal`
- **What**: The universal Tate-normal curve over R[A,B] is Tate-normal.
- **Hypotheses**: none.
- **Uses from project**: `tateCurveOver`, `tateCurve`, `IsTateNormal`.
- **Used by**: `tateCurveLocOver_isTateNormal`.
- **Visibility**: public
- **Lines**: 5140–5144 (proof 2 lines)
- **Notes**: —

### `theorem tateCurveLocOver_isTateNormal`
- **Type**: `(tateCurveLocOver R).IsTateNormal`
- **What**: The atlas curve is Tate-normal (image of the previous under the localization map).
- **Hypotheses**: none.
- **Uses from project**: `tateCurveOver_isTateNormal`, `IsTateNormal.map`, `tateCurveLocOver`.
- **Used by**: `projTateMap_map_tate` (htn), `tateBaseSpecMapOfPoint_inducedPt` (htn).
- **Visibility**: public
- **Lines**: 5147–5150 (term proof)
- **Notes**: —

### `theorem projTateMap_map_tate`
- **Type**: for a Z-chart point g of `(tateCurveLocOver R).map (algebraMap (tateRingOver R) A)` with both evaluations 0 (hx, hy) and htower: `projTateMap R ((tateCurveLocOver R).map …) g hZ hord = projModelBaseChange (algebraMap (tateRingOver R) A) (tateCurveLocOver R)`
- **What**: **Self-classification**: the classifying top map of the base-changed universal Tate curve at a (0,0)-marked point is the base-change morphism itself — the crux pinning the top component of an arbitrary classifying morphism.
- **How**: The T-E1 normalisation at (0,0) is the identity change (hC1, by `tateNormalVariableChange_unique` with `tateCurveLocOver_isTateNormal.map`); the pointed atlas map is then the algebra map itself (hL, by `tateRingOver_algHom_ext` at the universal coefficients via `tateCurveLocOver_a₁/a₂`); unfold `projTateMap_unfold`, replace the VC-inverse by an eqToHom (`projModelVCIso_inv_congr`, imported `projModelVCIso_one`), slide the ring-hom congruence (`projModelBaseChange_ringHom_congr`), and cancel eqToHoms.
- **Hypotheses**: `[Algebra (tateRingOver R) A]`, IsElliptic instance for the mapped curve, htower, hZ, hx, hy, hord.
- **Uses from project**: `tateCurveLocOver_isTateNormal`, `IsTateNormal.map`, `tateNormalVariableChange(_unique)`, `zChartEval_equation_self`, `tateRingOverAlgLiftOfPoint(_X_zero/_X_one)`, `tateRingOver_algHom_ext`, `tateCurveLocOver_a₁/a₂`, `projTateMap_unfold`, `projModelVCIso_inv_congr`, `projModelVCIso_one` (imported), `projModelBaseChange_ringHom_congr`.
- **Used by**: `projTateMap_inducedPt`.
- **Visibility**: public
- **Lines**: 5156–5225 (proof ~53 lines)
- **Notes**: proof >30 lines

---

## Section `InducedChart` (lines 5229–5507)

### `noncomputable def MarkedChartData.classifyingSpecMap`
- **Type**: `(fb : Y.base ⟶ tateBase R) : Spec (.of Γ(U)) ⟶ tateBase R`
- **What**: The affine test map of a chart under a classifying base map (isoSpec.inv ≫ U.ι ≫ fb).
- **Hypotheses**: none.
- **Uses from project**: `MarkedChartData`, `tateBase`.
- **Used by**: `classifying_isPullback(')`, `inducedChart`, `inducedPt` lemmas, `inducedChart_tower`, `tateBaseSpecMapOfPoint_inducedPt`, `chart_baseMap_eq/chart_topMap_eq` (40 occurrences).
- **Visibility**: public
- **Lines**: 5247–5249
- **Notes**: —

### `theorem MarkedChartData.classifying_isPullback`
- **Type**: `IsPullback (pullback.fst … ≫ ftop ≫ eqToHom (tateUniversal_E_eq R)) (pullback.snd … ≫ isoSpec.hom) (projModelπ (tateCurveLocOver R)) (D.classifyingSpecMap fb)` from hPB
- **What**: The restricted cartesian square of a classifying square over a chart.
- **How**: pastes: chart pullback square + hPB horizontally, the eqToHom bridge square (`tateUniversal_π_eq`), and a vertical iso square for isoSpec.
- **Hypotheses**: hPB.
- **Uses from project**: `tateUniversal(_E_eq/_π_eq)` (imported), `classifyingSpecMap`, `tateCurveLocOver`.
- **Used by**: `classifying_isPullback'`.
- **Visibility**: public
- **Lines**: 5255–5274 (proof ~15 lines)
- **Notes**: —

### `theorem MarkedChartData.classifying_isPullback'`
- **Type**: same square with the test map in algebra form `Spec.map (ofHom (algebraMap (tateRingOver R) Γ(U)))` under the `Spec.preimage`-induced algebra
- **What**: The restricted square with the classifying test map in algebra form (for `pullbackChartIso`).
- **Hypotheses**: hPB.
- **Uses from project**: `classifying_isPullback`, `classifyingSpecMap`, `tateRingOver`.
- **Used by**: `inducedChart` (e/heπ/hez fields), `inducedPt_comp_bc`, `chart_baseMap_eq`, `chart_topMap_eq` (14 occurrences).
- **Visibility**: public
- **Lines**: 5278–5293 (proof ~10 lines)
- **Notes**: —

### `noncomputable def MarkedChartData.inducedChart`
- **Type**: `(fb) (ftop) (hPB) (hzw) : MarkedChartData R Y`
- **What**: **The induced marked chart** of a classifying square over a chart of the base: same U, W := the universal Tate curve base-changed along the affine restriction of fb, trivialisation := `pullbackChartIso` of the restricted square.
- **How** (embedded proofs): heπ from `pullbackChartIso_hom_π`; hez from `pullbackChartIso_zero` — the zero-lift splitting is checked directly and the atlas-zero hit is a calc through hzw and `eqToGeom_zero' (tateUniversal_geom R)`.
- **Hypotheses**: hPB, hzw.
- **Uses from project**: `classifyingSpecMap`, `classifying_isPullback'`, `pullbackChartIso(_hom_π/_zero)`, `eqToGeom_zero'`, `tateUniversal(_geom/_E_eq)`, `tateCurveLocOver`, `tateRingOver`, `MarkedChartData`.
- **Used by**: `inducedChart_U`, `inducedPt`, `inducedPt_inZChart`, `inducedPt_hord`, `chart_baseMap_eq`, `chart_topMap_eq` (9 occurrences).
- **Visibility**: public
- **Lines**: 5298–5353 (def with ~44 lines of embedded proof)
- **Notes**: proof >30 lines (embedded)

### `theorem MarkedChartData.inducedChart_U`
- **Type**: `(D.inducedChart fb ftop hPB hzw).U = D.U` (rfl)
- **What**: The induced chart sits on the same affine open.
- **Hypotheses**: none.
- **Uses from project**: `inducedChart`.
- **Used by**: unused in file (leaf @[simp]).
- **Visibility**: public
- **Lines**: 5355–5356 (rfl)
- **Notes**: @[simp]

### `noncomputable def MarkedChartData.inducedPt`
- **Type**: `SpecPoints (projModel ((tateCurveLocOver R).map (algebraMap (tateRingOver R) Γ(U)))) … Γ(U)`
- **What**: The section P, read in the induced chart, with its honest model spelling (= `(D.inducedChart …).pt P`).
- **Hypotheses**: none.
- **Uses from project**: `inducedChart`, `pt`.
- **Used by**: `inducedPt_inZChart/_comp_bc/_coordX/_coordY/_hord`, `specPointBaseChange_inducedPt`, `tateBaseSpecMapOfPoint_inducedPt`, `projTateMap_inducedPt`, `chart_baseMap_eq/chart_topMap_eq` (19 occurrences).
- **Visibility**: public
- **Lines**: 5361–5370
- **Notes**: —

### `theorem MarkedChartData.inducedPt_inZChart`
- **Type**: `InZChart ((tateCurveLocOver R).map …) (D.inducedPt …)` from hP
- **What**: The induced point lies in the Z-chart (through the induced chart's `pt_inZChart`).
- **Hypotheses**: hP.
- **Uses from project**: `inducedChart`, `pt_inZChart`, `inducedPt`.
- **Used by**: `inducedPt_coordX/Y`, `inducedPt_hord` statements, `tateBaseSpecMapOfPoint_inducedPt`, `projTateMap_inducedPt`, `chart_baseMap_eq/chart_topMap_eq` (17 occurrences).
- **Visibility**: public
- **Lines**: 5373–5379 (term proof)
- **Notes**: —

### `theorem MarkedChartData.inducedPt_comp_bc`
- **Type**: `(hmark : P.1 ≫ ftop = fb ≫ (tateMarkedPoint R).1) → (D.inducedPt …).1 ≫ projModelBaseChange … = D.classifyingSpecMap fb ≫ tateP0mor R`
- **What**: **The induced point hits the atlas marking under base change** (the pulled-back marking equation in chart coordinates).
- **How**: `pullbackChartIso_hom_bc` + `restrictSection` projection + hmark in a calc, converting `(tateMarkedPoint R).1 = tateP0mor R ≫ eqToHom` at the end.
- **Hypotheses**: hmark.
- **Uses from project**: `pullbackChartIso_hom_bc`, `classifying_isPullback'`, `restrictSection`, `tateMarkedPoint`, `tateP0mor`, `tateUniversal_E_eq`, `classifyingSpecMap`, `inducedPt`, `projModelBaseChange`.
- **Used by**: `specPointBaseChange_inducedPt`.
- **Visibility**: public
- **Lines**: 5383–5434 (proof ~44 lines)
- **Notes**: proof >30 lines

### `theorem MarkedChartData.specPointBaseChange_inducedPt`
- **Type**: `specPointBaseChange (tateCurveLocOver R) (D.inducedPt …) = specPointComp (tateCurveLocOver R) (tateP0SpecPoint R) (algebraMap …) …`
- **What**: The base-changed induced point is the composed atlas marking.
- **Hypotheses**: hmark.
- **Uses from project**: `inducedPt_comp_bc`, `specPointBaseChange`, `specPointComp`, `tateP0SpecPoint`, `algebraMap_comp_algebraMap_self`, `classifyingSpecMap`.
- **Used by**: `inducedPt_coordX`, `inducedPt_coordY`.
- **Visibility**: public
- **Lines**: 5437–5457 (proof ~13 lines)
- **Notes**: —

### `theorem MarkedChartData.inducedPt_coordX`
- **Type**: `zChartEval … (D.inducedPt …) … coordX = 0`
- **What**: The induced point evaluates to 0 (x-side) — via base-change invariance and the marked point's vanishing.
- **Hypotheses**: hP, hmark.
- **Uses from project**: `zChartEval_specPointBaseChange_coordX`, `zChartEval_congr`, `specPointBaseChange_inducedPt`, `inZChart_specPointBaseChange`, `inZChart_specPointComp`, `tateP0SpecPoint(_inZChart)`, `zChartEval_specPointComp`, `zChartEval_tateP0SpecPoint_coordX`, `inducedPt(_inZChart)`.
- **Used by**: `tateBaseSpecMapOfPoint_inducedPt` (hC1), `projTateMap_inducedPt`.
- **Visibility**: public
- **Lines**: 5460–5480 (proof ~12 lines)
- **Notes**: —

### `theorem MarkedChartData.inducedPt_coordY`
- **Type**: y-analogue = 0
- **What**: The induced point evaluates to 0 (y-side).
- **Hypotheses**: hP, hmark.
- **Uses from project**: as x-side with the y-variants.
- **Used by**: `tateBaseSpecMapOfPoint_inducedPt`, `projTateMap_inducedPt`.
- **Visibility**: public
- **Lines**: 5483–5503 (proof ~12 lines)
- **Notes**: —

---

## Section `SameChartEngine` (lines 5509–5585)

### `theorem MarkedChartData.sameU_tateBaseSpecMapOfPoint_agree`
- **Type**: two marked-chart presentations (W₁,e₁), (W₂,e₂) of the curve over the same affine open U carrying the same restricted section v give equal pointed atlas maps
- **What**: **Same-chart agreement of the pointed atlas maps** — the base-half ENGINE in unbundled form, instantiable both by chart fields and induced data.
- **How**: The comparison iso e₁.symm ≪≫ e₂ is pointed (from heπ₁/heπ₂, hez₁/hez₂) and carries g₁ to g₂ (from hg₁/hg₂); `tateBaseSpecMapOfPoint_eq_of_pointedIso`.
- **Hypotheses**: heπ₁/₂, hez₁/₂, hg₁/₂, hZ₁/₂, hord₁/₂ (include heπ₁ heπ₂ hez₁ hez₂ hg₁ hg₂).
- **Uses from project**: `tateBaseSpecMapOfPoint_eq_of_pointedIso`, `zChartEval_equation_self`, `tateBaseSpecMapOfPoint`, `projModel(π)`, `projModelZero`.
- **Used by**: `chart_baseMap_eq`.
- **Visibility**: public
- **Lines**: 5546–5561 (proof ~13 lines)
- **Notes**: —

### `theorem MarkedChartData.sameU_projTateMap_agree`
- **Type**: same setting: `e₁.hom ≫ projTateMap R W₁ g₁ … = e₂.hom ≫ projTateMap R W₂ g₂ …`
- **What**: **Same-chart agreement of the classifying top maps** — the top-half ENGINE in unbundled form.
- **How**: same pointed-iso construction, then `projTateMap_eq_of_pointedIso` and iso cancellation.
- **Hypotheses**: as previous.
- **Uses from project**: `projTateMap_eq_of_pointedIso`, `projTateMap`, `zChartEval_equation_self`.
- **Used by**: `chart_topMap_eq`.
- **Visibility**: public
- **Lines**: 5565–5581 (proof ~14 lines)
- **Notes**: —

---

## Section `InducedChartPins` (lines 5587–5826)

### `theorem MarkedChartData.tateStructMap_eq_algebraMap`
- **Type**: `tateStructMap R = Spec.map (ofHom (algebraMap R (tateRingOver R)))`
- **What**: The atlas structure map is Spec of the atlas algebra (aligning the MvPolynomial-C spelling with the algebraMap tower).
- **Hypotheses**: none.
- **Uses from project**: `tateStructMap`, `tateRingOver`.
- **Used by**: `inducedChart_tower`.
- **Visibility**: public
- **Lines**: 5600–5608 (proof ~6 lines)
- **Notes**: declared inside `namespace MarkedChartData` though about the atlas only

### `theorem MarkedChartData.inducedPt_hord`
- **Type**: `NowhereOrderLEThree ((tateCurveLocOver R).map …) (evals of inducedPt)` from hP
- **What**: The nowhere-small-order condition of the induced point (through the induced chart's geometric-fibre machinery `pt_hord`).
- **Hypotheses**: hP.
- **Uses from project**: `inducedChart`, `pt_hord`, `inducedPt(_inZChart)`.
- **Used by**: `tateBaseSpecMapOfPoint_inducedPt`, `projTateMap_inducedPt`, `chart_baseMap_eq`, `chart_topMap_eq` (9 occurrences).
- **Visibility**: public
- **Lines**: 5612–5625 (term proof)
- **Notes**: —

### `theorem MarkedChartData.inducedChart_tower`
- **Type**: `(halg) (hbw : fb ≫ tateStructMap R = Y.structMap) → (algebraMap (tateRingOver R) Γ(U)).comp (algebraMap R (tateRingOver R)) = algebraMap R Γ(U)`
- **What**: The induced atlas algebra is an R-algebra tower (compatibility of the Spec.preimage-induced algebra with the structure algebras).
- **How**: Spec both sides; the composite is `classifyingSpecMap fb ≫ tateStructMap R`, computed by hbw and halg; `Spec.map_injective` descends to rings.
- **Hypotheses**: halg, hbw.
- **Uses from project**: `tateStructMap_eq_algebraMap`, `classifyingSpecMap`, `tateStructMap`.
- **Used by**: `tateBaseSpecMapOfPoint_inducedPt` (htower), `projTateMap_inducedPt`.
- **Visibility**: public
- **Lines**: 5630–5664 (proof ~27 lines)
- **Notes**: —

### `theorem MarkedChartData.tateBaseSpecMapOfPoint_inducedPt`
- **Type**: `tateBaseSpecMapOfPoint R ((tateCurveLocOver R).map …) (inducedPt evals) … = D.classifyingSpecMap fb`
- **What**: **The base pin**: the pointed atlas map of the induced point is the classifying test map.
- **How**: The T-E1 change at the (0,0)-induced point is 1 (hC1, via `inducedPt_coordX/Y` and `tateNormalVariableChange_unique` with `tateCurveLocOver_isTateNormal.map`); then `tateBaseSpecMap_eq_tateBaseSpecMapOfPoint` applied to the algebra-map AlgHom, whose coordinates are the universal coefficients (`tateCurveLocOver_a₁/a₂`); `Spec.map_preimage` finishes.
- **Hypotheses**: halg, hbw, hP, hmark.
- **Uses from project**: `inducedChart_tower`, `tateCurveLocOver_isTateNormal`, `IsTateNormal.map`, `tateNormalVariableChange(_unique)`, `inducedPt(_inZChart/_coordX/_coordY/_hord)`, `tateBaseSpecMap_eq_tateBaseSpecMapOfPoint`, `tateCurveLocOver_a₁/a₂`, `classifyingSpecMap`, `zChartEval_equation_self`.
- **Used by**: `chart_baseMap_eq`.
- **Visibility**: public
- **Lines**: 5668–5729 (proof ~47 lines)
- **Notes**: proof >30 lines

### `theorem MarkedChartData.projTateMap_inducedPt`
- **Type**: `projTateMap R ((tateCurveLocOver R).map …) (D.inducedPt …) … = projModelBaseChange (algebraMap (tateRingOver R) Γ(U)) (tateCurveLocOver R)`
- **What**: **The top pin**: the classifying top map of the induced point is the base-change morphism (self-classification applied).
- **Hypotheses**: halg, hbw, hP, hmark.
- **Uses from project**: `projTateMap_map_tate`, `inducedChart_tower`, `inducedPt(_inZChart/_coordX/_coordY/_hord)`.
- **Used by**: `chart_topMap_eq`.
- **Visibility**: public
- **Lines**: 5733–5754 (term proof)
- **Notes**: —

### `theorem MarkedChartData.chart_baseMap_eq`
- **Type**: `(halg) (hbw) (hP) (hmark) → D.baseMap P hP = D.U.1.ι ≫ fb`
- **What**: **The chart-level base pin**: on any marked chart, the local classifying base map agrees with the restriction of any classifying base map.
- **How**: `sameU_tateBaseSpecMapOfPoint_agree` compares the chart fields (D.W, D.e) with the induced chart's fields at the same restricted section (`pt_coe` on both), then `tateBaseSpecMapOfPoint_inducedPt` and `classifyingSpecMap` unfolding.
- **Hypotheses**: hPB, hzw (include), halg, hbw, hP, hmark.
- **Uses from project**: `sameU_tateBaseSpecMapOfPoint_agree`, `pullbackChartIso(_hom_π)`, `classifying_isPullback'`, `inducedChart`, `inducedPt(_inZChart/_hord)`, `restrictSection`, `pt_coe`, `pt(_inZChart/_hord)`, `tateBaseSpecMapOfPoint_inducedPt`, `classifyingSpecMap`, `baseMap`.
- **Used by**: `components_unique`.
- **Visibility**: public
- **Lines**: 5756–5788 (proof ~21 lines)
- **Notes**: —

### `theorem MarkedChartData.chart_topMap_eq`
- **Type**: `D.topMap P hP = pullback.fst Y.curve.π D.U.1.ι ≫ ftop ≫ eqToHom (tateUniversal_E_eq R)`
- **What**: **The chart-level top pin**: on any marked chart, the local classifying top map agrees with the restriction of any classifying top map.
- **How**: `sameU_projTateMap_agree` against the induced chart, then `projTateMap_inducedPt` and `pullbackChartIso_hom_bc`.
- **Hypotheses**: as previous.
- **Uses from project**: `sameU_projTateMap_agree`, `projTateMap_inducedPt`, `pullbackChartIso(_hom_bc/_hom_π)`, `classifying_isPullback'`, `inducedChart`, `inducedPt(_inZChart/_hord)`, `pt_coe`, `pt(_inZChart/_hord)`, `topMap`, `projTateMap`, `tateUniversal_E_eq`.
- **Used by**: `components_unique`.
- **Visibility**: public
- **Lines**: 5790–5822 (proof ~20 lines)
- **Notes**: —

---

## Section `ClassifyingClause` (lines 5828–5903)

### `theorem MarkedChartData.components_unique`
- **Type**: any (fb, ftop) with hPB, hzw, hbw, hmark satisfies `fb = gluedBaseMap P hP ∧ ftop = gluedTopMap P hP ≫ eqToHom …`
- **What**: **Uniqueness of the classifying components**: any cartesian pointed square over Spec R pulling the atlas marking back to the section has the glued base and top maps.
- **How**: base: `Scheme.Cover.hom_ext (chartCover Y)` with `chart_baseMap_eq` + `ι_gluedBaseMap` per chart; top: `Scheme.Cover.hom_ext (curveCover Y)` with `chart_topMap_eq` (post-composed with the eqToHom) + `ι_gluedTopMap`.
- **Hypotheses**: hPB, hzw, hbw, hmark, hP.
- **Uses from project**: `chartAt`, `chartAlgebra(_compatible)`, `chart_baseMap_eq`, `chart_topMap_eq`, `ι_gluedBaseMap`, `ι_gluedTopMap`, `chartCover`, `curveCover`, `gluedBaseMap`, `gluedTopMap`, `tateUniversal_E_eq`.
- **Used by**: `tateMarkedPoint_classifies`.
- **Visibility**: public
- **Lines**: 5842–5876 (proof ~28 lines)
- **Notes**: —

### `theorem MarkedChartData.tateMarkedPoint_classifies`
- **Type**: `(R : CommRingCat) (Y : EllObj R) (P : Y.curve.Section) (hP : Y.curve.NowhereGeomOrderLEThree P) : ∃! fc : Y ⟶ tateEllObj R, EllHom.pullSection R fc (tateMarkedPoint R) = P`
- **What**: **The Tate atlas classifying clause** (the ∀-part of `exists_tatePoint`, Loeffler Cor 3.3.5 / Prop 3.3.4): every nowhere-small-order section arises from a unique classifying Ell/R morphism by pulling back the atlas marking. This is the headline theorem of the file.
- **How**: `EllObj.tateClassifyingHom_existsUnique_of_components` at the glued data; the marking equation is `gluedTopMap_marking`; the uniqueness input is `components_unique` applied to the components of an arbitrary classifying f (its marking equation extracted from `f.isPullback.lift_fst`).
- **Hypotheses**: hP.
- **Uses from project**: `EllObj.tateClassifyingHom_existsUnique_of_components`, `gluedBaseMap(_over)`, `gluedTopMap(_marking)`, `gluedTopMapEll_isPullback/_zero`, `tateMarkedPoint`, `tateP0mor`, `tateUniversal_E_eq`, `components_unique`, `EllHom.pullSection`, `tateEllObj`.
- **Used by**: unused in file — this is the deliverable consumed downstream (YOneAssembly / `exists_tatePoint`).
- **Visibility**: public
- **Lines**: 5878–5899 (proof ~18 lines)
- **Notes**: —

---

### File Summary
- Total declarations: 298 (60 noncomputable defs + 1 abbrev (`specPt`) + 1 structure (`MarkedChartData`) + 1 instance (unnamed `IsElliptic` repackaging, line 3022) + 225 theorems + 10 lemmas (2 public, 8 private)
- Key API (used by 3+ others): `zChartEval` (337 refs), `MarkedChartData.pt`/`pt_inZChart` (358/421), `chartAt` (280), `zChartEval_equation_self` (201), `specPt` (182), `geomPt` (159), `MarkedChartData.pt_hord` (132), `tateNormalVariableChange` (+ `_isTateNormal/_r/_t/_unique`), `tateRingOverAlgLiftOfPoint` (87), `MarkedChartData.baseMap`/`topMap`, `fibrePt` (+ `_inZChart/_hord`), `gluedBaseMap`/`gluedTopMap` (+ ι-restrictions), `chartCover`/`curveCover`/`coverBaseMap`/`coverTopMap`, `zChartHom` (+ `Spec_map_zChartHom_awayι`, `zChartHom_unique`), `MarkedChartData` (structure) + `restrictSection`/`pt_coe`, `fibreSection` (+ `_coe/_comp_bc`), `fibreChartIso`/`fibreMap`/`fibreTop_isPullback`, `fibreCurve` family (`_E_eq/_π_eq/_zero_eq/_hz`, `fibreCurveIso(_π/_zero)`), `fibreModelIso` (+ `_π/_zero`, `fibrePt_fibreModelIso`), `projTateMap` (+ `_isPullback/_zero/_marking/_unfold/_eq_of_pointedIso`), `tateNormalIso` family, `markedPointNormalised` family, `tateCurveLocOver_map_marked`, `tateBaseSpecMapOfPoint` (+ `_naturality/_congr/_eq_of_pointedIso`), `tateBaseSpecMap` (+ `_ext/_tateStructMap`), `tateRingOverLift`/`tateRingOverAlgLift`/`…OfTateNormal`, `tateRingOver_algHom_ext`, `specPointComp`/`specPointBaseChange` (+ inZChart/eval transport lemmas), `specPoint_ext_of_zChartEval`, `pointedIsoAwayHom` (+ chart square), `zChartEval_pointedIso`, `tateNormalVariableChange_mul`, `zChartEval_coords_of_pointedIso`, `pullbackChartIso` (+ `_hom_bc/_hom_π/_zero`), `inZChart_of_comp_baseChange`, `sectionMapIso(+Hom)`, `EllipticCurve.pointCongr(_coe)`, `affinePointCongr(_some)`, `zChartEval_congr`, `chartSolution_*`, `chartAlgebra(_compatible)`, `tateP0SpecPoint(_inZChart)` + coord lemmas, `classifyingSpecMap`/`classifying_isPullback'`/`inducedChart`/`inducedPt` family, `tateCurveLocOver_a₁/a₂`, `tateCurveLocOver_isTateNormal`, `eqToHom_projModelπ/Zero`, `eqToIso_projModelπ/Zero`, `eqToGeom_π'/zero'`, `EllObj.tateClassifyingHom` (+ `_pullSection_eq/_existsUnique_of_components`), `EllObj.tateBaseMapOfOpenCover` (+ ι/base_w/ext), `EllObj.tateBaseMapOfGlobalCoeffs` family, `EllObj.structAlgebra`
- Unused declarations (unused in file — this is a leaf headline file, so "unused in file" may mean "consumed downstream"; @[simp]-tagged ones may also fire anonymously inside simp calls): `tateRingOverLift_X_zero`, `tateRingOverLift_X_one`, `tateRingOverAlgLift_X_zero`, `tateRingOverAlgLift_X_one`, `tateRingOver_algHom_eq_lift` (docstring mention only), `tateRingOver_algHom_eq_algLift`, `EllObj.tateClassifyingHom_baseHom`, `EllObj.tateClassifyingHom_top`, `EllObj.tateClassifyingHom_ext`, `EllObj.tateClassifyingHom_pullSection_top`, `EllObj.tateClassifyingHomOfGlobalCoeffs_baseHom`, `EllObj.tateClassifyingHomOfGlobalCoeffs_top`, `EllObj.tateClassifyingHomOfGlobalCoeffs_ext`, `EllObj.tateClassifyingHomOfOpenCover_baseHom`, `EllObj.tateClassifyingHomOfOpenCover_top`, `EllObj.tateClassifyingHomOfOpenCover_ext`, `EllObj.tateClassifyingHomOfPullbackMap_baseHom_of_base_id`, `EllObj.tatePullbackAlong_hom_ext`, `EllObj.tateClassifyingHomOfPullbackMap_toPullbackAlong`, `EllObj.toPullbackAlong_tateClassifyingHomOfPullbackMap`, `EllObj.tateClassifyingHomOfPullbackMap_pullSection`, `tateRingOverLiftOfTateNormal_X_zero`, `tateRingOverLiftOfTateNormal_X_one`, `tateRingOverAlgLiftOfTateNormal_X_zero`, `tateRingOverAlgLiftOfTateNormal_X_one`, `tateBaseSpecMapOfTateNormal_tateStructMap`, `tateRingOverAlgLiftOfTateNormal_eq_of_variableChanges`, `tateBaseSpecMapOfTateNormal_eq_of_variableChanges`, `tateCurveLocOver_map_tateRingOverLiftOfPoint` (docstring mention only), `atlasLocalPointedIso_exists_variableChange`, `atlasLocal_projModelVCIso_injective` (both pure re-exports of imported T-W7 results), `projTateMap_π`, `chartCover_f`, `inducedChart_U`, `gluedHom_baseHom`, `gluedHom_top`, `gluedHom_pullSection` (existence-half deliverable), `tateMarkedPoint_classifies` (THE headline deliverable), `projModelVCIso_hom_congrC` (private, dead), `projModelVCIso_hom_congrW` (private, dead — the only two genuinely dead declarations, left over after the v10.118 `projModelVCIso_one` dedup relocation noted at lines 5120–5123)
- Declarations with CODE sorry: NONE — verified: `grep -c sorry` returns 0 occurrences of the string anywhere in the file (not even in comments)
- Declarations with set_option: NONE (grep verified)
- Proofs >30 lines (25): `MarkedChartData.gluedTopMap_isPullback` (~180), `MarkedChartData.test_topMap_agree` (~145), `MarkedChartData.coverTopMap_compat` (~140), `MarkedChartData.pt_hord` (~137), `MarkedChartData.projModelBaseChange_projTateMap` (~86), `projTateMap_eq_of_pointedIso` (~84), `Spec_map_pointedIsoAwayHom_awayι` (~68), `MarkedChartData.fibreModelIso_zero` (~65), `MarkedChartData.specPt_tateBaseSpecMapOfPoint_agree` (~61), `nowhereOrderLEThree_of_forall_geom` (~59), `MarkedChartData.coverBaseMap_compat` (~59), `MarkedChartData.fibreSection_comp_bc` (~57), `inZChart_of_forall_ne_zero` (~56), `MarkedChartData.fibrePt_fibreModelIso` (~54), `MarkedChartData.test_baseMap_agree` (~53), `projTateMap_map_tate` (~53), `three_zsmul_some_eq_zero_of_Ψ₃_eq_zero` (~50), `sectionMapIso_add` (~48), `MarkedChartData.tateBaseSpecMapOfPoint_inducedPt` (~47), `MarkedChartData.inducedChart` (~44, embedded field proofs), `MarkedChartData.inducedPt_comp_bc` (~44), `zChartEval_equation` (~40), `markedPointNormalised_coords` (~39), `MarkedChartData.gluedTopMap_zero` (~33), `zChartEval_pointedIso` (~32)
- Private-vs-public counts: 8 private (all `lemma`s: `projMapTransportHeq`, `gradedHomHeq`, `mkHeq`, `projModelBaseChange_eqToHom`, `projModelVCIso_inv_congr`, `projModelBaseChange_ringHom_congr`, `projModelVCIso_hom_congrC`, `projModelVCIso_hom_congrW`) vs 290 public
- Other notes: lines 4225–4264 (inside `projModelBaseChange_projTateMap`) contain machine-length source lines up to ~3,780 characters — fully elaborated eqToHom-calculus terms; a candidate for readability refactoring. Comment at lines 5120–5123 records the v10.118-Y1 dedup: `projModelVCIso_one` now lives in `EllipticCurve/ModelVariableChange.lean` and is imported.
