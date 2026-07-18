import ModularCurves.EllipticCurve.PoleSheafBaseCechHOne
import ModularCurves.EllipticCurve.PoleSheafBaseCechFlat
import ModularCurves.ForMathlib.AcyclicAffineCechComparison
import ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Higher base-linear Cech exactness for pole sheaves

Prove exactness in every positive degree after extending the base-linear Cech
complex of a pole sheaf to a residue field.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct TopologicalSpace

universe u

namespace ModularCurves

private theorem affineFieldFactor_isScalarTower
    {S : Scheme.{u}} [IsAffine S]
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    let t : Spec (.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, (⊤ : S.Opens)) K)) ≫
        S.isoSpec.inv
    let x := Scheme.SpecToEquivOfField K S t
    let s := x.1
    let ψ := x.2
    let A := Γ(Spec (S.residueField s),
      (⊤ : (Spec (S.residueField s)).Opens))
    letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
      (S.fromSpecResidueField s).appTop.hom.toAlgebra
    let χ : A →+* K :=
      ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
    letI : Algebra A K := χ.toAlgebra
    IsScalarTower Γ(S, (⊤ : S.Opens)) A K := by
  dsimp only
  let R := Γ(S, (⊤ : S.Opens))
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ S.isoSpec.inv
  let x := Scheme.SpecToEquivOfField K S t
  let s := x.1
  let ψ := x.2
  let A := Γ(Spec (S.residueField s),
    (⊤ : (Spec (S.residueField s)).Opens))
  letI : Algebra R A :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  let χ : A →+* K :=
    ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  letI : Algebra A K := χ.toAlgebra
  have hfac : Spec.map ψ ≫ S.fromSpecResidueField s = t := by
    simpa only [x, s, ψ, Scheme.SpecToEquivOfField_symm_apply] using
      (Scheme.SpecToEquivOfField K S).symm_apply_apply t
  have hcomp₀ :
      (S.fromSpecResidueField s).appTop ≫
          (Spec.map ψ).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom =
        CommRingCat.ofHom (algebraMap R K) := by
    rw [← Category.assoc]
    rw [← Scheme.Hom.comp_appTop (Spec.map ψ)
      (S.fromSpecResidueField s), hfac]
    dsimp only [t]
    rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    have hΓ : (Scheme.ΓSpecIso (.of R)).hom =
        S.isoSpec.hom.appTop := by
      dsimp only [R]
      exact (Scheme.toSpecΓ_appTop S).symm
    rw [hΓ]
    rw [← Category.assoc]
    rw [← Scheme.Hom.comp_appTop S.isoSpec.hom S.isoSpec.inv,
      S.isoSpec.hom_inv_id]
    simp only [Scheme.Hom.id_app, Category.id_comp]
  have hcomp : CommRingCat.ofHom (algebraMap R K) =
      (S.fromSpecResidueField s).appTop ≫
        (Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ := by
    rw [← Scheme.ΓSpecIso_naturality ψ]
    exact hcomp₀.symm
  apply IsScalarTower.of_algebraMap_eq'
  change (CommRingCat.ofHom (algebraMap R K)).hom =
    ((S.fromSpecResidueField s).appTop ≫
      (Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  exact congrArg CommRingCat.Hom.hom hcomp

private theorem baseChange_exact_of_forall_schemeResidueField_baseChange_exact
    {S : Scheme.{u}} [IsAffine S]
    {P Q T : Type u} [AddCommGroup P] [AddCommGroup Q] [AddCommGroup T]
    [Module Γ(S, (⊤ : S.Opens)) P] [Module Γ(S, (⊤ : S.Opens)) Q]
    [Module Γ(S, (⊤ : S.Opens)) T]
    (f : P →ₗ[Γ(S, (⊤ : S.Opens))] Q)
    (g : Q →ₗ[Γ(S, (⊤ : S.Opens))] T)
    (hres : ∀ s : S,
      let A := Γ(Spec (S.residueField s),
        (⊤ : (Spec (S.residueField s)).Opens))
      letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
        (S.fromSpecResidueField s).appTop.hom.toAlgebra
      Function.Exact (f.baseChange A) (g.baseChange A))
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K] :
    Function.Exact (f.baseChange K) (g.baseChange K) := by
  let t : Spec (.of K) ⟶ S :=
    Spec.map (CommRingCat.ofHom
      (algebraMap Γ(S, (⊤ : S.Opens)) K)) ≫ S.isoSpec.inv
  let x := Scheme.SpecToEquivOfField K S t
  let s := x.1
  let ψ := x.2
  let A := Γ(Spec (S.residueField s),
    (⊤ : (Spec (S.residueField s)).Opens))
  letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  let χ : A →+* K :=
    ((Scheme.ΓSpecIso (S.residueField s)).hom ≫ ψ).hom
  letI : Algebra A K := χ.toAlgebra
  letI : IsScalarTower Γ(S, (⊤ : S.Opens)) A K :=
    affineFieldFactor_isScalarTower K
  have hAfield : IsField A :=
    (Scheme.ΓSpecIso (S.residueField s)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (S.residueField s))
  letI : Module.Flat A K := by
    letI : Field A := hAfield.toField
    letI : Module.Free A K := Module.Free.of_divisionRing A K
    exact Module.Flat.of_free
  have hiter : Function.Exact
      ((f.baseChange A).baseChange K)
      ((g.baseChange A).baseChange K) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_exact K (hres s)
  let eP := AlgebraTensorModule.cancelBaseChange
    Γ(S, (⊤ : S.Opens)) A K K P
  let eQ := AlgebraTensorModule.cancelBaseChange
    Γ(S, (⊤ : S.Opens)) A K K Q
  let eT := AlgebraTensorModule.cancelBaseChange
    Γ(S, (⊤ : S.Opens)) A K K T
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := eP) (e₂ := eQ) (e₃ := eT)
    (f₁₂ := (f.baseChange A).baseChange K)
    (f₂₃ := (g.baseChange A).baseChange K)
    (g₁₂ := f.baseChange K) (g₂₃ := g.baseChange K)
    (by
      ext
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
        curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        LinearMap.baseChange_tmul, eP, eQ])
    (by
      ext
      simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp,
        curry_apply, LinearMap.coe_restrictScalars, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply,
        AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        LinearMap.baseChange_tmul, eQ, eT])).mpr hiter

/-- After extension to a residue field, the base-linear Cech complex of
`O(n[0])` is exact in every positive degree for `n ≥ 1` on a fibrewise
elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_exactAt_succ
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.baseCechComplex π
        (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) := by
  let t := S.fromSpecResidueField s
  let M := sectionPoleSheafPower π z hz n
  let Uf : ι → (π.fiber s).Opens :=
    fun i ↦ pullback.fst π t ⁻¹ᵁ U i
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) := by
    change IsSeparated (pullback.snd π t)
    infer_instance
  letI : (π.fiber s).IsSeparated := ⟨by
    rw [← terminal.comp_from (π.fiberToSpecResidueField s)]
    infer_instance⟩
  letI : (pullback π t).IsSeparated := ⟨by
    rw [← terminal.comp_from (pullback.snd π t)]
    infer_instance⟩
  let MF : (π.fiber s).Modules :=
    @sectionPoleSheafPower _ _ (π.fiberToSpecResidueField s) hsepFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  have hUf : IsOpenCover Uf :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst π t) hU
  have hUfaff : ∀ i, IsAffineOpen (Uf i) := by
    intro i
    exact IsAffineOpen.preimage_pullback_fst π t (hUaff i)
  have hsmFiber : SmoothOfRelativeDimension 1 (π.fiberToSpecResidueField s) := by
    change SmoothOfRelativeDimension 1 (pullback.snd π t)
    exact
      (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
        (IsPullback.of_hasPullback π t) hsm
  letI : MF.IsQuasicoherent := by
    dsimp only [MF]
    exact sectionPoleSheafPower_isQuasicoherent hsmFiber
      (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n
  let eM :
      (Scheme.Modules.pullback (pullback.fst π t)).obj M ≅ MF := by
    dsimp only [t, M, MF]
    exact sectionPoleSheafPowerFiberIso hsm z hz s n
  letI : ((Scheme.Modules.pullback (pullback.fst π t)).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (π.fiber s).ringCatSheaf).prop_of_iso
      eM.symm inferInstance
  letI hFiberH : Subsingleton (CategoryTheory.Sheaf.H MF.sheaf (q + 1)) := by
    cases q with
    | zero =>
        dsimp only [MF]
        simpa using h.sectionPoleSheafPower_fiber_subsingleton_H_one z hz s hn
    | succ q =>
        dsimp only [MF]
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
          h.sectionPoleSheafPower_fiber_subsingleton_H_add_two z hz s n q
  have hPullbackH : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf (q + 1)) := by
    let eH :=
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) (q + 1)).mapIso
          ((Scheme.Modules.toSheaf (π.fiber s)).mapIso eM)
    change Subsingleton ↑((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (π.fiber s)) (q + 1)).obj
        ((Scheme.Modules.toSheaf (π.fiber s)).obj
          ((Scheme.Modules.pullback (pullback.fst π t)).obj M)))
    letI : Subsingleton ↑((CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology (π.fiber s)) (q + 1)).obj
      ((Scheme.Modules.toSheaf (π.fiber s)).obj MF)) := by
      change Subsingleton (CategoryTheory.Sheaf.H MF.sheaf (q + 1))
      exact hFiberH
    exact eH.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
  have hNativeExact :
      ((cechComplexFunctor Uf).obj
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M).sheaf.obj).ExactAt
          (q + 1) := by
    exact Scheme.Modules.cechComplex_exactAt_succ_of_affine_openCover
      (U := Uf) ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
        hUf hUfaff q hPullbackH
  have hFiberExact :
      (Scheme.Modules.baseCechComplex (pullback.snd π t)
        ((Scheme.Modules.pullback (pullback.fst π t)).obj M) Uf).ExactAt
          (q + 1) := by
    exact (Scheme.Modules.baseCechComplex_exactAt_iff
      (pullback.snd π t)
      ((Scheme.Modules.pullback (pullback.fst π t)).obj M)
      Uf (q + 1)).mpr hNativeExact
  exact hFiberExact.of_iso
    (Scheme.Modules.baseCechComplexBaseChangeIso
      π t M U hUaff).symm

/-- After extension to a residue field, the bounded ordered Cech complex of
`O(n[0])` is exact in every positive degree for `n ≥ 1` on a fibrewise
elliptic family. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_exactAt_succ
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    (((ModuleCat.extendScalars
        (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex
          (.up ℕ)).obj
      (Scheme.Modules.orderedBaseCechComplex π
        (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) := by
  let F := (ModuleCat.extendScalars
    (S.fromSpecResidueField s).appTop.hom).mapHomologicalComplex (.up ℕ)
  have hbase :=
    FibrewiseElliptic.sectionPoleSheafPower_residueField_baseCech_exactAt_succ
      hsm z hz h U hU hUaff s hn q
  change (F.obj (Scheme.Modules.orderedBaseCechComplex π
    (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1)
  change (F.obj (Scheme.Modules.baseCechComplex π
    (sectionPoleSheafPower π z hz n) U)).ExactAt (q + 1) at hbase
  exact hbase.of_retract
    (F.map (Scheme.Modules.orderedToBaseCechAlternating π
      (sectionPoleSheafPower π z hz n) U))
    (F.map (Scheme.Modules.baseCechToOrdered π
      (sectionPoleSheafPower π z hz n) U))
    (by
      rw [← F.map_comp,
        Scheme.Modules.orderedToBaseCechAlternating_comp_baseCechToOrdered,
        F.map_id])

/-- The consecutive differentials of the bounded ordered Cech complex of
`O(n[0])` are exact after algebraic base change to the global sections of a
residue-field spectrum. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_residueField_orderedBaseCech_differential_exact
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S) {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    let A := Γ(Spec (S.residueField s),
      (⊤ : (Spec (S.residueField s)).Opens))
    letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
      (S.fromSpecResidueField s).appTop.hom.toAlgebra
    let C := Scheme.Modules.orderedBaseCechComplex π
      (sectionPoleSheafPower π z hz n) U
    Function.Exact
      ((C.d q (q + 1)).hom.baseChange A)
      ((C.d (q + 1) (q + 2)).hom.baseChange A) := by
  dsimp only
  let A := Γ(Spec (S.residueField s),
    (⊤ : (Spec (S.residueField s)).Opens))
  letI : Algebra Γ(S, (⊤ : S.Opens)) A :=
    (S.fromSpecResidueField s).appTop.hom.toAlgebra
  exact cochainComplex_baseChange_functionExact_of_map_exactAt A
    (Scheme.Modules.orderedBaseCechComplex π
      (sectionPoleSheafPower π z hz n) U) q
    (h.sectionPoleSheafPower_residueField_orderedBaseCech_exactAt_succ
      hsm z hz U hU hUaff s hn q)

/-- The consecutive positive-degree differentials of the bounded ordered Cech complex of
`O(n[0])` are exact after base change to every field over the affine base. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_field_orderedBaseCech_differential_exact
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → E.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (K : Type u) [Field K] [Algebra Γ(S, (⊤ : S.Opens)) K]
    {n : ℕ} (hn : 1 ≤ n) (q : ℕ) :
    let C := Scheme.Modules.orderedBaseCechComplex π
      (sectionPoleSheafPower π z hz n) U
    Function.Exact
      ((C.d q (q + 1)).hom.baseChange K)
      ((C.d (q + 1) (q + 2)).hom.baseChange K) := by
  dsimp only
  apply baseChange_exact_of_forall_schemeResidueField_baseChange_exact
    (S := S) _ _ _ K
  intro s
  exact h.sectionPoleSheafPower_residueField_orderedBaseCech_differential_exact
    hsm z hz U hU hUaff s hn q

/-- For `n ≥ 1`, a fibrewise elliptic family has a finite ordered affine Cech
model for `O(n[0])` which is termwise flat, bounded, and exact in positive
degrees after every field base change. -/
theorem FibrewiseElliptic.exists_sectionPoleSheafPower_orderedBaseCech_flat_bounded_field_exact
    {E S : Scheme.{u}} {π : E ⟶ S} [IsProper π] [IsAffine S]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : LinearOrder ι)
      (U : ι → E.Opens),
      IsOpenCover U ∧ (∀ i, IsAffineOpen (U i)) ∧
        (∀ i, Nonempty
          ((sectionPoleSheafPower π z hz n).restrict (U i).ι ≅
            Scheme.Modules.unitObj (U i).toScheme)) ∧
          let C := Scheme.Modules.orderedBaseCechComplex π
            (sectionPoleSheafPower π z hz n) U
          (∀ q, Module.Flat Γ(S, (⊤ : S.Opens)) (C.X q)) ∧
            (∀ q, Fintype.card ι ≤ q → Subsingleton (C.X q)) ∧
              ∀ (K : Type u) [Field K]
                [Algebra Γ(S, (⊤ : S.Opens)) K] (q : ℕ),
                Function.Exact
                  ((C.d q (q + 1)).hom.baseChange K)
                  ((C.d (q + 1) (q + 2)).hom.baseChange K) := by
  obtain ⟨ι, hι, hιord, U, hU, hUaff, htriv, hflat⟩ :=
    exists_sectionPoleSheafPower_finiteAffineOrderedBaseCech_flat
      hsm z hz n
  letI : Fintype ι := hι
  letI : LinearOrder ι := hιord
  refine ⟨ι, inferInstance, inferInstance, U, hU, hUaff, htriv, ?_⟩
  dsimp only
  refine ⟨hflat, ?_, ?_⟩
  · intro q hq
    exact Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le
      π (sectionPoleSheafPower π z hz n) U q hq
  · intro K _ _ q
    exact h.sectionPoleSheafPower_field_orderedBaseCech_differential_exact
      hsm z hz U hU hUaff K hn q

end ModularCurves
