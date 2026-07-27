import ModularCurves.EllipticCurve.PoleSheafPowerOneBaseChange
import ModularCurves.EllipticCurve.PoleSheafPushforwardBaseChange
import ModularCurves.ForMathlib.PrescribedLocalizedBasis
import ModularCurves.ForMathlib.SchemeModulePushforwardBaseChangeLinearEquiv

/-!
# Pole-section modules from pushforward base change

An isomorphic top component of the canonical pole-sheaf pushforward
base-change morphism gives the expected equivalence on base-linear global
sections. In degree one this equivalence preserves the canonical pole
section.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TensorProduct

universe u

namespace ModularCurves

/-- If the top component of canonical pushforward base change for
`O(n[0])` is an isomorphism, then its global sections commute with the
given affine base change. -/
noncomputable def
    sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
    {C S T : Scheme.{u}} [IsAffine S] [IsAffine T] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) (n : ℕ)
    [((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz n)).IsQuasicoherent]
    [IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      hsm z hz t n).val.app (.op (⊤ : T.Opens)))] :
    let M := sectionPoleSheafPower π z hz n
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    A ⊗[B] Scheme.Modules.baseSections π M ≃ₗ[A]
      Scheme.Modules.baseSections πT MT :=
  Scheme.Modules.baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso
    π t (sectionPoleSheafPower π z hz n)
      (sectionPoleSheafPower (pullback.snd π t)
        (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t) n)
      (sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n)

/-- The first-pole base-change equivalence sends the scalar extension of
the canonical first-pole section to the literal canonical first-pole
section on the base-changed family. -/
theorem
    sectionPoleSheafPowerOne_baseSectionsBaseChangeLinearEquivOfAppTopIso_one_tmul
    {C S T : Scheme.{u}} [IsAffine S] [IsAffine T] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S)
    [((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz 1)).IsQuasicoherent]
    [IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      hsm z hz t 1).val.app (.op (⊤ : T.Opens)))] :
    let M := sectionPoleSheafPower π z hz 1
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
        (π := π) hsm z hz t 1
        ((1 : A) ⊗ₜ[B]
          (sectionPoleSheafPowerOneSection π z hz :
            Scheme.Modules.baseSections π M)) =
      sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  unfold sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
  let M := sectionPoleSheafPower π z hz 1
  let N := (Scheme.Modules.pushforward π).obj M
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let φ := sectionPoleSheafPowerPushforwardBaseChange
    (π := π) hsm z hz t 1
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.baseSectionsPushforwardTopIso πT MT).hom).1
  rw [Scheme.Modules.baseSectionsPushforwardTopIso_hom_apply]
  have hBaseChangeRaw :=
    Scheme.Modules.baseSectionsPushforwardBaseChangeLinearEquivOfAppTopIso_one_tmul
      (X := C) (S := S) (T := T)
      (f := π) (t := t) (M := M) (MT := MT)
      (φ := φ)
      (s := sectionPoleSheafPowerOneSection π z hz)
  rw [hBaseChangeRaw]
  have hPushforward :
      φ.app (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t N
            (Scheme.Modules.pushforwardTopSection π M
              (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          ((sectionPoleSheafPowerBaseChangeIso
              (π := π) hsm z hz t 1).hom.app
            (⊤ : (pullback π t).Opens)
              (Scheme.Modules.affinePullbackUnitTop
                (pullback.fst π t) M
                  (sectionPoleSheafPowerOneSection π z hz))) :=
    sectionPoleSheafPowerPushforwardBaseChange_app_top_pullbackUnit
      (π := π) hsm z hz t 1 (sectionPoleSheafPowerOneSection π z hz)
  have hLiteral :
      (sectionPoleSheafPowerBaseChangeIso
          (π := π) hsm z hz t 1).hom.app
        (⊤ : (pullback π t).Opens)
          (Scheme.Modules.affinePullbackUnitTop
            (pullback.fst π t) M
              (sectionPoleSheafPowerOneSection π z hz)) =
        sectionPoleSheafPowerOneSection πT zT hzT :=
    sectionPoleSheafPowerOneSection_baseChange
      (π := π) hsm z hz t
  have hLiteralPushforward :
      Scheme.Modules.pushforwardTopSection πT MT
          ((sectionPoleSheafPowerBaseChangeIso
              (π := π) hsm z hz t 1).hom.app
            (⊤ : (pullback π t).Opens)
              (Scheme.Modules.affinePullbackUnitTop
                (pullback.fst π t) M
                  (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          (sectionPoleSheafPowerOneSection πT zT hzT) :=
    congrArg (Scheme.Modules.pushforwardTopSection πT MT) hLiteral
  have hAfterBaseChange :
      φ.app (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t N
            (Scheme.Modules.pushforwardTopSection π M
              (sectionPoleSheafPowerOneSection π z hz))) =
        Scheme.Modules.pushforwardTopSection πT MT
          (sectionPoleSheafPowerOneSection πT zT hzT) :=
    hPushforward.trans hLiteralPushforward
  exact hAfterBaseChange

end ModularCurves

namespace AlgebraicGeometry

/-- The global-sections map of the canonical morphism from `Spec A` to an
affine scheme is the composite of the given algebra map with the inverse
`Γ-Spec` equivalence. -/
theorem Scheme.specMap_algebraMap_isoSpec_inv_appTop
    {S : Scheme.{u}} [IsAffine S]
    (A : Type u) [CommRing A] [Algebra Γ(S, (⊤ : S.Opens)) A] :
    let B := Γ(S, (⊤ : S.Opens))
    let T := Spec (.of A)
    let t : T ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
    t.appTop.hom =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp (algebraMap B A) := by
  dsimp only
  let B := Γ(S, (⊤ : S.Opens))
  let T := Spec (.of A)
  let t : T ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
  have hcomp :
      t.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom =
        CommRingCat.ofHom (algebraMap B A) := by
    dsimp only [t]
    rw [Scheme.Hom.comp_appTop, Category.assoc,
      Scheme.ΓSpecIso_naturality]
    have hΓ :
        (Scheme.ΓSpecIso (.of B)).hom = S.isoSpec.hom.appTop :=
      (Scheme.toSpecΓ_appTop S).symm
    rw [hΓ, ← Category.assoc,
      ← Scheme.Hom.comp_appTop S.isoSpec.hom S.isoSpec.inv,
      S.isoSpec.hom_inv_id]
    simp
  have ht :
      t.appTop = CommRingCat.ofHom (algebraMap B A) ≫
        (Scheme.ΓSpecIso (.of A)).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso (.of A)).hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hcomp
  exact congrArg CommRingCat.Hom.hom ht

end AlgebraicGeometry

namespace ModularCurves

/-- A prescribed localized first-pole basis transports across any affine base
change whose global-sections map factors through the localization. -/
theorem
    exists_sectionPoleSheafPowerOne_baseChange_basis_of_localized_basis
    {C S T : Scheme.{u}} [IsAffine S] [IsAffine T] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (a : Γ(S, (⊤ : S.Opens))) (t : T ⟶ S)
    (g : Localization.Away a →+* Γ(T, (⊤ : T.Opens)))
    (hfactor : t.appTop.hom =
      g.comp (algebraMap Γ(S, (⊤ : S.Opens)) (Localization.Away a)))
    (bA : Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a
        (Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz 1))))
    (hbA : bA 0 = LocalizedModule.mkLinearMap (.powers a)
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1))
      (sectionPoleSheafPowerOneSection π z hz))
    (hQC : ((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz 1)).IsQuasicoherent)
    (hBC : IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      (π := π) hsm z hz t 1).val.app (.op (⊤ : T.Opens)))) :
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT 1
    ∃ b : Module.Basis (Fin 1) Γ(T, (⊤ : T.Opens))
        (Scheme.Modules.baseSections πT MT),
      b 0 = sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  let M := sectionPoleSheafPower π z hz 1
  let B := Γ(S, (⊤ : S.Opens))
  let A := Localization.Away a
  let K := Γ(T, (⊤ : T.Opens))
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  letI := hQC
  letI := hBC
  letI : Algebra B K := t.appTop.hom.toAlgebra
  letI : Algebra A K := g.toAlgebra
  letI : IsScalarTower B A K :=
    IsScalarTower.of_algebraMap_eq' hfactor
  have htargetRaw :=
    sectionPoleSheafPowerOne_baseSectionsBaseChangeLinearEquivOfAppTopIso_one_tmul
      (C := C) (S := S) (T := T) (π := π) hsm z hz t
  exact Module.exists_basis_singleton_of_localized_baseChange
    a (sectionPoleSheafPowerOneSection π z hz :
      Scheme.Modules.baseSections π M)
    bA hbA
    (sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
      (π := π) hsm z hz t 1)
    (sectionPoleSheafPowerOneSection πT zT hzT)
    htargetRaw

/-- A prescribed localized first-pole basis becomes a basis of the actual
first-pole module on the canonical principal affine base change, with its
vector identified with the literal canonical first-pole section. -/
theorem
    exists_sectionPoleSheafPowerOne_away_baseChange_basis_of_localized_basis
    {C S : Scheme.{u}} [IsAffine S] {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (a : Γ(S, (⊤ : S.Opens)))
    (bA : Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a
        (Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz 1))))
    (hbA : bA 0 = LocalizedModule.mkLinearMap (.powers a)
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1))
      (sectionPoleSheafPowerOneSection π z hz))
    (hQC : ((Scheme.Modules.pushforward π).obj
      (sectionPoleSheafPower π z hz 1)).IsQuasicoherent) :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Localization.Away a
    let T := Spec (.of A)
    let t : T ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT 1
    IsIso ((sectionPoleSheafPowerPushforwardBaseChange
      hsm z hz t 1).val.app (.op (⊤ : T.Opens))) →
      ∃ b : Module.Basis (Fin 1) Γ(T, (⊤ : T.Opens))
          (Scheme.Modules.baseSections πT MT),
        b 0 = sectionPoleSheafPowerOneSection πT zT hzT := by
  dsimp only
  intro hBC
  let B := Γ(S, (⊤ : S.Opens))
  let A := Localization.Away a
  let T := Spec (.of A)
  let t : T ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ S.isoSpec.inv
  have hfactor := Scheme.specMap_algebraMap_isoSpec_inv_appTop
    (S := S) A
  let M := sectionPoleSheafPower π z hz 1
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT 1
  let K := Γ(T, (⊤ : T.Opens))
  letI := hQC
  letI := hBC
  letI : Algebra B K := t.appTop.hom.toAlgebra
  letI : Algebra A K :=
    (Scheme.ΓSpecIso (.of A)).inv.hom.toAlgebra
  letI : IsScalarTower B A K :=
    IsScalarTower.of_algebraMap_eq' hfactor
  have htargetRaw :=
    sectionPoleSheafPowerOne_baseSectionsBaseChangeLinearEquivOfAppTopIso_one_tmul
      (C := C) (S := S) (T := T) (π := π) hsm z hz t
  exact Module.exists_basis_singleton_of_localized_baseChange
    a (sectionPoleSheafPowerOneSection π z hz :
      Scheme.Modules.baseSections π M)
    bA hbA
    (sectionPoleSheafPower_baseSectionsBaseChangeLinearEquivOfAppTopIso
      (π := π) hsm z hz t 1)
    (sectionPoleSheafPowerOneSection πT zT hzT)
    htargetRaw

end ModularCurves
