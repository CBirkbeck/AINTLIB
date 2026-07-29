import ModularCurves.EllipticCurve.PoleSheafPointedIso
import ModularCurves.EllipticCurve.PoleSheafModel
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Global pole sections on residue fibres

This file transports the explicit basis of pole sections on a projective Weierstrass
model across the pointed isomorphism supplied by `FibrewiseElliptic`. It proves the
dimension of `Γ(O(n[0]))` on every residue fibre for `n >= 1`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory SheafOfModules
  TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def pushforwardIsoOfPullbackIso
    {X Y S : Scheme.{u}} {πX : X ⟶ S} {πY : Y ⟶ S}
    (e : X ≅ Y) (heπ : e.hom ≫ πY = πX) (M : Y.Modules) (N : X.Modules)
    (p : (pullback e.hom).obj M ≅ N) :
    (pushforward πY).obj M ≅ (pushforward πX).obj N := by
  letI : (pullback e.hom).IsEquivalence := pullback_isEquivalence_of_iso e
  letI : (pushforward e.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction e.hom).isEquivalence_right_of_isEquivalence_left
  let adj := pullbackPushforwardAdjunction e.hom
  letI : IsIso adj.unit := by infer_instance
  letI : IsIso adj.counit := by infer_instance
  let ηIso := adj.toEquivalence.unitIso.app M
  exact (pushforward πY).mapIso ηIso ≪≫
    (pushforwardComp e.hom πY).app ((pullback e.hom).obj M) ≪≫
    (pushforwardCongr heπ).app ((pullback e.hom).obj M) ≪≫
    (pushforward πX).mapIso p

/-- The canonical action of the base ring on global functions, induced by the
structure morphism to its spectrum. -/
noncomputable def baseScalarHom {R : Type u} [CommRing R]
    {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) :
    R →+* Γ(X, (⊤ : X.Opens)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appTop).hom

private noncomputable def topSectionsEquivOfPullbackIso
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {πX : X ⟶ Spec (CommRingCat.of R)} {πY : Y ⟶ Spec (CommRingCat.of R)}
    (e : X ≅ Y) (heπ : e.hom ≫ πY = πX) (M : Y.Modules) (N : X.Modules)
    (p : (pullback e.hom).obj M ≅ N) :
    letI : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ (baseScalarHom πY)
    letI : Module R Γ(N, (⊤ : X.Opens)) := Module.compHom _ (baseScalarHom πX)
    Γ(M, (⊤ : Y.Opens)) ≃ₗ[R] Γ(N, (⊤ : X.Opens)) := by
  letI : Module R Γ(M, (⊤ : Y.Opens)) := Module.compHom _ (baseScalarHom πY)
  letI : Module R Γ(N, (⊤ : X.Opens)) := Module.compHom _ (baseScalarHom πX)
  let q := pushforwardIsoOfPullbackIso e heπ M N p
  let U : (Spec (CommRingCat.of R)).Opens := ⊤
  let qHom := q.hom.val.app (.op U)
  let qInv := q.inv.val.app (.op U)
  refine
    { toFun := qHom
      invFun := qInv
      left_inv := fun x => iso_hom_inv_app_applyT q (.op U) x
      right_inv := fun x => iso_inv_hom_app_applyT q (.op U) x
      map_add' := fun x y => qHom.hom.map_add x y
      map_smul' := fun r x => qHom.hom.map_smul
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom r) x }

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

private theorem isSeparated_fiberToSpecResidueField
    {E S : Scheme.{u}} (π : E ⟶ S) [IsSeparated π] (s : S) :
    IsSeparated (π.fiberToSpecResidueField s) := by
  change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
  exact AlgebraicGeometry.IsSeparated.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π (S.fromSpecResidueField s))
    (show IsSeparated π from inferInstance)

/-- A pointed isomorphism over `Spec R` induces an `R`-linear equivalence on global
sections of every tensor power of the pole sheaf. -/
noncomputable def sectionPoleSheafPowerPointedSectionsEquiv
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {π : C ⟶ Spec (CommRingCat.of R)} {π' : C' ⟶ Spec (CommRingCat.of R)}
    [IsSeparated π] [IsSeparated π']
    (z : Spec (CommRingCat.of R) ⟶ C) (hz : z ≫ π = 𝟙 _)
    (z' : Spec (CommRingCat.of R) ⟶ C') (hz' : z' ≫ π' = 𝟙 _)
    (hsm' : SmoothOfRelativeDimension 1 π')
    (e : C ≅ C') (heπ : e.hom ≫ π' = π) (hez : z ≫ e.hom = z') (n : ℕ) :
    letI : Module R Γ(sectionPoleSheafPower π' z' hz' n, (⊤ : C'.Opens)) :=
      Module.compHom _ (Scheme.Modules.baseScalarHom π')
    letI : Module R Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) :=
      Module.compHom _ (Scheme.Modules.baseScalarHom π)
    Γ(sectionPoleSheafPower π' z' hz' n, (⊤ : C'.Opens)) ≃ₗ[R]
      Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens)) := by
  exact Scheme.Modules.topSectionsEquivOfPullbackIso e heπ _ _
    (sectionPoleSheafPowerPointedIso z hz z' hz' hsm' e hez n)

/-- For `n >= 1`, global sections of `O(n[0])` on every residue fibre of a
fibrewise elliptic family have dimension `n` over the residue field. -/
theorem FibrewiseElliptic.sectionPoleSheafPower_fiber_finrank
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (h : FibrewiseElliptic π z hz)
    (s : S) {n : ℕ} (hn : 1 ≤ n) :
    letI : IsSeparated (π.fiberToSpecResidueField s) :=
      isSeparated_fiberToSpecResidueField π s
    letI : Module ↑(S.residueField s)
        Γ(sectionPoleSheafPower (π.fiberToSpecResidueField s)
          (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n,
          (⊤ : (π.fiber s).Opens)) :=
      Module.compHom _
        (Scheme.Modules.baseScalarHom (π.fiberToSpecResidueField s))
    Module.finrank ↑(S.residueField s)
      Γ(sectionPoleSheafPower (π.fiberToSpecResidueField s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n,
        (⊤ : (π.fiber s).Opens)) = n := by
  letI hsepFiber : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  letI : Module ↑(S.residueField s)
      Γ(sectionPoleSheafPower (π.fiberToSpecResidueField s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) n,
        (⊤ : (π.fiber s).Opens)) :=
    Module.compHom _
      (Scheme.Modules.baseScalarHom (π.fiberToSpecResidueField s))
  obtain ⟨W, hW, e, heπ, hez⟩ := h s
  letI : W.IsElliptic := hW
  letI : Module ↑(S.residueField s) (projModelPoleSections W n) :=
    Module.compHom _ (Scheme.Modules.baseScalarHom (projModelπ W))
  let eSections := @sectionPoleSheafPowerPointedSectionsEquiv
    (↑(S.residueField s)) inferInstance (π.fiber s) (projModel W)
    (π.fiberToSpecResidueField s) (projModelπ W)
    hsepFiber (by infer_instance)
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _)
    (projModelZero W) (projModelZero_projModelπ W) (projModel_smooth W)
    e heπ hez n
  exact eSections.finrank_eq.symm.trans
    (sectionPoleSheafPower_projModel_finrank W hn)

end ModularCurves
