import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ModularCurves.ForMathlib.SchemeModuleBaseCechFlat
import ModularCurves.Picard.InvertibleSheaf

/-!
# Flat Cech factors from local trivializations

A trivialization of a scheme module on an affine open identifies its section
module with the coordinate ring of that open.  Retaining the scalar action
from an affine base then makes the section module flat whenever the structural
morphism is flat.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- A trivialization on an open identifies its sections with the sections of
the ambient structure sheaf on that open. -/
noncomputable def sectionsIsoUnitSectionsOfRestrictIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.val.obj (op U) ≅ (unitObj X).val.obj (op U) := by
  let eAdd :=
    M.presheaf.mapIso (eqToIso U.ι_image_top).op ≪≫
      (M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).symm ≪≫
      asIso (e.hom.app (⊤ : U.toScheme.Opens)) ≪≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso
        U.topIso
  refine ModuleCat.isoMk eAdd ?_
  intro (r : Γ(X, U))
  ext (x : Γ(M, U))
  dsimp only [eAdd]
  change r • U.topIso.hom
      (e.hom.app (⊤ : U.toScheme.Opens)
        ((M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op x))) =
    U.topIso.hom
      (e.hom.app (⊤ : U.toScheme.Opens)
        ((M.restrictAppIso U.ι (⊤ : U.toScheme.Opens)).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op (r • x))))
  rw [M.map_smul]
  rw [smul_restrictAppIso_inv_apply]
  rw [Hom.app_smul]
  have hr : (U.ι.appIso (⊤ : U.toScheme.Opens)).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op r) =
      U.topIso.inv r := by
    rw [Scheme.Opens.topIso_inv]
    rw [Scheme.Opens.ι_appIso]
    change X.presheaf.map (eqToHom U.ι_image_top).op r = _
    rfl
  rw [hr]
  change r * U.topIso.hom _ = U.topIso.hom (U.topIso.inv r * _)
  rw [map_mul]
  have hri : U.topIso.hom (U.topIso.inv r) = r :=
    Iso.inv_hom_id_apply U.topIso r
  rw [hri]

/-- The local section comparison, regarded as an isomorphism of modules over
the global functions on the base. -/
noncomputable def baseModulePresheafObjIsoUnitOfRestrictIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    (baseModulePresheaf π M).obj (op U) ≅
      (baseModulePresheaf π (unitObj X)).obj (op U) := by
  let f : Γ(S, (⊤ : S.Opens)) →+* Γ(X, U) :=
    (X.presheaf.map
      ((initialOpOfTerminal isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  exact (ModuleCat.restrictScalars f).mapIso
    (sectionsIsoUnitSectionsOfRestrictIso M U e)

/-- Sections of a module trivialized on an affine open are flat over an
affine base when the structural morphism is flat. -/
theorem baseModulePresheaf_obj_flat_of_restrictIso
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    Module.Flat Γ(S, (⊤ : S.Opens))
      ((baseModulePresheaf π M).obj (op U)) := by
  letI : Module.Flat Γ(S, (⊤ : S.Opens))
      ((baseModulePresheaf π (unitObj X)).obj (op U)) :=
    π.flat_appLE (isAffineOpen_top S) hU le_top
  exact Module.Flat.of_linearEquiv
    (baseModulePresheafObjIsoUnitOfRestrictIso π M U e).toLinearEquiv

/-- Every intersection-section factor is flat when the cover consists of
affine opens carrying trivializations. -/
theorem baseCechFactor_flat_of_trivializingCover
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    [X.IsSeparated] (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    (htriv : ∀ i, Nonempty (M.restrict (U i).ι ≅ unitObj (U i).toScheme))
    (n : ℕ) (i : Fin (n + 1) → ι) :
    Module.Flat Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U n i) := by
  let W := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  have hW : IsAffineOpen W := by
    change IsAffineOpen (∏ᶜ fun k : Fin (n + 1) => U (i k))
    rw [show (∏ᶜ fun k : Fin (n + 1) => U (i k)) =
        ⨅ k : Fin (n + 1), U (i k) from
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (Preorder.isLimitIInf _)).to_eq]
    exact IsAffineOpen.iInf fun k => hU (i k)
  have hWU : W ≤ U (i 0) :=
    leOfHom (Pi.π (fun k : Fin (n + 1) => U (i k)) 0)
  obtain ⟨e⟩ := htriv (i 0)
  change Module.Flat Γ(S, (⊤ : S.Opens))
    ((baseModulePresheaf π M).obj (op W))
  exact baseModulePresheaf_obj_flat_of_restrictIso π M hW
    (restrictIsoOfPullbackIso M W
      (restrictTrivialization hWU (pullbackIsoOfRestrictIso M (U (i 0)) e)))

/-- Every term of the finite base-linear Cech complex is flat when the cover
consists of affine opens carrying trivializations. -/
theorem baseCechComplex_X_flat_of_trivializingCover
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    [X.IsSeparated] (M : X.Modules) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (htriv : ∀ i, Nonempty (M.restrict (U i).ι ≅ unitObj (U i).toScheme))
    (n : ℕ) :
    Module.Flat Γ(S, (⊤ : S.Opens)) ((baseCechComplex π M U).X n) :=
  baseCechComplex_X_flat_of_factors π M U n fun i =>
    baseCechFactor_flat_of_trivializingCover π M U hU htriv n i

end

end AlgebraicGeometry.Scheme.Modules
