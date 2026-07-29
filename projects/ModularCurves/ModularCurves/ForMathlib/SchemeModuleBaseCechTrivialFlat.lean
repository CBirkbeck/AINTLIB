/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ModularCurves.ForMathlib.SchemeModuleBaseCechFlat
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.Picard.InvertibleSheafLocallyFree

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
  rw [M.map_smul, smul_restrictAppIso_inv_apply, Hom.app_smul]
  have hr : (U.ι.appIso (⊤ : U.toScheme.Opens)).hom
      (X.presheaf.map (eqToHom U.ι_image_top).op r) =
      U.topIso.inv r := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appIso]
    change X.presheaf.map (eqToHom U.ι_image_top).op r = _
    rfl
  rw [hr]
  change r * U.topIso.hom _ = U.topIso.hom (U.topIso.inv r * _)
  rw [map_mul]
  have hri : U.topIso.hom (U.topIso.inv r) = r :=
    Iso.inv_hom_id_apply U.topIso r
  rw [hri]

/-- Sections of an invertible module on an affine open are flat over the ring of that open. -/
theorem sections_flat_of_isInvertible_of_isAffineOpen
    {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Module.Flat Γ(X, U) Γ(M, U) := by
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  obtain ⟨ι, V, hV, htriv⟩ := hM
  let t : Set Γ(X, U) := { f | ∃ i, X.basicOpen f ≤ V i }
  have hopen : ⨆ f : t, X.basicOpen f.1 = U := by
    apply le_antisymm
    · exact iSup_le fun f ↦ X.basicOpen_le f.1
    · calc
        U = U ⊓ ⊤ := by simp
        _ = U ⊓ ⨆ i, V i := by rw [hV]
        _ = ⨆ i, U ⊓ V i := by rw [inf_iSup_eq]
        _ ≤ ⨆ f : t, X.basicOpen f.1 := by
          refine iSup_le fun i ↦ ?_
          rintro x hx
          obtain ⟨f, hf, hxf⟩ :=
            hU.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
          exact (le_iSup (fun f : t ↦ X.basicOpen f.1) ⟨f, i, hf⟩) hxf
  have ht : Ideal.span t = ⊤ :=
    hU.iSup_basicOpen_eq_self_iff.mp hopen
  letI (g : t) : Algebra Γ(X, U) Γ(X, X.basicOpen g.1) :=
    inferInstance
  letI (g : t) : Module Γ(X, U) Γ(M, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen g.1))
  letI (g : t) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) :=
    hU.isLocalization_basicOpen g.1
  letI (g : t) : IsScalarTower Γ(X, U)
      Γ(X, X.basicOpen g.1) Γ(M, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : (g : t) →
      Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen g.1) :=
    fun g ↦
      {
        toFun := M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op
        map_add' :=
          (M.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom.map_add
        map_smul' := fun r x ↦
          M.map_smul (homOfLE (X.basicOpen_le g.1)) r x
      }
  letI : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) :=
    fun g ↦
      isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen
        M ⟨U, hU⟩ g.1
  refine Module.flat_of_isLocalized_span Γ(X, U) Γ(M, U) t ht
    (fun g ↦ Γ(M, X.basicOpen g.1)) φ ?_
  intro g
  obtain ⟨i, hi⟩ := g.2
  obtain ⟨e⟩ := htriv i
  let W := X.basicOpen g.1
  let eW : M.restrict W.ι ≅ unitObj W.toScheme :=
    restrictIsoOfPullbackIso M W (restrictTrivialization hi e)
  let eUnit : (unitObj X).val.obj (op W) ≅
      ModuleCat.of Γ(X, W) Γ(X, W) := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext x
    rfl
  letI : Module.Flat Γ(X, W) Γ(M, W) := by
    exact Module.Flat.of_linearEquiv
      (sectionsIsoUnitSectionsOfRestrictIso M W eW ≪≫ eUnit).toLinearEquiv
  letI : Module.Flat Γ(X, U) Γ(X, W) := by
    dsimp only [W]
    exact IsLocalization.flat Γ(X, X.basicOpen g.1) (Submonoid.powers g.1)
  exact Module.Flat.trans Γ(X, U) Γ(X, W) Γ(M, W)

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

/-- Sections of an invertible module on an affine source open are flat over an affine base
whenever the structural morphism is flat. -/
theorem baseModulePresheaf_obj_flat_of_isInvertible
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    (M : X.Modules) (hM : IsInvertible M) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Module.Flat Γ(S, (⊤ : S.Opens))
      ((baseModulePresheaf π M).obj (op U)) := by
  let R := Γ(S, (⊤ : S.Opens))
  let A := Γ(X, U)
  letI : Module R Γ(M, U) :=
    ((baseModulePresheaf π M).obj (op U)).isModule
  change Module.Flat R Γ(M, U)
  let f : R →+* A :=
    (X.presheaf.map
      ((initialOpOfTerminal isTerminalTop).to (op U))).hom.comp
        π.appTop.hom
  letI : Algebra R A := f.toAlgebra
  letI : IsScalarTower R A Γ(M, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Flat R A := by
    exact π.flat_appLE (isAffineOpen_top S) hU le_top
  letI : Module.Flat A Γ(M, U) := by
    exact sections_flat_of_isInvertible_of_isAffineOpen M hM hU
  exact Module.Flat.trans R A Γ(M, U)

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

/-- Every intersection-section factor is flat for an invertible module and an affine cover. -/
theorem baseCechFactor_flat_of_isInvertible
    {X S : Scheme.{u}} (π : X ⟶ S) [IsAffine S] [Flat π]
    [X.IsSeparated] (M : X.Modules) (hM : IsInvertible M)
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (i : Fin (n + 1) → ι) :
    Module.Flat Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U n i) := by
  let W := ∏ᶜ fun k : Fin (n + 1) ↦ U (i k)
  have hW : IsAffineOpen W := by
    change IsAffineOpen (∏ᶜ fun k : Fin (n + 1) ↦ U (i k))
    rw [show (∏ᶜ fun k : Fin (n + 1) ↦ U (i k)) =
        ⨅ k : Fin (n + 1), U (i k) from
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (Preorder.isLimitIInf _)).to_eq]
    exact IsAffineOpen.iInf fun k ↦ hU (i k)
  change Module.Flat Γ(S, (⊤ : S.Opens))
    ((baseModulePresheaf π M).obj (op W))
  exact baseModulePresheaf_obj_flat_of_isInvertible π M hM hW

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
