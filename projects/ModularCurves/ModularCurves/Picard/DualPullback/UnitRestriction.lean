import ModularCurves.Picard.DualPullback.UnitSquare

/-!
# Restriction of the local structure-module pullback

The canonical local pullback of the structure module is compatible with shrinking opens.
-/

universe u v

open AlgebraicGeometry CategoryTheory



namespace AlgebraicGeometry.Scheme.Modules

theorem openPullbackRestrictIso_hom_app_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) (M : U.toScheme.Modules) :
    (openPullbackRestrictIso f i).hom.app M =
      (pullback (f ∣_ V)).map
          ((restrictFunctorIsoPullback
            (X.homOfLE (leOfHom i))).hom.app M) ≫
        (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
          (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
          (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app M ≫
        (restrictFunctorIsoPullback
          (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
            ((pullback (f ∣_ U)).obj M) := by
  simp only [openPullbackRestrictIso, pullbackSquareIso, Iso.trans_hom,
    Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  let a := (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback (X.homOfLE (leOfHom i))).hom.app M)
  let b := (pullbackComp (f ∣_ V)
    (X.homOfLE (leOfHom i))).hom.app M
  let c := (pullbackCongr
    (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app M
  let d := (pullbackComp
    (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)).inv.app M
  let e := (restrictFunctorIsoPullback
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
      ((pullback (f ∣_ U)).obj M)
  change a ≫ b ≫ c ≫ d ≫ e = a ≫ (b ≫ c ≫ d) ≫ e
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace CategoryTheory

theorem reassoc_three_tailG {C : Type u} [Category.{v} C]
    {A B D E F G : C}
    {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : E ⟶ F} {e : F ⟶ G} {z : A ⟶ G}
    (h : a ≫ b ≫ (c ≫ d ≫ e) = z) :
    (a ≫ b ≫ c) ≫ d ≫ e = z := by
  calc
    (a ≫ b ≫ c) ≫ d ≫ e = a ≫ b ≫ (c ≫ d ≫ e) := by
      simp only [Category.assoc]
    _ = z := h

end CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def localPullbackUnitRestrictSourceG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) : (f ⁻¹ᵁ V : Scheme).Modules :=
  (pullback (f ∣_ V)).obj
    ((restrictFunctor (X.homOfLE (leOfHom i))).obj
      (unitObj U))

noncomputable def localPullbackUnitRestrictTargetG (f : Y ⟶ X)
    {U V : X.Opens} (_i : V ⟶ U) : (f ⁻¹ᵁ V : Scheme).Modules :=
  unitObj (f ⁻¹ᵁ V)

noncomputable def localPullbackUnitRestrictLeftG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (openPullbackRestrictIso f i).hom.app
        (unitObj U) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackUnitIso f U).hom ≫
      (overRestrictUnitIso
        ((TopologicalSpace.Opens.map f.base).map i)).hom

noncomputable def localPullbackUnitRestrictRightG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (pullback (f ∣_ V)).map (overRestrictUnitIso i).hom ≫
    (localPullbackUnitIso f V).hom

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def localPullbackUnitRestrictExpandedLeftG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictSourceG f i ⟶
      localPullbackUnitRestrictTargetG f i :=
  (pullback (f ∣_ V)).map
        ((restrictFunctorIsoPullback
          (X.homOfLE (leOfHom i))).hom.app (unitObj U)) ≫
      (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
        (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
        (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app (unitObj U) ≫
      (restrictFunctorIsoPullback
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
          ((pullback (f ∣_ U)).obj (unitObj U)) ≫
      (restrictFunctor
        (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
          (localPullbackUnitIso f U).hom ≫
      (overRestrictUnitIso
        ((TopologicalSpace.Opens.map f.base).map i)).hom

theorem localPullbackUnitRestrictLeft_eq_expandedG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictLeftG f i =
      localPullbackUnitRestrictExpandedLeftG f i := by
  unfold localPullbackUnitRestrictLeftG
    localPullbackUnitRestrictExpandedLeftG
  rw [openPullbackRestrictIso_hom_app_eq]
  exact CategoryTheory.reassoc_three_tailG rfl

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localPullbackUnitRestrictExpandedLeft_eq_rightG
    (f : Y ⟶ X) {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictExpandedLeftG f i =
      localPullbackUnitRestrictRightG f i := by
  unfold localPullbackUnitRestrictExpandedLeftG
    localPullbackUnitRestrictRightG
  rw [localPullbackUnitIso_hom_eqP, localPullbackUnitIso_hom_eqP]
  rw [overRestrictUnitIso_eq_restrictUnitIsoP,
    overRestrictUnitIso_eq_restrictUnitIsoP]
  unfold localPullbackUnitRestrictSourceG
    localPullbackUnitRestrictTargetG
  let a := (pullback (f ∣_ V)).map
    ((restrictFunctorIsoPullback
      (X.homOfLE (leOfHom i))).hom.app (unitObj U))
  let b := (pullbackSquareIso (f ∣_ V) (X.homOfLE (leOfHom i))
    (Y.homOfLE (f.preimage_mono (leOfHom i))) (f ∣_ U)
    (morphismRestrict_homOfLE f V U (leOfHom i))).hom.app (unitObj U)
  let c := (restrictFunctorIsoPullback
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).inv.app
      ((pullback (f ∣_ U)).obj (unitObj U))
  let d := (restrictFunctor
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).map
      (pullbackUnitIso (f ∣_ U)).hom
  let e := (restrictUnitIso
    (Y.homOfLE (f.preimage_mono (leOfHom i)))).hom
  let z := (pullback (f ∣_ V)).map
      (restrictUnitIso (X.homOfLE (leOfHom i))).hom ≫
    (pullbackUnitIso (f ∣_ V)).hom
  have hraw : a ≫ b ≫ (c ≫ d ≫ e) = z :=
    unitNat_rawStage0_eq_targetG f i
  change a ≫ b ≫ c ≫ d ≫ e = z
  exact hraw

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

theorem localPullbackUnitIso_restrict_homG (f : Y ⟶ X)
    {U V : X.Opens} (i : V ⟶ U) :
    localPullbackUnitRestrictLeftG f i =
      localPullbackUnitRestrictRightG f i :=
  (localPullbackUnitRestrictLeft_eq_expandedG f i).trans
    (localPullbackUnitRestrictExpandedLeft_eq_rightG f i)

end AlgebraicGeometry.Scheme.Modules
