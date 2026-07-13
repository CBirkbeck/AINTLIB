import ModularCurves.Picard.DualPullback.Map

/-!
# Pullback adjunction over an open target

The adjunction-defined comparison square agrees with the explicit pullback/restriction
isomorphism over an open subscheme.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable def openPushforwardSquareIsoT (f : Y ⟶ X)
    (U : X.Opens) :
    pushforward (f ∣_ U) ⋙ pushforward U.ι ≅
      pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f :=
  pushforwardComp (f ∣_ U) U.ι ≪≫
    pushforwardCongr (morphismRestrict_ι f U) ≪≫
    (pushforwardComp (f ⁻¹ᵁ U).ι f).symm

noncomputable def openPullbackSquareAdjunctionIsoT (f : Y ⟶ X)
    (U : X.Opens) :
    pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅
      restrictFunctor U.ι ⋙ pullback (f ∣_ U) :=
  let localAdj := (restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let globalAdj := (pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)
  globalAdj.leftAdjointUniq
    (localAdj.ofNatIsoRight (openPushforwardSquareIsoT f U))

noncomputable def openPullbackSquareExplicitIsoT (f : Y ⟶ X)
    (U : X.Opens) :
    restrictFunctor U.ι ⋙ pullback (f ∣_ U) ≅
      pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι)
      (pullback (f ∣_ U)) ≪≫
    pullbackComp (f ∣_ U) U.ι ≪≫
    pullbackCongr (morphismRestrict_ι f U) ≪≫
    (pullbackComp (f ⁻¹ᵁ U).ι f).symm ≪≫
    Functor.isoWhiskerLeft (pullback f)
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

theorem conjugateEquiv_pullbackCongr_homT
    {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) :
    conjugateEquiv (pullbackPushforwardAdjunction g)
        (pullbackPushforwardAdjunction f) (pullbackCongr h).hom =
      (pushforwardCongr h).inv := by
  subst g
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom,
    conjugateEquiv_id]
  apply NatTrans.ext
  funext M
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x = (((pushforwardCongr (rfl : f = f)).inv.app M).app U.unop) x
  rw [pushforwardCongr_inv_app_app]
  simp
  rfl

theorem conjugateEquiv_openPullbackSquareExplicitIso_homT
    (f : Y ⟶ X) (U : X.Opens) :
    conjugateEquiv
        ((pullbackPushforwardAdjunction f).comp
          (restrictAdjunction (f ⁻¹ᵁ U).ι))
        ((restrictAdjunction U.ι).comp
          (pullbackPushforwardAdjunction (f ∣_ U)))
        (openPullbackSquareExplicitIsoT f U).hom =
      (openPushforwardSquareIsoT f U).inv := by
  let h := morphismRestrict_ι f U
  let adj₀ := (restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let adj₁ := (pullbackPushforwardAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let adj₂ := pullbackPushforwardAdjunction ((f ∣_ U) ≫ U.ι)
  let adj₃ := pullbackPushforwardAdjunction ((f ⁻¹ᵁ U).ι ≫ f)
  let adj₄ := (pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι)
  let adj₅ := (pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)
  let A := Functor.whiskerRight (restrictFunctorIsoPullback U.ι).hom
    (pullback (f ∣_ U))
  let B := (pullbackComp (f ∣_ U) U.ι).hom
  let C := (pullbackCongr h).hom
  let D := (pullbackComp (f ⁻¹ᵁ U).ι f).inv
  let E := Functor.whiskerLeft (pullback f)
    (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).inv
  have hA : conjugateEquiv adj₁ adj₀ A = 𝟙 _ := by
    dsimp only [A, adj₁, adj₀]
    rw [conjugateEquiv_whiskerRight]
    simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  have hB : conjugateEquiv adj₂ adj₁ B =
      (pushforwardComp (f ∣_ U) U.ι).inv := by
    exact conjugateEquiv_pullbackComp_hom (f ∣_ U) U.ι
  have hC : conjugateEquiv adj₃ adj₂ C =
      (pushforwardCongr h).inv := by
    exact conjugateEquiv_pullbackCongr_homT h
  have hD : conjugateEquiv adj₄ adj₃ D =
      (pushforwardComp (f ⁻¹ᵁ U).ι f).hom := by
    dsimp only [D, adj₄, adj₃]
    exact conjugateEquiv_pullbackComp_inv (f ⁻¹ᵁ U).ι f
  have hE : conjugateEquiv adj₅ adj₄ E = 𝟙 _ := by
    dsimp only [E, adj₅, adj₄]
    rw [conjugateEquiv_whiskerLeft]
    simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  change conjugateEquiv adj₅ adj₀ (A ≫ B ≫ C ≫ D ≫ E) = _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp adj₅ adj₄ adj₀]
  rw [hE, Category.id_comp]
  rw [← conjugateEquiv_comp adj₄ adj₃ adj₀]
  rw [hD]
  rw [← conjugateEquiv_comp adj₃ adj₂ adj₀]
  rw [hC]
  rw [← conjugateEquiv_comp adj₂ adj₁ adj₀]
  rw [hB, hA]
  simp only [Category.comp_id]
  rfl

theorem conjugateEquiv_openPullbackSquareExplicitIso_invT
    (f : Y ⟶ X) (U : X.Opens) :
    conjugateEquiv
        ((restrictAdjunction U.ι).comp
          (pullbackPushforwardAdjunction (f ∣_ U)))
        ((pullbackPushforwardAdjunction f).comp
          (restrictAdjunction (f ⁻¹ᵁ U).ι))
        (openPullbackSquareExplicitIsoT f U).inv =
      (openPushforwardSquareIsoT f U).hom := by
  let e := openPullbackSquareExplicitIsoT f U
  let r := openPushforwardSquareIsoT f U
  let localAdj := (restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let globalAdj := (pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)
  have h := conjugateEquiv_comm globalAdj localAdj
    (α := e.hom) (β := e.inv) e.inv_hom_id
  have he : conjugateEquiv globalAdj localAdj e.hom = r.inv :=
    conjugateEquiv_openPullbackSquareExplicitIso_homT f U
  rw [he] at h
  apply (cancel_epi r.inv).1
  exact h.trans r.inv_hom_id.symm

theorem openPullbackSquareAdjunctionIso_eq_explicitT
    (f : Y ⟶ X) (U : X.Opens) :
    openPullbackSquareAdjunctionIsoT f U =
      (openPullbackSquareExplicitIsoT f U).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let localAdj := (restrictAdjunction U.ι).comp
    (pullbackPushforwardAdjunction (f ∣_ U))
  let globalAdj := (pullbackPushforwardAdjunction f).comp
    (restrictAdjunction (f ⁻¹ᵁ U).ι)
  apply (globalAdj.homEquiv _ _).injective
  change globalAdj.homEquiv _ _
      ((globalAdj.leftAdjointUniq
        (localAdj.ofNatIsoRight (openPushforwardSquareIsoT f U))).hom.app M) = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have h := unit_conjugateEquiv localAdj globalAdj
    (openPullbackSquareExplicitIsoT f U).inv M
  rw [conjugateEquiv_openPullbackSquareExplicitIso_invT] at h
  change localAdj.unit.app M ≫
      (openPushforwardSquareIsoT f U).hom.app _ =
    globalAdj.unit.app M ≫
      (pushforward (f ⁻¹ᵁ U).ι ⋙ pushforward f).map
        ((openPullbackSquareExplicitIsoT f U).inv.app M)
  exact h

theorem openPullbackSquareExplicitIsoT_hom_app
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (openPullbackSquareExplicitIsoT f U).hom.app M =
      (localPullbackRestrictIso f M U).hom := by
  rfl

theorem openPullbackSquareExplicitIsoT_app
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (openPullbackSquareExplicitIsoT f U).app M =
      localPullbackRestrictIso f M U := by
  rfl

theorem openPullbackSquareAdjunctionIsoT_app
    (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (openPullbackSquareAdjunctionIsoT f U).app M =
      (localPullbackRestrictIso f M U).symm := by
  have h := congrArg (fun e ↦ e.app M)
    (openPullbackSquareAdjunctionIso_eq_explicitT f U)
  change (openPullbackSquareAdjunctionIsoT f U).app M =
    ((openPullbackSquareExplicitIsoT f U).app M).symm at h
  rw [openPullbackSquareExplicitIsoT_app] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
