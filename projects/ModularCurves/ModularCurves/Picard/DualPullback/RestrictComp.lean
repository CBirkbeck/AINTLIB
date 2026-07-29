import ModularCurves.Picard.DualPullback.Square

/-!
# Restriction and pullback composition

Option-free comparison lemmas for restriction functors, pullback functors, and the
canonical square isomorphism.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Scheme.{u}}

theorem restrictFunctorComp_unit
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : C.Modules) :
    (restrictAdjunction (f ≫ g)).unit.app M ≫
        (pushforward (f ≫ g)).map
          ((restrictFunctorComp f g).hom.app M) =
      ((restrictAdjunction g).comp (restrictAdjunction f)).unit.app M ≫
        (pushforwardComp f g).hom.app
          ((restrictFunctor g ⋙ restrictFunctor f).obj M) := by
  rw [Adjunction.comp_unit_app]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  conv_lhs => erw [sheafOfModules_comp_app_apply]
  conv_rhs => erw [sheafOfModules_comp_app_apply]
  change ((restrictFunctorComp f g).hom.app M).app
      ((f ≫ g) ⁻¹ᵁ U.unop)
        (((restrictAdjunction (f ≫ g)).unit.app M).app U.unop x) =
    (((restrictAdjunction g).unit.app M ≫
      (pushforward g).map
        ((restrictAdjunction f).unit.app ((restrictFunctor g).obj M))).app U.unop) x
  let yfg := ((restrictAdjunction (f ≫ g)).unit.app M).app U.unop x
  let yg := ((restrictAdjunction g).unit.app M).app U.unop x
  let yfg' := M.presheaf.map
    (homOfLE ((f ≫ g).image_preimage_le U.unop)).op x
  let yg' := M.presheaf.map (homOfLE (g.image_preimage_le U.unop)).op x
  let q := fun z => ((restrictFunctorComp f g).hom.app M).app
    ((f ≫ g) ⁻¹ᵁ U.unop) z
  let r := fun z => ((restrictAdjunction f).unit.app
    ((restrictFunctor g).obj M)).app (g ⁻¹ᵁ U.unop) z
  let p := (restrictAdjunction g).unit.app M
  let s := (pushforward g).map
    ((restrictAdjunction f).unit.app ((restrictFunctor g).obj M))
  have hfg : yfg = yfg' := ConcreteCategory.congr_hom
    (restrictAdjunction_unit_app_app (f ≫ g) M U.unop) x
  have hg : yg = yg' := ConcreteCategory.congr_hom
    (restrictAdjunction_unit_app_app g M U.unop) x
  have hcomp := ConcreteCategory.congr_hom
    (restrictFunctorComp_hom_app_app
      (U := (f ≫ g) ⁻¹ᵁ U.unop) f g M) yfg'
  have hf := ConcreteCategory.congr_hom
    (restrictAdjunction_unit_app_app f ((restrictFunctor g).obj M)
      (g ⁻¹ᵁ U.unop)) yg'
  have hpush := ConcreteCategory.congr_hom
    (pushforward_map_app g
      ((restrictAdjunction f).unit.app ((restrictFunctor g).obj M)) U.unop) yg
  have hright : (p ≫ s).app U.unop x = s.app U.unop yg := by
    rfl
  have hmiddle : q yfg' =
      ((restrictFunctor g).obj M).presheaf.map
        (homOfLE (f.image_preimage_le (g ⁻¹ᵁ U.unop))).op yg' :=
    hcomp.trans (by
      dsimp only [yfg', yg']
      change M.presheaf.map _ (M.presheaf.map _ x) =
        M.presheaf.map _ (M.presheaf.map _ x)
      erw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
      exact ConcreteCategory.congr_hom
        (M.presheaf.congr_map (Subsingleton.elim _ _)) x)
  have htoR : q yfg' = r yg' := hmiddle.trans hf.symm
  have htoS : r yg = s.app U.unop yg := hpush.symm
  have htail : r yg' = (p ≫ s).app U.unop x :=
    (congrArg r hg.symm).trans (htoS.trans hright.symm)
  change q yfg = (p ≫ s).app U.unop x
  exact (congrArg q hfg).trans (htoR.trans htail)

theorem restrictFunctorComp_eq_leftAdjointCompIso_symm
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    restrictFunctorComp f g =
      (Adjunction.leftAdjointCompIso
        (restrictAdjunction g) (restrictAdjunction f)
        (restrictAdjunction (f ≫ g)) (pushforwardComp f g)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((restrictAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  have h := unit_conjugateEquiv
    ((restrictAdjunction g).comp (restrictAdjunction f))
    (restrictAdjunction (f ≫ g))
    (Adjunction.leftAdjointCompIso
      (restrictAdjunction g) (restrictAdjunction f)
      (restrictAdjunction (f ≫ g)) (pushforwardComp f g)).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at h
  exact (restrictFunctorComp_unit f g M).trans h

example (g : B ⟶ C) [IsOpenImmersion g] :
    conjugateEquiv (pullbackPushforwardAdjunction g) (restrictAdjunction g)
        (restrictFunctorIsoPullback g).hom =
      𝟙 (pushforward g) := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

theorem restrictFunctorIsoPullback_comp_middle
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    Functor.whiskerRight (restrictFunctorIsoPullback g).hom
          (restrictFunctor f) ≫
        Functor.whiskerLeft (pullback g)
          (restrictFunctorIsoPullback f).hom =
      (((restrictAdjunction g).comp (restrictAdjunction f)).leftAdjointUniq
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f))).hom := by
  apply (conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    ((restrictAdjunction g).comp (restrictAdjunction f))).injective
  rw [← conjugateEquiv_comp
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    ((pullbackPushforwardAdjunction g).comp (restrictAdjunction f))]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight]
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

theorem conjugateEquiv_restrictFunctorComp_hom
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
        ((restrictAdjunction g).comp (restrictAdjunction f))
        (restrictAdjunction (f ≫ g))
        (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  rw [restrictFunctorComp_eq_leftAdjointCompIso_symm]
  exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (restrictAdjunction g) (restrictAdjunction f)
    (restrictAdjunction (f ≫ g)) (pushforwardComp f g)

theorem conjugateEquiv_pullbackComp_hom
    (f : A ⟶ B) (g : B ⟶ C) :
    conjugateEquiv
        (pullbackPushforwardAdjunction (f ≫ g))
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f))
        (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  let eL := pullbackComp f g
  let eR := pushforwardComp f g
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g))
    (α := eL.inv) (β := eL.hom) eL.hom_inv_id
  rw [conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_epi eR.hom).1
  exact h.trans eR.hom_inv_id.symm

theorem conjugateEquiv_restrictFunctorIsoPullback_comp_middle
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f))
        ((restrictAdjunction g).comp (restrictAdjunction f))
        (Functor.whiskerRight (restrictFunctorIsoPullback g).hom
            (restrictFunctor f) ≫
          Functor.whiskerLeft (pullback g)
            (restrictFunctorIsoPullback f).hom) =
      𝟙 (pushforward f ⋙ pushforward g) := by
  rw [restrictFunctorIsoPullback_comp_middle]
  simp [Adjunction.leftAdjointUniq]

theorem restrictFunctorIsoPullback_comp
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : C.Modules) :
    (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctor f).map
          ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app ((pullback g).obj M) ≫
        (pullbackComp f g).hom.app M =
      (restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
  let a := (restrictFunctorComp f g).hom
  let b := Functor.whiskerRight (restrictFunctorIsoPullback g).hom
      (restrictFunctor f) ≫
    Functor.whiskerLeft (pullback g) (restrictFunctorIsoPullback f).hom
  let c := (pullbackComp f g).hom
  have h : a ≫ b ≫ c = (restrictFunctorIsoPullback (f ≫ g)).hom := by
    apply (conjugateEquiv
      (pullbackPushforwardAdjunction (f ≫ g))
      (restrictAdjunction (f ≫ g))).injective
    have h₁ := conjugateEquiv_comp
      (pullbackPushforwardAdjunction (f ≫ g))
      ((pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f))
      (restrictAdjunction (f ≫ g)) c (a ≫ b)
    have h₂ := conjugateEquiv_comp
      ((pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f))
      ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) b a
    calc
      conjugateEquiv
          (pullbackPushforwardAdjunction (f ≫ g))
          (restrictAdjunction (f ≫ g)) (a ≫ b ≫ c) =
        conjugateEquiv
            (pullbackPushforwardAdjunction (f ≫ g))
            ((pullbackPushforwardAdjunction g).comp
              (pullbackPushforwardAdjunction f)) c ≫
          conjugateEquiv
            ((pullbackPushforwardAdjunction g).comp
              (pullbackPushforwardAdjunction f))
            (restrictAdjunction (f ≫ g)) (a ≫ b) := h₁.symm
      _ = conjugateEquiv
            (pullbackPushforwardAdjunction (f ≫ g))
            ((pullbackPushforwardAdjunction g).comp
              (pullbackPushforwardAdjunction f)) c ≫
          (conjugateEquiv
              ((pullbackPushforwardAdjunction g).comp
                (pullbackPushforwardAdjunction f))
              ((restrictAdjunction g).comp (restrictAdjunction f)) b ≫
            conjugateEquiv
              ((restrictAdjunction g).comp (restrictAdjunction f))
              (restrictAdjunction (f ≫ g)) a) :=
        congrArg _ h₂.symm
      _ = conjugateEquiv
          (pullbackPushforwardAdjunction (f ≫ g))
          (restrictAdjunction (f ≫ g))
          (restrictFunctorIsoPullback (f ≫ g)).hom := by
        dsimp only [a, b, c]
        rw [conjugateEquiv_pullbackComp_hom]
        rw [conjugateEquiv_restrictFunctorIsoPullback_comp_middle]
        rw [conjugateEquiv_restrictFunctorComp_hom]
        simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]
  exact congr_app h M

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme.Modules

variable {A B C : Scheme.{u}}

theorem restrictFunctorIsoPullback_comp_inv
    (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : C.Modules) :
    (pullbackComp f g).inv.app M ≫
        (pullback f).map
          ((restrictFunctorIsoPullback g).inv.app M) ≫
        (restrictFunctorIsoPullback f).inv.app
          ((restrictFunctor g).obj M) =
      (restrictFunctorIsoPullback (f ≫ g)).inv.app M ≫
        (restrictFunctorComp f g).hom.app M := by
  let eC := (restrictFunctorComp f g).app M
  let eG := (restrictFunctor f).mapIso
    ((restrictFunctorIsoPullback g).app M)
  let eF := (restrictFunctorIsoPullback f).app ((pullback g).obj M)
  let eP := (pullbackComp f g).app M
  let eR := (restrictFunctorIsoPullback (f ≫ g)).app M
  have hcomp : eC.hom ≫ eG.hom ≫ eF.hom ≫ eP.hom = eR.hom :=
    restrictFunctorIsoPullback_comp f g M
  have hnat := (restrictFunctorIsoPullback f).inv.naturality
    ((restrictFunctorIsoPullback g).inv.app M)
  change eP.inv ≫
      (pullback f).map ((restrictFunctorIsoPullback g).inv.app M) ≫
      (restrictFunctorIsoPullback f).inv.app
        ((restrictFunctor g).obj M) = eR.inv ≫ eC.hom
  erw [hnat]
  change eP.inv ≫ eF.inv ≫ eG.inv = eR.inv ≫ eC.hom
  rw [← cancel_epi eR.hom]
  conv_lhs => rw [← hcomp]
  simp only [Category.assoc]
  erw [eP.hom_inv_id_assoc, eF.hom_inv_id_assoc,
    eG.hom_inv_id, Category.comp_id, eR.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory


namespace AlgebraicGeometry.Scheme.Modules

theorem pullbackSquareIso_vcomp_app
    {A B C D E F : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (q : D ⟶ F) (e : C ⟶ E) (r : E ⟶ F)
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ q = e ≫ r)
    (M : F.Modules) :
    (pullbackSquareIso a b c d h₁).hom.app ((pullback q).obj M) ≫
        (pullback c).map ((pullbackSquareIso d q e r h₂).hom.app M) =
      (pullback a).map ((pullbackComp b q).hom.app M) ≫
        (pullbackSquareIso a (b ≫ q) (c ≫ e) r
          (by
            exact (Category.assoc a b q).symm.trans
              ((congrArg (· ≫ q) h₁).trans
                ((Category.assoc c d q).trans
                  ((congrArg (c ≫ ·) h₂).trans
                    (Category.assoc c e r).symm))))).hom.app M ≫
        (pullbackComp c e).inv.app ((pullback r).obj M) := by
  have H := congrArg (fun z => z.hom.app M)
    (pullbackSquareIso_vcomp a b c d q e r h₁ h₂)
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app] at H
  change 𝟙 _ ≫
      (pullbackSquareIso a b c d h₁).hom.app ((pullback q).obj M) ≫
        𝟙 _ ≫
          (pullback c).map ((pullbackSquareIso d q e r h₂).hom.app M) =
    (pullback a).map ((pullbackComp b q).hom.app M) ≫
      (pullbackSquareIso a (b ≫ q) (c ≫ e) r _).hom.app M ≫
        (pullbackComp c e).inv.app ((pullback r).obj M) ≫ 𝟙 _ at H
  simpa only [Category.id_comp, Category.comp_id] using H

end AlgebraicGeometry.Scheme.Modules
