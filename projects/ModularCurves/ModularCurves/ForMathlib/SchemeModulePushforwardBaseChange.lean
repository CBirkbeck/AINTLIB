import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Limits
import ModularCurves.ForMathlib.AffineModuleBaseChange

/-!
# Pullback--pushforward base change for scheme modules

This file constructs the canonical base-change morphism for a scheme module on a
cartesian square. It is the mate, under the pullback--pushforward adjunction, of
pullback pseudofunctoriality followed by the adjunction counit.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S)

private noncomputable def pullbackPushforwardBaseChangeSquare :
    TwoSquare (pullback t) (pullback f)
      (pullback (Limits.pullback.snd f t))
      (pullback (Limits.pullback.fst f t)) :=
  TwoSquare.mk _ _ _ _
    ((pullbackComp (Limits.pullback.snd f t) t).hom ≫
      (pullbackCongr (Limits.pullback.condition.symm :
        Limits.pullback.snd f t ≫ t =
          Limits.pullback.fst f t ≫ f)).hom ≫
      (pullbackComp (Limits.pullback.fst f t) f).inv)

private theorem conjugateEquiv_pullbackComp_hom
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    conjugateEquiv
        (pullbackPushforwardAdjunction (a ≫ b))
        ((pullbackPushforwardAdjunction b).comp
          (pullbackPushforwardAdjunction a))
        (pullbackComp a b).hom =
      (pushforwardComp a b).inv := by
  let eL := pullbackComp a b
  let eR := pushforwardComp a b
  have h := conjugateEquiv_comm
    ((pullbackPushforwardAdjunction b).comp
      (pullbackPushforwardAdjunction a))
    (pullbackPushforwardAdjunction (a ≫ b))
    (α := eL.inv) (β := eL.hom) eL.hom_inv_id
  rw [conjugateEquiv_pullbackComp_inv] at h
  apply (cancel_epi eR.hom).1
  exact h.trans eR.hom_inv_id.symm

private theorem conjugateEquiv_pullbackCongr_hom
    {A B : Scheme.{u}} {a b : A ⟶ B} (h : a = b) :
    conjugateEquiv (pullbackPushforwardAdjunction b)
        (pullbackPushforwardAdjunction a) (pullbackCongr h).hom =
      (pushforwardCongr h).inv := by
  subst b
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
  change x = (((pushforwardCongr (rfl : a = a)).inv.app M).app U.unop) x
  rw [pushforwardCongr_inv_app_app]
  simp
  rfl

private noncomputable def pullbackPushforwardBaseChangePushSquare :
    pushforward (Limits.pullback.fst f t) ⋙ pushforward f ⟶
      pushforward (Limits.pullback.snd f t) ⋙ pushforward t :=
  (pushforwardComp (Limits.pullback.fst f t) f).hom ≫
    (pushforwardCongr (Limits.pullback.condition.symm :
      Limits.pullback.snd f t ≫ t =
        Limits.pullback.fst f t ≫ f)).inv ≫
    (pushforwardComp (Limits.pullback.snd f t) t).inv

private theorem pullbackPushforwardBaseChangeSquare_conjugate :
    conjugateEquiv
        ((pullbackPushforwardAdjunction f).comp
          (pullbackPushforwardAdjunction (Limits.pullback.fst f t)))
        ((pullbackPushforwardAdjunction t).comp
          (pullbackPushforwardAdjunction (Limits.pullback.snd f t)))
        (pullbackPushforwardBaseChangeSquare f t) =
      pullbackPushforwardBaseChangePushSquare f t := by
  let q := Limits.pullback.snd f t
  let g := Limits.pullback.fst f t
  let h : q ≫ t = g ≫ f := Limits.pullback.condition.symm
  let adj₀ := (pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)
  let adj₁ := pullbackPushforwardAdjunction (g ≫ f)
  let adj₂ := pullbackPushforwardAdjunction (q ≫ t)
  let adj₃ := (pullbackPushforwardAdjunction t).comp
    (pullbackPushforwardAdjunction q)
  let A := (pullbackComp q t).hom
  let B := (pullbackCongr h).hom
  let C := (pullbackComp g f).inv
  have hA : conjugateEquiv adj₂ adj₃ A =
      (pushforwardComp q t).inv := by
    exact conjugateEquiv_pullbackComp_hom q t
  have hB : conjugateEquiv adj₁ adj₂ B =
      (pushforwardCongr h).inv := by
    exact conjugateEquiv_pullbackCongr_hom h
  have hC : conjugateEquiv adj₀ adj₁ C =
      (pushforwardComp g f).hom := by
    exact conjugateEquiv_pullbackComp_inv g f
  change conjugateEquiv adj₀ adj₃ (A ≫ B ≫ C) = _
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp adj₀ adj₁ adj₃, hC]
  rw [← conjugateEquiv_comp adj₁ adj₂ adj₃, hB, hA]
  rfl

private noncomputable def pullbackPushforwardBaseChangeAdj :
    pushforward f ⋙ pullback t ⋙ pullback (Limits.pullback.snd f t) ⟶
      pullback (Limits.pullback.fst f t) :=
  Functor.whiskerLeft (pushforward f)
      (pullbackComp (Limits.pullback.snd f t) t).hom ≫
    Functor.whiskerLeft (pushforward f)
      (pullbackCongr (Limits.pullback.condition.symm :
        Limits.pullback.snd f t ≫ t = Limits.pullback.fst f t ≫ f)).hom ≫
    Functor.whiskerLeft (pushforward f)
      (pullbackComp (Limits.pullback.fst f t) f).inv ≫
    Functor.whiskerRight (pullbackPushforwardAdjunction f).counit
      (pullback (Limits.pullback.fst f t))

private noncomputable def pullbackPushforwardBaseChangeAdjApp (M : X.Modules) :
    (pullback (Limits.pullback.snd f t)).obj
        ((pushforward f ⋙ pullback t).obj M) ⟶
      (pullback (Limits.pullback.fst f t)).obj M := by
  change (pushforward f ⋙ pullback t ⋙
    pullback (Limits.pullback.snd f t)).obj M ⟶ _
  exact (pullbackPushforwardBaseChangeAdj f t).app M

private lemma pullbackPushforwardBaseChangeAdjApp_naturality
    {M N : X.Modules} (φ : M ⟶ N) :
    (pullback (Limits.pullback.snd f t)).map
          ((pushforward f ⋙ pullback t).map φ) ≫
        pullbackPushforwardBaseChangeAdjApp f t N =
      pullbackPushforwardBaseChangeAdjApp f t M ≫
        (pullback (Limits.pullback.fst f t)).map φ := by
  change (pushforward f ⋙ pullback t ⋙
      pullback (Limits.pullback.snd f t)).map φ ≫
      (pullbackPushforwardBaseChangeAdj f t).app N =
    (pullbackPushforwardBaseChangeAdj f t).app M ≫
      (pullback (Limits.pullback.fst f t)).map φ
  exact (pullbackPushforwardBaseChangeAdj f t).naturality φ

private noncomputable abbrev pullbackPushforwardBaseChangeTarget :
    X.Modules ⥤ T.Modules where
  obj M := (pushforward (Limits.pullback.snd f t)).obj
    ((pullback (Limits.pullback.fst f t)).obj M)
  map φ := (pushforward (Limits.pullback.snd f t)).map
    ((pullback (Limits.pullback.fst f t)).map φ)
  map_id M := by simp
  map_comp φ ψ := by simp

private noncomputable def pullbackPushforwardBaseChangeCore :
    pushforward f ⋙ pullback t ⟶ pullbackPushforwardBaseChangeTarget f t where
  app M := (pullbackPushforwardAdjunction (Limits.pullback.snd f t)).homEquiv _ _
    (pullbackPushforwardBaseChangeAdjApp f t M)
  naturality {M N} φ := by
    rw [← Adjunction.homEquiv_naturality_left,
      ← Adjunction.homEquiv_naturality_right]
    exact congrArg
      ((pullbackPushforwardAdjunction (Limits.pullback.snd f t)).homEquiv
        ((pushforward f ⋙ pullback t).obj M)
        ((pullback (Limits.pullback.fst f t)).obj N))
      (pullbackPushforwardBaseChangeAdjApp_naturality f t φ)

private noncomputable def pullbackPushforwardBaseChangeTargetIso :
    pullbackPushforwardBaseChangeTarget f t ≅
      pullback (Limits.pullback.fst f t) ⋙
        pushforward (Limits.pullback.snd f t) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The canonical base-change morphism
`t^*(f_*M) ⟶ f'_*(g^*M)` for the pullback square of `f` along `t`. -/
noncomputable def pullbackPushforwardBaseChange :
    pushforward f ⋙ pullback t ⟶
      pullback (Limits.pullback.fst f t) ⋙
        pushforward (Limits.pullback.snd f t) :=
  pullbackPushforwardBaseChangeCore f t ≫
    (pullbackPushforwardBaseChangeTargetIso f t).hom

private theorem pullbackPushforwardBaseChange_eq_mate :
    pullbackPushforwardBaseChange f t =
      (mateEquiv (pullbackPushforwardAdjunction f)
        (pullbackPushforwardAdjunction (Limits.pullback.snd f t))
        (pullbackPushforwardBaseChangeSquare f t)).natTrans := by
  rfl

private theorem pullbackPushforwardBaseChange_iterated_mate :
    (mateEquiv
      (pullbackPushforwardAdjunction (Limits.pullback.fst f t))
      (pullbackPushforwardAdjunction t)
      (TwoSquare.mk _ _ _ _ (pullbackPushforwardBaseChange f t))).natTrans =
        pullbackPushforwardBaseChangePushSquare f t := by
  rw [pullbackPushforwardBaseChange_eq_mate]
  rw [iterated_mateEquiv_conjugateEquiv]
  exact pullbackPushforwardBaseChangeSquare_conjugate f t

private theorem pullbackPushforwardBaseChange_unit
    (M : X.Modules) :
    (pushforward f).map
          ((pullbackPushforwardAdjunction
            (Limits.pullback.fst f t)).unit.app M) ≫
        (pullbackPushforwardBaseChangePushSquare f t).app
          ((pullback (Limits.pullback.fst f t)).obj M) =
      (pullbackPushforwardAdjunction t).unit.app ((pushforward f).obj M) ≫
        (pushforward t).map ((pullbackPushforwardBaseChange f t).app M) := by
  have h := unit_mateEquiv
    (pullbackPushforwardAdjunction (Limits.pullback.fst f t))
    (pullbackPushforwardAdjunction t)
    (TwoSquare.mk _ _ _ _ (pullbackPushforwardBaseChange f t)) M
  have hmate := congrArg
    (fun k => k.app ((pullback (Limits.pullback.fst f t)).obj M))
    (pullbackPushforwardBaseChange_iterated_mate f t)
  rw [hmate] at h
  simpa only [Functor.id_obj] using h

private noncomputable def pushforwardTopSection
    (M : X.Modules) (m : Γ(M, (⊤ : X.Opens))) :
    Γ((pushforward f).obj M, (⊤ : S.Opens)) := by
  change Γ(M, f ⁻¹ᵁ (⊤ : S.Opens))
  exact M.presheaf.map
    (eqToHom (Scheme.Hom.preimage_top f)).op m

private theorem pushforwardMap_app_top_pushforwardTopSection
    {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, (⊤ : X.Opens))) :
    ((pushforward f).map φ).app (⊤ : S.Opens)
        (pushforwardTopSection f M m) =
      pushforwardTopSection f N (φ.app (⊤ : X.Opens) m) := by
  exact PresheafOfModules.naturality_apply φ.val
    (eqToHom (Scheme.Hom.preimage_top f)).op m

private theorem pushforwardTopSection_injective (M : X.Modules) :
    Function.Injective (pushforwardTopSection f M) := by
  change Function.Injective
    (M.presheaf.map (eqToHom (Scheme.Hom.preimage_top f)).op)
  exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance

private theorem pushforwardTopSection_affinePullbackUnitTop
    (M : S.Modules) (m : Γ(M, (⊤ : S.Opens))) :
    pushforwardTopSection f ((pullback f).obj M)
        (affinePullbackUnitTop f M m) =
      (((pullbackPushforwardAdjunction f).unit.app M).val.app
        (.op (⊤ : S.Opens))) m := by
  let P := (pullback f).obj M
  let unitValue :=
    (((pullbackPushforwardAdjunction f).unit.app M).val.app
      (.op (⊤ : S.Opens))) m
  change P.presheaf.map
      (eqToHom (Scheme.Hom.preimage_top f)).op
        (P.presheaf.map
          (eqToHom (Scheme.Hom.preimage_top f).symm).op unitValue) =
    unitValue
  have hmaps :
      P.presheaf.map
          (eqToHom (Scheme.Hom.preimage_top f).symm).op ≫
        P.presheaf.map
          (eqToHom (Scheme.Hom.preimage_top f)).op = 𝟙 _ := by
    rw [← P.presheaf.map_comp, ← P.presheaf.map_id]
    exact P.presheaf.congr_map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hmaps unitValue

private theorem pullbackPushforwardBaseChangePushSquare_app_top
    (N : (Limits.pullback f t).Modules)
    (n : Γ(N, (⊤ : (Limits.pullback f t).Opens))) :
    ((pullbackPushforwardBaseChangePushSquare f t).app N).app
      (⊤ : S.Opens)
        (pushforwardTopSection f
          ((pushforward (Limits.pullback.fst f t)).obj N)
          (pushforwardTopSection (Limits.pullback.fst f t) N n)) =
      pushforwardTopSection t
        ((pushforward (Limits.pullback.snd f t)).obj N)
        (pushforwardTopSection (Limits.pullback.snd f t) N n) := by
  let g := Limits.pullback.fst f t
  let q := Limits.pullback.snd f t
  let h : q ≫ t = g ≫ f := Limits.pullback.condition.symm
  let a := (eqToHom (Scheme.Hom.preimage_top g)).op
  let b := ((TopologicalSpace.Opens.map g.base).map
    (eqToHom (Scheme.Hom.preimage_top f))).op
  let c := (eqToHom (show
    q ⁻¹ᵁ (t ⁻¹ᵁ (⊤ : S.Opens)) =
        g ⁻¹ᵁ (f ⁻¹ᵁ (⊤ : S.Opens)) by
      rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage])).op
  let d := (eqToHom (Scheme.Hom.preimage_top q)).op
  let e := ((TopologicalSpace.Opens.map q.base).map
    (eqToHom (Scheme.Hom.preimage_top t))).op
  have happ :
      N.presheaf.map c (N.presheaf.map b (N.presheaf.map a n)) =
        N.presheaf.map e (N.presheaf.map d n) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply]
    exact ConcreteCategory.congr_hom
      (N.presheaf.congr_map (Subsingleton.elim _ _)) n
  change N.presheaf.map c (N.presheaf.map b (N.presheaf.map a n)) =
    N.presheaf.map e (N.presheaf.map d n)
  exact happ

/-- On global sections, cartesian pushforward base change sends the pullback
unit along the base map to the pullback unit along the cartesian projection. -/
theorem pullbackPushforwardBaseChange_app_top_pullbackUnit
    (M : X.Modules) (m : Γ(M, (⊤ : X.Opens))) :
    ((pullbackPushforwardBaseChange f t).app M).app (⊤ : T.Opens)
        (affinePullbackUnitTop t ((pushforward f).obj M)
          (pushforwardTopSection f M m)) =
      pushforwardTopSection (Limits.pullback.snd f t)
        ((pullback (Limits.pullback.fst f t)).obj M)
        (affinePullbackUnitTop (Limits.pullback.fst f t) M m) := by
  let g := Limits.pullback.fst f t
  let q := Limits.pullback.snd f t
  let N := (pullback g).obj M
  let mPush := pushforwardTopSection f M m
  let gUnit := affinePullbackUnitTop g M m
  let tUnit := affinePullbackUnitTop t ((pushforward f).obj M) mPush
  have happ := congrArg
    (fun k => k.val.app (.op (⊤ : S.Opens)))
    (pullbackPushforwardBaseChange_unit f t M)
  have hraw := ConcreteCategory.congr_hom happ mPush
  have hLeft :
      (((pushforward f).map
            ((pullbackPushforwardAdjunction g).unit.app M) ≫
          (pullbackPushforwardBaseChangePushSquare f t).app N).val.app
        (.op (⊤ : S.Opens))) mPush =
        pushforwardTopSection t ((pushforward q).obj N)
          (pushforwardTopSection q N gUnit) := by
    calc
      _ = ((pullbackPushforwardBaseChangePushSquare f t).app N).app
          (⊤ : S.Opens)
            (((pushforward f).map
              ((pullbackPushforwardAdjunction g).unit.app M)).app
                (⊤ : S.Opens) mPush) := rfl
      _ = ((pullbackPushforwardBaseChangePushSquare f t).app N).app
          (⊤ : S.Opens)
            (pushforwardTopSection f ((pushforward g).obj N)
              (((pullbackPushforwardAdjunction g).unit.app M).app
                (⊤ : X.Opens) m)) := by
          apply congrArg
          change ((pushforward f).map
              ((pullbackPushforwardAdjunction g).unit.app M)).app
                (⊤ : S.Opens) (pushforwardTopSection f M m) = _
          exact pushforwardMap_app_top_pushforwardTopSection f
            ((pullbackPushforwardAdjunction g).unit.app M) m
      _ = ((pullbackPushforwardBaseChangePushSquare f t).app N).app
          (⊤ : S.Opens)
            (pushforwardTopSection f ((pushforward g).obj N)
              (pushforwardTopSection g N gUnit)) := by
          apply congrArg
          apply congrArg
          exact (pushforwardTopSection_affinePullbackUnitTop g M m).symm
      _ = _ := pullbackPushforwardBaseChangePushSquare_app_top f t N gUnit
  have hRight :
      (((pullbackPushforwardAdjunction t).unit.app ((pushforward f).obj M) ≫
          (pushforward t).map
            ((pullbackPushforwardBaseChange f t).app M)).val.app
        (.op (⊤ : S.Opens))) mPush =
        pushforwardTopSection t ((pushforward q).obj N)
          (((pullbackPushforwardBaseChange f t).app M).app
            (⊤ : T.Opens) tUnit) := by
    calc
      _ = ((pushforward t).map
            ((pullbackPushforwardBaseChange f t).app M)).app
          (⊤ : S.Opens)
            (((pullbackPushforwardAdjunction t).unit.app
              ((pushforward f).obj M)).app (⊤ : S.Opens) mPush) := rfl
      _ = ((pushforward t).map
            ((pullbackPushforwardBaseChange f t).app M)).app
          (⊤ : S.Opens)
            (pushforwardTopSection t
              ((pullback t).obj ((pushforward f).obj M)) tUnit) := by
          apply congrArg
          exact (pushforwardTopSection_affinePullbackUnitTop t
            ((pushforward f).obj M) mPush).symm
      _ = _ := pushforwardMap_app_top_pushforwardTopSection t
        ((pullbackPushforwardBaseChange f t).app M) tUnit
  apply pushforwardTopSection_injective t ((pushforward q).obj N)
  exact hRight.symm.trans (hraw.symm.trans hLeft)

end AlgebraicGeometry.Scheme.Modules
