/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PullbackUnitMonoidal
import ModularCurves.Picard.DualPullback.OverRestriction
import ModularCurves.Picard.DualPullback.RestrictComp
import ModularCurves.Picard.DualPullback.UnitComp
import ModularCurves.Picard.DualPullback.UnitSquare

/-!
# Restricting local trivializations

This file proves coherence for restricting module trivializations through nested opens.
It compares the direct restriction-functor construction with the pullback construction,
and identifies both with restriction on the over-site. It also records compatibility with
sheaf duals.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u u₁ v₁

namespace ModularCurves.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem restrictOverTrivialization_comp_inv_app_apply
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z).inv.val.app T x =
      e.inv.val.app
        (.op ((Over.map V.hom).obj ((Over.map Z.hom).obj T.unop))) x := by
  rw [restrictOverTrivialization_inv_app_apply]
  erw [restrictOverTrivialization_inv_app_apply]

private theorem restrictOverTrivialization_direct_inv_app_apply
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z)).inv.val.app T x =
      e.inv.val.app
        (.op ((Over.map ((Over.map V.hom).obj Z).hom).obj T.unop)) x := by
  erw [restrictOverTrivialization_inv_app_apply]

private theorem trivialization_inv_overMap_assoc
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    e.inv.val.app
        (.op ((Over.map V.hom).obj ((Over.map Z.hom).obj T.unop))) x =
      e.inv.val.app
        (.op ((Over.map ((Over.map V.hom).obj Z).hom).obj T.unop)) x := by
  let A := (Over.map V.hom).obj ((Over.map Z.hom).obj T.unop)
  let B := (Over.map ((Over.map V.hom).obj Z).hom).obj T.unop
  let k : A ⟶ B := Over.homMk (𝟙 T.unop.left) (by
    dsimp only [A, B]
    simp only [Over.map_obj_left, Over.map_obj_hom]
    rw [Category.id_comp]
    exact (Category.assoc T.unop.hom Z.hom V.hom).symm)
  have hnat := PresheafOfModules.naturality_apply e.inv.val k.op x
  change e.inv.val.app (.op A) ((R.over U).obj.map k.op x) =
    (M.over U).val.map k.op (e.inv.val.app (.op B) x) at hnat
  have hk : k.left = 𝟙 T.unop.left := rfl
  change e.inv.val.app (.op A) (R.obj.map k.left.op x) =
    M.val.map k.left.op (e.inv.val.app (.op B) x) at hnat
  have hRmap : R.obj.map k.left.op x = x := by
    rw [hk]
    change R.obj.map (𝟙 (.op T.unop.left)) x = x
    rw [R.obj.map_id]
    rfl
  have hMmap : M.val.map k.left.op (e.inv.val.app (.op B) x) =
      e.inv.val.app (.op B) x := by
    rw [hk]
    change M.val.map (𝟙 (.op T.unop.left)) (e.inv.val.app (.op B) x) = _
    rw [M.val.map_id]
    rfl
  rw [hRmap, hMmap] at hnat
  simpa only [A, B] using hnat

private theorem restrictOverTrivialization_comp_inv_eq
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z).inv.val.app T x =
      (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z)).inv.val.app T x := by
  rw [restrictOverTrivialization_comp_inv_app_apply]
  rw [trivialization_inv_overMap_assoc]
  exact (restrictOverTrivialization_direct_inv_app_apply
    R M U e V Z T x).symm

theorem restrictOverTrivialization_comp
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) :
    restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z =
      restrictOverTrivialization R M U e ((Over.map V.hom).obj Z) := by
  apply Iso.ext
  rw [← Iso.inv_eq_inv]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact restrictOverTrivialization_comp_inv_eq R M U e V Z T x

theorem restrictOverTrivialization_dualOverIsoOfIso
    [∀ U, IsMulCommutative (R.obj.obj U)]
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) :
    restrictOverTrivialization R (dual R M) U
        (dualOverIsoOfIso R M U e) V =
      dualOverIsoOfIso R M V.left
        (restrictOverTrivialization R M U e V) := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro alpha
  change dualTrivializationLinearEquiv R M Z.unop.left
      (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z.unop)) alpha =
    dualTrivializationLinearEquiv R M Z.unop.left
      (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z.unop) alpha
  rw [restrictOverTrivialization_comp R M U e V Z.unop]

end ModularCurves.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- Transport a trivialization across a commutative square. -/
noncomputable def pullbackSquareTrivialization
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules)
    (t : (pullback d).obj M ≅ unitObj C) :
    (pullback a).obj ((pullback b).obj M) ≅ unitObj A :=
  (pullbackSquareIso a b c d h).app M ≪≫
    (pullback c).mapIso t ≪≫ pullbackUnitIso c

/-- A square-transported trivialization factors through the direct pullback along the
composite map. -/
theorem pullbackSquareTrivialization_factor
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (w : A ⟶ D) (h : a ≫ b = c ≫ d) (hw : c ≫ d = w)
    (M : D.Modules) (t : (pullback d).obj M ≅ unitObj C) :
    (pullbackSquareTrivialization a b c d h M t).hom =
      ((((pullbackComp a b).app M) ≪≫
          ((pullbackCongr (h.trans hw)).app M)).hom) ≫
        (((pullbackCongr hw.symm).app M) ≪≫
          ((pullbackComp c d).app M).symm ≪≫
          (pullback c).mapIso t ≪≫ pullbackUnitIso c).hom := by
  simp only [pullbackSquareTrivialization, pullbackSquareIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  let P := (pullbackComp a b).app M
  let R := (pullbackComp c d).app M
  let Q := (pullbackCongr h).app M
  let Qw := (pullbackCongr (h.trans hw)).app M
  let Qback := (pullbackCongr hw.symm).app M
  let tail := R.inv ≫ (pullback c).map t.hom ≫
    (pullbackUnitIso c).hom
  change P.hom ≫ Q.hom ≫ tail =
    (P.hom ≫ Qw.hom) ≫ Qback.hom ≫ tail
  have htrans := pullbackCongr_trans (h.trans hw) hw.symm
  have hp : (h.trans hw).trans hw.symm = h := Subsingleton.elim _ _
  rw [hp] at htrans
  have htransApp := congrArg (fun z => z.hom.app M) htrans
  change Qw.hom ≫ Qback.hom = Q.hom at htransApp
  rw [← htransApp]
  simp only [Category.assoc]

/-- If the lower leg of a square is an inclusion of opens, the residual factor in a
square-transported trivialization is the usual restricted trivialization. -/
theorem pullbackSquareTrivialization_tail_restrict
    {X : Scheme.{u}} {N : X.Modules} {U W : X.Opens}
    (hWU : W ≤ U) (c : W.toScheme ⟶ U.toScheme)
    (hc : c = X.homOfLE hWU) (hw : c ≫ U.ι = W.ι)
    (t : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    (((pullbackCongr hw.symm).app N) ≪≫
          ((pullbackComp c U.ι).app N).symm ≪≫
          (pullback c).mapIso t ≪≫ pullbackUnitIso c).hom =
      (restrictTrivialization hWU t).hom := by
  subst c
  rfl

private theorem pullbackSquareTrivialization_factor_with
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (w : A ⟶ D) (h : a ≫ b = c ≫ d) (hw : c ≫ d = w)
    (hTo : a ≫ b = w) (M : D.Modules)
    (t : (pullback d).obj M ≅ unitObj C) :
    (pullbackSquareTrivialization a b c d h M t).hom =
      ((((pullbackComp a b).app M) ≪≫
          ((pullbackCongr hTo).app M)).hom) ≫
        (((pullbackCongr hw.symm).app M) ≪≫
          ((pullbackComp c d).app M).symm ≪≫
          (pullback c).mapIso t ≪≫ pullbackUnitIso c).hom := by
  have hfactor := pullbackSquareTrivialization_factor
    a b c d w h hw M t
  have hp : h.trans hw = hTo := Subsingleton.elim _ _
  rw [hp] at hfactor
  exact hfactor

private theorem pullbackComp_four_congr_trans_app_with
    {A B C D E : Scheme.{u}}
    (q : A ⟶ B) (p : B ⟶ C) (d : C ⟶ D) (g : D ⟶ E)
    (s : B ⟶ D) (hp : p ≫ d = s) (w : A ⟶ E)
    (h₁ : (q ≫ p) ≫ (d ≫ g) = (q ≫ s) ≫ g)
    (h₂ : (q ≫ s) ≫ g = w)
    (hTo : (q ≫ p) ≫ (d ≫ g) = w) (N : E.Modules) :
    (pullbackComp q p).hom.app
          ((pullback d).obj ((pullback g).obj N)) ≫
        (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N) ≫
        ((((pullbackComp (q ≫ p) (d ≫ g)).app N) ≪≫
          ((pullbackCongr hTo).app N)).hom) =
      (pullback q).map
          ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
            ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
        (pullbackComp q s).hom.app ((pullback g).obj N) ≫
      (pullbackComp (q ≫ s) g).hom.app N ≫
        ((pullbackCongr h₂).app N).hom := by
  have hnorm := pullbackComp_four_congr_trans_app
    q p d g s hp w h₁ h₂ N
  have hproof : h₁.trans h₂ = hTo := Subsingleton.elim _ _
  rw [hproof] at hnorm
  exact hnorm

/-- A fourfold pullback of a square-transported trivialization normalizes to the common
pullback followed by the ordinary restriction of the original trivialization. -/
theorem pullbackSquareTrivialization_four_restrict
    {X A B D : Scheme.{u}} {N : X.Modules} {U W : X.Opens}
    (hWU : W ≤ U) (q : W.toScheme ⟶ A) (p : A ⟶ B)
    (d : B ⟶ D) (g : D ⟶ X) (s : A ⟶ D)
    (c : W.toScheme ⟶ U.toScheme) (hp : p ≫ d = s)
    (hSquare : (q ≫ p) ≫ (d ≫ g) = c ≫ U.ι)
    (hc : c = X.homOfLE hWU)
    (hSource : (q ≫ p) ≫ (d ≫ g) = (q ≫ s) ≫ g)
    (hCommon : (q ≫ s) ≫ g = W.ι)
    (t : (pullback U.ι).obj N ≅ unitObj U.toScheme) :
    (pullbackComp q p).hom.app
          ((pullback d).obj ((pullback g).obj N)) ≫
      (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N) ≫
        (pullbackSquareTrivialization (q ≫ p) (d ≫ g)
          c U.ι hSquare N t).hom =
    (pullback q).map
          ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
            ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
      (pullbackComp q s).hom.app ((pullback g).obj N) ≫
      (pullbackComp (q ≫ s) g).hom.app N ≫
      ((pullbackCongr hCommon).app N).hom ≫
      (restrictTrivialization hWU t).hom := by
  let hw : c ≫ U.ι = W.ι :=
    (congrArg (· ≫ U.ι) hc).trans (X.homOfLE_ι hWU)
  let hTo := hSource.trans hCommon
  have hfactor := pullbackSquareTrivialization_factor_with
    (q ≫ p) (d ≫ g) c U.ι W.ι hSquare hw hTo N t
  have htail := pullbackSquareTrivialization_tail_restrict
    hWU c hc hw t
  have hnorm := pullbackComp_four_congr_trans_app_with
    q p d g s hp W.ι hSource hCommon hTo N
  rw [hfactor]
  rw [htail]
  exact (reassoc_of% hnorm) (restrictTrivialization hWU t).hom

private theorem transition_of_normalized
    {C : Type u} [Category C] {A B C' D E : C}
    (L₁ : A ≅ B) (L₂ : C' ≅ B) (K : B ⟶ D)
    (T₁ T₂ : D ≅ E) (scalar : E ⟶ E)
    (hscalar : T₁.inv ≫ T₂.hom = scalar) :
    (L₁.hom ≫ K ≫ T₁.hom) ≫ scalar =
      (L₁.hom ≫ L₂.inv) ≫ (L₂.hom ≫ K ≫ T₂.hom) := by
  rw [← hscalar]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- Two square-transported trivializations with a common lower composite differ by the
transition scalar of their ordinary restrictions. -/
theorem pullbackSquareTrivialization_two_transition
    {X A B₁ B₂ D : Scheme.{u}} {N : X.Modules}
    {U₁ U₂ W : X.Opens} (hWU₁ : W ≤ U₁) (hWU₂ : W ≤ U₂)
    (q : W.toScheme ⟶ A) (p₁ : A ⟶ B₁) (p₂ : A ⟶ B₂)
    (d₁ : B₁ ⟶ D) (d₂ : B₂ ⟶ D) (g : D ⟶ X) (s : A ⟶ D)
    (c₁ : W.toScheme ⟶ U₁.toScheme) (c₂ : W.toScheme ⟶ U₂.toScheme)
    (hp₁ : p₁ ≫ d₁ = s) (hp₂ : p₂ ≫ d₂ = s)
    (hSquare₁ : (q ≫ p₁) ≫ (d₁ ≫ g) = c₁ ≫ U₁.ι)
    (hSquare₂ : (q ≫ p₂) ≫ (d₂ ≫ g) = c₂ ≫ U₂.ι)
    (hc₁ : c₁ = X.homOfLE hWU₁) (hc₂ : c₂ = X.homOfLE hWU₂)
    (hSource₁ : (q ≫ p₁) ≫ (d₁ ≫ g) = (q ≫ s) ≫ g)
    (hSource₂ : (q ≫ p₂) ≫ (d₂ ≫ g) = (q ≫ s) ≫ g)
    (hCommon : (q ≫ s) ≫ g = W.ι)
    (t₁ : (pullback U₁.ι).obj N ≅ unitObj U₁.toScheme)
    (t₂ : (pullback U₂.ι).obj N ≅ unitObj U₂.toScheme)
    (scalar : unitObj W.toScheme ⟶ unitObj W.toScheme)
    (hscalar : (restrictTrivialization hWU₁ t₁).inv ≫
      (restrictTrivialization hWU₂ t₂).hom = scalar) :
    ((pullbackComp q p₁).hom.app
            ((pullback d₁).obj ((pullback g).obj N)) ≫
        (pullback (q ≫ p₁)).map ((pullbackComp d₁ g).hom.app N) ≫
          (pullbackSquareTrivialization (q ≫ p₁) (d₁ ≫ g)
            c₁ U₁.ι hSquare₁ N t₁).hom) ≫ scalar =
      ((pullback q).map
            ((((pullbackComp p₁ d₁).app ((pullback g).obj N)) ≪≫
              ((pullbackCongr hp₁).app ((pullback g).obj N))).hom) ≫
          (pullback q).map
            ((((pullbackComp p₂ d₂).app ((pullback g).obj N)) ≪≫
              ((pullbackCongr hp₂).app ((pullback g).obj N))).inv)) ≫
        ((pullbackComp q p₂).hom.app
              ((pullback d₂).obj ((pullback g).obj N)) ≫
          (pullback (q ≫ p₂)).map ((pullbackComp d₂ g).hom.app N) ≫
            (pullbackSquareTrivialization (q ≫ p₂) (d₂ ≫ g)
              c₂ U₂.ι hSquare₂ N t₂).hom) := by
  let L₁ := ((pullbackComp p₁ d₁).app ((pullback g).obj N)) ≪≫
    ((pullbackCongr hp₁).app ((pullback g).obj N))
  let L₂ := ((pullbackComp p₂ d₂).app ((pullback g).obj N)) ≪≫
    ((pullbackCongr hp₂).app ((pullback g).obj N))
  let pre := (pullback q).map L₁.hom ≫ (pullback q).map L₂.inv
  let Q₁ := (pullback q).mapIso L₁
  let Q₂ := (pullback q).mapIso L₂
  let K := (pullbackComp q s).hom.app ((pullback g).obj N) ≫
    (pullbackComp (q ≫ s) g).hom.app N ≫ ((pullbackCongr hCommon).app N).hom
  let T₁ := restrictTrivialization hWU₁ t₁
  let T₂ := restrictTrivialization hWU₂ t₂
  have hleft := pullbackSquareTrivialization_four_restrict hWU₁ q p₁ d₁ g s c₁
    hp₁ hSquare₁ hc₁ hSource₁ hCommon t₁
  have hright := pullbackSquareTrivialization_four_restrict hWU₂ q p₂ d₂ g s c₂
    hp₂ hSquare₂ hc₂ hSource₂ hCommon t₂
  refine (congrArg (· ≫ scalar) hleft).trans ?_
  refine Eq.trans ?_ (congrArg (pre ≫ ·) hright.symm)
  change (Q₁.hom ≫ K ≫ T₁.hom) ≫ scalar =
    (Q₁.hom ≫ Q₂.inv) ≫ (Q₂.hom ≫ K ≫ T₂.hom)
  exact transition_of_normalized Q₁ Q₂ K T₁ T₂ scalar hscalar

/-- Transporting a trivialization across two vertically composable squares agrees with
transport across the outer square. -/
theorem pullbackSquareTrivialization_vcomp
    {A B C D E F : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (q : D ⟶ F) (e : C ⟶ E) (r : E ⟶ F)
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ q = e ≫ r)
    (M : F.Modules) (t : (pullback r).obj M ≅ unitObj E) :
    let hOuter : a ≫ (b ≫ q) = (c ≫ e) ≫ r :=
      (Category.assoc a b q).symm.trans
        ((congrArg (· ≫ q) h₁).trans
          ((Category.assoc c d q).trans
            ((congrArg (c ≫ ·) h₂).trans (Category.assoc c e r).symm)))
    (pullbackSquareTrivialization a b c d h₁ ((pullback q).obj M)
        (pullbackSquareTrivialization d q e r h₂ M t)).hom =
      (pullback a).map ((pullbackComp b q).hom.app M) ≫
        (pullbackSquareTrivialization a (b ≫ q) (c ≫ e) r hOuter M t).hom := by
  dsimp only
  let hOuter : a ≫ (b ≫ q) = (c ≫ e) ≫ r :=
    (Category.assoc a b q).symm.trans
      ((congrArg (· ≫ q) h₁).trans
        ((Category.assoc c d q).trans
          ((congrArg (c ≫ ·) h₂).trans (Category.assoc c e r).symm)))
  let s₁ := pullbackSquareIso a b c d h₁
  let s₂ := pullbackSquareIso d q e r h₂
  let sOuter := pullbackSquareIso a (b ≫ q) (c ≫ e) r hOuter
  let pRight := (pullbackComp c e).app (unitObj E)
  have hsquare := pullbackSquareIso_vcomp_app
    a b c d q e r h₁ h₂ M
  have hnat := (pullbackComp c e).inv.naturality t.hom
  rw [Functor.comp_map] at hnat
  have hunit := ModularCurves.pullbackComp_inv_unitPairLow c e
  simp only [pullbackSquareTrivialization, Iso.trans_hom,
    Functor.mapIso_hom]
  rw [Functor.map_comp, Functor.map_comp]
  change
    s₁.hom.app ((pullback q).obj M) ≫
          (pullback c).map (s₂.hom.app M) ≫
        (pullback c).map ((pullback e).map t.hom) ≫
      (pullback c).map (pullbackUnitIso e).hom ≫
        (pullbackUnitIso c).hom =
      (pullback a).map ((pullbackComp b q).hom.app M) ≫
          sOuter.hom.app M ≫
        (pullback (c ≫ e)).map t.hom ≫
      (pullbackUnitIso (c ≫ e)).hom
  change s₁.hom.app ((pullback q).obj M) ≫
      (pullback c).map (s₂.hom.app M) =
        (pullback a).map ((pullbackComp b q).hom.app M) ≫
          sOuter.hom.app M ≫
            (pullbackComp c e).inv.app ((pullback r).obj M) at hsquare
  have hnat' : (pullbackComp c e).inv.app ((pullback r).obj M) ≫
      (pullback c).map ((pullback e).map t.hom) =
        (pullback (c ≫ e)).map t.hom ≫ pRight.inv := by
    exact hnat.symm
  change pRight.inv ≫ (pullback c).map (pullbackUnitIso e).hom ≫
      (pullbackUnitIso c).hom = (pullbackUnitIso (c ≫ e)).hom at hunit
  have htail :
      (sOuter.hom.app M ≫
            (pullbackComp c e).inv.app ((pullback r).obj M)) ≫
          (pullback c).map ((pullback e).map t.hom) ≫
        (pullback c).map (pullbackUnitIso e).hom ≫
          (pullbackUnitIso c).hom =
        sOuter.hom.app M ≫
          (pullback (c ≫ e)).map t.hom ≫
            (pullbackUnitIso (c ≫ e)).hom := by
    calc
      _ = sOuter.hom.app M ≫
          ((pullbackComp c e).inv.app ((pullback r).obj M) ≫
            (pullback c).map ((pullback e).map t.hom)) ≫
          (pullback c).map (pullbackUnitIso e).hom ≫
            (pullbackUnitIso c).hom := by
              simp only [Category.assoc]
      _ = sOuter.hom.app M ≫
          ((pullback (c ≫ e)).map t.hom ≫ pRight.inv) ≫
          (pullback c).map (pullbackUnitIso e).hom ≫
            (pullbackUnitIso c).hom :=
              congrArg
                (fun z => sOuter.hom.app M ≫ z ≫
                  (pullback c).map (pullbackUnitIso e).hom ≫
                    (pullbackUnitIso c).hom) hnat'
      _ = sOuter.hom.app M ≫
          (pullback (c ≫ e)).map t.hom ≫
            (pRight.inv ≫
              (pullback c).map (pullbackUnitIso e).hom ≫
                (pullbackUnitIso c).hom) := by
                  simp only [Category.assoc]
      _ = sOuter.hom.app M ≫
          (pullback (c ≫ e)).map t.hom ≫
            (pullbackUnitIso (c ≫ e)).hom :=
              congrArg
                (fun z => sOuter.hom.app M ≫
                  (pullback (c ≫ e)).map t.hom ≫ z) hunit
  conv_lhs =>
    rw [← Category.assoc, hsquare]
  calc
    _ = (pullback a).map ((pullbackComp b q).hom.app M) ≫
        ((sOuter.hom.app M ≫
              (pullbackComp c e).inv.app ((pullback r).obj M)) ≫
            (pullback c).map ((pullback e).map t.hom) ≫
          (pullback c).map (pullbackUnitIso e).hom ≫
            (pullbackUnitIso c).hom) := by
              exact
                (Category.assoc
                    ((pullback a).map ((pullbackComp b q).hom.app M))
                    (sOuter.hom.app M ≫
                      (pullbackComp c e).inv.app ((pullback r).obj M))
                    ((pullback c).map ((pullback e).map t.hom) ≫
                      (pullback c).map (pullbackUnitIso e).hom ≫
                        (pullbackUnitIso c).hom)).trans
                  (congrArg
                    (fun z =>
                      (pullback a).map ((pullbackComp b q).hom.app M) ≫ z)
                    (Category.assoc
                      (sOuter.hom.app M)
                      ((pullbackComp c e).inv.app ((pullback r).obj M))
                      ((pullback c).map ((pullback e).map t.hom) ≫
                        (pullback c).map (pullbackUnitIso e).hom ≫
                          (pullbackUnitIso c).hom)))
    _ = (pullback a).map ((pullbackComp b q).hom.app M) ≫
        (sOuter.hom.app M ≫
          (pullback (c ≫ e)).map t.hom ≫
            (pullbackUnitIso (c ≫ e)).hom) :=
      congrArg (fun z => (pullback a).map
        ((pullbackComp b q).hom.app M) ≫ z) htail
    _ = _ := rfl

/-- After pulling a unit transition through an isomorphism, flattening the target pullback
cancels the trailing inverse unit comparison. -/
theorem pullback_unitTransition_comp_flattenRight
    {X Y Z W : Scheme.{u}} (p₁ : X ⟶ Y) (p₂ : X ⟶ Z)
    (q : X ≅ W) (τ : unitObj X ≅ unitObj X) :
    (pullback q.inv).map
          ((pullbackUnitIso p₁).hom ≫ τ.hom ≫ (pullbackUnitIso p₂).inv) ≫
        (pullback q.inv).map (pullbackUnitIso p₂).hom ≫
      (pullbackUnitIso q.inv).hom =
    (pullback q.inv).map (pullbackUnitIso p₁).hom ≫
        (pullback q.inv).map τ.hom ≫
      (pullbackUnitIso q.inv).hom := by
  rw [Functor.map_comp, Functor.map_comp]
  let P := (pullback q.inv).mapIso (pullbackUnitIso p₂)
  have hP := P.inv_hom_id_assoc (pullbackUnitIso q.inv).hom
  exact congrArg
    (fun z =>
      (pullback q.inv).map (pullbackUnitIso p₁).hom ≫
        (pullback q.inv).map τ.hom ≫ z) hP

/-- Flattening two successive pullbacks of a trivializing morphism agrees with flattening
the pullback along the composite. -/
theorem pullbackTrivialization_comp_hom
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (t : M ⟶ unitObj Z) :
    (pullback f).map ((pullback g).map t) ≫
          (pullback f).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso f).hom =
      (pullbackComp f g).hom.app M ≫
          (pullback (f ≫ g)).map t ≫
        (pullbackUnitIso (f ≫ g)).hom := by
  let P := (pullbackComp f g).app M
  let Q := (pullbackComp f g).app (unitObj Z)
  have hnat := (pullbackComp f g).hom.naturality t
  have hunit := ModularCurves.pullbackUnitIso_compLow f g
  change _ ≫ _ ≫ _ = P.hom ≫ _ ≫ _
  change Q.hom ≫ _ = _ at hunit
  calc
    _ = (pullback f).map ((pullback g).map t) ≫
        (Q.hom ≫ (pullbackUnitIso (f ≫ g)).hom) :=
      congrArg (fun z => (pullback f).map ((pullback g).map t) ≫ z)
        hunit.symm
    _ = ((pullback f).map ((pullback g).map t) ≫ Q.hom) ≫
        (pullbackUnitIso (f ≫ g)).hom := (Category.assoc _ _ _).symm
    _ = (P.hom ≫ (pullback (f ≫ g)).map t) ≫
        (pullbackUnitIso (f ≫ g)).hom :=
      congrArg (fun z => z ≫ (pullbackUnitIso (f ≫ g)).hom) hnat
    _ = _ := Category.assoc _ _ _

/-- Transport across a reflexive square is ordinary pullback of the trivialization. -/
theorem pullbackSquareTrivialization_refl_hom
    {A B D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (M : D.Modules) (t : (pullback b).obj M ≅ unitObj B) :
    (pullbackSquareTrivialization a b a b rfl M t).hom =
      (pullback a).map t.hom ≫ (pullbackUnitIso a).hom := by
  let P := (pullbackComp a b).app M
  have hcongr : (pullbackCongr
      (rfl : a ≫ b = a ≫ b)).hom.app M = 𝟙 _ := rfl
  have hsquare :
      ((pullbackSquareIso a b a b rfl).app M).hom = 𝟙 _ := by
    change P.hom ≫ _ ≫ P.inv = 𝟙 _
    calc
      _ = P.hom ≫ 𝟙 _ ≫ P.inv :=
        congrArg (fun z => P.hom ≫ z ≫ P.inv) hcongr
      _ = P.hom ≫ (𝟙 _ ≫ P.inv) := Category.assoc _ _ _
      _ = P.hom ≫ P.inv := congrArg (fun z => P.hom ≫ z)
        (Category.id_comp P.inv)
      _ = 𝟙 _ := P.hom_inv_id
  let T := (pullback a).map t.hom ≫ (pullbackUnitIso a).hom
  change ((pullbackSquareIso a b a b rfl).app M).hom ≫ T = T
  exact (congrArg (fun z => z ≫ T) hsquare).trans (Category.id_comp T)

/-- Pulling a square-transported trivialization back along a map is transport across the
precomposed outer square. -/
theorem pullbackSquareTrivialization_precomp_hom
    {A' A B C D : Scheme.{u}} (r : A' ⟶ A)
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules)
    (t : (pullback d).obj M ≅ unitObj C) :
    let hOuter : r ≫ (a ≫ b) = (r ≫ c) ≫ d :=
      (Category.assoc r a b).symm.trans
        ((congrArg (r ≫ ·) h).trans (Category.assoc r c d))
    (pullback r).map
          (pullbackSquareTrivialization a b c d h M t).hom ≫
        (pullbackUnitIso r).hom =
      (pullback r).map ((pullbackComp a b).hom.app M) ≫
        (pullbackSquareTrivialization r (a ≫ b) (r ≫ c) d
          hOuter M t).hom := by
  dsimp only
  have hv := pullbackSquareTrivialization_vcomp
    r a r a b c d rfl h M t
  rw [pullbackSquareTrivialization_refl_hom] at hv
  exact hv

/-- The precomposition rule for a square-transported trivialization, with two successive
pullbacks left unflattened on the source. -/
theorem pullbackSquareTrivialization_comp_precomp_hom
    {A'' A' A B C D : Scheme.{u}} (f : A'' ⟶ A') (r : A' ⟶ A)
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) (M : D.Modules)
    (t : (pullback d).obj M ≅ unitObj C) :
    let hOuter : (f ≫ r) ≫ (a ≫ b) = ((f ≫ r) ≫ c) ≫ d :=
      (Category.assoc (f ≫ r) a b).symm.trans
        ((congrArg ((f ≫ r) ≫ ·) h).trans
          (Category.assoc (f ≫ r) c d))
    (pullback f).map ((pullback r).map
          (pullbackSquareTrivialization a b c d h M t).hom) ≫
        (pullback f).map (pullbackUnitIso r).hom ≫
      (pullbackUnitIso f).hom =
    (pullbackComp f r).hom.app
          ((pullback a).obj ((pullback b).obj M)) ≫
      (pullback (f ≫ r)).map ((pullbackComp a b).hom.app M) ≫
        (pullbackSquareTrivialization (f ≫ r) (a ≫ b)
          ((f ≫ r) ≫ c) d hOuter M t).hom := by
  dsimp only
  have hcomp := pullbackTrivialization_comp_hom f r
    (pullbackSquareTrivialization a b c d h M t).hom
  have hpre := pullbackSquareTrivialization_precomp_hom
    (f ≫ r) a b c d h M t
  calc
    _ = (pullbackComp f r).hom.app
          ((pullback a).obj ((pullback b).obj M)) ≫
        (pullback (f ≫ r)).map
            (pullbackSquareTrivialization a b c d h M t).hom ≫
          (pullbackUnitIso (f ≫ r)).hom := hcomp
    _ = (pullbackComp f r).hom.app
          ((pullback a).obj ((pullback b).obj M)) ≫
        ((pullback (f ≫ r)).map ((pullbackComp a b).hom.app M) ≫
          (pullbackSquareTrivialization (f ≫ r) (a ≫ b)
            ((f ≫ r) ≫ c) d _ M t).hom) :=
      congrArg
        (fun z => (pullbackComp f r).hom.app
          ((pullback a).obj ((pullback b).obj M)) ≫ z) hpre
    _ = _ := Category.assoc _ _ _

private theorem cancel_iso_inv_right
    {D : Type u₁} [Category.{v₁} D]
    {A B C : D} (e : A ≅ B) (p : C ⟶ B) (q : C ⟶ A)
    (h : p ≫ e.inv = q) : p = q ≫ e.hom :=
  e.comp_inv_eq.mp h

noncomputable def restrictOpenTrivialization
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.restrict V.ι ≅ unitObj V.toScheme :=
  (restrictOpenCompIso (homOfLE hVU)).app M ≪≫
    (restrictFunctor (X.homOfLE hVU)).mapIso e ≪≫
    restrictUnitIso (X.homOfLE hVU)

noncomputable def restrictOpenTrivializationPullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.restrict V.ι ≅ unitObj V.toScheme :=
  (restrictFunctorIsoPullback V.ι).app M ≪≫
    restrictTrivialization hVU
      ((restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e)

theorem restrictFunctorIsoPullback_comp_inv_cancel
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : C.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫
        (pullbackComp f g).inv.app M ≫
        (pullback f).map ((restrictFunctorIsoPullback g).inv.app M) =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctorIsoPullback f).hom.app
          ((restrictFunctor g).obj M) := by
  let eP := (pullbackComp f g).app M
  let eG := (pullback f).mapIso ((restrictFunctorIsoPullback g).app M)
  let eF := (restrictFunctorIsoPullback f).app ((restrictFunctor g).obj M)
  let eC := (restrictFunctorIsoPullback (f ≫ g)).app M
  let eR := (restrictFunctorComp f g).app M
  have hci := restrictFunctorIsoPullback_comp_inv f g M
  change eP.inv ≫ eG.inv ≫ eF.inv = eC.inv ≫ eR.hom at hci
  have hci' : (eP.inv ≫ eG.inv) ≫ eF.inv = eC.inv ≫ eR.hom :=
    (Category.assoc eP.inv eG.inv eF.inv).trans hci
  have hPG : eP.inv ≫ eG.inv = eC.inv ≫ eR.hom ≫ eF.hom :=
    cancel_iso_inv_right eF (eP.inv ≫ eG.inv)
      (eC.inv ≫ eR.hom) hci'
  change eC.hom ≫ eP.inv ≫ eG.inv = eR.hom ≫ eF.hom
  calc
    eC.hom ≫ eP.inv ≫ eG.inv =
        eC.hom ≫ (eP.inv ≫ eG.inv) := Category.assoc _ _ _
    _ = eC.hom ≫ (eC.inv ≫ eR.hom ≫ eF.hom) :=
      congrArg (fun q => eC.hom ≫ q) hPG
    _ = eR.hom ≫ eF.hom := eC.hom_inv_id_assoc _

theorem restrictOpenTrivialization_hom_eq_pullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    (restrictOpenTrivialization hVU e).hom =
      (restrictOpenTrivializationPullback hVU e).hom := by
  simp only [restrictOpenTrivialization,
    restrictOpenTrivializationPullback, restrictTrivialization,
    restrictOpenCompIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  let j := X.homOfLE hVU
  let hcomp := X.homOfLE_ι hVU
  have hc := restrictFunctorIsoPullback_congr hcomp.symm M
  have hcore := restrictFunctorIsoPullback_comp_inv_cancel j U.ι M
  have hnat := (restrictFunctorIsoPullback j).hom.naturality e.hom
  dsimp only [j] at hc hcore hnat
  rw [Functor.map_comp]
  let a := (restrictFunctorCongr hcomp.symm).hom.app M
  let b := (restrictFunctorComp (X.homOfLE hVU) U.ι).hom.app M
  let c := (restrictFunctor (X.homOfLE hVU)).map e.hom
  let d := (restrictUnitIso (X.homOfLE hVU)).hom
  let A := (restrictFunctorIsoPullback V.ι).hom.app M
  let P := (pullbackCongr hcomp.symm).hom.app M
  let Q := (pullbackComp (X.homOfLE hVU) U.ι).inv.app M
  let T := (pullback (X.homOfLE hVU)).map
    ((restrictFunctorIsoPullback U.ι).inv.app M)
  let s := (pullback (X.homOfLE hVU)).map e.hom
  let t := (pullbackUnitIso (X.homOfLE hVU)).hom
  let E := (restrictFunctorIsoPullback (X.homOfLE hVU ≫ U.ι)).hom.app M
  let J := (restrictFunctorIsoPullback (X.homOfLE hVU)).hom.app
    ((restrictFunctor U.ι).obj M)
  let JO := (restrictFunctorIsoPullback (X.homOfLE hVU)).hom.app
    (unitObj U.toScheme)
  change a ≫ b ≫ c ≫ d = A ≫ P ≫ Q ≫ T ≫ s ≫ t
  change a ≫ E = A ≫ P at hc
  change E ≫ Q ≫ T = b ≫ J at hcore
  change c ≫ JO = J ≫ s at hnat
  have hprefix : A ≫ P ≫ Q ≫ T = a ≫ b ≫ J := by
    calc
      A ≫ P ≫ Q ≫ T = (A ≫ P) ≫ (Q ≫ T) := by
        simp only [Category.assoc]
      _ = (a ≫ E) ≫ (Q ≫ T) :=
        congrArg (fun k => k ≫ (Q ≫ T)) hc.symm
      _ = a ≫ (E ≫ Q ≫ T) := by simp only [Category.assoc]
      _ = a ≫ (b ≫ J) := congrArg (fun k => a ≫ k) hcore
      _ = a ≫ b ≫ J := rfl
  have hunit : JO ≫ t = d :=
    restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG
      (X.homOfLE hVU)
  symm
  calc
    A ≫ P ≫ Q ≫ T ≫ s ≫ t = (A ≫ P ≫ Q ≫ T) ≫ (s ≫ t) := by
      simp only [Category.assoc]
    _ = (a ≫ b ≫ J) ≫ (s ≫ t) :=
      congrArg (fun k => k ≫ (s ≫ t)) hprefix
    _ = a ≫ b ≫ (J ≫ s) ≫ t := by simp only [Category.assoc]
    _ = a ≫ b ≫ (c ≫ JO) ≫ t :=
      congrArg (fun k => a ≫ b ≫ k ≫ t) hnat.symm
    _ = a ≫ b ≫ c ≫ (JO ≫ t) := by simp only [Category.assoc]
    _ = a ≫ b ≫ c ≫ d := congrArg (fun k => a ≫ b ≫ c ≫ k) hunit

theorem restrictOpenTrivialization_eq_pullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    restrictOpenTrivialization hVU e =
      restrictOpenTrivializationPullback hVU e := by
  apply Iso.ext
  exact restrictOpenTrivialization_hom_eq_pullback hVU e

theorem overTrivializationOfRestrictOpenTrivialization
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    overTrivializationOfRestrictIso M V
        (restrictOpenTrivialization hVU e) =
      ModularCurves.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U (overTrivializationOfRestrictIso M U e)
          (Over.mk (homOfLE hVU)) := by
  apply Iso.ext
  let G := (overEquiv V).functor
  apply G.map_injective
  simp only [overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom]
  let i : V ⟶ U := homOfLE hVU
  have hres := overEquiv_map_dualRestrict M i
    (overTrivializationOfRestrictIso M U e).hom
  change _ = G.map (ModularCurves.SheafOfModules.dualRestrict
    X.ringCatSheaf M i.op (overTrivializationOfRestrictIso M U e).hom)
  rw [hres]
  simp only [overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Functor.map_comp,
    Iso.trans_hom, restrictOpenTrivialization, Category.assoc]
  slice_rhs 1 2 => erw [overRestrictModuleIso_comp_overFunctorEquiv]
  rw [overRestrictUnitIso_eq_restrictUnitIsoP]
  rfl

/-- The passage from an open-subscheme trivialization to its over-site trivialization is
injective. -/
theorem overTrivializationOfRestrictIso_injective
    {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    {e g : M.restrict U.ι ≅ unitObj U.toScheme}
    (h : overTrivializationOfRestrictIso M U e =
      overTrivializationOfRestrictIso M U g) :
    e = g := by
  apply Iso.ext
  have hhom := congrArg Iso.hom h
  let G := (overEquiv U).functor
  have hmap := congrArg (fun q ↦ G.map q) hhom
  simp only [overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom] at hmap
  let F := overFunctorEquiv U
  let C := U.sheafOfModulesEquivOverUnit X.ringCatSheaf
  change F.hom.app M ≫ e.hom ≫ C.inv =
    F.hom.app M ≫ g.hom ≫ C.inv at hmap
  apply (cancel_epi (F.hom.app M)).1
  apply (cancel_mono C.inv).1
  exact hmap

/-- Restricting an open-subscheme trivialization through two nested opens agrees with direct
restriction. -/
theorem restrictOpenTrivialization_comp
    {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    restrictOpenTrivialization hWV (restrictOpenTrivialization hVU e) =
      restrictOpenTrivialization (hWV.trans hVU) e := by
  apply overTrivializationOfRestrictIso_injective
  rw [overTrivializationOfRestrictOpenTrivialization hWV]
  rw [overTrivializationOfRestrictOpenTrivialization hVU]
  rw [overTrivializationOfRestrictOpenTrivialization (hWV.trans hVU)]
  let eU := overTrivializationOfRestrictIso M U e
  let VU : Over U := Over.mk (homOfLE hVU)
  let WV : Over VU.left := Over.mk (homOfLE hWV)
  let WU : Over U := Over.mk (homOfLE (hWV.trans hVU))
  have hcomp := ModularCurves.SheafOfModules.restrictOverTrivialization_comp
    X.ringCatSheaf M U eU VU WV
  change ModularCurves.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M VU.left
        (ModularCurves.SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M U eU VU) WV =
    ModularCurves.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U eU WU
  calc
    _ = ModularCurves.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U eU ((Over.map VU.hom).obj WV) := hcomp
    _ = ModularCurves.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U eU WU := by
      congr 1

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

/-- Restriction of over-site trivializations preserves a scalar transition. -/
theorem restrictOverTrivialization_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫
      SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    let j : Over U := Over.mk (homOfLE hVU)
    (SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U g j).hom =
      (SheafOfModules.restrictOverTrivialization
          X.ringCatSheaf M U e j).hom ≫
        SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
          (X.presheaf.map (homOfLE hVU).op s) := by
  dsimp only
  let j : Over U := Over.mk (homOfLE hVU)
  apply SheafOfModules.hom_ext
  ext Z x
  change g.hom.val.app (.op ((Over.map j.hom).obj Z.unop)) x = _
  have happ := congrArg (fun q ↦ q.val.app
    (.op ((Over.map j.hom).obj Z.unop))) h
  have hx := ConcreteCategory.congr_hom happ x
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hx
  rw [SheafOfModules.overUnitScalarEnd_app_apply] at hx
  erw [SheafOfModules.overUnitScalarEnd_app_apply]
  have hmap : X.presheaf.map Z.unop.hom.op
      (X.presheaf.map (homOfLE hVU).op s) =
    X.presheaf.map ((Over.map j.hom).obj Z.unop).hom.op s := by
    have hc := congrArg (fun φ ↦ CommRingCat.Hom.hom φ s)
      ((X.presheaf.map_comp (homOfLE hVU).op Z.unop.hom.op).symm)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
    refine hc.trans ?_
    exact congrArg (fun ψ ↦ (CommRingCat.Hom.hom (X.presheaf.map ψ)) s)
      (Subsingleton.elim _ _)
  have he :
      (SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U e (Over.mk (homOfLE hVU))).hom.val.app Z x =
      e.hom.val.app (.op ((Over.map j.hom).obj Z.unop)) x := by
    rfl
  convert hx using 1
  all_goals first | exact congrArg₂ (fun a b ↦ a * b) he hmap | rfl

end ModularCurves
