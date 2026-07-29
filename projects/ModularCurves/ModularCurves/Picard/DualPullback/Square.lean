import ModularCurves.Picard.DualPullback
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor

/-!
# Pullback square coherence

Option-free coherence lemmas for pasting pullback squares and comparing the induced
natural isomorphisms. These are proof dependencies for pullback of sheaf duals.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory

universe u w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Pseudofunctor

variable {B : Type u₁} {C : Type u₂} [Bicategory.{w₁, v₁} B]
  [Strict B] [Bicategory.{w₂, v₂} C] (F : B ⥤ᵖ C)

theorem isoMapOfCommSq_vert_comp
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : B}
    {t : X₁ ⟶ Y₁} {l : X₁ ⟶ X₂} {r : Y₁ ⟶ Y₂}
    {b : X₂ ⟶ Y₂} {l' : X₂ ⟶ X₃} {r' : Y₂ ⟶ Y₃}
    {b' : X₃ ⟶ Y₃} (sq₁ : CommSq t l r b) (sq₂ : CommSq b l' r' b') :
    whiskerLeftIso (F.map t) (F.mapComp r r') ≪≫
        (α_ (F.map t) (F.map r) (F.map r')).symm ≪≫
        whiskerRightIso (F.isoMapOfCommSq sq₁) (F.map r') ≪≫
        α_ (F.map l) (F.map b) (F.map r') ≪≫
        whiskerLeftIso (F.map l) (F.isoMapOfCommSq sq₂) ≪≫
        (α_ (F.map l) (F.map l') (F.map b')).symm ≪≫
        whiskerRightIso (F.mapComp l l').symm (F.map b') =
      F.isoMapOfCommSq (sq₁.vert_comp sq₂) := by
  rw [F.isoMapOfCommSq_eq sq₁ (t ≫ r) rfl]
  rw [F.isoMapOfCommSq_eq sq₂ (b ≫ r') rfl]
  rw [F.isoMapOfCommSq_eq (sq₁.vert_comp sq₂)
    (t ≫ (r ≫ r')) rfl]
  apply Iso.ext
  rw [← F.mapComp'_eq_mapComp r r', ← F.mapComp'_eq_mapComp l l']
  simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    whiskerRightIso_hom, whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  rw [← F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_assoc
    t r r' (t ≫ r) (r ≫ r') (t ≫ (r ≫ r')) rfl rfl rfl]
  rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_assoc
    l b r' (t ≫ r) (b ≫ r') (t ≫ (r ≫ r'))
    sq₁.w.symm rfl (Category.assoc t r r')]
  rw [Iso.hom_inv_id_assoc]
  rw [F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_assoc
    l l' b' (l ≫ l') (b ≫ r') (t ≫ (r ≫ r'))
    rfl sq₂.w.symm (by rw [← Category.assoc, ← sq₁.w, Category.assoc])]
  simp

end CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Scheme.Modules

theorem adj_eqToHom_τl_toNatTrans
    {P Q : Bicategory.Adj Cat} {f g : P ⟶ Q} (h : f = g) :
    (eqToHom h : f ⟶ g).τl.toNatTrans =
      eqToHom (congrArg (fun k => k.l.toFunctor) h) := by
  subst h
  rfl

theorem adj_eqToIso_hom_τl_toNatTrans
    {P Q : Bicategory.Adj Cat} {f g : P ⟶ Q} (h : f = g) :
    (eqToIso h).hom.τl.toNatTrans =
      eqToHom (congrArg (fun k => k.l.toFunctor) h) := by
  subst h
  rfl

noncomputable def pullbackSquareIso
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    pullback b ⋙ pullback a ≅ pullback d ⋙ pullback c :=
  pullbackComp a b ≪≫ pullbackCongr h ≪≫ (pullbackComp c d).symm

theorem pullbackCongr_trans
    {X Y : Scheme.{u}} {f g h : X ⟶ Y}
    (p : f = g) (q : g = h) :
    pullbackCongr p ≪≫ pullbackCongr q = pullbackCongr (p.trans q) := by
  subst g
  subst h
  rfl

theorem pullbackCongr_inv
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (p : f = g) :
    (pullbackCongr p).inv = (pullbackCongr p.symm).hom := by
  subst g
  rfl

@[reassoc]
theorem pullbackComp_assoc_app
    {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ D) (M : D.Modules) :
    (pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M := by
  letI : (SheafOfModules.pushforward h.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction h).isRightAdjoint
  letI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have H := congrArg (fun z => z.hom.app M)
    (SheafOfModules.pullback_assoc.{u}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom] at H
  change
    (pullbackComp f g).hom.app ((pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M =
      (pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M at H
  exact H.symm

/-- Threefold pullback composition remains coherent after replacing the first composite and
transporting the resulting total composite to a common morphism. -/
theorem pullbackComp_three_congr_trans_app
    {A B C D : Scheme.{u}}
    (p : A ⟶ B) (d : B ⟶ C) (g : C ⟶ D)
    (s : A ⟶ C) (hp : p ≫ d = s) (w : A ⟶ D)
    (h₁ : p ≫ (d ≫ g) = s ≫ g)
    (h₂ : s ≫ g = w) (N : D.Modules) :
    (pullback p).map ((pullbackComp d g).hom.app N) ≫
        ((((pullbackComp p (d ≫ g)).app N) ≪≫
          ((pullbackCongr (h₁.trans h₂)).app N)).hom) =
      ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
          ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
        (pullbackComp s g).hom.app N ≫
        ((pullbackCongr h₂).app N).hom := by
  subst s
  simp only [Iso.trans_hom]
  have hcomp := pullbackComp_assoc_app p d g N
  have hproof : h₁.trans h₂ = h₂ := Subsingleton.elim _ _
  rw [hproof]
  have hcongr : ((pullbackCongr
      (rfl : p ≫ d = p ≫ d)).app ((pullback g).obj N)).hom = 𝟙 _ := rfl
  rw [hcongr, Category.comp_id]
  exact (reassoc_of% hcomp) ((pullbackCongr h₂).hom.app N)

/-- The two canonical ways to flatten four successive pullbacks agree. -/
theorem pullbackComp_four_assoc_app
    {A B C D E : Scheme.{u}}
    (q : A ⟶ B) (p : B ⟶ C) (d : C ⟶ D) (g : D ⟶ E)
    (N : E.Modules) :
    (pullbackComp q p).hom.app
          ((pullback d).obj ((pullback g).obj N)) ≫
        (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N) ≫
        (pullbackComp (q ≫ p) (d ≫ g)).hom.app N =
      (pullback q).map ((pullbackComp p d).hom.app
          ((pullback g).obj N)) ≫
        (pullbackComp q (p ≫ d)).hom.app ((pullback g).obj N) ≫
      (pullbackComp ((q ≫ p) ≫ d) g).hom.app N := by
  let α :
      (pullback q).obj ((pullback p).obj
        ((pullback d).obj ((pullback g).obj N))) ⟶
      (pullback (q ≫ p)).obj
        ((pullback d).obj ((pullback g).obj N)) :=
    (pullbackComp q p).hom.app ((pullback d).obj ((pullback g).obj N))
  let β :
      (pullback (q ≫ p)).obj
          ((pullback d).obj ((pullback g).obj N)) ⟶
        (pullback (q ≫ p)).obj ((pullback (d ≫ g)).obj N) :=
    (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N)
  let γ :
      (pullback (q ≫ p)).obj ((pullback (d ≫ g)).obj N) ⟶
        (pullback ((q ≫ p) ≫ (d ≫ g))).obj N :=
    (pullbackComp (q ≫ p) (d ≫ g)).hom.app N
  let δ :
      (pullback (q ≫ p)).obj
          ((pullback d).obj ((pullback g).obj N)) ⟶
        (pullback ((q ≫ p) ≫ d)).obj ((pullback g).obj N) :=
    (pullbackComp (q ≫ p) d).hom.app ((pullback g).obj N)
  let ε :
      (pullback ((q ≫ p) ≫ d)).obj ((pullback g).obj N) ⟶
        (pullback (((q ≫ p) ≫ d) ≫ g)).obj N :=
    (pullbackComp ((q ≫ p) ≫ d) g).hom.app N
  let ζ :
      (pullback q).obj ((pullback p).obj
          ((pullback d).obj ((pullback g).obj N))) ⟶
        (pullback q).obj
          ((pullback (p ≫ d)).obj ((pullback g).obj N)) :=
    (pullback q).map ((pullbackComp p d).hom.app ((pullback g).obj N))
  let η :
      (pullback q).obj
          ((pullback (p ≫ d)).obj ((pullback g).obj N)) ⟶
        (pullback ((q ≫ p) ≫ d)).obj ((pullback g).obj N) :=
    (pullbackComp q (p ≫ d)).hom.app ((pullback g).obj N)
  change α ≫ (β ≫ γ) = ζ ≫ (η ≫ ε)
  have hβγ : β ≫ γ = δ ≫ ε :=
    pullbackComp_assoc_app (q ≫ p) d g N
  have hζη : ζ ≫ η = α ≫ δ :=
    pullbackComp_assoc_app q p d ((pullback g).obj N)
  rw [hβγ]
  have hcomp := congrArg (fun z => z ≫ ε) hζη.symm
  exact (Category.assoc α δ ε).symm.trans
    (hcomp.trans (Category.assoc ζ η ε))

/-- Reassociating the first three maps before composing with a fourth map is absorbed by the
corresponding pullback congruence. -/
theorem pullbackComp_assoc_congr_app
    {A B C D E : Scheme.{u}}
    (q : A ⟶ B) (p : B ⟶ C) (d : C ⟶ D) (g : D ⟶ E)
    (h : (q ≫ p) ≫ (d ≫ g) = (q ≫ (p ≫ d)) ≫ g)
    (N : E.Modules) :
    (pullbackComp ((q ≫ p) ≫ d) g).hom.app N ≫
        ((pullbackCongr h).app N).hom =
      (pullbackComp (q ≫ (p ≫ d)) g).hom.app N := by
  rfl

/-- Fourfold pullback composition is compatible with replacing the middle composite by an
equal morphism. -/
theorem pullbackComp_four_congr_app
    {A B C D E : Scheme.{u}}
    (q : A ⟶ B) (p : B ⟶ C) (d : C ⟶ D) (g : D ⟶ E)
    (s : B ⟶ D) (hp : p ≫ d = s)
    (h : (q ≫ p) ≫ (d ≫ g) = (q ≫ s) ≫ g)
    (N : E.Modules) :
    (pullbackComp q p).hom.app
          ((pullback d).obj ((pullback g).obj N)) ≫
        (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N) ≫
        ((((pullbackComp (q ≫ p) (d ≫ g)).app N) ≪≫
          ((pullbackCongr h).app N)).hom) =
      (pullback q).map
          ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
            ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
        (pullbackComp q s).hom.app ((pullback g).obj N) ≫
      (pullbackComp (q ≫ s) g).hom.app N := by
  subst s
  simp only [Iso.trans_hom]
  have hinner :
      ((pullbackComp p d).app ((pullback g).obj N)).hom ≫
          ((pullbackCongr (rfl : p ≫ d = p ≫ d)).app
            ((pullback g).obj N)).hom =
        ((pullbackComp p d).app ((pullback g).obj N)).hom := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [hinner]
  let Q := ((pullbackCongr h).app N).hom
  have hfour := pullbackComp_four_assoc_app q p d g N
  have htail := pullbackComp_assoc_congr_app q p d g h N
  have hfourQ := congrArg (fun z => z ≫ Q) hfour
  let R₁ := (pullback q).map
    ((pullbackComp p d).hom.app ((pullback g).obj N))
  let R₂ := (pullbackComp q (p ≫ d)).hom.app ((pullback g).obj N)
  let R₃ := (pullbackComp ((q ≫ p) ≫ d) g).hom.app N
  let R₄ := (pullbackComp (q ≫ (p ≫ d)) g).hom.app N
  change R₃ ≫ Q = R₄ at htail
  have hright : (R₁ ≫ (R₂ ≫ R₃)) ≫ Q = R₁ ≫ (R₂ ≫ R₄) :=
    (Category.assoc R₁ (R₂ ≫ R₃) Q).trans
      (congrArg (R₁ ≫ ·)
        ((Category.assoc R₂ R₃ Q).trans (congrArg (R₂ ≫ ·) htail)))
  exact hfourQ.trans hright

/-- Fourfold pullback composition remains coherent after a further transport from the chosen
composite to a common target morphism. -/
theorem pullbackComp_four_congr_trans_app
    {A B C D E : Scheme.{u}}
    (q : A ⟶ B) (p : B ⟶ C) (d : C ⟶ D) (g : D ⟶ E)
    (s : B ⟶ D) (hp : p ≫ d = s) (w : A ⟶ E)
    (h₁ : (q ≫ p) ≫ (d ≫ g) = (q ≫ s) ≫ g)
    (h₂ : (q ≫ s) ≫ g = w) (N : E.Modules) :
    (pullbackComp q p).hom.app
          ((pullback d).obj ((pullback g).obj N)) ≫
        (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N) ≫
        ((((pullbackComp (q ≫ p) (d ≫ g)).app N) ≪≫
          ((pullbackCongr (h₁.trans h₂)).app N)).hom) =
      (pullback q).map
          ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
            ((pullbackCongr hp).app ((pullback g).obj N))).hom) ≫
        (pullbackComp q s).hom.app ((pullback g).obj N) ≫
      (pullbackComp (q ≫ s) g).hom.app N ≫
        ((pullbackCongr h₂).app N).hom := by
  have hbase := pullbackComp_four_congr_app q p d g s hp h₁ N
  simp only [Iso.trans_hom]
  let L₁ := (pullbackComp q p).hom.app
    ((pullback d).obj ((pullback g).obj N))
  let L₂ := (pullback (q ≫ p)).map ((pullbackComp d g).hom.app N)
  let P := ((pullbackComp (q ≫ p) (d ≫ g)).app N).hom
  let Q₁ := ((pullbackCongr h₁).app N).hom
  let Q₂ := ((pullbackCongr h₂).app N).hom
  let Q₁₂ := ((pullbackCongr (h₁.trans h₂)).app N).hom
  let R₁ := (pullback q).map
    ((((pullbackComp p d).app ((pullback g).obj N)) ≪≫
      ((pullbackCongr hp).app ((pullback g).obj N))).hom)
  let R₂ := (pullbackComp q s).hom.app ((pullback g).obj N)
  let R₃ := (pullbackComp (q ≫ s) g).hom.app N
  change L₁ ≫ L₂ ≫ (P ≫ Q₁₂) = R₁ ≫ R₂ ≫ R₃ ≫ Q₂
  change L₁ ≫ L₂ ≫ (P ≫ Q₁) = R₁ ≫ R₂ ≫ R₃ at hbase
  have htrans := pullbackCongr_trans h₁ h₂
  have htransApp := congrArg (fun z => z.hom.app N) htrans
  change Q₁ ≫ Q₂ = Q₁₂ at htransApp
  have hbaseQ := congrArg (fun z => z ≫ Q₂) hbase
  have hPQ : (P ≫ Q₁) ≫ Q₂ = P ≫ Q₁₂ :=
    (Category.assoc P Q₁ Q₂).trans (congrArg (P ≫ ·) htransApp)
  have hleft : (L₁ ≫ L₂ ≫ (P ≫ Q₁)) ≫ Q₂ =
      L₁ ≫ L₂ ≫ (P ≫ Q₁₂) :=
    (Category.assoc L₁ (L₂ ≫ (P ≫ Q₁)) Q₂).trans
      (congrArg (L₁ ≫ ·)
        ((Category.assoc L₂ (P ≫ Q₁) Q₂).trans
          (congrArg (L₂ ≫ ·) hPQ)))
  have hright : (R₁ ≫ R₂ ≫ R₃) ≫ Q₂ =
      R₁ ≫ R₂ ≫ R₃ ≫ Q₂ :=
    (Category.assoc R₁ (R₂ ≫ R₃) Q₂).trans
      (congrArg (R₁ ≫ ·) (Category.assoc R₂ R₃ Q₂))
  exact hleft.symm.trans (hbaseQ.trans hright)

theorem pullbackCompCongr_transition_app
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (p : A ⟶ D) (h₁ : a ≫ b = p) (h₂ : c ≫ d = p)
    (M : D.Modules) :
    (((pullbackComp a b).app M) ≪≫ ((pullbackCongr h₁).app M)).hom ≫
        (((pullbackComp c d).app M) ≪≫
          ((pullbackCongr h₂).app M)).inv =
      (pullbackSquareIso a b c d (h₁.trans h₂.symm)).hom.app M := by
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app]
  let P₁ := (pullbackComp a b).app M
  let P₂ := (pullbackComp c d).app M
  let Q₁ := (pullbackCongr h₁).app M
  let Q₂ := (pullbackCongr h₂).app M
  let Q₁₂ := (pullbackCongr (h₁.trans h₂.symm)).app M
  change (P₁.hom ≫ Q₁.hom) ≫ (Q₂.inv ≫ P₂.inv) =
    P₁.hom ≫ Q₁₂.hom ≫ P₂.inv
  have hQ₂ := congrArg (fun z => z.app M) (pullbackCongr_inv h₂)
  change Q₂.inv = (pullbackCongr h₂.symm).hom.app M at hQ₂
  have htrans := pullbackCongr_trans h₁ h₂.symm
  have htransApp := congrArg (fun z => z.hom.app M) htrans
  change Q₁.hom ≫ (pullbackCongr h₂.symm).hom.app M = Q₁₂.hom at htransApp
  calc
    (P₁.hom ≫ Q₁.hom) ≫ (Q₂.inv ≫ P₂.inv) =
        P₁.hom ≫ (Q₁.hom ≫ Q₂.inv) ≫ P₂.inv := by
      simp only [Category.assoc]
    _ = P₁.hom ≫
        (Q₁.hom ≫ (pullbackCongr h₂.symm).hom.app M) ≫ P₂.inv := by
      rw [hQ₂]
    _ = P₁.hom ≫ Q₁₂.hom ≫ P₂.inv := by rw [htransApp]

theorem pullbackSquareIso_trans_app
    {A B C E D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (d : C ⟶ D)
    (e : A ⟶ E) (f : E ⟶ D)
    (h₁ : a ≫ b = c ≫ d) (h₂ : c ≫ d = e ≫ f)
    (h₃ : a ≫ b = e ≫ f) (M : D.Modules) :
    (pullbackSquareIso a b c d h₁).hom.app M ≫
        (pullbackSquareIso c d e f h₂).hom.app M =
      (pullbackSquareIso a b e f h₃).hom.app M := by
  simp only [pullbackSquareIso, Iso.trans_hom, NatTrans.comp_app]
  let P₀ := (pullbackComp a b).app M
  let P₁ := (pullbackComp c d).app M
  let P₂ := (pullbackComp e f).app M
  let Q₁ := (pullbackCongr h₁).app M
  let Q₂ := (pullbackCongr h₂).app M
  let Q₃ := (pullbackCongr h₃).app M
  change P₀.hom ≫ Q₁.hom ≫ P₁.inv ≫
      (P₁.hom ≫ Q₂.hom ≫ P₂.inv) =
    P₀.hom ≫ Q₃.hom ≫ P₂.inv
  simp only [Iso.inv_hom_id_assoc]
  have hp : h₁.trans h₂ = h₃ := Subsingleton.elim _ _
  have hQ := pullbackCongr_trans h₁ h₂
  rw [hp] at hQ
  have hQapp := congrArg (fun z => z.hom.app M) hQ
  change Q₁.hom ≫ Q₂.hom = Q₃.hom at hQapp
  calc
    P₀.hom ≫ Q₁.hom ≫ Q₂.hom ≫ P₂.inv =
        P₀.hom ≫ (Q₁.hom ≫ Q₂.hom) ≫ P₂.inv := by
      simp only [Category.assoc]
    _ = P₀.hom ≫ Q₃.hom ≫ P₂.inv := by rw [hQapp]

noncomputable def pullbackSquareIsoP
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    pullback b ⋙ pullback a ≅ pullback d ⋙ pullback c :=
  (Cat.Hom.toNatIso (Bicategory.Adj.lIso
    (pseudofunctor.isoMapOfCommSq
      ((CommSq.mk h : CommSq a c b d).op.toLoc)))).symm

theorem pseudofunctor_isoMapOfCommSq_hom_τl_toNatTrans
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    (pseudofunctor.isoMapOfCommSq
      ((CommSq.mk h : CommSq a c b d).op.toLoc)).hom.τl.toNatTrans =
      (pullbackSquareIsoP a b c d h).inv := by
  rfl

theorem pseudofunctor_isoMapOfCommSq_inv_τl_toNatTrans
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    (pseudofunctor.isoMapOfCommSq
      ((CommSq.mk h : CommSq a c b d).op.toLoc)).inv.τl.toNatTrans =
      (pullbackSquareIsoP a b c d h).hom := by
  rfl

theorem pseudofunctor_mapComp'_inv_τl_toNatTrans_refl
    {A B D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) :
    (pseudofunctor.mapComp' b.op.toLoc a.op.toLoc (a ≫ b).op.toLoc
      (by rfl)).inv.τl.toNatTrans = (pullbackComp a b).hom := by
  rfl

theorem pseudofunctor_mapComp'_hom_τl_toNatTrans_eq
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    (pseudofunctor.mapComp' d.op.toLoc c.op.toLoc (a ≫ b).op.toLoc
      (by
        apply Discrete.ext
        change d.op ≫ c.op = (a ≫ b).op
        simpa only [← op_comp] using congrArg Quiver.Hom.op h.symm)).hom.τl.toNatTrans =
      (pullbackCongr h).hom ≫ (pullbackComp c d).inv := by
  let hloc : d.op.toLoc ≫ c.op.toLoc = (a ≫ b).op.toLoc := by
    apply Discrete.ext
    change d.op ≫ c.op = (a ≫ b).op
    simpa only [← op_comp] using congrArg Quiver.Hom.op h.symm
  let η : (a ≫ b).op.toLoc ≅ d.op.toLoc ≫ c.op.toLoc :=
    eqToIso hloc.symm
  simp only [Pseudofunctor.mapComp', Iso.trans_hom,
    Bicategory.Adj.comp_τl, Cat.Hom.toNatTrans_comp,
    pseudofunctor_mapComp_hom_τl]
  have hmap :
      (pseudofunctor.map₂Iso η).hom.τl.toNatTrans =
        (pullbackCongr h).hom := by
    rw [PrelaxFunctor.map₂Iso_eqToIso]
    rw [adj_eqToIso_hom_τl_toNatTrans]
    unfold pullbackCongr
    rfl
  exact congrArg (fun q => q ≫ (pullbackComp c d).inv) hmap

theorem pullbackSquareIso_eq_p
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (h : a ≫ b = c ≫ d) :
    pullbackSquareIso a b c d h = pullbackSquareIsoP a b c d h := by
  apply Iso.ext
  change (pullbackComp a b).hom ≫ (pullbackCongr h).hom ≫
      (pullbackComp c d).inv = _
  change _ = (pseudofunctor.isoMapOfCommSq
    ((CommSq.mk h : CommSq a c b d).op.toLoc)).inv.τl.toNatTrans
  rw [Pseudofunctor.isoMapOfCommSq_eq pseudofunctor
    ((CommSq.mk h : CommSq a c b d).op.toLoc) ((a ≫ b).op.toLoc)
    (by
      apply Discrete.ext
      change d.op ≫ c.op = (a ≫ b).op
      simpa only [← op_comp] using congrArg Quiver.Hom.op h.symm)]
  simp only [Iso.trans_inv, Bicategory.Adj.comp_τl,
    Cat.Hom.toNatTrans_comp]
  rw [pseudofunctor_mapComp'_inv_τl_toNatTrans_refl]
  let hloc : d.op.toLoc ≫ c.op.toLoc = (a ≫ b).op.toLoc := by
    apply Discrete.ext
    change d.op ≫ c.op = (a ≫ b).op
    simpa only [← op_comp] using congrArg Quiver.Hom.op h.symm
  change (pullbackComp a b).hom ≫ (pullbackCongr h).hom ≫
      (pullbackComp c d).inv =
    (pullbackComp a b).hom ≫
      (pseudofunctor.mapComp' d.op.toLoc c.op.toLoc (a ≫ b).op.toLoc
        hloc).hom.τl.toNatTrans
  rw [pseudofunctor_mapComp'_hom_τl_toNatTrans_eq a b c d h]
  exact Category.assoc _ _ _

theorem pseudofunctor_mapComp_hom_τl_toNatTrans
    {A B D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) :
    (pseudofunctor.mapComp b.op.toLoc a.op.toLoc).hom.τl.toNatTrans =
      (pullbackComp a b).inv := by
  rfl

theorem pseudofunctor_mapComp_inv_τl_toNatTrans
    {A B D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D) :
    (pseudofunctor.mapComp b.op.toLoc a.op.toLoc).inv.τl.toNatTrans =
      (pullbackComp a b).hom := by
  rfl

theorem pullbackSquareIso_vcomp
    {A B C D E F : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
    (q : D ⟶ F) (e : C ⟶ E) (r : E ⟶ F)
    (h₁ : a ≫ b = c ≫ d) (h₂ : d ≫ q = e ≫ r) :
    (Functor.associator (pullback q) (pullback b) (pullback a) ≪≫
        Functor.isoWhiskerLeft (pullback q)
          (pullbackSquareIso a b c d h₁) ≪≫
        (Functor.associator (pullback q) (pullback d) (pullback c)).symm ≪≫
        Functor.isoWhiskerRight (pullbackSquareIso d q e r h₂)
          (pullback c)) =
      (Functor.isoWhiskerRight (pullbackComp b q) (pullback a) ≪≫
        pullbackSquareIso a (b ≫ q) (c ≫ e) r
          (by
            exact (Category.assoc a b q).symm.trans
              ((congrArg (· ≫ q) h₁).trans
                ((Category.assoc c d q).trans
                  ((congrArg (c ≫ ·) h₂).trans
                    (Category.assoc c e r).symm)))) ≪≫
        Functor.isoWhiskerLeft (pullback r) (pullbackComp c e).symm ≪≫
        (Functor.associator (pullback r) (pullback e) (pullback c)).symm) := by
  rw [pullbackSquareIso_eq_p a b c d h₁]
  rw [pullbackSquareIso_eq_p d q e r h₂]
  rw [pullbackSquareIso_eq_p a (b ≫ q) (c ≫ e) r]
  let sq₁ : CommSq a c b d := ⟨h₁⟩
  let sq₂ : CommSq d e q r := ⟨h₂⟩
  let hpaste : a ≫ (b ≫ q) = (c ≫ e) ≫ r :=
    (Category.assoc a b q).symm.trans
      ((congrArg (· ≫ q) h₁).trans
        ((Category.assoc c d q).trans
          ((congrArg (c ≫ ·) h₂).trans
            (Category.assoc c e r).symm)))
  have H := Pseudofunctor.isoMapOfCommSq_vert_comp pseudofunctor
    sq₂.op.toLoc sq₁.op.toLoc
  apply Iso.ext
  have H' := congrArg (fun z => z.inv.τl.toNatTrans) H
  simp only [Iso.trans_inv, Iso.symm_inv, Bicategory.whiskerLeftIso_inv,
    Bicategory.whiskerRightIso_inv, Bicategory.Adj.comp_τl,
    Bicategory.Adj.whiskerLeft_τl, Bicategory.Adj.whiskerRight_τl,
    Bicategory.Adj.associator_hom_τl, Bicategory.Adj.associator_inv_τl,
    Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
    Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans,
    Cat.associator_inv_toNatTrans,
    pseudofunctor_mapComp_hom_τl_toNatTrans,
    pseudofunctor_mapComp_inv_τl_toNatTrans] at H'
  let e₀ := Functor.isoWhiskerRight (pullbackComp b q) (pullback a)
  let e₁ := Functor.associator (pullback q) (pullback b) (pullback a)
  let e₂ := (pullback q).isoWhiskerLeft
    (pullbackSquareIsoP a b c d h₁)
  let e₃ := (Functor.associator
    (pullback q) (pullback d) (pullback c)).symm
  let e₄ := Functor.isoWhiskerRight
    (pullbackSquareIsoP d q e r h₂) (pullback c)
  let e₅ := pullbackSquareIsoP a (b ≫ q) (c ≫ e) r hpaste
  let e₆ := (pullback r).isoWhiskerLeft (pullbackComp c e).symm
  let e₇ := (Functor.associator
    (pullback r) (pullback e) (pullback c)).symm
  change ((((((e₀.inv ≫ e₁.hom) ≫ e₂.hom) ≫ e₃.hom) ≫
    e₄.hom) ≫ e₇.inv) ≫ e₆.inv = e₅.hom) at H'
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  change e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom =
    e₀.hom ≫ e₅.hom ≫ e₆.hom ≫ e₇.hom
  have H'' := congrArg (fun k => k ≫ e₆.hom ≫ e₇.hom) H'
  rw [← cancel_epi e₀.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using H''

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {A B : Scheme.{u}}

theorem restrictFunctorCongr_refl_hom_app
    (f : A ⟶ B) [IsOpenImmersion f] (M : B.Modules) :
    (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((restrictFunctorCongr (rfl : f = f)).hom.app M).app U.unop x = x
  rw [restrictFunctorCongr_hom_app_app]
  change M.presheaf.map _ x = x
  erw [M.presheaf.congr_map
    (Subsingleton.elim _ (𝟙 (Opposite.op (f ''ᵁ U.unop))))]
  erw [M.presheaf.map_id]
  rfl

theorem restrictFunctorIsoPullback_congr
    {f g : A ⟶ B} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) (M : B.Modules) :
    (restrictFunctorCongr h).hom.app M ≫
        (restrictFunctorIsoPullback g).hom.app M =
      (restrictFunctorIsoPullback f).hom.app M ≫
        (pullbackCongr h).hom.app M := by
  subst h
  rw [restrictFunctorCongr_refl_hom_app]
  rfl

theorem restrictFunctorIsoPullback_congr_inv
    {f g : A ⟶ B} [IsOpenImmersion f] [IsOpenImmersion g]
    (h : f = g) (M : B.Modules) :
    (pullbackCongr h).inv.app M ≫
        (restrictFunctorIsoPullback f).inv.app M ≫
        (restrictFunctorCongr h).hom.app M =
      (restrictFunctorIsoPullback g).inv.app M := by
  let eR := (restrictFunctorCongr h).app M
  let eP := (pullbackCongr h).app M
  let eF := (restrictFunctorIsoPullback f).app M
  let eG := (restrictFunctorIsoPullback g).app M
  have hhom : eR.hom ≫ eG.hom = eF.hom ≫ eP.hom :=
    restrictFunctorIsoPullback_congr h M
  have hiso : eR ≪≫ eG = eF ≪≫ eP := by
    apply Iso.ext
    exact hhom
  have hinv := congrArg Iso.inv hiso
  simp only [Iso.trans_inv] at hinv
  change eP.inv ≫ eF.inv ≫ eR.hom = eG.inv
  rw [← Category.assoc]
  erw [← hinv]
  simp

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

theorem pullbackSquareIso_congr
    {A B C D : Scheme.{u}}
    (a : A ⟶ B) {b b' : B ⟶ D} {c c' : A ⟶ C} (d : C ⟶ D)
    (hb : b = b') (hc : c = c')
    (h : a ≫ b = c ≫ d) (h' : a ≫ b' = c' ≫ d) :
    Functor.isoWhiskerRight (pullbackCongr hb) (pullback a) ≪≫
        pullbackSquareIso a b' c' d h' ≪≫
        Functor.isoWhiskerLeft (pullback d) (pullbackCongr hc).symm =
      pullbackSquareIso a b c d h := by
  subst hb
  subst hc
  apply Iso.ext
  simp [pullbackCongr]

end AlgebraicGeometry.Scheme.Modules
