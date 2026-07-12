import ModularCurves.ForMathlib.FlasqueCohomology
import ModularCurves.ForMathlib.TopCatSheafRestrict

/-!
# Local vanishing of degree-one sheaf cohomology classes

This file gives the option-free degree-one local-killing step in Kempf's proof of affine
quasicoherent vanishing. A class in `H¹(X, F)` restricts to zero on a basis open around any
chosen point of `X`.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u v

namespace CategoryTheory.Sheaf.H

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  {S : ShortComplex (Sheaf J AddCommGrpCat.{u})} (hS : S.ShortExact)
  {T : C} (hT : IsTerminal T)

/-- Exactness at `H¹(S.X₁)`, with degree-zero cohomology expressed as sections over a terminal
object. -/
lemma longSequence_equiv₀_exact₁ (x₁ : H S.X₁ 1) (hx₁ : map S.f 1 x₁ = 0) :
    ∃ x₃ : S.X₃.obj.obj (op T),
      δ hS 0 1 rfl ((equiv₀ S.X₃ hT).symm x₃) = x₁ := by
  obtain ⟨x₃, hx₃⟩ := longSequence_exact₁ hS 0 1 rfl x₁ hx₁
  exact ⟨equiv₀ S.X₃ hT x₃, by simpa using hx₃⟩

end CategoryTheory.Sheaf.H

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

open Topology

/-- Restriction along an equality of open subsets. -/
abbrev restrictOfEq {C : Type*} [Category* C] (F : Sheaf C X) {U V : Opens X} (h : U = V) :=
  F.obj.map (homOfLE (le_of_eq h)).op

/-- Naturality of the unit from a sheaf to the pushforward of its restriction. -/
lemma toRestrict_naturality {C : Type*} [Category* C] (U : Opens X)
    {F G : Sheaf C X} (α : F ⟶ G) :
    α ≫ (toRestrict C U).app G =
      (toRestrict C U).app F ≫
        (restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').map α := by
  simpa using (toRestrict C U).naturality α

/-- Evaluate an equality of composites of concrete sheaf morphisms on a section. -/
lemma comp_app_apply {A : Type*} [Category.{u} A] {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    {F G H : Sheaf A X} {f : F ⟶ G} {g : G ⟶ H} {φ : F ⟶ H} (h : f ≫ g = φ)
    (V : (Opens X)ᵒᵖ) (x : ToType (F.obj.obj V)) :
    g.hom.app V (f.hom.app V x) = φ.hom.app V x := by
  simpa [Sheaf.comp_app] using congr($(h).hom.app V x)

/-- Restricting a section through two inclusions agrees with restricting through their
composite. -/
lemma restrict_restrict_apply {A : Type*} [Category.{u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    {F : Sheaf A X} {U V W : (Opens X)ᵒᵖ} (s : ToType (F.obj.obj U))
    (hUW : U ⟶ W) (hUV : U ⟶ V) (hVW : V ⟶ W) :
    F.obj.map hVW (F.obj.map hUV s) = F.obj.map hUW s := by
  have h : hUV ≫ hVW = hUW := Subsingleton.elim _ _
  simpa using congr(F.obj.map $(h) s)

/-- Naturality of a concrete sheaf morphism evaluated on a section. -/
lemma hom_naturality_apply {A : Type*} [Category.{u} A]
    {FC : A → A → Type*} {CC : A → Type u}
    [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} A FC]
    {F G : Sheaf A X} (f : F ⟶ G) {U V : (Opens X)ᵒᵖ} (hUV : U ⟶ V)
    (s : ToType (F.obj.obj U)) :
    f.hom.app V (F.obj.map hUV s) = G.obj.map hUV (f.hom.app U s) := by
  simp

private lemma H_one_map_toRestrict_eq_zero_of_lift
    (pres : ShortComplex (Sheaf AddCommGrpCat.{u} X)) (presEx : pres.ShortExact)
    (V : Opens X) (b : pres.X₃.obj.obj (op ⊤)) (s : pres.X₂.obj.obj (op V))
    (hs : pres.g.hom.app (op V) s = pres.X₃.obj.map V.leTop.op b) :
    H.map ((toRestrict AddCommGrpCat V).app pres.X₁) 1
      (CategoryTheory.Sheaf.H.δ presEx 0 1 rfl
        ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃ isTerminalTop).symm b)) = 0 := by
  letI : Mono pres.f := presEx.2
  letI : Epi pres.g := presEx.3
  let presV := ShortComplex.mk
    ((restrict AddCommGrpCat V.isOpenEmbedding ⋙ pushforward AddCommGrpCat V.inclusion').map
      pres.f)
    (cokernel.π ((restrict AddCommGrpCat V.isOpenEmbedding ⋙
      pushforward AddCommGrpCat V.inclusion').map pres.f))
    (cokernel.condition _)
  have presVEx : presV.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel _)
  let presV' := pres.map
    (restrict AddCommGrpCat V.isOpenEmbedding ⋙ pushforward AddCommGrpCat V.inclusion')
  have presV'Ex : presV'.Exact :=
    ((_ ⋙ pushforward _ _).preservesFiniteLimits_tfae.out 3 1 rfl rfl).mp inferInstance pres
      ⟨presEx.1, presEx.2⟩ |>.1
  let φ : presV.X₃ ⟶ presV'.X₃ := cokernel.desc presV'.f presV'.g presV'.zero
  have hφMono : Mono φ := ShortComplex.Exact.mono_cokernelDesc presV'Ex
  let res : pres ⟶ presV := ShortComplex.Hom.mk ((toRestrict _ V).app pres.X₁)
    ((toRestrict _ V).app pres.X₂)
    (ShortComplex.Exact.desc presEx.exact
      ((toRestrict _ V).app pres.X₂ ≫ presV.g)
      (by
        have hcomm : pres.f ≫ (toRestrict AddCommGrpCat V).app pres.X₂ =
            (toRestrict AddCommGrpCat V).app pres.X₁ ≫ presV.f := by
          change pres.f ≫ (toRestrict AddCommGrpCat V).app pres.X₂ =
            (toRestrict AddCommGrpCat V).app pres.X₁ ≫
              (restrict AddCommGrpCat V.isOpenEmbedding ⋙
                pushforward AddCommGrpCat V.inclusion').map pres.f
          exact toRestrict_naturality V pres.f
        calc
          pres.f ≫ ((toRestrict AddCommGrpCat V).app pres.X₂ ≫ presV.g) =
              (pres.f ≫ (toRestrict AddCommGrpCat V).app pres.X₂) ≫ presV.g :=
            (Category.assoc _ _ _).symm
          _ = ((toRestrict AddCommGrpCat V).app pres.X₁ ≫ presV.f) ≫ presV.g :=
            congrArg (fun k ↦ k ≫ presV.g) hcomm
          _ = (toRestrict AddCommGrpCat V).app pres.X₁ ≫ (presV.f ≫ presV.g) :=
            Category.assoc _ _ _
          _ = 0 := by rw [presV.zero, comp_zero]))
    (by
      change (toRestrict AddCommGrpCat V).app pres.X₁ ≫
          (restrict AddCommGrpCat V.isOpenEmbedding ⋙
            pushforward AddCommGrpCat V.inclusion').map pres.f =
        pres.f ≫ (toRestrict AddCommGrpCat V).app pres.X₂
      exact (toRestrict_naturality V pres.f).symm)
    (by simp)
  have φ₁ : presV.g ≫ φ =
      (restrict AddCommGrpCat V.isOpenEmbedding ⋙
        pushforward AddCommGrpCat V.inclusion').map pres.g :=
    cokernel.π_desc presV'.f presV'.g presV'.zero
  have φ₂ : res.τ₃ ≫ φ = (toRestrict _ V).app pres.X₃ := by
    rw [← cancel_epi pres.g, ← res.comm₂₃_assoc, φ₁]
    change (toRestrict AddCommGrpCat V).app pres.X₂ ≫
        (restrict AddCommGrpCat V.isOpenEmbedding ⋙
          pushforward AddCommGrpCat V.inclusion').map pres.g =
      pres.g ≫ (toRestrict AddCommGrpCat V).app pres.X₃
    exact (toRestrict_naturality V pres.g).symm
  change H.map res.τ₁ 1
    (CategoryTheory.Sheaf.H.δ presEx 0 1 rfl
      ((CategoryTheory.Sheaf.H.equiv₀ pres.X₃ isTerminalTop).symm b)) = 0
  rw [← CategoryTheory.Sheaf.H.δ_naturality 0 1 rfl presEx presVEx res,
    CategoryTheory.Sheaf.H.equiv₀_symm_naturality]
  have hres : res.τ₃.hom.app (op ⊤) b = presV.g.hom.app (op ⊤)
      (pres.X₂.restrictOfEq (Opens.isOpenEmbedding_obj_top V) s) := by
    haveI : Mono φ.hom := @Functor.map_mono _ _ _ _
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat) _ _ _ φ hφMono
    apply ConcreteCategory.injective_of_mono_of_preservesPullback (φ.hom.app (op ⊤))
    rw [comp_app_apply φ₁, comp_app_apply φ₂]
    erw [hom_naturality_apply pres.g]
    rw [hs]
    change pres.X₃.obj.map _ b = pres.X₃.obj.map _ (pres.X₃.obj.map _ b)
    exact (restrict_restrict_apply b ..).symm
  rw [hres, ← CategoryTheory.Sheaf.H.equiv₀_symm_naturality,
    CategoryTheory.Sheaf.H.longSequence_comp_zero₃]

/-- Every degree-one cohomology class restricts to zero on a basis open around a chosen point. -/
lemma one_ex_opens_toRestrict_app_zero (F : Sheaf AddCommGrpCat.{u} X)
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (c : H F 1) (x : X) :
    ∃ U : Opens X, x ∈ U ∧ U ∈ B ∧ H.map ((toRestrict _ U).app F) 1 c = 0 := by
  let pres := (EnoughInjectives.presentation F).some.shortComplex
  have presEx : pres.ShortExact :=
    (EnoughInjectives.presentation F).some.shortExact_shortComplex
  obtain ⟨b, hb⟩ :=
    CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₁ presEx isTerminalTop c
      (Subsingleton.elim _ _)
  have hEpi := presEx.3
  rw [← isLocallySurjective_iff_epi, Presheaf.isLocallySurjective_iff] at hEpi
  obtain ⟨V', ⟨hV'₁, ⟨⟨s', hs'⟩, hV'₃⟩⟩⟩ := hEpi ⊤ b x (Opens.mem_top x)
  obtain ⟨V, ⟨hV₁, ⟨hV₂, hV₃⟩⟩⟩ := Opens.isBasis_iff_nbhd.mp hB hV'₃
  refine ⟨V, hV₂, hV₁, ?_⟩
  let s := pres.X₂.obj.map (homOfLE hV₃).op s'
  have hs : pres.g.hom.app (op V) s = pres.X₃.obj.map V.leTop.op b := by
    dsimp [s]
    rw [hom_naturality_apply, hs']
    exact restrict_restrict_apply b ..
  rw [← hb]
  exact H_one_map_toRestrict_eq_zero_of_lift pres presEx V b s hs

end TopCat.Sheaf
