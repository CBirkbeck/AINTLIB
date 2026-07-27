/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
import Mathlib.RingTheory.PicardGroup

open CategoryTheory Abelian Limits ModuleCat
open scoped ModuleCat.Algebra

universe u

namespace ModuleCat.BaseChangeExt

variable {S : Type u} [CommRing S] (𝔪 : Submonoid S)

/-! ### The localization functor is `S`-linear -/

/-- The localization functor `ModuleCat S ⥤ ModuleCat (Localization 𝔪)` is `S`-linear. -/
instance functorLinear : (ModuleCat.localizedModuleFunctor.{u} 𝔪).Linear S where
  map_smul {M N} f s := by
    apply ModuleCat.hom_ext
    rw [show s • (ModuleCat.localizedModuleFunctor.{u} 𝔪).map f
        = (algebraMap S (Localization 𝔪) s) • (ModuleCat.localizedModuleFunctor.{u} 𝔪).map f
        from ModuleCat.hom_ext rfl, ModuleCat.hom_smul,
      show ModuleCat.Hom.hom ((ModuleCat.localizedModuleFunctor.{u} 𝔪).map (s • f))
        = IsLocalizedModule.mapExtendScalars 𝔪 (M.localizedModuleMkLinearMap 𝔪)
          (N.localizedModuleMkLinearMap 𝔪) (Localization 𝔪) (s • f.hom) from rfl,
      map_smul, ← IsScalarTower.algebraMap_smul (Localization 𝔪) s]
    rfl

/-- The `S`-module structure on `Ext` over `ModuleCat (Localization 𝔪)` is the restriction of the
`Localization 𝔪`-module structure. -/
instance isScalarTowerExt (A B : ModuleCat.{u} (Localization 𝔪)) (m : ℕ) :
    IsScalarTower S (Localization 𝔪) (Ext A B m) := by
  refine IsScalarTower.of_algebraMap_smul fun s e => ?_
  have hid : (algebraMap S (Localization 𝔪) s) • (𝟙 B) = s • 𝟙 B := by
    refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_coe,
      id_eq]
    exact IsScalarTower.algebraMap_smul (Localization 𝔪) s b
  rw [Ext.smul_eq_comp_mk₀, Ext.smul_eq_comp_mk₀, hid]

/-! ### Transport of `Ext` along isomorphisms in both variables -/

/-- An isomorphism in each variable induces an equivalence of `Ext` groups. -/
noncomputable def extEquivOfIso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ Ext X' Y' n where
  toFun f := (Ext.mk₀ eX.inv).comp (f.comp (Ext.mk₀ eY.hom) (add_zero n)) (zero_add n)
  invFun g := (Ext.mk₀ eX.hom).comp (g.comp (Ext.mk₀ eY.inv) (add_zero n)) (zero_add n)
  left_inv f := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id,
      Ext.mk₀_id_comp, Ext.comp_mk₀_id]
  right_inv g := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
      Ext.mk₀_id_comp, Ext.comp_mk₀_id]

/-! ### Object isomorphisms: localizing `S` and `S ⧸ I` -/

/-- `LocalizedModule 𝔪 S` is `Localization 𝔪` as a `Localization 𝔪`-module. -/
noncomputable def ringLocEquiv : LocalizedModule 𝔪 S ≃ₗ[Localization 𝔪] Localization 𝔪 :=
  LinearEquiv.extendScalarsOfIsLocalization 𝔪 (Localization 𝔪)
    (IsLocalizedModule.iso 𝔪 (Algebra.linearMap S (Localization 𝔪)))

/-- The localization of `S` (as an object of `ModuleCat`) is `Localization 𝔪`. -/
noncomputable def ringObjIso :
    (ModuleCat.localizedModuleFunctor.{u} 𝔪).obj (ModuleCat.of S S)
      ≅ ModuleCat.of (Localization 𝔪) (Localization 𝔪) :=
  ((Shrink.linearEquiv (Localization 𝔪) (LocalizedModule 𝔪 S)).trans (ringLocEquiv 𝔪)).toModuleIso

/-- `ringLocEquiv` sends `mkLinearMap x` to `algebraMap x`. -/
lemma ringLocEquiv_mkLinearMap (x : S) :
    (ringLocEquiv 𝔪) (LocalizedModule.mkLinearMap 𝔪 S x)
      = algebraMap S (Localization 𝔪) x := by
  rw [LocalizedModule.mkLinearMap_apply, ringLocEquiv]
  simp [IsLocalizedModule.iso_mk_one]

/-- Under `ringLocEquiv`, the localized submodule `I.localized 𝔪` corresponds to the extended
ideal `I.map (algebraMap S (Localization 𝔪))`. -/
lemma hmap (I : Ideal S) :
    Submodule.map (ringLocEquiv 𝔪).toLinearMap (I.localized 𝔪)
      = I.map (algebraMap S (Localization 𝔪)) := by
  rw [Submodule.localized, Submodule.localized'_eq_span, Submodule.map_span,
    ← Set.image_comp, Ideal.map, ← Ideal.submodule_span_eq]
  congr 1
  ext y
  simp only [Set.mem_image, Function.comp_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (ringLocEquiv_mkLinearMap 𝔪 x).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, ringLocEquiv_mkLinearMap 𝔪 x⟩

/-- The localization of `S ⧸ I` is `Localization 𝔪 ⧸ I.map (algebraMap …)`.
This is base change of a quotient module along the flat map `S → Localization 𝔪`. -/
noncomputable def quotObjIso (I : Ideal S) :
    (ModuleCat.localizedModuleFunctor.{u} 𝔪).obj (ModuleCat.of S (S ⧸ I))
      ≅ ModuleCat.of (Localization 𝔪)
        (Localization 𝔪 ⧸ I.map (algebraMap S (Localization 𝔪))) :=
  (((Shrink.linearEquiv (Localization 𝔪) (LocalizedModule 𝔪 (S ⧸ I))).trans
    ((LinearEquiv.extendScalarsOfIsLocalization 𝔪 (Localization 𝔪)
      (IsLocalizedModule.iso 𝔪 (I.toLocalizedQuotient 𝔪))).trans
      (Submodule.Quotient.equiv (I.localized 𝔪)
        (I.map (algebraMap S (Localization 𝔪))) (ringLocEquiv 𝔪) (hmap 𝔪 I))))).toModuleIso

/-! ### Helpers for the flat base change induction -/

/-- Every element of `𝔪` acts invertibly on any module over `Localization 𝔪`. -/
private lemma isUnit_algebraMap_end (M' : Type*) [AddCommGroup M']
    [Module (Localization 𝔪) M'] [Module S M'] [IsScalarTower S (Localization 𝔪) M'] (x : 𝔪) :
    IsUnit (algebraMap S (Module.End S M') x) := by
  rw [← (Algebra.lsmul S (A := Localization 𝔪) S M').commutes]
  exact (IsLocalization.map_units (Localization 𝔪) x).map _

/-- Bridge: an `S`-linear map into an `S`-module is a localization at `𝔪` iff the canonical
map out of `LocalizedModule 𝔪` (given by `LocalizedModule.lift`) is bijective. -/
private lemma isLocalizedModule_iff_bijective_lift {M M' : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup M'] [Module S M'] (f : M →ₗ[S] M')
    (h : ∀ x : 𝔪, IsUnit (algebraMap S (Module.End S M') x)) :
    IsLocalizedModule 𝔪 f ↔ Function.Bijective (LocalizedModule.lift 𝔪 f h) := by
  constructor
  · intro hf
    haveI := hf
    have heq : LocalizedModule.lift 𝔪 f h = (IsLocalizedModule.iso 𝔪 f).toLinearMap :=
      LocalizedModule.lift_unique 𝔪 f h _ (by
        ext x; simp [IsLocalizedModule.iso_mk_one, LocalizedModule.mkLinearMap_apply])
    rw [heq]
    exact (IsLocalizedModule.iso 𝔪 f).bijective
  · intro hbij
    have h2 : IsLocalizedModule 𝔪
        (LocalizedModule.lift 𝔪 f h ∘ₗ LocalizedModule.mkLinearMap 𝔪 M) :=
      (IsLocalizedModule.comp_iff_of_bijective_left 𝔪 (LocalizedModule.lift 𝔪 f h) hbij).mpr
        inferInstance
    rwa [LocalizedModule.lift_comp] at h2

/-- **Base case of flat base change for Ext** (`n = 0`). Conjugating `mapExtLinearMap … 0`
through `Ext.linearEquiv₀`/`homLinearEquiv` yields `IsLocalizedModule.mapExtendScalars`, which is a
localization because `X` is finitely presented. The two `Module S`-structures on the `L`-linear
hom-space (the `LocalizedModule` one and the `ModuleCat.Algebra` one) are provably-equal but not
defeq, so the transfer is done at the level of `Function.Bijective` of `LocalizedModule.lift`. -/
private lemma isLocalizedModule_mapExt_zero [IsNoetherianRing S] (X Y : ModuleCat.{u} S)
    [Module.Finite S X] :
    IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y 0) := by
  haveI : Module.FinitePresentation S X := Module.finitePresentation_of_finite S X
  -- Pin the `Module S`-structure on the localized objects to the `Localization`/`LocalizedModule`
  -- one (the structure `mapExtendScalars` uses), matching `g` below. Together with its scalar
  -- tower and `SMulCommClass`, this avoids the (non-defeq) scoped `ModuleCat.Algebra`-vs-
  -- `LocalizedModule` `Module S` instance diamond on the `Localization 𝔪`-linear hom-space.
  letI iX : Module S ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X) :=
    ModuleCat.instModuleCarrierLocalizationLocalizedModule X 𝔪
  letI iY : Module S ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y) :=
    ModuleCat.instModuleCarrierLocalizationLocalizedModule Y 𝔪
  letI tX : IsScalarTower S (Localization 𝔪) ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X) :=
    inferInstanceAs (IsScalarTower S (Localization 𝔪) (X.localizedModule 𝔪))
  letI tY : IsScalarTower S (Localization 𝔪) ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y) :=
    inferInstanceAs (IsScalarTower S (Localization 𝔪) (Y.localizedModule 𝔪))
  letI cX : SMulCommClass (Localization 𝔪) S ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X) :=
    ⟨fun l s z => by rw [← IsScalarTower.algebraMap_smul (Localization 𝔪) s z,
      ← IsScalarTower.algebraMap_smul (Localization 𝔪) s (l • z), smul_smul, smul_smul, mul_comm]⟩
  letI cY : SMulCommClass (Localization 𝔪) S ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y) :=
    ⟨fun l s z => by rw [← IsScalarTower.algebraMap_smul (Localization 𝔪) s z,
      ← IsScalarTower.algebraMap_smul (Localization 𝔪) s (l • z), smul_smul, smul_smul, mul_comm]⟩
  -- source identification `Ext X Y 0 ≃ₗ[S] (X →ₗ[S] Y)` and the (diamond-free, `L`-linear) target
  -- identification `Ext (FX) (FY) 0 ≃ₗ[L] (FX →ₗ[L] FY)`
  set eS : Ext X Y 0 ≃ₗ[S] (X →ₗ[S] Y) :=
    (Ext.linearEquiv₀).trans ModuleCat.homLinearEquiv with heS
  set w : Ext ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X)
        ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y) 0 ≃ₗ[Localization 𝔪]
      (↑((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X)
        →ₗ[Localization 𝔪] ↑((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y)) :=
    (Ext.linearEquiv₀ (R := Localization 𝔪)).trans ModuleCat.homLinearEquiv with hw
  set M := (ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y 0 with hM
  -- `g` is the localization map on the hom-space, a localization because `X` is finitely presented
  set g := IsLocalizedModule.mapExtendScalars 𝔪 (X.localizedModuleMkLinearMap 𝔪)
    (Y.localizedModuleMkLinearMap 𝔪) (Localization 𝔪) with hg
  haveI hgL : IsLocalizedModule 𝔪 g := inferInstance
  have hlin : ∀ q : ((ModuleCat.localizedModuleFunctor.{u} 𝔪).obj X ⟶
      (ModuleCat.localizedModuleFunctor.{u} 𝔪).obj Y),
      (Ext.linearEquiv₀ (R := Localization 𝔪)) (Ext.mk₀ q) = q := by
    intro q; rw [← Ext.linearEquiv₀_symm_apply (R := Localization 𝔪)]
    exact LinearEquiv.apply_symm_apply _ _
  -- the comparison map `M` is, through `eS`/`w`, exactly the hom-space localization map `g`
  have keyw : ∀ e, w (M e) = g (eS e) := by
    intro e
    simp only [hM, heS, hw, hg, LinearEquiv.trans_apply, ModuleCat.homLinearEquiv_apply,
      Functor.mapExtLinearMap_apply, Ext.mapExactFunctor₀, Function.comp_apply,
      Ext.homEquiv₀_symm_apply, hlin]
    rfl
  -- transfer the three localization axioms from `g` to `M` through `eS` and `w`
  refine ⟨?_, ?_, ?_⟩
  · intro s
    exact isUnit_algebraMap_end 𝔪 _ s
  · intro y
    obtain ⟨⟨φ, t⟩, ht⟩ := IsLocalizedModule.surj 𝔪 g (w y)
    refine ⟨⟨eS.symm φ, t⟩, ?_⟩
    apply w.injective
    rw [keyw, eS.apply_symm_apply, ← ht]
    exact LinearMapClass.map_smul_of_tower w (t : S) y
  · intro x₁ x₂ he
    have hgg : g (eS x₁) = g (eS x₂) := by rw [← keyw, ← keyw, he]
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := 𝔪) (f := g) hgg
    refine ⟨c, eS.injective ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul,
      ← Submonoid.smul_def, ← Submonoid.smul_def]
    exact hc

/-- A pointwise-commuting square of `S`-linear maps `ρ' ∘ iP = iK ∘ ρ` localizes: the
localized lifts of the verticals `iP, iK` (against `𝔪`-inverting units `hU_P, hU_K`)
intertwine `ρ'` with the localized map of `ρ`. The naturality core shared by the two
ladder squares of `isLocalizedModule_mapExt_succ`. -/
private lemma localizedLift_comp_map_eq {M₁ M₂ N₁ N₂ : Type u}
    [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    [AddCommGroup N₁] [Module S N₁] [AddCommGroup N₂] [Module S N₂]
    (iP : M₁ →ₗ[S] N₁) (hU_P : ∀ x : 𝔪, IsUnit (algebraMap S (Module.End S N₁) x))
    (iK : M₂ →ₗ[S] N₂) (hU_K : ∀ x : 𝔪, IsUnit (algebraMap S (Module.End S N₂) x))
    (ρ : M₁ →ₗ[S] M₂) (ρ' : N₁ →ₗ[S] N₂) (hnat : ∀ e, ρ' (iP e) = iK (ρ e)) :
    ρ'.comp (LocalizedModule.lift 𝔪 iP hU_P)
      = (LocalizedModule.lift 𝔪 iK hU_K).comp
          (IsLocalizedModule.map 𝔪 (LocalizedModule.mkLinearMap 𝔪 M₁)
            (LocalizedModule.mkLinearMap 𝔪 M₂) ρ) := by
  apply IsLocalizedModule.ext 𝔪 (LocalizedModule.mkLinearMap 𝔪 M₁) hU_K
  ext e
  show ρ' (LocalizedModule.lift 𝔪 iP hU_P (LocalizedModule.mkLinearMap 𝔪 M₁ e))
    = LocalizedModule.lift 𝔪 iK hU_K
        (IsLocalizedModule.map 𝔪 (LocalizedModule.mkLinearMap 𝔪 M₁)
          (LocalizedModule.mkLinearMap 𝔪 M₂) ρ (LocalizedModule.mkLinearMap 𝔪 M₁ e))
  rw [IsLocalizedModule.map_apply]
  simp only [LocalizedModule.mkLinearMap_apply, LocalizedModule.lift_mk_one]
  exact hnat e

/-- **Inductive step of flat base change for Ext.** Assuming the statement at degree `n` for every
finite module (hypothesis `ih`), it holds at degree `n + 1`. This is the five-lemma argument on the
localized contravariant `Ext` long exact sequence of a finite projective presentation
`0 → K → P → X → 0` of `X`. Unlike the base case, this step only involves the (diamond-free) `Ext`
modules, never the localized hom-space. -/
private lemma isLocalizedModule_mapExt_succ [IsNoetherianRing S] (Y : ModuleCat.{u} S) (n : ℕ)
    (ih : ∀ (X : ModuleCat.{u} S) [Module.Finite S X],
      IsLocalizedModule 𝔪
        ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y n))
    (X : ModuleCat.{u} S) [Module.Finite S X] :
    IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y (n + 1)) := by
  set F := ModuleCat.localizedModuleFunctor.{u} 𝔪 with hF
  -- finite projective presentation `0 → K → P → X → 0`
  obtain ⟨P, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation S X
  set 𝒮 : ShortComplex (ModuleCat.{u} S) := (f : P →ₗ[S] X).shortComplexKer with h𝒮def
  have h𝒮 : 𝒮.ShortExact := LinearMap.shortExact_shortComplexKer surjf
  haveI : Module.Finite S 𝒮.X₁ := inferInstanceAs (Module.Finite S ↥(LinearMap.ker f))
  haveI : Module.Finite S 𝒮.X₂ := inferInstanceAs (Module.Finite S P)
  haveI : Projective 𝒮.X₂ := inferInstanceAs (Projective (ModuleCat.of S P))
  haveI : Projective (F.obj 𝒮.X₂) := inferInstance
  haveI : Projective (𝒮.map F).X₂ := (inferInstance : Projective (F.obj 𝒮.X₂))
  -- comparison verticals
  set iP := F.mapExtLinearMap S 𝒮.X₂ Y n with hiP
  set iK := F.mapExtLinearMap S 𝒮.X₁ Y n with hiK
  set iX := F.mapExtLinearMap S 𝒮.X₃ Y (n + 1) with hiX
  have hU_P : ∀ x : 𝔪, IsUnit (algebraMap S (Module.End S (Ext (F.obj 𝒮.X₂) (F.obj Y) n)) x) :=
    isUnit_algebraMap_end 𝔪 _
  have hU_K : ∀ x : 𝔪, IsUnit (algebraMap S (Module.End S (Ext (F.obj 𝒮.X₁) (F.obj Y) n)) x) :=
    isUnit_algebraMap_end 𝔪 _
  have hU_X : ∀ x : 𝔪,
      IsUnit (algebraMap S (Module.End S (Ext (F.obj 𝒮.X₃) (F.obj Y) (n + 1))) x) :=
    isUnit_algebraMap_end 𝔪 _
  -- S-side and L-side long exact sequence maps
  set ρ := Ext.precompOfLinear (Ext.mk₀ 𝒮.f) S Y (zero_add n) with hρ
  set δ := Ext.precompOfLinear h𝒮.extClass S Y (add_comm 1 n) with hδ
  set ρ' := Ext.precompOfLinear (Ext.mk₀ (𝒮.map F).f) S (F.obj Y) (zero_add n) with hρ'
  set δ' := Ext.precompOfLinear (h𝒮.map_of_exact F).extClass S (F.obj Y) (add_comm 1 n) with hδ'
  -- localized top-row maps
  set Lρ := IsLocalizedModule.map 𝔪 (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₂ Y n))
    (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₁ Y n)) ρ with hLρ
  set Lδ := IsLocalizedModule.map 𝔪 (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₁ Y n))
    (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₃ Y (n + 1))) δ with hLδ
  -- goal reduction
  show IsLocalizedModule 𝔪 iX
  rw [isLocalizedModule_iff_bijective_lift 𝔪 iX hU_X]
  -- un-localized naturality squares
  have hnat1 : ∀ e, ρ' (iP e) = iK (ρ e) := by
    intro e
    simp only [hρ', hρ, hiP, hiK, Ext.precompOfLinear, Ext.bilinearCompOfLinear_apply_apply,
      Functor.mapExtLinearMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ShortComplex.map_f]
    rfl
  have hnat2 : ∀ e, δ' (iK e) = iX (δ e) := by
    intro e
    simp only [hδ', hδ, hiK, hiX, Ext.precompOfLinear, Ext.bilinearCompOfLinear_apply_apply,
      Functor.mapExtLinearMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
    rfl
  -- naturality of the localized ladder
  have hc₁ : ρ'.comp (LocalizedModule.lift 𝔪 iP hU_P)
      = (LocalizedModule.lift 𝔪 iK hU_K).comp Lρ := by
    rw [hLρ]; exact localizedLift_comp_map_eq 𝔪 iP hU_P iK hU_K ρ ρ' hnat1
  have hc₂ : δ'.comp (LocalizedModule.lift 𝔪 iK hU_K)
      = (LocalizedModule.lift 𝔪 iX hU_X).comp Lδ := by
    rw [hLδ]; exact localizedLift_comp_map_eq 𝔪 iK hU_K iX hU_X δ δ' hnat2
  -- exactness (S-side localized, and L-side)
  have hExactρδ : Function.Exact ρ δ :=
    (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.contravariant_sequence_exact₁' h𝒮 Y n (n + 1) (add_comm 1 n))
  have hf₁ : Function.Exact Lρ Lδ :=
    IsLocalizedModule.map_exact 𝔪 (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₂ Y n))
      (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₁ Y n))
      (LocalizedModule.mkLinearMap 𝔪 (Ext 𝒮.X₃ Y (n + 1))) ρ δ hExactρδ
  have hg₁ : Function.Exact ρ' δ' :=
    (ShortComplex.ab_exact_iff_function_exact _).1
      (Ext.contravariant_sequence_exact₁' (h𝒮.map_of_exact F) (F.obj Y) n (n + 1) (add_comm 1 n))
  -- surjectivity of the connecting maps (middle term projective)
  have hδsurj : Function.Surjective δ :=
    precomp_extClass_surjective_of_projective_X₂ Y h𝒮 n
  have hf₂ : Function.Surjective Lδ :=
    IsLocalizedModule.map_surjective 𝔪 _ _ δ hδsurj
  have hg₂ : Function.Surjective δ' :=
    precomp_extClass_surjective_of_projective_X₂ (F.obj Y) (h𝒮.map_of_exact F) n
  -- induction hypothesis at `K` and `P`
  have hbijP : Function.Surjective (LocalizedModule.lift 𝔪 iP hU_P) :=
    ((isLocalizedModule_iff_bijective_lift 𝔪 iP hU_P).mp (ih 𝒮.X₂)).surjective
  have hbijK : Function.Bijective (LocalizedModule.lift 𝔪 iK hU_K) :=
    (isLocalizedModule_iff_bijective_lift 𝔪 iK hU_K).mp (ih 𝒮.X₁)
  -- five lemma
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    Lρ Lδ ρ' δ' (LocalizedModule.lift 𝔪 iP hU_P) (LocalizedModule.lift 𝔪 iK hU_K)
    (LocalizedModule.lift 𝔪 iX hU_X) hc₁ hc₂ hf₁ hg₁ hbijP hbijK hf₂ hg₂

/-! ### Flat base change for `Ext` (the analytic core) -/

/-- **Flat base change for Ext.** For a finite module `X` over a Noetherian ring `S`, the
comparison map from `Ext_S(X, Y)` to `Ext_L(X_𝔪, Y_𝔪)` (`L = Localization 𝔪`) exhibits the
latter as the localization of the former at `𝔪`.

Everything downstream (`localizedModule_ext_subsingleton_iff`) is proved from it. It is a genuine,
mathlib-absent, PR-scale result, proved here by induction on `n` (generalizing `X`) from the two
helper lemmas `isLocalizedModule_mapExt_zero` (base case) and `isLocalizedModule_mapExt_succ`
(inductive step). The strategy mirrors `Functor.mapExt_bijective_of_preservesProjectiveObjects`
in `Mathlib/.../Ext/MapBijective.lean`, replacing "bijective for a fully faithful functor" by
"`IsLocalizedModule` for the localization functor":

* **Inductive step (proved).** Take a finite projective presentation `0 → K → P → X → 0`
  (`Module.exists_finite_presentation`; the syzygy `K` is finite over Noetherian `S`). `F` preserves
  projectives (`Functor.projective_obj`) and exactness (`ShortExact.map_of_exact`), and
  `Ext^{≥1}(projective, _) = 0` (`precomp_extClass_surjective_of_projective_X₂`). Localize the
  contravariant Ext long exact sequence (`Ext.contravariant_sequence_exact₁'`) for the SES —
  localization is exact (`IsLocalizedModule.map_exact`) — and apply the five lemma
  (`LinearMap.bijective_of_surjective_of_bijective_of_right_exact`) to the comparison ladder of
  `LocalizedModule.lift`s, whose neighbouring rungs are bijective by the induction hypothesis at
  degree `n` for the finite modules `K` and `P` (via `isLocalizedModule_iff_bijective_lift`).
  Naturality of the comparison comes from `Ext.mapExactFunctor_comp` and
  `Ext.mapExactFunctor_extClass`.
* **Base case `n = 0` (proved in `isLocalizedModule_mapExt_zero`).** Here
  `F.mapExtLinearMap S X Y 0`
  is, through `Ext.linearEquiv₀`/`ModuleCat.homLinearEquiv` (the identification `Ext _ _ 0 ≃ Hom`),
  the localization map `IsLocalizedModule.mapExtendScalars 𝔪 …` on the hom-space, which is a
  localization because `X` is finitely presented
  (`Module.FinitePresentation.isLocalizedModule_mapExtendScalars`). The only subtlety is a
  `Localization` instance-diamond: the `Ext`/`ModuleCat` hom-space carries the scoped
  `ModuleCat.Algebra` `Module S`-structure, while `mapExtendScalars` uses the `LocalizedModule` one;
  these are provably-equal but not defeq, so unifying them naively (which would touch
  `LocalizedModule.mk e s` for every `s`) is prohibitively expensive. We avoid the unification by
  pinning the `LocalizedModule` `Module S`-structure (plus its scalar tower and
  `SMulCommClass`) with `letI`, keeping the `L`-linear identification `w` diamond-free, and
  transferring the three localization axioms from `mapExtendScalars` to `mapExtLinearMap`
  elementwise through the bijections
  (only ever using `LocalizedModule.mk _ 1`, never a general `mk e s`). -/
lemma isLocalizedModule_mapExt [IsNoetherianRing S] (X Y : ModuleCat.{u} S)
    [Module.Finite S X] (n : ℕ) :
    IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S X Y n) := by
  induction n generalizing X with
  | zero => exact isLocalizedModule_mapExt_zero 𝔪 X Y
  | succ n ih => exact isLocalizedModule_mapExt_succ 𝔪 Y n (fun X _ => ih X) X

end ModuleCat.BaseChangeExt

open ModuleCat.BaseChangeExt in
/-- Flat base change for Ext: localizing the Ext module commutes with computing Ext over the
localization. -/
theorem localizedModule_ext_subsingleton_iff {S : Type u} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (q : PrimeSpectrum S) (i : ℕ) :
    Subsingleton (LocalizedModule q.asIdeal.primeCompl
        (Ext (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i))
      ↔ Subsingleton (Ext
          (ModuleCat.of (Localization q.asIdeal.primeCompl)
            (Localization q.asIdeal.primeCompl ⧸
              I.map (algebraMap S (Localization q.asIdeal.primeCompl))))
          (ModuleCat.of (Localization q.asIdeal.primeCompl)
            (Localization q.asIdeal.primeCompl)) i) := by
  set 𝔪 := q.asIdeal.primeCompl with h𝔪
  haveI : IsLocalizedModule 𝔪
      ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S
        (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i) :=
    isLocalizedModule_mapExt 𝔪 _ _ i
  -- localization of the Ext module identifies with Ext over the localization
  let e1 := IsLocalizedModule.iso 𝔪
    ((ModuleCat.localizedModuleFunctor.{u} 𝔪).mapExtLinearMap S
      (ModuleCat.of S (S ⧸ I)) (ModuleCat.of S S) i)
  -- transport Ext along the object isomorphisms
  let e2 := extEquivOfIso (quotObjIso 𝔪 I) (ringObjIso 𝔪) i
  exact Equiv.subsingleton_congr (e1.toEquiv.trans e2)
