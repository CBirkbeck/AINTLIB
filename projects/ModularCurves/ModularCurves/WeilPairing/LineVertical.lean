/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule
import ModularCurves.Picard.IdealModuleMono
import ModularCurves.ForMathlib.CrossProductKernel
import ModularCurves.ForMathlib.QuotientProductRankTwo
import ModularCurves.ForMathlib.SchemeModuleBaseCechZero
import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.UnitPullback

/-!
# The line and the vertical as rank-one kernels ([GAP-A-4])

The chord-and-tangent sections of the Weil-pairing construction (GME 2.6.4 Chain C):
the line `ℓ` through `[P] + [Q]` inside `H⁰(𝒪(3[0]))` and the vertical `v` through
`[R]` inside `H⁰(𝒪(2[0]))`, each cut out as the kernel of the global-sections
restriction to the divisor, each of rank one — the generator-up-to-unit that produces
the norm `N`.

This file starts with the ambient-module inclusion of an ideal module
(`idealModuleInclusion`), the mono that seeds every restriction cokernel downstream.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}} (J : C.IdealSheafData)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of the ideal module of `J` into the structure sheaf: componentwise
the subtype inclusion of `idealSections`. -/
noncomputable def idealModuleInclusion : idealModule J ⟶ unitObj C where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => (m.1 : Γ(C, U.unop))
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      naturality := fun {U V} i => by
        refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealModuleInclusion_app_apply (U : (TopologicalSpace.Opens ↥C)ᵒᵖ)
    (m : idealSections J U) :
    (idealModuleInclusion J).val.app U m = (m.1 : Γ(C, U.unop)) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : Mono (idealModuleInclusion J) := by
  constructor
  intro Z g h hgh
  ext U m
  have hval := congrArg (fun (q : Z ⟶ unitObj C) => q.val.app (op U) m) hgh
  have hg : (idealModuleInclusion J).val.app (op U) (g.val.app (op U) m) =
      (idealModuleInclusion J).val.app (op U) (h.val.app (op U) m) := hval
  exact Subtype.ext hg

section Twist

variable (L : C.Modules)

local instance (C : Scheme.{u}) :
    ∀ U, IsMulCommutative (C.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (C.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf-level action of the ideal module on any module — the whiskered
subtype inclusion followed by the left unitor. All naturality is the monoidal
structure's. -/
noncomputable def idealActionPre :
    ((idealModule J).val ⊗ L.val :
      _root_.PresheafOfModules (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      L.val :=
  MonoidalCategory.whiskerRight (idealModuleInclusion J).val L.val ≫
    (λ_ L.val).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The divisor twist map**: the sheafified action `I(J) ⊗ L ⟶ L`, the mono whose
cokernel is the restriction of `L` to the subscheme of `J`. Transpose of
`idealActionPre` through the sheafification adjunction (the `ev` idiom). -/
noncomputable def divisorTwistHom : tensorObj (idealModule J) L ⟶ L :=
  (PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id C.ringCatSheaf.obj)).homEquiv
      ((idealModule J).val ⊗ L.val) L |>.symm (idealActionPre J L)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem idealActionPre_app_tmul (U : (TopologicalSpace.Opens ↥C)ᵒᵖ)
    (m : idealSections J U) (l : L.val.obj U) :
    (idealActionPre J L).app U
        (m ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U] l) =
      (show ((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) from m.1) • l :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The generator equivalence of a principal nonzerodivisor ideal's sections:
`a ↦ a·g`. Self-contained from span + nzd. -/
private noncomputable def idealSectionsGenEquiv (V : C.affineOpens) (g : Γ(C, V.1))
    (hspan : J.ideal V = Ideal.span {g}) (hnzd : g ∈ nonZeroDivisors Γ(C, V.1)) :
    Γ(C, V.1) ≃ₗ[Γ(C, V.1)] idealSections J (Opposite.op V.1) := by
  have hIS : idealSections J (Opposite.op V.1) = J.ideal V :=
    J.ker_subschemeι_app V
  have hmem : ∀ a : Γ(C, V.1), a * g ∈ idealSections J (Opposite.op V.1) := by
    intro a
    have : a * g ∈ J.ideal V := by
      rw [hspan]
      exact Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self g)
    rw [hIS]
    exact this
  refine LinearEquiv.ofBijective
    { toFun := fun a => ⟨a * g, hmem a⟩
      map_add' := fun a b => Subtype.ext (add_mul a b g)
      map_smul' := fun r a => Subtype.ext (by
        show (r * a) * g = r * (a * g)
        rw [mul_assoc]) } ⟨?_, ?_⟩
  · intro a b hab
    have h1 : a * g = b * g := congrArg Subtype.val hab
    exact (mul_cancel_right_mem_nonZeroDivisors hnzd).mp h1
  · rintro ⟨m, hm⟩
    have hm' : m ∈ Ideal.span {g} := by
      rw [← hspan, ← hIS]
      exact hm
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hm'
    exact ⟨a, Subtype.ext ha⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a chart where the ideal is a principal nonzerodivisor span and scalar
multiplication by the generator acts injectively on the module's sections, the
componentwise action of the ideal module is injective. -/
private theorem idealActionPre_app_injective_of_span
    (V : C.affineOpens) (g : Γ(C, V.1))
    (hspan : J.ideal V = Ideal.span {g}) (hnzd : g ∈ nonZeroDivisors Γ(C, V.1))
    (hLinj : Function.Injective ((L.smul (U := V.1) g).hom)) :
    Function.Injective ((idealActionPre J L).app (Opposite.op V.1)) := by
  have hsurj : Function.Surjective
      (LinearMap.rTensor (L.val.obj (Opposite.op V.1))
        (idealSectionsGenEquiv J V g hspan hnzd).toLinearMap) :=
    LinearMap.rTensor_surjective _
      (g := (idealSectionsGenEquiv J V g hspan hnzd).toLinearMap)
      (idealSectionsGenEquiv J V g hspan hnzd).surjective
  have key : ∀ w, (idealActionPre J L).app (Opposite.op V.1)
      (LinearMap.rTensor (L.val.obj (Opposite.op V.1))
        (idealSectionsGenEquiv J V g hspan hnzd).toLinearMap w) =
      (show ((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V.1))
        from g) • (TensorProduct.lid _ _ w) := by
    intro w
    induction w with
    | zero => simp
    | add a b ha hb =>
        rw [map_add, map_add, ha, hb, map_add, smul_add]
    | tmul a l =>
        rw [LinearMap.rTensor_tmul]
        erw [idealActionPre_app_tmul]
        erw [TensorProduct.lid_tmul]
        show ((a * g : Γ(C, V.1)) :
          ((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (Opposite.op V.1))) • l = _
        rw [mul_comm]
        exact mul_smul g a l
  intro x y hxy
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  have h2 := (key x').symm.trans (hxy.trans (key y'))
  have h2' : (L.smul (U := V.1) g).hom ((TensorProduct.lid _ _) x') =
      (L.smul (U := V.1) g).hom ((TensorProduct.lid _ _) y') := h2
  have h3 := hLinj h2'
  have h4 := (TensorProduct.lid _ _).injective h3
  rw [h4]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scalar multiplication by a nonzerodivisor is injective on the sections of a
module trivialized on the open: `smul_restrictAppIso_inv` identifies it with the
restricted module's scalar action, which the trivialization conjugates to
multiplication on the structure sheaf of the open subscheme. -/
private theorem smul_injective_of_restrict_triv {W : C.Opens}
    (e : L.restrict W.ι ≅ unitObj W.toScheme)
    (g' : Γ(C, W)) (hg' : g' ∈ nonZeroDivisors Γ(C, W)) :
    Function.Injective ((L.smul (U := W) g').hom) := by
  have inner : ∀ g'' ∈ nonZeroDivisors Γ(C, W.ι ''ᵁ (⊤ : W.toScheme.Opens)),
      Function.Injective
        ((L.smul (U := W.ι ''ᵁ (⊤ : W.toScheme.Opens)) g'').hom) := by
    intro g'' hg''
    -- the module smul IS the restricted module's smul at the transported scalar:
    -- restrict-scalars acts through the appIso, and inv ∘ hom cancels
    have hEnd : (L.restrict W.ι).smul
        ((W.ι.appIso (⊤ : W.toScheme.Opens)).hom.hom g'') =
        L.smul (U := W.ι ''ᵁ (⊤ : W.toScheme.Opens))
          ((W.ι.appIso (⊤ : W.toScheme.Opens)).inv.hom
            ((W.ι.appIso (⊤ : W.toScheme.Opens)).hom.hom g'')) := rfl
    have hcanc : (W.ι.appIso (⊤ : W.toScheme.Opens)).inv.hom
        ((W.ι.appIso (⊤ : W.toScheme.Opens)).hom.hom g'') = g'' := by
      have := ConcreteCategory.congr_hom
        (W.ι.appIso (⊤ : W.toScheme.Opens)).hom_inv_id g''
      exact this
    rw [hcanc] at hEnd
    rw [← hEnd]
    -- conjugate the restricted smul through the trivialization's global component
    set r₀ := (W.ι.appIso (⊤ : W.toScheme.Opens)).hom.hom g'' with hr₀def
    have hr₀ : r₀ ∈ nonZeroDivisors Γ(W.toScheme, (⊤ : W.toScheme.Opens)) := by
      rw [hr₀def, ← MulEquivClass.map_nonZeroDivisors
        (W.ι.appIso (⊤ : W.toScheme.Opens)).commRingCatIsoToRingEquiv]
      exact ⟨g'', hg'', rfl⟩
    intro x y hxy
    have hΦiso : IsIso (e.hom.app (⊤ : W.toScheme.Opens)) :=
      Hom.isIso_iff_isIso_app.mp inferInstance _
    have hΦbij := (ConcreteCategory.isIso_iff_bijective
      (e.hom.app (⊤ : W.toScheme.Opens))).mp hΦiso
    let x' : Γ(L.restrict W.ι, (⊤ : W.toScheme.Opens)) := x
    let y' : Γ(L.restrict W.ι, (⊤ : W.toScheme.Opens)) := y
    have hxy2 : e.hom.app (⊤ : W.toScheme.Opens) (r₀ • x') =
        e.hom.app (⊤ : W.toScheme.Opens) (r₀ • y') := by
      have h1 : r₀ • x' = ((L.restrict W.ι).smul r₀).hom x' := rfl
      have h2 : r₀ • y' = ((L.restrict W.ι).smul r₀).hom y' := rfl
      rw [h1, h2]
      exact congrArg (fun t => e.hom.app (⊤ : W.toScheme.Opens) t) hxy
    rw [Hom.app_smul, Hom.app_smul] at hxy2
    let u : Γ(W.toScheme, (⊤ : W.toScheme.Opens)) :=
      e.hom.app (⊤ : W.toScheme.Opens) x'
    let v : Γ(W.toScheme, (⊤ : W.toScheme.Opens)) :=
      e.hom.app (⊤ : W.toScheme.Opens) y'
    have hmul : r₀ * u = r₀ * v := hxy2
    have hcancel : u = v := (mul_cancel_left_mem_nonZeroDivisors hr₀).mp hmul
    have hfin : x' = y' := hΦbij.injective hcancel
    exact hfin
  have heq : W.ι ''ᵁ (⊤ : W.toScheme.Opens) = W := by
    simp
  rw [heq] at inner
  exact inner g' hg'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The presheaf action of a locally principal nonzerodivisor ideal on an invertible
module is locally injective**: on a common refinement of the principal cover and the
trivializing cover, the componentwise action is injective
(`idealActionPre_app_injective_of_span` + `smul_injective_of_restrict_triv`), and
injectivity of the restriction is exactly the equalizer-sieve condition. -/
theorem isLocallyInjective_idealActionPre
    (h : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf _).map (idealActionPre J L)) := by
  obtain ⟨ι, Ut, hUt, htriv⟩ := hL
  constructor
  intro U x y hxy
  rw [Opens.mem_grothendieckTopology]
  intro c hcU
  obtain ⟨V, hcV, g, hspan, hnzd⟩ := h c
  have hcT : c ∈ iSup Ut := by rw [hUt]; trivial
  obtain ⟨i, hci⟩ := TopologicalSpace.Opens.mem_iSup.mp hcT
  have hopen : c ∈ U.unop ⊓ (V.1 ⊓ Ut i) := ⟨hcU, hcV, hci⟩
  obtain ⟨_, ⟨W, hWaff, rfl⟩, hcW, hsub⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open hopen
      (U.unop ⊓ (V.1 ⊓ Ut i)).2
  have hWU : W ≤ U.unop := fun a ha => (hsub ha).1
  have hWV : W ≤ V.1 := fun a ha => (hsub ha).2.1
  have hWT : W ≤ Ut i := fun a ha => (hsub ha).2.2
  refine ⟨W, homOfLE hWU, ?_, hcW⟩
  -- the descended generator on `W`
  have hspanW : J.ideal ⟨W, hWaff⟩ =
      Ideal.span {(C.presheaf.map (homOfLE hWV).op).hom g} := by
    rw [← Scheme.IdealSheafData.map_ideal' (I := J)
      (U := ⟨W, hWaff⟩) (V := V) ((homOfLE hWV).op), hspan,
      Ideal.map_span, Set.image_singleton]
  have hnzdW : (C.presheaf.map (homOfLE hWV).op).hom g ∈
      nonZeroDivisors Γ(C, W) := by
    have h1 := ModularCurves.affinePullbackSection_mem_nonZeroDivisors
      (𝟙 C) ⟨W, hWaff⟩ V (by simpa using hWV) hnzd
    rw [ModularCurves.affinePullbackSection_eq_appLE] at h1
    have h2 : (Scheme.Hom.appLE (𝟙 C) V.1 W (by simpa using hWV)).hom g =
        (C.presheaf.map (homOfLE hWV).op).hom g := by
      simp [Scheme.Hom.appLE, Scheme.Hom.id_app]
    rwa [h2] at h1
  -- injectivity of the component at `W`
  obtain ⟨eT⟩ := htriv i
  have hLinj := smul_injective_of_restrict_triv L
    (restrictIsoOfPullbackIso L W (restrictTrivialization hWT eT))
    ((C.presheaf.map (homOfLE hWV).op).hom g) hnzdW
  have hinj := idealActionPre_app_injective_of_span J L ⟨W, hWaff⟩
    ((C.presheaf.map (homOfLE hWV).op).hom g) hspanW hnzdW hLinj
  have hinj' : Function.Injective
      (((PresheafOfModules.toPresheaf _).map (idealActionPre J L)).app
        (Opposite.op W)) := hinj
  -- the equalizer condition: restrictions agree because the action values do
  refine hinj' ?_
  have hnx := NatTrans.naturality_apply
    ((PresheafOfModules.toPresheaf _).map (idealActionPre J L))
    (homOfLE hWU).op x
  have hny := NatTrans.naturality_apply
    ((PresheafOfModules.toPresheaf _).map (idealActionPre J L))
    (homOfLE hWU).op y
  rw [hnx, hny, hxy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Second-factor extraction of local injectivity, parametrized so the instance keys
unify at application position (across presheaf-clothing) instead of by typeclass
search. -/
private theorem isLocallyInjective_of_comp_fields
    {F₁ F₂ F₃ : (TopologicalSpace.Opens ↥C)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    (hcomp : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C) (f₁ ≫ f₂))
    (hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥C) f₁) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C) f₂ := by
  haveI := hcomp
  haveI := hsurj
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    (Opens.grothendieckTopology ↥C) f₁ f₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The divisor twist map is the sheafification of the presheaf action followed by
the counit (the `ev` idiom's identity). -/
theorem divisorTwistHom_eq :
    divisorTwistHom J L =
      (PresheafOfModules.sheafification
        (CategoryStruct.id C.ringCatSheaf.obj)).map (idealActionPre J L) ≫
        (sheafifyValIso L).hom := by
  have hCounit := (PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id C.ringCatSheaf.obj)).homEquiv_counit
    (X := (idealModule J).val ⊗ L.val) (Y := L) (g := idealActionPre J L)
  exact hCounit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The divisor twist map of a locally principal nonzerodivisor ideal into an
invertible module is a monomorphism.** Its presheaf action is locally injective, the
sheafification unit transports local injectivity to the sheafified map, and locally
injective maps of sheaves are monomorphisms. -/
theorem mono_divisorTwistHom
    (h : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L) :
    Mono (divisorTwistHom J L) := by
  classical
  haveI hφ := isLocallyInjective_idealActionPre J L h hL
  -- the sheafification units at source and target are in W, hence locally bijective
  have hWunitP : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components ((idealModule J).val ⊗ L.val)
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            ((idealModule J).val ⊗ L.val))) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  have hWunitL : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app L.val) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components L.val
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            L.val)) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  obtain ⟨-, hPsurj⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunitP
  obtain ⟨hLinj2, -⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunitL
  -- naturality of the unit
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 C.ringCatSheaf.obj)).unit.naturality (idealActionPre J L)
  rw [Functor.id_map] at hnat
  -- local injectivity of the composite, with goal-copied clothing
  haveI h1 : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf
        ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
          C.ringCatSheaf)).map (idealActionPre J L) ≫
        (PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app L.val)) := by
    haveI hφ' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map (idealActionPre J L)) := hφ
    haveI hu' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app L.val)) := hLinj2
    infer_instance
  rw [← Functor.map_comp, hnat, Functor.map_comp] at h1
  haveI := h1
  have h4 := isLocallyInjective_of_comp_fields _ _ h1 hPsurj
  -- the sheafified map is a mono: locally injective sheaf maps are monos, and the
  -- Ab-sheaf functor reflects monos
  haveI h5 : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf _).map
        ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).map
          (idealActionPre J L))) := h4
  haveI h6 : Mono ((SheafOfModules.toSheaf _).map
      ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).map
        (idealActionPre J L))) := Sheaf.mono_of_isLocallyInjective _
  haveI h7 : Mono ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).map
      (idealActionPre J L)) :=
    (SheafOfModules.toSheaf _).mono_of_mono_map h6
  rw [divisorTwistHom_eq]
  exact mono_comp _ _

section LineAssembly

open Matrix

variable {S : Scheme.{u}} {π : C ⟶ S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-d3] The kernel of the restriction to a degree-two divisor is spanned by the
Cramer line.** Hypothesis-slotted assembly: given a rank-3 basis `b3` of the ambient
base sections, coordinates `e2` for the base sections of the restriction cokernel, and
unimodularity of the cross product of the two evaluation rows, the kernel of the
restriction on base sections is free of rank one, spanned by the `b3`-vector of the
cross product — the chord-and-tangent line. -/
theorem ker_baseSectionsMap_cokernel_eq_span_crossProduct
    {M N : C.Modules} (f : M ⟶ N)
    (b3 : Module.Basis (Fin 3) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π N))
    (e2 : Scheme.Modules.baseSections π (Limits.cokernel f) ≃ₗ[Γ(S, (⊤ : S.Opens))]
      (Fin 2 → Γ(S, (⊤ : S.Opens))))
    (A : Fin 2 → Fin 3 → Γ(S, (⊤ : S.Opens)))
    (hA : ∀ i j, A i j =
      e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) (b3 j)) i)
    (huni : Ideal.span (Set.range ((A 0) ⨯₃ (A 1))) = ⊤) :
    LinearMap.ker
        ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens))
        {b3.equivFun.symm ((A 0) ⨯₃ (A 1))} := by
  have hcoord : ∀ x : Scheme.Modules.baseSections π N, ∀ i : Fin 2,
      e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) x) i =
        (A i) ⬝ᵥ (b3.equivFun x) := by
    intro x i
    conv_lhs => rw [← b3.sum_equivFun x]
    rw [map_sum, map_sum]
    rw [show (∑ j, e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f))
        (b3.equivFun x j • b3 j))) i =
      ∑ j, (b3.equivFun x j) *
        e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) (b3 j)) i from by
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [_root_.map_smul, _root_.map_smul]
      rfl]
    rw [show (A i) ⬝ᵥ (b3.equivFun x) = ∑ j, A i j * b3.equivFun x j from rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hA i j, mul_comm]
  ext x
  constructor
  · intro hx
    have hx0 : ∀ i : Fin 2, (A i) ⬝ᵥ (b3.equivFun x) = 0 := by
      intro i
      rw [← hcoord x i]
      have : (Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) x = 0 := hx
      rw [this, map_zero]
      rfl
    have hmem := ModularCurves.mem_span_crossProduct_of_dotProduct_eq_zero
      (A 0) (A 1) (b3.equivFun x) huni (hx0 0) (hx0 1)
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    have := congrArg (b3.equivFun.symm) hr
    rw [_root_.map_smul] at this
    simpa using this
  · intro hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hker : ∀ i : Fin 2,
        e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f))
          (r • b3.equivFun.symm ((A 0) ⨯₃ (A 1)))) i = 0 := by
      intro i
      rw [hcoord]
      rw [_root_.map_smul]
      rw [show b3.equivFun (b3.equivFun.symm ((A 0) ⨯₃ (A 1))) =
        (A 0) ⨯₃ (A 1) from b3.equivFun.apply_symm_apply _]
      rw [dotProduct_smul]
      fin_cases i
      · simp [dot_self_cross]
      · simp [dot_cross_self]
    have h2 : e2 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f))
        (r • b3.equivFun.symm ((A 0) ⨯₃ (A 1)))) = 0 := by
      funext i
      exact hker i
    have h3 := congrArg e2.symm h2
    rw [e2.symm_apply_apply, map_zero] at h3
    exact h3

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-e] The vertical**: the rank-two analogue — the kernel of the restriction to
a degree-one divisor is spanned by the perpendicular of the evaluation row. -/
theorem ker_baseSectionsMap_cokernel_eq_span_perp
    {M N : C.Modules} (f : M ⟶ N)
    (b2 : Module.Basis (Fin 2) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π N))
    (e1 : Scheme.Modules.baseSections π (Limits.cokernel f) ≃ₗ[Γ(S, (⊤ : S.Opens))]
      Γ(S, (⊤ : S.Opens)))
    (a : Fin 2 → Γ(S, (⊤ : S.Opens)))
    (ha : ∀ j, a j =
      e1 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) (b2 j)))
    (huni : Ideal.span (Set.range a) = ⊤) :
    LinearMap.ker
        ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens))
        {b2.equivFun.symm ![-(a 1), a 0]} := by
  have hcoord : ∀ x : Scheme.Modules.baseSections π N,
      e1 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f)) x) =
        a ⬝ᵥ (b2.equivFun x) := by
    intro x
    conv_lhs => rw [← b2.sum_equivFun x]
    rw [map_sum, map_sum]
    rw [show (a ⬝ᵥ (b2.equivFun x)) = ∑ j, a j * b2.equivFun x j from rfl]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [_root_.map_smul, _root_.map_smul, ha j]
    show b2.equivFun x j • _ = _
    rw [smul_eq_mul, mul_comm]
  ext x
  constructor
  · intro hx
    have hx0 : a ⬝ᵥ (b2.equivFun x) = 0 := by
      rw [← hcoord x]
      have hzero : (Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π f)) x = 0 := hx
      rw [hzero, map_zero]
    have hmem := ModularCurves.mem_span_perp_of_dotProduct_eq_zero
      a (b2.equivFun x) huni hx0
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    refine Submodule.mem_span_singleton.mpr ⟨r, ?_⟩
    have := congrArg (b2.equivFun.symm) hr
    rw [_root_.map_smul] at this
    simpa using this
  · intro hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hker : e1 ((Scheme.Modules.baseSectionsMap π (Limits.cokernel.π f))
        (r • b2.equivFun.symm ![-(a 1), a 0])) = 0 := by
      rw [hcoord]
      rw [_root_.map_smul]
      rw [show b2.equivFun (b2.equivFun.symm ![-(a 1), a 0]) =
        ![-(a 1), a 0] from b2.equivFun.apply_symm_apply _]
      rw [dotProduct_smul]
      rw [show a ⬝ᵥ ![-(a 1), a 0] = 0 from ModularCurves.dotProduct_perp a]
      exact smul_zero r
    have h3 := congrArg e1.symm hker
    rw [e1.symm_apply_apply, map_zero] at h3
    exact h3

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Adjunction-triangle evaluation for the divisor twist: on unit images, the twist is
the presheaf action. -/
theorem divisorTwistHom_app_unit (U : (TopologicalSpace.Opens ↥C)ᵒᵖ)
    (x : ToType ((((idealModule J).val ⊗ L.val :
      _root_.PresheafOfModules
        (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).obj U)) :
    (divisorTwistHom J L).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (CategoryStruct.id C.ringCatSheaf.obj)).unit.app
            ((idealModule J).val ⊗ L.val)).app U x) =
      (idealActionPre J L).app U x := by
  have htri := ((PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id C.ringCatSheaf.obj)).homEquiv
      ((idealModule J).val ⊗ L.val) L).apply_symm_apply (idealActionPre J L)
  rw [Adjunction.homEquiv_unit] at htri
  have hval := congrArg (fun (m : ((idealModule J).val ⊗ L.val :
      _root_.PresheafOfModules
        (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 C.ringCatSheaf.obj)).obj L) =>
    (ConcreteCategory.hom (m.app U)) x) htri
  exact hval

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Support vanishing**: off the divisor, the restriction cokernel of the twist is
zero — where the ideal contains `1`, the twist is an epimorphism because every section
is the action value of `1 ⊗ₜ` itself. -/
theorem isZero_restrict_cokernel_divisorTwistHom (V : C.Opens)
    (htriv : ∀ (W : C.Opens), W ≤ V →
      (1 : Γ(C, W)) ∈ idealSections J (Opposite.op W)) :
    Limits.IsZero ((restrictFunctor V.ι).obj
      (Limits.cokernel (divisorTwistHom J L))) := by
  haveI hsurj : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology ↥V.toScheme)
      ((PresheafOfModules.toPresheaf _).map
        ((restrictFunctor V.ι).map (divisorTwistHom J L)).val) := by
    constructor
    intro W' s
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hWle : V.ι ''ᵁ W' ≤ V := V.ι_image_le W'
    let s' : (L.val.obj (Opposite.op (V.ι ''ᵁ W'))) := s
    refine ⟨W', 𝟙 W', ?_, hx⟩
    refine ⟨((PresheafOfModules.sheafificationAdjunction
      (CategoryStruct.id C.ringCatSheaf.obj)).unit.app
        ((idealModule J).val ⊗ L.val)).app (Opposite.op (V.ι ''ᵁ W'))
        ((⟨(1 : Γ(C, V.ι ''ᵁ W')), htriv _ hWle⟩ :
          idealSections J (Opposite.op (V.ι ''ᵁ W'))) ⊗ₜ[
            (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (Opposite.op (V.ι ''ᵁ W'))] s'), ?_⟩
    have heval := divisorTwistHom_app_unit J L (Opposite.op (V.ι ''ᵁ W'))
      ((⟨(1 : Γ(C, V.ι ''ᵁ W')), htriv _ hWle⟩ :
        idealSections J (Opposite.op (V.ι ''ᵁ W'))) ⊗ₜ[
          (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
            (Opposite.op (V.ι ''ᵁ W'))] s')
    have hact := idealActionPre_app_tmul J L (Opposite.op (V.ι ''ᵁ W'))
      (⟨(1 : Γ(C, V.ι ''ᵁ W')), htriv _ hWle⟩ :
        idealSections J (Opposite.op (V.ι ''ᵁ W'))) s'
    have hone : (idealActionPre J L).app (Opposite.op (V.ι ''ᵁ W'))
        ((⟨(1 : Γ(C, V.ι ''ᵁ W')), htriv _ hWle⟩ :
          idealSections J (Opposite.op (V.ι ''ᵁ W'))) ⊗ₜ[
            (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (Opposite.op (V.ι ''ᵁ W'))] s') = s' := by
      rw [hact]
      exact one_smul _ s'
    show ((restrictFunctor V.ι).map (divisorTwistHom J L)).val.app
        (Opposite.op W') _ = _
    have hfin := heval.trans hone
    calc ((restrictFunctor V.ι).map (divisorTwistHom J L)).val.app
          (Opposite.op W') _
        = (divisorTwistHom J L).val.app (Opposite.op (V.ι ''ᵁ W')) _ := rfl
      _ = s' := hfin
      _ = _ := by
          rw [show (((PresheafOfModules.toPresheaf _).obj
            ((restrictFunctor V.ι).obj L).val).map (𝟙 W').op) s = s from by
              rw [op_id, CategoryTheory.Functor.map_id]
              rfl]
  haveI hepi2 : Epi ((SheafOfModules.toSheaf _).map
      ((restrictFunctor V.ι).map (divisorTwistHom J L))) := by
    haveI : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        ((restrictFunctor V.ι).map (divisorTwistHom J L))) := hsurj
    exact Sheaf.epi_of_isLocallySurjective _
  haveI hepi : Epi ((restrictFunctor V.ι).map (divisorTwistHom J L)) :=
    (SheafOfModules.toSheaf _).epi_of_epi_map hepi2
  have hz := Limits.isZero_cokernel_of_epi
    ((restrictFunctor V.ι).map (divisorTwistHom J L))
  exact hz.of_iso (Limits.PreservesCokernel.iso (restrictFunctor V.ι)
    (divisorTwistHom J L))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Concentration on a divisor neighborhood**: global sections of the twist cokernel
restrict bijectively to any open whose complementary open misses the divisor. -/
theorem cokernel_divisorTwistHom_bijective_restrict (U V : C.Opens)
    (hUV : U ⊔ V = ⊤)
    (htriv : ∀ (W : C.Opens), W ≤ V →
      (1 : Γ(C, W)) ∈ idealSections J (Opposite.op W)) :
    Function.Bijective fun s :
        Γ(Limits.cokernel (divisorTwistHom J L), (⊤ : C.Opens)) ↦
      (Limits.cokernel (divisorTwistHom J L)).presheaf.map
        (homOfLE (le_top : U ≤ (⊤ : C.Opens))).op s := by
  let M := Limits.cokernel (divisorTwistHom J L)
  let F := (SheafOfModules.toSheaf C.ringCatSheaf).obj M
  have hzeroV : Limits.IsZero ((restrictFunctor V.ι).obj M) :=
    isZero_restrict_cokernel_divisorTwistHom J L V htriv
  haveI hVsections : Subsingleton Γ(M, V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict M V hzeroV
  haveI hVsheaf : Subsingleton (ToType (F.1.obj (Opposite.op V))) := by
    change Subsingleton Γ(M, V)
    infer_instance
  have htrivOverlap : ∀ (W : C.Opens), W ≤ U ⊓ V →
      (1 : Γ(C, W)) ∈ idealSections J (Opposite.op W) :=
    fun W hW => htriv W (le_trans hW inf_le_right)
  have hzeroOverlap : Limits.IsZero ((restrictFunctor (U ⊓ V).ι).obj M) :=
    isZero_restrict_cokernel_divisorTwistHom J L (U ⊓ V) htrivOverlap
  haveI hoverlap : Subsingleton Γ(M, U ⊓ V) :=
    Scheme.Modules.subsingleton_sections_of_isZero_restrict M (U ⊓ V)
      hzeroOverlap
  haveI hoverlapSheaf : Subsingleton (ToType (F.1.obj (Opposite.op (U ⊓ V)))) := by
    change Subsingleton Γ(M, U ⊓ V)
    infer_instance
  exact TopCat.Sheaf.bijective_restrict_of_sup_eq_top_of_subsingleton F hUV

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a chart where both section kernels are principal, the pair divisor's ideal is
the principal span of the product of the generators. -/
theorem sectionsDivisor_pair_ideal_span {S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (P Q : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens) (rP rQ : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ}) :
    (ModularCurves.RelEffCartierDiv.sectionsDivisor π ![P, Q]).ideal.ideal U =
      Ideal.span {rP * rQ} := by
  rw [ModularCurves.RelEffCartierDiv.sectionsDivisor_ideal π hsm ![P, Q]]
  rw [show (∏ i, Scheme.Hom.ker ((![P, Q]) i).1) =
      Scheme.Hom.ker P.1 * Scheme.Hom.ker Q.1 from by
    rw [Fin.prod_univ_two]
    rfl]
  rw [show (Scheme.Hom.ker P.1 * Scheme.Hom.ker Q.1).ideal U =
      (Scheme.Hom.ker P.1).ideal U * (Scheme.Hom.ker Q.1).ideal U from by
    rw [Scheme.IdealSheafData.ideal_mul]
    rfl]
  rw [hP, hQ, Ideal.span_singleton_mul_span_singleton]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The single-chart restriction trivialization of an ideal module with a principal
nonzerodivisor generator (the `isInvertible_idealModule` tail, extracted): the
generator morphism is an isomorphism onto the restricted ideal module. -/
noncomputable def idealModuleRestrictTrivOfSpan {J : C.IdealSheafData}
    (U : C.affineOpens) (g : Γ(C, U.1))
    (hspan : J.ideal U = Ideal.span {g})
    (hnzd : g ∈ nonZeroDivisors Γ(C, U.1)) :
    (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme := by
  have hgmem : g ∈ idealSections J (Opposite.op U.1) := by
    rw [show idealSections J (Opposite.op U.1) = J.ideal U from
      J.ker_subschemeι_app U, hspan]
    exact Ideal.mem_span_singleton_self g
  haveI : IsIso (idealGenHom J U.1 g hgmem) := by
    refine isIso_of_bijective_app_on_basis _
      {W | ∃ (b : Γ(C, U.1)) (_ : C.basicOpen b ≤ U.1),
        W = U.1.ι ⁻¹ᵁ C.basicOpen b} ?_ ?_
    · intro x Uo hxUo
      have hxV : U.1.ι.base x ∈ U.1 := x.2
      obtain ⟨b, hble, hxb⟩ := U.2.exists_basicOpen_le
        (V := U.1.ι ''ᵁ Uo) ⟨U.1.ι.base x, ⟨x, hxUo, rfl⟩⟩ hxV
      refine ⟨U.1.ι ⁻¹ᵁ C.basicOpen b,
        ⟨b, hble.trans (U.1.ι_image_le Uo), rfl⟩, hxb, ?_⟩
      calc U.1.ι ⁻¹ᵁ C.basicOpen b
          ≤ U.1.ι ⁻¹ᵁ (U.1.ι ''ᵁ Uo) := fun y hy => hble hy
        _ = Uo := Scheme.Hom.preimage_image_eq _ Uo
    · rintro W ⟨b, hb, rfl⟩
      exact bijective_idealGenHom_app J U g hspan hnzd hgmem b hb
  exact (asIso (idealGenHom J U.1 g hgmem)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Classification of structure-sheaf endomorphisms**: every module endomorphism of
the unit is multiplication by its value at the global `1`. -/
theorem unit_endo_eq_ofTopSection {Z : Scheme.{u}}
    (e : unitObj Z ⟶ unitObj Z) :
    e = ModularCurves.unitEndomorphismOfTopSection
      (e.val.app (Opposite.op (⊤ : Z.Opens)) (1 : Γ(Z, (⊤ : Z.Opens)))) := by
  let cW : ∀ W : Z.Opens, Γ(Z, W) :=
    fun W => e.val.app (Opposite.op W) (1 : Γ(Z, W))
  have happ : ∀ (W : Z.Opens) (y : Γ(Z, W)),
      e.val.app (Opposite.op W) y = y * cW W := by
    intro W y
    have hsmul := (e.val.app (Opposite.op W)).hom.map_smul y (1 : Γ(Z, W))
    calc e.val.app (Opposite.op W) y
        = e.val.app (Opposite.op W) ((y * 1 : Γ(Z, W))) := by rw [mul_one]
      _ = y * cW W := hsmul
  have hnat : ∀ W : Z.Opens, cW W =
      Z.presheaf.map (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op
        (cW (⊤ : Z.Opens)) := by
    intro W
    have h := PresheafOfModules.naturality_apply e.val
      (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op (1 : Γ(Z, (⊤ : Z.Opens)))
    have hone : ((unitObj Z).val.map
        (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op)
          (1 : Γ(Z, (⊤ : Z.Opens))) = (1 : Γ(Z, W)) := by
      show ((Z.ringCatSheaf.obj).map
        (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op).hom
          (1 : Γ(Z, (⊤ : Z.Opens))) = (1 : Γ(Z, W))
      exact map_one _
    rw [hone] at h
    calc cW W = ((unitObj Z).val.map
        (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op) (cW (⊤ : Z.Opens)) := h
      _ = Z.presheaf.map (homOfLE (le_top : W ≤ (⊤ : Z.Opens))).op
          (cW (⊤ : Z.Opens)) := rfl
  apply SheafOfModules.hom_ext
  ext U
  change e.val.app U (1 : Γ(Z, U.unop)) = _
  calc e.val.app U (1 : Γ(Z, U.unop))
      = (1 : Γ(Z, U.unop)) * cW U.unop := happ U.unop 1
    _ = (1 : Γ(Z, U.unop)) * Z.presheaf.map
          (homOfLE (le_top : U.unop ≤ (⊤ : Z.Opens))).op
          (cW (⊤ : Z.Opens)) := by rw [hnat U.unop]
    _ = _ := (ModularCurves.unitEndomorphismOfTopSection_app_apply
        (cW (⊤ : Z.Opens)) U.unop 1).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction triangle for the divisor twist, morphism-level: the unit followed
by the underlying of the twist is the presheaf action. -/
theorem divisorTwistHom_unit_comp :
    (PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val) ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
        (𝟙 C.ringCatSheaf.obj)).map (divisorTwistHom J L) =
    idealActionPre J L := by
  have htri := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 C.ringCatSheaf.obj)).homEquiv
      ((idealModule J).val ⊗ L.val) L).apply_symm_apply (idealActionPre J L)
  rw [Adjunction.homEquiv_unit] at htri
  exact htri

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[3b-iii] The forward conjugation square** (statement-locked; proof by
adjunction triangles + unit naturality on both sides): restricting the divisor twist
along an open immersion agrees with the sheafified pushforward of the presheaf action,
through the sheafification-value isos and the inverted restricted unit. -/
theorem restrict_divisorTwistHom_forward_square (U : C.Opens) :
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
        ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))) ≫
      (sheafifyValIso ((restrictFunctor U.ι).obj
        (tensorObj (idealModule J) L))).hom ≫
      (restrictFunctor U.ι).map (divisorTwistHom J L) =
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
        ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          (idealActionPre J L)) ≫
      (sheafifyValIso ((restrictFunctor U.ι).obj L)).hom := by
  -- elementwise: the morphism-level route drowns in restrictScalars-𝟙 clothing
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 U.toScheme.ringCatSheaf.obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.id_obj]
  -- generic elementwise helpers: unit-naturality and the right triangle, valuewise
  have hYnat : ∀ {P Q : _root_.PresheafOfModules
      (U.toScheme.ringCatSheaf.obj)} (g : P ⟶ Q)
      (W : (TopologicalSpace.Opens ↥U.toScheme)ᵒᵖ) (p : ToType (P.obj W)),
      ((PresheafOfModules.sheafification
          (𝟙 U.toScheme.ringCatSheaf.obj)).map g).val.app W
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app P).app W p) =
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app Q).app W (g.app W p) := by
    intro P Q g W p
    have h := (PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).unit.naturality g
    have hval := congrArg (fun (m : P ⟶
        (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj) ⋙
          SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
            (𝟙 U.toScheme.ringCatSheaf.obj)).obj Q) =>
      (ModuleCat.Hom.hom (m.app W)) p) h
    exact hval.symm
  have hYtri : ∀ (M : U.toScheme.Modules)
      (W : (TopologicalSpace.Opens ↥U.toScheme)ᵒᵖ) (y : ToType (M.val.obj W)),
      (sheafifyValIso M).hom.val.app W
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app M.val).app W y) = y := by
    intro M W y
    have h := (PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).right_triangle_components M
    have hval := congrArg (fun (m : M.val ⟶ M.val) =>
      (ModuleCat.Hom.hom (m.app W)) y) h
    exact hval
  ext W' x
  -- both sides reduce to the pushforward action value at x
  have hL1 := hYnat (P := (PresheafOfModules.pushforward (restrictRingHom U.ι)).obj
      ((𝟭 (_root_.PresheafOfModules C.ringCatSheaf.obj)).obj
        ((idealModule J).val ⊗ L.val)))
    ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))) W' x
  have hR1 := hYnat (P := (PresheafOfModules.pushforward (restrictRingHom U.ι)).obj
      ((𝟭 (_root_.PresheafOfModules C.ringCatSheaf.obj)).obj
        ((idealModule J).val ⊗ L.val)))
    ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
      (idealActionPre J L)) W' x
  have hLtri := congrArg (fun (m : ((restrictFunctor U.ι).obj
      (tensorObj (idealModule J) L)).val ⟶ ((restrictFunctor U.ι).obj
      (tensorObj (idealModule J) L)).val) =>
    (ModuleCat.Hom.hom (m.app W'))
      (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 C.ringCatSheaf.obj)).unit.app
            ((idealModule J).val ⊗ L.val))).app W' x))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).right_triangle_components
        ((restrictFunctor U.ι).obj (tensorObj (idealModule J) L)))
  have hRtri := congrArg (fun (m : ((restrictFunctor U.ι).obj L).val ⟶
      ((restrictFunctor U.ι).obj L).val) =>
    (ModuleCat.Hom.hom (m.app W'))
      (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        (idealActionPre J L)).app W' x))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).right_triangle_components
        ((restrictFunctor U.ι).obj L))
  have hcoreL : ((PresheafOfModules.sheafification
      (𝟙 U.toScheme.ringCatSheaf.obj)).map
        ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))) ≫
      (sheafifyValIso ((restrictFunctor U.ι).obj
        (tensorObj (idealModule J) L))).hom ≫
      (restrictFunctor U.ι).map (divisorTwistHom J L)).val.app W'
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app _).app W' x) =
      ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        (idealActionPre J L)).app W' x := by
    show ((restrictFunctor U.ι).map (divisorTwistHom J L)).val.app W'
      ((sheafifyValIso ((restrictFunctor U.ι).obj
        (tensorObj (idealModule J) L))).hom.val.app W'
        (((PresheafOfModules.sheafification
          (𝟙 U.toScheme.ringCatSheaf.obj)).map
            ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
              ((PresheafOfModules.sheafificationAdjunction
                (𝟙 C.ringCatSheaf.obj)).unit.app
                  ((idealModule J).val ⊗ L.val)))).val.app W'
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app _).app W' x))) = _
    have h2 : (sheafifyValIso ((restrictFunctor U.ι).obj
        (tensorObj (idealModule J) L))).hom.val.app W'
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app
            ((PresheafOfModules.pushforward (restrictRingHom U.ι)).obj
              ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj) ⋙
                SheafOfModules.forget C.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars
                  (𝟙 C.ringCatSheaf.obj)).obj
                ((idealModule J).val ⊗ L.val)))).app W'
          (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 C.ringCatSheaf.obj)).unit.app
                ((idealModule J).val ⊗ L.val))).app W' x)) =
        (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app
              ((idealModule J).val ⊗ L.val))).app W' x) := hLtri
    exact ((congrArg (fun t => ((restrictFunctor U.ι).map
        (divisorTwistHom J L)).val.app W'
          ((sheafifyValIso ((restrictFunctor U.ι).obj
            (tensorObj (idealModule J) L))).hom.val.app W' t)) hL1).trans
      (congrArg (fun t => ((restrictFunctor U.ι).map
        (divisorTwistHom J L)).val.app W' t) h2)).trans
      (divisorTwistHom_app_unit J L (Opposite.op (U.ι ''ᵁ W'.unop)) x)
  have hcoreR : ((PresheafOfModules.sheafification
      (𝟙 U.toScheme.ringCatSheaf.obj)).map
        ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          (idealActionPre J L)) ≫
      (sheafifyValIso ((restrictFunctor U.ι).obj L)).hom).val.app W'
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app _).app W' x) =
      ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        (idealActionPre J L)).app W' x := by
    show (sheafifyValIso ((restrictFunctor U.ι).obj L)).hom.val.app W'
      (((PresheafOfModules.sheafification
        (𝟙 U.toScheme.ringCatSheaf.obj)).map
          ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            (idealActionPre J L))).val.app W'
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app _).app W' x)) = _
    have h3 : (sheafifyValIso ((restrictFunctor U.ι).obj L)).hom.val.app W'
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app
            ((PresheafOfModules.pushforward (restrictRingHom U.ι)).obj
              L.val)).app W'
          (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            (idealActionPre J L)).app W' x)) =
        (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
          (idealActionPre J L)).app W' x) := hRtri
    exact (congrArg (fun t => (sheafifyValIso
      ((restrictFunctor U.ι).obj L)).hom.val.app W' t) hR1).trans h3
  exact hcoreL.trans hcoreR.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[3b-iv] Cokernel transport across the forward square**: the restricted twist's
cokernel is the cokernel of the sheafified pushforward action. -/
noncomputable def cokernelRestrictTwistIso (U : C.Opens) :
    Limits.cokernel
        ((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
          ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            (idealActionPre J L))) ≅
      Limits.cokernel ((restrictFunctor U.ι).map (divisorTwistHom J L)) := by
  have hmem := sheafificationW_pushforward_unit_tensor U.ι (idealModule J) L
  rw [PresheafOfModules.sheafificationW_iff] at hmem
  haveI := hmem
  refine Limits.cokernel.mapIso _ _
    ((asIso ((PresheafOfModules.sheafification
        (𝟙 U.toScheme.ringCatSheaf.obj)).map
          ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            ((PresheafOfModules.sheafificationAdjunction
              (𝟙 C.ringCatSheaf.obj)).unit.app
                ((idealModule J).val ⊗ L.val))))) ≪≫
      sheafifyValIso ((restrictFunctor U.ι).obj (tensorObj (idealModule J) L)))
    (sheafifyValIso ((restrictFunctor U.ι).obj L)) ?_
  have h := restrict_divisorTwistHom_forward_square J L U
  rw [Iso.trans_hom, asIso_hom, Category.assoc]
  exact h.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[3b-v]** Sheafification commutes with the action cokernel. -/
noncomputable def cokernelSheafifyActionIso (U : C.Opens) :
    Limits.cokernel
        ((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
          ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            (idealActionPre J L))) ≅
      (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
        (Limits.cokernel
          ((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
            (idealActionPre J L))) :=
  (Limits.PreservesCokernel.iso
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)) _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[vi-a] Pointwise surjectivity of the pushforward action off the divisor**: where
`1` lies in the ideal's sections at the image open, the componentwise action is
surjective (every `l` is `1 ⊗ₜ l`'s value). -/
theorem pushforward_idealActionPre_app_surjective_of_one_mem (U : C.Opens)
    (W' : (TopologicalSpace.Opens ↥U.toScheme)ᵒᵖ)
    (h1 : (1 : Γ(C, U.ι ''ᵁ W'.unop)) ∈
      idealSections J (Opposite.op (U.ι ''ᵁ W'.unop))) :
    Function.Surjective
      (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        (idealActionPre J L)).app W') := by
  intro l
  refine ⟨(⟨(1 : Γ(C, U.ι ''ᵁ W'.unop)), h1⟩ :
    idealSections J (Opposite.op (U.ι ''ᵁ W'.unop))) ⊗ₜ[
      (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (U.ι ''ᵁ W'.unop))]
    (l : (L.val.obj (Opposite.op (U.ι ''ᵁ W'.unop)))), ?_⟩
  have hact := idealActionPre_app_tmul J L (Opposite.op (U.ι ''ᵁ W'.unop))
    (⟨(1 : Γ(C, U.ι ''ᵁ W'.unop)), h1⟩ :
      idealSections J (Opposite.op (U.ι ''ᵁ W'.unop)))
    (l : (L.val.obj (Opposite.op (U.ι ''ᵁ W'.unop))))
  calc (((PresheafOfModules.pushforward (restrictRingHom U.ι)).map
        (idealActionPre J L)).app W') _
      = (idealActionPre J L).app (Opposite.op (U.ι ''ᵁ W'.unop)) _ := rfl
    _ = _ := hact
    _ = l := one_smul _ _


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A morphism of sheaf modules vanishing locally on every section is zero
(separatedness gluing). -/
theorem hom_eq_zero_of_locally_zero {Z : Scheme.{u}} {M N : Z.Modules}
    (f : M ⟶ N)
    (h : ∀ (Uo : Z.Opens) (x : Γ(M, Uo)) (z : ↥Z), z ∈ Uo →
      ∃ W : Z.Opens, z ∈ W ∧ ∃ hWU : W ≤ Uo,
        N.presheaf.map (homOfLE hWU).op (f.app Uo x) = 0) : f = 0 := by
  apply SheafOfModules.hom_ext
  ext Uo x
  classical
  by_cases hne : Nonempty { z : ↥Z // z ∈ Uo.unop }
  · -- glue the local vanishings over the pointwise cover
    let W : { z : ↥Z // z ∈ Uo.unop } → Z.Opens :=
      fun z => (h Uo.unop x z.1 z.2).choose
    have hmem : ∀ z, z.1 ∈ W z := fun z => (h Uo.unop x z.1 z.2).choose_spec.1
    have hle : ∀ z, W z ≤ Uo.unop :=
      fun z => (h Uo.unop x z.1 z.2).choose_spec.2.choose
    have hzero : ∀ z, N.presheaf.map (homOfLE (hle z)).op
        (f.app Uo.unop x) = 0 :=
      fun z => (h Uo.unop x z.1 z.2).choose_spec.2.choose_spec
    have hcover : Uo.unop ≤ iSup W := by
      intro z hz
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩
    have hglue := TopCat.Sheaf.eq_of_locally_eq'
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj N) W Uo.unop
      (fun z => homOfLE (hle z)) hcover
      (f.app Uo.unop x) 0
      (fun z => by
        rw [map_zero]
        exact hzero z)
    calc (f.val.app Uo) x = f.app Uo.unop x := rfl
      _ = 0 := hglue
      _ = _ := rfl
  · -- the open is empty: sections are subsingleton by the empty gluing
    have hUo : Uo.unop ≤ iSup (fun z : { z : ↥Z // z ∈ Uo.unop } => (⊥ : Z.Opens)) := by
      intro z hz
      exact absurd ⟨⟨z, hz⟩⟩ hne
    have hglue := TopCat.Sheaf.eq_of_locally_eq'
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj N)
      (fun _ : { z : ↥Z // z ∈ Uo.unop } => (⊥ : Z.Opens)) Uo.unop
      (fun z => homOfLE bot_le) hUo
      (f.app Uo.unop x) 0
      (fun z => absurd ⟨z⟩ hne)
    calc (f.val.app Uo) x = f.app Uo.unop x := rfl
      _ = 0 := hglue
      _ = _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[desc-route ii] The twist of a smaller ideal dies in the larger twist's
cokernel**: locally every section is a unit image, on unit images the composite is the
presheaf action, and the action value casts along `idealSections_mono` into the larger
twist's image. -/
theorem divisorTwistHom_comp_cokernelπ_eq_zero {J₁ J₂ : C.IdealSheafData}
    (h12 : J₁ ≤ J₂) (L : C.Modules) :
    divisorTwistHom J₁ L ≫ Limits.cokernel.π (divisorTwistHom J₂ L) = 0 := by
  apply hom_eq_zero_of_locally_zero
  intro Uo x z hz
  -- the unit of the sheafification is locally surjective
  have hWunit : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J₁).val ⊗ L.val)) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components
        ((idealModule J₁).val ⊗ L.val)
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            ((idealModule J₁).val ⊗ L.val))) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  obtain ⟨-, hsurj⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunit
  have hmem := hsurj.imageSieve_mem
    (x : ToType (((PresheafOfModules.toPresheaf _).obj
      (tensorObj (idealModule J₁) L).val).obj (Opposite.op Uo)))
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨W, i, ⟨t, ht⟩, hzW⟩ := hmem z hz
  refine ⟨W, hzW, i.le, ?_⟩
  -- transport the section along the restriction and evaluate on the unit image
  have hnat := NatTrans.naturality_apply
    ((PresheafOfModules.toPresheaf _).map
      ((divisorTwistHom J₁ L ≫
        Limits.cokernel.π (divisorTwistHom J₂ L)).val))
    (homOfLE i.le).op x
  have hbridge : (((PresheafOfModules.toPresheaf _).obj
      (tensorObj (idealModule J₁) L).val).map (homOfLE i.le).op) x =
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app
          ((idealModule J₁).val ⊗ L.val)).app (Opposite.op W) t) := by
    exact ht.symm
  calc (Limits.cokernel (divisorTwistHom J₂ L)).presheaf.map
        (homOfLE i.le).op
        ((divisorTwistHom J₁ L ≫
          Limits.cokernel.π (divisorTwistHom J₂ L)).app Uo x)
      = ((divisorTwistHom J₁ L ≫
          Limits.cokernel.π (divisorTwistHom J₂ L)).val.app (Opposite.op W))
          (((PresheafOfModules.toPresheaf _).obj
            (tensorObj (idealModule J₁) L).val).map (homOfLE i.le).op x) :=
        hnat.symm
    _ = ((divisorTwistHom J₁ L ≫
          Limits.cokernel.π (divisorTwistHom J₂ L)).val.app (Opposite.op W))
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app
              ((idealModule J₁).val ⊗ L.val)).app (Opposite.op W) t) := by
        rw [hbridge]
    _ = 0 := by
        -- on unit images the composite is π ∘ action; induct on the tensor
        have hval : ∀ (s : TensorProduct
            ((C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op W))
            (idealSections J₁ (Opposite.op W))
            (L.val.obj (Opposite.op W))),
            ((Limits.cokernel.π (divisorTwistHom J₂ L)).val.app
              (Opposite.op W)) ((idealActionPre J₁ L).app (Opposite.op W) s) =
              0 := by
          intro s
          induction s with
          | zero => rw [map_zero, map_zero]
          | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
          | tmul m l =>
              have hcast := idealActionPre_app_tmul J₁ L (Opposite.op W) m l
              rw [hcast]
              have hcast2 := (idealActionPre_app_tmul J₂ L (Opposite.op W)
                (⟨m.1, idealSections_mono h12 (Opposite.op W) m.2⟩ :
                  idealSections J₂ (Opposite.op W)) l).symm
              rw [show (show ((C.sheaf.obj ⋙ forget₂ CommRingCat
                  RingCat).obj (Opposite.op W)) from m.1) • l =
                  (show ((C.sheaf.obj ⋙ forget₂ CommRingCat
                    RingCat).obj (Opposite.op W)) from
                    ((⟨m.1, idealSections_mono h12 (Opposite.op W) m.2⟩ :
                      idealSections J₂ (Opposite.op W))).1) • l from rfl]
              rw [hcast2]
              have happ_unit := divisorTwistHom_app_unit J₂ L (Opposite.op W)
                ((⟨m.1, idealSections_mono h12 (Opposite.op W) m.2⟩ :
                  idealSections J₂ (Opposite.op W)) ⊗ₜ[
                    (C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
                      (Opposite.op W)] l)
              rw [← happ_unit]
              show ((divisorTwistHom J₂ L ≫
                Limits.cokernel.π (divisorTwistHom J₂ L)).val.app
                  (Opposite.op W)) _ = 0
              rw [Limits.cokernel.condition]
              rfl
        have hcomp : ((divisorTwistHom J₁ L ≫
            Limits.cokernel.π (divisorTwistHom J₂ L)).val.app (Opposite.op W))
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 C.ringCatSheaf.obj)).unit.app
                ((idealModule J₁).val ⊗ L.val)).app (Opposite.op W) t) =
            ((Limits.cokernel.π (divisorTwistHom J₂ L)).val.app
              (Opposite.op W))
              ((divisorTwistHom J₁ L).val.app (Opposite.op W)
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 C.ringCatSheaf.obj)).unit.app
                    ((idealModule J₁).val ⊗ L.val)).app (Opposite.op W) t)) :=
          rfl
        rw [hcomp, divisorTwistHom_app_unit J₁ L (Opposite.op W) t]
        exact hval t

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The per-section evaluation quotient**: the induced map from the smaller-ideal
twist cokernel to the larger one, by the universal property. -/
noncomputable def cokernelTwistDesc {J₁ J₂ : C.IdealSheafData}
    (h12 : J₁ ≤ J₂) (L : C.Modules) :
    Limits.cokernel (divisorTwistHom J₁ L) ⟶
      Limits.cokernel (divisorTwistHom J₂ L) :=
  Limits.cokernel.desc _ (Limits.cokernel.π (divisorTwistHom J₂ L))
    (divisorTwistHom_comp_cokernelπ_eq_zero h12 L)

@[reassoc (attr := simp)]
theorem cokernelTwistDesc_π {J₁ J₂ : C.IdealSheafData}
    (h12 : J₁ ≤ J₂) (L : C.Modules) :
    Limits.cokernel.π (divisorTwistHom J₁ L) ≫ cokernelTwistDesc h12 L =
      Limits.cokernel.π (divisorTwistHom J₂ L) :=
  Limits.cokernel.π_desc _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Support avoidance gives the unit section**: an ideal sheaf whose support is
disjoint from an open contains `1` among its sections there. -/
theorem one_mem_idealSections_of_disjoint_support (J' : C.IdealSheafData)
    (W : C.Opens) (hW : Disjoint (J'.support : Set ↥C) (W : Set ↥C)) :
    (1 : Γ(C, W)) ∈ idealSections J' (Opposite.op W) := by
  refine RingHom.mem_ker.mpr ?_
  haveI hempty : IsEmpty ↥(J'.subschemeι ⁻¹ᵁ W) := by
    constructor
    rintro ⟨c, hc⟩
    have hcW : J'.subschemeι.base c ∈ W := hc
    have hcs : J'.subschemeι.base c ∈ (J'.support : Set ↥C) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨c, rfl⟩
    exact Set.disjoint_left.mp hW hcs hcW
  haveI hsub : Subsingleton
      Γ(J'.subscheme, J'.subschemeι ⁻¹ᵁ W) := by
    haveI : IsEmpty
        ↥((J'.subschemeι ⁻¹ᵁ W : J'.subscheme.Opens).toScheme) := by
      refine ⟨fun x => ?_⟩
      exact hempty.elim' ⟨x.1, x.2⟩
    have e := (J'.subschemeι ⁻¹ᵁ W : J'.subscheme.Opens).topIso
    exact Function.Surjective.subsingleton
      (fun y => ⟨e.inv.hom y, by
        change (e.inv ≫ e.hom).hom y = y
        rw [e.inv_hom_id]
        rfl⟩)
  exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Off the image of a closed immersion, `1` lies in the kernel ideal's sections:
the kernel subscheme's preimage of such an open is empty, so its section ring is a
subsingleton. -/
theorem one_mem_idealSections_ker_of_preimage_eq_bot {S : Scheme.{u}}
    (z : S ⟶ C) [IsClosedImmersion z] [QuasiCompact z]
    (W : C.Opens) (hW : z ⁻¹ᵁ W = ⊥) :
    (1 : Γ(C, W)) ∈ idealSections (Scheme.Hom.ker z) (Opposite.op W) := by
  refine RingHom.mem_ker.mpr ?_
  have hrange : Set.range ((Scheme.Hom.ker z).subschemeι.base) ⊆
      Set.range z.base := by
    have h1 := Scheme.IdealSheafData.range_subschemeι (I := Scheme.Hom.ker z)
    have h2 := Scheme.Hom.support_ker z
    intro c hc
    have hc2 : c ∈ closure (Set.range z.base) := h2 ▸ (h1 ▸ hc)
    rwa [z.isClosedEmbedding.isClosed_range.closure_eq] at hc2
  haveI hempty : IsEmpty
      ((Scheme.Hom.ker z).subschemeι ⁻¹ᵁ W : Set _) := by
    constructor
    rintro ⟨c, hc⟩
    obtain ⟨s, hs⟩ := hrange ⟨c, rfl⟩
    have hsW : z.base s ∈ W := by
      rw [hs]
      exact hc
    have : s ∈ z ⁻¹ᵁ W := hsW
    rw [hW] at this
    exact this
  haveI hsub : Subsingleton
      Γ((Scheme.Hom.ker z).subscheme, (Scheme.Hom.ker z).subschemeι ⁻¹ᵁ W) := by
    haveI : IsEmpty
        ↥(((Scheme.Hom.ker z).subschemeι ⁻¹ᵁ W : (Scheme.Hom.ker z).subscheme.Opens).toScheme) := by
      refine ⟨fun x => ?_⟩
      exact hempty.elim' ⟨x.1, x.2⟩
    have e := ((Scheme.Hom.ker z).subschemeι ⁻¹ᵁ W :
      (Scheme.Hom.ker z).subscheme.Opens).topIso
    exact Function.Surjective.subsingleton
      (fun y => ⟨e.inv.hom y, by
        change (e.inv ≫ e.hom).hom y = y
        rw [e.inv_hom_id]
        rfl⟩)
  exact Subsingleton.elim _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[per-section Γ core, statement-locked]** On an affine total space, the base
sections of the cokernel of multiplication by a global function are the quotient by
its span: the workhorse H⁰-exactness and H¹-vanishing of the affine structure sheaf,
with the range identified elementwise through `unitEndomorphismOfTopSection_app_apply`.
-/
theorem nonempty_baseSections_cokernel_unitEndo_equiv {Y S : Scheme.{u}}
    (π' : Y ⟶ S) [IsAffine Y] (a : Γ(Y, (⊤ : Y.Opens)))
    [Mono (ModularCurves.unitEndomorphismOfTopSection a)]
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) r =
        (Scheme.Hom.appTop π').hom r) :
    Nonempty ((Scheme.Modules.baseSections π'
        (Limits.cokernel (ModularCurves.unitEndomorphismOfTopSection a)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Γ(Y, (⊤ : Y.Opens)) ⧸ Ideal.span {a})) := by
  classical
  haveI hQCu : (unitObj Y).IsQuasicoherent :=
    isInvertible_unit.isQuasicoherent
  haveI hQCc : (Limits.cokernel
      (ModularCurves.unitEndomorphismOfTopSection a)).IsQuasicoherent :=
    isQuasicoherent_cokernel _
  haveI hH1 : Subsingleton (CategoryTheory.Sheaf.H (unitObj Y).sheaf 1) :=
    affine_subsingleton_H (F := unitObj Y) 0
  have hsurj := Scheme.Modules.baseSectionsMap_cokernel_surjective_of_subsingleton_H_one
    π' (ModularCurves.unitEndomorphismOfTopSection a)
  have hexact := Scheme.Modules.baseSectionsMap_exact_cokernel
    π' (ModularCurves.unitEndomorphismOfTopSection a)
  have hker := LinearMap.exact_iff.mp hexact
  -- the mk-map from unit base sections to the target quotient, Γ(S)-linear via halg
  let ψ : Scheme.Modules.baseSections π' (unitObj Y) →ₗ[Γ(S, (⊤ : S.Opens))]
      (Γ(Y, (⊤ : Y.Opens)) ⧸ Ideal.span {a}) :=
    { toFun := fun s => Ideal.Quotient.mk _ (s : Γ(Y, (⊤ : Y.Opens)))
      map_add' := fun s t => by
        exact map_add (Ideal.Quotient.mk (Ideal.span {a})) _ _
      map_smul' := fun r s => by
        let s' : Γ(Y, (⊤ : Y.Opens)) := s
        have h2 : (r • (Ideal.Quotient.mk (Ideal.span {a}) s')) =
            Ideal.Quotient.mk (Ideal.span {a})
              (algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) r * s') := by
          rw [Algebra.smul_def]
          rfl
        have h3 : ((r • s : Scheme.Modules.baseSections π' (unitObj Y)) :
            Γ(Y, (⊤ : Y.Opens))) =
            algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) r * s' := by
          rw [halg r]
          have hbase := Scheme.Modules.baseSections_smul π' (unitObj Y) r
            (s : Γ(unitObj Y, (⊤ : Y.Opens)))
          exact hbase
        rw [RingHom.id_apply]
        exact (congrArg (Ideal.Quotient.mk (Ideal.span {a})) h3).trans
          h2.symm }
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨y, rfl⟩
  -- the kernel of the mk-map is the range of the endomorphism on base sections
  have hkerψ : LinearMap.range (Scheme.Modules.baseSectionsMap π'
      (ModularCurves.unitEndomorphismOfTopSection a)).hom = LinearMap.ker ψ := by
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      show Ideal.Quotient.mk _ _ = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      have hval := ModularCurves.unitEndomorphismOfTopSection_app_apply a
        (⊤ : Y.Opens) (t : Γ(Y, (⊤ : Y.Opens)))
      have hida : Y.presheaf.map
          (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op a = a := by
        rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
          CategoryTheory.Functor.map_id]
        rfl
      rw [hida] at hval
      let t' : Γ(Y, (⊤ : Y.Opens)) := t
      let v : Γ(Y, (⊤ : Y.Opens)) :=
        ((ModularCurves.unitEndomorphismOfTopSection a).val.app
          (Opposite.op (⊤ : Y.Opens))) t'
      show v ∈ Ideal.span {a}
      rw [show v = t' * a from hval]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self a)
    · intro hs
      have hs0 : Ideal.Quotient.mk (Ideal.span {a})
          (s : Γ(Y, (⊤ : Y.Opens))) = 0 := hs
      rw [Ideal.Quotient.eq_zero_iff_mem] at hs0
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hs0
      refine ⟨(c : Γ(Y, (⊤ : Y.Opens))), ?_⟩
      have hval := ModularCurves.unitEndomorphismOfTopSection_app_apply a
        (⊤ : Y.Opens) (c : Γ(Y, (⊤ : Y.Opens)))
      have hida : Y.presheaf.map
          (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op a = a := by
        rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
          CategoryTheory.Functor.map_id]
        rfl
      rw [hida] at hval
      let w : Γ(Y, (⊤ : Y.Opens)) :=
        ((ModularCurves.unitEndomorphismOfTopSection a).val.app
          (Opposite.op (⊤ : Y.Opens))) (c : Γ(Y, (⊤ : Y.Opens)))
      show w = (s : Γ(Y, (⊤ : Y.Opens)))
      rw [show w = (c : Γ(Y, (⊤ : Y.Opens))) * a from hval]
      exact hc
  -- assemble: coker sections ≃ unit sections ⧸ ker(π-map) ≃ ⧸range ≃ target
  have c1 := (LinearMap.quotKerEquivOfSurjective _ hsurj).symm
  have c2 := Submodule.quotEquivOfEq _ _ hker
  have c3 := Submodule.quotEquivOfEq _ _ hkerψ
  have c4 := ψ.quotKerEquivOfSurjective hψsurj
  exact ⟨((c1.trans c2).trans c3).trans c4⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The chart trivialization of the restricted twisted tensor: restriction commutes
with the sheafified tensor along the open immersion, both factors trivialize, and the
unit absorbs. -/
noncomputable def twistChartTensorTriv (J : C.IdealSheafData) (L : C.Modules)
    (U : C.Opens)
    (eI : (restrictFunctor U.ι).obj (idealModule J) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    (restrictFunctor U.ι).obj (tensorObj (idealModule J) L) ≅
      unitObj U.toScheme :=
  (restrictFunctorIsoPullback U.ι).app
      (tensorObj (idealModule J) L) ≪≫
    (nonempty_pullback_tensorObj_of_isOpenImmersion U.ι
      (idealModule J) L).some ≪≫
    tensorObjCongr
      (((restrictFunctorIsoPullback U.ι).app (idealModule J)).symm ≪≫ eI)
      (((restrictFunctorIsoPullback U.ι).app L).symm ≪≫ eL) ≪≫
    (nonempty_tensorObj_unit_iso (unitObj U.toScheme)).some

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The conjugated multiplier of the restricted twist. -/
noncomputable def twistChartMultiplier (J : C.IdealSheafData) (L : C.Modules)
    (U : C.Opens)
    (eI : (restrictFunctor U.ι).obj (idealModule J) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
  ((twistChartTensorTriv J L U eI eL).inv ≫
    (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom).val.app
      (Opposite.op (⊤ : U.toScheme.Opens))
      (1 : Γ(U.toScheme, (⊤ : U.toScheme.Opens)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The restricted twist's cokernel is the multiplier's cokernel**: the tautological
square through the trivializations, with the endo classified as multiplication. -/
noncomputable def cokernelRestrictTwistUnitEndoIso (J : C.IdealSheafData)
    (L : C.Modules) (U : C.Opens)
    (eI : (restrictFunctor U.ι).obj (idealModule J) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme) :
    Limits.cokernel ((restrictFunctor U.ι).map (divisorTwistHom J L)) ≅
      Limits.cokernel (ModularCurves.unitEndomorphismOfTopSection
        (twistChartMultiplier J L U eI eL)) := by
  refine Limits.cokernel.mapIso _ _
    (twistChartTensorTriv J L U eI eL) eL ?_
  have hd := unit_endo_eq_ofTopSection
    ((twistChartTensorTriv J L U eI eL).inv ≫
      (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom)
  calc (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom
      = (twistChartTensorTriv J L U eI eL).hom ≫
        ((twistChartTensorTriv J L U eI eL).inv ≫
          (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom) :=
        (Iso.hom_inv_id_assoc _ _).symm
    _ = (twistChartTensorTriv J L U eI eL).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (twistChartMultiplier J L U eI eL) := by
        rw [hd]
        rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Local injectivity restricts along an open immersion of opens (the injective twin
of `isLocallySurjective_restrictFunctor_map`). -/
theorem isLocallyInjective_restrictFunctor_map {Z : Scheme.{u}}
    {A B : Z.Modules} (g : A ⟶ B)
    (hs : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map g.val))
    (W : Z.Opens) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥W.toScheme)
      ((PresheafOfModules.toPresheaf _).map ((restrictFunctor W.ι).map g).val) := by
  constructor
  intro V x y hxy
  rw [Opens.mem_grothendieckTopology]
  intro c hcV
  have hxy' : ((PresheafOfModules.toPresheaf _).map g.val).app
      (Opposite.op (W.ι ''ᵁ V.unop)) x =
      ((PresheafOfModules.toPresheaf _).map g.val).app
        (Opposite.op (W.ι ''ᵁ V.unop)) y := hxy
  have hmem := hs.equalizerSieve_mem x y hxy'
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V₂, i, hEq, hcV₂⟩ := hmem (W.ι.base c) ⟨c, hcV, rfl⟩
  refine ⟨W.ι ⁻¹ᵁ V₂ ⊓ V.unop, homOfLE inf_le_right, ?_,
    ⟨show W.ι.base c ∈ V₂ from hcV₂, hcV⟩⟩
  have hle : W.ι ''ᵁ (W.ι ⁻¹ᵁ V₂ ⊓ V.unop) ≤ V₂ := by
    refine le_trans ((W.ι.opensFunctor.map (homOfLE inf_le_left)).le) ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have hres := congrArg (fun (q : ToType ((((PresheafOfModules.toPresheaf _).obj
      A.val)).obj (Opposite.op V₂))) =>
    (((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op) q) hEq
  have hside : ∀ q : ToType ((((PresheafOfModules.toPresheaf _).obj
      ((restrictFunctor W.ι).obj A).val)).obj V),
      (((PresheafOfModules.toPresheaf _).obj
        ((restrictFunctor W.ι).obj A).val).map (homOfLE inf_le_right).op) q =
      (((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op)
        ((((PresheafOfModules.toPresheaf _).obj A.val).map i.op) q) := by
    intro q
    rw [show (((PresheafOfModules.toPresheaf _).obj A.val).map
        (homOfLE hle).op)
        ((((PresheafOfModules.toPresheaf _).obj A.val).map i.op) q) =
      (((PresheafOfModules.toPresheaf _).obj A.val).map
        (i.op ≫ (homOfLE hle).op)) q from by
      rw [Functor.map_comp]
      rfl]
    rfl
  calc (((PresheafOfModules.toPresheaf _).obj
      ((restrictFunctor W.ι).obj A).val).map (homOfLE inf_le_right).op) x
      = (((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op)
          ((((PresheafOfModules.toPresheaf _).obj A.val).map i.op) x) :=
        hside x
    _ = (((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op)
          ((((PresheafOfModules.toPresheaf _).obj A.val).map i.op) y) := hres
    _ = (((PresheafOfModules.toPresheaf _).obj
          ((restrictFunctor W.ι).obj A).val).map (homOfLE inf_le_right).op) y :=
        (hside y).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A restricted sheaf-module map is a monomorphism when the original map's underlying
presheaf map is locally injective: restrict the local injectivity and run the
mono pipeline on the open subscheme. -/
theorem mono_restrictFunctor_map_of_isLocallyInjective {Z : Scheme.{u}}
    {A B : Z.Modules} (f : A ⟶ B)
    (hs : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map f.val))
    (W : Z.Opens) : Mono ((restrictFunctor W.ι).map f) := by
  have h6 := isLocallyInjective_restrictFunctor_map f hs W
  haveI h7 : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf _).map ((restrictFunctor W.ι).map f)) := h6
  haveI h8 : Mono ((SheafOfModules.toSheaf _).map
      ((restrictFunctor W.ι).map f)) := Sheaf.mono_of_isLocallyInjective _
  exact (SheafOfModules.toSheaf _).mono_of_mono_map h8

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The divisor twist's underlying presheaf map is locally injective (the loc-inj
core of `mono_divisorTwistHom`, exposed for restriction). -/
theorem isLocallyInjective_divisorTwistHom
    (h : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      J.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hL : IsInvertible L) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf _).map (divisorTwistHom J L).val) := by
  classical
  haveI hφ := isLocallyInjective_idealActionPre J L h hL
  -- the sheafification units at source and target are in W, hence locally bijective
  have hWunitP : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components ((idealModule J).val ⊗ L.val)
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            ((idealModule J).val ⊗ L.val))) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  have hWunitL : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app L.val) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components L.val
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            L.val)) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  obtain ⟨-, hPsurj⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunitP
  obtain ⟨hLinj2, -⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunitL
  -- naturality of the unit
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 C.ringCatSheaf.obj)).unit.naturality (idealActionPre J L)
  rw [Functor.id_map] at hnat
  -- local injectivity of the composite, with goal-copied clothing
  haveI h1 : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf
        ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
          C.ringCatSheaf)).map (idealActionPre J L) ≫
        (PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app L.val)) := by
    haveI hφ' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map (idealActionPre J L)) := hφ
    haveI hu' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
        ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology ↥C) RingCat).obj
            C.ringCatSheaf)).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 C.ringCatSheaf.obj)).unit.app L.val)) := hLinj2
    infer_instance
  rw [← Functor.map_comp, hnat, Functor.map_comp] at h1
  haveI := h1
  have h4 := isLocallyInjective_of_comp_fields _ _ h1 hPsurj
  haveI h5' : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf _).map
        (((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).map
          (idealActionPre J L)).val)) := h4
  haveI hIv : IsIso (sheafifyValIso L).hom.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map (sheafifyValIso L).hom))
  haveI hI : IsIso ((PresheafOfModules.toPresheaf _).map
      (sheafifyValIso L).hom.val) := inferInstance
  have hval : (divisorTwistHom J L).val =
      ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).map
        (idealActionPre J L)).val ≫ (sheafifyValIso L).hom.val := by
    rw [divisorTwistHom_eq]
    rfl
  rw [hval, Functor.map_comp]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The chart multiplier's endomorphism inherits the twist's monomorphy through the
conjugation. -/
theorem mono_unitEndo_twistChartMultiplier (J : C.IdealSheafData)
    (L : C.Modules) (U : C.Opens)
    (eI : (restrictFunctor U.ι).obj (idealModule J) ≅ unitObj U.toScheme)
    (eL : (restrictFunctor U.ι).obj L ≅ unitObj U.toScheme)
    [Mono ((restrictFunctor U.ι).map (divisorTwistHom J L))] :
    Mono (ModularCurves.unitEndomorphismOfTopSection
      (twistChartMultiplier J L U eI eL)) := by
  have hd := unit_endo_eq_ofTopSection
    ((twistChartTensorTriv J L U eI eL).inv ≫
      (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom)
  rw [show ModularCurves.unitEndomorphismOfTopSection
      (twistChartMultiplier J L U eI eL) =
    (twistChartTensorTriv J L U eI eL).inv ≫
      (restrictFunctor U.ι).map (divisorTwistHom J L) ≫ eL.hom from hd.symm]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-hv i]** On an affine scheme, the unit endomorphism of a nonzerodivisor
global section is a monomorphism: on the basic-open basis the endomorphism is
multiplication by the localized section, which remains a nonzerodivisor. -/
theorem mono_unitEndomorphismOfTopSection_of_nzd {Z : Scheme.{u}} [IsAffine Z]
    (g : Γ(Z, (⊤ : Z.Opens))) (hnzd : g ∈ nonZeroDivisors Γ(Z, (⊤ : Z.Opens))) :
    Mono (ModularCurves.unitEndomorphismOfTopSection g) := by
  have hloc : Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map
        (ModularCurves.unitEndomorphismOfTopSection g).val) := by
    constructor
    intro V x y hxy
    rw [Opens.mem_grothendieckTopology]
    intro c hcV
    obtain ⟨t, htle, hct⟩ := (isAffineOpen_top Z).exists_basicOpen_le
      (V := V.unop) ⟨c, hcV⟩ trivial
    refine ⟨Z.basicOpen t, homOfLE htle, ?_, hct⟩
    letI := (isAffineOpen_top Z).isLocalization_basicOpen t
    have hgt : Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op g
        ∈ nonZeroDivisors Γ(Z, Z.basicOpen t) :=
      IsLocalization.map_nonZeroDivisors_le (Submonoid.powers t)
        Γ(Z, Z.basicOpen t) ⟨g, hnzd, rfl⟩
    let x' : Γ(Z, V.unop) := x
    let y' : Γ(Z, V.unop) := y
    have hxy' : (x' * Z.presheaf.map
          (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op g) =
        (y' * Z.presheaf.map
          (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op g) := hxy
    have hres := congrArg (Z.presheaf.map (homOfLE htle).op).hom hxy'
    have hcollapse : (Z.presheaf.map (homOfLE htle).op).hom
        (Z.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op g) =
        Z.presheaf.map (homOfLE (Z.basicOpen_le t)).op g := by
      show (Z.presheaf.map (homOfLE (le_top : V.unop ≤ (⊤ : Z.Opens))).op ≫
        Z.presheaf.map (homOfLE htle).op).hom g = _
      rw [← Functor.map_comp]
      rfl
    rw [map_mul, map_mul, hcollapse] at hres
    have hxyres := (mul_cancel_right_mem_nonZeroDivisors hgt).mp hres
    show (Z.presheaf.map (homOfLE htle).op).hom x' =
      (Z.presheaf.map (homOfLE htle).op).hom y'
    exact hxyres
  haveI h7 : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf _).map
        (ModularCurves.unitEndomorphismOfTopSection g)) := hloc
  haveI h8 : Mono ((SheafOfModules.toSheaf _).map
      (ModularCurves.unitEndomorphismOfTopSection g)) :=
    Sheaf.mono_of_isLocallyInjective _
  exact (SheafOfModules.toSheaf _).mono_of_mono_map h8

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification unit of the twist's presheaf tensor is locally surjective
(the `W`-extraction of the adjunction triangle, as in the pullback development). -/
theorem isLocallySurjective_tensor_sheafification_unit :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥C)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))) := by
  have hWunit : PresheafOfModules.sheafificationW (𝟙 C.ringCatSheaf.obj)
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)) := by
    rw [PresheafOfModules.sheafificationW_iff]
    have htri := (PresheafOfModules.sheafificationAdjunction
      (𝟙 C.ringCatSheaf.obj)).left_triangle_components
        ((idealModule J).val ⊗ L.val)
    haveI : IsIso ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).counit.app
          ((PresheafOfModules.sheafification (𝟙 C.ringCatSheaf.obj)).obj
            ((idealModule J).val ⊗ L.val))) := inferInstance
    exact IsIso.of_isIso_fac_right htri
  obtain ⟨-, hunitSurj⟩ :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ _).mp hWunit
  exact hunitSurj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On a principal chart, every presheaf-action value is a generator multiple. -/
private theorem exists_idealActionPre_app_eq_smul (V : C.affineOpens)
    (gV : Γ(C, V.1)) (hspanV : J.ideal V = Ideal.span {gV})
    (t : ToType (((idealModule J).val ⊗ L.val).obj (Opposite.op V.1))) :
    ∃ y : Γ(L, V.1), (idealActionPre J L).app (Opposite.op V.1) t = gV • y := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, smul_zero]⟩
  | add a b ha hb =>
    obtain ⟨y1, h1⟩ := ha
    obtain ⟨y2, h2⟩ := hb
    exact ⟨y1 + y2, by rw [map_add, h1, h2, smul_add]⟩
  | tmul m l =>
    have hm : (m.1 : Γ(C, V.1)) ∈ Ideal.span {gV} := by
      rw [← hspanV, ← show idealSections J (Opposite.op V.1) = J.ideal V from
        J.ker_subschemeι_app V]
      exact m.2
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hm
    refine ⟨a • l, ?_⟩
    erw [idealActionPre_app_tmul]
    show (m.1 : Γ(C, V.1)) • l = gV • a • l
    rw [← ha, smul_smul, mul_comm a gV, ← smul_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-hv ii]** Through a chart trivialization of the ambient module, the
restricted twist followed by the cokernel projection of the transported generator's
unit endomorphism vanishes: sections of the sheafified tensor are locally unit
images over basic affines of the chart, the action value there is a generator
multiple, and the transported generator's endomorphism range dies in its cokernel. -/
theorem restrict_divisorTwistHom_comp_cokernelπ_transport_eq_zero
    (U : C.affineOpens) (g : Γ(C, U.1))
    (hspan : J.ideal U = Ideal.span {g})
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    (restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom ≫
      Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)) = 0 := by
  classical
  refine hom_eq_zero_of_locally_zero _ ?_
  intro Uo x z hzUo
  haveI := isLocallySurjective_tensor_sheafification_unit (J := J) (L := L)
  let xC : Γ(tensorObj (idealModule J) L, U.1.ι ''ᵁ Uo) := x
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥C)
    ((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))) xC
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨W₂, i₂, ⟨t₂, ht₂⟩, hzW₂⟩ := hmem (U.1.ι.base z) ⟨z, hzUo, rfl⟩
  have hW₂U : W₂ ≤ U.1 := le_trans (leOfHom i₂) (U.1.ι_image_le Uo)
  obtain ⟨b, hble, hzb⟩ := U.2.exists_basicOpen_le (V := W₂)
    ⟨U.1.ι.base z, hzW₂⟩ (hW₂U hzW₂)
  -- the answer open and its image bookkeeping
  refine ⟨U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo,
    ⟨show U.1.ι.base z ∈ C.basicOpen b from hzb, hzUo⟩, inf_le_right, ?_⟩
  have hWbU : C.basicOpen b ≤ U.1 := hble.trans hW₂U
  have hle5 : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ C.basicOpen b := by
    refine le_trans ((U.1.ι.opensFunctor.map (homOfLE inf_le_left)).le) ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  have hle6 : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ W₂ := hle5.trans hble
  have hleUo : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1.ι ''ᵁ Uo :=
    (U.1.ι.opensFunctor.map (homOfLE inf_le_right)).le
  -- restrict the unit witness to the image of the answer open
  have htWtb : (((PresheafOfModules.toPresheaf _).obj
      ((idealModule J).val ⊗ L.val)).map (homOfLE hle6).op) t₂ =
      (((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hle5).op)
      ((((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hble).op) t₂) := by
    rw [show (((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hle5).op)
        ((((PresheafOfModules.toPresheaf _).obj
          ((idealModule J).val ⊗ L.val)).map (homOfLE hble).op) t₂) =
      (((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map
        ((homOfLE hble).op ≫ (homOfLE hle5).op)) t₂ from by
      rw [Functor.map_comp]
      rfl]
    rfl
  have hres6 : (((PresheafOfModules.toPresheaf _).map
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val))).app
      (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo))))
      ((((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hle6).op) t₂) =
      (((PresheafOfModules.toPresheaf _).obj
        ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars
          (𝟙 C.ringCatSheaf.obj)).obj (tensorObj (idealModule J) L))).map
        (homOfLE hleUo).op) xC := by
    have h1 := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)))
      (homOfLE hle6).op t₂
    refine h1.trans ?_
    rw [ht₂, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  -- the action value at the basic affine is a generator multiple
  have hspanWb : J.ideal (C.affineBasicOpen b) = Ideal.span
      {(C.presheaf.map (homOfLE (C.basicOpen_le b)).op).hom g} := by
    rw [← J.map_ideal_basicOpen U b, hspan, Ideal.map_span, Set.image_singleton]
  obtain ⟨y₀, hy₀⟩ := exists_idealActionPre_app_eq_smul (J := J) (L := L)
    (C.affineBasicOpen b)
    ((C.presheaf.map (homOfLE (C.basicOpen_le b)).op).hom g) hspanWb
    ((((PresheafOfModules.toPresheaf _).obj
      ((idealModule J).val ⊗ L.val)).map (homOfLE hble).op) t₂)
  let y₀' : Γ(L, C.basicOpen b) := y₀
  have hy₀' : (idealActionPre J L).app (Opposite.op (C.basicOpen b))
      ((((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hble).op) t₂) =
      (C.presheaf.map (homOfLE (C.basicOpen_le b)).op).hom g • y₀' := hy₀
  -- hoist the action value from the basic affine to the answer image open
  have hDnat := PresheafOfModules.naturality_apply (idealActionPre J L)
    (homOfLE hle5).op
    ((((PresheafOfModules.toPresheaf _).obj
      ((idealModule J).val ⊗ L.val)).map (homOfLE hble).op) t₂)
  have hDchain : (idealActionPre J L).app
      (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))
      ((((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hle6).op) t₂) =
      L.presheaf.map (homOfLE hle5).op
        ((C.presheaf.map (homOfLE (C.basicOpen_le b)).op).hom g • y₀') := by
    refine (congrArg ((idealActionPre J L).app
      (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))) htWtb).trans ?_
    refine hDnat.trans ?_
    exact congrArg (L.presheaf.map (homOfLE hle5).op) hy₀'
  -- the twist value on the answer open through the unit witness
  have htwistval : ((restrictFunctor U.1.ι).map (divisorTwistHom J L)).app
      (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
      (((restrictFunctor U.1.ι).obj (tensorObj (idealModule J) L)).presheaf.map
        (homOfLE (inf_le_right : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ Uo)).op x) =
      (idealActionPre J L).app
        (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))
        ((((PresheafOfModules.toPresheaf _).obj
          ((idealModule J).val ⊗ L.val)).map (homOfLE hle6).op) t₂) := by
    have h2 := divisorTwistHom_app_unit (J := J) (L := L)
      (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))
      ((((PresheafOfModules.toPresheaf _).obj
        ((idealModule J).val ⊗ L.val)).map (homOfLE hle6).op) t₂)
    refine Eq.trans ?_ h2
    exact congrArg ((divisorTwistHom J L).val.app
      (Opposite.op (U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))) hres6.symm
  -- scalar-section split of the hoisted value
  have hval2 : L.presheaf.map (homOfLE hle5).op
      ((C.presheaf.map (homOfLE (C.basicOpen_le b)).op).hom g • y₀') =
      (C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
        U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g •
        L.presheaf.map (homOfLE hle5).op y₀' := by
    rw [Scheme.Modules.map_smul]
    congr 1
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  -- transport coherence: the chart-top generator restricts to the single-arrow form
  have hcoh : (U.1.toScheme).presheaf.map
      (homOfLE (le_top : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ ⊤)).op
      ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g) =
      (C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
        U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g := by
    rw [Scheme.Opens.ι_appLE]
    rw [show (U.1.toScheme).presheaf.map
        (homOfLE (le_top : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ ⊤)).op =
      C.presheaf.map (U.1.ι.opensFunctor.map
        (homOfLE (le_top : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ ⊤))).op from rfl]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 1
  -- the endomorphism range dies in its cokernel, sectionwise
  have hEkill : ∀ s : Γ(unitObj U.1.toScheme, U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo),
      (Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))).app
        (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
        ((ModularCurves.unitEndomorphismOfTopSection
          ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)).app
          (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) s) = 0 := by
    intro s
    exact congrArg (fun (φ : unitObj U.1.toScheme ⟶ Limits.cokernel
        (ModularCurves.unitEndomorphismOfTopSection
          ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))) =>
      φ.app (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) s)
      (Limits.cokernel.condition (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)))
  -- the transported scalar as a chart section, and the smul-clothing bridge
  let rU : Γ(U.1.toScheme, U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) :=
    (C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
      U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g
  let yW : Γ((restrictFunctor U.1.ι).obj L, U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) :=
    L.presheaf.map (homOfLE hle5).op y₀'
  have hbridge : ((C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
      U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g •
      L.presheaf.map (homOfLE hle5).op y₀' :
        Γ(L, U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo))) = rU • yW := by
    have hIso : (U.1.ι.appIso (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)).inv.hom rU =
        ((C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
          U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g :
            Γ(C, U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo))) := by
      rw [Scheme.Opens.ι_appIso]
      rfl
    calc ((C.presheaf.map (homOfLE ((hle5.trans (C.basicOpen_le b)) :
        U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) ≤ U.1)).op).hom g •
        L.presheaf.map (homOfLE hle5).op y₀' :
          Γ(L, U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)))
        = (U.1.ι.appIso (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)).inv.hom rU •
            (L.presheaf.map (homOfLE hle5).op y₀' :
              Γ(L, U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo))) := by
          rw [hIso]
      _ = rU • yW := rfl
  -- the scalar action on a unit section is the endomorphism value
  have hEform : ∀ s : Γ(unitObj U.1.toScheme, U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo),
      rU • s =
      (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)).app
        (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) s := by
    intro s
    let s' : Γ(U.1.toScheme, U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo) := s
    show rU * s' = s' * (U.1.toScheme).presheaf.map
        (homOfLE (le_top : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ ⊤)).op
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)
    rw [hcoh]
    exact mul_comm rU s'
  -- assemble
  have hnatf := NatTrans.naturality_apply
    (Scheme.Modules.Hom.mapPresheaf
      ((restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom ≫
        Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
          ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))))
    (homOfLE (inf_le_right : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ Uo)).op x
  refine Eq.trans hnatf.symm ?_
  have hsplit : ((restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom ≫
      Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))).app
      (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
      (((restrictFunctor U.1.ι).obj (tensorObj (idealModule J) L)).presheaf.map
        (homOfLE (inf_le_right : U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo ≤ Uo)).op x) =
    (Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))).app
      (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
      (eL.hom.app (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
        (((restrictFunctor U.1.ι).map (divisorTwistHom J L)).app
          (U.1.ι ⁻¹ᵁ C.basicOpen b ⊓ Uo)
          (((restrictFunctor U.1.ι).obj (tensorObj (idealModule J) L)).presheaf.map
            (homOfLE inf_le_right).op x))) := rfl
  refine hsplit.trans ?_
  rw [htwistval, hDchain, hval2, hbridge]
  rw [Hom.app_smul]
  rw [hEform]
  exact hEkill _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-hv iii]** The chart multiplier lies in the span of the transported
generator: the zero-composite and baseSections-exactness over the identity
exhibit it as a multiple of the generator. -/
private theorem twistChartMultiplier_mem_span
    (U : C.affineOpens) (g : Γ(C, U.1))
    (hspan : J.ideal U = Ideal.span {g})
    (hnzd : g ∈ nonZeroDivisors Γ(C, U.1))
    (eI : (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    twistChartMultiplier J L U.1 eI eL ∈
      Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g} := by
  classical
  haveI : IsAffine U.1.toScheme := U.2
  have hg' : (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g ∈
      nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := by
    rw [← MulEquivClass.map_nonZeroDivisors
      (asIso (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge)).commRingCatIsoToRingEquiv]
    exact ⟨g, hnzd, rfl⟩
  haveI hMonoE : Mono (ModularCurves.unitEndomorphismOfTopSection
      ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)) :=
    mono_unitEndomorphismOfTopSection_of_nzd _ hg'
  have hz := restrict_divisorTwistHom_comp_cokernelπ_transport_eq_zero
    (J := J) (L := L) U g hspan eL
  have h0 : (twistChartTensorTriv J L U.1 eI eL).inv ≫
      ((restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom ≫
        Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
          ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))) = 0 := by
    rw [hz]
    exact Limits.comp_zero
  have hval := congrArg (fun (φ : unitObj U.1.toScheme ⟶ Limits.cokernel
      (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))) =>
    φ.val.app (Opposite.op (⊤ : U.1.toScheme.Opens))
      (1 : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))) h0
  have hexact := Scheme.Modules.baseSectionsMap_exact_cokernel
    (𝟙 U.1.toScheme) (ModularCurves.unitEndomorphismOfTopSection
      ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g))
  have hker := LinearMap.exact_iff.mp hexact
  let cB : Scheme.Modules.baseSections (𝟙 U.1.toScheme)
      (unitObj U.1.toScheme) := twistChartMultiplier J L U.1 eI eL
  have hczero : (Scheme.Modules.baseSectionsMap (𝟙 U.1.toScheme)
      (Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)))).hom cB = 0 :=
    hval
  have hmem : cB ∈ LinearMap.ker (Scheme.Modules.baseSectionsMap (𝟙 U.1.toScheme)
      (Limits.cokernel.π (ModularCurves.unitEndomorphismOfTopSection
        ((U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g)))).hom := hczero
  rw [hker] at hmem
  obtain ⟨y, hy⟩ := hmem
  let y' : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := y
  have hyval : (y' * (U.1.toScheme).presheaf.map (homOfLE (le_top :
      (⊤ : U.1.toScheme.Opens) ≤ ⊤)).op ((U.1.ι.appLE U.1 ⊤
        U.1.ι_preimage_self.ge).hom g) : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) =
      twistChartMultiplier J L U.1 eI eL := hy
  have hrestop : (U.1.toScheme).presheaf.map (homOfLE (le_top :
      (⊤ : U.1.toScheme.Opens) ≤ ⊤)).op ((U.1.ι.appLE U.1 ⊤
        U.1.ι_preimage_self.ge).hom g) = (U.1.ι.appLE U.1 ⊤
        U.1.ι_preimage_self.ge).hom g := by
    rw [show (homOfLE (le_top : (⊤ : U.1.toScheme.Opens) ≤ ⊤)) =
      𝟙 (⊤ : U.1.toScheme.Opens) from rfl]
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hrestop] at hyval
  exact Ideal.mem_span_singleton'.mpr ⟨y', hyval⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-hv iv]** The transported generator lies in the span of the chart
multiplier: evaluating the conjugation square on the unit image of
`g ⊗ eL.inv 1` writes the generator as a section multiple of the multiplier. -/
private theorem gen_mem_span_twistChartMultiplier
    (U : C.affineOpens) (g : Γ(C, U.1))
    (hspan : J.ideal U = Ideal.span {g})
    (eI : (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g ∈
      Ideal.span {twistChartMultiplier J L U.1 eI eL} := by
  classical
  -- the generator as an ideal-module section over the image of the top open
  have hgmem : g ∈ idealSections J (Opposite.op U.1) := by
    rw [show idealSections J (Opposite.op U.1) = J.ideal U from
      J.ker_subschemeι_app U, hspan]
    exact Ideal.mem_span_singleton_self g
  let gsec := (idealModule J).val.map
    (homOfLE (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op
    (⟨g, hgmem⟩ : idealSections J (Opposite.op U.1))
  -- the trivializing section of the ambient module
  let l₀ : Γ((restrictFunctor U.1.ι).obj L, (⊤ : U.1.toScheme.Opens)) :=
    eL.inv.app (⊤ : U.1.toScheme.Opens)
      (1 : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
  let l₀C : (L.val.obj (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))) := l₀
  -- the unit image of the tensor and its action value
  have heval := divisorTwistHom_app_unit J L
    (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
    (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
      (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C)
  -- the conjugation square
  have hsq : (restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom =
      (twistChartTensorTriv J L U.1 eI eL).hom ≫
        ModularCurves.unitEndomorphismOfTopSection
          (twistChartMultiplier J L U.1 eI eL) := by
    have hd := unit_endo_eq_ofTopSection
      ((twistChartTensorTriv J L U.1 eI eL).inv ≫
        (restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom)
    calc (restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom
        = (twistChartTensorTriv J L U.1 eI eL).hom ≫
          ((twistChartTensorTriv J L U.1 eI eL).inv ≫
            (restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫ eL.hom) :=
          (Iso.hom_inv_id_assoc _ _).symm
      _ = _ := by rw [hd]; rfl
  -- evaluate the square on the unit image
  have hsqval := congrArg (fun (φ : (restrictFunctor U.1.ι).obj
      (tensorObj (idealModule J) L) ⟶ unitObj U.1.toScheme) =>
    φ.val.app (Opposite.op (⊤ : U.1.toScheme.Opens))
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C))) hsq
  -- the action value is the restricted-generator multiple of the section
  have htm : (idealActionPre J L).app
      (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
      (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C) =
      ((C.presheaf.map (homOfLE
        (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g • l₀C :
          (L.val.obj (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))))) := by
    erw [idealActionPre_app_tmul]
    rfl
  -- smul-clothing bridge at the top open
  let rT : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    (C.presheaf.map (homOfLE
      (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g
  have hIsoT : (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom rT =
      ((C.presheaf.map (homOfLE
        (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g :
          Γ(C, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hbridgeT : ((C.presheaf.map (homOfLE
      (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g • l₀C :
        (L.val.obj (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))))) =
      rT • l₀ := by
    calc ((C.presheaf.map (homOfLE
        (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g • l₀C :
          (L.val.obj (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))))
        = (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom rT •
            (l₀C : (L.val.obj (Opposite.op
              (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))))) := by
          rw [hIsoT]
      _ = rT • l₀ := rfl
  -- the trivializing section maps to one
  have hinvhom : eL.hom.app (⊤ : U.1.toScheme.Opens) l₀ =
      (1 : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) := by
    have h := congrArg (fun (φ : unitObj U.1.toScheme ⟶ unitObj U.1.toScheme) =>
      Scheme.Modules.Hom.app φ (⊤ : U.1.toScheme.Opens)
        (1 : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))) (Iso.inv_hom_id eL)
    exact h
  -- top-restriction collapse for the multiplier
  have hrestopc : (U.1.toScheme).presheaf.map (homOfLE (le_top :
      (⊤ : U.1.toScheme.Opens) ≤ ⊤)).op (twistChartMultiplier J L U.1 eI eL) =
      twistChartMultiplier J L U.1 eI eL := by
    rw [show (homOfLE (le_top : (⊤ : U.1.toScheme.Opens) ≤ ⊤)) =
      𝟙 (⊤ : U.1.toScheme.Opens) from rfl]
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl
  -- the transported generator is the single-arrow restriction
  have hg'eq : (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g = rT := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  -- evaluate the left side of the square down to the generator
  have hLHS : ((restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫
      eL.hom).val.app (Opposite.op (⊤ : U.1.toScheme.Opens)) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C)) =
      (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g := by
    calc ((restrictFunctor U.1.ι).map (divisorTwistHom J L) ≫
        eL.hom).val.app (Opposite.op (⊤ : U.1.toScheme.Opens)) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C))
        = eL.hom.app (⊤ : U.1.toScheme.Opens)
            ((divisorTwistHom J L).val.app
              (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C))) := rfl
      _ = eL.hom.app (⊤ : U.1.toScheme.Opens)
            ((idealActionPre J L).app
              (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
              (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
                (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C)) := by
          rw [heval]
      _ = eL.hom.app (⊤ : U.1.toScheme.Opens)
            (((C.presheaf.map (homOfLE
              (U.1.ι_image_le (⊤ : U.1.toScheme.Opens))).op).hom g • l₀C :
                (L.val.obj (Opposite.op
                  (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))))) := by
          rw [htm]
      _ = eL.hom.app (⊤ : U.1.toScheme.Opens) (rT • l₀) := by
          rw [hbridgeT]
      _ = rT • eL.hom.app (⊤ : U.1.toScheme.Opens) l₀ :=
          Scheme.Modules.Hom.app_smul eL.hom rT l₀
      _ = rT • (1 : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) := by
          rw [hinvhom]
      _ = rT := by
          show rT * 1 = rT
          exact mul_one rT
      _ = (U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g := hg'eq.symm
  -- evaluate the right side of the square to the multiplier multiple
  let w : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    (twistChartTensorTriv J L U.1 eI eL).hom.val.app
      (Opposite.op (⊤ : U.1.toScheme.Opens)) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C))
  have hRHS : ((twistChartTensorTriv J L U.1 eI eL).hom ≫
      ModularCurves.unitEndomorphismOfTopSection
        (twistChartMultiplier J L U.1 eI eL)).val.app
      (Opposite.op (⊤ : U.1.toScheme.Opens)) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C)) =
      w * twistChartMultiplier J L U.1 eI eL := by
    show (ModularCurves.unitEndomorphismOfTopSection
        (twistChartMultiplier J L U.1 eI eL)).val.app
        (Opposite.op (⊤ : U.1.toScheme.Opens))
        ((twistChartTensorTriv J L U.1 eI eL).hom.val.app
          (Opposite.op (⊤ : U.1.toScheme.Opens)) (((PresheafOfModules.sheafificationAdjunction
        (𝟙 C.ringCatSheaf.obj)).unit.app ((idealModule J).val ⊗ L.val)).app
        (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
        (gsec ⊗ₜ[(C.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
          (Opposite.op (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))] l₀C))) = _
    rw [ModularCurves.unitEndomorphismOfTopSection_app_apply]
    rw [hrestopc]
  refine Ideal.mem_span_singleton'.mpr ⟨w, ?_⟩
  exact (hRHS.symm.trans hsqval.symm).trans hLHS

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[A4-hv] The chart multiplier's span is the transported generator's span** —
for ANY pair of chart trivializations. Feeds the `hv` slot of the rank-two
interface without ever computing the multiplier through the opaque tensor
trivialization. -/
theorem span_twistChartMultiplier_eq
    (U : C.affineOpens) (g : Γ(C, U.1))
    (hspan : J.ideal U = Ideal.span {g})
    (hnzd : g ∈ nonZeroDivisors Γ(C, U.1))
    (eI : (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    Ideal.span {twistChartMultiplier J L U.1 eI eL} =
      Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom g} := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem]
    exact twistChartMultiplier_mem_span J L U g hspan hnzd eI eL
  · rw [Ideal.span_singleton_le_iff_mem]
    exact gen_mem_span_twistChartMultiplier J L U g hspan eI eL

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[e2] The rank-two coordinates of the divisor restriction.** Chart-native form:
given trivializations of the ideal module and the ambient module on a concentrating
chart, a span identification of the conjugated multiplier as a product of two
generators, the first of them a nonzerodivisor, and evaluation equivalences for the
two factors, the base sections of the twist cokernel are free of rank two. -/
theorem nonempty_baseSections_cokernel_divisorTwistHom_equiv_pair
    {S : Scheme.{u}} {π : C ⟶ S} (J : C.IdealSheafData) (L : C.Modules)
    (U : C.affineOpens)
    (eI : (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (V : C.Opens) (hUV : U.1 ⊔ V = ⊤)
    (htriv : ∀ (W : C.Opens), W ≤ V →
      (1 : Γ(C, W)) ∈ idealSections J (Opposite.op W))
    (hMono : Mono ((restrictFunctor U.1.ι).map (divisorTwistHom J L)))
    (rP' rQ' : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (hv : Ideal.span {twistChartMultiplier J L U.1 eI eL} =
      Ideal.span {rP' * rQ'})
    (hrP' : rP' ∈ nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens))
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    (eP : (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸ Ideal.span {rP'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens)))
    (eQ : (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸ Ideal.span {rQ'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) :
    Nonempty ((Scheme.Modules.baseSections π
        (Limits.cokernel (divisorTwistHom J L)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] (Fin 2 → Γ(S, (⊤ : S.Opens)))) := by
  classical
  haveI hMono' := hMono
  haveI : IsAffine U.1.toScheme := U.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (twistChartMultiplier J L U.1 eI eL)) :=
    mono_unitEndo_twistChartMultiplier J L U.1 eI eL
  -- concentration and transport to the multiplier cokernel
  have hbij := cokernel_divisorTwistHom_bijective_restrict J L U.1 V hUV htriv
  let i1 := Scheme.Modules.baseSectionsRestrictIsoOfBijective π
    (Limits.cokernel (divisorTwistHom J L)) U.1 hbij
  let i2 := Scheme.Modules.baseSectionsMapIso (U.1.ι ≫ π)
    (Limits.PreservesCokernel.iso (restrictFunctor U.1.ι)
      (divisorTwistHom J L))
  let i3 := Scheme.Modules.baseSectionsMapIso (U.1.ι ≫ π)
    (cokernelRestrictTwistUnitEndoIso J L U.1 eI eL)
  -- the multiplier cokernel's base sections are the quotient (the CORE)
  obtain ⟨eCore⟩ := nonempty_baseSections_cokernel_unitEndo_equiv
    (U.1.ι ≫ π) (twistChartMultiplier J L U.1 eI eL) halg
  -- span identification and the ring-level split
  let eA : (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸
      Ideal.span {twistChartMultiplier J L U.1 eI eL}) ≃ₗ[
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
      (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸
        Ideal.span {rP' * rQ'}) :=
    Submodule.quotEquivOfEq _ _ hv
  let eSpan := eA.restrictScalars Γ(S, (⊤ : S.Opens))
  let e3a := ModularCurves.quotientSpanMulEquivProd rP' rQ' hrP' eP eQ
  exact ⟨(((i1 ≪≫ i2 ≪≫ i3).toLinearEquiv).trans eCore).trans
    (eSpan.trans e3a)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[e1] The rank-one coordinate of the divisor restriction** (the vertical's
degree-one case): with a single-generator span identification of the conjugated
multiplier and one evaluation equivalence, the base sections of the twist cokernel
are free of rank one. -/
theorem nonempty_baseSections_cokernel_divisorTwistHom_equiv_single
    {S : Scheme.{u}} {π : C ⟶ S} (J : C.IdealSheafData) (L : C.Modules)
    (U : C.affineOpens)
    (eI : (restrictFunctor U.1.ι).obj (idealModule J) ≅ unitObj U.1.toScheme)
    (eL : (restrictFunctor U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (V : C.Opens) (hUV : U.1 ⊔ V = ⊤)
    (htriv : ∀ (W : C.Opens), W ≤ V →
      (1 : Γ(C, W)) ∈ idealSections J (Opposite.op W))
    (hMono : Mono ((restrictFunctor U.1.ι).map (divisorTwistHom J L)))
    (r' : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)))
    (hv : Ideal.span {twistChartMultiplier J L U.1 eI eL} =
      Ideal.span {r'})
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens))
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r)
    (eP : (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸ Ideal.span {r'})
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) :
    Nonempty ((Scheme.Modules.baseSections π
        (Limits.cokernel (divisorTwistHom J L)))
      ≃ₗ[Γ(S, (⊤ : S.Opens))] Γ(S, (⊤ : S.Opens))) := by
  classical
  haveI hMono' := hMono
  haveI : IsAffine U.1.toScheme := U.2
  haveI hMonoEndo : Mono (ModularCurves.unitEndomorphismOfTopSection
      (twistChartMultiplier J L U.1 eI eL)) :=
    mono_unitEndo_twistChartMultiplier J L U.1 eI eL
  -- concentration and transport to the multiplier cokernel
  have hbij := cokernel_divisorTwistHom_bijective_restrict J L U.1 V hUV htriv
  let i1 := Scheme.Modules.baseSectionsRestrictIsoOfBijective π
    (Limits.cokernel (divisorTwistHom J L)) U.1 hbij
  let i2 := Scheme.Modules.baseSectionsMapIso (U.1.ι ≫ π)
    (Limits.PreservesCokernel.iso (restrictFunctor U.1.ι)
      (divisorTwistHom J L))
  let i3 := Scheme.Modules.baseSectionsMapIso (U.1.ι ≫ π)
    (cokernelRestrictTwistUnitEndoIso J L U.1 eI eL)
  -- the multiplier cokernel's base sections are the quotient (the CORE)
  obtain ⟨eCore⟩ := nonempty_baseSections_cokernel_unitEndo_equiv
    (U.1.ι ≫ π) (twistChartMultiplier J L U.1 eI eL) halg
  -- span identification and the evaluation
  let eA : (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸
      Ideal.span {twistChartMultiplier J L U.1 eI eL}) ≃ₗ[
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
      (Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) ⧸
        Ideal.span {r'}) :=
    Submodule.quotEquivOfEq _ _ hv
  let eSpan := eA.restrictScalars Γ(S, (⊤ : S.Opens))
  exact ⟨(((i1 ≪≫ i2 ≪≫ i3).toLinearEquiv).trans eCore).trans
    (eSpan.trans eP)⟩


end LineAssembly

end Twist

end AlgebraicGeometry.Scheme.Modules
