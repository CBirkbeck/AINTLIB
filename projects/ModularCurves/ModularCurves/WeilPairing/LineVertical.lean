/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule
import ModularCurves.ForMathlib.CrossProductKernel
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

end LineAssembly

end Twist

end AlgebraicGeometry.Scheme.Modules
