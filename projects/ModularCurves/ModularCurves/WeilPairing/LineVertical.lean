/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule

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

end Twist

end AlgebraicGeometry.Scheme.Modules
