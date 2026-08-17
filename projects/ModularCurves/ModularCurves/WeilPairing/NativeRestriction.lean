/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldLeaf

/-!
# Restriction-compatibility of the native tensor-ideal trivialisation ([NAT-RESTRICT])

The `ORD-G` pointwise divisor computation (`.mathlib-quality/decomposition-e4a-self.md`,
cont.19) needs the transition units of the G2 chart dataset to decompose into *per-chart*
factors; the `a`/`b` dressing units of `transitionUnitOfCover_eq_dressed_native` live only
on overlaps, which blocks the germ-order reading away from the anchor chart. The fix is
that with the e-family built from `nativeTensorIdealTriv` the dressing disappears, because
the native trivialisation *restricts on the nose*:

* `nuPullback_app_restrictTransport` ([NR-1], the brick): the `ν`-comparison map is
  natural under the open-restriction transport, at the level of `⊤`-sections.
* `restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu` ([NR-2]): the restricted
  native trivialisation satisfies the `W`-level `ν`-characterisation.
* `restrictTrivialization_nativeTensorIdealTriv` ([NR-3], NAT-RESTRICT): the restriction
  of the native trivialisation *is* the native trivialisation of the restricted
  generators.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
  AlgebraicGeometry.Scheme.Modules

-- the semireducible sheaf-type wall (v4.33 idiom)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

section NativeRestriction

variable {X : Scheme.{u}} (M : X.Modules)
variable (J₁ J₂ : X.IdealSheafData)
variable (e : tensorObj M (AlgebraicGeometry.Scheme.Modules.idealModule J₁) ≅
  AlgebraicGeometry.Scheme.Modules.idealModule J₂)

/-- The `⊤`-section transport of the open restriction `W ≤ V`: adjunction unit, `eqToHom`
re-indexing, composition iso, congruence — the composite whose value at the trivialising
section is computed by `restrictTrivialization_inv_app_top_one`. -/
noncomputable def restrictTransportSection {V W : X.Opens} (hWV : W ≤ V) (P : X.Modules)
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj P).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    ((Scheme.Modules.pullback W.ι).obj P).val.obj
      (Opposite.op (⊤ : W.toScheme.Opens)) :=
  ((Scheme.Modules.pullbackCongr (X.homOfLE_ι hWV).symm).app P).inv.val.app
    (Opposite.op (⊤ : W.toScheme.Opens))
    (((Scheme.Modules.pullbackComp (X.homOfLE hWV) V.ι).app P).hom.val.app
      (Opposite.op (⊤ : W.toScheme.Opens))
      (((Scheme.Modules.pullback (X.homOfLE hWV)).obj
          ((Scheme.Modules.pullback V.ι).obj P)).presheaf.map (eqToHom htop).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
            (X.homOfLE hWV)).unit.app
          ((Scheme.Modules.pullback V.ι).obj P)).val.app
          (Opposite.op (⊤ : V.toScheme.Opens)) x)))

/-- **([NR-ext])** A hom out of the unit sheaf of modules is determined by its value at
the `⊤`-section `1`: the section it corresponds to under `unitHomEquiv` is res-compatible,
so its `⊤`-value pins every value. -/
theorem unit_hom_ext {Y : Scheme.{u}} {N : Y.Modules} (f g : unitObj Y ⟶ N)
    (h : f.val.app (Opposite.op (⊤ : Y.Opens))
        (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1) =
      g.val.app (Opposite.op (⊤ : Y.Opens))
        (show Y.presheaf.obj (Opposite.op (⊤ : Y.Opens)) from 1)) : f = g := by
  apply (SheafOfModules.unitHomEquiv N).injective
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  have hf := PresheafOfModules.sections_property ((SheafOfModules.unitHomEquiv N) f)
    (X := Opposite.op (⊤ : Y.Opens)) (Y := U) (homOfLE le_top).op
  have hg := PresheafOfModules.sections_property ((SheafOfModules.unitHomEquiv N) g)
    (X := Opposite.op (⊤ : Y.Opens)) (Y := U) (homOfLE le_top).op
  rw [← hf, ← hg]
  exact congrArg _ h

/-- **([NR-ots])** The open-restriction of an `openTopSection` along `W ≤ V` is the
`openTopSection` of the restricted section: the two cast-paths from `Γ(X, V)` to
`Γ(W, ⊤)` agree. -/
theorem openTopSection_homOfLE {X : Scheme.{u}} {V W : X.Opens} (hWV : W ≤ V)
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (r : Γ(X, V)) :
    W.toScheme.presheaf.map (eqToHom htop).op
        ((Scheme.Hom.app (X.homOfLE hWV) (⊤ : V.toScheme.Opens)).hom
          (Scheme.Modules.openTopSection V r)) =
      Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op r) := by
  simp only [Scheme.Modules.openTopSection, Scheme.Opens.ι_appIso, Iso.refl_hom,
    Scheme.homOfLE_app]
  rw [show W.toScheme.presheaf.map (eqToHom htop).op =
    X.presheaf.map (W.ι.opensFunctor.map (eqToHom htop)).op from rfl]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  simp only [Category.comp_id, Category.id_comp, ← Functor.map_comp, ← op_comp]
  exact congrArg
    (fun (q : (W.ι ''ᵁ (⊤ : W.toScheme.Opens) : X.Opens) ⟶ V) =>
      (ConcreteCategory.hom (X.presheaf.map q.op)) r)
    (Subsingleton.elim _ _)

/-- **([NR-1], the brick)** The `ν`-comparison map is natural under the open-restriction
transport at `⊤`-sections: evaluating the `W`-level `ν` on a transported `V`-section is
the scheme-restriction of the `V`-level `ν`-value. -/
theorem nuPullback_app_restrictTransport {V W : X.Opens} (hWV : W ≤ V)
    (g₁ : Γ(X, V)) (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (htop : (⊤ : W.toScheme.Opens) = (X.homOfLE hWV) ⁻¹ᵁ (⊤ : V.toScheme.Opens))
    (x : ((Scheme.Modules.pullback V.ι).obj M).val.obj
      (Opposite.op (⊤ : V.toScheme.Opens))) :
    (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁').val.app
        (Opposite.op (⊤ : W.toScheme.Opens))
        (restrictTransportSection hWV M htop x) =
      W.toScheme.presheaf.map (eqToHom htop).op
        ((Scheme.Hom.app (X.homOfLE hWV) (⊤ : V.toScheme.Opens)).hom
          ((nuPullback M J₁ J₂ e V g₁ hg₁ hgi₁).val.app
            (Opposite.op (⊤ : V.toScheme.Opens)) x)) := by
  sorry

/-- **([NR-2])** The restricted native trivialisation satisfies the `W`-level
`ν`-characterisation with the restricted second generator. -/
theorem restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu
    {V W : X.Opens} (hWV : W ≤ V)
    (g₁ g₂ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op V))
    (hgi₂ : IsIso (idealGenHom J₂ V g₂ hg₂))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁')) :
    (restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv ≫
      nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁' =
      ModularCurves.unitEndomorphismOfTopSection
        (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op g₂)) := by
  sorry

/-- **([NR-3], NAT-RESTRICT)** The restriction of the native tensor-ideal trivialisation
is the native trivialisation of the restricted generators. -/
theorem restrictTrivialization_nativeTensorIdealTriv
    {V W : X.Opens} (hWV : W ≤ V)
    (g₁ g₂ : Γ(X, V))
    (hg₁ : g₁ ∈ idealSections J₁ (Opposite.op V))
    (hgi₁ : IsIso (idealGenHom J₁ V g₁ hg₁))
    (hg₂ : g₂ ∈ idealSections J₂ (Opposite.op V))
    (hgi₂ : IsIso (idealGenHom J₂ V g₂ hg₂))
    (hg₁' : X.presheaf.map (homOfLE hWV).op g₁ ∈ idealSections J₁ (Opposite.op W))
    (hgi₁' : IsIso (idealGenHom J₁ W (X.presheaf.map (homOfLE hWV).op g₁) hg₁'))
    (hg₂' : X.presheaf.map (homOfLE hWV).op g₂ ∈ idealSections J₂ (Opposite.op W))
    (hgi₂' : IsIso (idealGenHom J₂ W (X.presheaf.map (homOfLE hWV).op g₂) hg₂'))
    (hmono : Mono (ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W (X.presheaf.map (homOfLE hWV).op g₂)))) :
    restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂) =
      nativeTensorIdealTriv M J₁ J₂ e W
        (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
        hg₁' hgi₁' hg₂' hgi₂' := by
  have h₁ := restrictTrivialization_nativeTensorIdealTriv_inv_comp_nu M J₁ J₂ e hWV
    g₁ g₂ hg₁ hgi₁ hg₂ hgi₂ hg₁' hgi₁'
  have h₂ := nativeTensorIdealTriv_inv_comp_nu M J₁ J₂ e W
    (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
    hg₁' hgi₁' hg₂' hgi₂'
  have hread := pullbackTrivialization_inv_comp_hom_of_nu M
    (restrictTrivialization hWV
      (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂))
    (nativeTensorIdealTriv M J₁ J₂ e W
      (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
      hg₁' hgi₁' hg₂' hgi₂')
    (nuPullback M J₁ J₂ e W (X.presheaf.map (homOfLE hWV).op g₁) hg₁' hgi₁')
    (X.presheaf.map (homOfLE hWV).op g₂) (X.presheaf.map (homOfLE hWV).op g₂) 1
    h₁ h₂ (one_mul _).symm hmono
  have hone : ModularCurves.unitEndomorphismOfTopSection
      (Scheme.Modules.openTopSection W
        (1 : Γ(X, W))) = 𝟙 (unitObj W.toScheme) := by
    have h1 : Scheme.Modules.openTopSection W (1 : Γ(X, W)) =
        (1 : Γ(W.toScheme, ⊤)) := by
      simp [Scheme.Modules.openTopSection, map_one]
    rw [h1]
    exact ModularCurves.unitEndomorphismOfTopSection_one
  rw [hone] at hread
  have hhom : (nativeTensorIdealTriv M J₁ J₂ e W
      (X.presheaf.map (homOfLE hWV).op g₁) (X.presheaf.map (homOfLE hWV).op g₂)
      hg₁' hgi₁' hg₂' hgi₂').hom =
      (restrictTrivialization hWV
        (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).hom := by
    calc (nativeTensorIdealTriv M J₁ J₂ e W _ _ hg₁' hgi₁' hg₂' hgi₂').hom
        = (restrictTrivialization hWV
            (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).hom ≫
          (restrictTrivialization hWV
            (nativeTensorIdealTriv M J₁ J₂ e V g₁ g₂ hg₁ hgi₁ hg₂ hgi₂)).inv ≫
          (nativeTensorIdealTriv M J₁ J₂ e W _ _ hg₁' hgi₁' hg₂' hgi₂').hom := by
          rw [Iso.hom_inv_id_assoc]
      _ = _ := by rw [hread, Category.comp_id]
  exact (Iso.ext hhom.symm)

end NativeRestriction

end ModularCurves
