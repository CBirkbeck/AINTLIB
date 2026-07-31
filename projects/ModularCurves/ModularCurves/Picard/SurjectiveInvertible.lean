/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule

/-!
# Locally surjective maps of invertible modules are isomorphisms

The injectivity-free isomorphism criterion for line modules: a map of invertible
`𝒪ₓ`-modules whose underlying map of presheaves of abelian groups is locally surjective
is an isomorphism. Locally both sides trivialize to the structure sheaf, a module endo
of `𝒪` is multiplication by its value at `1`, and local surjectivity at the section `1`
makes that multiplier a unit — so injectivity comes for free and is never analyzed on
the (opaque) side of the map's domain.

This is the [A7-2] engine for `sheafificationW_idealPullHom`
(`Picard/IdealModulePullback.lean`): the sheafified ideal-pullback comparison is a map
of invertible modules, and only its local surjectivity needs elementwise work.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {Z : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A locally surjective module endomorphism of the structure sheaf is an isomorphism:
it is multiplication by its value at `1`, and local surjectivity at `1` exhibits local
inverses of that value, so the multiplier is a unit on a basis of opens. -/
theorem isIso_of_isLocallySurjective_unit_hom
    (u : unitObj Z ⟶ unitObj Z)
    (hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map u.val)) :
    IsIso u := by
  -- the multiplier of `u` over an open, as a section of the structure sheaf
  let cW : ∀ W : Z.Opens, Γ(Z, W) := fun W => u.val.app (op W) (1 : Γ(Z, W))
  have happ : ∀ (W : Z.Opens) (x : Γ(Z, W)),
      u.val.app (op W) x = x * cW W := by
    intro W x
    have hsmul := (u.val.app (op W)).hom.map_smul x (1 : Γ(Z, W))
    calc u.val.app (op W) x
        = u.val.app (op W) ((x * 1 : Γ(Z, W))) := by rw [mul_one]
      _ = x * cW W := hsmul
  refine isIso_of_bijective_app_on_basis u {W : Z.Opens | IsUnit (cW W)} ?_ ?_
  · intro x U hxU
    have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map u.val) (U := op U) (1 : Γ(Z, U))
    rw [Opens.mem_grothendieckTopology] at hmem
    obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := hmem x hxU
    refine ⟨V, ?_, hxV, i.le⟩
    have ht2 : u.val.app (op V) (t : Γ(Z, V)) = (1 : Γ(Z, V)) := by
      have hmap1 : ((Z.ringCatSheaf.obj).map i.op).hom (1 : Γ(Z, U)) =
          (1 : Γ(Z, V)) := map_one _
      exact ht.trans hmap1
    have hmul := (happ V t).symm.trans ht2
    refine isUnit_iff_exists.mpr ⟨t, ?_, ?_⟩
    · rw [mul_comm]
      exact hmul
    · exact hmul
  · intro W hW
    obtain ⟨c, hc⟩ := hW
    constructor
    · intro a b hab
      have hcc := (happ W a).symm.trans (hab.trans (happ W b))
      rw [← hc] at hcc
      have h3 := congrArg (fun z => z * (↑c⁻¹ : Γ(Z, W))) hcc
      simp only [mul_assoc, Units.mul_inv, mul_one] at h3
      exact h3
    · intro y
      let y' : Γ(Z, W) := y
      have h5 : u.val.app (op W) (y' * (↑c⁻¹ : Γ(Z, W))) =
          y' * (↑c⁻¹ : Γ(Z, W)) * cW W := happ W _
      rw [← hc] at h5
      have h6 : y' * (↑c⁻¹ : Γ(Z, W)) * (↑c : Γ(Z, W)) = y' := by
        rw [mul_assoc, Units.inv_mul, mul_one]
      exact ⟨y' * (↑c⁻¹ : Γ(Z, W)), h5.trans h6⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Local surjectivity restricts along an open immersion of opens: sections of the
restricted modules are literally sections over image opens, so the covering data
transports through the preimage. -/
theorem isLocallySurjective_restrictFunctor_map {A B : Z.Modules} (g : A ⟶ B)
    (hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map g.val))
    (W : Z.Opens) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥W.toScheme)
      ((PresheafOfModules.toPresheaf _).map ((restrictFunctor W.ι).map g).val) := by
  constructor
  intro V s
  rw [Opens.mem_grothendieckTopology]
  intro x hxV
  -- `s` is a section of `B` over the image open; localize the `Z`-level surjectivity
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥Z)
    ((PresheafOfModules.toPresheaf _).map g.val) (U := op (W.ι ''ᵁ V))
    (s : ToType (((PresheafOfModules.toPresheaf _).obj B.val).obj (op (W.ι ''ᵁ V))))
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V₂, i, ⟨t, ht⟩, hxV₂⟩ := hmem (W.ι.base x) ⟨x, hxV, rfl⟩
  refine ⟨W.ι ⁻¹ᵁ V₂ ⊓ V, homOfLE inf_le_right, ?_,
    ⟨show W.ι.base x ∈ V₂ from hxV₂, hxV⟩⟩
  have hle : W.ι ''ᵁ (W.ι ⁻¹ᵁ V₂ ⊓ V) ≤ V₂ := by
    refine le_trans ((W.ι.opensFunctor.map (homOfLE inf_le_left)).le) ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  refine ⟨((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op t, ?_⟩
  show ((PresheafOfModules.toPresheaf _).map g.val).app
      (op (W.ι ''ᵁ (W.ι ⁻¹ᵁ V₂ ⊓ V)))
      (((PresheafOfModules.toPresheaf _).obj A.val).map (homOfLE hle).op t) = _
  rw [NatTrans.naturality_apply, ht]
  show (((PresheafOfModules.toPresheaf _).obj B.val).map i.op ≫
    ((PresheafOfModules.toPresheaf _).obj B.val).map (homOfLE hle).op) s = _
  rw [← Functor.map_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **A locally surjective map of invertible `𝒪ₓ`-modules is an isomorphism.** On a
common refinement of the two trivializing covers the map conjugates to a module endo of
the structure sheaf, which is multiplication by a section that local surjectivity makes
a unit; being an isomorphism is Zariski-local. Injectivity of the original map is never
used — this is the isomorphism criterion of choice when the domain is an opaque
(left-adjoint) pullback. -/
theorem isIso_of_isLocallySurjective_of_isInvertible {A B : Z.Modules} (g : A ⟶ B)
    (hA : IsInvertible A) (hB : IsInvertible B)
    (hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥Z)
      ((PresheafOfModules.toPresheaf _).map g.val)) :
    IsIso g := by
  obtain ⟨ιA, U, hU, htA⟩ := hA
  obtain ⟨ιB, V, hV, htB⟩ := hB
  refine isIso_of_isIso_restrict g (fun p : ιA × ιB => U p.1 ⊓ V p.2) ?_ ?_
  · refine le_antisymm le_top ?_
    intro x _
    have hxU : x ∈ iSup U := by rw [hU]; trivial
    have hxV : x ∈ iSup V := by rw [hV]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxV
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hxi, hxj⟩
  · rintro ⟨i, j⟩
    obtain ⟨eA⟩ := htA i
    obtain ⟨eB⟩ := htB j
    have tA : A.restrict (U i ⊓ V j).ι ≅ unitObj (U i ⊓ V j).toScheme :=
      restrictIsoOfPullbackIso A (U i ⊓ V j)
        (restrictTrivialization inf_le_left eA)
    have tB : B.restrict (U i ⊓ V j).ι ≅ unitObj (U i ⊓ V j).toScheme :=
      restrictIsoOfPullbackIso B (U i ⊓ V j)
        (restrictTrivialization inf_le_right eB)
    have hres := isLocallySurjective_restrictFunctor_map g hs (U i ⊓ V j)
    haveI hvA : IsIso tA.inv.val :=
      inferInstanceAs (IsIso ((SheafOfModules.forget _).map tA.symm.hom))
    haveI hvB : IsIso tB.hom.val :=
      inferInstanceAs (IsIso ((SheafOfModules.forget _).map tB.hom))
    haveI hiA : IsIso ((PresheafOfModules.toPresheaf _).map tA.inv.val) :=
      inferInstance
    haveI hiB : IsIso ((PresheafOfModules.toPresheaf _).map tB.hom.val) :=
      inferInstance
    have hws : Presheaf.IsLocallySurjective (Opens.grothendieckTopology
        ↥(U i ⊓ V j).toScheme)
        ((PresheafOfModules.toPresheaf _).map
          (tA.inv ≫ (restrictFunctor (U i ⊓ V j).ι).map g ≫ tB.hom).val) := by
      show Presheaf.IsLocallySurjective _
        ((PresheafOfModules.toPresheaf _).map
          (tA.inv.val ≫ ((restrictFunctor (U i ⊓ V j).ι).map g).val ≫ tB.hom.val))
      rw [Functor.map_comp, Functor.map_comp]
      haveI := hres
      infer_instance
    haveI := isIso_of_isLocallySurjective_unit_hom _ hws
    have hg : (restrictFunctor (U i ⊓ V j).ι).map g =
        tA.hom ≫ (tA.inv ≫ (restrictFunctor (U i ⊓ V j).ι).map g ≫ tB.hom) ≫
          tB.inv := by
      simp
    rw [hg]
    infer_instance

end AlgebraicGeometry.Scheme.Modules
