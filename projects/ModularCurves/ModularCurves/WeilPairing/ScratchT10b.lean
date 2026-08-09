import ModularCurves.WeilPairing.TheoremOfSquareField

open CategoryTheory AlgebraicGeometry Opposite

universe u

theorem ker_ideal_of_fromSpec_factor {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {A : CommRingCat.{u}} (φ : Γ(X, U) ⟶ A) (f : Spec A ⟶ X) [QuasiCompact f]
    (hfac : f = Spec.map φ ≫ hU.fromSpec) :
    (Scheme.Hom.ker f).ideal ⟨U, hU⟩ = RingHom.ker φ.hom := by
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    rw [hfac]
    show Spec.map φ ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) = ⊤
    rw [hU.fromSpec_preimage_self]
    rfl
  have hi : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ U := le_of_eq hpre.symm
  -- `appLE` at the top open has the same kernel as `app`, the restriction being an iso
  have hkerApp : RingHom.ker ((f.app U)).hom = RingHom.ker ((f.appLE U ⊤ hi)).hom := by
    haveI : IsIso (homOfLE hi) :=
      ⟨homOfLE (le_of_eq hpre), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    have hinj : Function.Injective (((Spec A).presheaf.map (homOfLE hi).op)).hom :=
      (ConcreteCategory.bijective_of_isIso ((Spec A).presheaf.map (homOfLE hi).op)).1
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    show ((f.app U)).hom a = 0 ↔
      (((Spec A).presheaf.map (homOfLE hi).op)).hom (((f.app U)).hom a) = 0
    exact ⟨fun ha => by rw [ha, map_zero], fun ha => hinj (by rw [ha, map_zero])⟩
  -- `appLE` at the top open is `φ` followed by the `Γ`-`Spec` identification
  have happ : f.appLE U ⊤ hi = φ ≫ (Scheme.ΓSpecIso A).inv := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp]
    have h1 := hU.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec A)) hi
    have h2 : (isAffineOpen_top (Spec A)).fromSpec = Spec.map (Scheme.ΓSpecIso A).inv := by
      rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rw [h2] at h1
    rw [← cancel_mono hU.fromSpec]
    refine h1.trans ?_
    rw [Category.assoc, ← hfac]
  have hinj2 : Function.Injective (((Scheme.ΓSpecIso A).inv)).hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1
  rw [Scheme.Hom.ker_apply, hkerApp, happ, CommRingCat.hom_comp, ← RingHom.comap_ker]
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  exact ⟨fun h => hinj2 (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
