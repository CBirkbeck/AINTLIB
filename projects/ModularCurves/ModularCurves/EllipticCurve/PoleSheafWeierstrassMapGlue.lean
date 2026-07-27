/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapOverlap
import ModularCurves.ForMathlib.SpecBasicOpenAway

/-!
# Gluing the pole-sheaf Weierstrass comparison map

The projective comparison maps constructed in a Cartier frame near the marked
section and in the canonical frame away from the section glue on their union.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

private theorem exists_glue_on_sup
    {X Y : Scheme.{u}} (U V : X.Opens)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (hUV : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ fU =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ fV) :
    ∃ f : (U ⊔ V).toScheme ⟶ Y,
      X.homOfLE le_sup_left ≫ f = fU ∧
      X.homOfLE le_sup_right ≫ f = fV := by
  let D : Bool → X.Opens
    | false => U
    | true => V
  let F : (b : Bool) → (D b).toScheme ⟶ Y
    | false => fU
    | true => fV
  have hD : (⨆ b, D b) = U ⊔ V := by
    apply le_antisymm
    · refine iSup_le fun b => ?_
      cases b
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup D false) (le_iSup D true)
  have hF : ∀ b c,
      X.homOfLE (inf_le_left : D b ⊓ D c ≤ D b) ≫ F b =
        X.homOfLE (inf_le_right : D b ⊓ D c ≤ D c) ≫ F c := by
    intro b c
    cases b <;> cases c
    · simp only [D, F]
    · exact hUV
    · simp only [D, F]
      have hVU : V ⊓ U ≤ U ⊓ V := le_of_eq (inf_comm V U)
      have h := congrArg (X.homOfLE hVU ≫ ·) hUV.symm
      simpa only [← Category.assoc, Scheme.homOfLE_homOfLE] using h
    · simp only [D, F]
  let G : (⨆ b, D b).toScheme ⟶ Y :=
    (Scheme.Opens.iSupOpenCover D).glueMorphisms F
      (glueMorphisms_hf_of_agree D F hF)
  let e : (⨆ b, D b).toScheme ≅ (U ⊔ V).toScheme :=
    X.isoOfEq hD
  have hUe :
      X.homOfLE le_sup_left ≫ e.inv =
        X.homOfLE (le_iSup D false) := by
    rw [← cancel_mono (⨆ b, D b).ι]
    simp only [Category.assoc, e, Scheme.isoOfEq_inv_ι,
      Scheme.homOfLE_ι]
    rfl
  have hVe :
      X.homOfLE le_sup_right ≫ e.inv =
        X.homOfLE (le_iSup D true) := by
    rw [← cancel_mono (⨆ b, D b).ι]
    simp only [Category.assoc, e, Scheme.isoOfEq_inv_ι,
      Scheme.homOfLE_ι]
    rfl
  refine ⟨e.inv ≫ G, ?_, ?_⟩
  · rw [← Category.assoc, hUe]
    exact (Scheme.Opens.iSupOpenCover D).ι_glueMorphisms
      F (glueMorphisms_hf_of_agree D F hF) false
  · rw [← Category.assoc, hVe]
    exact (Scheme.Opens.iSupOpenCover D).ι_glueMorphisms
      F (glueMorphisms_hf_of_agree D F hF) true

private theorem hom_ext_on_sup
    {X Y : Scheme.{u}} (U V : X.Opens)
    (f g : (U ⊔ V).toScheme ⟶ Y)
    (hU : X.homOfLE le_sup_left ≫ f =
      X.homOfLE le_sup_left ≫ g)
    (hV : X.homOfLE le_sup_right ≫ f =
      X.homOfLE le_sup_right ≫ g) :
    f = g := by
  let D : Bool → X.Opens
    | false => U
    | true => V
  have hD : (⨆ b, D b) = U ⊔ V := by
    apply le_antisymm
    · refine iSup_le fun b => ?_
      cases b
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup D false) (le_iSup D true)
  let e : (⨆ b, D b).toScheme ≅ (U ⊔ V).toScheme :=
    X.isoOfEq hD
  have hUe :
      X.homOfLE (le_iSup D false) ≫ e.hom =
        X.homOfLE le_sup_left := by
    rw [← cancel_mono (U ⊔ V).ι]
    simp only [Category.assoc, e, Scheme.isoOfEq_hom_ι,
      Scheme.homOfLE_ι]
    rw [Scheme.homOfLE_ι]
  have hVe :
      X.homOfLE (le_iSup D true) ≫ e.hom =
        X.homOfLE le_sup_right := by
    rw [← cancel_mono (U ⊔ V).ι]
    simp only [Category.assoc, e, Scheme.isoOfEq_hom_ι,
      Scheme.homOfLE_ι]
    rw [Scheme.homOfLE_ι]
  rw [← cancel_epi e.hom]
  apply (Scheme.Opens.iSupOpenCover D).hom_ext
  intro b
  cases b
  · change X.homOfLE (le_iSup D false) ≫ e.hom ≫ f =
      X.homOfLE (le_iSup D false) ≫ e.hom ≫ g
    simpa only [← Category.assoc, hUe] using hU
  · change X.homOfLE (le_iSup D true) ≫ e.hom ≫ f =
      X.homOfLE (le_iSup D true) ≫ e.hom ≫ g
    simpa only [← Category.assoc, hVe] using hV

private theorem exists_glue_on_sup_over
    {X Y Z : Scheme.{u}} (U V : X.Opens)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (p : Y ⟶ Z) (b : X ⟶ Z)
    (hUV : X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ fU =
      X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ fV)
    (hU : fU ≫ p = U.ι ≫ b)
    (hV : fV ≫ p = V.ι ≫ b) :
    ∃ f : (U ⊔ V).toScheme ⟶ Y,
      X.homOfLE le_sup_left ≫ f = fU ∧
      X.homOfLE le_sup_right ≫ f = fV ∧
      f ≫ p = (U ⊔ V).ι ≫ b := by
  obtain ⟨f, hfU, hfV⟩ := exists_glue_on_sup U V fU fV hUV
  refine ⟨f, hfU, hfV, hom_ext_on_sup U V _ _ ?_ ?_⟩
  · rw [← Category.assoc, hfU, hU]
    rw [← Category.assoc, Scheme.homOfLE_ι]
  · rw [← Category.assoc, hfV, hV]
    rw [← Category.assoc, Scheme.homOfLE_ι]

private theorem exists_global_of_exists_on_sup
    {X Y Z : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
    (fU : U.toScheme ⟶ Y) (fV : V.toScheme ⟶ Y)
    (f : (U ⊔ V).toScheme ⟶ Y)
    (hfU : X.homOfLE le_sup_left ≫ f = fU)
    (hfV : X.homOfLE le_sup_right ≫ f = fV)
    (p : Y ⟶ Z) (b : X ⟶ Z)
    (hf : f ≫ p = (U ⊔ V).ι ≫ b) :
    ∃ g : X ⟶ Y,
      U.ι ≫ g = fU ∧ V.ι ≫ g = fV ∧ g ≫ p = b := by
  let e : (U ⊔ V).toScheme ≅ X :=
    (X.isoOfEq hUV).trans X.topIso
  have hUe : U.ι ≫ e.inv = X.homOfLE le_sup_left := by
    rw [← cancel_mono e.hom]
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    simp only [e, Iso.trans_hom, Scheme.topIso_hom,
      Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  have hVe : V.ι ≫ e.inv = X.homOfLE le_sup_right := by
    rw [← cancel_mono e.hom]
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    simp only [e, Iso.trans_hom, Scheme.topIso_hom,
      Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]
  have heι : e.inv ≫ (U ⊔ V).ι = 𝟙 X := by
    simp only [e, Iso.trans_inv, Category.assoc, Scheme.isoOfEq_inv_ι,
      Scheme.toIso_inv_ι]
  refine ⟨e.inv ≫ f, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hUe, hfU]
  · rw [← Category.assoc, hVe, hfV]
  · rw [Category.assoc, hf, ← Category.assoc, heι, Category.id_comp]

lemma opens_ι_appTop {C : Scheme.{u}} (U : C.Opens) :
    U.ι.appTop =
      CommRingCat.ofHom
        (U.topIso.inv.hom.comp
          (C.presheaf.map (homOfLE le_top).op).hom) := by
  apply CommRingCat.hom_ext
  rw [Scheme.Opens.ι_appTop]
  simp only [Scheme.Opens.topIso_inv]
  change (C.presheaf.map _).hom =
    (C.presheaf.map _ ≫ C.presheaf.map _).hom
  rw [← Functor.map_comp]
  congr 1

private theorem opens_toSpecΓ_comp_structureMap
    {C S : Scheme.{u}} (π : C ⟶ S) (U : C.Opens) :
    let A : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let τ : Γ(C, U) →+*
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      U.topIso.inv.hom
    let f := τ.comp A
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) =
      U.ι ≫ π ≫ S.toSpecΓ := by
  dsimp only
  symm
  calc
    U.ι ≫ π ≫ S.toSpecΓ =
        (U.ι ≫ π) ≫ S.toSpecΓ := (Category.assoc _ _ _).symm
    _ = U.toScheme.toSpecΓ ≫ Spec.map (U.ι ≫ π).appTop :=
      Scheme.toSpecΓ_naturality (U.ι ≫ π)
    _ = U.toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom
          (U.topIso.inv.hom.comp
            ((C.presheaf.map (homOfLE le_top).op).hom.comp
              π.appTop.hom))) := by
      congr 1
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      rw [Scheme.Hom.comp_appTop, opens_ι_appTop]
      rfl

/-- The Cartier-frame and away-frame pole maps glue over their common base. -/
theorem sectionPoleSheafPower_six_exists_projModelMap_on_cartier_away_union
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)))
    (hrel :
      sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y) +
          a₁ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (sectionPoleSheafPower_baseSectionsMul z hz 2 3 (x ⊗ₜ y)) +
          a₃ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3) y)) =
        sectionPoleSheafPower_baseSectionsMul z hz 2 4
            (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) +
          a₂ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) +
          a₄ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2) x))) +
          a₆ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2)
                          (Scheme.Modules.baseSectionsMap π
                            (sectionPoleSheafSuccHom π z hz 1)
                              (sectionPoleSheafPowerOneSection π z hz)))))) :
    let XU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 2) x
    let YU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 3) y
    let XV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 2)) x
    let YV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 3)) y
    let AU : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let AV : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let WC : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
      ⟨a₁, a₂, a₃, a₄, a₆⟩
    let τU : Γ(C, U.1) →+*
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom
    let τV : Γ(C, V) →+*
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      V.topIso.inv.hom
    let fU := τU.comp AU
    let fV := τV.comp AV
    let PU : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      τU ∘ ![XU * r, YU, r ^ 3]
    let PV : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      τV ∘ ![XV, YV, 1]
    let hPU : (WC.map fU).toProjective.Equation PU := by
      have hPU₀ :=
        sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_relation
          z hz U r hr hspan hnzd x y a₁ a₂ a₃ a₄ a₆ hrel
      simpa only [WC, fU, PU, WeierstrassCurve.map_map] using hPU₀.map τU
    let hPV : (WC.map fV).toProjective.Equation PV := by
      have hVeq :=
        sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
          z hz V hV x y a₁ a₂ a₃ a₄ a₆ hrel
      have hPV₀ : (WC.map AV).toProjective.Equation ![XV, YV, 1] := by
        rw [WeierstrassCurve.Projective.equation_some]
        simpa only [XV, YV, AV, WC] using hVeq
      simpa only [WC, fV, PV, WeierstrassCurve.map_map] using hPV₀.map τV
    ∀ hcop : IsCoprime (PU 1) (PU 2),
      ∃ f : (U.1 ⊔ V).toScheme ⟶ projModel WC,
        C.homOfLE le_sup_left ≫ f =
            projModelFromOfGlobalSectionsOfIsCoprime
              WC fU PU hPU 1 2 hcop ∧
          C.homOfLE le_sup_right ≫ f =
            projModelFromOfGlobalSections WC fV PV hPV 2
              (by
                simpa only [PV, Function.comp_apply,
                  WeierstrassCurve.Projective.fin3_def_ext, map_one] using
                  (isUnit_one :
                    IsUnit (1 :
                      Γ(V.toScheme, (⊤ : V.toScheme.Opens))))) ∧
          f ≫ projModelπ WC =
            (U.1 ⊔ V).ι ≫ π ≫ S.toSpecΓ := by
  dsimp only
  intro hcop
  let XU := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 2) x
  let YU := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 3) y
  let XV := overTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) V
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz 2) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV 2)) x
  let YV := overTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) V
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz 3) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV 3)) y
  let AU : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let AV : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
    (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
  let WC : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
    ⟨a₁, a₂, a₃, a₄, a₆⟩
  let τU : Γ(C, U.1) →+*
      Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom
  let τV : Γ(C, V) →+*
      Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    V.topIso.inv.hom
  let fU := τU.comp AU
  let fV := τV.comp AV
  let PU : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    τU ∘ ![XU * r, YU, r ^ 3]
  let PV : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
    τV ∘ ![XV, YV, 1]
  let hPU₀ :=
    sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_relation
      z hz U r hr hspan hnzd x y a₁ a₂ a₃ a₄ a₆ hrel
  let hPU : (WC.map fU).toProjective.Equation PU := by
    simpa only [WC, fU, PU, WeierstrassCurve.map_map] using hPU₀.map τU
  let hVeq :=
    sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
      z hz V hV x y a₁ a₂ a₃ a₄ a₆ hrel
  let hPV₀ : (WC.map AV).toProjective.Equation ![XV, YV, 1] := by
    rw [WeierstrassCurve.Projective.equation_some]
    simpa only [XV, YV, AV, WC] using hVeq
  let hPV : (WC.map fV).toProjective.Equation PV := by
    simpa only [WC, fV, PV, WeierstrassCurve.map_map] using hPV₀.map τV
  let hZ : IsUnit (PV 2) := by
    simpa only [PV, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext, map_one] using
      (isUnit_one :
        IsUnit (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))))
  have hUV :
      C.homOfLE (inf_le_left : U.1 ⊓ V ≤ U.1) ≫
          projModelFromOfGlobalSectionsOfIsCoprime
            WC fU PU hPU 1 2 hcop =
        C.homOfLE (inf_le_right : U.1 ⊓ V ≤ V) ≫
          projModelFromOfGlobalSections WC fV PV hPV 2 hZ := by
    simpa only [XU, YU, XV, YV, AU, AV, WC, τU, τV,
      fU, fV, PU, PV, hPU, hPV, hZ] using
      sectionPoleSheafPower_six_projModelMap_cartier_away_overlap
        z hz U r hr hspan hnzd V hV x y a₁ a₂ a₃ a₄ a₆ hrel hcop
  have hUbase :
      projModelFromOfGlobalSectionsOfIsCoprime
          WC fU PU hPU 1 2 hcop ≫ projModelπ WC =
        U.1.ι ≫ π ≫ S.toSpecΓ := by
    rw [projModelFromOfGlobalSectionsOfIsCoprime_projModelπ]
    exact opens_toSpecΓ_comp_structureMap π U.1
  have hVbase :
      projModelFromOfGlobalSections WC fV PV hPV 2 hZ ≫
          projModelπ WC =
        V.ι ≫ π ≫ S.toSpecΓ := by
    rw [projModelFromOfGlobalSections_projModelπ]
    exact opens_toSpecΓ_comp_structureMap π V
  exact exists_glue_on_sup_over U.1 V
    (projModelFromOfGlobalSectionsOfIsCoprime
      WC fU PU hPU 1 2 hcop)
    (projModelFromOfGlobalSections WC fV PV hPV 2 hZ)
    (projModelπ WC) (π ≫ S.toSpecΓ) hUV hUbase hVbase

/-- If the Cartier and away charts cover the source, their glued pole map is
an actual morphism from the whole curve to the projective Weierstrass model. -/
theorem sectionPoleSheafPower_six_exists_projModelMap_of_cartier_away_cover
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥) (hUV : U.1 ⊔ V = ⊤)
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)))
    (hrel :
      sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y) +
          a₁ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (sectionPoleSheafPower_baseSectionsMul z hz 2 3 (x ⊗ₜ y)) +
          a₃ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3) y)) =
        sectionPoleSheafPower_baseSectionsMul z hz 2 4
            (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)) +
          a₂ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) +
          a₄ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2) x))) +
          a₆ • Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz 5)
              (Scheme.Modules.baseSectionsMap π
                (sectionPoleSheafSuccHom π z hz 4)
                  (Scheme.Modules.baseSectionsMap π
                    (sectionPoleSheafSuccHom π z hz 3)
                      (Scheme.Modules.baseSectionsMap π
                        (sectionPoleSheafSuccHom π z hz 2)
                          (Scheme.Modules.baseSectionsMap π
                            (sectionPoleSheafSuccHom π z hz 1)
                              (sectionPoleSheafPowerOneSection π z hz)))))) :
    let XU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 2) x
    let YU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 3) y
    let XV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 2) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 2)) x
    let YV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz 3) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV 3)) y
    let AU : Γ(S, (⊤ : S.Opens)) →+* Γ(C, U.1) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let AV : Γ(S, (⊤ : S.Opens)) →+* Γ(C, V) :=
      (C.presheaf.map (homOfLE le_top).op).hom.comp π.appTop.hom
    let WC : WeierstrassCurve Γ(S, (⊤ : S.Opens)) :=
      ⟨a₁, a₂, a₃, a₄, a₆⟩
    let τU : Γ(C, U.1) →+*
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom
    let τV : Γ(C, V) →+*
        Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      V.topIso.inv.hom
    let fU := τU.comp AU
    let fV := τV.comp AV
    let PU : Fin 3 → Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      τU ∘ ![XU * r, YU, r ^ 3]
    let PV : Fin 3 → Γ(V.toScheme, (⊤ : V.toScheme.Opens)) :=
      τV ∘ ![XV, YV, 1]
    let hPU : (WC.map fU).toProjective.Equation PU := by
      have hPU₀ :=
        sectionPoleSheafPower_six_local_homogeneous_weierstrass_equation_of_relation
          z hz U r hr hspan hnzd x y a₁ a₂ a₃ a₄ a₆ hrel
      simpa only [WC, fU, PU, WeierstrassCurve.map_map] using hPU₀.map τU
    let hPV : (WC.map fV).toProjective.Equation PV := by
      have hVeq :=
        sectionPoleSheafPower_six_over_weierstrass_equation_of_preimage_eq_bot
          z hz V hV x y a₁ a₂ a₃ a₄ a₆ hrel
      have hPV₀ : (WC.map AV).toProjective.Equation ![XV, YV, 1] := by
        rw [WeierstrassCurve.Projective.equation_some]
        simpa only [XV, YV, AV, WC] using hVeq
      simpa only [WC, fV, PV, WeierstrassCurve.map_map] using hPV₀.map τV
    ∀ hcop : IsCoprime (PU 1) (PU 2),
      ∃ f : C ⟶ projModel WC,
        U.1.ι ≫ f =
            projModelFromOfGlobalSectionsOfIsCoprime
              WC fU PU hPU 1 2 hcop ∧
          V.ι ≫ f =
            projModelFromOfGlobalSections WC fV PV hPV 2
              (by
                simpa only [PV, Function.comp_apply,
                  WeierstrassCurve.Projective.fin3_def_ext, map_one] using
                  (isUnit_one :
                    IsUnit (1 :
                      Γ(V.toScheme, (⊤ : V.toScheme.Opens))))) ∧
          f ≫ projModelπ WC = π ≫ S.toSpecΓ := by
  dsimp only
  intro hcop
  obtain ⟨f, hfU, hfV, hf⟩ :=
    sectionPoleSheafPower_six_exists_projModelMap_on_cartier_away_union
      z hz U r hr hspan hnzd V hV x y a₁ a₂ a₃ a₄ a₆ hrel hcop
  exact exists_global_of_exists_on_sup U.1 V hUV _ _ f hfU hfV
    (projModelπ _) (π ≫ S.toSpecΓ) hf

end

end ModularCurves
