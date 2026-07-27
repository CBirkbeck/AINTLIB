/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue

/-!
# Pointedness of the pole-sheaf Weierstrass comparison

The normalized Cartier coordinates restrict to `[0, 1, 0]` along the marked
section. Consequently, the local comparison morphism carries the marked
section to the point at infinity of the projective Weierstrass model.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

private lemma topIso_inv_comp_resLE_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) :
    U.topIso.inv ≫ (f.resLE U V e).appTop =
      f.appLE U V e ≫ V.topIso.inv := by
  have hw :
      U.topIso.hom ≫ f.appLE U V e =
        (f.resLE U V e).appTop ≫ V.topIso.hom := by
    exact (arrowResLEAppIso f U V e).hom.w
  apply (cancel_mono V.topIso.hom).1
  rw [Category.assoc, ← hw, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private lemma top_open_topIso_inv {S : Scheme.{u}} :
    (⊤ : S.Opens).topIso.inv = S.topIso.hom.appTop := by
  rfl

private lemma top_open_topIso_inv_comp_scheme_topIso_inv_appTop
    {S : Scheme.{u}} :
    (⊤ : S.Opens).topIso.inv ≫ S.topIso.inv.appTop = 𝟙 _ := by
  rw [top_open_topIso_inv, ← Scheme.Hom.comp_appTop]
  simp

private lemma sectionFactor_appTop_topIso_inv
    {C S : Scheme.{u}} (z : S ⟶ C)
    (U : C.Opens) (hU : z ⁻¹ᵁ U = ⊤) (a : Γ(C, U)) :
    let zU : S ⟶ U.toScheme :=
      S.topIso.inv ≫ z.resLE U ⊤ (le_of_eq hU.symm)
    zU.appTop.hom (U.topIso.inv.hom a) =
      S.presheaf.map (eqToHom hU.symm).op (z.app U a) := by
  dsimp only
  rw [Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply,
    ← Category.assoc, topIso_inv_comp_resLE_appTop]
  rw [Category.assoc,
    top_open_topIso_inv_comp_scheme_topIso_inv_appTop,
    Category.comp_id]
  rfl

private lemma sectionFactor_appTop_comp_structureMap
    {C S : Scheme.{u}} (π : C ⟶ S) (z : S ⟶ C)
    (hz : z ≫ π = 𝟙 S) (U : C.Opens)
    (hU : z ⁻¹ᵁ U = ⊤) :
    let zU : S ⟶ U.toScheme :=
      S.topIso.inv ≫ z.resLE U ⊤ (le_of_eq hU.symm)
    let f : Γ(S, (⊤ : S.Opens)) →+*
        Γ(U.toScheme, (⊤ : U.toScheme.Opens)) :=
      U.topIso.inv.hom.comp
        ((C.presheaf.map (homOfLE le_top).op).hom.comp
          π.appTop.hom)
    zU.appTop.hom.comp f = RingHom.id _ := by
  dsimp only
  let zU : S ⟶ U.toScheme :=
    S.topIso.inv ≫ z.resLE U ⊤ (le_of_eq hU.symm)
  have hzUι : zU ≫ U.ι = z := by
    dsimp only [zU]
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Scheme.topIso_hom, ← Category.assoc,
      S.topIso.inv_hom_id, Category.id_comp]
  have hcomp : zU ≫ U.ι ≫ π = 𝟙 S := by
    change (zU ≫ U.ι) ≫ π = 𝟙 S
    rw [hzUι, hz]
  have happ := congrArg Scheme.Hom.appTop hcomp
  change zU.appTop.hom.comp
    (U.topIso.inv.hom.comp
      ((C.presheaf.map (homOfLE le_top).op).hom.comp
        π.appTop.hom)) = RingHom.id _
  apply RingHom.ext
  intro a
  have ha := ConcreteCategory.congr_hom happ a
  simp only [Scheme.Hom.comp_appTop, opens_ι_appTop] at ha
  change zU.appTop.hom
    (U.topIso.inv.hom
      ((C.presheaf.map (homOfLE le_top).op).hom
        (π.appTop.hom a))) = a at ha
  exact ha

/-- The normalized Cartier comparison morphism sends the marked section to
the point at infinity of the projective Weierstrass model. -/
theorem sectionPoleSheafPower_six_projModelMap_on_CartierChart_pointed
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens))) :
    let hr : r ∈ z.ker.ideal U :=
      hspan ▸ Ideal.subset_span (Set.mem_singleton r)
    let X := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 2) x
    let Y := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 3) y
    let f : Γ(S, (⊤ : S.Opens)) →+*
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom.comp
        ((C.presheaf.map (homOfLE le_top).op).hom.comp
          π.appTop.hom)
    let P : Fin 3 → Γ(U.1.toScheme,
        (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom ∘ ![X * r, Y, r ^ 3]
    ∀ (hP : (W.map f).toProjective.Equation P)
      (hcop : IsCoprime (P 1) (P 2)),
      let zU : S ⟶ U.1.toScheme :=
        S.topIso.inv ≫ z.resLE U.1 ⊤ (le_of_eq hU.symm)
      zU ≫
          projModelFromOfGlobalSectionsOfIsCoprime
            W f P hP 1 2 hcop =
        S.toSpecΓ ≫ projModelZero W := by
  dsimp only
  intro hP hcop
  let hr : r ∈ z.ker.ideal U :=
    hspan ▸ Ideal.subset_span (Set.mem_singleton r)
  let X := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 2) x
  let Y := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 3) y
  let f : Γ(S, (⊤ : S.Opens)) →+*
      Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom.comp
      ((C.presheaf.map (homOfLE le_top).op).hom.comp
        π.appTop.hom)
  let P : Fin 3 → Γ(U.1.toScheme,
      (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom ∘ ![X * r, Y, r ^ 3]
  let zU : S ⟶ U.1.toScheme :=
    S.topIso.inv ≫ z.resLE U.1 ⊤ (le_of_eq hU.symm)
  change (W.map f).toProjective.Equation P at hP
  change IsCoprime (P 1) (P 2) at hcop
  change zU ≫
      projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP 1 2 hcop =
    S.toSpecΓ ≫ projModelZero W
  have hf :
      zU.appTop.hom.comp f =
        RingHom.id Γ(S, (⊤ : S.Opens)) := by
    simpa only [zU, f] using
      sectionFactor_appTop_comp_structureMap π z hz U.1 hU
  letI : IsClosedImmersion z := isClosedImmersion_section z hz
  letI : QuasiCompact z := inferInstance
  have hr0 : z.app U.1 r = 0 := by
    rw [← RingHom.mem_ker, ← Scheme.Hom.ker_apply z U]
    exact hr
  have hY : z.app U.1 Y = 1 := by
    simpa only [Y, hr] using
      sectionPoleSheafPower_succ_app_coefficient_eq_one
        hsm z hz U hU r hspan hnzd 2 y hy
  have hPpull :
      zU.appTop.hom ∘ P =
        (![0, 1, 0] : Fin 3 → Γ(S, (⊤ : S.Opens))) := by
    funext i
    fin_cases i
    · change zU.appTop.hom
        (U.1.topIso.inv.hom (X * r)) = 0
      rw [sectionFactor_appTop_topIso_inv z U.1 hU (X * r)]
      simp only [map_mul, hr0, mul_zero, map_zero]
    · change zU.appTop.hom
        (U.1.topIso.inv.hom Y) = 1
      rw [sectionFactor_appTop_topIso_inv z U.1 hU Y,
        hY, map_one]
    · change zU.appTop.hom
        (U.1.topIso.inv.hom (r ^ 3)) = 0
      rw [sectionFactor_appTop_topIso_inv z U.1 hU (r ^ 3)]
      simp only [map_pow, hr0]
      norm_num
  have hcopPull := hcop.map zU.appTop.hom
  have hcop0 :
      IsCoprime
        ((![0, 1, 0] : Fin 3 → Γ(S, (⊤ : S.Opens))) 1)
        ((![0, 1, 0] : Fin 3 → Γ(S, (⊤ : S.Opens))) 2) := by
    change IsCoprime
      ((zU.appTop.hom ∘ P) 1)
      ((zU.appTop.hom ∘ P) 2) at hcopPull
    rw [hPpull] at hcopPull
    exact hcopPull
  have hnat :=
    projModelFromOfGlobalSectionsOfIsCoprime_naturality
      zU W f P hP 1 2 hcop
  have hnat' :
      zU ≫
          projModelFromOfGlobalSectionsOfIsCoprime
            W f P hP 1 2 hcop =
        projModelFromOfGlobalSectionsOfIsCoprime
          W (RingHom.id _) ![0, 1, 0]
          (WeierstrassCurve.Projective.equation_zero_one_zero
            W (RingHom.id _))
          1 2 hcop0 := by
    simpa only [hf, hPpull] using hnat
  rw [hnat']
  have hone :
      IsUnit
        ((![0, 1, 0] : Fin 3 → Γ(S, (⊤ : S.Opens))) 1) := by
    simp only [WeierstrassCurve.Projective.fin3_def_ext]
    exact isUnit_one
  rw [projModelFromOfGlobalSectionsOfIsCoprime_eq_of_isUnit
    W (RingHom.id _) ![0, 1, 0]
    (WeierstrassCurve.Projective.equation_zero_one_zero
      W (RingHom.id _))
    1 2 1 hcop0 hone]
  exact projModelFromOfGlobalSections_zero_one_zero W

/-- A global comparison morphism is pointed as soon as its restriction to the
Cartier chart is the normalized local comparison morphism. -/
theorem sectionPoleSheafPower_six_projModelMap_pointed_of_restrict
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (W : WeierstrassCurve Γ(S, (⊤ : S.Opens)))
    (F : C ⟶ projModel W) :
    let hr : r ∈ z.ker.ideal U :=
      hspan ▸ Ideal.subset_span (Set.mem_singleton r)
    let X := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 2) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 2) x
    let Y := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz 3) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd 3) y
    let f : Γ(S, (⊤ : S.Opens)) →+*
        Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom.comp
        ((C.presheaf.map (homOfLE le_top).op).hom.comp
          π.appTop.hom)
    let P : Fin 3 → Γ(U.1.toScheme,
        (⊤ : U.1.toScheme.Opens)) :=
      U.1.topIso.inv.hom ∘ ![X * r, Y, r ^ 3]
    ∀ (hP : (W.map f).toProjective.Equation P)
      (hcop : IsCoprime (P 1) (P 2)),
      U.1.ι ≫ F =
          projModelFromOfGlobalSectionsOfIsCoprime
            W f P hP 1 2 hcop →
        z ≫ F = S.toSpecΓ ≫ projModelZero W := by
  dsimp only
  intro hP hcop hF
  let hr : r ∈ z.ker.ideal U :=
    hspan ▸ Ideal.subset_span (Set.mem_singleton r)
  let X := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 2) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 2) x
  let Y := localTrivializationCoefficient
    (sectionPoleSheafPower π z hz 3) U
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd 3) y
  let f : Γ(S, (⊤ : S.Opens)) →+*
      Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom.comp
      ((C.presheaf.map (homOfLE le_top).op).hom.comp
        π.appTop.hom)
  let P : Fin 3 → Γ(U.1.toScheme,
      (⊤ : U.1.toScheme.Opens)) :=
    U.1.topIso.inv.hom ∘ ![X * r, Y, r ^ 3]
  let zU : S ⟶ U.1.toScheme :=
    S.topIso.inv ≫ z.resLE U.1 ⊤ (le_of_eq hU.symm)
  change (W.map f).toProjective.Equation P at hP
  change IsCoprime (P 1) (P 2) at hcop
  change U.1.ι ≫ F =
    projModelFromOfGlobalSectionsOfIsCoprime
      W f P hP 1 2 hcop at hF
  have hlocal :=
    sectionPoleSheafPower_six_projModelMap_on_CartierChart_pointed
      hsm z hz U hU r hspan hnzd x y hy W hP hcop
  change zU ≫
      projModelFromOfGlobalSectionsOfIsCoprime
        W f P hP 1 2 hcop =
    S.toSpecΓ ≫ projModelZero W at hlocal
  have hzUι : zU ≫ U.1.ι = z := by
    dsimp only [zU]
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Scheme.topIso_hom, ← Category.assoc,
      S.topIso.inv_hom_id, Category.id_comp]
  calc
    z ≫ F = (zU ≫ U.1.ι) ≫ F := by rw [hzUι]
    _ = zU ≫ U.1.ι ≫ F := Category.assoc _ _ _
    _ = zU ≫
        projModelFromOfGlobalSectionsOfIsCoprime
          W f P hP 1 2 hcop := by rw [hF]
    _ = S.toSpecΓ ≫ projModelZero W := hlocal

end

end ModularCurves
