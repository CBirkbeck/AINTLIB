/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafWeierstrassAway
import ModularCurves.EllipticCurve.PoleSheafWeierstrassChart
import ModularCurves.EllipticCurve.PoleSheafWeierstrassOverlap
import ModularCurves.EllipticCurve.WeierstrassModelCoordinateTransition
import ModularCurves.ForMathlib.ProjFromGlobalSectionsMap
import ModularCurves.Picard.InvertibleSheafFiniteStageModel

/-!
# Weierstrass comparison maps on Cartier/away overlaps

The local pole coordinates from a Cartier frame and the canonical frame away
from the marked section are compared after restriction to their overlap.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

open HomogeneousIdeal

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

private lemma projModelEval_comp
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : Y ⟶ X) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (hP' : (W.map (g.appTop.hom.comp f)).toProjective.Equation
      (g.appTop.hom ∘ P)) :
    g.appTop.hom.comp (projModelEval W f P hP) =
      projModelEval W (g.appTop.hom.comp f) (g.appTop.hom ∘ P)
        hP' := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply]
    rw [projModelEval_mk, projModelEval_mk]
    simp only [MvPolynomial.eval₂_C, RingHom.comp_apply]
  · intro i
    simp only [RingHom.comp_apply]
    rw [projModelEval_mk, projModelEval_mk]
    simp only [MvPolynomial.eval₂_X, Function.comp_apply]

theorem projModelFromOfGlobalSectionsOfIsCoprime_naturality
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : Y ⟶ X) (W : WeierstrassCurve R)
    (f : R →+* Γ(X, (⊤ : X.Opens)))
    (P : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map f).toProjective.Equation P)
    (i j : Fin 3) (hij : IsCoprime (P i) (P j)) :
    let P' : Fin 3 → Γ(Y, (⊤ : Y.Opens)) := g.appTop.hom ∘ P
    let hP' : (W.map (g.appTop.hom.comp f)).toProjective.Equation P' := by
      simpa only [WeierstrassCurve.map_map] using hP.map g.appTop.hom
    g ≫ projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij =
      projModelFromOfGlobalSectionsOfIsCoprime W
        (g.appTop.hom.comp f) P' hP' i j
        (hij.map g.appTop.hom) := by
  dsimp only
  let hP' :
      (W.map (g.appTop.hom.comp f)).toProjective.Equation
        (g.appTop.hom ∘ P) := by
    simpa only [WeierstrassCurve.map_map] using hP.map g.appTop.hom
  change g ≫
      projModelFromOfGlobalSectionsOfIsCoprime W f P hP i j hij =
    projModelFromOfGlobalSectionsOfIsCoprime W
      (g.appTop.hom.comp f) (g.appTop.hom ∘ P) hP' i j
      (hij.map g.appTop.hom)
  unfold projModelFromOfGlobalSectionsOfIsCoprime
  have heval := projModelEval_comp g W f P hP hP'
  have hcomp :
      (HomogeneousIdeal.irrelevant
        (quotientGrading (projIdeal W))).toIdeal.map
          (g.appTop.hom.comp (projModelEval W f P hP)) = ⊤ := by
    rw [heval]
    exact projModelEval_irrelevant_map_top_of_isCoprime W
      (g.appTop.hom.comp f) (g.appTop.hom ∘ P) hP'
      i j (hij.map g.appTop.hom)
  simpa only [heval] using
    Proj.fromOfGlobalSections_comp
      (𝒜 := quotientGrading (projIdeal W)) g
      (projModelEval W f P hP)
      (projModelEval_irrelevant_map_top_of_isCoprime W f P hP i j hij)
      hcomp

private lemma topIso_inv_restrict_apply
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U)
    (r : Γ(X, U)) :
    (X.homOfLE hVU).appTop.hom (U.topIso.inv.hom r) =
      V.topIso.inv.hom
        ((X.presheaf.map (homOfLE hVU).op).hom r) :=
  ConcreteCategory.congr_hom
    (Scheme.Modules.topIso_inv_naturality hVU) r

private lemma restrictRingHom_comp_top
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp
        (X.presheaf.map
          (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op).hom =
      (X.presheaf.map
        (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op).hom := by
  apply RingHom.ext
  intro r
  have hcomp := X.presheaf.map_comp
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op
    (homOfLE hVU).op
  have happ := ConcreteCategory.congr_hom hcomp r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at happ
  exact happ.symm.trans (ConcreteCategory.congr_hom
    (congrArg X.presheaf.map (Subsingleton.elim _ _)) r)

private theorem coprime_eq_unit_of_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    [Algebra R Γ(X, (⊤ : X.Opens))]
    (W : WeierstrassCurve R)
    (P P' : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (hP : (W.map
      (algebraMap R Γ(X, (⊤ : X.Opens)))).toProjective.Equation P)
    (hP' : (W.map
      (algebraMap R Γ(X, (⊤ : X.Opens)))).toProjective.Equation P')
    (i j k l : Fin 3) (hij : IsCoprime (P i) (P j))
    (hk : IsUnit (P' k)) (hl : IsUnit (P l))
    (e : Γ(X, (⊤ : X.Opens)))
    (hsmul : ∀ m, P m = e * P' m) :
    projModelFromOfGlobalSectionsOfIsCoprime W
        (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i j hij =
      projModelFromOfGlobalSections W
        (algebraMap R Γ(X, (⊤ : X.Opens))) P' hP' k hk := by
  rw [projModelFromOfGlobalSectionsOfIsCoprime_eq_of_isUnit
    W (algebraMap R Γ(X, (⊤ : X.Opens))) P hP i j l hij hl]
  exact projModelFromOfGlobalSections_congr_of_smul
    W k l P' P e hsmul hP' hP hk hl

private theorem restricted_coprime_eq_restricted_unit_of_smul
    {R : Type u} [CommRing R]
    {X Y Z : Scheme.{u}} (gX : Z ⟶ X) (gY : Z ⟶ Y)
    (W : WeierstrassCurve R)
    (fX : R →+* Γ(X, (⊤ : X.Opens)))
    (fY : R →+* Γ(Y, (⊤ : Y.Opens)))
    (PX : Fin 3 → Γ(X, (⊤ : X.Opens)))
    (PY : Fin 3 → Γ(Y, (⊤ : Y.Opens)))
    (hPX : (W.map fX).toProjective.Equation PX)
    (hPY : (W.map fY).toProjective.Equation PY)
    (i j k l : Fin 3) (hij : IsCoprime (PX i) (PX j))
    (hYk : IsUnit (PY k))
    (hXl : IsUnit (gX.appTop.hom (PX l)))
    (hf : gX.appTop.hom.comp fX = gY.appTop.hom.comp fY)
    (e : Γ(Z, (⊤ : Z.Opens)))
    (hsmul : ∀ m, gX.appTop.hom (PX m) =
      e * gY.appTop.hom (PY m)) :
    gX ≫ projModelFromOfGlobalSectionsOfIsCoprime
        W fX PX hPX i j hij =
      gY ≫ projModelFromOfGlobalSections W fY PY hPY k hYk := by
  let PX' : Fin 3 → Γ(Z, (⊤ : Z.Opens)) := gX.appTop.hom ∘ PX
  let PY' : Fin 3 → Γ(Z, (⊤ : Z.Opens)) := gY.appTop.hom ∘ PY
  let fZ : R →+* Γ(Z, (⊤ : Z.Opens)) := gY.appTop.hom.comp fY
  let hPX' : (W.map fZ).toProjective.Equation PX' := by
    change (W.map (gY.appTop.hom.comp fY)).toProjective.Equation
      (gX.appTop.hom ∘ PX)
    rw [← hf]
    simpa only [WeierstrassCurve.map_map] using hPX.map gX.appTop.hom
  let hPY' : (W.map fZ).toProjective.Equation PY' := by
    simpa only [PY', fZ, WeierstrassCurve.map_map] using hPY.map gY.appTop.hom
  have hleft :
      gX ≫ projModelFromOfGlobalSectionsOfIsCoprime
          W fX PX hPX i j hij =
        projModelFromOfGlobalSectionsOfIsCoprime W
          fZ PX' hPX' i j (hij.map gX.appTop.hom) := by
    simpa only [PX', fZ, hPX', hf] using
      projModelFromOfGlobalSectionsOfIsCoprime_naturality
        gX W fX PX hPX i j hij
  have hright :
      gY ≫ projModelFromOfGlobalSections W fY PY hPY k hYk =
        projModelFromOfGlobalSections W fZ PY' hPY' k
          (hYk.map gY.appTop.hom) := by
    simpa only [PY', fZ, hPY'] using
      projModelFromOfGlobalSections_naturality
        gY W fY PY hPY k hYk
  rw [hleft, hright]
  letI : Algebra R Γ(Z, (⊤ : Z.Opens)) := fZ.toAlgebra
  have hfZ : algebraMap R Γ(Z, (⊤ : Z.Opens)) = fZ :=
    RingHom.algebraMap_toAlgebra fZ
  let hPXalg :
      (W.map (algebraMap R Γ(Z, (⊤ : Z.Opens)))).toProjective.Equation PX' := by
    rwa [hfZ]
  let hPYalg :
      (W.map (algebraMap R Γ(Z, (⊤ : Z.Opens)))).toProjective.Equation PY' := by
    rwa [hfZ]
  change projModelFromOfGlobalSectionsOfIsCoprime W
      (algebraMap R Γ(Z, (⊤ : Z.Opens))) PX' hPXalg i j
        (hij.map gX.appTop.hom) =
    projModelFromOfGlobalSections W
      (algebraMap R Γ(Z, (⊤ : Z.Opens))) PY' hPYalg k
        (hYk.map gY.appTop.hom)
  exact coprime_eq_unit_of_smul
    W PX' PY' hPXalg hPYalg i j k l
      (hij.map gX.appTop.hom) (hYk.map gY.appTop.hom) hXl e
      (by simpa only [PX', PY', Function.comp_apply] using hsmul)

/-- Restricting a Cartier-frame pole coefficient to a Cartier/away overlap
gives the away-frame coefficient times the appropriate power of the Cartier
generator. -/
theorem sectionPoleSheafPower_cartier_away_overlap_restrict_coefficient
    {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (r : Γ(C, U.1)) (hr : r ∈ z.ker.ideal U)
    (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (V : C.Opens) (hV : z ⁻¹ᵁ V = ⊥)
    (n : ℕ)
    (m : Γ(sectionPoleSheafPower π z hz n, (⊤ : C.Opens))) :
    let W := U.1 ⊓ V
    let XU := localTrivializationCoefficient
      (sectionPoleSheafPower π z hz n) U
      (sectionPoleSheafPowerTrivializationOfCartierGenerator
        z hz U r hr hspan hnzd n) m
    let XV := overTrivializationCoefficient
      (sectionPoleSheafPower π z hz n) V
      (Scheme.Modules.overTrivializationOfRestrictIso
        (sectionPoleSheafPower π z hz n) V
        (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
          z hz V hV n)) m
    let resU : Γ(C, U.1) →+* Γ(C, W) :=
      (C.presheaf.map (homOfLE inf_le_left).op).hom
    let resV : Γ(C, V) →+* Γ(C, W) :=
      (C.presheaf.map (homOfLE inf_le_right).op).hom
    resU XU = resV XV * resU r ^ n := by
  dsimp only
  rw [← localTrivializationCoefficient_restrict
    (sectionPoleSheafPower π z hz n) U inf_le_left
    (sectionPoleSheafPowerTrivializationOfCartierGenerator
      z hz U r hr hspan hnzd n) m]
  rw [← overTrivializationCoefficient_restrict
    (sectionPoleSheafPower π z hz n) inf_le_right
    (Scheme.Modules.overTrivializationOfRestrictIso
      (sectionPoleSheafPower π z hz n) V
      (sectionPoleSheafPowerTrivializationOfSectionPreimageEqBot
        z hz V hV n)) m]
  simpa only [
    Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] using
      sectionPoleSheafPower_cartier_away_overlap_coefficient
        z hz U r hr hspan hnzd V hV n m

private theorem sectionPoleSheafPower_six_projModelMap_cartier_away_overlap_aux
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
    (a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens))) :
    let T := U.1 ⊓ V
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
    ∀ (hPU : (WC.map fU).toProjective.Equation PU)
      (hPV : (WC.map fV).toProjective.Equation PV)
      (hcop : IsCoprime (PU 1) (PU 2)),
      C.homOfLE (inf_le_left : T ≤ U.1) ≫
          projModelFromOfGlobalSectionsOfIsCoprime
            WC fU PU hPU 1 2 hcop =
        C.homOfLE (inf_le_right : T ≤ V) ≫
          projModelFromOfGlobalSections WC fV PV hPV 2
            (by
              simpa only [PV, Function.comp_apply,
                WeierstrassCurve.Projective.fin3_def_ext, map_one] using
                (isUnit_one :
                  IsUnit (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))))) := by
  dsimp only
  intro hPU hPV hcop
  let T := U.1 ⊓ V
  let gU : T.toScheme ⟶ U.1.toScheme := C.homOfLE inf_le_left
  let gV : T.toScheme ⟶ V.toScheme := C.homOfLE inf_le_right
  let resU : Γ(C, U.1) →+* Γ(C, T) :=
    (C.presheaf.map (homOfLE inf_le_left).op).hom
  let resV : Γ(C, V) →+* Γ(C, T) :=
    (C.presheaf.map (homOfLE inf_le_right).op).hom
  let τT : Γ(C, T) →+* Γ(T.toScheme, (⊤ : T.toScheme.Opens)) :=
    T.topIso.inv.hom
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
  let hZ : IsUnit (PV 2) := by
    simpa only [PV, Function.comp_apply,
      WeierstrassCurve.Projective.fin3_def_ext, map_one] using
      (isUnit_one :
        IsUnit (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))))
  have hrT : IsUnit (resU r) := by
    simpa only [T, resU] using
      sectionPoleSheaf_cartier_away_overlap_generator_isUnit
        z hz U r hr hspan hnzd V hV
  have hPUZ : IsUnit (gU.appTop.hom (PU 2)) := by
    change IsUnit (gU.appTop.hom (τU (r ^ 3)))
    rw [show gU = C.homOfLE (inf_le_left : T ≤ U.1) by rfl]
    rw [topIso_inv_restrict_apply]
    simpa only [τT, map_pow] using (hrT.pow 3).map τT
  have hf : gU.appTop.hom.comp fU = gV.appTop.hom.comp fV := by
    apply RingHom.ext
    intro a
    change gU.appTop.hom (τU (AU a)) =
      gV.appTop.hom (τV (AV a))
    rw [show gU = C.homOfLE (inf_le_left : T ≤ U.1) by rfl,
      show gV = C.homOfLE (inf_le_right : T ≤ V) by rfl]
    rw [topIso_inv_restrict_apply, topIso_inv_restrict_apply]
    apply congrArg τT
    change (resU.comp
        (C.presheaf.map
          (homOfLE (le_top : U.1 ≤ (⊤ : C.Opens))).op).hom)
          (π.appTop.hom a) =
      (resV.comp
        (C.presheaf.map
          (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op).hom)
          (π.appTop.hom a)
    rw [show resU.comp
          (C.presheaf.map
            (homOfLE (le_top : U.1 ≤ (⊤ : C.Opens))).op).hom =
        (C.presheaf.map
          (homOfLE (le_top : T ≤ (⊤ : C.Opens))).op).hom by
          simpa only [resU] using
            restrictRingHom_comp_top
              (X := C) (inf_le_left : T ≤ U.1)]
    rw [show resV.comp
          (C.presheaf.map
            (homOfLE (le_top : V ≤ (⊤ : C.Opens))).op).hom =
        (C.presheaf.map
          (homOfLE (le_top : T ≤ (⊤ : C.Opens))).op).hom by
          simpa only [resV] using
            restrictRingHom_comp_top
              (X := C) (inf_le_right : T ≤ V)]
  have hX : resU XU = resV XV * resU r ^ 2 := by
    simpa only [T, XU, XV, resU, resV] using
      sectionPoleSheafPower_cartier_away_overlap_restrict_coefficient
        z hz U r hr hspan hnzd V hV 2 x
  have hY : resU YU = resV YV * resU r ^ 3 := by
    simpa only [T, YU, YV, resU, resV] using
      sectionPoleSheafPower_cartier_away_overlap_restrict_coefficient
        z hz U r hr hspan hnzd V hV 3 y
  have hsmul (m : Fin 3) :
      gU.appTop.hom (PU m) =
        τT (resU r ^ 3) * gV.appTop.hom (PV m) := by
    fin_cases m
    · change gU.appTop.hom (τU (XU * r)) =
        τT (resU r ^ 3) * gV.appTop.hom (τV XV)
      rw [show gU = C.homOfLE (inf_le_left : T ≤ U.1) by rfl,
        show gV = C.homOfLE (inf_le_right : T ≤ V) by rfl]
      rw [topIso_inv_restrict_apply, topIso_inv_restrict_apply]
      change τT (resU (XU * r)) =
        τT (resU r ^ 3) * τT (resV XV)
      simp only [map_mul, map_pow, hX]
      ring
    · change gU.appTop.hom (τU YU) =
        τT (resU r ^ 3) * gV.appTop.hom (τV YV)
      rw [show gU = C.homOfLE (inf_le_left : T ≤ U.1) by rfl,
        show gV = C.homOfLE (inf_le_right : T ≤ V) by rfl]
      rw [topIso_inv_restrict_apply, topIso_inv_restrict_apply]
      change τT (resU YU) =
        τT (resU r ^ 3) * τT (resV YV)
      simp only [map_mul, map_pow, hY]
      ring
    · change gU.appTop.hom (τU (r ^ 3)) =
        τT (resU r ^ 3) * gV.appTop.hom (τV 1)
      rw [show gU = C.homOfLE (inf_le_left : T ≤ U.1) by rfl,
        show gV = C.homOfLE (inf_le_right : T ≤ V) by rfl]
      rw [topIso_inv_restrict_apply, topIso_inv_restrict_apply]
      change τT (resU (r ^ 3)) =
        τT (resU r ^ 3) * τT (resV 1)
      simp only [map_pow, map_one, mul_one]
  exact restricted_coprime_eq_restricted_unit_of_smul
    gU gV WC fU fV PU PV hPU hPV 1 2 2 2 hcop hZ hPUZ hf
      (τT (resU r ^ 3)) hsmul

/-- The projective morphisms defined by a fixed pole relation in a Cartier
frame and in the canonical frame away from the section agree on their
overlap. -/
theorem sectionPoleSheafPower_six_projModelMap_cartier_away_overlap
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
    let T := U.1 ⊓ V
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
      C.homOfLE (inf_le_left : T ≤ U.1) ≫
          projModelFromOfGlobalSectionsOfIsCoprime
            WC fU PU hPU 1 2 hcop =
        C.homOfLE (inf_le_right : T ≤ V) ≫
          projModelFromOfGlobalSections WC fV PV hPV 2
            (by
              simpa only [PV, Function.comp_apply,
                WeierstrassCurve.Projective.fin3_def_ext, map_one] using
                (isUnit_one :
                  IsUnit (1 : Γ(V.toScheme, (⊤ : V.toScheme.Opens))))) := by
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
  exact sectionPoleSheafPower_six_projModelMap_cartier_away_overlap_aux
    z hz U r hr hspan hnzd V hV x y a₁ a₂ a₃ a₄ a₆ hPU hPV hcop

end

end ModularCurves
