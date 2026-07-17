/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineSectionDoubling
import ModularCurves.EllipticCurve.AffineSectionSpecPoints
import ModularCurves.Moduli.SectionMarking

/-!
# `RING-DBL`: the scheme-level doubling identity (parts C/D/E)

**(STREAM-OMEGA 2026-07-17, CHARTER-O v10.316.)** The universal-domain proof of
`2 • affineSection p q = affineSection (dblX, dblY)` (KM's banked route,
`decomposition-km-integral.md` [RING-DBL]):

* **[C] the universal base**: the `a₆`-ELIMINATION trick — solving the Weierstrass
  equation for `a₆` presents the universal marked curve over the FREE polynomial ring
  `ℤ[a₁, a₂, a₃, a₄, p, q]` (a domain, no irreducibility argument needed), localized at
  `tangentDen · Δ` (so the tangent denominator AND ellipticity are units).
* **[D]** over that domain, `2 • affineSection` is fibrewise nonzero (the field
  criterion), hence has marked coordinates ([hArb-1/2] pipeline), which the generic
  (fraction-field) fibre pins to `dblX/dblY` by injectivity.
* **[E]** the identity transports to every ring along the classifying map
  (the Stage-D `modelBaseChangeIso` section transport).
-/

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory WeierstrassCurve MvPolynomial

/-! ### [C] the universal doubling base -/

/-- Variables: `0,1,2,3 ↦ a₁,a₂,a₃,a₄`, `4 ↦ p`, `5 ↦ q`. -/
abbrev DblBase₀ : Type := MvPolynomial (Fin 6) ℤ

/-- The `a₆`-elimination: the value of `a₆` making `(p, q)` a curve point. -/
def dblA₆ : DblBase₀ :=
  X 5 ^ 2 + X 0 * X 4 * X 5 + X 2 * X 5 - X 4 ^ 3 - X 1 * X 4 ^ 2 - X 3 * X 4

/-- The universal marked Weierstrass curve (with `a₆` solved out). -/
def dblW : WeierstrassCurve DblBase₀ :=
  ⟨X 0, X 1, X 2, X 3, dblA₆⟩

/-- The tautological marked point lies on the curve. -/
theorem dblW_equation : dblW.toAffine.Equation (X 4) (X 5) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  show (X 5 : DblBase₀) ^ 2 + X 0 * X 4 * X 5 + X 2 * X 5
    = X 4 ^ 3 + X 1 * X 4 ^ 2 + X 3 * X 4 + dblA₆
  rw [dblA₆]
  ring

/-- The universal localization element: tangent denominator times discriminant. -/
def dblLoc : DblBase₀ := dblW.tangentDen (X 4) (X 5) * dblW.Δ

/-- The universal doubling base: localize away from `tangentDen · Δ`. -/
abbrev DblRing₀ : Type := Localization.Away dblLoc

/-- The universal doubling curve (level 0). -/
def dblWu₀ : WeierstrassCurve DblRing₀ :=
  dblW.map (algebraMap DblBase₀ DblRing₀)

/-- The localization element is nonzero (evaluate at
`a₁ = a₂ = a₄ = 0, a₃ = 1, p = 0, q = 0`: `tangentDen = 1`, `Δ = -27`). -/
theorem dblLoc_ne_zero : dblLoc ≠ 0 := by
  intro hc
  have h := congrArg (MvPolynomial.eval
    (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)) hc
  rw [map_zero] at h
  rw [dblLoc, map_mul] at h
  have h1 : MvPolynomial.eval (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)
      (dblW.tangentDen (X 4) (X 5)) = 1 := by
    simp [tangentDen, dblW]
  have h2 : MvPolynomial.eval (fun i : Fin 6 => if i = 2 then (1 : ℤ) else 0)
      dblW.Δ = -27 := by
    simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, dblW, dblA₆]
  rw [h1, h2] at h
  norm_num at h

instance : IsDomain DblRing₀ :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors dblLoc_ne_zero)

/-! ### the universe-`u` layer (`ULift`, the `ZInvThree` pattern) -/

/-- The universal doubling base in universe `u`. -/
abbrev DblRing : Type u := ULift.{u} DblRing₀

instance : IsDomain DblRing.{u} :=
  Function.Injective.isDomain
    (ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀)
    (ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).injective

/-- The structure map from the polynomial base into the universe-`u` doubling ring. -/
noncomputable def dblι : DblBase₀ →+* DblRing.{u} :=
  ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).symm.toRingHom).comp
    (algebraMap DblBase₀ DblRing₀)

/-- The universal doubling curve in universe `u`. -/
noncomputable def dblWu : WeierstrassCurve DblRing.{u} :=
  dblW.map dblι

/-- The image of the localization element is a unit in the universe-`u` ring. -/
theorem isUnit_dblι_dblLoc : IsUnit (dblι.{u} dblLoc) := by
  have h : IsUnit (algebraMap DblBase₀ DblRing₀ dblLoc) :=
    IsLocalization.Away.algebraMap_isUnit (S := DblRing₀) dblLoc
  exact h.map (ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).symm.toRingHom

/-- The tangent denominator of the universal marked point, as a `dblι`-image. -/
theorem dblWu_tangentDen_eq :
    dblWu.{u}.tangentDen (dblι (X 4)) (dblι (X 5))
      = dblι (dblW.tangentDen (X 4) (X 5)) := by
  simp only [WeierstrassCurve.tangentDen, dblWu, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₃, map_add, map_mul, map_ofNat]

/-- The tangent denominator is a unit in the universal doubling base. -/
theorem isUnit_dblD : IsUnit (dblWu.{u}.tangentDen (dblι (X 4)) (dblι (X 5))) := by
  rw [dblWu_tangentDen_eq]
  have h : IsUnit (dblι.{u} (dblW.tangentDen (X 4) (X 5) * dblW.Δ)) :=
    isUnit_dblι_dblLoc
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- The universal doubling curve is elliptic. -/
instance : dblWu.{u}.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  have h : IsUnit (dblι.{u} (dblW.tangentDen (X 4) (X 5) * dblW.Δ)) :=
    isUnit_dblι_dblLoc
  rw [map_mul] at h
  have hΔ : dblWu.{u}.Δ = dblι dblW.Δ := by
    rw [dblWu, WeierstrassCurve.map_Δ]
  rw [hΔ]
  exact isUnit_of_mul_isUnit_right h

/-! ### [D] the universal identity -/

/-- The universal marked abscissa/ordinate. -/
noncomputable def dblPu : DblRing.{u} := dblι (X 4)
noncomputable def dblQu : DblRing.{u} := dblι (X 5)

/-- The universal inverse of the tangent denominator: `Δ · (dΔ)⁻¹`. -/
noncomputable def dblEu : DblRing.{u} :=
  dblι dblW.Δ * (ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).symm
    (IsLocalization.Away.invSelf (S := DblRing₀) dblLoc)

theorem dblEu_spec : dblWu.{u}.tangentDen dblPu dblQu * dblEu = 1 := by
  show dblWu.{u}.tangentDen (dblι (X 4)) (dblι (X 5)) * dblEu = 1
  rw [dblWu_tangentDen_eq, dblEu, dblι]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← mul_assoc, ← map_mul, ← map_mul, ← map_mul]
  rw [show dblW.tangentDen (X 4) (X 5) * dblW.Δ = dblLoc from rfl]
  rw [IsLocalization.Away.mul_invSelf (S := DblRing₀) dblLoc]
  exact map_one _

theorem dblWu_equation : dblWu.{u}.toAffine.Equation dblPu dblQu :=
  WeierstrassCurve.Affine.Equation.map dblι dblW_equation

/-- The universal doubling coordinates satisfy the Weierstrass equation (checked at the
generic fibre and pulled back by injectivity). -/
theorem dblWu_equation_dbl : dblWu.{u}.toAffine.Equation
    (dblWu.dblX dblPu dblQu dblEu) (dblWu.dblY dblPu dblQu dblEu) := by
  set K := FractionRing DblRing.{u}
  letI : DecidableEq K := Classical.decEq K
  have hinj := IsFractionRing.injective DblRing.{u} K
  set φ := algebraMap DblRing.{u} K
  haveI : ((dblWu.{u}.map φ)).IsElliptic := inferInstance
  have hK : (dblWu.{u}.map φ).toAffine.Equation (φ dblPu) (φ dblQu) :=
    WeierstrassCurve.Affine.Equation.map φ dblWu_equation
  have heK : (dblWu.{u}.map φ).tangentDen (φ dblPu) (φ dblQu) * φ dblEu = 1 := by
    have h := congrArg φ dblEu_spec
    rw [map_mul, map_one] at h
    rw [show (dblWu.{u}.map φ).tangentDen (φ dblPu) (φ dblQu)
      = φ (dblWu.{u}.tangentDen dblPu dblQu) from by
        simp only [WeierstrassCurve.tangentDen, WeierstrassCurve.map_a₁,
          WeierstrassCurve.map_a₃, map_add, map_mul, map_ofNat]]
    exact h
  have hnsK : (dblWu.{u}.map φ).toAffine.Nonsingular (φ dblPu) (φ dblQu) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hK
  have hyne : φ dblQu ≠ (dblWu.{u}.map φ).toAffine.negY (φ dblPu) (φ dblQu) := by
    intro hc
    have hd0 : (dblWu.{u}.map φ).tangentDen (φ dblPu) (φ dblQu) = 0 := by
      rw [WeierstrassCurve.tangentDen]
      have := congrArg (fun z => φ dblQu - z) hc
      simp only [sub_self] at this
      rw [WeierstrassCurve.Affine.negY] at this
      linear_combination -this
    rw [hd0, zero_mul] at heK
    exact zero_ne_one heK
  have hne : ¬(φ dblPu = φ dblPu ∧ φ dblQu
      = (dblWu.{u}.map φ).toAffine.negY (φ dblPu) (φ dblQu)) := fun hc => hyne hc.2
  have hnsAdd := WeierstrassCurve.Affine.nonsingular_add hnsK hnsK hne
  have hXY : (dblWu.{u}.map φ).toAffine.Equation
      ((dblWu.{u}.map φ).dblX (φ dblPu) (φ dblQu) (φ dblEu))
      ((dblWu.{u}.map φ).dblY (φ dblPu) (φ dblQu) (φ dblEu)) := by
    have h1 := hnsAdd.1
    rwa [show (dblWu.{u}.map φ).toAffine.slope (φ dblPu) (φ dblPu) (φ dblQu) (φ dblQu)
        = (dblWu.{u}.map φ).dblSlope (φ dblPu) (φ dblQu) (φ dblEu) from
      WeierstrassCurve.slope_eq_dblSlope heK] at h1
  rw [WeierstrassCurve.map_dblX, WeierstrassCurve.map_dblY] at hXY
  rw [WeierstrassCurve.Affine.equation_iff] at hXY ⊢
  apply hinj
  simp only [map_add, map_mul, map_pow,
    show φ (dblWu.{u}.toAffine.a₁) = (dblWu.{u}.map φ).toAffine.a₁ from rfl,
    show φ (dblWu.{u}.toAffine.a₂) = (dblWu.{u}.map φ).toAffine.a₂ from rfl,
    show φ (dblWu.{u}.toAffine.a₃) = (dblWu.{u}.map φ).toAffine.a₃ from rfl,
    show φ (dblWu.{u}.toAffine.a₄) = (dblWu.{u}.map φ).toAffine.a₄ from rfl,
    show φ (dblWu.{u}.toAffine.a₆) = (dblWu.{u}.map φ).toAffine.a₆ from rfl]
  exact hXY

/-! ### [E] the additive section transport along a coefficient map -/

section Transport

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  (W : WeierstrassCurve A) [W.IsElliptic]

set_option backward.isDefEq.respectTransparency false in
/-- **([RING-DBL E] the section transport)** The additive map on model sections induced
by a coefficient ring map: pull along `Spec`, cast the base identity, invert the
base-change point equivalence, and push across the Stage-D pointed comparison. -/
noncomputable def sectionMapHom :
    letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
    (modelEllipticCurve W).Section →+
      (modelEllipticCurve (W.map (algebraMap A A'))).Section :=
  letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  ((EllipticCurve.pointAddEquiv (modelBaseChangeIso (A' := A') W)
      ((isMonHom_modelBaseChangeIso (A' := A') W).mul_hom)
      (𝟙 (Spec (CommRingCat.of A')))).toAddMonoidHom).comp
    (((EllipticCurve.Point.baseChangeEquiv (E := modelEllipticCurve W)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        (𝟙 (Spec (CommRingCat.of A')))).symm.toAddMonoidHom).comp
      (((EllipticCurve.Point.castBase (modelEllipticCurve W)
          (Category.id_comp (Spec.map (CommRingCat.ofHom
            (algebraMap A A')))).symm).toAddMonoidHom).comp
        (AddMonoidHom.mk' (EllipticCurve.Point.pull (modelEllipticCurve W)
            (Spec.map (CommRingCat.ofHom (algebraMap A A'))))
          (fun P Q => EllipticCurve.Point.pull_add (modelEllipticCurve W) _ P Q))))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([RING-DBL E] the transport value)** The section transport carries affine-point
sections to the affine-point sections of the mapped coordinates (the Stage-D matched
section, as a value of `sectionMapHom`). -/
theorem sectionMapHom_affineSection {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] (W : WeierstrassCurve A) [W.IsElliptic] (p q : A)
    (h : W.toAffine.Equation p q)
    (h' : (W.map (algebraMap A A')).toAffine.Equation (algebraMap A A' p)
      (algebraMap A A' q)) :
    letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
    sectionMapHom (A' := A') W ⟨projModelAffineSection W p q h,
        projModelAffineSection_projModelπ _ _ _ _⟩
      = ⟨projModelAffineSection (W.map (algebraMap A A')) (algebraMap A A' p)
          (algebraMap A A' q) h',
        projModelAffineSection_projModelπ _ _ _ _⟩ := by
  letI : (W.map (algebraMap A A')).IsElliptic := inferInstance
  refine Subtype.ext ?_
  show ((EllipticCurve.Point.asSection (modelEllipticCurve W)
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      (EllipticCurve.Point.pull (modelEllipticCurve W)
        (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        ⟨projModelAffineSection W p q h,
          projModelAffineSection_projModelπ _ _ _ _⟩)).1 ≫
      (modelBaseChangeIso (A' := A') W).hom.left) = _
  rw [modelBaseChangeIso_hom_left, Iso.comp_inv_eq]
  refine pullback.hom_ext ?_ ?_
  · refine ((EllipticCurve.Point.asSection_val_fst _ _ _).trans
      (projModelAffineSection_baseChange W p q h h').symm).trans ?_
    exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
      (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_fst.symm
  · refine ((EllipticCurve.Point.asSection_val_snd _ _ _).trans
      (projModelAffineSection_projModelπ _ _ _ h').symm).trans ?_
    exact congrArg (fun m => projModelAffineSection (W.map (algebraMap A A'))
        (algebraMap A A' p) (algebraMap A A' q) h' ≫ m)
      (isPullback_projModelBaseChange (R' := A') W).isoPullback_hom_snd.symm


end Transport


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- **([RING-DBL D] the universal identity ★★★)** Over the universal doubling base,
doubling the tautological marked section lands at the ring doubling coordinates. -/
theorem two_zsmul_affineSection_universal :
    (2 : ℤ) • (⟨projModelAffineSection dblWu.{u} dblPu.{u} dblQu.{u} dblWu_equation.{u},
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      (modelEllipticCurve dblWu.{u}).Section)
      = ⟨projModelAffineSection dblWu.{u} (dblWu.{u}.dblX dblPu.{u} dblQu.{u} dblEu.{u})
          (dblWu.{u}.dblY dblPu.{u} dblQu.{u} dblEu.{u}) dblWu_equation_dbl.{u},
        projModelAffineSection_projModelπ _ _ _ _⟩ := by
  classical
  set σu : (modelEllipticCurve dblWu).Section :=
    ⟨projModelAffineSection dblWu dblPu dblQu dblWu_equation,
      projModelAffineSection_projModelπ _ _ _ _⟩ with hσu
  set τ : (modelEllipticCurve dblWu).Section := (2 : ℤ) • σu with hτ
  -- STEP 1: fibrewise nonvanishing of the double
  have hne : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (t : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of DblRing)),
      t ≫ τ.1 ≠ t ≫ (modelEllipticCurve dblWu).zero := by
    intro k _ _ t hc
    obtain ⟨ψ, rfl⟩ : ∃ ψ : CommRingCat.of DblRing ⟶ CommRingCat.of k,
        Spec.map ψ = t := ⟨Spec.preimage t, Spec.map_preimage t⟩
    letI : Algebra DblRing k := ψ.hom.toAlgebra
    letI : DecidableEq k := Classical.decEq k
    haveI : ((dblWu.baseChange k)).IsElliptic :=
      inferInstanceAs (((dblWu.map (algebraMap DblRing k))).IsElliptic)
    have hτ0 : EllipticCurve.Point.pull (modelEllipticCurve dblWu) (Spec.map ψ) τ
        = 0 :=
      Subtype.ext (hc.trans ((modelEllipticCurve dblWu).point_zero_val _).symm)
    rw [hτ, EllipticCurve.Point.pull_zsmul] at hτ0
    -- the dictionary value of the pulled marked section
    have hns : (dblWu.baseChange k).toAffine.Nonsingular
        (algebraMap DblRing k dblPu) (algebraMap DblRing k dblQu) :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        (WeierstrassCurve.Affine.Equation.map _ dblWu_equation)
    have hval : modelPointAddEquiv dblWu (K' := k)
        (EllipticCurve.Point.pull (modelEllipticCurve dblWu) (Spec.map ψ) σu)
        = WeierstrassCurve.Affine.Point.some _ _ hns := by
      have hxpkg : EllipticCurve.Point.pull (modelEllipticCurve dblWu)
          (Spec.map ψ) σu
          = ⟨(affineSectionSpecPoint dblWu k dblPu dblQu dblWu_equation).1,
            (affineSectionSpecPoint dblWu k dblPu dblQu dblWu_equation).2⟩ :=
        Subtype.ext rfl
      rw [hxpkg]
      show projModelPointsEquiv dblWu k
        (affineSectionSpecPoint dblWu k dblPu dblQu dblWu_equation) = _
      exact projModelPointsEquiv_affineSectionSpecPoint dblWu dblPu dblQu
        dblWu_equation hns
    have hek : (dblWu.baseChange k).tangentDen (algebraMap DblRing k dblPu)
        (algebraMap DblRing k dblQu) * algebraMap DblRing k dblEu = 1 := by
      have h := congrArg (algebraMap DblRing k) dblEu_spec
      rw [map_mul, map_one] at h
      rw [show (dblWu.baseChange k).tangentDen (algebraMap DblRing k dblPu)
          (algebraMap DblRing k dblQu)
          = algebraMap DblRing k (dblWu.tangentDen dblPu dblQu) from by
        simp only [WeierstrassCurve.tangentDen, WeierstrassCurve.map_a₁,
          WeierstrassCurve.map_a₃, map_add, map_mul, map_ofNat]
        rfl]
      exact h
    have h2 : (2 : ℤ) • (WeierstrassCurve.Affine.Point.some _ _ hns :
        (dblWu.baseChange k).toAffine.Point) = 0 := by
      rw [← hval, ← map_zsmul, hτ0, map_zero]
    exact WeierstrassCurve.two_zsmul_some_ne_zero hns hek h2
  -- STEP 2: the double factors through the Z-chart with coordinates
  have hπτ : τ.1 ≫ projModelπ dblWu = 𝟙 _ := τ.2
  haveI : IsProper (modelEllipticCurve dblWu).π := (modelEllipticCurve dblWu).proper
  have havoid : ∀ w : ↥(Spec (CommRingCat.of DblRing)),
      τ.1.base w ∉ Set.range (modelEllipticCurve dblWu).zero.base :=
    fun w => LocalPresentation.forall_not_mem_range_of_pull_ne
      τ.1 (modelEllipticCurve dblWu).zero hπτ
      (modelEllipticCurve dblWu).zero_π hne w
  have hrange : Set.range (τ.1).base ⊆
      Set.range (Proj.awayι (HomogeneousIdeal.quotientGrading (projIdeal dblWu))
        ((HomogeneousIdeal.quotientGradingHom (projIdeal dblWu)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one dblWu 2) one_pos).base := by
    rw [show Set.range (Proj.awayι (HomogeneousIdeal.quotientGrading (projIdeal dblWu))
        ((HomogeneousIdeal.quotientGradingHom (projIdeal dblWu)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one dblWu 2) one_pos).base
        = (Proj.basicOpen (HomogeneousIdeal.quotientGrading (projIdeal dblWu))
            ((HomogeneousIdeal.quotientGradingHom (projIdeal dblWu))
              (MvPolynomial.X 2)) :
          Set (Proj (HomogeneousIdeal.quotientGrading (projIdeal dblWu)))) from by
      rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι]]
    rintro _ ⟨x, rfl⟩
    by_contra hmem
    exact havoid x (mem_range_zero_of_not_mem_zChart hmem)
  obtain ⟨p', q', heq', hτeq⟩ := eq_affineSection_of_zChart_factor dblWu
    τ.1 hπτ (IsOpenImmersion.lift _ _ hrange)
    (IsOpenImmersion.lift_fac _ _ hrange)
  -- STEP 3: pin the coordinates at the generic fibre
  set K := FractionRing DblRing
  letI : DecidableEq K := Classical.decEq K
  have hinj := IsFractionRing.injective DblRing K
  haveI : ((dblWu.baseChange K)).IsElliptic :=
    inferInstanceAs (((dblWu.map (algebraMap DblRing K))).IsElliptic)
  set tF : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of DblRing) :=
    Spec.map (CommRingCat.ofHom (algebraMap DblRing K)) with htF
  have hnsF : (dblWu.baseChange K).toAffine.Nonsingular
      (algebraMap DblRing K dblPu) (algebraMap DblRing K dblQu) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ dblWu_equation)
  have hnsF' : (dblWu.baseChange K).toAffine.Nonsingular
      (algebraMap DblRing K (dblWu.dblX dblPu dblQu dblEu))
      (algebraMap DblRing K (dblWu.dblY dblPu dblQu dblEu)) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ dblWu_equation_dbl)
  have hnsP' : (dblWu.baseChange K).toAffine.Nonsingular
      (algebraMap DblRing K p') (algebraMap DblRing K q') :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heq')
  have heF : (dblWu.baseChange K).tangentDen (algebraMap DblRing K dblPu)
      (algebraMap DblRing K dblQu) * algebraMap DblRing K dblEu = 1 := by
    have h := congrArg (algebraMap DblRing K) dblEu_spec
    rw [map_mul, map_one] at h
    rw [show (dblWu.baseChange K).tangentDen (algebraMap DblRing K dblPu)
        (algebraMap DblRing K dblQu)
        = algebraMap DblRing K (dblWu.tangentDen dblPu dblQu) from by
      simp only [WeierstrassCurve.tangentDen, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃, map_add, map_mul, map_ofNat]
      rfl]
    exact h
  -- (a) the pulled double is the doubled dictionary value
  have hvalσ : modelPointAddEquiv dblWu (K' := K)
      (EllipticCurve.Point.pull (modelEllipticCurve dblWu) tF σu)
      = WeierstrassCurve.Affine.Point.some _ _ hnsF := by
    have hxpkg : EllipticCurve.Point.pull (modelEllipticCurve dblWu) tF σu
        = ⟨(affineSectionSpecPoint dblWu K dblPu dblQu dblWu_equation).1,
          (affineSectionSpecPoint dblWu K dblPu dblQu dblWu_equation).2⟩ :=
      Subtype.ext rfl
    rw [hxpkg]
    show projModelPointsEquiv dblWu K
      (affineSectionSpecPoint dblWu K dblPu dblQu dblWu_equation) = _
    exact projModelPointsEquiv_affineSectionSpecPoint dblWu dblPu dblQu
      dblWu_equation hnsF
  have hvalτa : modelPointAddEquiv dblWu (K' := K)
      (EllipticCurve.Point.pull (modelEllipticCurve dblWu) tF τ)
      = WeierstrassCurve.Affine.Point.some _ _ hnsF' := by
    rw [hτ, EllipticCurve.Point.pull_zsmul, map_zsmul, hvalσ]
    have h2 := WeierstrassCurve.two_zsmul_some_eq_dbl (W' := dblWu.baseChange K)
      hnsF heF (by
        have h := hnsF'
        rw [show (dblWu.baseChange K).dblX (algebraMap DblRing K dblPu)
            (algebraMap DblRing K dblQu) (algebraMap DblRing K dblEu)
            = algebraMap DblRing K (dblWu.dblX dblPu dblQu dblEu) from
          WeierstrassCurve.map_dblX dblWu (algebraMap DblRing K) dblPu dblQu dblEu,
          show (dblWu.baseChange K).dblY (algebraMap DblRing K dblPu)
            (algebraMap DblRing K dblQu) (algebraMap DblRing K dblEu)
            = algebraMap DblRing K (dblWu.dblY dblPu dblQu dblEu) from
          WeierstrassCurve.map_dblY dblWu (algebraMap DblRing K) dblPu dblQu dblEu]
        exact h)
    rw [h2]
    congr 1
    · exact WeierstrassCurve.map_dblX dblWu (algebraMap DblRing K) dblPu dblQu dblEu
    · exact WeierstrassCurve.map_dblY dblWu (algebraMap DblRing K) dblPu dblQu dblEu
  -- (b) the pulled double is the pulled coordinate section
  have hvalτb : modelPointAddEquiv dblWu (K' := K)
      (EllipticCurve.Point.pull (modelEllipticCurve dblWu) tF τ)
      = WeierstrassCurve.Affine.Point.some _ _ hnsP' := by
    have hτsec : τ = (⟨projModelAffineSection dblWu p' q' heq',
        projModelAffineSection_projModelπ _ _ _ _⟩ :
      (modelEllipticCurve dblWu).Section) := Subtype.ext hτeq
    rw [hτsec]
    have hxpkg : EllipticCurve.Point.pull (modelEllipticCurve dblWu) tF
        (⟨projModelAffineSection dblWu p' q' heq',
          projModelAffineSection_projModelπ _ _ _ _⟩ :
        (modelEllipticCurve dblWu).Section)
        = ⟨(affineSectionSpecPoint dblWu K p' q' heq').1,
          (affineSectionSpecPoint dblWu K p' q' heq').2⟩ :=
      Subtype.ext rfl
    rw [hxpkg]
    show projModelPointsEquiv dblWu K
      (affineSectionSpecPoint dblWu K p' q' heq') = _
    exact projModelPointsEquiv_affineSectionSpecPoint dblWu p' q' heq' hnsP'
  -- combine: the coordinates agree
  have hsome := hvalτa.symm.trans hvalτb
  have hp' : p' = dblWu.dblX dblPu dblQu dblEu := by
    injection hsome with h1 h2
    exact (hinj h1).symm
  have hq' : q' = dblWu.dblY dblPu dblQu dblEu := by
    injection hsome with h1 h2
    exact (hinj h2).symm
  -- STEP 4: assemble
  refine Subtype.ext ?_
  show τ.1 = _
  rw [hτeq]
  congr 1 <;> first
    | exact hp'
    | exact hq'


end ModularCurves
