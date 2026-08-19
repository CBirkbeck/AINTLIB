/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineSectionDoublingIdentity
import ModularCurves.ForMathlib.NegModelAffineSection
import ModularCurves.Moduli.E3DatumAssembly

/-!
# The bridge assembly: `3•σ = 0 ⟹ hdbl` (the hArb close)

**(STREAM-OMEGA 2026-07-17, CHARTER-O v10.316, the finish.)** `RING-DBL` +
KM's negation coordinate + coordinate injectivity turn the section-level `3`-torsion of
a marked section into the cleared doubling condition `hdbl`, which fires KM's
certificate (`ThreeTorsionRingCertificate`) into the two `isE3Datum_of_bridges`
bridge-Props — closing `Bootstrap:95`.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory WeierstrassCurve MvPolynomial

/-- The doubling coordinates satisfy the Weierstrass equation (universal transport;
the classifier block of `two_zsmul_affineSection`, landed on the `Equation`). -/
theorem equation_dblXY {A' : Type u} [CommRing A'] (W : WeierstrassCurve A')
    [W.IsElliptic] (p q e : A') (h : W.toAffine.Equation p q)
    (he : W.tangentDen p q * e = 1) :
    W.toAffine.Equation (W.dblX p q e) (W.dblY p q e) := by
  classical
  set ψ₀ : DblBase₀ →+* A' := MvPolynomial.eval₂Hom (Int.castRingHom A')
    (fun i : Fin 6 => ![W.a₁, W.a₂, W.a₃, W.a₄, p, q] i) with hψ₀def
  have hψX : ∀ i : Fin 6, ψ₀ (X i) = ![W.a₁, W.a₂, W.a₃, W.a₄, p, q] i :=
    fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have hWmap : dblW.map ψ₀ = W := by
    ext
    · exact (hψX 0)
    · exact (hψX 1)
    · exact (hψX 2)
    · exact (hψX 3)
    · show ψ₀ dblA₆ = W.a₆
      rw [dblA₆]
      simp only [map_add, map_sub, map_mul, map_pow, hψX]
      show q ^ 2 + W.a₁ * p * q + W.a₃ * q - p ^ 3 - W.a₂ * p ^ 2 - W.a₄ * p = W.a₆
      have hEq := (WeierstrassCurve.Affine.equation_iff _ _).mp h
      linear_combination hEq
  have hdenIm : ψ₀ (dblW.tangentDen (X 4) (X 5)) = W.tangentDen p q := by
    simp only [WeierstrassCurve.tangentDen, dblW, map_add, map_mul, map_ofNat, hψX]
    rfl
  have hloc : IsUnit (ψ₀ dblLoc) := by
    rw [show (dblLoc : DblBase₀) = dblW.tangentDen (X 4) (X 5) * dblW.Δ from rfl,
      map_mul, hdenIm]
    refine IsUnit.mul (isUnit_iff_exists_inv.mpr ⟨e, he⟩) ?_
    rw [show ψ₀ dblW.Δ = (dblW.map ψ₀).Δ from (WeierstrassCurve.map_Δ _ _).symm,
      hWmap]
    exact (WeierstrassCurve.isElliptic_iff W).mp inferInstance
  set φ₀ : DblRing₀ →+* A' := IsLocalization.Away.lift dblLoc hloc with hφ₀def
  set φ : DblRing.{u} →+* A' :=
    φ₀.comp ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀) : DblRing.{u} →+* DblRing₀)
    with hφdef
  letI : Algebra DblRing.{u} A' := φ.toAlgebra
  have halg : ∀ z : DblRing.{u}, algebraMap DblRing.{u} A' z = φ z := fun _ => rfl
  have hcomp : ∀ z : DblBase₀, φ (dblι z) = ψ₀ z := by
    intro z
    show φ₀ ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀)
      ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).symm
        (algebraMap DblBase₀ DblRing₀ z))) = ψ₀ z
    rw [RingEquiv.apply_symm_apply]
    exact IsLocalization.Away.lift_eq dblLoc hloc z
  have hWeq : dblWu.{u}.map (algebraMap DblRing.{u} A') = W := by
    rw [show (algebraMap DblRing.{u} A') = φ from rfl, dblWu,
      WeierstrassCurve.map_map,
      show φ.comp dblι = ψ₀ from RingHom.ext hcomp]
    exact hWmap
  have hPim : algebraMap DblRing.{u} A' dblPu = p := by
    rw [halg, dblPu, hcomp, hψX]
    rfl
  have hQim : algebraMap DblRing.{u} A' dblQu = q := by
    rw [halg, dblQu, hcomp, hψX]
    rfl
  have hdIm : algebraMap DblRing.{u} A' (dblWu.{u}.tangentDen dblPu dblQu)
      = W.tangentDen p q := by
    rw [halg, show dblWu.{u}.tangentDen dblPu dblQu
      = dblι (dblW.tangentDen (X 4) (X 5)) from dblWu_tangentDen_eq, hcomp, hdenIm]
  have hEim : algebraMap DblRing.{u} A' dblEu = e := by
    have hd2 : W.tangentDen p q * algebraMap DblRing.{u} A' dblEu = 1 := by
      have hh := congrArg (algebraMap DblRing.{u} A') dblEu_spec
      rw [map_mul, map_one, hdIm] at hh
      exact hh
    have hu : IsUnit (W.tangentDen p q) := isUnit_iff_exists_inv.mpr ⟨e, he⟩
    exact hu.mul_left_cancel (hd2.trans he.symm)
  have hXim : algebraMap DblRing.{u} A' (dblWu.{u}.dblX dblPu dblQu dblEu)
      = W.dblX p q e := by
    rw [← WeierstrassCurve.map_dblX dblWu.{u} (algebraMap DblRing.{u} A')
      dblPu dblQu dblEu, hPim, hQim, hEim, hWeq]
  have hYim : algebraMap DblRing.{u} A' (dblWu.{u}.dblY dblPu dblQu dblEu)
      = W.dblY p q e := by
    rw [← WeierstrassCurve.map_dblY dblWu.{u} (algebraMap DblRing.{u} A')
      dblPu dblQu dblEu, hPim, hQim, hEim, hWeq]
  have hEmap := WeierstrassCurve.Affine.Equation.map (algebraMap DblRing.{u} A')
    dblWu_equation_dbl
  rw [hXim, hYim] at hEmap
  rw [show dblWu.{u}.toAffine.map (algebraMap DblRing.{u} A')
      = W.toAffine from by rw [← hWeq]] at hEmap
  exact hEmap

/-- The clearing algebra: `dblX = p` clears to KM's `hdbl`. -/
theorem hdbl_of_dblX_eq {A' : Type*} [CommRing A'] (W : WeierstrassCurve A')
    (p q e : A') (he : W.tangentDen p q * e = 1)
    (hX : W.dblX p q e = p) :
    (W.tangentNum p q) ^ 2 + W.a₁ * (W.tangentNum p q) * (W.tangentDen p q)
      - (W.a₂ + 3 * p) * (W.tangentDen p q) ^ 2 = 0 := by
  have h := congrArg (fun z => z * (W.tangentDen p q) ^ 2) hX
  simp only [WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
    WeierstrassCurve.Affine.addX] at h
  rw [show W.toAffine.a₁ = W.a₁ from rfl, show W.toAffine.a₂ = W.a₂ from rfl] at h
  linear_combination h + (-(W.tangentNum p q) ^ 2 * (W.tangentDen p q) * e
      - (W.tangentNum p q) ^ 2
      - (W.tangentNum p q) * W.a₁ * (W.tangentDen p q)) * he

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(the tangent-denominator certificate)** On a chart marking a fibrewise-nonzero
`3`-torsion section at `(p, q)`, the tangent denominator is a unit (a vanishing fibre
value would make the point `2`-torsion, but `3`- and `2`-torsion force zero). -/
theorem isUnit_tangentDen_of_marked {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {p q : Γ(S, V.1)} (heq : Pr.W.toAffine.Equation p q)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heq)
    (hkill : (3 : ℤ) • (⟨σ, hσ⟩ : E.Section) = 0)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ E.zero) :
    IsUnit (Pr.W.tangentDen p q) := by
  letI := Pr.elliptic
  refine isUnit_of_forall_algebraMap_residueField_ne_zero (fun 𝔭 => ?_)
  intro hd0
  set K : Type u := 𝔭.asIdeal.ResidueField with hK
  set Kb : Type u := AlgebraicClosure K with hKb
  letI : DecidableEq Kb := Classical.decEq Kb
  letI : Algebra ↑Γ(S, V.1) Kb :=
    ((algebraMap K Kb).comp (algebraMap ↑Γ(S, V.1) K)).toAlgebra
  have halgKb : ∀ z : ↑Γ(S, V.1), algebraMap ↑Γ(S, V.1) Kb z =
      algebraMap K Kb (algebraMap ↑Γ(S, V.1) K z) := fun _ => rfl
  set tVb : Spec (CommRingCat.of Kb) ⟶ Spec Γ(S, V.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(S, V.1) Kb)) with htVb
  set x := chartPointsEquiv Pr tVb
    (EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩) with hx
  have hkillE : (3 : ℤ) • EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have hkill3 : (3 : ℤ) • x = 0 := by
    rw [hx, ← map_zsmul, hkillE, map_zero]
  have hx0 : x ≠ 0 := by
    intro hc
    have h0 : EllipticCurve.Point.pull E (tVb ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
      exact (chartPointsEquiv Pr tVb).map_eq_zero_iff.mp (hx ▸ hc)
    refine hne Kb (tVb ≫ chartρ V) ?_
    have hval := congrArg Subtype.val h0
    rw [E.point_zero_val] at hval
    exact hval
  haveI : ((Pr.W.baseChange Kb)).IsElliptic :=
    inferInstanceAs ((Pr.W.map (algebraMap ↑Γ(S, V.1) Kb)).IsElliptic)
  have hns : (Pr.W.baseChange Kb).toAffine.Nonsingular
      (algebraMap ↑Γ(S, V.1) Kb p) (algebraMap ↑Γ(S, V.1) Kb q) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (WeierstrassCurve.Affine.Equation.map _ heq)
  have hxpkg : x = ⟨(affineSectionSpecPoint Pr.W Kb p q heq).1,
      (affineSectionSpecPoint Pr.W Kb p q heq).2⟩ := by
    refine Subtype.ext ?_
    rw [hx, chartPointsEquiv_pull_marked Pr tVb heq hMeq]
    rfl
  set y := modelPointAddEquiv Pr.W (K' := Kb) x with hy
  have hyval : y = WeierstrassCurve.Affine.Point.some _ _ hns := by
    rw [hy, hxpkg]
    show projModelPointsEquiv Pr.W Kb (affineSectionSpecPoint Pr.W Kb p q heq) = _
    exact projModelPointsEquiv_affineSectionSpecPoint Pr.W p q heq hns
  have hy3 : (3 : ℤ) • y = 0 := by
    rw [hy, ← map_zsmul, hkill3, map_zero]
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact fun hc => hx0 ((modelPointAddEquiv Pr.W (K' := Kb)).map_eq_zero_iff.mp hc)
  -- the vanishing denominator makes `y` two-torsion
  have hdKb : algebraMap ↑Γ(S, V.1) Kb (Pr.W.tangentDen p q) = 0 := by
    rw [halgKb, hd0, map_zero]
  have hyeq : algebraMap ↑Γ(S, V.1) Kb q
      = (Pr.W.baseChange Kb).toAffine.negY
        (algebraMap ↑Γ(S, V.1) Kb p) (algebraMap ↑Γ(S, V.1) Kb q) := by
    rw [WeierstrassCurve.Affine.negY]
    rw [show ((Pr.W.baseChange Kb)).toAffine.a₁
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₁ from rfl,
      show ((Pr.W.baseChange Kb)).toAffine.a₃
        = algebraMap ↑Γ(S, V.1) Kb Pr.W.a₃ from rfl]
    have hexp : algebraMap ↑Γ(S, V.1) Kb (2 * q + Pr.W.a₁ * p + Pr.W.a₃) = 0 := by
      rw [show (2 * q + Pr.W.a₁ * p + Pr.W.a₃ : ↑Γ(S, V.1))
        = Pr.W.tangentDen p q from rfl]
      exact hdKb
    rw [map_add, map_add, map_mul, map_mul, map_ofNat] at hexp
    linear_combination hexp
  have hy2 : (2 : ℤ) • y = 0 := by
    rw [hyval, two_zsmul]
    exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hyeq
  have : y = 0 := by
    have h1 : ((3 : ℤ) - 2) • y = 0 := by
      rw [sub_smul, hy3, hy2, sub_zero]
    rwa [show ((3 : ℤ) - 2) = 1 by norm_num, one_smul] at h1
  exact hy0 this


open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(the master bridge input ★★★)** A chart-marked fibrewise-nonzero `3`-torsion
section satisfies the cleared doubling condition `hdbl`: `RING-DBL` + the negation
coordinate + coordinate injectivity. -/
theorem hdbl_of_marked_three_torsion {S : Scheme.{u}} {E : EllipticCurve S}
    {V : S.affineOpens} (Pr : LocalPresentation E.toEllipticCurveGeom V)
    {σ : S ⟶ E.toEllipticCurveGeom.E} {hσ : σ ≫ E.toEllipticCurveGeom.π = 𝟙 S}
    {p q : Γ(S, V.1)} (heq : Pr.W.toAffine.Equation p q)
    (hMeq : (V.2.isoSpec.inv ≫ sectionLift E.toEllipticCurveGeom hσ V) ≫ Pr.e.hom =
      projModelAffineSection Pr.W p q heq)
    (hkill : (3 : ℤ) • (⟨σ, hσ⟩ : E.Section) = 0)
    (hne : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
      t ≫ σ ≠ t ≫ E.zero) :
    (Pr.W.tangentNum p q) ^ 2
      + Pr.W.a₁ * (Pr.W.tangentNum p q) * (Pr.W.tangentDen p q)
      - (Pr.W.a₂ + 3 * p) * (Pr.W.tangentDen p q) ^ 2 = 0 := by
  letI := Pr.elliptic
  -- the unit tangent denominator and its inverse witness
  have hd := isUnit_tangentDen_of_marked Pr heq hMeq hkill hne
  set e : ↑Γ(S, V.1) := ((hd.unit⁻¹ : _ˣ) : ↑Γ(S, V.1)) with he_def
  have he : Pr.W.tangentDen p q * e = 1 := hd.mul_val_inv
  -- the model section of the marked point
  set σm := chartPointsEquiv Pr (𝟙 (Spec Γ(S, V.1)))
    (EllipticCurve.Point.pull E (𝟙 (Spec Γ(S, V.1)) ≫ chartρ V) ⟨σ, hσ⟩) with hσm
  have hσmval : σm = ⟨projModelAffineSection Pr.W p q heq,
      projModelAffineSection_projModelπ _ _ _ _⟩ := by
    refine Subtype.ext ?_
    rw [hσm, chartPointsEquiv_pull_marked Pr (𝟙 _) heq hMeq]
    exact Category.id_comp _
  -- three-torsion of the model section
  have hkillE : (3 : ℤ) • EllipticCurve.Point.pull E
      (𝟙 (Spec Γ(S, V.1)) ≫ chartρ V) ⟨σ, hσ⟩ = 0 := by
    rw [← EllipticCurve.Point.pull_zsmul, hkill, EllipticCurve.Point.pull_zero]
  have h3 : (3 : ℤ) • σm = 0 := by
    rw [hσm, ← map_zsmul, hkillE, map_zero]
  have h2 : (2 : ℤ) • σm = -σm := by
    have h1 : ((3 : ℤ) - 1) • σm = (3 : ℤ) • σm - (1 : ℤ) • σm := sub_smul _ _ _
    rw [h3, one_smul, zero_sub] at h1
    rw [show ((3 : ℤ) - 1) = 2 by norm_num] at h1
    exact h1
  -- RING-DBL: the double is the doubling-coordinate section
  have hdblsec := two_zsmul_affineSection Pr.W p q e heq he
    (equation_dblXY Pr.W p q e heq he)
  -- the negation coordinate: `−σm` is the negY-section
  have hnegval : -σm = (⟨projModelAffineSection Pr.W p (Pr.W.toAffine.negY p q)
      ((Pr.W.toAffine.equation_neg p q).mpr heq),
      projModelAffineSection_projModelπ _ _ _ _⟩ :
    (modelEllipticCurve Pr.W).Section) := by
    refine Subtype.ext ?_
    have hv : (-σm).1 = σm.1 ≫ (modelEllipticCurve Pr.W).mulByHom (-1) := by
      rw [show -σm = (-1 : ℤ) • σm from (neg_one_zsmul σm).symm]
      exact (modelEllipticCurve Pr.W).point_smul_eq_comp_mulBy _ (-1) σm
    rw [hv, modelEllipticCurve_mulByHom_neg_one, hσmval]
    exact negModelHom_affineSection_general Pr.W p q heq
  -- combine and read off the X-coordinate
  have hchain : (⟨projModelAffineSection Pr.W (Pr.W.dblX p q e) (Pr.W.dblY p q e)
      (equation_dblXY Pr.W p q e heq he),
      projModelAffineSection_projModelπ _ _ _ _⟩ :
    (modelEllipticCurve Pr.W).Section)
      = ⟨projModelAffineSection Pr.W p (Pr.W.toAffine.negY p q)
        ((Pr.W.toAffine.equation_neg p q).mpr heq),
        projModelAffineSection_projModelπ _ _ _ _⟩ := by
    rw [← hnegval, ← h2, ← hdblsec, hσmval]
  have hvals : projModelAffineSection Pr.W (Pr.W.dblX p q e) (Pr.W.dblY p q e)
      (equation_dblXY Pr.W p q e heq he)
      = projModelAffineSection Pr.W p (Pr.W.toAffine.negY p q)
        ((Pr.W.toAffine.equation_neg p q).mpr heq) :=
    congrArg Subtype.val hchain
  have hX := (projModelAffineSection_injective Pr.W (heq := hvals)).1
  exact hdbl_of_dblX_eq Pr.W p q e he hX


open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(BRIDGE-P ★★★)** The `a₂`-obstruction of an origin-marked chart of the first
marked section vanishes. -/
theorem bridgeP_holds {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (3 : R))
    (L : X.curve.FullLevelPt 3) (V : X.base.affineOpens)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (hM : Pr.MarksAt L.1.1.2 0 0) :
    Pr.W.a₂ * Pr.W.a₃ ^ 2 - Pr.W.a₄ * Pr.W.a₁ * Pr.W.a₃ - Pr.W.a₄ ^ 2 = 0 := by
  obtain ⟨heq, hMeq⟩ := id hM
  have hN : NIsInvertible X.base 3 := by
    have h0 : NIsInvertible (Spec R) 3 := by
      rw [NIsInvertible, Nat.cast_ofNat]
      have := hR.map (Scheme.ΓSpecIso R).inv.hom
      rwa [map_ofNat] at this
    exact h0.of_hom X.structMap
  have hne := X.curve.pull_ne_zero_left_of_isNaiveFullLevel 3 (by norm_num) hN L.2
  have hkill : (3 : ℤ) • (⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ : X.curve.Section) = 0 := by
    have h := L.2.1.1
    exact_mod_cast h
  have ha₆ : Pr.W.a₆ = 0 := WeierstrassCurve.Affine.equation_zero.mp heq
  have hdbl := hdbl_of_marked_three_torsion Pr heq hMeq hkill hne
  exact bridgeP_of_dbl_origin Pr.W ha₆ hdbl

open LocalPresentation in
set_option backward.isDefEq.respectTransparency false in
/-- **(BRIDGE-Q ★★★)** The flex-chart cubic at the second marked point vanishes. -/
theorem bridgeQ_holds {R : CommRingCat.{u}} (X : EllObj R) (hR : IsUnit (3 : R))
    (L : X.curve.FullLevelPt 3) (V : X.base.affineOpens)
    (Pr : LocalPresentation X.curve.toEllipticCurveGeom V)
    (ha₂ : Pr.W.a₂ = 0) (ha₄ : Pr.W.a₄ = 0) (ha₆ : Pr.W.a₆ = 0)
    (hMP : Pr.MarksAt L.1.1.2 0 0) (p q : Γ(X.base, V.1))
    (hMQ : Pr.MarksAt L.1.2.2 p q) :
    3 * p ^ 3 + Pr.W.a₁ ^ 2 * p ^ 2 + 3 * Pr.W.a₁ * Pr.W.a₃ * p
      + 3 * Pr.W.a₃ ^ 2 = 0 := by
  obtain ⟨heqQ, hMeqQ⟩ := id hMQ
  obtain ⟨heqP, hMeqP⟩ := id hMP
  have hN : NIsInvertible X.base 3 := by
    have h0 : NIsInvertible (Spec R) 3 := by
      rw [NIsInvertible, Nat.cast_ofNat]
      have := hR.map (Scheme.ΓSpecIso R).inv.hom
      rwa [map_ofNat] at this
    exact h0.of_hom X.structMap
  have hneQ := X.curve.pull_ne_zero_right_of_isNaiveFullLevel 3 (by norm_num) hN L.2
  have hkillQ : (3 : ℤ) • (⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩ : X.curve.Section) = 0 := by
    have h := L.2.1.2
    exact_mod_cast h
  have hdbl := hdbl_of_marked_three_torsion Pr heqQ hMeqQ hkillQ hneQ
  have hcurve : q ^ 2 + Pr.W.a₁ * p * q + Pr.W.a₃ * q
      = p ^ 3 + Pr.W.a₂ * p ^ 2 + Pr.W.a₄ * p + Pr.W.a₆ := by
    have h := (WeierstrassCurve.Affine.equation_iff _ _).mp heqQ
    linear_combination h
  have hΨ := WeierstrassCurve.Ψ₃_eval_eq_zero_of_dbl_eq_neg Pr.W p q hcurve hdbl
  have hpm : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (t : Spec (CommRingCat.of k) ⟶ X.base),
      EllipticCurve.Point.pull X.curve t ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩
        ≠ EllipticCurve.Point.pull X.curve t ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ ∧
      EllipticCurve.Point.pull X.curve t ⟨(L.1.2 : _ ⟶ _), L.1.2.2⟩
        ≠ -EllipticCurve.Point.pull X.curve t ⟨(L.1.1 : _ ⟶ _), L.1.1.2⟩ := by
    intro k _ _ t
    exact X.curve.pull_ne_pm_of_isNaiveFullLevel 3 (by norm_num) hN L.2 k t
  have hp : IsUnit p :=
    isUnit_x_of_marked_pair Pr heqP hMeqP heqQ hMeqQ hpm
  exact WeierstrassCurve.bridgeQ_cubic_of_Ψ₃ Pr.W ha₂ ha₄ ha₆ p hp hΨ


end ModularCurves
