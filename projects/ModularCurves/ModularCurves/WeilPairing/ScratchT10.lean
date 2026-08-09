import ModularCurves.WeilPairing.TheoremOfSquareField
import ModularCurves.EllipticCurve.SectionCoordinates
import ModularCurves.EllipticCurve.PoleSheafModel
import ModularCurves.EllipticCurve.AffineSectionSpecPoints

open CategoryTheory AlgebraicGeometry Opposite Polynomial HomogeneousIdeal
open WeierstrassCurve.Affine.CoordinateRing

namespace ModularCurves

universe v

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

variable {R : Type*} [CommRing R]

/-- The kernel of an `R`-algebra evaluation of the affine coordinate ring at a point of the
curve is exactly `XYIdeal`. -/
theorem ker_eq_XYIdeal {W : WeierstrassCurve.Affine R} {p q : R}
    (h : W.Equation p q) (ε : W.CoordinateRing →+* R)
    (hC : ∀ r : R, ε (algebraMap R W.CoordinateRing r) = r)
    (hx : ε (XClass W p) = 0) (hy : ε (YClass W (C q)) = 0) :
    RingHom.ker ε = XYIdeal W p (C q) := by
  have hle : XYIdeal W p (C q) ≤ RingHom.ker ε := by
    rw [XYIdeal, Ideal.span_le]
    rintro a (rfl | rfl)
    · exact hx
    · exact hy
  refine le_antisymm (fun a ha => ?_) hle
  set e := quotientXYIdealEquiv (W' := W) (x := p) (y := C q) h with he
  set r : R := e (Ideal.Quotient.mk (XYIdeal W p (C q)) a) with hr
  have hcomm : e (Ideal.Quotient.mk (XYIdeal W p (C q)) (algebraMap R W.CoordinateRing r)) = r :=
    e.commutes r
  have hzero : Ideal.Quotient.mk (XYIdeal W p (C q)) (a - algebraMap R W.CoordinateRing r) = 0 := by
    refine e.injective ?_
    rw [map_sub, map_sub, hcomm, ← hr, sub_self, map_zero]
  have hmem : a - algebraMap R W.CoordinateRing r ∈ XYIdeal W p (C q) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hr0 : r = 0 := by
    have := hle hmem
    rw [RingHom.mem_ker, map_sub, hC, RingHom.mem_ker.mp ha, zero_sub, neg_eq_zero] at this
    exact this
  rw [hr0, map_zero, sub_zero] at hmem
  exact hmem

/-- `X - x` as the difference of the coordinate `x` and a constant. -/
theorem XClass_eq_coordX_sub (W : WeierstrassCurve R) (p : R) :
    XClass W.toAffine p = coordX W - algebraMap R W.toAffine.CoordinateRing p := by
  rw [XClass, coordX]
  show AdjoinRoot.mk _ _ = AdjoinRoot.mk _ _ - AdjoinRoot.mk _ _
  rw [← map_sub]
  congr 1
  rw [map_sub]
  rfl

/-- `Y - y` as the difference of the coordinate `y` and a constant. -/
theorem YClass_eq_coordY_sub (W : WeierstrassCurve R) (q : R) :
    YClass W.toAffine (C q) = coordY W - algebraMap R W.toAffine.CoordinateRing q := by
  rw [YClass, coordY]
  show AdjoinRoot.mk _ _ = AdjoinRoot.mk _ _ - AdjoinRoot.mk _ _
  rw [← map_sub]
  congr 1

/-- The affine-point chart evaluation on the chart coordinates `Xⱼ/Z` is `Xⱼ` evaluated at
`[p : q : 1]`. -/
theorem affineChartHom_isLocalizationElem (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (j : Fin 3) :
    affineChartHom W p q h (Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W 2) (mk_X_mem_quotientGrading_one W j)) =
      MvPolynomial.eval ![p, q, 1] (MvPolynomial.X j) := by
  rw [show Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
      (mk_X_mem_quotientGrading_one W j) =
    Away.mk (quotientGrading (projIdeal W)) (mk_X_mem_quotientGrading_one W 2) 1
      (((quotientGradingHom (projIdeal W)) (MvPolynomial.X j)) ^ 1)
      (by simpa using SetLike.pow_mem_graded 1 (mk_X_mem_quotientGrading_one W j)) from rfl]
  rw [affineChartHom_mk, map_pow, pow_one]
  rw [show (quotientGradingHom (projIdeal W)) (MvPolynomial.X j) =
    Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.X j) from rfl]
  rw [projModelAffineEval_mk]

/-- The affine-point chart evaluation retracts the base ring. -/
theorem affineChartHom_fromZero (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) (r : R) :
    affineChartHom W p q h ((fromZeroRingHom (quotientGrading (projIdeal W))
      (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
        ((algebraMapGradeZero (projIdeal W)) r)) = r :=
  RingHom.congr_fun (affineChartHom_comp_algebraMap W p q h) r

/-- **The `Z`-chart ideal dictionary, ring form.** The kernel of the chart evaluation at the
affine point `(p, q)` is mathlib's `XYIdeal W p (C q)`, pulled back along the identification of
the `Z`-chart ring with the affine coordinate ring. -/
theorem ker_affineChartHom (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    RingHom.ker (affineChartHom W p q h) =
      Ideal.comap (chartZRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (XYIdeal W.toAffine p (C q)) := by
  set ε : W.toAffine.CoordinateRing →+* R :=
    (affineChartHom W p q h).comp ((chartZRingEquiv W).symm : _ →+* _) with hε
  have hC : ∀ r : R, ε (algebraMap R W.toAffine.CoordinateRing r) = r := by
    intro r
    have hsym : (chartZRingEquiv W).symm (algebraMap R W.toAffine.CoordinateRing r) =
        (fromZeroRingHom (quotientGrading (projIdeal W))
          (Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))))
            ((algebraMapGradeZero (projIdeal W)) r) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_fromZero W r).symm
    show affineChartHom W p q h ((chartZRingEquiv W).symm _) = r
    rw [hsym, affineChartHom_fromZero]
  have hx : ε (XClass W.toAffine p) = 0 := by
    have hsym : (chartZRingEquiv W).symm (coordX W) =
        Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
          (mk_X_mem_quotientGrading_one W 0) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_x W).symm
    rw [XClass_eq_coordX_sub, map_sub, hC]
    show affineChartHom W p q h ((chartZRingEquiv W).symm (coordX W)) - p = 0
    rw [hsym, affineChartHom_isLocalizationElem]
    simp
  have hy : ε (YClass W.toAffine (C q)) = 0 := by
    have hsym : (chartZRingEquiv W).symm (coordY W) =
        Away.isLocalizationElem (mk_X_mem_quotientGrading_one W 2)
          (mk_X_mem_quotientGrading_one W 1) :=
      (RingEquiv.symm_apply_eq _).mpr (chartZRingEquiv_y W).symm
    rw [YClass_eq_coordY_sub, map_sub, hC]
    show affineChartHom W p q h ((chartZRingEquiv W).symm (coordY W)) - q = 0
    rw [hsym, affineChartHom_isLocalizationElem]
    simp
  have hker := ker_eq_XYIdeal h ε hC hx hy
  have hcomp : ε.comp (chartZRingEquiv W : _ →+* W.toAffine.CoordinateRing) =
      affineChartHom W p q h := by
    refine RingHom.ext fun a => ?_
    show affineChartHom W p q h ((chartZRingEquiv W).symm (chartZRingEquiv W a)) = _
    rw [RingEquiv.symm_apply_apply]
  rw [← hker, ← hcomp, ← RingHom.comap_ker]

/-- The affine-point section in `fromSpec` chart coordinates. -/
theorem projModelAffineSection_eq_fromSpec (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h =
      Spec.map ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
        CommRingCat.ofHom (affineChartHom W p q h)) ≫
      (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).fromSpec := by
  rw [← spec_affineChartHom_awayι W p q h, Proj_fromSpec_awayToSection_awayι, Spec.map_comp,
    Category.assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    show Proj.awayToSection (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) ≫
        (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
        CommRingCat.ofHom (affineChartHom W p q h) =
        CommRingCat.ofHom (affineChartHom W p q h) from by
      rw [← Category.assoc, show Proj.awayToSection (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) =
        (Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
          ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
          (mk_X_mem_quotientGrading_one W 2) one_pos).hom from rfl,
        Iso.hom_inv_id, Category.id_comp]]

/-- **(general)** If a morphism out of an affine scheme factors as `Spec` of a ring map followed
by `fromSpec` of an affine open `U`, then its kernel ideal sheaf on `U` is the kernel of that ring
map. -/
theorem ker_ideal_of_fromSpec_factor {X : Scheme.{v}} {U : X.Opens} (hU : IsAffineOpen U)
    {A : CommRingCat.{v}} (φ : Γ(X, U) ⟶ A) (f : Spec A ⟶ X) [QuasiCompact f]
    (hfac : f = Spec.map φ ≫ hU.fromSpec) :
    (Scheme.Hom.ker f).ideal ⟨U, hU⟩ = RingHom.ker φ.hom := by
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    rw [hfac]
    show Spec.map φ ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) = ⊤
    rw [hU.fromSpec_preimage_self]
    rfl
  have hi : (⊤ : (Spec A).Opens) ≤ f ⁻¹ᵁ U := le_of_eq hpre.symm
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
  exact ⟨fun hh => hinj2 (by rw [hh, map_zero]), fun hh => by rw [hh, map_zero]⟩

/-- **(1a) The `Z`-chart ideal dictionary, sheaf form.** The section ideal sheaf of the affine
point `(p, q)`, read on the affine `Z`-chart, is mathlib's `XYIdeal W p (C q)`. -/
theorem ker_ideal_projModelAffineSection_chartZ (W : WeierstrassCurve R) (p q : R)
    (h : W.toAffine.Equation p q) :
    (Scheme.Hom.ker (projModelAffineSection W p q h)).ideal (projModelZChart W) =
      Ideal.comap (chartZSectionsRingEquiv W : _ →+* W.toAffine.CoordinateRing)
        (XYIdeal W.toAffine p (C q)) := by
  have hker := ker_ideal_of_fromSpec_factor
    (Proj.isAffineOpen_basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
      (mk_X_mem_quotientGrading_one W 2) one_pos)
    ((Proj.basicOpenIsoAway (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2))
        (mk_X_mem_quotientGrading_one W 2) one_pos).inv ≫
      CommRingCat.ofHom (affineChartHom W p q h))
    (projModelAffineSection W p q h) (projModelAffineSection_eq_fromSpec W p q h)
  refine hker.trans ?_
  rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, ker_affineChartHom,
    Ideal.comap_comap]
  rfl

section Field

variable {k : Type u} [Field k] [DecidableEq k]

example (W : WeierstrassCurve k) (x : k) : algebraMap k k x = x := rfl

/-- **(1a, the section identification)** The section of the projective model attached to an
affine point `some x y` is the affine-point section `[x : y : 1]`. -/
theorem pointSection_some (W : WeierstrassCurve k) [W.IsElliptic] (x y : k)
    (h : W.toAffine.Nonsingular x y) :
    pointSection W (WeierstrassCurve.Affine.Point.some x y h) =
      projModelAffineSection W x y h.left := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [show CommRingCat.ofHom (algebraMap k k) = 𝟙 (CommRingCat.of k) from rfl, Spec.map_id]
  have hsec : (affineSectionSpecPoint W k x y h.left).1 = projModelAffineSection W x y h.left := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ projModelAffineSection W x y h.left = _
    rw [hid, Category.id_comp]
  have hkey := projModelPointsEquiv_affineSectionSpecPoint W (K := k) x y h.left h
  have hsym := (projModelPointsEquiv W k).symm_apply_eq.mpr hkey.symm
  show (((projModelPointsEquiv W k).symm) (WeierstrassCurve.Affine.Point.some x y h)).1 = _
  rw [hsym]
  exact hsec

end Field

end ModularCurves
