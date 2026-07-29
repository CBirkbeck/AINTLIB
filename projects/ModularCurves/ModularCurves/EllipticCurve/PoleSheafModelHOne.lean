import ModularCurves.EllipticCurve.PoleSheafModel
import ModularCurves.EllipticCurve.PoleSheafQuasicoherent
import ModularCurves.ForMathlib.AffineVanishing
import ModularCurves.ForMathlib.TwoOpenHOne

/-!
# First cohomology of pole sheaves on Weierstrass models

This file proves the explicit two-chart principal-parts calculation for `O(n[0])` on a
projective Weierstrass model over a field. The resulting surjectivity of the section-difference
map, together with affine vanishing, gives `H^1(O(n[0])) = 0` for every `n >= 1`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

private lemma exists_add_twisted_of_denominator_step
    {C S A : Type*} [CommRing C] [CommRing S] [CommRing A]
    (r : C) [Algebra C S] [IsLocalization.Away r S]
    (φ : A →+* S) (n : ℕ)
    (hstep : ∀ (c : C) (k : ℕ), ∃ (a : A) (c' : C),
      algebraMap C S c =
        φ a * algebraMap C S r ^ (n + k + 1) +
          algebraMap C S (c' * r)) :
    ∀ q : S, ∃ (c : C) (a : A),
      algebraMap C S c + φ a * algebraMap C S r ^ n = q := by
  let R : S := algebraMap C S r
  have hR : IsUnit R := IsLocalization.map_units S
    (⟨r, ⟨1, pow_one r⟩⟩ : Submonoid.powers r)
  have aux : ∀ (k : ℕ) (c : C) (q : S), q * R ^ k = algebraMap C S c →
      ∃ (b : C) (a : A), algebraMap C S b + φ a * R ^ n = q := by
    intro k
    induction k with
    | zero =>
      intro c q hq
      simp only [pow_zero, mul_one] at hq
      exact ⟨c, 0, by simpa only [map_zero, zero_mul, add_zero] using hq.symm⟩
    | succ k ih =>
      intro c q hq
      obtain ⟨a, c', hc⟩ := hstep c k
      let q' := q - φ a * R ^ n
      have hq' : q' * R ^ k = algebraMap C S c' := by
        apply hR.mul_right_cancel
        calc
          q' * R ^ k * R = q * R ^ (k + 1) - φ a * R ^ (n + k + 1) := by
            dsimp only [q']
            rw [pow_succ]
            ring
          _ = algebraMap C S c - φ a * R ^ (n + k + 1) := by rw [hq]
          _ = algebraMap C S (c' * r) := by rw [hc]; ring
          _ = algebraMap C S c' * R := by rw [map_mul]
      obtain ⟨b, a', ha'⟩ := ih c' q' hq'
      refine ⟨b, a' + a, ?_⟩
      rw [map_add]
      calc
        algebraMap C S b + (φ a' + φ a) * R ^ n =
            (algebraMap C S b + φ a' * R ^ n) + φ a * R ^ n := by ring
        _ = q' + φ a * R ^ n := by rw [ha']
        _ = q := by dsimp only [q']; ring
  intro q
  obtain ⟨⟨c, d⟩, hq⟩ := IsLocalization.surj (Submonoid.powers r) q
  obtain ⟨k, hk⟩ := d.2
  apply aux k c q
  simpa only [R, ← hk, map_pow] using hq

namespace ModularCurves

variable {K : Type u} [Field K]

private noncomputable def projModelSectionNeighborhoodMap
    (W : WeierstrassCurve K) :
    AdjoinRoot (infChartCubic W) →+*
      Γ(projModel W, projModelSectionNeighborhood W) :=
  ((projModel W).presheaf.map
      (homOfLE ((projModel W).affineBasicOpen_le
        (projModelSectionUnitSection W))).op).hom.comp
    (chartYSectionsRingEquiv W).symm.toRingHom

private lemma exists_projModelSectionNeighborhood_scalar_add_root_mul
    (W : WeierstrassCurve K)
    (c : Γ(projModel W, projModelSectionNeighborhood W)) :
    ∃ (scalar : K) (e : Γ(projModel W, projModelSectionNeighborhood W)),
      c = projModelSectionNeighborhoodMap W
          (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) +
        e * projModelSectionRoot W := by
  let X := projModel W
  let Y := projModelYChart W
  let N := projModelSectionNeighborhood W
  let u : Γ(X, Y) := projModelSectionUnitSection W
  let res : Γ(X, Y) →+* Γ(X, N) :=
    (X.presheaf.map (homOfLE (X.affineBasicOpen_le u)).op).hom
  let ψ : AdjoinRoot (infChartCubic W) →+* Γ(X, N) :=
    res.comp (chartYSectionsRingEquiv W).symm.toRingHom
  let s : Γ(X, N) := ψ (AdjoinRoot.root (infChartCubic W))
  let I : Ideal Γ(X, N) := Ideal.span {s}
  letI : Algebra Γ(X, Y) Γ(X, N) := res.toAlgebra
  haveI : IsLocalization.Away u Γ(X, N) := Y.2.isLocalization_basicOpen u
  have hu : IsUnit (res u) :=
    AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace u
  have himage : Ideal.map ψ (RingHom.ker (infChartAug W)) ≤ I := by
    exact image_ker_aug_le_span_of_isUnit ψ (by
      change IsUnit (res u)
      exact hu)
  obtain ⟨⟨b, d⟩, hbd⟩ := IsLocalization.surj (Submonoid.powers u) c
  obtain ⟨j, hj⟩ := d.2
  let b' := chartYSectionsRingEquiv W b
  let scalar := infChartAug W b'
  have hnum : res b - ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) ∈ I := by
    have hker : b' - algebraMap K (AdjoinRoot (infChartCubic W)) scalar ∈
        RingHom.ker (infChartAug W) := by
      rw [RingHom.mem_ker, map_sub, infChartAug_algebraMap]
      exact sub_self scalar
    have hmap := himage (Ideal.mem_map_of_mem ψ hker)
    change ψ (b' - algebraMap K (AdjoinRoot (infChartCubic W)) scalar) ∈ I at hmap
    rw [map_sub] at hmap
    change res ((chartYSectionsRingEquiv W).symm b') -
      ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) ∈ I at hmap
    rw [show (chartYSectionsRingEquiv W).symm b' = b by
      exact RingEquiv.symm_apply_apply _ _] at hmap
    exact hmap
  have hu1 : res u - 1 ∈ I := by
    have hker : sectionUnitElem W - 1 ∈ RingHom.ker (infChartAug W) := by
      rw [RingHom.mem_ker, map_sub, infChartAug_sectionUnitElem, map_one, sub_self]
    have hmap := himage (Ideal.mem_map_of_mem ψ hker)
    change ψ (sectionUnitElem W - 1) ∈ I at hmap
    rw [map_sub, map_one] at hmap
    change res ((chartYSectionsRingEquiv W).symm (sectionUnitElem W)) - 1 ∈ I at hmap
    exact hmap
  have hpow : (res u) ^ j - 1 ∈ I :=
    Ideal.mem_of_dvd _ (sub_one_dvd_pow_sub_one (res u) j) hu1
  have hden : algebraMap Γ(X, Y) Γ(X, N) d.1 = (res u) ^ j := by
    change res d.1 = (res u) ^ j
    rw [show d.1 = u ^ j from hj.symm, map_pow]
  have hcb : c - res b ∈ I := by
    have hmul : c * ((res u) ^ j - 1) ∈ I := Ideal.mul_mem_left I c hpow
    have hrel : c * (res u) ^ j = res b := by
      rw [← hden]
      exact hbd
    have heq : c - res b = -(c * ((res u) ^ j - 1)) := by
      calc
        c - res b = c - c * (res u) ^ j := congrArg (c - ·) hrel.symm
        _ = -(c * ((res u) ^ j - 1)) := by ring
    rw [heq]
    exact I.neg_mem hmul
  have hscalar : c - ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) ∈ I := by
    convert I.add_mem hcb hnum using 1
    ring
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hscalar
  refine ⟨scalar, e, ?_⟩
  change c = ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) + e * s
  linear_combination he

private noncomputable def sectionCofactorElem (W : WeierstrassCurve K) :
    AdjoinRoot (infChartCubic W) :=
  sectionUnitElem W -
    algebraMap (Polynomial K) (AdjoinRoot (infChartCubic W))
        (Polynomial.C W.a₂) * AdjoinRoot.root (infChartCubic W) ^ 2

private lemma tel_mul_sectionCofactorElem (W : WeierstrassCurve K) :
    infChartTElem W * sectionCofactorElem W =
      AdjoinRoot.root (infChartCubic W) ^ 3 := by
  rw [sectionCofactorElem]
  have h := tel_mul_sectionUnitElem W
  simp only [map_mul] at h ⊢
  linear_combination h

private lemma sectionCofactorElem_sub_one_mem_ker (W : WeierstrassCurve K) :
    sectionCofactorElem W - 1 ∈ RingHom.ker (infChartAug W) := by
  rw [RingHom.mem_ker, sectionCofactorElem, map_sub, map_sub, map_mul, map_pow,
    infChartAug_sectionUnitElem, infChartAug_poly, infChartAug_root, map_one]
  simp only [Polynomial.eval_C]
  ring

private lemma exists_projModelSectionNeighborhood_scalar_cofactor_add_root_mul
    (W : WeierstrassCurve K)
    (c : Γ(projModel W, projModelSectionNeighborhood W)) (p : ℕ) :
    ∃ (scalar : K) (e : Γ(projModel W, projModelSectionNeighborhood W)),
      c = projModelSectionNeighborhoodMap W
          (algebraMap K (AdjoinRoot (infChartCubic W)) scalar *
            sectionCofactorElem W ^ p) +
        e * projModelSectionRoot W := by
  obtain ⟨scalar, e₀, hc⟩ :=
    exists_projModelSectionNeighborhood_scalar_add_root_mul W c
  let ψ := projModelSectionNeighborhoodMap W
  let s := projModelSectionRoot W
  let I : Ideal Γ(projModel W, projModelSectionNeighborhood W) := Ideal.span {s}
  have hvp : ψ (sectionCofactorElem W ^ p) - 1 ∈ I := by
    let X := projModel W
    let Y := projModelYChart W
    let N := projModelSectionNeighborhood W
    let u : Γ(X, Y) := projModelSectionUnitSection W
    let res : Γ(X, Y) →+* Γ(X, N) :=
      (X.presheaf.map (homOfLE (X.affineBasicOpen_le u)).op).hom
    have hu : IsUnit (res u) :=
      AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen X.toRingedSpace u
    have himage : Ideal.map ψ (RingHom.ker (infChartAug W)) ≤ I := by
      exact image_ker_aug_le_span_of_isUnit ψ (by
        change IsUnit (res u)
        exact hu)
    have hker : sectionCofactorElem W ^ p - 1 ∈ RingHom.ker (infChartAug W) := by
      rw [RingHom.mem_ker, map_sub, map_pow]
      have hv := sectionCofactorElem_sub_one_mem_ker W
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hv
      rw [hv, one_pow, map_one, sub_self]
    have hmap := himage (Ideal.mem_map_of_mem ψ hker)
    simpa only [map_sub, map_pow, map_one] using hmap
  have hregular : e₀ * s ∈ I :=
    Ideal.mul_mem_left I e₀ (Ideal.mem_span_singleton_self s)
  have hcorrection : ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar) *
      (1 - ψ (sectionCofactorElem W ^ p)) ∈ I := by
    have hneg : 1 - ψ (sectionCofactorElem W ^ p) ∈ I := by
      convert I.neg_mem hvp using 1
      ring
    exact Ideal.mul_mem_left I _ hneg
  have hmem : c - ψ (algebraMap K (AdjoinRoot (infChartCubic W)) scalar *
      sectionCofactorElem W ^ p) ∈ I := by
    convert I.add_mem hregular hcorrection using 1
    rw [hc, map_mul]
    ring
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hmem
  refine ⟨scalar, e, ?_⟩
  linear_combination he

private lemma tel_mul_overlapInvT' (W : WeierstrassCurve K) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) * overlapInvT W = 1 := by
  unfold overlapInvT
  rw [Localization.mk_eq_mk', IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [mul_comm]

private lemma tel_mul_overlapXElem' (W : WeierstrassCurve K) :
    algebraMap (AdjoinRoot (infChartCubic W)) (Localization.Away (infChartTElem W))
        (infChartTElem W) * overlapXElem W =
      algebraMap _ _ (AdjoinRoot.root (infChartCubic W)) := by
  unfold overlapXElem
  rw [Localization.mk_eq_mk', IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_eq_iff_eq_mul]
  simp [mul_comm]

private lemma overlapMap_coordX_mul_root_sq_eq_cofactor
    (W : WeierstrassCurve K) :
    overlapMap W (coordX W) *
        algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 2 =
      algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) (sectionCofactorElem W) := by
  let T := algebraMap (AdjoinRoot (infChartCubic W))
    (Localization.Away (infChartTElem W)) (infChartTElem W)
  have hT : IsUnit T := IsLocalization.map_units _
    (⟨infChartTElem W, ⟨1, pow_one _⟩⟩ : Submonoid.powers (infChartTElem W))
  apply hT.mul_left_cancel
  rw [overlapMap_coordX]
  calc
    T * (overlapXElem W * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 2) =
        (T * overlapXElem W) * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 2 := by ring
    _ = algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 3 := by
      rw [tel_mul_overlapXElem']
      ring
    _ = T * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W)) (sectionCofactorElem W) := by
      rw [← map_pow, ← map_mul, tel_mul_sectionCofactorElem]

private lemma overlapMap_coordY_mul_root_cube_eq_cofactor
    (W : WeierstrassCurve K) :
    overlapMap W (coordY W) *
        algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 3 =
      algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) (sectionCofactorElem W) := by
  let T := algebraMap (AdjoinRoot (infChartCubic W))
    (Localization.Away (infChartTElem W)) (infChartTElem W)
  have hT : IsUnit T := IsLocalization.map_units _
    (⟨infChartTElem W, ⟨1, pow_one _⟩⟩ : Submonoid.powers (infChartTElem W))
  apply hT.mul_left_cancel
  rw [overlapMap_coordY]
  calc
    T * (overlapInvT W * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 3) =
        (T * overlapInvT W) * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 3 := by ring
    _ = algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ 3 := by rw [tel_mul_overlapInvT', one_mul]
    _ = T * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W)) (sectionCofactorElem W) := by
      rw [← map_pow, ← map_mul, tel_mul_sectionCofactorElem]

private lemma exists_overlapMap_mul_root_pow_eq_cofactor_pow
    (W : WeierstrassCurve K) (m : ℕ) (hm : 2 ≤ m) :
    ∃ (f : W.toAffine.CoordinateRing) (p : ℕ),
      algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W)) (sectionCofactorElem W) ^ p =
        overlapMap W f * algebraMap (AdjoinRoot (infChartCubic W))
          (Localization.Away (infChartTElem W))
            (AdjoinRoot.root (infChartCubic W)) ^ m := by
  by_cases heven : m % 2 = 0
  · let i := m / 2
    have hm' : m = 2 * i := by omega
    refine ⟨coordX W ^ i, i, ?_⟩
    rw [map_pow (overlapMap W), hm', pow_mul]
    calc
      _ = (overlapMap W (coordX W) *
          algebraMap (AdjoinRoot (infChartCubic W))
            (Localization.Away (infChartTElem W))
              (AdjoinRoot.root (infChartCubic W)) ^ 2) ^ i := by
        rw [overlapMap_coordX_mul_root_sq_eq_cofactor]
      _ = _ := by rw [mul_pow]
  · let i := (m - 3) / 2
    have hm' : m = 2 * i + 3 := by omega
    refine ⟨coordX W ^ i * coordY W, i + 1, ?_⟩
    rw [map_mul (overlapMap W), map_pow (overlapMap W), pow_succ, hm', pow_add, pow_mul]
    calc
      _ = (overlapMap W (coordX W) *
            algebraMap (AdjoinRoot (infChartCubic W))
              (Localization.Away (infChartTElem W))
                (AdjoinRoot.root (infChartCubic W)) ^ 2) ^ i *
          (overlapMap W (coordY W) *
            algebraMap (AdjoinRoot (infChartCubic W))
              (Localization.Away (infChartTElem W))
                (AdjoinRoot.root (infChartCubic W)) ^ 3) := by
        rw [overlapMap_coordX_mul_root_sq_eq_cofactor,
          overlapMap_coordY_mul_root_cube_eq_cofactor]
      _ = _ := by rw [mul_pow]; ring

private lemma exists_projModelPoleCoefficients_add
    (W : WeierstrassCurve K) (n : ℕ) (hn : 1 ≤ n)
    (q : Γ(projModel W, projModelPoleOverlap W)) :
    ∃ (b : Γ(projModel W, projModelSectionNeighborhood W))
        (f : Γ(projModel W, projModelZChart W)),
      (projModel W).presheaf.map
            (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W)).op b +
          (projModel W).presheaf.map
              (homOfLE (projModelPoleOverlap_le_ZChart W)).op f *
            projModelSectionRootOverlap W ^ n = q := by
  let X := projModel W
  let N := projModelSectionNeighborhood W
  let Z := projModelZChart W
  let P := projModelPoleOverlap W
  let r := projModelSectionRoot W
  let resN : Γ(X, N) →+* Γ(X, P) :=
    (X.presheaf.map
      (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W)).op).hom
  let resZ : Γ(X, Z) →+* Γ(X, P) :=
    (X.presheaf.map (homOfLE (projModelPoleOverlap_le_ZChart W)).op).hom
  letI : Algebra Γ(X, N) Γ(X, P) := resN.toAlgebra
  haveI : IsLocalization.Away r Γ(X, P) :=
    N.2.isLocalization_of_eq_basicOpen (f := r)
      (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W))
      (projModelPoleOverlap_eq_basicOpen_sectionRoot W)
  apply exists_add_twisted_of_denominator_step r resZ n ?_ q
  intro c k
  let m := n + k + 1
  have hm : 2 ≤ m := by omega
  obtain ⟨f, p, hfp⟩ := exists_overlapMap_mul_root_pow_eq_cofactor_pow W m hm
  obtain ⟨scalar, e, hc⟩ :=
    exists_projModelSectionNeighborhood_scalar_cofactor_add_root_mul W c p
  let f' := algebraMap K W.toAffine.CoordinateRing scalar * f
  let b' := algebraMap K (AdjoinRoot (infChartCubic W)) scalar *
    sectionCofactorElem W ^ p
  have hb' : algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W)) b' =
      overlapMap W f' * algebraMap (AdjoinRoot (infChartCubic W))
        (Localization.Away (infChartTElem W))
          (AdjoinRoot.root (infChartCubic W)) ^ m := by
    dsimp only [b', f']
    rw [map_mul, map_pow, map_mul, overlapMap_algebraMap, hfp]
    rw [IsScalarTower.algebraMap_apply K (AdjoinRoot (infChartCubic W))
      (Localization.Away (infChartTElem W))]
    ring
  have hcompat := projModelPoleCoefficients_compatible W m f' b' hb'
  have hψ (z : AdjoinRoot (infChartCubic W)) :
      projModelSectionNeighborhoodMap W z =
        (X.presheaf.map
          (homOfLE (X.affineBasicOpen_le (projModelSectionUnitSection W))).op).hom
            ((chartYSectionsRingEquiv W).symm z) := rfl
  refine ⟨(chartZSectionsRingEquiv W).symm f', e, ?_⟩
  change resN c = resZ ((chartZSectionsRingEquiv W).symm f') *
      resN r ^ (n + k + 1) + resN (e * r)
  rw [hc, map_add]
  have hcompat' : resN
        ((X.presheaf.map
            (homOfLE (X.affineBasicOpen_le (projModelSectionUnitSection W))).op).hom
              ((chartYSectionsRingEquiv W).symm
                (algebraMap K (AdjoinRoot (infChartCubic W)) scalar)) *
          (X.presheaf.map
            (homOfLE (X.affineBasicOpen_le (projModelSectionUnitSection W))).op).hom
              ((chartYSectionsRingEquiv W).symm (sectionCofactorElem W)) ^ p) =
      resZ ((chartZSectionsRingEquiv W).symm f') * resN r ^ m := by
    dsimp only [b'] at hcompat
    simp only [map_mul, map_pow] at hcompat
    simpa only [resN, resZ, r, X, N, P, projModelSectionRootOverlap] using hcompat
  have hlead : resN
        (projModelSectionNeighborhoodMap W
          (algebraMap K (AdjoinRoot (infChartCubic W)) scalar *
            sectionCofactorElem W ^ p)) =
      resZ ((chartZSectionsRingEquiv W).symm f') * resN r ^ m := by
    rw [map_mul, map_pow, hψ, hψ]
    exact hcompat'
  calc
    resN
          (projModelSectionNeighborhoodMap W
            (algebraMap K (AdjoinRoot (infChartCubic W)) scalar *
              sectionCofactorElem W ^ p)) +
        resN (e * projModelSectionRoot W) =
      (resZ ((chartZSectionsRingEquiv W).symm f') * resN r ^ m) +
        resN (e * r) := congrArg (· + resN (e * r)) hlead
    _ = _ := by rfl

private lemma overTrivializationSection_of_coefficient
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, U)) :
    overTrivializationSection M U e
        (e.hom.val.app (.op (Over.mk (𝟙 U))) m) = m := by
  unfold overTrivializationSection
  have hcomp := congrArg
    (fun q => q.val.app (.op (Over.mk (𝟙 U)))) e.hom_inv_id
  exact ConcreteCategory.congr_hom hcomp m

/-- Every overlap section of `O(n[0])`, for `n >= 1`, is the difference of a section
on the canonical section neighborhood and a section on the affine `Z`-chart. -/
theorem exists_projModelPoleLocalSections_sub_eq
    (W : WeierstrassCurve K) (n : ℕ) (hn : 1 ≤ n)
    (a : Γ(sectionPoleSheafPower (projModelπ W) (projModelZero W)
      (projModelZero_projModelπ W) n, projModelPoleOverlap W)) :
    ∃ (aN : Γ(sectionPoleSheafPower (projModelπ W) (projModelZero W)
          (projModelZero_projModelπ W) n, projModelSectionNeighborhood W))
      (aZ : Γ(sectionPoleSheafPower (projModelπ W) (projModelZero W)
          (projModelZero_projModelπ W) n, projModelZChart W)),
      (sectionPoleSheafPower (projModelπ W) (projModelZero W)
          (projModelZero_projModelπ W) n).presheaf.map
            (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W)).op aN -
        (sectionPoleSheafPower (projModelπ W) (projModelZero W)
          (projModelZero_projModelπ W) n).presheaf.map
            (homOfLE (projModelPoleOverlap_le_ZChart W)).op aZ = a := by
  let X := projModel W
  let M := sectionPoleSheafPower (projModelπ W) (projModelZero W)
    (projModelZero_projModelπ W) n
  let N := projModelSectionNeighborhood W
  let Z := projModelZChart W
  let P := projModelPoleOverlap W
  let eN := projModelSectionPoleSheafPowerOverTrivialization W n
  let eZ := projModelSectionPoleSheafPowerOverTrivializationZ W n
  let eP := projModelSectionPolePowerOverlapOverTrivialization W n
  let ePZ := projModelSectionPolePowerOverlapOverTrivializationZ W n
  let q : Γ(X, P) := eP.hom.val.app (.op (Over.mk (𝟙 P))) a
  obtain ⟨b, f, hbf⟩ := exists_projModelPoleCoefficients_add W n hn q
  let aN : Γ(M, N) := overTrivializationSection M N eN b
  let aZ : Γ(M, Z) := overTrivializationSection M Z eZ (-f)
  refine ⟨aN, aZ, ?_⟩
  have hZ : overTrivializationSection M P eP
        ((X.presheaf.map (homOfLE (projModelPoleOverlap_le_ZChart W)).op (-f)) *
          projModelSectionRootOverlap W ^ n) =
      overTrivializationSection M P ePZ
        (X.presheaf.map (homOfLE (projModelPoleOverlap_le_ZChart W)).op (-f)) := by
    apply overTrivializationSection_eq_of_transition M P eP ePZ
      (projModelSectionRootOverlap W ^ n)
    · exact projModelSectionPolePowerOverlapOver_transition W n
    · rfl
  have hcoeff :
      X.presheaf.map
          (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W)).op b -
        X.presheaf.map (homOfLE (projModelPoleOverlap_le_ZChart W)).op (-f) *
          projModelSectionRootOverlap W ^ n = q := by
    rw [map_neg, neg_mul, sub_neg_eq_add]
    exact hbf
  dsimp only [aN, aZ]
  rw [overTrivializationSection_restrict, overTrivializationSection_restrict]
  rw [projModelSectionPoleSheafPowerOverTrivialization_restrict,
    projModelSectionPoleSheafPowerOverTrivializationZ_restrict]
  rw [← hZ]
  let bP := X.presheaf.map
    (homOfLE (projModelPoleOverlap_le_sectionNeighborhood W)).op b
  let fP := X.presheaf.map (homOfLE (projModelPoleOverlap_le_ZChart W)).op (-f) *
    projModelSectionRootOverlap W ^ n
  change overTrivializationSection M P eP bP -
      overTrivializationSection M P eP fP = a
  have hMapSub :
      overTrivializationSection M P eP bP -
          overTrivializationSection M P eP fP =
        overTrivializationSection M P eP (bP - fP) := by
    exact ((eP.inv.val.app (.op (Over.mk (𝟙 P)))).hom.map_sub bP fP).symm
  have hCoefficient : bP - fP = q := by
    exact hcoeff
  have hApplyCoefficient :
      overTrivializationSection M P eP (bP - fP) =
        overTrivializationSection M P eP q :=
    congrArg (overTrivializationSection M P eP) hCoefficient
  have hInverse : overTrivializationSection M P eP q = a :=
    overTrivializationSection_of_coefficient M P eP a
  exact hMapSub.trans <| hApplyCoefficient.trans hInverse

/-- Over a field, `H^1(O(n[0]))` vanishes on a projective Weierstrass model for every
`n >= 1`. -/
theorem sectionPoleSheafPower_projModel_subsingleton_H_one
    (W : WeierstrassCurve K) (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower (projModelπ W) (projModelZero W)
        (projModelZero_projModelπ W) n).sheaf 1) := by
  let M := sectionPoleSheafPower (projModelπ W) (projModelZero W)
    (projModelZero_projModelπ W) n
  let N := projModelSectionNeighborhood W
  let Z := projModelZChart W
  apply TopCat.Sheaf.subsingleton_H_one_of_two_open_cover M.sheaf N Z
  · rw [sup_comm]
    exact projModelZChart_sup_sectionNeighborhood_eq_top W
  · change Subsingleton (CategoryTheory.Sheaf.H (M.restrict N.1.ι).sheaf 1)
    letI : IsAffine N.1.toScheme := N.2
    letI : (M.restrict N.1.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent N.1.toScheme.ringCatSheaf).prop_of_iso
        (projModelSectionPoleSheafPowerTrivialization W n).symm
        (Scheme.Modules.isInvertible_unit (X := N.1.toScheme)).isQuasicoherent
    exact Scheme.Modules.affine_subsingleton_H (M.restrict N.1.ι) 0
  · change Subsingleton (CategoryTheory.Sheaf.H (M.restrict Z.1.ι).sheaf 1)
    letI : IsAffine Z.1.toScheme := Z.2
    letI : (M.restrict Z.1.ι).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent Z.1.toScheme.ringCatSheaf).prop_of_iso
        (projModelSectionPoleSheafPowerTrivializationZ W n).symm
        (Scheme.Modules.isInvertible_unit (X := Z.1.toScheme)).isQuasicoherent
    exact Scheme.Modules.affine_subsingleton_H (M.restrict Z.1.ι) 0
  · intro a
    change Γ(M, N ⊓ Z) at a
    obtain ⟨aN, aZ, ha⟩ := exists_projModelPoleLocalSections_sub_eq W n hn a
    exact ⟨aN, aZ, ha⟩
end ModularCurves
