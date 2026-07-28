/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.ProjMapClosedImmersion
import ModularCurves.ForMathlib.SegreProductStandardCover
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Coefficient base change for polynomial projective space

Polynomial projective space commutes with extension of its coefficient ring. The proof identifies
each standard projective chart with a polynomial ring and uses the scalar-extension equivalence for
multivariate polynomial rings.
-/

open CategoryTheory Limits AlgebraicGeometry
open HomogeneousIdeal HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra
local instance (priority := 10000) {n : ℕ} : DecidableEq (Fin n) :=
  Classical.decEq _

/-- Coefficient extension on homogeneous polynomial rings, preserving the standard grading. -/
noncomputable abbrev coefficientGradedHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    homogeneousSubmodule (Fin (d + 1)) k →+*ᵍ
      homogeneousSubmodule (Fin (d + 1)) R where
  toRingHom := MvPolynomial.map φ
  map_mem := fun hp => MvPolynomial.IsHomogeneous.map hp φ

@[simp]
lemma coefficientGradedHom_X
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1)) :
    coefficientGradedHom φ d (X i) = X i := by
  change MvPolynomial.map φ (X i) = X i
  exact MvPolynomial.map_X φ i

/-- Coefficient extension satisfies the irrelevant-ideal hypothesis required by `Proj.map`. -/
lemma coefficientIrrelevantLE
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    (homogeneousSubmodule (Fin (d + 1)) R)₊ ≤
      (homogeneousSubmodule (Fin (d + 1)) k)₊.map
        (coefficientGradedHom φ d) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn p hp
  have hpIrrelevant :
      p ∈ (homogeneousSubmodule (Fin (d + 1)) R)₊.toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin (d + 1)) R) hn hp
  have hpSpan :
      p ∈ Ideal.span
        (Set.range
          (X : Fin (d + 1) → MvPolynomial (Fin (d + 1)) R)) :=
    irrelevant_toIdeal_le_span_range_X hpIrrelevant
  refine (Ideal.span_le.2 ?_) hpSpan
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  rw [← coefficientGradedHom_X φ i]
  exact Ideal.mem_map_of_mem
    (coefficientGradedHom φ d)
    (HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule (Fin (d + 1)) k)
      Nat.zero_lt_one
      (X_mem_homogeneousSubmodule_one k i))

/-- The morphism from projective space after coefficient extension to the original projective
space. -/
def coefficientMap
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) :
    Proj (homogeneousSubmodule (Fin (d + 1)) R) ⟶
      Proj (homogeneousSubmodule (Fin (d + 1)) k) :=
  Proj.map (coefficientGradedHom φ d) (coefficientIrrelevantLE φ d)

/-- The standard coordinate chart is preserved by coefficient extension. -/
@[simp]
lemma coefficientMap_preimage_coordinateOpen
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) (d : ℕ) (i : Fin (d + 1)) :
    coefficientMap φ d ⁻¹ᵁ coordinateOpen (R := k) i =
      coordinateOpen (R := R) i := by
  simpa only [coefficientMap, coordinateOpen, coefficientGradedHom_X] using
    (Proj.map_preimage_basicOpen
      (coefficientGradedHom φ d)
      (coefficientIrrelevantLE φ d)
      (X i))

/-- Coefficient extension on a standard projective chart. -/
noncomputable abbrev coefficientChartRingHom
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway k i →+* ProjectiveCoordinateAway R i :=
  (ModularCurves.awayCongr
      (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
      (MvPolynomial.map_X φ i)).toRingHom.comp
    (Away.map (coefficientGradedHom φ d) (X i))

/-- Coefficient extension on a standard chart commutes with homogenization. -/
lemma coefficientChartRingHom_homogenizeAt
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1))
    (p : MvPolynomial {j : Fin (d + 1) // j ≠ i} k) :
    coefficientChartRingHom φ i (homogenizeAt k i p) =
      homogenizeAt R i (MvPolynomial.map φ p) :=
  (homogenizeAt_map k φ i p).symm

private lemma dehomogenizeAt_homogenizeAt
    (A : Type u) [CommRing A] {d : ℕ} (i : Fin (d + 1))
    (p : MvPolynomial {j : Fin (d + 1) // j ≠ i} A) :
    dehomogenizeAt A i (homogenizeAt A i p) = p := by
  change ((dehomogenizeAt A i).comp (homogenizeAt A i)) p = p
  rw [dehomogenizeAt_comp_homogenizeAt]
  rfl

/-- Coefficient extension on a standard chart commutes with dehomogenization. -/
lemma coefficientChartRingHom_dehomogenizeAt
    {k R : Type u} [CommRing k] [CommRing R]
    (φ : k →+* R) {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway k i) :
    dehomogenizeAt R i (coefficientChartRingHom φ i x) =
      MvPolynomial.map φ (dehomogenizeAt k i x) := by
  obtain ⟨p, rfl⟩ := (chartRingEquiv k i).symm.surjective x
  change dehomogenizeAt R i
      (coefficientChartRingHom φ i (homogenizeAt k i p)) =
    MvPolynomial.map φ (dehomogenizeAt k i (homogenizeAt k i p))
  rw [coefficientChartRingHom_homogenizeAt]
  rw [dehomogenizeAt_homogenizeAt, dehomogenizeAt_homogenizeAt]

private lemma chartRingEquiv_apply
    (A : Type u) [CommRing A] {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway A i) :
    chartRingEquiv A i x = dehomogenizeAt A i x :=
  rfl

/-- The standard projective chart equivalence as an algebra homomorphism. -/
noncomputable def coordinateChartAlgHom
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway R i →ₐ[R]
      MvPolynomial {j : Fin (d + 1) // j ≠ i} R where
  toRingHom := (chartRingEquiv R i).toRingHom
  commutes' := by
    intro r
    calc
      chartRingEquiv R i
          (algebraMap R (ProjectiveCoordinateAway R i) r) = C r :=
        chartRingEquiv_algebraMap (R := R) i r
      _ = algebraMap R
          (MvPolynomial {j : Fin (d + 1) // j ≠ i} R) r := by
        rw [MvPolynomial.algebraMap_apply]
        simp

private lemma coordinateChartAlgHom_bijective
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    Function.Bijective (coordinateChartAlgHom R i) :=
  (chartRingEquiv R i).bijective

/-- The standard projective chart equivalence as an algebra equivalence. -/
noncomputable def coordinateChartAlgEquiv
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1)) :
    ProjectiveCoordinateAway R i ≃ₐ[R]
      MvPolynomial {j : Fin (d + 1) // j ≠ i} R :=
  AlgEquiv.ofBijective
    (coordinateChartAlgHom R i)
    (coordinateChartAlgHom_bijective R i)

@[simp]
lemma coordinateChartAlgEquiv_apply
    (R : Type u) [CommRing R] {d : ℕ} (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway R i) :
    coordinateChartAlgEquiv R i x = chartRingEquiv R i x :=
  rfl

/-- The scalar extension of a standard projective chart ring is the corresponding chart ring over
the new coefficient ring. -/
noncomputable def coefficientChartTensorAlgEquiv
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    R ⊗[k] ProjectiveCoordinateAway k i ≃ₐ[R]
      ProjectiveCoordinateAway R i :=
  (Algebra.TensorProduct.congr
      (AlgEquiv.refl)
      (coordinateChartAlgEquiv k i)).trans
    ((MvPolynomial.algebraTensorAlgEquiv k R).trans
      (coordinateChartAlgEquiv R i).symm)

/-- The chart scalar-extension equivalence agrees with the coefficient map on its left factor. -/
lemma coefficientChartTensorAlgEquiv_comp_includeLeft
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    (coefficientChartTensorAlgEquiv k R i).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          R →+* R ⊗[k] ProjectiveCoordinateAway k i) =
      algebraMap R (ProjectiveCoordinateAway R i) := by
  apply RingHom.ext
  intro r
  change coefficientChartTensorAlgEquiv k R i (r ⊗ₜ[k] 1) =
    algebraMap R (ProjectiveCoordinateAway R i) r
  simp only [coefficientChartTensorAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    AlgEquiv.refl_toAlgHom, AlgHom.id_apply, map_one,
    MvPolynomial.algebraTensorAlgEquiv_tmul]
  rw [show r • (1 : MvPolynomial {j : Fin (d + 1) // j ≠ i} R) =
      algebraMap R _ r by rw [Algebra.smul_def, mul_one]]
  exact (coordinateChartAlgEquiv R i).symm.commutes r

/-- The chart scalar-extension equivalence agrees with coefficient extension on its right factor. -/
lemma coefficientChartTensorAlgEquiv_comp_includeRight
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    (coefficientChartTensorAlgEquiv k R i).toRingHom.comp
        (Algebra.TensorProduct.includeRight :
          ProjectiveCoordinateAway k i →ₐ[k]
            R ⊗[k] ProjectiveCoordinateAway k i).toRingHom =
      coefficientChartRingHom (algebraMap k R) i := by
  apply RingHom.ext
  intro x
  apply (coordinateChartAlgEquiv R i).injective
  change coordinateChartAlgEquiv R i
      (coefficientChartTensorAlgEquiv k R i (1 ⊗ₜ[k] x)) =
    coordinateChartAlgEquiv R i
      (coefficientChartRingHom (algebraMap k R) i x)
  rw [coordinateChartAlgEquiv_apply R i
    (coefficientChartRingHom (algebraMap k R) i x)]
  rw [chartRingEquiv_apply]
  rw [coefficientChartRingHom_dehomogenizeAt]
  simp [coefficientChartTensorAlgEquiv]
  rw [chartRingEquiv_apply]

/-- Coefficient extension on a projective chart respects the coefficient embeddings. -/
lemma coefficientChartRingHom_algebraMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) (r : k) :
    coefficientChartRingHom (algebraMap k R) i
        (algebraMap k (ProjectiveCoordinateAway k i) r) =
      algebraMap R (ProjectiveCoordinateAway R i) (algebraMap k R r) := by
  apply (chartRingEquiv R i).injective
  rw [chartRingEquiv_apply]
  rw [coefficientChartRingHom_dehomogenizeAt]
  have hk :
      dehomogenizeAt k i
          (algebraMap k (ProjectiveCoordinateAway k i) r) = C r := by
    rw [← chartRingEquiv_apply]
    exact chartRingEquiv_algebraMap (R := k) i r
  rw [hk, MvPolynomial.map_C]
  exact (chartRingEquiv_algebraMap (R := R) i (algebraMap k R r)).symm

/-- The affine square on a standard projective chart is cartesian. -/
lemma isPullback_coefficientChart
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    {d : ℕ} (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (ProjectiveCoordinateAway R i))))
      (Spec.map
        (CommRingCat.ofHom
          (coefficientChartRingHom (algebraMap k R) i)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap k (ProjectiveCoordinateAway k i)))) := by
  let tensorMap :=
    (coefficientChartTensorAlgEquiv k R i).toRingHom
  letI : IsIso (CommRingCat.ofHom tensorMap) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (coefficientChartTensorAlgEquiv k R i).bijective
  let e :
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) ≅
        pullback
          (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          (Spec.map
            (CommRingCat.ofHom
              (algebraMap k (ProjectiveCoordinateAway k i)))) :=
    asIso (Spec.map (CommRingCat.ofHom tensorMap)) ≪≫
      (pullbackSpecIso k R (ProjectiveCoordinateAway k i)).symm
  apply IsPullback.of_iso_pullback _ e
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_fst, asIso_hom, ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientChartTensorAlgEquiv_comp_includeLeft k R i)
  · dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackSpecIso_inv_snd, asIso_hom, ← Spec.map_comp]
    dsimp only [tensorMap]
    rw [← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f => Spec.map (CommRingCat.ofHom f))
      (coefficientChartTensorAlgEquiv_comp_includeRight k R i)
  · constructor
    simp only [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    apply RingHom.ext
    intro r
    exact (coefficientChartRingHom_algebraMap k R i r).symm

/-- The coefficient-extension map restricts on each standard chart to
`coefficientChartRingHom`. -/
private lemma Spec_map_awayCongr_awayι
    {R₀ B : Type u} [CommRing R₀] [CommRing B] [Algebra R₀ B]
    (𝒜 : ℕ → Submodule R₀ B) [GradedAlgebra 𝒜]
    {s t : B} (h : s = t) {m : ℕ} (hs : s ∈ 𝒜 m) (hm : 0 < m) :
    Spec.map
          (CommRingCat.ofHom
            (ModularCurves.awayCongr (𝒜 := 𝒜) h).toRingHom) ≫
        Proj.awayι 𝒜 s hs hm =
      Proj.awayι 𝒜 t (h ▸ hs) hm := by
  subst h
  rw [show
    (ModularCurves.awayCongr (𝒜 := 𝒜) (rfl : s = s)).toRingHom =
        RingHom.id _ by
      rw [ModularCurves.awayCongr_rfl, RingEquiv.toRingHom_refl]]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

lemma isPullback_coefficientChart_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (d : ℕ) (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (coefficientChartRingHom (algebraMap k R) i)))
      (coordinateChartMap R (Fin (d + 1)) i)
      (coordinateChartMap k (Fin (d + 1)) i)
      (coefficientMap (algebraMap k R) d) := by
  apply IsOpenImmersion.isPullback
  · let f := coefficientGradedHom (algebraMap k R) d
    let hX : f (X i) = X i :=
      coefficientGradedHom_X (algebraMap k R) i
    calc
      coordinateChartMap R (Fin (d + 1)) i ≫
          coefficientMap (algebraMap k R) d =
        (Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            Proj.awayι
              (homogeneousSubmodule (Fin (d + 1)) R)
              (f (X i))
              (GradedRingHom.map_mem f
                (X_mem_homogeneousSubmodule_one k i))
              Nat.zero_lt_one) ≫
          coefficientMap (algebraMap k R) d := by
            rw [Spec_map_awayCongr_awayι]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            (Proj.awayι
                (homogeneousSubmodule (Fin (d + 1)) R)
                (f (X i))
                (GradedRingHom.map_mem f
                  (X_mem_homogeneousSubmodule_one k i))
                Nat.zero_lt_one ≫
              coefficientMap (algebraMap k R) d) := by
                rw [Category.assoc]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (ModularCurves.awayCongr
                  (𝒜 := homogeneousSubmodule (Fin (d + 1)) R)
                  hX).toRingHom) ≫
            (Spec.map (CommRingCat.ofHom (Away.map f (X i))) ≫
              coordinateChartMap k (Fin (d + 1)) i) := by
                change _ ≫
                    (Proj.awayι _ (f (X i)) _ _ ≫
                      Proj.map f
                        (coefficientIrrelevantLE (algebraMap k R) d)) =
                  _
                rw [Proj.awayι_comp_map]
      _ =
        Spec.map
              (CommRingCat.ofHom
                (coefficientChartRingHom (algebraMap k R) i)) ≫
            coordinateChartMap k (Fin (d + 1)) i := by
              rw [← Category.assoc, ← Spec.map_comp,
                ← CommRingCat.ofHom_comp]
  · rw [coordinateAffineOpenCover_opensRange,
      coordinateAffineOpenCover_opensRange]
    exact coefficientMap_preimage_coordinateOpen
      (algebraMap k R) d i

/-- Polynomial projective space commutes with extension of its coefficient ring. -/
theorem isPullback_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (d : ℕ) :
    IsPullback
      (coefficientMap (algebraMap k R) d)
      (homogeneousProjπ (R := R) (σ := Fin (d + 1)))
      (homogeneousProjπ (R := k) (σ := Fin (d + 1)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) := by
  apply Scheme.isPullback_of_openCover
    (coefficientMap (algebraMap k R) d)
    (homogeneousProjπ (R := R) (σ := Fin (d + 1)))
    (homogeneousProjπ (R := k) (σ := Fin (d + 1)))
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (coordinateOpenCover k (Fin (d + 1)))
  rintro (i : Fin (d + 1))
  let global := coefficientMap (algebraMap k R) d
  let toBaseR := homogeneousProjπ (R := R) (σ := Fin (d + 1))
  let toBaseK := homogeneousProjπ (R := k) (σ := Fin (d + 1))
  let base := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let chartMap :=
    Spec.map
      (CommRingCat.ofHom
        (coefficientChartRingHom (algebraMap k R) i))
  have hChart :
      IsPullback chartMap
        (coordinateChartMap R (Fin (d + 1)) i)
        (coordinateChartMap k (Fin (d + 1)) i)
        global :=
    isPullback_coefficientChart_coefficientMap k R d i
  have hLocal :
      IsPullback
        chartMap
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))))
        (Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k i))))
        base :=
    (isPullback_coefficientChart k R i).flip
  let e :
      Spec (CommRingCat.of (ProjectiveCoordinateAway R i)) ≅
        ((coordinateOpenCover k (Fin (d + 1))).pullback₁ global).X i :=
    hChart.isoPullback ≪≫
      pullbackSymmetry
        (coordinateChartMap k (Fin (d + 1)) i) global
  have e_snd :
      e.hom ≫
          pullback.snd global
            (coordinateChartMap k (Fin (d + 1)) i) =
        chartMap := by
    change
      (hChart.isoPullback.hom ≫
          (pullbackSymmetry
            (coordinateChartMap k (Fin (d + 1)) i) global).hom) ≫
        pullback.snd global
          (coordinateChartMap k (Fin (d + 1)) i) =
      chartMap
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
      hChart.isoPullback_hom_fst]
  have e_fst :
      e.hom ≫
          pullback.fst global
            (coordinateChartMap k (Fin (d + 1)) i) =
        coordinateChartMap R (Fin (d + 1)) i := by
    change
      (hChart.isoPullback.hom ≫
          (pullbackSymmetry
            (coordinateChartMap k (Fin (d + 1)) i) global).hom) ≫
        pullback.fst global
          (coordinateChartMap k (Fin (d + 1)) i) =
      coordinateChartMap R (Fin (d + 1)) i
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      hChart.isoPullback_hom_snd]
  refine hLocal.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change chartMap =
      e.hom ≫
        pullback.snd global
          (coordinateChartMap k (Fin (d + 1)) i)
    exact e_snd.symm
  · change
      Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))) =
        e.hom ≫
          pullback.fst global
              (coordinateChartMap k (Fin (d + 1)) i) ≫
            toBaseR
    calc
      Spec.map
          (CommRingCat.ofHom
            (algebraMap R (ProjectiveCoordinateAway R i))) =
          coordinateChartMap R (Fin (d + 1)) i ≫ toBaseR :=
        (coordinateAffineOpenCover_comp_homogeneousProjπ
          R (Fin (d + 1)) i).symm
      _ =
          (e.hom ≫
              pullback.fst global
                (coordinateChartMap k (Fin (d + 1)) i)) ≫
            toBaseR :=
        congrArg (fun q => q ≫ toBaseR) e_fst.symm
      _ =
          e.hom ≫
            pullback.fst global
                (coordinateChartMap k (Fin (d + 1)) i) ≫
              toBaseR :=
        Category.assoc _ _ _
  · change
      Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k i))) =
        coordinateChartMap k (Fin (d + 1)) i ≫ toBaseK
    exact
      (coordinateAffineOpenCover_comp_homogeneousProjπ
        k (Fin (d + 1)) i).symm
  · change base = base
    rfl

end MvPolynomial
