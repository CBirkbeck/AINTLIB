/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-A2d.
-/
import ModularCurves.ForMathlib.GradedQuotient
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# `Proj` of a quotient grading is a closed subscheme of `Proj`

For a homogeneous ideal `I` of a graded algebra `𝒜`, the morphism
`Proj.map (quotientGradingHom I) : Proj (𝒜/I) ⟶ Proj 𝒜` is a closed immersion:
closed immersions are Zariski-local on the target, over each basic open `D₊(s)` the
map is `Spec` of `Away.map (quotientGradingHom I) s`, and that ring map is surjective
because the quotient grading consists of images.
-/

namespace HomogeneousIdeal

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)

theorem away_map_quotientGradingHom_surjective {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map (quotientGradingHom I) s) := by
  intro z
  obtain ⟨n, a', ha', rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective _ (mk_mem_quotientGrading I hs) z
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp ha'
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs n a ha, ?_⟩
  rw [Away.map_mk]
  rfl

variable {I} in
private theorem mem_span_sigma_of_mem_irrelevant {z : A}
    (hz : z ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    z ∈ Ideal.span (Set.range fun x : Σ i : ℕ+, 𝒜 i => (x.2 : A)) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c _ => ?_
  by_cases hc0 : c = 0
  · subst hc0
    have hz0 : GradedRing.proj 𝒜 0 z = 0 := hz
    rw [GradedRing.proj_apply] at hz0
    rw [hz0]
    exact zero_mem _
  · exact Ideal.subset_span
      ⟨⟨⟨c, Nat.pos_of_ne_zero hc0⟩, DirectSum.decompose 𝒜 z c⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- **`Proj` of a quotient is a closed subscheme**: the morphism induced by the quotient
map on a homogeneous ideal is a closed immersion. -/
theorem isClosedImmersion_proj_map_quotientGradingHom :
    IsClosedImmersion (Proj.map (quotientGradingHom I)
      (quotientGradingHom_irrelevant_le I)) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (Proj.iSup_basicOpen_eq_top 𝒜 (fun x : Σ i : ℕ+, 𝒜 i => (x.2 : A))
      fun _ hz => mem_span_sigma_of_mem_irrelevant hz)]
  rintro ⟨i, t, ht⟩
  have hi : 0 < (i : ℕ) := i.2
  have hcomm := Proj.awayι_comp_map (quotientGradingHom I)
    (quotientGradingHom_irrelevant_le I) hi t ht
  -- unfold both `awayι`s and cancel the (mono) open immersion of the target open
  rw [← Proj.basicOpenIsoSpec_inv_ι, ← Proj.basicOpenIsoSpec_inv_ι,
    Category.assoc] at hcomm
  have hres : (Proj.basicOpen (quotientGrading I) (quotientGradingHom I t)).ι ≫
      Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) =
      (Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) ∣_
        Proj.basicOpen 𝒜 t) ≫ (Proj.basicOpen 𝒜 t).ι := by
    rw [morphismRestrict_ι]
    rfl
  rw [hres] at hcomm
  -- hcomm : isoQ.inv ≫ (g ∣_ U) ≫ U.ι = Spec.map (Away.map …) ≫ iso𝒜.inv ≫ U.ι
  rw [← Category.assoc, ← Category.assoc] at hcomm
  replace hcomm := (cancel_mono (Proj.basicOpen 𝒜 t).ι).mp hcomm
  -- hcomm : isoQ.inv ≫ (g ∣_ U) = Spec.map (Away.map …) ≫ iso𝒜.inv
  have key : (Proj.map (quotientGradingHom I) (quotientGradingHom_irrelevant_le I) ∣_
      Proj.basicOpen 𝒜 t) =
      (Proj.basicOpenIsoSpec (quotientGrading I) (quotientGradingHom I t)
          (mk_mem_quotientGrading I ht) hi).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (quotientGradingHom I) t)) ≫
        (Proj.basicOpenIsoSpec 𝒜 t ht hi).inv := by
    rw [← Iso.inv_comp_eq]
    exact hcomm
  rw [key]
  haveI h1 : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Away.map (quotientGradingHom I) t))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_quotientGradingHom_surjective I ht)
  haveI h2 : IsClosedImmersion ((Proj.basicOpenIsoSpec 𝒜 t ht hi).inv) := inferInstance
  haveI h3 : IsClosedImmersion ((Proj.basicOpenIsoSpec (quotientGrading I)
      (quotientGradingHom I t) (mk_mem_quotientGrading I ht) hi).hom) := inferInstance
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ h3
    (MorphismProperty.IsStableUnderComposition.comp_mem _ _ h1 h2)

end HomogeneousIdeal
