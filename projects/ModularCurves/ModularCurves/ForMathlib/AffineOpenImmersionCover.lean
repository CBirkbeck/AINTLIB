import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import ModularCurves.ForMathlib.FinitePresentationFunctorCover

/-!
# Detecting affine open immersions on principal covers

An affine morphism is an open immersion when finitely many target functions pull
back to a principal cover of its source and the morphism is an isomorphism on each
corresponding principal open. This criterion retains exactly the finite data that can
be transported through a filtered approximation.
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {R S : Type u} [CommRing R] [CommRing S]

private lemma primeSpectrum_comap_injective_of_awayCover
    (f : R →+* S) {κ : Type u} [Finite κ] (r : κ → R)
    (hspan : Ideal.span (Set.range fun k => f (r k)) = ⊤)
    (hmap : ∀ k, Function.Surjective
      (IsLocalization.Away.map (Localization.Away (r k))
        (Localization.Away (f (r k))) f (r k))) :
    Function.Injective (PrimeSpectrum.comap f) := by
  intro x y hxy
  have hx : ∃ k, f (r k) ∉ x.asIdeal := by
    by_contra! h
    apply x.2.ne_top
    rw [← top_le_iff, ← hspan, Ideal.span_le, Set.range_subset_iff]
    exact h
  obtain ⟨k, hxk⟩ := hx
  have hyk : f (r k) ∉ y.asIdeal := by
    intro hyk
    apply hxk
    have hyr : r k ∈ (PrimeSpectrum.comap f y).asIdeal := hyk
    rw [← hxy] at hyr
    exact hyr
  have hxrange : x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap S (Localization.Away (f (r k))))) := by
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (f (r k))) (f (r k))]
    exact hxk
  have hyrange : y ∈ Set.range (PrimeSpectrum.comap
      (algebraMap S (Localization.Away (f (r k))))) := by
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (f (r k))) (f (r k))]
    exact hyk
  obtain ⟨x', rfl⟩ := hxrange
  obtain ⟨y', rfl⟩ := hyrange
  let g := IsLocalization.Away.map (Localization.Away (r k))
    (Localization.Away (f (r k))) f (r k)
  have hcomp : (algebraMap S (Localization.Away (f (r k)))).comp f =
      g.comp (algebraMap R (Localization.Away (r k))) := by
    ext a
    simp [g, IsLocalization.Away.map]
  have hxy' :
      PrimeSpectrum.comap (algebraMap R (Localization.Away (r k)))
          (PrimeSpectrum.comap g x') =
        PrimeSpectrum.comap (algebraMap R (Localization.Away (r k)))
          (PrimeSpectrum.comap g y') := by
    change PrimeSpectrum.comap
      ((algebraMap S (Localization.Away (f (r k)))).comp f) x' =
        PrimeSpectrum.comap
          ((algebraMap S (Localization.Away (f (r k)))).comp f) y' at hxy
    rw [hcomp] at hxy
    exact hxy
  have hlocal : PrimeSpectrum.comap g x' = PrimeSpectrum.comap g y' :=
    PrimeSpectrum.localization_comap_injective
      (Localization.Away (r k)) (Submonoid.powers (r k)) hxy'
  have hpoints : x' = y' :=
    PrimeSpectrum.comap_injective_of_surjective g (hmap k) hlocal
  exact congrArg (PrimeSpectrum.comap
    (algebraMap S (Localization.Away (f (r k))))) hpoints

/-- A ring map induces an open immersion on spectra if finitely many target
functions pull back to a principal cover of the source and every induced map on
the corresponding principal localizations is bijective. -/
theorem isOpenImmersion_SpecMap_of_awayCover
    (f : R →+* S) {κ : Type u} [Finite κ] (r : κ → R)
    (hspan : Ideal.span (Set.range fun k => f (r k)) = ⊤)
    (hmap : ∀ k, Function.Bijective
      (IsLocalization.Away.map (Localization.Away (r k))
        (Localization.Away (f (r k))) f (r k))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  let 𝒰 := Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of S) (fun k => f (r k)) hspan
  apply IsOpenImmersion.of_openCover_source _ 𝒰.openCover
  · change Function.Injective (PrimeSpectrum.comap f)
    exact primeSpectrum_comap_injective_of_awayCover f r hspan fun k => (hmap k).2
  · intro k
    haveI : IsIso (CommRingCat.ofHom
        (IsLocalization.Away.map (Localization.Away (r k))
          (Localization.Away (f (r k))) f (r k))) :=
      (RingEquiv.toCommRingCatIso (RingEquiv.ofBijective _ (hmap k))).isIso_hom
    change IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
          (algebraMap S (Localization.Away (f (r k))))) ≫
        Spec.map (CommRingCat.ofHom f))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (algebraMap S (Localization.Away (f (r k)))).comp f =
        (IsLocalization.Away.map (Localization.Away (r k))
          (Localization.Away (f (r k))) f (r k)).comp
            (algebraMap R (Localization.Away (r k))) by
      ext x
      simp [IsLocalization.Away.map]]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance

end AlgebraicGeometry
