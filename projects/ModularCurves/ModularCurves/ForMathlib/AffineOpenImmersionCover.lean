import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
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

/-- An open immersion between affine schemes admits finitely many target basic opens
covering its image. Their pullbacks cover the source, and the induced maps between
the corresponding principal localizations are bijective. -/
theorem Scheme.Hom.exists_awayCover_of_isOpenImmersion
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsOpenImmersion f] :
    ∃ (κ : Type u) (_ : Finite κ) (r : κ → Γ(Y, ⊤)),
      Ideal.span (Set.range fun k => f.appTop (r k)) = ⊤ ∧
        ∀ k, Function.Bijective
          (IsLocalization.Away.map
            (Localization.Away (r k))
            (Localization.Away (f.appTop (r k))) f.appTop.hom (r k)) := by
  have hcompact : IsCompact (f.opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange]
    exact isCompact_range f.continuous
  obtain ⟨s, hs, hscov⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen (X := Y)).mp
      ⟨hcompact, f.opensRange.isOpen⟩
  letI := hs.fintype
  have hscov' : f.opensRange = ⨆ k : s, Y.basicOpen k.1 := by
    apply Opens.ext
    simpa using hscov
  refine ⟨s, inferInstance, fun k => k.1, ?_, ?_⟩
  · have htop : (⨆ k : s, X.basicOpen (f.appTop k.1)) = ⊤ := by
      calc
        (⨆ k : s, X.basicOpen (f.appTop k.1)) =
            f ⁻¹ᵁ (⨆ k : s, Y.basicOpen k.1) := by
              rw [f.preimage_iSup]
              congr 1
              funext k
              exact (f.preimage_basicOpen_top k.1).symm
        _ = f ⁻¹ᵁ f.opensRange := by rw [hscov']
        _ = ⊤ := f.preimage_opensRange
    rw [← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
    calc
      (⨆ a : Set.range (fun k : s => f.appTop k.1), X.basicOpen a.1) =
          ⨆ k : s, X.basicOpen (f.appTop k.1) := by
            apply le_antisymm
            · rw [iSup_le_iff]
              rintro ⟨_, k, rfl⟩
              exact le_iSup (fun k : s => X.basicOpen (f.appTop k.1)) k
            · rw [iSup_le_iff]
              intro k
              exact le_iSup (fun a : Set.range (fun k : s => f.appTop k.1) =>
                X.basicOpen a.1) ⟨f.appTop k.1, k, rfl⟩
      _ = ⊤ := htop
  · intro k
    have hk : Y.basicOpen k.1 ≤ f.opensRange := by
      rw [hscov']
      exact le_iSup (fun k : s => Y.basicOpen k.1) k
    letI : IsIso (f.app (Y.basicOpen k.1)) := f.isIso_app _ hk
    have hpre : IsAffineOpen (f ⁻¹ᵁ (⊤ : Y.Opens)) := by
      simpa using isAffineOpen_top X
    let gsec := IsLocalization.Away.map
      Γ(Y, Y.basicOpen k.1)
      Γ(X, X.basicOpen (f.appTop k.1)) f.appTop.hom k.1
    let e := (isAffineOpen_top Y).appBasicOpenIsoAwayMap f hpre k.1
    haveI : IsIso (CommRingCat.ofHom gsec) :=
      (Arrow.isIso_iff_isIso_of_isIso e.hom).mp inferInstance
    let graw := IsLocalization.Away.map
      (Localization.Away k.1)
      (Localization.Away (f.appTop k.1)) f.appTop.hom k.1
    let eY := IsLocalization.algEquiv (Submonoid.powers k.1)
      (Localization.Away k.1) Γ(Y, Y.basicOpen k.1)
    let eX := IsLocalization.algEquiv (Submonoid.powers (f.appTop k.1))
      (Localization.Away (f.appTop k.1))
      Γ(X, X.basicOpen (f.appTop k.1))
    have hsq : eX.toRingEquiv.toRingHom.comp graw =
        gsec.comp eY.toRingEquiv.toRingHom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers k.1)
      ext a
      simp [eX, eY, graw, gsec, IsLocalization.Away.map]
    have hgsec : Function.Bijective gsec := by
      simpa using ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom gsec)
    have hright : Function.Bijective (gsec.comp eY.toRingEquiv.toRingHom) :=
      hgsec.comp eY.toEquiv.bijective
    have hleft : Function.Bijective (eX.toRingEquiv.toRingHom.comp graw) :=
      hsq.symm ▸ hright
    exact (eX.toEquiv.bijective.of_comp_iff' graw).mp hleft

end AlgebraicGeometry
