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

private lemma gammaSpecIso_naturality_apply (f : R →+* S)
    (x : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        ((Spec.map (CommRingCat.ofHom f)).appTop x) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x) := by
  change ((Spec.map (CommRingCat.ofHom f)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom) x =
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom f) x
  exact congrArg (fun g => g x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

private noncomputable def awayEquivOfRingEquiv
    (e : R ≃+* S) (r : R) :
    Localization.Away r ≃+* Localization.Away (e r) :=
  IsLocalization.ringEquivOfRingEquiv _ _ e (Submonoid.map_powers e r)

private lemma awayEquivOfRingEquiv_algebraMap
    (e : R ≃+* S) (r x : R) :
    awayEquivOfRingEquiv e r (algebraMap R (Localization.Away r) x) =
      algebraMap S (Localization.Away (e r)) (e x) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq (Submonoid.map_powers e r) x

private lemma awayMap_bijective_of_equiv
    {R₁ S₁ R₂ S₂ : Type u}
    [CommRing R₁] [CommRing S₁] [CommRing R₂] [CommRing S₂]
    (f₁ : R₁ →+* S₁) (f₂ : R₂ →+* S₂)
    (eR : R₁ ≃+* R₂) (eS : S₁ ≃+* S₂)
    (hcomm : eS.toRingHom.comp f₁ = f₂.comp eR.toRingHom)
    (r : R₁)
    (hmap : Function.Bijective
      (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (f₁ r)) f₁ r)) :
    Function.Bijective
      (IsLocalization.Away.map (Localization.Away (eR r))
        (Localization.Away (f₂ (eR r))) f₂ (eR r)) := by
  have hvalue (x : R₁) : eS (f₁ x) = f₂ (eR x) := by
    change (eS.toRingHom.comp f₁) x = (f₂.comp eR.toRingHom) x
    rw [hcomm]
  let eAwayR := awayEquivOfRingEquiv eR r
  have hpowersS : Submonoid.map eS.toMonoidHom (Submonoid.powers (f₁ r)) =
      Submonoid.powers (f₂ (eR r)) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (hvalue r)
  let eAwayS : Localization.Away (f₁ r) ≃+* Localization.Away (f₂ (eR r)) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eS hpowersS
  let g₁ := IsLocalization.Away.map
    (Localization.Away r) (Localization.Away (f₁ r)) f₁ r
  let g₂ := IsLocalization.Away.map
    (Localization.Away (eR r)) (Localization.Away (f₂ (eR r))) f₂ (eR r)
  have hsq : eAwayS.toRingHom.comp g₁ = g₂.comp eAwayR.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    change eAwayS (g₁ (algebraMap _ (Localization.Away r) x)) =
      g₂ (eAwayR (algebraMap _ (Localization.Away r) x))
    rw [show g₁ (algebraMap _ (Localization.Away r) x) =
        algebraMap _ (Localization.Away (f₁ r)) (f₁ x) by
      simp [g₁, IsLocalization.Away.map]]
    rw [show eAwayS (algebraMap _ (Localization.Away (f₁ r)) (f₁ x)) =
        algebraMap _ (Localization.Away (f₂ (eR r))) (eS (f₁ x)) by
      exact IsLocalization.ringEquivOfRingEquiv_eq hpowersS (f₁ x)]
    rw [show eAwayR (algebraMap _ (Localization.Away r) x) =
        algebraMap _ (Localization.Away (eR r)) (eR x) by
      exact awayEquivOfRingEquiv_algebraMap eR r x]
    rw [show g₂ (algebraMap _ (Localization.Away (eR r)) (eR x)) =
        algebraMap _ (Localization.Away (f₂ (eR r))) (f₂ (eR x)) by
      simp [g₂, IsLocalization.Away.map]]
    rw [hvalue]
  have hleft : Function.Bijective (eAwayS.toRingHom.comp g₁) :=
    eAwayS.bijective.comp hmap
  have hright : Function.Bijective (g₂.comp eAwayR.toRingHom) := hsq ▸ hleft
  exact (Function.Bijective.of_comp_iff g₂ eAwayR.bijective).mp hright

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

/-- If a ring map induces an open immersion on spectra, finitely many elements
of the source ring cut out a principal cover of the target and induce
isomorphisms on the corresponding principal localizations. -/
theorem exists_awayCover_of_isOpenImmersion_SpecMap
    (f : R →+* S)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    ∃ (κ : Type u) (_ : Finite κ) (r : κ → R),
      Ideal.span (Set.range fun k => f (r k)) = ⊤ ∧
        ∀ k, Function.Bijective
          (IsLocalization.Away.map
            (Localization.Away (r k))
            (Localization.Away (f (r k))) f (r k)) := by
  let g := Spec.map (CommRingCat.ofHom f)
  obtain ⟨κ, hκ, rΓ, hspan, hmap⟩ :=
    Scheme.Hom.exists_awayCover_of_isOpenImmersion g
  let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eS := (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
  let r : κ → R := fun k => eR (rΓ k)
  have hcommRing : eS.toRingHom.comp g.appTop.hom = f.comp eR.toRingHom := by
    ext x
    exact gammaSpecIso_naturality_apply f x
  have hcomm (x : Γ(Spec (CommRingCat.of R), ⊤)) :
      eS (g.appTop x) = f (eR x) := gammaSpecIso_naturality_apply f x
  have hvalue (k : κ) : eS (g.appTop (rΓ k)) = f (r k) := hcomm (rΓ k)
  have hspan' : Ideal.span (Set.range fun k => f (r k)) = ⊤ := by
    have hrange : eS.toRingHom '' Set.range (fun k => g.appTop (rΓ k)) =
        Set.range (fun k => f (r k)) := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (hvalue k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨g.appTop (rΓ k), ⟨k, rfl⟩, hvalue k⟩
    have hspanMap := congrArg (Ideal.map eS.toRingHom) hspan
    rw [Ideal.map_top, Ideal.map_span, hrange] at hspanMap
    exact hspanMap
  refine ⟨κ, hκ, r, hspan', ?_⟩
  intro k
  simpa only [r] using awayMap_bijective_of_equiv
    g.appTop.hom f eR eS hcommRing (rΓ k) (hmap k)

end AlgebraicGeometry
