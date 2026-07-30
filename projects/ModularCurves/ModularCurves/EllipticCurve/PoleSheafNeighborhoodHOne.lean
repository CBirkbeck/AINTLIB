/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafNoetherianStage
import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlue
import ModularCurves.EllipticCurve.PoleSheafNoetherianStageCech
import ModularCurves.EllipticCurve.PoleSheafProjectiveBaseChangeHOne
import ModularCurves.ForMathlib.CochainComplexFlatBaseChangeExact

/-!
# Local `H¹` vanishing for the simple-pole sheaf (FLW-1)

Around every point of an affine smooth proper fibrewise elliptic family there is a
principal open of the base over which the simple-pole sheaf has vanishing `H¹` — with
**no Noetherian hypothesis** on the base.

The route is the codex handover's stage argument: descend the family and its pole sheaf
to a Noetherian presentation stage (`exists_noetherianPoleSheafModel`); spread the
residue-fibre exactness of the stage's ordered base-Čech complex to a principal
neighborhood of the image of the chosen point
(`exists_away_orderedBaseCech_exact_of_poleSheafModel`); transport that exactness — the
stage complex is termwise flat, so its bounded tail-exactness is universal
(`LinearMap.baseChange_exact_of_bounded_flat_baseChange_exact`) — down the localization
tower to the corresponding basic open of the original base; convert to intrinsic Čech
exactness of the direct base-change family
(`orderedBaseCechComplex_baseChange_exact_iff_of_iso`), and read off `H¹ = 0` through
the ordered/unordered Čech comparison.

The conclusion is stated on the direct stage family together with a pointed isomorphism
to the restricted original family; downstream consumers work with the direct family and
cross back at the `LocallyWeierstrass` level (`LocallyWeierstrass.of_iso`).
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ModularCurves

/-- The global sections of the spectrum of a residue field form a field. -/
theorem isField_gamma_spec_residueField (X : Scheme.{u}) (x : X) :
    IsField Γ(Spec (X.residueField x), (⊤ : (Spec (X.residueField x)).Opens)) := by
  have e : Γ(Spec (X.residueField x), ⊤) ≃+* X.residueField x :=
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv
  exact e.toMulEquiv.isField (Field.toIsField (X.residueField x))

/-- If a global section of `Z` pulls back to a nonzero element of a field-sectioned
scheme `W` along `c`, then the image of any point of `W` lies in its basic open. -/
theorem mem_basicOpen_of_appTop_ne_zero {W Z : Scheme.{u}} (c : W ⟶ Z)
    (hW : IsField Γ(W, (⊤ : W.Opens))) (w : W)
    (r : Γ(Z, (⊤ : Z.Opens))) (hr : c.appTop.hom r ≠ 0) :
    c.base w ∈ Z.basicOpen r := by
  refine (Z.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) (c.base w) trivial r).mp ?_
  intro h0
  -- naturality of the global evaluation along `c`
  have hnat := Scheme.Γevaluation_naturality_apply (f := c) w r
  rw [show Z.Γevaluation (c.base w) r = 0 from h0, map_zero] at hnat
  -- the pulled-back section is a unit, so its evaluation cannot vanish
  obtain ⟨y, hy⟩ := hW.mul_inv_cancel hr
  have hunit : IsUnit (c.appTop.hom r) := isUnit_iff_exists.mpr
    ⟨y, hy, (mul_comm _ _).trans hy⟩
  have : IsUnit (W.Γevaluation w (c.appTop.hom r)) := hunit.map _
  rw [← hnat] at this
  exact this.ne_zero rfl

/-- A pointed identification `φ` of a once-base-changed family with an original family
induces, over any further leg `v` into the original base, a pointed identification of the
direct pullback with the base change of the original family. -/
private theorem exists_pointedIso_direct_pullback
    {Y Z W X S T' : Scheme.{u}} (yπ : Y ⟶ Z) (g : W ⟶ Z)
    {π : X ⟶ S} (q : S ≅ W) (φ : pullback yπ g ≅ X)
    (hφπ : φ.hom ≫ π ≫ q.hom = pullback.snd yπ g)
    (zA : W ⟶ pullback yπ g) (hzA : zA ≫ pullback.snd yπ g = 𝟙 W)
    (z : S ⟶ X) (hz : z ≫ π = 𝟙 S)
    (hφz : zA ≫ φ.hom = q.inv ≫ z) (v : T' ⟶ S) :
    ∃ eC : pullback yπ ((v ≫ q.hom) ≫ g) ≅ pullback π v,
      eC.hom ≫ pullback.snd π v = pullback.snd yπ ((v ≫ q.hom) ≫ g) ∧
        sectionIteratedBaseChangeDirect yπ g zA hzA (v ≫ q.hom) ≫ eC.hom =
          sectionBaseChange z hz v := by
  -- the iterated pullback is a pullback of `π` along `v`, via `φ` and `q`
  have hP : IsPullback
      (pullback.fst (pullback.snd yπ g) (v ≫ q.hom) ≫ φ.hom)
      (pullback.snd (pullback.snd yπ g) (v ≫ q.hom)) π v := by
    refine (IsPullback.of_hasPullback (pullback.snd yπ g) (v ≫ q.hom)).of_iso
      (Iso.refl _) φ (Iso.refl _) q.symm ?_ ?_ ?_ ?_
    · simp
    · simp
    · rw [Iso.symm_hom, ← hφπ]
      simp
    · simp
  refine ⟨(pullbackLeftPullbackSndIso yπ g (v ≫ q.hom)).symm ≪≫ hP.isoPullback,
    ?_, ?_⟩
  · simp
  · refine pullback.hom_ext ?_ ?_
    · simp only [sectionIteratedBaseChangeDirect, sectionBaseChange,
        Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id_assoc,
        IsPullback.isoPullback_hom_fst, pullback.lift_fst,
        pullback.lift_fst_assoc]
      rw [hφz, Iso.hom_inv_id_assoc]
    · simp only [sectionIteratedBaseChangeDirect, sectionBaseChange,
        Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.hom_inv_id_assoc,
        IsPullback.isoPullback_hom_snd, pullback.lift_snd,
        pullback.lift_snd_assoc]

/-- **(FLW-1 package)** Around every point of an affine smooth proper fibrewise elliptic
family there is a basic open of the base carrying a pointed family — identified with the
restricted original family — whose simple-pole sheaf admits a finite ordered affine cover
with a termwise-flat, bounded, positive-tail-exact ordered base-Čech complex. This is the
raw package; `exists_mem_basicOpen_pointedIso_subsingleton_H_one` reads off `H¹ = 0`, and
the FLW-2 chain reads off base-change of global sections. -/
theorem FibrewiseElliptic.exists_mem_basicOpen_pointedIso_orderedBaseCech_package
    {X S : Scheme.{u}} {π : X ⟶ S} [IsAffine S] [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ X) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz) (s : S) :
    ∃ a : Γ(S, (⊤ : S.Opens)), s ∈ S.basicOpen a ∧
      ∃ (E' : Scheme.{u}) (π' : E' ⟶ (S.basicOpen a).toScheme)
        (z' : (S.basicOpen a).toScheme ⟶ E') (hz' : z' ≫ π' = 𝟙 _)
        (hproper' : IsProper π'),
        SmoothOfRelativeDimension 1 π' ∧
          ∃ h' : FibrewiseElliptic π' z' hz',
            (∃ eC : E' ≅ pullback π (S.basicOpen a).ι,
              eC.hom ≫ pullback.snd π (S.basicOpen a).ι = π' ∧
                z' ≫ eC.hom = sectionBaseChange z hz (S.basicOpen a).ι) ∧
              (letI : IsProper π' := hproper'
              ∃ (ι : Type u) (_ : Fintype ι) (_ : LinearOrder ι)
                (UT : ι → E'.Opens),
                IsOpenCover UT ∧ (∀ i, IsAffineOpen (UT i)) ∧
                  0 < Fintype.card ι ∧
                    (∀ q, Module.Flat Γ((S.basicOpen a).toScheme,
                      (⊤ : (S.basicOpen a).toScheme.Opens))
                      ((Scheme.Modules.orderedBaseCechComplex π'
                        (sectionPoleSheafPower π' z' hz' 1) UT).X q)) ∧
                      (∀ q, Fintype.card ι ≤ q → Subsingleton
                        ((Scheme.Modules.orderedBaseCechComplex π'
                          (sectionPoleSheafPower π' z' hz' 1) UT).X q)) ∧
                        ∀ q, q < Fintype.card ι →
                          Function.Exact
                            ((Scheme.Modules.orderedBaseCechComplex π'
                              (sectionPoleSheafPower π' z' hz' 1) UT).d q (q + 1)).hom
                            ((Scheme.Modules.orderedBaseCechComplex π'
                              (sectionPoleSheafPower π' z' hz' 1) UT).d
                                (q + 1) (q + 2)).hom) := by
  classical
  -- the Noetherian stage model
  letI : Algebra (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)) :=
    ULift.algebra' ℤ Γ(S, (⊤ : S.Opens))
  obtain ⟨j, Y, yπ, L, hfp, hproperY, hsmoothY, hL, φ, zA, hzA, hproperA, hπA, hzAφ,
    hsmA, hfibA, ⟨e⟩⟩ :=
    FibrewiseElliptic.exists_noetherianPoleSheafModel hsm z hz h
  haveI := hfp
  haveI := hproperY
  haveI := hsmoothY
  haveI := hproperA
  let Bst : Type u :=
    Algebra.PresentationSystem.stage (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)) j
  letI : Algebra Bst Γ(S, (⊤ : S.Opens)) :=
    (Algebra.PresentationSystem.colimMap (ULift.{u} ℤ)
      Γ(S, (⊤ : S.Opens)) j).toRingHom.toAlgebra
  let gA : Spec (.of Γ(S, (⊤ : S.Opens))) ⟶ Spec (.of Bst) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap Bst Γ(S, (⊤ : S.Opens))))
  haveI : IsNoetherianRing Bst := inferInstance
  haveI : Y.IsSeparated := ⟨by rw [← terminal.comp_from yπ]; infer_instance⟩
  haveI : CompactSpace Y := (quasiCompact_iff_compactSpace yπ).mp inferInstance
  letI : L.IsQuasicoherent := hL.isQuasicoherent
  -- a finite ordered affine cover of the stage total space
  obtain ⟨ι, hιfin, V, hV, hVaff⟩ := Y.exists_finite_affine_openCover
  letI : Fintype ι := Fintype.ofFinite ι
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι)
    (Fintype.equivFin ι).injective
  -- the residue-field point over the chosen base point
  let sA : Spec (.of Γ(S, (⊤ : S.Opens))) := S.isoSpec.hom.base s
  let u : Spec ((Spec (.of Γ(S, (⊤ : S.Opens)))).residueField sA) ⟶
      Spec (.of Γ(S, (⊤ : S.Opens))) :=
    (Spec (.of Γ(S, (⊤ : S.Opens)))).fromSpecResidueField sA
  have hField := isField_gamma_spec_residueField (Spec (.of Γ(S, (⊤ : S.Opens)))) sA
  -- spread the stage Čech exactness to a principal neighborhood of `sA`'s image
  obtain ⟨r, hrp, hexact⟩ :=
    FibrewiseElliptic.exists_away_orderedBaseCech_exact_of_poleSheafModel L hL gA zA
      hzA hsmA hfibA e u hField V hV hVaff
  -- the corresponding basic open of `S` contains `s`
  have hrne : (u ≫ gA).appTop.hom r ≠ 0 := fun h0 => hrp (RingHom.mem_ker.mpr h0)
  let a : Γ(S, (⊤ : S.Opens)) := ((S.isoSpec.hom ≫ gA).appTop).hom r
  obtain ⟨w⟩ : Nonempty (Spec ((Spec (.of Γ(S, (⊤ : S.Opens)))).residueField sA)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum _))
  have hmem₀ : (u ≫ gA).base w ∈ (Spec (.of Bst)).basicOpen r :=
    mem_basicOpen_of_appTop_ne_zero (u ≫ gA) hField w r hrne
  have hbase : (S.isoSpec.hom ≫ gA).base s = (u ≫ gA).base w := by
    have hw : u.base w = sA := Scheme.fromSpecResidueField_apply sA w
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hw]
  have hmem : s ∈ S.basicOpen a := by
    rw [← Scheme.preimage_basicOpen_top]
    have hthis := hmem₀
    rwa [← hbase] at hthis
  -- the restricted base and the direct stage family over it
  let T' : Scheme.{u} := (S.basicOpen a).toScheme
  let v : T' ⟶ S := (S.basicOpen a).ι
  let u' : T' ⟶ Spec (.of Γ(S, (⊤ : S.Opens))) := v ≫ S.isoSpec.hom
  haveI : IsAffineOpen (S.basicOpen a) := (isAffineOpen_top S).basicOpen a
  haveI : IsAffine T' := ‹IsAffineOpen (S.basicOpen a)›
  let π' : pullback yπ (u' ≫ gA) ⟶ T' := pullback.snd yπ (u' ≫ gA)
  let z' : T' ⟶ pullback yπ (u' ≫ gA) :=
    sectionIteratedBaseChangeDirect yπ gA zA hzA u'
  have hz' : z' ≫ π' = 𝟙 T' := sectionIteratedBaseChangeDirect_snd yπ gA zA hzA u'
  haveI : IsProper π' := inferInstance
  have hsm' : SmoothOfRelativeDimension 1 π' :=
    smoothOfRelativeDimension_pullback_snd_comp yπ gA u' hsmA
  have h' : FibrewiseElliptic π' z' hz' :=
    fibrewiseElliptic_pullback_snd_comp yπ gA zA hzA hfibA u'
  -- the pole model on the direct family
  have eD := sectionPoleSheafPowerDirectBaseChangeIso gA zA hzA hsmA L e u'
  -- the localization tower `Γ(Spec Bst) → (Away r) → Γ(T')`
  letI : Algebra Γ(Spec (.of Bst), (⊤ : (Spec (.of Bst)).Opens))
      Γ(T', (⊤ : T'.Opens)) := (u' ≫ gA).appTop.hom.toAlgebra
  have hunit : IsUnit ((u' ≫ gA).appTop.hom r) := by
    have hsplit : ((u' ≫ gA).appTop).hom r =
        (v.appTop).hom (((S.isoSpec.hom ≫ gA).appTop).hom r) := by
      simp only [u', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
        Category.assoc]
    have h1 : IsUnit ((S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom a) :=
      AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen S.toRingedSpace a
    have happ : (v.appTop).hom a = ((S.basicOpen a).topIso.inv).hom
        ((S.presheaf.map (homOfLE (S.basicOpen_le a)).op).hom a) := by
      rw [opens_ι_appTop]
      rfl
    rw [hsplit, happ]
    exact h1.map ((S.basicOpen a).topIso.inv).hom
  letI : Algebra (Localization.Away r) Γ(T', (⊤ : T'.Opens)) :=
    (IsLocalization.Away.lift r hunit).toAlgebra
  haveI : IsScalarTower Γ(Spec (.of Bst), (⊤ : (Spec (.of Bst)).Opens))
      (Localization.Away r) Γ(T', (⊤ : T'.Opens)) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    exact congrFun (congrArg DFunLike.coe
      (IsLocalization.Away.lift_comp (x := r)
        (g := (u' ≫ gA).appTop.hom) hunit).symm) x
  -- flatness, boundedness, and the universal transport of the spread exactness
  let C := Scheme.Modules.orderedBaseCechComplex yπ L V
  letI : ∀ q, Module.Flat Γ(Spec (.of Bst), (⊤ : (Spec (.of Bst)).Opens)) (C.X q) :=
    fun q => Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible yπ L hL V hVaff q
  letI : Subsingleton (C.X (Fintype.card ι + 1)) :=
    Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le yπ L V
      (Fintype.card ι + 1) (Nat.le_succ _)
  have hexactT' : ∀ q, q < Fintype.card ι →
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange Γ(T', (⊤ : T'.Opens)))
        ((C.d (q + 1) (q + 2)).hom.baseChange Γ(T', (⊤ : T'.Opens))) := fun q hq =>
    LinearMap.baseChange_exact_of_bounded_flat_baseChange_exact
      (fun n => C.X n) (fun n => (C.d n (n + 1)).hom) (Fintype.card ι)
      (Localization.Away r) Γ(T', (⊤ : T'.Opens))
      (fun p hp => hexact p hp) q hq
  -- convert to intrinsic Čech exactness of the direct family
  let MT := sectionPoleSheafPower π' z' hz' 1
  let UT := fun i => pullback.fst yπ (u' ≫ gA) ⁻¹ᵁ V i
  have hUT : IsOpenCover UT :=
    Scheme.Hom.iSup_preimage_eq_top (pullback.fst yπ (u' ≫ gA)) hV
  have hUTaff : ∀ i, IsAffineOpen (UT i) := fun i =>
    IsAffineOpen.preimage_pullback_fst yπ (u' ≫ gA) (hVaff i)
  -- the cover is nonempty because the total space has a point over `s`
  have hNpos : 0 < Fintype.card ι := by
    have ht0 : (⟨s, hmem⟩ : T') ∈ (⊤ : T'.Opens) := trivial
    have hy : ∃ i, (z' ≫ pullback.fst yπ (u' ≫ gA)).base ⟨s, hmem⟩ ∈ V i := by
      have hmemTop : (z' ≫ pullback.fst yπ (u' ≫ gA)).base ⟨s, hmem⟩ ∈ iSup V := by
        rw [show iSup V = ⊤ from hV]
        trivial
      exact TopologicalSpace.Opens.mem_iSup.mp hmemTop
    obtain ⟨i, -⟩ := hy
    exact Fintype.card_pos_iff.mpr ⟨i⟩
  have hDexact : ∀ q, q < Fintype.card ι →
      Function.Exact
        ((Scheme.Modules.orderedBaseCechComplex π' MT UT).d q (q + 1)).hom
        ((Scheme.Modules.orderedBaseCechComplex π' MT UT).d (q + 1) (q + 2)).hom :=
    fun q hq =>
      (Scheme.Modules.orderedBaseCechComplex_baseChange_exact_iff_of_iso yπ (u' ≫ gA)
        L V hVaff MT eD q).mp (hexactT' q hq)
  letI : MT.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm' z' hz' 1
  have hMTinv : Scheme.Modules.IsInvertible MT :=
    sectionPoleSheafPower_isInvertible hsm' z' hz' 1
  haveI : (pullback yπ (u' ≫ gA)).IsSeparated :=
    ⟨by rw [← terminal.comp_from π']; infer_instance⟩
  have hDflat : ∀ q, Module.Flat Γ((S.basicOpen a).toScheme,
      (⊤ : (S.basicOpen a).toScheme.Opens))
      ((Scheme.Modules.orderedBaseCechComplex π' MT UT).X q) := fun q =>
    Scheme.Modules.orderedBaseCechObject_flat_of_isInvertible π' MT hMTinv UT hUTaff q
  have hDbdd : ∀ q, Fintype.card ι ≤ q → Subsingleton
      ((Scheme.Modules.orderedBaseCechComplex π' MT UT).X q) := fun q hq =>
    Scheme.Modules.orderedBaseCechObject_subsingleton_of_card_le π' MT UT q hq
  -- the pointed identification with the restricted original family
  obtain ⟨eC, hCπ, hCz⟩ :=
    exists_pointedIso_direct_pullback yπ gA S.isoSpec φ hπA zA hzA z hz hzAφ v
  exact ⟨a, hmem, pullback yπ (u' ≫ gA), π', z', hz', inferInstance, hsm', h',
    ⟨eC, hCπ, hCz⟩, ι, inferInstance, inferInstance, UT, hUT, hUTaff, hNpos,
    hDflat, hDbdd, hDexact⟩

/-- **(FLW-1)** Around every point of an affine smooth proper fibrewise elliptic family
there is a basic open of the base over which the simple-pole sheaf of a pointed family —
isomorphic, compatibly with the projection and the section, to the restricted original
family — has vanishing first cohomology. No Noetherian hypothesis on the base. -/
theorem FibrewiseElliptic.exists_mem_basicOpen_pointedIso_subsingleton_H_one
    {X S : Scheme.{u}} {π : X ⟶ S} [IsAffine S] [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π) (z : S ⟶ X) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz) (s : S) :
    ∃ a : Γ(S, (⊤ : S.Opens)), s ∈ S.basicOpen a ∧
      ∃ (E' : Scheme.{u}) (π' : E' ⟶ (S.basicOpen a).toScheme)
        (z' : (S.basicOpen a).toScheme ⟶ E') (hz' : z' ≫ π' = 𝟙 _)
        (hproper' : IsProper π'),
        SmoothOfRelativeDimension 1 π' ∧
          ∃ h' : FibrewiseElliptic π' z' hz',
            (∃ eC : E' ≅ pullback π (S.basicOpen a).ι,
              eC.hom ≫ pullback.snd π (S.basicOpen a).ι = π' ∧
                z' ≫ eC.hom = sectionBaseChange z hz (S.basicOpen a).ι) ∧
              (letI : IsProper π' := hproper'
              Subsingleton (CategoryTheory.Sheaf.H
                (sectionPoleSheafPower π' z' hz' 1).sheaf 1)) := by
  obtain ⟨a, hmem, E', π', z', hz', hproper', hsm', h', heC, ι, hfin, hord, UT, hUT,
    hUTaff, hpos, hflat, hbdd, hexact⟩ :=
    FibrewiseElliptic.exists_mem_basicOpen_pointedIso_orderedBaseCech_package
      hsm z hz h s
  letI : IsProper π' := hproper'
  letI : Fintype ι := hfin
  letI : LinearOrder ι := hord
  refine ⟨a, hmem, E', π', z', hz', hproper', hsm', h', heC, ?_⟩
  have hDexactAt :
      (Scheme.Modules.orderedBaseCechComplex π'
        (sectionPoleSheafPower π' z' hz' 1) UT).ExactAt 1 :=
    (ModularCurves.cochainComplex_functionExact_iff_exactAt
      (Scheme.Modules.orderedBaseCechComplex π'
        (sectionPoleSheafPower π' z' hz' 1) UT) 0).mp (hexact 0 hpos)
  letI : (sectionPoleSheafPower π' z' hz' 1).IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsm' z' hz' 1
  have hBC : (Scheme.Modules.baseCechComplex π'
      (sectionPoleSheafPower π' z' hz' 1) UT).ExactAt 1 :=
    Scheme.Modules.baseCechComplex_exactAt_one_of_orderedBaseCechComplex_exactAt_one
      π' (sectionPoleSheafPower π' z' hz' 1) UT hDexactAt
  exact (Scheme.Modules.baseCechComplex_exactAt_one_iff_subsingleton_H π'
    (sectionPoleSheafPower π' z' hz' 1) UT hUT hUTaff).mp hBC

end ModularCurves
