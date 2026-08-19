import ModularCurves.EllipticCurve.MulByHomFlatFibre
import ModularCurves.ForMathlib.FiniteFibrewiseFlat
import ModularCurves.ForMathlib.FinitePresentationCancel
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# BB-FLAT: `[N] : E ⟶ E` is flat over an arbitrary base

The assembly of the fibrewise criterion: `Flat` is Zariski-local at the target, so it
suffices to prove flatness of each restriction `[N] ∣_ V` for affine `V ≤ π⁻¹U`
(`U ⊆ S` affine). Each such restriction is a morphism of affine schemes, so this is
`RingHom.Flat` of the section ring map, which follows from the ring-level fibrewise
criterion `flat_of_fibre_flat_of_finitePresentation`:

* `T := Γ(E, [N]⁻¹V)` is a finite (BB-QF + ZMT) finitely presented module over
  `R := Γ(E, V)`, and flat over `A := Γ(S, U)` (`π` is smooth);
* the fibre of `R → T` at a prime `q ⊆ A` is the section map of the restriction of
  `[N]` on `E ×_S Spec κ(q)` — flat by `flat_mulByHom_baseChange_of_field` — matched
  through the **chart square**: the affine-restricted fibre of the base-changed curve
  is the spectrum of `κ(q) ⊗[A] Γ(E, V)` (`isoIsPullback` of the restricted pullback
  square against the `pullbackSpecIso` square).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Limits TensorProduct

universe u

namespace ModularCurves

open EllipticCurve

variable {S : Scheme.{u}}

section PullbackHelpers

variable {C : Type*} [Category C]

/-- The square with identity left leg over a mono is a pullback. -/
lemma isPullback_comp_mono {X Y Z : C} (g : X ⟶ Y) (m : Y ⟶ Z) [Mono m] :
    IsPullback g (𝟙 X) m (g ≫ m) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_)
    (fun s => by simp) (fun s t h1 h2 => by simpa using h2)⟩⟩
  have hcond := s.condition
  rw [← Category.assoc] at hcond
  exact (cancel_mono m).mp hcond.symm

/-- Extend the cospan of a pullback square by a monomorphism. -/
lemma IsPullback.comp_mono {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (m : Z ⟶ W) [Mono m] :
    IsPullback fst snd (f ≫ m) (g ≫ m) := by
  have hpaste := h.paste_vert (isPullback_comp_mono g m)
  simpa using hpaste

end PullbackHelpers

section Chart

variable (E : EllipticCurve S) {U : S.Opens} (hU : IsAffineOpen U)
  (K : Type u) [Field K] [Algebra Γ(S, U) K]

/-- The field-valued point of `S` classified by an algebra `Γ(S, U) → K`. -/
noncomputable def chartPoint : Spec (CommRingCat.of K) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) K)) ≫ hU.fromSpec

/-- The scheme-side chart square: for affine `V ≤ π⁻¹U`, the `V`-restriction of the
projection `E ×_S Spec K ⟶ E` sits in a pullback square over the cospan
`(V.ι ≫ π, chartPoint)`. -/
theorem isPullback_chart (V : (E.E).Opens) :
    IsPullback ((pullback.fst E.π (chartPoint hU K)) ∣_ V)
      (((pullback.fst E.π (chartPoint hU K)) ⁻¹ᵁ V).ι ≫
        pullback.snd E.π (chartPoint hU K))
      (V.ι ≫ E.π) (chartPoint hU K) :=
  (isPullback_morphismRestrict (pullback.fst E.π (chartPoint hU K)) V).paste_vert
    (IsPullback.of_hasPullback E.π (chartPoint hU K))

variable {V : (E.E).Opens} (hV : IsAffineOpen V) (eV : V ≤ E.π ⁻¹ᵁ U)

/-- The `Spec`-side chart square over the same cospan: `Spec (K ⊗[A] Γ(E,V))` with its
two tensor legs is a pullback over `(V.ι ≫ π, chartPoint)`. Here the `Γ(S,U)`-algebra
structure on `Γ(E,V)` is the section map of `π`. -/
theorem isPullback_chartSpec :
    letI : Algebra Γ(S, U) Γ(E.E, V) := (E.π.appLE U V eV).hom.toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(E.E, V) →ₐ[Γ(S, U)] K ⊗[Γ(S, U)] Γ(E.E, V)).toRingHom) ≫ hV.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          K →+* K ⊗[Γ(S, U)] Γ(E.E, V))))
      (V.ι ≫ E.π) (chartPoint hU K) := by
  letI : Algebra Γ(S, U) Γ(E.E, V) := (E.π.appLE U V eV).hom.toAlgebra
  -- the tensor pushout, seen as a pullback of spectra over `Spec Γ(S,U)`
  have h0 : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          K →+* K ⊗[Γ(S, U)] Γ(E.E, V))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          Γ(E.E, V) →ₐ[Γ(S, U)] K ⊗[Γ(S, U)] Γ(E.E, V)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) K)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(E.E, V)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct Γ(S, U) K Γ(E.E, V))
  -- extend the cospan along the (mono) affine-open inclusion `hU.fromSpec`
  have h1 := IsPullback.comp_mono h0.flip hU.fromSpec
  -- identify the two extended cospan legs
  have hleg1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) Γ(E.E, V))) ≫
      hU.fromSpec = hV.isoSpec.inv ≫ (V.ι ≫ E.π) := by
    have hkey : Spec.map (E.π.appLE U V eV) ≫ hU.fromSpec = hV.fromSpec ≫ E.π :=
      IsAffineOpen.SpecMap_appLE_fromSpec E.π hU hV eV
    rw [show CommRingCat.ofHom (algebraMap Γ(S, U) Γ(E.E, V)) = E.π.appLE U V eV from
      rfl, hkey, ← hV.isoSpec_inv_ι, Category.assoc]
  have hleg2 : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) K)) ≫ hU.fromSpec
      = chartPoint hU K := rfl
  rw [hleg1, hleg2] at h1
  -- absorb the `isoSpec` into the first leg
  have h2 := h1.paste_horiz (IsPullback.of_horiz_isIso
    (fst := hV.isoSpec.inv) (g := 𝟙 S) ⟨(Category.comp_id _).symm⟩)
  simpa using h2

end Chart

section IsoSpecConjugation

/-- `isoSpec`-conjugation of a restricted morphism: `Spec` of the section map equals
`f ∣_ V` conjugated by the `isoSpec`s (the arrow-square of the affine piece). -/
lemma isoSpec_hom_SpecMap_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (hpre : IsAffineOpen (f ⁻¹ᵁ V)) :
    hpre.isoSpec.hom ≫ Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)
      = (f ∣_ V) ≫ hV.isoSpec.hom := by
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec f hV hpre le_rfl
  have hw : Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl) ≫ hV.isoSpec.inv
      = hpre.isoSpec.inv ≫ (f ∣_ V) := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, hV.isoSpec_inv_ι,
      morphismRestrict_ι, ← Category.assoc, hpre.isoSpec_inv_ι, hsq]
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq]
  exact hw

/-- Transport of flatness from the section ring map to the restricted morphism. -/
lemma flat_morphismRestrict_of_flat_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) (hpre : IsAffineOpen (f ⁻¹ᵁ V))
    (hflat : RingHom.Flat (f.appLE V (f ⁻¹ᵁ V) le_rfl).hom) : Flat (f ∣_ V) := by
  haveI : IsAffine (V : Y.Opens).toScheme := hV
  haveI : IsAffine ((f ⁻¹ᵁ V) : X.Opens).toScheme := hpre
  have harrow : Arrow.mk (f ∣_ V) ≅
      Arrow.mk (Spec.map (f.appLE V (f ⁻¹ᵁ V) le_rfl)) :=
    Arrow.isoMk hpre.isoSpec hV.isoSpec (isoSpec_hom_SpecMap_appLE f hV hpre)
  rw [MorphismProperty.arrow_mk_iso_iff (P := @Flat) harrow]
  exact Flat.SpecMap_iff.mpr hflat

end IsoSpecConjugation

section Assembly

open IsLocalRing

/-- **BB-FLAT, general base**: multiplication by `N ≥ 1` is a flat endomorphism of any
elliptic curve over any base scheme. -/
theorem mulByHom_flat_general (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    Flat (E.mulByHom (N : ℤ)) := by
  -- global instances for `[N]`
  haveI : LocallyQuasiFinite (E.mulByHom (N : ℤ)) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      fun x => mulByHom_finite_preimage_singleton E N x
  haveI hfin : IsFinite (E.mulByHom (N : ℤ)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI hsmooth : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) E.π
  haveI hLFP : LocallyOfFinitePresentation (E.mulByHom (N : ℤ)) := by
    have h : LocallyOfFinitePresentation (E.mulByHom (N : ℤ) ≫ E.π) := by
      rw [E.mulByHom_π]; infer_instance
    exact LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h inferInstance
  set f := E.mulByHom (N : ℤ) with hf
  -- the affine cover of the target subordinate to affines of `S`
  have hexists : ∀ y : E.E, ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : (E.E).Opens)
      (_ : IsAffineOpen V), y ∈ V ∧ V ≤ E.π ⁻¹ᵁ U := by
    intro y
    obtain ⟨U', hU'mem, hUmem, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      S.isBasis_affineOpens (show E.π.base y ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨V', hV'mem, hyV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (E.E).isBasis_affineOpens (show y ∈ E.π ⁻¹ᵁ U' from hUmem)
    exact ⟨U', hU'mem, V', hV'mem, hyV, hVle⟩
  choose U hU V hV hyV eV using hexists
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) (f := f) V ?_ ?_
  · rw [eq_top_iff]
    exact fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyV y⟩
  · intro y
    -- the affine piece
    haveI hpre : IsAffineOpen (f ⁻¹ᵁ V y) := (hV y).preimage f
    have eT : (f ⁻¹ᵁ V y) ≤ E.π ⁻¹ᵁ U y := by
      intro x hx
      have hπ : E.π.base (f.base x) = E.π.base x := by
        have h1 : (f ≫ E.π).base x = E.π.base x := by
          rw [hf, E.mulByHom_π (N : ℤ)]
        simpa using h1
      have hmem : f.base x ∈ V y := hx
      have := eV y hmem
      show E.π.base x ∈ U y
      rw [← hπ]
      exact this
    refine flat_morphismRestrict_of_flat_appLE f (hV y) hpre ?_
    -- ring data
    set A := Γ(S, U y)
    set R := Γ(E.E, V y)
    set T := Γ(E.E, f ⁻¹ᵁ V y)
    letI : Algebra A R := (E.π.appLE (U y) (V y) (eV y)).hom.toAlgebra
    letI : Algebra A T := (E.π.appLE (U y) (f ⁻¹ᵁ V y) eT).hom.toAlgebra
    letI : Algebra R T := (f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl).hom.toAlgebra
    haveI : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq' <| by
      have hstep := Scheme.Hom.appLE_comp_appLE f E.π (U y) (V y) (f ⁻¹ᵁ V y)
        (eV y) le_rfl
      simp only [hf ▸ E.mulByHom_π (N : ℤ)] at hstep
      exact congrArg CommRingCat.Hom.hom hstep.symm
    -- finiteness and presentation of `T` over `R`
    haveI hTfin : Module.Finite R T := by
      have h := f.finite_app (V y) (hV y)
      rwa [Scheme.Hom.app_eq_appLE] at h
    haveI hTfp : Module.FinitePresentation R T := by
      haveI : Algebra.FinitePresentation R T :=
        f.finitePresentation_appLE (hV y) hpre le_rfl
      exact Module.FinitePresentation.of_finite_of_finitePresentation R T
    -- flatness of `T` over `A`
    haveI hTA : Module.Flat A T := E.π.flat_appLE (hU y) hpre eT
    -- the criterion; its fibre input is the chart conversion below
    have hcrit : Module.Flat R T := by
      refine flat_of_fibre_flat_of_finitePresentation (A := A) ?_
      intro q hq
      set K := q.ResidueField with hKdef
      set gK := chartPoint (hU y) K with hgKdef
      set fstP := pullback.fst E.π gK with hfstPdef
      set sndP := pullback.snd E.π gK with hsndPdef
      set fP : pullback E.π gK ⟶ pullback E.π gK :=
        (E.baseChange gK).mulByHom (N : ℤ) with hfPdef
      -- geometric flatness of the fibre `[N]`, restricted to the chart
      have hgeo : Flat fP := flat_mulByHom_baseChange_of_field E N gK
      have hgeoW : Flat (fP ∣_ (fstP ⁻¹ᵁ V y)) := IsZariskiLocalAtTarget.restrict hgeo _
      -- the four chart squares and the two comparison isomorphisms
      have sqR := isPullback_chart E (hU y) K (V y)
      have sqT := isPullback_chart E (hU y) K (f ⁻¹ᵁ V y)
      have sqRS := isPullback_chartSpec E (hU y) K (hV y) (eV y)
      have sqTS := isPullback_chartSpec E (hU y) K hpre eT
      let eR := sqR.isoIsPullback _ _ sqRS
      let eTS := sqT.isoIsPullback _ _ sqTS
      -- the preimage identity
      have hcompP : fP ≫ fstP = fstP ≫ f := mulByHom_baseChange_fst E gK (N : ℤ)
      have hpre2 : fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y) = fstP ⁻¹ᵁ (f ⁻¹ᵁ V y) := by
        show (fP ≫ fstP) ⁻¹ᵁ (V y) = (fstP ≫ f) ⁻¹ᵁ (V y)
        exact congrArg (fun g : pullback E.π gK ⟶ E.E => g ⁻¹ᵁ (V y)) hcompP
      -- the ring triangles for the fibre inclusion
      have hT1 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
            R →ₐ[A] K ⊗[A] R).toRingHom ≫
            CommRingCat.ofHom (fiberInclusion (R := R) (T := T) q).toRingHom
          = f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl ≫
            CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
              T →ₐ[A] K ⊗[A] T).toRingHom := by
        ext r
        exact congrArg (fun (φ : R →ₐ[A] K ⊗[A] T) => φ r)
          (Algebra.TensorProduct.map_restrictScalars_comp_includeRight
            (AlgHom.id K K) (IsScalarTower.toAlgHom A R T))
      have hT2 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            K →+* K ⊗[A] R) ≫
            CommRingCat.ofHom (fiberInclusion (R := R) (T := T) q).toRingHom
          = CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            K →+* K ⊗[A] T) := by
        rw [← CommRingCat.ofHom_comp]
        refine congrArg CommRingCat.ofHom (RingHom.ext fun k => ?_)
        show (fiberInclusion (R := R) (T := T) q) (k ⊗ₜ[A] 1) = k ⊗ₜ[A] 1
        simp
      -- the arrow square: both legs checked against the `Spec`-side pullback
      have hw : ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS).hom ≫
            Spec.map (CommRingCat.ofHom (fiberInclusion (R := R) (T := T) q).toRingHom)
          = (fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ eR.hom := by
        refine sqRS.hom_ext ?_ ?_
        · -- component into the `V`-chart
          have hR1 : eR.hom ≫ (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.includeRight :
                  R →ₐ[A] K ⊗[A] R).toRingHom) ≫ (hV y).isoSpec.inv)
              = fstP ∣_ (V y) := sqR.isoIsPullback_hom_fst _ _ sqRS
          have hT1' : eTS.hom ≫ (Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.includeRight :
                  T →ₐ[A] K ⊗[A] T).toRingHom) ≫ hpre.isoSpec.inv)
              = fstP ∣_ (f ⁻¹ᵁ V y) := sqT.isoIsPullback_hom_fst _ _ sqTS
          -- unfold both sides through the triangles
          have lhs1 : Spec.map (CommRingCat.ofHom
                (fiberInclusion (R := R) (T := T) q).toRingHom) ≫
                Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
                  R →ₐ[A] K ⊗[A] R).toRingHom)
              = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
                  T →ₐ[A] K ⊗[A] T).toRingHom) ≫
                Spec.map (f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl) := by
            rw [← Spec.map_comp, hT1, Spec.map_comp]
          calc ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS).hom ≫
                Spec.map (CommRingCat.ofHom
                  (fiberInclusion (R := R) (T := T) q).toRingHom) ≫
                (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
                  R →ₐ[A] K ⊗[A] R).toRingHom) ≫ (hV y).isoSpec.inv)
              = ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS).hom ≫
                Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
                  T →ₐ[A] K ⊗[A] T).toRingHom) ≫
                (Spec.map (f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl) ≫ (hV y).isoSpec.inv) := by
                rw [← Category.assoc (Spec.map _), lhs1]
                simp only [Category.assoc]
            _ = ((pullback E.π gK).isoOfEq hpre2).hom ≫ (fstP ∣_ (f ⁻¹ᵁ V y)) ≫
                (hpre.isoSpec.hom ≫
                  Spec.map (f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl) ≫ (hV y).isoSpec.inv) := by
                have h' : eTS.hom ≫ Spec.map (CommRingCat.ofHom
                    (Algebra.TensorProduct.includeRight :
                      T →ₐ[A] K ⊗[A] T).toRingHom)
                    = (fstP ∣_ (f ⁻¹ᵁ V y)) ≫ hpre.isoSpec.hom := by
                  have h := hT1'
                  rw [← Category.assoc] at h
                  exact (Iso.comp_inv_eq _).mp h
                simp only [Iso.trans_hom, Category.assoc]
                rw [← Category.assoc eTS.hom, h']
                simp only [Category.assoc]
            _ = ((pullback E.π gK).isoOfEq hpre2).hom ≫ (fstP ∣_ (f ⁻¹ᵁ V y)) ≫
                (f ∣_ (V y)) := by
                rw [show hpre.isoSpec.hom ≫
                    Spec.map (f.appLE (V y) (f ⁻¹ᵁ V y) le_rfl) ≫ (hV y).isoSpec.inv
                    = f ∣_ (V y) from by
                  rw [← Category.assoc, isoSpec_hom_SpecMap_appLE f (hV y) hpre]
                  simp]
            _ = (fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ (fstP ∣_ (V y)) := by
                rw [← cancel_mono (V y).ι]
                calc (((pullback E.π gK).isoOfEq hpre2).hom ≫ (fstP ∣_ (f ⁻¹ᵁ V y)) ≫
                      (f ∣_ (V y))) ≫ (V y).ι
                    = ((pullback E.π gK).isoOfEq hpre2).hom ≫ (fstP ∣_ (f ⁻¹ᵁ V y)) ≫
                      ((f ∣_ (V y)) ≫ (V y).ι) := by simp only [Category.assoc]
                  _ = ((pullback E.π gK).isoOfEq hpre2).hom ≫ (fstP ∣_ (f ⁻¹ᵁ V y)) ≫
                      ((f ⁻¹ᵁ V y).ι ≫ f) := by rw [morphismRestrict_ι]
                  _ = (((pullback E.π gK).isoOfEq hpre2).hom ≫
                      ((fstP ∣_ (f ⁻¹ᵁ V y)) ≫ (f ⁻¹ᵁ V y).ι)) ≫ f := by
                      simp only [Category.assoc]
                  _ = (((pullback E.π gK).isoOfEq hpre2).hom ≫
                      ((fstP ⁻¹ᵁ (f ⁻¹ᵁ V y)).ι ≫ fstP)) ≫ f := by
                      rw [morphismRestrict_ι]
                  _ = ((fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ fstP) ≫ f := by
                      rw [← Category.assoc, (pullback E.π gK).isoOfEq_hom_ι hpre2]
                  _ = (fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ fP ≫ fstP := by
                      rw [Category.assoc, hcompP]
                  _ = ((fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ fP) ≫ fstP := by
                      simp only [Category.assoc]
                  _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ (fstP ⁻¹ᵁ V y).ι) ≫ fstP := by
                      rw [morphismRestrict_ι]
                  _ = (fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ ((fstP ⁻¹ᵁ V y).ι ≫ fstP) := by
                      simp only [Category.assoc]
                  _ = (fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ ((fstP ∣_ (V y)) ≫ (V y).ι) := by
                      rw [morphismRestrict_ι]
                  _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ (fstP ∣_ (V y))) ≫ (V y).ι := by
                      simp only [Category.assoc]
            _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ eR.hom) ≫
                (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
                  R →ₐ[A] K ⊗[A] R).toRingHom) ≫ (hV y).isoSpec.inv) := by
                rw [Category.assoc, hR1]
        · -- component into `Spec K`
          have hR2 : eR.hom ≫ Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] R))
              = (fstP ⁻¹ᵁ V y).ι ≫ sndP := sqR.isoIsPullback_hom_snd _ _ sqRS
          have hT2' : eTS.hom ≫ Spec.map (CommRingCat.ofHom
                (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] T))
              = (fstP ⁻¹ᵁ (f ⁻¹ᵁ V y)).ι ≫ sndP := sqT.isoIsPullback_hom_snd _ _ sqTS
          calc ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS).hom ≫
                Spec.map (CommRingCat.ofHom
                  (fiberInclusion (R := R) (T := T) q).toRingHom) ≫
                Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] R))
              = ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS).hom ≫
                Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] T)) := by
                rw [← Spec.map_comp, hT2]
            _ = ((pullback E.π gK).isoOfEq hpre2).hom ≫
                (fstP ⁻¹ᵁ (f ⁻¹ᵁ V y)).ι ≫ sndP := by
                simp only [Iso.trans_hom, Category.assoc]
                rw [hT2']
            _ = (fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ sndP := by
                rw [← Category.assoc, (pullback E.π gK).isoOfEq_hom_ι hpre2]
            _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ eR.hom) ≫
                Spec.map (CommRingCat.ofHom
                  (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] R)) := by
                calc (fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ sndP
                    = (fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ (fP ≫ sndP) := by
                      rw [show fP ≫ sndP = sndP from
                        mulByHom_π (E.baseChange gK) (N : ℤ)]
                  _ = ((fP ⁻¹ᵁ (fstP ⁻¹ᵁ V y)).ι ≫ fP) ≫ sndP := by
                      simp only [Category.assoc]
                  _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ (fstP ⁻¹ᵁ V y).ι) ≫ sndP := by
                      rw [morphismRestrict_ι]
                  _ = (fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ ((fstP ⁻¹ᵁ V y).ι ≫ sndP) := by
                      simp only [Category.assoc]
                  _ = ((fP ∣_ (fstP ⁻¹ᵁ V y)) ≫ eR.hom) ≫
                      Spec.map (CommRingCat.ofHom
                        (Algebra.TensorProduct.includeLeftRingHom :
                          K →+* K ⊗[A] R)) := by
                      rw [Category.assoc, hR2]
      -- transport flatness through the arrow isomorphism
      have harrow : Arrow.mk (fP ∣_ (fstP ⁻¹ᵁ V y)) ≅
          Arrow.mk (Spec.map (CommRingCat.ofHom
            (fiberInclusion (R := R) (T := T) q).toRingHom)) :=
        Arrow.isoMk ((pullback E.π gK).isoOfEq hpre2 ≪≫ eTS) eR hw
      have hflatSpec : Flat (Spec.map (CommRingCat.ofHom
          (fiberInclusion (R := R) (T := T) q).toRingHom)) :=
        (MorphismProperty.arrow_mk_iso_iff (P := @Flat) harrow).mp hgeoW
      exact Flat.SpecMap_iff.mp hflatSpec
    exact hcrit

/-- **BB-DEG, general base**: `[N]` has fibre rank `N²` at every point of any elliptic
curve over any base. The rank is read off the residue fibre through the `[N]`
base-change square (`finrank_of_isPullback`), where the fibre curve is
pointed-isomorphic to a projective Weierstrass model (`fibreModelIsoAsOver`) whose rank
is `N²` by STREAM-KM's field-level `modelEllipticCurve_mulByHom_finrank` (the HasseWeil
`deg [N] = N²` anchor — not re-derived here). -/
theorem mulByHom_finrank_general (E : EllipticCurve S) (N : ℕ) [NeZero N] (x : E.E) :
    (E.mulByHom (N : ℤ)).finrank x = N ^ 2 := by
  -- global instances for `[N]`
  haveI : LocallyQuasiFinite (E.mulByHom (N : ℤ)) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _
      fun z => mulByHom_finite_preimage_singleton E N z
  haveI hfin : IsFinite (E.mulByHom (N : ℤ)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI hflat : Flat (E.mulByHom (N : ℤ)) := mulByHom_flat_general E N
  -- the residue fibre at `s := π x` and a preimage of `x` in it
  set s := E.π.base x with hs
  set gK := S.fromSpecResidueField s with hgKdef
  obtain ⟨y', hy'⟩ : x ∈ Set.range (pullback.fst E.π gK).base := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact Set.mem_preimage.mpr rfl
  -- rank transfer along the `[N]` base-change square
  have sq := isPullback_mulByHom_baseChange E gK (N : ℤ)
  have h1 : Scheme.Hom.finrank ((E.baseChange gK).mulByHom (N : ℤ)) y'
      = Scheme.Hom.finrank (E.mulByHom (N : ℤ)) ((pullback.fst E.π gK).base y') :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ sq.flip y'
  -- the fibre curve is pointed-isomorphic to a model over `κ(s)`
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  -- instances for the field-level rank theorem
  haveI : LocallyQuasiFinite ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    modelMulByHom_locallyQuasiFinite_of_field W N
  haveI : IsFinite ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : Flat ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
    modelMulByHom_flat_of_field W N
  haveI : Smooth (modelEllipticCurve W).π :=
    SmoothOfRelativeDimension.smooth (n := 1) (modelEllipticCurve W).π
  haveI : LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
    have h : LocallyOfFinitePresentation ((modelEllipticCurve W).mulByHom (N : ℤ) ≫
        (modelEllipticCurve W).π) := by
      rw [mulByHom_π]; infer_instance
    exact LocallyOfFinitePresentation.of_comp_of_locallyOfFiniteType h inferInstance
  haveI : DecidableEq (S.residueField s) := Classical.decEq _
  -- the conjugation square along the pointed group-object iso
  let ψ : (E.baseChange gK).E ⟶ (modelEllipticCurve W).E := φ.hom.left
  let ψ' : (modelEllipticCurve W).E ⟶ (E.baseChange gK).E := φ.inv.left
  have hc : (E.baseChange gK).mulByHom (N : ℤ) ≫ ψ
      = ψ ≫ (modelEllipticCurve W).mulByHom (N : ℤ) :=
    mulByHom_comp_left_of_isMonHom _ _ φ.hom (N : ℤ)
  have hinv : ψ ≫ ψ' = 𝟙 _ := by
    show φ.hom.left ≫ φ.inv.left = 𝟙 _
    rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
  have hinv' : ψ' ≫ ψ = 𝟙 _ := by
    show φ.inv.left ≫ φ.hom.left = 𝟙 _
    rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  haveI : IsIso ψ := ⟨ψ', hinv, hinv'⟩
  have sqψ : IsPullback ψ ((E.baseChange gK).mulByHom (N : ℤ))
      ((modelEllipticCurve W).mulByHom (N : ℤ)) ψ :=
    IsPullback.of_horiz_isIso ⟨hc.symm⟩
  have h2 : Scheme.Hom.finrank ((E.baseChange gK).mulByHom (N : ℤ)) y'
      = Scheme.Hom.finrank ((modelEllipticCurve W).mulByHom (N : ℤ)) (ψ.base y') :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ sqψ y'
  -- conclude via the field-level `N²`
  have h3 := EllipticCurve.modelEllipticCurve_mulByHom_finrank W N (ψ.base y')
  rw [← hy', ← h1, h2, h3]

end Assembly


-- Ported from main's MulByHomFlat: this file carries dev's version (for
-- `mulByHom_flat_general`), and `KernelDivisibilityGlue` consumes this definition.
namespace EllipticCurve

/-- **(BB-FLAT funnel)** The square-zero kernels of the point functor are `N`-divisible:
for every affine square-zero thickening `Spec (A'/I) ⊆ Spec A'` over `S` and every point
`ε ∈ E(A')` restricting to zero on the thickening, `ε` is `N` times such a point. This is
the Lie-theoretic content of `[N]`-smoothness (`d[N] = N·`, invertible when `N` is);
discharge route: the `TorsionUnramifiedFibre` co-multiplication layer off the field base
(board v10.147). -/
def KernelNDivisible {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) : Prop :=
  ∀ (A' : CommRingCat.{u}) (I : Ideal A'), I ^ 2 = ⊥ → ∀ (b' : Spec A' ⟶ S)
    (ε : E.Point b'),
    Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ε = 0 →
    ∃ δ : E.Point b',
      Point.restrict E (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) δ = 0 ∧
      (N : ℤ) • δ = ε

end EllipticCurve


end ModularCurves
