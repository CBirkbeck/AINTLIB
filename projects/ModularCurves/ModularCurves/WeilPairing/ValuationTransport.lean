/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.MulByHomDegree
import HasseWeil.HasseBound.WeilPairing.Constancy

/-!
# The scheme↔valuation transport at the Z-chart (U5-L1a r-pinning, RP-3)

The P-parametrised transport identifying the model curve's chart-side local data with
HasseWeil's valuation layer: for a smooth point `P` of the Weierstrass curve, the
maximal ideal `maximalIdealAt P` (mathlib's `XYIdeal`) transports along the fixed chart
identification `coordRingToZSection` to a maximal ideal of `Γ(projModel W, zChart W)`,
localisations transport accordingly (`zChartLocalizationEquiv`), and the transport is
compatible with the fixed function-field identification `projModelFunctionFieldEquiv`
(`zChartLocalizationEquiv_compat` — both extensions of `coordRingToZSection.symm`, equal
by localisation-extension uniqueness).

This is the core of the divisor dictionary's r-pinning: with it, the order of a chart
section at `P` can be read as HasseWeil's `ord_P` of its function-field image.

No point classification appears anywhere: everything is parametrised by `P`.
-/

universe u

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open HasseWeil.Curves HasseWeil.WeilPairing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurves

variable {K : Type u} [Field K] [DecidableEq K]

/-- **(RP-3 transport, step 1)** The zChart-side maximal ideal of a smooth point: the
transport of `maximalIdealAt` (= mathlib's `XYIdeal`) along the fixed chart
identification `coordRingToZSection`. -/
noncomputable def zChartMaximalIdeal (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :=
  Ideal.map (coordRingToZSection W)
    ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P)

/-- **(RP-3 transport, step 1b)** Maximality transports along the ring equivalence. -/
theorem zChartMaximalIdeal_isMaximal (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :
    (zChartMaximalIdeal W P).IsMaximal := by
  have h := (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P
  exact Ideal.map_isMaximal_of_equiv _ (hp := h)

/-- **(RP-3 transport, step 2a-abstract)** For any ring equivalence, the prime
complement of the transported ideal pulls back to the original prime complement. -/
theorem submonoid_map_primeCompl_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (m : Ideal R) [hm : m.IsPrime]
    (hmap : (Ideal.map e m).IsPrime) :
    Submonoid.map e.symm.toMonoidHom (Ideal.map e m).primeCompl = m.primeCompl := by
  have hmem : ∀ y : S, y ∈ Ideal.map e m ↔ e.symm y ∈ m := by
    intro y
    constructor
    · intro hy
      have hle : Ideal.map e m ≤ Ideal.comap (e.symm : S →+* R) m :=
        Ideal.map_le_iff_le_comap.mpr fun a ha => by simpa using ha
      simpa using hle hy
    · intro hy
      simpa using Ideal.mem_map_of_mem e hy
  ext x
  simp only [Submonoid.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    intro hx
    exact hg ((hmem g).mpr (by simpa using hx))
  · intro hx
    exact ⟨e x, fun hmem' => hx (by simpa using (hmem _).mp hmem'), by simp⟩

/-- **(RP-3 transport, step 2a)** The instantiation at the chart identification. -/
theorem primeCompl_map_zChartMaximalIdeal (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :
    haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
    haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
    Submonoid.map (coordRingToZSection W).symm.toMonoidHom
        (zChartMaximalIdeal W P).primeCompl =
      ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P).primeCompl :=
  haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  submonoid_map_primeCompl_of_ringEquiv (coordRingToZSection W)
    ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P)
    ((zChartMaximalIdeal_isMaximal W P).isPrime)

/-- **(RP-3 transport, step 2)** The chart-side localisation at `P` is HasseWeil's
local ring: `Localization.AtPrime` transported along the fixed chart identification. -/
noncomputable def zChartLocalizationEquiv (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :
    haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
    Localization.AtPrime (zChartMaximalIdeal W P) ≃+*
      (⟨W⟩ : SmoothPlaneCurve K).localRingAt P :=
  haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  IsLocalization.ringEquivOfRingEquiv
    (M := (zChartMaximalIdeal W P).primeCompl)
    (T := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P).primeCompl)
    (S := Localization.AtPrime (zChartMaximalIdeal W P))
    (Q := (⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
    (coordRingToZSection W).symm
    (primeCompl_map_zChartMaximalIdeal W P)

/-- **(RP-3 transport, step 3 — the FF-compatibility square)** The localisation
transport agrees with the fixed function-field identification: composing
`zChartLocalizationEquiv` with the HasseWeil fraction-field embedding equals the
prime-to-nonZeroDivisors tower map followed by `projModelFunctionFieldEquiv`. Both are
localisation extensions of `coordRingToZSection.symm`, so they agree by extension
uniqueness (`IsLocalization.ringHom_ext` at the prime complement). -/
theorem zChartLocalizationEquiv_compat (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :
    haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
    haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
      Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
    haveI : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
      (coordRingToZSection W).toEquiv.symm.nontrivial
    haveI hNe : Nonempty (EllipticCurve.zChart W) :=
      ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
    haveI : IsFractionRing Γ(projModel W, EllipticCurve.zChart W) (projModel W).functionField :=
      functionField_isFractionRing_of_isAffineOpen (projModel W) (EllipticCurve.zChart W) hZaff
    haveI : IsDomain Γ(projModel W, EllipticCurve.zChart W) :=
      (coordRingToZSection W).symm.toMulEquiv.isDomain W.toAffine.CoordinateRing
    ((algebraMap ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
        (⟨W⟩ : SmoothPlaneCurve K).FunctionField).comp
      (zChartLocalizationEquiv W P).toRingHom) =
    ((EllipticCurve.projModelFunctionFieldEquiv W : _ →+* _).comp
      (IsLocalization.map (M := (zChartMaximalIdeal W P).primeCompl)
        (T := nonZeroDivisors Γ(projModel W, EllipticCurve.zChart W))
        ((projModel W).functionField) (RingHom.id _)
        (fun x hx => Ideal.primeCompl_le_nonZeroDivisors _ hx))) := by
  haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI : Nontrivial Γ(projModel W, EllipticCurve.zChart W) :=
    (coordRingToZSection W).toEquiv.symm.nontrivial
  haveI hNe : Nonempty (EllipticCurve.zChart W) :=
    ⟨hZaff.isoSpec.inv.base (Classical.arbitrary _)⟩
  haveI : IsFractionRing Γ(projModel W, EllipticCurve.zChart W) (projModel W).functionField :=
    functionField_isFractionRing_of_isAffineOpen (projModel W) (EllipticCurve.zChart W) hZaff
  haveI : IsDomain Γ(projModel W, EllipticCurve.zChart W) :=
    (coordRingToZSection W).symm.toMulEquiv.isDomain W.toAffine.CoordinateRing
  apply IsLocalization.ringHom_ext (zChartMaximalIdeal W P).primeCompl
  ext a
  simp [zChartLocalizationEquiv, IsLocalization.ringEquivOfRingEquiv_eq,
    EllipticCurve.projModelFunctionFieldEquiv, IsLocalization.map_eq]
  have h1 : (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
      (⟨W⟩ : SmoothPlaneCurve K).FunctionField)
        ((algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
          ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P))
            ((coordRingToZSection W).symm a)) =
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        (⟨W⟩ : SmoothPlaneCurve K).FunctionField)
          ((coordRingToZSection W).symm a) :=
    (IsScalarTower.algebraMap_apply _ _ _ _).symm
  refine h1.trans ?_
  -- Residual: `(IsLocalization.map_eq _ a).symm` — the six loc-instance implicits
  -- refuse to pin blind (stuck metavars even goal-anchored); LSP-session one-liner.
  sorry

/-- **(RP-3 transport, step 4a)** The scheme point of the Z-chart at a smooth point
`P`: the `fromSpec`-image of the transported maximal ideal. -/
noncomputable def zChartPoint (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) : projModel W :=
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  hZaff.fromSpec.base
    ⟨zChartMaximalIdeal W P, (zChartMaximalIdeal_isMaximal W P).isPrime⟩

/-- **(RP-3 transport, step 4)** The scheme stalk at `zChartPoint` is the localisation
of the chart sections at the transported maximal ideal — mathlib's
`isLocalization_stalk'` instantiated at the Z-chart. Composed with
`zChartLocalizationEquiv`, the stalk is HasseWeil's `localRingAt P`. -/
theorem isLocalization_stalk_zChartPoint (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint) :
    haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
      Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
    haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
    @IsLocalization.AtPrime
      (R := Γ(projModel W, EllipticCurve.zChart W))
      (S := (projModel W).presheaf.stalk (zChartPoint W P)) _ _
      ((TopCat.Presheaf.algebra_section_stalk (projModel W).presheaf _))
      (zChartMaximalIdeal W P) _ := by
  haveI hZaff : IsAffineOpen (EllipticCurve.zChart W) :=
    Proj.isAffineOpen_basicOpen _ _ (mk_X_mem_quotientGrading_one W 2) one_pos
  haveI := (zChartMaximalIdeal_isMaximal W P).isPrime
  exact hZaff.isLocalization_stalk'
    ⟨zChartMaximalIdeal W P, (zChartMaximalIdeal_isMaximal W P).isPrime⟩
    (by rw [← SetLike.mem_coe, ← hZaff.range_fromSpec]; exact Set.mem_range_self _)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- **(RP-4a)** A generator of the maximal ideal at a smooth point is a uniformizer:
its function-field image has `ord_P = 1`. Chain: the local-ring image generates the
DVR maximal ideal (`AtPrime` map-span), `intValuation_singleton` reads its integral
valuation as `exp (-1)`, `valuation_of_algebraMap` transports to the function field,
and the `ord_P` computation mirrors `exists_uniformizer`'s ending. -/
theorem uniformizer_of_span_maximalIdealAt (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (r : (⟨W⟩ : SmoothPlaneCurve K).CoordinateRing) (hr : r ≠ 0)
    (hspan : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P = Ideal.span {r}) :
    SmoothPlaneCurve.Uniformizer (⟨W⟩ : SmoothPlaneCurve K) P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) := by
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  haveI hDVR : IsDiscreteValuationRing
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) :=
    SmoothPlaneCurve.localRingAt.instIsDVR _ P
  haveI hPID := hDVR.toIsPrincipalIdealRing
  haveI hDed : IsDedekindDomain
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) := inferInstance
  have hr' : algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) r ≠ 0 := by
    intro h0
    exact hr (IsLocalization.injective
      (M := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P).primeCompl)
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
      (Ideal.primeCompl_le_nonZeroDivisors _) (h0.trans (map_zero _).symm))
  have hgen : (IsDiscreteValuationRing.maximalIdeal
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).asIdeal =
      Ideal.span {algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) r} := by
    show IsLocalRing.maximalIdeal _ = _
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine (congrArg (Ideal.map (algebraMap _ _)) hspan).trans ?_
    rw [Ideal.map_span, Set.image_singleton]
  have hval := IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
    (v := IsDiscreteValuationRing.maximalIdeal
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)) hr' hgen
  have htower : algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r =
      algebraMap ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField)
        (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
          ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) r) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  have hpv : (⟨W⟩ : SmoothPlaneCurve K).pointValuation P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [htower]
    show (IsDiscreteValuationRing.maximalIdeal
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).valuation
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) _ = _
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval]
    rfl
  have hne : (⟨W⟩ : SmoothPlaneCurve K).pointValuation P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) ≠ 0 := by
    rw [hpv]; exact WithZero.coe_ne_zero
  show (⟨W⟩ : SmoothPlaneCurve K).ord_P P _ = 1
  simp only [SmoothPlaneCurve.ord_P]
  rw [dif_neg hne]
  have hunz : WithZero.unzero hne = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero]
    exact hpv
  rw [hunz]
  rfl

/-- **(RP-4b)** The chart-side uniformizer law: a generator of the transported maximal
ideal `zChartMaximalIdeal` has `ord_P = 1` after passing through the fixed
function-field identification. Reduction to RP-4a along the chart equivalence
(span-roundtrip + the `ringEquivOfRingEquiv` computation rule). -/
theorem uniformizer_of_span_zChartMaximalIdeal (W : WeierstrassCurve K)
    [W.IsElliptic] (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (r' : Γ(projModel W, EllipticCurve.zChart W)) (hr' : r' ≠ 0)
    (hspan' : zChartMaximalIdeal W P = Ideal.span {r'}) :
    SmoothPlaneCurve.Uniformizer (⟨W⟩ : SmoothPlaneCurve K) P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField)
        ((coordRingToZSection W).symm r')) := by
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  refine uniformizer_of_span_maximalIdealAt W P ((coordRingToZSection W).symm r')
    (fun h0 => hr' (by simpa using congrArg (coordRingToZSection W) h0)) ?_
  have hround : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P =
      Ideal.map ((coordRingToZSection W).symm)
        (zChartMaximalIdeal W P) := by
    unfold zChartMaximalIdeal
    ext x
    constructor
    · intro hx
      have := Ideal.mem_map_of_mem (coordRingToZSection W) hx
      have h2 := Ideal.mem_map_of_mem ((coordRingToZSection W).symm) this
      simpa using h2
    · intro hx
      have hle : Ideal.map ((coordRingToZSection W).symm)
          (Ideal.map (coordRingToZSection W)
            ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P)) ≤
          (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P := by
        refine Ideal.map_le_iff_le_comap.mpr ?_
        refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
        simpa using ha
      exact hle hx
  rw [hround, hspan', Ideal.map_span, Set.image_singleton]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- **(RP-5 atom)** Away from the point: a coordinate function not in the maximal
ideal has `ord_P = 0`. Chain: its local-ring image lies in the prime complement
(`under_maximalIdeal` membership), so its integral valuation is `1`
(`intValuation_eq_one_iff_mem_primeCompl`), hence the point valuation is `1` and
`ord_P = 0` by the HasseWeil characterisation. -/
theorem ord_P_algebraMap_eq_zero_of_notMem (W : WeierstrassCurve K) [W.IsElliptic]
    (P : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (g : (⟨W⟩ : SmoothPlaneCurve K).CoordinateRing) (hg0 : g ≠ 0)
    (hg : g ∉ (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P) :
    (⟨W⟩ : SmoothPlaneCurve K).ord_P P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) g) = 0 := by
  haveI := ((⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt_isMaximal P).isPrime
  haveI hDVR : IsDiscreteValuationRing
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) :=
    SmoothPlaneCurve.localRingAt.instIsDVR _ P
  haveI hPID := hDVR.toIsPrincipalIdealRing
  haveI hDed : IsDedekindDomain
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) := inferInstance
  have hFFne : algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) g ≠ 0 := by
    intro h0
    exact hg0 (IsFractionRing.injective
      ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField)
      (h0.trans (map_zero _).symm))
  have hcompl : algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) g ∈
      (IsDiscreteValuationRing.maximalIdeal
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).asIdeal.primeCompl := by
    intro hmem
    refine hg ?_
    have hunder : g ∈ (IsLocalRing.maximalIdeal
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).under
        ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing) :=
      Ideal.mem_comap.mpr hmem
    rwa [Localization.AtPrime.under_maximalIdeal] at hunder
  have hval1 : (IsDiscreteValuationRing.maximalIdeal
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).intValuation
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P) g) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl
      (v := IsDiscreteValuationRing.maximalIdeal
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)) _).mpr hcompl
  have hpv1 : (⟨W⟩ : SmoothPlaneCurve K).pointValuation P
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) g) = 1 := by
    rw [IsScalarTower.algebraMap_apply
      ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
      ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) g]
    show (IsDiscreteValuationRing.maximalIdeal
        ((⟨W⟩ : SmoothPlaneCurve K).localRingAt P)).valuation
      ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) _ = 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hval1]
  exact (SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one
    (⟨W⟩ : SmoothPlaneCurve K) hFFne).mpr hpv1

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- **(RP-5, affine packaging)** A generator of the maximal ideal at `P₀` that lies in
no other point's maximal ideal has principal divisor exactly `[P₀]`: order one at the
point (RP-4a), zero everywhere else (the RP-5 atom). The affine half of the divisor
dictionary's `div r = (Q) − (O)`-pinning; the infinity part is the dataset's
normalisation content. -/
theorem divisorOf_algebraMap_eq_single (W : WeierstrassCurve K) [W.IsElliptic]
    (P₀ : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (r : (⟨W⟩ : SmoothPlaneCurve K).CoordinateRing) (hr : r ≠ 0)
    (hspan : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P₀ = Ideal.span {r})
    (hoff : ∀ Q : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint, Q ≠ P₀ →
      r ∉ (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt Q) :
    (⟨W⟩ : SmoothPlaneCurve K).divisorOf
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) =
      Finsupp.single P₀ 1 := by
  refine Finsupp.ext fun Q => ?_
  rw [SmoothPlaneCurve.divisorOf_apply]
  by_cases hQ : Q = P₀
  · subst hQ
    have h1 : (⟨W⟩ : SmoothPlaneCurve K).ord_P Q
        (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
          ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) = 1 :=
      uniformizer_of_span_maximalIdealAt W Q r hr hspan
    rw [h1]
    simp
  · have h0 : (⟨W⟩ : SmoothPlaneCurve K).ord_P Q
        (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
          ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) = 0 :=
      ord_P_algebraMap_eq_zero_of_notMem W Q r hr (hoff Q hQ)
    rw [h0]
    symm
    exact Finsupp.single_eq_of_ne hQ


/-- **(DIV-PIN separation)** Distinct smooth points have distinct maximal ideals:
containment of maximal ideals forces equality, and equality forces equal coordinates
through the quotient evaluations. -/
theorem eq_of_maximalIdealAt_le (W : WeierstrassCurve K) [W.IsElliptic]
    {P Q : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint}
    (h : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P ≤
      (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt Q) : P = Q := by
  have heq : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P =
      (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt Q :=
    ((SmoothPlaneCurve.maximalIdealAt_isMaximal _ P).eq_of_le
      (Ideal.IsMaximal.ne_top (SmoothPlaneCurve.maximalIdealAt_isMaximal _ Q)) h)
  sorry

/-- **(DIV-PIN, the affine pinning)** A generator of the maximal ideal at a point has
principal divisor `[P₀]`: the away-nonmembership follows from the span by maximal-ideal
separation. The chart-local form of `div r = (Q) − (O)`. -/
theorem divisorOf_algebraMap_eq_single_of_span (W : WeierstrassCurve K) [W.IsElliptic]
    (P₀ : (⟨W⟩ : SmoothPlaneCurve K).SmoothPoint)
    (r : (⟨W⟩ : SmoothPlaneCurve K).CoordinateRing) (hr : r ≠ 0)
    (hspan : (⟨W⟩ : SmoothPlaneCurve K).maximalIdealAt P₀ = Ideal.span {r}) :
    (⟨W⟩ : SmoothPlaneCurve K).divisorOf
      (algebraMap ((⟨W⟩ : SmoothPlaneCurve K).CoordinateRing)
        ((⟨W⟩ : SmoothPlaneCurve K).FunctionField) r) =
      Finsupp.single P₀ 1 := by
  refine divisorOf_algebraMap_eq_single W P₀ r hr hspan (fun Q hQ hmem => ?_)
  refine hQ (eq_of_maximalIdealAt_le W ?_).symm
  rw [hspan]
  exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)

end ModularCurves
