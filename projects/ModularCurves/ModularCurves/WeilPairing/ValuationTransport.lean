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

end ModularCurves
