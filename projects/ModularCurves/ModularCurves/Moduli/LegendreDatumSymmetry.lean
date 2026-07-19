/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLevelThree

/-!
# The `{±1}`-symmetry of Legendre data ([T-E14-ACT'] datum layer)

**(STREAM-OMEGA 2026-07-17, G0's :206 asks (2a).)** The Legendre-datum condition is
symmetric under the `{±1}`-action on the `ω`-basis: `IsLegendreDatum.neg` — a datum for
`(L, b)` is a datum for `(L, (-1) • b)`. Mechanism: the scaling variable change
`C = ⟨-1, 0, 0, 0⟩` fixes every Legendre curve (`a₁ = a₃ = 0`, and `a₂, a₄, a₆` scale
by even powers of `u`), fixes both markings (their `y`-coordinates vanish and
`r = s = t = 0`), and flips the adaptation unit by `C.u = -1`
(`basisUnitAt_ofVC` + `basisUnitAt_smul`), matching the basis flip.

This is one of the two fibre-pinning lemmas of the `±ω` scale-torsor over the level-2
locus (G0's `legendreDelta_relRep_finiteEtale_of_scaleTorsor` funnel for
`Bootstrap.lean:206`); the other (uniqueness-up-to-`±`) is tracked separately.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory Scheme LocalPresentation

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E14-ACT'] the `{±1}`-flip of a Legendre datum)** A Legendre datum for
`(L, b)` is one for `(L, (-1) • b)`: twist each witness chart by the scaling variable
change `⟨-1, 0, 0, 0⟩`. -/
theorem IsLegendreDatum.neg {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) :
    IsLegendreDatum X L ((-1 : Γ(X.base, ⊤)ˣ) • b) := by
  intro s
  obtain ⟨V, hsV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD s
  set C : WeierstrassCurve.VariableChange Γ(X.base, V.1) := ⟨-1, 0, 0, 0⟩ with hC
  have hWfix : C • Pr.W = legendreCurve lam := by
    rw [hW]
    ext <;>
      simp [hC, legendreCurve, WeierstrassCurve.variableChange_def, Units.val_neg,
        Units.val_one] <;>
      ring
  refine ⟨V, hsV, Pr.ofVC C, lam, ?_, ?_, ?_, ?_⟩
  · -- adaptation to the flipped basis
    show (((Pr.ofVC C).basisUnitAt _)).1 = 1
    rw [basisUnitAt_smul, basisUnitAt_ofVC, hAd]
    refine Units.ext ?_
    simp [hC, Scheme.resUnit_val]
  · -- the twisted chart curve is the same Legendre curve
    show C • Pr.W = legendreCurve lam
    exact hWfix
  · -- the `P`-marking at `(0, 0)` survives
    refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_zero lam
    · convert hMP using 2 <;> simp [hC]
  · -- the `Q`-marking at `(1, 0)` survives
    refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_one lam
    · convert hMQ using 2 <;> simp [hC]

open WeierstrassCurve in
/-- **([T-E14-ACT'] sublemma B1 — the genuine `μ₂`-on-`ω` stability)** For any global unit
`g` with `g² = 1`, rescaling the `ω`-basis by `g` preserves the Legendre-datum condition.
This generalises `IsLegendreDatum.neg` (the `g = -1` case) to the full `μ₂` factor: the
variable change `⟨g, 0, 0, 0⟩` scales the Weierstrass coefficients by `g⁻²`, `g⁻⁴`, `g⁻⁶`,
all `= 1` under `g² = 1`, so the chart curve stays `legendreCurve lam` and the markings
survive (the `x`-coordinates scale by `g² = 1`). Unlike the `GL₂(𝔽₂)` re-marking (which
needs a global `√`, see the `legendreDeltaGAction` B2), this `μ₂`-on-`ω` action is genuine
and global — it is the honest content of the `{±1}` factor. -/
theorem IsLegendreDatum.smul_of_sq_eq_one {R : CommRingCat.{u}} {X : EllObj R}
    {L : X.curve.FullLevelPt 2} {b : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (g : Γ(X.base, ⊤)ˣ) (hg : g ^ 2 = 1) :
    IsLegendreDatum X L (g • b) := by
  intro s
  obtain ⟨V, hsV, Pr, lam, hAd, hW, hMP, hMQ⟩ := hD s
  set gV : Γ(X.base, V.1)ˣ := Scheme.resUnit (le_top : V.1 ≤ ⊤) g with hgV
  have hgV2 : gV ^ 2 = 1 := by
    rw [hgV, ← map_pow, hg, map_one]
  set C : WeierstrassCurve.VariableChange Γ(X.base, V.1) := ⟨gV, 0, 0, 0⟩ with hC
  have hgVval2 : (gV : Γ(X.base, V.1)) ^ 2 = 1 := by
    have := congrArg (Units.val) hgV2
    simpa using this
  have hginv2 : (↑gV⁻¹ : Γ(X.base, V.1)) ^ 2 = 1 := by
    have : (gV⁻¹) ^ 2 = 1 := by rw [inv_pow, hgV2, inv_one]
    have := congrArg (Units.val) this
    simpa using this
  have h4 : (↑gV⁻¹ : Γ(X.base, V.1)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hginv2, one_pow]
  have hWfix : C • Pr.W = legendreCurve lam := by
    rw [hW]
    ext <;>
      simp [hC, legendreCurve, WeierstrassCurve.variableChange_def, hginv2, h4]
  refine ⟨V, hsV, Pr.ofVC C, lam, ?_, ?_, ?_, ?_⟩
  · show (((Pr.ofVC C).basisUnitAt _)).1 = 1
    rw [basisUnitAt_smul, basisUnitAt_ofVC, hAd]
    rw [mul_one]
    show gV * gV = 1
    rw [← sq]; exact hgV2
  · show C • Pr.W = legendreCurve lam
    exact hWfix
  · refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_zero lam
    · convert hMP using 2 <;> simp [hC]
  · refine LocalPresentation.MarksAt.ofVC Pr C ?_ ?_
    · rw [hWfix]
      exact legendreCurve_equation_one lam
    · convert hMQ using 2 <;> simp [hC, hgVval2]

open WeierstrassCurve in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- **([T-E14-ACT'] uniqueness up to `±`: the `μ₂`-torsor pinning)** Two Legendre data
for the same level structure compare by a global unit `g` (the `ω`-pseudotorsor) with
`g² = 1`: locally, the `g`-twisted second witness is adapted to the first basis, the
`ω`-datum + char-≠2 normal form pin the comparison to a pure translation
(`transVC_of_isAdapted_charNeTwo`), and the two markings kill the translation and force
`x(Q)`: `1 = (g⁻¹)²·1`. No connectedness hypothesis — this is exactly the `μ₂`-torsor
statement for G0's scale-torsor over the level-2 locus. -/
theorem IsLegendreDatum.unit_sq_eq_one {R : CommRingCat.{u}} {X : EllObj R}
    (h2 : IsUnit (2 : Γ(X.base, ⊤)))
    {L : X.curve.FullLevelPt 2} {b b' : OmegaBasis X.curve.toEllipticCurveGeom}
    (hD : IsLegendreDatum X L b) (hD' : IsLegendreDatum X L b')
    (g : Γ(X.base, ⊤)ˣ) (hg : g • b = b') :
    g ^ 2 = 1 := by
  have key : ∀ s : ↥X.base, ∃ U : X.base.affineOpens, s ∈ U.1 ∧
      Scheme.resUnit (le_top : U.1 ≤ ⊤) (g ^ 2) =
        Scheme.resUnit (le_top : U.1 ≤ ⊤) 1 := by
    intro s
    obtain ⟨V, hsV, P₁, lam₁, hAd₁, hW₁, hMP₁, hMQ₁⟩ := hD s
    obtain ⟨V', hsV', P₂, lam₂, hAd₂, hW₂, hMP₂, hMQ₂⟩ := hD' s
    obtain ⟨U₀, hU₀aff, hsU₀, hU₀le⟩ := exists_isAffineOpen_mem_and_subset
      (show s ∈ (V.1 ⊓ V'.1 : X.base.Opens) from ⟨hsV, hsV'⟩)
    set U : X.base.affineOpens := ⟨U₀, hU₀aff⟩ with hU
    have hle₁ : U.1 ≤ V.1 := le_trans hU₀le inf_le_left
    have hle₂ : U.1 ≤ V'.1 := le_trans hU₀le inf_le_right
    set gU : Γ(X.base, U.1)ˣ := Scheme.resUnit (le_top : U.1 ≤ ⊤) g with hgU
    set C₂ : VariableChange Γ(X.base, U.1) := ⟨gU, 0, 0, 0⟩ with hC₂
    -- restricted witnesses
    have hAd₁' : (P₁.restrict hle₁).IsAdapted b := hAd₁.restrict hle₁
    have hMP₁' : (P₁.restrict hle₁).MarksAt L.1.1.2 0 0 := by
      have h := hMP₁.restrict hle₁
      rwa [map_zero] at h
    have hMQ₁' : (P₁.restrict hle₁).MarksAt L.1.2.2 1 0 := by
      have h := hMQ₁.restrict hle₁
      rwa [map_one, map_zero] at h
    have hMP₂' : (P₂.restrict hle₂).MarksAt L.1.1.2 0 0 := by
      have h := hMP₂.restrict hle₂
      rwa [map_zero] at h
    have hMQ₂' : (P₂.restrict hle₂).MarksAt L.1.2.2 1 0 := by
      have h := hMQ₂.restrict hle₂
      rwa [map_one, map_zero] at h
    -- the restricted chart curves are Legendre
    have hWQ₁ : (P₁.restrict hle₁).W
        = legendreCurve (Scheme.resLE hle₁ lam₁) := by
      show P₁.W.map (sectionsMapLE (𝟙 X.base) (by simpa using hle₁)) = _
      rw [sectionsMapLE_id, hW₁]
      ext <;> simp [legendreCurve]
    have hWQ₂ : (P₂.restrict hle₂).W
        = legendreCurve (Scheme.resLE hle₂ lam₂) := by
      show P₂.W.map (sectionsMapLE (𝟙 X.base) (by simpa using hle₂)) = _
      rw [sectionsMapLE_id, hW₂]
      ext <;> simp [legendreCurve]
    -- the g-twist of the second witness is adapted to b
    have hAd₂'' : ((P₂.restrict hle₂).ofVC C₂).IsAdapted b := by
      show ((((P₂.restrict hle₂).ofVC C₂)).basisUnitAt b).1 = 1
      rw [basisUnitAt_ofVC]
      have h1 : (((P₂.restrict hle₂)).basisUnitAt (g • b)).1 = 1 := by
        rw [hg]
        exact hAd₂.restrict hle₂
      rw [basisUnitAt_smul] at h1
      exact h1
    -- normal forms
    have hNF₁ : (P₁.restrict hle₁).W.IsCharNeTwoNF := by
      rw [hWQ₁]
      exact ⟨rfl, rfl⟩
    have hNF₂' : (((P₂.restrict hle₂).ofVC C₂)).W.IsCharNeTwoNF := by
      show (C₂ • (P₂.restrict hle₂).W).IsCharNeTwoNF
      rw [hWQ₂]
      constructor
      · show (C₂ • legendreCurve (Scheme.resLE hle₂ lam₂)).a₁ = 0
        rw [WeierstrassCurve.variableChange_a₁]
        simp [hC₂]
      · show (C₂ • legendreCurve (Scheme.resLE hle₂ lam₂)).a₃ = 0
        rw [WeierstrassCurve.variableChange_a₃]
        simp [hC₂]
    -- the twisted markings
    obtain ⟨hEq00, -⟩ := id hMP₂'
    obtain ⟨hEq10, -⟩ := id hMQ₂'
    have hMP₂'' : (((P₂.restrict hle₂)).ofVC C₂).MarksAt L.1.1.2
        (C₂.vcX 0) (C₂.vcY 0 0) := by
      refine LocalPresentation.MarksAt.ofVC _ C₂
        (C₂.equation_smul (P₂.restrict hle₂).W hEq00) ?_
      convert hMP₂' using 2
      · simp [WeierstrassCurve.VariableChange.vcX, hC₂, ← mul_assoc, ← mul_pow]
      · simp [WeierstrassCurve.VariableChange.vcX,
          WeierstrassCurve.VariableChange.vcY, hC₂, ← mul_assoc, ← mul_pow]
    have hMQ₂'' : (((P₂.restrict hle₂)).ofVC C₂).MarksAt L.1.2.2
        (C₂.vcX 1) (C₂.vcY 1 0) := by
      refine LocalPresentation.MarksAt.ofVC _ C₂
        (C₂.equation_smul (P₂.restrict hle₂).W hEq10) ?_
      convert hMQ₂' using 2
      · simp [WeierstrassCurve.VariableChange.vcX, hC₂, ← mul_assoc, ← mul_pow]
      · simp [WeierstrassCurve.VariableChange.vcX,
          WeierstrassCurve.VariableChange.vcY, hC₂, ← mul_assoc, ← mul_pow]
    -- the b-adapted char-≠2 comparison is a pure translation
    have h2U : IsUnit (2 : Γ(X.base, U.1)) := by
      have h := h2.map (Scheme.resLE (le_top : U.1 ≤ ⊤))
      rwa [map_ofNat] at h
    have hCval := transVC_of_isAdapted_charNeTwo hAd₁' hAd₂'' hNF₁ hNF₂' h2U
    -- the two marking chases
    obtain ⟨hxP, -⟩ := e3_markChase hMP₁' hMP₂''
    obtain ⟨hxQ, -⟩ := e3_markChase hMQ₁' hMQ₂''
    have hu : (((P₁.restrict hle₁).transVC (((P₂.restrict hle₂)).ofVC C₂)).u :
        Γ(X.base, U.1)) = 1 := by
      rw [hCval]
      rfl
    -- combine: `1 = (g⁻¹)²`
    rw [hu] at hxP hxQ
    have hval : ((gU⁻¹ : Γ(X.base, U.1)ˣ) : Γ(X.base, U.1)) ^ 2 = 1 := by
      simp only [WeierstrassCurve.VariableChange.vcX, hC₂] at hxP hxQ
      linear_combination hxP - hxQ
    have hgU2 : gU ^ 2 = 1 := by
      have hinv : (gU⁻¹ : Γ(X.base, U.1)ˣ) ^ 2 = 1 := by
        refine Units.ext ?_
        rw [Units.val_pow_eq_pow_val, hval, Units.val_one]
      rw [inv_pow] at hinv
      exact inv_eq_one.mp hinv
    refine ⟨U, hsU₀, ?_⟩
    rw [map_pow, map_one]
    rw [show Scheme.resUnit (le_top : U.1 ≤ ⊤) g = gU from rfl, hgU2]
  choose Us hUs hres using key
  refine Scheme.unit_ext_of_res_cover X.base (fun s => (Us s).1)
    (fun s => le_top) ?_ hres
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hUs x⟩


end ModularCurves
