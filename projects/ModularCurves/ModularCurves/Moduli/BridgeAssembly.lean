/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineSectionDoublingIdentity
import ModularCurves.ForMathlib.NegModelAffineSection
import ModularCurves.Moduli.E3DatumAssembly

/-!
# The bridge assembly: `3•σ = 0 ⟹ hdbl` (the hArb close)

**(STREAM-OMEGA 2026-07-17, CHARTER-O v10.316, the finish.)** `RING-DBL` +
KM's negation coordinate + coordinate injectivity turn the section-level `3`-torsion of
a marked section into the cleared doubling condition `hdbl`, which fires KM's
certificate (`ThreeTorsionRingCertificate`) into the two `isE3Datum_of_bridges`
bridge-Props — closing `Bootstrap:95`.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory WeierstrassCurve MvPolynomial

/-- The doubling coordinates satisfy the Weierstrass equation (universal transport;
the classifier block of `two_zsmul_affineSection`, landed on the `Equation`). -/
theorem equation_dblXY {A' : Type u} [CommRing A'] (W : WeierstrassCurve A')
    [W.IsElliptic] (p q e : A') (h : W.toAffine.Equation p q)
    (he : W.tangentDen p q * e = 1) :
    W.toAffine.Equation (W.dblX p q e) (W.dblY p q e) := by
  classical
  set ψ₀ : DblBase₀ →+* A' := MvPolynomial.eval₂Hom (Int.castRingHom A')
    (fun i : Fin 6 => ![W.a₁, W.a₂, W.a₃, W.a₄, p, q] i) with hψ₀def
  have hψX : ∀ i : Fin 6, ψ₀ (X i) = ![W.a₁, W.a₂, W.a₃, W.a₄, p, q] i :=
    fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have hWmap : dblW.map ψ₀ = W := by
    ext
    · exact (hψX 0)
    · exact (hψX 1)
    · exact (hψX 2)
    · exact (hψX 3)
    · show ψ₀ dblA₆ = W.a₆
      rw [dblA₆]
      simp only [map_add, map_sub, map_mul, map_pow, hψX]
      show q ^ 2 + W.a₁ * p * q + W.a₃ * q - p ^ 3 - W.a₂ * p ^ 2 - W.a₄ * p = W.a₆
      have hEq := (WeierstrassCurve.Affine.equation_iff _ _).mp h
      linear_combination hEq
  have hdenIm : ψ₀ (dblW.tangentDen (X 4) (X 5)) = W.tangentDen p q := by
    simp only [WeierstrassCurve.tangentDen, dblW, map_add, map_mul, map_ofNat, hψX]
    rfl
  have hloc : IsUnit (ψ₀ dblLoc) := by
    rw [show (dblLoc : DblBase₀) = dblW.tangentDen (X 4) (X 5) * dblW.Δ from rfl,
      map_mul, hdenIm]
    refine IsUnit.mul (isUnit_iff_exists_inv.mpr ⟨e, he⟩) ?_
    rw [show ψ₀ dblW.Δ = (dblW.map ψ₀).Δ from (WeierstrassCurve.map_Δ _ _).symm,
      hWmap]
    exact (WeierstrassCurve.isElliptic_iff W).mp inferInstance
  set φ₀ : DblRing₀ →+* A' := IsLocalization.Away.lift dblLoc hloc with hφ₀def
  set φ : DblRing.{u} →+* A' :=
    φ₀.comp ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀) : DblRing.{u} →+* DblRing₀)
    with hφdef
  letI : Algebra DblRing.{u} A' := φ.toAlgebra
  have halg : ∀ z : DblRing.{u}, algebraMap DblRing.{u} A' z = φ z := fun _ => rfl
  have hcomp : ∀ z : DblBase₀, φ (dblι z) = ψ₀ z := by
    intro z
    show φ₀ ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀)
      ((ULift.ringEquiv : DblRing.{u} ≃+* DblRing₀).symm
        (algebraMap DblBase₀ DblRing₀ z))) = ψ₀ z
    rw [RingEquiv.apply_symm_apply]
    exact IsLocalization.Away.lift_eq dblLoc hloc z
  have hWeq : dblWu.{u}.map (algebraMap DblRing.{u} A') = W := by
    rw [show (algebraMap DblRing.{u} A') = φ from rfl, dblWu,
      WeierstrassCurve.map_map,
      show φ.comp dblι = ψ₀ from RingHom.ext hcomp]
    exact hWmap
  have hPim : algebraMap DblRing.{u} A' dblPu = p := by
    rw [halg, dblPu, hcomp, hψX]
    rfl
  have hQim : algebraMap DblRing.{u} A' dblQu = q := by
    rw [halg, dblQu, hcomp, hψX]
    rfl
  have hdIm : algebraMap DblRing.{u} A' (dblWu.{u}.tangentDen dblPu dblQu)
      = W.tangentDen p q := by
    rw [halg, show dblWu.{u}.tangentDen dblPu dblQu
      = dblι (dblW.tangentDen (X 4) (X 5)) from dblWu_tangentDen_eq, hcomp, hdenIm]
  have hEim : algebraMap DblRing.{u} A' dblEu = e := by
    have hd2 : W.tangentDen p q * algebraMap DblRing.{u} A' dblEu = 1 := by
      have hh := congrArg (algebraMap DblRing.{u} A') dblEu_spec
      rw [map_mul, map_one, hdIm] at hh
      exact hh
    have hu : IsUnit (W.tangentDen p q) := isUnit_iff_exists_inv.mpr ⟨e, he⟩
    exact hu.mul_left_cancel (hd2.trans he.symm)
  have hXim : algebraMap DblRing.{u} A' (dblWu.{u}.dblX dblPu dblQu dblEu)
      = W.dblX p q e := by
    rw [← WeierstrassCurve.map_dblX dblWu.{u} (algebraMap DblRing.{u} A')
      dblPu dblQu dblEu, hPim, hQim, hEim, hWeq]
  have hYim : algebraMap DblRing.{u} A' (dblWu.{u}.dblY dblPu dblQu dblEu)
      = W.dblY p q e := by
    rw [← WeierstrassCurve.map_dblY dblWu.{u} (algebraMap DblRing.{u} A')
      dblPu dblQu dblEu, hPim, hQim, hEim, hWeq]
  have hEmap := WeierstrassCurve.Affine.Equation.map (algebraMap DblRing.{u} A')
    dblWu_equation_dbl
  rw [hXim, hYim] at hEmap
  rw [show dblWu.{u}.toAffine.map (algebraMap DblRing.{u} A')
      = W.toAffine from by rw [← hWeq]] at hEmap
  exact hEmap

/-- The clearing algebra: `dblX = p` clears to KM's `hdbl`. -/
theorem hdbl_of_dblX_eq {A' : Type*} [CommRing A'] (W : WeierstrassCurve A')
    (p q e : A') (he : W.tangentDen p q * e = 1)
    (hX : W.dblX p q e = p) :
    (W.tangentNum p q) ^ 2 + W.a₁ * (W.tangentNum p q) * (W.tangentDen p q)
      - (W.a₂ + 3 * p) * (W.tangentDen p q) ^ 2 = 0 := by
  have h := congrArg (fun z => z * (W.tangentDen p q) ^ 2) hX
  simp only [WeierstrassCurve.dblX, WeierstrassCurve.dblSlope,
    WeierstrassCurve.Affine.addX] at h
  rw [show W.toAffine.a₁ = W.a₁ from rfl, show W.toAffine.a₂ = W.a₂ from rfl] at h
  linear_combination h + (-(W.tangentNum p q) ^ 2 * (W.tangentDen p q) * e
      - (W.tangentNum p q) ^ 2
      - (W.tangentNum p q) * W.a₁ * (W.tangentDen p q)) * he

end ModularCurves
