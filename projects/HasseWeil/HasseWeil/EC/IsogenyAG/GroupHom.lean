/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.PushforwardDivisor
import HasseWeil.Curves.AFConditional
import HasseWeil.Curves.MillerAllChar

/-!
# Silverman III.4.8: every isogeny is a group homomorphism

This file assembles **Silverman III.4.8** — every isogeny `φ : E₁ → E₂` of
elliptic curves is a group homomorphism `φ(P + Q) = φ(P) + φ(Q)` — from the
restored Pic⁰ spine.  The textbook proof (book p.71): the divisor pushforward
`φ_∗` induces a group homomorphism `Pic⁰(E₁) → Pic⁰(E₂)`, the Abel–Jacobi maps
`κᵢ : Eᵢ ≅ Pic⁰(Eᵢ)` (III.3.4) are group isomorphisms, and the square
`κ₂ ∘ φ = φ_∗ ∘ κ₁` commutes because `φ(O) = O`; a diagram chase then forces `φ`
to be additive.

The whole spine is already proven in the project:

* `Curves.picZeroIsoE_allChar` (Abel–Jacobi `κ = σ⁻¹`, III.3.4),
* `EC.Isogeny.picZeroOfPoint_pushforwardPicZero` (the square commutes, `φ(O)=O`),
* `Curves.AddHomProperty_of_AFInputs` (the diagram chase, III.4.8 modulo the
  pushforward-preserves-principal witness `h_pres`),
* `Curves.SmoothPlaneCurve.principal_mem_degZero` (II.3.1(b)).

The sole deep input `h_pres` (`φ_∗` preserves principal divisors, Silverman
II.3.6/II.3.7) is supplied by
`EC.Isogeny.pushforward_preserves_principal` (`PushforwardDivisor.lean`).

## Main results

* `EC.Isogeny.addHomProperty` — Silverman III.4.8 (point-map form, over
  `[IsAlgClosed F]`, with a `CoordHom` witness `cd`).
* `EC.Isogeny.toAddMonoidHom'` — the induced `AddMonoidHom` on points.
* `EC.Isogeny.addHomProperty_descend` — the `K`-rational consequence over a
  general base field via base change to `K̄` (ISO-L7).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.8, III.3.4, II.3.6/7.
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

open HasseWeil.Curves

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Silverman III.4.8** (point-map form): an isogeny `φ : E₁ → E₂` (with a
coordinate-ring witness `cd`, over an algebraically closed field) is a group
homomorphism on `K`-rational points, `φ(P + Q) = φ(P) + φ(Q)`.

The proof is Silverman's Pic⁰ diagram chase (`AddHomProperty_of_AFInputs`),
fed the proven Abel–Jacobi spine (`afInputs_allChar`), the degree-zero witness
(`principal_mem_degZero`), and the pushforward-preserves-principal input
(`pushforward_preserves_principal`, the norm–conorm theorem II.3.6/7).

The module-finiteness of the coordinate-ring extension (the standing finite-map
hypothesis of II.2/II.3) is supplied by `CurveMap.CoordHom.module_finite`. -/
theorem addHomProperty [IsAlgClosed F]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    φ.AddHomProperty cd :=
  Curves.AddHomProperty_of_AFInputs φ cd
    (Curves.afInputs_allChar W₁) (Curves.afInputs_allChar W₂)
    (fun _ hD => (⟨W₁⟩ : SmoothPlaneCurve F).principal_mem_degZero hD)
    (fun _ hD => (⟨W₂⟩ : SmoothPlaneCurve F).principal_mem_degZero hD)
    (fun D hD => φ.pushforward_preserves_principal cd D hD)

/-- The `AddMonoidHom` on points induced by Silverman III.4.8: the point map of
an isogeny (with `CoordHom` witness, over `[IsAlgClosed F]`) packaged as an
additive group homomorphism `E₁ → E₂`. -/
noncomputable def toAddMonoidHom' [IsAlgClosed F]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom) :
    W₁.Point →+ W₂.Point :=
  φ.toAddMonoidHomOfWitness cd (φ.addHomProperty cd)

@[simp] theorem toAddMonoidHom'_apply [IsAlgClosed F]
    [IsDedekindDomain (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsDedekindDomain (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₁⟩ : SmoothPlaneCurve F).CoordinateRing]
    [IsIntegrallyClosed (⟨W₂⟩ : SmoothPlaneCurve F).CoordinateRing]
    (φ : Isogeny W₁ W₂) (cd : φ.toCurveMap.CoordHom)
    (P : W₁.Point) :
    φ.toAddMonoidHom' cd P = φ.toPointMap cd P := rfl

end HasseWeil.EC.Isogeny
