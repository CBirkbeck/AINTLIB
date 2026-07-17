/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.UniversalLegendre

/-!
# The general ring-level negation coordinate (KM CHARTER-K / K1, a RING-DBL leaf)

**[KM-W0 / hArb RING-DBL support]** The model negation `negModelHom` sends the affine-point
section `[p : q : 1]` to the affine-point section `[p : negY p q : 1]`, over ANY commutative
ring. This generalises `negModelHom_affineSection` (which required the `2`-torsion symmetry
`negY p q = q`) to arbitrary marked points — the version the `3`-torsion bridges need, since
a `3`-torsion point is never `2`-torsion so `negY p q ≠ q` in general.

Used in the `RING-DBL` chain: `3•σ = 0 ⟹ 2•σ = −σ`, and `−σ = affineSection(p, negY p q)`
by this lemma, so the doubling-equals-negation abscissa comparison closes via
`projModelAffineSection_injective`.
-/

universe u

noncomputable section

namespace ModularCurves

open AlgebraicGeometry CategoryTheory HomogeneousIdeal HomogeneousLocalization

open WeierstrassCurve

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- **(RING-DBL leaf)** The model negation on a general affine-point section: it lands at the
negated `y`-coordinate `negY p q = −q − a₁p − a₃`. -/
theorem negModelHom_affineSection_general {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    (p q : A) (h : W.toAffine.Equation p q) :
    projModelAffineSection W p q h ≫ negModelHom W =
      projModelAffineSection W p (W.toAffine.negY p q)
        ((W.toAffine.equation_neg p q).mpr h) := by
  have hfeq : ((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W p q h)).comp (negGradedQuot W).toRingHom =
      (Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W p (W.toAffine.negY p q)
          ((W.toAffine.equation_neg p q).mpr h)) := by
    refine RingHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine congrArg (Scheme.ΓSpecIso (.of A)).inv.hom ?_
    rw [show (negGradedQuot W).toRingHom (Ideal.Quotient.mk (projIdeal W).toIdeal a) =
      Ideal.Quotient.mk (projIdeal W).toIdeal (MvPolynomial.aeval (negVec W) a) from
      quotientGradingMap_mk _ _ _ _ a]
    rw [projModelAffineEval_mk, projModelAffineEval_mk]
    rw [show (MvPolynomial.aeval (negVec W) a :
        MvPolynomial (Fin 3) A) = MvPolynomial.bind₁ (negVec W) a from by
      rw [MvPolynomial.aeval_eq_bind₁]]
    rw [show MvPolynomial.eval ![p, q, 1] (MvPolynomial.bind₁ (negVec W) a) =
      MvPolynomial.eval (fun i => MvPolynomial.eval ![p, q, 1] (negVec W i)) a from by
      rw [← MvPolynomial.aeval_eq_eval, MvPolynomial.aeval_bind₁]
      rfl]
    refine congrArg (fun v => MvPolynomial.eval v a) ?_
    funext i
    fin_cases i
    · simp [negVec]
    · show MvPolynomial.eval ![p, q, 1] (-MvPolynomial.X 1 -
        MvPolynomial.C W.a₁ * MvPolynomial.X 0 -
        MvPolynomial.C W.a₃ * MvPolynomial.X 2) = W.toAffine.negY p q
      simp only [MvPolynomial.eval_sub, MvPolynomial.eval_neg, MvPolynomial.eval_mul,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      show -q - W.a₁ * p - W.a₃ * 1 = W.toAffine.negY p q
      rw [WeierstrassCurve.Affine.negY]
      ring
    · simp [negVec]
  have key := Proj.fromOfGlobalSections_map (negGradedQuot W)
    (negGradedQuot_irrelevant_le W)
    ((Scheme.ΓSpecIso (.of A)).inv.hom.comp (projModelAffineEval W p q h))
    (projModelAffineEval_irrelevant_map_top W p q h)
    (Proj.irrelevant_map_comp_toRingHom_eq_top (negGradedQuot W)
      (negGradedQuot_irrelevant_le W) _
      (projModelAffineEval_irrelevant_map_top W p q h))
  have congr_from : ∀ (g₁ g₂ : projCoordRing W →+* Γ(Spec (.of A), ⊤))
      (h₁ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₁ = ⊤)
      (h₂ : (HomogeneousIdeal.irrelevant
          (quotientGrading (projIdeal W))).toIdeal.map g₂ = ⊤)
      (hg : g₁ = g₂),
      Proj.fromOfGlobalSections _ g₁ h₁ = Proj.fromOfGlobalSections _ g₂ h₂ := by
    rintro g₁ g₂ h₁ h₂ rfl
    rfl
  rw [show projModelAffineSection W p q h ≫ negModelHom W =
    Proj.fromOfGlobalSections _
      (((Scheme.ΓSpecIso (.of A)).inv.hom.comp
        (projModelAffineEval W p q h)).comp (negGradedQuot W).toRingHom)
      (Proj.irrelevant_map_comp_toRingHom_eq_top (negGradedQuot W)
        (negGradedQuot_irrelevant_le W) _
        (projModelAffineEval_irrelevant_map_top W p q h)) from key]
  exact congr_from _ _ _ _ hfeq

end ModularCurves
