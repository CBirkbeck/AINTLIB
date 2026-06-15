import HasseWeil.WeilPairing.Fiber
import HasseWeil.Curves.PicZero

/-!
# Route 2A — the multiplicity-free geometric divisor pullback (keystone)

For a **separable** point-map endomorphism `f` (étale fibres, `e = 1`), the pullback divisor is
the mult-1 fibre sum `f*((Q)) = Σ_{fP=Q} (P)`. This is the central new object of the Weil-pairing
route — the same divisor pullback Route 1 lacked, now in the multiplicity-free regime — used by
both the pairing construction (`div g = [ℓ]*((T)) − [ℓ]*((O))`) and the separable adjoint
(Silverman III.8.2's function `h`).

This file ships the definition and its **degree**: `deg(f*((Q))) = #fibre = #ker f` (Silverman
III.4.10c, the separable case). The `σ`-bridge and the addition-formula linkage are downstream.
-/

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false

open WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

omit [DecidableEq F] [W.IsElliptic] in
/-- Degree of a single projective place `(P)` with multiplicity `n` is `n`. -/
theorem degree_single (P : Curves.ProjectiveSmoothPoint (⟨W⟩ : Curves.SmoothPlaneCurve F)) (n : ℤ) :
    Curves.ProjectiveDivisor.degree (Finsupp.single P n) = n := by
  unfold Curves.ProjectiveDivisor.degree
  exact Finsupp.sum_single_index rfl

/-- **The multiplicity-free geometric pullback divisor** `f*((Q)) = Σ_{fP=Q} (P)`, summed over the
(finite) fibre. Each fibre point carries multiplicity `1` (the separable/étale case). -/
noncomputable def pullbackDiv (f : W.Point →+ W.Point) (h : Finite f.ker) (Q : W.Point) :
    Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F) :=
  letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
  ∑ P : {P : W.Point // f P = Q}, Finsupp.single P.val.toProjectiveSmoothPoint (1 : ℤ)

/-- **Degree of the mult-1 pullback** (Silverman III.4.10c, separable): `deg(f*((Q))) = #ker f`. -/
theorem degree_pullbackDiv (f : W.Point →+ W.Point) (h : Finite f.ker) {P₀ Q : W.Point}
    (hP₀ : f P₀ = Q) : (pullbackDiv f h Q).degree = Nat.card f.ker := by
  letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
  rw [pullbackDiv, ← Curves.ProjectiveDivisor.degreeHom_apply, map_sum]
  simp only [Curves.ProjectiveDivisor.degreeHom_apply, degree_single, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, fiber_card_eq_ker_card f hP₀]

/-- **The `σ`-section of the pullback divisor:** `σ(f*((Q))) = Σ_{fP=Q} P` (the group sum of the
fibre). The start of the III.6.1(b) `σ`-bridge `σ(f*((Q))−f*((O))) = f̂(Q)`. -/
theorem projectiveDivisorSum_pullbackDiv (f : W.Point →+ W.Point) (h : Finite f.ker) (Q : W.Point) :
    letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
    Curves.projectiveDivisorSum W (pullbackDiv f h Q) = ∑ P : {P : W.Point // f P = Q}, P.val := by
  letI : Fintype {P : W.Point // f P = Q} := @Fintype.ofFinite _ (fiber_finite f h Q)
  rw [pullbackDiv, ← Curves.projectiveDivisorSumHom_apply, map_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [Curves.projectiveDivisorSumHom_apply, Curves.projectiveDivisorSum_single, one_zsmul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint]

end HasseWeil.WeilPairing
