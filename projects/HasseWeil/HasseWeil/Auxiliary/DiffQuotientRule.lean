import HasseWeil.InvariantDifferential
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Derivation Calculus for Function Fields of Elliptic Curves

Quotient rule and inverse rule for the universal derivation.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (E : Affine F) [E.IsElliptic]

local notation "KE" => E.FunctionField

omit [DecidableEq F] in
/-- `D(f⁻¹) = -f⁻² • D(f)` for nonzero `f ∈ K(E)`. -/
theorem D_inv_smul (f : KE) (hf : f ≠ 0) :
    KaehlerDifferential.D F KE f⁻¹ =
      -(f⁻¹ ^ 2 • KaehlerDifferential.D F KE f) := by
  set D := KaehlerDifferential.D F KE
  have h1 : f * f⁻¹ = 1 := mul_inv_cancel₀ hf
  have h2 : D (f * f⁻¹) = 0 := by rw [h1, Derivation.map_one_eq_zero]
  rw [Derivation.leibniz] at h2
  have h3 : f • D f⁻¹ = -(f⁻¹ • D f) := eq_neg_of_add_eq_zero_left h2
  calc D f⁻¹
      = f⁻¹ • (f • D f⁻¹) := by rw [smul_smul, inv_mul_cancel₀ hf, one_smul]
    _ = f⁻¹ • (-(f⁻¹ • D f)) := by rw [h3]
    _ = -(f⁻¹ ^ 2 • D f) := by rw [smul_neg, smul_smul, ← sq]

omit [DecidableEq F] in
/-- `D(f * g⁻¹) = g⁻¹ • D(f) + (stuff involving D(g))`. Leibniz + inverse rule. -/
theorem D_mul_inv_smul (f g : KE) (hg : g ≠ 0) :
    KaehlerDifferential.D F KE (f * g⁻¹) =
      g⁻¹ • KaehlerDifferential.D F KE f +
      f • (-(g⁻¹ ^ 2 • KaehlerDifferential.D F KE g)) := by
  set D := KaehlerDifferential.D F KE
  rw [Derivation.leibniz, D_inv_smul E g hg, add_comm]

end HasseWeil
