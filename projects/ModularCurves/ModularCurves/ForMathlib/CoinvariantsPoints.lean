import ModularCurves.ForMathlib.CoactionCharpoly
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Points of the co-invariants: surjectivity

Construction support for `[CHARTER-HOPF]` / `T-G3d-infra` Piece 3
(`.mathlib-quality/decomposition-hopf-crux.md`, leaf `[HG-B4]`; Stacks
`groupoids-lemma-points`, tag 03BL): the easy half — `Spec B → Spec (coinvariants ρ)` is
surjective, because `B` is integral over the co-invariants (`isIntegral_coinvariants`,
03BJ) and the inclusion is injective, so lying-over applies.

The hard half of 03BL — the `k̄`-points orbit theorem and the finitely-many-maximals
corollary — is the next increment of this file.
-/

open scoped TensorProduct

namespace ModularCurves

variable (R A : Type*) [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Module.Free R A] [Module.Finite R A]
variable {B : Type*} [CommRing B] [Algebra R B]

/-- The co-invariants inclusion is an integral algebra (03BJ, instance-shaped). -/
theorem isIntegral_algebra_coinvariants (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ) :
    Algebra.IsIntegral (coinvariants ρ) B :=
  ⟨fun f => isIntegral_coinvariants R A ρ hρ f⟩

/-- **03BL, surjectivity half**: every prime of the co-invariants is the restriction of a
prime of `B` — lying-over along the integral, injective inclusion. -/
theorem exists_prime_over_coinvariants (ρ : B →ₐ[R] B ⊗[R] A) (hρ : IsCoaction ρ)
    (p : Ideal (coinvariants ρ)) [p.IsPrime] :
    ∃ q : Ideal B, q.IsPrime ∧ Ideal.comap (algebraMap (coinvariants ρ) B) q = p := by
  haveI := isIntegral_algebra_coinvariants R A ρ hρ
  obtain ⟨q, -, hq, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p ⊥ (by
    rw [Ideal.comap_bot_of_injective (algebraMap (coinvariants ρ) B)
      (Subtype.val_injective)]
    exact bot_le)
  exact ⟨q, hq, hcomap⟩

end ModularCurves
