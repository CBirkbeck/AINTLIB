module

public import BernoulliRegular.Reflection.SingularKummer.CharacterProjection

/-!
# Singular Kummer: `ZMod p` structures on the singular exact sequence

The singular quotient `S` is killed by `p`: for a singular pair
`(I, alpha)` with `(alpha) = I^p`, the `p`-th power of the pair is the
principal pair attached to `alpha`, hence trivial in the quotient by principal
pairs.  The target `A[p]` is killed by `p` by definition.

After passing to additive notation, both sides become `ZMod p`-modules and the
map `S → A[p]` becomes a surjective `ZMod p`-linear map.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `p`-th power of a singular pair is the principal pair attached to its
generator. -/
theorem pow_eq_principalPair_generator (p : ℕ) (s : SingularPair R K p) :
    s ^ p = principalPair (R := R) (K := K) p (generator s) := by
  apply Subtype.ext
  apply Prod.ext
  · change ideal s ^ p = toPrincipalIdeal R K (generator s)
    exact (principal_eq_ideal_pow (R := R) (K := K) s).symm
  · change generator s ^ p = generator s ^ p
    rfl

/-- The image of a singular pair in the singular quotient is killed by `p`. -/
theorem singularGroup_mk_pow_eq_one (p : ℕ) (s : SingularPair R K p) :
    ((QuotientGroup.mk s : SingularGroup (R := R) (K := K) p) ^ p) = 1 := by
  rw [← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff
    (N := principalPairSubgroup (R := R) (K := K) p) (s ^ p)).2
      ⟨generator s, (pow_eq_principalPair_generator (R := R) (K := K) p s).symm⟩

/-- Every element of the singular quotient is killed by `p`. -/
theorem singularGroup_pow_eq_one (p : ℕ)
    (x : SingularGroup (R := R) (K := K) p) :
    x ^ p = 1 := by
  refine QuotientGroup.induction_on x ?_
  intro s
  exact singularGroup_mk_pow_eq_one (R := R) (K := K) p s

/-- Every element of `A[p]` is killed by `p`, by definition. -/
theorem classGroupPTorsion_pow_eq_one (p : ℕ)
    (x : classGroupPTorsion (R := R) p) :
    x ^ p = 1 :=
  Subtype.ext <| show (x.1 ^ p = 1) from x.2

/-- Additive `ZMod p`-module structure on the singular quotient. -/
instance instModuleZModAdditiveSingularGroup (p : ℕ) :
    Module (ZMod p) (Additive (SingularGroup (R := R) (K := K) p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact singularGroup_pow_eq_one (R := R) (K := K) p x.toMul

/-- Additive `ZMod p`-module structure on `A[p]`. -/
instance instModuleZModAdditiveClassGroupPTorsion (p : ℕ) :
    Module (ZMod p) (Additive (classGroupPTorsion (R := R) p)) :=
  AddCommGroup.zmodModule (n := p) fun x => by
    apply Additive.ext
    rw [toMul_nsmul, toMul_zero]
    exact classGroupPTorsion_pow_eq_one (R := R) p x.toMul

/-- The singular quotient map as a `ZMod p`-linear map after passing to
additive notation. -/
def singularGroupClassMapToPTorsionLinear (p : ℕ) :
    Additive (SingularGroup (R := R) (K := K) p) →ₗ[ZMod p]
      Additive (classGroupPTorsion (R := R) p) :=
  (singularGroupClassMapToPTorsion (R := R) (K := K) p).toAdditive.toZModLinearMap p

@[simp]
theorem singularGroupClassMapToPTorsionLinear_apply_toMul (p : ℕ)
    (x : Additive (SingularGroup (R := R) (K := K) p)) :
    (singularGroupClassMapToPTorsionLinear (R := R) (K := K) p x).toMul =
      singularGroupClassMapToPTorsion (R := R) (K := K) p x.toMul :=
  rfl

/-- The linearized singular quotient map is surjective. -/
theorem singularGroupClassMapToPTorsionLinear_surjective (p : ℕ) :
    Function.Surjective
      (singularGroupClassMapToPTorsionLinear (R := R) (K := K) p) := by
  intro y
  obtain ⟨x, hx⟩ :=
    singularGroupClassMapToPTorsion_surjective (R := R) (K := K) p y.toMul
  refine ⟨Additive.ofMul x, ?_⟩
  exact Additive.ext <| hx

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end

end
