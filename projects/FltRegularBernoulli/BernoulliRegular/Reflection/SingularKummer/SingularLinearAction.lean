module

public import BernoulliRegular.Reflection.SingularKummer.SingularZMod

/-!
# Singular Kummer: multiplicative actions as additive `ZMod p`-linear actions

This file converts multiplicative automorphism actions on `p`-torsion
commutative groups into additive `ZMod p`-linear actions.  Applied to the
singular exact sequence, multiplicative equivariance of `S → A[p]` becomes
linear equivariance of the corresponding `ZMod p`-linear map.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace SingularLinearAction

variable {p : ℕ}
variable {G H D : Type*} [CommGroup G] [CommGroup H] [Monoid D]
variable [Module (ZMod p) (Additive G)] [Module (ZMod p) (Additive H)]

/-- A multiplicative equivalence between `p`-torsion commutative groups is
`ZMod p`-linear after passing to additive notation. -/
def mulEquivToAdditiveZModLinearEquiv (e : G ≃* H) :
    Additive G ≃ₗ[ZMod p] Additive H :=
  { e.toMonoidHom.toAdditive.toZModLinearMap p with
    invFun := e.symm.toMonoidHom.toAdditive
    left_inv := by
      intro x
      apply Additive.ext
      simp
    right_inv := by
      intro y
      apply Additive.ext
      simp }

@[simp]
theorem mulEquivToAdditiveZModLinearEquiv_apply_toMul
    (e : G ≃* H) (x : Additive G) :
    (mulEquivToAdditiveZModLinearEquiv (p := p) e x).toMul = e x.toMul :=
  rfl

/-- A multiplicative action by automorphisms gives a linear action after
passing to additive notation. -/
def mulActionToAdditiveLinearAction (ρ : D →* G ≃* G) :
    D →* Additive G ≃ₗ[ZMod p] Additive G where
  toFun d := mulEquivToAdditiveZModLinearEquiv (p := p) (ρ d)
  map_one' := by
    ext x
    change (ρ 1) x.toMul = x.toMul
    simp
  map_mul' a b := by
    ext x
    change (ρ (a * b)) x.toMul = ((ρ a) * (ρ b)) x.toMul
    rw [map_mul]

@[simp]
theorem mulActionToAdditiveLinearAction_apply_toMul
    (ρ : D →* G ≃* G) (d : D) (x : Additive G) :
    (mulActionToAdditiveLinearAction (p := p) ρ d x).toMul =
      ρ d x.toMul :=
  rfl

/-- Multiplicative equivariance becomes linear equivariance after passing to
additive `ZMod p`-modules. -/
theorem linear_equivariant_of_multiplicative_equivariant
    (φ : G →* H) (ρG : D →* G ≃* G) (ρH : D →* H ≃* H)
    (hφ : ∀ (d : D) (x : G), φ (ρG d x) = ρH d (φ x))
    (d : D) (x : Additive G) :
    φ.toAdditive.toZModLinearMap p
        (mulActionToAdditiveLinearAction (p := p) ρG d x) =
      mulActionToAdditiveLinearAction (p := p) ρH d
        (φ.toAdditive.toZModLinearMap p x) := by
  apply Additive.ext
  change φ (ρG d x.toMul) = ρH d (φ x.toMul)
  exact hφ d x.toMul

namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Singular-sequence specialization of the multiplicative-to-linear
equivariance conversion. -/
theorem singular_linearMap_equivariant_of_multiplicative_equivariant
    (p : ℕ) (D : Type*) [Monoid D]
    (ρS :
      D →*
        SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularPair.SingularGroup (R := R) (K := K) p)
    (ρA :
      D →*
        SingularPair.classGroupPTorsion (R := R) p ≃*
          SingularPair.classGroupPTorsion (R := R) p)
    (hρ : ∀ (d : D) (x : SingularPair.SingularGroup (R := R) (K := K) p),
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (ρS d x) =
        ρA d (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (d : D)
    (x : Additive (SingularPair.SingularGroup (R := R) (K := K) p)) :
    SingularPair.singularGroupClassMapToPTorsionLinear (R := R) (K := K) p
        (mulActionToAdditiveLinearAction (p := p) ρS d x) =
      mulActionToAdditiveLinearAction (p := p) ρA d
        (SingularPair.singularGroupClassMapToPTorsionLinear (R := R) (K := K) p x) :=
  linear_equivariant_of_multiplicative_equivariant
    (p := p)
    (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p)
    ρS ρA hρ d x

/-- Character-projection range surjectivity for the linearized singular map,
assuming the corresponding multiplicative `Delta`-equivariance. -/
theorem singular_characterProjection_range_eq_range_of_multiplicative_equivariant
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularPair.SingularGroup (R := R) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        SingularPair.classGroupPTorsion (R := R) p ≃*
          SingularPair.classGroupPTorsion (R := R) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularPair.SingularGroup (R := R) (K := K) p),
      SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (ρS d x) =
        ρA d (SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x)) :
    Submodule.map
        (SingularPair.singularGroupClassMapToPTorsionLinear (R := R) (K := K) p)
        (LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS))) =
      LinearMap.range
        (CharacterProjection.characterProjection (p := p) i
          (mulActionToAdditiveLinearAction (p := p) ρA)) :=
  CharacterProjection.map_characterProjection_range_eq_range_of_surjective
    (p := p) i
    (mulActionToAdditiveLinearAction (p := p) ρS)
    (mulActionToAdditiveLinearAction (p := p) ρA)
    (SingularPair.singularGroupClassMapToPTorsionLinear (R := R) (K := K) p)
    (SingularPair.singularGroupClassMapToPTorsionLinear_surjective (R := R) (K := K) p)
    (fun d x =>
      singular_linearMap_equivariant_of_multiplicative_equivariant
        (R := R) (K := K) p (CharacterProjection.Delta p) ρS ρA hρ d x)

end SingularPair

end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
