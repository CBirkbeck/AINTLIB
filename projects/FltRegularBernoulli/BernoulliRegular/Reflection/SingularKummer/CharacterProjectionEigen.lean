module

public import BernoulliRegular.Reflection.SingularKummer.SingularRepresentative

/-!
# Singular Kummer: character projections are eigenspaces

This file proves the elementary eigenspace calculation for the character
projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a].
```

If an element lies in the range of this projection, then the action of
`b : Delta` on it is multiplication by `b^i`.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable {p : ℕ} [NeZero p]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- Reindexing coefficient identity for the `i`-th character. -/
theorem characterProjectionCoefficient_inv_mul
    (i : ℕ) (b a : Delta p) :
    characterProjectionCoefficient (p := p) i (b⁻¹ * a) =
      ((b : ZMod p) ^ i) * characterProjectionCoefficient (p := p) i a := by
  have hinv : (b⁻¹ * a)⁻¹ = a⁻¹ * b := by
    group
  rw [characterProjectionCoefficient, characterProjectionCoefficient, hinv]
  simp only [Units.val_mul]
  rw [mul_pow]
  ring

/-- The character projection is contained in the eigenspace for the
corresponding character. -/
theorem apply_characterProjection
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p) (x : M) :
    ρ b (characterProjection (p := p) i ρ x) =
      ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
  calc
    ρ b (characterProjection (p := p) i ρ x)
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ (b * a) x := by
          simp [characterProjection, projection, map_mul]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i (b⁻¹ * a) • ρ a x := by
          refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
          intro a
          simp [map_mul]
    _ = ((b : ZMod p) ^ i) • characterProjection (p := p) i ρ x := by
          simp [characterProjection, projection, characterProjectionCoefficient_inv_mul,
            smul_smul, Finset.smul_sum]

/-- Elementwise eigenspace statement for the range of the character
projection. -/
theorem mem_characterProjection_range_apply
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (b : Delta p)
    {x : M}
    (hx : x ∈ LinearMap.range (characterProjection (p := p) i ρ)) :
    ρ b x = ((b : ZMod p) ^ i) • x := by
  obtain ⟨y, rfl⟩ := hx
  exact apply_characterProjection (p := p) i ρ b y

end CharacterProjection

namespace SingularLinearAction
namespace SingularPair

variable (R K : Type*) [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Singular-quotient form of the character eigenspace relation.
If the additive class of `x` lies in the `i`-th projection range, then the
action of `b` on `x` is scalar multiplication by `(b : ZMod p)^i` after
passing to additive notation. -/
theorem singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)
    (b : CharacterProjection.Delta p)
    {x : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p}
    (hx :
      Additive.ofMul x ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS))) :
    Additive.ofMul (ρS b x) =
      ((b : ZMod p) ^ i) • Additive.ofMul x :=
  CharacterProjection.mem_characterProjection_range_apply
      (p := p) i (mulActionToAdditiveLinearAction (p := p) ρS) b hx

/-- Combined representative-and-eigen statement for the singular-Kummer argument.  From a
nontrivial projected component of `A[p]`, choose a singular pair `(I, alpha)`
with nontrivial class image, satisfying `(alpha) = I^p`, whose singular
quotient class lies in the `i`-th projection range and therefore satisfies the
corresponding eigenspace relation. -/
theorem exists_representative_with_eigen_relation_of_target_ne_bot
    (p : ℕ) [NeZero p] (i : ℕ)
    (ρS :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p ≃*
          SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)
    (ρA :
      CharacterProjection.Delta p →*
        SingularKummer.SingularPair.classGroupPTorsion (R := R) p ≃*
          SingularKummer.SingularPair.classGroupPTorsion (R := R) p)
    (hρ : ∀ (d : CharacterProjection.Delta p)
        (x : SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p),
      SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p (ρS d x) =
        ρA d (SingularKummer.SingularPair.singularGroupClassMapToPTorsion (R := R) (K := K) p x))
    (hA :
      LinearMap.range
        (CharacterProjection.characterProjection (p := p) i
          (mulActionToAdditiveLinearAction (p := p) ρA)) ≠ ⊥) :
    ∃ s : SingularKummer.SingularPair R K p,
      Additive.ofMul
          (QuotientGroup.mk s :
            SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p) ∈
        LinearMap.range
          (CharacterProjection.characterProjection (p := p) i
            (mulActionToAdditiveLinearAction (p := p) ρS)) ∧
      SingularKummer.SingularPair.classMapToPTorsion (R := R) (K := K) p s ≠ 1 ∧
      toPrincipalIdeal R K (SingularKummer.SingularPair.generator s) =
        SingularKummer.SingularPair.ideal s ^ p ∧
      ∀ b : CharacterProjection.Delta p,
        Additive.ofMul
            (ρS b
              (QuotientGroup.mk s :
                SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p)) =
          ((b : ZMod p) ^ i) •
            Additive.ofMul
              (QuotientGroup.mk s :
                SingularKummer.SingularPair.SingularGroup (R := R) (K := K) p) := by
  obtain ⟨s, hs_component, hs_nontrivial, hs_principal⟩ :=
    exists_representative_in_characterProjection_of_target_ne_bot
      (R := R) (K := K) p i ρS ρA hρ hA
  refine ⟨s, hs_component, hs_nontrivial, hs_principal, ?_⟩
  intro b
  exact
    singularGroup_additive_apply_eq_smul_of_mem_characterProjection_range
      (R := R) (K := K) p i ρS b hs_component

end SingularPair
end SingularLinearAction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
