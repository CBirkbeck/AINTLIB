module

public import BernoulliRegular.Reflection.SingularKummer.IntegralCharacterProjection

/-!
# Singular Kummer: idempotence of character projections

The character projection

```text
  e_i = |Delta|^{-1} sum_a a^{-i} [a]
```

acts as the identity on its own range as soon as `|Delta|` is invertible in the
coefficient ring `ZMod p`.  This is the algebraic fact needed to recognize the
torsion in the range of the integral lift as lying in the corresponding
projected component of `A[p]`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace CharacterProjection

variable {p : ℕ} [NeZero p]
variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

theorem characterProjectionCoefficient_mul_pow
    (i : ℕ) (a : Delta p) :
    characterProjectionCoefficient (p := p) i a * ((a : ZMod p) ^ i) =
      (Fintype.card (Delta p) : ZMod p)⁻¹ := by
  have hmul : ((a⁻¹ : Delta p) : ZMod p) * (a : ZMod p) = 1 := by
    change (((a⁻¹ : Delta p) * a : Delta p) : ZMod p) = 1
    simp
  rw [characterProjectionCoefficient, mul_assoc, ← mul_pow, hmul, one_pow, mul_one]

/-- A character projection acts as the identity on its range, provided
`|Delta|` is invertible in `ZMod p`. -/
theorem characterProjection_apply_eq_self_of_mem_range
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M)
    {x : M}
    (hx : x ∈ LinearMap.range (characterProjection (p := p) i ρ)) :
    characterProjection (p := p) i ρ x = x := by
  calc
    characterProjection (p := p) i ρ x
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ a x := by
          simp [characterProjection, projection]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a •
              (((a : ZMod p) ^ i) • x) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [mem_characterProjection_range_apply (p := p) i ρ a hx]
    _ = ∑ a : Delta p,
            (Fintype.card (Delta p) : ZMod p)⁻¹ • x := by
          simp [smul_smul, characterProjectionCoefficient_mul_pow]
    _ = ((Fintype.card (Delta p) : ZMod p) *
            (Fintype.card (Delta p) : ZMod p)⁻¹) • x := by
          rw [Finset.sum_const]
          change Fintype.card (Delta p) •
              ((Fintype.card (Delta p) : ZMod p)⁻¹ • x) =
            ((Fintype.card (Delta p) : ZMod p) *
              (Fintype.card (Delta p) : ZMod p)⁻¹) • x
          rw [← Nat.cast_smul_eq_nsmul (ZMod p)
            (Fintype.card (Delta p))
            ((Fintype.card (Delta p) : ZMod p)⁻¹ • x)]
          rw [smul_smul]
    _ = x := by
          have hmul :
              (Fintype.card (Delta p) : ZMod p) *
                (Fintype.card (Delta p) : ZMod p)⁻¹ = 1 :=
            ZMod.mul_inv_of_unit _ hcard
          rw [hmul, one_smul]

/-- Conversely, an element satisfying the character eigenrelation lies in the
projection range. -/
theorem mem_characterProjection_range_of_forall_apply_eq_smul
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M)
    {x : M}
    (hx : ∀ a : Delta p, ρ a x = ((a : ZMod p) ^ i) • x) :
    x ∈ LinearMap.range (characterProjection (p := p) i ρ) := by
  refine ⟨x, ?_⟩
  calc
    characterProjection (p := p) i ρ x
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ a x := by
          simp [characterProjection, projection]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a •
              (((a : ZMod p) ^ i) • x) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [hx a]
    _ = ∑ a : Delta p,
            (Fintype.card (Delta p) : ZMod p)⁻¹ • x := by
          simp [smul_smul, characterProjectionCoefficient_mul_pow]
    _ = ((Fintype.card (Delta p) : ZMod p) *
            (Fintype.card (Delta p) : ZMod p)⁻¹) • x := by
          rw [Finset.sum_const]
          change Fintype.card (Delta p) •
              ((Fintype.card (Delta p) : ZMod p)⁻¹ • x) =
            ((Fintype.card (Delta p) : ZMod p) *
              (Fintype.card (Delta p) : ZMod p)⁻¹) • x
          rw [← Nat.cast_smul_eq_nsmul (ZMod p)
            (Fintype.card (Delta p))
            ((Fintype.card (Delta p) : ZMod p)⁻¹ • x)]
          rw [smul_smul]
    _ = x := by
          have hmul :
              (Fintype.card (Delta p) : ZMod p) *
                (Fintype.card (Delta p) : ZMod p)⁻¹ = 1 :=
            ZMod.mul_inv_of_unit _ hcard
          rw [hmul, one_smul]

/-- Idempotence of the character projection, as an elementwise statement. -/
theorem characterProjection_apply_characterProjection
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M) (x : M) :
    characterProjection (p := p) i ρ
        (characterProjection (p := p) i ρ x) =
      characterProjection (p := p) i ρ x :=
  characterProjection_apply_eq_self_of_mem_range
    (p := p) hcard i ρ ⟨x, rfl⟩

end CharacterProjection

end SingularKummer
end Reflection
end BernoulliRegular

end

end
