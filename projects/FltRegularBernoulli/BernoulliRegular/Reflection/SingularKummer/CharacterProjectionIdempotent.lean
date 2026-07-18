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

/-- The `i`-th character coefficient at `a`, multiplied back by `a ^ i`, leaves
just the inverse of `|Delta|`. -/
theorem characterProjectionCoefficient_mul_pow
    (i : ℕ) (a : Delta p) :
    characterProjectionCoefficient (p := p) i a * ((a : ZMod p) ^ i) =
      (Fintype.card (Delta p) : ZMod p)⁻¹ := by
  have hmul : ((a⁻¹ : Delta p) : ZMod p) * (a : ZMod p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [characterProjectionCoefficient, mul_assoc, ← mul_pow, hmul, one_pow, mul_one]

/-- The character projection fixes any `x` satisfying the eigenrelation
`ρ a x = a ^ i • x`, provided `|Delta|` is invertible in `ZMod p`.

This is the common core of `characterProjection_apply_eq_self_of_mem_range`
and `mem_characterProjection_range_of_forall_apply_eq_smul`: each supplies the
eigenrelation from a different side. -/
private theorem characterProjection_apply_of_forall_apply_eq_smul
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M)
    {x : M}
    (hx : ∀ a : Delta p, ρ a x = ((a : ZMod p) ^ i) • x) :
    characterProjection (p := p) i ρ x = x := by
  calc
    characterProjection (p := p) i ρ x
        = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a • ρ a x := by
          simp [characterProjection, projection]
    _ = ∑ a : Delta p,
            characterProjectionCoefficient (p := p) i a •
              (((a : ZMod p) ^ i) • x) := by
          exact Finset.sum_congr rfl fun a _ ↦ by rw [hx a]
    _ = ∑ _a : Delta p,
            (Fintype.card (Delta p) : ZMod p)⁻¹ • x := by
          simp [smul_smul, characterProjectionCoefficient_mul_pow]
    _ = x := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod p),
            smul_smul, ZMod.mul_inv_of_unit _ hcard, one_smul]

/-- A character projection acts as the identity on its range, provided
`|Delta|` is invertible in `ZMod p`. -/
theorem characterProjection_apply_eq_self_of_mem_range
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M)
    {x : M}
    (hx : x ∈ LinearMap.range (characterProjection (p := p) i ρ)) :
    characterProjection (p := p) i ρ x = x :=
  characterProjection_apply_of_forall_apply_eq_smul (p := p) hcard i ρ
    fun a ↦ mem_characterProjection_range_apply (p := p) i ρ a hx

/-- Conversely, an element satisfying the character eigenrelation lies in the
projection range. -/
theorem mem_characterProjection_range_of_forall_apply_eq_smul
    (hcard : IsUnit (Fintype.card (Delta p) : ZMod p))
    (i : ℕ) (ρ : Delta p →* M ≃ₗ[ZMod p] M)
    {x : M}
    (hx : ∀ a : Delta p, ρ a x = ((a : ZMod p) ^ i) • x) :
    x ∈ LinearMap.range (characterProjection (p := p) i ρ) :=
  ⟨x, characterProjection_apply_of_forall_apply_eq_smul (p := p) hcard i ρ hx⟩

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
