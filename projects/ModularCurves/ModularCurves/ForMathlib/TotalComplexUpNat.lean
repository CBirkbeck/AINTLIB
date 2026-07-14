import Mathlib.Algebra.Homology.TotalComplex

/-!
# Total complexes of first-quadrant bicomplexes

Supply the standard signs for cochain complexes indexed by the natural numbers, so that
mathlib's existing total-complex construction applies to first-quadrant bicomplexes.
-/

namespace ComplexShape

/-- The standard tensor signs for natural-number-indexed cochain complexes. -/
instance upNat_tensorSigns : TensorSigns (up ℕ) where
  ε' := MonoidHom.mk' (fun n : Multiplicative ℕ ↦ (-1 : ℤˣ) ^ n.toAdd) (by
    intro m n
    exact pow_add (-1 : ℤˣ) m.toAdd n.toAdd)
  rel_add p q r hpq := by
    change p + r + 1 = q + r
    change p + 1 = q at hpq
    omega
  add_rel p q r hpq := by
    change r + p + 1 = r + q
    change p + 1 = q at hpq
    omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -((-1 : ℤˣ) ^ p)
    calc
      (-1 : ℤˣ) ^ (p + 1) = (-1 : ℤˣ) ^ p * (-1 : ℤˣ) :=
        pow_succ _ _
      _ = -((-1 : ℤˣ) ^ p) := by rw [mul_neg, mul_one]

@[simp]
lemma ε_up_ℕ (n : ℕ) : (up ℕ).ε n = (-1 : ℤˣ) ^ n :=
  rfl

end ComplexShape
