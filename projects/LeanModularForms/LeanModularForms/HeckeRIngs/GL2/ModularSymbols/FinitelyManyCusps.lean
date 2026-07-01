/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Finitely many cusps for `Γ₁(N)`

The projective line `ℙ¹(ℚ) = Projectivization ℚ (Fin 2 → ℚ)` carries an action of `SL(2, ℤ)`,
obtained by mapping `SL(2, ℤ) → SL(2, ℚ)` (entrywise via `ℤ → ℚ`) and then using the standard
`SL(2, ℚ)`-action on its projective line.  This is exactly the point action underlying
`HeckeRing.GL2.ModularSymbols.div0Rep`.

## Main results

* `HeckeRing.GL2.ModularSymbols.isPretransitive_SL2Z_projQQ` : `SL(2, ℤ)` acts transitively on
  `ℙ¹(ℚ)`.
* `HeckeRing.GL2.ModularSymbols.instFiniteCuspsGamma1` : `Γ₁(N)` has only finitely many orbits on
  `ℙ¹(ℚ)`.
-/

namespace HeckeRing.GL2.ModularSymbols

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix OnePoint

/-- The action of `SL(2, ℤ)` on the projective line `ℙ¹(ℚ)`, obtained by mapping
`SL(2, ℤ) → SL(2, ℚ)` and using the standard `SL(2, ℚ)`-action.  This is the point action
underlying `div0Rep`. -/
noncomputable instance instMulActionSL2ZProjQQ :
    MulAction SL(2, ℤ) (Projectivization ℚ (Fin 2 → ℚ)) :=
  MulAction.compHom _ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))

/-- `SL(2, ℤ)` acts transitively on `ℙ¹(ℚ)`. -/
theorem isPretransitive_SL2Z_projQQ :
    MulAction.IsPretransitive SL(2, ℤ) (Projectivization ℚ (Fin 2 → ℚ)) := by
  apply MulAction.IsPretransitive.of_orbit (x₀ := OnePoint.equivProjectivization ℚ ∞)
  intro x
  obtain ⟨g, hg⟩ := ((OnePoint.equivProjectivization ℚ).symm x).exists_mem_SL2 ℤ
  refine ⟨g, ?_⟩
  have hkey : (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) g)
      • OnePoint.equivProjectivization ℚ ∞ = x := by
    have h2 := congrArg (OnePoint.equivProjectivization ℚ) hg
    rw [OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply] at h2
    rw [← h2]
    rfl
  exact hkey

/-- `Γ₁(N)` has only finitely many orbits on `ℙ¹(ℚ)`. -/
instance instFiniteCuspsGamma1 (N : ℕ) [NeZero N] :
    Finite (MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma1 N)
      (Projectivization ℚ (Fin 2 → ℚ))) :=
  haveI := isPretransitive_SL2Z_projQQ
  Subgroup.finite_quotient_of_pretransitive_of_index_ne_zero
    Subgroup.FiniteIndex.index_ne_zero

end HeckeRing.GL2.ModularSymbols
