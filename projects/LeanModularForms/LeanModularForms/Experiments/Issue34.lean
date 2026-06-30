import LeanModularForms.Experiments.Issue55
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.CMField

/-!
# LeanBridge issue #34: coefficient fields of newforms

This file states the key coefficient-field targets for newforms.
-/

noncomputable section

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

namespace Newform

/-- The coefficient field `ℚ(a_n : n ≥ 1)` of a newform. -/
noncomputable def coefficientField (f : Newform N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (Set.range fun n : ℕ+ => fourierCoeffAtInfinity f.toCuspForm n.val)

/-- The coefficient field of a newform is finite-dimensional over `ℚ`. -/
theorem coefficientField_finiteDimensional (f : Newform N k) :
    FiniteDimensional ℚ f.coefficientField := by
  sorry

/-- The coefficient field of a newform is a number field. -/
theorem coefficientField_numberField (f : Newform N k) :
    NumberField f.coefficientField := by
  sorry

/-- The relative dimension attached to a newform. -/
noncomputable def relativeDimension (f : Newform N k) : ℕ :=
  Module.finrank ℚ f.coefficientField

theorem coefficientField_degree_eq_relativeDimension (f : Newform N k) :
    Module.finrank ℚ f.coefficientField = f.relativeDimension := by
  sorry

/-- A newform's coefficient field is totally real if and only if the newform is self-dual. -/
theorem coefficientField_isTotallyReal_iff_isSelfDual (f : Newform N k) :
    NumberField.IsTotallyReal f.coefficientField ↔ IsSelfDual f.toCuspForm := by
  sorry

/-- A newform's coefficient field is CM if and only if the newform is not self-dual. -/
theorem coefficientField_isCM_iff_not_isSelfDual (f : Newform N k) :
    NumberField.IsCMField f.coefficientField ↔ ¬ IsSelfDual f.toCuspForm := by
  sorry

end Newform

end HeckeRing.GL2
