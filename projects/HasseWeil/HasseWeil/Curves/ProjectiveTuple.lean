import HasseWeil.Curves.Valuation
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective tuples on a smooth plane curve

A **projective tuple** of length `N + 1` on a smooth plane curve `C` is a
nonzero tuple `[f₀, …, f_N]` of functions in `K(C)`, modulo simultaneous
scaling by `K(C)ˣ`. Geometrically, this represents a rational map
`C ⇢ ℙᴺ`.

This closes ticket T-II-INFRA-B-001 of the Stream-A infrastructure plan
and is the building block for the `RationalMap`/`Morphism` theory of
Phase B.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.3 (definition of
  rational map into projective space)
-/

open scoped LinearAlgebra.Projectivization

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F]

/-- A **projective tuple** of length `N + 1` on a smooth plane curve `C`:
a point in the projective space `ℙ K(C) (Fin (N + 1) → K(C))`. This is the
algebraic model of a rational map `C ⇢ ℙᴺ`.
Reference: Silverman I.3 (definition of rational map). -/
def ProjectiveTuple (C : SmoothPlaneCurve F) (N : ℕ) : Type _ :=
  ℙ C.FunctionField (Fin (N + 1) → C.FunctionField)

namespace ProjectiveTuple

variable {C : SmoothPlaneCurve F} {N : ℕ}

/-- Build a projective tuple from a nonzero `(N + 1)`-tuple of elements of
`K(C)`. -/
noncomputable def mk (f : Fin (N + 1) → C.FunctionField) (hf : f ≠ 0) :
    ProjectiveTuple C N :=
  Projectivization.mk C.FunctionField f hf

/-- Choose a nonzero representative of a projective tuple. -/
noncomputable def repr (φ : ProjectiveTuple C N) :
    Fin (N + 1) → C.FunctionField :=
  Projectivization.rep φ

theorem repr_ne_zero (φ : ProjectiveTuple C N) : φ.repr ≠ 0 :=
  Projectivization.rep_nonzero φ

@[simp] theorem mk_repr (φ : ProjectiveTuple C N) :
    mk φ.repr φ.repr_ne_zero = φ :=
  Projectivization.mk_rep φ

/-- Two representatives define the same projective tuple iff they are
scalar multiples. -/
theorem mk_eq_mk_iff {f g : Fin (N + 1) → C.FunctionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    mk f hf = mk g hg ↔ ∃ a : C.FunctionFieldˣ, a • g = f :=
  Projectivization.mk_eq_mk_iff C.FunctionField f g hf hg

/-- Scaling a representative by a unit of `K(C)` gives the same projective tuple.
Reference: Silverman I.3 (rational maps are defined modulo common scaling). -/
theorem mk_smul (f : Fin (N + 1) → C.FunctionField) (hf : f ≠ 0)
    (a : C.FunctionFieldˣ) :
    mk ((a : C.FunctionField) • f) (smul_ne_zero_iff.mpr ⟨a.ne_zero, hf⟩) =
      mk f hf :=
  (mk_eq_mk_iff _ hf).mpr ⟨a, rfl⟩

end ProjectiveTuple

end SmoothPlaneCurve

end HasseWeil.Curves
