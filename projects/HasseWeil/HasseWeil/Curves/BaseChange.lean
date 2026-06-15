import HasseWeil.Curves.Basic

/-!
# Base change of a smooth plane curve

For a smooth plane curve `C` over a field `F` and an `F`-algebra `L`, we
define `C.baseChange L : SmoothPlaneCurve L` by changing the base of the
underlying Weierstrass data via mathlib's
`WeierstrassCurve.baseChange`. This produces the same curve viewed over
the extension `L`.

This closes ticket `T-II-INFRA-C-001` of the Stream-A infrastructure
plan, and is the foundation for the `F`/`L̄` distinction needed by
T-II-3-004 (Galois action on divisors) and downstream "defined over F"
statements.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], I.2 (definition of
  "defined over `K`")
-/

open WeierstrassCurve

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- The base change of a smooth plane curve `C/F` along an `F`-algebra
extension `L`. The underlying Weierstrass data is transported via
`WeierstrassCurve.baseChange`.
Reference: Silverman I.2 (definition of "defined over `K`"). -/
noncomputable def baseChange (L : Type*) [Field L] [Algebra F L] :
    SmoothPlaneCurve L where
  toAffine := C.toAffine.baseChange L

@[simp] theorem baseChange_toAffine (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine = C.toAffine.baseChange L := rfl

@[simp] theorem baseChange_a₁ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₁ = algebraMap F L C.toAffine.a₁ := rfl

@[simp] theorem baseChange_a₂ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₂ = algebraMap F L C.toAffine.a₂ := rfl

@[simp] theorem baseChange_a₃ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₃ = algebraMap F L C.toAffine.a₃ := rfl

@[simp] theorem baseChange_a₄ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₄ = algebraMap F L C.toAffine.a₄ := rfl

@[simp] theorem baseChange_a₆ (L : Type*) [Field L] [Algebra F L] :
    (C.baseChange L).toAffine.a₆ = algebraMap F L C.toAffine.a₆ := rfl

/-! ### Points over an extension -/

/-- The `L`-rational smooth points of a curve `C` defined over `F`, for
`L` an `F`-algebra: equivalently, smooth points of the base change
`C.baseChange L`. Reference: Silverman I.2 (notation `V(L)`). -/
abbrev pointsOver (L : Type*) [Field L] [Algebra F L] : Type _ :=
  (C.baseChange L).SmoothPoint

/-- The inclusion `C.SmoothPoint → C.pointsOver L` obtained by applying
`algebraMap F L` to coordinates. -/
noncomputable def includePoint (C : SmoothPlaneCurve F) (L : Type*) [Field L]
    [Algebra F L] (P : C.SmoothPoint) : C.pointsOver L where
  x := algebraMap F L P.x
  y := algebraMap F L P.y
  nonsingular :=
    (Affine.map_nonsingular C.toAffine (f := algebraMap F L)
      (FaithfulSMul.algebraMap_injective F L) P.x P.y).mpr P.nonsingular

@[simp] theorem includePoint_x (L : Type*) [Field L] [Algebra F L]
    (P : C.SmoothPoint) : (C.includePoint L P).x = algebraMap F L P.x := rfl

@[simp] theorem includePoint_y (L : Type*) [Field L] [Algebra F L]
    (P : C.SmoothPoint) : (C.includePoint L P).y = algebraMap F L P.y := rfl

end SmoothPlaneCurve

end HasseWeil.Curves
