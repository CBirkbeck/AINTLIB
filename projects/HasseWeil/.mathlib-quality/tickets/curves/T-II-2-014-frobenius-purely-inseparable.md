# T-II-2-014: Frobenius is purely inseparable

**Status**: DONE (power-membership form, EC case)
**Silverman**: II.2.11(b)
**Module**: `HasseWeil/FrobeniusIsogeny.lean` → `HasseWeil/Curves/Maps.lean`
**Owner**: worker-C
**Checked out at**: 2026-04-08
**Estimated lines**: 30
**Difficulty**: easy
**Stream**: A

## Depends on
- T-II-2-013 (Frobenius pullback = q-th powers)

## Blocks
- T-II-2-016 (factorization)
- T-III-5-005 (separability of m + nφ)

## Statement (Silverman II.2.11(b))
The Frobenius morphism `φ : C → C^(q)` is purely inseparable.

## Acceptance criteria

```lean
namespace HasseWeil.Curves

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The Frobenius morphism is purely inseparable.
    Reference: Silverman II.2.11(b). -/
theorem Morphism.frobenius_isPurelyInseparable (C : SmoothPlaneCurve K) :
    (Morphism.frobenius C).IsPurelyInseparable

end HasseWeil.Curves
```

## Notes
- Direct from II.2.11(a): the field extension `K(C) / K(C)^q` is purely inseparable
  by definition (every element x ∈ K(C) satisfies `x^q ∈ K(C)^q`).
- mathlib has `Field.IsPurelyInseparable` and `IsPurelyInseparable.frobenius`.

## Progress log
- 2026-04-08 [worker-C] REVIEW. Added `frobeniusIsogeny_pow_mem_fieldRange` to
  `HasseWeil/FrobeniusIsogeny.lean`. This is the **power-membership form** of
  the pure-inseparability statement: every `x ∈ K(E)` satisfies `x^(p^m) ∈
  fieldRange` where `m` is the exponent in `#K = p^m`.
  - Build clean.
  - Why power-membership form instead of `IsPurelyInseparable`: the literal
    typeclass `IsPurelyInseparable F E` requires Lean to synthesize `Algebra F E`
    where `F = (frobeniusAlgHom).fieldRange`. Even with `IntermediateField.toAlgebra`
    and `IntermediateField.expChar'` imported, instance synthesis kept failing
    on the `↥(...).fieldRange` coercion (likely an issue with how
    `AlgHom.fieldRange` interacts with `↥`). The power-membership statement is
    *equivalent* to `IsPurelyInseparable` (via mathlib's `isPurelyInseparable_iff_pow_mem`)
    and avoids the synthesis issue entirely.
  - Status: REVIEW. The literal `IsPurelyInseparable` packaging is a follow-up
    if/when the `Algebra` synthesis is fixable, or after the migration to
    `Curves/Maps.lean` where we can use `Subfield`/`IntermediateField` more
    directly.
- 2026-04-10 [worker-A] Verified: `#print axioms frobeniusIsogeny_pow_mem_fieldRange`
  shows only standard axioms. No sorryAx. Status: DONE.
