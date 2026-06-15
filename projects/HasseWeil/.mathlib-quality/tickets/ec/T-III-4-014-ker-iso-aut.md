# T-III-4-014: ker φ ≅ Aut(K̄(E₁)/φ*K̄(E₂)) via T ↦ τ_T*

**Status**: REVIEW (2026-05-08, audit pending — codebase has shipped
`translateAlgEquivOfPoint_injective` (`HasseWeil/EC/TranslationOrd.lean`)
and `faithfulSMul_kernel` (`HasseWeil/Hasse/PointFix.lean:1146`) axiom-
clean, both unconditional. The injection half of III.4.10(b) is structurally
done. Surjection half (the isomorphism statement) follows from T-II-2-009
+ counting bound `|Aut| ≤ deg_s` via `Field.finSepDegree_le_finrank`.)
**Silverman**: III.4.10(b)
**Module**: `HasseWeil/EC/IsogenyFactor.lean`
**Owner**: (unassigned)
**Estimated lines**: 100
**Difficulty**: hard (CRITICAL)
**Stream**: C

## Depends on
- T-III-4-009 (translation map)
- T-III-4-011 (ker finite)
- T-III-2-006 (even functions)

## Blocks
- T-III-4-015 (separable ⇒ Galois)
- T-III-4-016 (factorization)

## Statement (Silverman III.4.10(b))
For a nonzero isogeny `φ : E₁ → E₂`, the map
`ker φ → Aut(K̄(E₁)/φ*K̄(E₂))`, `T ↦ (τ_T)*`,
is an injective group homomorphism. (Where `τ_T*` is precomposition with the
translation `τ_T`.)

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The action of ker φ on K̄(E₁) by translation gives a group hom into Aut.
    Reference: Silverman III.4.10(b). -/
def Isogeny.kerToAut (α : Isogeny E₁ E₂) (hα : α ≠ 0) :
    AddMonoidHom.ker α.asAddMonoidHom →*
      AlgEquiv (R := α.pullback E₂.FunctionField) (S := E₁.FunctionField) _ _

theorem Isogeny.kerToAut_injective (α : Isogeny E₁ E₂) (hα : α ≠ 0) :
    Function.Injective (α.kerToAut hα)

end HasseWeil.EC
```

## Notes
- For `T ∈ ker φ`, the translation `τ_T : E₁ → E₁` satisfies `φ ∘ τ_T = φ`
  (since `τ_T` is translation by an element of the kernel). So `τ_T*` fixes
  `φ*K̄(E₂)`, hence is in `Aut(K̄(E₁)/φ*K̄(E₂))`.
- Injectivity: if `τ_T* = id` on `K̄(E₁)`, then `τ_T = id` on `E₁` (Galois
  correspondence), hence `T = O₁`.

## Audit notes (2026-05-08)

The codebase has shipped:
- `translateAlgEquivOfPoint_add` (group hom property — `EC/TranslationOrd.lean`).
- `translateAlgEquivOfPoint_injective` (the injectivity argument via pole-order
  analysis at `−T`; the `x_gen` pole at `O` argument from Silverman III.4.10(b)).
- `kernelMulSemiringAction` + `faithfulSMul_kernel` (the multiplicative
  semiring action packaging in `Hasse/PointFix.lean:1146`, unconditional and
  axiom-clean).

These together discharge the **injection** half of III.4.10(b)
unconditionally. The surjection half is the **isomorphism** statement and
requires T-II-2-009 (`#fiber = deg_s`) + the Galois bound
`|Aut(L/F)| ≤ Field.finSepDegree F L` from Mathlib (per reviewer's Q4').

**Recommendation**: promote to DONE for the injection half, leave the
isomorphism statement under T-III-4-015 since it requires T-II-2-009 to
close.

## Progress log
