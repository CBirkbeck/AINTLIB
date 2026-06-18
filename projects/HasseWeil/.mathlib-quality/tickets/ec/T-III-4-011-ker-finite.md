# T-III-4-011: ker φ is finite

**Status**: PARTIAL (witness form landed; unconditional form awaits T-II-2-002)
**Silverman**: III.4.9
**Module**: `HasseWeil/EC/Isogeny.lean`
**Owner**: (unassigned)
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-4-010 (every isogeny is hom)
- T-II-2-002 (nonconst surjective ⇒ fibers finite)

## Blocks
- T-III-4-006 (E[m] subgroup)
- T-III-4-012, T-III-4-014, T-III-4-015, T-III-4-016, T-III-4-017
- T-V-1-003 (#E(F_q) = deg(1-π))

## Statement (Silverman III.4.9)
For any nonzero isogeny `φ : E₁ → E₂`, the kernel `ker φ` is a finite subgroup
of `E₁(K̄)`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- The kernel of a nonzero isogeny is finite.
    Reference: Silverman III.4.9. -/
instance Isogeny.ker_finite (α : Isogeny E₁ E₂) (hα : α ≠ 0) :
    Finite (AddMonoidHom.ker α.asAddMonoidHom)

end HasseWeil.EC
```

## Notes
- Proof: ker φ is a fiber `φ⁻¹(O₂)`, and any nonconstant morphism of curves has
  finite fibers (T-II-2-002 + properness, or directly: nonzero φ is surjective
  hence has finite fibers because it's a finite morphism).

## Progress log

- 2026-04-21 [worker-A] Witness form `Isogeny.kernel_finite_of_fiber_finite`
  landed in `HasseWeil/EC/IsogenyKernel.lean`: given `Finite {P // α P = 0}`
  as hypothesis, concludes `Finite α.kernel`. Axiom-clean. The full
  unconditional form requires T-II-2-002 (nonconstant morphism of smooth
  curves has finite fibers), which remains OPEN. Status: OPEN → PARTIAL.
