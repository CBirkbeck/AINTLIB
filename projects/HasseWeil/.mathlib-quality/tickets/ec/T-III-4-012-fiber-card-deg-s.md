# T-III-4-012: #φ⁻¹(Q) = deg_s φ for all Q (isogeny version)

**Status**: PARTIAL (witness-parametric, worker-A)
**Silverman**: III.4.10(a)(i)
**Module**: `HasseWeil/EC/IsogenyKernel.lean`
**Owner**: worker-A
**Estimated lines**: 50
**Difficulty**: medium (CRITICAL)
**Stream**: C

## Depends on
- T-II-2-009 (#φ⁻¹(Q) = deg_s for almost all Q)
- T-III-4-010 (every isogeny is hom)
- T-III-4-011 (ker is finite)

## Blocks
- T-III-4-015 (separable ⇒ unramified, ker = deg)
- T-V-1-003 (#E(F_q) = deg(1-π))

## Statement (Silverman III.4.10(a) first half)
For every nonzero isogeny `φ : E₁ → E₂` and every `Q ∈ E₂(K̄)`,
`#φ⁻¹(Q) = deg_s φ`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- For an isogeny, every fiber has the same cardinality, equal to deg_s.
    Reference: Silverman III.4.10(a) first part. -/
theorem Isogeny.fiber_card_eq_sepDegree (α : Isogeny E₁ E₂) (hα : α ≠ 0)
    (Q : E₂.toAffine.Point) :
    Fintype.card (α.fiber Q) = α.sepDegree

end HasseWeil.EC
```

## Notes
- For curve maps, T-II-2-009 only gives this for "almost all Q" (away from
  ramification). For an isogeny it holds for ALL Q because of the
  group-translation symmetry: any fiber `φ⁻¹(Q)` is a translate of
  `φ⁻¹(O) = ker φ`, hence all fibers have the same cardinality. The "almost all"
  case pins it to `deg_s`.

## Progress log

- **Prior session** (worker-A): witness-parametric form
  `Isogeny.fiber_card_eq_sepDegree_of_witness` delivered in
  `HasseWeil/EC/IsogenyKernel.lean`. Takes fiber-finiteness + sepDegree
  witness as hypotheses; unconditional closure awaits T-II-2-009.
