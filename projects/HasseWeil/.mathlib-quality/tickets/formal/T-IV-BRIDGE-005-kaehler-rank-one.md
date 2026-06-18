# T-IV-BRIDGE-005: kaehler_rank_one: dim_{K(E)} Ω_{K(E)/K} = 1

**Status**: DONE
**Silverman**: II.4.2(a) for E
**Module**: `HasseWeil/FormalGroupCorrespondence.lean`
**Owner**: (proved)
**Estimated lines**: 50 (actual ~155 lines of tactic proof)
**Difficulty**: medium
**Stream**: E

## Depends on
- T-II-4-002 (Ω_C is 1-dim — for general C, specialized to E)

## Blocks
- T-III-5-001..010 (everything that uses Ω_E ≅ K(E))

## Statement
For an elliptic curve `E`, the Kähler differentials `Ω_{K(E)/K}` form a
1-dimensional `K(E)`-vector space.

## Acceptance criteria

```lean
namespace HasseWeil

theorem kaehler_rank_one (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] :
    Module.finrank E.toAffine.FunctionField (Ω[E.toAffine.FunctionField⁄F]) = 1

end HasseWeil
```

## Notes
- This was the existing `kaehler_rank_one` SORRY in the codebase.
- It was proved directly (without going through T-II-4-002's general statement)
  using the explicit structure of K(E) = Frac(F[X][Y]/(W)). The proof walks
  the algebra tower F → F[X] → CoordinateRing → FunctionField, showing that
  D(f) lies in span{D(x)} for every f ∈ K(E), via induction on polynomial
  structure and the Weierstrass relation to reduce D(y) to D(x) multiples.

## Progress log
- 2026-04-08 [auto] PARTIAL — existing SORRY
- 2026-04-17 [agent] DONE — verified `lake build` passes and
  `#print axioms HasseWeil.kaehler_rank_one` reports only
  `[propext, Classical.choice, Quot.sound]` (no sorry, no extra axioms).
  The theorem is located at `HasseWeil/FormalGroupCorrespondence.lean:61`.
  Note: the acceptance criterion uses `E : WeierstrassCurve F` with
  `[Fact (E.Δ ≠ 0)]`; the proved version uses `E : Affine F` with
  `[E.IsElliptic]`, which is the equivalent mathlib idiom in scope.
