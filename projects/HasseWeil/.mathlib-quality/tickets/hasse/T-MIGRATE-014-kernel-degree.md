# T-MIGRATE-014: Refactor KernelDegree.lean → EC/IsogenyFactor.lean

**Status**: OPEN
**Module**: `HasseWeil/KernelDegree.lean` → `HasseWeil/EC/IsogenyFactor.lean`
**Owner**: (unassigned)
**Estimated lines**: 0 (refactor)
**Difficulty**: easy
**Stream**: M

## Depends on
- T-MIGRATE-001

## Blocks
- T-MIGRATE-015

## Statement
Refactor:
- `HasseWeil/KernelDegree.lean` (group hom + ker degree theorems) →
  `HasseWeil/EC/IsogenyFactor.lean`
- The `E(F_q) = ker(1-π)` part is moved to `HasseWeil/Hasse/PointCount.lean`.

## Progress log
