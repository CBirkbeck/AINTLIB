# T-V-1-004: #E(F_q) = q + 1 − tr(π)

**Status**: PARTIAL (witness-parametric form landed)
**Silverman**: V.1.1 setup
**Module**: `HasseWeil/Hasse/PointFix.lean` (witness form); target
`HasseWeil/Hasse/PointCount.lean` (unconditional form)
**Owner**: worker-J
**Estimated lines**: 40
**Difficulty**: medium
**Stream**: F

## Depends on
- T-V-1-003 (#E = deg(1-π)) — BLOCKED
- T-III-6-005 (dual additivity) — OPEN
- T-III-6-007 (deg dual = deg) — OPEN

## Blocks
- T-V-1-006 (Hasse bound)

## Statement (Silverman V.1.1 setup)
Let `E/F_q`. Define `tr(π) := 1 + q − #E(F_q) = π + π̂` (the trace of Frobenius).
Then `#E(F_q) = q + 1 − tr(π)`.

## Acceptance criteria

```lean
namespace HasseWeil.Hasse

theorem card_Fq_formula
    (E : WeierstrassCurve (ZMod p)) [Fact p.Prime] [Fact (E.Δ ≠ 0)]
    (q : ℕ) (hq : q = p^k) :
    (Fintype.card (E.toAffine.Point) : ℤ) =
      q + 1 - ((E.frobeniusIsogeny q) + (E.frobeniusIsogeny q).dual).toIntDegLike

end HasseWeil.Hasse
```

## Notes
- Expand: `deg(1 − π) = (1 - π̂)(1 - π) = 1 - π̂ - π + π̂ π = 1 - tr(π) + q`
  (using `π̂ ∘ π = [deg π] = [q]`).
- The current `HasseWeil.pointCount_eq` (at `Frobenius.lean:94-100`) has the
  shape of this statement but is not provable: `oneSubFrobeniusIsog` is a
  placeholder (pullback = `AlgHom.id`, degree = 1). Using `isogTrace`'s
  definition `1 + deg(α) − deg(1−α)`, the RHS collapses to `q + 1 − (1 + q − 1)
  = 1`. The remaining `sorry` is not closable until the placeholder is
  replaced by a concrete pullback with the correct degree. See
  `T-V-1-003-card-Eq-eq-deg.md` for the two available unblocking paths.

## Progress log
- 2026-04-17 [auto] Reviewed `Frobenius.lean:100` sorry. Status upgraded from
  PARTIAL → BLOCKED (cascades from T-V-1-003). No proof change.
- 2026-04-20 [worker-J] Witness-parametric form
  `pointCount_eq_of_hom_kernel_witness` landed at
  `HasseWeil/Hasse/PointFix.lean`. Given a witness isogeny `β` with
  `β.toAddMonoidHom = id − π.toAddMonoidHom` and
  `Nat.card β.kernel = β.degree` (T-III-4-015 content for `β`),
  concludes `#E(F_q) = q + 1 − isogTrace π β`. Note our `isogTrace`
  computes the trace algebraically from degrees (`1 + deg π − deg β`)
  rather than via the dual (`π + π̂`); the two agree when `β` is the
  true `1 − π` by V.1.2 expansion. Also part of
  `hasse_bound_of_full_witnesses` in `BoundOfWitnesses.lean`. Status
  BLOCKED → PARTIAL.
