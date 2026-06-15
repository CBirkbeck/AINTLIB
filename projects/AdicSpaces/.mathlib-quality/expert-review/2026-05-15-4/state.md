# Expert-review session state (round 9)

- Generated: 2026-05-15 (same day as rounds 6, 7, 8; follow-up to round 8's reply)
- Audience: ChatGPT Pro (continuing series, round 9 follow-up)
- Goal of brief: Verify that the round-8 reviewer feedback was correctly applied. The reviewer flagged that unitCover was under-specified; round 9 added `IsCanonicalRelativeBase`, `IsRelativeUnitPieceFor`, and `IsUnitGeneratedCoverFrom` predicates to pin down the relative unit-generated cover.
- Scope: three new predicates + revised W3 and W3-transport using them.
- Reply received: false
- Reply integrated: false

## Questions in the brief

| # | Question (verbatim from §5 of the brief) |
|---|------------------------------------------|
| Q1 | Is the round-9 `IsUnitGeneratedCoverFrom` predicate now strong enough? Two-way correspondence + relative-unit-piece identification — anything missing (bijection-as-function vs. mere existence)? |
| Q2 | Is `IsRelativeUnitPieceFor`'s Spv-comap formulation correct? Reviewer noted relative generator should correspond to `f / C.base.s`, not `s⁻¹ f`. Does the predicate encode this? |
| Q3 | Is `IsCanonicalRelativeBase` (T = ∅ ∧ s = 1) the right canonical form, or something more semantic? |
| Q4 | With round-9 predicates in place, is the architecture now correct as a proof target? |

## Round-8 changes applied

- New `IsCanonicalRelativeBase L L_rel` predicate.
- New `IsRelativeUnitPieceFor L C f piece` predicate.
- New `IsUnitGeneratedCoverFrom L C s I_units L_rel unitCover` predicate.
- W3 updated to take both new hypotheses.
- W3-transport updated to take both new hypotheses + the relative inner tree.

## File state at brief time

- 6 sorries: W1, W2, W3, W3-transport, I.1's body, V.1.
- `lake build` clean.
- W3-transport descent chain documented inline with each arrow's witness named.
