# T-III-6-010: Structure of E[m] (no Tate, no Weil pairing)

**Status**: PARTIAL (witness form + deg [m] = m² both in place)
**Silverman**: III.6.4
**Module**: `HasseWeil/Hasse/TorsionCard.lean` (witness form);
`HasseWeil/Basic.lean` (`mulByInt_degree`)
**Owner**: worker-J
**Estimated lines**: 50
**Difficulty**: medium
**Stream**: C

## Depends on
- T-III-6-006 (deg [m] = m²)
- T-III-4-015 (separable ⇒ #ker = deg)

## Blocks
- (none in critical path; mathlib-quality)

## Statement (Silverman III.6.4)
For an elliptic curve `E` and `m ∈ ℤ` with `m ≠ 0`:
- `#E[m] | m²` always.
- If `char K = 0` or `char K = p ∤ m`, then `E[m] ≅ ℤ/m × ℤ/m` (so `#E[m] = m²`).
- If `char K = p`, then `E[p^e]` is either `0` or `ℤ/p^e` (depending on
  ordinary vs supersingular).

We will only prove the cardinality part (`#E[m] = m²` when separable), not the
structure as a product (which uses the Weil pairing — out of scope).

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- |E[m]| = m² when m is invertible in K (separable case).
    Reference: Silverman III.6.4(a). -/
theorem WeierstrassCurve.torsionSubgroup_card_eq_msq
    (E : WeierstrassCurve F) [Fact (E.Δ ≠ 0)] (m : ℤ) (hm : (m : F) ≠ 0) :
    Fintype.card E[m] = m^2

end HasseWeil.EC
```

## Notes
- From T-III-5-004 ([m] separable when m ≠ 0 in K) and T-III-4-015
  (#ker = deg) and T-III-6-006 (deg [m] = m²).

## Progress log
- 2026-04-20 [worker-J] Witness form `torsionSubgroup_card_of_witness`
  landed in `HasseWeil/Hasse/TorsionCard.lean`: given `m ≠ 0 : ℤ` and
  `Nat.card (mulByInt W.toAffine m).kernel = (mulByInt W.toAffine m).degree`
  (T-III-4-015 content for `[m]`), concludes `Nat.card W.toAffine[m] = m²`
  in `ℤ`. Proof via `mulByInt_degree` + `Int.toNat_of_nonneg (sq_nonneg _)`.
  Axiom-hygienic (standard only). Full unconditional form requires
  T-III-4-015.
