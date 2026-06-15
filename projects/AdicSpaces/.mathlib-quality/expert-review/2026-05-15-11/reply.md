# Reviewer reply — ChatGPT Pro (round 16) — 2026-05-15

## Assessment: FINAL APPROVAL ✅

**The round-16 architecture is now a sound proof target.**

Core structural problems from rounds 6–15 resolved:
- Ratio splits no longer forced into ordinary Laurent splits.
- Ratio splits no longer require global inverses in `A`.
- `RatioNodeData` packages validity of each denominator-cleared ratio node.
- Chosen ratio data are coherent through `RatioTreeRealization`.
- `Refines` and `allSplitsInducing` are predicates on the realised tree.
- Final Wedhorn existence theorem has the right output shape:
  ```lean
  ∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
    ρ.Refines C ∧ ρ.allSplitsInducing
  ```

**Reviewer's directive: STOP REDESIGNING THE ARCHITECTURE AND START PROVING THE OPEN LEMMAS.**

## Recommended proof order

1. `isUnit_relativeUnitGenerator_from_W2_unit` (short unit calculation: `f/C.base.s = (s⁻¹·f) · (s/C.base.s)`)
2. `isUnit_base_s_in_presheafValue_of_containment` — prefer **structured rational-containment data** over bare set inclusion
3. **Key transport theorem**: `relative_ratio_split_transports_to_RatioNodeData` — constructs `RatioNodeData L g h` from a relative split at `u_g · u_h⁻¹`
4. W3-transport (using #3)
5. W3 (unit-generated cover refinement)
6. W2 (using Cor 7.32; output the derived `restricted_standard_cover_generated_by_units` property, NOT the technical Cor 7.32 side conditions)
7. W1 (from Hübner-Nullstellensatz)
8. Assemble + update downstream `productRestrictionSub_isInducing_via_ratio_tree`

## Local caution

`isUnit_base_s_in_presheafValue_of_subset` should be proved from the project's **rational-containment / restriction-map denominator-unit data**, not bare set inclusion. The mathematically clean reason: the denominator of the larger rational datum becomes a unit after restricting to the smaller rational datum.

## Other risks (proof-side, not architectural)

- For `RatioNodeData.cover`: if `plus = minus`, `{plus, minus}` collapses to a singleton. Downstream NODE induction must use the **projection/absorption method**, not a strict two-factor homeomorphism requiring distinct pieces.
- W3-transport must use the constructed `RatioNodeData` consistently — `RatioTreeRealization` is designed to enforce this.
- For W1, verify the existing refinement theorem actually produces the absolute `Ideal.span S = ⊤` form (not just relative over `O(C.base)`).
- V.1 (Stacks 00MA) is external; should not block proof work on W1–W3.
