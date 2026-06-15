# Expert-review session state (round 13)

- Generated: 2026-05-15 (same day as rounds 6-12)
- Audience: ChatGPT Pro (continuing series)
- Goal: Verify round-12 fix (denominator-cleared ratio data without global inverses).
- Scope: New `ratioPlusDatumDC`, `ratioMinusDatumDC`, `ratioCoveringDC`; updated `RatioLaurentTree.Refines` and `.allSplitsInducing`.
- Reply received: false
- Reply integrated: false

## Questions

| # | Question |
|---|---|
| Q1 | Are the denominator-cleared formulas correct? |
| Q2 | Is `ratioCoveringDC` the right 2-cover for inducing? |
| Q3 | Does this correctly capture Wedhorn's ratio split? |
| Q4 | Architecture finally correct? Should I.1 switch to RatioLaurentTree A? |

## File state at brief time

- Sorries: W1, bridge1, bridge2, ratioPlusDatumDC.hopen, ratioMinusDatumDC.hopen, ratioCoveringDC.hsubset, ratioCoveringDC.hcover, W2, W3, W3-transport, I.1 body, V.1.
- `lake build` clean.
