# T-IV-2-005: Formal group Ê of an elliptic curve

**Status**: BLOCKED — OFF Hasse-critical path (2026-05-08)

**Reviewer-driven correction**: this ticket WAS thought to be on the
qf_nonneg / Hasse-critical path via the formal-group polynomial form.
External reviewer confirmed that approach is NOT how Silverman proves
III.6.1, and recommended the differential bypass instead:

```
[p]*ω = 0 in char p (one-line corollary of shipped omegaPullbackCoeff_mulByInt)
  ⇒ [p] inseparable (III.4.2(c))
  ⇒ [p] = ψ ∘ Frob_p (II.2.12, T-II-2-016)
  ⇒ Frobenius dual ψ exists (III.6.1 Case 2)
```

This route avoids the abstract `FormalGroup R` packaging entirely. Bridge
(a) (the four formal-group axiom verifications, including associativity
which is genuine Silverman IV.1 substance, ~500-1500 LOC for direct proof)
is therefore **OFF the Hasse-critical path**. This ticket remains BLOCKED
as a long-term mathematical objective (formal group theory is a worthy
upstream goal in its own right) but is not driving Hasse closure.

The real work for `qf_nonneg` is now in T-FROB-OMEGA-ZERO + T-FROB-INSEP +
T-II-2-016 + T-FROB-DUAL-ASSEMBLY + T-VERSCHIEBUNG-ADAPTER (see INDEX).

**Silverman**: IV.2.3
**Module**: `HasseWeil/FormalGroup/Curve.lean`
**Owner**: (existing)
**Estimated lines**: 30
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-1-008 (formal addition F(z₁, z₂))
- T-IV-2-001 (FormalGroup R)

## Blocks
- T-IV-3-005 (Ê(M) → E(K))
- T-IV-BRIDGE-001..004

## Statement (Silverman IV.2.3)
For a Weierstrass curve `E` over `R`, the formal group `Ê` over `R` is the
formal group law `F(z₁, z₂)` from T-IV-1-008.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The formal group of an elliptic curve.
    Reference: Silverman IV.2.3. -/
def WeierstrassCurve.formalGroup (E : WeierstrassCurve R) : FormalGroup R

end HasseWeil.FormalGroup
```

## Notes
- Existing in `HasseWeil/FormalGroup.lean`. Wraps T-IV-1-008.

## Progress log
- 2026-04-08 [auto] PARTIAL — exists in HasseWeil/FormalGroup.lean
