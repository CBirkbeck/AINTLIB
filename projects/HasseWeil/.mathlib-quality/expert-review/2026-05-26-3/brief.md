# Review note (round 3) — QF: genuine rV−s via formal-group reduction vs Pic⁰ comorphism

*2026-05-26, same reviewer. Short follow-up to round 2's "B-narrow + C" decision. One
sub-fork, surfaced by testing the existing construction.*

## Context (round 2 recap)

You decided the QF route is **B-narrow**: construct, for β = rπ−s only, a *genuine*
degree-bearing dual β_dual = rV−s with a real pullback, with C (K̄-extensionality) as a
supporting accelerator. We then tested the construction.

## Finding: the `addIsog` route to genuine rV−s is confirmed obstructed

The project's existing genuine-isogeny constructor (`addIsog`, used successfully for the
π-side rπ−s) builds rV−s modulo one pole bound: `ord_∞((rV−s)*x) < 0` (its function-field
injectivity needs the dual's x-coordinate to have a pole at the identity O). We proved this
bound is **not** reachable on the V-side via the existing machinery:

- The "weak bound" (just `intDegree > 0`, a pole exists) is **not** easier than the exact
  value, because `ord_∞(g) = −2·intDegree(g)` is an exact equivalence in our setup — so
  proving either still requires the **sign of the dominant order**, which is exactly the
  3-way order tie at −6 (`X₁²X₂, X₁X₂², −2Y₁Y₂`) we flagged earlier (V does not scale orders,
  so the π-side's unique-dominant-term argument has no V-analogue).
- The transcendence/pole shortcut is **circular**: rV−s is *built by* `addIsog`, whose
  injectivity is what this bound feeds — so rV−s isn't yet an isogeny when the bound is needed.

So the genuine rV−s cannot come from `addIsog`. The honest discharge of the pole bound is
**formal-group / kernel-of-reduction** content: the two summand points `(rV)(P)` and `(−s)(P)`
both lie in `E₁` = the kernel of reduction at O (a subgroup), so their sum does too (unless O,
excluded), forcing the pole — Silverman IV.1–IV.3 / VII.2. This is an *alternative* to the
Pic⁰ comorphism for getting the genuine rV−s.

## Questions

**Q1.** For the specific genuine-rV−s pole bound, do you prefer (a) **formal-group
kernel-of-reduction** (build `E₁ = {points reducing to O}` is a subgroup, then the pole
follows) or (b) the **Pic⁰ comorphism** you recommended? Is (a) lighter for *this* bound?

**Q2.** Does your "Pic⁰ comorphism" construction internally rely on formal-group reduction
anyway — i.e. are (a) and (b) the same content in different clothes, or genuinely different
developments?

**Q3.** mathlib's `Reduction` reduces curve *coefficients*, not points; our formal-group
scaffold (`FormalIsogenySeries`) has open `sorry`s. So route (a) means building the
`E₁`-kernel-of-reduction-subgroup infrastructure (Silverman VII.2). Is that a known-tractable,
self-contained development, or comparable in effort to the Pic⁰ comorphism?

## Aside (V.1.3 status — good)

The other keystone (V.1.3 point count) is nearly closed: reduced to a single sharp
valuation-identity `v_{P_T} = exp(−ord_T)` (the Sinf carrier's prime-adic valuation equals the
curve's order), with a concrete `ValuationSubring`-maximality discharge route in progress. No
question here — just context that QF is now the sole deep frontier.
