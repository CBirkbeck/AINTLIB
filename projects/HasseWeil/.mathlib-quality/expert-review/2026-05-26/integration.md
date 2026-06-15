# Reply integration — 2026-05-26 (QF keystone route)

Reply received from the prior-rounds reviewer on 2026-05-26.
Brief: ./brief.md   Reply: ./reply.md   State: ./state.md

## Interpretation summary

| # | Reviewer point | Maps to | Type |
|---|----------------|---------|------|
| 1 | Commit to Route 1 (Pic⁰ / restricted dual additivity); steer unchanged | Q1 | direct answer |
| 2 | No substantially simpler path; parallelogram ≡ III.6.3, point-count insufficient, Weil/determinant heavier | Q2 | direct answer |
| 3 | Route-2 sign worry confirmed — degree-square gives only deg=\|Q\| | Q3 | direct answer (validates) |
| 4 | Invest in genuine-isogeny extensionality (point-map ⟹ pullback ⟹ degree), parallel, but it does NOT replace the dual identification | Q4 | direct answer + lemma |
| 5 | Absorb ordinary/supersingular in Verschiebung/inseparability infra, never in the QF proof | Q5 | direct answer |
| 6 | Audit Wall A's blanket ord=−2 → general form ord_O(α*x) = −2·e_α(O) | unprompted | correction |

## Decision (committed)

**`qf_nonneg` (Silverman III.6.3) is committed to Route 1: restricted dual additivity
`(rπ − s)^ = rV − s` on the Frobenius plane ℤπ + ℤ, via Pic⁰ functoriality**, with the
**genuine-isogeny extensionality lemma** as the high-leverage parallel shortcut. The
irreducible mathematical residue is the dual identification itself; everything else is
either shipped or formalisation friction the extensionality lemma removes.

## Changes applied

1. New committed-route ticket board `tickets/QF-PIC0-ROUTE.md` (extensionality lemma;
   restricted dual additivity on ℤπ+ℤ; Pic⁰(E)≅E activation; dual-via-Pic⁰ functoriality;
   qf_nonneg close).
2. Picard ticket stack (`tickets/picard/`) promoted to **primary critical path** for the QF
   witness (was background infrastructure).
3. Route 3 docs parked (not superseded): `decomposition-WallB-y-side-2026-05-25.md`,
   `v-side-pole-bound-obstruction.md`, `decomposition-L2-char-divisible-2026-05-25.md` —
   each carries a PARKED banner pointing here. Retained as fallback for local computations.
4. Wall A `ord = −2` audit note recorded (below).

## Settled questions (decisions, no further work)

- **Q2**: no simpler route avoids restricted dual additivity; torsion-determinant is the
  only serious alternative and is heavier. Do not pursue.
- **Q3**: the abstract degree-square route is NOT a separate lighter route — without the
  dual identification it yields only `deg(rπ−s) = |Q|`, not the signed identity. It folds
  into Route 1.
- **Q5**: ordinary/supersingular is absorbed in Verschiebung existence / inseparable-degree
  infrastructure (already constructed), NOT in the QF proof. No char split in the final
  quadratic-form argument.

## Wall A audit note (Q6)

The blanket claim `ord_∞((rV−s)*x) = −2` is only valid when the isogeny is separable at O;
the general local formula is `ord_O(α*x) = −2·e_α(O)` with `e_α(O)` the
ramification/inseparable contribution (tied to `deg_i(α)`). This affects only the **parked**
V-side computation (Route 3). It does **not** affect the in-hand V.1.3 bridge: there the
relevant isogeny is `1 − π`, which is **separable** (shipped witness), so `e = 1` and the
`ord = −2` at kernel primes is correct. No change to the V.1.3 route.

## Changes rejected by user

None.

## Open questions remaining

None unanswered — the reviewer addressed Q1–Q5 directly and added the Q6 correction.
