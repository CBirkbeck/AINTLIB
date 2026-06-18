# Hasse-Weil Closure Campaign

This directory contains the **final-push tickets** that close the Hasse-Weil
bound formalization. All remaining mathematical content in the proof reduces
to the two open holes in `HasseWeil/Hasse/Unconditional.lean`:

- **HOLE D** (fiber-witness for β_pc = 1−π): needs real isogeny pullback
- **HOLE E** (degree as quadratic form): needs III.6 chain

## Tickets

| Ticket | Goal | Hole closed | Stream |
|---|---|---|---|
| [T-HASSE-CLOSE-A](T-HASSE-CLOSE-A-addition-pullback-transcendence.md) | Close 3 AdditionPullback transcendence sorries | HOLE D | C |
| [T-HASSE-CLOSE-B](T-HASSE-CLOSE-B-bridge-001-formal-series.md) | BRIDGE-001 + BRIDGE-003 → III.6.9 | HOLE E (Route B) | D / E |
| [T-HASSE-CLOSE-C](T-HASSE-CLOSE-C-dual-existence.md) | T-III-6-001 dual existence → III.6.9 | HOLE E (Route A) | C |
| ↳ [T-HASSE-CLOSE-C-VERSCHIEBUNG-FROBENIUS](T-HASSE-CLOSE-C-VERSCHIEBUNG-FROBENIUS.md) | Frobenius-specific Verschiebung (Route A pivot) | HOLE E (Route A pragmatic) | C |

**Pivot note (2026-04-27)**: T-HASSE-CLOSE-C's universal `exists_dual` was
discovered to be **structurally unprovable** in the current `Isogeny`
representation (independent pullback/hom fields admit non-unique duals;
documented in `HasseWeil/DualIsogeny/RouteA.lean` docstring). The Hasse-Weil
strategy pivoted to the Frobenius-specific Verschiebung sub-ticket, which is
sufficient for HOLE E without requiring universal exists_dual. Tier 1
(`hole_e_closer_via_frobenius_dual_witness`) shipped axiom-clean in
`HasseWeil/Hasse/HoleE.lean`; Tier 2 (`verschiebungIsog` definition + IsDualOf)
is the new sub-ticket above.

## Strategy

**HOLE D** has **exactly one** path: T-HASSE-CLOSE-A. There is no alternative.
Ticket A is the **critical path** and must be assigned.

**HOLE E** has **two parallel paths** (Route A vs Route B). Both are legitimate
Silverman content. Running both in parallel hedges against one getting stuck.

Recommended assignment for 3 workers:

- **Worker 1**: T-HASSE-CLOSE-A (AdditionPullback) — hard-path, no substitute
- **Worker 2**: T-HASSE-CLOSE-B (BRIDGE-001) — shorter path, formal-group work
- **Worker 3**: T-HASSE-CLOSE-C (dual existence) — longer path, kernel theory

If Worker 2 or Worker 3 finishes first, HOLE E closes and the other's work
becomes stream-C/D infrastructure rather than Hasse-blocking. If both finish,
we have two independent proofs of III.6.9 — the redundancy is a bonus, not
waste, since it exposes both API routes for downstream users.

## When all three land

`HasseWeil/Hasse/Unconditional.lean:hasse_bound_target` becomes axiom-clean
(`[propext, Classical.choice, Quot.sound]` only). The original
`HasseWeil/HasseBound.lean:hasse_bound` becomes a one-line corollary through
it. The formalization is complete.

## Wire-up reference

Once all three tickets close, the HOLE D and HOLE E sorries in
`Unconditional.lean` discharge as follows:

```lean
case h_pc_fiber_witness =>
  -- HOLE D: via T-HASSE-CLOSE-A → real isogOneSub → T-II-2-009 fiber witness
  exact hole_d_via_unconditional_fiber_card W ... -- (worker-A's shipped closer)
case h_qf_deg =>
  -- HOLE E: via T-HASSE-CLOSE-B or -C → T-III-6-009
  intro r s
  exact isogSmulSub_degree_quadratic_closed ... -- (worker-A's shipped closer)
```
