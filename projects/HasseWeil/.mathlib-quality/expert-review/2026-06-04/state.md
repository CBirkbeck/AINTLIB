# Expert-review session state (round 23)

- Generated: 2026-06-04
- Audience: the same senior arithmetic-geometry reviewer as rounds 1–22
- Goal of brief: specific-blocker guidance — close the SINGLE remaining residual of the (assembled, compiling) unconditional Hasse bound: the pencil scaling leaf for `p∣r, p∤s` (where the `r·π` summand turns inseparable). Routes A (geometric comap, ~800 lines) vs B (weaken the discriminant reduction to need Q≥0 only on {p∤r∧p∤s}, drop p∣r, ~150-250 lines).
- Scope: the one open case; the bound is otherwise assembled + axiom-clean (leaves π, 1−π closed; pencil closed for p∤r∧p∤s + r=0).
- Depth: focused
- Reply received: false
- Reply integrated: false

## Questions in the brief (verbatim from §5)

| # | Question |
|---|----------|
| Q1 | (main) Clean low-machinery proof of `Q(r,s)=qr²−trs+s² ≥ 0 on {p∤r∧p∤s} ⟹ Q≥0 ∀(r,s)` (q>0, p prime)? Slick explicit (r,s) prime to p with Q<0 when t²>4q (avoiding a general density argument)? = crux of route B. |
| Q2 | Is route B's hypothesis weakening sound + COMPLETE (edge cases t=0, p∣q)? Does Q≥0 on {p∤r∧p∤s} really suffice? |
| Q3 | Route A: does "separable ⟹ unramified at O (e_O=1)" have a clean differential proof (φ*ω nonvanishing at O ⟹ e_O=1) sidestepping the inseparable-summand division-poly analysis — so ord_∞=−2 follows from rπ−s separable, shortening A drastically? |
| Q4 | A THIRD route? (handle p∣r via an algebraic identity to the p∤r members, or supply the p∣r scaling at the pairing level without the comorphism construction) |
| Q5 | (meta) Which route to a genuinely axiom-clean result, and any integrity concern with the #ker-not-deg exponent (the bound isn't literally about deg(rπ−s))? |

## Ticket-board snapshot at brief time

No /develop tickets.md. In-session: the bound `hasse_bound_unconditional` is ASSEMBLED + compiles, carrying sorry only via the p∣r pencil case (`pencilScalingComapDataCard_pDvdR`). Leaves π (frobeniusScaling_holds, Galois) + 1−π (oneSubFrobeniusScaling_holds) closed axiom-clean; pencil closed for p∤r∧p∤s (canonical) + r=0; finiteKer, ∞-orders, transport-to-O all general/done. deg=#ker route (avoids #ker=deg). Committed at 9dfc649 (+ uncommitted p∣r residue/keystone progress).

## Stuck points (from §3/§4)

1. The p∣r pencil scaling: the `r·π=[r]∘π` summand is inseparable for p∣r, breaking the canonical division-poly comap construction (the ord_∞=−2 nonvanishing step is p∤r-gated). Verified ord_∞=−2 still holds (asymmetric pole, not the symmetric tie) — tractable but ~800 lines (route A). Route B (weaken the qf reduction to p∤r∧p∤s) drops it.

## Reference list

[Silverman] Arithmetic of Elliptic Curves 2nd ed GTM 106 — III.4.10, III.5.1–2, III.6, III.8, V.1.1. Prior replies rounds 16–22 (this conversation).
