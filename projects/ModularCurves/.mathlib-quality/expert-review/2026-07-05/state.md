# Expert-review session state

- Generated: 2026-07-05 (Europe/London)
- Audience: senior arithmetic geometer (no proof-assistant knowledge assumed)
- Goal of brief: soundness check on the *definitions* + strategic guidance on the six
  decision points, before execution starts
- Scope: whole project (phase 1–3 plan)
- Status: sent; reply received and integrated
- Reply received: true (2026-07-05)
- Reply integrated: true (2026-07-05; see integration.md)

## Questions in the brief (verbatim §8 headers)

| # | Question |
|---|----------|
| Q1 | Definition of record for elliptic curve over a scheme (Weierstrass-fibre form vs waiting for cohomology/genus) |
| Q2 | Fibre condition at residue fields vs geometric points |
| Q3 | Group-law route: Abel/Pic⁰ with named cohomology black boxes — endorse? which boxes exactly? |
| Q4 | Registered-data discipline: is "unique up to stated specification" ever insufficient? |
| Q5 | Weil pairing construction of record (KM 2.8 norm/divisor vs theta groups vs autoduality); composite N |
| Q6 | Normalisation of the Weil pairing (fix once; propagates into p and the ρ-level condition) |
| Q7 | Moduli packaging: Ell/R engine + fppf statements + deferred stack packaging — honest and future-proof? |
| Q8 | Which integral (char p | N) statements will consumers force earliest? |
| Q9 | Y(ρ̄) via Galois-descent twist of Y(N): obstructions to the moduli interpretation; slicker routes? |

## Ticket-board snapshot at brief time

24 work tickets + 11 cleanup tickets, 6 streams (A foundations, B torsion/μ_N, C Weil
pairing, D Drinfeld structures, E moduli/representability, F Y(ρ,p)); start-now set
T-E1, T-E2, T-A2, T-B2, T-D3, T-F0; milestones T-E2, T-E7 (Y₁(N)), T-E9 (Y(N)),
T-F4 (Y(ρ̄)). Full board: `.mathlib-quality/tickets.md` at commit `b758179b`+.

## Stuck points (from §7 of brief)

1. Genus bottleneck → Weierstrass-fibre primitive (Q1/Q2)
2. Abel/Pic⁰ chain length and route (Q3)
3. Weil pairing construction + normalisation (Q5/Q6)
4. Γ₀(N) fppf-cyclicity staging (§7.4)
5. Full KM text not yet in refs (quote-gates open)

## Reference tags

[KM] [Loe] [Buz] [Hida] [Katz] [Sil] + SGA1-VIII / EGA-IV-11.3.10 / Oort–Tate boxes.
