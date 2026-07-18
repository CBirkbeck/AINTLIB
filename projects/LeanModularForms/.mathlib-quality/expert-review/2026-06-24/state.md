# Expert-review session state

- Generated: 2026-06-24
- Audience: formalization + math expert (knows both the math and Mathlib's current state); **same
  reviewer as the 2026-06-19 round** — this brief is an explicit follow-up.
- Goal of brief: all three — (1) cheaper route to (FIH), (2) soundness check on the isolated inputs,
  (3) best path forward; sharpened to the formalize-vs-cite decision on IHR-c and a lighter route to
  period-map injectivity.
- Scope: whole Group A (Hecke-eigenvalue arithmetic), centered on the one remaining k≥2 input.
- Reply received: true (2026-06-24)
- Reply integrated: true (2026-06-24) — see integration.md; decision: Eichler-integral/Bol route, plan via /develop --decompose then build

## Relationship to the 2026-06-19 round

The prior brief asked lattice-vs-modular-symbols. Reviewer verdict (see ../2026-06-19/reply.md):
the q-expansion lattice is "sufficient but stronger than necessary"; build a finite integral
modular-symbol module + INJECTIVE period map (IHR → FIH); k=1 out of scope (Deligne–Serre). We
EXECUTED this. This round reports the result and asks the deferred formalize-vs-cite decision +
whether injectivity can avoid the full boundary identity.

## Questions in the brief

| # | Question (from §1–§4 of the brief) |
|---|------------------------------------|
| Q1 | The deferred decision, now forced: fully formalize IHR-c (the area→boundary-period identity over the tiling, a multi-month modular-curve-boundary build) vs. isolate (FIH)/(IHR-c) as a cited classical input (Shimura Thm 3.51 / DS Ch.6)? Is (ii) acceptable practice here? |
| Q2a | Can injectivity of the period map be obtained from non-degeneracy of the cup product / Petersson pairing on H¹_par(Γ₁(N), Sym^{k-2}) — via the group-cohomology Eichler–Shimura (arXiv:1701.00611), using the divisor cocycle now in Mathlib's H¹ — WITHOUT the geometric boundary integral (8.2.22)? |
| Q2b | Can "all periods of f vanish ⟹ f=0" be proved directly from the q-expansion (periods as explicit functionals of the a_n), bypassing Petersson and the boundary identity? |
| Q2c | Has the cost calculus shifted? Given injectivity is now a multi-month boundary build, AND the two prior corrections to the q-expansion lattice (root-of-unity χ(d) ⟹ O_{ℚ(χ)}-lattice; ℤ[1/N] misses bad primes), is modular symbols still the lighter route to (FIH), or is the lattice / a cohomological / a q-expansion route now preferable? |
| Q3 | Is isolating k=1 as the full-rank Hecke-stable lattice input (cited Deligne–Serre) the right disposition? Does the integral-q-expansion-lattice argument go through at k=1 without full Deligne–Serre? |
| Q4 | Soundness: are (IHR-c) [nonzero Manin boundary cycle] and the lattice input [full rank explicit, faithfulness derived] faithfully stated, matching Shimura (8.2.22) and Thm 3.52? |

## Ticket-board snapshot at brief time (open mathematical sub-goals)

- **(FIH)** — integral Hecke algebra finite over ℤ: INSTALLED; rests on the two inputs below.
- **(IHR-c)** = `interior_edges_cancel_sum` / `periodPairingA_eq_boundary_period` — the area→Manin-
  boundary-period identity, Shimura (8.2.22), k≥2. THE open k≥2 input. Everything around it proved
  (single-tile region-Stokes, binomial bridge, FTC edge assembly, Manin paired boundary, divisor
  cocycle in H¹). Believed multi-month.
- **(L)** = `exists_HeckeStableLattice` — full-rank Hecke-stable ℤ-lattice in S_k; the k<2 (Deligne–
  Serre) input; would also re-prove k≥2 via the all-weights lattice lemma. Only deep content = full
  rank.
- PROVED: (FIH)⇒(A),(B),labels (T004/T005/T006, LMFDB canonicity); IHR-a (𝕄 finite); IHR-b (integral
  Hecke action + ι equivariance); abstract endgame; period injectivity MODULO (IHR-c); single-tile
  Stokes; divisor cocycle ∈ Z¹.

## Stuck points (from §1–§2 of brief)

1. IHR-c / (P): area→boundary-period identity over the SL₂(ℤ)-tiling. Obstruction = per-tile slashing
   breaks interior-edge cancellation; global-form route hits non-Type-I translated tiles (no Mathlib
   region-Stokes); residue = Manin↔Siegel model change (no Mathlib foothold). Empirically established.
2. (L): full rank of the integral-q-expansion lattice (the q-expansion / rationality principle).

## Reference list (from §6)

Shimura 1971 (§3.5: (3.5.20), Thm 3.48(3), 3.51(1), 3.52; §8.2: (8.2.17)–(8.2.22), (8.2.18c)); Diamond–
Shurman 2005 (§5.4; Thm 5.8.2(a); Ch.6, Thm 6.5.1); Miyake 2006 (Thm 4.5.9, 4.5.19(2)); Manin 1972;
Eichler–Shimura via group cohomology (arXiv:1701.00611); Deligne–Serre 1974.
