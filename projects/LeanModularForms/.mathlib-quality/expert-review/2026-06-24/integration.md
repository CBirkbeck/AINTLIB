# Reply integration — 2026-06-24 (round 2)

Reply: ./reply.md   Brief: ./brief.md   (follow-up to ../2026-06-19/)

## Verdict
A **third option** for period-map injectivity (IHR-d): the **Eichler integral + Bol's identity**,
avoiding IHR-c (the area→boundary identity), Petersson, cup products, Green–Stokes, and the
fundamental-domain tiling. Uses only one-variable integration, an SL₂(ℤ) change of variables, cusp
Fourier expansions, and negative-weight vanishing. **This eliminates `interior_edges_cancel_sum` (the
multi-month wall) from the critical path for k≥2.** Fallback if awkward in Lean: cite classical
period-map injectivity (ranked injectivity > IHR-c > FIH).

## Interpretation summary (reply → our questions)
- Q1 (third option): ADOPT Eichler/Bol injectivity. Don't switch to q-lattice; don't build IHR-c.
- Q2a (cup product): NOT cheaper — needs Haberland comparison to Petersson, recreates the integral.
- Q2b (Fourier inversion): possible (Paşol–Popa) but not foundational; stronger than injectivity.
- Q2c (cost calculus): modular-symbol route still lightest; expensive part was Petersson/Haberland,
  not symbols.
- Q3 (k=1): cite Deligne–Serre **Prop 2.7** (finite free Hecke+diamond-stable lattice, S_K=K⊗L),
  which is pre-Galois-rep so does NOT import full DS weight-1. CAVEAT: Prop 2.7's T_p-stability
  Fourier formula is p∤N — bad-prime U_p must be added separately.
- Q4 (soundness): verified against code — BOTH catches are precision/framing issues; **code is
  sound**. (§7) `boundaryDivisor ∈ Div0` (raw), `rawPairing` is pre-descent, `div0Rep` acts on the
  divisor factor only → nonzeroness is at the raw level, correct (not a 𝕄-coinvariant claim). (§8)
  `HeckeStableLattice` bundles `finite` as a field → sound (f.g. is genuinely substantive, not
  "routine"). The errors were in the BRIEF's prose only.

## Decision (user: "decompose then build")
Plan the Eichler-integral route via /develop --decompose (source-faithful leaves vs mathlib + the
existing periodForm-primitive infra), then execute. Eichler integral E_f = the holomorphic primitive
`Fp` of `periodForm` we already have (`exists_primitive_periodForm`, `isExactOn_upperHalf`); new
ingredient = negative-weight vanishing (E_f^{12}·Δ^n weight 0 ⟹ 0; weight-0 cusp form = 0).

## Changes to apply (during/after the decompose pass)
1. NEW: `periodMap_injective_via_eichler` (≈6 atomic lemmas) → reprove `periodMap'_injective`.
2. SUPERSEDE `interior_edges_cancel_sum` / IHR-c (and the Petersson→boundary route) — off critical
   path; "do not formalize"; keep proven pieces (`tile_stokes_fd`, binomial bridge) dormant/reusable.
3. Docstring fixes: raw-vs-coinvariant typing note on `boundaryDivisor`; k=1 citation → DS Prop 2.7 +
   bad-prime U_p caveat in `exists_HeckeStableLattice`.
4. Record the secured fallback: cite period-map injectivity.

## Open items
- The negative-weight-vanishing ingredient: confirm Δ (discriminant) + "weight-0 cusp form = 0"
  (S_0(Γ₁N)=0) availability in project/mathlib (to be checked in the decompose pass).
- Whether the Eichler integral needs the full (τ−z)^{k-2} universal kernel assembled from the
  per-P period primitives (binomial), or can be done per-P then summed.
