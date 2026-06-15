# Decomposition — Thm 8.28(b) flatness summit (`presheafValue` noetherian → `isSheafy`)

**Date:** 2026-06-03 · `/develop` resume. Source read in full: wedhorn.txt:4051–4255 (Thm 8.28 →
Lemma 8.34) + Remark 7.55 (3504) + Remark 8.29 (4074). Repo state mapped (Explore audit).

## Goal
```lean
-- Wedhorn828.lean:~2047 — SORRY-FREE assembly; the work is in its two fields
theorem isSheafy_of_stronglyNoetherian_828b : IsSheafy A where
  embedding := cor_8_32_productRestrictionSub_isEmbedding C   -- separation
  gluing    := lemma_8_34_gluing                              -- acyclicity
```

## Wedhorn's proof chain (faithful skeleton, with repo status)
- **Thm 8.28(b)** ← (Prop A.4 + A.3(2)) ← **Lemma 8.34** (acyclicity of T-covers).
- **Lemma 8.34** (4222) ← **Lemma 8.33** (Laurent) + **Cor 7.32** (`cor_7_32_dominating_unit`, ✅ sorry-free) + Prop A.3(1)(2)(3) induction.
- **Lemma 8.33** (4151) ← **Cor 8.32** (ε injective) + Examples 6.38/6.39 + λ/λ'/ι diagram chase.
- **Cor 8.32** (4142) ← **Prop 8.30** (each restriction flat) + cover ⟹ faithfully flat (maximals).
- **Prop 8.30** (4095) ← Remark 7.55 chain (reduce to basic Laurent U₁/U₂) + Example 6.38 over `B` (`O_X(U₁)=B̂⟨X⟩/(f−X)`) + **Lemma 8.31** (✅ sorry-free: `lemma_8_31_{fSubX,oneSubfX}_flat`, `[IsNoetherianRing B]` only).
- **Lemma 8.31** ← **Remark 8.29** (`muMap`, ✅ sorry-free).

## Repo status — what's DONE (faithful, sorry-free) vs. the residuals
**DONE (sorry-free, no noeth-A₀):** Remark 8.29 (`muMap`), Lemma 8.31 (both flat-quotients),
Cor 7.32 (`cor_7_32_dominating_unit`), Lemma 7.45 (`exists_spa_point_supp_ge_maxIdeal_of_complete`,
`isUnit_iff_forall_not_vle_zero_of_complete` = Nullstellensatz 7.52(2)), Banach OMT / Prop 6.18,
the Example-6.38 noetherian discharge (this session), `faithfullyFlat_pi_of_prime_surjection`,
`productRestrictionSub_injective_of_flat_and_lifting`, `isSheafy_…_828b` (assembly).

**The genuine residuals (6 sorries on the critical path):**

- **L1 — `prop_8_30_relative_laurent_flat`** (Wedhorn828:1838). Relative Example 6.38 over
  `B := presheafValue D` + Remark 7.55 chain. **Now MORE tractable than the old docstring claims:**
  the session just built the *generic* general-`n` Tate topology (`MvTateAlgebraTopology`, any Tate
  ring) + the Example-6.38 completion-comparison iso for general `D`. The faithful route: re-instantiate
  that machinery at base `B`, identify `O_X(Xᵢ) ≅ₗ[B] O_X(Xᵢ₋₁)⟨X⟩/(f̄−X)` for each Remark-7.55 step,
  and compose `Module.Flat` via `lemma_8_31_*` (done) + `Module.Flat.of_linearEquiv`. NO Fubini (direct
  `Fin n`), NO case-(a) noeth-A₀ (the entangled `relativeLaurentNormalized_equiv` is bypassed).
  Source: Prop 8.30 proof (4099–4104) + Remark 7.55 (3504–3517) + Example 6.38 (2700).

- **L2 — `cor_8_32_maximal_liftedIdeal_ne_top`** (Wedhorn828:1942). The faithful Cor 8.32 maximals
  criterion. **HIGH-ROI:** blocked only by `exists_spa_point_supp_ge_in_presheafValue` (Cor832:1598),
  which carries `[IsNoetherianRing P.A₀]` + `[IsNoetherianRing locSubring]` — but its conclusion is
  available sorry-free + noeth-A₀-free from `exists_spa_point_supp_ge_maxIdeal_of_complete`
  (Lemma745:710) applied on the completion `presheafValue C.base`. Retype L2's helper to route
  through Lemma 7.45 directly. Source: Cor 8.32 (4142, "immediate") + Lemma 7.45.

- **L3 — re-wire faithfully-flat/injective to the maximals route.** `cor_8_32_productRestriction_faithfullyFlat`
  (1948) + `cor_8_32_productRestrictionSub_injective` (1974) currently consume the DEAD-END
  `cor_8_32_prime_surjection` (1912, needs Bourbaki rank-1, absent). mathlib's `Module.FaithfullyFlat`
  is defined by the maximals criterion (`submodule_ne_top`), so add `faithfullyFlat_pi_of_maximal_ne_top`
  (Cor832, mirror `_of_prime_surjection`) consuming L2 + Prop 8.30. Then `cor_8_32_prime_surjection`
  is DELETED. Source: mathlib `Module.FaithfullyFlat.iff_flat_and_…`.

- **L4 — `cor_8_32_productRestrictionSub_isInducing`** (Wedhorn828:1988). Signature-level noeth-A₀
  retype of the OMT input (`productRestrictionSubToEqualizer_isOpenMap`, BanachOMT, sorry-free math).
  Source: Prop 6.18(2) / the Tate-absorbing OMT.

- **L5 — `lemma_8_33_laurent_cover_gluing`** (Wedhorn828:2009). The 2-element Laurent diagram chase.
  ε injective (L2/Cor 8.32) + Examples 6.38/6.39 (`example638Bivariate_equiv` for `U₁∩U₂`, ✅ exists)
  + λ/λ'/ι surjectivity + `im ι = ker λ`. Depends on Prop A.3 Čech machinery (WedhornCechAcyclicity,
  partial). Source: Lemma 8.33 proof (4160–4210).

- **L6 — `lemma_8_34_gluing`** (Wedhorn828:2029). The (i)–(iv) induction: Laurent acyclic (L5 +
  Prop A.3(3)) → T-cover refines to unit-Laurent (Cor 7.32, done) → combine (Prop A.3(1)(2)). DEEPEST:
  depends on Prop A.3(1)(2)(3) — `WedhornCechAcyclicity.lean` has ~25 sorries; needs its own
  sub-decomposition to identify the blocking Prop-A.3 leaves. Source: Lemma 8.34 proof (4225–4255).

## Tractability tiers (feasibility)
- **TIER 1 — tractable now (Cor 8.32 cluster):** L2 (maximals via Lemma-7.45 retype), L3 (re-wire to
  maximals + delete prime_surjection), L4 (OMT noeth-A₀ retype). ~4–6 tickets. Unblocks the
  `embedding` field of `isSheafy`. Highest ROI; the ingredients are all sorry-free.
- **TIER 2 — tractable via the just-landed infra (Prop 8.30):** L1 (relative Example 6.38 over `B`
  + Remark 7.55 + Lemma 8.31). The big new construction, but the generic `MvTateAlgebraTopology` +
  Example-6.38 iso make it feasible without Fubini/noeth-A₀. ~3–5 tickets.
- **TIER 3 — DEEP (Čech gluing):** L5 + L6 depend on Prop A.3(1)(2)(3). `WedhornCechAcyclicity.lean`
  carries ~25 sorries; this needs its OWN `/develop --decompose` pass against Appendix A before
  ticketing (the Čech-cohomology machinery is a separate sub-project). Flag, don't ticket blind.

## NOT to do (faithfulness guards)
- Do NOT route Cor 8.32 through `cor_8_32_prime_surjection` (needs absent Bourbaki rank-1 domination).
- Do NOT route Prop 8.30 through `presheafValue_flat_of_canonical`/`flat_quotient_oneSubfX_general P`
  (Wedhorn case (a), ℂ_p-false noeth-A₀).
- Do NOT use `exists_spa_point_supp_ge_in_presheafValue` as-is (noeth-A₀); retype via Lemma 7.45.
- Run the ℂ_p test on every hypothesis (no noeth-A₀ smuggling).
