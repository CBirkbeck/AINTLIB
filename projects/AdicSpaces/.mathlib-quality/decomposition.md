# Decomposition — Wedhorn Theorem 8.28(b): `isSheafy_of_stronglyNoetherian_828b` (WHOLE HEADLINE)

**Mode:** `/develop --decompose` (adversarial), whole headline. **Date:** 2026-06-05.
*(Supersedes the 2026-06-04 Čech-layer-only pass — prior version in git. This pass covers BOTH halves
and uses `lean_verify` axiom sets to correct earlier `[PROVEN]` mislabels.)*
**Source:** Wedhorn, *Adic Spaces*, `/private/tmp/wedhorn.txt`. **All status claims verified by `lean_verify` (sorryAx ⇒ has a sorry descendant).**

## Skeleton location (existing — takeover-decompose)
- Faithful headline: `Adic spaces/Wedhorn828.lean:2424` (`isSheafy_of_stronglyNoetherian_828b`).
- Embedding chain: `Adic spaces/Wedhorn828.lean` (Cor 8.32 / Prop 8.30 / Remark 7.55).
- Gluing assembly (complete but defect-carrying, disconnected): `Adic spaces/WedhornCechAcyclicity.lean:3641` (`isSheafy_ofStronglyNoetherianTate_clean`).
- Banach OMT: `WedhornBanachTheorem.lean`, `BanachOMT.lean`. Cor 7.32: `Cor732.lean`.
`lake build` passes (3147 jobs, sorries-only).

## Wedhorn's proof (transcribed, with line locators)
```
Thm 8.28(b)  IsSheafy A                                              wedhorn.txt:4214-4220
 ├─ EMBEDDING  O_X(X) → ∏O_X(Uᵢ) is a topological embedding (inj + inducing)
 │   ├─ injective ⇐ Cor 8.32 faithfully flat                        wedhorn.txt:4142-4149
 │   │   └─ Prop 8.30 restriction flat ⇐ Remark 7.55 chain + Lemma 8.31  wedhorn.txt:4095-4104, 3504-3517
 │   └─ inducing ⇐ Prop 6.18(2) "f : M→f(M) open" (Banach OMT)      wedhorn.txt:2456-2463 ("Proof. Missing")
 └─ GLUING  every rational cover OX-acyclic ⇒ sheaf
     ├─ Prop A.4   deg-0 exactness ⇒ sheaf                          wedhorn.txt:5332-5354
     ├─ Lemma 7.54 every cover refines to T-generated (T·A=A)       wedhorn.txt:4216-4217, 3490
     ├─ Prop A.3(2) refinement transfers acyclicity                 wedhorn.txt:5320
     └─ Lemma 8.34 T-generated cover acyclic                        wedhorn.txt:4222-4255
         ├─(i)  Laurent acyclic [Lemma 8.33 + Prop A.3(3) induction]    wedhorn.txt:4225-4234, 4151
         ├─(ii) T-gen ⇒ unit-gen Laurent [Cor 7.32 dominating unit]     wedhorn.txt:4235-4241, 3153
         ├─(iii) unit-gen ⇒ refines to Laurent                          wedhorn.txt:4242-4244
         └─(iv) Prop A.3(1) assembly                                    wedhorn.txt:4248-4255
```

## TREE vs CODE (lean_verify-confirmed; ★ = bare-sorry leaf)
```
isSheafy_of_stronglyNoetherian_828b  Wedhorn828:2424  [SORRY; faithful bundle, NO IsDomain/noethA₀]
├─ EMBEDDING = cor_8_32_productRestrictionSub_isEmbedding  Wedhorn828:2371  [SORRY-COMPOSITE]
│  ├─ cor_8_32_productRestrictionSub_isInducing            Wedhorn828:2365  ★E1  Prop 6.18(2)
│  └─ cor_8_32_productRestrictionSub_injective             Wedhorn828:2340  [SORRY — gated by E2, NOT proven]
│     └─ …faithfullyFlat → prop_8_30_restriction_flat → …flat_of_faithful_base → …relative_laurent_flat
│        ├─ faithfullyFlat_pi_of_maximal_ne_top      Cor832:155      [PROVEN ✓]
│        ├─ cor_8_32_maximal_liftedIdeal_ne_top      Wedhorn828:2273 [PROVEN ✓]
│        ├─ presheafValue_isTateRing_faithful        Wedhorn828:887  [PROVEN ✓]  Example 6.38
│        ├─ presheafValue_isNoetherianRing_faithful  Wedhorn828:1883 [PROVEN ✓]  Example 6.38 (multivariate surj landed)
│        └─ prop_8_30_remark755_chain                Wedhorn828:2156  ★E2  Remark 7.55  (sub-gap: laurent_cover_from_dominating_unit sorry)
└─ GLUING = lemma_8_34_gluing  Wedhorn828:2406  ★G0 (statement ≡ IsOXAcyclic.gluing) — NOT wired to assembly

ASSEMBLY (WedhornCechAcyclicity; complete but [IsDomain]+noethA₀, disconnected):
isSheafy_ofStronglyNoetherianTate_clean  WCA:3641  [IsDomain]+noethA₀
└─ every_rational_cover_is_OXAcyclic  WCA:3598  [IsDomain]+noethA₀
   ├─ exists_ideal_gen_refinement_covers_each_D  WCA:3425  [IsDomain]  (Lemma 7.54)
   │  ├─ exists_form_a_refinement  WCA:3345  ★G6 (⚠FALSE-for-proper-base, B2-logged) [IsDomain]
   │  │   └─ faithful twin exists_form_a_refinement_coversSpa WCA:3275 (NO IsDomain) → exists_finite_normalized_rational_refinement WCA:3241 (→ Spa-QC keystone)
   │  └─ ideal_gen_refinement_covers_each_piece  WCA:3390  ★G7  [IsDomain]
   ├─ IsOXAcyclic_of_refining_acyclic_cover  WCA:468  [PROVEN ✓ Prop A.3(2)]
   │  └─ restrictToPiece_acyclic_at_D  WCA:3558  ★G5 (recursive 8.34 over O_X(D) = base-change)  noethA₀
   └─ wedhorn_lemma_834  WCA:2687  [noethA₀, full Lemma 8.34]
      ├─ part_ii_unit_gen_via_dominating  WCA:1971
      │  ├─ cor_7_32_dominating_unit → exists_dominating_unit_noHArch_finset  Cor732:557  ★G2 (→ Spa-QC keystone)
      │  └─ unit_gen_restriction_of_dominating_laurent  WCA:1942  ★G3
      │     ├─ index_selection_on_laurent_piece  WCA:1886  ★G3a
      │     └─ canonical_unit_of_pointwise_lower_bound  WCA:1907  ★G3b
      ├─ part_i_laurent_acyclic → laurentProdCoverOf_isOXAcyclic → unitCover_isOXAcyclic  WCA:1595  ★G1  noethA₀
      │     (Lemma 8.33; sub-sorries WCA:587/605/674/816 = 5-lemma chase)  [MY SESSION: A.3(3) engine PROVEN above this]
      ├─ part_i_laurent_restriction_acyclic → laurent_restriction_isLaurent  WCA:1738  ★G4 (⚠DEFECTIVE statement)
      ├─ laurent_cover_refines_idealgen_cover  WCA:2631  ★G8 (live σ-walk)  noethA₀
      ├─ laurent_cover_covers_each_idealgen_piece  WCA:2660  ★G9 (live σ-walk)  noethA₀
      └─ wedhorn_lemma_834_propA3_part1_bridge  WCA:2589  [PROVEN ✓ Prop A.3(1)]

DEAD (parallel part-iii, NOT on assembled path): ratio_laurent_cover_of_units/_refines/_covers_each  WCA:2033/2076/2053
```
**PROVEN engines (lean_verify clean):** Prop A.3(1)/(2)/(3) [A.3(3) = my `isOXAcyclic_interProd`+`isOXAcyclic_congr`], Cor-8.32 maximals criterion, Example-6.38 noetherian/Tate facts, σ-compact-free Banach OMT `wedhorn_6_16_of_topNilpUnit`.

## LEAVES — source quote + match + discharge + adversarial attacks

### ★E1 `cor_8_32_productRestrictionSub_isInducing` (Wedhorn828:2365) — Banach-OMT inducing
- Source (Prop 6.18(2), wedhorn.txt:2459): *"Let f : M → N be an A-linear map of finitely generated modules … Then f is continuous and the map f : M → f(M) is open."* (Wedhorn 2463: *"Proof. Missing"* — content is BGR §3.7.2.)
- Match: inducing of `O_X(X)→∏O_X(Uᵢ)` = "open onto image". Discharge: **project-decl, engine EXISTS but UNWIRED** — `wedhorn_6_16_of_topNilpUnit` (WedhornBanachTheorem.lean:408, sorry-free, σ-compact-free, **IsDomain-free** — whole file `grep IsDomain = 0`). The faithful leaf `productRestrictionSub_isInducing_tate` (StructureSheaf:1382, NO domain hyp) and `cor_8_32_…isInducing` (Wedhorn828:2367) are bare sorries calling NOTHING.
- Attacks: (drift) PASS — Prop 6.18 / Thm 6.16 / Cor 8.32 / Rmk 8.29 are ALL domain-free (verified quotes 2026-06-05). (hyp) PASS — faithful bundle, no IsDomain. (discharge) ⚠ **VAPORWARE**: docstring (2361) cites `productRestrictionSubToEqualizer_isOpenMap` which **does not exist**. Real blocker per the docstring = the **noeth-A₀ → ring-noetherian retyping** of the OMT-adjacent infra (case-(b) gives ring-noeth, not noeth-A₀), THEN wire `wedhorn_6_16_of_topNilpUnit` + the "inducing ⇒ open-onto-image" reduction. (The plain `wedhorn_6_16` still carries load-bearing `[SigmaCompactSpace]` — must use `_of_topNilpUnit`.)

### ★E2 `prop_8_30_remark755_chain` (Wedhorn828:2156) — Remark 7.55 chain
- Source (Remark 7.55, wedhorn.txt:3504-3517): *"…by Corollary 7.32 a unit u … X₀ := {x; 1 ≤ x(s/u)} … Xᵢ := {x ∈ Xᵢ₋₁; x(tᵢ/s) ≤ 1} … Spa A ⊇ X₀ ⊇ X₁ ⊇ ··· ⊇ Xₙ = U."* Consumed at Prop 8.30 (wedhorn.txt:4100).
- Match: geometric chain reducing `U⊆V` to basic-Laurent steps so per-step flatness (Lemma 8.31) folds by `Module.Flat.trans`. Discharge: **project-decl, construction gap** (sub-gap: `laurent_cover_from_dominating_unit` sorry; inductive Xᵢ unbuilt).
- Attacks: (drift) PASS. (hyp) PASS. (discharge) PARTIAL — per-step engine OK, chain-builder unbuilt.

### ★G1 `unitCover_isOXAcyclic` (WCA:1595) — Lemma 8.33 (deepest leaf)
- Source (Lemma 8.33, wedhorn.txt:4151+): 2-cover `U₁={x(f)≤1},U₂={x(f)≥1}` Čech-exact; via `O_X(U₁)=Âhζi/(f−ζ)` (Example 6.38/6.39, 5-lemma chase 4160-4210).
- Match: `unitCover D₀ f = {R(f/1)∩D₀, R(1/f)∩D₀}` (s=1, base-independent FAITHFUL form). Discharge: **genuine-new-math, heaviest** (sub-sorries 587/605/674/816; restricted-power-series surjectivity risk).
- Attacks: (drift) PASS — matches 4152; docstring flags the *relativized* `wedhorn_lemma_833` as divergent. (hyp) ⚠ noethA₀ — Wedhorn = "strongly noeth Tate" only; strippable. (discharge) deep, 4 open sub-sorries.

### ★G2 `exists_dominating_unit_noHArch_finset` (Cor732:557) — Cor 7.32 [KEYSTONE]
- Source (Cor 7.32, wedhorn.txt:3153-3161 / 4239-4241): *"…there exists a unit s ∈ A× such that for all x ∈ X an i exists with x(s) < x(fᵢ)."* Discharge: **genuine-new-math** — bottoms at **hArch-free Spa quasi-compactness** (Wedhorn 7.35(2)). **Same Spa-QC keystone gates ★G6's faithful twin.**
- Attacks: PASS drift/hyp (IsLinearTopology already stripped, prior session); discharge = the shared Spa-QC-noHArch keystone.

### ★G3/G3a/G3b — part-(ii) σ-selection (WCA:1942/1886/1907)
- Source (wedhorn.txt:4235-4241): unit-generated restrictions of the `s⁻¹·T` Laurent cover. Discharge: **project-decl, light** (finite σ-walk + canonicalMap-unit). Attacks PASS.

### ★G4 `laurent_restriction_isLaurent` (WCA:1738) — ⚠ DEFECTIVE STATEMENT
- Source (wedhorn.txt:4232-4234): *"If U is any rational subset, then V|U is the Laurent cover generated by f₁|U,…,fr|U."* (computed equality.)
- Attack (well-statedness) **FAIL**: `V_restrict` abstract (only `base=U`+pieces-refine); conclusion FALSE for `V_restrict:={U}`. Must **bind `V_restrict := V.restrictToPiece U`** (call sites already do). Re-state before ticketing.

### ★G5 `restrictToPiece_acyclic_at_D` (WCA:3558) — recursive 8.34 over O_X(D) (base-change)
- Source: Prop A.3(2) hypothesis "U|Vj0…jq F-acyclic" (wedhorn.txt:5316) over base `O_X(D)`. Discharge: **genuine-new-math** (Lemma 8.34 over a general strongly-noeth Tate base; base-change). noethA₀.

### ★G6 `exists_form_a_refinement` (WCA:3345) — ⚠ FALSE-for-proper-base (B2-logged)
- Source (Lemma 7.54, wedhorn.txt:4216-4217): about coverings of **Spa A** (whole space).
- Attack (drift) **FAIL**: general-`C` node FALSE for proper base (WCA:3319-3329). Faithful = whole-space `exists_form_a_refinement_coversSpa` (3275, no IsDomain) + A.3(2) relativization. Kernel `exists_finite_normalized_rational_refinement` (3241) largely proven, bottoms at Spa-QC keystone (shared with G2).

### ★G7/G8/G9 — refinement combinatorics (WCA:3390/2631/2660)
- Source (wedhorn.txt:4251-4255): V-refines-C / covers-each feeding Prop A.3(1). Discharge: **project-decl, light** (finite σ-walk over ValuativeRel; noethA₀ is dead weight here).

## FAITHFULNESS DEFECTS (cleanup, distinct from the math leaves)
1. **`[IsDomain A]` (structure ring)** — gluing decls (WCA:3345/3363/3390/3425/3598/3641) + legacy embedding wrappers (StructureSheaf:1398/1414/1429). **REMOVABLE = "delete dead code", NOT "strip a live decoration"** (verified carefully 2026-06-05): (a) **Wedhorn 7.51/7.52/7.53 are domain-free** — read the proofs: `A/m` is a field because `m` is *maximal*, not because `A` is a domain; 7.54 = "[Hu3] 2.6" (wedhorn.txt:3457-3502); "integral domain" never appears near 7.32/7.51-7.54/8.33/8.34. (b) `exists_form_a_refinement` (3345) is a **bare sorry**, *false-for-proper-base* (B2-logged), being deprecated. (c) The **faithful twin** `exists_form_a_refinement_coversSpa` (3275) has **NO IsDomain + a real proof**; its kernel (3241) is domain-free (bottoms at Spa-QC + Cor 7.32). (d) The **live** Nullstellensatz/span steps (`span_top_of_distinguished_products`, `spanTop_iff_noCommonZero_spa`, `exists_mem_rationalOpen_of_spanTop`) ALL carry zero IsDomain. (e) `[IsDomain A]` is **never invoked** — the only real `IsDomain` *uses* are `A⧸p` (p prime) and `residueRing` (about quotients, not A); the legacy wrappers just delegate to domain-free `_tate` companions.
1b. **`IsDomain (presheafValue D₀)` (LOCALIZED ring — a SEPARATE hypothesis, do not conflate)** — explicit hyp `hDom_B` on **11** `EmbeddingTopo.lean` decls (504/582/648/800/898/984/1126/1225/1298/1409/1503). **ALSO REMOVABLE — a dead parallel prototype + a faithfulness DEFECT** (verified 2026-06-05): (a) all 11 are transitively `sorryAx` (bottom at LaurentRefinementCore:4794) and consumed ONLY by other `hDom_B` decls in the same file; (b) **import-isolated** from the faithful headline — Wedhorn828 does not import EmbeddingTopo, and StructureSheaf is *upstream* of EmbeddingTopo, so neither the headline nor the faithful inducing leaf (`productRestrictionSub_isInducing_tate`, bare sorry, calls nothing) can structurally reach them; (c) **Wedhorn-defect, not requirement** — Prop 6.18 / Thm 6.16 / Cor 8.32 / Thm 8.28 / Rmk 8.29 are ALL domain-free (verified quotes); the inducing of f.g. modules over a complete-noeth-Tate ring never uses a domain. The intended faithful inducing route (domain-free Banach-OMT `wedhorn_6_16_of_topNilpUnit`) introduces no such hypothesis.
2. **noeth-A₀** — ~10 gluing decls. Wedhorn-absent, **FALSE-for-ℂ_p**. **Strippable-in-principle but SUBSTANTIVE** (re-derive noetherianness from `IsStronglyNoetherian`; `presheafValue` already faithfully noetherian). Headline path is already noethA₀-free.
3. **Vaporware citation** — `productRestrictionSubToEqualizer_isOpenMap` (Wedhorn828:2361) does not exist.
4. **Stale docstrings** — Wedhorn828:1842/2232 call `example638_multivariate_surjection` "absent" though sorry-free.
5. **`banach_two_of_three`** (BanachOMT:443) bare sorry (B2-FALSE direction) — off the faithful path.

## CONNECTION GAP (gluing → headline)
`lemma_8_34_gluing` (Wedhorn828:2406-2413) ≡ `RationalCovering.IsOXAcyclic.gluing` (WCA:103-111) **character-for-character**. Bridge = NOT mathematical: (1) `import «Adic spaces».WedhornCechAcyclicity`; (2) **make `every_rational_cover_is_OXAcyclic` faithful** (strip [IsDomain]+noethA₀ — else won't typecheck in the headline's clean context); (3) `lemma_8_34_gluing C g h := (every_rational_cover_is_OXAcyclic C).gluing g h`.

## FEASIBILITY ASSESSMENT
The proof is **structurally complete on both halves** — every internal node composed; holes are leaves only (Prop A.3(1)(2)(3), the Cor-8.32 maximals criterion, Example-6.38 facts are genuinely PROVEN). This is a **leaf-discharge + faithfulness-cleanup** project, NOT a scaffold-gap one. Genuine remaining MATH:
- **(M1) hArch-free Spa quasi-compactness** (Wedhorn 7.35(2)) — KEYSTONE feeding BOTH Cor 7.32 (G2) and faithful 7.54 Step-1 (G6). Discharge once, two leaves unblock.
- **(M2) Lemma 8.33** (G1) — restricted-power-series 5-lemma chase; deepest leaf, real mathlib-infra risk.
- **(M3) Banach-OMT inducing wiring** (E1) — engine exists; needs "inducing ⇒ open-onto-image" reduction.
- **(M4) Remark 7.55 chain** (E2) + its `laurent_cover_from_dominating_unit` sub-sorry.
- **(M5) σ-walk + base-change** (G3/G5/G7/G8/G9) — finite/light, several leaves.

Cleanup: remove `[IsDomain A]` = delete the dead false-for-proper-base sorry chain + re-route through the domain-free twin (NOT stripping a live decoration — nothing uses it); delete/ignore the 11 `IsDomain (presheafValue)` `EmbeddingTopo` prototype decls (import-isolated, Wedhorn-defect); noeth-A₀ migration (substantive); re-state G4 + re-point G6; fix vaporware/stale docstrings; wire import.

**Verdict: feasible. No multi-week-mathlib-gap blocker EXCEPT (M2) Lemma 8.33's restricted-power-series chase (genuine risk) and (M3)'s open-onto-image reduction. The keystone (M1) unblocks the most.** Recommended order: faithfulness cleanup (strip IsDomain, fix G4/G6, wire import) → (M1) Spa-QC keystone → σ-walk leaves → (M3) Banach wiring → (M4) 7.55 chain → noeth-A₀ migration → (M2) Lemma 8.33.

## Source check / Lean↔source coverage
Leaves with verbatim source quote: 11/11 (E1,E2,G1–G9). Lean↔source match paragraph: 11/11. Prior-B2 log consulted: G6 (`exists_form_a_refinement`, false-for-proper-base, logged 2026-06-04) and G4 (`laurent_restriction_isLaurent`, abstract-V_restrict) are unaddressed prior-B2-shape matches — DO NOT ticket until re-stated. noeth-A₀ matches the systematic-defect log.

## Next step
Approve → run `/develop` (full) / `/develop --continue` to create tickets from the verified leaves. EXCLUDE the two DEFECTIVE-as-stated nodes (G4, G6) until re-stated; EXCLUDE dead `ratio_laurent_*`.
