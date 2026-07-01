# Tickets — `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p`

Branch hecke-ring. Build GREEN. Workers run via /beastmode. Full analysis +
type-check-deferred skeletons in `decomposition-tracehecke.md`. Verdict: leaf BOUNDED
(~350–630 LOC, crux = L2); full residual closure needs W5 which is OPEN.

Target file for new lemmas: `LeanModularForms/HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean`
(or a new sibling `FamilyTrace.lean` imported there) — they sit just below `traceSlash_Gamma_p_α`
(FDTransport:1332) usage. NEVER touch `heckeT_p_aggregate_peeled_diagonal_balance` (CF:5391, the
residual sorry) or any protected statement until the leaf + W-chain are ready to replace it.

---

## TICKET T1 — L2 (THE CRUX): coset↔Hecke-rep bijection  [API-GAP, BOUNDED ~150–300 LOC]
**Statement:** `fiber_T_p_lower_equiv_HeckeReps` + `slash_A_delta_eq_slash_Hecke_rep`
(skeletons in decomposition §7). Build `{q : SL/Γ_p(A) // slGamma_p_αToGamma1 A q = q₀} ≃
Option(Fin p)`, and prove `f∣(A·δ_q) = f∣β_{i(q)}`.
**Discharge inputs (PROVEN, cite):** `T_p_lower_tile_family` (DeltaB:687) and its Γ₁-membership
(`M_infty_Gamma1_factor_mem_Gamma1` SA:1308, `shiftSL_loc_mem_Gamma1` SA:344); SMUL geometry
`T_p_lower_mul_T_p_upper_smul_eq_shift_smul` (DeltaB:456), `T_p_lower_mul_M_infty_smul_eq_…`
(DeltaB:483); matrix bridge `mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower`
(DeltaB:794); distinctness `adj_upper_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:348),
`adj_M_infty_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:378); `.out`↔`γ_i` absorption
`slash_α_Gamma_p_α_invariant` (FDT:134); `slash_Gamma1_eq f` (used FDT:162).
**NEW work:** the `.out`-rep-vs-`γ_i` bridge + surjectivity (completeness of the p+1 enumeration).
**Attacks (≥3, decomposition §5):** (i) forward matrix-enumeration `i↦mk(γ_i⁻¹)`; (ii)
injectivity-via-distinctness then count; (iii) bypass via SET identity (serves W2, not the form
leaf). Recommended: (i)+(ii) combined.
**DoD:** both lemmas compile, axiom-clean (no `sorry`/`native_decide`/`maxHeartbeats`).

## TICKET T2 — L1 fiber card = p+1  [collapses into T1, ~10 LOC]
**Statement:** `slGamma_p_αToGamma1_fiberCard (T_p_lower p hp.pos) = p + 1`.
**Discharge:** `Fintype.card` of T1's codomain `Option (Fin p)` (`Fintype.card_option`,
`Fintype.card_fin`); `slGamma_p_αToGamma1_fiberCard_eq` (FDT:1090) to move to the q₀ fiber.
**DoD:** compiles; do NOT prove the index independently (route through T1).

## TICKET T3 — L0/L3/L4 + assemble the LEAF  [DISCHARGED-once-T1, ~80 LOC]
**Statement:** `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p` (the leaf, skeleton §7).
**Route:** L0 (`SlashAction.slash_mul`) → unfold `traceSlash_Gamma_p_α` (FDT:1332) →
`Finset.sum_bij'` along `fiber_T_p_lower_equiv_HeckeReps` (T1) using `slash_A_delta_eq_slash_Hecke_rep`
→ `Σ_i f∣β_i` → `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307), reshaped EXACTLY as
`petN_heckeT_p_LHS_eq_aggregate` (CF:5207–5223, copy the `Fintype.sum_option` + `add_comm` pattern).
**DoD:** the leaf compiles axiom-clean. **This is the achievable milestone** — at this point the
combinatorial half of the residual is fully discharged behind a clean named lemma.

## TICKET T4 — W2 the FD set identity  [API-GAP, BOUNDED ~80–150 LOC]
**Statement:** `aggregate_D_ae_eq_T_p_lower_smul_Gamma_p_α_fundDomain` (skeleton §7):
`⋃_i β_i•Γ₁-FD =ᵐ[μ_hyp] A•Γ_p(A)-FD`.
**Discharge:** `A•D = ⋃γ_i•Γ₁-FD` (`T_p_lower_smul_Hecke_FD_eq_iUnion_tile` DeltaB:700);
`A•Γ_p(A)-FD = ⋃(A·q.out⁻¹)•Γ₁-FD` (`Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted_eq_smul`
FDT:366 / CF:285); both FDs for `Γ₁∩AΓ₁A⁻¹` (`smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain`
FDT:879) ⟹ `IsFundamentalDomain.ae_eq`-style uniqueness. Measure facts reuse
`aggregate_HeckeFD_measure_hyps` (CF:5233) and `aedisjoint_pairwise_T_p_family` (SA:1431).
**CAUTION:** still routes through the T1/T2 counts for tile matching. Depends on T1/T2.
**DoD:** compiles; serves the INTEGRATED route only.

## TICKET T5 (OPEN — DO NOT promise a bound) — W5 the index/det reconciliation
**Goal:** produce the BILINEAR both-slot peeled-diagonal balance from the integrated leaf+engine,
i.e. close `heckeT_p_aggregate_peeled_diagonal_balance` (CF:5391). Needs the c_p =
`slToPslQuot_fiberCard_Gamma_p_α A` vs c_N = `slToPslQuot_fiberCard N` reconciliation AND the
det-`p^{k-2}` weight bookkeeping across `∫_{Γ_p(A)-FD}` ↔ `∫_{Γ₁-FD}` (per-rep CoV FDT:1235 moves
ONE slot; the other slot's weight must be reconciled). **This is the genuinely-open analytic
half** (residual docstring CF:5337–5371; learning `ca13d40b`). **Run `/develop --decompose` on W5
SEPARATELY before committing effort** — it is NOT covered by the leaf and is the true remaining
mathematics. Do NOT assume T1–T4 close the residual.

---

## Sequencing
T1 → T2 (free) → T3 (LEAF DONE, combinatorial half discharged). Then T4 (W2). Then re-decompose
T5 (W5, OPEN) on its own. Land T1–T3 first as a self-contained, verifiable win even if T5 stalls.

## Guardrails
- No `set_option maxHeartbeats`, no `native_decide`, no custom `axiom`, no `sorry` in landed code.
- One tactic per line in proof bodies; pack hypothesis lists to ~100 chars; `fun x ↦` style.
- After every change: `lake build` GREEN before moving on.
- Protected (never edit): `heckeT_p_aggregate_peeled_diagonal_balance` (until replaced),
  `heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_axiom_clean`,
  `miyake_4_6_14_*`.
