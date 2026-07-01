# Tickets — W5 (`heckeT_p_aggregate_peeled_diagonal_balance`, the T_p adjoint residual)

**Date:** 2026-05-27. **Branch:** hecke-ring. Planning-only. Verdict: **BOUNDED ~700–1100 LOC,
crux = W5a (finite combinatorics, NOT analysis).** Execute via `/beastmode`. No protected edits.
File: `LeanModularForms/HeckeRIngs/GL2/AdjointTheory/{ConcreteFamily,FDTransport,DeltaBSystem}.lean`.

Order is dependency-forced: W5a-1 → W5a-2 → (W5b ‖ trace-leaf) → W5c → W5d → W5-top.

---

## Ticket W5a-1 — `[Γ₁ : Γ_p(T_p_lower)] = p+1` via explicit complete coset reps  ⚠ CRUX
**Goal.** Prove `{γ_i = T_p_lower_tile_family N p hpN i : i ∈ Option(Fin p)} ⊂ Γ₁` is a complete,
irredundant set of coset reps for `(Γ₁ ∩ A Γ₁ A⁻¹)\Γ₁` (A = glMap T_p_lower), hence
`Fintype.card ((Γ₁∩AΓ₁A⁻¹)\Γ₁) = p+1` (equivalently `slGamma_p_αToGamma1_fiberCard (T_p_lower) =
p+1` after A-conjugation).
**Reuse (PROVEN).** distinctness `adj_upper_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:348),
`adj_M_infty_inv_mul_upper_not_mem_Gamma1` (:378); geometry DeltaB:456/483/700; conj
`Gamma_p_α_conjBy_spec` (FDT:98).
**New.** SURJECTIVITY (covers): every `γ ∈ Γ₁` is `(Γ₁∩AΓ₁A⁻¹)·γ_i` for some i. Then
`Fintype.card_option + Fintype.card_fin`. Elementary `Fin 2`/`ZMod` arithmetic mod N, mod p.
**Est.** ~120–250 LOC. **Risk.** Surjectivity — the one genuine unknown; finite, no mathlib
diag-conjugate-index lemma. Do NOT prove index independently — get it from the bijection card.

## Ticket W5a-2 — `D =ᵃᵉ Γ_p(A)-FD` (the tile-FD identification)
**Goal.** `(⋃_i β_i•Γ₁-FD) =ᵐ[μ_hyp] Gamma_p_α_fundDomain_PSL (T_p_lower)`, AND
`IsFundamentalDomain (Γ₁∩AΓ₁A⁻¹) (⋃_i γ_i•Γ₁-FD)`.
**Reuse.** `T_p_lower_smul_Hecke_FD_eq_iUnion_tile` (DeltaB:700, `A•D=⋃γ_i•Γ₁-FD`);
`smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDT:879, `A•Γ_p(A)-FD` is FD);
`aedisjoint_pairwise_T_p_family` (SA:1431, disjoint half); `IsFundamentalDomain.ae_eq`/
`.eq_of_…` (mathlib, two FDs for same group ⟹ ae-equal); W5a-1 (covers/index).
**New.** Assemble FD from disjoint(SA:1431) + covers(W5a-1); then ae_eq via FD-uniqueness; then
apply A⁻¹ to descend `A•D=ᵃᵉA•Γ_p(A)-FD` to `D=ᵃᵉΓ_p(A)-FD`.
**Est.** ~80–120 LOC. **Dep.** W5a-1.

## Ticket W5b — integral transfer `⟨D⟩ f (g∣A) = ∫_{Γ_p(A)-FD} pet f (g∣A)`
**Goal.** Both balance ends: `peterssonInner k D F G = ∫_{Γ_p(A)-FD} petersson k F G` for the two
(F,G) pairs `(f, g∣A)` and `((⟨p⟩f)∣A, g)`.
**Reuse.** W5a-2 + `setIntegral_congr_set_ae` (mathlib) OR `IsFundamentalDomain.setIntegral_eq`
(needs integrand Γ_p(A)-invariance: `slash_α_Gamma_p_α_invariant_cuspForm` FDT:152 for `g∣A`);
`peterssonInner` def (PLN:203); integrability `aggregate_HeckeFD_measure_hyps` (CF:5233).
**Est.** ~80–150 LOC. **Dep.** W5a-2.

## Ticket trace-leaf — `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p`  (crux SHARED with W5a)
**Goal.** `tr_{q₀}(f∣A) = ⇑(heckeT_p_cusp k p hp hpN f)`. **Full sub-decomposition L0–L4 in
`decomposition-tracehecke.md` §4/§7.** Crux L2 (coset↔Hecke-rep bijection) ≡ W5a-1 object.
**Reuse.** `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307); `slash_α_Gamma_p_α_invariant`
(FDT:134); `SlashAction.slash_mul`; `Finset.sum_bij'` (mathlib); W5a-1 (the bijection/card).
**Est.** ~350–630 LOC (L2 ~150–300 shared with W5a-1 — net new ~100–330 once W5a-1 lands).
**Dep.** W5a-1 (shares the coset bijection).

## Ticket W5c — fire the PROVEN trace engine FDT:1612 + `c_p/c_N` cancellation
**Goal.** `c_p • ∫_{Γ_p(A)-FD} pet f (g∣A) = c_N • ∫_{Γ₁-FD} pet f (tr_{q₀}(g∣A))`, then cancel
`c_p, c_N` (uniform ℕ → invertible ℂ scalars) across both balance ends.
**Reuse (engine PROVEN).** `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`
(FDT:1612); hF=`slash_Gamma1_eq f`; hG=`slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152);
integrability: `integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical` (FDT:972) + trace/per-q
integrability (DeltaB:1666-pattern); fiber-card uniformity (FDT fiber_card_uniform).
**New.** Supply the 3 integrability hyps for THIS (F,G); the `c_p/c_N` `nsmul`/`smul_right_injective`
algebra.
**Est.** ~120–200 LOC. **Dep.** W5b.

## Ticket W5d — weight reconciliation + assemble `tr(g∣A)=T_p g`
**Goal.** Substitute trace-leaf (`tr(g∣A)=T_p g`); re-fold `c_N•∫_{Γ₁-FD} pet f (T_p g) =
petN(f, T_p g)`; apply the `det-p^{k-2}` / ⟨p⟩ weight to land both ends on `petN((⟨p⟩f)…, T_p g)`.
**Reuse (PROVEN).** trace-leaf ticket; weight `slash_diag_scalar` (Nebentypus:794, `f∣(cI)=c^{k-2}f`),
`A·T_p_upper(b)=pI·γ` (DeltaB:456), `A·M_∞=pI·γ'` (DeltaB:483); `peterssonAdj_glMap_T_p_lower_…`
(SA:273); diamond shuffle `petN_heckeT_p_diamond_shift_core` (CF:5489),
`diamondOp_petersson_unitary` (used CF:5508); `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (PLN).
**Est.** ~60–120 LOC. **Dep.** W5c + trace-leaf.

## Ticket W5-top — discharge `heckeT_p_aggregate_peeled_diagonal_balance` (CF:5391)
**Goal.** Replace the `sorry` (CF:5391): assemble W5b → W5c → W5d on both symmetric slots; the two
`peterssonInner k D` ends carry identical `c_N` factors and cancel.
**Reuse.** All W5b–W5d. Then `petN_heckeT_p_symmetric_form_doubleCoset` (CF:5400) and the whole
downstream chain (`…_global`, `heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`) become
sorry-free / axiom-clean automatically.
**Est.** ~40–80 LOC wiring (`match`/`Finset.sum_option`/`Set.iUnion_option` hygiene; no
`maxHeartbeats`). **Dep.** W5b, W5c, W5d.

---

## Dependency graph
```
W5a-1 ──┬─► W5a-2 ──► W5b ──┐
        └─► trace-leaf ─────┼─► W5c ──► W5d ──► W5-top
                            │
        (W5c also needs W5b)┘   (W5d needs W5c + trace-leaf)
```

## Totals
- New, de-duplicated (W5a-1 ≡ trace-leaf L2 counted once): **~700–1100 LOC.**
- Crux: **W5a-1 surjectivity** (the only genuine unknown; finite/elementary).
- Confirms learning `ca13d40b` (400–800, NOT bounded glue) — refined UP once transfer +
  integrability are counted. Refutes v2-plan "relIndex cancels over proven engines" (omits W5a).
- Proven-and-reused: trace engine FDT:1612, CoV 770, FD-image 879, weight (DeltaB:456/483 +
  Nebentypus:794 + SA:273), diamond shuffle CF:5489, disjoint SA:1431, distinctness :348/378.
