# Tickets (v4) — `petN_heckeT_p_symmetric_form_doubleCoset`: verdict BOUNDED

**Supersedes tickets-adjoint-v3.md** (OPEN, "no BUILD tickets" — STALE: the trace machinery
v3 declared unbuilt is now PROVEN in FDTransport.lean). See decomposition-adjoint.md (v4).

Verdict: **BOUNDED via the trace route.** The work is ~250–400 LOC of finite glue. Below are
the BUILD tickets, in dependency order. All cited support lemmas are PROVEN (grep-verified).

---

## T-A1 — petN linearity expansion (LEAF A + B)
**Statement:** `petN(T_p f, g) = Σ_i petN(f∣β_i, g)` over `i : Option (Fin p)`,
β_i = `α_T_p_GLPos p hp hpN i`.
**Discharge:** `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307, already used CF:5445) +
`peterssonInner` additivity in slot-1 (`map_sum`; cf. DeltaBSystem:1613). ~15 LOC.
**Risk:** none. DISCHARGED-project pattern.

## T-C2 — `g∣adj β_i` is `Γ_p(α_i)`-slash-invariant (LEAF C2)  [API-GAP, BOUNDED]
**Statement:** `g_slash_adj_beta_Gamma_p_alpha_inv_slash_invariant` (skeleton in decomp §5):
`∀ γ ∈ Gamma_p_α α_i, (g∣adj β_i)∣γ = g∣adj β_i`.
**Discharge:** `Gamma_p_α_conj_mem_Gamma1` (FDT:68) → conj δ∈Γ₁; then
`SlashInvariantFormClass.slash_action_eq g` (pattern at SA:1917–1922). ~40 LOC.
**Attacks:** (i) direct conj; (ii) reuse SA:1917–1922 pattern; (iii) via `adj β_i = β_i'·Γ₁-factor`.
**Risk:** LOW. Needed as `hG_slash` for T-C-trace.

## T-C1 — per-rep routing to `Γ_p(α_i)-FD` (LEAF C1)  [BOUNDED]
**Statement:** turn `c_N•∫_{Γ₁-FD} pet(f∣β_i) g` into `peterssonInner k (Γ_p(α_i)-FD) (f∣β_i) g`
form (the domain 1235 consumes), via `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291)
+ `setIntegral_Gamma1_smul_eq` (PLN) + the measure-hyp engine.
**Discharge:** CF:291 (PROVEN) gives the β_i•Γ_p(α_i)-FD tiling; index reconciliation IS T-C-trace.
~60 LOC + measure hyps (T-MEAS).
**Pin:** CoV (1235) must come AFTER landing on `Γ_p(α_i)-FD`; do NOT apply 1612 with `F=f∣β_i`
(not Γ₁-inv — attack iii in decomp §5 FAILS).
**Risk:** MEDIUM (sequencing + measure hyps).

## T-C-CoV — per-rep adjoint exchange (LEAF C-CoV)  [DISCHARGED-project, cite]
**Statement:** `⟪Γ_p(α_i)-FD⟫ (f∣β_i) g = ⟪α_i•Γ_p(α_i)-FD⟫ f (g∣adj β_i)`.
**Discharge:** `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235) verbatim, det β_i = p > 0.
0 LOC (cite). **Risk:** none.

## T-C-trace — `Γ_p(α_i)-FD ↔ Γ₁-FD` transfer (LEAF C-trace)  [DISCHARGED-project, cite]
**Statement:** `c_p,i•∫_{Γ_p(α_i)-FD} pet f (g∣adj β_i) = c_N•∫_{Γ₁-FD} pet f (tr_i(g∣adj β_i))`.
**Discharge:** `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`
(FDT:1612), fed `hF_slash` (f Γ₁-inv, trivial), `hG_slash` (= T-C2), measure hyps (T-MEAS).
0 LOC of new math; ~20 LOC wiring. **Risk:** LOW.

## T-D — family-trace bookkeeping (LEAF D)  [API-GAP, BOUNDED — the genuine residue]
**Statement:** `heckeT_p_g_traceSlash_family_identity` (skeleton in decomp §5):
`Σ_i tr_i(g∣adj β_i) = T_p(⟨p⟩⁻¹g)` (form-level), OR its integrated `petN`-form.
**Discharge attacks (all FINITE — coset combinatorics / linearity / diamond algebra):**
- (i) DIRECT: expand `traceSlash` def (FDT:1332); SA:1925/1934 makes the slash uniform
  (`g∣adj β_i = g∣T_p_lower`); `Finset.sum_bij'` matching `⊔_i Γ₁/Γ_p(α_i)` to the
  `T_p_upper`-family (concrete det-p coset reps from `heckeT_p_fun_eq_coset_sum`).
- (ii) σ-TWIST: use `Gamma1QuotEquivOfGamma0` (PLN:823) for the `⟨p⟩` reindex, compose with
  `heckeT_p_comm_diamondOp` (HeckeT_p:1013).
- (iii) INTEGRATED FALLBACK (SAFEST): prove the `petN`-level form
  `Σ_i c_N•∫_{Γ₁-FD} pet f (tr_i(g∣adj β_i)) = petN(f, T_p(⟨p⟩⁻¹g))`, matching against the
  PROVEN-equivalent `petN_heckeT_p_adjoint_unsymm` shape (CF:5333) via
  `diamondOp_petersson_unitary` (SA:93) + `petN_slash_invariant` (PLN:923).
~120–200 LOC. **Risk:** MEDIUM-HIGH (largest piece), but NOT analysis and NOT circular
(D carries no `f`, no integral; cannot ⟺ the bilinear goal — see decomp §8).

## T-MEAS — measure/integrability hypotheses  [DISCHARGED-pattern]
**Statement:** the per-`i` `NullMeasurableSet` / `IntegrableOn` hyps for T-C1/T-C-trace.
**Discharge:** reuse `aggregate_HeckeFD_measure_hyps` (CF:5463, PROVEN) +
`integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure`. ~50 LOC.
**Risk:** LOW (engine exists).

## T-ASSEMBLE — close `petN_heckeT_p_symmetric_form_doubleCoset` (replace 5218 sorry)
**Statement:** chain T-A1 → (per i: T-C1 → T-C-CoV → T-C2 → T-C-trace) → sum → T-D →
`petN_eq_setIntegral_Gamma1_fundDomain_PSL` back + diamond recombination.
**Discharge:** the §4 assembly in decomposition-adjoint.md. ~40 LOC.
**Risk:** integration risk only; each leaf independently bounded.

---

## Dependency graph
T-C-CoV, T-C-trace, T-A1, T-MEAS, T-C2 (leaves) → T-C1 → T-D → T-ASSEMBLE.
Critical path: T-C2 → T-C-trace → T-D → T-ASSEMBLE.

## Bottom line
**BOUNDED.** Two true API-GAPs (T-C2 ~40 LOC, T-D ~120–200 LOC) + routing/measure glue;
everything else cites PROVEN lemmas. NO multi-week analytic development remains. The trace
route SUPERSEDES the false per-tile `h_tile_shift_to_prefactored` (decomp §6).
