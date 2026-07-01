# Plan (v4) — `petN_heckeT_p_symmetric_form_doubleCoset` via the TRACE route

**Supersedes plan-adjoint-v3.md** (which carried the OPEN verdict). The FD-image /
per-rep-CoV / index-reconciliation machinery v3 called "unbuilt, multi-week" is now PROVEN
in FDTransport.lean (0 sorries). Verdict: **BOUNDED.** See decomposition-adjoint.md for the
full red-team analysis, verbatim sources, and Lean citations.

## Goal (ConcreteFamily.lean:5212, sole real `sorry` @5218)
`petN(T_p f, g) = petN(⟨p⟩ f, T_p g)` (DS 5.5.2(b)/5.5.3, Miyake 2.8.2(2)/4.5.4(2),
`α=diag(1,p)`, Γ₁(N)). `T*_p = ⟨p⟩⁻¹ T_p`.

## Strategy — prove the consolidated lemma HEAD-ON (drop the circular aggregate route)
v3's "smoking gun" only shows the GLOBAL-AGGREGATE framing is circular (post-(leaf1,
aggregate) residual == leaf2). The aggregate (CF:122) is DS Def 5.1.3 (LHS expansion), not
DS 5.5.2(b); abandon it. Instead mirror **Miyake 2.8.2(2)** directly:
1. `T_p f = Σ_i f∣β_i` (β_i ∈ {M_∞}⊔{T_p_upper b}, det β_i = p) — `heckeT_p_fun_eq_coset_sum`.
2. Pull the sum through `petN` (linearity) — proven API.
3. Per `i`, apply per-rep CoV (Miyake 2.8.2(1)) over `Γ_p(α_i)-FD` — `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235).
4. Transfer each `Γ_p(α_i)-FD` integral to `Γ₁-FD` with the global trace — `setIntegral_..._eq_traceSlash_Gamma1_fundDomain` (FDT:1612, DS Ex 5.4.4).
5. Re-fold the family of traces into `T_p(⟨p⟩⁻¹g)` and recombine via the proven diamond
   bookkeeping (`diamondOp_petersson_unitary` SA:93, `heckeT_p_comm_diamondOp` HeckeT_p:1013).

## Banked, PROVEN (cite, do not re-derive)
- `peterssonInner_slash_adjoint` (AdjT:770) — CoV `z↦α•z`, any D, det>0.
- `smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDT:879) — `α•(Γ_p(α)-FD)` is FD for `Γ₁∩αΓ₁α⁻¹`.
- `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235) — per-rep CoV over `Γ_p(α)-FD`.
- `traceSlash_Gamma_p_α` def (FDT:1332); `_indep` (1449); `_slash_Gamma1` (1522).
- `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain` (FDT:1612) — `c_p•∫_{Γ_p-FD} = c_N•∫_{Γ₁-FD}(tr)`.
- `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291) — β_i•Γ_p(α_i)-FD tiling.
- `slash_peterssonAdj_glMap_{M_infty,T_p_upper}_eq_slash_T_p_lower` (SA:1925/1934) — `g∣adj β_i = g∣T_p_lower`.
- `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (PLN:1069); `petN_slash_invariant` (PLN:923).
- `diamondOp_petersson_unitary` (SA:93); `heckeT_p_comm_diamondOp` (HeckeT_p:1013).
- Measure-hyp engine: `aggregate_HeckeFD_measure_hyps` (CF:5463), `integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure`.

## The three NEW leaves (full skeletons in decomposition §5)
- **C2** (~40 LOC, API-GAP-BOUNDED): `g∣adj β_i` is `Γ_p(α_i)`-slash-invariant
  (so 1612's `hG_slash` is met). Discharge: `Gamma_p_α_conj_mem_Gamma1` (FDT:68) +
  `SlashInvariantFormClass.slash_action_eq`.
- **C1** (~60 LOC + meas, BOUNDED): route leaf-1's `c_N•∫_{Γ₁-FD} pet(f∣β_i) g` into the
  `Γ_p(α_i)-FD` shape 1235 consumes; index reconciliation IS 1612. Order pinned:
  **CoV (1235) FIRST**, then trace (1612) — because `f∣β_i` is not Γ₁-invariant, 1612 cannot
  be applied with `F = f∣β_i`.
- **D** (~120–200 LOC, the GENUINE API-GAP): `Σ_i tr_i(g∣adj β_i) = T_p(⟨p⟩⁻¹g)` (form-level,
  DS family-trace = adjoint double coset). Safest attack: integrated `petN`-form, reusing
  `petN_heckeT_p_adjoint_unsymm`-shape (CF:5333, PROVEN-equivalent to goal) + diamond unitarity.

## Risks / pins
- Sequencing: CoV-before-trace is mandatory (C1 attack-iii FAILS otherwise).
- LEAF D is the only step with no proven analogue; its 3 attacks are all FINITE
  (coset combinatorics / linearity / diamond algebra) — no analysis. Spectral fallback
  (attack iii) routes through already-proven diamond lemmas (`diamondOp_petersson_unitary`,
  `heckeT_p_comm_diamondOp`), so D cannot be circular (it carries no `f`, no integral).
- det^{k-1} (Miyake prefactor) absorbed by `peterssonAdj` def + `c_p`/`c_N`; cross-checked
  against SA:317 (`peterssonAdj M_∞ = T_p_upper(0)σ_p⁻¹`, no loose det).

## Correction to the prompt's framing
`Gamma1QuotEquivOfGamma0` (PLN:823) is NOT the Miyake-4.5.3(2) common-reps bijection; it is
the diamond reindex `[δ]↦[δγ⁻¹]` of `SL/Γ₁` (used in `petN_slash_invariant`). The 4.5.3(2)
common-reps role is carried by `heckeT_p_fun_eq_coset_sum` (explicit `Option (Fin p)` family
on BOTH sides) + the `Γ_p(α_i)` apparatus. σ enters only in LEAF D as the `⟨p⟩` twist.

## Total: ~250–400 LOC, finite glue, NO new measure-theoretic/FD development. BOUNDED.
