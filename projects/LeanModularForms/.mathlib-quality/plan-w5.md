# Plan — W5: closing `heckeT_p_aggregate_peeled_diagonal_balance` (the T_p adjoint residual)

**Date:** 2026-05-27. **Branch:** hecke-ring. **Mode:** planning-only (READ-ONLY). No build run.

## Goal
Close the single live `sorry` in the AdjointTheory chain,
`heckeT_p_aggregate_peeled_diagonal_balance` (ConcreteFamily.lean:5391) = **W5**, the
`c_p/c_N + det-p^{k-2}` bilinear reconciliation. Closing it makes
`exists_simultaneous_eigenform_basis` axiom-clean (rest of the spectral chain is sorry-free).

## What W5 is (one line)
`⟨D⟩ f (g∣A) = ⟨D⟩ ((⟨p⟩f)∣A) g` over the fixed aggregate `D = ⋃_i β_i•Γ₁-FD`, `A = diag(p,1)`.
= DS Ex 5.4.4 un-normalized, for `Γ'=Γ_p(A) ⊂ Γ=Γ₁`, with the `det-p^{k-2}` center weight and
`c_p/c_N` fiber factors made explicit.

## BINDING VERDICT (see `decomposition-w5.md` §5)
**BOUNDED-BUT-SUBSTANTIAL, ~700–1100 LOC. NOT open (no hard analysis). NOT free glue.**
The brief's route (tile-FD identification + proven engine FDT:1612 + verified weight) is the
CORRECT architecture and DOES work — BUT the "tile-FD identification" (W5a) is itself the unbuilt
hard core: a finite, elementary congruence-coset completeness/index fact, NOT a citation.

## Strategy (the route that works — confirmed sound)
1. **W5a** (CRUX): prove `⋃_i γ_i•Γ₁-FD` is a FD for `Γ₁∩AΓ₁A⁻¹` ⟺ `D =ᵃᵉ Γ_p(A)-FD`.
   Equivalent: `{γ_i = T_p_lower_tile_family i} ⊂ Γ₁` are complete coset reps for
   `(Γ₁∩AΓ₁A⁻¹)\Γ₁`, with `[Γ₁:Γ_p(A)] = p+1`.
2. **W5b**: transfer `⟨D⟩ f (g∣A) → ∫_{Γ_p(A)-FD} pet f (g∣A)` via W5a + `setIntegral_eq`.
3. **W5c**: fire the PROVEN trace engine FDT:1612 →
   `c_p•∫_{Γ_p(A)-FD} = c_N•∫_{Γ₁-FD} pet f (tr(g∣A))`; cancel `c_p/c_N` (ℂ-scalars).
4. **W5d**: `tr(g∣A) = T_p g` (the trace leaf, `decomposition-tracehecke.md`) + the `p^{k-2}`/⟨p⟩
   weight (PROVEN-from-project: DeltaB:456/483, Nebentypus:794, SA:273; diamond shuffle already
   in CF:5489 downstream); re-fold to `petN((⟨p⟩f)…, T_p g)`. Both balance slots symmetric.

## Crux & sharing
- **W5a is THE crux.** It is the SAME object as the trace-leaf L2 (`decomposition-tracehecke.md`)
  and counts ONCE: coset reps for `Γ_p(A)` in `Γ₁`, index p+1.
- Already PROVEN halves of W5a: DISJOINT (`aedisjoint_pairwise_T_p_family`, SA:1431),
  DISTINCTNESS (`adj_upper_inv_mul_upper_not_mem_Gamma1` HeckeT_p_Gamma1:348,
  `adj_M_infty_inv_mul_upper_not_mem_Gamma1` :378). UNBUILT: COVERS/surjectivity + INDEX=p+1.

## Already-proven vs new
| Piece | Status |
|---|---|
| Trace engine FDT:1612 (W5c core) | **PROVEN, unwired** |
| `peterssonInner_slash_adjoint` CoV (AdjointTheory:770) | PROVEN |
| FD-image `smul_Gamma_p_α_…_ae_isFundamentalDomain` (FDT:879) | PROVEN |
| `slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152) — W5c hG hyp | PROVEN |
| `A•D = ⋃γ_i•Γ₁-FD` (DeltaB:700) — W5a geometry | PROVEN |
| AE-disjoint p+1 tiles (SA:1431) — W5a disjoint half | PROVEN |
| distinctness (HeckeT_p_Gamma1:348/378) — W5a half | PROVEN |
| weight `g∣(A·β_i)=p^{k-2}g` (DeltaB:456/483 + Nebentypus:794) — W5d | PROVEN |
| `peterssonAdj(A)=T_p_upper(0)` (SA:273) — W5d α↦α' | PROVEN |
| diamond ⟨p⟩↔⟨p⟩⁻¹ shuffle (CF:5489) — W5d | PROVEN |
| `aggregate_HeckeFD_measure_hyps` (CF:5233) — integrability pattern | PROVEN |
| **W5a COVERS + index p+1** | **NEW (~150–300 LOC)** |
| **W5b integral transfer** | **NEW (~80–150 LOC, glue)** |
| **W5c engine wiring + c_p/c_N** | **NEW (~120–200 LOC, engine cited)** |
| **trace leaf `traceSlash_…_eq_heckeT_p`** | **NEW (~350–630 LOC, see tracehecke; crux shared w/ W5a)** |
| **W5d weight reconciliation** | **NEW (~60–120 LOC)** |

## Risks
- **W5a surjectivity** is the one real unknown: proving `{γ_i}` cover all of `(Γ₁∩AΓ₁A⁻¹)\Γ₁`.
  Finite, elementary (matrix entries mod N / mod p), but no mathlib lemma for diag(p,1)-conjugate
  index. Mitigation: derive index p+1 AS `Fintype.card_option` of the explicit complete-reps
  bijection (don't prove index independently).
- The v2-plan "relIndex cancels over proven engines" shortcut is FALSE (omits W5a/multiplicity).
  Do NOT route through per-i `Γ_p(α_i)` hoping the index cancels — that relocates W5a, not removes.
- `match`/`Finset.sum_option`/`Set.iUnion_option` expansion + heartbeat hygiene in wiring
  (no `set_option maxHeartbeats` — forbidden).

## Out of scope / do not touch
`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_axiom_clean`,
`miyake_4_6_14_*`. No downstream-file edits; discharge lives in ConcreteFamily / FDTransport.

## Source confirmation
DS Ex 5.4.4 (p.183) ↔ trace engine FDT:1606–1631 (un-normalized form, verbatim). Miyake Thm 2.8.2
/ 4.5.6 ↔ the `α↦α'`, p+1 reps (see `decomposition-tracehecke.md` §1). Learnings `ca13d40b`,
`00f97f28`: W5 ≡ symmetric form (logical equivalence), engine reachable not dead, family-trace
bookkeeping unbuilt (~400–800 → refined to ~700–1100 here once transfer+integrability counted).
