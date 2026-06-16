# Plan — `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p` (the T_p-spectral residue leaf)

**Date:** 2026-05-27. **Branch:** hecke-ring. Planning-only; see
`decomposition-tracehecke.md` for the full adversarial analysis and verbatim Miyake checks.

## Goal & context
The entire `T_p` self-adjointness / simultaneous-eigenbasis chain bottoms out at ONE
executable `sorry`: `heckeT_p_aggregate_peeled_diagonal_balance` (ConcreteFamily.lean:5391),
the peeled-diagonal balance `⟨D⟩ f (g∣A) = ⟨D⟩ ((⟨p⟩f)∣A) g` over `D = ⋃_i β_i•Γ₁-FD`,
`A = T_p_lower = diag(p,1)`, `β_i ∈ {M_∞}⊔{T_p_upper(b)}`.

The proposed reframing introduces a **form-level** leaf
`traceSlash_Gamma_p_α A (f∣A) q₀ = T_p f` (the `Γ_p(A)\Γ₁` family-trace = Hecke identity), the
Lean realization of Miyake 2.8.2(2)'s "`(f|ΓαΓ,g)=…Σ_v(f|ₖαᵥ,g)`" read fiberwise via the
common-reps `ΓαΓ=⊔Γαᵥ=⊔αᵥΓ` (Lemma 2.7.7 / 4.5.6(1): p+1 reps).

## Binding verdict (see decomposition §6)
**MIXED.** The **leaf is BOUNDED (~350–630 LOC)**; its crux is the explicit coset↔Hecke-rep
bijection **L2** (finite, elementary congruence-coset combinatorics; L1 ⊂ L2). **BUT the leaf
does NOT by itself close the residual `sorry`**: the integrated wiring needs **W2** (`D =ₐₑ
A•Γ_p(A)-FD`, bounded ~80–150 but re-uses L1/L2) and **W5** (the c_p/c_N + det-`p^{k-2}` bilinear
reconciliation), and **W5 is OPEN** — it is exactly the content the residual docstring
(CF:5337–5371) and learning `ca13d40b` (2026-05-27) flag as genuine multi-lemma development. The
prior ~400–800 estimate is HIGH for the leaf-in-isolation, ON-TARGET-to-LOW for full closure.

## Decomposition (ordered; full table + skeletons in decomposition-tracehecke.md §4/§7)
**Leaf-internal:**
1. **L0** trace summand `(f∣A)∣δ = f∣(A·δ)`, `δ∈Γ₁` — DISCHARGED-mathlib (`slash_mul`), ~15.
2. **L2 (CRUX)** bijection `fiber(q₀) ≃ Option(Fin p)` with `A·δ_q ∈ glMap β_i·Γ₁` — **API-GAP,
   bounded, ~150–300**. Reuses PROVEN distinctness (`adj_upper_inv_mul_upper_not_mem_Gamma1`
   HeckeT_p_Gamma1:348, `adj_M_infty_inv_mul_upper_not_mem_Gamma1` :378) + the SMUL geometry
   (`T_p_lower_mul_{T_p_upper,M_infty}_smul_eq_…` DeltaB:456/483, `T_p_lower_tile_family`
   DeltaB:687, `mapGL_tile_mul_peterssonAdj_…` DeltaB:794). New = the `.out`-rep↔`γ_i` bridge
   (absorb via `slash_α_Gamma_p_α_invariant` FDT:134) + surjectivity (completeness).
3. **L1** `slGamma_p_αToGamma1_fiberCard (T_p_lower) = p+1` — collapses to `Fintype.card_option`
   of L2's codomain, ~10 given L2.
4. **L3** `Σ_q f∣(A·δ_q) = Σ_i f∣β_i` — `Finset.sum_bij'` + `slash_Gamma1_eq f`, ~40.
5. **L4** `Σ_i f∣β_i = T_p f` — copy `petN_heckeT_p_LHS_eq_aggregate` (CF:5207–5223) /
   `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307), ~25.

**Wiring (separate obligations the leaf is meant to feed):**
6. **W1** `(f∣A)` Γ_p(A)-invariant — DISCHARGED (`slash_α_Gamma_p_α_invariant_cuspForm` FDT:152).
7. **W2** `D =ₐₑ A•Γ_p(A)-FD` — API-GAP bounded ~80–150 (FDs for `Γ₁∩AΓ₁A⁻¹` via 879, `.ae_eq`).
8. **W3** apply trace engine `setIntegral_…_eq_traceSlash_Gamma1_fundDomain` (FDT:1612) — cite.
9. **W4** re-fold to `petN(f,T_p f)` — `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (PLN), ~40.
10. **W5 (OPEN)** c_p/c_N + det-`p^{k-2}` reconciliation to the BILINEAR both-slot balance — **no
    skeleton closes this; the genuine remaining wall.**

## Reference grounding
- Miyake (verbatim, PDF pages 84/146/147/150): Thm 2.8.2(1)(2), Lemma 4.5.6(1)(2), (4.5.26).
- Lean: `heckeT_p_fun` (HeckeT_p:111), `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307),
  `traceSlash_Gamma_p_α` (FDT:1332), trace engine FDT:1612, per-rep CoV FDT:1235, FD-image
  FDT:879. Residual `sorry`: ConcreteFamily:5391.

## Recommended execution order (if pursued)
L2 first (the crux; build the bijection + slash-match). Then L1/L3/L4/L0 → assemble the leaf
(BOUNDED, achievable). SEPARATELY, attempt the integrated route W2→W4 (bounded) and confront W5
(OPEN) — do NOT assume the leaf closes the residual `sorry` until W5 is resolved. If W5 stays
open, the leaf is still a NET GAIN: it isolates and discharges the combinatorial half of the
problem behind a clean, source-faithful named lemma, shrinking the residual `sorry`'s content to
the pure index/det-weight transfer.

## Constraints honored
READ-ONLY: no `lake build`/`lean` run, no tree edits, skeletons type-check-deferred in the
decomposition doc only. Protected statements untouched (`heckeT_p_aggregate_peeled_diagonal_balance`,
`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_axiom_clean`,
`miyake_4_6_14_*`).
