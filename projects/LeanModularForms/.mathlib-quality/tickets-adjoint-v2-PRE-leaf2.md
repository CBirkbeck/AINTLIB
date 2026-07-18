# Tickets (v2, CORRECTED) — T_p Petersson self-adjointness, GLOBAL route

**Supersedes** `tickets-adjoint-v1-PRE-correction.md` (per-tile route, proven WRONG).

Goal: prove `petN_heckeT_p_symmetric_form_global` (the GLOBAL DS 5.5.2(b) route, no M_∞/upper
split), then repoint `heckeT_p_adjoint`'s chain to it and delete the 2 false-split sorries at
`ConcreteFamily.lean:5198`/`:5201`. Makes `exists_simultaneous_eigenform_basis` axiom-clean.

Skeleton (4 decls, all `:= by sorry`) is in `ConcreteFamily.lean` ~5376–5475; verified by
`lean_diagnostic_messages`: **4 sorry warnings, 0 errors, 0 failed dependencies**.

Legend: **EXIST** = proven, no work. **BUILD** = new. ⚠ = riskiest. ⊕ = mechanical.

---

## Phase A — the three bridge leaves (in ConcreteFamily, near the new skeleton)

### A1 ⊕ `aggregate_HeckeFD_measure_hyps` (leaf 3) — BUILD
- Statement: skeleton ~5437. Returns the conjunction (∀i NullMeas `β_i•D₁`) ∧
  (∀i IntegrableOn swapped kernel on `D₁`) ∧ (IntegrableOn fwd kernel on `⋃_i β_i•D₁`).
- Source: DS p.182 "ϕ(α(τ))→0 as Im→∞ … convergent" (one of f,g a cusp form); p.181
  "ℚ∪{∞} measure zero".
- Route: `refine ⟨?_, ?_, ?_⟩`. (i) NullMeas of `β_i•(PSL-FD)` — `β_i` det>0
  (`glMap_M_infty_det_pos`, `glMap_T_p_upper_det_pos`) + `measurePreserving_glPos_smul` preimage
  of the proven PSL-FD null-measurability; per-`i` via `Fintype.sum_option` / `cases i`. (ii)
  Per-`i` integrability on `D₁` — adapt `integrableOn_petersson_combinedGL_tile_on_fd`
  (DeltaBSystem:1122) lifted from `fd` to `D₁ = Gamma1_fundDomain_PSL` (which is a finite union
  of `fd`-tiles; bounded measure `hyperbolicMeasure_..._lt_top`). (iii) iUnion integrability —
  `integrableOn_finset_iUnion` (mathlib) over `Finset.univ : Finset (Option (Fin p))` + (ii).
- Deps: none. Size: ~60–110 lines. Patterns: DeltaBSystem:1666–1736.

### A2 `petN_heckeT_p_LHS_eq_aggregate` (leaf 1) — BUILD
- Statement: skeleton ~5397. `petN(T_p f,g) = ⟨D₁⟩(Σ_i f∣β_i) g`.
- Source: DS Def 5.1.3 + Lemma 5.5.1(c) "the {β_j} can serve in Definition 5.1.3 of [ΓαΓ]_k".
- Route: (a) `heckeT_p_cusp` coerces to `Σ_i f∣β_i` via `heckeT_p_fun_eq_coset_sum`
  (HeckeT_n; pattern at DeltaBSystem:1646) — i.e. `T_p f = (Σ_b f∣T_p_upper b) + f∣M_∞`,
  matching the `Option (Fin p)` `match` after `Fintype.sum_option`. (b) `petN(·,g)` on the LHS
  unfolds (def of `petN`) to `Σ_q ⟨fd⟩(·∣q⁻¹)(g∣q⁻¹)`; `peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum`
  (FDTransport:410) rewrites `⟨D₁⟩` to that same `Σ_q`. Use `peterssonInner` linearity in the
  first slot to pull the `Σ_i` out (both sides linear in `f`-slot).
- Deps: A1 not needed (LHS side). Size: ~40–80 lines.
- ⚠ note: keep `match`/sum-of-slashes alignment via `simp only [Fintype.sum_option]` /
  `SlashAction.sum_slash`; mirror the algebra in `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` body (122).

### A3 ⚠ `petN_heckeT_p_RHS_aggregate_eq` (leaf 2) — BUILD (RISKIEST)
- Statement: skeleton ~5417. `⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower) = petN(⟨p⟩f, T_p g)`.
- Source: DS 5.5.2(b) "∑_j ⟨f,g[β′_j]_k⟩_{Γ∩β_jΓβ_j⁻¹} = ⟨f,g[Γα′Γ]_k⟩" + Thm 5.5.3 "= ⟨p⟩⁻¹T_p".
- Route:
  1. Split family `iUnion` per-`i`: `peterssonInner_iUnion_finite_aedisjoint` (PeterssonLevelN:1140)
     with the AEDisjoint/NullMeas/Integrable from A1 → `Σ_i ⟨β_i•D₁⟩ f (g∣T_p_lower)`.
  2. Identify `β_i•D₁ = β_i•Gamma_p_α_fundDomain_PSL(α_T_p_Q i)` (the family FD = the
     conjugate-intersection-group FD; `α_T_p_Q` at ConcreteFamily:32). Apply the PROVEN
     `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (ConcreteFamily:291) →
     `Σ_i Σ_{Γ_p(α)-cosets} ⟨β_i·q⁻¹•Γ₁-FD⟩ f (g∣T_p_lower)`.
  3. On each term apply DS 5.5.2(a) (`peterssonInner_slash_adjoint`, AdjointTheory:770) /
     `peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd` (FDTransport:1156) and collapse the
     `Γ_p(α)`-coset sum to `relIndex • petN(...)` via
     `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDTransport:1169).
  4. relIndex CANCELLATION: the `slGamma_p_αToGamma1_fiberCard` is identical across the family
     terms (DS Lemma 5.5.1(b): `[SL:Γ_p(α)]` depends only on the double coset, same for `α`,`α′`)
     — divide out / `smul_right_injective`.
  5. Recombine `Σ_i (g∣T_p_lower-via-β_i)` into `T_p g` (with the `⟨p⟩` twist) using the family
     slash identities `slash_diamond_inv_T_p_upper_eq_T_p_lower_delta` (DeltaBSystem:1739) and
     `slash_T_p_upper_eq_diamond_slash_T_p_lower_factor` (TileBridge:3647), inverse to leaf 1.
- Deps: A1. Size: ~120–220 lines. **The analytic heart.** Risk localised to steps 4–5
  (relIndex bookkeeping + family recombination); every sub-step has a proven engine.

---

## Phase B — wiring + repoint (in ConcreteFamily)

### B1 `petN_heckeT_p_symmetric_form_global` (top assembler) — BUILD-wiring
- Statement: skeleton ~5455 (currently `sorry` to dodge the `whnf` budget).
- Route: `obtain ⟨hm, h_int_per, hfi⟩ := aggregate_HeckeFD_measure_hyps p hp hpN f g`; then
  `simp only [Finset.sum_option, Set.iUnion_option, Fintype.sum_option]` to expand the `match`
  family BEFORE the `rw` (this is why the eager term-mode form timed out — a definitional issue,
  not a gap); then `rw [petN_heckeT_p_LHS_eq_aggregate, peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R … hm h_int_per hfi, petN_heckeT_p_RHS_aggregate_eq]`.
  If `rw` still struggles, use `calc` with the three leaves as explicit steps.
- Deps: A1, A2, A3. Size: ~10–30 lines.

### B2 ⊕ repoint `heckeT_p_adjoint` chain — BUILD-wiring
- `petN_heckeT_p_symmetric_form` (5185) is consumed (transitively) by
  `petN_heckeT_p_diamond_shift` → `petN_heckeT_p_adjoint_of_diamond_shift` (5341) →
  `heckeT_p_adjoint` (5368). Replace the call to `petN_heckeT_p_symmetric_form` with
  `petN_heckeT_p_symmetric_form_global` (same signature — verified type-identical).
- Then DELETE the superseded split: the 2 sorries' parent `petN_heckeT_p_symmetric_form`
  (5185–5201) and any now-unused `SigmaQPermResidual_*` / `DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed`
  lemmas. Confirm no other consumer (grep). Size: small, but verify the dependency graph first.

### B3 verify axiom-cleanliness — VERIFY
- `lean_verify HeckeRing.GL2.heckeT_p_adjoint` and
  `lean_verify ...exists_simultaneous_eigenform_basis` — confirm `sorryAx` gone (expect
  `[propext, Classical.choice, Quot.sound]`). Then confirm the Miyake 4.6.12 chain is unaffected.

---

## Summary
- **Total: 6 tickets** (A1–A3 BUILD leaves, B1 wiring, B2 repoint+delete, B3 verify).
- **EXIST (no proof work)**: the GLOBAL aggregate (ConcreteFamily:122/202, UNUSED), the
  `Γ_p(α)` engine (FDTransport + ConcreteFamily:291), the GL₂⁺ change-of-variables
  (AdjointTheory:770), the family slash identities, the per-tile integrability.
- **BUILD**: A1 (measure hyps), A2 (LHS=aggregate), **A3 (aggregate=RHS, the heart)**, B1/B2 wiring.
- **Riskiest**: A3 — the per-`i` `Γ_p(α)` collapse + relIndex cancellation + family
  recombination. Bounded; relIndex cancels by DS Lemma 5.5.1(b).
- **Feasibility: BOUNDED.** No open-ended piece; the global identity is already proven.

## Suggested execution order
A1 → A2 → **A3** → B1 → B2 → B3.

## DO-NOT
Do NOT try to prove `SigmaQPermResidual_M_infty`/`SigmaQPermResidual_upper` (FALSE in isolation).
Do NOT split the Hecke family. Do NOT touch the 4.6.12 board, `strongMultiplicityOne_axiom_clean`,
or `miyake_4_6_14_delta_slash_sum_coeff_zero`. No `set_option maxHeartbeats`.
