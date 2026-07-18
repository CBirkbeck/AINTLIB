# Plan (v2, CORRECTED) — T_p Petersson self-adjointness, GLOBAL double-coset route

**Supersedes** `plan-adjoint-v1-PRE-correction.md` (which planned a per-tile "8 FD-tile
measure leaves" pass — proven WRONG in EXECUTION; learnings.jsonl id `d6e58f26`).

## Goal
Make `AdjointTheoryPetersson.exists_simultaneous_eigenform_basis` (line 880) axiom-clean by
proving `T_p` Petersson self-adjointness `petN(T_p f, g) = petN(⟨p⟩f, T_p g)` (DS Prop 5.5.2(b)
/ Thm 5.5.3; Miyake Thm 4.5.4) WITHOUT the false M_∞/upper split. The split currently leaves 2
sorries at `ConcreteFamily.lean:5198` and `:5201` inside `petN_heckeT_p_symmetric_form`.

## The mathematics (verified against the PDFs)
DS §5.5 (PDF idx 196–198) proves the Hecke adjoint GLOBALLY. `ΓαΓ = ⊔_j β_jΓ` (Lemma 5.5.1(c)),
and `⟨f[ΓαΓ]_k,g⟩ = ∑_j ⟨f[β_j]_k,g⟩_{β_j⁻¹Γβ_j∩Γ} = ∑_j ⟨f,g[β′_j]_k⟩_{Γ∩β_jΓβ_j⁻¹} =
⟨f,g[Γα′Γ]_k⟩` — each term's change-of-variables (5.5.2(a)) is taken over the
**conjugate-intersection group** `β_j⁻¹Γβ_j∩Γ`, a fundamental domain of `[Γ:β_j⁻¹Γβ_j∩Γ]`
copies of `D*`, NOT over `Γ` itself. The CORRECTION: the per-tile-family identity (M_∞ alone /
upper alone) is FALSE because `det M_∞ = p`; closure holds only over the whole double coset.
See `decomposition-adjoint.md` for full verbatim quotes + the Lean↔source paragraph.

## State of the Lean proof (verified this pass)
- Adjoint/spectral chain sorry-free EXCEPT the 2 ConcreteFamily sorries (`grep -c sorry`: 0 in
  TileBridge/FDTransport/SummandAdjoint/DeltaBSystem/PeterssonLevelN; 2 in ConcreteFamily).
- The GLOBAL identity DS 5.5.2(b) is **already proven** but **currently UNUSED**:
  `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` (ConcreteFamily:122) + `_PSL_R`
  (:202): `⟨D₁⟩(Σ_i f∣β_i) g = ⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower)` over the FULL family
  `Option (Fin p) = {M_∞} ⊔ {T_p_upper b}`.
- The conjugate-intersection-group engine is fully present:
  `Gamma_p_α` (FDTransport:41); `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q`
  (ConcreteFamily:291); `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDTransport:1169);
  `peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum` (FDTransport:410).
- The per-rep change-of-variables DS 5.5.2(a) = `peterssonInner_slash_adjoint`
  (AdjointTheory:770), on mathlib `measurePreserving_smul`.

## The corrected bridge (3 new leaves + wiring)
Route `petN(T_p f,g)` through the proven aggregate, never splitting the family:

1. **leaf 1 `petN_heckeT_p_LHS_eq_aggregate`** —
   `petN(T_p f,g) = ⟨D₁⟩(Σ_i f∣β_i) g`.
   (`heckeT_p_fun_eq_coset_sum` + `peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum`.)
2. **proven aggregate** `..._HeckeFD_PSL_R` (:202) — needs leaf 3's 3 measure hyps.
3. **leaf 2 `petN_heckeT_p_RHS_aggregate_eq`** (RISKIEST) —
   `⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower) = petN(⟨p⟩f, T_p g)`.
   (per-i `iUnion` split → `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` →
   `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` → relIndex cancels → family slash
   identities `slash_diamond_inv_T_p_upper_eq_T_p_lower_delta`.)
4. **leaf 3 `aggregate_HeckeFD_measure_hyps`** — the 3 NullMeas/Integrable hyps for the
   aggregate (per-tile engines at DeltaBSystem:1122/1666–1736 + mathlib `integrableOn_finset_iUnion`).
5. **top `petN_heckeT_p_symmetric_form_global`** — `obtain` leaf 3; `rw` leaf 1 → aggregate →
   leaf 2 (expand the `match` via `simp only [Finset.sum_option, Set.iUnion_option]` first).

## Strategy / ordering
- **Phase A**: leaf 3 (warm-up; reuse DeltaBSystem integrability) → leaf 1 → **leaf 2** (the
  analytic heart; build the per-i `Γ_p(α)` collapse + relIndex cancellation).
- **Phase B (wiring)**: top assembler; then repoint `heckeT_p_adjoint`'s chain from
  `petN_heckeT_p_symmetric_form` to `petN_heckeT_p_symmetric_form_global`; delete the
  superseded split lemmas (`SigmaQPermResidual_*`, `DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed`
  if now unused) and the 2 sorries.

## Design decisions
- New lemmas live in `ConcreteFamily.lean` (the discharge is here; upstream-only constraint
  satisfied). Stated over `Gamma1_fundDomain_PSL N` + the `Option (Fin p)` family `match`,
  matching the proven aggregate verbatim (verified type-checks).
- Do NOT attempt to prove the individual `SigmaQPermResidual_M_infty/upper` — they are FALSE.
  The `_global` route bypasses `DSDoubleCosetTileBridge`'s split entirely.

## Constraints
No `native_decide`, no final-sorry left in the chain, no custom axiom, no
`set_option maxHeartbeats` (use `simp only [Finset.sum_option, Set.iUnion_option]` for the
`match`-expansion budget issue). Do NOT touch the 4.6.12 board (`plan.md`/`decomposition.md`/
`tickets.md`), `strongMultiplicityOne_axiom_clean`, or `miyake_4_6_14_delta_slash_sum_coeff_zero`.
No stray/backup files beyond the `*-v1-PRE-correction.md` backups.

## Feasibility verdict
**BOUNDED.** The full GLOBAL identity (DS 5.5.2(b)) and the conjugate-intersection-group
(`Γ_p(α)`) change-of-variables are ALREADY PROVEN; the aggregate is sitting unused. The
remaining work is assembly + the per-i `Γ_p(α)` collapse with relIndex cancellation (leaf 2).
The relIndex cancels by DS Lemma 5.5.1(b) (index depends only on the double coset). No
open-ended piece. The only non-mathematical risk is `match`/heartbeat hygiene in the wiring.

## Artifacts
- `.mathlib-quality/plan-adjoint.md` (this file)
- `.mathlib-quality/decomposition-adjoint.md` (verbatim quotes + corrected leaf tree)
- `.mathlib-quality/tickets-adjoint.md` (dependency-ordered ticket board)
- `LeanModularForms/HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean` (4-decl sorry skeleton @
  ~5376–5475; verified 4 sorry warnings / 0 errors / 0 failed deps)
- backups: `*-adjoint-v1-PRE-correction.md`
