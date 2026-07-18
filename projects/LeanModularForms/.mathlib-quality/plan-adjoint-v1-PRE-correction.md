# Plan — Petersson/Hecke-adjoint frontier (axiom-clean spectral theorem)

## Goal
Make `AdjointTheoryPetersson.exists_simultaneous_eigenform_basis` (line 880) axiom-clean by
closing the **two** residual sorries in
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean:5198` and `:5201`
(inside `petN_heckeT_p_symmetric_form`). This is the last prerequisite to make the full
Miyake 4.6.12 development axiom-clean. The two leaves are the M_∞ and upper-triangular FD-tile
residuals of the diamond-twisted Petersson self-adjointness of `T_p` (Miyake Thm 4.5.4 /
Diamond–Shurman Prop 5.5.2 / Thm 5.5.3).

## What is the mathematics (verified against the PDFs)
DS §5.4–5.5 (PDF idx 193–198) and Miyake §2.8/§4.5 (PDF idx 84, 144) give the proof:
`⟨T_p f, g⟩ = ⟨⟨p⟩f, T_p g⟩` follows from **Prop 5.5.2(b)** (`⟨f[ΓαΓ],g⟩ = ⟨f,g[Γα′Γ]⟩`),
which reduces by **Lemma 5.5.1(c)** (`ΓαΓ = ⊔ β_jΓ`) to a finite sum of **Prop 5.5.2(a)**
per-orbit-rep identities `⟨f[β]_k,g⟩ = ⟨f,g[β′]_k⟩`, each proven by the change-of-variables
`z ↦ β′z` using the cocycle relation, `Im(β′z) = detβ′·|j(β′,z)|⁻²·Imz`, and the
**GL₂⁺-invariance of the hyperbolic measure dµ** (Exercise 5.4.1(a)). See
`decomposition-adjoint.md` for full verbatim quotes and the Lean↔source paragraph.

## State of the Lean proof (verified)
- Entire adjoint/spectral chain is sorry-free EXCEPT the 2 ConcreteFamily sorries
  (`grep -c sorry`: 0 in DeltaBSystem/FDTransport/SummandAdjoint/TileBridge/PeterssonLevelN/
  AdjointTheory/AdjointTheoryPetersson; 2 in ConcreteFamily).
- The deepest analytic leaf — DS 5.5.2(a)/Miyake 2.8.2(1) — is **already proven**:
  `peterssonInner_slash_adjoint` (AdjointTheory:770), resting on mathlib
  `measurePreserving_smul (⟨α,hα⟩:GL(2,ℝ)⁺) μ_hyp` (= DS Exercise 5.4.1(a)).
- The per-q tile identities are proven: `peterssonInner_M_infty_slash_adjoint_coset`,
  `peterssonInner_slash_adj_T_p_upper_q_summand_eq` (SummandAdjoint).
- **Both residuals already have proven assemblers**:
  `SigmaQPermResidual_M_infty_of_TileFormIntegralResidual` (4856),
  `SigmaQPermResidual_upper_of_TileFormIntegralResidual` (5135), each taking the four FD-tile
  measure hypotheses + the per-tile residual identity.

## The open frontier (what must be built)
Discharge the four FD-tile measure hypotheses, for both tile families (M_∞ and `T_p_upper b`):
1. **NullMeasurableSet** of each tile `(glMap M * mapGL q.out⁻¹) • fd` — engine proven
   (`nullMeasurableSet_M_infty_q_tile`, `nullMeasurableSet_fd_aux`); ~mechanical.
2. **Pairwise AEDisjoint over `q`** (same family) — engine proven
   (`aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1`); **this is the genuinely-new direction**
   (project has cross-family per-q and same-family per-b, not same-family per-q).
3/4. **IntegrableOn (LHS/RHS) over the AE-disjoint tile iUnion** — per-tile integrability proven
   (`integrableOn_petersson_combinedGL_tile_on_fd`, DeltaBSystem:1122); lift to the finite iUnion
   via mathlib `integrableOn_finset_iUnion` over `Fintype.univ`.

Then (EXECUTION wiring inside ConcreteFamily): bridge composed-`*` ⇄ nested-`•` tile shape
(`mul_smul`), construct the private `TpHeckeFamilyMeasureHypotheses` bundle, and feed the two
proven assemblers.

## Strategy / ordering
- **Phase A (independent leaves, parallelisable).** Build the 8 obligation lemmas in
  `SMOObligations/PeterssonHeckeAdjoint.lean` (NullMeas ×2, AEDisjoint-pairwise-q ×2,
  IntegrableOn ×4). Riskiest first: the two AEDisjoint-pairwise-q lemmas (need the per-q
  conjugation algebra `(glMap M·mapGL q₁.out⁻¹)⁻¹(glMap M·mapGL q₂.out⁻¹) = mapGL γ ∈ Γ₁(N)`).
- **Phase B (wiring, inside ConcreteFamily).** Bridge `*`⇄`•`; construct the bundle; close
  5198 and 5201 via the assemblers + the proven per-tile/per-q identities.

## Design decisions
- New file `SMOObligations/PeterssonHeckeAdjoint.lean` (imports ConcreteFamily) holds the 8
  public obligation lemmas — ConcreteFamily is 5376 lines, and these statements reference only
  public names. The final private wiring stays in ConcreteFamily (the assemblers + bundle are
  `private`). This keeps the new analytic content reviewable and out of the giant file.
- All tile shapes use the composed-`*` form `(glMap M * mapGL q.out⁻¹) • ModularGroup.fd`
  matching `TpHeckeFamilyMeasureHypotheses` exactly (verified type-checks).

## Constraints
No `native_decide`, no final-sorry, no custom axiom, no `set_option maxHeartbeats`. Do not touch
`strongMultiplicityOne_axiom_clean` or `miyake_4_6_14_delta_slash_sum_coeff_zero`. Do not touch
the existing 4.6.12 `plan.md`/`decomposition.md`/`tickets.md`. No stray/backup files.

## Feasibility verdict
**BOUNDED.** No piece is open-ended. The hard analytic core (the GL₂⁺ change-of-variables and
the per-tile/per-q adjoint identities) is already proven; the FD-tile fundamental-domain
tiling (`isFundamentalDomain_Gamma1_coset_tiling`) and the measure-preservation
(`measurePreserving_glPos_smul` / mathlib `measurePreserving_smul`) are present and used. The
remaining work is measure-theoretic bookkeeping — NullMeasurableSet/AEDisjoint/IntegrableOn of
explicit tiles — with all engines proven; only the same-family pairwise-over-`q` AEDisjoint and
the finite-iUnion integrability lift are genuinely new, and both have a clear, cited route.

## Artifacts
- `.mathlib-quality/plan-adjoint.md` (this file)
- `.mathlib-quality/decomposition-adjoint.md` (verbatim source quotes + leaf tree + citations)
- `.mathlib-quality/tickets-adjoint.md` (dependency-ordered ticket board)
- `LeanModularForms/SMOObligations/PeterssonHeckeAdjoint.lean` (8-lemma sorry skeleton, type-checks)
