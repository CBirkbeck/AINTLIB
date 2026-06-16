# Tickets — Petersson/Hecke-adjoint frontier

Dependency-ordered. Goal: close `ConcreteFamily.lean:5198` (M_∞ residual) and `:5201` (upper
residual) inside `petN_heckeT_p_symmetric_form`, making `exists_simultaneous_eigenform_basis`
axiom-clean. Each ticket marked **EXIST** (proven, no work) / **BUILD** (new). Skeleton lemmas
live in `LeanModularForms/SMOObligations/PeterssonHeckeAdjoint.lean` (8 sorries, type-checks).

Legend: ⚠ = riskiest. ⊕ = mechanical. Sizes are source-grounded estimates.

---

## Phase A — FD-tile measure obligations (parallelisable; all in SMOObligations file)

### A1 ⊕ `nullMeasurableSet_M_infty_q_tile_star` (leaf N-∞) — BUILD-tiny
- Statement: skeleton @ PeterssonHeckeAdjoint.lean:52.
- Route: rewrite composed-`*` tile to nested-`•` via `mul_smul`, then `exact`
  `nullMeasurableSet_M_infty_q_tile` (SummandAdjoint.lean:1589, PROVEN).
- Deps: none. Size: ~5–10 lines.

### A2 ⊕ `nullMeasurableSet_T_p_upper_q_tile_star` (leaf N-U) — BUILD-tiny
- Statement: skeleton @ :64.
- Route: mirror `nullMeasurableSet_M_infty_q_tile`'s proof (SummandAdjoint:1589) with
  `T_p_upper p hp.pos b` in place of `M_∞`: `nullMeasurableSet_fd_aux` (SummandAdjoint:1162)
  `.preimage (measurePreserving_glPos_smul _ (det_val_inv_pos (glMap_T_p_upper_det_pos …)))`,
  pattern @ SummandAdjoint:1214.
- Deps: none. Size: ~15–25 lines.

### A3 ⚠ `aedisjoint_pairwise_M_infty_q_tiles` (leaf D-∞) — BUILD (RISKIEST #1)
- Statement: skeleton @ :84.
- Source: DS p.181 "the union SL₂(ℤ)=⋃_j {±I}Γα_j is disjoint" + Lemma 5.5.1.
- Route: `intro q₁ q₂ hne`; apply engine `aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1`
  (SummandAdjoint:1020) with `α₁ = glMap M_∞ * mapGL q₁.out⁻¹`, `α₂ = glMap M_∞ * mapGL q₂.out⁻¹`.
  Must supply: (i) `measurePreserving ((α₁⁻¹•·)) μ_hyp` via `measurePreserving_glPos_smul`
  (det>0 from `glMap_M_infty_det_pos` + `mapGL_det = 1`); (ii) `γ : SL(2,ℤ)` with
  `α₁⁻¹·α₂ = mapGL γ` and `γ ∈ Γ₁(N)` — here `α₁⁻¹α₂ = mapGL(q₁.out · q₂.out⁻¹)` (the M_∞
  factors cancel: `(glMap M·mapGL q₁⁻¹)⁻¹(glMap M·mapGL q₂⁻¹) = mapGL q₁ · glMap M⁻¹ glMap M · mapGL q₂⁻¹
  = mapGL(q₁·q₂⁻¹)`); (iii) PSL-nontriviality `(QuotientGroup.mk γ) ≠ 1` from `q₁ ≠ q₂` in
  `SL(2,ℤ)⧸Γ₁(N)` (so `q₁.out · q₂.out⁻¹ ∉ Γ₁(N)`-image-is-1, i.e. PSL class ≠ 1).
- **Risk**: the `q₁≠q₂ ⇒ PSL(q₁.out·q₂.out⁻¹)≠1` step needs care (`Γ₁(N) ≤ Γ₀(N)`, `-I` handling
  in PSL). Cross-check against the existing per-`b` lemma `aedisjoint_glMap_T_p_upper_pair_fd_per_q`
  (SummandAdjoint:1122) which does the analogous PSL-nontriviality for the `b`-index, and the
  Gamma1-coset disjointness `aedisjoint_imageGamma1_PSL_smul_Gamma1_fundDomain` (885).
- **fd-shape nuance**: the direct engine `aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1` lands
  on `Gamma1_fundDomain_PSL N`, but the assembler/`TpHeckeFamilyMeasureHypotheses` need
  `ModularGroup.fd`. The existing `aedisjoint_glMap_..._pair_fd_per_q` lemmas (1122/1652) DO
  produce `ModularGroup.fd`-shape output via `aedisjoint_glMap_smul_fd_of_mul_inv_eq_mapGL_PSL_ne`
  (981) — so A3/A4 should mirror THAT (the `_fd_` engine), not the `Gamma1_fundDomain_PSL` one.
- Deps: none. Size: ~40–70 lines. Possible API gap: a clean
  `q₁ ≠ q₂ → (QuotientGroup.mk (q₁.out * q₂.out⁻¹) : PSL(2,ℤ)) ∉ imageGamma1_PSL N` helper.

### A4 ⚠ `aedisjoint_pairwise_T_p_upper_q_tiles` (leaf D-U) — BUILD (RISKIEST #2)
- Statement: skeleton @ :100.
- Route: identical to A3 with `α = glMap (T_p_upper p hp.pos b)`; the `T_p_upper` factor cancels
  the same way, leaving `mapGL(q₁.out·q₂.out⁻¹)`. det>0 from `glMap_T_p_upper_det_pos`.
- **Risk**: same PSL-nontriviality step as A3 (shared helper); otherwise mechanical.
- Deps: A3 (shares the PSL-nontriviality helper). Size: ~30–50 lines.

### A5 `integrableOn_LHS_M_infty_iUnion` (leaf I-∞-LHS) — BUILD
- Statement: skeleton @ :120.
- Source: DS p.182 (convergence of the Petersson integral when one of f,g is a cusp form).
- Route: `rw [Set.iUnion_eq_biUnion_univ]` (or `← Finset.set_biUnion_univ`); apply mathlib
  `integrableOn_finset_iUnion` (`Mathlib/MeasureTheory/Integral/IntegrableOn.lean:227`) with
  `s = (Finset.univ : Finset (SL(2,ℤ)⧸Γ₁(N)))` (Fintype @ PeterssonLevelN:51); per-tile goal is
  per-`q` integrability — rewrite the `peterssonAdj (glMap M_∞)` slot into the mixed-slash form
  and `exact integrableOn_petersson_combinedGL_tile_on_fd` (DeltaBSystem:1122, PROVEN) on the
  per-tile `(glMap M_∞ * mapGL q.out⁻¹) • fd` (after `mul_smul`).
- **Risk**: matching the `peterssonAdj`-slot integrand to the `combinedGL_tile` integrand
  (the `f`/`g` order + diamond ops). Pattern available @ DeltaBSystem:1666–1676 (the M_∞ case
  uses `integrableOn_petersson_combinedGL_tile_on_fd g f (M_infty …) q`).
- Deps: A1 (for the per-tile NullMeas if needed by the union lemma). Size: ~25–45 lines.

### A6 `integrableOn_RHS_M_infty_iUnion` (leaf I-∞-RHS) — BUILD
- Statement: skeleton @ :135. Route: as A5, RHS integrand (`f`,`g` swapped via `petersson_symm`
  if needed). Deps: A1. Size: ~25–45 lines.

### A7 `integrableOn_LHS_T_p_upper_iUnion` (leaf I-U-LHS) — BUILD
- Statement: skeleton @ :150. Route: as A5 with `T_p_upper p hp.pos b`; pattern @ DeltaBSystem:1176
  (`integrableOn_petersson_combinedGL_tile_on_fd g f (T_p_upper …) q`). Deps: A2. Size: ~25–45 lines.

### A8 `integrableOn_RHS_T_p_upper_iUnion` (leaf I-U-RHS) — BUILD
- Statement: skeleton @ :165. Route: as A7, RHS. Deps: A2. Size: ~25–45 lines.

---

## Phase B — wiring (inside ConcreteFamily.lean; EXECUTION, not in skeleton)

### B0 (reference) per-tile residual identities — EXIST (no work)
- `TileFormIntegralResidual_M_infty` via `SigmaQPermResidual_M_infty_of_sigma_p_reduced` (4967)
  / `_of_per_q_tile_form` (4955) → `peterssonInner_M_infty_slash_adjoint_coset` (SummandAdjoint:1689).
- `TileFormIntegralResidual_upper b` via `peterssonInner_slash_adj_T_p_upper_q_summand_eq`
  (SummandAdjoint:~640). Both PROVEN; confirm the per-q reductions plug into the tile-form defs.

### B1 ⊕ shape bridge `*` ⇄ nested-`•`
- The 8 Phase-A lemmas are stated in composed-`*` shape; the assemblers
  `SigmaQPermResidual_{M_infty,upper}_of_TileFormIntegralResidual` (4856/5135) want nested-`•`
  shape `glMap M • (mapGL q.out⁻¹ • fd)`. Bridge via `mul_smul` (the identity
  `(glMap M * mapGL q⁻¹) • fd = glMap M • (mapGL q⁻¹ • fd)` is `h_domain` inside
  `peterssonInner_slash_adjoint_coset`). Apply to each `h_meas`/`h_disj`/`h_int`. Size: trivial
  per-hyp rewrites.

### B2 close `ConcreteFamily.lean:5198` (M_∞ residual)
- `exact SigmaQPermResidual_M_infty_of_TileFormIntegralResidual p hp hpN f g` fed with
  A1 (h_meas), A3 (h_disj), A5 (h_LHS_int), A6 (h_RHS_int) [all `*`→`•` bridged via B1] and
  B0's `TileFormIntegralResidual_M_infty`. Deps: A1,A3,A5,A6,B0,B1. Size: ~10–20 lines.

### B3 close `ConcreteFamily.lean:5201` (upper residual)
- `exact SigmaQPermResidual_upper_of_TileFormIntegralResidual p hp hpN f g` fed with
  A2 (∀b h_meas), A4 (∀b h_disj), A7 (∀b h_LHS_int), A8 (∀b h_RHS_int) and B0's
  `∀ b, TileFormIntegralResidual_upper b`. Deps: A2,A4,A7,A8,B0,B1. Size: ~10–20 lines.

### B4 verify axiom-cleanliness
- `lean_verify exists_simultaneous_eigenform_basis` — confirm `sorryAx` gone (expect
  `[propext, Classical.choice, Quot.sound]`). Then confirm Miyake 4.6.12 chain axiom-clean.

---

## Summary
- **Total tickets: 16** (8 Phase-A obligation lemmas + 4 Phase-B wiring/reference + B0 reference + B4 verify;
  effectively **8 BUILD leaves + ~5 wiring/verify**).
- **EXIST (no proof work)**: both residual assemblers, both per-tile residual identities (B0), the
  GL₂⁺ change-of-variables, all leaf engines.
- **BUILD**: A1–A8 (2 tiny NullMeas, 2 risky AEDisjoint-pairwise-q, 4 iUnion-integrability) + B-wiring.
- **Riskiest leaves**: A3 & A4 (same-family pairwise-over-`q` AEDisjoint — the only genuinely-new
  mathematical direction; needs the `q₁≠q₂ ⇒ PSL(q₁.out·q₂.out⁻¹)≠1` helper). Secondary risk:
  A5–A8 integrand-matching to `integrableOn_petersson_combinedGL_tile_on_fd`.
- **Feasibility: BOUNDED** — every leaf has a cited proven engine; no open-ended piece.

## Suggested execution order
A1, A2 (warm-up, tiny) → A3 (build the shared PSL-nontriviality helper) → A4 → A5,A6,A7,A8
(parallel) → B0 (confirm) → B1 → B2, B3 → B4.
