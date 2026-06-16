# Plan (v3, ADVERSARIAL) — leaf 2 `petN_heckeT_p_RHS_aggregate_eq`: verdict OPEN

**Supersedes** `plan-adjoint-v2-PRE-leaf2.md` (BOUNDED — **WRONG**). See
`decomposition-adjoint.md` for the full red-team analysis + verbatim sources + Lean citations.

## Binding verdict: **OPEN**

Leaf 2 (ConcreteFamily.lean:5450) is mathematically TRUE (DS Prop 5.5.2(b) at α=diag(1,p)) but
**logically equivalent — modulo only the PROVEN leaf1 + aggregate rewrites — to the entire
symmetric-form goal `petN(T_p f,g) = petN(⟨p⟩f,T_p g)`**. It is NOT a bounded wiring gap.

### Proof of the OPEN verdict (one line, machine-checked)
`lean_goal` inside `petN_heckeT_p_symmetric_form_global` (5537), at the point after
`obtain … ; rw [petN_heckeT_p_LHS_eq_aggregate, peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD]`
and before the final `rw [petN_heckeT_p_RHS_aggregate_eq]`, shows the residual goal is **leaf 2's
statement, verbatim**, with `goals_after = []`. Since leaf1 (5403) + the aggregate (122) are
proven equalities, leaf 2 ⟺ the goal.

### Why the v2 plan was wrong
v2 claimed the proven aggregate `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` (122)
"IS DS 5.5.2(b)" and that leaf 2 is "assembly + relIndex cancellation". In fact:
- The aggregate is only DS **Def 5.1.3** (LHS expansion). It rests on
  `peterssonInner_sum_slash_adjoint_constantRHS` (SummandAdjoint:864), whose `hadj` hypothesis
  requires all Hecke reps to share ONE Petersson-adjoint `g' = g∣T_p_lower` — the *trivial*
  same-adjoint slot-swap. It rewrites the symmetric form's LHS into itself; it never touches the
  RHS `petN(⟨p⟩f,·)` and carries **zero** cross-term content.
- The v2 route via `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (291) +
  `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (1169) is **inapplicable**: lemma 291 needs
  the multi-tile `β_i•Γ_p(α_i)-FD`, but the aggregate hands leaf 2 only the single tile
  `β_i•Γ₁_FD_PSL`. The relIndex cancellation is therefore vacuous, and even if forced, the
  residual is `h_HeckeFD_swap` = the goal.

## L_cov (the make-or-break leaf): NOT proven over Γ_p(α_j)
- PROVEN: `peterssonInner_slash_adjoint` (AdjointTheory:770) — the GL₂⁺ change of variables
  `⟨D⟩(f∣α) g = ⟨α•D⟩ f (g∣peterssonAdj α)` over ANY measurable `D`. This is the *substrate* of
  DS 5.5.2(a).
- NOT PROVEN: the full DS 5.5.2(a) `⟨f[α]_k,g⟩_{α⁻¹Γα} = ⟨f,g[α′]_k⟩_Γ`, which additionally
  needs the **FD-image identification** `α•(FD of α⁻¹Γα) ≈ FD of Γ` (DS Lemma 5.5.1(a,b)). The
  repo's `Γ_p(α)` machinery (FDTransport 860/916/957/1169) is purely DS Lemma 5.5.1(b)
  index/volume on the SAME-domain kernel; it never does the `f∣α↔g∣α′` exchange. There is NO
  lemma `β_j•Gamma_p_α_fundDomain_PSL(α_j) = Γ₁_FD`, NO per-rep exchange over `Γ_p(α_j)`, and NO
  bridge between the PSL family-union `⋃_i β_i•D₁` and the SL coset-union `⋃_q β q⁻¹ fd`.

## The c_N arithmetic closes; it is NOT the issue
leaf1's `petN = c_N • ⟨D₁⟩(…)` (via `setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum`,
FDTransport:381) and leaf2's `c_N •` are consistent; the aggregate is fiber-count-free between
them. Leaf 2's stated `slToPslQuot_fiberCard N •` is the CORRECT statement — **no correction**.

## What OPEN requires (multi-week, not <150 LOC)
Build DS 5.5.2(a) over the conjugate-intersection group `Γ_p(α_j)`:
1. FD-image identification: `β_j • (Gamma_p_α_fundDomain_PSL α_j)` is a.e. an FD for
   `β_j Γ₁ β_j⁻¹ ∩ Γ₁` (hard: det β_j = p, β_j ∉ PSL(2,ℝ) Γ₁-symmetries).
2. Per-rep exchange over those FDs (CoV via 770, but with conjugate-group domains).
3. Family summation with `[Γ₁:Γ_p(α_j)]` index reconciliation + the cross-block
   `Gamma1QuotEquivOfGamma0` reindex (false per-block, closes only globally — id `d6e58f26`).
Several hundred LOC of new measure-theoretic + FD-combinatorial development = the Diamond–Shurman
§5.5 / Miyake §2.8 double-coset CoV over conjugate-intersection FDs.

## Recommendation
- Do NOT pursue the "global aggregate" route as a *proof* of the symmetric form: it is circular.
  Keep the proven leaf1/aggregate/leaf3 as honest restatements, but recognise leaf 2 = the goal.
- Either (a) commit to the multi-week DS 5.5.2(a)-over-Γ_p(α) build, or (b) park
  `petN_heckeT_p_symmetric_form` (and the downstream `heckeT_p_adjoint`,
  `exists_simultaneous_eigenform_basis` axiom-cleanliness) as OPEN, matching T024 in MEMORY.
- The two false-split sorries (5198/5201) and the leaf-2 sorry (5461) all encode the SAME
  irreducible content (`h_HeckeFD_swap ⟺ symm`). There is exactly ONE genuine open obligation,
  appearing in three guises.

## Constraints honoured
No skeleton edits (RED-TEAM/planning-only). No `native_decide`, no `set_option maxHeartbeats`, no
custom `axiom`. Protected statements untouched (`heckeT_p_adjoint`,
`exists_simultaneous_eigenform_basis`, `petN_heckeT_p_symmetric_form` sigs;
`strongMultiplicityOne_axiom_clean`, `miyake_4_6_14_delta_slash_sum_coeff_zero`). No new stray
files beyond the v2 backups + these v3 artifacts. No `lake build` run.

## Artifacts
- `.mathlib-quality/plan-adjoint.md` (this file)
- `.mathlib-quality/decomposition-adjoint.md` (red-team analysis, smoking gun, per-leaf table)
- `.mathlib-quality/tickets-adjoint.md` (the one genuine open obligation + its skeleton)
- backups: `*-adjoint-v2-PRE-leaf2.md`, `*-adjoint-v1-PRE-correction.md`
