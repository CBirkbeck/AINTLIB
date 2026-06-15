# Adversarial Audit — Tate Acyclicity Chain, Session 26

*Date: 2026-05-18. Scope: every sorry on the `isSheafy_ofStronglyNoetherianTate` discharge path.*
*Trigger: user directive — adversarial `/develop --decompose` passes until /beastmode hits no blocks.*

> **Session 27 update (2026-05-18 — round-4 reviewer reply integrated)**: see
> `.mathlib-quality/expert-review/2026-05-18-4/integration.md`.
> Key Parts IV-VI deltas:
> - **D12 sub-tree**: SCRATCH the "canonical Huber-field valuation" mathlib gap (~30-50 LOC). Replace with case-split: open `𝔪` → trivial valuation; non-open → Wedhorn 7.45 chain. Reduces D12 LOC ~120-150 → ~50-80.
> - **I2** (`laurentCover_exact_general`): **APPLIED THIS SESSION** — added `[IsDomain A]`, docstring updated.
> - **Cor 8.32**: SPLIT into `T-COR832-CLEAN-VIA-FLAT` (main, consumes general restriction flatness from C1) + `T-COR832-CLEAN-VIA-LAURENT` (subsidiary, refinement-tree internal only).
> - **C3 sub-tree**: 3 reviewer-named sub-lemmas (`valuation_extends_to_localization_of_rationalOpen`, `valuation_extends_to_completion_of_continuous`, `Spa_comap_image_eq_rationalOpen`).
> - **Tier order revised** per reviewer: F12 → C3 → Stacks 0316 → `cor_8_32_clean_via_flat` → 8.33 patch (done) → 8.31 replacements (already proved).
> - **Methodology**: 5-column hypothesis ledger now in `feedback_hypothesis_ledger_v2.md` (supersedes v1).

This document consolidates findings from **6 parallel adversarial review agents** (Waves 1 + 2 = Clusters A, B+C, D, E+K+L, F, I+H) plus targeted code inspection of placeholder/mismatch issues. It is the master pre-flight document for `/beastmode`.

## Executive summary

| Category | Count | Notes |
|----------|------:|-------|
| Total in-scope sorries (231 occurrences, ~56 named leaves) | 56 | Per existing `decomposition.md` |
| NEW B2 candidates found this session | 7 | Logged in `b2_log.jsonl` |
| Placeholder violations FIXED this session | 1 | `_sub_lemma_L5_1_1` rewritten to honest sorry |
| Signature corrections RECOMMENDED (statement-level B2) | 3 | D9, D12, H-2 — need user OK before beastmode |
| Path α end-to-end breaks identified | 5 | A3 docstring/sig, B5 cascade, C1 import-cycle, II.2 degenerate wrapper, flat_over_base_tate |
| Sub-trees needed (each its own mini-development) | 6 | Stacks 0316, D2, D9, D12, D14.3, F-chain |
| Mathlib gaps identified | 3 | AdicCompletion.isNoetherianRing, MvPowerSeries Hilbert basis, "canonical valuation on complete Huber field" |
| Cluster L verdict | CLEAR | Replacements exist at TateAlgebra.lean — no Path α hole |
| Stacks 0316 skeleton | DONE | `Adic spaces/AdicCompletionNoetherian.lean` (5 sorries, compiles) |

**Bottom line**: the Path α chain is **NOT ready for /beastmode** as-is. Three statement-level signature corrections + one placeholder fix (already done) + one A3 IsDomain decision are required pre-flight. After those, beastmode can pick up tickets in the recommended order without hitting blocks.

---

## Part I — NEW findings from Session 26 (this audit)

### NEW B2 candidates (added to `b2_log.jsonl`)

| ID | Lemma | Issue | Counterexample |
|----|-------|-------|----------------|
| B2-D12-2026-05-18 | `exists_spa_point_supp_eq_maxIdeal_of_complete` (Presheaf.lean:2360) | Missing `[CompleteSpace A] [UniformSpace A] [IsUniformAddGroup A]` | Pathological non-complete Huber with non-closed max ideal |
| B2-D9-2026-05-18 | `exists_valuationSubring_dominating_for_rationalOpen` | Missing `[IsAdicComplete P.I P.A₀]` | A = ℤ[X], P.A₀ = ℤ[X], P.I = (X), 𝔭 = (1−X): 1 = X + (1−X) ∈ I + 𝔭, so I·R' = R' |
| B2-I2.3-2026-05-18 | `iInf_pow_eq_bot_for_nonunit_in_nondomain_complete_noetherian_tate` | FALSE without `[IsDomain A]` | A = ℚ_p × ℚ_p, f = (p, 0): idempotent annihilator (0,1)·f = 0 gives ⨅(f)^n ⊇ {(0,c)} ≠ ⊥ |
| B2-H2-2026-05-18 | `exists_dominating_unit_noHArch_finset` | Hidden `CompactSpace ↥(Spa A A⁺)` dependency | (Not a falsity B2, but signature-incompleteness B2: singleton version takes (hY : IsCompact Y) explicitly, finset version drops it) |
| B2-L5.1.1-PLACEHOLDER | `_sub_lemma_L5_1_1_tateAlgebra_eq_adicCompletion` | Vacuous self-iso `∃ e : X ≃+* X, e = e` discharged by reflexivity | FIXED THIS SESSION — rewritten to honest sorry stating `TateAlgebra A ≃+* base-change of P.A₀[X]^∧` |
| B2-A3-DOCSTRING-2026-05-18-3 | `isSheafy_ofStronglyNoetherianTate` (StructureSheaf:1618) | Signature still has `[IsDomain A]` despite docstring claiming "without IsDomain" | Statement mismatch; needs user decision (refactor empty-cover handling OR update docstring) |
| B2-tateAcyclicity_part2_gluing | `tateAcyclicity_part2_gluing_via_flat_descent` (Residuals:2109) | DEGENERATE WRAPPER — body calls `rationalCovering_hasGluing` which calls back `tateAcyclicity.2` (the sorry) | Refactor: move into TateAcyclicityFinalAssembly with real body using `faithfullyFlat_descent_equalizer` |

### Mathlib gaps identified

1. **`AdicCompletion.isNoetherianRing`** (= Stacks tag 0316). Sub-development started in this session as `Adic spaces/AdicCompletionNoetherian.lean`. 5 sorry-bodied leaves; main result `AdicCompletion.isNoetherianRing` is the last leaf. Discharges E3 in one line + unblocks `presheafValue_pairOfDefinition_isNoetherian`. ~150 LOC.

2. **`MvPowerSeries.instIsNoetherianRing_fin`** (= Stacks tag 0306 in multivariate form). Mathlib's `Mathlib/RingTheory/PowerSeries/Ideal.lean:45` has explicit TODO: "Prove noetherianity of MvPowerSeries in finitely many variables." `PowerSeries.instIsNoetherianRing` (single var) exists. Sub-leaf L2 of the Stacks 0316 file provides this via iso `MvPowerSeries (Fin (n+1)) R ≃+* MvPowerSeries (Fin n) R⟦X⟧` + induction. ~60 LOC included in the Stacks 0316 plan.

3. **"Canonical rank-1 valuation on a complete non-archimedean Huber field"**. Needed by D12 sub-leaf D12.4 (when 𝔪 is non-open, lift the topology valuation from `A/𝔪` back to a Spa point). Mathlib has `Valued K Γ` typeclass and infrastructure for valued fields, but no construction "complete non-arch Huber field ⟹ canonical rank-1 valuation". May need project-internal development. ~30-50 LOC.

---

## Part II — Wave 1 + Wave 2 cluster findings

### Cluster D (Wedhorn 7.40-7.52) — 10 open leaves

**Top 3 risks**:
1. D12 missing `[CompleteSpace A]` (NEW B2).
2. D9 missing `[IsAdicComplete P.I P.A₀]` (NEW B2).
3. D2 hidden circularity through `mulArchimedean_valueGroup_of_analytic`.

**Sub-trees needed**:
- **D2 Route B** (~80-120 LOC, 4 sub-leaves) — pre-decompose to avoid circularity.
- **D9** (~80-100 LOC, 4 sub-leaves) — Chevalley extension; D9.3 hardest (`I·R' ≠ R'` for adjoined `t/s`).
- **D12** (~120-150 LOC, 7 sub-leaves) — includes potential mathlib gap D12.4.
- **D14.3** (~50 LOC) NEW SUB-LEMMA: enlarge ideal of definition to include top-nilp element. Should be standalone helper in `HuberRings.lean` next to `PairOfDefinition.adjoin`.

**Safe-to-pick-first** (Cluster D only):
1. D1 (~15 LOC, all infra present).
2. D14 (~60-80 LOC after D14.3 helper).
3. D8 forward direction only (~30 LOC, if downstream only needs forward).

**Cleanup candidate**: D6 is DEAD CODE (no callers; HasLocLiftPowerBounded uses D7 instead). Either delete or `@[deprecated "use D7"]`.

**Recommended beastmode order for D**:
Pre-flight: amend D9 + D12 signatures with the new B2 hypotheses (rule (b) — mathematically required). Rename D8 (already known-wrong name). Delete D6.
1. D1 → 2. D14 → 3. D9 → 4. D10 → 5. D5 → 6. D2 → 7. D7 → 8. D8 → 9. D12.

### Cluster F (Refinement-to-standard-cover + Lemma 8.34) — 12 leaves

**Status from Wave 1 (truncated in tool output; key findings)**:
- F-cluster covers Wedhorn pp 83-84 (Lemma 8.34 + Lemma 7.54)
- F5 question (drops IsDomain) needs resolution
- F2 scope-error: RESTATED form needs propagation through P3-P8
- F12 import-cycle needs file split (currently scaffolded in LaurentRefinement.lean which is upstream of Cor832; needs to move downstream)

**Pending decisions for F**:
- F5: re-add `[IsDomain A]` OR develop non-domain Laurent split argument?
- F12 location: move into `TateAcyclicityFinalAssembly.lean`?

### Cluster I+H — 7 leaves

**Top risks**:
1. I-2.3 non-unit non-domain Krull intersection FALSE (NEW B2, ℚ_p × ℚ_p counterexample).
2. H-2 hidden CompactSpace dependency (NEW B2).
3. I-1 typeclass plumbing (low risk, mathlib has the pieces).

**Out of scope confirmed**: H-3, H-4 (depend on excluded SpvAI cluster).

**Safe-to-pick-first**:
1. I-1 (~50-80 LOC, mathlib infra fully verified via `tensorEqLocusEquiv`).
2. H-1 (~80-120 LOC).
3. I-2 unit case only (~40 LOC; punt non-unit pending B2-I2.3 resolution).

**I-3 already done** — remove from board.

### Cluster A (top-level IsSheafy wrappers) — 3 leaves

**Critical finding**: A3 docstring/signature mismatch + literal sorry body + no delegation written.

**5 INDEPENDENT BREAKS in Path α discharge**:
1. A3 itself: literal `sorry`, no body.
2. A1 (only in-file delegation candidate): literal `sorry` on embedding side (line 1220).
3. A2 (parametric variant): inherits `tateAcyclicity` Parts 1+2 sorries.
4. `isSheafyComplete` (documented closure): `[sorryAx]` from I.1 + II.1 + II.2 inheritance.
5. `cor_8_32_clean_proof` route: blocked by `flat_over_base_tate` sorry (which CAN'T close on original route — `restrictionMap_isLocalization` is FALSE).
6. (Bonus) `tateAcyclicity_part2_gluing_via_flat_descent` (Residuals:2109) is DEGENERATE wrapper — calls back to the sorry it claims to discharge. Listed as II.2 "discharged leaf" but isn't.

**Hidden blocker** (silent): `hasLocLiftPowerBounded_of_stronglyNoetherianTate` (StructureSheaf:1326, B1 instance) is a literal sorry. Without this, every `presheafValue`-using statement in the post-section A3 namespace fails to elaborate (the namespace is OUTSIDE the original `variable [HasLocLiftPowerBounded A]` block).

**Required user decision (Ticket 0)**: A3 `[IsDomain A]` stays or goes?

### Cluster B+C — 10 leaves

**Status**:
- `TateAlgebra.faithfullyFlat_general` IS AXIOM-CLEAN (Path α pillar is solid).
- `Spa.comap_of_continuousRingHom_continuous` is AXIOM-CLEAN.
- C1's discharge in `AuditCleanWrappers` is STRUCTURALLY INCOMPATIBLE — delegates to `productRestriction_faithfullyFlat_tate_of_hSpa_points` which requires deleted wrong-shaped B5 + sorry'd `hSpa_surj_from_spanTop`.
- `hSpa_surj_from_spanTop` contains explicit CIRCULARITY WARNING preventing C2 discharge.

**Recommended fix sequence**:
1. Write fresh `cor_8_32_clean_via_laurent` combinator in `TateAcyclicityFinalAssembly.lean` that takes `(laurent_witness)` parameter and uses `flat_over_base_tate_laurent` (the Wedhorn-honest alternative) + `productRestriction_faithfullyFlat_abstract`.
2. Refactor `tateAcyclicity` Parts 1+2 OUT of `LaurentRefinement.lean` into `TateAcyclicityFinalAssembly.lean` (structural, no math).
3. Wire `tateAcyclicity.1` via `productRestriction_injective_tate_of_hSpa_points` (now reachable).
4. Wire `tateAcyclicity.2` via `faithfullyFlat_descent_equalizer` (StructureSheaf:1409, axiom-clean modulo Stacks 023N cocycle kernel).

### Cluster E+K+L — 8 leaves

**Cluster L verdict** (definitive): **REPLACEMENT EXISTS — no Path α hole**.

| Old (deleted) | New (PROVED, axiom-clean) | File:line |
|---------------|---------------------------|-----------|
| L1 Wedhorn 8.31(1) | `TateAlgebra.faithfullyFlat_general` | `TateAlgebra.lean:2625-2629` |
| L2 Wedhorn 8.31(2)- | `TateAlgebra.flat_quotient_fSubX_general` | `TateAlgebra.lean:2597-2604` |
| L3 Wedhorn 8.31(2)+ | `TateAlgebra.flat_quotient_oneSubfX_general` | `TateAlgebra.lean:2607-2614` |

All three take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` — exactly Path α signature. Live consumers:
- `StructureSheaf.lean:930` (`presheafValue_flat_of_tateQuotient`).
- `StructureSheaf.lean:980` (`presheafValue_flat_of_canonical`).
- `RestrictionFlatness.lean:526`.
- `LaurentCoverExact.lean:39` (docstring reference).

**Do NOT re-introduce L1/L2/L3 wrappers.** The L cluster is correctly handled.

**Cluster E status**:
- E1 FALSE-AS-STATED, body sorried. Stage 2 cascade (restate + migrate 4-5 consumers) is **BLOCKING**. The current `_sub_lemma_L3_1b_fg_submodule_closed` and `_sub_lemma_L4_3_strict_via_closed_image` are unsound because they `inferInstance`-invoke E1. **HIGH RISK** for beastmode.
- E2 statement now TRUE (Stage 1 tightening added `[T2Space M^{τ'}]` + `[ContinuousSMul A M^{τ'}]`). Discharge is ~25 LOC wrapper around `L4.4`. **LOW RISK**.
- E3 unblocked by `AdicCompletionNoetherian.lean` (this session). Body becomes 1 line `exact AdicCompletion.isNoetherianRing _`. **CONFIRMED**.
- E4 NOT ~40 LOC — depends on (now fixed) L5.1.1 ring iso. Real LOC ~250. **MEDIUM-HIGH risk**, was previously hidden.

**Cluster K status**:
- K1: depends on D10 → D9. Need parametric restatement to take `(P, [IsAdicComplete P.I P.A₀])`.
- K2: depends on D7 → {D5, C3}. Full chain ~300+ LOC. Do NOT pick K2 standalone.

---

## Part III — Cross-cluster dependency graph (post-Session 26)

```
                            isSheafy_ofStronglyNoetherianTate (A3)
                                          ↓
                          ┌───────────────┼───────────────┐
                          ↓               ↓               ↓
                          A1              A2              isSheafyComplete (Residuals:2373)
                          │               │               │
                          ↓               ↓               ↓
                ┌────[embedding]──────────┴───────────────┴──┐
                │                                            │
                B6 productRestrictionSub_isInducing          B7 separation + B8 gluing
                │                                            │
                ↓                                            ↓
                F4 (P8: ratio-tree)                          C2 cor_8_32_clean (BLOCKED on import cycle)
                │                                            │
                ↓                                            ↓
              F7+F8+F9+F10                          C1 prop_8_30_flat_clean
                                                            │
                                                  ┌─────────┼─────────┐
                                                  ↓         ↓         ↓
                                          (L replacement chain — all PROVED ✓)
                                          TateAlgebra.faithfullyFlat_general
                                          TateAlgebra.flat_quotient_fSubX_general
                                          TateAlgebra.flat_quotient_oneSubfX_general

  presheafValue_pairOfDefinition_isNoetherian (PresheafTateStructure:930)
                            ↓
                            E3 = AdicCompletion.isNoetherianRing
                            ↓
                            (Stacks 0316 sub-dev: 5 leaves in new file ✓ created)
                                          ↓
                            ┌─────────────┴─────────────┐
                            ↓                           ↓
                MvPowerSeries.instIsNoetherianRing_fin   mvPowerSeriesEval + surjective
                (L2 — covers mathlib TODO)               (L3 + L4 workhorses)

Wedhorn 7.40-7.52 (Cluster D):
  D1 → (independent)
  D2 → D5 → D7 → {K2, D8} → (B1)
  D9 → D10 → {K1, B5 cover-level}
  D14 (needs D14.3 helper)

Cluster I:
  I-1 (mathlib infra clean) → tateAcyclicity.2 via Stacks 023N
  I-2 (unit case only; non-unit blocked on I-2.3 B2)
  I-3 done

Cluster H:
  H-1 → H-2 (after CompactSpace hypothesis added)
  H-3, H-4 OUT OF SCOPE
```

**No circularities detected** in the graph above. The "Path α discharge" of A3 has 5 INDEPENDENT BREAKS that need to be repaired in this order:
1. (PRE) Decide A3 IsDomain status.
2. (PRE) Add hypothesis fixes to D9 + D12 + H-2 + I-2.
3. Write `cor_8_32_clean_via_laurent` combinator in TateAcyclicityFinalAssembly.
4. Refactor `tateAcyclicity` Parts 1+2 out of LaurentRefinement.
5. Discharge L5.1.1 (now honest sorry; ~80 LOC).

---

## Part IV — Pre-flight checklist for /beastmode

**MUST be done before /beastmode runs** (otherwise B2-stop or wasted cycles):

### A. Signature corrections (rule (b) — mathematically required)

- [ ] **D9**: amend `exists_valuationSubring_dominating_for_rationalOpen` to add `[IsAdicComplete P.I P.A₀]`.
- [ ] **D12**: amend `exists_spa_point_supp_eq_maxIdeal_of_complete` to add `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]`.
- [ ] **H-2**: amend `exists_dominating_unit_noHArch_finset` to take `(hSpa_compact : CompactSpace ↥(Spa A A⁺))` explicitly.
- [ ] **I-2**: either re-add `[IsDomain A]` to `laurentCover_exact_general` OR case-split on `IsUnit f`.

### B. Cleanup

- [ ] **D6**: delete or `@[deprecated "use D7"]` (DEAD CODE).
- [ ] **D8**: rename to remove the `wedhorn_7_42_` prefix (acknowledged-wrong citation).
- [ ] **I-3**: remove from ticket board (already DONE).
- [ ] **H-3, H-4**: confirm out-of-scope, do not pick.

### C. Decisions from user (Session 26, 2026-05-18 — RESOLVED)

- [x] **A3 `[IsDomain A]`**: KEEP. Matches A1; A3 becomes a delegating wrapper over A1. Docstring at StructureSheaf:1605-1624 updated to reflect.
- [x] **F5 `[IsDomain A]`**: KEEP. Same rationale as A3. B2 entry F5-S22-AUDIT downgraded — non-domain case is not in scope.
- [x] **F12 location**: MOVE `tateAcyclicity` Parts 1+2 out of `LaurentRefinement.lean` into `TateAcyclicityFinalAssembly.lean`. (Execution pending; structural refactor, no math.)
- [x] **C3 Spa.comap framework**: BUILD NOW (~500 LOC sub-development). Unblocks B1. (Execution pending; planning in expert-review brief.)
- [x] **D12.4 canonical Huber-field valuation**: → EXPERT REVIEW (Session 26 brief — see REVIEW_BRIEF.md).

### D. Code edits already applied this session

- [x] **L5.1.1 placeholder fixed** — was `∃ e : X ≃+* X, e = e := ⟨RingEquiv.refl _, rfl⟩`; rewritten to honest sorry stating `TateAlgebra A ≃+* base change of P.A₀[X]^∧`.
- [x] **Stacks 0316 skeleton created** — `Adic spaces/AdicCompletionNoetherian.lean` with 5 leaves (compiles, sorries only). Added to root import.
- [x] **b2_log.jsonl updated** — 7 new entries (D12, D9, I-2.3, H-2, L5.1.1, A3-DOCSTRING, II.2-DEGENERATE).

---

## Part V — Recommended /beastmode ticket order

After pre-flight items A-C are done, /beastmode can work the following ticket order without hitting blocks:

### Tier 1: Foundational (no inter-cluster dependencies)

1. **T-STACKS-0316-L2-PROVE** — `MvPowerSeries.instIsNoetherianRing_fin` via iso + induction (~60 LOC). [`AdicCompletionNoetherian.lean:97`]
2. **T-STACKS-0316-L3** — `AdicCompletion.mvPowerSeriesEval` constructor (~40 LOC). [`AdicCompletionNoetherian.lean:124`]
3. **T-STACKS-0316-L4** — surjectivity workhorse (~50 LOC). [`AdicCompletionNoetherian.lean:142`]
4. **T-STACKS-0316-MAIN** — `AdicCompletion.isNoetherianRing` assembly (~10 LOC). [`AdicCompletionNoetherian.lean:169`]
5. **T-E3-DISCHARGE** — one-line `exact AdicCompletion.isNoetherianRing _` in `_sub_lemma_L5_1_2_adicCompletion_noetherian`. [`WedhornStronglyNoetherian.lean:128`]
6. **T-D1** — `exists_topNilp_ne_zero_of_analytic` (~15 LOC, all mathlib infra). [`Presheaf.lean`]
7. **T-D14.3-HELPER** — new sub-lemma `enlarge_definitionIdeal_to_include_topNilp` (~50 LOC) in `HuberRings.lean`.
8. **T-D14** — `topologicallyNilpotent_eq_union_definitionIdeals` (~10 LOC after T-D14.3). [`Presheaf.lean:2401`]
9. **T-I-3-REMOVE** — remove I-3 from board (already DONE).
10. **T-D6-CLEANUP** — delete dead-code D6.

### Tier 2: Cluster-internal chains (after Tier 1)

11. **T-D9** (~80-100 LOC, with `[IsAdicComplete P.I P.A₀]` added per pre-flight). [`Presheaf.lean:2253`]
12. **T-D10** (~30-50 LOC after T-D9). [`Presheaf.lean:2325`]
13. **T-K1** (~80 LOC after T-D10 + parametric restatement).
14. **T-D2-ROUTE-B** sub-tree (4 sub-leaves, ~80-120 LOC). [`Presheaf.lean`]
15. **T-D5** (~50 LOC after T-D2). [`Presheaf.lean`]
16. **T-D7** (~30 LOC after T-D5). [`Presheaf.lean:2898`]
17. **T-K2** (~80 LOC after T-D7). [`Presheaf.lean:1035`]
18. **T-D8** forward direction (~30 LOC). Rename in pre-flight. [`Presheaf.lean`]
19. **T-D12** sub-tree (7 sub-leaves, ~120-150 LOC, with completeness hypothesis added). [`Presheaf.lean:2360`]

### Tier 3: Stacks 023N + Cor 8.32 + Laurent (architectural changes)

20. **T-I-1** — `faithfullyFlat_cocycle_kernel_eq_algebraMap_range` (~50-80 LOC via `tensorEqLocusEquiv`). [`StructureSheaf.lean:1398`]
21. **T-COR832-CLEAN-LAURENT** — write new `cor_8_32_clean_via_laurent` combinator in `TateAcyclicityFinalAssembly.lean`. Takes laurent_witness, uses `flat_over_base_tate_laurent` + `productRestriction_faithfullyFlat_abstract`. (~80 LOC)
22. **T-TATEACYC-REFACTOR** — move `tateAcyclicity` Parts 1+2 out of `LaurentRefinement.lean` into `TateAcyclicityFinalAssembly.lean`. Structural, no math. (~100 LOC diff)
23. **T-TATEACYC-PART-1** — discharge `tateAcyclicity.1` via `productRestriction_injective_tate_of_hSpa_points` (now reachable). (~30 LOC)
24. **T-TATEACYC-PART-2** — discharge `tateAcyclicity.2` via Stacks 023N descent + I-1. (~50 LOC)

### Tier 4: F-cluster (refinement tree)

25. **T-F2-RESTATED-PROPAGATE** — propagate F2-RESTATED through F3 → F1 + P3-P8 chain. (~200 LOC)
26. **T-F7** (~120 LOC after T-H2-COMPACT-FIX).
27. **T-F8** (~100 LOC).
28. **T-F9** (~150 LOC).
29. **T-F10** (~80 LOC).
30. **T-F4** (~30 LOC composition after F7-F10).
31. **T-F11** (~30 LOC after T-F4).
32. **T-F5** (decision pending — IsDomain stays or goes).
33. **T-F12** (move into TateAcyclicityFinalAssembly per refactor; ~80 LOC).

### Tier 5: B-cluster, A-cluster, final assembly

34. **T-C1-DISCHARGE** — `prop_8_30_flat_clean` via `TateAlgebra.faithfullyFlat_general` + `flat_quotient_fSubX_general` + composition. (~80 LOC)
35. **T-C2-DISCHARGE** — `cor_8_32_clean` via T-COR832-CLEAN-LAURENT. (~20 LOC composition)
36. **T-B5-CONSUMER-MIGRATION** — retrofit consumers from wrong-shaped B5 onto `hSpa_surj_cover_level`. (~50 LOC across files)
37. **T-B1-DISCHARGE** — `hasLocLiftPowerBounded_of_stronglyNoetherianTate` instance via C3 + D8. (~50 LOC after C3 done)
38. **T-C3-SPA-COMAP** — if user opts to build (multi-session, ~500 LOC).
39. **T-C4, T-C5** — Example 6.38 cleanup (~10 LOC each).
40. **T-B6-CLOSE** — `productRestrictionSub_isInducing_tate` (~30 LOC after T-F4).
41. **T-B7-CLOSE** — `tateAcyclicity_separation_via_cor832` (~20 LOC after T-C2).
42. **T-B8-CLOSE** — `tateAcyclicity_gluing_via_descent` (~50 LOC after T-I-1 + T-TATEACYC-PART-2).
43. **T-PRESHEAFVALUE-PAIR-NOETH** — discharge `presheafValue_pairOfDefinition_isNoetherian` (~30-50 LOC after T-STACKS-0316-MAIN).
44. **T-A1-EMBEDDING-CLOSE** — discharge A1's embedding sorry via T-F4 + T286 chain. (~30 LOC)
45. **T-A1-GLUING-CLOSE** — discharge A1's gluing via T-TATEACYC-PART-2 (already done in Tier 3).
46. **T-A2-CLOSE** — A2 via T-A1 inheritance. (~5 LOC)
47. **T-A3-CLOSE** — A3 via direct `exact A1 P` or via `isSheafyComplete` (depends on A3 IsDomain decision).

### Tier 6: Cluster E remaining

48. **T-E1-CASCADE** — Stage 2 cascade for E1 (~80 LOC + 4-5 consumer migrations).
49. **T-E2-DISCHARGE** — wedhorn_6_18_unique via L4.4 wrapper + SigmaCompactSpace adapter (~25 LOC).
50. **T-E4-FULL** — inductive step via T-L5.1.1 + T-E3 + Hilbert basis (~250 LOC, NOT ~40).
51. **T-L5.1.1-DISCHARGE** — TateAlgebra ↔ adic completion of polynomial extension (~80 LOC).

### Tier 7: Cleanup + final pass

52. CLEANUP tickets per cadence rule.
53. T-CLEANUP-FINAL.

---

## Part VI — Per-cluster sub-tree decompositions

### Sub-tree: Stacks 0316 (E3 / E4 / presheafValue_pairOfDefinition_isNoetherian)

```
AdicCompletion.isNoetherianRing                       [Stacks 0316, file:line AdicCompletionNoetherian.lean:169]
├── L1: pick generators of I                          [mathlib: IsNoetherianRing ⇒ Ideal.FG]
├── L2: MvPowerSeries.instIsNoetherianRing_fin        [Stacks 0306 multivariate, AdicCompletionNoetherian.lean:97]
│   ├── L2.1: MvPowerSeries.finSuccEquivPowerSeries   [project gap, ~30 LOC]
│   └── L2.2: induction on n                          [~30 LOC]
├── L3: mvPowerSeriesEval                             [project, AdicCompletionNoetherian.lean:124]
│   ├── L3.1: each formal monomial maps to I^|α|      [direct]
│   ├── L3.2: partial sums Cauchy in R̂                [adic convergence]
│   └── L3.3: ring hom structure (add, mul, 1)        [universal property]
├── L4: mvPowerSeriesEval_surjective                  [project, AdicCompletionNoetherian.lean:142]
│   ├── L4.1: I^k generated by deg-k monomials in fᵢ  [mathlib: Ideal.span_pow_eq]
│   └── L4.2: inductive Cauchy lifting                [~30 LOC]
└── L5: isNoetherianRing_of_surjective                [mathlib]
```

### Sub-tree: D9 (Chevalley extension for rational opens)

```
exists_valuationSubring_dominating_for_rationalOpen   [Presheaf.lean:2253, needs [IsAdicComplete P.I P.A₀] added]
├── D9.1: I + 𝔭₀ ≠ ⊤ (using IsAdicComplete + I·P.A₀ ⊂ Jacobson)
├── D9.2: standard Chevalley — extend (P.A₀)_{𝔭} to a valuation subring (R', 𝔪')
├── D9.3: adjoin t/s with sₘ ∉ 𝔪' (hardest — algebraic-independence-modulo-I)
└── D9.4: rationalOpen control — verify (V, 𝔪') ⊃ R'
```

### Sub-tree: D12 (trivial valuation lift, max ideal case)

```
exists_spa_point_supp_eq_maxIdeal_of_complete         [Presheaf.lean:2360, needs CompleteSpace added]
├── D12.1: 𝔪 closed in A                              [maxIdeal_isClosed_of_complete_huber]
├── D12.2: A/𝔪 topological field structure            [~25 LOC]
├── D12.3: A/𝔪 complete                               [~20 LOC, quotient of complete by closed]
├── D12.4: A/𝔪 = K is Huber-field; canonical rank-1 valuation v_K    [MATHLIB GAP, ~30-50 LOC]
├── D12.5: lift v_K to v : A → Γ_K, show continuity + A⁺ ≤ 1         [~30 LOC]
├── D12.6: supp(v) = 𝔪                                                [~10 LOC]
└── D12.7: special-case open 𝔪 (trivial-valuation lift)               [~10 LOC]
```

### Sub-tree: D14 (definition-ideal enlargement)

```
topologicallyNilpotent_eq_union_definitionIdeals      [Presheaf.lean:2401]
├── (⊇) already proved
├── D14.1: x ∈ A°° ⇒ IsPowerBounded x                 [Bounded.lean:188]
├── D14.2: enlarge A₀ via PairOfDefinition.adjoin     [HuberRings.lean:690]
└── D14.3: enlarge ideal of definition (NEW SUB-LEMMA, ~50 LOC)
    ├── D14.3.a: construct J := P.I + (⟨x, hx⟩)
    ├── D14.3.b: J is open
    ├── D14.3.c: J is FG
    ├── D14.3.d: J^n → 0 (uses Ideal.exists_pow_le_of_le_radical_of_fg)
    └── D14.3.e: bundle into PairOfDefinition
```

### Sub-tree: D2 Route B (rank-one value group from analytic)

```
rankOne_valueGroup_of_analytic                        [Presheaf.lean]
├── D2.1: analytic ⇒ exists topnilp non-zero (= D1)
├── D2.2: topnilp + valuation continuous ⇒ value lies in (0,1)
├── D2.3: dichotomy: if value group has element of order > 1 ⇒ rank ≥ 1
└── D2.4: rank ≥ 1 + non-trivial valuation ⇒ rank = 1
   (Hahn embedding / microbiality reasoning)
```

---

## Part VII — Files modified this session

| File | Change | Reason |
|------|--------|--------|
| `Adic spaces.lean` | +1 import line | Added `AdicCompletionNoetherian` |
| `Adic spaces/AdicCompletionNoetherian.lean` | NEW FILE (170 lines, 5 sorries) | Stacks 0316 skeleton |
| `Adic spaces/WedhornStronglyNoetherian.lean` | L5.1.1 rewritten | Placeholder violation FIX |
| `.mathlib-quality/b2_log.jsonl` | +7 entries | New B2 candidates from waves |
| `.mathlib-quality/adversarial-audit-2026-05-18-3.md` | NEW FILE (this document) | Master audit |

Build verification: both modified `.lean` files compile cleanly (sorries only, no type errors). Verified via `lake env lean` 2026-05-18.

---

## Part VIII — What's NOT in this audit

- **Cluster G3** (`isClosed_setOf_mul_eq_zero`): general topology, low risk; ~5 LOC mathlib composition. Not adversarially reviewed.
- **N1-N4 honest sorries** (Session 21 post-deletion): covered partly via Cluster A's review of `flat_over_base_tate`. N3, N4 (LaurentRefinement) discharge via T-TATEACYC-REFACTOR + T-TATEACYC-PART-1/2.
- **Scottish Book, FarguesFontaine, Tilting, PerfectoidRing, SpvAITopology, CharacteristicSubgroup**: explicitly out of scope per `feedback_scope_tate_acyclicity.md`.
- **F-cluster detailed per-leaf review**: Wave 1 agent output truncated. Headlines captured; per-leaf detail pending (Wave 3 if needed).
- **C3 Spa.comap framework decomposition**: noted as API gap; not yet sub-decomposed.

---

## Closing

This session ran 6 parallel adversarial agents across 9 clusters (D, F, I+H, A, B+C, E+K+L), found 7 new B2 candidates, FIXED 1 placeholder violation, CREATED the Stacks 0316 skeleton (compiling), and produced this master audit document plus the recommended 53-ticket /beastmode order.

**Bottom-line readiness verdict for /beastmode**:
- **Cluster L**: ✓ CLEAR (replacements exist, no Path α hole).
- **Stacks 0316 sub-development**: ✓ READY (skeleton compiles).
- **Tier 1 tickets (foundational)**: ✓ READY pre-flight A is done.
- **Tier 2-7 tickets**: blocked on pre-flight items A, B, C above.
- **A3 final discharge**: blocked on pre-flight C (IsDomain decision) + Tier 3 architectural changes (cor_8_32_clean_via_laurent + tateAcyclicity refactor).

Recommended next action: user reviews the **Pre-flight checklist (Part IV)** and decides on the open questions, then `/beastmode` can begin from Tier 1.
