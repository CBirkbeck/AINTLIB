# Development Plan: Wedhorn Theorem 8.28(b) via the Čech-acyclicity route

**Target**: make `ValuationSpectrum.isSheafy_ofStronglyNoetherianTate_clean`
(`Adic spaces/WedhornCechAcyclicity.lean`, line ~1710) sorry-free under the
Wedhorn-faithful signature:

```lean
theorem isSheafy_ofStronglyNoetherianTate_clean [IsDomain A]
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    [IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] :
    IsSheafy A
```

**No per-cover hypothesis leaks** (no `h_separation`, no explicit `P` parameter,
no `hZavyalov`, no `hArch` carried in as side input — every typeclass on the
signature is Wedhorn-textual).

## Supersession notice

This plan supersedes the 2026-04-16 Block-A / Block-B / Block-B.1 critical-
path plan (archived as `plan-block-A-B-archived-2026-05-28.md`). The old plan
targeted `tateAcyclicity` via the `laurentOverlapBridge_exists_compatible` →
`tateAcyclicity` Part-2 route, which required either the bivariate Example
6.38 primitive (T-OV-1, ~500 LOC) or the Bourbaki CA III §2.8 port. Both
remain valid alternative routes but are not the focus going forward.

The new route follows **Wedhorn's actual proof of Theorem 8.28(b)** more
faithfully: §8.3's Lemma 8.33 (2-cover acyclic) + Lemma 8.34 (ideal-gen
acyclic) + Lemma 7.54 (ideal-gen refinement) + Appendix A's Prop A.3 to
transfer acyclicity along refinements. The decomposition lives in
`Adic spaces/WedhornCechAcyclicity.lean` (74 declarations, committed at
`809b78e`).

## Top-down decomposition

```
isSheafy_ofStronglyNoetherianTate_clean
├── productRestrictionSub_isInducing_tate  (existing, axiom-clean, project)
└── every_rational_cover_is_OXAcyclic
    ├── exists_ideal_gen_refinement  (Wedhorn Lemma 7.54)
    │   ├── exists_standard_cover_refining  (existing project)
    │   └── rationalCovering_from_idealGenSet  (LEAF — combinatorics)
    ├── wedhorn_lemma_834  (Wedhorn Lemma 8.34, ideal-gen cover acyclic)
    │   ├── part_ii  (Cor 7.32 dominating unit + Laurent cover)
    │   │   ├── noCommonZero_of_idealGen  ✓ proved
    │   │   ├── cor_7_32_dominating_unit  ✓ composed (from 3 leaves)
    │   │   │   ├── exists_pair_with_A₀_subset_Aplus  (LEAF)
    │   │   │   ├── exists_pseudouniformizer_of_tate  (LEAF)
    │   │   │   └── mulArchimedean_valueGroup_of_stronglyNoetherianTate  (LEAF — Wedhorn 7.40(6))
    │   │   ├── laurent_cover_from_dominating_unit  (LEAF)
    │   │   └── unit_gen_restriction_of_dominating_laurent
    │   │       ├── index_selection_on_laurent_piece  (LEAF)
    │   │       ├── canonical_unit_of_pointwise_lower_bound  (LEAF)
    │   │       └── restricted_cover_construction  ✓ proved
    │   ├── part_iii  (ratio Laurent refines unit-gen)
    │   │   ├── unitGenerators_of_unitGenCover  ✓ proved
    │   │   ├── ratio_laurent_cover_of_units  (LEAF)
    │   │   ├── ratio_laurent_refines_unit_gen  (LEAF)
    │   │   └── wedhorn_lemma_834_part_iii body  (B2 — IsUnit lift wrong direction)
    │   ├── part_i  (Laurent acyclic, induction)
    │   │   ├── part_i_base  (empty case)
    │   │   │   ├── laurent_empty_gen_eq_one  ✓ proved
    │   │   │   ├── single_unit_piece_of_empty_laurent  ✓ proved
    │   │   │   └── isOXAcyclic_of_single_unit_piece
    │   │   │       ├── isOXAcyclic_of_single_unit_piece_separation  (LEAF)
    │   │   │       └── isOXAcyclic_of_single_unit_piece_gluing  (LEAF)
    │   │   ├── part_i_step  (inductive, via Prop A.3(3))
    │   │   │   ├── laurent_cons_decomp_as_product  (LEAF)
    │   │   │   └── propA3_part3_bridge_for_laurent_product  (LEAF)
    │   │   └── part_i_laurent_restriction_acyclic
    │   │       └── laurent_restriction_isLaurent  (LEAF)
    │   ├── part_iv  (Prop A.3(1) composition)
    │   │   ├── wedhorn_lemma_834_C_restr_acyclic  (forward-ref to A.3(2) bridge)
    │   │   ├── wedhorn_lemma_834_V_restr_acyclic  ✓ proved
    │   │   ├── wedhorn_lemma_834_propA3_part1_separation  (LEAF — cast plumbing)
    │   │   ├── wedhorn_lemma_834_propA3_part1_gluing  (LEAF — cast plumbing)
    │   │   └── wedhorn_lemma_834 body  (composition, currently sorry)
    │   └── wedhorn_lemma_833  (Wedhorn Lemma 8.33, 2-cover acyclic)
    │       ├── wedhorn_lemma_833_separation_as_field  ✓ proved
    │       │   └── injectivity_from_faithfullyFlat_2cover  (LEAF — Pi.algebra plumbing)
    │       │       └── cor_8_32_for_2cover  ✓ proved (wraps project's cor_8_32_clean_proof)
    │       └── wedhorn_lemma_833_diagram_chase
    │           ├── wedhorn_lemma_833_example_638_plus  ✓ composed
    │           │   ├── example_638_plus_side_complete  ✓ proved
    │           │   ├── example_638_plus_side_noeth_pairSubring  (LEAF — Wedhorn 6.18)
    │           │   ├── example_638_plus_side_cont_evalHom  (LEAF — evalHom continuity)
    │           │   └── example_638_plus_side_cont_quotient_lift  (LEAF — quotient topology)
    │           ├── wedhorn_lemma_833_example_638_minus  ✓ composed
    │           │   ├── example_638_minus_side_cont_underlying_evalHom  (LEAF)
    │           │   └── example_638_minus_side_cont_quotient_lift  (LEAF)
    │           ├── wedhorn_lemma_833_example_639_intersection  (placeholder — see below)
    │           ├── wedhorn_lemma_833_gluing_as_field  (LEAF — 5-lemma composition)
    │           │   ├── laurentRationalCover_pieces_identified  ✓ proved
    │           │   └── compatible_pair_lifts_via_5lemma  (LEAF — 5-lemma core)
    │           └── 5-lemma row-2/3 sub-lemmas (currently `True` placeholders, see below)
    └── IsOXAcyclic_of_refining_acyclic_cover  (Prop A.3(2) project bridge)
        ├── propA3_part2_project_separation  (LEAF — cast plumbing)
        ├── propA3_part2_project_gluing  (LEAF — cast plumbing)
        ├── double_restriction_acyclicity  ✓ composed
        │   └── restricted_cover_inherits_IsGeneratedBy  (LEAF — B2 candidate)
        ├── RationalCovering.toFiniteCover  (LEAF — B2 candidate, signature wrong)
        ├── RationalCovering.toRefinement  (LEAF)
        └── IsOXAcyclic_iff_IsAcyclic  (placeholder, currently `True`)
```

## Sorry inventory (33 in WedhornCechAcyclicity.lean as of 2026-05-28)

Categorised by discharge strategy:

### Cat. A — Wedhorn-text leaves (substantive math, each is its own ticket)

| Leaf | Wedhorn reference | LOC est. (source line count) |
|---|---|---|
| `injectivity_from_faithfullyFlat_2cover` | Pi.algebra plumbing for Cor 8.32 | ~30 |
| `example_638_plus_side_noeth_pairSubring` | Wedhorn 6.18 (noeth pair-subring) | ~80 |
| `example_638_plus_side_cont_evalHom` | evalHomBounded continuity (via completion) | ~60 |
| `example_638_plus_side_cont_quotient_lift` | universal property of quotient topology | ~15 |
| `example_638_minus_side_cont_underlying_evalHom` | parallel to plus branch | ~60 |
| `example_638_minus_side_cont_quotient_lift` | parallel to plus branch | ~15 |
| `exists_pair_with_A₀_subset_Aplus` | smallest A₀ inside A⁺ | ~40 |
| `exists_pseudouniformizer_of_tate` | π generates I, top.nilp unit | ~50 |
| `mulArchimedean_valueGroup_of_stronglyNoetherianTate` | Wedhorn 7.40(6) (analytic ⇒ height ≤ 1) | ~150 |
| `compatible_pair_lifts_via_5lemma` | Wedhorn p. 84 5-lemma | ~120 |
| `wedhorn_lemma_833_gluing_as_field` | composes 5-lemma + pieces ID | ~40 |

### Cat. B — Construction sub-lemmas (project-side combinatorics)

| Leaf | Content | LOC est. |
|---|---|---|
| `laurent_cover_from_dominating_unit` | build Laurent cover from `s⁻¹·T` | ~80 |
| `laurent_cons_decomp_as_product` | `𝒱_{f::gs}` as 𝒰_f × 𝒱_gs | ~100 |
| `laurent_restriction_isLaurent` | restriction of Laurent is Laurent | ~80 |
| `ratio_laurent_cover_of_units` | ratio Laurent from finite unit set | ~60 |
| `ratio_laurent_refines_unit_gen` | σ-walk → refinement | ~120 |
| `index_selection_on_laurent_piece` | σ-walk selects t_{i_max} | ~60 |
| `canonical_unit_of_pointwise_lower_bound` | v(t) ≥ v(s) on V_j ⇒ canonical image is unit | ~40 |
| `unit_gen_restriction_of_dominating_laurent` | composition of (a)+(b)+(c) above | ~40 |
| `rationalCovering_from_idealGenSet` | build cover from ideal-spanning Finset | ~80 |

### Cat. C — Cast plumbing (`C'.base = C.base` type equality)

| Leaf | Issue | LOC est. |
|---|---|---|
| `propA3_part2_project_separation` | `Eq.rec` cast through restrictionMap | ~30 |
| `propA3_part2_project_gluing` | parallel to separation | ~40 |
| `wedhorn_lemma_834_propA3_part1_separation` | similar cast for Prop A.3(1) | ~30 |
| `wedhorn_lemma_834_propA3_part1_gluing` | similar | ~40 |

Could be discharged collectively via a `RationalCovering.changeBase` helper
that internalises the cast.

### Cat. D — Single-piece base case

| Leaf | Content | LOC est. |
|---|---|---|
| `isOXAcyclic_of_single_unit_piece_separation` | single piece R({1}/1) ⇒ identity restriction | ~25 |
| `isOXAcyclic_of_single_unit_piece_gluing` | parallel | ~25 |

### Cat. E — Project-to-abstract Čech bridges

| Leaf | Content | LOC est. |
|---|---|---|
| `RationalCovering.toFiniteCover` | **B2: signature targets all of Spa A A⁺, not C.base's rational subset** | ~50 (after fix) |
| `RationalCovering.toRefinement` | refinement-to-Refinement | ~30 |
| `restricted_cover_inherits_IsGeneratedBy` | **B2: requires \|E.covers\| = \|T\| bijection** | needs restate |

### Cat. F — Forward-reference compositions

| Leaf | Issue |
|---|---|
| `wedhorn_lemma_834_C_restr_acyclic` body | wants `IsOXAcyclic_of_refining_acyclic_cover` (defined later) |
| `wedhorn_lemma_834` body | same forward-ref + plumbing |

Fix: reorder file so Prop A.3(2) project bridge is defined before Lemma 8.34.

### Cat. G — B2-suspected statements

| Leaf | Issue |
|---|---|
| `wedhorn_lemma_834_part_iii_unit_gen_refines_to_laurent` body | Wedhorn requires lifting `IsUnit (canonicalMap f)` to `f ∈ A^×`, which is the wrong direction. Needs reformulation: ratios should be at the 𝒪_X(C.base) level, not at the A level. |
| `propA3_part3_bridge_for_laurent_product` | V is unconstrained relative to Uf, Vgs_at; statement is too weak. |
| `wedhorn_lemma_833_example_639_intersection` | currently identity-iso placeholder; needs proper distinct R(T/s) for intersection piece + iso to A⟨ζ, ζ⁻¹⟩/(f-ζ). |

## Critical path

1. **Cat. C** (cast plumbing, ~140 LOC) — closes 4 sorries directly + unlocks
   IsOXAcyclic_of_refining_acyclic_cover and wedhorn_lemma_834_propA3_part1_bridge.
2. **Cat. F** (file reorder, ~10 LOC) — closes 2 sorries (forward-ref).
3. **Cat. D** (single-piece, ~50 LOC) — closes 2 sorries.
4. **Cat. E.1 + Cat. G.1** (B2 fixes, ~80 LOC restate) — RationalCovering.toFiniteCover
   signature + part_iii reformulation.
5. **Cat. B** (combinatorics, ~700 LOC) — substantive but mechanical.
6. **Cat. A** (Wedhorn-text, ~660 LOC) — substantive math, each is its own
   focused effort.

## Risk

- **Cat. A**'s leaves (Wedhorn 6.18, 7.40(6), 5-lemma) are each multi-session
  efforts. The 5-lemma in particular needs new abstract infrastructure in
  `CechCohomology.lean` (or a project-side replacement).
- **Cat. E** B2 issues: the `RationalCovering.toFiniteCover` signature change
  may cascade through the project's abstract-Čech bridge.
- **Cat. G** B2 issues: the part_iii body needs `/develop --continue` re-plan;
  the bridge sub-lemma needs strengthened hypotheses tying V to Uf × Vgs_at.

## File structure

- `Adic spaces/WedhornCechAcyclicity.lean` (1671 lines, 74 decls, 33 sorries) —
  the main file; all new tickets target this.
- `Adic spaces/CechCohomology.lean` (1400 lines, 7 sorries) — abstract Čech
  framework. Some sorries here will be co-discharged with Cat. A leaves
  (5-lemma) and Cat. E bridges.
- `Adic spaces/Example638.lean` (1647 lines, 0 sorry) — generic Example 6.38
  equivs; consumed by Cat. A's continuity leaves.

## State document provenance

This file regenerated 2026-05-28 from direct inspection of
`WedhornCechAcyclicity.lean` (committed at 809b78e). Supersedes
`plan-block-A-B-archived-2026-05-28.md`.
