# Critical-Path Plan for `isSheafy_ofStronglyNoetherianTate` (post-audit 2026-05-21)

## Audit motivation

A prior session was burning effort on the Stacks 0316 chain (`AdicCompletion.isNoetherianRing`
and its 5 L3/L4 sub-leaves in `AdicCompletionNoetherian.lean`). Cross-check of
`docs/TATE-ACYCLICITY-WORK-PLAN.md` ("Sorry #9") and a grep for actual call-sites
revealed:

> "For Tate acyclicity in case (b) — strongly noetherian Tate — we explicitly
> assume `IsStronglyNoetherian A` which gives us `A⟨X⟩` noetherian as a
> hypothesis, so we might be able to bypass this entirely."

Confirmed: `presheafValue_pairOfDefinition_isNoetherian` has **zero call-sites in proof
bodies** (only docstring references). The 5 sorries in `AdicCompletionNoetherian.lean`
are **NOT critical-path** for IsSheafy and should be DEPRIORITIZED until needed
elsewhere.

This document collects the actually-critical sorries and their feasibility.

## Target

```
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A
```
at `Adic spaces/StructureSheaf.lean:1629`. ✓ Body is `isSheafy_ofStronglyNoetherianTate_flat A P` (one-line delegation).

## Critical chain (top-down)

### Tier 1 — `isSheafy_ofStronglyNoetherianTate_flat` (A1)

**Location**: `StructureSheaf.lean:1117`. Body is an `IsSheafy A` structure with:
- `embedding C := by ...` — **sorry at line 1220** (topological inducing residual)
- `gluing C f hcompat := rationalCovering_hasGluing P C f hcompat` — closed by delegation but consumer has sorries

**S1** (the embedding sorry, line 1220): Topological inducing of `productRestrictionSub A C`. Per A1's docstring + Sorry #10 of work-plan, closes via:
```
exact productRestrictionSub_isInducing_tate C  -- TateAcyclicityResiduals.lean
```
once T-LANE-C-induction lands.

### Tier 2 — `rationalCovering_hasGluing` / `rationalCovering_hasSeparation`

**Location**: `LaurentRefinement.lean:6036, 6070`. Both delegate to `tateAcyclicity` (line 5943).

**S2** `tateAcyclicity` Part 1 (separation, line 5967): zero-kernel form.
**S3** `tateAcyclicity` Part 2 (gluing, line 6010): equalizer descent.

Per the docstring at line 5961-6008, both should ultimately delegate to wrappers in `TateAcyclicityResiduals.lean` to avoid an import cycle. Specifically:
- Part 1 → `tateAcyclicity_part1_separation_via_cor832` (already closed at TateAcyclicityResiduals:2088)
- Part 2 → `tateAcyclicity_part2_gluing_via_flat_descent` (already closed at TateAcyclicityResiduals:2110)

**The structural fix**: relocate `tateAcyclicity` from `LaurentRefinement.lean` to `TateAcyclicityFinalAssembly.lean` (the "F12 move" — task #85 pending). Once moved, `tateAcyclicity` can directly invoke the existing axiom-clean wrappers.

### Tier 3 — The Lane C / Laurent ratio tree chain (Wedhorn 8.34)

**S4** `productRestrictionSub_isInducing_tate` — `StructureSheaf.lean:1361`. Closed by S5 (one tactic call).

**S5** `productRestrictionSub_isInducing_via_ratio_tree` — `TateAcyclicityResiduals.lean:2464`. Consumes:
- T286 (Lane C single-step closer) ✓
- A `RatioLaurentTree` realization satisfying `Refines C` and `allSplitsInducing`

**S6** `exists_wedhorn_ratio_laurent_refinement_tree_realized` (P8) — `TateAcyclicityResiduals.lean:1830`. Assembly of:

**S6a** `exists_first_stage_laurent_tree_unit_generated` (P6/W2) — `TateAcyclicityResiduals.lean:1455`. Wedhorn 8.34 first-stage existence.

**S6b** `unitGeneratedCover_has_relative_ratioLaurentRefinement` (P5/W3) — `TateAcyclicityResiduals.lean:1508`. Wedhorn 8.34 ratio refinement existence.

**S6c** `relative_laurent_tree_to_absolute` (P4) — `TateAcyclicityResiduals.lean:1641`. Wedhorn 8.34(iii)+(i) transport.

**S6d** `exists_standard_cover_refining` (P7/W1) — `TateAcyclicityResiduals.lean:210`. Wedhorn 7.54 standard cover refinement.

### Tier 4 — Wedhorn 7.35 Spa quasi-compactness (no-hArch)

Used by `exists_first_stage_laurent_tree_unit_generated` (S6a) downstream via `exists_dominating_unit_noHArch`.

**S7** `isCompact_preimage_rationalOpen_noHArch` — `SpaCompactNoHArch.lean:257`. Wedhorn 7.35(2). Decomposed into A.1-A.6 already.

**S8** `Spa.proConstructible_in_SpvAI` — `SpaCompactNoHArch.lean:245`. Wedhorn 7.35(1). Constructible decomposition of `Spa A`.

### Tier 5 — Cor 8.32 chain (used by S2 separation via `tateAcyclicity_part1_separation_via_cor832`)

**S9** `prop_8_30_flat_clean` (C1) — `StructureSheaf.lean:1543`. Wedhorn 8.30 flat-restriction.

**S10** `_sub_lemma_C1_2_laurent_normalization_exists` (C1.2) — `StructureSheaf.lean:1882`. Rem 7.55 Laurent normalization.

**S11** `cor_8_32_clean` body — `StructureSheaf.lean:1565` (delegates to `cor_8_32_clean_via_flat` ✓). Cor 8.32 closes once C1 ✓ + B5' ✓ land.

**S12** `hSpa_surj_cover_level` (B5') — `StructureSheaf.lean:1466`. Cover-level Spec-surjectivity.

## Sorry inventory (critical-path only)

| # | Sorry | File:Line | Tier | Status / Closer |
|---|-------|-----------|------|----------------|
| S1 | A1 embedding | StructureSheaf:1220 | 1 | One line: `productRestrictionSub_isInducing_tate C` |
| S2 | tateAcyclicity Part 1 | LaurentRefinement:5967 | 2 | F12 move + delegate to part1_separation_via_cor832 ✓ |
| S3 | tateAcyclicity Part 2 | LaurentRefinement:6010 | 2 | F12 move + delegate to part2_gluing_via_flat_descent ✓ |
| S4 | productRestrictionSub_isInducing_tate | StructureSheaf:1361 | 3 | One line via S5 |
| S5 | productRestrictionSub_isInducing_via_ratio_tree | TateAcyclicityResiduals:2464 | 3 | Composes T286 ✓ + ratio tree |
| S6a | exists_first_stage_laurent_tree_unit_generated (P6/W2) | TateAcyclicityResiduals:1455 | 3 | Wedhorn 8.34, ~50 LOC |
| S6b | unitGeneratedCover_has_relative_ratioLaurentRefinement (P5/W3) | TateAcyclicityResiduals:1508 | 3 | Wedhorn 8.34, ~80 LOC |
| S6c | relative_laurent_tree_to_absolute (P4) | TateAcyclicityResiduals:1641 | 3 | Wedhorn 8.34(iii)+(i), ~60 LOC |
| S6d | exists_standard_cover_refining (P7/W1) | TateAcyclicityResiduals:210 | 3 | Wedhorn 7.54, ~80 LOC |
| S6 | exists_wedhorn_ratio_laurent_refinement_tree_realized (P8) | TateAcyclicityResiduals:1830 | 3 | Composes S6a–d, ~30 LOC |
| S7 | isCompact_preimage_rationalOpen_noHArch | SpaCompactNoHArch:257 | 4 | Wedhorn 7.35(2) via S8, ~40 LOC |
| S8 | Spa.proConstructible_in_SpvAI | SpaCompactNoHArch:245 | 4 | Wedhorn 7.35(1) constructible decomp, ~60 LOC |
| S9 | prop_8_30_flat_clean (C1) | StructureSheaf:1543 | 5 | Wedhorn 8.30, via C1.1–C1.4 + S10 |
| S10 | _sub_lemma_C1_2_laurent_normalization_exists | StructureSheaf:1882 | 5 | Rem 7.55, ~50 LOC |
| S12 | hSpa_surj_cover_level (B5') | StructureSheaf:1466 | 5 | Cover-level Spa, ~80 LOC |

**Total: 15 critical sorries.**

The "F12 move" (relocating `tateAcyclicity` from `LaurentRefinement.lean` to `TateAcyclicityFinalAssembly.lean`, task #85) is the structural unblocker for S2+S3.

## Deprioritized (NOT critical-path)

- `AdicCompletionNoetherian.lean` — 5 sorries (L3.A.compat, L3.B.map_one, L3.B.map_mul, L4.2, L4). Stacks 0316 development is bypassed by `IsStronglyNoetherian A` hypothesis.
- `presheafValue_pairOfDefinition_isNoetherian` — 0 actual call-sites.
- `_sub_lemma_L5_1_2_adicCompletion_noetherian` — delegated via S5.1.2 wrapper, not reached.

## Feasibility

**Tier 1 (S1)**: 1 line. Trivial once S4 lands.

**Tier 2 (S2, S3)**: Structural move (F12), no new math content. The downstream wrappers are already axiom-clean.

**Tier 3 (S4-S6 + sub-leaves)**: Wedhorn 8.34 chain. ~300 LOC across 6 leaves. The hardest is W3 (S6b) since it constructs the ratio refinement.

**Tier 4 (S7, S8)**: Wedhorn 7.35 Spa quasi-compactness. ~100 LOC. The proConstructible part (S8) is the substantive Stacks/Spa work.

**Tier 5 (S9-S12)**: Cor 8.32 chain. The flatness route via `restrictionMap_flat_via_iteratedMinus` ✓ already exists. S10 (Laurent normalization) is the substantive piece.

**Total honest estimate**: ~700-900 LOC of new substantive proof, spread across 5 tiers, ~15 leaves. Each leaf is ~30-100 LOC.

## Recommended order for /beastmode

1. **F12 move** (task #85): unblocks S2+S3 immediately (delegation to existing proven wrappers).
2. **S10 + S9**: Cor 8.32 chain via Laurent normalization. Largely composes existing infrastructure.
3. **S12** (B5' cover-level Spa-surjectivity): unblocks S5/S11.
4. **S6d** (W1/P7): Wedhorn 7.54. Substantive.
5. **S7, S8**: Wedhorn 7.35 chain.
6. **S6a, S6b, S6c, S6**: Laurent ratio tree assembly.
7. **S5**: Ratio tree → isInducing.
8. **S4**: One line.
9. **S1**: One line, closes A1 → A3 ✓.

## To run /develop --decompose

Suggested invocation: `/develop --decompose` targeting this plan. The decomposer should
generate sub-tickets for each tier's sub-leaves, with the Wedhorn references already
identified in the docstrings of the existing sorry-bodied declarations.
