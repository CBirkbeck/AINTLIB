# Plan: Option B — Inclusion-Exclusion Replacement for the (4.6.14) Sorry

**Date**: 2026-05-19
**Status**: planning-only (`/develop`)
**Strategy**: bypass the broken Miyake (4.6.14) Fourier-vanishing chain by
constructing the same-level prime decomposition `f = ∑_p f_p` via
inclusion-exclusion using same-level projection operators `P_p`.

## Goal

Currently `miyake_descent_l_prime_gt_one_helper` (the Miyake (4.6.14)
sorry at `SMOObligations.lean:6833`) is the M8 inductive step's
critical sub-lemma. The M8 chain produces the decomposition

```
f = ∑_{p ∈ S} f_p p,    f_p p ∈ cuspFormCharSpace k χ ∩ qSupportedOnDvdSubmodule N k p
```

via `miyake_4_6_8_subset_helper` (induction on `S.card`).

**Option B**: replace this inductive construction with a direct
**inclusion-exclusion** construction. The new construction does NOT
rely on the (4.6.14) Fourier-vanishing — it uses only the same-level
projection operators `P_p = V_p ∘ U_p` (where `U_p = heckeT_p_divN`,
`V_p = modularFormLevelRaise`).

## References

- **Expert review 2026-05-16** (`.mathlib-quality/expert-review/2026-05-16-SMO-obligations-plan/reply.md`):
  proposes inclusion-exclusion using `P_p = V_p U_p`.
- **Project's existing infrastructure** in
  `Eigenforms/AtkinLehnerProjection.lean:607`: the consumer
  `mainLemma_charSpace_of_finset_decomposition` accepts
  `f = ∑_{p ∈ N.primeFactors} f_p p` and produces `f ∈ cuspFormsOld N k`.
- **Diamond–Shurman, A First Course in Modular Forms, Ch. 5**: standard
  reference for the Hecke operators `U_p`, `V_p` and their commutation.

## High-Level Strategy

```
Existing route (broken):
  f ──[M3+M4+M7-sqfree+M6(2) chain]──> ∑_p f_p
                ↑
            sorry at line 6833 (Miyake 4.6.14)

Option B route (proposed):
  f ──[Inclusion-Exclusion via P_p = V_p U_p]──> ∑_T f_T (T ⊆ N.primeFactors)
                                              ──[reindex per Möbius]──> ∑_p f_p
```

The inclusion-exclusion construction works at the **q-expansion level**
first (where the identity is purely arithmetic), then upgrades to the
**form level** via `qExpansion_eq_zero_iff` at a common level.

## Mathlib Inventory

| Concept | Project Status | Action |
|---------|----------------|--------|
| `heckeT_p_divN` (U_p, same-level) | ✅ Exists (`HeckeT_p.lean`) | USE |
| `modularFormLevelRaise` (V_p, lifts level) | ✅ Exists (`LevelRaise.lean`) | USE |
| `qExpansion_one_heckeT_p_divN_coeff` | ✅ Exists | USE |
| `qExpansion_one_modularFormLevelRaise_coeff` | ✅ Exists | USE |
| Same-level `P_p` operator | ❌ Not in project | **DEFINE** |
| `P_p`'s q-expansion projection identity | ❌ Not in project | **PROVE** |
| `P_p` preserves `cuspFormCharSpace` | ❌ Not in project | **PROVE** |
| Inclusion-exclusion identity | ❌ Not in project | **PROVE** |
| Consumer `mainLemma_charSpace_of_finset_decomposition` | ✅ Exists | USE |

## File Structure (New Module)

Create new file `LeanModularForms/Eigenforms/InclusionExclusionDecomp.lean`:
- Section 1: `P_p` same-level operator definition + q-expansion identity.
- Section 2: `P_p` commutation lemmas (`P_p P_q = P_q P_p` at q-exp level).
- Section 3: Inclusion-exclusion identity for `f = ∑_T (-1)^{|T|+1} (∏_T P_p) f`.
- Section 4: Reindexing to per-prime decomposition `f = ∑_p f_p`.
- Section 5: Replacement of `miyake_4_6_8_main_lemma_cuspForm` consumer.

## Dependency Graph

```
heckeT_p_divN (U_p)          modularFormLevelRaise (V_p)
       │                              │
       └──────────┬───────────────────┘
                  ↓
            same-level P_p
                  │
                  ↓
          P_p commutation
                  │
                  ↓
       inclusion-exclusion (q-exp level)
                  │
                  ↓
      function-level upgrade via qExpansion_eq_zero_iff
                  │
                  ↓
       Reindex to f = ∑_p f_p
                  │
                  ↓
    mainLemma_charSpace_of_finset_decomposition  ──> f ∈ cuspFormsOld N k
```

## Generality Decisions

- **Same-level P_p**: defined for `p` prime with `p ∣ N` (matching `heckeT_p_divN`'s hypothesis).
- **Character preservation**: requires χ factors through `N/p` (otherwise the
  diamond-commutation between U_p and ⟨d⟩ doesn't give same-level P_p).
- **The decomposition is for `f` with `Coprime n N` Fourier vanishing**, not for
  arbitrary `f`. (Inclusion-exclusion requires the vanishing hypothesis.)

## Estimated Effort

| Section | LOC estimate | Risk |
|---------|--------------|------|
| 1. P_p def + q-exp identity | 100-150 LOC | Medium (extra-rep behavior under V_p) |
| 2. P_p commutation | 80-120 LOC | Low (q-exp level reasoning) |
| 3. Inclusion-exclusion identity | 100-150 LOC | Medium (Möbius / IE bookkeeping) |
| 4. Function-level upgrade | 80-100 LOC | Low (uses qExpansion_eq_zero_iff) |
| 5. Reindex + consumer composition | 50-80 LOC | Low |
| **Total** | **~500-700 LOC** | Medium |

## Risk Assessment

**Highest risk**: Section 1, the same-level P_p's q-expansion identity. The naive
composition `V_p (heckeT_p_divN f)` at level `Γ_1(N)` produces a form at level
`Γ_1(p·N)` (not Γ_1(N)). To get a same-level operator, we need either:
- (a) A character-equivariant restriction from Γ_1(p·N) back to Γ_1(N) using χ
  factoring through N/p.
- (b) A different construction (e.g., via the matrix `[[p,0;0,1]]` slash with
  appropriate normalization).

Option (a) requires the diamond-commutation between U_p and the character action,
which is standard but not formalized in the project.

Option (b) requires defining a new same-level slash operator that the project
doesn't have.

**Second risk**: the inclusion-exclusion identity. While straightforward at the
q-expansion level, upgrading to a form-level identity requires bundling at a
common level (`l'²·N` or similar) and applying `qExpansion_eq_zero_iff`. This
mirrors the level-management issues we already encountered in Option A.

**Third risk**: alignment with the existing `mainLemma_charSpace_of_finset_decomposition`
consumer. The consumer expects exactly the decomposition shape we'd produce, but
the f_p indexing might need re-shuffling (the IE gives `∑_T`, but the consumer
expects `∑_p`).

## Alternative Sub-strategies

**Sub-strategy B-Lite (same level via Φ_p)**: Instead of P_p = V_p U_p, use
P_p = V_p ∘ Φ_p where Φ_p is the descend slash sum (`miyake_hecke_descend`).
This composition naturally lands at level Γ_1(N) (since Φ_p: Γ_1(N) → Γ_1(N/p)
and V_p: Γ_1(N/p) → Γ_1(N)). The q-expansion identity then depends on the
Φ_p's q-exp formula.

**Status**: For V_p-lifted inputs, M5b gives the clean formula. For general
inputs, the formula has an extra-rep contribution (per audit note in
SMOObligations.lean:4157). For χ-eigen f with χ factoring through N/p, the
extra-rep should be controllable, but this needs a custom argument.

**Sub-strategy B-Direct (skip P_p, use Φ_p ∘ V_p directly)**: Construct each
f_p as `V_p (Φ_p f) - <appropriate corrections>`. This bypasses the same-level
P_p entirely, working at the function level throughout. The decomposition is
constructed iteratively, with character bookkeeping at each step.

## Decision Point

Given the risk and LOC estimate, this is a substantial undertaking. The user
should choose between:

1. **Full Option B**: ~500-700 LOC of new infrastructure.
2. **Sub-strategy B-Lite**: ~300-400 LOC, leveraging existing Φ_p (but inherits
   its extra-rep complexity).
3. **Sub-strategy B-Direct**: ~200-300 LOC, function-level throughout (less
   infrastructure, more local).
4. **Abandon Option B**: return to Option A (Miyake's 4.6.14 chain) and tackle
   the level mismatch via a different intermediate.

The next step is to run `/develop --decompose` on the chosen sub-strategy.
