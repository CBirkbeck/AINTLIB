# Tate Acyclicity Work Plan — bite-size sub-lemmas

**Target**: close Tate acyclicity (Wedhorn 8.28 strongly noetherian Tate case) + sheafy upgrade.

**Method**: every remaining sorry on the critical path is decomposed into atomic sub-lemmas. Each sub-lemma cites the exact Wedhorn step. We work the list bottom-up.

The 10 critical-path sorries identified by grep, in dependency order:

| # | File:Line | Name | Wedhorn ref |
|---|---|---|---|
| 1 | `SpaCompactNoHArch.lean:191` | `isCompact_rationalOpen_inter_vle_noHArch` | 7.30 + 7.32 + 7.35 |
| 2 | `TateAcyclicityResiduals.lean:218` | `exists_standard_cover_refining` (P7) | 7.54 |
| 3 | `TateAcyclicityResiduals.lean:1392` | P5 outer existence | 8.34(iii) |
| 4 | `TateAcyclicityResiduals.lean:1504` | P5 inner `refines` | 8.34(iii) leaf step |
| 5 | `TateAcyclicityResiduals.lean:1515` | P5 inner `allSplitsInducing` | Lane C inducing |
| 6 | `TateAcyclicityResiduals.lean:1632` | P4 W3-transport | 8.34(i)+(iii) compose |
| 7 | `TateAcyclicityResiduals.lean:1759` | P8 final assembly | 8.34(iv) |
| 8 | `TateAcyclicityResiduals.lean:1810` | I.1 legacy LaurentTree | typeclass-conditional |
| 9 | `TateAcyclicityResiduals.lean:2167` | `adicCompletion_noetherian` | Stacks 00MA (Mathlib gap) |
| 10 | `StructureSheaf.lean:1207` | IsSheafy topo-inducing | 8.34 topological |

Plus, on the unblocking chain for #1: the hArch dependency in `Cor732.lean:206` for use by P6 = `exists_first_stage_laurent_tree_unit_generated`.

---

## Sorry #1 — half-space compactness no-hArch

**Statement** (`SpaCompactNoHArch.lean:186`):
```lean
theorem isCompact_rationalOpen_inter_vle_noHArch
    (L : RationalLocData A) (g h : A) :
    IsCompact (Subtype.val ⁻¹'
      (rationalOpen L.T L.s ∩ {v | v.vle g h}) : Set ↥(Spa A A⁺))
```

**Wedhorn proof**: Combination of Theorem 7.35 (Spa is spectral, rational subsets are QC opens), the closedness of `{v(g) ≤ v(h)}` in Spv (continuous evaluation), and the spectral-space fact that QC-open ∩ closed is QC.

**Decomposition** (4 atomic sub-lemmas):

### 1.1 `Set.image_isClosed_vle` — half-space is closed in `Spv A`
```lean
theorem isClosed_setOf_vle (g h : A) :
    IsClosed { v : Spv A | v.vle g h }
```
**Wedhorn ref**: implicit in 7.8 (evaluation `Spv A → Γ` is continuous) + closedness of `{(x,y) | x ≤ y}` in `Γ × Γ`. **Project status**: needs to be stated.

### 1.2 `IsCompact.inter_closed_in_subtype` — generic topology fact
```lean
theorem IsCompact.inter_preimage_isClosed
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} (hS : IsCompact S) (f : Y → X) (hf : Continuous f)
    {C : Set X} (hC : IsClosed C) :
    IsCompact (f ⁻¹' (S ∩ C) ∩ f ⁻¹' Set.univ)
```
*Actually* this is just `IsCompact.inter_right` applied to `(f ⁻¹' S) ∩ (f ⁻¹' C)`. **Project status**: in Mathlib, just need to invoke.

### 1.3 `isCompact_preimage_rationalOpen_noHArch` — QC of rational opens, no hArch
```lean
theorem isCompact_preimage_rationalOpen_noHArch
    (L : RationalLocData A) :
    IsCompact (Subtype.val ⁻¹' rationalOpen L.T L.s : Set ↥(Spa A A⁺))
```
**Wedhorn ref**: Theorem 7.35(2). **Project status**: existing `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` at `SpaCompact.lean:586` requires `hArch`. The no-hArch version needs a different path. Two options:
- (a) Replace the bool encoding with a stronger one that doesn't need hArch.
- (b) Use `Spv(A,I)` spectrality (Wedhorn 7.5 + 7.35(1)) — Route 2 that I added signatures for.

This is **Sorry #1's actual content**. Decomposes into:

#### 1.3.a `Continuous.spv_eval_vle` — `fun v ↦ (v.vle g h)` is continuous to Prop
```lean
theorem Spv.vle_isClopen (g h : A) :
    IsClopen { v : Spv A | v.vle g h }
```
Actually `IsOpen` only — let me reconsider. The set `{v.vle g h}` may not be clopen, only closed. Drop this, use 1.1.

#### 1.3.b Route via existing `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer`, supplying `hArch` from a fact internal to the project.

This is where the chain branches:

**Branch B (Route 2 — Spv(A,I) spectral)**: depends on the Spv(A,I)-spectrality chain I added signatures for in `SpvAITopology.lean` lines 459–510 and `SpvAI.lean` lines 408–434.

**Branch C (direct cofinality bool encoding)**: a new bool-encoding that puts cofinality conditions as closed subsets of the Tychonoff cube. Needs a new lemma in `SpaCompact.lean`.

### 1.4 Sorry #1 final assembly
```lean
theorem isCompact_rationalOpen_inter_vle_noHArch ...
  := isCompact_preimage_rationalOpen_noHArch L
       |>.inter_right (1.1)
```
**Once 1.1, 1.3 land, this is one line.**

---

## Sorry #2 — Lemma 7.54 cover refinement (P7)

**Statement** (`TateAcyclicityResiduals.lean:210`):
```lean
theorem exists_standard_cover_refining
    (C : RationalCovering A) :
    ∃ S : Finset A,
      refines_cover C S ∧ refines_contain C S ∧ refines_span_top S
```

**Wedhorn proof (Lemma 7.54, p.70)**: For complete affinoid A and open cover (V_j) of Spa A, there exist f_0,…,f_n ∈ A generating A as ideal such that each R((f_0…f_n)/f_i) is contained in some V_j. Wedhorn cites [Hu3] Lemma 2.6.

**Decomposition** (3 atomic sub-lemmas):

### 2.1 `exists_finite_subcover_rationalOpens` — extract a finite rational subcover from a cover
```lean
theorem exists_finite_rationalOpen_subcover_of_qc
    (C : RationalCovering A) :
    ∃ (n : ℕ) (T : Fin n → Finset A) (s : Fin n → A),
      (∀ i, (T i) · A = ⊤) ∧
      (∀ x ∈ Set.univ, ∃ i, x ∈ rationalOpen (T i) (s i)) ∧
      (∀ i, ∃ V ∈ C.covers, rationalOpen (T i) (s i) ⊆ rationalOpen V.T V.s)
```
**Wedhorn ref**: rational subsets are QC opens (7.35(2)), so the cover (V_j ∩ rational basis) refines to a finite subcover.

### 2.2 `exists_ideal_generators_from_cover` — collapse the rational subcover to a single ideal-generated cover
```lean
theorem exists_ideal_generators_dominating_cover
    {n : ℕ} (T : Fin n → Finset A) (s : Fin n → A)
    (h_cover : ∀ x ∈ Set.univ, ∃ i, x ∈ rationalOpen (T i) (s i)) :
    ∃ S : Finset A, S · A = ⊤ ∧
      ∀ f ∈ S, ∃ i, rationalOpen ({f} ∪ ⋃_i T i) f ⊆ rationalOpen (T i) (s i)
```
*Or similar — this is the Wedhorn 7.54 construction:* combine all `T i ∪ {s i}` into one generating set S, then individual quotients refine.

### 2.3 `refines_cover_per_E_of_ideal_cover` — package as `refines_cover`/`refines_contain`/`refines_span_top`
```lean
-- Once 2.1 + 2.2 land, this is bookkeeping using the project's existing
-- predicates `refines_cover`, `refines_contain`, `refines_span_top`.
```

---

## Sorry #3 — P5 outer (W3 unit-generated → Laurent-ratio refinement)

**Statement** (`TateAcyclicityResiduals.lean:1430`):
```lean
theorem unitGeneratedCover_has_relative_ratioLaurentRefinement
    (L : RationalLocData A) (C : RationalCovering A)
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (I_units : Finset A)
    (_h_unitCover : IsUnitGeneratedCoverFrom L C h_unit_base I_units) :
    ∃ inner_rel : LaurentTree (presheafValue L),
      ⟨refines + allSplitsInducing + IsRatioLaurentTreeFrom⟩
```

**Wedhorn proof (Lemma 8.34(iii))**: Every rational cover U of X generated by units f_0,…,f_n of A has a refinement by a Laurent cover. *Proof*: the Laurent cover generated by {f_i f_j⁻¹ ; 0 ≤ i,j ≤ n} is a refinement of U.

**Status this session**: 1 of 3 sub-properties closed (`IsRatioLaurentTreeFrom`). The other 2 (`refines` and `allSplitsInducing`) are the inner sorries 1504 and 1515.

So sorries #3, #4, #5 are the SAME decomposition: outer construction at 1430 + 2 inner sub-properties.

### 3.1 (inner sorry 1504) `unitCover_refines_per_leaf` — every leaf of the ratio tree refines a cover piece
```lean
theorem ratio_leaves_refine_unitCover
    (L : RationalLocData A) (C : RationalCovering A)
    (h_unit_base : IsUnit (L.canonicalMap C.base.s))
    (I_units : Finset A)
    (h_unitCover : IsUnitGeneratedCoverFrom L C h_unit_base I_units)
    (ratio_list : List (presheafValue L)) :
    ∀ D ∈ (LaurentTree.ofBalancedList ratio_list).leaves L,
      ∃ E ∈ C.covers, rationalOpen D.T D.s ⊆ rationalOpen E.T E.s
```
**Wedhorn ref**: each leaf is determined by a sign vector σ over the ratio pairs; σ forces a maximal `f* ∈ I_units` with `v(u_{f*})` largest; the unitCover piece for `f*` contains the leaf. Already sketched in the existing code at line 1504 comment block.

### 3.2 (inner sorry 1515) `BalancedInducing_per_pair` — per-pair Lane C inducing
```lean
theorem balancedInducing_ratio_list_of_unitCover
    (L : RationalLocData A) (h_unit_base : ...)
    (I_units : Finset A) (h_units_invertible : ...)
    (ratio_list : List (presheafValue L)) :
    LaurentTree.BalancedInducing L ratio_list
```
**Wedhorn ref**: each Laurent split node uses Lane C inducing (`productRestrictionSub_isInducing_via_laurent_refinement_tau` = T286, already done #48), reduced via `BalancedInducing` predicate.

### 3.3 (outer 1392 closure) Once 3.1 + 3.2 land, sorry #3 closes by `refine ⟨inner_rel, ?_, ?_, ?_⟩` where the three holes are 3.1, 3.2, and the already-closed `IsRatioLaurentTreeFrom`.

---

## Sorry #6 — P4 W3-transport (relative Laurent → absolute)

**Statement** (`TateAcyclicityResiduals.lean:1632`):
```lean
theorem relative_laurent_tree_to_absolute ...
```

**Wedhorn proof (compose 8.34(iii) and 8.34(i))**: transport the relative Laurent refinement (over `presheafValue L`) up to an absolute `RatioLaurentTree A` via the typed retraction `RatioTreeRealization`.

**Decomposition** (1 inductive recursion):

### 6.1 `RatioTreeRealization.transport_from_relative`
```lean
theorem ratioTreeRealization_of_relative
    (t_rel : LaurentTree (presheafValue L))
    (h_rel_refines : ∀ D ∈ t_rel.leaves L, ...)
    (h_rel_inducing : t_rel.allSplitsInducing L)
    (h_rel_ratio : IsRatioLaurentTreeFrom L C h_unit_base t_rel) :
    ∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
      ρ.Refines C ∧ ρ.allSplitsInducing
```
**Wedhorn ref**: this is the on-target W3-transport induction; it's structural recursion on `t_rel`. The leaf-level `Refines C` follows from `h_rel_refines`'s leaf form + the unitCover → restricted-unit-piece → C-piece chain. Internal-node recursion uses P3 (`relative_ratio_split_transports_to_RatioNodeData`).

**Already-proved dependency**: P3 (`relative_ratio_split_transports_to_RatioNodeData` line 1241) — verified above to have a complete proof body (closes via `exists_absolute_ratio_rationalLocData_aux` which goes through `exists_ideal_pow_generators_dominated_for_half_space` which needs **Sorry #1**).

So Sorry #6 needs only:
- Sorry #1 (half-space compactness) — feeds P3 via the chain
- This recursive transport (6.1) — pure structural recursion, no new math

---

## Sorry #7 — P8 final assembly

**Statement** (`TateAcyclicityResiduals.lean:1759`):
```lean
theorem exists_wedhorn_ratio_laurent_refinement_tree_realized
    (P : PairOfDefinition A) (C : RationalCovering A) :
    ∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
      ρ.Refines C ∧ ρ.allSplitsInducing
```

**Wedhorn proof (8.34(iv))**: combine 8.34(i), (ii), (iii) via Prop A.3(1).

**Decomposition** (1 composition):

### 7.1 `assemble_W1_W2_W3_transport`
```lean
-- Compose:
-- (W1) exists_standard_cover_refining (Sorry #2) — gives S
-- (W2) exists_first_stage_laurent_tree_unit_generated — uses Cor 7.32 (with or without hArch)
-- (W3) unitGeneratedCover_has_relative_ratioLaurentRefinement (Sorry #3)
-- (W3-transport) relative_laurent_tree_to_absolute (Sorry #6)
```
No new math; just calling the predecessors in order.

---

## Sorry #8 — I.1 legacy LaurentTree

**Statement** (line 1810): conditional on typeclass instances `HasLocLiftPowerBounded (presheafValue D)` etc. **NOT on the critical path** for the main `tateAcyclicity` if we drop the legacy interface. Marked deferred unless the user wants the legacy form.

---

## Sorry #9 — `adicCompletion_noetherian` (Stacks 00MA)

**Statement** (line 2167):
```lean
theorem adicCompletion_noetherian
    (R : Type*) [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R)
```

**Mathlib gap**. Either upstream to Mathlib or use a project-local workaround (perhaps reduce to the specific cases we need: `R = A[X]` for a noetherian Tate ring `A`). **Not bite-size** — this is a real Mathlib contribution.

For Tate acyclicity in case (b) — strongly noetherian Tate — we explicitly assume `IsStronglyNoetherian A` which gives us `A⟨X⟩` noetherian as a *hypothesis*, so we might be able to bypass this entirely. Verify whether the critical path actually needs `adicCompletion_noetherian` or just the strong-noetherian hypothesis.

---

## Sorry #10 — IsSheafy topological-inducing residual

**Statement** (`StructureSheaf.lean:1207`):
The topological-inducing residual for arbitrary `C : RationalCovering A`, conditional on T-LANE-C-induction = constructing a Laurent τ-refinement.

**Wedhorn ref**: same content as P3–P5 transported to topology side. **Wedhorn 8.34 used twice**: once for algebraic injectivity (Cor 8.32), once for topological inducing.

### 10.1 `productRestrictionSub_isInducing_general` — close the sorry
```lean
-- Direct application of T286 (productRestrictionSub_isInducing_via_laurent_refinement_tau)
-- to the τ-existence supplied by Sorry #7 (P8).
```
Once P8 lands, sorry #10 is one tactic call.

---

# Dependency graph

```
#1 (half-space) ──→ exists_ideal_pow_generators_dominated_for_half_space
                  ──→ exists_absolute_ratio_rationalLocData_aux
                  ──→ P3 (relative_ratio_split)
                  ──→ #6 (P4 W3-transport, via recursion)
                                                  ↘
#2 (W1, Lemma 7.54)                                ↘
                ↘                                   ↘
                 → P6 (W2, needs Cor 7.32 no-hArch)  → #7 (P8 assembly)
                                                  ↗            ↓
#3,#4,#5 (P5 W3 — 1/3 closed, 2 reduced) ────────/      #10 (IsSheafy topo)
```

# Workable bite-size list (atomic order)

The user can pick any of these as a one-session task:

1. **L1.1** `isClosed_setOf_vle` (Spv side closedness) — 5–15 lines.
2. **L1.3.B (Route B)** `isCompact_preimage_rationalOpen_noHArch` via Spv(A,I) — needs the Spv(A,I) signatures already added. Each Spv(A,I) sub-lemma I added is bite-size (continuity, basis, spectral).
3. **L1.4** Sorry #1 final assembly (1 line, after L1.1 + L1.3).
4. **L2.1** `exists_finite_rationalOpen_subcover_of_qc` — standard QC argument.
5. **L2.2** `exists_ideal_generators_dominating_cover` — the Wedhorn 7.54 combinatorial step.
6. **L2.3** Sorry #2 packaging (1–5 lines).
7. **L3.1** `ratio_leaves_refine_unitCover` — sign-vector / pigeonhole argument, ~30–50 lines.
8. **L3.2** `balancedInducing_ratio_list_of_unitCover` — chain of T286 calls, ~20 lines.
9. **L3.3** Sorry #3 outer closure (assembles L3.1 + L3.2 + existing `IsRatioLaurentTreeFrom`).
10. **L6.1** `ratioTreeRealization_of_relative` — structural recursion on `LaurentTree`, ~30 lines.
11. **L7.1** Sorry #7 composition (~10 lines).
12. **L10.1** Sorry #10 (1 tactic call after L7.1).

Cor 7.32 no-hArch is needed for **P6** (the W2 stage). Its decomposition is the Spv(A,I) chain I already added signatures for; the bite-size sub-lemmas there are:
- W7.10 equality `cont_eq_spvAI_inter_lt_one` (`SpvAI.lean:408`)
- W7.5(1) basis `SpvAI.rationalSubset_isBasis` (`SpvAITopology.lean:480`)
- W7.5(1) spectrality `SpvAI.isSpectralSpace` (`SpvAITopology.lean:497`)
- W7.12 `cont_isClosed_in_SpvAI` (`SpvAITopology.lean:524`)
- 7.35(1) `Spa.eq_Cont_inter_basicOpens` (not yet stated — bite-size to add)
- 7.32-no-hArch (assembled from above + 7.31).

# Stop conditions

- **DONE** when `lake build` is clean and there are no sorries on the path from `tateAcyclicity_stronglyNoetherianTate` to the leaves (excluding `adicCompletion_noetherian` if we route around it).
- **#9 (`adicCompletion_noetherian`)** is the only genuine Mathlib gap; treat separately.
- **#8 (I.1 legacy)** is off the critical path; defer.
