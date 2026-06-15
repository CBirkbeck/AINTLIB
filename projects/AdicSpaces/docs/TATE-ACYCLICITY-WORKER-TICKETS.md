# Tate Acyclicity — Worker-Ready Ticket Board

**Target**: close `isSheafy_ofStronglyNoetherianTate` (Wedhorn Theorem 8.28(b),
Path α) at `Adic spaces/StructureSheaf.lean:1629`.

**Project route**: Path α takes `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]`
as explicit parameter + `[IsDomain A] [CompleteSpace A]`. The Wedhorn 7.5
chain is OUT of scope per project scope memo.

**Build invariant**: `lake build` must remain clean after every ticket closes
(3141 jobs, 0 errors). Each worker should run `lake build` before marking
DONE.

**Naming convention**:
- `T-S*` = top-level tickets (existing IDs in `.mathlib-quality/tickets.md`)
- `T-DEF*` = decomposition-phase tickets (existing IDs)
- `T-FOUND*` = new foundation tickets created here for Layer 0
- `T-ACYC*` = new acyclicity-chain tickets created here for Layer 2

---

## Layer 0 — Foundation (no Tate-acyclicity dependencies; parallel-safe)

### T-FOUND-A — Wedhorn 7.35(1): Spa pro-constructible in Spv(A,I)

- **Status**: in_progress (structural commit + sub-leaves decomposed)
- **File**: `Adic spaces/SpaCompactNoHArch.lean:340` (assembly), sub-leaves at lines 268, 312
- **Depends on**: T-FOUND-A.b sub-lemmas
- **Type**: theorem (body assembled, sub-leaves remain)
- **Existing alias**: T-S8

#### Progress (2026-05-22 beastmode)

- Main body fully assembled using A.b sub-lemma (line 340-405)
- A.b atomically decomposed into 4 sub-leaves:
  - A.b.1 (P.fg) — ✓ provided by `PairOfDefinition.fg` field
  - A.b.2 `SpvAI.proConstructible_in_Spv` (line 268) — Wedhorn 7.5(iv), sorry
  - A.b.3-fwd `cont_lt_one_on_I_imp_on_generators` (line 295) — ✓ closed (5 LOC)
  - A.b.4 `Cont.iff_isInSpvAI_and_lt_one_on_I` (line 312) — Wedhorn 7.10
    - fwd-1 (continuous → ∈ Spv(A,I)) — sorry
    - fwd-2 (continuous → ∀ a₀ ∈ P.I, ¬ v.vle 1 (subtype a₀)) — ✓ closed (28 LOC)
    - reverse (∈ Spv(A,I) + ∀ a₀ ∈ P.I, v(a₀) < 1 → continuous) — sorry
- A.b main body partially closed: forward inclusion ✓, reverse inclusion sorry
- **Statement correction (B2 self-fix)**: A.b.4 originally had `∀ a ∈ P.I.map _`
  (= elements of the full ideal in A); corrected to `∀ a₀ ∈ P.I` (= elements
  of P.I via subtype). The ideal-map form was too strong — products c·p with
  c ∉ A° need not be topnilp.
- Build clean 3141 jobs throughout.

#### Statement

```lean
theorem Spa.proConstructible_in_SpvAI
    (P : PairOfDefinition A) :
    ∃ (S : Set (Set (Spv A))),
      (∀ s ∈ S, ∃ (T : Finset A) (b : A),
        s = { v : Spv A | (∀ t ∈ T, v.vle t b) ∧ ¬ v.vle b 0 } ∨
        s = { v : Spv A | (∀ t ∈ T, v.vle t b) ∧ ¬ v.vle b 0 }ᶜ) ∧
      (Spa A A⁺ : Set (Spv A)) = ⋂₀ S
```

#### Proof sketch

Per the existing TODO comment at the sorry:
1. `Spa A A⁺ = Cont A ∩ ⋂_{a ∈ A⁺} {v.vle a 1 ∧ ¬ v.vle 1 0}` (already proved as `spa_eq_cont_inter`).
2. A⁺-cylinder: each `{v.vle a 1}` for `a ∈ A⁺` is constructible.
3. `Cont A` = continuous valuations = countable intersection of constructibles (Wedhorn 7.34).
4. Combine via `Spa.eq_Cont_inter_basicOpens`.

#### Mathlib lemmas / project supports

- `spa_eq_cont_inter` (line 231, ✓ proved)
- Wedhorn 7.34 continuous-valuation pro-constructibility (substantive sub-piece)

#### Sources

Wedhorn p.64–66 §7.35.

---

### T-FOUND-B — Wedhorn 7.35(2): rational opens are QC in Spa

- **Status**: open
- **File**: `Adic spaces/SpaCompactNoHArch.lean:276`
- **Depends on**: T-FOUND-A
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S7

#### Statement

```lean
theorem isCompact_preimage_rationalOpen_noHArch
    [DecidableEq A] (T : Finset A) (s : A) :
    IsCompact (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺))
```

#### Proof sketch

1. Use T-FOUND-A to view `Spa A` inside `Spv(A, I)` where I is an ideal of definition.
2. The rational open `R(T/s)` in `Spv(A, I)` is a basic constructible open, hence QC.
3. QC of a closed subspace of QC is QC.

#### Mathlib lemmas / project supports

- T-FOUND-A
- `SpvAI.rationalSubset_isBasis` (sorry at `SpvAITopology.lean:498`, should be proved separately if needed)

#### Sources

Wedhorn p.66 Lemma 7.35(2).

---

### T-FOUND-C — Wedhorn 7.31: zero-neighborhood dominated by nonvanishing f on QC

- **Status**: **DONE 2026-05-22** (close existing sorry; ~80 LOC)
- **File**: `Adic spaces/Cor732.lean:421`
- **Depends on**: none (T-FOUND-B not actually needed; `exists_pow_dominated_finset` suffices)
- **Type**: theorem
- **Progress**:
  - 2026-05-22: closed via topnilp unit + topologicallyNilpotentElements route. Added `[IsTateRing A]`
    hypothesis (per binding rule (b); the proof needs a topologically nilpotent unit which is
    Tate-specific). Strategy: pick π topnilp unit, apply `exists_pow_dominated_finset` with
    `T = {π}` to get m, define I = `π^(m+1) · A°°`. A°° is open in Tate
    (`IsTateRing.isOpen_topologicallyNilpotentElements`), multiplication by unit is a homeomorphism
    (`IsUnit.isHomeomorph_smul`). Strict v-bound: v(π) < 1 strict via D2.2 + v(b) ≤ 1 for b ∈ A°°
    via `not_vle_one_of_mem_spa_of_topologicallyNilpotent`.
  - Build clean (3141 jobs).

#### Statement

```lean
theorem exists_zero_nbhd_lt_on_qc
    {X : Set ↥(Spa A A⁺)} (hX : IsCompact X) (f : A)
    (hf : ∀ x ∈ X, ¬ (x.1 : Spv A).vle f 0) :
    ∃ I : Set A, IsOpen I ∧ (0 : A) ∈ I ∧
      ∀ a ∈ I, ∀ x ∈ X, (x.1 : Spv A).vle a f ∧ ¬ (x.1 : Spv A).vle f a
```

#### Proof sketch (Wedhorn p.63)

1. Get topologically nilpotent finite set `T ⊆ A°°` from `IsHuberRing` / `IsTateRing`.
2. Apply `exists_pow_dominated_finset` (already proved at `Cor732.lean:318`) with X compact and f nonvanishing. Get m ∈ ℕ.
3. Set `I := T^m · A°°` (the m-th power of T applied to A°°). This is open (it's a fundamental nbhd of 0 in the f-adic topology).
4. For a ∈ I: a = t^m · b for t ∈ T, b ∈ A°°. Then v(a) = v(t)^m · v(b) ≤ v(f) · 1 = v(f). Strictly < via v(b) < 1 (b topologically nilpotent + v continuous).

#### Mathlib lemmas / project supports

- `exists_pow_dominated_finset` (✓ proved at `Cor732.lean:318`)
- `IsTopologicallyNilpotent.eventually` (mathlib / project)
- f-adic topology basis structure

#### Sources

Wedhorn p.63 Lemma 7.31. BGR §3.7.2/3.

---

### T-FOUND-D — Wedhorn Cor 7.32 finset form: dominating unit

- **Status**: open
- **File**: `Adic spaces/Cor732.lean:468`
- **Depends on**: T-FOUND-C
- **Type**: theorem (close existing sorry)

#### Statement

```lean
theorem exists_dominating_unit_noHArch_finset
    (hSpa_compact : CompactSpace ↥(Spa A A⁺))
    (T : Finset A) (hT : ∀ v ∈ Spa A A⁺, ∃ t ∈ T, ¬ v.vle t 0) :
    ∃ s : Aˣ, ∀ v ∈ Spa A A⁺, ∃ t ∈ T,
      v.vle (s : A) t ∧ ¬ v.vle t (s : A)
```

#### Proof sketch

For each `t ∈ T`, the set `Y_t := {v ∈ Spa A : v(t) ≠ 0}` is QC (Wedhorn 7.35(2),
= T-FOUND-B) and `t` is nonvanishing on `Y_t`. Apply singleton
`exists_dominating_unit_noHArch` (proved at `Cor732.lean:445`) to each `(Y_t, t)`
to get unit `u_t ∈ A^×` with `v(u_t) < v(t)` on `Y_t`.

Take `s = ∏_{t ∈ T} u_t ∈ A^×`. For any v ∈ Spa A, by hT pick `t_v ∈ T` with
`v(t_v) ≠ 0`. Each `u_t` is topnilp (came from Cor 7.32 singleton), so `v(u_t) < 1`.
Then `v(s) = ∏ v(u_t) ≤ v(u_{t_v}) · 1 · 1 · … < v(t_v)`. ✓

#### Mathlib lemmas / project supports

- `exists_dominating_unit_noHArch` (✓ proved at `Cor732.lean:445`)
- `T-FOUND-B` (Y_t QC)
- `Units.prod` for the product of T-indexed units

#### Sources

Wedhorn p.63 Cor 7.32. Used by Wedhorn 8.34(ii).

---

### T-FOUND-E — Strong-noetherian Tate preservation under presheafValue

- **Status**: open
- **File**: `Adic spaces/PresheafTateStructure.lean:2371`
- **Depends on**: none (Wedhorn-direct, avoids Stacks 0316)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-DEF4

#### Statement

```lean
theorem presheafValue_isNoetherianRing_of_strongly_noetherian
    [IsTateRing A] [IsStronglyNoetherian A] [T2Space A]
    (D₀ : RationalLocData A) :
    IsNoetherianRing (presheafValue D₀)
```

#### Proof sketch (Wedhorn p.55 Ex 6.38 + p.54 Rem 6.37(1))

1. **Sub-lemma T-FOUND-E.1** (~40 LOC): If A is Tate and B is topologically of finite type over A, then `IsTopologicallyFiniteType A B` is preserved under composition.

2. **Sub-lemma T-FOUND-E.2** (~60 LOC): Wedhorn Rem 6.37(1): "Every Tate ring topologically of finite type over a strongly noetherian Tate ring is strongly noetherian by Prop 6.33."

3. **Main**: presheafValue D₀ = Â⟨T/s⟩ is tft over A by Ex 6.38. Apply E.2 to get IsStronglyNoetherian. Then take n = 0 to get IsNoetherianRing.

#### Mathlib lemmas / project supports

- Existing TateAlgebra noetherianness machinery
- `presheafValue_iso_AlangleT_quotient` (needs verification)

#### Sources

Wedhorn p.54 Rem 6.37(1) (verbatim): "Every Tate ring topologically of finite type
over a strongly noetherian Tate ring is strongly noetherian by Proposition 6.33."
Wedhorn p.55 Ex 6.38.

---

### T-FOUND-F — Wedhorn Rem 7.55: Laurent normalization existence

- **Status**: open
- **File**: TBD (likely `TateAcyclicityResiduals.lean` or `LaurentRefinement.lean`)
- **Depends on**: none
- **Type**: definition + lemma
- **Existing alias**: T-S10

#### Statement

For every rational subset `V = R(T/s)`, the project's `LaurentNormalized` instance
provides the structure: `1 ∈ T` (per the project's class definition). Wedhorn 7.55
says: every rational subset can be put in this normalized form, i.e., we can
WLOG assume `1 ∈ T`.

#### Proof sketch (Wedhorn Remark 7.55)

The "Laurent normalization" amounts to adjoining 1 to T without changing the
rational subset (since v(1) = 1 ≤ v(s) iff v(s) ≥ 1, which is always true in
the project's normalization).

Mathematically: `R(T/s) = R(T ∪ {1}/s)` since adding `1 ≤ v(s)` to the constraint
set is consistent with the existing constraints (assuming s is chosen so v(s) ≠ 0).

#### Mathlib lemmas / project supports

- Existing `LaurentNormalized` class
- `rationalOpen` definition + `insert_T` invariance lemma

#### Sources

Wedhorn p.70–71 Remark 7.55.

---

### T-FOUND-G — Wedhorn Prop 8.30: flat rational restriction

- **Status**: open
- **File**: `Adic spaces/Cor832.lean:547`
- **Depends on**: T-FOUND-E (`hNoeth_B` for `restrictionMap_flat_via_iteratedMinus`)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S9

#### Statement

```lean
theorem flat_over_base_tate
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule)
```

#### Proof sketch

For each `D ∈ C.covers`, use `restrictionMap_flat_via_iteratedMinus`
(`Adic spaces/RestrictionFlatness.lean`) which already proves flatness via
Wedhorn 8.30 + Lemma 2.13. The hypothesis bundle has to be threaded — needs
`hNoeth_B = T-FOUND-E` (for `IsNoetherianRing (presheafValue D₀)`) and the
chain-construction lemmas (T-CHAIN-* tasks, all done).

#### Mathlib lemmas / project supports

- `restrictionMap_flat_via_iteratedMinus` (RestrictionFlatness.lean)
- T-CHAIN-CONSTRUCTION, T-CHAIN-STEP-FLATNESS, T-CHAIN-COMPOSITION (all ✓ done)
- T-FOUND-E for `hNoeth_B`

#### Sources

Wedhorn p.79–81 Prop 8.30, Lemma 8.31 + 2.13.

---

## Layer 1 — Embedding chain (`IsSheafy.embedding` field)

### T-DEF1 — Unit-case Lane C single-step inducing

- **Status**: in_progress (skeleton declared 2026-05-22)
- **File**: `Adic spaces/EmbeddingTopo.lean:1054`
- **Depends on**: none (uses standard topology infrastructure)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-DEF1

#### Statement

```lean
theorem productRestrictionSub_laurentCovering_isInducing_of_isUnit
    (D₀ : RationalLocData A) (f : A) (_hf : IsUnit (D₀.canonicalMap f)) :
    Topology.IsInducing (productRestrictionSub A (laurentCovering D₀ f))
```

#### Proof sketch

When `D₀.canonicalMap f` is a unit in `presheafValue D₀`:
1. The maps `O(D₀) → O(plus)` and `O(D₀) → O(minus)` are ring isomorphisms
   (localizing at an already-unit is the identity up to completion).
2. The product factors as `x ↦ (φ(x), ψ(x))` where φ, ψ are topological isos.
3. IsInducing follows by `Topology.IsInducing.id_of_iso ∘ prodMk`.

Sub-pieces to develop:
- `localizationAway_isIso_of_isUnit`
- `presheafValue_iso_of_canonical_isUnit`
- Topological transfer via completion + uniform continuity

#### Sources

Project-internal — bridges Lane C base case to ratio-tree case. Complement to T276
(non-unit case, proved).

---

### T-DEF2 — BalancedInducing for list of units

- **Status**: open
- **File**: `Adic spaces/EmbeddingTopo.lean` or `TateAcyclicityResiduals.lean`
- **Depends on**: T-DEF1
- **Type**: theorem

#### Statement (sketch, see existing tickets.md for full)

For a `RationalLocData D₀` and a list `L : List A` of elements all units in
`presheafValue D₀`, the iterated Laurent covering is IsInducing.

#### Proof sketch

Induction on L using T-DEF1 (base case) and existing T289/T290 (inductive step).

---

### T-DEF3 — σ-vector → maximal-f* refinement bridge

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean`
- **Depends on**: T-DEF2
- **Type**: theorem

#### Statement (see existing tickets.md)

Bridges the σ-vector encoding (per Wedhorn 8.34 proof) to the maximal-f* refinement
needed by P5.

---

### T-W3-P3 — Relative ratio-split transport to `RatioNodeData`

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean` (relative side)
- **Depends on**: P1, P2 (both ✓ done)
- **Type**: theorem
- **Existing task**: #63

#### Statement

```lean
theorem relative_ratio_split_transports_to_RatioNodeData
    (L : RationalLocData A) (...)
    -- transports a relative ratio split (over presheafValue L) into a
    -- RatioNodeData of the absolute tree
```

#### Sources

Wedhorn 8.34 step (iii) + the W3-transport bridge per round-6 reviewer
relative-labels revision.

---

### T-S6c (P4) — Relative-to-absolute Laurent tree transport

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:1656`
- **Depends on**: T-W3-P3
- **Type**: theorem
- **Existing task**: #64

#### Statement

```lean
theorem relative_laurent_tree_to_absolute
    (L : RationalLocData A) (...)
    -- given a relative LaurentTree over presheafValue L,
    -- produces an absolute LaurentTree over A
```

#### Proof sketch (Wedhorn 8.34 step transport)

Apply Wedhorn 2.13 (= project's `restrictionMap_flat_via_iteratedMinus` infrastructure)
to lift the relative tree to the absolute level via the canonical map.

---

### T-S6b (P5) — W3: unit-generated cover has relative ratio Laurent refinement

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:1479`
- **Depends on**: T-DEF3, T-S10 (= T-FOUND-F)
- **Type**: theorem
- **Existing task**: #65

#### Statement

(See existing `TateAcyclicityResiduals.lean:1479` for full signature.)

```lean
theorem unitGeneratedCover_has_relative_ratioLaurentRefinement
    ...
```

#### Proof sketch (Wedhorn 8.34 step (iii))

For a rational cover generated by units in `𝒪_X(L)`, the Laurent cover generated
by pairwise ratios of those units refines the input cover. Uses T-DEF3 for the
σ-vector encoding and T-S10 for the Laurent normalization.

---

### T-S6a (P6) — W2: first-stage Laurent tree exists

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:1426`
- **Depends on**: T-FOUND-D (Cor 7.32 finset)
- **Type**: theorem
- **Existing task**: #66

#### Statement

(See existing `TateAcyclicityResiduals.lean:1426` for full signature.)

```lean
theorem exists_first_stage_laurent_tree_unit_generated
    ...
```

#### Proof sketch (Wedhorn 8.34 step (i))

From a `refines_cover` standard cover S (provided by W1 = T-S6d), construct
the first-stage Laurent tree by:
1. Apply T-FOUND-D (Cor 7.32 finset) to get a unit s ∈ A^× dominating the cover.
2. Build the outer LaurentTree as `LaurentTree.ofBalancedList` over the ratios `(s⁻¹·f)` for `f ∈ S`.
3. Verify the tree's `allSplitsInducing` property (Wedhorn 8.34(ii)).
4. Verify each leaf is `restricted_standard_cover_generated_by_units`.

---

### T-S6d (P7) — W1: standard cover refining a rational cover

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:211`
- **Depends on**: T-FOUND-D, T-S7 (= T-FOUND-B)
- **Type**: theorem
- **Existing task**: #67

#### Statement

(See existing `TateAcyclicityResiduals.lean:211` for full signature.)

```lean
theorem exists_standard_cover_refining
    (C : RationalCovering A) :
    ∃ S : Finset A,
      refines_cover C S ∧
      refines_contain C S ∧
      refines_span_top S
```

#### Proof sketch (Wedhorn p.70 Lemma 7.54)

Wedhorn cites [Hu3] Lemma 2.6 with the monolithic proof:
1. For each E ∈ C.covers, apply Wedhorn Cor 7.32 (= T-FOUND-D) to get a finite
   set of generators for E.
2. Union over all E gives `S : Finset A`.
3. Span-top from joint Spa-cover surjectivity.
4. refines_cover / refines_contain per-piece from Cor 7.32.

#### Sources

Wedhorn p.70 Lemma 7.54. Huber [Hu3] Lemma 2.6.

---

### T-S6 (P8) — Assemble Wedhorn 8.34 ratio Laurent refinement tree

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:1845`
- **Depends on**: T-S6a, T-S6b, T-S6c, T-S6d
- **Type**: theorem (assembly)
- **Existing task**: #68

#### Statement

(See existing `TateAcyclicityResiduals.lean:1845` for full signature.)

```lean
theorem exists_wedhorn_ratio_laurent_refinement_tree_realized
    (C : RationalCovering A) :
    ∃ (t : RatioLaurentTree A) (ρ : RatioTreeRealization t C.base),
      ρ.Refines C ∧ ρ.allSplitsInducing
```

#### Proof sketch (Wedhorn 8.34 assembly)

Combines W1 (T-S6d) → W2 (T-S6a) → W3 (T-S6b) → P4 (T-S6c):
1. W1: get standard cover S refining C.
2. W2: build first-stage Laurent tree t_outer with unit-generated leaves.
3. W3: per leaf L, get relative ratio refinement (over `presheafValue L`).
4. P4: transport each relative refinement to absolute, producing the inner trees.
5. `graftAt` the inner trees onto t_outer at each leaf.
6. Verify Refines and allSplitsInducing properties.

---

### T-S5 — Ratio-tree → IsInducing of productRestrictionSub

- **Status**: open
- **File**: `Adic spaces/TateAcyclicityResiduals.lean:2441`
- **Depends on**: T-S6, plus existing T-LAURENT-REFINEMENT-TREE (done)
- **Type**: theorem
- **Existing alias**: T-S5

#### Statement

```lean
theorem productRestrictionSub_isInducing_via_ratio_tree
    (C : RationalCovering A)
    (t : RatioLaurentTree A)
    (ρ : RatioTreeRealization t C.base)
    (h_refines : ρ.Refines C)
    (h_split : ρ.allSplitsInducing) :
    Topology.IsInducing (productRestrictionSub A C)
```

#### Proof sketch

Recursion on `RatioLaurentTree` structure:
- Leaf (laurentCovering): T286 (proved) + T279 (proved).
- Internal node (ratio split): T289 (proved) + T280 (proved).

This is the ratio-tree variant of T-LAURENT-REFINEMENT-TREE (done).

---

### T-S4 — productRestrictionSub_isInducing_tate (= IsSheafy.embedding)

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1356`
- **Depends on**: T-S5, T-S6
- **Type**: theorem
- **Existing alias**: T-S4

#### Statement

```lean
theorem productRestrictionSub_isInducing_tate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A) :
    Topology.IsInducing (productRestrictionSub A C)
```

#### Proof sketch

1. Apply T-S6 to get `(t, ρ)` with `Refines C ∧ allSplitsInducing`.
2. Apply T-S5 with this data.

One-liner once T-S5 and T-S6 are both closed.

---

## Layer 2 — Acyclicity chain (`IsSheafy.acyclicity` field)

### T-ACYC-A — Per-cover-piece Spa-point construction (B5')

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1466`
- **Depends on**: T-FOUND-E (presheafValue noetherian)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S12

#### Statement

```lean
theorem hSpa_surj_cover_level
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    (hspan_top : ∀ p : Ideal (presheafValue C.base), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p) :
    ∀ p : Ideal (presheafValue C.base), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p
```

#### Proof sketch (per existing comment at Cor832:512)

For each prime p of `presheafValue C.base`:
1. By `hspan_top`, pick D ∈ C.covers with `C.base.canonicalMap D.1.s ∉ p`.
2. Construct a Spa-point q at the `presheafValue D.1`-level whose comap to `presheafValue C.base` equals p.
3. The construction uses Wedhorn 7.45 / trivial-valuation lifting at the
   `presheafValue D`-level. `presheafValue D` is strongly noetherian Tate again
   by Ex 6.38 (= T-FOUND-E).

NOT discharged via `cor_8_32_clean` to avoid circularity.

---

### T-ACYC-B — hSpa_surj_from_spanTop (wraps T-ACYC-A)

- **Status**: open
- **File**: `Adic spaces/Cor832.lean:512`
- **Depends on**: T-ACYC-A
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-DEF6

#### Statement

```lean
theorem hSpa_surj_from_spanTop
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCovering A)
    [Finite { D : RationalLocData A // D ∈ C.covers }]
    (hspan_top : ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ D : { D // D ∈ C.covers }, C.base.canonicalMap D.1.s ∉ p) :
    ∀ (p : Ideal (presheafValue C.base)), p.IsPrime →
      ∃ (D : { D // D ∈ C.covers }) (q : Ideal (presheafValue D.1)),
        q.IsPrime ∧ q.comap (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)) = p
```

#### Proof sketch

Wraps T-ACYC-A, adding the `[IsDomain A]` and completion hypotheses if needed.
Same proof content; this version threads the lighter hypothesis bundle used by
`cor_8_32_clean_via_flat`.

---

### T-ACYC-C — Stacks 023N faithfully flat descent

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1398`
- **Depends on**: none (pure algebra)
- **Type**: theorem (close existing sorry)

#### Statement

```lean
theorem faithfullyFlat_cocycle_kernel_eq_algebraMap_range
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (s : S) (h_cocycle : faithfullyFlat_cocycleMap R S s = 0) :
    ∃ r : R, algebraMap R S r = s
```

#### Proof sketch (Stacks Tag 023N)

1. Tensor the sequence `R → S ⇉ S ⊗_R S` with S over R; result `S → S ⊗_R S ⇉ S ⊗_R S ⊗_R S` has a section (mult map), so it's split exact.
2. Faithful flatness reflects exactness back to the un-tensored sequence.
3. Conclude `R → ker(cocycleMap)` is surjective.

#### Mathlib lemmas / project supports

- `Module.FaithfullyFlat` (mathlib)
- `TensorProduct` exactness lemmas
- `Algebra.tensorEquiv` for the section

#### Sources

Stacks Project Tag 023N. Standard fpqc-descent equalizer.

---

### T-ACYC-D — Tate acyclicity Part 1 (separation) via cor_8_32_clean

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1343`
- **Depends on**: T-ACYC-B (via cor_8_32_clean), T-FOUND-G (flatness)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S2

#### Statement

```lean
theorem tateAcyclicity_separation_via_cor832
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : C.covers.Nonempty) :
    ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0
```

#### Proof sketch

Hypothesis profile = Wedhorn 8.28(b). Uses `cor_8_32_clean` (faithful flatness of
the product restriction map) to conclude separation: if x maps to 0 in every
cover piece, then x = 0 by faithful flatness.

---

### T-ACYC-E — Tate acyclicity Part 2 (gluing) via flat-descent

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1426`
- **Depends on**: T-ACYC-B, T-ACYC-C, T-FOUND-G
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S3

#### Statement

```lean
theorem tateAcyclicity_gluing_via_descent
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (C : RationalCovering A) (hne : C.covers.Nonempty)
    ...
```

#### Proof sketch

Wedhorn-exact route via Lemma 8.34 (Čech-based) — NOT Stacks 023N. Per the
existing comment: Wedhorn's actual route uses 8.34 acyclicity directly. But the
fallback Stacks 023N (T-ACYC-C) is also a valid route.

For Wedhorn route: use `tateAcyclicity_gluing_via_refinement` (LaurentRefinement)
to reduce to a Laurent cover, then use the closed-form Laurent 2-cover gluing.

---

### T-ACYC-F — Gluing via refinement (Laurent reduction)

- **Status**: open
- **File**: `Adic spaces/LaurentRefinement.lean:5878`
- **Depends on**: T-S6 (the ratio Laurent tree)
- **Type**: theorem (close existing sorry)

#### Statement

```lean
theorem tateAcyclicity_gluing_via_refinement
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCovering A)
    (V_covers : Finset (RationalLocData A))
    (hV_subset : ∀ D ∈ V_covers, rationalOpen D.T D.s ⊆ rationalOpen C.base.T C.base.s)
    (τ : { D // D ∈ V_covers } → { E // E ∈ C.covers })
    (hτ : ∀ d : { D // D ∈ V_covers },
      rationalOpen d.1.T d.1.s ⊆ rationalOpen (τ d).1.T (τ d).1.s)
    (hτ_surj : Function.Surjective τ)
    ...
```

#### Proof sketch (per existing docstring)

Pure reshuffling: converts "gluing on C" to "gluing on V" + "surjective refinement map τ".
Use `restrictionMapHom_injective` (Cor 8.32 — sorry in `PresheafTateStructure`) for the
local-separation step.

---

## Layer 3 — Final assembly

### T-S1 — A1 Path α IsSheafy

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1117`
- **Depends on**: T-S4 (embedding), T-ACYC-D (separation), T-ACYC-E (gluing)
- **Type**: theorem (close existing sorry)
- **Existing alias**: T-S1

#### Statement

```lean
theorem isSheafy_ofStronglyNoetherianTate_flat
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A
```

#### Proof sketch

Construct an `IsSheafy A` structure:
- `embedding C`: use T-S4 `productRestrictionSub_isInducing_tate`.
- `acyclicity C hne`: use T-ACYC-D (separation) + T-ACYC-E (gluing).

#### Sources

Wedhorn 8.28(b) Path α (parametric variant). Reviewer-confirmed scope: A1 is the
parametric variant taking `(P, [IsNoetherianRing P.A₀])` and `[IsDomain A]`.

---

### T-FINAL — A3 IsSheafy (Wedhorn 8.28(b) headline)

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1629`
- **Depends on**: T-S1 (Path α with extras) OR T-WED-FAITHFUL-FINAL (Wedhorn-faithful, no extras)
- **Type**: theorem (close existing sorry)

#### Statement

```lean
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A
```

#### Proof sketch

Direct re-export of T-S1. The A3 vs A1 distinction is naming/wrapping; the
mathematical content is identical per the Session 26 Path α decision.

```lean
theorem isSheafy_ofStronglyNoetherianTate ... :=
  isSheafy_ofStronglyNoetherianTate_flat (A := A) P
```

---

---

# Layer 4 — Wedhorn-faithful (drop Path α extras)

These tickets remove the two extra hypotheses (`[IsDomain A]` and
`[IsNoetherianRing P.A₀]`) that Path α currently carries but Wedhorn 8.28(b)
does not. The goal is **Wedhorn 8.28(b) as stated** — strongly noeth Tate
alone, no domain assumption, no noeth-A₀ parametric.

Both extras are **proof-route artifacts**, not mathematical necessities. The
removals require switching to Wedhorn's actual proof routes (μ_M + 5-lemma
for Lemma 8.33; Cor 8.35 for noeth propagation).

### T-WED-FAITHFUL-A — Drop `[IsDomain A]` via Wedhorn's μ_M route

- **Status**: open
- **File**: `Adic spaces/LaurentCoverExact.lean` (replace existing Krull-based body of `laurentCover_exact_general` if reinstated; or refactor in place)
- **Depends on**: T-FOUND-E (for `Â⟨X⟩` noetherian transport)
- **Type**: theorem refactor + new lemma
- **Addresses**: Wedhorn 8.28(b) signature parity — drops the project's `[IsDomain A]` artifact

### Statement

```lean
theorem laurentCover_exact_general_noDomain
    [IsHuberRing A] [IsTateRing A] [IsNoetherianRing A]
    [T2Space A] [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace) (f : A) :
    Function.Injective (LaurentCover.epsilonHom_gen f) ∧
    Function.Surjective (LaurentCover.deltaMap_gen f) ∧
    (∀ x, LaurentCover.deltaMap_gen f (LaurentCover.epsilonHom_gen f x) = 0) ∧
    (∀ p, LaurentCover.deltaMap_gen f p = 0 →
      ∃ a, LaurentCover.epsilonHom_gen f a = p)
```

**Note**: NO `[IsDomain A]`. Statement matches Wedhorn Lemma 8.33 hypotheses
exactly (noeth complete Tate, no domain).

### Proof sketch (Wedhorn p.83, verbatim)

Replace the Krull-intersection route (which needs `[IsDomain]` for `⨅(f)^n = ⊥`)
with Wedhorn's diagram-chase route via Remark 8.29.

**Wedhorn Lemma 8.33 proof (p.83, verbatim)**:
> "We may assume that A is complete (to simplify the notation). [...] By Examples
> 6.38 and 6.39 we have
>     𝒪_X(U_1) = A⟨ζ⟩/(f − ζ),
>     𝒪_X(U_2) = A⟨η⟩/(1 − fη),
>     𝒪_X(U_1 ∩ U_2) = A⟨ζ, η⟩/(f − ζ, 1 − fη) = A⟨ζ, η⟩/(f − ζ, 1 − ζη)
>       = A⟨ζ, ζ^{-1}⟩/(f − ζ).
> Consider the following commutative diagram [3×3 diagram]
> Here ι is the canonical injection, λ is the map (g(ζ), h(η)) ↦ g(ζ) − h(ζ^{-1}),
> and λ' is induced by λ. The columns are exact by (8.2.1). A diagram chase shows
> that if the first and second row are exact, then the third row is exact (note
> that we know already the injectivity of ε)."

**Then Wedhorn continues**:
> "The equations A⟨ζ, ζ^{-1}⟩ = A⟨ζ⟩ + ζ^{-1}A⟨ζ^{-1}⟩, (f − ζ)A⟨ζ, ζ^{-1}⟩ =
> (f − ζ)A⟨ζ⟩ + (1 − fζ^{-1})A⟨ζ^{-1}⟩ show the surjectivity of λ and λ' [...]
> the equality 0 = λ(Σ a_k ζ^k, Σ b_k η^k) = Σ a_k ζ^k − Σ b_k ζ^{-k} is
> equivalent to a_k = b_k = 0 for k > 0 and a_0 = b_0. Thus im(ι) = ker(λ)."

### Sub-leaves

- **W-FA.1**: `A⟨ζ⟩` noetherian when A is — Wedhorn 8.31(1). Project has via
  `tateAlgebra_isNoetherianRing` (existing). No domain needed.
- **W-FA.2**: Remark 8.29 (μ_M : M ⊗_A A⟨X⟩ → M⟨X⟩ bijective) — project's
  Tate-algebra base-change infrastructure. No domain needed.
- **W-FA.3**: Decomposition `A⟨ζ, ζ^{-1}⟩ = A⟨ζ⟩ + ζ^{-1}A⟨ζ^{-1}⟩` — direct
  Laurent series manipulation.
- **W-FA.4**: Kernel calculation `im(ι) = ker(λ)` via coefficient identity
  `a_k = b_k = 0 for k > 0, a_0 = b_0`.
- **W-FA.5**: 5-lemma diagram chase to conclude `im(ε) = ker(δ)`.

### Mathlib lemmas / project supports

- `Module.exact_iff_lift` for 5-lemma style.
- Existing `tateAlgebra_isNoetherianRing` (project).
- Existing chain construction (T-CHAIN-* tickets, ✓ done).

### B2 verdict: NO

Wedhorn's proof is fully constructive without domain hypothesis.
Drops `[IsDomain A]` from Lemma 8.33 closure path.

### Downstream effect

Once W-FA closes, the project's `cor_8_32_clean_via_laurent` (if reinstated)
and the F-cluster's `restrictionMap_flat_via_iteratedMinus` chain can be
re-statemented without `[IsDomain A]`. The Path α final assembly T-S1 /
T-FINAL then loses `[IsDomain A]`.

---

### T-WED-FAITHFUL-B — Drop `[IsNoetherianRing P.A₀]` via Wedhorn Cor 8.35

- **Status**: open
- **File**: `Adic spaces/PresheafTateStructure.lean` + Cor832 / StructureSheaf refactor
- **Depends on**: T-FOUND-E (closed via Wedhorn-direct, NOT Stacks 0316)
- **Type**: theorem chain refactor
- **Addresses**: Wedhorn 8.28(b) signature parity — drops the project's `[IsNoetherianRing P.A₀]` parametric

### Statement

Replace all chain consumers of `[IsNoetherianRing P.A₀]` with calls to
`presheafValue_isNoetherianRing_of_strongly_noetherian` (= T-FOUND-E).

```lean
-- New consumer-facing API:
theorem flat_over_base_tate_noNoethA₀
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    (C : RationalCovering A) :
    ∀ D : { D // D ∈ C.covers },
      @Module.Flat (presheafValue C.base) (presheafValue D.1) _ _
        ((restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toModule)
```

**Note**: NO `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` parameter.

### Proof sketch (Wedhorn Cor 8.35, p.85, verbatim)

> "Let A be an f-adic ring satisfying one of the following properties.
> (a) The completion Â has a noetherian ring of definition.
> (b) A is a strongly noetherian Tate ring.
> (c) Â has the discrete topology.
> Then A is stably sheafy.
>
> Proof. If A has one of these properties, then every A-algebra topologically
> of finite type over A has the same property."

For our use:
1. `IsStronglyNoetherian A` ⟹ `presheafValue D₀` strongly noeth Tate (via Cor 8.35 + Ex 6.38).
2. Strongly noeth Tate ⟹ noeth (n = 0 case).
3. **No noeth-A₀ needed**: the Cor 8.35 argument propagates strong-noetherianness
   directly from A to the tft A-algebra `Â⟨T/s⟩`, bypassing the need to
   establish a specific noetherian ring of definition for A.

### Sub-leaves

- **W-FB.1** (= T-FOUND-E.1): `presheafValue D₀ ≃+* Â⟨T/s⟩` (Ex 6.38 correct
  Tate-algebra form, NOT MvPolynomial). Project needs to re-derive the iso
  with the correct ambient structure.
- **W-FB.2** (= T-FOUND-E.2): Wedhorn Cor 8.35: strongly-noeth-Tate
  propagates along tft maps. Substantive Wedhorn-faithful sub-lemma.
- **W-FB.3**: Refactor `restrictionMap_flat_via_iteratedMinus` to use
  W-FB.1 + W-FB.2 directly instead of routing through `IsNoetherianRing P.A₀`.
- **W-FB.4**: Audit all downstream consumers of the existing
  `[IsNoetherianRing P.A₀]` parameter; replace with W-FB-direct version.

### Mathlib lemmas / project supports

- Existing TateAlgebra infrastructure.
- T-FOUND-E (this ticket's prerequisite).
- Existing T-STRONG-NOETH-PRESERVATION (✓ done at single level — needs lifting to general D₀).

### B2 verdict: NO

Wedhorn Cor 8.35 directly applies. The `[IsNoetherianRing P.A₀]` is a
project artifact, not a Wedhorn requirement.

### Downstream effect

Drops `[IsNoetherianRing P.A₀]` from ALL Path α theorems including
`flat_over_base_tate`, `cor_8_32_clean_via_flat`, `hSpa_surj_from_spanTop`,
the IsSheafy assembly. **Massive simplification** of the consumer interface.

---

### T-WED-FAITHFUL-FINAL — Wedhorn 8.28(b) as stated

- **Status**: open
- **File**: `Adic spaces/StructureSheaf.lean:1629`
- **Depends on**: T-WED-FAITHFUL-A, T-WED-FAITHFUL-B, all upstream Layer 0/1/2/3 tickets
- **Type**: theorem (Wedhorn-exact final result)

### Statement

```lean
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] :
    IsSheafy A
```

### Wedhorn source (Theorem 8.28(b), p.81, verbatim)

> "Let A = (A, A⁺) be an affinoid ring and X = Spa A. Assume that A satisfies
> one of the following conditions. [...] (b) A is a strongly noetherian Tate
> ring. [...] Then 𝒪_X is a sheaf of complete topological rings."

### Hypothesis profile vs Wedhorn

| Project hypothesis | Wedhorn requires? | Notes |
|---|---|---|
| `[IsTateRing A]` | ✓ direct (8.28(b)) | matches |
| `[IsNoetherianRing A]` | ✓ implied by IsStronglyNoetherian | matches |
| `[IsStronglyNoetherian A]` | ✓ direct (8.28(b)) | matches |
| `[T2Space A]` | ✓ implied by Tate + complete | matches |
| `[NonarchimedeanRing A]` | ✓ implied by Huber/Tate | matches |
| `[UniformSpace A]` + `[IsUniformAddGroup A]` + `[CompleteSpace A]` | ✓ "we may assume complete" reduction (p.84) | matches via project's Lean translation |
| ~~`[IsDomain A]`~~ | **NO — dropped via T-WED-FAITHFUL-A** | Wedhorn does NOT require this |
| ~~`(P, [IsNoetherianRing P.A₀])`~~ | **NO — dropped via T-WED-FAITHFUL-B** | Wedhorn does NOT require this |

### Proof sketch

Once W-FA and W-FB land, this is a direct re-export of the Path α structure
without the extras. The body is identical to T-S1's proof, but the
hypothesis profile matches Wedhorn 8.28(b) directly.

### Downstream effect

`isSheafy_ofStronglyNoetherianTate` becomes the **Wedhorn-faithful** headline
theorem. The project's signature matches the published statement of
Wedhorn 8.28(b) exactly.

This is the **true definition-of-DONE** for the Tate acyclicity goal.

---

## Dependency graph (visual)

```
T-FINAL                          ← Tate acyclicity final theorem
  └─ T-S1                        ← A1 Path α IsSheafy assembly
       ├─ T-S4 (embedding)
       │    ├─ T-S5
       │    │    └─ T-LAURENT-REFINEMENT-TREE (✓ done)
       │    └─ T-S6
       │         ├─ T-S6a (W2)
       │         │    └─ T-FOUND-D (Cor 7.32 finset)
       │         │         ├─ T-FOUND-C (Cor 7.31)
       │         │         │    └─ T-FOUND-B (Wedhorn 7.35(2))
       │         │         │         └─ T-FOUND-A (Wedhorn 7.35(1))
       │         │         └─ T-FOUND-B
       │         ├─ T-S6b (W3 = P5)
       │         │    ├─ T-DEF1 (in progress: skeleton declared)
       │         │    ├─ T-DEF2
       │         │    ├─ T-DEF3
       │         │    └─ T-FOUND-F (Wedhorn 7.55)
       │         ├─ T-S6c (P4)
       │         │    └─ T-W3-P3
       │         └─ T-S6d (W1)
       │              ├─ T-FOUND-D
       │              └─ T-FOUND-B
       ├─ T-ACYC-D (separation)
       │    └─ T-ACYC-B
       │         └─ T-ACYC-A (B5')
       │              └─ T-FOUND-E (presheafValue noetherian)
       └─ T-ACYC-E (gluing)
            ├─ T-ACYC-B
            ├─ T-ACYC-C (Stacks 023N)
            ├─ T-ACYC-F (gluing via refinement)
            │    └─ T-S6
            └─ T-FOUND-G (Wedhorn 8.30)
                 └─ T-FOUND-E
```

---

## Worker assignment hints

### Independent parallel tracks (can be assigned to different workers immediately):

**Track 0A — Spectral foundation**:
T-FOUND-A → T-FOUND-B → T-FOUND-C → T-FOUND-D

**Track 0B — Noetherian propagation**:
T-FOUND-E (single ticket, ~60 LOC)

**Track 0C — Laurent normalization**:
T-FOUND-F (single ticket, ~30 LOC)

**Track 0D — Stacks 023N descent**:
T-ACYC-C (single ticket, ~100 LOC pure algebra)

**Track 0E — Wedhorn-faithful refactors (after Path α validated)**:
T-WED-FAITHFUL-A (drop IsDomain via μ_M + 5-lemma, ~150 LOC)
T-WED-FAITHFUL-B (drop NoethA₀ via Cor 8.35 chain, ~100 LOC refactor)

### After Layer 0 done, parallel tracks:

**Track 1A — Embedding chain**:
T-DEF1 → T-DEF2 → T-DEF3 → T-W3-P3 → T-S6c → T-S6b
And in parallel: T-S6a (after T-FOUND-D), T-S6d (after T-FOUND-D + T-FOUND-B)

**Track 1B — Acyclicity setup**:
T-ACYC-A → T-ACYC-B (after T-FOUND-E)
T-FOUND-G (after T-FOUND-E)

### Final assembly (serial, single worker):

T-S6 (after all T-S6a..d) → T-S5 → T-S4 → T-ACYC-D → T-ACYC-E → T-ACYC-F → T-S1 → T-FINAL

### Total estimated effort

- **Layer 0 (T-FOUND-*)**: ~400-500 LOC across 7 tickets
- **Layer 1 (Embedding)**: ~600-800 LOC across 10 tickets
- **Layer 2 (Acyclicity)**: ~500-700 LOC across 6 tickets
- **Layer 3 (Final)**: ~50 LOC (assembly)
- **Layer 4 (Wedhorn-faithful, optional)**: ~250-350 LOC across 3 tickets (W-FA, W-FB, W-FINAL)

**Total Path α (DONE)**: ~1500-2000 LOC of new Lean proof, distributable across ~25 tickets.
**Total Wedhorn-faithful (DONE-FAITHFUL)**: ~1750-2350 LOC across ~28 tickets (Path α + Layer 4).

---

## Worker checklist (per ticket)

For each ticket:

1. ☐ Read the full ticket above (Statement, Proof sketch, Mathlib lemmas, Sources)
2. ☐ Read the existing sorry location in the named file
3. ☐ Run `lake build` to confirm baseline is clean
4. ☐ Implement the proof
5. ☐ Run `lake build` to confirm new closure compiles cleanly
6. ☐ Run `#print axioms <theorem_name>` to confirm no `sorryAx` taint
7. ☐ Update this file: mark Status `done` + add Progress note with date + commit hash
8. ☐ Commit with a message referencing the ticket ID

## Definition of DONE for Tate acyclicity

There are TWO levels of DONE depending on hypothesis profile:

### DONE (Path α — with project's extras)

Status reached when T-S1 + T-FINAL close with `[IsDomain A]` + parametric
`(P, [IsNoetherianRing P.A₀])`. Narrower than Wedhorn 8.28(b) but **not false**
per Session 26 reviewer-confirmed decisions. Easier to close given available
infrastructure.

1. `isSheafy_ofStronglyNoetherianTate_flat` (T-S1) at `StructureSheaf.lean:1117` sorry-free.
2. `isSheafy_ofStronglyNoetherianTate` (T-FINAL) at `StructureSheaf.lean:1629` sorry-free.
3. `lake build` clean (3141 jobs).
4. `#print axioms` shows only `[propext, Classical.choice, Quot.sound]`.
5. All Layer 0 / 1 / 2 / 3 tickets above are status `done`.

### DONE-FAITHFUL (Wedhorn 8.28(b) as stated)

Status reached when T-WED-FAITHFUL-FINAL closes WITHOUT `[IsDomain A]` and
WITHOUT `(P, [IsNoetherianRing P.A₀])`. This is the **published Wedhorn
statement** — strongly noeth Tate alone.

1. `isSheafy_ofStronglyNoetherianTate` (T-WED-FAITHFUL-FINAL) at
   `StructureSheaf.lean:1629` sorry-free, matching Wedhorn 8.28(b)
   hypothesis profile.
2. All Layer 0 / 1 / 2 / 3 / 4 tickets done.
3. T-WED-FAITHFUL-A done (Lemma 8.33 via Wedhorn's μ_M + 5-lemma, no Krull).
4. T-WED-FAITHFUL-B done (Cor 8.35 propagation closed).
5. Project's signature matches Wedhorn p.81 published statement.

**Recommended sequencing**: close DONE (Path α) first to validate the proof
infrastructure end-to-end. Then refactor to DONE-FAITHFUL by closing
T-WED-FAITHFUL-A/B and dropping the extras from the consumer interface.
