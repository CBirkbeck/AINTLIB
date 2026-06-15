# Tate Acyclicity Tickets — Clean IsSheafy Path (Wedhorn 8.28b)

Methodical ticket plan. Target: `ValuationSpectrum.isSheafy_ofStronglyNoetherianTate` (clean — no `IsDomain`, no explicit `PairOfDefinition`).

For each ticket: Wedhorn page + ref · statement-check · existing repo helpers · sub-breakdown · dependencies · effort.

**Audit findings before tickets**:
- `RationalSubsets.lean:72` already has `rationalOpen_inter` (Wedhorn 7.30(5)) — **my added `rationalOpen_inter_eq_rationalOpen` (A.3) is REDUNDANT**, delete it.
- `ValuationSpectrumCompact.lean:698` has `isClosed_vleOfBool` (bool-side closedness). Useful for A.2.
- `EmbeddingTopo.lean:2007` already has `productRestrictionSub_isInducing_via_tree` (LaurentTree, splits + disjoint hypotheses). Powers Gap B.
- `Cor832.lean:1025` has `productRestriction_faithfullyFlat_tate_of_hSpa_points` with `hSpa_points` hypothesis. Powers Gap A.
- `Lemma745.lean` has `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Wedhorn 7.45, no hArch). Powers L.1 non-open case.
- `AdicSpectrum.lean:157` has `exists_mem_spa_supp_eq` (Prop 7.51 for open maximal). Powers L.1 open case.

---

## Phase A — Half-space compactness (Sorry #1)

### T-A.1 `setOf_vle_eq_basicOpen_union_supp`
- **File**: `SpaCompactNoHArch.lean:198`
- **Wedhorn**: Not directly stated — Lean-side set-theoretic identity.
- **Statement** (corrected this turn): `{v | v.vle g h} = basicOpen g h ∪ {v | v.vle g 0}`.
- **Mathematical check** ✓: `v(g) ≤ v(h)` ↔ either `v(h) ≠ 0` (basicOpen) OR `v(g) = 0` (right side automatically gives `v(g) ≤ v(h)`).
- **Existing helpers**: `Spv.vle_total` (totality), `Spv.basicOpen` definition (`AdicSpectrum.lean:230`).
- **Sub-breakdown**: none. Single 5–10-line tactic proof via set extensionality + LEM on `v.vle h 0`.
- **Dependencies**: none.
- **Effort**: ~10 lines.

### T-A.2 `isClosed_setOf_vle_zero`
- **File**: `SpaCompactNoHArch.lean:207`
- **Wedhorn**: Not directly stated — Spv-side closedness of support.
- **Statement**: `IsClosed {v : Spv A | v.vle g 0}`.
- **Mathematical check** ✓: `v.vle g 0` ↔ `v(g) = 0` ↔ `g ∈ supp v`. The support map `Spv A → Spec A` is continuous (well-known), and `{p | g ∈ p}` = `V({g})` is closed in Spec.
- **Existing helpers**:
  - `ValuationSpectrumCompact.lean:698` `isClosed_vleOfBool` — bool-side analogue (could pull back via `ιSpv_bool`).
  - `Spv.basicOpen` and complement reasoning.
  - Direct support-map approach: need `Spv.support_continuous : Continuous (·.supp : Spv A → PrimeSpectrum A)` — check if exists; likely yes.
- **Sub-breakdown**: none. ~10 lines either way.
- **Dependencies**: none.
- **Effort**: ~10–15 lines.

### T-A.3 — DELETED (redundant with existing `rationalOpen_inter`)
- **Action**: remove the `rationalOpen_inter_eq_rationalOpen` signature; downstream tickets (A.5) use existing `RationalSubsets.lean:72` `rationalOpen_inter` instead.

### T-A.4 `isCompact_preimage_rationalOpen_noHArch`
- **File**: `SpaCompactNoHArch.lean:227`
- **Wedhorn**: Theorem 7.35(2) (p.64): rational subsets form a basis of QC opens of `Spa A`, stable under finite intersection.
- **Statement**: `IsCompact (Subtype.val ⁻¹' rationalOpen T s : Set ↥(Spa A A⁺))`.
- **Match check**: ✓ matches Wedhorn 7.35(2) for the single rational subset case.
- **Existing helpers**:
  - `SpaCompact.lean:586` `isCompact_preimage_rationalOpen_of_tate_pseudouniformizer` — same statement WITH hArch.
  - `SpaCompact.lean:455` `image_spa_ιSpv_bool_of_tate` — bool-image characterization with hArch.
- **Sub-breakdown**: YES. Needs the Spv(A,I)-spectrality route:
  - **T-A.4.a** `Spa.eq_Cont_inter_basicOpens` (Wedhorn 7.35(1) statement): `Spa A = Cont(A) ∩ ⋂_{a ∈ A⁺} Spv(A, I)(a/1)` — not yet stated.
  - **T-A.4.b** `Spa.isSpectralSpace` (Wedhorn 7.35(1)): `Spa A` carries spectral topology — not yet stated.
  - **T-A.4.c** Compose: rational subset is intersection of spectral basis elements → QC by spectral-space axioms.
- **Dependencies**: T-A.4.a, T-A.4.b → Phase Spv (W7.5 spectrality of `Spv(A, I)`).
- **Effort**: T-A.4 itself is ~5 lines once T-A.4.a/b land; the supporting Spv chain is substantial (~150 lines total — see Phase Spv).

### T-A.5 `isCompact_preimage_rationalOpen_inter_basicOpen_noHArch`
- **File**: `SpaCompactNoHArch.lean:233`
- **Wedhorn**: Combines 7.30(5) (rational intersection is rational) + 7.35(2) (rational is QC).
- **Statement**: `IsCompact (Subtype.val ⁻¹' (rationalOpen L.T L.s ∩ basicOpen g h) : Set ↥(Spa A A⁺))`.
- **Match check** ✓. `basicOpen g h = R({g}/h)` (when `h ∉ T` and we expand using 7.30(3)); intersection rewrites to a rational subset.
- **Existing helpers**:
  - `RationalSubsets.lean:72` `rationalOpen_inter` — direct.
  - `RationalSubsets.lean` probably has `rationalOpen_insert_self` (7.30(3)).
  - T-A.4 — for QC of the result.
- **Sub-breakdown**: none. Direct from `rationalOpen_inter` (after recognizing `basicOpen g h = rationalOpen {g, h} h`) + T-A.4.
- **Dependencies**: T-A.4. Needs `rationalOpen_inter`'s `s ∈ T` hypothesis to apply (check that `h ∈ {g, h}` is trivial).
- **Effort**: ~15–20 lines.

### T-A.6 `isCompact_preimage_rationalOpen_inter_setOf_vle_zero_noHArch`
- **File**: `SpaCompactNoHArch.lean:241` (corrected this turn, was `h`, now `g`)
- **Wedhorn**: Compactness of closed subset of QC.
- **Statement**: `IsCompact (Subtype.val ⁻¹' (rationalOpen L.T L.s ∩ {v | v.vle g 0}) : Set ↥(Spa A A⁺))`.
- **Match check** ✓. Standard: closed (T-A.2) ∩ QC (T-A.4) = QC by `IsCompact.inter_left`/`IsCompact.of_isClosed_subset`.
- **Existing helpers**: Mathlib `IsCompact.inter_right`.
- **Sub-breakdown**: none. ~5 lines.
- **Dependencies**: T-A.2, T-A.4.
- **Effort**: ~5 lines.

### T-A.0 (PARENT) `isCompact_rationalOpen_inter_vle_noHArch`
- **File**: `SpaCompactNoHArch.lean:186`
- **Wedhorn**: Combines 7.30(5) + 7.35(2).
- **Statement**: `IsCompact (Subtype.val ⁻¹' (rationalOpen L.T L.s ∩ {v | v.vle g h}) : Set ↥(Spa A A⁺))`.
- **Match check** ✓. Decomposition: A.1 split + A.5 + A.6 + `IsCompact.union`.
- **Existing helpers**: Mathlib `IsCompact.union`, `Set.preimage_union`.
- **Sub-breakdown**: none. ~5–10 lines.
- **Dependencies**: T-A.1, T-A.5, T-A.6.
- **Effort**: ~10 lines.

---

## Phase Spv — Spv(A,I) spectrality (powers T-A.4)

### T-Spv.1 `SpvAI.rationalSubset_isBasis`
- **File**: `SpvAITopology.lean:472`
- **Wedhorn**: Lemma 7.5(1) (p.57): the sets `Spv(A,I)(T/s)` form a basis of QC opens of `Spv(A,I)`, stable under finite intersection.
- **Statement** (as added):
  ```
  TopologicalSpace.IsTopologicalBasis (SpvAI.topology I)
    { U | ∃ T s, I ≤ (Ideal.span (T ∪ {s})).radical ∧
                 U = Subtype.val ⁻¹' SpvAI.rationalSubset I T s }
  ```
- **Match check**: ✓ — but verify `I ≤ √(T·A)` matches Wedhorn's `I ⊆ √(T·A)`.
- **Existing helpers**: `SpvAI.rationalSubset_inter` (62 — already proved for ∩-stability), `SpvAI.exists_rationalSubset` (376 — basis ↦ exists).
- **Sub-breakdown**: none. ~30–50 lines combining existing helpers.
- **Dependencies**: none (uses existing).
- **Effort**: ~40 lines.

### T-Spv.2 `SpvAI.isSpectralSpace`
- **File**: `SpvAITopology.lean:497`
- **Wedhorn**: Lemma 7.5(1)(iv) (p.58): `Spv(A,I)` is a spectral space (proof via constructible topology on `Spv A` + Proposition 3.31).
- **Statement**:
  ```
  CompactSpace (SpvAI A I) ∧ T0Space (SpvAI A I) ∧ QuasiSober (SpvAI A I)
  ```
- **Match check**: ⚠️ Wedhorn's proof goes through `(Spv A)_cons` (constructible topology) and Mathlib's `PrespectralSpace`/`QuasiSober`. The Mathlib lemma `IsSpectralSpace` may need different decomposition.
- **Existing helpers**:
  - `ValuationSpectrumCompact.lean:545` references Spv-spectrality scaffold.
  - `Mathlib.Topology.Sober` for `QuasiSober`.
- **Sub-breakdown**: YES. ~3 sub-tickets:
  - **T-Spv.2.a** `Spv.compactSpace_cons` — constructible topology compact (Wedhorn 3.23). Likely exists or via Tychonoff cube.
  - **T-Spv.2.b** `SpvAI.surjective_from_cons` — retraction continuous + surjective in constructible topology.
  - **T-Spv.2.c** Apply Mathlib `IsSpectralSpace.of_*` constructor.
- **Dependencies**: T-Spv.1.
- **Effort**: ~100–150 lines total.

### T-Spv.3 (cluster) Retraction lemmas (W7.5(2)/(3))
Added: `restrictIdeal_mem_SpvAI`, `SpvAI.retraction` (def), `SpvAI.retraction_eq_self`, `SpvAI.retraction_continuous`, `SpvAI.retraction_preimage_rationalSubset`, `SpvAI.retraction_ideal_ne_zero`. All in `SpvAITopology.lean:413–470`.

- **Wedhorn**: Lemma 7.5(2)(3) (p.57).
- **Match check** ✓ each one.
- **Existing helpers**: `Valuation.restrictIdeal` already in `CharacteristicSubgroup.lean`; the Spv-side typed retraction is the main novelty.
- **Sub-breakdown**: each is bite-size on its own; the spectrality of `retraction` (T-Spv.3.b inside the cluster) is the hardest, ~50 lines.
- **Dependencies**: T-Spv.1 (basis), `cGammaIdeal_eq_top_iff_cofinalFor_top` (W7.4 — see Phase Cofinality).
- **Effort**: ~150 lines for the cluster.

### T-Spv.4 (cluster) Cont(A) in Spv(A,I) (W7.10, W7.12)
Added: `cont_eq_spvAI_inter_lt_one` (`SpvAI.lean:415`), `cont_isClosed_in_SpvAI` (`SpvAITopology.lean:524`), `cont_isSpectralSpace` (`SpvAITopology.lean:534`).

- **Wedhorn**: Theorem 7.10 (p.59), Corollary 7.12 (p.59).
- **Match check** ✓.
- **Existing helpers**: `Spv.isContinuous_of_isInSpvAI_of_lt_one` (`SpvAI.lean:294` — one direction proved), `Spv.cofinalValue_of_isContinuous` (374 — other direction proved).
- **Sub-breakdown**: combining the two direction lemmas + the SpvAI basis to deduce subset equality (W7.10) is ~30 lines. Closedness (W7.12) is the complement-of-union (open) argument ~20 lines.
- **Dependencies**: T-Spv.1 (basis for the union complement).
- **Effort**: ~60 lines combined.

### T-Spv.5 (cluster) Wedhorn 7.1/7.2/7.4 — cofinality ideal + cGamma characterizations
Added: `CofinalFor` (def), `cofinalityIdeal` (def, sorry), `mem_cofinalityIdeal`, `cofinalityIdeal_radical_eq_self`, `exists_greatest_cofinalFor_subgroup_of_ideal`, `cGammaIdeal_eq_top_iff_cofinalFor_top`, `cofinalFor_all_iff_cofinalFor_generators`. In `CharacteristicSubgroup.lean:561–608`.

- **Wedhorn**: Lemma 7.1 (p.56), Lemma 7.2 (p.56), Lemma 7.4 (p.57).
- **Match check** ⚠️ for `cofinalityIdeal` def — the H parameter is convex; my def uses `ConvexSubgroup Γ₀ˣ`. Verify radicality proof closes the way Wedhorn does (uses convex absorbing for `v(b) > 1` case).
- **Existing helpers**:
  - `CharacteristicSubgroup.lean` `cGammaIdealUnits`, `cGammaIdeal` (Definition 7.3 already).
  - `Valuation.CofinalValue` (SpvAI.lean:56 — case H = ⊤).
- **Sub-breakdown**: each Wedhorn lemma is direct, ~20–40 lines each. The greatest-subgroup existence (7.2) is the longest ~60 lines.
- **Dependencies**: none (uses existing convex-subgroup machinery).
- **Effort**: ~200 lines total for the cluster.

### T-Spv.6 `Spv.IsInSpvAI` characterization for retraction (auxiliary)
- **File**: `SpvAITopology.lean:413` (`restrictIdeal_mem_SpvAI`)
- **Wedhorn**: Definition 7.3 (`cΓ_v(I)`) + Lemma 7.4 disjunction (already in project as `Spv.IsInSpvAI`).
- **Match check** ✓. The retraction's image lies in `Spv(A,I)` by construction.
- **Existing helpers**: `Spv.IsInSpvAI` (SpvAITopology.lean:83). The proof composes `cGammaIdeal_eq_top_iff_cofinalFor_top` (T-Spv.5) with the retraction structural property.
- **Effort**: ~30 lines.

---

## Phase B — Cor 7.32 no-hArch (powers P6)

### T-B.1 `exists_zero_nbhd_lt_on_qc` (Wedhorn 7.31)
- **File**: `Cor732.lean:307`
- **Wedhorn**: Lemma 7.31 (p.63).
- **Statement**: `∃ I open nbhd of 0, ∀ a ∈ I, ∀ x ∈ X, v(a) < v(f)`.
- **Match check** ✓ matches Wedhorn 7.31.
- **Existing helpers**:
  - Wedhorn's proof uses `T ⊆ A°°` (system of generators of A°°), constructs `X_n := {x : v(t) ≤ v(f), t ∈ T^n}`, uses QC of X to extract finite subcover. Then `I := T^m · A°°`.
  - Project: `A°°` = topologically nilpotent ideal — exists in `Bounded.lean` or `HuberRings.lean`.
- **Sub-breakdown**: 2 atomic sub-lemmas:
  - **T-B.1.a** `IsOpen.exists_subset_dominated_finset` — for QC `X` ⊆ Spa, `f` nonvanishing, ∃ finite `T ⊆ A°°` with each `t ∈ T^m` satisfying `v(t) ≤ v(f)` on `X`. (Open-cover argument on `X_n` increasing union.)
  - **T-B.1.b** Wrap as `T^m · A°°` is the desired open nbhd of `0`.
- **Dependencies**: T-A.4 if `X = rationalOpen` (which is what's used in practice).
- **Effort**: ~50 lines.

### T-B.2 `exists_dominating_unit_noHArch` (Wedhorn 7.32, set form)
- **File**: `Cor732.lean:317`
- **Wedhorn**: Corollary 7.32 (p.63).
- **Statement**: `Y QC, |s| ≠ 0 ⇒ ∃ π : Aˣ, |π| < |s|`.
- **Match check** ✓.
- **Existing helpers**: `Cor732.lean:206` `exists_dominating_unit` (with hArch). Proof in Wedhorn: apply 7.31 with `f = s` to get nbhd `I` of `0`, then use Tate axiom `∃ unit π ∈ I` (every nbhd of 0 contains a unit in Tate).
- **Sub-breakdown**: 1 sub-lemma:
  - **T-B.2.a** `Tate.exists_unit_in_zero_nbhd` — Wedhorn p.63 cites "as A is Tate, there exists a unit π of A in I." This is the Tate axiom in action. Likely exists in `HuberRings.lean` or `IsTateRing` API.
- **Dependencies**: T-B.1.
- **Effort**: ~20 lines.

### T-B.3 `exists_dominating_unit_noHArch_finset` (for P6)
- **File**: `Cor732.lean:325`
- **Wedhorn**: Derived from 7.32 — not directly stated by Wedhorn.
- **Statement**: For finite T with no common zero on Spa, ∃ s : Aˣ, ∀ v, ∃ t ∈ T, v(s) < v(t).
- **Match check** ✓ matches existing `exists_dominating_unit` shape (B.2's finset form).
- **Existing helpers**: `Cor732.lean:206` is the hArch finset form (proof structure transports). Uses `exists_dominatedBy_cover` (line 154).
- **Sub-breakdown**: same as the existing proof but with T-A.4 (no-hArch Spa compact) instead of `instCompactSpace_spa_of_tate_pseudouniformizer hArch`.
- **Dependencies**: T-A.4, T-B.2 (via per-point application).
- **Effort**: ~50 lines (mostly mimicking existing proof).

---

## Phase C — Lemma 7.54 cover refinement (P7)

### T-C.1 — DELETE (unnecessary intermediate)
- **Action**: Remove `exists_finite_rationalOpen_subcover`. Wedhorn 7.54 proves the result without an explicit "finite rational subcover" intermediate step (it cites [Hu3] 2.6 which does it in one shot).

### T-C.2 — RENAME to T-754-MAIN
- **Action**: `exists_ideal_generators_dominating_subcover` becomes the single main Lemma-7.54 statement, with its hypothesis adjusted to match Wedhorn's:
  ```
  Wedhorn 7.54: (V_j)_{j∈J} open cover of Spa A ⇒ ∃ f_0,…,f_n generating A as ideal,
    each R((f_0,…,f_n)/f_i) ⊆ some V_j.
  ```
- **Statement to add** (corrected, single main):
  ```lean
  theorem exists_ideal_generators_refining_cover
      (C : RationalCovering A) :
      ∃ S : Finset A,
        Ideal.span (S : Set A) = ⊤ ∧
        (∀ v ∈ rationalOpen C.base.T C.base.s, ∃ f ∈ S, v ∈ rationalOpen S f) ∧
        ∀ f ∈ S, ∃ E ∈ C.covers, rationalOpen S f ⊆ rationalOpen E.T E.s
  ```
- **Wedhorn**: Lemma 7.54 (p.70). Proof cited as [Hu3] Lemma 2.6 — external.
- **Match check** ✓ matches Wedhorn.
- **Existing helpers**: Cor 7.53 (P implies cover; not yet stated but follows from 7.52(2)); QC of Spa (T-A.4).
- **Sub-breakdown**: this is a single Wedhorn lemma whose proof is external; we can either:
  - (a) port [Hu3] Lemma 2.6 directly (~100 lines)
  - (b) state as a sorry leaf and accept it as a single non-decomposable lemma
- **Dependencies**: T-A.4.
- **Effort**: ~100 lines (option a), or 1-line sorry (option b).

### T-C.3 `exists_standard_cover_refining_via_754` (= P7)
- **File**: `TateAcyclicityResiduals.lean:266`
- **Wedhorn**: 7.54 packaged for the project's `refines_cover ∧ refines_contain ∧ refines_span_top` predicates.
- **Statement**: identical to existing `exists_standard_cover_refining` (P7) at line 210.
- **Match check** ✓.
- **Existing helpers**: T-C.2.
- **Sub-breakdown**: bookkeeping after T-C.2 lands.
- **Dependencies**: T-C.2.
- **Effort**: ~30 lines.

---

## Phase Spa-Points — L.1 (powers Cor 8.32 clean)

### T-L.1 `exists_spa_point_in_rationalOpen_of_prime`
- **File**: `StructureSheaf.lean:681`
- **Wedhorn**: Combines 7.51 (max ideal closed + Spa-point exists) with 7.45 (non-open prime case).
- **Statement**: `∀ p prime, C.base.s ∉ p → ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp`.
- **Match check** ✓.
- **Existing helpers**:
  - `StructureSheaf.lean:602` `exists_spa_point_in_rationalOpen_of_isOpen_prime` (open prime case, done).
  - `Lemma745.lean` `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma 7.45, done).
  - `AdicSpectrum.lean:157` `exists_mem_spa_supp_eq` (Prop 7.51 for maximal ideals).
- **Sub-breakdown**: 1 sub-step:
  - **T-L.1.a** Case `IsOpen (↑p)`: use the open-prime helper.
  - **T-L.1.b** Case `¬ IsOpen (↑p)`: use Lemma 7.45 (via `presheafValue_pairOfDefinition` instance).
- **Dependencies**: none (uses existing).
- **Effort**: ~30 lines.

---

## Phase H, I, J, K — Final assembly

### T-H.2 `hasLocLiftPowerBounded_of_stronglyNoetherianTate` (instance)
- **File**: `StructureSheaf.lean:1297`
- **Wedhorn**: Not directly stated (project-internal typeclass).
- **Statement**: `HasLocLiftPowerBounded A` from strong-noeth-Tate hypothesis.
- **Match check**: project-internal. `HasLocLiftPowerBounded` is a project predicate; need to verify it follows from strong-noetherian Tate.
- **Existing helpers**: Tickets #38 (T-LOCLIFT-PRESERVATION) is the open project ticket for this exact thing. Status: pending.
- **Sub-breakdown**: needs definition of `HasLocLiftPowerBounded` audit. Likely 1–2 sub-lemmas about `Localization.Away` of A having `≤ 1` valuations.
- **Dependencies**: existing `IsStronglyNoetherian` API.
- **Effort**: unclear without auditing `HasLocLiftPowerBounded` definition. Estimate ~50 lines.

### T-I.1 `exists_pairOfDefinition_isNoetherian_of_stronglyNoetherianTate`
- **File**: `StructureSheaf.lean:1304`
- **Wedhorn**: Strongly noetherian Tate definition includes "has noetherian ring of definition" — implicit in Wedhorn 8.28(b).
- **Statement**: `∃ P : PairOfDefinition A, Nonempty (IsNoetherianRing P.A₀)`.
- **Match check** ✓.
- **Existing helpers**: `IsStronglyNoetherian` definition + `IsTateRing.principalPair` (in HuberRings.lean).
- **Sub-breakdown**: none. Direct existence proof from the definition.
- **Effort**: ~10 lines.

### T-J.1 `tateAcyclicity_separation_via_cor832`
- **File**: `StructureSheaf.lean:1327`
- **Wedhorn**: 8.32 + 8.30 give injectivity of `M → ∏ M_D`.
- **Statement**: `∀ x, (∀ D hD, restrict x = 0) → x = 0`.
- **Match check** ✓.
- **Existing helpers**: T-GapA (`productRestriction_faithfullyFlat_tate_clean`), Mathlib `Module.FaithfullyFlat.algebraMap_injective`.
- **Sub-breakdown**: none, direct application.
- **Dependencies**: T-GapA.
- **Effort**: ~10 lines.

### T-K.1 `faithfullyFlat_descent_equalizer` (Stacks 023N)
- **File**: `StructureSheaf.lean:1340`
- **Wedhorn**: not stated directly — references "faithfully flat descent" / Stacks 023N.
- **Statement**: For faithfully flat `φ : R → S` and `s ∈ S` satisfying the cocycle condition (`1 ⊗ s = s ⊗ 1`), `∃ r : R, algebraMap r = s`.
- **Match check** ⚠️: real Stacks 023N is about MODULE descent, not just element existence. The element form follows from the module equalizer property.
- **Existing helpers**: Mathlib `Module.FaithfullyFlat.equalizer` — check if exists.
- **Sub-breakdown**: maybe upstream from Mathlib if doesn't exist; otherwise sub-lemmas about tensor-product equalizer.
- **Dependencies**: Mathlib search needed.
- **Effort**: 10 lines if Mathlib has it; ~50 lines otherwise.

### T-K.2 `tateAcyclicity_gluing_via_descent`
- **File**: `StructureSheaf.lean:1357`
- **Wedhorn**: combines K.1 with Cor 8.32.
- **Statement**: gluing from compatible local sections.
- **Match check** ✓ matches the IsSheafy `gluing` field shape.
- **Existing helpers**: T-K.1, T-GapA.
- **Sub-breakdown**: 1–2 sub-lemmas to reduce compatibility to the K.1 cocycle.
- **Dependencies**: T-K.1, T-GapA.
- **Effort**: ~50 lines.

### T-GapA `productRestriction_faithfullyFlat_tate_clean`
- **File**: `StructureSheaf.lean:1317`
- **Wedhorn**: Corollary 8.32 (p.83).
- **Statement**: `∃ alg_inst, Module.FaithfullyFlat (presheafValue C.base) (∀ D, presheafValue D)`.
- **Match check** ✓.
- **Existing helpers**: `Cor832.lean:1025` `productRestriction_faithfullyFlat_tate_of_hSpa_points` (hSpa form).
- **Sub-breakdown**: discharges `hSpa_points` via T-L.1; discharges `P : PairOfDefinition` via T-I.1.
- **Dependencies**: T-L.1, T-I.1.
- **Effort**: ~20 lines.

### T-GapB `productRestrictionSub_isInducing_tate`
- **File**: `StructureSheaf.lean:1378`
- **Wedhorn**: 8.34 topological version (not stated explicitly by Wedhorn but follows from 8.33 topological strictness + Lane C transfer).
- **Statement**: `Topology.IsInducing (productRestrictionSub A C)` for all `C`.
- **Match check** ✓ matches what IsSheafy's `embedding` needs.
- **Existing helpers**:
  - `EmbeddingTopo.lean:2007` `productRestrictionSub_isInducing_via_tree` (LaurentTree form, done).
  - `EmbeddingTopo.lean` T286 (done, #57).
  - P8 (`exists_wedhorn_ratio_laurent_refinement_tree_realized`) — provides the τ-refinement.
- **Sub-breakdown**: 1 sub-lemma:
  - **T-GapB.1** `productRestrictionSub_isInducing_via_ratio_tree` — RatioLaurentTree version of `via_tree`. Referenced in `TateAcyclicityResiduals.lean:67` but not defined.
- **Dependencies**: T-P8 (transitively), `via_tree` (existing), T286 (existing).
- **Effort**: ~50 lines for GapB.1; T-GapB itself is ~10 lines on top.

---

## Phase P3–P8 — Existing parametric sorries (kept as-is, with inner decomposition)

### T-P3 `relative_ratio_split_transports_to_RatioNodeData`
- **File**: `TateAcyclicityResiduals.lean:1241`
- **Wedhorn**: Decomposition step inside Wedhorn 8.34(iii) for ratio refinement.
- **Status**: HAS proof body using `exists_absolute_ratio_rationalLocData_aux` (line 893). That uses `exists_ideal_pow_generators_dominated_for_half_space` (line 678) which uses **T-A.0** (parent half-space sorry).
- **Sub-breakdown**: NONE — proof body is complete once T-A.0 lands.
- **Dependencies**: T-A.0.
- **Effort**: 0 (closes automatically when T-A.0 lands).

### T-P4 `relative_laurent_tree_to_absolute`
- **File**: `TateAcyclicityResiduals.lean:1571` (approx)
- **Wedhorn**: W3-transport, decomposition step.
- **Status**: literal sorry at line 1632, inside named theorem.
- **Sub-breakdown**: structural recursion on `RatioLaurentTree`. The leaf-level uses unitCover→C chain; internal-node recursion uses P3.
- **Dependencies**: T-P3.
- **Effort**: ~30 lines.

### T-P5.outer + T-P5.inner1 + T-P5.inner2 `unitGeneratedCover_has_relative_ratioLaurentRefinement`
- **File**: `TateAcyclicityResiduals.lean:1483`
- **Wedhorn**: Lemma 8.34(iii) — unit-generated rational cover has Laurent refinement.
- **Status**: outer has proof body that delegates to 3 sub-properties; 2 are inner sorries (1557, 1568); the 3rd is closed.
- **Sub-breakdown**:
  - **T-P5.inner1** (line 1557): leaf σ-vector → max unit picks containing piece. Pigeonhole argument. ~30 lines.
  - **T-P5.inner2** (line 1568): per-pair Lane C inducing. Uses T286 (done). ~30 lines.
- **Dependencies**: T286 (done).
- **Effort**: ~60 lines total.

### T-P6 `exists_first_stage_laurent_tree_unit_generated`
- **File**: `TateAcyclicityResiduals.lean:1377`
- **Wedhorn**: Lemma 8.34(ii).
- **Status**: sorry'd. Uses Cor 7.32 currently with hArch — needs T-B.3.
- **Sub-breakdown**: Wedhorn proof is 3-line — direct application of Cor 7.32 (no-hArch version T-B.3).
- **Dependencies**: T-B.3.
- **Effort**: ~30 lines (mostly setup, then 3-line Wedhorn argument).

### T-P7 `exists_standard_cover_refining`
- **File**: `TateAcyclicityResiduals.lean:210`
- **Wedhorn**: Lemma 7.54.
- **Status**: sorry'd.
- **Dependencies**: T-C.3 (which depends on T-C.2 = Lemma 7.54).
- **Effort**: ~5 lines once T-C.3 lands.

### T-P8 `exists_wedhorn_ratio_laurent_refinement_tree_realized`
- **File**: `TateAcyclicityResiduals.lean:1759`
- **Wedhorn**: Lemma 8.34 final assembly (= 8.34(iv)).
- **Status**: sorry'd.
- **Sub-breakdown**: composition of P3, P4, P5, P6, P7.
- **Dependencies**: T-P3, T-P4, T-P5.outer, T-P6, T-P7.
- **Effort**: ~30 lines composition.

---

## Phase Top — Clean IsSheafy

### T-H.1 `isSheafy_ofStronglyNoetherianTate`
- **File**: `StructureSheaf.lean:1387`
- **Wedhorn**: Theorem 8.28(b) (p.81) — "O_X is a sheaf of complete topological rings."
- **Statement**: `IsSheafy A` from strong-noeth-Tate hypotheses only.
- **Match check** ✓ matches Wedhorn 8.28(b) (sheafy half; H^q vanishing skipped per user instruction).
- **Sub-breakdown**: `IsSheafy.mk ⟨embedding, gluing⟩`:
  - `embedding`: `IsEmbedding.mk ⟨inducing, injective⟩`:
    - inducing ← T-GapB
    - injective ← T-J.1
    - empty-cover edge case ← `presheafValue_subsingleton_of_s_eq_zero` (existing)
  - `gluing` ← T-K.2
- **Dependencies**: T-H.2 (instance), T-GapB, T-J.1, T-K.2.
- **Effort**: ~30–50 lines for the case-split + composition.

---

## Composite graph

```
T-A.1 ──┐
T-A.2 ──┤
T-A.4 (depends on Spv chain) ──┐
T-A.5 ──┤  ─────────────────────┤
T-A.6 ──┤  ─────────────────────┤
        ↓                       ↓
       T-A.0 (PARENT) ──→ T-P3 ──→ T-P4 ──┐
                                          │
T-B.1 → T-B.2 → T-B.3 ──→ T-P6 ──┐        │
                                  │        │
T-C.2 → T-C.3 ──→ T-P7 ──────────┤        │
                                  │        │
T-P5.inner1, inner2 → T-P5 ──────┤        │
                                  ↓        ↓
                                  T-P8 ────┘
                                  ↓
T-L.1 → T-GapA → T-J.1            T-GapB (depends on T-P8)
       ↓                          ↓
T-I.1 ─┘                          │
T-H.2 ──→ T-K.1, T-K.2            │
                                  ↓
                           T-H.1 (FINAL)
```

# Workable order (no surprises)

1. **Easy leaves**: T-A.1, T-A.2, T-A.6, T-L.1, T-I.1, T-J.1 (one-liners after dependencies).
2. **Medium**: T-A.5, T-B.1, T-B.2, T-K.1, T-K.2, T-GapA, T-C.3, T-P5.inner1, T-P5.inner2.
3. **Substantial**: T-B.3, T-C.2 (Lemma 7.54 — could port [Hu3] or sorry-leaf), T-Spv.1, T-Spv.2, T-Spv.3, T-Spv.4, T-Spv.5, T-H.2 (lift-power), T-GapB.1.
4. **Composition**: T-A.4 (after Spv), T-A.0, T-P3 (trivial after A.0), T-P4, T-P6, T-P7, T-P8.
5. **Final**: T-H.1.

# Open audit notes

- **Cleanup**: delete T-A.3 (= `rationalOpen_inter_eq_rationalOpen`, redundant with existing `rationalOpen_inter`).
- **Cleanup**: drop T-C.1 (`exists_finite_rationalOpen_subcover`, unnecessary intermediate; Wedhorn 7.54 is monolithic).
- **Confirm**: T-Spv chain (W7.1, W7.2, W7.4, W7.5(1)/(2)/(3), W7.10, W7.12) is genuinely needed for T-A.4 (Spv(A,I) route). Alternative: fix bool encoding directly — would replace Phase Spv entirely with one big lemma.
- **Confirm**: T-K.1 Mathlib coverage. If Mathlib already has `Module.FaithfullyFlat.equalizer` or equivalent, T-K.1 is 1-line.
- **adicCompletion_noetherian**: NOT on IsSheafy critical path (per user instruction). Leave it as-is; it's only needed for some downstream Cor 8.35 / Wedhorn 7.49 work.
