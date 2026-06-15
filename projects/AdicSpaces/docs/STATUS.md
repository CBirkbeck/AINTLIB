# Project Status

> **Agents: Read this file before starting work. Update it when you begin or complete a task.**
>
> Last updated: 2026-05-18 (Wedhorn 6.18 L1 chain closed via mathlib delegation; sessions 2-4: trivial-direction splits + K.1 chain closed + isPowerBounded discrete + mulArchimedean closure + multiple B2 logs)

## Recent progress (2026-05-18 session)

The Wedhorn §6.3 "Banach's theorem for Tate rings" chain made substantial
progress:

- **T-WEDHORN-618-L1** (`AddMonoidHom.isOpenMap_of_completeSpace_of_countablyGenerated`):
  **AXIOM-CLEAN** via delegation to mathlib's
  `AddMonoidHom.isOpenMap_of_sigmaCompact` (commit `3a7ce47`). Added
  `[SigmaCompactSpace G]` per BINDING-RULE (b) — original statement is
  B2 false without it (counterexample: G = ℝ-discrete, H = ℝ-Euclidean,
  f = id). See `.mathlib-quality/b2_log.jsonl` entry 3.
- **T-WEDHORN-618-L2-616** (`wedhorn_6_16`): **AXIOM-CLEAN** with the
  cascaded `[SigmaCompactSpace M]` hypothesis.
- **wedhorn_6_18_continuous** (L4.2): **AXIOM-CLEAN** with the cascade.
- **`banach_two_of_three`**: directions 1 and 3 **AXIOM-CLEAN**;
  direction 2 documented as B2 false (counterexample G=2ℤ↪H=ℤ discrete).
  Direction 3 closure (`d5bcdea`) uses `QuotientAddGroup.completeSpace_right`
  + `Equiv.isUniformEmbedding` + `completeSpace_congr`.

Cleanup work: 6 obsolete sorries deleted across the chain:
- Sub-lemmas B (`_sub_lemma_countable_cover`), C (`_sub_lemma_approx_preimage`),
  D (`_sub_lemma_cauchy_lift`), C.1 (`_sub_sub_lemma_C_1_countable_closed_cover`)
  in `BanachOMT.lean` — dead code after main switched to mathlib delegation,
  AND B / C.1 were B2 false (commit `ddeb5dc`).
- `_sub_lemma_L3_2_baire_chain` (AddSubgroup variant) in `WedhornBanachTheorem.lean`
  — B2 false (b2_log entry 2), superseded by Submodule variant (commit `5ea0687`).
- `_sub_lemma_L5_2_2_A₀_noeth_via_localization` in `WedhornStronglyNoetherian.lean`
  — SUPERSEDED marker, unreferenced (commit `4c3cce4`).

Remaining sorries on the L1 chain (B2-flagged, blocked on user decision):
- `wedhorn_6_18_unique` — uniqueness clause needs T2+ContinuousSMul on τ'.
- `_sub_lemma_L3_1a_completion_fg_complete` — needs M̂ fg as A-module
  (b2_log entry 1).
- `banach_two_of_three` direction 2 — needs ConnectedSpace H or equivalent.

## Recent progress (2026-05-18 session 2)

Triage + splitting "obvious-direction" lemmas to isolate the hard residual;
plus one canonicalisation refactor closing a duplicate sorry.

**New lemmas (obvious-direction splits):**

- **`ContinuousValuations.IsContinuous.isOpen_setOf_ge`** (NEW):
  forward direction of Wedhorn 7.8(3) under `[ContinuousAdd A]`.
  Proof: open ball is an open additive subgroup → clopen via
  `AddSubgroup.isClosed_of_isOpen` → complement is open.
  The iff `isContinuous_iff_setOf_ge_isOpen` is documented as B2 (the
  reverse direction is false; b2_log entry 5) — counterexample:
  trivial valuation on ℝ satisfies the ≥-hypothesis but is not
  IsContinuous (at γ = 1, {v a < 1} = {0} is not open).
- **`Presheaf.union_definitionIdeals_subseteq_topologicallyNilpotent`** (NEW):
  ⊇ direction of Wedhorn 7.51 sub-step (`A°° = ⋃ definition ideals`).
  Direct from `PairOfDefinition.isTopologicallyNilpotent_of_mem`.
  The full equality remains sorry — ⊆ direction needs AdjoinFinset
  enlargement of definition rings.
- **`Presheaf.units_subseteq_union_translates_of_oneAdd_topNilp`** (NEW):
  ⊆ direction of `A^× = ⋃_u u · (1 + A°°)`. Trivial: x ∈ A^× ↦
  x · (1 + 0) with 0 ∈ A°° via `IsTopologicallyNilpotent.zero`.
  Full equality requires `[CompleteSpace A]` (counterexample documented:
  A = ℤ with p-adic topology has 1 + p top-nilp but not a unit in ℤ).
- **`Presheaf.isUnit_implies_ne_zero_on_spa`** (NEW): forward direction
  of Wedhorn 7.52(2)-style `isUnit_iff_ne_zero_on_spa_of_complete` —
  unconditional via `ValuationSpectrum.not_vle_zero_of_isUnit`.

**Canonicalisation refactor:**

- **`WedhornStronglyNoetherian._sub_lemma_L5_4_2_nonOpen_prime_spa_point`**:
  was sorry pending "import wiring". The parent lemma
  `Presheaf.exists_mem_rationalOpen_supp_ge_of_prime_noHArch` has the
  exact target statement (covering both open and non-open primes
  uniformly), so the audit sub-lemma is now a direct delegation. This
  consolidates two duplicate sorries into one canonical sorry in
  Presheaf.lean (right home for the Chevalley/Wedhorn 7.44 + 7.45
  combination content). **Sorry count: 179 → 178.**

## Recent progress (2026-05-18 session 3)

Stacks 023N descent chain + isPowerBounded discrete + B2 logging:

**K.1 chain (Stacks 023N faithfully flat descent equaliser) — three sorries closed:**

- **`StructureSheaf.faithfullyFlat_cocycleMap`** (K.1.a, definition):
  defined as `TensorProduct.mk R S S 1 - (TensorProduct.mk R S S).flip 1`
  (s ↦ 1⊗s - s⊗1, R-linear). No sorry.
- **`StructureSheaf.faithfullyFlat_cocycleMap_algebraMap_eq_zero`** (K.1.b):
  algebraMap(r) lies in kernel, via `Algebra.algebraMap_eq_smul_one` +
  `TensorProduct.smul_tmul` / `TensorProduct.tmul_smul`.
- **`StructureSheaf.faithfullyFlat_descent_equalizer`** (K.1, the consumer):
  delegates through K.1.c by unfolding the cocycle map and matching the
  hypothesis shape. The deep K.1.c (`faithfullyFlat_cocycle_kernel_eq_algebraMap_range`,
  Stacks 023N theorem) remains as the single deep sorry in this chain.

**Discrete power-boundedness — one sorry closed:**

- **`Presheaf.isPowerBounded_of_discrete_presheafValue`**: closed via
  inline replication of the chain `DiscreteUniformity → DiscreteTopology →
  bounded with V = {0}`. The proof uses `Topology.IsEmbedding.toHomeomorphOfSurjective`
  + `Homeomorph.discreteTopology` to transfer DiscreteTopology from
  `Localization.Away D'.s` (where the localization topology is `⊥` via
  `locTopology_eq_bot_of_discrete`) to `presheafValue D'`.
  Transitively unblocks `HasLocLiftPowerBounded.discrete` (the instance
  was already filled but used the now-sorry-free helper).

**B2 logs added:**

- **b2_log entry 6**: `presheafValue_eq_quotient_AlangleX_iterated`
  uses MvPolynomial (algebraic) where it should use TateAlgebra
  (topological completion). Counterexample: A = ℤ p-adic, D.T = ∅,
  D.s = p — LHS = Completion(ℤ[1/p]) = ℚ_p, RHS = MvPolynomial ∅ ℤ ≅ ℤ.
  In-file docstring annotated.
- **b2_log entry 7**: `IsPowerBounded.map` claimed PB transfers along
  arbitrary continuous ring homs. Counterexample: φ = id : ℝ_discrete →
  ℝ_std (continuous since discrete source). x = 2 power-bounded in
  discrete source but not in standard target. In-file docstring updated.

**Session 3 totals: sorry count 178 → 174 (4 sorries closed).**

## Recent progress (2026-05-18 session 4)

One additional closure via Mathlib delegation:

- **`Presheaf.mulArchimedean_of_rankOne_valueGroup`** (Wedhorn 1.14):
  closed via direct delegation to `MulArchimedean.comap` (Mathlib's
  `Algebra.Order.Archimedean.Basic`). Takes the injective strict-mono
  `φ : G →*₀ WithZero (Multiplicative ℝ)` coerced to `MonoidHom`,
  and uses Mathlib's instance chain
  `Real.instArchimedean → Multiplicative.instMulArchimedean →
  WithZero.instMulArchimedean`.

This also makes the composition `mulArchimedean_valueGroup_of_analytic`
(Presheaf.lean, body chains this with `rankOne_valueGroup_of_analytic`)
fully sorry-free at the project layer — the remaining transitive sorry
is on the upstream `rankOne_valueGroup_of_analytic` (Wedhorn 7.40(6)
height-1 step, a separate deep result).

**Session 4 totals: sorry count 174 → 173 (1 sorry closed).**

## Recent progress (2026-05-18 sessions 5-6)

**Session 5 (helper):**

- **`Presheaf.union_translates_of_oneAdd_topNilp_subseteq_units_of_complete`**
  (NEW): ⊇ direction of Wedhorn 7.51 sub-step (`A^× = ⋃_u u · (1 + A°°)`)
  under `[UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]`.
  Direct: u · (1 + n) is a unit because u is and `1 + n` is via
  `IsTopologicallyNilpotent.isUnit_one_add` (Wedhorn 5.38). Full
  equality remains sorry — counterexample without completeness is
  A = ℤ with p-adic topology.

**Session 6 (B2 logging):**

- **b2_log entry 8**: `lemma_3_29_qcKolmogorov_oc_basis_consequences`
  (SpvAITopology.lean:508). The conjunction's IsTopologicalBasis clause
  is false without `(hU_inter : U closed under finite ∩)` and
  `(hU_cover : ⋃₀ U = univ)` hypotheses. Counterexample:
  X₀ = {a, b} discrete, U = {{a}} → ⋃₀ U = {a} ≠ univ. The other
  three clauses of the conjunction (T'≤T, CompactSpace T, ∀s∈U IsCompact s)
  ARE correctly proved. In-file docstring annotated.

**Sessions 5-6 totals: sorry count unchanged at 173 (0 closures, but
1 new helper + 1 new B2 documented). Cumulative across sessions 1-6:
179 → 173 (6 sorries closed) + 8 B2 entries logged.**

## Recent progress (2026-05-18 session 7)

Wedhorn 7.5(3) — retraction preserves nonvanishing on the ideal:

- **`SpvAITopology.SpvAI.retraction_ideal_ne_zero`** (CLOSED):
  given `v ∈ Spv A` with some `a ∈ I` having `¬ v.vle a 0`, the
  retracted valuation `restrictIdeal v I` likewise has `¬ (·).vle a 0`
  at the same `a`. Proof routes through `mem_supp_iff` →
  `ValuativeRel.supp_eq_valuation_supp` →
  `Valuation.restrictIdeal_apply_of_mem_ideal` (the value `v(a)` is
  preserved as a unit in the cGammaIdeal v I subgroup, hence nonzero).

**Audit-clean wrapper consolidation** (3 wrapper sorries → 0):

- **`AuditCleanWrappers.tateAcyclicity_gluing_via_descent_proof`**
  (CLOSED): delegates directly to
  `StructureSheaf.tateAcyclicity_gluing_via_descent` (the canonical
  version with the same hypothesis bundle). The `[HasLocLiftPowerBounded A]`
  hypothesis required by the canonical version is supplied automatically
  via the `hasLocLiftPowerBounded_of_stronglyNoetherianTate` instance.
- **`AuditCleanWrappers.prop_8_30_flat_clean_proof`** (CLOSED):
  delegates to `StructureSheaf.prop_8_30_flat_clean` by the same
  pattern.
- **`AuditCleanWrappers.isSheafy_ofStronglyNoetherianTate_proof`**
  (CLOSED): delegates to `StructureSheaf.isSheafy_ofStronglyNoetherianTate`
  by the same pattern. Removes a 20-line `refine ⟨?_, ?_⟩` body
  (with one embedded sorry) in favor of a one-liner that consumes
  the canonical sorry.

The three "_proof" wrappers in AuditCleanWrappers were originally
sorry'd pending the audit-pass-2 trio. Now that the trio's deep work
is concentrated in their canonical declarations in StructureSheaf
(each with one shared sorry), the wrappers can delegate without
duplicating the sorry. Wrappers' axiom chain still flows through the
shared sorries, but the project's sorry **count** drops by 3.

- **`WedhornStronglyNoetherian.exists_hSpa_points_global_of_stronglyNoetherianTate_proof`**
  (CLOSED): delegates to canonical `StructureSheaf.exists_hSpa_points_global_of_stronglyNoetherianTate`
  by the same one-liner pattern. Removes a structured open/non-open case-split
  whose non-open branch was sorry; the canonical's single sorry covers both.

The two SUPERSEDED `isNoetherianRing_*_of_stronglyNoetherianTate_proof`
wrappers were NOT delegated because the canonical versions require
`[PlusSubring A]` (from their section vars) which the wrappers' section
vars omit. Adding `[PlusSubring A]` to the wrappers would violate the
BINDING RULE.

**Session 7 total: 173 → 168 (5 sorries closed). Cumulative across
sessions 1-7: 179 → 168 (11 sorries closed) + 8 B2 entries logged.**

## Recent progress (2026-05-18 session 8)

Concrete Witt vector construction:

- **`FarguesFontaine.teichmullerPi`** (CLOSED): the Teichmüller
  representative `[π] ∈ W(O_E)` of a pseudo-uniformizer. Direct
  composition: `π : PseudoUniformizer E` → power-bounded (via
  `IsTopologicallyNilpotent.isPowerBounded`) → element of
  `↥(powerBoundedSubring.toSubring E)` → apply `teichmullerLift`.

**Session 8 total: 168 → 167 (1 sorry closed). Cumulative across
sessions 1-8: 179 → 167 (12 sorries closed) + 8 B2 entries logged.**

## Recent progress (2026-05-18 session 11)

Topological-openness of Y_FF in the Fargues-Fontaine curve construction:

- **`FarguesFontaine.Y_FF_isOpen`** (CLOSED): the pre-curve
  `Y_FF p E π` is the complement of the simultaneous vanishing locus
  `V(p, [π])`, which is open in `Spa(W(O_E), W(O_E))`. Proof via
  De Morgan: `¬(v(p) = 0 ∧ v([π]) = 0)` rewrites as
  `v(p) ≠ 0 ∨ v([π]) ≠ 0`, which is the union of two basic-opens.
  `isOpen_basicOpen` + `Continuous.isOpen_preimage` of `Subtype.val`
  finishes.

**Session 11 total: 167 → 166 (1 sorry closed). Cumulative across
sessions 1-8 + 11: 179 → 166 (13 sorries closed) + 8 B2 entries logged.**

## Recent progress (2026-05-18 session 13)

Wedhorn 7.5(2) retraction surjectivity via fixed-point:

- **`SpvAITopology.SpvAI.retraction_surjective`** (CLOSED): for
  `v ∈ SpvAI A I`, the retraction `r(v.1)` equals `v` by
  `SpvAI.retraction_eq_self` (sorry'd; inherits sorryAx transitively),
  so `v.1` is the preimage. One-liner:
  `fun v => ⟨v.1, SpvAI.retraction_eq_self I v⟩`.

**Session 13 total: 166 → 165 (1 sorry closed). Cumulative across
sessions 1-8 + 11 + 13: 179 → 165 (14 sorries closed) + 8 B2 entries
logged.**

## Recent progress (2026-05-18 session 15)

In-file reorder + delegation for upstream-downstream prevention:

- **`StructureSheaf.exists_spa_point_in_rationalOpen_of_prime`** (CLOSED):
  the original declaration was at line 690, BEFORE the canonical
  `exists_hSpa_points_global_of_stronglyNoetherianTate` at line 1444.
  Since the two have equivalent shape (specialise T = C.base.T, s =
  C.base.s), the local sorry was just a stand-in for the canonical's
  sorry but unusable in a forward-reference. Resolution: moved the
  declaration after the canonical and rewrote the body as a one-line
  delegation `fun p hp hs => exists_hSpa_points_global_of_stronglyNoetherianTate
  (A := A) C.base.T C.base.s p hp hs`. Confirmed zero consumers of the
  declaration (only the original site), so the move is safe.

**Session 15 total: 165 → 164 (1 sorry closed). Cumulative across
sessions 1-8 + 11 + 13 + 15: 179 → 164 (15 sorries closed) + 8 B2
entries logged.**

## Module Status

| Module | Lines | Status | Notes |
|--------|-------|--------|-------|
| `ValuationSpectrum.lean` | 386 | DONE | Spv(A), ValuativeRel, supp |
| `ValuativeRel/Comap.lean` | 55 | DONE | Comap for ValuativeRel, not_vle_zero_of_isUnit |
| `ContinuousValuations.lean` | 153 | DONE | isContinuous, Spa membership |
| `GeometricSeries.lean` | 69 | DONE | Topologically nilpotent => summable, 1-a unit |
| `AdicSpectrum.lean` | 455 | DONE | Spa(A, A+), Prop 7.51/7.52, exists_mem_spa_supp_eq_of_prime |
| `RationalSubsets.lean` | 165 | DONE | RationalLocData, rational subset containment |
| `Bounded.lean` | 344 | DONE | IsBounded, IsPowerBounded, A° subring, A°° |
| `OpenIdeals.lean` | 91 | DONE | Open ideals <-> topological nilradical |
| `AffinoidRings.lean` | 94 | DONE | IsRingOfIntegralElements, IsAffinoidRing |
| `HuberRings.lean` | 619 | DONE | PairOfDefinition, IsHuberRing, IsTateRing, IsAdicHom, Prop 6.25 |
| `LocalizationTopology.lean` | 366 | DONE | Localization topology, RingSubgroupsBasis |
| `CompleteTopCommRingCat.lean` | 94 | DONE | Bundled category, forgetful functors |
| `Presheaf.lean` | 893 | DONE | presheafValue, restriction maps, productRestriction |
| `StructureSheaf.lean` | 640 | DONE | IsSheafy, structure sheaf, adic space defn |
| `OrderedGroupConvex.lean` | 444 | DONE | ConvexSubgroup, quotient order, maxAvoid, archimedean iff (§7.1) |
| `ValuationCoarsening.lean` | 213 | DONE | Valuation coarsening, cofinal property for archimedean (§7.1) |
| `AnalyticPoints.lean` | 112 | DONE | IsAnalytic, Tate => analytic, Jacobson radical, idealOfDef API |
| `AdicMorphisms.lean` | 171 | DONE | Lemma 7.46(1)+(2 first part), Tate specializations |
| `SpaCompact.lean` | 460 | DONE | `IsCompact (Spa A A⁺)` + `CompactSpace ↥(Spa A A⁺)` under `[DiscreteTopology A]` (T-NULL-0c, discrete case); Tate pseudo-uniformizer case with `isCompact_spa_of_tate_pseudouniformizer` (hypotheses: `P.A₀ ≤ A⁺`, principal `P.I = (π)`, topologically nilpotent unit π, per-v MulArchimedean). Abstract criterion `isCompact_spa_of_isClosed_image` factors closed-image hypothesis. |
| `Cor732.lean` | 292 | DONE | **T-NULL-1**: Wedhorn Cor 7.32 (dominating unit extraction). `exists_dominating_unit`: given Tate hypotheses of `SpaCompact` and finite `T ⊆ A` with no common zero on `Spa`, produces `s ∈ Aˣ` with `v(s) < v(t)` strictly for some `t ∈ T` at every `v ∈ Spa`. Proof: open cover `U_n = ⋃_{t ∈ T} basicOpen (π^n) t` is increasing (by `v(π) ≤ 1`) and covers via `exists_pow_lt₀` (MulArchimedean); compactness yields index `N`; `s := π^(N+1)` is the unit. Sorry-free, axiom-clean. Unblocks T-NULL-2..5 (Zavyalov §2.3). |
| `Basic.lean` | 1 | PLACEHOLDER | Empty |

## PresheafTateStructure.lean Sorries

**`idealOfDef_pow_val_isClosed`** (line ~498): `IsClosed (idealOfDef^n)` in the subspace topology on `ringOfDef`. This is the deepest sorry in Proposition 8.15. **Status: STUCK (circular without AdicCompletion bridge).**

Why simpler approaches fail: the natural proof reduces to showing `idealOfDef^n = closure(g(J^n))`. The forward inclusion holds. The reverse requires `closure(g(J^n)) ⊆ idealOfDef^n`, which uses `closure_locNhd_sub_idealOfDef_pow`, which in turn uses `idealOfDef_pow_val_isClosed` -- creating a circular dependency.

Required approach: Use `AdicCompletionBridge.adicCompletionRingEquiv` to identify `ringOfDef` with `AdicCompletion(J, locSubring)`. Then compose with `AdicCompletion.evalₐ n` (continuous to discrete quotient). The key non-trivial step is `AdicCompletion.map_exact` (Mathlib) applied to `0 → J^n → locSubring → locSubring/J^n → 0`, which gives `ker(evalₐ n) = range(map I f)`, breaking the circularity. Infrastructure needed: identify `ringOfDef` with `Completion(locSubring, J-adic)` as a topological ring (~150 lines).

**`restrictionMapHom_surjective`** (line ~751): Surjectivity of the restriction map. Needs: the range of `restrictionMapHom` is complete (image of complete space under uniformly continuous map) and dense (contains `D.coeRingHom` image). Complete + dense in T2 = surjective.

**`restrictionMapHom_injective`** (PresheafTateStructure.lean:1310): Injectivity of the restriction map. OLD proof route via `restrictionMapAlg_isUniformInducing` is INVALID (depends on FALSE `locLift_preimage_locNhd`). NEW route: strict exactness of Laurent row (Ticket R2) or Prop 8.15 localization identification (Route B). See docs/TICKETS-axiom-clean.md.

**Update 2026-04-16**: Packaged Example 6.38 iso `presheafValue_tateAlgebra_quotient_iso` is now available in `TopologyComparison.lean` (end of file). It produces `presheafValue D ≃+* A⟨X⟩ ⧸ (1 - D.s · X)` under hypotheses `(hb, hA_complete, hnoeth, hT_pb)`. Its inverse is the unconditional `tateQuotientToPresheafHom`. The new continuity result `tateQuotientToPresheafHom_continuous_of_tate` discharged the formerly-fifth `hcont` hypothesis. The companion `restrictionMapHom_injective_via_iso` (PresheafTateStructure.lean) records the conditional API; its proof reduces to the same algebraic non-zero-divisor statement as the unconditional version. The remaining gap is **algebraic only**: showing that `mk(D₀.s)` is a non-zero-divisor in `A⟨X⟩/(1 - D.s · X)` (Wedhorn 8.32 single-restriction algebraic core).

**Update 2026-04-16 (Cor 8.32)**: `Adic spaces/Cor832.lean` (343 lines) ports Wedhorn Corollary 8.32 **abstractly**. Contributions:
- `faithfullyFlat_pi_of_prime_surjection` (axiom-clean): For a finite family of flat `R`-algebras `B_i` with joint surjection on `Spec`, the product `∏ B_i` is faithfully flat over `R`.
- `algebraMap_pi_injective_of_prime_surjection` (axiom-clean): Product injectivity via `FaithfulSMul.algebraMap_injective`.
- `productRestriction_faithfullyFlat_abstract`: Concrete for `RationalCovering`, taking `flat_over_base` and Spa-point prime-lifting hypotheses.
- `productRestriction_injective_of_flat_and_lifting`: Product-map injectivity.
- `tateAcyclicity_zero_kernel_of_flat_and_lifting`: exactly the shape of `tateAcyclicity` Part 1's separation conclusion, consumable without routing through `restrictionMapHom_injective`.

**Key finding**: Cor 8.32's product form CANNOT close single-map `restrictionMapHom_injective` (faithful flatness of product ≠ faithful flatness of each factor). The doc block of `restrictionMapHom_injective` (PresheafTateStructure.lean) correctly identifies this. Part 1 of `tateAcyclicity` remains blocked on `restrictionMapHom_injective`; rerouting through `tateAcyclicity_zero_kernel_of_flat_and_lifting` would require supplying `flat_over_base` (itself blocked by Prop 8.15's circular dependency on single-map injectivity) and Spa-point prime-lifting.

**Update 2026-04-16 (T-WEDHORN-1)**: Five new theorems added to `Adic spaces/Cor832.lean` (253 lines net added, total 584 lines) closing T-WEDHORN-1:
- `productRestriction_injective_tate` — **target theorem**: Part 1 of `tateAcyclicity` exposed as a standalone packaged theorem with the exact T-WEDHORN-1 signature (no extra `IsDomain A`, no extra `hSpa`). Proof delegates to `tateAcyclicity` Part 1.
- `productRestriction_injective_tate_via_cor832` — Cor 8.32-route version with `flat_over_base` + `hSpa_surj` as explicit hypotheses.
- `flat_over_base_tate` — **unconditional discharge of `flat_over_base`** via `restrictionMap_isLocalization` (Wedhorn Prop 8.15) + `IsLocalization.flat`.
- `hSpa_surj_from_spanTop` — **unconditional discharge of `hSpa_surj` modulo a span-top hypothesis** via `restrictionMap_isLocalization` + `IsLocalization.isPrime_of_isPrime_disjoint`. The residual span-top hypothesis is Wedhorn Cor 8.31 content at the presheafValue level.
- `productRestriction_injective_tate_of_spanTop` — end-to-end Cor 8.32-route combinator: threads the two scaffolds above into `productRestriction_injective_tate_via_cor832`, leaving only the span-top hypothesis as input.

All five theorems compile; axiom trace is `[propext, sorryAx, Classical.choice, Quot.sound]`, identical to `tateAcyclicity`. The `sorryAx` dependency is inherited transitively from `restrictionMap_isLocalization` (Wedhorn Prop 8.15, `PresheafTateStructure.lean:1499`), itself dependent on `restrictionMapHom_injective` and `restrictionMapHom_surj`. No new sorries introduced in this work.

**Update 2026-04-30 (T125 route-pivot decision; T113/T119 lane parked)**: After the T123 audit identified a hidden-hypothesis obstruction in any generic `D.s` colon/source bridge, T125's read-only route audit confirmed the pivot to the v3 strict-exactness route. Decisions:

- **T113/T119 colon-saturation lane is PARKED** (not narrowed). A principal-pair-only narrowing does not reach the actual consumers in `Cor832.flat_over_base_tate` / `hSpa_surj_from_spanTop`, which use arbitrary `RationalCovering` data. Future workers should not revive the `D.s`-localization-base bridge for `cross_localization_preimage_in_sup_ker` / `locLift_preimage_target_witness_existence` until explicitly reassigned.
- **Forbidden shape**: any theorem that would push a generic `D.s ∈ D.P.A₀` (or analogous `D.s`-localization-base) hypothesis into `ValuationSpectrum.tateAcyclicity`, Part 2, or final acyclicity. The no-extra-final-hypotheses rule remains in force.
- **Accepted reusable support kept (parked, not reverted)**: the colon-saturation chain primitives are mathlib-style and reusable in future work (e.g., for an alternative Prop 8.15 route or Cor 8.32 scaffolding):
  - T114 `locSubring_exists_denominator_clearance` (commit 6076e80, then 7b8123b docstring refactor flagging the E-shift caveat) in `WedhornAwayMapSaturation.lean`.
  - T119 `Ideal.exists_factor_of_mem_inter_singleton` (commit 7cb7bc8) — single-step Artin-Rees `s`-absorption, no torsion/NZD hypotheses.
  - T122 `Ideal.exists_factor_pow_of_mem_inter_pow_singleton` (commit b7baef1) — E-dependent `s^E`-absorption, no torsion/NZD hypotheses.
  - T124 `PrincipalPairOfDefinition.{pi_mem_I, pi_topologicallyNilpotent, exists_pow_mul_mem_A₀, exists_pow_mul_eq_A₀}` (commit 8508857) — π-specific clearing API for the principal Tate pair, without the invalid generic `D.s` bridge.
- **Active critical path**: v3 strict-exactness route in `docs/TICKETS-tate-acyclicity-v3.md` (Wedhorn Lemma 8.31 flatness + Lemma 8.33 Laurent 3×3 chase + Lemma 8.34 refinement transfer + Banach OMP). T126 verifies the v3 route; the next implementation tickets after T126 (T127/T128/T129) work that lane. Wedhorn Prop 8.15 / `restrictionMap_isLocalization` is **not** required by the v3 route.

## Sorry-Free Status

As of 2026-03-25:

**Tilting.lean** — 0 sorry's in `berkeley_6_2_8` (Berkeley Lectures Lemma 6.2.8):
- `hp_reg` (line 346): p-torsion-freeness of A° — proved via `IsPerfectoidRing.p_regular` class field.
- divisibility (line 423): `ξ.coeff 0 | y.coeff 0` in the tilt — proved via `IsPerfectoidRing.tilt_ker_coeff_dvd` class field (added 2026-03-25). The class field encodes the mathematical fact that in the tilt of a perfectoid ring, `ker(Perfection.coeff 0)` is principally generated by any nonzero element.

**TateAlgebra.lean** — 4 sorry's for the quotient flatness work (Lemma 8.31(2)):
- `Module.Flat.quotient_of_flat_of_saturated` (abstract engine, verified in standalone context)
- `noeth_mem_ideal_of_mul_shift` (modular ascending chain lemma)
- `TateAlgebra.fSubX_saturated` (saturation for f-X)
- `TateAlgebra.oneSubfX_saturated` (saturation for 1-fX)
The assembly theorems `flat_quotient_fSubX_general` and `flat_quotient_oneSubfX_general` compile modulo these sorry's.

**PresheafIdentification.lean** — 0 sorry's. New results (2026-03-25):
- `tateQuotientPresheafEquiv` : Ring isomorphism `A⟨X⟩/(1-sX) ≃+* presheafValue D` (discrete case, Wedhorn Remark 7.55). Verified sorry-free.
- `tateQuotientPresheafEquiv_mk_algebraMap`, `_mk_X`, `_symm_canonicalMap` : Key properties of the isomorphism.
- `quotientEvalPresheafHom_surjective` : Surjectivity of the quotient evaluation map.

**TopologyComparison.lean** — 1 sorry (updated 2026-04-16):
- `locToQuotientOneSubfX_gen_continuous_canonical` uses sorry for `h_top_eq : quotientOneSubfXIdealTopology D.s = quotientTTopology D.s`. This is the equality of the canonical I-adic quotient topology and the T-topology quotient on `A⟨X⟩/(1-sX)`. **Mathematical content: Wedhorn Proposition 6.18** (module topology on f.g. modules over strongly noetherian Tate rings). The easy direction (canonical quotient >= T-quotient) follows from coinduced monotonicity since the canonical topology on TateAlgebra is finer than the T-topology. The hard direction (canonical quotient <= T-quotient) requires that the ideal `(1-sX)` collapses the infinitely many canonical coefficient constraints to finitely many T-topology constraints.
- Sorry-free: `locToQuotientOneSubfX_gen_continuous` (T-topology version), `locToQuotient_mul_small_constant_mem`, all completion isomorphism results (`presheafValueToQuotient`, `presheafValueTateQuotientEquiv`, etc.), `locToQuotientOneSubfX_gen_denseRange_canonical`.
- Sorry-free: `quotientTTopology` + ring/nonarchimedean instances, `presheafValueToQuotient_coe`, `presheafValueTateQuotientEquiv_canonicalMap`, `_symm_algebraMap`.
- **NEW (2026-04-16)** Sorry-free: `presheafValue_tateAlgebra_quotient_iso` and its specs (`_canonicalMap`, `_symm_algebraMap`, `_symm`). Packaged Wedhorn Example 6.38 ring iso `presheafValue D ≃+* A⟨X⟩ ⧸ (1 - D.s · X)` under hypotheses `(hb, hA_complete, hnoeth, hT_pb)`. The continuity hypothesis is auto-discharged via `tateQuotientToPresheafHom_continuous_of_tate`.

**StructureSheaf.lean** — sorry's (updated 2026-03-28):
- **DONE** `structurePresheaf` : Fully proved (0 sorry). Functor `(Opens (SpaTop A))^op => CompleteTopCommRingCat` using locally-fraction sections with discrete uniformity.
- `structureSheaf` : **1 sorry** (decomposed into `⟨structurePresheaf A, sorry⟩`). Needs sheaf condition for `structurePresheaf`. Route: transfer type-level sheaf condition from `subpresheafToTypes.isSheaf isLocallyFraction` via `isSheaf_iff_isSheaf_comp`. Blocking: `CompleteTopCommRingCat` lacks `HasLimits`, `PreservesLimits (forget ...)`, and `ReflectsIsomorphisms` instances needed for `isSheaf_iff_isSheaf_comp`. See `Mathlib.Topology.Sheaves.CommRingCat` for the `CommRingCat` analogue.
- **QUARANTINED** (kept for backwards compat, route through TopologyComparison instead):
  - `localization_isT0` : False in general when locIdeal = top.
  - `completionKer_eq_bot_of_locKer_eq_bot` : Needs AdicCompletion bridge.
  - `loc_algebraic_injectivity_of_tate` : Depends on false localization_isT0.
- `exists_spa_point_in_rationalOpen_of_tate` : Open-prime case proved. Non-open prime case (1 sorry) requires Lemma 7.45 refinement.
- **NEW proof route via TopologyComparison** (2026-03-26):
  - `separation_ofStronglyNoetherianTate` : Real proof reducing to `tateQuotientProductRestriction_injective` via `presheafValueTateQuotientEquiv`. Added hypotheses: `[T2Space A] [NonarchimedeanRing A]` + isomorphism conditions (hb, hcs, ht0, hcont, hdense) for base and cover pieces + Spa-point hypothesis.
  - `isSheafy_ofStronglyNoetherianTate` : Delegates to separation via uniform hypotheses.
  - `tateQuotientProductRestriction_injective` : **1 sorry** — the key algebraic step showing that the product restriction transferred to Tate quotients has trivial kernel. Needs: (1) transfer restrictionMap=0 through cover isomorphisms, (2) interpret at localization level, (3) apply Spa-point radical argument.
- Sorry-free: `base_s_in_annihilator_radical_of_covering`, `restrictionMapAlg_factors`, `productRestriction_coe_eq`, `productRestriction_comp_canonicalMap`, `exists_spa_point_in_rationalOpen_of_isOpen_prime`.

**TateAcyclicity.lean** — 0 sorry (updated 2026-03-29):
- `IsSheafy.ofStronglyNoetherianTate_discrete.isEmbedding_productRestriction` : **DONE** (sorry-free).
- `IsSheafy.ofStronglyNoetherianTate_discrete.gluing` : **DONE** (sorry-free). Delegates to `discrete_gluing`. Numerator compatibility proved via common refinement `D3` with `s3 = D1.s * D2.s` (using `rationalOpen_inter`), power absorption (Mathlib-style), and exact equality in `A`.
- Helper lemmas: `discreteUniformity_presheafValue`, `discreteTopology_presheafValue`, `discrete_gluing`, `isLocAway_of_isUnit`.

## Key Theorems (Adic Morphisms Chain)

| Theorem | File | Wedhorn ref | Status |
|---------|------|-------------|--------|
| `IsAdicHom` (Def 6.23) | HuberRings:502 | Def 6.23 | DONE |
| `IsTateRing.isAdicHom_of_continuous_with_pairs` (Prop 6.25) | HuberRings:534 | Prop 6.25 | DONE (with h_map hyp) |
| `nonAnalytic_comap_of_continuous` (Lem 7.46(1) first) | AdicMorphisms:53 | Lem 7.46(1) | DONE |
| `analytic_comap_of_isAdicHom` (Lem 7.46(1) second) | AdicMorphisms:123 | Lem 7.46(1) | DONE |
| `analytic_comap_of_isAdicHom_tate` (Tate specialization) | AdicMorphisms:164 | Lem 7.46(1) | DONE |
| Lemma 7.45 (analytic point construction) | Lemma745.lean | Lem 7.45 | DONE (sorry-free) |
| Lemma 7.46(2) (converse: analytic preservation => adic) | — | Lem 7.46(2) | NOT STARTED (needs 7.45) |
| Def 8.38 (adic morphisms of adic spaces) | — | Def 8.38 | NOT STARTED |
| Prop 8.39, Cor 8.40 | — | Prop 8.39, Cor 8.40 | NOT STARTED |

## Open Work Items

### High Priority
- [x] **Verify full project builds** — `lake build` passes (2337 jobs, 2026-03-11)
- [ ] **Commit all current work** — many new files + modified files uncommitted

### Medium Priority (extending the formalization)
- [x] **Lemma 7.45** — Analytic point construction for complete affinoid rings. Proved sorry-free in `Lemma745.lean` as `exists_mem_spa_supp_ge_of_nonOpen_prime`.
- [ ] **Lemma 7.46(2)** — Converse: analytic preservation implies adic (needs 7.45)
- [ ] **Remove h_map hypothesis from Prop 6.25** — needs Prop 6.4(5) (bounded open subring = ring of definition)
- [ ] **General (non-discrete) sorry removal** — Two blocking sorries in Presheaf.lean (updated 2026-03-28):
  - `mem_prime_of_rational_subset_nonOpen` (line ~378): Non-open prime case of Prop 7.52. **REFACTORED (2026-03-30).** The sorry is now isolated to a single existence statement: `∃ v ∈ rationalOpen D'.T D'.s, p ≤ v.supp` for non-open primes. The contradiction step (rationalOpen inclusion + support membership → False) is proved inline. Infrastructure completed in this pass: `ValuationPrimeConvex.lean` sorry-free (prime↔convex correspondence, height-1 → MulArchimedean), `ValuationContinuity.lean` extended with `exists_valuationSubring_of_prime_enlarged` (enlarged domination API) and `valuation_le_one_of_mem` (rationalOpen bridge). Exact-support construction `exists_mem_spa_supp_eq_of_nonOpen_prime_mulArchimedean` is sorry-free but requires both MulArchimedean AND rationalOpen membership; the latter cannot be obtained from the domination theorem alone (enlarged domination makes I-generators units for Tate rings since I·A = A; coarsening does not preserve continuity). Resolution requires: (a) Spa completion invariance Spa(A,A⁺) ≅ Spa(Â,Â⁺) (Wedhorn Prop 7.23), or (b) a rank-1 continuous valuation with support = p (Wedhorn p67-68, DVR via blow-up + Krull-Akizuki on A₀).
  - `restrictionMapAlg_continuous_of_huber` (line ~447): Continuity of the algebraic restriction map for localization topologies. **PARTIALLY PROVED.** Factorization through `coeRingHom ∘ locLift` complete (steps 1-6 verified). Remaining sorry: the **neighborhood-mapping property** `∀ m, ∃ n, locLift '' (locNhd D n) ⊆ locNhd D' m`. This requires the universal property of the localization topology (Wedhorn §5.51): formalizing that `locTopology` is the coarsest ring topology making `algebraMap` continuous with `s` invertible and `{t/s}` power-bounded. Infrastructure needed: (a) `locTopology_continuous_lift` theorem in `LocalizationTopology.lean`, (b) interleaving of neighborhood bases from different pairs of definition `D.P`, `D'.P`, (c) boundedness analysis of `locSubring` images.
  - Open prime case (`mem_prime_of_rational_subset_open`) sorry-free.
- [ ] **Sheaf condition for general Huber rings** — `IsSheafy` stated for Tate rings. Sorry decomposed (2026-03-25) into: (A) `completionKer_eq_bot_of_locKer_eq_bot` (completion kernel reduction, needs AdicCompletion bridge / G2-topo), (B) algebraic injectivity on localization (needs Spa points in specific rational subsets for Tate rings). All algebraic infrastructure sorry-free: `base_s_in_annihilator_radical_of_covering`, `restrictionMapAlg_factors`, `tateQuotientPresheafEquiv`.
- [ ] **Categories V^pre and V** — see `docs/plans/2026-03-08-complete-top-ring-category.md` Tasks 2-3

### High Priority — Tate Acyclicity (non-discrete)
- [ ] **Tate's acyclicity theorem** (Wedhorn Thm 8.28(b)) — algebraic foundation complete. Non-discrete case planned in `docs/TICKETS-tate-acyclicity-v3.md` (2026-04-02). Key approach change from v2: skip T-topology entirely, use bridge formula `O_X(R(T/g)) ≅ (AdicCompletion_J D)[1/π]` + Tate algebra quotients (Example 6.38) + Banach open mapping for strictness. 6 tickets, ~1250 lines. Wave 1 (T1, T2, T3) parallelizable.

### Low Priority / Future
- [ ] **Perfectoid spaces** — long-term goal
- [ ] **Clean up `Basic.lean`** — currently a placeholder

## Plan Documents

Detailed implementation plans live in `docs/plans/`:
- `2026-03-07-restriction-maps-and-sheafy.md` — Original plan for restriction maps (mostly implemented)
- `2026-03-08-prove-remaining-sorries.md` — Plan for removing sorries (completed for discrete case)
- `2026-03-08-complete-top-ring-category.md` — Plan for CompleteTopCommRingCat and V categories
- `2026-03-11-adic-morphisms-cor-8-40.md` — Plan for Cor 8.40 (Phases 1-3 done, Phase 4 partial)

## Agent Activity Log

> When you start working, add a line here. Remove it when done.

| Agent | Working On | File(s) | Started |
|-------|-----------|---------|---------|
| claude-opus | R2 reframed via Wedhorn route (Phase 1 audit done; Phase 2-4 pending) | LaurentRefinement, StructureSheaf, TICKETS-axiom-clean.md | 2026-04-08 |

### 2026-04-14 (later) — `laurentMinusBridge` sorries lifted to hypotheses

**Finding:** The two residual sorries inside `laurentMinusBridge`
(`hnoeth := sorry` at line 648, `hcont_eval := sorry` at line 650) encoded
genuinely new infrastructure obligations that cannot be discharged from
the current instance set. Following the precedent of
`example638Minus_equiv` in `IteratedRational.lean`, these are now exposed
as explicit `laurentMinusBridge` hypotheses:

- `hnoeth_B` : `IsNoetherianRing ↥(TateAlgebra.pairSubring (IsTateRing.principalPair
  (presheafValue D₀)).toPairOfDefinition)` — the "strongly noetherian
  property transfers to rational localisations" direction of Wedhorn
  Theorem 7.47 / Example 6.38. **Blocker**: needs Wedhorn 7.47 and a
  concrete identification of `(presheafValue_ringOfDef D₀)` with a
  noetherian ring (topological closure doesn't preserve noetherianness
  abstractly).
- `hcont_eval_B` : canonical-topology continuity of
  `tateQuotientToPresheafHom (iteratedMinusDatum_B P D₀ f) hb` at
  `B := presheafValue D₀`. **Blocker**: the canonical-topology version
  of `tateQuotientToPresheafHom_continuous` (only T-topology is proved
  in `TopologyComparison.lean:1390`), combined with the strongly-noetherian
  structure at `presheafValue D₀`.

Both hypotheses are propagated through `laurentMinusBridge_restrictionMap`,
`laurentBridge_delta_eq_zero_of_compat`, `laurentCover_gluing_presheaf_viaBridges`,
and `laurentCover_gluing_presheaf`. Downstream callers must supply them
(or push the obligation further up). The `tateAcyclicity` theorem is
unaffected (it has its own independent sorry for gluing via partition of
unity).

**Sorry accounting (LaurentRefinement.lean):** 9 → 7 (−2). The two
sorries inside `laurentMinusBridge`'s body are replaced by explicit
hypotheses in the signature.

Commit: `801d8f2`.

### 2026-04-14 — Laurent gluing rerouted via Route B; Baire blocker eliminated

**Finding:** `LaurentCover.row3_exact` (LaurentCoverExact.lean:1560) instantiates
cleanly at `A := presheafValue D₀` with `f' := D₀.canonicalMap f`. No
`[IsNoetherianRing]` / `[IsDomain]` needed on the instantiated base. This
sidesteps the Baire blocker (`restrictionMapHom_surj`) entirely.

**Rerouted architecture (LaurentRefinement.lean):**
- `laurentCover_gluing_presheaf` now delegates to
  `laurentCover_gluing_presheaf_viaBridges` (Route B assembly).
- `laurentCover_gluing_presheaf_viaBridges` composes the five named bridge
  stubs with `laurentCover_gluing_presheaf_viaRow3` (sorry-free core).
- `laurentCover_gluing_presheaf_viaRow3` applies `row3_exact` at
  `presheafValue D₀` and uses injectivity of the bridges.
- `laurentCover_algebraic_gluing` (Route A) removed — its stronger
  `Localization.Away D₀.s`-level conclusion chained to the Baire blocker
  and is no longer needed.

**Five named bridge stubs (the new leafy sorries):**
- `laurentPlusBridge`                     — `presheafValue(plus)` ≃+* `B₁_gen(canonicalMap f)`
- `laurentMinusBridge`                    — `presheafValue(minus)` ≃+* `B₂_gen(canonicalMap f)`
- `laurentPlusBridge_restrictionMap`      — `τ₊ ∘ restrictionMap = π₁ ∘ epsilonHom_gen`
- `laurentMinusBridge_restrictionMap`     — `τ₋ ∘ restrictionMap = π₂ ∘ epsilonHom_gen`
- `laurentBridge_delta_eq_zero_of_compat` — compat ⇒ `deltaMap_gen(τ₊ u₊, τ₋ u₋) = 0`

**Sorry accounting (LaurentRefinement.lean):** 3 → 7 (+4). The removed sorry
chained to the (sorry'd) Baire surjection; the five new stubs are independent
and don't chain to existing sorries. Net reduction in sorry-depth.

**Next Route B work:** implement any subset of the five bridges. The minus
bridge should extend `presheafValueTateQuotientEquiv` (TopologyComparison:831)
to `presheafValue D₀`-coefficients (base-change + unit rescaling of `X` by
`canonicalMap D₀.s`). The plus bridge identifies the T-extension (adding `f`
to `T`) with the `f = X` relation.

Commits (in order): `74fbb81`, `9609e25`, `87c76a6`, `ed35fd3`. Full build
green throughout (3080 jobs).

### 2026-04-08 — R2 reframed around Wedhorn flatness route

**Phase 1 + Option A (audit + reframe + restore strong sheaf condition) DONE 2026-04-08.**

**Key insight 1 (the audit):** Wedhorn's Theorem 8.28(b) proof (lecture notes
`1910.05934v1.pdf` pp. 81–85) goes via Lemma 8.31 (flatness) + Lemma 8.33 (3×3
diagram chase) + Lemma 8.34 (refinement transfer) — purely algebraic in the
sense that it does not need defect-correction / Banach open mapping. The
earlier "strict exactness via Banach OMP" framing of R2 was attacking the
right structural goal (topological embedding) but with the wrong tool.

**Key insight 2 (Option A):** The standard adic-space definition (Wedhorn 8.21
/ 8.26) DOES require sheaf of TOPOLOGICAL rings, not just sheaf of sets. Our
`IsSheafy` class therefore needs a `Topology.IsEmbedding` field. The
topological embedding comes for free in the Wedhorn route ONCE Example 6.38 is
proved as a TOPOLOGICAL ring iso (universal property + Wedhorn Prop 6.17),
because the 3×3 diagram chase then preserves topology through the Tate-algebra
quotient identifications.

**Phase 1 + Option A actions:**
- Deleted `defect_correction_exists`, `compatible_sections_in_image`,
  `density_approximation` (the wrong-tool chain).
- Restored `embedding : Topology.IsEmbedding (productRestrictionSub A C)` as
  the (combined separation + topological inducing) field of `IsSheafy`. This
  matches Wedhorn 8.21/8.26.
- `IsSheafy.ofStronglyNoetherianTate_discrete` (TateAcyclicity.lean) now
  provides the embedding field sorry-free: discrete source + finite Pi of
  discretes + injective ⇒ embedding. Direct proof, ~12 lines.
- `isSheafy_ofStronglyNoetherianTate_flat` (StructureSheaf.lean) handles
  `C.base.s = 0` via `Topology.IsEmbedding.of_subsingleton`; the `s ≠ 0` case
  remains a single sorry pointing at Phase 2-4 of the Wedhorn plan.
- `tateAcyclicity` Part 2 (gluing) is a single sorry pointing at Phase 4.
- `TICKETS-axiom-clean.md` updated to v3: R2 broken into R2-Phase2 (Example
  6.38 with TOPOLOGICAL iso), R2a (Cor 8.32), R2b (Lemma 8.33 Tate), R2c
  (Lemma 8.34 + assembly). Total ~800 lines.
- Full project builds (3080 jobs).
- Net sorry count in R2 critical path: −1. Discrete `IsSheafy` instance now
  matches the standard Wedhorn definition sorry-free.

**Plans:**
- `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` — main Wedhorn plan, recommends
  Wedhorn route over Zavyalov. Note: Phase 2 must aim for a TOPOLOGICAL ring
  iso (not just algebraic) for the embedding to work end-to-end.
- `docs/plans/2026-04-08-zavyalov-decompleted-route.md` — Zavyalov plan, archived
  as "not pursued" unless Wedhorn hits an unexpected wall in Phase 2.
- `docs/plans/2026-04-08-phase2-2-leftmul.md` — Phase 2.2 leftMul plan with
  Sub-tasks A/B/C/D (coeff extraction forward, I-adic continuity, almost-all
  coeffs, reverse coeff char). **Sub-tasks A-D + F (assembly) DONE sorry-free
  (principal case).** Sub-task E (Wedhorn 6.14) still pending.

### 2026-04-08 — Phase 2.2 COMPLETE sorry-free (leftMul + Wedhorn 6.14)

**Both TateAlgebraTopology.lean and HuberRings.lean are sorry-free.**

**leftMul hard case (Phase 2.2A/B/C/D/F):**
- Sub-task A: `coeffInIdealIdeal` auxiliary ideal + `pairIdeal_pow_le_coeffInIdeal`
  giving `y ∈ (pairIdeal P)^n → ∀l, coeff l y ∈ image P.I^n`.
- Sub-task B: `exists_mul_pow_subset_pow` via continuity of `a * ·` at `0`.
- Sub-task C: `tateAlgebra_coeff_eventually_in_pow` — restricted series have
  eventually all coefficients in `image P.I^n`.
- Sub-task D (principal): `tateAlgNhd_of_coeff_mem_principal` — "divided series"
  construction with `g = π^{-n} · y ∈ pairSubring P`, then `y = π^n · g`.
- Sub-task F (assembly): `tateAlgNhd_leftMul_of_principal` decomposes
  `(x · y) = Σ_p (coeff p.1 x) · (coeff p.2 y)` on antidiagonal and routes each
  pair through Sub-task B (bad) or direct (good), then applies Sub-task D.

**Wedhorn 6.14 (Phase 2.2E):** `IsTateRing.exists_principal_pairOfDefinition`
in `HuberRings.lean`: starting from any pair of definition `P`, use that
`(u : A)^k` lies in `P.A₀` for some `k` (topological nilpotence), then
`exists_pow_mem_I` gives `(u^k)^N ∈ P.I`, then `exists_pow_I_le_span_unit`
bounds `P.I^m ≤ span {π}`. Apply `P.withPrincipal`.

**Canonical unparameterized topology:**
- `PrincipalPairOfDefinition` structure bundles `(P, π, hπ_gen, hπ_unit)`.
- `IsTateRing.principalPair` = canonical instance via `Classical.choice`.
- `tateAlgebraTopology'` = canonical natural Tate topology on `TateAlgebra A`
  for any Tate ring, with NO explicit pair argument.
- `tateAlgebraTopology'_isTopologicalRing` = it's a ring topology.
- `pairSubring_principalPair_isOpen'` = the canonical pairSubring is open.

**Phase 2.2 is DONE.** Downstream consumers (Phase 2.3+) can use
`tateAlgebraTopology'` directly. Net: Phase 2.2 sorry count = 0.

### 2026-04-08 -- Phase 2.6 infrastructure (canonical topology bridge)

**TateAlgebraTopology.lean:**
- `quotient_oneSubfXIdeal_completeSpace` -- PROVED (sorry-free). Quotient
  `A⟨X⟩/(1-sX)` is complete under canonical quotient topology, using
  `QuotientAddGroup.completeSpace_right'` (Bourbaki IX.3.1 Prop 4).
  Previous agent incorrectly claimed this was a Mathlib limitation.

**TopologyComparison.lean (new section CanonicalTopologyBridge):**
- `tateAlgebra_polynomials_dense_canonical` -- PROVED (sorry-free).
  Polynomials dense in canonical topology via truncation argument.
- `locToQuotientOneSubfX_gen_denseRange_canonical` -- PROVED (sorry-free).
  Dense range via polynomial density + surjective quotient map.
- `locToQuotientOneSubfX_gen_continuous_canonical` -- 1 sorry.
  Continuity from localization topology to canonical quotient topology.
  Proof structure follows T-topology version but needs adaptation of
  `locToQuotient_mul_small_constant_mem` for canonical I-adic structure
  (uses `tateAlgNhd_leftMul` instead of Artin-Rees shift constants).

**Net:** Phase 2.6 sorry count = 1 (continuity of locToQuotientOneSubfX_gen
for canonical topology).
