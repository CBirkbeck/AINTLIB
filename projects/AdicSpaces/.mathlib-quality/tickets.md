# Ticket Board — Campaign 5: the adic Fargues–Fontaine curve (definition layer)

**Status: ACTIVE (approved 2026-07-24).** Campaign-4 board archived as
`tickets-fjp-archived-2026-07-24.md`.

**Contract**: every statement already exists as a `:= by sorry` declaration in the
skeleton under `Adic spaces/FarguesFontaine/` (build-verified; see decomposition §0.5).
A ticket = *fill the named sorries*; statements are NOT to be changed (B2-stop if a
statement is wrong — report, don't bend). Each ticket cites its decomposition leaves
(`decomposition.md`, e.g. L4.6), which carry the verbatim source
quotes, discharge plans, and attack logs. Sources local under `refs/AdicSpaces/`.

## Summary
- Core proof tickets: 22 (T101–T505) + 1 stretch (T601, blocked-on-plan)
- Cleanup tickets: 10 (CLEANUP-1…8, CLEANUP-ALL-1, CLEANUP-FINAL)
- Open: all | Done: 0 | Peak parallel capacity: 3 workers
  (M2-summit track ∥ M4-window track ∥ M3/M5 tail)

## Milestone map
M1 T101–T103 → M2 T201–T205 (summit T205 = A_inf complete) ∥ M4-early
→ M3 T301–T303 → M4 T401–T406 (summit T405/T406 = covering machine)
→ M5 T501–T505 (**milestone T503** = Def 2.1.1 honest with Kedlaya's two charts)
→ stretch T601. Cleanups interleaved per cadence.

Global rules for every ticket: verify bar = `lake build '«Adic spaces»'` green, zero
new `sorry` in the touched file beyond the remaining skeleton ones, `#print axioms` of
each filled declaration ∈ {propext, Classical.choice, Quot.sound}. Generality: exactly
the skeleton signatures (maximal-generality decisions frozen at plan §Generality; do
not weaken or strengthen hypotheses).

---

### [T101] O_F: domain, char p, perfect (L1.1–L1.5)
- **Status**: open | **File**: FarguesFontaine/PerfectoidFieldCharP.lean | **Depends**: none | **Parallel**: yes
- **Statements**: `instIsDomainOF`-anon (`IsDomain (OF F)`), `instCharPOF`
  (`CharP (OF F) p`), `frobenius_surjective_OF`
  (`Function.Surjective (frobenius (OF F) p)`), `instPerfectRingOF`
  (`PerfectRing (OF F) p`), `PseudoUniformizer.toOF_ne_zero` — verbatim in file.
- **Sketch**: (1) IsDomain: subring of the field `F` — mathlib subring-domain instance
  (`Subring.instIsDomain`-shape) or `Function.Injective.isDomain` along
  `Subring.subtype`. (2) CharP: transfer along the injective `(powerBoundedSubring
  .toSubring F).subtype` via `charP_of_injective_ringHom`; keep the `have := ‹CharP F p›`
  line (semi-out-param gate). (3) Surjectivity: from the project class field
  `IsPerfectoidRing.frobenius_surj`: `x = y^p + p·z`; kill `p·z` with
  `CharP.cast_eq_zero`; beware `frobenius` needs the `ExpChar` chain — provided by
  CharP + Fact prime instances. (4) PerfectRing: bijectivity from injectivity
  (`frobenius_inj`-shape for domains/reduced rings) + (3); use mathlib's
  `PerfectRing.ofSurjective`/`ofBijective`-style constructor (check exact name via
  `lean_local_search`). (5) ne_zero: `Subtype.ext_iff` + `Units.ne_zero`.
- **Mathlib needed**: `charP_of_injective_ringHom`, `frobenius_inj` (or
  `frobenius_injective`), a `PerfectRing` constructor, `Units.ne_zero` — verify each
  name before use.
- **Sources**: decomposition L1.1–L1.5 ([Bhatt §3.1 Ex. 3.1.2(3)] verbatim quote there).

### [T102] O_F: the ϖ-adic neighbourhood basis (L1.6)
- **Status**: open | **File**: PerfectoidFieldCharP.lean | **Depends**: T101 | **Parallel**: with T2xx after T101
- **Statements**: `span_toOF_pow_mem_nhds_zero`, `exists_span_toOF_pow_subset_nhds`.
- **Sketch**: (1) identify `((span {ϖof})^n : Set)` with `ϖ^n • (O_F)` via
  `Ideal.span_singleton_pow` + `Ideal.mem_span_singleton'`. (2) membership in 𝓝 0: O_F
  is open in F (uniformity: `IsUniform` gives `IsBounded (powerBoundedSubring F)`; the
  project's Tate/uniform API for openness of F° — locate in Uniform.lean/Bounded.lean;
  if genuinely absent, STOP-B3 and report: this is the flagged sub-risk of L1.6) and
  `x ↦ ϖ^n x` is a homeomorphism of F (`Homeomorph.mulLeft₀`/unit smul) carrying O_F
  onto the target set; intersect with O_F for the subspace statement. (3) converse:
  `IsTopologicallyNilpotent` of ϖ + boundedness of O_F: for U ∈ 𝓝 0 pick V with
  O_F·V ⊆ U (`IsBounded`), then ϖ^n ∈ V eventually.
- **Mathlib needed**: `Ideal.span_singleton_pow`, `Homeomorph.mulLeft₀`,
  `Filter.Tendsto` unfolding of `IsTopologicallyNilpotent`.
- **Sources**: decomposition L1.6 (standard Tate-ring facts; [SW §11.2] pattern).

### [T103] O_F is ϖ-adically separated and complete (L1.7–L1.8)
- **Status**: open | **File**: PerfectoidFieldCharP.lean | **Depends**: T102
- **Statements**: `isHausdorff_span_toOF`, `isAdicComplete_span_toOF`.
- **Sketch**: (1) Hausdorff: `IsHausdorff` unfolds to SMOD-congruences; an element in
  all `ϖ^n O_F` lies in every neighbourhood of 0 (T102 converse) hence = 0 by the
  `T0Space F` class field (T0 topological group separation:
  `t0Space_iff`/`specializes`-API or the project's preferred route). (2) Complete: given
  a ϖ-adic Cauchy family, it is Cauchy in F (T102 forward), converges by `CompleteSpace
  F`; the limit is power-bounded via `isPowerBounded_of_tendsto_of_powerBounded`
  (PerfectoidRing.lean, audit-verified); ϖ-adic convergence via T102 converse. Assemble
  with `IsPrecomplete`/`IsAdicComplete` constructors and the project `AdicConvergence`
  API.
- **Mathlib needed**: `IsAdicComplete` constructors, `SModEq` bridges
  (`SModEq.sub_mem`), `CompleteSpace.complete`.
- **Sources**: decomposition L1.7–L1.8 ([Bhatt Cor. 3.2.3] verbatim quote there).

### [CLEANUP-1] /cleanup on PerfectoidFieldCharP.lean
- **Status**: open | **Depends**: T103 (final per-file; 3 proof tickets).

### [T201] A_inf: Teichmüller lemmas + topological ring (L2.1–L2.2)
- **Status**: open | **File**: FarguesFontaine/AinfHuber.lean | **Depends**: T101
- **Statements**: `teichPi_pow`, `teichPi_ne_zero`, `instIsTopologicalRingAinf`.
- **Sketch**: (1) `teichPi_pow`: `map_pow` of the `teichmuller` MonoidHom. (2)
  `teichPi_ne_zero`: Teichmüller coeff-0 is `ϖof ≠ 0` (T101) — `WittVector.ext_iff` or
  coeff API. (3) topological ring: the adic topology is a ring topology — mathlib route
  via `RingSubgroupsBasis` (see `Ideal.adicTopology`'s definition; instance-producing
  spelling per AdicTopology.lean's own `isAdic_iff` proof pattern).
- **Mathlib needed**: `MonoidHom.map_pow`, `WittVector.teichmuller_coeff`-family,
  `RingSubgroupsBasis.toRingFilterBasis` route.
- **Sources**: decomposition L2.1–L2.2 ([SW §13.1] quote).

### [T202] A_inf is Huber with A⁺ = A_inf (L2.3–L2.5)
- **Status**: open | **File**: AinfHuber.lean | **Depends**: T201, T102
- **Statements**: `isAdic_Iinf`, `instIsHuberRingAinf`, `isPowerBounded_Ainf`,
  `isAffinoidRing_Ainf`.
- **Sketch**: (1) `isAdic_Iinf` via mathlib `isAdic_iff`: (i) `Iinf ϖ`-powers are open
  and (ii) every neighbourhood of 0 contains one — for the canonical-ϖ instance both
  hold by definition; for arbitrary ϖ use mutual divisibility: `ϖ'^n ∈ ϖ·O_F` (T102) +
  `teichPi_pow` + monomial expansion (decomposition L2.3 attack [2] records the ~20-line
  bookkeeping). (2) Huber: `PairOfDefinition` with `A₀ = ⊤`, ideal = `Iinf` transported
  along `Subring.topEquiv`; fg by the 2-element generating set. (3) power-boundedness:
  `{x^k}·I^n ⊆ I^n` (ideal absorption) makes `Set.range (x^·)` bounded. (4) affinoid:
  ⊤ open + integrally closed + (3).
- **Mathlib needed**: `isAdic_iff`, `Subring.topEquiv`, `Ideal.span` finiteness API.
- **Sources**: decomposition L2.3–L2.5 ([Ked-AWS §11.2] independence quote; [Ked-AWS
  Def 3.1.5]).

### [T203] The filtration sandwich (L2.6)
- **Status**: open | **File**: AinfHuber.lean | **Depends**: T201 | **Parallel**: with T202
- **Statement**: `Iinf_pow_two_mul_le : Iinf ϖ ^ (2*n) ≤ span {p}^n ⊔ span {[ϖ]}^n`.
- **Sketch**: induction/`Ideal.span_pow` expansion: `Iinf^(2n)` is generated by
  monomials `p^a [ϖ]^b`, `a+b = 2n`; `a ≥ n ∨ b ≥ n`; place accordingly. Use
  `Ideal.span_insert`, `Ideal.pow_le_iff`-shape or the `Finset`-free two-generator
  expansion (`Ideal.add_pow_le`? — mathlib has `Ideal.add_pow_le : (I + J)^(m+n-1)-ish`?
  If `Ideal.add_pow_le` exists with the right shape, the proof is 3 lines; check first
  via loogle "Ideal.add ^ ≤").
- **Sources**: decomposition L2.6 (elementary; sandwich for the completeness transfer).

### [CLEANUP-2] /cleanup on AinfHuber.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T203.

### [T204] A_inf is (p,[ϖ])-adically separated (L2.7)
- **Status**: open | **File**: AinfHuber.lean | **Depends**: T103, T203, CLEANUP-2
- **Statement**: `isHausdorff_Iinf`.
- **Sketch**: x ∈ ⋂ Iinf^n ⟹ (T203) x ∈ ⋂ ((p)^n ⊔ ([ϖ])^n); describe coordinates:
  `p^n·A` has coeffs 0..n-1 zero (mathlib WittVector.Complete's span-p
  characterisation), `[ϖ]^n·y` has coeff i = `ϖof^(n·p^i) · y.coeff i`
  (`teichmuller_mul_pow_coeff`-family, TeichmullerSeries.lean); conclude each coeff of
  x lies in ⋂_m ϖ^m O_F = 0 (T103). RE-DERIVE the coordinate description on paper
  first (RR1); if the sum-decomposition x = p-part + [ϖ]-part obstructs coordinatewise
  reasoning, switch to SMOD form: x ≡ 0 [SMOD (p)^n ⊔ ([ϖ])^n] and evaluate
  `truncate n`.
- **Sources**: decomposition L2.7 (+[Ked-AWS Def 3.1.2] quote), RR1 register.

### [T205] ★ SUMMIT: A_inf is (p,[ϖ])-adically complete (L2.8)
- **Status**: open | **File**: AinfHuber.lean | **Depends**: T204
- **Statement**: `isAdicComplete_Iinf`.
- **Sketch**: (1) prove the transfer lemma "mutually cofinal filtrations share
  IsAdicComplete" (Iinf^(2n) ≤ (p)^n ⊔ ([ϖ])^n ≤ Iinf^n, T203) — search mathlib for an
  existing congruence (`IsAdicComplete` under `≤`-cofinal ideals) first. (2) for the
  product filtration: given coherent (x_n), per Witt coordinate i extract ϖ-adically
  Cauchy sequences; converge by T103; define the limit x coordinatewise; verify
  coherence mod (p)^n ⊔ ([ϖ])^n using mathlib's p-adic completeness
  `WittVector.isAdicCompleteIdealSpanP` for the p-direction and
  `teichmuller_mul_pow_coeff` for the [ϖ]-direction. (3) HARD-STOP RULE: if the
  coordinatewise route develops a genuine gap, do NOT improvise — B2-report and switch
  to the documented fallback (inverse-limit presentation `W(O_F) = lim_m W(O_F/ϖ^m)`,
  Bhatt-diagram pattern), which is a plan revision (new sub-tickets), not a statement
  change. External-review packet (RR3) should be re-sent before starting this ticket.
- **Sources**: decomposition L2.8 + RR1 (quotes there); mathlib
  `WittVector/Complete.lean` as the formal p-direction anchor.

### [CLEANUP-3] /cleanup on AinfHuber.lean (final per-file)
- **Status**: open | **Depends**: T205.

### [T301] Frobenius identities (L3.1–L3.2, L3.5)
- **Status**: open | **File**: FarguesFontaine/FrobeniusAction.lean | **Depends**: T201
- **Statements**: `frob_natCast`, `frob_teichPi`, `ofAdd_zsmul_def`.
- **Sketch**: (1) `map_natCast (frob p F)`. (2) `frobenius_eq_map_frobenius` (CharP) +
  `map_teichmuller` + `teichPi_pow`: φ([ϖ]) = [ϖ^p] = [ϖ]^p — mind that
  `frobeniusEquiv`'s forward map is definitionally `frobenius` (Frobenius.lean:286).
  (3) unfolding: by `rfl` if `MulSemiringAction.compHom`/`zpowersHom` reduce;
  otherwise `Int.induction_on` with `zpow_add_one`/`zpow_sub_one`.
- **Sources**: decomposition L3.1–L3.2 ([SW §12.2]).

### [T302] Frobenius is a homeomorphism (L3.3 — corrected bound)
- **Status**: open | **File**: FrobeniusAction.lean | **Depends**: T301, T202
- **Statements**: `map_frob_Iinf_pow_le`, `Iinf_pow_succ_mul_le_map_frob` (exponent
  `(p+1)*n` — the 2n version is FALSE for p ≥ 3, see decomposition L3.3 attack log),
  `continuous_frob`, `continuous_frob_symm`.
- **Sketch**: (1) forward: generators p ↦ p, [ϖ] ↦ [ϖ]^p ∈ I; `Ideal.map` of span =
  span of images; monotone powers. (2) reverse: φ(I^n) = (p, [ϖ]^p)^n as ideals
  (automorphism image of span); monomial p^a[ϖ]^b with a+b = (p+1)n has a ≥ n or
  b ≥ pn; in the second case [ϖ]^b ∈ ([ϖ]^p)^n. (3) continuity: additive-group
  continuity criterion at 0 with the `Ideal.adicTopology` basis
  (`Ideal.hasBasis_nhds_zero`-shape), one direction per map.
- **Sources**: decomposition L3.3 (attack log documents the corrected exponent).

### [T303] The φ^ℤ-action reaches Spa (L3.4, L3.6–L3.7)
- **Status**: open | **File**: FrobeniusAction.lean | **Depends**: T302
- **Statements**: `instContinuousConstSMulAinf`, `smul_mem_spa_Ainf`
  (+ regression: `instMulSemiringActionAinf` is already sorry-free; ValuationAction's
  `[Finite G]` drop is already in the tree — keep both green).
- **Sketch**: (1) `ContinuousConstSMul`: for g = ofAdd k, smul = (frob^k); continuity
  by `Int.induction_on` from T302 (both directions needed for negative k). (2)
  `smul_mem_spa_Ainf` := `ValuationSpectrum.smul_mem_spa` with stability `fun _ _ _ =>
  Subring.mem_top _`.
- **Sources**: decomposition L3.4–L3.7 ([SW §12.2] quote).

### [CLEANUP-4] /cleanup on FrobeniusAction.lean (final per-file)
- **Status**: open | **Depends**: T303.

### [T401] 𝒴: basic-open description and element facts (L4.1 + part of L4.4)
- **Status**: open | **File**: FarguesFontaine/YSpace.lean | **Depends**: T201 | **Parallel**: with T30x
- **Statements**: `Y_eq_spa_inter_basicOpen`, `isOpen_Y`, `v_p_ne_zero`,
  `v_teichPi_ne_zero`.
- **Sketch**: (1) set-extensionality: `basicOpen f f` membership is (refl ∧ ¬ v f ≤ 0);
  reflexivity from the ValuativeRel preorder. (2) openness: the legacy `Y_FF_isOpen`
  proof pattern (subtype-val preimage of a basicOpen; `isOpen_basicOpen` +
  `continuous_subtype_val`), line-for-line. (3) product nonvanishing splits: supp-prime
  API (`v.supp` prime, project ValuationSpectrum) or direct: v(p·[ϖ]) ≤ 0 ⟸ v(p) ≤ 0
  by vle-mul-compat.
- **Sources**: decomposition L4.1, L4.4 ([BFHHLWY Def 2.1.1] + [Ked-AWS Rem 3.1.9]
  quotes).

### [T402] 𝒴: φ-stability and ϖ-independence (L4.2–L4.3)
- **Status**: open | **File**: YSpace.lean | **Depends**: T401, T301, T102
- **Statements**: `smul_mem_Y`, `Y_indep`.
- **Sketch**: per decomposition L4.2/L4.3: Teichmüller-power divisibility + supp
  primality; for smul: (g•v)(p·[ϖ]) ≠ 0 ⟺ v(p) ≠ 0 ∧ v([ϖ^{p^{-k}}]) ≠ 0, and the
  latter's p^k-th power is v([ϖ]).
- **Sources**: decomposition L4.2–L4.3 ([Ked-AWS §11.2] quote; [SW §12.2] quote).

### [T403] 𝒴: strictness and cofinality from continuity (L4.4–L4.5)
- **Status**: open | **File**: YSpace.lean | **Depends**: T401
- **Statements**: `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`,
  `exists_pow_teichPi_vlt`.
- **Sketch**: unfold `Valuation.IsContinuous` at γ = value of the target element via
  the `ValuativeRel.valuation` bridge; the open set contains some `Iinf^N` (adic
  basis); evaluate at p^N resp. [ϖ]^N; for strictness run the γ = v(p) instance and
  close the `γ ≥ 1 ⟹ γ^N ≥ γ` chain (linear-ordered group-with-zero pow-mono lemmas).
  Mind the N = 0 edge (decomposition L4.5 attack [2]).
- **Sources**: decomposition L4.4–L4.5.

### [CLEANUP-5] /cleanup on YSpace.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T403.

### [T404] The κ-predicate core (L4.6, L5.1)
- **Status**: open | **File**: YSpace.lean | **Depends**: T403, CLEANUP-5
- **Statements**: `KGE_iff`, `KLE_iff`, `KGE_or_KLE`, `not_KGE_of_KLE_of_lt`,
  `one_lt_cFF`, `cFF_lt_p`.
- **Sketch**: (1) iffs: cross-multiplication: from q = a/b = num/den derive
  a·den = num·b (`Rat` API: `Rat.num_div_den`, `div_eq_div_iff`); then
  vle-power-cancellation γ^k ≤ δ^k ⟺ γ ≤ δ (strict-mono pow on
  LinearOrderedCommGroupWithZero via the valuation bridge; `pow_le_pow_iff_left₀`-shape
  — locate exact name). (2) totality: ValuativeRel linearity axiom. (3)
  incompatibility: clear both to a common denominator; flip rule
  `pow_le_pow_iff_right_of_lt_one₀`-shape with 0 < v(p) < 1 (T403). (4) cFF bounds:
  `norm_num`-level rational arithmetic with `1 < p` from `(Fact.out :
  p.Prime).one_lt`.
- **Mathlib needed**: named pow-order lemmas on `LinearOrderedCommGroupWithZero` —
  verify names by loogle before coding (the decomposition flags this as the one
  mathlib-name uncertainty of R3).
- **Sources**: decomposition L4.6/L5.1 ([Ked-AWS Rem 3.1.9] verbatim; orientation
  cross-checked against [SW Fig. 12.1] in the decomposition).

### [T405] The covering 𝒴 = ⋃ (U_n ∪ V_n) (L5.5)
- **Status**: open | **File**: YSpace.lean | **Depends**: T404
- **Statement**: `Y_eq_iUnion_windows`.
- **Sketch**: per decomposition L5.5: cofinality → KLE(p^N), KGE(p^{-N}); the set
  {n : ℤ | KGE(p^n)} ∩ [-N, N] is nonempty-bounded; take max (Int/Finset.max');
  totality at p^{n₀+1}; split at c·p^{n₀}. All ordered-field arithmetic on ℚ-indices +
  KGE/KLE monotonicity (prove tiny `KGE.mono`/`KLE.mono` helpers inline if not already
  forced by T404's iff forms).
- **Sources**: decomposition L5.5 ([Ked-AWS Rem 3.1.9] quote; higher-rank check in the
  attack log).

### [T406] Window translation, disjointness, openness (L5.2–L5.4)
- **Status**: open | **File**: YSpace.lean | **Depends**: T404, T402
- **Statements**: `zsmul_windowU`, `zsmul_windowV`, `windowU_disjoint`,
  `windowV_disjoint`, `isOpen_windowU`, `isOpen_windowV`.
- **Sketch**: (1) translation: KGE-transformation under the action (evaluate at
  Teichmüller of the p^{-k}-th root; clear via ^(p^k); ℚ-index arithmetic
  `zpow_add`); Set.smul_set images by the bijective action. (2) disjointness:
  `not_KGE_of_KLE_of_lt` at the interval endpoints; rational strict inequalities from
  `one_lt_cFF`/`cFF_lt_p`. (3) openness: windows = Y ∩ two basicOpen-conditions; the
  ≠0 side-conditions hold on Y (T401); reuse the isOpen_Y pattern for finite
  intersections.
- **Sources**: decomposition L5.2–L5.4 ([Ked-AWS Rem 3.1.9]; [SW §12.2] κ∘φ = pκ).

### [CLEANUP-6] /cleanup on YSpace.lean (final per-file)
- **Status**: open | **Depends**: T406.

### [T501] Freeness and wandering (L6.1–L6.2)
- **Status**: open | **File**: FarguesFontaine/Curve.lean | **Depends**: T405, T406
- **Statements**: `smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`.
- **Sketch**: pure set logic over T405/T406 per decomposition §4 prose: membership in
  some window; translated window is the (n-k)-window; within-family disjointness
  forbids fixation; the window itself is the wandering neighbourhood.
- **Sources**: decomposition L6.1–L6.2 ([Ked-AWS §3.1] and [SW Def 13.5.1] quotes).

### [T502] The quotient map is an open quotient map (L6.3, L7.1)
- **Status**: open | **File**: Curve.lean | **Depends**: T402, T303
- **Statements**: `instMulActionYSub` laws, `instContinuousConstSMulYSub`,
  `toCurve_surjective`, `isOpenQuotientMap_toCurve`.
- **Sketch**: subtype-action laws by `Subtype.ext` + parent action laws (pattern:
  ValuationAction's `instMulActionCont`); continuity by
  `Continuous.subtype_mk`∘`continuous_subtype_val` from the Spv-level
  `comap_continuous`; surjectivity `Quotient.mk_surjective`; open-quotient by mathlib
  `MulAction.isOpenQuotientMap_quotientMk`.
- **Sources**: decomposition L6.3, L7.1 ([BFHHLWY Def 2.1.1] verbatim).

### [T503] ★ MILESTONE: Kedlaya's two charts (L7.2–L7.3)
- **Status**: open | **File**: Curve.lean | **Depends**: T501, T502, CLEANUP-ALL-1
- **Statements**: `injOn_toCurve_windowU`, `injOn_toCurve_windowV`,
  `curve_eq_image_window_zero`.
- **Sketch**: injectivity: orbit-mates in one window contradict wandering unless k = 0
  (decomposition L7.2); covering: shift the covering index to 0 by acting with ofAdd n
  (mind the D5 sign, recomputed in L7.3's attack log).
- **Sources**: decomposition L7.2–L7.3 ([Ked-AWS Rem 3.1.9] verbatim: "The spaces U_0
  and V_0 map isomorphically to their images in X_S and cover the latter").

### [CLEANUP-7] /cleanup on Curve.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T503.

### [T504] The curve is T0 (L7.4)
- **Status**: open | **File**: Curve.lean | **Depends**: T503, CLEANUP-7
- **Statement**: `instT0SpaceCurve`.
- **Sketch**: distinct orbits: if some window meets both, separate inside the chart
  (chart is an open embedding by T502+T503; Spv/Spa T0 — locate or prove the small
  Spv-T0 lemma flagged in decomposition L7.4); otherwise the open image of the window
  of x avoids y's orbit. Assemble with `t0Space_iff_inseparable`-API.
- **Sources**: decomposition L7.4.

### [T505] The curve is quasicompact (L7.5 — RR2, descopable)
- **Status**: open | **File**: Curve.lean | **Depends**: T503
- **Statements**: `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`.
- **Sketch**: route A: Boolean-embedding closed-image criterion
  (`isCompact_spa_of_isClosed_image`-family, SpaCompact.lean) — the window is cut out
  by finitely many vle-coordinate conditions; route B: qc of `basicOpen`-intersections
  via SpaQCviaSpvAI. **If neither route lands within budget: HARD-STOP, mark T505
  blocked, leave the three sorries** (no dependents; the campaign closes without them
  per RR2) — do NOT weaken statements.
- **Sources**: decomposition L7.5 ([Ked-AWS Rem 3.1.9]: "covered by two affinoid
  subspaces").

### [CLEANUP-8] /cleanup on Curve.lean (final per-file)
- **Status**: open | **Depends**: T505 (or T504 if T505 blocked).

### [CLEANUP-ALL-1] /cleanup-all over the campaign so far
- **Status**: open | **Depends**: T501, T502, CLEANUP-1..6 | blocks T503 (pre-milestone
  pass per cadence rule).

### [T601] STRETCH (blocked-on-plan): 𝒴 is nonempty (L7.6)
- **Status**: blocked | **File**: Curve.lean | **Depends**: fresh `/develop --continue`
  sub-decomposition (Gauss norms, [FF §1.4]); do NOT start from this board.
- **Statement**: `Y_nonempty`.

### [CLEANUP-FINAL] /cleanup-all over the whole campaign
- **Status**: open | **Depends**: everything above (T601 excluded if still blocked).

---

Cadence audit: 22 core proof tickets → ⌈22/3⌉ = 8 in-flow cleanups (CLEANUP-1..8 ✓,
noting files with exactly 3 tickets merge the in-flow and final roles), plus final
per-file covered (1,3,4,6,8), CLEANUP-ALL-1 before milestone T503 ✓, CLEANUP-FINAL ✓.
