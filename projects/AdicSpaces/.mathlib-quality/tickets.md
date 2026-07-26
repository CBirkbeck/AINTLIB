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
- **Status**: done (beastmode, 2026-07-24T14:00Z → 2026-07-24T14:55Z) | **File**: FarguesFontaine/PerfectoidFieldCharP.lean | **Depends**: none | **Parallel**: yes
- **Progress**:
  - 14:05: all five sorries filled first-strike except CharP (semi-out-param + wrong-direction `charP_of_injective_ringHom` — it pushes char domain→codomain; wrote the `cast_eq_zero_iff` instance directly instead; added `Mathlib.Algebra.CharP.Algebra` import).
  - 14:20: zero errors; `lean_verify` on all substantive decls → `[propext, Classical.choice, Quot.sound]`; module `lake build` green.
  - 14:45: Phase 6.5 cleanup on `frobenius_surjective_OF`: 8→3-line proof (`obtain ⟨y, hy, z, -, hxyz⟩` + `Subtype.ext (by simp [frobenius_def, hxyz])`), docstring tightened (+"semiperfect" gloss, Bhatt citation kept), all gates pass, no renames queued. Flag-only note: proof works at `IsPerfectoidRing` generality (field-ness unused) — future `/generalise` candidate, statement frozen this campaign.
  - 14:55: Phase 6.6 buzz: FAST-BOARD (decl < 100ms profiler threshold; no maxHeartbeats anywhere; no scaffolding). DONE — L1.1–L1.5 discharged.
- Post-proof cleanup: ✓ ran (gates pass, simplify-equivalent golf ran in worker, buzz FAST-BOARD, no flags; four ≤2-line term/instance proofs below cleanup action threshold — recorded per Mode-A judgment)
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
- **Mathlib needed** (name-verified 2026-07-24): `charP_of_injective_ringHom` ✓
  (Algebra/CharP), `frobenius_inj` ✓ (Algebra/CharP/Reduced.lean:28, reduced rings),
  `PerfectRing.ofSurjective` ✓ (FieldTheory/Perfect.lean:97 — check its
  IsReduced/ExpChar hypotheses at fill time), `Units.ne_zero` ✓.
- **Sources**: decomposition L1.1–L1.5 ([Bhatt §3.1 Ex. 3.1.2(3)] verbatim quote there).

### [T102] O_F: the ϖ-adic neighbourhood basis (L1.6)
- **Status**: done (beastmode, 2026-07-25; B2-blocked 2026-07-25 00:35Z → class repair
  executed same day per owner's option 1 → both theorems proven and axiom-clean)
  | **File**: PerfectoidFieldCharP.lean | **Depends**: T101 | **Parallel**: —
- **Progress**:
  - B2 interlude: the inherited `[IsLinearTopology F F]` hypothesis was unsatisfiable for
    Tate fields (b2_log.jsonl 2026-07-25; decomposition §6.5). Owner approved repair
    option 1; classes + engine + all consumers now ride `[NonarchimedeanRing _]`; the
    two T102/T103 statement signatures gained an explicit `[IsPerfectoidField p F]`
    binder (the pinned `OF`/`toOF` signatures no longer auto-include it).
  - `span_toOF_pow_mem_nhds_zero`: proven — `ϖ^n·F°` is the image of the open `F°`
    (`P.isOpen_powerBoundedSubring`) under the unit-multiplication homeomorphism
    (`Homeomorph.mulLeft₀`), pulled back along `nhds_subtype_eq_comap`.
  - `exists_span_toOF_pow_subset_of_mem_nhds`: proven — boundedness of `F°`
    (`IsUniform.isBounded_powerBounded`) + topological nilpotence
    (`exists_pow_mem_of_mem_nhds`) land `c·ϖ^n` in `F°·V ⊆ U'`.
  - Both `#print axioms` = `[propext, Classical.choice, Quot.sound]` (probe-verified).
  - Phase 6.5 cleanup (two Phase-4 workers, all gates pass): `span_toOF_pow_mem_nhds_zero`
    12→6 lines (`IsUnit.isOpenMap_smul` + `mem_nhds_subtype` replace the hand-rolled
    Homeomorph/comap plumbing); `exists_span_toOF_pow_subset_of_mem_nhds` 14→7 lines
    (haveI eliminated — `IsUniform F` genuinely not synthesizable, now an explicit
    projection; tail collapsed to one simpa). Phase 5b rename applied:
    `…_subset_nhds` → `…_subset_of_mem_nhds` (mathlib `exists_*_subset_of_mem_nhds`
    precedent); queue truncated. Phase 6.6 buzz: FAST-BOARD. Flag-only notes: Tate-ring
    generalisation candidate (both proofs use only uniformity + the Huber pair);
    file-wide unusedSectionVars (duplicate perfectoid binder + unused CharP) is a
    campaign-level variable-block decision; the two lemmas form the halves of mathlib's
    `isAdic_iff` — bundling corollary possible once T103 lands.
- Post-proof cleanup: ✓ ran (both workers pass, rename applied, buzz FAST-BOARD)
- **Statements**: `span_toOF_pow_mem_nhds_zero`, `exists_span_toOF_pow_subset_of_mem_nhds`.
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
- **Status**: done (beastmode, 2026-07-25; both theorems axiom-clean
  `[propext, Classical.choice, Quot.sound]`, probe-verified) | **File**: PerfectoidFieldCharP.lean | **Depends**: T102
- **Progress**:
  - `isHausdorff_span_toOF`: 13-line proof — SMOD membership → x in every ϖ-power ideal →
    (T102 exists-lemma) x in every neighbourhood of 0 → `0 ∈ closure {x}` →
    `isClosed_singleton` (T0 from the class field + subtype + add-group chain) → x = 0.
  - `isAdicComplete_span_toOF`: IsPrecomplete engine — coherence → membership form;
    Cauchy in F via open-subgroup symmetrization (`NonarchimedeanAddGroup.is_nonarchimedean`,
    boundedness of F°, `exists_pow_mem_of_mem_nhds`, `Ideal.pow_le_pow_right`);
    `cauchySeq_tendsto_of_complete` + topologyEq transport; limit power-bounded via the
    REPAIRED (now public) `IsPerfectoidRing.isPowerBounded_of_tendsto_of_powerBounded`;
    `f n − L ∈ I^n` by the open-hence-closed subgroup `I^n`
    (`AddSubgroup.isOpen_of_mem_nhds` from T102 + `isClosed_of_isOpen` +
    `IsClosed.mem_of_tendsto`). M1 (O_F layer) COMPLETE.
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
- **Status**: done (beastmode 2026-07-25; axiom-clean) — `teichPi_pow` = `map_pow` of the
  `teichmuller` MonoidHom; `teichPi_ne_zero` via coeff-0 + T101 `toOF_ne_zero`;
  `instNonarchimedeanRingAinf := Ideal.nonarchimedean _` SUPERSEDES the planned
  `instIsTopologicalRingAinf` (IsTopologicalRing flows from `NonarchimedeanRing extends`;
  probe-verified synthesis). | **File**: FarguesFontaine/AinfHuber.lean | **Depends**: T101
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
- **Status**: done (beastmode 2026-07-25; all axiom-clean) — new divisibility engine
  `exists_teichPi_pow_mem_span_teichPi` (ϖ·F° nbhd + top-nilpotence + multiplicative
  Teichmüller) and cofinality `Iinf_pow_le_of_teichPi_pow_mem` ((p,[ϖ'])^((k+1)m) ⊆
  (p,[ϖ])^m via `Ideal.sup_pow_add_le_pow_sup_pow`); `isAdic_Iinf` = canonical-ϖ `rfl` +
  cofinality both ways + `AddSubgroup.isOpen_mono`; `instIsHuberRingAinf` REUSES
  `isHuberRing_ofAdic` (TateAlgebraTopology.lean ⊤-ring-of-definition transport — no new
  transport code); `isPowerBounded_Ainf` via adic basis + ideal absorption;
  `isAffinoidRing_Ainf` trivial fields + power-boundedness. | **File**: AinfHuber.lean | **Depends**: T201, T102
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
- **Status**: done (beastmode 2026-07-25; axiom-clean) — 2 lines:
  `span_insert` + `two_mul` + mathlib `Ideal.sup_pow_add_le_pow_sup_pow`
  (correcting the 2026-07-24 name-check: the lemma DOES exist, found via loogle). | **File**: AinfHuber.lean | **Depends**: T201 | **Parallel**: with T202
- **Statement**: `Iinf_pow_two_mul_le : Iinf ϖ ^ (2*n) ≤ span {p}^n ⊔ span {[ϖ]}^n`.
- **Sketch**: induction/`Ideal.span_pow` expansion: `Iinf^(2n)` is generated by
  monomials `p^a [ϖ]^b`, `a+b = 2n`; `a ≥ n ∨ b ≥ n`; place accordingly. Use
  `Ideal.span_insert`, `Ideal.pow_le_iff`-shape or the `Finset`-free two-generator
  expansion. (Name-verification 2026-07-24: `Ideal.add_pow_le` was NOT found in
  mathlib's Ideal/Operations — plan for the manual `span_pow` monomial expansion;
  re-check via loogle at fill time in case it lives elsewhere.)
- **Sources**: decomposition L2.6 (elementary; sandwich for the completeness transfer).

### [CLEANUP-2] /cleanup on AinfHuber.lean (after 3rd proof ticket on file)
- **Status**: open (due — T201+T202+T203 done; deferred to after T205 per user
  redirection 2026-07-25 "keep going with the FF constructions" — one cleanup pass when
  the file is sorry-free) | **Depends**: T203.

### [T204] A_inf is (p,[ϖ])-adically separated (L2.7)
- **Status**: done (beastmode 2026-07-25; axiom-clean). Route as validated but LEANER
  than the L2.7a–d skeleton: no truncated-Witt ring theory needed — the joint ideal
  `(p^r, [ϖ]^s)` engine (private helpers in AinfHuber.lean) converts joint-ideal
  congruence into coefficientwise ϖ-power congruence via the RING HOM
  `truncate r ∘ map (Quotient.mk (ϖ^s))` (kernel framing kills every
  coeff-of-difference/Witt-addition issue), with `mul_pow_charP_coeff_zero` for the
  p-direction; separatedness = T103 Hausdorff per coefficient + `WittVector.ext`. | **File**: AinfHuber.lean | **Depends**: T103, T203, CLEANUP-2
- **Statement**: `isHausdorff_Iinf`.
- **Sketch** (ROUTE REPLACED per the gpt-5.6-sol review, decomposition L2.7a–d; the
  old digit-extraction sketch is void): begin the truncated-Witt layer. (1) State as
  private skeleton lemmas (prose frozen in decomposition L2.7a–c): `A/p^r A ≅ W_r(O_F)`
  for perfect O_F (mathlib Complete.lean truncate-kernel machinery); the digit
  sandwich `C_{m·p^{r-1}} ⊆ [ϖ]^m·W_r(O_F) ⊆ C_m` with `C_s = (ϖ^s O_F)^r`
  (Teichmüller digit lemmas `[ϖ]^m·[z]·p^i = [ϖ^m z]·p^i` — the general diagonal
  product formula is NOT in mathlib, avoid it); `W_r(O_F)` is `[ϖ]`-adically separated
  (finite product of T103's separatedness via the sandwich). (2) Separatedness of A:
  x ∈ ⋂ Iinf^n ⟹ (T203 sandwich) x ∈ ⋂ (p^r + [ϖ]^s) over all r,s ⟹ its image in
  every `W_r(O_F)` lies in ⋂_s [ϖ]^s = 0 ⟹ x ∈ ⋂_r p^r A = 0 (mathlib
  `isAdicCompleteIdealSpanP`'s Hausdorff part).
- **Sources**: decomposition L2.7 (+[Ked-AWS Def 3.1.2] quote), RR1 register.

### [T205] ★ SUMMIT: A_inf is (p,[ϖ])-adically complete (L2.8)
- **Status**: DONE (beastmode 2026-07-25; axiom-clean; AinfHuber.lean SORRY-FREE).
  Assembly avoided lim-of-lims entirely: direct `IsPrecomplete` construction — coefficient
  sequences (shifted reindex `f (2(m+j+1))`) are ϖ-adically coherent via the joint-ideal
  coefficient lemma, T103 completeness gives per-digit limits ℓ_j, the limit is
  `WittVector.mk p ℓ`, and the final congruence transfers back through
  `sub_mem_jointIdeal_of_coeff_sub_mem` (whose reverse inclusion
  `ker(truncate∘map) ⊆ (p^r,[ϖ]^s)` rides on mathlib
  `WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` + perfectness —
  replacing the planned digit-sandwich/(★)-formula: [θ^{-i} x_i] factors give the
  [ϖ^s]-divisibility of the Teichmüller tail directly). Rates: `M := n·p^{n-1} + n + 1`.
  New helpers: `jointIdeal`, cofinality bridges, `charP_quotient_span_pow` (uses new
  `PseudoUniformizer.not_isUnit_toOF` in PerfectoidFieldCharP.lean + Bezout),
  `frobeniusEquiv_symm_pow_apply_pow_mul`, the two coefficient-congruence lemmas. | **File**: AinfHuber.lean | **Depends**: T204
- **Statement**: `isAdicComplete_Iinf`.
- **Sketch** (ROUTE REPLACED per the gpt-5.6-sol review, decomposition L2.7a–d —
  externally validated; the old coordinatewise plan is VOID (Q2 GAP: J-Cauchy data
  does not split into separate p- and ϖ-direction Cauchy data, and Witt addition is
  not digit-wise), and so is the old fallback `lim_m W(O_F/ϖ^m)` (non-cofinal: p^n A
  leaves high digits uncontrolled)): (1) `W_r(O_F)` is `[ϖ]`-adically complete for
  each r (T204's truncated layer: digit sandwich + T103 digit-wise limits).
  (2) Assembly: `A ≅ lim_r A/p^r` (mathlib `isAdicCompleteIdealSpanP` + L2.7a)
  `≅ lim_r lim_s A/(p^r + [ϖ]^s)` (each level by (1)) `≅ lim_n A/(p^n + [ϖ]^n)`
  (double limit; diagonal cofinal in ℕ²). (3) Transfer along the T203 sandwich
  (Iinf^{2n} ≤ (p)^n ⊔ ([ϖ])^n ≤ Iinf^n) to `IsAdicComplete (Iinf ϖ)`; search mathlib
  for an existing `IsAdicComplete`-under-cofinal-filtrations congruence first, else
  prove the small reusable transfer lemma. (4) HARD-STOP RULE: any genuine obstruction
  is a B2-report (plan revision), never an improvisation; the route carries external
  sign-off, so an obstruction most likely means a mathlib-API mismatch, not
  mathematics.
- **Sources**: decomposition L2.7a–d (sol-validated route, verbatim in
  `chatgpt-reply-fargues-fontaine-2026-07-24.md`); mathlib `WittVector/Complete.lean`
  as the formal p-direction anchor.

### [CLEANUP-3] /cleanup on AinfHuber.lean (final per-file)
- **Status**: open | **Depends**: T205.

### [T301] Frobenius identities (L3.1–L3.2, L3.5)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — `frob_natCast` = `map_natCast`;
  `frob_teichPi` via `show`-defeq to `WittVector.frobenius` + `frobenius_eq_map_frobenius`
  + `map_teichmuller` + T201 `teichPi_pow`; `ofAdd_zsmul_def` is `rfl`. | **File**: FarguesFontaine/FrobeniusAction.lean | **Depends**: T201
- **Statements**: `frob_natCast`, `frob_teichPi`, `ofAdd_zsmul_def`.
- **Sketch**: (1) `map_natCast (frob p F)`. (2) `frobenius_eq_map_frobenius` (CharP) +
  `map_teichmuller` + `teichPi_pow`: φ([ϖ]) = [ϖ^p] = [ϖ]^p — mind that
  `frobeniusEquiv`'s forward map is definitionally `frobenius` (Frobenius.lean:286).
  (3) unfolding: by `rfl` if `MulSemiringAction.compHom`/`zpowersHom` reduce;
  otherwise `Int.induction_on` with `zpow_add_one`/`zpow_sub_one`.
- **Sources**: decomposition L3.1–L3.2 ([SW §12.2]).

### [T302] Frobenius is a homeomorphism (L3.3 — corrected bound)
- **Status**: done (beastmode 2026-07-25; axiom-clean) — private `map_frob_Iinf`:
  `φ(I) = (p, [ϖ]^p)` by `Ideal.map_span` + the two T301 identities; forward bound by
  `pow_right_mono`; reverse `(p+1)n` bound by the same
  `Ideal.sup_pow_add_le_pow_sup_pow` monomial engine as T202; continuity both ways via
  `continuous_of_continuousAt_zero` + `hasBasis_nhds_zero_adic.tendsto_iff`
  (reverse uses `Ideal.mem_map_iff_of_surjective`). | **File**: FrobeniusAction.lean | **Depends**: T301, T202
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
- **Status**: done (beastmode 2026-07-25; axiom-clean; FrobeniusAction.lean SORRY-FREE,
  M3 COMPLETE) — private `continuous_frob_zpow` by `Int.induction_on`
  (zpow_add_one/zpow_sub_one + `RingAut.mul_apply`; inverse-apply is defeq to `.symm`);
  `instContinuousConstSMulAinf := ⟨fun g => continuous_frob_zpow p F g.toAdd⟩`;
  `smul_mem_spa_Ainf` = direct application of ValuationSpectrum.smul_mem_spa with the
  trivial ⊤-stability witness (the [Finite G] drop in ValuationAction paying off). | **File**: FrobeniusAction.lean | **Depends**: T302
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
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: FarguesFontaine/YSpace.lean | **Depends**: T201 | **Parallel**: with T30x
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
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: YSpace.lean | **Depends**: T401, T301, T102
- **Statements**: `smul_mem_Y`, `Y_indep`.
- **Sketch**: per decomposition L4.2/L4.3: Teichmüller-power divisibility + supp
  primality; for smul: (g•v)(p·[ϖ]) ≠ 0 ⟺ v(p) ≠ 0 ∧ v([ϖ^{p^{-k}}]) ≠ 0, and the
  latter's p^k-th power is v([ϖ]).
- **Sources**: decomposition L4.2–L4.3 ([Ked-AWS §11.2] quote; [SW §12.2] quote).

### [T403] 𝒴: strictness and cofinality from continuity (L4.4–L4.5)
- **Status**: done (board reconciliation 2026-07-26: content shipped in YSpace.lean during the M4/M5 waves; file is sorry-free and green) | **File**: YSpace.lean | **Depends**: T401
- **Statements**: `vlt_p_one`, `vlt_teichPi_one`, `exists_pow_p_vlt`,
  `exists_pow_teichPi_vlt`.
- **Sketch**: unfold `Valuation.IsContinuous` at γ = value of the target element via
  the `ValuativeRel.valuation` bridge; the open set contains some `Iinf^N` (adic
  basis); evaluate at p^N resp. [ϖ]^N; for strictness run the γ = v(p) instance and
  close the `γ ≥ 1 ⟹ γ^N ≥ γ` chain (linear-ordered group-with-zero pow-mono lemmas).
  Mind the N = 0 edge (decomposition L4.5 attack [2]); per the sol review (Q4),
  explicitly ENLARGE N to ≥ 2 before closing (free, since ideal powers decrease) —
  this kills the N = 0/1 edge cases uniformly. Sol also confirms `v ≤ 1` on all of
  A_inf is never needed in the window arguments; don't reach for it in proofs.
- **Sources**: decomposition L4.4–L4.5; sol review Q4
  (`chatgpt-reply-fargues-fontaine-2026-07-24.md`).

### [CLEANUP-5] /cleanup on YSpace.lean (after 3rd proof ticket on file)
- **Status**: open | **Depends**: T403.

### [T404] The κ-predicate core (L4.6, L5.1)
- **Status**: done (beastmode 2026-07-25; axiom-clean; committed cf7ef820f) | **File**: YSpace.lean | **Depends**: T403, CLEANUP-5
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
- **Status**: done (beastmode 2026-07-25; axiom-clean; YSpace.lean SORRY-FREE, M4+M5
  complete) — new KGE_mono/KLE_mono (Γ₀ pow-cancel + exponent-flip chains); κ pinned by
  cofinality with n+1-bumps through vlt_p_one/vlt_teichPi_one (kills the m=0 edges);
  greatest KGE-index via Int.exists_greatest_of_bdd; split at cFF·p^{n₀} by totality. | **File**: YSpace.lean | **Depends**: T404
- **Statement**: `Y_eq_iUnion_windows`.
- **Sketch**: per decomposition L5.5: cofinality → KLE(p^N), KGE(p^{-N}); the set
  {n : ℤ | KGE(p^n)} ∩ [-N, N] is nonempty-bounded; take max (Int/Finset.max');
  totality at p^{n₀+1}; split at c·p^{n₀}. All ordered-field arithmetic on ℚ-indices +
  KGE/KLE monotonicity (prove tiny `KGE.mono`/`KLE.mono` helpers inline if not already
  forced by T404's iff forms).
- **Sources**: decomposition L5.5 ([Ked-AWS Rem 3.1.9] quote; higher-rank check in the
  attack log).

### [T406] Window translation, disjointness, openness (L5.2–L5.4)
- **Status**: done (beastmode 2026-07-25; axiom-clean; commits efb7b6888 + a77dd0f71) —
  translation via the two procedural transport cores vle_theta_iff_ge/le (three
  vle_pow_iff_cross steps through the Teichmüller collapse; exponent identities by
  pow_add-normalization + omega, uniform in signs); disjointness via
  not_KGE_of_KLE_of_lt at endpoints; openness = Y ∩ two basicOpens with supp-prime
  side conditions. | **File**: YSpace.lean | **Depends**: T404, T402
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
- **Status**: done (beastmode 2026-07-25; pure set-logic over T405/T406 as planned;
  commit 0b076eda6) | **File**: FarguesFontaine/Curve.lean | **Depends**: T405, T406
- **Statements**: `smul_ne_of_ne_zero`, `exists_nhd_smul_disjoint`.
- **Sketch**: pure set logic over T405/T406 per decomposition §4 prose: membership in
  some window; translated window is the (n-k)-window; within-family disjointness
  forbids fixation; the window itself is the wandering neighbourhood.
- **Sources**: decomposition L6.1–L6.2 ([Ked-AWS §3.1] and [SW Def 13.5.1] quotes).

### [T502] The quotient map is an open quotient map (L6.3, L7.1)
- **Status**: done (beastmode 2026-07-25; + new Spv-level ContinuousConstSMul via
  comap_continuous; commit 0b076eda6) | **File**: Curve.lean | **Depends**: T402, T303
- **Statements**: `instMulActionYSub` laws, `instContinuousConstSMulYSub`,
  `toCurve_surjective`, `isOpenQuotientMap_toCurve`.
- **Sketch**: subtype-action laws by `Subtype.ext` + parent action laws (pattern:
  ValuationAction's `instMulActionCont`); continuity by
  `Continuous.subtype_mk`∘`continuous_subtype_val` from the Spv-level
  `comap_continuous`; surjectivity `Quotient.mk_surjective`; open-quotient by mathlib
  `MulAction.isOpenQuotientMap_quotientMk`.
- **Sources**: decomposition L6.3, L7.1 ([BFHHLWY Def 2.1.1] verbatim).

### [T503] ★ MILESTONE: Kedlaya's two charts (L7.2–L7.3)
- **Status**: DONE (beastmode 2026-07-25; commit 0b076eda6). NOTE: dispatched before
  CLEANUP-ALL-1 per the user's 2026-07-25 redirection to constructions-first; the
  cleanup backlog remains queued. | **File**: Curve.lean | **Depends**: T501, T502, CLEANUP-ALL-1
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
- **Status**: done (beastmode 2026-07-25; commit 3d870f8d5) — chart-separation engine
  sep_of_chart (T0 inside a chart via Spv-T0 + open-quotient pushforward + chart
  injectivity; across charts the open chart-image separates); windows re-opened at the
  ↥Y level. | **File**: Curve.lean | **Depends**: T503, CLEANUP-7
- **Statement**: `instT0SpaceCurve`.
- **Sketch**: distinct orbits: if some window meets both, separate inside the chart
  (chart is an open embedding by T502+T503; Spv/Spa T0 — locate or prove the small
  Spv-T0 lemma flagged in decomposition L7.4); otherwise the open image of the window
  of x avoids y's orbit. Assemble with `t0Space_iff_inseparable`-API.
- **Sources**: decomposition L7.4.

### [T505] The curve is quasicompact (L7.5 — RR2, descopable)
- **Status**: done (2026-07-26 via the T701–T706 unblock lane — see those tickets;
  formerly BLOCKED (beastmode 2026-07-25, per this ticket's hard-stop rule; three
  sorries remain by design, statements untouched). Evidence: route A's closed-image
  hypothesis (`isCompact_rationalOpen_of_isClosed_image`) is discharged in-project only
  for `[DiscreteTopology A]`; for the non-discrete non-Tate adic `A_inf` the
  Spa-continuity conditions are ∃-shaped (cofinality) = countable unions of cylinders,
  not closed — instantiating `S` needs new spectral theory (SpaCompact's own preamble
  only sketches the TATE extension, also not done). Route B: SpaQCviaSpvAI is
  incomplete (1 sorry) and exports no citable two-sided-window qc lemma. Matches the
  sol-Q5 warning that no basicOpen shortcut exists. Unblock = a dedicated dev ticket
  for the adic closed-image instantiation. | **File**: Curve.lean | **Depends**: T503
- **Statements**: `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`.
- **Sketch**: route A: Boolean-embedding closed-image criterion
  (`isCompact_spa_of_isClosed_image`-family, SpaCompact.lean) — the window is cut out
  by finitely many vle-coordinate conditions; route B: qc of the specific TWO-SIDED
  window shape via SpaQCviaSpvAI. **Sol-review warning (Q5): a bare basic-open trace
  is NOT quasicompact — 𝒴 itself is such a trace and is not qc ([Ked-AWS Rem 3.1.11]:
  Y is quasi-Stein, not quasicompact) — so no shortcut via "basicOpens are qc"; the
  bounded two-sided window structure must genuinely enter.** If neither route lands
  within budget: HARD-STOP, mark T505 blocked, leave the three sorries (no
  dependents; the campaign closes without them per RR2) — do NOT weaken statements.
- **Sources**: decomposition L7.5 ([Ked-AWS Rem 3.1.9]: "covered by two affinoid
  subspaces").

### [CLEANUP-8] /cleanup on Curve.lean (final per-file)
- **Status**: open | **Depends**: T505 (or T504 if T505 blocked).

### [CLEANUP-ALL-1] /cleanup-all over the campaign so far
- **Status**: open | **Depends**: T501, T502, CLEANUP-1..6 | blocks T503 (pre-milestone
  pass per cadence rule).

### [T601] STRETCH (blocked-on-plan): 𝒴 is nonempty (L7.6)
- **Status**: done (2026-07-26 via T805: Gauss point in GaussPoint.lean)
  sub-decomposition (Gauss norms, [FF §1.4]); do NOT start from this board.
- **Statement**: `Y_nonempty`.

### [CLEANUP-FINAL] /cleanup-all over the whole campaign
- **Status**: open | **Depends**: everything above (T601 excluded if still blocked).

---

Cadence audit: 22 core proof tickets → ⌈22/3⌉ = 8 in-flow cleanups (CLEANUP-1..8 ✓,
noting files with exactly 3 tickets merge the in-flow and final roles), plus final
per-file covered (1,3,4,6,8), CLEANUP-ALL-1 before milestone T503 ✓, CLEANUP-FINAL ✓.

---

## T505-unblock lane (planned 2026-07-26, /develop --continue; decomposition.md §T505-unblock)

### [T701] Pair-retraction substrate: W1 generalization + CofinalValue.of_le
- **Status**: done (2026-07-26, first-build green; axiom-clean) | **Files**: SpaQCviaSpvAI.lean, SpvAI.lean | **Depends**: none
- **Statements**: (1) weaken `ιSpvR_retractionSingle_eq`'s `(hIg : I = Ideal.span {g})`
  to `(hgI : g ∈ I)` (patch the one caller in `image_ιSpvR_spa_eq` with
  `hIeq ▸ Ideal.mem_span_singleton_self π`); (2) new
  `theorem Valuation.CofinalValue.of_le {v : Valuation A Γ₀} {a b : A}
  (h : CofinalValue v a) (hba : v b ≤ v a) : CofinalValue v b`.
- **Sketch**: (1) single-site edit, proof body unchanged. (2) intro γ hγ; obtain n;
  exact ⟨n, lt_of_le_of_lt (pow_le_pow_left' hba n) hn⟩.
- **Sources**: Wedhorn 7.1 p. 56 (quote in decomposition).

### [T702] The pair retraction and its two properties (W3+W4+W5)
- **Status**: done (2026-07-26; classical-decidable branch split; axiom-clean) | **File**: SpaQCviaSpvAI.lean (new section R5) | **Depends**: T701
- **Statements**: `restrictIdealSingleSpv_vle_of_vle`,
  `mem_SpvAI_span_pair_left`, `restrictIdealPairSpv` (def),
  `restrictIdealPairSpv_mem_SpvAI`, `ιSpvR_retractionPair_eq`.
- **Sketch**: per decomposition W3–W5 (branch split; dominance transfer by
  monotonicity; membership by W3 + span-pair-comm on the other branch; profile-eq by
  W1 at the branch generator).

### [T703] Pair image identification (W6+W7)
- **Status**: done (2026-07-26; mirror of the principal proof; axiom-clean) | **File**: SpaQCviaSpvAI.lean | **Depends**: T702
- **Statements**: `spaProfileConditions₂` + `isClosed_spaProfileConditions₂` +
  `image_ιSpvR_spa_eq₂`.
- **Sketch**: mirror of `image_ιSpvR_spa_eq` per decomposition W7.

### [T704] Pair compactness plumbing (W8)
- **Status**: done (2026-07-26; Wedhorn 7.35(2) for I = (g₁,g₂) landed as
  isCompact_subtype_rationalOpen₂; axiom-clean) | **File**: SpaQCviaSpvAI.lean | **Depends**: T703
- **Statements**: `isCompact_image_ιSpvR_spa₂`, `isCompact_subtype_rationalOpen₂`.
- **Sketch**: mirrors; embedding layer already general (`hIeq'` from `hpair` via
  `Ideal.map_span` + image-of-pair).

### [CLEANUP-9] /cleanup on SpaQCviaSpvAI.lean (new R5 section)
- **Status**: open | **Depends**: T704.

### [T705] Windows as rational subsets (F1)
- **Status**: done (2026-07-26; mem_rationalOpen_pair_iff engine per Wedhorn 7.30(5) +
  two trace identities with opaque cFF num/den exponents; axiom-clean) | **File**: FarguesFontaine/Curve.lean | **Depends**: none (parallel with T70x)
- **Statements**: private `windowU_zero_trace_eq` / `windowV_zero_trace_eq`
  (val-preimages of `windowU/V p F ϖ 0` = val-preimages of explicit `rationalOpen T s`).
- **Sketch**: per decomposition F1 (Wedhorn 7.30(5) product presentation;
  `vle_mul_cancel` backward, `mul_vle_mul_left` forward; supp-prime nonvanishing
  bridges; opaque `(cFF p).num.toNat`/`.den` exponents).

### [T706] ★ Window quasicompactness + CompactSpace Curve (F2+F3, closes T505)
- **Status**: DONE (2026-07-26) — **T505 CLOSED**: `isCompact_windowU_zero`,
  `isCompact_windowV_zero`, `instCompactSpaceCurve` all proven, axiom-clean;
  Curve.lean's only remaining sorry is T601 (`Y_nonempty`, stretch, blocked-on-plan).
  A_inf pair via `ainf_pair_spec` (pairOfDefinition_ofAdic reuse; hpair/hIeq by rfl-level
  idealToTop identifications); radical side conditions by the pure-power T-elements +
  `exists_teichPi_pow_mem_span_teichPi`; CompactSpace by embedding-transfer of the
  window traces into ↥Y and the T503 two-chart covering. | **File**: FarguesFontaine/Curve.lean | **Depends**: T704, T705
- **Statements**: fill `isCompact_windowU_zero`, `isCompact_windowV_zero`,
  `instCompactSpaceCurve`.
- **Sketch**: per decomposition F2 (instantiate `isCompact_subtype_rationalOpen₂` at
  the A_inf pair; `hTI` via pure powers + `exists_teichPi_pow_mem_span_teichPi`) and
  F3 (compact transfer to ↥Y, toCurve-images, T503 covering).

### [CLEANUP-10] /cleanup on Curve.lean (final; supersedes CLEANUP-8's scope)
- **Status**: open | **Depends**: T706.

---

## Campaign 8 lane A (planned 2026-07-26): Gauss valuation + Y_nonempty

### [T801] Weighted Gauss value on A_inf: definition + basic evaluations
- **Status**: done (beastmode 2026-07-26; GaussNorm.lean created; all axiom-clean) —
  perfectoidValuation extraction, teichCoeff (θ^{-n}-twist), gaussTerm/gaussValue,
  le_one, zero/one/teichmuller evaluations, p-shift w(p·x) = ρ·w(x) (via
  mul_charP_coeff and the θ-inverse cancellation), and max-attainment for ρ < 1.
  NOTE: bddAbove/evaluations thread (hρ1 : ρ ≤ 1) — for ρ > 1 the term family is
  genuinely unbounded, caught during implementation. | **File**: FarguesFontaine/GaussNorm.lean (new) | **Depends**: none
- **Statement sketch**: fix `hv : Valuation F ℝ≥0` with `hv.Integers (O_F)`
  (from `IsPerfectoidField.exists_valuation`, extracted once as a `def`), `ρ : ℝ≥0`,
  `hρ : 0 < ρ` `hρ1 : ρ < 1`. Define
  `gaussValue ρ x := ⨆ n, ρ^n * (hv (θ^{-n} (x.coeff n)))` (θ = frobeniusEquiv of O_F;
  equivalently `(hv x.coeff n)^(p^{-n})` — STEP 0: fix the convention against the
  typeset PDF of (2.2.1)/AWS 2.6.3). Prove: value at 0/1/[a]/p·x; ≤ 1 globally;
  iSup attained (ρ<1); monotone tail bounds.
- **Sources**: Kedlaya 1410.5160 (2.2.1); AWS Rem 2.6.3.

### [T802] Ultrametric additivity of the Gauss value
- **Status**: done (beastmode 2026-07-26; gaussValue_add_le axiom-clean)
- **Progress**: Route as frozen (1004.0466 Lemma 4.1) but with a formalization
  simplification found during implementation: the pair-case `[a]+[b]` needs NO
  Witt-polynomial homogeneity — over the perfectoid FIELD F one writes
  `[a]+[b] = [a]·(1+[u])`, `u = b/a ∈ O_F` (Integers.exists_of_le_one), and uses the
  new scaling lemma `teichCoeff_teichmuller_mul` (coordinates of `[w]·s` are `w·coords(s)`),
  itself a consequence of expansion uniqueness `teichCoeff_sum_range_add` (CORE-1, via
  le_coeff_eq_iff_le_sub_coeff_eq_zero + sum_coeff_eq_coeff_sum + teichmuller_mul_pow_coeff).
  Kedlaya's (4.1.1)/(4.1.2) multiset induction became `exists_level_rep` (digit-prefix +
  p^n·List.sum invariant) with two list-engines: `exists_list_head_split` (op. 1: head-split
  every member via `exists_head_split`, tails controlled by `mul_gaussValue_le_of_tail`)
  and `exists_fold_teichmuller_heads` (op. 2 iterated: fold Teichmüller heads pairwise,
  re-splitting after each merge). All axiom-clean.
  Kedlaya 1004.0466 Lemma 4.1 (paper in refs). Core input: `[a] ± [b] =
  Σ_j p^j [P_j^±(a,b)^{p^{-j}}]`, P_j^± ∈ 𝔽_p[X,Y] homogeneous of degree p^j ⟹
  |c_j| ≤ max(|a|,|b|); digit-carry induction; ρ^N tail bound; density extends.
- **Statement**: `gaussValue ρ (x+y) ≤ max (gaussValue ρ x) (gaussValue ρ y)`.

### [T803] Multiplicativity (paper Lemma 2.3 / 1004.0466 Lemma 4.1)
- **Status**: done (beastmode 2026-07-26; gaussValue_mul + gaussValue_mul_le + neg/sub/isosceles/positivity all axiom-clean)
  p^i[a]·p^j[b] = p^{i+j}[ab] + T802; equality via least max-attaining indices +
  strictly-smaller discarded parts (sol Q2).
- **Statement**: `gaussValue ρ (x*y) = gaussValue ρ x * gaussValue ρ y`.

### [CLEANUP-11] /cleanup on GaussNorm.lean
- **Status**: done-as-scoped (2026-07-26: lint-clean pass on GaussNorm/GaussPoint — omit-annotations, deprecated-name fixes, unused simp args; deep per-decl golf is fleet /cleanup work on main per AINTLIB architecture, not producer work)

### [T804] The Gauss point: Valuation package, continuity, Spa-membership
- **Status**: done (beastmode 2026-07-26; GaussPoint.lean: gaussVal bundle, v(pseudo-uniformizer)<1 via not_isUnit_toOF, Iinf^n-estimate by Submodule.mul_induction_on, Wedhorn-7.7 continuity via isAdic_Iinf + map_add_left_nhds_zero; all axiom-clean)
- **Statement**: `gaussValuation ρ : Valuation (Ainf p F) ℝ≥0`; `gaussSpv ρ : Spv _`;
  `gaussSpv_isContinuous`; `gaussSpv_mem_spa`.

### [T805] ★ Y_nonempty (closes T601)
- **Status**: done (beastmode 2026-07-26; Curve.lean Y_nonempty := Y_nonempty' — the rho=1/2 Gauss point; AXIOM-CLEAN; closes T601; FarguesFontaine/ is sorry-free; full library green 6141 jobs)
- **Statement**: fill `Y_nonempty` in Curve.lean: `⟨gaussSpv ρ, mem_spa, w(p[ϖ]) ≠ 0⟩`.

### [PLAN-GATE-1] /develop --decompose: Kedlaya §2–§4 (Euclidean/PID + strongly noetherian + B^I)
- **Status**: done (2026-07-26: decomposition-laneB.md written; Lane-B tickets T901–T912 filed; AD-1..AD-7 frozen) | **Depends**: T805
- Scope PER SOL REVIEW: §2–§3 PLUS Definition 4.2, Lemma 4.9, Theorem 4.10 (the
  two-sided interval rings B^{[1,c]} (U₀) and B^{[c,p]} (V₀), normalization
  |ϖ| = p^{-1}); include the Banach-vs-Huber Tate-algebra topological agreement.
- NOT executable by /beastmode: this is a planning action producing lane-B tickets.

### [PLAN-GATE-2] Lane C assembly planning (identification theorem + sheafy instances)
- **Status**: blocked (planning gate) | **Depends**: PLAN-GATE-1 only for the
  sheafiness core (the repo's `isSheafy_of_stronglyNoetherian_828b` is sorry-free);
  presheafValue-identification additionally depends on the PresheafTateStructure
  plumbing. SOL CORRECTIONS (binding): 𝒪(U₀) ≅ B^I is a genuine theorem (dense
  subalgebra + topology comparison, or Lemma 4.9); the rational PLUS ring is the
  integral closure of A⁺[T/s] (NOT of the image of A⁺) and is what gets
  transported — equality with B^{I,+} not required.

### [PLAN-GATE-3] Lane D: 𝒳 as a locally v-ringed quotient (NEW per sol Q6)
- **Status**: blocked (planning gate) | **Depends**: PLAN-GATE-2
- Content: 𝒴 pre-adic structure + chart identifications respecting restrictions
  (Wedhorn Rem 8.27); then EITHER 𝒪_X(W) := 𝒪_Y(q⁻¹W)^{φ^ℤ} descent (with plus
  sheaf and stalk valuations) OR two-chart gluing along the Frobenius transitions
  (overlap pieces: κ = c identity; κ = 1 ↔φ↔ κ = p), cocycle condition, and the
  local-isomorphism property of q — only then is 𝒳 an adic space.

---

## Campaign 8 Lane B (PLAN-GATE-1 output, 2026-07-26): Kedlaya 1410.5160 §2–§4
Architecture decisions AD-1..AD-7 in `.mathlib-quality/decomposition-laneB.md` are BINDING.
File plan: `FarguesFontaine/RobbaLoc.lean` (T901), `FarguesFontaine/WittF.lean` (T902–T903),
`FarguesFontaine/Euclidean.lean` (T904), `FarguesFontaine/Groebner.lean` (T905–T907),
`FarguesFontaine/IntervalRing.lean` (T908–T911), `FarguesFontaine/StronglyNoetherianB.lean` (T912).

### [T901] Bloc + the extended Gauss-valuation family
- **Status**: done (beastmode 2026-07-26; RobbaLoc.lean — Bloc, wLoc via extendToLocalization, mk'/algebraMap/unit-inverse evaluations; axiom-clean) | **File**: FarguesFontaine/RobbaLoc.lean | **Depends**: T803/T804 (done)
- **Statement**: `Bloc p F := Localization.Away ((p : Ainf p F) * teichPi p F ϖ)`;
  `wLoc ρ hρ0 hρ1 : Valuation (Bloc p F ϖ) ℝ≥0 := (gaussVal p F hρ0 hρ1).extendToLocalization hS _`
  with `hS : Submonoid.powers (p·[ϖ]) ≤ (gaussVal).supp.primeCompl` from
  `gaussValue_p_teichPi_ne_zero`; evaluation lemmas `wLoc_mk'` (from
  `Valuation.extendToLocalization_mk'`), `wLoc_coe` (on `Ainf`-images), values on
  `p⁻¹`, `[ϖ]⁻¹`; `wLoc_teichmullerFrac : wLoc ([a]/[ϖ^k]) = |a|/c^k`.
- **Sketch**: pure API assembly; mathlib `extendToLocalization` verified present with
  `extendToLocalization_mk'`. Source: Kedlaya Def 2.2 (ln 85–95) + AD-1/AD-2.

### [T902] W(F) engines + the Hölder coordinate-continuity lemma
- **Status**: done-as-scoped (beastmode 2026-07-26; b1/b1'/b2/b3 all in WittF.lean,
  axiom-clean; b4 + engine ports (a) explicitly moved into T903). DONE so far in WittF.lean (all axiom-clean):
  (b1) `exists_teichmuller_sub_coeff_eq` — diagonal divisibility via W(O_F[T])-naturality
  (evalRingHom x/y through map_coeff + map_teichmuller + Polynomial.dvd_iff_isRoot);
  (b1') `valuation_teichCoeff_teichmuller_sub_pow_le` — the pow-form twist bound
  v(teichCoeff([x]−[y]) k)^(p^k) ≤ v(x−y) (via frobeniusEquiv_symm_pow_pow_cancel,
  now de-privatized in GaussNorm.lean);
  (b2) `gaussValue_teichmuller_sub_le_of_le` — ε-δ continuity of a ↦ [a] with
  δ = ε^(p^K), K from exists_pow_lt_of_lt_one; pow_le_pow_iff_left₀ for root-taking.
  (b3) DONE: `exists_delta_teichCoeff_sub` — per-coordinate ε-δ on Ainf by head-split
  recursion (eq_sub_of_add_eq to avoid rewriting under teichCoeff; δ = min (min (ρδₙ) δT) 1);
  axiom-clean. REMAINING: (b4) clearing denominators to Aloc/Bloc (coords of x/(p[ϖ])^k);
  (a) the W(F) engine ports — DECISION: defer both into T903 where the completion
  context fixes the right statement shapes | **File**: FarguesFontaine/WittF.lean | **Depends**: T901
- **REVISED per AD-3-revision**: two deliverables. (a) Port the GaussNorm engines
  (CORE-1/2, head split, scaling, pair bound via u-trick + `WittVector.map`-naturality
  from `W(O_F)`, level-rep) to `W(F)`-elements with attained-sup statements under
  explicit BddAbove hypotheses (no global ≤1). (b) **Coordinate continuity** (the
  load-bearing new lemma, source Kedlaya 1004.0466 Thm 4.5): quantitative Hölder bound
  on `Ainf` first — if `gaussValue ρ (a−b) ≤ ρⁿ·δ^{p^n}` with `δ ≤ 1` then
  `|teichCoeff a n − teichCoeff b n| ≤ δ` (exact constant shape to be fixed against the
  1004.0466 proof) — then the same on `Bloc` by clearing denominators.
- **Sketch REVISED (route derived 2026-07-26, replaces the 1004.0466-transcription —
  that theorem is Gelfand-spectra continuity, not the coordinate estimate)**:
  (b1) **Diagonal divisibility**: for k ≥ 1, `(teichmuller x − teichmuller y).coeff k`
  is divisible by `x − y` in `O_F`. Proof WITHOUT polynomial computations: work in
  `W((O_F)[X,Y])`; the element `E_k := ([X] − [Y]).coeff k ∈ O_F[X,Y]` vanishes under
  the diagonal evaluation `Y ↦ X` (since `[x]−[x] = 0`), by `WittVector.map`-naturality
  (map (evalHom) commutes with coeff and with teichmuller); hence `(X−Y) ∣ E_k`;
  specialize by `WittVector.map (eval (x,y))`. Corollary (pow form, no rpow):
  `v(teichCoeff ([x]−[y]) k)^(p^k) ≤ v (x−y)` (the twist θ^{-k} takes p^k-th roots;
  the cofactor is in O_F so v ≤ 1). Same for `[x]+[y]` against `[x+y]` if needed.
  (b2) **Teichmüller-difference modulus**: `w_ρ([a]−[b]) ≤ max(v(a−b),
  sup_{k≥1} ρ^k·v(a−b)^{p^{-k}})` — an explicit modulus ω(ε) → 0 (NOT Lipschitz;
  choose the K-balanced bound `ω(ε) = max(ε^{p^{-K}}, ρ^K)`-style to stay in pow-form).
  (b3) **Per-coordinate modulus on Ainf**: digit-0 differences are exact
  (constantCoeff is additive): `v(a₀−b₀) ≤ w(a−b)`; recurse via head-split:
  `a = [a₀]+p·x'`, `b = [b₀]+p·y'`, `w(x'−y') ≤ ρ⁻¹·max(w(a−b), w([a₀]−[b₀]))` (using
  (b2)), and `aₙ₊₁ − bₙ₊₁ = x'ₙ − y'ₙ`. Gives: ∀ n ∃ modulus ωₙ with
  `|teichCoeff a n − teichCoeff b n| ≤ ωₙ(w(a−b))`, `ωₙ(ε) → 0` as `ε → 0` — exactly
  the uniform continuity needed for coordinates on the completion (T903).
  (b4) Extend to `Aloc/Bloc` by clearing `[ϖ]`/`p[ϖ]`-denominators (scaling lemma).

### [T903] Ar as Valued completion; realization; wAr; deg
- **Status**: in_progress (beastmode 2026-07-26). DONE (ArCompletion.lean, axiom-clean):
  wK (Gauss valuation on Frac(Ainf) via nonZeroDivisors-extendToLocalization, using
  gaussValue_pos_of_ne_zero), hatK := (wK).Completion (mathlib field machinery),
  toHatK with valued_toHatK (Valued.v ∘ toHatK = gaussValue, via valuedCompletion_apply),
  Aloc (abbrev, finally defined here), AlocToHatK/BlocToHatK (IsLocalization.lift,
  unit-values via map_pow through the gaussVal bundle), ArSub/BrSub :=
  range.topologicalClosure. REMAINING (exact next steps, in order):
  (1) DONE (`alocToWittF`, `isUnit_map_teichPi`, `alocToWittF_algebraMap`) — was: IsLocalization.lift of
      `WittVector.map (powerBoundedSubring.toSubring F).subtype` ([ϖ]-image is a unit:
      inverse `teichmuller p (ϖ⁻¹ : F)`, via map_teichmuller + teichmuller-mult +
      mul_inv_cancel₀ + teichmuller_one); injectivity (denominators map to nonzerodivisors);
  (2) DONE (`teichCoeffF_map` via `frobeniusEquivF_symm_subtype`/`_pow_subtype`) — was:
      (frobenius commutes with ring homs; symm-version by injectivity), hence
      `teichCoeffAloc := teichCoeffF ∘ alocToWittF` extends teichCoeff with
      [ϖ]-denominator scaling (scaling lemma teichCoeff_teichmuller_mul, F-version);
  (3) DECIDED (2026-07-26): common-denominator shortcuts are DEAD — counterexample
      sₘ = p^m·[ϖ^{-m/2}] is wAloc-small with unbounded denominators when ρ < √c. The
      honest route is the full W(F) value-port with BddAbove-threading:
      `gaussTermF ρ x n := ρⁿ·|teichCoeffF x n|`, `gaussValueF := ⨆` (with explicit
      `BddAbove (Set.range (gaussTermF ρ x))` hypotheses on every lemma — no global ≤1),
      ports of: term_le_value, add_le (level-rep machinery re-run over F: list engines
      port verbatim, pair bound via u-trick over F using Integers.exists_of_le_one on
      b/a), p_mul, sub_le (needs mul_le for neg — port submult too OR use -1 = [-1]…
      CAREFUL: over F use -x = (-1)·x and w((-1)x) via... port gaussValue_neg's argument
      needs submult; alternatively prove neg-invariance coordinatewise: teichCoeffF(-x) n
      = -teichCoeffF(x) n?? FALSE in general for p=2? no: -1 = [u]-Teichmüller in char p:
      (-1)^p = -1 so -1 = [-1] in W(F) for ALL p (p=2: -1=1 ✓ consistent): -x = [-1]·x:
      coords scale by -1 via teichCoeffF_teichmuller_mul-port: |coords| UNCHANGED ⟹
      w(-x) = w(x) COORDINATEWISE, no submult needed!! — ALSO backport this trick to
      simplify GaussNorm's gaussValue_neg in a later cleanup), boundedness-propagation
      through head-splits (tail-coords are shifted coords), then the (b3)-recursion
      verbatim. Deliverable: `exists_delta_teichCoeffF_sub` for W(F)-pairs with
      BddAbove-hyps — applied to Aloc-images (which are bounded: their w-values are
      wAloc-values via the embedding, bounded on Cauchy sequences).
STEP (3) COMPLETE (2026-07-26, all axiom-clean in WittF.lean):
      `exists_delta_teichCoeffF_sub` — per-coordinate ε-δ over W(F) on value-bounded
      boundedly-termed sets (m-generalized induction; heads via the scaled Teichmüller
      continuity `gaussValueF_teichmuller_sub_le_of_le_scaled`; tails via p-shift +
      m→m+K rescaling with c^K < ρ). Supporting F-layer all green: gaussTermF/ValueF,
      scaling, head split, pair bound, list engines + level rep + `gaussValueF_add_le`,
      `gaussValueF_p_mul`, transport (`gaussValueF_map`), boundedness lemmas for
      tails/sums/Teichmüller-differences. The [-1]-question was DODGED entirely: the
      only negation needed was digit-0 (additive, exact).
      (4) COMPLETE (2026-07-26): (4a) done, (4b) done (`gaussValueF_alocToWittF` attainment
      equality), (4c-i) done (`valued_AlocToHatK` bridge + `teichCoeffAr :=
      limUnder(comap AlocToHatK (𝓝 x)) coords` definition). (4c-ii) PARTIAL: `ball_mem_nhds_zero` +
      `exists_ball_subset_nhds` DONE (valuation balls are a neighborhood basis of 0 in
      F — ϖ^m·O_F-scaling one way, boundedness of O_F + top-nilpotent scaling the other;
      note `haveI := IsPerfectoidRing.uniform (p := p) (A := F)` needed for
      IsUniform.isBounded_powerBounded). NeBot done (`neBot_comap_of_mem_ArSub`,
      topologicalClosure-carrier is closure by rfl). BLOCKER FOUND for the ball/Cauchy
      steps: mathlib's Valued-lemmas (`Valued.mem_nhds`, `hasBasis_uniformity`) are
      stated via `v.restrict` into `(MonoidWithZeroHom.ValueGroup₀ (.ofClass v))ˣ`, NOT
      raw NNReal comparisons — the translation layer is
      `Valuation.restrict_lt_iff_lt_embedding` / `embedding_strictMono` /
      `restrict₀_apply` (see Mathlib/Topology/Algebra/Valued/ValuedField.lean ~520-566
      for worked patterns). RESOLVED (2026-07-26):
      `eventually_pair_wAloc_le` GREEN — approximant pairs of any x are eventually
      wAloc-close: cauchy_nhds.2 into hasBasis_uniformity's γ-ball with γ :=
      Units.mk0 (v.restrict z₀) for z₀ := toHatK(p^N), ρ^N < ε; the pair condition
      transfers via Valuation.restrict_lt_iff (SAME-valuation comparisons only — no
      value-group computation); prod_comap_comap_eq aligns the filters;
      valued_AlocToHatK converts to wAloc. tendsto_teichCoeffAr GREEN (the step-4 capstone: coordinates of A^r-elements
      converge along approximants; two-topology diamonds bridged by
      IsPerfectoidRing.topologyEq rewrites both at the W-neighborhood and at the
      completeness output). STEP-5 ROUTE REVISION (2026-07-26, after Lemma A `gaussTerm_teichCoeffAr_le` went
      green): the (≥)-direction CANNOT go through approximant-attainment transfer —
      attaining indices are NOT uniformly bounded over the filter (the p^m[ϖ^{-m/2}]
      denominator demon again), and per-index limits control only finitely many terms.
      CORRECT ORDER: (5b-i) DONE (alocTeich + alocToWittF_alocTeich + wAloc_alocTeich +
      exists_finite_teichmuller_sum_close, all axiom-clean; the h2gen-pattern:
      generalize auxiliary inductions over a FRESH variable, never over an index the
      context mentions). Was: **finite-Teichmüller-sum density**: the subring of finite
      sums Σ_{n<N} pⁿ·[cₙ] (cₙ ∈ F) is dense in Aloc for every wAloc (CORE-2 on the
      Ainf-numerator + [ϖ]^{-k}-scaling — tails of prefixes are ρᴺ-small), hence its
      image is dense in ArSub; define `alocTeich : F → Aloc` (choice: Tate absorption
      → O_F-numerator/[ϖ]^k) with `alocToWittF (alocTeich c) = teichmuller p c` and
      `wAloc (alocTeich c) = |c|`. (5b-ii/iii) ROUTE SUPERSEDED (2026-07-26 second revision): direct reconstruction
      hits the coordinate-decay knot — Hölder moduli degrade in n, so no finite-δ
      controls infinitely many coordinates, and digit-nonadditivity blocks transfer
      through differences. THE C₀-ARCHITECTURE instead (classical, no perturbation
      analysis): (A) SeqSpace := {b : ℕ → F // Tendsto (fun n => ρⁿ·|bₙ|) atTop (𝓝 0)};
      (B) Φ b := limit in hatK of images of prefixes Σ_{n<N} pⁿ·alocTeich(bₙ)
      (Cauchy: consecutive differences have value ρᴺ|b_N| → 0; Valued-completeness of
      hatK); (C) ISOMETRY: Valued.v (Φ b) = ⨆ n, ρⁿ|bₙ| — prefix values are exact
      finite maxima (wAloc of finite sums = max of terms: compute via
      gaussValueF_alocToWittF + F-CORE-1 coords of finite sums + attained finite sup),
      pass to the limit by isosceles; (D) Φ-image is complete (isometric image of the
      complete SeqSpace — prove SeqSpace-Cauchy ⟹ coordinatewise-Cauchy + uniform
      tail control, c₀-style) hence closed, contains the Aloc-image densely
      (exists_finite_teichmuller_sum_close!) ⟹ image = ArSub; (E) uniqueness of the
      preimage sequence + consistency with tendsto_teichCoeffAr gives teichCoeffAr-
      decay, reconstruction, AND the realization equality (with Lemma A already green)
      all at once. IMPLEMENT (B)+(C) for FIXED b first (no SeqSpace-topology needed:
      state Φ as a def + its value; completeness of SeqSpace can be replaced by:
      every ArSub-element is hit — prove surjectivity directly: given x, the
      coordAr-sequence… NO that needs decay again. Honest order: SeqSpace-completeness
      IS needed; alternatively dodge once more: ArSub ⊆ Φ-image ⟸ Φ-image closed ∧
      ⊇ dense subset; closedness ⟸ completeness of SeqSpace + isometry. So: (A)(B)(C),
      then SeqSpace-complete, then (D)(E).) THEN attainment
      (wAr x = sup ρⁿ|teichCoeffAr x n|, attained — via the eventual bounds +
      coordinate limits + gaussValueF_alocToWittF), then deg/deg_mul/Rem-2.7/summability,
      unlocking T904 (Euclidean division). Historical assembly notes:
      (i) eventual value-bound B via one small set from eventually_pair_wAloc_le at
      ε := 1 + a base point u₀ (NeBot), B := max (wAloc u₀) 1... wAloc u ≤
      max(wAloc(u−u₀), wAloc u₀)-ultrametric; pick M with (c⁻¹)^M ≥ B;
      (ii) Cauchy (map coords L): for V ∈ 𝓝(0:F)-entourage-side use
      uniformity_eq_comap_nhds_zero F + exists_ball_subset_nhds → c^m-ball;
      exists_delta_teichCoeffF_sub p F ϖ n hρ0 hρ1 M (ε := min (c^m) 1) → δ;
      eventually_pair_wAloc_le at δ + hyps (bddAbove via bddAbove_gaussTermF_alocToWittF,
      differences boundedly-termed since u−u' ∈ Aloc, values via gaussValueF_alocToWittF
      + (i)) give coord-pairs in the ball ⊆ V;
      (iii) CompleteSpace F (haveI := IsPerfectoidRing.complete p F) → limit;
      Tendsto.limUnder_eq needs T2 F (haveI t0 + IsTopologicalAddGroup.t2Space-chain);
      unfold teichCoeffAr. OLD notes (superseded):
      `valued_ball_mem_nhds : {z : hatK | Valued.v (z − x) < (δ : NNReal)} ∈ 𝓝 x` for
      δ ≠ 0 (via mem_nhds + the embedding-strictMono translation, choosing γ :=
      the image of δ under the valueGroup₀-equiv — OR dodge entirely: prove the
      Cauchy-condition using `Valued.hasBasis_uniformity`'s γ-balls directly and
      TRANSLATE only the pair-condition v.restrict(f u' − f u) < γ into
      wAloc(u'−u)-smallness via restrict-monotonicity: since only ≤-COMPARISONS between
      values of the SAME valuation are needed, the strictMono embedding transfers them
      without computing γ). Then: eventual value-bound from ONE small-set (Cauchy ⟹
      ∃ S ∈ L small: all u,u' ∈ S have wAloc(u−u') ≤ 1, fix u₀ ∈ S: wAloc u ≤
      max(wAloc u₀, 1) =: B, pick M with (c⁻¹)^M ≥ B — NO x-ball needed!), then
      exists_delta_teichCoeffF_sub-application, F-complete limit, Tendsto.limUnder_eq
      (T2 F from t0 + group instances). The Tendsto-characterization for x ∈ ArSub — NeBot from closure-membership
      (mem_closure_iff_nhds_neBot + comap-transfer), Cauchy of the pushed filter via
      exists_delta_teichCoeffF_sub (hyps: approximant-terms bounded (4a), differences
      are Aloc-images with wAloc = Valued.v-difference by the bridge, value-bounds
      (c⁻¹)^m ≥ max(v x, 1) by ultrametric ball-constancy near x), F complete
      (IsPerfectoidRing.complete), Tendsto.limUnder_eq. `wAloc` defined (mirror);
      `gaussTermF_alocToWittF_le` DONE (dense-layer term bound: every Aloc-image is
      boundedly termed with terms ≤ wAloc-value; via IsLocalization.surj +
      teichmuller-scaling + c^k-cancellation; note the teichPi-rw-in-type trap: use
      compound-pattern haves (hteich) since teichPi occurs in Aloc's TYPE index).
      NEXT within (4): (4b) attainment equality `gaussValueF (alocToWittF u) = wAloc u`
      (≥ via exists_gaussValue_eq_gaussTerm on the numerator, scaled); (4c) coordinate
      filters: for x ∈ ArSub define teichCoeffAr x n := lim of coords along
      comap AlocToHatK (𝓝 x) (NeBot from closure-membership; Cauchy via
      exists_delta_teichCoeffF_sub applied to differences of approximants — approximants
      are boundedly-termed (4a) with values eventually ≤ v(x)+ball-const, i.e. pick m
      with (c⁻¹)^m ≥ that; differences are Aloc-images hence boundedly termed);
      F complete (IsPerfectoidRing.complete) gives the limit; characterize by
      `Tendsto`. (4d) also relate Valued.v x to the coordinate data (attainment on the
      completion) — that is step (5).
      (5) reconstruction + attainment (wAr x = max ρⁿ|xₙ|, attained) on ArSub; then
      deg := largest attaining index, deg_mul (T803-mirror), Rem-2.7, summability —
      unlocking T904 (Euclidean). Br-vs-Ar[1/p] deferred until needed | **File**: FarguesFontaine/WittF.lean | **Depends**: T902
- **REVISED per AD-3-revision**: `Aloc := Localization.Away (teichPi p F ϖ)`; wAloc :=
  extendToLocalization of gaussVal (mirror of T901 for the ϖ-only localization);
  `Ar ρ := UniformSpace.Completion (WithVal (wAloc ρ))` with mathlib `Valued`-instance
  and `Valued.extension`; **realization theorems**: extended coordinates
  `teichCoeffAr : Ar → F` (n-indexed ℤ after p-clearing — for Ar the index is ℕ on the
  Aloc-side times [ϖ]-denominators; precise indexing fixed in implementation) via T902(b)
  + Completion.denseInducing; reconstruction + attainment `wAr x = max ρⁿ|xₙ|`;
  `deg x := largest attaining index` for x ≠ 0; `deg_mul` (T803-mirror on the
  realization), `deg_eq_of_lt` (Rem 2.7); summability of `Σ zₗ` with `wAr zₗ → 0`
  (completion: Cauchy prefix sums — now FREE).
- **Source quotes**: Def 2.4 ln 100–106; Def 2.5 ln 115–118; Rem 2.7 ln 137–139.

### [T904] Euclidean division on Ar; Ar is a PID
- **Status**: open | **File**: FarguesFontaine/Euclidean.lean | **Depends**: T903
- **Statement**: Lemma 2.8 (approximate division): for x ≠ 0 ∃ ε ∈ (0,1) s.t. ∀ y ∃ z w:
  `y = z*x + w ∧ wAr w ≤ wAr y ∧ (wAr w > ε·wAr y → deg w < deg x)`. Prop 2.9 (exact):
  `∀ x ≠ 0, ∀ y, ∃ z w, y = z*x + w ∧ wAr w ≤ wAr y ∧ deg w < deg x`. Cor 2.10:
  `EuclideanDomain (Ar ρ)` (deg into ℕ; mul_left_not_lt from deg_mul) + PID instance.
- **Sketch** (transcribe ln 141–216 faithfully): ε with `ρ ≤ ε` and
  `wCoeff x n ≤ ε·wAr x` for n > m := deg x. Iteration: `zₗ := Σ pⁿ[y_{l,n+m}/x_m]`
  (coefficientwise quotient by the leading coefficient — legal in F), `y_{l+1} = yₗ − zₗx`;
  the (2.8.2) T-polynomial bookkeeping bounds the ε-support top index Nₗ strictly down —
  well-founded. Prop 2.9: geometric iteration of 2.8, `wAr zₗ ≤ ε^l·wAr y/wAr x → 0`,
  summability from T903. EuclideanDomain: mathlib structure on the subtype.

### [T905] Gröbner data on Ar⟨X₁..Xₖ⟩
- **Status**: open | **File**: FarguesFontaine/Groebner.lean | **Depends**: T903; repo A⟨X⟩
- **Statement**: for the repo's `RestrictedPowerSeries` over `Ar` (Gauss norm, radius 1
  per AD-5): leading index (graded-lex-maximal norm-attaining multi-index, Def 3.6
  ln 267–270 — attainment from coefficient decay), leading coefficient; `d_I`-function
  and the finite Gröbner set S (Def 3.7 ln 273–283; Dickson: `(Fin k →₀ ℕ, ≤)` is a WQO —
  use mathlib `MonomialOrder`/`Finsupp` WQO machinery, else prove Dickson by induction);
  monotonicity `I₁ ≤ I₂ → d_{I₂} ≤ d_{I₁}` (multiply by the monomial `T^{I₂−I₁}`,
  norm-multiplicativity of monomial scaling).
- **Quote** (ln 273–283): "the set of I for which d_I < +∞ contains only finitely many
  minimal elements ... For each I ∈ S, choose x_I ∈ H∖{0} with leading index I and
  leading coefficient of degree d_I."

### [T906] Lemma 3.8: approximate ideal generation
- **Status**: open | **File**: FarguesFontaine/Groebner.lean | **Depends**: T904, T905
- **Statement**: ∃ ε ∈ (0,1): ∀ y ∈ H ∃ (a_I)_{I∈S}: `|a_I|·|x_I| ≤ |y|` and
  `|y − Σ a_I x_I| ≤ ε|y|`.
- **Sketch** (transcribe ln 285–320): ε := max over I ∈ S, J ≻ I of |x_{I,J}T^J|/|c_I T^I|
  (or any ε if that set is empty). Iteration: leading index Jₗ of yₗ, pick Iₗ ∈ S with
  Iₗ ≤ Jₗ, d_{Iₗ} = d_{Jₗ}; divide leading coefficients by Prop 2.9; the ε-support
  argument (El sets, J₊ bound, the largest infinitely-recurring index J, Rem-2.7 finish)
  gives the contradiction. Strictly-decreasing/finitely-bounded ≺-data: well-founded.

### [T907] Lemma 3.9 + Theorem 3.2: Ar is strongly noetherian
- **Status**: open | **File**: FarguesFontaine/Groebner.lean | **Depends**: T906
- **Statement**: every ideal H of `Ar⟨X₁..Xₖ⟩` is generated by the finite set
  {x_I : I ∈ S}; hence `IsStronglyNoetherian (Ar ρ)` (repo predicate; radius-1 per AD-5).
- **Sketch** (ln 322–330): geometric iteration of T906, `|yₗ| ≤ ε^l|y|`, sums converge
  (Tate-algebra completeness — repo RestrictedPowerSeries API), `y = Σ_I a_I x_I`.

### [T908] λ_I, BI, three circles, coordinate continuity
- **Status**: open | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T901; T902
- **Statement**: for `I = [ρ₁,ρ₂] ⊂ (0,1)` (endpoints in c^ℚ per AD-4):
  `wI := fun x => max (wLoc ρ₁ x) (wLoc ρ₂ x)` (power-multiplicative ring norm);
  `BI := UniformSpace.Completion (Bloc, wI-uniformity)` as a NormedRing (AD-7);
  three-circles (Lemma 4.4 ln 344–352: reduce to single terms `pⁿ[xₙ]` where equality;
  in ρ-form: `wLoc ρ^θ... ≤ wLoc ρ₁ ^θ · wLoc ρ₂ ^{1−θ}` for the geometric interpolation)
  ⟹ `wI = sup {wLoc ρ, ρ ∈ I}` (Cor 4.5); coordinate-continuity on wI-balls
  (Hölder: source Kedlaya 1004.0466 Thm 4.5, transcribe) ⟹ extended coefficient
  functionals `teichCoeffI : BI → F` and the series realization of BI-elements
  (two-sided decay description).
- **NOTE**: this is the hardest *infrastructure* ticket; sequence AFTER T907 unless
  parallel capacity exists.

### [T909] Restriction maps BI → BI'
- **Status**: open | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T908
- **Statement**: for I' ⊆ I: continuous ring hom `res : BI → BI'` (Completion-functorial
  from `wI' ≤ wI` on Bloc via Cor 4.5), injective (Cor 4.6 ln 361–368: λ_t = 0 on I'
  propagates by three-circles + continuity).

### [T910] Lemma 4.9, first two presentations
- **Status**: open | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T907, T908
- **Statement** (untwisted form; z := ϖF^{a/b}-powers, radii in c^ℚ, rescale per AD-5):
  `BI⟨T⟩/(T − [z]·unit-rescaled) ≅ B^{I∩[...]}` and the `[z⁻¹]`-variant — the exact
  endpoint arithmetic per Kedlaya ln 380–392, transported through ρ = p^{-1/t}.
  Strictness, closed ideal, injectivity, surjectivity with (4.9.1)-norm control, and the
  ρ ∈ p^ℚ (here c^ℚ) plus-ring statement (integral closures of images).
- **Sketch**: transcribe ln 394–460 (the four-paragraph proof) with the T908 coefficient
  realization; the geometric-series unit case for empty intersections (ln 396–399).

### [T911] Lemma 4.9, third presentation (Ar → BI bridge)
- **Status**: open | **File**: FarguesFontaine/IntervalRing.lean | **Depends**: T907, T908
- **Statement**: `Ar⟨T⟩/(p·T − [zⁿ]) ≅ B^{I'''}` (ln 384–386: I''' = [−n⁻¹log_c p, r]
  in t-coordinates; transport to ρ) — THE bridge that makes BI-algebras quotients of
  Ar-Tate algebras.

### [T912] Theorem 4.10: BI is strongly noetherian
- **Status**: open | **File**: FarguesFontaine/StronglyNoetherianB.lean | **Depends**: T907, T910, T911
- **Statement**: `IsStronglyNoetherian (BI)` for every c^ℚ-endpoint closed
  `I ⊂ (0,1)` — in particular for the two FF window intervals (U₀ and V₀ charts).
- **Sketch** (ln 462–470): `BI⟨X₁..Xₖ⟩` is, by T911 + T910 applied with extra Tate
  variables carried along, a quotient of `Ar⟨T, X₁..Xₖ⟩` (noetherian by T907); quotients
  of noetherian rings are noetherian. Endpoint bookkeeping per Rem 4.11 uses the AD-5
  rescalings.

### [PLAN-GATE-1] — CLOSED 2026-07-26 by this decomposition (see decomposition-laneB.md).
