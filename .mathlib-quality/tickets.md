# Ticket Board — ROIE (`A⁺ ⊆ A°` ring-of-integral-elements interface, full option (a))

## Summary
- Total: 4 proof tickets + 2 cleanup = 6
- Open: 6 | In Progress: 0 | Done: 0 (foundation 489fe72 already committed: `IsRingOfIntegralElements`
  class, `support_eq_maximal_of_le`, `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` named leaf)
- WIP for T-ROIE-1 is in `git stash@{0}` (Presheaf + Cor832 IntCl migration, builds through Cor832).
- Plan: `.mathlib-quality/plan-roie.md`. Refines TaskList #68; supersedes its B2.

---

### [T-ROIE-1] Restore + verify the IntCl plus-ring migration core
- **Status**: DONE (2026-06-18) — WIP restored; IntCl `completedPlusSubring` migration builds.
- **File**: Presheaf.lean, Cor832.lean
- **Depends on**: none
- **Parallel**: no (foundation of the cascade)
- **Type**: refactor (restore stashed WIP)

#### Statement
Restore `git stash@{0}` (the verified WIP) and confirm Presheaf + Cor832 build:
- `Presheaf.lean`: `RationalLocData.completedPlusSubring D := ((integralClosure ↥(D.locPlusSubring)
  (Localization.Away D.s)).toSubring.map D.coeRingHom).topologicalClosure`; the helper
  `locPlusSubring_le_integralClosure`; the membership lemma re-proof; `import AffinoidRings`; the
  instance `presheafValuePlus_isRingOfIntegralElements : IsRingOfIntegralElements ((presheafValue D)⁺)`
  (3 fields `sorry`, discharged in T-ROIE-3); dropped `completedPlusSubring_le_completedLocSubring`.
- `Cor832.lean`: `exists_spa_point_supp_ge_in_presheafValue` faithful re-proof (via the named leaf +
  the instance); dropped unused `isUnit_canonicalMap_s_via_nullstellensatz`.

#### Proof sketch
1. `git stash pop` (or re-apply the diff). 2. `lake build «Adic spaces».Cor832` — verified to pass
   in the planning run (the full build reached SpaPresheafValueEquivalence, i.e. *past* Cor832, with
   0 errors there). 3. If `git stash` was discarded, re-do the edits per `plan-roie.md`.

#### Mathlib lemmas needed
`integralClosure`, `Subalgebra.toSubring`, `Subalgebra.algebraMap_mem`, `Subring.topologicalClosure`,
`Subring.le_topologicalClosure` (all verified at planning time).

#### Sources
Wedhorn 8.16 (`Ĉ = 𝒪_X⁺(U)`), Def. 7.14(1); REVIEW_BRIEF.md Q1/Q2.

#### Generality decision
`(D : RationalLocData A) [PlusSubring A]` + the project's standard `A`-bundle; index the instance by
`(presheafValue D)⁺` (`ringPlus` key) to match consumer queries.

---

### [T-ROIE-2] Cascade re-route: OLD `A⁺⊆A₀` machinery → faithful `A⁺⊆A°`
- **Status**: DONE (2026-06-18) — foundation + pair→pair-free migration + 8-file cascade landed; full `lake build` GREEN (3190 jobs, 0 errors). Residual = T-ROIE-3/4 honest leaves (warnings).

#### Progress
- 2026-06-18: SpaPresheafValueEquivalence:525 casualty FIXED (helper `vle_image_le_one_of_isIntegral_of_subring`
  via `IsIntegral.map_of_comp_eq` + `Valuation.Integers.mem_of_integral`; `erw` for the field-instance
  diamond). Builds green.
- 2026-06-18: REFINED the WCA half. The `completedPlusSubring_le_ringOfDef` (false) is NOT a 5-leaf
  re-route — it produces `hplusB = B⁺⊆B₀` feeding the acyclicity engine's `hplus` param, which threads
  `wedhorn_lemma_834_part_i_laurent_acyclic → laurentProdCoverOf_isOXAcyclic → unitCover_isOXAcyclic →
  cor_8_32_productRestrictionSub_injective → cor_8_32_productRestriction_faithfullyFlat →
  cor_8_32_maximal_liftedIdeal_ne_top → exists_spa_point_supp_ge_in_presheafValue`. The WIP already made
  the BOTTOM faithful (uses the `IsRingOfIntegralElements` instance + 7.45 leaf). So `hplus` is VESTIGIAL
  engine-wide. De-threaded it from the whole WCA acyclicity engine + Cor832 bottom + RPK Cor-8.32 chain
  + SpaPresheafValueEquivalence:525 (IntCl casualty fixed via `vle_image_le_one_of_isIntegral_of_subring`).
- 2026-06-18 **SCOPE DISCOVERY — the de-thread does NOT terminate inside WCA.** The B-level recursion of
  Lemma 8.34 (`genRestrictedCover_isOXAcyclic_of_spanTop`/`imageCover_isOXAcyclic` instantiate
  `wedhorn_lemma_834`/`every_rational_cover_is_OXAcyclic_whole_space` at `B = presheafValue`) bottoms at
  **`spanTop_iff_noCommonZero_spa` (StandardCover.lean) → `exists_spa_point_with_supp_ge_of_prime`**, which
  is pair-based (`(P : PairOfDefinition A) (hAplus : A⁺⊆P.A₀)`, via Lemma 7.45). At B-level `hAplus = B⁺⊆B₀`
  is FALSE. To de-thread it requires the pair-free form `[IsRingOfIntegralElements (A⁺)]` (the Def-7.14
  affinoid axiom) — but there is **NO base-level instance** of `IsRingOfIntegralElements (A⁺)` (the bare
  `PlusSubring`/`CompatiblePlusSubring` classes lack the `A⁺⊆A°`+integrally-closed+open fields). So the
  faithful fix is the **reviewer's foundational interface change** (give the affinoid axiom so the instance
  resolves) + a **pair→pair-free migration of `spanTop_iff_noCommonZero_spa` across its 8 caller files**
  (WedhornStandardCoverRefinement, TateAcyclicityResiduals, WedhornStage2SpanExtractor, GeometricReduction,
  LocalBasis, WedhornCechAcyclicity, WedhornOutsideRescue, StandardCover). This is the documented
  multi-session **P1 marathon** (#58-#61), NOT a bounded ticket. The WCA-engine de-thread (~90% done,
  faithful) is preserved in `git stash` (with the IntCl WIP). Build restored to green 489fe72. NEEDS
  re-plan foundation-first + a user decision on the foundational interface vehicle.
- 2026-06-18 **RESUMED + LANDED (user: "do full"/"why arent you working").** Foundation chosen:
  extended `CompatiblePlusSubring` (Presheaf.lean) with the 3 Def-7.14 fields (`isOpen'`,
  `isIntegrallyClosed'`, `subset_powerBounded'`) + derived `instance
  CompatiblePlusSubring.toIsRingOfIntegralElements : IsRingOfIntegralElements (A⁺)` (sorry-free; it has
  NO instances, only hypothesis-sites, so strengthening it is the faithful affinoid axiom). Made
  `exists_spa_point_with_supp_ge_of_prime` + `spanTop_iff_noCommonZero_spa` (StandardCover) pair-free
  (drop `(P, hAplus)`, add `[IsHuberRing][T2Space][NonarchimedeanRing][IsRingOfIntegralElements (A⁺)]`,
  use `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` + instance). Cascaded the (P,hAplus)→instance
  swap through ALL 8 caller files (StandardCover, TateAcyclicityResiduals, WedhornStage2SpanExtractor,
  GeometricReduction, WedhornCechAcyclicity) + the WCA P₀-chain + whole_space + imageCover (B-level
  instances resolve from `presheafValuePlus_isRingOfIntegralElements` + the faithful `presheafValue_*`).
  Deleted false `completedPlusSubring_le_ringOfDef`. **GREEN: Presheaf, Cor832, RPK,
  SpaPresheafValueEquivalence, StandardCover, TateAcyclicityResiduals, WedhornStage2SpanExtractor,
  GeometricReduction, WedhornCechAcyclicity all build with 0 errors.** Residual = T-ROIE-3 (presheafValue
  instance 3 sorry fields) + T-ROIE-4 (prime leaf sorry) — both honest named leaves (warnings, not
  errors). Running full `lake build` to confirm downstream (headline). Vestigial (P,hAplus)/hplusA params
  left as unused-warnings (cleanup later).
- **File**: SpaPresheafValueEquivalence.lean, WedhornCechAcyclicity.lean, + any downstream
- **Depends on**: T-ROIE-1
- **Parallel**: no
- **Type**: refactor (re-route, iterate to green)

#### Statement
Re-route every consumer that relied on `(presheafValue D)⁺ = closure(locPlusSubring image)` or on the
two deleted `B⁺⊆B₀` lemmas, to the faithful route (the `IsRingOfIntegralElements` instance +
`exists_cont_supp_ge_powerBounded_of_nonOpen_prime` + the pair-free criteria). Known casualties:
- `SpaPresheafValueEquivalence.lean:525` (`spa_completion_of_spa_localization`): show
  `(presheafValue D)⁺ = closure(IntCl image) ⊆ (Valued.v.integer).comap φhat` by `topologicalClosure_minimal`
  on the **IntCl** image; for `c ∈ IntCl(locPlusSubring)`, `φhat (coeRingHom c)` is integral over
  `φhat (coeRingHom (locPlusSubring))) ⊆ integer`, and the valuation integer is integrally closed
  (`Valuation.Integers.mem_of_integral`), so it lands in the integer.
- `WedhornCechAcyclicity.lean`: `completedPlusSubring_le_ringOfDef` is now FALSE (IntCl ⊄ ringOfDef) →
  DROP it; re-route its 5 users (10958, 11078, 11220, 12417, 12524) to the faithful route (the
  pair-free `isUnit_iff_forall_not_vle_zero_of_complete_pairFree` / `exists_spa_point_supp_ge_in_presheafValue`
  + the instance's `subset_powerBounded`), exactly as `canonical_unit_of_pointwise_lower_bound` was
  re-routed in the WIP.
- **Downstream discovery**: the planning build halted at the first error (SpaPresheafValueEquivalence),
  so WCA + the chain + headline were not fully re-checked. Run `lean_diagnostic_messages` on each
  affected file after its deps build; iterate until `lake build` is fully GREEN (the deep sorries from
  T-ROIE-3/T-ROIE-4 remain as warnings).

#### Proof sketch
Each casualty has the same shape: it used `B⁺ ⊆ B₀` (a ring of definition) to feed pair-based
machinery; with IntCl that inclusion is false, but `B⁺ ⊆ B°` holds (the instance) and the faithful
pair-free criteria consume exactly `B⁺ ⊆ B°`. So: replace `B⁺ ⊆ B₀` + pair-based-criterion with
the pair-free criterion (+ `IsRingOfIntegralElements.subset_powerBounded` where a `B° `bound is
needed). For the integral-closure step (SpaPresheafValueEquivalence), use that valuation integers
are integrally closed.

#### Mathlib lemmas needed
`Subring.topologicalClosure_minimal`, `Valuation.Integers.mem_of_integral` (valuation integer
integrally closed), `IsIntegral.map`/`RingHom.IsIntegralElem.map` (integral transfer through
`coeRingHom`, `φhat`), `IsRingOfIntegralElements.subset_powerBounded`.

#### Sources
Wedhorn 8.16, Def. 7.14(1); the valuation-integer-integrally-closed fact ([BGR] 6.1.2 / standard).

#### Generality decision
No new hypotheses — the re-routes DROP `A⁺⊆A₀`/noeth-`A₀` arguments (rename to `_h…` where a
signature must keep them for callers).

---

### [CLEANUP-1] Run /cleanup on Presheaf.lean + Cor832.lean
- **Status**: open
- **Depends on**: T-ROIE-2
- **Parallel**: no
- **Type**: cleanup
- **Description**: cadence (3 proof tickets across these files since the foundation). Run /cleanup on
  the migrated declarations.

---

### [T-ROIE-3] Discharge `IsRingOfIntegralElements ((presheafValue D)⁺)` (3 fields)
- **Status**: open — PARKED at external leaf (2026-06-18). The instance EXISTS + RESOLVES (build green);
  its 3 fields are cited sorries. `isOpen`/`isIntegrallyClosed` bottom at **Wedhorn 7.47(4) = [Hu1]
  2.4.3** (completion preserves rings of integral elements — EXTERNAL, Wedhorn cites without reproof;
  building it = the CLAUDE.md "substantial missing infrastructure" STOP tell). `subset_powerBounded`
  (Ĉ ⊆ B°) is provable via 7.19/7.20 + completion power-bounded transfer (a real sub-development).
  Faithful as a cited named-leaf per CLAUDE.md.
- **File**: Presheaf.lean (or a new `PresheafAffinoid.lean` if imports demand)
- **Depends on**: T-ROIE-1
- **Parallel**: yes (with T-ROIE-2, T-ROIE-4 — discharges sorries; doesn't affect build greenness)
- **Type**: theorem (3 instance fields)

#### Statement
Replace the three `sorry` fields of `presheafValuePlus_isRingOfIntegralElements`
(`(presheafValue D)⁺ = Ĉ = closure((A⁺⟨T/s⟩)^int)`):
```lean
  isOpen : IsOpen ((presheafValue D)⁺ : Set (presheafValue D))
  isIntegrallyClosed : ∀ a, IsIntegral ↥((presheafValue D)⁺) a → a ∈ (presheafValue D)⁺
  subset_powerBounded : ((presheafValue D)⁺ : Set _) ⊆ TopologicalRing.powerBoundedSubring (presheafValue D)
```

#### Proof sketch (Wedhorn 7.19 + 7.20 + 7.47(4))
1. **Precompletion (Wedhorn 7.19/7.20):** `C := (A⁺[T/s])^int = IntCl(locPlusSubring)` is a ring of
   integral elements of `A_s = Localization.Away D.s`: open (A⁺ open ⟹ A⁺[T/s] open ⟹ ^int open);
   integrally closed (integral closure is idempotent — `integralClosure_idem`); `⊆ (A_s)°` (Lemma 7.20:
   `(A°)⟨T/s⟩ ⊆ (A_s)°`, and `C ⊆ (A°)⟨T/s⟩`).
2. **Completion (Wedhorn 7.47(4) = [Hu1] 2.4.3):** `Ĉ = closure(coeRingHom C)` is a ring of integral
   elements of the completion `presheafValue D`. This is the EXTERNAL cite — state it as a named leaf
   `ringOfIntegralElements_completion` (Wedhorn 7.47(4)/[Hu1] 2.4.3) with a `sorry`, source-justified;
   it discharges all three fields at once (the lift preserves open + integrally-closed + ⊆°).
3. Each field then = the corresponding projection of the 7.47(4) leaf applied to the 7.19/7.20 input.

#### Mathlib lemmas needed
`integralClosure_idem` (integral closure integrally closed), `IsOpen` of subring-images,
`TopologicalRing.powerBoundedSubring`; the 7.20 inclusion is provable (power-bounded localisation).

#### Sources
Wedhorn Prop. 7.19 (p.61), Lemma 7.20 (p.61), Lemma 7.47(4) = [Hu1] 2.4.3 (p.68). `isIntegrallyClosed`
+ `isOpen` bottom at the [Hu1] 2.4.3 completion-lift (EXTERNAL, acceptable parking — like [Hu2] 3.3).

#### Generality decision
`(D : RationalLocData A) [PlusSubring A]` + standard bundle. The 7.47(4) leaf stated generally
("`B` ring of integral elements of `A` ⟹ `B̂` ring of integral elements of `Â`") for reuse.

---

### [T-ROIE-4] Discharge `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` (Wedhorn 7.45+7.42+7.41)
- **Status**: open — PARKED at deep leaf (2026-06-18). Faithful named leaf in place (cited sorry,
  Presheaf:2785). Bottoms at the **height-one vertical generalization** (Remark 4.12) connecting the
  repo's `restrictToConvex` analytic point (bounded on A₀) to a height-1 point bounded on **A°** (Prop
  7.41). The A₀→A° height-one step is deep repo infrastructure (not the optimistic "~6 lines" — that was
  7.41 ALONE assuming the height-1 point). Faithful as a cited named-leaf per CLAUDE.md.
- **File**: Presheaf.lean (+ Lemma745.lean for the 7.41 sub-leaf if cleaner)
- **Depends on**: T-ROIE-1
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem exists_cont_supp_ge_powerBounded_of_nonOpen_prime
    {A} [CommRing A] [TopologicalSpace A] [PlusSubring A] [IsTopologicalRing A] [IsHuberRing A]
    [T2Space A] [NonarchimedeanRing A] {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : ¬ IsOpen (𝔭 : Set A)) :
    ∃ v : Spv A, v ∈ Cont A ∧ 𝔭 ≤ v.supp ∧
      ∀ a ∈ (TopologicalRing.powerBoundedSubring A : Set A), v.vle a 1
```

#### Proof sketch (Wedhorn Remark 7.25 → Lemma 7.45 → Remark 7.42(2)/4.12 → Prop 7.41)
1. **Analytic point (Lemma 7.45):** the non-open prime `𝔭` is dominated by an analytic continuous
   valuation `v₀` with `𝔭 ≤ supp v₀`. In-repo: `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
   / `exists_spa_point_via_restrictToConvex` (a deep in-repo sorry; obtain a pair via
   `IsHuberRing.exists_pairOfDefinition`). NOTE: that lemma currently returns a Spa point bounded on
   `A₀`; here we only need the *analytic continuous* valuation with `𝔭 ≤ supp` — drop the `A⁺`/`A₀`
   bound and take its analytic content.
2. **Height-1 generization (Remark 7.42(2) / 4.12):** `v₀` analytic ⟹ microbial ⟹ ∃ height-1
   vertical generization `v` of `v₀` (Remark 4.12; unique). `supp v ⊇ supp v₀ ⊇ 𝔭` and `v` continuous
   (Remark 7.11(2)).
3. **Bounded on A° (Prop 7.41):** `v` height-1 analytic ⟹ `v(a) ≤ 1 ∀ a ∈ A°`. Wedhorn proof (≈6
   lines): if `v(a) > 1` for `a ∈ A°`, pick `b ∈ A°°` with `v(b) ≠ 0`; `Γ_v` height-1 ⟹ archimedean
   (Prop 1.14) ⟹ `∃n, v(aⁿb) > 1`; but `aⁿb ∈ A°°` so continuity ⟹ `v(aⁿb) < 1`, contradiction.
   → state Prop 7.41 as its own sub-leaf `heightOne_le_one_on_powerBounded` and PROVE it (provable).

#### Mathlib lemmas needed
height-1/microbial/archimedean valuation API (`LinearOrderedCommGroupWithZero`, Prop 1.14 analogue),
vertical-generization (Remark 4.12 — repo `restrictToConvex`/`ValuativeRel` vertical generization),
`A°°`-continuity (`IsTopologicallyNilpotent`).

#### Sources
Wedhorn Remark 7.25 (p.62), Lemma 7.45 (p.67), Remark 7.40(5)/7.42(2) (p.65/66), Prop 7.41 (p.66),
Remark 4.12. Residual deep leaf: Lemma 7.45 analytic-point existence (in-repo `restrictToConvex`).

#### Generality decision
Stated for any affinoid `(A, A⁺)` with `A⁺` a ring of integral elements implicit (the `A°` bound is
`A⁺`-independent — Prop 7.41 gives `Spa(A,A⁺)` membership for *every* such `A⁺`).

---

### [CLEANUP-FINAL] Run /cleanup-all on the ROIE diff
- **Status**: open
- **Depends on**: T-ROIE-2, T-ROIE-3, T-ROIE-4
- **Parallel**: no
- **Type**: cleanup
- **Description**: final pass; `#print axioms isSheafy_of_stronglyNoetherian_828b` to confirm the
  residual is exactly {[Hu1] 2.4.3, Lemma 7.45, + the pre-existing [Hu2] 3.3 / 7.49}.
