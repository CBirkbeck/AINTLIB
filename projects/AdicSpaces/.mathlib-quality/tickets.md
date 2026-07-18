# ★★★ CAMPAIGN COMPLETE (2026-07-17): ALL FIVE `FiniteJetMain` THEOREMS AXIOM-CLEAN ★★★
# `finiteJet_isSheafy` + `finiteJet_isUniform` + `finiteJet_isDomain` +
# `finiteJet_not_noetherian` + `finiteJet_not_stablyUniform` — every one
# `[propext, Classical.choice, Quot.sound]`, no sorryAx; `lake build «Adic spaces»` green
# (root imports `FJP.FiniteJetMain`; FJP files live in `Adic spaces/FJP/`).
# 𝓐 sheafy + uniform + domain + non-noetherian all verified; 𝓑 non-uniform verified.
# Remaining: NONE dispatchable — M7 stretch (needs /develop --continue), CLEANUP-* (cleanup fleet).
# ★ M8 COMPLETE (2026-07-17): HasLocLiftPowerBounded at FULL HUBER generality —
# hasLocLiftPowerBounded_huber + priority-1150 instance (no Tate, no noetherian),
# axiom-clean. IsSheafy's class parameter is now a THEOREM for every complete Huber
# ring with A⁺ a ring of integral elements — matching Wedhorn Prop 8.2/7.52's generality.

# Ticket Board — Campaign 4: Finite-jet pinching (uniform sheafy non-noetherian domain, not stably uniform)

**Contract**: every statement already exists as a `:= by sorry` declaration in the skeleton
(build-verified 2026-07-16, 3084 jobs). A ticket = *fill the named sorries*; statements are
NOT to be changed (B2-stop if a statement is wrong — report, don't bend). Each ticket cites
its decomposition leaves (`decomposition.md`, e.g. L3.2) which carry the verbatim [FJP]
quotes, discharge plans, and attack logs. Paper: `refs/AdicSpaces/sheafyring.pdf` (local
only). Priority spine: T1xx → T3xx → T4xx → T5xx → T6xx → T7xx (sheafiness). The T2xx track
(uniform/domain/non-noetherian) is parallel after T1xx.

## Summary
- Total: 36 tickets (28 proof + 8 embedded cleanup/milestone controls listed inline)
- Open: 25 | Done: 11 (T001, T101–T109, T201) | Parallel capacity at peak: 4 workers
  (T2xx ∥ T3xx ∥ T4xx-polynomial ∥ T1xx-tail)

## Milestone map
M0 T001 ✓ → M1 T101–T109 → { M2′ T201–T203 ∥ M2 T301–T304 ∥ M3 T401–T406 } → M4 T501–T505
→ M5 T601–T606 → M6 T701–T704 ★ → M5′ T801–T804. M7 (strong sheafiness) opens only after
T704, by a fresh `/develop --continue`.

---

### [T001] V0 gate: verify the consumed 828b theorem — **DONE 2026-07-16**
- **Status**: done. `lean_verify ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b`
  → `[propext, Classical.choice, Quot.sound]`, axiom-clean. Recorded in decomposition §0.

### [T101] `RestrictedLaurent.lean` — ring core — **DONE 2026-07-16**
- **Status**: done (beastmode). All ring-core sorries discharged: decay closures via
  `eventually_cofinite_ne`/squeeze; coefficient bound via `ℝ≥0`-`Finset.sup`; convolution
  summability via `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`; the `Mul`
  decay via the sumset/`image2` estimate + `IsUltrametricDist.norm_tsum_le_of_forall_le`;
  `mul_assoc` via `summable_conv_triple` (ℤ² nonarch summability) + `Summable.tsum_prod'`
  + the shear equivalence `(a,c) ↦ (a+c,a)`; `mul_comm` via `Equiv.subLeft`; distrib via
  `Summable.tsum_add`; `one_mul`/`mul_one`/`single_mul_single` via `tsum_eq_single`;
  `C`/`Wu` closed. Build green (3084 jobs). | **Type**: proofs (leaf L1.1)
- **Sorries**: `instOne/instAdd/instNeg` decay fields, `instMul` decay, `summable_mul_coeff`,
  `CommRing` proof fields, `single` decay, `single_mul_single`, `C` hom fields, `Wu`
  val_inv/inv_val.
- **Sketch**: decay closure by `Filter.Tendsto` squeeze (cofinite; `‖f+g‖ ≤ max`);
  summability: `Summable` of null family over ℤ in complete ultrametric K —
  `cauchySeq_of…`/`Summable.of_norm_bounded_eventually` route, or the nonarch criterion
  (`IsUltrametricDist` summable-iff-tendsto-zero: `Summable.of_tendsto_cofinite_zero`-style;
  search `IsUltrametricDist` summability lemmas). Ring axioms: `tsum` linearity + Fubini
  (`Summable.tsum_comm` on ℤ×ℤ with product summability from decay); assoc via double-sum
  regrouping (mirror vendored convolution proofs). `Wu`: `single_mul_single` + `single 0 1 = 1`.
- **Mathlib**: `tsum_add`, `Summable.tsum_comm`, `Summable.mul_of_nonneg`-analogues,
  `Filter.Tendsto.cofinite`. **Source**: [FJP] §1.4, (1.8) — quotes at L1.1.

### [T102] `RestrictedLaurent.lean` — norm package — **DONE 2026-07-16**
- **Status**: done (beastmode). Attained sup via `Set.exists_max_image` over the finite
  super-level set; `RingNorm` fields (mul_le' via `norm_tsum_le_of_forall_le`);
  ultrametric via `isUltrametricDist_of_isNonarchimedean_norm`; `norm_single`, `norm_W`,
  `norm_W_inv`, shift isometry `norm_W_mul` (+ helper `coeff_Wu_mul` via `tsum_eq_single`);
  completeness adapted from the vendored radius-c proof (coefficientwise Cauchy + uniform
  convergence + ultrametric decay transfer). Build green. | **Type**: proofs (L1.2)
- **Sorries**: `exists_gaussNorm_eq`, `norm_coeff_le_gaussNorm`, `isRingNorm` fields,
  `norm_single`, `norm_W`, `norm_W_inv`, `IsUltrametricDist`, `norm_W_mul`, `CompleteSpace`.
- **Sketch**: sup attained: decay ⟹ finitely many `‖coeff‖ ≥ ‖f‖/2` (mirror
  `MvRestricted.gaussNorm_achieved`); `mul_le'` via coefficientwise `‖∑'‖ ≤ sup·sup`
  (ultrametric tsum bound `norm_tsum_le` for nonarch); completeness: coefficientwise Cauchy
  + uniform decay (mirror `Restricted.isCompleteSpace`, CoramRestrictedNorm:257).
- **Source**: [FJP] Prop 2.3 attained-sup sentence (quote at L1.2).

### [T103] `RestrictedLaurent.lean` — multiplicativity & domain — **DONE 2026-07-16**
- **Status**: done (beastmode). Route (b) of the leaf plan (minimal-achiever), which
  needs NO discreteness: minimal achievers `a₁, b₁` via `Set.exists_min_image` on the
  finite achiever sets; the `(a₁+b₁)`-coefficient splits off its `a₁`-term
  (`tsum_eq_add_tsum_ite`); every other term is strictly submaximal; new helper
  `norm_tsum_lt_of_forall_lt` (attained-sup strict bound) + the ultrametric isosceles
  argument give equality. `mul_ne_zero_of_ne_zero` from positivity of the norm.
  The unused `hd` hypothesis is retained for statement stability. | **Type**: proofs (L1.3)
- **Sorries**: `norm_mul_eq`, `mul_ne_zero_of_ne_zero`.
- **Sketch**: route (a) residue reduction: scale to norm 1 by an attained coefficient
  (T102); reduce `{‖·‖ ≤ 1} → AddMonoidAlgebra F ℤ` (kill `< 1` = `≤ |ϖ|` coefficients —
  discreteness `norm_K_discrete` from T108); reduction is multiplicative on norm-one
  elements (finitely many norm-one coefficients); `AddMonoidAlgebra` over a field with ℤ
  (`UniqueProds` via linear order) is a domain. Route (b) fallback: min-index achiever
  convolution argument (leaf log L1.3 attack 3).
- **Mathlib**: `AddMonoidAlgebra`, `NoZeroDivisors` instance (`UniqueProds.of_covariant…`),
  `Finsupp` support lemmas. **Source**: [FJP] Prop 2.3 full multiplicativity paragraph.

### [CLEANUP-1] /cleanup `RestrictedLaurent.lean` — **Depends**: T103.

### [T104] `RestrictedLaurent.lean` — nonneg subring, `nonnegEquiv`, `evalHom` — **DONE 2026-07-17**
- **Status**: done (beastmode). File is now **0-sorry**. Beyond part 1/2: `negate`
  automorphism (+ involution, `norm_negate`), `evalLE` (evaluation at a unit-ball point —
  multiplicativity via the mathlib nonarchimedean Cauchy-product
  `Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal`), `restrictedCongr` +
  `coeff_restrictedCongr`/`restrictedCongr_norm`, `innerToSeries` (Fin-1 ↔ univariate via
  `finSuccOne` + `foo`), `negOfSeries` (isometric), `Wu_pow`, `evalHom` assembled with
  `evalHom_norm_le`, and `evalHom_surjective` via the explicit section (`truncNonpos` +
  constant-coefficient tail, coefficient/tsum interchange through `HasSum.map` along the
  1-Lipschitz `coeffHom`). NOTE: file now imports `ExampleUnitDisc` (for `finSuccOne`) —
  acceptable; flagged for the final cleanup pass. | **Type**: def-completion (L1.4)
- **Sorries**: `nonnegSubring` closure fields, `isClosed_nonnegSubring`, `nonnegEquiv`
  (data + proofs), `nonnegEquiv_norm`, `ofRestricted_norm/injective`, `evalHom` (data +
  fields), `evalHom_surjective`, `evalHom_norm_le`.
- **Sketch**: closure: convolution support additivity on ℕ; closedness: intersection of
  coefficient-functional kernels; `nonnegEquiv`: coefficient transport `ℕ ↪ ℤ`
  (`PowerSeries.coeff` ↔ `coeff (a : ℤ)`, zero on negatives); `evalHom`: on a restricted
  2-variable series `∑ c_{ij} W^i V^j ↦ ∑ c_{ij} W^{i−j}` — coefficient of `a` is
  `∑'_{i−j=a} c_{ij}` (summable, decay); surjectivity via the monomial section (L1.4).
- **Source**: [FJP] Lemma 2.2 (`k⟨W⟩` closed), Prop 2.1 (presentation) — quotes at L1.4.

### [CLEANUP-2] /cleanup `RestrictedLaurent.lean` (final) — **Depends**: T104. In progress with T104 close-out (lint scan; import-weight note carried to CLEANUP-FINAL).

### [T105] `JetDualNumberNorm.lean` — complete file — **DONE 2026-07-17**
- **Status**: done (beastmode). File is **0-sorry**: max-norm `RingNorm` (cross term via
  ultrametric + `op_smul_eq_mul`), `norm_inl`/`norm_eps_smul`, ultrametric + `NormOneClass`
  + componentwise `CompleteSpace`, jet-power formula via `TrivSqZeroExt.snd_pow`, `mapHom`
  functoriality (+ norm, injectivity), `aeval_eps_surjective` and
  `isNoetherianRing (DualNumber S)` via the `S[X] ↠ S[ε]` surjection. | **Type**: proofs (L1.5)
- **Sorries**: all 20 (`isRingNorm` fields, `norm_inl`, `norm_eps_smul`, ultrametric,
  `NormOneClass`, `CompleteSpace`, `pow_eq`, `mapHom` fields + `norm_mapHom` +
  `mapHom_injective`, `aeval_eps_surjective`, `isNoetherianRing`).
- **Sketch**: max-norm axioms (cross-term ultrametric bound); completeness: product of two
  copies (`TrivSqZeroExt` = `R × R` as additive group — `CompleteSpace.prod` transported);
  `pow_eq` by induction (`Q² = 0`: `TrivSqZeroExt.inr_mul_inr` = 0); noetherianity:
  `Polynomial.aeval ε` surjective (`a + bε = aeval (C a + X·C b)`… over `S`) +
  `isNoetherianRing_of_surjective`.
- **Mathlib**: `TrivSqZeroExt.fst_mul/snd_mul/inl_mul_inl/inr`, `DualNumber.eps`,
  `isNoetherianRing_of_surjective`. **Source**: [FJP] (5.2) power display; Lemma 2.2 max
  norm — quotes at L1.5.

### [CLEANUP-3] /cleanup `JetDualNumberNorm.lean` (final) — **Depends**: T105. Folded into the T105 close-out (no outstanding lints beyond project-standard warnings).

### [T106] `FiniteJetRings.lean` — square maps and sections — **DONE 2026-07-17**
- **Status**: done (beastmode). `rhoC` ring hom (2-jet truncation; multiplicativity by
  antidiagonal-0/1 evaluation), `sectionD` + `qCoeff_sectionD`/`rhoC_sectionD`/
  `sectionD_add`/`norm_sectionD` (two-sided via `le_gaussNorm` at indices 0, 1),
  `norm_rhoC_le`, `norm_rhoB` (= `mapHom` of the isometric `ofRestricted`),
  `rhoB_injective`, `rhoC_surjective`. | **Type**: proofs (L1.6 first half)
- **Sorries**: `rhoC` hom fields, `sectionD` decay + `rhoC_sectionD` + `sectionD_add` +
  `norm_sectionD`, `norm_rhoC_le`, `norm_rhoB`, `rhoB_injective`, `rhoC_surjective`.
- **Sketch**: `rhoC` multiplicativity: `PowerSeries.coeff_mul` at indices 0, 1 matches
  `TrivSqZeroExt` multiplication (2-term convolution); `sectionD` is the degree-≤1 series;
  norms by coefficient inspection. Do NOT claim `sectionD` multiplicative (L1.6 attack 2).
- **Source**: [FJP] Prop 2.1 section sentence — quote at L1.6.

### [T107] `FiniteJetRings.lean` — 𝓐 and the strict row — **DONE 2026-07-17**
- **Status**: done (beastmode). `qCoeff` algebra helpers (`qCoeff_zero_mul`/`one_mul`/…,
  `continuous_qCoeff` 1-Lipschitz), `jetSupport` closure incl. the jet-multiplication
  argument, `isClosed_jetSupport` (preimage form), `CompleteSpace (JetA F)` via
  `IsClosed.completeSpace_coe`, `jB` (term-style `congrArg`/`trans` proofs through
  `nonnegEquiv.symm`), `norm_jB_le`, `square_commutes`, `mem_jetSupport_iff_jet_in_range`
  (via `mem_range_ofRestricted_iff`), `milnorRow_exact` (existence + uniqueness through
  `ofRestricted_injective`), `max_norm_eq`, `difference_strict_surjective` (constants 1 —
  [FJP] (2.1b)). | **Type**: proofs (L1.6 second half)
- **Sorries**: `jetSupport` closure fields, `isClosed_jetSupport`, `CompleteSpace (JetA F)`,
  `jB` hom fields, `norm_jB_le`, `square_commutes`, `mem_jetSupport_iff_jet_in_range`,
  `milnorRow_exact`, `max_norm_eq`, `difference_strict_surjective`.
- **Sketch**: support additivity (paper's S-monoid, subcases in L1.6 attack 1); closedness →
  completeness (`IsClosed.completeSpace_coe`); row exactness: membership chase through
  `nonnegEquiv`; `max_norm_eq`: `‖jB a‖ = max(‖c₀‖,‖c₁‖) ≤ ‖a‖ = ‖ιC a‖`.
- **Source**: [FJP] Prop 2.1 + Lemma 2.2 + (2.1b) — quotes at L1.6.

### [T108] `FiniteJetRings.lean` — constants, Tate structure, `unitBall` — **DONE 2026-07-17**
- **Status**: done (beastmode). Constants (`constHomC`/`constC`/`constA`/`constHomPS`) with
  norms and 𝓐-membership; `tA/tB/tC/tD` pseudouniformizers (norms via
  `Valued.toNormedField.norm_lt_one_iff` + `valuation_t`; units via `IsUnit.map`); scalar
  scaling lemmas (`norm_C_mul`/`norm_restrictedC_mul` in `RestrictedLaurent.lean` via
  `Real.mul_iSup_of_nonneg`, per-ring `norm_t*_mul`); `unitBall` (with the recorded
  `NormOneClass` signature fix) + openness; the **generic
  `unitBallPod`/`isHuberRing_of_scale`/`isTateRing_of_scale`** (norm-scaling
  pseudouniformizer ⟹ pair of definition, adapting `ExampleUnitDisc.podD`'s isAdic);
  all eight `IsHuberRing`/`IsTateRing` instances are real terms. Also new
  `NormOneClass (PowerSeries.Restricted R 1)` + `NormOneClass (JetA F)` instances.
  | **Type**: proofs (L1.7 first half)
- **Sorries**: `norm_K_discrete`, `constC` (data + norm), `constC_mem_jetSupport`, `constA`,
  `tA` norm/unit lemmas, `unitBall` fields + `isOpen_unitBall`, `IsHuberRing ×4`,
  `IsTateRing ×4`.
- **Sketch**: `norm_K_discrete` from `Valued.toNormedField` + `WithZeroMulInt.toNNReal 2`
  normalisation (unfold the `RankOne` hom; mirror `ExampleUnitDisc` norm lemmas);
  Tate/Huber: `podD` pattern with `unitBall` + `Ideal.span {t}`; topological nilpotence of
  `t` from `‖t‖ < 1` + norm multiplicativity on constants.
- **Source**: [FJP] (2.1a) — quote at L1.7.

### [CLEANUP-4] /cleanup `FiniteJetRings.lean` — **Depends**: T108.

### [T109] `FiniteJetRings.lean` — plus rings and right-uniformity completeness — **DONE 2026-07-17**
- **Status**: done (beastmode). `norm_K_discrete` (via `Valued.toNormedField.norm_def` +
  `WithZeroMulInt.toNNReal_neg_apply`); right-uniformity `CompleteSpace ×4`
  (`IsUniformAddGroup.rightUniformSpace_eq`); the generic
  `isRingOfIntegralElements_powerBounded` (openness via ball-membership +
  `AddSubgroup.isOpen_of_mem_nhds`; integral closedness via the project's
  `isPowerBounded_of_isIntegral_of_subset_powerBounded`; plus `isBounded_unitBall` and
  `unitBall_subset_powerBounded` generics) instantiated ×4.
  **M1 (construction layer) COMPLETE: RestrictedLaurent, JetDualNumberNorm, and
  FiniteJetRings are all 0-sorry.** | **Type**: proofs (L1.7 second half)
- **Sorries**: `IsRingOfIntegralElements ×4`, right-uniformity `CompleteSpace ×4`.
- **Sketch**: `E°` open (⊇ ball), integrally closed ([FJP] §5 monic-`M`-module argument —
  quote at L1.7), `subset_powerBounded` refl; completeness: `SeminormedAddCommGroup.to_isUniformAddGroup`
  + `IsUniformAddGroup.rightUniformSpace_eq` + metric completeness (disc pattern,
  `ExampleUnitDisc.lean:492`). NOTE (L1.7 attack 2): plus ring is the MAXIMAL one; do not
  attempt the unit ball for 𝓑/𝓓.
- **Source**: [FJP] p. 17 (5.2) block — quotes at L1.7.

### [CLEANUP-5] /cleanup `FiniteJetRings.lean` (final) — **Depends**: T109. Light pass folded into T109 close-out; full lint sweep deferred to CLEANUP-ALL-1.

### [T201] `FiniteJetUniformDomain.lean` — multiplicativity, domains — **DONE 2026-07-17**
- **Status**: done (beastmode). `norm_L_mul` (one-liner from T103), `norm_JetC_mul` via the
  vendored `PowerSeries.gaussNorm_mul_eq_mul` with the minimal-achiever dominance witness
  (`finite_setOf_le_norm_qCoeff` + `exists_norm_qCoeff_eq` + `Set.exists_min_image`;
  `achievesGaussNorm_iff` bridging), `Nontrivial`/`NoZeroDivisors`/`IsDomain` for 𝒞 and 𝓐
  (norm positivity route; subring transfer). **The `finiteJet_isDomain` headline ingredient
  is proven.** | **Type**: proofs (R2 leaves)
- **Sorries**: `norm_L_mul`, `norm_JetC_mul`, `IsDomain (JetC F)`, `IsDomain (JetA F)`.
- **Sketch**: `norm_L_mul` = `RestrictedLaurent.norm_mul_eq` at `norm_K_discrete`;
  `norm_JetC_mul` via vendored univariate mult lemma over base `L` (check its exact
  hypothesis shape — risk 2; fallback: ℤ×ℕ achiever, L1.3); domains from multiplicativity;
  `JetA` domain via `Subring` + `IsDomain` of `JetC` (`Function.Injective.isDomain`).

### [T202] `FiniteJetUniformDomain.lean` — uniformity and (5.2)
- **Status**: **DONE** (part 1: `norm_JetA_mul/pow`, `isPowerBounded_JetA_iff` via tA-escape +
  inline Huber-power-boundedness, `isUniform_JetA`, both `maxHeartbeats 1000000` — cleanup
  candidates; part 2: generic `norm_pow_le_of_fst_le` + `isPowerBounded_dualNumber_iff`
  (dual numbers over any multiplicative base w/ scaling pseudouniformizer) instantiated to
  `isPowerBounded_JetB_iff`/`isPowerBounded_JetD_iff`; `not_isUniform_JetB` via the
  square-zero element `inr (constHomPS t^{-(m+1)})` — power-bounded by the iff (fst = 0),
  kills the ball-1 boundedness of `powerBoundedSubring 𝓑` against `tB^m`-scaling). **The
  `isUniform_JetA` and `not_isUniform_JetB` headline ingredients are proven.**
  | **Type**: proofs (R2 + R4 inputs)
- **Sorries**: `isPowerBounded_JetA_iff`, `isUniform_JetA`, `isPowerBounded_JetB_iff`,
  `isPowerBounded_JetD_iff`, `not_isUniform_JetB`.
- **Sketch**: powers via `norm_JetC_mul` restricted (L: "powers computed in 𝒞"); ball
  bounded: `t`-absorption (disc `isBounded_OD` pattern); (5.2) via `JetNorm.pow_eq` + Gauss
  multiplicativity on the fst-component; `not_isUniform_JetB`: `{inr (λ)} = λ·ε` family
  power-bounded with `‖λε‖ = |λ|` unbounded — negate `IsBounded` via the `t^{-n}`-scaling
  characterisation.
- **Source**: [FJP] Prop 2.3 + (5.2) + (2.1d) — quotes at R2/L1.7/R4.

### [T203] `FiniteJetUniformDomain.lean` — non-noetherianity (R3 complete)
- **Status**: **DONE** (`winv_not_integral`: read off the `W^{-n}`-coefficient of the monic
  relation — `coeff_mul_single_one` shift + `coeff_ofRestricted'` extension-by-zero, top term
  `1`, lower terms at negative exponents vanish; `not_moduleFinite_L` via
  `Algebra.IsIntegral.of_finite`; `moduleFinite_of_ker_jB_fg`: concrete `J/KJ ≅ L` transport —
  `jB_eq_zero_iff` (ker jB = Q²𝒞), `q2elt` Q²-monomial witness, `qCoeff_two_mul` +
  generator-jet vanishing reads the span decomposition off at Q², coefficients land in
  `nonnegSubring` → `K⟨W⟩`-span; `ker_jB_not_fg`, `not_isNoetherianRing_JetA` chain. All three
  axiom-clean (propext/Classical.choice/Quot.sound). **The `not_isNoetherianRing_JetA`
  headline ingredient is proven; file sorry-free; M2′ complete.** | **Type**: proofs
- **Sorries**: `winv_not_integral`, `not_moduleFinite_L`, `moduleFinite_of_ker_jB_fg`,
  `ker_jB_not_fg`, `not_isNoetherianRing_JetA`.
- **Sketch**: R3 leaf (decomposition) — monic relation × `Wⁿ`, all terms in the
  `ofRestricted`-image, `constantCoeff` on `K⟨W⟩` gives `1 = 0`;
  `Algebra.IsIntegral.of_finite` for the finite⟹integral step; `moduleFinite_of_ker_jB_fg`:
  generators' `Q²`-leading coefficients generate `L` over `K⟨W⟩` (the `J/KJ ≅ L` transport,
  done concretely: for `x ∈ J = ker jB`, write `x = ∑ aᵢxᵢ`, read off the `Q²`-coefficient
  mod `Q`-multiples — [FJP] "Modulo `KJ`, multiplication by `f₀+Qf₁+Q²h` remembers only
  `f₀`").
- **Source**: [FJP] Prop 2.4 — full quote at R3. **Note**: statements are deliberately
  concrete (no `J/KJ` quotient-module formalisation needed).

### [CLEANUP-6] /cleanup `FiniteJetUniformDomain.lean` (final) — **Depends**: T202, T203.

### [T301] `FiniteJetNoetherianVertices.lean` — `L` strongly noetherian
- **Status**: **DONE** (`evalHom_exists_norm_le` — evalHom_surjective strengthened in place
  to a norm-nonincreasing section (norm_truncNonpos_le + coefficient sup bound), original
  theorem re-derived; generic `mapRestrictedGauss` (coefficientwise φ on radius-1
  MvRestricted, squeeze for restrictedness) + `mapRestrictedGauss_surjective` (choice on the
  bounded section); `isNoetherianRing_restricted_L`: restrictedGaussEquiv(L) ∘
  mapRestricted(evalHom) ∘ (exists_flatten' ×2: K⟨W,V⟩⟨Z⃗ₘ⟩ ≅ K⟨m+2 vars⟩) surjection from
  `IsStronglyNoetherian K` anchor. Axiom-clean. `IsStronglyNoetherian (L F)` +
  `IsNoetherianRing (L F)` instances live.) | **Type**: proofs (L2.1)
- **Sorries**: `isNoetherianRing_restricted_L`.
- **Sketch**: per-`m` surjection `K⟨W,V,Z₁..Zₘ⟩ ↠ L⟨Z₁..Zₘ⟩`: vendored
  `restrictedGaussEquiv` (both ends) + `exists_flatten'`-style regrouping +
  `mapRestricted (evalHom)` surjectivity (coefficientwise section) +
  `isNoetherianRing_of_surjective` + `IsStronglyNoetherian K`. NEVER "noeth ⟹ strongly
  noeth" (B2). **Source**: [FJP] Prop 2.1 quotient sentence — quote at L2.1.

### [T302] vertices strongly noetherian
- **Status**: **DONE** (`isNoetherianRing_restricted_univariate` — generic disc pattern over
  any complete NormOneClass strongly-noetherian base via `innerToSeries.symm` +
  `exists_flatten'` → `IsStronglyNoetherian (JetC F)` over L; dual-number flattening WITHOUT
  a pair-algebra RingEquiv: surjection `Polynomial(S⟨Z⃗⟩-Gauss) → (DualNumber S)⟨Z⃗⟩-Gauss` via
  `Polynomial.eval₂RingHom (mapRestrictedGauss inlHom) epsRestricted` (Hilbert basis on the
  source; decomposition `F = inl∘fst + inl∘snd·ε` per coefficient) →
  `isNoetherianRing_restricted_dualNumber` → `IsStronglyNoetherian (JetB F)` (base K⟨W⟩) and
  `(JetD F)` (base L). All axiom-clean.) | **Type**: proofs (L2.2–L2.3)
- **Sorries**: `IsStronglyNoetherian (JetC F)`, `isNoetherianRing_restricted_dualNumber`,
  `IsStronglyNoetherian (JetB F)`, `(JetD F)`.
- **Sketch**: JetC = disc-example flattening verbatim over base `L` (copy
  `ExampleUnitDisc`'s instance proof, base swapped); dual-number flattening
  `(DualNumber S)⟨Z⟩ ≅ DualNumber (S⟨Z⟩)` coefficientwise (fst/snd of coefficients) +
  `JetNorm.isNoetherianRing`.

### [T303] unit-ball pods noetherian
- **Status**: **DONE** (generic `isNoetherianRing_unitBall_of_section`/`_of_isometry`
  transfer lemmas (ball codRestrict + section); anchor `isNoetherianRing_unitBall_gaussK`:
  the integral `K⟨T₁..Tₖ⟩` is the `psiR`-image of `(MvPolynomial (Fin k) F)⟦X⟧`
  (`exists_psi_eq` + `Valued.toNormedField.norm_le_one_iff` bridge, `psi_coeff_v_le` at 0);
  `norm_mapRestrictedGauss_le` + `mapRestrictedGauss_exists_norm_le` (strengthened in place);
  NormOneClass instance for radius-1 Gauss rings; `unitBall_L` (evalHom from k=2 anchor),
  `unitBall_KW` (innerToSeries from k=1), `unitBall_JetC` (flatten ×2 + coefficientwise
  evalHom + innerToSeries over L from k=3), `unitBall_JetB/JetD` via generic
  `isNoetherianRing_unitBall_dualNumber` (ε-polynomial image of the ball, Hilbert basis).)
  | **Parallel**: with T302 | **Type**: proofs (L2.4)
- **Sorries**: `isNoetherianRing_unitBall_L/JetB/JetC/JetD`.
- **Sketch**: `k° = F⟦X⟧` noetherian; integral restricted rings as ϖ-adic completions of
  polynomial rings (`AdicCompletionBridge` pattern / `Psi`-transpose as in
  `ExampleLaurentSeries`'s strong-noetherianity proof); balls of `L`/`JetC` are quotients/
  images of those; `DualNumber` of noetherian (T105). Fallbacks recorded at L2.4.

### [CLEANUP-7] /cleanup `FiniteJetNoetherianVertices.lean` — **Depends**: T302, T303.

### [T304] vertices sheafy (828b application)
- **Status**: **DONE** (one-liner ×3: `ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b`
  — the T109 instance bundle + T302 strong noetherianity resolve by instance search, exactly
  as `isSheafy_unitDisc`. `isSheafy_JetB/JetC/JetD` all axiom-clean.
  **`FiniteJetNoetherianVertices.lean` is sorry-free; milestone M2 complete.**)
  | **Type**: proofs (L2.5)
- **Sorries**: `isSheafy_JetB/C/D`.
- **Sketch**: `exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` with the letI
  plumbing of `ExampleUnitDisc.isSheafy_unitDisc`; if instance search balks, `haveI` the
  bundle members explicitly. All bundle members exist by T109/T302.

### [CLEANUP-8] /cleanup `FiniteJetNoetherianVertices.lean` (final) — **Depends**: T304.

### [T401] `FiniteJetGraphKoszul.lean` — polynomial syzygies, coordinate case
- **Status**: **DONE** (`d1_d2`: sum_comm + pairwise mul_right_comm; `syzygy_coordinate`:
  the planned induction on m — strip variable 0 via `finSuccEquiv`, `hrel` in `A[y]`,
  `coeff 0` gives the reduced syzygy `a` over `Fin m`, IH wedge `w`, `divX` decomposition
  `U i.succ = y·Q i + C (a i)`, `y`-cancellation (`coeff_X_mul` shift) gives
  `U 0 = -∑ Qᵢ C(Xᵢ)`, wedge assembled by dite on `p.1.1 = 0` (`e.symm (Q ·)` on the
  0-row, `e.symm (C (w ·))` on succ-pairs); both components verified through
  `e.injective` + dite-simp + `ring`. Axiom-clean.) | **Type**: proofs (L3.1–L3.2)
- **Sorries**: `d1_d2`, `syzygy_coordinate`.
- **Sketch**: `d1_d2`: `Finset.sum` reindexing, terms cancel in pairs; `syzygy_coordinate`:
  induction on `m` (L3.2 log has the full argument: reduce mod `T_m` via
  `MvPolynomial.aeval`-substitution to `Fin (m−1)`, IH, correct with `T_m e_j − T_j e_m`,
  extract the `T_m`-cofactor, close with mul-by-variable injectivity).
- **Mathlib**: `MvPolynomial.finSuccEquiv` (poly version), `Polynomial` mul-X-injective.

### [T402] graph syzygies over the polynomial ring
- **Status**: **DONE** — but by a REFINEMENT of the planned route: instead of localized
  Koszul-homology modules at every prime, the proof is fully elementary/global via the
  ideal of reachable multipliers `A := {a | ∃ v, d2 r v = a • u}` (an ideal by
  d2_zero/add/smul): (i) each `rᵢ ∈ A` explicitly (`d2_koszul_single`, the contractibility
  wedge, verified componentwise with the [FJP] formula); (ii) `(C g)^P ∈ A` via base change
  to `MvPoly(D_g)` — `syzygy_graph_of_isUnit` (translation automorphism `translationEquiv` +
  unit rescale + T401 coordinate case), then `exists_pow_C_mul_eq_map` (denominator
  clearing by MvPolynomial.induction_on) and `exists_pow_C_mul_eq_zero_of_map_eq_zero`
  (g-power torsion kernel) pull the wedge back; (iii) `1 ∈ span((Cg)^P, r⃗) ≤ A` by the
  (4.3) combination + quotient-nilpotence (mk(Cg·G) = 1, mk(Cg)^P = 0 ⟹ quotient trivial).
  Same two-case dichotomy as [FJP], no localized-module API. Axiom-clean.
  | **Type**: proofs (L3.3)
- **Sorries**: `syzygy_graph_polynomial`.
- **Sketch**: localize at maximal ideals (`Submodule.eq_top_of_localization_maximal` on the
  quotient submodule Syz/⟨Koszul⟩, or eq_bot form); case split on `r_i ∉ 𝔭` (explicit
  Koszul expression — formula in L3.3 log) vs all `r_i ∈ 𝔭` (then `g ∉ 𝔭` by (4.3);
  translate `T_i ↦ T_i + f_i/g` via `MvPolynomial.aeval` automorphism; unit-scale
  `v_{ij} ↦ g² v_{ij}`-corrected; T401). m = 1 comes out as `ker = 0` automatically.
- **Source**: [FJP] Lemma 4.2 proof ¶1 — full quote in file docstring + L3.3.

### [T403] `mapRestricted` + `polyToP`
- **Status**: **DONE** (`mapRestricted` general-radius via `isRestrictedGauss_abs_iff`
  squeeze; `norm_mapRestricted_le` via `le_gaussNorm` + StrongPos; `polyToP` via
  `MvPolynomial.IsRestrictedGauss` + `coeToMvPowerSeries.ringHom` laws.)
  | **Type**: def-completion (L3.4 + `polyToP`)
- **Sorries**: `mapRestricted` membership + hom fields, `norm_mapRestricted_le`, `polyToP`.
- **Sketch**: `MvPowerSeries.map` coefficient formula; decay via `‖φ x‖ ≤ ‖x‖`; `polyToP`
  via vendored `MvPolynomial.toMvRestricted` (or coefficient-finsupp embedding).

### [CLEANUP-9] /cleanup `FiniteJetGraphKoszul.lean` — **Depends**: T401–T403.

### [T404] flatness of `E[T] → E⟨T⟩`
- **Status**: **DONE** (plan of record executed in full: ballAdicEquiv — the direct
  algebraic (4.4) identification `unitBall(E⟨T⃗⟩) ≃+* AdicCompletion (C t₀) (E₀[T⃗])` via
  truncation classes/mk_trnc_eq/coefficientwise-Cauchy surjectivity; then
  `AdicCompletion.flat_of_isNoetherian` + AlgEquiv transport (`Module.Flat.of_linearEquiv`)
  gives the ball flat over `E₀[T⃗]`; hand-built `IsLocalization (powers (C t₀)) (E[T⃗])` and
  `IsLocalization (algebraMapSubmonoid …) (E⟨T⃗⟩)` instances (coefficient-clearing +
  norm-absorption); `isLocalizedModule_iff_isLocalization` →
  `IsLocalizedModule.isBaseChange` → base-change flatness → transport. `flat_polyToP`
  axiom-clean, with the t-bundle signature completion.) | **Type**: proofs (L3.5)
- **Plan of record (algebraic route, no uniform-space bridge)**: statement gets the
  standard scaling-pseudouniformizer bundle `(t, htu, ht1, ht0, hscale)` (as in
  `unitBallPod` — legitimate signature completion; instantiations 𝓑/𝓒/𝓓 have tB/tC/tD).
  Sub-lemmas: (L1) `coeff_polyToP`; (L2) `norm_tP_mul` (C t-scaling on P via
  `Real.mul_iSup_of_nonneg`); (L3) generic ball division `x = tⁿ·y, ‖y‖ ≤ 1` from
  `‖x‖ ≤ ‖t‖ⁿ` (unit + `norm_pow_mul_of_scale`); (L4) = L3 at `(P E m, tP)`;
  (L5) polynomial division: all-coeffs ≤ ‖t‖ⁿ ⟹ `∈ (C t₀)ⁿ`-span over `E₀ = unitBall E`;
  (L6) `Φ : unitBall (P E m) ≃+* AdicCompletion (span {C t₀}) (MvPoly E₀)` built DIRECTLY:
  truncations `trnc n F` over the finite super-level set, compatible classes; ring-hom by
  the L5 division on `trnc(FG) − trnc F·trnc G` (tails bounded by ‖t‖ⁿ since ball);
  injective by ‖F‖ ≤ ‖t‖ⁿ ∀n; surjective by coefficientwise Cauchy limits of reps
  (`p_{n+1} − p_n ∈ I₀ⁿ` ⟹ coeff-Cauchy, complete E); (L7) flat transport:
  `AdicCompletion.flat_of_isNoetherian` (Hilbert + T303) + AlgEquiv transport + two
  `IsLocalization (powers ·)` instances (E = E₀[1/t] pattern, coefficientwise) +
  `isLocalizedModule_iff_isLocalization` → `IsLocalizedModule.isBaseChange` →
  `Module.Flat.baseChange` → `Module.Flat.of_linearEquiv`.
- **Sorries**: `flat_polyToP`.
- **Sketch**: (4.4): `E₀⟨T⟩ = AdicCompletion (t) (E₀[T])` (coefficientwise; the heaviest
  sub-leaf — mirror `AdicCompletionBridge`); `AdicCompletion.flat_of_isNoetherian`
  (`E₀[T]` noetherian by T303 + Hilbert basis); invert `t`
  (`Module.Flat` of localization + composition). ONLY positive-degree facts downstream —
  never claim faithful flatness (L3.5 attack 1).
- **Source**: [FJP] (4.4) + Tag 00MB sentence — quote at L3.5.

### [T405] syzygy transport to `E⟨T⟩`
- **Status**: **DONE** — via mathlib's **equational criterion for flatness**
  (`Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`, Stacks 00HK) instead of
  kernel-tensor identifications: the P-relation `∑ ρᵢ • uᵢ = 0` factors through a finite
  matrix `a` with polynomial-syzygy columns; T402 Koszul-expresses each column; `d2_sum`
  (new finite-sum linearity) + `d2_map` reassemble the wedge over `P`. Axiom-clean.
  (TC quirk: pass the Flat instance by dot-notation.) | **Type**: proofs (L3.6)
- **Sorries**: `syzygy_graph_restricted`.
- **Sketch**: kernels of matrix maps commute with flat base change (`Module.Flat` +
  `LinearMap.ker` tensor lemmas); span of pushed Koszul generators; identification of
  `Fin m → P` with the base-changed free module.

### [T406] closedness and strictness constants
- **Status**: **DONE** (plan of record executed: (i) `isClosed_graphIdeal` :=
  `Wedhorn.isClosed_ideal_of_noetherian` at the tP-`unitBallPod` (t-bundle + `hE₀P`
  statement completion); (ii) `exists_lift_norm_le_of_closed_range` — the NEW generic
  ultrametric Banach-with-constants lemma, proven in full: Baire on the closed range,
  ball-image closures as open subgroups, `hδkey`, t-equivariant approximation `step`,
  `Nat.rec` dependent-choice sequences, geometric ultrametric series correction
  (Summable.of_norm_bounded + HasSum.map + partial-sum ultrametric bound), and the
  `[δ‖t‖, δ)` Nat.find window for the constant `max 1 (R/(δ‖t‖))`;
  (iii) `exists_d1_lift`/`exists_d2_lift` derived (part 2). All axiom-clean.
  **`FiniteJetGraphKoszul.lean` is sorry-free — milestone M3 complete.**)
  | **Type**: proofs (L3.7–L3.9)
- **Plan of record**:
  (i) `isClosed_graphIdeal` := `Wedhorn.isClosed_ideal_of_noetherian` at the pod
  `unitBallPod tP …` (tP := polyToP (C t); instances IsTateRing (P E m) via
  `isTateRing_of_scale`, T2/Complete/UniformAddGroup present) — REQUIRES noetherian pod-A₀ =
  `IsNoetherianRing (unitBall (P E m))`: add as hypothesis `hE₀P` (statement completion, like
  the t-bundle; dischargeable at the vertices by the T303 arity-generic ball-transfer
  machinery). Also add the t-bundle to the statement.
  (ii) generic `exists_lift_norm_le_of_closed_range` (NEW, ultrametric Banach with
  constants): for a continuous `t`-equivariant additive map `f : (ι → A) →+ (κ → A)` over
  complete ultrametric `A` with closed range: Baire on the closed range (complete metric →
  BaireSpace), cover by closures of images of `‖t‖⁻ᴺ`-balls (balls are subgroups
  ultrametrically, so images/closures are subgroups; nonempty interior ⟹ open via
  `AddSubgroup.isOpen_of_mem_nhds`), remove the closure by the geometric ultrametric
  series correction (t-equivariance rescales the approximation), extract the constant by
  the `exists_mem_Ico_zpow` window `δ‖t‖ ≤ ‖t‖^k‖y‖ < δ`.
  (iii) `exists_d1_lift` := (ii) at `f := d1`-as-hom (range = span(range r) by
  `mem_span_range_iff_exists_fun`, closed by (i));
  `exists_d2_lift` := (ii) at `f := d2`-as-hom (range = ker d1 : closed since d1 continuous;
  range ⊇ ker by `syzygy_graph_restricted`, ⊆ by `d1_d2`); `m = 1` degenerate case noted in
  the statement handles itself (`Pairs 1` empty ⟹ ker d1 = 0 forced).
  Both get the t-bundle + `hE₀P` as needed (statement completion, recorded).
- **Sorries**: `isClosed_graphIdeal`, `exists_d1_lift`, `exists_d2_lift`.
- **Sketch**: finite-module theory over noetherian `P` (`NoetherianTateModules.lean`:
  module topology = Banach on finite frees; submodules closed; surjections open) →
  images/kernels closed; OMT-with-constants: corestrict `d₁`/`d₂` to closed images
  (`ContinuousLinearMap.exists_preimage_norm_le` over `K`; build the small
  `NormedSpace K` instances for `P`/tuples as prep). m = 1: `Pairs 1` empty; `exists_d2_lift`
  reduces to `ker d₁ = 0` — supplied by T405.
- **Source**: [FJP] Lemma 4.2 final ¶ — quote at L3.7.

### [CLEANUP-10] /cleanup `FiniteJetGraphKoszul.lean` (final) — **Depends**: T406.

### [T501] `FiniteJetStrictLocalization.lean` — Lemma 4.1 layer
- **Status**: **DONE** (coefficientwise as planned: `ext_square_commutes` (4×coeff_map +
  square_commutes), `extRhoC_strict_surjective` (sectionD coefficientwise, norm_sectionD
  restrictedness + gauss sup), `ext_milnorRow_exact` (the JetA-valued coefficient series
  ⟨coeff c, mem⟩ with milnorRow_exact per coefficient; uniqueness via iotaC-injectivity),
  `ext_max_norm_eq` (‖extIotaC‖ = ‖p‖ isometric + norm_mapRestricted_le → max_eq_right),
  `ext_pair_injective` (MvPowerSeries.map_injective on iotaC). Constants 1 throughout.)
  | **Type**: proofs (L4.1)
- **Sorries**: `ext_square_commutes`, `extRhoC_strict_surjective`, `ext_milnorRow_exact`,
  `ext_max_norm_eq`, `ext_pair_injective`.
- **Sketch**: coefficientwise application of T106/T107's row via `MvPowerSeries.map_coeff`;
  constants 1 (decay bookkeeping trivial).

### [T502] pushed spans + ideal-row surjectivity
- **Status**: **DONE** (`span_pushed_B/C/D` via Ideal.map; NEW arity-m ball lemmas in
  NoetherianVertices: `isNoetherianRing_unitBall_restricted_L` (transfer chain at arity m)
  and `isNoetherianRing_unitBall_restricted_dualNumber` (ε-polynomial ball surjection) —
  these discharge `hE₀P` at the vertices; `ideal_row_surjective` := `exists_d1_lift` at the
  𝓓-vertex (tD-bundle) + coefficientwise `extRhoC_strict_surjective` sections +
  ultrametric sum bound, constant `h·(1 + ∑‖rC i‖)`.) | **Type**: proofs (L4.2–L4.3 part)
- **Sorries**: `span_pushed_B/C/D`, `ideal_row_surjective`.
- **Sketch**: span push through ring homs; surjectivity: `exists_d1_lift` at 𝓓 →
  coefficientwise lift through `extRhoC` (T501) → `d_{1,C}` image ([FJP] (4.11) chase,
  constants recorded at L4.3).

### [T503] the controlled pullback and closedness of `I_𝓐`
- **Status**: **DONE** (the (4.12)–(4.16) d₂-correction in full: controlled d1-lifts at B/C, the defect w ∈ ker d1(rD), exists_d2_lift at 𝓓, coefficientwise ρC-sections of the wedge, corrected generator v' = v + d2(rC)s', per-component ext_milnorRow_exact pullback, ultrametric norm bookkeeping with constant 1 + Bs·CrA; isClosed_IA from the controlled pullback + Wedhorn-closedness of IB/IC + Lipschitz continuity of the ext-maps + pair injectivity.) | OLD: | **Depends**: T502 | **Type**: proofs (L4.4–L4.5) — the §4 heart
- **Sorries**: `ideal_pullback_controlled`, `isClosed_IA`.
- **Sketch**: the (4.12)–(4.16) chase, exactly as in the paper (independently re-derived
  twice — L4.3/L4.4 logs): representatives via `exists_d1_lift` at 𝓑, 𝓒; mismatch is a
  𝓓-syzygy; correct with `exists_d2_lift` + pair-lift (T501 on `Pairs`-tuples); recombine
  via `ext_milnorRow_exact`; closedness: preimage of closed matching set under the T501
  embedding.

### [CLEANUP-11] /cleanup `FiniteJetStrictLocalization.lean` — **Depends**: T503.

### [T504] quotient row, algebraic part
- **Status**: **DONE** (loc-maps as Ideal.Quotient.lift over the ideal pushforwards; mk-lemmas rfl; square/pair-injectivity/row-exactness via the controlled pullback and defect absorption) | OLD: | **Depends**: T503 | **Type**: proofs (L4.6–L4.7)
- **Sorries**: `quotient_row_exact`, `locJB/locIotaC/locRhoB/locRhoC` (defs via
  `Ideal.Quotient.lift`), `_mk` lemmas, `loc_square_commutes`, `loc_row_exact`,
  `loc_pair_injective`, `locRhoC_surjective`.
- **Sketch**: lifts exist since `ext*` map ideals into ideals (definition of `rB/rC/rD`);
  3×3 chase per L4.6 with `hHsurj` = T502.

### [T505] quotient row, topological part (Prop 4.5 complete)
- **Status**: **DONE** (Lemma 4.4 executed: 1-Lipschitz quotient projections; `loc_norm_le` — the quantitative pullback estimate via norm_mk_lt representatives, defect absorption, ext_milnorRow_exact with constants 1, and pair injectivity; `loc_pair_isEmbedding` via AntilipschitzWith.isEmbedding; locRhoC continuous open surjection (constant-1 sections make extRhoC open; quotient mk-maps open via norm_mk_lt); locA_t2 (closed ideal ⟹ normed quotient); locA_completeSpace (Banach quotient, rightUniformSpace aligned). ALL of FiniteJetStrictLocalization sorry-free — milestone M4 COMPLETE, axiom-clean (verified via oleans).) | OLD: | **Depends**: T504 | **Type**: proofs (L4.8)
- **Sorries**: `loc_pair_isEmbedding`, `locRhoC_isOpenMap`, `locA_t2`, `locA_completeSpace`.
- **Sketch**: group-quotient maps open; embedding: inducing via the quotient-of-embedding
  diagram + closedness (T503); T2 from closed ideal; completeness of normed-group quotient
  by closed subgroup (mathlib quotient norm instances) transported to the ring quotient.

### [CLEANUP-12] /cleanup `FiniteJetStrictLocalization.lean` (final) — **Depends**: T505.

### [T601] `FiniteJetFunctoriality.lean` — pods and datum pushes — **DONE 2026-07-17**
- **Status**: done (beastmode). `podA/B/C/D := unitBallPod (tX) …` (generic pod from T109's
  `unitBallPod`; no bespoke isAdic needed). `pushDatumB/C/D` `hopen` := `genPiece_hopen`
  (T-image, s-image) fed by new helper `span_image_eq_top` (`Ideal.map_span` + `map_top`);
  `pushDatum*_isRational` := `isRational_of_span_eq_top ∘ span_image_eq_top`. Also
  discharged T606's data early: `interDatum` `hopen` via `span_mul_image_eq_top`
  (`Finset.coe_image`/`coe_product` + `Set.image_mul_prod` + `Ideal.span_mul_span'`) and
  `interDatum_isRational`. File compiles green (~11 s), remaining sorries are T602–T606.
- **Signature completions (recorded)**: `pushDatumB/C/D` take `(hD : D.IsRational)` (needed
  to discharge `hopen`); cascade threaded through `presheafValueMapB/C/D` (+continuity,
  +canonicalMap-compat, +restriction), `mem_rationalOpen_pushDatum*_iff`,
  `pushCoveringB/C/D (hC : C.IsRational)` (covers via `C.covers.attach.image` +
  `IsRational.piece`), `interDatum (h₁ h₂)`.
- **Gotcha (norm-tower defeq storm)**: at `JetA` the ambient `DecidableEq` for
  `Finset.image` is `Subtype.instDecidableEq` (JetA is reducibly a subring-subtype), NOT
  `Classical.decEq`; a generic image-lemma without a `[DecidableEq A]` binder bakes in
  `Classical.decEq`, and unifying the two unfolds the whole jet/norm tower (>4M heartbeats,
  diverges). Fix: put `[DecidableEq A]` binders on generic `Finset.image` span lemmas so
  the use site synthesizes the ambient instance. Type: def-completion + proofs (L5.1–L5.2).

### [T602] covariant presheaf-value maps — **DONE 2026-07-17**
- **Status**: done (beastmode). Built a **generic covariant layer** (section
  `CovariantPush`, no PlusSubring needed): `locMapOfHom φ D D' (hs : D'.s = φ D.s)` via
  `IsLocalization.map` (powers-comap inclusion), `locMapOfHom_algebraMap`
  (`IsLocalization.map_eq`), `locMapOfHom_divByS` (`map_mk'` + `Subtype.ext`),
  `locMapOfHom_continuous` via `locTopology_continuous_lift` — hf_alg from naturality +
  inlined `algebraMap`-continuity basis proof, hpow FREE since pushed generators land in
  `locSubring D'` (`divByS_mem_locSubring` + `locSubring_isBounded_of_pair`; no
  Nullstellensatz/`HasLocLiftPowerBounded` input, unlike restriction maps); `pushMapAlg` =
  `coeRingHom ∘ locMapOfHom`; `presheafValueMapOfHom` via
  `UniformSpace.Completion.extensionHom` (restrictionMapHom letI-plumbing mirrored);
  `_continuous` (`Completion.continuous_extension`), `_coe` (`extensionHom_coe`),
  `_canonicalMap`. Instantiated: `presheafValueMapB/C/D` (+`continuous_jB/iotaC/rhoC` via
  `AddMonoidHomClass.continuous_of_bound` from the norm bounds), continuity ×2,
  canonicalMap-compat ×2 — all one-liners. File green, 19 sorries remain (T603–T606).
- **Gotchas**: (i) `algebraMap_continuous_loc` carries a `[NonarchimedeanRing A]` section
  variable — inline its 10-line basis proof instead of adding the instance; (ii) anonymous
  `Submonoid.powers` witness needs `by show D'.s ^ 1 = φ D.s` (unreduced beta blocks
  `rw [pow_one]`); (iii) `IsLocalization.map_eq` as a term gets TC-stuck on metas — use
  `unfold locMapOfHom; rw [IsLocalization.map_eq]`.

### [T603] **KEYSTONE**: the graph bridge for 𝓐 — **DONE 2026-07-17**
- **Status**: done (beastmode). `graphBridgeA : 𝒪_𝓐(D) ≃+* 𝓐_α` with continuity BOTH ways,
  plus the real `graphBridge_natural_C` (True-stub replaced per L5.4 attack 3 — recorded
  statement fix): `bridgeFwdC ∘ presheafValueMapC = locIotaC ∘ graphBridgeA`.
  **Forward**: `bridgeBase = mk ∘ polyToP ∘ C`; graph relation `s̄·X̄ᵢ = f̄ᵢ` via
  `Ideal.Quotient.eq`; `s̄` unit from the span decomposition (`mem_span_singleton'` +
  `Ideal.mem_span_range_iff_exists_fun`, `Finset.mul_sum` calc); `IsLocalization.Away.lift`;
  continuity via `locTopology_continuous_lift` (base 1-Lipschitz via
  `AddMonoidHomClass.continuous_of_bound` + `gaussNorm_C_norm`; generators ↦ `X̄ᵢ` of norm
  ≤ 1 (`gaussNorm_X_le_one`) hence power-bounded via new `isPowerBounded_of_norm_le_one`);
  `Completion.extensionHom` into `locA` (complete+T2 from `isClosed_IA` +
  `Submodule.Quotient.normedAddCommGroup`). **Reverse**: `bridgeToRestricted` (norm-decay ⇒
  topological decay), `bridgeEval` on `mvEvalHomBounded` at the power-bounded `fᵢ/s` tuple
  (`coeRingHom_image_locSubring_isBounded`); kills `I_𝓐` (term-mode `map_sub`/`congrArg₂`
  chain + `mk'_spec`); `Ideal.Quotient.lift`. **Continuity of rev**: fresh Gauss-ball-basis
  mirror of `mvEvalHomBounded_continuous` (coefficient norms ≤ series norm via
  `norm_coeff_le_gauss`) + `QuotientRing.isOpenQuotientMap_mk`. **Round trips**:
  `polyToP_denseRange` (new: truncation below any coefficient level via
  `finite_setOf_le_norm_coeff`); rev∘fwd by `IsLocalization.ringHom_ext` + dense equalizer;
  fwd∘rev by `MvPolynomial.ringHom_ext` (C/X agreement) + polynomial density + T2.
  **Naturality**: C-side forward bridge re-instantiated at `locC` (same A-side `(D.s, e.f)`
  parameters; `rC_eq` gives the C-graph polynomials; `span_pushed_C` for the unit;
  `isClosed_graphIdeal` + `isNoetherianRing_PC` for closedness), then
  `IsLocalization.ringHom_ext` + `denseRange_coe` equalizer through `locIotaC_mk` +
  `mapRestricted_polyToP` + `MvPolynomial.map_C`.
- **New reusable infra**: `instIsUltrametricDistIdealQuotient` (quotients of ultrametric
  seminormed rings are ultrametric, via `norm_mk_lt` ε-representatives),
  `instNonarchimedeanRingOfSeminormedUltra`, `isPowerBounded_of_norm_le_one`,
  `gaussNorm_X_le_one`, `polyToP_denseRange`, `mkIA_continuous`, local copies of the
  private Wedhorn828 helpers (`tsum_mem_of_isOpen_addSubgroup'`, range-product bounded).
- **Gotchas**: instance-path storms at `JetA`/`PA` for `Sub`/`Mul`/`Module` — never rw with
  generic `map_*` INTO applications (use term-mode `map_sub ... |>.trans (congrArg₂ ...)`
  or `RingHom.map_*` with explicit hom); `AddMonoidHomClass.continuous_of_bound` avoids all
  dist/sub rewriting for 1-Lipschitz homs; `haveI : NormedAddCommGroup (quotient)` SHADOWS
  the seminormed norm — hoist metric lemmas (e.g. `mkIA_continuous`) OUTSIDE such scopes;
  `open X in` goes BEFORE the docstring; `synthInstance.maxHeartbeats 400000` needed where
  T2/metric instances synthesize through the quotient tower. | **Depends**: T505, T602 |
  **Type**: def-completion + proofs (L5.4)
- **Sorries**: `graphBridgeA` (data), `graphBridgeA_continuous`, `_symm_continuous`; ALSO
  replace the stub `graphBridge_natural_C : True` with the real statement (bridge ∘
  `presheafValueMapC` = `locIotaC`-side map ∘ bridge) — statement fixed in L5.4 attack 3.
- **Sketch**: forward: `s` invertible in `locA` ((4.3) computation from span-⊤);
  `IsLocalization.Away.lift`; continuity (lattice: `locSubring` generators `tᵢ/s ↦ T̄ᵢ`,
  norm ≤ 1); extend (`locA` complete Hausdorff by T505). Reverse: evaluation
  `P_𝓐 → presheafValue D`, `Tᵢ ↦ canonicalMap tᵢ · (canonicalMap s)⁻¹` (the D′=D unit is
  free in `Localization.Away` — L5.4 circularity note); Lemma 1.1's convergence bound (1.3)
  for boundedness (referee-verified); kills `I_𝓐`; quotient-factor; round-trips on dense
  images (`Ideal.Quotient.mk`-image dense; localization dense in completion). In-project
  precedent: `TopologyComparison.presheafValueTateQuotientEquiv` (singleton-T) — generalise
  its architecture, replace its hypothesis bundle with our T505 facts.
- **HARD-STOP note**: if the universal-property route stalls, STOP and file the concrete
  blocker — do NOT invent an alternative topology comparison (B2 #6/P3 territory).

### [CLEANUP-13] /cleanup `FiniteJetFunctoriality.lean` — **Depends**: T603.

### [T604] loc-lift instances — **DONE 2026-07-17**
- **Status**: done (beastmode). `HasLocLiftPowerBounded (JetB/C/D)` are one-line
  `hasLocLiftPowerBounded_faithful` (all binders were already instances: noetherian
  vertices, IRIE plus rings, right-uniformity completeness, ultra-nonarch, T2).
  **`hasLocLiftPowerBounded_JetA`: the L5.6 componentwise-Milnor plan was NOT needed** —
  the faithful chain's `[IsNoetherianRing A]` was pure threading (its own docstrings said
  "NO noeth-A₀"; the concrete-pair sub-lemmas `presheafValue_ringOfDef/idealOfDef_fg/
  isAdic/topNilUnit` never consume it). De-noetherianized (compiler-verified):
  `presheafValue_concretePair`, `presheafValue_concretePair_A₀`,
  `presheafValue_isTateRing_concrete` (PresheafTateStructure),
  `presheafValue_isAdicComplete` (Cor832), `mem_plus_of_forall_spa_vle_one`,
  `isPowerBounded_of_forall_vle_one_spa_of_complete`, `isUnit_canonicalMap_s_faithful`,
  `locLift_divByS_isPowerBounded_faithful`, `hasLocLiftPowerBounded_faithful`
  (FaithfulLocLift) — hypothesis-weakening only, all callers unaffected, full project
  green (3079-job chain + full `lake build`). JetA (non-noetherian!) then satisfies the
  faithful package directly: `instance hasLocLiftPowerBounded_JetA :=
  hasLocLiftPowerBounded_faithful`. This also future-proofs the LL-package for ℂ_p-style
  bases (the original faithful-design goal). NOTE: the componentwise route would anyway
  have been blocked for non-rational `D'` (the class quantifies over ALL data; bridges
  need span-⊤) — the Spa-route is rationality-free. | **Depends**: T603, T304 |
  **Type**: proofs (L5.5–L5.6)

### [T605] restriction naturality + coverage — **DONE 2026-07-17**
- **Status**: done (beastmode). Coverage: `plus_le_comap_of_norm_le` (𝓐° = unit ball by
  `isPowerBounded_JetA_iff` [new import: FiniteJetUniformDomain], then norm-noninc maps +
  `isPowerBounded_of_norm_le_one` — norms, never bare continuity ✓);
  `mem_rationalOpen_pushDatum B/C/D_iff` (D-side added as supporting lemma) via
  `comap_mem_spa` + `comap_vle`-rfl pushing; `pushCoveringB/C/D` hsubset/hcover by the
  iffs + the base covering's fields through `Finset.attach`; `*_isRational` via
  `pushDatum*_isRational` + `IsRational.piece`. Naturality:
  `restrictionMapHom_canonicalMap'` (local public form of the private coe-lemma via
  `extensionHom_coe` + `Away.lift_eq`), then both squares by
  `IsLocalization.ringHom_ext` on canonical images + `denseRange_coe` equalizer
  (RegularSpace haveI for T2). Gotcha: the D-side hAB lambda needs explicit
  `Subring.mem_comap.mpr` + `show IsPowerBounded` casts (composite-hom metas).
  | **Depends**: T604 | **Type**: proofs (L5.3 rest + L5.7)

### [T606] intersection data — **DONE 2026-07-17**
- **Status**: done (beastmode). **The L5.8 fallback normalisation was REQUIRED**: with the
  bare product `T₁·T₂` the ⊆-direction of the intersection formula is false (nothing
  isolates `v(t₁) ≤ v(s₁)` from products alone); `interDatum.T` redefined (recorded) as
  `(insert s₁ T₁ ×ˢ insert s₂ T₂).image (·*·)` — `R(T/s) = R(T∪{s}/s)` on opens, so the
  normalized datum cuts out exactly the intersection. `rationalOpen_interDatum` proved
  pointwise with the `Spv` methods: `mul_vle_mul_left`, `vle_mul_cancel` (against the
  `(t, s₂)`/`(s₁, t)` pairs), `vle_total` (reflexivity at inserted `s`), `vle_trans`
  (product of inequalities), and `¬vle(s₁s₂)0 → ¬vle sᵢ 0` by `0 = 0·s₂` cancellation —
  no supp-primality needed. `span_insert_eq_top` helper (with the `[DecidableEq]`-binder
  lesson applied — `insert` also synthesizes it ambiently). `interDatum_isRational`
  updated to the normalized span. | **Depends**: T601 | **Type**: proofs (L5.8)

### [CLEANUP-14] /cleanup `FiniteJetFunctoriality.lean` (final) — **Depends**: T605, T606.

### [T701] transfer: separation — **DONE 2026-07-17**
- **Status**: done (beastmode). The L6.1 chase: `z := x - y` has vanishing piece
  restrictions; `presheafValueMapB/C z = 0` by vertex `IsSheafy.separationSub` at the
  pushed coverings (funext over attach-image pieces via the `⟨d, -, rfl⟩` destructuring +
  T605 naturality applied backwards + `hres`); through the base bridge (`datumEnum` — new
  canonical enum via `Finset.equivFin`), `graphBridge_natural_B` (NEW — 𝓑-mirror of the
  𝓒-square, built with the full B-side forward bridge `bridgeFwdB` [@-application of
  `extensionHom` to dodge an fvar-keyed instance-synthesis failure]) + `natural_C` give
  vanishing of both `locJB`/`locIotaC`-images; `loc_pair_injective` + bridge injectivity
  force `z = 0`. Gotchas: transfer file needs `open scoped Classical` (attach-image
  membership) + `open StrictLoc`; `restrictionMap` vs `restrictionMapHom` and
  `(pushCovering).base` vs `pushDatum` need `show`-retyping before rewrites (defeq,
  not syntactic); `RingHom.map_sub` only as a term-have. | **Type**: proofs (L6.1)

### [T702] transfer: gluing — **the sheafiness workhorse** — **DONE 2026-07-17**
- **Status**: done (beastmode). `gluing_JetA` proven along the recorded architecture:
  `restrictionMap_cast` (the ▸-elimination identity, `subst`-provable with free target),
  choice-based `gB/gC` with `hgBres/hgCres` (cast-elimination + `restrictionMap_comp`),
  `pushedCompatB/C` (arbitrary vertex `D₃` through the pushed intersection),
  hoisted `hgBd/hgCd` piece-value identities (self-restriction + `restrictionMap_id` +
  pushedCompat at the canonical element), vertex `IsSheafy.gluing`, 𝓓-matching by
  `IsSheafy.separationSub (JetD)` + generic `presheafValueMapOfHom_restriction` at ρB/ρC +
  `mapBD_mapB_eq_mapCD_mapC`, loc-transport (`locRhoB/C_bridgeFwdB/C` squares →
  `loc_row_exact` → `x := (graphBridgeA).symm w`), `bridgeFwdB/C_injective` recover
  `mapB x = bB`, `mapC x = bC`; piece-identification by `pairMapBC_injective` (L6.1 core
  at one datum). `maxHeartbeats 6400000` on the theorem (one heavy naturality-rw; 53 s
  file). Gotchas: inline `dI`-lets break rw-motives (dependent `hIrat`); congr_fun-results
  must be ASCRIBED to their comp-applied-reduced forms (never `simp [RingHom.comp_apply]`
  on completion-typed haves); `id_eq`-cleanup after `restrictionMap_id`-rewrites; beware
  python-patch collisions when a hoisted block contains the replaced substring.
- (prior progress note follows) DONE so far: `pushDatumB/C_interOpen`
  (pushed opens of `interDatum` = intersections, via the T605 iffs +
  `rationalOpen_interDatum`) — in FiniteJetSheafTransfer, green.
- **ARCHITECTURE (verified by dependency-chase, follow this)**: (1) pushed families `gB/gC`
  on `(pushCoveringB/C C hC).covers` defined via `(Finset.mem_image.mp D'.2).choose` +
  `choose_spec.2 ▸` transport; in proofs destructure `⟨DD, hDD⟩`, name
  `b := (mem_image.mp hDD).choose`, `subst` its spec-eq — the `▸` then REDUCES
  (definitional proof irrelevance), no cast-juggling. (2) `pushedCompatB/C` (arbitrary
  vertex `D₃` ⊆ two pushed pieces): A-compat at `D₃ₐ := interDatum d₁ d₂` + T605
  naturality (congrArg `mapB-inter`) + `pushDatum*_interOpen` to see `D₃ ⊆ pushed-inter`,
  then `restrictionMap_comp` (containment proofs are definitionally irrelevant). (3)
  vertex `IsSheafy.gluing` → `bB, bC`. (4) **𝓓-matching + Milnor transport REQUIRE
  `bridgeFwdB/C` to be isomorphisms** — MIRROR THE A-SIDE REVERSE BLOCK at 𝓑 and 𝓒
  (bridgeToRestrictedB/C [generic decay proof], bridgeGenB/C [divByS of jB/ι-images at
  the pushed datum ∈ locSubring], bridgeEvalB/C via `mvEvalHomBounded`, kills `IB/IC`
  via `rB_eq/rC_eq`, `bridgeRevB/C`, roundtrips via `polyToP_denseRange`-mirror; ~250
  lines each — NO shortcut exists: every injectivity-free route loops back to the
  conclusion). Also `mapBD := presheafValueMapOfHom (rhoB F)` (generic layer!) for the
  𝓓-compat of `(bB, bC)`, using `square_commutes` + `Finset.image_image` to identify
  `pushDatumD` with the `ρB`-push of `pushDatumB`. (5) `w := loc_row_exact`-witness;
  `x := bridgeRevA w`; `mapB x = bB` via fwdB-injectivity (from the iso) + roundtrip
  `locJB w = fwdB bB`. (6) piece-identification: piece-level pair-injectivity (T701's
  z-argument specialized to one piece) + `restrict-pushed(mapB x) = restrict-pushed bB`
  from (5) + `hbB`. | **Depends**: T701 | **Type**: proofs (L6.2)

### [T703] transfer: embedding — **DONE 2026-07-17**
- **Status**: done (beastmode). Verbatim 828b-assembly mirror at 𝓐 (all ingredients
  noetherian-free): A-linear `rho` with `productRestriction_comp_canonicalMap` smul-field,
  `range = sectionEqualizer` (⊆ generic; ⊇ = T702 gluing), `sectionEqualizer_isClosed`,
  countably-generated uniformities + `ContinuousSMul` haveIs, Tate unit ϖ, and the
  σ-compact-free `isInducing_of_closedRange_of_topNilpUnit` with the two explicit module
  instances; injectivity = T701. `maxHeartbeats 1600000` (lake-build default differs from
  `lake env lean` — always confirm with `lake build`). | **Type**: proofs (L6.3)

### [CLEANUP-ALL-1] /cleanup-all — **Depends**: T703 (pre-milestone).

### [T704] ★ MILESTONE: `finiteJet_isSheafy` axiom-clean — **DONE 2026-07-17** ★★★
- **Status**: **COMPLETE**. `#print axioms FiniteJet.finiteJet_isSheafy` (and
  `isSheafy_JetA`) → `[propext, Classical.choice, Quot.sound]` — NO sorryAx, checked
  against built oleans; full `lake build` green (3082 jobs). **THE CAMPAIGN'S PRIORITY
  THEOREM IS PROVEN: 𝓐 is sheafy** ([FJP] Theorem 5.3), joining the already-complete
  headline trio (uniform, domain, non-noetherian at 𝓐; 𝓑 non-uniform). The CLEANUP-*
  dependency is process-only (cleanup fleet); the mathematics is done and verified.

### [T801] chart datum — **DONE 2026-07-17**
- **Status**: done (beastmode). `Wa` membership via `mem_jetSupport_iff_jet_in_range` +
  `rhoC_sectionD` + the nonneg-support witness `⟨nonnegEquiv.symm ⟨Wu.val, coeff_single⟩⟩`
  (snd-component `ofRestricted 0 = 0`); `hopen := genPiece_hopen` +
  `Ideal.eq_top_of_isUnit_mem` at the `tA`-unit ∈ {Wa, tA}; `chartDatum_isRational`
  likewise (needs a `show`-unfold of the structure `.T` before `Finset.coe_insert`).

### [T802] Prop 3.1: the chart is 𝓑 — **DONE 2026-07-17**
- **Completed** steps 4–7 (2026-07-17): `chartRev_theta` (rev∘θ = ρ via `jet_decomposition` +
  `canonicalMap_eq_zero_of_qSq` + `evalRescale_eq`; helpers `chartRev_inl`, `chartRev_inr_one`,
  `jB_constNN`, `theta_constNN`, `constKW_nonnegEquiv_symm`, `theta_Qa`); Roundtrip I
  `chartRev_chartFwd` (IsLocalization.ringHom_ext (powers ϖ) + completion-dense equalizer);
  `jB_constKW`/`theta_constKW`; Roundtrip II `chartFwd_chartEval` (fwd∘ev = inl, polynomial
  density, C-case via θ-on-constants + `rescaleRestricted_const`, X-case via
  `chartLocHom_divByS_Wa`) and `chartFwd_chartRev` (inl/inr reassembly); `chartRev_continuous`
  (fst/snd 1-bounded for the jet sup-norm + `chartEval_continuous`); `chartEquiv` via
  `RingEquiv.ofRingHom`; both continuities definitial.
- **Statement completions (recorded per protocol)**: `chartEquiv` skeleton `def` →
  `noncomputable def` (chartFwd is a completion extension); `chartEquiv_canonicalMap_W`
  `True`-stub → real pinning `chartEquiv (ρ W) = tB·jB(W) ∧ chartEquiv (ρ Q) = ε`.
- Original ticket text follows.

### [T802-orig] (historical)
- **Status**: IN PROGRESS — DONE: twist (`rescaleRestricted` + `twistB` + `thetaChart`),
  `jB_tA/thetaChart_tA/thetaChart_Wa` jet computations, FULL forward (`chartLocHom` with
  generator identities + continuity + `chartFwd` extension), `Qa`, collapse data
  (`Wa_val_eq`, `yQ`, `Wa_pow_mul_yQ`, `norm_yQ_le`), **the (3.3) limit
  `canonicalMap_Qa_sq : ρ(Q)² = 0`**, `kwToTate` reindexing bridge, `gChart_isBounded`,
  `chartConst(+cont)`, `chartEval` (via `TateAlgebraWedhorn.evalHomBounded`), and
  **`chartRev` ring hom** (mul-field by `linear_combination (-(ev x₂ ev y₂)) * Q̄²-collapse`).
- **REMAINING (roundtrips fully de-risked, follow this)**: (1) GENERALIZE
  `canonicalMap_Qa_sq` to `ρ(y) = 0` for ANY `y ∈ 𝓐` with `qCoeff 0/1 = 0` (same proof,
  `yQ`-family at `y`; norms via `‖y‖`). (2) 2-jet decomposition: `sectionD(b₀,b₁) =
  constHomC b₀ + Qa·constHomC b₁` (coeff-check ∀n) ⇒ every `a ∈ 𝓐` is
  `constNN b₀ + Qa·constNN b₁ + (Q²-part)` where `constNN b := ⟨constHomC b, mem⟩`.
  (3) key identity `chartEval (rescaleRestricted t _ f) = ρ (constNN (ofRestricted f))`-ish:
  two continuous K-homs KW → 𝒪(chart) agreeing on `C r` (both `ρ(constA r)`) and on `X`
  (LHS `ev(tX) = ρ(tA)·gChart = ρ(Wa)` by the `hWsplit`-identity from the collapse proof;
  RHS `ρ(Wa)`) + K[X]-density in KW (1-var `polyToP_denseRange`-mirror) + T2. (4)
  `chartRev (thetaChart a) = ρ a` from (1)+(2)+(3) + `θ(Qa) = ε`, `rev(ε) = Q̄`. (5)
  rev∘fwd = id via `ringHom_ext` (powers tA) + density; fwd∘rev = id via KW-poly+ε
  density on `JetB` (fwd(rev(inl f)) = fwd(ev f)-agreement on C/X + fwd(Q̄) = θ(Qa) = ε).
  (6) assemble `chartEquiv`; continuities (fwd ✓; rev: `evalHomBounded`-continuity
  [`TateAlgebraWedhorn`, grep exact name] + component-sums). (7) pinning stub :=
  `chartEquiv ((chartDatum F).canonicalMap (Wa F)) = tB F * jB F (Wa F)` proven by
  `chartFwd_coe` + `chartLocHom_algebraMap` + `thetaChart_Wa`. Then T803 closes, T804
  sweeps. **Prior plan follows.** — in the
  project model `‖W_B‖ = 1` (radius-1 `PowerSeries.Restricted`), so the naive evaluation
  does NOT kill the graph relation — Prop 3.1's `W ↦ ϖX` is implemented by the TWISTED
  base map `θ := (rescale-by-ϖ on both TrivSqZeroExt components) ∘ jB : JetA →+* JetB`
  (the substitution X ↦ ϖX = mathlib `PowerSeries.rescale`; Restricted-version needed —
  decay preserved since `‖ϖ‖ ≤ 1`; θ is norm-≤ hence continuous). **Forward**: `tB` IS a
  unit of `JetB` (constant Laurent scalar — `isUnit_tB` exists!), so
  `IsLocalization.Away.lift (tA) (hu : IsUnit (θ tA) = IsUnit tB)`;
  `locTopology_continuous_lift`: generators `Wa/t ↦ θ(Wa)/tB = (tB·W_B)/tB = W_B` (norm 1,
  pb ✓) and `t/t ↦ 1`; `extensionHom` (JetB complete T2 ✓). θ(Wa) = tB·W_B is the key jet
  computation: `jB (Wa) = W_B` (the norm-1 generator) then rescale. **Reverse**: for
  `(f, g) : JetB = DualNumber K⟨X⟩`: `rev (f,g) := ev f + ev g · Q̄` with `ev : K⟨X⟩ →
  𝒪(chart)` := single-variable `evalHomBounded` (Wedhorn828 predecessor of mvEval) at the
  base `canonicalMap ∘ constA : K → 𝒪(chart)` and `X ↦ coeRingHom (divByS (Wa) (tA))`
  (pb ✓ locSubring), `Q̄ := canonicalMap Qa` (Qa : JetA the (0,1)-support element, build
  like Wa); ring-hom fields need `Q̄² = 0` in 𝒪(chart) — the (3.3)-collapse:
  `Q̄² = canonicalMap (Qa²)` … `Qa² ∈ Q²𝓒`-part; use the referee factorisation
  `y − ϖⁿXⁿ(W⁻ⁿy) = (Wⁿ − (ϖX)ⁿ)(W⁻ⁿy)` at the localization level: in
  `Localization.Away tA`, `Qa·Qa = (Wa/tA)ⁿ·tAⁿ·(W⁻ⁿ·Qa²)`-chain gives
  `‖coe(Qa²-image)‖ → 0`, i.e. `canonicalMap (Qa²) = 0` by T0-separation (limit of a
  null sequence in the completion). Round trips by density (localization dense; K⟨X⟩[Q]
  polynomials dense) exactly as T603. | **Depends**: T801, T603 | **Type**:
  def-completion + proofs (R4)
- **Sorries**: `chartEquiv` (data), continuity ×2; replace stub
  `chartEquiv_canonicalMap_W : True` with the real pinning statement
  (`chartEquiv (canonicalMap (Wa)) = tK • X`-form — fix statement per R4).
- **Sketch**: through `graphBridgeA` at `chartDatum` (m = 2 enumeration {W, t}) OR directly
  by the paper's two-map argument: `Q²`-collapse via the factorisation
  `y − ϖⁿXⁿ(W⁻ⁿy) = (Wⁿ − (ϖX)ⁿ)(W⁻ⁿy)` (R4 quote); `ψ` bounded multiplicative (planner-
  verified jet computation); `φ` from power-boundedness of X, Q and `Q̄² = 0`; dense
  round-trips. The graph-bridge route is preferred (reuses T603); the direct route is the
  recorded fallback.

### [T803] Cor 3.2: not stably uniform — **DONE 2026-07-17** (T802 landed; `not_isUniform_chart` + `not_isStablyUniform_JetA` sorry-free)
- **Status**: `isPowerBounded_map_of_ringEquiv` + `isUniform_of_ringEquiv` PROVEN
  (bi-continuous transport; beta-`show` before final rws); `not_isUniform_chart` and
  `not_isStablyUniform_JetA` fully wired — they compile and will be sorry-free the moment
  T802's `chartEquiv` (+2 continuities) lands. Only T802 remains on the whole board's
  mathematical spine.

### [CLEANUP-15] /cleanup `FiniteJetChart.lean` (final) — **Depends**: T803.

### [T804] MILESTONE: headline assembly verification — **DONE 2026-07-17**
- All five `FiniteJetMain` theorems `#print axioms` = `[propext, Classical.choice, Quot.sound]`
  (user directive: all of FiniteJetMain axiom-clean — SATISFIED). Root target builds green.
- Original ticket text follows.

### [T804-orig] (historical)
- **Status**: open | **Depends**: T704, CLEANUP-6, CLEANUP-15
- **Deliverable**: `lean_verify` all five `FiniteJet.finiteJet_*` theorems axiom-clean;
  update board banner; PR-readiness note for `dev/adic-spaces → main`.

### [CLEANUP-FINAL] /cleanup-all — **Depends**: T804. Last item before any M7 planning.

---

## M8 — `HasLocLiftPowerBounded` at FULL HUBER generality (opened 2026-07-17)

Owner directive: prove Wedhorn Prop 7.52's consequences (the two `HasLocLiftPowerBounded`
fields) for general complete f-adic/Huber rings, removing `[IsTateRing A]` from the
faithful LL chain. Plan artifact: `decomposition-m8-huber-loclift.md` (verbatim source
quotes per leaf, adversarial logs, gate PASSED; skeleton compiled green 2026-07-17).
Sources: `references/wedhorn.txt` (8.1/8.2 at 3660-3760, 7.51-7.52 at 3457-3495),
`references/huber2.txt` ([Hu2] §2-§3: 2.4 at 432-438, 2.5 at 454-460, 3.1 at 585-604,
3.3(i) at 624-658). Tate enters the current chain at EXACTLY two points (audit in the
decomposition file): the `IsHuberRing (presheafValue D')` supply, and the principal-pair
continuity engine + `restrictIdealSingle` in the [Hu2] 3.3(i) witness.

### [T901] Support layer de-Tate (concretePair, isHuberRing, isAdicComplete)
- **Status**: done (2026-07-17) — **File**: PresheafTateStructure.lean, Cor832.lean — **Depends**: none — **Type**: relax + lemma
- **Progress**: (a) dropped `[IsTateRing A]` from `presheafValue_concretePair` — the five ingredients are Tate-free; `presheafValue_concretePair_eq`'s `rfl` still holds. (b) `presheafValue_isHuberRing_huber := ⟨⟨presheafValue_concretePair D₀⟩⟩` (IsHuberRing = Nonempty pair + IsTopologicalRing, instance-available). (c) dropped `[IsTateRing A]` from `presheafValue_isAdicComplete` (kept `[T2Space A]`; body used no Tate/π). All three `#print axioms` = `[propext, Classical.choice, Quot.sound]`; PresheafTateStructure + Cor832 + FaithfulLocLift build error-free.
- (a) Drop `[IsTateRing A]` from `presheafValue_concretePair` (its five ingredients are
  already Tate-free; binder is vestigial — compiler-verified relaxation, T604 pattern).
- (b) Fill `presheafValue_isHuberRing_huber` (skeleton in PresheafTateStructure.lean tail):
  `⟨⟨presheafValue_concretePair D₀⟩⟩` after (a); `IsHuberRing` = `Nonempty (PairOfDefinition ·)`
  + `IsTopologicalRing` (instance available on the completion) per HuberRings.lean:71.
- (c) Drop `[IsTateRing A]` from `presheafValue_isAdicComplete` (Cor832.lean:1556; proof
  body greps clean of Tate/π — verify by compiler; keep `[T2Space A]` only if consumed).
- **Sources**: Wedhorn 8.1 construction (wedhorn.txt:3673-3675: "The pair (D, I·D) is a
  pair of definition of A(T/s)").
- **Generality**: general `[IsHuberRing A]` base; no new hypotheses.

### [T902] `restrictIdeal` value-transfer trio (general I)
- **Status**: done (2026-07-17) — **File**: SpvAITopology.lean — **Depends**: none — **Type**: lemma ×3
- **Progress**: `restrictIdeal_le_one`/`_one_lt`/`_lt_one` filled, mirroring the
  `restrictIdealSingle` trio case-for-case via `restrictIdeal_apply_of_mem`/`_of_not_mem`/
  `_apply_zero` + `vUnit_mem_cGammaIdeal`. All three axiom-clean. (General API; kept for
  reuse though the critical-path witness in T906 uses `restrictIdealSingle 1` instead.)

### [T903] Characteristic restriction: microbial + `IsInSpvAI` — **DONE 2026-07-17**
- **Status**: done (2026-07-17) — **File**: SpvAITopology.lean — **Depends**: none — **Type**: lemma ×2
- **Progress**: REFINED the encoding from `restrictIdeal ⊥` to `restrictIdealSingle w 1`
  (= Huber's `u|cΓ_u`, since `(w 1)⁻¹ = 1 ∈ cΓ_w` gives `cGammaSingle w 1 = cΓ_w`). This
  reuses the PROVEN `restrictIdealSingle_isMicrobial_of_mem` + the existing
  `restrictIdealSingle_le_one/_lt_one/_one_lt` (no new trio needed on the critical path).
  Filled `restrictIdealSingle_one_isMicrobial` (2-line: `mk0 (w 1) hg = 1`, `1 ∈ cΓ_w`) and
  `ofValuation_restrictIdealSingle_one_isInSpvAI` (`Or.inr` microbial disjunct, I-independent).
  Both axiom-clean. Prior-B2 (2026-06-22) respected: microbiality is at the characteristic
  subgroup only, not a general-I restriction claim.

### [T904] A°°-form decay: `cofinalValue_ideal_pow_lt_of_le_one_on_ideal` — **DONE 2026-07-17**
- **Progress**: proven via TWO new general lemmas (better than planned — reusable at bare
  `Valuation` level, no PairOfDefinition needed): `pow_gen_prod_lt` (pigeonhole decay on
  pure generator-products, function-form `∀ f : Fin m → ↥S` avoiding Finset-pow in the
  statement) + `exists_pow_lt_of_forall_le_one_cofinal` (head-absorption: `c_p·p =
  (c_p·s₀)·(tail)`, `c_p·s₀ ∈ I`, tail bound by pigeonhole; `Valuation.map_sum_lt` closes).
  `cofinalValue_ideal_pow_lt_of_le_one_on_ideal` is a 3-line instantiation at
  `v.comap P.A₀.subtype`. All axiom-clean.
- **Status**: done (2026-07-17) — **File**: SpvAI.lean (skeleton at tail) — **Depends**: none — **Type**: lemma
- Coefficient-free route (decomposition L3.1): helper claim
  `∀ a ∈ (span S)·J, v a ≤ (max_{c∈S} v c) · (bound J)` by `Submodule.mul_induction_on`
  (no scalar case) + `∀ z ∈ J`-strengthened `span_induction` on the left factor whose
  smul-case reassociates `(r • y)·z = y·(r • z)`; iterate from J := P.I (base h_le_one);
  then `M := max_S v` is attained (S finite) and `CofinalValue v c*` gives `Mⁿ < γ`.
  Edge: `S = ∅` → `I^n = ⊥` → `v 0 = 0 < γ`.
- **Mathlib**: `Submodule.mul_induction_on`, `Submodule.span_induction`,
  `Finset.exists_mem_eq_sup'` (max attained), `pow_lt` bookkeeping as in
  `cofinalValue_ideal_pow_lt` (SpvAI.lean:100, the A₀-form analogue, ~165 lines).
- **Sources**: Huber 3.1 decay (huber2.txt:598-604), Lemma 2.4 max-generator (432-438).
- **Generality**: hypothesis only `≤ 1` on P.I (weaker than strict; decay from Mⁿ).

### [T905] A°°-form engine: `Spv.isContinuous_of_isInSpvAI_of_lt_one_AOO` — **DONE 2026-07-17**
- **Progress**: assembled exactly as planned — `Valuation.isContinuous_of_ideal_pow_lt` +
  T904 decay (`h_le_one` on P.I from `h_lt_one·.le`) + cofinal/microbial dispatch with the
  A₀-engine's microbial branch verbatim. CONFIRMED: `h_le_AOO` is NOT consumed by the
  proof (kept in the signature for Huber-Thm-3.1 statement parity; droppable by the
  cleanup fleet if desired). Axiom-clean.
- **Status**: done (2026-07-17) — **File**: SpvAI.lean (skeleton at tail) — **Depends**: T904 — **Type**: lemma
- Assembly mirrors `isContinuous_of_isInSpvAI_of_lt_one` (SpvAI.lean:332): reduce via
  `Valuation.isContinuous_of_ideal_pow_lt` to the T904 decay; per-generator cofinality
  from the `IsInSpvAI` disjuncts — cofinal branch direct, microbial branch = the existing
  argument at SpvAI.lean:360-414 verbatim (consumes only `h_lt_one` +
  `PairOfDefinition.exists_pow_mul_mem_A₀` — verified).
- Note: `h_le_AOO` may be droppable (T904 needs only P.I-bounds); attempt without it and
  record; keeping it is sound.
- **Sources**: [Hu2] Thm 3.1 reverse (huber2.txt:586-604).

### [CLEANUP-M8-1] /cleanup SpvAI.lean + SpvAITopology.lean — **Depends**: T905.

### [T906] General witness: `mem_plus_of_forall_spa_vle_one_huber` (+ PB wrapper) — **DONE 2026-07-17**
- **Progress**: Tate body transformed exactly per plan — HU-a…d verbatim; witness
  `rs := (t.comap algB).restrictIdealSingle 1 hW1` (characteristic restriction); continuity
  via the T905 AOO-engine at `presheafValue_concretePair D'` with `h_in` from T903's
  I-independent microbiality; B⁺-bound and `w(x) > 1` via the Single transfer trio at `1`.
  PB wrapper one-liner. Compiled first try; axiom-clean.
- **Status**: done (2026-07-17) — **File**: FaithfulLocLift.lean (skeleton at tail) — **Depends**: T901, T903, T905, CLEANUP-M8-1 — **Type**: theorem ×2
- De-Tate the [Hu2] 3.3(i) witness (decomposition L4): keep HU-a…d blocks verbatim (all
  Tate-free); replace lines-454-530's Tate-pair machinery with:
  `rs := (t.comap algB).restrictIdeal ⊥`; Spa-membership: continuity via T905 at
  `P := presheafValue_concretePair D'` (`h_in` := T903's IsInSpvAI; `h_le_AOO` :=
  `hW_lt_AOO ·.le` + T902 transfer; `h_lt_one` :=
  `P.isTopologicallyNilpotent_of_mem` → `hW_lt_AOO` → `restrictIdeal_lt_one`), B⁺-bound
  via `hW_le` + `restrictIdeal_le_one`; witness `¬ vle x 1` via `hW_x` +
  `restrictIdeal_one_lt`; vle-bridge = same `Compatible.ofValuation` plumbing as now.
  Then `isPowerBounded_of_forall_vle_one_spa_of_complete_huber` :=
  `IsRingOfIntegralElements.subset_powerBounded ∘ mem_plus…`.
- **Sources**: [Hu2] 3.3(i) (huber2.txt:633-658) — "Put u = t|A ∈ Spv A and v = u|cΓ_u".

### [T907] General LL fields: `isUnit_canonicalMap_s_huber` + `locLift_divByS_isPowerBounded_huber` — **DONE 2026-07-17**
- **Progress**: faithful bodies reused verbatim with the two swaps — Huber-ring supply
  `presheafValue_isHuberRing_huber D'` (T901) in place of the Tate route, and `_huber`
  criteria names. Both axiom-clean.
- **Status**: done (2026-07-17) — **File**: FaithfulLocLift.lean (skeleton at tail) — **Depends**: T901, T906 — **Type**: theorem ×2
- Unit side: same body as `isUnit_canonicalMap_s_faithful` with
  `haveI := presheafValue_isHuberRing_huber D'` in place of the Tate route; criterion
  `isUnit_iff_forall_not_vle_zero_of_completePair` already Tate-free + axiom-clean
  (verified 2026-07-17). Bdd side: same body as `locLift_divByS_isPowerBounded_faithful`
  (comap-pullback + mk'_spec + unit-cancel), criterion := T906's wrapper.
- **Sources**: Wedhorn Lemma 8.1 proof (wedhorn.txt:3701-3706), Prop 7.52 (3472-3477),
  Prop 7.51 (3457-3470).

### [CLEANUP-M8-ALL] /cleanup-all M8 files — **Depends**: T907. Before the milestone.

### [T908] MILESTONE: `hasLocLiftPowerBounded_huber` + instance + axiom sweep — **DONE 2026-07-17**
- **Progress**: class assembled (two fields := T907); `instance (priority := 1150)
  hasLocLiftPowerBounded_huber_instance` — NO `[IsTateRing]`, NO `[IsNoetherianRing]`.
  `#print axioms` on hasLocLiftPowerBounded_huber + all three chain theorems =
  `[propext, Classical.choice, Quot.sound]`. Smoke test: `IsSheafy A` elaborates for a
  general complete Huber ring through the new instance alone. Full `lake build
  «Adic spaces»` green; all five `FiniteJetMain` theorems re-verified axiom-clean.
- **Status**: done (2026-07-17) — **File**: FaithfulLocLift.lean — **Depends**: CLEANUP-M8-ALL — **Type**: assembly
- Fill `hasLocLiftPowerBounded_huber where isUnit… := T907a; locLift… := T907b`; add
  `instance (priority := 1150) hasLocLiftPowerBounded_huber_instance` with NO
  `[IsNoetherianRing]`, NO `[IsTateRing]` (subsumes the faithful instance's vestigial
  noetherian binder). `#print axioms hasLocLiftPowerBounded_huber` must be
  `[propext, Classical.choice, Quot.sound]`. Smoke-test: `IsSheafy A` elaborates for a
  general complete Huber `A` via the new instance. Re-verify the five `FiniteJetMain`
  theorems still axiom-clean (`lake build` root + sweep). Board banner + owner digest.

### [T909] Drop `[HasLocLiftPowerBounded A]` from `IsSheafy`'s signature — **DONE 2026-07-17** (owner-directed)
- **Status**: done (2026-07-17) — **Files**: HuberLocLift.lean (NEW), StructureSheaf.lean, FaithfulLocLift.lean, Cor832.lean, EmbeddingTopo.lean, TateAcyclicity.lean, PerfectoidRing.lean, ScottishBook/Stated/{004,007,008,019,031,032,033} — **Depends**: T908 — **Type**: definition refactor (owner-requested statement change)
- **What changed**: `IsSheafy` now reads
  `class IsSheafy (A) [CommRing][TopologicalSpace][IsTopologicalRing][PlusSubring][IsHuberRing][T2Space][NonarchimedeanRing][CompleteSpace(right)][IsRingOfIntegralElements (A⁺)]`
  — i.e. quantified over exactly a **complete Hausdorff affinoid pair** (Wedhorn Def 9.31 /
  BV / [FJP] setting); `HasLocLiftPowerBounded` is synthesized INSIDE the definition via the
  M8 instance and no longer appears in any signature a user meets.
- **How**: source-faithful relayering mirroring Wedhorn's own order (§7.52 before §8) — new
  upstream module `HuberLocLift.lean` (imports PresheafTateStructure + SpvAITopology) hosts
  the relocated [Hu2]-3.3(i) infrastructure (from FaithfulLocLift), the relocated
  `presheafValue_isAdicComplete` + `comap_canonicalMap_mem_rationalOpen` (from Cor832), and
  the full-Huber chain + priority-1150 instance; StructureSheaf imports it. `AffinoidAdicSpace`'s
  `instHasLocLiftPowerBounded` field replaced by the four bundle fields. Consumer binder
  fallout patched at 11 sites (bundle in place of the class; ScottishBook @-form stubs
  restated with the bundle components — statement changes recorded here per protocol).
- **Verification**: full `lake build «Adic spaces»` green (3237 jobs); `#check @IsSheafy`
  shows no `HasLocLiftPowerBounded`; all five `FiniteJetMain` theorems re-verified
  `[propext, Classical.choice, Quot.sound]`.

### [CLEANUP-M8-FINAL] /cleanup FaithfulLocLift.lean — **Depends**: T908. Also fix the
stale docstrings recorded 2026-07-17: `hasLocLiftPowerBounded_JetA`'s "does not apply"
note (FiniteJetFunctoriality.lean:2147) and FaithfulLocLift's "Status: sorry" relics.

## MERGE-TO-MAIN (owner directive 2026-07-18, in progress)

Goal: land dev/adic-spaces on main with nothing breaking. Steps done: backup branch
`backup/pre-main-sync-20260718` pushed; merged origin/main (toolchain v4.31→v4.33-rc1,
mathlib pin fd1d54bcac5c; 7 conflicts resolved keeping branch-newer versions); mathlib
cache fetched. v4.33 fallout repaired so far (all committed):
- JetDualNumberNorm: TrivSqZeroExt Prod-literal elaboration (inl/inr limit witness), RightActions snd_mul.
- Vendored/XiaMvPowerSeriesEquiv: Finsupp.add_apply qualification, coeff_mk transparency
  (congrArg route), toAdicCompletion_coe via of_apply + Submodule.Quotient.eq.
- HuberRings: codRestrict defeq-show + exponent ring.
- Vendored/CoramMvGaussNorm: TRIMMED — 8 decls upstreamed into mathlib GaussNorm.
- SpvAI: mul_le_mul_left'/right' → renamed unprimed (sides swapped in v4.33).
- Vendored/CoramMvRestrictedNorm: three subtype-iff convert tails.
- Presheaf: subtype-algebra instance for completedPlusSubringBase; coe_map local-eq rewrites.
Remaining: wave-4 root build running (Wedhorn stack + FJP + Milnor downstream of
Presheaf). Then: gh pr create dev/adic-spaces → main. M9a T1001 resumes after the PR.

## M9 — [FJP] Cor 5.5 + Cor 6.1 (OPENED 2026-07-18, owner-approved FULL scope)

Plan: `plan-m9.md` (+ audit `plan-m9-preplan.md`). M9a ticketed below; M9b/M9c open
with their own /develop pass when M9a lands. Interface skeleton compiled:
`FJP/Milnor/StrictMilnorSquare.lean` (structure + glue_unique).

### [T1001] Pod row over an abstract square (Lemma 4.1, m-variables form)
- **Status**: in_progress (2026-07-18) — **File**: FJP/Milnor/PodRow.lean (NEW) — **Depends**: none — **Type**: defs + lemmas
- Port FiniteJetStrictLocalization's top layer (extJB/extIotaC/extRhoB/extRhoC,
  ext_square_commutes, extRhoC_strict_surjective, ext_milnorRow_exact, ext_max_norm_eq,
  ext_pair_injective — its first ~180 lines) from the four concrete Jet rings to
  `(S : StrictMilnorSquare k)`: coefficientwise maps `GraphKoszul.P S.R m → GraphKoszul.P S.B m`
  etc. via the existing generic `mapRestricted` machinery, with the SAME constants κ, ρ.
- **Sources**: [FJP] Lemma 4.1 (fjp.txt:610-635): "Choose lifts cν ∈ C with ‖cν‖ ≤ κ‖dν‖.
  Since ‖dν‖ → 0, the series Σ cν T^ν is restricted and is a lift of norm at most κ‖d‖."
  Source proof: 1 paragraph + wedge remark; concrete d=2 port anchor ≈ 180 lines.

### [T1002] Prop 4.5 heart: ideal row + controlled pullback + closedness (abstract)
- **Status**: open — **File**: FJP/Milnor/Localization.lean (NEW) — **Depends**: T1001 — **Type**: lemmas
- Port ideal_row_surjective / ideal_pullback_controlled / isClosed_IA (+ the rA/rB/rC/rD
  generator bookkeeping and span_pushed_*) from FiniteJetStrictLocalization (its middle
  ~600 lines) to S: the (4.12)-(4.16) d₂-correction chase verbatim with S's constants
  (defect constant becomes 1 + Bs·CrA-analogue in κ, ρ). Vertex inputs from S's
  pods_noetherian_* / unitBall_pods_noetherian_* fields + the generic Lemma-4.2 layer
  (FiniteJetGraphKoszul, already generic — 0 Jet-mentions).
- **Sources**: [FJP] (4.12)-(4.16) (fjp.txt:760-905); Prop 4.5 proof (fjp.txt:925-960).

### [T1003] Prop 4.5 assembly: localized square `S.localize`
- **Status**: open — **File**: FJP/Milnor/Localization.lean — **Depends**: T1002 — **Type**: def + lemmas
- Port the loc_* chain (locJB..locRhoC, loc_square_commutes, loc_pair_injective,
  loc_row_exact, loc_pair_isEmbedding, locRhoC_surjective, loc_norm_le — the file's last
  ~400 lines) and assemble `S.localize (datum) : StrictMilnorSquare k` with tracked
  constants ((4.19)/(4.20)). DESIGN NOTE (recorded): degenerate data (s = 0 ⟹ zero
  localized rings) violate NormOneClass — follow the d=2 resolution
  (presheafValue_subsingleton_of_s_eq_zero handled separately in the transfer), i.e.
  `S.localize` takes the nondegeneracy hypothesis; the transfer ticket handles s = 0
  directly as in T70x.
- **Sources**: Prop 4.5 statement+proof (fjp.txt:910-960).

### [CLEANUP-M9-1] /cleanup Milnor/PodRow + Localization — **Depends**: T1003. (fleet)

### [T1004] Naturality/(4.21) identifications (Lemma 4.6/5.1 abstract)
- **Status**: open — **File**: FJP/Milnor/Naturality.lean (NEW) — **Depends**: T1003 — **Type**: defs + lemmas
- Port the graph-bridge layer of FiniteJetFunctoriality (bridgeConst..bridgeRev,
  graphBridgeA + continuity, graphBridge_natural_B/C, pushDatum/pushCovering + interDatum,
  presheafValueMapOfHom consumers) to S: the Banach-quotient identification
  `Eα ≅ P_E/I_E` (4.21) at each vertex + naturality under refinement. The
  presheafValueMapOfHom/CovariantPush section is ALREADY generic — reuse directly.
- **Sources**: [FJP] (4.21) (fjp.txt:930-940); Lemma 4.6 (fjp.txt:981+); Lemma 5.1
  (fjp.txt:1133-1170). d=2 anchor ≈ 1400 concrete lines of the 2580-line file.

### [T1005] Transfer (Lemma 5.2 abstract): `S.isSheafy_R`
- **Status**: open — **File**: FJP/Milnor/Transfer.lean (NEW) — **Depends**: T1004 — **Type**: theorems
- Port FiniteJetSheafTransfer (productRestrictionSub_injective, gluing, embedding,
  isSheafy — 705 lines) to S with hypotheses `IsSheafy S.B`, `IsSheafy S.C`,
  `IsSheafy S.D` + the pair-package bundle on the four carriers. Conclusion
  `IsSheafy S.R`. s = 0 degenerate case per T1003's design note.
- **Sources**: [FJP] Lemma 5.2 statement (fjp.txt:1190-1200): "If the Huber pairs
  (B,B⁺), (C,C⁺), (D,D⁺) are sheafy as complete topological rings, then (R,R⁺) is
  sheafy as a complete topological ring." Proof fjp.txt:1203-1310.

### [CLEANUP-M9-2] /cleanup Milnor/Naturality + Transfer — **Depends**: T1005. (fleet)

### [T1006] Regression instance: `FiniteJetSquare F : StrictMilnorSquare K`
- **Status**: open — **File**: FJP/Milnor/FiniteJetInstance.lean (NEW) — **Depends**: T1005 — **Type**: def + theorem
- Package the d=2 square as an instance (κ = ρ = 1, all fields from the existing
  FiniteJetRings/UniformDomain/NoetherianVertices theorems — (2.1b) gives K = P = 0)
  and RE-DERIVE `isSheafy_JetA'` through the abstract machine; check it against the
  original (`example : isSheafy_JetA' F = isSheafy_JetA F`-level regression not
  required — axiom-sweep + statement identity suffice). Old concrete chain stays.
- **Sources**: [FJP] "For the finite-jet square both may be taken equal to one"
  (fjp.txt:584), (2.1b).

### [T1007] MILESTONE M9a: axiom sweep + banner + M9b//M9c /develop opening
- **Status**: open — **Depends**: T1006, CLEANUP-M9-2 — **Type**: verification
- `#print axioms` on S.isSheafy_R + isSheafy_JetA'; root build; banner; then run the
  M9b + M9c /develop passes (detailed ticketing per plan-m9.md architecture).

## M7 (stretch, NOT opened): strong sheafiness ([FJP] Cor 5.5)
Blocked on T704. Requires: `𝓐⟨Z₁..Zₙ⟩ ≅ 𝓑⟨Z⟩ ×_{𝓓⟨Z⟩} 𝓒⟨Z⟩` (Lemma 4.1 with `Z`-variables),
instance stacks for `𝓐⟨Z⟩`, and re-running M5/M6 over the extended square. Open via
`/develop --continue` after T704 with a fresh decomposition section.
