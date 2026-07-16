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
- Open: 33 | Done: 3 (T001, T101, T102) | Parallel capacity at peak: 4 workers
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

### [T103] `RestrictedLaurent.lean` — multiplicativity & domain
- **Status**: open | **Depends**: T102 | **Type**: proofs (L1.3)
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

### [T104] `RestrictedLaurent.lean` — nonneg subring, `nonnegEquiv`, `evalHom`
- **Status**: open | **Depends**: CLEANUP-1 | **Type**: def-completion + proofs (L1.4)
- **Sorries**: `nonnegSubring` closure fields, `isClosed_nonnegSubring`, `nonnegEquiv`
  (data + proofs), `nonnegEquiv_norm`, `ofRestricted_norm/injective`, `evalHom` (data +
  fields), `evalHom_surjective`, `evalHom_norm_le`.
- **Sketch**: closure: convolution support additivity on ℕ; closedness: intersection of
  coefficient-functional kernels; `nonnegEquiv`: coefficient transport `ℕ ↪ ℤ`
  (`PowerSeries.coeff` ↔ `coeff (a : ℤ)`, zero on negatives); `evalHom`: on a restricted
  2-variable series `∑ c_{ij} W^i V^j ↦ ∑ c_{ij} W^{i−j}` — coefficient of `a` is
  `∑'_{i−j=a} c_{ij}` (summable, decay); surjectivity via the monomial section (L1.4).
- **Source**: [FJP] Lemma 2.2 (`k⟨W⟩` closed), Prop 2.1 (presentation) — quotes at L1.4.

### [CLEANUP-2] /cleanup `RestrictedLaurent.lean` (final) — **Depends**: T104.

### [T105] `JetDualNumberNorm.lean` — complete file
- **Status**: open | **Depends**: none (parallel with T101) | **Type**: proofs (L1.5)
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

### [CLEANUP-3] /cleanup `JetDualNumberNorm.lean` (final) — **Depends**: T105.

### [T106] `FiniteJetRings.lean` — square maps and sections
- **Status**: open | **Depends**: T102, T105 | **Type**: proofs (L1.6 first half)
- **Sorries**: `rhoC` hom fields, `sectionD` decay + `rhoC_sectionD` + `sectionD_add` +
  `norm_sectionD`, `norm_rhoC_le`, `norm_rhoB`, `rhoB_injective`, `rhoC_surjective`.
- **Sketch**: `rhoC` multiplicativity: `PowerSeries.coeff_mul` at indices 0, 1 matches
  `TrivSqZeroExt` multiplication (2-term convolution); `sectionD` is the degree-≤1 series;
  norms by coefficient inspection. Do NOT claim `sectionD` multiplicative (L1.6 attack 2).
- **Source**: [FJP] Prop 2.1 section sentence — quote at L1.6.

### [T107] `FiniteJetRings.lean` — 𝓐 and the strict row
- **Status**: open | **Depends**: T104, T106 | **Type**: proofs (L1.6 second half)
- **Sorries**: `jetSupport` closure fields, `isClosed_jetSupport`, `CompleteSpace (JetA F)`,
  `jB` hom fields, `norm_jB_le`, `square_commutes`, `mem_jetSupport_iff_jet_in_range`,
  `milnorRow_exact`, `max_norm_eq`, `difference_strict_surjective`.
- **Sketch**: support additivity (paper's S-monoid, subcases in L1.6 attack 1); closedness →
  completeness (`IsClosed.completeSpace_coe`); row exactness: membership chase through
  `nonnegEquiv`; `max_norm_eq`: `‖jB a‖ = max(‖c₀‖,‖c₁‖) ≤ ‖a‖ = ‖ιC a‖`.
- **Source**: [FJP] Prop 2.1 + Lemma 2.2 + (2.1b) — quotes at L1.6.

### [T108] `FiniteJetRings.lean` — constants, Tate structure, `unitBall`
- **Status**: open | **Depends**: T107 | **Type**: proofs (L1.7 first half)
- **Sorries**: `norm_K_discrete`, `constC` (data + norm), `constC_mem_jetSupport`, `constA`,
  `tA` norm/unit lemmas, `unitBall` fields + `isOpen_unitBall`, `IsHuberRing ×4`,
  `IsTateRing ×4`.
- **Sketch**: `norm_K_discrete` from `Valued.toNormedField` + `WithZeroMulInt.toNNReal 2`
  normalisation (unfold the `RankOne` hom; mirror `ExampleUnitDisc` norm lemmas);
  Tate/Huber: `podD` pattern with `unitBall` + `Ideal.span {t}`; topological nilpotence of
  `t` from `‖t‖ < 1` + norm multiplicativity on constants.
- **Source**: [FJP] (2.1a) — quote at L1.7.

### [CLEANUP-4] /cleanup `FiniteJetRings.lean` — **Depends**: T108.

### [T109] `FiniteJetRings.lean` — plus rings and right-uniformity completeness
- **Status**: open | **Depends**: CLEANUP-4 | **Type**: proofs (L1.7 second half)
- **Sorries**: `IsRingOfIntegralElements ×4`, right-uniformity `CompleteSpace ×4`.
- **Sketch**: `E°` open (⊇ ball), integrally closed ([FJP] §5 monic-`M`-module argument —
  quote at L1.7), `subset_powerBounded` refl; completeness: `SeminormedAddCommGroup.to_isUniformAddGroup`
  + `IsUniformAddGroup.rightUniformSpace_eq` + metric completeness (disc pattern,
  `ExampleUnitDisc.lean:492`). NOTE (L1.7 attack 2): plus ring is the MAXIMAL one; do not
  attempt the unit ball for 𝓑/𝓓.
- **Source**: [FJP] p. 17 (5.2) block — quotes at L1.7.

### [CLEANUP-5] /cleanup `FiniteJetRings.lean` (final) — **Depends**: T109.

### [T201] `FiniteJetUniformDomain.lean` — multiplicativity, domains ∥parallel track∥
- **Status**: open | **Depends**: T103, T107 | **Type**: proofs (R2 leaves)
- **Sorries**: `norm_L_mul`, `norm_JetC_mul`, `IsDomain (JetC F)`, `IsDomain (JetA F)`.
- **Sketch**: `norm_L_mul` = `RestrictedLaurent.norm_mul_eq` at `norm_K_discrete`;
  `norm_JetC_mul` via vendored univariate mult lemma over base `L` (check its exact
  hypothesis shape — risk 2; fallback: ℤ×ℕ achiever, L1.3); domains from multiplicativity;
  `JetA` domain via `Subring` + `IsDomain` of `JetC` (`Function.Injective.isDomain`).

### [T202] `FiniteJetUniformDomain.lean` — uniformity and (5.2)
- **Status**: open | **Depends**: T201, T109 | **Type**: proofs (R2 + R4 inputs)
- **Sorries**: `isPowerBounded_JetA_iff`, `isUniform_JetA`, `isPowerBounded_JetB_iff`,
  `isPowerBounded_JetD_iff`, `not_isUniform_JetB`.
- **Sketch**: powers via `norm_JetC_mul` restricted (L: "powers computed in 𝒞"); ball
  bounded: `t`-absorption (disc `isBounded_OD` pattern); (5.2) via `JetNorm.pow_eq` + Gauss
  multiplicativity on the fst-component; `not_isUniform_JetB`: `{inr (λ)} = λ·ε` family
  power-bounded with `‖λε‖ = |λ|` unbounded — negate `IsBounded` via the `t^{-n}`-scaling
  characterisation.
- **Source**: [FJP] Prop 2.3 + (5.2) + (2.1d) — quotes at R2/L1.7/R4.

### [T203] `FiniteJetUniformDomain.lean` — non-noetherianity (R3 complete)
- **Status**: open | **Depends**: T104, T107 | **Parallel**: with T202 | **Type**: proofs
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
- **Status**: open | **Depends**: T104 | **Type**: proofs (L2.1)
- **Sorries**: `isNoetherianRing_restricted_L`.
- **Sketch**: per-`m` surjection `K⟨W,V,Z₁..Zₘ⟩ ↠ L⟨Z₁..Zₘ⟩`: vendored
  `restrictedGaussEquiv` (both ends) + `exists_flatten'`-style regrouping +
  `mapRestricted (evalHom)` surjectivity (coefficientwise section) +
  `isNoetherianRing_of_surjective` + `IsStronglyNoetherian K`. NEVER "noeth ⟹ strongly
  noeth" (B2). **Source**: [FJP] Prop 2.1 quotient sentence — quote at L2.1.

### [T302] vertices strongly noetherian
- **Status**: open | **Depends**: T301, T105 | **Type**: proofs (L2.2–L2.3)
- **Sorries**: `IsStronglyNoetherian (JetC F)`, `isNoetherianRing_restricted_dualNumber`,
  `IsStronglyNoetherian (JetB F)`, `(JetD F)`.
- **Sketch**: JetC = disc-example flattening verbatim over base `L` (copy
  `ExampleUnitDisc`'s instance proof, base swapped); dual-number flattening
  `(DualNumber S)⟨Z⟩ ≅ DualNumber (S⟨Z⟩)` coefficientwise (fst/snd of coefficients) +
  `JetNorm.isNoetherianRing`.

### [T303] unit-ball pods noetherian
- **Status**: open | **Depends**: T301 | **Parallel**: with T302 | **Type**: proofs (L2.4)
- **Sorries**: `isNoetherianRing_unitBall_L/JetB/JetC/JetD`.
- **Sketch**: `k° = F⟦X⟧` noetherian; integral restricted rings as ϖ-adic completions of
  polynomial rings (`AdicCompletionBridge` pattern / `Psi`-transpose as in
  `ExampleLaurentSeries`'s strong-noetherianity proof); balls of `L`/`JetC` are quotients/
  images of those; `DualNumber` of noetherian (T105). Fallbacks recorded at L2.4.

### [CLEANUP-7] /cleanup `FiniteJetNoetherianVertices.lean` — **Depends**: T302, T303.

### [T304] vertices sheafy (828b application)
- **Status**: open | **Depends**: CLEANUP-7, T109 | **Type**: proofs (L2.5)
- **Sorries**: `isSheafy_JetB/C/D`.
- **Sketch**: `exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` with the letI
  plumbing of `ExampleUnitDisc.isSheafy_unitDisc`; if instance search balks, `haveI` the
  bundle members explicitly. All bundle members exist by T109/T302.

### [CLEANUP-8] /cleanup `FiniteJetNoetherianVertices.lean` (final) — **Depends**: T304.

### [T401] `FiniteJetGraphKoszul.lean` — polynomial syzygies, coordinate case
- **Status**: open | **Depends**: none (pure algebra; parallel from day 1) | **Type**: proofs
  (L3.1–L3.2)
- **Sorries**: `d1_d2`, `syzygy_coordinate`.
- **Sketch**: `d1_d2`: `Finset.sum` reindexing, terms cancel in pairs; `syzygy_coordinate`:
  induction on `m` (L3.2 log has the full argument: reduce mod `T_m` via
  `MvPolynomial.aeval`-substitution to `Fin (m−1)`, IH, correct with `T_m e_j − T_j e_m`,
  extract the `T_m`-cofactor, close with mul-by-variable injectivity).
- **Mathlib**: `MvPolynomial.finSuccEquiv` (poly version), `Polynomial` mul-X-injective.

### [T402] graph syzygies over the polynomial ring
- **Status**: open | **Depends**: T401 | **Type**: proofs (L3.3)
- **Sorries**: `syzygy_graph_polynomial`.
- **Sketch**: localize at maximal ideals (`Submodule.eq_top_of_localization_maximal` on the
  quotient submodule Syz/⟨Koszul⟩, or eq_bot form); case split on `r_i ∉ 𝔭` (explicit
  Koszul expression — formula in L3.3 log) vs all `r_i ∈ 𝔭` (then `g ∉ 𝔭` by (4.3);
  translate `T_i ↦ T_i + f_i/g` via `MvPolynomial.aeval` automorphism; unit-scale
  `v_{ij} ↦ g² v_{ij}`-corrected; T401). m = 1 comes out as `ker = 0` automatically.
- **Source**: [FJP] Lemma 4.2 proof ¶1 — full quote in file docstring + L3.3.

### [T403] `mapRestricted` + `polyToP`
- **Status**: open | **Depends**: T102 | **Type**: def-completion (L3.4 + `polyToP`)
- **Sorries**: `mapRestricted` membership + hom fields, `norm_mapRestricted_le`, `polyToP`.
- **Sketch**: `MvPowerSeries.map` coefficient formula; decay via `‖φ x‖ ≤ ‖x‖`; `polyToP`
  via vendored `MvPolynomial.toMvRestricted` (or coefficient-finsupp embedding).

### [CLEANUP-9] /cleanup `FiniteJetGraphKoszul.lean` — **Depends**: T401–T403.

### [T404] flatness of `E[T] → E⟨T⟩`
- **Status**: open | **Depends**: T303, T403 | **Type**: proofs (L3.5)
- **Sorries**: `flat_polyToP`.
- **Sketch**: (4.4): `E₀⟨T⟩ = AdicCompletion (t) (E₀[T])` (coefficientwise; the heaviest
  sub-leaf — mirror `AdicCompletionBridge`); `AdicCompletion.flat_of_isNoetherian`
  (`E₀[T]` noetherian by T303 + Hilbert basis); invert `t`
  (`Module.Flat` of localization + composition). ONLY positive-degree facts downstream —
  never claim faithful flatness (L3.5 attack 1).
- **Source**: [FJP] (4.4) + Tag 00MB sentence — quote at L3.5.

### [T405] syzygy transport to `E⟨T⟩`
- **Status**: open | **Depends**: T402, T404 | **Type**: proofs (L3.6)
- **Sorries**: `syzygy_graph_restricted`.
- **Sketch**: kernels of matrix maps commute with flat base change (`Module.Flat` +
  `LinearMap.ker` tensor lemmas); span of pushed Koszul generators; identification of
  `Fin m → P` with the base-changed free module.

### [T406] closedness and strictness constants
- **Status**: open | **Depends**: T405, T302 | **Type**: proofs (L3.7–L3.9)
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
- **Status**: open | **Depends**: T107, T403 | **Type**: proofs (L4.1)
- **Sorries**: `ext_square_commutes`, `extRhoC_strict_surjective`, `ext_milnorRow_exact`,
  `ext_max_norm_eq`, `ext_pair_injective`.
- **Sketch**: coefficientwise application of T106/T107's row via `MvPowerSeries.map_coeff`;
  constants 1 (decay bookkeeping trivial).

### [T502] pushed spans + ideal-row surjectivity
- **Status**: open | **Depends**: T501, T406 | **Type**: proofs (L4.2–L4.3 part)
- **Sorries**: `span_pushed_B/C/D`, `ideal_row_surjective`.
- **Sketch**: span push through ring homs; surjectivity: `exists_d1_lift` at 𝓓 →
  coefficientwise lift through `extRhoC` (T501) → `d_{1,C}` image ([FJP] (4.11) chase,
  constants recorded at L4.3).

### [T503] the controlled pullback and closedness of `I_𝓐`
- **Status**: open | **Depends**: T502 | **Type**: proofs (L4.4–L4.5) — the §4 heart
- **Sorries**: `ideal_pullback_controlled`, `isClosed_IA`.
- **Sketch**: the (4.12)–(4.16) chase, exactly as in the paper (independently re-derived
  twice — L4.3/L4.4 logs): representatives via `exists_d1_lift` at 𝓑, 𝓒; mismatch is a
  𝓓-syzygy; correct with `exists_d2_lift` + pair-lift (T501 on `Pairs`-tuples); recombine
  via `ext_milnorRow_exact`; closedness: preimage of closed matching set under the T501
  embedding.

### [CLEANUP-11] /cleanup `FiniteJetStrictLocalization.lean` — **Depends**: T503.

### [T504] quotient row, algebraic part
- **Status**: open | **Depends**: T503 | **Type**: proofs (L4.6–L4.7)
- **Sorries**: `quotient_row_exact`, `locJB/locIotaC/locRhoB/locRhoC` (defs via
  `Ideal.Quotient.lift`), `_mk` lemmas, `loc_square_commutes`, `loc_row_exact`,
  `loc_pair_injective`, `locRhoC_surjective`.
- **Sketch**: lifts exist since `ext*` map ideals into ideals (definition of `rB/rC/rD`);
  3×3 chase per L4.6 with `hHsurj` = T502.

### [T505] quotient row, topological part (Prop 4.5 complete)
- **Status**: open | **Depends**: T504 | **Type**: proofs (L4.8)
- **Sorries**: `loc_pair_isEmbedding`, `locRhoC_isOpenMap`, `locA_t2`, `locA_completeSpace`.
- **Sketch**: group-quotient maps open; embedding: inducing via the quotient-of-embedding
  diagram + closedness (T503); T2 from closed ideal; completeness of normed-group quotient
  by closed subgroup (mathlib quotient norm instances) transported to the ring quotient.

### [CLEANUP-12] /cleanup `FiniteJetStrictLocalization.lean` (final) — **Depends**: T505.

### [T601] `FiniteJetFunctoriality.lean` — pods and datum pushes
- **Status**: open | **Depends**: T109 | **Type**: def-completion + proofs (L5.1–L5.2)
- **Sorries**: `podA/B/C/D` fields, `pushDatumB/C/D` `hopen`, `*_isRational`.
- **Sketch**: pod `isAdic` = disc `podD` metric argument; `hopen` generic span-⊤/principal
  computation (worked out at L5.2; fallback per-vertex).

### [T602] covariant presheaf-value maps
- **Status**: open | **Depends**: T601 | **Type**: def-completion + proofs (L5.3 part)
- **Sorries**: `presheafValueMapB/C/D` (data), continuity ×2, `canonicalMap`-compat ×2.
- **Sketch**: `IsLocalization.Away.map` on `Localization.Away D.s`; continuity via
  `locTopology` lattice inclusion (generators ↦ generators over the pod pair);
  `UniformSpace.Completion.extensionHom` (T0 + complete targets are project instances).

### [T603] **KEYSTONE**: the graph bridge for 𝓐
- **Status**: open | **Depends**: T505, T602 | **Type**: def-completion + proofs (L5.4)
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

### [T604] loc-lift instances
- **Status**: open | **Depends**: T603, T304 | **Type**: proofs (L5.5–L5.6)
- **Sorries**: `HasLocLiftPowerBounded (JetB/C/D)` (via `hasLocLiftPowerBounded_faithful`),
  `hasLocLiftPowerBounded_JetA` (componentwise through the bridge + `loc_row_exact` +
  vertices' fields; unit gluing `(b⁻¹, c⁻¹)`; power-bounded componentwise in max norm).

### [T605] restriction naturality + coverage
- **Status**: open | **Depends**: T604 | **Type**: proofs (L5.3 rest + L5.7)
- **Sorries**: `presheafValueMapB/C_restriction`, `mem_rationalOpen_pushDatum*_iff`,
  `pushCoveringB/C/D` fields, `*_isRational`.
- **Sketch**: naturality by `IsLocalization.ringHom_ext` + completion-extension uniqueness;
  coverage pointwise via `ValuationSpectrum.comap`/`comap_mem_spa` (power-bounded
  preservation via norms — never bare continuity, B2).

### [T606] intersection data
- **Status**: open | **Depends**: T601 | **Parallel**: with T602–T605 | **Type**: proofs (L5.8)
- **Sorries**: `interDatum` `hopen`, `rationalOpen_interDatum`, `interDatum_isRational`.
- **Sketch**: product datum, both inclusions pointwise under span-⊤; fallback
  normalisation `insert s T` recorded at L5.8.

### [CLEANUP-14] /cleanup `FiniteJetFunctoriality.lean` (final) — **Depends**: T605, T606.

### [T701] transfer: separation
- **Status**: open | **Depends**: CLEANUP-14 | **Type**: proofs (L6.1)
- **Sorries**: `productRestrictionSub_injective_JetA`.

### [T702] transfer: gluing — **the sheafiness workhorse**
- **Status**: open | **Depends**: T701 | **Type**: proofs (L6.2)
- **Sorries**: `gluing_JetA`.
- **Sketch**: the ten-step chain of L6.2 with the vertex-side-`D₃` resolution (L6.2 attack 1
  — read it before starting). May be expanded into sub-tickets by /beastmode if > 1 session.

### [T703] transfer: embedding
- **Status**: open | **Depends**: T702 | **Type**: proofs (L6.3)
- **Sorries**: `productRestrictionSub_isEmbedding_JetA`.
- **Sketch**: 828b-assembly mirror: range = `sectionEqualizer` (⊆ generic; ⊇ from T702);
  `sectionEqualizer_isClosed`; `isInducing_of_closedRange_of_topNilpUnit`; + T701.

### [CLEANUP-ALL-1] /cleanup-all — **Depends**: T703 (pre-milestone).

### [T704] ★ MILESTONE: `finiteJet_isSheafy` axiom-clean
- **Status**: open | **Depends**: CLEANUP-ALL-1 (and transitively everything on the spine)
- **Deliverable**: `lean_verify FiniteJet.finiteJet_isSheafy` →
  `[propext, Classical.choice, Quot.sound]`; board banner; owner digest.

### [T801] chart datum
- **Status**: open | **Depends**: T601 | **Parallel**: with T7xx | **Type**: proofs (R4)
- **Sorries**: `Wa` membership, `chartDatum` `hopen`, `chartDatum_isRational`.

### [T802] Prop 3.1: the chart is 𝓑
- **Status**: open | **Depends**: T801, T603 | **Type**: def-completion + proofs (R4)
- **Sorries**: `chartEquiv` (data), continuity ×2; replace stub
  `chartEquiv_canonicalMap_W : True` with the real pinning statement
  (`chartEquiv (canonicalMap (Wa)) = tK • X`-form — fix statement per R4).
- **Sketch**: through `graphBridgeA` at `chartDatum` (m = 2 enumeration {W, t}) OR directly
  by the paper's two-map argument: `Q²`-collapse via the factorisation
  `y − ϖⁿXⁿ(W⁻ⁿy) = (Wⁿ − (ϖX)ⁿ)(W⁻ⁿy)` (R4 quote); `ψ` bounded multiplicative (planner-
  verified jet computation); `φ` from power-boundedness of X, Q and `Q̄² = 0`; dense
  round-trips. The graph-bridge route is preferred (reuses T603); the direct route is the
  recorded fallback.

### [T803] Cor 3.2: not stably uniform
- **Status**: open | **Depends**: T802, T202 | **Type**: proofs (R4)
- **Sorries**: `isUniform_of_ringEquiv`, `not_isUniform_chart`, `not_isStablyUniform_JetA`.
- **Sketch**: transport boundedness/power-boundedness through the bi-continuous iso;
  negate `IsStablyUniform` at `chartDatum` (class field instantiation).

### [CLEANUP-15] /cleanup `FiniteJetChart.lean` (final) — **Depends**: T803.

### [T804] MILESTONE: headline assembly verification
- **Status**: open | **Depends**: T704, CLEANUP-6, CLEANUP-15
- **Deliverable**: `lean_verify` all five `FiniteJet.finiteJet_*` theorems axiom-clean;
  update board banner; PR-readiness note for `dev/adic-spaces → main`.

### [CLEANUP-FINAL] /cleanup-all — **Depends**: T804. Last item before any M7 planning.

---

## M7 (stretch, NOT opened): strong sheafiness ([FJP] Cor 5.5)
Blocked on T704. Requires: `𝓐⟨Z₁..Zₙ⟩ ≅ 𝓑⟨Z⟩ ×_{𝓓⟨Z⟩} 𝓒⟨Z⟩` (Lemma 4.1 with `Z`-variables),
instance stacks for `𝓐⟨Z⟩`, and re-running M5/M6 over the extended square. Open via
`/develop --continue` after T704 with a fresh decomposition section.
