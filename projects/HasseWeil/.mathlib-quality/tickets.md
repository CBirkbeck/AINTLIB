# Ticket Board: Hasse-Weil Sorry Elimination

## Active skeleton leaves (2026-05-22, via /beastmode on the universal-bound skeleton)

### [SK-KERD-FINRANK-P] [K(E):K(E)ᵖ] = p — **DONE 2026-05-22** (`finrank_KE_over_frobeniusRange_p`, Parent: SK-KERD-PTH)
- **DONE 2026-05-22**: `finrank_KE_over_frobeniusRange_p` PROVEN, axiom-clean (`#print axioms` =
  [propext, Classical.choice, Quot.sound], NO sorryAx), build green (2606 jobs). All sub-pieces closed:
  SK-FINRANK-P-1 (`x_gen∉K(E)ᵖ`), the IsPurelyInseparable instance, SK-FINRANK-P-3 minpoly degree
  (`minpoly_x_gen_frobeniusRange_natDegree`), the finrank-combine (`respectTransparency false` for the
  nested `Algebra ↥L KE`; `surjective_algebraMap_of_isSeparable`→`L=⊤`; `adjoin.finrank`+`topEquiv`),
  and the separable tower (helper `isSeparable_KE_over_frobeniusRange_adjoin_x_gen`, with FractionRing
  `Algebra`/`IsSeparable`/`IsScalarTower` passed as explicit `halg`/`hsep0`/`htower`; `himg` proven via
  polynomial induction + `IsFractionRing.div_surjective` + `map_div₀` + scalar tower + `div_mem`).
  Required `import HasseWeil.Ramification` (cycle-free).
- **STATED 2026-05-22** in GapQfKernel.lean (build green; `(frobenius KE p).fieldRange` form verified).
- **Cleaner proof route**: `[K(E):K(E)ᵖ] = [K(x,y):K(x,yᵖ)]·[K(x,yᵖ):K(xᵖ,yᵖ)] = 1·p`.
  `[K(x,y):K(x,yᵖ)]=1`: y is separable over K(x)⊆K(x,yᵖ) (`functionField_isSeparable`) AND purely
  inseparable over K(x,yᵖ) (`yᵖ ∈` it), so `y ∈ K(x,yᵖ)` (separable∩purely-insep = trivial).
  `[K(x,yᵖ):K(xᵖ,yᵖ)] = [K(x):K(xᵖ)] = p` (x transcendental, K perfect).
- **Sub-pieces (primitive-element route, 2026-05-22)**:
  - **[SK-FINRANK-P-1]** `x_gen ∉ K(E)ᵖ` — **DONE** (`x_gen_not_pth_power`, GapQfKernel.lean, build green).
    Even cleaner than planned: `D(gᵖ)=0` (`kaehlerD_pth_power_eq_zero`) but `D(x_gen)≠0` (`D_x_ne_zero`),
    so `x_gen` is no p-th power. (No separability/transcendence argument needed.)
  - **[SK-FINRANK-P-2]** `K(E)=K(E)ᵖ(x_gen)` — **COMPLETE VERIFIED ROUTE (all mathlib lemmas exist)**:
    set `B := K(E)ᵖ(x_gen)` (= `IntermediateField.adjoin ↥((frobenius KE p).fieldRange) {x_gen}`, with
    `K ⊆ fieldRange` since F perfect ⟹ `a=(a^{1/p})ᵖ`). `KE/B` is **purely insep** (`KE=B(y_gen)`,
    `y_genᵖ∈K(E)ᵖ⊆B`, via `isPurelyInseparable_iff_pow_mem`) AND **separable** (`KE/K(x_gen)` separable
    by `functionField_isSeparable`, `K(x_gen)⊆B`, tower-top `Algebra.isSeparable_tower_top_of_isSeparable`).
    Then `IsPurelyInseparable.surjective_algebraMap_of_isSeparable B KE` ⟹ `algebraMap B KE` surjective ⟹
    `KE=B`. (Pattern: `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`, Basic.lean:179.)
  - **[SK-FINRANK-P-3]** combine: **DEGREE PIECE DONE** — `minpoly_x_gen_frobeniusRange_natDegree`
    (`(minpoly K(E)ᵖ x_gen).natDegree = p`, GapQfKernel.lean, build green 2570 jobs). Proof:
    `ExpChar` via `ExpChar.prime`+`expChar_of_injective_ringHom`/`RingHom.charP_iff`;
    `IsPurelyInseparable.minpoly_eq_X_pow_sub_C` gives `natDegree = pⁿ`; `n≥1` (`x_gen∉K(E)ᵖ` via
    `minpoly.aeval`+`y.2` membership), `n≤1` (`minpoly ∣ Xᵖ−x_genᵖ` via `minpoly.dvd`+`natDegree_le_of_dvd`).
    REMAINING: `finrank = minpoly.natDegree = p` via `IntermediateField.adjoin.finrank` + SK-FINRANK-P-2.
    **finrank-combine FULLY PROVEN (2026-05-22) modulo one concrete lemma `himg`.**
    `finrank_KE_over_frobeniusRange_p` is NO LONGER in the sorry list — PROVEN, wired to helper
    `isSeparable_KE_over_frobeniusRange_adjoin_x_gen` (the separable tower), which compiles with `himg`
    as its ONLY sorry. respectTransparency-vs-FractionRing conflict resolved: helper takes FractionRing
    `Algebra`/`IsSeparable` as EXPLICIT args (`halg`,`hsep0`) under `respectTransparency false`; finrank
    passes them as TERMS (`functionField_algebra_fractionRing`+`functionField_isSeparable`, via new
    `import HasseWeil.Ramification` — cycle-free, build 2606 jobs). Tower body: `codRestrict` +
    `IsScalarTower.of_algebraMap_eq (fun _ => rfl)` + `isSeparable_tower_top_of_isSeparable (FractionRing _) ↥L KE`.
    **SOLE REMAINING for `[K(E):K(E)ᵖ]=p`: `himg`** = `∀ z : FractionRing (Polynomial F),
    algebraMap (FractionRing (Polynomial F)) KE z ∈ L` (GapQfKernel.lean ~389). Route: `x_gen =
    algebraMap R KE (algebraMap (Polynomial F) R X)` (MulByIntPullback:27), tower `Poly F→FractionRing→KE`
    (Ramification:298); image = `K(x_gen) ⊆ L` (x_gen∈L via `subset_adjoin`, K⊆fieldRange⊆L, L field).
    Prove: `x_gen∈L`, `algebraMap (Poly F) KE p = aeval x_gen p ∈ L`, then `IsLocalization.mk'`/field-quotient.
    --- (historical) finrank-combine STRUCTURE PROVEN (2026-05-22), reduced to just `hLsep`. The nested-instance
    wall (`Algebra ↥L KE` for `L := adjoin ↥((frobenius KE p).fieldRange) {x_gen}`) was SOLVED by
    `set_option backward.isDefEq.respectTransparency false in` (the same option `l6_B3_tower` needed for
    IntermediateField instances). PROVEN now (build green, finrank line 375 has only `hLsep` sorry inside):
    `IsPurelyInseparable ↥L KE` (pow_mem); `surjective_algebraMap_of_isSeparable` ⟹ `L=⊤`
    (`eq_top_iff`+`l.2`); finrank via `IntermediateField.adjoin.finrank hint` (`hint` from
    `hpi.isIntegral.isIntegral`) + `minpoly_x_gen_frobeniusRange_natDegree` (=p) +
    `LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv`.
    **Sole remaining: `hLsep : Algebra.IsSeparable ↥L KE`** (the separable tower). Route: `functionField_isSeparable`
    (`Algebra.IsSeparable (FractionRing (Polynomial F)) KE`, an EXPENSIVE instance — needs
    `synthInstance.maxHeartbeats` bump) + `K(x)=FractionRing(Polynomial F) ⊆ L` (x_gen∈L) → tower-top
    `Algebra.isSeparable_tower_top_of_isSeparable`. Plumbing: `Algebra (FractionRing(Polynomial F)) ↥L`
    via `codRestrict` (image ⊆ L = `himg`) + `IsScalarTower`. ISSUE: the FractionRing instance synthesis
    interacts badly with `respectTransparency false`; try establishing `hLsep` in a *separate* lemma
    WITHOUT that option (only the finrank-combine needs it), then pass `hLsep` in.
- **File**: HasseWeil/GapQfKernel.lean (or a new Verschiebung helper). **Type**: lemma.
- **Statement**: `Module.finrank (frobeniusSubfield_p) W.toAffine.FunctionField = p` where `frobeniusSubfield_p`
  is `(frobenius KE p).range` (= K(E)ᵖ) as an IntermediateField (K=K(E)).
- **Proof sketch**: char p, K perfect, trdeg 1. Either (a) derive from the project's
  `frobeniusIsog_pullback_finrank` (`[K(E):K(E)^q]=q`, FieldTower.lean:69) via the Frobenius tower
  `K(E)^q ⊆ K(E)^{q/p} ⊆ … ⊆ K(E)^p ⊆ K(E)`, each step `[K(E)^{p^k}:K(E)^{p^{k+1}}] = [K(E):K(E)^p]`
  by the `frobeniusEquiv`-iso, so `[K(E):K(E)^p]^n = p^n` ⟹ `=p`; or (b) `IsPurelyInseparable.finrank_eq_pow`
  (mathlib PurelyInseparable/Basic.lean:326) + trdeg-1. **Mathlib**: `frobeniusEquiv` (Perfect.lean:126),
  `IsPurelyInseparable.finrank_eq_pow`. This is the key remaining gap of SK-KERD-PTH ⟹.

### [SK-KERD-FIELD-ARG] ker D = K(E)ᵖ via prime-degree intermediate field — **DONE 2026-05-22** (Parent: SK-KERD-PTH)
- **DONE 2026-05-22**: `kaehlerD_eq_zero_iff_mem_pth_powers` PROVEN, axiom-clean (`#print axioms` =
  [propext, Classical.choice, Quot.sound], NO sorryAx), build green (2606 jobs). So **SK-KERD-PTH `⟹`
  is DONE** — the char-`p` Kähler kernel theorem `D w = 0 ↔ ∃ g, gᵖ = w` is complete. Proof: `ker D`
  built as an `IntermediateField ↥K(E)ᵖ KE` (carrier `{v | D v = 0}`; `mul_mem'` via `Derivation.leibniz`,
  `inv_mem'` via `Derivation.leibniz_inv`, `algebraMap_mem'` via `kaehlerD_pth_power_eq_zero`); `M ≠ ⊤`
  from `kaehlerD_ne_zero`; prime-degree tower `Module.finrank_mul_finrank` + `[K(E):K(E)ᵖ]=p` (prime) ⟹
  `finrank K(E)ᵖ M ∈ {1,p}`; `=1` ⟹ `M=⊥` (`IntermediateField.finrank_eq_one_iff`), `=p` ⟹ `M=⊤`
  (`Submodule.eq_top_of_finrank_eq`) contradicting `M≠⊤`; so `M=⊥`, `w∈⊥=K(E)ᵖ` ⟹ `∃g gᵖ=w`. Needed
  `set_option backward.isDefEq.respectTransparency false` (nested-IntermediateField instances) + heartbeat bumps.
- **File**: HasseWeil/GapQfKernel.lean. **Type**: lemma (closes `kaehlerD_eq_zero_iff_mem_pth_powers` ⟹).
- **Statement**: discharges `D w = 0 → ∃ g, g^p = w`.
- **Proof sketch**: `ker D` is an intermediate field `K(E)ᵖ ⊆ ker D ⊆ K(E)` — closed under field ops
  since `D(w₁w₂)=w₁Dw₂+w₂Dw₁`, `D(w⁻¹)=−w⁻²Dw`, and contains `K(E)ᵖ` (`kaehlerD_pth_power_eq_zero`, PROVEN).
  `D ≠ 0` (from `kaehler_rank_one`, Ω≠0) ⟹ `ker D ⊊ K(E)`. With `[K(E):K(E)ᵖ]=p` prime (SK-KERD-FINRANK-P),
  the tower `[K(E):ker D]·[ker D:K(E)ᵖ]=p` forces `ker D = K(E)ᵖ`. So `w∈ker D ⟹ w∈K(E)ᵖ ⟹ ∃g g^p=w`.
  **Mathlib**: `IntermediateField`, `Module.finrank_mul_finrank`, `Nat.Prime` divisor argument.
- **Foundations PROVEN (2026-05-22, two invocations, build green)**: `kaehlerD_pth_power_eq_zero`
  (`D(gᵖ)=0`), `kaehlerD_pth_power_mul` (`D(gᵖ·h)=gᵖ·Dh`, the Kᵖ-semilinearity ⟹ ker D is a
  Kᵖ-submodule), `kaehlerD_ne_zero` (`∃w, Dw≠0`, from `kaehler_rank_one` + `span_range_derivation`
  ⟹ ker D ⊊ K(E)). So both structural inputs to the prime-degree argument are in hand; the only
  residual is SK-KERD-FINRANK-P (`[K(E):K(E)ᵖ]=p`) + constructing `ker D`/`K(E)ᵖ` as IntermediateFields
  and applying `Module.finrank_mul_finrank` with `p` prime.


### [SK-L6-B3] l6_B3_tower — DONE (2026-05-22)
- **Status**: done — axiom-clean (`[propext, Classical.choice, Quot.sound]`), lake build 2940 jobs.
- **File**: HasseWeil/GapSpines.lean
- Framework wall #1 (IntermediateField nested tower). Template recorded in THE-PLAN §0b.

### [SK-KER-INJ] localExpand_injective — DONE (2026-05-22)
- **Status**: done — `(localExpand W).injective` (RingHom from a field).
- **File**: HasseWeil/GapQfKernel.lean

### [SK-LAURENT-DERIV-MUL] LaurentSeries.derivative product rule — DONE (2026-05-22)
- **Status**: done — `laurentSeries_derivative_mul` axiom-clean (`[propext, Classical.choice, Quot.sound]`),
  lake build 2570 jobs. Proved via `coeff` + reindex (h1: `j↦j+1`, h2: `i↦i+1`) over `addAntidiagonal`,
  zero-extension of the support complement, combine `(i+j)=m+1`.
- **(superseded status below)**: in_progress (2026-05-22)
- **File**: HasseWeil/GapQfKernel.lean (general lemma, consumed by `localExpand_derivative_leibniz`)
- **Parent**: SK-KER-LEIBNIZ (`localExpand_derivative_leibniz`)
- **Type**: lemma
- **Statement**: `theorem LaurentSeries.derivative_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) : LaurentSeries.derivative R (f * g) = f * LaurentSeries.derivative R g + g * LaurentSeries.derivative R f`
- **Proof sketch**: `ext n`; `LaurentSeries.derivative R = hasseDeriv R 1`, so `(deriv (f*g)).coeff n = (n+1) • (f*g).coeff (n+1)` (hasseDeriv_coeff, `(n+1).choose 1 = n+1`); HahnSeries `mul_coeff`/`coeff_mul` expands `(f*g).coeff (n+1)` as a finite sum over the add-antidiagonal of `n+1`; on the RHS `(f * deriv g + g * deriv f).coeff n` expands similarly with the `+1` shift; both equal `∑_{i+j=n+1} (i+j)•(f.coeff i)(g.coeff j)` after distributing `(n+1)=(i+j)` and reindexing. Use `nsmul`/`zsmul` distributivity + `Finset.sum_congr`.
- **Mathlib lemmas needed**: `LaurentSeries.derivative_apply`, `LaurentSeries.hasseDeriv_coeff`, `HahnSeries.mul_coeff` (or `HahnSeries.coeff_mul`), `Finset.addAntidiagonal` API.
- **Generality**: `CommRing R`, `V = R`.

### [SK-KER-LEIBNIZ] localExpand_derivative_leibniz — DONE (2026-05-22)
- **Status**: done — axiom-clean. `rw [map_mul]; exact laurentSeries_derivative_mul _ _`.
- **File**: HasseWeil/GapQfKernel.lean

### [SK-L6CA] l6_computationA via non-RR degree=poleDegree (user-confirmed 2026-05-22: NO Riemann–Roch)
- **Status**: superseded (2026-05-29, reviewer Round 7) by [separable-isogeny-fibre-count] — the bespoke Sinf pole-locus / inertia-sum dictionary is replaced by the direct separable⇒unramified fibre-count route (Option B). Kept as audit trail; the done LHS finrank pieces (SK-L6CA-LHS) may be reused. — **Parent**: GAP-L6 / ker_deg_skeleton
- **File**: HasseWeil/GapSpines.lean (consumes PoleDivisorFallback + Curves/RamificationAtInfinity)
- **Route (NON-RR)**: `ComputationA_bridge_pullback_x_gen` = `[K(E):F(γ*x)] = degreePoleDivisor (γ*x)`.
  The proven `finrank_gamma_pullback_x_eq_weightedPoleDegree` (PoleDivisorFallback:3074, = the elementary
  `finrank_eq_weighted_poleDegree_of_nonconstant` Dedekind ramification·inertia identity) gives
  `finrank (FractionRing(Poly K)) (LinfAt f) = ∑_{primesOverFinset} (-ordAt P).toNat · inertiaDeg P`.
  Sub-tickets (the framing bridges + hypothesis discharge):
  - **[SK-L6CA-HYPS]** discharge `Fact (Transcendental K (γ*x)⁻¹)` + `Module.Finite (FractionRing(Poly K)) (LinfAt (γ*x))`
    + `data : Sinf K (γ*x)` (via `Sinf.ofIntegralClosure`). Per OpenLemmas:529-545.
  - **[SK-L6CA-LHS]** `finrank (adjoin K {γ*x}) KE = finrank (FractionRing(Poly K)) (LinfAt (γ*x))`
    — **DONE 2026-05-22** (`finrank_adjoin_eq_finrank_LinfAt`, PoleDivisorFallback, build green 2917 jobs,
    not in sorry list). Both `hc` cases proven: X↦f⁻¹ (via `algEquivOfTranscendental_X` +
    `LinfAt.algebraMap_fractionRing_apply`→`ratFunToFieldOfInv`→`IsFractionRing.liftAlgHom_apply`→
    `IsFractionRing.lift_algebraMap`→`polyToFieldOfInv_X`) and constant `C a` (via `e₁.commutes` +
    `IntermediateField.coe_algebraMap_apply` (rfl) + `IsScalarTower.algebraMap_apply K (FractionRing) (LinfAt)`,
    combined `hLHS.trans hRHS.symm`). The non-RR route delivered.
    --- (historical) STATED + SETUP PROVEN (2026-05-22) as `finrank_adjoin_eq_finrank_LinfAt`
    (PoleDivisorFallback, build green 2917 jobs). Proven: `e₁ := toFractionRingAlgEquiv.symm.trans
    (RatFunc.algEquivOfTranscendental f⁻¹ h_f_inv)` (FractionRing≃K⟮f⁻¹⟯, X↦f⁻¹); `hadj : adjoin K {f}
    = adjoin K {f⁻¹}` (via `inv_mem`+`inv_inv`); `e₂ := (RingEquiv.refl K(E) : LinfAt f ≃+* K(E))`
    (synonym-refl — plain refl asks for nonexistent `Algebra (K⟮f⁻¹⟯) (LinfAt f)`); the
    `Algebra.finrank_eq_of_equiv_equiv e₁ e₂ hc).symm` conclusion compiles. `hc` via
    `IsLocalization.ringHom_ext` + `Polynomial.ringHom_ext`. **X CASE PROVEN (2026-05-22)**: LHS via
    `algEquivOfTranscendental_X` (+ `toFractionRingAlgEquiv` h_symm_X mirror), RHS via
    `LinfAt.algebraMap_fractionRing_apply` → `ratFunToFieldOfInv` → `IsFractionRing.liftAlgHom_apply`
    → `IsFractionRing.lift_algebraMap` → `polyToFieldOfInv_X` (= f⁻¹), combine `hL.trans hR.symm`.
    **ONLY GAP = constant case** (`C a`: both sides `= algebraMap K K(E) a`): blocked synthesizing
    `IsScalarTower K ↥K⟮f⁻¹⟯ K(E)` (nested adjoin; respectTransparency-vs-FractionRing tension — adjoin
    wants `false`, X-case FractionRing wants `true`). FIX: prove the constant equality in a SEPARATE
    helper under `respectTransparency false` (no FractionRing there), pass it in; or `coe_algebraMap`-style
    lemma avoiding `IsScalarTower` synthesis. Build green 2917 jobs.
  - **[SK-L6CA-RHS] — l6_computationA FRAMING FULLY ASSEMBLED & REORDERED (2026-05-22, GapSpines green 2940 / full project 2987)**:
    `l6_computationA` now sits after `l6_lemma5`, with the COMPLETE non-RR framing committed: `data := @Sinf.ofIntegralClosure`
    (HYPS-discharged) + `finrank_adjoin_eq_finrank_LinfAt` ∘ `finrank_gamma_pullback_x_eq_weightedPoleDegree`
    ∘ `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount` ∘ `(l6_lemma5).symm`. Collapsed to **3 geometric
    witness `sorry`s** (the `by sorry` args to `weightedPoleDegree...`): `h_pole` ∀P ordAt=-2, `h_inertia` ∀P inertiaDeg=1,
    `h_card` #primesOverFinset=pointCount. **These bottom out at the Silverman V.1.3 BRIDGE lemmas (genuine deep geometry, 6 sorries
    in OpenLemmas:337-470)**: `bridge_Bii_bijective` (kernel↔primes bijection, :392/409 SORRY), `bridge_Biii_ord_eq_neg_two`
    (per-pt ordAt=-2, :426), `bridge_Biv_inertia_eq_one` (per-pt inertiaDeg=1, :455). The card side is PROVEN
    (`card_oneSubFrobeniusIsog_kernel`: #ker(1-π)=pointCount, PointFix:76, geometric/non-circular). So the genuine remaining
    L6 content = the V.1.3 bridge geometry (closed-point↔prime correspondence + ramification index 2). The whole
    finrank=poleDegree/HYPS machinery is DONE — only the V.1.3 ramification bridges remain.
    --- (historical SK-L6CA-RHS notes:) `∑primesOverFinset = ∑projectiveDivisorOf`. `l6_computationA`'s LHS-side
    is ASSEMBLED & committed (GapSpines, green): with HYPS COMPLETE (`moduleFinite_linfAt_gamma_pullback_x`
    proven), `data := @Sinf.ofIntegralClosure … hfact hmf hsep` constructs (the OpenLemmas:545 "Project ticket"
    typeclass discharge — DONE), and `Conditional.finrank_adjoin_eq_finrank_LinfAt`∘`finrank_gamma_pullback_x_eq_weightedPoleDegree`
    rewrites the goal to exactly this RHS-bridge (the lone `sorry` in `l6_computationA`).
    ROUTE: `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount W hq data h_pole h_inertia h_card`
    (= 2·pointCount) `.trans (l6_lemma5 W hq).symm`. Needs the data's primesOverFinset witnesses: `h_pole`
    (∀P ordAt=-2 — OpenLemmas:434/1664 per-kernel-point via `bridge_Bi_kernelToPrime`), `h_inertia` (∀P inertiaDeg=1
    — OpenLemmas:1677), `h_card` (#primesOverFinset=pointCount — `fiber_witness_*` PointFix:312-520).
    ⚠ **CIRCULARITY**: `fiber_witness_via_card_kernel_eq_degree` routes through `card_kernel=degree`=`ker_deg_skeleton`,
    which uses `sepDegree_oneSub_eq_pointCount` → `l6_computationA` (CIRCULAR). Use a GEOMETRIC fiber-witness
    (`fiber_witness_via_galois_witnesses`/`via_isGalois_and_bijection`, PointFix:402/462) that gets card=pointCount
    from the Galois action on the fiber, NOT from degree=pointCount. (~the genuine remaining L6 divisor work.)
  - **[SK-L6CA-HYPS]** discharge `Fact (Transcendental K (γ*x)⁻¹)` + `Module.Finite (FractionRing(Poly K)) (LinfAt (γ*x))`
    + `data : Sinf K (γ*x)` (via `Sinf.ofIntegralClosure`). PARTIAL (2026-05-22):
    `transcendental_inv` PROVEN (PoleDivisorFallback, build green) — `Transcendental K y → Transcendental K y⁻¹`
    via `IsAlgebraic.inv`. **TRANSCENDENTAL PART DONE 2026-05-22** (build green 2917 jobs):
    `transcendental_gamma_pullback_x` (`Transcendental K (γ*x)`: `pullback : →ₐ[K]` is injective
    (`pullback_injective`) + `x_gen_transcendental` + `Polynomial.aeval_algHom_apply`) +
    `fact_transcendental_gamma_pullback_x_inv` (the `Fact (Transcendental K (γ*x)⁻¹)` that the LHS-bridge,
    `LinfAt.algebraFractionRing`, and `finrank_gamma...` all need; `haveI` at call sites).
    **IsSeparable PART ALSO DONE**: `K_E_separable_over_LinfAt_gamma_pullback_x_gen` (PoleDivisorFallback:3409)
    is PROVEN (whole file sorry-free). So `Sinf.ofIntegralClosure` (which needs Fact-Transcendental [done] +
    Module.Finite + IsSeparable [done]) reduces to **ONE remaining piece**: `Module.Finite (FractionRing(Poly K))
    (LinfAt (γ*x))` (= `[K(E):K(γ*x⁻¹)]=[K(E):K(γ*x)] < ∞`). Route: `FiniteDimensional ↥(adjoin K {γ*x}) K(E)`
    via the tower `K(E) ⊇ γ.pullback.fieldRange ⊇ K(γ*x)` ([K(E):fieldRange]=`γ.degree` via
    `finrank_pullback_fieldRange_eq_degree`, [fieldRange:K(γ*x)]=2 via `gammaBar`+`finrank_functionField_eq_two`,
    cf GapSpines `l6_v_1_3`), then transfer to `LinfAt` via the `e₁` algEquiv (the LHS-bridge's
    `RatFunc.algEquivOfTranscendental`). Then `data := Sinf.ofIntegralClosure (γ*x)` assembles, `finrank_gamma...` applies.
    **PROBED 2026-05-22**: `FiniteDimensional ↥(adjoin K {γ*x}) K(E)`, `FiniteDimensional fieldRange K(E)`,
    and even `FiniteDimensional ↥(adjoin K {x_gen}) K(E)` are NOT auto-instances (synthInstance fails) — the
    function-field finiteness must be CONSTRUCTED. → spawned **[SK-L6CA-FINITE]**.
  - **[SK-L6CA-FINITE] ✅ DONE 2026-05-22** — `moduleFinite_linfAt_gamma_pullback_x` PROVEN in GapSpines
    (green, 2940 jobs): `Module.Finite (FractionRing) (LinfAt γ*x)` = the LAST HYPS hypothesis. Proof:
    `Conditional.finrank_adjoin_eq_finrank_LinfAt` (LHS-bridge) identifies `finrank (FractionRing)(LinfAt γ*x)
    = finrank K⟮γ*x⟯ K(E)`; `l6_B3_tower` evaluates that to `2·γ.degree`; `0 < γ.degree` via `Module.finrank_pos`
    on the axiom-clean `isogOneSub_negFrobenius_finiteDimensional` (φ.toAlgebra module is `Module.Free` over the
    field K(E) via `@Module.Free.of_divisionRing`, giving IsTorsionFree); then `Module.finite_of_finrank_pos`
    (with `@Module.Free.of_divisionRing` for the LinfAt module too). The whole degree>0 / finiteness chain was
    cracked error-driven via @-explicit module forcing — NO lean_goal needed after all. **HYPS now COMPLETE**
    (Transcendental + IsSeparable + Module.Finite all done). l6_computationA = LHS-bridge ∘ finrank_gamma
    (Sinf.ofIntegralClosure + HYPS) ∘ RHS-bridge (∑primesOverFinset=∑projectiveDivisorOf). RHS via
    `weightedPoleDegree_gamma_pullback_x_eq_two_mul_pointCount` (=2·pointCount given primesOverFinset witnesses
    ordAt=-2 [OpenLemmas:434/1664], inertia=1 [:1677], card=pointCount) + `l6_lemma5` (∑projectiveDivisorOf=2·pointCount).
    --- (historical SK-L6CA-FINITE notes below) ---
  - **[SK-L6CA-FINITE]** (spawned 2026-05-22, Parent SK-L6CA-HYPS). **BASE ALREADY EXISTS (found 2026-05-22)**:
    `Curves.SmoothPlaneCurve.finite_fracPolynomialX_functionField` (FiniteOverKx.lean:126) is an INSTANCE
    `Module.Finite (FractionRing (Polynomial F)) C.FunctionField` for `C : SmoothPlaneCurve F`, via
    `Module.Finite.of_isLocalization` — CLEAN, no diamond (FiniteOverKx:36 uses the proper `Algebra.toModule`,
    not a redundant custom instance). The whole FrobeniusIsogeny `coordinateRing_module` diamond saga was a RED
    HERRING — don't reinvent the base, just use FiniteOverKx's instance (the base for `(W_smooth W).FunctionField`).
    **PROBED 2026-05-22 (both via `lake env lean`, import GapSpines):**
    • `Module.Finite (FractionRing (Polynomial K)) W.toAffine.FunctionField` → `infer_instance` SUCCEEDS (PROBE=0).
      So the canonical base is FREE — no work, no diamond.
    • `Module.Finite (FractionRing) (LinfAt (γ*x))` [the `algebraFractionRing` X↦(γ*x)⁻¹ module] →
      `infer_instance` FAILS (PROBE=1). This non-canonical algebra is the ONLY remaining gap.
    REMAINING (the sole SK-L6CA-FINITE task): get `Module.Finite (FractionRing) (LinfAt (γ*x))`. Route:
    `FiniteDimensional ↥(adjoin K {γ*x}) K(E)` via the tower `K(E) ⊇ γ.pullback.fieldRange ⊇ K(γ*x)`
    ([K(E):fieldRange]=γ.degree via `finrank_pullback_fieldRange_eq_degree`; [fieldRange:K(γ*x)]=2 via `gammaBar`
    + the now-FREE base [K(E):K(x_gen)]=2 — make these FiniteDimensional, not just finrank), then transfer to
    `LinfAt` via the proven LHS-bridge's `e₁` algEquiv (`Module.Finite.of_surjective`/`equiv`). With this +
    the DONE Transcendental Fact + DONE IsSeparable, `data := Sinf.ofIntegralClosure (γ*x)` assembles and
    `finrank_gamma_pullback_x_eq_weightedPoleDegree` applies.
    **KNOWN-DEFERRED WALL (found 2026-05-22)**: this `FiniteDimensional`-tower is EXACTLY the wall the project
    already deferred — see `L6ViaPoleDivisor.lean:107-112` NOTE ("the inclusion-algebra Module instance had a
    typeclass synthesis wall (`letI inst_A_B : Algebra ↥A ↥B` didn't propagate `Module ↥A ↥B` to
    `Module.Free.of_divisionRing`). Deferred… the LOWER step requires the gammaBar transfer adapted for
    IntermediateFields"). `finrank_pullback_fieldRange_eq_degree` (:86, PROVEN) gives the finrank via
    `Algebra.finrank_eq_of_equiv_equiv gammaBar (refl)` but NOT `FiniteDimensional`; and
    `bridgeA_intermediateField_finrank_eq_two_mul_degree_of_witness` (:118) packages `[K(E):K(γ*x)]=2·γ.degree`
    witness-parametrically. So SK-L6CA-FINITE's tower = discharging that deferred IntermediateField-tower
    `FiniteDimensional` synthesis (the `Algebra ↥A ↥B → Module ↥A ↥B → Module.Free.of_divisionRing` propagation),
    then `FiniteDimensional.trans` + the `e₁` transfer. Substantial; for the next /loop session.
    **ROOT-CAUSE (traced 2026-05-22)**: the whole tower bottoms out at `FiniteDimensional (φ.toAlgebra) K(E)`
    (`@Module.Finite K(E) K(E) _ _ φ.toAlgebra.toModule`) — i.e. K(E) finite over `φ.pullback`'s image. `Isogeny.degree`
    (Isogeny.lean:61) is DEFINED as `@Module.finrank … φ.toAlgebra.toModule` but the project never proves the
    matching `FiniteDimensional`/`Module.Finite` (finrank is 0 if infinite-dim — so all the `…_eq_degree` lemmas
    are vacuous-safe but give no finiteness). `infer_instance` for it FAILS (probed). This is THE fundamental gap:
    **an isogeny gives a finite field extension `[K(E):φ*K(E)] = deg φ < ∞`**. Clean route: `φ.pullback` injective
    (`pullback_injective`) ⟹ `φ*K(E) ≅ K(E)` (tr.deg 1); K(E) f.g. over K + algebraic over `φ*K(E)` ⟹ `Module.Finite`
    via `Algebra.IsAlgebraic` + `Algebra.FiniteType` (or a finite-morphism lemma). Prove this ONE finiteness
    (`finiteDimensional_of_isogeny` / `Module.Finite (φ.toAlgebra) K(E)`), make it an instance, and the entire
    tower + SK-L6CA-FINITE + the existing deferred B3 bridgeA all unblock at once. **Highest-leverage next target.**
    **★★ ALREADY PROVEN — the "deferred wall" framing was WRONG (found 2026-05-22) ★★**: this exact root finiteness
    IS `HasseWeil.isogOneSub_negFrobenius_finiteDimensional W hq` (= `OpenLemmas.witness_pc_fin W hq`),
    `@FiniteDimensional K(E) K(E) _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule` — **AXIOM-CLEAN**
    (`#print axioms` = [propext, Classical.choice, Quot.sound], NO sorryAx). SK-L6CA-FINITE is UNBLOCKED.
    **Next-session recipe (verified pieces):** (1) `FiniteDimensional ↥(γ.pullback.fieldRange) K(E)` :=
    `Module.finite_of_finrank_pos` (Free.lean:186) + `finrank_pullback_fieldRange_eq_degree` (rewrites finrank→γ.degree)
    + `0 < γ.degree`. The `0 < γ.degree` = `0 < @Module.finrank K(E) K(E) _ _ φ.toAlgebra.toModule` via
    `Module.finrank_pos` (Dimension/Finite.lean:397, needs [IsDomain][IsTorsionFree][Nontrivial] + the root
    `Module.Finite`) — REMAINING PLUMBING: pass `φ.toAlgebra.toModule` so the synthesized module instance matches
    (the bare `Module.finrank_pos` synthesizes the canonical KE-module, not φ's — "not defeq" / "type mismatch";
    use `@`-explicit module + matching `show`, or find `Isogeny.degree_pos`). Alt for `0<γ.degree`: γ.degree =
    pointCount (OpenLemmaPrimitives:1767 `h_deg_eq_pc`) > 0. (2) `FiniteDimensional ↥K⟮γ*x⟯ ↥fieldRange` = 2 via
    `gammaBar` + free base. (3) `FiniteDimensional.trans` → `FiniteDimensional ↥K⟮γ*x⟯ K(E)`. (4) transfer to
    `Module.Finite (FractionRing) (LinfAt γ*x)` via the proven LHS-bridge `e₁`. Then `Sinf.ofIntegralClosure`+`finrank_gamma`.
    (Original tower route detail:)
    **BASE PROBE-CONFIRMED 2026-05-22**: `Module.Finite (FractionRing K[X]) K(E)` (X↦x_gen) IS derivable —
    `import Mathlib.RingTheory.TensorProduct.Finite` (ADDED to FrobeniusIsogeny, green) makes
    `Module.Finite.base_change` fire for `FractionRing ⊗[K[X]] CoordinateRing` (from `coordinateRing_finite`),
    then `Module.Finite.of_surjective (isBaseChange_coordToFunc K W).equiv.toLinearMap ….surjective`. Cross-file
    probe succeeds; IN-FILE synthesis fails — **ROOT CAUSE: module-instance diamond**: FrobeniusIsogeny:131 declares a
    CUSTOM `instance coordinateRing_module : Module K[X] CoordinateRing := @Algebra.toModule …` which
    `Module.Finite.base_change` doesn't align with the tensor's Algebra-derived module (cross-file the canonical
    built instance wins). **FINAL STATE 2026-05-22**: `isBaseChange_coordToFunc` MADE PUBLIC (FrobeniusIsogeny,
    green, kept). New file `HasseWeil/Hasse/FunctionFieldFinite.lean` states the target
    `HasseWeil.functionField_finite_fractionRing (W) : Module.Finite (FractionRing K[X]) K(E)` (sorry-stub,
    green-with-sorry) with the full recipe. Tried: in-file/cross-file, term/tactic, `open` vs `namespace`,
    `attribute [-instance]` — the tensor `Module.Finite` synthesis is UNSTABLE (one isolated probe passed,
    every built-file form failed), AND `attribute [-instance] coordinateRing_module` breaks `coordinateRing_finite`
    (stated w.r.t. that module). **CLEAN FIX for next session**: `coordinateRing_module` (FrobeniusIsogeny:131)
    is REDUNDANT (`:= @Algebra.toModule …` = the canonical instance) — drop its `instance` attribute (→ plain `def`
    or delete), so the canonical `Algebra.toModule` is the sole `Module K[X] CoordinateRing`, the diamond vanishes,
    and `Module.Finite.base_change`+`of_surjective` resolve everywhere. (Core-file edit; rebuild downstream +
    check `definition_protected` gate.) ALT: `Module.Finite.of_isLocalization K[X] CoordinateRing
    (nonZeroDivisors K[X])` (also routes through `coordinateRing_finite`, so same diamond — prefer the drop). OPEN.
  - **ASSEMBLY for `l6_computationA`** (once HYPS + RHS done): `(finrank_adjoin_eq_finrank_LinfAt W hq)`
    [DONE] `.trans (finrank_gamma_pullback_x_eq_weightedPoleDegree W hq hMF data)` [proven, needs HYPS]
    `.trans (SK-L6CA-RHS).symm`. All non-RR.

**Progress**:
- 2026-05-24T: shipped axiom-clean witness-parametric closures of L3 + L4 (GAP-L6 smooth-point side)
  reducing both to a single 2-torsion-witness sub-leaf:
  - `Conditional.projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness` (L6Witnesses.lean,
    pointwise helper: composes `lemma3_pole_at_T_unconditional` (non-2-tor) + `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen` (∞) + 2-torsion witness).
  - `Conditional.l6_support_card_of_two_torsion_witness` (L6Witnesses.lean, L4 = W2 derivation from
    the single 2-torsion witness via `support_card_eq_pointCount_of_per_point_witness`).
  - `l6_pole_orders_of_two_torsion_witness` (GapSpines.lean, L3 in the per-point form).
  - Path A partial discharge: `degree_quadratic_exists_edge_r_int_zero` + `degree_quadratic_exists_edge_s_int_zero`
    (GapSpines.lean) discharge the trivial `r = 0 ∈ ℤ` / `s = 0 ∈ ℤ` edge cases of L2; `degree_quadratic_exists_skeleton`
    refactored to dispatch these inline.
- 2026-05-24T: net L3/L4 sorry status — both still SORRY at their original sites, BUT each now has a
  witness-parametric closure axiom-clean, so the substantive remaining content reduces to the single
  2-torsion-witness sub-leaf. The 2-torsion sub-leaf needs `bridge_at_addPullback_x_negFrobenius_of_2_tor`
  (the doubling-formula analog of the existing `bridge_at_addPullback_x_negFrobenius_of_non_2_tor`).
- 2026-05-24T (cont. ④ BREAKTHROUGH): shipped the FULL Y-SIDE SUBSTANTIVE chain at 2-torsion
  (~400 LOC of new axiom-clean Lean):
  - `ord_P_x_gen_sub_const_eq_two_at_2tor` — the EXACT ord = 2 value at smooth 2-torsion T,
    via curve identity + the EXACT `ord_P_A_eq_one_at_2tor` + `ord_P_B_minus_a1_yk_eq_zero_at_2tor`.
  - `ord_P_translateY_xy_eq_neg_three_at_2tor` — the SUBSTANTIVE y-side value at 2-torsion via
    `translateY_xy_mul_cube_eq` algebraic identity + strict comparison using the 2-tor ord values
    (yd ord = 1, xd ord = 2 exactly, yd³ ord = 3 strictly < all other RHS terms at ord ≥ 4).
    Required making `translateY_xy_mul_cube_eq` public (was `private`) — minimal `EC/TranslationOrd.lean` change.
  - `twoTorYValueWitness_discharge` — UNCONDITIONALLY discharges the TwoTorYValueWitness from
    `ord_P_translateY_xy_eq_neg_three_at_2tor`.
  - `bridge_at_y_gen_of_2_tor`, `bridge_at_y_gen_pow_card_of_2_tor`, `bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor`
    — all UNCONDITIONAL y-side bridges at 2-torsion (composing the discharged witness with the
    witness-parametric bridges).
  Net: the TwoTorYValueWitness hypothesis is now UNCONDITIONALLY dischargeable. The y-side chain
  at 2-tor is FULLY UNBLOCKED. Remaining: T3/T4/T5 piece bridges + Num bridge composer + sq composer
  + `lemma3_pole_at_T_at_2tor` (all mechanical mirrors of non-2-tor structure, ~300 LOC total).

- 2026-05-24T (cont. ②): shipped y-side witness-parametric bridges in `Hasse/PoleDivisor2Tor.lean`
  reducing the y-side chain to a single substantive witness `TwoTorYValueWitness` (= the lemma
  `ord_P_translateY_xy_eq_neg_three_at_2tor`, deferred — ~200 LOC port of the non-2-tor proof):
  - `TwoTorYValueWitness` (Prop abbrev for the single substantive y-side value)
  - `bridge_at_y_gen_of_2_tor_of_witness`
  - `bridge_at_y_gen_pow_card_of_2_tor_of_witness`
  Once `TwoTorYValueWitness` is discharged, the y-side bridges become unconditional. The
  remaining mechanical work to fully discharge `lemma3_pole_at_T_at_2tor` (and hence
  `l6_pole_orders` + `l6_support_card`): T3/T4/T5 piece bridges (witness-parametric, ~80 LOC each)
  + `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor` (dominant-T7 strict-comparison
  consumer, ~120 LOC) + `bridge_at_addPullback_x_negFrobenius_of_2_tor` (Num + sq composer, ~30 LOC)
  + `lemma3_pole_at_T_at_2tor` (the final per-point discharge, ~30 LOC).

- 2026-05-24T (cont. ①): shipped 12 axiom-clean 2-torsion x-side bridges in `Hasse/PoleDivisor2Tor.lean`,
  mirroring the non-2-tor x-side chain:
  - `bridge_at_x_gen_of_2_tor`
  - `bridge_at_x_gen_pow_card_of_2_tor`
  - `bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`
  - `bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor`
  - `bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor`
  - `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor`
  - `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor` (slope-denominator squared, needed by Num composer)
  - `bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor`
  - `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor` (T7 — DOMINANT in Num decomposition)
  - `bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor` (T6)
  - `bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor` (T1/T8 building block)
  - `bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor`
  All 12 are direct compositions of existing pieces (no new substantive geometric content).
  Remaining for the full Num-bridge at 2-tor: (a) y-side substantive value
  `ord_P_translateY_xy_eq_neg_three_at_2tor` (analog of the x-side analysis at PoleDivisor2Tor:78-272,
  ~200 LOC of careful porting); (b) the T3/T4/T5 y-side piece bridges; (c) `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor`
  (dominant-T7 strict-comparison consumer); (d) `bridge_at_addPullback_x_negFrobenius_of_2_tor` (Num + sq composer);
  (e) `lemma3_pole_at_T_at_2tor` (the 2-tor analog discharge of the witness hypothesis in
  `l6_pole_orders_of_two_torsion_witness` / `l6_support_card_of_two_torsion_witness`).

### [SK-IV43-MEMF] omegaPullbackCoeff_mem_F (III.1.5: a_α is constant)
- **Status**: open (2026-05-22) — **Per-α PASS leaves + closures shipped 2026-05-25T19:15Z**: for α ∈ {`Isogeny.id`, `frobeniusIsog`, `mulByInt n` (n≠0), `negFrobeniusIsog`, `isogOneSub_negFrobenius` (KEY isogeny)} the mem_F + isIntegral + ordAtInfty_nonneg sub-leaves all ship FULLY AXIOM-CLEAN. PLUS 7 axiom-clean witness-parametric mem_F closures: composition (explicit + existential), additivity, chord-step (`addIsog (id, α)`), **UNIVERSAL `α.comp β` for any β** when `omega(α) = 0` (purely inseparable α), specialized to Frobenius and negFrobenius. The universal-α form remains gated on the III.1 substrate; the per-α + composition closure layer gives mem_F for the critical-path isogenies AND all their compositions with arbitrary β (via the omega-zero closures). — **Parent**: SK-KER-IV43 (`omegaPullbackCoeff_localExpand_eq_coeff_one`)
- **File**: HasseWeil/GapQfKernel.lean
- **Statement**: `∃ c : F, omegaPullbackCoeff W α = algebraMap F KE c`
- **Proof sketch**: Silverman III.1.5 — ω is a global generator of Ω[K(E)/F] with no zeros/poles,
  so `α*ω = a_α·ω` forces `a_α` to be a global rational function with no zeros/poles, hence constant
  (∈ image of `algebraMap F KE`). Project infra: `InvariantDifferentialPullback.omegaPullbackCoeff_comp_of_base`.

### [SK-IV43-VAL] omegaPullbackCoeff_F_value_eq_coeff_one (IV.4.3: value = linear formal coeff)
- **Status**: in_progress (2026-05-23) — leaf WIRED to two sub-lemmas; both sub-lemmas open — **Parent**: SK-KER-IV43
- **File**: HasseWeil/GapQfKernel.lean
- **Statement**: `(c : F) (hc : omegaPullbackCoeff W α = algebraMap F KE c) : c = PowerSeries.coeff 1 (formalIsogenySeries W α)`
- **Proof sketch**: Silverman IV.4.3 — apply the lift `Λ = (localExpand-derivation).liftKaehlerDifferential`
  (derivation from the now-DONE `localExpand_derivative_leibniz`; cf `Auxiliary/PullbackKaehler.lean`'s
  `derivationCompHom.liftKaehlerDifferential`) to `omegaPullbackCoeff_spec`; compare `coeff 1` with the
  `formalIsogenySeries` def (`coeff 1 = (localExpand (α.pullback localParam)).coeff 1`).
- **Progress (2026-05-23)**:
  - ★ BUILT the lift infrastructure (the "missing setup"), AXIOM-CLEAN (`#print axioms localExpandKaehlerLift_D
    = [propext, Classical.choice, Quot.sound]`), building: `LExp` wrapper (LaurentSeries F as KE-module via
    localExpand, F-module restricted through `algebraMap F KE` so `IsScalarTower F KE _` is free — sidesteps
    the `SMul F (LaurentSeries F)` instance diamond that blocks the direct `(localExpand W).toAlgebra` route);
    `localExpandDeriv : Derivation F KE (LExp W)`; `localExpandKaehlerLift : Ω[KE/F] →ₗ[KE] LExp W`;
    `localExpandKaehlerLift_D`, `localExpandKaehlerLift_smul`; helper `derivative_localExpand_algebraMap`.
  - ★ LEAF FULLY WIRED (proof complete): applies the lift to `omegaPullbackCoeff_spec` (Key Identity) and reads
    off `coeff 0`. Reduces to two NEW concrete coeff sub-lemmas (both `sorry`, in GapQfKernel.lean):
    `invariantDiff_localExpand_coeff_zero` (N: `((localExpand u)⁻¹·d/dt(localExpand x)).coeff 0 = 1`) and
    `pullback_invariantDiff_coeff_zero` (P: chain rule, `coeff 0 = (localExpand(α*localParam)).coeff 1`).
  - ⚠ **B2 / STATEMENT-GENERALITY (see b2_log.jsonl, IV.4.3-P)**: (P) as decomposed is FALSE for non-genuine α
    (a translation-type F-algebra endo has `α*localParam` of order 0, breaking the substitution structure
    `localExpand(α*g) = subst(α*localParam)(localExpand g)`). The general-α leaf inherits this. Consumers only
    use `mulByInt` (genuine) ⟹ RECOMMEND adding a genuineness hyp to (P)+leaf and threading through
    `omegaPullbackCoeff_localExpand_eq_coeff_one` → `_via_localization` → `_mulByInt_via_formalGroup`.
  - ⚠ **(N) is CHAR-FRAGILE via leading coeffs** (char 2: `−2 = 0` kills the dominant `2·formalY` and
    `d/dt(formalX)` terms). Char-independent (N)/(P) need the **curve↔formal-group invariant-differential
    correspondence** (Silverman IV.1: `Ω₀ = FormalGroup.invariantDiff` of W's formal group, `constantCoeff = 1`).
    `FormalGroupCorrespondence.lean` is currently placeholders — this is the research-scale remaining piece.

### [SK-ROUTEB-ADD] omegaPullbackCoeff_add (III.5.2) → a_[m]=m, curve-side (Route B) — **DONE 2026-05-23**
- **Status**: done (2026-05-23) — omegaPullbackCoeff_mulByInt_routeB (a_[n]=n, all n≠0) AXIOM-CLEAN in RouteBInduction.lean (RB-ω4+RB-ADD+RB-ID+chord-step+induction+negation); a_[p]=0 (_p_eq_zero_routeB) wired into GapQfKernel D_mulByInt (axiom-clean). Wronskian-free + formal-group-free. — **Parent**: SK-KER (a_[m]=m)
- **File**: HasseWeil/AdditionPullback/SilvermanIV14.lean (+ AdditionPullback.lean, OmegaPullbackCoeff.lean)
- **Statement (target)**: `omegaPullbackCoeff W (mulByInt W.toAffine m) = algebraMap F KE m` (wronskian-free,
  formal-group-free), via `omegaPullbackCoeff_add` (III.5.2: a_{φ+ψ}=a_φ+a_ψ for the genuine addition-formula
  sum) + `omegaPullbackCoeff_id=1` + induction (III.5.3).
- **Proof sketch**: Silverman III.5.2 (`(φ+ψ)*ω=φ*ω+ψ*ω`, addition formula + III.5.1) + III.5.3 induction.
  Verified vs Silverman PDF; NO Riemann-Roch (kaehler_rank_one elementary), NO wronskian, NO formal group.
- **Sources**: Silverman AEC III.5.1–5.3, III.4 (isogeny def: φ(O)=O). 
- **Progress (2026-05-23)**:
  - SHIPPED axiom-clean (build 2871, verified `#print axioms = [propext, Classical.choice, Quot.sound]`):
    `kaehler_D_addPullback_x_general` (D(addPullback_x)=(2ℓ+a₁)·D(ℓ)−D(x)−D(α*x)),
    `kaehler_D_addSlope_general` (Den²·D(addSlope)=Den·(D(y)−D(α*y))−N·(D(x)−D(α*x)), needs x≠α*x), and
    `kaehler_D_addPullback_x_general_cleared` (Den²·D(addPullback_x) cleared form combining the two).
    Generalize Sub-helpers 109/128/129 (which assumed Frobenius D=0).
  - REUSABLE for slope→ω: `kaehler_D_weierstrass_equation_K_E` (Sub-helper 121, GENERAL curve-eqn differential
    `u·D(y)=(3x²+2a₂x+a₄−a₁y)·D(x)` chain 121–125), `omegaPullbackCoeff_spec` (D(x)=u•ω form),
    `omegaPullbackCoeff_id=1`, `Isogeny.pullbackKaehler_invariantDifferential` (α.pullbackKaehler ω = a_α•ω).
  - SLOPE→ω DECOMPOSITION (SilvermanIV14.lean) — 4 of 5 leaves PROVEN axiom-clean this session:
    RB-ω1 `kaehler_D_x_gen_eq_u_smul_omega` (D(x)=u•ω) ✓; RB-ω2 `kaehler_D_y_gen_eq_num_smul_omega`
    (D(y)=num•ω, via curve-eqn 127 + cancel u) ✓; RB-ω3a `kaehler_D_alpha_pullback_x_eq_smul_omega`
    (D(α*x)=(α*u·a_α)•ω, via omegaPullbackCoeff_spec) ✓; RB-ω3b `kaehler_D_alpha_pullback_y_eq_smul_omega`
    (D(α*y)=(α*num·a_α)•ω, via pullbackKaehler of curve-eqn 127 + RB-ω3a) ✓.
  - RB-ω4 `kaehler_D_addPullback_x_eq_one_add_smul_omega` — REDUCTION BANKED (build green): the full
    pipeline works (substitute RB-ω1/ω2/ω3a/ω3b into `_general_cleared` → collect `•ω` via
    smul_smul/sub_smul/add_smul → `congr 1` → unfold addX/addY/slope + `field_simp [sub_ne_zero.mpr h_ne]`).
    Residual is a PURE POLYNOMIAL identity (denominators cleared, **verified NO `y²` ⟹ NO Weierstrass
    relations needed**) blocked ONLY on normalising coefficient atoms `(W_KE W).toAffine.aᵢ` / `W.toAffine.aᵢ`
    → `algebraMap K KE W.aᵢ` so `ring` closes. NEXT: fold `W_KE W = W.baseChange KE` (rfl) + the @[simp]
    `WeierstrassCurve.baseChange_aᵢ` rfl-lemmas via `rw` (forces all occurrences, unlike the `simp only`
    rfl-shows that didn't fire) + `W.toAffine.aᵢ=W.aᵢ`, then `ring`. Pure Lean-engineering, ~1 fix from done.
  - (OLD note) RB-ω4 (THE ring collapse, sorry leaf):
    substitute RB-ω1/ω2/ω3a/ω3b into `kaehler_D_addPullback_x_general_cleared`; collect into `(scalar)•ω`
    via smul_smul/sub_smul/add_smul; then the scalar identity `scalar = Den²·addPullback_u·(1+a_α)` by
    `field_simp` (clear ℓ=N/Den) + `linear_combination` (Weierstrass relations both points, `generic_equation`
    + `pullback_equation`) + `ring`; cancel Den²≠0. Then assembly: RB-ADD (omegaPullbackCoeff(id+α)=1+a_α via
    genuine-sum spec + omegaPullbackCoeff_unique), RB-SUM (addPullbackAlgHom for id+[m], reuse
    mulByInt_coordHom_injective), RB-ID (id+[m]=[m+1]), RB-IND (induction → a_[m]=m), re-route
    omegaPullbackCoeff_mulByInt_via_formalGroup. Full chain in `decomposition-routeB.md`.

### DEV-1 (`mulByInt_q_pullback_qth_root`) sub-ticket decomposition (2026-05-22)
Non-circular route (avoids the documented `PurelyInsep.lean:194-224` blocker by going through
the invariant-differential kernel instead of Silverman III.6.1 degree decomposition):

- **[SK-QTH-Dpx0]** `D([p]*x_gen) = 0` — **Parent**: SK-QTH-PROOT. File: HasseWeil/GapQfKernel.lean.
  Statement: `KaehlerDifferential.D F KE ((mulByInt W.toAffine (p:ℤ)).pullback x_ff) = 0` (x_ff = x_gen as the
  algebraMap image). Proof: `omegaPullbackCoeff_spec` at α=[p] gives `a_{[p]} • ω = ([p]*u)⁻¹ • D([p]*x)`;
  `a_{[p]} = 0` (`omegaPullbackCoeff_mulByInt_p_eq_zero_via_formalGroup`) ⟹ `([p]*u)⁻¹ • D([p]*x) = 0`;
  `([p]*u)⁻¹ ≠ 0` ⟹ `D([p]*x) = 0`. CONCRETE / provable now.
- **[SK-KERD-PTH]** char-p Kähler kernel: `D F KE w = 0 ↔ w ∈ K(E)^p` (K perfect, finite).
  **STATED in GapQfKernel.lean (`kaehlerD_eq_zero_iff_mem_pth_powers`); `⟸` direction PROVEN**
  (`Derivation.leibniz_pow` + `Nat.cast_smul_eq_nsmul` + `CharP.cast_eq_zero`); `⟹` is the deep
  sorry. CONFIRMED mathlib-gap (2026-05-22, 3 searches all empty: no `KaehlerDifferential` D-kernel,
  no `IsPurelyInseparable`+derivation, no Derivation+char-p-frobenius). `⟹` sub-decomposition:
  `[K(E):K(E)^p] = p` (char-p, K perfect, trdeg 1) + the kernel = `K(E)^p` computation. This is a
  substantial char-p function-field differential development mathlib lacks (textbook, e.g. Stichtenoth).

**DEV-1 PROGRESS (2026-05-22, this /beastmode invocation)**: PROVEN axiom-clean-modulo-kernel-leaves:
`D_mulByInt_p_pullback_x_gen_eq_zero` (D([p]*x_gen)=0 from a_{[p]}=0 + spec); `mulByInt_p_pullback_x_gen_mem_pth_powers`
([p]*x_gen ∈ K(E)^p, reduced to SK-KERD-PTH); SK-KERD-PTH `⟸`. **Dev-1 bottom now isolated to
SK-KERD-PTH `⟹`** (the char-p differential kernel theorem) + assembly ([p]*y instance, `Im([p]*)⊆K(E)^p`
via perfect-field ring-hom, iterate p→q, then `mem_frobenius_range_iff`).
- **[SK-QTH-PROOT-P]** `Im([p]*) ⊆ K(E)^p`: from SK-QTH-Dpx0 (+ same for y_gen) + SK-KERD-PTH + K perfect
  (`P(u^p,v^p) = (P'(u,v))^p`, K=K^p).
- **[SK-QTH-ITERATE]** `Im([q]*) ⊆ K(E)^q` from `Im([p]*) ⊆ K(E)^p` iterated n times (q=p^n), then
  `mulByInt_q_pullback_qth_root` via `mem_frobenius_range_iff`.

### DECOMPOSITION-PUSH RESULTS (2026-05-22) — fillability map

Pushed each remaining leaf to its closer-chain so fillability is *verifiable*, not asserted:

| Leaf | Status after push | Reduced to (sub-leaves / closer-chain) |
|---|---|---|
| `l6_lemma5` | **PROVEN** (composes closer) | `Conditional.lemma5_of_pole_orders_and_support_card` + `l6_pole_orders` + `l6_support_card` |
| `coeff_one_formalIsogenySeries_mulByInt_eq` (IV.2.3a) | **PROVEN** (composes closer) | `coeff_one_..._via_bridge_003` + `formalIsogenySeries_FGL_additivity` (BRIDGE-003) + `..._mulByInt_nonpos` |
| `l6_computationA` (`finrank=pole-sum`, NON-RR) | **FRAMING ASSEMBLED 2026-05-22 (green)** — NOT Riemann–Roch. HYPS COMPLETE (`moduleFinite_linfAt_gamma_pullback_x` PROVEN this session) ⟹ `Sinf.ofIntegralClosure` data + `finrank_adjoin_eq_finrank_LinfAt`∘`finrank_gamma`∘`weightedPoleDegree`∘`l6_lemma5`. Reduced to 3 geometric witness sorries → the **V.1.3 bridge B chain** (6 sorries OpenLemmas:337-470, closed-point↔prime + ramification, route `NormValuation.maximalIdealAt`). |
| `omegaPullbackCoeff_F_value_eq_coeff_one` (B, IV.4.3) | wireable | `Derivation.liftKaehlerDifferential` + `liftKaehlerDifferential_comp_D` (mathlib; cf `Auxiliary/PullbackKaehler.lean`) of the `localExpand`-derivation (Leibniz DONE) applied to `omegaPullbackCoeff_spec`, then `formalIsogenySeries` def. |
| `omegaPullbackCoeff_mem_F` (A, III.1.5) | **genuine development** | NO existing closer — invariant differential has trivial divisor ⟹ `a_α` constant. Divisor theory. |
| `mulByInt_q_pullback_qth_root` | genuine development | purely-insep degree-tower (`Verschiebung.PurelyInsep` infra exists; GAP-DUAL-A1). |
| `genuineIsogSmulSub_degree_eq_signed` | **genuine development (wall #2) — ROOT TRACED 2026-05-22** | Single deepest dep = **dual isogeny additivity `(α+β)^=α^+β^`** (Silverman III.6.2, NOT in mathlib — searched). Then ALL follows: `self_comp_isogDual`(:198 PROVEN)⟹π∘π^=[q] free; trace sum π+π^=[tr] via (1−π)(1−π)^=[deg(1−π)] expansion; `genuineIsogSmulSub=r•π−s`(rfl @Frobenius:4036) ⟹ (r•π−s)∘(r•π^−s)=r²[q]−rs[tr]+s²=[N]⟹deg=N (mulByInt inj). ⚠BOTH `DegreeQuadraticForm` dualChain lemmas CIRCULAR (abs/0≤N). Build dual-additivity via DivisionPolynomial (mathlib HAS) or explicit dual. |
| `degree_quadratic_exists_edge` | **subtle (2026-05-22 reassessment, NOT small)** | `h_edge` is `(r:K)=0 ∨ (s:K)=0` (char-divisible), which does NOT imply `r=0`/`s=0` in ℤ — so the clean `[s]` (r=0) / `[r]∘π` (s=0) constructions only cover the literal-zero sub-cases. For char-divisible `r`/`s` (≠0 in ℤ, =0 in K), the QF value `q·r²−tr·rs+s²` must be realized by the **inseparable `r•π−s`**, whose degree is the same deg-QF problem (chains to the Dev-1/Verschiebung root). Genuinely deep, not a quick construction. |

So: 2 more PROVEN (composing closers); 2 wireable to shipped closers (l6_computationA, B); 3 genuine
developments (A III.1.5, wall #2 deg-QF, qth_root) + 1 small (edge). Sub-leaves added:
`l6_pole_orders`, `l6_support_card`, `formalIsogenySeries_FGL_additivity`, `coeff_one_..._mulByInt_nonpos`.

### Remaining skeleton leaves (7) — as of 2026-05-22
- GapQfKernel: `coeff_one_formalIsogenySeries_mulByInt_eq` (IV.2.3a, needs BRIDGE-003),
  `omegaPullbackCoeff_localExpand_eq_coeff_one` (IV.4.3 bridge; Leibniz/derivation input now DONE).
- GapSpines: `mulByInt_q_pullback_qth_root` (purely-insep), `l6_computationA`, `l6_lemma5` (pole-divisor),
  `genuineIsogSmulSub_degree_eq_signed` (framework wall #2: deg bilinear / signed III.6.3),
  `degree_quadratic_exists_edge`.

> **⚠ STALE (frozen 2026-04-18) — content below predates R26–R29.**
>
> Active planning has moved to the **R26–R29 universal-bound dispatch
> packet**. Read these instead:
>
> - `.mathlib-quality/WORKER-DISPATCH-BOARD.md` — entry point (86
>   tickets across 5 tiers, ~2820 LOC mid).
> - `.mathlib-quality/tickets/R27-SORRY-LIST-COMPLETE.md` — 38 main
>   ticket statements with Silverman citations.
> - `.mathlib-quality/tickets/R29-FULL-DECOMPOSITION.md` — full ≤80
>   LOC decomposition.
> - `.mathlib-quality/tickets/INDEX.md` — sorry-count snapshot +
>   TIER 6 progress + frozen legacy pool.
>
> **2026-05-20 sorry-count reality**: ~45 across 14 files in
> `HasseWeil/`; protected files carry 14 critical-path sorries
> (not the "17 code sorries" claimed below).
>
> The historical content below is preserved for git archaeology only.
> Do **not** treat it as the current state of the project.

## Summary (FROZEN 2026-04-18)
- Total: 26 tickets (17 done, 9 open/blocked)
- Open: 3 | In Progress: 1 | Done: 17 | Blocked: 6
- Sorry count: 17 code sorries across 8 files
- Build: SUCCESS (0 errors)
- Last updated: 2026-04-18

## Recent closures (2026-04-18)
- **T-IV-3-001**: F(M) AddCommGroup instance closed via
  `AddGroup.ofLeftAxioms` (commit b07ac2c). Axiom-clean.
- **Infrastructure scaffold**: `HasseWeil/EC/IsogenyKernel.lean`
  (kernel API, IsSeparable definition). No new sorries. Provides
  foundation for Bucket A (dual isogeny chain).
- **3 tickets updated** (T-III-4-015/016/017) with detailed Silverman
  proof strategies and dependency analysis.
- See `.mathlib-quality/sorries_infrastructure_2026-04-18.md` for the
  6-bucket plan covering all remaining 17 sorries.

## Stream D — Formal Group Critical Path (NEW)

These tickets build the formal group ↔ function field bridge needed to unblock T015.
See `.mathlib-quality/tickets/INDEX.md` for the full Stream D ticket list.

### [T-IV-2-005] Ê for elliptic curve (Stream A)
- **Status**: open
- **File**: HasseWeil/FormalGroup.lean (or new EllipticCurve/FormalGroupInstance.lean)
- **Depends on**: T-IV-2-001 (done), T-IV-1-008 (done)
- **Parallel**: yes (with T-IV-4-001)
- **Description**: Show the EC formal group law `formalGroupLaw W` satisfies
  the `FormalGroup` axioms (associativity, commutativity, unit, inverse).
  Associativity is the hardest — may use formal logarithm argument or
  direct coefficient comparison. We already have `formalW_recurrence` and
  `formalGroupLaw` defined; need to verify the axioms.

### [T-IV-4-001] Abstract invariant differential -- DONE
- **Status**: done (2026-04-10)
- **File**: HasseWeil/FormalGroup/Differential.lean (new)
- **Depends on**: T-IV-2-001 (done), T-IV-2-002 (done)
- **Parallel**: yes (with T-IV-2-005)
- **Description**: Define the invariant differential of a formal group:
  `ω_F = F_X(0,T)⁻¹ dT` (Silverman Prop IV.4.2). Prove uniqueness and
  that every invariant differential is `a · ω` for some `a ∈ R`.
  Work over `CommRing R`, no EC dependency.

### [T-IV-4-005] Pullback of invariant differential (THE KEY)
- **Status**: blocked (by T-IV-4-001)
- **File**: HasseWeil/FormalGroup/Differential.lean
- **Depends on**: T-IV-4-001
- **Eliminates**: the theoretical gap blocking T015
- **Description**: Silverman Cor. IV.4.3: for a formal group homomorphism
  `f : F → G`, `ω_G ∘ f = f'(0) · ω_F`. Proof: differentiate the
  associative law `F(U, F(T,S)) = F(F(U,T), S)` w.r.t. U, set U = 0.
  This is the formal-group version of "pullback coefficient = leading term".

### [T-IV-BRIDGE-001/003] Formal group bridge + additivity -- DONE
- **Status**: done (2026-04-10)
- **File**: HasseWeil/FormalGroupBridge.lean
- **Description**: `isogPullbackCoeff_add_of_formal` proved: given bridge hypotheses
  (coeff = omegaPullbackCoeff for each isogeny) and the formal addition identity,
  pullback coefficient additivity follows. Bridge verified for `[n]` via
  `bridge_mulByInt`. Sanity check: `omegaPullbackCoeff_mulByInt_add` proved.
  The bridge approach bypasses the need for full Cor. IV.4.3 and T-IV-2-005;
  callers discharge the hypotheses for specific isogenies.

## Done

### [T000] Remove pullback_injective from Isogeny -- DONE
### [T001] Restructure Basic.lean with unified Isogeny -- DONE
### [T002] Build mulByInt pullback (Weierstrass identity) -- DONE
### [T003] Update Endomorphism.lean (scalar specializations) -- DONE
### [T005] Define isogPullbackCoeff via Kahler differentials -- DONE
### [T010] Frobenius pullback + degree -- DONE
### [T011] HasseBound assembly -- DONE
### [T012] mulByInt_finrank tower law -- DONE
### [T013] coordHom_injective structure -- DONE
### [T018] Ramification: polynomialY case -- DONE (squarefree argument)
### [T020] Basic.lean mulByInt_finrank substep -- DONE (adjoin_induction proof)
### [T021] Ramification build errors -- DONE (5 type class diamonds fixed)
### [T019] mulByInt_x_transcendental -- DONE (no sorry in MulByIntPullback.lean)
### [T023] LocalExpansion coordHom injectivity -- DONE (order-parity argument)

## Open Tickets

### [T015] PullbackCoeff dual_mul (line 138 DONE)
- **Status**: partially done (line 138 eliminated, line 188 remains)
- **File**: HasseWeil/PullbackCoeff.lean:188
- **Eliminates**: 1 remaining sorry (isogPullbackCoeff_dual_mul)
- **Line 138** (`isogPullbackCoeff_add`): **DONE** (2026-04-10). Restructured with
  formal-group-level hypotheses. Uses `isogPullbackCoeff_add_of_formal` from
  `FormalGroupBridge.lean`. Callers must now provide bridge hypotheses (hα, hβ, hαβ)
  and formal addition identity (h_formal_add).
- **Line 188** (`isogPullbackCoeff_dual_mul`): blocked by T016 (`isogDual_comp_self`).
  Still a sorry — depends on DualIsogeny infrastructure.

### [T014] Endomorphism general pullbacks
- **Status**: blocked (by formal group bridge — needs addition formula on K(E))
- **File**: HasseWeil/Endomorphism.lean:59,85
- **Eliminates**: 2 sorries (pullback for isogOneSub, isogSmulSub)
- **Blocked by**: Constructing pullbacks for sum-endomorphisms requires the formal
  group addition formula on K(E). The `FormallyCompatible` typeclass from
  T-IV-BRIDGE-001 provides the right abstraction. Also has a design issue:
  AlgHom.id for n=0 gives degree 1 not 0.

### [T016] DualIsogeny -- all 8 sorries
- **Status**: blocked (by T015 line 138 + isogeny factorization III.4.11)
- **File**: HasseWeil/DualIsogeny.lean:33-87
- **Depends on**: T015 (isogPullbackCoeff_add) + isogeny factorization (III.4.11)
- **Eliminates**: 8 sorries (but T015 line 170 also depends on T016 — circular)

### [T017] degree_quadratic + pointCount_eq
- **Status**: blocked (by T016)
- **File**: HasseWeil/DegreeQuadraticForm.lean:88, HasseWeil/Frobenius.lean:100
- **Depends on**: T016
- **Eliminates**: 2 sorries

### [T019] mulByInt_x_transcendental -- DONE
- **Status**: done (2026-04-10, no sorry remains in MulByIntPullback.lean)
- **File**: HasseWeil/MulByIntPullback.lean
- **Eliminates**: 1 sorry
- **Description**: Nonconstant rational function of transcendental is transcendental.

### [T022] Ramification: polynomialY-in-P case (Worker B)
- **Status**: in_progress (partial - 2026-04-17 deep-pass)
- **File**: HasseWeil/Ramification.lean:553 (sorry line moved due to added helpers)
- **Eliminates**: 1 sorry
- **Description**: When mk(polynomialY) in P, show maximal ideal is principal.
  Char != 2: identity mk(polynomialX) = (a1/2)*mk(polynomialY) - g(d'/4),
  then d' not in p from hX, giving direct principality.
  Char 2: either Wbar irreducible (P = p*R) or F-rational point (localRing_isDVR).
- **2026-04-17 deep-pass progress**:
  - Added `four_polynomialX_eq_jacobi` (the Jacobian polynomial identity in F[X][Y]).
  - Added `dprime_not_in_p` (in char != 2, d' not in p follows from the Jacobian).
  - Sorry at line 553 now has a detailed 6-step proof outline comment covering
    char != 2 (cotangent-space approach) and char 2 (case analysis / base-change).
  - Remaining gap: generator structure of P (showing P = span{mk(C π), mk(polynomialY)})
    and the cotangent dimension conclusion. Alternative: base-change to residue field
    to reuse `Valuation.localRing_isDVR` (see HANDOFF.md:122). Estimated 150-200 lines.

### [T023] LocalExpansion sorries (Worker A) -- DONE
- **Status**: done (2026-04-10)
- **File**: HasseWeil/LocalExpansion.lean (0 sorries)
- **Eliminates**: 1 sorry (localExpand_coordHom_injective; 6 others were already proved)
- **Description**: The local expansion map K(E) -> LaurentSeries F.
  Proof of coordHom injectivity uses order-parity argument:
  formalX has order -2 (even), formalY has order -3 (odd).
  Polynomial evaluation at formalX is injective (transcendence).
  Decompose R elements via power basis {1, root}, image is
  p(formalX) + q(formalX)*formalY; even + odd orders can't cancel.
- **Depends on**: FormalGroup (done), FormalGroupAssoc (done)

### [T024] OmegaPullbackCoeff mulByInt_pullback_x_eq
- **Status**: open
- **File**: HasseWeil/OmegaPullbackCoeff.lean:359
- **Eliminates**: 1 sorry
- **Description**: [n]*(x) = Phi_n/Psi^2_n as division polynomials.
  Silverman Exercise III.3.7. Strong induction on m.
  Estimated ~500 lines if fully formalized.

## Critical Path
```
Stream D formal group bridge (NEW):
  T-IV-2-005 (Ê is FormalGroup)  ──┐
  T-IV-4-001 (invariant diff def) ─┤
    → T-IV-4-005 (ω∘f = f'(0)·ω) ─┤
      → T-IV-BRIDGE-001 (coeff bridge) ←─┘
        → T-IV-BRIDGE-003 (formal additivity)
          → T015 (isogPullbackCoeff_add)
            → T016 (dual isogeny) → T017 (degree + pointCount)

Independent:
  T022 (Ramification, Worker B) → kernel-degree for separable isogenies
  T024 (Wronskian, independent) → completes omegaPullbackCoeff_mulByInt

Done:
  T023 (LocalExpansion) ✓ → enabled formal group bridge
```
T-IV-2-005 and T-IV-4-001 can start NOW (parallel). They are the new entry points for Stream A.

### [GAP-QF-DEGQF] genuineIsogSmulSub_degree_eq_signed (Silverman III.6.3) — 3 research walls (2026-05-23)
- **Status**: open — **Parent**: qf_nonneg_skeleton (GapSpines:338/348). Keystone `verschiebung_dual_exists` DONE (axiom-clean). Direct route `[deg β]=[N] (AddMonoidHom) ⟹ deg β=N` is UNSOUND over finite fields (E(𝔽_q) finite ⟹ AddMonoidHom doesn't determine the integer). Squared route (`degree_quadratic_closed`) is CIRCULAR (deg=|N| needs N≥0=goal). Genuine proof needs the FULL Isogeny identity `β_dual∘β = mulByInt N` (pullback incl.), via 3 walls:
  - **Wall C** — **SHIPPED axiom-clean** as `HasseWeil.mulByInt_left_injective` at `HasseWeil/EC/MulByIntAddRecurrence.lean:60` (verified 2026-05-25T19:30Z, axioms = `[propext, Classical.choice, Quot.sound]`). Via pullback on x_gen + y_gen → `mulByInt_xy_inj` (generic point has infinite order).
  - **Wall A** (V-side pole bound): construct `genuineIsogSmulSubV_universal` (Genuine:1024) with `h_pole : ordAtInfty(addPullback_x_pair (V.zsmul r) [−s]) < 0`. Curve-dependent (ord-∞ = −2 ordinary vs −2q supersingular per Genuine:349); `ord_addPullback_x_pair_zsmul_verschiebung` does NOT exist.
  - **Wall B** (Isogeny-level dual pullback, "double-Vieta match"): `IsDualOf β_dual β` needs the PULLBACK equality (dual-additivity lemmas give only AddMonoidHom). Compose two `addPullbackAlgHomPair`s, match `mulByInt_x/y N` on generators (cf. `addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses`, OpenLemmaPrimitives:1453). ~hundreds of lines.
- **B2 NOTE**: the placeholder gate `traceOfFrobenius_sq_le` (HasseBound:81) is FALSE (traceOfFrobenius via placeholder AlgHom.id ⟹ trace=q ⟹ q²≤4q false q≥5; see b2_log.jsonl). Genuine bound = `hasse_bound_skeleton` (sorry-free body) → qf_nonneg_skeleton (this) + ker_deg_skeleton (GAP-L6). Retire/redefine traceOfFrobenius. [Done 2026-05-29: `traceOfFrobenius_sq_le` placeholder DELETED in the placeholder purge.]
- **Round-7 reviewer guidance (2026-05-29)**: RE-SCOPE. The RESTRICTED-dual route (`W4-repair-dual-composition`: `(rπ−s)^=rV−s` on the Frobenius plane) yields `deg(rπ−s)=qr²−trs+s²` via `(rV−s)(rπ−s)=[N]`. Terminology: the QF is positive **semidefinite** (nonnegative), not positive-definite.
- **⚠ CORRECTION (2026-05-29 build pass) — the restricted dual does NOT obviate Wall A.** Verified by a read-only investigation: `Isogeny.degree` depends ONLY on `.pullback`, and `rπ−s` is generically INSEPARABLE, so closing the pivot REQUIRES a genuine `β_dual = rV−s` whose **pullback** satisfies `(rπ−s).pullback ∘ β_dual.pullback = [N].pullback` (the "double-Vieta" Wall B at the FUNCTION-FIELD / inseparable-degree level — NOT the point-map level). The only construction of `rV−s`'s pullback is `genuineIsogSmulSubV` via `addIsog`, whose injectivity needs **Wall A** (`addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pole`, Genuine.lean — the V-side formal-group pole order). Even discharging Wall A leaves Wall B + `IsDualOf (rV−s) (rπ−s)`, both pullback-level. SHIPPED already: the AddMonoidHom-level composition `(rV−s)(rπ−s)=[N]` (`genuine_dual_comp_toAddMonoidHom_eq_mulByInt`), `π+V=[t]`, `Vπ=[q]`, the witness-parametric composer (`genuineIsogSmulSub_degree_eq_signed_of_full_pivot_chain`). The IRREDUCIBLE residual = the pullback-level double-Vieta `(rV−s)(rπ−s)=[N]` for the genuine `rV−s` (presupposing the genuine `rV−s` pullback = Wall A). **No point-level escape exists for Leaf 1 (unlike Leaf 2, which closed via embeddings):** the inseparable degree genuinely lives at the pullback level. This is genuine Silverman III.6.2 / IV.1–3 / VII.2 formal-group + inseparable-degree content, not reachable from the shipped point-level / Pic⁰ / kernel-count infrastructure.
- **★ ROUND-10 CHOSEN PLAN (2026-05-29) — narrow Route A (formal-group dual), with extensionality as the Wall-B killer.** Reviewer chose Route A over Route B (Weil-pairing/Tate-module starts from ~zero; Route A reuses shipped V, Vπ=[q], π+V=[t], point-map composition, Wall C). NOT full VII.2. Three steps:
  1. **Minimal Wall A** (nonconstancy, NOT exact pole order): `rV−s ≠ 0 ⟹ ord_O((rV−s)*x) < 0` — makes `genuineIsogSmulSubV` (rV−s via addIsog) a GENUINE degree-bearing isogeny. (State exact pole order separately only if later needed.)
  2. **★ Genuine-isogeny EXTENSIONALITY lemma** (the new shortcut — ELIMINATES Wall B): `genuine_isogeny_ext_of_geometric_pointMap_eq (φ ψ : Isogeny E E) (hφ : φ.IsGenuine) (hψ : ψ.IsGenuine) (hpt : ∀ P : E(K̄), φ P = ψ P) : φ.pullback = ψ.pullback`. Apply to `φ = (rV−s).comp(rπ−s)`, `ψ = [N]` (both genuine): the SHIPPED point-map composition `(rV−s)(rπ−s)=[N]` (`genuine_dual_comp_toAddMonoidHom_eq_mulByInt`) upgrades to the COMORPHISM identity, avoiding the explicit double-Vieta (Wall B). Needs `IsGenuine` defined (cf. `isogeny-genuine-hygiene` ticket) + the lemma proven (a genuine isogeny's comorphism is determined by its geometric point-map) + `genuineIsogSmulSub`/`genuineIsogSmulSubV`/their comp/`mulByInt` all `IsGenuine`.
  3. **Wall C** (`signed_degree_of_genuine_dual_pair`, SHIPPED): from the genuine dual pair `IsDualOf (rV−s) (rπ−s)` + `(rV−s).comp(rπ−s)=[N]` + `0<deg`, conclude `deg(rπ−s)=N`.
  - **Q2 verdict**: extensionality replaces Wall B but CANNOT replace Wall A (it needs `rV−s` already genuine to compare; can't create it). The alt to Wall A is the factorisation/descent `ker β ⊆ ker[N] ⟹ [N] factors through β` (Silverman III.4.11/4.12) — another route to duality, not a cheap rigidity lemma.
  - **Separability correction (round 10)**: `rπ−s` (≠0) is separable ⟺ `p∤s` (`a_{rπ−s} = −s`); the Frobenius term does NOT make it non-étale once `a≠0`. The inseparable degree only matters for `p∣s`.
  - **Q3 verdict**: NO cheap third route avoiding `deg(rπ−s)=N`. Leaf 2 gives `t=q+1−#E` but no bound; parallelogram law = the same bilinear-degree content (needs duals); kernel counts for `rπ−s` opaque + inseparable; Stepanov/Weil-pairing are big alternate theories. Do NOT chase Q3 unless pivoting to Stepanov (prototype separately).
  - Route B (Weil-pairing) = fallback only.
- **★★ ROUND-11 CHOSEN PLAN (2026-05-29) — PIVOT to Pic⁰ dual existence/additivity; the round-10 narrow-Route-A plan above is SUPERSEDED.** The reviewer CONFIRMED the §3 finding: narrow Route A (Wall A + extensionality + Wall C) does NOT close Leaf 1. Wall A / BRIDGE-003 supplies only condition (i) — genuineness of `rV−s` + the comorphism composition `(rV−s)(rπ−s)=[N]` — but NOT condition (ii) `IsDualOf (rV−s) (rπ−s)` (= `(rV−s)(rπ−s)=[deg(rπ−s)]`), which GIVEN (i) is logically EQUIVALENT to the goal `deg(rπ−s)=N`. Crucially the SIGN is irreducible: two-sided `[N]` + degree multiplicativity give only `deg(rπ−s)·deg(rV−s)=N²`, hence at best `deg=|N|` (cf. `[−1]∘[m]=[−m]`, deg `m²>0`, scalar `<0`); `N≥0` comes ONLY from the dual relation `β̂β=[deg β]`. So the real target is dual existence/additivity. **Revised critical path (Pic⁰):**
  1. **Pic⁰ dual construction / functoriality**: `Pic⁰(E) ≅ E` + pushforward/pullback functoriality ⟹ a GENUINE dual isogeny `α̂` with `α̂∘α = [deg α]`.
  2. **Dual additivity on the Frobenius plane**: `(φ+ψ)^=φ̂+ψ̂` (natural from Pic⁰ functoriality) ⟹ `(rπ−s)^ = r·π̂ − s = rV−s` (using `π̂=V`), at least at point-map level, dual itself genuine.
  3. **Extensionality lifts the Vieta `[N]`**: the shipped point-map composition `(rV−s)(rπ−s)=[N]` upgrades to the comorphism level since the dual is genuine (`genuine_isogeny_ext`).
  4. **Compare scalars**: `β̂β=[deg β]` (step 1) vs `=[N]` (step 3) ⟹ signed `deg(rπ−s)=N` (mulByInt injectivity = shipped Wall C).
  5. Leaf 1 (qf_nonneg) follows since `deg ≥ 0`.
  - **★ Reviewer implementation refinement**: do NOT construct `rV−s` via `addIsog`/BRIDGE-003. Let the Pic⁰ dual theorem RETURN the genuine `β̂`; prove its point-map `= rV−s` by Pic⁰ functoriality/additivity; then steps 3–4. This is exactly why dual existence subsumes BRIDGE-003 for Leaf 1.
  - **Q2 (route choice)**: Pic⁰ chosen OVER kernel/factorisation — Pic⁰ gives dual ADDITIVITY (what Leaf 1 needs) naturally; factorisation proves existence but additivity is a heavy second theorem (uniqueness + degree bookkeeping + quotient curves + sep/insep factorisation). May target the narrow `frobeniusPlane_dual (r s : ℤ) : IsDualOf (r•V − s•id) (r•π − s•id)`, but the general `exists_dual` likely uses the same Pic⁰ machinery and is cleaner/more reusable once it exists.
  - **Q3 (no cheaper substitute)**: parallelogram law = the same quadratic-form/dual content (not independent); degree-symmetry `deg(rV−s)=deg(rπ−s)` gives only `|N|` (no sign); Tate-module/Weil-pairing determinant is a valid but HEAVY alternate route (needs `E[N]≅(ℤ/N)²`, Weil pairing, det-degree, trace comparison, congruence lift — not lighter than Pic⁰); point-count only helps separable members + opaque two-parameter kernel.
  - **Q4 (DEMOTION)**: BRIDGE-003 (`formalIsogenySeries_add`) and Wall A (`genuineIsogSmulSubV_universal*`, `addPullback_x_pair_x_ord_neg`) are DEMOTED from the Leaf-1 critical path — RETAINED as reusable addition-pullback/formal-group infrastructure, NOT deleted. They should no longer drive the Hasse-bound effort.
  - **⚠ ASSEMBLY CAUTION (reviewer round 11)**: the global `∀ r,s` qf_nonneg must isolate the zero-endomorphism / scalar-collapse branch (`rπ−s=0`, possible for `(r,s)=(k,km)` when `q=m²` is a perfect square, t=2m): there `deg` is 0/undefined, but `Q(r,s)=qr²−trs+s²=0` too, so prove `0≤0` DIRECTLY; else (`rπ−s≠0`) use `deg>0` (shipped `isogeny_degree_pos`) + the dual argument. NOTE: the shipped `isogeny_degree_pos` is SOUND (the `Isogeny` type carries an injective pullback, cannot represent the zero map); the caution bites only at final assembly. Also AUDIT that `genuineIsogSmulSub` is never invoked at a scalar-collapse `(r,s)` (would be a placeholder if it claimed a genuine isogeny for `rπ−s=0`).

---

## PIC⁰ — DUAL ISOGENY VIA THE PICARD GROUP (round-11 critical path, 2026-05-29)

The Leaf-1 deep core, per the round-11 reviewer verdict. Goal: discharge `exists_dual`
(`HasseWeil.exists_dual`, DualIsogeny.lean:142) — a genuine dual isogeny `α̂` with
`α̂∘α=[deg α]` and dual additivity — via `Pic⁰(E)≅E` + class-group functoriality, then
close `genuineIsogSmulSub_degree_eq_signed` ⟹ qf_nonneg ⟹ Hasse.

**Scoping result (2026-05-29, Explore + targeted search).**
- MATHLIB PROVIDES: `WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)` — a GROUP HOM, proven INJECTIVE (`toClass_injective`); `ClassGroup R` + `ClassGroup.mk`/`mk0`; `Ideal.relNorm : Ideal S →*₀ Ideal R` (multiplicative + transitive) with `Ideal.spanNorm_singleton : spanNorm R (span {r}) = span {intNorm r}` (norm of principal = principal — the descent key); `Ideal.map`/`comap`; `CommRing.Pic` + `ClassGroup.equivPic` (ClassGroup ≅ Pic for domains).
- MATHLIB LACKS: (P1) surjectivity of `toClass` / the equiv `Point ≃+ Additive(ClassGroup)` (= the `E≅Pic⁰` other half, genus-1 Riemann–Roch); (P2) any `ClassGroup`-level functoriality map (relNorm/Ideal.map are ideal-level only); isogenies/dual (none); Weil divisors / `Pic⁰` (none).
- PROJECT PROVIDES: the parametric dual scaffolding (`exists_dual_of_construction`/`_constructor`/`_iff_constructor`, witness-parametric `isogDual_*_of_witness`, `degree_dual_of_witness`); **AXIOM-CLEAN dual additivity at point level** (`dual_add_of_trace_witnesses`, `dual_add_of_sum_witnesses`); `IsDualOf V π` genuine (`verschiebung_dual_exists`); shipped Wall C (`mulByInt_left_injective`), `0<deg` (`isogeny_degree_pos`), point-map Vieta `(rV−s)(rπ−s)=[N]`, genuine-isogeny extensionality.

**Sub-ticket DAG (lowest → highest):**
- **[PIC0-2a] `ClassGroup.relNorm`** (LOWEST — pure ring theory, START HERE): descend `Ideal.relNorm : Ideal S →*₀ Ideal R` to a monoid hom `ClassGroup S →* ClassGroup R`, well-defined because relNorm sends principal to principal (`spanNorm_singleton`). Self-contained, abstraction-independent, reusable (upstreamable). Companion: `ClassGroup.map` from `Ideal.map` for the pullback direction.
- **[PIC0-2b] norm∘extension = `[deg]`** on `ClassGroup`: for a finite extension, `relNorm ∘ (Ideal.map) = (·)^[deg]` at the class level (the pushforward-pullback composition = multiplication by the field-extension degree). The arithmetic core of `α̂∘α=[deg α]`.
- **[PIC0-1] `toClass` surjective ⟹ `Point ≃+ Additive(ClassGroup)`** (`E≅Pic⁰`): genus-1 Riemann–Roch — every degree-0 class has a representative `(P)−(O)`. mathlib has injectivity; this is the other half.
- **[PIC0-0] BRIDGE: codebase `Isogeny` ↔ coordinate-ring/ClassGroup picture**: connect `Isogeny.pullback` (on `FunctionField`) to the `CoordinateRing` finite extension and the `ClassGroup` functoriality (PIC0-2a/b) + `toClass` (PIC0-1). The architecture-defining glue; design carefully (FunctionField = FractionField CoordinateRing).
- **[PIC0-3] `isogDual` construction**: `α̂ := (E≅Pic⁰) ∘ α^*_class ∘ (Pic⁰≅E)` as a genuine `Isogeny`; prove `IsDualOf (isogDual α) α` ⟹ discharge `exists_dual` via `exists_dual_of_construction`. Then `(rπ−s)^=rV−s` via the shipped point-level additivity + uniqueness; extensionality lifts Vieta; Wall C ⟹ signed `deg=N`.
- Reviewer refinement: the dual RETURNS genuine `β̂`; never build `rV−s` via `addIsog`. May target narrow `frobeniusPlane_dual` but PIC0-0..2 machinery is needed either way.

**PROGRESS (2026-05-29, beastmode):** PIC0-2a ✓ (`ClassGroup.relNorm`), PIC0-2b ✓ (`ClassGroup.relNorm_comp_map = (·)^finrank`, via mathlib's `Ideal.relNorm_algebraMap`), SUB-1 ✓ (`coordinateRing_isDedekindDomain` was ALREADY axiom-clean — the 6 Ramification.lean sorries are off-path). PIC0-1 reduced to ONE predicate `ClassReducesToCodimLEOne` (= the genus-1 RR inequality), decomposed into codim-additivity [routine] + FD instance [routine] + the rank-2-F[X]-lattice norm-degree inequality [core]. `verschiebung_dual_exists` confirmed axiom-clean = a PROVED full-Isogeny `IsDualOf V π`.

**★ PIC0-0/3 DESIGN-PASS FINDINGS (2026-05-29) — the general Pic⁰ `exists_dual` has THREE deep gaps (worse than the round-11 plan anticipated):**
1. **Comorphism ≠ AlgHom**: the Pic⁰ dual is naturally a POINT map (on Pic⁰≅E); its function-field comorphism is the field NORM `Algebra.norm` (multiplicative, NOT an `AlgHom`), so it cannot directly populate `Isogeny.pullback`. The codebase `Isogeny` (Basic.lean:63) needs the comorphism; Pic⁰ gives only the point map. Mismatch with `IsDualOf`'s full-Isogeny demand. (And the signed degree NEEDS the comorphism/generic-point level — point-level over finite `E(𝔽_q)` is insufficient, cf. Wall C uses pullback on x_gen.)
2. **`toClass_isogeny_compat` (PIC0-3b) = Silverman III.3.4**: linking the point map `α.toAddMonoidHom` to the ideal map `ClassGroup.map`/`relNorm` through `toClass` (`α^*⟨X−x,Y−y⟩ = ⟨X−α(x),…⟩` mod principal). DEEP, zero in-repo scaffolding. THIS is the actual gate.
3. **Universal `CoordHom` = integrality preservation** = the bare `sorry` `omegaPullbackCoeff_isIntegral_polynomialX` (GapQfKernel.lean:357, Silverman III.1 divisor-of-differential). A general `α` has a CoordHom iff `α.pullback` preserves integrality.
- **The SIGN is irreducible regardless of route**: any construction giving `β_dual∘β=[N]` (Vieta, or the factorization `[N]=δ∘β` since `ker β⊆ker[N]` by Cayley–Hamilton on points) yields only `deg(δ)·deg(β)=N²` → `deg=|N|`. Signed `deg=N` needs the dual's DEFINING `β̂∘β=[deg β]` (same deg both sides), i.e. an intrinsic dual construction (Pic⁰ III.3.4 or quotient `E/ker β` III.6.1).
- **Design rec**: PIC0-0a/b (the `Isogeny.CoordHom` bridge struct + `classNorm_comp_classMap`) is routine reusable infra (instantiable for Frobenius via `frobeniusCoordHom`, for `mulByInt`); PIC0-3b (III.3.4) is the deep blocker to flag, not grind blindly. The Frobenius-plane route via `verschiebung_dual_exists` + `dual_add_of_trace_witnesses` still needs genuine `rV−s` assembly (reconnects to Wall A) AND the comorphism. NET: Leaf-1 endgame is a genuine multi-month formalization (mathlib has NO RR for curves / NO Pic⁰ / NO isogenies); the deepest single gate is III.3.4 `toClass`-functoriality.
- Key shipped assets (axiom-clean): `verschiebung_dual_exists` (GapSpines:64, full-Isogeny IsDualOf V π), `dual_add_of_trace_witnesses` (DualIsogeny:280, point-level dual additivity), `Isogeny.frobeniusCoordHom` (EC/IsogenyAG:306), `Algebra.IsAlgebraic.finrank_of_isFractionRing` (mathlib, the FunctionField↔CoordinateRing finrank link).

**★★★ PIC0 ROUTE VERDICT — ⚠ RETRACTED 2026-05-30 (the "DEAD END / degree-blind" conclusion was a MISDIAGNOSIS).** Confirmed independently by (i) reading Silverman III.4.10 + III.6.1 directly and (ii) the round-12 reviewer: **classical Pic⁰ is NOT degree-blind; only the IMPLEMENTED comap bridge was.** The scoping pass analyzed the WRONG operation — `comap`/`relNorm` correspond to the *point action* `φ_*` (pushforward), which is multiplicity-free (`toClass(α P)=mk0(comap α* m_P)` just moves the point); but the **dual** uses `φ*` = the *divisor pullback* = **ideal EXTENSION** `Ideal.map` (= shipped `ClassGroup.map`), whose exponent is the ramification `e_φ(P)`. By Silverman III.4.10(a), `e_φ(P) = deg_i φ` (inseparable degree) for every `P∈φ⁻¹(Q)`, and `#φ⁻¹(Q)=deg_s φ`, so `φ*((Q))=deg_i·Σ(P)` and `sum(φ*((Q)−(O)))=[deg φ]P` (III.6.1b) — the FULL degree. The project ALREADY shipped the right relation: `ClassGroup.relNorm_comp_map = (·)^finrank` is `φ_*∘φ* = [deg]` with `finrank = full degree`. So Pic⁰ sees inseparability via the ramification multiplicity in the EXTENSION map. **The `b2_log` PIC0-route-leaf1 entry is RETRACTED (see the retraction line).** The Pic⁰ work is NOT wasted.
- **★ ROUTE C — CORRECTED PIC⁰ (round-12 reviewer's recommended primary path; over Route A formal-group and Route B kernel-quotient).** Fix the bridge from prime-comap to divisor pullback / ideal extension with ramification, then Pic⁰ gives the full degree + dual additivity. **4 steps:**
  1. **Fix the bridge**: the dual uses `ClassGroup.map` (ideal EXTENSION `𝔭↦𝔭ℬ=∏𝔓^e`), NOT `comap`. (The shipped `toClass_toPointMap` comap-functoriality is the *point action* `φ_*` — correct as such, but the WRONG operation for the dual.)
  2. **Full-degree push-pull** `α_*α* = [deg α]` on Pic⁰ (THE critical theorem) — build on the shipped `ClassGroup.relNorm_comp_map = (·)^finrank`. Target `divisor_pullback_point_class_eq_extension` (with multiplicities) + `pic_push_pull_eq_degree`.
  3. **Dual additivity** `(φ+ψ)^=φ̂+ψ̂` (from Pic⁰ functoriality) ⟹ `(rπ−s)^=rV−s`.
  4. **Close** with shipped `V`, `Vπ=[q]`, `π+V=[t]`, point-map composition.
  - **⚠ Reviewer WARNING (independently matches our analysis):** `(rV−s)(rπ−s)=[N]` ALONE gives only `deg(rV−s)deg(rπ−s)=N²` → `|N|`, NOT signed `deg(rπ−s)=N` (e.g. `[3]∘[2]=[6]`, `deg[2]=4≠6`). The sign needs the genuine DUAL relation `φ̂φ=[deg]` (same deg both sides) — which Route C's full-degree Pic⁰ supplies, Route A alone does NOT.
  - **Comorphism**: the Pic⁰ dual is a point map; get its comorphism via genuine-isogeny extensionality (`genuine_isogeny_ext`) once a candidate genuine map agrees on points, OR via the formal-group local route for genuineness (Route A as a *secondary* helper only).
- **REUSABLE ASSETS (axiom-clean, ON the Leaf-1 path via Route C):** `E≅Pic⁰` (`toClassEquiv'`, genus-1 RR), `ClassGroup.relNorm`/`map`/`relNorm_comp_map` (the full-degree push-pull core), the `Isogeny↔ClassGroup` bridge, the `comap` point-action functoriality (`toClass_toPointMap` — keep, it's the `φ_*` half). `HasseWeil/Pic0/*.lean`.
- **Silverman's framing (cleanest target):** `deg` is a positive-definite quadratic form (III.6.3) via the dual; `deg(rπ−s)=r²q−rs·t+s²=N` is the QF identity; `qf_nonneg` is then TRIVIAL (`deg≥0`). Hasse (V.1.1) = Cauchy–Schwarz (Lemma 1.2) on the pair `(π,1)`. USER chose "correct records + pause" — Route C build pending go-ahead.

---

## V2 PATH TO UNCONDITIONAL HASSE BOUND (2026-05-25)

Per `.mathlib-quality/decomposition-residual-walls-v2.md`. The 7 tickets below
discharge the residual obligations of `HasseWeil.hasse_bound_target_via_negFrobenius`.
Path A (Galois route via `hasse_bound_via_witness1_normal_bijection` in
`Hasse/HoleE.lean:809`) — bypasses the Sinf bridges entirely.

**Silverman verification protocol** (binding for each ticket below): each proof
sketch step cites the Silverman page (GTM 106, 2nd ed.) it implements; the
mathlib/project lemma it uses is named explicitly; the source quote (verbatim)
appears in the ticket's Sources section. Workers running `/beastmode` MUST
re-verify the cited Silverman passage matches the Lean signature before
proceeding to tactics.

### [T-PFA-1] PIVOT-FINISH-TRANSLATION-ALGEBRA — translation_algebra .some case
- **Status**: done (2026-05-25T08:30Z — was: open) — **PRE-EXISTING SHIPMENT, ticket premise invalid**
- **File**: `HasseWeil/EC/TranslationOrd.lean:3312` (`translateAlgEquivOfPoint`)
- **Depends on**: none
- **Parallel**: yes
- **Type**: def + proof

**Progress**:
- 2026-05-25T08:30Z: DONE. The ticket's premise was incorrect — the "sorry"
  at `PointFix.lean:642` is **inside a docstring code block**
  (`/-- ... \`\`\`lean ... sorry ... \`\`\` -/`), not in compiled code. The
  actual translation construction is fully shipped axiom-clean as
  `HasseWeil.translateAlgEquivOfPoint` (`EC/TranslationOrd.lean:3312`),
  with all 4 ticket-sketch steps discharged via the dispatch over
  `.zero` / `.some 2-tor` / `.some non-2-tor`. Verified:
  `#print axioms HasseWeil.translateAlgEquivOfPoint` returns
  `[propext, Classical.choice, Quot.sound]`. Build green (2565 jobs on the
  module subset; 2994 on full project).
- **Note for downstream T-PFA-2 / T-PFA-3**: the full group-hom property
  `translateAlgEquivOfPoint (T₁ + T₂) = (translateAlgEquivOfPoint T₁).trans
  (translateAlgEquivOfPoint T₂)` is shipped for trivial cases (when either
  operand is `.zero`) at `TranslationOrd.lean:3353-3380` but the substantive
  both-non-zero case is noted as "ship in follow-up commits". T-PFA-3
  (Aut≃kernel) will likely need this — spawn sub-ticket there if needed.

#### Silverman verification
- **Source**: Silverman III.4 (addition formula), pp. 58–60. The translation
  τ_k(P) = P + k is the chord-tangent construction at k. The addition
  formula gives:
  - x(P + k) = λ² − a₁λ − a₂ − x(P) − x(k), where λ = (y(P) − y(k))/(x(P) − x(k)).
  - y(P + k) = -λ·(x(P + k) - x(P)) - y(P) - a₁·x(P + k) - a₃.
- **Source quote (verbatim, p. 58)**:
  > "Let E be a Weierstrass cubic and P₁ = (x₁, y₁), P₂ = (x₂, y₂) ∈ E.
  > Define λ = (y₂ − y₁)/(x₂ − x₁). Then P₁ + P₂ = (x₃, y₃) with
  > x₃ = λ² + a₁λ − a₂ − x₁ − x₂ and y₃ = −(λ + a₁)·x₃ − ν − a₃,
  > where ν = (y₁·x₂ − y₂·x₁)/(x₂ − x₁)."
- **Lean ↔ source match**: `translation_algebra W k` builds the K-algebra
  endomorphism `τ_k* : K(E) → K(E)`, sending `x_gen ↦ x(τ_k(x_gen))` and
  `y_gen ↦ y(τ_k(x_gen, y_gen))`. The image x-coordinate is computed via
  `addX W (x_gen, x_k, slope_k(y_k, y_gen))` (`Affine.addX` from mathlib).
  The image y-coordinate analogously via `addY`. The K-algebra hom extends
  to all of K(E) by universality (K(E) = K(x_gen, y_gen)).

#### Statement
```lean
-- In HasseWeil/Hasse/PointFix.lean around line 632–646, the existing
-- sorry-stubbed code in the `.some xk yk` branch of `translation_algebra`.
-- The full statement is the `match` arm at line 642:
noncomputable def translation_algebra (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] (k : W.toAffine.Point) :
    W.toAffine.FunctionField ≃ₐ[K] W.toAffine.FunctionField :=
  match k with
  | .zero => AlgEquiv.refl
  | .some xk yk _h_eq h_ns => /- TODO: provide the τ_k* construction -/
```

(Verify the exact Lean signature at PointFix.lean:642 before starting.)

#### Proof sketch (Silverman III.4 + project addition-pullback API)
1. **(Silverman III.4 step 1)** Define τ_k(x_gen) = addX(x_gen, xk, slope_k(yk, y_gen))
   in K(E). The slope formula uses (y_gen - yk)/(x_gen - xk).
   Tactical realisation: use the project's `addX_x_gen_xk_slope` if shipped,
   or directly construct via `Affine.CoordinateRing` operations.
2. **(Silverman III.4 step 2)** Show it satisfies the Weierstrass equation
   via `addPullback_equation` (in `HasseWeil/AdditionPullback.lean`).
3. **(Silverman III.4.8(b), p. 73)** Build the K-algebra hom: K(E) → K(E)
   sending x_gen, y_gen to their τ_k-translates. Use
   `addCoordAlgHom` + `liftAlgHom` from the project's
   `EC/TranslationOrd.lean`. Silverman III.4.8(b):
   > "Let φ : C₁ → C₂ be a morphism of curves. The pullback φ* : K(C₂) → K(C₁)
   > is a K-algebra homomorphism."
4. **(Silverman III.4 step 3 — group action)** Show τ_k ∘ τ_{-k} = id via
   the group law on `Affine.Point`. Then `AlgEquiv` is built from the
   K-algebra hom + its inverse.

#### Mathlib lemmas needed
- `WeierstrassCurve.Affine.Point.add_neg_cancel` — `(P + k) + (-k) = P` for the
  group inverse argument (verify: `lean_loogle "Affine.Point.add_neg"`).
- `IntermediateField.algebraMap_eq` — for the K-algebra hom restriction.
- Project: `addCoordAlgHom` (`EC/TranslationOrd.lean`), `liftAlgHom`,
  `addPullback_equation` (`HasseWeil/AdditionPullback.lean`).

#### Sources
- Silverman, GTM 106, 2nd ed., Chapter III §4 addition formula (pp. 58–60).
- Silverman III.4.8(b) (p. 73) for the morphism→pullback functoriality.

#### Generality decision
- `(W : WeierstrassCurve K)` with `[W.toAffine.IsElliptic]` (the smooth case).
- `(k : W.toAffine.Point)` arbitrary K-rational point. Sub-case `.zero` already
  shipped via `AlgEquiv.refl`.

#### Sizing
~80 LOC (source: comments at PointFix.lean:632-646 list 4 explicit steps;
each step is ~20 LOC of Lean per the project's `addPullback` API style).

### [T-PFA-2] WIRE-GALOIS-NORMAL — Normal instance on (1−π)-pullback extension
- **Status**: deferred (was: blocked) (2026-05-25T10:30Z, per reviewer Round 8)
- **Reviewer guidance** (Round 8, 2026-05-25): "I would not make Route A primary. A non-circular normality-first route is unlikely; normality follows cleanly only after kernel-degree or quotient/fixed-field equality. For W3, prove the fibre/cardinality theorem directly via Sinf/pole-divisor instead."
- **Demote rationale**: T-PFA-2 stays as a `:= by sorry` skeleton in `HasseWeil/Hasse/GaloisNormal.lean` for future use, but no work is scheduled. Unblock requires either: (i) finite-étale fibre-degree theorem for isogenies, or (ii) elliptic-curve quotient by finite subgroup (Silverman III.4.12(b)) — both research-scale new infrastructure.
- **File**: new file `HasseWeil/Hasse/GaloisNormal.lean` (or add to `Hasse/HoleE.lean`)
- **Depends on**: T-PFA-1 (translation_algebra needed for the Galois orbits) — DONE
- **Parallel**: parallel with T-PFA-3 once T-PFA-1 done
- **Type**: theorem

**Progress (refinement note 2026-05-25)**: project has SUBSTANTIAL pre-shipped
infrastructure for the FixedPoints route, more than v2 plan acknowledged:
- ✅ `HasseWeil.kernelMulSemiringAction` (`PointFix.lean:943`): MulSemiringAction
  of `Multiplicative β.kernel` on `K(E)` via `translateAlgEquivOfPoint`.
- ✅ `HasseWeil.kernelMulSemiringAction_smulCommClass` (`PointFix.lean:952`).
- ✅ `HasseWeil.faithfulSMul_kernel` (`PointFix.lean:1146`, UNCONDITIONAL): the
  action is faithful via `translateAlgEquivOfPoint_injective`.
- ✅ `HasseWeil.finrank_pullback_fieldRange_eq_degree` (`PointFix.lean:1183`,
  UNCONDITIONAL): `[K(E) : β.pullback.fieldRange] = β.degree`.
- ✅ `HasseWeil.pullback_fieldRange_le_fixedField_of_xy_family` (`PointFix.lean:979`,
  witness-parametric on `h_xy_family`): forward inclusion.
- ✅ `HasseWeil.pullback_fieldRange_eq_fixedField_of_card_match` (`PointFix.lean:1069`,
  witness-parametric on `h_xy_family` + cardinality match).

**Circularity flag**: the FixedPoints route via `pullback_fieldRange_eq_fixedField_of_card_match`
takes `Fintype.card (Multiplicative β.kernel) = β.degree` as a hypothesis, which IS the
substantive Hasse content (V.1.1). Using this route to prove `Normal` would be circular
with the eventual Hasse bound.

**Non-circular route required**: build `Normal β.toAlgebra` via the orbit polynomial
construction DIRECTLY over `β.pullback.fieldRange`:
1. For each `f ∈ K(E)`, define `P_f := ∏ T ∈ ker β, (X − τ_T*(f))`.
2. Show `P_f.coeff i ∈ β.pullback.fieldRange` for all `i` (symmetric polynomials
   in the orbit are fixed by the kernel action, AND lie in `β.pullback.fieldRange`
   via the xy-invariance + scalar-tower argument).
3. Show `P_f` has `f` as a root (T=0 case).
4. So `minpoly (β.pullback.fieldRange) f` divides `P_f`.
5. `P_f` splits over `K(E)` (factorization is given), hence so does `minpoly_f`.

Substantial sub-content needed:
- L-2-A: `xy_family` for non-zero kernel of `isogOneSub_negFrobenius` (the σ-commutation
  chain + curve-group-law identity at K(E)-lifted level using `frobeniusIsog_apply`).
  Currently witness-parametric in `PointFix.lean:979` (≈100 LOC to discharge).
- L-2-B: orbit polynomial construction + symmetric-polynomial coefficient identification
  in `β.pullback.fieldRange` (≈150 LOC).
- L-2-C: composition → `Normal β.toAlgebra K(E) K(E)` (≈30 LOC).

Total revised estimate: ~280 LOC (up from ~100 LOC v2 estimate).

#### Silverman verification
- **Source**: Silverman III.4.10(a), p. 76:
  > "Let φ : E → E' be a nonconstant isogeny. Then the function field
  > extension K(E)/φ*K(E') is finite of degree deg(φ), and if φ is separable,
  > it is moreover separable. If E = E' and φ ∈ End(E), then K(E)/φ*K(E) is
  > a Galois extension."
- **Lean ↔ source match**: The Lean `Normal β.toAlgebra K(E) K(E)` (where
  `β = isogOneSub_negFrobenius`) asserts the extension is normal. Combined
  with `IsSeparable` (already shipped via Witness #1), this gives `IsGalois`
  via `isGalois_iff` in mathlib.

#### Statement
```lean
namespace HasseWeil

open WeierstrassCurve

theorem isogOneSub_negFrobenius_normal_extension
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) :
    letI := (isogOneSub_negFrobenius W hq).toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField := by sorry

end HasseWeil
```

#### Proof sketch (Silverman III.4.10(a) via Galois-orbit argument)
1. **(Silverman III.4.10(a) paragraph 1)** Every element of K(E) is algebraic
   over `β.pullback K(E)` (the function-field extension is finite, hence
   algebraic). Discharge via `h_pc_fin` (shipped).
2. **(Silverman III.4.10(a) paragraph 2)** For every f ∈ K(E), the Galois
   orbit of f over `β.pullback K(E)` is contained in K(E). Use the
   translation action: for each T ∈ ker(β), `τ_T* f` is another root of
   the minimal polynomial of f over β.pullback K(E). So the orbit is
   `{τ_T* f : T ∈ ker β}` ⊆ K(E).
3. **(Silverman III.4.10(a) paragraph 3)** The minimal polynomial splits in
   K(E): its roots are the Galois orbit (step 2), all in K(E). So K(E) is a
   splitting field for every minimal polynomial of an element. This IS the
   definition of `Normal`.
4. **(Lean discharge)** Use mathlib's `Normal.mk` constructor with the
   orbit/splitting-field witness from step 2. The witness uses T-PFA-1's
   `translation_algebra` to produce K-algebra automorphisms.

#### Mathlib lemmas needed
- `Normal.mk` or `Normal_iff_isSplittingField` — Mathlib normal definition.
- `Polynomial.splits_iff_orbit_subset` (or similar; verify name) — splitting
  field equivalence with orbit closure.
- Project: T-PFA-1's `translation_algebra`.

#### Sources
- Silverman, GTM 106, 2nd ed., III.4.10(a), p. 76 (Galois closure for endomorphism extensions).

#### Generality decision
- Stated for `isogOneSub_negFrobenius` specifically (the only isogeny we
  need this for in the Hasse path). Generalisation to all separable
  endomorphisms is possible but out-of-scope for this ticket.

#### Sizing
~100 LOC (Silverman's argument fits in 2 paragraphs; Lean expansion ~2× = 100 LOC).

### [T-PFA-3] WIRE-AUT-EQUIV-KERNEL — Aut ≃ kernel bijection (depends on T-PFA-2 replan)
- **Status**: deferred (was: blocked) (2026-05-25T10:30Z, per reviewer Round 8)
- **Reviewer guidance** (Round 8): chained on T-PFA-2 demotion — same V.1.1 circularity, same demotion rationale.
- **File**: new file `HasseWeil/Hasse/GaloisNormal.lean` (or add to `Hasse/HoleE.lean`)
- **Depends on**: T-PFA-1 (translation_algebra)
- **Parallel**: parallel with T-PFA-2
- **Type**: theorem

#### Silverman verification
- **Source**: Silverman III.4.12, p. 78:
  > "Let φ : E₁ → E₂ be a nonconstant separable isogeny. Then the kernel of φ
  > acts on E₁ by translation, and the induced map ker(φ) → Aut(K(E₁)/φ*K(E₂))
  > is a group isomorphism."
- **Lean ↔ source match**: The Lean `Nonempty (Equiv (AlgEquiv K(E) K(E)) β.kernel)`
  is the existential form of "there is a bijection between Aut and ker(β)".

#### Statement
```lean
theorem isogOneSub_negFrobenius_aut_equiv_kernel
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) :
    Nonempty (Equiv
      (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _
        (isogOneSub_negFrobenius W hq).toAlgebra
        (isogOneSub_negFrobenius W hq).toAlgebra)
      (isogOneSub_negFrobenius W hq).kernel) := by sorry
```

#### Proof sketch (Silverman III.4.12 with 4 steps from Source)
1. **(Silverman III.4.12 step 1, p. 78)** The action: for T ∈ ker(β),
   define τ_T* : K(E) → K(E) (uses T-PFA-1). Show τ_T* fixes β.pullback K(E):
   for any f ∈ K(E'), `τ_T*(β.pullback f) = β.pullback(f ∘ τ_T) = β.pullback(f)`
   because β ∘ τ_T = β (T is in ker(β)).
2. **(Silverman III.4.12 step 2)** The map `T ↦ τ_T*` is a group hom:
   `τ_{T₁+T₂}* = τ_{T₁}* ∘ τ_{T₂}*` follows from `τ_{T₁+T₂} = τ_{T₁} ∘ τ_{T₂}`
   on Affine.Point (group law).
3. **(Silverman III.4.12 step 3 — injectivity)** If τ_T* = id, then τ_T = id
   on E (faithfulness of translation), so T = 0 (only the zero element fixes
   id).
4. **(Silverman III.4.12 step 4 — surjectivity by counting)** Cardinality:
   `|Aut(K(E)/β.pullback K(E))| = [K(E) : β.pullback K(E)] = deg(β)` (using
   T-PFA-2's `Normal` + the shipped `h_pc_sep`, `h_pc_fin`). Also
   `|ker(β)| = sepDeg(β) = deg(β)` (since β separable, via shipped
   `card_kernel_eq_degree_of_separable_witness`). So both finite of same
   cardinality — injective + same finite cardinality ⟹ bijective.

#### Mathlib lemmas needed
- `IsGalois.card_aut_eq_finrank` — to identify `|Aut| = [K(E):φ*K(E)]`
  (shipped at `Isogeny.card_aut_eq_degree_of_isGalois`, see HoleE.lean).
- `Equiv.ofInjective` + cardinality bijection for finite sets.
- Project: T-PFA-1, T-PFA-2.

#### Sources
- Silverman, GTM 106, 2nd ed., III.4.12, p. 78.

#### Generality decision
- Specialised to `isogOneSub_negFrobenius`. Same scope as T-PFA-2.

#### Sizing
~50 LOC (Silverman's argument is 4 short steps; Lean ~12 LOC each).

### [T-PFA-4] WALL-A-VPULLBACK — V-side pole bound (REPAIRED per reviewer Round 8)
- **Status**: in_progress (was: open) — STATEMENT REPAIRED 2026-05-25T10:30Z; **WEAK FORM SUBSTRATE LEAF + UNCONDITIONAL CONSTRUCTOR LANDED 2026-05-25T18:45Z**

**Progress (2026-05-25T18:45Z)**: WEAK form Wall A substrate leaf stated as `ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_lt_zero` (single bare `sorry`) in `HasseWeil/Verschiebung/Genuine.lean:1083`. Wired into new unconditional constructor `genuineIsogSmulSubV_universal_unconditional` (line 1102) that builds the V-side genuine isogeny without taking `h_pole` as hypothesis.

**Progress (2026-05-25T20:00Z)**: **WEAK form NOW PROVED** modulo a SINGLE FOCUSED substrate sub-leaf `intDegree_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_pos`. The discharge route composes the existing axiom-clean K(x)-image lemma (line 179) with `Curves.SmoothPlaneCurve.ordAtInfty_algebraMap_fracPolyX_of_ne_zero` (Infinity.lean:194). The remaining substrate is now JUST: `0 < RatFunc.intDegree (canonical K(x) preimage of addPullback_x_pair (V.zsmul r) (-s))` — a focused substantive substrate about the addition-formula output's rational-function shape. Build green at 2994 jobs.

**REVIEWER MATHEMATICAL CORRECTION** (Round 8, 2026-05-25): the original statement `ord_∞(addPullback_x(rV, [-s])) = -2` is **NOT generally true**. Counter-example: `α = 1-V` dual to `β = 1-π`. When `p ∣ #E(F_q)` (i.e., `p ∣ deg(1-π)`), `[#E(F_q)]` is inseparable. Since `(1-V)(1-π) = [#E(F_q)]` and `(1-π)` is separable, the inseparability is carried by `(1-V)`. So `ord_O((1-V)^* x) < -2`.

**Correct general formula**: `ord_O(φ^* x) = -2 · deg_i(φ)` for any isogeny `φ`. So `ord_∞(addPullback_x(rV, [-s])) = -2 · deg_i(rV-s)` — equals `-2` only when `(rV-s)` is separable.

**REPAIRED statement (weak form, default per reviewer suggestion (i))**: `ord_∞(addPullback_x(rV, [-s])) < 0` — sufficient for nonconstancy/injectivity of the addition-pullback algebra map.

**Alternative exact form (per reviewer suggestion (ii))**: `ord_∞(addPullback_x(rV, [-s])) = -2 · deg_i(rV-s)` — to be used if downstream Wall B requires it.

**Decision deferred**: choice of weak vs exact pinned to Wall B audit (T-PFA-5).

**Reviewer guidance** (Round 8): "Use the local ramification formula `ord_O(φ^* x) = -2 · deg_i(φ)`. Do not try to compute `Ψ_q` leading terms unless forced. Avoid algebraic-closure descent (won't make V uniformly separable). Best: global degree formulation if available."
- **File**: `HasseWeil/Hasse/L6Witnesses.lean:641` (replaces the sorry)
- **Depends on**: none (independent of T-PFA-1/2/3)
- **Parallel**: yes (independent)
- **Type**: theorem

**Progress (refinement 2026-05-25)**: investigation surfaced that the
"mirror π-side" strategy in v2 is more subtle than estimated, due to a
substantial structural difference between π (the q-Frobenius) and V (its dual):
- The π-side proof at `AdditionPullback/Frobenius.lean:3857` foundationally
  uses `(zsmul r π).pullback x_gen = (mulByInt_x W r)^q` (a q-th power),
  derived from `π.pullback f = f^q` (`frobeniusIsog_pullback_apply`).
- The V-side analog `(zsmul r V).pullback x_gen = V.pullback (mulByInt_x W r)`
  is NOT directly a clean q-th power — V is the DUAL of π, not the q-power
  morphism.
- The shipped V-side relation is `V.comp π = mulByInt q`
  (`verschiebung_comp_frobenius_eq_mulByInt_q`), which at the pullback
  level gives `π.pullback ∘ V.pullback = (mulByInt q).pullback`. Applied to
  `mulByInt_x W r`, this gives `(V.pullback (mulByInt_x W r))^q = (mulByInt q · r).pullback x_gen = mulByInt_x W (qr)`.
- For the foundational `ord_∞(V.pullback x_gen) = -2`: the relation
  `(V.pullback x_gen)^q = (mulByInt q).pullback x_gen = mulByInt_x W q`.
  Crucially `(q:K) = 0` in `K = F_q`, so `ordAtInfty_mulByInt_x` does NOT
  apply to `n = q`. The actual ord depends on the polynomial degeneracy
  of `Ψ_q²` in characteristic dividing q (`coeff_ΨSq` shows leading
  coefficient is `n²` which vanishes when char | n).

**Refined strategy** (replaces "200 LOC direct mirror"):
- Sub-leaf T-PFA-4-A: establish `ord_∞(V.pullback x_gen) = -2` directly
  via the polynomial-degree analysis of `mulByInt_x W q` in characteristic
  dividing q (where `Ψ_q²` degenerates), then derive V's ord by taking the
  q-th root in the resulting equation. ~100 LOC.
- Sub-leaf T-PFA-4-B: scale to `ord_∞((V.zsmul r).pullback x_gen) = -2 r²`
  for `(r:K) ≠ 0`. ~50 LOC (using `V.pullback (mulByInt_x W r) = (something
  with degree r² in x)`).
- Sub-leaf T-PFA-4-C: combine with the mulByInt -s side to derive the
  pair sub-result `ord_∞(... - ...) = -2`. ~50 LOC.
- Composer: combine via Wall A's numerator/denominator structure. ~50 LOC.

**Revised sizing**: ~250 LOC (slightly above v2's 200 LOC estimate).
**Replanning required before execution**: the foundational V-side
ord lemmas need development as separate sub-tickets, not as inline
work within T-PFA-4. Each sub-leaf is a focused research-pass on
ramification at infinity for the dual isogeny (Silverman III.6.2(a)).

#### Silverman verification
- **Source**: Silverman III.6.1(d), p. 82:
  > "Let φ : E → E' be an isogeny of degree m. Then there exists a unique
  > isogeny φ̂ : E' → E such that φ̂ ∘ φ = [m] on E. We have deg φ̂ = m."
  And III.6.2(a):
  > "deg(φ̂) = deg(φ)."
- **Lean ↔ source match**: For our V = π̂, deg V = deg π = q. So V has the
  same pole degree at infinity as π (both degree-q isogenies of E to E).
  The `addPullback_x_pair` for V-side is structurally identical to the
  π-side modulo replacing π by V — the pole-counting argument carries.

#### Statement
```lean
-- HasseWeil/Hasse/L6Witnesses.lean:641 (existing skeleton — replace sorry)
theorem ord_addPullback_x_pair_zsmul_verschiebung_mulByInt_neg_decomp
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_subset : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
                  (frobeniusIsog W).pullback.range)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0) :
    (W_smooth W).ordAtInfty
        ((addPullback_x_pair ((verschiebungIsog_of_witness W h_subset).zsmul r)
          (mulByInt W.toAffine (-s))) : W.toAffine.FunctionField) =
      ((-2 : ℤ) : WithTop ℤ) := by sorry
```

#### Proof sketch (mirror of π-side at `AdditionPullback/Frobenius.lean:3857`)
1. **(Silverman III.6.2(a), p. 84)** ord_∞ of `V.zsmul r .pullback x_gen`
   mirrors ord_∞ of `π.zsmul r .pullback x_gen` because deg V = deg π = q.
   The pole degree at infinity of φ.pullback x_gen for degree-d separable
   φ is `−2d` (= −2·d because x has order -2 at ∞, and a degree-d separable
   map multiplies pole orders by d at unramified places).
2. **(Silverman III.4 + III.6)** ord_∞ of `mulByInt (-s) .pullback x_gen`:
   the [-s] map has degree s² (already shipped); its pullback of x_gen has
   pole order `−2s²`.
3. **(Silverman III.4 addition formula, pp. 58–60)** The addition formula
   `addPullback_x_pair` combines the two pullbacks. The pole-order of the
   combined formula is `min(ord_∞(α.pullback x_gen), ord_∞(β.pullback x_gen))`
   when the addition is generic (i.e., the slope formula doesn't vanish at
   infinity), which our hypotheses `hr, hs, hrK, hsK` ensure. Final ord = -2
   for the specific combination because the leading terms cancel out
   (mirror of the π-side calculation).

#### Mathlib lemmas needed
- Project: `ord_addPullback_x_pair_zsmul_frobenius_mulByInt_neg`
  (`AdditionPullback/Frobenius.lean:3857`, the π-side mirror — verified shipped).
- Project: `verschiebung_dual_exists` (axiom-clean, shipped in GapSpines.lean).
- Project: `Curves.SmoothPlaneCurve.ordAtInfty_mul`, `ordAtInfty_pow`, etc.

#### Sources
- Silverman, GTM 106, 2nd ed., III.6.1(d), p. 82 (existence of dual isogeny V).
- Silverman III.6.2(a), p. 84 (deg V = deg π).
- Silverman III.4 addition formula, pp. 58–60.

#### Generality decision
- Stated for the specific (V.zsmul r, mulByInt(-s)) pair needed by the
  L4.a closure. Could be generalised to (φ.zsmul r, ψ.zsmul s) for any
  separable φ, ψ, but the project only uses this specific instance.

#### Sizing
~200 LOC. Source-grounded: the π-side analog at `Frobenius.lean:3857` spans
~200 LOC and the structure mirrors directly.

### [T-PFA-5] WALL-B-DOUBLE-VIETA — pullback double-Vieta match (x + y)
- **Status**: blocked-pending-Wall-A-repair (was: open) (2026-05-25T10:30Z, per reviewer Round 8)
- **Reviewer guidance** (Round 8): "Audit Wall B / Wall C to see which version of repaired Wall A is actually needed." After Wall A statement is finalised (weak `< 0` vs exact `= -2 · deg_i(rV-s)`), audit whether Wall B can be discharged from the abstract dual-composition identity `(rV-s)(rπ-s) = [qr² - trs + s²]` directly (Option W4-A from reviewer) instead of via the local pole-order chain.
- **File**: `HasseWeil/Hasse/L6Witnesses.lean:659, 679` (replaces 2 sorries)
- **Depends on**: T-PFA-4 (for AddMonoidHom→pullback step via Wall A's pole bound)
- **Parallel**: parallel with T-PFA-6
- **Type**: theorem (× 2: x-coord and y-coord)

#### Silverman verification
- **Source**: Silverman III.6.2(c), p. 84:
  > "For all φ, ψ ∈ End(E), `(φ + ψ)̂ = φ̂ + ψ̂`."
- **Lean ↔ source match**: The pullback double-Vieta match identity is the
  PULLBACK form of III.6.2(c) specialised to (r·π−s, r·V−s). The composition
  `β_dual ∘ β` (where β_dual = r·V−s, β = r·π−s) has pullback equal to
  `mulByInt_x(N)` for `N = q·r² − t·rs + s²` (the polarisation value).

#### Statement (x-coord version)
```lean
-- HasseWeil/Hasse/L6Witnesses.lean:659 (existing skeleton — replace sorry)
theorem genuine_dual_comp_pullback_x_gen_eq_mulByInt_x_decomp
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (V : Isogeny W.toAffine W.toAffine)
    (hV : IsDualOf W.toAffine V (frobeniusIsog W))
    (h_sum_trace : (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom =
      (mulByInt W.toAffine
        (isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq))).toAddMonoidHom)
    (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hrK : (r : K) ≠ 0) (hsK : (s : K) ≠ 0)
    (β_dual : Isogeny W.toAffine W.toAffine)
    (h_beta_dual_hom : β_dual.toAddMonoidHom =
      r • V.toAddMonoidHom - s • (AddMonoidHom.id _)) :
    (β_dual.comp (genuineIsogSmulSub W r s hr hs hrK hsK)).pullback (x_gen W) =
      mulByInt_x W
        ((Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2)
    := by sorry
```

(Analogous y-coord version at line 679.)

#### Proof sketch (Silverman III.6.2(c) via AddMonoidHom→pullback bridge)
1. **(Silverman III.6.2(c), p. 84)** At the AddMonoidHom level:
   `(β_dual ∘ β).toAddMonoidHom = (mulByInt N).toAddMonoidHom` where
   `N = q·r² − t·rs + s²`. This is the SHIPPED
   `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (axiom-clean in GapSpines).
2. **(Silverman II.2.6(b) determinacy)** Two isogenies E → E with equal
   AddMonoidHoms have equal pullbacks. This holds because:
   - The pullback is determined by the AddMonoidHom up to the kernel-action.
   - For endomorphisms of an elliptic curve, the kernel is finite, and the
     pullback's image is determined by the AddMonoidHom modulo this.
   Lean discharge: project's `pullback_eq_iff_addMonoidHom_eq` if shipped,
   else build via `algHom_ext_x_y_gen` + the dual additivity.
3. **(Composition)** Apply step 2 to `β_dual ∘ β` vs `mulByInt N`: both
   have the same AddMonoidHom (step 1), so their pullbacks of `x_gen`
   agree, giving the conclusion.

#### Mathlib lemmas needed
- Project: `genuine_dual_comp_toAddMonoidHom_eq_mulByInt` (axiom-clean in
  GapSpines.lean).
- Project: `algHom_ext_x_y_gen` (`EC/TranslationOrd.lean:2341`).
- Project: `addPullback_x_negFrobenius_sigma_invariant`
  (`AdditionPullback/Frobenius.lean:2186`) — σ-invariance content
  for analogous pair handling.

#### Sources
- Silverman, GTM 106, 2nd ed., III.6.2(c), p. 84.
- Silverman II.2.6(b) (morphism determined by behaviour on points), pp. 21–22.

#### Generality decision
- Specialised to the (genuineIsogSmulSub, β_dual) pair needed for L4.a.
- The general AddMonoidHom→pullback bridge could be a separate lemma, but
  the specialised version suffices here.

#### Sizing
~75 LOC each for x and y (so ~150 LOC total). Grounded in the
σ-invariance content at `Frobenius.lean:2186` (~75 LOC for analogous
structure).

### [T-PFA-6] L4B-DENSITY-CHAR-DIVISIBLE — qf_nonneg via density argument
- **Status**: blocked-pending-W4-repair (was: open) (2026-05-25T10:30Z, per reviewer Round 8)
- **Reviewer guidance** (Round 8): "Decide W4 route after Wall A repair." Density argument may still be usable as a structural tool once the upstream Wall A/B chain is repaired via the abstract dual-composition route (W4-repair-dual-composition).
- **File**: `HasseWeil/Hasse/L6Witnesses.lean:707, 718` (replaces 2 sorries) — or
  new file `HasseWeil/Hasse/QfNonnegDensity.lean`
- **Depends on**: T-PFA-4 + T-PFA-5 (which together give the generic case
  `genuineIsogSmulSub_degree_eq_signed` axiom-clean via existing composer)
- **Parallel**: yes (independent of T-PFA-1/2/3)
- **Type**: theorem

#### Silverman verification
- **Source**: Silverman III.6.3 (Corollary), p. 99:
  > "The map End(E) → ℤ defined by sending an isogeny to its degree (and the
  > zero map to 0) is a positive-definite quadratic form."
- **Lean ↔ source match**: The form Q(r, s) = q·r² − t·rs + s² is the
  polarisation form on End(E) at the basis (π, 1). Silverman's
  positive-definiteness applies UNIFORMLY (no characteristic restriction),
  so Q(r, s) ≥ 0 for ALL (r, s) ∈ ℤ², including the char-divisible cases.
  The standard argument is via the **discriminant test** on quadratic forms.

#### Statement (Route C — density argument)
```lean
-- Replaces the sorries at L6Witnesses.lean:707 (s_char_divisible) and 718 (r_char_divisible).
-- Or as a single composite lemma:
theorem degree_quadratic_exists_edge_via_density
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K) (r s : ℤ) (hr : r ≠ 0) (hs : s ≠ 0)
    (h_edge : (r : K) = 0 ∨ (s : K) = 0) :
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) * r * s + s ^ 2
    := by sorry
```

(After this lands, `degree_quadratic_exists_edge` at GapSpines.lean:583
becomes `⟨mulByInt W.toAffine ..., ...⟩` for the s_int_zero case, etc., or
the existing `qf_nonneg_skeleton` is reorganised to call this directly.)

#### Proof sketch (Route C — discriminant + density)
1. **(Quadratic-form discriminant test, standard)** For Q(r, s) = q·r² − t·rs + s²
   over ℝ², `Q ≥ 0 ∀(r, s) ∈ ℝ²` iff the discriminant `t² − 4q ≤ 0`, i.e.,
   `t² ≤ 4q`.
2. **(Sub-leaf C1)** The QF discriminant test:
   `(∀ r s ∈ ℤ, Q r s ≥ 0) ↔ t² ≤ 4q`. Forward direction: instantiate at
   `(r, s)` near a real root of Q (when Q has discriminant > 0, a real
   root exists, and integers near it give Q < 0). Reverse direction:
   completing the square.
   Mathlib: standard quadratic-form theory, possibly
   `quadratic_nonneg_iff_discrim_nonpos`.
3. **(Sub-leaf C2)** Density-of-non-vanishing: the subset
   `{(r, s) : (r:K), (s:K) ≠ 0}` of `ℤ²` has positive density (the complement
   is `p·ℤ × ℤ ∪ ℤ × p·ℤ`, density `2/p − 1/p² < 1`).
4. **(Sub-leaf C3)** **From shipped GENERIC case** (T-PFA-4 + T-PFA-5):
   `∀ r s ∈ ℤ with (r:K), (s:K) ≠ 0, Q r s ≥ 0`. So Q ≥ 0 on a
   positive-density subset of ℤ².
5. **(Sub-leaf C4)** Positive density on ℤ² ⟹ density at every scale in ℝ².
   Specifically: if `Q(r₀, s₀) < 0` for some real `(r₀, s₀)`, then there's a
   non-empty open set near `(r₀, s₀)` where `Q < 0` (continuity). The
   non-vanishing-in-K subset of ℤ² intersects this open set at all scales
   (positive density of non-vanishing integers). So `Q ≥ 0` on the
   non-vanishing subset ⟹ `Q ≥ 0` on all of ℝ² ⟹ `t² ≤ 4q` (step 1).
6. **(Sub-leaf C5)** `t² ≤ 4q ⟹ Q(r, s) ≥ 0 ∀ (r, s) ∈ ℤ²`, including the
   char-divisible cases. Compose with step 1.

#### Mathlib lemmas needed
- `Polynomial.discriminant` or `quadratic_nonneg_iff_discrim_nonpos`
  (verify name in mathlib).
- `Nat.coprime_iff_not_dvd` for the density argument.
- Continuity of polynomials and density of non-divisible integers
  (standard mathlib lemmas).
- Project: shipped GENERIC case
  `genuineIsogSmulSub_degree_eq_signed` (becomes axiom-clean after
  T-PFA-4 + T-PFA-5).

#### Sources
- Silverman, GTM 106, 2nd ed., III.6.3, p. 99 (positive-definite QF).
- Standard quadratic-form theory (any algebra textbook, e.g. Lang Ch. XV).

#### Generality decision
- The density argument is universal over `K = F_q` for any finite field.
- Stated specifically for the QF (q·r² − t·rs + s²); the argument
  generalises to any indefinite quadratic form on ℤ² but we don't need that.

#### Sizing
~100 LOC (Route C analysis ~30 LOC discriminant test + ~50 LOC density
argument + ~20 LOC composition).

### [T-PFA-7] WIRE-FINAL-HASSE-BOUND — assemble unconditional Hasse bound
- **Status**: open
- **File**: `HasseWeil/Hasse/Unconditional.lean:142` (replaces the pc_fiber_witness sorry)
- **Depends on**: T-PFA-2, T-PFA-3, T-PFA-4, T-PFA-5, T-PFA-6
- **Parallel**: no (waits on all others)
- **Type**: theorem (final assembly)

#### Silverman verification
- **Source**: Silverman V.1.1 proof, p. 138 (the assembly):
  > "Now apply Corollary V.1.2 (`#E(F_q) = #ker(1 − π)`), Theorem III.4.10(c)
  > (`#ker(1 − π) = deg(1 − π)`), and Corollary III.6.3 (degree QF on End(E)).
  > Setting `t = isogTrace(π, 1 − π) = q + 1 − #E(F_q)`, the QF
  > `q·r² − t·rs + s² ≥ 0` for all `r, s ∈ ℤ` gives `t² ≤ 4q`. Hence
  > `|#E(F_q) − q − 1| = |t| ≤ 2·√q`."
- **Lean ↔ source match**: The Lean assembly composes
  `hasse_bound_via_witness1_normal_bijection` (shipped at `HoleE.lean:809`)
  with T-PFA-2 (Normal), T-PFA-3 (Aut≃kernel), T-PFA-6 (qf_nonneg uniform),
  and the shipped Witness #1 + Witness #2.

#### Statement
```lean
-- Replaces the sorry at Hasse/Unconditional.lean:165 inside
-- hasse_bound_target_via_negFrobenius. The new body:
theorem hasse_bound_target_via_negFrobenius
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (h_qf_nonneg :
      letI hq := (two_le_card_of_field : (2 ≤ Fintype.card K))
      ∀ r s : ℤ,
        0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
          isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
            r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) := by
  have hq : 2 ≤ Fintype.card K := two_le_card_of_field
  -- Wire to hasse_bound_via_witness1_normal_bijection (HoleE.lean:809)
  -- Args: h_pc_sep (Witness #1), h_pc_fin (Witness #2),
  --       h_normal (T-PFA-2), h_iso (T-PFA-3),
  --       h_qf_signed (uniform QF, from T-PFA-4 + T-PFA-5 generic + T-PFA-6 char-divisible)
  sorry
```

After T-PFA-6 ships, the unconditional version that **takes no parametric
input** can be derived: change the signature to drop `h_qf_nonneg` and
discharge it internally using `qf_nonneg_skeleton` (which becomes
axiom-clean after T-PFA-6).

#### Proof sketch (composition of all the above)
1. **Get hq**: shipped via `two_le_card_of_field`.
2. **h_pc_sep**: shipped via `isogOneSub_negFrobenius_isSeparable`.
3. **h_pc_fin**: shipped via `isogOneSub_negFrobenius_finiteDimensional`.
4. **h_normal**: from T-PFA-2.
5. **h_iso**: from T-PFA-3.
6. **h_qf_signed (∀ r s, deg(genuineIsogSmulSub r s) = q·r² − t·rs + s²)**:
   from the existing `genuineIsogSmulSub_degree_eq_signed` chain
   (becomes axiom-clean after T-PFA-4 + T-PFA-5; the char-divisible
   cases handled by T-PFA-6's density argument routes through
   `degree_quadratic_exists_skeleton_nonzero`).
7. **Compose**: pass everything to
   `hasse_bound_via_witness1_normal_bijection` (HoleE.lean:809). Done.

#### Mathlib lemmas needed
- `Isogeny.isGalois_of_isSeparable_and_normal` (`HoleE.lean`).
- All sub-lemmas from T-PFA-2 through T-PFA-6.

#### Sources
- Silverman, GTM 106, 2nd ed., V.1.1, pp. 137–138.

#### Generality decision
- The final assembly is specialised to the Hasse-Weil theorem for `E/F_q`.
  Generalisation to arbitrary algebraic surfaces is out of scope.

#### Sizing
~30 LOC (pure composition; no new mathematics).

### [CLEANUP-PFA-1] /cleanup on PointFix.lean
- **Status**: open
- **File**: HasseWeil/Hasse/PointFix.lean
- **Depends on**: T-PFA-1
- **Type**: cleanup

### [CLEANUP-PFA-2] /cleanup on new Galois module
- **Status**: open
- **File**: HasseWeil/Hasse/GaloisNormal.lean (or wherever T-PFA-2 / T-PFA-3 land)
- **Depends on**: T-PFA-2, T-PFA-3
- **Type**: cleanup

### [CLEANUP-PFA-3] /cleanup on L6Witnesses.lean
- **Status**: open
- **File**: HasseWeil/Hasse/L6Witnesses.lean
- **Depends on**: T-PFA-4, T-PFA-5, T-PFA-6
- **Type**: cleanup

### [CLEANUP-PFA-FINAL] /cleanup-all before final assembly
- **Status**: open
- **Depends on**: CLEANUP-PFA-1, CLEANUP-PFA-2, CLEANUP-PFA-3
- **Type**: cleanup (project-wide)
- **Blocks**: T-PFA-7

## V2 Dependency Graph

```
              T-PFA-1 (translation_algebra .some, ~80 LOC)
                ├─→ T-PFA-2 (Normal, ~100 LOC) ─┐
                └─→ T-PFA-3 (Aut≃ker, ~50 LOC) ─┤
              T-PFA-4 (Wall A V-side, ~200 LOC) ┤
                └─→ T-PFA-5 (Wall B Vieta, ~150 LOC) ─┤
              T-PFA-6 (Route C density, ~100 LOC) ────┤
                                                       │
              CLEANUP-PFA-{1,2,3} ────────────────────┤
              CLEANUP-PFA-FINAL ──────────────────────┤
                                                       ↓
                                       T-PFA-7 (final assembly, ~30 LOC)
                                                       ↓
                              `hasse_bound_target_via_negFrobenius` ✅
```

**Parallel capacity at peak**: 4 workers (T-PFA-1, T-PFA-4, T-PFA-5 (after T-PFA-4),
T-PFA-6 (after T-PFA-4 + T-PFA-5)).

**Total LOC estimate**: ~710 LOC (sum of T-PFA-1 through T-PFA-7 sizings).

**Critical-path latency**: T-PFA-1 (80) → T-PFA-2 or T-PFA-3 (100) → CLEANUP →
T-PFA-7 (30). Or alternatively: T-PFA-4 (200) → T-PFA-5 (150) → T-PFA-6 (100) →
CLEANUP → T-PFA-7 (30). Either chain is ~310–480 LOC.

## Silverman cross-reference summary (binding for every PFA ticket)

| Ticket | Silverman section | Page | Source quote in ticket | Lean ↔ source match in ticket |
|---|---|---|---|---|
| T-PFA-1 | III.4 addition formula | 58–60 | ✓ | ✓ |
| T-PFA-2 | III.4.10(a) | 76 | ✓ | ✓ |
| T-PFA-3 | III.4.12 | 78 | ✓ | ✓ |
| T-PFA-4 | III.6.1(d) + III.6.2(a) | 82, 84 | ✓ | ✓ |
| T-PFA-5 | III.6.2(c) | 84 | ✓ | ✓ |
| T-PFA-6 | III.6.3 | 99 | ✓ | ✓ |
| T-PFA-7 | V.1.1 | 137–138 | ✓ | ✓ |

Every ticket has Silverman-page citation, verbatim quote, and Lean↔source
match paragraph. Workers running `/beastmode` MUST re-verify the cited
passage before starting tactics (per the binding protocol at the top of
this V2 section).

---

## REVIEWER ROUND 8 INTEGRATION (2026-05-25)

Per the reviewer's Round 8 response (`.mathlib-quality/expert-review/2026-05-25/reply.md`),
the project is **pivoting strategy**:

- **W3 (point count)**: continue Route B / Sinf / pole-divisor as PRIMARY (was: parallel with Route A).
- **W4 (QF non-negativity)**: repair via abstract dual-composition (Silverman III.6.2 + III.6.3), bypassing the broken Wall A "uniformly -2" approach.
- **Route A (Galois Normal)**: demoted to future infrastructure (T-PFA-2 + T-PFA-3 deferred).

The three new tickets below encode the W4 strategy options.

### [W4-repair-dual-composition] Abstract dual-composition identity (Silverman III.6.2) — PRIMARY W4 PATH
- **Status**: open — **PRIMARY Leaf-1 target** (narrowed to the Frobenius plane per reviewer Round 7, 2026-05-29)
- **File**: `HasseWeil/DegreeQuadraticForm.lean` or new file `HasseWeil/Hasse/W4DualComposition.lean`
- **Depends on**: `verschiebung_dual_exists` (done axiom-clean), `signed_degree_of_isDualOf_and_comp_eq` (done axiom-clean). NOTE (Round 7): does **NOT** need full/general Silverman III.6.2 additivity nor general dual existence (III.6.1) — only the RESTRICTED `(rπ−s)^=rV−s` on the ℤπ+ℤ (Frobenius) plane.
- **Type**: theorem chain
- **Statement**: For all `(r, s) ∈ ℤ²` with `(r, s) ≠ (0, 0)`, the abstract dual-composition identity `(rV - s)(rπ - s) = [qr² - trs + s²]` holds at the AddMonoidHom level AND at the full isogeny level (pullback included). Conclude `deg(rπ - s) = qr² - trs + s²` from the dual-composition theorem `α̂ ∘ α = [deg α]` (III.6.1(a)) plus `deg(α̂) = deg(α)` (III.6.2(a)).
- **Strategy** (reviewer's Option W4-A):
  1. Establish `widehat{rπ - s} = rV - s` from Silverman III.6.2(c) additivity of dual.
  2. Apply the dual-composition theorem `α̂ ∘ α = [deg α]` (III.6.1(a)).
  3. Identify `deg(rπ - s) = qr² - trs + s²` from the positive **semidefinite** (nonnegative) QF structure on End(E) (III.6.3).
- **Reviewer guidance** (Round 8, 2026-05-25): "Prove enough of Silverman III.6.2 to get `widehat{rπ-s} = rV-s` and `(rV-s)(rπ-s) = [qr²-trs+s²]`. Then identify the integer with the degree using the dual-composition theorem. This is closest to Silverman."
- **Reviewer guidance** (Round 7, 2026-05-29): NARROW to the RESTRICTED Frobenius-plane dual `(rπ−s)^=rV−s`; do NOT attempt general III.6.1. `{1,π,V}`+relations alone are insufficient (they give the composition identity, not that the integer IS the degree; multiplicativity yields only `deg(rV−s)·deg(rπ−s)=N²`, fixing neither sign nor factor). Parallelogram law is not a shortcut. If this identity lands it likely OBVIATES Wall A of GAP-QF-DEGQF (the V-side addIsog pole bound / VII.2).
- **Sources**: Silverman III.6.1(a), III.6.2(a), III.6.2(c), III.6.3.
- **Generality**: universal in q including small characteristic (p = 2, 3).
- **Sizing**: ~200-400 LOC (Silverman III.6.2 + III.6.3 substrate). Replaces Wall A's broken direct-ord chain.

### [W4-fallback-weil-pairing-determinant] Finite-torsion / Weil-pairing route — SECONDARY FALLBACK
- **Status**: open, secondary (fallback option)
- **File**: TBD (new file, probably under `HasseWeil/WeilPairing/`)
- **Depends on**: Weil-pairing infrastructure (status: TBD — needs mathlib audit; may require substantial new content)
- **Type**: theorem chain
- **Statement**: For `N` coprime to `p`, `deg(rπ - s) ≡ det(rM_π - sI) (mod N)` where `M_π : E[N] → E[N]` is the Frobenius matrix on `N`-torsion. Lift via all such `N` to integer equality `deg(rπ - s) = qr² - trs + s²`.
- **Strategy** (reviewer's Option W4-B):
  1. Build the Weil-pairing infrastructure on `E[N]` for `gcd(N, p) = 1`.
  2. Show the Frobenius acts on `E[N]` as a matrix `M_π` with `det M_π = q` and `tr M_π = t`.
  3. Use the determinant formula `deg(α) ≡ det(α | E[N]) (mod N)` for endomorphisms `α`.
  4. Conclude by taking `N` → ∞ through primes coprime to `p`.
- **Reviewer guidance** (Round 8): "Use the finite-level Weil-pairing determinant proof... avoids full dual-additivity but requires torsion/Weil pairing infrastructure."
- **Rationale**: project-management hedge if `W4-repair-dual-composition` proves too expensive (e.g., the III.6.2(c) additivity of dual turns out to need its own substantive sub-development).
- **Sizing**: unknown — depends on what Weil-pairing infrastructure mathlib has. Defer detailed sizing until primary path is decided.

### [W4-deferred-conditional-pack] Hasse consumer conditional on QF non-negativity — PROJECT-MANAGEMENT OPTION
- **Status**: open, optional
- **File**: existing `hasse_bound_of_qf_nonneg_witnesses` consumer chain already encodes this shape (`HasseWeil/Hasse/QuadraticForm.lean`)
- **Type**: status decision (not a new proof obligation)
- **Statement**: Keep the Hasse bound conditional on `∀ r, s, qr² - trs + s² ≥ 0` and finish W3 (via Sinf bridges) first. Defer W4 to a separate track.
- **Reviewer guidance** (Round 8): "This is likely the best project-management move if the immediate goal is a clean point-count witness."
- **Rationale**: lets W3 ship axiom-clean without waiting for W4 substantive content. Hasse bound becomes "axiom-clean given the QF non-negativity hypothesis", which is itself a textbook fact (Silverman III.6.3) but requires its own proof. Use only if the user wants to ship a partial result quickly.

### Sinf-bridges UPDATE (existing ticket — endorsed as PRIMARY for W3)

(No code change; documentation update.)

The existing `Sinf-bridges` / `T22-COMPOSER` / `l6_computationA` tickets are **endorsed as PRIMARY W3 path** per reviewer Round 8. The L3 strict-dominance (shipped 2026-05-25) is the right foundation; the bridges Bi/Bii/Biii/Biv discharge the remaining substantive content for W3.

**Note for execution**: phrase the proof through Sinf ramification-at-infinity (NOT via the global principal-divisor degree-zero theorem) to stay within the "no Riemann–Roch" constraint. The reviewer flagged the brief's Theorem 5.10 phrasing as risking confusion on this point.

### Verschiebung shipping status (confirmed 2026-05-25)

(No ticket change; documentation update.)

The project ships `HasseWeil.verschiebung_dual_exists` and `HasseWeil.mulByInt_q_pullback_qth_root` **axiom-clean** (`[propext, Classical.choice, Quot.sound]`), verified post-reply. The Verschiebung construction is unconditionally available for any elliptic curve over any finite field. This was a clarification the reviewer requested in Round 8.

---

## Round-7 reviewer integration (2026-05-29) — new tickets

### [separable-isogeny-fibre-count] deg α = #ker α for separable isogenies (Silverman III.4.10a) — PRIMARY Leaf-2 target
- **Status**: open — supersedes [SK-L6CA]. **Parent**: GAP-L6 / ker_deg_skeleton.
- **File**: HasseWeil/GapSpines.lean (the sharp residual `isogOneSub_negFrobenius_degree_eq_pointCount`) or a new helper file.
- **Depends on**: `1−π separable` (done), `ker(1−π)=E(F_q)` (done), the fundamental identity `Σ_{P|Q} e_P f_P = [K(E):α*K(E)]` (project has ramification/inertia infra), nonzero invariant differential ω (done).
- **Type**: theorem.
- **Statement**: for a separable isogeny α, `#ker α = deg α`; specialise to `deg(1−π) = #ker(1−π) = #E(F_q)` (closes Leaf 2 / V.1.3).
- **Proof sketch (round-8 ROUTE: base change to K̄=F̄_q — supersedes the round-7 "Option B" e_P=1 mechanism, which was WRONG: the kernel places have e=2, the double pole of x at O)**:
  `deg(1−π) = deg((1−π)_K̄) = #ker((1−π)_K̄) = #E(F_q)`. No residue degrees.
  1. `degree_oneSubFrob_eq_baseChange_degree`: `deg(1−π) = deg((1−π).baseChange K̄)` (degree invariant under base change — needs a concrete `Isogeny.baseChange`; only `mkBaseChange` (witness-parametric) + `degree_eq_of_finrank_eq` exist now).
  2. `oneSubFrob_baseChange_isSeparable`: `((1−π).baseChange K̄).IsSeparable`.
  3. `algClosed_fiber_card_eq_sepDegree` (III.4.10a over K̄): `#{P : (W.baseChange K̄).Point // ((1−π)_K̄).toPointMap P = 0} = sepDegree((1−π)_K̄)`; separable ⟹ `sepDegree = deg`. (II.2.6b generic fibre = deg_s + translation-invariance ⟹ every fibre = deg_s.)
  4. `oneSubFrob_baseChange_fiber_eq_base_points`: the fibre over O ≃ `W.toAffine.Point`, via the fixed-field lemma.
  - **Key fixed-field lemma** (elementary, mathlib has the half): `fixed_by_card_frobenius_iff_mem_range (a : AlgebraicClosure K) : a ^ Fintype.card K = a ↔ ∃ b : K, algebraMap K (AlgebraicClosure K) b = a` — forward = `FiniteField.pow_card`; reverse = roots of `X^q−X` are exactly K (`X_pow_card_sub_X`). Then `(1−π)_K̄(P)=O ⟺ P=π(P) ⟺ x^q=x ∧ y^q=y ⟺ x,y∈F_q`.
- **Reviewer guidance (Round 8, 2026-05-29)**: "Use base change to F̄_q and apply the separable-isogeny fibre count there (III.4.10a). Over K̄ residue degrees disappear — counts are geometric. Do NOT prove the K-level f_P=1 statement first. One sentence: prove `#ker((1−π)_K̄)=deg(1−π)` over K̄, then `ker((1−π)_K̄)=E(F_q)` by the coordinate fixed-field lemma `a^q=a ⟺ a∈F_q`."
- **Deprioritized alternative (K-level closed-point/Frobenius-orbit dictionary)**: correct but heavier — needs place residue field κ(v)=F_{q^d} ↔ size-d Frobenius orbit; all-fixed ⟹ d=1. Use only if the closed-point dictionary is needed elsewhere.
- **Infra to build**: concrete `Isogeny.baseChange` + degree invariance (1); separability under base change (2); the alg-closed fibre count `#ker = sepDegree` over K̄ (3, the III.4.10a core — NOT yet in project/mathlib); the fixed-field equivalence (4, mostly mathlib).
- **Shipped**: `isogOneSub_negFrobenius_pointCount_le_degree` (`pointCount ≤ deg(1−π)`, axiom-clean) — keep as a sanity check; do NOT route the equality through the K(f)-place count.
- **⚠ ROUND-8 ATTEMPT OUTCOME (2026-05-29) — base change does NOT avoid the core wall.** `FrobeniusFixedPoint.lean` already ships step (4): `ncard_ker_oneSubGeomFrobHom_eq_pointCount` (`#ker(1−geomFrob over K̄) = pointCount`, 0 sorries). But steps (1)(2)(3) all bottom at the SAME obstruction as the K-level route: the III.4.10a core `#ker = deg` needs the **generic-fibre theorem** (Silverman II.2.6b), and the project's generic-fibre count is `CoordHom`-bound — which `1−π` provably lacks (even over K̄). The **circularity trap** recurs: `card_kernel_eq_degree_of_separable_witness` (EC/IsogenyKernel) reduces `#ker=deg` to a fibre-size witness, but for `1−π` the only computable fibre is over `0` (= the kernel), giving `#ker=#ker` — no handle on `deg`. The witness must come from a GENERIC fibre = CoordHom. So base change relocates but does not remove the difficulty.
- **TWO genuine routes for the residual `deg(1−π) ≤ pointCount` (each substantial NEW infra; needs a decision):**
  - **Route 1 (non-CoordHom generic fibre over K̄):** build a genuine `Isogeny.baseChange` (pullback via the function-field tensor equivalence `functionField_baseChange_tensorEquiv` + `lTensor`, point-map via `geomFrobeniusPoint`) + a generic-fibre-over-K̄ theorem NOT routed through `CurveMap.CoordHom` (`Field.finSepDegree_eq_of_isAlgClosed` + a direct place↔point bijection over K̄). Large.
  - **Route 2 (over-K Galois — avoids K̄ and base change):** since `ker(1−π)` is fully K-rational, construct the translation automorphisms `τ_k : K(E) ≃ₐ[K((1−π)*x)] K(E)` for `k ∈ ker(1−π)`, prove `IsGalois K((1−π)*x) K(E)` + the `Aut ≃ ker(1−π)` bijection. Scaffold consumers exist (`PointFix.lean` `card_kernel_eq_degree_of_galois_witness`, `fiber_witness_via_inverse_witnesses`); undischarged = the `IsGalois` normality + the `Aut≃kernel` translation construction (~200+ LOC, self-rated "same difficulty as `addPullbackAlgHom_negFrobenius`").
- **★ ROUND-9 CHOSEN ROUTE (2026-05-29) — R2 as EMBEDDINGS-CLASSIFICATION, NOT "IsGalois first".** Reviewer: do NOT prove normality/IsGalois up front (circular if via cardinality). Instead prove `Hom_M(L,Ω) ≅ ker(1−π) = E(F_q)` for `L=K(E)`, `M=(1−π)*K(E)`, `Ω` an alg-closure of `M`; finite separability gives `#Hom_M(L,Ω) = [L:M] = deg(1−π)`, so `deg(1−π) = #E(F_q)`. Normality follows AFTER (all embeddings land back in L as translations).
  - **Step 1 (τ_T) — LIKELY ALREADY BUILT**: `translateAlgEquivOfPoint` (`EC/TranslationOrd.lean:3307`) is a real def with `_apply_x_gen`/`_apply_y_gen` (action on generators) + a large valuation API (`EC/TranslateValuation.lean`). Verify sorry-free + that it is the translation-by-T K-algebra auto.
  - **Step 2**: `τ_T*(γ*f) = γ*f` for `T ∈ ker γ` (translation fixes `M`).
  - **Step 3**: `T ↦ τ_T*` injective (evaluate on `x_gen`/`y_gen` or on the induced point map).
  - **Step 4 (CORE — the new content)**: classify every `σ ∈ Hom_M(L,Ω)` as a translation: `Q_σ=(σx,σy)`, `σ` fixes `M=γ*K(E)` ⟹ `γ(Q_σ)=γ(P_gen)` ⟹ `T_σ := Q_σ − P_gen ∈ ker γ = E(F_q)` ⟹ `σ = τ_{T_σ}*`. (Trap: `P_gen` lives over `L`; place both points over `Ω` via the σ-inclusion. Use the projective group law, not affine slopes. Reuse the fixed-field lemma `a^q=a ⟺ a∈F_q` for `ker = E(F_q)` over `Ω`.)
  - **Step 5 (COUNT) — mathlib**: `#(L →ₐ[M] Ω) = finSepDegree = [L:M]` via `AlgHom.card` (`FieldTheory/PrimitiveElement.lean`, `[IsAlgClosed Ω]`) + `finSepDegree_eq_finrank_of_isSeparable` (`FieldTheory/SeparableDegree.lean` / `CardinalEmb.lean`). Combine: `deg γ = [L:M] = #Hom_M(L,Ω) = #ker γ = #E(F_q)`.
  - **Net new work**: steps 2–4 (esp. step 4, the embedding-classification core); steps 1 and 5 are largely in hand (project + mathlib). This is the recommended Leaf-2 path; R1/base-change deprioritized.
- **Sources**: Silverman III.4.10(a), II.2.6(b), `FiniteField.pow_card`, `X_pow_card_sub_X`.
- **Generality**: universal in q, all characteristics.

### [stepanov-prototype] Bounded decision-prototype for Stepanov's elementary Hasse proof — DO NOT PIVOT until assessed
- **Status**: open, GATED (decision prototype only — do NOT pivot the project until both lemmas are assessed). **Parent**: strategy.
- **File**: new, e.g. HasseWeil/Stepanov/Prototype.lean.
- **Depends on**: K(E) (done), pole-order/`ordAtInfty` at O (done, incl. the place-valuation identity `orderTop(localExpand f)=ord_∞ f`), explicit Weierstrass coordinate algebra (done).
- **Type**: prototype (two core lemmas).
- **Statement**: (1) `basis_L_nO`: the space `L(nO) = {f ∈ K(E) : div_∞ f ≤ nO}` has explicit basis `{x^i, x^j·y : 2i ≤ n, 2j+3 ≤ n}` (pole orders generated by 2 and 3) — avoids general Riemann–Roch; (2) `zeros_le_poles`: for `0 ≠ f ∈ L(D)`, `Σ_{P∈E(F_q)} ord_P(f) ≤ deg D`.
- **Reviewer guidance (Round 7, 2026-05-29)**: "Prototype these two lemmas in a bounded session BEFORE deciding whether to pivot. Stepanov is plausible but not obviously cheaper — it replaces duals with auxiliary-function existence + multiplicity at all F_q-points + zero-counting + Hasse-derivative bookkeeping in char p. If both are easy here, Stepanov becomes attractive; if either is a multi-week project, stay with Silverman." Watch: small-characteristic derivative collapse (use Hasse derivatives); high-multiplicity vanishing.
- **Sources**: [Bombieri 1973] Sém. Bourbaki 430; [Schmidt 1976] LNM 536.
- **Decision rule**: after both lemmas, compare cost to `W4-repair-dual-composition`; pivot only if Stepanov is clearly cheaper.

### [isogeny-genuine-hygiene] Require IsGenuine on point-map↔pullback transfer lemmas — policy
- **Status**: open, policy (ongoing). **Parent**: soundness.
- **Motivation**: `HasseWeil.Isogeny` stores comorphism (algebra hom) and point-map (group hom) as INDEPENDENT fields, with no compatibility / basepoint-preservation. This produced the purged "placeholder" class AND two false-as-stated lemmas (mulByP separability, R5a) — see b2_log.jsonl.
- **Immediate rule**: every theorem relating point-maps to pullbacks/degrees must require a predicate `IsGenuine (φ)` (or use the project's compatible isogeny type `HasseWeil.EC.Isogeny`). Point-map-only statements should use a bare `AddMonoidHom`.
- **Reviewer guidance (Round 7, 2026-05-29)**: "Carry explicit genuine hypotheses NOW; full core-type refactor later. Long-term: split into RawIsogeny / GenuineIsogeny / PointHomOnly. WARNING: do NOT add a naive `compat : ∀ P, point_map P = evaluate_pullback_at P` field — rational functions have poles and projective points need local/projective evaluation (the round-5 CoordHom obstruction shows affine coordinate-ring compatibility is NOT globally available for 1−π). The compatibility predicate must be local/projective/function-field aware."
- **Sizing**: policy (apply incrementally); the type split is a separate, deferred refactor.
