# Mathlib / Project Audit for Tate Acyclicity (TICKET-0)

> Date: 2026-03-21
> Mathlib version: v4.29.0-rc3
> Agent: claude-main

---

## 1. Existing Project API

### Key definitions and signatures downstream tickets will use

**From `Presheaf.lean`:**
- `RationalLocData A` -- packages `(P : PairOfDefinition A, T : Finset A, s : A, hopen)` for the localization topology on `Localization.Away s`.
- `presheafValue (D : RationalLocData A) : Type` -- the completion of `Localization.Away D.s` with the localization topology. Has `CommRing`, `TopologicalSpace`, `IsTopologicalRing`, `CompleteSpace`, `T0Space` instances.
- `RationalLocData.canonicalMap (D : RationalLocData A) : A ->+* presheafValue D` -- the canonical `A -> A<T/s>`.
- `restrictionMap (D D' : RationalLocData A) (h : rationalOpen D'.T D'.s <= rationalOpen D.T D.s) : presheafValue D -> presheafValue D'` -- the restriction map (via `Completion.extensionHom`).
- `restrictionMapHom` -- the `RingHom` version.
- `restrictionMap_comp` -- presheaf functoriality.
- `restrictionMapMor` -- as a `CompleteTopCommRingCat` morphism.
- `RationalCovering A` -- a finite rational covering of a rational subset.
- `HasRestrictionMaps A` (class) -- requires `isUnit_canonicalMap_s` and `restrictionMapAlg_continuous` for all rational inclusions.
- `HasRestrictionMaps.discrete` -- instance for discrete rings.
- `productRestriction_injective_discrete` -- Theorem 8.28(c) for discrete rings.

**From `StructureSheaf.lean`:**
- `IsSheafy A` (class) -- separation axiom for rational coverings.
- `IsSheafyTopRing A` (class) -- full sheaf condition: `isEmbedding_productRestriction` + `gluing`. Implies `IsSheafy`.
- `IsSheafy.discrete` -- instance for discrete rings.
- `productRestrictionSub` -- product restriction indexed by `C.covers` as a subtype.
- `structureSheaf A` -- the structure sheaf valued in `CommRingCat`.
- `VPreObj`, `VObj` -- categories V^pre and V.

**From `RationalSubsets.lean`:**
- `IsRationalSubset U` -- predicate for rational subsets.
- `rationalOpen_inter` -- `R(T1/s1) cap R(T2/s2) = R(T1*T2 / s1*s2)` (Remark 7.30(5)).
- `IsRationalSubset.inter` -- intersection of rational subsets is rational.
- `rationalOpen_isOpen` -- rational subsets are open.

**From `LocalizationTopology.lean`:**
- `divByS t s : Localization.Away s` -- the element `t/s`.
- `locSubring P T s` -- the ring of definition `D = A0[t1/s, ..., tn/s]`.
- `locIdeal P T s` -- the ideal of definition `J = I * D`.
- `locNhd P T s n` -- the n-th neighborhood basis element.
- `locBasis P T s hopen : RingSubgroupsBasis (locNhd P T s)`.
- `locTopology P T s hopen : TopologicalSpace (Localization.Away s)`.

**From `RestrictedPowerSeries.lean`:**
- `MvPowerSeries.IsRestricted f` -- coefficients tend to 0 along the cofinite filter.
- `restrictedMvPowerSeriesSubring k A : Subring (MvPowerSeries (Fin k) A)` -- the restricted power series ring `A<T1,...,Tk>`, requires `[NonarchimedeanRing A]`.
- `IsStronglyNoetherian A` (class) -- `restrictedMvPowerSeriesSubring k A` is noetherian for all `k`.

**From `HuberRings.lean`:**
- `PairOfDefinition A` -- `(A0, I)` with `A0` open subring, `I` f.g. ideal, subspace topology is I-adic.
- `IsHuberRing A` (class) -- admits a pair of definition.
- `IsTateRing A` (class) -- Huber ring with a topologically nilpotent unit.
- `IsAdicHom` -- adic homomorphism between Huber rings.
- `IsTateRing.isAdicHom_of_continuous_with_pairs` -- Prop 6.25.

---

## 2. Wedhorn Remark 7.55 (Basic Rational Subset Decomposition)

**Status: NOT IN PROJECT.**

Searched for `R_f`, `basicRational`, `Remark 7.55`, `basic rational`, `decompos.*rational` in all project files. No result.

**Difficulty: Medium (~50-80 lines).**

Remark 7.55 says every rational subset `R(T/s)` can be written as a finite composition of basic inclusions of the form `R(f/1)` (localization at f) and `R(1/f)` (units where f is invertible). The proof reduces to the fact that `R({s,t1,...,tn}/s) = R({1,t1/s,...,tn/s}/1)` after localizing at s. This is needed by TICKET-3 (Prop 8.30) to reduce flatness of restriction maps to the two basic cases.

**Proposal:** Define `BasicRationalType` as an inductive with constructors `.localize (f : A)` and `.invert (f : A)`, then prove that every `rationalOpen T s` is a finite intersection of basic rational opens. The key lemma is that `R(T/s) = R(1/s) cap (bigcap_{t in T} R(t/s))` and that `R(t/s)` inside `R(1/s)` is `R(t*s^{-1}/1)`.

---

## 3. `RingHom.Flat` / `Module.Flat`

**Status: WELL-DEVELOPED in Mathlib.**

Key declarations found:

| Declaration | File | Notes |
|---|---|---|
| `Module.Flat` (class) | `Mathlib.RingTheory.Flat.Basic` | Definition via rTensor preserving injectivity |
| `RingHom.Flat` | `Mathlib.RingTheory.RingHom.Flat` | Ring hom variant |
| `Module.Flat.lTensor_exact` | `Mathlib.RingTheory.Flat.Basic` | Flat => lTensor preserves exactness |
| `Module.Flat.rTensor_exact` | `Mathlib.RingTheory.Flat.Basic` | Flat => rTensor preserves exactness |
| `Module.Flat.directSum` | `Mathlib.RingTheory.Flat.Basic` | Direct sum of flats is flat |
| `Module.Flat.dfinsupp` | `Mathlib.RingTheory.Flat.Basic` | Dfinsupp of flats is flat |
| `Module.Flat.trans` | `Mathlib.RingTheory.Flat.Stability` | Transitivity: flat over flat is flat |
| `Module.Flat.baseChange` | `Mathlib.RingTheory.Flat.Stability` | Base change of flat is flat |
| `IsLocalization.flat` | `Mathlib.RingTheory.Flat.Localization` | Localizations are flat |

**Gap: Finite products of flat algebras.**
Mathlib has `Module.Flat.directSum` and `Module.Flat.dfinsupp` (for `bigoplus` and `Pi_0`), but NOT for `Pi` (full product). For a *finite* type `iota`, one can derive `Flat R (Pi iota M)` from `dfinsupp_iff` plus `DFinsupp.equivFunOnFintype`, but this is not yet wrapped as an instance or lemma.

**Assessment: Trivial to build** (3-5 lines wrapping existing API). Needed by TICKET-3 (Cor 8.32).

---

## 4. `RingHom.FaithfullyFlat` / `Module.FaithfullyFlat`

**Status: GOOD in Mathlib.**

| Declaration | File | Notes |
|---|---|---|
| `Module.FaithfullyFlat` (class) | `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` | |
| `Module.FaithfullyFlat.of_comap_surjective` | `...FaithfullyFlat/Algebra` | flat + surjective on Spec => faithfully flat |
| `Module.FaithfullyFlat.of_flat_of_isLocalHom` | `...FaithfullyFlat/Algebra` | flat + local => faithfully flat |
| `Module.FaithfullyFlat.lTensor_exact_iff_exact` | `...FaithfullyFlat/Basic` | tensor reflects exactness |
| `Module.FaithfullyFlat.injective_of_tensorProduct` | `...FaithfullyFlat/Descent` | descent for injectivity |
| `Module.FaithfullyFlat.surjective_of_tensorProduct` | `...FaithfullyFlat/Descent` | descent for surjectivity |
| `Module.FaithfullyFlat.tensorProduct_mk_injective` | `...FaithfullyFlat/Algebra` | |
| `RingHom.FaithfullyFlat.codescendsAlong_*` | `...FaithfullyFlat/Descent` | bijective/injective/surjective descent |

**Assessment: The key lemma `of_comap_surjective` (flat + surjective on spectra => faithfully flat) is exactly what TICKET-3 (Cor 8.32) needs.** This is on the critical path and is already available.

---

## 5. Snake Lemma / 3x3 Lemma

**Status: AVAILABLE but ABSTRACT (in abelian category language).**

| Declaration | File | Notes |
|---|---|---|
| `ShortComplex.SnakeInput` | `Mathlib.Algebra.Homology.ShortComplex.SnakeLemma` | 3x3 input in abelian categories |
| `ShortComplex.SnakeInput.snake_lemma` | (same file) | 6-term exact sequence |
| `ShortComplex.SnakeInput.delta` | (same file) | connecting homomorphism |

The snake lemma is formalized for abelian categories via `ShortComplex.SnakeInput`. This structure requires `L0, L1, L2, L3 : ShortComplex C` with vertical maps, plus `L0` = kernel of `L1 -> L2`, `L3` = cokernel.

**Assessment for TICKET-4 (Lemma 8.33):** The 3x3 diagram argument CAN use this, but it requires setting up the concrete module maps as morphisms in `ModuleCat R` and verifying the `SnakeInput` axioms. This is **medium difficulty** (~40-60 lines of glue code). An alternative is a direct diagram chase on concrete module elements, which might be simpler for the specific case.

**Recommendation:** For TICKET-4, prefer a DIRECT element-based proof of the 3x3 lemma for the specific diagram, rather than instantiating the abstract `SnakeInput`. The abstract version's overhead (category theory, kernel/cokernel API) may outweigh the savings.

---

## 6. Artin-Rees Lemma

**Status: AVAILABLE in Mathlib.**

| Declaration | File | Type |
|---|---|---|
| `Ideal.exists_pow_inf_eq_pow_smul` | `Mathlib.RingTheory.Filtration` | `[IsNoetherianRing R] [Module.Finite R M] (N : Submodule R M) : exists k, forall n >= k, I^n smul top cap N = I^(n-k) smul (I^k smul top cap N)` |

This is exactly the Artin-Rees lemma in the form needed by TICKET-6 (Prop 6.18 open mapping theorem). The proof uses the Rees algebra and Hilbert basis theorem.

Additional related results in the same file:
- `Ideal.Filtration` -- structure for I-filtrations on modules.
- `Ideal.Filtration.Stable` -- stability predicate.
- `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` -- Krull's intersection theorem (local case).
- `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson` -- Krull's intersection (Jacobson case).

**Assessment: Fully available. No work needed.**

---

## 7. Module Topology / I-adic Topology on Modules

**Status: PARTIALLY AVAILABLE in Mathlib (two independent systems).**

### 7a. I-adic module topology (`Ideal.adicModuleTopology`)

| Declaration | File | Notes |
|---|---|---|
| `Ideal.adicModuleTopology` | `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology` | `I^n smul top` as nbhd basis of 0 on module M |
| `IsAdic` | (same file) | predicate that topology equals I-adic topology |
| `IsAdic.hasBasis_nhds_zero` | (same file) | neighborhood basis characterization |
| `IsAdic.isHausdorff_iff` | `...AdicCompletion/Topology` | relates `IsHausdorff I R` to `T2Space R` |
| `IsAdic.isPrecomplete_iff` | (same file) | relates to `CompleteSpace` |
| `IsAdic.isAdicComplete_iff` | (same file) | complete + separated characterization |

### 7b. Module topology (`moduleTopology`)

| Declaration | File | Notes |
|---|---|---|
| `moduleTopology R A` | `Mathlib.Topology.Algebra.Module.ModuleTopology` | finest topology making `+` and `smul` continuous |
| `IsModuleTopology R A` (class) | (same file) | asserts topology equals module topology |
| `IsModuleTopology.continuous_of_linearMap` | (same file) | **any** linear map from module-topology source is continuous |
| `IsModuleTopology.continuous_bilinear_of_finite_left` | (same file) | bilinear maps on f.g. modules are continuous |
| `IsModuleTopology.continuous_mul_of_finite` | (same file) | multiplication on f.g. algebras is continuous |

### 7c. Adic completion on modules

| Declaration | File | Notes |
|---|---|---|
| `AdicCompletion I M` | `Mathlib.RingTheory.AdicCompletion.Basic` | I-adic completion of module M |
| `AdicCompletion.map_surjective` | `...AdicCompletion/Exactness` | preserves surjectivity |
| `AdicCompletion.map_injective` | (same file) | preserves injectivity (f.g. over noetherian) |
| `AdicCompletion.map_exact` | (same file) | preserves exactness (f.g. over noetherian) |
| `AdicCompletion.ofTensorProduct` | `...AdicCompletion/AsTensorProduct` | `hat{R} tensor M -> hat{M}` |
| `AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian` | (same file) | `hat{R} tensor M ~= hat{M}` for f.g. M over noetherian |
| `AdicCompletion.flat_of_isNoetherian` | (same file) | `hat{R}` is flat over noetherian R |

**Assessment for TICKET-6:** The `moduleTopology` + `continuous_of_linearMap` gives automatic continuity of A-linear maps between f.g. modules. The `adicModuleTopology` gives the I-adic topology on modules. The gap is connecting these: proving that for a complete noetherian Tate ring, the module topology on f.g. modules equals the I-adic module topology. This is the content of Prop 6.18 and requires work (~100 lines including the open mapping theorem).

**Assessment for TICKET-4:** The `AdicCompletion.map_exact` is NOT directly usable because TICKET-4 works with Tate algebra completions (uniform space completions), not `AdicCompletion` (which is a projective limit `lim M/I^n M`). However, the proof strategy in `AdicCompletion/Exactness.lean` (direct construction of lifts using Artin-Rees) is a useful template.

---

## 8. `IsNoetherianRing` for Polynomial / Power Series

**Status: BOTH AVAILABLE.**

| Declaration | File | Notes |
|---|---|---|
| `Polynomial.isNoetherianRing` | `Mathlib.RingTheory.Polynomial.Basic` | `R noetherian => R[X] noetherian` |
| `PowerSeries.instIsNoetherianRing` | `Mathlib.RingTheory.PowerSeries.Ideal` | `R noetherian => R[[X]] noetherian` |
| `AdjoinRoot.instIsNoetherianRing` | `Mathlib.RingTheory.AdjoinRoot` | `R noetherian => R[X]/(f) noetherian` |
| `reesAlgebra` noetherian | `Mathlib.RingTheory.ReesAlgebra` | Rees algebra is noetherian over noetherian rings |

**NOT available:** `MvPowerSeries (Fin k) R` noetherian when `R` is noetherian. This is not in mathlib for general `k` (only for `k = 1` via `PowerSeries`).

**Assessment:** The univariate results are sufficient for TICKET-2A (Tate algebra `A<X>`). For `IsStronglyNoetherian`, the project already defines the predicate directly via `restrictedMvPowerSeriesSubring` rather than relying on `MvPowerSeries`.

---

## 9. `TensorProduct` Right Exactness

**Status: AVAILABLE.**

| Declaration | File | Notes |
|---|---|---|
| `lTensor_exact` | `Mathlib.LinearAlgebra.TensorProduct.RightExactness` | tensoring a right exact pair gives right exact pair |
| `rTensor_exact` | (same file) | same, right tensor |
| `lTensor_surjective` | (same file) | tensoring preserves surjectivity |
| `rTensor_surjective` | (same file) | same, right tensor |
| `LinearMap.rTensor_exact_iff_lTensor_exact` | (same file) | equivalence |

These are stated for `Function.Exact` (not short exact sequences), so they apply to pairs `f, g` with `range f = ker g` and `g` surjective.

**Assessment: Fully available. No work needed.** Needed by TICKET-2B (Remark 8.29).

---

## 10. `UniformSpace.Completion` Properties

**Status: WELL-DEVELOPED.**

| Declaration | File | Notes |
|---|---|---|
| `Completion.extension` | `Mathlib.Topology.UniformSpace.Completion` | extend uniformly continuous map to completion |
| `Completion.extension_coe` | (same file) | extension agrees on dense image |
| `Completion.continuous_extension` | (same file) | extension is continuous |
| `Completion.map` | (same file) | functorial map between completions |
| `Completion.map_coe` | (same file) | `map f (coe a) = coe (f a)` |
| `Completion.map_id` | (same file) | `map id = id` |
| `Completion.map_comp` | (same file) | `map g o map f = map (g o f)` |
| `Completion.denseRange_coe` | (same file) | coe has dense range |
| `Completion.isUniformEmbedding_coe` | (same file) | coe is a uniform embedding |
| `Completion.extensionHom` | `Mathlib.Topology.Algebra.UniformRing` | extend continuous ring hom to completion as `RingHom` |
| `Completion.extensionHom_coe` | (same file) | agreement on dense image |
| `Completion.coeRingHom` | (same file) | coe as `RingHom` |
| `Completion.mapRingHom` | (same file) | functorial ring hom between completions |
| `Completion.topologicalRing` | (same file) | completion of a topological ring is a topological ring |
| `Completion.algebra` | (same file) | completion inherits algebra structure |

**Assessment: Fully available.** The project already uses `extensionHom` heavily in `Presheaf.lean` for restriction maps. TICKET-2A/2B will also use these.

---

## 11. Restricted Power Series in Project

**Status: DEFINED, BASIC API.**

File: `Adic spaces/RestrictedPowerSeries.lean` (~256 lines, fully proved).

**What's defined:**
- `MvPowerSeries.IsRestricted f` -- coefficient sequence tends to 0.
- `restrictedMvPowerSeriesSubring k A : Subring (MvPowerSeries (Fin k) A)` -- requires `[NonarchimedeanRing A]`.
- Closure under `+`, `-`, `*`, `0`, `1` is proved (the multiplication proof is ~100 lines using the nonarchimedean property).
- `restrictedMvPowerSeriesSubring.instAlgebra` -- `A`-algebra structure.
- `IsStronglyNoetherian A` (class) -- all restricted power series rings are noetherian.

**What's missing for TICKET-2A:**
- No topology on the restricted power series ring (needed to make it a Tate ring).
- No evaluation/coefficient maps.
- No quotient API (`A<X>/(f)`).
- No univariate specialization.
- No connection to `Localization.Away` or `presheafValue`.

**Assessment: Medium work needed** for TICKET-2A. The subring definition is usable, but TICKET-2A needs to build a new concrete model for the univariate case with topology, rather than extending this multivariate subring.

---

## 12. Laurent Series

**Status: AVAILABLE in Mathlib (as Hahn series).**

| Declaration | File | Notes |
|---|---|---|
| `HahnSeries` (structure) | `Mathlib.RingTheory.HahnSeries.Basic` | formal power series with well-ordered support |
| `LaurentSeries R` (abbrev) | `Mathlib.RingTheory.LaurentSeries` | `= HahnSeries Z R` |
| `LaurentSeries.powerSeriesPart` | (same file) | non-negative part |
| `LaurentSeries.of_powerSeries_localization` | (same file) | localization map |
| `LaurentSeriesRingEquiv` | (same file) | completion of `K(X)` ~= `K((X))` |
| `LaurentSeriesAlgEquiv` | (same file) | as algebra equivalence |

**Assessment for TICKET-2A:** Mathlib's `LaurentSeries` is for the *field of fractions* of `K[[X]]`, NOT for the *restricted* Laurent series `A<zeta, zeta^{-1}>` needed by Wedhorn. The restricted Laurent series is a bilateral series with coefficients tending to 0 in both directions. TICKET-2A must build this from scratch (possibly as a quotient `A<X,Y>/(XY-1)` or as a direct coefficient-based definition). Mathlib's `HahnSeries` could potentially be used as the bilateral series model, but the topology would still need to be built.

---

## Critical Path Analysis

### On the Critical Path for Wedhorn 8.33 (TICKET-4)

These are BLOCKING for the hardest ticket:

1. **Tate algebra `A<X>` model with topology** (TICKET-2A) -- must be built from scratch. The project's `restrictedMvPowerSeriesSubring` provides the subring but lacks topology, quotient API, and univariate specialization. **Hard, ~200 lines.**

2. **Laurent algebra `A<zeta, zeta^{-1}>` model** (TICKET-2A) -- must be built from scratch. Mathlib's `LaurentSeries` is not suitable. **Hard, ~100 lines additional.**

3. **`AdicCompletion.map_exact`** -- available in mathlib for I-adic completions, but TICKET-4 works with uniform space completions of Tate algebras, not I-adic completions. The proof *strategy* (Artin-Rees based lifting) transfers, but the formal setup must be adapted. **Not directly usable but good template.**

4. **Snake lemma / 3x3 lemma** -- available abstractly via `SnakeInput`. For TICKET-4, a direct element-based argument is probably more efficient. **Available but indirect.**

5. **TensorProduct right exactness** (`lTensor_exact`, `rTensor_exact`) -- **fully available**, needed by TICKET-2B. No work needed.

6. **`Module.FaithfullyFlat.of_comap_surjective`** -- **fully available**, needed by TICKET-3 (Cor 8.32). No work needed.

### Nice to Have but Not Blocking

These are useful but can be worked around:

1. **Flat over finite products** -- not in mathlib as a dedicated lemma, but derivable from `dfinsupp_iff` in ~5 lines. Needed by TICKET-3.

2. **Wedhorn Remark 7.55** (basic rational subset decomposition) -- NOT in project. Needed by TICKET-3 to reduce Prop 8.30 to two basic cases. **Medium, ~60 lines.** Could alternatively be avoided by a different proof strategy, but the standard proof uses it.

3. **`PowerSeries.instIsNoetherianRing`** -- available in mathlib. May be useful for showing `A<X>/(f)` is noetherian.

4. **`AdjoinRoot.instIsNoetherianRing`** -- available. Useful for quotients of polynomial rings.

### Future / Zavyalov Phase Only

These are NOT needed for Wedhorn 8.28(b):

1. **MvPowerSeries noetherianity for general k** -- not in mathlib, not needed (the project's `IsStronglyNoetherian` is a direct axiom).

2. **`moduleTopology` = I-adic topology on f.g. modules** -- the full comparison theorem is needed for Prop 6.18 (TICKET-6) but not for the Zavyalov generalization. TICKET-6 can build the canonical topology directly from the I-adic module topology.

3. **Full `AdicCompletion.map_exact` integration** -- the formal I-adic completion framework in mathlib is extensive but is not needed for Wedhorn 8.33. The proof works directly with uniform space completions.

4. **Multivariate restricted power series API** -- the existing `restrictedMvPowerSeriesSubring` is sufficient for `IsStronglyNoetherian`. Further API (e.g., change-of-variables, substitution) is Zavyalov-phase only.

---

## Summary Table

| Item | Status | Difficulty if Missing | Needed By |
|---|---|---|---|
| Existing project API | Available | -- | All tickets |
| Remark 7.55 decomposition | **MISSING** | Medium (~60L) | TICKET-3 |
| `Module.Flat` API | Available | -- | TICKET-2B, 3 |
| `FaithfullyFlat.of_comap_surjective` | Available | -- | TICKET-3 |
| Flat over finite products | **MISSING** (trivial) | Trivial (~5L) | TICKET-3 |
| Snake lemma (abstract) | Available | -- | TICKET-4 (optional) |
| Artin-Rees lemma | Available | -- | TICKET-6 |
| I-adic module topology | Available (basic) | -- | TICKET-6 |
| Module topology continuity | Available | -- | TICKET-6 |
| `IsNoetherianRing` poly/power | Available | -- | TICKET-2A |
| TensorProduct right exactness | Available | -- | TICKET-2B |
| `Completion.extensionHom` etc. | Available | -- | All tickets |
| Restricted power series | Partial (subring only) | Hard (~200L for full) | TICKET-2A |
| Laurent series (restricted) | **MISSING** | Hard (~100L) | TICKET-2A, 4 |
| Tate algebra topology | **MISSING** | Hard (~100L) | TICKET-2A |
