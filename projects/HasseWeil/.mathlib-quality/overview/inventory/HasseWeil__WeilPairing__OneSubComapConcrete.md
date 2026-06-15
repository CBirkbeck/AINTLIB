# Inventory: ./HasseWeil/WeilPairing/OneSubComapConcrete.lean

**File summary:** 185 lines. Instantiates the general isogeny same-place + `e = 1` machinery at the concrete base-changed `1 − π` over `K̄` to produce the `affine` field of `ComapPointValuationWitness`. Five declarations (1 instance, 3 theorems, 1 def). No sorries, no `set_option maxHeartbeats`, no long proofs. The omega-coefficient value transport `omegaPullbackCoeff (1−π)_{K̄} = 1` is the key hub, used by two corollary theorems and then the assembly theorem.

---

## Declaration inventory

### `noncomputable local instance instDecEqACOSCC`

- **Type**: `DecidableEq (AlgebraicClosure K) := Classical.decEq _`
- **What**: Provides a `DecidableEq` instance on the algebraic closure `K̄` via the classical axiom; needed to satisfy instance requirements for later declarations in the section.
- **How**: Single application of `Classical.decEq`.
- **Hypotheses**: `K` a field with `Fintype K`.
- **Uses from project**: none
- **Used by**: `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one`, and all subsequent declarations (via typeclass resolution).
- **Visibility**: private (local instance)
- **Lines**: 57–57 (1 line)
- **Notes**: Local instance; suppresses the three linter warnings declared above it.

---

### `theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one`

- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) = 1`
- **What**: Proves that the omega-pullback coefficient of the base-changed `(1 − π)_{K̄}` equals `1`. This is the VALUE transport of the K-level identity `omegaPullbackCoeff (1−π) = 1` (Silverman III.5.5) across the base-change functoriality.
- **How**: `rw [omegaPullbackCoeff_baseChangePullback ...]` reduces the K̄-level coefficient to a `functionFieldMap` applied to the K-level value; then `rw [omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one ...]` substitutes `1`; finally `exact map_one _` closes.  The key lemmas are `omegaPullbackCoeff_baseChangePullback` (from `OmegaBaseChange.lean`) and `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (from `SilvermanIV14.lean`).
- **Hypotheses**: `2 ≤ Fintype.card K` (the isogeny `1−π` exists); `K` finite field of characteristic `p`, `|K| = p^r`; `W` elliptic over `K` and its base change over `K̄` elliptic.
- **Uses from project**: `omegaPullbackCoeff_baseChangePullback` (OmegaBaseChange.lean), `isogOneSub_negFrobenius` (Frobenius/AdditionPullback), `oneSubFrobeniusIsogBaseChange` (OneSubScaling.lean), `oneSubFrobeniusPullback_L` (IsogenyBaseChangeConcrete.lean), `oneSubFrobeniusIsogBaseChange_pullback` (OneSubScaling.lean), `omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one` (SilvermanIV14.lean)
- **Used by**: `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero`, `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range`, (indirectly) `comap_pointValuation_oneSub_eq_affine_of_residues`; also used in `OneSubAffineResidues.lean`.
- **Visibility**: public
- **Lines**: 71–81 (proof 5 lines)
- **Notes**: Axiom-clean (`[propext, Classical.choice, Quot.sound]`). This is the key hub from which the next two theorems are immediate corollaries.

---

### `theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero`

- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) ≠ 0`
- **What**: Corollary: the omega-pullback coefficient is nonzero, giving the separability input for the general `comap_pointValuation_isog_eq_affine`. Eliminates the need to carry `OmegaBaseChangeNeZero`.
- **How**: `rw [omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one ...]` then `exact one_ne_zero`.
- **Hypotheses**: Same as the `_eq_one` theorem.
- **Uses from project**: `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one` (this file)
- **Used by**: `comap_pointValuation_oneSub_eq_affine_of_residues` (this file); `OneSubAffineResidues.lean`.
- **Visibility**: public
- **Lines**: 86–90 (proof 1 line)
- **Notes**: Trivial corollary. Axiom-clean.

---

### `theorem omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range`

- **Type**: `(hq : 2 ≤ Fintype.card K) → omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K) (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) ∈ (algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField).range`
- **What**: Corollary: the omega-pullback coefficient lies in the image of `algebraMap K̄ → K̄(E)`, i.e., it is a constant function. This is the constancy input for `comap_pointValuation_isog_eq_affine`, formerly requiring the `sorryAx`-tainted `omegaPullbackCoeff_mem_F`.
- **How**: `rw [omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one ...]` reduces to showing `1 ∈ range(algebraMap ...)`, closed by `exact ⟨1, map_one _⟩`.
- **Hypotheses**: Same as the `_eq_one` theorem.
- **Uses from project**: `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_eq_one` (this file)
- **Used by**: `comap_pointValuation_oneSub_eq_affine_of_residues` (this file); `OneSubAffineResidues.lean`.
- **Visibility**: public
- **Lines**: 94–101 (proof 2 lines)
- **Notes**: Eliminates the previously sorry-tainted `omegaPullbackCoeff_mem_F` path. Axiom-clean.

---

### `def OneSubAffineResidues`

- **Type**: `(hq : 2 ≤ Fintype.card K) : Prop` — a universally quantified conjunction over all smooth points `P` of `E_{K̄}` with affine image `(1−π)P = (x, y)`: the two generator residues `val_P((1−π)^*x_gen − x) < 1`, `val_P((1−π)^*y_gen − y) < 1`, and the non-2-torsion-image unit condition `ord_P((1−π)^*u) = 0`.
- **What**: Names the isolated closed-point geometric residual for the `(1 − π)` comap identity: the claim that the opaque base-changed pullback `oneSubFrobeniusPullback_L` is compatible with the point map `id − π̄` at every affine closed point. This is a `Prop`-valued definition (a hypothesis placeholder), not a proof.
- **How**: Pure `Prop`-valued `def`; no proof content. Bundles three pointwise inequalities/equalities in a `∀ P x y h_ns, hQ → ... ∧ ... ∧ ...` form matching the input signature of `comap_pointValuation_isog_eq_affine`.
- **Hypotheses**: (none — it is a `Prop`, the content IS the hypothesis)
- **Uses from project**: `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`, `x_gen`, `y_gen`, `alpha_star_u`, `SmoothPlaneCurve.pointValuation`, `SmoothPlaneCurve.ord_P`
- **Used by**: `comap_pointValuation_oneSub_eq_affine_of_residues` (carried as `hres`); `OneSubAffineResidues.lean` (there it is discharged).
- **Visibility**: public
- **Lines**: 118–143 (definition body, no proof)
- **Notes**: This is an explicitly "parked" residual placeholder: the comment states the fully unconditional version is in `OneSubAffineResidues.lean`. The definition isolates the hard closed-point geometric content.

---

### `theorem comap_pointValuation_oneSub_eq_affine_of_residues`

- **Type**: Given `hq`, `hres : OneSubAffineResidues W p r hq`, a smooth point `P`, nonsingularity data `h_ns`, and the hypothesis `hQ` that the isogeny maps `P` to `some x y h_ns`: `(pointValuation P).comap ((1−π)^*).toRingHom = pointValuation ⟨x, y, h_ns⟩`.
- **What**: The affine comap-valuation identity for `(1 − π)_{K̄}`: the comap of the point valuation at `P` along the function-field pullback of the base-changed `1 − π` equals the point valuation at the image `(x, y)`. This is the `affine` field of `ComapPointValuationWitness` (carried-residue form).
- **How**: `obtain ⟨hx, hy, h_u⟩ := hres P h_ns hQ` destructs the residue datum; then `exact comap_pointValuation_isog_eq_affine (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range ...) (omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero ...) P h_ns hx hy h_u` assembles all inputs for the general headline.
- **Hypotheses**: `2 ≤ Fintype.card K`; `hres : OneSubAffineResidues W p r hq`; the smooth point `P` maps to the affine point `(x, y)` under `(1−π)`.
- **Uses from project**: `comap_pointValuation_isog_eq_affine` (AdditionPullback/SamePlace.lean), `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_mem_range` (this file), `omegaPullbackCoeff_oneSubFrobeniusIsogBaseChange_ne_zero` (this file), `OneSubAffineResidues` (this file), `oneSubFrobeniusIsogBaseChange`, `oneSubFrobeniusPullback_L`
- **Used by**: Unused in this file; used in `OneSubAffineResidues.lean`.
- **Visibility**: public
- **Lines**: 164–183 (proof 5 lines: `obtain` + `exact`)
- **Notes**: The "carried-residue" form; the unconditional version (with `OneSubAffineResidues` discharged) is `comap_pointValuation_oneSub_eq_affine` in `OneSubAffineResidues.lean`. Proof is very short once all ingredients are assembled.
