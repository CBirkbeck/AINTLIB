/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.BridgeFrobenius
import HasseWeil.Curves.Differentials
import HasseWeil.Hasse.HoleE

/-!
# Differential pullback for the addition isogeny `1 − π`

Witness #1 of `hasse_bound_via_signed_QF_negFrobenius` needs the omega-pullback
coefficient of `isogOneSub_negFrobenius W hq` to equal `1`. This file assembles the
separability of `1 − π` from that coefficient via the cotangent (T-II-4-004) criterion,
and computes the supporting coefficients for `mulByInt (-1)` and `negFrobeniusIsog`.

The omega-coefficient identity itself is reduced to a Silverman III.5.2 additivity
hypothesis (the `id + (-1)·π` decomposition); several witness-parametric consumers below
take that hypothesis in different shapes and produce the separability conclusion.

## Main results

* `isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero`: the T-II-4-004
  separability criterion for `1 − π`, unconditional.
* `omegaPullbackCoeff_mulByInt_neg_one`, `omegaPullbackCoeff_negFrobeniusIsog`: the
  supporting omega-coefficient computations.
* `isogOneSub_negFrobenius_finiteDimensional`: Witness #2 (finite-dimensionality).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5.2 (additivity),
  III.5.3 (`[m]*ω = m·ω`), III.5.5 (Frobenius is purely inseparable).
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- **Witness-parametric Witness #1 omega-coefficient closer**: takes the
Silverman III.5.2 additivity witness for `isogOneSub_negFrobenius` and
produces the deliverable `omegaPullbackCoeff = 1`.

The additivity hypothesis is exactly the III.5.2 specialization to the
`1 − π = 1·id + (-1)·π` decomposition. Closing it via the witness-parametric
bridge chain (`omegaPullbackCoeff_add_of_leading_witness`,
`FormalIsogenySeries.lean`; the unconditional
`omegaPullbackCoeff_add_via_bridge_of_constCoeff` was deleted 2026-06-11 as
refutable) is the substantive piece — once that's in hand, this lemma fires
the closure axiom-clean. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness
    (hq : 2 ≤ Fintype.card K)
    (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      ((1 : ℤ) : KE) * omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        ((-1 : ℤ) : KE) * omegaPullbackCoeff W (frobeniusIsog W)) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  have h := omegaPullbackCoeff_m_plus_n_frob_of_witness W
    (isogOneSub_negFrobenius W hq) 1 (-1) h_add
  simpa using h

/-- **Hom decomposition for `1 − π`**: the rational-point map of
`isogOneSub_negFrobenius W hq` equals the sum of `(Isogeny.id W.toAffine).toAddMonoidHom`
and `(negFrobeniusIsog W).toAddMonoidHom`. (Historically the `h_add` input of the
deleted-2026-06-11 `omegaPullbackCoeff_add_via_bridge_of_constCoeff`; retained as the
group-law decomposition identity in its own right.) -/
theorem isogOneSub_negFrobenius_toAddMonoidHom_decomposition
    (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).toAddMonoidHom =
      (Isogeny.id W.toAffine).toAddMonoidHom +
        (negFrobeniusIsog W).toAddMonoidHom := by
  ext P
  change P - (frobeniusIsog W).toAddMonoidHom P =
    (Isogeny.id W.toAffine).toAddMonoidHom P +
      (negFrobeniusIsog W).toAddMonoidHom P
  rw [Isogeny.id_toAddMonoidHom, AddMonoidHom.id_apply,
    negFrobeniusIsog_toAddMonoidHom_apply, sub_eq_add_neg]

/-- **Composed Witness #1**: separability of `isogOneSub_negFrobenius W hq`,
taking only the additivity sum hypothesis (Silverman III.5.2 input for the
specific `1 − π = 1·id + (-1)·π` decomposition) and the T-II-4-004
differential separability criterion.

Hypothesis count drops from two (omega-coeff + T-II-4-004) to two of a
sharper shape (additivity sum + T-II-4-004) — the additivity sum is the
direct discharge target of the T-DIFFERENTIAL-PULLBACK-ADDITION-MAP
infrastructure, removing one layer of indirection. -/
theorem isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004
    (hq : 2 ≤ Fintype.card K)
    (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      ((1 : ℤ) : KE) * omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        ((-1 : ℤ) : KE) * omegaPullbackCoeff W (frobeniusIsog W))
    (h_sep_iff : (isogOneSub_negFrobenius W hq).IsSeparable ↔
      omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ≠ 0) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_witnesses W hq
    (omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_additivity_witness
      W hq h_add)
    h_sep_iff

/-- **Composed Witness #1 (sharper)**: separability of `isogOneSub_negFrobenius W hq`,
taking the additivity sum, Witness #2 (FiniteDim), and the algebra-Kähler bridge
(Subsingleton ↔ pullbackKaehler injective) as inputs.

Composes Commit 13 (T-II-4-004 full iff witness-parametric) with the existing
additivity-Witness-1 closer. Replaces the iff hypothesis with the two
witnesses underlying it; when the bridge discharges (cotangent-sequence
argument unblocked by Sub-piece A break-through), this becomes an
unconditional consumer of Witness #2 only. -/
theorem isogOneSub_negFrobenius_isSeparable_of_additivity_finiteDim_bridge
    (hq : 2 ≤ Fintype.card K)
    (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      ((1 : ℤ) : KE) * omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        ((-1 : ℤ) : KE) * omegaPullbackCoeff W (frobeniusIsog W))
    (h_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_bridge : @Subsingleton (@KaehlerDifferential W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ (isogOneSub_negFrobenius W hq).toAlgebra) ↔
      Function.Injective (isogOneSub_negFrobenius W hq).pullbackKaehler) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004 W hq h_add
    (isSeparable_iff_omegaPullbackCoeff_ne_zero_of_witnesses W
      (isogOneSub_negFrobenius W hq) h_fin h_bridge)

/-- **{addPullback_x_negFrobenius} is alg-indep over K (axiom-clean)**:
the singleton family is algebraically independent over `K`, by transcendentality
(`addPullback_x_transcendental_negFrobenius`). -/
theorem addPullback_x_negFrobenius_algebraicIndependent
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    AlgebraicIndependent K
      (![addPullback_x W (negFrobeniusIsog W)] :
        Fin 1 → W.toAffine.FunctionField) := by
  rw [algebraicIndependent_unique_type_iff]
  exact addPullback_x_transcendental_negFrobenius W hq hxy

/-- **{addPullback_x_negFrobenius} is a transcendence basis (axiom-clean)**:
combines alg-independence with `trdeg K K(E) = 1` to yield the 1-element
transcendence basis via `AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite`. -/
theorem addPullback_x_negFrobenius_isTranscendenceBasis
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    IsTranscendenceBasis K
      (![addPullback_x W (negFrobeniusIsog W)] :
        Fin 1 → W.toAffine.FunctionField) := by
  apply AlgebraicIndependent.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    (addPullback_x_negFrobenius_algebraicIndependent W hq hxy)
  rw [weierstrass_functionField_trdeg_eq_one W]
  simp

/-- **K(E) is algebraic over `Algebra.adjoin K {addPullback_x_negFrobenius}`
(axiom-clean, Path (a) step 4)**: applying `IsTranscendenceBasis.isAlgebraic`
to the trans-basis singleton gives the relative algebraicity over the
adjoin subalgebra.

@-explicit `Subalgebra.toAlgebra` to bypass typeclass-synthesis flakiness
on the specific Weierstrass term `addPullback_x W (negFrobeniusIsog W)`. -/
theorem addPullback_x_negFrobenius_isAlgebraic_subalgebra
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    @Algebra.IsAlgebraic
      (↥(Algebra.adjoin K (Set.range (![addPullback_x W (negFrobeniusIsog W)] :
        Fin 1 → W.toAffine.FunctionField))))
      W.toAffine.FunctionField _ _
      (Subalgebra.toAlgebra _) :=
  (addPullback_x_negFrobenius_isTranscendenceBasis W hq hxy).isAlgebraic

/-- **addPullback_x is in the negFrobenius pullback's range (axiom-clean)**:
direct identification via the `addPullbackAlgHom` construction —
`x_gen` maps to `addPullback_x`. -/
theorem addPullback_x_negFrobenius_mem_range
    (hq : 2 ≤ Fintype.card K) :
    addPullback_x W (negFrobeniusIsog W) ∈
      (isogOneSub_negFrobenius W hq).pullback.range := by
  refine ⟨x_gen W.toAffine, ?_⟩
  change addPullbackAlgHom_negFrobenius W hq (x_gen W.toAffine) =
    addPullback_x W (negFrobeniusIsog W)
  unfold addPullbackAlgHom_negFrobenius addPullbackAlgHom_negFrobenius_of_inj addPullbackAlgHom
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  change (addCoordAlgHom (negFrobeniusIsog_addNonInverse W)).toRingHom
    (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) =
    addPullback_x W (negFrobeniusIsog W)
  change addCoordRingHom (negFrobeniusIsog_addNonInverse W) _ = _
  unfold addCoordRingHom
  rw [show algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X =
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) from rfl]
  rw [AdjoinRoot.lift_mk]
  simp [addBaseHom, Polynomial.eval₂_C]

/-- **Algebraicity over α.pullback.range** (Path (a) step 5, witness-parametric):
given `addPullback_x ∈ (isogOneSub_negFrobenius W hq).pullback.range`,
lift the IsAlgebraic from the smaller adjoin subalgebra to α.pullback.range.

Uses `IsAlgebraic.tower_top_of_subalgebra_le` element-wise. -/
theorem addPullback_x_negFrobenius_isAlgebraic_range_of_witness
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W))
    (h_mem : addPullback_x W (negFrobeniusIsog W) ∈
      (isogOneSub_negFrobenius W hq).pullback.range) :
    @Algebra.IsAlgebraic
      (↥(isogOneSub_negFrobenius W hq).pullback.range)
      W.toAffine.FunctionField _ _
      (Subalgebra.toAlgebra _) := by
  have h_le : Algebra.adjoin K
      (Set.range (![addPullback_x W (negFrobeniusIsog W)] :
        Fin 1 → W.toAffine.FunctionField)) ≤
      (isogOneSub_negFrobenius W hq).pullback.range := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    fin_cases i
    exact h_mem
  have h_alg_adjoin :=
    addPullback_x_negFrobenius_isAlgebraic_subalgebra W hq hxy
  refine @Algebra.IsAlgebraic.mk
    (↥(isogOneSub_negFrobenius W hq).pullback.range)
    W.toAffine.FunctionField _ _ (Subalgebra.toAlgebra _) (fun y => ?_)
  exact (h_alg_adjoin.isAlgebraic y).tower_top_of_subalgebra_le h_le

/-- **Algebraicity over α.pullback.range (UNCONDITIONAL, axiom-clean)**:
discharges Commit 26 by feeding Commit 27's membership witness. -/
theorem addPullback_x_negFrobenius_isAlgebraic_range
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    @Algebra.IsAlgebraic
      (↥(isogOneSub_negFrobenius W hq).pullback.range)
      W.toAffine.FunctionField _ _
      (Subalgebra.toAlgebra _) :=
  addPullback_x_negFrobenius_isAlgebraic_range_of_witness W hq hxy
    (addPullback_x_negFrobenius_mem_range W hq)

/-- **Algebraicity over the type-synonym wrapper (UNCONDITIONAL, axiom-clean,
Path (a) step 8)**: `K(E)` is algebraic over `IsogenyAlgebraSource W
(isogOneSub_negFrobenius W hq)`.

Transfers Commit 28's algebraicity-over-`α.pullback.range` to the type-synonym
form via the bijective range iso `α.pullback : K(E) ≃ₐ[K] α.pullback.range`. -/
theorem isogOneSub_negFrobenius_isAlgebraic_synonym
    (hq : 2 ≤ Fintype.card K)
    (hxy : AddNonInverse W (negFrobeniusIsog W)) :
    Algebra.IsAlgebraic
      (IsogenyAlgebraSource W (isogOneSub_negFrobenius W hq))
      W.toAffine.FunctionField := by
  have h_range := addPullback_x_negFrobenius_isAlgebraic_range W hq hxy
  let α := isogOneSub_negFrobenius W hq
  let e : W.toAffine.FunctionField ≃ₐ[K] α.pullback.range :=
    AlgEquiv.ofInjective α.pullback α.pullback_injective
  refine ⟨fun y => ?_⟩
  have h_y_alg := h_range.isAlgebraic y
  obtain ⟨p, hp_ne, hp_eval⟩ := h_y_alg
  let f : α.pullback.range →+* W.toAffine.FunctionField := e.symm
  refine ⟨p.map f, ?_, ?_⟩
  · have hf_inj : Function.Injective f := e.symm.injective
    exact (Polynomial.map_ne_zero_iff hf_inj).mpr hp_ne
  · -- The synonym's algebra map is `α.pullback ∘ e.symm`, i.e. the inclusion `range → K(E)`.
    have h_e_inv : ∀ (z : α.pullback.range),
        α.pullback (e.symm z) = (z : W.toAffine.FunctionField) := by
      intro z
      change α.pullback (e.symm z) = z.1
      exact congrArg Subtype.val (e.apply_symm_apply z)
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map] at hp_eval ⊢
    refine Eq.trans (Polynomial.eval₂_congr ?_ rfl rfl) hp_eval
    apply RingHom.ext
    intro z
    change α.pullback (e.symm z) = (z : W.toAffine.FunctionField)
    exact h_e_inv z

/-- **WITNESS #2 UNCONDITIONAL (axiom-clean)**: K(E) is finite-dimensional
over `(isogOneSub_negFrobenius W hq).pullback K(E)` (via `α.toAlgebra.toModule`).

Composes:
* Commit 18 (`isogeny_finiteDimensional_of_isAlgebraic_synonym`): the
  type-synonym Witness #2 producer.
* Commit 19 (`isogenyAlgebraSource_essFiniteType` UNCONDITIONAL): synonym
  EssFiniteType from FractionRing localization + `EssFiniteType.of_comp`.
* Commit 29 (`isogOneSub_negFrobenius_isAlgebraic_synonym` UNCONDITIONAL):
  synonym IsAlgebraic from trans-deg + IsTranscendenceBasis + range iso.

This closes the bound's Witness #2 fully unconditional. T-II-4-004's full
iff (Commit 17 = `isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`)
chains to fully unconditional `α.IsSeparable ↔ ω-coeff ≠ 0` for the
negFrobenius case. -/
theorem isogOneSub_negFrobenius_finiteDimensional
    (hq : 2 ≤ Fintype.card K) :
    @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule := by
  haveI := isogOneSub_negFrobenius_isAlgebraic_synonym W hq
    (negFrobeniusIsog_addNonInverse W)
  exact isogeny_finiteDimensional_of_isAlgebraic_synonym W (isogOneSub_negFrobenius W hq)

/-- **T-II-4-004 FULLY UNCONDITIONAL for negFrobenius (axiom-clean)**:
the iff `α.IsSeparable ↔ omegaPullbackCoeff W α ≠ 0` for
`α = isogOneSub_negFrobenius W hq` lands axiom-clean with no remaining
hypotheses (modulo only the `hq : 2 ≤ Fintype.card K` standing on
the bound's signature).

One-line composition of Commit 17 (witness-parametric iff on FiniteDim)
+ Commit 30 (Witness #2 UNCONDITIONAL).

This closes T-II-4-004 for the bound's purpose. The bound's deferred-
witness count drops to 2 (Witness #1 unconditional + the additivity
discharge for general α through BRIDGE-001). -/
theorem isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero
    (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).IsSeparable ↔
      omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ≠ 0 :=
  isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim W
    (isogOneSub_negFrobenius W hq)
    (isogOneSub_negFrobenius_finiteDimensional W hq)

-- `[Fintype K]` is unused in the statement but needed transitively by the proof's
-- instance resolution, so it cannot be `omit`ted.
set_option linter.unusedFintypeInType false in
/-- **`alpha_star_u` for `mulByInt (-1)` equals `-u_gen` (axiom-clean)**:
the negation isogeny pulls `u_gen = 2y + a₁x + a₃` to its negative
(via `mulByInt_pullback_y_neg_one`). -/
theorem alpha_star_u_mulByInt_neg_one :
    alpha_star_u W (mulByInt W.toAffine (-1)) = -u_gen W := by
  change 2 * (mulByInt W.toAffine (-1)).pullback (y_gen W) +
      algebraMap K W.toAffine.FunctionField W.a₁ *
        (mulByInt W.toAffine (-1)).pullback (x_gen W) +
      algebraMap K W.toAffine.FunctionField W.a₃ =
      -(2 * y_gen W + algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
        algebraMap K W.toAffine.FunctionField W.a₃)
  rw [mulByInt_pullback_y_neg_one, mulByInt_pullback_x_neg_one]
  ring

-- `[Fintype K]` is unused in the statement but needed transitively by the proof.
set_option linter.unusedFintypeInType false in
/-- **omegaPullbackCoeff for `mulByInt (-1)` equals `-1` (axiom-clean)**:
direct via `omegaPullbackCoeff_unique` + the spec equation, using
`alpha_star_u_mulByInt_neg_one` and `mulByInt_pullback_x_neg_one`.

This is independent of the Wronskian-based `omegaPullbackCoeff_mulByInt`,
so it lands axiom-clean (`omegaPullbackCoeff_mulByInt` uses `sorryAx` via
the Wronskian derivation). -/
theorem omegaPullbackCoeff_mulByInt_neg_one :
    omegaPullbackCoeff W (mulByInt W.toAffine (-1)) = -1 := by
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec]
  have h_pb_x : (mulByInt W.toAffine (-1)).pullback (algebraMap W.toAffine.CoordinateRing
      W.toAffine.FunctionField (algebraMap (Polynomial K) W.toAffine.CoordinateRing
        Polynomial.X)) = x_gen W := mulByInt_pullback_x_neg_one W
  rw [h_pb_x, alpha_star_u_mulByInt_neg_one, inv_neg, neg_smul, neg_one_smul]
  rfl

/-- **omegaPullbackCoeff for `negFrobeniusIsog` = 0 (axiom-clean)**:
`negFrobeniusIsog = mulByInt(-1) ∘ frobeniusIsog`, so by the chain rule
`omegaPullbackCoeff_comp_of_base` (with the outer-base coefficient -1 ∈ K),
`omega-coeff(negFrob) = (-1) * omega-coeff(frobenius) = (-1) * 0 = 0`.

Avoids the Wronskian-tainted `omegaPullbackCoeff_mulByInt`; uses the
direct `omegaPullbackCoeff_mulByInt_neg_one` (Commit 35) instead. -/
theorem omegaPullbackCoeff_negFrobeniusIsog :
    omegaPullbackCoeff W (negFrobeniusIsog W) = 0 := by
  unfold negFrobeniusIsog
  rw [omegaPullbackCoeff_comp_of_base W (mulByInt W.toAffine (-1)) (frobeniusIsog W) (-1)]
  · rw [omegaPullbackCoeff_frobenius, mul_zero]
  · rw [omegaPullbackCoeff_mulByInt_neg_one]
    push_cast
    rfl

/-- **Witness #1 (witness-parametric on additivity ONLY, axiom-clean)**:
separability of `isogOneSub_negFrobenius W hq`, taking only the additivity
sum hypothesis. T-II-4-004 iff (Commit 31) + Witness #2 (Commit 30) absorbed.

When the additivity discharge lands (per-α BRIDGE-001 instances +
`omegaPullbackCoeff_add_of_leading_witness`, `FormalIsogenySeries.lean`),
this fires the unconditional Witness #1 of the bound. -/
theorem isogOneSub_negFrobenius_isSeparable_of_h_add_only
    (hq : 2 ≤ Fintype.card K)
    (h_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      ((1 : ℤ) : KE) * omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        ((-1 : ℤ) : KE) * omegaPullbackCoeff W (frobeniusIsog W)) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_additivity_and_T2_4_004 W hq h_add
    (isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero W hq)

/-- **Witness #1 (taking ONLY `omegaPullbackCoeff = 1`, axiom-clean)**:
shorter consumer of the existing chain — takes only the omega-coefficient
identity (= 1), since T-II-4-004 iff (Commit 31) is now unconditional.

When the omega-coefficient computation lands axiom-clean (via either direct
algebraic computation or BRIDGE-001 + III.5.2), this fires the unconditional
Witness #1 of the bound. -/
theorem isogOneSub_negFrobenius_isSeparable_of_h_coeff_only
    (hq : 2 ≤ Fintype.card K)
    (h_coeff : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_witnesses W hq h_coeff
    (isogOneSub_negFrobenius_isSeparable_iff_omegaPullbackCoeff_ne_zero W hq)

/-- **Witness #3 (FiniteDim absorbed)**: sepDegree = pointCount for
`isogOneSub_negFrobenius W hq`, taking only IsSeparable, the fiber witness,
and Finite kernel — Witness #2 is absorbed via Commit 30 (unconditional). -/
theorem isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_sep_and_fiber
    [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (isogOneSub_negFrobenius W hq).toAddMonoidHom P =
            (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀} =
        (isogOneSub_negFrobenius W hq).sepDegree)
    [Finite (isogOneSub_negFrobenius W hq).kernel] :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine :=
  isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses W hq h_pc_sep
    (isogOneSub_negFrobenius_finiteDimensional W hq)
    h_pc_fiber_witness

/-- **Fiber witness from sepDegree-pointCount identity**: for `γ = isogOneSub_negFrobenius`,
the fiber witness `∃ P₀, Nat.card fiber-over-P₀ = sepDegree` follows directly
from `sepDegree = pointCount` via the kernel-identity (kernel = ⊤). -/
theorem isogOneSub_negFrobenius_fiber_witness_of_sepDegree_eq_pointCount
    [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_sepDeg : (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine) :
    ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (isogOneSub_negFrobenius W hq).toAddMonoidHom P =
            (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀} =
        (isogOneSub_negFrobenius W hq).sepDegree :=
  hole_d_of_hom_and_sepDegree W (isogOneSub_negFrobenius W hq)
    (by rfl : (isogOneSub_negFrobenius W hq).toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    h_sepDeg

/-- **Witness #1 via leading-coefficient bridge witness (axiom-clean)**:
takes BRIDGE-001 for the three isogenies + leading-coefficient additivity
of formal series, then chains via Commit 46 to derive omega-coeff(γ) = 1
unconditional, which closes Witness #1 via Commit 38.

When the leading-coefficient additivity (`h_leading_add`) and BRIDGE-001 for
negFrobeniusIsog and isogOneSub_negFrobenius are discharged, this becomes
the unconditional Witness #1 of the bound. -/
theorem isogOneSub_negFrobenius_isSeparable_via_leading_witnesses
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_negFrob : omegaPullbackCoeff W (negFrobeniusIsog W) =
      algebraMap K W.toAffine.FunctionField
        (PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))))
    (h_bridge_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField
        (PowerSeries.coeff 1
          (formalIsogenySeries W (isogOneSub_negFrobenius W hq))))
    (h_leading_add :
      PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
        PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))) :
    (isogOneSub_negFrobenius W hq).IsSeparable := by
  have h_omega_add : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      omegaPullbackCoeff W (Isogeny.id W.toAffine) +
        omegaPullbackCoeff W (negFrobeniusIsog W) :=
    omegaPullbackCoeff_add_of_leading_witness W
      (Isogeny.id W.toAffine) (negFrobeniusIsog W) (isogOneSub_negFrobenius W hq)
      (omegaPullbackCoeff_eq_formalIsogenyLeading_id W) h_bridge_negFrob h_bridge_γ
      h_leading_add
  rw [omegaPullbackCoeff_id W, omegaPullbackCoeff_negFrobeniusIsog W,
    add_zero] at h_omega_add
  exact isogOneSub_negFrobenius_isSeparable_of_h_coeff_only W hq h_omega_add

end HasseWeil
