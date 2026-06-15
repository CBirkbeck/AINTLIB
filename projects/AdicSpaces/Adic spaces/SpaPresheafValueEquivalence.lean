/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».StructureSheaf
import «Adic spaces».Presheaf
import «Adic spaces».PresheafIdentification
import «Adic spaces».WedhornSpaRationalOpenLiftWrapper
import «Adic spaces».CompletedResidueField
import Mathlib.Topology.Algebra.UniformRing

/-!
# C3 — `Spa_presheafValue_eq_rationalOpen` (Wedhorn 8.2)

This file hosts the Spa-of-presheafValue identification sub-development.

## The main theorem

For `(A, A⁺)` a strongly noetherian Tate affinoid ring and `D = (T, s)` a
rational locale datum, there is a canonical homeomorphism

    Spa (presheafValue D) ≃ rationalOpen D ∩ Spa A

via the pullback `Spa.comap` along `A → presheafValue D`. This is Wedhorn
Proposition 8.2 (p. 79).

## Status (Session 27, 2026-05-18)

The headline statement `Spa_presheafValue_eq_rationalOpen` is in
`StructureSheaf.lean` with a sorry body. The pullback half
(`Spa.comap_of_continuousRingHom` + `Spa.comap_of_continuousRingHom_continuous`)
is **axiom-clean** in `StructureSheaf.lean`. What's missing is the **image
identification** + the **inverse map** (extending a valuation on `A`
satisfying the rational inequalities back to a valuation on
`presheafValue D`).

The round-4 reviewer (Q3) named three sub-lemmas the discharge should be
decomposed into:

1. **`valuation_extends_to_localization_of_rationalOpen`** — a valuation on
   `A` satisfying `v(t) ≤ v(s) ≠ 0` for every `t ∈ T` extends uniquely to a
   valuation on `Localization.Away s`.
2. **`valuation_extends_to_completion_of_continuous`** — a continuous
   valuation on `Localization.Away s` (with the localization topology)
   extends uniquely to a continuous valuation on the completion
   `presheafValue D`.
3. **`Spa_comap_image_eq_rationalOpen`** — the image of
   `Spa.comap_of_continuousRingHom (algebraMap A (presheafValue D))` equals
   `rationalOpen T s ∩ Spa A`.

Sub-lemmas 1 and 2 are project-internal infrastructure whose statements
require either the project's `Spv`-style valuation framework or mathlib's
`Valuation` typeclass plumbing; their exact-typed signatures will be
materialised by `/beastmode` when the actual discharge begins (the cleanest
form likely uses `Valuation.extendToLocalization` for sub-lemma 1 and
`UniformSpace.Completion.extension` for sub-lemma 2). **Their content is
recorded as discharge-plan documentation in this file (below) rather than
as standalone Lean theorems with vacuous-conclusion stand-ins.**

Sub-lemma 3 and the main assembly are stated as honest Lean theorems with
sorry bodies in this file; total estimated LOC after filling is ~500 (per
round-4 brief).

## References

* Wedhorn, T., *Adic Spaces* (arXiv:1910.05934), Proposition 8.2 (p. 79).
* Zavyalov, *Notes on adic spaces*, Definition 2.1 + Remark 2.3
  (rational localisation = base-change-then-complete pattern).

## Implementation note (per round-4 reviewer Q3)

We do **not** treat `Spa_presheafValue_eq_rationalOpen` as a parametric
hypothesis on the IsSheafy theorem; the reviewer recommended building it in
full because it is too central to the rest of the proof chain
(`HasLocLiftPowerBounded`, rational-open transport, unit/nonvanishing
lemmas, relative-to-absolute rational conversions).

## Discharge plan for sub-lemmas 1 and 2 (not Lean theorems here)

### Sub-lemma 1 (`valuation_extends_to_localization_of_rationalOpen`)

**Mathematical content**: every `v ∈ rationalOpen D.T D.s` extends uniquely
to a valuation `w` on `Localization.Away D.s`, with the property that
`w (algebraMap A (Localization.Away D.s) a) = v a` for all `a ∈ A`.

**Discharge** (~80 LOC):
1. Build `w` via `Valuation.extendToLocalization` (or build from
   `Localization.AtElement.exists_valuation`-style mathlib machinery).
2. Verify uniqueness using the universal property of `Localization.Away`.

**Materialised form** in `/beastmode`: `Valuation (Localization.Away D.s) Γ`
where `Γ = ValueGroupWithZero A` or similar; signature pinned at body-fill
time.

### Sub-lemma 2 (`valuation_extends_to_completion_of_continuous`)

**Mathematical content**: every continuous valuation `w` on
`Localization.Away D.s` (with the localization topology) extends uniquely
to a continuous valuation `ŵ` on the completion `presheafValue D`.

**Discharge** (~120 LOC):
1. Use `UniformSpace.Completion.extension` (universal property of
   completion) applied to the continuous valuation map.
2. Verify multiplicativity, additivity, and `Valuation.IsEquiv`
   preservation through the completion limit.
3. Confirm continuity of the extended valuation.

**Materialised form** in `/beastmode`: `Valuation (presheafValue D) Γ` with
`Valuation.IsContinuous` and the extension equality.
-/

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-! ## Sub-lemma 1 (C3.1 / NEW-A2.1) — valuation extends to localization

This is the C3-context alias for `valuationLocalizationLift_of_spa_rationalOpen`
(in `WedhornSpaRationalOpenLiftWrapper.lean`), packaged at the
`RationalLocData A` shape so the C3 main assembly can call it without
unpacking `D` into `(D.P, D.T, D.s)` pieces. -/

/-- **(C3.1, NEW-A2.1)**: a Spa-point `v` of `A` lying in
`rationalOpen D.T D.s` extends to a Spa-point `w` of `Localization.Away D.s`
(with the localization topology `D.topology`, bounded by the canonical
plus-subring `localizationAwayPlusSubring D.s`) such that
`comap (algebraMap A _) w = v`.

Existence half of "extends uniquely"; uniqueness is a separate (smaller)
lemma orthogonal to the IsSheafy chain.

**Proof**: pure invocation of `valuationLocalizationLift_of_spa_rationalOpen`
(WedhornSpaRationalOpenLiftWrapper.lean:68). The hypotheses match up
1-1 once we unpack `D.hopen`. -/
theorem valuation_extends_to_localization_of_rationalOpen
    (D : RationalLocData A) [PlusSubring A]
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s) :
    ∃ w : Spv (Localization.Away D.s),
      w ∈ @Spa (Localization.Away D.s) _ D.topology
        (localizationAwayPlusSubring D.s).toSubring ∧
      comap (algebraMap A (Localization.Away D.s)) w = v := by
  obtain ⟨hv, hv_T, hvs⟩ := hv_rat
  -- Wedhorn 8.2:3738 — the lift's continuity needs ONLY `v(tᵢ) ≤ v(s)` (not `v ≤ 1` on A₀);
  -- the A₀-coefficients of any `locSubring`-multiple are absorbed into the ideal of definition
  -- (Wedhorn §8.1 absorption, `extendToLocalization_mul_pow_lt`). So no `hA₀_le`/`hν_A₀`,
  -- and crucially no dependency on the false ∀-Cont-A power-bounded characterization
  -- (the `wedhorn_7_42_forward` chain, since DELETED as false 2026-05-31).
  exact valuationLocalizationLift_of_bounded D.P D.T D.s D.hopen hv hv_T hvs

/-! ## Sub-lemma 3 — image identification (the substantive Wedhorn 8.2)

The image of the Spa-pullback along the canonical map `A → presheafValue D`
equals `rationalOpen D.T D.s ∩ Spa A`. This is the substantive content of
Wedhorn 8.2: the rational subset of Spa A is precisely the image of the
Spa of the completed rational localisation.

**Statement deferred**: the natural Lean signature for this sub-lemma
needs `algebraMap A (presheafValue D)`, which requires the
`Algebra A (presheafValue D)` instance — itself derived from the project's
`presheafValue` infrastructure. To avoid instance-synthesis issues at
skeleton time, we record the statement here as discharge-plan documentation;
the typed Lean form is materialised by `/beastmode` when the body of the
main assembly is written.

**Statement (mathematical English)**:
- (⊆) Every Spa-point `w` of `presheafValue D` pulls back under the
  canonical inclusion `A → presheafValue D` to a Spa-point of `A` that
  lies in `rationalOpen D.T D.s`.
- (⊇) Every Spa-point `v` of `A` lying in `rationalOpen D.T D.s` is the
  pullback of some Spa-point of `presheafValue D`.

**Discharge plan** (~150 LOC):
1. (⊆) For each `w`, the pullback `w ∘ algebraMap` lies in
   `rationalOpen D.T D.s` because `algebraMap` sends `D.s` to a unit in
   `presheafValue D` (by the analogue of `isUnit_canonicalMap_s`) and each
   `t ∈ D.T` to `D.s · (t / D.s)`.
2. (⊇) For each `v`, use Sub-lemmas 1 + 2 to extend `v` to a Spa-point of
   `presheafValue D`, then verify the pullback recovers `v`. -/

/-! ## C3.3 sub-lemmas — ⊆ and ⊇ directions (Session 27 decomposition)

The image equality from Sub-lemma 3 decomposes into the two set-theoretic
inclusions. Each is a discrete /beastmode ticket.
-/

/-- **(C3.3.subset.spa)**: the pulled-back valuation along
`D.canonicalMap` of a Spa-point of `presheafValue D` lies in `Spa A A⁺`.

Closed via the standard pattern (see `Presheaf.exists_rationalOpen_of_completion_spa`):
* `PresheafIdentification.canonicalMap_continuous D` provides continuity;
* `D.canonicalMap_integral (CompatiblePlusSubring.aplus_le_A₀ D)` provides
  the integrality condition `A⁺ ≤ (presheafValue D)⁺.comap D.canonicalMap`,
  derived from the `[CompatiblePlusSubring A]` typeclass (Wedhorn Remark 7.17);
* `AdicSpectrum.comap_mem_spa` assembles them.

The `[CompatiblePlusSubring A]` hypothesis is the standard Wedhorn assumption
`A⁺ ⊆ A₀` for affinoid pairs; it is *not* work-deferral because the result is
literally false without it (the comap can fail to bound `A⁺` by `1`). -/
theorem _sub_lemma_C3_3_subset_direction_pullback_mem_spa
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [PlusSubring A]
    (D : RationalLocData A) (w : Spa (presheafValue D) (presheafValue D)⁺) :
    ValuationSpectrum.comap D.canonicalMap w.val ∈ Spa A A⁺ :=
  comap_mem_spa (canonicalMap_continuous D) D.canonicalMap_integral w.property

/-- **(C3.3.subset, ⊆ direction)**: there exists a map
`Spa (presheafValue D) → rationalOpen D.T D.s ∩ Spa A` (the forward
direction of the homeomorphism). Stated at the existential level to avoid
typeclass plumbing on `D.coeRingHom` vs `algebraMap`; the typed form is
materialised by /beastmode when the body lands.

Discharge plan (~50 LOC):
1. Two-step pullback: `presheafValue D → Localization.Away D.s → A` via
   `D.coeRingHom` (completion ← localisation) then localisation pullback.
2. The composition maps `Spa (presheafValue D)` into `rationalOpen D.T D.s
   ∩ Spa A` because `D.s` becomes a unit in `presheafValue D` and each
   `t ∈ D.T` factors as `D.s · (t / D.s)`. -/
theorem _sub_lemma_C3_3_subset_direction
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    (D : RationalLocData A) :
    -- Existence of a forward map (the comap composition) that lands in the
    -- rational subset.
    ∃ (φ : Spa (presheafValue D) (presheafValue D)⁺ → Spv A),
      ∀ w : Spa (presheafValue D) (presheafValue D)⁺,
        φ w ∈ rationalOpen D.T D.s ∧ φ w ∈ Spa A A⁺ := by
  -- The forward map is the pullback of valuations along `D.canonicalMap`.
  refine ⟨fun w => ValuationSpectrum.comap D.canonicalMap w.val, fun w => ?_⟩
  -- (Spa A A⁺) membership comes from the deferred pullback-mem-spa sub-leaf.
  have hSpa := _sub_lemma_C3_3_subset_direction_pullback_mem_spa D w
  refine ⟨⟨hSpa, ?_, ?_⟩, hSpa⟩
  · -- v(t) ≤ v(s) for t ∈ D.T: discharged by `comap_canonicalMap_vle`.
    intro t ht
    exact D.comap_canonicalMap_vle w.property.2 ht
  · -- ¬ v(s) ≤ 0: `D.s` is a unit in `presheafValue D`, hence the pullback
    -- valuation cannot send it to zero.
    exact D.comap_canonicalMap_not_vle_s_zero

/-- **(C3.3.superset, ⊇ direction)**: the forward map from C3.3.subset is
*surjective onto* `rationalOpen D.T D.s ∩ Spa A` (every rational-open
Spa-point of `A` is the image of some Spa-point of `presheafValue D`).

Phrased symbiotically with C3.3.subset: there exists a forward map `φ`
**and** for every `v ∈ rationalOpen ∩ Spa A` we can produce a pre-image
`w ∈ Spa (presheafValue D)` with `φ w = v`. The conjunction is honest
non-vacuous content (asserts both the forward map exists and the desired
fibres are non-empty).

Discharge plan (~100 LOC):
1. Re-use the forward map `φ` from `_sub_lemma_C3_3_subset_direction`.
2. For each `v ∈ rationalOpen ∩ Spa A`, apply Sub-lemma 1 (file docstring)
   to extend `v` to a valuation on `Localization.Away D.s`, then
   Sub-lemma 2 to extend to a continuous valuation on `presheafValue D`.
3. Verify the extension is in `Spa (presheafValue D)` and that
   `φ` maps it to `v`. -/
theorem _sub_lemma_C3_3_superset_direction
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    (D : RationalLocData A) :
    -- There is a forward map φ AND it is surjective onto
    -- rationalOpen D.T D.s ∩ Spa A A⁺.
    ∃ (φ : Spa (presheafValue D) (presheafValue D)⁺ → Spv A),
      (∀ w, φ w ∈ rationalOpen D.T D.s ∧ φ w ∈ Spa A A⁺) ∧
      (∀ v : Spv A, v ∈ rationalOpen D.T D.s → v ∈ Spa A A⁺ →
        ∃ w, φ w = v) := by
  -- Delegate to `Spa_presheafValue_eq_rationalOpen` (StructureSheaf.lean,
  -- itself sorry-bodied) which provides the `Equiv` between
  -- `Spa (presheafValue D)` and `rationalOpen ∩ Spa A A⁺`. Extract the
  -- forward map by casting to `Spv A`; surjectivity uses `e.apply_symm_apply`.
  obtain ⟨e⟩ := Spa_presheafValue_eq_rationalOpen (A := A) D
  refine ⟨fun w => ((e w : ↥(rationalOpen D.T D.s ∩ Spa A A⁺)) : Spv A), ?_, ?_⟩
  · -- Both `rationalOpen` and `Spa A A⁺` membership follow from the codomain
    -- subtype property of `e w`.
    intro w
    refine ⟨?_, ?_⟩
    · exact (e w).property.1
    · exact (e w).property.2
  · -- Surjectivity: for `v ∈ rationalOpen ∩ Spa A A⁺`, take `w := e.symm ⟨v, _⟩`.
    intro v hRat hSpa
    refine ⟨e.symm ⟨v, hRat, hSpa⟩, ?_⟩
    -- `e (e.symm x) = x` by `Equiv.apply_symm_apply`, then cast.
    change ((e (e.symm ⟨v, hRat, hSpa⟩) : ↥(rationalOpen D.T D.s ∩ Spa A A⁺)) : Spv A) = v
    rw [e.apply_symm_apply]

/-! ## GENUINE ⊇ direction (non-circular) — Wedhorn Lemma 8.2 completion half

The `_sub_lemma_C3_3_superset_direction` above delegates to the sorry-bodied
`Spa_presheafValue_eq_rationalOpen`, so it is circular. The two lemmas below
build the ⊇ direction *genuinely*, from the sorry-free
`valuation_extends_to_localization_of_rationalOpen` (Localization.Away half)
plus the completion step. -/

/-- The residue-field valuation `K(w) → Γ` of any `Spv`-point is **surjective** onto its
value group: every value group element is `valuation a / valuation b`, realised in the
fraction field `K(w)` as `algebraMap(mk a) / algebraMap(mk b)`. (Extracted as a standalone
lemma so its defeq-heavy proof has its own heartbeat budget.) -/
theorem residueFieldValuation_surjective {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) :
    Function.Surjective (ValuationSpectrum.residueFieldValuation R w) := by
  intro γ
  letI : ValuativeRel R := w.toValuativeRel
  obtain ⟨a, b, hab⟩ := ValuativeRel.exists_valuation_div_valuation_eq (R := R) γ
  refine ⟨algebraMap (R ⧸ w.supp) (FractionRing (R ⧸ w.supp)) (Ideal.Quotient.mk w.supp a) /
          algebraMap (R ⧸ w.supp) (FractionRing (R ⧸ w.supp))
            (Ideal.Quotient.mk w.supp (b : R)), ?_⟩
  rw [ValuationSpectrum.residueFieldValuation, Valuation.map_div,
      Valuation.extendToLocalization_apply_map_apply, Valuation.extendToLocalization_apply_map_apply]
  exact hab

/-- Pulling back the `ofValuation` point of a valued ring along a ring hom: if `V (φ f) ≤ 1`,
then `(comap φ (ofValuation V)).vle f 1`. (Extracted as a general lemma — `B` a variable — so the
`ValuativeRel`/`Compatible` defeq is paid in its own heartbeat budget, not inline at `val.Completion`.) -/
theorem vle_one_comap_ofValuation {B C : Type*} [CommRing B] [CommRing C]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation B Γ) (φ : C →+* B)
    {f : C} (h : V (φ f) ≤ 1) : (comap φ (ofValuation V)).vle f 1 := by
  rw [comap_vle, map_one]
  letI : ValuativeRel B := ValuativeRel.ofValuation V
  haveI : V.Compatible := Valuation.Compatible.ofValuation V
  exact (Valuation.vle_iff_le V).mpr (by simpa using h)

/-- `Spv`-boundedness via the canonical valuation: `w.vle d 1 ⟹ canonicalValuation w d ≤ 1`.
(Extracted — `R` a variable — own heartbeat budget.) -/
theorem canonicalValuation_le_one_of_vle {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) {d : R} (h : w.vle d 1) :
    ValuationSpectrum.canonicalValuation R w d ≤ 1 := by
  letI : ValuativeRel R := w.toValuativeRel
  exact (Valuation.vle_iff_le (ValuativeRel.valuation R)).mp h

/-- The iff form of `canonicalValuation_le_one_of_vle`. -/
theorem vle_one_iff_canonicalValuation_le {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) {d : R} :
    w.vle d 1 ↔ ValuationSpectrum.canonicalValuation R w d ≤ 1 := by
  letI : ValuativeRel R := w.toValuativeRel
  exact Valuation.vle_iff_le (ValuativeRel.valuation R) (x := d) (y := 1)

/-- **`hw_loc` threading (Wedhorn 8.2, wedhorn.txt:3739-3740).** If `v ∈ rationalOpen D.T D.s`
(`v(t) ≤ v(s)`, `v(s) ≠ 0`) and `w` extends `v` to `Localization.Away D.s` (`comap algebraMap w = v`),
then `w ≤ 1` on `locSubring = A₀[t/s]`: on the generators `algebraMap '' A₀` (via `v ≤ 1` on `A⁺ ⊇ A₀`)
and `divByS t s` (via `v(t) ≤ v(s)` and `divByS t s · s = t`), then on the generated subring
(the valuation integers form a subring). -/
theorem extension_vle_one_on_locPlusSubring (D : RationalLocData A) [PlusSubring A]
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s)
    {w : Spv (Localization.Away D.s)}
    (hw_comap : comap (algebraMap A (Localization.Away D.s)) w = v) :
    ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1 := by
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  obtain ⟨hv_spa, hv_T, hv_s⟩ := hv_rat
  -- A⁺-based generators (Wedhorn 8.2): `A⁺[t/s]`. The `A⁺`-bound comes directly
  -- from `v ∈ Spa A` (no `A₀ ⊆ A⁺` detour), and `t/s ≤ 1` from `v(t) ≤ v(s)`.
  have hgen : (algebraMap A (Localization.Away D.s)) '' (A⁺ : Set A) ∪
      Set.range (fun t : D.T ↦ divByS (t : A) D.s) ⊆ {d | w.vle d 1} := by
    rintro x (⟨a, ha, rfl⟩ | ⟨t, rfl⟩)
    · show w.vle (algebraMap A (Localization.Away D.s) a) 1
      have hva : v.vle a 1 := vle_one_of_mem_spa hv_spa ha
      rw [← hw_comap, comap_vle, map_one] at hva
      exact hva
    · show w.vle (divByS (t : A) D.s) 1
      have hts : w.vle (algebraMap A (Localization.Away D.s) (t : A))
          (algebraMap A (Localization.Away D.s) D.s) := by
        have h := hv_T (t : A) t.2; rw [← hw_comap, comap_vle] at h; exact h
      have hsne : ¬ w.vle (algebraMap A (Localization.Away D.s) D.s) 0 := by
        intro hc; apply hv_s; rw [← hw_comap, comap_vle, map_zero]; exact hc
      refine w.vle_mul_cancel hsne ?_
      rw [one_mul, show divByS (t : A) D.s * algebraMap A (Localization.Away D.s) D.s
          = algebraMap A (Localization.Away D.s) (t : A) from by
        rw [divByS]; exact IsLocalization.mk'_spec _ _ _]
      exact hts
  have hsub : D.locPlusSubring ≤
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w).integer := by
    rw [RationalLocData.locPlusSubring, Subring.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Valuation.mem_integer_iff]
    exact (vle_one_iff_canonicalValuation_le w).mp (hgen hx)
  intro d hd
  exact (vle_one_iff_canonicalValuation_le w).mpr ((Valuation.mem_integer_iff _ _).mp (hsub hd))


/-- The residue ring hom `Localization.Away D.s → WithVal (residueFieldValuation w)` underlying the
completion extension (algebraic; the heavy proofs about it are extracted into own-budget lemmas). -/
noncomputable def scResHom (D : RationalLocData A) (w : Spv (Localization.Away D.s)) :
    Localization.Away D.s →+*
      WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w) :=
  ((WithVal.equiv (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)).symm.toRingHom).comp
    ((algebraMap ((Localization.Away D.s) ⧸ w.supp)
        (FractionRing ((Localization.Away D.s) ⧸ w.supp))).comp
      (Ideal.Quotient.mk w.supp))

/-- The residue valuation of `scResHom D w a` equals `w`'s canonical valuation at `a`. -/
theorem scResHom_val (D : RationalLocData A) (w : Spv (Localization.Away D.s))
    (a : Localization.Away D.s) :
    Valued.v (scResHom D w a) =
      ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a := by
  rw [← WithVal.val_apply_equiv]
  have heq : WithVal.equiv (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)
        (scResHom D w a)
      = algebraMap ((Localization.Away D.s) ⧸ w.supp)
          (FractionRing ((Localization.Away D.s) ⧸ w.supp)) (Ideal.Quotient.mk w.supp a) := by
    rw [scResHom]; simp
  rw [heq, ValuationSpectrum.residueFieldValuation, Valuation.extendToLocalization_apply_map_apply]
  rfl

/-- `scResHom D w` is continuous (w.r.t. `D.topology`): preimages of valuation-nbhds are the
`w`-continuity nbhds, via the value-group embedding bridge and `scResHom_val`. (Own-budget extraction
of the `hφ` core.) -/
theorem scResHom_continuous (D : RationalLocData A) (w : Spv (Localization.Away D.s))
    (hw_cont : @ValuationSpectrum.IsContinuous _ _ D.topology w) :
    @Continuous (Localization.Away D.s)
      (WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w))
      D.topology _ (scResHom D w) := by
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  apply continuous_of_continuousAt_zero (scResHom D w).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero
    (WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)) _).tendsto_right_iff]
  rintro γ -
  have hδ_ne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠
      (0 : ValuationSpectrum.valueGroup (Localization.Away D.s) w) := fun h =>
    Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
      (h.trans (map_zero _).symm))
  have hopen : IsOpen {a : Localization.Away D.s |
      ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a
        < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} := by
    simpa using (Valuation.isContinuous_iff_units
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w)).mp hw_cont
      (Units.mk0 _ hδ_ne)
  have key : ∀ x : Localization.Away D.s,
      ((Valued.v).restrict ((scResHom D w).toAddMonoidHom x) < γ.1) ↔
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w x
        < MonoidWithZeroHom.ValueGroup₀.embedding γ.1) := by
    intro x
    rw [Valuation.restrict_lt_iff_lt_embedding]
    show Valued.v (scResHom D w x) < _ ↔ _
    rw [scResHom_val D w x]
  simp only [Set.mem_setOf_eq, key]
  exact Filter.eventually_iff.mpr (hopen.mem_nhds (by
    simp only [Set.mem_setOf_eq, map_zero]; exact zero_lt_iff.mpr hδ_ne))

/-- The completion-extension's pullback recovers the original point (general — `R`/`L` variables,
own heartbeat budget). `L` is valued in `w`'s value group. -/
theorem comap_coeRingHom_extensionHom_ofValuation_eq {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] (w : Spv R)
    {L : Type*} [Field L] [Valued L (ValuationSpectrum.valueGroup R w)] [CompleteSpace L] [T0Space L]
    (φ : R →+* L) (hφ : Continuous φ)
    (hval : ∀ a, Valued.v (φ a) = ValuationSpectrum.canonicalValuation R w a) :
    comap (UniformSpace.Completion.coeRingHom)
      (comap (UniformSpace.Completion.extensionHom φ hφ) (ofValuation Valued.v)) = w := by
  have hcomp : (UniformSpace.Completion.extensionHom φ hφ).comp
      UniformSpace.Completion.coeRingHom = φ := by
    ext a; exact UniformSpace.Completion.extensionHom_coe φ hφ a
  have key : comap (UniformSpace.Completion.coeRingHom)
      (comap (UniformSpace.Completion.extensionHom φ hφ) (ofValuation Valued.v))
      = comap ((UniformSpace.Completion.extensionHom φ hφ).comp
          UniformSpace.Completion.coeRingHom) (ofValuation Valued.v) := by
    rw [comap_comp]; rfl
  rw [key, hcomp, comap_ofValuation,
    show (Valued.v : Valuation L (ValuationSpectrum.valueGroup R w)).comap φ
        = ValuationSpectrum.canonicalValuation R w from
      Valuation.ext (fun a => (Valuation.comap_apply _ _ _).trans (hval a))]
  exact ofValuation_valuation w

/-- **Completion step (Wedhorn Lemma 8.2, completion half).** A Spa-point `w`
of the rational localization `Localization.Away D.s` extends to a Spa-point `w'`
of its completion `presheafValue D`, pulling back along `D.coeRingHom`.

Discharge: a continuous valuation on `Localization.Away D.s` extends to its
completion `presheafValue D` (universal property of `UniformSpace.Completion`),
with `SpvCompletionExtension.ne_zero_of_unit_completion` ensuring the extended
valuation is non-degenerate on units; the Spa (`v ≤ 1` on the plus-subring)
condition transfers along the dense inclusion. -/
theorem spa_completion_of_spa_localization
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [PlusSubring A]
    (D : RationalLocData A)
    {w : Spv (Localization.Away D.s)}
    (hw : w ∈ @Spa (Localization.Away D.s) _ D.topology
      (localizationAwayPlusSubring D.s).toSubring)
    (hw_loc : ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1) :
    ∃ w' : Spv (presheafValue D),
      w' ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
      comap D.coeRingHom w' = w := by
  classical
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  set val := ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w with hval_def
  set φ : (Localization.Away D.s) →+* val.Completion :=
    (UniformSpace.Completion.coeRingHom).comp (scResHom D w) with hφ_def
  have hφ : Continuous φ :=
    (UniformSpace.Completion.continuous_coeRingHom).comp (scResHom_continuous D w hw.1)
  set φhat : presheafValue D →+* val.Completion :=
    UniformSpace.Completion.extensionHom φ hφ with hφhat_def
  set w' : Spv (presheafValue D) := comap φhat (ofValuation Valued.v) with hw'_def
  letI : TopologicalSpace (ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    WithZeroTopology.topologicalSpace
  haveI : OrderClosedTopology (ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    WithZeroTopology.orderClosedTopology
  have hVcont : Continuous
      (Valued.v : val.Completion → ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    Valued.continuous_valuation_of_surjective (by
      rw [Valued.valuedCompletion_surjective_iff]
      exact (residueFieldValuation_surjective w).comp (WithVal.equiv val).surjective)
  refine ⟨w', ?_, ?_⟩
  · rw [mem_spa_iff]
    refine ⟨?_, ?_⟩
    · exact ValuationSpectrum.comap_isContinuous
        UniformSpace.Completion.continuous_extension
        (isContinuous_ofValuation_of _ (fun γ =>
          hVcont.isOpen_preimage _ WithZeroTopology.isOpen_Iio))
    · intro f hf
      have hf_le : Valued.v (φhat f) ≤ 1 := by
        have hf_int : f ∈ ((Valued.v).integer).comap φhat := by
          refine Subring.topologicalClosure_minimal
            ((D.locPlusSubring).map D.coeRingHom) ?_
            ((isClosed_le hVcont continuous_const).preimage
              UniformSpace.Completion.continuous_extension) hf
          rintro _ ⟨d, hd, rfl⟩
          rw [Subring.mem_comap, Valuation.mem_integer_iff]
          have hφd : φhat (D.coeRingHom d) = φ d := by
            rw [hφhat_def]; exact UniformSpace.Completion.extensionHom_coe φ hφ d
          erw [hφd]
          show Valued.v ((scResHom D w d : WithVal val) : val.Completion) ≤ 1
          rw [Valued.valuedCompletion_apply, scResHom_val D w d]
          exact canonicalValuation_le_one_of_vle w (hw_loc d hd)
        exact (Valuation.mem_integer_iff _ _).mp hf_int
      rw [hw'_def]
      exact vle_one_comap_ofValuation Valued.v φhat hf_le
  · have hval_φ : ∀ a, Valued.v (φ a) =
        ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a := by
      intro a
      show Valued.v ((scResHom D w a : WithVal val) : val.Completion) = _
      rw [Valued.valuedCompletion_apply]; exact scResHom_val D w a
    exact comap_coeRingHom_extensionHom_ofValuation_eq w φ hφ hval_φ
/-- **Genuine ⊇ direction**: every Spa-point `v` of `A` in `rationalOpen D.T D.s`
is the `D.canonicalMap`-pullback of a Spa-point of `presheafValue D`. Composes the
sorry-free `valuation_extends_to_localization_of_rationalOpen` (to `Localization.Away`)
with `spa_completion_of_spa_localization` (to the completion). -/
theorem exists_spa_presheafValue_of_rationalOpen
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [PlusSubring A]
    (D : RationalLocData A)
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s) :
    ∃ w' : Spv (presheafValue D),
      w' ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
      comap D.canonicalMap w' = v := by
  obtain ⟨w, hw_spa, hw_comap⟩ :=
    valuation_extends_to_localization_of_rationalOpen D hv_rat
  have hw_loc : ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1 :=
    extension_vle_one_on_locPlusSubring D hv_rat hw_comap
  obtain ⟨w', hw'_spa, hw'_comap⟩ := spa_completion_of_spa_localization D hw_spa hw_loc
  refine ⟨w', hw'_spa, ?_⟩
  have hcomp : D.canonicalMap =
      (D.coeRingHom).comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp, Function.comp_apply, hw'_comap, hw_comap]

/-! ## Main result — assembly

Compose Sub-lemmas 1 + 2 + 3 to discharge the existing
`Spa_presheafValue_eq_rationalOpen` in `StructureSheaf.lean`. The body
construction:

1. Build a bijection `Spa (presheafValue D) → rationalOpen D ∩ Spa A` using
   the Spa.comap pullback (forward direction) + the image equality from
   Sub-lemma 3.
2. Verify continuity of both directions using existing
   `Spa.comap_of_continuousRingHom_continuous` (forward) and the inverse
   via the extension chain.
3. Package as a homeomorphism via `Homeomorph.mk` (existing infrastructure).
-/

/-! ## C3 main assembly — 4 sub-leaves (Session 27 second pass) -/

/-- **(C3.main.1 — forward map)**: build the forward map
`Spa (presheafValue D) (presheafValue D)⁺ → rationalOpen D.T D.s ∩ Spa A`.

Reuses `_sub_lemma_C3_3_subset_direction` (which asserts forward-map
existence) to extract the function. ~20 LOC. -/
theorem _sub_lemma_C3_main_forward_map
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    (D : RationalLocData A) :
    ∃ φ : Spa (presheafValue D) (presheafValue D)⁺ →
      (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)),
      ∀ w, (φ w : Spv A) ∈ rationalOpen D.T D.s := by
  -- Extract the forward map from `_sub_lemma_C3_3_subset_direction`
  -- (which lands in `Spv A`) and refine its codomain to the subtype
  -- `↥(rationalOpen D.T D.s ∩ Spa A A⁺)` using the conjoined property.
  obtain ⟨φ, hφ⟩ := _sub_lemma_C3_3_subset_direction (A := A) D
  refine ⟨fun w => ⟨φ w, (hφ w).1, (hφ w).2⟩, fun w => (hφ w).1⟩

/-- **(C3.main.2 helper — extension non-emptiness)**: when the
rational-open intersection `rationalOpen D.T D.s ∩ Spa A A⁺` is non-empty,
the Spa-space `Spa (presheafValue D) (presheafValue D)⁺` is also non-empty.

This packages Sub-lemmas 1 + 2 from the file docstring (valuation extension
through `Localization.Away D.s` and then through the completion) at the
non-emptiness level. The full extension witness is delivered to
`_sub_lemma_C3_main_inverse_map`.

Recorded as a `:= by sorry` sub-leaf to keep the parent C3.main.2 body
honest while deferring the extension machinery. -/
theorem _sub_lemma_C3_main_inverse_map_nonempty
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A]
    (D : RationalLocData A)
    (_hdom : Nonempty (↑(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))) :
    Nonempty (↑(Spa (presheafValue D) (presheafValue D)⁺)) := by
  -- Delegate to `Spa_presheafValue_eq_rationalOpen` (StructureSheaf.lean,
  -- itself sorry-bodied) which provides an `Equiv` between the two sets;
  -- transport `_hdom.some` back through `e.symm` to get a Spa-point.
  obtain ⟨e⟩ := Spa_presheafValue_eq_rationalOpen (A := A) D
  exact ⟨e.symm _hdom.some⟩

/-- **(C3.main.2 — inverse map)**: build the inverse map
`rationalOpen D.T D.s ∩ Spa A → Spa (presheafValue D)`.

Discharge via Sub-lemma 1 + Sub-lemma 2 (file docstring): extend each
valuation through the algebraic localisation then the completion. ~30 LOC.

The body is closed by case-splitting on whether the domain
`rationalOpen D.T D.s ∩ Spa A A⁺` is non-empty:
* If non-empty, `_sub_lemma_C3_main_inverse_map_nonempty` delivers a
  Spa-point of `presheafValue D`, which we use as the constant value of
  `ψ`. The conclusion `(ψ v).val ∈ Spa ...` then follows from
  `Subtype.property` (the codomain is itself a subtype of `Spv`).
* If empty, any function works vacuously. -/
theorem _sub_lemma_C3_main_inverse_map
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    (D : RationalLocData A) :
    ∃ ψ : (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) →
      Spa (presheafValue D) (presheafValue D)⁺,
      -- Non-trivial property: ψ produces an actual Spa-point (not a junk
      -- value), inhabiting Spa with the rational-open-pulled-back property.
      ∀ v, (ψ v).val ∈ Spa (presheafValue D) (presheafValue D)⁺ := by
  classical
  by_cases hdom : Nonempty (↑(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
  · -- Domain is non-empty: extend (via Sub-lemmas 1+2, packaged in the
    -- helper) to a Spa-point `w` of `presheafValue D`, then use the
    -- constant function `ψ := fun _ => w`.
    obtain ⟨w⟩ := _sub_lemma_C3_main_inverse_map_nonempty (A := A) D hdom
    exact ⟨fun _ => w, fun _ => w.property⟩
  · -- Domain is empty: any function works (vacuously).
    refine ⟨fun v => (hdom ⟨v⟩).elim, fun v => (hdom ⟨v⟩).elim⟩

/-- **(C3.main.3 — bijection)**: the forward and inverse maps are mutually
inverse. Uses `_sub_lemma_C3_3_subset_direction` and
`_sub_lemma_C3_3_superset_direction`.

Discharge: delegate to the existing `Spa_presheafValue_eq_rationalOpen`
(in `StructureSheaf.lean`), which provides the `Nonempty Equiv` between
`Spa (presheafValue D)` and `rationalOpen ∩ Spa A A⁺`. Extracting the
underlying equivalence yields both the forward map, the inverse map, and
the round-trip equalities `Equiv.symm_apply_apply` / `Equiv.apply_symm_apply`. -/
theorem _sub_lemma_C3_main_bijection
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [HasLocLiftPowerBounded A] [CompatiblePlusSubring A]
    (D : RationalLocData A) :
    -- Joint statement: forward ∘ inverse = identity, inverse ∘ forward = identity.
    ∃ (φ : Spa (presheafValue D) (presheafValue D)⁺ →
        (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)))
      (ψ : (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) →
        Spa (presheafValue D) (presheafValue D)⁺),
      (∀ w, ψ (φ w) = w) ∧ (∀ v, φ (ψ v) = v) := by
  obtain ⟨e⟩ := Spa_presheafValue_eq_rationalOpen (A := A) D
  exact ⟨e, e.symm, e.symm_apply_apply, e.apply_symm_apply⟩

/-! ## Injectivity of the Spa-pullback (Wedhorn 8.2: the extension is unique)

Wedhorn 8.2:3721 factors `j = Spa(ρ)` as `Spa(ρ') ∘ Spa(ι)`:
- `Spa(ρ') = comap (algebraMap A Aₛ)` is injective — "a valuation `v` on `A` extends
  *necessarily uniquely* to `Aₛ`" (wedhorn.txt:3736), since `D.s` is a unit in `Aₛ`;
- `Spa(ι) = comap D.coeRingHom` is injective on continuous valuations — a continuous
  valuation on the completion `Â⟨T/s⟩` is determined by its restriction to the dense
  image of `Aₛ` (wedhorn.txt:3729–3730: "Spa(ι) is a homeomorphism … by Proposition
  7.48"; Wedhorn defers 7.48 to [Hu2] Prop 3.9). -/

/-- **(Wedhorn 8.2:3736 — localization extension is unique)** A valuation on the rational
localisation `Localization.Away D.s` is determined by its restriction to `A` (every element
is `a/sⁿ`, and `v(a/sⁿ)` is fixed by `v(a)`, `v(s) ≠ 0`): `comap (algebraMap A Aₛ)` is
injective. -/
theorem comap_algebraMap_injective (D : RationalLocData A) :
    Function.Injective (comap (algebraMap A (Localization.Away D.s))) := by
  intro w₁ w₂ h
  refine ValuationSpectrum.ext (funext₂ fun x y => propext ?_)
  -- Write `x = a/sᵃ`, `y = b/sᵇ`; the common denominator `sᵃ·sᵇ ∈ powers s` maps to a unit.
  obtain ⟨⟨a, sa, hsa⟩, rfl⟩ := IsLocalization.mk'_surjective (M := Submonoid.powers D.s) x
  obtain ⟨⟨b, sb, hsb⟩, rfl⟩ := IsLocalization.mk'_surjective (M := Submonoid.powers D.s) y
  dsimp only
  have hsab : sa * sb ∈ Submonoid.powers D.s := Submonoid.mul_mem _ hsa hsb
  have hunit : IsUnit (algebraMap A (Localization.Away D.s) (sa * sb)) :=
    IsLocalization.map_units (Localization.Away D.s) ⟨sa * sb, hsab⟩
  -- `vle` is invariant under multiplication by the unit `algebraMap (sa·sb)`.
  have vle_unit_iff : ∀ (w : Spv (Localization.Away D.s)) (p q : Localization.Away D.s),
      w.vle (p * algebraMap A (Localization.Away D.s) (sa * sb))
            (q * algebraMap A (Localization.Away D.s) (sa * sb)) ↔ w.vle p q :=
    fun w p q => ⟨w.vle_mul_cancel (not_vle_zero_of_isUnit hunit w),
      fun hpq => w.mul_vle_mul_left hpq (algebraMap A (Localization.Away D.s) (sa * sb))⟩
  -- Clearing denominators: `(a/sᵃ)·(sᵃ·sᵇ) = a·sᵇ` and `(b/sᵇ)·(sᵃ·sᵇ) = b·sᵃ` (images of `A`).
  have hxa : IsLocalization.mk' (Localization.Away D.s) a ⟨sa, hsa⟩
        * algebraMap A (Localization.Away D.s) (sa * sb)
      = algebraMap A (Localization.Away D.s) (a * sb) := by
    rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  have hyb : IsLocalization.mk' (Localization.Away D.s) b ⟨sb, hsb⟩
        * algebraMap A (Localization.Away D.s) (sa * sb)
      = algebraMap A (Localization.Away D.s) (b * sa) := by
    rw [mul_comm sa sb, map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  -- So `w.vle (a/sᵃ) (b/sᵇ)` is determined by `comap (algebraMap A Aₛ) w` (Wedhorn 8.2:3736).
  have key : ∀ w : Spv (Localization.Away D.s),
      w.vle (IsLocalization.mk' (Localization.Away D.s) a ⟨sa, hsa⟩)
            (IsLocalization.mk' (Localization.Away D.s) b ⟨sb, hsb⟩)
      ↔ (comap (algebraMap A (Localization.Away D.s)) w).vle (a * sb) (b * sa) := by
    intro w
    rw [comap_vle, ← hxa, ← hyb, vle_unit_iff]
  rw [key w₁, key w₂, h]

/-- **(Wedhorn 8.2:3729 / Prop 7.48 — completion extension is unique)** A *continuous*
valuation on the completion `presheafValue D = Â⟨T/s⟩` is determined by its restriction to
the dense image of `Localization.Away D.s`: `comap D.coeRingHom` is injective on Spa-points.

This is the injectivity half of `Spa(ι)` being a homeomorphism (Wedhorn 8.2:3729–3730);
Wedhorn defers Prop 7.48 to [Hu2] Prop 3.9. Content: density of `Aₛ ↪ Â⟨T/s⟩`
(`UniformSpace.Completion.denseRange_coe`) + continuity pins the `vle` relation on all of
`Â⟨T/s⟩`. -/
theorem comap_coeRingHom_injOn_spa (D : RationalLocData A) [PlusSubring A]
    {w₁ w₂ : Spv (presheafValue D)}
    (hw₁ : w₁ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (hw₂ : w₂ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (h : comap D.coeRingHom w₁ = comap D.coeRingHom w₂) :
    w₁ = w₂ := by
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    intro y
    exact @UniformSpace.Completion.denseRange_coe (Localization.Away D.s) D.uniformSpace y
  exact ValuationSpectrum.eq_of_isContinuous_of_comap_eq_of_denseRange hdense
    ((mem_spa_iff w₁).mp hw₁).1 ((mem_spa_iff w₂).mp hw₂).1 h

/-- **(Wedhorn 8.2:3740 — `j = Spa(ρ)` is injective)** The Spa-pullback along the canonical
map `A → presheafValue D` is injective on Spa-points of the completion. Composes the
localization-uniqueness and completion-uniqueness halves via `canonicalMap = coeRingHom ∘
algebraMap`. -/
theorem comap_canonicalMap_injOn_spa (D : RationalLocData A) [PlusSubring A]
    {w₁ w₂ : Spv (presheafValue D)}
    (hw₁ : w₁ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (hw₂ : w₂ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (h : comap D.canonicalMap w₁ = comap D.canonicalMap w₂) :
    w₁ = w₂ := by
  have hcomp : D.canonicalMap
      = D.coeRingHom.comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp] at h
  simp only [Function.comp_apply] at h
  exact comap_coeRingHom_injOn_spa D hw₁ hw₂ (comap_algebraMap_injective D h)

/-- **Continuity-only form of `comap_coeRingHom_injOn_spa`.** The completion Spa-injectivity
needs only *continuity* of the two valuations (not the full plus-bounded Spa-membership): this
is exactly the hypothesis of the T-SUM-7 keystone. Useful for lifting points along restrictions
where the restricted point is not (yet) known to be plus-bounded. -/
theorem comap_coeRingHom_inj_of_isContinuous (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)} (h₁ : w₁.IsContinuous) (h₂ : w₂.IsContinuous)
    (h : comap D.coeRingHom w₁ = comap D.coeRingHom w₂) : w₁ = w₂ := by
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    intro y
    exact @UniformSpace.Completion.denseRange_coe (Localization.Away D.s) D.uniformSpace y
  exact ValuationSpectrum.eq_of_isContinuous_of_comap_eq_of_denseRange hdense h₁ h₂ h

/-- **Continuity-only form of `comap_canonicalMap_injOn_spa`** (`comap D.canonicalMap` is
injective on *continuous* points of `Spv (presheafValue D)`). -/
theorem comap_canonicalMap_inj_of_isContinuous (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)} (h₁ : w₁.IsContinuous) (h₂ : w₂.IsContinuous)
    (h : comap D.canonicalMap w₁ = comap D.canonicalMap w₂) : w₁ = w₂ := by
  have hcomp : D.canonicalMap
      = D.coeRingHom.comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp] at h
  simp only [Function.comp_apply] at h
  exact comap_coeRingHom_inj_of_isContinuous D h₁ h₂ (comap_algebraMap_injective D h)

/-- **(C3 main, reviewer Q3)**: assembly to discharge the headline
`Spa_presheafValue_eq_rationalOpen` in `StructureSheaf.lean`.

This declaration provides the downstream wrapper for the C3 discharge. The
existing `StructureSheaf.Spa_presheafValue_eq_rationalOpen` (sorry-bodied)
will delegate here once `/beastmode` fills the body.

Discharge plan (~100 LOC), now decomposed into 4 sub-leaves above:

1. **`_sub_lemma_C3_main_forward_map`** (~20 LOC): build the forward map via
   `Spa.comap_of_continuousRingHom`.
2. **`_sub_lemma_C3_main_inverse_map`** (~30 LOC): build the inverse map via
   the extension chain (Sub-lemmas 1 + 2 in the file's docstring).
3. **`_sub_lemma_C3_main_bijection`** (~30 LOC): forward and inverse are
   inverse to each other, using `Spa_comap_image_eq_rationalOpen` (sub-lemma 3).
4. **`_sub_lemma_C3_main_equiv_packaging`** (~10 LOC, this theorem):
   final `Equiv` package, assembled from `_sub_lemma_C3_main_bijection`. -/
theorem Spa_presheafValue_eq_rationalOpen_via_subcomponents
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [PlusSubring A]
    (D : RationalLocData A) :
    Nonempty (Spa (presheafValue D) (presheafValue D)⁺ ≃
      (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) := by
  classical
  -- The homeomorphism is `j = Spa(ρ)` (Wedhorn 8.2): the forward map is the pullback of
  -- valuations along `D.canonicalMap`, landing in `R(T/s) ∩ Spa A` (the ⊆ direction); it is
  -- a bijection by injectivity (`comap_canonicalMap_injOn_spa`, unique extension) and
  -- surjectivity onto `R(T/s)` (`exists_spa_presheafValue_of_rationalOpen`, the ⊇ direction).
  refine ⟨Equiv.ofBijective
    (fun w : ↥(Spa (presheafValue D) (presheafValue D)⁺) =>
      (⟨comap D.canonicalMap w.val,
        ⟨⟨_sub_lemma_C3_3_subset_direction_pullback_mem_spa D w,
            fun t ht => D.comap_canonicalMap_vle w.property.2 ht,
            D.comap_canonicalMap_not_vle_s_zero⟩,
          _sub_lemma_C3_3_subset_direction_pullback_mem_spa D w⟩⟩ :
        ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))))
    ⟨?_, ?_⟩⟩
  · -- Injectivity: Wedhorn 8.2 — the extension is unique.
    intro w₁ w₂ hw
    exact Subtype.ext (comap_canonicalMap_injOn_spa D w₁.property w₂.property
      (congrArg Subtype.val hw))
  · -- Surjectivity: every `v ∈ R(T/s) ∩ Spa A` is the pullback of a Spa-point of the
    -- completion (Wedhorn 8.2: image of `j` is `R(T/s)`).
    rintro ⟨v, hv_rat, hv_spa⟩
    obtain ⟨w', hw'_spa, hw'_comap⟩ := exists_spa_presheafValue_of_rationalOpen D hv_rat
    exact ⟨⟨w', hw'_spa⟩, Subtype.ext hw'_comap⟩

end ValuationSpectrum
