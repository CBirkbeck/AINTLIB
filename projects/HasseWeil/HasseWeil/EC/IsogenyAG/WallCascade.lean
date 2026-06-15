/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.KernelCount
import HasseWeil.EC.IsogenyAG.DualGaloisClosed

/-!
# The wall cascade: the separable dual is unconditional for the CoordHom class (ROUTE-W, W-4)

The W-3 kernel count `card_kernel_eq_degree_of_separable_coordHom` (`EC/KernelCount.lean`,
Silverman III.4.10c via the good-fibre/different-ideal route) makes `#ker β = deg β` a *theorem*
for the class

  `{β separable, CoordHom for β.pullback (module-finite), cofinite PullbackEvaluation, K̄}`.

This file cascades that count through the dual's two remaining Galois witnesses, in the
reviewer's (round 24) order — with the count now geometric, the fixed-field equality and then
normality/descent fall out **without circularity**:

1. **Im = Fix** (Silverman III.4.10c): `pullback_fieldRange_eq_fixedField_general`
   (`DualGaloisClosed.lean`) consumes `{xy_family, #ker = deg}`; both are theorems for the class
   (`xy_family_of_pullbackEvaluation` + the count), so
   `β.pullback.fieldRange = Fix(ker β)` holds unconditionally
   (`pullback_fieldRange_eq_fixedField_of_coordHom`).
2. **Galois transport** (Artin): mathlib's `IsGalois.of_fixed_field` makes `K(E) / Fix(ker β)`
   Galois for the finite translation action; transporting along the base isomorphism
   `K(E) ≃+* Fix(ker β)` induced by `β.pullback` (via `IsGalois.of_equiv_equiv`, the
   fieldRange↔`toAlgebra` move of `Hasse/PointFix.lean`'s
   `finrank_pullback_fieldRange_eq_degree`) yields `IsGalois` for the `β.toAlgebra` structure
   (`isGalois_of_xy_family_card`), hence **`h_normal`** (`normal_of_xy_family_card`).
3. **`hdesc` by counting** (Silverman III.4.10c, the torsor): the kernel-translation map
   `kernelTranslateForwardAut` is injective; `#Aut = deg β` (Galois, from step 2 via
   `card_aut_eq_degree_of_isGalois`) and `#ker β = deg β` (the count) make it a bijection
   between finite sets of equal cardinality, so **every** `σ` is a kernel translation `τ_k`,
   and `genericPointAct_kernelTranslateForwardAut` reads off
   `σ(P_gen) − P_gen = lift k` (`hdesc_of_xy_family_card`).
4. **The payoff**: all of `{hdeg, hgcomm, h_normal, hdesc, hν}` are theorems for the class, so
   `DualGaloisData φ` — hence the dual isogeny — needs **no carried geometric witnesses**:
   only the structural coherence data `{CoordHom, PullbackEvaluation, h_pb, h_hom}` plus
   `[IsAlgClosed F]`/`[IsIntegrallyClosed]` and separability
   (`dualGaloisData_of_coordHom_unconditional`, `exists_dual_of_coordHom_unconditional`,
   and the class-restricted universal shape `dualGaloisData_of_class` — see the pointer on
   `EC.universal_dualGaloisData`, `EC/IsogenyAG/Dual.lean`, which this does *not* replace:
   that sorry covers arbitrary isogenies, including the inseparable side).

The Galois-transport steps 2–3 are **field-general** (no `[IsAlgClosed F]`, no `[Fintype F]`):
they consume only `{xy_family, #ker = deg}`, exactly like the fixed-field equality they extend.

## Main statements

* `isGalois_of_xy_family_card` — `K(E)/β^*K(E)` is Galois from `{xy_family, #ker = deg}`.
* `normal_of_xy_family_card` — the `h_normal` witness shape, same inputs.
* `hdesc_of_xy_family_card` — the `hdesc` witness shape, same inputs.
* `pullback_fieldRange_eq_fixedField_of_coordHom` / `normal_of_separable_coordHom` /
  `hdesc_of_separable_coordHom` — the three instantiated at the W-3 class over `K̄`.
* `dualGaloisData_of_pullbackEvaluation_unconditional` /
  `dualGaloisData_of_coordHom_unconditional` — `DualGaloisData φ` with every Galois witness a
  theorem.
* `exists_dual_of_pullbackEvaluation_unconditional` / `exists_dual_of_coordHom_unconditional` —
  the dual exists for the class.
* `dualGaloisData_of_class` — the class-restricted form of `EC.universal_dualGaloisData`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10–4.11, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-! ### The Galois transport (field-general)

`K(E)/β^*K(E)` is Galois from `{xy_family, #ker = deg}`: Artin's theorem on the fixed
subfield of the finite translation action, transported from the subfield inclusion to the
`β.toAlgebra` structure along the isomorphism `K(E) ≅ Im(β^*) = Fix(ker β)`. -/

/-- **`K(E)/β^*K(E)` is Galois** (Silverman III.4.10c, Galois form), field-general, from the
xy-covariance family and the cardinality match `#ker β = deg β`.  By
`pullback_fieldRange_eq_fixedField_general`, `Im(β^*) = Fix(Multiplicative (ker β))`; mathlib's
Artin instance `IsGalois.of_fixed_field` makes `K(E)` Galois over the fixed subfield of the
finite faithful translation action, and `IsGalois.of_equiv_equiv` transports along the base
isomorphism `K(E) ≃+* Fix(ker β)` induced by `β.pullback` (the
fieldRange↔`toAlgebra` move of `finrank_pullback_fieldRange_eq_degree`). -/
theorem isGalois_of_xy_family_card (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree) :
    letI := β.toAlgebra
    IsGalois W.toAffine.FunctionField W.toAffine.FunctionField := by
  letI := β.toAlgebra
  -- the kernel-translation covariance and kernel finiteness
  have hcov : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_general W β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov W β hcov
  -- Im(β^*) = Fix(Multiplicative (ker β)) (Silverman III.4.10c)
  have h_eq := pullback_fieldRange_eq_fixedField_general W β h_xy_family h_card
  -- `β^*` is fixed-subfield-valued (forward inclusion, via Im = Fix)
  have hmem : ∀ z : W.toAffine.FunctionField,
      β.pullback z ∈
        FixedPoints.subfield (Multiplicative β.kernel) W.toAffine.FunctionField := by
    intro z
    have hz : β.pullback z ∈ β.pullback.fieldRange := ⟨z, rfl⟩
    rw [h_eq] at hz
    exact hz
  -- ... and surjects onto the fixed subfield (backward inclusion, via Im = Fix)
  have hsurj : ∀ w : W.toAffine.FunctionField,
      w ∈ FixedPoints.subfield (Multiplicative β.kernel) W.toAffine.FunctionField →
      ∃ z, β.pullback z = w := by
    intro w hw
    have hw' : w ∈ β.pullback.fieldRange := by
      rw [h_eq]
      exact hw
    exact hw'
  -- the base isomorphism `K(E) ≃+* Fix(ker β)` induced by `β^*`
  let e : W.toAffine.FunctionField ≃+*
      (FixedPoints.subfield (Multiplicative β.kernel) W.toAffine.FunctionField) :=
    RingEquiv.ofBijective
      (β.pullback.toRingHom.codRestrict
        (FixedPoints.subfield (Multiplicative β.kernel) W.toAffine.FunctionField) hmem)
      ⟨fun a b hab => β.pullback_injective (congrArg Subtype.val hab),
       fun w => by
        obtain ⟨z, hz⟩ := hsurj w.val w.property
        exact ⟨z, Subtype.ext hz⟩⟩
  -- transport mathlib's Artin instance `IsGalois (Fix(ker β)) K(E)` along `e.symm`/`refl`
  refine IsGalois.of_equiv_equiv
    (f := e.symm) (g := RingEquiv.refl W.toAffine.FunctionField) ?_
  refine RingHom.ext fun w => ?_
  exact congrArg Subtype.val (e.apply_symm_apply w)

/-- **The `h_normal` witness is a theorem from `{xy_family, #ker = deg}`** (Silverman
III.4.10c), field-general: the function-field extension `K(E)/β^*K(E)` is normal, in exactly
the witness shape carried by `dualGaloisData_of_separable_general` /
`card_kernel_eq_degree_of_separable_concrete`.  Immediate from `isGalois_of_xy_family_card`. -/
theorem normal_of_xy_family_card (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree) :
    letI := β.toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField := by
  letI := β.toAlgebra
  haveI := isGalois_of_xy_family_card W β h_xy_family h_card
  exact IsGalois.to_normal

/-- **The `hdesc` witness is a theorem from `{xy_family, #ker = deg}`** (Silverman III.4.10c,
the generic-point translation torsor), field-general, by **counting**: the kernel-translation
map `kernelTranslateForwardAut : ker β → Aut(K(E)/β^*K(E))` is injective
(`kernelTranslateForwardAut_injective`); `#Aut = deg β` (Galois theory, from
`isGalois_of_xy_family_card` via `card_aut_eq_degree_of_isGalois`) and `#ker β = deg β` (the
supplied count) make it a bijection between finite types of equal cardinality
(`Nat.bijective_iff_injective_and_card`).  Hence every `σ ∈ Aut(K(E)/β^*K(E))` *is* a kernel
translation `τ_k`, and the Phase-1 action lemma `genericPointAct_kernelTranslateForwardAut`
identifies `σ(P_gen) − P_gen = lift k`. -/
theorem hdesc_of_xy_family_card (β : Isogeny W.toAffine W.toAffine)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W k.val (β.pullback (x_gen W)) =
        β.pullback (x_gen W)) ∧
      (translateAlgEquivOfPoint W k.val (β.pullback (y_gen W)) =
        β.pullback (y_gen W)))
    (h_card : Nat.card β.kernel = β.degree) :
    ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W := by
  letI := β.toAlgebra
  -- the kernel-translation covariance, kernel finiteness, and the Galois package
  have hcov : ∀ k : β.kernel, ∀ z : W.toAffine.FunctionField,
      translateAlgEquivOfPoint W k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_general W β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov W β hcov
  haveI hfd : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ β.toAlgebra.toModule := isogeny_finiteDimensional W β
  haveI hgal := isGalois_of_xy_family_card W β h_xy_family h_card
  haveI : Finite (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) :=
    Finite.of_fintype _
  -- #Aut = deg β (Galois theory) and #ker β = deg β (the count) make the injective
  -- kernel-translation map a bijection
  have hAut : Nat.card (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra) = β.degree :=
    Isogeny.card_aut_eq_degree_of_isGalois β hfd hgal
  have hbij : Function.Bijective (kernelTranslateForwardAut W β hcov) :=
    (Nat.bijective_iff_injective_and_card _).mpr
      ⟨kernelTranslateForwardAut_injective W β hcov, by rw [h_card, hAut]⟩
  -- every σ is a kernel translation τ_k, and τ_k(P_gen) − P_gen = lift k
  intro σ
  obtain ⟨k, hk⟩ := hbij.2 σ
  refine ⟨k.val, k.property, ?_⟩
  rw [← hk, genericPointAct_kernelTranslateForwardAut W β hcov k, add_comm,
    add_sub_cancel_right]

/-! ### The W-3 class over `K̄`: every Galois witness instantiated

The hypothesis class of the W-3 kernel count: `β` separable with a coordinate-ring witness
`cd` for its pullback (module-finite) and the cofinite pullback-evaluation coherence, over an
algebraically closed base.  `xy_family` is `xy_family_of_pullbackEvaluation` and `#ker = deg`
is the W-3 count, so the three Galois facts above hold with no carried witnesses. -/

section AlgClosed

variable [IsAlgClosed F] [IsIntegrallyClosed W.toAffine.CoordinateRing]

/-- **Im = Fix for the W-3 class** (Silverman III.4.10c): the fixed-field equality
`β.pullback.fieldRange = Fix(Multiplicative (ker β))` is a theorem for a separable isogeny
with a module-finite `CoordHom` and the cofinite pullback-evaluation witness over `K̄` —
both inputs of `pullback_fieldRange_eq_fixedField_general` are now theorems
(`xy_family_of_pullbackEvaluation` + the W-3 count). -/
theorem pullback_fieldRange_eq_fixedField_of_coordHom
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W.toAffine.FunctionField) :=
  pullback_fieldRange_eq_fixedField_general W β
    (WeilPairing.xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable_coordHom W β hsep cd hbad hw)

/-- **`h_normal` for the W-3 class** (Silverman III.4.10c): normality of `K(E)/β^*K(E)` is a
theorem for a separable isogeny with a module-finite `CoordHom` and the cofinite
pullback-evaluation witness over `K̄`. -/
theorem normal_of_separable_coordHom
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    letI := β.toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField :=
  normal_of_xy_family_card W β
    (WeilPairing.xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable_coordHom W β hsep cd hbad hw)

/-- **`hdesc` for the W-3 class** (Silverman III.4.10c): the generic-point translation torsor
— every `σ(P_gen) − P_gen` is an `F`-rational kernel point — is a theorem for a separable
isogeny with a module-finite `CoordHom` and the cofinite pullback-evaluation witness over
`K̄`. -/
theorem hdesc_of_separable_coordHom
    (β : Isogeny W.toAffine W.toAffine) (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _ β.toAlgebra β.toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ β.kernel ∧
        liftPointToKE W k = genericPointAct W β σ - genericPoint W :=
  hdesc_of_xy_family_card W β
    (WeilPairing.xy_family_of_pullbackEvaluation W β hbad hw)
    (card_kernel_eq_degree_of_separable_coordHom W β hsep cd hbad hw)

/-! ### The payoff: `DualGaloisData` and the dual with no carried Galois witnesses -/

/-- **`DualGaloisData φ` for the W-3 class — every Galois witness a theorem** (Silverman
III.4.10–4.11, III.6.1).  Compared to `dualGaloisData_of_pullbackEvaluation`
(`DualGaloisClosed.lean`), the previously carried `hdeg`/`h_normal`/`hdesc`/`hν` are all
discharged: `hdeg` by `isogeny_degree_pos`, `h_normal`/`hdesc` by the W-4 cascade above, and
`hν` by the `MulByIntBasepoint` theorem `hν_mulByInt`.  Residuals: only the structural
coherence data `{h_pb, cd, PullbackEvaluation}` and separability. -/
noncomputable def dualGaloisData_of_pullbackEvaluation_unconditional
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_pullbackEvaluation W φ β h_pb hsep
    (isogeny_degree_pos W β).ne' hbad hw
    (normal_of_separable_coordHom W β hsep cd hbad hw)
    (hdesc_of_separable_coordHom W β hsep cd hbad hw)
    (hν_mulByInt W (β.degree : ℤ)
      (by exact_mod_cast (isogeny_degree_pos W β).ne'))

/-- **`DualGaloisData φ` for a separable isogeny with a `CoordHom` over `K̄`, unconditional**
(Silverman III.6.1, the W-4 capstone): in the `(φE, cd, h_pb, h_hom)` witness shape of
`pullbackEvaluation_of_coordHom`, with **no carried Galois witnesses** — compare
`dualGaloisData_of_coordHom` (`DualGaloisClosed.lean`), which still carried
`{hdeg, h_normal, hdesc, hν}`.  Residuals: only the structural coherence data
`{cd, h_pb, h_hom}` and separability. -/
noncomputable def dualGaloisData_of_coordHom_unconditional
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φ.toPointMap cd P)
    (hsep : β.IsSeparable) :
    EC.Isogeny.DualGaloisData φ :=
  dualGaloisData_of_pullbackEvaluation_unconditional W φ β h_pb hsep
    ⟨cd.toAlgHom, fun u => by
      have h := cd.compat u
      rw [h_pb] at h
      exact h⟩
    Set.finite_empty
    (WeilPairing.pullbackEvaluation_of_coordHom W φ cd β h_pb h_hom)

/-- **`exists_dual` for the W-3 class** (Silverman III.6.1): a separable isogeny with the
module-finite `CoordHom` + cofinite pullback-evaluation coherence over `K̄` admits a reverse
isogeny, with no carried Galois witnesses. -/
theorem exists_dual_of_pullbackEvaluation_unconditional
    (φ : EC.Isogeny W.toAffine W.toAffine)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (hsep : β.IsSeparable)
    (cd : (β.endCurveMap W).CoordHom)
    {bad : Set (W_smooth W).SmoothPoint} (hbad : bad.Finite)
    (hw : WeilPairing.PullbackEvaluation W β bad) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_pullbackEvaluation_unconditional W φ β h_pb hsep cd hbad hw))

/-- **`exists_dual` for a separable isogeny with a `CoordHom` over `K̄`, unconditional**
(Silverman III.6.1 capstone): the dual exists from `{cd, h_pb, h_hom, hsep}` alone. -/
theorem exists_dual_of_coordHom_unconditional
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φ.toPointMap cd P)
    (hsep : β.IsSeparable) :
    Nonempty (EC.Isogeny W.toAffine W.toAffine) :=
  φ.exists_dual_of_witness
    (φ.hasDualWitness_of_galoisData
      (dualGaloisData_of_coordHom_unconditional W φ cd β h_pb h_hom hsep))

/-- **The class-restricted form of `EC.universal_dualGaloisData`** (Silverman III.4.10c +
III.6.1): for the separable CoordHom class over `K̄`, the universal Galois-data statement is a
*theorem* — `Nonempty (DualGaloisData φ)` holds with no geometric witnesses, only the
structural coherence data `{cd, h_pb, h_hom}` and separability.  The universal sorry in
`EC/IsogenyAG/Dual.lean` is **not** subsumed: it quantifies over arbitrary isogenies between
possibly distinct curves (including the inseparable/Frobenius side); this is its restriction
to the W-3 endomorphism class. -/
theorem dualGaloisData_of_class
    (φ : EC.Isogeny W.toAffine W.toAffine) (cd : φ.toCurveMap.CoordHom)
    (β : Isogeny W.toAffine W.toAffine)
    (h_pb : φ.toCurveMap.pullback = β.pullback)
    (h_hom : ∀ P : W.toAffine.Point, β.toAddMonoidHom P = φ.toPointMap cd P)
    (hsep : β.IsSeparable) :
    Nonempty (EC.Isogeny.DualGaloisData φ) :=
  ⟨dualGaloisData_of_coordHom_unconditional W φ cd β h_pb h_hom hsep⟩

end AlgClosed

end HasseWeil
