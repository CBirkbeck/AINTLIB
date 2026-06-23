/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.DualGaloisClosed
import HasseWeil.EC.IsogenyKernel
import HasseWeil.Curves.OrdAtInftyRamification

/-!
# The fixed-field equality `Im(φ*) = Fix(ker φ)` for a **two-curve** isogeny

The project's Galois fixed-field machinery (`Hasse/PointFix.lean`,
`EC/IsogenyAG/DualGaloisClosed.lean`, `EC/IsogenyAG/WallCascade.lean`) is *stated* for an
endomorphism `β : Isogeny W.toAffine W.toAffine`, but every step of it is in fact about the
**source** curve: the kernel `ker β ⊆ E₁.Point` acts on the source function field `K(E₁)` by
translation (`translateAlgEquivOfPoint W₁`), and the only cross-curve object is the pullback
`β.pullback : K(E₂) →ₐ[F] K(E₁)`.  None of the source-side facts (the translation action, its
faithfulness, the Artin finrank, the forward inclusion `Im(β*) ⊆ Fix(ker β)`) reference the
target curve at all.

This file re-bases the chain over a **general** `β : Isogeny W₁ W₂` (the project's points-bearing
`Basic.Isogeny`), proving — all axiom-clean — the two-curve

* `translate_pullback_invariance_of_xy_twoCurve` — covariance on `x_gen₂`/`y_gen₂` extends to all
  of `K(E₂)` (the two-curve generator extensionality `algHom_ext_x_y_gen_twoCurve`);
* `pullback_fieldRange_le_fixedField_twoCurve` — `Im(β*) ⊆ Fix(Multiplicative (ker β))`;
* `finrank_pullback_fieldRange_eq_degree_twoCurve` — `[K(E₁) : Im(β*)] = deg β`;
* `pullback_fieldRange_eq_fixedField_twoCurve` — the fixed-field **equality** (Silverman III.4.10c)
  from `{xy_family, #ker = deg}`;
* `fixedField_hfix_twoCurve` — the `hfix` shape (membership ↔ fixed-by-kernel).

The kernel-translation action `Multiplicative (ker β)` on `K(E₁)`, its faithfulness, and the
`SMulCommClass` are re-instanced here from the source-curve master action
`translateMulSemiringAction` (`EC/TranslationOrd.lean`).

The two genuine geometric inputs are then exactly the same two facts as in the endomorphism case,
read for a two-curve `β`: the per-`β` translation covariance `xy_family` (kernel translation fixes
the pullback generators) and the cardinality match `#ker β = deg β` (Silverman III.4.10c via the
two-curve good-fibre count `LocalizedDictionary`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10–4.11, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

namespace Isogeny

/-! ### The two-curve generator extensionality reducer -/

/-- **Two-curve `AlgHom` extensionality on the generic coordinates.** An `F`-algebra hom out of
`K(E₂)` is determined by its values on `x_gen W₂` and `y_gen W₂`.  (The two-curve analogue of
`algHom_ext_x_y_gen`; same proof, with distinct source/target.) -/
theorem algHom_ext_x_y_gen_twoCurve {A : Type*} [CommRing A] [Algebra F A]
    {ψ₁ ψ₂ : W₂.FunctionField →ₐ[F] A}
    (hx : ψ₁ (x_gen W₂) = ψ₂ (x_gen W₂)) (hy : ψ₁ (y_gen W₂) = ψ₂ (y_gen W₂)) : ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W₂.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ _ (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ _ (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ _ (AdjoinRoot.root W₂.polynomial)) =
      ψ₂ (algebraMap _ _ (AdjoinRoot.root W₂.polynomial))
    exact hy

/-- **Generator-restricted covariance reducer, two-curve** (the two-curve
`translate_pullback_invariance_of_xy_general`): covariance of `τ_k` (translation on the *source*
`K(E₁)` by `k ∈ E₁.Point`) with `β.pullback` on `x_gen₂` and `y_gen₂` extends to all of `K(E₂)`,
via the two-curve generator extensionality `algHom_ext_x_y_gen_twoCurve`. -/
theorem translate_pullback_invariance_of_xy_twoCurve
    (β : Isogeny W₁ W₂) (k : W₁.Point)
    (h_x : translateAlgEquivOfPoint W₁ k (β.pullback (x_gen W₂)) = β.pullback (x_gen W₂))
    (h_y : translateAlgEquivOfPoint W₁ k (β.pullback (y_gen W₂)) = β.pullback (y_gen W₂)) :
    ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k (β.pullback z) = β.pullback z := fun z =>
  DFunLike.congr_fun
    (algHom_ext_x_y_gen_twoCurve
      (ψ₁ := (translateAlgEquivOfPoint W₁ k).toAlgHom.comp β.pullback)
      (ψ₂ := β.pullback) h_x h_y) z

/-! ### Two-curve finite-dimensionality of the pullback extension

The endo `isogeny_finiteDimensional` is stated `W → W`; for a two-curve `β : Isogeny W₁ W₂` the
analogue `[K(E₁) : Im(β*)] < ∞` follows from the same transcendence-degree argument, packaged here
through the `SmoothPlaneCurve` algebraicity lemma `Curves.SmoothPlaneCurve.isAlgebraic_toAlgebra`
applied to a `CurveMap` carrying `β.pullback` — but, more directly, from the bare injective
`F`-algebra hom `β.pullback`, since the algebraicity argument never uses the basepoint condition. -/

/-- **`K(E₁)` is algebraic over `Im(β*)`, two-curve** (bare-pullback form): for `β : Isogeny W₁ W₂`,
with `K(E₁)` an `K(E₂)`-algebra via `β.pullback`, every element is algebraic.  Same
transcendence-degree argument as `Curves.SmoothPlaneCurve.isAlgebraic_toAlgebra`, depending only on
injectivity of `β.pullback`. -/
theorem isAlgebraic_toAlgebra_twoCurve (β : Isogeny W₁ W₂) (z : W₁.FunctionField) :
    letI := β.toAlgebra
    IsAlgebraic W₂.FunctionField z := by
  letI := β.toAlgebra
  set C₁ : Curves.SmoothPlaneCurve F := ⟨W₁⟩ with hC₁
  set C₂ : Curves.SmoothPlaneCurve F := ⟨W₂⟩ with hC₂
  -- `β* x₂` is transcendental over `F`
  have hu : Transcendental F (β.pullback C₂.coordX) := fun hAlg =>
    C₂.transcendental_coordX
      ((isAlgebraic_algHom_iff β.pullback β.pullback_injective).mp hAlg)
  have hindep : AlgebraicIndependent F
      (![β.pullback C₂.coordX] : Fin 1 → C₁.FunctionField) := by
    rw [algebraicIndependent_unique_type_iff]; exact hu
  have hbasis : IsTranscendenceBasis F
      (![β.pullback C₂.coordX] : Fin 1 → C₁.FunctionField) := by
    apply hindep.isTranscendenceBasis_of_lift_trdeg_le_of_finite
    rw [C₁.functionField_trdeg_eq_one]; simp
  have hle : Algebra.adjoin F
      (Set.range (![β.pullback C₂.coordX] : Fin 1 → C₁.FunctionField)) ≤ β.pullback.range := by
    rw [Algebra.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    fin_cases i
    exact ⟨C₂.coordX, rfl⟩
  have hrange := ((hbasis.isAlgebraic).isAlgebraic z).tower_top_of_subalgebra_le hle
  obtain ⟨p, hp_ne, hp_eval⟩ := hrange
  let e : C₂.FunctionField ≃ₐ[F] β.pullback.range :=
    AlgEquiv.ofInjective β.pullback β.pullback_injective
  let f : (↥β.pullback.range) →+* C₂.FunctionField := e.symm
  have hf_inj : Function.Injective f := e.symm.injective
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf_inj).mpr hp_ne, ?_⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_map] at hp_eval ⊢
  have hcomp : (algebraMap C₂.FunctionField C₁.FunctionField).comp f =
      algebraMap (↥β.pullback.range) C₁.FunctionField := by
    apply RingHom.ext
    intro w
    change β.pullback (e.symm w) = (w : C₁.FunctionField)
    exact congrArg Subtype.val (e.apply_symm_apply w)
  rw [hcomp]
  exact hp_eval

/-- **Two-curve finite-dimensionality**: `[K(E₁) : Im(β*)] < ∞` for any `β : Isogeny W₁ W₂`.  From
`isAlgebraic_toAlgebra_twoCurve` (algebraic) + `EssFiniteType` (localization of a finite-type ring)
via `Algebra.finite_of_essFiniteType_of_isAlgebraic`. -/
theorem finiteDimensional_toAlgebra_twoCurve (β : Isogeny W₁ W₂) :
    @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule := by
  letI := β.toAlgebra
  haveI : IsScalarTower F W₂.FunctionField W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun x => (β.pullback.commutes x).symm
  haveI : Algebra.EssFiniteType W₂.FunctionField W₁.FunctionField :=
    Algebra.EssFiniteType.of_comp F W₂.FunctionField W₁.FunctionField
  haveI : Algebra.IsAlgebraic W₂.FunctionField W₁.FunctionField :=
    ⟨fun z => isAlgebraic_toAlgebra_twoCurve β z⟩
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **Two-curve degree positivity**: `0 < deg β` for `β : Isogeny W₁ W₂`. -/
theorem degree_pos_twoCurve (β : Isogeny W₁ W₂) : 0 < β.degree := by
  unfold Isogeny.degree
  exact @Module.finrank_pos W₂.FunctionField W₁.FunctionField _ _
    β.toAlgebra.toModule _ (finiteDimensional_toAlgebra_twoCurve β) _ _ _

/-! ### The kernel-translation action on the source function field

For a two-curve `β : Isogeny W₁ W₂`, the kernel `ker β ⊆ E₁.Point` acts on the *source*
function field `K(E₁)` by translation — exactly as in the endomorphism case, since the action
references only the source.  We re-instance the `MulSemiringAction`, `SMulCommClass`, and
`FaithfulSMul` from the source-curve master action `translateMulSemiringAction`. -/

/-- **Restricted kernel-translation action**: `Multiplicative (ker β)` acts on `K(E₁)` via the
inclusion `ker β → E₁.Point` composed with the master translation action.

`scoped` (and likewise the companion `SMulCommClass`/`FaithfulSMul`) so the `MulSemiringAction`
instance on the function field does **not** leak into downstream files' global instance scope (where
it would expand `simp`/typeclass search through `Submodule` lattice instances); inside this file's
own `namespace HasseWeil.Isogeny` the scoped instances are active automatically. -/
noncomputable scoped instance kernelMulSemiringAction_twoCurve (β : Isogeny W₁ W₂) :
    MulSemiringAction (Multiplicative β.kernel) W₁.FunctionField :=
  MulSemiringAction.compHom W₁.FunctionField
    ((AddSubgroup.subtype β.kernel).toMultiplicative :
      Multiplicative β.kernel →* Multiplicative W₁.Point)

scoped instance kernelMulSemiringAction_twoCurve_smulCommClass (β : Isogeny W₁ W₂) :
    SMulCommClass (Multiplicative β.kernel) F W₁.FunctionField where
  smul_comm g c f := by
    change translateAlgEquivOfPoint W₁ (Multiplicative.toAdd g).val (c • f) =
      c • translateAlgEquivOfPoint W₁ (Multiplicative.toAdd g).val f
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]

theorem kernelMulSemiringAction_twoCurve_smul (β : Isogeny W₁ W₂)
    (g : Multiplicative β.kernel) (f : W₁.FunctionField) :
    g • f = translateAlgEquivOfPoint W₁ (Multiplicative.toAdd g).val f := rfl

/-- **The kernel-translation action is faithful** (the two-curve `faithfulSMul_kernel`): distinct
kernel points give distinct translations (`translateAlgEquivOfPoint_injective`, source-only). -/
scoped instance faithfulSMul_kernel_twoCurve (β : Isogeny W₁ W₂) :
    FaithfulSMul (Multiplicative β.kernel) W₁.FunctionField where
  eq_of_smul_eq_smul {g₁ g₂} h :=
    Multiplicative.toAdd.injective <| Subtype.ext <|
      translateAlgEquivOfPoint_injective W₁ (AlgEquiv.ext fun f => h f)

/-! ### Kernel finiteness, the forward inclusion, and the intrinsic finrank (two-curve) -/

/-- **Kernel finiteness from the covariance `hcov`, two-curve** (the two-curve
`finite_kernel_of_hcov`): the kernel embeds into the finite group `Aut(K(E₁)/β^*K(E₂))` via the
faithful translation action. -/
theorem finite_kernel_of_hcov_twoCurve (β : Isogeny W₁ W₂)
    (hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z) :
    Finite β.kernel := by
  letI := β.toAlgebra
  haveI : @FiniteDimensional W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule :=
    finiteDimensional_toAlgebra_twoCurve β
  haveI : Finite (@AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra) := Finite.of_fintype _
  -- the injective kernel-translation map into the automorphism group
  refine Finite.of_injective
    (β := @AlgEquiv W₂.FunctionField W₁.FunctionField W₁.FunctionField _ _ _
      β.toAlgebra β.toAlgebra)
    (fun k => AlgEquiv.ofRingEquiv (f := (translateAlgEquivOfPoint W₁ k.val).toRingEquiv)
      (fun r => hcov k r)) ?_
  intro k₁ k₂ h
  apply Subtype.ext
  apply translateAlgEquivOfPoint_injective W₁
  refine AlgEquiv.ext fun z => ?_
  exact DFunLike.congr_fun h z

/-- **Forward inclusion of the fixed-field theorem, two-curve** (the two-curve
`pullback_fieldRange_le_fixedField_general`): under the xy-covariance family,
`Im(β*) ⊆ Fix(Multiplicative (ker β))`. -/
theorem pullback_fieldRange_le_fixedField_twoCurve (β : Isogeny W₁ W₂)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (x_gen W₂)) = β.pullback (x_gen W₂)) ∧
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (y_gen W₂)) = β.pullback (y_gen W₂))) :
    β.pullback.fieldRange ≤
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W₁.FunctionField) := by
  rintro z ⟨w, rfl⟩
  intro g
  change translateAlgEquivOfPoint W₁ (Multiplicative.toAdd g).val (β.pullback w) = β.pullback w
  exact translate_pullback_invariance_of_xy_twoCurve β (Multiplicative.toAdd g).val
    (h_xy_family (Multiplicative.toAdd g)).1
    (h_xy_family (Multiplicative.toAdd g)).2 w

/-- **`[K(E₁) : Im(β*)] = deg β`, two-curve** (the two-curve
`finrank_pullback_fieldRange_eq_degree`): the source function field has the same dimension over the
pullback image `Im(β*)` as the isogeny degree `[K(E₁) : K(E₂)]`, since `β*` is an isomorphism
`K(E₂) ≅ Im(β*)`. -/
theorem finrank_pullback_fieldRange_eq_degree_twoCurve (β : Isogeny W₁ W₂) :
    Module.finrank ↥β.pullback.fieldRange W₁.FunctionField = β.degree := by
  letI := β.toAlgebra
  letI inst_im : Algebra ↥β.pullback.fieldRange W₁.FunctionField :=
    IntermediateField.toAlgebra _
  change @Module.finrank ↥β.pullback.fieldRange W₁.FunctionField _ _ inst_im.toModule = β.degree
  show _ = @Module.finrank W₂.FunctionField W₁.FunctionField _ _ β.toAlgebra.toModule
  -- the base isomorphism `K(E₂) ≃+* Im(β*)` induced by `β*`
  let i_alg : W₂.FunctionField ≃ₐ[F] ↥β.pullback.range :=
    AlgEquiv.ofInjective β.pullback β.pullback_injective
  let bridge : ↥β.pullback.range ≃+* ↥β.pullback.fieldRange :=
    { toFun := fun x => ⟨x.val, by obtain ⟨y, hy⟩ := x.property; exact ⟨y, hy⟩⟩
      invFun := fun x => ⟨x.val, by obtain ⟨y, hy⟩ := x.property; exact ⟨y, hy⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let i : W₂.FunctionField ≃+* ↥β.pullback.fieldRange := i_alg.toRingEquiv.trans bridge
  let j : W₁.FunctionField ≃+* W₁.FunctionField := RingEquiv.refl _
  have h_compat : (algebraMap ↥β.pullback.fieldRange W₁.FunctionField).comp i.toRingHom =
      j.toRingHom.comp (algebraMap W₂.FunctionField W₁.FunctionField) := by
    ext c; rfl
  exact (Algebra.finrank_eq_of_equiv_equiv i j h_compat).symm

/-- **`K(E₁)` is finite-dimensional over `Im(β*)`, two-curve** (the two-curve
`finiteDimensional_pullback_fieldRange`). -/
theorem finiteDimensional_pullback_fieldRange_twoCurve (β : Isogeny W₁ W₂) :
    FiniteDimensional ↥β.pullback.fieldRange W₁.FunctionField :=
  FiniteDimensional.of_finrank_pos
    ((finrank_pullback_fieldRange_eq_degree_twoCurve β).symm ▸ degree_pos_twoCurve β)

/-! ### The fixed-field equality and `hfix` (two-curve) -/

/-- **The Galois fixed-field equality `Im(β*) = Fix(ker β)`, two-curve** (Silverman III.4.10c).
Inputs: the xy-covariance family and the cardinality match `#ker β = deg β` (`Nat.card` form).
Kernel finiteness is derived from the covariance, `FiniteDimensional ↥Im(β*) K(E₁)` from the
intrinsic finrank, and the Artin step `FixedPoints.finrank_eq_card` needs only the finite group
`Multiplicative (ker β)` acting faithfully. -/
theorem pullback_fieldRange_eq_fixedField_twoCurve (β : Isogeny W₁ W₂)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (x_gen W₂)) = β.pullback (x_gen W₂)) ∧
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (y_gen W₂)) = β.pullback (y_gen W₂)))
    (h_card : Nat.card β.kernel = β.degree) :
    β.pullback.fieldRange =
      (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W₁.FunctionField) := by
  have hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_twoCurve β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov_twoCurve β hcov
  haveI : Fintype (Multiplicative β.kernel) := Fintype.ofFinite _
  haveI := finiteDimensional_pullback_fieldRange_twoCurve β
  refine IntermediateField.eq_of_le_of_finrank_eq'
    (pullback_fieldRange_le_fixedField_twoCurve β h_xy_family) ?_
  rw [finrank_pullback_fieldRange_eq_degree_twoCurve β, ← h_card,
    Nat.card_congr (Multiplicative.ofAdd (α := β.kernel)), Nat.card_eq_fintype_card]
  exact (FixedPoints.finrank_eq_card (Multiplicative β.kernel) W₁.FunctionField).symm

/-- **`hfix` from `xy_family` + `#ker = deg`, two-curve** (Silverman III.4.10c).  The image of
`β.pullback` is exactly the subset of `K(E₁)` fixed by the kernel translations. -/
theorem fixedField_hfix_twoCurve (β : Isogeny W₁ W₂)
    (h_xy_family : ∀ k : β.kernel,
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (x_gen W₂)) = β.pullback (x_gen W₂)) ∧
      (translateAlgEquivOfPoint W₁ k.val (β.pullback (y_gen W₂)) = β.pullback (y_gen W₂)))
    (h_card : Nat.card β.kernel = β.degree) :
    ∀ z : W₁.FunctionField,
      z ∈ β.pullback.range ↔
        ∀ σ ∈ (Set.range (fun k : β.kernel => translateAlgEquivOfPoint W₁ k.val)), σ z = z := by
  have hcov : ∀ k : β.kernel, ∀ z : W₂.FunctionField,
      translateAlgEquivOfPoint W₁ k.val (β.pullback z) = β.pullback z :=
    fun k z => translate_pullback_invariance_of_xy_twoCurve β k.val
      (h_xy_family k).1 (h_xy_family k).2 z
  haveI : Finite β.kernel := finite_kernel_of_hcov_twoCurve β hcov
  haveI : Fintype (Multiplicative β.kernel) := Fintype.ofFinite _
  have h_eq := pullback_fieldRange_eq_fixedField_twoCurve β h_xy_family h_card
  intro z
  constructor
  · rintro ⟨w, rfl⟩ σ ⟨k, rfl⟩
    have hmem : β.pullback w ∈ β.pullback.fieldRange := ⟨w, rfl⟩
    rw [h_eq] at hmem
    exact hmem (Multiplicative.ofAdd k)
  · intro hz
    have hmem : z ∈ (FixedPoints.intermediateField (Multiplicative β.kernel) :
        IntermediateField F W₁.FunctionField) := fun g => hz _ ⟨Multiplicative.toAdd g, rfl⟩
    rw [← h_eq, AlgHom.mem_fieldRange] at hmem
    rw [AlgHom.mem_range]
    exact hmem

end Isogeny

end HasseWeil
