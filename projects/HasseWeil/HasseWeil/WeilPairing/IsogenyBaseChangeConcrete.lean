/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.OneSubScaling

/-!
# Concrete base-change of a function-field pullback (CoordHom-free)

For a smooth plane curve `C / F` and an `F`-algebra extension `L` with `L/F` algebraic, the
function-field scalar-extension iso `K(C_L) ≅ L ⊗_F K(C)` is **already** available, axiom-clean, in
`HasseWeil/Curves/CurveMapBaseChange.lean`:

* `functionField_tensor_locBaseChange L : (L ⊗ K(C)) ≃ₐ[L] FractionRing (L ⊗ C.CR)`,
* `functionField_baseChange_fracEquiv L : FractionRing (L ⊗ C.CR) ≃ₐ[L] K(C_L)`.

Composing them gives the iso `Φ : (L ⊗ K(C)) ≃ₐ[L] K(C_L)` (`tensorFunctionFieldEquiv`).

This file uses `Φ` to **construct** the base-change of an arbitrary function-field `F`-algebra hom
`f : K(C) →ₐ[F] K(C)` — *no `CoordHom` required* — as the conjugate

  `baseChangePullback f := Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹ : K(C_L) →ₐ[L] K(C_L)`,

an honest `L`-algebra hom (`Algebra.TensorProduct.map (AlgHom.id L) f` is the `L`-linear scalar
extension of the `F`-linear `f`, conjugated by the `L`-algebra equiv `Φ`).

The payoff (`oneSubFrobeniusPullback_L`) is the concrete `pullback_L` field of `OneSubScalingData`
for the separable genuine isogeny `1 − π`, whose pullback has poles at the affine kernel so admits
**no** `CoordHom` — hence the whole CoordHom-free route.

## Degree preservation

`finrank_baseChangePullback_eq_finrank_lTensorMap` reduces the degree of the conjugate
`baseChangePullback f` (as an `Isogeny`, via `Isogeny.degree_eq_of_finrank_eq`) to the `finrank` of
the *scalar extension* `id_L ⊗ f` over `L ⊗ K(C)`, by transporting the finrank along the `L`-algebra
equiv `Φ` (`Algebra.finrank_eq_of_equiv_equiv`).  This **conjugation step is proved here in full**.

The remaining equality `finrank_{L ⊗ K(C), via id_L ⊗ f}(L ⊗ K(C)) = finrank_{K(C), via f} K(C)`
is the curve-free **base-change-of-finrank** content; it is **proved here in full** as
`finrankBaseChange`, by realizing the `f`-twisted self-module `K(C)` as the type synonym `Twist f`
and exhibiting `(L ⊗ K(C)) ⊗_{K(C)} Twist f ≃ₗ[L ⊗ K(C)] Twist (id_L ⊗ f)` (so
`Module.finrank_baseChange` applies).  Hence `baseChangePullback_finrank_eq` (and the degree
preservation it feeds) carries **no** finrank hypothesis.

## What this file discharges for `OneSubScalingData`

`mkOneSubScalingDataConcrete` assembles a full `OneSubScalingData` for the genuine `1 − π` base
change in which:

* `pullback_L` is **constructed** as the concrete `oneSubFrobeniusPullback_L` (the conjugate
  `Φ ∘ (id_L ⊗ (1−π).pullback) ∘ Φ⁻¹`) — *no longer a raw input* (axiom-clean);
* `hdeg_bc` is **fully discharged** by the proved conjugation step
  `finrank_baseChangePullback_eq_finrank_lTensorMap` chained with the proved curve-free
  `finrankBaseChange` — no carried hypothesis.

The remaining inputs are exactly the genuinely-deep **K̄-level geometric** residuals, each stated
against the concrete pullback:

* `finiteKer` — finiteness of `ker(1 − π)_{K̄}` (a separable isogeny has finite kernel over `K̄`);
* `hproj` — `ProjOrdTransport` (multiplicity-free divisor pullback);
* `δ`/`hdc` — the divisor-pushforward dual `1 − V̄` and Silverman III.6.2(a) `δ ∘ φ = [#ker φ]`;
* `hsurj` — surjectivity over `K̄` (Silverman III.4.10a);
* `hkerdeg` — the separable degree match `#ker = deg` (Silverman III.4.10c);
* `hcomm'` — the translation covariance (Silverman III.8.2).

These are the genuine geometric content of the base-changed separable isogeny; the project ships no
concrete base-change of a non-Frobenius isogeny's *point map* (only the witness-parametric
`mkBaseChange`), so they remain carried (cf. `ProjOrdTransport`/`Naturality` elsewhere).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.11 (degree under base change),
  III.4.10a/c, III.6.2(a), III.8.2, III.8.6.1.
-/

open WeierstrassCurve HasseWeil.Curves
open scoped TensorProduct

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.DivisorPullback HasseWeil.WeilPairing.TorsionGeometric

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-- `Twist f` is the ring `B` carrying the `f`-twisted `B`-module structure (`b • x = f b * x`),
for an algebra endomorphism `f : B →ₐ[R] B`.  A *type synonym* of `B` so the twisted module
structure does not shadow the canonical instances on `B`. -/
def Twist {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B] (_f : B →ₐ[R] B) := B

namespace Twist
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (f : B →ₐ[R] B)

/-- Identification `Twist f → B` (the synonym is definitionally `B`). -/
def toB (x : Twist f) : B := x
lemma toB_injective : Function.Injective (toB f) := fun _ _ h ↦ h
/-- Build an element of `Twist f` from `B`. -/
def ofB (x : B) : Twist f := x
@[simp] lemma toB_ofB (x : B) : toB f (ofB f x) = x := rfl

instance : AddCommGroup (Twist f) := inferInstanceAs (AddCommGroup B)

/-- The `f`-twisted `B`-module on `Twist f`: `b • x = f b * x`. -/
noncomputable instance instModule : Module B (Twist f) :=
  RingHom.toModule (R := B) (S := B) f.toRingHom

@[simp] lemma smul_toB (b : B) (x : Twist f) : toB f (b • x) = f b * toB f x := rfl
@[simp] lemma toB_add (x y : Twist f) : toB f (x + y) = toB f x + toB f y := rfl
@[simp] lemma ofB_add (x y : B) : ofB f (x + y) = ofB f x + ofB f y := rfl

/-- The `S`-action on `Twist f` (for a scalar `s : S` acting through `S → B`), via the `B`-action. -/
lemma smul_toB_of_algebra {S : Type*} [CommRing S] [Algebra S B] [Module S (Twist f)]
    [IsScalarTower S B (Twist f)] (s : S) (x : Twist f) :
    toB f (s • x) = f (algebraMap S B s) * toB f x := by
  rw [show s • x = (algebraMap S B s) • x by rw [algebraMap_smul], smul_toB]

/-- The `R`-module on `Twist f`, restriction of the twisted `B`-module along `R → B`. -/
noncomputable instance instModuleR : Module R (Twist f) := Module.compHom (Twist f) (algebraMap R B)

@[simp] lemma smul_toB_R (c : R) (x : Twist f) :
    toB f (c • x) = f (algebraMap R B c) * toB f x := rfl

/-- `ofB` packaged as an `R`-linear map `B → Twist f` (works since `f` fixes the image of `R`). -/
noncomputable def ofBₗ : B →ₗ[R] Twist f where
  toFun := ofB f
  map_add' := ofB_add f
  map_smul' c x := by
    apply toB_injective f
    rw [RingHom.id_apply, toB_ofB, smul_toB_R, toB_ofB, Algebra.smul_def, AlgHom.commutes]

instance : IsScalarTower R B (Twist f) :=
  ⟨fun c a x ↦ by
    rw [show c • (a • x) = (algebraMap R B c) • (a • x) from rfl, smul_smul]
    change (c • a) • x = (algebraMap R B c * a) • x
    rw [Algebra.smul_def]⟩

noncomputable instance instFree {R B : Type*} [Field R] [Field B] [Algebra R B] (f : B →ₐ[R] B) :
    Module.Free B (Twist f) := Module.Free.of_divisionRing B (Twist f)

end Twist

section TwistLTensor

variable {F A L : Type*} [Field F] [Field A] [Algebra F A] [Field L] [Algebra F L]
  (f : A →ₐ[F] A)

local notation "lTM" => Algebra.TensorProduct.map (AlgHom.id L L) f

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `eFwd` is surjective, from its action on pure tensors (`heFwd`) and the section `eInv`
(`heInv`).  Stated with the forward/inverse maps as opaque parameters so it elaborates within the
default heartbeat budget. -/
private theorem twistLTensor_surjective [Module A (Twist (lTM))]
    [IsScalarTower A (L ⊗[F] A) (Twist (lTM))]
    (eFwd : ((L ⊗[F] A) ⊗[A] (Twist f)) →ₗ[L ⊗[F] A] (Twist (lTM)))
    (eInv : (L ⊗[F] A) →ₗ[F] ((L ⊗[F] A) ⊗[A] (Twist f)))
    (heFwd : ∀ (w : L ⊗[F] A) (m : Twist f),
      Twist.toB (lTM) (eFwd (w ⊗ₜ[A] m)) = lTM w * (1 ⊗ₜ[F] Twist.toB f m))
    (heInv : ∀ (s : L) (a : A),
      eInv (s ⊗ₜ[F] a) = (s ⊗ₜ[F] (1 : A)) ⊗ₜ[A] (Twist.ofB f a)) :
    Function.Surjective eFwd := by
  intro z
  refine ⟨eInv (Twist.toB (lTM) z), ?_⟩
  apply Twist.toB_injective (lTM)
  induction (Twist.toB (lTM) z) with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy =>
      rw [map_add, map_add, Twist.toB_add]
      rw [show Twist.toB (lTM) (eFwd (eInv x)) = x from hx,
        show Twist.toB (lTM) (eFwd (eInv y)) = y from hy]
  | tmul s a =>
      rw [heInv, heFwd]
      change lTM (s ⊗ₜ[F] 1) * (1 ⊗ₜ[F] Twist.toB f (Twist.ofB f a)) = s ⊗ₜ[F] a
      rw [Twist.toB_ofB, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, map_one,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- `eInv ∘ toB ∘ eFwd = id`, from the action on pure tensors.  The left inverse, giving
injectivity of `eFwd`.  Forward/inverse maps are opaque parameters for heartbeat budget. -/
private theorem twistLTensor_leftInverse [Module A (Twist (lTM))]
    [IsScalarTower A (L ⊗[F] A) (Twist (lTM))]
    (eFwd : ((L ⊗[F] A) ⊗[A] (Twist f)) →ₗ[L ⊗[F] A] (Twist (lTM)))
    (eInv : (L ⊗[F] A) →ₗ[F] ((L ⊗[F] A) ⊗[A] (Twist f)))
    (heFwd : ∀ (w : L ⊗[F] A) (m : Twist f),
      Twist.toB (lTM) (eFwd (w ⊗ₜ[A] m)) = lTM w * (1 ⊗ₜ[F] Twist.toB f m))
    (heInv : ∀ (s : L) (a : A),
      eInv (s ⊗ₜ[F] a) = (s ⊗ₜ[F] (1 : A)) ⊗ₜ[A] (Twist.ofB f a)) :
    ∀ t : (L ⊗[F] A) ⊗[A] (Twist f), eInv (Twist.toB (lTM) (eFwd t)) = t := by
  intro t
  induction t with
  | zero => rw [map_zero (f := eFwd), show Twist.toB (lTM) 0 = 0 from rfl,
      map_zero (f := eInv)]
  | add x y hx hy => rw [map_add (f := eFwd), Twist.toB_add, map_add (f := eInv), hx, hy]
  | tmul w m =>
      induction w with
      | zero =>
          rw [TensorProduct.zero_tmul, map_zero (f := eFwd),
            show Twist.toB (lTM) 0 = 0 from rfl, map_zero (f := eInv)]
      | add x y hx hy =>
          rw [TensorProduct.add_tmul, map_add (f := eFwd), Twist.toB_add, map_add (f := eInv),
            hx, hy]
      | tmul s a =>
          have heq : Twist.toB (lTM) (eFwd ((s ⊗ₜ[F] a) ⊗ₜ[A] m)) =
              (s ⊗ₜ[F] (f a * Twist.toB f m) : L ⊗[F] A) := by
            rw [heFwd, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
          rw [heq, heInv]
          rw [show Twist.ofB f (f a * Twist.toB f m) = a • m by
            apply Twist.toB_injective f
            rw [Twist.toB_ofB, Twist.smul_toB]]
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          congr 1
          change a • (s ⊗ₜ[F] (1 : A)) = s ⊗ₜ[F] a
          rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Curve-free base-change-of-finrank heart: for a field endomorphism `f : A →ₐ[F] A` and a field
extension `F → L`, the `(L ⊗ A)`-module finrank of `L ⊗ A` via the scalar extension `id_L ⊗ f`
equals the `A`-module finrank of `A` via `f`.  Proved by exhibiting the `L ⊗ A`-linear equivalence
`(L ⊗ A) ⊗_A (Twist f) ≃ₗ Twist (id_L ⊗ f)` and `Module.finrank_baseChange`. -/
private theorem finrank_lTensorMap_eq_finrank :
    @Module.finrank (L ⊗[F] A) (L ⊗[F] A) _ _ (lTM).toRingHom.toAlgebra.toModule =
      @Module.finrank A A _ _ f.toRingHom.toAlgebra.toModule := by
  letI iA_TwL : Module A (Twist (lTM)) :=
    Module.compHom (Twist (lTM)) (algebraMap A (L ⊗[F] A))
  haveI iA_TwL_tower : IsScalarTower A (L ⊗[F] A) (Twist (lTM)) :=
    SMul.comp.isScalarTower (algebraMap A (L ⊗[F] A))
  let l : (Twist f) →ₗ[A] (Twist (lTM)) :=
    { toFun := fun m ↦ Twist.ofB (lTM) (1 ⊗ₜ[F] Twist.toB f m)
      map_add' := fun x y ↦ by
        apply Twist.toB_injective (lTM)
        simp only [Twist.toB_ofB, Twist.toB_add, Twist.toB_ofB, TensorProduct.tmul_add]
      map_smul' := fun a m ↦ by
        apply Twist.toB_injective (lTM)
        rw [RingHom.id_apply]
        rw [show Twist.toB (lTM) (a • Twist.ofB (lTM) (1 ⊗ₜ[F] Twist.toB f m)) =
            lTM (algebraMap A (L ⊗[F] A) a) *
              Twist.toB (lTM) (Twist.ofB (lTM) (1 ⊗ₜ[F] Twist.toB f m))
            from Twist.smul_toB_of_algebra (lTM) a _]
        rw [Twist.toB_ofB, Twist.toB_ofB, Twist.smul_toB]
        change (1 : L) ⊗ₜ[F] (f a * Twist.toB f m) = lTM (1 ⊗ₜ[F] a) * (1 ⊗ₜ[F] Twist.toB f m)
        rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul] }
  let eFwd : ((L ⊗[F] A) ⊗[A] (Twist f)) →ₗ[L ⊗[F] A] (Twist (lTM)) :=
    l.liftBaseChange (L ⊗[F] A)
  have heFwd : ∀ (w : L ⊗[F] A) (m : Twist f),
      Twist.toB (lTM) (eFwd (w ⊗ₜ[A] m)) = lTM w * (1 ⊗ₜ[F] Twist.toB f m) := by
    intro w m
    change Twist.toB (lTM) (w • l m) = _
    rw [Twist.smul_toB]
    rfl
  let bil : L →ₗ[F] A →ₗ[F] ((L ⊗[F] A) ⊗[A] (Twist f)) :=
    { toFun := fun s ↦
        (TensorProduct.mk A (L ⊗[F] A) (Twist f) (s ⊗ₜ[F] (1 : A))).restrictScalars F ∘ₗ
          (Twist.ofBₗ f)
      map_add' := fun s t ↦ by
        ext a
        simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
          TensorProduct.mk_apply, LinearMap.add_apply]
        rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
      map_smul' := fun c s ↦ by
        ext a
        simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
          TensorProduct.mk_apply, RingHom.id_apply, LinearMap.smul_apply]
        rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul'] }
  let eInv : (L ⊗[F] A) →ₗ[F] ((L ⊗[F] A) ⊗[A] (Twist f)) := TensorProduct.lift bil
  have heInv : ∀ (s : L) (a : A),
      eInv (s ⊗ₜ[F] a) = (s ⊗ₜ[F] (1 : A)) ⊗ₜ[A] (Twist.ofB f a) :=
    fun s a ↦ by
    change TensorProduct.lift bil (s ⊗ₜ[F] a) = _
    rw [TensorProduct.lift.tmul]
    rfl
  clear_value eFwd eInv
  have hinj : Function.Injective eFwd := fun x y hxy ↦ by
    rw [← twistLTensor_leftInverse f eFwd eInv heFwd heInv x,
      ← twistLTensor_leftInverse f eFwd eInv heFwd heInv y, hxy]
  let eLA : ((L ⊗[F] A) ⊗[A] (Twist f)) ≃ₗ[L ⊗[F] A] (Twist (lTM)) :=
    LinearEquiv.ofBijective eFwd ⟨hinj, twistLTensor_surjective f eFwd eInv heFwd heInv⟩
  have key : @Module.finrank (L ⊗[F] A) (Twist (lTM)) _ _ _ =
      @Module.finrank A (Twist f) _ _ _ := by
    rw [← eLA.finrank_eq]
    exact Module.finrank_baseChange
  exact key

end TwistLTensor

namespace IsogenyBaseChangeConcrete

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)
variable (L : Type*) [Field L] [Algebra F L] [Algebra.IsAlgebraic F L]

/-- **The function-field scalar-extension iso** `Φ : (L ⊗_F K(C)) ≃ₐ[L] K(C_L)`, the composite of
`functionField_tensor_locBaseChange` (`L ⊗ K(C) ≅ FractionRing (L ⊗ C.CR)`) and
`functionField_baseChange_fracEquiv` (`FractionRing (L ⊗ C.CR) ≅ K(C_L)`).  Both are shipped
axiom-clean in `CurveMapBaseChange.lean`. -/
noncomputable def tensorFunctionFieldEquiv :
    letI := C.isDomain_tensorCoordRing L
    (L ⊗[F] C.toAffine.FunctionField) ≃ₐ[L] (C.baseChange L).toAffine.FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  (C.functionField_tensor_locBaseChange L).trans (C.functionField_baseChange_fracEquiv L)

/-- **The `L`-linear scalar extension `id_L ⊗ f`** of an `F`-algebra hom `f : K(C) →ₐ[F] K(C)`:
`Algebra.TensorProduct.map (AlgHom.id L) f : (L ⊗_F K(C)) →ₐ[L] (L ⊗_F K(C))`.  It is `L`-linear by
`Algebra.TensorProduct.map` (the left factor is the `L`-algebra identity). -/
noncomputable def lTensorMap (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    (L ⊗[F] C.toAffine.FunctionField) →ₐ[L] (L ⊗[F] C.toAffine.FunctionField) :=
  Algebra.TensorProduct.map (AlgHom.id L L) f

@[simp] theorem lTensorMap_tmul
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) (l : L)
    (u : C.toAffine.FunctionField) :
    lTensorMap C L f (l ⊗ₜ u) = l ⊗ₜ f u := by
  simp [lTensorMap]

/-- **The base-changed pullback** `baseChangePullback f : K(C_L) →ₐ[L] K(C_L)`, the conjugate
`Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹` of the scalar extension `id_L ⊗ f` by the function-field iso `Φ`.

This is the honest base-change of the function-field hom `f` along `F → L`, requiring **no**
`CoordHom`.  It is an `L`-algebra hom by construction (composite of `L`-algebra homs). -/
noncomputable def baseChangePullback
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    (C.baseChange L).toAffine.FunctionField →ₐ[L] (C.baseChange L).toAffine.FunctionField :=
  letI := C.isDomain_tensorCoordRing L
  (tensorFunctionFieldEquiv C L).toAlgHom.comp
    ((lTensorMap C L f).comp (tensorFunctionFieldEquiv C L).symm.toAlgHom)

theorem baseChangePullback_apply
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField)
    (z : (C.baseChange L).toAffine.FunctionField) :
    baseChangePullback C L f z =
      tensorFunctionFieldEquiv C L (lTensorMap C L f
        ((tensorFunctionFieldEquiv C L).symm z)) :=
  rfl

/-- `Φ⁻¹ ∘ (baseChangePullback f) = (id_L ⊗ f) ∘ Φ⁻¹`: the conjugation identity at the function-field
level (the algebra-map compatibility square feeding `Algebra.finrank_eq_of_equiv_equiv`). -/
theorem symm_comp_baseChangePullback
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField)
    (z : (C.baseChange L).toAffine.FunctionField) :
    (tensorFunctionFieldEquiv C L).symm (baseChangePullback C L f z) =
      lTensorMap C L f ((tensorFunctionFieldEquiv C L).symm z) := by
  rw [baseChangePullback_apply, AlgEquiv.symm_apply_apply]

/-- **Conjugation step (proved)**: the `K(C_L)`-module finrank of `K(C_L)` via the conjugate
`baseChangePullback f` equals the `L ⊗ K(C)`-module finrank of `L ⊗ K(C)` via the scalar extension
`id_L ⊗ f`.  Proved by `Algebra.finrank_eq_of_equiv_equiv` with `i = j = Φ⁻¹`, whose compatibility
square is the conjugation identity `symm_comp_baseChangePullback`. -/
theorem finrank_baseChangePullback_eq_finrank_lTensorMap
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    @Module.finrank (C.baseChange L).toAffine.FunctionField
        (C.baseChange L).toAffine.FunctionField _ _
        (baseChangePullback C L f).toRingHom.toAlgebra.toModule =
      @Module.finrank (L ⊗[F] C.toAffine.FunctionField) (L ⊗[F] C.toAffine.FunctionField) _ _
        (lTensorMap C L f).toRingHom.toAlgebra.toModule := by
  letI := C.isDomain_tensorCoordRing L
  letI algBcp : Algebra (C.baseChange L).toAffine.FunctionField
      (C.baseChange L).toAffine.FunctionField := (baseChangePullback C L f).toRingHom.toAlgebra
  letI algLt : Algebra (L ⊗[F] C.toAffine.FunctionField) (L ⊗[F] C.toAffine.FunctionField) :=
    (lTensorMap C L f).toRingHom.toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (tensorFunctionFieldEquiv C L).symm.toRingEquiv
    (tensorFunctionFieldEquiv C L).symm.toRingEquiv ?_
  ext z
  change lTensorMap C L f ((tensorFunctionFieldEquiv C L).symm z) =
    (tensorFunctionFieldEquiv C L).symm (baseChangePullback C L f z)
  exact (symm_comp_baseChangePullback C L f z).symm

/-- **The base-change-of-finrank content** (curve-free): the `L ⊗ K(C)`-module finrank of
`L ⊗ K(C)` via the scalar extension `id_L ⊗ f` equals the `K(C)`-module finrank of `K(C)` via `f`.

Base change along `F → L` preserves the degree `[K(C) : f(K(C))]` of the (injective, possibly
non-surjective) field endomorphism `f`.  This `Prop` is **proved** by `finrankBaseChange` below
(via the `Twist` synonym and `Module.finrank_baseChange`); it remains a named `Prop` only to keep
the statement of `FinrankBaseChange`/`finrankBaseChange` readable. -/
def FinrankBaseChange (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) : Prop :=
  @Module.finrank (L ⊗[F] C.toAffine.FunctionField) (L ⊗[F] C.toAffine.FunctionField) _ _
      (lTensorMap C L f).toRingHom.toAlgebra.toModule =
    @Module.finrank C.toAffine.FunctionField C.toAffine.FunctionField _ _
      f.toRingHom.toAlgebra.toModule

/-- **The base-change-of-finrank fact, proved (curve-free).**  For an `F`-algebra endomorphism `f`
of the field `K(C)`, base change along `F → L` preserves the degree of the (injective) field
endomorphism: `[L ⊗ K(C) : (id_L ⊗ f)(L ⊗ K(C))] = [K(C) : f(K(C))]`. -/
theorem finrankBaseChange
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    FinrankBaseChange C L f :=
  finrank_lTensorMap_eq_finrank f

/-- **Degree preservation of `baseChangePullback`** (curve-free).  The conjugation step is the proved
`finrank_baseChangePullback_eq_finrank_lTensorMap`; chaining with the now-proved `finrankBaseChange`
gives the finrank equality `Isogeny.degree_eq_of_finrank_eq` consumes. -/
theorem baseChangePullback_finrank_eq
    (f : C.toAffine.FunctionField →ₐ[F] C.toAffine.FunctionField) :
    @Module.finrank (C.baseChange L).toAffine.FunctionField
        (C.baseChange L).toAffine.FunctionField _ _
        (baseChangePullback C L f).toRingHom.toAlgebra.toModule =
      @Module.finrank C.toAffine.FunctionField C.toAffine.FunctionField _ _
        f.toRingHom.toAlgebra.toModule :=
  (finrank_baseChangePullback_eq_finrank_lTensorMap C L f).trans (finrankBaseChange C L f)

end IsogenyBaseChangeConcrete

section OneSub

open IsogenyBaseChangeConcrete

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L] [ExpChar L p]
  [(W.baseChange L).toAffine.IsElliptic]

/-- **The concrete base-changed pullback of `1 − π`** (CoordHom-free): the conjugate
`Φ ∘ (id_L ⊗ (1 − π).pullback) ∘ Φ⁻¹`.  This is the `pullback_L` field for `OneSubScalingData`. -/
noncomputable def oneSubFrobeniusPullback_L (hq : 2 ≤ Fintype.card K) :
    (W.baseChange L).toAffine.FunctionField →ₐ[L] (W.baseChange L).toAffine.FunctionField :=
  baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L (isogOneSub_negFrobenius W hq).pullback

/-- **Degree preservation for the concrete `1 − π` base change** (curve-free, fully discharged).
Chains the proved conjugation step (inside `baseChangePullback_finrank_eq`, which now invokes the
proved `finrankBaseChange`) into the shipped witness-parametric
`oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank`.  This **discharges the `hdeg_bc` field** of
`OneSubScalingData` with no carried `FinrankBaseChange` hypothesis. -/
theorem oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange (hq : 2 ≤ Fintype.card K) :
    (oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).degree =
      (isogOneSub_negFrobenius W hq).degree :=
  oneSubFrobeniusIsogBaseChange_degree_eq_of_finrank W p r L hq (oneSubFrobeniusPullback_L W L hq)
    (baseChangePullback_finrank_eq (⟨W.toAffine⟩ : SmoothPlaneCurve K) L
      (isogOneSub_negFrobenius W hq).pullback)

variable [IsAlgClosed L]
  [IsIntegrallyClosed (⟨(W.baseChange L).toAffine⟩ : SmoothPlaneCurve L).CoordinateRing]

/-- **Assemble `OneSubScalingData` with concrete `pullback_L` and discharged `hdeg_bc`.**  The
degree-preservation field `hdeg_bc` is discharged with **no** finrank hypothesis (the curve-free
`finrankBaseChange` is proved); the only inputs are the genuinely-deep K̄-level residuals against the
concrete pullback `oneSubFrobeniusPullback_L`.  Produces the full bundled `OneSubScalingData` that
`oneSubFrobeniusScaling_of_data` consumes. -/
noncomputable def mkOneSubScalingDataConcrete (hq : 2 ≤ Fintype.card K)
    (finiteKer :
      Finite (oneSubFrobeniusIsogBaseChange W p r L
        (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom.ker)
    (hproj : ProjOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)))
    (δ : (W.baseChange L).toAffine.Point →+ (W.baseChange L).toAffine.Point)
    (hdc :
      δ.comp (oneSubFrobeniusIsogBaseChange W p r L
          (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom =
        (mulByInt (W.baseChange L).toAffine
          (Nat.card (oneSubFrobeniusIsogBaseChange W p r L
            (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom.ker : ℤ)).toAddMonoidHom)
    (hsurj : Function.Surjective
      (oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom)
    (hkerdeg :
      Nat.card (oneSubFrobeniusIsogBaseChange W p r L
          (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom.ker =
        (oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).degree)
    (hcomm' :
      ∀ (ℓ : ℕ) (hℓF : (ℓ : L) ≠ 0)
        (S T : (W.baseChange L).toAffine.Point)
        (_hS : ((ℓ : ℕ) : ℤ) • S = 0)
        (hφT : ((ℓ : ℕ) : ℤ) •
          (oneSubFrobeniusIsogBaseChange W p r L
            (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom T = 0),
        translateAlgEquivOfPoint (W.baseChange L) S
            ((oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).pullback
              (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r L
                  (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom T) hφT)) =
          (oneSubFrobeniusIsogBaseChange W p r L (oneSubFrobeniusPullback_L W L hq)).pullback
            (translateAlgEquivOfPoint (W.baseChange L)
              ((oneSubFrobeniusIsogBaseChange W p r L
                (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom S)
              (weilFunction (W.baseChange L) ((ℓ : ℕ) : ℤ) (by exact_mod_cast hℓF)
                ((oneSubFrobeniusIsogBaseChange W p r L
                  (oneSubFrobeniusPullback_L W L hq)).toAddMonoidHom T) hφT))) :
    OneSubScalingData W p r L hq where
  pullback_L := oneSubFrobeniusPullback_L W L hq
  finiteKer := finiteKer
  hdeg_bc := oneSubFrobeniusIsogBaseChange_degree_eq_of_finrankBaseChange W p r L hq
  hproj := hproj
  δ := δ
  hdc := hdc
  hsurj := hsurj
  hkerdeg := hkerdeg
  hcomm' := hcomm'

end OneSub

end HasseWeil.WeilPairing
