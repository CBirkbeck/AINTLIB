/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.InvariantDifferentialPullback
import HasseWeil.WeilPairing.WallAGenericRealization
import HasseWeil.WeilPairing.IsogenyBaseChangeConcrete

/-!
# Base change of the invariant-differential pullback coefficient (Silverman III.5)

For a smooth plane curve `C / F` and an `F`-algebra extension `L`, the concrete base-changed
function-field pullback `baseChangePullback f := Φ ∘ (id_L ⊗ f) ∘ Φ⁻¹`
(`IsogenyBaseChangeConcrete`, CoordHom-free) carries the omega-based pullback coefficient
**by value** across base change:

  `omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`

whenever `α_L.pullback = baseChangePullback α.pullback`.  This is the differential analogue of the
**degree** base change `baseChangePullback_finrank_eq` (`finrankBaseChange`); together they say that
both the degree and the (in)separability of an isogeny are stable under base change.

## The differential transport map

The proof builds the natural base-change map on Kähler differentials,

  `diffMap := KaehlerDifferential.map K L K(E) K(E_L) : Ω[K(E)/K] →ₗ[K(E)] Ω[K(E_L)/L]`,

for the square `K → K(E)`, `L → K(E_L)`, with `algebraMap K(E) K(E_L) = functionFieldMap`
(the `K`-algebra hom `functionField_baseChange`).  It satisfies:

* `diffMap (D_K z) = D_L (functionFieldMap z)` (`KaehlerDifferential.map_D`);
* `diffMap (s • ω) = s • diffMap ω` (`K(E)`-linearity);
* `diffMap (ω_K) = ω_L` (the invariant differential transports — `x_gen`, `y_gen`, `a₁`, `a₃` all
  base-change, `diffMap_invariantDifferential`);
* `diffMap ∘ α.pullbackKaehler = α_L.pullbackKaehler ∘ diffMap` (`diffMap_pullbackKaehler`), whose
  generator step is exactly the intertwining `baseChangePullback (functionFieldMap z) =
  functionFieldMap (α.pullback z)` (`baseChangePullback_functionFieldMap`).

Reading these through `pullbackKaehler_invariantDifferential` (`α^*ω = a_α·ω`) and uniqueness of the
omega coefficient gives the value transport.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.5.2, III.5.3, III.5.5.
-/

open WeierstrassCurve HasseWeil.Curves
open scoped TensorProduct

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (L : Type*) [Field L] [DecidableEq L] [Algebra K L] [Algebra.IsAlgebraic K L]
  [(W.baseChange L).toAffine.IsElliptic]

/-! ### The algebra `K(E) → K(E_L)` and the square instances for `KaehlerDifferential.map` -/

/-- The `K(E)`-algebra structure on `K(E_L)` via the function-field base-change `K`-algebra hom
`functionField_baseChange` (so `algebraMap K(E) K(E_L) = functionFieldMap`). -/
noncomputable scoped instance algFunctionFieldBaseChange :
    Algebra W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField :=
  ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionField_baseChange L).toAlgebra

/-- `algebraMap K(E) K(E_L) = functionFieldMap` (definitional via `functionField_baseChange`). -/
theorem algebraMap_functionField_baseChange_eq (z : W.toAffine.FunctionField) :
    algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z := rfl

/-- The bottom-left/top tower `K → K(E) → K(E_L)` (the `K`-algebra hom `functionField_baseChange`
factors `K → K(E_L)` through `K → K(E)`). -/
noncomputable scoped instance towerFunctionFieldBaseChange :
    IsScalarTower K W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap K (W.baseChange L).toAffine.FunctionField k =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (algebraMap K W.toAffine.FunctionField k)
    rw [SmoothPlaneCurve.functionFieldMap_algebraMap_F]
    rfl

set_option synthInstance.maxHeartbeats 1000000 in
/-- `SMulCommClass L K(E) K(E_L)`: both act by multiplication in the commutative ring `K(E_L)`. -/
noncomputable scoped instance smulCommFunctionFieldBaseChange :
    SMulCommClass L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField where
  smul_comm l s b := by
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring

/-! ### The differential transport map `diffMap : Ω[K(E)/K] → Ω[K(E_L)/L]` -/

/-- **The base-change map on Kähler differentials** `Ω[K(E)/K] →ₗ[K(E)] Ω[K(E_L)/L]`, for the
square `K → K(E)`, `L → K(E_L)` with `algebraMap K(E) K(E_L) = functionFieldMap`. -/
noncomputable def omegaDiffMap :
    KaehlerDifferential K W.toAffine.FunctionField →ₗ[W.toAffine.FunctionField]
      KaehlerDifferential L (W.baseChange L).toAffine.FunctionField :=
  KaehlerDifferential.map K L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField

/-- `omegaDiffMap (D_K z) = D_L (functionFieldMap z)` (`KaehlerDifferential.map_D`). -/
theorem omegaDiffMap_D (z : W.toAffine.FunctionField) :
    omegaDiffMap W L (KaehlerDifferential.D K W.toAffine.FunctionField z) =
      KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
        (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z) :=
  KaehlerDifferential.map_D K L W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField z

/-- `omegaDiffMap (s • ω) = s • omegaDiffMap ω` (`K(E)`-linearity, the `K(E)`-action on `Ω[K(E_L)/L]`
factoring through `functionFieldMap`). -/
theorem omegaDiffMap_smul (s : W.toAffine.FunctionField) (ω : KaehlerDifferential K W.toAffine.FunctionField) :
    omegaDiffMap W L (s • ω) = s • omegaDiffMap W L ω :=
  LinearMap.map_smul (omegaDiffMap W L) s ω

/-- **`functionFieldMap` intertwines `α.pullback` with `α_L.pullback`** for a base-changed isogeny,
i.e. the function-field shadow of `α_L = α` over `L` (`baseChangePullback_functionFieldMap`). -/
theorem functionFieldMap_pullback
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback)
    (z : W.toAffine.FunctionField) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (α.pullback z) =
      α_L.pullback ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z) := by
  rw [hpb]
  exact (baseChangePullback_functionFieldMap (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback z).symm

/-- **Pullback compatibility**: `omegaDiffMap ∘ α.pullbackKaehler = α_L.pullbackKaehler ∘ omegaDiffMap`
for a base-changed isogeny `α_L` whose pullback is `baseChangePullback α.pullback`.  Proved by span
induction over the generators `D_K z`; the generator step is exactly `functionFieldMap_pullback`. -/
theorem omegaDiffMap_pullbackKaehler
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback)
    (ω : KaehlerDifferential K W.toAffine.FunctionField) :
    omegaDiffMap W L (α.pullbackKaehler ω) = α_L.pullbackKaehler (omegaDiffMap W L ω) := by
  have hω : ω ∈ Submodule.span W.toAffine.FunctionField
      (Set.range (KaehlerDifferential.D K W.toAffine.FunctionField)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [Isogeny.pullbackKaehler_D, omegaDiffMap_D, omegaDiffMap_D, Isogeny.pullbackKaehler_D]
    congr 1
    rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq]
    exact functionFieldMap_pullback W L α α_L hpb z
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul s x _ hx =>
    rw [Isogeny.pullbackKaehler_smul_KE, omegaDiffMap_smul, hx, omegaDiffMap_smul]
    rw [show (α.pullback s) • α_L.pullbackKaehler (omegaDiffMap W L x) =
        algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (α.pullback s) •
          α_L.pullbackKaehler (omegaDiffMap W L x) from (algebraMap_smul _ _ _).symm,
      show s • omegaDiffMap W L x =
        algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField s •
          omegaDiffMap W L x from (algebraMap_smul _ _ _).symm]
    rw [Isogeny.pullbackKaehler_smul_KE]
    congr 1
    rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq]
    exact functionFieldMap_pullback W L α α_L hpb s

set_option synthInstance.maxHeartbeats 1000000 in
/-- **`functionFieldMap (u_gen) = u_gen` over `L`** (the invariant-differential denominator
`u = 2y + a₁x + a₃` base-changes, since `x_gen`, `y_gen`, `a₁`, `a₃` do). -/
theorem functionFieldMap_u_gen :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (u_gen W) = u_gen (W.baseChange L) := by
  have hx : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (x_gen W) = x_gen (W.baseChange L) :=
    functionFieldMap_x_gen W L
  have hy : (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (y_gen W) = y_gen (W.baseChange L) :=
    functionFieldMap_y_gen W L
  rw [show u_gen W = 2 * y_gen W + algebraMap K W.toAffine.FunctionField W.a₁ * x_gen W +
      algebraMap K W.toAffine.FunctionField W.a₃ from rfl]
  rw [show u_gen (W.baseChange L) = 2 * y_gen (W.baseChange L) +
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₁ * x_gen (W.baseChange L) +
      algebraMap L (W.baseChange L).toAffine.FunctionField (W.baseChange L).a₃ from rfl]
  rw [map_add, map_add, map_mul, map_mul, map_ofNat, hx, hy,
    SmoothPlaneCurve.functionFieldMap_algebraMap_F, SmoothPlaneCurve.functionFieldMap_algebraMap_F]
  congr 2

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The invariant differential transports**: `omegaDiffMap (ω_K) = ω_L`.  Both are
`u⁻¹ • D(x_gen)`, and `functionFieldMap` carries `u_gen ↦ u_gen` (`functionFieldMap_u_gen`) and
`x_gen ↦ x_gen` (`functionFieldMap_x_gen`). -/
theorem omegaDiffMap_invariantDifferential :
    omegaDiffMap W L (invariantDifferential W.toAffine) =
      invariantDifferential (W.baseChange L).toAffine := by
  rw [show invariantDifferential W.toAffine =
      (u_gen W)⁻¹ • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from rfl]
  rw [omegaDiffMap_smul, omegaDiffMap_D]
  rw [show invariantDifferential (W.baseChange L).toAffine =
      (u_gen (W.baseChange L))⁻¹ •
        KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField (x_gen (W.baseChange L))
      from rfl]
  rw [show (u_gen W)⁻¹ • KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
        (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (x_gen W)) =
      algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField ((u_gen W)⁻¹) •
        KaehlerDifferential.D L (W.baseChange L).toAffine.FunctionField
          (algebraMap W.toAffine.FunctionField (W.baseChange L).toAffine.FunctionField (x_gen W))
      from (algebraMap_smul _ _ _).symm]
  rw [algebraMap_functionField_baseChange_eq, algebraMap_functionField_baseChange_eq, map_inv₀,
    functionFieldMap_u_gen]
  congr 2
  rw [show x_gen W = algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) from rfl]
  exact functionFieldMap_x_gen W L

/-- **The omega-coefficient base-change transport (Silverman III.5)**: for a base-changed isogeny
`α_L` whose pullback is the concrete `baseChangePullback α.pullback`,

  `omegaPullbackCoeff (E_L) α_L = functionFieldMap (omegaPullbackCoeff E α)`.

The differential analogue of the degree base change `baseChangePullback_finrank_eq`.  Proof:
`a_{α_L} • ω_L = α_L^* ω_L = α_L^* (omegaDiffMap ω_K) = omegaDiffMap (α^* ω_K) =
omegaDiffMap (a_α • ω_K) = a_α • ω_L = functionFieldMap(a_α) • ω_L`, then uniqueness of the
omega coefficient. -/
theorem omegaPullbackCoeff_baseChangePullback
    (α : Isogeny W.toAffine W.toAffine)
    (α_L : Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine)
    (hpb : α_L.pullback = baseChangePullback (⟨W.toAffine⟩ : SmoothPlaneCurve K) L α.pullback) :
    omegaPullbackCoeff (W.baseChange L) α_L =
      (⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L (omegaPullbackCoeff W α) := by
  apply omegaPullbackCoeff_unique
  rw [← Isogeny.pullbackKaehler_invariantDifferential α_L,
    ← omegaDiffMap_invariantDifferential W L,
    ← omegaDiffMap_pullbackKaehler W L α α_L hpb,
    Isogeny.pullbackKaehler_invariantDifferential α,
    omegaDiffMap_smul, omegaDiffMap_invariantDifferential W L,
    ← algebraMap_functionField_baseChange_eq, algebraMap_smul]

end HasseWeil.WeilPairing
