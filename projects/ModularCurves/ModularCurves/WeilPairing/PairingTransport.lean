/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.FieldPairingDet
import ModularCurves.WeilPairing.GaloisFieldPairing

/-!
# The Weil pairing's transport core, across **two** fields (WP-D3c-2d)

`weilPairing_galois_core_of_algEquiv` (`WeilPairing/GaloisFunctionField.lean`) is the constant-
ratio computation behind every equivariance statement about the Weil pairing: from

* the conjugation law `Φ ∘ τ_S = τ_{S'} ∘ Φ` at `g_T`,
* the naturality of the Weil function up to a constant, `Φ g_T = c · g_{T'}`, and
* the constants law `Φ (algebraMap a) = algebraMap (σ₀ a)`,

it concludes `e(S', T') = σ₀ (e(S, T))`. It is stated with **one** field `F`, one curve, and
`Φ` an automorphism of that curve's function field, because the only consumer so far was the
`Gal(k̄/k)`-action, where the curve is `σ`-invariant.

The field-change naturality of the field-level pairing (WP-D3c step 2) needs the same
computation with a **source and a target** field: `σ₀ : F →+* F'`, curves `V / F` and `V' / F'`,
and `Φ : K(V) →+* K(V')`. That is `weilPairing_transport_core` below; the existing one-field
lemma is its `F' = F`, `V' = V` case (with `Φ` an equivalence, which the argument never uses).

Nothing in the proof needs `Φ` to be bijective, and nothing needs the two fields to be
related: the cancellation happens entirely in `K(V')`.
-/

universe v w

open WeierstrassCurve

namespace ModularCurves

/-- **(WP-D3c-2d)** The two-field transport core of the Weil pairing.

Given a ring map `σ₀ : F →+* F'` on the base fields and a ring map `Φ : K(V) →+* K(V')` on the
function fields which

* conjugates the translation by `S` into the translation by `S'` at `g_T` (`hconj`),
* carries `g_T` to a nonzero constant multiple of `g_{T'}` (`hnat`), and
* acts on the constants by `σ₀` (`hconst`),

the pairing at `(S', T')` is `σ₀` of the pairing at `(S, T)`.

The proof is the constant-ratio computation of `weilPairing_galois_core_of_algEquiv`, of which
this is the two-field generalisation: apply `Φ` to `τ_S g_T = e(S,T) · g_T`, rewrite the left
side by `hconj` and the right by `hconst`, substitute `Φ g_T = c · g_{T'}`, and cancel the
nonzero factor `c · g_{T'}` in `K(V')`. -/
theorem weilPairing_transport_core
    {F : Type v} [Field F] [DecidableEq F] [IsAlgClosed F] (V : WeierstrassCurve F)
    [V.toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).CoordinateRing]
    {F' : Type w} [Field F'] [DecidableEq F'] [IsAlgClosed F'] (V' : WeierstrassCurve F')
    [V'.toAffine.IsElliptic]
    [IsIntegrallyClosed (⟨V'.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F').CoordinateRing]
    (N : ℤ) (hN : (N : F) ≠ 0) (hN' : (N : F') ≠ 0) (σ₀ : F →+* F')
    (Φ : (⟨V.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F).FunctionField →+*
      (⟨V'.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F').FunctionField)
    (S T : V.toAffine.Point) (S' T' : V'.toAffine.Point)
    (hS : N • S = 0) (hT : N • T = 0) (hS' : N • S' = 0) (hT' : N • T' = 0)
    (hconj : Φ (HasseWeil.translateAlgEquivOfPoint V S
        (HasseWeil.WeilPairing.weilFunction V N hN T hT)) =
      HasseWeil.translateAlgEquivOfPoint V' S'
        (Φ (HasseWeil.WeilPairing.weilFunction V N hN T hT)))
    {c : F'} (hc : c ≠ 0)
    (hnat : Φ (HasseWeil.WeilPairing.weilFunction V N hN T hT) =
      algebraMap F' _ c * HasseWeil.WeilPairing.weilFunction V' N hN' T' hT')
    (hconst : ∀ a : F, Φ (algebraMap F _ a) = algebraMap F' _ (σ₀ a)) :
    HasseWeil.WeilPairing.weilPairing V' N hN' S' T' hS' hT' =
      σ₀ (HasseWeil.WeilPairing.weilPairing V N hN S T hS hT) := by
  set e := HasseWeil.WeilPairing.weilPairing V N hN S T hS hT
  set e' := HasseWeil.WeilPairing.weilPairing V' N hN' S' T' hS' hT'
  set gT := HasseWeil.WeilPairing.weilFunction V N hN T hT
  set gT' := HasseWeil.WeilPairing.weilFunction V' N hN' T' hT'
  have hgT'_ne : gT' ≠ 0 := HasseWeil.WeilPairing.weilFunction_ne_zero V' N hN' T' hT'
  have hc_ne : algebraMap F'
      (⟨V'.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F').FunctionField c ≠ 0 :=
    (map_ne_zero_iff (algebraMap F'
      (⟨V'.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve F').FunctionField)
      (algebraMap F' _).injective).mpr hc
  have hrel : Φ (HasseWeil.translateAlgEquivOfPoint V S gT) =
      Φ (algebraMap F _ e * gT) := by
    rw [HasseWeil.WeilPairing.weilPairing_translate V N hN S T hS hT]
  rw [hconj] at hrel
  rw [map_mul, hconst] at hrel
  rw [hnat] at hrel
  rw [map_mul, (HasseWeil.translateAlgEquivOfPoint V' S').commutes,
    HasseWeil.WeilPairing.weilPairing_translate V' N hN' S' T' hS' hT'] at hrel
  have hcancel : algebraMap F' _ e' * (algebraMap F' _ c * gT') =
      algebraMap F' _ (σ₀ e) * (algebraMap F' _ c * gT') := by
    rw [← hrel]; ring
  exact (algebraMap F' _).injective (mul_right_cancel₀ (mul_ne_zero hc_ne hgT'_ne) hcancel)

/-! ### The semilinear transport maps

The `Gal(k̄/k)`-machinery of `WeilPairing/GaloisFunctionField.lean` transports along a `k`-algebra
automorphism `σ : L ≃ₐ[k] L`, which lets it use mathlib's `Affine.Point.map` (defined for algebra
homomorphisms over a common base) directly. A field **isomorphism** `σ : F ≃+* F'` has no common
base, but there is a standard substitute: give `F'` the `F`-algebra structure `σ.toAlgebra`, under
which `algebraMap F F' = σ` and hence `V.baseChange F' = V.map σ` by definition. Every
algebra-based construction then applies verbatim. -/

section Transport

variable {F : Type v} [Field F] [DecidableEq F] {F' : Type v} [Field F'] [DecidableEq F']

/-- **(WP-D3c-2d)** The transport of affine points along a ring homomorphism of the base fields:
`(x, y) ↦ (σ x, σ y)`, an additive map to the `σ`-mapped curve.

This is mathlib's `Affine.Point.map` read through the `F`-algebra structure `σ.toAlgebra` on `F'`,
for which `V.baseChange F' = V.map σ` holds by definition. -/
noncomputable def pointMapOfRingHom (V : WeierstrassCurve F) (σ : F →+* F') :
    V.toAffine.Point →+ (V.map σ).toAffine.Point :=
  letI : Algebra F F' := σ.toAlgebra
  WeierstrassCurve.Affine.Point.map (W' := V) (F := F) (K := F') (Algebra.ofId F F')

@[simp] theorem pointMapOfRingHom_zero (V : WeierstrassCurve F) (σ : F →+* F') :
    pointMapOfRingHom V σ 0 = 0 := rfl

@[simp] theorem pointMapOfRingHom_some (V : WeierstrassCurve F) (σ : F →+* F') {x y : F}
    (h : V.toAffine.Nonsingular x y) :
    pointMapOfRingHom V σ (WeierstrassCurve.Affine.Point.some x y h) =
      WeierstrassCurve.Affine.Point.some (σ x) (σ y)
        ((V.toAffine.map_nonsingular σ.injective x y).mpr h) :=
  rfl

theorem pointMapOfRingHom_injective (V : WeierstrassCurve F) (σ : F →+* F') :
    Function.Injective (pointMapOfRingHom V σ) :=
  letI : Algebra F F' := σ.toAlgebra
  WeierstrassCurve.Affine.Point.map_injective (W' := V) (f := Algebra.ofId F F')

theorem pointMapOfRingHom_surjective (V : WeierstrassCurve F) (e : F ≃+* F') :
    Function.Surjective (pointMapOfRingHom V (e : F →+* F')) := by
  rintro (_ | ⟨x', y', h'⟩)
  · exact ⟨0, rfl⟩
  · refine ⟨WeierstrassCurve.Affine.Point.some (e.symm x') (e.symm y')
      ((V.toAffine.map_nonsingular (f := (e : F →+* F')) (e : F →+* F').injective _ _).mp ?_), ?_⟩
    · rwa [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    · rw [pointMapOfRingHom_some]
      congr 1 <;> exact RingEquiv.apply_symm_apply e _

/-- **(WP-D3c-2d)** …and along a ring **equivalence** the transport is an additive
equivalence. -/
noncomputable def pointEquivOfRingEquiv (V : WeierstrassCurve F) (e : F ≃+* F') :
    V.toAffine.Point ≃+ (V.map (e : F →+* F')).toAffine.Point :=
  AddEquiv.ofBijective (pointMapOfRingHom V (e : F →+* F'))
    ⟨pointMapOfRingHom_injective V _, pointMapOfRingHom_surjective V e⟩

@[simp] theorem pointEquivOfRingEquiv_apply (V : WeierstrassCurve F) (e : F ≃+* F')
    (P : V.toAffine.Point) :
    pointEquivOfRingEquiv V e P = pointMapOfRingHom V (e : F →+* F') P := rfl

/-- **(WP-D3c-2d)** The coordinate-ring equivalence induced by a ring equivalence of the base
fields: `CoordinateRing.map` is bijective there (`coordRingMap_bijective_of_ringEquiv`). -/
noncomputable def coordRingEquivOfRingEquiv (V : WeierstrassCurve F) (e : F ≃+* F') :
    V.toAffine.CoordinateRing ≃+* (V.map (e : F →+* F')).toAffine.CoordinateRing :=
  RingEquiv.ofBijective _ (coordRingMap_bijective_of_ringEquiv V e)

omit [DecidableEq F] [DecidableEq F'] in
theorem coordRingEquivOfRingEquiv_toRingHom (V : WeierstrassCurve F) (e : F ≃+* F') :
    (coordRingEquivOfRingEquiv V e).toRingHom =
      WeierstrassCurve.Affine.CoordinateRing.map V.toAffine (e : F →+* F') := rfl

/-- **(WP-D3c-2d)** The function-field equivalence induced by a ring equivalence of the base
fields: `coordRingEquivOfRingEquiv` lifted to fraction fields. -/
noncomputable def functionFieldEquivOfRingEquiv (V : WeierstrassCurve F) [V.toAffine.IsElliptic]
    (e : F ≃+* F') [(V.map (e : F →+* F')).toAffine.IsElliptic] :
    V.toAffine.FunctionField ≃+* (V.map (e : F →+* F')).toAffine.FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv (coordRingEquivOfRingEquiv V e)

end Transport

/-! ### The root transforms by `det` — the Galois case

`hdet` (`WeilPairing/DetCocycle.lean`) asks for `ζ_a ^ det v = ζ_b ^ det w`, i.e. that the root of
unity attached to a trivialisation transforms by the determinant of the transition matrix. At the
field level and for a transition realised by a **Galois automorphism** of the geometric point that
re-marks the basis by `g`, that is now a two-line consequence of results already proved:
`fieldWeilPairing_galois` moves `σ` across the pairing and `fieldWeilPairing_gl2_zmod` evaluates the
re-marked pairing as the `det g`-th power.

This is the `Stab`-case of the determinant law: it needs no cross-field transport, because `σ`
is an automorphism of a single geometric point fixing the curve. -/

/-- **(WP-D3c-2g)** *The root transforms by `det`*, at the field level, for a Galois automorphism
`σ` of the geometric point which re-marks the basis `(P, Q)` by the matrix `g`:

`σ (e_N(P, Q)) = e_N(P, Q) ^ det g`.

`fieldWeilPairing_galois` turns the left side into `e_N(σP, σQ)`, the hypotheses rewrite that
pair as `g · (P, Q)`, and `fieldWeilPairing_gl2_zmod` evaluates it. -/
theorem fieldWeilPairing_det_of_galois {k : Type v} [Field k] (W : WeierstrassCurve k)
    {L : Type v} [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L]
    [(W.baseChange L).toAffine.IsElliptic] (σ : L ≃ₐ[k] L)
    (N : ℕ) [NeZero N] (hN : (N : L) ≠ 0)
    (P Q : (W.baseChange L).toAffine.Point)
    (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (g : Matrix (Fin 2) (Fin 2) (ZMod N))
    (hσP : galoisPointEquiv W σ P = (g 0 0).val • P + (g 0 1).val • Q)
    (hσQ : galoisPointEquiv W σ Q = (g 1 0).val • P + (g 1 1).val • Q) :
    σ (fieldWeilPairing (W.baseChange L) N hN P Q hP hQ : L) =
      (fieldWeilPairing (W.baseChange L) N hN P Q hP hQ : L) ^
        (g 0 0 * g 1 1 - g 0 1 * g 1 0).val := by
  have h₁ : (N : ℤ) • ((g 0 0).val • P + (g 0 1).val • Q) = 0 := by
    rw [← hσP]; exact zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hP
  have h₂ : (N : ℤ) • ((g 1 0).val • P + (g 1 1).val • Q) = 0 := by
    rw [← hσQ]; exact zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hQ
  rw [← fieldWeilPairing_gl2_zmod (W.baseChange L) N hN P Q hP hQ g h₁ h₂,
    ← fieldWeilPairing_congr (W.baseChange L) N hN
      (zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hP)
      (zsmul_galoisPointEquiv_eq_zero W σ (N : ℤ) hQ) h₁ h₂ hσP hσQ]
  exact (fieldWeilPairing_galois W σ N hN P Q hP hQ _ _).symm

end ModularCurves
