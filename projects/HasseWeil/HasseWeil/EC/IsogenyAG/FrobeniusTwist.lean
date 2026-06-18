/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Maps
import HasseWeil.EC.IsogenyAG
import HasseWeil.EC.IsogenyAG.MulByIntBasepoint
import HasseWeil.EC.IsogenyAG.DualReduction
import HasseWeil.GapQfKernel
import HasseWeil.GapSpines
import HasseWeil.IsogenyBaseChange

/-!
# G2: the explicit Frobenius-twist package (cross-curve relative Frobenius)

The cross-curve `p^e`-power relative Frobenius `Frob_{p^e} : E → E^{(p^e)}` in the
two-curve `EC.Isogeny` framework, for the inseparable factorisation when the
inseparable degree is not a `q`-power.

This file builds ON the existing twist machinery, it does not duplicate it:

* the twist curve `E^{(p^e)}` is the existing `WeierstrassCurve.iterateFrobeniusTwist`
  (`Curves/Maps.lean`, defined as `E.map (iterateFrobenius F p e)`);
* the single-`p` relative Frobenius pullback construction of `Curves/Maps.lean`
  (`frobeniusRelativePullback`, in the parametric `HasseWeil.Isogeny` framework)
  is **generalised** here into a reusable builder `EC.Isogeny.ofEquation`
  producing genuine `EC.Isogeny`s (with the `ord_∞` basepoint condition proven,
  not carried) from an `Equation` witness plus transcendence of the `x`-image;
* the basepoint condition is discharged by the `{1, y}`-parity route of
  `EC/IsogenyAG/MulByIntBasepoint.lean`, with *exact* generator orders
  `ord_∞(x^{p^e}) = -2p^e`, `ord_∞(y^{p^e}) = -3p^e`.

## The six package items

1. **Twist curve** `E^{(p^e)}`: `WeierstrassCurve.iterateFrobeniusTwist p E e`
   (already shipped in `Curves/Maps.lean`; iteration laws added here).
2. **Ellipticity preserved**: `iterateFrobeniusTwist_isElliptic` (instance) and
   `iterateFrobeniusTwist_Δ : Δ(E^{(p^e)}) = Δ(E)^{p^e} ≠ 0` via mathlib's
   `WeierstrassCurve.map_Δ` naturality.
3. **Relative Frobenius** `EC.Isogeny.relativeFrobenius p E e :
   EC.Isogeny E.toAffine (E.iterateFrobeniusTwist p e).toAffine`, with pullback
   `x_gen ↦ x_gen^{p^e}`, `y_gen ↦ y_gen^{p^e}` and the basepoint condition a
   theorem.
4. **Degree** `= p^e`: `relativeFrobenius_degree` over a perfect base, via the
   imperfection tower `[K(E) : K(E)^{p^e}] = p^e`
   (`finrank_KE_over_iterateFrobeniusRange`, proven here by induction from the
   `e = 1` case `GapQfKernel.finrank_KE_over_frobeniusRange_p`, transporting each
   rung along the `p^e`-power isomorphism `K(E) ≅ K(E)^{p^e}`).
5. **Iteration**: curve-level `iterateFrobeniusTwist_iterateFrobeniusTwist`
   (`(E^{(p^a)})^{(p^b)} = E^{(p^{a+b})}`) and the pullback-level composition law
   `relativeFrobenius_compose_pullback_x_gen`/`_y_gen` (stated on generators —
   the cast-free form these definitions support), plus the transported full
   identity `relativeFrobenius_add` via `EC.Isogeny.congrTarget`.
6. **`q`-power identification**: over `F = 𝔽_q`, `q = p^s`, the twist by
   `p^{s·m}` is `E` itself (`iterateFrobeniusTwist_card_mul_eq_self`) and the
   relative Frobenius is the same-curve `EC.Isogeny.frobeniusPower E m`
   (`relativeFrobenius_card_mul_eq_frobeniusPower`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.11–II.2.12, III.4
  Example 4.6 (the Frobenius twist and the relative Frobenius morphism).
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

/-! ### Item 1 + 5 (curve level): iteration laws for the twist -/

section TwistCurve

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p]

/-- The `0`-fold Frobenius twist is the curve itself. -/
@[simp] theorem iterateFrobeniusTwist_zero (E : WeierstrassCurve F) :
    E.iterateFrobeniusTwist p 0 = E := by
  show E.map (iterateFrobenius F p 0) = E
  rw [iterateFrobenius_zero]
  exact E.map_id

/-- The `1`-fold iterated Frobenius twist is the single Frobenius twist. -/
theorem iterateFrobeniusTwist_one (E : WeierstrassCurve F) :
    E.iterateFrobeniusTwist p 1 = E.frobeniusTwist p := by
  show E.map (iterateFrobenius F p 1) = E.map (frobenius F p)
  rw [iterateFrobenius_one]

/-- **Item 5, curve level**: `(E^{(p^a)})^{(p^b)} = E^{(p^{a+b})}`. -/
theorem iterateFrobeniusTwist_iterateFrobeniusTwist (E : WeierstrassCurve F) (a b : ℕ) :
    (E.iterateFrobeniusTwist p a).iterateFrobeniusTwist p b =
      E.iterateFrobeniusTwist p (a + b) := by
  show (E.map (iterateFrobenius F p a)).map (iterateFrobenius F p b) =
    E.map (iterateFrobenius F p (a + b))
  rw [WeierstrassCurve.map_map, ← iterateFrobenius_add, Nat.add_comm b a]

/-! ### Item 2: ellipticity of the twist -/

/-- **Item 2 (instance form)**: the iterated Frobenius twist of an elliptic curve
is elliptic. From mathlib's `(W.map f).IsElliptic` propagation. -/
instance iterateFrobeniusTwist_isElliptic (E : WeierstrassCurve F) [E.IsElliptic] (e : ℕ) :
    (E.iterateFrobeniusTwist p e).IsElliptic :=
  show (E.map (iterateFrobenius F p e)).IsElliptic from inferInstance

/-- **Item 2 (Silverman III.4 Example 4.6)**: the discriminant of the twist is the
`p^e`-th power of the discriminant, `Δ(E^{(p^e)}) = Δ(E)^{p^e}`. Naturality of `Δ`
under `WeierstrassCurve.map` (mathlib `map_Δ`). -/
theorem iterateFrobeniusTwist_Δ (E : WeierstrassCurve F) (e : ℕ) :
    (E.iterateFrobeniusTwist p e).Δ = E.Δ ^ p ^ e := by
  show (E.map (iterateFrobenius F p e)).Δ = E.Δ ^ p ^ e
  rw [WeierstrassCurve.map_Δ]
  rfl

/-- **Item 2 (nonvanishing)**: `Δ(E^{(p^e)}) ≠ 0`, so the twist is nonsingular. -/
theorem iterateFrobeniusTwist_Δ_ne_zero (E : WeierstrassCurve F) [E.IsElliptic] (e : ℕ) :
    (E.iterateFrobeniusTwist p e).Δ ≠ 0 := by
  rw [iterateFrobeniusTwist_Δ]
  exact pow_ne_zero _ E.isUnit_Δ.ne_zero

end TwistCurve

/-! ### The `EC.Isogeny.ofEquation` builder

A reusable cross-curve isogeny builder: given a pair `(u, v)` in `K(E)` satisfying
the Weierstrass equation of a second curve `V` (base-changed to `K(E)`), with `u`
transcendental over `F` and of even negative order at infinity, we obtain a genuine
`EC.Isogeny E.toAffine V.toAffine` whose pullback sends `x_gen V ↦ u`, `y_gen V ↦ v`.

This abstracts the single-`p` relative-Frobenius construction of `Curves/Maps.lean`
(`frobeniusRelativeBaseHom` → `frobeniusRelativeCoordRingHom` →
`frobeniusRelativePullback`) over the image pair, and discharges the basepoint
condition `pullback_ordAtInfty_nonneg` by the `{1, y}`-parity route of
`MulByIntBasepoint.lean`. -/

section Builder

variable {F : Type*} [Field F] [DecidableEq F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]
variable (V : WeierstrassCurve F) [V.toAffine.IsElliptic]

local notation "KE" => E.toAffine.FunctionField
local notation "KV" => V.toAffine.FunctionField

-- NB: the variable type must be spelled out (not via the `KE` notation): declaring a
-- section variable through a local notation that captures an earlier section variable
-- silently breaks elaboration of every downstream declaration using it.
variable (u v : E.toAffine.FunctionField)

/-- The base ring hom `F[X] → K(E)`, `X ↦ u`. -/
noncomputable def ofEquationBaseHom : Polynomial F →+* KE :=
  Polynomial.eval₂RingHom (algebraMap F KE) u

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
/-- The Weierstrass polynomial of `V` evaluates to zero at `(u, v)` (as an `eval₂`
over `Polynomial F`), given the `Equation` witness on the base-changed curve. -/
theorem ofEquation_polynomial_eval₂_zero
    (h_eqn : (V.map (algebraMap F KE)).toAffine.Equation u v) :
    V.toAffine.polynomial.eval₂ (ofEquationBaseHom E u) v = 0 := by
  rw [ofEquationBaseHom, Polynomial.eval₂_eval₂RingHom_apply, ← Affine.map_polynomial]
  exact h_eqn

-- NB: proof-witness arguments (`h_eqn`, `h_trans`) are explicit binders on the
-- *definitions* below: `include` does not apply to `def`s, and Prop-typed section
-- variables used only in a definition body are silently `sorry`-ed rather than
-- auto-included. The theorems keep them as section variables (declared below) since
-- there they occur in the statement types.
/-- The coordinate-ring pullback `F[V] → K(E)`, `X ↦ u`, `Y ↦ v`, via
`AdjoinRoot.lift`. -/
noncomputable def ofEquationCoordRingHom
    (h_eqn : (V.map (algebraMap F KE)).toAffine.Equation u v) :
    V.toAffine.CoordinateRing →+* KE :=
  AdjoinRoot.lift (ofEquationBaseHom E u) v
    (ofEquation_polynomial_eval₂_zero E V u v h_eqn)

/-- The coordinate-ring pullback as an `F`-algebra hom. -/
noncomputable def ofEquationCoordAlgHom
    (h_eqn : (V.map (algebraMap F KE)).toAffine.Equation u v) :
    V.toAffine.CoordinateRing →ₐ[F] KE :=
  { toRingHom := ofEquationCoordRingHom E V u v h_eqn
    commutes' := fun r ↦ by
      change ofEquationCoordRingHom E V u v h_eqn
        (algebraMap (Polynomial F) _ (algebraMap F (Polynomial F) r)) = _
      change AdjoinRoot.lift (ofEquationBaseHom E u) v _
        (AdjoinRoot.mk _ (Polynomial.C (algebraMap F (Polynomial F) r))) = _
      rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
      change ofEquationBaseHom E u (algebraMap F (Polynomial F) r) = _
      simp [ofEquationBaseHom, Polynomial.eval₂_C] }

-- NB: again no `KE` notation in the `variable` type (see above).
variable (h_eqn : (V.map (algebraMap F E.toAffine.FunctionField)).toAffine.Equation u v)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
/-- Action on the `X`-class: `X ↦ u`. -/
theorem ofEquationCoordAlgHom_x :
    ofEquationCoordAlgHom E V u v h_eqn
      (algebraMap (Polynomial F) V.toAffine.CoordinateRing Polynomial.X) = u := by
  change AdjoinRoot.lift (ofEquationBaseHom E u) v
    (ofEquation_polynomial_eval₂_zero E V u v h_eqn)
    (AdjoinRoot.mk _ (Polynomial.C Polynomial.X)) = _
  rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
  simp [ofEquationBaseHom, Polynomial.eval₂_X]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
/-- Action on the `Y`-class: `Y ↦ v`. -/
theorem ofEquationCoordAlgHom_y :
    ofEquationCoordAlgHom E V u v h_eqn
      (AdjoinRoot.root V.toAffine.polynomial) = v := by
  change AdjoinRoot.lift (ofEquationBaseHom E u) v
    (ofEquation_polynomial_eval₂_zero E V u v h_eqn) (AdjoinRoot.root _) = _
  exact AdjoinRoot.lift_root _

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
/-- Action on `F[X]`-classes: `q(X) ↦ q(u)`. -/
theorem ofEquationCoordRingHom_algebraMap_polynomial (q : Polynomial F) :
    ofEquationCoordRingHom E V u v h_eqn
      (algebraMap (Polynomial F) V.toAffine.CoordinateRing q) =
        Polynomial.aeval u q := by
  change AdjoinRoot.lift (ofEquationBaseHom E u) v
    (ofEquation_polynomial_eval₂_zero E V u v h_eqn) (AdjoinRoot.of _ q) = _
  rw [AdjoinRoot.lift_of]
  rfl

variable (h_trans : Transcendental F u)

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
include h_trans in
/-- The base hom `F[X] → K(E)`, `X ↦ u` is injective when `u` is transcendental. -/
theorem ofEquationBaseHom_injective : Function.Injective (ofEquationBaseHom E u) := by
  have h : (ofEquationBaseHom E u : Polynomial F →+* E.toAffine.FunctionField) =
      (Polynomial.aeval u : Polynomial F →ₐ[F] E.toAffine.FunctionField).toRingHom := by
    ext <;> simp [ofEquationBaseHom, Polynomial.aeval_def]
  rw [h]
  exact transcendental_iff_injective.mp h_trans

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
/-- Image of a rank-2 basis decomposition under the coordinate-ring pullback. -/
theorem ofEquationCoordRingHom_smul_basis_eq (a b : Polynomial F) :
    ofEquationCoordRingHom E V u v h_eqn
        (a • 1 + b • Affine.CoordinateRing.mk V.toAffine Polynomial.X) =
      ofEquationBaseHom E u a + ofEquationBaseHom E u b * v := by
  simp only [ofEquationCoordRingHom, map_add]
  congr 1
  · change AdjoinRoot.lift _ _ _ (a • 1) = _
    rw [Algebra.smul_def, mul_one]
    exact AdjoinRoot.lift_of _
  · change AdjoinRoot.lift _ _ _ (b • AdjoinRoot.root _) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    · exact AdjoinRoot.lift_of _
    · exact AdjoinRoot.lift_root _

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
include h_eqn h_trans in
/-- A vanishing rank-2 image forces the `Y`-coefficient to vanish (norm-degree
analysis via `degree_norm_smul_basis`). -/
private theorem ofEquationCoordRingHom_smul_basis_b_eq_zero (a b : Polynomial F)
    (h0 : ofEquationBaseHom E u a + ofEquationBaseHom E u b * v = 0) :
    b = 0 := by
  by_contra hb
  set r' := a • (1 : V.toAffine.CoordinateRing) +
      b • Affine.CoordinateRing.mk V.toAffine Polynomial.X with hr'_def
  have h_alg : ∀ f : Polynomial F,
      ofEquationCoordRingHom E V u v h_eqn
        (algebraMap (Polynomial F) _ f) = ofEquationBaseHom E u f := fun f ↦ by
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ f) = _
    exact AdjoinRoot.lift_of _
  set conj_r := Affine.CoordinateRing.mk V.toAffine
    (Polynomial.C a + Polynomial.C b *
      (-Polynomial.X - Polynomial.C
        (Polynomial.C V.toAffine.a₁ * Polynomial.X +
          Polynomial.C V.toAffine.a₃))) with hconj_def
  have h_factor : algebraMap (Polynomial F) _
      (Algebra.norm (Polynomial F) r') = r' * conj_r := by
    rw [hr'_def, hconj_def]
    change AdjoinRoot.of _ _ = _
    rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
    congr 1
    rw [map_add, map_mul]
    simp [Algebra.smul_def]
  have hr'_zero : ofEquationCoordRingHom E V u v h_eqn r' = 0 :=
    (ofEquationCoordRingHom_smul_basis_eq E V u v h_eqn a b).trans h0
  have h_norm_zero : ofEquationBaseHom E u
      (Algebra.norm (Polynomial F) r') = 0 := by
    rw [← h_alg, h_factor, map_mul, hr'_zero, zero_mul]
  have h_norm_eq : Algebra.norm (Polynomial F) r' = 0 :=
    ofEquationBaseHom_injective E u h_trans (h_norm_zero.trans (map_zero _).symm)
  rw [hr'_def] at h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis
    (W' := V.toAffine) a b
  rw [h_norm_eq, Polynomial.degree_zero] at h_deg
  have hb_deg : b.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hb
  have h2bot : 2 • b.degree + 3 ≠ (⊥ : WithBot ℕ) := by
    intro h
    apply hb_deg
    cases hd : b.degree with
    | bot => rfl
    | coe n =>
        rw [hd] at h
        exact absurd h (by
          change ¬ (2 • (↑n : WithBot ℕ) + 3 = ⊥)
          simp [WithBot.mul_ne_bot])
  exact absurd (h_deg ▸ le_max_right _ _ : 2 • b.degree + 3 ≤ ⊥)
    (not_le.mpr (WithBot.bot_lt_iff_ne_bot.mpr h2bot))

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
include h_trans in
/-- **Injectivity of the coordinate-ring pullback** (rank-2 basis decomposition +
norm-degree analysis, pattern of `frobeniusRelativeCoordRingHom_injective`). -/
theorem ofEquationCoordRingHom_injective :
    Function.Injective (ofEquationCoordRingHom E V u v h_eqn) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨a, b, hab⟩ :=
    Affine.CoordinateRing.exists_smul_basis_eq (W' := V.toAffine) r
  rw [← hab, ofEquationCoordRingHom_smul_basis_eq] at hr
  have hb : b = 0 :=
    ofEquationCoordRingHom_smul_basis_b_eq_zero E V u v h_eqn h_trans a b hr
  rw [hb, map_zero, zero_mul, add_zero] at hr
  have ha : a = 0 :=
    ofEquationBaseHom_injective E u h_trans (hr.trans (map_zero _).symm)
  rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
include h_trans in
/-- AlgHom-level injectivity. -/
lemma ofEquationCoordAlgHom_injective :
    Function.Injective (ofEquationCoordAlgHom E V u v h_eqn) :=
  ofEquationCoordRingHom_injective E V u v h_eqn h_trans

/-- **The function-field pullback** `K(V) →ₐ[F] K(E)`, `x_gen V ↦ u`,
`y_gen V ↦ v`: the `IsFractionRing.liftAlgHom` extension of the coordinate-ring
pullback. -/
noncomputable def ofEquationPullback
    (h_eqn : (V.map (algebraMap F KE)).toAffine.Equation u v)
    (h_trans : Transcendental F u) : KV →ₐ[F] KE :=
  IsFractionRing.liftAlgHom (ofEquationCoordAlgHom_injective E V u v h_eqn h_trans)

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
/-- The pullback sends `x_gen V ↦ u`. -/
theorem ofEquationPullback_x_gen :
    ofEquationPullback E V u v h_eqn h_trans (x_gen V) = u := by
  unfold ofEquationPullback
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  exact ofEquationCoordAlgHom_x E V u v h_eqn

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
/-- The pullback sends `y_gen V ↦ v`. -/
theorem ofEquationPullback_y_gen :
    ofEquationPullback E V u v h_eqn h_trans (y_gen V) = v := by
  unfold ofEquationPullback
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  exact ofEquationCoordAlgHom_y E V u v h_eqn

omit [WeierstrassCurve.IsElliptic E.toAffine] [WeierstrassCurve.IsElliptic V.toAffine] in
/-- The pullback of a polynomial in `x`: `q(x_gen V) ↦ q(u)`. -/
theorem ofEquationPullback_algebraMap_polynomial (q : Polynomial F) :
    ofEquationPullback E V u v h_eqn h_trans
      (algebraMap (Polynomial F) KV q) = Polynomial.aeval u q := by
  rw [IsScalarTower.algebraMap_apply (Polynomial F) V.toAffine.CoordinateRing
    (V.toAffine.FunctionField) q]
  unfold ofEquationPullback
  rw [IsFractionRing.liftAlgHom_apply]
  rw [IsFractionRing.lift_algebraMap]
  exact ofEquationCoordRingHom_algebraMap_polynomial E V u v h_eqn q

/-! #### The basepoint condition for `ofEquationPullback` -/

omit [WeierstrassCurve.IsElliptic E.toAffine] in
set_option maxHeartbeats 800000 in
/-- **Order transport for `F(x)`-elements**: for nonzero `r ∈ F(x)` and
`ord_∞ u = M < 0`, there is `t ∈ ℤ` with `ord_∞^V(r) = -2t` and
`ord_∞^E(pullback r) = t·M`. Mirror of
`ord_mulByInt_pullback_algebraMap_fracPolyX`. -/
theorem ord_ofEquationPullback_algebraMap_fracPolyX
    {M : ℤ} (hM : (W_smooth E).ordAtInfty u = ((M : ℤ) : WithTop ℤ)) (hMneg : M < 0)
    {r : FractionRing (Polynomial F)} (hr : r ≠ 0) :
    ∃ t : ℤ,
      (W_smooth V).ordAtInfty
        (algebraMap (FractionRing (Polynomial F)) KV r) =
        ((-2 * t : ℤ) : WithTop ℤ) ∧
      (W_smooth E).ordAtInfty
        (ofEquationPullback E V u v h_eqn h_trans
          (algebraMap (FractionRing (Polynomial F)) KV r)) =
        ((t * M : ℤ) : WithTop ℤ) := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Polynomial F) r
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hr hab.symm
  have himg : algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r =
      algebraMap (Polynomial F) (V.toAffine.FunctionField) a /
        algebraMap (Polynomial F) (V.toAffine.FunctionField) b := by
    rw [← hab, map_div₀,
      ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) _,
      ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) _]
  have hab_ne : algebraMap (Polynomial F) (V.toAffine.FunctionField) b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) _]
    intro h
    exact hb0 (FaithfulSMul.algebraMap_injective (Polynomial F)
      (FractionRing (Polynomial F))
      (((algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField)).injective
        (h.trans (map_zero _).symm)).trans (map_zero _).symm))
  refine ⟨(a.natDegree : ℤ) - (b.natDegree : ℤ), ?_, ?_⟩
  · have h := (W_smooth V).ord_div_concrete hab_ne
      (-2 * a.natDegree) (-2 * b.natDegree)
      ((W_smooth V).ordAtInfty_algebraMap_polynomial_of_ne_zero ha0)
      ((W_smooth V).ordAtInfty_algebraMap_polynomial_of_ne_zero hb0)
    rw [himg]
    exact h.trans (WithTop.coe_inj.mpr (by ring))
  · have hpb : ofEquationPullback E V u v h_eqn h_trans
        (algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r) =
        Polynomial.aeval u a / Polynomial.aeval u b := by
      rw [himg, map_div₀, ofEquationPullback_algebraMap_polynomial,
        ofEquationPullback_algebraMap_polynomial]
    have hq_img_ne : Polynomial.aeval u b ≠ 0 :=
      (W_smooth E).aeval_ne_zero_of_ord_neg hM hMneg hb0
    have h := (W_smooth E).ord_div_concrete hq_img_ne
      ((a.natDegree : ℤ) * M) ((b.natDegree : ℤ) * M)
      ((W_smooth E).ordAtInfty_aeval_of_ord_eq hM hMneg ha0)
      ((W_smooth E).ordAtInfty_aeval_of_ord_eq hM hMneg hb0)
    rw [hpb]
    exact h.trans (WithTop.coe_inj.mpr (by ring))

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine]
  [WeierstrassCurve.IsElliptic V.toAffine] in
include h_eqn h_trans in
/-- The `y`-image of the builder is nonzero: `v = 0` would make `u` a root of the
monic cubic `X³ + a₂X² + a₄X + a₆` over `F`, contradicting transcendence. -/
private theorem ofEquation_v_ne_zero : v ≠ 0 := by
  have h_eq : v ^ 2 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₁ * u * v +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₃ * v =
      u ^ 3 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₂ * u ^ 2 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₄ * u +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₆ := by
    have h := (WeierstrassCurve.Affine.equation_iff
      (W := (V.map (algebraMap F (E.toAffine.FunctionField))).toAffine) u v).mp h_eqn
    simpa using h
  intro hv
  rw [hv] at h_eq
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero] at h_eq
  set q : Polynomial F := Polynomial.X ^ 3 + Polynomial.C V.toAffine.a₂ * Polynomial.X ^ 2 +
    Polynomial.C V.toAffine.a₄ * Polynomial.X + Polynomial.C V.toAffine.a₆ with hq_def
  have hq_ne : q ≠ 0 := by
    intro h
    have h3 := congrArg (fun r ↦ Polynomial.coeff r 3) h
    simp [hq_def, Polynomial.coeff_X_pow] at h3
  have hq_eval : Polynomial.aeval u q = 0 := by
    rw [hq_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← h_eq]
  exact h_trans ⟨q, hq_ne, hq_eval⟩

omit [DecidableEq F] in
/-- Abstract `WithTop ℤ` order arithmetic for the `y`-part of the basepoint
condition: if `ord A = t·2m` with `t ≤ -2`, `m ≤ -1`, and `ord B ≥ 3m` with
`B ≠ 0`, then `ord (A·B) ≥ 0`. Stated over abstract elements so that the
workhorse below only instantiates (no deep defeq on large pullback terms). -/
private theorem ofEquation_ord_mul_nonneg_aux {C : Curves.SmoothPlaneCurve F}
    {A B : C.FunctionField} {t m : ℤ} (hm : m ≤ -1) (ht : t ≤ -2)
    (hA : C.ordAtInfty A = ((t * (2 * m) : ℤ) : WithTop ℤ))
    (hB3 : ((3 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty B) (hB : B ≠ 0) :
    0 ≤ C.ordAtInfty (A * B) := by
  have hA_ne : A ≠ 0 :=
    (C.ordAtInfty_eq_top_iff _).not.mp (ne_of_eq_of_ne hA WithTop.coe_ne_top)
  rw [C.ordAtInfty_mul hA_ne hB, hA]
  refine le_trans ?_ (add_le_add le_rfl hB3)
  rw [← WithTop.coe_add]
  have : (0 : ℤ) ≤ t * (2 * m) + 3 * m := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -2 - t)
      (by linarith : (0:ℤ) ≤ -(2 * m))]
  exact_mod_cast this

omit [WeierstrassCurve.IsElliptic E.toAffine] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The basepoint condition**: the pullback preserves regularity at infinity,
provided `ord_∞ u = 2m` is even and `≤ -2`. The `{1, y}`-parity route of
`mulByInt_pullbackAlgHom_ordAtInfty_nonneg`, with the `y`-image order bound coming
from the Weierstrass equation `h_eqn` via `le_ordAtInfty_y_of_weierstrass`. -/
theorem ofEquationPullback_ordAtInfty_nonneg
    {m : ℤ} (hm : m ≤ -1)
    (hu : (W_smooth E).ordAtInfty u = ((2 * m : ℤ) : WithTop ℤ))
    (f : KV) (hf : 0 ≤ (W_smooth V).ordAtInfty f) :
    0 ≤ (W_smooth E).ordAtInfty
      (ofEquationPullback E V u v h_eqn h_trans f) := by
  classical
  have hMneg : 2 * m < 0 := by omega
  -- the Weierstrass equation satisfied by the image pair `(u, v)` over `K(E)`
  have h_eq : v ^ 2 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₁ * u * v +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₃ * v =
      u ^ 3 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₂ * u ^ 2 +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₄ * u +
        algebraMap F (E.toAffine.FunctionField) V.toAffine.a₆ := by
    have h := (WeierstrassCurve.Affine.equation_iff
      (W := (V.map (algebraMap F (E.toAffine.FunctionField))).toAffine) u v).mp h_eqn
    simpa using h
  -- the `y`-image order bound from the curve equation
  have h_y : ((3 * m : ℤ) : WithTop ℤ) ≤ (W_smooth E).ordAtInfty v :=
    (W_smooth E).le_ordAtInfty_y_of_weierstrass hm hu h_eq
  -- decompose `f = r₁ + r₂·y` over `F(x)`
  obtain ⟨r₁, r₂, hf_decomp⟩ := (W_smooth V).exists_decomp f
  have hf_eq : f = algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₁ +
      algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₂ * y_gen V := by
    rw [hf_decomp, y_gen_eq_coordYInFunctionField' V, Algebra.smul_def, mul_one,
      Algebra.smul_def]
    rfl
  -- split the hypothesis through the parity/min formula
  have h_min : (W_smooth V).ordAtInfty f =
      min ((W_smooth V).ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₁))
          ((W_smooth V).ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₂) +
           (W_smooth V).ordAtInfty (y_gen V)) := by
    rw [hf_eq]
    exact (W_smooth V).ordAtInfty_basis_eq_min r₁ r₂
  rw [h_min, le_min_iff] at hf
  obtain ⟨hf1, hf2⟩ := hf
  rw [ordAtInfty_y_gen V] at hf2
  -- the image decomposition
  have himg : ofEquationPullback E V u v h_eqn h_trans f =
      ofEquationPullback E V u v h_eqn h_trans
        (algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₁) +
      ofEquationPullback E V u v h_eqn h_trans
        (algebraMap (FractionRing (Polynomial F)) (V.toAffine.FunctionField) r₂) * v := by
    rw [hf_eq, map_add, map_mul, ofEquationPullback_y_gen E V u v h_eqn h_trans]
  rw [himg]
  refine le_trans (le_min ?_ ?_) ((W_smooth E).ordAtInfty_add_ge_min _ _)
  · -- the `F(x)`-part: `ord ≥ 0` transports to `ord ≥ 0`
    rcases eq_or_ne r₁ 0 with rfl | hr₁
    · rw [map_zero, map_zero]
      exact le_of_le_of_eq le_top ((W_smooth E).ordAtInfty_zero).symm
    · obtain ⟨t, hsrc, himg1⟩ :=
        ord_ofEquationPullback_algebraMap_fracPolyX E V u v h_eqn h_trans hu hMneg hr₁
      rw [hsrc] at hf1
      have ht : t ≤ 0 := by
        have : (0 : ℤ) ≤ -2 * t := by exact_mod_cast hf1
        linarith
      rw [himg1]
      have : (0 : ℤ) ≤ t * (2 * m) := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -t)
          (by linarith : (0:ℤ) ≤ -(2 * m))]
      exact_mod_cast this
  · -- the `y`-part
    rcases eq_or_ne r₂ 0 with rfl | hr₂
    · rw [map_zero, map_zero, zero_mul]
      exact le_of_le_of_eq le_top ((W_smooth E).ordAtInfty_zero).symm
    · have hv_ne : v ≠ 0 := ofEquation_v_ne_zero E V u v h_eqn h_trans
      obtain ⟨t, hsrc, himg2⟩ :=
        ord_ofEquationPullback_algebraMap_fracPolyX E V u v h_eqn h_trans hu hMneg hr₂
      rw [hsrc] at hf2
      have ht : t ≤ -2 := by
        have h0 : (0 : WithTop ℤ) ≤ ((-2 * t + -3 : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_add]
          exact_mod_cast hf2
        have : (0 : ℤ) ≤ -2 * t + -3 := by exact_mod_cast h0
        omega
      exact ofEquation_ord_mul_nonneg_aux hm ht himg2 h_y hv_ne

/-- **The packaged builder**: a genuine `EC.Isogeny E.toAffine V.toAffine` from an
`Equation` witness, transcendence of the `x`-image, and the even-negative-order
witness. The basepoint condition is a theorem, not data. -/
noncomputable def _root_.HasseWeil.EC.Isogeny.ofEquation
    (h_eqn : (V.map (algebraMap F KE)).toAffine.Equation u v)
    (h_trans : Transcendental F u)
    {m : ℤ} (hm : m ≤ -1)
    (hu : (W_smooth E).ordAtInfty u = ((2 * m : ℤ) : WithTop ℤ)) :
    EC.Isogeny E.toAffine V.toAffine where
  toCurveMap := { pullback := ofEquationPullback E V u v h_eqn h_trans }
  pullback_ordAtInfty_nonneg := fun f hf ↦
    ofEquationPullback_ordAtInfty_nonneg E V u v h_eqn h_trans hm hu f hf

@[simp] theorem _root_.HasseWeil.EC.Isogeny.ofEquation_pullback
    {m : ℤ} (hm : m ≤ -1)
    (hu : (W_smooth E).ordAtInfty u = ((2 * m : ℤ) : WithTop ℤ)) (f : KV) :
    (EC.Isogeny.ofEquation E V u v h_eqn h_trans hm hu).toCurveMap.pullback f =
      ofEquationPullback E V u v h_eqn h_trans f := rfl

end Builder

/-! ### Generic degree bridge: `degree = finrank` over the pullback field range -/

section DegreeBridge

variable {F : Type*} [Field F]

/-- The degree of an `EC.Isogeny` equals the `Module.finrank` of `K(E₁)` over the
field range of its pullback. Mirror of `frobenius_finrank_eq_fieldRange_finrank`
(via `AlgEquiv.ofInjective` and `Algebra.finrank_eq_of_equiv_equiv`), generic in
the isogeny. -/
theorem EC.Isogeny.degree_eq_finrank_fieldRange
    {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] (φ : EC.Isogeny W₁ W₂) :
    φ.degree =
      Module.finrank φ.toCurveMap.pullback.fieldRange W₁.FunctionField := by
  have := @Algebra.finrank_eq_of_equiv_equiv
    (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField
    (⟨W₁⟩ : Curves.SmoothPlaneCurve F).FunctionField _ _
    φ.toCurveMap.toAlgebra
    φ.toCurveMap.pullback.fieldRange (⟨W₁⟩ : Curves.SmoothPlaneCurve F).FunctionField _ _ _
    ((AlgEquiv.ofInjective φ.toCurveMap.pullback
      φ.toCurveMap.pullback.toRingHom.injective).toRingEquiv) (RingEquiv.refl _) ?_
  · exact this
  · ext x
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.coe_refl]
    change ↑(AlgEquiv.ofInjective φ.toCurveMap.pullback
      φ.toCurveMap.pullback.toRingHom.injective x) =
      φ.toCurveMap.pullback.toRingHom x
    simp [AlgEquiv.ofInjective_apply]

end DegreeBridge

/-! ### Item 3: the relative Frobenius `Frob_{p^e} : E → E^{(p^e)}` as an `EC.Isogeny` -/

section RelativeFrobenius

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [ExpChar F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

local notation "KE" => E.toAffine.FunctionField

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
/-- The `K(E)`-base-change of the twist equals the `iterateFrobenius`-pullback of
`W_KE E` (mirror of `frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius`, via
`RingHom.iterateFrobenius_comm`). -/
theorem iterateFrobeniusTwist_map_KE_eq (e : ℕ) :
    (E.iterateFrobeniusTwist p e).map (algebraMap F KE) =
      (W_KE E).map (iterateFrobenius KE p e) := by
  unfold WeierstrassCurve.iterateFrobeniusTwist W_KE
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      RingHom.iterateFrobenius_comm (algebraMap F (E.toAffine.FunctionField)) p e]

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
/-- **The twist Weierstrass equation at the generic point**: the base-changed twist
curve passes through `(x_gen^{p^e}, y_gen^{p^e})`. -/
theorem iterateFrobeniusTwist_generic_equation (e : ℕ) :
    ((E.iterateFrobeniusTwist p e).map (algebraMap F KE)).toAffine.Equation
      (x_gen E ^ p ^ e) (y_gen E ^ p ^ e) := by
  have h := Affine.Equation.map (W := W_KE E) (iterateFrobenius (E.toAffine.FunctionField) p e)
    (generic_equation E)
  rw [Affine.map] at h
  rw [show iterateFrobenius (E.toAffine.FunctionField) p e (x_gen E) = x_gen E ^ p ^ e from rfl,
      show iterateFrobenius (E.toAffine.FunctionField) p e (y_gen E) = y_gen E ^ p ^ e from rfl,
      ← iterateFrobeniusTwist_map_KE_eq p E e] at h
  exact h

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
/-- `x_gen^{p^e}` is transcendental over `F`. -/
lemma x_gen_pow_p_pow_transcendental (e : ℕ) :
    Transcendental F (x_gen E ^ p ^ e) :=
  (x_gen_transcendental E).pow (pow_pos (expChar_pos F p) e)

omit [ExpChar F p] in
/-- `ord_∞(x_gen^{p^e}) = 2·(-p^e)` (even and `≤ -2`). -/
lemma ordAtInfty_x_gen_pow_p_pow (e : ℕ) :
    (W_smooth E).ordAtInfty (x_gen E ^ p ^ e) =
      ((2 * (-(p ^ e : ℤ)) : ℤ) : WithTop ℤ) :=
  ((W_smooth E).ord_pow_concrete (x_gen_ne_zero E) (-2) (p ^ e)
    (ordAtInfty_x_gen E)).trans (WithTop.coe_inj.mpr (by push_cast; ring))

lemma neg_p_pow_le_neg_one {p : ℕ} (hp : 0 < p) (e : ℕ) : -(p ^ e : ℤ) ≤ -1 := by
  have h1 : (1 : ℕ) ≤ p ^ e := Nat.one_le_pow e p hp
  have : (1 : ℤ) ≤ (p ^ e : ℤ) := by exact_mod_cast h1
  omega

/-- **Item 3: the relative `p^e`-power Frobenius** `Frob_{p^e} : E → E^{(p^e)}` as a
genuine `EC.Isogeny` — the pullback sends `x_gen ↦ x_gen^{p^e}`,
`y_gen ↦ y_gen^{p^e}` (`F`-linearly: the coefficients are de-twisted, the variables
are `p^e`-powered), and the basepoint condition `ord_∞`-nonnegativity-preservation
is proven, not carried. Reference: Silverman II.2.11. -/
noncomputable def EC.Isogeny.relativeFrobenius (e : ℕ) :
    EC.Isogeny E.toAffine (E.iterateFrobeniusTwist p e).toAffine :=
  EC.Isogeny.ofEquation E (E.iterateFrobeniusTwist p e)
    (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
    (iterateFrobeniusTwist_generic_equation p E e)
    (x_gen_pow_p_pow_transcendental p E e)
    (neg_p_pow_le_neg_one (expChar_pos F p) e)
    (ordAtInfty_x_gen_pow_p_pow p E e)

/-- The relative Frobenius pullback sends `x_gen E^{(p^e)} ↦ x_gen E^{p^e}`. -/
@[simp] theorem relativeFrobenius_pullback_x_gen (e : ℕ) :
    (EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (x_gen (E.iterateFrobeniusTwist p e)) = x_gen E ^ p ^ e :=
  ofEquationPullback_x_gen E (E.iterateFrobeniusTwist p e) (x_gen E ^ p ^ e)
    (y_gen E ^ p ^ e) (iterateFrobeniusTwist_generic_equation p E e)
    (x_gen_pow_p_pow_transcendental p E e)

/-- The relative Frobenius pullback sends `y_gen E^{(p^e)} ↦ y_gen E^{p^e}`. -/
@[simp] theorem relativeFrobenius_pullback_y_gen (e : ℕ) :
    (EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (y_gen (E.iterateFrobeniusTwist p e)) = y_gen E ^ p ^ e :=
  ofEquationPullback_y_gen E (E.iterateFrobeniusTwist p e) (x_gen E ^ p ^ e)
    (y_gen E ^ p ^ e) (iterateFrobeniusTwist_generic_equation p E e)
    (x_gen_pow_p_pow_transcendental p E e)

/-! #### The compositional identity and the pullback field range -/

/-- **Compositional identity**: the relative Frobenius pullback of the
`CoordinateRing.map (iterateFrobenius F p e)`-image of `r` is the `p^e`-th power of
the image of `r` (mirror of `frobeniusRelativeCoordRingHom_comp_map`). The
algebraic heart of pure inseparability. -/
private theorem relativeFrobenius_coordRingHom_comp_map (e : ℕ) :
    (ofEquationCoordRingHom E (E.iterateFrobeniusTwist p e)
        (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
        (iterateFrobeniusTwist_generic_equation p E e)).comp
        (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)) =
      (iterateFrobenius (E.toAffine.FunctionField) p e).comp
        (algebraMap E.toAffine.CoordinateRing (E.toAffine.FunctionField)) := by
  apply AdjoinRoot.ringHom_ext
  · -- composition with `of`: agree on the polynomial-base.
    apply RingHom.ext
    intro q
    change ofEquationCoordRingHom E (E.iterateFrobeniusTwist p e)
        (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
        (iterateFrobeniusTwist_generic_equation p E e)
      (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
        (AdjoinRoot.mk _ (Polynomial.C q))) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_C]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (Polynomial.C _)) = _
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
    change ((Polynomial.mapRingHom (iterateFrobenius F p e)) q).eval₂
        (algebraMap F (E.toAffine.FunctionField)) (x_gen E ^ p ^ e) = _
    rw [show (Polynomial.mapRingHom (iterateFrobenius F p e)) q =
          q.map (iterateFrobenius F p e) from rfl,
        Polynomial.eval₂_map,
        show ((algebraMap F (E.toAffine.FunctionField)).comp (iterateFrobenius F p e)) =
          ((iterateFrobenius (E.toAffine.FunctionField) p e).comp
            (algebraMap F (E.toAffine.FunctionField))) from
          RingHom.iterateFrobenius_comm (algebraMap F (E.toAffine.FunctionField)) p e,
        show (x_gen E ^ p ^ e : E.toAffine.FunctionField) =
          (iterateFrobenius (E.toAffine.FunctionField) p e) (x_gen E) from rfl,
        ← Polynomial.hom_eval₂]
    change (iterateFrobenius (E.toAffine.FunctionField) p e) (q.eval₂ _ _) =
      (iterateFrobenius (E.toAffine.FunctionField) p e) (algebraMap _ _ _)
    congr 1
    change q.eval₂ (algebraMap F (E.toAffine.FunctionField)) (x_gen E) =
      algebraMap _ _ ((AdjoinRoot.of _) q)
    exact (algebraMap_CR_KE_of_eq_eval₂ E q).symm
  · -- At root: both sides give y_gen^(p^e).
    change ofEquationCoordRingHom E (E.iterateFrobeniusTwist p e)
        (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
        (iterateFrobeniusTwist_generic_equation p E e)
      (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
        (AdjoinRoot.root _)) =
      (iterateFrobenius (E.toAffine.FunctionField) p e)
        ((algebraMap E.toAffine.CoordinateRing (E.toAffine.FunctionField))
          (AdjoinRoot.root _))
    rw [show WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)
          (AdjoinRoot.root E.toAffine.polynomial) =
          AdjoinRoot.root (E.iterateFrobeniusTwist p e).toAffine.polynomial by
        change AdjoinRoot.lift _ _ _ _ = _
        rw [AdjoinRoot.lift_root]
        rfl]
    rw [show ofEquationCoordRingHom E (E.iterateFrobeniusTwist p e)
          (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
          (iterateFrobeniusTwist_generic_equation p E e)
          (AdjoinRoot.root (E.iterateFrobeniusTwist p e).toAffine.polynomial) =
            y_gen E ^ p ^ e from
        ofEquationCoordAlgHom_y E (E.iterateFrobeniusTwist p e) (x_gen E ^ p ^ e)
          (y_gen E ^ p ^ e) (iterateFrobeniusTwist_generic_equation p E e)]
    rfl

theorem relativeFrobenius_pullback_coordRingMap (e : ℕ) (r : E.toAffine.CoordinateRing) :
    (EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e) r)) =
    algebraMap E.toAffine.CoordinateRing KE r ^ p ^ e := by
  have h1 : (EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback
      (algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
        (E.iterateFrobeniusTwist p e).toAffine.FunctionField
        (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e) r)) =
      ofEquationCoordRingHom E (E.iterateFrobeniusTwist p e)
        (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
        (iterateFrobeniusTwist_generic_equation p E e)
        (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e) r) := by
    change ofEquationPullback E (E.iterateFrobeniusTwist p e)
      (x_gen E ^ p ^ e) (y_gen E ^ p ^ e)
      (iterateFrobeniusTwist_generic_equation p E e)
      (x_gen_pow_p_pow_transcendental p E e) _ = _
    unfold ofEquationPullback
    rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
    rfl
  rw [h1]
  exact RingHom.congr_fun (relativeFrobenius_coordRingHom_comp_map p E e) r

/-- Every `p^e`-th power in `K(E)` lies in the relative Frobenius pullback range
(pure inseparability witness; mirror of `frobeniusIsog_relative_pow_p_mem_fieldRange`). -/
theorem relativeFrobenius_pow_mem_fieldRange (e : ℕ) (f : KE) :
    f ^ p ^ e ∈
      (EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback.fieldRange := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) f
  rw [div_pow]
  apply IntermediateField.div_mem
  · exact ⟨algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
      (E.iterateFrobeniusTwist p e).toAffine.FunctionField
      (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e) a),
      relativeFrobenius_pullback_coordRingMap p E e a⟩
  · exact ⟨algebraMap (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing
      (E.iterateFrobeniusTwist p e).toAffine.FunctionField
      (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e) b),
      relativeFrobenius_pullback_coordRingMap p E e b⟩

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
/-- Over a perfect base, `CoordinateRing.map` along the iterated Frobenius is
surjective (coefficientwise `p^e`-th roots exist). -/
private theorem coordinateRingMap_iterateFrobenius_surjective [PerfectField F] (e : ℕ) :
    Function.Surjective (Affine.CoordinateRing.map E.toAffine (iterateFrobenius F p e)) := by
  intro w
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective w
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (Polynomial.mapRingHom (iterateFrobenius F p e))
    (Polynomial.map_surjective _ (bijective_iterateFrobenius F p e).surjective) q
  exact ⟨AdjoinRoot.mk _ q',
    (WeierstrassCurve.Affine.CoordinateRing.map_mk (iterateFrobenius F p e) q')⟩

set_option maxHeartbeats 800000 in
/-- **Range identification over a perfect base**: the pullback field range of the
relative `p^e`-Frobenius is exactly the subfield `K(E)^{p^e}` of `p^e`-th powers. -/
theorem relativeFrobenius_fieldRange_toSubfield [PerfectField F] (e : ℕ) :
    ((EC.Isogeny.relativeFrobenius p E e).toCurveMap.pullback.fieldRange).toSubfield =
      (iterateFrobenius KE p e).fieldRange := by
  apply le_antisymm
  · -- the pullback range consists of `p^e`-th powers
    rintro x hx
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ :=
      IsFractionRing.div_surjective (A := (E.iterateFrobeniusTwist p e).toAffine.CoordinateRing) w
    rw [map_div₀]
    apply div_mem
    · obtain ⟨a₀, rfl⟩ := coordinateRingMap_iterateFrobenius_surjective p E e a
      exact ⟨algebraMap E.toAffine.CoordinateRing (E.toAffine.FunctionField) a₀,
        (relativeFrobenius_pullback_coordRingMap p E e a₀).symm⟩
    · obtain ⟨b₀, rfl⟩ := coordinateRingMap_iterateFrobenius_surjective p E e b
      exact ⟨algebraMap E.toAffine.CoordinateRing (E.toAffine.FunctionField) b₀,
        (relativeFrobenius_pullback_coordRingMap p E e b₀).symm⟩
  · -- every `p^e`-th power is in the pullback range
    rintro x ⟨g, rfl⟩
    exact relativeFrobenius_pow_mem_fieldRange p E e g

end RelativeFrobenius

/-! ### Item 4: the degree of the relative Frobenius -/

section Degree

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

local notation "KE" => E.toAffine.FunctionField

/-- The `p^e`-power map as a ring isomorphism of `K(E)` onto the subfield
`K(E)^{p^e} = (iterateFrobenius K(E) p e).fieldRange`. -/
private noncomputable def iterFrobRangeEquiv (e : ℕ) :
    E.toAffine.FunctionField ≃+*
      ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange) :=
  { toFun := fun x ↦ ⟨iterateFrobenius (E.toAffine.FunctionField) p e x,
      RingHom.mem_fieldRange.mpr ⟨x, rfl⟩⟩
    invFun := fun y ↦ Classical.choose (RingHom.mem_fieldRange.mp y.2)
    left_inv := fun x ↦ (iterateFrobenius (E.toAffine.FunctionField) p e).injective
      (Classical.choose_spec (RingHom.mem_fieldRange.mp
        (RingHom.mem_fieldRange.mpr ⟨x, rfl⟩)))
    right_inv := fun y ↦ Subtype.ext
      (Classical.choose_spec (RingHom.mem_fieldRange.mp y.2))
    map_mul' := fun a b ↦ Subtype.ext (map_mul _ a b)
    map_add' := fun a b ↦ Subtype.ext (map_add _ a b) }

/-- Finrank transport along an equality of subfields. -/
private theorem finrank_subfield_congr {L : Type*} [Field L] {S T : Subfield L}
    (h : S = T) : Module.finrank ↥S L = Module.finrank ↥T L := by
  subst h
  rfl

omit [DecidableEq F] [WeierstrassCurve.IsElliptic E.toAffine] in
set_option maxHeartbeats 800000 in
/-- **The tower step**: `[K(E) : K(E)^{p^{e+1}}] = [K(E) : K(E)^p] · [K(E) : K(E)^{p^e}]`.
The first factor of the tower law `[K(E)^{p^e} : K(E)^{p^{e+1}}]` is transported to
`[K(E) : K(E)^p]` along the `p^e`-power isomorphism `K(E) ≅ K(E)^{p^e}`. -/
private theorem finrank_iterFrobRange_succ (e : ℕ) :
    Module.finrank ↥((iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange)
        (E.toAffine.FunctionField) =
      Module.finrank ↥((iterateFrobenius (E.toAffine.FunctionField) p 1).fieldRange)
          (E.toAffine.FunctionField) *
        Module.finrank ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange)
          (E.toAffine.FunctionField) := by
  have hle : (iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange ≤
      (iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange := by
    rintro x hx
    obtain ⟨g, rfl⟩ := RingHom.mem_fieldRange.mp hx
    refine RingHom.mem_fieldRange.mpr ⟨g ^ p, ?_⟩
    show (g ^ p) ^ p ^ e = g ^ p ^ (e + 1)
    rw [← pow_mul, ← pow_succ']
  letI : Algebra
      ↥((iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange)
      ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange) :=
    (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower
      ↥((iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange)
      ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange)
      (E.toAffine.FunctionField) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have h_tower := Module.finrank_mul_finrank
    ↥((iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange)
    ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange)
    (E.toAffine.FunctionField)
  have h_first : Module.finrank
      ↥((iterateFrobenius (E.toAffine.FunctionField) p 1).fieldRange)
      (E.toAffine.FunctionField) = Module.finrank
      ↥((iterateFrobenius (E.toAffine.FunctionField) p (e + 1)).fieldRange)
      ↥((iterateFrobenius (E.toAffine.FunctionField) p e).fieldRange) := by
    refine Algebra.finrank_eq_of_equiv_equiv
      ((iterFrobRangeEquiv p E 1).symm.trans (iterFrobRangeEquiv p E (e + 1)))
      (iterFrobRangeEquiv p E e) ?_
    ext x
    show ((iterFrobRangeEquiv p E 1).symm x : E.toAffine.FunctionField) ^ p ^ (e + 1) =
      (x : E.toAffine.FunctionField) ^ p ^ e
    have hz : ((iterFrobRangeEquiv p E 1).symm x : E.toAffine.FunctionField) ^ p ^ 1 =
        (x : E.toAffine.FunctionField) :=
      congrArg Subtype.val ((iterFrobRangeEquiv p E 1).apply_symm_apply x)
    rw [← hz, ← pow_mul]
    congr 1
    rw [pow_one, ← pow_succ']
  rw [← h_tower, h_first]

/-- **The imperfection tower** `[K(E) : K(E)^{p^e}] = p^e` over a perfect base
field: induction on `e` with the tower step `finrank_iterFrobRange_succ`, the
`e = 1` case `finrank_KE_over_frobeniusRange_p` (`GapQfKernel.lean`), and the
trivial base `e = 0`. -/
theorem finrank_KE_over_iterateFrobeniusRange [PerfectField F] (e : ℕ) :
    Module.finrank ↥((iterateFrobenius KE p e).fieldRange) KE = p ^ e := by
  induction e with
  | zero =>
    have h0 : (iterateFrobenius (E.toAffine.FunctionField) p 0).fieldRange = ⊤ := by
      rw [iterateFrobenius_zero]
      exact eq_top_iff.mpr fun x _ ↦ RingHom.mem_fieldRange.mpr ⟨x, rfl⟩
    rw [finrank_subfield_congr h0, pow_zero]
    have htop := Algebra.finrank_eq_of_equiv_equiv
      (R₀ := ↥(⊤ : Subfield (E.toAffine.FunctionField)))
      (S₀ := E.toAffine.FunctionField)
      (R₁ := E.toAffine.FunctionField) (S₁ := E.toAffine.FunctionField)
      Subfield.topEquiv (RingEquiv.refl _) (by ext x; rfl)
    exact htop.trans (Module.finrank_self (E.toAffine.FunctionField))
  | succ e ih =>
    have h1 : Module.finrank
        ↥((iterateFrobenius (E.toAffine.FunctionField) p 1).fieldRange)
        (E.toAffine.FunctionField) = p := by
      rw [finrank_subfield_congr
        (congrArg RingHom.fieldRange (iterateFrobenius_one (E.toAffine.FunctionField) p))]
      exact finrank_KE_over_frobeniusRange_p E p
    rw [finrank_iterFrobRange_succ p E e, ih, h1, ← pow_succ']

/-- Finrank transport along an `IntermediateField.toSubfield` identification. -/
private theorem finrank_congr_toSubfield {K L : Type*} [Field K] [Field L] [Algebra K L]
    (IF : IntermediateField K L) (S : Subfield L) (h : IF.toSubfield = S) :
    Module.finrank ↥IF L = Module.finrank ↥S L := by
  subst h
  let i : (↥IF) ≃+* ↥(IF.toSubfield) :=
    { toFun := fun x ↦ ⟨x.1, (IntermediateField.mem_toSubfield IF x.1).mpr x.2⟩
      invFun := fun x ↦ ⟨x.1, (IntermediateField.mem_toSubfield IF x.1).mp x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  exact Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl L) (by ext x; rfl)

/-- **Item 4 (`e = 1`)**: the relative `p`-Frobenius has degree `p`, over a perfect
base. Via the range identification and `finrank_KE_over_frobeniusRange_p`. -/
theorem relativeFrobenius_degree_one [PerfectField F] :
    (EC.Isogeny.relativeFrobenius p E 1).degree = p := by
  have h1 : ((iterateFrobenius (E.toAffine.FunctionField) p 1).fieldRange :
      Subfield (E.toAffine.FunctionField)) = (frobenius (E.toAffine.FunctionField) p).fieldRange := by
    rw [iterateFrobenius_one]
  rw [EC.Isogeny.degree_eq_finrank_fieldRange,
    finrank_congr_toSubfield _ _ ((relativeFrobenius_fieldRange_toSubfield p E 1).trans h1)]
  exact finrank_KE_over_frobeniusRange_p E p

/-- **Item 4**: `deg Frob_{p^e} = p^e` over a perfect base, via
`finrank_KE_over_iterateFrobeniusRange`. -/
theorem relativeFrobenius_degree [PerfectField F] (e : ℕ) :
    (EC.Isogeny.relativeFrobenius p E e).degree = p ^ e := by
  rw [EC.Isogeny.degree_eq_finrank_fieldRange,
    finrank_congr_toSubfield _ _ (relativeFrobenius_fieldRange_toSubfield p E e)]
  exact finrank_KE_over_iterateFrobeniusRange p E e

end Degree

/-! ### Item 5: iteration (pullback-level composition law) -/

section Iteration

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [ExpChar F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- **Item 5 (composition on generators, `x`)**: composing the relative
`p^b`-Frobenius of the twist `E^{(p^a)}` with the relative `p^a`-Frobenius of `E`
acts on the generic `x`-coordinate exactly as the relative `p^{a+b}`-Frobenius:
the pullback image is `x_gen E^{p^{a+b}}`. This is the cast-free composition law. -/
theorem relativeFrobenius_compose_pullback_x_gen (a b : ℕ) :
    ((EC.Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).compose
        (EC.Isogeny.relativeFrobenius p E a)).toCurveMap.pullback
      (x_gen ((E.iterateFrobeniusTwist p a).iterateFrobeniusTwist p b)) =
    x_gen E ^ p ^ (a + b) := by
  show (EC.Isogeny.relativeFrobenius p E a).toCurveMap.pullback
    ((EC.Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).toCurveMap.pullback
      (x_gen ((E.iterateFrobeniusTwist p a).iterateFrobeniusTwist p b))) = _
  rw [relativeFrobenius_pullback_x_gen, map_pow, relativeFrobenius_pullback_x_gen,
    ← pow_mul, ← pow_add]

/-- **Item 5 (composition on generators, `y`)**. -/
theorem relativeFrobenius_compose_pullback_y_gen (a b : ℕ) :
    ((EC.Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).compose
        (EC.Isogeny.relativeFrobenius p E a)).toCurveMap.pullback
      (y_gen ((E.iterateFrobeniusTwist p a).iterateFrobeniusTwist p b)) =
    y_gen E ^ p ^ (a + b) := by
  show (EC.Isogeny.relativeFrobenius p E a).toCurveMap.pullback
    ((EC.Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).toCurveMap.pullback
      (y_gen ((E.iterateFrobeniusTwist p a).iterateFrobeniusTwist p b))) = _
  rw [relativeFrobenius_pullback_y_gen, map_pow, relativeFrobenius_pullback_y_gen,
    ← pow_mul, ← pow_add]

end Iteration

/-! ### Curve-equality transport (`congrTarget`) and the full iteration identity -/

section CongrTarget

variable {F : Type*} [Field F]

/-- Two `F`-algebra homs out of a Weierstrass function field agreeing on `x_gen`
and `y_gen` are equal. Fintype-free restatement of `algHom_ext_x_y_gen_omega`
(`GapSpines.lean`, whose section carries a `[Fintype K]`); same reduction chain
`IsLocalization.algHom_ext` → `AdjoinRoot.algHom_ext'` → `Polynomial.algHom_ext`. -/
theorem functionField_algHom_ext {V : WeierstrassCurve F} [V.toAffine.IsElliptic]
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ψ₁ ψ₂ : V.toAffine.FunctionField →ₐ[F] Ω}
    (hx : ψ₁ (x_gen V) = ψ₂ (x_gen V)) (hy : ψ₁ (y_gen V) = ψ₂ (y_gen V)) :
    ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors V.toAffine.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ V.toAffine.FunctionField (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ V.toAffine.FunctionField (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ V.toAffine.FunctionField (AdjoinRoot.root V.toAffine.polynomial)) =
      ψ₂ (algebraMap _ V.toAffine.FunctionField (AdjoinRoot.root V.toAffine.polynomial))
    exact hy

/-- Transport an `EC.Isogeny` along an equality of target curves. Term-level `cast`
(the type equality is closed by `subst` + proof-irrelevance of `IsElliptic`),
avoiding `▸`-motive issues on curve-indexed types. -/
noncomputable def EC.Isogeny.congrTarget {W₁ : Affine F} [W₁.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : EC.Isogeny W₁ V.toAffine) : EC.Isogeny W₁ V'.toAffine :=
  cast (by subst h; rfl) φ

@[simp] theorem EC.Isogeny.congrTarget_rfl {W₁ : Affine F} [W₁.IsElliptic]
    {V : WeierstrassCurve F} [V.toAffine.IsElliptic] (φ : EC.Isogeny W₁ V.toAffine) :
    EC.Isogeny.congrTarget rfl φ = φ := rfl

/-- The transported pullback agrees on the generic `x`-coordinate. -/
theorem EC.Isogeny.congrTarget_pullback_x_gen {W₁ : Affine F} [W₁.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : EC.Isogeny W₁ V.toAffine) :
    (EC.Isogeny.congrTarget h φ).toCurveMap.pullback (x_gen V') =
      φ.toCurveMap.pullback (x_gen V) := by
  subst h
  rfl

/-- The transported pullback agrees on the generic `y`-coordinate. -/
theorem EC.Isogeny.congrTarget_pullback_y_gen {W₁ : Affine F} [W₁.IsElliptic]
    {V V' : WeierstrassCurve F} [V.toAffine.IsElliptic] [V'.toAffine.IsElliptic]
    (h : V = V') (φ : EC.Isogeny W₁ V.toAffine) :
    (EC.Isogeny.congrTarget h φ).toCurveMap.pullback (y_gen V') =
      φ.toCurveMap.pullback (y_gen V) := by
  subst h
  rfl

end CongrTarget

section IterationFull

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [ExpChar F p]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- **Item 5 (full transported identity)**:
`Frob_{p^{a+b}} = (Frob_{p^b} of the twist) ∘ Frob_{p^a}`, after transporting along
the curve identification `(E^{(p^a)})^{(p^b)} = E^{(p^{a+b})}`. -/
theorem relativeFrobenius_add (a b : ℕ) :
    EC.Isogeny.congrTarget (iterateFrobeniusTwist_iterateFrobeniusTwist p E a b)
        ((EC.Isogeny.relativeFrobenius p (E.iterateFrobeniusTwist p a) b).compose
          (EC.Isogeny.relativeFrobenius p E a)) =
      EC.Isogeny.relativeFrobenius p E (a + b) := by
  refine EC.Isogeny.ext_toCurveMap (Curves.CurveMap.ext ?_)
  refine functionField_algHom_ext (V := E.iterateFrobeniusTwist p (a + b)) ?_ ?_
  · rw [EC.Isogeny.congrTarget_pullback_x_gen, relativeFrobenius_compose_pullback_x_gen,
      relativeFrobenius_pullback_x_gen]
  · rw [EC.Isogeny.congrTarget_pullback_y_gen, relativeFrobenius_compose_pullback_y_gen,
      relativeFrobenius_pullback_y_gen]

end IterationFull

/-! ### Item 6: `q`-power identification over a finite base -/

section QPowerIdentification

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (p s : ℕ) [Fact p.Prime] [CharP F p] [ExpChar F p]
variable [Fact (Fintype.card F = p ^ s)]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

omit [DecidableEq F] [Fact (Nat.Prime p)] [CharP F p] in
/-- The `(s·m)`-fold `p`-Frobenius on `F = 𝔽_{p^s}` is the identity
(`x^{q^m} = x`). -/
theorem iterateFrobenius_card_mul_eq_id (m : ℕ) :
    (iterateFrobenius F p (s * m) : F →+* F) = RingHom.id F := by
  ext x
  change iterateFrobenius F p (s * m) x = x
  rw [iterateFrobenius_def, pow_mul,
    show p ^ s = Fintype.card F from (Fact.out : Fintype.card F = p ^ s).symm]
  exact FiniteField.pow_card_pow m x

omit [DecidableEq F] [Fact (Nat.Prime p)] [CharP F p]
  [WeierstrassCurve.IsElliptic E.toAffine] in
/-- **Item 6 (curve level)**: over `F = 𝔽_q` with `q = p^s`, the `p^{s·m}`-twist is
the curve itself — the coefficients are `q`-power-fixed. -/
theorem iterateFrobeniusTwist_card_mul_eq_self (m : ℕ) :
    E.iterateFrobeniusTwist p (s * m) = E := by
  show E.map (iterateFrobenius F p (s * m)) = E
  rw [iterateFrobenius_card_mul_eq_id p s]
  exact E.map_id

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- **Item 6 (generator compatibility, `x`)**: the relative `p^{s·m}`-Frobenius and
the same-curve `q^m`-power Frobenius `EC.Isogeny.frobeniusPower` have the same
pullback image of the generic `x`-coordinate, namely `x_gen E^{q^m}`. -/
theorem relativeFrobenius_card_mul_pullback_x_gen (m : ℕ) :
    (EC.Isogeny.relativeFrobenius p E (s * m)).toCurveMap.pullback
        (x_gen (E.iterateFrobeniusTwist p (s * m))) =
      (EC.Isogeny.frobeniusPower E.toAffine m).toCurveMap.pullback (x_gen E) := by
  rw [relativeFrobenius_pullback_x_gen, EC.Isogeny.frobeniusPower_pullback,
    show Fintype.card F = p ^ s from Fact.out, ← pow_mul]

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- **Item 6 (full identification)**: over `F = 𝔽_q`, `q = p^s`, the relative
`p^{s·m}`-Frobenius, transported along the twist trivialisation, **is** the
same-curve `EC.Isogeny.frobeniusPower E m` (pullback `f ↦ f^{q^m}`). -/
theorem relativeFrobenius_card_mul_eq_frobeniusPower (m : ℕ) :
    EC.Isogeny.congrTarget (iterateFrobeniusTwist_card_mul_eq_self p s E m)
        (EC.Isogeny.relativeFrobenius p E (s * m)) =
      EC.Isogeny.frobeniusPower E.toAffine m := by
  refine EC.Isogeny.ext_toCurveMap (Curves.CurveMap.ext ?_)
  refine functionField_algHom_ext (V := E) ?_ ?_
  · rw [EC.Isogeny.congrTarget_pullback_x_gen, relativeFrobenius_pullback_x_gen,
      EC.Isogeny.frobeniusPower_pullback,
      show Fintype.card F = p ^ s from Fact.out, ← pow_mul]
  · rw [EC.Isogeny.congrTarget_pullback_y_gen, relativeFrobenius_pullback_y_gen,
      EC.Isogeny.frobeniusPower_pullback,
      show Fintype.card F = p ^ s from Fact.out, ← pow_mul]

end QPowerIdentification

end HasseWeil
