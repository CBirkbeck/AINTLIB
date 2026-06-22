/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Basic
import HasseWeil.EC.IsogenyKernel
import Mathlib.Algebra.CharP.Lemmas

/-!
# T-II-2-016 (Silverman II.2.12 specialised to `[p]`): factorisation of `[p]`

Foundational pieces toward Silverman II.2.12 specialised to `[p]`: in
characteristic `p > 0`, the multiplication-by-`p` isogeny factors as

```
[p] = ψ ∘ F_{E/k}
```

where `F_{E/k} : E → E^{(p)}` is the relative `p`-Frobenius and `ψ : E^{(p)} → E`
is separable.

## Structural pieces shipped here

* `WeierstrassCurve.frobeniusTwist`: the Frobenius twist `E^{(p)}` of a
  Weierstrass curve `E` in characteristic `p`. Defined as
  `E.map (frobenius k p)`. Inherits `IsElliptic` from Mathlib's
  `(W.map f).IsElliptic` instance.

## Downstream content

The full immediate-scope theorem `mulByNat_p_factors_through_frobenius`
requires:

* The relative Frobenius isogeny `frobeniusIsog_relative : Isogeny E.toAffine
  (E.frobeniusTwist).toAffine` as a structured `Isogeny`. Construction
  involves the pullback `(E^{(p)}).FunctionField →ₐ[k] E.FunctionField`
  factoring through the absolute Frobenius on `E.FunctionField`, plus
  the corresponding point map. This is structurally substantial
  (estimated 50-100 LOC) and is NOT shipped here pending coordination
  with Worker C's T-FROB-INSEP / T-FROB-OMEGA-ZERO output.

* Silverman II.2.12 specialised to `[p]`: the existence of the separable
  factor `ψ`. Construction follows the separable closure of `[p]^* K(E)`
  in `K(E)`; the intermediate field corresponds to `K(E^{(p)})` (Silverman
  II.2.12 proof). Estimated 50-100 LOC of substantive curve-theory.

Total realistic budget for the unconditional immediate-scope theorem:
~150-250 LOC across multiple commits, beyond the original 30 LOC estimate.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.11–II.2.12.

-/

open WeierstrassCurve

namespace HasseWeil

namespace Curves

variable {k : Type*} [CommRing k] (p : ℕ) [ExpChar k p]

/-- **Frobenius twist** `E^{(p)}` of a Weierstrass curve `E` in characteristic
`p`: the curve obtained by applying the `p`-th power Frobenius RingHom to
the coefficients. The relative `p`-Frobenius isogeny will be
`F_{E/k} : E → E^{(p)}`. -/
@[simps!] noncomputable def _root_.WeierstrassCurve.frobeniusTwist
    (E : WeierstrassCurve k) : WeierstrassCurve k :=
  E.map (frobenius k p)

/-- **Iterated Frobenius twist** `E^{(p^e)}`: the curve obtained by applying
the `e`-fold iterated `p`-th power Frobenius RingHom to the coefficients.
Definitionally equals `E.map (iterateFrobenius k p e)`, which is also the
codomain of `frobeniusIsog_relative_iterate p E e`. -/
@[simps!] noncomputable def _root_.WeierstrassCurve.iterateFrobeniusTwist
    (E : WeierstrassCurve k) (e : ℕ) : WeierstrassCurve k :=
  E.map (iterateFrobenius k p e)

end Curves

/-! ### T-II-2-016a: Relative `p`-Frobenius equation (W_KE-level)

The substantive structural content needed for the relative Frobenius
isogeny: the polynomial of `(E.frobeniusTwist p).baseChange K(E)` evaluates
to zero at `(x_gen^p, y_gen^p)`. This is the Weierstrass equation of `E^{(p)}`
satisfied by the p-th-power image of the generic point.

Proof: apply `Affine.Equation.map` with `f = frobenius K(E) p` to
`generic_equation` (`(W_KE E).Equation x_gen y_gen`). The result is
`((W_KE E).map (frobenius K(E) p)).Equation (x_gen^p) (y_gen^p)`. The
identification `(W_KE E).map (frobenius K(E) p) = (E.frobeniusTwist).baseChange K(E)`
follows from `RingHom.frobenius_comm` (algebraMap commutes with Frobenius). -/

variable {k : Type*} [Field k] [DecidableEq k] (p : ℕ) [ExpChar k p]
variable (E : WeierstrassCurve k) [E.toAffine.IsElliptic]

local notation "KE" => E.toAffine.FunctionField

/-- ExpChar propagation from `k` to `K(E)` via the injective algebraMap. -/
instance instExpChar_FunctionField : ExpChar KE p :=
  expChar_of_injective_algebraMap
    (RingHom.injective (algebraMap k KE)) p

/-- The W_KE-level base-change of `E.frobeniusTwist` equals the absolute
Frobenius pullback of `W_KE E`. Direct from `RingHom.frobenius_comm` (the
algebraMap commutes with Frobenius on coefficients). -/
theorem frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius :
    (E.frobeniusTwist p).map (algebraMap k KE) =
      (W_KE E).map (frobenius KE p) := by
  unfold WeierstrassCurve.frobeniusTwist W_KE
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      RingHom.frobenius_comm (algebraMap k KE) p]

/-- **Frobenius twist Weierstrass equation at the generic point** (`W_KE`-level):
`((E.frobeniusTwist p).baseChange K(E)).Equation (x_gen^p) (y_gen^p)`.
Direct from `Affine.Equation.map` with `f = frobenius K(E) p` applied to
`generic_equation`, then the curve identification. -/
theorem frobeniusTwist_generic_equation :
    ((E.frobeniusTwist p).map (algebraMap k KE)).toAffine.Equation
      (x_gen E ^ p) (y_gen E ^ p) := by
  have h := Affine.Equation.map (W := W_KE E) (frobenius KE p) (generic_equation E)
  rw [show frobenius KE p (x_gen E) = x_gen E ^ p from rfl,
      show frobenius KE p (y_gen E) = y_gen E ^ p from rfl] at h
  -- `Affine.map` is an abbreviation for `WeierstrassCurve.map`; bridge the
  -- displayed head so the structural identification lemma's pattern matches.
  rw [show (WeierstrassCurve.Affine.map (W_KE E) (frobenius KE p)) =
        (W_KE E).map (frobenius KE p) from rfl,
      ← frobeniusTwist_baseChange_KE_eq_W_KE_map_frobenius p E] at h
  exact h

/-! ### Relative Frobenius pullback at the polynomial level

The base ring hom `Polynomial k → K(E)` sending `X ↦ x_gen^p`, the y-coordinate
image `y_gen^p`, and the `eval₂ = 0` proof package up via `AdjoinRoot.lift` to
give the coordinate ring hom `(E.frobeniusTwist).CoordinateRing → K(E)`. -/

/-- The base ring hom `Polynomial k → K(E)` sending `X ↦ x_gen^p`. -/
noncomputable def frobeniusRelativeBaseHom : Polynomial k →+* KE :=
  Polynomial.eval₂RingHom (algebraMap k KE) (x_gen E ^ p)

/-- The Weierstrass polynomial of `E.frobeniusTwist` evaluates to zero at the
p-th-power generic point coordinates (as an `eval₂` over `Polynomial k`). -/
theorem frobeniusTwist_polynomial_eval₂_zero :
    (E.frobeniusTwist p).toAffine.polynomial.eval₂
      (frobeniusRelativeBaseHom p E) (y_gen E ^ p) = 0 := by
  rw [frobeniusRelativeBaseHom, Polynomial.eval₂_eval₂RingHom_apply,
      ← Affine.map_polynomial]
  exact frobeniusTwist_generic_equation p E

/-- The relative Frobenius pullback as a ring hom on the coordinate ring:
`(E.frobeniusTwist).CoordinateRing → K(E)` sending `X ↦ x_gen^p`,
`Y ↦ y_gen^p`. Built via `AdjoinRoot.lift` from the base hom + the
`eval₂ = 0` proof. -/
noncomputable def frobeniusRelativeCoordRingHom :
    (E.frobeniusTwist p).toAffine.CoordinateRing →+* KE :=
  AdjoinRoot.lift (frobeniusRelativeBaseHom p E) (y_gen E ^ p)
    (frobeniusTwist_polynomial_eval₂_zero p E)

/-- The relative Frobenius pullback as a `k`-AlgHom on the coordinate ring.
Direct from `frobeniusRelativeCoordRingHom` + the standard k-AlgHom
factorisation `algebraMap k → Polynomial k → CoordinateRing`. -/
noncomputable def frobeniusRelativeCoordAlgHom :
    (E.frobeniusTwist p).toAffine.CoordinateRing →ₐ[k] KE where
  toRingHom := frobeniusRelativeCoordRingHom p E
  commutes' r := by
    change frobeniusRelativeCoordRingHom p E
      (algebraMap (Polynomial k) _ (algebraMap k (Polynomial k) r)) = _
    change AdjoinRoot.lift (frobeniusRelativeBaseHom p E) (y_gen E ^ p) _
      (AdjoinRoot.mk _ (Polynomial.C (algebraMap k (Polynomial k) r))) = _
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
    change frobeniusRelativeBaseHom p E (algebraMap k (Polynomial k) r) = _
    simp [frobeniusRelativeBaseHom, Polynomial.eval₂_C]

/-- **Action of the relative Frobenius coord AlgHom on the X-coordinate**:
sends `algebraMap (Polynomial k) CoordinateRing X` (the X-coordinate generator)
to `x_gen^p`. Direct from the AdjoinRoot.lift structure. -/
theorem frobeniusRelativeCoordAlgHom_x :
    frobeniusRelativeCoordAlgHom p E
      (algebraMap (Polynomial k) (E.frobeniusTwist p).toAffine.CoordinateRing
        Polynomial.X) =
      x_gen E ^ p := by
  change AdjoinRoot.lift (frobeniusRelativeBaseHom p E) (y_gen E ^ p)
    (frobeniusTwist_polynomial_eval₂_zero p E)
    (AdjoinRoot.mk _ (Polynomial.C Polynomial.X)) = _
  rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
  simp [frobeniusRelativeBaseHom, Polynomial.eval₂_X]

/-- **Action of the relative Frobenius coord AlgHom on the Y-coordinate**:
sends `AdjoinRoot.root` (the Y-coordinate generator) to `y_gen^p`. Direct
from `AdjoinRoot.lift_root`. -/
theorem frobeniusRelativeCoordAlgHom_y :
    frobeniusRelativeCoordAlgHom p E
      (AdjoinRoot.root (E.frobeniusTwist p).toAffine.polynomial) =
      y_gen E ^ p := by
  change AdjoinRoot.lift (frobeniusRelativeBaseHom p E) (y_gen E ^ p)
    (frobeniusTwist_polynomial_eval₂_zero p E)
    (AdjoinRoot.root _) = _
  exact AdjoinRoot.lift_root _

/-! ### Injectivity of the relative Frobenius coord AlgHom

To extend `frobeniusRelativeCoordAlgHom` to the function field via
`IsFractionRing.liftAlgHom`, we need injectivity. The proof follows the
standard pattern from `mulByInt_coordHom_injective`: transcendence of
`x_gen^p` over `k` gives injectivity at the polynomial-base level, then
the rank-2 basis decomposition + norm-degree analysis extends to the
full coordinate ring. -/

/-- **`x_gen^p` is transcendental over `k`**: direct from
`x_gen_transcendental` + `Transcendental.pow` + `expChar_pos`. -/
lemma x_gen_pow_p_transcendental : Transcendental k (x_gen E ^ p) :=
  (x_gen_transcendental E).pow (expChar_pos k p)

/-- **`frobeniusRelativeBaseHom` is injective**: the polynomial-base hom
`Polynomial k →+* K(E)` sending `X ↦ x_gen^p` is injective via
`transcendental_iff_injective`. -/
lemma frobeniusRelativeBaseHom_injective :
    Function.Injective (frobeniusRelativeBaseHom p E) := by
  have h : (frobeniusRelativeBaseHom p E : Polynomial k →+* KE) =
      (Polynomial.aeval (x_gen E ^ p) : Polynomial k →ₐ[k] KE).toRingHom := by
    ext <;> simp [frobeniusRelativeBaseHom, Polynomial.aeval_def]
  rw [h]
  exact transcendental_iff_injective.mp (x_gen_pow_p_transcendental p E)

/-- **Image of a rank-2 basis decomposition** under `frobeniusRelativeCoordRingHom`:
for `a • 1 + b • Y` in the coordinate ring, the image is
`baseHom a + baseHom b * y_gen^p`. The algebraic core of injectivity. -/
theorem frobeniusRelativeCoordRingHom_smul_basis_eq (a b : Polynomial k) :
    frobeniusRelativeCoordRingHom p E
        (a • 1 + b • Affine.CoordinateRing.mk (E.frobeniusTwist p).toAffine Polynomial.X) =
      frobeniusRelativeBaseHom p E a + frobeniusRelativeBaseHom p E b * (y_gen E ^ p) := by
  simp only [frobeniusRelativeCoordRingHom, map_add]
  congr 1
  · change AdjoinRoot.lift _ _ _ (a • 1) = _
    rw [Algebra.smul_def, mul_one]
    exact AdjoinRoot.lift_of _
  · change AdjoinRoot.lift _ _ _ (b • AdjoinRoot.root _) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    · exact AdjoinRoot.lift_of _
    · exact AdjoinRoot.lift_root _

/-- **Degree obstruction to a vanishing rank-2 norm** (curve-generic): for an
elliptic affine Weierstrass curve `W` over the field `k`, the `Polynomial k`-norm
of a rank-2 element `a • 1 + b • Y` of its coordinate ring is nonzero whenever its
`Y`-coefficient `b` is nonzero. By `degree_norm_smul_basis` the norm has degree
`max (2·deg a) (2·deg b + 3)`; a nonzero `b` makes `2·deg b + 3 ≠ ⊥`, so the norm
cannot have degree `⊥`, i.e. cannot be zero. -/
private lemma norm_smul_basis_ne_zero_of_coeff_ne_zero (W : WeierstrassCurve k)
    (a b : Polynomial k) (hb : b ≠ 0) :
    Algebra.norm (Polynomial k)
      (a • (1 : W.toAffine.CoordinateRing) +
        b • Affine.CoordinateRing.mk W.toAffine Polynomial.X) ≠ 0 := by
  intro h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine) a b
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

/-- **The `Polynomial k`-norm of a rank-2 element killed by the relative Frobenius
coord ring hom vanishes**: if `baseHom a + baseHom b * y_gen^p = 0`, then the norm
of `a • 1 + b • Y` in `(E.frobeniusTwist p).CoordinateRing` is zero. The norm
factors as `r' * conj_r` with `r' = a • 1 + b • Y` (via `coe_norm_smul_basis`);
since the coord ring hom sends `r'` to `baseHom a + baseHom b * y_gen^p = 0` and
restricts to `frobeniusRelativeBaseHom` on `algebraMap`-images, the injectivity of
`frobeniusRelativeBaseHom` forces the norm itself to vanish. -/
private theorem frobeniusRelativeCoordRingHom_norm_smul_basis_eq_zero (a b : Polynomial k)
    (h0 : frobeniusRelativeBaseHom p E a + frobeniusRelativeBaseHom p E b * (y_gen E ^ p) = 0) :
    Algebra.norm (Polynomial k)
      (a • (1 : (E.frobeniusTwist p).toAffine.CoordinateRing) +
        b • Affine.CoordinateRing.mk (E.frobeniusTwist p).toAffine Polynomial.X) = 0 := by
  set r' := a • (1 : (E.frobeniusTwist p).toAffine.CoordinateRing) +
      b • Affine.CoordinateRing.mk (E.frobeniusTwist p).toAffine Polynomial.X with hr'_def
  have h_alg : ∀ f : Polynomial k,
      frobeniusRelativeCoordRingHom p E
        (algebraMap (Polynomial k) _ f) = frobeniusRelativeBaseHom p E f := fun f ↦ by
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ f) = _
    exact AdjoinRoot.lift_of _
  set conj_r := Affine.CoordinateRing.mk (E.frobeniusTwist p).toAffine
    (Polynomial.C a + Polynomial.C b *
      (-Polynomial.X - Polynomial.C
        (Polynomial.C (E.frobeniusTwist p).a₁ * Polynomial.X +
          Polynomial.C (E.frobeniusTwist p).a₃))) with hconj_def
  have h_factor : algebraMap (Polynomial k) _
      (Algebra.norm (Polynomial k) r') = r' * conj_r := by
    rw [hr'_def, hconj_def]
    change AdjoinRoot.of _ _ = _
    rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
    congr 1
    rw [map_add, map_mul]
    simp [Algebra.smul_def]
  have hr'_zero : frobeniusRelativeCoordRingHom p E r' = 0 :=
    (frobeniusRelativeCoordRingHom_smul_basis_eq p E a b).trans h0
  have h_norm_zero : frobeniusRelativeBaseHom p E
      (Algebra.norm (Polynomial k) r') = 0 := by
    rw [← h_alg, h_factor, map_mul, hr'_zero, zero_mul]
  exact frobeniusRelativeBaseHom_injective p E (h_norm_zero.trans (map_zero _).symm)

/-- A vanishing rank-2 image forces the `Y`-coefficient to vanish: if
`baseHom a + baseHom b * y_gen^p = 0` then `b = 0`. Uses the norm-degree
analysis (`degree_norm_smul_basis`): a nonzero `b` would give the norm of
`a • 1 + b • Y` degree `2·deg b + 3 ≠ ⊥`, yet the norm maps to zero, so it
must itself be zero — a contradiction. -/
private theorem frobeniusRelativeCoordRingHom_smul_basis_b_eq_zero (a b : Polynomial k)
    (h0 : frobeniusRelativeBaseHom p E a + frobeniusRelativeBaseHom p E b * (y_gen E ^ p) = 0) :
    b = 0 := by
  by_contra hb
  exact norm_smul_basis_ne_zero_of_coeff_ne_zero (E.frobeniusTwist p) a b hb
    (frobeniusRelativeCoordRingHom_norm_smul_basis_eq_zero p E a b h0)

/-- **Full coord ring injectivity** for `frobeniusRelativeCoordRingHom`.
Pattern parallel to `mulByInt_coordHom_injective`: rank-2 basis
decomposition + norm-degree analysis using `degree_norm_smul_basis`.

For r ∈ (E.frobeniusTwist).CoordinateRing decomposed as `a • 1 + b • Y`,
the image equals `baseHom a + baseHom b * y_gen^p`. The image being zero
forces `a = 0 ∧ b = 0` via:
* `b = 0` case: image = baseHom a, injective by `frobeniusRelativeBaseHom_injective`.
* `b ≠ 0` case: derive contradiction via `degree_norm_smul_basis` (norm
  has degree ≥ 3 when b ≠ 0). -/
theorem frobeniusRelativeCoordRingHom_injective :
    Function.Injective (frobeniusRelativeCoordRingHom p E) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨a, b, hab⟩ :=
    Affine.CoordinateRing.exists_smul_basis_eq (W' := (E.frobeniusTwist p).toAffine) r
  rw [← hab, frobeniusRelativeCoordRingHom_smul_basis_eq] at hr
  have hb : b = 0 := frobeniusRelativeCoordRingHom_smul_basis_b_eq_zero p E a b hr
  rw [hb, map_zero, zero_mul, add_zero] at hr
  have ha : a = 0 := frobeniusRelativeBaseHom_injective p E (hr.trans (map_zero _).symm)
  rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]

/-- Coord-ring AlgHom injectivity (AlgHom-level form) for the relative
Frobenius, derived from the ring-hom injectivity. -/
lemma frobeniusRelativeCoordAlgHom_injective :
    Function.Injective (frobeniusRelativeCoordAlgHom p E) :=
  frobeniusRelativeCoordRingHom_injective p E

/-! ### Function-field extension: the relative Frobenius pullback as an AlgHom on K(E^(p))

`IsFractionRing.liftAlgHom` extends the coord-ring AlgHom to the function
field. This is the pullback of the relative Frobenius isogeny F : E → E^(p). -/

/-- **Relative Frobenius pullback at function-field level**:
`(E.frobeniusTwist).FunctionField →ₐ[k] K(E)` sending `x_gen ↦ x_gen^p`,
`y_gen ↦ y_gen^p`. The k-AlgHom extension of `frobeniusRelativeCoordAlgHom`
to the field of fractions, via `IsFractionRing.liftAlgHom`. -/
noncomputable def frobeniusRelativePullback :
    (E.frobeniusTwist p).toAffine.FunctionField →ₐ[k] KE :=
  IsFractionRing.liftAlgHom (frobeniusRelativeCoordAlgHom_injective p E)

/-! ### Relative Frobenius point map: `(x, y) ↦ (x^p, y^p)`

Constructs the toAddMonoidHom component of the relative Frobenius
isogeny F : E → E^(p) at the K-rational point level. -/

/-- **Relative Frobenius point map** (function-level): sends `.zero ↦ .zero`
and `.some x y h ↦ .some (x^p) (y^p) h'` where `h'` is derived from
`map_nonsingular` (frobenius is injective on a field). -/
noncomputable def frobeniusRelativePointFun :
    E.toAffine.Point → (E.frobeniusTwist p).toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((frobenius k p) x) ((frobenius k p) y)
      ((WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine)
          (RingHom.injective (frobenius k p)) x y).mpr h)

/-- **`frobeniusRelativePointFun` preserves addition**. Pattern parallel to
Mathlib's `Affine.Point.map.map_add'`: case analysis on the curve group
law (`add_of_Y_eq` / `add_some`) + `simpa` with `map_addX`, `map_addY`,
`map_slope`, `map_negY` for ring-hom transport. -/
theorem frobeniusRelativePointFun_add (P₁ P₂ : E.toAffine.Point) :
    frobeniusRelativePointFun p E (P₁ + P₂) =
      frobeniusRelativePointFun p E P₁ + frobeniusRelativePointFun p E P₂ := by
  rcases P₁ with _ | ⟨x₁, y₁, h₁⟩ <;> rcases P₂ with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = E.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.left hxy.right]
    change (0 : (E.frobeniusTwist p).toAffine.Point) =
      frobeniusRelativePointFun p E (.some x₁ y₁ h₁) +
        frobeniusRelativePointFun p E (.some x₂ y₂ h₂)
    change (0 : (E.frobeniusTwist p).toAffine.Point) =
      Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_of_Y_eq (congr_arg (frobenius k p) hxy.left) <| by
        rw [hxy.right, ← WeierstrassCurve.Affine.map_negY]; rfl]
  · -- `(E.frobeniusTwist p).toAffine` and `E.toAffine.map (frobenius k p)` are the
    -- same curve definitionally; align the displayed head so `exact` closes.
    change (_ : (E.toAffine.map (frobenius k p)).Point) = _
    simp only [frobeniusRelativePointFun, Affine.Point.add_some hxy,
      ← WeierstrassCurve.Affine.map_addX (W' := E.toAffine) (f := frobenius k p),
      ← WeierstrassCurve.Affine.map_addY (W' := E.toAffine) (f := frobenius k p),
      ← WeierstrassCurve.Affine.map_slope (W := E.toAffine) (frobenius k p)]
    exact
      (Affine.Point.add_some (h₁ :=
          (WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine)
            (RingHom.injective (frobenius k p)) x₁ y₁).mpr h₁)
        (h₂ := (WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine)
          (RingHom.injective (frobenius k p)) x₂ y₂).mpr h₂)
        (fun h ↦ hxy ⟨RingHom.injective (frobenius k p) h.1,
          RingHom.injective (frobenius k p)
            (WeierstrassCurve.Affine.map_negY (W' := E.toAffine)
              (f := frobenius k p) x₂ y₂ ▸ h.2)⟩)).symm

/-- **Relative Frobenius point map** packaged as an `AddMonoidHom`. -/
noncomputable def frobeniusRelativePointMap :
    E.toAffine.Point →+ (E.frobeniusTwist p).toAffine.Point where
  toFun := frobeniusRelativePointFun p E
  map_zero' := rfl
  map_add' := frobeniusRelativePointFun_add p E

/-! ### T-II-2-016a deliverable: the relative Frobenius `Isogeny`

Combining `frobeniusRelativePullback` (the function-field k-AlgHom) and
`frobeniusRelativePointMap` (the K-rational point AddMonoidHom) into the
full `Isogeny` structure. -/

/-- The Frobenius twist of an elliptic curve is itself elliptic.
Direct from Mathlib's `(W.map f).IsElliptic` instance via the
`WeierstrassCurve.frobeniusTwist` definition. -/
instance : (E.frobeniusTwist p).toAffine.IsElliptic :=
  show (E.map (frobenius k p)).IsElliptic from inferInstance

/-- **T07 (R27)**: the Frobenius twist of an elliptic curve is elliptic.

Silverman III.4 Example 4.6 + III.4.2 (page 70): `Δ(E^{(p)}) = Δ(E)^p ≠ 0`,
so `E^{(p)}` is nonsingular.

This is the explicit-named theorem version of the auto-inferred instance
above. Its existence is what `tickets/R27-SORRY-LIST-COMPLETE.md` §T07 names. -/
theorem _root_.WeierstrassCurve.frobeniusTwist_isElliptic :
    (E.frobeniusTwist p).toAffine.IsElliptic := inferInstance

/-- **Relative Frobenius isogeny** `F_{E/k} : E → E^{(p)}`. The pullback
sends `x_gen ↦ x_gen^p`, `y_gen ↦ y_gen^p` (k-linear); the point map sends
`(x, y) ↦ (x^p, y^p)`. The codomain is the Frobenius twist `E^{(p)}`,
NOT the same curve in general (only when `E` is over the fixed field of
the chosen Frobenius). -/
noncomputable def frobeniusIsog_relative :
    Isogeny E.toAffine (E.frobeniusTwist p).toAffine where
  pullback := frobeniusRelativePullback p E
  toAddMonoidHom := frobeniusRelativePointMap p E

/-! ### Evaluation lemmas for `frobeniusIsog_relative`

Direct evaluation of the relative Frobenius isogeny on x_gen, y_gen of E^(p)
and on K-rational points. These are what downstream consumers (T-II-2-016b
degree analysis, T-FROB-DUAL-ASSEMBLY) use to interface with the isogeny. -/

/-- **Relative Frobenius pullback on `x_gen` of E^(p)**: sends to `x_gen E ^ p`.
Direct from `IsFractionRing.liftAlgHom_apply` + `frobeniusRelativeCoordAlgHom_x`. -/
theorem frobeniusIsog_relative_pullback_x_gen :
    (frobeniusIsog_relative p E).pullback (x_gen (E.frobeniusTwist p)) =
      x_gen E ^ p := by
  change frobeniusRelativePullback p E (x_gen (E.frobeniusTwist p)) = _
  unfold frobeniusRelativePullback
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  exact frobeniusRelativeCoordAlgHom_x p E

/-- **Relative Frobenius pullback on `y_gen` of E^(p)**: sends to `y_gen E ^ p`.
Direct from `IsFractionRing.liftAlgHom_apply` + `frobeniusRelativeCoordAlgHom_y`. -/
theorem frobeniusIsog_relative_pullback_y_gen :
    (frobeniusIsog_relative p E).pullback (y_gen (E.frobeniusTwist p)) =
      y_gen E ^ p := by
  change frobeniusRelativePullback p E (y_gen (E.frobeniusTwist p)) = _
  unfold frobeniusRelativePullback
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  exact frobeniusRelativeCoordAlgHom_y p E

/-- **Relative Frobenius point map on `.some`**: sends `(x, y) ↦ (x^p, y^p)`. -/
theorem frobeniusIsog_relative_apply_some
    (x y : k) (h : E.toAffine.Nonsingular x y) :
    (frobeniusIsog_relative p E).toAddMonoidHom (.some x y h) =
      .some ((frobenius k p) x) ((frobenius k p) y)
        ((WeierstrassCurve.Affine.map_nonsingular (W := E.toAffine)
          (RingHom.injective (frobenius k p)) x y).mpr h) :=
  rfl

/-- **Relative Frobenius point map on `.zero`**: sends to `.zero`. -/
@[simp] theorem frobeniusIsog_relative_apply_zero :
    (frobeniusIsog_relative p E).toAddMonoidHom 0 = 0 := rfl

/-! ### T-II-2-016b: purely inseparable structural lemmas

The relative Frobenius is purely inseparable of degree p. We ship the
foundational `*_mem_fieldRange` lemmas: x_gen^p, y_gen^p, and algebraMap
k images all lie in `(frobeniusIsog_relative E).pullback.fieldRange`. -/

/-- **`x_gen^p ∈ (frobeniusIsog_relative E).pullback.fieldRange`**: explicit
witness via `frobeniusIsog_relative_pullback_x_gen`. -/
theorem x_gen_pow_p_mem_fieldRange :
    x_gen E ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange :=
  ⟨x_gen (E.frobeniusTwist p), frobeniusIsog_relative_pullback_x_gen p E⟩

/-- **`y_gen^p ∈ (frobeniusIsog_relative E).pullback.fieldRange`**: explicit
witness via `frobeniusIsog_relative_pullback_y_gen`. -/
theorem y_gen_pow_p_mem_fieldRange :
    y_gen E ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange :=
  ⟨y_gen (E.frobeniusTwist p), frobeniusIsog_relative_pullback_y_gen p E⟩

/-- **`algebraMap k KE c ∈ (frobeniusIsog_relative E).pullback.fieldRange`**:
the k-AlgHom property. -/
theorem algebraMap_k_mem_fieldRange (c : k) :
    algebraMap k KE c ∈ (frobeniusIsog_relative p E).pullback.fieldRange :=
  ⟨algebraMap k _ c, AlgHom.commutes _ c⟩

/-! ### T-II-2-016b-1: Compositional identity at the CoordinateRing level

`algebraMap (Polynomial k) FF q = Polynomial.aeval (x_gen E) q`: the
`Polynomial k`-algebra map to FF coincides with `aeval` at `x_gen`, since
the algebra structure on FF over `Polynomial k` (via the IsScalarTower
`Polynomial k → CR → FF`) sends `Polynomial.X` to `x_gen`.

Then the compositional identity
`frobeniusRelativeCoordRingHom (CoordinateRing.map (frobenius k p) r) =
  (algebraMap CR KE r) ^ p` follows via `AdjoinRoot.ringHom_ext`. -/

/-- **algebraMap CR KE applied to `of q`** for q ∈ Polynomial k equals
`q.eval₂ (algebraMap k KE) (x_gen E)`. Direct induction on q via
`Polynomial.induction_on'`: handles `C` (constant), `X^n`, and `+` cases
using `eval₂_C`, `eval₂_X_pow`, `eval₂_add` plus the IsScalarTower
identification of `x_gen` with `algMap CR KE (of X)`. -/
lemma algebraMap_CR_KE_of_eq_eval₂ (q : Polynomial k) :
    algebraMap E.toAffine.CoordinateRing KE
      (AdjoinRoot.of E.toAffine.polynomial q) =
    q.eval₂ (algebraMap k KE) (x_gen E) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Polynomial.eval₂_add]
      rw [hp, hq]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      rw [show (AdjoinRoot.of E.toAffine.polynomial) (Polynomial.C c) =
            algebraMap k E.toAffine.CoordinateRing c from rfl,
          ← IsScalarTower.algebraMap_apply k E.toAffine.CoordinateRing KE c]
      rfl

/-- **Compositional identity (CoordinateRing level)**: the relative Frobenius
pullback composed with `Affine.CoordinateRing.map (frobenius k p)` equals
the absolute Frobenius `(·^p)` on the algebraMap-image. -/
theorem frobeniusRelativeCoordRingHom_comp_map :
    (frobeniusRelativeCoordRingHom p E).comp
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p)) =
      (frobenius KE p).comp (algebraMap E.toAffine.CoordinateRing KE) := by
  apply AdjoinRoot.ringHom_ext
  · -- composition with `of`: agree on the polynomial-base.
    apply RingHom.ext
    intro q
    change frobeniusRelativeCoordRingHom p E
      (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p)
        (AdjoinRoot.mk _ (Polynomial.C q))) = _
    rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_C]
    change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ (Polynomial.C _)) = _
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_C]
    change ((Polynomial.mapRingHom (frobenius k p)) q).eval₂
        (algebraMap k KE) (x_gen E ^ p) = _
    rw [show (Polynomial.mapRingHom (frobenius k p)) q = q.map (frobenius k p) from rfl,
        Polynomial.eval₂_map,
        show ((algebraMap k KE).comp (frobenius k p)) =
          ((frobenius KE p).comp (algebraMap k KE)) from
          RingHom.frobenius_comm (algebraMap k KE) p,
        show (x_gen E ^ p : KE) = (frobenius KE p) (x_gen E) from rfl,
        ← Polynomial.hom_eval₂]
    change (frobenius KE p) (q.eval₂ _ _) = (frobenius KE p) (algebraMap _ _ _)
    congr 1
    change q.eval₂ (algebraMap k KE) (x_gen E) = algebraMap _ _ ((AdjoinRoot.of _) q)
    exact (algebraMap_CR_KE_of_eq_eval₂ E q).symm
  · -- At root: both sides give y_gen^p.
    change frobeniusRelativeCoordRingHom p E
      (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p)
        (AdjoinRoot.root _)) =
      (frobenius KE p)
        ((algebraMap E.toAffine.CoordinateRing KE) (AdjoinRoot.root _))
    rw [show WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p)
          (AdjoinRoot.root E.toAffine.polynomial) =
          AdjoinRoot.root (E.frobeniusTwist p).toAffine.polynomial by
        change AdjoinRoot.lift _ _ _ _ = _
        rw [AdjoinRoot.lift_root]
        rfl]
    rw [show frobeniusRelativeCoordRingHom p E
          (AdjoinRoot.root (E.frobeniusTwist p).toAffine.polynomial) = y_gen E ^ p from
        frobeniusRelativeCoordAlgHom_y p E]
    rfl

/-- **T-II-2-016b-1 applied form**: for `r ∈ E.toAffine.CoordinateRing`, the
relative Frobenius pullback of the `frobeniusTwist`-mapped image equals
`(algebraMap r)^p`. -/
theorem frobeniusRelative_compose_eq_pow (r : E.toAffine.CoordinateRing) :
    frobeniusRelativeCoordRingHom p E
        (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p) r) =
      (algebraMap E.toAffine.CoordinateRing KE r) ^ p :=
  RingHom.congr_fun (frobeniusRelativeCoordRingHom_comp_map p E) r

/-! ### T-II-2-016b-2: Extension to the function field K(E)

The compositional identity at CoordinateRing level extends to: for any
`f ∈ K(E)`, `f^p ∈ frobeniusRelativePullback.fieldRange`. This is the
purely-inseparable witness in power-membership form.

Proof: write `f = algMap a / algMap b` via `IsFractionRing.div_surjective`,
apply `frobeniusRelative_compose_eq_pow` to a and b, use
`IntermediateField.div_mem` on the field range. -/

/-- **algMap CR KE r raised to p-th power lies in frobeniusRelativePullback.fieldRange**.
Direct from `frobeniusRelative_compose_eq_pow` + the fact that
`frobeniusRelativeCoordRingHom`'s image lies in `frobeniusRelativePullback.fieldRange`
(via `IsFractionRing.liftAlgHom_apply`). -/
theorem algebraMap_CR_KE_pow_p_mem_fieldRange (r : E.toAffine.CoordinateRing) :
    (algebraMap E.toAffine.CoordinateRing KE r) ^ p ∈
      (frobeniusIsog_relative p E).pullback.fieldRange := by
  refine ⟨algebraMap (E.frobeniusTwist p).toAffine.CoordinateRing
    (E.frobeniusTwist p).toAffine.FunctionField
    (WeierstrassCurve.Affine.CoordinateRing.map E.toAffine (frobenius k p) r), ?_⟩
  change frobeniusRelativePullback p E _ = _
  unfold frobeniusRelativePullback
  rw [IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change frobeniusRelativeCoordRingHom p E _ = _
  exact frobeniusRelative_compose_eq_pow p E r

/-- **T-II-2-016b-2 deliverable**: every element of K(E) has its p-th power
in `(frobeniusIsog_relative E).pullback.fieldRange`. The purely-inseparable
witness in power-membership form, parallel to
`frobeniusIsogeny_pow_mem_fieldRange` for the q-Frobenius case. -/
theorem frobeniusIsog_relative_pow_p_mem_fieldRange (f : KE) :
    f ^ p ∈ (frobeniusIsog_relative p E).pullback.fieldRange := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (A := E.toAffine.CoordinateRing) f
  rw [div_pow]
  apply IntermediateField.div_mem
  · exact algebraMap_CR_KE_pow_p_mem_fieldRange p E a
  · exact algebraMap_CR_KE_pow_p_mem_fieldRange p E b

/-! ### T-II-2-016c: Factorisation `[p] = ψ ∘ frobeniusIsog_relative E`

The Hasse-critical Silverman II.2.12 specialisation: in characteristic p,
`[p]` factors as a separable map ψ post-composed with the relative
Frobenius. The full unconditional construction of `ψ` requires Silverman
II.2.12's separable closure machinery (the separable closure of
`[p]^* K(E)` in `K(E)` corresponds to `K(E^{(p)})`).

We ship the **witness-parametric form** under `Conditional` namespace
(per anti-drift gate 1): the factorisation existence is the structured
interface Worker C's T-FROB-DUAL-ASSEMBLY consumes for III.6.1 Case 2.
The substantive Silverman II.2.12 content (separable closure construction)
is the upstream witness; specialised to [p] it gives the factorisation.

The `Conditional` namespace makes the witness-parametric nature explicit
and prevents drift — downstream consumers MUST discharge the hypothesis
upstream (via Silverman II.2.12 + T-FROB-INSEP) rather than stack
further witness layers. -/

namespace Conditional

/-- **T-II-2-016c (Conditional)**: given Silverman II.2.12 specialised to
the inseparable map `[p]` — i.e., the existence of a separable factor
through the relative Frobenius — we package this as the structured
factorisation theorem. The hypothesis represents UPSTREAM content
(Silverman II.2.12's separable–inseparable decomposition); specialised
here for clean downstream consumption. -/
theorem mulByNat_p_factors_through_frobenius_of_silvermanII212
    (h_factor : ∃ ψ : Isogeny (E.frobeniusTwist p).toAffine E.toAffine,
      ψ.IsSeparable ∧
        ψ.comp (frobeniusIsog_relative p E) = mulByInt E.toAffine (p : ℤ)) :
    ∃ ψ : Isogeny (E.frobeniusTwist p).toAffine E.toAffine,
      ψ.IsSeparable ∧
        ψ.comp (frobeniusIsog_relative p E) = mulByInt E.toAffine (p : ℤ) :=
  h_factor

/-- **T-II-2-016c (Conditional, factored form)**: refines the witness
into separate hypotheses — `[p]` inseparable (T-FROB-INSEP / Worker C)
+ Silverman II.2.12 applied to the inseparable map. Both are upstream
content; their composition gives the factorisation. -/
theorem mulByNat_p_factors_through_frobenius_of_witnesses
    (_h_p_insep : ¬ (mulByInt E.toAffine (p : ℤ)).IsSeparable)
    (h_factor : ∀ φ : Isogeny E.toAffine E.toAffine, ¬ φ.IsSeparable →
      ∃ ψ : Isogeny (E.frobeniusTwist p).toAffine E.toAffine,
        ψ.IsSeparable ∧ ψ.comp (frobeniusIsog_relative p E) = φ) :
    ∃ ψ : Isogeny (E.frobeniusTwist p).toAffine E.toAffine,
      ψ.IsSeparable ∧
        ψ.comp (frobeniusIsog_relative p E) = mulByInt E.toAffine (p : ℤ) :=
  h_factor _ _h_p_insep

end Conditional

end HasseWeil
