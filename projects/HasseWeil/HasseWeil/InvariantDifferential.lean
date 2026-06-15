import HasseWeil.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Unramified.Field

/-!
# The Invariant Differential

We define the invariant differential ω = dx/(2y + a₁x + a₃) on an elliptic curve
and the pullback coefficient map End(E) → K.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.1.5, III.5
-/

open WeierstrassCurve Polynomial.Bivariate

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Helper lemmas for the invariant differential -/

/-- The partial derivative `polynomialY = 2Y + a₁X + a₃` of the Weierstrass polynomial with
respect to `Y` is nonzero for elliptic curves. In characteristic 2, this uses `Δ ≠ 0`. -/
private lemma polynomialY_ne_zero (E : Affine F) [E.IsElliptic] : E.polynomialY ≠ 0 := by
  intro h; rw [Affine.polynomialY] at h
  have h1 := congr_arg (fun p => p.coeff 1) h
  have h0 := congr_arg (fun p => p.coeff 0) h
  simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C] at h1 h0
  have ha1 : E.a₁ = 0 := by
    have := congr_arg (fun p => p.coeff 1) h0; simp at this; exact this
  have ha3 : E.a₃ = 0 := by
    have := congr_arg (fun p => p.coeff 0) h0; simp at this; exact this
  exact absurd ((show WeierstrassCurve.Δ E = 0 by
    simp only [WeierstrassCurve.Δ]; rw [show WeierstrassCurve.b₂ E = 0 by
      simp only [WeierstrassCurve.b₂, ha1]; linear_combination 2 * E.a₂ * h1,
      show WeierstrassCurve.b₄ E = 0 by
      simp only [WeierstrassCurve.b₄, ha1, ha3]; linear_combination E.a₄ * h1,
      show WeierstrassCurve.b₆ E = 0 by
      simp only [WeierstrassCurve.b₆, ha3]; linear_combination 2 * E.a₆ * h1]; ring) ▸ E.isUnit_Δ)
    not_isUnit_zero

/-- The algebra map `F[X] → K(E)` is injective since `x` is transcendental over `F`. -/
private lemma algebraMap_polynomial_injective (E : Affine F) [E.IsElliptic] :
    Function.Injective (algebraMap (Polynomial F) E.FunctionField) := by
  rw [IsScalarTower.algebraMap_eq (Polynomial F) E.CoordinateRing E.FunctionField]
  refine (IsFractionRing.injective E.CoordinateRing E.FunctionField).comp ?_
  intro p q (h : algebraMap _ E.CoordinateRing p = algebraMap _ E.CoordinateRing q)
  by_contra hpq
  have h' : algebraMap (Polynomial F) E.CoordinateRing (p - q) = 0 := by
    rw [map_sub, sub_eq_zero, h]
  have hle := Polynomial.natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp h')
    (Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hpq))
  have : (algebraMap (Polynomial F) (Polynomial (Polynomial F)) (p - q)).natDegree = 0 :=
    Polynomial.natDegree_C _
  rw [Affine.natDegree_polynomial] at hle; omega

/-- Evaluating a polynomial at `x = algebraMap X` in `K(E)` equals applying `algebraMap`. -/
private lemma aeval_x_eq_algebraMap' (E : Affine F) (p : Polynomial F) :
    Polynomial.aeval (algebraMap (Polynomial F) E.FunctionField Polynomial.X) p =
    algebraMap (Polynomial F) E.FunctionField p := by
  induction p using Polynomial.induction_on' with
  | add _ _ hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial]
    show (algebraMap (Polynomial F) E.FunctionField (Polynomial.C a)) *
      (algebraMap (Polynomial F) E.FunctionField Polynomial.X) ^ n =
      algebraMap (Polynomial F) E.FunctionField ((Polynomial.monomial n) a)
    rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

/-- The coordinate `x` is not algebraic over `F` in the function field `K(E)`. -/
private lemma not_isAlgebraic_x (E : Affine F) [E.IsElliptic] :
    ¬ IsAlgebraic F (algebraMap (Polynomial F) E.FunctionField Polynomial.X) := by
  intro ⟨p, hp_ne, hp_eval⟩
  exact hp_ne (algebraMap_polynomial_injective E
    ((aeval_x_eq_algebraMap' E p).symm.trans hp_eval |>.trans (map_zero _).symm))

set_option maxHeartbeats 3200000 in
/-- `D(x) ≠ 0` in `Ω[K(E)/F]`. The proof assumes `D(x) = 0` and derives that `Ω = 0`
(hence `K(E)/F` is formally unramified, hence separable algebraic), contradicting
`x` being transcendental over `F`. The key step uses the Weierstrass relation:
differentiating `W(x,y) = 0` with `D(x) = 0` gives `W_Y · D(y) = 0`, and since
`W_Y ≠ 0` in `K(E)` (a field), `D(y) = 0`. Then `D` vanishes on all of `K(E)`. -/
lemma D_x_ne_zero (E : Affine F) [E.IsElliptic] :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)) ≠ 0 := by
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
  intro hDx
  have hΩ : Subsingleton (KaehlerDifferential F E.FunctionField) := by
    set D := KaehlerDifferential.D F E.FunctionField
    set x := algebraMap (Polynomial F) E.FunctionField Polynomial.X
    set y : E.FunctionField :=
      algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)
    have hDpoly : ∀ p : Polynomial F, D (algebraMap (Polynomial F) E.FunctionField p) = 0 := by
      intro p
      have hxn : ∀ n : ℕ, D (x ^ n) = 0 := by
        intro n; induction n with
        | zero => simp [Derivation.map_one_eq_zero]
        | succ n ih =>
          rw [pow_succ, Derivation.leibniz, ih, smul_zero, hDx, smul_zero, add_zero]
      have haeval : ∀ q : Polynomial F,
          Polynomial.aeval x q = algebraMap (Polynomial F) E.FunctionField q := by
        intro q; induction q using Polynomial.induction_on' with
        | add _ _ hp hq => simp [hp, hq]
        | monomial n a =>
          simp only [Polynomial.aeval_monomial]
          show algebraMap (Polynomial F) E.FunctionField (Polynomial.C a) *
            (algebraMap (Polynomial F) E.FunctionField Polynomial.X) ^ n =
            algebraMap (Polynomial F) E.FunctionField (Polynomial.monomial n a)
          rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [← haeval]; induction p using Polynomial.induction_on' with
      | add _ _ hp hq => rw [map_add, map_add, hp, hq, add_zero]
      | monomial n a =>
        rw [Polynomial.aeval_monomial, Derivation.leibniz, Derivation.map_algebraMap, smul_zero,
          add_zero, show D (x ^ n) = 0 from hxn n, smul_zero]
    have hDy : D y = 0 := by
      set c := algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
      have hW_coord : (AdjoinRoot.root E.polynomial) ^ 2 +
          algebraMap (Polynomial F) E.CoordinateRing
            (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) *
          AdjoinRoot.root E.polynomial =
          algebraMap (Polynomial F) E.CoordinateRing
            (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
             Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) := by
        have Y_sq : (AdjoinRoot.mk E.polynomial) Y ^ 2 =
          (AdjoinRoot.mk E.polynomial) (Polynomial.C (Polynomial.X ^ 3 + Polynomial.C E.a₂ *
            Polynomial.X ^ 2 + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) -
          Polynomial.C (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) * Y) :=
          AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [Affine.polynomial]; ring1⟩
        rw [AdjoinRoot.mk_X] at Y_sq
        simp only [map_sub, map_mul, AdjoinRoot.mk_X] at Y_sq
        have hcc : ∀ p : Polynomial F, AdjoinRoot.mk E.polynomial (Polynomial.C p) =
          algebraMap (Polynomial F) E.CoordinateRing p := fun _ => rfl
        rw [hcc, hcc] at Y_sq; linear_combination Y_sq
      have hW_FF : y ^ 2 + c * y = algebraMap (Polynomial F) E.FunctionField
          (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
           Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) := by
        have h := congr_arg (algebraMap E.CoordinateRing E.FunctionField) hW_coord
        rw [map_add, map_mul, map_pow] at h
        rwa [← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
          ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField] at h
      have hsmul : (2 * y + c) • D y = 0 := by
        have hD_lhs : D (y ^ 2 + c * y) = (2 * y + c) • D y := by
          rw [map_add, sq, Derivation.leibniz, Derivation.leibniz,
            show D c = 0 from hDpoly _, smul_zero, add_zero, add_smul, two_mul, add_smul]
        rw [← hD_lhs, hW_FF]; exact hDpoly _
      have hne : 2 * y + c ≠ 0 := by
        have hmk_ne : Affine.CoordinateRing.mk E E.polynomialY ≠ 0 :=
          AdjoinRoot.mk_ne_zero_of_natDegree_lt (Affine.monic_polynomial)
            (polynomialY_ne_zero E) (by
              rw [Affine.natDegree_polynomial, Affine.polynomialY]
              have : (Polynomial.C (Polynomial.C (2 : F)) * (Y : F[X][Y])).natDegree ≤ 1 :=
                Polynomial.natDegree_mul_le.trans
                  (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
              exact Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
                (by rw [Polynomial.natDegree_C]; omega))
        have hmk_eq : algebraMap E.CoordinateRing E.FunctionField
            (Affine.CoordinateRing.mk E E.polynomialY) = 2 * y + c := by
          have hmk : (Affine.CoordinateRing.mk E E.polynomialY : E.CoordinateRing) =
            algebraMap (Polynomial F) E.CoordinateRing (Polynomial.C 2) *
              AdjoinRoot.root E.polynomial +
            algebraMap (Polynomial F) E.CoordinateRing
              (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
            show AdjoinRoot.mk E.polynomial E.polynomialY = _
            rw [Affine.polynomialY, map_add, map_mul, AdjoinRoot.mk_X]; rfl
          rw [hmk, map_add, map_mul,
            ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
            ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
          congr 1; congr 1
          rw [show (Polynomial.C (2 : F) : Polynomial F) = algebraMap F (Polynomial F) 2
                from rfl,
            ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField,
            show algebraMap F E.FunctionField (2 : F) = (2 : E.FunctionField)
              from by simp [map_ofNat]]
        rw [← hmk_eq]; intro h
        exact hmk_ne ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
          (h.trans (map_zero _).symm))
      calc D y = (1 : E.FunctionField) • D y := (one_smul _ _).symm
        _ = ((2 * y + c)⁻¹ * (2 * y + c)) • D y := by rw [inv_mul_cancel₀ hne]
        _ = (2 * y + c)⁻¹ • ((2 * y + c) • D y) := (smul_smul _ _ _).symm
        _ = (2 * y + c)⁻¹ • 0 := by rw [hsmul]
        _ = 0 := smul_zero _
    have hDcoord : ∀ r : E.CoordinateRing,
        D (algebraMap E.CoordinateRing E.FunctionField r) = 0 := by
      intro r
      obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
      rw [← hpq, map_add]
      simp only [Algebra.smul_def, map_mul, mul_one]
      rw [AdjoinRoot.mk_X, map_add, Derivation.leibniz,
        ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
        ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
        hDpoly p, hDpoly q, hDy, smul_zero, smul_zero, add_zero, add_zero]
    have hDall : ∀ s : E.FunctionField, D s = 0 := by
      intro s
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := E.CoordinateRing) s
      rw [← hab, div_eq_mul_inv, Derivation.leibniz, hDcoord a, smul_zero, add_zero]
      have hb_ne : algebraMap E.CoordinateRing E.FunctionField b ≠ 0 :=
        (IsLocalization.map_units E.FunctionField ⟨b, hb⟩).ne_zero
      have hDinv : D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) = 0 := by
        have h1 : algebraMap E.CoordinateRing E.FunctionField b •
          D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) = 0 := by
          have : D (algebraMap E.CoordinateRing E.FunctionField b *
            (algebraMap E.CoordinateRing E.FunctionField b)⁻¹) = 0 := by
            rw [mul_inv_cancel₀ hb_ne, Derivation.map_one_eq_zero]
          rwa [Derivation.leibniz, hDcoord b, smul_zero, add_zero] at this
        rw [show D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) =
          (algebraMap E.CoordinateRing E.FunctionField b)⁻¹ •
            (algebraMap E.CoordinateRing E.FunctionField b •
              D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹)) from by
          rw [smul_smul, inv_mul_cancel₀ hb_ne, one_smul], h1, smul_zero]
      rw [hDinv, smul_zero]
    suffices (⊤ : Submodule E.FunctionField (KaehlerDifferential F E.FunctionField)) ≤ ⊥ from
      (subsingleton_iff_forall_eq 0).mpr fun ω => this trivial
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_bot]
    exact hDall s
  have hFU : Algebra.FormallyUnramified F E.FunctionField := ⟨hΩ⟩
  have hSep := (Algebra.FormallyUnramified.iff_isSeparable F E.FunctionField).mp hFU
  exact not_isAlgebraic_x E
    ((Algebra.IsSeparable.isAlgebraic F E.FunctionField).isAlgebraic _)

/-! ### The invariant differential -/

section InvariantDifferential

variable (E : Affine F) [E.IsElliptic]

/-- The denominator `2y + a₁x + a₃` of the invariant differential is nonzero in `K(E)`.
    This is the image of `polynomialY` under the canonical map to the function field,
    and it is nonzero because `polynomialY ≠ 0` as a polynomial of degree < deg(W),
    and the algebra map to the fraction field is injective. -/
lemma denom_ne_zero :
    (2 : E.FunctionField) *
      (algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)) +
    algebraMap F E.FunctionField E.a₁ *
      (algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)) +
    algebraMap F E.FunctionField E.a₃ ≠ 0 := by
  set x : E.FunctionField :=
    algebraMap E.CoordinateRing E.FunctionField
      (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)
  set y : E.FunctionField :=
    algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)
  set c := algebraMap (Polynomial F) E.FunctionField
    (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
  have hc_eq : algebraMap F E.FunctionField E.a₁ * x + algebraMap F E.FunctionField E.a₃ = c := by
    simp only [c, map_add, map_mul]
    rw [show algebraMap (Polynomial F) E.FunctionField (Polynomial.C E.a₁) =
          algebraMap F E.FunctionField E.a₁ from
        IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₁,
      show algebraMap (Polynomial F) E.FunctionField (Polynomial.C E.a₃) =
          algebraMap F E.FunctionField E.a₃ from
        IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₃,
      show algebraMap (Polynomial F) E.FunctionField Polynomial.X = x from by
        simp only [x,
          IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]]
  rw [show 2 * y + algebraMap F E.FunctionField E.a₁ * x +
      algebraMap F E.FunctionField E.a₃ = 2 * y +
      (algebraMap F E.FunctionField E.a₁ * x + algebraMap F E.FunctionField E.a₃) from by ring,
    hc_eq]
  have hmk_ne : Affine.CoordinateRing.mk E E.polynomialY ≠ 0 :=
    AdjoinRoot.mk_ne_zero_of_natDegree_lt (Affine.monic_polynomial)
      (polynomialY_ne_zero E) (by
        rw [Affine.natDegree_polynomial, Affine.polynomialY]
        have : (Polynomial.C (Polynomial.C (2 : F)) * (Y : F[X][Y])).natDegree ≤ 1 :=
          Polynomial.natDegree_mul_le.trans
            (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
        exact Nat.lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
          (by rw [Polynomial.natDegree_C]; omega))
  have hmk_eq : algebraMap E.CoordinateRing E.FunctionField
      (Affine.CoordinateRing.mk E E.polynomialY) = 2 * y + c := by
    have hmk : (Affine.CoordinateRing.mk E E.polynomialY : E.CoordinateRing) =
      algebraMap (Polynomial F) E.CoordinateRing (Polynomial.C 2) *
        AdjoinRoot.root E.polynomial +
      algebraMap (Polynomial F) E.CoordinateRing
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) := by
      change AdjoinRoot.mk E.polynomial E.polynomialY = _
      rw [Affine.polynomialY, map_add, map_mul, AdjoinRoot.mk_X]; rfl
    rw [hmk, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
      ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
    congr 1; congr 1
    rw [show (Polynomial.C (2 : F) : Polynomial F) = algebraMap F (Polynomial F) 2
          from rfl,
      ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField,
      show algebraMap F E.FunctionField (2 : F) = (2 : E.FunctionField)
        from by simp [map_ofNat]]
  rw [← hmk_eq]; intro h
  exact hmk_ne ((IsFractionRing.injective E.CoordinateRing E.FunctionField).eq_iff.mp
    (h.trans (map_zero _).symm))

/-- The invariant differential ω = dx/(2y + a₁x + a₃) on E, concretely
    constructed in the Kähler differential module Ω[K(E)/F]. -/
noncomputable def invariantDifferential : KaehlerDifferential F E.FunctionField :=
  let x : E.FunctionField :=
    algebraMap E.CoordinateRing E.FunctionField
      (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)
  let y : E.FunctionField :=
    algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)
  let a₁ : E.FunctionField := algebraMap F E.FunctionField E.a₁
  let a₃ : E.FunctionField := algebraMap F E.FunctionField E.a₃
  (2 * y + a₁ * x + a₃)⁻¹ • (KaehlerDifferential.D F E.FunctionField x)

set_option linter.unusedDecidableInType false in
/-- The invariant differential is nonzero (equivalently, div(ω) = 0).
    Reference: Silverman, Proposition III.1.5. -/
theorem invariantDifferential_ne_zero :
    invariantDifferential E ≠ 0 := by
  unfold invariantDifferential
  exact smul_ne_zero (inv_ne_zero (denom_ne_zero E)) (D_x_ne_zero E)

end InvariantDifferential

end HasseWeil
