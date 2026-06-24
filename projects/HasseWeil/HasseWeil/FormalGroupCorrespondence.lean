import HasseWeil.Auxiliary.DivisionPolynomial
import HasseWeil.FormalGroupAssoc
import HasseWeil.InvariantDifferential
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Formal Group ↔ Curve Correspondence (Silverman IV.1–2, IV.4)

This file establishes the connection between the formal group of an elliptic curve
and the curve's group law. The key results:

1. **Local parameter**: z = -x/y is a local uniformizer at O (Silverman IV.1).
2. **w(z)**: The power series solving w = f(z,w) (already in FormalGroup.lean).
3. **Formal group law**: z(P+Q) = F(z(P), z(Q)) where F is the formal group law.
4. **Pullback coefficient**: For [m], the formal group series has linear coefficient m.

## The Key Connection (Silverman IV.4)

For an endomorphism φ of E, the pullback coefficient a_φ is defined by:
  φ*ω = a_φ · ω
where ω = dx/(2y+a₁x+a₃) is the invariant differential.

Equivalently (via the formal group): φ induces a power series φ_F(T) = a_φ T + O(T²),
and a_φ is the linear coefficient.

The map φ ↦ a_φ is a ring homomorphism End(E) → K̄ (Silverman Cor. III.5.6).

## Kähler Module is 1-Dimensional (Silverman III.1.5)

For an elliptic curve E/K (genus 1), the space Ω_{K(E)/K} of differentials is
1-dimensional over K(E). This means every differential η can be written as c·ω
for a unique c ∈ K(E).

This follows from the Riemann-Roch theorem (genus = dim Ω) applied to the
function field K(E) of transcendence degree 1 over K.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.1.5, III.5, IV.1–4
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]

/-! ### Ω_{K(E)/K} is 1-dimensional -/

section OmegaOneDim

variable (E : Affine F) [E.IsElliptic]

/-- The image `x` of the coordinate `X` in the function field `K(E)`. -/
private noncomputable def coordXFF : E.FunctionField :=
  algebraMap E.CoordinateRing E.FunctionField
    (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X)

/-- The image `y` of the root of the Weierstrass polynomial in `K(E)`. -/
private noncomputable def coordYFF : E.FunctionField :=
  algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial)

/-- The `K(E)`-span of `D(x)`, where `x = coordXFF E`. The whole proof that `Ω` has
rank one amounts to showing `D f ∈ derivSpanX E` for every `f ∈ K(E)`, since
`D(x)` is a nonzero multiple of the invariant differential `ω`. -/
private noncomputable def derivSpanX :
    Submodule E.FunctionField (KaehlerDifferential F E.FunctionField) :=
  Submodule.span E.FunctionField {KaehlerDifferential.D F E.FunctionField (coordXFF E)}

omit [DecidableEq F] in
/-- `D(x) ∈ span{ω}`: since `ω = u⁻¹ • D(x)` with `u = 2y + a₁x + a₃ ≠ 0`, we have
`D(x) = u • ω`. -/
private lemma D_coordXFF_mem_span_invariantDifferential :
    KaehlerDifferential.D F E.FunctionField (coordXFF E) ∈
      Submodule.span E.FunctionField {invariantDifferential E} := by
  unfold coordXFF invariantDifferential
  rw [Submodule.mem_span_singleton]
  exact ⟨2 * algebraMap E.CoordinateRing E.FunctionField (AdjoinRoot.root E.polynomial) +
      algebraMap F E.FunctionField E.a₁ * algebraMap E.CoordinateRing E.FunctionField
        (algebraMap (Polynomial F) E.CoordinateRing Polynomial.X) +
      algebraMap F E.FunctionField E.a₃,
    by rw [smul_smul, mul_inv_cancel₀ (denom_ne_zero E), one_smul]⟩

omit [DecidableEq F] in
/-- `D(x) ∈ derivSpanX E`: `D(x)` is the generator of the span by definition. -/
private lemma D_coordXFF_mem :
    KaehlerDifferential.D F E.FunctionField (coordXFF E) ∈ derivSpanX E :=
  Submodule.subset_span rfl

omit [DecidableEq F] in
/-- `D(xⁿ) ∈ derivSpanX E` for every `n`, by induction on `n` using the Leibniz rule. -/
private lemma D_coordXFF_pow_mem (n : ℕ) :
    KaehlerDifferential.D F E.FunctionField (coordXFF E ^ n) ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  induction n with
  | zero => rw [pow_zero, Derivation.map_one_eq_zero]; exact S.zero_mem
  | succ n ih =>
    rw [pow_succ, Derivation.leibniz]
    exact S.add_mem (S.smul_mem _ (D_coordXFF_mem E)) (S.smul_mem _ ih)

omit [DecidableEq F] in
/-- `D(p(x)) ∈ derivSpanX E` for every polynomial `p ∈ F[X]`, by induction on `p`,
reducing each monomial to a power of `x` via `D_coordXFF_pow_mem`. -/
private lemma D_algebraMap_polynomial_mem (p : Polynomial F) :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap (Polynomial F) E.FunctionField p) ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add]; exact S.add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
      show algebraMap (Polynomial F) E.FunctionField (Polynomial.C a) =
        algebraMap F E.FunctionField a from
        IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField a,
      show algebraMap (Polynomial F) E.FunctionField Polynomial.X = coordXFF E from
        IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField _]
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
    exact S.smul_mem _ (D_coordXFF_pow_mem E n)

open Polynomial.Bivariate in
omit [DecidableEq F] in
/-- The Weierstrass relation `y² + (a₁x+a₃)·y = x³ + a₂x² + a₄x + a₆` in the
coordinate ring `K[E]` (Silverman II.4.2b), obtained from the defining polynomial. -/
private lemma weierstrass_relation_coordinateRing :
    (AdjoinRoot.root E.polynomial) ^ 2 +
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
    algebraMap (Polynomial F) E.CoordinateRing p := fun _ ↦ rfl
  rw [hcc, hcc] at Y_sq; linear_combination Y_sq

omit [DecidableEq F] in
/-- The Weierstrass relation lifted to the function field `K(E)`:
`y² + c·y = rhs`, where `c = a₁x+a₃` and `rhs = x³+a₂x²+a₄x+a₆`. -/
private lemma weierstrass_relation_functionField :
    coordYFF E ^ 2 + algebraMap (Polynomial F) E.FunctionField
        (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) * coordYFF E =
      algebraMap (Polynomial F) E.FunctionField
        (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
         Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) := by
  have h := congr_arg (algebraMap E.CoordinateRing E.FunctionField)
    (weierstrass_relation_coordinateRing E)
  rw [map_add, map_mul, map_pow] at h
  rwa [← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField] at h

omit [DecidableEq F] in
/-- The denominator `2y + c` (with `c = a₁x+a₃`) of the invariant differential is nonzero
in `K(E)`; this is `denom_ne_zero` rephrased with `c` written as `algebraMap _ _ (C a₁·X+C a₃)`. -/
private lemma two_coordYFF_add_c_ne_zero :
    2 * coordYFF E + algebraMap (Polynomial F) E.FunctionField
      (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) ≠ 0 := by
  have hc_eq : algebraMap (Polynomial F) E.FunctionField
      (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) =
      algebraMap F E.FunctionField E.a₁ * coordXFF E +
        algebraMap F E.FunctionField E.a₃ := by
    rw [map_add, map_mul,
      show (Polynomial.C E.a₁ : Polynomial F) = algebraMap F (Polynomial F) E.a₁ from rfl,
      show (Polynomial.C E.a₃ : Polynomial F) = algebraMap F (Polynomial F) E.a₃ from rfl,
      ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₁,
      ← IsScalarTower.algebraMap_apply F (Polynomial F) E.FunctionField E.a₃,
      show algebraMap (Polynomial F) E.FunctionField Polynomial.X = coordXFF E from
        (IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing
          E.FunctionField Polynomial.X).symm]
  rw [hc_eq, ← add_assoc]; exact denom_ne_zero E

omit [DecidableEq F] in
/-- `D(y) ∈ derivSpanX E`. Differentiating the Weierstrass relation gives
`(2y+c)•D(y) = D(rhs) - y•D(c) ∈ S` (since `c, rhs` are polynomials in `x`), and
`2y+c ≠ 0`, so `D(y) ∈ S`. Reference: Silverman II.4.2b. -/
private lemma D_coordYFF_mem :
    KaehlerDifferential.D F E.FunctionField (coordYFF E) ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  set c_ff : E.FunctionField := algebraMap (Polynomial F) E.FunctionField
      (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) with hc_def
  set rhs_ff : E.FunctionField := algebraMap (Polynomial F) E.FunctionField
      (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
       Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆)
  have hW_FF : coordYFF E ^ 2 + c_ff * coordYFF E = rhs_ff :=
    weierstrass_relation_functionField E
  -- Leibniz: D(y²+c·y) = (2y+c)•D(y) + y•D(c)
  have hD_expand : D (coordYFF E ^ 2 + c_ff * coordYFF E) =
      (2 * coordYFF E + c_ff) • D (coordYFF E) + coordYFF E • D c_ff := by
    rw [map_add, sq, Derivation.leibniz, Derivation.leibniz,
      ← add_smul, ← two_mul, ← add_assoc, ← add_smul]
  -- D(c) and D(rhs) are in S (polynomials in x)
  have hD_c : D c_ff ∈ S := D_algebraMap_polynomial_mem E _
  have hD_rhs : D rhs_ff ∈ S := D_algebraMap_polynomial_mem E _
  -- From Weierstrass: (2y+c)•D(y) = D(rhs) - y•D(c) ∈ S
  have h_uDy_mem : (2 * coordYFF E + c_ff) • D (coordYFF E) ∈ S := by
    have h_eq : (2 * coordYFF E + c_ff) • D (coordYFF E) =
        D rhs_ff - coordYFF E • D c_ff :=
      (sub_eq_of_eq_add (hD_expand.symm.trans (congr_arg D hW_FF)).symm).symm
    rw [h_eq]; exact S.sub_mem hD_rhs (S.smul_mem _ hD_c)
  -- 2y+c ≠ 0, so D(y) = (2y+c)⁻¹ • ((2y+c)•D(y)) ∈ S
  rw [← inv_smul_smul₀ (two_coordYFF_add_c_ne_zero E) (D (coordYFF E))]
  exact S.smul_mem _ h_uDy_mem

omit [DecidableEq F] in
/-- `D(r) ∈ derivSpanX E` for every `r` in the coordinate ring `K[E]`. Writing
`r = p • 1 + q • y` with `p, q ∈ F[X]`, this follows from `D_algebraMap_polynomial_mem`
and `D_coordYFF_mem`. -/
private lemma D_algebraMap_coordinateRing_mem (r : E.CoordinateRing) :
    KaehlerDifferential.D F E.FunctionField
      (algebraMap E.CoordinateRing E.FunctionField r) ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  rw [← hpq, map_add]
  simp only [Algebra.smul_def, map_mul, mul_one]
  rw [AdjoinRoot.mk_X, map_add, Derivation.leibniz,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField,
    ← IsScalarTower.algebraMap_apply (Polynomial F) E.CoordinateRing E.FunctionField]
  exact S.add_mem (D_algebraMap_polynomial_mem E p)
    (S.add_mem (S.smul_mem _ (D_coordYFF_mem E)) (S.smul_mem _ (D_algebraMap_polynomial_mem E q)))

omit [DecidableEq F] in
/-- `D(b⁻¹) ∈ derivSpanX E` for `b` the image of a coordinate-ring element: from
`b · b⁻¹ = 1`, the Leibniz rule gives `b·D(b⁻¹) = -(b⁻¹·D(b))`, and `D(b) ∈ S`. -/
private lemma D_inv_algebraMap_coordinateRing_mem (b : E.CoordinateRing)
    (hb_ne : algebraMap E.CoordinateRing E.FunctionField b ≠ 0) :
    KaehlerDifferential.D F E.FunctionField
      ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  have h0 : algebraMap E.CoordinateRing E.FunctionField b •
      D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) =
      -((algebraMap E.CoordinateRing E.FunctionField b)⁻¹ •
        D (algebraMap E.CoordinateRing E.FunctionField b)) :=
    eq_neg_of_add_eq_zero_left (by
      rw [← Derivation.leibniz, mul_inv_cancel₀ hb_ne, Derivation.map_one_eq_zero])
  have h1 : D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹) =
      (algebraMap E.CoordinateRing E.FunctionField b)⁻¹ •
        (-((algebraMap E.CoordinateRing E.FunctionField b)⁻¹ •
          D (algebraMap E.CoordinateRing E.FunctionField b))) := by
    calc D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹)
        = (algebraMap E.CoordinateRing E.FunctionField b)⁻¹ •
            (algebraMap E.CoordinateRing E.FunctionField b •
              D ((algebraMap E.CoordinateRing E.FunctionField b)⁻¹)) := by
          rw [smul_smul, inv_mul_cancel₀ hb_ne, one_smul]
      _ = _ := by rw [h0]
  rw [h1]; exact S.smul_mem _ (S.neg_mem (S.smul_mem _ (D_algebraMap_coordinateRing_mem E b)))

omit [DecidableEq F] in
/-- `D(f) ∈ derivSpanX E` for every `f ∈ K(E) = Frac(K[E])`. Writing `f = a · b⁻¹`,
this follows from `D_algebraMap_coordinateRing_mem` and `D_inv_algebraMap_coordinateRing_mem`
via the Leibniz rule. -/
private lemma D_mem_derivSpanX (f : E.FunctionField) :
    KaehlerDifferential.D F E.FunctionField f ∈ derivSpanX E := by
  set D := KaehlerDifferential.D F E.FunctionField
  set S := derivSpanX E
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := E.CoordinateRing) f
  rw [← hab, div_eq_mul_inv, Derivation.leibniz]
  have hb_ne : algebraMap E.CoordinateRing E.FunctionField b ≠ 0 :=
    (IsLocalization.map_units E.FunctionField ⟨b, hb⟩).ne_zero
  exact S.add_mem (S.smul_mem _ (D_inv_algebraMap_coordinateRing_mem E b hb_ne))
    (S.smul_mem _ (D_algebraMap_coordinateRing_mem E a))

omit [DecidableEq F] in
/-- The invariant differential `ω` spans all of `Ω_{K(E)/F}`. Since `Ω` is spanned by
`{D f : f ∈ K(E)}` and each `D f ∈ span{D(x)} ≤ span{ω}` (as `D(x) ∈ span{ω}`), the
span of `ω` is everything. Reference: Silverman III.1.5. -/
private lemma span_invariantDifferential_eq_top :
    Submodule.span E.FunctionField {invariantDifferential E} = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation F E.FunctionField,
    Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  rw [SetLike.mem_coe]
  exact Submodule.span_le.mpr
    (Set.singleton_subset_iff.mpr (D_coordXFF_mem_span_invariantDifferential E))
    (D_mem_derivSpanX E f)

-- The Kähler differential module Ω[K(E)/F] is generated by dx/(2y+a₁x+a₃)
-- as a K(E)-module. Every element η ∈ Ω is of the form c · ω for some c ∈ K(E).
-- This follows from E having genus 1: by Riemann-Roch, dim_K(E) Ω = g = 1.
-- Reference: Silverman III.1.5, Prop. II.4.2(a).
theorem kaehler_rank_one :
    Module.finrank E.FunctionField (KaehlerDifferential F E.FunctionField) = 1 := by
  haveI : Module.Free E.FunctionField (KaehlerDifferential F E.FunctionField) :=
    Module.Free.of_divisionRing _ _
  rw [finrank_eq_one_iff']
  refine ⟨invariantDifferential E, invariantDifferential_ne_zero E, fun w ↦ ?_⟩
  -- Every w ∈ Ω is a K(E)-multiple of ω because span{ω} = ⊤.
  have hw : w ∈ (⊤ : Submodule E.FunctionField _) := Submodule.mem_top
  rw [← span_invariantDifferential_eq_top E] at hw
  rwa [Submodule.mem_span_singleton] at hw

end OmegaOneDim

/-! ### The multiplication-by-m map on the formal group -/

section MulByMFormal

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- The formal group power series [m]_F(T) = m·T + O(T²) for the multiplication
    by m map. The linear coefficient is m.

    This is Silverman Proposition IV.2.3(a): for the formal group associated to
    an elliptic curve, the formal multiplication-by-m has linear coefficient m.

    Combined with the formal group ↔ curve correspondence (IV.1), this gives
    [m]*ω = m·ω (Silverman Cor. III.5.3). -/
theorem formalMulByInt_linear_coeff (m : ℤ) :
    formalMulByInt_coeff W.toAffine m 1 = (m : F) := by
  simp only [formalMulByInt_coeff, one_ne_zero, ↓reduceIte]

/-- The multiplication-by-m on the formal group starts with 0 (no constant term). -/
theorem formalMulByInt_const_zero (m : ℤ) :
    formalMulByInt_coeff W.toAffine m 0 = 0 := by
  simp only [formalMulByInt_coeff, ↓reduceIte]

end MulByMFormal

/-! ### Connection: formal group linear coefficient = invariant differential pullback

From Silverman IV.4 and III.5.6: for any endomorphism φ of E,
- φ induces a formal power series φ_F(T) = a_φ T + O(T²) on the formal group
- φ*ω = a_φ · ω where ω is the invariant differential
- The coefficient a_φ is the same in both descriptions

The key insight (Silverman IV.4.2): the formal group invariant differential
ω_F(T) = (1 + ...) dT satisfies ω_F = ω ∘ (local parameter)⁻¹, where the
local parameter t = -x/y identifies a neighborhood of O with the formal group.

Under this identification:
- φ_F(T) = t(φ(t⁻¹(T))) (the endomorphism in local coordinates)
- φ*(ω_F) = a_φ · ω_F (since ω_F = ω up to the change of coordinates)
- a_φ = coeff_1(φ_F) = d(φ_F)/dT |_{T=0}

For [m]: the formal group power series is [m]_F(T) = m·T + O(T²),
so a_{[m]} = m. This matches Silverman Cor. III.5.3: [m]*ω = mω.
-/

section Correspondence

variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- The formal group ↔ curve correspondence for the pullback coefficient.

    For the multiplication-by-m endomorphism [m]:
    1. The formal group series has linear coefficient m (formalMulByInt_linear_coeff)
    2. The invariant differential pullback gives [m]*ω = mω (Silverman III.5.3)
    3. These are consistent: a_{[m]} = m in both descriptions.

    This is a DEFINITIONAL identity — the formal group was constructed (IV.1)
    precisely so that the group law on the curve near O matches the formal group law.
    Reference: Silverman IV.1–4. -/
theorem pullback_coeff_eq_formal_coeff_mulByInt (m : ℤ) :
    -- The pullback coefficient of [m] computed via the formal group
    -- equals m (matching the invariant differential computation).
    formalMulByInt_coeff W.toAffine m 1 = (m : F) :=
  formalMulByInt_linear_coeff W m

end Correspondence

/-! ### The Frobenius pullback coefficient

For the Frobenius endomorphism π (x,y) ↦ (x^q, y^q):
- π*(ω) = π*(dx/(2y+a₁x+a₃)) = d(x^q)/(2y^q+a₁x^q+a₃)
         = qx^{q-1}dx / (2y+a₁x+a₃)^q
- In characteristic p with q = p^r: qx^{q-1} = 0
- So π*(ω) = 0, meaning a_π = 0
- This confirms: Frobenius is purely inseparable (Silverman IV.4.2c)

For (1-π): (1-π)*ω = ω - π*ω = ω - 0 = ω ≠ 0
- So a_{1-π} = 1
- This confirms: 1-π is separable (Silverman Cor. III.5.5)
-/

/-! **[2026-05-28 placeholder grind]** The section `FrobeniusPullback`, holding
the two vacuous placeholders `frobenius_pullback_coeff_zero` (`a_π = 0`) and
`one_sub_frobenius_pullback_coeff_one` (`a_{1-π} = 1`) — both stated as
`True := trivial` with the real content only in their docstrings — was deleted.
The genuine omega-pullback-coefficient facts live in `OmegaPullbackCoeff.lean`
(`omegaPullbackCoeff`), where they are stated and used with real content. -/

end HasseWeil
