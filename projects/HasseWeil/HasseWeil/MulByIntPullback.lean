/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Auxiliary.DivisionPolynomial

/-!
# The Pullback of [n] on Function Fields

We construct the pullback `[n]* : K(E) →ₐ[F] K(E)` for the multiplication-by-n
endomorphism, using division polynomial formulas.

The key identity is the Jacobian Weierstrass equation for the division polynomial
triple `[φ_n, ω_n, ψ_n]` evaluated at the generic point. This is proved by
base-changing W to K(E), using `zsmul_eq_smulEval` over K(E), and extracting
the equation from the resulting Jacobian point.

## Main definitions

* `mulByInt_x`, `mulByInt_y`: the coordinates of `[n]` at the generic point.
* `mulByInt_coordHom`: the induced coordinate-ring hom `R → K(E)`.
* `mulByInt_pullbackAlgHom`: the pullback algebra hom `[n]* : K(E) →ₐ[F] K(E)`.

## Main results

* `mulByInt_weierstrass`: the generic point of `[n]` satisfies the Weierstrass equation.
* `mulByInt_coordHom_injective`: the coordinate-ring hom is injective.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

/-- The generic `x`-coordinate: the image of `X` in `K(E)`. -/
noncomputable def x_gen : KE :=
  algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)

/-- The generic `y`-coordinate: the image of the adjoined root in `K(E)`. -/
noncomputable def y_gen : KE :=
  algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)

/-- The base change of `W` to `K(E)`. The generic point `(x_gen, y_gen)` is a
`K(E)`-rational point on it. -/
noncomputable def W_KE : WeierstrassCurve KE := W.map (algebraMap F KE)

/-- The base-changed curve is elliptic (automatic from `W.IsElliptic` + `map`). -/
instance W_KE_isElliptic : (W_KE W).IsElliptic :=
  show (W.map (algebraMap F KE)).IsElliptic from inferInstance

noncomputable def Φ_ff (n : ℤ) : KE :=
  algebraMap R KE (algebraMap (Polynomial F) R (W.Φ n))

noncomputable def ΨSq_ff (n : ℤ) : KE :=
  algebraMap R KE (algebraMap (Polynomial F) R (W.ΨSq n))

noncomputable def ψ_ff (n : ℤ) : KE :=
  algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ψ n))

noncomputable def ω_ff (n : ℤ) : KE :=
  algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.ω n))

/-- The `x`-coordinate of `[n]` at the generic point: `Φ_n(x) / ΨSq_n(x)`. -/
noncomputable def mulByInt_x (n : ℤ) : KE := Φ_ff W n / ΨSq_ff W n

/-- The `y`-coordinate of `[n]` at the generic point: `ω_n / ψ_n³`. -/
noncomputable def mulByInt_y (n : ℤ) : KE := ω_ff W n / ψ_ff W n ^ 3

/-- The ring hom `F[X] → K(E)` sending `X ↦ mulByInt_x W n`. -/
noncomputable def mulByInt_xHom (n : ℤ) : Polynomial F →+* KE :=
  Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W n)

omit [W.toAffine.IsElliptic] in
/-- The generic point `(x_gen, y_gen)` satisfies the equation of `W_KE`. -/
lemma generic_equation : (W_KE W).toAffine.Equation (x_gen W) (y_gen W) := by
  change (W.map (algebraMap F KE)).toAffine.polynomial.evalEval (x_gen W) (y_gen W) = 0
  have hfactor : (algebraMap F KE : F →+* KE) =
      (algebraMap R KE).comp (algebraMap F R) :=
    (IsScalarTower.algebraMap_eq F R KE).symm
  rw [Affine.map_polynomial]
  conv_lhs => rw [hfactor, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map]
  set f := algebraMap R KE
  set p := Polynomial.map (Polynomial.mapRingHom (algebraMap F R))
    (Affine.polynomial W.toAffine) with hp
  change (p.map (Polynomial.mapRingHom f)).evalEval (f _) (f _) = 0
  rw [Polynomial.map_mapRingHom_evalEval,
    map_eq_zero_iff f (IsFractionRing.injective R KE)]
  rw [hp, ← Polynomial.eval₂_eval₂RingHom_apply]
  have hinner : Polynomial.eval₂RingHom (algebraMap F R)
      (algebraMap (Polynomial F) R Polynomial.X) = algebraMap (Polynomial F) R := by
    ext x
    · simp [Polynomial.eval₂_C, IsScalarTower.algebraMap_apply F (Polynomial F) R]
    · simp
  rw [hinner]
  exact AdjoinRoot.eval₂_root W.toAffine.polynomial

/-- The generic point is nonsingular on W_KE (follows from equation + IsElliptic).
    (private helper; `HasseWeil.generic_nonsingular` is the public version in
    `EC/GenericPoint.lean`). -/
private lemma generic_nonsingular' : (W_KE W).toAffine.Nonsingular (x_gen W) (y_gen W) :=
  Affine.equation_iff_nonsingular.mp (generic_equation W)

omit [W.toAffine.IsElliptic] in
/-- `ψ_ff W n` squared equals `ΨSq_ff W n`. This follows from `mk_Ψ_sq` in mathlib. -/
lemma ψ_ff_sq_eq_ΨSq_ff (n : ℤ) : ψ_ff W n ^ 2 = ΨSq_ff W n := by
  simp only [ψ_ff, ΨSq_ff]
  rw [← map_pow]
  congr 1
  rw [Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]
  exact Affine.CoordinateRing.mk_Ψ_sq (W := W.toAffine) n

omit [W.toAffine.IsElliptic] in
/-- `φ_ff W n` equals `Φ_ff W n`. This follows from `mk_φ` in mathlib. -/
lemma φ_ff_eq_Φ_ff (n : ℤ) :
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine (W.φ n)) = Φ_ff W n := by
  simp only [Φ_ff]; congr 1
  exact Affine.CoordinateRing.mk_φ (W := W.toAffine) n

omit [W.toAffine.IsElliptic] in
private lemma natDegree_ψ₂_le : W.ψ₂.natDegree ≤ 1 := by
  rw [ψ₂, Affine.polynomialY]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  rw [Nat.max_le]
  exact ⟨Polynomial.natDegree_mul_le.trans (by
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add]; lia),
    (Polynomial.natDegree_C _).le.trans (Nat.zero_le _)⟩

omit [W.toAffine.IsElliptic] in
private lemma natDegree_Ψ_le (n : ℤ) : (W.Ψ n).natDegree ≤ 1 := by
  rw [WeierstrassCurve.Ψ]
  split_ifs with h
  · exact (Polynomial.natDegree_mul_le).trans (by
      rw [Polynomial.natDegree_C]; exact Nat.zero_add _ ▸ natDegree_ψ₂_le W)
  · rw [mul_one, Polynomial.natDegree_C]; exact Nat.zero_le _

/-- `W.ΨSq n` is nonzero for n ≠ 0 on an elliptic curve.
This uses the coprimality `IsCoprime (Φ n) (ΨSq n)` and `Φ n` not being a unit. -/
lemma ΨSq_poly_ne_zero {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  intro h
  have hcop := isCoprime_Φ_ΨSq W (W.coe_Δ' ▸ W.Δ'.ne_zero) hn
  rw [h, isCoprime_zero_right, Polynomial.isUnit_iff] at hcop
  obtain ⟨c, _, hΦ⟩ := hcop
  -- Φ n is a nonzero constant, but natDegree(Φ n) = n² > 0 for n ≠ 0
  have hpos := natDegree_Φ_pos W hn
  rw [← hΦ, Polynomial.natDegree_C] at hpos
  exact Nat.lt_irrefl 0 hpos

private lemma Ψ_ne_zero {n : ℤ} (hn : n ≠ 0) : W.Ψ n ≠ 0 := by
  intro hΨ
  apply ΨSq_poly_ne_zero W hn
  rw [WeierstrassCurve.Ψ] at hΨ
  have hpreΨ : W.preΨ n = 0 := by
    rcases mul_eq_zero.mp hΨ with hC | h1
    · exact Polynomial.C_eq_zero.mp hC
    · exfalso; split_ifs at h1 with heven
      · -- `polynomialY = 0` would force `a₁ = a₃ = 0` in char 2, hence `Δ = 0`.
        rw [ψ₂] at h1
        have hpy : W.toAffine.polynomialY ≠ 0 := by
          intro hpy
          have h2 : (2 : F) = 0 := by
            simpa [Affine.polynomialY] using congr_arg (fun (p : F[X][X]) ↦ p.coeff 1) hpy
          have ha1 : W.a₁ = 0 := by
            have h0c := congr_arg (fun (p : F[X][X]) ↦ p.coeff 0) hpy
            simp only [Affine.polynomialY, h2, map_zero, zero_mul, map_add, map_mul, zero_add,
              coeff_add, mul_coeff_zero, coeff_C_zero, coeff_zero] at h0c
            simpa using congr_arg (fun (p : F[X]) ↦ p.coeff 1) h0c
          have ha3 : W.a₃ = 0 := by
            have h0c := congr_arg (fun (p : F[X][X]) ↦ p.coeff 0) hpy
            simp only [Affine.polynomialY, h2, map_zero, zero_mul, map_add, map_mul, zero_add,
              coeff_add, mul_coeff_zero, coeff_C_zero, coeff_zero] at h0c
            simpa using congr_arg (fun (p : F[X]) ↦ p.coeff 0) h0c
          have hΔ : W.Δ = 0 := by
            -- Every `bᵢ` carries a factor of `2`, so `Δ = 0` in char 2.
            have hb₂ : WeierstrassCurve.b₂ W = 0 := by
              rw [WeierstrassCurve.b₂, ha1]; linear_combination 2 * W.a₂ * h2
            have hb₄ : WeierstrassCurve.b₄ W = 0 := by
              rw [WeierstrassCurve.b₄, ha1, ha3]; linear_combination W.a₄ * h2
            have hb₆ : WeierstrassCurve.b₆ W = 0 := by
              rw [WeierstrassCurve.b₆, ha3]; linear_combination 2 * W.a₆ * h2
            rw [WeierstrassCurve.Δ, hb₂, hb₄, hb₆]; ring
          exact W.Δ'.ne_zero (W.coe_Δ' ▸ hΔ)
        exact hpy h1
      · exact one_ne_zero h1
  rw [ΨSq, hpreΨ, zero_pow (by norm_num : 2 ≠ 0), zero_mul]

/-- The image of `mk W (ψ n)` in the coordinate ring is nonzero for n ≠ 0. -/
lemma mk_ψ_ne_zero {n : ℤ} (hn : n ≠ 0) :
    Affine.CoordinateRing.mk W.toAffine (W.ψ n) ≠ 0 := by
  rw [Affine.CoordinateRing.mk_ψ (W := W.toAffine) n]
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (Affine.monic_polynomial) (Ψ_ne_zero W hn) ?_
  have := natDegree_Ψ_le W n
  have := Affine.natDegree_polynomial (W := W.toAffine)
  lia

/-- The image of `ψ_n` in K(E) is nonzero for n ≠ 0. -/
lemma ψ_ff_ne_zero {n : ℤ} (hn : n ≠ 0) : ψ_ff W n ≠ 0 := by
  rw [ψ_ff]
  intro h
  exact mk_ψ_ne_zero W hn
    ((IsFractionRing.injective R KE) (h.trans (map_zero _).symm))

/-- `ΨSq_ff W n` is nonzero for n ≠ 0 (follows from ψ_ff_ne_zero). -/
lemma ΨSq_ff_ne_zero {n : ℤ} (hn : n ≠ 0) : ΨSq_ff W n ≠ 0 := by
  rw [← ψ_ff_sq_eq_ΨSq_ff]
  exact pow_ne_zero 2 (ψ_ff_ne_zero W hn)

omit [W.toAffine.IsElliptic] in
/-- Evaluating a bivariate polynomial (mapped from `F` to `K(E)`) at the generic point
gives the image in `K(E)` via `mk` and `algebraMap`. -/
private lemma evalEval_generic_eq_mk (p : (Polynomial F)[X]) :
    (p.map (Polynomial.mapRingHom (algebraMap F KE))).evalEval (x_gen W) (y_gen W) =
    algebraMap R KE (Affine.CoordinateRing.mk W.toAffine p) := by
  have hfactor : (algebraMap F KE : F →+* KE) =
      (algebraMap R KE).comp (algebraMap F R) :=
    (IsScalarTower.algebraMap_eq F R KE).symm
  conv_lhs => rw [hfactor, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map]
  set g := algebraMap R KE
  set q := Polynomial.map (Polynomial.mapRingHom (algebraMap F R)) p with hq
  change (q.map (Polynomial.mapRingHom g)).evalEval (g _) (g _) = g _
  rw [Polynomial.map_mapRingHom_evalEval]
  congr 1
  rw [hq, ← Polynomial.eval₂_eval₂RingHom_apply]
  have hinner : Polynomial.eval₂RingHom (algebraMap F R)
      (algebraMap (Polynomial F) R Polynomial.X) = algebraMap (Polynomial F) R := by
    ext x
    · simp [Polynomial.eval₂_C, IsScalarTower.algebraMap_apply F (Polynomial F) R]
    · simp
  rw [hinner, ← Polynomial.aeval_def]
  exact AdjoinRoot.aeval_eq p

omit [W.toAffine.IsElliptic] in
/-- The smulEval of W_KE at the generic point relates to division polynomial images.
Component 2 (the Z-coordinate / ψ-coordinate) of smulEval. -/
lemma smulEval_generic_Z (n : ℤ) :
    smulEval (W_KE W) (x_gen W) (y_gen W) n 2 = ψ_ff W n := by
  change ((W.map (algebraMap F KE)).ψ n).evalEval (x_gen W) (y_gen W) = ψ_ff W n
  rw [map_ψ, ψ_ff]
  exact evalEval_generic_eq_mk W (W.ψ n)

omit [W.toAffine.IsElliptic] in
/-- Component 0 (the X-coordinate / φ-coordinate) of smulEval. -/
lemma smulEval_generic_X (n : ℤ) :
    smulEval (W_KE W) (x_gen W) (y_gen W) n 0 = Φ_ff W n := by
  change ((W.map (algebraMap F KE)).φ n).evalEval (x_gen W) (y_gen W) = Φ_ff W n
  rw [map_φ, evalEval_generic_eq_mk]
  exact φ_ff_eq_Φ_ff W n

omit [W.toAffine.IsElliptic] in
/-- Component 1 (the Y-coordinate / ω-coordinate) of smulEval. -/
lemma smulEval_generic_Y (n : ℤ) :
    smulEval (W_KE W) (x_gen W) (y_gen W) n 1 = ω_ff W n := by
  change ((W.map (algebraMap F KE)).ω n).evalEval (x_gen W) (y_gen W) = ω_ff W n
  rw [map_ω, ω_ff]
  exact evalEval_generic_eq_mk W (W.ω n)

/-- The Jacobian equation holds for the smulEval of the generic point.
This follows from the fact that [n]P is a point on the curve. -/
private lemma jacobian_equation_smulEval (n : ℤ) :
    WeierstrassCurve.Jacobian.Equation (W_KE W).toJacobian
      (smulEval (W_KE W) (x_gen W) (y_gen W) n) := by
  have hns := generic_nonsingular' W
  have hJ : WeierstrassCurve.Jacobian.Nonsingular (W_KE W).toJacobian
      (smulEval (W_KE W) (x_gen W) (y_gen W) n) := by
    rw [← WeierstrassCurve.Jacobian.nonsingularLift_iff]
    rw [← zsmul_eq_smulEval (W_KE W) hns n]
    exact (n • WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some _ _ hns)).nonsingular
  exact hJ.1

theorem mulByInt_weierstrass (n : ℤ) (hn : n ≠ 0) :
    Polynomial.eval₂ (mulByInt_xHom W n) (mulByInt_y W n) W.toAffine.polynomial = 0 := by
  -- Rewrite the `eval₂` as an affine `Equation` on `W_KE`.
  change Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap F KE) (mulByInt_x W n))
    (mulByInt_y W n) W.toAffine.polynomial = 0
  rw [Polynomial.eval₂_eval₂RingHom_apply]
  rw [show Polynomial.map (Polynomial.mapRingHom (algebraMap F KE)) W.toAffine.polynomial =
    (W_KE W).toAffine.polynomial from (Affine.map_polynomial W.toAffine (algebraMap F KE)).symm]
  -- `[n]P` is a nonsingular Jacobian point, so it satisfies the Jacobian equation.
  have hns := generic_nonsingular' W
  have hns_smul : WeierstrassCurve.Jacobian.Nonsingular (W_KE W).toJacobian
      (smulEval (W_KE W) (x_gen W) (y_gen W) n) := by
    rw [← WeierstrassCurve.Jacobian.nonsingularLift_iff,
      ← zsmul_eq_smulEval (W_KE W) hns n]
    exact (n • WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some _ _ hns)).nonsingular
  -- Pass to affine coordinates via `ψ ≠ 0` and match them against `mulByInt_x`, `mulByInt_y`.
  have hψ_ne : smulEval (W_KE W) (x_gen W) (y_gen W) n 2 ≠ 0 := by
    rw [smulEval_generic_Z]; exact ψ_ff_ne_zero W hn
  have hJ := (WeierstrassCurve.Jacobian.equation_of_Z_ne_zero hψ_ne).mp hns_smul.1
  rw [smulEval_generic_X, smulEval_generic_Y, smulEval_generic_Z,
    show Φ_ff W n / ψ_ff W n ^ 2 = mulByInt_x W n from by
      rw [mulByInt_x, ψ_ff_sq_eq_ΨSq_ff],
    show ω_ff W n / ψ_ff W n ^ 3 = mulByInt_y W n from rfl] at hJ
  exact hJ

/-- The coordinate-ring hom `R → K(E)` induced by `[n]`, lifting `mulByInt_xHom` and
`mulByInt_y` along the Weierstrass relation. -/
noncomputable def mulByInt_coordHom (n : ℤ) (hn : n ≠ 0) : R →+* KE :=
  AdjoinRoot.lift (mulByInt_xHom W n) (mulByInt_y W n) (mulByInt_weierstrass W n hn)

omit [W.toAffine.IsElliptic] in
private lemma algebraMap_poly_KE_injective : Function.Injective (algebraMap (Polynomial F) KE) := by
  change Function.Injective ((algebraMap R KE).comp (algebraMap (Polynomial F) R))
  exact (IsFractionRing.injective R KE).comp Affine.CoordinateRing.algebraMap_poly_injective

omit [W.toAffine.IsElliptic] in
/-- `x_gen` is transcendental over `F` in `KE`:
the generic x-coordinate of an elliptic curve is transcendental over the base field. -/
lemma x_gen_transcendental : Transcendental F (x_gen W) := by
  rw [x_gen, show algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X) =
    algebraMap (Polynomial F) KE Polynomial.X from
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE Polynomial.X).symm]
  exact (transcendental_algebraMap_iff (algebraMap_poly_KE_injective W)).mpr
    (Polynomial.transcendental_X F)

omit [W.toAffine.IsElliptic] in
/-- The image of `Φ_n` in `KE` is transcendental over `F` for `n ≠ 0`. -/
private lemma Φ_ff_transcendental (n : ℤ) (hn : n ≠ 0) :
    Transcendental F (Φ_ff W n) := by
  rw [Φ_ff, show algebraMap R KE (algebraMap (Polynomial F) R (W.Φ n)) =
    algebraMap (Polynomial F) KE (W.Φ n) from
    (IsScalarTower.algebraMap_apply (Polynomial F) R KE _).symm]
  exact (transcendental_algebraMap_iff (algebraMap_poly_KE_injective W)).mpr
    (Polynomial.transcendental (W.Φ n) (by have := natDegree_Φ_pos W hn; lia)
      (by rw [leadingCoeff_Φ]; exact mem_nonZeroDivisors_of_ne_zero one_ne_zero))

-- The `Subalgebra F KE` scalar-tower instances and the `aeval` defeq steps below need the
-- relaxed transparency; this is a defeq setting, not a heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
/-- `mulByInt_x W n = Φ_n(x_gen) / ΨSq_n(x_gen)` is transcendental over `F` for `n ≠ 0`.

The proof uses the integral closure approach: if `mulByInt_x` were algebraic over `F`,
then the subalgebra `S := F[mulByInt_x]` would be algebraic over `F`. The element
`x_gen` is integral over `S` via the monic polynomial
`Φ_n(T) - mulByInt_x · ΨSq_n(T) ∈ S[T]` (monic because `Φ_n` is monic of degree `n²`
and `ΨSq_n` has degree `< n²`). By transitivity (`IsIntegral.trans_isAlgebraic`),
`x_gen` would be algebraic over `F`, contradicting `x_gen_transcendental`. -/
private lemma mulByInt_x_transcendental (n : ℤ) (hn : n ≠ 0) :
    Transcendental F (mulByInt_x W n) := by
  intro h_alg
  apply x_gen_transcendental W
  set S : Subalgebra F KE := Algebra.adjoin F ({mulByInt_x W n} : Set KE) with hS_def
  haveI hS_alg : Algebra.IsAlgebraic F S :=
    (Subalgebra.isAlgebraic_iff S).mp
      (Algebra.isAlgebraic_adjoin_singleton_iff.mpr h_alg)
  have hmem : mulByInt_x W n ∈ S := Algebra.subset_adjoin (Set.mem_singleton _)
  let mxS : S := ⟨mulByInt_x W n, hmem⟩
  -- Witness polynomial: `Φ_n(T) - mxS · ΨSq_n(T) ∈ S[T]`, monic since `deg Φ_n > deg ΨSq_n`.
  let p_wit : Polynomial S :=
    (W.Φ n).map (algebraMap F S) - Polynomial.C mxS * (W.ΨSq n).map (algebraMap F S)
  have hΦ_monic : (W.Φ n).Monic := show (W.Φ n).leadingCoeff = 1 from W.leadingCoeff_Φ n
  have hΦS_monic : ((W.Φ n).map (algebraMap F S)).Monic := hΦ_monic.map _
  have hΦS_natDeg : ((W.Φ n).map (algebraMap F S)).natDegree = n.natAbs ^ 2 := by
    rw [hΦ_monic.natDegree_map]; exact W.natDegree_Φ n
  have hΨSqS_natDeg_le :
      (Polynomial.C mxS * (W.ΨSq n).map (algebraMap F S)).natDegree ≤ n.natAbs ^ 2 - 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (W.natDegree_ΨSq_le n))
  have hn2_pos : 0 < n.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hn) 2
  have h_pwit_monic : p_wit.Monic := by
    refine hΦS_monic.sub_of_left ?_
    rw [Polynomial.degree_eq_natDegree hΦS_monic.ne_zero, hΦS_natDeg]
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    have h1 : n.natAbs ^ 2 - 1 < n.natAbs ^ 2 := Nat.sub_lt hn2_pos Nat.one_pos
    exact_mod_cast lt_of_le_of_lt hΨSqS_natDeg_le h1
  have h_pwit_eval : Polynomial.aeval (x_gen W) p_wit = 0 := by
    change Polynomial.aeval (x_gen W)
      ((W.Φ n).map (algebraMap F S) -
        Polynomial.C mxS * (W.ΨSq n).map (algebraMap F S)) = 0
    rw [map_sub, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap]
    have hΦ_aeval : Polynomial.aeval (x_gen W) (W.Φ n) = Φ_ff W n := by
      change Polynomial.aeval (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))
          (W.Φ n) = Φ_ff W n
      rw [Polynomial.aeval_algebraMap_apply (A := R) (B := KE),
          Polynomial.aeval_algebraMap_apply (A := Polynomial F) (B := R),
          Polynomial.aeval_X_left_apply]
      rfl
    have hΨSq_aeval : Polynomial.aeval (x_gen W) (W.ΨSq n) = ΨSq_ff W n := by
      change Polynomial.aeval (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))
          (W.ΨSq n) = ΨSq_ff W n
      rw [Polynomial.aeval_algebraMap_apply (A := R) (B := KE),
          Polynomial.aeval_algebraMap_apply (A := Polynomial F) (B := R),
          Polynomial.aeval_X_left_apply]
      rfl
    rw [hΦ_aeval, hΨSq_aeval]
    change Φ_ff W n - mulByInt_x W n * ΨSq_ff W n = 0
    rw [mulByInt_x, div_mul_cancel₀ _ (ΨSq_ff_ne_zero W hn), sub_self]
  have h_int : IsIntegral S (x_gen W) := ⟨p_wit, h_pwit_monic, h_pwit_eval⟩
  have h_alg_S : IsAlgebraic S (x_gen W) := h_int.isAlgebraic
  exact h_alg_S.restrictScalars F

/-- `mulByInt_xHom` is injective because `mulByInt_x` is transcendental over `F`. -/
private lemma mulByInt_xHom_injective (n : ℤ) (hn : n ≠ 0) :
    Function.Injective (mulByInt_xHom W n) := by
  have h : (mulByInt_xHom W n : Polynomial F →+* KE) =
      (Polynomial.aeval (mulByInt_x W n) : Polynomial F →ₐ[F] KE).toRingHom := by
    ext <;> simp [mulByInt_xHom, Polynomial.aeval_def]
  rw [h]
  exact transcendental_iff_injective.mp (mulByInt_x_transcendental W n hn)

omit [W.toAffine.IsElliptic] in
/-- The norm of a basis element `p • 1 + q • Y` of `R` over `F[X]` is nonzero when `q ≠ 0`:
its degree is `max (2 • deg p) (2 • deg q + 3) ≥ 3`. -/
private lemma norm_smul_basis_ne_zero (p q : Polynomial F) (hq : q ≠ 0) :
    Algebra.norm (Polynomial F)
      (p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X) ≠ 0 := by
  intro h_norm_eq
  have h_deg := Affine.CoordinateRing.degree_norm_smul_basis (W' := W.toAffine) p q
  rw [h_norm_eq, Polynomial.degree_zero] at h_deg
  have hq_deg : q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hq
  have : 2 • q.degree + 3 ≠ (⊥ : WithBot ℕ) := by
    intro h
    apply hq_deg
    cases hd : q.degree with
    | bot => rfl
    | coe n =>
        rw [hd] at h
        exact absurd h (by change ¬ (2 • (↑n : WithBot ℕ) + 3 = ⊥); simp [WithBot.mul_ne_bot])
  exact absurd (h_deg ▸ le_max_right _ _ : 2 • q.degree + 3 ≤ ⊥)
    (not_le.mpr (WithBot.bot_lt_iff_ne_bot.mpr this))

theorem mulByInt_coordHom_injective (n : ℤ) (hn : n ≠ 0) :
    Function.Injective (mulByInt_coordHom W n hn) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  -- Decompose r = p • 1 + q • (mk W Y) using the basis of R over F[X]
  obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
  have h_image : mulByInt_coordHom W n hn r =
      mulByInt_xHom W n p + mulByInt_xHom W n q * mulByInt_y W n := by
    rw [← hpq]
    simp only [mulByInt_coordHom, map_add]
    congr 1
    · change AdjoinRoot.lift _ _ _ (p • 1) = _
      rw [Algebra.smul_def, mul_one]
      exact AdjoinRoot.lift_of _
    · change AdjoinRoot.lift _ _ _ (q • AdjoinRoot.root _) = _
      rw [Algebra.smul_def, map_mul]
      congr 1
      · exact AdjoinRoot.lift_of _
      · exact AdjoinRoot.lift_root _
  rw [h_image] at hr
  suffices hp : p = 0 ∧ q = 0 by
    have ⟨hp1, hp2⟩ := hp
    rw [← hpq, hp1, hp2]
    change (0 : Polynomial F) • (1 : R) + (0 : Polynomial F) •
      Affine.CoordinateRing.mk W.toAffine Polynomial.X = 0
    rw [Algebra.smul_def, Algebra.smul_def, map_zero, zero_mul, zero_mul, add_zero]
  have hxinj := mulByInt_xHom_injective W n hn
  by_cases hq : q = 0
  · rw [hq, map_zero, zero_mul, add_zero] at hr
    exact ⟨hxinj (hr.trans (map_zero _).symm), hq⟩
  · -- `q ≠ 0`: the norm of `r' = p•1 + q•Y` would have to vanish, but `degree_norm_smul_basis`
    -- makes it `max (2•deg p) (2•deg q + 3) ≥ 3`, a contradiction.
    exfalso
    set r' := p • (1 : R) + q • Affine.CoordinateRing.mk W.toAffine Polynomial.X with hr'_def
    have h_alg : ∀ f : Polynomial F,
        mulByInt_coordHom W n hn (algebraMap (Polynomial F) R f) = mulByInt_xHom W n f := by
      intro f; change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ f) = _
      exact AdjoinRoot.lift_of _
    set conj_r := Affine.CoordinateRing.mk W.toAffine
      (Polynomial.C p + Polynomial.C q *
        (-Polynomial.X - Polynomial.C
          (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))) with hconj_def
    have h_factor : algebraMap (Polynomial F) R (Algebra.norm (Polynomial F) r') =
        r' * conj_r := by
      rw [hr'_def, hconj_def]
      change AdjoinRoot.of _ _ = _
      rw [Affine.CoordinateRing.coe_norm_smul_basis, map_mul]
      congr 1
      rw [map_add, map_mul]
      simp [Algebra.smul_def]
    have hr'_zero : mulByInt_coordHom W n hn r' = 0 := by
      have : r' = r := hpq
      rw [this]; exact h_image.trans hr
    have h_norm_zero : mulByInt_xHom W n (Algebra.norm (Polynomial F) r') = 0 := by
      rw [← h_alg, h_factor, map_mul, hr'_zero, zero_mul]
    have h_norm_eq : Algebra.norm (Polynomial F) r' = 0 :=
      hxinj (h_norm_zero.trans (map_zero _).symm)
    rw [hr'_def] at h_norm_eq
    exact norm_smul_basis_ne_zero W p q hq h_norm_eq

theorem mulByInt_coordHom_map_nonZeroDivisors (n : ℤ) (hn : n ≠ 0)
    (s : R) (hs : s ∈ nonZeroDivisors R) :
    IsUnit (mulByInt_coordHom W n hn s) := by
  rw [isUnit_iff_ne_zero]
  intro h
  exact nonZeroDivisors.ne_zero hs
    (mulByInt_coordHom_injective W n hn (h.trans (map_zero _).symm))

/-- The pullback ring hom `[n]* : K(E) → K(E)`, extending `mulByInt_coordHom` to the
fraction field. -/
noncomputable def mulByInt_pullbackRingHom (n : ℤ) (hn : n ≠ 0) : KE →+* KE :=
  IsLocalization.lift (g := mulByInt_coordHom W n hn)
    (fun (a : nonZeroDivisors R) ↦
      mulByInt_coordHom_map_nonZeroDivisors W n hn a.1 a.2)

/-- The pullback algebra hom `[n]* : K(E) →ₐ[F] K(E)` for multiplication-by-`n`. -/
noncomputable def mulByInt_pullbackAlgHom (n : ℤ) (hn : n ≠ 0) : KE →ₐ[F] KE where
  toRingHom := mulByInt_pullbackRingHom W n hn
  commutes' r := by
    change mulByInt_pullbackRingHom W n hn (algebraMap F KE r) = algebraMap F KE r
    rw [show algebraMap F KE r = algebraMap R KE (algebraMap F R r) from
      (IsScalarTower.algebraMap_apply F R KE r).symm]
    change IsLocalization.lift _ (algebraMap R KE (algebraMap F R r)) = _
    rw [IsLocalization.lift_eq]
    change mulByInt_coordHom W n hn (algebraMap F R r) = _
    simp only [mulByInt_coordHom, mulByInt_xHom]
    rw [show algebraMap F R r = Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C (Polynomial.C r)) from rfl]
    rw [AdjoinRoot.lift_mk]
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      show Affine.CoordinateRing.mk W.toAffine (Polynomial.C (Polynomial.C r)) =
        algebraMap F R r from rfl]
    exact (IsScalarTower.algebraMap_apply F R KE r).symm

end HasseWeil
