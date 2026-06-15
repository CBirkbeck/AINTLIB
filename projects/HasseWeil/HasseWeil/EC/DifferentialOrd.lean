/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.NoFinitePolesBridge
import HasseWeil.EC.TranslationOrd
import HasseWeil.WeilPairing.TorsionGeometric

/-!
# The order inequality for the `ω`-derivative (`ord_P` ≤ `ord_P` of the differential + 1)

For an elliptic curve `W/F` with invariant differential `ω = dx/(2y+a₁x+a₃)`, the module of
Kähler differentials `Ω[K(E)/F]` is one-dimensional over `K(E)` (`kaehler_rank_one`), so every
function `f ∈ K(E)` has a unique **`ω`-derivative** `Dω f ∈ K(E)` characterised by
`D f = (Dω f) • ω`.  `Dω` is an `F`-derivation of `K(E)` (it is `KaehlerDifferential.D` composed
with the `K(E)`-linear isomorphism `Ω ≅ K(E)`, `ω ↦ 1`), and on the generators it takes the
*regular* values
* `Dω (x_gen) = u_gen = 2y+a₁x+a₃`  (`Dω_x_gen`),
* `Dω (y_gen) = 3x²+2a₂x+a₄-a₁y`   (`Dω_y_gen`),

both coordinate-ring elements.  Consequently `Dω` maps the coordinate ring `R` into itself
(`Dω_mem_range`), hence is *regular at every smooth point* `P` (`ord_P_Dω_nonneg`), and the usual
Leibniz/uniformiser computation yields the **fundamental order inequality**

  `ord_P (Dω f) ≥ ord_P f − 1`   (`ord_P_Dω_ge`) for `f` regular at `P`.

This is the local form of "a differential lowers the order of vanishing by at most one"; with
`[ℓ]^*ω = ℓ·ω` (`omegaCoeff_mulByInt`) it is the separability/unramifiedness input
`ord_P ([ℓ]^*t) ≤ 1` for the `y`-uniformiser `t` at a 2-torsion image, in *every* characteristic
(in particular char `2`, where the duplication-formula route degenerates).

No algebraic closure of `F` is used.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.4.3.
-/

open WeierstrassCurve HasseWeil.Curves Polynomial

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

/-- The **`ω`-derivative** of `f`: the unique `c ∈ K(E)` with `D f = c • ω`, extracted from the
one-dimensionality of `Ω[K(E)/F]` (`kaehler_rank_one`). -/
noncomputable def Dω (f : KE) : KE :=
  (exists_smul_eq_of_finrank_eq_one (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine) (KaehlerDifferential.D F KE f)).choose

/-- Defining property: `D f = (Dω f) • ω`. -/
theorem Dω_spec (f : KE) :
    KaehlerDifferential.D F KE f = Dω W f • invariantDifferential W.toAffine :=
  (exists_smul_eq_of_finrank_eq_one (kaehler_rank_one W.toAffine)
    (invariantDifferential_ne_zero W.toAffine) (KaehlerDifferential.D F KE f)).choose_spec.symm

/-- Uniqueness reformulation: `c • ω = D f ⟹ c = Dω f`. -/
theorem Dω_eq_of_smul {f : KE} {c : KE}
    (h : c • invariantDifferential W.toAffine = KaehlerDifferential.D F KE f) :
    c = Dω W f :=
  omegaPullbackCoeff_unique W c (Dω W f) (h.trans (Dω_spec W f))

/-- `Dω` is additive. -/
@[simp] theorem Dω_add (f g : KE) : Dω W (f + g) = Dω W f + Dω W g := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [add_smul, ← Dω_spec, ← Dω_spec, map_add]

/-- `Dω` kills base-field constants. -/
@[simp] theorem Dω_algebraMap (a : F) : Dω W (algebraMap F KE a) = 0 := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [zero_smul, (KaehlerDifferential.D F KE).map_algebraMap]

/-- `Dω` of `0`. -/
@[simp] theorem Dω_zero : Dω W (0 : KE) = 0 := by
  simpa using Dω_algebraMap W (0 : F)

/-- Leibniz rule for `Dω`. -/
@[simp] theorem Dω_mul (f g : KE) : Dω W (f * g) = f * Dω W g + g * Dω W f := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [add_smul, mul_smul, mul_smul, ← Dω_spec, ← Dω_spec,
    (KaehlerDifferential.D F KE).leibniz, add_comm]

/-- `Dω` is `F`-homogeneous. -/
@[simp] theorem Dω_smul (a : F) (f : KE) : Dω W (a • f) = a • Dω W f := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [smul_assoc, ← Dω_spec, (KaehlerDifferential.D F KE).map_smul]

/-- `Dω` is subtractive. -/
@[simp] theorem Dω_sub (f g : KE) : Dω W (f - g) = Dω W f - Dω W g := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [sub_smul, ← Dω_spec, ← Dω_spec, map_sub]

/-- `Dω` of a negation. -/
@[simp] theorem Dω_neg (f : KE) : Dω W (-f) = -Dω W f := by
  rw [show (-f : KE) = 0 - f by ring, Dω_sub, Dω_zero, zero_sub]

/-- Power rule for `Dω` (natural exponent). -/
theorem Dω_pow (f : KE) (n : ℕ) : Dω W (f ^ n) = (n : KE) * f ^ (n - 1) * Dω W f := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [(KaehlerDifferential.D F KE).leibniz_pow, Dω_spec W f, smul_smul]
  rw [← Nat.cast_smul_eq_nsmul KE]
  rw [smul_smul, mul_assoc]

/-- `Dω` of an inverse. -/
theorem Dω_inv (f : KE) : Dω W f⁻¹ = -f⁻¹ ^ 2 * Dω W f := by
  refine (Dω_eq_of_smul W ?_).symm
  rw [mul_smul, ← Dω_spec, (KaehlerDifferential.D F KE).leibniz_inv, neg_smul]

/-- `Dω (x_gen) = u_gen`. -/
theorem Dω_x_gen : Dω W (x_gen W) = u_gen W :=
  (Dω_eq_of_smul W (kaehlerD_x_gen_eq_u_smul_omega W).symm).symm

/-- `Dω (y_gen) = 3x²+2a₂x+a₄-a₁y`. -/
theorem Dω_y_gen :
    Dω W (y_gen W) =
      3 * x_gen W ^ 2 + 2 * algebraMap F KE W.a₂ * x_gen W +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W :=
  (Dω_eq_of_smul W (kaehlerD_y_gen_eq_num_smul_omega W).symm).symm

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- The bridge `(p.map φ).evalEval x_gen y_gen = algebraMap R KE (mk p)` (local re-derivation of the
private `evalEval_generic_eq_mk`). -/
theorem evalEval_xy_gen_eq_algebraMap_mk (p : (Polynomial F)[X]) :
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

/-- The coordinate-ring image `R ↪ K(E)` as a subring of `K(E)`. -/
noncomputable def Rimg : Subring KE := (algebraMap R KE).range

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `F`-constants land in the coordinate-ring image. -/
theorem algebraMap_F_mem_Rimg (c : F) : algebraMap F KE c ∈ Rimg W :=
  ⟨algebraMap F R c, (IsScalarTower.algebraMap_apply F R KE c).symm⟩

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `x_gen ∈ Rimg`. -/
theorem x_gen_mem_Rimg : x_gen W ∈ Rimg W :=
  ⟨algebraMap (Polynomial F) R Polynomial.X, rfl⟩

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `y_gen ∈ Rimg`. -/
theorem y_gen_mem_Rimg : y_gen W ∈ Rimg W :=
  ⟨AdjoinRoot.root W.toAffine.polynomial, rfl⟩

/-- `Dω (x_gen)` is in the coordinate-ring image (it is `u_gen`). -/
theorem Dω_x_gen_mem_Rimg : Dω W (x_gen W) ∈ Rimg W := by
  rw [Dω_x_gen, u_gen]
  exact Subring.add_mem _ (Subring.add_mem _
    (Subring.mul_mem _ (natCast_mem _ 2) (y_gen_mem_Rimg W))
    (Subring.mul_mem _ (algebraMap_F_mem_Rimg W W.a₁) (x_gen_mem_Rimg W)))
    (algebraMap_F_mem_Rimg W W.a₃)

/-- `Dω (y_gen)` is in the coordinate-ring image. -/
theorem Dω_y_gen_mem_Rimg : Dω W (y_gen W) ∈ Rimg W := by
  rw [Dω_y_gen]
  exact Subring.sub_mem _ (Subring.add_mem _ (Subring.add_mem _
    (Subring.mul_mem _ (natCast_mem _ 3) (Subring.pow_mem _ (x_gen_mem_Rimg W) 2))
    (Subring.mul_mem _ (Subring.mul_mem _ (natCast_mem _ 2)
      (algebraMap_F_mem_Rimg W W.a₂)) (x_gen_mem_Rimg W))) (algebraMap_F_mem_Rimg W W.a₄))
    (Subring.mul_mem _ (algebraMap_F_mem_Rimg W W.a₁) (y_gen_mem_Rimg W))

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `aeval x_gen q ∈ Rimg` for a univariate polynomial `q ∈ F[X]`. -/
theorem aeval_x_gen_mem_Rimg (q : Polynomial F) :
    Polynomial.aeval (x_gen W) q ∈ Rimg W := by
  induction q using Polynomial.induction_on with
  | C c => rw [Polynomial.aeval_C]; exact algebraMap_F_mem_Rimg W c
  | add q₁ q₂ h₁ h₂ => rw [map_add]; exact Subring.add_mem _ h₁ h₂
  | monomial m c _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact Subring.mul_mem _ (algebraMap_F_mem_Rimg W c)
      (Subring.pow_mem _ (x_gen_mem_Rimg W) (m + 1))

/-- `Dω (aeval x_gen q) ∈ Rimg` for a univariate polynomial `q ∈ F[X]` (poly in `x_gen`). -/
theorem Dω_aeval_x_gen_mem_Rimg (q : Polynomial F) :
    Dω W (Polynomial.aeval (x_gen W) q) ∈ Rimg W := by
  induction q using Polynomial.induction_on with
  | C c => rw [Polynomial.aeval_C, Dω_algebraMap]; exact Subring.zero_mem _
  | add q₁ q₂ h₁ h₂ => rw [map_add, Dω_add]; exact Subring.add_mem _ h₁ h₂
  | monomial m c _ =>
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, Dω_mul, Dω_pow,
      Dω_algebraMap, mul_zero, add_zero]
    exact Subring.mul_mem _ (algebraMap_F_mem_Rimg W c)
      (Subring.mul_mem _ (Subring.mul_mem _ (natCast_mem _ (m + 1))
        (Subring.pow_mem _ (x_gen_mem_Rimg W) (m + 1 - 1))) (Dω_x_gen_mem_Rimg W))

/-- **`Dω` maps the coordinate ring into itself.** For `r : R`, `Dω (algebraMap R KE r) ∈ Rimg`.
Induction over the bivariate presentation `r = mk p`, using `Dω_mul`/`Dω_add`/`Dω_pow` and the
regular generator-values `Dω(x_gen), Dω(y_gen) ∈ Rimg`. -/
theorem Dω_algebraMap_mem_Rimg (r : R) : Dω W (algebraMap R KE r) ∈ Rimg W := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  rw [← evalEval_xy_gen_eq_algebraMap_mk]
  induction p using Polynomial.induction_on with
  | C q =>
    rw [Polynomial.map_C, Polynomial.evalEval_C,
      show (Polynomial.mapRingHom (algebraMap F KE)) q = q.map (algebraMap F KE) from rfl,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact Dω_aeval_x_gen_mem_Rimg W q
  | add p₁ p₂ h₁ h₂ =>
    rw [Polynomial.map_add, Polynomial.evalEval_add, Dω_add]
    exact Subring.add_mem _ h₁ h₂
  | monomial m q _ =>
    rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      Polynomial.evalEval_mul, Polynomial.evalEval_pow, Polynomial.evalEval_X,
      Polynomial.evalEval_C,
      show (Polynomial.mapRingHom (algebraMap F KE) q).eval (x_gen W) =
          Polynomial.aeval (x_gen W) q from by
        rw [show (Polynomial.mapRingHom (algebraMap F KE)) q = q.map (algebraMap F KE) from rfl,
          Polynomial.eval_map, ← Polynomial.aeval_def],
      Dω_mul, Dω_pow]
    exact Subring.add_mem _
      (Subring.mul_mem _ (aeval_x_gen_mem_Rimg W q)
        (Subring.mul_mem _ (Subring.mul_mem _ (natCast_mem _ (m + 1))
          (Subring.pow_mem _ (y_gen_mem_Rimg W) (m + 1 - 1))) (Dω_y_gen_mem_Rimg W)))
      (Subring.mul_mem _ (Subring.pow_mem _ (y_gen_mem_Rimg W) (m + 1))
        (Dω_aeval_x_gen_mem_Rimg W q))

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- An `Rimg`-element has nonnegative order at every smooth point. -/
theorem ord_P_nonneg_of_mem_Rimg {f : KE} (hf : f ∈ Rimg W)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) :
    (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f := by
  obtain ⟨u, rfl⟩ := hf
  by_cases hu : algebraMap R KE u = 0
  · rw [hu, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero]; exact le_top
  · have hv := (⟨W⟩ : SmoothPlaneCurve F).pointValuation_algebraMap_le_one u P
    have hv0 : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P (algebraMap R KE u) ≠ 0 :=
      ((⟨W⟩ : SmoothPlaneCurve F).pointValuation P).ne_zero_iff.mpr hu
    unfold SmoothPlaneCurve.ord_P
    rw [dif_neg hv0, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv0 ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]; exact hv
    have h_toAdd : (WithZero.unzero hv0).toAdd ≤ 0 := h_unz_le
    omega

/-- **`Dω` is regular at `P` on functions regular at `P`.** If `ord_P f ≥ 0`, then
`ord_P (Dω f) ≥ 0`. -/
theorem ord_P_Dω_nonneg {f : KE} (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hf : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f) :
    (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W f) := by
  have hf_le : (⟨W⟩ : SmoothPlaneCurve F).pointValuation P f ≤ 1 := by
    by_cases hf0 : f = 0
    · rw [hf0]; simp
    · exact pointValuation_le_one_of_ord_nonneg W hf0 P hf
  obtain ⟨x, hx⟩ := SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
    (C := (⟨W⟩ : SmoothPlaneCurve F)) f hf_le
  haveI hP : ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P).IsPrime :=
    (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt_isPrime P
  haveI : IsLocalization ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P).primeCompl
      ((⟨W⟩ : SmoothPlaneCurve F).localRingAt P) := Localization.isLocalization
  obtain ⟨⟨a, s⟩, hxas⟩ := IsLocalization.surj
    ((⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P).primeCompl x
  set b : R := (s : R) with hb
  have hbnotmem : b ∉ (⟨W⟩ : SmoothPlaneCurve F).maximalIdealAt P := s.2
  have hb_ne : algebraMap R KE b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R KE)).mpr
      (fun h0 ↦ hbnotmem (h0 ▸ Submodule.zero_mem _))
  have hb_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (algebraMap R KE b) = 0 := by
    by_contra h_ne
    exact hbnotmem (((⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt
      ((map_ne_zero_iff _ (IsFractionRing.injective R KE)).mp hb_ne) P).mp h_ne)
  have hfb : f * algebraMap R KE b = algebraMap R KE a := by
    have := congrArg (algebraMap ((⟨W⟩ : SmoothPlaneCurve F).localRingAt P) KE) hxas
    rwa [map_mul, hx,
      ← IsScalarTower.algebraMap_apply R ((⟨W⟩ : SmoothPlaneCurve F).localRingAt P) KE,
      ← IsScalarTower.algebraMap_apply R ((⟨W⟩ : SmoothPlaneCurve F).localRingAt P) KE] at this
  have hDfb := congrArg (Dω W) hfb
  rw [Dω_mul] at hDfb
  have hDf : Dω W f = (Dω W (algebraMap R KE a) - f * Dω W (algebraMap R KE b))
      * (algebraMap R KE b)⁻¹ := by
    field_simp
    linear_combination hDfb
  rw [hDf, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul,
    (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hb_ne, hb_ord, neg_zero, add_zero]
  have h1 : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W (algebraMap R KE a)) :=
    ord_P_nonneg_of_mem_Rimg W (Dω_algebraMap_mem_Rimg W a) P
  have h2 : (0 : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (-(f * Dω W (algebraMap R KE b))) := by
    rw [SmoothPlaneCurve.ord_P_neg, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    exact add_nonneg hf (ord_P_nonneg_of_mem_Rimg W (Dω_algebraMap_mem_Rimg W b) P)
  rw [sub_eq_add_neg]
  exact le_trans (le_min h1 h2) (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)

/-- **The key order inequality (used form).** If `f` vanishes at `P` to order `≥ 2`
(`ord_P f ≥ 2`), then `ord_P (Dω f) ≥ 1`. Factor `f = g · s` with `s` a uniformizer and
`ord_P g = ord_P f − 1 ≥ 1`; then `Dω f = s · Dω g + g · Dω s`, and both summands vanish at `P`
(`Dω g, Dω s` regular by `ord_P_Dω_nonneg`). -/
theorem one_le_ord_P_Dω_of_two_le {f : KE} (hf_ne : f ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hf : ((2 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P f) :
    ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W f) := by
  obtain ⟨s, hs⟩ := SmoothPlaneCurve.exists_uniformizer (⟨W⟩ : SmoothPlaneCurve F) P
  have hs_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P s = ((1 : ℤ) : WithTop ℤ) := hs
  have hs_ne : s ≠ 0 := SmoothPlaneCurve.Uniformizer.ne_zero hs
  set g : KE := f * s⁻¹ with hg
  have hfgs : f = g * s := by rw [hg, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
  have hg_ne : g ≠ 0 := by rw [hg]; exact mul_ne_zero hf_ne (inv_ne_zero hs_ne)
  have hg_ord : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P g := by
    obtain ⟨mf, hmf⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff f).not.mpr hf_ne)
    obtain ⟨mg, hmg⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff g).not.mpr hg_ne)
    have hsum : (⟨W⟩ : SmoothPlaneCurve F).ord_P P f =
        (⟨W⟩ : SmoothPlaneCurve F).ord_P P g + (⟨W⟩ : SmoothPlaneCurve F).ord_P P s := by
      rw [hfgs, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    rw [← hmf, ← hmg, hs_ord, ← WithTop.coe_add, WithTop.coe_inj] at hsum
    rw [← hmg, WithTop.coe_le_coe]
    have hmf2 : (2 : ℤ) ≤ mf := by rw [← hmf] at hf; exact_mod_cast hf
    omega
  have hg_nonneg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P g :=
    le_trans (by exact_mod_cast (by norm_num : (0 : ℤ) ≤ 1)) hg_ord
  have hs_nonneg : (0 : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P s := by
    rw [hs_ord]; exact_mod_cast (by norm_num : (0 : ℤ) ≤ 1)
  rw [hfgs, Dω_mul]
  have ht1 : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (s * Dω W g) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, hs_ord]
    have hDg := ord_P_Dω_nonneg W (f := g) P hg_nonneg
    have := add_le_add (le_refl (((1 : ℤ) : WithTop ℤ))) hDg
    rwa [add_zero] at this
  have ht2 : ((1 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (g * Dω W s) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul]
    have hDs := ord_P_Dω_nonneg W (f := s) P hs_nonneg
    have := add_le_add hg_ord hDs
    rwa [add_zero] at this
  exact le_trans (le_min ht2 ht1) (SmoothPlaneCurve.ord_P_add_le (P := P) _ _)

/-- **Order-`≥ 2` criterion (the doubling / tangent lemma).**  If `φ ≠ 0` vanishes at `P`
(`ord_P φ ≥ 1`), its `ω`-derivative `Dω φ` also vanishes at `P` (`ord_P (Dω φ) ≥ 1`), and there is a
uniformizer `s` at `P` whose `ω`-derivative is a *unit* (`ord_P (Dω s) = 0`), then `φ` vanishes to
order `≥ 2` at `P`. -/
theorem two_le_ord_P_of_Dω_vanishes_of_uniformizer {φ s : KE} (hφ_ne : φ ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint)
    (hφ : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P φ)
    (hDφ : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W φ))
    (hs : (⟨W⟩ : SmoothPlaneCurve F).ord_P P s = ((1 : ℤ) : WithTop ℤ))
    (hDs : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W s) = 0) :
    ((2 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P φ := by
  by_contra! hlt
  have hφ_eq : (⟨W⟩ : SmoothPlaneCurve F).ord_P P φ = ((1 : ℤ) : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff φ).not.mpr hφ_ne)
    rw [← hm] at hφ hlt ⊢
    rw [WithTop.coe_le_coe] at hφ; rw [WithTop.coe_lt_coe] at hlt
    rw [WithTop.coe_inj]; omega
  have hs_ne : s ≠ 0 := fun h0 ↦ by
    rw [h0, (⟨W⟩ : SmoothPlaneCurve F).ord_P_zero] at hs
    exact (by simp : (⊤ : WithTop ℤ) ≠ _) hs
  set w : KE := φ * s⁻¹ with hw
  have hw_ne : w ≠ 0 := mul_ne_zero hφ_ne (inv_ne_zero hs_ne)
  have hw_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P w = 0 := by
    rw [hw, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, (⟨W⟩ : SmoothPlaneCurve F).ord_P_inv _ hs_ne,
      hφ_eq, hs]; simp
  have hφws : φ = w * s := by rw [hw, mul_assoc, inv_mul_cancel₀ hs_ne, mul_one]
  have hDφ_eq : Dω W φ = w * Dω W s + s * Dω W w := by rw [hφws, Dω_mul]
  have hterm1 : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (w * Dω W s) = 0 := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, hw_ord, hDs, add_zero]
  have hterm2 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨W⟩ : SmoothPlaneCurve F).ord_P P (s * Dω W w) := by
    rw [(⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, hs]
    have hDw_nonneg := ord_P_Dω_nonneg W (f := w) P (by rw [hw_ord])
    have := add_le_add (le_refl (((1 : ℤ) : WithTop ℤ))) hDw_nonneg
    rwa [add_zero] at this
  have hDφ_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (Dω W φ) = 0 := by
    rw [hDφ_eq,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_add_eq_of_lt
        (by rw [hterm1]; exact lt_of_lt_of_le (by simp) hterm2), hterm1]
  rw [hDφ_ord] at hDφ
  exact absurd hDφ (by simp)

/-- **`Dω (α^*x_gen) = α^*u · a_α`** for any isogeny `α` (the chain rule on `x_gen`, read
through the `ω`-derivative). -/
theorem Dω_isog_pullback_x_gen (α : Isogeny W.toAffine W.toAffine) :
    Dω W (α.pullback (x_gen W)) = alpha_star_u W α * omegaPullbackCoeff W α :=
  (Dω_eq_of_smul W
    (kaehlerD_alpha_pullback_x_eq_smul_omega W α).symm).symm

set_option linter.unusedDecidableInType false in
/-- **General differential `e ≤ 1` bound (x-coordinate, non-2-torsion image).**  For an isogeny `α`
with separable invariant-differential coefficient `a_α = omegaPullbackCoeff W α ≠ 0`, if the pulled
back differential denominator `α^*u = alpha_star_u W α` is a *unit* at `P` (`ord_P = 0`, the
non-2-torsion-image condition `u(α(P)) ≠ 0`), then `α^*x_gen − x_Q` has order `≤ 1` at `P`.

`Dω (α^*x_gen − x_Q) = α^*u · a_α` is then a unit at `P` (both factors units — `a_α` a nonzero
base-field constant, `α^*u` a unit by hypothesis), so by `one_le_ord_P_Dω_of_two_le` the function
cannot vanish to order `≥ 2`. -/
theorem ord_P_isog_pullback_x_sub_const_le_one (α : Isogeny W.toAffine W.toAffine)
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range)
    (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (x_Q : F)
    (hf_ne : α.pullback (x_gen W) - algebraMap F KE x_Q ≠ 0)
    (h_u : (⟨W⟩ : SmoothPlaneCurve F).ord_P P (alpha_star_u W α) = 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (x_gen W) - algebraMap F KE x_Q) ≤
      ((1 : ℤ) : WithTop ℤ) := by
  have hDω_eq : Dω W (α.pullback (x_gen W) - algebraMap F KE x_Q) =
      alpha_star_u W α * omegaPullbackCoeff W α := by
    rw [Dω_sub, Dω_algebraMap, sub_zero, Dω_isog_pullback_x_gen W α]
  obtain ⟨c, hc⟩ := hcoeff
  have hc_ne : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact hcoeff_ne hc.symm
  have hDω_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (Dω W (α.pullback (x_gen W) - algebraMap F KE x_Q)) = 0 := by
    rw [hDω_eq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, h_u, ← hc,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero hc_ne, add_zero]
  by_contra! hlt
  have h2le : ((2 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (x_gen W) - algebraMap F KE x_Q) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff _).not.mpr hf_ne)
    rw [← hm] at hlt ⊢
    rw [WithTop.coe_lt_coe] at hlt
    rw [WithTop.coe_le_coe]; omega
  have := one_le_ord_P_Dω_of_two_le W hf_ne P h2le
  rw [hDω_ord] at this
  exact absurd this (by simp)

/-- **`Dω (α^*y_gen) = α^*ν · a_α`** for any isogeny `α`, where
`α^*ν = 3(α^*x)²+2a₂(α^*x)+a₄−a₁(α^*y)` is the pulled-back `y`-numerator (the chain rule on `y_gen`,
read through the `ω`-derivative).  Direct from `kaehlerD_alpha_pullback_y_eq_smul_omega` via
`Dω_eq_of_smul`. -/
theorem Dω_isog_pullback_y_gen (α : Isogeny W.toAffine W.toAffine) :
    Dω W (α.pullback (y_gen W)) =
      (3 * (α.pullback (x_gen W)) ^ 2 + 2 * algebraMap F KE W.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (α.pullback (y_gen W))) *
        omegaPullbackCoeff W α :=
  (Dω_eq_of_smul W
    (kaehlerD_alpha_pullback_y_eq_smul_omega W α).symm).symm

set_option linter.unusedDecidableInType false in
/-- **General differential `e ≤ 1` bound (y-coordinate, 2-torsion image).**  For an isogeny `α` with
separable invariant-differential coefficient `a_α = omegaPullbackCoeff W α ≠ 0`, if the pulled-back
`y`-numerator `α^*ν = 3(α^*x)²+2a₂(α^*x)+a₄−a₁(α^*y)` is a *unit* at `P` (`ord_P = 0`, the condition
`ν(α(P)) ≠ 0`, automatic at a 2-torsion image), then `α^*y_gen − y_Q` has order `≤ 1` at `P`.

`Dω (α^*y_gen − y_Q) = α^*ν · a_α` is then a unit at `P`, so by `one_le_ord_P_Dω_of_two_le` the
function cannot vanish to order `≥ 2`. -/
theorem ord_P_isog_pullback_y_sub_const_le_one (α : Isogeny W.toAffine W.toAffine)
    (hcoeff : omegaPullbackCoeff W α ∈ (algebraMap F KE).range)
    (hcoeff_ne : omegaPullbackCoeff W α ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (y_Q : F)
    (hf_ne : α.pullback (y_gen W) - algebraMap F KE y_Q ≠ 0)
    (h_ν : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        (3 * (α.pullback (x_gen W)) ^ 2 + 2 * algebraMap F KE W.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (α.pullback (y_gen W))) = 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (y_gen W) - algebraMap F KE y_Q) ≤
      ((1 : ℤ) : WithTop ℤ) := by
  have hDω_eq : Dω W (α.pullback (y_gen W) - algebraMap F KE y_Q) =
      (3 * (α.pullback (x_gen W)) ^ 2 + 2 * algebraMap F KE W.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (α.pullback (y_gen W))) *
        omegaPullbackCoeff W α := by
    rw [Dω_sub, Dω_algebraMap, sub_zero, Dω_isog_pullback_y_gen W α]
  obtain ⟨c, hc⟩ := hcoeff
  have hc_ne : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact hcoeff_ne hc.symm
  have hDω_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (Dω W (α.pullback (y_gen W) - algebraMap F KE y_Q)) = 0 := by
    rw [hDω_eq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, h_ν, ← hc,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero hc_ne, add_zero]
  by_contra! hlt
  have h2le : ((2 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (α.pullback (y_gen W) - algebraMap F KE y_Q) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff _).not.mpr hf_ne)
    rw [← hm] at hlt ⊢
    rw [WithTop.coe_lt_coe] at hlt
    rw [WithTop.coe_le_coe]; omega
  have := one_le_ord_P_Dω_of_two_le W hf_ne P h2le
  rw [hDω_ord] at this
  exact absurd this (by simp)

/-- `Dω ((mulByInt ℓ).pullback y_gen) = (3X²+2a₂X+a₄−a₁Y) · ℓ`, where `X = mulByInt_x`,
`Y = mulByInt_y`. (Chain rule + `[ℓ]^*ω = ℓω`, from `kaehlerD_alpha_pullback_y_eq_smul_omega` and
`omegaCoeff_mulByInt`.) -/
theorem Dω_mulByInt_pullback_y_gen (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    Dω W ((mulByInt W.toAffine ℓ).pullback (y_gen W)) =
      (3 * ((mulByInt W.toAffine ℓ).pullback (x_gen W)) ^ 2 +
          2 * algebraMap F KE W.a₂ * ((mulByInt W.toAffine ℓ).pullback (x_gen W)) +
          algebraMap F KE W.a₄ -
          algebraMap F KE W.a₁ * ((mulByInt W.toAffine ℓ).pullback (y_gen W))) *
        algebraMap F KE ℓ := by
  have hkey := kaehlerD_alpha_pullback_y_eq_smul_omega
    W (mulByInt W.toAffine ℓ)
  rw [omegaCoeff_mulByInt W ℓ hℓ] at hkey
  exact (Dω_eq_of_smul W hkey.symm).symm

set_option linter.unusedDecidableInType false in
/-- **The differential `e = 1` bound.** With `[ℓ]` separable (`(ℓ:F) ≠ 0`) and the pulled-back
`y`-numerator `[ℓ]^*polynomialX = 3X²+2a₂X+a₄−a₁Y` a unit at `P` (hypothesis `hPX`), the
function `mulByInt_y ℓ − y_Q` has order `≤ 1` at `P`. -/
theorem ord_P_mulByInt_y_sub_const_le_one (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0)
    (P : (⟨W⟩ : SmoothPlaneCurve F).SmoothPoint) (y_Q : F)
    (hf_ne : mulByInt_y W ℓ - algebraMap F KE y_Q ≠ 0)
    (hPX : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
        (3 * (mulByInt_x W ℓ) ^ 2 + 2 * algebraMap F KE W.a₂ * (mulByInt_x W ℓ) +
          algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (mulByInt_y W ℓ)) = 0) :
    (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_y W ℓ - algebraMap F KE y_Q) ≤
      ((1 : ℤ) : WithTop ℤ) := by
  have hDω_eq : Dω W (mulByInt_y W ℓ - algebraMap F KE y_Q) =
      (3 * (mulByInt_x W ℓ) ^ 2 + 2 * algebraMap F KE W.a₂ * (mulByInt_x W ℓ) +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (mulByInt_y W ℓ)) *
        algebraMap F KE (ℓ : F) := by
    rw [Dω_sub, Dω_algebraMap, sub_zero,
      show mulByInt_x W ℓ = (mulByInt W.toAffine ℓ).pullback (x_gen W) from
        (mulByInt_pullback_x W ℓ hℓ).symm,
      show mulByInt_y W ℓ = (mulByInt W.toAffine ℓ).pullback (y_gen W) from
        (mulByInt_pullback_y W ℓ hℓ).symm,
      Dω_mulByInt_pullback_y_gen W ℓ hℓ]
  have hDω_ord : (⟨W⟩ : SmoothPlaneCurve F).ord_P P
      (Dω W (mulByInt_y W ℓ - algebraMap F KE y_Q)) = 0 := by
    rw [hDω_eq, (⟨W⟩ : SmoothPlaneCurve F).ord_P_mul, hPX,
      (⟨W⟩ : SmoothPlaneCurve F).ord_P_algebraMap_F_of_ne_zero hℓF, add_zero]
  by_contra! hlt
  have h2le : ((2 : ℤ) : WithTop ℤ) ≤
      (⟨W⟩ : SmoothPlaneCurve F).ord_P P (mulByInt_y W ℓ - algebraMap F KE y_Q) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (((⟨W⟩ : SmoothPlaneCurve F).ord_P_eq_top_iff _).not.mpr hf_ne)
    rw [← hm] at hlt ⊢
    rw [WithTop.coe_lt_coe] at hlt
    rw [WithTop.coe_le_coe]; omega
  have := one_le_ord_P_Dω_of_two_le W hf_ne P h2le
  rw [hDω_ord] at this
  exact absurd this (by simp)

end HasseWeil
