/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.CurveMap

/-!
# Module-finiteness along a coordinate-ring witness (the standing `hfin`, DERIVED)

For a curve map `φ : C₁ → C₂` with a coordinate-ring pullback witness
`cd : φ.CoordHom`, the coordinate ring `F[C₁]` is a **finite module** over
`F[C₂]` via `cd.toAlgebra` — *unconditionally*.  This derives the standing
`Module.Finite` hypothesis (`hfin`) carried throughout the isogeny theory by
`CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`,
`EC.Isogeny.addHomProperty` / `toBasicIsogeny` (K̄-level),
`EC.Isogeny.addHomProperty_descend_of_finite` / `toBasicIsogenyDescend`
(K-level), `Isogeny.pushforward` (`Curves/PushforwardDivisor.lean`),
`EC/KernelCount.lean`, and friends.

## The proof (no separability, no places classification)

Write `u := ψ(x₂) ∈ F[C₁]` for the image of the coordinate generator of `C₂`
under an injective `F`-algebra map `ψ : F[C₂] →ₐ[F] F[C₁]`, and decompose
`u = p•1 + q•Y` in the `{1, Y}` basis of `F[C₁]` over `F[x₁] = F[X]`.  Then
`u` satisfies the quadratic relation of its conjugate pair over `F[X]`:

`u² − t(x₁)·u + n(x₁) = 0`, where `t := 2p − q·(a₁X + a₃)` and
`n := p² − pq·(a₁X + a₃) − q²·(X³ + a₂X² + a₄X + a₆)`

(`n` is mathlib's `Algebra.norm F[X] u`; the difference of the two sides is
`q²·W(X, Y)`, which vanishes mod the Weierstrass polynomial).  Reading the
relation backwards as a polynomial in `x₁` with coefficients in the image of
`ψ` gives `n(T) − u·t(T) + u² = 0` at `T = x₁`.

**The parity trick**: `deg(p²) = 2 deg p` is even while
`deg(q²·(X³ + ⋯)) = 2 deg q + 3` is odd, so the two leading terms never
cancel: `deg n = max(2 deg p, 2 deg q + 3)` with leading coefficient a
**unit of `F`** (`WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`),
and `deg t < deg n`.  Hence the displayed `T`-polynomial is monic after
scaling by that unit's inverse, with coefficients in the image of `F[C₂]`:
the generator `x₁` is **integral** over `F[C₂]`.  (`u ∉ F·1` because `ψ` is
injective, ruling out the degenerate `q = 0 ∧ p constant` case.)  Since
`F[C₁]` is spanned by `F[x₁]·{1, Y}`, module-finiteness follows from
`IsIntegral.fg_adjoin_singleton`.

This argument works in **any characteristic and for inseparable maps** (for
the Frobenius comorphism `u = x₁^p` it produces the monic witness
`(T^p − u)²`-style relation), so no separability hypothesis, no AKLB
machinery, and no Nagata-style finiteness of integral closures is needed.
The classical "places of `K(C₁)` over affine places of `C₂` are point
places" wall is bypassed entirely by the explicit Weierstrass presentation.

## Main results

* `algHom_coordinateRing_isIntegralElem_X` — the keystone: the coordinate
  generator `x₁` is integral over `F[C₂]` along any injective `F`-algebra
  hom `F[C₂] →ₐ[F] F[C₁]`.
* `algHom_coordinateRing_module_finite` — `F[C₁]` is a finite module over
  `F[C₂]` along any injective `F`-algebra hom.
* `CurveMap.CoordHom.toAlgHom_injective` — a `CoordHom` is automatically
  injective (from `compat` plus injectivity of the function-field pullback).
* `CurveMap.CoordHom.module_finite` — **the deliverable**: the standing
  `hfin` hypothesis holds for every `(φ, cd)`, with no further assumptions.
* `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree'` — Silverman
  II.2.6(a) `Σ e·f = deg φ` with `hfin` discharged.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.6, II.3 (finiteness
  of morphisms of smooth curves) — obtained here by direct
  Weierstrass-presentation algebra instead of valuation theory.
-/

namespace HasseWeil.Curves

open Polynomial WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

variable {F : Type*} [Field F]

/-! ### The quadratic relation of a coordinate-ring element over `F[X]` -/

section Quadratic

variable (C : SmoothPlaneCurve F)

/-- `algebraMap F[X] F[C]` is reduction mod the Weierstrass polynomial of
the constant-in-`Y` embedding `C : F[X] → F[X][Y]`. -/
theorem algebraMap_coordinateRing_eq_mk_C (g : Polynomial F) :
    algebraMap (Polynomial F) C.CoordinateRing g =
      CoordinateRing.mk C.toAffine (Polynomial.C g) := by
  rw [Algebra.algebraMap_eq_smul_one, CoordinateRing.smul, mul_one]

/-- Evaluating a polynomial with `F`-coefficients at the coordinate
generator `x = X mod W` recovers the image under `algebraMap F[X] F[C]`. -/
theorem aeval_algebraMap_X (g : Polynomial F) :
    Polynomial.aeval (algebraMap (Polynomial F) C.CoordinateRing Polynomial.X) g =
      algebraMap (Polynomial F) C.CoordinateRing g := by
  rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]

/-- **The quadratic relation**: every `u = p•1 + q•Y ∈ F[C]` satisfies
`u² − t(x)·u + n(x) = 0`, where `t := 2p − q(a₁X + a₃)` is its trace and
`n := p² − pq(a₁X + a₃) − q²(X³ + a₂X² + a₄X + a₆)` its norm over `F[X]`
(cf. `WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis`).  The
difference of the two sides is `q²·W(X, Y)`, which vanishes in `F[C]`. -/
theorem smul_basis_quadratic_relation (p q : Polynomial F) :
    (p • (1 : C.CoordinateRing) + q • CoordinateRing.mk C.toAffine Y) ^ 2 -
        algebraMap (Polynomial F) C.CoordinateRing
            (2 * p - q * (Polynomial.C C.toAffine.a₁ * Polynomial.X +
              Polynomial.C C.toAffine.a₃)) *
          (p • (1 : C.CoordinateRing) + q • CoordinateRing.mk C.toAffine Y) +
        algebraMap (Polynomial F) C.CoordinateRing
          (p ^ 2 - p * q * (Polynomial.C C.toAffine.a₁ * Polynomial.X +
              Polynomial.C C.toAffine.a₃) -
            q ^ 2 * (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
              Polynomial.C C.toAffine.a₄ * Polynomial.X + Polynomial.C C.toAffine.a₆)) = 0 := by
  have hb : p • (1 : C.CoordinateRing) + q • CoordinateRing.mk C.toAffine Y =
      CoordinateRing.mk C.toAffine (Polynomial.C p + Polynomial.C q * Y) := by
    rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul]
  have key : (Polynomial.C p + Polynomial.C q * Y) ^ 2 -
      Polynomial.C (2 * p - q * (Polynomial.C C.toAffine.a₁ * Polynomial.X +
        Polynomial.C C.toAffine.a₃)) * (Polynomial.C p + Polynomial.C q * Y) +
      Polynomial.C (p ^ 2 - p * q * (Polynomial.C C.toAffine.a₁ * Polynomial.X +
          Polynomial.C C.toAffine.a₃) -
        q ^ 2 * (Polynomial.X ^ 3 + Polynomial.C C.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C C.toAffine.a₄ * Polynomial.X + Polynomial.C C.toAffine.a₆)) =
      Polynomial.C (q ^ 2) * C.toAffine.polynomial := by
    rw [WeierstrassCurve.Affine.polynomial]
    simp only [map_ofNat, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow]
    ring1
  rw [hb, algebraMap_coordinateRing_eq_mk_C, algebraMap_coordinateRing_eq_mk_C, ← map_pow,
    ← map_mul, ← map_sub, ← map_add, key, map_mul, AdjoinRoot.mk_self, mul_zero]

end Quadratic

/-! ### The keystone integrality -/

section Integrality

variable {C₁ C₂ : SmoothPlaneCurve F}

/-- Auxiliary: evaluating (via `eval₂` along `ψ`) the coefficient-wise image
in `F[C₂][T]` of a polynomial `g ∈ F[X]` at the coordinate generator `x₁`
recovers `g(x₁) = algebraMap F[X] F[C₁] g`. -/
private theorem eval₂_map_algebraMap (ψ : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing)
    (g : Polynomial F) :
    Polynomial.eval₂ ψ.toRingHom (algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X)
      (g.map (algebraMap F C₂.CoordinateRing)) =
    algebraMap (Polynomial F) C₁.CoordinateRing g := by
  rw [Polynomial.eval₂_map,
    show ψ.toRingHom.comp (algebraMap F C₂.CoordinateRing) = algebraMap F C₁.CoordinateRing from
      RingHom.ext fun c => ψ.commutes c,
    ← Polynomial.aeval_def, aeval_algebraMap_X]

/-- Auxiliary: a `RingHom.IsIntegralElem` witness from an `F[X]`-polynomial
`n` of positive degree (whose leading coefficient is automatically a unit of
the field `F`) plus a lower-order tail `r` over `F[C₂]`, given the root
identity for `n.map (algebraMap F F[C₂]) + r`. -/
private theorem isIntegralElem_aux (ψ : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing)
    {n : Polynomial F} {r : Polynomial C₂.CoordinateRing} {ξ : C₁.CoordinateRing}
    (h0 : 0 < n.degree) (hr : r.degree < n.degree)
    (hroot : Polynomial.eval₂ ψ.toRingHom ξ
      (n.map (algebraMap F C₂.CoordinateRing) + r) = 0) :
    ψ.toRingHom.IsIntegralElem ξ := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Polynomial.degree_zero] at h0
    simp at h0
  have hinj : Function.Injective (algebraMap F C₂.CoordinateRing) :=
    (algebraMap F C₂.CoordinateRing).injective
  have hdeg_nh : (n.map (algebraMap F C₂.CoordinateRing)).degree = n.degree :=
    Polynomial.degree_map_eq_of_injective hinj n
  have hdeg_big : (n.map (algebraMap F C₂.CoordinateRing) + r).degree = n.degree := by
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by rw [hdeg_nh]; exact hr), hdeg_nh]
  have hN : (n.map (algebraMap F C₂.CoordinateRing) + r).natDegree = n.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (by rw [hdeg_big, Polynomial.degree_eq_natDegree hn0])
  have hrcoeff : r.coeff n.natDegree = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt
      (hr.trans_le (Polynomial.degree_eq_natDegree hn0).le)
  have hcoeff : (n.map (algebraMap F C₂.CoordinateRing) + r).coeff n.natDegree =
      algebraMap F C₂.CoordinateRing n.leadingCoeff := by
    rw [Polynomial.coeff_add, Polynomial.coeff_map, hrcoeff, add_zero]
    rfl
  refine ⟨Polynomial.C (algebraMap F C₂.CoordinateRing n.leadingCoeff⁻¹) *
    (n.map (algebraMap F C₂.CoordinateRing) + r), ?_, ?_⟩
  · refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    have hlead : (n.map (algebraMap F C₂.CoordinateRing) + r).leadingCoeff =
        algebraMap F C₂.CoordinateRing n.leadingCoeff := by
      rw [Polynomial.leadingCoeff, hN, hcoeff]
    rw [hlead, ← map_mul,
      inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hn0), map_one]
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hroot, mul_zero]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Instance synthesis and unification at curve-indexed coordinate-ring types
-- (`AdjoinRoot`-quotients) need a higher budget; same settings as
-- `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`.
/-- **Keystone integrality**: along any *injective* `F`-algebra homomorphism
`ψ : F[C₂] →ₐ[F] F[C₁]` of Weierstrass coordinate rings, the coordinate
generator `x₁ = X mod W₁ ∈ F[C₁]` is integral over `F[C₂]`.

The monic witness is the conjugate-pair ("norm") relation of
`u := ψ(x₂) = p•1 + q•Y` read as a polynomial in `x₁`: parity of degrees
(`2 deg p` even versus `2 deg q + 3` odd) forces its leading coefficient to
be a unit of `F`.  Injectivity of `ψ` excludes the degenerate case
`u ∈ F·1`.  No separability assumption is involved. -/
theorem algHom_coordinateRing_isIntegralElem_X
    (ψ : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing) (hψ : Function.Injective ψ) :
    ψ.toRingHom.IsIntegralElem
      (algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X) := by
  classical
  obtain ⟨p, q, hu⟩ := CoordinateRing.exists_smul_basis_eq
    (W' := C₁.toAffine) (ψ (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X))
  -- the degenerate case `u ∈ F·1` contradicts injectivity of `ψ`
  have hnondeg : q ≠ 0 ∨ 0 < p.degree := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hq0, hp0⟩ := hcon
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_degree_le_zero hp0
    have hu' : ψ (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X) =
        algebraMap F C₁.CoordinateRing (p.coeff 0) := by
      rw [← hu, hq0, zero_smul, add_zero, hpC, Algebra.smul_def, mul_one,
        IsScalarTower.algebraMap_apply F (Polynomial F) C₁.CoordinateRing,
        Polynomial.algebraMap_eq, Polynomial.coeff_C_zero]
    have hX : algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X =
        algebraMap (Polynomial F) C₂.CoordinateRing (Polynomial.C (p.coeff 0)) := by
      apply hψ
      rw [hu', ← ψ.commutes (p.coeff 0),
        IsScalarTower.algebraMap_apply F (Polynomial F) C₂.CoordinateRing,
        Polynomial.algebraMap_eq]
    exact Polynomial.X_ne_C _
      (FaithfulSMul.algebraMap_injective (Polynomial F) C₂.CoordinateRing hX)
  by_cases hq : q = 0
  · -- linear case: `u = p(x₁)` with `p` nonconstant; witness `p(T) − x₂`
    subst hq
    rw [zero_smul, add_zero] at hu
    have hp0 : 0 < p.degree := hnondeg.resolve_left fun h => h rfl
    refine isIntegralElem_aux ψ (n := p)
      (r := -Polynomial.C (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X))
      hp0 (lt_of_le_of_lt ((Polynomial.degree_neg _).trans_le Polynomial.degree_C_le) hp0) ?_
    rw [Polynomial.eval₂_add, Polynomial.eval₂_neg, Polynomial.eval₂_C,
      eval₂_map_algebraMap,
      show algebraMap (Polynomial F) C₁.CoordinateRing p = p • (1 : C₁.CoordinateRing) by
        rw [Algebra.smul_def, mul_one],
      hu]
    exact add_neg_cancel _
  · -- quadratic case: the conjugate-pair relation
    have hrel := smul_basis_quadratic_relation C₁ p q
    have hnorm : (p ^ 2 - p * q * (Polynomial.C C₁.toAffine.a₁ * Polynomial.X +
          Polynomial.C C₁.toAffine.a₃) -
        q ^ 2 * (Polynomial.X ^ 3 + Polynomial.C C₁.toAffine.a₂ * Polynomial.X ^ 2 +
          Polynomial.C C₁.toAffine.a₄ * Polynomial.X + Polynomial.C C₁.toAffine.a₆)).degree =
        max (2 • p.degree) (2 • q.degree + 3) := by
      rw [← CoordinateRing.norm_smul_basis (W' := C₁.toAffine)]
      exact CoordinateRing.degree_norm_smul_basis p q
    set s : Polynomial F := Polynomial.C C₁.toAffine.a₁ * Polynomial.X +
      Polynomial.C C₁.toAffine.a₃ with hs
    set f : Polynomial F := Polynomial.X ^ 3 + Polynomial.C C₁.toAffine.a₂ * Polynomial.X ^ 2 +
      Polynomial.C C₁.toAffine.a₄ * Polynomial.X + Polynomial.C C₁.toAffine.a₆ with hf
    set t : Polynomial F := 2 * p - q * s with ht
    set n : Polynomial F := p ^ 2 - p * q * s - q ^ 2 * f with hn
    -- degree bookkeeping: `deg t < deg n` and `0 < deg n`
    have h2le : ((2 : Polynomial F)).degree ≤ 0 := by
      rw [← map_ofNat (Polynomial.C : F →+* Polynomial F) 2]
      exact Polynomial.degree_C_le
    have hsle : s.degree ≤ 1 := Polynomial.degree_linear_le
    have htle : t.degree ≤ max p.degree (q.degree + 1) := by
      refine (Polynomial.degree_sub_le _ _).trans (max_le_max ?_ ?_)
      · refine (Polynomial.degree_mul_le _ _).trans ?_
        calc (2 : Polynomial F).degree + p.degree ≤ 0 + p.degree := by gcongr
          _ = p.degree := zero_add _
      · refine (Polynomial.degree_mul_le _ _).trans ?_
        gcongr
    obtain ⟨b, hqd⟩ : ∃ b : ℕ, q.degree = (b : WithBot ℕ) :=
      ⟨q.natDegree, Polynomial.degree_eq_natDegree hq⟩
    rw [hqd] at htle hnorm
    have h0n : 0 < n.degree := by
      rw [hnorm]
      refine lt_max_of_lt_right ?_
      rw [two_nsmul]
      exact_mod_cast (by omega : 0 < b + b + 3)
    have htn : t.degree < n.degree := by
      refine lt_of_le_of_lt htle (max_lt ?_ ?_)
      · -- `p.degree < deg n`
        rw [hnorm]
        rcases eq_or_ne p 0 with hp0 | hp0
        · -- `p = 0`: `⊥ <` anything finite
          rw [hp0, Polynomial.degree_zero]
          refine lt_max_of_lt_right ?_
          rw [two_nsmul]
          exact lt_of_lt_of_le (WithBot.bot_lt_coe 0)
            (by exact_mod_cast (by omega : 0 ≤ b + b + 3))
        · obtain ⟨a, hpd⟩ : ∃ a : ℕ, p.degree = (a : WithBot ℕ) :=
            ⟨p.natDegree, Polynomial.degree_eq_natDegree hp0⟩
          rw [hpd]
          rcases le_or_gt a (b + 1) with hab | hab
          · refine lt_max_of_lt_right ?_
            rw [two_nsmul]
            exact_mod_cast (by omega : a < b + b + 3)
          · refine lt_max_of_lt_left ?_
            rw [two_nsmul]
            exact_mod_cast (by omega : a < a + a)
      · -- `q.degree + 1 < deg n`
        rw [hnorm]
        refine lt_max_of_lt_right ?_
        rw [two_nsmul]
        exact_mod_cast (by omega : b + 1 < b + b + 3)
    -- assemble the integrality witness
    refine isIntegralElem_aux ψ (n := n)
      (r := Polynomial.C ((algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X) ^ 2) -
        Polynomial.C (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X) *
          t.map (algebraMap F C₂.CoordinateRing))
      h0n ?_ ?_
    · refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt Polynomial.degree_C_le h0n
      · refine lt_of_le_of_lt ?_ htn
        refine (Polynomial.degree_mul_le _ _).trans ?_
        have hC : (Polynomial.C (algebraMap (Polynomial F) C₂.CoordinateRing
            Polynomial.X)).degree ≤ 0 := Polynomial.degree_C_le
        have hmap : (t.map (algebraMap F C₂.CoordinateRing)).degree ≤ t.degree :=
          Polynomial.degree_map_le
        calc (Polynomial.C (algebraMap (Polynomial F) C₂.CoordinateRing
              Polynomial.X)).degree + (t.map (algebraMap F C₂.CoordinateRing)).degree ≤
            0 + t.degree := by gcongr
          _ = t.degree := zero_add _
    · have hu' : p • (1 : C₁.CoordinateRing) + q • CoordinateRing.mk C₁.toAffine Y =
          ψ.toRingHom (algebraMap (Polynomial F) C₂.CoordinateRing Polynomial.X) := hu
      rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_C, eval₂_map_algebraMap ψ n,
        eval₂_map_algebraMap ψ t, map_pow, ← hu']
      linear_combination hrel

end Integrality

/-! ### Module-finiteness -/

/-- Abstract assembly step (stated over general commutative rings to avoid
instance-diamond friction at coordinate-ring types): if `x` is integral over
`R` and `A` is spanned over `R[x]` by a finite set `s`, then `A` is a finite
`R`-module. -/
private theorem module_finite_of_adjoin_singleton_mul_span
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : A} (hx : IsIntegral R x) {s : Set A} (hs : s.Finite)
    (hspan : (⊤ : Submodule R A) ≤
      Subalgebra.toSubmodule (Algebra.adjoin R {x}) * Submodule.span R s) :
    Module.Finite R A :=
  Module.finite_def.mpr (top_le_iff.mp hspan ▸
    Submodule.FG.mul hx.fg_adjoin_singleton (Submodule.fg_span hs))

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Instance synthesis and unification at curve-indexed coordinate-ring types
-- (`AdjoinRoot`-quotients) need a higher budget; same settings as
-- `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`.
/-- **`F[C₁]` is a finite module over `F[C₂]` along any injective
`F`-algebra homomorphism** `ψ : F[C₂] →ₐ[F] F[C₁]` of Weierstrass coordinate
rings (the module structure being `ψ.toRingHom.toAlgebra`).

Proof: the coordinate generator `x₁` is integral over `F[C₂]`
(`algHom_coordinateRing_isIntegralElem_X`), so `F[C₂][x₁]` is a finite
module; and `F[C₁] = F[C₂][x₁]·{1, Y}` by the `{1, Y}` basis over `F[X]`
(every `F`-coefficient lies in the image of `ψ` since `ψ` is an
`F`-algebra map). -/
theorem algHom_coordinateRing_module_finite
    {C₁ C₂ : SmoothPlaneCurve F}
    (ψ : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing) (hψ : Function.Injective ψ) :
    @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      ψ.toRingHom.toAlgebra.toModule := by
  letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := ψ.toRingHom.toAlgebra
  letI : Module C₂.CoordinateRing C₁.CoordinateRing := Algebra.toModule
  haveI : IsScalarTower F C₂.CoordinateRing C₁.CoordinateRing :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have hx : IsIntegral C₂.CoordinateRing
      (algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X) :=
    algHom_coordinateRing_isIntegralElem_X ψ hψ
  -- polynomials in `x₁` with `F`-coefficients lie in the `F[C₂]`-adjoin of `x₁`
  have hadj : ∀ g : Polynomial F, algebraMap (Polynomial F) C₁.CoordinateRing g ∈
      Algebra.adjoin C₂.CoordinateRing
        {algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X} := by
    intro g
    rw [← aeval_algebraMap_X C₁ g]
    have h1 : Polynomial.aeval (algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X) g ∈
        Algebra.adjoin F {algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨g, rfl⟩
    have h2 : Algebra.adjoin F
        {algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X} ≤
        (Algebra.adjoin C₂.CoordinateRing
          {algebraMap (Polynomial F) C₁.CoordinateRing Polynomial.X}).restrictScalars F :=
      Algebra.adjoin_le_iff.mpr fun w hw => Algebra.subset_adjoin hw
    exact h2 h1
  -- assemble via the abstract lemma; the `{1, Y}` basis spans `F[C₁]` over the adjoin
  refine module_finite_of_adjoin_singleton_mul_span hx
    (Set.toFinite ({1, CoordinateRing.mk C₁.toAffine Y} : Set C₁.CoordinateRing)) ?_
  rintro z -
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq (W' := C₁.toAffine) z
  rw [Algebra.smul_def p (1 : C₁.CoordinateRing),
    Algebra.smul_def q (CoordinateRing.mk C₁.toAffine Y)]
  refine Submodule.add_mem _ ?_ ?_
  · refine Submodule.mul_mem_mul ?_ ?_
    · exact hadj p
    · exact Submodule.subset_span (Set.mem_insert _ _)
  · refine Submodule.mul_mem_mul ?_ ?_
    · exact hadj q
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)

namespace CurveMap.CoordHom

variable {C₁ C₂ : SmoothPlaneCurve F} {φ : CurveMap C₁ C₂}

/-- A coordinate-ring witness is automatically **injective**: its
`compat` square exhibits `algebraMap ∘ cd.toAlgHom` as the injective
composite `φ.pullback ∘ algebraMap`. -/
theorem toAlgHom_injective (cd : φ.CoordHom) : Function.Injective cd.toAlgHom := by
  intro a b hab
  have h : φ.pullback (algebraMap C₂.CoordinateRing C₂.FunctionField a) =
      φ.pullback (algebraMap C₂.CoordinateRing C₂.FunctionField b) := by
    rw [cd.compat a, cd.compat b, hab]
  exact IsFractionRing.injective C₂.CoordinateRing C₂.FunctionField
    (φ.pullback_injective h)

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Instance synthesis and unification at curve-indexed coordinate-ring types
-- (`AdjoinRoot`-quotients) need a higher budget; same settings as
-- `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`.
/-- **The standing `Module.Finite` hypothesis of the isogeny theory,
DERIVED** (closing the last repo-wide carried hypothesis): for any curve map
`φ : C₁ → C₂` with coordinate-ring witness `cd`, the coordinate ring
`F[C₁]` is a finite `F[C₂]`-module via `cd.toAlgebra`.

Unconditional: no separability, no integral closedness, and no algebraically
closed base are required.  This discharges the `hfin` arguments of
`CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`,
`EC.Isogeny.addHomProperty`, `EC.Isogeny.toBasicIsogeny`,
`EC.Isogeny.addHomProperty_descend_of_finite`, `Isogeny.pushforward`, and
the `KernelCount` chain. -/
theorem module_finite (cd : φ.CoordHom) :
    @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _ cd.toAlgebra.toModule :=
  algHom_coordinateRing_module_finite cd.toAlgHom cd.toAlgHom_injective

end CurveMap.CoordHom

namespace CurveMap

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
-- Instance synthesis and unification at curve-indexed coordinate-ring types
-- (`AdjoinRoot`-quotients) need a higher budget; same settings as
-- `CurveMap.sum_ramificationIdx_mul_inertiaDeg_eq_degree`.
/-- **Silverman II.2.6(a), Σ e·f form, `hfin`-free** (T-II-2-008): for a
`CurveMap φ : C₁ → C₂` with coordinate-ring pullback witness `coordHom`, the
sum `Σ_{P over p} e_P · f_P` equals the function-field degree `φ.degree`.
The module-finiteness input of
`sum_ramificationIdx_mul_inertiaDeg_eq_degree` is supplied by
`CoordHom.module_finite`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_eq_degree'
    {C₁ C₂ : SmoothPlaneCurve F}
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    {p : Ideal C₂.CoordinateRing} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ∑ P ∈ primesOverFinset p C₁.CoordinateRing,
        Ideal.ramificationIdx p P *
        Ideal.inertiaDeg p P = φ.degree :=
  φ.sum_ramificationIdx_mul_inertiaDeg_eq_degree coordHom
    coordHom.module_finite hpMax hp0

end CurveMap

end HasseWeil.Curves
