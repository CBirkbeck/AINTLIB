/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.Extension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic

import HasseWeil.EC.GenericPointZsmul
import HasseWeil.EC.SeparableKernelTorsor

/-!
# Kernel-rationality of `[ℓ]` over `K̄` (Silverman III.4.10c)

For the multiplication-by-`ℓ` isogeny `[ℓ] = mulByInt W.toAffine ℓ` over an algebraically closed
field `F = K̄`, we discharge the two genuine-isogeny coherence inputs of the capstone
`HasseWeil.card_kernel_eq_degree_of_separable_concrete` (`SeparableKernelTorsor.lean`):

* `hdesc_mulByInt` — the inverse-witness descent: every fibre `σ(P_gen) − P_gen` (`σ` an
  automorphism of `K(E)/[ℓ]*K(E)`) is an `F`-rational kernel point of `[ℓ]`.
* `h_normal_mulByInt` — the function-field extension `K(E)/[ℓ]*K(E)` is normal.

Both rest on **kernel-rationality** (`kernelDescends_general`, specialised to
`kernelOverKE_descends` at `L = K(E)`): over `K̄`, every point `Q` of `E` with coordinates in a
field extension `L` that is killed by `[ℓ]` already descends to a `K̄`-rational `ℓ`-torsion point.
The reason is the division-polynomial connection `[ℓ]Q = O ⟹ ψ_ℓ(x(Q), y(Q)) = 0 ⟹ Ψ²_ℓ(x(Q)) = 0`:
the `x`-coordinate of `Q` is a root of the `ℓ`-division polynomial `Ψ²_ℓ`, whose coefficients lie
in `K̄` (not just `L`); since `K̄` is algebraically closed, `Ψ²_ℓ` splits over `K̄`, so `x(Q)` is
the image of a `K̄`-element. The `y`-coordinate then descends via the Weierstrass equation over `K̄`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.4.10c.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **Jacobian division-polynomial coordinates of `[m]`** for an *arbitrary* elliptic curve `V`
over a field `L` (the curve-general form of `zsmul_affine_point_eq`): for a nonsingular point
`(x₀, y₀)` with `ψ_m(x₀, y₀) ≠ 0`, `m • (x₀, y₀) = (φ_m/ψ_m², ω_m/ψ_m³)`. Same Jacobian↔affine
proof as the `W_KE`-specific version. Used by `kernelDescends_general` at
`V = W.map (algebraMap F L)`. -/
theorem zsmul_affine_point_eq_gen {L : Type*} [Field L] [DecidableEq L] (V : WeierstrassCurve L)
    [V.toAffine.IsElliptic] (m : ℤ) {x₀ y₀ : L}
    (h_ns : V.toAffine.Nonsingular x₀ y₀)
    (h_ψ_ne : (V.ψ m).evalEval x₀ y₀ ≠ 0) :
    ∃ h_ns' : V.toAffine.Nonsingular
        ((V.φ m).evalEval x₀ y₀ / (V.ψ m).evalEval x₀ y₀ ^ 2)
        ((V.ω m).evalEval x₀ y₀ / (V.ψ m).evalEval x₀ y₀ ^ 3),
      m • Affine.Point.some x₀ y₀ h_ns =
        Affine.Point.some _ _ h_ns' := by
  have h_smulEval := WeierstrassCurve.zsmul_eq_smulEval (W := V) h_ns m
  have hZ : smulEval V x₀ y₀ m 2 ≠ 0 := h_ψ_ne
  have h_ns_smulEval :
      WeierstrassCurve.Jacobian.Nonsingular V.toJacobian
        (smulEval V x₀ y₀ m) := by
    have h_ns_jac := (m • WeierstrassCurve.Jacobian.Point.fromAffine
      (Affine.Point.some x₀ y₀ h_ns)).nonsingular
    change WeierstrassCurve.Jacobian.NonsingularLift _ _ at h_ns_jac
    rwa [h_smulEval] at h_ns_jac
  have h_ns_affine :
      V.toAffine.Nonsingular
        (smulEval V x₀ y₀ m 0 / smulEval V x₀ y₀ m 2 ^ 2)
        (smulEval V x₀ y₀ m 1 / smulEval V x₀ y₀ m 2 ^ 3) :=
    (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero hZ).mp h_ns_smulEval
  refine ⟨h_ns_affine, ?_⟩
  have h_inv :
      WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V
        (WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
      Affine.Point.some x₀ y₀ h_ns :=
    (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V).right_inv _
  have h_toAffine :
      m • Affine.Point.some x₀ y₀ h_ns =
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) := by
    have h := map_zsmul (WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V)
      m (WeierstrassCurve.Jacobian.Point.fromAffine
        (Affine.Point.some x₀ y₀ h_ns))
    rw [WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply] at h
    rw [show WeierstrassCurve.Jacobian.Point.toAffineAddEquiv V
      (WeierstrassCurve.Jacobian.Point.fromAffine _) =
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (WeierstrassCurve.Jacobian.Point.fromAffine _) from rfl] at h
    have h2 : WeierstrassCurve.Jacobian.Point.toAffineLift
        (WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
        Affine.Point.some x₀ y₀ h_ns := by
      rw [← WeierstrassCurve.Jacobian.Point.toAffineAddEquiv_apply]
      exact h_inv
    rw [h2] at h
    exact h.symm
  rw [h_toAffine]
  have h_eq_lift :
      WeierstrassCurve.Jacobian.Point.toAffineLift
        (m • WeierstrassCurve.Jacobian.Point.fromAffine
          (Affine.Point.some x₀ y₀ h_ns)) =
      WeierstrassCurve.Jacobian.Point.toAffine V
        (smulEval V x₀ y₀ m) := by
    show _ = WeierstrassCurve.Jacobian.Point.toAffine V _
    unfold WeierstrassCurve.Jacobian.Point.toAffineLift
    rw [h_smulEval]
    rfl
  rw [h_eq_lift, WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero h_ns_smulEval hZ]
  rfl

/-- The `y`-coordinate descent of `kernelDescends_general`: over an algebraically closed `F`, if the
`x`-coordinate of a Weierstrass point already descends (`xv = algebraMap F L x₀`) and the equation
holds at `(xv, yv)`, then `yv = algebraMap F L y₀` for some `y₀ : F`. The `y`-coordinate is a root of
the monic Weierstrass quadratic specialised at `x₀`, which splits over the algebraically closed `F`. -/
private theorem yCoord_descends_of_equation {F : Type*} [Field F] [IsAlgClosed F]
    (W : WeierstrassCurve F) {L : Type*} [Field L] [Algebra F L] (x₀ : F) (yv : L)
    (heqn : (W.map (algebraMap F L)).toAffine.Equation (algebraMap F L x₀) yv) :
    ∃ y₀ : F, yv = algebraMap F L y₀ := by
  set c1 := W.a₁ * x₀ + W.a₃ with hc1
  set c0 := x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆ with hc0
  set q : F[X] := Polynomial.X ^ 2 + (C c1 * Polynomial.X - C c0) with hq
  have hq_natDeg : (C c1 * Polynomial.X - C c0 : F[X]).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by
        simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
    · simp [Polynomial.natDegree_C]
  have hq_monic : q.Monic := by
    rw [hq]
    exact monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast Nat.lt_succ_of_le hq_natDeg))
  have hYroot : (q.map (algebraMap F L)).IsRoot yv := by
    rw [Affine.equation_iff] at heqn
    simp only [IsRoot.def, hq, eval_map, eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_mul,
      eval₂_C, eval₂_X]
    rw [show (W.map (algebraMap F L)).a₁ = algebraMap F L W.a₁ from rfl,
      show (W.map (algebraMap F L)).a₂ = algebraMap F L W.a₂ from rfl,
      show (W.map (algebraMap F L)).a₃ = algebraMap F L W.a₃ from rfl,
      show (W.map (algebraMap F L)).a₄ = algebraMap F L W.a₄ from rfl,
      show (W.map (algebraMap F L)).a₆ = algebraMap F L W.a₆ from rfl] at heqn
    rw [hc1, hc0]
    push_cast [map_add, map_mul, map_pow]
    linear_combination heqn
  obtain ⟨y₀, hy₀⟩ := (IsAlgClosed.splits q).mem_range_of_isRoot
    hq_monic.ne_zero (i := algebraMap F L) (x := yv) hYroot
  exact ⟨y₀, hy₀.symm⟩

/-- **Kernel-rationality over a general extension** (Silverman III.4.10c, the engine): over `K̄`,
every point `Q` of `W` with coordinates in an extension `L` that is killed by `[ℓ]` descends to a
`K̄`-rational `ℓ`-torsion point `k : E(K̄)` with `Point.map (Algebra.ofId F L) k = Q`.

Proof by cases on `Q`. The zero point descends to `k = 0`. For `Q = (X, Y)`: from `ℓ • Q = 0` the
Jacobian `Z`-coordinate `ψ_ℓ(X, Y)` of `[ℓ]Q` vanishes (contrapositive of
`zsmul_affine_point_eq_gen`, which would otherwise produce a nonzero `.some` point), hence
`Ψ²_ℓ(X) = ψ_ℓ(X, Y)² = 0` (`evalEval_ψ_sq`). Now `Ψ²_{W_L,ℓ} = (Ψ²_{W,ℓ}).map (algebraMap F L)`
(`map_ΨSq`) is the image of a polynomial **over `F = K̄`**; since `K̄` is algebraically closed
`Ψ²_{W,ℓ}` splits over `K̄`, so by `Splits.mem_range_of_isRoot` the root `X` is `algebraMap F L x₀`.
The `y`-coordinate `Y` descends by `yCoord_descends_of_equation`. The pair `(x₀, y₀)` is nonsingular
on `W` (`baseChange_nonsingular`), giving the curve point `k = some x₀ y₀` with `Point.map k = Q` and
`ℓ • k = 0` (the latter by `Point.map` injectivity). -/
theorem kernelDescends_general {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    [W.toAffine.IsElliptic] [IsAlgClosed F] {L : Type*} [Field L] [DecidableEq L]
    [Algebra F L] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (Q : (W.map (algebraMap F L)).toAffine.Point)
    (hQ : (ℓ : ℤ) • Q = 0) :
    ∃ k : W.toAffine.Point, ℓ • k = 0 ∧
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L) k = Q := by
  rcases Q with _ | ⟨xv, yv, hns⟩
  · exact ⟨0, zsmul_zero ℓ, WeierstrassCurve.Affine.Point.map_zero (Algebra.ofId F L)⟩
  · have hψ : ((W.map (algebraMap F L)).ψ ℓ).evalEval xv yv = 0 := by
      by_contra hψ
      obtain ⟨h', heq⟩ := zsmul_affine_point_eq_gen (W.map (algebraMap F L)) ℓ hns hψ
      exact (Affine.Point.some_ne_zero h') (heq.symm.trans hQ)
    have heqn : (W.map (algebraMap F L)).toAffine.Equation xv yv :=
      Affine.equation_iff_nonsingular.mpr hns
    have hΨ : ((W.map (algebraMap F L)).ΨSq ℓ).eval xv = 0 := by
      have hsq := WeierstrassCurve.evalEval_ψ_sq (W := W.map (algebraMap F L)) heqn ℓ
      rw [hψ] at hsq; simpa using hsq.symm
    obtain ⟨x₀, hX⟩ : ∃ x₀ : F, xv = algebraMap F L x₀ := by
      rw [show (W.map (algebraMap F L)).ΨSq ℓ = (W.ΨSq ℓ).map (algebraMap F L) from
        WeierstrassCurve.map_ΨSq (W := W) (algebraMap F L) ℓ] at hΨ
      obtain ⟨x₀, hx₀⟩ := (IsAlgClosed.splits (W.ΨSq ℓ)).mem_range_of_isRoot
        (ΨSq_poly_ne_zero W hℓ) (i := algebraMap F L) (x := xv) hΨ
      exact ⟨x₀, hx₀.symm⟩
    obtain ⟨y₀, hY⟩ := yCoord_descends_of_equation W x₀ yv (hX ▸ heqn)
    have hns₀ : W.toAffine.Nonsingular x₀ y₀ := by
      have h := (WeierstrassCurve.Affine.baseChange_nonsingular (W := W) (A := F)
        (B := L) (f := Algebra.ofId F L)
        (Algebra.ofId F L).injective x₀ y₀).mp
      simp only [Algebra.ofId_apply] at h
      rw [hX, hY] at hns
      exact h hns
    have hlk : WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L)
        (Affine.Point.some x₀ y₀ hns₀) = Affine.Point.some xv yv hns := by
      subst hX hY
      rw [WeierstrassCurve.Affine.Point.map_some]
      simp only [Algebra.ofId_apply]
      rfl
    refine ⟨Affine.Point.some x₀ y₀ hns₀, ?_, hlk⟩
    have hlift_inj : Function.Injective
        (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L)) :=
      WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId F L)
    apply hlift_inj
    have hzs : (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L))
        (ℓ • Affine.Point.some x₀ y₀ hns₀) =
        ℓ • (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F L))
          (Affine.Point.some x₀ y₀ hns₀) :=
      map_zsmul _ ℓ _
    rw [hzs, hlk]
    exact hQ.trans (WeierstrassCurve.Affine.Point.map_zero (Algebra.ofId F L)).symm

/-- **Kernel-rationality of `[ℓ]` over `K̄`** (Silverman III.4.10c): the `L = K(E)` specialisation
of `kernelDescends_general`. Every point `Q : (W_KE W).toAffine.Point` (coordinates in the function
field `K(E)`) killed by `[ℓ]` descends to a `K̄`-rational `ℓ`-torsion point `k` with
`liftPointToKE W k = Q`. Here `W_KE W = W.map (algebraMap F K(E))` and
`liftPointToKE W = Point.map (Algebra.ofId F K(E))` definitionally, so this is
`kernelDescends_general` applied verbatim. -/
theorem kernelOverKE_descends [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (Q : (W_KE W).toAffine.Point)
    (hQ : (ℓ : ℤ) • Q = 0) :
    ∃ k : W.toAffine.Point, ℓ • k = 0 ∧ liftPointToKE W k = Q :=
  kernelDescends_general W ℓ hℓ Q hQ

/-- **`hdesc` for `[ℓ]` over `K̄`** (Silverman III.4.10c). Discharges the `hdesc` hypothesis of
`card_kernel_eq_degree_of_separable_concrete` at `φ = mulByInt W.toAffine ℓ`: for every
automorphism `σ` of `K(E)/[ℓ]*K(E)`, the fibre `σ(P_gen) − P_gen` is an `F`-rational kernel point
of `[ℓ]`.

The geometric action `g` of `[ℓ]` on `(W_KE).Point` is multiplication-by-`ℓ` (`zsmulAddGroupHom ℓ`),
whose value at the generic point is `(mulByInt_x ℓ, mulByInt_y ℓ) = ([ℓ]*x_gen, [ℓ]*y_gen)`
(`zsmul_genericPoint_eq` + `mulByInt_pullback_x/y`); this is the genuine data. The shipped
`genericPointAct_mem_ker_g` then yields `g(σ P_gen) = g(P_gen)` — using `σ.commutes` (it fixes the
pullback range) and the equivariance `g ∘ (Point.map σ) = (Point.map σ) ∘ g`, which here is just
`map_zsmul`. Thus `ℓ • (σ P_gen − P_gen) = 0`, and `kernelOverKE_descends` produces the descended
`F`-rational kernel point. -/
theorem hdesc_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    ∀ σ : (@AlgEquiv W.toAffine.FunctionField W.toAffine.FunctionField
        W.toAffine.FunctionField _ _ _
        (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra),
      ∃ k : W.toAffine.Point, k ∈ (mulByInt W.toAffine ℓ).kernel ∧
        liftPointToKE W k =
          genericPointAct W (mulByInt W.toAffine ℓ) σ - genericPoint W := by
  intro σ
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  set g : (W_KE W).toAffine.Point →+ (W_KE W).toAffine.Point := zsmulAddGroupHom ℓ with hg
  obtain ⟨hns, hsmul⟩ := zsmul_genericPoint_eq W ℓ hℓ
  have hsmul' : ℓ • genericPoint W =
      Affine.Point.some (mulByInt_x W ℓ) (mulByInt_y W ℓ) hns :=
    Subsingleton.elim (instDecidableEqFunctionField W) FractionRing.instDecidableEq ▸ hsmul
  have hgP : g (genericPoint W) =
      Affine.Point.some (mulByInt_x W ℓ) (mulByInt_y W ℓ) hns := by
    rw [hg]; change ℓ • genericPoint W = _; exact hsmul'
  have hX : mulByInt_x W ℓ = (mulByInt W.toAffine ℓ).pullback (x_gen W) :=
    (mulByInt_pullback_x W ℓ hℓ).symm
  have hY : mulByInt_y W ℓ = (mulByInt W.toAffine ℓ).pullback (y_gen W) :=
    (mulByInt_pullback_y W ℓ hℓ).symm
  -- σ-equivariance of `g = ℓ • ·` is just `map_zsmul` for `Point.map σ`.
  have hequiv : g (genericPointAct W (mulByInt W.toAffine ℓ) σ) =
      WeierstrassCurve.Affine.Point.map (W' := W) (σ.toAlgHom.restrictScalars F)
        (g (genericPoint W)) := by
    unfold genericPointAct
    rw [hg]
    change ℓ • _ = WeierstrassCurve.Affine.Point.map (W' := W)
      (σ.toAlgHom.restrictScalars F) (ℓ • _)
    exact (map_zsmul (WeierstrassCurve.Affine.Point.map (W' := W)
      (σ.toAlgHom.restrictScalars F)) ℓ (genericPoint W)).symm
  have hmem := genericPointAct_mem_ker_g W (mulByInt W.toAffine ℓ) g
    (mulByInt_x W ℓ) (mulByInt_y W ℓ) hns hgP hX hY σ hequiv
  have hker : (ℓ : ℤ) • (genericPointAct W (mulByInt W.toAffine ℓ) σ - genericPoint W) = 0 := by
    have hsmul_eq : ℓ • genericPointAct W (mulByInt W.toAffine ℓ) σ = ℓ • genericPoint W := by
      have h1 : g (genericPointAct W (mulByInt W.toAffine ℓ) σ) =
          ℓ • genericPointAct W (mulByInt W.toAffine ℓ) σ := rfl
      have h2 : g (genericPoint W) = ℓ • genericPoint W := rfl
      rw [← h1, ← h2]; exact hmem
    rw [zsmul_sub, hsmul_eq, sub_self]
  obtain ⟨k, hk0, hklift⟩ := kernelOverKE_descends W ℓ hℓ _ hker
  refine ⟨k, ?_, hklift⟩
  rw [Isogeny.mem_kernel_iff, mulByInt_apply]
  exact hk0

omit [W.toAffine.IsElliptic] [DecidableEq F] in
private theorem algebraMapPoly_mem_adjoin_x_gen (p : F[X]) :
    algebraMap F[X] W.toAffine.FunctionField p ∈
      IntermediateField.adjoin F ({x_gen W} : Set W.toAffine.FunctionField) := by
  have hx : x_gen W = algebraMap F[X] W.toAffine.FunctionField Polynomial.X := by
    rw [x_gen, ← IsScalarTower.algebraMap_apply]
  have he : algebraMap F[X] W.toAffine.FunctionField p = Polynomial.aeval (x_gen W) p := by
    rw [hx]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a =>
      rw [Polynomial.aeval_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        show (C a : F[X]) = algebraMap F F[X] a from rfl, ← IsScalarTower.algebraMap_apply]
  rw [he]
  exact IntermediateField.algebra_adjoin_le_adjoin F _ (Polynomial.aeval_mem_adjoin_singleton _ _)

omit [W.toAffine.IsElliptic] [DecidableEq F] in
/-- **`K(E)` is generated over `F` by `x_gen` and `y_gen`** (the affine coordinates of the generic
point). Every `z : K(E)` is a ratio `algebraMap R z₁ / algebraMap R z₂` of images of coordinate-ring
elements (`IsFractionRing.div_surjective`), and each `algebraMap R r` lies in `F⟮x_gen, y_gen⟯`: by
the rank-2 basis `{1, mk Y}` of `R` over `F[X]` (`exists_smul_basis_eq`), `r = p • 1 + q • mk Y`, so
`algebraMap R r = (algebraMap F[X] p) + (algebraMap F[X] q) · y_gen`, with the `F[X]`-images in
`F⟮x_gen⟯` (`algebraMapPoly_mem_adjoin_x_gen`) and `y_gen` a generator. Closure under `+`, `·`, `/`
finishes. -/
theorem adjoin_x_gen_y_gen_eq_top :
    IntermediateField.adjoin F ({x_gen W, y_gen W} : Set W.toAffine.FunctionField) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  set S := IntermediateField.adjoin F ({x_gen W, y_gen W} : Set W.toAffine.FunctionField)
  have hxS : x_gen W ∈ S := IntermediateField.subset_adjoin _ _ (by left; rfl)
  have hyS : y_gen W ∈ S := IntermediateField.subset_adjoin _ _ (by right; rfl)
  have hadjx : IntermediateField.adjoin F ({x_gen W} : Set W.toAffine.FunctionField) ≤ S := by
    rw [IntermediateField.adjoin_le_iff]
    intro w hw; rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hxS
  have hpolyS : ∀ p : F[X], algebraMap F[X] W.toAffine.FunctionField p ∈ S :=
    fun p => hadjx (algebraMapPoly_mem_adjoin_x_gen W p)
  have hRmem : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ S := by
    intro r
    obtain ⟨p, q, hpq⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
    rw [← hpq, map_add]
    refine S.add_mem ?_ ?_
    · rw [Algebra.smul_def, mul_one]
      change algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap F[X] W.toAffine.CoordinateRing p) ∈ S
      rw [← IsScalarTower.algebraMap_apply]; exact hpolyS p
    · rw [Algebra.smul_def, map_mul]
      refine S.mul_mem ?_ ?_
      · change algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
            (algebraMap F[X] W.toAffine.CoordinateRing q) ∈ S
        rw [← IsScalarTower.algebraMap_apply]; exact hpolyS q
      · rw [show Affine.CoordinateRing.mk W.toAffine Polynomial.X =
          AdjoinRoot.root W.toAffine.polynomial from rfl]
        exact hyS
  obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  rw [← hrs]
  exact S.div_mem (hRmem r) (hRmem s)

/-- **The geometric heart** (Silverman III.4.10c): an `F`-embedding `g : K(E) → Ω` that agrees
with a reference embedding `ι` on the pullback range `[ℓ]*K(E)` sends the generic-point coordinates
`x_gen, y_gen` into the range of `ι`. Reason: `g` and `ι` give two points `g(P_gen), ι(P_gen)` of
`E(Ω)` with the same `[ℓ]`-image (`σ` fixes `[ℓ]*x_gen, [ℓ]*y_gen`), so their difference is an
`[ℓ]`-kernel point of `E(Ω)`, which by `kernelDescends_general` is `F`-rational; hence
`g(P_gen) = ι(P_gen + lift k)` and reading off coordinates gives `g x_gen, g y_gen ∈ range ι`. -/
theorem sigma_genCoord_mem_range_proto [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {Ω : Type*} [Field Ω] [Algebra F Ω]
    (ι : W.toAffine.FunctionField →ₐ[F] Ω)
    (g : W.toAffine.FunctionField →ₐ[F] Ω)
    (hfix : ∀ z : W.toAffine.FunctionField,
      g ((mulByInt W.toAffine ℓ).pullback z) = ι ((mulByInt W.toAffine ℓ).pullback z)) :
    g (x_gen W) ∈ Set.range ι ∧ g (y_gen W) ∈ Set.range ι := by
  classical
  set gP := WeierstrassCurve.Affine.Point.map (W' := W.toAffine) g (genericPoint W) with hgP_def
  set ιP := WeierstrassCurve.Affine.Point.map (W' := W.toAffine) ι (genericPoint W) with hιP_def
  obtain ⟨hns_mul, hsmul⟩ := zsmul_genericPoint_eq W ℓ hℓ
  rw [show (FractionRing.instDecidableEq :
        DecidableEq W.toAffine.FunctionField) = instDecidableEqFunctionField W from
    Subsingleton.elim _ _] at hsmul
  have hgx : g (mulByInt_x W ℓ) = ι (mulByInt_x W ℓ) := by
    rw [(mulByInt_pullback_x W ℓ hℓ).symm]; exact hfix _
  have hgy : g (mulByInt_y W ℓ) = ι (mulByInt_y W ℓ) := by
    rw [(mulByInt_pullback_y W ℓ hℓ).symm]; exact hfix _
  -- `ℓ • (map φ P_gen) = map φ (some (mulByInt_x) (mulByInt_y))` for either embedding `φ`.
  have hsc : ∀ φ : W.toAffine.FunctionField →ₐ[F] Ω,
      (ℓ : ℤ) • WeierstrassCurve.Affine.Point.map (W' := W.toAffine) φ (genericPoint W) =
        WeierstrassCurve.Affine.Point.map (W' := W.toAffine) φ
          (Affine.Point.some (mulByInt_x W ℓ) (mulByInt_y W ℓ) hns_mul) := fun φ =>
    (map_zsmul (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) φ) ℓ
      (genericPoint W)).symm.trans (congrArg _ hsmul)
  have hkey : (ℓ : ℤ) • gP = (ℓ : ℤ) • ιP := by
    rw [hgP_def, hιP_def, hsc g, hsc ι, WeierstrassCurve.Affine.Point.map_some,
      WeierstrassCurve.Affine.Point.map_some, Affine.Point.some.injEq]
    exact ⟨hgx, hgy⟩
  have hker : (ℓ : ℤ) • (gP - ιP) = 0 := by rw [zsmul_sub, hkey, sub_self]
  obtain ⟨k, _, hklift⟩ := kernelDescends_general W ℓ hℓ (gP - ιP) hker
  have hcomp : WeierstrassCurve.Affine.Point.map (W' := W.toAffine) (Algebra.ofId F Ω) k =
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine) ι (liftPointToKE W k) := by
    change _ = WeierstrassCurve.Affine.Point.map (W' := W.toAffine) ι
      (WeierstrassCurve.Affine.Point.map (W' := W.toAffine)
        (Algebra.ofId F (W.toAffine.FunctionField)) k)
    rw [WeierstrassCurve.Affine.Point.map_map (W' := W.toAffine)
      (f := Algebra.ofId F (W.toAffine.FunctionField)) (g := ι),
      Algebra.comp_ofId]
  have hgP_eq : gP =
      WeierstrassCurve.Affine.Point.map (W' := W.toAffine) ι
        (genericPoint W + liftPointToKE W k) := by
    have hsplit : gP = ιP + (gP - ιP) := by abel
    rw [hsplit, ← hklift, hcomp, hιP_def]
    exact (map_add (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) ι)
      (genericPoint W) (liftPointToKE W k)).symm
  have hgP_some : gP = Affine.Point.some (g (x_gen W)) (g (y_gen W))
      ((W.toAffine.baseChange_nonsingular g.injective (x_gen W) (y_gen W)).mpr
        (generic_nonsingular W)) := by
    rw [hgP_def, genericPoint_xOf_some]
    exact WeierstrassCurve.Affine.Point.map_some (f := g) (generic_nonsingular W)
  rcases h_sum : (genericPoint W + liftPointToKE W k) with _ | ⟨x', y', hns'⟩
  · -- impossible: `gP = map ι 0 = 0`, yet `gP = some (g x_gen) (g y_gen)`.
    exfalso
    rw [hgP_some, h_sum] at hgP_eq
    exact Affine.Point.some_ne_zero _ hgP_eq
  · rw [hgP_some, h_sum] at hgP_eq
    have hgP_eq2 : Affine.Point.some (g (x_gen W)) (g (y_gen W))
        ((W.toAffine.baseChange_nonsingular g.injective (x_gen W) (y_gen W)).mpr
          (generic_nonsingular W)) =
        Affine.Point.some (ι x') (ι y')
          ((W.toAffine.baseChange_nonsingular ι.injective x' y').mpr hns') :=
      hgP_eq.trans (WeierstrassCurve.Affine.Point.map_some (f := ι) hns')
    rw [Affine.Point.some.injEq] at hgP_eq2
    exact ⟨⟨x', hgP_eq2.1.symm⟩, ⟨y', hgP_eq2.2.symm⟩⟩

/-- A root in an algebraically closed extension of the minimal polynomial of `a` (over a base
field `Kb`) is the image of `a` under some `Kb`-algebra hom into that extension. Repackages
`Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly` in `aeval` form, with all-distinct type
variables (so it instantiates cleanly at `Kb = K(E)`-with-pullback, `K = K(E)`-standard). -/
theorem root_minpoly_in_range_eval {Kb K A : Type*} [Field Kb] [Field K] [Field A]
    [Algebra Kb K] [Algebra Kb A] [IsAlgClosed A] [Algebra.IsAlgebraic Kb K]
    (a : K) (t : A)
    (ht : Polynomial.eval₂ (algebraMap Kb A) t (minpoly Kb a) = 0) :
    t ∈ Set.range (fun ψ : K →ₐ[Kb] A ↦ ψ a) := by
  rw [Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly A a,
    mem_rootSet_of_ne (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)), Polynomial.aeval_def]
  exact ht

/-- **Splitting from algHom-image control** (distinct type variables, no same-type instance
shadowing). For a base field `Kb`, an extension `K`, and an algebraically closed extension `A` of
`K` via `jb : K →+* A`, with `A` a `Kb`-algebra compatibly (`hcompat`): if every `Kb`-algebra hom
image `ψ a` (`ψ : K →ₐ[Kb] A`) lands in `range jb`, then `minpoly Kb a` splits over `K`. -/
theorem minpoly_splits_of_algHom_image_mem {Kb K A : Type*} [Field Kb] [Field K] [Field A]
    [Algebra Kb K] [Algebra Kb A] [IsAlgClosed A] [Algebra.IsAlgebraic Kb K]
    (a : K) (jb : K →+* A) (hjb : Function.Injective jb)
    (hcompat : (algebraMap Kb A) = jb.comp (algebraMap Kb K))
    (hmem : ∀ ψ : K →ₐ[Kb] A, ψ a ∈ jb.range) :
    Polynomial.Splits ((minpoly Kb a).map (algebraMap Kb K)) := by
  refine Splits.of_splits_map_of_injective (i := jb) hjb (IsAlgClosed.splits _) ?_
  intro t ht
  rw [Polynomial.map_map, ← hcompat] at ht
  rw [mem_roots (map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a)))] at ht
  rw [IsRoot.def, eval_map] at ht
  obtain ⟨ψ, hψ⟩ := root_minpoly_in_range_eval a t ht
  rw [← hψ]
  exact hmem ψ

/-- Single-coordinate splitting: if every `B`-algHom image of `a ∈ {x_gen, y_gen}` into the
algebraic closure `Ω` of `K(E)` lies in the canonical embedding's range, the minpoly of `a` over
`B` splits in `K(E)`. (`Ω` is fixed to `AlgebraicClosure K(E)` to avoid universe polymorphism.) -/
theorem minpoly_gen_splits_of_mem_range [IsAlgClosed F] (ℓ : ℤ) (_hℓ : ℓ ≠ 0)
    (a : W.toAffine.FunctionField)
    (hmem : ∀ (g : W.toAffine.FunctionField →ₐ[F] AlgebraicClosure W.toAffine.FunctionField),
      (∀ z : W.toAffine.FunctionField, g ((mulByInt W.toAffine ℓ).pullback z) =
        algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)
          ((mulByInt W.toAffine ℓ).pullback z)) →
      g a ∈ (algebraMap W.toAffine.FunctionField
        (AlgebraicClosure W.toAffine.FunctionField)).range) :
    letI := (mulByInt W.toAffine ℓ).toAlgebra
    Polynomial.Splits ((minpoly W.toAffine.FunctionField a).map
      (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField)) := by
  letI algB := (mulByInt W.toAffine ℓ).toAlgebra
  -- Re-pin the canonical `Algebra K(E) Ω` to use `Algebra.id` for the `[Algebra K(E) K(E)]` slot
  -- of `AlgebraicClosure.instAlgebra` (otherwise the ambient `letI := pullback` poisons it, making
  -- the proof's `algebraMap K(E) Ω` disagree with the one baked into `hmem`).
  letI stdΩ : Algebra W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField) :=
    @AlgebraicClosure.instAlgebra W.toAffine.FunctionField _ W.toAffine.FunctionField _
      (Algebra.id W.toAffine.FunctionField)
  haveI hfin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ algB.toModule := isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)
  haveI halg : Algebra.IsAlgebraic W.toAffine.FunctionField W.toAffine.FunctionField :=
    Algebra.IsAlgebraic.of_finite _ _
  -- `Ω = AlgebraicClosure K(E)` is made a *base*-algebra via the ring hom `algebraMap ∘ pullback`,
  -- supplied *inline* to the abstract criterion (never a scope instance, so the standard
  -- `Algebra K(E) Ω` — hence the canonical embedding `algebraMap K(E) Ω` — stays unambiguous).
  refine @minpoly_splits_of_algHom_image_mem W.toAffine.FunctionField W.toAffine.FunctionField
    (AlgebraicClosure W.toAffine.FunctionField)
    _ _ _ algB (((algebraMap W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField)).comp
        (mulByInt W.toAffine ℓ).pullback.toRingHom).toAlgebra) _ halg a
    (algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField))
    (RingHom.injective _) rfl ?_
  intro ψ
  have hψfix : ∀ z : W.toAffine.FunctionField,
      ψ ((mulByInt W.toAffine ℓ).pullback z) =
        algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)
          ((mulByInt W.toAffine ℓ).pullback z) := by
    intro z
    have hc := @AlgHom.commutes W.toAffine.FunctionField W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField) _ _ _ algB
      (((algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)).comp
        (mulByInt W.toAffine ℓ).pullback.toRingHom).toAlgebra) ψ z
    rw [show @algebraMap W.toAffine.FunctionField W.toAffine.FunctionField _ _ algB z =
      (mulByInt W.toAffine ℓ).pullback z from rfl] at hc
    rw [hc, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    rfl
  -- Build the `F`-algHom `g` by restricting scalars along `F → B`, using the inline scalar tower
  -- `F → B → Ω` (`of_algHom` for `(algebraMap) ∘ pullback`); supplied `@`-explicitly.
  haveI htower : @IsScalarTower F W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField) _
      (((algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)).comp
        (mulByInt W.toAffine ℓ).pullback.toRingHom).toAlgebra).toSMul _ :=
    IsScalarTower.of_algHom ((IsScalarTower.toAlgHom F W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField)).comp (mulByInt W.toAffine ℓ).pullback)
  let g : W.toAffine.FunctionField →ₐ[F] AlgebraicClosure W.toAffine.FunctionField :=
    @AlgHom.restrictScalars F W.toAffine.FunctionField W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField) _ _ _ _ _ algB
      (((algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)).comp
        (mulByInt W.toAffine ℓ).pullback.toRingHom).toAlgebra) _ _ _ htower ψ
  have hgψ : ∀ z, g z = ψ z := fun z =>
    @AlgHom.restrictScalars_apply F W.toAffine.FunctionField W.toAffine.FunctionField
      (AlgebraicClosure W.toAffine.FunctionField) _ _ _ _ _ algB
      (((algebraMap W.toAffine.FunctionField (AlgebraicClosure W.toAffine.FunctionField)).comp
        (mulByInt W.toAffine ℓ).pullback.toRingHom).toAlgebra) _ _ _ htower ψ z
  obtain ⟨b, hb⟩ := hmem g (fun z => (hgψ _).trans (hψfix z))
  exact ⟨b, hb.trans (hgψ a)⟩

/-- **The deep residual** (Silverman III.4.10c): the minimal polynomials over `[ℓ]*K(E)` of the
two generic-point coordinates split in `K(E)`. Combines the geometric claim
(`sigma_genCoord_mem_range_proto`: each `[ℓ]*K(E)`-fixing `F`-embedding sends `x_gen`/`y_gen` into
the canonical-embedding range) with the abstract splitting criterion
(`minpoly_gen_splits_of_mem_range`). -/
theorem mulByInt_genCoords_minpoly_splits [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    letI := (mulByInt W.toAffine ℓ).toAlgebra
    Polynomial.Splits ((minpoly W.toAffine.FunctionField (x_gen W)).map
        (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField)) ∧
    Polynomial.Splits ((minpoly W.toAffine.FunctionField (y_gen W)).map
        (algebraMap W.toAffine.FunctionField W.toAffine.FunctionField)) := by
  classical
  refine ⟨minpoly_gen_splits_of_mem_range W ℓ hℓ (x_gen W) (fun g hfix => ?_),
          minpoly_gen_splits_of_mem_range W ℓ hℓ (y_gen W) (fun g hfix => ?_)⟩
  · exact (sigma_genCoord_mem_range_proto W ℓ hℓ
      (IsScalarTower.toAlgHom F W.toAffine.FunctionField
        (AlgebraicClosure W.toAffine.FunctionField)) g hfix).1
  · exact (sigma_genCoord_mem_range_proto W ℓ hℓ
      (IsScalarTower.toAlgHom F W.toAffine.FunctionField
        (AlgebraicClosure W.toAffine.FunctionField)) g hfix).2

/-- **`h_normal` for `[ℓ]` over `K̄`** (Silverman III.4.10c). Discharges the `h_normal` hypothesis
of `card_kernel_eq_degree_of_separable_concrete` at `φ = mulByInt W.toAffine ℓ`: the function-field
extension `K(E)/[ℓ]*K(E)` is normal.

Proof: algebraicity is finite-dimensionality (`isogeny_finiteDimensional`). For splitting, `K(E)` is
generated over `F ⊆ [ℓ]*K(E)` by `x_gen, y_gen` (`adjoin_x_gen_y_gen_eq_top`); by
`IntermediateField.splits_of_mem_adjoin`, every minimal polynomial over `[ℓ]*K(E)` splits in `K(E)`
once the two generator minimal polynomials do (`mulByInt_genCoords_minpoly_splits`). Packaged via
`normal_iff`. -/
theorem h_normal_mulByInt [IsAlgClosed F] (ℓ : ℤ) (hℓ : ℓ ≠ 0) :
    letI := (mulByInt W.toAffine ℓ).toAlgebra
    Normal W.toAffine.FunctionField W.toAffine.FunctionField := by
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  haveI hfin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine ℓ).toAlgebra.toModule :=
    isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)
  haveI halg : Algebra.IsAlgebraic W.toAffine.FunctionField W.toAffine.FunctionField :=
    Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨hsx, hsy⟩ := mulByInt_genCoords_minpoly_splits W ℓ hℓ
  refine normal_iff.mpr fun z => ⟨(halg.isAlgebraic z).isIntegral, ?_⟩
  have hz : z ∈ IntermediateField.adjoin W.toAffine.FunctionField
      ({x_gen W, y_gen W} : Set W.toAffine.FunctionField) := by
    have hsub : IntermediateField.adjoin F ({x_gen W, y_gen W} : Set W.toAffine.FunctionField) ≤
        (IntermediateField.adjoin W.toAffine.FunctionField
          ({x_gen W, y_gen W} : Set W.toAffine.FunctionField)).restrictScalars F :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin _ _)
    exact hsub (by rw [adjoin_x_gen_y_gen_eq_top W]; trivial :
      z ∈ IntermediateField.adjoin F ({x_gen W, y_gen W} : Set W.toAffine.FunctionField))
  refine IntermediateField.splits_of_mem_adjoin
    (F := W.toAffine.FunctionField) (K := W.toAffine.FunctionField)
    (L := W.toAffine.FunctionField) (splits := fun x hx => ?_) hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨(halg.isAlgebraic _).isIntegral, hsx⟩
  · exact ⟨(halg.isAlgebraic _).isIntegral, hsy⟩

end HasseWeil
