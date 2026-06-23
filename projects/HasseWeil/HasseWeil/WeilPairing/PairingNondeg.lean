/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.Pairing
import HasseWeil.WeilPairing.PairingProps
import HasseWeil.WeilPairing.DivisorPullback
import HasseWeil.WeilPairing.TorsionCardEll
import HasseWeil.EC.SeparableKernelTorsor
import HasseWeil.Curves.MillerAllChar

/-!
# Nondegeneracy of the Weil pairing `e_ℓ` (Silverman III.8.1c, ticket T-R2-NONDEG)

The finite-level Weil pairing `e_ℓ : E[ℓ] × E[ℓ] → F` over an algebraically closed field `F`
(`(ℓ : F) ≠ 0`) is **nondegenerate in the second slot**:

```
weilPairing_nondegenerate : (∀ S, ℓ • S = 0 → e_ℓ(S, T) = 1) → T = O      (T ∈ E[ℓ]).
```

## The proof (Silverman III.8.1c)

Suppose `e_ℓ(S, T) = 1` for all `S ∈ E[ℓ]`. From the pairing relation
`τ_S g_T = e_ℓ(S, T) · g_T` (`weilPairing_translate`) this means `τ_S g_T = g_T` for all
`S ∈ E[ℓ]`, i.e. `g_T` is fixed by every translation `τ_S`, `S ∈ ker[ℓ]`.

Over `K̄` the extension `K(E) / [ℓ]^* K(E)` is **Galois** with group `ker[ℓ]` acting by translation
(`isGalois_of_isSeparable_and_normal` from `mulByInt_isSeparable` + `h_normal_mulByInt`; the
torsion-torsor bijection `forward : ker[ℓ] ≃ Aut(K(E)/[ℓ]^*K(E))` of `SeparableKernelTorsor.lean`).
So `g_T` fixed by every `τ_S` ⟹ `g_T` fixed by every automorphism `σ`, whence `g_T ∈ ⊥` (the bottom
intermediate field, `IsGalois.mem_bot_iff_fixed`), i.e. `g_T = [ℓ]^* h` for some `h ∈ K(E)`
(`IntermediateField.mem_bot`; `algebraMap` of `[ℓ].toAlgebra` *is* `[ℓ].pullback`).

Then `div(g_T) = div([ℓ]^* h) = [ℓ]^*(div h)` (divisor-pullback functoriality
`projectiveDivisorOf_pullback_eq_pullbackDivisor`). But `div(g_T) = [ℓ]^*((T) − (O))`
(`weilFunction_divisor`, written as `pullbackDivisor` of `(T) − (O)`). By **injectivity of `[ℓ]^*`
on divisors** — which holds because `[ℓ]` is **surjective** on `E(K̄)` (Silverman III.4.10b), so the
fibre-pullback `pullbackDivisor` recovers each coefficient — we get `div h = (T) − (O)`. Hence
`(T) − (O)` is principal, so `T = O` by Abel–Jacobi (`(P) ∼ (Q) ⟺ P = Q`, here in the form
`σ(div h) = 0` for a principal divisor, with `σ((T) − (O)) = T`).

## The single deep geometric input

The one non-trivial geometric fact this proof rests on is **`[ℓ] : E(K̄) → E(K̄)` is surjective**
(Silverman III.4.10b: a nonzero isogeny is surjective on `K̄`-points), `mulByInt_point_surjective`,
used only to prove the divisor-pullback injectivity `pullbackDivisor_injective`. It is now proven by
the elementary division-polynomial route: for `Q = (x_Q, y_Q)`, the `x`-coordinate of a preimage is
a root of the monic degree-`ℓ²` fibre polynomial `g := Φ_ℓ − x_Q·Ψ²_ℓ`, which splits over `K̄`; a
root `x₀` lifts to a curve point `(x₀, y₀)` (`exists_point_on_curve`), with `Ψ²_ℓ(x₀) ≠ 0` forced by
coprimality `isCoprime_Φ_ΨSq`. The forward formula `zsmul_affine_point_eq_gen` then gives
`x([ℓ]·(x₀,y₀)) = Φ_ℓ(x₀)/Ψ²_ℓ(x₀) = x_Q`, so `[ℓ]·(x₀,y₀) = ±Q`; one of `±(x₀,y₀)` is a preimage.

The whole proof is axiom-clean — in particular the genuinely delicate / novel content of Prop 8.1c:

* the Galois fixed-field step `mem_pullback_range_of_translate_fixed` (and `aut_eq_translate`: every
  `[ℓ]^*K(E)`-automorphism is a translation), axiom-clean `[propext, Classical.choice, Quot.sound]`;
* the Abel–Jacobi `(T) ∼ (O) ⟹ T = O` `eq_zero_of_kappaDivisor_principal`, axiom-clean;
* the divisor-functoriality wiring `pullbackDivisor_kappaDivisor`, axiom-clean.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Prop 8.1c), III.4.10b, III.3.3.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric HasseWeil.WeilPairing.DivisorPullback

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

section Nondeg

variable [IsAlgClosed F]

/-! ### The single deep geometric input: `[ℓ]` is surjective on `E(K̄)` -/

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`[ℓ] : E(K̄) → E(K̄)` is surjective** (Silverman III.4.10b: every nonzero isogeny is surjective
on `K̄`-points). For `Q ∈ E(K̄)`, the `x`-coordinate of a preimage is a root of the degree-`ℓ²`
polynomial `Φ_ℓ(X) − x_Q · Ψ_ℓ²(X)` over `K̄`, which splits since `K̄` is algebraically closed; the
`y`-coordinate then comes from the Weierstrass quadratic. (The boundary case `Ψ_ℓ(x₀) = 0` —
`P` an `ℓ`-torsion point — is handled by the coprimality of `Φ_ℓ` and `Ψ_ℓ²`.)

This is the one genuinely-geometric input of nondegeneracy; it is used only to prove
`pullbackDivisor_injective`. -/
theorem mulByInt_point_surjective (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    Function.Surjective (mulByInt W.toAffine ℓ).toAddMonoidHom := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  -- `[ℓ]·P = ℓ • P`; reduce to finding a preimage point.
  intro Q
  simp only [mulByInt_apply]
  -- The curve has nonzero discriminant (`[IsElliptic]`), so `Φ_ℓ`, `Ψ²_ℓ` are coprime.
  have hΔ : W.Δ ≠ 0 := W.coe_Δ' ▸ W.Δ'.ne_zero
  have hcop : IsCoprime (W.Φ ℓ) (W.ΨSq ℓ) := isCoprime_Φ_ΨSq W hΔ hℓ0
  rcases Q with _ | ⟨x_Q, y_Q, hQns⟩
  · -- `Q = O`: take `P = O`.
    exact ⟨0, zsmul_zero ℓ⟩
  · -- `Q = (x_Q, y_Q)`: the `x`-coordinate of a preimage is a root of the fibre polynomial
    -- `g := Φ_ℓ − x_Q·Ψ²_ℓ`, which is monic of degree `ℓ² > 0`, hence has a root over `K̄`.
    set g : Polynomial F := W.Φ ℓ - Polynomial.C x_Q * W.ΨSq ℓ with hg_def
    have hΦ_monic : (W.Φ ℓ).Monic := W.leadingCoeff_Φ ℓ
    have hΦ_natDeg : (W.Φ ℓ).natDegree = ℓ.natAbs ^ 2 := W.natDegree_Φ ℓ
    have hℓ2_pos : 0 < ℓ.natAbs ^ 2 := pow_pos (Int.natAbs_pos.mpr hℓ0) 2
    have hsub_natDeg_le :
        (Polynomial.C x_Q * W.ΨSq ℓ).natDegree ≤ ℓ.natAbs ^ 2 - 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (W.natDegree_ΨSq_le ℓ)
    have hg_monic : g.Monic := by
      refine hΦ_monic.sub_of_left ?_
      rw [Polynomial.degree_eq_natDegree hΦ_monic.ne_zero, hΦ_natDeg]
      refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
      exact_mod_cast lt_of_le_of_lt hsub_natDeg_le (Nat.sub_lt hℓ2_pos Nat.one_pos)
    have hg_natDeg : g.natDegree = ℓ.natAbs ^ 2 := by
      rw [hg_def]
      refine (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_).trans hΦ_natDeg
      rw [hΦ_natDeg]; exact lt_of_le_of_lt hsub_natDeg_le (Nat.sub_lt hℓ2_pos Nat.one_pos)
    -- A root `x₀ ∈ K̄` of `g`.
    obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root g (by
      rw [Polynomial.degree_eq_natDegree hg_monic.ne_zero, hg_natDeg]
      exact_mod_cast hℓ2_pos.ne')
    -- `g(x₀) = 0` ⟹ `Φ_ℓ(x₀) = x_Q · Ψ²_ℓ(x₀)`.
    have hroot : (W.Φ ℓ).eval x₀ = x_Q * (W.ΨSq ℓ).eval x₀ := by
      rw [Polynomial.IsRoot.def, hg_def, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, sub_eq_zero] at hx₀
      exact hx₀
    -- Lift `x₀` to a point `(x₀, y₀)` on the curve.
    obtain ⟨y₀, hy₀eq⟩ := exists_point_on_curve W x₀
    have hns₀ : W.toAffine.Nonsingular x₀ y₀ :=
      (W.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp hy₀eq
    -- `Ψ²_ℓ(x₀) ≠ 0`: else `Φ_ℓ(x₀) = x_Q·0 = 0`, contradicting coprimality of `Φ_ℓ`, `Ψ²_ℓ`.
    have hΨSq_ne : (W.ΨSq ℓ).eval x₀ ≠ 0 := by
      intro hΨ0
      have hor := Polynomial.aeval_ne_zero_of_isCoprime hcop x₀
      simp only [Polynomial.coe_aeval_eq_eval] at hor
      rcases hor with hΦne | hΨne
      · rw [hroot, hΨ0, mul_zero] at hΦne; exact hΦne rfl
      · exact hΨne hΨ0
    -- Hence `ψ_ℓ(x₀, y₀) ≠ 0` (it is a square root of `Ψ²_ℓ(x₀)`).
    have hψ_ne : (W.ψ ℓ).evalEval x₀ y₀ ≠ 0 := by
      intro hψ0
      apply hΨSq_ne
      rw [ΨSq_eval_eq_psi_sq W hy₀eq ℓ, hψ0, zero_pow (by norm_num)]
    -- Forward formula: `ℓ • (x₀, y₀) = (Φ_ℓ(x₀)/Ψ²_ℓ(x₀), …)`, whose `x`-coordinate is `x_Q`.
    obtain ⟨hns', hsmul⟩ := zsmul_affine_point_eq_gen W ℓ hns₀ hψ_ne
    -- The `x`-coordinate of `ℓ • (x₀, y₀)` equals `x_Q`.
    have hx_eq : (W.φ ℓ).evalEval x₀ y₀ / (W.ψ ℓ).evalEval x₀ y₀ ^ 2 = x_Q := by
      rw [evalEval_φ_eq_Φ W hy₀eq ℓ,
        show (W.ψ ℓ).evalEval x₀ y₀ ^ 2 = (W.ΨSq ℓ).eval x₀ from
          (ΨSq_eval_eq_psi_sq W hy₀eq ℓ).symm,
        hroot, mul_div_assoc, div_self hΨSq_ne, mul_one]
    -- The image point `(xφ, y')` (with `xφ = x_Q`) and `(x_Q, y_Q)` are both on the curve, so
    -- `y' = y_Q` or `y' = negY x_Q y_Q` (`Y_eq_of_X_eq`, applied through `hx_eq : xφ = x_Q`).
    have heqn' : W.toAffine.Equation
        ((W.φ ℓ).evalEval x₀ y₀ / (W.ψ ℓ).evalEval x₀ y₀ ^ 2)
        ((W.ω ℓ).evalEval x₀ y₀ / (W.ψ ℓ).evalEval x₀ y₀ ^ 3) :=
      Affine.equation_iff_nonsingular.mpr hns'
    have heqnQ : W.toAffine.Equation x_Q y_Q := Affine.equation_iff_nonsingular.mpr hQns
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq heqn' heqnQ hx_eq with hyy | hyy
    · -- `y' = y_Q`: `ℓ • (x₀, y₀) = Q`, take `P = (x₀, y₀)`.
      refine ⟨Affine.Point.some x₀ y₀ hns₀, ?_⟩
      rw [hsmul]
      exact (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hx_eq, hyy⟩
    · -- `y' = negY x_Q y_Q`: `ℓ • (x₀, y₀) = -Q`, so `ℓ • (-(x₀, y₀)) = Q`.
      refine ⟨-(Affine.Point.some x₀ y₀ hns₀), ?_⟩
      rw [zsmul_neg, hsmul, Affine.Point.neg_some]
      refine (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨hx_eq, ?_⟩
      -- `negY xφ y' = y_Q`: substitute `xφ = x_Q`, `y' = negY x_Q y_Q`, use `negY_negY`.
      rw [hx_eq, hyy, WeierstrassCurve.Affine.negY_negY]

/-! ### Injectivity of the divisor pullback `[ℓ]^*`

The fibre-pullback `pullbackDivisor [ℓ]` reads off the coefficient of `D` at the image place `[ℓ]·v`
at every place `v` (`pullbackDivisor_apply`). Since `[ℓ]` is surjective on `E(K̄)`
(`mulByInt_point_surjective`), every place is `[ℓ]·v` for some `v`, so `pullbackDivisor [ℓ] D`
determines `D` — i.e. `pullbackDivisor [ℓ]` is injective. -/

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`pullbackDivisor [ℓ]` is injective** (over `K̄`). If `pullbackDivisor [ℓ] D₁ = pullbackDivisor
[ℓ] D₂` then `D₁ = D₂`: at any place `w`, by `pullbackDivisor_apply`, `D₁((ℓ·w.toAffine).proj) =
D₂((ℓ·w.toAffine).proj)`; surjectivity of `[ℓ]` on points (`mulByInt_point_surjective`) makes every
place arise as `(ℓ·w.toAffine).proj`, so `D₁ = D₂`. -/
theorem pullbackDivisor_injective (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] :
    Function.Injective
      (pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker) := by
  intro D₁ D₂ hD
  refine Finsupp.ext fun v ↦ ?_
  -- Pick `w` with `[ℓ]·w.toAffine = v.toAffinePoint` (point-surjectivity).
  obtain ⟨P, hP⟩ := mulByInt_point_surjective W ℓ hℓ v.toAffinePoint
  -- A place mapping onto `v` under `[ℓ]`: `w := P.toProjectiveSmoothPoint`.
  set w : ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F) :=
    P.toProjectiveSmoothPoint with hw
  have hwaff : (mulByInt W.toAffine ℓ).toAddMonoidHom w.toAffinePoint = v.toAffinePoint := by
    rw [hw, Affine.Point.toProjectiveSmoothPoint_toAffinePoint]; exact hP
  have h1 := congrFun (congrArg DFunLike.coe hD) w
  rw [pullbackDivisor_apply (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker D₁ w,
    pullbackDivisor_apply (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker D₂ w,
    hwaff, Affine.Point.toAffinePoint_toProjectiveSmoothPoint] at h1
  exact h1

/-! ### Abel–Jacobi: `(T) ∼ (O) ⟹ T = O`

A principal degree-`0` divisor has trivial `σ`-image (`projectiveDivisorSum_eq_zero_of_principal`,
all characteristics via `afInputs_allChar`), and `σ((T) − (O)) = T`. So if `(T) − (O)` is principal
then `T = O`. This is Silverman III.3.3 (`Pic⁰(E) ≅ E`) in the form needed here. -/

/-- **`(T) ∼ (O) ⟹ T = O`** (Abel–Jacobi, Silverman III.3.3). If the divisor `(T) − (O) =
`kappaDivisor W T`` is principal, then `T = O`. Proof: `σ` (the group-sum map) vanishes on principal
divisors (`projectiveDivisorSum_eq_zero_of_principal`), and `σ((T) − (O)) = T`
(`projectiveDivisorSum_kappaDivisor`). -/
theorem eq_zero_of_kappaDivisor_principal {T : W.toAffine.Point}
    (hT : (⟨W.toAffine⟩ : SmoothPlaneCurve F).ProjIsPrincipal
      (Curves.kappaDivisor W.toAffine T)) :
    T = 0 := by
  have hvan : Curves.projectiveDivisorSum W.toAffine (Curves.kappaDivisor W.toAffine T) = 0 :=
    (afInputs_allChar W.toAffine).h_van
      (fun _ hD ↦ SmoothPlaneCurve.principal_mem_degZero (C := ⟨W.toAffine⟩) hD)
      (Curves.kappaDivisor W.toAffine T) hT
  rwa [Curves.projectiveDivisorSum_kappaDivisor] at hvan

/-! ### The Galois fixed-field step: every automorphism is a translation

The torsion-torsor of `SeparableKernelTorsor.lean` makes `forward : ker[ℓ] → Aut(K(E)/[ℓ]^*K(E))`,
`k ↦ τ_k`, a bijection. We reconstruct the surjectivity half (`h_right`): every `σ ∈ Aut` agrees, as
an `F`-algebra map, with the translation `τ_{k.val}` for the descended kernel point `k = σ(P_gen) −
P_gen` (`hdesc_mulByInt`). This is the geometric content `Aut ≃ ker[ℓ]` (Silverman III.4.10c). -/

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **Every `[ℓ]^*K(E)`-automorphism of `K(E)` is a translation by an `ℓ`-torsion point.** For each
`σ ∈ Aut(K(E)/[ℓ]^*K(E))` there is `k ∈ E[ℓ]` with `σ z = τ_k z` for all `z`. The kernel point `k =
σ(P_gen) − P_gen` is supplied by the descent torsor `hdesc_mulByInt`; the agreement is forced on the
generators `x_gen, y_gen` (`genericPointAct_kernelTranslateForwardAut` + `genericPointAct_eq_some`)
and extends to all of `K(E)` by `algHom_ext_x_y_gen`. -/
theorem aut_eq_translate (ℓ : ℤ) (hℓ0 : ℓ ≠ 0)
    (σ : @AlgEquiv KE KE KE _ _ _
      (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra) :
    ∃ k : W.toAffine.Point, ℓ • k = 0 ∧
      ∀ z : KE, σ z = translateAlgEquivOfPoint W k z := by
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  -- The covariance hypothesis `hcov` for `[ℓ]` and the resulting `forward` map.
  have hcov := hcov_mulByInt_of_xy W ℓ hℓ0 (hxy_mulByInt W ℓ hℓ0)
  set forward := kernelTranslateForwardAut W (mulByInt W.toAffine ℓ) hcov with hfwd_def
  -- The descended kernel point `k = σ(P_gen) − P_gen`.
  obtain ⟨k, hk_mem, hk_lift⟩ := hdesc_mulByInt W ℓ hℓ0 σ
  have hk0 : ℓ • k = 0 := by
    rw [← mulByInt_apply]; exact (HasseWeil.Isogeny.mem_kernel_iff _ k).mp hk_mem
  refine ⟨k, hk0, ?_⟩
  -- `forward ⟨k, hk_mem⟩` acts on `P_gen` as `P_gen + lift k = genericPointAct σ`.
  have hact : genericPointAct W (mulByInt W.toAffine ℓ) (forward ⟨k, hk_mem⟩) =
      genericPointAct W (mulByInt W.toAffine ℓ) σ := by
    rw [hfwd_def,
      genericPointAct_kernelTranslateForwardAut W (mulByInt W.toAffine ℓ) hcov ⟨k, hk_mem⟩]
    rw [hk_lift, add_comm, sub_add_cancel]
  -- Read off coordinate agreement on `x_gen`, `y_gen`.
  rw [genericPointAct_eq_some W (mulByInt W.toAffine ℓ) (forward ⟨k, hk_mem⟩),
    genericPointAct_eq_some W (mulByInt W.toAffine ℓ) σ] at hact
  have hcoords := (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hact
  -- `forward ⟨k, hk_mem⟩ z` is definitionally `τ_k z`, so `hcoords` gives `τ_k = σ` on generators.
  have hσx : σ (x_gen W) = translateAlgEquivOfPoint W k (x_gen W) := hcoords.1.symm
  have hσy : σ (y_gen W) = translateAlgEquivOfPoint W k (y_gen W) := hcoords.2.symm
  have hcoeq : (σ.toAlgHom.restrictScalars F) = (translateAlgEquivOfPoint W k).toAlgHom :=
    algHom_ext_x_y_gen W hσx hσy
  intro z
  exact DFunLike.congr_fun hcoeq z

/-! ### The fixed-field consequence: `g_T = [ℓ]^* h`

If `g_T` is fixed by every translation `τ_S` (`S ∈ E[ℓ]`), then by `aut_eq_translate` it is fixed by
every automorphism `σ`, so `g_T ∈ (⊥ : IntermediateField [ℓ]^*K(E) K(E))`
(`IsGalois.mem_bot_iff_fixed`), i.e. `g_T = [ℓ]^* h` (`IntermediateField.mem_bot`; `algebraMap` of
`[ℓ].toAlgebra` is `[ℓ].pullback`). -/

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`g` fixed by all `ℓ`-translations lies in `[ℓ]^*K(E)`.** If `τ_S g = g` for every `S ∈ E[ℓ]`,
then `g = [ℓ]^* h` for some `h ∈ K(E)`. Combines `aut_eq_translate` (every automorphism is a
translation), the Galois `IsGalois.mem_bot_iff_fixed`, and `IntermediateField.mem_bot`. -/
theorem mem_pullback_range_of_translate_fixed (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    {g : KE} (hg : ∀ S : W.toAffine.Point, ℓ • S = 0 →
      translateAlgEquivOfPoint W S g = g) :
    ∃ h : KE, (mulByInt W.toAffine ℓ).pullback h = g := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  letI := (mulByInt W.toAffine ℓ).toAlgebra
  -- The Galois / finite-dimensional structure on `K(E) / [ℓ]^*K(E)`.
  haveI hfin : @FiniteDimensional KE KE _ _ (mulByInt W.toAffine ℓ).toAlgebra.toModule :=
    isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)
  haveI hgal : @IsGalois KE _ KE _ (mulByInt W.toAffine ℓ).toAlgebra :=
    Isogeny.isGalois_of_isSeparable_and_normal (mulByInt W.toAffine ℓ)
      (mulByInt_isSeparable W ℓ hℓ) (h_normal_mulByInt W ℓ hℓ0)
  -- `g` is fixed by every automorphism (each is a translation by `aut_eq_translate`).
  have hfix : ∀ σ : @AlgEquiv KE KE KE _ _ _
      (mulByInt W.toAffine ℓ).toAlgebra (mulByInt W.toAffine ℓ).toAlgebra, σ g = g := by
    intro σ
    obtain ⟨k, hk0, hσ⟩ := aut_eq_translate W ℓ hℓ0 σ
    rw [hσ g]; exact hg k hk0
  -- Hence `g ∈ ⊥`, i.e. `g ∈ range (algebraMap base K(E)) = range [ℓ].pullback`.
  have hbot : g ∈ (⊥ : IntermediateField KE KE) :=
    (IsGalois.mem_bot_iff_fixed g).mpr hfix
  rwa [IntermediateField.mem_bot] at hbot

/-! ### Assembly: nondegeneracy `(∀ S, e_ℓ(S,T) = 1) → T = O` -/

omit [IsAlgClosed F] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`[ℓ]^*((T) − (O))` is the divisor of `g_T`.** The fibre-pullback `pullbackDivisor [ℓ]` of
the divisor `(T) − (O) = kappaDivisor T` equals `pullbackDiv [ℓ] T − pullbackDiv [ℓ] O`, the divisor
of `g_T` (`weilFunction_divisor`). (`∞.toAffinePoint = O`.) -/
theorem pullbackDivisor_kappaDivisor (ℓ : ℤ)
    [hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker] (T : W.toAffine.Point) :
    pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        (Curves.kappaDivisor W.toAffine T) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker 0 := by
  rw [Curves.kappaDivisor, ← pullbackDivisorHom_apply, map_sub, pullbackDivisorHom_apply,
    pullbackDivisorHom_apply, pullbackDivisor_single, pullbackDivisor_single, one_smul, one_smul,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    ProjectiveSmoothPoint.toAffinePoint_infinity]

/-- **Nondegeneracy of the Weil pairing** (Silverman III.8.1c). If `e_ℓ(S, T) = 1` for every
`S ∈ E[ℓ]`, then `T = O` (for `T ∈ E[ℓ]`).

Proof. The hypothesis gives `τ_S g_T = e_ℓ(S, T) · g_T = g_T` for all `S ∈ E[ℓ]`
(`weilPairing_translate`), so `g_T = [ℓ]^* h` for some `h` (the Galois fixed-field step
`mem_pullback_range_of_translate_fixed`). Then `[ℓ]^*(div h) = div([ℓ]^* h) = div(g_T) = [ℓ]^*((T) −
(O))` (functoriality `projectiveDivisorOf_pullback_eq_pullbackDivisor` + `weilFunction_divisor` +
`pullbackDivisor_kappaDivisor`), so `div h = (T) − (O)` by injectivity of `[ℓ]^*`
(`pullbackDivisor_injective`, from `[ℓ]` surjective on `E(K̄)`). Hence `(T) − (O)` is principal, so
`T = O` by Abel–Jacobi (`eq_zero_of_kappaDivisor_principal`). -/
theorem weilPairing_nondegenerate (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0)
    (h_deg : ∀ S : W.toAffine.Point, (hS : ℓ • S = 0) →
      weilPairing W ℓ hℓ S T hS hT = 1) :
    T = 0 := by
  haveI hker : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := mulByInt_ker_finite W ℓ hℓ
  have hcore : ProjOrdTransport (mulByInt W.toAffine ℓ) := projOrdTransport_mulByInt ℓ hℓ
  -- `g_T` is fixed by every `ℓ`-translation.
  have hfix : ∀ S : W.toAffine.Point, ℓ • S = 0 →
      translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT) = weilFunction W ℓ hℓ T hT := by
    intro S hS
    rw [weilPairing_translate W ℓ hℓ S T hS hT, h_deg S hS, map_one, one_mul]
  -- So `g_T = [ℓ]^* h` for some `h`.
  obtain ⟨h, hh⟩ := mem_pullback_range_of_translate_fixed W ℓ hℓ hfix
  have hh_ne : h ≠ 0 := by
    rintro rfl
    rw [map_zero] at hh
    exact weilFunction_ne_zero W ℓ hℓ T hT hh.symm
  -- `div(g_T) = [ℓ]^*(div h)`.
  have hdiv_pullback : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (weilFunction W ℓ hℓ T hT) =
      pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        ((⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf h) := by
    rw [← hh,
      projectiveDivisorOf_pullback_eq_pullbackDivisor (W := W.toAffine) hcore h]
  -- `div(g_T) = [ℓ]^*((T) − (O))`.
  have hdiv_kappa : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf
      (weilFunction W ℓ hℓ T hT) =
      pullbackDivisor (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom hker
        (Curves.kappaDivisor W.toAffine T) :=
    (weilFunction_divisor W ℓ hℓ T hT).trans (pullbackDivisor_kappaDivisor W ℓ T).symm
  -- `[ℓ]^*(div h) = [ℓ]^*((T) − (O))`, so `div h = (T) − (O)` by injectivity.
  have hdiv_eq : (⟨W.toAffine⟩ : SmoothPlaneCurve F).projectiveDivisorOf h =
      Curves.kappaDivisor W.toAffine T :=
    pullbackDivisor_injective W ℓ hℓ (hdiv_pullback.symm.trans hdiv_kappa)
  -- `(T) − (O)` is principal (it is `div h`), so `T = O` by Abel–Jacobi.
  exact eq_zero_of_kappaDivisor_principal W ⟨h, hh_ne, hdiv_eq⟩

end Nondeg

end HasseWeil.WeilPairing
