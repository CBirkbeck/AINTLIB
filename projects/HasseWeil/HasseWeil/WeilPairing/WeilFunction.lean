import HasseWeil.Curves.PicZero
import HasseWeil.Curves.MillerAllChar
import HasseWeil.Curves.EffectiveSumReduce
import HasseWeil.WeilPairing.Pullback
import HasseWeil.WeilPairing.SigmaBridge

/-!
# Route 2A — the Weil function divisor (Weil pairing construction, step 1)

The finite-level Weil pairing `e_ℓ(S,T)` (Silverman III.8.1) is built from a function `f_T` with
divisor `ℓ(T) − ℓ(O)` for `T ∈ E[ℓ]`. The existence of `f_T` is **Abel–Jacobi**: a degree-`0`
divisor `D` on `E` is principal iff its `σ`-image (group sum) is `O`.

This file ships the divisor `D_T := ℓ(T) − ℓ(O)` and the two Abel–Jacobi prerequisites:
* `degree_weilDivisor` — `deg D_T = 0`;
* `sigma_weilDivisor` — `σ(D_T) = ℓ • T`, hence `σ(D_T) = O` exactly when `T ∈ E[ℓ]`
  (`weilDivisor_sigma_eq_zero`).

Together these say `D_T` lies in the kernel of `(deg, σ)`, i.e. `D_T` is principal — the input to
extracting the Weil function `f_T`.
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing

open Curves

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]

/-- **The `[ℓ]`-fibre is invariant under translation by `S ∈ E[ℓ]`** (the fibre-shift behind the
translation functoriality `div(τ_S^* g) = div(g)` of the Weil pairing): for `ℓ • S = 0`,
`ℓ • (Q + S) = T ↔ ℓ • Q = T`. -/
theorem smul_add_torsion_eq_iff {ℓ : ℤ} {S : W.Point} (hS : ℓ • S = 0) (T Q : W.Point) :
    ℓ • (Q + S) = T ↔ ℓ • Q = T := by
  rw [smul_add, hS, add_zero]

/-- The `[ℓ]`-fibre over `T` maps to itself bijectively under `· + S` for `S ∈ E[ℓ]`. This is the
geometric reason the Weil pairing value `e_ℓ(S,T) = (τ_S^* g)/g` is constant: translation by an
`ℓ`-torsion point permutes the fibre `[ℓ]^{-1}(T)`, leaving the divisor `div(g) = [ℓ]^*(T)−[ℓ]^*(O)`
unchanged. -/
def fiberTranslateEquiv {ℓ : ℤ} {S : W.Point} (hS : ℓ • S = 0) (T : W.Point) :
    {Q : W.Point // ℓ • Q = T} ≃ {Q : W.Point // ℓ • Q = T} :=
  Equiv.subtypeEquiv (Equiv.addRight S) (fun Q => (smul_add_torsion_eq_iff hS T Q).symm)

/-- **The Weil divisor** `D_T := ℓ·(T) − ℓ·(O)` (projective) for `T ∈ E` and `ℓ : ℤ`. For
`T ∈ E[ℓ]` this is the divisor of the Weil function `f_T`. -/
noncomputable def weilDivisor (T : W.Point) (ℓ : ℤ) :
    Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F) :=
  Finsupp.single T.toProjectiveSmoothPoint ℓ -
    Finsupp.single (0 : W.Point).toProjectiveSmoothPoint ℓ

omit [DecidableEq F] in
/-- **`deg D_T = 0`**: the Weil divisor has degree zero (`ℓ − ℓ`). -/
theorem degree_weilDivisor (T : W.Point) (ℓ : ℤ) :
    (weilDivisor T ℓ).degree = 0 := by
  rw [weilDivisor, ← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
    Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
    degree_single, degree_single, sub_self]

/-- **`σ(D_T) = ℓ • T`**: the `σ`-image (group sum) of the Weil divisor is `ℓ • T`. -/
theorem sigma_weilDivisor (T : W.Point) (ℓ : ℤ) :
    Curves.projectiveDivisorSum W (weilDivisor T ℓ) = ℓ • T := by
  rw [weilDivisor, Curves.projectiveDivisorSum_sub, Curves.projectiveDivisorSum_single,
    Curves.projectiveDivisorSum_single, Affine.Point.toProjectiveSmoothPoint_toAffinePoint,
    Affine.Point.toProjectiveSmoothPoint_toAffinePoint, smul_zero, sub_zero]

/-- **Abel–Jacobi prerequisite for `T ∈ E[ℓ]`**: if `ℓ • T = 0` (i.e. `T` is an `ℓ`-torsion point),
then `σ(D_T) = O`. Together with `degree_weilDivisor` (`deg D_T = 0`), this is exactly the condition
for `D_T = ℓ(T) − ℓ(O)` to be **principal** — the divisor of the Weil function `f_T`. -/
theorem weilDivisor_sigma_eq_zero (T : W.Point) (ℓ : ℤ) (hT : ℓ • T = 0) :
    Curves.projectiveDivisorSum W (weilDivisor T ℓ) = 0 := by
  rw [sigma_weilDivisor, hT]

/-! ### Abel–Jacobi: extracting the Weil function `f_T` (pairing step 2)

`Pic⁰(E) ≅ E` (`Curves.picZeroIsoE`) makes the degree-0 divisor class group isomorphic to the
points, via `[D] = [(σD) − (O)]` (`Curves.divZeroReduce_holds_allChar`, axiom-clean in all
characteristics, needing only `IsIntegrallyClosed` of the coordinate ring). Hence a degree-`0`
divisor `D` with `σ(D) = O` is **principal**, and for `T ∈ E[ℓ]` the Weil divisor
`D_T = ℓ(T) − ℓ(O)` is the divisor of a function `f_T`. -/

/-- **Abel–Jacobi extraction**: a degree-`0` projective divisor with `σ(D) = O` is principal.
From `divZeroReduce` (`D ∼ (σD) − (O)`) at `σD = O`, where `(O) − (O) = 0`. -/
theorem projIsPrincipal_of_degZero_of_sigma_eq_zero
    [IsIntegrallyClosed (⟨W⟩ : Curves.SmoothPlaneCurve F).CoordinateRing]
    (D : Curves.ProjectiveDivisor (⟨W⟩ : Curves.SmoothPlaneCurve F))
    (hdeg : D.degree = 0) (hsig : Curves.projectiveDivisorSum W D = 0) :
    (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal D := by
  have h := Curves.divZeroReduce_holds_allChar W
    ⟨D, Curves.ProjectiveDivisor.mem_degZero.mpr hdeg⟩
  rw [hsig, Curves.kappaDivisor_zero] at h
  simpa [Curves.SmoothPlaneCurve.ProjLinearlyEquiv] using h

/-- **The Weil function exists** (Silverman III.8.1): for `T ∈ E[ℓ]` (`ℓ • T = 0`), the Weil divisor
`ℓ(T) − ℓ(O)` is principal — there is a function `f_T` with `div(f_T) = ℓ(T) − ℓ(O)`. This is the
function from which the pairing `e_ℓ(·, T)` is built. -/
theorem weilFunction_exists
    [IsIntegrallyClosed (⟨W⟩ : Curves.SmoothPlaneCurve F).CoordinateRing]
    (T : W.Point) (ℓ : ℤ) (hT : ℓ • T = 0) :
    (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal (weilDivisor T ℓ) :=
  projIsPrincipal_of_degZero_of_sigma_eq_zero (weilDivisor T ℓ)
    (degree_weilDivisor T ℓ) (weilDivisor_sigma_eq_zero T ℓ hT)

/-! ### The pulled-back function `g` (pairing step 3a)

The second Weil function `g` has divisor `[ℓ]*((T)) − [ℓ]*((O)) = Σ_{[ℓ]P=T}(P) − Σ_{[ℓ]P=O}(P)`,
the multiplicity-free fibre difference (`pullbackDiv` from `Pullback.lean`). It exists iff that
divisor is principal: degree `#ker − #ker = 0`, and `σ = #ker · P₀`
(`SigmaBridge.sigma_pullbackDiv_sub`, for any `P₀` with `[ℓ]P₀ = T`). So `g` exists exactly when
`#ker(f) · P₀ = O` — which, for `f = [ℓ]` and `T ∈ E[ℓ]`, is the consequence of `#ker[ℓ] = ℓ²`
(then `ℓ²·P₀ = ℓ·([ℓ]P₀) = ℓ·T = O`). This isolates the lone torsion-card dependency
`#ker[ℓ] = ℓ²` (Silverman III.4.10/12, T-II-2-009 over `K̄`) as the single clean hypothesis
`hann`. -/

/-- **The `g`-divisor is principal** (pairing step 3a): for an additive endomorphism `f` (the `[ℓ]`
point map) with finite kernel, a point `P₀` with `f P₀ = T`, and the annihilation `#ker(f)·P₀ = O`,
the fibre-difference `f*((T)) − f*((O))` is principal — i.e. the second Weil function `g` (with
`div g = [ℓ]*((T)) − [ℓ]*((O))`) exists. -/
theorem pullbackDiv_sub_isPrincipal
    [IsIntegrallyClosed (⟨W⟩ : Curves.SmoothPlaneCurve F).CoordinateRing]
    (f : W.Point →+ W.Point) (h_ker : Finite f.ker) {T P₀ : W.Point}
    (hP₀ : f P₀ = T) (hann : Nat.card f.ker • P₀ = 0) :
    (⟨W⟩ : Curves.SmoothPlaneCurve F).ProjIsPrincipal
      (pullbackDiv f h_ker T - pullbackDiv f h_ker 0) := by
  refine projIsPrincipal_of_degZero_of_sigma_eq_zero _ ?_ ?_
  · rw [← Curves.ProjectiveDivisor.degreeHom_apply, map_sub,
      Curves.ProjectiveDivisor.degreeHom_apply, Curves.ProjectiveDivisor.degreeHom_apply,
      degree_pullbackDiv f h_ker hP₀, degree_pullbackDiv f h_ker (map_zero f), sub_self]
  · rw [Curves.projectiveDivisorSum_sub, sigma_pullbackDiv_sub f h_ker hP₀, hann]

end HasseWeil.WeilPairing
