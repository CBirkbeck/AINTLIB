/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic

/-!
# Route 2A — the Weil-pairing determinant identity (Silverman III.8.6, abstract finite-level core)

The linear-algebra heart of Prop 8.6 `det(φ_ℓ) = deg φ`, isolated from the pairing construction.

On a rank-2 space the (Weil) pairing is the standard symplectic form `J = [[0,1],[-1,0]]`, and
the adjoint property `e(φS,T)=e(S,φ̂T)` says `φᵀ J = J φ̂`. Combined with the dual relation
`φ̂φ = [deg]` (`= d • 1` on `E[ℓ] ≅ 𝔽_ℓ²`), the **symplectic identity** `φᵀ J φ = (det φ) • J`
forces `det φ = d`.

This is the residual interface for the finite-level Weil-pairing route: once the pairing
construction supplies, on `E[ℓ] ≅ 𝔽_ℓ²`, the Frobenius matrix `φ`, its symplectic adjoint `φ̂`
(from the pairing adjoint), and `φ̂φ = (deg φ) • 1`, this gives `det(φ|E[ℓ]) = deg φ` in `𝔽_ℓ` — the
per-`ℓ`
input the shipped `Reduction`/discriminant machinery consumes.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.8.6 (`det φ_ℓ = deg φ` via the Weil
pairing); the symplectic-adjoint formulation of the pairing's adjoint property (III.8.2/8.3).
-/

namespace HasseWeil.WeilPairing

open Matrix

/-- The standard symplectic form matrix `J = [[0,1],[-1,0]]` on `Fin 2`. -/
def symJ (F : Type*) [CommRing F] : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

/-- `symJ` is nonzero in its `(0,1)` entry, so it cancels from a scalar action: `a • J = b • J`
forces `a = b`. -/
private theorem symJ_smul_inj {F : Type*} [CommRing F] {a b : F}
    (h : a • symJ F = b • symJ F) : a = b := by
  simpa [symJ, Matrix.smul_apply] using congrFun (congrFun h 0) 1

/-- **Symplectic determinant identity:** `φᵀ J φ = (det φ) • J` for any `2×2` matrix `φ`. -/
theorem transpose_mul_symJ_mul {F : Type*} [CommRing F] (φ : Matrix (Fin 2) (Fin 2) F) :
    φᵀ * symJ F * φ = φ.det • symJ F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symJ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.transpose_apply, Matrix.smul_apply] <;> ring

/-- **Weil-pairing determinant (Silverman III.8.6, abstract finite-level form).**
If `ψ` is the symplectic adjoint of `φ` (`φᵀ J = J ψ`, the matrix form of `e(φS,T)=e(S,ψT)`) and
`ψ φ = d • 1` (the dual relation `φ̂φ = [deg]`), then `det φ = d`. -/
theorem det_eq_of_symplectic_adjoint {F : Type*} [CommRing F]
    {φ ψ : Matrix (Fin 2) (Fin 2) F} {d : F}
    (hadj : φᵀ * symJ F = symJ F * ψ)
    (hψφ : ψ * φ = d • (1 : Matrix (Fin 2) (Fin 2) F)) :
    φ.det = d := by
  have h1 : φᵀ * symJ F * φ = d • symJ F := by
    rw [hadj, Matrix.mul_assoc, hψφ, Matrix.mul_smul, Matrix.mul_one]
  exact symJ_smul_inj (by rw [← transpose_mul_symJ_mul, h1])

/-! ### The scaling form of Prop 8.6 (additivity-free — the load-bearing residual interface)

The adjoint formulation above secretly routes through the trace relation `π + π̂ = [t]`, whose
geometric content is dual **additivity** `(φ+ψ)̂ = φ̂ + ψ̂` (Silverman III.6.2c) — the very fact
that has no elementary characteristic-`p` proof and stalled the divisor route (Route 1).

The Weil pairing **avoids** additivity through its scaling property
`e_ℓ(φS, φT) = e_ℓ(S,T)^{deg φ}`, which holds for **every** isogeny `φ` individually (Silverman
III.8.6, the heart of Prop 8.6). In matrix form on `E[ℓ] ≅ 𝔽_ℓ²` this is `φᵀ J φ = (deg φ) • J`;
combined with the universal `φᵀ J φ = (det φ) • J` it forces `det φ = deg φ` — per isogeny, with no
adjoint, no trace, and no additivity. This is the interface the pairing construction discharges. -/

/-- **Weil-pairing determinant, scaling form (Silverman III.8.6).** If `φᵀ J φ = d • J` (the matrix
form of the pairing scaling `e(φS,φT) = e(S,T)^d` with `d = deg φ`), then `det φ = d`. Holds for any
single `φ` — no adjoint, no dual-additivity hypothesis. -/
theorem det_eq_of_symplectic_scaling {F : Type*} [CommRing F]
    {φ : Matrix (Fin 2) (Fin 2) F} {d : F}
    (hscale : φᵀ * symJ F * φ = d • symJ F) : φ.det = d :=
  symJ_smul_inj (by rw [← transpose_mul_symJ_mul]; exact hscale)

/-- **The three Frobenius det facts from the per-isogeny scaling property** (additivity-free). Given
the Weil-pairing scaling `φᵀ J φ = (deg φ) • J` for each of `π`, `1−π`, `rπ−s` (whose matrices on
`E[ℓ] ≅ 𝔽_ℓ²` are `M`, `1−M`, `r•M − s•1` since the `ℓ`-adic representation is a ring map), the
three det facts `det M = q (= deg π)`, `det(1−M) = dE (= deg(1−π) = #E)`, and
`det(r•M − s•1) = D (= deg(rπ−s))` all hold — with the **geometric** degrees on the right (each
manifestly `≥ 0`). -/
theorem frob_det_data_of_scaling {F : Type*} [CommRing F]
    {M : Matrix (Fin 2) (Fin 2) F} {q dE r s D : F}
    (hπ : Mᵀ * symJ F * M = q • symJ F)
    (h1 : (1 - M)ᵀ * symJ F * (1 - M) = dE • symJ F)
    (hrs : (r • M - s • (1 : Matrix (Fin 2) (Fin 2) F))ᵀ * symJ F
      * (r • M - s • (1 : Matrix (Fin 2) (Fin 2) F)) = D • symJ F) :
    M.det = q ∧ (1 - M).det = dE ∧ (r • M - s • (1 : Matrix (Fin 2) (Fin 2) F)).det = D :=
  ⟨det_eq_of_symplectic_scaling hπ, det_eq_of_symplectic_scaling h1,
    det_eq_of_symplectic_scaling hrs⟩

/-! ### From the Frobenius adjoint / norm / trace to the three det facts

The Weil pairing supplies, for the **generator** `π` on `E[ℓ] ≅ 𝔽_ℓ²`, three matrix facts about
`M = ρ_ℓ(π)` and `Mhat = ρ_ℓ(π̂)`:
* the symplectic adjoint `Mᵀ J = J Mhat` (the matrix form of `e(πS,T) = e(S,π̂T)`),
* the norm `Mhat M = q • 1` (the dual relation `π̂π = [deg π] = [q]`),
* the trace `M + Mhat = t • 1` (`π + π̂ = [t]`, `t = 1 + q − #E`).

From these, **every** `(r,s)`-linear combination `a•M + b•1` of Frobenius has its symplectic
adjoint `a•Mhat + b•1` and norm `(a•Mhat+b•1)(a•M+b•1) = (a²q + abt + b²)•1` forced by linearity,
so `det(a•M + b•1) = a²q + abt + b²` by `det_eq_of_symplectic_adjoint`.  Specialising `(a,b)` to
`(1,0)`, `(−1,1)`, `(r,−s)` yields the three det facts `det M = q`, `det(1−M) = q+1−t = #E`, and
`det(r•M − s•1) = q r² − t r s + s²` that the `Reduction` / `Assembly` interface consumes. -/

/-- **The Frobenius pencil determinant.** Given the symplectic adjoint `Mᵀ J = J Mhat`, the norm
`Mhat M = q • 1`, and the trace `M + Mhat = t • 1`, every linear combination has
`det(a•M + b•1) = a²·q + a·b·t + b²`. This is the matrix-level evaluation of the characteristic
form of Frobenius on `E[ℓ]` (Silverman III.8.6 applied to `a·π + b`). -/
theorem det_smul_add_smul_one_eq {F : Type*} [CommRing F]
    {M Mhat : Matrix (Fin 2) (Fin 2) F} {q t : F}
    (hadj : Mᵀ * symJ F = symJ F * Mhat)
    (hnorm : Mhat * M = q • (1 : Matrix (Fin 2) (Fin 2) F))
    (htr : M + Mhat = t • (1 : Matrix (Fin 2) (Fin 2) F)) (a b : F) :
    (a • M + b • (1 : Matrix (Fin 2) (Fin 2) F)).det = a ^ 2 * q + a * b * t + b ^ 2 := by
  apply det_eq_of_symplectic_adjoint (ψ := a • Mhat + b • 1)
  · -- symplectic adjoint of `a•M + b•1` is `a•Mhat + b•1`, by linearity from `hadj`
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hadj]
  · -- norm `(a•Mhat + b•1)(a•M + b•1) = (a²q + abt + b²)•1`, from `hnorm` and `htr`
    have key : (a • Mhat + b • (1 : Matrix (Fin 2) (Fin 2) F)) * (a • M + b • 1)
        = (a * a) • (Mhat * M) + (a * b) • (M + Mhat)
          + (b * b) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      match_scalars <;> ring
    rw [key, hnorm, htr]
    module

/-- **The three Frobenius det facts** (the `Reduction` / `Assembly` interface), packaged from the
symplectic adjoint, norm `π̂π = [q]`, and trace `π + π̂ = [t]` of Frobenius on `E[ℓ] ≅ 𝔽_ℓ²`. For
every `(r,s)`: `det M = q`, `det(1 − M) = q+1−t (= #E)`, and
`det(r•M − s•1) = q r² − t r s + s²`. -/
theorem frob_det_data_of_adjoint_norm_trace {F : Type*} [CommRing F]
    {M Mhat : Matrix (Fin 2) (Fin 2) F} {q t : F}
    (hadj : Mᵀ * symJ F = symJ F * Mhat)
    (hnorm : Mhat * M = q • (1 : Matrix (Fin 2) (Fin 2) F))
    (htr : M + Mhat = t • (1 : Matrix (Fin 2) (Fin 2) F)) (r s : F) :
    M.det = q ∧ (1 - M).det = q + 1 - t ∧
      (r • M - s • (1 : Matrix (Fin 2) (Fin 2) F)).det = q * r ^ 2 - t * r * s + s ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · -- `det M = q`  (specialise `(a,b) = (1,0)`)
    have h := det_smul_add_smul_one_eq hadj hnorm htr 1 0
    rw [one_smul, zero_smul, add_zero] at h
    simpa using h
  · -- `det(1 − M) = q+1−t`  (specialise `(a,b) = (−1,1)`)
    have e : (1 : Matrix (Fin 2) (Fin 2) F) - M = (-1 : F) • M + (1 : F) • 1 := by
      module
    rw [e, det_smul_add_smul_one_eq hadj hnorm htr (-1) 1]; ring
  · -- `det(r•M − s•1) = q r² − t r s + s²`  (specialise `(a,b) = (r,−s)`)
    have e : r • M - s • (1 : Matrix (Fin 2) (Fin 2) F) = r • M + (-s) • 1 := by
      module
    rw [e, det_smul_add_smul_one_eq hadj hnorm htr r (-s)]; ring

/-! ### Module-level connector: `LinearMap.det` from the symplectic scaling

The finite-level Weil pairing acts on `E[ℓ]` as a rank-2 module with Frobenius a **linear map**
`φ : V →ₗ V` (not a priori a matrix). Choosing a symplectic basis `b` (where the additive Weil
pairing is `symJ`), the scaling `e(φx,φy) = e(x,y)^{deg φ}` becomes
`(toMatrix b b φ)ᵀ J (toMatrix b b φ) = (deg φ) • J`, and `LinearMap.det φ = deg φ` follows. This
is the natural form of Prop 8.6 in terms of the linear endomorphism on `E[ℓ]`. -/

/-- **`LinearMap.det` from the symplectic scaling.** For a rank-2 module `V` with basis `b`, a
linear endomorphism `φ` whose matrix `M = toMatrix b b φ` satisfies the symplectic scaling
`Mᵀ J M = d • J`, has `LinearMap.det φ = d`. The bridge from the `E[ℓ]`-as-module Frobenius to the
matrix residual `frob_det_data_of_scaling`. -/
theorem linearMap_det_eq_of_symplectic_scaling {R : Type*} [CommRing R]
    {V : Type*} [AddCommGroup V] [Module R V] (b : Module.Basis (Fin 2) R V)
    (φ : V →ₗ[R] V) {d : R}
    (hscale : (LinearMap.toMatrix b b φ)ᵀ * symJ R * LinearMap.toMatrix b b φ = d • symJ R) :
    LinearMap.det φ = d := by
  rw [← LinearMap.det_toMatrix b φ]
  exact det_eq_of_symplectic_scaling hscale

/-! ### Module-level Prop 8.6: `det φ = d` from a scaled alternating form

The natural form of `det φ = deg φ` for the Weil pairing: the pairing is an **alternating bilinear
form** `ω` on `E[ℓ]` (after additivising `μ_ℓ ≅ 𝔽_ℓ`), not a matrix. On a rank-2 space, any
endomorphism `φ` scales `ω` by `det φ` (the `Λ²` action: `ω(φx, φy) = (det φ)·ω(x,y)`), so the Weil
scaling `ω(φx, φy) = (deg φ)·ω(x,y)` forces `det φ = deg φ` — with no basis choice exposed to the
caller. This is what the finite-level pairing construction discharges directly. -/

/-- **The `Λ²` scaling identity (rank 2):** for an alternating bilinear form `ω` and any `φ`,
`ω(φ(b 0), φ(b 1)) = (det φ)·ω(b 0, b 1)`. -/
theorem alternating_comp_eq_det_smul {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F)
    (halt : ∀ x, ω x x = 0) (φ : V →ₗ[F] V) :
    ω (φ (b 0)) (φ (b 1)) = LinearMap.det φ * ω (b 0) (b 1) := by
  have hrepr : ∀ j : Fin 2, φ (b j)
      = (LinearMap.toMatrix b b φ) 0 j • b 0 + (LinearMap.toMatrix b b φ) 1 j • b 1 := by
    intro j
    have hsum := (b.sum_repr (φ (b j))).symm
    rw [Fin.sum_univ_two] at hsum
    simpa [LinearMap.toMatrix_apply] using hsum
  have hskew : ω (b 1) (b 0) = -ω (b 0) (b 1) := by
    have h := halt (b 0 + b 1)
    simp only [map_add, LinearMap.add_apply, halt (b 0), halt (b 1), zero_add, add_zero] at h
    linear_combination h
  rw [hrepr 0, hrepr 1]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    halt (b 0), halt (b 1), hskew, mul_zero, add_zero, zero_add]
  rw [← LinearMap.det_toMatrix b φ, Matrix.det_fin_two]
  ring

/-- **Module-level Prop 8.6 (Silverman III.8.6):** for a rank-2 space `V`, a **nondegenerate**
alternating bilinear form `ω` (witnessed by `ω(b 0, b 1) ≠ 0`), and `φ` with the scaling
`ω(φx, φy) = d · ω(x, y)`, the determinant is `LinearMap.det φ = d`. The additivised Weil pairing
supplies `ω` and the scaling with `d = deg φ`. -/
theorem det_eq_of_alternating_scaling {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F)
    (halt : ∀ x, ω x x = 0) (hnd : ω (b 0) (b 1) ≠ 0)
    (φ : V →ₗ[F] V) {d : F} (hscale : ∀ x y, ω (φ x) (φ y) = d * ω x y) :
    LinearMap.det φ = d := by
  have key := alternating_comp_eq_det_smul b ω halt φ
  rw [hscale] at key
  exact mul_right_cancel₀ hnd key.symm

/-- **The three Frobenius det facts from the pairing form** (the form-level `Reduction` interface).
Given a rank-2 space with a nondegenerate alternating form `ω` (the additivised Weil pairing),
Frobenius `φ`, and the per-isogeny scalings `ω(ψ x, ψ y) = (deg ψ)·ω(x,y)` for `ψ ∈ {π, 1−π, rπ−s}`
(`= φ, id−φ, r•φ−s•id`), the matrix `M = toMatrix b φ` satisfies `det M = q`, `det(1−M) = dE`, and
`det(r•M − s•1) = D` — with the geometric degrees `q = deg π`, `dE = deg(1−π) = #E`,
`D = deg(rπ−s)`. This is what the AG Weil-pairing construction discharges; it feeds
`Reduction.frob_det_congruence`. -/
theorem frob_det_data_of_pairing_form {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (b : Module.Basis (Fin 2) F V) (ω : V →ₗ[F] V →ₗ[F] F)
    (halt : ∀ x, ω x x = 0) (hnd : ω (b 0) (b 1) ≠ 0)
    (φ : V →ₗ[F] V) {q dE r s D : F}
    (hπ : ∀ x y, ω (φ x) (φ y) = q * ω x y)
    (h1 : ∀ x y, ω ((LinearMap.id - φ : V →ₗ[F] V) x)
        ((LinearMap.id - φ : V →ₗ[F] V) y) = dE * ω x y)
    (hrs : ∀ x y, ω ((r • φ - s • LinearMap.id : V →ₗ[F] V) x)
        ((r • φ - s • LinearMap.id : V →ₗ[F] V) y) = D * ω x y) :
    (LinearMap.toMatrix b b φ).det = q ∧
      (1 - LinearMap.toMatrix b b φ).det = dE ∧
      (r • LinearMap.toMatrix b b φ - s • 1).det = D := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.det_toMatrix]
    exact det_eq_of_alternating_scaling b ω halt hnd φ hπ
  · have hM : (1 : Matrix (Fin 2) (Fin 2) F) - LinearMap.toMatrix b b φ
        = LinearMap.toMatrix b b (LinearMap.id - φ) := by
      rw [map_sub, LinearMap.toMatrix_id]
    rw [hM, LinearMap.det_toMatrix]
    exact det_eq_of_alternating_scaling b ω halt hnd _ h1
  · have hM : r • LinearMap.toMatrix b b φ - s • (1 : Matrix (Fin 2) (Fin 2) F)
        = LinearMap.toMatrix b b (r • φ - s • (LinearMap.id : V →ₗ[F] V)) := by
      rw [map_sub, map_smul, map_smul, LinearMap.toMatrix_id]
    rw [hM, LinearMap.det_toMatrix]
    exact det_eq_of_alternating_scaling b ω halt hnd _ hrs

end HasseWeil.WeilPairing
