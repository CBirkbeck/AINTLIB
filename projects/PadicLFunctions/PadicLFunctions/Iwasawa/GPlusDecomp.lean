/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.PadicExp
import PadicLFunctions.Iwasawa.PlusPart
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The group-theoretic decomposition of `GPlus` for the carrier bridge

For odd `p`, this file builds two structural isomorphisms underlying the
identification `Λ(𝒢⁺) = Λ(Δ × Γ)` used downstream by the carrier bridge:

* **(A) `gammaLogBundle`** — the pro-cyclic 1-units
  `Γ = {u : ℤ_[p]ˣ // (u : ℤ_[p]) ∈ 1 + pℤ_p}` are continuously monoid-isomorphic
  to the *additive* group `ℤ_[p]`. Packaged as the data of two continuous maps
  `logCM : C(Γ, ℤ_[p])`, `expCM : C(ℤ_[p], Γ)` with the homomorphism and inverse
  equations. The maps are the integral `p`-adic logarithm / exponential of
  `PadicExp.lean` (`pZpLog`/`pZpExp`), rescaled by `p` so that the additive
  parameter runs over all of `ℤ_[p]`: `expCM a = exp(p·a)`, `logCM u = log(u)/p`.

* **(B) `gplusEquiv`** — the continuous monoid isomorphism
  `PadicMeasure.GPlus p ≃ₜ* (Δ × Γ)`, where `Δ` is the finite torsion part.
  The Teichmüller decomposition `ℤ_[p]ˣ ≅ μ_{p−1} × Γ` (`x = ω(x)·⟨x⟩`,
  `Branches.lean`) and the collapse `GPlus p = ℤ_[p]ˣ/{±1}` with `−1 ∈ μ_{p−1}`
  give `GPlus p ≅ (μ_{p−1}/{±1}) × Γ = Δ × Γ`.
-/

open PadicLFunctions PadicInt

noncomputable section

namespace PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## Division by `p`, total via `ℚ_p`, integral on `pℤ_p` -/

/-- Division by `p`, made total on `ℤ_[p]` via the quotient in `ℚ_[p]` with junk
value `0` off the integral branch. On `pℤ_p` it is the genuine division (its two
algebraic specs below). -/
def divP (x : ℤ_[p]) : ℤ_[p] :=
  if h : ‖(x : ℚ_[p]) / (p : ℚ_[p])‖ ≤ 1 then ⟨(x : ℚ_[p]) / (p : ℚ_[p]), h⟩ else 0

/-- On `pℤ_p`, `(divP x : ℚ_[p]) = x / p`. -/
theorem divP_coe {t : ℤ_[p]} (ht : t ∈ Ideal.span {(p : ℤ_[p])}) :
    ((divP p t : ℤ_[p]) : ℚ_[p]) = (t : ℚ_[p]) / (p : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ht
  have hle : ‖((c * (p : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p])‖ ≤ 1 := by
    push_cast; rw [mul_div_assoc, div_self hp0, mul_one]; exact_mod_cast c.2
  rw [divP, dif_pos hle]

/-- On `pℤ_p`, `p · divP x = x`. -/
theorem mul_divP {t : ℤ_[p]} (ht : t ∈ Ideal.span {(p : ℤ_[p])}) :
    (p : ℤ_[p]) * divP p t = t := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply PadicInt.ext
  rw [PadicInt.coe_mul, divP_coe p ht]
  push_cast
  field_simp

/-- `divP (p · a) = a`. -/
@[simp]
theorem divP_mul_self (a : ℤ_[p]) : divP p ((p : ℤ_[p]) * a) = a := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  apply PadicInt.ext
  rw [divP_coe p (Ideal.mem_span_singleton'.2 ⟨a, by ring⟩)]
  push_cast
  field_simp

/-- `divP` is additive on `pℤ_p`. -/
theorem divP_sub {z w : ℤ_[p]} (hz : z ∈ Ideal.span {(p : ℤ_[p])})
    (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
    divP p z - divP p w = divP p (z - w) := by
  apply PadicInt.ext
  rw [PadicInt.coe_sub, divP_coe p hz, divP_coe p hw, divP_coe p (Ideal.sub_mem _ hz hw),
    PadicInt.coe_sub]
  ring

/-- On `pℤ_p`, `‖divP t‖ = p · ‖t‖`. -/
theorem norm_divP {t : ℤ_[p]} (ht : t ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖divP p t‖ = (p : ℝ) * ‖t‖ := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [PadicInt.norm_def, divP_coe p ht, norm_div, Padic.norm_p, ← PadicInt.norm_def]
  field_simp

/-! ## The integral `p`-adic exponential / logarithm as group maps -/

/-- `pZpLog` is multiplicative on `1 + pℤ_p` (`padicLog_mul` over `ℚ_p`). -/
theorem pZpLog_mul (hp2 : p ≠ 2) {x y : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpLog p (x * y) = pZpLog p x + pZpLog p y := by
  have hxy : x * y - 1 ∈ Ideal.span {(p : ℤ_[p])} := PadicInt.mul_sub_one_mem p hx hy
  apply PadicInt.ext
  rw [PadicInt.coe_add, pZpLog_coe p hp2 hxy, pZpLog_coe p hp2 hx, pZpLog_coe p hp2 hy,
    PadicInt.coe_mul]
  have hballx : InExpBall p ((x : ℚ_[p]) - 1) := by
    rw [show ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
    exact inExpBall_of_mem_span p hp2 hx
  have hbally : InExpBall p ((y : ℚ_[p]) - 1) := by
    rw [show ((y : ℚ_[p]) - 1) = ((y - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
    exact inExpBall_of_mem_span p hp2 hy
  rw [padicLog_mul (L := ℚ_[p]) p hballx hbally]

/-- `pZpLog 1 = 0`. -/
theorem pZpLog_one (hp2 : p ≠ 2) : pZpLog p (1 : ℤ_[p]) = 0 := by
  have h1 : (1 : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])} := by simp
  have h := pZpLog_mul p hp2 h1 h1
  rw [mul_one] at h
  have h2 : pZpLog p 1 + pZpLog p 1 = pZpLog p 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- **The p-adic logarithm is an isometry (shifted) on `1 + pℤ_p`**: `‖pZpLog x‖ = ‖x − 1‖`.
The integral incarnation of `norm_padicLog`. -/
theorem norm_pZpLog (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖pZpLog p x‖ = ‖x - 1‖ := by
  have hxsub : ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, PadicInt.coe_one]
  have hball : InExpBall p ((x : ℚ_[p]) - 1) := by rw [hxsub]; exact inExpBall_of_mem_span p hp2 hx
  rw [PadicInt.norm_def, pZpLog_coe p hp2 hx, norm_padicLog (L := ℚ_[p]) p hball, hxsub,
    ← PadicInt.norm_def]

/-- `pZpExp` of a sum is the product on `pℤ_p` (`padicExp_add` over `ℚ_p`). -/
theorem pZpExp_add (hp2 : p ≠ 2) {x y : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])})
    (hy : y ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpExp p (x + y) = pZpExp p x * pZpExp p y := by
  apply PadicInt.ext
  rw [PadicInt.coe_mul, pZpExp_coe p hp2 (Ideal.add_mem _ hx hy), pZpExp_coe p hp2 hx,
    pZpExp_coe p hp2 hy, PadicInt.coe_add,
    padicExp_add (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hx)
      (inExpBall_of_mem_span p hp2 hy)]

/-- `exp(log x) = x` on `1 + pℤ_p`. -/
theorem pZpExp_pZpLog (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpExp p (pZpLog p x) = x := by
  have hmem := pZpLog_mem p hp2 hx
  apply PadicInt.ext
  rw [pZpExp_coe p hp2 hmem, pZpLog_coe p hp2 hx]
  refine padicExp_padicLog (L := ℚ_[p]) p ?_
  rw [show ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
  exact inExpBall_of_mem_span p hp2 hx

/-- `log(exp y) = y` on `pℤ_p`. -/
theorem pZpLog_pZpExp (hp2 : p ≠ 2) {y : ℤ_[p]} (hy : y ∈ Ideal.span {(p : ℤ_[p])}) :
    pZpLog p (pZpExp p y) = y := by
  have hmem := pZpExp_sub_one_mem p hp2 hy
  apply PadicInt.ext
  rw [pZpLog_coe p hp2 hmem, pZpExp_coe p hp2 hy]
  exact padicLog_padicExp (L := ℚ_[p]) p (inExpBall_of_mem_span p hp2 hy)

/-- `pZpExp 0 = 1` (`exp 0 = 1`). -/
theorem pZpExp_zero (hp2 : p ≠ 2) : pZpExp p (0 : ℤ_[p]) = 1 := by
  apply PadicInt.ext
  rw [pZpExp_coe p hp2 (Ideal.zero_mem _), PadicInt.coe_zero, padicExp_zero, PadicInt.coe_one]

end PadicLFunctions
