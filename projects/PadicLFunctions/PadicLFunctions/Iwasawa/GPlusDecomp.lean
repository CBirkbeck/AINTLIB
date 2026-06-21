/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.PadicExp
import PadicLFunctions.Iwasawa.PlusPart
import PadicLFunctions.Interpolation.Branches
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.ContinuousMap.Units

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

/-- `divP` is additive on `pℤ_p`. -/
theorem divP_add {z w : ℤ_[p]} (hz : z ∈ Ideal.span {(p : ℤ_[p])})
    (hw : w ∈ Ideal.span {(p : ℤ_[p])}) :
    divP p (z + w) = divP p z + divP p w := by
  apply PadicInt.ext
  rw [PadicInt.coe_add, divP_coe p (Ideal.add_mem _ hz hw), divP_coe p hz, divP_coe p hw,
    PadicInt.coe_add]; ring

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

/-- **The p-adic logarithm is a difference-isometry on `1 + pℤ_p`**: `‖pZpLog x − pZpLog y‖ = ‖x − y‖`.
Since `padicExp` is an isometry on the convergence ball (`norm_padicExp_sub_padicExp`) and `padicLog`
is its two-sided inverse there (`padicExp_padicLog`), the logarithm is an isometry too — no `ℤ_p`-unit
inverses needed.  This gives (uniform) continuity of `logCM` for the `Γ ≅ ℤ_p` carrier-bridge factor. -/
theorem norm_pZpLog_sub (hp2 : p ≠ 2) {x y : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])})
    (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖pZpLog p x - pZpLog p y‖ = ‖x - y‖ := by
  have hballx : InExpBall p ((x : ℚ_[p]) - 1) := by
    rw [show ((x : ℚ_[p]) - 1) = ((x - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
    exact inExpBall_of_mem_span p hp2 hx
  have hbally : InExpBall p ((y : ℚ_[p]) - 1) := by
    rw [show ((y : ℚ_[p]) - 1) = ((y - 1 : ℤ_[p]) : ℚ_[p]) by push_cast; ring]
    exact inExpBall_of_mem_span p hp2 hy
  have ha : InExpBall p (padicLog p (x : ℚ_[p])) := by rw [InExpBall, norm_padicLog p hballx]; exact hballx
  have hb : InExpBall p (padicLog p (y : ℚ_[p])) := by rw [InExpBall, norm_padicLog p hbally]; exact hbally
  have key := norm_padicExp_sub_padicExp p ha hb
  rw [padicExp_padicLog p hballx, padicExp_padicLog p hbally] at key
  rw [PadicInt.norm_def, PadicInt.coe_sub, pZpLog_coe p hp2 hx, pZpLog_coe p hp2 hy, ← key,
    PadicInt.norm_def, PadicInt.coe_sub]

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

/-! ## The compact group `Γ` of principal `1`-units -/

/-- The subgroup of **principal `1`-units** `{u : ℤ_[p]ˣ // (u : ℤ_[p]) - 1 ∈ pℤ_p}`.
This is the pro-cyclic factor `Γ` of `ℤ_[p]ˣ` (for odd `p`). It is closed under `*`
(`PadicInt.mul_sub_one_mem`) and `⁻¹` (`u⁻¹ - 1 = -u⁻¹·(u-1)`). -/
def OneUnits : Subgroup ℤ_[p]ˣ where
  carrier := {u | ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    simpa only [Set.mem_setOf_eq, Units.val_mul] using PadicInt.mul_sub_one_mem p hu hv
  inv_mem' {u} hu := by
    simp only [Set.mem_setOf_eq] at hu ⊢
    have hval : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((u : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hrw : ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1
        = -((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (((u : ℤ_[p]ˣ) : ℤ_[p]) - 1) := by
      rw [neg_mul, mul_sub, mul_one, hval]; ring
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hu

/-- `Γ` — the principal `1`-units as a type. -/
abbrev Gamma : Type _ := OneUnits p

/-- The carrier of `OneUnits` is **closed** in `ℤ_[p]ˣ`: it is the preimage of the
closed ideal `pℤ_p` (closed since `ℤ_[p]` is a compact Hausdorff Noetherian topological
ring, `IsNoetherianRing.isClosed_ideal`) under the continuous map `u ↦ (u : ℤ_[p]) - 1`. -/
theorem isClosed_oneUnits : IsClosed (OneUnits p : Set ℤ_[p]ˣ) := by
  have hcont : Continuous (fun u : ℤ_[p]ˣ => ((u : ℤ_[p]ˣ) : ℤ_[p]) - 1) :=
    (Units.continuous_val).sub continuous_const
  have hclosed : IsClosed (↑(Ideal.span {(p : ℤ_[p])}) : Set ℤ_[p]) := inferInstance
  exact hclosed.preimage hcont

/-- `Γ` is a **compact space**: it is a closed subgroup of the compact group `ℤ_[p]ˣ`
(`Units.instCompactSpaceOfT1SpaceOfContinuousMul` makes `ℤ_[p]ˣ` compact). -/
instance instCompactSpaceGamma : CompactSpace (Gamma p) :=
  isCompact_iff_compactSpace.mp ((isClosed_oneUnits p).isCompact)

/-! ## The Teichmüller splitting `ℤ_[p]ˣ ≅ μ_{p−1} × Γ` (the `gplusEquiv` foundation) -/

/-- The **principal (`1`-unit) part** `u · ω(u)⁻¹` lies in `Γ`: since `ω(u) ≡ u (mod p)`
(`teichmullerFun_sub_self_mem`), `u·ω(u)⁻¹ − 1 = (u − ω(u))·ω(u)⁻¹ ∈ pℤ_p`. -/
theorem oneUnitPart_mem (u : ℤ_[p]ˣ) : (u * (teichmuller p u)⁻¹) ∈ OneUnits p := by
  show ((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}
  have ht : ((teichmuller p u : ℤ_[p]ˣ) : ℤ_[p]) = teichmullerFun p (u : ℤ_[p]) := teichmuller_coe p u
  have hinv : ((teichmuller p u : ℤ_[p]ˣ) : ℤ_[p]) * (((teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1
      = (((u : ℤ_[p]ˣ) : ℤ_[p]) - teichmullerFun p (u : ℤ_[p]))
        * (((teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [Units.val_mul, sub_mul,
      show ((u : ℤ_[p]ˣ) : ℤ_[p]) * (((teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
          = ((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) from by rw [Units.val_mul], ← ht, hinv]
  rw [key]
  exact Ideal.mul_mem_right _ _ (by
    rw [show ((u : ℤ_[p]ˣ) : ℤ_[p]) - teichmullerFun p (u : ℤ_[p])
        = -(teichmullerFun p (u : ℤ_[p]) - (u : ℤ_[p])) from by ring]
    exact Submodule.neg_mem _ (teichmullerFun_sub_self_mem p (u : ℤ_[p])))

/-- The **principal-part projection** `ℤ_[p]ˣ →* Γ`, `u ↦ u · ω(u)⁻¹` — a monoid hom because `ω`
is (`teichmuller`) and `ℤ_[p]ˣ` is commutative. -/
noncomputable def gammaProj : ℤ_[p]ˣ →* Gamma p where
  toFun u := ⟨u * (teichmuller p u)⁻¹, oneUnitPart_mem p u⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' u v := by
    apply Subtype.ext
    show (u * v) * (teichmuller p (u * v))⁻¹
      = (u * (teichmuller p u)⁻¹) * (v * (teichmuller p v)⁻¹)
    rw [map_mul, _root_.mul_inv, mul_mul_mul_comm]

/-- `ω` is trivial on `1`-units: `g ≡ 1 (mod p) ⟹ ω(g) = 1`. -/
theorem teichmuller_oneUnit (g : ℤ_[p]ˣ) (hg : g ∈ OneUnits p) : teichmuller p g = 1 := by
  apply Units.ext
  rw [teichmuller_coe, Units.val_one]
  show teichmullerFun p ((g : ℤ_[p]ˣ) : ℤ_[p]) = 1
  rw [teichmullerFun_eq_of_sub_mem p (y := 1) hg]
  show teichmullerZMod p (toZMod 1) = 1
  rw [map_one, map_one]

/-- `ω` is idempotent: `ω(ω(u)) = ω(u)`. -/
theorem teichmuller_idem (u : ℤ_[p]ˣ) : teichmuller p (teichmuller p u) = teichmuller p u := by
  apply Units.ext
  rw [teichmuller_coe, teichmuller_coe]
  show teichmullerFun p (teichmullerFun p ((u : ℤ_[p]ˣ) : ℤ_[p]))
    = teichmullerFun p ((u : ℤ_[p]ˣ) : ℤ_[p])
  rw [teichmullerFun, teichmullerFun, toZMod_teichmullerZMod]

/-- **The Teichmüller splitting** `ℤ_[p]ˣ ≃* μ_{p−1} × Γ` (`μ_{p−1} = range ω`, `Γ` the `1`-units):
`u ↦ (ω(u), u·ω(u)⁻¹)`, inverse `(t, g) ↦ t·g`.  Left inverse: `ω(u)·(u·ω(u)⁻¹) = u`; right inverse:
`ω(t·g) = ω(t)·ω(g) = t·1 = t` (`teichmuller_idem`, `teichmuller_oneUnit`) and the `Γ`-part returns `g`. -/
noncomputable def unitsSplitEquiv : ℤ_[p]ˣ ≃* ((teichmuller p).range × Gamma p) where
  toFun u := (⟨teichmuller p u, u, rfl⟩, gammaProj p u)
  invFun tg := (tg.1 : ℤ_[p]ˣ) * (tg.2 : ℤ_[p]ˣ)
  left_inv u := by
    show (teichmuller p u : ℤ_[p]ˣ) * (u * (teichmuller p u)⁻¹) = u
    rw [mul_comm (teichmuller p u : ℤ_[p]ˣ), inv_mul_cancel_right]
  right_inv := by
    rintro ⟨⟨t, u, rfl⟩, g⟩
    have h1 : teichmuller p ((teichmuller p u : ℤ_[p]ˣ) * (g : ℤ_[p]ˣ)) = teichmuller p u := by
      rw [map_mul, teichmuller_idem, teichmuller_oneUnit p g g.2, mul_one]
    apply Prod.ext
    · apply Subtype.ext; exact h1
    · apply Subtype.ext
      show (teichmuller p u : ℤ_[p]ˣ) * (g : ℤ_[p]ˣ)
        * (teichmuller p ((teichmuller p u : ℤ_[p]ˣ) * (g : ℤ_[p]ˣ)))⁻¹ = (g : ℤ_[p]ˣ)
      rw [h1, mul_comm (teichmuller p u : ℤ_[p]ˣ) (g : ℤ_[p]ˣ), mul_inv_cancel_right]
  map_mul' u v := by
    apply Prod.ext
    · apply Subtype.ext; show teichmuller p (u * v) = _; rw [map_mul]; rfl
    · exact (gammaProj p).map_mul u v

/-- `ω(u)` depends only on `u mod p`: `ω(u) = teichmullerZMod (toZMod u)`. -/
theorem teichmuller_eq_teichmullerZMod_toZMod (u : ℤ_[p]ˣ) :
    ((teichmuller p u : ℤ_[p]ˣ) : ℤ_[p]) = teichmullerZMod p (toZMod ((u : ℤ_[p]ˣ) : ℤ_[p])) := by
  rw [teichmuller_coe]; rfl

/-- `μ_{p−1} = range ω` is **finite**: `ω` factors through the finite `ZMod p` (`u ↦ ω(u)` depends
only on `toZMod u`), so the map `range ω → ZMod p`, `t ↦ toZMod t`, is injective. -/
instance instFiniteTeichRange : Finite ((teichmuller p).range) := by
  apply Finite.of_injective
    (fun t : (teichmuller p).range => toZMod (((t : ℤ_[p]ˣ)) : ℤ_[p]))
  rintro ⟨t, u, rfl⟩ ⟨s, v, rfl⟩ h
  simp only at h
  apply Subtype.ext; apply Units.ext
  rw [teichmuller_eq_teichmullerZMod_toZMod, teichmuller_eq_teichmullerZMod_toZMod]
  congr 1
  rw [teichmuller_eq_teichmullerZMod_toZMod, teichmuller_eq_teichmullerZMod_toZMod,
    toZMod_teichmullerZMod, toZMod_teichmullerZMod] at h
  exact h

/-- `ω(-1) = -1` for odd `p`: `ω(-1)² = ω(1) = 1` forces `ω(-1) = ±1`, and `ω(-1) ≡ -1 (mod p)`
excludes `+1` (else `2 ∈ pℤ_p`, impossible for `p` odd). -/
theorem teichmuller_neg_one (hp2 : p ≠ 2) : teichmuller p (-1) = -1 := by
  apply Units.ext
  have hsq : ((teichmuller p (-1) : ℤ_[p]ˣ) : ℤ_[p]) * ((teichmuller p (-1) : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    rw [← Units.val_mul, ← map_mul]; norm_num
  have hred : ((teichmuller p (-1) : ℤ_[p]ˣ) : ℤ_[p]) - (-1 : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p])} := by
    have h := teichmullerFun_sub_self_mem p ((-1 : ℤ_[p]ˣ) : ℤ_[p])
    simpa [teichmuller_coe] using h
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exfalso
    rw [h1, show (1 : ℤ_[p]) - (-1) = 2 from by ring] at hred
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hred
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      rw [show (2 : ℤ_[p]) = ((2 : ℕ) : ℤ_[p]) from by norm_num]
      exact PadicInt.norm_natCast_eq_one_iff.mpr
        (Odd.coprime_two_right (hp.out.odd_of_ne_two hp2))
    have hplt : ‖(p : ℤ_[p])‖ < 1 := by
      rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    rw [hc, norm_mul] at h2
    have hlt : ‖(p : ℤ_[p])‖ * ‖c‖ < 1 :=
      calc ‖(p : ℤ_[p])‖ * ‖c‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (norm_nonneg _)
        _ = ‖(p : ℤ_[p])‖ := mul_one _
        _ < 1 := hplt
    rw [h2] at hlt; exact lt_irrefl 1 hlt
  · rw [h1, Units.val_neg, Units.val_one]

/-- The Teichmüller character `ω : ℤ_[p]ˣ →* ℤ_[p]ˣ` is **continuous** (its value is locally constant,
`isLocallyConstant_teichmullerFun`; continuity into the units is `Units.continuous_iff`). -/
theorem continuous_teichmuller : Continuous (teichmuller p) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · rw [show (Units.val ∘ (teichmuller p)) = fun u : ℤ_[p]ˣ => teichmullerFun p (u : ℤ_[p]) from
      funext fun u => teichmuller_coe p u]
    exact (isLocallyConstant_teichmullerFun p).continuous.comp Units.continuous_val
  · rw [show (fun u : ℤ_[p]ˣ => ((teichmuller p u)⁻¹ : ℤ_[p]ˣ).val)
        = fun u : ℤ_[p]ˣ => teichmullerFun p ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) from
      funext fun u => by rw [← map_inv, teichmuller_coe]]
    exact (isLocallyConstant_teichmullerFun p).continuous.comp
      (Units.continuous_val.comp continuous_inv)

/-- The principal-part projection `gammaProj : ℤ_[p]ˣ →* Γ` is **continuous** (`u ↦ u·ω(u)⁻¹`, both
factors continuous; continuity into the `Γ ⊆ ℤ_[p]ˣ` subtype via `Units.continuous_iff`). -/
theorem continuous_gammaProj : Continuous (gammaProj p) := by
  rw [continuous_induced_rng, Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous (fun u : ℤ_[p]ˣ => ((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]))
    simp only [Units.val_mul]
    exact (Units.continuous_val).mul ((Units.continuous_val.comp continuous_inv).comp
      (continuous_teichmuller p))
  · show Continuous (fun u : ℤ_[p]ˣ => (((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ))⁻¹ : ℤ_[p]ˣ).val)
    have : (fun u : ℤ_[p]ˣ => (((u * (teichmuller p u)⁻¹ : ℤ_[p]ˣ))⁻¹ : ℤ_[p]ˣ).val)
        = fun u : ℤ_[p]ˣ => ((teichmuller p u : ℤ_[p]ˣ) : ℤ_[p]) * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
      funext u; rw [_root_.mul_inv, inv_inv, Units.val_mul, mul_comm]
    rw [this]
    exact ((Units.continuous_val).comp (continuous_teichmuller p)).mul
      (Units.continuous_val.comp continuous_inv)

/-- `-1` as an element of `μ_{p−1} = range ω` (via `ω(-1) = -1`). -/
noncomputable def negOneT (hp2 : p ≠ 2) : (teichmuller p).range :=
  ⟨-1, -1, teichmuller_neg_one p hp2⟩

/-- **The finite torsion factor** `Δ = μ_{p−1} / ⟨-1⟩`. -/
abbrev Delta (hp2 : p ≠ 2) : Type _ :=
  (teichmuller p).range ⧸ Subgroup.zpowers (negOneT p hp2)

/-- `Δ` is a finite type (quotient of the finite `μ_{p−1}`). -/
noncomputable instance instFintypeDelta (hp2 : p ≠ 2) : Fintype (Delta p hp2) :=
  Fintype.ofFinite _

/-- `ℤ_[p]` has enough `(p−1)`-th roots of unity (a primitive one from Teichmüller,
`PadicInt.exists_primitiveRoot_card_sub_one`; the roots of an integral domain are cyclic).  This is
the source of the `μ_{(p−1)/2} ⊆ ℤ_[p]` needed for the isotypic completeness `∑_ω e_ω = 1` over `Δ`. -/
instance instHasEnoughRootsOfUnity : HasEnoughRootsOfUnity ℤ_[p] (p - 1) := by
  haveI : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  exact ⟨PadicInt.exists_primitiveRoot_card_sub_one p, rootsOfUnity.isCyclic ℤ_[p] (p - 1)⟩

/-- The exponent of `Δ` divides `p − 1`: every element `[t]` of `Δ = μ_{p−1}/⟨-1⟩` satisfies
`[t]^{p−1} = [t^{p−1}] = [1] = 1`, since `t ∈ μ_{p−1}` (`teichmullerFun_pow_card_sub_one`). -/
theorem exponent_Delta_dvd (hp2 : p ≠ 2) : Monoid.exponent (Delta p hp2) ∣ (p - 1) := by
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro x
  induction x using QuotientGroup.induction_on with
  | _ t =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have ht : t ^ (p - 1) = 1 := by
      apply Subtype.ext; apply Units.ext
      rw [SubmonoidClass.coe_pow, Subgroup.coe_one, Units.val_one, Units.val_pow_eq_pow_val]
      obtain ⟨u, hu⟩ := t.2
      rw [← hu, teichmuller_coe]
      exact teichmullerFun_pow_card_sub_one p u
    rw [ht]; exact one_mem _

/-- `ℤ_[p]` has enough roots of unity of order `exponent Δ` (divisor of `p − 1`,
`exponent_Delta_dvd`), the precise hypothesis of the isotypic completeness `∑_ω e_ω = 1` over `Δ`. -/
instance instHasEnoughRootsOfUnityExponentDelta (hp2 : p ≠ 2) :
    HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (Delta p hp2)) := by
  haveI : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  exact HasEnoughRootsOfUnity.of_dvd ℤ_[p] (exponent_Delta_dvd p hp2)

/-- The character group `Δ →* ℤ_[p]ˣ` is finite (`≃* Δ` by the duality, `Δ` finite). -/
noncomputable instance instFintypeCharHomDelta (hp2 : p ≠ 2) :
    Fintype (Delta p hp2 →* ℤ_[p]ˣ) :=
  Fintype.ofEquiv (Delta p hp2)
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (Delta p hp2) ℤ_[p]).some.symm.toEquiv

/-- Under `unitsSplitEquiv`, `-1 ↦ (negOneT, 1)` — it lives purely in the `μ_{p−1}` factor. -/
theorem unitsSplitEquiv_neg_one (hp2 : p ≠ 2) :
    unitsSplitEquiv p (-1) = (negOneT p hp2, 1) := by
  apply Prod.ext
  · apply Subtype.ext; exact teichmuller_neg_one p hp2
  · apply Subtype.ext
    show (-1 : ℤ_[p]ˣ) * (teichmuller p (-1))⁻¹ = 1
    rw [teichmuller_neg_one p hp2]; norm_num

/-- `zpowers (a, 1) = (zpowers a).prod ⊥` in a product group. -/
theorem zpowers_prod_bot {A B : Type*} [Group A] [Group B] (a : A) :
    Subgroup.zpowers ((a, 1) : A × B) = (Subgroup.zpowers a).prod ⊥ := by
  have hmem : ((a, 1) : A × B) ∈ (Subgroup.zpowers a).prod ⊥ :=
    ⟨Subgroup.mem_zpowers a, Subgroup.mem_bot.mpr rfl⟩
  refine le_antisymm (Subgroup.zpowers_le.mpr hmem) ?_
  rintro ⟨x, y⟩ h
  rw [Subgroup.mem_prod, Subgroup.mem_bot] at h
  obtain ⟨hx, hy⟩ := h; subst hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine ⟨n, Prod.ext ?_ ?_⟩
  · change a ^ n = x; exact hn
  · change (1 : B) ^ n = 1; exact one_zpow n

/-- **The `/±1` quotient** `GPlus ≃* Δ × Γ`.  `unitsSplitEquiv` carries `⟨-1⟩` to `⟨(negOneT,1)⟩ =
⟨negOneT⟩ × ⊥` (`unitsSplitEquiv_neg_one`, `zpowers_prod_bot`); transporting the quotient
(`QuotientGroup.congr`) and splitting the product quotient (`QuotientGroup.prodMulEquiv`,
`QuotientGroup.quotientBot`) gives `GPlus ≃* (μ_{p−1}/⟨-1⟩) × Γ = Δ × Γ`. -/
noncomputable def gplusMulEquiv (hp2 : p ≠ 2) :
    PadicMeasure.GPlus p ≃* (Delta p hp2 × Gamma p) := by
  have he : Subgroup.map (unitsSplitEquiv p).toMonoidHom (Subgroup.zpowers (-1 : ℤ_[p]ˣ))
      = (Subgroup.zpowers (negOneT p hp2)).prod ⊥ := by
    rw [MonoidHom.map_zpowers,
      show (unitsSplitEquiv p).toMonoidHom (-1) = (negOneT p hp2, 1) from
        unitsSplitEquiv_neg_one p hp2]
    exact zpowers_prod_bot _
  exact (QuotientGroup.congr (Subgroup.zpowers (-1 : ℤ_[p]ˣ))
      ((Subgroup.zpowers (negOneT p hp2)).prod ⊥) (unitsSplitEquiv p) he).trans
    ((QuotientGroup.prodMulEquiv (Subgroup.zpowers (negOneT p hp2)) ⊥).trans
      (MulEquiv.prodCongr (MulEquiv.refl _) (QuotientGroup.quotientBot)))

instance instDiscreteTopologyTeichRange : DiscreteTopology ((teichmuller p).range) :=
  Finite.instDiscreteTopology

instance instDiscreteTopologyDelta (hp2 : p ≠ 2) : DiscreteTopology (Delta p hp2) :=
  QuotientGroup.discreteTopology (isOpen_discrete _)

/-- **`gplusMulEquiv` is continuous** (forward).  `GPlus` carries the quotient topology, so it
suffices that `gplusMulEquiv ∘ mk = (u ↦ (Δ-class of ω(u), u·ω(u)⁻¹))` is continuous: the `Δ`-part is
`mk' ∘ (continuous ω into the range)` and the `Γ`-part is `gammaProj` (`continuous_gammaProj`). -/
theorem continuous_gplusMulEquiv (hp2 : p ≠ 2) : Continuous (gplusMulEquiv p hp2) := by
  apply continuous_coinduced_dom.mpr
  refine Continuous.prodMk ?_ (continuous_gammaProj p)
  exact continuous_quot_mk.comp (continuous_induced_rng.2 (continuous_teichmuller p))

/-! ## The logarithm isomorphism `Γ ≅ (ℤ_p, +)` as continuous maps -/

/-- **The p-adic exponential is a difference-isometry on `pℤ_p`**: `‖pZpExp x − pZpExp y‖ = ‖x − y‖`
(integral incarnation of `norm_padicExp_sub_padicExp`). -/
theorem norm_pZpExp_sub (hp2 : p ≠ 2) {x y : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])})
    (hy : y ∈ Ideal.span {(p : ℤ_[p])}) :
    ‖pZpExp p x - pZpExp p y‖ = ‖x - y‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_sub, pZpExp_coe p hp2 hx, pZpExp_coe p hp2 hy,
    norm_padicExp_sub_padicExp p (inExpBall_of_mem_span p hp2 hx) (inExpBall_of_mem_span p hp2 hy),
    ← PadicInt.coe_sub, ← PadicInt.norm_def]

/-- **`logCM`** — the continuous map `Γ → ℤ_p`, `u ↦ log(u)/p`.  Continuity: `divP ∘ pZpLog` is
`LipschitzOnWith p` on the `1`-units (`divP_sub`, `norm_divP`, `norm_pZpLog_sub`), composed with the
continuous value coercion `Γ → ℤ_p` whose image lies in the `1`-units. -/
noncomputable def logCM (hp2 : p ≠ 2) : C(Gamma p, ℤ_[p]) where
  toFun u := divP p (pZpLog p ((↑u : ℤ_[p]ˣ) : ℤ_[p]))
  continuous_toFun := by
    have hF : ContinuousOn (fun x : ℤ_[p] => divP p (pZpLog p x))
        {x : ℤ_[p] | x - 1 ∈ Ideal.span {(p : ℤ_[p])}} := by
      have hlip : LipschitzOnWith (p : NNReal) (fun x : ℤ_[p] => divP p (pZpLog p x))
          {x : ℤ_[p] | x - 1 ∈ Ideal.span {(p : ℤ_[p])}} := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro x hx y hy
        have hlx : pZpLog p x ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hx
        have hly : pZpLog p y ∈ Ideal.span {(p : ℤ_[p])} := pZpLog_mem p hp2 hy
        rw [dist_eq_norm, dist_eq_norm, divP_sub p hlx hly, norm_divP p (Ideal.sub_mem _ hlx hly),
          norm_pZpLog_sub p hp2 hx hy]
        simp [NNReal.coe_natCast]
      exact hlip.continuousOn
    exact hF.comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun u => u.2)

/-- The unit `exp(p·a) ∈ ℤ_[p]ˣ` (with explicit inverse `exp(p·(−a))`), used to land `expCM` in the
group of units. -/
noncomputable def expUnit (hp2 : p ≠ 2) (a : ℤ_[p]) : ℤ_[p]ˣ where
  val := pZpExp p ((p : ℤ_[p]) * a)
  inv := pZpExp p ((p : ℤ_[p]) * (-a))
  val_inv := by
    rw [← pZpExp_add p hp2 (Ideal.mem_span_singleton'.2 ⟨a, by ring⟩)
      (Ideal.mem_span_singleton'.2 ⟨-a, by ring⟩),
      show (p : ℤ_[p]) * a + (p : ℤ_[p]) * (-a) = 0 from by ring, pZpExp_zero p hp2]
  inv_val := by
    rw [← pZpExp_add p hp2 (Ideal.mem_span_singleton'.2 ⟨-a, by ring⟩)
      (Ideal.mem_span_singleton'.2 ⟨a, by ring⟩),
      show (p : ℤ_[p]) * (-a) + (p : ℤ_[p]) * a = 0 from by ring, pZpExp_zero p hp2]

@[simp] theorem expUnit_val (hp2 : p ≠ 2) (a : ℤ_[p]) :
    ((expUnit p hp2 a : ℤ_[p]ˣ) : ℤ_[p]) = pZpExp p ((p : ℤ_[p]) * a) := rfl

@[simp] theorem expUnit_inv (hp2 : p ≠ 2) (a : ℤ_[p]) :
    ((expUnit p hp2 a)⁻¹ : ℤ_[p]ˣ).val = pZpExp p ((p : ℤ_[p]) * (-a)) := rfl

/-- `exp(p·a)` is a principal `1`-unit, so `expUnit a ∈ Γ`. -/
theorem expUnit_mem (hp2 : p ≠ 2) (a : ℤ_[p]) : expUnit p hp2 a ∈ OneUnits p := by
  show ((expUnit p hp2 a : ℤ_[p]ˣ) : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}
  rw [expUnit_val]
  exact pZpExp_sub_one_mem p hp2 (Ideal.mem_span_singleton'.2 ⟨a, by ring⟩)

/-- `a ↦ pZpExp (p·a)` is continuous (`ContinuousOn pZpExp` on `pℤ_p`, via the exp isometry,
precomposed with the continuous `a ↦ p·a` landing in `pℤ_p`). -/
theorem continuous_pZpExp_mul (hp2 : p ≠ 2) :
    Continuous (fun a : ℤ_[p] => pZpExp p ((p : ℤ_[p]) * a)) := by
  have hE : ContinuousOn (pZpExp p) {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}} := by
    have hlip : LipschitzOnWith 1 (pZpExp p) {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}} := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro x hx y hy
      rw [dist_eq_norm, dist_eq_norm, norm_pZpExp_sub p hp2 hx hy]
      simp
    exact hlip.continuousOn
  exact hE.comp_continuous (continuous_const.mul continuous_id)
    (fun a => Ideal.mem_span_singleton'.2 ⟨a, by ring⟩)

/-- **`expCM`** — the continuous map `ℤ_p → Γ`, `a ↦ exp(p·a)`.  Continuity into the units uses
`Units.continuous_iff` (both the value `exp(p·a)` and the inverse `exp(p·(−a))` are continuous). -/
noncomputable def expCM (hp2 : p ≠ 2) : C(ℤ_[p], Gamma p) where
  toFun a := ⟨expUnit p hp2 a, expUnit_mem p hp2 a⟩
  continuous_toFun := by
    refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · show Continuous (fun a : ℤ_[p] => ((expUnit p hp2 a : ℤ_[p]ˣ) : ℤ_[p]))
      simp only [expUnit_val]
      exact continuous_pZpExp_mul p hp2
    · show Continuous (fun a : ℤ_[p] => ((expUnit p hp2 a)⁻¹ : ℤ_[p]ˣ).val)
      simp only [expUnit_inv]
      exact (continuous_pZpExp_mul p hp2).comp continuous_neg

/-! ## The four homomorphism / inverse equations of `Γ ≅ (ℤ_p,+)` (the `gammaLogEquiv` data) -/

/-- `logCM` is multiplicative→additive: `log(uv)/p = log u/p + log v/p`. -/
theorem logCM_mul (hp2 : p ≠ 2) (u v : Gamma p) :
    logCM p hp2 (u * v) = logCM p hp2 u + logCM p hp2 v := by
  show divP p (pZpLog p ((↑(u * v) : ℤ_[p]ˣ) : ℤ_[p])) = divP p (pZpLog p _) + divP p (pZpLog p _)
  have huv : ((↑(u * v) : ℤ_[p]ˣ) : ℤ_[p]) = ((↑u : ℤ_[p]ˣ) : ℤ_[p]) * ((↑v : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [Subgroup.coe_mul, Units.val_mul]
  rw [huv, pZpLog_mul p hp2 u.2 v.2, divP_add p (pZpLog_mem p hp2 u.2) (pZpLog_mem p hp2 v.2)]

/-- `logCM 1 = 0`. -/
theorem logCM_one (hp2 : p ≠ 2) : logCM p hp2 1 = 0 := by
  show divP p (pZpLog p ((↑(1 : Gamma p) : ℤ_[p]ˣ) : ℤ_[p])) = 0
  rw [show ((↑(1 : Gamma p) : ℤ_[p]ˣ) : ℤ_[p]) = 1 by rw [OneMemClass.coe_one, Units.val_one],
    pZpLog_one p hp2]
  apply PadicInt.ext; rw [divP_coe p (by simp), PadicInt.coe_zero, zero_div]

/-- `exp(p · (log u / p)) = u` — left inverse. -/
theorem expCM_logCM (hp2 : p ≠ 2) (u : Gamma p) : expCM p hp2 (logCM p hp2 u) = u := by
  apply Subtype.ext; apply Units.ext
  show pZpExp p ((p : ℤ_[p]) * divP p (pZpLog p ((↑u : ℤ_[p]ˣ) : ℤ_[p]))) = ((↑u : ℤ_[p]ˣ) : ℤ_[p])
  rw [mul_divP p (pZpLog_mem p hp2 u.2), pZpExp_pZpLog p hp2 u.2]

/-- `log(exp(p · a))/p = a` — right inverse. -/
theorem logCM_expCM (hp2 : p ≠ 2) (a : ℤ_[p]) : logCM p hp2 (expCM p hp2 a) = a := by
  show divP p (pZpLog p ((↑(expCM p hp2 a) : ℤ_[p]ˣ) : ℤ_[p])) = a
  rw [show ((↑(expCM p hp2 a) : ℤ_[p]ˣ) : ℤ_[p]) = pZpExp p ((p : ℤ_[p]) * a) from rfl,
    pZpLog_pZpExp p hp2 (Ideal.mem_span_singleton'.2 ⟨a, by ring⟩), divP_mul_self]

end PadicLFunctions
