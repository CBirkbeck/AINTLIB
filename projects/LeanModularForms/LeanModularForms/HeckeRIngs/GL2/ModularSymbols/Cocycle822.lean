/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import LeanModularForms.HeckeRIngs.GL2.ModularSymbols.ModuleMFinite

/-!
# The group-1-cocycle bridge for Shimura's period pairing (8.1.3 / 8.2.22)

Shimura's actual proof of the period↔Petersson identity (8.2.22) is a **group-1-cocycle**
computation: the Eichler-integral defect `u_f(α) = F(α z) − F(z)` is a `1`-cocycle in
`Z¹(Γ, X)` (8.1.1), satisfying `u(α⁻¹) = −α⁻¹·u(α)` (8.1.3), and the boundary integral over a
single fundamental domain collapses through this cocycle structure.

This file provides the **founded** algebraic core of that route: the *divisor* `1`-cocycle
`a ↦ (a·c₀) − (c₀) ∈ Div⁰(ℙ¹ℚ)` is a genuine group-1-cocycle for the `Γ₁(N)`-action, landing in
mathlib's `groupCohomology.cocycles₁`.  Its cocycle identity is pure divisor algebra
(`divDiff_add_divDiff` + the equivariance `div0Rep_divDiff_gamma1`) — no analysis.  Pairing it
against a cusp form `f` recovers Shimura's `u_f`; this is the algebraic skeleton onto which the
single-fundamental-domain Stokes computation is grafted.
-/

namespace HeckeRing.GL2.ModularSymbols

open groupCohomology CongruenceSubgroup

local notation "ℙ¹ℚ" => Projectivization ℚ (Fin 2 → ℚ)

universe u

variable {N : ℕ} [NeZero N]

/-- The `Div⁰(ℙ¹ℚ)`-representation of `Γ₁(N)`: the restriction of `div0Rep` along
`Γ₁(N) ↪ SL(2,ℤ)`. -/
noncomputable def div0RepGamma1 (N : ℕ) [NeZero N] :
    Representation ℤ (Gamma1 N) (Div0 ℤ) :=
  (div0Rep ℤ).comp (Gamma1 N).subtype

@[simp] theorem div0RepGamma1_apply (g : Gamma1 N) (x : Div0 ℤ) :
    div0RepGamma1 N g x = div0Rep ℤ g.1 x := rfl

/-- The `Div⁰(ℙ¹ℚ)`-representation of `Γ₁(N)` as a bundled object of the representation category
`Rep ℤ (Γ₁ N)`, so mathlib's `groupCohomology.cocycles₁` applies. -/
noncomputable def div0RepGamma1Rep (N : ℕ) [NeZero N] : Rep ℤ (Gamma1 N) :=
  Rep.of (div0RepGamma1 N)

@[simp] theorem div0RepGamma1Rep_ρ (g : Gamma1 N) (x : Div0 ℤ) :
    (div0RepGamma1Rep N).ρ g x = div0Rep ℤ g.1 x := rfl

/-- **Shimura's divisor 1-cochain** `u(a) = (a·c₀) − (c₀) ∈ Div⁰(ℙ¹ℚ)`, base-pointed at a cusp
`c₀`.  Pairing `u(a)` against a cusp form recovers the Eichler-integral period defect. -/
noncomputable def divCocycle (N : ℕ) [NeZero N] (c₀ : ℙ¹ℚ) : Gamma1 N → Div0 ℤ :=
  fun a => divDiff (a • c₀) c₀

@[simp] theorem divCocycle_apply (c₀ : ℙ¹ℚ) (a : Gamma1 N) :
    divCocycle N c₀ a = divDiff (a • c₀) c₀ := rfl

/-- **The divisor cochain is a group-1-cocycle** (Shimura 8.1.1): `u(gh) = ρ(g)·u(h) + u(g)`.
Proof is pure divisor algebra — the equivariance `div0Rep_divDiff_gamma1` turns `ρ(g)·u(h)` into
`(gh·c₀) − (g·c₀)`, and `divDiff_add_divDiff` telescopes it with `u(g) = (g·c₀) − (c₀)`. -/
theorem divCocycle_mem_cocycles₁ (c₀ : ℙ¹ℚ) :
    divCocycle N c₀ ∈ cocycles₁ (div0RepGamma1Rep N) := by
  refine (mem_cocycles₁_iff _).mpr fun g h => ?_
  simp only [divCocycle_apply, div0RepGamma1Rep_ρ, div0Rep_divDiff_gamma1, mul_smul]
  exact (divDiff_add_divDiff _ _ _).symm

/-- The divisor `1`-cocycle as a bundled element of `Z¹(Γ₁ N, Div⁰)`. -/
noncomputable def divCocycle₁ (N : ℕ) [NeZero N] (c₀ : ℙ¹ℚ) : cocycles₁ (div0RepGamma1Rep N) :=
  ⟨divCocycle N c₀, divCocycle_mem_cocycles₁ c₀⟩

/-- Shimura (8.1.3) specialised to the divisor cocycle: `ρ(a)·u(a⁻¹) = −u(a)`. -/
theorem div0Rep_divCocycle_inv (c₀ : ℙ¹ℚ) (a : Gamma1 N) :
    div0Rep ℤ a.1 (divCocycle N c₀ a⁻¹) = -divCocycle N c₀ a := by
  have h := cocycles₁_map_inv (divCocycle₁ N c₀) a
  exact h

end HeckeRing.GL2.ModularSymbols
