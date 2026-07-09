/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.FieldTheory.Fixed
import ModularCurves.ForMathlib.InvariantTorsor

/-!
# Descent of a `G`-invariant Weierstrass curve to the fixed subring

For a `MulSemiringAction G A`, a `WeierstrassCurve A` all of whose coefficients are `G`-invariant
comes, by `WeierstrassCurve.map`, from a `WeierstrassCurve Aᴳ` over the fixed subring.

This is building block `[a5-iv]` of `locallyWeierstrass_quotientπ` (`Moduli/EngineDescent.lean`):
after the `VariableChange` cocycle of the `G`-action on the universal curve's Weierstrass model is
trivialized Zariski-locally on `Spec Aᴳ` (additive Hilbert 90 for `(r,s,t)` +
`exists_unit_smul_eq_of_isLocalRing` for `u`, both proven in `ForMathlib/InvariantTorsor.lean`),
the model becomes `G`-invariant, and *this* lemma descends it to a Weierstrass curve over `Aᴳ` —
the model of the quotient curve `E/G` over `X/G = Spec Aᴳ`.

`FixedPoints.subring A G` is defeq to `FixedPoints.subalgebra ℤ A G` (the ring the project's
`localQuotient`/`invariantsπ` are `Spec` of), so this interoperates with the descent geometry.
-/

open scoped Pointwise

universe u

variable {G : Type*} [Group G] {A : Type u} [CommRing A] [MulSemiringAction G A]

namespace WeierstrassCurve

/-- A Weierstrass curve over `A` all of whose coefficients are `G`-invariant, as a Weierstrass
curve over the fixed subring `Aᴳ = FixedPoints.subring A G`. -/
def descendFixed (W : WeierstrassCurve A)
    (h₁ : ∀ g : G, g • W.a₁ = W.a₁) (h₂ : ∀ g : G, g • W.a₂ = W.a₂)
    (h₃ : ∀ g : G, g • W.a₃ = W.a₃) (h₄ : ∀ g : G, g • W.a₄ = W.a₄)
    (h₆ : ∀ g : G, g • W.a₆ = W.a₆) : WeierstrassCurve (FixedPoints.subring A G) where
  a₁ := ⟨W.a₁, h₁⟩
  a₂ := ⟨W.a₂, h₂⟩
  a₃ := ⟨W.a₃, h₃⟩
  a₄ := ⟨W.a₄, h₄⟩
  a₆ := ⟨W.a₆, h₆⟩

/-- Base-changing `descendFixed` back up to `A` recovers the original curve: the descended curve
`W₀` over `Aᴳ` satisfies `W₀.map (Aᴳ ↪ A) = W`. -/
@[simp]
theorem descendFixed_map (W : WeierstrassCurve A) (h₁ h₂ h₃ h₄ h₆) :
    (W.descendFixed h₁ h₂ h₃ h₄ h₆).map (algebraMap (FixedPoints.subring A G) A) = W := by
  cases W
  rfl

/-- If the base-changed-up curve is elliptic, so is the descended curve — the discriminant of
`descendFixed` is a unit because its image in `A` is (`Δ` commutes with `map`, and `Aᴳ ↪ A` is
injective, reflecting units of the subring). -/
theorem descendFixed_isElliptic [Nontrivial A] (W : WeierstrassCurve A) (h₁ h₂ h₃ h₄ h₆)
    (hΔ : IsUnit (W.descendFixed h₁ h₂ h₃ h₄ h₆ (G := G)).Δ) :
    (W.descendFixed h₁ h₂ h₃ h₄ h₆ (G := G)).IsElliptic := by
  rw [isElliptic_iff]
  exact hΔ

/-! ### The `G`-action on `VariableChange A` ([a5-iii] foundation)

For the descent of the quotient curve's Weierstrass model, the `G`-action on the universal curve's
model is expressed (via `pointedIso_exists_variableChange`, T-W7.1b) as a `1`-cocycle valued in the
group `VariableChange A`. The base action of `G` on `A` induces a coefficientwise action on
`VariableChange A` **by group automorphisms** — this is what makes "cocycle" meaningful and is the
foundation of the trivialization ([a5-iii]): the `u`-part is a multiplicative cocycle
(`exists_unit_smul_eq_of_isLocalRing`), the `(r,s,t)`-part additive (`exists_sub_smul_eq_of_isCocycle`).
-/

/-- The `G`-action on a unit of `A`, through the induced ring automorphism. -/
noncomputable def uSMul (g : G) (u : Aˣ) : Aˣ :=
  Units.map (MulSemiringAction.toRingHom G A g).toMonoidHom u

@[simp] theorem uSMul_coe (g : G) (u : Aˣ) : ((uSMul g u : Aˣ) : A) = g • (u : A) := rfl

/-- The coefficientwise `G`-action on `VariableChange A`. -/
noncomputable def vcSMul (g : G) (C : VariableChange A) : VariableChange A where
  u := uSMul g C.u
  r := g • C.r
  s := g • C.s
  t := g • C.t

@[simp] theorem vcSMul_u (g : G) (C : VariableChange A) : (vcSMul g C).u = uSMul g C.u := rfl
@[simp] theorem vcSMul_r (g : G) (C : VariableChange A) : (vcSMul g C).r = g • C.r := rfl
@[simp] theorem vcSMul_s (g : G) (C : VariableChange A) : (vcSMul g C).s = g • C.s := rfl
@[simp] theorem vcSMul_t (g : G) (C : VariableChange A) : (vcSMul g C).t = g • C.t := rfl

/-- The action distributes over the `VariableChange` group law: `G` acts by group homomorphisms. -/
theorem vcSMul_mul (g : G) (C C' : VariableChange A) :
    vcSMul g (C * C') = vcSMul g C * vcSMul g C' := by
  have hp : ∀ (u : Aˣ) (n : ℕ), g • ((u : A) ^ n) = ((uSMul g u : Aˣ) : A) ^ n := by
    intro u n; rw [uSMul_coe]; exact (map_pow (MulSemiringAction.toRingHom G A g) _ _)
  simp only [vcSMul, VariableChange.mul_def, VariableChange.mk.injEq]
  refine ⟨by ext; simp [smul_mul'], ?_, ?_, ?_⟩
  · rw [smul_add, smul_mul', hp, uSMul_coe]
  · rw [smul_add, smul_mul', uSMul_coe]
  · rw [smul_add, smul_add, smul_mul', smul_mul', smul_mul', hp, hp, uSMul_coe]

@[simp] theorem vcSMul_one (g : G) : vcSMul g (1 : VariableChange A) = 1 := by
  simp only [vcSMul, VariableChange.one_def, smul_zero]
  ext <;> simp [uSMul]

/-- `VariableChange A` carries a `MulDistribMulAction` of `G`: the base action acts by group
automorphisms of the admissible-change-of-variables group. -/
noncomputable instance : MulDistribMulAction G (VariableChange A) where
  smul := vcSMul
  one_smul C := by
    show vcSMul 1 C = C
    cases C; simp only [vcSMul, one_smul, VariableChange.mk.injEq, and_true, true_and]
    ext; simp [uSMul]
  mul_smul g h C := by
    show vcSMul (g * h) C = vcSMul g (vcSMul h C)
    cases C
    simp only [vcSMul, mul_smul, VariableChange.mk.injEq, and_true, true_and]
    ext; simp [uSMul, mul_smul]
  smul_mul g := vcSMul_mul g
  smul_one := vcSMul_one

@[simp] theorem vcSMul_smul_def (g : G) (C : VariableChange A) : g • C = vcSMul g C := rfl

/-! ### The cocycle and its `u`-part trivialization ([a5-iii], step 1) -/

/-- A `1`-cocycle for the `G`-action on `VariableChange A`: `C (gh) = C g · (g • C h)`.
This is the shape of the `VariableChange`-valued datum produced by the `G`-action on the
universal curve's Weierstrass model (`pointedIso_exists_variableChange`, T-W7.1b). -/
def IsVCocycle (C : G → VariableChange A) : Prop :=
  ∀ g h : G, C (g * h) = C g * g • C h

/-- **([a5-iii], step 1 — the `u`-part trivializes)** For a free action with `Aᴳ` local, the
`u`-component of a `VariableChange` cocycle is a coboundary: there is a unit `d : Aˣ` with
`g • d = (C g).u · d` for all `g`.

The `u`-part `g ↦ (C g).u` is a multiplicative `1`-cocycle in `Aˣ` (`IsVCocycle` ⟹
`(C (gh)).u = (C g).u · g • (C h).u`), so this is exactly `exists_unit_smul_eq_of_isLocalRing`
([A711-DESC], PROVEN). Conjugating `C` by `(d, 0, 0, 0)` reduces to the case `u = 1`, where the
remaining `(r, s, t)`-cocycle is trivialized by the additive Hilbert 90
`exists_sub_smul_eq_of_isCocycle`. -/
theorem exists_unit_u_of_isVCocycle [Fintype G] [DecidableEq G] [Nontrivial A]
    [IsLocalRing (FixedPoints.subalgebra ℤ A G)]
    (hfree : IsFreeAlgebraAction G ℤ A) {C : G → VariableChange A} (hC : IsVCocycle C) :
    ∃ d : Aˣ, ∀ g : G, g • (d : A) = ((C g).u : A) * (d : A) := by
  refine exists_unit_smul_eq_of_isLocalRing G ℤ A hfree (fun g => (C g).u) ?_
  intro g h
  have h1 := congrArg WeierstrassCurve.VariableChange.u (hC g h)
  simp only [VariableChange.mul_def, vcSMul_smul_def, vcSMul_u] at h1
  rw [h1, Units.val_mul, uSMul_coe]

/-- Conjugating a `VariableChange` cocycle by a constant `D` yields a cocycle (same cohomology
class): `[a5-iii] step 2` conjugates by `(d,0,0,0)` — with `d` from `exists_unit_u_of_isVCocycle` —
to reduce to the `u = 1` case, where the residual `(r,s,t)`-cocycle is trivialized by the additive
Hilbert 90 `exists_sub_smul_eq_of_isCocycle` (PROVEN). -/
theorem isVCocycle_conj (D : VariableChange A) {C : G → VariableChange A} (hC : IsVCocycle C) :
    IsVCocycle (fun g => D * C g * (g • D)⁻¹) := by
  intro g h
  simp only [hC g h, mul_smul g h D, smul_mul', smul_inv']
  group

/-- `g • (d, 0, 0, 0) = (g • d, 0, 0, 0)`. -/
theorem vcSMul_mk_zero (g : G) (d : Aˣ) :
    (g • (⟨d, 0, 0, 0⟩ : VariableChange A)) = ⟨uSMul g d, 0, 0, 0⟩ :=
  VariableChange.ext rfl (smul_zero g) (smul_zero g) (smul_zero g)

/-- The `u`-part of the conjugate of `C g` by `(d, 0, 0, 0)` is `1`, when `d` witnesses the
`u`-coboundary `uSMul g d = (C g).u · d`. -/
theorem conj_u_one (d : Aˣ) {C : G → VariableChange A}
    (hd : ∀ g : G, uSMul g d = (C g).u * d) (g : G) :
    ((⟨d,0,0,0⟩ : VariableChange A) * C g * (g • (⟨d,0,0,0⟩ : VariableChange A))⁻¹).u = 1 := by
  rw [vcSMul_mk_zero]
  show d * (C g).u * (uSMul g d)⁻¹ = 1
  rw [hd g]
  exact mul_inv_eq_one.mpr (mul_comm d (C g).u)

/-- **([a5-iii], step 2 — reduce to `u = 1`)** For a free action with `Aᴳ` local, every
`VariableChange` cocycle is cohomologous to one with `u`-component identically `1`: conjugate by
`(d, 0, 0, 0)` where `d` is the unit from `exists_unit_u_of_isVCocycle`. The residual cocycle lives
in the `(r, s, t)` translation subgroup, to be trivialized by the additive Hilbert 90. -/
theorem exists_conj_u_one [Fintype G] [DecidableEq G] [Nontrivial A]
    [IsLocalRing (FixedPoints.subalgebra ℤ A G)] (hfree : IsFreeAlgebraAction G ℤ A)
    {C : G → VariableChange A} (hC : IsVCocycle C) :
    ∃ D : VariableChange A, IsVCocycle (fun g => D * C g * (g • D)⁻¹) ∧
      ∀ g : G, (D * C g * (g • D)⁻¹).u = 1 := by
  obtain ⟨d, hd'⟩ := exists_unit_u_of_isVCocycle hfree hC
  have hd : ∀ g : G, uSMul g d = (C g).u * d := by
    intro g; apply Units.ext; rw [uSMul_coe, Units.val_mul]; exact hd' g
  exact ⟨⟨d, 0, 0, 0⟩, isVCocycle_conj _ hC, conj_u_one d hd⟩

end WeierstrassCurve
