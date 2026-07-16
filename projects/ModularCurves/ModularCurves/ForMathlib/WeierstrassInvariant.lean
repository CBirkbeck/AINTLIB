/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
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
(`exists_unit_smul_eq_of_isLocalRing`), the `(r,s,t)`-part additive
(`exists_sub_smul_eq_of_isCocycle`).
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
    cases C; simp only [vcSMul, one_smul, VariableChange.mk.injEq, and_true]
    ext; simp [uSMul]
  mul_smul g h C := by
    show vcSMul (g * h) C = vcSMul g (vcSMul h C)
    cases C
    simp only [vcSMul, mul_smul, VariableChange.mk.injEq, and_true]
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

/-- Base change of a Weierstrass curve along the ring hom of a product `g * h` factors as the two
single base changes (functoriality of `map` + multiplicativity of `MulSemiringAction.toRingHom`):
`W.map (toRingHom (g*h)) = (W.map (toRingHom h)).map (toRingHom g)`, i.e. `(gh)•W = g•(h•W)`. -/
theorem map_toRingHom_mul (W : WeierstrassCurve A) (g h : G) :
    W.map (MulSemiringAction.toRingHom G A (g * h))
      = (W.map (MulSemiringAction.toRingHom G A h)).map (MulSemiringAction.toRingHom G A g) := by
  rw [map_map]
  congr 1
  ext a
  show (g * h) • a = g • h • a
  exact mul_smul g h a

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

/-- **([a5-iii], step 3 — the `s`-layer is additive)** For a cocycle with `u`-component identically
`1`, the `s`-component is an additive `1`-cocycle `s(gh) = s(g) + g • s(h)` — so
`exists_sub_smul_eq_of_isCocycle` (additive Hilbert 90, PROVEN) yields `σ` with `(C g).s = σ − g•σ`,
and conjugating by `(1, 0, σ, 0)` kills it (preserving `u = 1`). The `r`- and `t`-layers follow the
same pattern (the `t`-cocycle carries the nilpotent twist `r·(g•s')`, handled after `r`, `s` are
trivialized), completing the trivialization of the residual `(r,s,t)`-cocycle. -/
theorem s_isCocycle_of_u_one {C : G → VariableChange A} (hC : IsVCocycle C)
    (hu : ∀ g, (C g).u = 1) (g h : G) :
    (C (g * h)).s = (C g).s + g • (C h).s := by
  have h1 := congrArg WeierstrassCurve.VariableChange.s (hC g h)
  simp only [VariableChange.mul_def, vcSMul_smul_def, vcSMul_u, vcSMul_s] at h1
  rw [h1]
  have hu1 : ((uSMul g (C h).u : Aˣ) : A) = 1 := by
    rw [uSMul_coe, hu h, Units.val_one, smul_one]
  rw [hu1, one_mul]

/-- `g • (1, 0, σ, 0) = (1, 0, g • σ, 0)`. -/
theorem vcSMul_mk_s (g : G) (σ : A) :
    (g • (⟨1,0,σ,0⟩ : VariableChange A)) = ⟨1, 0, g • σ, 0⟩ := by
  apply VariableChange.ext
  · apply Units.ext; simp [vcSMul_smul_def, vcSMul, uSMul_coe, smul_one]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]
  · simp [vcSMul_smul_def, vcSMul]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]

/-- The `s`-component of conjugating a `u = 1` element `C g` by `(1, 0, σ, 0)`. -/
theorem conj_s_component (σ : A) {C : G → VariableChange A} (hu : ∀ g, (C g).u = 1) (g : G) :
    ((⟨1,0,σ,0⟩ : VariableChange A) * C g * (g • (⟨1,0,σ,0⟩ : VariableChange A))⁻¹).s
      = σ + (C g).s - g • σ := by
  rw [vcSMul_mk_s]
  simp only [VariableChange.mul_def, VariableChange.inv_def, hu g, Units.val_one,
    inv_one, mul_one, one_mul]
  ring

/-- **([a5-iii], step 3 — kill `s`)** A `u = 1` `VariableChange` cocycle is cohomologous to one with
`u = 1` *and* `s = 0`: conjugate by `(1, 0, -d, 0)`, where `d` is the additive Hilbert 90
witness for the `s`-cocycle (`(C g).s = d - g•d`). The residual cocycle now lives in the
`(r, t)` subgroup. -/
theorem exists_conj_s_zero [Fintype G] (hfree : IsFreeAlgebraAction G ℤ A)
    {C : G → VariableChange A} (hC : IsVCocycle C) (hu : ∀ g, (C g).u = 1) :
    ∃ D : VariableChange A, IsVCocycle (fun g => D * C g * (g • D)⁻¹) ∧
      (∀ g, (D * C g * (g • D)⁻¹).u = 1) ∧ (∀ g, (D * C g * (g • D)⁻¹).s = 0) := by
  obtain ⟨d, hd⟩ := exists_sub_smul_eq_of_isCocycle G ℤ A hfree (fun g => (C g).s)
    (s_isCocycle_of_u_one hC hu)
  refine ⟨⟨1, 0, -d, 0⟩, isVCocycle_conj _ hC, fun g => ?_, fun g => ?_⟩
  · rw [vcSMul_mk_s]
    simp only [VariableChange.mul_def, VariableChange.inv_def, hu g, Units.val_one, inv_one,
      mul_one, one_mul]
  · rw [conj_s_component (-d) hu g, hd g, smul_neg]
    ring

/-- `g • (1, ρ, 0, 0) = (1, g • ρ, 0, 0)`. -/
theorem vcSMul_mk_r (g : G) (ρ : A) :
    (g • (⟨1,ρ,0,0⟩ : VariableChange A)) = ⟨1, g • ρ, 0, 0⟩ := by
  apply VariableChange.ext
  · apply Units.ext; simp [vcSMul_smul_def, vcSMul, uSMul_coe, smul_one]
  · simp [vcSMul_smul_def, vcSMul]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]

/-- **([a5-iii], step 4 — kill `r`)** With `s = 0` the `r`-component of a `u = 1` cocycle is an
additive cocycle (the nilpotent twist `r·s'` vanishes), so conjugating by `(1, -d, 0, 0)`
(`d` the Hilbert 90 witness for the `r`-cocycle) kills `r` while preserving `u = 1` and `s = 0`.
The residual cocycle lives in the central `t`-subgroup. -/
theorem exists_conj_r_zero [Fintype G] (hfree : IsFreeAlgebraAction G ℤ A)
    {C : G → VariableChange A} (hC : IsVCocycle C) (hu : ∀ g, (C g).u = 1)
    (hs : ∀ g, (C g).s = 0) :
    ∃ D : VariableChange A, IsVCocycle (fun g => D * C g * (g • D)⁻¹) ∧
      (∀ g, (D * C g * (g • D)⁻¹).u = 1) ∧ (∀ g, (D * C g * (g • D)⁻¹).s = 0) ∧
      (∀ g, (D * C g * (g • D)⁻¹).r = 0) := by
  have hrc : ∀ g h : G, (C (g * h)).r = (C g).r + g • (C h).r := by
    intro g h
    have h1 := congrArg WeierstrassCurve.VariableChange.r (hC g h)
    simp only [VariableChange.mul_def, vcSMul_smul_def, vcSMul_u, vcSMul_r] at h1
    rw [h1]
    have : ((uSMul g (C h).u : Aˣ) : A) = 1 := by rw [uSMul_coe, hu h, Units.val_one, smul_one]
    rw [this]; ring
  obtain ⟨d, hd⟩ := exists_sub_smul_eq_of_isCocycle G ℤ A hfree (fun g => (C g).r) hrc
  refine ⟨⟨1, -d, 0, 0⟩, isVCocycle_conj _ hC, fun g => ?_, fun g => ?_, fun g => ?_⟩
  · rw [vcSMul_mk_r]
    simp [VariableChange.mul_def, VariableChange.inv_def, hu g]
  · rw [vcSMul_mk_r]
    simp only [VariableChange.mul_def, VariableChange.inv_def, hu g, hs g, Units.val_one,
      inv_one, mul_one, mul_zero, zero_mul, add_zero, zero_add, neg_zero]
  · rw [vcSMul_mk_r]
    simp only [VariableChange.mul_def, VariableChange.inv_def, hu g, hs g, Units.val_one,
      inv_one, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    rw [hd g, smul_neg]; ring

/-- `g • (1, 0, 0, τ) = (1, 0, 0, g • τ)`. -/
theorem vcSMul_mk_t (g : G) (τ : A) :
    (g • (⟨1,0,0,τ⟩ : VariableChange A)) = ⟨1, 0, 0, g • τ⟩ := by
  apply VariableChange.ext
  · apply Units.ext; simp [vcSMul_smul_def, vcSMul, uSMul_coe, smul_one]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]
  · simp [vcSMul_smul_def, vcSMul, smul_zero]
  · simp [vcSMul_smul_def, vcSMul]

/-- With `r = s = 0` the `t`-component of a `u = 1` cocycle is a *central* additive cocycle. -/
theorem t_isCocycle {C : G → VariableChange A} (hC : IsVCocycle C)
    (hu : ∀ g, (C g).u = 1) (_hs : ∀ g, (C g).s = 0) (hr : ∀ g, (C g).r = 0) (g h : G) :
    (C (g * h)).t = (C g).t + g • (C h).t := by
  have h1 := congrArg WeierstrassCurve.VariableChange.t (hC g h)
  simp only [VariableChange.mul_def, vcSMul_smul_def, vcSMul_u, vcSMul_r, vcSMul_s, vcSMul_t,
    hr g, hu h] at h1
  rw [h1]
  simp only [uSMul_coe, Units.val_one, smul_one, one_pow, mul_one,
    zero_mul, add_zero]

/-- **([a5-iii], step 5 — kill `t`)** With `u = 1, r = s = 0` the `t`-cocycle is killed by
conjugating with `(1, 0, 0, -d)`, leaving the trivial cocycle `1`. -/
theorem exists_conj_t_zero [Fintype G] (hfree : IsFreeAlgebraAction G ℤ A)
    {C : G → VariableChange A} (hC : IsVCocycle C) (hu : ∀ g, (C g).u = 1)
    (hs : ∀ g, (C g).s = 0) (hr : ∀ g, (C g).r = 0) :
    ∃ D : VariableChange A, ∀ g, D * C g * (g • D)⁻¹ = 1 := by
  obtain ⟨d, hd⟩ := exists_sub_smul_eq_of_isCocycle G ℤ A hfree (fun g => (C g).t)
    (t_isCocycle hC hu hs hr)
  refine ⟨⟨1, 0, 0, -d⟩, fun g => ?_⟩
  rw [vcSMul_mk_t]
  apply VariableChange.ext
  · apply Units.ext
    simp [VariableChange.mul_def, VariableChange.inv_def, VariableChange.one_def, hu g]
  · simp [VariableChange.mul_def, VariableChange.inv_def, VariableChange.one_def, hu g, hr g]
  · simp [VariableChange.mul_def, VariableChange.inv_def, VariableChange.one_def, hu g, hs g]
  · simp only [VariableChange.mul_def, VariableChange.inv_def, VariableChange.one_def, hu g,
      hr g, hs g, Units.val_one, mul_one, one_mul, one_pow, mul_zero, zero_mul, add_zero, zero_add]
    rw [hd g, smul_neg]; ring

/-- **([a5-iii] COMPLETE — local vanishing of `H¹(G, VariableChange A)`)** For a free action with
`Aᴳ` local, every `VariableChange` cocycle is a **coboundary**: there is `E : VariableChange A` with
`C g = E * (g • E)⁻¹` for all `g`. Chain the four layer-trivializations
`exists_conj_u_one → exists_conj_s_zero → exists_conj_r_zero → exists_conj_t_zero`; the composite
conjugator `D = Dₜ·Dᵣ·D_s·D_u` satisfies `D · C g · (g•D)⁻¹ = 1`, i.e.
`C g = D⁻¹ · (g•D) = E · (g•E)⁻¹`
with `E = D⁻¹`.

Geometrically: the `VariableChange` cocycle of the `G`-action on the universal curve's Weierstrass
model `W₀` is trivialized by a single `E`, so `E⁻¹ • W₀` is `G`-invariant and descends to the model
of `E/G` over `X/G = Spec Aᴳ` (`descendFixed`). This is the heart of `[a5]`. -/
theorem exists_coboundary [Fintype G] [DecidableEq G] [Nontrivial A]
    [IsLocalRing (FixedPoints.subalgebra ℤ A G)] (hfree : IsFreeAlgebraAction G ℤ A)
    {C : G → VariableChange A} (hC : IsVCocycle C) :
    ∃ E : VariableChange A, ∀ g : G, C g = E * (g • E)⁻¹ := by
  obtain ⟨Du, hCu_coc, hCu⟩ := exists_conj_u_one hfree hC
  obtain ⟨Ds, hCs_coc, hCs_u, hCs⟩ := exists_conj_s_zero hfree hCu_coc hCu
  obtain ⟨Dr, hCr_coc, hCr_u, hCr_s, hCr⟩ := exists_conj_r_zero hfree hCs_coc hCs_u hCs
  obtain ⟨Dt, hDt⟩ := exists_conj_t_zero hfree hCr_coc hCr_u hCr_s hCr
  refine ⟨(Dt * Dr * Ds * Du)⁻¹, fun g => ?_⟩
  have hflat : (Dt * Dr * Ds * Du) * C g * (g • (Dt * Dr * Ds * Du))⁻¹ = 1 := by
    have := hDt g
    simp only [smul_mul', mul_inv_rev, mul_assoc] at this ⊢
    convert this using 3
  have h2 : (Dt * Dr * Ds * Du) * C g = g • (Dt * Dr * Ds * Du) := mul_inv_eq_one.mp hflat
  rw [smul_inv', inv_inv]
  exact eq_inv_mul_iff_mul_eq.mpr h2

/-- `vcSMul g` is `VariableChange.map` along the ring automorphism `g`. -/
theorem vcSMul_eq_map (g : G) (C : VariableChange A) :
    vcSMul g C = C.map (MulSemiringAction.toRingHom G A g) := by
  apply VariableChange.ext
  · apply Units.ext; rfl
  all_goals rfl

/-- **([a5-iii], the cocycle candidate is action-compatible)** If `C` is action-compatible
(`C g • (g•W₀) = W₀`), then the cocycle candidate `C g * g • C h` sends `(gh)•W₀` to `W₀` as well —
the *cardinality* half of the cocycle identity `C (gh) = C g * g • C h`. Both `C (gh)` and
`C g * g • C h` carry `(gh)•W₀` to `W₀`; faithfulness of the model action
(`projModelVCIso_injective`) upgrades this to the identity itself (the geometric half). Chains
`mul_smul`, `map_toRingHom_mul`, `map_variableChange` and the two action-compatibilities. -/
theorem vc_mul_smul_eq (W₀ : WeierstrassCurve A) {C : G → VariableChange A}
    (hact : ∀ g, C g • (W₀.map (MulSemiringAction.toRingHom G A g)) = W₀) (g h : G) :
    (C g * g • C h) • (W₀.map (MulSemiringAction.toRingHom G A (g * h))) = W₀ := by
  rw [mul_smul, map_toRingHom_mul, vcSMul_smul_def, vcSMul_eq_map, map_variableChange, hact h,
    hact g]

/-- **([a5-iv] algebraic core — the descended model)** Let `G` act freely on `A` with `Aᴳ` local,
and let `W₀ : WeierstrassCurve A` carry a `VariableChange`-cocycle `G`-action, i.e. `C : G →
VariableChange A` a cocycle with `C_g • (g • W₀) = W₀` for all `g` (here `g • W₀ = W₀.map g` is the
coefficientwise action). Then there is `E : VariableChange A` and a `WeierstrassCurve Aᴳ` `W₁` with
`W₁.map (Aᴳ ↪ A) = E⁻¹ • W₀`.

`E` comes from `exists_coboundary` (`C_g = E·(g•E)⁻¹`); `E⁻¹ • W₀` is then `G`-invariant
(`g • (E⁻¹•W₀) = (g•E)⁻¹•(g•W₀) = E⁻¹•W₀`, using `map_variableChange` and the cocycle relation),
so its coefficients lie in `Aᴳ` and `descendFixed` produces `W₁`.

Geometrically: `W₀` is the (global) Weierstrass model of the universal curve `E`, the cocycle is the
`G`-action's change-of-variables datum (`a5-ii`), and `W₁` is the Weierstrass model of the quotient
curve `E/G` over `X/G = Spec Aᴳ`. Together with `isPullback_projModelBaseChange`,
`projModelVCIso` and `isPullback_quotientπ` this yields the `LocallyWeierstrass` iso — the
remaining geometric `a5-iv`. -/
theorem exists_invariant_descent [Fintype G] [DecidableEq G] [Nontrivial A]
    [IsLocalRing (FixedPoints.subalgebra ℤ A G)] (hfree : IsFreeAlgebraAction G ℤ A)
    (W₀ : WeierstrassCurve A) {C : G → VariableChange A} (hC : IsVCocycle C)
    (haction : ∀ g : G, C g • (W₀.map (MulSemiringAction.toRingHom G A g)) = W₀) :
    ∃ (E : VariableChange A) (W₁ : WeierstrassCurve (FixedPoints.subring A G)),
      W₁.map (algebraMap (FixedPoints.subring A G) A) = E⁻¹ • W₀ := by
  obtain ⟨E, hE⟩ := exists_coboundary hfree hC
  have hinv : ∀ g : G,
      (E⁻¹ • W₀).map (MulSemiringAction.toRingHom G A g) = E⁻¹ • W₀ := by
    intro g
    rw [← WeierstrassCurve.map_variableChange, ← vcSMul_eq_map, ← vcSMul_smul_def, smul_inv']
    have h1 := haction g
    rw [hE g, mul_smul] at h1
    rw [← inv_smul_smul E ((g • E)⁻¹ • (W₀.map (MulSemiringAction.toRingHom G A g))), h1]
  refine ⟨E, (E⁻¹ • W₀).descendFixed (fun g => ?_) (fun g => ?_) (fun g => ?_) (fun g => ?_)
      (fun g => ?_), (E⁻¹ • W₀).descendFixed_map _ _ _ _ _⟩
  · exact congrArg WeierstrassCurve.a₁ (hinv g)
  · exact congrArg WeierstrassCurve.a₂ (hinv g)
  · exact congrArg WeierstrassCurve.a₃ (hinv g)
  · exact congrArg WeierstrassCurve.a₄ (hinv g)
  · exact congrArg WeierstrassCurve.a₆ (hinv g)

/-- A `G`-fixed element that is a unit in `A` is a unit in the fixed subring: its inverse is
automatically fixed (`g • x⁻¹ = (g • x)⁻¹`). No integrality or finiteness needed. -/
theorem isUnit_subring_of_isUnit {x : FixedPoints.subring A G}
    (h : IsUnit (x : A)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  have hfix : ∀ g : G, g • (↑u⁻¹ : A) = ↑u⁻¹ := by
    intro g
    have h₁ : (g • (↑u⁻¹ : A)) * (↑u : A) = 1 := by
      have := congrArg (g • ·) u.inv_mul
      simpa [smul_mul', hu, x.2 g] using this
    calc g • (↑u⁻¹ : A) = (g • (↑u⁻¹ : A)) * ((↑u : A) * ↑u⁻¹) := by
          rw [u.mul_inv, mul_one]
      _ = ((g • (↑u⁻¹ : A)) * ↑u) * ↑u⁻¹ := by ring
      _ = ↑u⁻¹ := by rw [h₁, one_mul]
  refine IsUnit.of_mul_eq_one ⟨↑u⁻¹, fun g => hfix g⟩ ?_
  ext
  push_cast
  rw [← hu, u.mul_inv]

/-- **Ellipticity descends**: the invariant model produced by `exists_invariant_descent` is
elliptic whenever `W₀` is — its discriminant is a fixed element mapping to the unit
`Δ(E⁻¹ • W₀) = (E.u⁻¹)¹² • Δ(W₀)` of `A`, hence a unit of the fixed subring
(`isUnit_subring_of_isUnit`). -/
theorem isElliptic_of_map_isElliptic {W₁ : WeierstrassCurve (FixedPoints.subring A G)}
    {W : WeierstrassCurve A} (hmap : W₁.map (algebraMap (FixedPoints.subring A G) A) = W)
    (hW : W.IsElliptic) : W₁.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff] at hW ⊢
  refine isUnit_subring_of_isUnit ?_
  have : (algebraMap (FixedPoints.subring A G) A) W₁.Δ = W.Δ := by
    rw [← hmap, WeierstrassCurve.map_Δ]
  rw [show (W₁.Δ : A) = (algebraMap (FixedPoints.subring A G) A) W₁.Δ from rfl, this]
  exact hW

end WeierstrassCurve
