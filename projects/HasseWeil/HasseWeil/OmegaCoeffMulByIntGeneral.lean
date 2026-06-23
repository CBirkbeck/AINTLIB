/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Differentials
import HasseWeil.EC.MulByIntAddRecurrence
import HasseWeil.FormalIsogenySeries

/-!
# Route B over a general field: `[n]^*ω = n·ω` and separability of `[n]`

The **field-general Route-B chord induction** (Silverman III.5.2/3 at the differential level):
for an elliptic curve `W` over an arbitrary field `F`, the `ω`-pullback coefficient of the
multiplication-by-`n` isogeny is `a_{[n]} = n` (`omegaCoeff_mulByInt`), hence `[n]` is
separable whenever `(n : F) ≠ 0` (`mulByInt_isSeparable`, Silverman III.5.4 / II.4.10c).
The whole chain is a sequence of pure Kähler / ring identities — no finite-field hypothesis,
no EDS Wronskian — so every declaration is axiom-clean.

The chain:
* the curve-equation Kähler identity `kaehler_curve_eqn`
  (`(a₃+2y+a₁x) • D(y) = (3x²+2a₂x+a₄−a₁y) • D(x)`);
* the RB-ω cone: `D(x_gen) = u_gen • ω` (`kaehlerD_x_gen_eq_u_smul_omega`), its `y`-analogue,
  and their `α`-pullbacks (`kaehlerD_alpha_pullback_x/y_eq_smul_omega`);
* the III.5.2 chord collapse `kaehlerD_addPullback_x_eq_one_add_smul_omega`
  (`D(addPullback_x α) = addPullback_u • (1 + a_α) • ω`);
* the chord step `omegaCoeff_mulByInt_succ` (`a_{[k+1]} = 1 + a_{[k]}` for `k ≥ 2`), seeded by
  the axiom-clean `[2]` base case `omegaPullbackCoeff_mulByInt_two` and closed under negation
  (`omegaCoeff_mulByInt_neg`), assembling to `omegaCoeff_mulByInt : a_{[n]} = n` for all `n ≠ 0`.

## Provenance

Relocated verbatim (2026-06-11) from `HasseWeil/WeilPairing/TorsionGeometric.lean`, where the
chain was born as a deliberate `K → F` re-derivation of the `[Fintype K]`-scoped
`RouteBInduction.lean` induction (whose blanket `Fintype` was an artifact of its section
headers, not of the mathematics). It now sits **below** `Hasse/Separability.lean` in the import
graph, so `Separability`/`PullbackCoeff` can discharge `a_{[n]} = n` through the axiom-clean
`omegaCoeff_mulByInt` instead of the EDS-Wronskian-tainted `omegaPullbackCoeff_mulByInt`
(`OmegaPullbackCoeff.lean`, whose `m ≥ 5` Wronskian branch carries the project's standing
`sorryAx`).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, III.5.2–III.5.4.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `y_gen² + a₁·x_gen·y_gen + a₃·y_gen = x_gen³ + a₂·x_gen² + a₄·x_gen + a₆` in `K(E)`
(`weierstrass_equation_in_KE`, restated field-general from `generic_equation`). -/
theorem weierstrassEqn_KE :
    y_gen W ^ 2 + algebraMap F KE W.a₁ * x_gen W * y_gen W +
        algebraMap F KE W.a₃ * y_gen W =
      x_gen W ^ 3 + algebraMap F KE W.a₂ * x_gen W ^ 2 +
        algebraMap F KE W.a₄ * x_gen W + algebraMap F KE W.a₆ := by
  have h_gen := generic_equation W
  rw [(W_KE W).toAffine.equation_iff] at h_gen
  exact h_gen

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D(y_gen² + a₁xy + a₃y) = D(x_gen³ + a₂x² + a₄x + a₆)` in `Ω[K(E)/F]`. -/
theorem kaehlerD_weierstrassEqn :
    KaehlerDifferential.D F KE
        (y_gen W ^ 2 + algebraMap F KE W.a₁ * x_gen W * y_gen W +
          algebraMap F KE W.a₃ * y_gen W) =
      KaehlerDifferential.D F KE
        (x_gen W ^ 3 + algebraMap F KE W.a₂ * x_gen W ^ 2 +
          algebraMap F KE W.a₄ * x_gen W + algebraMap F KE W.a₆) :=
  congrArg (KaehlerDifferential.D F KE) (weierstrassEqn_KE W)

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D(y_gen²) = y_gen • D(y_gen) + y_gen • D(y_gen)`. -/
theorem kaehlerD_y_gen_sq :
    KaehlerDifferential.D F KE (y_gen W ^ 2) =
      y_gen W • KaehlerDifferential.D F KE (y_gen W) +
      y_gen W • KaehlerDifferential.D F KE (y_gen W) := by
  rw [pow_two, (KaehlerDifferential.D F KE).leibniz (y_gen W) (y_gen W)]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D(x_gen²) = x_gen • D(x_gen) + x_gen • D(x_gen)`. -/
theorem kaehlerD_x_gen_sq :
    KaehlerDifferential.D F KE (x_gen W ^ 2) =
      x_gen W • KaehlerDifferential.D F KE (x_gen W) +
      x_gen W • KaehlerDifferential.D F KE (x_gen W) := by
  rw [pow_two, (KaehlerDifferential.D F KE).leibniz (x_gen W) (x_gen W)]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `D(x_gen³) = x_gen² • D(x_gen) + x_gen • D(x_gen²)`. -/
theorem kaehlerD_x_gen_cube :
    KaehlerDifferential.D F KE (x_gen W ^ 3) =
      x_gen W ^ 2 • KaehlerDifferential.D F KE (x_gen W) +
      x_gen W • KaehlerDifferential.D F KE (x_gen W ^ 2) := by
  rw [show (x_gen W) ^ 3 = (x_gen W) ^ 2 * x_gen W from by ring,
    (KaehlerDifferential.D F KE).leibniz (x_gen W ^ 2) (x_gen W)]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- D-expansion of the Weierstrass-equation LHS. -/
theorem kaehlerD_weierstrass_LHS :
    KaehlerDifferential.D F KE
        (y_gen W ^ 2 + algebraMap F KE W.a₁ * x_gen W * y_gen W +
          algebraMap F KE W.a₃ * y_gen W) =
      (y_gen W • KaehlerDifferential.D F KE (y_gen W) +
        y_gen W • KaehlerDifferential.D F KE (y_gen W)) +
      ((algebraMap F KE W.a₁ * x_gen W) • KaehlerDifferential.D F KE (y_gen W) +
        y_gen W • (algebraMap F KE W.a₁ • KaehlerDifferential.D F KE (x_gen W))) +
      algebraMap F KE W.a₃ • KaehlerDifferential.D F KE (y_gen W) := by
  rw [map_add, map_add, kaehlerD_y_gen_sq W,
    (KaehlerDifferential.D F KE).leibniz (algebraMap F KE W.a₁ * x_gen W) (y_gen W),
    (KaehlerDifferential.D F KE).leibniz (algebraMap F KE W.a₁) (x_gen W),
    (KaehlerDifferential.D F KE).leibniz (algebraMap F KE W.a₃) (y_gen W),
    (KaehlerDifferential.D F KE).map_algebraMap W.a₁,
    (KaehlerDifferential.D F KE).map_algebraMap W.a₃]
  simp only [smul_zero, add_zero]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- D-expansion of the Weierstrass-equation RHS. -/
theorem kaehlerD_weierstrass_RHS :
    KaehlerDifferential.D F KE
        (x_gen W ^ 3 + algebraMap F KE W.a₂ * x_gen W ^ 2 +
          algebraMap F KE W.a₄ * x_gen W + algebraMap F KE W.a₆) =
      ((x_gen W ^ 2 • KaehlerDifferential.D F KE (x_gen W) +
          x_gen W • (x_gen W • KaehlerDifferential.D F KE (x_gen W) +
              x_gen W • KaehlerDifferential.D F KE (x_gen W))) +
        algebraMap F KE W.a₂ •
          (x_gen W • KaehlerDifferential.D F KE (x_gen W) +
            x_gen W • KaehlerDifferential.D F KE (x_gen W))) +
      algebraMap F KE W.a₄ • KaehlerDifferential.D F KE (x_gen W) := by
  rw [map_add, map_add, map_add, kaehlerD_x_gen_cube W, kaehlerD_x_gen_sq W,
    (KaehlerDifferential.D F KE).leibniz (algebraMap F KE W.a₂) (x_gen W ^ 2),
    kaehlerD_x_gen_sq W,
    (KaehlerDifferential.D F KE).leibniz (algebraMap F KE W.a₄) (x_gen W),
    (KaehlerDifferential.D F KE).map_algebraMap W.a₂,
    (KaehlerDifferential.D F KE).map_algebraMap W.a₄,
    (KaehlerDifferential.D F KE).map_algebraMap W.a₆]
  simp only [smul_zero, add_zero]

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- **Curve-equation Kähler identity** (the substantive K(E) identity):
`(a₃ + 2y + a₁x) • D(y) = (3x² + 2a₂x + a₄ − a₁y) • D(x)`. -/
theorem kaehler_curve_eqn :
    (algebraMap F KE W.a₃ + (2 : KE) * y_gen W + algebraMap F KE W.a₁ * x_gen W) •
        KaehlerDifferential.D F KE (y_gen W) =
      ((3 : KE) * x_gen W ^ 2 + (2 : KE) * algebraMap F KE W.a₂ * x_gen W +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W) •
        KaehlerDifferential.D F KE (x_gen W) := by
  set Dx := KaehlerDifferential.D F KE (x_gen W)
  set Dy := KaehlerDifferential.D F KE (y_gen W)
  have h2y : (2 : KE) * y_gen W = y_gen W + y_gen W := by ring
  have h3x2 : (3 : KE) * x_gen W ^ 2 = x_gen W ^ 2 + x_gen W ^ 2 + x_gen W ^ 2 := by ring
  have h2a2x : (2 : KE) * algebraMap F KE W.a₂ * x_gen W =
    algebraMap F KE W.a₂ * x_gen W + algebraMap F KE W.a₂ * x_gen W := by ring
  rw [h2y, h3x2, h2a2x]
  simp only [add_smul, sub_smul]
  have h_eq := kaehlerD_weierstrassEqn W
  rw [kaehlerD_weierstrass_LHS W, kaehlerD_weierstrass_RHS W] at h_eq
  simp only [smul_add, ← mul_smul] at h_eq ⊢
  rw [show x_gen W * x_gen W = x_gen W ^ 2 from (sq (x_gen W)).symm] at h_eq
  rw [show y_gen W * algebraMap F KE W.a₁ = algebraMap F KE W.a₁ * y_gen W from by ring] at h_eq
  linear_combination (norm := abel) h_eq

omit [DecidableEq F] in
/-- **RB-ω1**: `D(x_gen) = u_gen • ω`. -/
theorem kaehlerD_x_gen_eq_u_smul_omega :
    KaehlerDifferential.D F KE (x_gen W) =
      u_gen W • invariantDifferential W.toAffine := by
  rw [show invariantDifferential W.toAffine =
        (u_gen W)⁻¹ • KaehlerDifferential.D F KE (x_gen W) from rfl,
    smul_smul, mul_inv_cancel₀ (u_gen_ne_zero W), one_smul]

omit [DecidableEq F] in
/-- **RB-ω2**: `D(y_gen) = (3x²+2a₂x+a₄−a₁y) • ω`. -/
theorem kaehlerD_y_gen_eq_num_smul_omega :
    KaehlerDifferential.D F KE (y_gen W) =
      (3 * x_gen W ^ 2 + 2 * algebraMap F KE W.a₂ * x_gen W +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W) •
        invariantDifferential W.toAffine := by
  have h127 := kaehler_curve_eqn W
  have hu : algebraMap F KE W.a₃ + (2 : KE) * y_gen W + algebraMap F KE W.a₁ * x_gen W =
      u_gen W := by
    change algebraMap F KE W.a₃ + (2 : KE) * y_gen W + algebraMap F KE W.a₁ * x_gen W =
      2 * y_gen W + algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃
    ring
  rw [hu] at h127
  have h2 : u_gen W • KaehlerDifferential.D F KE (y_gen W) =
      u_gen W • ((3 * x_gen W ^ 2 + 2 * algebraMap F KE W.a₂ * x_gen W +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * y_gen W) •
        invariantDifferential W.toAffine) := by
    rw [h127, kaehlerD_x_gen_eq_u_smul_omega, smul_comm]
  exact smul_right_injective _ (u_gen_ne_zero W) h2

/-- `alpha_star_u W α ≠ 0`: the pulled-back `u_gen` is nonzero since `α.pullback` is injective
and `u_gen` is nonzero. -/
theorem alpha_star_u_ne_zero (α : Isogeny W.toAffine W.toAffine) : alpha_star_u W α ≠ 0 := by
  rw [alpha_star_u_eq]
  exact fun h ↦ u_gen_ne_zero W (α.pullback_injective (by rw [h, map_zero]))

/-- **RB-ω3a**: `D(α*x) = (α*u · a_α) • ω`. -/
theorem kaehlerD_alpha_pullback_x_eq_smul_omega (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D F KE (α.pullback (x_gen W)) =
      (alpha_star_u W α * omegaPullbackCoeff W α) • invariantDifferential W.toAffine := by
  have hspec := omegaPullbackCoeff_spec W α
  rw [show (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) = x_gen W from rfl] at hspec
  have key : alpha_star_u W α • (omegaPullbackCoeff W α • invariantDifferential W.toAffine) =
      KaehlerDifferential.D F KE (α.pullback (x_gen W)) := by
    rw [hspec, smul_smul, mul_inv_cancel₀ (alpha_star_u_ne_zero W α), one_smul]
  rw [← key, smul_smul]

/-- **RB-ω3b**: `D(α*y) = (α*num · a_α) • ω`. -/
theorem kaehlerD_alpha_pullback_y_eq_smul_omega (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D F KE (α.pullback (y_gen W)) =
      ((3 * (α.pullback (x_gen W)) ^ 2 +
          2 * algebraMap F KE W.a₂ * (α.pullback (x_gen W)) +
          algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (α.pullback (y_gen W))) *
        omegaPullbackCoeff W α) • invariantDifferential W.toAffine := by
  have hx := kaehlerD_alpha_pullback_x_eq_smul_omega W α
  have himg := congrArg (Isogeny.pullbackKaehler α) (kaehler_curve_eqn W)
  rw [Isogeny.pullbackKaehler_smul_KE, Isogeny.pullbackKaehler_smul_KE,
    Isogeny.pullbackKaehler_D, Isogeny.pullbackKaehler_D] at himg
  have hC : α.pullback (algebraMap F KE W.a₃ + 2 * y_gen W + algebraMap F KE W.a₁ * x_gen W) =
      alpha_star_u W α := by
    rw [alpha_star_u_eq, u_gen]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
      show α.pullback (algebraMap R KE (AdjoinRoot.root W.toAffine.polynomial)) =
          α.pullback (y_gen W) from rfl,
      show α.pullback (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) =
          α.pullback (x_gen W) from rfl]
    ring
  have hN : α.pullback ((3 : KE) * x_gen W ^ 2 +
      2 * algebraMap F KE W.a₂ * x_gen W + algebraMap F KE W.a₄ -
      algebraMap F KE W.a₁ * y_gen W) =
      3 * (α.pullback (x_gen W)) ^ 2 +
        2 * algebraMap F KE W.a₂ * (α.pullback (x_gen W)) +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * (α.pullback (y_gen W)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, AlgHom.commutes]
  rw [hC, hN, hx, smul_smul] at himg
  refine smul_right_injective _ (alpha_star_u_ne_zero W α)
    (?_ : alpha_star_u W α • _ = alpha_star_u W α • _)
  rw [himg, smul_smul]
  congr 1
  ring

/-- **General slope differential** (Route B core III.5.2): for `x_gen ≠ α*x_gen`,
`Den²·D(addSlope) = Den·(D(y)−D(α*y)) − N·(D(x)−D(α*x))`. -/
theorem kaehlerD_addSlope_general (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D F KE (addSlope W α) =
      (x_gen W - α.pullback (x_gen W)) •
        (KaehlerDifferential.D F KE (y_gen W) -
         KaehlerDifferential.D F KE (α.pullback (y_gen W))) -
      (y_gen W - α.pullback (y_gen W)) •
        (KaehlerDifferential.D F KE (x_gen W) -
         KaehlerDifferential.D F KE (α.pullback (x_gen W))) := by
  set D := KaehlerDifferential.D F KE
  set N := y_gen W - α.pullback (y_gen W) with hN
  set Den := x_gen W - α.pullback (x_gen W) with hDen
  have hDen_ne : Den ≠ 0 := sub_ne_zero.mpr h_ne
  have h_slope : addSlope W α = N / Den := by
    rw [addSlope, hN, hDen]
    exact (W_KE W).toAffine.slope_of_X_ne h_ne
  rw [h_slope, D.leibniz_div N Den]
  have h_DN : D N = D (y_gen W) - D (α.pullback (y_gen W)) := by rw [hN, map_sub]
  have h_DDen : D Den = D (x_gen W) - D (α.pullback (x_gen W)) := by rw [hDen, map_sub]
  rw [h_DN, h_DDen, smul_smul,
    show Den ^ 2 * Den⁻¹ ^ 2 = 1 from by rw [← mul_pow, mul_inv_cancel₀ hDen_ne, one_pow],
    one_smul]

/-- **General `D(addPullback_x)`** (Route B core III.5.2):
`D(addPullback_x) = (2·addSlope + a₁)·D(addSlope) − D(x) − D(α*x)`. -/
theorem kaehlerD_addPullback_x_general (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D F KE (addPullback_x W α) =
      (2 * addSlope W α + algebraMap F KE W.a₁) •
        KaehlerDifferential.D F KE (addSlope W α) -
      KaehlerDifferential.D F KE (x_gen W) -
      KaehlerDifferential.D F KE (α.pullback (x_gen W)) := by
  unfold addPullback_x W_KE
  set D := KaehlerDifferential.D F KE
  set ℓ := addSlope W α
  change D ((ℓ) ^ 2 + (algebraMap F KE) W.a₁ * ℓ
          - (algebraMap F KE) W.a₂ - x_gen W - α.pullback (x_gen W)) = _
  rw [map_sub, map_sub, map_sub, map_add, D.leibniz ((algebraMap F KE) W.a₁) ℓ,
    D.leibniz_pow ℓ 2, D.map_algebraMap W.a₁, D.map_algebraMap W.a₂]
  simp only [smul_zero, add_zero, sub_zero]
  change (2 : ℕ) • ℓ ^ (2 - 1) • D ℓ + (algebraMap F KE) W.a₁ • D ℓ
      - D (x_gen W) - D (α.pullback (x_gen W)) =
      (2 * ℓ + (algebraMap F KE) W.a₁) • D ℓ - D (x_gen W) - D (α.pullback (x_gen W))
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, add_smul, mul_smul]
  congr 2
  -- `(2 : KE)` rather than the `(R := …)` named arg, since the local `R` notation shadows it.
  rw [show (2 : ℕ) • (ℓ • D ℓ) = ((2 : KE)) • (ℓ • D ℓ) from by
        rw [← Nat.cast_smul_eq_nsmul KE 2 (ℓ • D ℓ)]; norm_num]

/-- **General cleared `D(addPullback_x)`** (`Den²` cleared). -/
theorem kaehlerD_addPullback_x_general_cleared (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D F KE (addPullback_x W α) =
      (2 * addSlope W α + algebraMap F KE W.a₁) •
        ((x_gen W - α.pullback (x_gen W)) •
          (KaehlerDifferential.D F KE (y_gen W) -
           KaehlerDifferential.D F KE (α.pullback (y_gen W)))) -
      (2 * addSlope W α + algebraMap F KE W.a₁) •
        ((y_gen W - α.pullback (y_gen W)) •
          (KaehlerDifferential.D F KE (x_gen W) -
           KaehlerDifferential.D F KE (α.pullback (x_gen W)))) -
      (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D F KE (x_gen W) -
      (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D F KE (α.pullback (x_gen W)) := by
  rw [kaehlerD_addPullback_x_general W α, smul_sub, smul_sub, smul_smul,
    mul_comm ((x_gen W - α.pullback (x_gen W)) ^ 2)
      (2 * addSlope W α + algebraMap F KE W.a₁),
    ← smul_smul, kaehlerD_addSlope_general W α h_ne, smul_sub]

-- `map_add`/`map_mul` in the multi-target `simp only … at hP hαP ⊢` below are used on the
-- hypotheses but flagged unused on the goal; silence the (harmless) linter for this leaf.
set_option linter.unusedSimpArgs false in
/-- **RB-ω4 leaf (the III.5.2 ring collapse)**:
`D(addPullback_x) = addPullback_u • (1 + a_α) • ω`. -/
theorem kaehlerD_addPullback_x_eq_one_add_smul_omega (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    KaehlerDifferential.D F KE (addPullback_x W α) =
      (2 * addPullback_y W α + algebraMap F KE W.a₁ * addPullback_x W α +
        algebraMap F KE W.a₃) •
        ((1 + omegaPullbackCoeff W α) • invariantDifferential W.toAffine) := by
  have hcleared := kaehlerD_addPullback_x_general_cleared W α h_ne
  rw [kaehlerD_x_gen_eq_u_smul_omega W, kaehlerD_y_gen_eq_num_smul_omega W,
    kaehlerD_alpha_pullback_x_eq_smul_omega W α,
    kaehlerD_alpha_pullback_y_eq_smul_omega W α] at hcleared
  refine smul_right_injective _ (pow_ne_zero 2 (sub_ne_zero.mpr h_ne)) (?_ :
    (x_gen W - α.pullback (x_gen W)) ^ 2 • _ =
      (x_gen W - α.pullback (x_gen W)) ^ 2 • _)
  rw [hcleared]
  simp only [smul_smul, ← sub_smul]
  congr 1
  rw [addPullback_y, addPullback_x]
  rw [show addSlope W α =
      (y_gen W - α.pullback (y_gen W)) / (x_gen W - α.pullback (x_gen W)) from by
        rw [addSlope]; exact (W_KE W).toAffine.slope_of_X_ne h_ne]
  rw [show u_gen W = 2 * y_gen W + algebraMap F KE W.a₁ * x_gen W + algebraMap F KE W.a₃ from rfl,
    show alpha_star_u W α = 2 * α.pullback (y_gen W) +
      algebraMap F KE W.a₁ * α.pullback (x_gen W) + algebraMap F KE W.a₃ from rfl]
  have hP := generic_equation W
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  have hαP := pullback_equation W α
  rw [WeierstrassCurve.Affine.equation_iff] at hαP
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    W_KE, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    map_add, map_mul, map_ofNat, AlgHom.commutes] at hP hαP ⊢
  field_simp [sub_ne_zero.mpr h_ne]
  set X := x_gen W
  set Y := y_gen W
  set PX := α.pullback X
  set PY := α.pullback Y
  set c1 := algebraMap F KE W.a₁
  linear_combination
    (-(2 * (Y - PY) + c1 * (X - PX)) * (1 - omegaPullbackCoeff W α)) * hP +
      ((2 * (Y - PY) + c1 * (X - PX)) * (1 - omegaPullbackCoeff W α)) * hαP

/-- **RB chord step**: for `k ≥ 2`, `a_{[k+1]} = 1 + a_{[k]}`. -/
theorem omegaCoeff_mulByInt_succ (k : ℤ) (hk2 : 2 ≤ k) :
    omegaPullbackCoeff W (mulByInt W.toAffine (k + 1))
      = 1 + omegaPullbackCoeff W (mulByInt W.toAffine k) := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k + 1 ≠ 0 := by omega
  have hx_ne : x_gen W ≠ mulByInt_x W k := by
    rw [← mulByInt_x_one W]
    exact mulByInt_x_ne_mulByInt_x W 1 k one_ne_zero hk0 (by omega) (by omega)
  have hkx : (mulByInt W.toAffine k).pullback (x_gen W) = mulByInt_x W k :=
    mulByInt_pullback_x W k hk0
  have hx_ne_pb : x_gen W ≠ (mulByInt W.toAffine k).pullback (x_gen W) := by
    rw [hkx]; exact hx_ne
  obtain ⟨hAx, hAy⟩ := addPullback_xy_mulByInt_eq_succ W k hk0 hk1 hx_ne
  have hu : alpha_star_u W (mulByInt W.toAffine (k + 1))
      = 2 * addPullback_y W (mulByInt W.toAffine k)
        + algebraMap F KE W.a₁ * addPullback_x W (mulByInt W.toAffine k) +
          algebraMap F KE W.a₃ := by
    rw [alpha_star_u_mulByInt W (k + 1) hk1, ← hAx, ← hAy]
  have hu3_ne : 2 * addPullback_y W (mulByInt W.toAffine k)
      + algebraMap F KE W.a₁ * addPullback_x W (mulByInt W.toAffine k) +
        algebraMap F KE W.a₃ ≠ 0 :=
    hu ▸ alpha_star_u_ne_zero W (mulByInt W.toAffine (k + 1))
  have hpx : (mulByInt W.toAffine (k + 1)).pullback
        (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))
      = addPullback_x W (mulByInt W.toAffine k) := by
    rw [mulByInt_pullback_x W (k + 1) hk1, ← hAx]
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx, hu,
    kaehlerD_addPullback_x_eq_one_add_smul_omega W (mulByInt W.toAffine k) hx_ne_pb, smul_smul,
    inv_mul_cancel₀ hu3_ne, one_smul]

/-- `a_{[n]} = n` for `n ≥ 2`. -/
theorem omegaCoeff_mulByInt_ge_two (n : ℤ) (hn : 2 ≤ n) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n := by
  induction n, hn using Int.leInduction with
  | base => exact omegaPullbackCoeff_mulByInt_two W
  | succ k hk2 ih =>
    rw [omegaCoeff_mulByInt_succ W k hk2, ih, Int.cast_add, Int.cast_one, map_add,
      map_one, add_comm]

/-- `a_{[n]} = n` for `n ≥ 1`. -/
theorem omegaCoeff_mulByInt_pos (n : ℤ) (hn : 1 ≤ n) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1; rw [mulByInt_one_eq_id, omegaPullbackCoeff_id, Int.cast_one, map_one]
  · exact omegaCoeff_mulByInt_ge_two W n (by omega)

/-- **RB negation**: `a_{[-n]} = -a_{[n]}` for `n ≠ 0`. -/
theorem omegaCoeff_mulByInt_neg (n : ℤ) (hn : n ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine (-n))
      = -omegaPullbackCoeff W (mulByInt W.toAffine n) := by
  have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
  have hpx_eq : (mulByInt W.toAffine (-n)).pullback
        (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X))
      = (mulByInt W.toAffine n).pullback
        (algebraMap R KE (algebraMap (Polynomial F) R Polynomial.X)) := by
    rw [mulByInt_pullback_x W (-n) hneg, mulByInt_pullback_x W n hn, mulByInt_x_neg]
  have hu_neg : alpha_star_u W (mulByInt W.toAffine (-n))
      = -alpha_star_u W (mulByInt W.toAffine n) := by
    rw [alpha_star_u_mulByInt W (-n) hneg, alpha_star_u_mulByInt W n hn,
      mulByInt_x_neg, mulByInt_y_neg W n hn]
    show 2 * (W_KE W).toAffine.negY (mulByInt_x W n) (mulByInt_y W n)
        + algebraMap F KE W.a₁ * mulByInt_x W n + algebraMap F KE W.a₃ = _
    rw [WeierstrassCurve.Affine.negY,
      show (W_KE W).a₁ = algebraMap F KE W.a₁ from rfl,
      show (W_KE W).a₃ = algebraMap F KE W.a₃ from rfl]
    ring
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, hpx_eq, hu_neg, inv_neg, neg_smul, neg_smul]
  congr 1
  exact (omegaPullbackCoeff_spec W (mulByInt W.toAffine n)).symm

/-- **`a_{[n]} = n` for all `n ≠ 0`** (Silverman III.5.3), over a general field — the Fintype-free
restatement of `omegaPullbackCoeff_mulByInt_routeB`. -/
theorem omegaCoeff_mulByInt (n : ℤ) (hn : n ≠ 0) :
    omegaPullbackCoeff W (mulByInt W.toAffine n) = algebraMap F KE n := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · rw [show n = -(-n) from (neg_neg n).symm,
      omegaCoeff_mulByInt_neg W (-n) (by omega),
      omegaCoeff_mulByInt_pos W (-n) (by omega), ← map_neg]
    norm_cast
  · exact omegaCoeff_mulByInt_pos W n (by omega)

/-- **`[ℓ]` is separable over a general field** when `(ℓ : F) ≠ 0` (Silverman III.5.4),
axiom-clean and finite-field free. The `ω`-coefficient witness is the Route-B chain
`omegaCoeff_mulByInt` (`= ℓ ≠ 0`); finite-dimensionality is the general
`isogeny_finiteDimensional`; the criterion is
`isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim`. -/
theorem mulByInt_isSeparable (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    (mulByInt W.toAffine ℓ).IsSeparable := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  rw [isSeparable_iff_omegaPullbackCoeff_ne_zero_of_finiteDim W (mulByInt W.toAffine ℓ)
      (HasseWeil.isogeny_finiteDimensional W (mulByInt W.toAffine ℓ)),
    omegaCoeff_mulByInt W ℓ hℓ0]
  exact fun h ↦ hℓ ((map_eq_zero _).mp h)

end HasseWeil
