/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.GaloisAction
import PadicLFunctions.Iwasawa.ResidueField

/-!
# Equivariance of the Coleman map (RJW §12.1, TeX 3117–3243) — 12.1

The `ℤ_p`-action on `𝒰_{∞,1}` (via `zpPow`), the Teichmüller split
`𝒰_∞ = μ_{p−1} × 𝒰_{∞,1}`, the killing of `μ_{p−1}` by `Col`, and the assembly into the
`Λ(𝒢)`-module statement `cor:G-eq`. (The `ℤ_p`-equivariance Prop, TeX 3130–3156,
is subsumed by `Col_lambdaG_equivariant`: the scalar part of the `Λ(𝒢)`-action; its
standalone form is finalised when the `NormCompatUnits` `ℤ_p`-module structure lands at
execution.) The `μ_{p−1}`-killing (`Col_eq_zero_of_torsion`) and the `Λ(𝒢)`-equivariance
(`Col_lambdaG_equivariant`) are complete; the Teichmüller split
(`normCompat_eq_teichmuller_mul_principal`) is now sorry-free, proved in
`Iwasawa/ResidueField.lean` on the residue-field-of-`O_n` infrastructure (the norm-residue
compatibility `norm_levelNorm_sub_one_lt_one`, the `𝒪_n`-residue `residueZp`, and the constant
Teichmüller system `omegaNCU`).
-/

open PadicLFunctions PadicLFunctions.Coleman

noncomputable section

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### `∂log`-homomorphism helpers (re-derived in-file)

`Equivariance.lean` imports `Coleman.Map` (where `dlog` lives) but not `LogDerivative.lean`
(where `dlog_mul`/`dlog_one`/`dlog_pow` are proven); these short re-derivations make the
`μ_{p−1}`-killing argument self-contained. -/

/-- `∂log(g·h) = ∂log g + ∂log h` for units `g, h` (re-derivation of
`LogDerivative.dlog_mul`): `(gh)' = g'h + gh'`, divide by `gh`. -/
private theorem dlog_mul {g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) :
    dlog p (g * h) = dlog p g + dlog p h := by
  have hg' : g * Ring.inverse g = 1 := Ring.mul_inverse_cancel _ hg
  have hh' : h * Ring.inverse h = 1 := Ring.mul_inverse_cancel _ hh
  rw [dlog, dlog, dlog, PowerSeries.derivativeFun_mul, smul_eq_mul, smul_eq_mul,
    Ring.mul_inverse_rev]
  rw [show (1 + PowerSeries.X) * (g * h.derivativeFun + h * g.derivativeFun)
        * (Ring.inverse h * Ring.inverse g)
      = (1 + PowerSeries.X) * g.derivativeFun * Ring.inverse g * (h * Ring.inverse h)
        + (1 + PowerSeries.X) * h.derivativeFun * Ring.inverse h * (g * Ring.inverse g) from by
        ring,
    hg', hh', mul_one, mul_one, add_comm]

/-- `∂log 1 = 0` (re-derivation of `LogDerivative.dlog_one`). -/
private theorem dlog_one : dlog p (1 : PowerSeries ℤ_[p]) = 0 := by
  rw [dlog, PowerSeries.derivativeFun_one, mul_zero, zero_mul]

/-- `∂log(gᵏ) = k·∂log g` for a unit `g` (re-derivation of `LogDerivative.dlog_pow`). -/
private theorem dlog_pow {g : PowerSeries ℤ_[p]} (hg : IsUnit g) (k : ℕ) :
    dlog p (g ^ k) = (k : ℤ) • dlog p g := by
  induction k with
  | zero => simp [dlog_one p]
  | succ m ih => rw [pow_succ, dlog_mul p (hg.pow m) hg, ih]; push_cast; ring

/-- `colemanSeries 1 = 1`: the unit `colemanSeries 1` is idempotent
(`colemanSeries_mul` at `1·1 = 1`), hence `1`. -/
private theorem colemanSeries_one : colemanSeries p (1 : NormCompatUnits p) = 1 := by
  have h := colemanSeries_mul p (1 : NormCompatUnits p) 1
  rw [mul_one] at h
  exact (mul_right_eq_self₀.mp h.symm).resolve_right (colemanSeries_isUnit p 1).ne_zero

/-- `colemanSeries (uᵏ) = (colemanSeries u)ᵏ` (`colemanSeries_mul`/`colemanSeries_one`). -/
private theorem colemanSeries_pow (u : NormCompatUnits p) (k : ℕ) :
    colemanSeries p (u ^ k) = (colemanSeries p u) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, colemanSeries_one p]
  | succ m ih => rw [pow_succ, pow_succ, colemanSeries_mul p, ih]

/-- The level units of a power: `(uᵏ).elems n = (u.elems n)ᵏ` (the `NormCompatUnits`
multiplication is pointwise). -/
private theorem elems_pow (u : NormCompatUnits p) (k n : ℕ) :
    (u ^ k).elems n = (u.elems n) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ m ih => rw [pow_succ, pow_succ, ← ih]; rfl

/-- A nonzero integer kills no `ℤ_p` power series: `(k : ℤ) • g = 0` with `k ≠ 0`
forces `g = 0` (coefficientwise, `ℤ_[p]` a `CharZero` domain). -/
private theorem zsmul_powerSeries_eq_zero {g : PowerSeries ℤ_[p]} {k : ℕ} (hk : k ≠ 0)
    (h : (k : ℤ) • g = 0) : g = 0 := by
  ext n
  have hcoef : (k : ℤ) • PowerSeries.coeff n g = 0 := by
    rw [← map_zsmul (PowerSeries.coeff n) (k : ℤ) g, h, map_zero]
  rw [map_zero]
  exact (smul_eq_zero.mp hcoef).resolve_left (by exact_mod_cast hk)

/-- **RJW §12.1 Lemma (TeX 3170–3178)**: `μ_{p−1} ⊂ 𝒰_∞` is killed by `Col` (constant
Coleman series are killed by `∂log`). Stated for a `(p−1)`-torsion tower.

Proof (homomorphism route, TeX 3174–3178): elementwise `(p−1)`-torsion gives
`u^{p−1} = 1` in `𝒰_∞`, so `(f_u)^{p−1} = f_{u^{p−1}} = f_1 = 1` (`colemanSeries_pow`,
`colemanSeries_one`). Hence `(p−1)·∂log f_u = ∂log((f_u)^{p−1}) = ∂log 1 = 0`
(`dlog_pow`, `dlog_one`); as `p − 1 ≠ 0` and `ℤ_p⟦T⟧` is torsion-free,
`∂log f_u = 0`. The Coleman map is `∂log f_u ↦ 𝒜⁻¹ ↦ Res ↦ x⁻¹·`, all linear, so
`Col u = 0` (`map_zero`/`LinearMap.zero_comp`). -/
theorem Col_eq_zero_of_torsion (u : NormCompatUnits p) (htor : ∀ n, (u.elems n) ^ (p - 1) = 1) :
    Col p u = 0 := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  -- elementwise torsion ⟹ `u^{p−1} = 1` in `𝒰_∞`
  have hupow : u ^ (p - 1) = (1 : NormCompatUnits p) := by
    apply NormCompatUnits.ext; funext n; rw [elems_pow p, htor n]; rfl
  -- so the Coleman series is a `(p−1)`-th root of unity: `(f_u)^{p−1} = 1`
  have hfpow : (colemanSeries p u) ^ (p - 1) = 1 := by
    rw [← colemanSeries_pow p, hupow, colemanSeries_one p]
  -- `(p−1)·∂log f_u = ∂log 1 = 0`
  have hsmul : ((p - 1 : ℕ) : ℤ) • dlog p (colemanSeries p u) = 0 := by
    rw [← dlog_pow p (colemanSeries_isUnit p u), hfpow, dlog_one p]
  -- torsion-freeness of `ℤ_p⟦T⟧` ⟹ `∂log f_u = 0`
  have hd : dlog p (colemanSeries p u) = 0 := zsmul_powerSeries_eq_zero p hp1 hsmul
  -- push `∂log f_u = 0` through the (linear) tail of `Col`
  rw [Col, hd, map_zero, LinearMap.zero_comp, PadicMeasure.unitsCmul]
  exact LinearMap.zero_comp _

/-- **RJW cor:G-eq (TeX 3241–3243)**: `Col` restricts to a map `𝒰_{∞,1} → Λ(𝒢)` of
`Λ(𝒢)`-modules (the `ℤ_p`- and `𝒢`-actions commute and assemble to `Λ(𝒢)`). Stated as
the conjunction of `ℤ_p`- and `𝒢`-equivariance already established: the `𝒢`-action `σ_a`
on `Λ(𝒢) = Λ(ℤ_[p]ˣ)` is the pushforward of measures along `v ↦ a·v`
(`PadicMeasure.pushforward p (unitsMulLeftCM p a)`), and `Col (σ_a u) = σ_a (Col u)`. -/
theorem Col_lambdaG_equivariant (a : ℤ_[p]ˣ) (u : NormCompatUnits p)
    (_hu : u ∈ unitsTower1 p) :
    Col p (galNCU p a u)
      = PadicMeasure.pushforward p (unitsMulLeftCM p a) (Col p u) := Col_galNCU p a u

end PadicLFunctions.Coleman
