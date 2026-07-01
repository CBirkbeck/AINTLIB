import HasseWeil.FormalGroup.MulByNat
import HasseWeil.FormalGroup.InvariantDiff
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.CharP.Invertible

/-!
# Multiplication by p in characteristic p (Silverman IV.4.4)

For a formal group `F` over a ring `R` of prime characteristic `p`, the
multiplication-by-`p` series lies in `R[[T^p]]`.

## Main result

* `HasseWeil.FormalGroup.FormalGroup.mulByP_exists_expand` — in characteristic
  `p`, there exists `g : PowerSeries R` with `(F.mulByNatHom p).toSeries =
  g.expand p hp`, i.e., `[p](T) = g(T^p)`.

## Proof outline

1. Apply the invariant-differential chain rule to `mulByNatHom p`. This gives
   `(subst [p] ω_F) · [p]'(T) = (p : R) · ω_F`. In characteristic `p`,
   `(p : R) = 0`, so the RHS vanishes.
2. `subst [p] ω_F` has constant coefficient `1` (inherited from `ω_F`), hence
   is a unit in `R⟦T⟧`. Therefore `[p]'(T) = 0`.
3. The formal derivative of a power series is zero iff every non-trivial
   coefficient is annihilated by its degree. In characteristic `p`, the cast
   `(n : R)` is a unit whenever `p ∤ n` (a standard `CharP` fact), so
   `[p]` has zero coefficients outside `{0, p, 2p, …}`.
4. Such a series factors as `g.expand p hp` with `g.coeff m = [p].coeff (p·m)`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.4.4.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-- If a power series factors through every non-`p`-multiple coefficient being
zero, then it is the `expand p hp` of another series. -/
private theorem exists_expand_of_coeff_vanishing (p : ℕ) (hp : p ≠ 0)
    (f : PowerSeries R) (h : ∀ n, ¬ p ∣ n → PowerSeries.coeff n f = 0) :
    ∃ g : PowerSeries R, f = g.expand p hp := by
  refine ⟨PowerSeries.mk (fun m ↦ PowerSeries.coeff (p * m) f), ?_⟩
  ext n
  rw [PowerSeries.coeff_expand]
  split_ifs with hd
  · obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), PowerSeries.coeff_mk]
  · exact h n hd

/-- In characteristic `p`, if `d⁄dX f = 0` then every coefficient `f.coeff n`
vanishes unless `p ∣ n` (or `n = 0`). -/
private theorem coeff_eq_zero_of_derivative_eq_zero_charP {p : ℕ}
    [Fact p.Prime] [CharP R p] {f : PowerSeries R}
    (hf : PowerSeries.derivative R f = 0)
    (n : ℕ) (hpn : ¬ p ∣ n) :
    PowerSeries.coeff n f = 0 := by
  -- `n ≠ 0` since `p ∣ 0`; write `n = m + 1`.
  have hn : n ≠ 0 := fun h ↦ hpn (h ▸ dvd_zero p)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  -- `coeff m (derivative f) = 0` reads `coeff (m+1) f * (m+1) = 0`.
  have hcoeff : PowerSeries.coeff (m + 1) f * ((m + 1 : ℕ) : R) = 0 := by
    simpa [PowerSeries.coeff_derivative, Nat.cast_add_one] using
      congr_arg (PowerSeries.coeff m) hf
  -- `(m + 1 : R)` is a unit since `p ∤ (m+1)`.
  have hunit : IsUnit ((m + 1 : ℕ) : R) :=
    (CharP.isUnit_natCast_iff (p := p) Fact.out).mpr hpn
  exact hunit.mul_left_eq_zero.mp hcoeff

/-- `PowerSeries.subst g f` has the same constant coefficient as `f` when the
constant coefficient of `g` is zero. -/
private lemma constantCoeff_subst_zero_const
    (g : PowerSeries R) (hg : PowerSeries.constantCoeff g = 0)
    (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.subst g f) = PowerSeries.constantCoeff f := by
  rw [PowerSeries.subst_def]
  have h : MvPowerSeries.HasSubst (fun _ : Unit ↦ g) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ hg)
  exact HasseWeil.FG.constantCoeff_subst_vanishing h (fun _ ↦ hg) f

/-- **Silverman IV.4.4**: In characteristic `p`, the multiplication-by-`p`
series of a formal group is a power series in `T^p`.

Concretely, there exists `g : PowerSeries R` with
`(F.mulByNatHom p).toSeries = g.expand p hp`, equivalently `[p](T) = g(T^p)`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.4.4. -/
theorem FormalGroup.mulByP_exists_expand (F : FormalGroup R) (p : ℕ)
    [hp_prime : Fact p.Prime] [CharP R p] :
    ∃ g : PowerSeries R, (F.mulByNatHom p).toSeries =
      g.expand p hp_prime.out.ne_zero := by
  apply exists_expand_of_coeff_vanishing p hp_prime.out.ne_zero
  intro n hpn
  -- `derivative [p] = 0`, from the chain rule and `[p] = 0` in characteristic `p`.
  have hder : PowerSeries.derivative R (F.mulByNatHom p).toSeries = 0 := by
    have chain := FormalGroupHom.invariantDifferential_chain (F.mulByNatHom p)
    have hp_zero :
        PowerSeries.C (PowerSeries.coeff 1 (F.mulByNatHom p).toSeries) *
          F.normalizedDifferential.toSeries = 0 := by
      rw [F.coeff_one_mulByNatHom p, CharP.cast_eq_zero R p, map_zero, zero_mul]
    rw [hp_zero] at chain
    -- `subst [p] ω_F` is a unit (constant coefficient `1`), so `derivative [p] = 0`.
    have hunit : IsUnit (PowerSeries.subst (F.mulByNatHom p).toSeries
        F.normalizedDifferential.toSeries) := by
      rw [PowerSeries.isUnit_iff_constantCoeff,
        constantCoeff_subst_zero_const _ (F.mulByNatHom p).zero_const]
      change IsUnit (@PowerSeries.constantCoeff R _ F.invariantDiff)
      rw [F.invariantDiff_constantCoeff]
      exact isUnit_one
    exact hunit.mul_right_eq_zero.mp chain
  exact coeff_eq_zero_of_derivative_eq_zero_charP hder n hpn

/-- **Silverman IV.4.4 (decomposition form)**: for a formal group over a ring of
characteristic `p`, `[p](T) = p·f(T) + g(T^p)` for some `f, g`. In characteristic
`p` the term `p·f` vanishes and we can take `f = 0`.

This mirrors the statement in Silverman, but the simpler form
`FormalGroup.mulByP_exists_expand` is usually more useful. -/
theorem FormalGroup.mulByP_decomposition (F : FormalGroup R) (p : ℕ)
    [hp_prime : Fact p.Prime] [CharP R p] :
    ∃ f g : PowerSeries R,
      (F.mulByNatHom p).toSeries =
        PowerSeries.C (p : R) * f + g.expand p hp_prime.out.ne_zero := by
  obtain ⟨g, hg⟩ := F.mulByP_exists_expand p
  exact ⟨0, g, by simpa using hg⟩

end HasseWeil.FormalGroup
