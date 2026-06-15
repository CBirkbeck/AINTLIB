import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Order of a power series substitution

For a univariate power series `g : R⟦X⟧` and a univariate power series
`f : R⟦X⟧` with vanishing constant coefficient, the order of the substitution
`PowerSeries.subst f g` is the product of the orders:

`order (subst f g) = order g * order f`.

The hypothesis `constantCoeff f = 0` is essential so that `subst f g` is
well-defined (`HasSubst f`). No hypothesis on `g` is needed (we case-split on
whether `g = 0` or `constantCoeff g = 0`).

This complements `PowerSeries.le_order_subst` in mathlib, which provides only
the inequality `order g * order f ≤ order (subst f g)`.

## Main result

* `PowerSeries.order_subst` — the order of a substitution (equality, under
  `[NoZeroDivisors R]`).

## References

This is used to prove additivity of the height of a composition of formal
group homomorphisms (Silverman IV.7).
-/

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The constant coefficient of `PowerSeries.subst f g` equals `constantCoeff g`
when `constantCoeff f = 0`. -/
private lemma constantCoeff_subst_univariate
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) (g : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.subst f g) = PowerSeries.constantCoeff g := by
  have hsub : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_subst' hsub g 0,
      finsum_eq_single _ 0]
  · simp
  · intro d hd
    have hc : PowerSeries.coeff 0 (f ^ d) = (0 : R) := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hf, zero_pow hd]
    rw [hc, smul_zero]

/-- **Order of a substitution**: for `f, g : R⟦X⟧` with `constantCoeff f = 0`
and `R` a commutative ring with no zero divisors,
`order (subst f g) = order g * order f`.

This is a strengthening of `PowerSeries.le_order_subst`, which only provides
the `≤` direction. The hypothesis `constantCoeff f = 0` is needed so that
the substitution is well-defined (`HasSubst f`). -/
theorem order_subst [NoZeroDivisors R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.order ((PowerSeries.subst f g : PowerSeries R)) = g.order * f.order := by
  -- `HasSubst` instance for `f`.
  have hsub : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf
  -- Handle trivial ring case uniformly.
  by_cases hRtriv : Subsingleton R
  · have h0 : ∀ (h : PowerSeries R), h = 0 := by
      intro h; ext n; exact Subsingleton.elim _ _
    -- Both sides are `⊤`, since every power series equals `0`.
    have hlhs :
        PowerSeries.order ((PowerSeries.subst f g : PowerSeries R)) = ⊤ := by
      rw [h0 ((PowerSeries.subst f g : PowerSeries R))]; exact PowerSeries.order_zero
    have hrhs_g : PowerSeries.order g = ⊤ := by rw [h0 g]; exact PowerSeries.order_zero
    have hrhs_f : PowerSeries.order f = ⊤ := by rw [h0 f]; exact PowerSeries.order_zero
    rw [hlhs, hrhs_g, hrhs_f]; simp
  -- Now `R` is nontrivial.
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp hRtriv
  -- Case on whether `g = 0`.
  by_cases hg0 : g = 0
  · subst hg0
    have hz : PowerSeries.subst f (0 : PowerSeries R) = 0 := by
      rw [← PowerSeries.coe_substAlgHom hsub]; exact map_zero _
    have hlhs :
        PowerSeries.order ((PowerSeries.subst f (0 : PowerSeries R)) : PowerSeries R) = ⊤ := by
      rw [show ((PowerSeries.subst f (0 : PowerSeries R)) : PowerSeries R) = 0 from hz]
      exact PowerSeries.order_zero
    rw [hlhs]
    rw [show PowerSeries.order (0 : PowerSeries R) = ⊤ from PowerSeries.order_zero]
    have hf_ord_ne_zero : PowerSeries.order f ≠ 0 := by
      rw [PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]; exact hf
    exact (ENat.top_mul hf_ord_ne_zero).symm
  -- Case on whether `constantCoeff g = 0`.
  by_cases hcg : PowerSeries.constantCoeff g = 0
  · -- Main case: `g ≠ 0` and `constantCoeff g = 0`.
    set n : ℕ := g.order.toNat with hn_def
    have hn_cast : (n : ℕ∞) = g.order := PowerSeries.coe_toNat_order hg0
    -- Decompose subst f g using subst_mul, subst_pow, subst_X.
    have h_decomp : (PowerSeries.subst f g : PowerSeries R) =
        f ^ n * ((PowerSeries.subst f (PowerSeries.divXPowOrder g)) : PowerSeries R) := by
      conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := g)]
      rw [PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
          PowerSeries.subst_X hsub]
    have h_g'_cc : PowerSeries.constantCoeff (PowerSeries.divXPowOrder g) ≠ 0 := by
      rw [PowerSeries.constantCoeff_divXPowOrder]
      exact PowerSeries.coeff_order hg0
    have h_sub_g'_cc :
        PowerSeries.constantCoeff
          ((PowerSeries.subst f (PowerSeries.divXPowOrder g)) : PowerSeries R) ≠ 0 := by
      rw [constantCoeff_subst_univariate hf]; exact h_g'_cc
    have h_sub_g'_order :
        PowerSeries.order
            ((PowerSeries.subst f (PowerSeries.divXPowOrder g)) : PowerSeries R) = 0 := by
      apply le_antisymm _ (zero_le)
      have := PowerSeries.order_le (φ := ((PowerSeries.subst f (PowerSeries.divXPowOrder g))
          : PowerSeries R)) 0 (by rwa [PowerSeries.coeff_zero_eq_constantCoeff])
      exact_mod_cast this
    rw [h_decomp, PowerSeries.order_mul, PowerSeries.order_pow, h_sub_g'_order,
        add_zero, nsmul_eq_mul, ← hn_cast]
  · -- Case: `g ≠ 0` and `constantCoeff g ≠ 0`. Then `g.order = 0`, both sides 0.
    have h_sub_cc :
        PowerSeries.constantCoeff ((PowerSeries.subst f g) : PowerSeries R) ≠ 0 := by
      rw [constantCoeff_subst_univariate hf]; exact hcg
    have h_sub_order :
        PowerSeries.order ((PowerSeries.subst f g) : PowerSeries R) = 0 := by
      apply le_antisymm _ (zero_le)
      have := PowerSeries.order_le (φ := ((PowerSeries.subst f g) : PowerSeries R)) 0
        (by rwa [PowerSeries.coeff_zero_eq_constantCoeff])
      exact_mod_cast this
    have h_g_order : PowerSeries.order g = 0 := by
      apply le_antisymm _ (zero_le)
      have := PowerSeries.order_le (φ := g) 0 (by rwa [PowerSeries.coeff_zero_eq_constantCoeff])
      exact_mod_cast this
    rw [h_sub_order, h_g_order, zero_mul]

end PowerSeries
