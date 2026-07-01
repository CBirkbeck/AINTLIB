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

/-- A power series with nonzero constant coefficient has order `0`. -/
private lemma order_eq_zero_of_constantCoeff_ne_zero {φ : PowerSeries R}
    (h : PowerSeries.constantCoeff φ ≠ 0) : PowerSeries.order φ = 0 := by
  refine le_antisymm ?_ (zero_le)
  have := PowerSeries.order_le (φ := φ) 0
    (by rwa [PowerSeries.coeff_zero_eq_constantCoeff])
  exact_mod_cast this

/-- Over a trivial ring, the substitution order identity holds because every
power series equals `0`, so both sides are `⊤`. -/
private lemma order_subst_of_subsingleton [Subsingleton R] (f g : PowerSeries R) :
    PowerSeries.order ((PowerSeries.subst f g : PowerSeries R)) = g.order * f.order := by
  have h0 : ∀ h : PowerSeries R, h = 0 := fun h ↦ by ext n; exact Subsingleton.elim _ _
  -- Every power series is `0`, hence of order `⊤`.
  have hord : ∀ h : PowerSeries R, PowerSeries.order h = ⊤ :=
    fun h ↦ by rw [h0 h]; exact PowerSeries.order_zero
  rw [hord ((PowerSeries.subst f g : PowerSeries R)), hord g, hord f]; simp

/-- The substitution order identity when the substituted series `g` is `0`:
the left side is `⊤` and `g.order = ⊤`, while `f.order ≠ 0` (as
`constantCoeff f = 0`), so the right side is `⊤ * f.order = ⊤`. -/
private lemma order_subst_of_eq_zero {f : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.order ((PowerSeries.subst f (0 : PowerSeries R) : PowerSeries R)) =
      (0 : PowerSeries R).order * f.order := by
  have hsub : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have hz : PowerSeries.subst f (0 : PowerSeries R) = 0 := by
    rw [← PowerSeries.coe_substAlgHom hsub]; exact map_zero _
  rw [show ((PowerSeries.subst f (0 : PowerSeries R)) : PowerSeries R) = 0 from hz,
      PowerSeries.order_zero]
  have hf_ord_ne_zero : PowerSeries.order f ≠ 0 := by
    rw [PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]; exact hf
  exact (ENat.top_mul hf_ord_ne_zero).symm

/-- The substitution order identity in the main case `g ≠ 0`. Writing
`n = g.order` and `g = X ^ n * divXPowOrder g`, substitution turns this into
`subst f g = f ^ n * subst f (divXPowOrder g)`. The cofactor
`subst f (divXPowOrder g)` has nonzero constant coefficient hence order `0`, so
`order (subst f g) = n • f.order = g.order * f.order`. -/
private lemma order_subst_of_ne_zero [NoZeroDivisors R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg0 : g ≠ 0) :
    PowerSeries.order ((PowerSeries.subst f g : PowerSeries R)) = g.order * f.order := by
  -- `g ≠ 0` forces `R` to be nontrivial (needed for `order_pow`).
  have : Nontrivial R := by
    refine not_subsingleton_iff_nontrivial.mp fun hs ↦ hg0 ?_
    ext n; exact Subsingleton.elim _ _
  have hsub : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  set n : ℕ := g.order.toNat with hn_def
  have hn_cast : (n : ℕ∞) = g.order := PowerSeries.coe_toNat_order hg0
  -- Decompose `subst f g` using `subst_mul`, `subst_pow`, `subst_X`.
  have h_decomp : (PowerSeries.subst f g : PowerSeries R) =
      f ^ n * ((PowerSeries.subst f (PowerSeries.divXPowOrder g)) : PowerSeries R) := by
    conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := g)]
    rw [PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub, PowerSeries.subst_X hsub]
  -- The cofactor has nonzero constant coefficient, hence order `0`.
  have h_sub_g'_cc :
      PowerSeries.constantCoeff
        ((PowerSeries.subst f (PowerSeries.divXPowOrder g)) : PowerSeries R) ≠ 0 := by
    rw [constantCoeff_subst_univariate hf, PowerSeries.constantCoeff_divXPowOrder]
    exact PowerSeries.coeff_order hg0
  rw [h_decomp, PowerSeries.order_mul, PowerSeries.order_pow,
      order_eq_zero_of_constantCoeff_ne_zero h_sub_g'_cc, add_zero, nsmul_eq_mul, ← hn_cast]

/-- **Order of a substitution**: for `f, g : R⟦X⟧` with `constantCoeff f = 0`
and `R` a commutative ring with no zero divisors,
`order (subst f g) = order g * order f`.

This is a strengthening of `PowerSeries.le_order_subst`, which only provides
the `≤` direction. The hypothesis `constantCoeff f = 0` is needed so that
the substitution is well-defined (`HasSubst f`). -/
theorem order_subst [NoZeroDivisors R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.order ((PowerSeries.subst f g : PowerSeries R)) = g.order * f.order := by
  -- Trivial ring: both sides are `⊤`.
  by_cases hRtriv : Subsingleton R
  · exact order_subst_of_subsingleton f g
  -- `g = 0`: left side is `⊤ = ⊤ * f.order`.
  by_cases hg0 : g = 0
  · subst hg0; exact order_subst_of_eq_zero hf
  -- `g ≠ 0`: decompose `g = X ^ g.order * divXPowOrder g` and substitute.
  · exact order_subst_of_ne_zero hf hg0

end PowerSeries
