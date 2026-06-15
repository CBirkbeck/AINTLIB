import HasseWeil.FormalGroup.CharP
import HasseWeil.FormalGroup.Hom
import HasseWeil.FormalGroup.OrderSubst
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Order

/-!
# Height of a formal group in characteristic `p` (Silverman IV.7)

For a nonzero formal group homomorphism `f : F → G` over a ring of prime
characteristic `p`, the **height** `h(f)` measures the "p-adic depth" of `f`:

* If `f = 0`, then `h(f) = ⊤`.
* Otherwise, `h(f)` is the largest `h` such that `p^h` divides the order of
  the underlying power series. Mathematically, for a nonzero formal group
  hom in char `p`, Silverman shows the order is always a power of `p`
  (proof not formalized here), and the height is that power's exponent.

We define the height directly as `padicValNat p (order f.toSeries).toNat`
when `f.toSeries` is nonzero, and `⊤` otherwise. This always yields the
correct value when the order is a `p`-power (which, by Silverman IV.7, is
the case for every nonzero formal group hom in char `p`).

## Main definitions

* `HasseWeil.FormalGroup.FormalGroupHom.height` — height of a formal group
  homomorphism.
* `HasseWeil.FormalGroup.FormalGroup.height` — height of a formal group,
  defined as the height of `[p]`.

## Main results

* `HasseWeil.FormalGroup.FormalGroupHom.height_comp` — height is additive
  under composition (Silverman IV.7).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], IV.7.
-/

set_option linter.dupNamespace false

namespace HasseWeil.FormalGroup

variable {R : Type*} [CommRing R]

/-- The **height** of a formal group homomorphism `f : F → G` over a ring of
prime characteristic `p`.

For a nonzero formal group hom `f` in char `p`, `order f.toSeries = p^h` and
the height is `h`. The definition uses `padicValNat` to extract the
`p`-adic exponent from the order; if `f = 0`, the height is `⊤`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.7. -/
noncomputable def FormalGroupHom.height {F G : FormalGroup R}
    (p : ℕ) (f : FormalGroupHom F G) : ℕ∞ :=
  f.toSeries.order.map (padicValNat p)

/-- The height of a zero formal group hom is `⊤`. -/
@[simp]
theorem FormalGroupHom.height_zero_toSeries {F G : FormalGroup R} (p : ℕ)
    (f : FormalGroupHom F G) (hf : f.toSeries = 0) :
    f.height p = ⊤ := by
  rw [FormalGroupHom.height, hf, PowerSeries.order_zero]; rfl

/-- The height of a formal group hom with nonzero underlying series is the
`p`-adic valuation of the series' order. -/
theorem FormalGroupHom.height_of_ne_zero {F G : FormalGroup R} (p : ℕ)
    (f : FormalGroupHom F G) (hf : f.toSeries ≠ 0) :
    f.height p = padicValNat p f.toSeries.order.toNat := by
  rw [FormalGroupHom.height]
  rw [← PowerSeries.coe_toNat_order hf]
  rfl

/-- The **height** of a formal group `F` over a ring of prime characteristic
`p`, defined as the height of the multiplication-by-`p` homomorphism.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, IV.7. -/
noncomputable def FormalGroup.height (F : FormalGroup R) (p : ℕ) : ℕ∞ :=
  (F.mulByNatHom p).height p

/-- `FormalGroup.height F p = FormalGroupHom.height p (mulByNatHom F p)`. -/
theorem FormalGroup.height_eq (F : FormalGroup R) (p : ℕ) :
    F.height p = (F.mulByNatHom p).height p :=
  rfl

/-! ### Height of a composition (Silverman IV.7 selected)

The key identity `h(g ∘ f) = h(f) + h(g)` follows from
`order (subst f.toSeries g.toSeries) = order g.toSeries * order f.toSeries`
(provided by `PowerSeries.order_subst` in
`HasseWeil/FormalGroup/OrderSubst.lean`), combined with the multiplicativity
of `padicValNat` at a prime. -/

/-- **Helper**: `ENat.map (padicValNat p)` distributes over multiplication in `ℕ∞`,
when both factors are nonzero and `p` is prime. -/
private theorem ENat.map_padicValNat_mul (p : ℕ) [Fact p.Prime] {a b : ℕ∞}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).map (padicValNat p) =
      a.map (padicValNat p) + b.map (padicValNat p) := by
  cases a with
  | top =>
    cases b with
    | top => simp
    | coe n =>
      rw [_root_.ENat.top_mul hb]
      simp
  | coe m =>
    cases b with
    | top =>
      rw [_root_.ENat.mul_top ha]
      simp
    | coe n =>
      have hm : m ≠ 0 := by
        intro h; apply ha; simp [h]
      have hn : n ≠ 0 := by
        intro h; apply hb; simp [h]
      rw [show ((m : ℕ∞) * (n : ℕ∞) : ℕ∞) = ((m * n : ℕ) : ℕ∞) from by push_cast; ring]
      rw [ENat.map_coe, ENat.map_coe, ENat.map_coe, _root_.padicValNat.mul hm hn]
      push_cast
      rfl

/-- **Silverman IV.7 (selected)**: the height of a composition is the sum of heights.

For formal group homomorphisms `f : F → G` and `g : G → H` over a commutative
ring `R` with no zero divisors, and a prime `p`,
`(g ∘ f).height p = f.height p + g.height p`.

The proof uses `PowerSeries.order_subst` to reduce to the multiplicativity of
`padicValNat` at a prime. -/
theorem FormalGroupHom.height_comp {F G H : FormalGroup R} [NoZeroDivisors R]
    (p : ℕ) [Fact p.Prime]
    (g : FormalGroupHom G H) (f : FormalGroupHom F G) :
    (g.comp f).height p = f.height p + g.height p := by
  -- (g.comp f).toSeries = subst f.toSeries g.toSeries.
  -- height = order.map (padicValNat p).
  unfold FormalGroupHom.height
  rw [FormalGroupHom.comp_toSeries]
  -- Convert `MvPowerSeries.order` to `PowerSeries.order` on the LHS.
  change ENat.map _ (PowerSeries.order _) = _
  rw [PowerSeries.order_subst f.zero_const]
  -- Goal: (g.toSeries.order * f.toSeries.order).map (padicValNat p)
  --     = f.toSeries.order.map (padicValNat p) + g.toSeries.order.map (padicValNat p)
  rw [ENat.map_padicValNat_mul p
    (by rw [PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]; exact g.zero_const)
    (by rw [PowerSeries.order_ne_zero_iff_constCoeff_eq_zero]; exact f.zero_const)]
  -- Goal: g.order.map ... + f.order.map ... = f.order.map ... + g.order.map ...
  exact add_comm _ _

end HasseWeil.FormalGroup
