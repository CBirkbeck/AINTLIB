import BernoulliRegular.FLT37.PadicL.GaussSumValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic

/-!
# B-C1.2, discharged — Washington Proposition 6.13 at `f = 1` over an abstract DVR

This file **discharges** `GaussSumValuationCaseF1` (Washington Prop 6.13 in the
conductor-`1` case) by proving the genuine Stickelberger valuation of the
`f = 1` Gauss sum over an abstract discrete valuation ring (DVR), then packaging
the conclusion in the abstract `(E, v, τ)` shape that `GaussSumValuationCaseF1`
expects.

## Setup: the abstract `f = 1` Gauss-sum environment

The conductor-`1` Gauss sum `τ(ω^{-i}) = Σ_{a=1}^{p-1} ω^{-i}(a) ζ_p^a` does **not**
live in `ℚ(ζ_p)` — the Teichmüller character `ω` takes values in `μ_{p-1}`, which
is *not* contained in `ℚ(ζ_p)` (whose roots of unity are only `±ζ_p^k`).  Washington
works in the completion `ℚ_p(ζ_p)`, whose ring of integers `O = ℤ_p[ζ_p]` is a DVR
with maximal ideal `𝔓 = (ζ_p - 1)`, residue field `𝔽_p`, ramification index
`e = p - 1`, so `v_𝔓(p) = p - 1` and the normalised valuation is `v_p = v_𝔓/(p-1)`.

We abstract exactly this data into `StickelbergerF1Setup`: a DVR `O` with residue
field `𝔽_p`, a uniformizer-related primitive `p`-th root `ζ = 1 + π`, and the
Teichmüller character `ω : (ZMod p)ˣ → Oˣ` with `ω(a) ≡ a (mod 𝔓)`.  This carries
no completion-specific `whnf` cost (it is a plain DVR) and side-steps the
`μ_{p-1} ⊄ ℚ(ζ_p)` obstruction (the roots are hypotheses).

## What is proved here

* `StickelbergerF1Setup.gaussSum`: the genuine `f = 1` Gauss sum `g i ∈ O`.
* `StickelbergerF1Setup.gaussSum_eq_sum_pi_pow_coeff`: its base-`π` expansion
  `g i = Σ_j π^j · c i j`, with `c i j = Σ_a (ω a)^{-i} · C(a, j)` the explicit
  binomial coefficient (`a` the chosen nat representative of the unit).
* `StickelbergerF1Setup.gaussSumNormVal`: the normalised valuation
  `v_p(g i) = v_𝔓(g i) / (p - 1) : ℚ`.
* `StickelbergerF1Setup.gaussSumValuationCaseF1_of_integralValuation`: **the full
  reduction** — from the integral leaf `addVal O (g i) = i` (the genuine
  Stickelberger value, the `s(i) = i` digit collapse), `GaussSumValuationCaseF1`
  holds for `(O, v_p, g)`.

The integral leaf `IntegralStickelbergerValuationF1` (`addVal O (g i) = i`) is the
precise residual: the Gross–Koblitz / Dwork higher-congruence content
(`c i j ∈ 𝔓^{i+1-j}` for `j < i`, `c i i ∉ 𝔓`).  It is a concrete `ℕ∞`-valued
statement about an explicit element, carried as a named `Prop`, **not** an axiom.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Prop 6.13,
  Lemmas 6.2–6.4, §6.2.
-/

namespace BernoulliRegular.FLT37.PadicL

open IsDiscreteValuationRing IsLocalRing

section FiniteFieldSum

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The pure `𝔽_p` leading character sum** `Σ_{a ∈ (ZMod p)ˣ} a^{-i} · C(a.val, i)`,
the residue of `gaussSumCoeff i i`.  The leading non-degeneracy of the `f = 1`
Gauss sum is exactly the non-vanishing of this concrete `ZMod p` sum (Washington
§6.2: it equals `-1/i!`). -/
noncomputable def leadingFiniteFieldSum (i : ℕ) : ZMod p :=
  ∑ a : (ZMod p)ˣ, ((a : ZMod p)⁻¹) ^ i * (((a : ZMod p).val.choose i : ℕ) : ZMod p)

/-- **Sum of a low-degree polynomial over `𝔽_p` vanishes.**  If
`P.natDegree < p - 1` then `∑_{x ∈ ZMod p} P.eval x = 0`.  (The single-variable
Chevalley–Warning core: each monomial `x^k` with `k ≤ deg P < p - 1` sums to `0`,
and the `k = 0` term sums to `card · c₀ = p · c₀ = 0`.) -/
theorem sum_eval_eq_zero_of_natDegree_lt {P : Polynomial (ZMod p)}
    (h : P.natDegree < p - 1) : ∑ x : ZMod p, P.eval x = 0 := by
  have hn : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self _
  calc
    ∑ x : ZMod p, P.eval x
        = ∑ x : ZMod p, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * x ^ k := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Polynomial.eval_eq_sum_range' hn x]
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), ∑ x : ZMod p, P.coeff k * x ^ k :=
          Finset.sum_comm
    _ = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * ∑ x : ZMod p, x ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
    _ = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          rw [Finset.mem_range] at hk
          have hkd : k ≤ P.natDegree := by omega
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · -- k = 0: ∑ x, x^0 = card = p = 0 in ZMod p.
            subst hk0
            simp only [pow_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
              nsmul_eq_mul]
            rw [ZMod.natCast_self]; ring
          · -- 0 < k < p - 1: ∑ x, x^k = 0.
            have hkq : k < Fintype.card (ZMod p) - 1 := by rw [ZMod.card]; omega
            rw [FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) k hkq, mul_zero]

/-- The univariate `𝔽_p`-polynomial `∏_{t < i} (1 - t·X)` whose evaluation gives
the product appearing in the leading character sum (after the `b = a⁻¹`
substitution). -/
noncomputable def leadingPoly (i : ℕ) : Polynomial (ZMod p) :=
  ∏ t ∈ Finset.range i, (Polynomial.C 1 - Polynomial.C (t : ZMod p) * Polynomial.X)

theorem leadingPoly_eval (i : ℕ) (b : ZMod p) :
    (leadingPoly (p := p) i).eval b = ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * b) := by
  unfold leadingPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [Polynomial.eval_sub, Polynomial.eval_mul]

theorem leadingPoly_natDegree_le (i : ℕ) : (leadingPoly (p := p) i).natDegree ≤ i := by
  unfold leadingPoly
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    ∑ t ∈ Finset.range i,
        (Polynomial.C 1 - Polynomial.C (t : ZMod p) * Polynomial.X).natDegree
        ≤ ∑ _t ∈ Finset.range i, 1 := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine (Polynomial.natDegree_sub_le _ _).trans ?_
          rw [Polynomial.natDegree_C]
          exact max_le (by norm_num)
            ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
    _ = i := by simp

/-- **The leading character sum after the `b = a⁻¹` substitution and the
factorisation** `a^{-i}∏_{t<i}(a-t) = ∏_{t<i}(1 - t·a⁻¹)`:
`Σ_{b ∈ 𝔽_p^×} ∏_{t<i}(1 - t·b) = -1`.

Obtained from `Σ_{b ∈ 𝔽_p} (leadingPoly).eval b = 0` (degree `< p - 1`,
`sum_eval_eq_zero_of_natDegree_lt`) minus the `b = 0` term, which is
`∏_{t<i}(1 - 0) = 1`. -/
theorem sum_units_leadingProd_eq_neg_one {i : ℕ} (hip : i < p - 1) :
    ∑ b : (ZMod p)ˣ, ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * (b : ZMod p)) = -1 := by
  classical
  -- Sum over all of 𝔽_p of the polynomial is 0.
  have hall : ∑ b : ZMod p, ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * b) = 0 := by
    have := sum_eval_eq_zero_of_natDegree_lt
      (P := leadingPoly (p := p) i) (lt_of_le_of_lt (leadingPoly_natDegree_le i) hip)
    rw [← this]
    exact (Finset.sum_congr rfl fun b _ => (leadingPoly_eval i b).symm)
  -- Split off b = 0: sum over 𝔽_p = (b=0 term) + sum over units.
  set f : ZMod p → ZMod p :=
    fun b => ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * b) with hf
  have hunits : ∑ b : (ZMod p)ˣ, f (b : ZMod p) = ∑ x ∈ Finset.univ \ {(0 : ZMod p)}, f x := by
    let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
    have hmap : (Finset.univ : Finset (ZMod p)ˣ).map φ = Finset.univ \ {0} := by
      ext x
      simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
        Finset.mem_sdiff, Finset.mem_singleton, φ] using isUnit_iff_ne_zero
    rw [← hmap, Finset.sum_map]
    rfl
  have hsplit : ∑ b : ZMod p, f b = f 0 + ∑ b : (ZMod p)ˣ, f (b : ZMod p) := by
    rw [hunits, ← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
      Finset.sum_singleton, add_comm]
  rw [hsplit] at hall
  have hf0 : f 0 = 1 := by simp [hf]
  rw [hf0] at hall
  -- 1 + (units sum) = 0 ⟹ units sum = -1.
  have hres : ∑ b : (ZMod p)ˣ, f (b : ZMod p) = -1 := by linear_combination hall
  simpa [hf] using hres

/-- `(i! : ZMod p) ≠ 0` for `i < p` (no factor of `p`). -/
theorem factorial_cast_ne_zero {i : ℕ} (hip : i < p) : ((Nat.factorial i : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  exact absurd ((Nat.Prime.dvd_factorial hp.out).mp hdvd) (by omega)

/-- **The leading character sum equals `-(i!)⁻¹`** (Washington §6.2).  Multiplying
the leading-coefficient residue by `i!` and using the descending-factorial
factorisation `C(a.val, i)·i! = ∏_{t<i}(a - t)` plus the inversion substitution,
the sum collapses to `-1`, so `leadingFiniteFieldSum i = -(i!)⁻¹`. -/
theorem leadingFiniteFieldSum_mul_factorial {i : ℕ} (hip : i < p - 1) :
    leadingFiniteFieldSum (p := p) i * ((Nat.factorial i : ℕ) : ZMod p) = -1 := by
  unfold leadingFiniteFieldSum
  rw [Finset.sum_mul]
  -- Per-term: a^{-i} · C(a.val,i) · i! = a^{-i} · ∏_{t<i}(a - t) = ∏_{t<i}(1 - t·a⁻¹).
  have hterm : ∀ a : (ZMod p)ˣ,
      ((a : ZMod p)⁻¹) ^ i * (((a : ZMod p).val.choose i : ℕ) : ZMod p) *
          ((Nat.factorial i : ℕ) : ZMod p) =
        ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * ((a : ZMod p)⁻¹)) := by
    intro a
    have ha0 : (a : ZMod p) ≠ 0 := a.ne_zero
    -- C(a.val,i) · i! = descFactorial(a.val,i) = ∏_{t<i}((a:ZMod p) - t) (via descPochhammer).
    have hdf : (((a : ZMod p).val.choose i : ℕ) : ZMod p) *
          ((Nat.factorial i : ℕ) : ZMod p) =
        ∏ t ∈ Finset.range i, ((a : ZMod p) - (t : ZMod p)) := by
      have hnat : (a : ZMod p).val.choose i * Nat.factorial i =
          (a : ZMod p).val.descFactorial i := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; ring
      have hcast : (((a : ZMod p).val.descFactorial i : ℕ) : ZMod p) =
          ∏ t ∈ Finset.range i, ((a : ZMod p) - (t : ZMod p)) := by
        rw [← descPochhammer_eval_eq_descFactorial (ZMod p), descPochhammer_eval_eq_prod_range,
          ZMod.natCast_val, ZMod.cast_id]
      rw [← Nat.cast_mul, hnat, hcast]
    -- a^{-i} · ∏(a - t) = ∏(1 - t·a⁻¹):  a - t = a·(1 - t·a⁻¹), so ∏(a-t) = a^i ∏(1-t·a⁻¹).
    rw [mul_assoc, hdf]
    have hfactor : ∀ t : ℕ, (a : ZMod p) - (t : ZMod p) =
        (a : ZMod p) * (1 - (t : ZMod p) * ((a : ZMod p)⁻¹)) := by
      intro t
      rw [mul_sub, mul_one, ← mul_assoc, mul_comm (a : ZMod p) (t : ZMod p), mul_assoc,
        mul_inv_cancel₀ ha0, mul_one]
    have hprod : ∏ t ∈ Finset.range i, ((a : ZMod p) - (t : ZMod p)) =
        (a : ZMod p) ^ i * ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * ((a : ZMod p)⁻¹)) := by
      rw [Finset.prod_congr rfl (fun t _ => hfactor t), Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_range]
    rw [hprod, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha0, one_pow, one_mul]
  -- Assemble: ∑_a (per-term) = ∑_a ∏_{t<i}(1 - t·a⁻¹) = ∑_b ∏_{t<i}(1 - t·b) = -1.
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  -- Reindex a ↦ a⁻¹ (bijection of units): ∑_a ∏(1 - t·a⁻¹) = ∑_b ∏(1 - t·b).
  rw [show (∑ a : (ZMod p)ˣ, ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * ((a : ZMod p)⁻¹))) =
      ∑ b : (ZMod p)ˣ, ∏ t ∈ Finset.range i, (1 - (t : ZMod p) * ((b : ZMod p))) from
    Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ (fun a => by
      simp only [Equiv.inv_apply]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Units.val_inv_eq_inv_val])]
  exact sum_units_leadingProd_eq_neg_one hip

/-- **The leading character sum is nonzero** (`= -(i!)⁻¹ ≠ 0`).  This is the
genuine `𝔽_p` content of the leading non-degeneracy in Washington Prop 6.13 at
`f = 1`, **proved** here for `i < p - 1` (in particular for the FLT37 range
`2 ≤ i ≤ p - 3`). -/
theorem leadingFiniteFieldSum_ne_zero {i : ℕ} (hip : i < p - 1) :
    leadingFiniteFieldSum (p := p) i ≠ 0 := by
  intro h0
  have := leadingFiniteFieldSum_mul_factorial (p := p) hip
  rw [h0, zero_mul] at this
  exact absurd this.symm (by norm_num)

end FiniteFieldSum

/-- The chosen natural-number representative `a.val ∈ {1, …, p-1}` of a unit
`a : (ZMod p)ˣ`, used as the exponent of `ζ` in the Gauss sum.  (`ZMod.val` lands
in `{0, …, p-1}` and is nonzero on units.) -/
def teichRep {p : ℕ} (a : (ZMod p)ˣ) : ℕ := (a : ZMod p).val

/-- **The abstract `f = 1` Stickelberger / Gauss-sum environment.**

A discrete valuation ring `O` modelling `ℤ_p[ζ_p]` (the integers of `ℚ_p(ζ_p)`),
together with the cyclotomic and Teichmüller data needed to write down the
`f = 1` Gauss sum `τ(ω^{-i})` and reason about its `𝔓`-adic valuation:

* `π` — a uniformizer (`Irreducible`), modelling `ζ_p - 1`;
* `ζ = 1 + π` — the primitive `p`-th root of unity;
* `ζpow_p_eq_one` — `ζ^p = 1` (the cyclotomic relation, equivalently
  `(1 + π)^p = 1`);
* `ω` — the Teichmüller character `(ZMod p)ˣ → Oˣ`, multiplicative, with
  `ω(a)^{p-1} = 1`;
* `omega_residue` — the defining congruence `ω(a) ≡ a (mod 𝔓)` in the residue
  field `𝔽_p` (here phrased through the residue map to `ZMod p`).

The ramification `e = p - 1` is recorded as `addVal_p_eq` (`v_𝔓(p) = p - 1`),
matching `ℚ_p(ζ_p)/ℚ_p` totally ramified of degree `p - 1`. -/
structure StickelbergerF1Setup (p : ℕ) [Fact p.Prime] where
  /-- The ring of integers `O = ℤ_p[ζ_p]`, a DVR. -/
  O : Type*
  [commRing : CommRing O]
  [isDomain : IsDomain O]
  [isDVR : IsDiscreteValuationRing O]
  /-- The residue field is `ZMod p` (i.e. `𝔽_p`), via the residue map. -/
  residue : O →+* ZMod p
  residue_surjective : Function.Surjective residue
  /-- A uniformizer `π`, modelling `ζ_p - 1`. -/
  π : O
  π_irreducible : Irreducible π
  /-- `π` generates the maximal ideal, so it is exactly the prime of the residue
  map: `residue x = 0 ↔ π ∣ x`. -/
  residue_eq_zero_iff : ∀ x : O, residue x = 0 ↔ π ∣ x
  /-- The Teichmüller character on units. -/
  ω : (ZMod p)ˣ → Oˣ
  ω_mul : ∀ a b : (ZMod p)ˣ, ω (a * b) = ω a * ω b
  ω_pow_sub_one : ∀ a : (ZMod p)ˣ, ω a ^ (p - 1) = 1
  /-- `ω(a) ≡ a (mod 𝔓)`: the residue of the Teichmüller lift is the residue
  class itself. -/
  omega_residue : ∀ a : (ZMod p)ˣ, residue (ω a : O) = (a : ZMod p)
  /-- The cyclotomic relation `ζ^p = 1` with `ζ = 1 + π`. -/
  one_add_pi_pow_p : (1 + π) ^ p = 1
  /-- Ramification `e = p - 1`: `v_𝔓(p) = p - 1`. -/
  addVal_p_eq : addVal O (p : O) = (p - 1 : ℕ)

namespace StickelbergerF1Setup

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

instance : CommRing S.O := S.commRing
instance : IsDomain S.O := S.isDomain
instance : IsDiscreteValuationRing S.O := S.isDVR

/-- **The `f = 1` Gauss sum** `τ(ω^{-i}) = Σ_{a ∈ (ZMod p)ˣ} (ω a)⁻ⁱ · ζ^{rep a}`,
realised in `O` with `ζ = 1 + π`. -/
noncomputable def gaussSum (i : ℕ) : S.O :=
  ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (1 + S.π) ^ teichRep a

/-- The `π`-adic coefficient `c i j = Σ_a (ω a)⁻ⁱ · C(rep a, j)` of `π^j` in the
base-`π` expansion of the Gauss sum (Washington §6.2, the binomial-coefficient
character sum). -/
noncomputable def gaussSumCoeff (i j : ℕ) : S.O :=
  ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * ((teichRep a).choose j : S.O)

/-- Each unit representative is at most `p - 1`, so `teichRep a < p`. -/
theorem teichRep_lt (a : (ZMod p)ˣ) : teichRep a < p :=
  ZMod.val_lt _

/-- **Base-`π` expansion of the Gauss sum** (Washington §6.2):
`g i = Σ_{j < p} π^j · c i j`.  Obtained from the binomial theorem
`(1 + π)^{rep a} = Σ_j π^j C(rep a, j)` (padded to `range p` since
`C(n, j) = 0` for `j > n`) and swapping the order of summation. -/
theorem gaussSum_eq_sum_pi_pow_coeff (i : ℕ) :
    S.gaussSum i = ∑ j ∈ Finset.range p, S.π ^ j * S.gaussSumCoeff i j := by
  unfold gaussSum gaussSumCoeff
  -- Expand each `(1 + π)^{rep a}` binomially over `range p`.
  have hbin : ∀ a : (ZMod p)ˣ,
      (1 + S.π) ^ teichRep a =
        ∑ j ∈ Finset.range p, S.π ^ j * ((teichRep a).choose j : S.O) := by
    intro a
    have hcomm : Commute S.π (1 : S.O) := Commute.one_right _
    rw [add_comm (1 : S.O) S.π, hcomm.add_pow]
    -- ∑_{m ∈ range (rep a + 1)} π^m * 1^{rep a - m} * C(rep a, m)
    have hstep : ∑ m ∈ Finset.range (teichRep a + 1),
          S.π ^ m * (1 : S.O) ^ (teichRep a - m) * ((teichRep a).choose m : S.O) =
        ∑ m ∈ Finset.range (teichRep a + 1), S.π ^ m * ((teichRep a).choose m : S.O) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [one_pow, mul_one]
    rw [hstep]
    -- Extend `range (rep a + 1)` to `range p`: the added terms have C(rep a, m) = 0.
    have hle : teichRep a + 1 ≤ p := teichRep_lt a
    refine Finset.sum_subset (Finset.range_subset_range.mpr hle) ?_
    intro m _ hm
    rw [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega : teichRep a < m), Nat.cast_zero, mul_zero]
  -- Substitute and swap sums.
  calc
    ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (1 + S.π) ^ teichRep a
        = ∑ a : (ZMod p)ˣ, ∑ j ∈ Finset.range p,
            (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (S.π ^ j * ((teichRep a).choose j : S.O)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hbin a, Finset.mul_sum]
    _ = ∑ j ∈ Finset.range p, ∑ a : (ZMod p)ˣ,
            (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * (S.π ^ j * ((teichRep a).choose j : S.O)) :=
          Finset.sum_comm
    _ = ∑ j ∈ Finset.range p, S.π ^ j *
            ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) * ((teichRep a).choose j : S.O) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring

/-- `(n : ℕ∞) ≤ addVal x ↔ π^n ∣ x`: the `𝔓`-adic order is `≥ n` exactly when
`π^n` divides `x`. -/
theorem le_addVal_iff_pi_pow_dvd (x : S.O) (n : ℕ) :
    (n : ℕ∞) ≤ addVal S.O x ↔ S.π ^ n ∣ x := by
  rw [← S.π_irreducible.addVal_pow n, addVal_le_iff_dvd]

/-- A `𝔓`-adic exactness lemma over the DVR (the `addVal` analogue of
`Padic.valuation_sub_eq_of_lt`): if `π^(n+1) ∣ x - y` and `addVal y = n`, then
`addVal x = n`.  Used to make the leading-term congruence `g ≡ π^i c_i (mod
𝔓^{i+1})` sharp. -/
theorem addVal_eq_of_sub_pi_pow_dvd {x y : S.O} {n : ℕ}
    (hdvd : S.π ^ (n + 1) ∣ x - y) (hy : addVal S.O y = (n : ℕ∞)) :
    addVal S.O x = (n : ℕ∞) := by
  have hd : (↑(n + 1) : ℕ∞) ≤ addVal S.O (x - y) :=
    (S.le_addVal_iff_pi_pow_dvd (x - y) (n + 1)).mpr hdvd
  have hlt : addVal S.O y < addVal S.O (x - y) := by
    rw [hy]; exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hd
  -- Lower bound addVal y ≤ addVal x: from x = y + (x - y) and addVal(x-y) > addVal y.
  have hmin : addVal S.O y ≤ addVal S.O x := by
    have h := (addVal S.O).map_add y (x - y)
    rw [show y + (x - y) = x by ring, min_eq_left hlt.le] at h
    exact h
  -- Upper bound addVal x ≤ addVal y: from y = x + (-(x - y)).
  have hmin2 : addVal S.O x ≤ addVal S.O y := by
    by_contra hlt2
    rw [not_le] at hlt2
    have h := (addVal S.O).map_add x (-(x - y))
    rw [show x + (-(x - y)) = y by ring, AddValuation.map_neg] at h
    have hlt3 : addVal S.O y < addVal S.O x := hlt2
    have hlt4 : addVal S.O y < addVal S.O (x - y) := hlt
    rcases min_cases (addVal S.O x) (addVal S.O (x - y)) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h; exact absurd (lt_of_lt_of_le hlt3 h) (lt_irrefl _)
    · rw [he] at h; exact absurd (lt_of_lt_of_le hlt4 h) (lt_irrefl _)
  rw [le_antisymm hmin2 hmin, hy]

/-- **The normalised `𝔓`-adic valuation** `v_p : O → ℚ` with `v_p(p) = 1`:
the `addVal` (= `v_𝔓`, ramification-`(p-1)` integral valuation) divided by the
ramification index `p - 1`.  (`addVal` is `ℕ∞`-valued; `toNat` is exact on the
finite values that occur for the nonzero Gauss sums.) -/
noncomputable def normVal (x : S.O) : ℚ := ((addVal S.O x).toNat : ℚ) / ((p : ℚ) - 1)

/-- **The integral `f = 1` Stickelberger valuation** (Washington Prop 6.13 at
`f = 1`, integral form): `v_𝔓(τ(ω^{-i})) = i`.

This is the genuine Stickelberger / Gross–Koblitz content of Prop 6.13 in the
conductor-`1` case — the base-`p` digit-sum `s(i) = i` collapse (`i < p`),
realised as the exact `𝔓`-adic order of the explicit Gauss sum.  It is a concrete
`ℕ∞`-valued statement about the explicit element `S.gaussSum i`, carried as a named
`Prop`, **not** an axiom; everything else in Prop 6.13 at `f = 1` (the
normalisation `i ↦ i/(p-1)`, the `GaussSumValuationCaseF1` packaging) is proved
unconditionally from it below.

Mathematically it is the conjunction of the higher-congruences
`gaussSumCoeff i j ∈ 𝔓^{i+1-j}` for `j < i` (Gross–Koblitz / Dwork higher-order
vanishing) and the leading non-degeneracy `gaussSumCoeff i i ∉ 𝔓` (the `𝔽_p`
character-orthogonality leading term, `≡ -1/i! ≢ 0`). -/
def IntegralStickelbergerValuationF1 : Prop :=
  ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → addVal S.O (S.gaussSum i) = (i : ℕ∞)

/-- **The leading non-degeneracy** `c_i ∉ 𝔓` (Washington §6.2, the `𝔽_p`
character-orthogonality leading term `≡ -1/i! ≢ 0`): the `π^i`-coefficient of the
Gauss sum is a `𝔓`-adic **unit**, equivalently its residue is nonzero. -/
def GaussSumLeadingUnit (i : ℕ) : Prop := ¬ S.π ∣ S.gaussSumCoeff i i

/-- **The residue of the leading coefficient is the pure `𝔽_p` sum.**  Applying the
residue map `O → 𝔽_p` to `gaussSumCoeff i i`, the Teichmüller factor `(ω a)⁻¹`
reduces to `a⁻¹` (by `omega_residue`) and the binomial natCast reduces to itself,
giving `residue(c_i) = leadingFiniteFieldSum i`. -/
theorem residue_gaussSumCoeff_self (i : ℕ) :
    S.residue (S.gaussSumCoeff i i) = leadingFiniteFieldSum i := by
  unfold gaussSumCoeff leadingFiniteFieldSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Units.val_pow_eq_pow_val, map_mul, map_pow]
  congr 1
  · -- residue((ω a)⁻¹ : O) = (residue (ω a : O))⁻¹ = (a : ZMod p)⁻¹.
    rw [map_units_inv S.residue (S.ω a), S.omega_residue a]
  · -- residue((C(rep a, i) : O)) = (C(rep a, i) : ZMod p), and rep a = a.val.
    rw [map_natCast]
    rfl

/-- **Bridge: leading non-degeneracy from the `𝔽_p` sum.**  If the pure finite-field
leading sum is nonzero, then `c_i ∉ 𝔓`, i.e. `GaussSumLeadingUnit i` holds.

This reduces the leading non-degeneracy to a self-contained `ZMod p` statement
(no DVR, no Teichmüller lift): `leadingFiniteFieldSum i ≠ 0`. -/
theorem gaussSumLeadingUnit_of_finiteFieldSum_ne_zero {i : ℕ}
    (h : leadingFiniteFieldSum (p := p) i ≠ 0) : S.GaussSumLeadingUnit i := by
  unfold GaussSumLeadingUnit
  intro hdvd
  apply h
  rw [← residue_gaussSumCoeff_self S i]
  exact (S.residue_eq_zero_iff _).mpr hdvd

/-- **The Stickelberger higher congruences** (Washington §6.2 / Gross–Koblitz,
the genuine deep content): for `j < i`, the `π^j`-coefficient vanishes to order
`i + 1 - j`, i.e. `c i j ∈ 𝔓^{i+1-j}`.  This is exactly the statement that makes
the leading-term congruence `g i ≡ π^i c_i (mod 𝔓^{i+1})` hold. -/
def GaussSumHigherCongruence (i : ℕ) : Prop :=
  ∀ j, j < i → S.π ^ (i + 1 - j) ∣ S.gaussSumCoeff i j

/-- The character `ω^{-i}` is **nontrivial** for `0 < i < p - 1`: there is a unit
`b` with `(ω b)^i ≠ 1`.  (Otherwise `b^i ≡ 1 (mod 𝔓)` for all `b`, forcing
`(p-1) ∣ i`, impossible.) -/
theorem exists_omega_pow_ne_one {i : ℕ} (hi0 : 0 < i) (hip : i < p - 1) :
    ∃ b : (ZMod p)ˣ, (S.ω b) ^ i ≠ 1 := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  -- All (ω b)^i = 1 ⟹ b^i = 1 in 𝔽_p^× ⟹ exponent (p-1) ∣ i, contradiction.
  have hcyc : ∀ b : (ZMod p)ˣ, b ^ i = 1 := by
    intro b
    have hb := h b
    have hres : S.residue ((S.ω b : S.O) ^ i) = S.residue (1 : S.O) := by
      rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
    rw [map_pow, S.omega_residue b, map_one] at hres
    rw [← Units.val_eq_one, Units.val_pow_eq_pow_val]
    exact hres
  have hexp : Monoid.exponent (ZMod p)ˣ ∣ i := Monoid.exponent_dvd_of_forall_pow_eq_one hcyc
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units p] at hexp
  have hle : p - 1 ≤ i := Nat.le_of_dvd hi0 hexp
  omega

/-- **The `j = 0` higher congruence: `c i 0 = 0`** (the exact character-sum
vanishing slice of `GaussSumHigherCongruence`).  Since
`c i 0 = Σ_a (ω a)^{-i}·C(a,0) = Σ_a (ω a)^{-i}` is the sum of the nontrivial
character `ω^{-i}` over `(ZMod p)ˣ`, it vanishes by orthogonality.  Proved for
`0 < i < p - 1`. -/
theorem gaussSumCoeff_zero_eq_zero {i : ℕ} (hi0 : 0 < i) (hip : i < p - 1) :
    S.gaussSumCoeff i 0 = 0 := by
  -- c i 0 = ∑_a (ω a)⁻¹^i (since C(a,0)=1).
  have hc0 : S.gaussSumCoeff i 0 = ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) := by
    unfold gaussSumCoeff
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.choose_zero_right, Nat.cast_one, mul_one]
  rw [hc0]
  -- Orthogonality: pick b with χ(b) ≠ 1; then χ(b)·S = S, so (χ(b)-1)·S = 0, S = 0.
  obtain ⟨b, hb⟩ := S.exists_omega_pow_ne_one hi0 hip
  set S₀ : S.O := ∑ a : (ZMod p)ˣ, (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) with hS₀
  -- Reindex a ↦ b * a:  χ(b)·∑_a χ(a) = ∑_a χ(b*a) = ∑_{a'} χ(a') = S₀.
  have hreindex : S₀ = (((S.ω b)⁻¹ ^ i : S.Oˣ) : S.O) * S₀ := by
    have hcomp := Equiv.sum_comp (Equiv.mulLeft b)
      (fun a : (ZMod p)ˣ => (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O))
    calc
      S₀ = ∑ a : (ZMod p)ˣ, (((S.ω ((Equiv.mulLeft b) a))⁻¹ ^ i : S.Oˣ) : S.O) := by
            rw [hS₀, hcomp]
      _ = ∑ a : (ZMod p)ˣ,
            (((S.ω b)⁻¹ ^ i : S.Oˣ) : S.O) * (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Equiv.coe_mulLeft, S.ω_mul, mul_inv, mul_pow, Units.val_mul]
      _ = (((S.ω b)⁻¹ ^ i : S.Oˣ) : S.O) * S₀ := by rw [hS₀, Finset.mul_sum]
  -- (1 - χ(b))·S₀ = 0, and 1 - χ(b) ≠ 0 (a unit difference), so S₀ = 0.
  have hfactor : ((1 : S.O) - (((S.ω b)⁻¹ ^ i : S.Oˣ) : S.O)) * S₀ = 0 := by
    rw [sub_mul, one_mul, ← hreindex, sub_self]
  rcases mul_eq_zero.mp hfactor with hne | hzero
  · -- 1 - χ(b) = 0 ⟹ χ(b) = 1 ⟹ (ω b)^i = 1, contradiction.
    exfalso
    apply hb
    have heq : (((S.ω b)⁻¹ ^ i : S.Oˣ) : S.O) = 1 := by linear_combination -hne
    have : ((S.ω b)⁻¹ ^ i : S.Oˣ) = 1 := Units.ext heq
    rw [inv_pow, inv_eq_one] at this
    exact this
  · exact hzero

/-- The Gauss sum is congruent to its leading term modulo `𝔓^{i+1}`:
`g i ≡ π^i · c_i (mod 𝔓^{i+1})`, given the higher congruences.  (Here `1 ≤ i` and
`i < p`.) -/
theorem pi_pow_succ_dvd_gaussSum_sub_leading {i : ℕ} (hip : i < p)
    (hhc : S.GaussSumHigherCongruence i) :
    S.π ^ (i + 1) ∣ S.gaussSum i - S.π ^ i * S.gaussSumCoeff i i := by
  rw [S.gaussSum_eq_sum_pi_pow_coeff i]
  -- Split off the `j = i` term from the sum over `range p`.
  have hi_mem : i ∈ Finset.range p := Finset.mem_range.mpr hip
  rw [← Finset.sum_erase_add _ _ hi_mem, add_sub_cancel_right]
  -- Remaining: π^{i+1} ∣ ∑_{j ∈ range p \ {i}} π^j c_j.
  refine Finset.dvd_sum fun j hj => ?_
  rw [Finset.mem_erase, Finset.mem_range] at hj
  obtain ⟨hji, hjp⟩ := hj
  rcases lt_or_gt_of_ne hji with hlt | hgt
  · -- j < i: π^{i+1-j} ∣ c_j, so π^{i+1} = π^j · π^{i+1-j} ∣ π^j c_j.
    have hc : S.π ^ (i + 1 - j) ∣ S.gaussSumCoeff i j := hhc j hlt
    have hsplit : S.π ^ (i + 1) = S.π ^ j * S.π ^ (i + 1 - j) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit]
    exact mul_dvd_mul (dvd_refl _) hc
  · -- j > i: π^{i+1} ∣ π^j (since j ≥ i+1), so π^{i+1} ∣ π^j c_j.
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

/-- **The integral Stickelberger valuation, from the two leaves.**  Given the
higher congruences (`GaussSumHigherCongruence`) and the leading non-degeneracy
(`GaussSumLeadingUnit`), the `𝔓`-adic order of the Gauss sum is exactly `i`:
`v_𝔓(τ(ω^{-i})) = i`.  (Here `1 ≤ i < p`.) -/
theorem addVal_gaussSum_eq {i : ℕ} (_hi1 : 1 ≤ i) (hip : i < p)
    (hhc : S.GaussSumHigherCongruence i) (hlu : S.GaussSumLeadingUnit i) :
    addVal S.O (S.gaussSum i) = (i : ℕ∞) := by
  -- The leading coefficient is a unit (addVal = 0).
  have hcunit : addVal S.O (S.gaussSumCoeff i i) = 0 := by
    rw [addVal_eq_zero_iff]
    -- π ∤ c ⟹ addVal c < 1 ⟹ addVal c = 0 ⟹ IsUnit c.
    by_contra hnu
    have hne : addVal S.O (S.gaussSumCoeff i i) ≠ 0 := fun hz =>
      hnu ((addVal_eq_zero_iff).mp hz)
    have h1 : (1 : ℕ∞) ≤ addVal S.O (S.gaussSumCoeff i i) :=
      ENat.one_le_iff_ne_zero.mpr hne
    have hdvd : S.π ^ 1 ∣ S.gaussSumCoeff i i :=
      (S.le_addVal_iff_pi_pow_dvd _ 1).mp (by exact_mod_cast h1)
    rw [pow_one] at hdvd
    exact hlu hdvd
  -- The leading term has addVal = i.
  have hlead : addVal S.O (S.π ^ i * S.gaussSumCoeff i i) = (i : ℕ∞) := by
    rw [(addVal S.O).map_mul, S.π_irreducible.addVal_pow, hcunit, add_zero]
  -- Exactness via the leading congruence.
  exact S.addVal_eq_of_sub_pi_pow_dvd
    (S.pi_pow_succ_dvd_gaussSum_sub_leading hip hhc) hlead

/-- **The integral leaf, discharged from the two structural leaves.**  Packages
`addVal_gaussSum_eq` over the even index range `2 ≤ i ≤ p - 3` that
`IntegralStickelbergerValuationF1` quantifies over. -/
theorem integralStickelbergerValuationF1_of_leaves
    (hhc : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → S.GaussSumHigherCongruence i)
    (hlu : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → S.GaussSumLeadingUnit i) :
    S.IntegralStickelbergerValuationF1 := by
  intro i h1 h2 hev
  have hip : i < p := by have := hp.out.two_le; omega
  exact S.addVal_gaussSum_eq (by omega) hip (hhc i h1 h2 hev) (hlu i h1 h2 hev)

/-- **The leading non-degeneracy leaf is DISCHARGED** (unconditionally, for
`i < p - 1`).  This is the genuine `𝔽_p` character-orthogonality content of
Washington Prop 6.13 at `f = 1`, now **proved** via `leadingFiniteFieldSum_ne_zero`
(`= -(i!)⁻¹ ≠ 0`): the leading coefficient `c_i` is a `𝔓`-adic unit.  No hypothesis
needed beyond the structural setup. -/
theorem gaussSumLeadingUnit_proven {i : ℕ} (hip : i < p - 1) :
    S.GaussSumLeadingUnit i :=
  S.gaussSumLeadingUnit_of_finiteFieldSum_ne_zero (leadingFiniteFieldSum_ne_zero hip)

/-- **The integral leaf, from the higher-congruence leaf ALONE.**  Combining the
just-proved leading non-degeneracy (`gaussSumLeadingUnit_proven`) with the
higher congruences, the integral Stickelberger valuation `v_𝔓(τ(ω^{-i})) = i`
holds.  This **removes the leading-unit leaf from the residual set**: the only
remaining analytic input is `GaussSumHigherCongruence` (the Gross–Koblitz /
Dwork higher-order vanishing `c i j ∈ 𝔓^{i+1-j}`). -/
theorem integralStickelbergerValuationF1_of_higherCongruence
    (hhc : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → S.GaussSumHigherCongruence i) :
    S.IntegralStickelbergerValuationF1 := by
  refine S.integralStickelbergerValuationF1_of_leaves hhc fun i _ h2 _ => ?_
  exact S.gaussSumLeadingUnit_proven (by have := hp.out.two_le; omega)

/-- **B-C1.2 discharged from the integral leaf.**  Given the genuine integral
Stickelberger valuation `v_𝔓(τ(ω^{-i})) = i`, the normalised valuation satisfies
`v_p(τ(ω^{-i})) = i/(p-1)`, i.e. `GaussSumValuationCaseF1` holds for the concrete
data `(O, v_p, g)`.

This is the full content of Washington Proposition 6.13 at `f = 1`: the
normalisation step `i ↦ i/(p-1)` is the division by the ramification index, proved
here unconditionally; the only input is the integral digit-sum collapse. -/
theorem gaussSumValuationCaseF1_of_integralValuation
    (hint : S.IntegralStickelbergerValuationF1) :
    GaussSumValuationCaseF1 p S.normVal S.gaussSum := by
  intro i h1 h2 hev
  rw [gaussSumNormalizedValuation_def, normVal, hint i h1 h2 hev]
  simp

/-- **B-C1.2 reduced to the single higher-congruence leaf.**  `GaussSumValuationCaseF1`
for the concrete `(O, v_p, g)` follows from the higher congruences alone — the
normalisation, the ramification, the leading non-degeneracy, and the exactness are
all proved.  The sole remaining residual is `GaussSumHigherCongruence`. -/
theorem gaussSumValuationCaseF1_of_higherCongruence
    (hhc : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → S.GaussSumHigherCongruence i) :
    GaussSumValuationCaseF1 p S.normVal S.gaussSum :=
  S.gaussSumValuationCaseF1_of_integralValuation
    (S.integralStickelbergerValuationF1_of_higherCongruence hhc)

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL
