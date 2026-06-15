import BernoulliRegular.FLT37.PadicL.GaussSumValuationF1
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# B-C1.2, fully discharged — the integral `f = 1` Stickelberger valuation via Gauss sums

This file **proves** `StickelbergerF1Setup.IntegralStickelbergerValuationF1`
(`v_𝔓(τ(ω^{-i})) = i`, Washington Proposition 6.13 at `f = 1`, integral form)
**unconditionally** over the abstract DVR setup of `GaussSumValuationF1.lean`,
thereby discharging `GaussSumValuationCaseF1` (B-C1.2) without the
coefficient-level Gross–Koblitz carry (`GaussSumHigherCongruence`).

## The route: Washington's actual Prop 6.13 proof at `f = 1`

Washington proves `s(α) := v_𝔓(g(ω^{-α})) = α` for `0 ≤ α ≤ p - 2` from four
inputs (Lemmas 6.11, 6.12), none of which is the coefficient carry:

* **(orthogonality)** `s(α) > 0` for `α ≢ 0 (mod p - 1)` — the Gauss sum reduces
  to `Σ ω^{-α}(a) ≡ 0 (mod 𝔓)`.  (Already available as
  `gaussSumCoeff_zero_eq_zero`.)
* **`s(1) = 1`** — the explicit `g(ω^{-1}) ≡ π·(-1) (mod 𝔓²)` computation
  (Lemma 6.12).  Realised here through the file's `addVal_gaussSum_eq` at `i = 1`
  (whose only higher-congruence input is `c_{1,0} = 0`, which holds).
* **(subadditivity)** `s(α + β) ≤ s(α) + s(β)` — from
  `g(χφ)·J(χ,φ) = g(χ)·g(φ)` (`jacobiSum_mul_nontrivial`) and `v_𝔓(J) ≥ 0`
  (the Jacobi sum is an element of `O`).
* **(pairing)** `s(α) + s(p - 1 - α) = p - 1` — from
  `g(χ)·g(χ⁻¹) = ±p` (`gaussSum_mul_gaussSum_eq_card`) and `v_𝔓(p) = p - 1`.

Then `s(α) ≤ α` (subadditivity from `s(1) = 1`) and, via the pairing,
`s(α) = (p-1) - s(p-1-α) ≥ (p-1) - (p-1-α) = α`, so `s(α) = α`.  This needs no
`mod (p-1)` congruence and no Dwork machinery.

## Bridge to mathlib's Gauss/Jacobi sums

The abstract `StickelbergerF1Setup.gaussSum i = Σ_{a ∈ (ZMod p)ˣ} (ω a)^{-i}·(1+π)^{rep a}`
is identified with mathlib's `gaussSum χ_i ψ` for
`χ_i = (MulChar.ofUnitHom ω)⁻¹^i : MulChar (ZMod p) O` and
`ψ = AddChar.zmodChar p ((1+π)^p = 1) : AddChar (ZMod p) O`, which unlocks the
two multiplicative identities above.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Prop 6.13,
  Lemmas 6.11–6.12.
-/

namespace BernoulliRegular.FLT37.PadicL

open IsDiscreteValuationRing IsLocalRing

namespace StickelbergerF1Setup

variable {p : ℕ} [hp : Fact p.Prime] (S : StickelbergerF1Setup p)

instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- The Teichmüller character packaged as a `MonoidHom (ZMod p)ˣ → S.Oˣ`
(its multiplicativity is `ω_mul`; `ω 1 = 1` is forced). -/
noncomputable def omegaHom : (ZMod p)ˣ →* S.Oˣ where
  toFun := S.ω
  map_one' := by
    have h : S.ω 1 * (1 : S.Oˣ) = S.ω 1 * S.ω 1 := by
      rw [mul_one]
      have := S.ω_mul 1 1; rwa [mul_one] at this
    exact (mul_left_cancel h).symm
  map_mul' := S.ω_mul

@[simp] theorem omegaHom_apply (a : (ZMod p)ˣ) : S.omegaHom a = S.ω a := rfl

/-- The base Teichmüller multiplicative character `χ : MulChar (ZMod p) O`,
`χ(a) = ω(a)` on units, `χ(0) = 0`. -/
noncomputable def teichChar : MulChar (ZMod p) S.O := MulChar.ofUnitHom S.omegaHom

/-- The character `χ_i := χ⁻¹^i = ω^{-i}`. -/
noncomputable def teichCharPow (i : ℕ) : MulChar (ZMod p) S.O := (S.teichChar)⁻¹ ^ i

theorem teichChar_apply_unit (a : (ZMod p)ˣ) : S.teichChar (a : ZMod p) = (S.ω a : S.O) := by
  rw [teichChar, MulChar.ofUnitHom_coe, omegaHom_apply]

/-- The additive character `ψ(x) = (1+π)^{x.val}` on `ZMod p`. -/
noncomputable def addCharPi : AddChar (ZMod p) S.O := AddChar.zmodChar p S.one_add_pi_pow_p

theorem addCharPi_apply (x : ZMod p) : S.addCharPi x = (1 + S.π) ^ x.val := rfl

theorem addCharPi_apply_unit (a : (ZMod p)ˣ) :
    S.addCharPi (a : ZMod p) = (1 + S.π) ^ teichRep a := rfl

/-- The value of `χ_i = ω^{-i}` on a unit `a` is `(ω a)⁻ⁱ`, matching the summand
in `S.gaussSum i`. -/
theorem teichChar_inv_apply_unit (a : (ZMod p)ˣ) :
    (S.teichChar)⁻¹ (a : ZMod p) = (((S.ω a)⁻¹ : S.Oˣ) : S.O) := by
  rw [MulChar.inv_apply',
    show ((a : ZMod p))⁻¹ = ((a⁻¹ : (ZMod p)ˣ) : ZMod p) by rw [Units.val_inv_eq_inv_val],
    teichChar_apply_unit]
  -- S.ω (a⁻¹) = (S.ω a)⁻¹ via the monoid hom `omegaHom`.
  rw [← omegaHom_apply, map_inv, omegaHom_apply]

theorem teichCharPow_apply_unit (i : ℕ) (a : (ZMod p)ˣ) :
    S.teichCharPow i (a : ZMod p) = (((S.ω a)⁻¹ ^ i : S.Oˣ) : S.O) := by
  rw [teichCharPow, MulChar.pow_apply_coe, teichChar_inv_apply_unit, ← Units.val_pow_eq_pow_val]

/-- **Identification with mathlib's Gauss sum**:
`S.gaussSum i = gaussSum χ_i ψ`.  The `a = 0` term of mathlib's sum vanishes
(`χ_i 0 = 0`), so the sum over `ZMod p` collapses to the sum over units. -/
theorem gaussSum_eq_mathlib (i : ℕ) :
    S.gaussSum i = _root_.gaussSum (S.teichCharPow i) S.addCharPi := by
  classical
  -- Mathlib's Gauss sum, split off the `a = 0` term (which vanishes since `χ 0 = 0`).
  have hmathlib : _root_.gaussSum (S.teichCharPow i) S.addCharPi =
      ∑ a ∈ Finset.univ \ {(0 : ZMod p)}, S.teichCharPow i a * S.addCharPi a := by
    have hsplit := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (0 : ZMod p))
      (fun a : ZMod p => S.teichCharPow i a * S.addCharPi a)
    rw [MulChar.map_zero, zero_mul, add_zero] at hsplit
    exact hsplit
  rw [hmathlib]
  -- The sum over `univ \ {0}` equals the sum over units.
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : (Finset.univ : Finset (ZMod p)ˣ).map φ = Finset.univ \ {0} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ] using isUnit_iff_ne_zero
  rw [← hmap, Finset.sum_map]
  unfold StickelbergerF1Setup.gaussSum
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Function.Embedding.coeFn_mk, teichCharPow_apply_unit, addCharPi_apply_unit]

@[simp] theorem teichCharPow_zero : S.teichCharPow 0 = 1 := by
  rw [teichCharPow, pow_zero]

/-- `χ_{α+β} = χ_α · χ_β`. -/
theorem teichCharPow_add (a b : ℕ) :
    S.teichCharPow (a + b) = S.teichCharPow a * S.teichCharPow b := by
  rw [teichCharPow, teichCharPow, teichCharPow, pow_add]

/-- `χ^{p-1} = 1` (the Teichmüller character has order dividing `p - 1`). -/
theorem teichChar_pow_card : (S.teichChar) ^ (p - 1) = 1 := by
  rw [MulChar.eq_one_iff]
  intro a
  rw [MulChar.pow_apply_coe, teichChar_apply_unit, ← Units.val_pow_eq_pow_val,
    S.ω_pow_sub_one a, Units.val_one]

/-- `χ_α⁻¹ = χ_{p-1-α}` for `α ≤ p - 1`. -/
theorem teichCharPow_inv_eq {α : ℕ} (hα : α ≤ p - 1) :
    (S.teichCharPow α)⁻¹ = S.teichCharPow (p - 1 - α) := by
  have hcard : (S.teichCharPow α) * (S.teichCharPow (p - 1 - α)) = 1 := by
    rw [← teichCharPow_add, Nat.add_sub_cancel' hα, teichCharPow, inv_pow,
      S.teichChar_pow_card, inv_one]
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hcard)).symm

/-- `χ_α ≠ 1` for `1 ≤ α ≤ p - 2` (the character `ω^{-α}` is nontrivial when
`(p-1) ∤ α`). -/
theorem teichCharPow_ne_one {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) :
    S.teichCharPow α ≠ 1 := by
  have hαp : α < p - 1 := by have := hp.out.two_le; omega
  obtain ⟨b, hb⟩ := S.exists_omega_pow_ne_one h1 hαp
  rw [MulChar.ne_one_iff]
  refine ⟨b, ?_⟩
  rw [teichCharPow_apply_unit]
  intro hcontra
  apply hb
  -- ((ω b)⁻¹ ^ α : Oˣ) = 1, hence (ω b)^α = 1.
  have : ((S.ω b)⁻¹ ^ α : S.Oˣ) = 1 := Units.ext hcontra
  rw [inv_pow, inv_eq_one] at this
  exact this

/-- The additive character `ψ = (1+π)^{·}` is nontrivial (`π ≠ 0`). -/
theorem addCharPi_ne_one : S.addCharPi ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff]
  -- ψ 1 = (1+π)^1 = 1 + π ≠ 1.
  have hval : ((1 : ZMod p)).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hp.out.one_lt]
  rw [addCharPi_apply, hval, pow_one]
  intro hcontra
  -- 1 + π = 1 ⟹ π = 0, contradicting irreducibility.
  have : S.π = 0 := by linear_combination hcontra
  exact S.π_irreducible.ne_zero this

/-- The additive character `ψ` is primitive (since `ZMod p` is a field and `ψ ≠ 1`). -/
theorem isPrimitive_addCharPi : S.addCharPi.IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one S.addCharPi_ne_one

/-- Shorthand for the `𝔓`-adic order `s(α) = v_𝔓(g(ω^{-α}))`. -/
noncomputable def gaussSumVal (α : ℕ) : ℕ∞ := addVal S.O (S.gaussSum α)

/-- `(p : O) ≠ 0`: otherwise `v_𝔓(p) = ⊤`, contradicting `v_𝔓(p) = p - 1`. -/
theorem cast_p_ne_zero : ((p : ℕ) : S.O) ≠ 0 := by
  intro h
  have hval := S.addVal_p_eq
  rw [h, addVal_zero] at hval
  exact (ENat.coe_ne_top _ hval.symm).elim

/-- The Gauss sum `g(ω^{-α})` is nonzero for `1 ≤ α ≤ p - 2` (nontrivial
character over the field `ZMod p` with primitive `ψ`), so `s(α) < ⊤`. -/
theorem gaussSum_ne_zero {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) : S.gaussSum α ≠ 0 := by
  rw [S.gaussSum_eq_mathlib]
  refine gaussSum_ne_zero_of_nontrivial ?_ (S.teichCharPow_ne_one h1 h2) S.isPrimitive_addCharPi
  rw [ZMod.card]
  exact S.cast_p_ne_zero

theorem gaussSumVal_lt_top {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) : S.gaussSumVal α < ⊤ := by
  rw [gaussSumVal, lt_top_iff_ne_top, Ne, addVal_eq_top_iff]
  exact S.gaussSum_ne_zero h1 h2

/-- **(subadditivity)** `s(α + β) ≤ s(α) + s(β)` when `χ_α · χ_β ≠ 1`.  From
`g(χ_{α+β}) · J(χ_α, χ_β) = g(χ_α) · g(χ_β)` and `v_𝔓(J) ≥ 0`. -/
theorem gaussSumVal_add_le {α β : ℕ} (h : S.teichCharPow α * S.teichCharPow β ≠ 1) :
    S.gaussSumVal (α + β) ≤ S.gaussSumVal α + S.gaussSumVal β := by
  have hmul := jacobiSum_mul_nontrivial h S.addCharPi
  rw [← S.teichCharPow_add] at hmul
  -- addVal both sides: addVal(g_{α+β}) + addVal(J) = addVal(g_α) + addVal(g_β).
  have hval := congrArg (addVal S.O) hmul
  rw [addVal_mul, addVal_mul] at hval
  rw [gaussSumVal, gaussSumVal, gaussSumVal, S.gaussSum_eq_mathlib, S.gaussSum_eq_mathlib,
    S.gaussSum_eq_mathlib]
  calc addVal S.O (_root_.gaussSum (S.teichCharPow (α + β)) S.addCharPi)
      ≤ addVal S.O (_root_.gaussSum (S.teichCharPow (α + β)) S.addCharPi) +
          addVal S.O (jacobiSum (S.teichCharPow α) (S.teichCharPow β)) := le_self_add
    _ = addVal S.O (_root_.gaussSum (S.teichCharPow α) S.addCharPi) +
          addVal S.O (_root_.gaussSum (S.teichCharPow β) S.addCharPi) := hval

/-- The value of a `MulChar` on `-1` is a `𝔓`-adic unit (it is a value on a unit),
so it has `addVal = 0`; hence twisting `ψ ↦ ψ⁻¹` does not change the valuation of a
Gauss sum. -/
theorem addVal_gaussSum_inv_addChar (χ : MulChar (ZMod p) S.O) :
    addVal S.O (_root_.gaussSum χ S.addCharPi⁻¹) = addVal S.O (_root_.gaussSum χ S.addCharPi) := by
  have hkey := mul_gaussSum_inv_eq_gaussSum χ S.addCharPi
  have hval := congrArg (addVal S.O) hkey
  rw [addVal_mul] at hval
  have hunit : addVal S.O (χ (-1)) = 0 := by
    rw [addVal_eq_zero_iff]
    have : IsUnit ((-1 : ZMod p)) := isUnit_one.neg
    exact this.map χ
  rw [hunit, zero_add] at hval
  exact hval

/-- **(pairing)** `s(α) + s(p-1-α) = p - 1` for `1 ≤ α ≤ p - 2`.  From
`g(χ_α) · g(χ_α⁻¹) = ±p` (`gaussSum_mul_gaussSum_eq_card`) and `v_𝔓(p) = p - 1`,
together with `χ_α⁻¹ = χ_{p-1-α}`. -/
theorem gaussSumVal_pairing {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) :
    S.gaussSumVal α + S.gaussSumVal (p - 1 - α) = ((p : ℕ) - 1 : ℕ) := by
  have hαp1 : α ≤ p - 1 := by have := hp.out.two_le; omega
  have hcard := gaussSum_mul_gaussSum_eq_card (S.teichCharPow_ne_one h1 h2) S.isPrimitive_addCharPi
  -- addVal: addVal(g_α) + addVal(g(χ_α⁻¹, ψ⁻¹)) = addVal(p) = p - 1.
  have hval := congrArg (addVal S.O) hcard
  rw [addVal_mul] at hval
  rw [S.addVal_gaussSum_inv_addChar (S.teichCharPow α)⁻¹, S.teichCharPow_inv_eq hαp1] at hval
  rw [ZMod.card] at hval
  rw [gaussSumVal, gaussSumVal, S.gaussSum_eq_mathlib, S.gaussSum_eq_mathlib]
  rw [hval, S.addVal_p_eq]

/-- The `j = 0` higher congruence for `i = 1`: `c_{1,0} = 0`, so
`GaussSumHigherCongruence 1` holds vacuously beyond it. -/
theorem gaussSumHigherCongruence_one (hp3 : 3 ≤ p) : S.GaussSumHigherCongruence 1 := by
  intro j hj
  interval_cases j
  -- j = 0: π^2 ∣ c_{1,0} = 0.
  rw [S.gaussSumCoeff_zero_eq_zero (by norm_num) (by omega)]
  exact dvd_zero _

/-- **`s(1) = 1`** (Washington Lemma 6.12 at `f = 1`): `v_𝔓(g(ω^{-1})) = 1`.
Realised through the file's `addVal_gaussSum_eq` — the only higher-congruence
input is `c_{1,0} = 0`, and the leading non-degeneracy is
`gaussSumLeadingUnit_proven`. -/
theorem gaussSumVal_one (hp3 : 3 ≤ p) : S.gaussSumVal 1 = 1 := by
  rw [gaussSumVal]
  rw [S.addVal_gaussSum_eq (le_refl 1) (by omega) (S.gaussSumHigherCongruence_one hp3)
    (S.gaussSumLeadingUnit_proven (by omega))]
  rfl

/-- **(subadditive upper bound)** `s(α) ≤ α` for `1 ≤ α ≤ p - 2`, by induction
from `s(1) = 1` using subadditivity (`s(α+1) ≤ s(α) + s(1)`). -/
theorem gaussSumVal_le_self (hp3 : 3 ≤ p) {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) :
    S.gaussSumVal α ≤ (α : ℕ∞) := by
  induction α with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · -- α = 1: s(1) = 1 ≤ 1.
      subst hn0
      rw [S.gaussSumVal_one hp3]; norm_num
    · -- α = n + 1 with n ≥ 1: s(n+1) ≤ s(n) + s(1) ≤ n + 1.
      have hn1' : 1 ≤ n := hn0
      have hn2 : n ≤ p - 2 := by omega
      have hstep : S.gaussSumVal (n + 1) ≤ S.gaussSumVal n + S.gaussSumVal 1 := by
        refine S.gaussSumVal_add_le ?_
        rw [← S.teichCharPow_add]
        exact S.teichCharPow_ne_one (by omega) h2
      calc S.gaussSumVal (n + 1) ≤ S.gaussSumVal n + S.gaussSumVal 1 := hstep
        _ ≤ (n : ℕ∞) + 1 := by
            rw [S.gaussSumVal_one hp3]
            gcongr
            exact ih hn1' hn2
        _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- **`s(α) = α`** for `1 ≤ α ≤ p - 2` (Washington Prop 6.13 at `f = 1`).
The upper bound `s(α) ≤ α` is subadditivity from `s(1) = 1`; the lower bound is
the pairing `s(α) = (p-1) - s(p-1-α) ≥ (p-1) - (p-1-α) = α`. -/
theorem gaussSumVal_eq_self (hp3 : 3 ≤ p) {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ p - 2) :
    S.gaussSumVal α = (α : ℕ∞) := by
  have hp2 := hp.out.two_le
  -- The complementary index `p - 1 - α` is also in `[1, p-2]`.
  have hc1 : 1 ≤ p - 1 - α := by omega
  have hc2 : p - 1 - α ≤ p - 2 := by omega
  -- Both valuations are finite; name their `toNat` values.
  set a : ℕ := (S.gaussSumVal α).toNat with ha
  set b : ℕ := (S.gaussSumVal (p - 1 - α)).toNat with hb
  have hafin : S.gaussSumVal α = (a : ℕ∞) :=
    (ENat.coe_toNat (S.gaussSumVal_lt_top h1 h2).ne).symm
  have hbfin : S.gaussSumVal (p - 1 - α) = (b : ℕ∞) :=
    (ENat.coe_toNat (S.gaussSumVal_lt_top hc1 hc2).ne).symm
  -- Pairing: a + b = p - 1 (as ℕ).
  have hpair : a + b = p - 1 := by
    have := S.gaussSumVal_pairing h1 h2
    rw [hafin, hbfin] at this
    exact_mod_cast this
  -- Upper bounds: a ≤ α, b ≤ p - 1 - α.
  have hbnda : a ≤ α := by
    have := S.gaussSumVal_le_self hp3 h1 h2
    rw [hafin] at this; exact_mod_cast this
  have hbndb : b ≤ p - 1 - α := by
    have := S.gaussSumVal_le_self hp3 hc1 hc2
    rw [hbfin] at this; exact_mod_cast this
  -- a = α follows by arithmetic.
  rw [hafin]
  norm_cast
  omega

/-- **The integral `f = 1` Stickelberger valuation is DISCHARGED unconditionally**
(`v_𝔓(τ(ω^{-i})) = i` for the even FLT range `2 ≤ i ≤ p - 3`), via the Gauss-sum
multiplicative route (`gaussSumVal_eq_self`).  This removes the
`GaussSumHigherCongruence` (Gross–Koblitz carry) input entirely. -/
theorem integralStickelbergerValuationF1_proven :
    S.IntegralStickelbergerValuationF1 := by
  intro i h1 h2 _hev
  have hp3 : 3 ≤ p := by omega
  have hi2 : i ≤ p - 2 := by omega
  exact S.gaussSumVal_eq_self hp3 (by omega) hi2

/-- **B-C1.2 = Washington Proposition 6.13 at `f = 1`, fully proved**:
`v_p(τ(ω^{-i})) = i/(p-1)` for the concrete data `(O, v_p, g)`.  This composes the
unconditional integral valuation `integralStickelbergerValuationF1_proven` with the
normalisation reduction `gaussSumValuationCaseF1_of_integralValuation`. -/
theorem gaussSumValuationCaseF1_proven :
    GaussSumValuationCaseF1 p S.normVal S.gaussSum :=
  S.gaussSumValuationCaseF1_of_integralValuation S.integralStickelbergerValuationF1_proven

end StickelbergerF1Setup

end BernoulliRegular.FLT37.PadicL
