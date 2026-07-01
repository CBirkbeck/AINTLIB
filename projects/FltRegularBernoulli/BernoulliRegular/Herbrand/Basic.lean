module

public import BernoulliRegular.KummerCongruence.Bridge
public import BernoulliRegular.Stickelberger.Psylow

/-!
# Herbrand's theorem, one direction

This file starts the `T035` Herbrand layer.  The project currently represents
the odd class-group eigenspaces as declared `p`-Sylow components, before the
future intrinsic `ℤ_p[G]`-module action on the finite class group is available.
Accordingly, this file states the precise bridge needed from that future action:
if the Stickelberger/Bernoulli annihilation certificate from `T034c` annihilates
a nontrivial odd component, then the generalized Bernoulli scalar is divisible
by `p` in the `p`-adic sense.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField Pointwise nonZeroDivisors

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section Herbrand

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

/-- A rational number is divisible by `p` when its image in `ℚ_[p]` is
`p` times a `p`-adic integer.  This is the useful rational form of
"`p` divides the numerator" and is the shape consumed by the later
Bernoulli-number bridge. -/
def PAdicDivisibleByP (q : ℚ) : Prop :=
  ∃ z : ℤ_[p], ((q : ℚ_[p]) = (p : ℚ_[p]) * (z : ℚ_[p]))

/-- Divisibility of the generalized Bernoulli number attached to the inverse
character of a rational unit character. -/
def GeneralizedBernoulliPDivisible (χ : MulChar (ZMod p)ˣ ℚ) : Prop :=
  PAdicDivisibleByP p (BernoulliGen (unitMulCharDirichlet p χ⁻¹) 1)

lemma generalizedBernoulliPDivisible_iff_pSylowBernoulliScalar
    (χ : MulChar (ZMod p)ˣ ℚ) :
    GeneralizedBernoulliPDivisible p χ ↔
      PAdicDivisibleByP p (pSylowBernoulliScalar p χ) :=
  Iff.rfl

/-- The component-level nontriviality hypothesis `A_i ≠ 0`, expressed for the
current multiplicative subgroup model. -/
def OddComponentNontrivial
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) : Prop :=
  ∃ x : C.Carrier, x ≠ 1

/-- The exact missing Herbrand bridge from the future intrinsic class-group
module action.  Once the project has that action, this structure should be
instantiated from the statement that a nonzero `χ`-component cannot be killed by
a `p`-adic unit scalar; with the current data-driven component API, this bridge
is the honest interface needed to avoid smuggling in an unproved module-action
claim. -/
structure OddComponentHerbrandBridge
    (hp_odd : p ≠ 2) (χ : MulChar (ZMod p)ˣ ℚ)
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L)) where
  pDivides_of_annihilation :
    OddComponentBernoulliAnnihilation (p := p) (L := L) hp_odd χ C →
      OddComponentNontrivial (p := p) (L := L) C →
        GeneralizedBernoulliPDivisible p χ

/-- `T035a`: for a declared odd component, the Herbrand bridge turns the
`T034c` Bernoulli annihilation certificate and nontriviality of the component
into `p`-adic divisibility of `B_{1,χ⁻¹}`. -/
theorem generalizedBernoulliPDivisible_of_nontrivial_oddComponent
    (hp_odd : p ≠ 2) {χ : MulChar (ZMod p)ˣ ℚ}
    (hχ_odd : IsOddUnitCharacter (p := p) χ)
    (C : CyclotomicClassGroupPSylowComponent (p := p) (L := L))
    (hC : C.character = χ)
    (bridge : OddComponentHerbrandBridge (p := p) (L := L) hp_odd χ C)
    (hC_nontrivial : OddComponentNontrivial (p := p) (L := L) C) :
    GeneralizedBernoulliPDivisible p χ :=
  bridge.pDivides_of_annihilation
    (oddComponentBernoulliAnnihilation (p := p) (L := L) hp_odd hχ_odd C hC)
    hC_nontrivial

/-! ### Rewriting generalized Bernoulli divisibility -/

/-- A `ℚ_[p]` value is divisible by `p` when it is `p` times a `p`-adic
integer. -/
def PAdicValueDivisibleByP (x : ℚ_[p]) : Prop :=
  ∃ z : ℤ_[p], x = (p : ℚ_[p]) * (z : ℚ_[p])

/-- Divisibility of the Teichmüller generalized Bernoulli number
`B_{1,ω^j}`.  This is the `T012`-compatible form of the generalized
Bernoulli divisibility statement. -/
def TeichmullerBernoulliPDivisible (j : ℕ) : Prop :=
  PAdicValueDivisibleByP p (BernoulliGen ((teichmullerCharQp p) ^ j) 1)

/-- Ordinary Bernoulli numerator divisibility, in the form used by the
reflection tickets. -/
def OrdinaryBernoulliPDivisible (n : ℕ) : Prop :=
  (p : ℤ) ∣ (_root_.bernoulli n).num

/-- The explicit compatibility still needed between the rational-character
eigenspace API from `T035a` and the `ℚ_[p]`-valued Teichmüller character used by
the Kummer congruence bridge `T012`. -/
structure GeneralizedBernoulliToTeichmullerBridge
    (χ : MulChar (ZMod p)ˣ ℚ) (j : ℕ) where
  teichmuller_pDivisible :
    GeneralizedBernoulliPDivisible p χ → TeichmullerBernoulliPDivisible p j

lemma negHalf_mem_padicInt (hp_odd : p ≠ 2) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) = -(1 / 2 : ℚ_[p]) := by
  have hp_prime : Nat.Prime p := hp.out
  have h2_not_dvd : ¬ p ∣ 2 := fun h ↦
    hp_odd (le_antisymm (Nat.le_of_dvd (by positivity) h) hp_prime.two_le)
  have h2_unit : IsUnit ((2 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp_prime.coprime_iff_not_dvd.mpr h2_not_dvd
  let c : ℤ_[p] := -((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val)
  have hunit_mul :
      ((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) *
          (2 : ℚ_[p]) = 1 := by
    have h2_spec : ((h2_unit.unit : (ℤ_[p])ˣ) : ℤ_[p]) = 2 := h2_unit.unit_spec
    have h2_specQ :
        ((((h2_unit.unit : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) =
          (2 : ℚ_[p]) :=
      congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) h2_spec
    rw [← h2_specQ]
    change (((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ) * h2_unit.unit).val : ℤ_[p]) :
      ℚ_[p])) = 1
    simp
  have hhalf :
      ((((h2_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) : ℚ_[p])) =
        (1 / 2 : ℚ_[p]) :=
    eq_one_div_of_mul_eq_one_left hunit_mul
  exact ⟨c, by simp [c, hhalf]⟩

lemma ordinaryBernoulliPDivisible_of_ratio_pDivisible
    (hp_odd : p ≠ 2) {n : ℕ} (hn_pos : 0 < n) (hn_lt : n < p)
    (hden : ¬ p ∣ (_root_.bernoulli n).den)
    (hdiv : PAdicValueDivisibleByP p (((_root_.bernoulli n : ℚ) / n : ℚ) : ℚ_[p])) :
    OrdinaryBernoulliPDivisible p n := by
  obtain ⟨a, ha, ha_unit⟩ := exists_padicInt_bernoulli_factor
    (p := p) (hp := hp) (n := n) hp_odd hn_pos hn_lt hden
  obtain ⟨c, hc⟩ := negHalf_mem_padicInt (p := p) hp_odd
  obtain ⟨z, hz⟩ := hdiv
  have ha_pdiv : ((a : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) * ((c * z : ℤ_[p]) : ℚ_[p]) := by
    rw [ha, hz, ← hc, PadicInt.coe_mul]
    ring
  have ha_lt_Qp : ‖((a : ℤ_[p]) : ℚ_[p])‖ < 1 := by
    rw [ha_pdiv]
    have hp_lt : ‖(p : ℚ_[p])‖ < 1 := by
      simpa using (Padic.norm_natCast_lt_one_iff (p := p) (n := p)).2 dvd_rfl
    calc
      ‖(p : ℚ_[p]) * ((c * z : ℤ_[p]) : ℚ_[p])‖ =
          ‖((c * z : ℤ_[p]) : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ := by
            rw [norm_mul, mul_comm]
      _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (c * z).2 (norm_nonneg _) hp_lt
  have ha_nonunit : ¬ IsUnit a :=
    (PadicInt.not_isUnit_iff (z := a)).2 <| by
      simpa [PadicInt.padic_norm_e_of_padicInt] using ha_lt_Qp
  by_contra hnot
  exact ha_nonunit (ha_unit.mpr hnot)

/-- `T035b`, Teichmüller form: if `B_{1,ω^j}` is divisible by `p`, then the
ordinary Bernoulli numerator `B_{j+1}` is divisible by `p`, for the non-boundary
odd indices where the Kummer bridge `T012` applies. -/
theorem ordinaryBernoulliPDivisible_of_teichmullerBernoulliPDivisible
    (hp_odd : p ≠ 2) {j : ℕ} (hj_odd : Odd j) (hj_pos : 0 < j)
    (hj_small : j + 1 < p - 1)
    (hgen : TeichmullerBernoulliPDivisible p j) :
    OrdinaryBernoulliPDivisible p (j + 1) := by
  have hj_not_dvd : ¬ (p - 1) ∣ (j + 1) :=
    Nat.not_dvd_of_pos_of_lt (by omega) hj_small
  have hj_p_plus : ¬ (p : ℕ) ∣ (j + 1) :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hj_p_plus_two : ¬ (p : ℕ) ∣ (j + 2) :=
    Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  obtain ⟨z₁, hz₁⟩ := hgen
  obtain ⟨z₂, hz₂⟩ := bernoulliGen_teichmuller_pow_sModEq_div
    (p := p) hp_odd hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two hj_small
  have hratio :
      PAdicValueDivisibleByP p
        (((_root_.bernoulli (j + 1) : ℚ) / (j + 1 : ℕ) : ℚ) : ℚ_[p]) := by
    refine ⟨z₁ - z₂, ?_⟩
    have hz₂' :
        BernoulliGen ((teichmullerCharQp p) ^ j) 1 =
          (((_root_.bernoulli (j + 1) : ℚ) / (j + 1 : ℕ) : ℚ) : ℚ_[p]) +
            (p : ℚ_[p]) * (z₂ : ℚ_[p]) := by
      rw [sub_eq_iff_eq_add] at hz₂
      simpa [add_comm] using hz₂
    calc
      (((_root_.bernoulli (j + 1) : ℚ) / (j + 1 : ℕ) : ℚ) : ℚ_[p])
          = BernoulliGen ((teichmullerCharQp p) ^ j) 1 -
              (p : ℚ_[p]) * (z₂ : ℚ_[p]) := by rw [hz₂']; ring
      _ = (p : ℚ_[p]) * ((z₁ - z₂ : ℤ_[p]) : ℚ_[p]) := by
            rw [hz₁]
            push_cast
            ring
  exact ordinaryBernoulliPDivisible_of_ratio_pDivisible
    (p := p) hp_odd (by omega : 0 < j + 1) (by omega : j + 1 < p)
    (BernoulliRegular.prime_not_dvd_bernoulli_den_of_lt_sub_one
      (p := p) (n := j + 1) (hp := hp) hp_odd (by omega))
    hratio

/-- `T035b`, rational-character interface: after an explicit compatibility
bridge identifies the rational-character generalized Bernoulli divisibility
from `T035a` with the Teichmüller form used by `T012`, the conclusion is the
ordinary Bernoulli numerator divisibility required downstream. -/
theorem ordinaryBernoulliPDivisible_of_generalizedBernoulliPDivisible
    (hp_odd : p ≠ 2) {χ : MulChar (ZMod p)ˣ ℚ} {j : ℕ}
    (hj_odd : Odd j) (hj_pos : 0 < j) (hj_small : j + 1 < p - 1)
    (bridge : GeneralizedBernoulliToTeichmullerBridge (p := p) χ j)
    (hgen : GeneralizedBernoulliPDivisible p χ) :
    OrdinaryBernoulliPDivisible p (j + 1) :=
  ordinaryBernoulliPDivisible_of_teichmullerBernoulliPDivisible
    (p := p) hp_odd hj_odd hj_pos hj_small (bridge.teichmuller_pDivisible hgen)

end Herbrand

end BernoulliRegular

end
