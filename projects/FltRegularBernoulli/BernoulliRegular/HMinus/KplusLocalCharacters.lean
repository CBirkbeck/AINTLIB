module

import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Ideal.GoingUp

public import BernoulliRegular.TotallyRealSubfield
public import BernoulliRegular.ZetaFactorisation

/-!
# `K⁺` local even-character data (T023b2a1)

Character-side local input for the maximal real subfield package:

- `localResidueDegreePlus` and `localPrimeCountPlus` — the residue degree and
  number of primes of `K⁺ = maximalRealSubfield K` above a rational prime
  `ℓ ≠ p`, expressed purely in terms of the cyclotomic-side invariants
  `localResidueDegree` and `localPrimeCount` together with the sign dichotomy
  `-1 ∈ ⟨ℓ⟩ mod p`.
- Elementary power-equal-one / order-divides lemmas for even Dirichlet
  characters evaluated at `unitOfPrimeNe`.
- Cardinality identities `card_even_characters_kplus` and
  `card_evenNontrivialCharacters`.
- `localPrimeCountPlus_mul_localResidueDegreePlus`, the numerical identity
  matching the `K⁺` degree count with the even-character count.
- `prod_even_characters_eval_eq_pow_localResidueDegreePlus`, the orbit-product
  formula collapsing the full even-character product at `ℓ ≠ p` to a single
  Euler factor.
- `trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus`, the final
  unramified character-side local factor theorem in the shape later matched
  against the `K⁺` Dedekind local factor.

This file is the character half of the old monolithic
`BernoulliRegular.HMinus.KplusLocalResidue`; the prime-ideal / contraction /
`K⁺` inertia lemmas now live in
`BernoulliRegular.HMinus.KplusPrimeArithmetic`.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open scoped BigOperators Pointwise

namespace BernoulliRegular

lemma prod_pow_primRoot_eq_pow_kplus {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω n) (T : ℂ) :
    ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) =
      (1 - T ^ (n / n.gcd a)) ^ n.gcd a := by
  classical
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n : d ∣ n := ⟨c, by rw [mul_comm]; exact hc_mul_d.symm⟩
  have hω_a_prim : IsPrimitiveRoot (ω ^ a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period : ∀ k : ℕ, ω ^ (k * a) = ω ^ ((k % d) * a) := by
    intro k
    have hkd : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
    have h_da : ω ^ ((k / d) * (d * a)) = 1 := by
      obtain ⟨a', ha'⟩ := hc_dvd_a
      rw [ha', show (k / d) * (d * (c * a')) = (k / d) * a' * (c * d) from by ring, hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k / d) * a', mul_comm _ _⟩
    conv_lhs => rw [hkd]
    rw [show (d * (k / d) + k % d) * a = (k % d) * a + (k / d) * (d * a) from by ring, pow_add,
      h_da, mul_one]
  rw [show (∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T)) =
      ∏ k ∈ Finset.range n, (1 - ω ^ ((k % d) * a) * T) from
    Finset.prod_congr rfl (fun k _ => by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun k : ℕ => k % d) (t := Finset.range d)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner : ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k % d = j), (1 - ω ^ ((k % d) * a) * T)) =
      (1 - ω ^ (j * a) * T) ^ c := by
    intro j hj
    have h_rewrite : ∀ k ∈ (Finset.range n).filter (fun k => k % d = j),
        (1 - ω ^ ((k % d) * a) * T) = (1 - ω ^ (j * a) * T) := fun k hk => by
      rw [Finset.mem_filter] at hk
      rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite, Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c', hcd'⟩ := hd_dvd_n
    have hc_eq : c = c' := by
      have hd_mul : d * c = n := by rw [mul_comm, hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul, hcd'])
    rw [hc_eq]
    have hset : (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      refine ⟨fun ⟨hk_lt, hk_mod⟩ => ?_, ?_⟩
      · have hk_dec : k = j + (k / d) * d := by
          have h1 : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
          rw [hk_mod, mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d, ?_, hk_dec.symm⟩
        have h_lt_cd : (k / d) * d < c' * d := by
          have h_le : (k / d) * d ≤ k := Nat.div_mul_le_self k d
          rw [mul_comm c' d, ← hcd']
          omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m, hm_lt, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hcd', mul_comm]
          nlinarith
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hset, Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner, Finset.prod_pow]
  congr 1
  have h_inj : Set.InjOn (fun j : ℕ => (ω ^ a) ^ j) ↑(Finset.range d) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image : Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image, Finset.mem_range] at hζ
      obtain ⟨j, _, rfl⟩ := hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos, ← pow_mul, mul_comm j d, pow_mul,
        hω_a_prim.pow_eq_one, one_pow]
    · rw [hω_a_prim.card_nthRootsFinset, Finset.card_image_of_injOn h_inj, Finset.card_range]
  calc ∏ j ∈ Finset.range d, (1 - ω ^ (j * a) * T)
      = ∏ j ∈ Finset.range d, (1 - (ω ^ a) ^ j * T) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul, mul_comm a j]
    _ = ∏ ζ ∈ Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d), (1 - ζ * T) := by
        rw [Finset.prod_image h_inj]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) := by rw [h_image]
    _ = 1 - T ^ d := prod_nthRootsFinset_one_sub_mul d hd_pos T

section KplusLocalCharacters

variable (p : ℕ) [hp : Fact p.Prime]

/-- The residue-degree candidate for `K⁺`: the order of `ℓ mod p` up to sign. -/
noncomputable def localResidueDegreePlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  if Even d then d / 2 else d

/-- The expected number of primes above `ℓ ≠ p` on the `K⁺` side. -/
noncomputable def localPrimeCountPlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  let c := localPrimeCount (p := p) ℓ hℓp
  if Even d then c else c / 2

lemma localResidueDegreePlus_eq_half {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  simp [localResidueDegreePlus, hd_even]

lemma localResidueDegreePlus_eq_self {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_odd : ¬ Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp := by
  simp [localResidueDegreePlus, hd_odd]

lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = 1) ∨
      (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = -1) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hsq : (((u : ZMod p) ^ (d / 2)) ^ 2) = 1 := by
      rw [← pow_mul]
      have : (d / 2) * 2 = d := by omega
      rw [this]
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    have hcases : ((u : ZMod p) ^ (d / 2)) = 1 ∨ ((u : ZMod p) ^ (d / 2)) = -1 :=
      sq_eq_one_iff.mp hsq
    have hnot_one : ((u : ZMod p) ^ (d / 2)) ≠ 1 := by
      intro hpow
      have hpow_units : u ^ (d / 2) = 1 := by
        apply Units.ext
        simpa using hpow
      have hdvd : d ∣ d / 2 := by
        simpa [d, localResidueDegree, u] using
          (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
      have hk_pos : 0 < k := by
        have hd_pos : 0 < d := by
          dsimp [d, localResidueDegree]
          exact orderOf_pos u
        omega
      have hle : 2 * k ≤ k := by
        have hdvd' : 2 * k ∣ k := by
          rw [hk] at hdvd
          rw [show k + k = 2 * k by omega] at hdvd
          simpa using hdvd
        exact Nat.le_of_dvd hk_pos hdvd'
      omega
    rcases hcases with hpow | hpow
    · exact False.elim (hnot_one hpow)
    · right
      simpa [localResidueDegreePlus, d, hk] using hpow
  · left
    have hpow : (u : ZMod p) ^ d = 1 := by
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    simpa [localResidueDegreePlus, d, hd_even] using hpow

lemma even_char_eval_unitOfPrimeNe_eq_eval_neg_unitOfPrimeNe
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) :
    χ (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p)) =
      χ (-(((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p))) := by
  symm
  rw [hχ_even.eval_neg]

lemma even_char_pow_localResidueDegreePlus_eq_one
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) :
    χ (ℓ : ZMod p) ^ localResidueDegreePlus (p := p) ℓ hℓp = 1 := by
  have hunit :
      (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p)) = (ℓ : ZMod p) := by
    simp [unitOfPrimeNe]
  rw [← hunit]
  rcases unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one (p := p) hℓp with hpow | hpow
  · simpa [map_pow] using congrArg χ hpow
  · rw [DirichletCharacter.Even] at hχ_even
    simpa [map_pow, hχ_even] using congrArg χ hpow

lemma orderOf_even_char_eval_dvd_localResidueDegreePlus
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {χ : DirichletCharacter ℂ p} (hχ_even : χ.Even) :
    orderOf (χ (ℓ : ZMod p)) ∣ localResidueDegreePlus (p := p) ℓ hℓp := by
  rw [orderOf_dvd_iff_pow_eq_one]
  exact even_char_pow_localResidueDegreePlus_eq_one (p := p) hℓp hχ_even

lemma orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) =
      localResidueDegreePlus (p := p) ℓ hℓp := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨d, by
      dsimp [d, localResidueDegree]
      exact orderOf_pos u,
      by
        dsimp [d, localResidueDegree]
        exact pow_orderOf_eq_one u⟩
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hd_even' : Even (localResidueDegree (p := p) ℓ hℓp) :=
      ⟨k, by simpa [d] using hk⟩
    have hgcd : d.gcd 2 = 2 := by
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right d 2
      · exact Nat.dvd_gcd ⟨k, by omega⟩ dvd_rfl
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [hfin.orderOf_pow], hgcd,
      localResidueDegreePlus_eq_half (p := p) hℓp hd_even']
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    have hgcd : d.gcd 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hd_odd.coprime_two_right
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [hfin.orderOf_pow], hgcd,
      localResidueDegreePlus_eq_self (p := p) hℓp (by simpa [d] using hd_even)]
    simp [d]

attribute [local instance] Classical.decEq Classical.propDecidable

lemma card_even_characters_kplus (hp_odd' : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  let O : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Odd
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one : (-1 : ZMod p) ≠ 1 := by
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero :
      ∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p) = 0 :=
    DirichletCharacter.sum_characters_eq_zero (R := ℂ) (n := p) hneg_ne_one
  have hsum_split :
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) = (E.card : ℂ) - O.card := by
    have hsum_union :
        (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          (E ∪ O).sum (fun χ => χ (-1 : ZMod p)) := by
      rw [hunion]
    have hsum_E : E.sum (fun χ => χ (-1 : ZMod p)) = E.card := by
      calc
        E.sum (fun χ => χ (-1 : ZMod p)) = E.sum (fun _ => (1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_even : χ.Even := by simpa [E] using hχ
          simpa [DirichletCharacter.Even] using hχ_even
        _ = E.card := by simp
    have hsum_O : O.sum (fun χ => χ (-1 : ZMod p)) = -(O.card : ℂ) := by
      calc
        O.sum (fun χ => χ (-1 : ZMod p)) = O.sum (fun _ => (-1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_odd : χ.Odd := by simpa [O] using hχ
          simpa [DirichletCharacter.Odd] using hχ_odd
        _ = -(O.card : ℂ) := by simp
    calc
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p))
          = E.sum (fun χ => χ (-1 : ZMod p)) + O.sum (fun χ => χ (-1 : ZMod p)) := by
            rw [hsum_union, Finset.sum_union hdisj]
      _ = (E.card : ℂ) - O.card := by
            rw [hsum_E, hsum_O]
            simp [sub_eq_add_neg]
  have hbalance : (E.card : ℂ) - O.card = 0 := by
    rw [← hsum_split]
    exact hsum_zero
  have hsame : E.card = O.card := by
    have hsame_real : (E.card : ℝ) = O.card := by
      have hdiff_real : (E.card : ℝ) - O.card = 0 := by
        simpa using congrArg Complex.re hbalance
      nlinarith
    exact_mod_cast hsame_real
  have hcard_total : E.card + O.card = p - 1 := by
    calc
      E.card + O.card = (E ∪ O).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Nat.card (DirichletCharacter ℂ p) := by
        rw [hunion, Finset.card_univ, Nat.card_eq_fintype_card]
      _ = p - 1 := card_dirichletCharacter_complex (p := p)
  have hcardE : E.card = (p - 1) / 2 := by
    omega
  simpa [E] using hcardE

lemma card_evenNontrivialCharacters (hp_odd' : p ≠ 2) :
    (evenNontrivialCharacters (p := p)).card = (p - 3) / 2 := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  rw [hrewrite, Finset.card_erase_of_mem]
  · have hcard_even :
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
      card_even_characters_kplus (p := p) hp_odd'
    omega
  · simp [htriv_even]

lemma localPrimeCountPlus_mul_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card := by
  classical
  set d := localResidueDegree (p := p) ℓ hℓp with hd
  set c := localPrimeCount (p := p) ℓ hℓp with hc
  have hprod_card : c * d = Nat.card (DirichletCharacter ℂ p) := by
    simpa [c, d] using (localPrimeCount_mul_localResidueDegree (p := p) hℓp)
  have hprod : c * d = p - 1 := by
    rw [hprod_card, card_dirichletCharacter_complex (p := p)]
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  rw [card_even_characters_kplus (p := p) hp_odd']
  rcases hp_odd_nat with ⟨m, hm⟩
  have hhalf : (p - 1) / 2 = m := by
    omega
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hkdiv : (k + k) / 2 = k := by
      omega
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp = c * k := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hkdiv, ← hc]
    have hck : c * k = m := by
      have hdouble : c * k + c * k = m + m := by
        calc
          c * k + c * k = c * (k + k) := by rw [Nat.mul_add]
          _ = p - 1 := by simpa [hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (c * k) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hck]
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    rcases hd_odd with ⟨k, hk⟩
    have hc_even : Even c := by
      have hprod' : c * (2 * k + 1) = p - 1 := by
        simpa [hk] using hprod
      have h_rhs_even : Even (p - 1) := by
        refine ⟨m, ?_⟩
        rw [hm]
        omega
      by_contra hc_not_even
      have hc_odd : Odd c := Nat.not_even_iff_odd.mp hc_not_even
      have hlhs_odd : Odd (c * (2 * k + 1)) :=
        hc_odd.mul (show Odd (2 * k + 1) by exact ⟨k, rfl⟩)
      have h_lhs_even : Even (c * (2 * k + 1)) := by
        simpa [hprod'] using h_rhs_even
      exact (Nat.not_even_iff_odd.mpr hlhs_odd) h_lhs_even
    rcases hc_even with ⟨j, hj⟩
    have hc_half : localPrimeCount (p := p) ℓ hℓp / 2 = j := by
      rw [← hc, hj]
      simpa [two_mul, Nat.mul_comm] using (Nat.mul_div_right j (by decide : 0 < 2))
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
          j * (2 * k + 1) := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hc_half]
    have hjk : j * (2 * k + 1) = m := by
      have hdouble : j * (2 * k + 1) + j * (2 * k + 1) = m + m := by
        calc
          j * (2 * k + 1) + j * (2 * k + 1) = (j + j) * (2 * k + 1) := by
            rw [Nat.add_mul]
          _ = p - 1 := by simpa [hj, hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (j * (2 * k + 1)) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hjk]

/-- The product over all even characters at `ℓ ≠ p` is a single local factor of
degree `localResidueDegreePlus`, repeated `localPrimeCountPlus` times. -/
lemma prod_even_characters_eval_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (T : ℂ) :
    Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ => (1 - χ (ℓ : ZMod p) * T)) =
      (1 - T ^ localResidueDegreePlus (p := p) ℓ hℓp) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  let E : Finset (DirichletCharacter ℂ p) :=
    Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by
    rw [← hn_units]
    exact Fintype.card_pos
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  have hn_even : Even n := by
    rcases hp_odd_nat with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hn_def, card_dirichletCharacter_complex (p := p), hm]
    omega
  rcases hn_even with ⟨n2, hn2⟩
  have hn2' : n = 2 * n2 := by
    omega
  have hn2_pos : 0 < n2 := by
    omega
  have hnp1 : n = p - 1 := by
    rw [hn_def, card_dirichletCharacter_complex (p := p)]
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' (unitOfPrimeNe (p := p) ℓ hℓp)
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]
    exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']
    exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hfin_g : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n, hn_pos, by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
  have hgcd2 : n.gcd 2 = 2 := by
    apply Nat.dvd_antisymm
    · exact Nat.gcd_dvd_right n 2
    · exact Nat.dvd_gcd ⟨n2, hn2'⟩ dvd_rfl
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hℓ_eq : (ℓ : ZMod p) = (((g : (ZMod p)ˣ) : ZMod p)) ^ a := by
    have h1 : (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p)) = (ℓ : ZMod p) := by
      simp [unitOfPrimeNe]
    rw [← h1, ← ha, Units.val_pow_eq_pow_val]
  have hχAt_ℓ : ∀ k : ℕ, χAt k (ℓ : ZMod p) = ω ^ (k * a) := fun k => by
    rw [hℓ_eq, map_pow, hχAt_g, ← pow_mul]
  have hg_half_sq : ((((g : (ZMod p)ˣ) : ZMod p) ^ n2) ^ 2) = 1 := by
    rw [← pow_mul]
    have : n2 * 2 = n := by
      omega
    rw [this]
    simpa [Units.val_pow_eq_pow_val, hg_order] using
      congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one g)
  have hg_half_ne_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) ≠ 1 := by
    intro hpow
    have hpow_units : g ^ n2 = 1 := by
      apply Units.ext
      simpa using hpow
    have hdvd : n ∣ n2 := by
      rw [← hg_order]
      exact (orderOf_dvd_iff_pow_eq_one (x := g)).2 hpow_units
    have hle : n ≤ n2 := Nat.le_of_dvd hn2_pos hdvd
    rw [hn2] at hle
    omega
  have hg_half_eq_neg_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) = -1 := by
    rcases sq_eq_one_iff.mp hg_half_sq with h1 | h1
    · exact False.elim (hg_half_ne_one h1)
    · exact h1
  let χEvenAt : ℕ → DirichletCharacter ℂ p := fun k => χAt (2 * k)
  have hχEven_mem : ∀ k ∈ Finset.range n2, χEvenAt k ∈ E := by
    intro k hk
    have h_even : χAt (2 * k) (-1 : ZMod p) = 1 := by
      rw [← hg_half_eq_neg_one, map_pow, hχAt_g, ← pow_mul]
      have : (2 * k) * n2 = k * n := by
        rw [hn2']
        simp [Nat.mul_left_comm, Nat.mul_comm]
      rw [this, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    change χAt (2 * k) ∈ E
    rw [show E = Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even) from rfl,
      Finset.mem_filter]
    simp [DirichletCharacter.Even, h_even]
  have hχEven_inj : Set.InjOn χEvenAt ↑(Finset.range n2) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χEvenAt j ((g : (ZMod p)ˣ) : ZMod p) = χEvenAt k ((g : (ZMod p)ˣ) : ZMod p) :=
      congrArg (fun χ : DirichletCharacter ℂ p => χ ((g : (ZMod p)ˣ) : ZMod p)) hjk
    rw [hχAt_g, hχAt_g] at hval
    have hj2 : 2 * j < n := by
      omega
    have hk2 : 2 * k < n := by
      omega
    have h_eq : 2 * j = 2 * k := by
      simpa [χEvenAt] using hω.pow_inj hj2 hk2 hval
    omega
  have hE_card : E.card = n2 := by
    rw [card_even_characters_kplus (p := p) hp_odd']
    omega
  have himage_eq : Finset.image χEvenAt (Finset.range n2) = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨k, hk, rfl⟩
      exact hχEven_mem k hk
    · rw [hE_card, Finset.card_image_of_injOn hχEven_inj, Finset.card_range]
  have hprod_transfer :
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T) =
        ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
    calc
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T)
          = ∏ χ ∈ Finset.image χEvenAt (Finset.range n2), (1 - χ (ℓ : ZMod p) * T) := by
              rw [← himage_eq]
      _ = ∏ k ∈ Finset.range n2, (1 - χEvenAt k (ℓ : ZMod p) * T) := by
            rw [Finset.prod_image hχEven_inj]
      _ = ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
            refine Finset.prod_congr rfl (fun k _ => ?_)
            simpa [χEvenAt] using congrArg (fun z : ℂ => 1 - z * T) (hχAt_ℓ (2 * k))
  have hω_sq_prim' : IsPrimitiveRoot (ω ^ 2) (n / n.gcd 2) :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos 2 hω
  have hω_sq_prim : IsPrimitiveRoot (ω ^ 2) n2 := by
    simpa [hgcd2, hn2'] using hω_sq_prim'
  have hcollapse :
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) =
        (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a := by
    calc
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T)
          = ∏ k ∈ Finset.range n2, (1 - (ω ^ 2) ^ (k * a) * T) := by
              refine Finset.prod_congr rfl (fun k _ => ?_)
              congr 1
              have hexp : (2 * k) * a = 2 * (k * a) := by
                simp [Nat.mul_assoc, Nat.mul_comm]
              rw [hexp, pow_mul]
      _ = (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a :=
            prod_pow_primRoot_eq_pow_kplus hn2_pos a hω_sq_prim T
  have hfin_g2 : IsOfFinOrder (g ^ 2) := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n2, hn2_pos, by
      rw [← pow_mul]
      have : 2 * n2 = n := by
        omega
      rw [this, ← hg_order]
      exact pow_orderOf_eq_one g⟩
  have hg_sq_order : orderOf (g ^ 2) = n2 := by
    rw [hfin_g.orderOf_pow, hg_order, hgcd2, hn2']
    simp
  have hu_sq : (unitOfPrimeNe (p := p) ℓ hℓp) ^ 2 = (g ^ 2) ^ a := by
    rw [← ha, ← pow_mul]
    have : a * 2 = 2 * a := by
      omega
    rw [this, pow_mul]
  have horder_u_sq : orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) = n2 / n2.gcd a := by
    rw [hu_sq, hfin_g2.orderOf_pow, hg_sq_order]
  have hlocalResidue :
      localResidueDegreePlus (p := p) ℓ hℓp = n2 / n2.gcd a := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp, horder_u_sq]
  have hlocalResiduePlus_pos : 0 < localResidueDegreePlus (p := p) ℓ hℓp := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp]
    exact orderOf_pos _
  have hlocalResidue_pos : 0 < n2 / n2.gcd a := by
    simpa [hlocalResidue] using hlocalResiduePlus_pos
  have hcount_mul : localPrimeCountPlus (p := p) ℓ hℓp * (n2 / n2.gcd a) = n2 := by
    have hbase := localPrimeCountPlus_mul_localResidueDegreePlus (p := p) hp_odd' hℓp
    rw [hlocalResidue] at hbase
    simpa [E, hE_card] using hbase
  have hgcd_mul : n2.gcd a * (n2 / n2.gcd a) = n2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n2 a)
  have hlocalPrimeCount :
      localPrimeCountPlus (p := p) ℓ hℓp = n2.gcd a := by
    have hmul :
        (n2 / n2.gcd a) * localPrimeCountPlus (p := p) ℓ hℓp =
          (n2 / n2.gcd a) * (n2.gcd a) := by
      rw [Nat.mul_comm (n2 / n2.gcd a) (localPrimeCountPlus (p := p) ℓ hℓp),
        Nat.mul_comm (n2 / n2.gcd a) (n2.gcd a), hcount_mul, hgcd_mul]
    exact Nat.eq_of_mul_eq_mul_left hlocalResidue_pos hmul
  simpa [E] using
    (Eq.trans hprod_transfer (Eq.trans hcollapse (by rw [← hlocalResidue, ← hlocalPrimeCount])))

lemma trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) {s : ℂ} :
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
      (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  have htrivial_mul :
      (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
        Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
          (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := by
    unfold evenCharLocalFactor
    rw [hrewrite, ← Finset.mul_prod_erase
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ : DirichletCharacter ℂ p => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s)))]
    · have hℓ_unit : IsUnit ((ℓ : ZMod p)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (coprime_of_prime_ne (p := p) hℓp).symm
      rw [MulChar.one_apply hℓ_unit, one_mul]
    · simp [htriv_even]
  calc
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s
        = Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
            (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := htrivial_mul
    _ =
        (1 - (((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp)) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            simpa using
              prod_even_characters_eval_eq_pow_localResidueDegreePlus (p := p) hp_odd' hℓp
                ((ℓ : ℂ) ^ (-s))
    _ =
        (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            congr 1
            congr 1
            rw [show ((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp =
                (ℓ : ℂ) ^ ((-s) * ((localResidueDegreePlus (p := p) ℓ hℓp : ℕ) : ℂ)) by
                  rw [Complex.cpow_mul_nat]]
            congr 1
            ring

end KplusLocalCharacters

end BernoulliRegular
