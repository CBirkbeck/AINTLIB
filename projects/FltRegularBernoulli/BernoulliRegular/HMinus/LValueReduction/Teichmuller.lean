module

public import BernoulliRegular.BernoulliGeneralized
public import BernoulliRegular.HMinus.LValueReduction.Final

/-!
# Teichmüller reindexing for `hMinus`

This file rewrites the odd-character product in `hMinus_formula` as a product
over odd powers of the Teichmüller character in the `p`-adic coefficient ring.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section Teichmuller

variable (p : ℕ) [hp : Fact p.Prime]

lemma prime_sub_one_pos : 0 < p - 1 :=
  Nat.sub_pos_of_lt hp.out.one_lt

lemma prime_sub_one_ne_zero : p - 1 ≠ 0 :=
  (prime_sub_one_pos (p := p)).ne'

/-- The abstract index type for odd characters modulo `p`: odd exponents in
`Fin (p - 1)`. This is the common finite indexing object used to compare the
complex and `ℚ_[p]` odd-character families. -/
abbrev OddCharacterIndex := {j : Fin (p - 1) // Odd (j : ℕ)}

theorem card_oddCharacterIndex (hp_odd' : p ≠ 2) :
    Nat.card (OddCharacterIndex p) = (p - 1) / 2 := by
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨m, hm⟩
  have hhalf : (p - 1) / 2 = m := by
    omega
  let e : Fin m ≃ OddCharacterIndex p := {
    toFun := fun k =>
      ⟨⟨2 * (k : ℕ) + 1, by
          rw [hm]
          omega⟩, ⟨(k : ℕ), rfl⟩⟩
    invFun := fun j =>
      ⟨Classical.choose j.2, by
      have hk : (j.1 : ℕ) = 2 * Classical.choose j.2 + 1 := Classical.choose_spec j.2
      have hj_lt : (j.1 : ℕ) < p - 1 := j.1.is_lt
      omega⟩
    left_inv := fun k => by
      apply Fin.ext
      change Classical.choose (show Odd (2 * (k : ℕ) + 1) from ⟨(k : ℕ), rfl⟩) = (k : ℕ)
      have hk :
          2 * Classical.choose (show Odd (2 * (k : ℕ) + 1) from ⟨(k : ℕ), rfl⟩) + 1 =
            2 * (k : ℕ) + 1 :=
        (Classical.choose_spec (show Odd (2 * (k : ℕ) + 1) from ⟨(k : ℕ), rfl⟩)).symm
      omega
    right_inv := fun j => by
      apply Subtype.ext
      apply Fin.ext
      change 2 * Classical.choose j.2 + 1 = (j.1 : ℕ)
      exact (Classical.choose_spec j.2).symm }
  calc
    Nat.card (OddCharacterIndex p) = Nat.card (Fin m) := Nat.card_congr e.symm
    _ = m := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    _ = (p - 1) / 2 := hhalf.symm

theorem card_oddCharacterIndex_eq_card_oddCharacters (hp_odd' : p ≠ 2) :
    Nat.card (OddCharacterIndex p) = (oddCharacters (p := p)).card := by
  rw [card_oddCharacterIndex (p := p) hp_odd', card_oddCharacters (p := p) hp_odd']

omit hp in
theorem oddCharacterIndex_ne_two (j : OddCharacterIndex p) : p ≠ 2 := by
  intro hp_two
  rcases j.2 with ⟨k, hk⟩
  have hj_lt : (j.1 : ℕ) < p - 1 := j.1.is_lt
  omega

/-- A fixed generator of `(ZMod p)ˣ`, used for the concrete polynomial model in
`T023g1b2`. -/
noncomputable def unitGroupGenerator : (ZMod p)ˣ :=
  (IsCyclic.exists_generator (α := (ZMod p)ˣ)).choose

theorem unitGroupGenerator_zpowers :
    ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers (unitGroupGenerator p) := by
  simpa [unitGroupGenerator] using
    (IsCyclic.exists_generator (α := (ZMod p)ˣ)).choose_spec

theorem orderOf_unitGroupGenerator :
    orderOf (unitGroupGenerator p) = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers (unitGroupGenerator_zpowers (p := p)),
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem unitGroupGenerator_pow_eq_iff_of_lt {m n : ℕ}
    (hm : m < p - 1) (hn : n < p - 1) :
    unitGroupGenerator p ^ m = unitGroupGenerator p ^ n ↔ m = n := by
  constructor
  · intro hmn
    have hmod :
        m ≡ n [MOD orderOf (unitGroupGenerator p)] := by
      simpa using (pow_eq_pow_iff_modEq (x := unitGroupGenerator p) (n := m) (m := n)).mp hmn
    have hmod' : m ≡ n [MOD p - 1] := by
      simpa [orderOf_unitGroupGenerator (p := p)] using hmod
    have hEq : m % (p - 1) = n := Nat.mod_eq_of_modEq hmod' hn
    simpa [Nat.mod_eq_of_lt hm] using hEq
  · rintro rfl
    rfl

/-- The complementary exponent to `j` modulo `p - 1`, normalized to the range
`[0, p - 1)`. -/
def complementExponent (j : Fin (p - 1)) : ℕ := (p - 1) - (j : ℕ)

/-- The rational coefficient attached to the residue represented by the `m`-th
power of the chosen generator of `(ZMod p)ˣ`. -/
noncomputable def oddBernoulliKernelCoeff (m : Fin (p - 1)) : ℚ :=
  ((((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val : ℚ)

/-- The explicit polynomial whose two realizations control the complex and
`ℚ_[p]` odd Bernoulli factors in `T023g1b2`. -/
noncomputable def oddBernoulliKernelPoly (j : Fin (p - 1)) : Polynomial ℚ :=
  ∑ m : Fin (p - 1),
    Polynomial.monomial ((m : ℕ) * complementExponent (p := p) j)
      (oddBernoulliKernelCoeff (p := p) m)

theorem unitGroupGenerator_pow_bijective :
    Function.Bijective fun m : Fin (p - 1) => unitGroupGenerator p ^ (m : ℕ) := by
  let f : Fin (p - 1) → (ZMod p)ˣ := fun m => unitGroupGenerator p ^ (m : ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_, ?_⟩
  · intro m n hmn
    exact Fin.ext <| (unitGroupGenerator_pow_eq_iff_of_lt (p := p) m.is_lt n.is_lt).mp hmn
  · rw [Fintype.card_fin, ZMod.card_units]

/-- The powers of `unitGroupGenerator` enumerate all units of `ZMod p`. -/
noncomputable def unitGroupGeneratorPowEquiv : Fin (p - 1) ≃ (ZMod p)ˣ :=
  Equiv.ofBijective (fun m : Fin (p - 1) => unitGroupGenerator p ^ (m : ℕ))
    (unitGroupGenerator_pow_bijective (p := p))

theorem sum_zmod_eq_sum_unitGroupGeneratorPowers
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R) (hF0 : F 0 = 0) :
    ∑ a : ZMod p, F a =
      ∑ m : Fin (p - 1), F (((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := by
  have hsplit :
      ∑ a : ZMod p, F a = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne F (0 : ZMod p)
  have hnonzero :
      ∑ a : {a : ZMod p // a ≠ 0}, F a.1 =
        ∑ u : (ZMod p)ˣ, F (u : ZMod p) := by
    simpa using
      (Fintype.sum_equiv unitsEquivNeZero
        (fun u : (ZMod p)ˣ => F (u : ZMod p))
        (fun a : {a : ZMod p // a ≠ 0} => F a.1)
        (fun u => rfl)).symm
  have hpowers :
      ∑ u : (ZMod p)ˣ, F (u : ZMod p) =
        ∑ m : Fin (p - 1), F (((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := by
    simpa using
      (Fintype.sum_equiv (unitGroupGeneratorPowEquiv (p := p))
        (fun m : Fin (p - 1) => F (((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p))
        (fun u : (ZMod p)ˣ => F (u : ZMod p))
        (fun m => rfl)).symm
  calc
    ∑ a : ZMod p, F a = F 0 + ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := hsplit
    _ = ∑ a : {a : ZMod p // a ≠ 0}, F a.1 := by rw [hF0, zero_add]
    _ = ∑ u : (ZMod p)ˣ, F (u : ZMod p) := hnonzero
    _ = ∑ m : Fin (p - 1), F (((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p) := hpowers

theorem oddCharacter_ne_one {R : Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ : DirichletCharacter R p} (hχ_odd : χ.Odd) :
    χ ≠ 1 := by
  rintro rfl
  exact DirichletCharacter.Odd.not_even _ hχ_odd (by
    change (1 : DirichletCharacter R p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (isUnit_one.neg)])

theorem oddBernoulliFactor_eq_sum {R : Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ : DirichletCharacter R p} (hχ_odd : χ.Odd) :
    (-(1 / 2 : R)) * BernoulliGen (χ⁻¹) 1 =
      ((p : R)⁻¹ * (-(1 / 2 : R))) *
        ∑ a : ZMod p, (χ⁻¹) a * (a.val : R) := by
  have hpR_ne_zero : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hχinv_ne_one : χ⁻¹ ≠ 1 := by
    intro hχinv
    apply oddCharacter_ne_one (p := p) hχ_odd
    simpa using congrArg Inv.inv hχinv
  calc
    (-(1 / 2 : R)) * BernoulliGen (χ⁻¹) 1 =
        ((p : R)⁻¹ * (p : R)) * ((-(1 / 2 : R)) * BernoulliGen (χ⁻¹) 1) := by
          rw [inv_mul_cancel₀ hpR_ne_zero, one_mul]
    _ = (p : R)⁻¹ * ((-(1 / 2 : R)) * ((p : R) * BernoulliGen (χ⁻¹) 1)) := by
          ac_rfl
    _ = (p : R)⁻¹ * ((-(1 / 2 : R)) * ∑ a : ZMod p, (χ⁻¹) a * (a.val : R)) := by
          rw [natCast_mul_BernoulliGen_one_of_ne_one (R := R) (N := p) (χ := χ⁻¹) hχinv_ne_one]
    _ = ((p : R)⁻¹ * (-(1 / 2 : R))) * ∑ a : ZMod p, (χ⁻¹) a * (a.val : R) := by
          ac_rfl

theorem complexCharacters_isCyclic : IsCyclic (DirichletCharacter ℂ p) :=
  ((dirichletCharacterMulEquivUnits (p := p)).isCyclic).2 inferInstance

/-- A chosen generator of the complex Dirichlet character group mod `p`. -/
noncomputable def complexCharacterGenerator : DirichletCharacter ℂ p := by
  letI : IsCyclic (DirichletCharacter ℂ p) := complexCharacters_isCyclic (p := p)
  exact (IsCyclic.exists_monoid_generator (α := DirichletCharacter ℂ p)).choose

/-- The complex value of `complexCharacterGenerator` at the chosen generator of
`(ZMod p)ˣ`. -/
noncomputable def complexGeneratorRoot : ℂ :=
  complexCharacterGenerator p (((unitGroupGenerator p : (ZMod p)ˣ) : ZMod p))

theorem complexCharacterGenerator_powers :
    ∀ χ : DirichletCharacter ℂ p, χ ∈ Submonoid.powers (complexCharacterGenerator p) := by
  letI : IsCyclic (DirichletCharacter ℂ p) := complexCharacters_isCyclic (p := p)
  simpa [complexCharacterGenerator] using
    (IsCyclic.exists_monoid_generator (α := DirichletCharacter ℂ p)).choose_spec

theorem orderOf_complexCharacterGenerator :
    orderOf (complexCharacterGenerator p) = p - 1 := by
  calc
    orderOf (complexCharacterGenerator p) = Nat.card (DirichletCharacter ℂ p) :=
      orderOf_eq_card_of_forall_mem_powers (complexCharacterGenerator_powers (p := p))
    _ = p - 1 := card_dirichletCharacter_complex (p := p)

theorem complexCharacterGenerator_apply_unitGroupGeneratorPow (m : ℕ) :
    complexCharacterGenerator p (((unitGroupGenerator p) ^ m : (ZMod p)ˣ) : ZMod p) =
      complexGeneratorRoot p ^ m := by
  change complexCharacterGenerator p ((((unitGroupGenerator p : (ZMod p)ˣ) : ZMod p) ^ m)) =
    complexGeneratorRoot p ^ m
  rw [map_pow]
  rfl

theorem complexCharacterGenerator_pow_eq_one_of_generatorRoot_pow_eq_one {l : ℕ}
    (hl : complexGeneratorRoot p ^ l = 1) :
    (complexCharacterGenerator p) ^ l = 1 := by
  apply (MulChar.eq_one_iff).2
  intro a
  let m : Fin (p - 1) := (unitGroupGeneratorPowEquiv (p := p)).symm a
  have hm : ((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) = a :=
    (unitGroupGeneratorPowEquiv (p := p)).apply_symm_apply a
  rw [← hm, MulChar.pow_apply_coe, complexCharacterGenerator_apply_unitGroupGeneratorPow]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hl, one_pow]

theorem complexGeneratorRoot_isPrimitiveRoot :
    IsPrimitiveRoot (complexGeneratorRoot p) (p - 1) := by
  refine ⟨?_, fun l hl => ?_⟩
  · calc
      complexGeneratorRoot p ^ (p - 1) =
          complexCharacterGenerator p
            ((((unitGroupGenerator p) ^ (p - 1) : (ZMod p)ˣ) : ZMod p)) := by
            symm
            exact complexCharacterGenerator_apply_unitGroupGeneratorPow (p := p) (p - 1)
      _ = complexCharacterGenerator p (1 : ZMod p) := by
            rw [show (unitGroupGenerator p) ^ (p - 1) = (1 : (ZMod p)ˣ) by
              rw [← orderOf_unitGroupGenerator (p := p), pow_orderOf_eq_one]]
            simp
      _ = 1 := by
            simp
  · have hpow : (complexCharacterGenerator p) ^ l = 1 :=
      complexCharacterGenerator_pow_eq_one_of_generatorRoot_pow_eq_one (p := p) hl
    have hdiv : orderOf (complexCharacterGenerator p) ∣ l :=
      (orderOf_dvd_iff_pow_eq_one (x := complexCharacterGenerator p)).2 hpow
    simpa [orderOf_complexCharacterGenerator (p := p)] using hdiv

theorem complexCharacterGenerator_pow_inv_eq_pow_complement (j : Fin (p - 1)) :
    (((complexCharacterGenerator p) ^ (j : ℕ))⁻¹ : DirichletCharacter ℂ p) =
      (complexCharacterGenerator p) ^ complementExponent (p := p) j := by
  apply inv_eq_of_mul_eq_one_right
  have hj : (j : ℕ) + complementExponent (p := p) j = p - 1 := by
    dsimp [complementExponent]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add, hj, ← orderOf_complexCharacterGenerator (p := p), pow_orderOf_eq_one]

theorem complexCharacterGenerator_pow_eq_iff_of_lt {i j : ℕ}
    (hi : i < p - 1) (hj : j < p - 1) :
    (complexCharacterGenerator p) ^ i = (complexCharacterGenerator p) ^ j ↔ i = j := by
  constructor
  · intro hij
    have hmod :
        i ≡ j [MOD orderOf (complexCharacterGenerator p)] := by
      simpa using (pow_eq_pow_iff_modEq (x := complexCharacterGenerator p) (n := i) (m := j)).mp hij
    have hmod' : i ≡ j [MOD p - 1] := by
      simpa [orderOf_complexCharacterGenerator (p := p)] using hmod
    have hEq : i % (p - 1) = j := Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl

theorem exists_oddCharacter (hp_odd' : p ≠ 2) :
    ∃ χ : DirichletCharacter ℂ p, χ.Odd := by
  classical
  have hcard_pos : 0 < (oddCharacters (p := p)).card := by
    rw [card_oddCharacters (p := p) hp_odd']
    have hp_gt_two : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
    omega
  obtain ⟨χ, hχ⟩ := Finset.card_pos.mp hcard_pos
  exact ⟨χ, (Finset.mem_filter.mp hχ).2⟩

theorem complexCharacterGenerator_odd (hp_odd' : p ≠ 2) :
    (complexCharacterGenerator p).Odd := by
  rcases DirichletCharacter.even_or_odd (complexCharacterGenerator p) with h_even | h_odd
  · exfalso
    obtain ⟨χ, hχ_odd⟩ := exists_oddCharacter (p := p) hp_odd'
    rcases (Submonoid.mem_powers_iff χ (complexCharacterGenerator p)).mp
      (complexCharacterGenerator_powers (p := p) χ) with ⟨n, rfl⟩
    have hpow_even : ((complexCharacterGenerator p) ^ n).Even := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
        simpa using (MulChar.one_apply (R := ZMod p) (R' := ℂ) isUnit_one.neg)
      · change ((complexCharacterGenerator p) ^ n) (-1 : ZMod p) = 1
        rw [MulChar.pow_apply' _ hn.ne', h_even, one_pow]
    exact DirichletCharacter.Odd.not_even _ hχ_odd hpow_even
  · exact h_odd

theorem complexCharacterGenerator_pow_apply_neg_one (hp_odd' : p ≠ 2) (i : ℕ) :
    ((complexCharacterGenerator p) ^ i) (-1 : ZMod p) = (-1 : ℂ) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R := ZMod p) (R' := ℂ) isUnit_one.neg)
  · rw [MulChar.pow_apply' _ hi.ne', complexCharacterGenerator_odd (p := p) hp_odd']

theorem complexCharacterGenerator_pow_odd_iff (hp_odd' : p ≠ 2) (i : ℕ) :
    ((complexCharacterGenerator p) ^ i).Odd ↔ Odd i := by
  change ((complexCharacterGenerator p) ^ i) (-1 : ZMod p) = (-1 : ℂ) ↔ Odd i
  rw [complexCharacterGenerator_pow_apply_neg_one (p := p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)

noncomputable def oddComplexCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact (Finset.univ : Finset (OddCharacterIndex p)).image
    (fun j => (complexCharacterGenerator p) ^ (j.1 : ℕ))

theorem oddCharacters_eq_image_oddComplexPowers (hp_odd' : p ≠ 2) :
    oddCharacters (p := p) = oddComplexCharacters (p := p) := by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
    rcases (Submonoid.mem_powers_iff χ (complexCharacterGenerator p)).mp
      (complexCharacterGenerator_powers (p := p) χ) with ⟨j, hj⟩
    let k : Fin (p - 1) := ⟨j % (p - 1), Nat.mod_lt j (prime_sub_one_pos (p := p))⟩
    have hk_eq : (complexCharacterGenerator p) ^ (k : ℕ) = χ := by
      dsimp [k]
      calc
        (complexCharacterGenerator p) ^ (j % (p - 1)) =
            (complexCharacterGenerator p) ^ (j % orderOf (complexCharacterGenerator p)) := by
              rw [orderOf_complexCharacterGenerator (p := p)]
        _ = (complexCharacterGenerator p) ^ j := by rw [pow_mod_orderOf]
        _ = χ := hj
    have hk_odd : Odd (k : ℕ) := by
      have hk_odd' : ((complexCharacterGenerator p) ^ (k : ℕ)).Odd := by simpa [hk_eq] using hχ_odd
      exact (complexCharacterGenerator_pow_odd_iff (p := p) hp_odd' (k : ℕ)).1 hk_odd'
    refine Finset.mem_image.mpr ⟨⟨k, hk_odd⟩, Finset.mem_univ _, ?_⟩
    simpa using hk_eq
  · intro hχ
    unfold oddComplexCharacters at hχ
    rcases Finset.mem_image.mp hχ with ⟨j, -, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      exact (complexCharacterGenerator_pow_odd_iff (p := p) hp_odd' (j.1 : ℕ)).2 j.2⟩

theorem prod_oddCharacters_eq_prod_oddCharacterIndex (hp_odd' : p ≠ 2)
    {α : Type*} [CommMonoid α] (F : DirichletCharacter ℂ p → α) :
    Finset.prod (oddCharacters (p := p)) F =
      Finset.prod (Finset.univ : Finset (OddCharacterIndex p))
        (fun j => F ((complexCharacterGenerator p) ^ (j.1 : ℕ))) := by
  classical
  rw [oddCharacters_eq_image_oddComplexPowers (p := p) hp_odd']
  unfold oddComplexCharacters
  exact Finset.prod_image fun a _ b _ hab =>
    Subtype.ext <| Fin.ext <|
      (complexCharacterGenerator_pow_eq_iff_of_lt (p := p) a.1.is_lt b.1.is_lt).mp hab

theorem complexBernoulliSum_eq_eval_oddBernoulliKernelPoly (j : Fin (p - 1)) :
    ∑ a : ZMod p, ((((complexCharacterGenerator p) ^ (j : ℕ))⁻¹) a) * (a.val : ℂ) =
      Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
        (oddBernoulliKernelPoly (p := p) j) := by
  have hEval :
      Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
        (oddBernoulliKernelPoly (p := p) j) =
          ∑ m : Fin (p - 1),
            Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
              (Polynomial.monomial ((m : ℕ) * complementExponent (p := p) j)
                (oddBernoulliKernelCoeff (p := p) m)) := by
    simpa [oddBernoulliKernelPoly] using
      (Polynomial.eval₂_finsetSum (f := algebraMap ℚ ℂ) (s := Finset.univ)
        (g := fun m : Fin (p - 1) =>
          Polynomial.monomial ((m : ℕ) * complementExponent (p := p) j)
            (oddBernoulliKernelCoeff (p := p) m))
        (x := complexGeneratorRoot p))
  rw [sum_zmod_eq_sum_unitGroupGeneratorPowers (p := p)
    (F := fun a => ((((complexCharacterGenerator p) ^ (j : ℕ))⁻¹) a) * (a.val : ℂ))
    (hF0 := by simp), hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff :
      algebraMap ℚ ℂ (oddBernoulliKernelCoeff (p := p) m) =
        (((((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val : ℂ)) := by
    rw [oddBernoulliKernelCoeff]
    exact map_ratCast (algebraMap ℚ ℂ)
      (((((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val : ℚ))
  rw [Polynomial.eval₂_monomial, complexCharacterGenerator_pow_inv_eq_pow_complement (p := p) j,
    MulChar.pow_apply_coe, complexCharacterGenerator_apply_unitGroupGeneratorPow]
  rw [hcoeff, pow_mul]
  ac_rfl

theorem complexOddBernoulliFactor_eq_eval_oddBernoulliKernelPoly (j : OddCharacterIndex p) :
    (-(1 / 2 : ℂ)) * BernoulliGen (((complexCharacterGenerator p) ^ (j.1 : ℕ))⁻¹) 1 =
      ((p : ℂ)⁻¹ * (-(1 / 2 : ℂ))) *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
          (oddBernoulliKernelPoly (p := p) j.1) := by
  rw [oddBernoulliFactor_eq_sum (p := p)
    (χ := (complexCharacterGenerator p) ^ (j.1 : ℕ))
    ((complexCharacterGenerator_pow_odd_iff (p := p) (oddCharacterIndex_ne_two (p := p) j)
      (j.1 : ℕ)).2 j.2)]
  rw [complexBernoulliSum_eq_eval_oddBernoulliKernelPoly (p := p) j.1]

lemma exponent_zmodUnits_eq_prime_sub_one :
    Monoid.exponent (ZMod p)ˣ = p - 1 := by
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units]

theorem qpadic_hasEnoughRootsOfUnity_prime_sub_one :
    HasEnoughRootsOfUnity ℚ_[p] (p - 1) := by
  letI : NeZero (p - 1) := ⟨prime_sub_one_ne_zero (p := p)⟩
  apply HasEnoughRootsOfUnity.of_card_le (R := ℚ_[p])
  refine le_of_eq ?_
  rw [eq_comm, card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨((teichmuller p (g : ZMod p) : ℤ_[p]) : ℚ_[p]), ?_⟩
  exact (teichmuller_isPrimitiveRoot_of_generator (p := p) hg_gen).map_of_injective
    (f := PadicInt.Coe.ringHom) (hf := fun _ _ h => Subtype.coe_injective h)

theorem card_dirichletCharacterQp :
    Nat.card (DirichletCharacter ℚ_[p] p) = p - 1 := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : HasEnoughRootsOfUnity ℚ_[p] (Monoid.exponent (ZMod p)ˣ) := by
    simpa [exponent_zmodUnits_eq_prime_sub_one (p := p)] using
      qpadic_hasEnoughRootsOfUnity_prime_sub_one (p := p)
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.out]

/-- The `ℚ_[p]` value of `teichmullerCharQp` at the chosen generator of
`(ZMod p)ˣ`. -/
noncomputable def qpadicGeneratorRoot : ℚ_[p] :=
  (((teichmuller p (((unitGroupGenerator p : (ZMod p)ˣ) : ZMod p)) : ℤ_[p])) : ℚ_[p])

theorem qpadicGeneratorRoot_isPrimitiveRoot :
    IsPrimitiveRoot (qpadicGeneratorRoot p) (p - 1) := by
  simpa [qpadicGeneratorRoot] using
    (teichmuller_isPrimitiveRoot_of_generator (p := p) (g := unitGroupGenerator p)
      (unitGroupGenerator_zpowers (p := p))).map_of_injective
      (f := PadicInt.Coe.ringHom) (hf := fun _ _ h => Subtype.coe_injective h)

theorem teichmullerCharQp_apply_unitGroupGeneratorPow (m : ℕ) :
    teichmullerCharQp p (((unitGroupGenerator p) ^ m : (ZMod p)ˣ) : ZMod p) =
      qpadicGeneratorRoot p ^ m := by
  change teichmullerCharQp p ((((unitGroupGenerator p : (ZMod p)ˣ) : ZMod p) ^ m)) =
    qpadicGeneratorRoot p ^ m
  rw [teichmullerCharQp, MulChar.ringHomComp_apply, teichmullerChar_apply, map_pow]
  rfl

theorem teichmullerCharQp_pow_inv_eq_pow_complement (j : Fin (p - 1)) :
    (((teichmullerCharQp p) ^ (j : ℕ))⁻¹ : DirichletCharacter ℚ_[p] p) =
      (teichmullerCharQp p) ^ complementExponent (p := p) j := by
  apply inv_eq_of_mul_eq_one_right
  have hj : (j : ℕ) + complementExponent (p := p) j = p - 1 := by
    dsimp [complementExponent]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add, hj, ← orderOf_teichmullerCharQp (p := p), pow_orderOf_eq_one]

theorem teichmullerCharQp_pow_eq_iff_of_lt {i j : ℕ}
    (hi : i < p - 1) (hj : j < p - 1) :
    (teichmullerCharQp p) ^ i = (teichmullerCharQp p) ^ j ↔ i = j := by
  constructor
  · intro hij
    have hmod :
        i ≡ j [MOD orderOf (teichmullerCharQp p)] := by
      simpa using (pow_eq_pow_iff_modEq (x := teichmullerCharQp p) (n := i) (m := j)).mp hij
    have hmod' : i ≡ j [MOD p - 1] := by
      simpa [orderOf_teichmullerCharQp (p := p)] using hmod
    have hEq : i % (p - 1) = j := Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl

theorem teichmullerCharQp_pow_bijective :
    Function.Bijective fun j : Fin (p - 1) => (teichmullerCharQp p) ^ (j : ℕ) := by
  let f : Fin (p - 1) → DirichletCharacter ℚ_[p] p := fun j => (teichmullerCharQp p) ^ (j : ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_, ?_⟩
  · intro i j hij
    exact Fin.ext <| (teichmullerCharQp_pow_eq_iff_of_lt (p := p) i.is_lt j.is_lt).mp hij
  · rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_dirichletCharacterQp (p := p)]

theorem teichmullerCharQp_pow_apply_neg_one (hp_odd' : p ≠ 2) (i : ℕ) :
    ((teichmullerCharQp p) ^ i) (-1 : ZMod p) = (-1 : ℚ_[p]) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R := ZMod p) (R' := ℚ_[p]) isUnit_one.neg)
  · rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := i), MulChar.ringHomComp_apply,
      teichmullerChar_pow_apply_neg_one (p := p) hp_odd' i, map_pow]
    rfl

theorem teichmullerCharQp_pow_odd_iff (hp_odd' : p ≠ 2) (i : ℕ) :
    ((teichmullerCharQp p) ^ i).Odd ↔ Odd i := by
  change ((teichmullerCharQp p) ^ i) (-1 : ZMod p) = (-1 : ℚ_[p]) ↔ Odd i
  rw [teichmullerCharQp_pow_apply_neg_one (p := p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℚ_[p]) ≠ 1)

noncomputable def oddTeichmullerExponents : Finset ℕ :=
  (Finset.range (p - 1)).filter fun j => Odd j

noncomputable def oddCharactersQp : Finset (DirichletCharacter ℚ_[p] p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Odd

noncomputable def oddTeichmullerCharactersQp : Finset (DirichletCharacter ℚ_[p] p) := by
  classical
  exact (oddTeichmullerExponents (p := p)).image fun j => (teichmullerCharQp p) ^ j

theorem oddCharactersQp_eq_image_oddTeichmullerPowers (hp_odd' : p ≠ 2) :
    oddCharactersQp (p := p) =
      oddTeichmullerCharactersQp (p := p) := by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd : χ.Odd := by
      simpa [oddCharactersQp] using hχ
    rcases (teichmullerCharQp_pow_bijective (p := p)).surjective χ with ⟨j, hj⟩
    have hj_odd : Odd (j : ℕ) := by
      have hj' : ((teichmullerCharQp p) ^ (j : ℕ)).Odd := by simpa [hj] using hχ_odd
      exact (teichmullerCharQp_pow_odd_iff (p := p) hp_odd' (j : ℕ)).1 hj'
    refine Finset.mem_image.mpr ⟨(j : ℕ), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.is_lt, hj_odd⟩
    · simpa using hj
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j, hj, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      exact (teichmullerCharQp_pow_odd_iff (p := p) hp_odd' j).2
        ((Finset.mem_filter.mp hj).2)⟩

noncomputable def oddQpCharacters : Finset (DirichletCharacter ℚ_[p] p) := by
  classical
  exact (Finset.univ : Finset (OddCharacterIndex p)).image
    (fun j => (teichmullerCharQp p) ^ (j.1 : ℕ))

theorem oddCharactersQp_eq_oddQpCharacters (hp_odd' : p ≠ 2) :
    oddCharactersQp (p := p) = oddQpCharacters (p := p) := by
  classical
  rw [oddCharactersQp_eq_image_oddTeichmullerPowers (p := p) hp_odd']
  unfold oddTeichmullerCharactersQp oddQpCharacters
  ext χ
  constructor
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j, hj, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨⟨j, Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩,
      (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j, -, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(j.1 : ℕ), Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr j.1.is_lt, j.2⟩, ?_⟩
    rfl

theorem prod_oddCharactersQp_eq_prod_oddCharacterIndex (hp_odd' : p ≠ 2)
    {α : Type*} [CommMonoid α] (F : DirichletCharacter ℚ_[p] p → α) :
    Finset.prod (oddCharactersQp (p := p)) F =
      Finset.prod (Finset.univ : Finset (OddCharacterIndex p))
        (fun j => F ((teichmullerCharQp p) ^ (j.1 : ℕ))) := by
  classical
  rw [oddCharactersQp_eq_oddQpCharacters (p := p) hp_odd']
  unfold oddQpCharacters
  exact Finset.prod_image fun a _ b _ hab =>
    Subtype.ext <| Fin.ext <|
      (teichmullerCharQp_pow_eq_iff_of_lt (p := p) a.1.is_lt b.1.is_lt).mp hab

theorem qpadicBernoulliSum_eq_eval_oddBernoulliKernelPoly (j : Fin (p - 1)) :
    ∑ a : ZMod p, ((((teichmullerCharQp p) ^ (j : ℕ))⁻¹) a) * (a.val : ℚ_[p]) =
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
        (oddBernoulliKernelPoly (p := p) j) := by
  have hEval :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
        (oddBernoulliKernelPoly (p := p) j) =
          ∑ m : Fin (p - 1),
            Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
              (Polynomial.monomial ((m : ℕ) * complementExponent (p := p) j)
                (oddBernoulliKernelCoeff (p := p) m)) := by
    simpa [oddBernoulliKernelPoly] using
      (Polynomial.eval₂_finsetSum (f := algebraMap ℚ ℚ_[p]) (s := Finset.univ)
        (g := fun m : Fin (p - 1) =>
          Polynomial.monomial ((m : ℕ) * complementExponent (p := p) j)
            (oddBernoulliKernelCoeff (p := p) m))
        (x := qpadicGeneratorRoot p))
  rw [sum_zmod_eq_sum_unitGroupGeneratorPowers (p := p)
    (F := fun a => ((((teichmullerCharQp p) ^ (j : ℕ))⁻¹) a) * (a.val : ℚ_[p]))
    (hF0 := by simp), hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff :
      algebraMap ℚ ℚ_[p] (oddBernoulliKernelCoeff (p := p) m) =
        (((((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val : ℚ_[p])) := by
    rw [oddBernoulliKernelCoeff]
    exact map_ratCast (algebraMap ℚ ℚ_[p])
      (((((unitGroupGenerator p) ^ (m : ℕ) : (ZMod p)ˣ) : ZMod p).val : ℚ))
  rw [Polynomial.eval₂_monomial, teichmullerCharQp_pow_inv_eq_pow_complement (p := p) j,
    MulChar.pow_apply_coe, teichmullerCharQp_apply_unitGroupGeneratorPow]
  rw [hcoeff, pow_mul]
  ac_rfl

theorem qpadicOddBernoulliFactor_eq_eval_oddBernoulliKernelPoly (j : OddCharacterIndex p) :
    (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1 =
      ((p : ℚ_[p])⁻¹ * (-(1 / 2 : ℚ_[p]))) *
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
          (oddBernoulliKernelPoly (p := p) j.1) := by
  rw [oddBernoulliFactor_eq_sum (p := p)
    (χ := (teichmullerCharQp p) ^ (j.1 : ℕ))
    ((teichmullerCharQp_pow_odd_iff (p := p) (oddCharacterIndex_ne_two (p := p) j)
      (j.1 : ℕ)).2 j.2)]
  rw [qpadicBernoulliSum_eq_eval_oddBernoulliKernelPoly (p := p) j.1]

theorem oddBernoulliFactor_eq_commonKernelEvaluations (j : OddCharacterIndex p) :
    ((-(1 / 2 : ℂ)) * BernoulliGen (((complexCharacterGenerator p) ^ (j.1 : ℕ))⁻¹) 1 =
        ((p : ℂ)⁻¹ * (-(1 / 2 : ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
            (oddBernoulliKernelPoly (p := p) j.1))
      ∧
    ((-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1 =
        ((p : ℚ_[p])⁻¹ * (-(1 / 2 : ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
            (oddBernoulliKernelPoly (p := p) j.1)) :=
  ⟨complexOddBernoulliFactor_eq_eval_oddBernoulliKernelPoly (p := p) j,
    qpadicOddBernoulliFactor_eq_eval_oddBernoulliKernelPoly (p := p) j⟩

theorem oddBernoulliProduct_eq_commonKernelEvaluations :
    ((Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
        (-(1 / 2 : ℂ)) * BernoulliGen (((complexCharacterGenerator p) ^ (j.1 : ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
        ((p : ℂ)⁻¹ * (-(1 / 2 : ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
            (oddBernoulliKernelPoly (p := p) j.1))
      ∧
    ((Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
        (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
        ((p : ℚ_[p])⁻¹ * (-(1 / 2 : ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
            (oddBernoulliKernelPoly (p := p) j.1)) := by
  constructor
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (oddBernoulliFactor_eq_commonKernelEvaluations (p := p) j).1
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (oddBernoulliFactor_eq_commonKernelEvaluations (p := p) j).2

/-- The single rational polynomial whose evaluations at the chosen complex and
`ℚ_[p]` generator roots recover the full odd Bernoulli product. -/
noncomputable def oddBernoulliProductPoly : Polynomial ℚ :=
  Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
    Polynomial.C (((p : ℚ)⁻¹) * (-(1 / 2 : ℚ))) *
      oddBernoulliKernelPoly (p := p) j.1

theorem eval_oddBernoulliProductPoly
    {R : Type*} [Field R] [CharZero R] [Algebra ℚ R] (x : R) :
    Polynomial.eval₂ (algebraMap ℚ R) x (oddBernoulliProductPoly (p := p)) =
      Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
        ((p : R)⁻¹ * (-(1 / 2 : R))) *
          Polynomial.eval₂ (algebraMap ℚ R) x (oddBernoulliKernelPoly (p := p) j.1) := by
  change (Polynomial.eval₂RingHom (algebraMap ℚ R) x) (oddBernoulliProductPoly (p := p)) = _
  rw [oddBernoulliProductPoly, map_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  change Polynomial.eval₂ (algebraMap ℚ R) x
      (Polynomial.C (((p : ℚ)⁻¹) * (-(1 / 2 : ℚ))) *
        oddBernoulliKernelPoly (p := p) j.1) = _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C]
  congr 1
  simp

theorem complexOddBernoulliProduct_eq_eval_oddBernoulliProductPoly :
    Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) (fun j =>
      (-(1 / 2 : ℂ)) * BernoulliGen (((complexCharacterGenerator p) ^ (j.1 : ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
          (oddBernoulliProductPoly (p := p)) := by
  rw [(oddBernoulliProduct_eq_commonKernelEvaluations (p := p)).1,
    eval_oddBernoulliProductPoly (p := p) (R := ℂ) (x := complexGeneratorRoot p)]

theorem qpadicOddBernoulliProduct_eq_eval_oddBernoulliProductPoly :
    Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) (fun j =>
      (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
          (oddBernoulliProductPoly (p := p)) := by
  rw [(oddBernoulliProduct_eq_commonKernelEvaluations (p := p)).2,
    eval_oddBernoulliProductPoly (p := p) (R := ℚ_[p]) (x := qpadicGeneratorRoot p)]

theorem teichmullerCharQp_pow_ne_one_of_mem_oddTeichmullerExponents
    {j : ℕ} (hj : j ∈ oddTeichmullerExponents (p := p)) :
    (teichmullerCharQp p) ^ j ≠ 1 := by
  have hj_lt : j < p - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hj_odd : Odd j := (Finset.mem_filter.mp hj).2
  have hj_ne_zero : j ≠ 0 := by
    rcases hj_odd with ⟨k, hk⟩
    omega
  intro hpow
  have hzero :
      (teichmullerCharQp p) ^ j = (teichmullerCharQp p) ^ 0 := by
    simpa using hpow
  have hj_zero :
      j = 0 := (teichmullerCharQp_pow_eq_iff_of_lt (p := p) hj_lt
        (prime_sub_one_pos (p := p))).mp hzero
  exact hj_ne_zero hj_zero

end Teichmuller

section FinalTeichmuller

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- The complex `hMinus` formula rewritten over the shared abstract odd-exponent
index type from `T023g1a1`. -/
theorem hMinus_formula_oddCharacterIndex (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℂ) =
      (2 * p : ℂ) *
        Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
          (-(1 / 2 : ℂ)) * BernoulliGen (((complexCharacterGenerator p) ^ (j.1 : ℕ))⁻¹) 1 := by
  rw [hMinus_formula (p := p) (K := K) hp_odd']
  rw [prod_oddCharacters_eq_prod_oddCharacterIndex (p := p) hp_odd'
    (fun χ => (-(1 / 2 : ℂ)) * BernoulliGen (χ⁻¹) 1)]

/-- The `ℚ_[p]` analogue of `hMinus_formula_oddCharacterIndex`, obtained by
transporting the common rational polynomial identity across the shared
cyclotomic minimal polynomial. -/
theorem hMinus_formula_oddCharacterIndex_qpadic (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℚ_[p]) =
      (2 * p : ℚ_[p]) *
        Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) fun j =>
          (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1 := by
  let Q : Polynomial ℚ :=
    Polynomial.C (2 * p : ℚ) * oddBernoulliProductPoly (p := p) -
      Polynomial.C ((hMinus K : ℕ) : ℚ)
  have hcomplex :
      ((hMinus K : ℕ) : ℂ) =
        (2 * p : ℂ) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (complexGeneratorRoot p)
            (oddBernoulliProductPoly (p := p)) := by
    rw [hMinus_formula_oddCharacterIndex (p := p) (K := K) hp_odd',
      complexOddBernoulliProduct_eq_eval_oddBernoulliProductPoly (p := p)]
  have hQ_complex : Polynomial.aeval (complexGeneratorRoot p) Q = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    simpa only [eq_ratCast, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, map_natCast,
      Polynomial.eval₂_natCast] using sub_eq_zero.mpr hcomplex.symm
  have hdvd : Polynomial.cyclotomic (p - 1) ℚ ∣ Q := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat
      (complexGeneratorRoot_isPrimitiveRoot (p := p)) (prime_sub_one_pos (p := p))]
    exact minpoly.dvd ℚ (complexGeneratorRoot p) hQ_complex
  have hcycl_qpadic :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
        (Polynomial.cyclotomic (p - 1) ℚ) = 0 := by
    simpa [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic, Polynomial.IsRoot.def] using
      (qpadicGeneratorRoot_isPrimitiveRoot (p := p)).isRoot_cyclotomic
      (prime_sub_one_pos (p := p))
  have hQ_qpadic :
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p) Q = 0 :=
    Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (f := algebraMap ℚ ℚ_[p]) (x := qpadicGeneratorRoot p) hdvd hcycl_qpadic
  have hq :
      (2 * p : ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
            (oddBernoulliProductPoly (p := p)) -
        ((hMinus K : ℕ) : ℚ_[p]) = 0 := by
    simpa [Q, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C] using hQ_qpadic
  calc
    ((hMinus K : ℕ) : ℚ_[p]) =
        (2 * p : ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qpadicGeneratorRoot p)
            (oddBernoulliProductPoly (p := p)) :=
          (sub_eq_zero.mp hq).symm
    _ = (2 * p : ℚ_[p]) *
        Finset.prod (Finset.univ : Finset (OddCharacterIndex p)) (fun j =>
          (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ (j.1 : ℕ))⁻¹) 1) := by
          rw [← qpadicOddBernoulliProduct_eq_eval_oddBernoulliProductPoly (p := p)]

/-- The `ℚ_[p]` odd-character product form of `hMinus_formula`, with the odd
side written over the concrete character finset `oddCharactersQp`. -/
theorem hMinus_formula_oddCharactersQp (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℚ_[p]) =
      (2 * p : ℚ_[p]) *
        Finset.prod (oddCharactersQp (p := p)) fun χ =>
          (-(1 / 2 : ℚ_[p])) * BernoulliGen χ⁻¹ 1 := by
  rw [hMinus_formula_oddCharacterIndex_qpadic (p := p) (K := K) hp_odd']
  rw [← prod_oddCharactersQp_eq_prod_oddCharacterIndex (p := p) hp_odd'
    (fun χ => (-(1 / 2 : ℚ_[p])) * BernoulliGen χ⁻¹ 1)]

/-- The `ℚ_[p]` odd-character product form reindexed by odd Teichmüller
exponents, still with inverse characters in the Bernoulli factors. -/
theorem hMinus_formula_oddTeichmullerExponents (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℚ_[p]) =
      (2 * p : ℚ_[p]) *
        Finset.prod (oddTeichmullerExponents (p := p)) fun j =>
          (-(1 / 2 : ℚ_[p])) * BernoulliGen (((teichmullerCharQp p) ^ j)⁻¹) 1 := by
  classical
  rw [hMinus_formula_oddCharactersQp (p := p) (K := K) hp_odd']
  rw [oddCharactersQp_eq_image_oddTeichmullerPowers (p := p) hp_odd']
  unfold oddTeichmullerCharactersQp
  rw [Finset.prod_image]
  · intro a ha b hb hab
    exact (teichmullerCharQp_pow_eq_iff_of_lt (p := p)
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)).mp hab

/-- Diekmann Theorem 43 specialized to the prime-conductor case
`K = ℚ(ζ_p)` as written on page 50, equation (32): the odd characters are the
odd powers of the Teichmueller character. This is the form used in the proof
of Theorem 42. -/
theorem hMinus_formula_teichmuller (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℚ_[p]) =
      (2 * p : ℚ_[p]) *
        Finset.prod ((Finset.range (p - 1)).filter fun j => Odd j) fun j =>
          (-(1 / 2 : ℚ_[p])) * BernoulliGen ((teichmullerCharQp p) ^ j) 1 := by
  rw [hMinus_formula_oddTeichmullerExponents (p := p) (K := K) hp_odd']
  have hp_even : Even (p - 1) := hp.out.even_sub_one hp_odd'
  have hmem_complement :
      ∀ {j : ℕ}, j ∈ (Finset.range (p - 1)).filter (fun j => Odd j) →
        (p - 1) - j ∈ (Finset.range (p - 1)).filter (fun j => Odd j) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have hj_pos : 0 < j := by
      rcases hj.2 with ⟨k, hk⟩
      omega
    have hcomp_odd : Odd ((p - 1) - j) :=
      Nat.Even.sub_odd (Nat.le_of_lt hj.1) hp_even hj.2
    exact ⟨Nat.sub_lt (prime_sub_one_pos (p := p)) hj_pos, hcomp_odd⟩
  congr 1
  unfold oddTeichmullerExponents
  refine Finset.prod_bij (fun j _ => (p - 1) - j) ?_ ?_ ?_ ?_
  · intro j hj
    exact hmem_complement hj
  · intro a ha b hb hab
    rw [Finset.mem_filter, Finset.mem_range] at ha hb
    simpa [Nat.sub_sub_self (Nat.le_of_lt ha.1), Nat.sub_sub_self (Nat.le_of_lt hb.1)] using
      congrArg (fun t => (p - 1) - t) hab
  · intro j hj
    have hj_mem : j ∈ (Finset.range (p - 1)).filter (fun j => Odd j) := hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨(p - 1) - j, hmem_complement hj_mem, ?_⟩
    · exact Nat.sub_sub_self (Nat.le_of_lt hj.1)
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    let j' : Fin (p - 1) := ⟨j, hj.1⟩
    simpa [j', complementExponent] using
      congrArg (fun χ : DirichletCharacter ℚ_[p] p =>
        (-(1 / 2 : ℚ_[p])) * BernoulliGen χ 1)
        (teichmullerCharQp_pow_inv_eq_pow_complement (p := p) j')

end FinalTeichmuller

end BernoulliRegular
