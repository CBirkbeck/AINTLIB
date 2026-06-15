module

public import BernoulliRegular.ImaginaryQuadratic.CN05.OddPrimes

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

section CN05_statement

variable (p : ℕ) [hp : Fact p.Prime]

/-- For `p ≡ 3 (mod 4)` and p odd prime, p ≡ 3 or 7 (mod 8). -/
lemma p_mod_eight_cases (hp3 : p % 4 = 3) (hp_odd : p ≠ 2) : p % 8 = 3 ∨ p % 8 = 7 := by
  have h1 : p % 8 < 8 := Nat.mod_lt _ (by decide)
  have h2 : p % 8 % 4 = p % 4 := Nat.mod_mod_of_dvd _ (by decide)
  rw [hp3] at h2
  have h3 : p % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hp.out with h | h
    · exact absurd h hp_odd
    · exact h
  have h4 : p % 8 % 2 = p % 2 := Nat.mod_mod_of_dvd _ (by decide)
  rw [h3] at h4
  omega

omit hp in
/-- For `p ≡ 7 (mod 8)`, `(p+1)/4` is even, i.e., `((p+1)/4 : ZMod 2) = 0`. -/
lemma pSuccDivFour_zero_mod_two_of_seven (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    (((p + 1) / 4 : ℕ) : ZMod 2) = 0 := by
  have h_div : (p + 1) / 4 = 2 * ((p + 1) / 8) := by omega
  rw [h_div]
  push_cast
  have : (2 : ZMod 2) = 0 := by decide
  rw [this]; ring

omit hp in
/-- For `p ≡ 3 (mod 8)`, `(p+1)/4` is odd, i.e., `((p+1)/4 : ZMod 2) = 1`. -/
lemma pSuccDivFour_one_mod_two_of_three (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    (((p + 1) / 4 : ℕ) : ZMod 2) = 1 := by
  have h_div : (p + 1) / 4 = 2 * (p / 8) + 1 := by omega
  rw [h_div]
  push_cast
  have : (2 : ZMod 2) = 0 := by decide
  rw [this]; ring

/-- In `ZMod 2`, `-1 = 1`. -/
private lemma neg_one_eq_one_mod_two : (-1 : ZMod 2) = 1 := by decide

/-- In `(ZMod 2)[X]`, `-X = X`. -/
private lemma neg_X_eq_X_mod_two : (-Polynomial.X : Polynomial (ZMod 2)) = Polynomial.X := by
  rw [show (-Polynomial.X : Polynomial (ZMod 2)) = (-1 : ZMod 2) • Polynomial.X from by
    rw [neg_smul, one_smul]]
  rw [neg_one_eq_one_mod_two, one_smul]

/-- For `p ≡ 7 (mod 8)` prime, minpoly α mod 2 factors as `X · (X + 1)`. -/
theorem alphaInOK_minpoly_factor_mod_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    Polynomial.map (Int.castRingHom (ZMod 2)) (minpoly ℤ (alphaInOK p hp3)) =
      Polynomial.X * (Polynomial.X + Polynomial.C (1 : ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [alphaInOK_minpoly_int_mod_q p hp3 2, pSuccDivFour_zero_mod_two_of_seven p hp3 hp7]
  rw [Polynomial.C_0, add_zero]
  calc (Polynomial.X ^ 2 - Polynomial.X : Polynomial (ZMod 2))
      = Polynomial.X ^ 2 + Polynomial.X := by rw [sub_eq_add_neg, neg_X_eq_X_mod_two]
    _ = Polynomial.X * (Polynomial.X + Polynomial.C 1) := by
        rw [Polynomial.C_1]; ring

/-- For `p ≡ 3 (mod 8)` prime, minpoly α mod 2 equals `X² + X + 1`. -/
theorem alphaInOK_minpoly_factor_mod_two_inert (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    Polynomial.map (Int.castRingHom (ZMod 2)) (minpoly ℤ (alphaInOK p hp3)) =
      Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [alphaInOK_minpoly_int_mod_q p hp3 2, pSuccDivFour_one_mod_two_of_three p hp3 hp3_8]
  rw [sub_eq_add_neg, neg_X_eq_X_mod_two]

/-- For `p ≡ 7 (mod 8)`, `monicFactorsMod α 2 = {X, X + 1}`. -/
theorem monicFactorsMod_alpha_at_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2 =
      {Polynomial.X, Polynomial.X + Polynomial.C (1 : ZMod 2)} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold RingOfIntegers.monicFactorsMod
  rw [alphaInOK_minpoly_factor_mod_two_split p hp3 hp7]
  have hX_ne_zero : (Polynomial.X : Polynomial (ZMod 2)) ≠ 0 := Polynomial.X_ne_zero
  have hXp1_ne_zero : (Polynomial.X + Polynomial.C (1 : ZMod 2) : Polynomial (ZMod 2)) ≠ 0 := by
    rw [show (Polynomial.X + Polynomial.C (1 : ZMod 2) : Polynomial (ZMod 2)) =
        Polynomial.X - Polynomial.C (-1 : ZMod 2) by rw [Polynomial.C_neg]; ring]
    exact (Polynomial.monic_X_sub_C _).ne_zero
  have hX_irred : Irreducible (Polynomial.X : Polynomial (ZMod 2)) := by
    rw [show (Polynomial.X : Polynomial (ZMod 2)) = Polynomial.X - Polynomial.C 0 by
      rw [Polynomial.C_0, sub_zero]]
    exact Polynomial.irreducible_X_sub_C _
  have hXp1_irred : Irreducible (Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)) := by
    rw [show (Polynomial.X + Polynomial.C (1 : ZMod 2) : Polynomial (ZMod 2)) =
        Polynomial.X - Polynomial.C (-1 : ZMod 2) by rw [Polynomial.C_neg]; ring]
    exact Polynomial.irreducible_X_sub_C _
  have hX_monic : (Polynomial.X : Polynomial (ZMod 2)).Monic := Polynomial.monic_X
  have hXp1_monic : (Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)).Monic := by
    rw [show (Polynomial.X + Polynomial.C (1 : ZMod 2) : Polynomial (ZMod 2)) =
        Polynomial.X - Polynomial.C (-1 : ZMod 2) by rw [Polynomial.C_neg]; ring]
    exact Polynomial.monic_X_sub_C _
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hX_ne_zero hXp1_ne_zero]
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hX_irred,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hXp1_irred,
    hX_monic.normalize_eq_self, hXp1_monic.normalize_eq_self]
  ext x
  simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.toFinset_singleton,
    Finset.mem_singleton, Finset.mem_insert]

/-- For `p ≡ 7 (mod 8)`, `monicFactorsMod α 2` has 2 elements. -/
theorem monicFactorsMod_alpha_at_two_split_card (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2).card = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [monicFactorsMod_alpha_at_two_split p hp3 hp7]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro h
  -- X = X + C 1 means C 1 = 0, but 1 ≠ 0 in ZMod 2.
  have h_sub : Polynomial.C (1 : ZMod 2) = (0 : Polynomial (ZMod 2)) := by
    linear_combination -h
  rw [Polynomial.C_1] at h_sub
  exact one_ne_zero h_sub

/-- For `p ≡ 3 (mod 8)`, `X² + X + 1` is irreducible in `(ZMod 2)[X]`. -/
lemma irreducible_X_sq_add_X_add_one_mod_two :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)) := by
  have h_deg : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)).natDegree = 2 := by
    have h_eq : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
        Polynomial (ZMod 2)) = Polynomial.X ^ 2 + (Polynomial.X + Polynomial.C (1 : ZMod 2)) := by
      ring
    rw [h_eq]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 2
    · rw [Polynomial.natDegree_X_pow]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
      decide
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [h_deg]; decide
  · intro a ha
    rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at ha
    fin_cases a
    · revert ha; decide
    · revert ha; decide

/-- For `p ≡ 3 (mod 8)`, `monicFactorsMod α 2 = {X² + X + 1}` (singleton). -/
theorem monicFactorsMod_alpha_at_two_inert (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2 =
      {Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2)} := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_irred := irreducible_X_sq_add_X_add_one_mod_two
  have h_monic : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)).Monic := by
    have h_eq : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
        Polynomial (ZMod 2)) = Polynomial.X ^ 2 + (Polynomial.X + Polynomial.C (1 : ZMod 2)) := by
      ring
    rw [h_eq]
    refine Polynomial.monic_X_pow_add ?_
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    refine lt_of_le_of_lt ?_ (by decide : (1 : WithBot ℕ) < 2)
    refine max_le ?_ ?_
    · rw [Polynomial.degree_X]
    · exact (Polynomial.degree_C_le).trans (by decide)
  unfold RingOfIntegers.monicFactorsMod
  rw [alphaInOK_minpoly_factor_mod_two_inert p hp3 hp3_8]
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred,
    h_monic.normalize_eq_self]
  simp

/-- For `p ≡ 3 (mod 8)`, `monicFactorsMod α 2` has 1 element. -/
theorem monicFactorsMod_alpha_at_two_inert_card (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2).card = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [monicFactorsMod_alpha_at_two_inert p hp3 hp3_8]
  simp

/-- Number of primes above 2 in `𝒪 (Kminus p)` is 2 (split, p ≡ 7 mod 8). -/
theorem ncard_primesOver_at_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    (Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))).ncard = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_exp : ¬ (2 : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 2
  have h_equiv :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  rw [← Nat.card_coe_set_eq, Nat.card_congr h_equiv, Nat.card_eq_finsetCard,
    monicFactorsMod_alpha_at_two_split_card p hp3 hp7]

/-- Number of primes above 2 in `𝒪 (Kminus p)` is 1 (inert, p ≡ 3 mod 8). -/
theorem ncard_primesOver_at_two_inert (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    (Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))).ncard = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_exp : ¬ (2 : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 2
  have h_equiv :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  rw [← Nat.card_coe_set_eq, Nat.card_congr h_equiv, Nat.card_eq_finsetCard,
    monicFactorsMod_alpha_at_two_inert_card p hp3 hp3_8]

/-- Each prime above 2 in the split case has inertiaDeg = 1. -/
theorem inertiaDeg_at_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7)
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) :
    (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_exp : ¬ (2 : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 2
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  set P_sub : ↥(Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) := ⟨P, hP⟩
  set Qfactor := (e P_sub : Polynomial (ZMod 2))
  have hQ_mem : Qfactor ∈ RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2 :=
    (e P_sub).prop
  have hP_from : P = (e.symm ⟨Qfactor, hQ_mem⟩ : Ideal (𝓞 (Kminus p))) := by
    have : e.symm ⟨Qfactor, hQ_mem⟩ = P_sub := by
      change e.symm (e P_sub) = P_sub
      exact e.symm_apply_apply P_sub
    change (P_sub : Ideal (𝓞 (Kminus p))) = _
    rw [this]
  rw [hP_from]
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      h_exp hQ_mem]
  -- Qfactor is X or X + 1, both natDegree 1.
  rw [monicFactorsMod_alpha_at_two_split p hp3 hp7] at hQ_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hQ_mem
  rcases hQ_mem with hQ | hQ
  · rw [hQ]
    exact Polynomial.natDegree_X
  · rw [hQ]
    rw [show (Polynomial.X + Polynomial.C (1 : ZMod 2) : Polynomial (ZMod 2)) =
        Polynomial.X - Polynomial.C (-1 : ZMod 2) by rw [Polynomial.C_neg]; ring]
    exact Polynomial.natDegree_X_sub_C _

/-- Each prime above 2 in the split case has absNorm = 2. -/
theorem absNorm_primeOver_at_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7)
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) :
    Ideal.absNorm P = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  have h_ine : (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P = 1 :=
    inertiaDeg_at_two_split p hp3 hp7 P hP
  calc Ideal.absNorm P
      = 2 ^ ((Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P) :=
        Ideal.absNorm_eq_pow_inertiaDeg' P Nat.prime_two
    _ = 2 ^ (1 : ℕ) := by rw [h_ine]
    _ = 2 := pow_one 2

/-- The unique prime above 2 in the inert case has inertiaDeg = 2. -/
theorem inertiaDeg_at_two_inert (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3)
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) :
    (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_exp : ¬ (2 : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 2
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  set Qfactor : Polynomial (ZMod 2) :=
    Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2)
  have hQ_mem : Qfactor ∈ RingOfIntegers.monicFactorsMod (alphaInOK p hp3) 2 := by
    rw [monicFactorsMod_alpha_at_two_inert p hp3 hp3_8]
    exact Finset.mem_singleton.mpr rfl
  have hP_eq : P = (e.symm ⟨Qfactor, hQ_mem⟩ : Ideal (𝓞 (Kminus p))) := by
    have h_sub : Subsingleton ↥(Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) := by
      have h_card := ncard_primesOver_at_two_inert p hp3 hp3_8
      rw [Set.ncard_eq_one] at h_card
      obtain ⟨x, hx⟩ := h_card
      refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
      have ha_eq : a = x := by rw [hx] at ha; exact ha
      have hb_eq : b = x := by rw [hx] at hb; exact hb
      subst ha_eq; subst hb_eq; rfl
    have hP_set : (⟨P, hP⟩ : ↥(Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)))) =
                  e.symm ⟨Qfactor, hQ_mem⟩ := h_sub.elim _ _
    exact congrArg (fun (x : ↥(Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)))) =>
      (x : Ideal (𝓞 (Kminus p)))) hP_set
  rw [hP_eq]
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      h_exp hQ_mem]
  change (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)).natDegree = 2
  have h_eq : (Polynomial.X ^ 2 + Polynomial.X + Polynomial.C (1 : ZMod 2) :
      Polynomial (ZMod 2)) =
      Polynomial.X ^ 2 + (Polynomial.X + Polynomial.C (1 : ZMod 2)) := by
    ring
  rw [h_eq]
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
  · exact Polynomial.natDegree_X_pow 2
  · rw [Polynomial.natDegree_X_pow]
    refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
    rw [Polynomial.natDegree_X, Polynomial.natDegree_C]
    decide

/-- The unique prime above 2 in the inert case has absNorm = 4. -/
theorem absNorm_primeOver_at_two_inert (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3)
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p))) :
    Ideal.absNorm P = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  have h_ine : (Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P = 2 :=
    inertiaDeg_at_two_inert p hp3 hp3_8 P hP
  calc Ideal.absNorm P
      = 2 ^ ((Ideal.span {((2 : ℕ) : ℤ)}).inertiaDeg P) :=
        Ideal.absNorm_eq_pow_inertiaDeg' P Nat.prime_two
    _ = 2 ^ (2 : ℕ) := by rw [h_ine]
    _ = 4 := by norm_num

/-- Decomposition of I with absNorm I = 2^k in the split case at q = 2. -/
lemma ideal_decomp_at_two_split (hp3 : p % 4 = 3) (hp7 : p % 8 = 7)
    {P₁ P₂ : Ideal (𝓞 (Kminus p))}
    (hP₁_mem : P₁ ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)))
    (hP₂_mem : P₂ ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)))
    (hP_eq : Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) = {P₁, P₂})
    {k : ℕ} {I : Ideal (𝓞 (Kminus p))} (hI_ne : I ≠ ⊥)
    (hI_norm : Ideal.absNorm I = 2 ^ k) :
    ∃ a ≤ k, I = P₁ ^ a * P₂ ^ (k - a) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqp : (2 : ℕ) ≠ p := by
    intro h_eq
    have : p % 4 = 2 % 4 := by rw [← h_eq]
    rw [hp3] at this; norm_num at this
  have hP₁_ne : P₁ ≠ ⊥ := primeOver_ne_bot p 2 P₁ hP₁_mem
  have hP₂_ne : P₂ ≠ ⊥ := primeOver_ne_bot p 2 P₂ hP₂_mem
  haveI : P₁.IsPrime := hP₁_mem.1
  haveI : P₂.IsPrime := hP₂_mem.1
  haveI : P₁.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₁_ne hP₁_mem.1
  haveI : P₂.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₂_ne hP₂_mem.1
  have habsNormP₁ : Ideal.absNorm P₁ = 2 := absNorm_primeOver_at_two_split p hp3 hp7 P₁ hP₁_mem
  have habsNormP₂ : Ideal.absNorm P₂ = 2 := absNorm_primeOver_at_two_split p hp3 hp7 P₂ hP₂_mem
  have hq_gt_one : (1 : ℕ) < 2 := by decide
  obtain ⟨Q₁, hP₁Q₁, hIeq₁⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P₁
  set a : ℕ := Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors I)
  have hQ₁_ne : Q₁ ≠ ⊥ := fun h => hI_ne (by rw [hIeq₁, h, Ideal.mul_bot])
  obtain ⟨Q₂, hP₂Q₂, hQ₁eq⟩ := Ideal.eq_prime_pow_mul_coprime hQ₁_ne P₂
  set b : ℕ := Multiset.count P₂ (UniqueFactorizationMonoid.normalizedFactors Q₁)
  have hQ₂_ne : Q₂ ≠ ⊥ := fun h => hQ₁_ne (by rw [hQ₁eq, h, Ideal.mul_bot])
  have hI_decomp : I = P₁ ^ a * P₂ ^ b * Q₂ := by rw [hIeq₁, hQ₁eq]; ring
  have hP₁Q₂ : P₁ ⊔ Q₂ = ⊤ := by
    refine top_le_iff.mp ?_
    calc ⊤ = P₁ ⊔ Q₁ := hP₁Q₁.symm
      _ = P₁ ⊔ (P₂ ^ b * Q₂) := by rw [hQ₁eq]
      _ ≤ P₁ ⊔ Q₂ := sup_le_sup_left Ideal.mul_le_left _
  have hQ₂_top : Q₂ = ⊤ := by
    by_contra hQ₂_ne_top
    have hQ₂_nf_ne : UniqueFactorizationMonoid.normalizedFactors Q₂ ≠ 0 := by
      intro hnf
      apply hQ₂_ne_top
      rw [← Ideal.prod_normalizedFactors_eq_self hQ₂_ne, hnf]; simp
    obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hQ₂_nf_ne
    have hRfac := (Ideal.mem_normalizedFactors_iff hQ₂_ne).1 hRmem
    have hRprime : R.IsPrime := hRfac.1
    have hQ₂_le_R : Q₂ ≤ R := hRfac.2
    have hR_ne : R ≠ ⊥ := fun h => hQ₂_ne (le_bot_iff.mp (hQ₂_le_R.trans_eq h))
    haveI : NeZero R := ⟨hR_ne⟩
    have hQ₂_dvd_I : Ideal.absNorm Q₂ ∣ Ideal.absNorm I := by
      rw [hI_decomp, map_mul]; exact dvd_mul_left _ _
    have hR_dvd_2k : Ideal.absNorm R ∣ 2 ^ k := by
      rw [← hI_norm]
      exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ₂_le_R) hQ₂_dvd_I
    have hR_in : R ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) :=
      prime_factor_of_q_pow_is_above_q p hp3 2 hqp R hR_ne hR_dvd_2k
    rw [hP_eq] at hR_in
    rcases Set.mem_insert_iff.mp hR_in with hR | hR
    · have hQ₂_le_P₁ : Q₂ ≤ P₁ := hR ▸ hQ₂_le_R
      have : P₁ ⊔ Q₂ = P₁ := sup_of_le_left hQ₂_le_P₁
      rw [this] at hP₁Q₂
      exact (inferInstance : P₁.IsMaximal).ne_top hP₁Q₂
    · rw [Set.mem_singleton_iff] at hR
      have hQ₂_le_P₂ : Q₂ ≤ P₂ := hR ▸ hQ₂_le_R
      have : P₂ ⊔ Q₂ = P₂ := sup_of_le_left hQ₂_le_P₂
      rw [this] at hP₂Q₂
      exact (inferInstance : P₂.IsMaximal).ne_top hP₂Q₂
  have hI_prod : I = P₁ ^ a * P₂ ^ b := by rw [hI_decomp, hQ₂_top]; exact Ideal.mul_top _
  have hab_eq : a + b = k := by
    have h : (2 : ℕ) ^ (a + b) = 2 ^ k := by
      rw [← hI_norm, hI_prod, map_mul, map_pow, map_pow, habsNormP₁, habsNormP₂, ← pow_add]
    exact Nat.pow_right_injective hq_gt_one h
  refine ⟨a, by omega, ?_⟩
  rw [hI_prod]
  congr 2
  omega

/-- **Split case counting for q = 2**: the number of ideals of norm 2^k is k+1. -/
theorem idealNormMultiplicity_at_two_split_eq (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) (k : ℕ) :
    idealNormMultiplicity (Kminus p) (2 ^ k) = k + 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_set_card := ncard_primesOver_at_two_split p hp3 hp7
  rw [Set.ncard_eq_two] at h_set_card
  obtain ⟨P₁, P₂, hP₁₂_ne, hP_eq⟩ := h_set_card
  have hP₁_mem : P₁ ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq]; exact Set.mem_insert _ _
  have hP₂_mem : P₂ ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq]; exact Set.mem_insert_of_mem _ rfl
  have hP₁_ne : P₁ ≠ ⊥ := primeOver_ne_bot p 2 P₁ hP₁_mem
  have hP₂_ne : P₂ ≠ ⊥ := primeOver_ne_bot p 2 P₂ hP₂_mem
  haveI : P₁.IsPrime := hP₁_mem.1
  haveI : P₂.IsPrime := hP₂_mem.1
  haveI : P₁.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₁_ne hP₁_mem.1
  haveI : P₂.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₂_ne hP₂_mem.1
  have habsNormP₁ : Ideal.absNorm P₁ = 2 := absNorm_primeOver_at_two_split p hp3 hp7 P₁ hP₁_mem
  have habsNormP₂ : Ideal.absNorm P₂ = 2 := absNorm_primeOver_at_two_split p hp3 hp7 P₂ hP₂_mem
  have hq_gt_one : (1 : ℕ) < 2 := by decide
  unfold idealNormMultiplicity
  have h_ideal_ne : ∀ a : ℕ, P₁ ^ a * P₂ ^ (k - a) ≠ ⊥ :=
    fun a => mul_ne_zero (pow_ne_zero _ hP₁_ne) (pow_ne_zero _ hP₂_ne)
  have h_ideal_norm : ∀ a ≤ k, Ideal.absNorm (P₁ ^ a * P₂ ^ (k - a)) = 2 ^ k := by
    intro a ha
    rw [map_mul, map_pow, map_pow, habsNormP₁, habsNormP₂, ← pow_add]
    congr 1; omega
  have h_uniqueness : ∀ (a₁ a₂ : ℕ), a₁ ≤ k → a₂ ≤ k →
      P₁ ^ a₁ * P₂ ^ (k - a₁) = P₁ ^ a₂ * P₂ ^ (k - a₂) → a₁ = a₂ := by
    intro a₁ a₂ ha₁ ha₂ h_eq
    have h_prime_P₁ : Prime P₁ := Ideal.prime_of_isPrime hP₁_ne inferInstance
    have h_prime_P₂ : Prime P₂ := Ideal.prime_of_isPrime hP₂_ne inferInstance
    have h_count : Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors
        (P₁ ^ a₁ * P₂ ^ (k - a₁))) =
        Multiset.count P₁ (UniqueFactorizationMonoid.normalizedFactors
        (P₁ ^ a₂ * P₂ ^ (k - a₂))) := by rw [h_eq]
    rw [UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hP₁_ne)
        (pow_ne_zero _ hP₂_ne),
      UniqueFactorizationMonoid.normalizedFactors_mul (pow_ne_zero _ hP₁_ne)
        (pow_ne_zero _ hP₂_ne),
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h_prime_P₁.irreducible,
      UniqueFactorizationMonoid.normalizedFactors_irreducible h_prime_P₂.irreducible,
      normalize_eq, normalize_eq] at h_count
    simp only [Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self,
      Multiset.count_singleton, if_neg hP₁₂_ne, mul_zero, mul_one, add_zero] at h_count
    exact h_count
  set S := {I : NonzeroIdeal (Kminus p) // Ideal.absNorm I.1 = 2 ^ k}
  let forward : S → Fin (k + 1) := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    ⟨(ideal_decomp_at_two_split p hp3 hp7 hP₁_mem hP₂_mem hP_eq hI_ne hI_norm).choose,
      Nat.lt_succ_of_le
        (ideal_decomp_at_two_split p hp3 hp7 hP₁_mem hP₂_mem hP_eq hI_ne hI_norm).choose_spec.1⟩
  let backward : Fin (k + 1) → S := fun ⟨a, ha⟩ =>
    ⟨⟨P₁ ^ a * P₂ ^ (k - a), h_ideal_ne a⟩, h_ideal_norm a (Nat.lt_succ_iff.mp ha)⟩
  have h_equiv : S ≃ Fin (k + 1) :=
    { toFun := forward
      invFun := backward
      left_inv := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ => by
        simp only [forward, backward]
        refine Subtype.ext (Subtype.ext ?_)
        simp only
        exact (ideal_decomp_at_two_split p hp3 hp7 hP₁_mem hP₂_mem hP_eq hI_ne
          hI_norm).choose_spec.2.symm
      right_inv := fun ⟨a, ha⟩ => by
        simp only [forward, backward]
        refine Fin.ext ?_
        simp only
        have ha_le : a ≤ k := Nat.lt_succ_iff.mp ha
        set decomp := ideal_decomp_at_two_split p hp3 hp7 hP₁_mem hP₂_mem hP_eq
          (h_ideal_ne a) (h_ideal_norm a ha_le)
        have ha'_le : decomp.choose ≤ k := decomp.choose_spec.1
        have h_eq : P₁ ^ decomp.choose * P₂ ^ (k - decomp.choose) = P₁ ^ a * P₂ ^ (k - a) :=
          decomp.choose_spec.2.symm
        exact h_uniqueness _ _ ha'_le ha_le h_eq }
  rw [Nat.card_congr h_equiv, Nat.card_fin]

/-- **Inert case, odd k at q=2**: count = 0. -/
theorem idealNormMultiplicity_at_two_inert_odd (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3)
    {k : ℕ} (hk_odd : Odd k) :
    idealNormMultiplicity (Kminus p) (2 ^ k) = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_ofNat]
    decide
  haveI : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have h_set_card := ncard_primesOver_at_two_inert p hp3 hp3_8
  rw [Set.ncard_eq_one] at h_set_card
  obtain ⟨P, hP_eq_set⟩ := h_set_card
  have hP_mem : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq_set]; rfl
  have hP_ne : P ≠ ⊥ := primeOver_ne_bot p 2 P hP_mem
  haveI : P.IsPrime := hP_mem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hP_mem.1
  haveI : P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)}) := hP_mem.2
  have habsNormP : Ideal.absNorm P = 4 := absNorm_primeOver_at_two_inert p hp3 hp3_8 P hP_mem
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P
  let m : ℕ := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
  have hQ_top : Q = ⊤ := by
    by_contra hQ_ne_top
    have hQ_ne : Q ≠ ⊥ := fun hQ_bot => hI_ne (by rw [hIeq, hQ_bot, Ideal.mul_bot])
    have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
      intro hnf
      apply hQ_ne_top
      rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]; simp
    obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
    have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
    have hRprime : R.IsPrime := hRfac.1
    have hQ_le_R : Q ≤ R := hRfac.2
    have hR_ne : R ≠ ⊥ := fun hR_bot => hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
    haveI : NeZero R := ⟨hR_ne⟩
    have hI_le_Q : I ≤ Q := by rw [hIeq]; exact Ideal.mul_le_left
    have hR_dvd_I : Ideal.absNorm R ∣ 2 ^ k := by
      rw [← hI_norm]
      exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
        (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
    have h2qp : (2 : ℕ) ≠ p := by
      intro h
      have : p % 4 = 2 % 4 := by rw [← h]
      rw [hp3] at this; norm_num at this
    have hR_in : R ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) :=
      prime_factor_of_q_pow_is_above_q p hp3 2 h2qp R hR_ne hR_dvd_I
    have hR_eq_P : R = P := by rw [hP_eq_set] at hR_in; exact hR_in
    have hQ_le_P : Q ≤ P := by simpa [hR_eq_P] using hQ_le_R
    have htop_le_P : (⊤ : Ideal (𝓞 (Kminus p))) ≤ P :=
      calc ⊤ = P ⊔ Q := hPQ.symm
        _ ≤ P := sup_le le_rfl hQ_le_P
    exact hP_mem.1.ne_top (top_le_iff.mp htop_le_P)
  have hI_pow : I = P ^ m := by simpa [m, hQ_top] using hIeq
  have hI_norm_val : Ideal.absNorm I = 2 ^ k := hI_norm
  have hI_norm_eq : 2 ^ (2 * m) = 2 ^ k := by
    have := hI_norm_val
    rw [hI_pow, map_pow, habsNormP] at this
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul] at this
    exact this
  have h_k_eq : 2 * m = k := Nat.pow_right_injective (by decide : 1 < 2) hI_norm_eq
  have : Even k := ⟨m, by omega⟩
  exact (Nat.not_even_iff_odd.mpr hk_odd) this

/-- **Inert case, even k at q=2**: count = 1. -/
theorem idealNormMultiplicity_at_two_inert_even (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) (m : ℕ) :
    idealNormMultiplicity (Kminus p) (2 ^ (2 * m)) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_ofNat]
    decide
  haveI : (Ideal.span {((2 : ℕ) : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have h_set_card := ncard_primesOver_at_two_inert p hp3 hp3_8
  rw [Set.ncard_eq_one] at h_set_card
  obtain ⟨P, hP_eq_set⟩ := h_set_card
  have hP_mem : P ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) := by
    rw [hP_eq_set]; rfl
  have hP_ne : P ≠ ⊥ := primeOver_ne_bot p 2 P hP_mem
  haveI : P.IsPrime := hP_mem.1
  haveI : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP_ne hP_mem.1
  haveI : P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)}) := hP_mem.2
  have habsNormP : Ideal.absNorm P = 4 := absNorm_primeOver_at_two_inert p hp3 hp3_8 P hP_mem
  unfold idealNormMultiplicity
  haveI : Unique {I : NonzeroIdeal (Kminus p) // Ideal.absNorm I.1 = 2 ^ (2 * m)} :=
    { default := ⟨⟨P ^ m, pow_ne_zero m hP_ne⟩, by
          rw [map_pow, habsNormP]
          rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne P
        let mI : ℕ := Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
        have hQ_top : Q = ⊤ := by
          by_contra hQ_ne_top
          have hQ_ne : Q ≠ ⊥ := fun hQ_bot => hI_ne (by rw [hIeq, hQ_bot, Ideal.mul_bot])
          have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]; simp
          obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime : R.IsPrime := hRfac.1
          have hQ_le_R : Q ≤ R := hRfac.2
          have hR_ne : R ≠ ⊥ :=
            fun hR_bot => hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          haveI : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by rw [hIeq]; exact Ideal.mul_le_left
          have hR_dvd_I : Ideal.absNorm R ∣ 2 ^ (2 * m) := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have h2qp : (2 : ℕ) ≠ p := by
            intro h
            have : p % 4 = 2 % 4 := by rw [← h]
            rw [hp3] at this; norm_num at this
          have hR_in : R ∈ Ideal.primesOver (Ideal.span {((2 : ℕ) : ℤ)}) (𝓞 (Kminus p)) :=
            prime_factor_of_q_pow_is_above_q p hp3 2 h2qp R hR_ne hR_dvd_I
          have hR_eq_P : R = P := by rw [hP_eq_set] at hR_in; exact hR_in
          have hQ_le_P : Q ≤ P := by simpa [hR_eq_P] using hQ_le_R
          have htop_le_P : (⊤ : Ideal (𝓞 (Kminus p))) ≤ P :=
            calc ⊤ = P ⊔ Q := hPQ.symm
              _ ≤ P := sup_le le_rfl hQ_le_P
          exact hP_mem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow : I = P ^ mI := by simpa [mI, hQ_top] using hIeq
        have hmI_eq : mI = m := by
          have hI_norm_val : Ideal.absNorm I = 2 ^ (2 * m) := hI_norm
          have : 2 ^ (2 * mI) = 2 ^ (2 * m) := by
            rw [hI_pow, map_pow, habsNormP] at hI_norm_val
            rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul] at hI_norm_val
            exact hI_norm_val
          have := Nat.pow_right_injective (by decide : 1 < 2) this
          omega
        refine Subtype.ext (Subtype.ext ?_)
        simpa [mI, hmI_eq] using hI_pow }
  exact Nat.card_unique

/-- For `p ≡ 7 (mod 8)`, `legendreDirichletNat p 2 = 1`. -/
lemma legendreDirichletNat_two_of_seven (hp3 : p % 4 = 3) (hp7 : p % 8 = 7) :
    legendreDirichletNat p 2 = 1 := by
  have hp_odd : p ≠ 2 := by omega
  have h_sq : IsSquare ((2 : ℕ) : ZMod p) := by
    have := ZMod.exists_sq_eq_two_iff hp_odd
    rw [show ((2 : ℕ) : ZMod p) = (2 : ZMod p) by push_cast; rfl]
    exact this.mpr (Or.inr hp7)
  exact (legendreDirichletNat_eq_one_iff_isSquare p 2 (fun h => by omega)).mpr h_sq

/-- For `p ≡ 3 (mod 8)`, `legendreDirichletNat p 2 = -1`. -/
lemma legendreDirichletNat_two_of_three (hp3 : p % 4 = 3) (hp3_8 : p % 8 = 3) :
    legendreDirichletNat p 2 = -1 := by
  have hp_odd : p ≠ 2 := by omega
  have h_not_sq : ¬ IsSquare ((2 : ℕ) : ZMod p) := by
    have := ZMod.exists_sq_eq_two_iff hp_odd
    rw [show ((2 : ℕ) : ZMod p) = (2 : ZMod p) by push_cast; rfl]
    intro h
    rcases this.mp h with h1 | h7
    · omega
    · omega
  exact (legendreDirichletNat_eq_neg_one_iff_not_isSquare p 2 (fun h => by omega)).mpr h_not_sq

/-- **CN-05 coefficient equality at q = 2**: LHS = RHS for p ≡ 3 mod 4 and q = 2. -/
theorem CN05CoeffEq_at_prime_pow_two (hp3 : p % 4 = 3) (k : ℕ) :
    ((idealNormMultiplicity (Kminus p) (2 ^ k)) : ℂ) =
      LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (2 ^ k) := by
  have hp_odd : p ≠ 2 := by omega
  rcases p_mod_eight_cases p hp3 hp_odd with hp3_8 | hp7
  · -- p ≡ 3 mod 8: 2 inert, η(2) = -1.
    have hη : legendreDirichletNat p 2 = -1 := legendreDirichletNat_two_of_three p hp3 hp3_8
    rw [convolution_one_legendreNat_at_prime_pow_inert p 2 Nat.prime_two k hη]
    rcases Nat.even_or_odd k with hk | hk
    · obtain ⟨m, hm⟩ := hk
      rw [hm, show m + m = 2 * m from by ring,
        idealNormMultiplicity_at_two_inert_even p hp3 hp3_8 m]
      rw [if_pos ⟨m, by ring⟩]; simp
    · rw [idealNormMultiplicity_at_two_inert_odd p hp3 hp3_8 hk]
      rw [if_neg (Nat.not_even_iff_odd.mpr hk)]; simp
  · -- p ≡ 7 mod 8: 2 splits, η(2) = 1.
    have hη : legendreDirichletNat p 2 = 1 := legendreDirichletNat_two_of_seven p hp3 hp7
    rw [convolution_one_legendreNat_at_prime_pow_split p 2 Nat.prime_two k hη]
    rw [idealNormMultiplicity_at_two_split_eq p hp3 hp7]

end CN05_statement

end BernoulliRegular
