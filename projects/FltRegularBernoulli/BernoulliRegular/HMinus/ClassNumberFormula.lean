module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import BernoulliRegular.TotallyRealSubfield
public import BernoulliRegular.ZetaFactorisation

/-!
# Analytic class number formula for `K` and `K⁺`

Rearrangements of mathlib's analytic class-number formula for the prime
cyclotomic field `K = ℚ(ζ_p)` and its maximal real subfield
`K⁺ = maximalRealSubfield K`, together with the cyclotomic specialization of
each invariant (torsion order, unit rank, regulator ratio, discriminant).

Outputs:

- `h_formula` — `h K` as residue times discriminant/regulator factor.
- `hPlus_formula` — the corresponding formula for `h⁺ K`.
- `hMinus_eq_h_div_hPlus` — the relative class number as `h / h⁺`.
- `hMinus_formula_via_residues` — `h⁻` expressed as a quotient of residue
  packages.
- `h_formula_cyclotomic` — the prime-conductor specialization of `h_formula`
  with explicit cyclotomic invariants.

See the sibling module `BernoulliRegular.HMinus.LValueReduction` for the
reduction of these residue expressions to character `L`-values.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace BernoulliRegular

section ClassNumberFormula

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- The class number formula for `K`, rearranged to solve for `h`. -/
theorem h_formula :
    (h K : ℝ) =
      NumberField.dedekindZeta_residue K *
        (((Units.torsionOrder K : ℝ) * Real.sqrt |discr K|) /
          (2 ^ InfinitePlace.nrRealPlaces K *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)) := by
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K
  let B : ℝ := (Units.torsionOrder K : ℝ) * Real.sqrt |discr K|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos K)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA : A ≠ 0 := hA_pos.ne'
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos K
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  have hB : B ≠ 0 := hB_pos.ne'
  calc
    (h K : ℝ) = ((A * (h K : ℝ)) / B) * (B / A) := by
      field_simp [hA, hB]
    _ = NumberField.dedekindZeta_residue K * (B / A) := by
          dsimp [A, B]
          rw [NumberField.dedekindZeta_residue_def, BernoulliRegular.h, NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue K *
          (((Units.torsionOrder K : ℝ) * Real.sqrt |discr K|) /
            (2 ^ InfinitePlace.nrRealPlaces K *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)) := by
          simp [A, B]

/-- The class number formula for the maximal real subfield `K⁺`, rearranged to
solve for `h⁺`. -/
theorem hPlus_formula :
    (hPlus K : ℝ) =
      NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) *
        (((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
            Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
          (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
              Units.regulator (NumberField.maximalRealSubfield K))) := by
  let L := NumberField.maximalRealSubfield K
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B : ℝ := (Units.torsionOrder L : ℝ) * Real.sqrt |discr L|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA : A ≠ 0 := hA_pos.ne'
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  have hB : B ≠ 0 := hB_pos.ne'
  calc
    (hPlus K : ℝ) = ((A * (hPlus K : ℝ)) / B) * (B / A) := by
      field_simp [hA, hB]
    _ = NumberField.dedekindZeta_residue L * (B / A) := by
          dsimp [A, B, L]
          rw [NumberField.dedekindZeta_residue_def, BernoulliRegular.hPlus, NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue L *
          (((Units.torsionOrder L : ℝ) * Real.sqrt |discr L|) /
            (2 ^ InfinitePlace.nrRealPlaces L *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L)) := by
          simp [A, B]

/-- The relative class number is the quotient `h / h⁺`, viewed in `ℝ`. -/
theorem hMinus_eq_h_div_hPlus (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℝ) = (h K : ℝ) / (hPlus K : ℝ) := by
  have hhPlus_pos : 0 < (hPlus K : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K))))
  have hmul : (h K : ℝ) = (hPlus K : ℝ) * ((hMinus K : ℕ) : ℝ) := by
    exact_mod_cast (h_eq_hPlus_mul_hMinus (p := p) (hp_odd := hp_odd') (K := K))
  apply (eq_div_iff hhPlus_pos.ne').2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm

/-- Rearranging the analytic class number formulas for `K` and `K⁺` gives a
relative residue expression for `h⁻`. This isolates the remaining analytic
input needed for Theorem 43 to the identification of the `K⁺`-side residue
with the even-character product. -/
theorem hMinus_formula_via_residues (hp_odd' : p ≠ 2) :
    ((hMinus K : ℕ) : ℝ) =
      (NumberField.dedekindZeta_residue K *
          (((Units.torsionOrder K : ℝ) * Real.sqrt |discr K|) /
            (2 ^ InfinitePlace.nrRealPlaces K *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K))) /
        (NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) *
          (((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
              Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
            (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
                Units.regulator (NumberField.maximalRealSubfield K)))) := by
  rw [hMinus_eq_h_div_hPlus (p := p) (K := K) hp_odd',
    h_formula (K := K),
    hPlus_formula (K := K)]

omit [IsCMField K] in
lemma nrComplexPlaces_maximalRealSubfield_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
      (K := NumberField.maximalRealSubfield K)

lemma nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two :
    NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) = (p - 1) / 2 := by
  let L := NumberField.maximalRealSubfield K
  calc
    NumberField.InfinitePlace.nrRealPlaces L = Module.finrank ℚ L := by
      rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 := by
      rw [finrank_Kplus_over_rat (p := p) (K := K)]

lemma maximalRealSubfield_archimedeanFactor_eq_pow :
    2 ^ NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 1) / 2 : ℕ) := by
  rw [nrComplexPlaces_maximalRealSubfield_eq_zero (K := K), pow_zero, mul_one,
    nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two (p := p) (K := K)]

set_option linter.unusedSectionVars false in
lemma maximalRealSubfield_torsion_eq_one_or_neg_one
    (x : NumberField.Units.torsion (NumberField.maximalRealSubfield K)) :
    (x : (𝓞 (NumberField.maximalRealSubfield K))ˣ) = 1 ∨
      (x : (𝓞 (NumberField.maximalRealSubfield K))ˣ) = -1 := by
  let L := NumberField.maximalRealSubfield K
  let φ : L →+* ℂ := Classical.choice inferInstance
  let hφ : ComplexEmbedding.IsReal φ :=
    NumberField.IsTotallyReal.complexEmbedding_isReal φ
  let u : (𝓞 L)ˣ := x
  let r : ℝ := hφ.embedding (u : L)
  have hur : ((r : ℂ)) = φ (u : L) :=
    hφ.coe_embedding_apply (u : L)
  have hu_fin : IsOfFinOrder u := (CommGroup.mem_torsion u).1 x.prop
  obtain ⟨n, hn, hu_pow⟩ := isOfFinOrder_iff_pow_eq_one.mp hu_fin
  have hnorm : ‖φ (u : L)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one
    · simpa [map_pow] using congrArg (fun z : (𝓞 L)ˣ => φ (z : L)) hu_pow
    · exact Nat.ne_of_gt hn
  have hr_norm : ‖(r : ℂ)‖ = 1 := by
    rwa [← hur] at hnorm
  have hr_abs : |r| = 1 := by
    simpa [Complex.norm_real] using hr_norm
  have hr_sq : r ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · left
    apply NumberField.Units.coe_injective (K := L)
    apply φ.injective
    simpa [hr] using hur.symm
  · right
    apply NumberField.Units.coe_injective (K := L)
    apply φ.injective
    simpa [hr] using hur.symm

lemma maximalRealSubfield_torsionOrder_eq_two :
    Units.torsionOrder (NumberField.maximalRealSubfield K) = 2 := by
  let L := NumberField.maximalRealSubfield K
  classical
  refine
    Finset.card_eq_two.2
      ⟨1, ⟨-1, neg_one_mem_torsion⟩, by simp [← Subtype.coe_ne_coe],
        Finset.ext fun x ↦
          ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact maximalRealSubfield_torsion_eq_one_or_neg_one (K := K) x

set_option linter.unusedSectionVars false in
lemma cyclotomic_torsionOrder_eq_two_mul_prime (hp_odd' : p ≠ 2) :
    Units.torsionOrder K = 2 * p := by
  letI := neZero_p (p := p)
  have hneven : ¬ Even p := fun h =>
    hp_odd' ((hp.out.even_iff).mp h)
  simpa [hneven, two_mul] using
    (IsCyclotomicExtension.Rat.torsionOrder_eq (n := p) (K := K))

lemma units_rank_eq_prime_sub_three_div_two :
    Units.rank K = (p - 3) / 2 := by
  let L := NumberField.maximalRealSubfield K
  rw [← NumberField.IsCMField.units_rank_eq_units_rank (K := K), Units.rank]
  calc
    Fintype.card (NumberField.InfinitePlace L) - 1
        = NumberField.InfinitePlace.nrRealPlaces L - 1 := by
            rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
              NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    _ = Module.finrank ℚ L - 1 := by
          rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 - 1 := by
          rw [finrank_Kplus_over_rat (p := p) (K := K)]
    _ = (p - 3) / 2 := by omega

lemma regulator_div_regulator_maximalRealSubfield_eq_pow (hp_odd' : p ≠ 2) :
    Units.regulator K / Units.regulator (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 3) / 2 : ℕ) := by
  rw [NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv (K := K),
    indexRealUnits_eq_one (p := p) (K := K) (hp_odd := hp_odd'),
    units_rank_eq_prime_sub_three_div_two (p := p) (K := K)]
  simp

set_option linter.unusedSectionVars false in
lemma abs_discr_cyclotomic_eq_pow :
    |((NumberField.discr K : ℤ) : ℝ)| = (p : ℝ) ^ (p - 2) := by
  rw [IsCyclotomicExtension.Rat.discr_prime (p := p) (K := K)]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow]
  simp [abs_of_nonneg (show 0 ≤ ((p : ℝ) ^ (p - 2)) by positivity)]

set_option linter.unusedSectionVars false in
lemma zeta_not_mem_maximalRealSubfield (hp_odd' : p ≠ 2) :
    IsCyclotomicExtension.zeta p ℚ K ∉ NumberField.maximalRealSubfield K := by
  classical
  let ζ : K := IsCyclotomicExtension.zeta p ℚ K
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  intro hmem
  have hfix := (NumberField.mem_maximalRealSubfield_iff (K := K) ζ).mp hmem
  let φ : K →+* ℂ := Classical.choice inferInstance
  have hstar : star (φ ζ) = φ ζ := hfix φ
  have hpow : (φ ζ) ^ p = 1 := by
    simpa [map_pow] using congrArg φ hζ.pow_eq_one
  have hnorm : ‖φ ζ‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one
    · exact hpow
    · exact hp.out.ne_zero
  have him : (φ ζ).im = 0 := by
    simpa [RCLike.star_def] using (Complex.conj_eq_iff_im.mp hstar)
  let r : ℝ := (φ ζ).re
  have hreal : φ ζ = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  rw [hreal] at hnorm
  have hr_abs : |r| = 1 := by
    simpa [Complex.norm_real] using hnorm
  have hr_sq : r ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · have hφζ : φ ζ = 1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (1 : ℂ) := by simp [hr]
    have hζeq : ζ = 1 := φ.injective <| by simpa using hφζ
    exact (hζ.ne_one hp.out.one_lt) hζeq
  · have hφζ : φ ζ = -1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (-1 : ℂ) := by simp [hr]
    have hpo : Odd p := hp.out.odd_of_ne_two hp_odd'
    have : ((-1 : ℂ) ^ p) = 1 := by simpa [hφζ] using hpow
    have hneg : (-1 : ℂ) = 1 := by simpa [Odd.neg_one_pow hpo] using this
    have hneq : (-1 : ℂ) ≠ 1 := by norm_num
    exact hneq hneg

lemma zetaInteger_not_mem_field_range (hp_odd' : p ≠ 2) :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∉
      Set.range (algebraMap (NumberField.maximalRealSubfield K) K) := by
  rintro ⟨x, hx⟩
  have hxmem : (algebraMap (NumberField.maximalRealSubfield K) K x) ∈
      NumberField.maximalRealSubfield K := x.2
  have hzmem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈
      NumberField.maximalRealSubfield K := by
    simpa [hx] using hxmem
  exact zeta_not_mem_maximalRealSubfield (p := p) (K := K) hp_odd' hzmem

lemma zetaInteger_not_mem_ring_range (hp_odd' : p ≠ 2) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ∉
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
  rintro ⟨x, hx⟩
  apply zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd'
  refine ⟨(x : NumberField.maximalRealSubfield K), ?_⟩
  exact congrArg (fun y : 𝓞 K => (y : K)) hx

lemma zetaInteger_adjoin_eq_top_maximalRealSubfield (hp_odd' : p ≠ 2) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K) = ⊤ := by
  let L : IntermediateField (NumberField.maximalRealSubfield K) K :=
    IntermediateField.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K)
  have hL : L = ⊤ := by
    have hprime : Nat.Prime (Module.finrank (NumberField.maximalRealSubfield K) K) := by
      simpa [finrank_K_over_Kplus (K := K)] using Nat.prime_two
    have hsimple :=
      ((IntermediateField.isSimpleOrder_of_finrank_prime (NumberField.maximalRealSubfield K) K
          hprime).eq_bot_or_eq_top L)
    refine hsimple.resolve_left ?_
    intro hbot
    have hzeta_mem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈ L :=
      IntermediateField.subset_adjoin _ _ (by simp)
    rw [hbot, IntermediateField.mem_bot] at hzeta_mem
    exact zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd' hzeta_mem
  have hzeta_alg : IsAlgebraic (NumberField.maximalRealSubfield K)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact Algebra.adjoin_eq_top_of_primitive_element hzeta_alg hL

set_option linter.unusedSectionVars false in
lemma one_add_zetaInteger_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)) := by
  let ζ : K := IsCyclotomicExtension.zeta p ℚ K
  let η : K := -ζ
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  have hη : IsPrimitiveRoot η (2 * p) := by
    convert IsPrimitiveRoot.orderOf η
    rw [show η = -ζ by rfl, neg_eq_neg_one_mul,
      (Commute.all (-1 : K) ζ).orderOf_mul_eq_mul_orderOf_of_coprime]
    · simp [hζ.eq_orderOf]
    · simp [← hζ.eq_orderOf, hp.out.odd_of_ne_two hp_odd']
  let S : Set K := {x | ∃ n ∈ ({2 * p} : Set ℕ), n ≠ 0 ∧ x ^ n = 1}
  letI : IsCyclotomicExtension {2 * p} ℚ K :=
    (IsCyclotomicExtension.iff_adjoin_eq_top {2 * p} ℚ K).2
      ⟨fun n hn hn0 => by
          rw [Set.mem_singleton_iff] at hn
          subst hn
          exact ⟨η, hη⟩,
        by
          refine le_antisymm le_top ?_
          have hzeta_mem : ζ ∈ Algebra.adjoin ℚ S := by
            have hη_mem : η ∈ Algebra.adjoin ℚ S :=
              Algebra.subset_adjoin
                ⟨2 * p, by simp, Nat.mul_ne_zero two_ne_zero hp.out.ne_zero, hη.pow_eq_one⟩
            simpa [η, S] using Subalgebra.neg_mem (Algebra.adjoin ℚ S) hη_mem
          have hle : Algebra.adjoin ℚ ({ζ} : Set K) ≤ Algebra.adjoin ℚ S :=
            Algebra.adjoin_le fun x hx => by
              rw [Set.mem_singleton_iff] at hx
              subst x
              exact hzeta_mem
          have htopζ : Algebra.adjoin ℚ ({ζ} : Set K) = ⊤ :=
            IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
          change ⊤ ≤ Algebra.adjoin ℚ S
          rw [← htopζ]
          exact hle⟩
  have hnotPrimePow : ∀ {q : ℕ}, q.Prime → ∀ k : ℕ, q ^ k ≠ 2 * p := by
    intro q hq k
    cases k with
    | zero =>
        intro hk
        simp at hk
        have hp2 : 2 ≤ p := hp.out.two_le
        omega
    | succ k =>
        intro hk
        have hpow : IsPrimePow (2 * p) := ⟨q, k + 1, by simpa [Nat.prime_iff] using hq,
          Nat.succ_pos _, hk⟩
        have hcop : Nat.Coprime 2 p := by
          simpa using (hp.out.odd_of_ne_two hp_odd').coprime_two_left
        rcases (Nat.Coprime.isPrimePow_dvd_mul (a := 2) (b := p) hcop hpow).1 dvd_rfl with h | h
        · have hp2 : 2 ≤ p := hp.out.two_le
          have hle : 2 * p ≤ 2 := Nat.le_of_dvd (by positivity) h
          omega
        · have hp2 : 2 ≤ p := hp.out.two_le
          have hle : 2 * p ≤ p := Nat.le_of_dvd hp.out.pos h
          omega
  have hnorm : Algebra.norm ℤ ((hη.toInteger : 𝓞 K) - 1) = 1 := by
    apply IsPrimitiveRoot.norm_toInteger_sub_one_eq_one (K := K) hη
    · have hp2 : 2 ≤ p := hp.out.two_le
      have : 2 < 2 * p := by omega
      exact this
    · intro q hq k
      exact hnotPrimePow hq k
  have hspan : Ideal.span ({((hη.toInteger : 𝓞 K) - 1)} : Set (𝓞 K)) = ⊤ := by
    apply (Ideal.absNorm_eq_one_iff).mp
    rw [Ideal.absNorm_span_singleton, hnorm, Int.natAbs_one]
  have hunit : IsUnit ((hη.toInteger : 𝓞 K) - 1) :=
    (Ideal.span_singleton_eq_top).mp hspan
  simpa [η, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hunit.neg

set_option linter.unusedSectionVars false in
lemma zetaInteger_pow_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p : 𝓞 K) = 1 := by
  simpa using
    congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K))
      (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit_unit
        (NeZero.ne p)).pow_eq_one)

lemma zetaInteger_pow_pred_mul_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) = 1 := by
  calc
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)
    = (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) + 1) :
        𝓞 K) := by
      rw [pow_succ]
  _ = (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p : 𝓞 K) := by
      rw [Nat.sub_add_cancel hp.out.one_le]
    _ = 1 := zetaInteger_pow_eq_one (p := p) (K := K)

lemma zetaInteger_mul_pow_pred_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) : 𝓞 K) = 1 := by
  simpa [mul_comm] using zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)

lemma one_add_zetaInteger_pow_pred_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hzeta_unit : IsUnit (ζi ^ (p - 1) : 𝓞 K) := by
    simpa [ζi] using
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit
        (NeZero.ne p)).pow (p - 1)
  have hmul : (ζi ^ (p - 1) : 𝓞 K) * (1 + ζi) = 1 + ζi ^ (p - 1) := by
    rw [mul_add, mul_one, zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
    ring
  rw [← hmul]
  exact hzeta_unit.mul (one_add_zetaInteger_isUnit (p := p) (K := K) hp_odd')

lemma algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred :
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) (piPlus p K) =
      (2 : 𝓞 K) - (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [algebraMap_piPlus]
  have hconj : NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1) =
      ζi ^ (p - 1) - 1 := by
    rw [map_sub, map_one, complexConj_apply_zeta]
  calc
    (ζi - 1) * NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1)
        = (ζi - 1) * (ζi ^ (p - 1) - 1) := by rw [hconj]
    _ = ζi * ζi ^ (p - 1) - ζi - ζi ^ (p - 1) + 1 := by
          ring
    _ = (2 : 𝓞 K) - ζi - ζi ^ (p - 1) := by
          rw [zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)]
          ring_nf

lemma aeval_zetaInteger_quadratic_eq_zero :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))) = 0 := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hcalc :
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1 = 0 := by
    calc
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1
          = -(ζi ^ (p - 1) * ζi) + 1 := by ring
      _ = 0 := by
            rw [zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
            norm_num
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    pow_two, map_sub, map_ofNat, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm]
    using hcalc

lemma minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (hp_odd' : p ≠ 2) :
    minpoly (𝓞 (NumberField.maximalRealSubfield K))
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) =
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))) := by
  let A := 𝓞 (NumberField.maximalRealSubfield K)
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hint : IsIntegral A ζi := IsIntegralClosure.isIntegral A K ζi
  have hdeg :
      ((Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree) ≤
        (minpoly A ζi).degree := by
    have hnatdeg : 2 ≤ (minpoly A ζi).natDegree :=
      (minpoly.two_le_natDegree_iff hint).2
        (zetaInteger_not_mem_ring_range (p := p) (K := K) hp_odd')
    have hpoly_deg :
        (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree = 2 := by
      simpa [one_mul, Polynomial.C_1] using
        (Polynomial.degree_quadratic
          (R := A)
          (a := (1 : A))
          (b := piPlus p K - 2)
          (c := (1 : A))
          one_ne_zero)
    rw [hpoly_deg, Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast hnatdeg
  symm
  refine IsIntegrallyClosed.minpoly.unique (R := A) (S := 𝓞 K) (s := ζi) ?_ ?_ ?_
  · simpa [Polynomial.C_1] using
      (Polynomial.isMonicOfDegree_add_add_two (a := piPlus p K - 2) (b := (1 : A))).monic
  · exact aeval_zetaInteger_quadratic_eq_zero (p := p) (K := K)
  · intro Q hQ hQroot
    exact hdeg.trans (minpoly.min (A := A) (x := ζi) hQ hQroot)

lemma aeval_derivative_minpoly_zetaInteger_eq_zeta_sub_complexConj_zeta (hp_odd' : p ≠ 2) :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.derivative
        (minpoly (𝓞 (NumberField.maximalRealSubfield K))
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have htwo :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2 = (2 : 𝓞 K) := by
    simpa using map_natCast (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2
  rw [minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (p := p) (K := K) hp_odd']
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    map_sub, htwo, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using
    (show ((1 + 1 : 𝓞 K) * ζi) + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) =
        ζi - ζi ^ (p - 1) by ring)

lemma span_zetaInteger_sub_zetaPowPred_eq_zetaPrime (hp_odd' : p ≠ 2) :
    Ideal.span
        ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1)} :
          Set (𝓞 K)) =
      zetaPrime p K := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [zetaPrime]
  have hcalc :
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - ζi ^ (p - 1) := by
    have hmul : ζi * ζi ^ (p - 1) = 1 := zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)
    calc
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - 1 + (ζi * ζi ^ (p - 1) - ζi ^ (p - 1)) := by
        ring
      _ = ζi - ζi ^ (p - 1) := by
        rw [hmul]
        ring
  rw [← hcalc, Ideal.span_singleton_mul_right_unit]
  exact one_add_zetaInteger_pow_pred_isUnit (p := p) (K := K) hp_odd'

lemma differentIdeal_maximalRealSubfield_eq_zetaPrime (hp_odd' : p ≠ 2) :
    differentIdeal (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) = zetaPrime p K := by
  let A := 𝓞 (NumberField.maximalRealSubfield K)
  let B := 𝓞 K
  let PPlus : Ideal A := zetaPrimePlus p K
  let P : Ideal B := zetaPrime p K
  have hPPlus0 : PPlus ≠ ⊥ := by
    intro hbot
    have hmap : Ideal.map (algebraMap A B) PPlus = P ^ 2 := by
      simpa [A, B, PPlus, P] using zetaPrimePlus_map_eq (p := p) (hp_odd := hp_odd') (K := K)
    rw [hbot, Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 (zetaPrime_ne_bot p K)) hmap.symm
  have hle : differentIdeal A B ≤ P := by
    letI : PPlus.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPPlus0
    have hdiv : P ∣ differentIdeal A B := by
      have hpow : P ^ 2 ∣ Ideal.map (algebraMap A B) PPlus := by
        rw [zetaPrimePlus_map_eq (p := p) (hp_odd := hp_odd') (K := K)]
      simpa [A, B, P, PPlus] using
        (pow_sub_one_dvd_differentIdeal (A := A) (B := B) (p := PPlus) P 2 hPPlus0 hpow)
    exact Ideal.dvd_iff_le.mp hdiv
  have hmem :
      Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
          (Polynomial.derivative
            (minpoly A ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : B))) ∈
        differentIdeal A B :=
    aeval_derivative_mem_differentIdeal (A := A)
      (K := NumberField.maximalRealSubfield K) (L := K) (B := B)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger)
      (zetaInteger_adjoin_eq_top_maximalRealSubfield (p := p) (K := K) hp_odd')
  have hP_le : P ≤ differentIdeal A B := by
    change zetaPrime p K ≤ differentIdeal A B
    rw [← span_zetaInteger_sub_zetaPowPred_eq_zetaPrime (p := p) (K := K) hp_odd']
    rw [Ideal.span_singleton_le_iff_mem]
    convert hmem using 1
    symm
    exact aeval_derivative_minpoly_zetaInteger_eq_zeta_sub_complexConj_zeta
      (p := p) (K := K) hp_odd'
  exact le_antisymm hle hP_le

lemma absNorm_differentIdeal_maximalRealSubfield_eq_prime (hp_odd' : p ≠ 2) :
    Ideal.absNorm (differentIdeal (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = p := by
  rw [differentIdeal_maximalRealSubfield_eq_zetaPrime (p := p) (K := K) hp_odd',
    zetaPrime]
  rw [Ideal.absNorm_span_singleton,
    (IsCyclotomicExtension.zeta_spec p ℚ K).norm_toInteger_sub_one_of_prime_ne_two' hp_odd']
  simp [Int.natAbs_natCast]

lemma natAbs_discr_maximalRealSubfield_eq_pow (hp_odd' : p ≠ 2) :
    (NumberField.discr (NumberField.maximalRealSubfield K)).natAbs = p ^ ((p - 3) / 2) := by
  let L := NumberField.maximalRealSubfield K
  have hmain := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := L) (𝒪 := 𝓞 L) (L := K) (𝒪' := 𝓞 K)
  have hdiscrK : (NumberField.discr K).natAbs = p ^ (p - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime (p := p) (K := K)]
    simp [Int.natAbs_mul]
  have hfin : Module.finrank L K = 2 := by
    simpa [L] using (finrank_K_over_Kplus (K := K))
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.out.two_le
    omega
  rw [hdiscrK, absNorm_differentIdeal_maximalRealSubfield_eq_prime (p := p)
      (K := K) hp_odd'] at hmain
  have hmain2 : p ^ (p - 2) = p * (NumberField.discr L).natAbs ^ 2 := by
    conv_rhs => rw [← hfin]
    exact hmain
  have hsq : (NumberField.discr L).natAbs ^ 2 = p ^ (p - 3) := by
    have hmain' : p * p ^ (p - 3) = p * (NumberField.discr L).natAbs ^ 2 := by
      calc
        p * p ^ (p - 3) = p ^ (p - 2) := by
          rw [show p - 2 = (p - 3) + 1 by omega, pow_succ', mul_comm]
        _ = p * (NumberField.discr L).natAbs ^ 2 := hmain2
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmain'.symm
  have hpow : (p ^ ((p - 3) / 2)) ^ 2 = p ^ (p - 3) := by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n, hn⟩
    have hdiv : (p - 3) / 2 = n - 1 := by
      rw [hn, show 2 * n + 1 - 3 = 2 * (n - 1) by omega,
        Nat.mul_div_right _ (by decide : 0 < 2)]
    calc
      (p ^ ((p - 3) / 2)) ^ 2 = (p ^ (n - 1)) ^ 2 := by rw [hdiv]
      _ = p ^ ((n - 1) * 2) := by rw [← pow_mul]
      _ = p ^ (p - 3) := by
            congr
            rw [hn]
            omega
  have hsq' : (NumberField.discr L).natAbs ^ 2 = (p ^ ((p - 3) / 2)) ^ 2 := by
    rw [hpow, hsq]
  have := congrArg Nat.sqrt hsq'
  simpa [Nat.sqrt_eq'] using this

lemma abs_discr_maximalRealSubfield_eq_pow (hp_odd' : p ≠ 2) :
    |((NumberField.discr (NumberField.maximalRealSubfield K) : ℤ) : ℝ)| =
      (p : ℝ) ^ ((p - 3) / 2) := by
  have habs : (((NumberField.discr (NumberField.maximalRealSubfield K)).natAbs : ℕ) : ℝ) =
      |((NumberField.discr (NumberField.maximalRealSubfield K) : ℤ) : ℝ)| := by
    convert
      (Nat.cast_natAbs (α := ℝ) (NumberField.discr (NumberField.maximalRealSubfield K))) using 1
    simp
  rw [← habs, natAbs_discr_maximalRealSubfield_eq_pow (p := p) (K := K) hp_odd', Nat.cast_pow]

/-- The class number formula for the prime cyclotomic field, with the standard
cyclotomic invariants made explicit. -/
theorem h_formula_cyclotomic (hp_odd' : p ≠ 2) :
    (h K : ℝ) =
      NumberField.dedekindZeta_residue K *
        ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K)) := by
  have hp_gt2 : 2 < p := lt_of_le_of_ne hp.out.two_le (by simpa using hp_odd'.symm)
  have hreal : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := p) (K := K) hp_gt2
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = (p - 1) / 2 := by
    simpa [Nat.totient_prime hp.out] using
      (IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := p) (K := K))
  rw [h_formula (K := K), hreal, hcomplex,
    cyclotomic_torsionOrder_eq_two_mul_prime (p := p) (K := K) hp_odd',
    abs_discr_cyclotomic_eq_pow (p := p) (K := K)]
  simp [mul_assoc, mul_comm]

end ClassNumberFormula

end BernoulliRegular
