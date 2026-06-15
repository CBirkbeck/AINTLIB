module

public import BernoulliRegular.ImaginaryQuadratic.CN05.Statement


@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

section CN05_statement

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Hypothesis: `𝒪_{Kminus p} = ℤ[α]`** (the integral closure coincides with the
ℤ-adjoin of `α`), for `p ≡ 3 (mod 4)` prime.

This follows from `disc(ℤ[α]) = disc(𝒪) = -p` via `[𝒪 : ℤ[α]]² · disc(𝒪) = disc(ℤ[α])`
⟹ `[𝒪 : ℤ[α]]² = 1` ⟹ `[𝒪 : ℤ[α]] = 1` ⟹ `ℤ[α] = 𝒪`. The CN-03 proof implicitly
establishes this (via `P_int.det² = 1`), but the explicit lemma requires
re-extracting the determinant condition from CN-03.

Once proved, this gives `RingOfIntegers.exponent alphaInOK = 1` via
`RingOfIntegers.exponent_eq_one_iff`, unlocking Kummer-Dedekind for all primes
q coprime to `exponent α = 1` (i.e., all q).

Kummer-Dedekind then gives the splitting behavior of primes `q` in `Kminus p`
via `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`: primes over q in `𝒪_K`
biject with irreducible factors of `minpoly α = X² - X + C((p+1)/4)` mod q. -/
def AlphaGenerates (hp3 : p % 4 = 3) : Prop :=
  Algebra.adjoin ℤ ({alphaInOK p hp3} : Set (𝓞 (Kminus p))) = ⊤

/-- `Algebra.trace ℤ (𝒪 (Kminus p)) 1 = 2`. -/
lemma trace_one_Kminus_eq :
    Algebra.trace ℤ (𝓞 (Kminus p)) (1 : 𝓞 (Kminus p)) = 2 := by
  have h : ((Algebra.trace ℤ (𝓞 (Kminus p)) 1 : ℤ) : ℚ) =
      Algebra.trace ℚ (Kminus p) ((1 : 𝓞 (Kminus p)) : Kminus p) :=
    Algebra.coe_trace_int 1
  rw [show ((1 : 𝓞 (Kminus p)) : Kminus p) = 1 from rfl] at h
  have h_trace_one : Algebra.trace ℚ (Kminus p) (1 : Kminus p) = 2 := by
    rw [Algebra.trace_eq_matrix_trace (Module.finBasis ℚ (Kminus p))]
    simp [Matrix.trace, finrank_Kminus p]
  rw [h_trace_one] at h
  exact_mod_cast h

/-- `Algebra.trace ℚ (Kminus p) (halfOnePlusSqrtNegP p) = 1`. Follows from
`PowerBasis.trace_gen_eq_nextCoeff_minpoly` and `halfOnePlusSqrtNegP_minpoly`. -/
lemma trace_halfOnePlusSqrtNegP_eq_one (hp3 : p % 4 = 3) :
    Algebra.trace ℚ (Kminus p) (halfOnePlusSqrtNegP p) = 1 := by
  have h := (alphaPowerBasis p hp3).trace_gen_eq_nextCoeff_minpoly
  rw [alphaPowerBasis_gen, halfOnePlusSqrtNegP_minpoly p hp3] at h
  have hnatDeg : (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ℚ) : Polynomial ℚ).natDegree = 2 := by
    compute_degree!
  rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hnatDeg]; omega), hnatDeg] at h
  simp at h
  linarith

/-- `Algebra.trace ℤ (𝒪 (Kminus p)) alphaInOK = 1`. -/
lemma trace_alphaInOK_eq_one (hp3 : p % 4 = 3) :
    Algebra.trace ℤ (𝓞 (Kminus p)) (alphaInOK p hp3) = 1 := by
  have h : ((Algebra.trace ℤ (𝓞 (Kminus p)) (alphaInOK p hp3) : ℤ) : ℚ) =
      Algebra.trace ℚ (Kminus p) ((alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) :=
    Algebra.coe_trace_int (alphaInOK p hp3)
  rw [show ((alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) = halfOnePlusSqrtNegP p from rfl] at h
  rw [trace_halfOnePlusSqrtNegP_eq_one p hp3] at h
  exact_mod_cast h

/-- `α² = α - (p+1)/4` in `Kminus p` (the "square rewrite" from minpoly). -/
lemma halfOnePlusSqrtNegP_sq_eq (hp3 : p % 4 = 3) :
    halfOnePlusSqrtNegP p * halfOnePlusSqrtNegP p =
      halfOnePlusSqrtNegP p - (((p + 1) / 4 : ℕ) : Kminus p) := by
  have h_rel := halfOnePlusSqrtNegP_minpoly_relation p hp3
  -- h_rel : halfOnePlusSqrtNegP p ^ 2 - halfOnePlusSqrtNegP p + ((p + 1) / 4 : ℕ) = 0
  have : halfOnePlusSqrtNegP p ^ 2 = halfOnePlusSqrtNegP p - (((p + 1) / 4 : ℕ) : Kminus p) := by
    linear_combination h_rel
  rw [← sq]
  exact this

/-- `Algebra.trace ℚ (Kminus p) (α²) = 1 - 2·(p+1)/4 = 1 - (p+1)/2`. -/
lemma trace_halfOnePlusSqrtNegP_sq_eq_Q (hp3 : p % 4 = 3) :
    Algebra.trace ℚ (Kminus p) (halfOnePlusSqrtNegP p * halfOnePlusSqrtNegP p) =
      1 - 2 * (((p + 1) / 4 : ℕ) : ℚ) := by
  rw [halfOnePlusSqrtNegP_sq_eq p hp3, map_sub, trace_halfOnePlusSqrtNegP_eq_one p hp3]
  -- Goal: 1 - trace((p+1)/4 : Kminus p) = 1 - 2 * ((p+1)/4 : ℚ)
  rw [show (((p + 1) / 4 : ℕ) : Kminus p) =
      algebraMap ℚ (Kminus p) (((p + 1) / 4 : ℕ) : ℚ) from by push_cast; rfl]
  rw [Algebra.trace_algebraMap, finrank_Kminus]
  ring

/-- `Algebra.trace ℤ (𝒪 (Kminus p)) (α * α) = 1 - 2·(p+1)/4` as an integer. -/
lemma trace_alphaInOK_sq_eq (hp3 : p % 4 = 3) :
    Algebra.trace ℤ (𝓞 (Kminus p)) (alphaInOK p hp3 * alphaInOK p hp3) =
      1 - 2 * (((p + 1) / 4 : ℕ) : ℤ) := by
  have h : ((Algebra.trace ℤ (𝓞 (Kminus p)) (alphaInOK p hp3 * alphaInOK p hp3) : ℤ) : ℚ) =
      Algebra.trace ℚ (Kminus p)
        ((alphaInOK p hp3 * alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) :=
    Algebra.coe_trace_int _
  rw [show ((alphaInOK p hp3 * alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) =
      halfOnePlusSqrtNegP p * halfOnePlusSqrtNegP p from by push_cast; rfl] at h
  rw [trace_halfOnePlusSqrtNegP_sq_eq_Q p hp3] at h
  exact_mod_cast h

/-- **Key computation**: `Algebra.discr ℤ ![1, alphaInOK] = -p` for `p ≡ 3 mod 4`.

Direct trace-matrix computation:
  T[0,0] = trace(1) = 2
  T[0,1] = T[1,0] = trace(α) = 1
  T[1,1] = trace(α²) = 1 - 2·(p+1)/4

  det = 2·(1 - 2·(p+1)/4) - 1·1 = 2 - (p+1) - 1 = -p.

With the additional check that `p ≡ 3 mod 4` ⟹ `4·(p+1)/4 = p+1` so
`2·(p+1)/4 = (p+1)/2` ... but we can compute in ℤ directly via the
natural-number identity `4 ∣ p+1`. -/
theorem discr_alphaBasis_eq_neg_p (hp3 : p % 4 = 3) :
    Algebra.discr ℤ (![(1 : 𝓞 (Kminus p)), alphaInOK p hp3]) = -(p : ℤ) := by
  rw [Algebra.discr_def, Algebra.traceMatrix, Matrix.det_fin_two]
  simp_rw [Algebra.traceForm_apply]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.of_apply,
    Matrix.cons_val_zero, mul_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul]
  -- Goal: trace(1·1) · trace(α·α) - trace(1·α) · trace(1·α) = -p
  -- Reduce (1 : 𝒪 K) · x = x and x · (1 : 𝒪 K) = x.
  have h00 : Algebra.trace ℤ (𝓞 (Kminus p)) (1 : 𝓞 (Kminus p)) = 2 :=
    trace_one_Kminus_eq p
  have h01 : Algebra.trace ℤ (𝓞 (Kminus p)) (alphaInOK p hp3) = 1 :=
    trace_alphaInOK_eq_one p hp3
  have h11 : Algebra.trace ℤ (𝓞 (Kminus p))
      (alphaInOK p hp3 * alphaInOK p hp3) = 1 - 2 * (((p + 1) / 4 : ℕ) : ℤ) :=
    trace_alphaInOK_sq_eq p hp3
  rw [h00, h01, h11]
  -- 2 · (1 - 2 · (p+1)/4) - 1 · 1 = -p.
  -- The RHS here: 2·(p+1)/4 involves natural division.
  have hdvd : 4 ∣ p + 1 := four_dvd_succ_of_three_mod_four p hp3
  have h_nat : ((p + 1) / 4 : ℕ) * 4 = p + 1 := Nat.div_mul_cancel hdvd
  have h_cast : (((p + 1) / 4 : ℕ) : ℤ) * 4 = (p : ℤ) + 1 := by
    exact_mod_cast h_nat
  linarith

/-- `![1, alphaInOK]` is ℤ-linearly independent in `𝒪 (Kminus p)`.

Follows from `Algebra.discr_zero_of_not_linearIndependent`: if not LI, the
discriminant would be 0, but we just proved `discr = -p ≠ 0`. -/
lemma alphaBasis_linearIndependent (hp3 : p % 4 = 3) :
    LinearIndependent ℤ (![(1 : 𝓞 (Kminus p)), alphaInOK p hp3]) := by
  by_contra h_not_li
  have h_disc_zero : Algebra.discr ℤ (![(1 : 𝓞 (Kminus p)), alphaInOK p hp3]) = 0 :=
    Algebra.discr_zero_of_not_linearIndependent ℤ h_not_li
  rw [discr_alphaBasis_eq_neg_p p hp3] at h_disc_zero
  have : (p : ℤ) = 0 := by linarith
  have : p = 0 := by exact_mod_cast this
  exact hp.out.ne_zero this

/-- The signed discriminant of `Kminus p` is `-p` for `p ≡ 3 (mod 4)` prime.

Follows from CN-03 `natAbs(discr K) = p` combined with `NumberField.sign_discr`:
since `Kminus p` has `1` complex place (from `nrComplexPlaces_Kminus`),
`sign(discr K) = (-1)^1 = -1`, so `discr K < 0` with `natAbs = p`, giving
`discr K = -p`. -/
theorem discr_Kminus_eq_neg_p (hp3 : p % 4 = 3) :
    NumberField.discr (Kminus p) = -(p : ℤ) := by
  have h_natAbs : (NumberField.discr (Kminus p)).natAbs = p := discr_Kminus_natAbs_eq p hp3
  have h_sign : (NumberField.discr (Kminus p)).sign = -1 := by
    rw [NumberField.sign_discr, nrComplexPlaces_Kminus p]
    rfl
  have h_neg : NumberField.discr (Kminus p) < 0 := by
    rcases lt_trichotomy (NumberField.discr (Kminus p)) 0 with h | h | h
    · exact h
    · exact absurd h (NumberField.discr_ne_zero _)
    · rw [Int.sign_eq_one_of_pos h] at h_sign; norm_num at h_sign
  have h_eq : NumberField.discr (Kminus p) = -((NumberField.discr (Kminus p)).natAbs : ℤ) := by
    omega
  rw [h_eq, h_natAbs]

/-- `Module.finrank ℤ (𝒪 (Kminus p)) = 2` for `p ≡ 3 (mod 4)` prime. -/
lemma finrank_ringOfIntegers_Kminus :
    Module.finrank ℤ (𝓞 (Kminus p)) = 2 := by
  rw [NumberField.RingOfIntegers.rank, finrank_Kminus]

/-- **`AlphaGenerates` is true**: `𝒪_{Kminus p} = ℤ[α]` for `p ≡ 3 (mod 4)` prime.

The strategy: given any ℤ-basis `B` of `𝒪 K` (indexed by `Fin 2`), the matrix
`M = B.toMatrix ![1, α]` satisfies `disc ℤ ![1, α] = M.det² · disc ℤ B`, i.e.,
`-p = M.det² · (-p)`, so `M.det² = 1`, hence `M.det = ±1`, i.e., `IsUnit M.det`.
By `Basis.is_basis_iff_det`, `![1, α]` spans `𝒪 K`, and since `Algebra.adjoin ℤ {α}`
contains both `1` and `α`, it contains the span, hence equals `⊤`. -/
theorem alphaGenerates (hp3 : p % 4 = 3) :
    Algebra.adjoin ℤ ({alphaInOK p hp3} : Set (𝓞 (Kminus p))) = ⊤ := by
  classical
  set v : Fin 2 → 𝓞 (Kminus p) := ![1, alphaInOK p hp3] with hv_def
  have hli : LinearIndependent ℤ v := alphaBasis_linearIndependent p hp3
  -- Step 1: Get a ℤ-basis of 𝒪 (Kminus p) indexed by Fin 2.
  have h_rank : Module.finrank ℤ (𝓞 (Kminus p)) = 2 := finrank_ringOfIntegers_Kminus p
  set B : Module.Basis (Fin 2) ℤ (𝓞 (Kminus p)) :=
    Module.finBasisOfFinrankEq ℤ (𝓞 (Kminus p)) h_rank with hB_def
  -- Step 2: disc ℤ v = -p and disc ℤ B = -p.
  have h_disc_v : Algebra.discr ℤ v = -(p : ℤ) := discr_alphaBasis_eq_neg_p p hp3
  have h_disc_B : Algebra.discr ℤ ⇑B = -(p : ℤ) := by
    rw [NumberField.discr_eq_discr (Kminus p) B]
    exact discr_Kminus_eq_neg_p p hp3
  -- Step 3: Use `Algebra.discr_of_matrix_vecMul` to relate them.
  set M : Matrix (Fin 2) (Fin 2) ℤ := B.toMatrix v with hM_def
  have h_vecMul : v = Matrix.vecMul (⇑B) (M.map (algebraMap ℤ (𝓞 (Kminus p)))) := by
    symm; exact B.toMatrix_map_vecMul v
  have h_disc_eq : Algebra.discr ℤ v = M.det ^ 2 * Algebra.discr ℤ ⇑B := by
    rw [h_vecMul]; exact Algebra.discr_of_matrix_vecMul _ _
  rw [h_disc_v, h_disc_B] at h_disc_eq
  -- h_disc_eq : -(p : ℤ) = M.det ^ 2 * -(p : ℤ)
  -- Step 4: Deduce M.det ^ 2 = 1.
  have hp_ne : (-(p : ℤ)) ≠ 0 := by
    simp only [ne_eq, neg_eq_zero, Nat.cast_eq_zero]; exact hp.out.ne_zero
  have h_det_sq : M.det ^ 2 = 1 := by
    have h_factor : -(p : ℤ) * (1 - M.det ^ 2) = 0 := by linarith
    rcases mul_eq_zero.mp h_factor with h | h
    · exact absurd h hp_ne
    · linarith
  -- Step 5: IsUnit M.det.
  have h_det_unit : IsUnit M.det := by
    rcases sq_eq_one_iff.mp h_det_sq with h | h
    · rw [h]; exact isUnit_one
    · rw [h]; exact isUnit_one.neg
  -- Step 6: By `is_basis_iff_det`, span ℤ (range v) = ⊤.
  have h_det_v_unit : IsUnit (B.det v) := by
    rw [Module.Basis.det_apply]; exact h_det_unit
  obtain ⟨_, h_span⟩ := B.is_basis_iff_det.mpr h_det_v_unit
  -- Step 7: Algebra.adjoin ℤ {α} contains 1 and α, hence contains span v.
  rw [eq_top_iff]
  rintro x -
  have h_one : (1 : 𝓞 (Kminus p)) ∈ Algebra.adjoin ℤ ({alphaInOK p hp3} : Set _) :=
    Subalgebra.one_mem _
  have h_alpha : alphaInOK p hp3 ∈ Algebra.adjoin ℤ ({alphaInOK p hp3} : Set _) :=
    Algebra.self_mem_adjoin_singleton ℤ _
  have h_subset : Submodule.span ℤ (Set.range v) ≤
      (Algebra.adjoin ℤ ({alphaInOK p hp3} : Set _)).toSubmodule := by
    rw [Submodule.span_le]
    rintro y ⟨i, hi⟩
    fin_cases i
    · simp only [hv_def] at hi
      rw [← hi]
      exact h_one
    · simp only [hv_def] at hi
      rw [← hi]
      exact h_alpha
  have hx : x ∈ Submodule.span ℤ (Set.range v) := by
    rw [h_span]; trivial
  exact h_subset hx

/-- **Corollary of `alphaGenerates`**: the Kummer-Dedekind exponent of `α`
as an element of `𝒪 (Kminus p)` is `1`, unlocking Kummer-Dedekind for all
rational primes `q`. -/
theorem exponent_alphaInOK_eq_one (hp3 : p % 4 = 3) :
    RingOfIntegers.exponent (alphaInOK p hp3) = 1 := by
  rw [RingOfIntegers.exponent_eq_one_iff]
  exact alphaGenerates p hp3

/-- **Corollary of `exponent_alphaInOK_eq_one`**: for any prime `q`,
`q` does not divide the exponent of `α`. -/
theorem not_dvd_exponent_alphaInOK (hp3 : p % 4 = 3) (q : ℕ) [hq : Fact q.Prime] :
    ¬ q ∣ RingOfIntegers.exponent (alphaInOK p hp3) := by
  rw [exponent_alphaInOK_eq_one p hp3]
  exact fun h => hq.out.one_lt.ne' (Nat.dvd_one.mp h)

/-- The minimal polynomial of `alphaInOK p hp3` over `ℤ` is `X² - X + C((p+1)/4)`. -/
theorem alphaInOK_minpoly_int (hp3 : p % 4 = 3) :
    minpoly ℤ (alphaInOK p hp3) =
      Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℤ) := by
  -- Reduce to the coercion.
  have h_coe : minpoly ℤ ((alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) =
               minpoly ℤ (alphaInOK p hp3) :=
    NumberField.RingOfIntegers.minpoly_coe _
  have h_eq : ((alphaInOK p hp3 : 𝓞 (Kminus p)) : Kminus p) = halfOnePlusSqrtNegP p := rfl
  rw [h_eq] at h_coe
  -- Relate minpoly ℤ to minpoly ℚ via integral closure.
  have h_Q : minpoly ℚ (halfOnePlusSqrtNegP p) =
             Polynomial.map (algebraMap ℤ ℚ) (minpoly ℤ (halfOnePlusSqrtNegP p)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (halfOnePlusSqrtNegP_isIntegral p hp3)
  rw [halfOnePlusSqrtNegP_minpoly p hp3] at h_Q
  -- The candidate integer polynomial maps to the rational one.
  have h_map : Polynomial.map (algebraMap ℤ ℚ)
      (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℤ) : Polynomial ℤ) =
      Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℚ) := by
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    push_cast
    rfl
  -- Polynomial.map is injective over an injective ring hom.
  have h_inj : Function.Injective (Polynomial.map (algebraMap ℤ ℚ)) :=
    Polynomial.map_injective _ (by exact_mod_cast Int.cast_injective (α := ℚ))
  have h_minp : minpoly ℤ (halfOnePlusSqrtNegP p) =
                Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℤ) := by
    apply h_inj
    rw [h_map]
    exact h_Q.symm
  rw [← h_coe]
  exact h_minp

/-- The reduction of `minpoly ℤ α` mod a prime `q` is `X² - X + C((p+1)/4 mod q)`. -/
theorem alphaInOK_minpoly_int_mod_q (hp3 : p % 4 = 3) (q : ℕ) [Fact q.Prime] :
    Polynomial.map (Int.castRingHom (ZMod q)) (minpoly ℤ (alphaInOK p hp3)) =
      Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) := by
  rw [alphaInOK_minpoly_int p hp3]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C]
  congr 2
  exact Int.cast_natCast _

/-- For `p ≡ 3 (mod 4)` prime, `(p+1)/4 ≡ 4⁻¹ (mod p)`. Equivalently,
`4 · ((p+1)/4 : ZMod p) = 1`. -/
lemma four_mul_pSuccDivFour_eq_one_mod_p (hp3 : p % 4 = 3) :
    (4 : ZMod p) * (((p + 1) / 4 : ℕ) : ZMod p) = 1 := by
  have hdvd : 4 ∣ p + 1 := four_dvd_succ_of_three_mod_four p hp3
  have h_nat : ((p + 1) / 4 : ℕ) * 4 = p + 1 := Nat.div_mul_cancel hdvd
  have h_cast : ((((p + 1) / 4 : ℕ) * 4 : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h_nat
  push_cast at h_cast
  have hp_z : (p : ZMod p) = 0 := ZMod.natCast_self p
  rw [hp_z, zero_add] at h_cast
  rw [mul_comm]
  exact h_cast

/-- For `p ≡ 3 (mod 4)` prime, the reduction of `minpoly ℤ α` mod `p`
has discriminant `1² - 4·((p+1)/4) = 1 - 1 = 0`, i.e., a repeated root. -/
lemma alphaInOK_minpoly_discriminant_zero_mod_p (hp3 : p % 4 = 3) :
    (1 : ZMod p) - 4 * (((p + 1) / 4 : ℕ) : ZMod p) = 0 := by
  rw [four_mul_pSuccDivFour_eq_one_mod_p p hp3]; ring

omit hp in
/-- For any prime `q` with `p ≡ 3 (mod 4)`, `4 · ((p+1)/4 : ZMod q) = p + 1` in `ZMod q`. -/
lemma four_mul_pSuccDivFour_eq_mod_q (hp3 : p % 4 = 3) (q : ℕ) [Fact q.Prime] :
    (4 : ZMod q) * (((p + 1) / 4 : ℕ) : ZMod q) = ((p : ZMod q) + 1) := by
  have hdvd : 4 ∣ p + 1 := four_dvd_succ_of_three_mod_four p hp3
  have h_nat : ((p + 1) / 4 : ℕ) * 4 = p + 1 := Nat.div_mul_cancel hdvd
  have h_cast : ((((p + 1) / 4 : ℕ) * 4 : ℕ) : ZMod q) = ((p + 1 : ℕ) : ZMod q) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod q) h_nat
  push_cast at h_cast
  rw [mul_comm]
  exact h_cast

/-- For a prime `q ≠ p` (both primes, `p ≡ 3 mod 4`), the discriminant of
`minpoly α mod q = X² - X + C((p+1)/4)` is `1 - (p+1) = -p`, which is nonzero
in `ZMod q` since `q ≠ p`. -/
lemma alphaInOK_minpoly_discriminant_mod_q_ne_zero (hp3 : p % 4 = 3) (q : ℕ)
    [hq : Fact q.Prime] (hqp : q ≠ p) :
    (1 : ZMod q) - 4 * (((p + 1) / 4 : ℕ) : ZMod q) = -(p : ZMod q) ∧
      -(p : ZMod q) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [four_mul_pSuccDivFour_eq_mod_q p hp3 q]; ring
  · intro h_zero
    rw [neg_eq_zero] at h_zero
    have hq_dvd_p : (q : ℕ) ∣ p := (ZMod.natCast_eq_zero_iff p q).mp (by exact_mod_cast h_zero)
    rcases (Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp hq_dvd_p with h
    exact hqp h

/-- For a prime `q` and nonzero `r : ZMod q`, `(1+r)·2⁻¹ ≠ (1-r)·2⁻¹`. -/
lemma split_roots_distinct (q : ℕ) [hq : Fact q.Prime] (hq_odd : q ≠ 2)
    {r : ZMod q} (hr_ne : r ≠ 0) :
    ((1 + r) * (2 : ZMod q)⁻¹) ≠ ((1 - r) * (2 : ZMod q)⁻¹) := by
  intro h_eq
  have h2_ne : (2 : ZMod q) ≠ 0 := by
    intro h2_zero
    have hq_dvd : (q : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h2_zero)
    have hq_one : 1 < q := hq.out.one_lt
    have hq_le : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd
    omega
  have h2_inv_ne : (2 : ZMod q)⁻¹ ≠ 0 := inv_ne_zero h2_ne
  -- h_eq gives (2r) · 2⁻¹ = 0 by subtraction.
  have h_2r : (2 * r : ZMod q) * (2 : ZMod q)⁻¹ = 0 := by
    have h_diff : (1 + r - (1 - r) : ZMod q) * (2 : ZMod q)⁻¹ = 0 := by
      rw [sub_mul]
      linear_combination h_eq
    have h_rewrite : (1 + r - (1 - r) : ZMod q) = 2 * r := by ring
    rw [h_rewrite] at h_diff
    exact h_diff
  have h_2r_zero : (2 * r : ZMod q) = 0 := by
    rcases mul_eq_zero.mp h_2r with h | h
    · exact h
    · exact absurd h h2_inv_ne
  rcases mul_eq_zero.mp h_2r_zero with h | h
  · exact absurd h h2_ne
  · exact absurd h hr_ne

/-- For a prime `q ≠ p, 2` with `p ≡ 3 mod 4` and `r² = -p` in `ZMod q`, the
reduction of `minpoly α mod q = X² - X + C((p+1)/4)` factors as
`(X - (1+r)·2⁻¹)(X - (1-r)·2⁻¹)`. -/
theorem alphaInOK_minpoly_factor_mod_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [hq : Fact q.Prime] (hq_odd : q ≠ 2) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q)) :
    Polynomial.map (Int.castRingHom (ZMod q)) (minpoly ℤ (alphaInOK p hp3)) =
      (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹)) *
      (Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹)) := by
  have h2_ne : (2 : ZMod q) ≠ 0 := by
    intro h2_zero
    have hq_dvd : (q : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h2_zero)
    have hq_one : 1 < q := hq.out.one_lt
    have hq_le : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd
    omega
  have h2_inv_mul : (2 : ZMod q)⁻¹ * (2 : ZMod q) = 1 := inv_mul_cancel₀ h2_ne
  rw [alphaInOK_minpoly_int_mod_q p hp3 q]
  -- Let u = (1+r)·2⁻¹, v = (1-r)·2⁻¹. Then u + v = 1, u·v = (1 - r²)/4 = (1+p)/4.
  have h_sum_uv : ((1 + r) * (2 : ZMod q)⁻¹) + ((1 - r) * (2 : ZMod q)⁻¹) = 1 := by
    have : (1 + r) * (2 : ZMod q)⁻¹ + (1 - r) * (2 : ZMod q)⁻¹ =
        2 * (2 : ZMod q)⁻¹ := by ring
    rw [this, mul_comm, h2_inv_mul]
  have h_prod_uv : ((1 + r) * (2 : ZMod q)⁻¹) * ((1 - r) * (2 : ZMod q)⁻¹) =
      (((p + 1) / 4 : ℕ) : ZMod q) := by
    have h4_inv_eq : (2 : ZMod q)⁻¹ * (2 : ZMod q)⁻¹ = (4 : ZMod q)⁻¹ := by
      have h4 : (4 : ZMod q) = 2 * 2 := by norm_num
      rw [h4, mul_inv]
    have h_step : ((1 + r) * (2 : ZMod q)⁻¹) * ((1 - r) * (2 : ZMod q)⁻¹) =
        (1 - r ^ 2) * ((2 : ZMod q)⁻¹ * (2 : ZMod q)⁻¹) := by ring
    rw [h_step, hr, h4_inv_eq]
    have h4_inv_times : (4 : ZMod q) * (((p + 1) / 4 : ℕ) : ZMod q) =
        ((p : ZMod q) + 1) := four_mul_pSuccDivFour_eq_mod_q p hp3 q
    have h4_ne : (4 : ZMod q) ≠ 0 := by
      have : (4 : ZMod q) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2_ne h2_ne
    have h_inv : (4 : ZMod q)⁻¹ * ((p : ZMod q) + 1) = (((p + 1) / 4 : ℕ) : ZMod q) := by
      rw [← h4_inv_times, ← mul_assoc, inv_mul_cancel₀ h4_ne, one_mul]
    rw [show ((1 : ZMod q) - -(p : ZMod q)) = (p : ZMod q) + 1 from by ring]
    rw [mul_comm]
    exact h_inv
  -- Expand (X - Cu)(X - Cv) = X² - C(u+v)·X + C(u·v).
  let u : ZMod q := (1 + r) * (2 : ZMod q)⁻¹
  let v : ZMod q := (1 - r) * (2 : ZMod q)⁻¹
  have h_expand : (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) =
      Polynomial.X ^ 2 - Polynomial.C (u + v) * Polynomial.X + Polynomial.C (u * v) := by
    have hC_add := (Polynomial.C_add (a := u) (b := v)).symm
    have hC_mul := (Polynomial.C_mul (a := u) (b := v)).symm
    calc (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v)
        = Polynomial.X ^ 2 - (Polynomial.C u + Polynomial.C v) * Polynomial.X +
            Polynomial.C u * Polynomial.C v := by ring
      _ = Polynomial.X ^ 2 - Polynomial.C (u + v) * Polynomial.X + Polynomial.C (u * v) := by
          rw [hC_add, hC_mul]
  rw [h_expand, h_sum_uv, h_prod_uv, Polynomial.C_1, one_mul]

/-- Helper: in the split case, `r ≠ 0` when `-p ≠ 0` in `ZMod q`. -/
lemma split_r_ne_zero (q : ℕ) [Fact q.Prime] (hqp : q ≠ p)
    {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q)) : r ≠ 0 := by
  intro hr_zero
  rw [hr_zero, zero_pow two_ne_zero] at hr
  have h_neg_p_zero : -(p : ZMod q) = 0 := hr.symm
  rw [neg_eq_zero] at h_neg_p_zero
  have hq_dvd : (q : ℕ) ∣ p :=
    (ZMod.natCast_eq_zero_iff p q).mp (by exact_mod_cast h_neg_p_zero)
  rcases (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp.out).mp hq_dvd with h
  exact hqp h

/-- For `q ≠ p, 2` with `r² = -p` in `ZMod q`, `monicFactorsMod α q` has 2 elements. -/
theorem monicFactorsMod_alpha_at_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q)) :
    RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q =
      {Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹),
       Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹)} := by
  classical
  have hr_ne : r ≠ 0 := split_r_ne_zero p q hqp hr
  have h_distinct : ((1 + r) * (2 : ZMod q)⁻¹) ≠ ((1 - r) * (2 : ZMod q)⁻¹) :=
    split_roots_distinct q hq_odd hr_ne
  unfold RingOfIntegers.monicFactorsMod
  rw [alphaInOK_minpoly_factor_mod_q_split p hp3 q hq_odd hr]
  have hu_ne_zero : (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)) ≠ 0 := (Polynomial.monic_X_sub_C _).ne_zero
  have hv_ne_zero : (Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)) ≠ 0 := (Polynomial.monic_X_sub_C _).ne_zero
  have hu_irred : Irreducible (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)) := Polynomial.irreducible_X_sub_C _
  have hv_irred : Irreducible (Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)) := Polynomial.irreducible_X_sub_C _
  have hu_monic : (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)).Monic := Polynomial.monic_X_sub_C _
  have hv_monic : (Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) :
      Polynomial (ZMod q)).Monic := Polynomial.monic_X_sub_C _
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hu_ne_zero hv_ne_zero]
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hu_irred,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hv_irred,
    hu_monic.normalize_eq_self, hv_monic.normalize_eq_self]
  ext x
  simp only [Multiset.toFinset_add, Finset.mem_union, Multiset.toFinset_singleton,
    Finset.mem_singleton, Finset.mem_insert]

/-- A root of `X² - X + C c` in a field `F` gives a square root of `1 - 4c`. -/
lemma root_of_quadratic_gives_sqrt {F : Type*} [Field F] (c : F) {a : F}
    (ha : a ^ 2 - a + c = 0) :
    (2 * a - 1) ^ 2 = 1 - 4 * c := by
  linear_combination 4 * ha

/-- If `1 - 4c` is not a square in a field `F` of characteristic ≠ 2, then
`X² - X + C c` is irreducible over `F`. -/
lemma irreducible_quadratic_of_not_sqrt {F : Type*} [Field F] (_h2_ne : (2 : F) ≠ 0) (c : F)
    (h_not_sq : ∀ s : F, s ^ 2 ≠ 1 - 4 * c) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c : Polynomial F) := by
  have h_deg : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c : Polynomial F).natDegree = 2 := by
    compute_degree!
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [h_deg]; decide
  · intro a ha
    rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at ha
    exact h_not_sq (2 * a - 1) (root_of_quadratic_gives_sqrt c ha)

/-- For `q ≠ p, 2` with `-p` NOT a square in `ZMod q`, the minpoly of α mod q is
irreducible, so `monicFactorsMod α q = {minpoly α mod q}` (singleton). -/
theorem monicFactorsMod_alpha_at_q_inert (hp3 : p % 4 = 3) (q : ℕ)
    [hq : Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q)) :
    RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q =
      {Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q)} := by
  classical
  have h2_ne : (2 : ZMod q) ≠ 0 := by
    intro h2_zero
    have hq_dvd : (q : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h2_zero)
    have hq_one : 1 < q := hq.out.one_lt
    have hq_le : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd
    omega
  -- Show 1 - 4·(p+1)/4 = -p mod q, and convert h_not_sq to the form needed.
  have h_disc : (1 : ZMod q) - 4 * (((p + 1) / 4 : ℕ) : ZMod q) = -(p : ZMod q) := by
    rw [four_mul_pSuccDivFour_eq_mod_q p hp3 q]; ring
  have h_not_sq' : ∀ s : ZMod q, s ^ 2 ≠ 1 - 4 * (((p + 1) / 4 : ℕ) : ZMod q) := by
    intro s
    rw [h_disc]; exact h_not_sq s
  have h_irred : Irreducible (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) : Polynomial (ZMod q)) :=
    irreducible_quadratic_of_not_sqrt h2_ne _ h_not_sq'
  have h_monic : (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) : Polynomial (ZMod q)).Monic := by
    have h_eq : Polynomial.X ^ 2 - Polynomial.X +
        Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) =
        Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q)) := by
      ring
    rw [h_eq]
    refine Polynomial.monic_X_pow_add ?_
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    rw [Polynomial.degree_neg, Polynomial.degree_X]
    refine lt_of_le_of_lt ?_ (by decide : (1 : WithBot ℕ) < 2)
    refine max_le (le_refl _) ?_
    exact (Polynomial.degree_C_le).trans (by decide)
  unfold RingOfIntegers.monicFactorsMod
  rw [alphaInOK_minpoly_int_mod_q p hp3 q]
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred,
    h_monic.normalize_eq_self]
  simp

/-- For `q ≠ p, 2` with `-p` NOT a square in `ZMod q`, cardinality of
`monicFactorsMod α q` is 1. -/
theorem monicFactorsMod_alpha_at_q_inert_card (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q)) :
    (RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q).card = 1 := by
  rw [monicFactorsMod_alpha_at_q_inert p hp3 q hq_odd hqp h_not_sq]
  simp

/-- For the split case at `q`, cardinality of `monicFactorsMod α q` is 2. -/
theorem monicFactorsMod_alpha_at_q_split_card (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q)) :
    (RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q).card = 2 := by
  classical
  have hr_ne : r ≠ 0 := split_r_ne_zero p q hqp hr
  have h_distinct : ((1 + r) * (2 : ZMod q)⁻¹) ≠ ((1 - r) * (2 : ZMod q)⁻¹) :=
    split_roots_distinct q hq_odd hr_ne
  rw [monicFactorsMod_alpha_at_q_split p hp3 q hq_odd hqp hr]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simp only [Finset.mem_singleton]
  intro h
  apply h_distinct
  have h_sub : Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) -
      Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) = 0 := by
    have : Polynomial.X - Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) -
        (Polynomial.X - Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹)) =
        Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) -
          Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) := by ring
    rw [← this, h]; ring
  have h_neg : Polynomial.C ((1 + r) * (2 : ZMod q)⁻¹) =
               Polynomial.C ((1 - r) * (2 : ZMod q)⁻¹) := sub_eq_zero.mp h_sub
  exact Polynomial.C_injective h_neg

/-- Number of primes above `q` (q ≠ p, 2) in split case: 2. -/
theorem ncard_primesOver_at_q_split (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p) {r : ZMod q} (hr : r ^ 2 = -(p : ZMod q)) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))).ncard = 2 := by
  classical
  have h_exp : ¬ (q : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 q
  have h_equiv :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  rw [← Nat.card_coe_set_eq, Nat.card_congr h_equiv, Nat.card_eq_finsetCard,
    monicFactorsMod_alpha_at_q_split_card p hp3 q hq_odd hqp hr]

/-- Number of primes above `q` (q ≠ p, 2) in inert case: 1. -/
theorem ncard_primesOver_at_q_inert (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q)) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))).ncard = 1 := by
  classical
  have h_exp : ¬ (q : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 q
  have h_equiv :=
    NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  rw [← Nat.card_coe_set_eq, Nat.card_congr h_equiv, Nat.card_eq_finsetCard,
    monicFactorsMod_alpha_at_q_inert_card p hp3 q hq_odd hqp h_not_sq]

/-- In the inert case at `q ≠ p, 2`, the unique prime has inertia degree 2. -/
theorem inertiaDeg_at_q_inert (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q))
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) :
    (Ideal.span {(q : ℤ)}).inertiaDeg P = 2 := by
  classical
  have h_exp : ¬ (q : ℕ) ∣ RingOfIntegers.exponent (alphaInOK p hp3) :=
    not_dvd_exponent_alphaInOK p hp3 q
  set e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (K := Kminus p) h_exp
  set Qfactor : Polynomial (ZMod q) :=
    Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q)
  have hQ_mem : Qfactor ∈ RingOfIntegers.monicFactorsMod (alphaInOK p hp3) q := by
    rw [monicFactorsMod_alpha_at_q_inert p hp3 q hq_odd hqp h_not_sq]
    exact Finset.mem_singleton.mpr rfl
  have hP_eq : P = (e.symm ⟨Qfactor, hQ_mem⟩ : Ideal (𝓞 (Kminus p))) := by
    have h_sub : Subsingleton ↥(Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) := by
      have h_card := ncard_primesOver_at_q_inert p hp3 q hq_odd hqp h_not_sq
      rw [Set.ncard_eq_one] at h_card
      obtain ⟨x, hx⟩ := h_card
      refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
      have ha_eq : a = x := by rw [hx] at ha; exact ha
      have hb_eq : b = x := by rw [hx] at hb; exact hb
      subst ha_eq; subst hb_eq; rfl
    have hP_set : (⟨P, hP⟩ : ↥(Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)))) =
                  e.symm ⟨Qfactor, hQ_mem⟩ := h_sub.elim _ _
    exact congrArg (fun (x : ↥(Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p)))) =>
      (x : Ideal (𝓞 (Kminus p)))) hP_set
  rw [hP_eq]
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      h_exp hQ_mem]
  -- Qfactor has natDegree 2.
  change (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) : Polynomial (ZMod q)).natDegree = 2
  have h_monic : (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) : Polynomial (ZMod q)).Monic := by
    have h_eq : Polynomial.X ^ 2 - Polynomial.X +
        Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) =
        Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q)) := by
      ring
    rw [h_eq]
    refine Polynomial.monic_X_pow_add ?_
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
    rw [Polynomial.degree_neg, Polynomial.degree_X]
    refine lt_of_le_of_lt ?_ (by decide : (1 : WithBot ℕ) < 2)
    refine max_le (le_refl _) ?_
    exact (Polynomial.degree_C_le).trans (by decide)
  -- Now use Monic + degree_X_pow_add → natDegree = 2.
  have h_deg : (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) : Polynomial (ZMod q)).natDegree = 2 := by
    have h_eq : Polynomial.X ^ 2 - Polynomial.X +
        Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q) =
        Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ZMod q)) := by
      ring
    rw [h_eq]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 2
    · rw [Polynomial.natDegree_X_pow]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_neg, Polynomial.natDegree_X, Polynomial.natDegree_C]
      decide
  exact h_deg

/-- In the inert case at `q ≠ p, 2`, the absolute norm of the unique prime is `q²`. -/
theorem absNorm_primeOver_at_q_inert (hp3 : p % 4 = 3) (q : ℕ)
    [Fact q.Prime] (hq_odd : q ≠ 2) (hqp : q ≠ p)
    (h_not_sq : ∀ s : ZMod q, s ^ 2 ≠ -(p : ZMod q))
    (P : Ideal (𝓞 (Kminus p)))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 (Kminus p))) :
    Ideal.absNorm P = q ^ 2 := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hP.2
  have h_ine : (Ideal.span {(q : ℤ)}).inertiaDeg P = 2 :=
    inertiaDeg_at_q_inert p hp3 q hq_odd hqp h_not_sq P hP
  calc Ideal.absNorm P
      = q ^ ((Ideal.span {(q : ℤ)}).inertiaDeg P) :=
        Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : q.Prime)
    _ = q ^ 2 := by rw [h_ine]

end CN05_statement

end BernoulliRegular
