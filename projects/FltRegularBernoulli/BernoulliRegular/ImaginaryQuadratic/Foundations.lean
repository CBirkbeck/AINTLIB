module

public import BernoulliRegular.CompletedDedekindZeta
public import BernoulliRegular.LFunctionPositive
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Imaginary quadratic field `ℚ(√-p)` — abstract setup

For `p ≡ 3 (mod 4)` prime, the imaginary quadratic field `K = ℚ(√-p)` has:

* discriminant `|d_K| = p`
* signature `r₁ = 0, r₂ = 1`
* regulator `Reg_K = 1` (imag quadratic has trivial unit rank)
* torsion unit order `w = 2` (for `p > 3`)

By the analytic class number formula:
  `L(legendreDirichlet p, 1) = π · h(-p) / √p`   (for `p > 3`)

This file sets up the ABSTRACT typeclass framework for `K = ℚ(√-p)` and records
the classical identities. Concrete instance construction (e.g., via `Zsqrtd` or
`Polynomial.SplittingField (X² + p)`) is deferred; this file works abstractly
with any `K` satisfying the `IsImaginaryQuadraticOfPrime p` typeclass defined
here.

## Main definitions

* `IsImaginaryQuadraticOfPrime p K`: typeclass asserting that `K` is a number
  field realizing `ℚ(√-p)`, i.e., degree 2 totally imaginary with discriminant
  of absolute value `p`.

## Main results (to be added)

* `ζ_K(s) = ζ(s) · L(legendreDirichlet p, s)` — Dedekind factorization.
* Residue formula → `L(legendreDirichlet p, 1) = π · h(-p) / √p`.

## References

* Borevich–Shafarevich, *Number Theory*, §4.
* Lang, *Algebraic Number Theory*, Ch XIII.
-/

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

/-- A number field `K` is `IsImaginaryQuadraticOfPrime p` if it is isomorphic
(as a number field) to `ℚ(√-p)` for `p ≡ 3 (mod 4)` prime. Concretely:

* `[K : ℚ] = 2`
* `K` is totally imaginary (`r₁ = 0`)
* `|disc K| = p`

For `p > 3`, the torsion unit group has order `2`. -/
class IsImaginaryQuadraticOfPrime (p : ℕ) (K : Type*) [Field K] [NumberField K] : Prop where
  /-- Degree over ℚ is 2. -/
  finrank_eq_two : Module.finrank ℚ K = 2
  /-- Totally imaginary: no real embeddings. -/
  nrRealPlaces_eq_zero : InfinitePlace.nrRealPlaces K = 0
  /-- Absolute discriminant is `p`. -/
  absDiscr_eq : (discr K).natAbs = p

/-- For `K = ℚ(√-p)` (an imaginary quadratic of prime discriminant `p`), the
number of complex embeddings (pairs) is `1`. -/
lemma nrComplexPlaces_eq_one (p : ℕ) (K : Type*) [Field K] [NumberField K]
    [h : IsImaginaryQuadraticOfPrime p K] :
    InfinitePlace.nrComplexPlaces K = 1 := by
  have h_sum := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [h.nrRealPlaces_eq_zero, h.finrank_eq_two] at h_sum
  omega

/-! ### Concrete construction via `Polynomial.SplittingField` -/

section ConcreteConstruction

variable (p : ℕ) [hp : Fact p.Prime]

/-- The polynomial `X² + p` over `ℚ`. This is irreducible (since `p > 0` and
has no rational square root as a nonzero natural). For `p ≡ 3 mod 4`, its
splitting field is `ℚ(√-p)`. -/
noncomputable def sqPlusPrime : Polynomial ℚ :=
  Polynomial.X ^ 2 + Polynomial.C (p : ℚ)

omit hp in
/-- `sqPlusPrime p` is monic (leading coefficient `1`). -/
lemma sqPlusPrime_monic : (sqPlusPrime p).Monic :=
  Polynomial.monic_X_pow_add_C (p : ℚ) (by norm_num : (2 : ℕ) ≠ 0)

omit hp in
/-- The natural degree of `X² + p` is `2`. -/
lemma sqPlusPrime_natDegree : (sqPlusPrime p).natDegree = 2 := by
  rw [sqPlusPrime]
  have h_deg : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ) : Polynomial ℚ).natDegree = 2 := by
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 2
    · rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
      omega
  exact h_deg

/-- `X² + p` has no rational root for `p > 0` (since `-p` is not a rational square). -/
lemma sqPlusPrime_no_root (q : ℚ) : ¬ (sqPlusPrime p).IsRoot q := by
  intro h_root
  unfold sqPlusPrime at h_root
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at h_root
  -- q^2 + p = 0 ⟹ q^2 = -p. But q^2 ≥ 0 and -p < 0. Contradiction.
  have h_q_sq_eq : q ^ 2 = -(p : ℚ) := by linarith
  have h_q_sq_nonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have h_neg_p_lt_zero : -(p : ℚ) < 0 := by
    have : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
    linarith
  rw [h_q_sq_eq] at h_q_sq_nonneg
  linarith

/-- `X² + p` is irreducible over `ℚ` (since it has no rational root and degree 2). -/
lemma sqPlusPrime_irreducible : Irreducible (sqPlusPrime p) := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
    (sqPlusPrime_natDegree p).ge (by rw [sqPlusPrime_natDegree]; omega)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro q hq
  rw [Polynomial.mem_roots (sqPlusPrime_monic p).ne_zero] at hq
  exact sqPlusPrime_no_root p q hq

/-- `Fact` instance for `sqPlusPrime p` irreducible. -/
instance sqPlusPrime_fact_irreducible : Fact (Irreducible (sqPlusPrime p)) :=
  ⟨sqPlusPrime_irreducible p⟩

/-- The imaginary quadratic field `ℚ(√-p)`, realized as `AdjoinRoot (X² + p)`
over `ℚ`. Since `X² + p` is monic irreducible of degree 2, this is a field
of dimension 2 over `ℚ`. -/
abbrev Kminus : Type := AdjoinRoot (sqPlusPrime p)

-- `NumberField (AdjoinRoot f)` instance provided by mathlib for any irreducible
-- `f : Polynomial ℚ` via `AdjoinRoot.instNumberFieldRat`.

/-- `[Kminus p : ℚ] = 2`. -/
theorem finrank_Kminus : Module.finrank ℚ (Kminus p) = 2 := by
  have h := (AdjoinRoot.powerBasis (sqPlusPrime_monic p).ne_zero (f := sqPlusPrime p)).finrank
  rw [h, AdjoinRoot.powerBasis_dim, sqPlusPrime_natDegree]

/-- For `p > 0` prime, `X² + p` has no real roots. -/
lemma sqPlusPrime_no_real_root (x : ℝ) : ¬ (Polynomial.aeval x (sqPlusPrime p) = 0) := by
  intro h
  unfold sqPlusPrime at h
  simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    eq_ratCast, Rat.cast_natCast] at h
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

/-- No ring homomorphism `Kminus p → ℝ` exists (since `Kminus p` contains a
square root of `-p`, and `-p < 0` in `ℝ`). -/
lemma no_real_ringHom (ψ : Kminus p →+* ℝ) : False := by
  -- Convert ψ to a ℚ-algebra hom, then apply AdjoinRoot.aeval_algHom_eq_zero.
  set ϕ : Kminus p →ₐ[ℚ] ℝ := ψ.toRatAlgHom
  have h_root : Polynomial.aeval (ϕ (AdjoinRoot.root (sqPlusPrime p))) (sqPlusPrime p) = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero (sqPlusPrime p) ϕ
  exact sqPlusPrime_no_real_root p _ h_root

/-- No complex embedding of `Kminus p` into `ℂ` is real. -/
lemma no_real_embedding (φ : Kminus p →+* ℂ) : ¬ NumberField.ComplexEmbedding.IsReal φ := fun h ↦
  no_real_ringHom p h.embedding

/-- Every infinite place of `Kminus p` is complex (not real). -/
lemma isTotallyComplex_Kminus : NumberField.IsTotallyComplex (Kminus p) := by
  refine ⟨fun v ↦ ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro h_real
  obtain ⟨φ, h_φ_real, _⟩ := h_real
  exact no_real_embedding p φ h_φ_real

/-- `nrRealPlaces (Kminus p) = 0`. -/
theorem nrRealPlaces_Kminus : NumberField.InfinitePlace.nrRealPlaces (Kminus p) = 0 :=
  NumberField.nrRealPlaces_eq_zero_iff.mpr (isTotallyComplex_Kminus p)

end ConcreteConstruction

/-! ### CN-03 foundations: the element `α = (1 + √-p)/2` and its integrality

For `p ≡ 3 (mod 4)` prime, the ring of integers of `ℚ(√-p)` is `ℤ[α]` where
`α = (1 + √-p)/2`. This element satisfies the monic integer polynomial
`X² - X + (p+1)/4`, and the ring `ℤ[α]` has discriminant `-p`.

This section sets up the basic lemmas: the defining relations for `√-p`, the
element `α`, and its integrality over `ℤ`. The final identification of
`ℤ[α]` with the full ring of integers is in `section RingOfIntegers` below. -/
section DiscriminantFoundations

variable (p : ℕ) [hp : Fact p.Prime]

/-- The canonical square root of `-p` in `Kminus p`, as the root of `X² + p`. -/
noncomputable abbrev sqrtNegP : Kminus p := AdjoinRoot.root (sqPlusPrime p)

/-- `(√-p)² = -p` in `Kminus p`. -/
lemma sqrtNegP_sq : sqrtNegP p ^ 2 = -(p : Kminus p) := by
  have h : sqrtNegP p ^ 2 + (p : Kminus p) = 0 := by
    have h1 : (sqPlusPrime p).eval₂ (AdjoinRoot.of (sqPlusPrime p))
        (AdjoinRoot.root (sqPlusPrime p)) = 0 := AdjoinRoot.eval₂_root _
    -- Evaluate the concrete polynomial `X² + C p`, keeping `sqPlusPrime p`
    -- folded inside the ring-hom arguments (it carries the `Fact Irreducible`
    -- instance, so it must not be rewritten there).
    have h2 : (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)).eval₂
          (AdjoinRoot.of (sqPlusPrime p)) (AdjoinRoot.root (sqPlusPrime p)) =
        sqrtNegP p ^ 2 + (p : Kminus p) := by
      rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
        map_natCast]
    rw [← h2]
    exact h1
  linear_combination h

/-- The element `(1 + √-p)/2` in `Kminus p`. For `p ≡ 3 (mod 4)`, this is a
generator of the ring of integers. -/
noncomputable def halfOnePlusSqrtNegP : Kminus p := (1 + sqrtNegP p) / 2

local notation "α" => halfOnePlusSqrtNegP p

/-- Key identity: `2α - 1 = √-p` in `Kminus p`. -/
lemma two_halfOnePlusSqrtNegP_sub_one : 2 * α - 1 = sqrtNegP p := by
  change 2 * ((1 + sqrtNegP p) / 2) - 1 = sqrtNegP p
  have h2 : (2 : Kminus p) ≠ 0 := two_ne_zero
  rw [mul_div_cancel₀ _ h2]
  ring

/-- The defining relation: `4α² - 4α + 1 = -p` in `Kminus p`. -/
lemma four_halfOnePlusSqrtNegP_sq_minus_four_alpha_plus_one :
    4 * α ^ 2 - 4 * α + 1 = -(p : Kminus p) := by
  have h1 : (2 * α - 1) ^ 2 = sqrtNegP p ^ 2 := by
    rw [two_halfOnePlusSqrtNegP_sub_one]
  rw [sqrtNegP_sq] at h1
  linear_combination h1

omit hp in
/-- Under `p ≡ 3 (mod 4)`, we have `4 ∣ p + 1`. -/
lemma four_dvd_succ_of_three_mod_four (hp3 : p % 4 = 3) : 4 ∣ p + 1 := by
  omega

/-- For `p ≡ 3 (mod 4)`: `α² - α + (p+1)/4 = 0` in `Kminus p`. This is the minimal
polynomial relation with integer coefficients. -/
lemma halfOnePlusSqrtNegP_minpoly_relation (hp3 : p % 4 = 3) :
    α ^ 2 - α + ((p + 1) / 4 : ℕ) = 0 := by
  have h4 := four_halfOnePlusSqrtNegP_sq_minus_four_alpha_plus_one p
  have hdvd : 4 ∣ p + 1 := four_dvd_succ_of_three_mod_four p hp3
  have hcast : (((p + 1) / 4 : ℕ) * 4 : Kminus p) = ((p + 1 : ℕ) : Kminus p) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  have key : 4 * (α ^ 2 - α + ((p + 1) / 4 : ℕ)) = 0 := by
    have hpush : ((p + 1 : ℕ) : Kminus p) = (p : Kminus p) + 1 := by push_cast; ring
    rw [hpush] at hcast
    linear_combination h4 + hcast
  have h4_ne : (4 : Kminus p) ≠ 0 := by
    have : (4 : ℚ) ≠ 0 := by norm_num
    exact_mod_cast this
  have := mul_left_cancel₀ h4_ne (key.trans (mul_zero 4).symm)
  exact this

/-- For `p ≡ 3 (mod 4)`, the element `α = (1 + √-p)/2` is integral over `ℤ`,
with monic minimal polynomial `X² - X + (p+1)/4`. -/
lemma halfOnePlusSqrtNegP_isIntegral (hp3 : p % 4 = 3) :
    IsIntegral ℤ (halfOnePlusSqrtNegP p) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℤ), ?_, ?_⟩
  · -- Monic: rewrite as `X^2 - (X - C c)`, then use `monic_X_pow_sub`.
    have heq :
        (Polynomial.X ^ 2 - Polynomial.X +
          Polynomial.C (((p + 1) / 4 : ℕ) : ℤ) : Polynomial ℤ) =
        Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C (((p + 1) / 4 : ℕ) : ℤ)) := by
      ring
    rw [heq]
    exact Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X_sub_C]; decide)
  · -- aeval = 0 via the minimal polynomial relation.
    change Polynomial.aeval (halfOnePlusSqrtNegP p)
      (Polynomial.X ^ 2 - Polynomial.X +
        Polynomial.C (((p + 1) / 4 : ℕ) : ℤ)) = 0
    rw [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    have h := halfOnePlusSqrtNegP_minpoly_relation p hp3
    convert h using 3
    rw [map_natCast]

/-- The element `α = (1 + √-p)/2` is integral over `ℚ` (consequence of integrality
over `ℤ`). -/
lemma halfOnePlusSqrtNegP_isIntegral_rat (hp3 : p % 4 = 3) :
    IsIntegral ℚ (halfOnePlusSqrtNegP p) :=
  (halfOnePlusSqrtNegP_isIntegral p hp3).tower_top

/-- `α = (1 + √-p)/2` generates `Kminus p` over `ℚ`: `ℚ[α] = ⊤`. -/
lemma adjoin_halfOnePlusSqrtNegP_eq_top :
    Algebra.adjoin ℚ ({halfOnePlusSqrtNegP p} : Set (Kminus p)) = ⊤ := by
  apply top_le_iff.mp
  calc (⊤ : Subalgebra ℚ (Kminus p))
      = Algebra.adjoin ℚ ({sqrtNegP p} : Set (Kminus p)) :=
          AdjoinRoot.adjoinRoot_eq_top.symm
    _ ≤ Algebra.adjoin ℚ ({halfOnePlusSqrtNegP p} : Set (Kminus p)) := by
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        change sqrtNegP p ∈ Algebra.adjoin ℚ ({halfOnePlusSqrtNegP p} : Set (Kminus p))
        have hα := Algebra.self_mem_adjoin_singleton ℚ (halfOnePlusSqrtNegP p)
        rw [show sqrtNegP p = 2 * halfOnePlusSqrtNegP p - 1 from
          (two_halfOnePlusSqrtNegP_sub_one p).symm]
        exact sub_mem (mul_mem (Subalgebra.natCast_mem _ 2) hα) (one_mem _)

/-- The `ℚ`-power basis of `Kminus p` generated by `α = (1 + √-p)/2`. -/
noncomputable def alphaPowerBasis (hp3 : p % 4 = 3) : PowerBasis ℚ (Kminus p) :=
  PowerBasis.ofAdjoinEqTop
    (halfOnePlusSqrtNegP_isIntegral_rat p hp3)
    (adjoin_halfOnePlusSqrtNegP_eq_top p)

/-- The generator of the `α`-power basis is `α`. -/
lemma alphaPowerBasis_gen (hp3 : p % 4 = 3) :
    (alphaPowerBasis p hp3).gen = halfOnePlusSqrtNegP p := rfl

/-- The `α`-power basis of `Kminus p` has dimension `2`. -/
lemma alphaPowerBasis_dim (hp3 : p % 4 = 3) : (alphaPowerBasis p hp3).dim = 2 := by
  have h1 : Module.finrank ℚ (Kminus p) = (alphaPowerBasis p hp3).dim :=
    (alphaPowerBasis p hp3).finrank
  rw [finrank_Kminus] at h1
  exact h1.symm

/-- The minimal polynomial of `α = (1 + √-p)/2` over `ℚ` is `X² - X + (p+1)/4`.
Proof: both polynomials are monic, divide each other (via `minpoly.dvd` and `α²-α+c=0`),
and have the same degree `2` (via `PowerBasis.ofAdjoinEqTop_dim`). -/
lemma halfOnePlusSqrtNegP_minpoly (hp3 : p % 4 = 3) :
    minpoly ℚ (halfOnePlusSqrtNegP p) =
      Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℚ) := by
  set q : Polynomial ℚ :=
    Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (((p + 1) / 4 : ℕ) : ℚ) with hq_def
  -- `q` is monic with natDegree `2`.
  have hq_eq :
      q = Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C (((p + 1) / 4 : ℕ) : ℚ)) := by
    rw [hq_def]; ring
  have hq_monic : q.Monic := by
    rw [hq_eq]; exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X_sub_C]; decide)
  have hq_aeval : Polynomial.aeval (halfOnePlusSqrtNegP p) q = 0 := by
    rw [hq_def, map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    have h := halfOnePlusSqrtNegP_minpoly_relation p hp3
    simpa using h
  have hq_natDeg : q.natDegree = 2 := by
    rw [hq_eq, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · exact Polynomial.natDegree_X_pow 2
    · rw [Polynomial.natDegree_X_pow]
      exact lt_of_le_of_lt (Polynomial.natDegree_X_sub_C_le _) (by decide)
  -- `minpoly ℚ α` has natDegree `2` via the power basis.
  have hmp_natDeg : (minpoly ℚ (halfOnePlusSqrtNegP p)).natDegree = 2 := by
    have h1 : (alphaPowerBasis p hp3).dim =
        (minpoly ℚ (halfOnePlusSqrtNegP p)).natDegree :=
      PowerBasis.ofAdjoinEqTop_dim _ _
    rw [alphaPowerBasis_dim] at h1
    exact h1.symm
  have hmp_monic : (minpoly ℚ (halfOnePlusSqrtNegP p)).Monic :=
    minpoly.monic (halfOnePlusSqrtNegP_isIntegral_rat p hp3)
  have h_dvd : minpoly ℚ (halfOnePlusSqrtNegP p) ∣ q :=
    minpoly.dvd _ _ hq_aeval
  -- Both monic of same natDegree implies equal.
  obtain ⟨c, hc⟩ := h_dvd
  have hc_monic : c.Monic := Polynomial.Monic.of_mul_monic_left hmp_monic (hc ▸ hq_monic)
  have hsum : (minpoly ℚ (halfOnePlusSqrtNegP p)).natDegree + c.natDegree = 2 := by
    rw [← Polynomial.natDegree_mul hmp_monic.ne_zero hc_monic.ne_zero, ← hc, hq_natDeg]
  have hc_deg : c.natDegree = 0 := by omega
  have hc_eq : c = 1 := hc_monic.natDegree_eq_zero.mp hc_deg
  rw [hc, hc_eq, mul_one]

/-- The `AdjoinRoot`-power basis of `Kminus p` with generator `√-p`. -/
noncomputable def sqrtNegPPowerBasis : PowerBasis ℚ (Kminus p) :=
  AdjoinRoot.powerBasis (sqPlusPrime_monic p).ne_zero

lemma sqrtNegPPowerBasis_gen : (sqrtNegPPowerBasis p).gen = sqrtNegP p := rfl

lemma sqrtNegPPowerBasis_dim : (sqrtNegPPowerBasis p).dim = 2 := by
  rw [sqrtNegPPowerBasis, AdjoinRoot.powerBasis_dim, sqPlusPrime_natDegree]

/-- The minimal polynomial of `√-p` over `ℚ` is `X² + p`. -/
lemma sqrtNegP_minpoly : minpoly ℚ (sqrtNegP p) = sqPlusPrime p := by
  have h := AdjoinRoot.minpoly_root (f := sqPlusPrime p) (sqPlusPrime_monic p).ne_zero
  rw [(sqPlusPrime_monic p).leadingCoeff, inv_one, Polynomial.C_1, mul_one] at h
  exact h

/-- `norm ℚ (√-p) = p`. -/
lemma norm_sqrtNegP : Algebra.norm ℚ (sqrtNegP p) = (p : ℚ) := by
  have h1 : Algebra.norm ℚ (sqrtNegPPowerBasis p).gen =
      (-1) ^ (sqrtNegPPowerBasis p).dim * (minpoly ℚ (sqrtNegPPowerBasis p).gen).coeff 0 :=
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (sqrtNegPPowerBasis p)
  rw [sqrtNegPPowerBasis_gen, sqrtNegPPowerBasis_dim, sqrtNegP_minpoly] at h1
  rw [h1, sqPlusPrime]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow]

/-- α = (1 + √-p)/2 as an element of the ring of integers of `Kminus p`. -/
noncomputable def alphaInOK (hp3 : p % 4 = 3) : 𝓞 (Kminus p) :=
  ⟨halfOnePlusSqrtNegP p, halfOnePlusSqrtNegP_isIntegral p hp3⟩

/-- The cardinality of the choose-basis-index of `𝓞 (Kminus p)` is 2. -/
lemma card_chooseBasisIndex_Kminus :
    Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 (Kminus p))) = 2 := by
  rw [← Module.finrank_eq_card_chooseBasisIndex ℤ (𝓞 (Kminus p)),
    NumberField.RingOfIntegers.rank, finrank_Kminus]

/-- The discriminant of the ℚ-power basis of `Kminus p` generated by `α = (1+√-p)/2`
is `-p`. -/
lemma discr_alphaPowerBasis (hp3 : p % 4 = 3) :
    Algebra.discr ℚ (alphaPowerBasis p hp3).basis = -(p : ℚ) := by
  -- Use the norm formula and compute the derivative evaluation.
  rw [Algebra.discr_powerBasis_eq_norm ℚ (alphaPowerBasis p hp3)]
  rw [finrank_Kminus]
  -- Now: (-1)^(2*(2-1)/2) * norm ℚ (aeval α (derivative minpoly))
  --    = (-1)^1 * norm ℚ (2α - 1) = -norm ℚ (sqrtNegP p) = -p
  have hmp : minpoly ℚ (alphaPowerBasis p hp3).gen = Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ℚ) := by
    rw [alphaPowerBasis_gen]; exact halfOnePlusSqrtNegP_minpoly p hp3
  rw [hmp]
  -- derivative X^2 - X + C c = 2X - 1
  have hderiv : Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X +
      Polynomial.C (((p + 1) / 4 : ℕ) : ℚ)) =
      2 * Polynomial.X - 1 := by
    simp [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_X]
    ring
  rw [hderiv]
  -- aeval α (2X - 1) = 2α - 1 = sqrtNegP p
  rw [map_sub, map_mul, map_ofNat, Polynomial.aeval_X, map_one]
  rw [alphaPowerBasis_gen]
  rw [show (2 : Kminus p) * halfOnePlusSqrtNegP p - 1 = sqrtNegP p from
    two_halfOnePlusSqrtNegP_sub_one p]
  rw [norm_sqrtNegP]
  -- Compute (-1)^(2*1/2) = -1, so answer = -p
  norm_num

/-- The `α`-power basis elements are integral over `ℤ`. -/
lemma alphaPowerBasis_basis_isIntegral (hp3 : p % 4 = 3) :
    ∀ j : Fin (alphaPowerBasis p hp3).dim, IsIntegral ℤ ((alphaPowerBasis p hp3).basis j) := by
  intro j
  rw [(alphaPowerBasis p hp3).basis_eq_pow]
  have hα : IsIntegral ℤ (halfOnePlusSqrtNegP p) := halfOnePlusSqrtNegP_isIntegral p hp3
  have : (alphaPowerBasis p hp3).gen = halfOnePlusSqrtNegP p := rfl
  rw [this]
  exact hα.pow _

/-- **CN-03**: the absolute discriminant of `Kminus p` has `natAbs = p`, for
`p ≡ 3 (mod 4)` prime.

Strategy: using `Algebra.discr ℚ (alphaPowerBasis.basis) = -p` and the fact
that the α-power basis elements are in 𝓞, we can write
`α-basis = (P_int.map (algebraMap ℚ K)).vecMul iB` for some integer matrix
P_int. By `Algebra.discr_of_matrix_vecMul`, `-p = P_int.det² · disc K`.
Since `p` is prime (not a perfect square) and `disc K ≠ 0`, we conclude
`P_int.det² = 1` and `natAbs(disc K) = p`. -/
theorem discr_Kminus_natAbs_eq (hp3 : p % 4 = 3) :
    (NumberField.discr (Kminus p)).natAbs = p := by
  classical
  haveI : IsScalarTower ℤ (𝓞 (Kminus p)) (Kminus p) := inferInstance
  set pb := alphaPowerBasis p hp3 with hpb_def
  have hdim : pb.dim = 2 := alphaPowerBasis_dim p hp3
  -- Fin 2 ≃ ChooseBasisIndex for 𝓞 (Kminus p).
  let e : Fin 2 ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 (Kminus p)) :=
    (Fintype.equivFinOfCardEq (card_chooseBasisIndex_Kminus p)).symm
  -- Bases indexed by Fin 2.
  let pbBas : Module.Basis (Fin 2) ℚ (Kminus p) := pb.basis.reindex (finCongr hdim)
  let iB : Module.Basis (Fin 2) ℚ (Kminus p) :=
    (NumberField.integralBasis (Kminus p)).reindex e.symm
  -- Discriminants of the reindexed bases.
  have h_pbBas_disc : Algebra.discr ℚ pbBas = -(p : ℚ) := by
    have h1 : (pbBas : Fin 2 → Kminus p) = pb.basis ∘ (finCongr hdim).symm := by
      funext j; simp [pbBas]
    rw [h1, Algebra.discr_reindex]
    exact discr_alphaPowerBasis p hp3
  have h_iB_disc : Algebra.discr ℚ iB = (NumberField.discr (Kminus p) : ℚ) := by
    have h1 : (iB : Fin 2 → Kminus p) = NumberField.integralBasis (Kminus p) ∘ e := by
      funext i; simp [iB]
    rw [h1]
    have h2 : Algebra.discr ℚ (NumberField.integralBasis (Kminus p) ∘ e) =
        Algebra.discr ℚ (NumberField.integralBasis (Kminus p)) := by
      have := Algebra.discr_reindex ℚ (NumberField.integralBasis (Kminus p)) e.symm
      rw [show ((e.symm : _ ≃ _).symm : _ → _) = (e : _ → _) from rfl] at this
      exact this
    rw [h2, ← NumberField.coe_discr]
  -- pb.basis elements are integral.
  have h_pbBas_int : ∀ j : Fin 2, IsIntegral ℤ (pbBas j) := fun j ↦ by
    have : pbBas j = pb.basis ((finCongr hdim).symm j) := by simp [pbBas]
    rw [this]
    exact alphaPowerBasis_basis_isIntegral p hp3 _
  -- Lift to 𝓞.
  let pbLift : Fin 2 → 𝓞 (Kminus p) := fun j ↦ ⟨pbBas j, h_pbBas_int j⟩
  -- Integer matrix: P_int i j = RingOfIntegers.basis.repr (pbLift j) (e i).
  let P_int : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦
    (NumberField.RingOfIntegers.basis (Kminus p)).repr (pbLift j) (e i)
  -- Key: iB.toMatrix pbBas = P_int.map (algebraMap ℤ ℚ).
  have h_toMatrix_eq : iB.toMatrix pbBas = P_int.map (algebraMap ℤ ℚ) := by
    ext i j
    change iB.repr (pbBas j) i = _
    rw [show iB = (NumberField.integralBasis (Kminus p)).reindex e.symm from rfl]
    rw [Module.Basis.repr_reindex_apply]
    rw [Equiv.symm_symm]
    have h : (pbBas j : Kminus p) = (algebraMap (𝓞 (Kminus p)) (Kminus p)) (pbLift j) := rfl
    rw [h, NumberField.integralBasis_repr_apply]
    rfl
  -- Apply the discr formula.
  have h_vecMul :
      Matrix.vecMul (iB : Fin 2 → Kminus p)
        ((P_int.map (algebraMap ℤ ℚ)).map (algebraMap ℚ (Kminus p))) =
      (pbBas : Fin 2 → Kminus p) := by
    funext j
    change ∑ i, (iB i : Kminus p) *
        (algebraMap ℚ (Kminus p)) ((P_int.map (algebraMap ℤ ℚ)) i j) = pbBas j
    have h_entry : ∀ i, (P_int.map (algebraMap ℤ ℚ)) i j = iB.repr (pbBas j) i := by
      intro i
      have := congrFun (congrFun h_toMatrix_eq.symm i) j
      change _ = iB.toMatrix pbBas i j
      exact this
    conv_lhs => rw [show (fun i ↦ (iB i : Kminus p) *
      (algebraMap ℚ (Kminus p)) ((P_int.map (algebraMap ℤ ℚ)) i j)) =
      (fun i ↦ (iB i : Kminus p) *
        (algebraMap ℚ (Kminus p)) (iB.repr (pbBas j) i)) from by
      funext i; rw [h_entry]]
    conv_rhs => rw [← iB.sum_repr (pbBas j)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Algebra.smul_def, mul_comm]
  have h_discr_eq : Algebra.discr ℚ pbBas =
      (P_int.map (algebraMap ℤ ℚ)).det ^ 2 * Algebra.discr ℚ iB := by
    rw [← h_vecMul]
    exact Algebra.discr_of_matrix_vecMul _ _
  -- Simplify det: (P_int.map algebraMap).det = P_int.det (cast).
  have h_det_map : (P_int.map (algebraMap ℤ ℚ)).det = (P_int.det : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) P_int
    -- this : (Int.castRingHom ℚ) P_int.det = ((Int.castRingHom ℚ).mapMatrix P_int).det
    -- Note: mapMatrix = map + cast.
    change _ = (Int.castRingHom ℚ) P_int.det
    rw [this]
    rfl
  rw [h_pbBas_disc, h_iB_disc] at h_discr_eq
  -- h_discr_eq : -(p : ℚ) = (P_int.map algebraMap ℤ ℚ).det^2 * (discr K : ℚ).
  rw [h_det_map] at h_discr_eq
  -- Cast to ℤ.
  have h_cast_eq : -(p : ℤ) = P_int.det ^ 2 * NumberField.discr (Kminus p) := by
    have h_rat : ((-(p : ℤ) : ℤ) : ℚ) =
        ((P_int.det ^ 2 * NumberField.discr (Kminus p) : ℤ) : ℚ) := by
      push_cast
      have h_det_cast : (P_int.map (Int.cast : ℤ → ℚ)).det = (P_int.det : ℚ) := h_det_map
      rw [h_det_cast]
      exact h_discr_eq
    exact_mod_cast h_rat
  -- Arithmetic: |-p| = |P_int.det²| · |disc K|, p prime → det² = 1.
  have h_abs_prod : P_int.det.natAbs ^ 2 * (NumberField.discr (Kminus p)).natAbs = p := by
    have h_na : Int.natAbs (-(p : ℤ)) = p := by simp
    have h_prod_na : (P_int.det ^ 2 * NumberField.discr (Kminus p)).natAbs = p := by
      rw [← h_cast_eq, h_na]
    rw [Int.natAbs_mul, Int.natAbs_pow] at h_prod_na
    exact h_prod_na
  have h_prime : Nat.Prime p := hp.out
  have h_det_sq_dvd : P_int.det.natAbs ^ 2 ∣ p := ⟨_, h_abs_prod.symm⟩
  have h_det_sq_eq : P_int.det.natAbs ^ 2 = 1 := by
    rcases h_prime.eq_one_or_self_of_dvd _ h_det_sq_dvd with h | h
    · exact h
    · -- P_int.det.natAbs² = p impossible since p is prime (not a perfect square).
      exfalso
      have h_dvd : P_int.det.natAbs ∣ p := ⟨P_int.det.natAbs, by rw [← h, sq]⟩
      rcases h_prime.eq_one_or_self_of_dvd _ h_dvd with h' | h'
      · -- h' : P_int.det.natAbs = 1, so h : 1^2 = p, so p = 1, contradiction.
        rw [h', one_pow] at h
        exact h_prime.one_lt.ne' h.symm
      · -- h' : P_int.det.natAbs = p, so h : p^2 = p, so p(p-1) = 0, contradiction.
        rw [h', sq] at h
        have hpos : 1 < p := h_prime.one_lt
        nlinarith
  rw [h_det_sq_eq, one_mul] at h_abs_prod
  exact h_abs_prod

end DiscriminantFoundations

end BernoulliRegular
