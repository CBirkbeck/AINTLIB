module

public import BernoulliRegular.Reflection.WeakSplitting.Factorization
public import BernoulliRegular.Reflection.WeakSplitting.Final
public import BernoulliRegular.Reflection.WeakSplitting.QPowerIdealEquiv

/-!
# Unconditional global identity and final API (REF-21h)

This file re-proves `dedekindZeta_eq_tprod_localFactorRat_inv` WITHOUT the
uniform-residue-degree hypothesis, using REF-21f3
(`dedekindLocalFactorRat_inv_eq_tsum_idealNormMultiplicity`). Multipliability
of `(dedekindLocalFactorRat L · s)⁻¹` over `Nat.Primes` is proved via the
project's Euler-product machinery.

The closing API `weakSplittingLemma_of_splits` takes only the splits-completely
hypothesis (a finite bad set `S` of K-primes such that every K-prime above
any rational prime, outside `S`, splits completely in `𝓞 L`) and concludes
`Module.finrank K L = 1`. NO uniform-residue-degree hypothesis, NO
multipliability hypotheses.

This closes REF-21.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (L : Type*) [Field L] [NumberField L]

/--
**Unconditional version of `dedekindZeta_eq_tprod_localFactorRat_inv` (REF-21h).**
For any number field `L` and `Re(s) > 1`, the Dedekind zeta function equals the
tprod of inverse local factors. NO uniform-residue-degree hypothesis.
-/
theorem dedekindZeta_eq_tprod_localFactorRat_inv'
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta L s =
      ∏' q : Nat.Primes, (dedekindLocalFactorRat L (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_primePowerSeries L hs]
  exact tprod_congr fun q =>
    (dedekindLocalFactorRat_inv_eq_tsum_idealNormMultiplicity L q.2 hs).symm

/--
**Multipliability of `(dedekindLocalFactorRat L q s)⁻¹` over `q`.**
Follows from the unconditional Euler-product machinery.
-/
theorem multipliable_dedekindLocalFactorRat_inv {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun q : Nat.Primes => (dedekindLocalFactorRat L (q : ℕ) s)⁻¹) := by
  classical
  let f : ℕ → ℂ := fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)
  have hf_zero : f 0 = 0 := by simp [f, idealNormMultiplicity_zero L]
  have hf_one : f 1 = 1 := by simp [f, idealNormMultiplicity_one L]
  have hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := fun {m n} hcop => by
    simp only [f]
    rw [idealNormMultiplicity_mul L hcop, Nat.cast_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum : Summable fun n => ‖f n‖ :=
    summable_idealNormMultiplicity_mul_cpow_neg L hs
  have h_eulerProduct : HasProd
      (fun p : Nat.Primes => ∑' k : ℕ, (idealNormMultiplicity L ((p : ℕ) ^ k) : ℂ) *
        (((p : ℕ) ^ k : ℕ) : ℂ) ^ (-s))
      (∑' n : ℕ, f n) :=
    EulerProduct.eulerProduct_hasProd hf_one hf_mul hf_sum hf_zero
  have h_eulerProduct' : HasProd
      (fun p : Nat.Primes => (dedekindLocalFactorRat L (p : ℕ) s)⁻¹)
      (∑' n : ℕ, f n) := by
    convert h_eulerProduct using 1
    funext p
    exact dedekindLocalFactorRat_inv_eq_tsum_idealNormMultiplicity L p.2 hs
  exact h_eulerProduct'.multipliable

/--
**Multipliability of the F-side correction product (REF-21h helper).**
For a finite set `F : Finset (Ideal (𝓞 L))` of nonzero primes, the function
`q ↦ ∏ Q ∈ F ∩ T_L(q), (1 - absNorm Q^(-s))` has finite support: only
rational primes underneath some `Q ∈ F` contribute. Hence multipliable.
-/
theorem multipliable_F_correction
    (F : Finset (Ideal (𝓞 L)))
    (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥) {s : ℂ} :
    Multipliable (fun q : Nat.Primes =>
      ∏ Q ∈ F ∩ IsDedekindDomain.primesOverFinset (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s))) := by
  classical
  let mkPrime : (Q : Ideal (𝓞 L)) → Q ∈ F → Nat.Primes := fun Q hQ =>
    have h := hF Q hQ
    haveI : Q.IsPrime := h.1
    haveI : NeZero Q := ⟨h.2⟩
    ⟨Ideal.absNorm (Ideal.under ℤ Q), Nat.absNorm_under_prime Q⟩
  let primesUnder : Finset Nat.Primes :=
    F.attach.image (fun Q => mkPrime Q.val Q.property)
  refine multipliable_of_ne_finset_one (s := primesUnder) ?_
  intro q hq
  apply Finset.prod_eq_one
  intro Q hQ_in
  exfalso
  obtain ⟨hQ_F, hQ_in_T⟩ := Finset.mem_inter.mp hQ_in
  obtain ⟨hQ_prime, hQ_ne⟩ := hF Q hQ_F
  haveI : Q.IsPrime := hQ_prime
  haveI : NeZero Q := ⟨hQ_ne⟩
  have hq_ne : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast q.2.ne_zero
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  haveI : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime (q : ℕ)
  have hQ_above : Q ∈ Ideal.primesOver (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp hQ_in_T
  haveI : Q.LiesOver (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) := hQ_above.2
  have h_under_eq : Ideal.under ℤ Q = Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ) :=
    (Q.over_def _).symm
  have h_absNorm_eq : Ideal.absNorm (Ideal.under ℤ Q) = (q : ℕ) := by
    rw [h_under_eq, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Int.card_ideal_quot]
  exact hq <| Finset.mem_image.mpr
    ⟨⟨Q, hQ_F⟩, Finset.mem_attach _ _, Subtype.ext h_absNorm_eq⟩

/--
**Multipliability of `(dedekindLocalFactorRatPartial L F · s)⁻¹` over `q`.**
Follows from `multipliable_dedekindLocalFactorRat_inv` plus
`multipliable_F_correction` via `dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv`.
-/
theorem multipliable_dedekindLocalFactorRatPartial_inv
    (F : Finset (Ideal (𝓞 L)))
    (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥)
    {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRatPartial L F (q : ℕ) s)⁻¹) := by
  have h_eq : ∀ q : Nat.Primes,
      (dedekindLocalFactorRatPartial L F (q : ℕ) s)⁻¹ =
        (dedekindLocalFactorRat L (q : ℕ) s)⁻¹ *
          ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L) ∩ F,
            ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) := fun q =>
    (dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv L F q.2
      (by linarith : (0 : ℝ) < s.re)).symm
  rw [show (fun q : Nat.Primes => (dedekindLocalFactorRatPartial L F (q : ℕ) s)⁻¹) =
    fun q : Nat.Primes => (dedekindLocalFactorRat L (q : ℕ) s)⁻¹ *
      ∏ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L) ∩ F,
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) from funext h_eq]
  refine (multipliable_dedekindLocalFactorRat_inv L hs).mul ?_
  have h := multipliable_F_correction L F hF (s := s)
  convert h using 1
  funext q
  rw [Finset.inter_comm]

variable (K : Type*) [Field K] [NumberField K] [Algebra K L]

/--
**Unconditional `dedekindZeta_mul_prod_eq_tprod_partial_inv` (REF-21h).**
Same as the original but without uniformity hypothesis.
-/
theorem dedekindZeta_mul_prod_eq_tprod_partial_inv'
    {s : ℂ} (hs : 1 < s.re) (F : Finset (Ideal (𝓞 L)))
    (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥) :
    dedekindZeta L s * ∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      ∏' q : Nat.Primes, (dedekindLocalFactorRatPartial L F (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_localFactorRat_inv' L hs,
    prod_F_eq_tprod_intersect L F hF (fun Q => (1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)),
    ((multipliable_dedekindLocalFactorRat_inv L hs).hasProd.mul
      (multipliable_F_correction L F hF).hasProd).tprod_eq.symm]
  refine tprod_congr fun q => ?_
  rw [Finset.inter_comm F (IsDedekindDomain.primesOverFinset _ (𝓞 L))]
  exact dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv L F q.2
    (by linarith : (0 : ℝ) < s.re)

/--
**Unconditional `dedekindZeta_mul_prod_eq_pow_of_splits` (REF-21h).**
Same as the original but without uniformity hypothesis.
-/
theorem dedekindZeta_mul_prod_eq_pow_of_splits'
    {s : ℂ} (hs : 1 < s.re)
    (S : Finset (Ideal (𝓞 K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (hsplits : ∀ q : ℕ, q.Prime →
      ∀ P ∈ (IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)) \ S,
        BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P)
    (hMult_partialK : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRatPartial K S (q : ℕ) s)⁻¹))
    (hF_L_prime : ∀ Q ∈ S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)),
      Q.IsPrime ∧ Q ≠ ⊥)
    (hS_S_prime : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) :
    dedekindZeta L s * ∏ Q ∈ S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)),
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      (dedekindZeta K s * ∏ P ∈ S, ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s))) ^
        Module.finrank K L := by
  rw [dedekindZeta_mul_prod_eq_tprod_partial_inv' L hs _ hF_L_prime,
    dedekindZeta_mul_prod_eq_tprod_partial_inv' K hs S hS_S_prime]
  exact tprod_dedekindLocalFactorRatPartial_inv_eq_pow_of_splits L K S hS_ne hS_prime
    hsplits s hMult_partialK

/--
The bi-union of `IsDedekindDomain.primesOverFinset` over `S` consists of nonzero primes of `𝓞 L`
when `S` is a set of nonzero primes of `𝓞 K`.
-/
private lemma biUnion_S_isPrime_and_ne_bot
    (S : Finset (Ideal (𝓞 K)))
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime) :
    ∀ Q ∈ S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)),
      Q.IsPrime ∧ Q ≠ ⊥ := by
  intro Q hQ
  rw [Finset.mem_biUnion] at hQ
  obtain ⟨P, hP_S, hQ_in⟩ := hQ
  have hP_ne := hS_ne P hP_S
  have hP_prime := hS_prime P hP_S
  haveI : P.IsPrime := hP_prime
  haveI : P.IsMaximal := hP_prime.isMaximal hP_ne
  haveI : NeZero P := ⟨hP_ne⟩
  have hQ_in_set : Q ∈ Ideal.primesOver P (𝓞 L) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hP_ne (𝓞 L)).mp hQ_in
  exact ⟨hQ_in_set.1, Ideal.ne_bot_of_mem_primesOver hP_ne hQ_in_set⟩

/--
**REF-21h: the closing API.**

If almost all primes of `K` split completely in `L` — i.e., there exists
a finite "bad" set `S : Finset (Ideal (𝓞 K))` of nonzero primes such that
every K-prime above any rational prime, but outside `S`, splits completely
in `𝓞 L` — then `Module.finrank K L = 1`.

This composes the unconditional global identity (REF-21h) with the
analytic backbone (REF-21d/e). NO uniform-residue-degree hypothesis,
NO multipliability hypotheses.
-/
theorem weakSplittingLemma_of_splits
    (S : Finset (Ideal (𝓞 K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (hsplits : ∀ q : ℕ, q.Prime →
      ∀ P ∈ (IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)) \ S,
        BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P)
    [Module.Finite K L] [Module.Free K L] (h_finrank_pos : 0 < Module.finrank K L) :
    Module.finrank K L = 1 := by
  have hS_S_prime : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥ :=
    fun P hP => ⟨hS_prime P hP, hS_ne P hP⟩
  have hF_L_prime := biUnion_S_isPrime_and_ne_bot L K S hS_ne hS_prime
  apply weakSplittingLemma L K
    (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) S
  · exact hF_L_prime
  · exact hS_S_prime
  · intro s hs
    have hs_re : 1 < (s : ℂ).re := by simp [hs]
    exact dedekindZeta_mul_prod_eq_pow_of_splits' L K hs_re S hS_ne hS_prime hsplits
      (multipliable_dedekindLocalFactorRatPartial_inv K S hS_S_prime hs_re)
      hF_L_prime hS_S_prime
  · exact h_finrank_pos

end WeakSplitting

end BernoulliRegular
