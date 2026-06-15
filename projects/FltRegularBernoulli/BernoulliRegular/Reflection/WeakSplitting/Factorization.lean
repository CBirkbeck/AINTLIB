module

public import BernoulliRegular.Reflection.WeakSplitting.KummerComparison
public import BernoulliRegular.Reflection.WeakSplitting.PartialZeta
public import BernoulliRegular.Reflection.WeakSplitting.UniformResidueDegree


/-!
# Partial local Euler factor and bridge to the partial Dedekind zeta

For a number field `L` and a finite set `F` of `L`-primes, the partial
local Euler factor at a rational prime `q`, restricted to primes outside
`F`, is
$$
\mathrm{localFactor}_L^{F}(q, s) :=
  \prod_{Q \in T_L(q) \setminus F}\bigl(1 - N(Q)^{-s}\bigr).
$$

The cancellation lemma `dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv`
shows that multiplying `(dedekindLocalFactorRat L q s)⁻¹` by the missing
factors at primes in `F` recovers `(dedekindLocalFactorRatPartial L F q s)⁻¹`.

This is one of the building blocks for REF-21c2c (the global tprod
assembly).

## Main definitions

* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRatPartial`: the
  partial local Euler factor restricted to `T_L(q) \ F`.

## Main results

* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRatPartial_eq`:
  product of factors over `T_L(q) \ F` equals the partial form.
* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRat_eq_mul_partial`:
  the full local factor decomposes as the partial factor times the
  factors at `F`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (L : Type*) [Field L] [NumberField L]

/--
The partial local Euler factor at a rational prime `q`, restricted to the
primes `Q` of `𝓞 L` lying above `q` that are **not** in the finite "bad"
set `F`. When `F = ∅`, this reduces to `dedekindLocalFactorRat L q`.
-/
def dedekindLocalFactorRatPartial (F : Finset (Ideal (𝓞 L))) (q : ℕ) (s : ℂ) : ℂ :=
  ∏ Q ∈ (IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) \ F,
    (1 - (Ideal.absNorm Q : ℂ) ^ (-s))

/--
The full local factor `dedekindLocalFactorRat L q s` decomposes as the
partial factor (over primes outside `F`) times the factors at primes
in `F ∩ T_L(q)`.
-/
theorem dedekindLocalFactorRat_eq_mul_partial (F : Finset (Ideal (𝓞 L)))
    (q : ℕ) (s : ℂ) :
    dedekindLocalFactorRat L q s =
      dedekindLocalFactorRatPartial L F q s *
        ∏ Q ∈
          (IsDedekindDomain.primesOverFinset
            (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) ∩ F,
          (1 - (Ideal.absNorm Q : ℂ) ^ (-s)) := by
  classical
  unfold dedekindLocalFactorRat dedekindLocalFactorRatPartial
  set T : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  rw [show T \ F = T \ (T ∩ F) from (Finset.sdiff_inter_self_left T F).symm]
  exact (Finset.prod_sdiff Finset.inter_subset_left).symm

/--
Multiplying the inverse of the full local factor by the missing factors at
primes in `F` (intersected with `T_L(q)`) yields the inverse of the partial
local factor. This is the cancellation form of
`dedekindLocalFactorRat_eq_mul_partial`.
-/
theorem dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv
    (F : Finset (Ideal (𝓞 L))) {q : ℕ} (hq : q.Prime) {s : ℂ}
    (hs : 0 < s.re) :
    (dedekindLocalFactorRat L q s)⁻¹ *
        ∏ Q ∈
          (IsDedekindDomain.primesOverFinset
            (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) ∩ F,
          (1 - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      (dedekindLocalFactorRatPartial L F q s)⁻¹ := by
  classical
  set T : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  have h_inter_ne :
      (∏ Q ∈ T ∩ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun Q hQ => ?_
    have h_full := dedekindLocalFactorRat_ne_zero L hq hs
    unfold dedekindLocalFactorRat at h_full
    exact Finset.prod_ne_zero_iff.mp h_full Q (Finset.mem_inter.mp hQ).1
  rw [dedekindLocalFactorRat_eq_mul_partial L F q s, mul_inv, mul_assoc,
    inv_mul_cancel₀ h_inter_ne, mul_one]

variable (K : Type*) [Field K] [NumberField K] [Algebra K L]

/--
For a tower `K ⊆ L`, a rational prime `q`, a finite set `S` of `K`-primes,
and assuming every `K`-prime above `q` outside `S` splits completely in
`L`, the partial-local-factor identity at `q`:
$$
\mathrm{localFactor}_L^{F_L}(q, s)
  = \bigl(\mathrm{localFactor}_K^{S}(q, s)\bigr)^{[L : K]},
$$
where `F_L = S.biUnion (IsDedekindDomain.primesOverFinset · (𝓞 L))` is the
set of `L`-primes above `S`.
-/
theorem dedekindLocalFactorRatPartial_eq_pow_of_splits {q : ℕ} (hq : q.Prime)
    (S : Finset (Ideal (𝓞 K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (hsplits : ∀ P ∈
      (IsDedekindDomain.primesOverFinset
        (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)) \ S,
      BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P) (s : ℂ) :
    dedekindLocalFactorRatPartial L
        (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) q s =
      (dedekindLocalFactorRatPartial K S q s) ^ Module.finrank K L := by
  classical
  set T_K : Finset (Ideal (𝓞 K)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)
  set T_L : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  unfold dedekindLocalFactorRatPartial
  have h_index_eq :
      T_L \ (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) =
        (T_K \ S).biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)) := by
    ext Q
    simp only [Finset.mem_sdiff, Finset.mem_biUnion]
    constructor
    · rintro ⟨hQ_in_TL, hQ_notin⟩
      change Q ∈
        IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ))
          (𝓞 L) at hQ_in_TL
      rw [primesOverFinset_rat_eq_biUnion K L q hq] at hQ_in_TL
      simp only [Finset.mem_biUnion] at hQ_in_TL
      obtain ⟨P, hP_TK, hQ_above_P⟩ := hQ_in_TL
      exact ⟨P, ⟨hP_TK, fun hP_S => hQ_notin ⟨P, hP_S, hQ_above_P⟩⟩, hQ_above_P⟩
    · rintro ⟨P, ⟨hP_TK, hP_notin_S⟩, hQ_above_P⟩
      refine ⟨?_, fun ⟨P', hP'_S, hQ_above_P'⟩ => ?_⟩
      · change Q ∈
          IsDedekindDomain.primesOverFinset
            (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
        rw [primesOverFinset_rat_eq_biUnion K L q hq]
        exact Finset.mem_biUnion.mpr ⟨P, hP_TK, hQ_above_P⟩
      · haveI : Fact q.Prime := ⟨hq⟩
        have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact_mod_cast hq.ne_zero
        have hP_in : P ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
          (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp hP_TK
        have hP_ne : P ≠ ⊥ := by
          intro hP_bot
          have hover : Ideal.span ({(q : ℤ)} : Set ℤ) = Ideal.under ℤ P := by
            haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_in.2
            exact P.over_def _
          rw [hP_bot, Ideal.under_bot, Ideal.span_singleton_eq_bot] at hover
          exact hq.ne_zero (by exact_mod_cast hover)
        haveI : P.IsMaximal := hP_in.1.isMaximal hP_ne
        have hQ_lies_P : Q.LiesOver P :=
          ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hP_ne (𝓞 L)).mp hQ_above_P).2
        have hP'_ne : P' ≠ ⊥ := hS_ne P' hP'_S
        haveI hP'_prime : P'.IsPrime := hS_prime P' hP'_S
        haveI : P'.IsMaximal := hP'_prime.isMaximal hP'_ne
        have hQ_lies_P' : Q.LiesOver P' :=
          ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hP'_ne (𝓞 L)).mp hQ_above_P').2
        have h1 : P = Ideal.under (𝓞 K) Q := (Ideal.liesOver_iff Q P).mp hQ_lies_P
        have h2 : P' = Ideal.under (𝓞 K) Q := (Ideal.liesOver_iff Q P').mp hQ_lies_P'
        exact hP_notin_S (h1.trans h2.symm ▸ hP'_S)
  rw [h_index_eq, Finset.prod_biUnion (fun P hP P' hP' hne =>
    primesOverFinset_disjoint_of_ne K L q hq
      ((Finset.mem_sdiff.mp hP).1) ((Finset.mem_sdiff.mp hP').1) hne)]
  have h_factor : ∀ P ∈ T_K \ S,
        ∏ Q ∈ IsDedekindDomain.primesOverFinset P (𝓞 L),
          ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
          ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s)) ^ Module.finrank K L := by
    intro P hP
    haveI : Fact q.Prime := ⟨hq⟩
    have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hq.ne_zero
    have hP_in : P ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp
        (Finset.mem_sdiff.mp hP).1
    haveI hP_lies_q : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_in.2
    have hP_ne : P ≠ ⊥ := by
      intro hP_bot
      have hover : Ideal.span ({(q : ℤ)} : Set ℤ) = Ideal.under ℤ P := P.over_def _
      rw [hP_bot, Ideal.under_bot, Ideal.span_singleton_eq_bot] at hover
      exact hq.ne_zero (by exact_mod_cast hover)
    haveI := hP_in.1
    haveI : P.IsMaximal := hP_in.1.isMaximal hP_ne
    exact BernoulliRegular.Ideal.SplitsCompletely.prod_localFactor_eq_pow
      (𝓞 L) K L hP_ne (hsplits P hP) s
  rw [Finset.prod_congr rfl h_factor, ← Finset.prod_pow]

/--
The tprod-form of the global identity: under the splits-completely
hypothesis at every good `K`-prime above every rational prime,
$$
\prod_{q : \text{Nat.Primes}}\bigl(\mathrm{localFactor}_L^{F_L}(q, s)\bigr)^{-1}
  = \Bigl(\prod_{q}\bigl(\mathrm{localFactor}_K^{S}(q, s)\bigr)^{-1}\Bigr)^{[L : K]},
$$
where `F_L = S.biUnion (IsDedekindDomain.primesOverFinset · (𝓞 L))`.

This is a per-q identity, lifted to a `tprod` via `tprod_pow`. It gives the
GLOBAL Kummer-comparison at the partial-zeta level, modulo the bridge from
the original `dedekindZetaPartial` definition (which is REF-21c2c's full
form). Both sides here are TPROD forms; converting them to the original
`dedekindZetaPartial` form is the remaining bridge step.
-/
theorem tprod_dedekindLocalFactorRatPartial_inv_eq_pow_of_splits
    (S : Finset (Ideal (𝓞 K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (hsplits : ∀ q : ℕ, q.Prime →
      ∀ P ∈
        (IsDedekindDomain.primesOverFinset
          (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)) \ S,
        BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P) (s : ℂ)
    (hMult_K : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRatPartial K S (q : ℕ) s)⁻¹)) :
    (∏' q : Nat.Primes, (dedekindLocalFactorRatPartial L
        (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) (q : ℕ) s)⁻¹) =
      (∏' q : Nat.Primes, (dedekindLocalFactorRatPartial K S (q : ℕ) s)⁻¹) ^
        Module.finrank K L := by
  have h_per_q : ∀ q : Nat.Primes,
      (dedekindLocalFactorRatPartial L
        (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) (q : ℕ) s)⁻¹ =
      ((dedekindLocalFactorRatPartial K S (q : ℕ) s)⁻¹) ^ Module.finrank K L := fun q => by
    rw [dedekindLocalFactorRatPartial_eq_pow_of_splits L K q.2 S hS_ne hS_prime
      (hsplits (q : ℕ) q.2) s, inv_pow]
  rw [tprod_congr h_per_q]
  exact hMult_K.tprod_pow _

/--
Under uniformity at every rational prime `q`, the Dedekind zeta of `L`
equals the tprod of the inverse local factors:
$$
\zeta_L(s) = \prod_{q : \text{Nat.Primes}}
  \bigl(\mathrm{localFactor}_L(q, s)\bigr)^{-1}.
$$
This combines the project's `dedekindZeta_eq_tprod_primePowerSeries` (which
works for any number field) with REF-21c2a2 (the local-factor identity at
uniform residue degree).
-/
theorem dedekindZeta_eq_tprod_localFactorRat_inv
    (huni : ∀ q : ℕ, q.Prime → ∃ d : ℕ, 1 ≤ d ∧ UniformResidueDegree L q d)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta L s =
      ∏' q : Nat.Primes, (dedekindLocalFactorRat L (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_primePowerSeries L hs]
  refine tprod_congr fun q => ?_
  obtain ⟨d, hd, huni_q⟩ := huni (q : ℕ) q.2
  exact dedekindLocalFactorRat_identity_of_uniform L q.2 hd huni_q hs

/--
For a finite set `F` of nonzero prime ideals of `𝓞 L`, the product over
`F` of the local factors equals the tprod (over `Nat.Primes`) of the
intersected products at each rational prime. The function `q ↦ ∏ Q ∈ F ∩
T_L(q), g Q` has finite support (only the rational primes underneath some
prime in `F` contribute non-trivially).
-/
theorem prod_F_eq_tprod_intersect
    (F : Finset (Ideal (𝓞 L)))
    (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥)
    (g : Ideal (𝓞 L) → ℂ) :
    ∏ Q ∈ F, g Q =
      ∏' q : Nat.Primes,
        ∏ Q ∈ F ∩
          IsDedekindDomain.primesOverFinset
            (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
          g Q := by
  classical
  set ratPrimes : Finset Nat.Primes :=
    F.attach.image (fun ⟨Q, hQ⟩ => ⟨Ideal.absNorm (Ideal.under ℤ Q),
      have ⟨hQ_prime, hQ_ne⟩ := hF Q hQ
      haveI : Q.IsPrime := hQ_prime
      haveI : NeZero Q := ⟨hQ_ne⟩
      Nat.absNorm_under_prime Q⟩) with h_ratPrimes
  have h_finite_supp : ∀ q : Nat.Primes, q ∉ ratPrimes →
      ∏ Q ∈ F ∩
          IsDedekindDomain.primesOverFinset
            (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
        g Q = 1 := by
    intro q hq_notin
    apply Finset.prod_eq_one
    intro Q hQ_in
    exfalso
    apply hq_notin
    have ⟨hQ_F, hQ_in_q⟩ := Finset.mem_inter.mp hQ_in
    have ⟨hQ_prime, hQ_ne⟩ := hF Q hQ_F
    haveI : Q.IsPrime := hQ_prime
    haveI : NeZero Q := ⟨hQ_ne⟩
    have hq_ne : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast q.2.ne_zero
    haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
    haveI : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime (q : ℕ)
    have hQ_lies : Q.LiesOver (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) :=
      ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp
        hQ_in_q).2
    have hQ_under : Ideal.under ℤ Q = Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ) :=
      hQ_lies.over.symm
    have h_absNorm_eq : Ideal.absNorm (Ideal.under ℤ Q) = q := by
      rw [hQ_under,
        show Ideal.absNorm (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) =
            Nat.card (ℤ ⧸ Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) from ?_]
      · exact Int.card_ideal_quot _
      · rw [← Submodule.cardQuot_apply]; rfl
    rw [h_ratPrimes]
    exact Finset.mem_image.mpr ⟨⟨Q, hQ_F⟩, Finset.mem_attach _ _, Subtype.ext h_absNorm_eq⟩
  rw [tprod_eq_prod h_finite_supp,
    show (∏ q ∈ ratPrimes,
        ∏ Q ∈ F ∩
            IsDedekindDomain.primesOverFinset
              (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
          g Q) =
        ∏ Q ∈ ratPrimes.biUnion
          (fun q => F ∩ IsDedekindDomain.primesOverFinset
            (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L)),
        g Q from ?_]
  · congr 1
    ext Q
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    refine ⟨fun hQ_F => ?_, fun ⟨_, _, hQ_F, _⟩ => hQ_F⟩
    have ⟨hQ_prime, hQ_ne⟩ := hF Q hQ_F
    haveI : Q.IsPrime := hQ_prime
    haveI : NeZero Q := ⟨hQ_ne⟩
    let qNat : ℕ := Ideal.absNorm (Ideal.under ℤ Q)
    let qPrime : Nat.Primes := ⟨qNat, Nat.absNorm_under_prime Q⟩
    have hqPrime_in : qPrime ∈ ratPrimes := by
      rw [h_ratPrimes]
      exact Finset.mem_image.mpr ⟨⟨Q, hQ_F⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨qPrime, hqPrime_in, hQ_F, ?_⟩
    have hq_ne : (Ideal.span ({((qPrime : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast qPrime.2.ne_zero
    haveI : Fact (qPrime : ℕ).Prime := ⟨qPrime.2⟩
    haveI : (Ideal.span ({((qPrime : ℕ) : ℤ)} : Set ℤ)).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime (qPrime : ℕ)
    refine (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mpr ⟨hQ_prime, ?_⟩
    have hunder : Ideal.under ℤ Q = Ideal.span ({((qPrime : ℕ) : ℤ)} : Set ℤ) := by
      rw [show ((qPrime : ℕ) : ℤ) = ((Ideal.absNorm (Ideal.under ℤ Q) : ℕ) : ℤ) from rfl]
      exact (Int.ideal_span_absNorm_eq_self (Ideal.under ℤ Q)).symm
    exact ⟨hunder.symm⟩
  · refine (Finset.prod_biUnion ?_).symm
    intros q _ q' _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro Q hQ_in_q hQ_in_q'
    have ⟨hQ_F, hQ_in_q_set⟩ := Finset.mem_inter.mp hQ_in_q
    have ⟨_, hQ_in_q'_set⟩ := Finset.mem_inter.mp hQ_in_q'
    have hq_ne : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast q.2.ne_zero
    have hq'_ne : (Ideal.span ({((q' : ℕ) : ℤ)} : Set ℤ)) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast q'.2.ne_zero
    haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
    haveI : Fact (q' : ℕ).Prime := ⟨q'.2⟩
    haveI : (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime (q : ℕ)
    haveI : (Ideal.span ({((q' : ℕ) : ℤ)} : Set ℤ)).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime (q' : ℕ)
    have hQ_lies_q : Q.LiesOver (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) :=
      ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp hQ_in_q_set).2
    have hQ_lies_q' : Q.LiesOver (Ideal.span ({((q' : ℕ) : ℤ)} : Set ℤ)) :=
      ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hq'_ne (𝓞 L)).mp hQ_in_q'_set).2
    apply hne
    apply Subtype.ext
    have hspan_eq :
        Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ) = Ideal.span ({((q' : ℕ) : ℤ)} : Set ℤ) :=
      hQ_lies_q.over.trans hQ_lies_q'.over.symm
    have h_dvd1 : ((q : ℕ) : ℤ) ∣ ((q' : ℕ) : ℤ) := by
      rw [← Ideal.mem_span_singleton, hspan_eq]
      exact Ideal.subset_span (Set.mem_singleton _)
    have h_dvd2 : ((q' : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := by
      rw [← Ideal.mem_span_singleton, ← hspan_eq]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact Nat.dvd_antisymm (by exact_mod_cast h_dvd1) (by exact_mod_cast h_dvd2)

/--
The bridge: under uniformity at every rational prime for `L`, and assuming
multipliability of the relevant tprods,
$$
\zeta_L(s) \cdot \prod_{Q \in F}(1 - N(Q)^{-s})
  = \prod_{q : \text{Nat.Primes}}\bigl(\mathrm{localFactor}_L^{F}(q, s)\bigr)^{-1}.
$$
The left side is `dedekindZeta L s * ∏ Q ∈ F, ...`, the unfolded form of
`dedekindZetaPartial L F s` (modulo the `Finset (Ideal)` vs
`Finset (HeightOneSpectrum)` type translation).
-/
theorem dedekindZeta_mul_prod_eq_tprod_partial_inv
    {s : ℂ} (hs : 1 < s.re)
    (F : Finset (Ideal (𝓞 L))) (hF : ∀ Q ∈ F, Q.IsPrime ∧ Q ≠ ⊥)
    (huni : ∀ q : ℕ, q.Prime → ∃ d : ℕ, 1 ≤ d ∧ UniformResidueDegree L q d)
    (hMult : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRat L (q : ℕ) s)⁻¹))
    (hMult_F : Multipliable (fun q : Nat.Primes =>
      ∏ Q ∈ F ∩ IsDedekindDomain.primesOverFinset
        (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)))) :
    dedekindZeta L s * ∏ Q ∈ F, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      ∏' q : Nat.Primes, (dedekindLocalFactorRatPartial L F (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_localFactorRat_inv L huni hs,
    prod_F_eq_tprod_intersect L F hF (fun Q => (1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)),
    (hMult.hasProd.mul hMult_F.hasProd).tprod_eq.symm]
  refine tprod_congr fun q => ?_
  rw [Finset.inter_comm F (IsDedekindDomain.primesOverFinset _ (𝓞 L))]
  exact dedekindLocalFactorRat_inv_mul_factor_eq_partial_inv L F q.2 (by linarith)

/--
The full global Kummer-comparison at the level of `dedekindZeta · ∏(removed)`:
$$
\zeta_L(s) \cdot \prod_{Q \in F_L}(1 - N(Q)^{-s})
  = \Bigl(\zeta_K(s) \cdot \prod_{P \in S}(1 - N(P)^{-s})\Bigr)^{[L : K]},
$$
where `F_L = S.biUnion (IsDedekindDomain.primesOverFinset · (𝓞 L))` is the
set of `L`-primes above `S`.

The hypotheses:
- Uniformity at every rational prime for both `K` and `L`.
- Splits-completely at every good `K`-prime.
- Multipliability of the relevant tprods.

This is the global content of REF-21c2c, in a form suitable for the
pole-order argument (REF-21d) once translated to the
`dedekindZetaPartial` definition (which uses `Finset (HeightOneSpectrum)`).
-/
theorem dedekindZeta_mul_prod_eq_pow_of_splits
    {s : ℂ} (hs : 1 < s.re)
    (S : Finset (Ideal (𝓞 K))) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hS_prime : ∀ P ∈ S, P.IsPrime)
    (huni_L : ∀ q : ℕ, q.Prime → ∃ d : ℕ, 1 ≤ d ∧ UniformResidueDegree L q d)
    (huni_K : ∀ q : ℕ, q.Prime → ∃ d : ℕ, 1 ≤ d ∧ UniformResidueDegree K q d)
    (hsplits : ∀ q : ℕ, q.Prime →
      ∀ P ∈
        (IsDedekindDomain.primesOverFinset
          (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)) \ S,
        BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P)
    (hMult_L : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRat L (q : ℕ) s)⁻¹))
    (hMult_K : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRat K (q : ℕ) s)⁻¹))
    (hMult_FL : Multipliable (fun q : Nat.Primes =>
      ∏ Q ∈ (S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L))) ∩
        IsDedekindDomain.primesOverFinset (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 L),
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s))))
    (hMult_S : Multipliable (fun q : Nat.Primes =>
      ∏ P ∈ S ∩ IsDedekindDomain.primesOverFinset
        (Ideal.span ({((q : ℕ) : ℤ)} : Set ℤ)) (𝓞 K),
        ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s))))
    (hMult_partialK : Multipliable (fun q : Nat.Primes =>
      (dedekindLocalFactorRatPartial K S (q : ℕ) s)⁻¹))
    (hF_L_prime : ∀ Q ∈ S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)),
      Q.IsPrime ∧ Q ≠ ⊥)
    (hS_S_prime : ∀ P ∈ S, P.IsPrime ∧ P ≠ ⊥) :
    dedekindZeta L s * ∏ Q ∈ S.biUnion (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)),
        ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      (dedekindZeta K s * ∏ P ∈ S, ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s))) ^
        Module.finrank K L := by
  rw [dedekindZeta_mul_prod_eq_tprod_partial_inv L hs _ hF_L_prime huni_L hMult_L hMult_FL,
    dedekindZeta_mul_prod_eq_tprod_partial_inv K hs S hS_S_prime huni_K hMult_K hMult_S]
  exact tprod_dedekindLocalFactorRatPartial_inv_eq_pow_of_splits L K S hS_ne hS_prime
    hsplits s hMult_partialK

end WeakSplitting

end BernoulliRegular
