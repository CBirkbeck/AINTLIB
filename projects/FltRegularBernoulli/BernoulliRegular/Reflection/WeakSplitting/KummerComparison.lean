module

public import BernoulliRegular.Reflection.WeakSplitting.LocalFactor
public import BernoulliRegular.Reflection.WeakSplitting.RationalPrimeFactor
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Int


/-!
# Kummer comparison of local Euler factors at split rational primes

For a tower of number fields `K ⊆ L` and a rational prime `q` such that
every `K`-prime above `q` splits completely in `L`, the local Euler factor
of `ζ_L` at `q` is the `[L:K]`-th power of the local Euler factor of
`ζ_K` at `q`:
$$
\mathrm{localFactor}_L(q, s) = \bigl(\mathrm{localFactor}_K(q, s)\bigr)^{[L:K]}.
$$

The proof uses the partition of prime sets
$$
\{Q \mid q \text{ in } 𝓞 L\}
  = \bigsqcup_{P \mid q \text{ in } 𝓞 K} \{Q \mid P \text{ in } 𝓞 L\}
$$
via the contraction of an `L`-prime to its underlying `K`-prime. The
inner product collapses by REF-21c1 (`SplitsCompletely.prod_localFactor_eq_pow`).

## Main results

* `BernoulliRegular.WeakSplitting.primesOverFinset_rat_eq_biUnion`:
  the partition of L-primes above q by their K-prime contraction.
* `BernoulliRegular.WeakSplitting.dedekindLocalFactorRat_eq_pow_of_splits`:
  the L-side local factor equals the [L:K]-th power of the K-side.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L]

/-- The integer ideal `Ideal.span {(q : ℤ)}` is non-zero whenever `q` is a prime natural. -/
private lemma span_int_q_ne_bot {q : ℕ} (hq : q.Prime) :
    (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hq.ne_zero

/-- A `𝓞 F`-prime `P` lying over `Ideal.span {(q : ℤ)}` for `q.Prime` is itself non-zero. -/
private lemma ne_bot_of_liesOver_span_int_q {q : ℕ} (hq : q.Prime)
    (F : Type*) [Field F] [NumberField F] (P : Ideal (𝓞 F))
    [P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))] : P ≠ ⊥ := by
  intro hP_bot
  have hover : Ideal.span ({(q : ℤ)} : Set ℤ) = Ideal.under ℤ P := P.over_def _
  rw [hP_bot, Ideal.under_bot, Ideal.span_singleton_eq_bot] at hover
  exact hq.ne_zero (by exact_mod_cast hover)

/--
For a tower `ℤ → 𝓞 K → 𝓞 L` and a rational prime `q`, the set of `L`-
primes above `q` decomposes as the disjoint union over `K`-primes above
`q` of the `L`-primes above each `K`-prime.
-/
theorem primesOverFinset_rat_eq_biUnion (q : ℕ) (hq : q.Prime) :
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L) =
      (IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K)).biUnion
        (fun P => IsDedekindDomain.primesOverFinset P (𝓞 L)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_ne := span_int_q_ne_bot hq
  ext Q
  simp only [Finset.mem_biUnion]
  constructor
  · intro hQ
    have hQ_mem : Q ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 L) :=
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp hQ
    haveI hQ_prime : Q.IsPrime := hQ_mem.1
    haveI : Q.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hQ_mem.2
    let P : Ideal (𝓞 K) := Q.under (𝓞 K)
    haveI hP_prime : P.IsPrime := Ideal.IsPrime.under (𝓞 K) Q
    haveI hQ_lies_P : Q.LiesOver P := ⟨rfl⟩
    haveI hP_lies_q : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Ideal.LiesOver.tower_bot (𝔓 := Q) (P := P)
        (p := (Ideal.span ({(q : ℤ)} : Set ℤ)))
    have hP_ne : P ≠ ⊥ := ne_bot_of_liesOver_span_int_q hq K P
    haveI : P.IsMaximal := hP_prime.isMaximal hP_ne
    refine ⟨P,
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mpr
        ⟨hP_prime, hP_lies_q⟩,
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hP_ne (𝓞 L)).mpr
        ⟨hQ_prime, hQ_lies_P⟩⟩
  · rintro ⟨P, hP_mem, hQ_mem⟩
    have hP_in : P ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp hP_mem
    haveI hP_prime : P.IsPrime := hP_in.1
    haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_in.2
    have hP_ne : P ≠ ⊥ := ne_bot_of_liesOver_span_int_q hq K P
    haveI : P.IsMaximal := hP_prime.isMaximal hP_ne
    have hQ_in : Q ∈ P.primesOver (𝓞 L) :=
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hP_ne (𝓞 L)).mp hQ_mem
    haveI : Q.IsPrime := hQ_in.1
    haveI : Q.LiesOver P := hQ_in.2
    haveI : Q.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) :=
      Ideal.LiesOver.trans (𝔓 := Q) (P := P) (p := (Ideal.span ({(q : ℤ)} : Set ℤ)))
    exact (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mpr
      ⟨‹_›, ‹_›⟩

/--
Different `K`-primes above `q` have disjoint sets of `L`-primes above them,
because each `L`-prime sits over a unique `K`-prime (its contraction).
-/
theorem primesOverFinset_disjoint_of_ne (q : ℕ) (hq : q.Prime)
    {P P' : Ideal (𝓞 K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K))
    (hP' : P' ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K))
    (hne : P ≠ P') :
    Disjoint (IsDedekindDomain.primesOverFinset P (𝓞 L))
      (IsDedekindDomain.primesOverFinset P' (𝓞 L)) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  rw [Finset.disjoint_left]
  intro Q hQ_in_P hQ_in_P'
  have hq_ne := span_int_q_ne_bot hq
  have hP_in : P ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp hP
  have hP'_in : P' ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp hP'
  haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_in.2
  haveI : P'.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP'_in.2
  have hP_ne : P ≠ ⊥ := ne_bot_of_liesOver_span_int_q hq K P
  have hP'_ne : P' ≠ ⊥ := ne_bot_of_liesOver_span_int_q hq K P'
  haveI : P.IsMaximal := hP_in.1.isMaximal hP_ne
  haveI : P'.IsMaximal := hP'_in.1.isMaximal hP'_ne
  have hQ_lies_P : Q.LiesOver P :=
    ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hP_ne (𝓞 L)).mp hQ_in_P).2
  have hQ_lies_P' : Q.LiesOver P' :=
    ((_root_.IsDedekindDomain.mem_primesOverFinset_iff hP'_ne (𝓞 L)).mp hQ_in_P').2
  exact hne <| ((Ideal.liesOver_iff Q P).mp hQ_lies_P).trans
    ((Ideal.liesOver_iff Q P').mp hQ_lies_P').symm

/--
Inner factor: for a `K`-prime `P` above `q` at which `L/K` splits completely,
the product of the local factors over the `L`-primes above `P` equals the
local factor at `P`, raised to `[L:K]`.
-/
private lemma inner_prod_localFactor_eq_pow
    {q : ℕ} (hq : q.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K))
    (hsplitsP : BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P) (s : ℂ) :
    ∏ Q ∈ IsDedekindDomain.primesOverFinset P (𝓞 L),
      ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
      ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s)) ^ Module.finrank K L := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_ne := span_int_q_ne_bot hq
  have hP_in : P ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 K) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 K)).mp hP
  haveI : P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hP_in.2
  have hP_ne : P ≠ ⊥ := ne_bot_of_liesOver_span_int_q hq K P
  haveI : P.IsMaximal := hP_in.1.isMaximal hP_ne
  exact BernoulliRegular.Ideal.SplitsCompletely.prod_localFactor_eq_pow
    (𝓞 L) K L hP_ne hsplitsP s

/--
Under the splits-completely hypothesis at every `K`-prime above `q`, the
`L`-side rational-prime local factor equals the `[L:K]`-th power of the
`K`-side local factor:
$$
\mathrm{dedekindLocalFactorRat}_L(q, s) =
  \bigl(\mathrm{dedekindLocalFactorRat}_K(q, s)\bigr)^{[L:K]}.
$$
-/
theorem dedekindLocalFactorRat_eq_pow_of_splits {q : ℕ} (hq : q.Prime)
    (hsplits : ∀ P ∈ IsDedekindDomain.primesOverFinset
      (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K),
      BernoulliRegular.Ideal.SplitsCompletely (𝓞 L) P) (s : ℂ) :
    dedekindLocalFactorRat L q s = (dedekindLocalFactorRat K q s) ^ Module.finrank K L := by
  classical
  set T_K : Finset (Ideal (𝓞 K)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 K) with hT_K
  set T_L : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L) with hT_L
  change ∏ Q ∈ T_L, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) =
    (∏ P ∈ T_K, ((1 : ℂ) - (Ideal.absNorm P : ℂ) ^ (-s))) ^ Module.finrank K L
  rw [hT_L, primesOverFinset_rat_eq_biUnion K L q hq, ← hT_K,
    Finset.prod_biUnion (fun _ hP _ hP' hne =>
      primesOverFinset_disjoint_of_ne K L q hq hP hP' hne),
    Finset.prod_congr rfl (fun P hP =>
      inner_prod_localFactor_eq_pow K L hq hP (hsplits P hP) s),
    ← Finset.prod_pow]

end WeakSplitting

end BernoulliRegular
