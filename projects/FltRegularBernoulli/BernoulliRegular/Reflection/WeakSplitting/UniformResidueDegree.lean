module

public import BernoulliRegular.Reflection.WeakSplitting.RationalPrimeFactor
public import BernoulliRegular.NumberFieldEulerProduct
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Local-factor identity under uniform residue degree

For a general number field `L` and a rational prime `q`, suppose every
prime `Q` of `𝓞 L` above `q` has the same `inertiaDeg q Q = d`. Then the
rational-prime local factor of `ζ_L(s)` at `q` equals the inverse of the
finite product of local Euler factors.

This generalises the project's cyclotomic-specific machinery
(`BernoulliRegular.dedekind_prime_power_series_eq_localFactor`) to any
number field admitting a uniform residue degree at the rational prime.

## Main definitions

* `BernoulliRegular.WeakSplitting.UniformResidueDegree`: the predicate
  that all primes of `𝓞 L` above the rational prime `q` have the same
  inertia degree.

## Main results (in this file)

* `BernoulliRegular.WeakSplitting.absNorm_eq_q_pow_d_of_uniform`:
  every prime above `q` has absolute norm `q^d`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField Ideal Filter Topology

variable (L : Type*) [Field L] [NumberField L]

/--
The predicate that every prime `Q` of `𝓞 L` above the rational prime `q`
has the same inertia degree `d` (over `ℤ`).
-/
def UniformResidueDegree (q d : ℕ) : Prop :=
  ∀ Q ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L),
    inertiaDeg (Ideal.span ({(q : ℤ)} : Set ℤ)) Q = d

/--
Under the uniform-residue-degree assumption, every prime `Q ∈ T` above the
rational prime `q` has `absNorm Q = q^d`.
-/
theorem absNorm_eq_q_pow_d_of_uniform {q d : ℕ} (hq : q.Prime)
    (huni : UniformResidueDegree L q d)
    {Q : Ideal (𝓞 L)}
    (hQ : Q ∈
      IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) :
    Ideal.absNorm Q = q ^ d := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hQ_mem : Q ∈ (Ideal.span ({(q : ℤ)} : Set ℤ)).primesOver (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp hQ
  haveI : Q.IsPrime := hQ_mem.1
  haveI : Q.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hQ_mem.2
  rw [Ideal.absNorm_eq_pow_inertiaDeg' Q hq, huni Q hQ]

/--
Under the uniform-residue-degree assumption with `d ≥ 1`, every prime `Q`
above `q` has `absNorm Q = q^d ≥ 2`.
-/
theorem one_lt_absNorm_of_uniform {q d : ℕ} (hq : q.Prime) (hd : 1 ≤ d)
    (huni : UniformResidueDegree L q d)
    {Q : Ideal (𝓞 L)}
    (hQ : Q ∈
      IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) :
    1 < Ideal.absNorm Q := by
  rw [absNorm_eq_q_pow_d_of_uniform L hq huni hQ]
  exact Nat.one_lt_pow (by lia) hq.one_lt

/--
For any number field `L`, prime factors of an ideal `I` of `𝓞 L` whose
absolute norm is a power of the rational prime `q` lie above `q`. This
is the generic version of the project's
`normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow`.
-/
theorem normalizedFactors_subset_primesOverFinset_of_qpow
    {q : ℕ} (hq : q.Prime) {I : Ideal (𝓞 L)} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = q ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  intro P hP
  obtain ⟨hP_prime, hI_le_P⟩ :=
    (Ideal.mem_normalizedFactors_iff hI_ne).1 (Multiset.mem_toFinset.1 hP)
  haveI : P.IsPrime := hP_prime
  have hP_ne : P ≠ ⊥ := fun hP_bot => hI_ne (le_bot_iff.mp (hP_bot ▸ hI_le_P))
  haveI : NeZero P := ⟨hP_ne⟩
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ P) = q :=
    (Nat.prime_dvd_prime_iff_eq (Nat.absNorm_under_prime P) hq).1 <|
      (Nat.absNorm_under_prime P).dvd_of_dvd_pow <|
        (Int.absNorm_under_dvd_absNorm P).trans <| hI_norm ▸
          Ideal.absNorm_dvd_absNorm_of_le hI_le_P
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  refine (IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).2 ⟨hP_prime, ?_⟩
  rw [Ideal.liesOver_iff, ← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P)]
  simp [hunder_eq_q]

/--
Under the uniform-residue-degree assumption, the number of normalised
prime factors of an ideal `I` of `𝓞 L` of norm `q^k` is exactly `k / d`,
i.e., `d * card_factors = k`. This is the generic version of the project's
`normalizedFactors_card_mul_localResidueDegree_of_absNorm_prime_pow`.
-/
theorem normalizedFactors_card_mul_d_eq_n_of_uniform
    {q d : ℕ} (hq : q.Prime) (huni : UniformResidueDegree L q d)
    {I : Ideal (𝓞 L)} (hI_ne : I ≠ ⊥) {k : ℕ} (hI_norm : Ideal.absNorm I = q ^ k) :
    d * (UniqueFactorizationMonoid.normalizedFactors I).card = k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set T : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset : m.toFinset ⊆ T :=
    normalizedFactors_subset_primesOverFinset_of_qpow L hq hI_ne hI_norm
  have hsum_count : ∑ P ∈ T, m.count P = m.card :=
    Multiset.sum_count_eq_card fun P hP => hsubset (Multiset.mem_toFinset.2 hP)
  refine Nat.pow_right_injective hq.one_lt ?_
  calc
    q ^ (d * m.card) = q ^ (d * ∑ P ∈ T, m.count P) := by rw [hsum_count]
    _ = ∏ P ∈ T, (q ^ d) ^ m.count P := by
          rw [Finset.prod_pow_eq_pow_sum]; simp [Nat.pow_mul]
    _ = ∏ P ∈ T, Ideal.absNorm (P ^ m.count P) :=
          Finset.prod_congr rfl fun P hP => by
            rw [map_pow, absNorm_eq_q_pow_d_of_uniform L hq huni hP]
    _ = Ideal.absNorm m.prod := by
          rw [Finset.prod_multiset_count_of_subset m T hsubset, map_prod]
    _ = Ideal.absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
    _ = q ^ k := hI_norm

/--
Under the uniform-residue-degree assumption, if `d ∤ k` then no ideal of
`𝓞 L` has absolute norm `q^k`. Hence `idealNormMultiplicity L (q^k) = 0`.
-/
theorem idealNormMultiplicity_prime_pow_eq_zero_of_uniform_of_not_dvd
    {q d : ℕ} (hq : q.Prime) (huni : UniformResidueDegree L q d)
    {k : ℕ} (hk : ¬ d ∣ k) :
    idealNormMultiplicity L (q ^ k) = 0 := by
  classical
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  exact hk ⟨_, (normalizedFactors_card_mul_d_eq_n_of_uniform L hq huni hI_ne hI_norm).symm⟩

/-- Auxiliary: any prime of `𝓞 L` lying over the rational prime `q` is `Prime`. -/
private lemma prime_of_mem_primesOverFinset_of_uniform
    {q d : ℕ} (hq : q.Prime) (huni : UniformResidueDegree L q d)
    {Q : Ideal (𝓞 L)}
    (hQ : Q ∈
      IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)) :
    Prime Q := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ_norm := absNorm_eq_q_pow_d_of_uniform L hq huni hQ
  have hQ_ne : Q ≠ ⊥ := fun hQ_bot => by
    rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot] at hQ_norm
    exact pow_ne_zero d hq.ne_zero hQ_norm.symm
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  exact (Ideal.prime_iff_isPrime hQ_ne).2
    ((IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).1 hQ).1

/-- Auxiliary: the absolute norm of a product of primes above `q` is `q^(d·N)`,
where `N` is the cardinality and `d` the common residue degree. -/
private lemma absNorm_prod_eq_q_pow_of_uniform
    {q d : ℕ} (hq : q.Prime) (huni : UniformResidueDegree L q d)
    {T : Finset (Ideal (𝓞 L))}
    (hT : T = IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L))
    {m : Multiset (Ideal (𝓞 L))} (hm_subset : m.toFinset ⊆ T) {N : ℕ} (hm_card : m.card = N) :
    Ideal.absNorm m.prod = q ^ (d * N) := by
  have hsum_count : ∑ P ∈ T, m.count P = m.card :=
    Multiset.sum_count_eq_card fun P hP => hm_subset (Multiset.mem_toFinset.2 hP)
  rw [Finset.prod_multiset_count_of_subset m T hm_subset, map_prod]
  calc
    ∏ P ∈ T, Ideal.absNorm (P ^ m.count P) = ∏ P ∈ T, (q ^ d) ^ m.count P :=
          Finset.prod_congr rfl fun P hP => by
            rw [map_pow, absNorm_eq_q_pow_d_of_uniform L hq huni (hT ▸ hP)]
    _ = q ^ (d * ∑ P ∈ T, m.count P) := by
          rw [Finset.prod_pow_eq_pow_sum]; simp [Nat.pow_mul]
    _ = q ^ (d * N) := by rw [hsum_count, hm_card]

/--
Under the uniform-residue-degree assumption with `d ≥ 1`, the number of
nonzero ideals of `𝓞 L` of absolute norm `q^(d·n)` equals the number of
multisets of size `n` drawn from the (finite) set of primes of `𝓞 L`
above `q`.

This is the generic version of the project's
`idealNormMultiplicity_prime_pow_mul_localResidueDegree_eq_card_sym`,
applicable to any number field `L` with uniform residue degree at `q`.
-/
theorem idealNormMultiplicity_prime_pow_mul_d_eq_card_sym_of_uniform
    {q d : ℕ} (hq : q.Prime) (hd : 1 ≤ d) (huni : UniformResidueDegree L q d) (n : ℕ) :
    idealNormMultiplicity L (q ^ (d * n)) =
      Fintype.card (Sym {P : Ideal (𝓞 L) //
        P ∈ IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)} n) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  let T : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  let α : Type _ := {P : Ideal (𝓞 L) // P ∈ T}
  letI : Fintype α := Fintype.ofFinset T fun P => by simp
  let β : Type _ := {I : NonzeroIdeal L // Ideal.absNorm I.1 = q ^ (d * n)}
  have hd_pos : 0 < d := hd
  have hpmap_val :
      ∀ {m : Multiset (Ideal (𝓞 L))} (H : ∀ P, P ∈ m → P ∈ T),
        (Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H).map Subtype.val = m := fun H => by
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ P, P ∈ m → P ∈ T := fun P hP =>
      normalizedFactors_subset_primesOverFinset_of_qpow L hq hI_ne hI_norm
        (Multiset.mem_toFinset.2 hP)
    have hm_card : m.card = n :=
      Nat.eq_of_mul_eq_mul_left hd_pos
        (normalizedFactors_card_mul_d_eq_n_of_uniform L hq huni hI_ne hI_norm)
    ⟨Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H, by simp [hm_card]⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 L)) := s.1.map Subtype.val
    have hm_card : m.card = n := by simp [m]
    have hm_subset : m.toFinset ⊆ T := fun P hP => by
      obtain ⟨Q, _, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hP)
      exact Q.2
    have hm_prime : ∀ P ∈ m, Prime P := fun P hP => by
      obtain ⟨Q, _, rfl⟩ := Multiset.mem_map.1 hP
      exact prime_of_mem_primesOverFinset_of_uniform L hq huni Q.2
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : Ideal.absNorm m.prod = q ^ (d * n) :=
      absNorm_prod_eq_q_pow_of_uniform L hq huni rfl hm_subset hm_card
    ⟨⟨m.prod, hm_prod_ne⟩, hm_norm⟩
  have htoSym_map_val :
      ∀ b : β, (toSym b).1.map Subtype.val =
        UniqueFactorizationMonoid.normalizedFactors b.1.1 := by
    rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
    dsimp [toSym]
    exact hpmap_val _
  have hofSym_nfactors :
      ∀ s : Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    refine UniqueFactorizationMonoid.normalizedFactors_prod_of_prime fun P hP => ?_
    obtain ⟨Q, _, rfl⟩ := Multiset.mem_map.1 hP
    exact prime_of_mem_primesOverFinset_of_uniform L hq huni Q.2
  have hleft : Function.LeftInverse ofSym toSym := fun b => by
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val, Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright : Function.RightInverse ofSym toSym := fun s => by
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold idealNormMultiplicity
  rw [Nat.card_congr (⟨toSym, ofSym, hleft, hright⟩ : β ≃ Sym α n), Nat.card_eq_fintype_card]

/--
The rational-prime local-factor identity for any number field `L` under
the uniform-residue-degree assumption with `d ≥ 1`. On the half-plane
`Re(s) > 1`,
$$
\sum_{k = 0}^\infty a_L(q^k) \cdot (q^k)^{-s}
  = \bigl(\mathrm{localFactor}_L(q, s)\bigr)^{-1}
  = \bigl(1 - q^{-ds}\bigr)^{-\#\{Q \mid q\}}.
$$
This is the specialised REF-21c2a2 — sufficient for our cyclotomic +
Kummer setting where every prime of `𝓞 L` above the rational prime `q`
has the common residue degree `d` inherited from `K`.
-/
theorem dedekindLocalFactorRat_identity_of_uniform
    {q d : ℕ} (hq : q.Prime) (hd : 1 ≤ d) (huni : UniformResidueDegree L q d)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicity L (q ^ k) : ℂ) * (((q ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactorRat L q s)⁻¹ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  set T : Finset (Ideal (𝓞 L)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)
  let α : Type _ := {P : Ideal (𝓞 L) // P ∈ T}
  letI : Fintype α := Fintype.ofFinset T fun P => by simp
  let f : ℕ → ℂ := fun k =>
    (idealNormMultiplicity L (q ^ k) : ℂ) * (((q ^ k : ℕ) : ℂ) ^ (-s))
  let g : ℕ → ℂ := fun n =>
    (idealNormMultiplicity L (q ^ (d * n)) : ℂ) * (((q ^ (d * n) : ℕ) : ℂ) ^ (-s))
  let z : ℂ := (q : ℂ) ^ (-((d : ℂ) * s))
  have hd_pos : 0 < d := hd
  have hs_d : 1 < ((d : ℂ) * s).re := by
    rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul]
    have hd_ge : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [hs, hd_ge]
  have hz : ‖z‖ < 1 :=
    (Complex.norm_prime_cpow_le_one_half ⟨q, hq⟩ hs_d).trans_lt (by norm_num)
  have hg_eq : g = fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n := by
    funext n
    dsimp [g, z]
    rw [idealNormMultiplicity_prime_pow_mul_d_eq_card_sym_of_uniform L hq hd huni n,
      Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul (q : ℕ) (d * n) (-s),
      show (((d * n : ℕ) : ℂ) * (-s)) = (-((d : ℂ) * s)) * n by push_cast; ring,
      Complex.cpow_mul_nat]
  have hg_hasSum : HasSum g (((1 - z)⁻¹) ^ Fintype.card α) := by
    rw [hg_eq, ← tsum_symGeometric α hz]
    exact (summable_tsum_symGeometric α hz).1.hasSum
  have hf_hasSum : HasSum f (((1 - z)⁻¹) ^ Fintype.card α) := by
    refine (hasSum_iff_hasSum_of_ne_zero_bij
      (f := f) (g := g) (i := fun x : Function.support g => d * x.1) ?_ ?_ ?_).2 hg_hasSum
    · exact fun x y hxy => Subtype.ext (Nat.eq_of_mul_eq_mul_left hd_pos hxy)
    · intro k hk
      have hk_mult : idealNormMultiplicity L (q ^ k) ≠ 0 :=
        fun hk_zero => hk (by simp [f, hk_zero])
      obtain ⟨n, rfl⟩ : d ∣ k := by
        by_contra hk_ndvd
        exact hk_mult <|
          idealNormMultiplicity_prime_pow_eq_zero_of_uniform_of_not_dvd L hq huni hk_ndvd
      exact ⟨⟨n, by simpa [f, g] using hk⟩, rfl⟩
    · intro x
      simp [f, g]
  have h_factor : ∀ Q ∈ T, (1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s) = 1 - z := fun Q hQ => by
    have hN : (Ideal.absNorm Q : ℂ) = (q : ℂ) ^ d := by
      rw [absNorm_eq_q_pow_d_of_uniform L hq huni hQ]; push_cast; rfl
    rw [hN, ← Complex.natCast_cpow_natCast_mul q d (-s)]
    ring_nf
    rfl
  have hLF : dedekindLocalFactorRat L q s = (1 - z) ^ Fintype.card α := by
    change ∏ Q ∈ T, ((1 : ℂ) - (Ideal.absNorm Q : ℂ) ^ (-s)) = (1 - z) ^ Fintype.card α
    rw [Finset.prod_congr rfl h_factor, Finset.prod_const, ← Fintype.card_coe T]
  rw [hLF, ← inv_pow]
  exact hf_hasSum.tsum_eq

end WeakSplitting

end BernoulliRegular
