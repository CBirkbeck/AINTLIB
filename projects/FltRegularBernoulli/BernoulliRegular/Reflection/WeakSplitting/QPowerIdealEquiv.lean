module

public import BernoulliRegular.Reflection.WeakSplitting.MultiGeometric
public import BernoulliRegular.Reflection.WeakSplitting.RationalPrimeFactor
public import BernoulliRegular.Reflection.WeakSplitting.UniformResidueDegree

/-!
# Equiv between q-power-norm ideals and multiplicity functions (REF-21f1)

For a number field `L` and a rational prime `q`, this file constructs the
bijection between

* the type of ideals `I : Ideal (𝓞 L)` with `I ≠ ⊥` and
  `Ideal.absNorm I = q^k` for some `k : ℕ`, and

* the type of functions `f : ↥(IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 L)) → ℕ`,

via the multiplicity map `I ↦ Q ↦ Multiset.count Q.1 (normalizedFactors I)`.

This is the c2a2B bijection in its fully general (non-uniform-residue-degree)
form. It is the main reindexing ingredient for proving the local-factor
identity `(dedekindLocalFactorRat L q s)⁻¹ = ∑' k, idealNormMultiplicity ...`
without assuming uniform residue degree.

## Main definitions

* `BernoulliRegular.WeakSplitting.QPowerNormIdeal L q`: the type of nonzero
  ideals of `𝓞 L` with absolute norm a power of `q`.
* `BernoulliRegular.WeakSplitting.qPowerNormIdealEquiv L hq`: the `Equiv`
  between `QPowerNormIdeal L q` and `↥(IsDedekindDomain.primesOverFinset _ (𝓞 L)) → ℕ`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open NumberField UniqueFactorizationMonoid

variable (L : Type*) [Field L] [NumberField L]

/--
The type of nonzero ideals of `𝓞 L` whose absolute norm is a power of the
rational prime `q`. These are exactly the ideals supported on primes above `q`.
-/
abbrev QPowerNormIdeal (q : ℕ) : Type _ :=
  { I : Ideal (𝓞 L) // I ≠ ⊥ ∧ ∃ k : ℕ, Ideal.absNorm I = q ^ k }

/--
The finset of primes of `𝓞 L` lying above the rational prime `q`.
-/
abbrev tQ (q : ℕ) : Finset (Ideal (𝓞 L)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L)

/--
For `Q ∈ tQ L q`, `Q.1` is a nonzero prime ideal.
-/
lemma tQ_isPrime_and_ne_bot {q : ℕ} (hq : q.Prime) (Q : ↥(tQ L q)) :
    Q.1.IsPrime ∧ Q.1 ≠ ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hQ_in : Q.1 ∈ Ideal.primesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L) :=
    (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp Q.2
  refine ⟨hQ_in.1, ?_⟩
  haveI : Q.1.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hQ_in.2
  intro hQ_bot
  have hover : Ideal.span ({(q : ℤ)} : Set ℤ) = Ideal.under ℤ Q.1 := Q.1.over_def _
  rw [hQ_bot, Ideal.under_bot, Ideal.span_singleton_eq_bot] at hover
  exact hq.ne_zero (by exact_mod_cast hover)

/--
**Forward map (REF-21f1).** Send a q-power-norm ideal `I` to the function
`Q ↦ Multiset.count Q.1 (normalizedFactors I)` on primes above `q`.
-/
def QPowerNormIdeal.mult {q : ℕ} (I : QPowerNormIdeal L q) :
    ↥(tQ L q) → ℕ := fun Q =>
  Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors I.1)

/--
**Backward map (REF-21f1).** Reconstruct an ideal from a multiplicity function
`f : ↥tQ → ℕ` as the product `∏ Q ∈ tQ.attach, Q.1 ^ f Q`.
-/
def buildIdealFromMult {q : ℕ} (f : ↥(tQ L q) → ℕ) : Ideal (𝓞 L) :=
  ∏ Q ∈ (tQ L q).attach, Q.1 ^ f Q

lemma buildIdealFromMult_ne_bot {q : ℕ} (hq : q.Prime)
    (f : ↥(tQ L q) → ℕ) :
    buildIdealFromMult L f ≠ ⊥ := by
  classical
  unfold buildIdealFromMult
  refine Finset.prod_ne_zero_iff.mpr fun Q _ => ?_
  exact pow_ne_zero _ (tQ_isPrime_and_ne_bot L hq Q).2

lemma buildIdealFromMult_absNorm_isPow {q : ℕ} (hq : q.Prime)
    (f : ↥(tQ L q) → ℕ) :
    ∃ k : ℕ, Ideal.absNorm (buildIdealFromMult L f) = q ^ k := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : (Ideal.span ({(q : ℤ)} : Set ℤ)).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime q
  have hq_ne : (Ideal.span ({(q : ℤ)} : Set ℤ)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  unfold buildIdealFromMult
  let d : ↥(tQ L q) → ℕ := fun Q =>
    Ideal.inertiaDeg (Ideal.span ({(q : ℤ)} : Set ℤ)) Q.1
  have h_each : ∀ Q : ↥(tQ L q), Ideal.absNorm Q.1 = q ^ d Q := fun Q => by
    have hQ_in : Q.1 ∈ Ideal.primesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) (𝓞 L) :=
      (_root_.IsDedekindDomain.mem_primesOverFinset_iff hq_ne (𝓞 L)).mp Q.2
    obtain ⟨hQ_prime, hQ_ne⟩ := tQ_isPrime_and_ne_bot L hq Q
    haveI : Q.1.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) := hQ_in.2
    haveI : Q.1.IsMaximal := hQ_prime.isMaximal hQ_ne
    haveI : NeZero Q.1 := ⟨hQ_ne⟩
    exact Ideal.absNorm_eq_pow_inertiaDeg' Q.1 hq
  refine ⟨∑ Q ∈ (tQ L q).attach, d Q * f Q, ?_⟩
  rw [map_prod]
  trans ∏ Q ∈ (tQ L q).attach, q ^ (d Q * f Q)
  · refine Finset.prod_congr rfl fun Q _ => ?_
    rw [map_pow, h_each Q, ← pow_mul]
  · rw [← Finset.prod_pow_eq_pow_sum]

/-- The backward map wrapped to land in `QPowerNormIdeal L q`. -/
def QPowerNormIdeal.ofMult {q : ℕ} (hq : q.Prime)
    (f : ↥(tQ L q) → ℕ) : QPowerNormIdeal L q :=
  ⟨buildIdealFromMult L f,
    buildIdealFromMult_ne_bot L hq f,
    buildIdealFromMult_absNorm_isPow L hq f⟩

/-- For `Q ∈ tQ L q`, `Q.1` is irreducible (= prime in a Dedekind domain). -/
lemma tQ_irreducible {q : ℕ} (hq : q.Prime) (Q : ↥(tQ L q)) :
    Irreducible Q.1 :=
  let ⟨hQ_prime, hQ_ne⟩ := tQ_isPrime_and_ne_bot L hq Q
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr
    ((Ideal.prime_iff_isPrime hQ_ne).mpr hQ_prime)

/-- The reconstruction equation: `I` is recovered from its multiplicity function.
This is the "left inverse" direction of the Equiv. -/
lemma buildIdealFromMult_mult_eq_self {q : ℕ} (hq : q.Prime)
    (I : QPowerNormIdeal L q) :
    buildIdealFromMult L (QPowerNormIdeal.mult L I) = I.1 := by
  classical
  unfold buildIdealFromMult QPowerNormIdeal.mult
  obtain ⟨I, hI_ne, k, hI_norm⟩ := I
  have h_subset : (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ tQ L q :=
    normalizedFactors_subset_primesOverFinset_of_qpow L hq hI_ne hI_norm
  have h_eq := Finset.prod_multiset_count_of_subset
    (UniqueFactorizationMonoid.normalizedFactors I) (tQ L q) h_subset
  rw [Ideal.prod_normalizedFactors_eq_self hI_ne] at h_eq
  rw [Finset.prod_attach (tQ L q) (fun Q => Q ^ Multiset.count Q
    (UniqueFactorizationMonoid.normalizedFactors I))]
  exact h_eq.symm

/-- Multiplicity at `Q' ∈ tQ L q` of `buildIdealFromMult f` equals `f Q'`.
This is the "right inverse" direction of the Equiv. -/
lemma count_normalizedFactors_buildIdealFromMult {q : ℕ} (hq : q.Prime)
    (f : ↥(tQ L q) → ℕ) (Q' : ↥(tQ L q)) :
    Multiset.count Q'.1
      (UniqueFactorizationMonoid.normalizedFactors (buildIdealFromMult L f)) = f Q' := by
  classical
  unfold buildIdealFromMult
  have h_pow_factors : ∀ Q : ↥(tQ L q), ∀ n : ℕ,
      UniqueFactorizationMonoid.normalizedFactors (Q.1 ^ n) =
        Multiset.replicate n Q.1 := fun Q n => by
    rw [(tQ_irreducible L hq Q).normalizedFactors_pow, normalize_eq]
  have h_ne : ∀ Q : ↥(tQ L q), Q.1 ^ f Q ≠ 0 := fun Q =>
    pow_ne_zero _ (tQ_isPrime_and_ne_bot L hq Q).2
  have h_factors_finset : UniqueFactorizationMonoid.normalizedFactors
      (∏ Q ∈ (tQ L q).attach, Q.1 ^ f Q) =
      ∑ Q ∈ (tQ L q).attach, Multiset.replicate (f Q) Q.1 := by
    induction (tQ L q).attach using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty,
        UniqueFactorizationMonoid.normalizedFactors_one]
    | @insert Q' s hQ' ih =>
      rw [Finset.prod_insert hQ', Finset.sum_insert hQ',
        normalizedFactors_mul (h_ne Q')
          (Finset.prod_ne_zero_iff.mpr fun Q _ => h_ne Q),
        ih, h_pow_factors Q' (f Q')]
  rw [h_factors_finset, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_eq_single Q']
  · simp
  · intro Q _ hne
    have hne_val : Q.1 ≠ Q'.1 := fun heq => hne (Subtype.ext heq)
    simp [hne_val]
  · intro hmem
    exact absurd (Finset.mem_attach _ Q') hmem

/--
**The bijection (REF-21f1).** For a number field `L` and a rational prime `q`,
the type of nonzero ideals of `𝓞 L` with `q`-power norm is in canonical bijection
with the multiplicity functions on the primes of `𝓞 L` lying above `q`.
-/
def qPowerNormIdealEquiv {q : ℕ} (hq : q.Prime) :
    QPowerNormIdeal L q ≃ (↥(tQ L q) → ℕ) where
  toFun := QPowerNormIdeal.mult L
  invFun := QPowerNormIdeal.ofMult L hq
  left_inv I := Subtype.ext (buildIdealFromMult_mult_eq_self L hq I)
  right_inv f := funext fun Q => count_normalizedFactors_buildIdealFromMult L hq f Q

/--
Norm formula on `buildIdealFromMult`: `absNorm (∏ Q^(f Q)) = ∏ (absNorm Q)^(f Q)`.
-/
lemma absNorm_buildIdealFromMult {q : ℕ} (f : ↥(tQ L q) → ℕ) :
    Ideal.absNorm (buildIdealFromMult L f) =
      ∏ Q ∈ (tQ L q).attach, (Ideal.absNorm Q.1) ^ f Q := by
  unfold buildIdealFromMult
  rw [map_prod]
  exact Finset.prod_congr rfl fun Q _ => map_pow _ _ _

/--
**Norm formula (REF-21f2).** For an ideal `I` of `𝓞 L` with `q`-power norm,
`absNorm I` is the product over `Q ∈ tQ.attach` of
`(absNorm Q.1) ^ count Q.1 (normalizedFactors I)`.
-/
theorem absNorm_eq_prod_pow_count {q : ℕ} (hq : q.Prime)
    (I : QPowerNormIdeal L q) :
    Ideal.absNorm I.1 =
      ∏ Q ∈ (tQ L q).attach,
        Ideal.absNorm Q.1 ^ QPowerNormIdeal.mult L I Q := by
  classical
  rw [← buildIdealFromMult_mult_eq_self L hq I, absNorm_buildIdealFromMult]

/-- Distribution of `cpow` over a finset product of natural-number casts. -/
private lemma cpow_finset_prod_natCast {α : Type*} (s : Finset α) (g : α → ℕ) (z : ℂ) :
    (((∏ x ∈ s, g x : ℕ) : ℂ)) ^ z =
      ∏ x ∈ s, ((g x : ℕ) : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/--
For `Q ∈ tQ L q` and `Re(s) > 1`, `‖(absNorm Q.1 : ℂ)^(-s)‖ < 1`.
This is the input hypothesis for the multidim geometric series.
-/
lemma norm_cpow_neg_lt_one_of_mem_tQ {q : ℕ} (hq : q.Prime) {s : ℂ}
    (hs : 1 < s.re) (Q : Ideal (𝓞 L)) (hQ : Q ∈ tQ L q) :
    ‖(Ideal.absNorm Q : ℂ) ^ (-s)‖ < 1 := by
  have hone_lt := one_lt_absNorm_of_mem_primesOverFinset_rat L hq hQ
  have habsN_pos : 0 < Ideal.absNorm Q := by omega
  rw [Complex.norm_natCast_cpow_of_pos habsN_pos, Complex.neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hone_lt
  · linarith

/--
Per-pair identity (REF-21f3 helper): `∏ Q (z_Q)^(f Q) = (absNorm (ofMult f).1 : ℂ)^(-s)`,
where `z_Q := (absNorm Q.1 : ℂ)^(-s)`.
-/
lemma prod_cpow_neg_eq_absNorm_ofMult_cpow_neg {q : ℕ} (hq : q.Prime) {s : ℂ}
    (f : ↥(tQ L q) → ℕ) :
    ∏ Q ∈ (tQ L q).attach, ((Ideal.absNorm Q.1 : ℂ) ^ (-s)) ^ (f Q) =
      ((Ideal.absNorm (QPowerNormIdeal.ofMult L hq f).1 : ℕ) : ℂ) ^ (-s) := by
  classical
  have h_step : ∀ Q : ↥(tQ L q),
      ((Ideal.absNorm Q.1 : ℂ) ^ (-s)) ^ (f Q) =
        (((Ideal.absNorm Q.1 ^ f Q : ℕ) : ℂ)) ^ (-s) := fun Q => by
    rw [← Complex.cpow_mul_nat (Ideal.absNorm Q.1 : ℂ) (-s) (f Q),
      mul_comm, Complex.natCast_cpow_natCast_mul]
    push_cast
    rfl
  simp_rw [h_step]
  rw [← cpow_finset_prod_natCast]
  congr 2
  exact (absNorm_buildIdealFromMult L f).symm

/--
The map from the sigma type `Σ k, {I // absNorm I = q^k}` to `QPowerNormIdeal L q`
that re-packages the data.
-/
private def sigmaToQPowerNormIdeal {q : ℕ}
    (x : Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k}) :
    QPowerNormIdeal L q :=
  ⟨x.2.1.1, x.2.1.2, ⟨x.1, x.2.2⟩⟩

private lemma sigmaToQPowerNormIdeal_injective {q : ℕ} (hq : q.Prime) :
    Function.Injective (sigmaToQPowerNormIdeal L (q := q)) := by
  rintro ⟨k, ⟨⟨I, hI_ne⟩, hI⟩⟩ ⟨k', ⟨⟨I', hI'_ne⟩, hI'⟩⟩ h
  unfold sigmaToQPowerNormIdeal at h
  have hI_eq : I = I' := congrArg Subtype.val h
  subst hI_eq
  have hpow_eq : q^k = q^k' := by rw [← hI, ← hI']
  have hk_eq : k = k' := Nat.pow_right_injective hq.two_le hpow_eq
  subst hk_eq
  rfl

private lemma sigmaToQPowerNormIdeal_surjective {q : ℕ} :
    Function.Surjective (sigmaToQPowerNormIdeal L (q := q)) := by
  rintro ⟨I, hI_ne, k, hI⟩
  exact ⟨⟨k, ⟨⟨I, hI_ne⟩, hI⟩⟩, rfl⟩

/-- Equiv between the sigma type `Σ k, {I // absNorm I.1 = q^k}` and `QPowerNormIdeal L q`. -/
private def sigmaQPowerNormIdealEquiv {q : ℕ} (hq : q.Prime) :
    (Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k}) ≃ QPowerNormIdeal L q :=
  Equiv.ofBijective (sigmaToQPowerNormIdeal L)
    ⟨sigmaToQPowerNormIdeal_injective L hq, sigmaToQPowerNormIdeal_surjective L⟩

/--
The fiber `{I : NonzeroIdeal L // absNorm I.1 = q^k}` is finite (and a Fintype
under classical decidability).
-/
instance qPowerFiber_finite {q : ℕ} (k : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} := by
  classical
  refine Set.Finite.to_subtype ?_
  have h_inj : Function.Injective (fun I : NonzeroIdeal L => I.1) := fun _ _ => Subtype.ext
  exact (Ideal.finite_setOf_absNorm_eq (q^k)).preimage h_inj.injOn

/--
Cardinality of the fiber `{I // absNorm I.1 = q^k}` equals `idealNormMultiplicity L (q^k)`.
-/
private lemma card_fiber {q : ℕ} (k : ℕ) :
    Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} =
      idealNormMultiplicity L (q^k) := rfl

/--
Reindex: tsum over QPowerNormIdeal equals tsum over the sigma type via
`sigmaToQPowerNormIdeal`.
-/
private lemma tsum_QPowerNormIdeal_eq_tsum_sigma {q : ℕ} (hq : q.Prime)
    (g : QPowerNormIdeal L q → ℂ) :
    ∑' (I : QPowerNormIdeal L q), g I =
      ∑' (x : Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k}),
        g (sigmaToQPowerNormIdeal L x) :=
  ((sigmaQPowerNormIdealEquiv L hq).tsum_eq g).symm

/-- Composition identity used to push functions across the `qPowerNormIdealEquiv`. -/
private lemma cpow_neg_absNorm_eq_comp {q : ℕ} (hq : q.Prime) (s : ℂ) :
    (fun I : QPowerNormIdeal L q => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
      (fun f : ↥(tQ L q) → ℕ =>
          ((Ideal.absNorm (QPowerNormIdeal.ofMult L hq f).1 : ℕ) : ℂ) ^ (-s)) ∘
        qPowerNormIdealEquiv L hq := by
  funext I
  rw [Function.comp_apply, show QPowerNormIdeal.ofMult L hq ((qPowerNormIdealEquiv L hq) I) = I
    from (qPowerNormIdealEquiv L hq).symm_apply_apply I]

/-- Summability of `I ↦ (absNorm I.1)^(-s)` on `QPowerNormIdeal L q` for `Re(s) > 1`. -/
private lemma summable_cpow_neg_qPowerNormIdeal {q : ℕ} (hq : q.Prime) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun I : QPowerNormIdeal L q => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  set z : Ideal (𝓞 L) → ℂ := fun P => (Ideal.absNorm P : ℂ) ^ (-s)
  have h_norm_lt_one : ∀ Q ∈ tQ L q, ‖z Q‖ < 1 := fun Q hQ =>
    norm_cpow_neg_lt_one_of_mem_tQ L hq hs Q hQ
  have h_pi_sum : Summable
      (fun f : ↥(tQ L q) → ℕ =>
        ((Ideal.absNorm (QPowerNormIdeal.ofMult L hq f).1 : ℕ) : ℂ) ^ (-s)) := by
    have hfun :
        (fun f : ↥(tQ L q) → ℕ =>
            ((Ideal.absNorm (QPowerNormIdeal.ofMult L hq f).1 : ℕ) : ℂ) ^ (-s)) =
          fun f : ↥(tQ L q) → ℕ =>
            ∏ Q ∈ (tQ L q).attach, ((z Q.1) ^ (f Q)) := by
      funext f
      exact (prod_cpow_neg_eq_absNorm_ofMult_cpow_neg L hq f).symm
    rw [hfun]
    exact Summable.of_norm (norm_summable_prod_pow (tQ L q) z h_norm_lt_one)
  rw [cpow_neg_absNorm_eq_comp L hq s]
  exact (qPowerNormIdealEquiv L hq).summable_iff.mpr h_pi_sum

/-- Summability over the sigma decomposition `Σ k, {I // absNorm I.1 = q^k}`. -/
private lemma summable_cpow_neg_sigma {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 1 < s.re) :
    Summable
      (fun x : Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} =>
        ((q^x.1 : ℕ) : ℂ) ^ (-s)) := by
  have h_eq : (fun x : Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} =>
        ((q^x.1 : ℕ) : ℂ) ^ (-s)) =
      (fun I : QPowerNormIdeal L q => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) ∘
        sigmaQPowerNormIdealEquiv L hq := by
    funext x
    obtain ⟨k, ⟨I, hI⟩⟩ := x
    simp only [Function.comp_apply, sigmaQPowerNormIdealEquiv, Equiv.ofBijective_apply,
      sigmaToQPowerNormIdeal, hI]
  rw [h_eq]
  exact (sigmaQPowerNormIdealEquiv L hq).summable_iff.mpr
    (summable_cpow_neg_qPowerNormIdeal L hq hs)

/--
**REF-21f3 (general c2a2 identity).** For a number field `L`, a rational prime
`q`, and `s : ℂ` with `Re(s) > 1`:
$$
\bigl(\mathrm{dedekindLocalFactorRat}_L(q, s)\bigr)^{-1}
  = \sum_{k = 0}^\infty \mathrm{idealNormMultiplicity}_L(q^k) \cdot (q^k)^{-s}.
$$

This is the generalisation of `dedekindLocalFactorRat_identity_of_uniform`
(which assumed `UniformResidueDegree`). Here, no uniform-residue-degree
hypothesis is needed.
-/
theorem dedekindLocalFactorRat_inv_eq_tsum_idealNormMultiplicity
    {q : ℕ} (hq : q.Prime) {s : ℂ} (hs : 1 < s.re) :
    (dedekindLocalFactorRat L q s)⁻¹ =
      ∑' k : ℕ, (idealNormMultiplicity L (q^k) : ℂ) * ((q^k : ℕ) : ℂ) ^ (-s) := by
  classical
  set z : Ideal (𝓞 L) → ℂ := fun P => (Ideal.absNorm P : ℂ) ^ (-s)
  have h_norm_lt_one : ∀ Q ∈ tQ L q, ‖z Q‖ < 1 := fun Q hQ =>
    norm_cpow_neg_lt_one_of_mem_tQ L hq hs Q hQ
  rw [show (dedekindLocalFactorRat L q s)⁻¹ = ∏ Q ∈ tQ L q, (1 - z Q)⁻¹ by
    unfold dedekindLocalFactorRat z; rw [← Finset.prod_inv_distrib]]
  rw [prod_one_sub_inv_eq_tsum_pi (tQ L q) z h_norm_lt_one,
    tsum_congr (fun f => prod_cpow_neg_eq_absNorm_ofMult_cpow_neg L hq f),
    ← (qPowerNormIdealEquiv L hq).tsum_eq
      (fun g : ↥(tQ L q) → ℕ =>
        ((Ideal.absNorm (QPowerNormIdeal.ofMult L hq g).1 : ℕ) : ℂ) ^ (-s)),
    tsum_congr fun I => by
      rw [show QPowerNormIdeal.ofMult L hq ((qPowerNormIdealEquiv L hq) I) = I from
        (qPowerNormIdealEquiv L hq).symm_apply_apply I],
    tsum_QPowerNormIdeal_eq_tsum_sigma L hq
      (fun I : QPowerNormIdeal L q => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))]
  rw [show (fun x : Σ k : ℕ, {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} =>
      ((Ideal.absNorm (sigmaToQPowerNormIdeal L x).1 : ℕ) : ℂ) ^ (-s)) =
      fun x => ((q^x.1 : ℕ) : ℂ) ^ (-s) by
    funext ⟨k, ⟨I, hI⟩⟩
    simp only [sigmaToQPowerNormIdeal, hI]]
  rw [(summable_cpow_neg_sigma L hq hs).tsum_sigma]
  refine tsum_congr fun k => ?_
  haveI : Fintype {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k} := Fintype.ofFinite _
  rw [tsum_fintype]
  change ∑ _b : {I : NonzeroIdeal L // Ideal.absNorm I.1 = q^k}, ((q^k : ℕ) : ℂ) ^ (-s) =
    (idealNormMultiplicity L (q^k) : ℂ) * ((q^k : ℕ) : ℂ) ^ (-s)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card, card_fiber]
  ring

end WeakSplitting

end BernoulliRegular
