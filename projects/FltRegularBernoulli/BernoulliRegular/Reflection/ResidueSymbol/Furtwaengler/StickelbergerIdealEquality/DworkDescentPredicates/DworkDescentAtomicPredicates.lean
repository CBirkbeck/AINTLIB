module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkAssembly
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CyclotomicLocalSetup
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceFormGalois


/-!
# `StickelbergerIdealEquality` from a `FullTeichDworkSetup`

This file provides the substantive valuation-descent content of c.1
(`REF-18c2d-main-c.1`) by showing how to assemble a
`StickelbergerIdealEquality (S.Q.under (𝓞 K))` from a
`FullTeichDworkSetup S` together with a coverage hypothesis on the
Galois orbit of the descent prime.

## Strategy

The Dwork bundle gives the EXACT `Q`-adic order
`S.gaussSumInt a ∈ S.Q^(stickOrdOrd a) ∧ S.gaussSumInt a ∉ S.Q^(stickOrdOrd a + 1)`
at the SINGLE prime `S.Q ⊂ 𝓞 R'` for each `a ∈ [1, p-1]`. The route
to the multi-conjugate Stickelberger ideal in `𝓞 K` factors through
the descent prime `q_K = S.Q.under (𝓞 K)` and the Galois orbit
`cyclotomicConjugates q_K`:

1. **Per-`a` descent witness** (`StickelbergerPerConjugateDescent`):
   for each `a`, the existence of `γ_a ∈ 𝓞 K` whose image in `𝓞 R'`
   equals `S.gaussSumInt a ^ p` and whose `descentPrime`-adic order is
   `p · stickOrdOrd a / e` where `e = descentRamificationIdx`.

2. **Galois-orbit coverage** (`StickelbergerOrbitCoverage`): the
   Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` admits a
   single global generator `γ ∈ 𝓞 K` whose ideal factorization at each
   conjugate matches the prescribed exponent.

3. **Final assembly** (`stickelbergerIdealEquality_of_dwork_witness`):
   under both witnesses, the principal ideal `(γ)` equals
   `stickelbergerIdeal q_K`, and so `StickelbergerIdealEquality q_K`
   holds.

The current file delivers (1) and the **conditional** (3) under (2).
The unconditional (2) requires a separate per-conjugate bundle for
each Galois conjugate prime above `ℓ` (one bundle per representative
of the Galois orbit of `S.Q`); that step is left as a coverage
hypothesis here, packaged as the `Prop` predicate
`StickelbergerOrbitCoverage`.

## Why split

The full unconditional c.1 builds a single global generator from
multiple per-conjugate bundles by orbit-summing. That assembly is the
substantive remaining content. The conditional form delivered here
already discharges all the **valuation-descent** content (per-`a`
exact orders, ramification descent, Dwork EXACT-order data); only the
**orbit-coverage** combinatorics remain.

## Files

* Per-`a` exact-order descent: theorems
  `gaussSumInt_pow_descentPrime_pow_mul_stickOrdOrd`,
  `gaussSumInt_pow_not_mem_descentPrime_pow_mul_stickOrdOrd_succ` (in
  this file, on `FullTeichDworkSetup`).
* Final `StickelbergerIdealEquality` constructor: theorem
  `stickelbergerIdealEquality_of_orbitCoverage`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichDworkSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']
variable [IsScalarTower ℤ (𝓞 K) (𝓞 R')]

variable (S : FullTeichDworkSetup ℓ p k K R')

/-! ### Per-`a` exact-order descent at `descentPrime`

Combining the Dwork EXACT-order theorem
`gaussSumInt_qadic_ord_at_prime_ord_dwork` with the ramification-descent
iff `mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul`, we transport
the Q-adic exact order of `S.gaussSumInt a^p` to a `descentPrime`-adic
order on a Galois-fixed lift `γ_a ∈ 𝓞 K`.
-/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The Dwork-EXACT-order Q-adic containment for `S.gaussSumInt a ^ p`. -/
theorem gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) := by
  classical
  have h := (S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂).1
  -- h : S.gaussSumInt a ∈ S.Q ^ stickOrdOrd a.
  -- Raise to pth power: gaussSumInt^p ∈ Q^(p · stickOrdOrd a).
  have hpow := Ideal.pow_mem_pow h p
  rwa [← pow_mul, mul_comm] at hpow

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The Dwork-EXACT-order Q-adic non-containment for
`S.gaussSumInt a ^ p`. -/
theorem gaussSumInt_pow_p_not_mem_Q_pow_p_mul_stickOrdOrd_succ
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p ∉ S.Q ^ (p * S.stickOrdOrd a + 1) := by
  classical
  set x : 𝓞 R' := S.gaussSumInt a with hx_def
  set s : ℕ := S.stickOrdOrd a with hs_def
  have h_exact := S.gaussSumInt_qadic_ord_at_prime_ord_dwork a ha₁ ha₂
  have h_mem : x ∈ S.Q ^ s := by
    simpa [x, s, hx_def, hs_def] using h_exact.1
  have h_not : x ∉ S.Q ^ (s + 1) := by
    simpa [x, s, hx_def, hs_def] using h_exact.2
  have hQ_ne : S.Q ≠ ⊥ := S.toConcreteStickelbergerSetup.Q_ne_bot'
  have hQ_prime : Prime S.Q :=
    Ideal.prime_of_isPrime hQ_ne S.toConcreteStickelbergerSetup.hQ_prime
  have h_dvd : S.Q ^ s ∣ Ideal.span ({x} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_mem
  have h_not_dvd : ¬ S.Q ^ (s + 1) ∣ Ideal.span ({x} : Set (𝓞 R')) := fun h_dvd' =>
    h_not ((Ideal.span_singleton_le_iff_mem (I := S.Q ^ (s + 1))).mp
      (Ideal.dvd_iff_le.mp h_dvd'))
  have h_emult :
      emultiplicity S.Q (Ideal.span ({x} : Set (𝓞 R'))) = (s : ℕ∞) :=
    emultiplicity_eq_coe.mpr ⟨h_dvd, h_not_dvd⟩
  have h_emult_pow :
      emultiplicity S.Q (Ideal.span ({x} : Set (𝓞 R')) ^ p) =
        ((p * s : ℕ) : ℕ∞) := by
    rw [emultiplicity_pow hQ_prime, h_emult]
    norm_num
  intro h_mem_pow
  have h_dvd_pow :
      S.Q ^ (p * s + 1) ∣ Ideal.span ({x ^ p} : Set (𝓞 R')) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_mem_pow
  have h_le :
      ((p * s + 1 : ℕ) : ℕ∞) ≤
        emultiplicity S.Q (Ideal.span ({x ^ p} : Set (𝓞 R')) : Ideal (𝓞 R')) :=
    pow_dvd_iff_le_emultiplicity.mp h_dvd_pow
  have h_span_pow :
      Ideal.span ({x ^ p} : Set (𝓞 R')) =
        Ideal.span ({x} : Set (𝓞 R')) ^ p :=
    (Ideal.span_singleton_pow x p).symm
  rw [h_span_pow, h_emult_pow] at h_le
  have h_le_nat : p * s + 1 ≤ p * s := by
    exact_mod_cast h_le
  exact (Nat.not_succ_le_self (p * s)) h_le_nat

/-- **Per-`a` descent at descentPrime, exact-power form.** Given a
Galois-fixed lift `γ_a` of `S.gaussSumInt a ^ p` and the Dwork EXACT-order
data, the lift `γ_a` lies in `S.descentPrime ^ n` for any `n` with
`e * n ≤ p * stickOrdOrd a`. -/
theorem descentPrime_pow_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    {n : ℕ}
    (hn : S.toConcreteStickelbergerSetup.descentRamificationIdx * n ≤
            p * S.stickOrdOrd a) :
    γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^ n := by
  -- Step 1: gaussSumInt a^p ∈ Q^(p · stickOrdOrd a).
  have h_image_mem : S.gaussSumInt a ^ p ∈ S.Q ^ (p * S.stickOrdOrd a) :=
    S.gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd ha₁ ha₂
  -- Step 2: transfer to algebraMap γ via hγ.
  have h_image :
      algebraMap (𝓞 K) (𝓞 R') γ ∈ S.Q ^ (p * S.stickOrdOrd a) := hγ ▸ h_image_mem
  -- Step 3: monotonicity Q^(p · stickOrdOrd a) ≤ Q^(e · n).
  have h_pow_le :
      S.Q ^ (p * S.stickOrdOrd a) ≤
        S.Q ^ (S.toConcreteStickelbergerSetup.descentRamificationIdx * n) :=
    Ideal.pow_le_pow_right hn
  have h_image' :
      algebraMap (𝓞 K) (𝓞 R') γ ∈
        S.Q ^ (S.toConcreteStickelbergerSetup.descentRamificationIdx * n) :=
    h_pow_le h_image
  -- Step 4: apply iff form to get descentPrime^n membership.
  exact (S.toConcreteStickelbergerSetup.mem_descentPrime_pow_iff_algebraMap_mem_Q_pow_mul
    hγ_ne n).mpr h_image'

/-- **Maximal-power form**: the lift `γ_a` lies in
`descentPrime ^ (p · stickOrdOrd a / e)` (where `e = descentRamificationIdx`). -/
theorem descentPrime_pow_div_mem_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
      ((p * S.stickOrdOrd a) / S.toConcreteStickelbergerSetup.descentRamificationIdx) := by
  apply S.descentPrime_pow_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ
  rw [mul_comm]
  exact Nat.div_mul_le_self (p * S.stickOrdOrd a)
    S.toConcreteStickelbergerSetup.descentRamificationIdx

/-- **Exact descentPrime order from Dwork exact order.**

If `descentRamificationIdx ∣ p * stickOrdOrd a`, then a descended lift of
`S.gaussSumInt a ^ p` has exact `descentPrime`-adic order
`p * stickOrdOrd a / descentRamificationIdx`. -/
theorem descentPrime_pow_div_mem_and_not_succ_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    (h_div :
      S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
        p * S.stickOrdOrd a) :
    γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
        ((p * S.stickOrdOrd a) /
          S.toConcreteStickelbergerSetup.descentRamificationIdx) ∧
      γ ∉ S.toConcreteStickelbergerSetup.descentPrime ^
        (((p * S.stickOrdOrd a) /
          S.toConcreteStickelbergerSetup.descentRamificationIdx) + 1) := by
  classical
  set e := S.toConcreteStickelbergerSetup.descentRamificationIdx with he_def
  set n := (p * S.stickOrdOrd a) / e with hn_def
  have h_en : e * n = p * S.stickOrdOrd a := by
    rw [hn_def, mul_comm]
    exact Nat.div_mul_cancel h_div
  rw [S.toConcreteStickelbergerSetup.mem_descentPrime_pow_and_not_succ_iff hγ_ne n]
  constructor
  · rw [hγ, h_en]
    exact S.gaussSumInt_pow_p_mem_Q_pow_p_mul_stickOrdOrd ha₁ ha₂
  · intro h_mem
    have he_pos : 0 < e := by
      simpa [e, he_def] using
        S.toConcreteStickelbergerSetup.descentRamificationIdx_pos
    have h_succ_le : p * S.stickOrdOrd a + 1 ≤ e * (n + 1) := by
      rw [Nat.mul_succ, h_en]
      omega
    have h_pow_le : S.Q ^ (e * (n + 1)) ≤
        S.Q ^ (p * S.stickOrdOrd a + 1) :=
      Ideal.pow_le_pow_right h_succ_le
    exact S.gaussSumInt_pow_p_not_mem_Q_pow_p_mul_stickOrdOrd_succ ha₁ ha₂
      (h_pow_le (hγ ▸ h_mem))

/-- **Exact descentPrime emultiplicity from Dwork exact order.**

This is the valuation form of
`descentPrime_pow_div_mem_and_not_succ_of_dwork_exactOrder`: a descended
lift of `S.gaussSumInt a ^ p` has exactly
`p * stickOrdOrd a / descentRamificationIdx` copies of the descent prime
in its principal ideal. -/
theorem descentPrime_emultiplicity_eq_of_dwork_exactOrder
    [FaithfulSMul (𝓞 K) (𝓞 R')]
    [Module.IsTorsionFree (𝓞 K) (𝓞 R')]
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p)
    (h_div :
      S.toConcreteStickelbergerSetup.descentRamificationIdx ∣
        p * S.stickOrdOrd a) :
    emultiplicity S.toConcreteStickelbergerSetup.descentPrime
        (Ideal.span ({γ} : Set (𝓞 K))) =
      (((p * S.stickOrdOrd a) /
        S.toConcreteStickelbergerSetup.descentRamificationIdx : ℕ) : ℕ∞) := by
  classical
  have h_exact :=
    S.descentPrime_pow_div_mem_and_not_succ_of_dwork_exactOrder
      ha₁ ha₂ hγ_ne hγ h_div
  refine emultiplicity_eq_coe.mpr ⟨?_, ?_⟩
  · rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h_exact.1
  · intro h_dvd
    exact h_exact.2
      ((Ideal.span_singleton_le_iff_mem
        (I := S.toConcreteStickelbergerSetup.descentPrime ^
          (((p * S.stickOrdOrd a) /
            S.toConcreteStickelbergerSetup.descentRamificationIdx) + 1))).mp
        (Ideal.dvd_iff_le.mp h_dvd))

/-- **Existence form** combining Dwork EXACT-order + Galois descent +
trace-form psi-shift: the lift `γ_a` exists and lies in the precise
descentPrime-power. Uses the trace-form Galois-compatibility from
`TraceFormGalois.lean` to discharge the psi-shift content. -/
theorem exists_descentPrime_pow_mul_stickOrdOrd_div
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (h_ne_zero : S.gaussSumInt a ^ p ≠ 0) :
    ∃ γ : 𝓞 K, γ ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p ∧
      γ ∈ S.toConcreteStickelbergerSetup.descentPrime ^
        ((p * S.stickOrdOrd a) /
          S.toConcreteStickelbergerSetup.descentRamificationIdx) := by
  classical
  haveI := S.toConcreteStickelbergerSetup.isGalois_K_R'_of_cyclotomic
  haveI := S.toConcreteStickelbergerSetup.finiteDimensional_K_R'_of_cyclotomic
  haveI := S.toConcreteStickelbergerSetup.faithfulSMul_OK_OR'_of_cyclotomic
  -- Use trace-form Galois compatibility from TraceFormGalois.lean.
  have h_psi :=
    S.toTraceFormStickelbergerSetup.isGalPsiShiftCompatible_traceForm
  obtain ⟨γ, hγ_ne, hγ_eq, _⟩ :=
    S.toConcreteStickelbergerSetup.exists_descentPrime_pow_div_of_psi_shift
      ha₁ ha₂ h_psi h_ne_zero
  refine ⟨γ, hγ_ne, hγ_eq, ?_⟩
  exact S.descentPrime_pow_div_mem_of_dwork_exactOrder ha₁ ha₂ hγ_ne hγ_eq

/-! ### Coverage of the Stickelberger orbit

The Stickelberger ideal `q_K^Θ = ∏_a (σ_{a^{-1}} q_K)^a.val` is a
product over the Galois orbit of `q_K`. Its principal generator —
which is what `StickelbergerIdealEquality` asserts to exist — must
have the correct ideal-multiplicity at EVERY conjugate prime. The
single bundle `S` only sees one prime in `𝓞 R'`; capturing the
multiplicity at all conjugate primes simultaneously requires either:
(a) a per-conjugate bundle, or (b) a coverage hypothesis.

We package (b) as a `Prop` predicate `StickelbergerOrbitCoverage`,
which the consumer must discharge to obtain the full
`StickelbergerIdealEquality`. -/

/-- **Coverage predicate**: a generator `γ ∈ 𝓞 K` whose principal ideal
equals the Stickelberger ideal at the bundle's descentPrime. This is the
content of c.1 packaged into a single ∃ — to be discharged by a multi-
conjugate descent or an absolute-order argument. -/
def StickelbergerOrbitCoverage : Prop :=
  ∃ γ : 𝓞 K, γ ≠ 0 ∧
    Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Final theorem.** Given a `FullTeichDworkSetup S` and a coverage
witness, we obtain `StickelbergerIdealEquality (S.Q.under (𝓞 K))`. -/
theorem stickelbergerIdealEquality_of_orbitCoverage
    (h_cov : S.StickelbergerOrbitCoverage) :
    StickelbergerIdealEquality (p := p) (K := K)
      (S.Q.under (𝓞 K)) := by
  refine ⟨?_⟩
  -- Unfold descentPrime in the coverage hypothesis.
  unfold StickelbergerOrbitCoverage
    ConcreteStickelbergerSetup.descentPrime at h_cov
  exact h_cov

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Constructor for the coverage predicate** from a single global
generator and the per-conjugate exponent equalities. The user supplies
γ together with the witness that its principal ideal equals the
Stickelberger product. -/
theorem stickelbergerOrbitCoverage_of_generator
    (γ : 𝓞 K) (hγ_ne : γ ≠ 0)
    (hγ_eq : Ideal.span ({γ} : Set (𝓞 K)) =
      stickelbergerIdeal (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime) :
    S.StickelbergerOrbitCoverage :=
  ⟨γ, hγ_ne, hγ_eq⟩

/-- **Per-conjugate descent witness** — what each individual `a` gives.
At each Galois conjugate, the descent gives a γ_a ∈ 𝓞 K with prescribed
descentPrime-adic order. This packages it as a tuple of witnesses. -/
def StickelbergerPerConjugateDescent : Prop :=
  ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 →
    S.gaussSumInt a ^ p ≠ 0 →
    ∃ γ_a : 𝓞 K, γ_a ≠ 0 ∧
      algebraMap (𝓞 K) (𝓞 R') γ_a = S.gaussSumInt a ^ p ∧
      γ_a ∈ S.toConcreteStickelbergerSetup.descentPrime ^
        ((p * S.stickOrdOrd a) /
          S.toConcreteStickelbergerSetup.descentRamificationIdx)

/-- **Per-conjugate descent always holds for `FullTeichDworkSetup`.**
This is the substantive content of c.1.4 + Dwork-EXACT-order. -/
theorem stickelbergerPerConjugateDescent :
    S.StickelbergerPerConjugateDescent :=
  fun _ ha₁ ha₂ h_ne_zero =>
    S.exists_descentPrime_pow_mul_stickOrdOrd_div ha₁ ha₂ h_ne_zero

/-! ### Atomic decomposition of `StickelbergerOrbitCoverage`

The orbit-coverage predicate
`∃ γ ∈ 𝓞 K, γ ≠ 0 ∧ Ideal.span {γ} = stickelbergerIdeal q_K`
admits a clean atomic decomposition into three Prop predicates whose
combination is mathematically equivalent to the coverage:

1. `StickelbergerExactConjugateExponents γ`: per-conjugate exact
   exponent at each Galois conjugate of `q_K`.
2. `StickelbergerSupportInOrbit γ`: support of `(γ)` is contained in
   the cyclotomic Galois orbit of `q_K`.
3. `StickelbergerIdealConjugateMultiplicity`: each cyclotomic
   conjugate appears in `normalizedFactors (stickelbergerIdeal q_K)`
   with multiplicity exactly `(a : ZMod p).val`.

The first two are properties of γ; the third is a structural property
of the Stickelberger ideal itself (true under faithfulness of the
Galois action on the orbit, i.e., the split case).

The substantive theorem `stickelbergerOrbitCoverage_of_atomic_with_stickMul`
provides the END-TO-END atomic discharge: given all three predicates,
the orbit coverage holds. The proof goes through both divisibility
directions (`(γ) ∣ stick` and `stick ∣ (γ)`) and uses
`associated_iff_eq` (which holds in `Ideal R` since `(Ideal R)ˣ` is
unique). -/

/-- **Atomic predicate: per-conjugate exact exponent.**

For `γ ∈ 𝓞 K \ {0}` and the descent prime `q_K`, this asserts the
exact `(σ_{a^{-1}} q_K)`-adic valuation of `γ` is `(a : ZMod p).val`
for every `a ∈ (ZMod p)ˣ`.

In Dedekind-domain language: `(σ_{a^{-1}} q_K)^{a.val} ∣ (γ)` and
`(σ_{a^{-1}} q_K)^{a.val + 1} ∤ (γ)`, equivalently:
`emultiplicity (σ_{a^{-1}} q_K) (γ) = a.val`. -/
def StickelbergerExactConjugateExponents (γ : 𝓞 K) : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime)
        (Ideal.span ({γ} : Set (𝓞 K))) =
      ((a : ZMod p).val : ℕ∞)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The cyclotomic Galois action on ideals as a multiplicative equivalence.

This lets multiplicity transport use the standard
`emultiplicity_map_eq` theorem rather than reproving divisibility
invariance from scratch. -/
noncomputable def cyclotomicGaloisConjugateIdealMulEquiv
    (a : CyclotomicUnitDelta p) :
    Ideal (𝓞 K) ≃* Ideal (𝓞 K) where
  toFun := cyclotomicGaloisConjugate (p := p) (K := K) a
  invFun := cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
  left_inv I := by
    rw [← cyclotomicGaloisConjugate_mul, inv_mul_cancel,
      cyclotomicGaloisConjugate_one]
  right_inv I := by
    rw [← cyclotomicGaloisConjugate_mul, mul_inv_cancel,
      cyclotomicGaloisConjugate_one]
  map_mul' I J := cyclotomicGaloisConjugate_mul_ideal a I J

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Cyclotomic Galois conjugation preserves ideal emultiplicity. -/
theorem emultiplicity_cyclotomicGaloisConjugate
    (a : CyclotomicUnitDelta p) (I J : Ideal (𝓞 K)) :
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a I)
        (cyclotomicGaloisConjugate (p := p) (K := K) a J) =
      emultiplicity I J :=
  emultiplicity_map_eq
    (cyclotomicGaloisConjugateIdealMulEquiv (p := p) (K := K) a)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Galois conjugation transports a principal ideal generated by `γ` to
the principal ideal generated by the conjugate of `γ`. -/
theorem cyclotomicGaloisConjugate_span_singleton'
    (a : CyclotomicUnitDelta p) (γ : 𝓞 K) :
    cyclotomicGaloisConjugate (p := p) (K := K) a
        (Ideal.span ({γ} : Set (𝓞 K))) =
      Ideal.span
        ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K)) := by
  unfold cyclotomicGaloisConjugate
  rw [Ideal.map_span, Set.image_singleton]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Multiplicity at a conjugate prime is the selected-prime multiplicity of
the conjugated element. -/
theorem emultiplicity_conjugatePrime_span_eq_descentPrime_conjugateElement
    (a : CyclotomicUnitDelta p) (q : Ideal (𝓞 K)) (γ : 𝓞 K) :
    emultiplicity
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q)
        (Ideal.span ({γ} : Set (𝓞 K))) =
      emultiplicity q
        (Ideal.span
          ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K))) := by
  have h :=
    emultiplicity_cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹ q
      (Ideal.span
        ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K)))
  rw [cyclotomicGaloisConjugate_span_singleton'] at h
  have h_elem :
      cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
          (cyclotomicRingOfIntegersEquiv (p := p) K a γ) = γ := by
    rw [← cyclotomicRingOfIntegersEquiv_mul_apply, inv_mul_cancel,
      cyclotomicRingOfIntegersEquiv_one_apply]
  rw [h_elem] at h
  simpa using h

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- To prove the exact Stickelberger exponents of `γ`, it suffices to prove
the selected-prime valuation of every cyclotomic conjugate of `γ`. -/
theorem stickelbergerExactConjugateExponents_of_conjugate_descentPrime_emultiplicity
    {γ : 𝓞 K}
    (h :
      ∀ a : CyclotomicUnitDelta p,
        emultiplicity S.toConcreteStickelbergerSetup.descentPrime
            (Ideal.span
              ({cyclotomicRingOfIntegersEquiv (p := p) K a γ} : Set (𝓞 K))) =
          ((a : ZMod p).val : ℕ∞)) :
    S.StickelbergerExactConjugateExponents γ := by
  intro a
  rw [emultiplicity_conjugatePrime_span_eq_descentPrime_conjugateElement]
  exact h a

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Atomic predicate: support inside cyclotomic orbit.**

For `γ ∈ 𝓞 K \ {0}`, this asserts the prime support of `(γ)` is
contained in the cyclotomic Galois orbit of `q_K`: every prime ideal
factor of `(γ)` is a Galois conjugate of `q_K`. -/
def StickelbergerSupportInOrbit (γ : 𝓞 K) : Prop :=
  ∀ b : Ideal (𝓞 K),
    b ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({γ} : Set (𝓞 K))) →
    b ∈ cyclotomicConjugates (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime

/-! ### Discharging `StickelbergerSupportInOrbit` from descent

For `γ ∈ 𝓞 K` whose image under `algebraMap (𝓞 K) (𝓞 R')` equals
`S.gaussSumInt a ^ p`, the prime support of `(γ)` is automatically
inside the cyclotomic Galois orbit of `S.descentPrime`.

The proof uses the Gauss-sum norm relation
`gaussSum (χ^a) ψ · gaussSum (χ^a)⁻¹ ψ⁻¹ = #k` (in `𝓞 R'`, a domain),
which raised to the `p`-th power gives
`gaussSumInt(a)^p · (gaussSum (χ^a)⁻¹ ψ⁻¹)^p = (#k)^p = ℓ^(f·p)`.
Combined with `prime_mem_of_mul_eq_pow`: any prime `B ⊂ 𝓞 R'`
containing `gaussSumInt(a)^p` contains `(ℓ : 𝓞 R')`.

Going-up (`Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`)
lifts a prime `b ⊂ 𝓞 K` containing `γ` to a prime `B ⊂ 𝓞 R'` with
`B.under (𝓞 K) = b` and `algebraMap γ ∈ B`. Then `(ℓ : 𝓞 R') ∈ B`
gives `(ℓ : 𝓞 K) ∈ b`, so `b` lies above `ℓ`. The Galois-transitivity
result `Q_under_mem_cyclotomicConjugates` then places `b` in
`cyclotomicConjugates S.descentPrime`. -/

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- The integral additive character `S.psiInt` is primitive.

Derived from `S.psi.IsPrimitive` via the injective `algebraMap (𝓞 R') R'`:
since `S.psi = (algebraMap _ _).compAddChar S.psiInt`, primitivity of
`S.psi` forces `S.psiInt ≠ 1`, and over a field `k`, nontriviality is
equivalent to primitivity (`AddChar.IsPrimitive.of_ne_one`). -/
theorem psiInt_isPrimitive :
    S.toConcreteStickelbergerSetup.psiInt.IsPrimitive := by
  -- It suffices to show psiInt ≠ 1, then apply IsPrimitive.of_ne_one over k.
  apply AddChar.IsPrimitive.of_ne_one
  intro h_eq
  -- If psiInt = 1, then S.psi = 1, contradicting S.hpsi.IsPrimitive.
  have h_psi_eq : S.toConcreteStickelbergerSetup.psi = 1 := by
    ext x
    rw [AddChar.one_apply]
    have h_alg := S.toConcreteStickelbergerSetup.algebraMap_psiInt x
    have h_one : S.toConcreteStickelbergerSetup.psiInt x = (1 : 𝓞 R') := by
      have := DFunLike.congr_fun h_eq x
      simpa [AddChar.one_apply] using this
    rw [h_one, map_one] at h_alg
    exact h_alg.symm
  -- S.psi.IsPrimitive contradicts S.psi = 1: with x = 1 ≠ 0,
  -- mulShift psi 1 = psi = 1, contradicting IsPrimitive.
  have h_one_ne : (1 : k) ≠ 0 := one_ne_zero
  have h_shift := S.toConcreteStickelbergerSetup.hpsi h_one_ne
  apply h_shift
  ext y
  simp [h_psi_eq, AddChar.one_apply]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Norm relation for `gaussSumInt(a)`.** In `𝓞 R'` (a domain),
the Gauss-sum norm relation gives
`gaussSumInt(a) · gaussSum (residueCharInt^a)⁻¹ psiInt⁻¹ = #k`. -/
theorem gaussSumInt_mul_inv_eq_card
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a *
        gaussSum (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹ =
      (Fintype.card k : 𝓞 R') := by
  have h_ne_one := S.toConcreteStickelbergerSetup.residueCharInt_pow_ne_one ha₁ ha₂
  have h_prim := S.psiInt_isPrimitive
  exact gaussSum_mul_gaussSum_eq_card (R := k) (R' := 𝓞 R')
    (χ := S.toConcreteStickelbergerSetup.residueCharInt ^ a)
    (ψ := S.toConcreteStickelbergerSetup.psiInt) h_ne_one h_prim

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Power form** of the Gauss-sum norm in `𝓞 R'`:
`gaussSumInt(a)^p · (gaussSum (residueCharInt^a)⁻¹ psiInt⁻¹)^p = (ℓ : 𝓞 R')^(f·p)`. -/
theorem gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    S.gaussSumInt a ^ p *
        gaussSum (S.toConcreteStickelbergerSetup.residueCharInt ^ a)⁻¹
          S.toConcreteStickelbergerSetup.psiInt⁻¹ ^ p =
      (ℓ : 𝓞 R') ^ (S.toConcreteStickelbergerSetup.f * p) := by
  rw [← mul_pow, S.gaussSumInt_mul_inv_eq_card ha₁ ha₂,
    S.toConcreteStickelbergerSetup.card_k_eq, Nat.cast_pow, ← pow_mul]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Support of `gaussSumInt(a)^p` lies above `ℓ` in `𝓞 R'`.**
For any prime `B ⊂ 𝓞 R'` containing `S.gaussSumInt a ^ p`, we have
`(ℓ : 𝓞 R') ∈ B`. -/
theorem ell_mem_of_gaussSumInt_pow_p_mem
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {B : Ideal (𝓞 R')} [B.IsPrime]
    (h_in : S.gaussSumInt a ^ p ∈ B) :
    (ℓ : 𝓞 R') ∈ B :=
  prime_mem_of_mul_eq_pow
    (S.gaussSumInt_pow_p_mul_inv_pow_p_eq_ell_pow ha₁ ha₂) h_in

/-- **Discharge of `StickelbergerSupportInOrbit` for descent of
`gaussSumInt(a)^p`.** Given `γ ∈ 𝓞 K` non-zero whose image in `𝓞 R'` is
`S.gaussSumInt a ^ p`, the prime support of `(γ)` lies in the cyclotomic
Galois orbit of `S.descentPrime`. -/
theorem stickelbergerSupportInOrbit_of_descentGaussSum
    {a : ℕ} (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    {γ : 𝓞 K} (hγ_ne : γ ≠ 0)
    (hγ : algebraMap (𝓞 K) (𝓞 R') γ = S.gaussSumInt a ^ p) :
    S.StickelbergerSupportInOrbit γ := by
  classical
  intro b hb_in
  -- Step 1: extract structural facts on `b`.
  have hb_prime_in_uf :=
    UniqueFactorizationMonoid.prime_of_normalized_factor b hb_in
  haveI hb_isPrime : b.IsPrime := Ideal.isPrime_of_prime hb_prime_in_uf
  have hb_ne : b ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot]
    exact hb_prime_in_uf.ne_zero
  have hspan_ne : Ideal.span ({γ} : Set (𝓞 K)) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  -- γ ∈ b: from b ∣ (γ).
  have hb_dvd : b ∣ Ideal.span ({γ} : Set (𝓞 K)) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb_in
  have hγ_in_b : γ ∈ b := by
    have h_span_le : Ideal.span ({γ} : Set (𝓞 K)) ≤ b := Ideal.le_of_dvd hb_dvd
    exact h_span_le (Ideal.subset_span (Set.mem_singleton _))
  -- Step 2: lift `b` to a prime `B ⊂ 𝓞 R'` with `B.under (𝓞 K) = b`.
  have hker_le : RingHom.ker (algebraMap (𝓞 K) (𝓞 R')) ≤ b := by
    rw [NumberField.RingOfIntegers.ker_algebraMap_eq_bot K R']
    exact bot_le
  obtain ⟨B, hB_prime, hB_under⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := 𝓞 K) (S := 𝓞 R') b hker_le
  haveI : B.IsPrime := hB_prime
  -- Step 3: algebraMap γ ∈ B (since γ ∈ b = B.comap algebraMap).
  have h_algMap_in_B : algebraMap (𝓞 K) (𝓞 R') γ ∈ B := by
    have : γ ∈ B.comap (algebraMap (𝓞 K) (𝓞 R')) := hB_under ▸ hγ_in_b
    rwa [Ideal.mem_comap] at this
  -- Step 4: gaussSumInt(a)^p ∈ B.
  have h_gauss_in_B : S.gaussSumInt a ^ p ∈ B := hγ ▸ h_algMap_in_B
  -- Step 5: (ℓ : 𝓞 R') ∈ B.
  have h_ell_in_B : (ℓ : 𝓞 R') ∈ B := S.ell_mem_of_gaussSumInt_pow_p_mem ha₁ ha₂ h_gauss_in_B
  -- Step 6: invoke `Q_under_mem_cyclotomicConjugates` with `q = S.descentPrime`,
  -- `Q = B`. We get `B.under (𝓞 K) ∈ cyclotomicConjugates S.descentPrime`,
  -- i.e., `b ∈ cyclotomicConjugates S.descentPrime`.
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have h_descent_under :
      S.toConcreteStickelbergerSetup.descentPrime.under ℤ =
        Ideal.span ({(ℓ : ℤ)} : Set ℤ) := by
    -- S.descentPrime is a non-zero maximal ideal of 𝓞 K containing ℓ.
    have h_ell_in : (ℓ : 𝓞 K) ∈ S.toConcreteStickelbergerSetup.descentPrime :=
      S.toConcreteStickelbergerSetup.descentPrime_contains_ell
    have h_ell_in_under : (ℓ : ℤ) ∈
        S.toConcreteStickelbergerSetup.descentPrime.under ℤ := by
      rw [show S.toConcreteStickelbergerSetup.descentPrime.under ℤ =
          Ideal.comap (algebraMap ℤ (𝓞 K))
            S.toConcreteStickelbergerSetup.descentPrime from rfl]
      rw [Ideal.mem_comap]
      rw [show (algebraMap ℤ (𝓞 K) (ℓ : ℤ)) = (ℓ : 𝓞 K) from by push_cast; rfl]
      exact h_ell_in
    have h_under_ne :
        S.toConcreteStickelbergerSetup.descentPrime.under ℤ ≠ ⊥ := by
      intro hbot
      rw [hbot, Ideal.mem_bot] at h_ell_in_under
      exact (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero : (ℓ : ℤ) ≠ 0)
        h_ell_in_under
    haveI : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).IsPrime :=
      Ideal.IsPrime.under ℤ (P := S.toConcreteStickelbergerSetup.descentPrime)
    haveI : (S.toConcreteStickelbergerSetup.descentPrime.under ℤ).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance h_under_ne
    haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsPrime := by
      rw [Ideal.span_singleton_prime
        (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)]
      exact Nat.prime_iff_prime_int.mp (Fact.out : ℓ.Prime)
    haveI : (Ideal.span ({(ℓ : ℤ)} : Set ℤ)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
    -- Both maximal, both contain (ℓ), so equal.
    have h2 :
        Ideal.span ({(ℓ : ℤ)} : Set ℤ) ≤
          S.toConcreteStickelbergerSetup.descentPrime.under ℤ := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact h_ell_in_under
    exact (Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.IsMaximal.ne_top inferInstance) h2).symm
  have h_descent_ne : S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.toConcreteStickelbergerSetup.descentPrime_ne_bot
  -- Apply Q_under_mem_cyclotomicConjugates.
  have h_b_eq : B.under (𝓞 K) = b := hB_under
  have h_orbit :
      B.under (𝓞 K) ∈ cyclotomicConjugates (p := p) (K := K)
        S.toConcreteStickelbergerSetup.descentPrime :=
    Q_under_mem_cyclotomicConjugates (K := K) (p := p) (ℓ := ℓ)
      h_descent_ne h_descent_under B h_ell_in_B
  rw [h_b_eq] at h_orbit
  exact h_orbit

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Atomic predicate: per-conjugate exponent in the Stickelberger ideal.**

For each `a ∈ (ZMod p)ˣ`, the count of `σ_{a^{-1}} q_K` in
`normalizedFactors (stickelbergerIdeal q_K)` equals `(a : ZMod p).val`.

This is a purely combinatorial statement about the Stickelberger
ideal: it holds under `StickelbergerOrbitFaithful` (distinct conjugates
⟹ each appears once with its prescribed exponent). It is isolated as a
Prop so the orbit-coverage discharge becomes a clean reduction. -/
def StickelbergerIdealConjugateMultiplicity : Prop :=
  ∀ a : CyclotomicUnitDelta p,
    (UniqueFactorizationMonoid.normalizedFactors
        (stickelbergerIdeal (p := p) (K := K)
          S.toConcreteStickelbergerSetup.descentPrime)).count
      (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime) =
    ((a : ZMod p).val : ℕ)

/-! ### Discharge of `StickelbergerIdealConjugateMultiplicity` from orbit faithfulness

The structural multiplicity predicate `StickelbergerIdealConjugateMultiplicity`
says each `σ_{a⁻¹} q_K` appears in `normalizedFactors (stickelbergerIdeal q_K)`
with multiplicity exactly `a.val`. Since `stickelbergerIdeal q_K = ∏_a (σ_{a⁻¹} q_K)^a.val`,
this reduces to:

* The conjugates `σ_{a⁻¹} q_K` are pairwise distinct (orbit faithfulness),
* Each conjugate is irreducible (prime + non-zero), hence
  `normalizedFactors ((σ_{a⁻¹} q_K)^a.val) = a.val • {σ_{a⁻¹} q_K}`,
* The total count picks out the unique matching index.

The faithfulness hypothesis is automatic in the **split case** (when `ℓ ≡ 1
mod p`, ramification = inertia = 1, orbit has size `p − 1`). We package it
as a separate `Prop` so the discharge is clean and reusable. -/

/-- The descentPrime is non-bot. -/
private theorem descentPrime_ne_bot' :
    S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
  S.toConcreteStickelbergerSetup.descentPrime_ne_bot

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Each Galois conjugate of `descentPrime` is non-bot. -/
theorem cyclotomicGaloisConjugate_descentPrime_ne_bot
    (a : CyclotomicUnitDelta p) :
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
  cyclotomicGaloisConjugate_ne_bot a⁻¹ S.descentPrime_ne_bot'

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- Each Galois conjugate factor `(σ_{a⁻¹} q_K)^a.val` is non-zero. -/
private theorem stickelbergerFactor_ne_zero (a : CyclotomicUnitDelta p) :
    (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val) :
        Ideal (𝓞 K)) ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot]
  exact pow_ne_zero _ (S.cyclotomicGaloisConjugate_descentPrime_ne_bot a)

/-- **Orbit faithfulness predicate.**

The Galois orbit indexing of `descentPrime` is one-to-one: distinct
units `a, b ∈ (ZMod p)ˣ` give distinct Galois conjugates
`σ_{a⁻¹} q_K ≠ σ_{b⁻¹} q_K`.

In the **split case** (`ℓ ≡ 1 mod p`, ramification index 1, inertia
degree 1), the orbit has size `p − 1` and faithfulness is automatic.
In the unramified case more generally, the stabilizer is the inertia
group, and faithfulness is equivalent to the Galois action being free
on the orbit. -/
def StickelbergerOrbitFaithful : Prop :=
  Function.Injective (fun a : CyclotomicUnitDelta p =>
    cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime)

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of a single factor `(σ_{a⁻¹} q_K)^a.val`
equals `a.val • {σ_{a⁻¹} q_K}`. Uses `normalizedFactors_pow` and the fact
that each conjugate is irreducible (prime + non-zero in a Dedekind domain). -/
theorem normalizedFactors_stickelbergerFactor (a : CyclotomicUnitDelta p) :
    UniqueFactorizationMonoid.normalizedFactors
        (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime ^
            ((a : ZMod p).val) : Ideal (𝓞 K)) =
      ((a : ZMod p).val) •
        ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
            S.toConcreteStickelbergerSetup.descentPrime}
          : Multiset (Ideal (𝓞 K))) := by
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  have h_ne : cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime ≠ ⊥ :=
    S.cyclotomicGaloisConjugate_descentPrime_ne_bot a
  haveI : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime).IsPrime :=
    cyclotomicGaloisConjugate_isPrime a⁻¹ _
  have h_prime : Prime (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) :=
    Ideal.prime_of_isPrime h_ne inferInstance
  have h_irred : Irreducible (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
      S.toConcreteStickelbergerSetup.descentPrime) := h_prime.irreducible
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_irreducible h_irred, normalize_eq]

omit [IsScalarTower ℤ (𝓞 K) (𝓞 R')] in
/-- **Helper:** `normalizedFactors` of a finset product
`∏_{a ∈ s} (σ_{a⁻¹} q_K)^a.val` equals
the sum `∑_{a ∈ s} a.val • {σ_{a⁻¹} q_K}`. Proved by induction on `s`. -/
theorem normalizedFactors_stickelbergerIdeal_finset_eq
    (s : Finset (CyclotomicUnitDelta p)) :
    UniqueFactorizationMonoid.normalizedFactors
        (∏ a ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
          S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val)) =
      ∑ a ∈ s,
        ((a : ZMod p).val) •
          ({cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
              S.toConcreteStickelbergerSetup.descentPrime}
            : Multiset (Ideal (𝓞 K))) := by
  classical
  haveI := S.toConcreteStickelbergerSetup.descentPrime_isPrime
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty,
      UniqueFactorizationMonoid.normalizedFactors_one]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.sum_insert has]
    have h_factor_ne : (cyclotomicGaloisConjugate (p := p) (K := K) a⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^ ((a : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 :=
      S.stickelbergerFactor_ne_zero a
    have h_prod_ne : (∏ b ∈ s, cyclotomicGaloisConjugate (p := p) (K := K) b⁻¹
        S.toConcreteStickelbergerSetup.descentPrime ^ ((b : ZMod p).val) :
          Ideal (𝓞 K)) ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot]
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro b _
      have := S.stickelbergerFactor_ne_zero b
      rwa [Ne, Ideal.zero_eq_bot] at this
    rw [UniqueFactorizationMonoid.normalizedFactors_mul h_factor_ne h_prod_ne,
      S.normalizedFactors_stickelbergerFactor a, ih]

end FullTeichDworkSetup

end Furtwaengler

end BernoulliRegular

end
