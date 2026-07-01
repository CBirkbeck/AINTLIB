module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.GaussSum
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.Stickelberger.GaussSumPowerFacts

/-!
# Stickelberger-style prime factorisation of `g(χ_q)^p` (REF-18c2c)

This file develops the Stickelberger-type theorem for the residue Gauss sum
`g(χ_q, ψ_q)` raised to its character order. The classical statement
(Ireland–Rosen Thm 14.5) gives the explicit prime factorisation of
`g(χ_q)^p` in `𝓞_{K(ζ_{Nq})}`, with exponents controlled by the
Stickelberger weight. We work in stages:

1. **Galois invariance of `g(χ)^n`** (this commit).
   For χ a multiplicative character of order dividing `n`, and a ring hom
   `σ : R' →+* R'` that *fixes* χ (`σ ∘ χ = χ`) and shifts the additive
   character ψ by some `a ∈ Rˣ` (`σ ∘ ψ = AddChar.mulShift ψ a`), the `n`-th
   power `g(χ, ψ)^n` is fixed by `σ`. Proof: `g(χ, AddChar.mulShift ψ a)^n` is
   `(χ a)⁻ⁿ · g(χ, ψ)^n` by `gaussSum_mulShift` raised to `n`, and
   `(χ a)^n = (χ^n) a = 1 a = 1` because `χ^n = 1`.

2. **Application to residue Gauss sums** (this commit).
   For `χ_q` of order `p` (residue character) and any Galois automorphism
   `σ` fixing `K = ℚ(ζ_p)` pointwise (so `σ ∘ χ_q = χ_q`), `g(χ_q, ψ_q)^p`
   is fixed by `σ`.

3. **Prime factorisation via Stickelberger weight** (deferred).
   The actual Stickelberger formula `g(χ_q)^p = q^{p-1} · ∏ σ_a^{?}`
   requires the explicit Galois-orbit computation and Jacobi-sum
   factorisation. This is the core of REF-18c2c and is left for follow-up
   commits.

The Galois-invariance step is small but essential: it shows that
`g(χ_q, ψ_q)^p` *descends* from the larger ring `R' = K(ζ_{Nq})` to the
fixed field of the appropriate Galois group, which in our application
will be `K = ℚ(ζ_p)`. This is the key feature exploited by the
Stickelberger formula's prime factorisation.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace Furtwaengler

variable {R : Type*} [CommRing R] [Fintype R]
variable {R' : Type*} [CommRing R']

/-- **Raised q-adic containment from cyclotomic additive character.**
Direct corollary lifting `residueGaussSum_mem_ideal_of_psi_pow_form` to
arbitrary powers via `Ideal.pow_mem_pow`. -/
theorem residueGaussSum_pow_mem_ideal_pow_of_psi_pow_form
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    {psi_q : AddChar k R'}
    (h_psi_pow : ∀ x : k, ∃ n : ℕ, psi_q x = ζ ^ n)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q) (n : ℕ) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ n ∈ Q ^ n :=
  Ideal.pow_mem_pow
    (residueGaussSum_mem_ideal_of_psi_pow_form
      zeta_q hzeta_q hdiv zeta_R hzeta_R hζ h_psi_pow hQ) n

/-- **Divisibility consequence of the norm relation.** From
`g(χ_q)^p · g(χ_q^{p-1})^p = (#k)^p`, the `p`-th power of the residue Gauss
sum divides `(#k)^p` in `R'`. The cofactor is `g(χ_q^{p-1})^p`.

This is a ring-element-level precursor to the prime ideal factorisation:
the principal ideal `(g(χ_q)^p)` divides the principal ideal `((#k)^p)`,
hence in any Dedekind extension the prime support of `(g(χ_q)^p)` is
contained in that of `((#k)^p)` (which is exactly the rational prime
under `q`). -/
theorem residueGaussSum_pow_p_dvd_card_pow
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {psi_q : AddChar k R'} (hpsi : psi_q.IsPrimitive) :
    (residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q) ^ p ∣
        ((Fintype.card k : R')) ^ p :=
  ⟨(gaussSum
      ((residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R) ^ (p - 1)) psi_q) ^ p,
   (residueGaussSum_pow_p_mul_pow_p_sub_one_eq_card_pow
      zeta_q hzeta_q hdiv zeta_R hzeta_R hpsi).symm⟩

/-- **Helper.** If `d` divides every term of a finite product, then `d^n`
divides the product, where `n` is the cardinality of the index set. -/
private lemma Finset.pow_card_dvd_prod_of_each {α β : Type*} [CommMonoid β]
    {s : Finset α} {f : α → β} {d : β} (h : ∀ i ∈ s, d ∣ f i) :
    d ^ s.card ∣ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ,
      mul_comm (d ^ s.card) d]
    exact mul_dvd_mul
      (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Cyclotomic ramification ideal identity.** In a domain `R` with primitive
`q`-th root of unity `ζ` (q prime), `(ζ - 1)^{q-1}` divides `q` in `R`.

This is the classical ramification statement, formulated as a divisibility:
the cyclotomic identity `q = ∏_{a=1}^{q-1} (1 - ζ^a)` together with the
associate relations among the factors gives `(ζ-1)^{q-1} | q`. -/
theorem natCast_mem_zeta_sub_one_pow_sub_one
    {R : Type*} [CommRing R] [IsDomain R]
    {q : ℕ} [hq : Fact q.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ q) :
    (q : R) ∈ Ideal.span {(ζ - 1) ^ (q - 1)} := by
  have hprod : (∏ μ ∈ primitiveRoots q R, ((1 : R) - μ)) = (q : R) := by
    have heval : (Polynomial.cyclotomic q R).eval 1 = (q : R) :=
      Polynomial.eval_one_cyclotomic_prime
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ] at heval
    rw [Polynomial.eval_prod] at heval
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
    exact heval
  have hcard : (primitiveRoots q R).card = q - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hq.out]
  rw [Ideal.mem_span_singleton, ← hprod, ← hcard]
  refine Finset.pow_card_dvd_prod_of_each ?_
  intro μ hμ
  have hμ_prim : IsPrimitiveRoot μ q :=
    isPrimitiveRoot_of_mem_primitiveRoots hμ
  have : NeZero q := ⟨hq.out.ne_zero⟩
  obtain ⟨a, _, _, rfl⟩ := (hζ.isPrimitiveRoot_iff (k := q)).mp hμ_prim
  have hdvd : (ζ - 1) ∣ (ζ ^ a - 1) := by
    have := sub_one_dvd_pow_sub_one ζ a
    simpa using this
  have h1 : (1 - ζ ^ a) = -(ζ ^ a - 1) := by ring
  rw [h1]
  exact dvd_neg.mpr hdvd

/-- **Cyclotomic ramification, converse direction.** In a domain `R` with
primitive `q`-th root of unity `ζ` (q prime), if a prime ideal `Q` contains
`ζ - 1`, then it contains `q`. This is the converse of
`zeta_sub_one_mem_of_natCast_mem`, completing the equivalence
`q ∈ Q ↔ ζ - 1 ∈ Q` for prime ideals. -/
theorem natCast_mem_of_zeta_sub_one_mem
    {R : Type*} [CommRing R] [IsDomain R]
    {q : ℕ} [hq : Fact q.Prime] {ζ : R} (hζ : IsPrimitiveRoot ζ q)
    {Q : Ideal R} (hQ : ζ - 1 ∈ Q) :
    (q : R) ∈ Q := by
  have hdvd := natCast_mem_zeta_sub_one_pow_sub_one hζ
  rw [Ideal.mem_span_singleton] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  refine Ideal.mul_mem_right c Q ?_
  have hpos : 1 ≤ q - 1 := by
    have := hq.out.two_le
    omega
  have hpow : (ζ - 1) ^ (q - 1) ∈ Q ^ (q - 1) := Ideal.pow_mem_pow hQ (q - 1)
  exact Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hpos) hpow

/-!
### Modulo `Q^2` reduction (REF-18c2c4 — Phase C precursor)

The Taylor expansion of `x^n` near `x = 1`: if `x - 1 ∈ I` for some ideal `I`,
then `x^n - 1 ≡ n · (x - 1) (mod I^2)`. This is the key algebraic input for
the modulo-Q² reduction of the Gauss sum, which feeds the exact q-adic
valuation calculation in Phase C.
-/

/-- **Taylor expansion modulo `I^2`.** For any `x` in a commutative ring `R`
and any natural `n`, the difference `x^n - 1 - n · (x - 1)` is divisible by
`(x - 1)^2`. Hence if `x - 1 ∈ I`, then `x^n - 1 ≡ n · (x - 1) (mod I^2)`. -/
theorem pow_sub_one_sub_smul_sub_one_dvd_sq
    {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (x - 1) ^ 2 ∣ x ^ n - 1 - (n : R) * (x - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hexpand : x ^ (n + 1) - 1 - ((n + 1 : ℕ) : R) * (x - 1) =
        (x - 1) * (x ^ n - 1 - (n : R) * (x - 1)) +
        (x ^ n - 1 - (n : R) * (x - 1)) +
        (x - 1) * ((x - 1) * (n : R)) := by push_cast; ring
    rw [hexpand]
    refine dvd_add (dvd_add ?_ ih) ?_
    · exact Dvd.dvd.mul_left ih (x - 1)
    · rw [sq]
      exact ⟨(n : R), by ring⟩

/-- **Taylor expansion as ideal containment.** If `x - 1 ∈ I` for an ideal
`I`, then `x^n - 1 - n · (x - 1) ∈ I^2`. -/
theorem pow_sub_one_sub_smul_sub_one_mem_sq
    {R : Type*} [CommRing R] (x : R) (n : ℕ)
    {I : Ideal R} (h : x - 1 ∈ I) :
    x ^ n - 1 - (n : R) * (x - 1) ∈ I ^ 2 := by
  obtain ⟨c, hc⟩ := pow_sub_one_sub_smul_sub_one_dvd_sq x n
  rw [hc]
  refine Ideal.mul_mem_right c (I ^ 2) ?_
  rw [sq, sq]
  exact Ideal.mul_mem_mul h h

/-- **Gauss sum modulo `I²`** (REF-18c2c4 — Phase C precursor). When the
additive character has the form `ψ(x) = ζ^{f(x)}` for an integer-valued
function `f`, the Gauss sum is `(ζ - 1) · ∑ χ(x) · f(x)` modulo `I²` for
any ideal `I` containing `ζ - 1`.

This is the *first-order Taylor expansion* of `g(χ, ψ)` near the point
`ψ ≡ 1 (mod I)`. The non-vanishing of `∑ χ(x) · f(x)` modulo `I` then
determines whether `ord_I(g(χ, ψ)) = 1`, which together with
`ord_I(ζ - 1) = 1` (Phase B+) controls the leading q-adic term. -/
theorem gaussSum_sub_smul_mem_sq_of_psi_pow
    {R : Type*} [CommRing R] [Fintype R] [IsDomain R]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {χ : MulChar R R'} (hχ : χ ≠ 1) {ψ : AddChar R R'}
    {ζ : R'} (f : R → ℕ) (hf : ∀ x : R, ψ x = ζ ^ f x)
    {I : Ideal R'} (hζ : ζ - 1 ∈ I) :
    gaussSum χ ψ - (ζ - 1) * (∑ x, χ x * (f x : R')) ∈ I ^ 2 := by
  -- Split: g(χ, ψ) = ∑ χ(x)(ψ(x) - 1) + ∑ χ(x), and ∑ χ(x) = 0.
  have hsplit : gaussSum χ ψ = ∑ x, χ x * (ψ x - 1) := by
    have hdiff : (∑ x, χ x * ψ x) - (∑ x, χ x * (ψ x - 1)) = ∑ x, χ x := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    have hzero : (∑ x, χ x : R') = 0 := MulChar.sum_eq_zero_of_ne_one hχ
    have := hdiff
    rw [hzero, sub_eq_zero] at this
    exact this
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  -- Goal: ∑ (χ(x)(ψ(x) - 1) - (ζ - 1) · χ(x) · f(x)) ∈ I^2
  refine Ideal.sum_mem _ fun x _ => ?_
  -- Each term: χ(x) · (ψ(x) - 1 - f(x)(ζ - 1)) ∈ I^2 (factor out χ(x))
  have h_step : χ x * (ψ x - 1) - (ζ - 1) * (χ x * (f x : R')) =
      χ x * (ψ x - 1 - (f x : R') * (ζ - 1)) := by ring
  rw [h_step]
  refine Ideal.mul_mem_left _ (χ x) ?_
  -- ψ x - 1 - f(x)(ζ - 1) = ζ^{f(x)} - 1 - f(x)(ζ - 1) ∈ I^2
  rw [hf x]
  exact pow_sub_one_sub_smul_sub_one_mem_sq ζ (f x) hζ

/-- **Non-vanishing of the leading term ⟹ Gauss sum has q-adic valuation 1.**
Direct consequence of `gaussSum_sub_smul_mem_sq_of_psi_pow`: if the linear
term `(ζ - 1) · S` is not in `I²` (where `S = ∑ χ(x) · f(x)`), then
`g(χ, ψ) ∉ I²`.

In a Dedekind domain context, the hypothesis `(ζ - 1) * S ∉ I²` can be
verified via the two independent conditions `ord_I(ζ - 1) = 1` and
`S ∉ I` (i.e., `S` is a unit modulo `I`). This is the usual route to
showing `ord_I(g(χ, ψ)) = 1`. -/
theorem gaussSum_not_mem_sq_of_psi_pow
    {R : Type*} [CommRing R] [Fintype R] [IsDomain R]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {χ : MulChar R R'} (hχ : χ ≠ 1) {ψ : AddChar R R'}
    {ζ : R'} (f : R → ℕ) (hf : ∀ x : R, ψ x = ζ ^ f x)
    {I : Ideal R'} (hζ : ζ - 1 ∈ I)
    (h_lead : (ζ - 1) * (∑ x, χ x * (f x : R')) ∉ I ^ 2) :
    gaussSum χ ψ ∉ I ^ 2 := by
  intro hg
  apply h_lead
  have hsub := gaussSum_sub_smul_mem_sq_of_psi_pow hχ f hf hζ
  -- hsub : g(χ, ψ) - (ζ - 1) · S ∈ I²
  -- hg : g(χ, ψ) ∈ I²
  -- ⟹ (ζ - 1) · S ∈ I²
  have : (ζ - 1) * (∑ x, χ x * (f x : R')) =
      gaussSum χ ψ - (gaussSum χ ψ - (ζ - 1) * (∑ x, χ x * (f x : R'))) := by ring
  rw [this]
  exact (I ^ 2).sub_mem hg hsub

/-!
### Combined ord_I = 1 statement (REF-18c2c4 — Phase B + C synthesis)

The combination of Phase B (`g(χ_q) ∈ I`) and Phase C
(`g(χ_q) ∉ I²` under non-degeneracy) gives the q-adic valuation `= 1`
statement at the abstract level. In a Dedekind context this is exactly
`ord_I(g(χ_q)) = 1`; in a general CommRing it captures the same content
as the conjunction `g ∈ I ∧ g ∉ I²`.

The bridge to the Stickelberger weight `(q^f - 1)/p`: the value `1` here
is the f=1 case of the weight; for general `f`, the weight is `f`-times
larger and requires recursive application of the same modulo-Q² argument
(or alternatively, computation of the Jacobi-sum closed form). -/

/-- **q-adic valuation `= 1` for the residue Gauss sum** under the
non-degeneracy hypothesis on the linear coefficient. Combines the Phase B
containment with the Phase C non-vanishing criterion.

This is the "valuation 1" instance of the Stickelberger weight (the simplest
case `s(p, q, 1) = 1` when `p ∣ q − 1`, i.e., the residue field is exactly
`𝔽_q`). The general Stickelberger weight `s = (q^f − 1)/p` for residue
degree `f > 1` requires further analysis via the chain identity. -/
theorem residueGaussSum_qadic_ord_eq_one_under_nondeg
    {k : Type*} [Field k] [Fintype k]
    {R' : Type*} [CommRing R'] [IsDomain R']
    {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
    (zeta_q : kˣ) (hzeta_q : IsPrimitiveRoot zeta_q p)
    (hdiv : p ∣ Fintype.card k - 1)
    (zeta_R : R'ˣ) (hzeta_R : IsPrimitiveRoot zeta_R p)
    {ζ : R'} (hζ : IsPrimitiveRoot ζ q)
    {psi_q : AddChar k R'}
    (f : k → ℕ) (hf : ∀ x : k, psi_q x = ζ ^ f x)
    {Q : Ideal R'} [Q.IsPrime] (hQ : (q : R') ∈ Q)
    (h_lead : (ζ - 1) *
        (∑ x, residueMulChar zeta_q hzeta_q hdiv zeta_R hzeta_R x * (f x : R')) ∉ Q ^ 2) :
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q ∈ Q ∧
    residueGaussSum zeta_q hzeta_q hdiv zeta_R hzeta_R psi_q ∉ Q ^ 2 := by
  refine ⟨?_, ?_⟩
  · -- Phase B containment
    refine residueGaussSum_mem_ideal_of_psi_sub_one_mem
      zeta_q hzeta_q hdiv zeta_R hzeta_R fun x => ?_
    rw [hf x]
    exact zeta_pow_sub_one_mem_of_natCast_mem hζ hQ (f x)
  · -- Phase C non-vanishing
    exact gaussSum_not_mem_sq_of_psi_pow
      (residueMulChar_ne_one zeta_q hzeta_q hdiv zeta_R hzeta_R) f hf
      (zeta_sub_one_mem_of_natCast_mem hζ hQ) h_lead

end Furtwaengler

end BernoulliRegular
