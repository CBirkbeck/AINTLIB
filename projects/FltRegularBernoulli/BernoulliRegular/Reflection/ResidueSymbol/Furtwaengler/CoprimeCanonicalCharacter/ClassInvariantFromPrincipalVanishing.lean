module

public import BernoulliRegular.Reflection.ResidueSymbol.CoprimeClassCharacter
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolPrincipalCanonical.CanonicalIdealSymbol
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.OneSidedKummerReciprocity


/-!
# Coprime class characters for the canonical residue symbol

This file instantiates the structural bad-set-coprime class-character
construction with the actual canonical ideal symbol
`I ↦ pthSymbolAtIdeal_canonical η I`.

The only arithmetic hypothesis left explicit here is class invariance for two
bad-set-coprime representatives. In weak reflection this is the theorem to be
proved from one-sided Kummer reciprocity plus fractional principal-ideal
vanishing.
-/

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Furtwaengler

open Reflection.ResidueSymbol.CoprimeClassCharacter

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Same-class invariance reduces to equality on the two principal balancing
factors supplied by `ClassGroup.mk0_eq_mk0_iff`.

If `ClassGroup.mk0 I = ClassGroup.mk0 J`, then there are nonzero integral
`x y` with `(x) I = (y) J`. Multiplicativity of the canonical ideal symbol
shows that equality of the two principal symbols `(eta / (x))` and
`(eta / (y))` implies equality of `(eta / I)` and `(eta / J)`.

The remaining arithmetic task is therefore to prove this principal-factor
equality from admissible principal/fractional principal vanishing. -/
theorem pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_principal_balance
    (η : 𝓞 K) {I J : (Ideal (𝓞 K))⁰}
    (hprincipal :
      ∀ (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
        Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
          Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({x} : Set (𝓞 K))) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({y} : Set (𝓞 K))))
    (hmk : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := (ClassGroup.mk0_eq_mk0_iff.mp hmk)
  have hspanx_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hspany_ne : Ideal.span ({y} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hy
  have hI_ne : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hJ_ne : (J : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hprod :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) := by
    rw [hxy]
  rw [pthSymbolAtIdeal_canonical_mul_ideal (p := p) (K := K) η hspanx_ne hI_ne,
    pthSymbolAtIdeal_canonical_mul_ideal (p := p) (K := K) η hspany_ne hJ_ne] at hprod
  have hprincipal' := hprincipal x y hx hy hxy
  simpa [hprincipal'] using hprod

/-- Bad-set-coprime same-class invariance reduces to the principal balancing
condition produced by `ClassGroup.mk0_eq_mk0_iff`.

For two bad-set-coprime representatives `I` and `J` of the same ideal class,
it is enough to prove equality of the two principal balancing symbols for
every equation `(x) I = (y) J`. The arithmetic proof of that balancing
condition is the fractional principal-ideal vanishing step. -/
theorem pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_coprime_principal_balance
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hprincipal :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
        (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
          Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
            Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) →
          pthSymbolAtIdeal_canonical (p := p) (K := K) η
              (Ideal.span ({x} : Set (𝓞 K))) =
            pthSymbolAtIdeal_canonical (p := p) (K := K) η
              (Ideal.span ({y} : Set (𝓞 K))))
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (hmk : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)) :=
  pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_principal_balance
    (p := p) (K := K) η
    (fun x y hx hy hxy ↦ hprincipal hI hJ x y hx hy hxy)
    hmk

/-- If an ideal is coprime to a nonzero prime `P`, then `P` occurs with
multiplicity zero in its normalized factorization. -/
theorem normalizedFactors_count_eq_zero_of_isCoprime_prime
    {I P : Ideal (𝓞 K)} [hPprime : P.IsPrime]
    (hI_ne : I ≠ ⊥) (_hP_ne : P ≠ ⊥) (hcop : IsCoprime I P) :
    (UniqueFactorizationMonoid.normalizedFactors I).count P = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  have hle : I ≤ P :=
    ((Ideal.mem_normalizedFactors_iff hI_ne).mp hmem).2
  have hsup : I ⊔ P = P := sup_eq_right.mpr hle
  have htop : I ⊔ P = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hcop
  have hP_top : P = ⊤ := hsup ▸ htop
  exact hPprime.ne_top hP_top

/-- In a principal balancing equation `(x) I = (y) J`, if `I` and `J` are
coprime to a nonzero prime `P`, then the principal factors `(x)` and `(y)`
have the same multiplicity at `P`.

This is the local ideal-factorization core of the fractional principal
vanishing step for the bad-set-coprime character. -/
theorem normalizedFactors_count_span_eq_of_principal_balance
    {I J : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)} [hPprime : P.IsPrime]
    (hP_ne : P ≠ ⊥)
    (hI : IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : IsCoprime (J : Ideal (𝓞 K)) P)
    {x y : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({x} : Set (𝓞 K)))).count P =
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({y} : Set (𝓞 K)))).count P := by
  have hspanx_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hspany_ne : Ideal.span ({y} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hy
  have hI_ne : (I : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hJ_ne : (J : Ideal (𝓞 K)) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp J.2
  have hcount := congrArg
    (fun A : Ideal (𝓞 K) ↦
      (UniqueFactorizationMonoid.normalizedFactors A).count P) hxy
  rw [UniqueFactorizationMonoid.normalizedFactors_mul
        (by simpa [Ideal.zero_eq_bot] using hspanx_ne)
        (by simpa [Ideal.zero_eq_bot] using hI_ne),
      UniqueFactorizationMonoid.normalizedFactors_mul
        (by simpa [Ideal.zero_eq_bot] using hspany_ne)
        (by simpa [Ideal.zero_eq_bot] using hJ_ne),
      Multiset.count_add, Multiset.count_add,
      normalizedFactors_count_eq_zero_of_isCoprime_prime
        (K := K) hI_ne hP_ne hI,
      normalizedFactors_count_eq_zero_of_isCoprime_prime
        (K := K) hJ_ne hP_ne hJ,
      add_zero, add_zero] at hcount
  exact hcount

/-- Bad-set version of
`normalizedFactors_count_span_eq_of_principal_balance`. -/
theorem normalizedFactors_count_span_eq_of_coprime_principal_balance
    (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    {x y : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)))
    {P : Ideal (𝓞 K)} (hP : P ∈ S) :
    (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({x} : Set (𝓞 K)))).count P =
      (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span ({y} : Set (𝓞 K)))).count P := by
  haveI : P.IsPrime := hSprime P hP
  exact normalizedFactors_count_span_eq_of_principal_balance
    (K := K) (P := P) (hS_ne P hP)
    (hI P hP) (hJ P hP) hx hy hxy

/-- If `(x * b) = (y * a)`, `b` is coprime to a bad prime `P`, and `(x)`
and `(y)` have the same multiplicity at `P`, then `a` is also coprime to
`P`.

This is the valuation half of the denominator-clearing step: once the
denominator `b` is chosen away from the bad set, the numerator forced by
`x*b = y*a` is away from the same bad set because the fractional ideal
`(x)/(y)` has valuation zero there. -/
theorem span_singleton_coprime_of_clear_denominator_count
    {P : Ideal (𝓞 K)} [hPprime : P.IsPrime] (hP_ne : P ≠ ⊥)
    {x y a b : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0) (hb : b ≠ 0)
    (hb_coprime : IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P)
    (hcount :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({x} : Set (𝓞 K)))).count P =
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({y} : Set (𝓞 K)))).count P)
    (hclear :
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K))) :
    IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P := by
  haveI : P.IsMaximal := hPprime.isMaximal hP_ne
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  have hspana_le : Ideal.span ({a} : Set (𝓞 K)) ≤ P := by
    have h_eq : P = Ideal.span ({a} : Set (𝓞 K)) ⊔ P :=
      Ideal.IsMaximal.eq_of_le (I := P) (J := Ideal.span ({a} : Set (𝓞 K)) ⊔ P)
        inferInstance hsup le_sup_right
    exact le_sup_left.trans_eq h_eq.symm
  have hxspan_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hyspan_ne : Ideal.span ({y} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hy
  have hbspan_ne : Ideal.span ({b} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hb
  have hxb_ne : x * b ≠ 0 := mul_ne_zero hx hb
  have hxbspan_ne : Ideal.span ({x * b} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hxb_ne
  have hya_le : Ideal.span ({y * a} : Set (𝓞 K)) ≤
      Ideal.span ({y} : Set (𝓞 K)) * P := by
    rw [← Ideal.span_singleton_mul_span_singleton]
    exact Ideal.mul_mono_right hspana_le
  have hxb_le : Ideal.span ({x * b} : Set (𝓞 K)) ≤
      Ideal.span ({y} : Set (𝓞 K)) * P :=
    hclear.trans_le hya_le
  have hle :=
    Ideal.count_le_of_ideal_ge (K := P) hxb_le hxbspan_ne
  have hP_count :
      (UniqueFactorizationMonoid.normalizedFactors P).count P = 1 := by
    have hP_prime : Prime P := Ideal.prime_of_isPrime hP_ne hPprime
    rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP_prime.irreducible,
      normalize_eq P, Multiset.count_singleton_self]
  have hyP_count :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({y} : Set (𝓞 K)) * P)).count P =
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({y} : Set (𝓞 K)))).count P + 1 := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul
        (by simpa [Ideal.zero_eq_bot] using hyspan_ne)
        (by simpa [Ideal.zero_eq_bot] using hP_ne),
      Multiset.count_add, hP_count]
  have hxb_count :
      (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({x * b} : Set (𝓞 K)))).count P =
        (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({x} : Set (𝓞 K)))).count P := by
    rw [show Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({x} : Set (𝓞 K)) * Ideal.span ({b} : Set (𝓞 K)) from
          (Ideal.span_singleton_mul_span_singleton x b).symm,
      UniqueFactorizationMonoid.normalizedFactors_mul
        (by simpa [Ideal.zero_eq_bot] using hxspan_ne)
        (by simpa [Ideal.zero_eq_bot] using hbspan_ne),
      Multiset.count_add,
      normalizedFactors_count_eq_zero_of_isCoprime_prime
        (K := K) hbspan_ne hP_ne hb_coprime,
      add_zero]
  rw [hyP_count, hxb_count, hcount] at hle
  exact Nat.not_succ_le_self _ hle

/-- Bad-set version of
`span_singleton_coprime_of_clear_denominator_count`. -/
theorem span_singleton_coprime_of_clear_denominator_count_finset
    (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    {x y a b : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0) (hb : b ≠ 0)
    (hb_coprime : ∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P)
    (hcount :
      ∀ P ∈ S,
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({x} : Set (𝓞 K)))).count P =
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({y} : Set (𝓞 K)))).count P)
    (hclear :
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K))) :
    ∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P := by
  intro P hP
  haveI : P.IsPrime := hSprime P hP
  exact span_singleton_coprime_of_clear_denominator_count
    (K := K) (P := P) (hS_ne P hP) hx hy hb (hb_coprime P hP)
    (hcount P hP) hclear

/-- Construct bad-set-coprime integral clearers from a coprime denominator
colon ideal.

For the fractional principal ideal `x / y`, take the denominator ideal
`(y) : (x)`. If this colon ideal is coprime to the bad set, finite ideal
avoidance chooses `b` in it with `(b)` coprime to the bad set. Membership
`b ∈ (y):(x)` gives `b*x = y*a` for some integral `a`; equal bad-prime
multiplicities of `(x)` and `(y)` then force `(a)` to be coprime to the same
bad set. -/
theorem exists_clear_denominators_span_of_colon_coprime
    (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    {x y : 𝓞 K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hcolon_coprime :
      ∀ P ∈ S,
        IsCoprime
          ((Ideal.span ({y} : Set (𝓞 K))).colon
            (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))) P)
    (hcount :
      ∀ P ∈ S,
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({x} : Set (𝓞 K)))).count P =
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({y} : Set (𝓞 K)))).count P) :
    ∃ a b : 𝓞 K,
      a ≠ 0 ∧ b ≠ 0 ∧
      (∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P) ∧
      (∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P) ∧
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K)) := by
  let D : Ideal (𝓞 K) :=
    (Ideal.span ({y} : Set (𝓞 K))).colon
      (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))
  have hyD : y ∈ D := by
    dsimp [D]
    rw [Ideal.mem_colon_span_singleton]
    exact (Ideal.span ({y} : Set (𝓞 K))).mul_mem_right x
      (Ideal.mem_span_singleton_self y)
  have hD_ne : D ≠ ⊥ := fun hD ↦
    hy (by simpa [hD] using hyD)
  have hSmax : ∀ P ∈ S, P.IsMaximal := fun P hP ↦
    (hSprime P hP).isMaximal (hS_ne P hP)
  obtain ⟨b, hb_ne, hbD, hb_coprime⟩ :=
    Reflection.ResidueSymbol.IdealAvoidance.exists_mem_coprime_principal_finset
      D hD_ne S hSmax (by simpa [D] using hcolon_coprime)
  have hbx_mem : b * x ∈ Ideal.span ({y} : Set (𝓞 K)) := by
    simpa [D] using (Ideal.mem_colon_span_singleton.mp hbD)
  obtain ⟨a, ha_eq⟩ := Ideal.mem_span_singleton.mp hbx_mem
  have hclear :
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K)) := by
    rw [mul_comm x b, ha_eq]
  have ha_ne : a ≠ 0 := by
    intro ha0
    have hzero : b * x = 0 := by simpa [ha0] using ha_eq
    exact mul_ne_zero hb_ne hx hzero
  have ha_coprime :
      ∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P :=
    span_singleton_coprime_of_clear_denominator_count_finset
      (K := K) S hSprime hS_ne hx hy hb_ne hb_coprime hcount hclear
  exact ⟨a, b, ha_ne, hb_ne, ha_coprime, hb_coprime, hclear⟩

omit [NumberField K] in
/-- In a principal balancing equation `(x) I = (y) J`, the denominator colon
ideal `(y):(x)` contains `I`. Hence, if `I` is coprime to a bad prime `P`, so
is the colon ideal.

This is the missing ideal-theoretic input for the denominator-clearing step:
no valuation computation is needed to prove the colon coprimality itself. -/
theorem colon_coprime_of_principal_balance_left {I J : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hI : IsCoprime (I : Ideal (𝓞 K)) P)
    {x y : 𝓞 K}
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    IsCoprime
      ((Ideal.span ({y} : Set (𝓞 K))).colon
        (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))) P := by
  let D : Ideal (𝓞 K) :=
    (Ideal.span ({y} : Set (𝓞 K))).colon
      (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))
  have hI_le_D : (I : Ideal (𝓞 K)) ≤ D := by
    intro d hd
    dsimp [D]
    rw [Ideal.mem_colon_span_singleton]
    have hxd_left :
        x * d ∈ Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) hd
    have hdx_left :
        d * x ∈ Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) := by
      simpa [mul_comm] using hxd_left
    have hdx_right :
        d * x ∈ Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) := by
      simpa [hxy] using hdx_left
    exact (Ideal.mul_le_right (I := Ideal.span ({y} : Set (𝓞 K)))
      (J := (J : Ideal (𝓞 K)))) hdx_right
  rw [Ideal.isCoprime_iff_sup_eq] at hI ⊢
  change D ⊔ P = ⊤
  exact top_unique (by
    have hsup_le : (I : Ideal (𝓞 K)) ⊔ P ≤ D ⊔ P :=
      sup_le_sup hI_le_D le_rfl
    simpa [hI] using hsup_le)

omit [NumberField K] in
/-- Bad-set version of
`colon_coprime_of_principal_balance_left`. -/
theorem colon_coprime_finset_of_principal_balance_left
    (S : Finset (Ideal (𝓞 K)))
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    {x y : 𝓞 K}
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    ∀ P ∈ S,
      IsCoprime
        ((Ideal.span ({y} : Set (𝓞 K))).colon
          (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))) P := fun P hP ↦
  colon_coprime_of_principal_balance_left
    (K := K) (P := P) (hI P hP) hxy

/-- Principal-symbol cancellation once a fractional principal quotient has
been cleared by bad-set-coprime integral denominators, in the natural
principal-ideal form.

The equality `(x * b) = (y * a)` says that the fractional principal ideals
`(x)/(y)` and `(a)/(b)` agree, allowing for the unavoidable unit ambiguity in
chosen integral generators. If the canonical symbols of `(a)` and `(b)`
vanish, multiplicativity in the denominator gives equality of the symbols of
`(x)` and `(y)`. -/
theorem pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span
    (η : 𝓞 K)
    {x y a b : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hclear :
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K)))
    (ha_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({a} : Set (𝓞 K))) = 0)
    (hb_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({b} : Set (𝓞 K))) = 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) := by
  have hxspan_ne : Ideal.span ({x} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hx
  have hyspan_ne : Ideal.span ({y} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hy
  have haspan_ne : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  have hbspan_ne : Ideal.span ({b} : Set (𝓞 K)) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hb
  have hxmul :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({x * b} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({x} : Set (𝓞 K))) +
          pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({b} : Set (𝓞 K))) := by
    rw [show Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({x} : Set (𝓞 K)) * Ideal.span ({b} : Set (𝓞 K)) from
          (Ideal.span_singleton_mul_span_singleton x b).symm]
    exact pthSymbolAtIdeal_canonical_mul_ideal (p := p) (K := K) η
      hxspan_ne hbspan_ne
  have hymul :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({y * a} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({y} : Set (𝓞 K))) +
          pthSymbolAtIdeal_canonical (p := p) (K := K) η
            (Ideal.span ({a} : Set (𝓞 K))) := by
    rw [show Ideal.span ({y * a} : Set (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * Ideal.span ({a} : Set (𝓞 K)) from
          (Ideal.span_singleton_mul_span_singleton y a).symm]
    exact pthSymbolAtIdeal_canonical_mul_ideal (p := p) (K := K) η
      hyspan_ne haspan_ne
  have hmul :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({x * b} : Set (𝓞 K))) =
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({y * a} : Set (𝓞 K))) := by
    rw [hclear]
  rw [hxmul, hymul, hb_zero, ha_zero, add_zero, add_zero] at hmul
  exact hmul

/-- Element-equality corollary of
`pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span`. -/
theorem pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators
    (η : 𝓞 K)
    {x y a b : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hclear : x * b = y * a)
    (ha_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({a} : Set (𝓞 K))) = 0)
    (hb_zero :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({b} : Set (𝓞 K))) = 0) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) :=
  pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span
    (p := p) (K := K) η hx hy ha hb (by rw [hclear]) ha_zero hb_zero

/-- Bad-set-coprime version of
`pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span`.

The hypothesis `hvanish` is the admissible principal-ideal vanishing theorem
coming from one-sided Kummer reciprocity. The only remaining arithmetic input
is the explicit clear-denominators data `a,b`. -/
theorem pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span_coprime
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    {x y a b : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_coprime : ∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P)
    (hb_coprime : ∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P)
    (hclear :
      Ideal.span ({x * b} : Set (𝓞 K)) =
        Ideal.span ({y * a} : Set (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) :=
  pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span
    (p := p) (K := K) η hx hy ha hb hclear
    (hvanish a ha ha_coprime) (hvanish b hb hb_coprime)

/-- Bad-set-coprime element-equality corollary of
`pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span_coprime`. -/
theorem pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_coprime
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    {x y a b : 𝓞 K}
    (hx : x ≠ 0) (hy : y ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha_coprime : ∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P)
    (hb_coprime : ∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P)
    (hclear : x * b = y * a) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) :=
  pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span_coprime
    (p := p) (K := K) η S hvanish hx hy ha hb ha_coprime hb_coprime
    (by rw [hclear])

/-- Principal-balancing input from denominator clearers stated as equality of
principal ideals.

This is the formal version of the tex step:
from `(x) I = (y) J` with `I,J` coprime to the bad set, show that `x/y` has
zero valuation at every bad prime; then choose bad-set-coprime integral
`a,b` with `(x*b) = (y*a)` as principal ideals; admissible principal
vanishing for `(a)` and `(b)` gives equality of the two principal symbols.

The theorem below proves the last two sentences from explicit clearers. The
remaining ideal-avoidance work is precisely to construct `a,b` from the
valuation equality. -/
theorem pthSymbolAtIdeal_canonical_principal_balance_of_clear_denominators_span
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    (hclear :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
        (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
          Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
            Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) →
          ∃ a b : 𝓞 K,
            a ≠ 0 ∧ b ≠ 0 ∧
            (∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P) ∧
            (∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P) ∧
            Ideal.span ({x * b} : Set (𝓞 K)) =
              Ideal.span ({y * a} : Set (𝓞 K)))
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) := by
  obtain ⟨a, b, ha, hb, ha_coprime, hb_coprime, hxb⟩ :=
    hclear hI hJ x y hx hy hxy
  exact pthSymbolAtIdeal_canonical_span_eq_of_clear_denominators_span_coprime
    (p := p) (K := K) η S hvanish hx hy ha hb
    ha_coprime hb_coprime hxb

/-- Element-equality version of
`pthSymbolAtIdeal_canonical_principal_balance_of_clear_denominators_span`. -/
theorem pthSymbolAtIdeal_canonical_principal_balance_of_clear_denominators
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    (hclear :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
        (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
          Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
            Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) →
          ∃ a b : 𝓞 K,
            a ≠ 0 ∧ b ≠ 0 ∧
            (∀ P ∈ S, IsCoprime (Ideal.span ({a} : Set (𝓞 K))) P) ∧
            (∀ P ∈ S, IsCoprime (Ideal.span ({b} : Set (𝓞 K))) P) ∧
            x * b = y * a)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) :=
  pthSymbolAtIdeal_canonical_principal_balance_of_clear_denominators_span
    (p := p) (K := K) η S hvanish
    (fun hI hJ x y hx hy hxy ↦ by
      obtain ⟨a, b, ha, hb, ha_coprime, hb_coprime, hxb⟩ :=
        hclear hI hJ x y hx hy hxy
      exact ⟨a, b, ha, hb, ha_coprime, hb_coprime, by rw [hxb]⟩)
    hI hJ x y hx hy hxy

/-- Principal-balancing input for the coprime representative character from
colon-coprimality.

This packages the completed fractional-principal argument except for the one
remaining Dedekind-domain valuation fact: in a principal balance
`(x) I = (y) J` with `I,J` coprime to the bad set, the denominator colon ideal
`(y):(x)` is coprime to the bad set. Given that fact, the theorem constructs
bad-set-coprime clearers and applies admissible principal-ideal vanishing. -/
theorem pthSymbolAtIdeal_canonical_principal_balance_of_colon_coprime
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    (hcolon_coprime :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
        (x y : 𝓞 K) (_hx : x ≠ 0) (_hy : y ≠ 0),
          Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
            Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K)) →
          ∀ P ∈ S,
            IsCoprime
              ((Ideal.span ({y} : Set (𝓞 K))).colon
                (Ideal.span ({x} : Set (𝓞 K)) : Set (𝓞 K))) P)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) := by
  refine pthSymbolAtIdeal_canonical_principal_balance_of_clear_denominators_span
    (p := p) (K := K) η S hvanish ?_ hI hJ x y hx hy hxy
  intro I J hI hJ x y hx hy hxy
  have hcount :
      ∀ P ∈ S,
        (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({x} : Set (𝓞 K)))).count P =
          (UniqueFactorizationMonoid.normalizedFactors
            (Ideal.span ({y} : Set (𝓞 K)))).count P :=
    fun P hP ↦
      normalizedFactors_count_span_eq_of_coprime_principal_balance
        (K := K) S hSprime hS_ne hI hJ hx hy hxy hP
  exact exists_clear_denominators_span_of_colon_coprime
    (K := K) S hSprime hS_ne hx hy
    (hcolon_coprime hI hJ x y hx hy hxy) hcount

/-- Principal-balancing input for the coprime representative character from
admissible principal-ideal vanishing alone.

Given `(x) I = (y) J` with `I,J` coprime to the bad set, the count lemma shows
that `(x)` and `(y)` have the same bad-prime multiplicities. The colon ideal
`(y):(x)` contains `I`, hence is also coprime to the bad set. We can therefore
choose bad-set-coprime clearers `a,b` and cancel the admissible principal
symbols of `(a)` and `(b)`. -/
theorem pthSymbolAtIdeal_canonical_principal_balance_of_coprime_vanishing
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy :
      Ideal.span ({x} : Set (𝓞 K)) * (I : Ideal (𝓞 K)) =
        Ideal.span ({y} : Set (𝓞 K)) * (J : Ideal (𝓞 K))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({x} : Set (𝓞 K))) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η
        (Ideal.span ({y} : Set (𝓞 K))) :=
  pthSymbolAtIdeal_canonical_principal_balance_of_colon_coprime
    (p := p) (K := K) η S hSprime hS_ne hvanish
    (fun hI _hJ _x _y _hx _hy hxy ↦
      colon_coprime_finset_of_principal_balance_left
        (K := K) S hI hxy)
    hI hJ x y hx hy hxy

/-- Bad-set-coprime class invariance for the canonical ideal symbol from
admissible principal-ideal vanishing.

This is the formal class-character descent step promised by the tex proof:
principal vanishing is only required for principal denominators coprime to the
finite bad set. -/
theorem pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_coprime_vanishing
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hvanish :
      ∀ z : 𝓞 K, z ≠ 0 →
        (∀ P ∈ S, IsCoprime (Ideal.span ({z} : Set (𝓞 K))) P) →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η
          (Ideal.span ({z} : Set (𝓞 K))) = 0)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (hmk : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)) :=
  pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_coprime_principal_balance
    (p := p) (K := K) η S
    (fun hI hJ x y hx hy hxy ↦
      pthSymbolAtIdeal_canonical_principal_balance_of_coprime_vanishing
        (p := p) (K := K) η S hSprime hS_ne hvanish
        hI hJ x y hx hy hxy)
    hI hJ hmk

/-- Bad-set-coprime class invariance for the canonical residue symbol attached
to a locally-primary pseudo-unit.

The input is exactly the admissible OSKR/WR-03 principal-vanishing package:
`η` is locally a `p`-th power at `λ`, prime to `p`, its principal ideal is a
`p`-th power, and the finite bad set contains the prime factors of `(η)` and
`(p)`. -/
theorem pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_locallyPrimaryPseudoUnit
    (hp_odd : Odd p)
    (η : 𝓞 K) (B : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hη_ne : η ≠ 0)
    (hη_prime_to_p :
      IsCoprime
        (Ideal.span ({η} : Set (𝓞 K)))
        (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hη_local : IsLambdaLocalPthPower (p := p) (K := K) η)
    (hη_span : Ideal.span ({η} : Set (𝓞 K)) = B ^ p)
    (hS_eta :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({η} : Set (𝓞 K))), P ∈ S)
    (hS_p :
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S)
    {I J : (Ideal (𝓞 K))⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P)
    (hmk : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)) :=
  pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_coprime_vanishing
    (p := p) (K := K) η S hSprime hS_ne
    (fun _z hz hzcop ↦
      locallyPrimaryPseudoUnit_principalSymbol_eq_zero_canonical_of_coprime_badSet
        p hp_odd K B S hη_ne hz hη_prime_to_p hη_local hη_span hS_eta hS_p hzcop)
    hI hJ hmk

/-- The canonical residue symbol as a bad-set-coprime ideal-symbol datum, once
class invariance is known for representatives coprime to the bad set. -/
def coprimeCanonicalIdealSymbolData
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K))) :
    CoprimeIdealSymbolData (R := 𝓞 K) p S where
  hSprime := hSprime
  hS_ne := hS_ne
  symbol I _hI := pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K))
  symbol_one := by
    intro _h1
    exact pthSymbolAtIdeal_canonical_one (p := p) (K := K) η
  symbol_mul := by
    intro I J _hI _hJ _hIJ
    exact pthSymbolAtIdeal_canonical_mul_ideal (p := p) (K := K) η
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
      (mem_nonZeroDivisors_iff_ne_zero.mp J.2)
  symbol_eq_of_mk0_eq := by
    intro I J hI hJ hmk
    exact hclass hI hJ hmk

end Furtwaengler

end BernoulliRegular

end
