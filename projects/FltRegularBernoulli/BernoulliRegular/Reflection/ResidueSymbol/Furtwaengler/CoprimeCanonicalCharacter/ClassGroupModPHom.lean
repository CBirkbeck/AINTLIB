module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.CoprimeCanonicalCharacter.ClassInvariantFromPrincipalVanishing

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Furtwaengler

open Reflection.ResidueSymbol.CoprimeClassCharacter

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

def locallyPrimaryCoprimeCanonicalIdealSymbolData
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
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S) :
    CoprimeIdealSymbolData (R := 𝓞 K) p S :=
  coprimeCanonicalIdealSymbolData (p := p) (K := K) η S hSprime hS_ne
    (fun hI hJ hmk ↦
      pthSymbolAtIdeal_canonical_eq_of_mk0_eq_of_locallyPrimaryPseudoUnit
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hη_span hS_eta hS_p hI hJ hmk)

/-- The canonical bad-set-coprime character on `ClassGroupModP`, once
bad-set-coprime class invariance has been proved. -/
def coprimeCanonicalClassGroupModPHom
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
    ClassGroupModP K p →* Multiplicative (ZMod p) :=
  toClassGroupModPHom
    (coprimeCanonicalIdealSymbolData (p := p) (K := K) η S hSprime hS_ne hclass)

/-- The canonical bad-set-coprime character as a `ZMod p`-linear functional on
`ClassGroupModP`. -/
def coprimeCanonicalClassGroupModPLinear
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
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p
    (coprimeCanonicalClassGroupModPHom (p := p) (K := K) η S hSprime hS_ne hclass).toAdditive

/-- The canonical bad-set-coprime character on `ClassGroupModP` attached to a
locally-primary pseudo-unit. -/
def locallyPrimaryCoprimeCanonicalClassGroupModPHom
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
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S) :
    ClassGroupModP K p →* Multiplicative (ZMod p) :=
  toClassGroupModPHom
    (locallyPrimaryCoprimeCanonicalIdealSymbolData
      (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
      hη_prime_to_p hη_local hη_span hS_eta hS_p)

/-- The canonical bad-set-coprime character attached to a locally-primary
pseudo-unit, as a `ZMod p`-linear functional. -/
def locallyPrimaryCoprimeCanonicalClassGroupModPLinear
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
          (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))), P ∈ S) :
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p
    (locallyPrimaryCoprimeCanonicalClassGroupModPHom
      (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
      hη_prime_to_p hη_local hη_span hS_eta hS_p).toAdditive

/-- Evaluation of the canonical bad-set-coprime `ClassGroupModP` character on
an already coprime ideal representative. -/
theorem coprimeCanonicalClassGroupModPHom_mk0
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    coprimeCanonicalClassGroupModPHom (p := p) (K := K) η S hSprime hS_ne hclass
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) =
      Multiplicative.ofAdd
        (pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K))) :=
  toClassGroupModPHom_mk0
    (coprimeCanonicalIdealSymbolData (p := p) (K := K) η S hSprime hS_ne hclass)
    I hI

/-- Linear evaluation of the canonical bad-set-coprime `ClassGroupModP`
character on an already coprime ideal representative. -/
theorem coprimeCanonicalClassGroupModPLinear_mk0
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    coprimeCanonicalClassGroupModPLinear (p := p) (K := K) η S hSprime hS_ne hclass
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) := by
  change
    (coprimeCanonicalClassGroupModPHom (p := p) (K := K) η S hSprime hS_ne hclass
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K))
  rw [coprimeCanonicalClassGroupModPHom_mk0
    (p := p) (K := K) η S hSprime hS_ne hclass I hI]
  rfl

/-- Evaluation of the locally-primary canonical bad-set-coprime
`ClassGroupModP` character on an already coprime ideal representative. -/
theorem locallyPrimaryCoprimeCanonicalClassGroupModPHom_mk0
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
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    locallyPrimaryCoprimeCanonicalClassGroupModPHom
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hη_span hS_eta hS_p
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) =
      Multiplicative.ofAdd
        (pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K))) :=
  toClassGroupModPHom_mk0
    (D := locallyPrimaryCoprimeCanonicalIdealSymbolData
      (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
      hη_prime_to_p hη_local hη_span hS_eta hS_p)
    I hI

/-- Linear evaluation of the locally-primary canonical bad-set-coprime
character on an already coprime ideal representative. -/
theorem locallyPrimaryCoprimeCanonicalClassGroupModPLinear_mk0
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
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    locallyPrimaryCoprimeCanonicalClassGroupModPLinear
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hη_span hS_eta hS_p
        (Additive.ofMul (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) := by
  change
    (locallyPrimaryCoprimeCanonicalClassGroupModPHom
        (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
        hη_prime_to_p hη_local hη_span hS_eta hS_p
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)).toAdd =
      pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K))
  rw [locallyPrimaryCoprimeCanonicalClassGroupModPHom_mk0
    (p := p) (K := K) hp_odd η B S hSprime hS_ne hη_ne
    hη_prime_to_p hη_local hη_span hS_eta hS_p I hI]
  rfl

/-- If the canonical bad-set-coprime character is trivial on `ClassGroupModP`,
then the canonical ideal symbol vanishes on every bad-set-coprime ideal. -/
theorem pthSymbolAtIdeal_canonical_eq_zero_of_coprimeCanonicalClassGroupModPHom_eq_one
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    (htriv :
      coprimeCanonicalClassGroupModPHom (p := p) (K := K) η S hSprime hS_ne hclass = 1)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) = 0 :=
  symbol_eq_zero_of_toClassGroupModPHom_eq_one
    (D := coprimeCanonicalIdealSymbolData (p := p) (K := K) η S hSprime hS_ne hclass)
    htriv I hI

/-- If the canonical bad-set-coprime character is trivial on `ClassGroupModP`,
then all bad-set-coprime prime denominator symbols vanish. -/
theorem pthSymbolAtPrime_canonical_eq_zero_of_coprimeCanonicalClassGroupModPHom_eq_one
    (η : 𝓞 K) (S : Finset (Ideal (𝓞 K)))
    (hSprime : ∀ P ∈ S, P.IsPrime)
    (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (hclass :
      ∀ {I J : (Ideal (𝓞 K))⁰}
        (_hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P)
        (_hJ : ∀ P ∈ S, IsCoprime (J : Ideal (𝓞 K)) P),
        ClassGroup.mk0 I = ClassGroup.mk0 J →
        pthSymbolAtIdeal_canonical (p := p) (K := K) η (I : Ideal (𝓞 K)) =
          pthSymbolAtIdeal_canonical (p := p) (K := K) η (J : Ideal (𝓞 K)))
    (htriv :
      coprimeCanonicalClassGroupModPHom (p := p) (K := K) η S hSprime hS_ne hclass = 1)
    {P : Ideal (𝓞 K)} [hPprime : P.IsPrime] (hP_ne : P ≠ ⊥)
    (hP : ∀ Q ∈ S, IsCoprime P Q) :
    pthSymbolAtPrime_canonical (p := p) (K := K) η P = 0 := by
  let I : (Ideal (𝓞 K))⁰ :=
    ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP_ne⟩
  have hzero :
      pthSymbolAtIdeal_canonical (p := p) (K := K) η P = 0 :=
    pthSymbolAtIdeal_canonical_eq_zero_of_coprimeCanonicalClassGroupModPHom_eq_one
      (p := p) (K := K) η S hSprime hS_ne hclass htriv I hP
  rw [pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
    (p := p) (K := K) η hP_ne] at hzero
  exact hzero

end Furtwaengler
end BernoulliRegular

end
