module

public import BernoulliRegular.Reflection.ResidueSymbol.IdealAvoidance
public import BernoulliRegular.Reflection.ClassGroupModP.Module
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Class characters from bad-set-coprime ideal symbols

This file is the structural part of the residue-symbol character construction
needed for weak reflection.  It does not prove reciprocity or nondegeneracy.

Given a finite bad set `S` of nonzero prime ideals and an ideal-symbol
function defined on integral ideals coprime to `S`, it constructs the induced
class-group character once the following two elementary properties are
available:

* the symbol is invariant on two `S`-coprime representatives of the same class;
* the symbol is additive under multiplication of `S`-coprime ideals.

The arithmetic work for weak reflection is to produce these properties for
`I ↦ (η / I)_p` from one-sided Kummer reciprocity plus the bad-set avoidance
argument.
-/

@[expose] public section

noncomputable section

open scoped nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace ResidueSymbol
namespace CoprimeClassCharacter

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- A chosen integral representative of a class, coprime to a finite set of
nonzero prime ideals. -/
noncomputable def classRepresentativeCoprime
    (S : Finset (Ideal R))
    (hSprime : ∀ P ∈ S, P.IsPrime) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (c : ClassGroup R) : (Ideal R)⁰ :=
  Classical.choose
    (IdealAvoidance.exists_class_representative_coprime_prime_finset
      (R := R) c S hSprime hS_ne)

/-- The chosen coprime representative represents the requested class. -/
theorem classRepresentativeCoprime_mk0
    (S : Finset (Ideal R))
    (hSprime : ∀ P ∈ S, P.IsPrime) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (c : ClassGroup R) :
    ClassGroup.mk0 (classRepresentativeCoprime S hSprime hS_ne c) = c :=
  (Classical.choose_spec
    (IdealAvoidance.exists_class_representative_coprime_prime_finset
      (R := R) c S hSprime hS_ne)).1

/-- The chosen representative is coprime to every ideal in the bad set. -/
theorem classRepresentativeCoprime_coprime
    (S : Finset (Ideal R))
    (hSprime : ∀ P ∈ S, P.IsPrime) (hS_ne : ∀ P ∈ S, P ≠ ⊥)
    (c : ClassGroup R) :
    ∀ P ∈ S, IsCoprime
      ((classRepresentativeCoprime S hSprime hS_ne c : (Ideal R)⁰) : Ideal R) P :=
  (Classical.choose_spec
    (IdealAvoidance.exists_class_representative_coprime_prime_finset
      (R := R) c S hSprime hS_ne)).2

/-- Coprimality to the bad set is preserved under multiplying integral ideals. -/
theorem coprime_mul_of_coprime
    {R' : Type*} [CommRing R'] {S : Finset (Ideal R')} {I J : (Ideal R')⁰}
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal R') P)
    (hJ : ∀ P ∈ S, IsCoprime (J : Ideal R') P) :
    ∀ P ∈ S, IsCoprime ((I * J : (Ideal R')⁰) : Ideal R') P := by
  intro P hP
  change IsCoprime ((I : Ideal R') * (J : Ideal R')) P
  exact (hI P hP).mul_left (hJ P hP)

/-- Structural data needed to descend a bad-set-coprime ideal symbol to the
class group.  For the weak-reflection application, `symbol I hI` will be the
canonical additive residue symbol `(η / I)_p`, with `hI` recording that `I`
avoids the primes dividing `pη`. -/
structure CoprimeIdealSymbolData (p : ℕ) [Fact p.Prime] (S : Finset (Ideal R)) where
  hSprime : ∀ P ∈ S, P.IsPrime
  hS_ne : ∀ P ∈ S, P ≠ ⊥
  symbol : (I : (Ideal R)⁰) →
    (∀ P ∈ S, IsCoprime (I : Ideal R) P) → ZMod p
  symbol_one :
    ∀ h1 : ∀ P ∈ S, IsCoprime ((1 : (Ideal R)⁰) : Ideal R) P,
      symbol 1 h1 = 0
  symbol_mul :
    ∀ (I J : (Ideal R)⁰)
      (hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P)
      (hJ : ∀ P ∈ S, IsCoprime (J : Ideal R) P)
      (hIJ : ∀ P ∈ S, IsCoprime ((I * J : (Ideal R)⁰) : Ideal R) P),
      symbol (I * J) hIJ = symbol I hI + symbol J hJ
  symbol_eq_of_mk0_eq :
    ∀ {I J : (Ideal R)⁰}
      (hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P)
      (hJ : ∀ P ∈ S, IsCoprime (J : Ideal R) P),
      ClassGroup.mk0 I = ClassGroup.mk0 J →
      symbol I hI = symbol J hJ

namespace CoprimeIdealSymbolData

variable {p : ℕ} [Fact p.Prime] {S : Finset (Ideal R)}
variable (D : CoprimeIdealSymbolData (R := R) p S)

/-- The bad-set-coprime representative chosen for this symbol data. -/
noncomputable def rep (c : ClassGroup R) : (Ideal R)⁰ :=
  classRepresentativeCoprime S D.hSprime D.hS_ne c

theorem rep_mk0 (c : ClassGroup R) :
    ClassGroup.mk0 (D.rep c) = c :=
  classRepresentativeCoprime_mk0 S D.hSprime D.hS_ne c

theorem rep_coprime (c : ClassGroup R) :
    ∀ P ∈ S, IsCoprime ((D.rep c : (Ideal R)⁰) : Ideal R) P :=
  classRepresentativeCoprime_coprime S D.hSprime D.hS_ne c

/-- The induced additive class-group function, using a representative coprime
to the bad set. -/
noncomputable def onClassGroup (c : ClassGroup R) : ZMod p :=
  D.symbol (D.rep c) (D.rep_coprime c)

/-- Evaluation on any already-coprime representative. -/
theorem onClassGroup_mk0
    (I : (Ideal R)⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P) :
    D.onClassGroup (ClassGroup.mk0 I) = D.symbol I hI := by
  unfold onClassGroup
  exact D.symbol_eq_of_mk0_eq (D.rep_coprime (ClassGroup.mk0 I)) hI
    (D.rep_mk0 (ClassGroup.mk0 I))

private theorem one_coprime {R' : Type*} [CommRing R'] {S : Finset (Ideal R')} :
    ∀ P ∈ S, IsCoprime ((1 : (Ideal R')⁰) : Ideal R') P := by
  intro P _hP
  rw [Ideal.isCoprime_iff_sup_eq]
  simp

theorem onClassGroup_one :
    D.onClassGroup (1 : ClassGroup R) = 0 := by
  have h :=
    D.onClassGroup_mk0 (1 : (Ideal R)⁰) (one_coprime (S := S))
  simpa using h.trans (D.symbol_one (one_coprime (S := S)))

theorem onClassGroup_mul (c₁ c₂ : ClassGroup R) :
    D.onClassGroup (c₁ * c₂) = D.onClassGroup c₁ + D.onClassGroup c₂ := by
  let I := D.rep c₁
  let J := D.rep c₂
  have hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P := D.rep_coprime c₁
  have hJ : ∀ P ∈ S, IsCoprime (J : Ideal R) P := D.rep_coprime c₂
  have hIJ : ∀ P ∈ S, IsCoprime ((I * J : (Ideal R)⁰) : Ideal R) P :=
    coprime_mul_of_coprime hI hJ
  have hc₁ : ClassGroup.mk0 I = c₁ := D.rep_mk0 c₁
  have hc₂ : ClassGroup.mk0 J = c₂ := D.rep_mk0 c₂
  have h_eval₁ : D.onClassGroup c₁ = D.symbol I hI := by
    rw [← hc₁]
    exact D.onClassGroup_mk0 I hI
  have h_eval₂ : D.onClassGroup c₂ = D.symbol J hJ := by
    rw [← hc₂]
    exact D.onClassGroup_mk0 J hJ
  calc
    D.onClassGroup (c₁ * c₂)
        = D.onClassGroup (ClassGroup.mk0 (I * J)) := by
            rw [← hc₁, ← hc₂, map_mul]
    _ = D.symbol (I * J) hIJ := D.onClassGroup_mk0 (I * J) hIJ
    _ = D.symbol I hI + D.symbol J hJ := D.symbol_mul I J hI hJ hIJ
    _ = D.onClassGroup c₁ + D.onClassGroup c₂ := by rw [h_eval₁, h_eval₂]

/-- The induced class-group character in multiplicative notation. -/
noncomputable def toClassGroupHom :
    ClassGroup R →* Multiplicative (ZMod p) where
  toFun c := Multiplicative.ofAdd (D.onClassGroup c)
  map_one' := by
    change Multiplicative.ofAdd (D.onClassGroup 1) = 1
    rw [D.onClassGroup_one]
    rfl
  map_mul' c₁ c₂ := by
    change Multiplicative.ofAdd (D.onClassGroup (c₁ * c₂)) =
      Multiplicative.ofAdd (D.onClassGroup c₁) *
        Multiplicative.ofAdd (D.onClassGroup c₂)
    rw [D.onClassGroup_mul]
    rfl

theorem toClassGroupHom_mk0
    (I : (Ideal R)⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P) :
    D.toClassGroupHom (ClassGroup.mk0 I) =
      Multiplicative.ofAdd (D.symbol I hI) := by
  change Multiplicative.ofAdd (D.onClassGroup (ClassGroup.mk0 I)) =
    Multiplicative.ofAdd (D.symbol I hI)
  rw [D.onClassGroup_mk0 I hI]

/-- If the descended class-group character is trivial, then every symbol value
on an already bad-set-coprime representative is zero. -/
theorem symbol_eq_zero_of_toClassGroupHom_eq_one
    (htriv : D.toClassGroupHom = 1)
    (I : (Ideal R)⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal R) P) :
    D.symbol I hI = 0 := by
  have h := congrArg (fun φ : ClassGroup R →* Multiplicative (ZMod p) =>
    φ (ClassGroup.mk0 I)) htriv
  dsimp at h
  rw [D.toClassGroupHom_mk0 I hI] at h
  exact congrArg Multiplicative.toAdd h

end CoprimeIdealSymbolData

section ClassGroupModP

open NumberField

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K]
variable {S : Finset (Ideal (𝓞 K))}
variable (D : CoprimeIdealSymbolData (R := 𝓞 K) p S)

private theorem multiplicative_zmod_pow_p_eq_one (x : Multiplicative (ZMod p)) :
    x ^ p = 1 := by
  ext
  change p • Multiplicative.toAdd x = (0 : ZMod p)
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The coprime-representative character descends to `Cl(O_K)/p`. -/
noncomputable def toClassGroupModPHom :
    ClassGroupModP K p →* Multiplicative (ZMod p) :=
  QuotientGroup.lift _ D.toClassGroupHom <| by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy]
    change D.toClassGroupHom ((powMonoidHom p) y) = 1
    change D.toClassGroupHom (y ^ p) = 1
    rw [map_pow, multiplicative_zmod_pow_p_eq_one]

/-- Evaluation of the descended character on the quotient class of an
already bad-set-coprime representative. -/
theorem toClassGroupModPHom_mk0
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    toClassGroupModPHom D
        (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p) =
      Multiplicative.ofAdd (D.symbol I hI) := by
  rw [toClassGroupModPHom, QuotientGroup.lift_mk,
    D.toClassGroupHom_mk0 I hI]

/-- If the descended `ClassGroupModP` character is trivial, then every symbol
value on an already bad-set-coprime representative is zero. -/
theorem symbol_eq_zero_of_toClassGroupModPHom_eq_one
    (htriv : toClassGroupModPHom D = 1)
    (I : (Ideal (𝓞 K))⁰)
    (hI : ∀ P ∈ S, IsCoprime (I : Ideal (𝓞 K)) P) :
    D.symbol I hI = 0 := by
  have h := congrArg (fun φ : ClassGroupModP K p →* Multiplicative (ZMod p) =>
    φ (QuotientGroup.mk (ClassGroup.mk0 I) : ClassGroupModP K p)) htriv
  dsimp at h
  rw [toClassGroupModPHom_mk0 D I hI] at h
  exact congrArg Multiplicative.toAdd h

/-- The descended character as a `ZMod p`-linear functional. -/
noncomputable def toClassGroupModPLinear :
    Additive (ClassGroupModP K p) →ₗ[ZMod p] ZMod p :=
  AddMonoidHom.toZModLinearMap p (toClassGroupModPHom D).toAdditive

end ClassGroupModP

end CoprimeClassCharacter
end ResidueSymbol
end Reflection
end BernoulliRegular

end
