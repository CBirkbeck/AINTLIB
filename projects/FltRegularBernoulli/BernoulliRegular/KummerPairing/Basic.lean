module

public import BernoulliRegular.KummerPairing.Setup

/-!
# Basic Kummer pairing API

This file defines the typed pairing object used by the reflection layer.  The
mathematical construction of the pairing is represented by data over a
`HilbertKummerPresentation`; the bilinearity theorems below are proved by
projecting the corresponding fields.  This keeps the interface honest while the
later reflection tickets work against a stable API.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section Basic

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

namespace HilbertKummerSubgroup

namespace HilbertKummerPresentation

/-- The left side of the Kummer pairing: the Galois group of the presentation
field over `K`. -/
abbrev PairingLeft (P : HilbertKummerPresentation.{u, v} (p := p) (K := K)) :
    Type v :=
  P.E ≃ₐ[K] P.E

/-- The right side of the Kummer pairing: the declared Kummer subgroup `C`. -/
abbrev PairingRight (P : HilbertKummerPresentation.{u, v} (p := p) (K := K)) :
    Type u :=
  P.C

end HilbertKummerPresentation

end HilbertKummerSubgroup

/-- The target group of the pairing.  We use `Multiplicative (ZMod p)` as a
compact model for the cyclic group of `p`-th roots of unity. -/
abbrev KummerPairingValue : Type :=
  Multiplicative (ZMod p)

/-- Data of a Kummer pairing on a Hilbert Kummer presentation, together with
the bilinearity laws needed downstream. -/
structure KummerPairingData
    (P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)) where
  pairing :
    P.PairingLeft → P.PairingRight → KummerPairingValue p
  map_one_left : ∀ b, pairing 1 b = 1
  map_mul_left : ∀ h₁ h₂ b, pairing (h₁ * h₂) b = pairing h₁ b * pairing h₂ b
  map_one_right : ∀ h, pairing h 1 = 1
  map_mul_right : ∀ h b₁ b₂, pairing h (b₁ * b₂) = pairing h b₁ * pairing h b₂

namespace KummerPairingData

variable {p K}
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- The Kummer pairing attached to the data. -/
def apply (B : KummerPairingData (p := p) (K := K) P) :
    P.PairingLeft → P.PairingRight → KummerPairingValue p :=
  B.pairing

@[simp]
theorem one_left (B : KummerPairingData (p := p) (K := K) P)
    (b : P.PairingRight) :
    B.apply 1 b = 1 :=
  B.map_one_left b

theorem mul_left (B : KummerPairingData (p := p) (K := K) P)
    (h₁ h₂ : P.PairingLeft) (b : P.PairingRight) :
    B.apply (h₁ * h₂) b = B.apply h₁ b * B.apply h₂ b :=
  B.map_mul_left h₁ h₂ b

@[simp]
theorem one_right (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) :
    B.apply h 1 = 1 :=
  B.map_one_right h

theorem mul_right (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) (b₁ b₂ : P.PairingRight) :
    B.apply h (b₁ * b₂) = B.apply h b₁ * B.apply h b₂ :=
  B.map_mul_right h b₁ b₂

/-- The right input is well defined as an element of the Kummer subgroup:
equal representatives in the subgroup give equal pairing values. -/
theorem right_ext (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) {b₁ b₂ : P.PairingRight}
    (hb : ((b₁ : P.C) : KummerPowerQuotient (p := p) K) = b₂) :
    B.apply h b₁ = B.apply h b₂ :=
  congrArg (B.apply h) (Subtype.ext hb)

end KummerPairingData

end Basic

end BernoulliRegular

end
