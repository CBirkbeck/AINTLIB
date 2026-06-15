module

public import BernoulliRegular.KummerPairing.Nondegenerate

/-!
# Galois twist formula for the Kummer pairing

This file packages the twist identity used in the reflection argument.  The
actual cyclotomic Galois actions on the Hilbert-side Galois group and the
Kummer subgroup are supplied as data; the exported theorem states the exact
formula downstream files should use.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section Twist

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- The exponent by which `σ_a` acts on `p`-th roots of unity, represented in
the pairing target `Multiplicative (ZMod p)`. -/
def kummerTwistExponent (a : (ZMod p)ˣ) : ℕ :=
  (a : ZMod p).val

/-- Data of the cyclotomic twist actions and the Kummer pairing twist formula.

The two action fields represent `h ↦ h^{σ_a}` on the Hilbert-side Galois group
and `b ↦ b^{σ_a}` on the Kummer subgroup. -/
structure KummerPairingTwistData
    (N : NondegenerateKummerPairing (p := p) (K := K) P) where
  leftTwist : (ZMod p)ˣ → P.PairingLeft → P.PairingLeft
  rightTwist : (ZMod p)ˣ → P.PairingRight → P.PairingRight
  twist_formula :
    ∀ (a : (ZMod p)ˣ) (h : P.PairingLeft) (b : P.PairingRight),
      NondegenerateKummerPairing.pairingMap (p := p) (K := K) N
          (leftTwist a h) (rightTwist a b) =
        NondegenerateKummerPairing.pairingMap (p := p) (K := K) N h b ^
          kummerTwistExponent p a

namespace KummerPairingTwistData

variable {p K}
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}

/-- The Hilbert-side twist `h ↦ h^{σ_a}`. -/
def twistLeft (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (h : P.PairingLeft) : P.PairingLeft :=
  T.leftTwist a h

/-- The Kummer-subgroup twist `b ↦ b^{σ_a}`. -/
def twistRight (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (b : P.PairingRight) : P.PairingRight :=
  T.rightTwist a b

/-- `T039`: the Galois twist formula for the Kummer pairing. -/
theorem pairing_twist_formula
    (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (h : P.PairingLeft) (b : P.PairingRight) :
    NondegenerateKummerPairing.pairingMap (p := p) (K := K) N
        (T.twistLeft a h) (T.twistRight a b) =
      NondegenerateKummerPairing.pairingMap (p := p) (K := K) N h b ^
        kummerTwistExponent p a :=
  T.twist_formula a h b

end KummerPairingTwistData

end Twist

end BernoulliRegular

end
