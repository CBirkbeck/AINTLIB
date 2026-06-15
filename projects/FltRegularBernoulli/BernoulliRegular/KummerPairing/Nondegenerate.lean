module

public import BernoulliRegular.KummerPairing.Basic

/-!
# Kernel triviality for the Kummer pairing

This file isolates the two kernel statements for a Kummer pairing.  The
nondegeneracy theorem used later is built from these separate left and right
kernel facts.
-/

@[expose] public section

universe u v

noncomputable section

open NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

section Nondegenerate

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- The left kernel of the Kummer pairing: Galois elements pairing trivially
with every Kummer class. -/
def KummerPairingData.leftKernel (B : KummerPairingData (p := p) (K := K) P) :
    Subgroup P.PairingLeft where
  carrier := {h | ∀ b : P.PairingRight, B.apply h b = 1}
  one_mem' := fun b =>
    B.one_left b
  mul_mem' := by
    intro h₁ h₂ h₁_mem h₂_mem b
    rw [B.mul_left h₁ h₂ b, h₁_mem b, h₂_mem b, one_mul]
  inv_mem' := by
    intro h h_mem b
    have hmul := B.mul_left h⁻¹ h b
    rw [inv_mul_cancel, B.one_left b, h_mem b, mul_one] at hmul
    exact hmul.symm

/-- The right kernel of the Kummer pairing: Kummer classes pairing trivially
with every Galois element. -/
def KummerPairingData.rightKernel (B : KummerPairingData (p := p) (K := K) P) :
    Subgroup P.PairingRight where
  carrier := {b | ∀ h : P.PairingLeft, B.apply h b = 1}
  one_mem' := fun h =>
    B.one_right h
  mul_mem' := by
    intro b₁ b₂ b₁_mem b₂_mem h
    rw [B.mul_right h b₁ b₂, b₁_mem h, b₂_mem h, one_mul]
  inv_mem' := by
    intro b b_mem h
    have hmul := B.mul_right h b⁻¹ b
    rw [inv_mul_cancel, B.one_right h, b_mem h, mul_one] at hmul
    exact hmul.symm

/-- The two kernel-triviality statements for a Kummer pairing, kept separate so
later tickets can use one side without unfolding the other. -/
structure KummerPairingKernelTrivial
    (B : KummerPairingData (p := p) (K := K) P) where
  leftKernel_eq_bot : B.leftKernel = ⊥
  rightKernel_eq_bot : B.rightKernel = ⊥

namespace KummerPairingKernelTrivial

variable {B : KummerPairingData (p := p) (K := K) P}

/-- `T038b`, left side: a Galois element in the left kernel is trivial. -/
theorem left_eq_one (N : KummerPairingKernelTrivial (p := p) (K := K) B)
    {h : P.PairingLeft} (hh : ∀ b : P.PairingRight, B.apply h b = 1) :
    h = 1 := by
  have hmem : h ∈ B.leftKernel := hh
  have hbot : h ∈ (⊥ : Subgroup P.PairingLeft) := by
    simpa [N.leftKernel_eq_bot] using hmem
  exact Subgroup.mem_bot.mp hbot

/-- `T038b`, right side: a Kummer class in the right kernel is trivial. -/
theorem right_eq_one (N : KummerPairingKernelTrivial (p := p) (K := K) B)
    {b : P.PairingRight} (hb : ∀ h : P.PairingLeft, B.apply h b = 1) :
    b = 1 := by
  have hmem : b ∈ B.rightKernel := hb
  have hbot : b ∈ (⊥ : Subgroup P.PairingRight) := by
    simpa [N.rightKernel_eq_bot] using hmem
  exact Subgroup.mem_bot.mp hbot

end KummerPairingKernelTrivial

/-! ### Packaged nondegenerate pairing -/

/-- The packaged nondegenerate Kummer pairing API consumed by reflection:
a bilinear pairing together with separate proofs that both kernels are trivial. -/
structure NondegenerateKummerPairing
    (P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)) where
  pairingData : KummerPairingData (p := p) (K := K) P
  kernelTrivial : KummerPairingKernelTrivial (p := p) (K := K) pairingData

namespace NondegenerateKummerPairing

variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}

/-- The underlying bilinear pairing data. -/
def toPairingData (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    KummerPairingData (p := p) (K := K) P :=
  N.pairingData

/-- The packaged pairing map. -/
def pairingMap (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    P.PairingLeft → P.PairingRight → KummerPairingValue p :=
  N.pairingData.apply

@[simp]
theorem one_left (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (b : P.PairingRight) :
    pairingMap (p := p) (K := K) N 1 b = 1 :=
  N.pairingData.one_left b

theorem mul_left (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h₁ h₂ : P.PairingLeft) (b : P.PairingRight) :
    pairingMap (p := p) (K := K) N (h₁ * h₂) b =
      pairingMap (p := p) (K := K) N h₁ b *
        pairingMap (p := p) (K := K) N h₂ b :=
  N.pairingData.mul_left h₁ h₂ b

@[simp]
theorem one_right (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h : P.PairingLeft) :
    pairingMap (p := p) (K := K) N h 1 = 1 :=
  N.pairingData.one_right h

theorem mul_right (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h : P.PairingLeft) (b₁ b₂ : P.PairingRight) :
    pairingMap (p := p) (K := K) N h (b₁ * b₂) =
      pairingMap (p := p) (K := K) N h b₁ *
        pairingMap (p := p) (K := K) N h b₂ :=
  N.pairingData.mul_right h b₁ b₂

/-- Left nondegeneracy in elementwise form. -/
theorem left_eq_one (N : NondegenerateKummerPairing (p := p) (K := K) P)
    {h : P.PairingLeft}
    (hh : ∀ b : P.PairingRight, pairingMap (p := p) (K := K) N h b = 1) :
    h = 1 :=
  KummerPairingKernelTrivial.left_eq_one (p := p) (K := K) N.kernelTrivial hh

/-- Right nondegeneracy in elementwise form. -/
theorem right_eq_one (N : NondegenerateKummerPairing (p := p) (K := K) P)
    {b : P.PairingRight}
    (hb : ∀ h : P.PairingLeft, pairingMap (p := p) (K := K) N h b = 1) :
    b = 1 :=
  KummerPairingKernelTrivial.right_eq_one (p := p) (K := K) N.kernelTrivial hb

/-- Left-kernel form of nondegeneracy. -/
theorem leftKernel_eq_bot (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    N.pairingData.leftKernel = ⊥ :=
  N.kernelTrivial.leftKernel_eq_bot

/-- Right-kernel form of nondegeneracy. -/
theorem rightKernel_eq_bot (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    N.pairingData.rightKernel = ⊥ :=
  N.kernelTrivial.rightKernel_eq_bot

end NondegenerateKummerPairing

end Nondegenerate

end BernoulliRegular

end
