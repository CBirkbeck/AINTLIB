/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.InvariantTorsor

/-!
# Galois descent of semilinear modules ([A711-DESC], general form)

Let `G` act freely on the `R`-algebra `A` in the sense of Katz–Mazur A7.1.1
(`IsFreeAlgebraAction`), and put `B = Aᴳ`. This file proves **Galois descent of modules**: for
every `A`-module `M` carrying a compatible *semilinear* `G`-action
(`g • (a • m) = (g • a) • (g • m)`), the multiplication map

  `A ⊗_B Mᴳ ⟶ M`,  `a ⊗ m ↦ a • m`

is bijective. Mathlib has no faithfully-flat descent of modules
(`RingTheory/Flat/FaithfullyFlat/Descent.lean` descends only ring-hom properties), and the
Galois-coordinate proof needs none: the same finite family `∑ᵢ aᵢ · (g • bᵢ) = δ_{g,1}`
(`exists_galoisCoords`) that produced the torsor isomorphism does this too, on its *fourth* use.

The inverse is `m ↦ ∑ᵢ aᵢ ⊗ (∑_g g • (bᵢ • m))`; the right inverse identity is precisely
`galoisCoords_dual` (`∑ᵢ aᵢ · tr(bᵢ x) = x`).

`twistedMul_bijective` (`InvariantTorsor.lean`) is the special case `M = A` with the action
twisted by a cocycle `w : G → Aˣ`; it is *not* subsumed, because there the semilinear module is
`A` with a twisted action, whose invariants are `M_w`.

Consumer: `[a3-ii]` of `[T-E5c-ROUTE-A]` — for a `G`-stable affine open `W` of the universal
curve, `Γ(W) ≅ Γ(W)ᴳ ⊗_{Aᴳ} A`, i.e. `W ≅ (W/G) ×_{X/G} X`. That is the cartesianness of the
KM descent square, obtained without SGA I Exp. VIII 7.8.
-/

universe u v

open TensorProduct

namespace MulSemiringAction

variable (G : Type*) [Group G]
variable (R : Type v) (A : Type u)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]
variable (M : Type u) [AddCommGroup M] [Module A M] [DistribMulAction G M]
variable (hsl : ∀ (g : G) (a : A) (m : M), g • (a • m) = (g • a) • (g • m))

/-- The invariants `Mᴳ` of a semilinear `G`-module, as a `B = Aᴳ`-submodule of `M`. -/
def semilinearInvariants : Submodule (FixedPoints.subalgebra R A G) M where
  carrier := {m : M | ∀ g : G, g • m = m}
  add_mem' hx hy := fun g => by rw [smul_add, hx g, hy g]
  zero_mem' := fun g => smul_zero g
  smul_mem' b m hm := fun g => by
    show g • ((b : A) • m) = (b : A) • m
    rw [hsl, b.2 g, hm g]

@[simp]
theorem mem_semilinearInvariants {m : M} :
    m ∈ semilinearInvariants G R A M hsl ↔ ∀ g : G, g • m = m := Iff.rfl

/-- **Galois descent, the comparison map**: `A ⊗_B Mᴳ ⟶ M`, `a ⊗ m ↦ a • m`. -/
noncomputable def descentMul :
    A ⊗[FixedPoints.subalgebra R A G] (semilinearInvariants G R A M hsl) →ₗ[
      FixedPoints.subalgebra R A G] M :=
  TensorProduct.lift
    (LinearMap.mk₂ (FixedPoints.subalgebra R A G)
      (fun (a : A) (m : semilinearInvariants G R A M hsl) => a • (m : M))
      (fun a₁ a₂ m => add_smul _ _ _)
      (fun b a m => by
        show ((b : A) * a) • (m : M) = (b : A) • (a • (m : M))
        rw [mul_smul])
      (fun a m₁ m₂ => smul_add _ _ _)
      (fun b a m => by
        show a • ((b : A) • (m : M)) = (b : A) • (a • (m : M))
        rw [smul_smul, smul_smul, mul_comm]))

@[simp]
theorem descentMul_tmul (a : A) (m : semilinearInvariants G R A M hsl) :
    descentMul G R A M hsl (a ⊗ₜ[FixedPoints.subalgebra R A G] m) = a • (m : M) := rfl

section Fintype

variable [Fintype G]

/-- The averaged element `∑_g g • (b • m)`, an invariant of `M`. -/
def semilinearTrace (b : A) (m : M) : semilinearInvariants G R A M hsl :=
  ⟨∑ g : G, g • (b • m), fun h => by
    rw [Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    exact (mul_smul h g (b • m)).symm⟩

@[simp]
theorem semilinearTrace_coe (b : A) (m : M) :
    ((semilinearTrace G R A M hsl b m : semilinearInvariants G R A M hsl) : M) =
      ∑ g : G, g • (b • m) := rfl

theorem semilinearTrace_add (b : A) (m m' : M) :
    semilinearTrace G R A M hsl b (m + m') =
      semilinearTrace G R A M hsl b m + semilinearTrace G R A M hsl b m' := by
  refine Subtype.ext ?_
  simp only [semilinearTrace_coe, Submodule.coe_add, smul_add, Finset.sum_add_distrib]

/-- On an *invariant* `m`, the averaged element is the trace of `A` acting on `m`. -/
theorem semilinearTrace_of_mem (b a : A) (m : M) (hm : ∀ g : G, g • m = m) :
    semilinearTrace G R A M hsl b (a • m) =
      (traceInvariants G R A (b * a)) • (⟨m, hm⟩ : semilinearInvariants G R A M hsl) := by
  refine Subtype.ext ?_
  show (∑ g : G, g • (b • (a • m))) = (traceInvariants G R A (b * a) : A) • m
  have hterm : ∀ g : G, g • (b • (a • m)) = (g • (b * a)) • m := by
    intro g
    rw [smul_smul, hsl, hm g]
  rw [Finset.sum_congr rfl fun g _ => hterm g]
  show (∑ g : G, (g • (b * a)) • m) = (∑ g : G, g • (b * a)) • m
  rw [Finset.sum_smul]

/-- **Galois descent, the inverse map**: `m ↦ ∑ᵢ aᵢ ⊗ (∑_g g • (bᵢ • m))`. -/
noncomputable def descentInv (S : Finset (A × A)) (m : M) :
    A ⊗[FixedPoints.subalgebra R A G] (semilinearInvariants G R A M hsl) :=
  ∑ p ∈ S, p.1 ⊗ₜ[FixedPoints.subalgebra R A G] (semilinearTrace G R A M hsl p.2 m)

theorem descentInv_add (S : Finset (A × A)) (m m' : M) :
    descentInv G R A M hsl S (m + m') =
      descentInv G R A M hsl S m + descentInv G R A M hsl S m' := by
  rw [descentInv, descentInv, descentInv, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by
    rw [semilinearTrace_add, TensorProduct.tmul_add]

variable [DecidableEq G]

/-- **Galois descent of semilinear modules ([A711-DESC], general form)**: for a free `G`-action
on `A` and any semilinear `A[G]`-module `M`, multiplication `A ⊗_{Aᴳ} Mᴳ → M` is bijective.

The right inverse is `descentInv`; surjectivity is the Galois-coordinate identity
`∑ᵢ aᵢ · (g • bᵢ) = δ_{g,1}` applied to `∑_g (g • m)`, and injectivity is `galoisCoords_dual`
(`∑ᵢ aᵢ · tr(bᵢ x) = x`) on the generators of the tensor product. -/
theorem descentMul_bijective (hfree : IsFreeAlgebraAction G R A) :
    Function.Bijective (descentMul G R A M hsl) := by
  classical
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  constructor
  · -- injectivity: `descentInv` is a left inverse
    have hleft : ∀ z, descentInv G R A M hsl S (descentMul G R A M hsl z) = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero =>
        rw [map_zero]
        show (∑ p ∈ S, p.1 ⊗ₜ[FixedPoints.subalgebra R A G]
          (semilinearTrace G R A M hsl p.2 0)) = 0
        refine Finset.sum_eq_zero fun p _ => ?_
        have h0 : semilinearTrace G R A M hsl p.2 (0 : M) = 0 := by
          refine Subtype.ext ?_
          simp only [semilinearTrace_coe, smul_zero, Finset.sum_const_zero]
          rfl
        rw [h0, TensorProduct.tmul_zero]
      | tmul a m =>
        rw [descentMul_tmul, descentInv]
        have hterm : ∀ p : A × A, p.1 ⊗ₜ[FixedPoints.subalgebra R A G]
            (semilinearTrace G R A M hsl p.2 (a • (m : M))) =
            (p.1 * (traceInvariants G R A (p.2 * a) : A)) ⊗ₜ[FixedPoints.subalgebra R A G] m := by
          intro p
          have hmm : (⟨(m : M), m.2⟩ : semilinearInvariants G R A M hsl) = m := Subtype.ext rfl
          rw [semilinearTrace_of_mem G R A M hsl p.2 a (m : M) m.2, hmm,
            TensorProduct.tmul_smul, TensorProduct.smul_tmul']
          congr 1
          exact mul_comm _ _
        rw [Finset.sum_congr rfl fun p _ => hterm p, ← TensorProduct.sum_tmul,
          galoisCoords_dual G R A hS a]
      | add z z' hz hz' =>
        rw [map_add, descentInv_add, hz, hz']
    exact Function.LeftInverse.injective hleft
  · -- surjectivity: `m = ∑ᵢ aᵢ • (∑_g g • (bᵢ • m))`
    intro m
    refine ⟨descentInv G R A M hsl S m, ?_⟩
    rw [descentInv, map_sum]
    have hterm : ∀ p : A × A, descentMul G R A M hsl
        (p.1 ⊗ₜ[FixedPoints.subalgebra R A G] (semilinearTrace G R A M hsl p.2 m)) =
        ∑ g : G, (p.1 * (g • p.2)) • (g • m) := by
      intro p
      rw [descentMul_tmul, semilinearTrace_coe, Finset.smul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hsl, smul_smul]
    rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_comm]
    have hcol : ∀ g : G, (∑ p ∈ S, (p.1 * (g • p.2)) • (g • m)) =
        (if g = 1 then (1 : A) else 0) • (g • m) := by
      intro g
      rw [← Finset.sum_smul, hS g]
    have hone : (∑ g : G, (if g = 1 then (1 : A) else 0) • (g • m)) = m := by
      rw [Finset.sum_eq_single (1 : G)]
      · simp
      · intro g _ hg
        rw [if_neg hg, zero_smul]
      · intro hc
        exact absurd (Finset.mem_univ (1 : G)) hc
    rw [Finset.sum_congr rfl fun g _ => hcol g, hone]

end Fintype

end MulSemiringAction
