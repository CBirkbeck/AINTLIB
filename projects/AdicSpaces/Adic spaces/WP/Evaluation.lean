/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedGaussAdic
import «Adic spaces».Presheaf

/-!
# Evaluation of restricted power series at power-bounded tuples

The universal property of `E⟨T_1,…,T_m⟩` ([WP] §2, lines 176–181: "The Tate variables
are power-bounded, so the same presentation records the rational inequalities
`|f_i| ≤ |g|`"; Huber's universal property, [Huber94] (1.2)/Prop 1.3): a continuous
ring homomorphism `φ : E → B` into a complete Hausdorff nonarchimedean topological
ring together with a power-bounded tuple `b : Fin m → B` extends uniquely to
`E⟨T⟩ → B`, `T_i ↦ b_i`, by `F ↦ ∑_t φ(c_t)·b^t` — the series converges because the
coefficients are null and the monomials `b^t` range in a bounded set.

This is the `rev`-direction engine for every identification of a `presheafValue` with
a concrete model in this campaign (the `chartRev`/`chartEval` pattern of
`FJP/Over/Chart.lean:1124`, done once generically).  Search first: pieces may exist in
`WedhornCechAcyclicity.lean` (the 828b quotient-presentation machinery) and in
mathlib's `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean`.
-/

@[expose] public section

namespace WeightedParity

open FiniteJet.GraphKoszul TopologicalRing Filter Topology

/-- Cofinitely-null families are summable in a complete Hausdorff nonarchimedean
group (search first: `Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean`). -/
theorem summable_of_tendsto_cofinite_nonarch {ι : Type*} {B : Type*} [AddCommGroup B]
    [UniformSpace B] [IsUniformAddGroup B] [CompleteSpace B] [T2Space B]
    [NonarchimedeanAddGroup B] (f : ι → B) (hf : Tendsto f cofinite (𝓝 0)) :
    Summable f := by sorry

section Eval

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}
variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [NonarchimedeanRing B]

/-- **Evaluation of restricted power series at a power-bounded tuple**: the universal
property of `E⟨T_1,…,T_m⟩` (Huber's (1.2); the generic form of the `chartEval`
construction, `FJP/Over/Chart.lean`).  Requires the coefficient images to be null and
the target monoid `{b^t}` bounded — both from `hb` and continuity of `φ`. -/
noncomputable def restrictedEval (φ : E →+* B) (hφ : Continuous φ)
    (hφb : ∀ S : Set E, Bornology.IsBounded S → IsBounded (φ '' S))
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) :
    P E m →+* B := by sorry

@[simp] theorem restrictedEval_C (φ : E →+* B) (hφ : Continuous φ)
    (hφb : ∀ S : Set E, Bornology.IsBounded S → IsBounded (φ '' S))
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (x : E) :
    restrictedEval φ hφ hφb b hb (polyToP (MvPolynomial.C x)) = φ x := by sorry

@[simp] theorem restrictedEval_X (φ : E →+* B) (hφ : Continuous φ)
    (hφb : ∀ S : Set E, Bornology.IsBounded S → IsBounded (φ '' S))
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) (i : Fin m) :
    restrictedEval φ hφ hφb b hb (polyToP (MvPolynomial.X i)) = b i := by sorry

theorem restrictedEval_continuous (φ : E →+* B) (hφ : Continuous φ)
    (hφb : ∀ S : Set E, Bornology.IsBounded S → IsBounded (φ '' S))
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i)) :
    Continuous (restrictedEval φ hφ hφb b hb) := by sorry

/-- Uniqueness of the evaluation extension on the closure of the polynomial subring
(the polynomials are dense in `E⟨T⟩`, [FJP] (4.4)). -/
theorem restrictedEval_unique (φ : E →+* B) (hφ : Continuous φ)
    (hφb : ∀ S : Set E, Bornology.IsBounded S → IsBounded (φ '' S))
    (b : Fin m → B) (hb : ∀ i, IsPowerBounded (b i))
    (ψ : P E m →+* B) (hψ : Continuous ψ)
    (hψC : ∀ x : E, ψ (polyToP (MvPolynomial.C x)) = φ x)
    (hψX : ∀ i, ψ (polyToP (MvPolynomial.X i)) = b i) :
    ψ = restrictedEval φ hφ hφb b hb := by sorry

end Eval

end WeightedParity
