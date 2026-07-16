/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# The nonarchimedean max norm on dual numbers (finite-jet vertices 𝓑 and 𝓓)

Source: [FJP] §1.4–§2. The comparison vertices of the finite-jet Milnor square are
`𝓑 = k⟨W,Q⟩/(Q²)` and `𝓓 = L⟨Q⟩/(Q²)`, i.e. *dual numbers* over `k⟨W⟩` resp. `L`, carrying
the quotient Gauss norm — which is the **max norm** `‖f₀ + Q f₁‖ = max(‖f₀‖, ‖f₁‖)`
([FJP] Lemma 2.2 and §5 (5.2): "Every element of 𝓑 is uniquely `f + Qg` with
`f, g ∈ k⟨W⟩`").

This file equips `DualNumber R` (mathlib's `TrivSqZeroExt R R`) with that norm for an
ultrametric normed base and provides the instance stack ([FJP] Prop 2.1's completeness and
noetherianity inputs for these vertices), the jet-power formula
`(f + Qg)ⁿ = fⁿ + n f^(n-1) Q g` ([FJP] (5.2)), and componentwise functoriality.
-/

open Filter Topology

namespace FiniteJet

namespace JetNorm

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R]

/-- The max norm on dual numbers ([FJP] Lemma 2.2: the quotient norm of `k⟨W,Q⟩/(Q²)` is
`max(‖f₀‖, ‖f₁‖)`). -/
noncomputable def jetNorm (x : DualNumber R) : ℝ := max ‖x.fst‖ ‖x.snd‖

/-- The max norm is a ring norm (submultiplicativity uses the ultrametric inequality on the
cross term of `(a,b)(c,d) = (ac, ad + bc)`). -/
noncomputable def isRingNorm : RingNorm (DualNumber R) where
  toFun := jetNorm
  map_zero' := by sorry
  add_le' := by sorry
  neg' := by sorry
  mul_le' := by sorry
  eq_zero_of_map_eq_zero' := by sorry

noncomputable instance : NormedCommRing (DualNumber R) where
  toNormedRing := RingNorm.toNormedRing isRingNorm
  mul_comm := mul_comm

theorem norm_def (x : DualNumber R) : ‖x‖ = max ‖x.fst‖ ‖x.snd‖ := by sorry

@[simp] theorem norm_inl (a : R) : ‖(TrivSqZeroExt.inl a : DualNumber R)‖ = ‖a‖ := by sorry

@[simp] theorem norm_eps_smul [NormOneClass R] (a : R) :
    ‖(TrivSqZeroExt.inr a : DualNumber R)‖ = ‖a‖ := by sorry

instance : IsUltrametricDist (DualNumber R) := by sorry

instance [NormOneClass R] : NormOneClass (DualNumber R) := by sorry

/-- Dual numbers over a complete base are complete (product of two copies). -/
instance [CompleteSpace R] : CompleteSpace (DualNumber R) := by sorry

/-- The jet-power formula `(f + εg)ⁿ = fⁿ + n f^(n-1) ε g` ([FJP] (5.2), verbatim:
"`(f + Qg)ⁿ = fⁿ + n f^(n-1) Q g` is bounded independently of `n`"). -/
theorem pow_eq (a b : R) (n : ℕ) :
    ((TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber R)) ^ n =
      TrivSqZeroExt.inl (a ^ n) + TrivSqZeroExt.inr ((n : R) * a ^ (n - 1) * b) := by sorry

/-! ### Componentwise functoriality -/

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S]

/-- Componentwise application of a ring homomorphism to dual numbers. -/
def mapHom (φ : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := ⟨φ x.fst, φ x.snd⟩
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

@[simp] theorem mapHom_fst (φ : R →+* S) (x : DualNumber R) : (mapHom φ x).fst = φ x.fst := rfl

@[simp] theorem mapHom_snd (φ : R →+* S) (x : DualNumber R) : (mapHom φ x).snd = φ x.snd := rfl

/-- `mapHom` of a norm-preserving homomorphism preserves the jet norm. -/
theorem norm_mapHom (φ : R →+* S) (hφ : ∀ a, ‖φ a‖ = ‖a‖) (x : DualNumber R) :
    ‖mapHom φ x‖ = ‖x‖ := by sorry

theorem mapHom_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (mapHom φ) := by sorry

/-! ### Noetherianity: `DualNumber S` is a quotient of `S[X]`

[FJP] Prop 2.1 (verbatim): "Each of 𝓑, 𝒞, 𝒟 is a quotient of a finite Tate algebra over `k`,
so each is strongly noetherian."  The engine at the coefficient level: dual numbers over a
noetherian ring are noetherian, via the surjection `S[X] → DualNumber S`, `X ↦ ε`. -/

/-- Evaluation of polynomials at `ε` is surjective onto the dual numbers. -/
theorem aeval_eps_surjective (S : Type*) [CommRing S] :
    Function.Surjective (Polynomial.aeval (R := S) (TrivSqZeroExt.inr 1 : DualNumber S)) := by
  sorry

/-- Dual numbers over a noetherian commutative ring are noetherian. -/
instance isNoetherianRing (S : Type*) [CommRing S] [IsNoetherianRing S] :
    IsNoetherianRing (DualNumber S) := by sorry

end JetNorm

end FiniteJet
