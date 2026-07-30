/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedFubini
import «Adic spaces».FJP.TateNullstellensatz
import «Adic spaces».WP.Heads

/-!
# Residue finiteness up the `T_N⟨T⟩` tower

([hrw-decomposition] D-prep, stage 1.)  The `k`-th Tate extension of the
even part of the head is a genuine Tate algebra (`evenTEquiv`, via the
isometric `evenSupportEquiv` and the restricted Fubini), so its maximal
residues are `K`-finite by the affinoid Nullstellensatz, transported along
the constants-compatible quotient equivalence.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N k : ℕ)

/-- The `k`-th Tate extension of the even part is a Tate algebra. -/
noncomputable def evenTEquiv :
    P ↥(wpEvenSupport K w N) k ≃+* P K (k + (N + 1)) :=
  (WeightedParity.mvRestrictedCongr (evenSupportEquiv K w N)
    (norm_evenSupportEquiv K w N)).trans
    (restrictedFubini (N + 1) k).symm

end WeightedParity
