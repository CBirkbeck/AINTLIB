/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».WP.HeadReducedMaximal
import «Adic spaces».WedhornBanachTheorem

/-!
# The trivial special fibre of the graph model (BETA)

([hrw-decomposition] BETA, adjudicated route R1′.)  This file builds the
bricks for the level-one bijectivity `A/𝔭 ≅ Q/𝔭Q` of the graph model at a
maximal contraction: closedness of ideals in normed noetherian Tate rings
(the faithful Wedhorn 6.17 engine), the residue-field package, the bounded
evaluation, and the closed-plus-dense argument.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver

/-- **Wedhorn 6.17, faithful, normed form**: every ideal of a complete
normed noetherian Tate ring is closed. -/
theorem isClosed_ideal_of_noetherian_normed {C : Type*} [NormedCommRing C]
    [CompleteSpace C] [IsTateRing C] [IsNoetherianRing C]
    (J : Ideal C) : IsClosed (J : Set C) := by
  haveI : ContinuousSMul C C := ⟨continuous_mul⟩
  refine ValuationSpectrum.fg_topologicalClosure_isClosed J ?_
  have hfg : (Submodule.topologicalClosure J).FG :=
    IsNoetherian.noetherian _
  exact Module.Finite.iff_fg.mpr hfg

end WeightedParity
