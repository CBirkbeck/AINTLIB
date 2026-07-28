/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.CurveAdicPresentation
import «Adic spaces».AdicSpaceV

/-!
# The Fargues–Fontaine affinoid charts as charts of `𝒱`

`windowSubAffinoid` presents a rational subdomain of a window chart ring as a
sheafy affinoid pair (`AffinoidAdicPresentation`).  Wedhorn Definition 8.22 asks
for more: the chart must be an object of `𝒱`, i.e. carry the stalk package.
Since the window chart rings are Tate and strongly noetherian, the P5-2 package
`spaVObjTate` applies, and `AffinoidVChart.ofTate` repackages it.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace Topology
  Filter CategoryTheory Opposite Pointwise

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

noncomputable local instance (n : ℤ) : IsTateRing (windowChartRing p F ϖ n) :=
  isTateRing_bigWindowChart p F (windowUnif p F ϖ n)

noncomputable local instance (n : ℤ) :
    IsStronglyNoetherian (windowChartRing p F ϖ n) :=
  isStronglyNoetherian_canonical_window p F ϖ n

noncomputable local instance (n : ℤ) :
    IsNoetherianRing (windowChartRing p F ϖ n) :=
  IsStronglyNoetherian.isNoetherianRing _

/-- **The Fargues–Fontaine window sub-affinoids are charts of `𝒱`** (Wedhorn
Definition 8.22): a rational localization of a window chart ring is a sheafy
strongly-noetherian complete Tate ring, so its `Spa` is an object of `𝒱`. -/
noncomputable def windowSubVChart (n : ℤ)
    (D' : RationalLocData (windowChartRing p F ϖ n)) :
    ValuationSpectrum.AffinoidVChart :=
  letI : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
  letI : IsStronglyNoetherian (presheafValue D') :=
    presheafValue_isStronglyNoetherian_faithful D'
  letI : @CompleteSpace (presheafValue D')
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D')) :=
    completeSpace_right_presheafValue D'
  ValuationSpectrum.AffinoidVChart.ofTate (presheafValue D')

end FarguesFontaine

end
