/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FarguesFontaine.Presentation

/-!
# `B^I` is strongly noetherian (Kedlaya Theorem 4.10, special intervals)

Kedlaya's Theorem *"strongly noetherian Robba2"* ([kedlaya-noetherian-ff], §4): the
interval ring `B^I` is strongly noetherian. We prove it for the AD-9 intervals — left
endpoint exactly `|ϖ|^{jn}` — which by the density of the reachable endpoints suffices
for the two charts of the Fargues–Fontaine curve.

The proof is Kedlaya's: by the case-3 presentation (`evalArMvHom`, surjective by
`surjective_evalArMvHom`), the restricted power series ring `B^I⟨T₁,…,T_k⟩` is a
quotient of `A^r⟨T,T₁,…,T_k⟩`, which is noetherian by Theorem 3.2
(`isNoetherianRing_restrictedMvPowerSeries`); quotients of noetherian rings are
noetherian.

## Main results

* `FarguesFontaine.isNoetherianRing_restrictedMvPowerSeries_BISub` : each
  `B^I⟨T₁,…,T_k⟩` is noetherian.
* `FarguesFontaine.isStronglyNoetherian_BISub` : **`B^I` is strongly noetherian**.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Theorem "strongly noetherian Robba2".
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

universe u

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- **Each Tate algebra over `B^I` is noetherian** (Kedlaya Theorem 4.10 for the AD-9
intervals): `B^I⟨T₁,…,T_k⟩` is a quotient of the noetherian `A^r⟨T,T₁,…,T_k⟩` under
the surjective case-3 presentation map. -/
theorem isNoetherianRing_restrictedMvPowerSeries_BISub (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁) (k : ℕ) :
    IsNoetherianRing ↥(restrictedMvPowerSeriesSubring k
      ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
  have : IsNoetherianRing ↥(restrictedMvPowerSeriesSubring (k + 1)
      ↥(ArSub p F ϖ hρ₂0 hρ₂1)) :=
    isNoetherianRing_restrictedMvPowerSeries p F ϖ
  exact isNoetherianRing_of_surjective
    ↥(restrictedMvPowerSeriesSubring (k + 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1))
    ↥(restrictedMvPowerSeriesSubring k ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
    (evalArMvHom p F ϖ h12 hbmem hb)
    (surjective_evalArMvHom p F ϖ h12 j n hbmem hb hexact)

/-- **`B^I` is strongly noetherian** (Kedlaya Theorem 4.10) for the AD-9 intervals —
left endpoint exactly `|ϖ|^{jn}` with the Tate variable `[ϖ^j]ⁿ/p` power-bounded. By
AD-9 these intervals realise both charts of the Fargues–Fontaine curve. -/
theorem isStronglyNoetherian_BISub (h12 : ρ₁ ≤ ρ₂) (j n : ℕ)
    (hbmem : BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)
      ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
    (hb : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ) ^ j) n)) ≤ 1)
    (hexact : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (j * n) = ρ₁) :
    IsStronglyNoetherian ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) where
  isNoetherianRing_restricted := fun k =>
    isNoetherianRing_restrictedMvPowerSeries_BISub p F ϖ h12 j n hbmem hb hexact k

end FarguesFontaine

end
