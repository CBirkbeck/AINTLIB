/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetNoetherianVertices

/-!
# `F((t))` is a finite-jet base

The finite-jet construction is stated over an abstract base (`IsFJPBase`,
`IsFJPNoetherianBase`; see `FJP/FJPBase.lean`). This file supplies the instances for the
Laurent series field `K = F((t))` over an arbitrary field `F`, recovering the original
[FJP] setting.

* `IsFJPBase (LaurentSeries F)` — pseudouniformizer `t`, from `LaurentSeriesExample`.
* `IsFJPNoetherianBase (LaurentSeries F)` — the Gauss unit ball `F[[t]]⟨T₁,…,T_k⟩` is
  noetherian, by the transpose argument of `ExampleLaurentSeries.lean`: an `X`-power series
  with `k`-variable-polynomial coefficients transposes to a `k`-variable restricted power
  series over `K` (`Psi`), the transpose lands in the unit ball (`psi_coeff_v_le`) and hits
  every integral restricted series (`exists_psi_eq`), so the unit ball is a quotient of the
  noetherian `(MvPolynomial (Fin k) F)⟦X⟧`.

The second instance is **equal-characteristic-specific**: it works because `K° = F[[t]]` is
literally a power series ring. The mixed-characteristic analogue (`ℤ_p⟨T⟩` noetherian) needs
Stacks 00MA, a mathlib gap. Anything depending only on `IsFJPBase` — including the Scottish
Book Problem 24 and 28 witnesses — is unaffected and runs over any complete ultrametric
field with a pseudouniformizer.
-/

open Filter Topology

namespace FiniteJet

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-- `t ∈ F((t))` is a pseudouniformizer: nonzero, of norm `< 1`. -/
noncomputable instance instIsFJPBaseLaurentSeries : IsFJPBase K where
  pseudoUniformizer := LaurentSeriesExample.t F
  pseudoUniformizer_ne_zero := LaurentSeriesExample.t_ne_zero F
  norm_pseudoUniformizer_lt_one := by
    rw [Valued.toNormedField.norm_lt_one_iff, LaurentSeriesExample.valuation_t,
      ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

@[simp] theorem ϖ_laurentSeries : ϖ K = LaurentSeriesExample.t F := rfl

/-- **The Gauss unit ball of `F((t))⟨T₁,…,T_k⟩` is noetherian** ([FJP] Lemma 4.2): the
integral restricted series are exactly the transpose images of the noetherian
`(MvPolynomial (Fin k) F)⟦X⟧`. This is the equal-characteristic input to sheafiness. -/
theorem isNoetherianRing_unitBall_gaussK_laurent (k : ℕ) :
    IsNoetherianRing (unitBall (MvPowerSeries.Restricted K (fun _ : Fin k => (1 : ℝ)))) := by
  classical
  refine isNoetherianRing_of_surjective (PowerSeries (MvPolynomial (Fin k) F)) _
    (RingHom.codRestrict
      (((UnitDiscExample.restrictedGaussEquiv K k).symm.toRingHom).comp
        (LaurentSeriesExample.psiR F k))
      (unitBall _) (fun g => ?_)) ?_
  · -- the transpose image is integral: every coefficient has valuation ≤ 1
    show ‖(UnitDiscExample.restrictedGaussEquiv K k).symm (LaurentSeriesExample.psiR F k g)‖
      ≤ 1
    rw [MvRestricted.norm_eq]
    show MvPowerSeries.gaussNorm _ _ (LaurentSeriesExample.Psi F k g) ≤ 1
    rw [MvPowerSeries.gaussNorm]
    refine Real.iSup_le (fun t => ?_) zero_le_one
    rw [finsupp_prod_one, mul_one]
    rw [Valued.toNormedField.norm_le_one_iff]
    have hv := LaurentSeriesExample.psi_coeff_v_le F k g t 0
      (fun m hm => absurd hm (Nat.not_lt_zero m))
    rwa [show (-(0 : ℕ) : ℤ) = 0 by omega, WithZero.exp_zero] at hv
  · -- surjectivity: integral restricted series are transpose images
    rintro ⟨y, hy⟩
    have hyres : MvPowerSeries.IsRestrictedAdic y.1 :=
      (UnitDiscExample.isRestrictedGauss_one_iff K k y.1).mp y.2
    have hyint : ∀ t, Valued.v (MvPowerSeries.coeff t y.1) ≤ 1 := fun t => by
      rw [← Valued.toNormedField.norm_le_one_iff]
      have h := MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ y) t
      rw [finsupp_prod_one, mul_one] at h
      refine h.trans ?_
      rw [← MvRestricted.norm_eq]
      exact hy
    obtain ⟨g, hg⟩ := LaurentSeriesExample.exists_psi_eq F k y.1 hyres hyint
    exact ⟨g, Subtype.ext (Subtype.ext hg)⟩

/-- `F((t))` supports the sheafiness half of [FJP] as well. -/
noncomputable instance instIsFJPNoetherianBaseLaurentSeries : IsFJPNoetherianBase K where
  isNoetherianRing_unitBall_gauss := isNoetherianRing_unitBall_gaussK_laurent F

end FiniteJet
