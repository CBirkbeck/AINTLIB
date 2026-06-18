/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwoCurveDualRange
import HasseWeil.EC.IsogenyKernelTwoCurve
import HasseWeil.EC.IsogenyAG.TwoCurveGroupHom
import HasseWeil.EC.IsogenyAG.DualDescent

/-!
# The two-curve `K̄`-dual range inclusion over an algebraically closed char-0 base

Route A, step 1.  For a separable two-curve isogeny `φ : E₁ → E₂` over an **algebraically closed
characteristic-zero** base `F`, the Silverman III.6.1 range inclusion

  `Im([deg φ]_{E₁}*) ⊆ Im(φ*)`

holds.  This is the `K̄`-level input that Route A descends to a finite Galois `L`.

The proof assembles the three **done** pieces over the alg-closed base: the geometric realization
`β := placeRestrictionRealization (ecShell φ) hgh` (a points-bearing `HasseWeil.Isogeny` with
`β.pullback = φ*`) from the norm–conorm preserves-principal wall (discharged from separability alone
in char 0, `placeRestrictionPreservesPrincipal_of_separable_charZero`, sorry-free); the
kernel-translation covariance `xy_family` of `β` (PE-2); the cardinality match `#ker β = deg β`
(T-B1); fed to the two-curve fixed-field range inclusion `mulByInt_deg_rangeIncl_twoCurve`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10–4.11, III.6.1.
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable {W₁ W₂ : WeierstrassCurve F} [W₁.toAffine.IsElliptic] [W₂.toAffine.IsElliptic]

/-- **Char-0 ⟹ separable, two-curve form** (for the Basic `HasseWeil.Isogeny`). The extension
`K(E₁)/β*K(E₂)` is finite-dimensional and algebraic, hence integral, and char 0 (inherited from
`F`), so it is separable by `Algebra.IsSeparable.of_integral`. -/
theorem Isogeny.isSeparable_of_charZero_twoCurve [CharZero F] (β : Isogeny W₁.toAffine W₂.toAffine) :
    β.IsSeparable := by
  letI := β.toAlgebra
  haveI : CharZero W₂.toAffine.FunctionField :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective F W₂.toAffine.FunctionField)
  haveI : Algebra.IsAlgebraic W₂.toAffine.FunctionField W₁.toAffine.FunctionField :=
    ⟨fun z => Isogeny.isAlgebraic_toAlgebra_twoCurve β z⟩
  exact (inferInstance :
    @Algebra.IsSeparable W₂.toAffine.FunctionField W₁.toAffine.FunctionField _ _ β.toAlgebra)

/-- **The Basic-`Isogeny` shell of an `EC.Isogeny`** over the alg-closed base: the function-field
pullback `φ*` packaged as a `HasseWeil.Isogeny` with a *dummy* point map (the geometric point map is
built by the realization, which depends only on the pullback). -/
noncomputable def ecShell (φ : EC.Isogeny W₁.toAffine W₂.toAffine) :
    HasseWeil.Isogeny W₁.toAffine W₂.toAffine where
  pullback := φ.toCurveMap.pullback
  toAddMonoidHom := 0

@[simp] theorem ecShell_pullback (φ : EC.Isogeny W₁.toAffine W₂.toAffine) :
    (ecShell φ).pullback = φ.toCurveMap.pullback := rfl

/-- **Route A, step 1 — the two-curve `K̄`-dual range inclusion over an alg-closed char-0 base.**
For a two-curve `EC.Isogeny φ : E₁ → E₂` over `[IsAlgClosed F] [CharZero F]`, the source-`E₁`
endomorphism `[deg φ]` has `Im([deg φ]*) ⊆ Im(φ*)`. -/
theorem ecIsog_mulByInt_deg_rangeIncl_of_charZero [IsAlgClosed F] [CharZero F]
    (φ : EC.Isogeny W₁.toAffine W₂.toAffine)
    (hreg : ∀ f : (⟨W₂⟩ : Curves.SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₂⟩ : Curves.SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : Curves.SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback f)) :
    (HasseWeil.mulByInt_pullbackAlgHom W₁.toAffine ((ecShell φ).degree : ℤ)
        (by exact_mod_cast (Isogeny.degree_pos_twoCurve (ecShell φ)).ne')).range ≤
      φ.toCurveMap.pullback.range := by
  classical
  -- the norm–conorm preserves-principal wall, from separability alone (char 0)
  have h_pres : WeilPairing.PlaceRestrictionPreservesPrincipal (ecShell φ) :=
    WeilPairing.placeRestrictionPreservesPrincipal_of_separable_charZero (ecShell φ)
      (Isogeny.isSeparable_of_charZero_twoCurve (ecShell φ)) hreg
  -- the group-hom property of the place-restriction point map
  have hgh := WeilPairing.placeRestrictionPointMap_add_of_preservesPrincipal (ecShell φ) h_pres
  -- the geometric realization `β` of `φ*`
  set β := WeilPairing.placeRestrictionRealization (ecShell φ) hgh with hβ
  -- `β.pullback = φ*`
  have hβpb : β.pullback = φ.toCurveMap.pullback :=
    WeilPairing.placeRestrictionRealization_pullback (ecShell φ) hgh
  -- `β` is separable (char 0)
  have hβsep : β.IsSeparable := Isogeny.isSeparable_of_charZero_twoCurve β
  -- `β`'s `PullbackEvaluation_twoCurve` witness (PE-1)
  have hw := WeilPairing.pullbackEvaluation_twoCurve_placeRestrictionRealization (ecShell φ) hgh
  -- PE-2: kernel-translation covariance of `β`
  have hxy := fun k => WeilPairing.xy_family_of_pullbackEvaluation_twoCurve W₁ W₂ β
    (WeilPairing.twoCurvePoleLocus_finite (ecShell φ)) hw k
  -- T-B1: `#ker β = deg β`
  have hcard : Nat.card β.kernel = β.degree :=
    card_kernel_eq_degree_twoCurve β hβsep
      (WeilPairing.twoCurvePoleLocus_finite (ecShell φ)) hw
  -- the two-curve fixed-field range inclusion for `β`
  have hincl := Isogeny.mulByInt_deg_rangeIncl_twoCurve β hxy hcard
  -- transport along `β.pullback = φ*`
  rw [hβpb] at hincl
  -- `β.degree = (ecShell φ).degree` (same algebra), and the `[m]*` AlgHoms differ only by the
  -- proof-irrelevant nonzeroness, so the ranges are defeq.
  exact hincl

end HasseWeil
