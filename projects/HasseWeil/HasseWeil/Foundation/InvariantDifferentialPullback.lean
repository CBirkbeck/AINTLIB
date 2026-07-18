/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Foundation.Auxiliary.PullbackKaehler
import HasseWeil.Foundation.OmegaPullbackCoeff

/-!
# Pullback of the invariant differential along an isogeny

This file specializes the generic `AlgHom.pullbackKaehler` API from
`HasseWeil/PullbackKaehler.lean` to elliptic curve isogenies. It provides:

* `Isogeny.pullbackKaehler` — the additive map on `Ω[K(E)/F]` induced by an isogeny.
* The bridge `pullbackKaehler_invariantDifferential` connecting this abstract pullback
  to `omegaPullbackCoeff` (the K(E)-valued pullback coefficient defined elsewhere).
* Functoriality and F-linearity specializations.

Once these are in place, the chain rule
`omegaPullbackCoeff_comp_of_base : a_{α∘β} = c_α · a_β` (for `c_α ∈ F`) follows from
a string of three rewrites.
-/

open WeierstrassCurve

namespace HasseWeil

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve F} [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

/-- The additive endomorphism of `Ω[K(E)/F]` induced by an isogeny `α : E → E`,
defined as the pullback along the algebra hom `α.pullback : K(E) →ₐ[F] K(E)`. -/
noncomputable def pullbackKaehler (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential F KE →+ KaehlerDifferential F KE :=
  α.pullback.pullbackKaehler

/-- `pullbackKaehler` on the universal derivation: `α.pullbackKaehler (D x) = D (α.pullback x)`. -/
@[simp]
theorem pullbackKaehler_D (α : Isogeny W.toAffine W.toAffine) (x : KE) :
    α.pullbackKaehler (KaehlerDifferential.D F KE x) =
      KaehlerDifferential.D F KE (α.pullback x) :=
  AlgHom.pullbackKaehler_D α.pullback x

/-- `pullbackKaehler` is `F`-linear (pulls out base field scalars). -/
theorem pullbackKaehler_smul_F (α : Isogeny W.toAffine W.toAffine)
    (c : F) (ω : KaehlerDifferential F KE) :
    α.pullbackKaehler (c • ω) = c • α.pullbackKaehler ω :=
  AlgHom.pullbackKaehler_smul_R α.pullback c ω

/-- `pullbackKaehler` is semilinear with respect to K(E) scalars: a K(E)-scalar `s`
becomes `α.pullback s` after the pullback. -/
theorem pullbackKaehler_smul_KE (α : Isogeny W.toAffine W.toAffine)
    (s : KE) (ω : KaehlerDifferential F KE) :
    α.pullbackKaehler (s • ω) = α.pullback s • α.pullbackKaehler ω :=
  AlgHom.pullbackKaehler_smul_S α.pullback s ω

/-- Composition of isogenies and `pullbackKaehler`. Note: by the convention in
`HasseWeil.Isogeny.comp` (where `(α.comp β).pullback = β.pullback.comp α.pullback`),
the induced action on Ω composes contravariantly:
`(α.comp β).pullbackKaehler = β.pullbackKaehler.comp α.pullbackKaehler`. -/
@[simp]
theorem pullbackKaehler_comp (α β : Isogeny W.toAffine W.toAffine) :
    (α.comp β).pullbackKaehler =
      β.pullbackKaehler.comp α.pullbackKaehler := by
  change (α.comp β).pullback.pullbackKaehler = _
  change (β.pullback.comp α.pullback).pullbackKaehler = _
  rw [AlgHom.pullbackKaehler_comp]
  rfl

/-- The bridge: applying `α.pullbackKaehler` to the invariant differential gives the
omega-based pullback coefficient times the invariant differential. This is the
invariant differential reformulation of `omegaPullbackCoeff_spec`. -/
theorem pullbackKaehler_invariantDifferential
    (α : Isogeny W.toAffine W.toAffine) :
    α.pullbackKaehler (invariantDifferential W.toAffine) =
      omegaPullbackCoeff W α • invariantDifferential W.toAffine := by
  rw [show invariantDifferential W.toAffine =
      (u_gen W)⁻¹ • KaehlerDifferential.D F KE
        (algebraMap R KE
          (algebraMap (Polynomial F) R Polynomial.X)) from rfl]
  rw [pullbackKaehler_smul_KE, pullbackKaehler_D]
  rw [show α.pullback (u_gen W)⁻¹ = (alpha_star_u W α)⁻¹ from by
    rw [map_inv₀, alpha_star_u_eq]]
  exact (omegaPullbackCoeff_spec W α).symm

end Isogeny

/-! ### The chain rule for omegaPullbackCoeff (Silverman III.5.6a)

For an isogeny composition `α.comp β` whose outer factor `α` has pullback coefficient
in the base field `F`, the omega-based pullback coefficient multiplies:
`a_{α∘β} = a_α · a_β`. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- The chain rule for omegaPullbackCoeff, assuming `a_α` is in the base field.
If `a_α = algebraMap F KE c_α` for some `c_α ∈ F`, then `a_{α∘β} = c_α · a_β`.

Proof (Silverman III.5.6a): pulling the invariant differential along `α.comp β`
gives `(α∘β)*(ω) = β*(α*(ω)) = β*(c_α · ω) = c_α · β*(ω) = c_α · a_β · ω`. The
critical step `β*(c_α · ω) = c_α · β*(ω)` uses `F`-linearity of the pullback,
which is `Isogeny.pullbackKaehler_smul_F`. -/
theorem omegaPullbackCoeff_comp_of_base (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (α β : Isogeny W.toAffine W.toAffine) (c_α : F)
    (hα : omegaPullbackCoeff W α =
      algebraMap F W.toAffine.FunctionField c_α) :
    omegaPullbackCoeff W (α.comp β) =
      algebraMap F W.toAffine.FunctionField c_α * omegaPullbackCoeff W β := by
  apply omegaPullbackCoeff_unique
  rw [← Isogeny.pullbackKaehler_invariantDifferential (α.comp β),
      Isogeny.pullbackKaehler_comp, AddMonoidHom.comp_apply,
      Isogeny.pullbackKaehler_invariantDifferential α, hα]
  rw [Isogeny.pullbackKaehler_smul_KE]
  rw [show β.pullback (algebraMap F W.toAffine.FunctionField c_α) =
      algebraMap F W.toAffine.FunctionField c_α from β.pullback.commutes c_α]
  rw [Isogeny.pullbackKaehler_invariantDifferential β, smul_smul]

end HasseWeil
