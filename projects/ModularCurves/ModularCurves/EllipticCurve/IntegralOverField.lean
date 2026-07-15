/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.GroupLawAxioms
import ModularCurves.EllipticCurve.GroupLaw

/-!
# An elliptic curve over a field is an integral scheme

`E.E` is integral for `E : EllipticCurve (Spec k)`, `k` a field. The base has a single point, so
the `LocallyWeierstrass` chart at that point is global: its affine open is `⊤`, its inclusion is
an isomorphism, and `E.E ≅ pullback E.π ⊤.ι ≅ projModel W` for a Weierstrass curve `W` over
`Γ(Spec k, ⊤) ≅ k` — integral by `isIntegral_projModel_u` (a projective Weierstrass model over a
field is integral). `IsIntegral.of_isIso` transports.

This discharges the `[IsIntegral E.E]` hypothesis of the endomorphism-degree tranche
(`endDeg_comp_of_isIntegral`, `endDeg_comp_mulBy_of_isIntegral`, `endo_surjective` —
`EndomorphismDegree.lean`) at every geometric-fibre call site `S = Spec k`.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

/-- **(E-INT)** An elliptic curve over a field is an integral scheme: the single-point base makes
the local Weierstrass chart global, and the projective Weierstrass model over a field is integral
(`isIntegral_projModel_u`). -/
instance isIntegral_of_field {k : Type u} [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) : IsIntegral E.E := by
  haveI hsub : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI hne : Nonempty ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨U, hsU, W, hell, e, -, -⟩ := E.localModel hne.some
  -- the chart is the whole (single-point) base
  have hUtop : U.1 = ⊤ := by
    refine top_unique fun x _ => ?_
    rwa [Subsingleton.elim x hne.some]
  -- its inclusion is an isomorphism
  haveI : IsIso U.1.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, hUtop]
  haveI : IsIso (pullback.fst E.π U.1.ι) := inferInstance
  -- the chart ring is a field
  have hf : IsField ↑Γ(Spec (CommRingCat.of k), U.1) := by
    have e1 : Γ(Spec (CommRingCat.of k), U.1) ≅ Γ(Spec (CommRingCat.of k), ⊤) :=
      (Spec (CommRingCat.of k)).presheaf.mapIso (eqToIso (congrArg Opposite.op hUtop))
    have e2 : Γ(Spec (CommRingCat.of k), ⊤) ≅ CommRingCat.of k :=
      Scheme.ΓSpecIso (CommRingCat.of k)
    exact MulEquiv.isField (Field.toIsField k)
      (e1 ≪≫ e2).commRingCatIsoToRingEquiv.toMulEquiv
  letI : Field ↑Γ(Spec (CommRingCat.of k), U.1) := hf.toField
  haveI : IsIntegral (projModel W) := isIntegral_projModel_u W
  exact IsIntegral.of_isIso (e.symm ≪≫ asIso (pullback.fst E.π U.1.ι)).hom

end EllipticCurve

end ModularCurves
