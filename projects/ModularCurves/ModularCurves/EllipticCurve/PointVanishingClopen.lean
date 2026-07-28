/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.MulByHomEtale
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.AgreementLocusClopen

/-!
# The vanishing locus of a killed torsion point is clopen (YFULL route γ)

For `N` invertible on `S`, `E[N] ⟶ S` is finite étale (`Torsionπ.etale'`) and separated
(`torsionι` is a closed immersion and `E ⟶ S` is proper). Hence, for a point `R` of `E`
over `T` killed by `N`, the locus in `T` where `R` agrees with the zero section — the
range of the agreement-locus inclusion of the two `E[N]`-classifiers `pointToTorsion R`
and `pointToTorsion 0` — is **clopen** (`isClopen_range_agreementι`).

Taking `R` to run over the nonzero combinations `[c]P + [d]Q` of a pair `(P, Q)`, the
union of these finitely many clopen vanishing loci is closed, so its complement — the
locus where all nonzero combinations are nonvanishing (the Drinfeld full-level locus for
`N` invertible) — is open. This is the openness input of the `Y(N)` clopen leaf.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- For `N` invertible, `E[N] ⟶ S` is separated: `torsionπ N = torsionι N ≫ E.π` is a
composite of the closed immersion `torsionι N` and the (proper, hence separated) structure
map `E.π`. -/
instance isSeparated_torsionπ : IsSeparated (E.torsionπ N) := by
  haveI : IsSeparated E.π := E.proper.toIsSeparated
  -- `IsSeparated (torsionι N)` goes through `Mono`, which needs the closed immersion in
  -- scope explicitly on this pin.
  haveI : IsClosedImmersion (E.torsionι N) := E.torsionι_isClosedImmersion N
  rw [← E.torsionι_π]
  infer_instance

/-- The zero point of `E` over `t` is killed by `N`. -/
theorem zero_point_comp_mulByHom {T : Scheme.{u}} (t : T ⟶ S) :
    ((0 : E.Point t) : T ⟶ E.E) ≫ E.mulByHom N = t ≫ E.zero :=
  (E.smul_eq_zero_iff_comp_mulByHom t N 0).mp (smul_zero _)

/-- The vanishing locus in `T` of an `N`-killed point `R` of `E` over `t`: the range of
the agreement-locus inclusion of the `E[N]`-classifiers of `R` and of the zero point. -/
noncomputable def pointVanishSet {T : Scheme.{u}} (t : T ⟶ S) (R : E.Point t)
    (hR : R.1 ≫ E.mulByHom N = t ≫ E.zero) : Set T :=
  Set.range (AlgebraicGeometry.agreementι (E.torsionπ N)
    (E.pointToTorsion R hR)
    (E.pointToTorsion (0 : E.Point t) (E.zero_point_comp_mulByHom N t))
    (by rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ])).base

/-- **[YF-CLOPEN engine, curve form]** For `N` invertible, the vanishing locus of an
`N`-killed point `R` of `E` over `t` is clopen. -/
theorem isClopen_pointVanishSet (hN : NIsInvertible S N) {T : Scheme.{u}} (t : T ⟶ S)
    (R : E.Point t) (hR : R.1 ≫ E.mulByHom N = t ≫ E.zero) :
    IsClopen (E.pointVanishSet N t R hR) := by
  haveI : Etale (E.torsionπ N) := Torsionπ.etale' E N hN
  exact AlgebraicGeometry.isClopen_range_agreementι _ _ _ _

end EllipticCurve

end ModularCurves
