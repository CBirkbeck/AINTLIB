/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.SelfField
import ModularCurves.ForMathlib.RegularSectionDensity

/-!
# U4 — vanishing over the universal torsion base

The universal `N`-torsion base `X_N := (modelEllipticCurve 𝕌).torsion N` is affine
(`torsionπ` is finite over the affine atlas), its section ring is `ℤ`-flat (the torsion
is flat over the `ℤ`-flat atlas ring), so sections inject into the `N`-inverted locus,
which is reduced; the diagonal pairing value is `1` at every residue field there by the
field leaf (`weilPairingEval_self_of_field'`), and a reduced ring embeds into the product
of its residue fields.

This file develops the pieces in order:
* [U4a] `X_N` is affine;
* [U4b] the `ℤ`-flatness of its ring;
* [U4c] `N` is a nonzerodivisor there;
* [U4d] the `N`-inverted ring is reduced;
* [U4e] pointwise vanishing at residue fields;
* [U4f] the conclusion.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

namespace EllipticCurve

/-- **([U4a])** The universal `N`-torsion base is affine: `torsionπ` is finite, hence
affine, over the affine atlas `Spec 𝕌`. -/
instance isAffine_torsion_universal (N : ℕ) [NeZero N] :
    IsAffine ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N) := by
  haveI : IsFinite ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N) :=
    (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ_isFinite N
  exact isAffine_of_isAffineHom
    ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N)

/-- The section ring of the universal `N`-torsion base. -/
noncomputable abbrev universalTorsionRing (N : ℕ) : CommRingCat.{u} :=
  Γ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N, ⊤)

/-- **([U4b], ring level)** The section ring is flat over the atlas ring: `torsionπ` is
flat and both schemes are affine. -/
theorem flat_universalTorsionRing (N : ℕ) [NeZero N] :
    RingHom.Flat (((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N).appTop).hom := by
  haveI : Flat ((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N) :=
    (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ_flat N
  exact (HasRingHomProperty.iff_of_isAffine (P := @Flat) (Q := RingHom.Flat)).mp
    inferInstance

/-- **([U4c-i])** The atlas ring is `ℤ`-flat: a localization of a polynomial ring over
`ℤ` (free, hence flat), transported through `ULift`. -/
instance flat_int_weierstrassAtlasRingU : Module.Flat ℤ WeierstrassAtlasRingU.{u} := by
  haveI hfreeP : Module.Free ℤ (MvPolynomial (Fin 5) ℤ) := inferInstance
  haveI hflatP : Module.Flat ℤ (MvPolynomial (Fin 5) ℤ) := Module.Flat.of_free
  haveI hflatL : Module.Flat ℤ WeierstrassAtlasRing := by
    haveI : Module.Flat (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing :=
      IsLocalization.flat _ (Submonoid.powers universalWeierstrass.Δ)
    exact Module.Flat.trans ℤ (MvPolynomial (Fin 5) ℤ) WeierstrassAtlasRing
  exact Module.Flat.of_linearEquiv
    (e := ((ULift.ringEquiv (R := WeierstrassAtlasRing)) :
      WeierstrassAtlasRingU.{u} ≃+* WeierstrassAtlasRing).toAddEquiv.toIntLinearEquiv)

/-- **([U4c-ii])** The universal torsion section ring is `ℤ`-flat: flat over the atlas
ring (U4b), which is `ℤ`-flat (U4c-i). -/
instance flat_int_universalTorsionRing (N : ℕ) [NeZero N] :
    Module.Flat ℤ (universalTorsionRing.{u} N) := by
  letI : Algebra (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) :
      CommRingCat.{u}) (universalTorsionRing.{u} N) :=
    (((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N).appTop).hom.toAlgebra
  haveI hflatA : Module.Flat
      (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) : CommRingCat.{u})
      (universalTorsionRing.{u} N) := flat_universalTorsionRing N
  haveI hflatZA : Module.Flat ℤ
      (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) : CommRingCat.{u}) :=
    Module.Flat.of_linearEquiv
      (e := ((Scheme.ΓSpecIso (CommRingCat.of WeierstrassAtlasRingU.{u})).commRingCatIsoToRingEquiv :
        (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) : CommRingCat.{u}) ≃+*
          WeierstrassAtlasRingU.{u}).toAddEquiv.toIntLinearEquiv)
  haveI : IsScalarTower ℤ
      (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) : CommRingCat.{u})
      (universalTorsionRing.{u} N) :=
    IsScalarTower.of_algebraMap_eq (fun n => by
      show (n : universalTorsionRing.{u} N) =
        (((modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N).appTop).hom
          ((algebraMap ℤ (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) :
            CommRingCat.{u})) n)
      rw [show (algebraMap ℤ (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) :
          CommRingCat.{u})) n = (n : (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) :
            CommRingCat.{u})) from map_intCast _ n, map_intCast])
  exact Module.Flat.trans ℤ
    (Γ(Spec (CommRingCat.of WeierstrassAtlasRingU.{u}), ⊤) : CommRingCat.{u})
    (universalTorsionRing.{u} N)

/-- **([U4c])** `N` is a nonzerodivisor on the universal torsion section ring. -/
theorem natCast_mem_nonZeroDivisors_universalTorsionRing (N : ℕ) [NeZero N] :
    ((N : ℤ) : universalTorsionRing.{u} N) ∈
      nonZeroDivisors (universalTorsionRing.{u} N) :=
  isSMulRegular_natCast_of_flat _ (by exact_mod_cast NeZero.ne N)

/-- **([U4d-i])** Over a field in which `N` is invertible, the `N`-torsion of any
elliptic-curve record has reduced section ring: `torsionπ` is étale, hence the section
ring is formally unramified over the field, hence reduced. -/
theorem isReduced_torsion_sections_of_field {k : Type u} [Field k]
    (E' : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] (hNk : (N : k) ≠ 0) :
    IsReduced (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) := by
  haveI hfin : IsFinite (E'.torsionπ N) := E'.torsionπ_isFinite N
  haveI hAff : IsAffine (E'.torsion N) := isAffine_of_isAffineHom (E'.torsionπ N)
  haveI hetale : Etale (E'.torsionπ N) :=
    E'.torsionπ_etale N ((nIsInvertible_spec_iff k N).mpr hNk)
  haveI hFU : AlgebraicGeometry.FormallyUnramified (E'.torsionπ N) := inferInstance
  -- read the property at the ring level, with `k` itself as the base
  letI : Algebra k (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (E'.torsionπ N).appTop).hom).toAlgebra
  letI : Algebra k (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  letI : Algebra (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u})
      (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    ((E'.torsionπ N).appTop).hom.toAlgebra
  haveI hUnram : Algebra.FormallyUnramified
      (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u})
      (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    (HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.FormallyUnramified)
      (Q := RingHom.FormallyUnramified)).mp hFU
  haveI : IsScalarTower k (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u})
      (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hUnramBase : Algebra.FormallyUnramified k
      (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}) :=
    Algebra.FormallyUnramified.of_equiv (R := k) (A := k)
      (AlgEquiv.ofRingEquiv (f :=
        ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv :
          (CommRingCat.of k : CommRingCat.{u}) ≃+*
            (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}))) (fun _ => rfl))
  haveI : Algebra.FormallyUnramified k (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    Algebra.FormallyUnramified.comp k (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}) _
  -- finiteness of the torsion algebra, for `EssFiniteType`
  haveI hfinRing : Module.Finite (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u})
      (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) := by
    have h := ((isFinite_iff (f := E'.torsionπ N)).mp hfin).2 ⊤ (isAffineOpen_top _)
    exact h
  haveI : Module.Finite k (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}) := by
    refine Module.Finite.of_surjective (Algebra.linearMap k _) (fun z => ?_)
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom z, ?_⟩
    show ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom z) = z
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
    rfl
  haveI : Module.Finite k (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    Module.Finite.trans (Γ(Spec (CommRingCat.of k), ⊤) : CommRingCat.{u}) _
  haveI : Algebra.FiniteType k (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    Module.Finite.finiteType (Γ(E'.torsion N, ⊤) : CommRingCat.{u})
  haveI : Algebra.EssFiniteType k (Γ(E'.torsion N, ⊤) : CommRingCat.{u}) :=
    Algebra.EssFiniteType.of_finiteType k _
  exact Algebra.FormallyUnramified.isReduced_of_field k _

end EllipticCurve

end ModularCurves
