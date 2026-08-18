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

/-- **([U4d-ii])** If `N` is invertible on the base, the torsion structure morphism is
geometrically reduced: every geometric fibre is the `N`-torsion of the fibre curve,
which is reduced by [U4d-i]. -/
theorem geometricallyReduced_torsionπ {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] (hN : NIsInvertible S N) :
    GeometricallyReduced (E.torsionπ N) := by
  constructor
  intro K _ y Z fst snd hsq
  -- the geometric fibre is the torsion of the base-changed curve
  have hbc := E.torsion_baseChange_isPullback N y
  have hiso : Z ≅ (E.baseChange y).torsion N := hsq.isoIsPullback _ _ hbc
  haveI hNK : (N : K) ≠ 0 := by
    have h1 : NIsInvertible (Spec (CommRingCat.of K)) N := NIsInvertible.of_hom y hN
    exact (nIsInvertible_spec_iff K N).mp h1
  haveI : IsReduced ((E.baseChange y).torsion N) := by
    haveI hAff : IsAffine ((E.baseChange y).torsion N) := by
      haveI : IsFinite ((E.baseChange y).torsionπ N) :=
        (E.baseChange y).torsionπ_isFinite N
      exact isAffine_of_isAffineHom ((E.baseChange y).torsionπ N)
    haveI : _root_.IsReduced (Γ((E.baseChange y).torsion N, ⊤) : CommRingCat.{u}) :=
      isReduced_torsion_sections_of_field (E.baseChange y) N hNK
    exact isReduced_of_isAffine_isReduced _
  exact isReduced_of_isOpenImmersion hiso.hom

/-- **([U4d])** Over a reduced locally-noetherian base on which `N` is invertible, the
`N`-torsion scheme is reduced. -/
theorem isReduced_torsion {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]
    (hN : NIsInvertible S N) [IsReduced S] [IsLocallyNoetherian S] :
    IsReduced (E.torsion N) := by
  haveI : GeometricallyReduced (E.torsionπ N) := geometricallyReduced_torsionπ E N hN
  haveI : Flat (E.torsionπ N) := E.torsionπ_flat N
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (E.torsionπ N)

/-- **([U4f], the vanishing principle)** On a reduced scheme, a global section vanishing
in every residue field is zero. -/
theorem eq_zero_of_forall_evaluation_eq_zero {X : Scheme.{u}} [IsReduced X]
    (s : Γ(X, ⊤)) (h : ∀ x : X, X.evaluation ⊤ x trivial s = 0) : s = 0 :=
  eq_zero_of_basicOpen_eq_bot s
    ((X.basicOpen_eq_bot_iff_forall_evaluation_eq_zero s).mpr (fun x => h x.1))

/-- **([U4f], unit form)** On a reduced scheme, a global unit whose value is `1` in every
residue field is `1`. -/
theorem eq_one_of_forall_evaluation_eq_one {X : Scheme.{u}} [IsReduced X]
    (u : Γ(X, ⊤)) (h : ∀ x : X, X.evaluation ⊤ x trivial u = 1) : u = 1 := by
  have h0 : (u - 1) = 0 := by
    refine eq_zero_of_forall_evaluation_eq_zero _ (fun x => ?_)
    rw [map_sub, h x, map_one, sub_self]
  linear_combination h0

/-- **([U4e-bridge])** The residue-field evaluation of a global section is its
restriction along `Spec κ(x) ⟶ X`, read through `ΓSpecIso`. -/
theorem evaluation_eq_fromSpecResidueField {X : Scheme.{u}} (x : X) (s : Γ(X, ⊤)) :
    X.evaluation ⊤ x trivial s =
      (Scheme.ΓSpecIso (X.residueField x)).hom
        ((X.fromSpecResidueField x).appTop s) := by
  have h1 : (X.fromSpecResidueField x).appTop =
      (X.fromSpecStalk x).appTop ≫ (Spec.map (X.residue x)).appTop :=
    Scheme.Hom.comp_app _ _ _
  rw [h1]
  rw [Scheme.fromSpecStalk_appTop]
  show _ = (Scheme.ΓSpecIso (X.residueField x)).hom
    ((Spec.map (X.residue x)).appTop
      ((Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op
        ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv
          (X.presheaf.germ ⊤ x trivial s))))
  have h2 : (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op =
      𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ≤ ⊤)).op =
      𝟙 (Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens)) from rfl]
    exact (Spec (X.presheaf.stalk x)).presheaf.map_id _
  rw [h2]
  show _ = (Scheme.ΓSpecIso (X.residueField x)).hom
    ((Spec.map (X.residue x)).appTop
      ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv
        (X.presheaf.germ ⊤ x trivial s)))
  have h3 := Scheme.ΓSpecIso_naturality (X.residue x)
  have h4 := congrArg (fun m : Γ(Spec (X.presheaf.stalk x), ⊤) ⟶ X.residueField x =>
    m.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom
      (X.presheaf.germ ⊤ x trivial s))) h3
  simp only [CommRingCat.comp_apply] at h4
  rw [h4]
  simp only [CommRingCat.comp_apply]
  rw [Iso.inv_hom_id_apply]
  rfl

/-- **([U4e])** The diagonal pairing value of a torsion point evaluates to `1` in every
residue field of the base, provided `N` is invertible there. -/
theorem weilPairingEval_self_evaluation_eq_one {S : Scheme.{u}} (E : EllipticCurve S)
    {T : Scheme.{u}} {g : T ⟶ S} {N : ℕ} [NeZero N] (hN : NIsInvertible T N)
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (t : T) :
    T.evaluation ⊤ t trivial (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  classical
  -- the restriction of the point along `Spec κ(t) ⟶ T`
  set δ : Spec (T.residueField t) ⟶ T := T.fromSpecResidueField t with hδ
  have hxr : (EllipticCurve.Point.restrict E δ x).1 ≫ E.mulByHom N = (δ ≫ g) ≫ E.zero := by
    show (δ ≫ x.1) ≫ E.mulByHom N = (δ ≫ g) ≫ E.zero
    rw [Category.assoc, hx, ← Category.assoc]
  haveI : NIsInvertible (Spec (T.residueField t)) N := NIsInvertible.of_hom δ hN
  have hNk : (N : (T.residueField t : CommRingCat.{u})) ≠ 0 := by
    have h1 : IsUnit (N : Γ(Spec (T.residueField t), ⊤)) := ‹_›
    have h2 := h1.map (Scheme.ΓSpecIso (T.residueField t)).hom.hom
    rw [map_natCast] at h2
    exact isUnit_iff_ne_zero.mp h2
  have hspecEq : Spec (CommRingCat.of (T.residueField t : Type u)) =
      Spec (T.residueField t) := rfl
  have hfield := weilPairingEval_self_of_pointOverField E
    (k := (T.residueField t : Type u)) hNk (δ ≫ g)
    (EllipticCurve.Point.restrict E δ x) hxr
  have hrestr := E.weilPairingEval_restrict δ x x hx hx hxr hxr
  rw [evaluation_eq_fromSpecResidueField t (E.weilPairingEval x x hx hx : Γ(T, ⊤))]
  have hval : (T.fromSpecResidueField t).appTop
      (E.weilPairingEval x x hx hx : Γ(T, ⊤)) =
      (E.weilPairingEval (EllipticCurve.Point.restrict E δ x)
        (EllipticCurve.Point.restrict E δ x) hxr hxr :
        Γ(Spec (T.residueField t), ⊤)) := by
    rw [hrestr, Scheme.Γ_map_op]
    rfl
  rw [hval, hfield, map_one]

/-- **(U4, the reduced-base vanishing)** Over a reduced locally-noetherian base on which
`N` is invertible, the diagonal pairing value of any `N`-torsion point is `1`. -/
theorem weilPairingEval_self_of_reduced {S : Scheme.{u}} (E : EllipticCurve S)
    {T : Scheme.{u}} {g : T ⟶ S} {N : ℕ} [NeZero N] (hN : NIsInvertible T N)
    [IsReduced T] (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 :=
  eq_one_of_forall_evaluation_eq_one
    ((E.weilPairingEval x x hx hx : Γ(T, ⊤)))
    (fun t => weilPairingEval_self_evaluation_eq_one E hN x hx t)

/-- **([U4-DENSITY])** On an affine scheme, restriction to the basic open of a
nonzerodivisor is injective on sections. -/
theorem injective_res_basicOpen_of_nonZeroDivisor {X : Scheme.{u}} [IsAffine X]
    (s : Γ(X, ⊤)) (hs : s ∈ nonZeroDivisors (Γ(X, ⊤) : CommRingCat.{u})) :
    Function.Injective
      ((X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op).hom) := by
  haveI hloc := (isAffineOpen_top X).isLocalization_basicOpen s
  have hmapeq : ((X.presheaf.map (homOfLE (le_top : X.basicOpen s ≤ ⊤)).op).hom) =
      algebraMap (Γ(X, ⊤) : CommRingCat.{u}) (Γ(X, X.basicOpen s) : CommRingCat.{u}) := rfl
  rw [hmapeq]
  exact IsLocalization.injective (M := Submonoid.powers s) _
    (Submonoid.powers_le.mpr hs)

end EllipticCurve

end ModularCurves
