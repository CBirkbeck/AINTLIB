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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

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
    ((N : ℕ) : universalTorsionRing.{u} N) ∈
      nonZeroDivisors (universalTorsionRing.{u} N) := by
  have h := isSMulRegular_natCast_of_flat (universalTorsionRing.{u} N)
    (N := (N : ℤ)) (by exact_mod_cast NeZero.ne N)
  rwa [show (((N : ℤ) : universalTorsionRing.{u} N)) =
    ((N : ℕ) : universalTorsionRing.{u} N) from by push_cast; ring] at h

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

/-- **([U4-REGULAR])** Over an affine base whose `N`-inverted locus is reduced and on
which `N` is a nonzerodivisor, the diagonal pairing value is `1`. -/
theorem weilPairingEval_self_of_nonZeroDivisor {S : Scheme.{u}} (E : EllipticCurve S)
    {T : Scheme.{u}} [IsAffine T] {g : T ⟶ S} {N : ℕ} [NeZero N]
    (hreg : (N : Γ(T, ⊤)) ∈ nonZeroDivisors (Γ(T, ⊤) : CommRingCat.{u}))
    [IsReduced (T.basicOpen (N : Γ(T, ⊤)) : Scheme.{u})]
    (x : E.Point g) (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  set U : T.Opens := T.basicOpen (N : Γ(T, ⊤)) with hU
  set i : (U : Scheme.{u}) ⟶ T := U.ι with hi
  have hxr : (EllipticCurve.Point.restrict E i x).1 ≫ E.mulByHom N =
      (i ≫ g) ≫ E.zero := by
    show (i ≫ x.1) ≫ E.mulByHom N = (i ≫ g) ≫ E.zero
    rw [Category.assoc, hx, ← Category.assoc]
  haveI hNU : NIsInvertible (U : Scheme.{u}) N := by
    show IsUnit ((N : ℕ) : Γ((U : Scheme.{u}), ⊤))
    have h1 : IsUnit (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (N : Γ(T, ⊤))) :=
      T.toRingedSpace.isUnit_res_basicOpen _
    have hnat : (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom ((N : ℕ) : Γ(T, ⊤)) =
        ((N : ℕ) : Γ(T, U)) := map_natCast _ N
    rw [hnat] at h1
    have h2 := h1.map U.topIso.inv.hom
    rw [show (U.topIso.inv.hom ((N : ℕ) : Γ(T, U))) = ((N : ℕ) : Γ((U : Scheme.{u}), ⊤))
      from map_natCast _ N] at h2
    exact h2
  have hone := weilPairingEval_self_of_reduced E hNU (EllipticCurve.Point.restrict E i x) hxr
  have hres := E.weilPairingEval_restrict i x x hx hx hxr hxr
  rw [hone] at hres
  refine injective_res_basicOpen_of_nonZeroDivisor (N : Γ(T, ⊤)) hreg ?_
  rw [map_one]
  have hbridge : U.topIso.hom.hom ((Scheme.Γ.map i.op).hom
        (E.weilPairingEval x x hx hx : Γ(T, ⊤))) =
      (T.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (E.weilPairingEval x x hx hx : Γ(T, ⊤)) := by
    rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
    show (U.topIso.hom.hom
      ((T.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op).hom _)) = _
    have hcomp : U.topIso.hom.hom
        ((T.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op).hom
          (E.weilPairingEval x x hx hx : Γ(T, ⊤))) =
        ((T.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op) ≫ U.topIso.hom).hom
          (E.weilPairingEval x x hx hx : Γ(T, ⊤)) := rfl
    rw [hcomp]
    refine congrArg (fun m : Γ(T, ⊤) ⟶ Γ(T, U) => m.hom
      (E.weilPairingEval x x hx hx : Γ(T, ⊤))) ?_
    rw [Scheme.Opens.topIso_hom]
    exact (T.presheaf.map_comp _ _).symm.trans
      (congrArg T.presheaf.map (Subsingleton.elim _ _))
  rw [← hbridge, ← hres, map_one]

/-- **([U4-NLOCUS])** The `N`-inverted locus of the torsion base is the torsion over the
`N`-inverted locus of the base, hence reduced when the base is. -/
theorem isReduced_basicOpen_natCast_torsion {S : Scheme.{u}} (E : EllipticCurve S)
    (N : ℕ) [NeZero N] [IsReduced S] [IsLocallyNoetherian S] :
    IsReduced ((E.torsion N).basicOpen ((N : ℕ) : Γ(E.torsion N, ⊤)) : Scheme.{u}) := by
  -- the locus is the preimage of the base's `N`-locus
  set V : S.Opens := S.basicOpen ((N : ℕ) : Γ(S, ⊤)) with hV
  have hpre : (E.torsionπ N) ⁻¹ᵁ V =
      (E.torsion N).basicOpen ((N : ℕ) : Γ(E.torsion N, ⊤)) := by
    rw [hV, Scheme.preimage_basicOpen]
    refine congrArg (E.torsion N).basicOpen ?_
    exact map_natCast ((E.torsionπ N).appTop).hom N
  -- the base's `N`-locus is reduced, locally noetherian, and `N` is invertible there
  haveI : IsReduced (V : Scheme.{u}) := isReduced_of_isOpenImmersion V.ι
  haveI : IsLocallyNoetherian (V : Scheme.{u}) :=
    isLocallyNoetherian_of_isOpenImmersion V.ι
  haveI hNV : NIsInvertible (V : Scheme.{u}) N := by
    show IsUnit ((N : ℕ) : Γ((V : Scheme.{u}), ⊤))
    have h1 : IsUnit (S.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ((N : ℕ) : Γ(S, ⊤))) :=
      S.toRingedSpace.isUnit_res_basicOpen _
    have hnat : (S.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom ((N : ℕ) : Γ(S, ⊤)) =
        ((N : ℕ) : Γ(S, V)) := map_natCast _ N
    rw [hnat] at h1
    have h2 := h1.map V.topIso.inv.hom
    rw [show (V.topIso.inv.hom ((N : ℕ) : Γ(S, V))) = ((N : ℕ) : Γ((V : Scheme.{u}), ⊤))
      from map_natCast _ N] at h2
    exact h2
  -- the torsion over that locus is reduced, and it is the preimage
  haveI hred : IsReduced ((E.baseChange V.ι).torsion N) :=
    isReduced_torsion (E.baseChange V.ι) N hNV
  have hsq := E.torsion_baseChange_isPullback N V.ι
  haveI : IsOpenImmersion (E.torsionBaseChangeHom N V.ι) :=
    MorphismProperty.of_isPullback hsq.flip inferInstance
  -- the image of that open immersion is exactly the preimage locus
  have hoRange : (E.torsionBaseChangeHom N V.ι).opensRange = (E.torsionπ N) ⁻¹ᵁ V := by
    apply TopologicalSpace.Opens.ext
    show Set.range (E.torsionBaseChangeHom N V.ι).base = _
    have h1 : (E.torsionBaseChangeHom N V.ι) =
        hsq.isoPullback.hom ≫ pullback.fst (E.torsionπ N) V.ι :=
      (hsq.isoPullback_hom_fst).symm
    rw [h1, Scheme.Hom.comp_base]
    show Set.range ((pullback.fst (E.torsionπ N) V.ι).base ∘ hsq.isoPullback.hom.base) = _
    rw [Set.range_comp]
    have hsurj : Set.range (hsq.isoPullback.hom.base) = Set.univ := by
      rw [Set.range_eq_univ]
      intro z
      exact ⟨hsq.isoPullback.inv.base z, by
        show (hsq.isoPullback.inv ≫ hsq.isoPullback.hom).base z = z
        rw [Iso.inv_hom_id]; rfl⟩
    rw [hsurj, Set.image_univ]
    rw [Scheme.Pullback.range_fst]
    show (E.torsionπ N).base ⁻¹' (Set.range V.ι.base) = _
    rw [show Set.range V.ι.base = (V : Set S) from V.range_ι]
    rfl
  -- transport reducedness along the induced isomorphism
  have hiso := (E.torsionBaseChangeHom N V.ι).isoOpensRange
  rw [hoRange, hpre] at hiso
  exact isReduced_of_isOpenImmersion hiso.inv

/-- **(U4, the universal vanishing)** The diagonal pairing value of the tautological
point over the universal `N`-torsion base is `1`. -/
theorem weilPairingEval_self_universal_eq_one (N : ℕ) [NeZero N] :
    ((modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval (N := N)
        (tautTorsionPoint _ N) (tautTorsionPoint _ N)
        (tautTorsionPoint_killedBy _ N) (tautTorsionPoint_killedBy _ N) :
      Γ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N, ⊤)) = 1 := by
  haveI : IsReduced (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})) := by
    haveI : _root_.IsReduced (CommRingCat.of WeierstrassAtlasRingU.{u}) :=
      inferInstanceAs (_root_.IsReduced WeierstrassAtlasRingU.{u})
    infer_instance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of WeierstrassAtlasRingU.{u})) := by
    haveI : IsNoetherianRing WeierstrassAtlasRingU.{u} := inferInstance
    infer_instance
  haveI : IsReduced
      (((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N).basicOpen
        ((N : ℕ) : Γ((modelEllipticCurve universalWeierstrassLocU.{u}).torsion N, ⊤)) :
        Scheme.{u}) :=
    isReduced_basicOpen_natCast_torsion (modelEllipticCurve universalWeierstrassLocU.{u}) N
  exact weilPairingEval_self_of_nonZeroDivisor
    (modelEllipticCurve universalWeierstrassLocU.{u})
    (natCast_mem_nonZeroDivisors_universalTorsionRing N)
    (tautTorsionPoint _ N) (tautTorsionPoint_killedBy _ N)

/-- **([ASM-1])** The record-level base-change iso for models over an arbitrary ring map
(the general-ring sibling of `modelBaseChangeIsoAsOver`). -/
theorem modelBaseChangeIsoAsOver_ring {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (R' : Type u) [CommRing R'] [Algebra R R']
    [(W.map (algebraMap R R')).IsElliptic] :
    ∃ φ : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).asOver ≅
      (modelEllipticCurve (W.map (algebraMap R R'))).asOver,
      IsMonHom φ.hom := by
  have b := isPullback_projModelBaseChange (R' := R') W
  let e' : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).asOver.left ≅
      (modelEllipticCurve (W.map (algebraMap R R'))).asOver.left := b.isoPullback.symm
  have heπ' : e'.hom ≫ (modelEllipticCurve (W.map (algebraMap R R'))).asOver.hom
      = ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).asOver.hom := by
    show b.isoPullback.inv ≫ projModelπ (W.map (algebraMap R R')) = _
    exact (Iso.inv_comp_eq _).mpr b.isoPullback_hom_snd.symm
  refine ⟨Over.isoMk e' heπ', ?_⟩
  suffices hη : (η[((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).asOver]) ≫
      (Over.isoMk e' heπ').hom =
      η[(modelEllipticCurve (W.map (algebraMap R R'))).asOver] by
    exact ⟨hη, isMonHom_of_pointedIso_records _ _ (Over.isoMk e' heπ') hη⟩
  have hz : ((modelEllipticCurve W).baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))).zero ≫ e'.hom
      = (modelEllipticCurve (W.map (algebraMap R R'))).zero := by
    have hfst : ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))).zero ≫
          pullback.fst (modelEllipticCurve W).π
            (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        = Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ (modelEllipticCurve W).zero :=
      pullback.lift_fst _ _ _
    have hsnd : ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))).zero ≫
          pullback.snd (modelEllipticCurve W).π
            (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        = 𝟙 _ :=
      pullback.lift_snd _ _ _
    have hz2 : projModelZero (W.map (algebraMap R R')) ≫ b.isoPullback.hom
        = ((modelEllipticCurve W).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))).zero := by
      refine pullback.hom_ext ?_ ?_
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_fst).trans ?_
        exact (projModelZero_baseChange (R' := R') W).trans hfst.symm
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg (CategoryStruct.comp _) b.isoPullback_hom_snd).trans ?_
        exact (projModelZero_projModelπ (W.map (algebraMap R R'))).trans hsnd.symm
    show _ ≫ b.isoPullback.inv = projModelZero (W.map (algebraMap R R'))
    exact (Iso.comp_inv_eq _).mpr hz2.symm
  ext1
  rw [Over.comp_left, show (Over.isoMk e' heπ').hom.left = e'.hom from rfl,
    ((modelEllipticCurve W).baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))).one_eq_zero,
    (modelEllipticCurve (W.map (algebraMap R R'))).one_eq_zero]
  exact (Category.assoc _ _ _).trans (congrArg _ hz)

/-- **([ASM-2], the universal pullback principle)** For the universal model record, the
diagonal value at ANY torsion point (over any base map) is `1`: the point classifies a
map to `X_N` along which the tautological value pulls back. -/
theorem weilPairingEval_self_universalModel {N : ℕ} [NeZero N] {T : Scheme.{u}}
    {g : T ⟶ Spec (CommRingCat.of WeierstrassAtlasRingU.{u})}
    (x : (modelEllipticCurve universalWeierstrassLocU.{u}).Point g)
    (hx : x.1 ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).mulByHom N =
      g ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).zero) :
    ((modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval x x hx hx :
      Γ(T, ⊤)) = 1 := by
  obtain ⟨k, hkπ, hkι⟩ :
      ∃ k : T ⟶ (modelEllipticCurve universalWeierstrassLocU.{u}).torsion N,
        k ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N = g ∧
        k ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).torsionι N = x.1 :=
    ⟨(modelEllipticCurve universalWeierstrassLocU.{u}).pointToTorsion x hx,
      (modelEllipticCurve universalWeierstrassLocU.{u}).pointToTorsion_torsionπ x hx,
      (modelEllipticCurve universalWeierstrassLocU.{u}).pointToTorsion_torsionι x hx⟩
  subst hkπ
  -- the restricted tautological point is `x`
  have hrestrkill : (EllipticCurve.Point.restrict
        (modelEllipticCurve universalWeierstrassLocU.{u}) k (tautTorsionPoint _ N)).1 ≫
      (modelEllipticCurve universalWeierstrassLocU.{u}).mulByHom N =
      (k ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).torsionπ N) ≫
        (modelEllipticCurve universalWeierstrassLocU.{u}).zero := by
    show (k ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).torsionι N) ≫ _ = _
    rw [Category.assoc, Category.assoc]
    exact congrArg (fun m => k ≫ m)
      (tautTorsionPoint_killedBy (modelEllipticCurve universalWeierstrassLocU.{u}) N)
  have hpt : EllipticCurve.Point.restrict
      (modelEllipticCurve universalWeierstrassLocU.{u}) k (tautTorsionPoint _ N) = x :=
    Subtype.ext hkι
  have hres := (modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval_restrict k
    (tautTorsionPoint _ N) (tautTorsionPoint _ N)
    (tautTorsionPoint_killedBy _ N) (tautTorsionPoint_killedBy _ N) hrestrkill hrestrkill
  rw [weilPairingEval_self_universal_eq_one N] at hres
  rw [show ((Scheme.Γ.map k.op).hom (1 : Γ((modelEllipticCurve
      universalWeierstrassLocU.{u}).torsion N, ⊤))) = 1 from map_one _] at hres
  rw [(modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval_congr
    (N := N) hpt hpt hrestrkill hrestrkill hx hx] at hres
  exact hres

/-- **([ASM-3], map form)** For a model that is a base change of the universal model
along a ring map, the diagonal pairing value at any `N`-torsion point is `1`. -/
theorem weilPairingEval_self_model_map {R : Type u} [CommRing R]
    [Algebra WeierstrassAtlasRingU.{u} R]
    [(universalWeierstrassLocU.{u}.map (algebraMap WeierstrassAtlasRingU.{u} R)).IsElliptic]
    {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of R)}
    (x : (modelEllipticCurve (universalWeierstrassLocU.{u}.map
      (algebraMap WeierstrassAtlasRingU.{u} R))).Point g)
    (hx : x.1 ≫ (modelEllipticCurve (universalWeierstrassLocU.{u}.map
        (algebraMap WeierstrassAtlasRingU.{u} R))).mulByHom N =
      g ≫ (modelEllipticCurve (universalWeierstrassLocU.{u}.map
        (algebraMap WeierstrassAtlasRingU.{u} R))).zero) :
    ((modelEllipticCurve (universalWeierstrassLocU.{u}.map
      (algebraMap WeierstrassAtlasRingU.{u} R))).weilPairingEval x x hx hx :
      Γ(T, ⊤)) = 1 := by
  classical
  set σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of WeierstrassAtlasRingU.{u}) :=
    Spec.map (CommRingCat.ofHom (algebraMap WeierstrassAtlasRingU.{u} R)) with hσ
  obtain ⟨φ, hφ⟩ := modelBaseChangeIsoAsOver_ring universalWeierstrassLocU.{u} R
  haveI := hφ
  -- transport `x` back to the base-changed universal record
  set y : ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).Point g :=
    Point.mapIso φ.symm x with hy
  have hykill : y.1 ≫ ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).mulByHom N
      = g ≫ ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).zero := by
    haveI : IsMonHom φ.symm.hom := isMonHom_symm φ
    exact Point.mapIso_killedBy φ.symm hx
  -- and further to a point of the universal record over `g ≫ σ`
  set z : (modelEllipticCurve universalWeierstrassLocU.{u}).Point (g ≫ σ) :=
    EllipticCurve.Point.baseChangeEquiv (modelEllipticCurve universalWeierstrassLocU.{u})
      σ g y with hz
  have hzkill : z.1 ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).mulByHom N =
      (g ≫ σ) ≫ (modelEllipticCurve universalWeierstrassLocU.{u}).zero := by
    rw [← (modelEllipticCurve universalWeierstrassLocU.{u}).smul_eq_zero_iff_comp_mulByHom
      (g ≫ σ) N z, hz]
    rw [← map_zsmul (EllipticCurve.Point.baseChangeEquiv
      (modelEllipticCurve universalWeierstrassLocU.{u}) σ g)]
    rw [((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange
      σ).smul_eq_zero_iff_comp_mulByHom g N y |>.mpr hykill]
    exact map_zero _
  -- the universal statement at `z`
  have huniv := weilPairingEval_self_universalModel z hzkill
  -- the base-changed record's value equals the universal record's value at `z`
  have hbc : (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).weilPairingEval
      y y hykill hykill : Γ(T, ⊤)) =
      ((modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval z z hzkill hzkill :
        Γ(T, ⊤)) := by
    haveI hsepU : IsSeparated (modelEllipticCurve universalWeierstrassLocU.{u}).π :=
      inferInstance
    haveI hsepBC : IsSeparated
        (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).π) :=
      MorphismProperty.pullback_snd (P := @IsSeparated) _ _ hsepU
    have hsmBC : SmoothOfRelativeDimension 1
        (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).π) :=
      haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
      MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _
        (modelEllipticCurve universalWeierstrassLocU.{u}).smooth
    rw [((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).weilPairingEval_eq_weilPairingKM
      y y hykill hykill,
      (modelEllipticCurve universalWeierstrassLocU.{u}).weilPairingEval_eq_weilPairingKM
      z z hzkill hzkill]
    refine congrArg Units.val ?_
    have hasec := asSection_comp_bcSwapGenIso
      (modelEllipticCurve universalWeierstrassLocU.{u}) σ g y
    have hzdef : z = EllipticCurve.Point.baseChangeEquiv
        (modelEllipticCurve universalWeierstrassLocU.{u}) σ g y := rfl
    -- the swapped point of `asSection z` is `asSection y`
    have hcancel : (EllipticCurve.Point.asSection
        ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) g y).1 =
        (EllipticCurve.Point.asSection
          (modelEllipticCurve universalWeierstrassLocU.{u}) (g ≫ σ) z).1 ≫
        (bcSwapGenIso (modelEllipticCurve universalWeierstrassLocU.{u}) σ g).inv := by
      rw [hzdef, ← hasec]
      exact ((Category.assoc _ _ _).trans
        ((congrArg (fun m => (EllipticCurve.Point.asSection
          ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) g y).1 ≫ m)
          (bcSwapGenIso (modelEllipticCurve universalWeierstrassLocU.{u}) σ g).hom_inv_id).trans
        (Category.comp_id _))).symm
    have hswcond : ((EllipticCurve.Point.asSection
        (modelEllipticCurve universalWeierstrassLocU.{u}) (g ≫ σ) z).1 ≫
        (bcSwapGenIso (modelEllipticCurve universalWeierstrassLocU.{u}) σ g).inv) ≫
        pullback.snd (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).π) g =
        𝟙 T := by
      rw [← hcancel]
      exact (EllipticCurve.Point.asSection
        ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) g y).2
    have hswpt : EllipticCurve.Point.asSection
        ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) g y =
        (⟨(EllipticCurve.Point.asSection
            (modelEllipticCurve universalWeierstrassLocU.{u}) (g ≫ σ) z).1 ≫
          (bcSwapGenIso (modelEllipticCurve universalWeierstrassLocU.{u}) σ g).inv,
          hswcond⟩ :
          (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).baseChange g).Point
            (𝟙 T)) := by
      exact Subtype.ext hcancel
    have hswt : (⟨(EllipticCurve.Point.asSection
          (modelEllipticCurve universalWeierstrassLocU.{u}) (g ≫ σ) z).1 ≫
        (bcSwapGenIso (modelEllipticCurve universalWeierstrassLocU.{u}) σ g).inv,
        hswcond⟩ :
        (((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ).baseChange g).Point
          (𝟙 T)) ∈
        torsionPoints ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) g N :=
      hswpt ▸ asSection_mem_torsionPoints
        ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) y hykill
    rw [weilPairingKM_congr
      ((modelEllipticCurve universalWeierstrassLocU.{u}).baseChange σ) hsmBC g N
      hswpt hswpt (asSection_mem_torsionPoints _ y hykill)
      (asSection_mem_torsionPoints _ y hykill)]
    exact weilPairingKM_bcSwapGen (modelEllipticCurve universalWeierstrassLocU.{u}) σ g
      (modelEllipticCurve universalWeierstrassLocU.{u}).smooth hsmBC N
      (EllipticCurve.Point.asSection _ (g ≫ σ) z)
      (asSection_mem_torsionPoints _ z hzkill)
      (EllipticCurve.Point.asSection _ (g ≫ σ) z)
      (asSection_mem_torsionPoints _ z hzkill) hswcond hswt hswcond hswt
  -- transport back along `φ`
  have hmap := weilPairingEval_mapIso φ y y hykill hykill
    (Point.mapIso_killedBy φ hykill) (Point.mapIso_killedBy φ hykill)
  -- `Point.mapIso φ y = x` since `y` was defined as the `φ.symm`-transport
  have hxy : Point.mapIso φ y = x := by
    refine Subtype.ext ?_
    show (y.1 ≫ φ.hom.left) = x.1
    show ((x.1 ≫ φ.symm.hom.left) ≫ φ.hom.left) = x.1
    rw [Category.assoc]
    have : φ.symm.hom.left ≫ φ.hom.left = 𝟙 _ := by
      show (φ.inv ≫ φ.hom).left = _
      rw [φ.inv_hom_id]
      rfl
    rw [this]
    exact Category.comp_id _
  rw [weilPairingEval_congr (E := modelEllipticCurve (universalWeierstrassLocU.{u}.map
    (algebraMap WeierstrassAtlasRingU.{u} R))) hxy hxy
    (Point.mapIso_killedBy φ hykill) (Point.mapIso_killedBy φ hykill) hx hx] at hmap
  exact hmap.trans (hbc.trans huniv)

/-- **([ASM-4a], locality)** The diagonal value is `1` as soon as it is `1` after
restriction to an open cover of the base. -/
theorem weilPairingEval_self_of_locally {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ}
    [NeZero N] {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hloc : ∀ p : T, ∃ V : T.Opens, p ∈ V ∧
      ∀ (hxr : (EllipticCurve.Point.restrict E V.ι x).1 ≫ E.mulByHom N =
        (V.ι ≫ g) ≫ E.zero),
        (E.weilPairingEval (EllipticCurve.Point.restrict E V.ι x)
          (EllipticCurve.Point.restrict E V.ι x) hxr hxr : Γ((V : Scheme.{u}), ⊤)) = 1) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := T.presheaf) T.sheaf.cond (U := Opposite.op ⊤) ?_
  intro p _
  obtain ⟨V, hpV, hV⟩ := hloc p
  refine ⟨V, le_top, hpV, ?_⟩
  have hxr : (EllipticCurve.Point.restrict E V.ι x).1 ≫ E.mulByHom N =
      (V.ι ≫ g) ≫ E.zero := by
    show (V.ι ≫ x.1) ≫ E.mulByHom N = (V.ι ≫ g) ≫ E.zero
    rw [Category.assoc, hx, ← Category.assoc]
  have hres := E.weilPairingEval_restrict V.ι x x hx hx hxr hxr
  rw [hV hxr] at hres
  -- translate the `Γ.map`-restriction into the presheaf restriction
  have hbridge : ∀ s : Γ(T, ⊤), V.topIso.hom.hom ((Scheme.Γ.map V.ι.op).hom s) =
      (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s := by
    intro s
    rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
    refine Eq.trans (show V.topIso.hom.hom
        ((T.presheaf.map (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op).hom s) =
        ((T.presheaf.map (homOfLE (x := V.ι ''ᵁ ⊤) le_top).op) ≫ V.topIso.hom).hom s
      from rfl) ?_
    refine congrArg (fun m : Γ(T, ⊤) ⟶ Γ(T, V) => m.hom s) ?_
    rw [Scheme.Opens.topIso_hom]
    exact (T.presheaf.map_comp _ _).symm.trans
      (congrArg T.presheaf.map (Subsingleton.elim _ _))
  refine ((hbridge (E.weilPairingEval x x hx hx : Γ(T, ⊤))).symm.trans ?_).trans
    (hbridge 1)
  refine congrArg V.topIso.hom.hom ?_
  exact hres.symm.trans (map_one _).symm

/-- **([ASM-4b-π])** The structure-map compatibility of the `localModel` record iso
(own elaboration budget). -/
private theorem localModel_recordIso_pi {S : Scheme.{u}} (E : EllipticCurve S)
    (U : S.affineOpens) (W : WeierstrassCurve Γ(S, U.1)) [W.IsElliptic]
    (e : pullback E.π U.1.ι ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π U.1.ι ≫ U.2.isoSpec.hom) :
    ((bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫
        pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫ e.hom) ≫ projModelπ W =
      pullback.snd E.π (U.2.isoSpec.inv ≫ U.1.ι) := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m => (bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫ m)
    ((Category.assoc _ _ _).trans
      (congrArg (fun m => pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫ m)
        heπ))).trans ?_
  have hcond : pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫
      pullback.snd E.π U.1.ι =
      pullback.snd ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫ U.2.isoSpec.inv :=
    pullback.condition
  refine (congrArg (fun m => (bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫ m)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ U.2.isoSpec.hom) hcond).trans
      ((Category.assoc _ _ _).trans
      ((congrArg (fun m => pullback.snd ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫ m)
        U.2.isoSpec.inv_hom_id).trans (Category.comp_id _)))))).trans ?_
  exact bcSwapGenIso_inv_snd E U.1.ι U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
/-- **([ASM-4b-0])** The zero-section compatibility: the base-changed zero section is
carried by the collapse to the `localModel`'s section (own elaboration budget). -/
private theorem localModel_recordIso_zero {S : Scheme.{u}} (E : EllipticCurve S)
    (U : S.affineOpens)
    (hzc : (U.1.ι ≫ E.zero) ≫ E.π = 𝟙 (U.1 : Scheme.{u}) ≫ U.1.ι) :
    (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫
        ((bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫
          pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv) =
      U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ E.zero) (𝟙 _) hzc := by
  refine pullback.hom_ext ?_ ?_
  · -- the `E`-leg: both sides are `isoSpec.inv ≫ U.ι ≫ E.zero`
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫ m)
      (bcSwapGenIso_inv_fst_fst E U.1.ι U.2.isoSpec.inv)).trans ?_
    refine (pullback.lift_fst _ _ _).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun m => U.2.isoSpec.inv ≫ m) (pullback.lift_fst _ _ _)).trans ?_
    exact (Category.assoc _ _ _).symm
  · -- the base leg: both sides are `isoSpec.inv`
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun m => (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫ m)
      ((Category.assoc _ _ _).trans
        (congrArg (fun m => (bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫ m)
          pullback.condition))).trans ?_
    refine (congrArg (fun m => (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫ m)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m => m ≫ U.2.isoSpec.inv)
          (bcSwapGenIso_inv_snd E U.1.ι U.2.isoSpec.inv)))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ U.2.isoSpec.inv) (pullback.lift_snd _ _ _)).trans ?_
    refine (Category.id_comp _).trans ?_
    refine Eq.symm ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun m => U.2.isoSpec.inv ≫ m) (pullback.lift_snd _ _ _)).trans ?_
    exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- **([ASM-4b])** The `localModel` data packaged as a pointed record iso over
`Spec Γ(S, U)`. -/
theorem exists_localModel_recordIso {S : Scheme.{u}} (E : EllipticCurve S)
    (U : S.affineOpens) (W : WeierstrassCurve Γ(S, U.1)) [W.IsElliptic]
    (e : pullback E.π U.1.ι ≅ projModel W)
    (heπ : e.hom ≫ projModelπ W = pullback.snd E.π U.1.ι ≫ U.2.isoSpec.hom)
    (hzc : (U.1.ι ≫ E.zero) ≫ E.π = 𝟙 (U.1 : Scheme.{u}) ≫ U.1.ι)
    (hez : (U.2.isoSpec.inv ≫ pullback.lift (U.1.ι ≫ E.zero) (𝟙 _) hzc) ≫ e.hom =
      projModelZero W) :
    ∃ φ : (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).asOver ≅
      (modelEllipticCurve W).asOver, IsMonHom φ.hom := by
  set eL : (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).asOver.left ≅
      (modelEllipticCurve W).asOver.left :=
    (bcSwapGenIso E U.1.ι U.2.isoSpec.inv).symm ≪≫
      asIso (pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv) ≪≫ e with heL
  have heπ' : eL.hom ≫ (modelEllipticCurve W).asOver.hom =
      (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).asOver.hom :=
    localModel_recordIso_pi E U W e heπ
  refine ⟨Over.isoMk eL heπ', ?_⟩
  have hz : (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫ eL.hom =
      (modelEllipticCurve W).zero := by
    show (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫
      ((bcSwapGenIso E U.1.ι U.2.isoSpec.inv).inv ≫
        pullback.fst ((E.baseChange U.1.ι).π) U.2.isoSpec.inv ≫ e.hom) = projModelZero W
    refine Eq.trans ?_ hez
    refine (congrArg (fun m => (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).zero ≫ m)
      (Category.assoc _ _ _).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun m => m ≫ e.hom) (localModel_recordIso_zero E U hzc)
  suffices hη : (η[(E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).asOver]) ≫
      (Over.isoMk eL heπ').hom = η[(modelEllipticCurve W).asOver] by
    exact ⟨hη, isMonHom_of_pointedIso_records _ _ (Over.isoMk eL heπ') hη⟩
  ext1
  rw [Over.comp_left, show (Over.isoMk eL heπ').hom.left = eL.hom from rfl,
    (E.baseChange (U.2.isoSpec.inv ≫ U.1.ι)).one_eq_zero,
    (modelEllipticCurve W).one_eq_zero]
  exact (Category.assoc _ _ _).trans (congrArg _ hz)

/-- **([ASM-4c])** The model case restated for an arbitrary elliptic Weierstrass curve
over a ring (via the classifying map). -/
theorem weilPairingEval_self_model {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] {N : ℕ} [NeZero N] {T : Scheme.{u}} {g : T ⟶ Spec (CommRingCat.of R)}
    (x : (modelEllipticCurve W).Point g)
    (hx : x.1 ≫ (modelEllipticCurve W).mulByHom N = g ≫ (modelEllipticCurve W).zero) :
    ((modelEllipticCurve W).weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  obtain ⟨c, hc⟩ : ∃ c : WeierstrassAtlasRingU.{u} →+* R,
      universalWeierstrassLocU.{u}.map c = W :=
    ⟨classifyRingHomU W, universalWeierstrassLocU_map_classifyRingHomU W⟩
  subst hc
  letI : Algebra WeierstrassAtlasRingU.{u} R := c.toAlgebra
  exact weilPairingEval_self_model_map x hx

/-- **([BC-VALUE])** The value on the base-changed record equals the value on the
original record at the corresponding point. -/
theorem weilPairingEval_baseChange_eq {S : Scheme.{u}} (E : EllipticCurve S)
    {B T : Scheme.{u}} (σ : T ⟶ S) (g : B ⟶ T) {N : ℕ} [NeZero N]
    (y : (E.baseChange σ).Point g)
    (hykill : y.1 ≫ (E.baseChange σ).mulByHom N = g ≫ (E.baseChange σ).zero)
    (hzkill : (EllipticCurve.Point.baseChangeEquiv E σ g y).1 ≫ E.mulByHom N =
      (g ≫ σ) ≫ E.zero) :
    ((E.baseChange σ).weilPairingEval y y hykill hykill : Γ(B, ⊤)) =
      (E.weilPairingEval (EllipticCurve.Point.baseChangeEquiv E σ g y)
        (EllipticCurve.Point.baseChangeEquiv E σ g y) hzkill hzkill : Γ(B, ⊤)) := by
  set z := EllipticCurve.Point.baseChangeEquiv E σ g y with hzdef0
  haveI hsepU : IsSeparated E.π :=
    inferInstance
  haveI hsepBC : IsSeparated
      ((E.baseChange σ).π) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) _ _ hsepU
  have hsmBC : SmoothOfRelativeDimension 1
      ((E.baseChange σ).π) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _
      E.smooth
  rw [(E.baseChange σ).weilPairingEval_eq_weilPairingKM
    y y hykill hykill,
    E.weilPairingEval_eq_weilPairingKM
    z z hzkill hzkill]
  refine congrArg Units.val ?_
  have hasec := asSection_comp_bcSwapGenIso
    E σ g y
  have hzdef : z = EllipticCurve.Point.baseChangeEquiv
      E σ g y := rfl
  -- the swapped point of `asSection z` is `asSection y`
  have hcancel : (EllipticCurve.Point.asSection
      (E.baseChange σ) g y).1 =
      (EllipticCurve.Point.asSection
        E (g ≫ σ) z).1 ≫
      (bcSwapGenIso E σ g).inv := by
    rw [hzdef, ← hasec]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun m => (EllipticCurve.Point.asSection
        (E.baseChange σ) g y).1 ≫ m)
        (bcSwapGenIso E σ g).hom_inv_id).trans
      (Category.comp_id _))).symm
  have hswcond : ((EllipticCurve.Point.asSection
      E (g ≫ σ) z).1 ≫
      (bcSwapGenIso E σ g).inv) ≫
      pullback.snd ((E.baseChange σ).π) g =
      𝟙 B := by
    rw [← hcancel]
    exact (EllipticCurve.Point.asSection
      (E.baseChange σ) g y).2
  have hswpt : EllipticCurve.Point.asSection
      (E.baseChange σ) g y =
      (⟨(EllipticCurve.Point.asSection
          E (g ≫ σ) z).1 ≫
        (bcSwapGenIso E σ g).inv,
        hswcond⟩ :
        ((E.baseChange σ).baseChange g).Point
          (𝟙 B)) := by
    exact Subtype.ext hcancel
  have hswt : (⟨(EllipticCurve.Point.asSection
        E (g ≫ σ) z).1 ≫
      (bcSwapGenIso E σ g).inv,
      hswcond⟩ :
      ((E.baseChange σ).baseChange g).Point
        (𝟙 B)) ∈
      torsionPoints (E.baseChange σ) g N :=
    hswpt ▸ asSection_mem_torsionPoints
      (E.baseChange σ) y hykill
  rw [weilPairingKM_congr
    (E.baseChange σ) hsmBC g N
    hswpt hswpt (asSection_mem_torsionPoints _ y hykill)
    (asSection_mem_torsionPoints _ y hykill)]
  exact weilPairingKM_bcSwapGen E σ g
    E.smooth hsmBC N
    (EllipticCurve.Point.asSection _ (g ≫ σ) z)
    (asSection_mem_torsionPoints _ z hzkill)
    (EllipticCurve.Point.asSection _ (g ≫ σ) z)
    (asSection_mem_torsionPoints _ z hzkill) hswcond hswt hswcond hswt

/-- **([ASM-4d])** The diagonal value is `1` whenever the record is a base change of a
model along a map factoring through an affine open on which `localModel` applies. -/
theorem weilPairingEval_self_of_recordIso {S : Scheme.{u}} (E : EllipticCurve S)
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    {N : ℕ} [NeZero N] {B : Scheme.{u}} (σ : Spec (CommRingCat.of R) ⟶ S)
    (φ : (E.baseChange σ).asOver ≅ (modelEllipticCurve W).asOver) [IsMonHom φ.hom]
    {g : B ⟶ Spec (CommRingCat.of R)}
    (x : E.Point (g ≫ σ)) (hx : x.1 ≫ E.mulByHom N = (g ≫ σ) ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(B, ⊤)) = 1 := by
  classical
  haveI hsepE : IsSeparated E.π := inferInstance
  haveI hsepBC : IsSeparated ((E.baseChange σ).π) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) E.π σ hsepE
  have hsmBC : SmoothOfRelativeDimension 1 ((E.baseChange σ).π) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ E.smooth
  -- the point, viewed on the base-changed record over `B`
  set y : (E.baseChange σ).Point g :=
    ((EllipticCurve.Point.baseChangeEquiv E σ g).symm x) with hy
  have hyval : y.1 ≫ pullback.fst E.π σ = x.1 := by
    rw [hy]
    exact pullback.lift_fst _ _ _
  have hykill : y.1 ≫ (E.baseChange σ).mulByHom N = g ≫ (E.baseChange σ).zero := by
    rw [← (E.baseChange σ).smul_eq_zero_iff_comp_mulByHom g N y, hy,
      ← map_zsmul (EllipticCurve.Point.baseChangeEquiv E σ g).symm,
      (E.smul_eq_zero_iff_comp_mulByHom (g ≫ σ) N x).mpr hx]
    exact map_zero _
  -- the model value at the transported point
  have hmodel := weilPairingEval_self_model W (N := N)
    (Point.mapIso φ y) (Point.mapIso_killedBy φ hykill)
  have hmap := weilPairingEval_mapIso φ y y hykill hykill
    (Point.mapIso_killedBy φ hykill) (Point.mapIso_killedBy φ hykill)
  -- the base-changed record's value equals `E`'s value at `x`
  have hxeq : EllipticCurve.Point.baseChangeEquiv E σ g y = x := by
    rw [hy]
    exact (EllipticCurve.Point.baseChangeEquiv E σ g).apply_symm_apply x
  have hbc : ((E.baseChange σ).weilPairingEval y y hykill hykill : Γ(B, ⊤)) =
      (E.weilPairingEval x x hx hx : Γ(B, ⊤)) := by
    have h0 := weilPairingEval_baseChange_eq E σ g y hykill (hxeq ▸ hx)
    rw [h0]
    exact E.weilPairingEval_congr hxeq hxeq _ _ hx hx
  exact hbc.symm.trans (hmap.symm.trans hmodel)

/-- The pairing value is invariant under transporting the point along an equality of
base maps. -/
theorem weilPairingEval_self_pointCongr {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ}
    [NeZero N] {T : Scheme.{u}} {σ σ' : T ⟶ S} (h : σ = σ') (x : E.Point σ)
    (hx : x.1 ≫ E.mulByHom N = σ ≫ E.zero)
    (hx' : (pointCongr E h x).1 ≫ E.mulByHom N = σ' ≫ E.zero) :
    (E.weilPairingEval (pointCongr E h x) (pointCongr E h x) hx' hx' : Γ(T, ⊤)) =
      (E.weilPairingEval x x hx hx : Γ(T, ⊤)) := by
  subst h
  rfl

/-- **(LEAF A — `e_N(x, x) = 1` over an arbitrary base)** The Weil pairing is alternating:
the diagonal value of any `N`-torsion point is `1`. -/
theorem weilPairingEval_self_general {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ}
    [NeZero N] {T : Scheme.{u}} {g : T ⟶ S} (x : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x x hx hx : Γ(T, ⊤)) = 1 := by
  classical
  refine weilPairingEval_self_of_locally E x hx (fun p => ?_)
  -- the local Weierstrass model at the image point
  obtain ⟨U, hsU, W, hWell, e, heπ, hez⟩ := E.localModel (g.base p)
  haveI := hWell
  refine ⟨g ⁻¹ᵁ U.1, hsU, fun hxr => ?_⟩
  -- the restricted base map factors through `Spec Γ(S, U)`
  have hfac : (g ⁻¹ᵁ U.1).ι ≫ g =
      ((g ∣_ U.1) ≫ U.2.isoSpec.hom) ≫ (U.2.isoSpec.inv ≫ U.1.ι) := by
    rw [Category.assoc, ← Category.assoc U.2.isoSpec.hom, Iso.hom_inv_id,
      Category.id_comp]
    exact (morphismRestrict_ι g U.1).symm
  obtain ⟨φ, hφ⟩ := exists_localModel_recordIso E U W e heπ
    (by rw [Category.assoc, E.zero_π, Category.comp_id, Category.id_comp]) hez
  haveI := hφ
  -- transport the restricted point to the factored base map
  have hxr' : (EllipticCurve.Point.restrict E (g ⁻¹ᵁ U.1).ι x).1 ≫ E.mulByHom N =
      (((g ∣_ U.1) ≫ U.2.isoSpec.hom) ≫ (U.2.isoSpec.inv ≫ U.1.ι)) ≫ E.zero := by
    rw [← hfac]; exact hxr
  have hxr'' : (pointCongr E hfac (EllipticCurve.Point.restrict E (g ⁻¹ᵁ U.1).ι x)).1 ≫
      E.mulByHom N =
      (((g ∣_ U.1) ≫ U.2.isoSpec.hom) ≫ (U.2.isoSpec.inv ≫ U.1.ι)) ≫ E.zero := by
    rw [pointCongr_apply_coe]
    exact hxr'
  refine (weilPairingEval_self_pointCongr E hfac
    (EllipticCurve.Point.restrict E (g ⁻¹ᵁ U.1).ι x) hxr hxr'').symm.trans ?_
  exact weilPairingEval_self_of_recordIso E W (U.2.isoSpec.inv ≫ U.1.ι) φ _ hxr''

/-! ## Consequences (axiom-clean versions of the register's derived laws)

`WeilPairing/Basic.lean` derives antisymmetry, the first-slot power law and the
symplectic formula from its (still sorried) register entry `weilPairingEval_self`. The
versions below are the same statements re-derived from `weilPairingEval_self_general`,
hence axiom-clean; downstream consumers should use these. -/

/-- **Antisymmetry** `e_N(x,y) · e_N(y,x) = 1`, axiom-clean. -/
theorem weilPairingEval_antisymm_general {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ}
    [NeZero N] {T : Scheme.{u}} {g : T ⟶ S} (x y : E.Point g)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval x y hx hy : Γ(T, ⊤)) * E.weilPairingEval y x hy hx = 1 := by
  have hxy := E.point_add_killedBy hx hy
  have h := weilPairingEval_self_general E (x + y) hxy
  rw [E.weilPairingEval_add_left x y (x + y) hx hy hxy hxy,
    E.weilPairingEval_add_right x x y hx hx hy hxy,
    E.weilPairingEval_add_right y x y hy hx hy hxy,
    weilPairingEval_self_general E x hx, weilPairingEval_self_general E y hy] at h
  rw [_root_.one_mul, _root_.mul_one] at h
  exact h

/-- **The power law in the first slot**, axiom-clean. -/
theorem weilPairingEval_zsmul_left_general {S : Scheme.{u}} (E : EllipticCurve S) {N : ℕ}
    [NeZero N] {T : Scheme.{u}} {g : T ⟶ S} (x y : E.Point g) (a : ℤ)
    (hx : x.1 ≫ E.mulByHom N = g ≫ E.zero) (hy : y.1 ≫ E.mulByHom N = g ≫ E.zero)
    (hax : (a • x).1 ≫ E.mulByHom N = g ≫ E.zero) :
    (E.weilPairingEval (a • x) y hax hy : Γ(T, ⊤)) =
      (E.weilPairingEval x y hx hy : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat) := by
  have hef : (E.weilPairingEval x y hx hy : Γ(T, ⊤)) *
      E.weilPairingEval y x hy hx = 1 :=
    weilPairingEval_antisymm_general E x y hx hy
  have h1 : (E.weilPairingEval (a • x) y hax hy : Γ(T, ⊤)) *
      E.weilPairingEval y (a • x) hy hax = 1 :=
    weilPairingEval_antisymm_general E (a • x) y hax hy
  have h2 : (E.weilPairingEval y (a • x) hy hax : Γ(T, ⊤)) =
      (E.weilPairingEval y x hy hx : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat) :=
    E.weilPairingEval_zsmul_right y x a hy hx hax
  have hunit : IsUnit ((E.weilPairingEval y x hy hx : Γ(T, ⊤)) ^ ((a % (N : ℤ)).toNat)) :=
    (isUnit_of_pow_eq_one (E.weilPairingEval y x hy hx).2).pow _
  refine (hunit.mul_left_inj).mp ?_
  rw [pow_mul_pow_eq_one hef, ← h2]
  exact h1

end EllipticCurve

end ModularCurves
