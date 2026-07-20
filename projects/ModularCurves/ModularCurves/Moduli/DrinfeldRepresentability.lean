/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.GammaH
import ModularCurves.LevelStructure.Incidence
import ModularCurves.LevelStructure.ExactOrderInvertible

/-!
# Relative representability of the Drinfeld `Γ₁(N)` problem (KM 3.6.0, Γ₁ half)

The Drinfeld `Γ₁(N)` moduli problem `gammaOneDrinfeldProblem` is **affine over `Ell`**
(hence relatively representable), assembled — per KM 1.6.2 (`ℤ/N`-Str, no rank hypothesis,
so **no `c4`**) — from two pieces that already exist sorry-free in the library:

* **c2 (the Hom-scheme ambient, KM 1.6.1)** — `EllipticCurve.torsionPointsEquiv`: `T`-points
  of `E[N] = E.torsion N` over `t` are the `N`-torsion of `E.Point t`
  (`Hom_{S-gp}(ℤ/N, E) = E[N]`).
* **c1 (the A-Str closed subscheme, KM 1.6.2 via 1.3.7)** — `ModularCurves.exists_exactOrderLocus`:
  a closed subscheme `Z ⊆ E[N]` through which an `N`-torsion `T`-point factors **iff** it has
  Drinfeld exact order `N`.

The representing `S`-scheme is `Z.subscheme` (finite over `S`, as a closed subscheme of the
finite `E[N]`), and the functor-of-points bijection is `torsionPointsEquiv` cut down to `Z`.

`Representable` itself then follows from `ModuliProblem.representable_iff` (KM SCHOLIE 4.7.0)
together with rigidity — the same shared engine endgame the naive problems consume.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {R : CommRingCat.{u}}

/-- The exact-order locus is a closed subscheme of the finite `E[N]`, so its structure
morphism to `S` is affine (`c1`/`c2` affineness ingredient for KM SCHOLIE 4.7.0). -/
theorem exactOrderLocus_isAffineHom {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] (Z : (E.torsion N).IdealSheafData) :
    IsAffineHom (Z.subschemeι ≫ E.torsionπ N) := by
  haveI : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  exact inferInstance

set_option maxHeartbeats 1000000 in
/-- The kernel `T`-point recovered from an `N`-torsion point via `torsionPointsEquiv` is the
original map into `E[N]` (both sides are the unique lift over the two `E[N]`-projections). This
is the uniqueness fact that makes the exact-order locus represent the Γ₁ functor of points. -/
theorem pointToTorsion_torsionPointsEquiv {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] {T : Scheme.{u}} (g : T ⟶ S)
    (j : { j : T ⟶ E.torsion N // j ≫ E.torsionπ N = g }) :
    E.pointToTorsion (↑(E.torsionPointsEquiv N g j))
        ((E.smul_eq_zero_iff_comp_mulByHom g N _).mp
          ((Submodule.mem_torsionBy_iff _ _).mp (E.torsionPointsEquiv N g j).2)) = j.1 :=
  congrArg Subtype.val ((E.torsionPointsEquiv N g).left_inv j)

set_option maxHeartbeats 1000000 in
/-- Mirror of `pointToTorsion_torsionPointsEquiv` (the `right_inv` direction): the `N`-torsion
point recovered from `pointToTorsion Q` via `torsionPointsEquiv` is `Q` itself. This is the
uniqueness fact used to close the `right_inv` of the Γ₁ functor-of-points equivalence. -/
theorem coe_torsionPointsEquiv_pointToTorsion {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    [NeZero N] {T : Scheme.{u}} (g : T ⟶ S) (Q : E.Point g)
    (hQ : (Q : T ⟶ E.E) ≫ E.mulByHom (N : ℤ) = g ≫ E.zero)
    (hπ : E.pointToTorsion Q hQ ≫ E.torsionπ N = g) :
    ((E.torsionPointsEquiv N g ⟨E.pointToTorsion Q hQ, hπ⟩ :
        Submodule.torsionBy ℤ (E.Point g) (N : ℤ)) : E.Point g) = Q :=
  congrArg Subtype.val ((E.torsionPointsEquiv N g).right_inv
    ⟨Q, (Submodule.mem_torsionBy_iff _ _).mpr ((E.smul_eq_zero_iff_comp_mulByHom g N Q).mpr hQ)⟩)

/-- `asSection` is injective: a point is recovered from its section by `≫ pullback.fst`. -/
theorem asSection_injective {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S) :
    Function.Injective (EllipticCurve.Point.asSection E g) := fun a b hab =>
  Subtype.ext (by
    have h := congrArg
      (fun s : (E.baseChange g).Section => s.1 ≫ Limits.pullback.fst E.π g) hab
    simpa only [EllipticCurve.Point.asSection_val_fst] using h)

/-- `asSection` sends the zero point to the zero section. -/
theorem asSection_zero {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}} (g : T ⟶ S) :
    EllipticCurve.Point.asSection E g 0 = 0 := by
  have h := EllipticCurve.Point.asSection_zsmul E g 0 0
  simpa using h

/-- The point of `E/S` over `g` underlying a section of the base change `E ×_S T` — the
inverse of `asSection`. Built term-mode: `(E.baseChange g).E` is defeq `pullback E.π g` only at
default transparency, so `rw`/`simp` on the composite fail (cf. `Point.asSection_zsmul`). -/
noncomputable def sectionToPoint {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (Q : (E.baseChange g).Section) : E.Point g :=
  ⟨Q.1 ≫ Limits.pullback.fst E.π g,
    (Category.assoc _ _ _).trans <|
      (congrArg (Q.1 ≫ ·) Limits.pullback.condition).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ g) Q.2).trans (Category.id_comp g)⟩

/-- `asSection` is a left inverse of `sectionToPoint`: the section of a section's underlying
point is the section itself. -/
theorem asSection_sectionToPoint {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (Q : (E.baseChange g).Section) :
    EllipticCurve.Point.asSection E g (sectionToPoint E g Q) = Q :=
  Subtype.ext (Limits.pullback.hom_ext
    (EllipticCurve.Point.asSection_val_fst E g (sectionToPoint E g Q))
    ((EllipticCurve.Point.asSection_val_snd E g (sectionToPoint E g Q)).trans Q.2.symm))

/-- `sectionToPoint` is a left inverse of `asSection`. -/
theorem sectionToPoint_asSection {S : Scheme.{u}} (E : EllipticCurve S) {T : Scheme.{u}}
    (g : T ⟶ S) (x : E.Point g) :
    sectionToPoint E g (EllipticCurve.Point.asSection E g x) = x :=
  Subtype.ext (EllipticCurve.Point.asSection_val_fst E g x)

/-- The underlying map of the point recovered from `j` via `torsionPointsEquiv` is
`j ≫ torsionι` (definitional; the naturality bookkeeping fact for the Γ₁ equivalence). -/
theorem torsionPointsEquiv_coe_fst {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    {T : Scheme.{u}} (g : T ⟶ S)
    (j : { j : T ⟶ E.torsion N // j ≫ E.torsionπ N = g }) :
    (((E.torsionPointsEquiv N g j : Submodule.torsionBy ℤ (E.Point g) (N : ℤ)) :
        E.Point g) : T ⟶ E.E) = j.1 ≫ E.torsionι N := rfl

open EllipticCurve in
/-- `EllHom.pullSection` along the base-change comparison morphism `pullbackAlongMap g k`
restricts the represented point: `pullSection (pullbackAlongMap g k) (asSection g P)
= asSection (k ≫ g) (P.restrict k)`. (Re-statement of the identically-named `private`
lemma of `Moduli/GammaHRepresentability.lean` / `ModularCurve/YFullRoute.lean`, needed
here for the Γ₁ functor-of-points naturality square.) -/
theorem pullSection_asSection {R : CommRingCat.{u}} (X : EllObj R)
    {T T' : Scheme.{u}} (g : T ⟶ X.base) (k : T' ⟶ T) (P : X.curve.Point g) :
    EllHom.pullSection R (X.pullbackAlongMap g k) (Point.asSection X.curve g P) =
      Point.asSection X.curve (k ≫ g) (Point.restrict X.curve k P) := by
  have htop : (X.pullbackAlongMap g k).top ≫ pullback.fst X.curve.π g =
      pullback.fst X.curve.π (k ≫ g) := by
    show Limits.pullback.map X.curve.π (k ≫ g) X.curve.π g (𝟙 _) k (𝟙 _)
        (by simp) (by simp) ≫ Limits.pullback.fst X.curve.π g =
      Limits.pullback.fst X.curve.π (k ≫ g)
    rw [Limits.pullback.lift_fst, Category.comp_id]
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · refine ((congrArg ((EllHom.pullSection R (X.pullbackAlongMap g k)
        (Point.asSection X.curve g P)).1 ≫ ·) htop.symm).trans ?_).trans
      (Point.asSection_val_fst X.curve (k ≫ g) (Point.restrict X.curve k P)).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ pullback.fst X.curve.π g)
      ((X.pullbackAlongMap g k).isPullback.lift_fst _ _ _)).trans ?_
    exact (Category.assoc _ _ _).trans
      (congrArg (k ≫ ·) (Point.asSection_val_fst X.curve g P))
  · exact (EllHom.pullSection R (X.pullbackAlongMap g k)
      (Point.asSection X.curve g P)).2.trans
      (Point.asSection_val_snd X.curve (k ≫ g) (Point.restrict X.curve k P)).symm

set_option maxHeartbeats 1000000 in
/-- **(KM 1.6.2, `ℤ/N`-Str — no rank hypothesis, hence no `c4`)** The Drinfeld `Γ₁(N)`
moduli problem is affine over `Ell` for `N` **invertible**: for each `E/S` the functor of
Drinfeld exact-order-`N` points is represented by the exact-order locus `Z ⊆ E[N]`,
finite (hence affine) over `S`. Assembled from `torsionPointsEquiv` (c2, KM 1.6.1) +
`exists_exactOrderLocus` (c1); the `N`-killing that places a Drinfeld structure inside
`E[N]` is KM 1.4.2 at invertible `N` (`smul_eq_zero_of_invertible`, T-E4F1 — the
board-sanctioned `hinv` restatement; the over-`ℤ` form awaits the statement-protected
BB-DELIGNE box). -/
theorem gammaOneDrinfeld_affineOverEll (N : ℕ) [NeZero N] (hinv : IsUnit (N : R)) :
    (gammaOneDrinfeldProblem R N).AffineOverEll := by
  intro X
  obtain ⟨Z, hZ⟩ := exists_exactOrderLocus X.curve N
  refine ⟨Z.subscheme, Z.subschemeι ≫ X.curve.torsionπ N,
    exactOrderLocus_isAffineHom X.curve N Z, ?_⟩
  refine ⟨fun {T} g => Equiv.mk (fun h => ⟨EllipticCurve.Point.asSection X.curve g
      (↑(X.curve.torsionPointsEquiv N g ⟨h.1 ≫ Z.subschemeι, by rw [Category.assoc]; exact h.2⟩)),
      (hZ g _ ((X.curve.smul_eq_zero_iff_comp_mulByHom g N _).mp ((Submodule.mem_torsionBy_iff _ _).mp
          (X.curve.torsionPointsEquiv N g ⟨h.1 ≫ Z.subschemeι, by rw [Category.assoc]; exact h.2⟩).2))).mp
        ⟨h.1, (pointToTorsion_torsionPointsEquiv X.curve N g
          ⟨h.1 ≫ Z.subschemeι, by rw [Category.assoc]; exact h.2⟩).symm⟩⟩)
      (fun P => ?_) ?_ ?_, ?_⟩
  · -- invFun: a Γ₁-structure `P` on `E ×_S T` gives a `T`-point of the exact-order locus
    have hinvT : NIsInvertible T N := by
      have hSpec : NIsInvertible (Spec R) N := by
        show IsUnit ((N : ℕ) : Γ(Spec R, ⊤))
        have h2 := hinv.map (Scheme.ΓSpecIso R).inv.hom
        rwa [map_natCast] at h2
      exact hSpec.of_hom (g ≫ X.structMap)
    have hxsmul : (N : ℤ) • sectionToPoint X.curve g P.1 = 0 := by
      apply asSection_injective X.curve g
      rw [EllipticCurve.Point.asSection_zsmul, asSection_sectionToPoint, asSection_zero]
      exact EllipticCurve.Section.HasExactOrder.smul_eq_zero_of_invertible
        (X.curve.baseChange g) hinvT P.2
    have hx := (X.curve.smul_eq_zero_iff_comp_mulByHom g N _).mp hxsmul
    have hle : Z ≤ (X.curve.pointToTorsion (sectionToPoint X.curve g P.1) hx).ker := by
      rw [← exists_factor_subschemeι_iff]
      refine (hZ g _ hx).mpr ?_
      rw [asSection_sectionToPoint]; exact P.2
    refine ⟨(X.curve.pointToTorsion (sectionToPoint X.curve g P.1) hx).toImage ≫
        Scheme.IdealSheafData.inclusion hle, ?_⟩
    have hcomp : ((X.curve.pointToTorsion (sectionToPoint X.curve g P.1) hx).toImage ≫
        Scheme.IdealSheafData.inclusion hle) ≫ Z.subschemeι =
        X.curve.pointToTorsion (sectionToPoint X.curve g P.1) hx := by
      rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]
    rw [← Category.assoc, hcomp, X.curve.pointToTorsion_torsionπ]
  · -- left_inv: a locus point `h` sent through `toFun` then `invFun` returns to `h`
    intro h
    haveI : Mono Z.subschemeι := inferInstance
    refine Subtype.ext ((cancel_mono Z.subschemeι).mp ?_)
    rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]
    simp only [sectionToPoint_asSection]
    exact pointToTorsion_torsionPointsEquiv X.curve N g _
  · -- right_inv: a Γ₁-section `P` sent through `invFun` then `toFun` returns to `P`
    intro P
    refine Subtype.ext (Eq.trans (congrArg (EllipticCurve.Point.asSection X.curve g) ?_)
      (asSection_sectionToPoint X.curve g P.1))
    simp only [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]
    exact coe_torsionPointsEquiv_pointToTorsion X.curve N g (sectionToPoint X.curve g P.1) _ _
  · -- naturality: the family of equivalences commutes with restriction along `k`
    intro T T' g k h
    refine Subtype.ext (Eq.trans ?_ (pullSection_asSection X g k
      (↑(X.curve.torsionPointsEquiv N g
          ⟨h.1 ≫ Z.subschemeι, by rw [Category.assoc]; exact h.2⟩))).symm)
    refine congrArg (EllipticCurve.Point.asSection X.curve (k ≫ g)) (Subtype.ext ?_)
    simp only [EllipticCurve.Point.restrict, torsionPointsEquiv_coe_fst, Category.assoc]

/-- **(KM 4.2 / SCHOLIE 4.7.0 relative half — the Γ₁ relative-representability ★)** The
Drinfeld `Γ₁(N)` moduli problem is relatively representable over `Ell` for `N`
invertible, immediately from `gammaOneDrinfeld_affineOverEll` (KM: "relatively
representable *and* affine over (Ell)"). The representing `S`-scheme is the exact-order
locus `Z ⊆ E[N]` (finite over `S`). No rank hypothesis (`c4`) is used; the only
inherited black box is `E[N]`-finiteness (KM 2.3.1). -/
theorem gammaOneDrinfeld_relativelyRepresentable (N : ℕ) [NeZero N]
    (hinv : IsUnit (N : R)) :
    (gammaOneDrinfeldProblem R N).RelativelyRepresentable :=
  (gammaOneDrinfeld_affineOverEll N hinv).relativelyRepresentable

end ModularCurves
