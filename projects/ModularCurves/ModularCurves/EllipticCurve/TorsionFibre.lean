import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.MulByHomUnramifiedField
import ModularCurves.EllipticCurve.MulByHomDegree
import ModularCurves.ForMathlib.EtaleSectionsCount
import ModularCurves.ForMathlib.FiniteAbelianRankTwo
import ModularCurves.ForMathlib.FormallyUnramifiedFibre
import ModularCurves.ForMathlib.NilpotentKerSpecMap
import ModularCurves.ForMathlib.UnramifiedOfCardAlgHom
import HasseWeil.NTorsion.TorsionGeneralN
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Fibre comparison for the torsion subscheme (ticket T-B6)

Two layers, per the T-B6 design of record (replanned 2026-07-06):

* `torsionPointsEquiv` — the **kernel universal property**: `T`-points of `E[N]` over
  `t : T ⟶ S` are exactly the `N`-torsion of the abstract point group `E.Point t`,
  i.e. `Submodule.torsionBy ℤ (E.Point t) (N : ℤ)`. This is what the Drinfeld-structure
  translations (stream D) consume, and it pins `E.torsion` against `mulBy`.
* `torsion_geometricFibre_rank_two` — the **headline geometric statement**: over an
  algebraically closed field in which `N` is invertible, that torsion group is
  `(ℤ/N)²`. Route (KM 2.3.5/Silverman III.6.4 counting, NOT the chord–tangent
  dictionary): torsion commutes with base change (`torsion_baseChange_isPullback`),
  the base-changed torsion is finite étale of rank `d ^ 2` over the fibre field
  (T-B4/T-B5 outputs, modulo the registered black boxes `BB-QF`/`BB-FLAT`/`BB-DEG`/
  `BB-DIFF`), a finite étale scheme over `Spec k̄` has exactly `finrank` sections
  (`natCard_sections_eq_finrank`), and the torsion-count characterisation of `(ℤ/N)²`
  (`addEquiv_pi_fin_two_zmod_of_natCard`) finishes. The comparison with the classical
  chord–tangent group (HasseWeil) is the separate optional dictionary leaf, still
  recorded on the board for the black-box discharges.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-- **(T-B6c)** On the spectrum of a field, `N` is invertible iff `N ≠ 0` in the field. -/
theorem nIsInvertible_spec_iff (k : Type u) [Field k] (N : ℕ) :
    NIsInvertible (Spec (CommRingCat.of k)) N ↔ (N : k) ≠ 0 := by
  rw [NIsInvertible]
  constructor
  · intro h
    have h2 := h.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    rw [map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom N] at h2
    exact isUnit_iff_ne_zero.mp h2
  · intro h
    have h2 := (isUnit_iff_ne_zero.mpr h).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    rwa [map_natCast (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom N] at h2

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The zero section of the base-changed curve projects to the zero section. -/
@[reassoc]
theorem baseChange_zero_fst {T : Scheme.{u}} (g : T ⟶ S) :
    (E.baseChange g).zero ≫ pullback.fst E.π g = g ≫ E.zero :=
  pullback.lift_fst _ _ _

/-- **(T-B6b, the comparison map)** The canonical morphism from the torsion of the
base-changed curve to the torsion of `E`, lifting `torsionι ≫ pr₁` and `torsionπ ≫ g`. -/
noncomputable def torsionBaseChangeHom (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    (E.baseChange g).torsion N ⟶ E.torsion N :=
  pullback.lift ((E.baseChange g).torsionι N ≫ pullback.fst E.π g)
    ((E.baseChange g).torsionπ N ≫ g) <| by
      have hcond : (E.baseChange g).torsionι N ≫ (E.baseChange g).mulByHom N =
          (E.baseChange g).torsionπ N ≫ (E.baseChange g).zero := pullback.condition
      calc ((E.baseChange g).torsionι N ≫ pullback.fst E.π g) ≫ E.mulByHom N
          = (E.baseChange g).torsionι N ≫ pullback.fst E.π g ≫ E.mulByHom N :=
            Category.assoc _ _ _
        _ = (E.baseChange g).torsionι N ≫ (E.baseChange g).mulByHom N ≫
              pullback.fst E.π g :=
            congrArg (fun q => (E.baseChange g).torsionι N ≫ q)
              (E.mulByHom_baseChange_fst g (N : ℤ)).symm
        _ = ((E.baseChange g).torsionι N ≫ (E.baseChange g).mulByHom N) ≫
              pullback.fst E.π g := (Category.assoc _ _ _).symm
        _ = ((E.baseChange g).torsionπ N ≫ (E.baseChange g).zero) ≫
              pullback.fst E.π g :=
            congrArg (fun q => q ≫ pullback.fst E.π g) hcond
        _ = (E.baseChange g).torsionπ N ≫ (E.baseChange g).zero ≫ pullback.fst E.π g :=
            Category.assoc _ _ _
        _ = (E.baseChange g).torsionπ N ≫ g ≫ E.zero :=
            congrArg (fun q => (E.baseChange g).torsionπ N ≫ q) (E.baseChange_zero_fst g)
        _ = ((E.baseChange g).torsionπ N ≫ g) ≫ E.zero := (Category.assoc _ _ _).symm

@[reassoc (attr := simp)]
theorem torsionBaseChangeHom_torsionι (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    E.torsionBaseChangeHom N g ≫ E.torsionι N =
      (E.baseChange g).torsionι N ≫ pullback.fst E.π g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem torsionBaseChangeHom_torsionπ (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    E.torsionBaseChangeHom N g ≫ E.torsionπ N =
      (E.baseChange g).torsionπ N ≫ g :=
  pullback.lift_snd _ _ _

private lemma torsionLiftAux_inner_w (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) :
    (a ≫ E.torsionι N) ≫ E.π = b ≫ g :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) (E.torsionι_π N)).trans hab)

private lemma torsionLiftAux_outer_w (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) :
    pullback.lift (a ≫ E.torsionι N) b (E.torsionLiftAux_inner_w N g a b hab) ≫
        (E.baseChange g).mulByHom N =
      b ≫ (E.baseChange g).zero := by
  have hcondS : E.torsionι N ≫ E.mulByHom N = E.torsionπ N ≫ E.zero :=
    pullback.condition
  have hπT : (E.baseChange g).mulByHom (N : ℤ) ≫ pullback.snd E.π g =
      pullback.snd E.π g := (E.baseChange g).mulByHom_π (N : ℤ)
  have hzπT : (E.baseChange g).zero ≫ pullback.snd E.π g = 𝟙 T :=
    (E.baseChange g).zero_π
  set c := pullback.lift (a ≫ E.torsionι N) b (E.torsionLiftAux_inner_w N g a b hab)
    with hc
  apply pullback.hom_ext
  · calc (c ≫ (E.baseChange g).mulByHom N) ≫ pullback.fst E.π g
        = c ≫ (E.baseChange g).mulByHom N ≫ pullback.fst E.π g := Category.assoc _ _ _
      _ = c ≫ pullback.fst E.π g ≫ E.mulByHom N :=
          congrArg (fun q => c ≫ q) (E.mulByHom_baseChange_fst g (N : ℤ))
      _ = (c ≫ pullback.fst E.π g) ≫ E.mulByHom N := (Category.assoc _ _ _).symm
      _ = (a ≫ E.torsionι N) ≫ E.mulByHom N :=
          congrArg (fun q => q ≫ E.mulByHom (N : ℤ)) (pullback.lift_fst _ _ _)
      _ = a ≫ E.torsionι N ≫ E.mulByHom N := Category.assoc _ _ _
      _ = a ≫ E.torsionπ N ≫ E.zero := congrArg (fun q => a ≫ q) hcondS
      _ = (a ≫ E.torsionπ N) ≫ E.zero := (Category.assoc _ _ _).symm
      _ = (b ≫ g) ≫ E.zero := congrArg (fun q => q ≫ E.zero) hab
      _ = b ≫ g ≫ E.zero := Category.assoc _ _ _
      _ = b ≫ (E.baseChange g).zero ≫ pullback.fst E.π g :=
          congrArg (fun q => b ≫ q) (E.baseChange_zero_fst g).symm
      _ = (b ≫ (E.baseChange g).zero) ≫ pullback.fst E.π g :=
          (Category.assoc _ _ _).symm
  · calc (c ≫ (E.baseChange g).mulByHom N) ≫ pullback.snd E.π g
        = c ≫ (E.baseChange g).mulByHom N ≫ pullback.snd E.π g := Category.assoc _ _ _
      _ = c ≫ pullback.snd E.π g := congrArg (fun q => c ≫ q) hπT
      _ = b := pullback.lift_snd _ _ _
      _ = b ≫ 𝟙 T := (Category.comp_id _).symm
      _ = b ≫ (E.baseChange g).zero ≫ pullback.snd E.π g :=
          congrArg (fun q => b ≫ q) hzπT.symm
      _ = (b ≫ (E.baseChange g).zero) ≫ pullback.snd E.π g :=
          (Category.assoc _ _ _).symm

/-- The universal lift into the base-changed torsion: a morphism into `E[N]` and a
morphism into `T` agreeing over `S` assemble into a morphism into `(E ×_S T)[N]`. -/
private noncomputable def torsionLiftAux (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) : X ⟶ (E.baseChange g).torsion N :=
  pullback.lift
    (pullback.lift (a ≫ E.torsionι N) b (E.torsionLiftAux_inner_w N g a b hab))
    b (E.torsionLiftAux_outer_w N g a b hab)

private lemma torsionLiftAux_torsionι (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) :
    E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N =
      pullback.lift (a ≫ E.torsionι N) b (E.torsionLiftAux_inner_w N g a b hab) :=
  pullback.lift_fst _ _ _

private lemma torsionLiftAux_torsionπ (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) :
    E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionπ N = b :=
  pullback.lift_snd _ _ _

private lemma torsionLiftAux_comp (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) :
    E.torsionLiftAux N g a b hab ≫ E.torsionBaseChangeHom N g = a := by
  have hθι : E.torsionBaseChangeHom N g ≫ E.torsionι N =
      (E.baseChange g).torsionι N ≫ pullback.fst E.π g :=
    E.torsionBaseChangeHom_torsionι N g
  have hθπ : E.torsionBaseChangeHom N g ≫ E.torsionπ N =
      (E.baseChange g).torsionπ N ≫ g := E.torsionBaseChangeHom_torsionπ N g
  set L := E.torsionLiftAux N g a b hab with hL
  apply pullback.hom_ext
  · calc (L ≫ E.torsionBaseChangeHom N g) ≫ pullback.fst (E.mulByHom N) E.zero
        = L ≫ E.torsionBaseChangeHom N g ≫ E.torsionι N := Category.assoc _ _ _
      _ = L ≫ (E.baseChange g).torsionι N ≫ pullback.fst E.π g :=
          congrArg (fun q => L ≫ q) hθι
      _ = (L ≫ (E.baseChange g).torsionι N) ≫ pullback.fst E.π g :=
          (Category.assoc _ _ _).symm
      _ = pullback.lift (a ≫ E.torsionι N) b
            (E.torsionLiftAux_inner_w N g a b hab) ≫ pullback.fst E.π g :=
          congrArg (fun q => q ≫ pullback.fst E.π g)
            (E.torsionLiftAux_torsionι N g a b hab)
      _ = a ≫ E.torsionι N := pullback.lift_fst _ _ _
  · calc (L ≫ E.torsionBaseChangeHom N g) ≫ pullback.snd (E.mulByHom N) E.zero
        = L ≫ E.torsionBaseChangeHom N g ≫ E.torsionπ N := Category.assoc _ _ _
      _ = L ≫ (E.baseChange g).torsionπ N ≫ g :=
          congrArg (fun q => L ≫ q) hθπ
      _ = (L ≫ (E.baseChange g).torsionπ N) ≫ g := (Category.assoc _ _ _).symm
      _ = b ≫ g := congrArg (fun q => q ≫ g) (E.torsionLiftAux_torsionπ N g a b hab)
      _ = a ≫ E.torsionπ N := hab.symm

private lemma torsionLiftAux_uniq (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S)
    {X : Scheme.{u}} (a : X ⟶ E.torsion N) (b : X ⟶ T)
    (hab : a ≫ E.torsionπ N = b ≫ g) (m : X ⟶ (E.baseChange g).torsion N)
    (hm1 : m ≫ E.torsionBaseChangeHom N g = a)
    (hm2 : m ≫ (E.baseChange g).torsionπ N = b) :
    m = E.torsionLiftAux N g a b hab := by
  have hιπT : (E.baseChange g).torsionι N ≫ pullback.snd E.π g =
      (E.baseChange g).torsionπ N := (E.baseChange g).torsionι_π N
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc (m ≫ (E.baseChange g).torsionι N) ≫ pullback.fst E.π g
          = m ≫ (E.baseChange g).torsionι N ≫ pullback.fst E.π g :=
            Category.assoc _ _ _
        _ = m ≫ E.torsionBaseChangeHom N g ≫ E.torsionι N :=
            congrArg (fun q => m ≫ q) (E.torsionBaseChangeHom_torsionι N g).symm
        _ = (m ≫ E.torsionBaseChangeHom N g) ≫ E.torsionι N :=
            (Category.assoc _ _ _).symm
        _ = a ≫ E.torsionι N := congrArg (fun q => q ≫ E.torsionι N) hm1
        _ = pullback.lift (a ≫ E.torsionι N) b
              (E.torsionLiftAux_inner_w N g a b hab) ≫ pullback.fst E.π g :=
            (pullback.lift_fst _ _ _).symm
        _ = (E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N) ≫
              pullback.fst E.π g :=
            congrArg (fun q => q ≫ pullback.fst E.π g)
              (E.torsionLiftAux_torsionι N g a b hab).symm
        _ = E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N ≫
              pullback.fst E.π g := Category.assoc _ _ _
        _ = (E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N) ≫
              pullback.fst E.π g := (Category.assoc _ _ _).symm
    · calc (m ≫ (E.baseChange g).torsionι N) ≫ pullback.snd E.π g
          = m ≫ (E.baseChange g).torsionι N ≫ pullback.snd E.π g :=
            Category.assoc _ _ _
        _ = m ≫ (E.baseChange g).torsionπ N := congrArg (fun q => m ≫ q) hιπT
        _ = b := hm2
        _ = E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionπ N :=
            (E.torsionLiftAux_torsionπ N g a b hab).symm
        _ = E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N ≫
              pullback.snd E.π g :=
            congrArg (fun q => E.torsionLiftAux N g a b hab ≫ q) hιπT.symm
        _ = (E.torsionLiftAux N g a b hab ≫ (E.baseChange g).torsionι N) ≫
              pullback.snd E.π g := (Category.assoc _ _ _).symm
  · exact hm2.trans (E.torsionLiftAux_torsionπ N g a b hab).symm

/-- **(T-B6b)** Torsion commutes with base change: the square
`(E ×_S T)[N] ⟶ E[N]`, `(E ×_S T)[N] ⟶ T`, `E[N] ⟶ S`, `T ⟶ S` is cartesian. -/
theorem torsion_baseChange_isPullback (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (E.torsionBaseChangeHom N g) ((E.baseChange g).torsionπ N)
      (E.torsionπ N) g :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (E.torsionBaseChangeHom_torsionπ N g)
    (fun s => E.torsionLiftAux N g s.fst s.snd s.condition)
    (fun s => E.torsionLiftAux_comp N g s.fst s.snd s.condition)
    (fun s => E.torsionLiftAux_torsionπ N g s.fst s.snd s.condition)
    (fun s m h1 h2 => E.torsionLiftAux_uniq N g s.fst s.snd s.condition m h1 h2))

/-- The zero of the point group is the pulled-back zero section. -/
theorem point_zero_val {T : Scheme.{u}} (g : T ⟶ S) :
    ((0 : E.Point g) : T ⟶ E.E) = g ≫ E.zero := by
  have h0 : (0 : E.Point g) = (E.pointEquivOverHom g).symm
      (Additive.toMul (0 : Additive (Over.mk g ⟶ E.asOver))) := rfl
  rw [h0, toMul_zero]
  show ((1 : Over.mk g ⟶ E.asOver)).left = g ≫ E.zero
  rw [Hom.one_def, Over.comp_left, E.one_eq_zero]
  have hw : (toUnit (Over.mk g)).left ≫ (𝟙_ (Over S)).hom = g :=
    Over.w (toUnit (Over.mk g))
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ E.zero) hw)

/-- Membership in the `N`-torsion of the point group, morphism-level form. -/
theorem smul_eq_zero_iff_comp_mulByHom {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ)
    (P : E.Point g) :
    (N : ℤ) • P = 0 ↔ (P : T ⟶ E.E) ≫ E.mulByHom (N : ℤ) = g ≫ E.zero := by
  constructor
  · intro h
    have hval := congrArg (fun Q : E.Point g ↦ (Q : T ⟶ E.E)) h
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val] at hval
    exact hval
  · intro h
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_zero_val]
    exact h

/-- **(T-B6, kernel universal property)** `T`-points of the torsion subscheme `E[N]`
over `t : T ⟶ S` are the `N`-torsion of the point group `E.Point t`. This pins
`E.torsion` (the kernel pullback of `[N]`) against the point-level `[N]`. -/
noncomputable def torsionPointsEquiv (N : ℕ) {T : Scheme.{u}} (t : T ⟶ S) :
    { h : T ⟶ E.torsion N // h ≫ E.torsionπ N = t } ≃
      Submodule.torsionBy ℤ (E.Point t) (N : ℤ) where
  toFun h := ⟨⟨h.1 ≫ E.torsionι N, by
      have hcond : E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero :=
        pullback.condition
      have hπ : E.torsionι N ≫ E.π = E.torsionπ N := by
        have h2 := congrArg (fun m ↦ m ≫ E.π) hcond
        simpa [E.mulByHom_π, E.zero_π] using h2
      rw [Category.assoc, hπ, h.2]⟩, by
    have hcond : E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero :=
      pullback.condition
    rw [Submodule.mem_torsionBy_iff, E.smul_eq_zero_iff_comp_mulByHom]
    show (h.1 ≫ E.torsionι N) ≫ E.mulByHom (N : ℤ) = t ≫ E.zero
    rw [Category.assoc, hcond, ← Category.assoc, h.2]⟩
  invFun P := ⟨E.pointToTorsion P.1
      ((E.smul_eq_zero_iff_comp_mulByHom t N P.1).mp
        ((Submodule.mem_torsionBy_iff _ _).mp P.2)),
    E.pointToTorsion_torsionπ _ _⟩
  left_inv h := Subtype.ext <| by
    apply pullback.hom_ext
    · show E.pointToTorsion _ _ ≫ E.torsionι N = h.1 ≫ E.torsionι N
      rw [E.pointToTorsion_torsionι]
    · show E.pointToTorsion _ _ ≫ E.torsionπ N = h.1 ≫ E.torsionπ N
      rw [E.pointToTorsion_torsionπ, h.2]
  right_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    show (E.pointToTorsion _ _ ≫ E.torsionι N : T ⟶ E.E) = ((P : E.Point t) : T ⟶ E.E)
    rw [E.pointToTorsion_torsionι]

/-- Sections of the base-changed torsion over `T` are the `E[N]`-points over `t`
(the two legs of `torsion_baseChange_isPullback`). -/
private noncomputable def sectionsEquivOverPoints (N : ℕ) {T : Scheme.{u}} (t : T ⟶ S) :
    {s : T ⟶ (E.baseChange t).torsion N // s ≫ (E.baseChange t).torsionπ N = 𝟙 T} ≃
      {h : T ⟶ E.torsion N // h ≫ E.torsionπ N = t} where
  toFun s := ⟨s.1 ≫ E.torsionBaseChangeHom N t, by
    rw [Category.assoc, E.torsionBaseChangeHom_torsionπ N t, ← Category.assoc, s.2,
      Category.id_comp]⟩
  invFun h := ⟨(E.torsion_baseChange_isPullback N t).lift h.1 (𝟙 T)
      (by rw [Category.id_comp]; exact h.2),
    (E.torsion_baseChange_isPullback N t).lift_snd _ _ _⟩
  left_inv s := Subtype.ext ((E.torsion_baseChange_isPullback N t).hom_ext
    (by rw [(E.torsion_baseChange_isPullback N t).lift_fst])
    (by rw [(E.torsion_baseChange_isPullback N t).lift_snd, s.2]))
  right_inv h := Subtype.ext ((E.torsion_baseChange_isPullback N t).lift_fst _ _ _)

private lemma torsionByNsmulKer_mem (G : Type u) [AddCommGroup G] {N d : ℕ}
    (hdN : d ∣ N) {y : G} (hy : (d : ℤ) • y = 0) :
    y ∈ Submodule.torsionBy ℤ G (N : ℤ) := by
  rw [Submodule.mem_torsionBy_iff]
  obtain ⟨c, hc⟩ := hdN
  rw [hc, Nat.cast_mul, mul_comm, mul_zsmul, hy, smul_zero]

private def torsionByNsmulKerEquiv (G : Type u) [AddCommGroup G] (N d : ℕ)
    (hdN : d ∣ N) :
    {x : Submodule.torsionBy ℤ G (N : ℤ) // d • x = 0} ≃
      Submodule.torsionBy ℤ G (d : ℤ) where
  toFun x := ⟨x.1.1, by
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    have h2 := congrArg (Submodule.torsionBy ℤ G (N : ℤ)).subtype x.2
    rwa [map_nsmul, map_zero] at h2⟩
  invFun y := ⟨⟨y.1, torsionByNsmulKer_mem G hdN
      ((Submodule.mem_torsionBy_iff _ _).mp y.2)⟩, by
    apply Subtype.ext
    have h2 : ((d • (⟨y.1, torsionByNsmulKer_mem G hdN
        ((Submodule.mem_torsionBy_iff _ _).mp y.2)⟩ :
        Submodule.torsionBy ℤ G (N : ℤ)) : Submodule.torsionBy ℤ G (N : ℤ)) : G) =
        d • (y.1 : G) :=
      map_nsmul (Submodule.torsionBy ℤ G (N : ℤ)).subtype d _
    rw [h2, ZeroMemClass.coe_zero, ← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp y.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

/-! ### BB-DIFF (T-B5 = Loeffler 3.4.2(2)): `[N]` and `E[N] ⟶ S` are unramified/étale
for `N` invertible

The torsor reduction (`formallyUnramified_mulByHom_of_torsionπ`, migrated from the
BB-DIFF skeleton), the residue-fibre criterion (`FormallyUnramifiedFibre`), and the
field-level fibre leg (`MulByHomUnramifiedField`) assemble `mulByHom_formallyUnramified`
and the étale trio, relocated here from `Torsion.lean` (statements unchanged) because
their proofs run through this file's torsion machinery. -/

/-- `pointEquivOverHom` carries point-subtraction to the division of `Over`-homs (companion to
`pointEquivOverHom_add`). -/
theorem pointEquivOverHom_sub {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P - Q) =
      (E.pointEquivOverHom g) P / (E.pointEquivOverHom g) Q := rfl

/-- Restriction of a point along `k` corresponds, under `pointEquivOverHom`, to precomposition by
the induced `Over`-morphism `Over.mk (k ≫ g) ⟶ Over.mk g`. -/
theorem pointEquivOverHom_restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.pointEquivOverHom (k ≫ g) (Point.restrict E k P) =
      (Over.homMk k : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ E.pointEquivOverHom g P := by
  apply Over.OverMorphism.ext
  simp only [pointEquivOverHom, Equiv.coe_fn_mk, Point.restrict, Over.comp_left, Over.homMk_left]
  rfl

/-- `Point.restrict` is additive on subtraction (precomposition is a group homomorphism). -/
theorem restrict_sub {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P - Q) = Point.restrict E k P - Point.restrict E k Q := by
  apply (E.pointEquivOverHom (k ≫ g)).injective
  simp only [E.pointEquivOverHom_restrict, E.pointEquivOverHom_sub, GrpObj.comp_div]

/-- **(BB-DIFF, L-A — the torsor reduction)** If the `N`-torsion `E[N] → S` is formally
unramified, then so is `[N] : E ⟶ E`. Route-independent: `[N]` is an f.p.p.f `E[N]`-torsor (KM Cor.
2.3.2), so two infinitesimal lifts `g₁, g₂` of `[N]` agreeing on a square-zero closed subscheme differ
by a map into `E[N]` vanishing there, which is `0` once `E[N] → S` is formally unramified — hence
`g₁ = g₂`. Uses only the `GrpObj` group structure of `E` and mathlib's `FormallyUnramified` morphism
property. -/
theorem formallyUnramified_mulByHom_of_torsionπ (N : ℕ)
    (htors : FormallyUnramified (E.torsionπ N)) :
    FormallyUnramified (E.mulByHom N) := by
  apply FormallyUnramified.of_hom_ext
  intro R S' φ hφ hφ2 g₁ g₂ hthick hf
  -- both lifts share a base `s`
  have hbase : g₁ ≫ E.π = g₂ ≫ E.π := by
    have h := congrArg (fun m => m ≫ E.π) hf
    simpa only [Category.assoc, E.mulByHom_π] using h
  set s : Spec R ⟶ S := g₁ ≫ E.π with hs
  let P₁ : E.Point s := ⟨g₁, hs.symm⟩
  let P₂ : E.Point s := ⟨g₂, hbase.symm.trans hs.symm⟩
  -- the difference is killed by `N`
  have hNP : ((N : ℤ) • P₁ : E.Point s) = (N : ℤ) • P₂ := by
    apply Subtype.ext
    rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
    exact hf
  have hNh : ((N : ℤ) • (P₁ - P₂) : E.Point s) = 0 := by rw [smul_sub, hNP, sub_self]
  have hkill : ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) ≫ E.mulByHom N = s ≫ E.zero :=
    (E.smul_eq_zero_iff_comp_mulByHom s N (P₁ - P₂)).mp hNh
  have hzero : ((0 : E.Point s) : Spec R ⟶ E.E) ≫ E.mulByHom N = s ≫ E.zero :=
    (E.smul_eq_zero_iff_comp_mulByHom s N 0).mp (smul_zero _)
  -- on the thickening, the difference restricts to `0`
  have hci : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  have hrestrict : Spec.map φ ≫ ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) =
      Spec.map φ ≫ (s ≫ E.zero) := by
    have hPeq : Point.restrict E (Spec.map φ) P₁ = Point.restrict E (Spec.map φ) P₂ :=
      Subtype.ext hthick
    have hh0 : Point.restrict E (Spec.map φ) (P₁ - P₂) = 0 := by
      rw [E.restrict_sub, hPeq, sub_self]
    have hval := congrArg Subtype.val hh0
    simp only [Point.restrict, E.point_zero_val] at hval
    rw [hval, Category.assoc]
  -- the two torsion points agree after the thickening and after `torsionπ`
  have e1 : (Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill) ≫ E.torsionι N =
      (Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero) ≫ E.torsionι N := by
    rw [Category.assoc, Category.assoc, E.pointToTorsion_torsionι, E.pointToTorsion_torsionι,
      E.point_zero_val]
    exact hrestrict
  have e2 : (Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill) ≫ E.torsionπ N =
      (Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero) ≫ E.torsionπ N := by
    rw [Category.assoc, Category.assoc, E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hig : Spec.map φ ≫ E.pointToTorsion (P₁ - P₂) hkill =
      Spec.map φ ≫ E.pointToTorsion (0 : E.Point s) hzero :=
    pullback.hom_ext e1 e2
  have hgf : E.pointToTorsion (P₁ - P₂) hkill ≫ E.torsionπ N =
      E.pointToTorsion (0 : E.Point s) hzero ≫ E.torsionπ N := by
    rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]
  have hPz : E.pointToTorsion (P₁ - P₂) hkill = E.pointToTorsion (0 : E.Point s) hzero :=
    FormallyUnramified.hom_ext (Spec.map φ) (isNilpotent_ker_SpecMap φ hφ2) (E.torsionπ N) hig hgf
  -- project back to the points
  have hfin : ((P₁ - P₂ : E.Point s) : Spec R ⟶ E.E) = ((0 : E.Point s) : Spec R ⟶ E.E) := by
    have h := congrArg (fun m => m ≫ E.torsionι N) hPz
    rwa [E.pointToTorsion_torsionι, E.pointToTorsion_torsionι] at h
  have hP : (P₁ : E.Point s) = P₂ := sub_eq_zero.mp (Subtype.ext hfin)
  exact congrArg Subtype.val hP

/-- **(BB-DIFF, T-DISC funnel)** `E[N] ⟶ S` is formally unramified once every
residue-field fibre is: T-DISC (`of_finite_fiberToSpecResidueField`) + `torsionπ_isFinite`. -/
theorem formallyUnramified_torsionπ_of_fibres (N : ℕ) [NeZero N]
    (hfib : ∀ y, FormallyUnramified ((E.torsionπ N).fiberToSpecResidueField y)) :
    FormallyUnramified (E.torsionπ N) :=
  haveI := E.torsionπ_isFinite N
  FormallyUnramified.of_finite_fiberToSpecResidueField (f := E.torsionπ N) hfib

/-! #### The geometric leaf: `[N]` on the model over an algebraically closed field

The kernel-count argument: `E[N] → Spec κ̄` has exactly `N²` sections
(`torsionPointsEquiv` + the points dictionary `projModelPointsAddEquiv` + HasseWeil's
`torsion_genN_addEquiv : E[N] ≃+ (ℤ/N)²`) and rank `N²` (`torsion_rank`), so it is
formally unramified by the split criterion — and the torsor reduction L-A pushes this
to `[N]` itself. The κ̄-descent then delivers every field, and `fibrewiseElliptic`
every residue fibre of an arbitrary base. -/

section GeometricLeaf

/-- An additive equivalence restricts to the `n`-torsion submodules. -/
private def addEquivTorsionBy {G H : Type u} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (n : ℤ) :
    Submodule.torsionBy ℤ G n ≃ Submodule.torsionBy ℤ H n where
  toFun x := ⟨e x.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul e,
      (Submodule.mem_torsionBy_iff _ _).mp x.2, map_zero]⟩
  invFun y := ⟨e.symm y.1, by
    rw [Submodule.mem_torsionBy_iff, ← map_zsmul e.symm,
      (Submodule.mem_torsionBy_iff _ _).mp y.2, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)

open WeierstrassCurve in
/-- **(the kernel count)** Over an algebraically closed field `κ` in which `N ≠ 0`, the
torsion scheme `E[N]` of the projective model has exactly `N ^ 2` sections: sections are
the `N`-torsion of the point group (`torsionPointsEquiv`), which the points dictionary
(`projModelPointsAddEquiv`) and HasseWeil's general-`N` structure theorem
(`torsion_genN_addEquiv`) identify with `(ℤ/N)²`. -/
theorem modelTorsion_sections_natCard {κ : Type u} [Field κ] [IsAlgClosed κ]
    (W : WeierstrassCurve κ) [W.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : κ) ≠ 0) :
    Nat.card { s : Spec (CommRingCat.of κ) ⟶ (modelEllipticCurve W).torsion N //
        s ≫ (modelEllipticCurve W).torsionπ N = 𝟙 (Spec (CommRingCat.of κ)) }
      = N ^ 2 := by
  classical
  have hmor : Spec.map (CommRingCat.ofHom (algebraMap κ κ))
      = 𝟙 (Spec (CommRingCat.of κ)) := by
    rw [show algebraMap κ κ = RingHom.id κ from rfl]
    rw [show CommRingCat.ofHom (RingHom.id κ) = 𝟙 (CommRingCat.of κ) from rfl]
    exact Spec.map_id _
  calc Nat.card { s : Spec (CommRingCat.of κ) ⟶ (modelEllipticCurve W).torsion N //
        s ≫ (modelEllipticCurve W).torsionπ N = 𝟙 (Spec (CommRingCat.of κ)) }
      = Nat.card { s : Spec (CommRingCat.of κ) ⟶ (modelEllipticCurve W).torsion N //
          s ≫ (modelEllipticCurve W).torsionπ N
            = Spec.map (CommRingCat.ofHom (algebraMap κ κ)) } :=
        Nat.card_congr (Equiv.subtypeEquivRight fun s => by rw [hmor])
    _ = Nat.card (Submodule.torsionBy ℤ
          ((modelEllipticCurve W).Point (Spec.map (CommRingCat.ofHom (algebraMap κ κ))))
          (N : ℤ)) :=
        Nat.card_congr ((modelEllipticCurve W).torsionPointsEquiv N _)
    _ = Nat.card (Submodule.torsionBy ℤ ((W.baseChange κ).toAffine.Point) (N : ℤ)) :=
        Nat.card_congr (addEquivTorsionBy (projModelPointsAddEquiv W κ) (N : ℤ))
    _ = Nat.card (HasseWeil.torsionSubgroup (W.baseChange κ).toAffine (N : ℤ)) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun P => by
          rw [Submodule.mem_torsionBy_iff, ← HasseWeil.mem_torsionSubgroup])
    _ = Nat.card (Fin 2 → ZMod N) :=
        Nat.card_congr
          (HasseWeil.NTorsion.torsion_genN_addEquiv (W.baseChange κ) N hN).toEquiv
    _ = N ^ 2 := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Nat.card_zmod,
          Fintype.card_fin]

/-- **(the geometric torsion is unramified)** Over an algebraically closed field with
`N ≠ 0`, `E[N] → Spec κ` is formally unramified: it is finite of rank `N ^ 2`
(`torsion_rank`) with `N ^ 2` sections (`modelTorsion_sections_natCard`), so the split
criterion applies. -/
theorem modelTorsionπ_formallyUnramified_of_isAlgClosed {κ : Type u} [Field κ]
    [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : κ) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).torsionπ N) := by
  haveI := (modelEllipticCurve W).torsionπ_isFinite N
  obtain ⟨x₀⟩ : Nonempty ↑(Spec (CommRingCat.of κ)) := inferInstance
  refine FormallyUnramified.of_natCard_sections_eq_finrank _ x₀ ?_
  rw [modelTorsion_sections_natCard W N hN,
    (modelEllipticCurve W).torsion_rank N x₀]

/-- **(BB-DIFF geometric leaf — the T-B5 residual, now a REAL proof)** Over an
algebraically closed field `κ` in which `N` is invertible, `[N]` on the projective model
is formally unramified: the torsor reduction L-A applied to the unramified kernel. -/
theorem modelMulByHom_formallyUnramified_of_isAlgClosed {κ : Type u} [Field κ]
    [IsAlgClosed κ] (W : WeierstrassCurve κ) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : κ) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).mulByHom (N : ℤ)) :=
  (modelEllipticCurve W).formallyUnramified_mulByHom_of_torsionπ N
    (modelTorsionπ_formallyUnramified_of_isAlgClosed W N hN)

open WeierstrassCurve in
/-- **(BB-DIFF field leaf, any field)** Over ANY field `k` in which `N` is invertible,
`[N]` on the projective model is formally unramified: base-change to the algebraic
closure (the geometric case above), transport across the pointed group-object iso
`modelBaseChangeIsoAsOver`, and fppf-descend along `Spec κ̄ → Spec k` via mathlib's
`DescendsAlong @FormallyUnramified` instance — the `@LocallyQuasiFinite` κ̄-wiring of
`modelMulByHom_locallyQuasiFinite_of_field`, verbatim. -/
theorem modelMulByHom_formallyUnramified_of_field {k : Type u} [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
  set κ := AlgebraicClosure k
  set fc : CommRingCat.of k ⟶ CommRingCat.of κ := CommRingCat.ofHom (algebraMap k κ)
    with hfc
  have hNκ : (N : κ) ≠ 0 := by
    intro h0
    apply hN
    have : algebraMap k κ (N : k) = 0 := by rw [map_natCast, h0]
    exact (map_eq_zero _).mp this
  -- (1) the geometric case over the algebraic closure
  haveI h1 : FormallyUnramified
      ((modelEllipticCurve (W.map (algebraMap k κ))).mulByHom (N : ℤ)) :=
    modelMulByHom_formallyUnramified_of_isAlgClosed (W.map (algebraMap k κ)) N hNκ
  -- (2) transport across the pointed group-object iso to the base-changed record
  obtain ⟨φ, hφ⟩ := modelBaseChangeIsoAsOver W κ
  haveI := hφ
  haveI h2 : FormallyUnramified
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ)) :=
    formallyUnramified_mulByHom_of_isMonHom_iso φ (N : ℤ) h1
  -- (3) the `[N]` base-change square, by cancelling the π-square off the big rectangle
  have hcomm : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ) ≫
        pullback.fst (modelEllipticCurve W).π (Spec.map fc)
      = pullback.fst (modelEllipticCurve W).π (Spec.map fc) ≫
        (modelEllipticCurve W).mulByHom (N : ℤ) :=
    mulByHom_baseChange_fst (modelEllipticCurve W) (Spec.map fc) (N : ℤ)
  have hsq : IsPullback
      (((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ))
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      (pullback.fst (modelEllipticCurve W).π (Spec.map fc))
      ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
    refine IsPullback.of_right ?_ hcomm
      ((IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip)
    have e1 : ((modelEllipticCurve W).baseChange (Spec.map fc)).mulByHom (N : ℤ) ≫
          pullback.snd (modelEllipticCurve W).π (Spec.map fc)
        = pullback.snd (modelEllipticCurve W).π (Spec.map fc) :=
      mulByHom_π ((modelEllipticCurve W).baseChange (Spec.map fc)) (N : ℤ)
    have e2 : (modelEllipticCurve W).mulByHom (N : ℤ) ≫ (modelEllipticCurve W).π
        = (modelEllipticCurve W).π :=
      mulByHom_π (modelEllipticCurve W) (N : ℤ)
    rw [e1, e2]
    exact (IsPullback.of_hasPullback (modelEllipticCurve W).π (Spec.map fc)).flip
  -- (4) the descent leg `Spec κ̄ → Spec k` is fppf
  haveI hSurjSpec : Surjective (Spec.map fc) := by
    refine ⟨fun y => ?_⟩
    haveI hsing : Subsingleton (↥(Spec (CommRingCat.of k))) :=
      ⟨fun a b => PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
        (Ideal.eq_bot_of_prime _).symm)⟩
    obtain ⟨x⟩ : Nonempty ↥(Spec (CommRingCat.of κ)) := inferInstance
    exact ⟨x, Subsingleton.elim _ _⟩
  haveI hFlatSpec : Flat (Spec.map fc) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (algebraMap k κ).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  haveI hQCSpec : QuasiCompact (Spec.map fc) := inferInstance
  -- (5) descend
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsq
    ⟨⟨MorphismProperty.pullback_fst _ _ hSurjSpec,
      MorphismProperty.pullback_fst _ _ hFlatSpec⟩,
      MorphismProperty.pullback_fst _ _ hQCSpec⟩ h2

open WeierstrassCurve in
/-- **(BB-DIFF fibre input at residue points)** `[N]` on the fibre curve
`E ×_S Spec κ(s)` is formally unramified when `N ≠ 0` in `κ(s)`: the fibre is
pointed-isomorphic to a projective Weierstrass model over `κ(s)`
(`fibreModelIsoAsOver`), whose `[N]` is formally unramified by the field-level leaf. -/
theorem formallyUnramified_mulByHom_baseChange_residueField' (E : EllipticCurve S)
    (N : ℕ) [NeZero N] (s : S) (hN : (N : S.residueField s) ≠ 0) :
    FormallyUnramified ((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) := by
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  exact formallyUnramified_mulByHom_of_isMonHom_iso φ (N : ℤ)
    (modelMulByHom_formallyUnramified_of_field W N hN)

end GeometricLeaf

/-- **(BB-DIFF, L-BC)** If `N` is invertible on `S`, the `N`-torsion `E[N] ⟶ S` is
formally unramified: each residue fibre is the torsion of the fibre curve
(`torsion_baseChange_isPullback`), which is a base change of the fibre curve's `[N]`
(unramified by the field-level leg `formallyUnramified_mulByHom_baseChange_residueField`
via the model comparison). -/
theorem formallyUnramified_torsionπ (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · haveI hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    haveI : IsEmpty (E.torsion 0) := ⟨fun x => hS.false ((E.torsionπ 0).base x)⟩
    infer_instance
  · haveI : NeZero N := ⟨hN0⟩
    refine E.formallyUnramified_torsionπ_of_fibres N (fun y => ?_)
    -- `N ≠ 0` in the residue field
    have hy : (N : S.residueField y) ≠ 0 :=
      (nIsInvertible_spec_iff (S.residueField y) N).mp
        (h.of_hom (S.fromSpecResidueField y))
    -- `[N]` on the fibre curve is formally unramified, hence so is its torsion
    haveI hNfib : FormallyUnramified
        ((E.baseChange (S.fromSpecResidueField y)).mulByHom (N : ℤ)) :=
      formallyUnramified_mulByHom_baseChange_residueField' E N y hy
    haveI hTfib : FormallyUnramified
        ((E.baseChange (S.fromSpecResidueField y)).torsionπ N) :=
      MorphismProperty.pullback_snd _ _ hNfib
    -- the scheme-theoretic fibre is the other pullback of the same cospan
    have sq1 := E.torsion_baseChange_isPullback N (S.fromSpecResidueField y)
    have hw : sq1.isoPullback.inv ≫ (E.baseChange (S.fromSpecResidueField y)).torsionπ N
        = pullback.snd (E.torsionπ N) (S.fromSpecResidueField y) ≫ 𝟙 _ := by
      rw [Category.comp_id]
      exact sq1.isoPullback_inv_snd
    show FormallyUnramified (pullback.snd (E.torsionπ N) (S.fromSpecResidueField y))
    exact (MorphismProperty.arrow_mk_iso_iff (P := @FormallyUnramified)
      (Arrow.isoMk sq1.isoPullback.symm (Iso.refl _) hw)).mpr hTfib

/-- **(BB-DIFF master, T-B5 = Loeffler 3.4.2(2))**: if `N` is invertible on `S` then
`[N]` is formally unramified — Loeffler (verbatim): *"The morphism `[N]` multiplies a
global differential by `N`, so it induces an isomorphism of tangent space."* Assembled
as L-A ∘ L-BC; the single remaining mathematical leaf is the field-level
`modelMulByHom_formallyUnramified_of_field`. -/
theorem mulByHom_formallyUnramified (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  E.formallyUnramified_mulByHom_of_torsionπ N (E.formallyUnramified_torsionπ N h)

/-- **(T-B5 = Loeffler 3.4.2(2))** If `N` is invertible on `S`, then `[N] : E ⟶ E` is étale
(it induces multiplication by `N`, an isomorphism, on the invariant differential). -/
theorem mulBy_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.mulByHom N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · haveI hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    haveI hE : IsEmpty E.E := ⟨fun x => hS.false (E.π x)⟩
    infer_instance
  · haveI : NeZero N := ⟨hN⟩
    haveI := E.mulByHom_flat N
    haveI := E.mulByHom_formallyUnramified N h
    haveI := E.mulByHom_locallyOfFinitePresentation N
    exact Etale.of_formallyUnramified_of_flat (E.mulByHom N)

/-- **(T-B5′)** If `N` is invertible on `S`, then `E[N] ⟶ S` is (finite) étale.
Source: Loeffler §3.4; KM 2.3.5. -/
theorem torsionπ_etale (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.torsionπ N) := by
  have he := E.mulBy_etale N h
  exact MorphismProperty.pullback_snd _ _ he

/-- **(T-B6 headline)** Over an algebraically closed field in which `N` is invertible,
the `N`-torsion of the geometric point group is `(ℤ/N)²`. Proof route: counting
(KM 2.3.5/[Sil] III.6.4) — étale rank-`d²` kernels over `k̄` have exactly `d ^ 2`
points, and the divisor-count spectrum pins the group. Rests on the registered
KM 2.3.1/3.4.2 black boxes (`BB-QF`/`BB-FLAT`/`BB-DEG`/`BB-DIFF`) via
`torsionπ_isFinite`/`torsionπ_etale`/`torsion_rank`. -/
theorem torsion_geometricFibre_rank_two (N : ℕ) [NeZero N] (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nonempty (Submodule.torsionBy ℤ (E.Point t) (N : ℤ) ≃+ (Fin 2 → ZMod N)) := by
  obtain ⟨x₀⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
  refine addEquiv_pi_fin_two_zmod_of_natCard N (NeZero.ne N) _ (fun x => ?_)
    (fun d hd hdN => ?_)
  · apply Subtype.ext
    have h2 : ((N • x : Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) : E.Point t) =
        N • (x : E.Point t) :=
      map_nsmul (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)).subtype N x
    rw [h2, ZeroMemClass.coe_zero, ← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).mp x.2
  · haveI : NeZero d := ⟨hd.ne'⟩
    have hdk : (d : k) ≠ 0 := by
      obtain ⟨c, hc⟩ := hdN
      intro h0
      apply hN
      rw [hc, Nat.cast_mul, h0, zero_mul]
    haveI hEt : Etale ((E.baseChange t).torsionπ d) :=
      (E.baseChange t).torsionπ_etale d ((nIsInvertible_spec_iff k d).mpr hdk)
    haveI hFin : IsFinite ((E.baseChange t).torsionπ d) :=
      (E.baseChange t).torsionπ_isFinite d
    calc Nat.card {x : Submodule.torsionBy ℤ (E.Point t) (N : ℤ) // d • x = 0}
        = Nat.card (Submodule.torsionBy ℤ (E.Point t) (d : ℤ)) :=
          Nat.card_congr (torsionByNsmulKerEquiv (E.Point t) N d hdN)
      _ = Nat.card {h : Spec (CommRingCat.of k) ⟶ E.torsion d //
            h ≫ E.torsionπ d = t} :=
          (Nat.card_congr (E.torsionPointsEquiv d t)).symm
      _ = Nat.card {s : Spec (CommRingCat.of k) ⟶ (E.baseChange t).torsion d //
            s ≫ (E.baseChange t).torsionπ d = 𝟙 (Spec (CommRingCat.of k))} :=
          (Nat.card_congr (E.sectionsEquivOverPoints d t)).symm
      _ = ((E.baseChange t).torsionπ d).finrank x₀ :=
          natCard_sections_eq_finrank ((E.baseChange t).torsionπ d) x₀
      _ = d ^ 2 := (E.baseChange t).torsion_rank d x₀

end EllipticCurve

end ModularCurves
