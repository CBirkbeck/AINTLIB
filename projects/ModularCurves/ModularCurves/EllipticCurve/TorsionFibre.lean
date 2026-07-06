import ModularCurves.EllipticCurve.Torsion
import ModularCurves.ForMathlib.EtaleSectionsCount
import ModularCurves.ForMathlib.FiniteAbelianRankTwo

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

open scoped CategoryTheory.Obj in
/-- **(T-B6a)** Multiplication by `n` commutes with base change: the first projection of
the defining pullback intertwines `[n]` on `E ×_S T` with `[n]` on `E`. -/
theorem mulByHom_baseChange {T : Scheme.{u}} (g : T ⟶ S) (n : ℤ) :
    (E.baseChange g).mulByHom n ≫ pullback.fst E.π g =
      pullback.fst E.π g ≫ E.mulByHom n := by
  letI : Group (E.asOver ⟶ E.asOver) := Hom.group
  letI : Group ((Over.pullback g).obj E.asOver ⟶ (Over.pullback g).obj E.asOver) :=
    Hom.group
  have key : (E.baseChange g).mulBy n = (Over.pullback g).map (E.mulBy n) := by
    show (𝟙 ((Over.pullback g).obj E.asOver)) ^ n =
      (Over.pullback g).map ((𝟙 E.asOver) ^ n)
    have h1 : (Over.pullback g).map ((𝟙 E.asOver) ^ n) =
        (Over.pullback g).homMonoidHom ((𝟙 E.asOver) ^ n) := rfl
    have h2 : (Over.pullback g).homMonoidHom (𝟙 E.asOver) =
        𝟙 ((Over.pullback g).obj E.asOver) := (Over.pullback g).map_id E.asOver
    rw [h1, map_zpow ((Over.pullback g).homMonoidHom) (𝟙 E.asOver) n, h2]
  have hleft : (E.baseChange g).mulByHom n = ((Over.pullback g).map (E.mulBy n)).left :=
    congrArg CommaMorphism.left key
  rw [hleft]
  exact pullback.lift_fst _ _ _

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
              (E.mulByHom_baseChange g (N : ℤ)).symm
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
          congrArg (fun q => c ≫ q) (E.mulByHom_baseChange g (N : ℤ))
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
