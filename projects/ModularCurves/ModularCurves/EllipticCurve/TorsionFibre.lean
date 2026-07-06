import ModularCurves.EllipticCurve.Torsion
import HasseWeil.NTorsion.TorsionGeneralN

/-!
# Fibre comparison for the torsion subscheme (ticket T-B6)

Two layers, per the T-B6 design note (2026-07-06):

* `torsionPointsEquiv` — the **kernel universal property**: `T`-points of `E[N]` over
  `t : T ⟶ S` are exactly the `N`-torsion of the abstract point group `E.Point t`,
  i.e. `Submodule.torsionBy ℤ (E.Point t) (N : ℤ)`. This is what the Drinfeld-structure
  translations (stream D) consume, and it pins `E.torsion` against `mulBy`.
* `torsion_geometricFibre_rank_two` — the **headline geometric statement**: over an
  algebraically closed field in which `N` is invertible, that torsion group is
  `(ℤ/N)²`. The classical input is this repository's
  `HasseWeil` `torsion_genN_addEquiv` (`E[N] ≃+ (Fin 2 → ZMod N)` for Weierstrass
  curves over a field — the cross-project import is isolated in this file). The
  remaining bridge is the **fibre group dictionary**: `FibrewiseElliptic` currently
  identifies each fibre with a Weierstrass model only as a *pointed scheme*, so
  transporting the group structure needs the fibrewise instance of the deferred
  Abel/canonicity comparison. Until that leaf lands, the headline stays a recorded
  `sorry` (see the T-B6 board entry).
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
    ((E.baseChange g).torsionπ N ≫ g) (by
      have hcond : (E.baseChange g).torsionι N ≫ (E.baseChange g).mulByHom N =
          (E.baseChange g).torsionπ N ≫ (E.baseChange g).zero := pullback.condition
      rw [Category.assoc, ← E.mulByHom_baseChange g (N : ℤ), ← Category.assoc, hcond,
        Category.assoc, E.baseChange_zero_fst g, ← Category.assoc])

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

/-- **(T-B6b)** Torsion commutes with base change: the square
`(E ×_S T)[N] ⟶ E[N]`, `(E ×_S T)[N] ⟶ T`, `E[N] ⟶ S`, `T ⟶ S` is cartesian. -/
theorem torsion_baseChange_isPullback (N : ℕ) {T : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (E.torsionBaseChangeHom N g) ((E.baseChange g).torsionπ N)
      (E.torsionπ N) g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (E.torsionBaseChangeHom_torsionπ N g) (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_))
  case _ =>
    exact pullback.lift
      (pullback.lift (s.fst ≫ E.torsionι N) s.snd
        (by rw [Category.assoc, E.torsionι_π]; exact s.condition))
      s.snd (by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, E.mulByHom_baseChange g (N : ℤ),
            E.baseChange_zero_fst g, ← Category.assoc, pullback.lift_fst,
            Category.assoc]
          have hcondS : E.torsionι N ≫ E.mulByHom N = E.torsionπ N ≫ E.zero :=
            pullback.condition
          rw [hcondS, ← Category.assoc, s.condition, Category.assoc]
        · rw [Category.assoc, Category.assoc]
          have hπT : (E.baseChange g).mulByHom (N : ℤ) ≫ (E.baseChange g).π =
              (E.baseChange g).π := (E.baseChange g).mulByHom_π (N : ℤ)
          have hzπT : (E.baseChange g).zero ≫ (E.baseChange g).π = 𝟙 T :=
            (E.baseChange g).zero_π
          show _ ≫ (E.baseChange g).mulByHom (N : ℤ) ≫ (E.baseChange g).π =
            s.snd ≫ (E.baseChange g).zero ≫ (E.baseChange g).π
          rw [hπT, hzπT, Category.comp_id]
          exact pullback.lift_snd _ _ _)
  case _ =>
    apply pullback.hom_ext
    · rw [Category.assoc]
      show _ ≫ E.torsionBaseChangeHom N g ≫ E.torsionι N = s.fst ≫ E.torsionι N
      rw [E.torsionBaseChangeHom_torsionι N g, ← Category.assoc]
      show (pullback.lift _ _ _ ≫ (E.baseChange g).torsionι N) ≫ pullback.fst E.π g = _
      rw [pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc]
      show _ ≫ E.torsionBaseChangeHom N g ≫ E.torsionπ N = s.fst ≫ E.torsionπ N
      rw [E.torsionBaseChangeHom_torsionπ N g, ← Category.assoc]
      show (pullback.lift _ _ _ ≫ (E.baseChange g).torsionπ N) ≫ g = _
      rw [pullback.lift_snd, s.condition]
  case _ =>
    show pullback.lift _ _ _ ≫ (E.baseChange g).torsionπ N = s.snd
    exact pullback.lift_snd _ _ _
  case _ =>
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]
        show m ≫ (E.baseChange g).torsionι N ≫ pullback.fst E.π g = _
        rw [← E.torsionBaseChangeHom_torsionι N g, ← Category.assoc, h1]
        rw [← Category.assoc, pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc]
        have hιπ : (E.baseChange g).torsionι N ≫ (E.baseChange g).π =
            (E.baseChange g).torsionπ N := (E.baseChange g).torsionι_π N
        show m ≫ (E.baseChange g).torsionι N ≫ pullback.snd E.π g = _
        show m ≫ (E.baseChange g).torsionι N ≫ (E.baseChange g).π = _
        rw [hιπ, h2, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · show m ≫ (E.baseChange g).torsionπ N = _
      rw [h2, ← pullback.lift_snd (pullback.lift (s.fst ≫ E.torsionι N) s.snd
        (by rw [Category.assoc, E.torsionι_π]; exact s.condition)) s.snd]
      · rfl

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

/-- **(T-B6 headline)** Over an algebraically closed field in which `N` is invertible,
the `N`-torsion of the geometric point group is `(ℤ/N)²`.

Classical input: `HasseWeil`'s `torsion_genN_addEquiv`. Outstanding bridge (recorded
on the board): the fibrewise group dictionary between `E`'s abstract group object and
the chord–tangent group of a Weierstrass fibre model — the fibrewise instance of the
deferred Abel/canonicity comparison. -/
theorem torsion_geometricFibre_rank_two (N : ℕ) [NeZero N] (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    Nonempty (Submodule.torsionBy ℤ (E.Point t) (N : ℤ) ≃+ (Fin 2 → ZMod N)) := by
  sorry

end EllipticCurve

end ModularCurves
