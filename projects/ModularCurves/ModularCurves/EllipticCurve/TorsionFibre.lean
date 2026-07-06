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

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

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
