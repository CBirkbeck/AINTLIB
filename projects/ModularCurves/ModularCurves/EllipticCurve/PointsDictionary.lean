import ModularCurves.Moduli.WeierstrassAtlas

/-!
# The field-points dictionary and the field-points extensionality principle

**(T-W7 skeleton, lane P2 — `/develop --decompose` 2026-07-07.)** The canonical form of the
(already-proven) pointed field-points dictionary `projModel_points`, the reducedness of the
universal atlas products, and the workhorse extensionality principle: two morphisms out of a
reduced scheme into a separated scheme that agree on composition with every field-valued
point are equal. Together these reduce every group axiom over the universal atlas to
mathlib's `WeierstrassCurve.Affine.Point.instAddCommGroup` over fields — the design
simplification recorded in `decomposition.md` (supersedes the generic-point-only route;
audit A5).

Sources: reviewer round 1 §Q4; audit A5; `projModel_points` (project, PROVEN).
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- **(T-W7.0f-i)** The canonical pointed field-points dictionary: `K`-points of the
projective model over `Spec R` biject with mathlib's nonsingular affine points over `K`.
Canonical (choice-extracted) form of the proven `projModel_points`. Source: project
`projModel_points` (WeierstrassModel.lean, T-A2e, PROVEN). -/
noncomputable def projModelPointsEquiv (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] :
    SpecPoints (projModel W) (projModelπ W) K ≃ (W.baseChange K).toAffine.Point :=
  sorry

/-- **(T-W7.0f-ii)** The dictionary is pointed: the point at infinity corresponds to `0`.
Source: `projModel_points` (its pointedness clause). -/
theorem projModelPointsEquiv_zero (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K] :
    projModelPointsEquiv W K
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ projModelZero W, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ = 0 := by
  sorry

/-- **(T-W7.0g-ext)** The field-points extensionality principle: two morphisms from a
*reduced* scheme to a *separated* scheme agreeing on composition with every field-valued
point are equal. Every point of `X` is hit by its residue-field point, so the (closed, by
separatedness) equalizer is topologically all of `X`; reducedness upgrades this to a scheme
equality. Valid tool ONLY over the reduced universal atlas — the general-`S` axioms are
obtained by base change of the universal identities, never by this principle. Source:
audit A5 (simplification of `ext_of_isDominant`-at-the-generic-point). -/
theorem hom_ext_of_forall_specPoint {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    {f g : X ⟶ Y}
    (h : ∀ (K : Type u) [Field K] (p : Spec (CommRingCat.of K) ⟶ X), p ≫ f = p ≫ g) :
    f = g := by
  sorry

/-- **(T-W7.0e-engine)** Smooth (of some relative dimension) over a reduced base implies
reduced: smooth morphisms are flat with regular (hence reduced) fibres, and flatness over a
reduced base with reduced fibres gives a reduced total space. Mathlib-availability to be
re-checked at implementation (Step 4); stated here as the project leaf. Source: reviewer
round 1 §Q4 ("smooth over integral base with geometrically integral fibres", reducedness
half); EGA IV 17.5.7-adjacent. -/
theorem isReduced_of_smoothOfRelativeDimension {X S : Scheme.{u}} {n : ℕ} {f : X ⟶ S}
    (hf : SmoothOfRelativeDimension n f) [IsReduced S] : IsReduced X := by
  sorry

instance : IsReduced weierstrassAtlas := by
  sorry

/-- **(T-W7.0e-i)** The universal curve is reduced (smooth of relative dimension 1 over the
reduced — indeed integral — atlas). -/
instance : IsReduced universalCurve := by
  sorry

/-- **(T-W7.0e-ii)** The fibre square of the universal curve is reduced. -/
instance : IsReduced (pullback universalCurveπ universalCurveπ) := by
  sorry

/-- **(T-W7.0e-iii)** The fibre cube of the universal curve is reduced (spelling: the triple
product as a fibre product of `E ×_U E → U` with `E → U`). -/
instance : IsReduced
    (pullback (pullback.fst universalCurveπ universalCurveπ ≫ universalCurveπ)
      universalCurveπ) := by
  sorry

end ModularCurves
