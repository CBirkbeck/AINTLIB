/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.EtaleSectionsCount
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.EllipticCurve.EndomorphismDegree

/-!
# The isogeny kernel bound `|ker δ| ≤ deg δ` ([KEY-KER], STREAM-GH input to KM 2.7.2)

An endomorphism `δ` of `E / Spec k` that kills `N` **distinct** points (each `pts i` with
`δ (pts i) = 0`) has scheme-theoretic degree `≥ N`: the killed points inject into the fibre of
`δ.left` over the zero point, and the number of `k`-rational points of a finite-flat fibre is at
most its rank (`card_le_finrank_of_injective_liftings`). This is the Abel-free / register-box route
to the kernel bound: it goes through the scheme fibre rank `δ.left.finrank 0`, never through the dual
isogeny, and tolerates an inseparable `δ`.

`STREAM-GH` consumes `le_finrank_of_killed_injective` and identifies `δ.left.finrank (zero point)`
with `E.endDeg δ` (the endDeg-via-K4-scheme-finrank ruling) to obtain `(N : ℤ) ≤ E.endDeg δ`.
The finiteness/flatness of `δ.left` are the isogeny fibre inputs, taken as instance hypotheses.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

-- v4.33 bump: neither the category instances nor the semireducible component types are
-- transparent enough for the rewrites and instance searches below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace ModularCurves

namespace EllipticCurve

variable {k : Type u} [Field k]

/-- **([KEY-KER], finrank form)** If a finite-flat endomorphism `δ` of `E / Spec k` kills `N`
pairwise-distinct points, then `N ≤ δ.left.finrank 0` (the scheme fibre rank of `δ` at the zero
point). The killed points `pts i` are exactly the liftings of the zero section through `δ.left`
(read off from `hkill` by taking `.left`), and there are at most `finrank`-many such `k`-points
(`card_le_finrank_of_injective_liftings`). -/
theorem le_finrank_of_killed_injective
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ)
    (δ : E.asOver ⟶ E.asOver) [Flat δ.left] [IsFinite δ.left]
    (pts : Fin N → E.Point (𝟙 (Spec (CommRingCat.of k))))
    (hinj : Function.Injective pts)
    (hkill : ∀ i, (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) (pts i) ≫ δ = 1)
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    N ≤ δ.left.finrank (E.zero x₀) := by
  have key : ∀ i, ((pts i : Spec (CommRingCat.of k) ⟶ E.E)) ≫ δ.left = E.zero := by
    intro i
    have h := congrArg (·.left) (hkill i)
    simp only [Over.comp_left] at h
    have hleft : ((E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) (pts i)).left
        = (pts i : Spec (CommRingCat.of k) ⟶ E.E) := rfl
    have hone : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ E.asOver).left = E.zero := by
      have hz1 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ E.asOver).left
          = 𝟙 (Spec (CommRingCat.of k)) ≫ E.zero := by
        rw [Hom.one_def, Over.comp_left, E.one_eq_zero]
        have hw : (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k))))).left ≫
            (𝟙_ (Over (Spec (CommRingCat.of k)))).hom = 𝟙 (Spec (CommRingCat.of k)) :=
          Over.w (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun m ↦ m ≫ E.zero) hw)
      rw [hz1, Category.id_comp]
    rw [hleft, hone] at h
    exact h
  refine card_le_finrank_of_injective_liftings δ.left E.zero x₀ N
    (fun i => ⟨(pts i : Spec (CommRingCat.of k) ⟶ E.E), key i⟩) ?_
  intro i j hij
  have hval : (pts i : Spec (CommRingCat.of k) ⟶ E.E)
      = (pts j : Spec (CommRingCat.of k) ⟶ E.E) := congrArg (·.1) hij
  exact hinj (Subtype.ext hval)

/-- **(UNIFICATION bridge — `endDeg` = scheme fibre rank; PROVEN by construction)** Over a field,
the KM endomorphism degree `E.endDeg δ` of a finite-flat isogeny `δ` equals the scheme-theoretic
fibre rank `δ.left.finrank` at the zero point. This is the **Abel-FREE ruling**
(`decomposition-keystone.md` ④, ratified v10.212), now *definitional*: the v10.250 foundation spine
constructs `endDeg` as exactly this fibre rank at the zero-section basepoint, and over a field the
base has a **unique** point (`Unique (PrimeSpectrum k)`), so the chosen basepoint is `x₀`. The
`[Flat]`/`[IsFinite]` instances record the isogeny fibre semantics (the rank is then the honest
constant fibre degree); the identity itself no longer needs them. -/
theorem endDeg_eq_left_finrank (E : EllipticCurve (Spec (CommRingCat.of k)))
    (δ : E.asOver ⟶ E.asOver) [Flat δ.left] [IsFinite δ.left]
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    E.endDeg δ = (δ.left.finrank (E.zero x₀) : ℤ) := by
  haveI hne : Nonempty ↑(Spec (CommRingCat.of k)) := ⟨x₀⟩
  haveI : Subsingleton ↑(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpt : (hne.some : ↑(Spec (CommRingCat.of k))) = x₀ := Subsingleton.elim _ _
  simp only [EllipticCurve.endDeg, dif_pos hne, hpt]

/-- **([KEY-KER], `endDeg` form — GH's `hH` second consumer, v10.219)** If a finite-flat endomorphism
`δ ≠ 1` of `E / Spec k` kills `N` pairwise-distinct points, then `(N : ℤ) ≤ E.endDeg δ`. This is the
Abel-free kernel bound in `endDeg` language: the finrank kernel bound `le_finrank_of_killed_injective`
(`N ≤ δ.left.finrank 0`, no Abel, no dual isogeny) composed with the UNIFICATION bridge
`endDeg_eq_left_finrank` (`endDeg δ = δ.left.finrank 0`). GH's general-`H` rigidity `hH` pin
(`gammaH_rigid_of_orderOf`) consumes it against the CM-unit degree bound `E.endDeg (ε − 1) ≤ 4`
(step (b), the `endDeg` quadratic form) to force `N ≤ 4`, contradicting exact order `N ≥ 5`. The
`endDeg`-vs-finrank bridge is the single register-box (K4 L4-iii landing); everything else is
sorry-free. -/
theorem le_endDeg_of_killed_injective
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N]
    (δ : E.asOver ⟶ E.asOver) [Flat δ.left] [IsFinite δ.left]
    (pts : Fin N → E.Point (𝟙 (Spec (CommRingCat.of k))))
    (hinj : Function.Injective pts)
    (hkill : ∀ i, (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) (pts i) ≫ δ = 1)
    (_hδ : δ ≠ 1) (x₀ : ↑(Spec (CommRingCat.of k))) :
    (N : ℤ) ≤ E.endDeg δ := by
  rw [endDeg_eq_left_finrank E δ x₀]
  exact_mod_cast le_finrank_of_killed_injective E N δ pts hinj hkill x₀

end EllipticCurve

end ModularCurves
