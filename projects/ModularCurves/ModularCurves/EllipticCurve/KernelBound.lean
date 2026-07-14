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

/-- **(UNIFICATION bridge — `endDeg` = scheme fibre rank; register-box, K4-landing pin)** Over a
field, the KM endomorphism degree `E.endDeg δ` of a finite-flat isogeny `δ` equals the
scheme-theoretic fibre rank `δ.left.finrank` at the zero point. This is the **Abel-FREE ruling**
(`decomposition-keystone.md` ④, ratified v10.212): the isogeny degree `[K(E) : δ*K(E)]` *is* the
generic-fibre rank, so `endDeg` is grounded on `Scheme.Hom.finrank` — **not** on the Abel/Pic⁰-gated
`endDual`. It is the single tracked register-box the K4 division-polynomial bridge (L4-iii) discharges:
once `endDeg` is grounded on the finrank, `modelEllipticCurve_mulByHom_finrank = N²` gives
`endDeg_mulBy = N²` and this identity becomes definitional. A new specification pin extending the
`endDeg` DATA-SORRY REGISTER (`EndomorphismDegree.lean`); `δ.left` finite/flat are the isogeny fibre
inputs (register-box BB, the same `δ ≠ 1 ⟹ isogeny` funnel). -/
theorem endDeg_eq_left_finrank (E : EllipticCurve (Spec (CommRingCat.of k)))
    (δ : E.asOver ⟶ E.asOver) [Flat δ.left] [IsFinite δ.left]
    (x₀ : ↑(Spec (CommRingCat.of k))) :
    E.endDeg δ = (δ.left.finrank (E.zero x₀) : ℤ) := sorry

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
