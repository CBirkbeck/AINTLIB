/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.ClosurePairCard
import ModularCurves.LevelStructure.Basic

/-!
# A naive full level-`N` structure forgets to a naive `Γ₁(N)`-structure (WP-D1a)

The level-forgetting map `(P, Q) ↦ P` is the first step of the route that closes the
sorry'd smoothness of `Y(N)`: `Y₁(N)` is already known to be smooth and affine
(`gammaOneNaive_representable`, axiom-verified), so a finite étale `Y(N) ⟶ Y₁(N)` would
transport it.

The map is **not definitional**. `IsNaiveFullLevel N P Q` only says that `P` and `Q`
*generate* the `N`-torsion at every geometric point, while `IsNaiveGammaOne N P` demands
that `P` have *exact order* `N` there. The bridge is a counting argument, split into

* the group theory — `ForMathlib/ClosurePairCard.lean`: two generators of an `N²`-element
  torsion group cannot have order `< N`, since an element of order `d` confines the whole
  subgroup to `d · N` elements;
* the geometry — `torsion_geometricFibre_rank_two` (T-B6): the `N`-torsion of the geometric
  point group is `(ℤ/N)²`, hence has exactly `N²` elements.

Both halves are axiom-verified, so this file is too.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The `N`-torsion of a geometric point group has exactly `N²` elements. The `Set.ncard`
repackaging of `torsion_geometricFibre_rank_two`, which is the shape the counting lemma
`smul_ne_zero_of_closure_pair_of_ncard` consumes. -/
theorem ncard_torsion_geometricFibre (N : ℕ) [NeZero N] (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S) (hN : (N : k) ≠ 0) :
    {x : E.Point t | (N : ℤ) • x = 0}.ncard = N * N := by
  obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k t hN
  have hset : {x : E.Point t | (N : ℤ) • x = 0} =
      (Submodule.torsionBy ℤ (E.Point t) (N : ℤ) : Set (E.Point t)) := by
    ext x
    exact (Submodule.mem_torsionBy_iff _ _).symm
  rw [hset]
  show Nat.card (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) = N * N
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Nat.card_zmod, Fintype.card_fin, sq]

/-- **(WP-D1a)** The level-forgetting map on level structures: the first member of a naive
full level-`N` structure is a naive `Γ₁(N)`-structure.

This is the content of the moduli-problem morphism `Γ(N) ⟶ Γ₁(N)`, whose induced map on
representing objects is (WP-D1c) finite étale, transporting `Y₁(N)`'s known smoothness to
`Y(N)`. -/
theorem isNaiveGammaOne_of_isNaiveFullLevel {N : ℕ} [NeZero N] {P Q : E.Section}
    (hinv : ∀ (k : Type u) [Field k] [IsAlgClosed k],
      (Spec (CommRingCat.of k) ⟶ S) → (N : k) ≠ 0)
    (h : E.IsNaiveFullLevel N P Q) : E.IsNaiveGammaOne N P := by
  refine ⟨h.1.1, fun k _ _ t => ⟨?_, fun a ha haN => ?_⟩⟩
  · rw [← Point.pull_zsmul, h.1.1, Point.pull_zero]
  · refine smul_ne_zero_of_closure_pair_of_ncard (Nat.pos_of_ne_zero (NeZero.ne N))
      (Q := Point.pull E t Q) ?_ (h.2 k t)
      (E.ncard_torsion_geometricFibre N k t (hinv k t)) ha haN
    rw [← Point.pull_zsmul, h.1.2, Point.pull_zero]

/-- **(WP-D1a)** The symmetric statement for the second member: `Q` is a naive
`Γ₁(N)`-structure too. Same counting argument with the roles of the generators swapped —
`AddSubgroup.closure` of a pair is symmetric. -/
theorem isNaiveGammaOne_snd_of_isNaiveFullLevel {N : ℕ} [NeZero N] {P Q : E.Section}
    (hinv : ∀ (k : Type u) [Field k] [IsAlgClosed k],
      (Spec (CommRingCat.of k) ⟶ S) → (N : k) ≠ 0)
    (h : E.IsNaiveFullLevel N P Q) : E.IsNaiveGammaOne N Q := by
  refine ⟨h.1.2, fun k _ _ t => ⟨?_, fun a ha haN => ?_⟩⟩
  · rw [← Point.pull_zsmul, h.1.2, Point.pull_zero]
  · refine smul_ne_zero_of_closure_pair_of_ncard (Nat.pos_of_ne_zero (NeZero.ne N))
      (Q := Point.pull E t P) ?_ (fun x hx => ?_)
      (E.ncard_torsion_geometricFibre N k t (hinv k t)) ha haN
    · rw [← Point.pull_zsmul, h.1.1, Point.pull_zero]
    · have := h.2 k t x hx
      rwa [Set.pair_comm (Point.pull E t P) (Point.pull E t Q)] at this

/-! ## Bridge to the Drinfeld notion

`Section.hasExactOrder_iff_geometric` (T-D6 = KM 1.4.4 (1)⟺(3)) has *exactly* the shape of
`IsNaiveGammaOne`'s second component, so the naive and Drinfeld notions differ only by the
global killing clause. That makes the level-forgetting map land in the exact-order locus
(`exists_exactOrderLocus`), which is what WP-D1c-rel needs.

**Dependency note.** The `mpr` direction of `hasExactOrder_iff_geometric` routes through
`Section.hasExactOrder_of_geometric`, which is a `sorry` (register box T-D6,
`LevelStructure/ExactOrder.lean:916`). So the two theorems below inherit `sorryAx` — they are
correct reductions, not closures, and T-D6 is the single named obligation they expose. -/

/-- The naive `Γ₁(N)`-condition is the Drinfeld one, given `N` invertible.
Depends on register box T-D6 (`Section.hasExactOrder_of_geometric`). -/
theorem hasExactOrder_of_isNaiveGammaOne {N : ℕ} [NeZero N] (hN : NIsInvertible S N)
    {P : E.Section} (h : E.IsNaiveGammaOne N P) : P.HasExactOrder E N :=
  (Section.hasExactOrder_iff_geometric E hN h.1).mpr h.2

/-- **(WP-D1c-rel, step 1)** The first member of a naive full level-`N` structure has exact
order `N` in the Drinfeld sense — the hypothesis `exists_exactOrderLocus`'s universal
property consumes, so the level-forgetting map factors through the exact-order locus.
Depends on register box T-D6. -/
theorem hasExactOrder_fst_of_isNaiveFullLevel {N : ℕ} [NeZero N] (hN : NIsInvertible S N)
    {P Q : E.Section}
    (hinv : ∀ (k : Type u) [Field k] [IsAlgClosed k],
      (Spec (CommRingCat.of k) ⟶ S) → (N : k) ≠ 0)
    (h : E.IsNaiveFullLevel N P Q) : P.HasExactOrder E N :=
  E.hasExactOrder_of_isNaiveGammaOne hN (E.isNaiveGammaOne_of_isNaiveFullLevel hinv h)

end EllipticCurve

end ModularCurves
