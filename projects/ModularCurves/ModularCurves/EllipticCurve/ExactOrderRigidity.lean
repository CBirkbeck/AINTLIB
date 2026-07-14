/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.EndomorphismDegree

/-!
# [RIG-2] The level-agnostic orbit-freeness core (KM 2.7.3/2.7.4)

**`Aut(E) acts freely on points of exact order `N`** — the Serre-style rigidity core
that BOTH the Γ₁ and Γ_H rigidity instantiations of the shared bridge
`ModuliProblem.QuotientProblemData.rigid_of_geom_free` (`Moduli/GammaHMaster.lean`)
consume. The full-level (`Γ(N)`, `N ≥ 3`) companion is
`EllipticCurve.aut_endo_eq_one` (`EndomorphismDegree.lean`); this file is the
**single-point** (`Γ₁`-flavoured) version, stated level-agnostically over any base.

The point `P` enters through the *naive* order predicate — `a • P ≠ 0` for
`0 < a < N` — which over a geometric point is exactly KM 1.4.4's characterisation of
Drinfeld exact order (`Section.hasExactOrder_iff_geometric` / the T-D6b register box
bridge from `Section.HasExactOrder`); keeping the hypothesis in this raw form makes
the core independent of the Cartier-divisor apparatus.

The arithmetic input is the single **KM-keystone pin** `hbound` (STREAM-KM's
endomorphism-degree charter; handshake v10.193-GH, Q2 ruled **Abel-FREE** v10.212):
*a nonzero difference endomorphism cannot kill `N` pairwise-distinct sections*. The
pin is stated with NO degree carrier at all, so KM discharges it through the
Abel-free fibre/finrank quantities (kernel size ≤ scheme `finrank`, `finrank(ε−1) < N`
— the `mulByHom_finrank` family), never through the Abel/Pic⁰-gated `endDual`/`endDeg`
data. Numerically: `#ker(ε−1) ≤ deg(ε−1) = 2 − tr ε ≤ 4`, with `= 4` only for
`ε = [-1]` — so the pin holds for `N ≥ 5` outright and for `N = 4` after excluding
`[-1]` (whose fixed points die on `2 • P = 0` against `hord`).

What is proved HERE (sorry-free, axiom-clean): the whole group-object plumbing — the
difference endomorphism `δ = ε * 𝟙⁻¹` (Hom.commGroup spelling of `ε − 1`) is pointed,
kills the entire cyclic subgroup `⟨P⟩` as soon as `ε` fixes `P`, and `⟨P⟩` has `N`
distinct members; so the pin forces `δ = 0`, i.e. `ε = 𝟙`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- The unit of the pointwise hom-group into `E.asOver` is the zero section. -/
theorem eta_eq_one : η[E.asOver] = (1 : 𝟙_ (Over S) ⟶ E.asOver) := by
  rw [Hom.one_def]; simp

/-- The difference `ε * 𝟙⁻¹` (the `Hom.commGroup` spelling of `ε − 1`) of a **pointed**
endomorphism is pointed. -/
theorem sub_one_pointed (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver]) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    η[E.asOver] ≫ (ε * (𝟙 E.asOver)⁻¹) = η[E.asOver] := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, hη, E.eta_eq_one, _root_.inv_one, _root_.mul_one]

/-- If `ε` fixes the point `P`, then the difference endomorphism `ε * 𝟙⁻¹` kills `P`
(sends it to the group unit of the point group). -/
theorem comp_sub_one_eq_one_of_fix (ε : E.asOver ⟶ E.asOver) (P : E.Point (𝟙 S))
    (hfix : (E.pointEquivOverHom (𝟙 S)) P ≫ ε = (E.pointEquivOverHom (𝟙 S)) P) :
    letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
    letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom (𝟙 S)) P ≫ (ε * (𝟙 E.asOver)⁻¹) = 1 := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
  rw [MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, hfix, _root_.mul_inv_cancel]

/-- **[RIG-2] CORE (level-agnostic orbit-freeness; KM 2.7.3/2.7.4 shape)** — a pointed
endomorphism `ε` of `E/S` fixing a point `P` whose first `N − 1` multiples are nonzero
is the identity, GIVEN the (degree-carrier-free, Abel-free) KM-keystone pin `hbound`:
*the nonzero difference `δ = ε * 𝟙⁻¹` cannot kill `N` pairwise-distinct sections*.
The plumbing proved here: `δ` is pointed, hence additive (`endMonHom`), hence kills
every multiple `a • P`; those multiples are pairwise distinct by the order hypothesis;
the pin then forces `δ` to be the zero endomorphism, i.e. `ε = 𝟙`. -/
theorem aut_endo_eq_one_of_fixes_point [IsLocallyNoetherian S] (N : ℕ) [NeZero N]
    (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (P : E.Point (𝟙 S))
    (hord : ∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0)
    (hfix : (E.pointEquivOverHom (𝟙 S)) P ≫ ε = (E.pointEquivOverHom (𝟙 S)) P)
    (hbound :
      letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
      letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
      ε * (𝟙 E.asOver)⁻¹ ≠ 1 →
      ∀ pts : Fin N → E.Point (𝟙 S), Function.Injective pts →
        (∀ i, (E.pointEquivOverHom (𝟙 S)) (pts i) ≫ (ε * (𝟙 E.asOver)⁻¹) = 1) →
        False) :
    ε = 𝟙 E.asOver := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
  by_cases hδ1 : ε * (𝟙 E.asOver)⁻¹ = 1
  · exact _root_.mul_inv_eq_one.mp hδ1
  · exfalso
    -- the difference endomorphism is pointed, hence a monoid homomorphism
    have hδη : η[E.asOver] ≫ (ε * (𝟙 E.asOver)⁻¹) = η[E.asOver] := E.sub_one_pointed ε hη
    haveI : IsMonHom (ε * (𝟙 E.asOver)⁻¹) :=
      { one_hom := hδη, mul_hom := E.endMonHom (ε * (𝟙 E.asOver)⁻¹) hδη }
    -- it kills every multiple of `P`
    have hkillP : (E.pointEquivOverHom (𝟙 S)) P ≫ (ε * (𝟙 E.asOver)⁻¹) = 1 :=
      E.comp_sub_one_eq_one_of_fix ε P hfix
    have hkillA : ∀ a : ℤ,
        (E.pointEquivOverHom (𝟙 S)) (a • P) ≫ (ε * (𝟙 E.asOver)⁻¹) = 1 := by
      intro a
      have htrans : (E.pointEquivOverHom (𝟙 S)) (a • P) =
          ((E.pointEquivOverHom (𝟙 S)) P) ^ a := rfl
      have hmap := (IsMonHom.monoidHom (ε * (𝟙 E.asOver)⁻¹)
        (Over.mk (𝟙 S))).map_zpow ((E.pointEquivOverHom (𝟙 S)) P) a
      simp only [IsMonHom.monoidHom_apply] at hmap
      rw [htrans, hmap, hkillP, _root_.one_zpow]
    -- the multiples `a • P`, `a = 0, …, N−1`, are pairwise distinct
    have hinj : Function.Injective (fun i : Fin N => ((i : ℕ) : ℤ) • P) := by
      intro i j hij
      by_contra hne
      have hij' : ((i : ℕ) : ℤ) • P = ((j : ℕ) : ℤ) • P := hij
      have hsub : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) • P = 0 := by
        rw [sub_smul, hij']
        exact sub_self _
      set d : ℤ := ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) with hd
      have hd0 : d ≠ 0 := by
        intro h0
        apply hne
        have : ((i : ℕ) : ℤ) = ((j : ℕ) : ℤ) := by omega
        exact Fin.ext (by exact_mod_cast this)
      have hdlt : d.natAbs < N := by
        have hi := i.2
        have hj := j.2
        omega
      refine hord d.natAbs (Int.natAbs_pos.mpr hd0) hdlt ?_
      rcases Int.natAbs_eq d with h | h
      · rw [← h]
        exact hsub
      · have h2 : -(((d.natAbs : ℤ)) • P) = 0 := by
          rw [← neg_smul, ← h]
          exact hsub
        exact neg_eq_zero.mp h2
    exact hbound hδ1 (fun i => ((i : ℕ) : ℤ) • P) hinj (fun i => hkillA _)

end EllipticCurve

end ModularCurves
