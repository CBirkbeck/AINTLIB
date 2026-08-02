/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.NaiveGammaOneLocus
import ModularCurves.LevelStructure.CombinationLevel

/-!
# The naive `Γ₁(N)` locus classifies naive `Γ₁(N)`-structures (WP-D1c-coarse)

The one-generator mirror of `LevelStructure/CombinationLevel.lean`. That file shows the
full-level locus classifies naive full level structures; this one does the same for the
naive `Γ₁(N)` locus of `GroupScheme/NaiveGammaOneLocus.lean`, which is what
`gammaOneNaiveProblem` needs.

Two of the ingredients are already single-generator in `CombinationLevel` and are reused
verbatim: `comp_torsion_mem_zeroSection_iff` (the zero test on `E[N]` itself) and
`torsionMapSection` (a `T`-point of `E[N]` over `g` as a section of `E ×_S T`). What has to
be mirrored is the *multiple* zero test, and it is strictly simpler than the combination
one — with a single generator the `pullback.lift` plumbing and the `torsionPair` detour both
disappear.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]
  {T : Scheme.{u}} {g : T ⟶ S}

/-- The multiple point restricts to the multiple of the restriction. -/
theorem restrict_multiplePoint {T' : Scheme.{u}} (u : T' ⟶ E.torsion N) (m : ℕ) :
    Point.restrict E u (E.multiplePoint N m)
      = (m : ℤ) • Point.restrict E u (E.torsionTaut N) := by
  rw [multiplePoint, restrict_zsmul']

variable {k : Type u} [Field k]

/-- **The pulled-multiple zero test.** For a `T`-point `a` of `E[N]` over `g` and a
field-valued point `τ` of `T`, the `m`-multiple morphism hits the zero section at `τ` iff
the `m`-multiple of the pulled torsion point vanishes.

The single-generator mirror of `comp_combination_mem_zeroSection_iff`. -/
theorem comp_multiple_mem_zeroSection_iff (h : NIsInvertible S N)
    (a : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g)
    (τ : Spec (CommRingCat.of k) ⟶ T) (pt : ↥(Spec (CommRingCat.of k))) (m : ℕ) :
    (τ ≫ a ≫ E.multipleHom N m).base pt ∈ Set.range (E.torsionZero N).base ↔
      (m : ℤ) • (⟨τ ≫ a ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ : E.Point (τ ≫ g))
        = 0 := by
  set p : E.Point ((τ ≫ a) ≫ E.torsionπ N) :=
    Point.restrict E (τ ≫ a) (E.multiplePoint N m) with hp
  have hbase : (τ ≫ a) ≫ E.torsionπ N = τ ≫ g := by
    rw [Category.assoc, ha]
  have hcongr : Point.congrBase E hbase p
      = (m : ℤ) • (⟨τ ≫ a ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ : E.Point (τ ≫ g)) := by
    rw [hp, restrict_multiplePoint, map_zsmul]
    congr 1
    refine Subtype.ext ?_
    rw [Point.congrBase_apply_coe]
    show (τ ≫ a) ≫ E.torsionι N = τ ≫ a ≫ E.torsionι N
    rw [Category.assoc]
  have hz1 : E.torsionZero N ≫ E.torsionι N = E.zero := by
    rw [E.torsionZero_torsionι N, E.point_zero_val, Category.id_comp]
  have hcarrier : (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionι N = ((p : _ ⟶ E.E)) := by
    rw [Category.assoc, Category.assoc, E.multipleHom_torsionι]
    rfl
  have hbase' : (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N
      = (τ ≫ a) ≫ E.torsionπ N := by
    rw [Category.assoc, Category.assoc, E.multipleHom_torsionπ, ← Category.assoc]
  have hcz : Point.congrBase E hbase p = 0 ↔ p = 0 :=
    ⟨fun h0 => (Point.congrBase E hbase).injective (h0.trans (map_zero _).symm),
      fun h0 => by rw [h0, map_zero]⟩
  refine (E.comp_torsion_mem_zeroSection_iff N h
    (τ ≫ a ≫ E.multipleHom N m) pt).trans
    (Iff.trans ?_ (hcz.symm.trans (by rw [hcongr])))
  rw [point_eq_zero_iff_coe]
  constructor
  · intro heq
    calc (p : _ ⟶ E.E)
        = (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionι N := hcarrier.symm
      _ = (((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionι N := congrArg (· ≫ E.torsionι N) heq
      _ = ((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.zero := by
          rw [Category.assoc, hz1]
      _ = ((τ ≫ a) ≫ E.torsionπ N) ≫ E.zero := congrArg (· ≫ E.zero) hbase'
  · intro heq
    apply pullback.hom_ext
    · show (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionι N
        = (((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionι N
      calc (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionι N
          = (p : _ ⟶ E.E) := hcarrier
        _ = ((τ ≫ a) ≫ E.torsionπ N) ≫ E.zero := heq
        _ = ((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.zero :=
            (congrArg (· ≫ E.zero) hbase').symm
        _ = (((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
            E.torsionι N := by
            rw [Category.assoc ((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N)
              (E.torsionZero N) (E.torsionι N), hz1]
    · show (τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N
        = (((τ ≫ a ≫ E.multipleHom N m) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionπ N
      exact ((Category.assoc _ _ _).trans (by
        rw [E.torsionZero_torsionπ N, Category.comp_id])).symm

end EllipticCurve

end ModularCurves
