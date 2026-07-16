/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TorsionCombinationSpec
import ModularCurves.LevelStructure.Basic
import ModularCurves.ForMathlib.PairGeneratesOfCardSq

/-!
# The combination locus classifies naive full level structures

The bridge between the geometry (`fullLevelLocus`, a clopen of `E[N] ×_S E[N]`) and
the moduli datum (`IsNaiveFullLevel`): for prime `N` invertible on `S`, a pair of
`T`-points of `E[N]` over `g` lands in the full-level set **iff** the corresponding
pair of sections of `E ×_S T` is a naive full level-`N` structure.

Ingredients:
* single-point zero-detection (`comp_torsion_eq_zero_iff`): a `Spec k`-point of `E[N]`
  meets the zero section topologically iff it *is* the zero point (`Spec` of a field
  has one point, so the open zero-locus factors the morphism);
* the fibre count: `torsion_geometricFibre_rank_two` (`#E[N](k̄) = N²`, axiom-clean);
* the combination criterion `addSubgroup_closure_pair_eq_top_iff`
  (`PairGeneratesOfCardSq`, AX2-e).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### Single-point zero-detection -/

private theorem subsingleton_spec_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  ⟨fun a b => PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
    (Ideal.eq_bot_of_prime _).symm)⟩

/-- A `Spec k`-valued point of `E[N]` meets the zero section topologically iff it is
the zero point: `Spec k` is a single point, so topological membership makes the whole
morphism factor through the (open) zero section. -/
theorem comp_torsion_mem_zeroSection_iff (h : NIsInvertible S N)
    {k : Type u} [Field k] (u : Spec (CommRingCat.of k) ⟶ E.torsion N)
    (pt : ↥(Spec (CommRingCat.of k))) :
    u.base pt ∈ Set.range (E.torsionZero N).base ↔
      u = (u ≫ E.torsionπ N) ≫ E.torsionZero N := by
  haveI := subsingleton_spec_field k
  constructor
  · intro hmem
    haveI := E.torsionZero_isOpenImmersion N h
    have hrange : Set.range u.base ⊆ Set.range (E.torsionZero N).base := by
      rintro x ⟨q, rfl⟩
      rw [Subsingleton.elim q pt]
      exact hmem
    have hfac : IsOpenImmersion.lift (E.torsionZero N) u hrange ≫
        E.torsionZero N = u := IsOpenImmersion.lift_fac _ _ _
    have hd : IsOpenImmersion.lift (E.torsionZero N) u hrange
        = u ≫ E.torsionπ N := by
      conv_lhs => rw [← Category.comp_id
        (IsOpenImmersion.lift (E.torsionZero N) u hrange)]
      rw [← torsionZero_torsionπ (E := E) (N := N), ← Category.assoc, hfac]
    calc u = IsOpenImmersion.lift (E.torsionZero N) u hrange ≫ E.torsionZero N :=
        hfac.symm
      _ = (u ≫ E.torsionπ N) ≫ E.torsionZero N := by rw [hd]
  · intro heq
    refine ⟨(u ≫ E.torsionπ N).base pt, ?_⟩
    conv_rhs => rw [heq]
    simp

/-! ### The tautological pair of a lifted pair -/

variable {T : Scheme.{u}} (g : T ⟶ S)

/-- The section of `E ×_S T` attached to a `T`-point of `E[N]` over `g`. -/
noncomputable def torsionMapSection (a : T ⟶ E.torsion N)
    (ha : a ≫ E.torsionπ N = g) : (E.baseChange g).Section :=
  ⟨pullback.lift (a ≫ E.torsionι N) (𝟙 T)
      (by rw [Category.assoc, E.torsionι_π, ha, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem torsionMapSection_fst (a : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g) :
    ((E.torsionMapSection N g a ha : (E.baseChange g).Point (𝟙 T)) :
      T ⟶ (E.baseChange g).E) ≫ pullback.fst E.π g = a ≫ E.torsionι N :=
  pullback.lift_fst _ _ _

/-- The section attached to a torsion map is `N`-killed. -/
theorem torsionMapSection_killed (a : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g) :
    (N : ℤ) • E.torsionMapSection N g a ha = 0 := by
  apply (Point.baseChangeEquiv E g (𝟙 T)).injective
  rw [map_zsmul, map_zero, E.smul_eq_zero_iff_comp_mulByHom,
    Point.baseChangeEquiv_apply_coe, E.torsionMapSection_fst N g a ha,
    Category.assoc,
    show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
      pullback.condition,
    ← Category.assoc, ha, Category.id_comp]

end EllipticCurve

end ModularCurves
