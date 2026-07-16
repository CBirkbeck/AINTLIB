/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.TorsionCombinationSpec
import ModularCurves.LevelStructure.Basic
import ModularCurves.ForMathlib.PairGeneratesOfCardSq
import ModularCurves.Moduli.LevelSpaceEtale

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

/-! ### Restrict-naturality of the combinations (step 1 of the four-step map) -/

omit [NeZero N] in
/-- Restriction of points is additive (companion to the migrated `restrict_sub`). -/
theorem restrict_add' {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P + Q) = Point.restrict E k P + Point.restrict E k Q := by
  apply (E.pointEquivOverHom (k ≫ g)).injective
  simp only [E.pointEquivOverHom_restrict, E.pointEquivOverHom_add, MonObj.comp_mul]

omit [NeZero N] in
/-- Restriction of points commutes with `zsmul` (carrier-level, via
`point_smul_eq_comp_mulBy`). -/
theorem restrict_zsmul' {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (n : ℤ)
    (P : E.Point g) :
    Point.restrict E k (n • P) = n • Point.restrict E k P := by
  refine Subtype.ext ?_
  show k ≫ ((n • P : E.Point g) : T ⟶ E.E)
      = ((n • Point.restrict E k P : E.Point (k ≫ g)) : T' ⟶ E.E)
  rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy, ← Category.assoc]
  rfl

/-- The combination point restricts to the combination of the restrictions. -/
theorem restrict_combinationPoint {T' : Scheme.{u}} (u : T' ⟶ E.torsionPair N)
    (v : ZMod N × ZMod N) :
    Point.restrict E u (E.combinationPoint N v)
      = (v.1.val : ℤ) • Point.restrict E u (E.torsionPairFst N)
        + (v.2.val : ℤ) • Point.restrict E u (E.torsionPairSnd N) := by
  rw [combinationPoint, restrict_add', restrict_zsmul', restrict_zsmul']

omit [NeZero N] in
/-- A point is zero iff its carrier is the zero-section composite (carrier-level zero
test; `Subtype.ext_iff` + `point_zero_val`). -/
theorem point_eq_zero_iff_coe {T : Scheme.{u}} {g : T ⟶ S} (P : E.Point g) :
    P = 0 ↔ (P : T ⟶ E.E) = g ≫ E.zero := by
  rw [Subtype.ext_iff, E.point_zero_val]

/-! ### The pulled-combination zero test (Spec of a field) -/

variable {k : Type u} [Field k]

/-- **The pulled-combination zero test.** For a pair `(a, b)` of `T`-points of `E[N]`
over `g` and a field-valued point `τ` of `T`, the `v`-combination morphism hits the
zero section at `τ` iff the `v`-combination of the pulled torsion points vanishes. -/
theorem comp_combination_mem_zeroSection_iff (h : NIsInvertible S N)
    (a b : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g) (hb : b ≫ E.torsionπ N = g)
    (τ : Spec (CommRingCat.of k) ⟶ T) (pt : ↥(Spec (CommRingCat.of k)))
    (v : ZMod N × ZMod N) :
    (τ ≫ pullback.lift a b (ha.trans hb.symm) ≫ E.combinationHom N v).base pt ∈
        Set.range (E.torsionZero N).base ↔
      (v.1.val : ℤ) • (⟨τ ≫ a ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ : E.Point (τ ≫ g))
        + (v.2.val : ℤ) • (⟨τ ≫ b ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, hb]⟩ : E.Point (τ ≫ g))
        = 0 := by
  set w : T ⟶ E.torsionPair N := pullback.lift a b (ha.trans hb.symm) with hw
  have hwπ : w ≫ E.torsionPairπ N = g := by
    rw [hw]
    show pullback.lift a b _ ≫ pullback.fst _ _ ≫ E.torsionπ N = g
    rw [← Category.assoc, pullback.lift_fst, ha]
  -- the restricted combination point at base `(τ ≫ w) ≫ torsionPairπ`
  set p : E.Point ((τ ≫ w) ≫ E.torsionPairπ N) :=
    Point.restrict E (τ ≫ w) (E.combinationPoint N v) with hp
  have hbase : (τ ≫ w) ≫ E.torsionPairπ N = τ ≫ g := by
    rw [Category.assoc, hwπ]
  -- carrier of the transported combination = combination of the pulled points
  have hcongr : Point.congrBase E hbase p
      = (v.1.val : ℤ) • (⟨τ ≫ a ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ : E.Point (τ ≫ g))
        + (v.2.val : ℤ) • (⟨τ ≫ b ≫ E.torsionι N, by
          rw [Category.assoc, Category.assoc, E.torsionι_π, hb]⟩ : E.Point (τ ≫ g)) := by
    rw [hp, restrict_combinationPoint, map_add, map_zsmul, map_zsmul]
    congr 1
    · congr 1
      refine Subtype.ext ?_
      rw [Point.congrBase_apply_coe]
      show (τ ≫ w) ≫ (pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N)
          = τ ≫ a ≫ E.torsionι N
      rw [← Category.assoc (τ ≫ w), Category.assoc τ w, hw, pullback.lift_fst,
        Category.assoc]
    · congr 1
      refine Subtype.ext ?_
      rw [Point.congrBase_apply_coe]
      show (τ ≫ w) ≫ (pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N)
          = τ ≫ b ≫ E.torsionι N
      rw [← Category.assoc (τ ≫ w), Category.assoc τ w, hw, pullback.lift_snd,
        Category.assoc]
  -- morphism-level data for `u := τ ≫ w ≫ c_v`
  have hz1 : E.torsionZero N ≫ E.torsionι N = E.zero := by
    rw [E.torsionZero_torsionι N, E.point_zero_val, Category.id_comp]
  have hcarrier : (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionι N = ((p : _ ⟶ E.E)) := by
    rw [Category.assoc, Category.assoc, E.combinationHom_torsionι]
    rfl
  have hbase' : (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N
      = (τ ≫ w) ≫ E.torsionPairπ N := by
    rw [Category.assoc, Category.assoc, E.combinationHom_torsionπ, ← Category.assoc]
  -- assemble: detection ∘ hom_ext-split ∘ carrier zero-test ∘ congrBase transport
  have hcz : Point.congrBase E hbase p = 0 ↔ p = 0 :=
    ⟨fun h0 => (Point.congrBase E hbase).injective (h0.trans (map_zero _).symm),
      fun h0 => by rw [h0, map_zero]⟩
  refine (E.comp_torsion_mem_zeroSection_iff N h
    (τ ≫ w ≫ E.combinationHom N v) pt).trans
    (Iff.trans ?_ (hcz.symm.trans (by rw [hcongr])))
  -- remaining: (u = (u ≫ π) ≫ z) ↔ p = 0
  rw [point_eq_zero_iff_coe]
  constructor
  · intro heq
    calc (p : _ ⟶ E.E)
        = (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionι N := hcarrier.symm
      _ = (((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionι N := congrArg (· ≫ E.torsionι N) heq
      _ = ((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.zero := by
          rw [Category.assoc, hz1]
      _ = ((τ ≫ w) ≫ E.torsionPairπ N) ≫ E.zero := congrArg (· ≫ E.zero) hbase'
  · intro heq
    apply pullback.hom_ext
    · show (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionι N
        = (((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionι N
      calc (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionι N
          = (p : _ ⟶ E.E) := hcarrier
        _ = ((τ ≫ w) ≫ E.torsionPairπ N) ≫ E.zero := heq
        _ = ((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.zero :=
            (congrArg (· ≫ E.zero) hbase').symm
        _ = (((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
            E.torsionι N := by
            rw [Category.assoc ((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N)
              (E.torsionZero N) (E.torsionι N), hz1]
    · show (τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N
        = (((τ ≫ w ≫ E.combinationHom N v) ≫ E.torsionπ N) ≫ E.torsionZero N) ≫
          E.torsionπ N
      exact ((Category.assoc _ _ _).trans (by
        rw [E.torsionZero_torsionπ N, Category.comp_id])).symm

end EllipticCurve

end ModularCurves
