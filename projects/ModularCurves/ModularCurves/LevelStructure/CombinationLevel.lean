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

-- v4.33 bump: the `Scheme` category instance inside these arguments is no longer
-- transparent enough for the `≫`-associativity rewrites below.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### Single-point zero-detection -/

private theorem subsingleton_spec_field (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  ⟨fun a b => by
    -- the `IsPrime` fields are no longer picked up as instances on this pin
    haveI := a.isPrime
    haveI := b.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans
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

/-! ### Closure-transport glue (step 2 of the four-step map) -/

private theorem addMonoidHom_mem_closure_image {A B : Type u} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) {s : Set A} {x : A}
    (hx : x ∈ AddSubgroup.closure s) : f x ∈ AddSubgroup.closure (f '' s) := by
  rw [← AddMonoidHom.map_closure]
  exact AddSubgroup.mem_map_of_mem f hx

private theorem injective_mem_closure_image_iff {A B : Type u} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (hf : Function.Injective f) (s : Set A) (x : A) :
    f x ∈ AddSubgroup.closure (f '' s) ↔ x ∈ AddSubgroup.closure s := by
  constructor
  · intro h
    rw [← AddMonoidHom.map_closure] at h
    obtain ⟨y, hy, hyx⟩ := AddSubgroup.mem_map.mp h
    rwa [← hf hyx]
  · exact addMonoidHom_mem_closure_image f

/-! ### The master identification (step 3): the full-level set classifies naive
full level structures -/

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in
/-- **The master iff.** For a pair `(a, b)` of `T`-points of `E[N]` over `g` (with `N`
invertible on `S`), the lifted pair-point lands in the full-level set at every point
of `T` **iff** the attached pair of sections of `E ×_S T` is a naive full level-`N`
structure. Forward: at each geometric point the set condition rules out vanishing
combinations (`comp_combination_mem_zeroSection_iff`), so the generation criterion
`pair_generates_iff_combos_ne_zero` (with the `N²`-count
`torsion_geometricFibre_rank_two`) yields the closure clause. Backward: a point of
`T` outside the set gives a vanishing nontrivial combination at the algebraic closure
of its residue field, contradicting the criterion. -/
theorem forall_mem_fullLevelSet_iff_isNaiveFullLevel (h : NIsInvertible S N)
    (a b : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g) (hb : b ≫ E.torsionπ N = g) :
    (∀ t : ↥T, (pullback.lift a b (ha.trans hb.symm)).base t ∈ E.fullLevelSet N)
      ↔ (E.baseChange g).IsNaiveFullLevel N (E.torsionMapSection N g a ha)
          (E.torsionMapSection N g b hb) := by
  classical
  -- the pulled points at an arbitrary field-valued point, and their properties
  have hpull : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T),
      ∀ (c : T ⟶ E.torsion N) (hc : c ≫ E.torsionπ N = g),
      (N : ℤ) • (⟨τ ≫ c ≫ E.torsionι N, by
        rw [Category.assoc, Category.assoc, E.torsionι_π, hc]⟩ : E.Point (τ ≫ g)) = 0 := by
    intro k _ τ c hc
    rw [E.smul_eq_zero_iff_comp_mulByHom]
    show (τ ≫ c ≫ E.torsionι N) ≫ E.mulByHom (N : ℤ) = (τ ≫ g) ≫ E.zero
    rw [Category.assoc, Category.assoc,
      show E.torsionι N ≫ E.mulByHom (N : ℤ) = E.torsionπ N ≫ E.zero from
        pullback.condition, ← Category.assoc c, hc, ← Category.assoc]
  -- the base-change dictionary identification for the two sections
  have hdict : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T)
      (c : T ⟶ E.torsion N) (hc : c ≫ E.torsionπ N = g),
      Point.baseChangeEquiv E g τ
          (Point.pull (E.baseChange g) τ (E.torsionMapSection N g c hc))
        = (⟨τ ≫ c ≫ E.torsionι N, by
            rw [Category.assoc, Category.assoc, E.torsionι_π, hc]⟩ : E.Point (τ ≫ g)) := by
    intro k _ τ c hc
    refine Subtype.ext ?_
    show (τ ≫ ((E.torsionMapSection N g c hc :
        (E.baseChange g).Point (𝟙 T)) : T ⟶ (E.baseChange g).E)) ≫ pullback.fst E.π g
      = τ ≫ c ≫ E.torsionι N
    rw [Category.assoc, E.torsionMapSection_fst N g c hc]
  constructor
  · -- forward: the set condition gives the naive structure
    intro hset
    refine ⟨⟨E.torsionMapSection_killed N g a ha, E.torsionMapSection_killed N g b hb⟩, ?_⟩
    intro k _ _ τ x hx
    obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
    set pA : E.Point (τ ≫ g) := ⟨τ ≫ a ≫ E.torsionι N, by
      rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ with hpAdef
    set pB : E.Point (τ ≫ g) := ⟨τ ≫ b ≫ E.torsionι N, by
      rw [Category.assoc, Category.assoc, E.torsionι_π, hb]⟩ with hpBdef
    have hNk : (N : k) ≠ 0 :=
      (nIsInvertible_spec_iff k N).mp (h.of_hom (τ ≫ g))
    obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N k (τ ≫ g) hNk
    have hcard : Nat.card ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) = N ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
        Nat.card_zmod, Fintype.card_fin]
    have hkillG : ∀ z : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)),
        (N : ℤ) • z = 0 := fun z => Subtype.ext (by
      simpa using (Submodule.mem_torsionBy_iff _ _).mp z.2)
    set P' : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) :=
      ⟨pA, (Submodule.mem_torsionBy_iff _ _).mpr (hpull τ a ha)⟩ with hP'def
    set Q' : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) :=
      ⟨pB, (Submodule.mem_torsionBy_iff _ _).mpr (hpull τ b hb)⟩ with hQ'def
    have hcombos : ∀ ab : ZMod N × ZMod N, ab ≠ 0 →
        (ab.1.val : ℤ) • P' + (ab.2.val : ℤ) • Q' ≠ 0 := by
      intro v hv h0
      have h0' : (v.1.val : ℤ) • pA + (v.2.val : ℤ) • pB = 0 := by
        have := congrArg
          (Submodule.subtype (Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ))) h0
        simpa using this
      have hmem := (E.comp_combination_mem_zeroSection_iff N g h a b ha hb τ pt v).mpr h0'
      have hin := hset (τ.base pt)
      rw [fullLevelSet] at hin
      have hnot := Set.mem_iInter₂.mp hin v hv
      apply hnot
      have hcomp : (τ ≫ pullback.lift a b (ha.trans hb.symm) ≫
            E.combinationHom N v).base pt
          = (E.combinationHom N v).base
            ((pullback.lift a b (ha.trans hb.symm)).base (τ.base pt)) := by
        simp
      rwa [hcomp] at hmem
    have hgen := (pair_generates_iff_combos_ne_zero (N := N) hcard hkillG P' Q').mp hcombos
    -- transport the closure statement back to the base-changed curve
    have hy : Point.baseChangeEquiv E g τ x ∈
        Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ) :=
      (Submodule.mem_torsionBy_iff _ _).mpr
        (by rw [← map_zsmul (Point.baseChangeEquiv E g τ), hx, map_zero])
    have hzG := hgen ⟨Point.baseChangeEquiv E g τ x, hy⟩
    -- down to the ambient group
    have hamb : Point.baseChangeEquiv E g τ x ∈
        AddSubgroup.closure ({pA, pB} : Set (E.Point (τ ≫ g))) := by
      have := addMonoidHom_mem_closure_image
        (Submodule.subtype (Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ))).toAddMonoidHom
        hzG
      simpa [Set.image_pair] using this
    -- back through the base-change equivalence
    have hx' := addMonoidHom_mem_closure_image
      (Point.baseChangeEquiv E g τ).symm.toAddMonoidHom hamb
    rw [Set.image_pair] at hx'
    have h1 : (Point.baseChangeEquiv E g τ).symm pA
        = Point.pull (E.baseChange g) τ (E.torsionMapSection N g a ha) := by
      rw [hpAdef, ← hdict τ a ha]
      exact (Point.baseChangeEquiv E g τ).symm_apply_apply _
    have h2 : (Point.baseChangeEquiv E g τ).symm pB
        = Point.pull (E.baseChange g) τ (E.torsionMapSection N g b hb) := by
      rw [hpBdef, ← hdict τ b hb]
      exact (Point.baseChangeEquiv E g τ).symm_apply_apply _
    simpa [h1, h2] using hx'
  · -- backward: a naive structure forces the set condition at every point
    intro hnaive t
    rw [fullLevelSet]
    refine Set.mem_iInter₂.mpr fun v hv => ?_
    set τ : Spec (CommRingCat.of (AlgebraicClosure (T.residueField t))) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
        (AlgebraicClosure (T.residueField t)))) ≫
        T.fromSpecResidueField t with hτ
    obtain ⟨pt⟩ : Nonempty
        ↥(Spec (CommRingCat.of (AlgebraicClosure (T.residueField t)))) := inferInstance
    have hτpt : τ.base pt = t := by
      have hmem2 : τ.base pt ∈ Set.range (T.fromSpecResidueField t).base := by
        rw [hτ]
        exact ⟨(Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
          (AlgebraicClosure (T.residueField t))))).base pt, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at hmem2
    rw [Set.mem_preimage, Set.mem_compl_iff]
    intro hmem
    have hmem' : (τ ≫ pullback.lift a b (ha.trans hb.symm) ≫
        E.combinationHom N v).base pt ∈
        Set.range (E.torsionZero N).base := by
      have hcomp : (τ ≫ pullback.lift a b (ha.trans hb.symm) ≫
            E.combinationHom N v).base pt
          = (E.combinationHom N v).base
            ((pullback.lift a b (ha.trans hb.symm)).base (τ.base pt)) := by
        simp
      rw [hcomp, hτpt]
      exact hmem
    have h0 := (E.comp_combination_mem_zeroSection_iff N g h a b ha hb τ pt v).mp hmem'
    set pA : E.Point (τ ≫ g) := ⟨τ ≫ a ≫ E.torsionι N, by
      simp only [Category.assoc]
      rw [E.torsionι_π N, ha]⟩ with hpAdef
    set pB : E.Point (τ ≫ g) := ⟨τ ≫ b ≫ E.torsionι N, by
      simp only [Category.assoc]
      rw [E.torsionι_π N, hb]⟩ with hpBdef
    have hNk : (N : AlgebraicClosure (T.residueField t)) ≠ 0 :=
      (nIsInvertible_spec_iff (AlgebraicClosure (T.residueField t)) N).mp
        (h.of_hom (τ ≫ g))
    obtain ⟨e⟩ := E.torsion_geometricFibre_rank_two N
      (AlgebraicClosure (T.residueField t)) (τ ≫ g) hNk
    have hcard : Nat.card ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) = N ^ 2 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
        Nat.card_zmod, Fintype.card_fin]
    have hkillG : ∀ z : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)),
        (N : ℤ) • z = 0 := fun z => Subtype.ext (by
      simpa using (Submodule.mem_torsionBy_iff _ _).mp z.2)
    set P' : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) :=
      ⟨pA, (Submodule.mem_torsionBy_iff _ _).mpr (hpull τ a ha)⟩ with hP'def
    set Q' : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)) :=
      ⟨pB, (Submodule.mem_torsionBy_iff _ _).mpr (hpull τ b hb)⟩ with hQ'def
    have hclosureG : ∀ x : ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ)),
        x ∈ AddSubgroup.closure ({P', Q'} :
          Set ↥(Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ))) := by
      intro z
      have hzkill : (N : ℤ) • (z : E.Point (τ ≫ g)) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp z.2
      have hxkill : (N : ℤ) • (Point.baseChangeEquiv E g τ).symm
          (z : E.Point (τ ≫ g)) = 0 := by
        rw [← map_zsmul ((Point.baseChangeEquiv E g τ).symm), hzkill, map_zero]
      have hcl := hnaive.2 (AlgebraicClosure (T.residueField t)) τ
        ((Point.baseChangeEquiv E g τ).symm (z : E.Point (τ ≫ g))) hxkill
      have himg := addMonoidHom_mem_closure_image
        (Point.baseChangeEquiv E g τ).toAddMonoidHom hcl
      rw [Set.image_pair] at himg
      have hz1 : (z : E.Point (τ ≫ g)) ∈
          AddSubgroup.closure ({pA, pB} : Set (E.Point (τ ≫ g))) := by
        have hthis := himg
        rw [show ((Point.baseChangeEquiv E g τ).toAddMonoidHom : _ → _)
            (Point.pull (E.baseChange g) τ (E.torsionMapSection N g a ha)) = pA from
            hdict τ a ha,
          show ((Point.baseChangeEquiv E g τ).toAddMonoidHom : _ → _)
            (Point.pull (E.baseChange g) τ (E.torsionMapSection N g b hb)) = pB from
            hdict τ b hb,
          show ((Point.baseChangeEquiv E g τ).toAddMonoidHom : _ → _)
            ((Point.baseChangeEquiv E g τ).symm (z : E.Point (τ ≫ g)))
            = (z : E.Point (τ ≫ g)) from
            (Point.baseChangeEquiv E g τ).apply_symm_apply _] at hthis
        exact hthis
      have hpairimg : ({pA, pB} : Set (E.Point (τ ≫ g)))
          = (Submodule.subtype
              (Submodule.torsionBy ℤ (E.Point (τ ≫ g)) (N : ℤ))).toAddMonoidHom ''
            {P', Q'} := by
        rw [Set.image_pair]
        rfl
      rw [hpairimg] at hz1
      exact (injective_mem_closure_image_iff _ Subtype.val_injective _ _).mp hz1
    have hcombos := (pair_generates_iff_combos_ne_zero (N := N) hcard hkillG P' Q').mpr
      hclosureG v hv
    apply hcombos
    refine Subtype.ext ?_
    simpa using h0

/-! ### The classifying equivalence (step 4): points of the locus = naive full level
structures -/

/-- The torsion map attached to a killed section of `E ×_S T` (the inverse dictionary
to `torsionMapSection`). -/
noncomputable def sectionTorsionMap (P : (E.baseChange g).Section)
    (hP : (N : ℤ) • P = 0) : { c : T ⟶ E.torsion N // c ≫ E.torsionπ N = g } :=
  (E.torsionPointsEquiv N g).symm
    ⟨Point.congrBase E (Category.id_comp g) (Point.baseChangeEquiv E g (𝟙 T) P),
      (Submodule.mem_torsionBy_iff _ _).mpr (by
        rw [← map_zsmul, ← map_zsmul, hP, map_zero, map_zero])⟩

/-- Roundtrip: the section of the torsion map of a killed section is the section. -/
theorem torsionMapSection_sectionTorsionMap (P : (E.baseChange g).Section)
    (hP : (N : ℤ) • P = 0) :
    E.torsionMapSection N g (E.sectionTorsionMap N g P hP).1
      (E.sectionTorsionMap N g P hP).2 = P := by
  refine Subtype.ext ?_
  apply pullback.hom_ext
  · have h1 : (E.sectionTorsionMap N g P hP).1 ≫ E.torsionι N
        = ((Point.congrBase E (Category.id_comp g)
            (Point.baseChangeEquiv E g (𝟙 T) P) : E.Point g) : T ⟶ E.E) :=
      E.pointToTorsion_torsionι _ _
    exact (pullback.lift_fst _ _ _).trans (by rw [h1]; rfl)
  · exact (pullback.lift_snd _ _ _).trans P.2.symm

/-- Roundtrip: the torsion map of the section of a torsion map is the torsion map. -/
theorem sectionTorsionMap_torsionMapSection (a : T ⟶ E.torsion N)
    (ha : a ≫ E.torsionπ N = g) :
    (E.sectionTorsionMap N g (E.torsionMapSection N g a ha)
      (E.torsionMapSection_killed N g a ha)).1 = a := by
  apply pullback.hom_ext
  · have h1 : (E.sectionTorsionMap N g (E.torsionMapSection N g a ha)
          (E.torsionMapSection_killed N g a ha)).1 ≫ E.torsionι N
        = ((Point.congrBase E (Category.id_comp g) (Point.baseChangeEquiv E g (𝟙 T)
            (E.torsionMapSection N g a ha)) : E.Point g) : T ⟶ E.E) :=
      E.pointToTorsion_torsionι _ _
    show (E.sectionTorsionMap N g (E.torsionMapSection N g a ha)
        (E.torsionMapSection_killed N g a ha)).1 ≫ E.torsionι N
      = a ≫ E.torsionι N
    rw [h1]
    show ((Point.baseChangeEquiv E g (𝟙 T) (E.torsionMapSection N g a ha)) :
        E.Point (𝟙 T ≫ g)).1 = a ≫ E.torsionι N
    rw [Point.baseChangeEquiv_apply_coe, E.torsionMapSection_fst]
  · show (E.sectionTorsionMap N g (E.torsionMapSection N g a ha)
        (E.torsionMapSection_killed N g a ha)).1 ≫ E.torsionπ N
      = a ≫ E.torsionπ N
    rw [(E.sectionTorsionMap N g (E.torsionMapSection N g a ha)
      (E.torsionMapSection_killed N g a ha)).2, ha]

/-- The over-`g` fact for the first projection of a pair point. -/
theorem pairFstπ {T : Scheme.{u}} {g : T ⟶ S} (w : T ⟶ E.torsionPair N)
    (hw : w ≫ E.torsionPairπ N = g) :
    (w ≫ pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionπ N = g := by
  rw [Category.assoc]
  exact hw

/-- The over-`g` fact for the second projection of a pair point. -/
theorem pairSndπ {T : Scheme.{u}} {g : T ⟶ S} (w : T ⟶ E.torsionPair N)
    (hw : w ≫ E.torsionPairπ N = g) :
    (w ≫ pullback.snd (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionπ N = g := by
  rw [Category.assoc, show pullback.snd (E.torsionπ N) (E.torsionπ N) ≫
    E.torsionπ N = E.torsionPairπ N from (pullback.condition).symm]
  exact hw

omit [NeZero N] in
/-- `torsionMapSection` depends only on the torsion map (proof-irrelevant
congruence). -/
theorem torsionMapSection_congr {T : Scheme.{u}} {g : T ⟶ S}
    {c c' : T ⟶ E.torsion N} (hcc : c = c') (hc : c ≫ E.torsionπ N = g) :
    E.torsionMapSection N g c hc = E.torsionMapSection N g c' (hcc ▸ hc) := by
  subst hcc
  rfl

set_option synthInstance.maxHeartbeats 160000 in
/-- **The classifying equivalence (ENGINE AXIOM 2, points form).** `T`-points of the
full-level locus over `g` are exactly the naive full level-`N` structures on
`E ×_S T`. -/
noncomputable def fullLevelLocusPointsEquiv (h : NIsInvertible S N) (g : T ⟶ S) :
    { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g } ≃
      { PQ : (E.baseChange g).Section × (E.baseChange g).Section //
        (E.baseChange g).IsNaiveFullLevel N PQ.1 PQ.2 } :=
  (E.fullLevelLocusSectionsEquiv N h g).trans
    { toFun := fun w => ⟨⟨E.torsionMapSection N g (w.1 ≫ pullback.fst _ _)
          (E.pairFstπ N w.1 w.2.1),
        E.torsionMapSection N g (w.1 ≫ pullback.snd _ _)
          (E.pairSndπ N w.1 w.2.1)⟩, by
        have hlift : pullback.lift (w.1 ≫ pullback.fst _ _) (w.1 ≫ pullback.snd _ _)
            ((E.pairFstπ N w.1 w.2.1).trans (E.pairSndπ N w.1 w.2.1).symm) = w.1 := by
          apply pullback.hom_ext
          · rw [pullback.lift_fst]
          · rw [pullback.lift_snd]
        refine (E.forall_mem_fullLevelSet_iff_isNaiveFullLevel N g h _ _
          (E.pairFstπ N w.1 w.2.1) (E.pairSndπ N w.1 w.2.1)).mp ?_
        intro t
        rw [hlift]
        exact w.2.2 t⟩
      invFun := fun PQ => ⟨pullback.lift
          (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1
          (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1
          ((E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2.trans
            (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2.symm),
        by
          show (pullback.lift _ _ _ ≫ pullback.fst _ _) ≫ E.torsionπ N = g
          rw [pullback.lift_fst]
          exact (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2,
        by
          have hmi := (E.forall_mem_fullLevelSet_iff_isNaiveFullLevel N g h
            (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1
            (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1
            (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2
            (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2).mpr
          rw [E.torsionMapSection_sectionTorsionMap N g PQ.1.1 PQ.2.1.1,
            E.torsionMapSection_sectionTorsionMap N g PQ.1.2 PQ.2.1.2] at hmi
          exact hmi PQ.2⟩
      left_inv := fun w => Subtype.ext (by
        apply pullback.hom_ext
        · rw [pullback.lift_fst,
            E.sectionTorsionMap_torsionMapSection N g _ (E.pairFstπ N w.1 w.2.1)]
        · rw [pullback.lift_snd,
            E.sectionTorsionMap_torsionMapSection N g _ (E.pairSndπ N w.1 w.2.1)])
      right_inv := fun PQ => Subtype.ext (by
        have hfst : pullback.lift
            (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1
            (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1
            ((E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2.trans
              (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2.symm) ≫
              pullback.fst (E.torsionπ N) (E.torsionπ N)
            = (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1 := pullback.lift_fst _ _ _
        have hsnd : pullback.lift
            (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1
            (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1
            ((E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2.trans
              (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2.symm) ≫
              pullback.snd (E.torsionπ N) (E.torsionπ N)
            = (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1 := pullback.lift_snd _ _ _
        refine Prod.ext ?_ ?_
        · refine Eq.trans ?_ (E.torsionMapSection_sectionTorsionMap N g PQ.1.1 PQ.2.1.1)
          refine Subtype.ext ?_
          apply pullback.hom_ext
          · have hc1 : (pullback.lift _ _
                ((E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2.trans
                  (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2.symm) ≫
                pullback.fst (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N
              = (E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).1 ≫ E.torsionι N :=
              congrArg (· ≫ E.torsionι N) hfst
            exact (pullback.lift_fst _ _ _).trans
              (hc1.trans (pullback.lift_fst _ _ _).symm)
          · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
        · refine Eq.trans ?_ (E.torsionMapSection_sectionTorsionMap N g PQ.1.2 PQ.2.1.2)
          refine Subtype.ext ?_
          apply pullback.hom_ext
          · have hc2 : (pullback.lift _ _
                ((E.sectionTorsionMap N g PQ.1.1 PQ.2.1.1).2.trans
                  (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).2.symm) ≫
                pullback.snd (E.torsionπ N) (E.torsionπ N)) ≫ E.torsionι N
              = (E.sectionTorsionMap N g PQ.1.2 PQ.2.1.2).1 ≫ E.torsionι N :=
              congrArg (· ≫ E.torsionι N) hsnd
            exact (pullback.lift_fst _ _ _).trans
              (hc2.trans (pullback.lift_fst _ _ _).symm)
          · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm) }

end EllipticCurve

end ModularCurves
