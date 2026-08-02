/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.GroupScheme.NaiveGammaOneLocus
import ModularCurves.LevelStructure.CombinationLevel
import ModularCurves.Moduli.LevelLocusNatural

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

-- The same file-level transparency options `LevelStructure/CombinationLevel.lean` uses:
-- without them `rw` cannot see through `(E.baseChange g).E` to `pullback E.π g`, which the
-- base-change dictionary needs. (Transparency options, not heartbeat bumps.)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-- Transporting a torsion condition through the base-change dictionary. Extracted as its
own lemma so that the `AddMonoidHomClass` instance search happens once, at fixed types —
inline inside the master proof it blows the instance budget, and heartbeat bumps are not an
option in this project. -/
theorem baseChangeEquiv_zsmul_eq_zero_iff (τ : Spec (CommRingCat.of k) ⟶ T) (n : ℤ)
    (x : (E.baseChange g).Point τ) :
    n • x = 0 ↔ n • (Point.baseChangeEquiv E g τ x) = 0 := by
  have hmap : ∀ y : (E.baseChange g).Point τ,
      (Point.baseChangeEquiv E g τ) (n • y) = n • (Point.baseChangeEquiv E g τ) y :=
    fun y => (Point.baseChangeEquiv E g τ).toAddMonoidHom.map_zsmul n y
  have hz : (Point.baseChangeEquiv E g τ) 0 = 0 :=
    (Point.baseChangeEquiv E g τ).map_zero
  constructor
  · intro h0
    rw [← hmap, h0, hz]
  · intro h0
    refine (Point.baseChangeEquiv E g τ).injective ?_
    rw [hmap, h0, hz]

/-! ### The master identification: the naive `Γ₁(N)` set classifies naive `Γ₁(N)`-structures

The mirror of `forall_mem_fullLevelSet_iff_isNaiveFullLevel` — and far shorter, because
`IsNaiveGammaOne`'s second clause ("no proper multiple vanishes at any geometric point") is
*literally* the locus condition read through `comp_multiple_mem_zeroSection_iff`. The
full-level original has to convert a no-vanishing-combination statement into a *generation*
statement, which is what costs it `pair_generates_iff_combos_ne_zero`, the `N²`-count and the
closure transport; none of that appears here. -/

/-- **The master iff.** For a `T`-point `a` of `E[N]` over `g` (with `N` invertible on `S`),
`a` lands in the naive `Γ₁(N)` set at every point of `T` **iff** the attached section of
`E ×_S T` is a naive `Γ₁(N)`-structure. -/
theorem forall_mem_naiveGammaOneSet_iff_isNaiveGammaOne (h : NIsInvertible S N)
    (a : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g) :
    (∀ t : ↥T, a.base t ∈ E.naiveGammaOneSet N)
      ↔ (E.baseChange g).IsNaiveGammaOne N (E.torsionMapSection N g a ha) := by
  classical
  have hdict0 : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T)
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
  have hdict : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T),
      Point.baseChangeEquiv E g τ
          (Point.pull (E.baseChange g) τ (E.torsionMapSection N g a ha))
        = (⟨τ ≫ a ≫ E.torsionι N, by
            rw [Category.assoc, Category.assoc, E.torsionι_π, ha]⟩ : E.Point (τ ≫ g)) :=
    fun τ => hdict0 τ a ha
  -- the zero test, transported through the base-change dictionary
  have hzero : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T)
      (pt : ↥(Spec (CommRingCat.of k))) (m : ℕ),
      ((m : ℤ) • Point.pull (E.baseChange g) τ (E.torsionMapSection N g a ha) = 0
        ↔ (τ ≫ a ≫ E.multipleHom N m).base pt ∈ Set.range (E.torsionZero N).base) := by
    intro k _ τ pt m
    rw [E.comp_multiple_mem_zeroSection_iff N h a ha τ pt m, ← hdict τ]
    exact E.baseChangeEquiv_zsmul_eq_zero_iff τ (m : ℤ) _
  -- composition of base maps, used in both directions
  have hcomp : ∀ {k : Type u} [Field k] (τ : Spec (CommRingCat.of k) ⟶ T)
      (pt : ↥(Spec (CommRingCat.of k))) (m : ℕ),
      (τ ≫ a ≫ E.multipleHom N m).base pt
        = (E.multipleHom N m).base (a.base (τ.base pt)) := by
    intro k _ τ pt m
    simp
  constructor
  · intro hset
    refine ⟨E.torsionMapSection_killed N g a ha, fun k _ _ τ => ⟨?_, fun m hm0 hmN => ?_⟩⟩
    · rw [← Point.pull_zsmul, E.torsionMapSection_killed N g a ha, Point.pull_zero]
    · obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
      intro h0
      have hmem := (hzero τ pt m).mp h0
      have hin := hset (τ.base pt)
      rw [naiveGammaOneSet] at hin
      exact Set.mem_iInter₂.mp hin m ⟨hm0, hmN⟩ (by rwa [hcomp τ pt m] at hmem)
  · intro hnaive t
    rw [naiveGammaOneSet]
    refine Set.mem_iInter₂.mpr fun m hm => ?_
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
    have hmem' : (τ ≫ a ≫ E.multipleHom N m).base pt
        ∈ Set.range (E.torsionZero N).base := by
      rw [hcomp τ pt m, hτpt]
      exact hmem
    exact (hnaive.2 (AlgebraicClosure (T.residueField t)) τ).2 m hm.1 hm.2
      ((hzero τ pt m).mpr hmem')

/-! ### The classifying equivalences -/

/-- `T`-points of the naive `Γ₁(N)` locus over `g` are `T`-points of `E[N]` over `g` whose
image lies in the naive `Γ₁(N)` set. The mirror of `fullLevelLocusSectionsEquiv`, without the
`torsionPair` detour. -/
noncomputable def naiveGammaOneLocusSectionsEquiv (h : NIsInvertible S N) (g : T ⟶ S) :
    { h' : T ⟶ E.naiveGammaOneLocus N h // h' ≫ E.naiveGammaOneLocusπ N h = g } ≃
      { a : T ⟶ E.torsion N // a ≫ E.torsionπ N = g ∧
        ∀ t : T, a.base t ∈ E.naiveGammaOneSet N } where
  toFun h' := ⟨h'.1 ≫ E.naiveGammaOneLocusι N h,
    by rw [Category.assoc]; exact h'.2,
    fun t => by
      have : (E.naiveGammaOneLocusι N h).base (h'.1.base t) ∈
          Set.range (E.naiveGammaOneLocusι N h).base := Set.mem_range_self _
      rw [Scheme.Opens.range_ι] at this
      exact this⟩
  invFun w := ⟨IsOpenImmersion.lift (E.naiveGammaOneLocusι N h) w.1
      (by
        rw [Scheme.Opens.range_ι]
        rintro x ⟨t, rfl⟩
        exact w.2.2 t),
    by
      rw [show E.naiveGammaOneLocusπ N h = E.naiveGammaOneLocusι N h ≫ E.torsionπ N
        from rfl, ← Category.assoc, IsOpenImmersion.lift_fac]
      exact w.2.1⟩
  left_inv h' := Subtype.ext (by
    haveI : Mono (E.naiveGammaOneLocusι N h) := IsOpenImmersion.mono _
    exact (cancel_mono (E.naiveGammaOneLocusι N h)).mp (IsOpenImmersion.lift_fac _ _ _))
  right_inv w := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

/-- **(WP-D1c-coarse, the classifying equivalence)** `T`-points of the naive `Γ₁(N)` locus
over `g` are exactly the naive `Γ₁(N)`-structures on `E ×_S T`.

This is the relative-representability datum for `gammaOneNaiveProblem`, mirroring
`fullLevelLocusPointsEquiv` — and with a single generator the `pullback.lift` round-trips of
the original collapse to the two `sectionTorsionMap`/`torsionMapSection` identities. -/
noncomputable def naiveGammaOneLocusPointsEquiv (h : NIsInvertible S N) (g : T ⟶ S) :
    { h' : T ⟶ E.naiveGammaOneLocus N h // h' ≫ E.naiveGammaOneLocusπ N h = g } ≃
      { P : (E.baseChange g).Section // (E.baseChange g).IsNaiveGammaOne N P } :=
  (E.naiveGammaOneLocusSectionsEquiv N h g).trans
    { toFun := fun w => ⟨E.torsionMapSection N g w.1 w.2.1,
        (E.forall_mem_naiveGammaOneSet_iff_isNaiveGammaOne N h w.1 w.2.1).mp w.2.2⟩
      invFun := fun P => ⟨(E.sectionTorsionMap N g P.1 P.2.1).1,
        (E.sectionTorsionMap N g P.1 P.2.1).2,
        by
          have hmi := (E.forall_mem_naiveGammaOneSet_iff_isNaiveGammaOne N h
            (E.sectionTorsionMap N g P.1 P.2.1).1
            (E.sectionTorsionMap N g P.1 P.2.1).2).mpr
          rw [E.torsionMapSection_sectionTorsionMap N g P.1 P.2.1] at hmi
          exact hmi P.2⟩
      left_inv := fun w => Subtype.ext
        (E.sectionTorsionMap_torsionMapSection N g w.1 w.2.1)
      right_inv := fun P => Subtype.ext
        (E.torsionMapSection_sectionTorsionMap N g P.1 P.2.1) }

/-! ### Naturality of the classifying equivalence

The mirror of `Moduli/LevelLocusNatural.lean`, halved: with one generator the `fst`/`snd`
pairs of pinning and naturality lemmas each collapse to a single statement. -/

/-- **(pinning)** The section produced by the locus dictionary is `w ≫ ι ≫ torsionι`, read
through the base-change projection. -/
theorem naiveGammaOneLocusPointsEquiv_comp_fst (h : NIsInvertible S N) (g : T ⟶ S)
    (w : { h' : T ⟶ E.naiveGammaOneLocus N h // h' ≫ E.naiveGammaOneLocusπ N h = g }) :
    ((E.naiveGammaOneLocusPointsEquiv N h g w).1 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g =
      w.1 ≫ E.naiveGammaOneLocusι N h ≫ E.torsionι N := by
  rw [show ((E.naiveGammaOneLocusPointsEquiv N h g w).1 : (E.baseChange g).Section) =
      E.torsionMapSection N g (w.1 ≫ E.naiveGammaOneLocusι N h)
        (by rw [Category.assoc]; exact w.2)
      from rfl]
  rw [E.torsionMapSection_fst N g _ _]
  simp only [Category.assoc]

/-- **Naturality in `T`.** -/
theorem naiveGammaOneLocusPointsEquiv_natural (h : NIsInvertible S N)
    {T' : Scheme.{u}} (g : T ⟶ S) (k : T' ⟶ T)
    (w : { h' : T ⟶ E.naiveGammaOneLocus N h // h' ≫ E.naiveGammaOneLocusπ N h = g }) :
    ((E.naiveGammaOneLocusPointsEquiv N h (k ≫ g)
          ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩).1 :
        T' ⟶ (E.baseChange (k ≫ g)).E) ≫ pullback.fst E.π (k ≫ g) =
      k ≫ ((E.naiveGammaOneLocusPointsEquiv N h g w).1 : T ⟶ (E.baseChange g).E) ≫
        pullback.fst E.π g := by
  rw [E.naiveGammaOneLocusPointsEquiv_comp_fst N h (k ≫ g)
      ⟨k ≫ w.1, by rw [Category.assoc, w.2]⟩,
    E.naiveGammaOneLocusPointsEquiv_comp_fst N h g w]
  simp only [Category.assoc]

/-! ### The completion locus classifies refinements (WP-D2c-3) -/

/-- A section of a base-changed curve is determined by its composite with the projection.
The `EllipticCurve`-level form of `EllObj.section_ext_comp_fst`. -/
theorem baseChange_section_ext {T : Scheme.{u}} {g : T ⟶ S}
    {P Q : (E.baseChange g).Section}
    (hfst : (P.1 : T ⟶ pullback E.π g) ≫ pullback.fst E.π g =
      (Q.1 : T ⟶ pullback E.π g) ≫ pullback.fst E.π g) : P = Q := by
  refine Subtype.ext (pullback.hom_ext hfst ?_)
  show (P.1 : T ⟶ (E.baseChange g).E) ≫ (E.baseChange g).π =
    (Q.1 : T ⟶ (E.baseChange g).E) ≫ (E.baseChange g).π
  rw [P.2, Q.2]

/-- `torsionMapSection` is injective in the torsion map: the round trip
`sectionTorsionMap_torsionMapSection` recovers it. -/
theorem torsionMapSection_injective {T : Scheme.{u}} (g : T ⟶ S)
    {a b : T ⟶ E.torsion N} (ha : a ≫ E.torsionπ N = g) (hb : b ≫ E.torsionπ N = g)
    (hab : E.torsionMapSection N g a ha = E.torsionMapSection N g b hb) : a = b := by
  haveI := E.torsionι_isClosedImmersion N
  haveI : Mono (E.torsionι N) := inferInstance
  have h1 := E.torsionMapSection_fst N g a ha
  have h2 := E.torsionMapSection_fst N g b hb
  rw [hab] at h1
  exact ((cancel_mono (E.torsionι N)).mp (h2.symm.trans h1)).symm

/-- **(WP-D2c-3, pinning)** The first member of the level structure classified by `w` is the
section attached to `w`'s first coordinate. -/
theorem fullLevelLocusPointsEquiv_fst_eq (h : NIsInvertible S N) {T : Scheme.{u}}
    (g : T ⟶ S) (w : { h' : T ⟶ E.fullLevelLocus N h // h' ≫ E.fullLevelLocusπ N h = g })
    (a : T ⟶ E.torsion N) (ha : a ≫ E.torsionπ N = g)
    (hw : w.1 ≫ E.fullLevelLocusFst N h = a) :
    (E.fullLevelLocusPointsEquiv N h g w).1.1 = E.torsionMapSection N g a ha := by
  refine E.baseChange_section_ext ?_
  rw [E.fullLevelLocusPointsEquiv_fst_comp_fst N h g w, E.torsionMapSection_fst N g a ha,
    ← hw]
  rfl

/-- **(WP-D2c-3)** The completion locus classifies exactly the naive full level structures
whose first member is the given section: `T`-points over `g` correspond to full level
structures on `E ×_S T` refining `g ≫ P`.

This is the corrected statement of what sits under `Y(N) ⟶ Y₁(N)` — the earlier version,
using the whole full-level locus, classified an *unrelated* pair. -/
noncomputable def completionLocusClassifies (h : NIsInvertible S N) (P : S ⟶ E.torsion N)
    (hP : P ≫ E.torsionπ N = 𝟙 S) {T : Scheme.{u}} (g : T ⟶ S) :
    { c : T ⟶ E.completionLocus N h P // c ≫ E.completionLocusπ N h P = g } ≃
      { PQ : { PQ : (E.baseChange g).Section × (E.baseChange g).Section //
            (E.baseChange g).IsNaiveFullLevel N PQ.1 PQ.2 } //
          PQ.1.1 = E.torsionMapSection N g (g ≫ P)
            (by rw [Category.assoc, hP, Category.comp_id]) } :=
  (E.completionLocusPointsEquiv N h P g).trans
    { toFun := fun w =>
        ⟨E.fullLevelLocusPointsEquiv N h g
            ⟨w.1, E.fullLevelLocusπ_of_fst N h P hP g w.1 w.2⟩,
          E.fullLevelLocusPointsEquiv_fst_eq N h g _ (g ≫ P) _ w.2⟩
      invFun := fun PQ =>
        ⟨((E.fullLevelLocusPointsEquiv N h g).symm PQ.1).1, by
          have hfst := E.fullLevelLocusPointsEquiv_fst_eq N h g
            ((E.fullLevelLocusPointsEquiv N h g).symm PQ.1)
            (((E.fullLevelLocusPointsEquiv N h g).symm PQ.1).1 ≫ E.fullLevelLocusFst N h)
            (by
              rw [Category.assoc]
              exact ((E.fullLevelLocusPointsEquiv N h g).symm PQ.1).2) rfl
          rw [Equiv.apply_symm_apply] at hfst
          refine E.torsionMapSection_injective N g
            (by
              rw [Category.assoc]
              exact ((E.fullLevelLocusPointsEquiv N h g).symm PQ.1).2)
            (by rw [Category.assoc, hP, Category.comp_id]) ?_
          rw [← hfst]
          exact PQ.2⟩
      left_inv := fun w => Subtype.ext (by
        simp only [Equiv.symm_apply_apply])
      right_inv := fun PQ => Subtype.ext (by
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]) }

end EllipticCurve

end ModularCurves
