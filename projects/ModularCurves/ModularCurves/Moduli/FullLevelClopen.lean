/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.FullLevelSupset
import ModularCurves.Moduli.FullLevelTautSection
import ModularCurves.LevelStructure.FullLevelDivisorBridge
import ModularCurves.ForMathlib.ClosedImmersionResidueField
import ModularCurves.EllipticCurve.ModelRecord

/-!
# The Y(N) clopen leaf, assembled (YFULL route γ, [YF-CLOPEN])

Wires the `[YF-⊇]` divisor chain (`sectionsDivisor_ideal_eq_torsionIdeal`) and the openness
engine (`fullLevelOpens`) into the open-immersion criterion
`isOpenImmersion_levelSpaceΓι_of_taut`: over the open locus `fullLevelOpens` where every
nonzero combination `[c]P + [d]Q` is nonvanishing, the `N²` tautological combinations are
pairwise pointwise-distinct (residue-field agreement of the base-changed **sections** upgrades
topological agreement, `sections_residue_eq_of_base_eq`, and then a nonzero combination would
have to vanish, `base_mem_pointVanishSet_of_comp_eq`), so the tautological pair is a full-level
structure `[YF-⊇]`. Combined with the image bound `[YF-⊆]` this upgrades the closed immersion
`levelSpaceΓι` to an open immersion.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-! ### Point-algebra API: `restrict` and `asSection` are additive -/

/-- `Point.restrict` intertwines integer scalar multiplication (precomposition commutes with
`[n]`, `point_smul_eq_comp_mulBy` + associativity). -/
theorem restrict_zsmul {T T' : Scheme.{u}} {g : T ⟶ S} (m : T' ⟶ T) (a : ℤ) (P : E.Point g) :
    Point.restrict E m (a • P) = a • Point.restrict E m P := by
  refine Subtype.ext ?_
  show m ≫ ((a • P : E.Point g) : T ⟶ E.E)
    = ((a • Point.restrict E m P : E.Point (m ≫ g)) : T' ⟶ E.E)
  rw [E.point_smul_eq_comp_mulBy, E.point_smul_eq_comp_mulBy]
  exact (Category.assoc m P.1 (E.mulByHom a)).symm

/-- `Point.asSection` is additive: a section of the base-changed curve is determined by its
first projection, and that projection (`baseChangeEquiv`) is an additive equivalence; the sum
is transported across the base equality `𝟙 T ≫ g = g` by `point_add_val_congr_base`. Written
term-mode to sidestep the semireducible-`baseChange.E` `kabstract` wall (the `asSection_zsmul`
idiom). -/
theorem Point.asSection_add {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    Point.asSection E g (P + Q) = Point.asSection E g P + Point.asSection E g Q := by
  refine Subtype.ext (pullback.hom_ext ?_ ?_)
  · -- fst legs: both compose with `pullback.fst E.π g` to `(P + Q).1`
    have lhs : (Point.asSection E g (P + Q)).1 ≫ pullback.fst E.π g = (P + Q).1 :=
      Point.asSection_val_fst E g (P + Q)
    have rhs : (Point.asSection E g P + Point.asSection E g Q).1 ≫ pullback.fst E.π g = (P + Q).1 :=
      (Point.baseChangeEquiv_apply_coe E g (𝟙 T)
          (Point.asSection E g P + Point.asSection E g Q)).symm.trans <|
        (congrArg (·.1) (map_add (Point.baseChangeEquiv E g (𝟙 T))
          (Point.asSection E g P) (Point.asSection E g Q))).trans <|
          point_add_val_congr_base E (Category.id_comp g) _ P _ Q
            ((Point.baseChangeEquiv_apply_coe E g (𝟙 T) (Point.asSection E g P)).trans
              (Point.asSection_val_fst E g P))
            ((Point.baseChangeEquiv_apply_coe E g (𝟙 T) (Point.asSection E g Q)).trans
              (Point.asSection_val_fst E g Q))
    exact lhs.trans rhs.symm
  · -- snd legs: both compose with `pullback.snd E.π g` to `𝟙 T`
    exact (Point.asSection_val_snd E g (P + Q)).trans
      ((Point.asSection E g P + Point.asSection E g Q).2).symm

/-- **Sub-lemma A.** The tautological combination `[a]P + [b]Q` of the base-changed taut
sections is the base-changed section of the ambient combination point `combPoint a b`. -/
theorem combo_eq_asSection_restrict {T : Scheme.{u}}
    (k : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) (a b : ℤ) :
    a • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₁ E N))
      + b • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₂ E N))
    = Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (combPoint E N a b)) := by
  rw [combPoint, E.restrict_add, E.restrict_zsmul, E.restrict_zsmul, Point.asSection_add,
    Point.asSection_zsmul, Point.asSection_zsmul]

/-- `Point.asSection` sends `0` to `0` (from additivity: `x = x + x ⟹ x = 0`). -/
theorem Point.asSection_zero {T : Scheme.{u}} (g : T ⟶ S) :
    Point.asSection E g (0 : E.Point g) = 0 := by
  refine add_left_cancel (a := Point.asSection E g (0 : E.Point g)) ?_
  rw [add_zero, ← Point.asSection_add, add_zero]

/-! ### Combination-point algebra -/

omit [NeZero N] in
/-- The difference of two combination points is the combination of the differences. -/
theorem combPoint_sub (a b c d : ℤ) :
    combPoint E N a b - combPoint E N c d = combPoint E N (a - c) (b - d) := by
  simp only [combPoint, sub_smul]
  abel

/-- Scalar multiplication of an `N`-killed point is `N`-periodic in the coefficient. -/
theorem zsmul_emod_eq {T : Scheme.{u}} {g : T ⟶ S} (P : E.Point g) (hP : (N : ℤ) • P = 0)
    (c : ℤ) : c • P = (c % (N : ℤ)) • P := by
  obtain ⟨k, hk⟩ : ∃ k, c = c % (N : ℤ) + (N : ℤ) * k :=
    ⟨c / (N : ℤ), (Int.emod_add_mul_ediv c (N : ℤ)).symm⟩
  conv_lhs => rw [hk]
  rw [add_zsmul, mul_comm (N : ℤ) k, mul_zsmul, hP, smul_zero, add_zero]

/-- Combination points depend on their coefficients only modulo `N`. -/
theorem combPoint_emod (a b : ℤ) :
    combPoint E N a b = combPoint E N (a % (N : ℤ)) (b % (N : ℤ)) := by
  rw [combPoint, combPoint, E.zsmul_emod_eq N (tautPt₁ E N) (tautPt₁_smul_eq_zero E N) a,
    E.zsmul_emod_eq N (tautPt₂ E N) (tautPt₂_smul_eq_zero E N) b]

/-- The first taut section (base-changed along `k`) is `N`-killed. -/
theorem smul_N_taut₁_section {T : Scheme.{u}}
    (k : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) :
    (N : ℤ) • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₁ E N)) = 0 := by
  rw [← Point.asSection_zsmul, ← restrict_zsmul, tautPt₁_smul_eq_zero, restrict_zero,
    Point.asSection_zero]

/-- The second taut section (base-changed along `k`) is `N`-killed. -/
theorem smul_N_taut₂_section {T : Scheme.{u}}
    (k : T ⟶ pullback (E.torsionπ N) (E.torsionπ N)) :
    (N : ℤ) • Point.asSection E (k ≫ tautBase E N) (Point.restrict E k (tautPt₂ E N)) = 0 := by
  rw [← Point.asSection_zsmul, ← restrict_zsmul, tautPt₂_smul_eq_zero, restrict_zero,
    Point.asSection_zero]

/-- The vanishing locus depends only on the point (the killing hypothesis is proof-irrelevant). -/
theorem pointVanishSet_congr {T : Scheme.{u}} (t : T ⟶ S) {R₁ R₂ : E.Point t} (h : R₁ = R₂)
    (hR₁ : R₁.1 ≫ E.mulByHom N = t ≫ E.zero) (hR₂ : R₂.1 ≫ E.mulByHom N = t ≫ E.zero) :
    E.pointVanishSet N t R₁ hR₁ = E.pointVanishSet N t R₂ hR₂ := by
  subst h; rfl

/-! ### `[YF-⊇]`: over `fullLevelOpens` the tautological combinations are pairwise distinct -/

/-- **[YF-⊇ distinctness].** Over `fullLevelOpens` (where every nonzero combination is
nonvanishing), two tautological combinations whose coefficient pair differs modulo `N` are
pointwise distinct: if they agreed at `w`, the base-changed sections agree over the residue
field (`sections_residue_eq_of_base_eq`), so the difference — a nonzero combination — would
vanish at `U.ι w ∈ fullLevelOpens`, contradicting the defining nonvanishing. -/
theorem combSec_ne_of_diff (hN : NIsInvertible S N) (a b c d : ℤ)
    (hdvd : ¬((N : ℤ) ∣ (a - c) ∧ (N : ℤ) ∣ (b - d)))
    (w : ↥(fullLevelOpens E N hN : Scheme.{u})) :
    (a • Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₁ E N))
      + b • Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₂ E N))).1.base w
    ≠ (c • Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₁ E N))
      + d • Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₂ E N))).1.base w := by
  intro hbase
  rw [combo_eq_asSection_restrict E N (fullLevelOpens E N hN).ι a b,
    combo_eq_asSection_restrict E N (fullLevelOpens E N hN).ι c d] at hbase
  set Uι := (fullLevelOpens E N hN).ι with hUι
  set g := Uι ≫ tautBase E N with hg
  -- the two combinations are sections of the (separated) base-changed structure map
  haveI : IsSeparated E.π := E.proper.toIsSeparated
  haveI : IsSeparated (E.baseChange g).π :=
    inferInstanceAs (IsSeparated (pullback.snd E.π g))
  have hres := sections_residue_eq_of_base_eq (E.baseChange g).π
    (Point.asSection E g (Point.restrict E Uι (combPoint E N a b))).1
    (Point.asSection E g (Point.restrict E Uι (combPoint E N c d))).1
    (Point.asSection E g (Point.restrict E Uι (combPoint E N a b))).2
    (Point.asSection E g (Point.restrict E Uι (combPoint E N c d))).2 w hbase
  -- push the residue agreement onto the ambient combination points via the first projection
  set fw := (fullLevelOpens E N hN : Scheme.{u}).fromSpecResidueField w with hfw
  have side_eq : ∀ z : ℤ × ℤ, (fw ≫ Uι) ≫ (combPoint E N z.1 z.2).1
      = (fw ≫ (Point.asSection E g (Point.restrict E Uι (combPoint E N z.1 z.2))).1)
        ≫ pullback.fst E.π g := by
    intro z
    simp only [Category.assoc, Point.asSection_val_fst]
    rfl
  have hm : (fw ≫ Uι) ≫ (combPoint E N a b).1 = (fw ≫ Uι) ≫ (combPoint E N c d).1 := by
    rw [side_eq (a, b), side_eq (c, d)]
    exact congrArg (· ≫ pullback.fst E.π g) hres
  -- the difference of the two ambient combinations vanishes at `v = Uι w`
  obtain ⟨p⟩ : Nonempty (↑(Spec ((fullLevelOpens E N hN : Scheme.{u}).residueField w))) :=
    inferInstance
  have hv := E.base_mem_pointVanishSet_of_comp_eq N (tautBase E N) (combPoint E N a b)
    (combPoint E N c d) (combPoint_killed E N a b) (combPoint_killed E N c d) (fw ≫ Uι) hm p
  have hvp : (fw ≫ Uι).base p = Uι.base w := by
    show Uι.base (fw.base p) = Uι.base w
    rw [hfw, Scheme.fromSpecResidueField_apply]
  rw [hvp, E.pointVanishSet_congr N (tautBase E N) (E.combPoint_sub N a b c d)
    (E.sub_killed N (tautBase E N) _ _ (combPoint_killed E N a b) (combPoint_killed E N c d))
    (combPoint_killed E N (a - c) (b - d))] at hv
  -- `v` lies in `fullLevelOpens`, so no nonzero combination vanishes there — contradiction
  have hN0 : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbdd : ∀ z : ℤ, (z % (N : ℤ)).toNat < N := fun z => by
    rw [Int.toNat_lt (Int.emod_nonneg z (by exact_mod_cast NeZero.ne N))]
    exact_mod_cast Int.emod_lt_of_pos z hN0
  set cd : Fin N × Fin N :=
    (⟨((a - c) % (N : ℤ)).toNat, hbdd _⟩, ⟨((b - d) % (N : ℤ)).toNat, hbdd _⟩) with hcd
  have hcast1 : ((cd.1 : ℕ) : ℤ) = (a - c) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N))
  have hcast2 : ((cd.2 : ℕ) : ℤ) = (b - d) % (N : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N))
  have hcomb : combPoint E N (cd.1 : ℤ) (cd.2 : ℤ) = combPoint E N (a - c) (b - d) := by
    rw [hcast1, hcast2, ← E.combPoint_emod]
  have hcd_ne : cd ≠ 0 := by
    intro h0
    refine hdvd ⟨?_, ?_⟩
    · rw [Int.dvd_iff_emod_eq_zero]
      have : ((cd.1 : ℕ) : ℤ) = 0 := by rw [h0]; rfl
      rwa [hcast1] at this
    · rw [Int.dvd_iff_emod_eq_zero]
      have : ((cd.2 : ℕ) : ℤ) = 0 := by rw [h0]; rfl
      rwa [hcast2] at this
  have hvU : Uι.base w ∈ fullLevelOpenSet E N hN := by
    have hr : Uι.base w ∈ Set.range Uι.base := ⟨w, rfl⟩
    rwa [hUι, Scheme.Opens.range_ι] at hr
  rw [fullLevelOpenSet, Set.mem_compl_iff, Set.mem_iUnion₂] at hvU
  exact hvU ⟨cd, hcd_ne, by
    rw [E.pointVanishSet_congr N (tautBase E N) hcomb (combPoint_killed E N _ _)
      (combPoint_killed E N (a - c) (b - d))]
    exact hv⟩

/-- **[YF-⊇].** Over `fullLevelOpens` the tautological pair is a full-level structure: the
`N²` combinations are `N`-killed (the taut points are) and pairwise pointwise-distinct
(`combSec_ne_of_diff`), so their section divisor equals `E[N]`
(`sectionsDivisor_ideal_eq_torsionIdeal`). -/
theorem isFullLevel_taut_over_fullLevelOpens (hN : NIsInvertible S N) :
    (E.baseChange ((fullLevelOpens E N hN).ι ≫ tautBase E N)).IsFullLevel N
      (Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₁ E N)))
      (Point.asSection E ((fullLevelOpens E N hN).ι ≫ tautBase E N)
        (Point.restrict E (fullLevelOpens E N hN).ι (tautPt₂ E N))) := by
  refine ⟨⟨smul_N_taut₁_section E N _, smul_N_taut₂_section E N _⟩, ?_⟩
  apply sectionsDivisor_ideal_eq_torsionIdeal
  · -- each combination is `N`-killed
    intro i
    rw [← (E.baseChange _).smul_eq_zero_iff_comp_mulByHom, smul_add, smul_comm (N : ℤ) _,
      smul_comm (N : ℤ) _, smul_N_taut₁_section E N _, smul_N_taut₂_section E N _, smul_zero,
      smul_zero, add_zero]
  · -- pairwise pointwise-distinct
    intro i _ j _ hij u
    refine combSec_ne_of_diff E N hN _ _ _ _ ?_ u
    rintro ⟨hd1, hd2⟩
    have hposN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hN0 : (0 : ℤ) < N := by exact_mod_cast hposN
    -- a divisor of a difference of two nonnegative integers below `N` forces equality
    have hkey : ∀ x y : ℤ, (N : ℤ) ∣ (x - y) → 0 ≤ x → x < N → 0 ≤ y → y < N → x = y := by
      rintro x y ⟨k, hk⟩ hx0 hxN hy0 hyN
      have hk1 : k < 1 := by nlinarith
      have hk2 : -1 < k := by nlinarith
      have hk0 : k = 0 := by omega
      rw [hk0, mul_zero] at hk
      omega
    refine hij (Fin.ext ?_)
    have e1 : (i : ℕ) % N = (j : ℕ) % N := by
      have := hkey _ _ hd1 (by positivity) (by exact_mod_cast Nat.mod_lt _ hposN)
        (by positivity) (by exact_mod_cast Nat.mod_lt _ hposN)
      exact_mod_cast this
    have e2 : (i : ℕ) / N = (j : ℕ) / N := by
      have := hkey _ _ hd2 (by positivity)
        (by exact_mod_cast Nat.div_lt_of_lt_mul (by simpa [pow_two] using i.2))
        (by positivity)
        (by exact_mod_cast Nat.div_lt_of_lt_mul (by simpa [pow_two] using j.2))
      exact_mod_cast this
    have hi := Nat.div_add_mod (i : ℕ) N
    have hj := Nat.div_add_mod (j : ℕ) N
    rw [e1, e2] at hi
    exact hi.symm.trans hj

/-! ### `[YF-⊆]` and the clopen leaf -/

/-- The tautological pair is a full-level structure over `levelSpaceΓ` itself — the level space
classifies full-level, so its own inclusion witnesses it (`levelSpaceΓ_spec` with `h = 𝟙`). -/
theorem taut_isFullLevel_over_levelSpaceΓ :
    (E.baseChange (levelSpaceΓι E N ≫ tautBase E N)).IsFullLevel N
      (Point.asSection E (levelSpaceΓι E N ≫ tautBase E N)
        (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N)))
      (Point.asSection E (levelSpaceΓι E N ≫ tautBase E N)
        (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N))) := by
  have hP : (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N)).1 ≫ E.mulByHom N =
      (levelSpaceΓι E N ≫ tautBase E N) ≫ E.zero := by
    show (levelSpaceΓι E N ≫ (tautPt₁ E N).1) ≫ E.mulByHom N = _
    rw [Category.assoc, tautPt₁_killed, ← Category.assoc]
  have hQ : (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N)).1 ≫ E.mulByHom N =
      (levelSpaceΓι E N ≫ tautBase E N) ≫ E.zero := by
    show (levelSpaceΓι E N ≫ (tautPt₂ E N).1) ≫ E.mulByHom N = _
    rw [Category.assoc, tautPt₂_killed, ← Category.assoc]
  refine (levelSpaceΓ_spec E N (levelSpaceΓι E N ≫ tautBase E N)
    (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N))
    (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N)) hP hQ).mp ⟨𝟙 _, ?_⟩
  rw [Category.id_comp]
  haveI := E.torsionι_isClosedImmersion N
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst]
    apply (cancel_mono (E.torsionι N)).mp
    rw [E.pointToTorsion_torsionι, Category.assoc]
    show levelSpaceΓι E N ≫ (tautPt₁ E N).1 =
      levelSpaceΓι E N ≫ pullback.fst (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N
    rfl
  · rw [pullback.lift_snd]
    apply (cancel_mono (E.torsionι N)).mp
    rw [E.pointToTorsion_torsionι, Category.assoc]
    show levelSpaceΓι E N ≫ (tautPt₂ E N).1 =
      levelSpaceΓι E N ≫ pullback.snd (E.torsionπ N) (E.torsionπ N) ≫ E.torsionι N
    rfl

/-- **[YF-⊆] piece 2.** The tautological pair generates `E[N]` at every geometric point of
`levelSpaceΓ` — apply the T-D8-bridge ⟹ (`naive_gen_of_divisor_eq`) to the full-level structure
`taut_isFullLevel_over_levelSpaceΓ`. -/
theorem taut_generates_over_levelSpaceΓ (hN : NIsInvertible S N) (k : Type u) [Field k]
    [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ levelSpaceΓ E N) :
    ∀ x : (E.baseChange (levelSpaceΓι E N ≫ tautBase E N)).Point t, (N : ℤ) • x = 0 →
      x ∈ AddSubgroup.closure
        {Point.pull (E.baseChange (levelSpaceΓι E N ≫ tautBase E N)) t
            (Point.asSection E (levelSpaceΓι E N ≫ tautBase E N)
              (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N))),
          Point.pull (E.baseChange (levelSpaceΓι E N ≫ tautBase E N)) t
            (Point.asSection E (levelSpaceΓι E N ≫ tautBase E N)
              (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N)))} := by
  have hN' : NIsInvertible (levelSpaceΓ E N) N := by
    have h := hN.map ((levelSpaceΓι E N ≫ tautBase E N).appTop).hom
    rwa [map_natCast] at h
  exact (E.baseChange (levelSpaceΓι E N ≫ tautBase E N)).naive_gen_of_divisor_eq N hN'
    (taut_isFullLevel_over_levelSpaceΓ E N).1.1 (taut_isFullLevel_over_levelSpaceΓ E N).1.2
    (taut_isFullLevel_over_levelSpaceΓ E N).2 k t

/-- **[YF-⊆ transport].** `taut_generates_over_levelSpaceΓ` pushed through the base-change point
equivalence (`Point.baseChangeEquiv`) and the associativity cast (`Point.castBase`): over a
geometric point `t` of `levelSpaceΓ`, the **restricted** tautological pair
`restrict (t ≫ levelSpaceΓι) tautPt₁/₂` generates the `N`-torsion of the ambient fibre
`E.Point ((t ≫ levelSpaceΓι) ≫ tautBase)`. This is the form consumed by the group core
`comb_ne_zero_of_generates`. -/
theorem taut_generates_restrict (hN : NIsInvertible S N) (k : Type u) [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ levelSpaceΓ E N) :
    ∀ x : E.Point ((t ≫ levelSpaceΓι E N) ≫ tautBase E N), (N : ℤ) • x = 0 →
      x ∈ AddSubgroup.closure
        {Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₁ E N),
         Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₂ E N)} := by
  set σ := levelSpaceΓι E N ≫ tautBase E N with hσ
  set Ψ : (E.baseChange σ).Point t ≃+ E.Point ((t ≫ levelSpaceΓι E N) ≫ tautBase E N) :=
    (Point.baseChangeEquiv E σ t).trans
      (Point.castBase E (Category.assoc t (levelSpaceΓι E N) (tautBase E N)).symm) with hΨ
  -- `Ψ` carries the base-change generators to the restricted tautological points
  have hΨ₁ : Ψ (Point.pull (E.baseChange σ) t
      (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N))))
      = Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₁ E N) := by
    apply Subtype.ext
    rw [hΨ, AddEquiv.trans_apply, Point.castBase_coe, Point.baseChangeEquiv_apply_coe]
    show (t ≫ (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N))).1)
        ≫ pullback.fst E.π σ = (t ≫ levelSpaceΓι E N) ≫ (tautPt₁ E N).1
    rw [Category.assoc, Point.asSection_val_fst]
    exact (Category.assoc _ _ _).symm
  have hΨ₂ : Ψ (Point.pull (E.baseChange σ) t
      (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N))))
      = Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₂ E N) := by
    apply Subtype.ext
    rw [hΨ, AddEquiv.trans_apply, Point.castBase_coe, Point.baseChangeEquiv_apply_coe]
    show (t ≫ (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N))).1)
        ≫ pullback.fst E.π σ = (t ≫ levelSpaceΓι E N) ≫ (tautPt₂ E N).1
    rw [Category.assoc, Point.asSection_val_fst]
    exact (Category.assoc _ _ _).symm
  intro x hx
  have hx' : (N : ℤ) • Ψ.symm x = 0 := by rw [← map_zsmul, hx, map_zero]
  have hmem := taut_generates_over_levelSpaceΓ E N hN k t (Ψ.symm x) hx'
  -- the base-change generators land in the preimage of the target closure
  have hle : AddSubgroup.closure
        {Point.pull (E.baseChange σ) t
            (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₁ E N))),
          Point.pull (E.baseChange σ) t
            (Point.asSection E σ (Point.restrict E (levelSpaceΓι E N) (tautPt₂ E N)))}
      ≤ (AddSubgroup.closure
          {Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₁ E N),
           Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₂ E N)}).comap Ψ.toAddMonoidHom := by
    rw [AddSubgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom]
    rcases (by simpa using hz : z = _ ∨ z = _) with rfl | rfl
    · rw [hΨ₁]; exact AddSubgroup.subset_closure (Set.mem_insert _ _)
    · rw [hΨ₂]; exact AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hfin := hle hmem
  rwa [AddSubgroup.mem_comap, AddEquiv.coe_toAddMonoidHom, Ψ.apply_symm_apply] at hfin

/-- **[YF-⊆] — GATE (reduced-fibre distinctness, KM 3.7.1).** The image of the full-level
closed immersion `levelSpaceΓι` lies in `fullLevelOpens`. At a full-level point the tautological
pair generates `E[N]` fibrewise (`levelSpaceΓ_spec` over `κ(p)`), and for `N` invertible `E[N]`
is finite étale hence has reduced geometric fibres of rank `N²`, so the `N²` combinations
`[c]P + [d]Q` are fibrewise **distinct** (the `naive_gen_of_divisor_eq` = T-D8-bridge ⟹ register);
therefore no nonzero combination vanishes there, i.e. the point lies in `fullLevelOpens`. This is
the reverse ("full-level ⟹ distinct") of the `[YF-⊇]` divisor chain. -/
theorem range_levelSpaceΓι_subset (hN : NIsInvertible S N) :
    Set.range (levelSpaceΓι E N).base ⊆ (fullLevelOpens E N hN : Set _) := by
  intro w hw
  show w ∈ fullLevelOpenSet E N hN
  rw [fullLevelOpenSet, Set.mem_compl_iff, Set.mem_iUnion₂]
  rintro ⟨cd, hcd, hmem⟩
  set fw := (pullback (E.torsionπ N) (E.torsionπ N)).fromSpecResidueField w with hfw
  -- Part 1: `combPoint (cd.1) (cd.2)` agrees with `0` after `fw` (the geometric point at `w`
  -- factors through the agreement locus, which is a closed immersion).
  have hzero : fw ≫ (E.combPoint N (cd.1 : ℤ) (cd.2 : ℤ)).1
      = fw ≫ ((0 : E.Point (E.tautBase N)) : _ ⟶ E.E) := by
    rw [pointVanishSet] at hmem
    obtain ⟨sA, hsA⟩ := AlgebraicGeometry.exists_fromSpecResidueField_factor _ w hmem
    have h := congrArg (sA ≫ ·) (AlgebraicGeometry.agreementι_comp_eq (E.torsionπ N)
      (E.pointToTorsion (E.combPoint N (cd.1 : ℤ) (cd.2 : ℤ)) (combPoint_killed E N _ _))
      (E.pointToTorsion 0 (E.zeroPoint_comp_mulByHom N (E.tautBase N)))
      (by rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ]))
    rw [← Category.assoc, ← Category.assoc, hsA] at h
    have h2 := congrArg (· ≫ E.torsionι N) h
    rwa [Category.assoc, Category.assoc, E.pointToTorsion_torsionι,
      E.pointToTorsion_torsionι] at h2
  -- Part 2: the taut pair generates at `w`, so no nonzero combination vanishes — contradiction.
  -- Factor `fw` through the full-level closed immersion `levelSpaceΓι` (its range contains `w`).
  haveI : IsClosedImmersion (levelSpaceΓι E N) :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.subschemeι _))
  obtain ⟨s, hs⟩ := AlgebraicGeometry.exists_fromSpecResidueField_factor (levelSpaceΓι E N) w hw
  -- pass to an algebraically closed geometric point over `w`
  set k : Type u :=
    AlgebraicClosure ↑((pullback (E.torsionπ N) (E.torsionπ N)).residueField w) with hk
  set π : Spec (CommRingCat.of k) ⟶
      Spec ((pullback (E.torsionπ N) (E.torsionπ N)).residueField w) :=
    Spec.map (CommRingCat.ofHom (algebraMap
      ↑((pullback (E.torsionπ N) (E.torsionπ N)).residueField w) k)) with hπ
  set t : Spec (CommRingCat.of k) ⟶ levelSpaceΓ E N := π ≫ s with ht_def
  have ht : t ≫ levelSpaceΓι E N = π ≫ fw := by rw [ht_def, Category.assoc, hs]
  -- `N` is invertible in `k`
  have hNk : (N : k) ≠ 0 := by
    refine (nIsInvertible_spec_iff k N).mp ?_
    have h := hN.map ((t ≫ (levelSpaceΓι E N ≫ tautBase E N)).appTop).hom
    rwa [map_natCast] at h
  -- the restricted tautological points at the geometric point over `w` are `N`-killed
  have hAtor : (N : ℤ) • Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₁ E N) = 0 := by
    rw [← E.restrict_zsmul, tautPt₁_smul_eq_zero, restrict_zero]
  have hBtor : (N : ℤ) • Point.restrict E (t ≫ levelSpaceΓι E N) (tautPt₂ E N) = 0 := by
    rw [← E.restrict_zsmul, tautPt₂_smul_eq_zero, restrict_zero]
  -- `cd ≠ 0` gives nonzero coefficients
  have hne : ¬((cd.1 : ℕ) = 0 ∧ (cd.2 : ℕ) = 0) := by
    rintro ⟨h1, h2⟩
    exact hcd (Prod.ext_iff.mpr ⟨Fin.val_eq_zero_iff.mp h1, Fin.val_eq_zero_iff.mp h2⟩)
  -- the group core: the nonzero combination is nonzero — but `hzero` forces it to vanish
  apply E.comb_ne_zero_of_generates hNk hAtor hBtor
    (taut_generates_restrict E N hN k t) cd.1.isLt cd.2.isLt hne
  rw [← E.restrict_zsmul, ← E.restrict_zsmul, ← E.restrict_add,
    show (0 : E.Point ((t ≫ levelSpaceΓι E N) ≫ tautBase E N))
        = Point.restrict E (t ≫ levelSpaceΓι E N) (0 : E.Point (tautBase E N)) from
      (E.restrict_zero (t ≫ levelSpaceΓι E N)).symm]
  apply Subtype.ext
  show (t ≫ levelSpaceΓι E N) ≫ (E.combPoint N (cd.1 : ℤ) (cd.2 : ℤ)).1
      = (t ≫ levelSpaceΓι E N) ≫ ((0 : E.Point (tautBase E N)) : _ ⟶ E.E)
  rw [ht, Category.assoc, Category.assoc]
  exact congrArg (π ≫ ·) hzero

/-- **[YF-CLOPEN].** For `N` invertible the full-level closed immersion `levelSpaceΓι` is an
**open immersion**: its image lies in the open `fullLevelOpens` (`[YF-⊆]`), over which the
tautological pair is a full-level structure (`[YF-⊇]`, `isFullLevel_taut_over_fullLevelOpens`),
providing a section — so `isOpenImmersion_levelSpaceΓι_of_taut` upgrades the closed immersion. -/
theorem isOpenImmersion_levelSpaceΓι_full (hN : NIsInvertible S N) :
    IsOpenImmersion (levelSpaceΓι E N) :=
  isOpenImmersion_levelSpaceΓι_of_taut E N (fullLevelOpens E N hN)
    (range_levelSpaceΓι_subset E N hN) (isFullLevel_taut_over_fullLevelOpens E N hN)

/-! ### The T-D8-bridge `⟸` direction (naive generation ⟹ divisor equality) -/

/-- **(T-D8-bridge ⟸, KM 3.7.1 / 1.4.4).** Fibrewise generation forces the `N²` combination
sections `[a]P + [b]Q` to be pairwise **topologically** distinct: if two collide at `u ∈ S`,
their difference — a combination that hits the *rational* identity section at `u` — has forced
residue-field agreement (`sections_residue_eq_of_base_eq`, separatedness), so it *vanishes* at
the geometric point over `u`; but generation makes the `N²` combinations injective there
(`naive_iff_comboFamily_injective`), forcing the two indices equal. Pairwise-distinctness then
feeds the `[YF-⊇]` divisor chain (`sectionsDivisor_ideal_eq_torsionIdeal`). No Galois ambiguity
(the collision point is rational), so the full-set-of-sections/T-D2 globalization is not needed. -/
theorem naive_gen_implies_divisor_eq (hN : NIsInvertible S N)
    {P Q : E.Section} (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0)
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
        ∀ x : E.Point t, (N : ℤ) • x = 0 →
          x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q}) :
    (RelEffCartierDiv.sectionsDivisor E.π
        (fun i : Fin (N ^ 2) =>
          (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) :
            E.Point (𝟙 S))))).ideal = E.torsionIdeal N := by
  haveI : IsSeparated E.π := E.proper.toIsSeparated
  apply sectionsDivisor_ideal_eq_torsionIdeal
  · -- each combination section is killed by `N`
    intro i
    refine (E.smul_eq_zero_iff_comp_mulByHom (𝟙 S) N _).mp ?_
    rw [smul_add, smul_comm (N : ℤ) _ P, smul_comm (N : ℤ) _ Q, hP, hQ, smul_zero,
      smul_zero, add_zero]
  · -- pairwise topological distinctness
    intro i _ j _ hij u hcollide
    -- separatedness forces residue-field agreement at `u`
    have hres := sections_residue_eq_of_base_eq E.π
      (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S))).1
      (((((j : ℕ) % N : ℕ) : ℤ) • P + ((((j : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S))).1
      (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S))).2
      (((((j : ℕ) % N : ℕ) : ℤ) • P + ((((j : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S))).2
      u hcollide
    -- the geometric point over `u`
    set k : Type u := AlgebraicClosure ↑(S.residueField u) with hk
    set ū : Spec (CommRingCat.of k) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap ↑(S.residueField u) k)) ≫
        S.fromSpecResidueField u with hū
    have hpull_eq : Point.pull E ū
          (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S)))
        = Point.pull E ū
          (((((j : ℕ) % N : ℕ) : ℤ) • P + ((((j : ℕ) / N : ℕ) : ℤ) • Q) : E.Point (𝟙 S))) := by
      apply Subtype.ext
      show ū ≫ _ = ū ≫ _
      rw [hū, Category.assoc, Category.assoc, hres]
    -- `N` invertible in `k`
    have hNk : (N : k) ≠ 0 := by
      refine (nIsInvertible_spec_iff k N).mp ?_
      have h := hN.map (ū.appTop).hom
      rwa [map_natCast] at h
    -- generation makes the combination family injective at the geometric point
    have hinj := (naive_iff_comboFamily_injective ū hNk hP hQ).mp (hgen k ū)
    apply hij
    apply hinj
    apply Subtype.ext
    rw [comboFamily, comboFamily, AddSubgroup.coe_add, AddSubgroup.coe_add,
      AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul]
    show ((((i : ℕ) % N : ℕ) : ℤ) • Point.pull E ū P
        + ((((i : ℕ) / N : ℕ) : ℤ) • Point.pull E ū Q) : E.Point ū)
      = ((((j : ℕ) % N : ℕ) : ℤ) • Point.pull E ū P
        + ((((j : ℕ) / N : ℕ) : ℤ) • Point.pull E ū Q))
    rw [← Point.pull_zsmul, ← Point.pull_zsmul, ← Point.pull_add, ← Point.pull_zsmul,
      ← Point.pull_zsmul, ← Point.pull_add]
    exact hpull_eq

/-- **(T-D8-bridge, full iff — downstream discharge of `Basic.fullLevel_divisor_iff_naive_gen`).**
For `N` invertible and `P, Q` killed by `N`, the Drinfeld full-level divisor equality holds iff on
every geometric point the pulled-back `P, Q` generate the `N`-torsion. `⟹` is
`naive_gen_of_divisor_eq` (the counting/pigeonhole register); `⟸` is `naive_gen_implies_divisor_eq`
(the collision-vanishing register). -/
theorem fullLevel_divisor_iff_naive_gen_downstream (hN : NIsInvertible S N)
    (P Q : E.Section) (hP : (N : ℤ) • P = 0) (hQ : (N : ℤ) • Q = 0) :
    (RelEffCartierDiv.sectionsDivisor E.π
        (fun i : Fin (N ^ 2) =>
          (((((i : ℕ) % N : ℕ) : ℤ) • P + ((((i : ℕ) / N : ℕ) : ℤ) • Q) :
            E.Point (𝟙 S))))).ideal = E.torsionIdeal N ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (t : Spec (CommRingCat.of k) ⟶ S),
        ∀ x : E.Point t, (N : ℤ) • x = 0 →
          x ∈ AddSubgroup.closure {Point.pull E t P, Point.pull E t Q} :=
  ⟨fun hdiv k _ _ t => E.naive_gen_of_divisor_eq N hN hP hQ hdiv k t,
   fun hgen => E.naive_gen_implies_divisor_eq N hN hP hQ hgen⟩

end EllipticCurve

end ModularCurves
