import PadicLFunctions.Measure.Basic
import Mathlib.Topology.CompactOpen

/-!
# A Fubini theorem for p-adic measures

The swap `∫∫ F(x,y) dμ(x) dν(y) = ∫∫ F(x,y) dν(y) dμ(x)` for `ℤ_[p]`-valued measures
on compact spaces. This is the engine behind commutativity and associativity of
convolution on `Λ(ℤ_p^×)` (RJW Rem. 3.11: "One checks that this does give an algebra
structure").

Strategy (the source's own reduction to locally constant functions, RJW Rem. 3.8,
applied to the *curried* map): approximate `curry F : X → C(Y, ℤ_p)` uniformly by a
locally constant map `Φ` (possible because the target is an ultrametric normed group —
`exists_locallyConstant_norm_sub_le'`). `Φ` has finitely many values `g` on clopen
fibres, so both iterated integrals of the approximation collapse to the same finite sum
`∑_g (∫𝟙_{Φ=g} dμ)·(∫g dν)`, and the error is controlled by `‖μ‖, ‖ν‖ ≤ 1`.

This route needs no total-disconnectedness or Hausdorff hypotheses (an earlier plan via
clopen-box decompositions did — replan recorded in `.mathlib-quality/tickets.md` T018).
-/

open scoped fwdDiff

variable (p : ℕ) [hp : Fact p.Prime]

noncomputable section

namespace PadicMeasure

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The inner integral: `x ↦ ∫ F(x, y) dν(y)`, as a continuous map. -/
noncomputable def innerInt [CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) :
    C(X, ℤ_[p]) :=
  ⟨fun x => ν (F.curry x), (continuous p ν).comp (map_continuous F.curry)⟩

@[simp]
lemma innerInt_apply [CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) (x : X) :
    innerInt p ν F x = ν (F.curry x) := rfl

@[simp]
lemma innerInt_add [CompactSpace Y] (ν : PadicMeasure p Y) (F G : C(X × Y, ℤ_[p])) :
    innerInt p ν (F + G) = innerInt p ν F + innerInt p ν G :=
  ContinuousMap.ext fun x => by
    have hcurry : (F + G).curry x = F.curry x + G.curry x := ContinuousMap.ext fun y => rfl
    simp [hcurry]

@[simp]
lemma innerInt_smul [CompactSpace Y] (c : ℤ_[p]) (ν : PadicMeasure p Y)
    (F : C(X × Y, ℤ_[p])) :
    innerInt p ν (c • F) = c • innerInt p ν F :=
  ContinuousMap.ext fun x => by
    have hcurry : (c • F).curry x = c • F.curry x := ContinuousMap.ext fun y => rfl
    simp [hcurry]

@[simp]
lemma innerInt_measure_add [CompactSpace Y] (ν₁ ν₂ : PadicMeasure p Y)
    (F : C(X × Y, ℤ_[p])) :
    innerInt p (ν₁ + ν₂) F = innerInt p ν₁ F + innerInt p ν₂ F :=
  ContinuousMap.ext fun _x => rfl

@[simp]
lemma innerInt_measure_zero [CompactSpace Y] (F : C(X × Y, ℤ_[p])) :
    innerInt p (0 : PadicMeasure p Y) F = 0 :=
  ContinuousMap.ext fun _x => rfl

/-- **Density of locally constant maps, general ultrametric target**: any continuous
map from a compact space to an ultrametric seminormed group is uniformly approximated
by locally constant maps. (Generalises `exists_locallyConstant_norm_sub_le`, whose
target is `ℤ_[p]`.) PR candidate for mathlib. -/
theorem exists_locallyConstant_norm_sub_le' [CompactSpace X]
    {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (f : C(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : LocallyConstant X E, ∀ x, ‖f x - Φ x‖ ≤ ε := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨⟨fun x => (IsEmpty.false x).elim, fun s => by
      rw [Set.eq_empty_of_isEmpty (_ ⁻¹' s)]; exact isOpen_empty⟩,
      fun x => (IsEmpty.false x).elim⟩
  classical
  -- clopen cover by ball preimages
  have hcov : ∀ x : X,
      ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ y ∈ U, ‖f y - f x‖ ≤ ε := by
    intro x
    refine ⟨f ⁻¹' Metric.closedBall (f x) ε,
      ⟨Metric.isClosed_closedBall.preimage (map_continuous f),
        (IsUltrametricDist.isOpen_closedBall _ hε.ne').preimage (map_continuous f)⟩,
      by simp [hε.le], fun y hy => ?_⟩
    simpa [dist_eq_norm] using hy
  choose U hUclopen hUmem hUapprox using hcov
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover isCompact_univ U
    (fun x => (hUclopen x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hUmem x⟩)
  -- the membership-pattern map into a finite type
  set P : X → (↥t → Bool) := fun x c => decide (x ∈ U ↑c) with hPdef
  have hPlc : IsLocallyConstant P := by
    intro s
    rw [← Set.biUnion_preimage_singleton]
    refine isOpen_biUnion fun b _ => ?_
    have hfib : P ⁻¹' {b} = ⋂ c : ↥t, {x | decide (x ∈ U ↑c) = b c} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, hPdef,
        Set.mem_iInter, Set.mem_setOf_eq]
    rw [hfib]
    refine isOpen_iInter_of_finite fun c => ?_
    cases hb : b c
    · have heq : {x | decide (x ∈ U ↑c) = false} = (U ↑c)ᶜ := by
        ext x; simp
      rw [heq]; exact (hUclopen _).compl.isOpen
    · have heq : {x | decide (x ∈ U ↑c) = true} = U ↑c := by
        ext x; simp
      rw [heq]; exact (hUclopen _).isOpen
  -- value assignment: the value of `f` at the centre of any covering member
  set h : (↥t → Bool) → E := fun b =>
    if hb : ∃ c, b c = true then f ↑(hb.choose) else f hX.some with hhdef
  refine ⟨⟨h ∘ P, hPlc.comp h⟩, fun x => ?_⟩
  have hex : ∃ c : ↥t, P x c = true := by
    obtain ⟨c₀, hmem⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    obtain ⟨hc₀t, hxc₀⟩ := hmem
    exact ⟨⟨c₀, hc₀t⟩, by simp [hPdef, hxc₀]⟩
  change ‖f x - h (P x)‖ ≤ ε
  rw [hhdef]
  simp only [dif_pos hex]
  have hxU : x ∈ U ↑(hex.choose) := by
    have := hex.choose_spec
    simpa [hPdef] using this
  exact hUapprox _ x hxU

/-- **Fubini for p-adic measures**: the two iterated integrals of
`F ∈ C(X × Y, ℤ_[p])` against measures `μ` on `X` and `ν` on `Y` agree:
`∫_X (∫_Y F(x,y) dν) dμ = ∫_Y (∫_X F(x,y) dμ) dν`.

Source: this is the "one checks" of RJW Rem. 3.11 (TeX line 910), reduced to locally
constant functions exactly as in RJW Rem. 3.8 (applied to the curried map). -/
theorem integral_swap [CompactSpace X] [CompactSpace Y]
    (μ : PadicMeasure p X) (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) :
    μ (innerInt p ν F) =
      ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩)) := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨Φ, hΦ⟩ := exists_locallyConstant_norm_sub_le' F.curry hε
  classical
  set R : Finset C(Y, ℤ_[p]) := Φ.range_finite.toFinset with hRdef
  have hmemR : ∀ x : X, Φ x ∈ R := fun x =>
    Φ.range_finite.mem_toFinset.2 ⟨x, rfl⟩
  -- the common middle value
  set S : ℤ_[p] := ∑ g ∈ R,
    μ (LocallyConstant.charFn ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber g) :
        C(X, ℤ_[p])) * ν g with hSdef
  -- pointwise collapse: at `x` only the `g = Φ x` term survives
  have hcollapse : ∀ (x : X) (w : C(Y, ℤ_[p]) → ℤ_[p]),
      (∑ g ∈ R, (LocallyConstant.charFn ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber g) :
          C(X, ℤ_[p])) x * w g) = w (Φ x) := by
    intro x w
    rw [Finset.sum_eq_single (Φ x)]
    · rw [show (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber (Φ x)) : C(X, ℤ_[p])) x = 1 from by
        simp only [LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
        rw [Set.indicator_of_mem (show x ∈ {y | Φ.toFun y = Φ x} from rfl), Pi.one_apply],
        one_mul]
    · intro g _ hgx
      rw [show (LocallyConstant.charFn ℤ_[p]
          (Φ.isLocallyConstant.isClopen_fiber g) : C(X, ℤ_[p])) x = 0 from by
        simp only [LocallyConstant.coe_continuousMap, LocallyConstant.coe_charFn]
        rw [Set.indicator_of_notMem
          (show x ∉ {y | Φ.toFun y = g} from fun hc => hgx hc.symm)],
        zero_mul]
    · intro hx
      exact absurd (hmemR x) hx
  -- LHS ≈ S
  have hL : dist (μ (innerInt p ν F)) S ≤ ε := by
    set mid₁ : C(X, ℤ_[p]) := ∑ g ∈ R,
      ν g • (LocallyConstant.charFn ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber g) :
        C(X, ℤ_[p])) with hmid
    have hμmid : μ mid₁ = S := by
      rw [hmid, map_sum, hSdef]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hbound : ‖innerInt p ν F - mid₁‖ ≤ ε := by
      rw [ContinuousMap.norm_le _ hε.le]
      intro x
      have hmidx : mid₁ x = ν (Φ x) := by
        rw [hmid]
        calc (∑ g ∈ R, ν g • (LocallyConstant.charFn ℤ_[p]
              (Φ.isLocallyConstant.isClopen_fiber g) : C(X, ℤ_[p]))) x
            = ∑ g ∈ R, (LocallyConstant.charFn ℤ_[p]
                (Φ.isLocallyConstant.isClopen_fiber g) : C(X, ℤ_[p])) x * ν g := by
              simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
                Pi.smul_apply, smul_eq_mul]
              exact Finset.sum_congr rfl fun g _ => mul_comm _ _
          _ = ν (Φ x) := hcollapse x ⇑ν
      rw [ContinuousMap.sub_apply, innerInt_apply, hmidx, ← map_sub]
      exact le_trans (norm_apply_le p ν _) (hΦ x)
    calc dist (μ (innerInt p ν F)) S = ‖μ (innerInt p ν F) - μ mid₁‖ := by
          rw [dist_eq_norm, hμmid]
      _ = ‖μ (innerInt p ν F - mid₁)‖ := by rw [map_sub]
      _ ≤ ‖innerInt p ν F - mid₁‖ := norm_apply_le p μ _
      _ ≤ ε := hbound
  -- RHS ≈ S
  have hR : dist (ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩))) S ≤ ε := by
    set mid₂ : C(Y, ℤ_[p]) := ∑ g ∈ R,
      μ (LocallyConstant.charFn ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber g) :
        C(X, ℤ_[p])) • g with hmid
    have hνmid : ν mid₂ = S := by
      rw [hmid, map_sum, hSdef]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_smul, smul_eq_mul]
    have hbound : ‖innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂‖
        ≤ ε := by
      rw [ContinuousMap.norm_le _ hε.le]
      intro y
      -- the column `x ↦ Φ x y`, as a continuous map
      set col : C(X, ℤ_[p]) :=
        ⟨fun x => Φ x y, by
          have : (fun x => Φ x y)
              = (fun g : C(Y, ℤ_[p]) => g y) ∘ ⇑Φ := rfl
          rw [this]
          exact (continuous_eval_const y).comp Φ.continuous⟩ with hcol
      have hmidy : mid₂ y = μ col := by
        rw [hmid]
        have hcolsum : col = ∑ g ∈ R,
            g y • (LocallyConstant.charFn ℤ_[p]
              (Φ.isLocallyConstant.isClopen_fiber g) : C(X, ℤ_[p])) := by
          ext x
          simp only [hcol, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
            ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
          exact ((Finset.sum_congr rfl fun g _ => mul_comm _ _).trans
            (hcollapse x fun g => g y)).symm
        rw [hcolsum, map_sum]
        simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
          Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
      rw [ContinuousMap.sub_apply, innerInt_apply, hmidy, ← map_sub]
      refine le_trans (norm_apply_le p μ _) ?_
      rw [ContinuousMap.norm_le _ hε.le]
      intro x
      have : ((F.comp ⟨Prod.swap, continuous_swap⟩).curry y - col) x
          = F.curry x y - Φ x y := by
        simp [hcol, ContinuousMap.sub_apply]
      rw [this]
      calc ‖F.curry x y - Φ x y‖ = ‖(F.curry x - Φ x) y‖ := by
            rw [ContinuousMap.sub_apply]
        _ ≤ ‖F.curry x - Φ x‖ := ContinuousMap.norm_coe_le_norm _ y
        _ ≤ ε := hΦ x
    calc dist (ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩))) S
        = ‖ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩)) - ν mid₂‖ := by
          rw [dist_eq_norm, hνmid]
      _ = ‖ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂)‖ := by
          rw [map_sub]
      _ ≤ ‖innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩) - mid₂‖ :=
          norm_apply_le p ν _
      _ ≤ ε := hbound
  calc dist (μ (innerInt p ν F)) (ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩)))
      ≤ max (dist (μ (innerInt p ν F)) S)
          (dist S (ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩)))) :=
        dist_triangle_max _ _ _
    _ ≤ ε := max_le hL (by rwa [dist_comm] at hR)

end PadicMeasure
