/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.IwasawaProof.FundamentalSequence
import PadicLFunctions.IwasawaProof.Generators
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Continuity of the Coleman map (RJW §13 / IMC analytic core)

This file builds the topology/continuity layer needed to cross from the dense
`ℤ_p[𝒢]`-span of Dirac scalars to the full `Λ(𝒢)` action, closing the §12.5 image
computation `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`.

## Main constructions

* `PadicMeasure.instTopologicalSpace`: the weak-* topology on `Λ = C(X,ℤ_[p]) →ₗ ℤ_[p]`
  (pointwise convergence: `μ_j → μ` iff `μ_j f → μ f` for every `f`), as the topology
  induced by `DFunLike.coe` from the product topology on `C(X,ℤ_[p]) → ℤ_[p]`.
* `Continuous (evalPi · n)`: evaluation at `π_n` is coefficientwise-continuous on
  `ℤ_p⟦T⟧` (the `PowerSeries.WithPiTopology`).
* `Continuous (colemanPipe p)`: the post-`colemanSeries` pipeline
  `g ↦ unitsCmul invCM ((mahler⁻¹ (dlog g)).comp extendByZero)` is weak-* continuous
  on the `𝒩`-fixed units `𝒲ˣ` (where `Ring.inverse` is continuous via the
  compact-Hausdorff homeomorphism trick), and `Col u = colemanPipe (colemanSeries u)`.
-/

open PadicLFunctions PadicLFunctions.Coleman
open scoped PowerSeries.WithPiTopology fwdDiff

noncomputable section

/-! ## The weak-* topology on `PadicMeasure` -/

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]
variable {X : Type*} [TopologicalSpace X]

/-- The weak-* topology on `Λ(X) = C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`: the coarsest topology making
every evaluation `μ ↦ μ f` continuous, i.e. the topology of pointwise convergence on
functionals. Induced from the product topology on `C(X,ℤ_[p]) → ℤ_[p]` by the coercion. -/
instance instTopologicalSpace : TopologicalSpace (PadicMeasure p X) :=
  TopologicalSpace.induced (DFunLike.coe) inferInstance

/-- Evaluation `μ ↦ μ f` is weak-* continuous. -/
theorem continuous_eval (f : C(X, ℤ_[p])) :
    Continuous (fun μ : PadicMeasure p X => μ f) :=
  (continuous_apply f).comp continuous_induced_dom

/-- A net/map into `PadicMeasure` is continuous iff every evaluation is. -/
theorem continuous_iff_eval {Y : Type*} [TopologicalSpace Y] (g : Y → PadicMeasure p X) :
    Continuous g ↔ ∀ f : C(X, ℤ_[p]), Continuous (fun y => g y f) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- `PadicMeasure p X` is Hausdorff (weak-*): two measures equal at every `f` are equal. -/
instance instT2Space : T2Space (PadicMeasure p X) := by
  refine ⟨fun μ ν hμν => ?_⟩
  exact separated_by_continuous continuous_induced_dom (fun h => hμν (DFunLike.coe_injective h))

/-- Right multiplication `s ↦ s * ν` is weak-* continuous on `Λ(ℤ_p^×)`: by the convolution
formula `(s * ν) f = s (innerInt ν (f.comp mulCM₂))`, it is the (continuous) evaluation of `s`
at the *fixed* function `innerInt ν (f.comp mulCM₂)` (independent of `s`). -/
theorem continuous_mul_right (ν : PadicMeasure p ℤ_[p]ˣ) :
    Continuous (fun s : PadicMeasure p ℤ_[p]ˣ => s * ν) := by
  rw [continuous_iff_eval]
  intro f
  simpa only [PadicMeasure.units_mul_apply] using
    continuous_eval p (PadicMeasure.innerInt p ν (f.comp (PadicMeasure.unitsMulCM₂ p)))

/-- Scalar multiplication `c ↦ c • μ` (for a fixed measure `μ`) is weak-* continuous in the
scalar `c : ℤ_[p]`: `(c • μ) f = c * (μ f)` is continuous in `c`. -/
theorem continuous_smul_scalar (μ : PadicMeasure p X) :
    Continuous (fun c : ℤ_[p] => c • μ) := by
  rw [continuous_iff_eval]
  intro f
  simp only [LinearMap.smul_apply, smul_eq_mul]
  exact continuous_id.mul continuous_const

/-- **A closed additive subgroup of `Λ` is a `ℤ_[p]`-submodule.** Since `ℕ ↪ ℤ_[p]` is dense
and `c ↦ c • x` is weak-* continuous, `ℤ_[p] • x = closure(ℤ • x) ⊆ H` for `x ∈ H` closed. -/
theorem smul_mem_of_isClosed_subgroup {H : AddSubgroup (PadicMeasure p X)}
    (hH : IsClosed (H : Set (PadicMeasure p X))) (c : ℤ_[p]) {x : PadicMeasure p X}
    (hx : x ∈ H) : c • x ∈ H := by
  -- `ℕ • x ⊆ H`, `ℕ ↪ ℤ_[p]` dense, `c ↦ c • x` continuous ⟹ `c • x ∈ closure H = H`
  have hnat : ∀ k : ℕ, (k : ℤ_[p]) • x ∈ H := by
    intro k
    rw [Nat.cast_smul_eq_nsmul ℤ_[p] k x]
    exact nsmul_mem hx k
  have hmem : c • x ∈ closure (H : Set (PadicMeasure p X)) := by
    have hsub : ((fun c : ℤ_[p] => c • x) '' Set.range (Nat.cast : ℕ → ℤ_[p]))
        ⊆ (H : Set (PadicMeasure p X)) := by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hnat k
    have hrange : Set.range (fun c : ℤ_[p] => c • x)
        ⊆ closure ((fun c : ℤ_[p] => c • x) '' Set.range (Nat.cast : ℕ → ℤ_[p])) := by
      have h1 : Set.range (fun c : ℤ_[p] => c • x)
          = (fun c : ℤ_[p] => c • x) '' closure (Set.range (Nat.cast : ℕ → ℤ_[p])) := by
        rw [PadicInt.denseRange_natCast.closure_range, Set.image_univ]
      rw [h1]
      exact image_closure_subset_closure_image (continuous_smul_scalar p x)
    exact closure_mono hsub (hrange ⟨c, rfl⟩)
  rwa [hH.closure_eq] at hmem

/-! ### Density of the Dirac span (weak-*) -/

/-- The level-`n` Dirac approximation of a measure on `ℤ_p^×`:
`D_n(μ) = ∑_{g ∈ (ℤ/p^n)ˣ} μ(𝟙_{g\text{-fibre}}) · [rep g]`, a `ℤ_[p]`-combination of
Dirac masses agreeing with `μ` on every level-`n` indicator. -/
def approxDirac (μ : PadicMeasure p ℤ_[p]ˣ) (n : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  if hn : 0 < n then
    ∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) •
      dirac p ((unitsToZModPow_surjective p n hn g).choose)
  else 0

/-- `D_n(μ)` agrees with `μ` on the level-`n` indicators: `D_n(μ)(𝟙_h) = μ(𝟙_h)`. -/
theorem approxDirac_levelChar {μ : PadicMeasure p ℤ_[p]ˣ} {n : ℕ} (hn : 0 < n)
    (h : (ZMod (p ^ n))ˣ) : approxDirac p μ n (levelChar p n h) = μ (levelChar p n h) := by
  classical
  rw [approxDirac, dif_pos hn, show (∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) •
        dirac p ((unitsToZModPow_surjective p n hn g).choose)) (levelChar p n h)
      = ∑ g : (ZMod (p ^ n))ˣ, μ (levelChar p n g) *
          (dirac p ((unitsToZModPow_surjective p n hn g).choose)) (levelChar p n h) from by
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun g _ => by rw [LinearMap.smul_apply, smul_eq_mul]]
  rw [Finset.sum_eq_single h]
  · rw [dirac_apply, levelChar_apply_eq p (unitsToZModPow_surjective p n hn h).choose_spec, mul_one]
  · intro g _ hgh
    rw [dirac_apply, levelChar_apply_ne p ?_, mul_zero]
    rw [(unitsToZModPow_surjective p n hn g).choose_spec]; exact hgh
  · exact fun hh => absurd (Finset.mem_univ _) hh

/-- `D_n(μ)` agrees with `μ` on any locally constant function `g` that factors through level
`n` (i.e. constant on level-`n` fibres). -/
theorem approxDirac_apply_eq {μ : PadicMeasure p ℤ_[p]ˣ} {n : ℕ} (hn : 0 < n)
    {g : LocallyConstant ℤ_[p]ˣ ℤ_[p]}
    (hfac : ∀ u v : ℤ_[p]ˣ, unitsToZModPow p n u = unitsToZModPow p n v → g u = g v) :
    approxDirac p μ n (g : C(ℤ_[p]ˣ, ℤ_[p])) = μ (g : C(ℤ_[p]ˣ, ℤ_[p])) := by
  classical
  -- `g = ∑_c g(rep c) • 𝟙_c` (level-`n` indicator decomposition, cf. `levelMap_jointly_injective`)
  have hg : (g : C(ℤ_[p]ˣ, ℤ_[p]))
      = ∑ c : (ZMod (p ^ n))ˣ,
          g ((unitsToZModPow_surjective p n hn c).choose) • levelChar p n c := by
    ext u
    rw [show (∑ c : (ZMod (p ^ n))ˣ,
        g ((unitsToZModPow_surjective p n hn c).choose) • levelChar p n c) u
        = ∑ c : (ZMod (p ^ n))ˣ,
          g ((unitsToZModPow_surjective p n hn c).choose) * levelChar p n c u from by
      simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
        Pi.smul_apply, smul_eq_mul]]
    rw [Finset.sum_eq_single (unitsToZModPow p n u)]
    · rw [levelChar_apply_eq p rfl, mul_one]
      exact (hfac _ u ((unitsToZModPow_surjective p n hn _).choose_spec)).symm
    · intro c _ hcu
      rw [levelChar_apply_ne p fun hc => hcu hc.symm, mul_zero]
    · exact fun hu => absurd (Finset.mem_univ _) hu
  rw [hg, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_smul, approxDirac_levelChar p hn c]

/-- **The Dirac span is weak-* dense**: the level-`n` Dirac approximations converge to `μ`,
`D_n(μ) f → μ f` for every test `f`. Given `ε`, approximate `f` by an lc `g` (`‖f-g‖ ≤ ε`)
factoring through some level `N`; for `n ≥ N`, `D_n(μ)` agrees with `μ` on `g`, so
`‖D_n(μ) f - μ f‖ ≤ ‖f - g‖ ≤ ε` by the operator bound `‖·f‖ ≤ ‖f‖`. -/
theorem tendsto_approxDirac (μ : PadicMeasure p ℤ_[p]ˣ) :
    Filter.Tendsto (fun n => approxDirac p μ n) Filter.atTop (nhds μ) := by
  rw [nhds_induced, Filter.tendsto_comap_iff, tendsto_pi_nhds]
  intro f
  change Filter.Tendsto (fun n => approxDirac p μ n f) Filter.atTop (nhds (μ f))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg⟩ := exists_locallyConstant_norm_sub_le p f (half_pos hε)
  have hgε : ‖f - (g : C(ℤ_[p]ˣ, ℤ_[p]))‖ < ε := lt_of_le_of_lt hg (by linarith)
  obtain ⟨N, hN, hfac⟩ := exists_level_factorization p g
  refine ⟨N, fun n hn => ?_⟩
  have hnpos : 0 < n := lt_of_lt_of_le hN hn
  -- `g` factors through level `n ≥ N`
  have hfacn : ∀ u v : ℤ_[p]ˣ, unitsToZModPow p n u = unitsToZModPow p n v → g u = g v := by
    intro u v huv
    exact hfac u v (by rw [unitsToZModPow_le p hn u, unitsToZModPow_le p hn v, huv])
  have hgeq : approxDirac p μ n (g : C(ℤ_[p]ˣ, ℤ_[p])) = μ (g : C(ℤ_[p]ˣ, ℤ_[p])) :=
    approxDirac_apply_eq p hnpos hfacn
  -- `D_n(μ) f − μ f = D_n(μ)(f − g) + μ(g − f)`
  have hsplit : approxDirac p μ n f - μ f
      = approxDirac p μ n (f - (g : C(ℤ_[p]ˣ, ℤ_[p]))) + μ ((g : C(ℤ_[p]ˣ, ℤ_[p])) - f) := by
    rw [map_sub, map_sub, hgeq]; ring
  rw [dist_eq_norm, hsplit]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
  rw [max_lt_iff]
  refine ⟨lt_of_le_of_lt (norm_apply_le p _ _) hgε, ?_⟩
  refine lt_of_le_of_lt (norm_apply_le p _ _) ?_
  rw [show (g : C(ℤ_[p]ˣ, ℤ_[p])) - f = -(f - (g : C(ℤ_[p]ˣ, ℤ_[p]))) from by ring, norm_neg]
  exact hgε

/-- **Closure-crossing for a principal ideal**: if `H` is a *closed* additive subgroup of
`Λ(ℤ_p^×)` containing `[a] · ν` for every group element `a ∈ ℤ_p^×`, then it contains the whole
principal ideal `r · ν` (`r ∈ Λ`). The Dirac span is weak-* dense (`tendsto_approxDirac`) and
`s ↦ s · ν` is continuous (`continuous_mul_right`), so `D_n(r) · ν → r · ν` with each
`D_n(r) · ν ∈ H` (a finite `ℤ_[p]`-combination of `[a] · ν`, using `H` `ℤ_[p]`-stable as a
closed subgroup), hence `r · ν ∈ closure H = H`. -/
theorem mul_mem_of_dirac_mul_mem {H : AddSubgroup (PadicMeasure p ℤ_[p]ˣ)}
    (hH : IsClosed (H : Set (PadicMeasure p ℤ_[p]ˣ))) {ν : PadicMeasure p ℤ_[p]ˣ}
    (hν : ∀ a : ℤ_[p]ˣ, dirac p a * ν ∈ H) (r : PadicMeasure p ℤ_[p]ˣ) :
    r * ν ∈ H := by
  classical
  -- each `D_n(r) · ν ∈ H`
  have hstep : ∀ n, approxDirac p r n * ν ∈ H := by
    intro n
    rw [approxDirac]
    by_cases hn : 0 < n
    · rw [dif_pos hn, Finset.sum_mul]
      refine AddSubgroup.sum_mem _ fun g _ => ?_
      rw [smul_mul_assoc]
      exact smul_mem_of_isClosed_subgroup p hH _ (hν _)
    · rw [dif_neg hn, zero_mul]; exact zero_mem _
  -- `D_n(r) · ν → r · ν`
  have htend : Filter.Tendsto (fun n => approxDirac p r n * ν) Filter.atTop (nhds (r * ν)) :=
    ((continuous_mul_right p ν).tendsto r).comp (tendsto_approxDirac p r)
  have hmem : r * ν ∈ closure (H : Set (PadicMeasure p ℤ_[p]ˣ)) :=
    mem_closure_of_tendsto htend (Filter.Eventually.of_forall hstep)
  rwa [hH.closure_eq, SetLike.mem_coe] at hmem

/-! ### Compactness of `Λ(ℤ_p^×)` and closedness of the ζ-ideal -/

/-- The coercion `DFunLike.coe : Λ(ℤ_p^×) → (C(ℤ_p^×,ℤ_[p]) → ℤ_[p])` has *closed* range:
its image is exactly the functionals satisfying additivity and `ℤ_[p]`-homogeneity, two
closed conditions (each is an intersection of equalities of weak-* continuous evaluations). -/
theorem isClosed_range_coe :
    IsClosed (Set.range (DFunLike.coe :
      PadicMeasure p ℤ_[p]ˣ → (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]))) := by
  have hset : Set.range (DFunLike.coe :
        PadicMeasure p ℤ_[p]ˣ → (C(ℤ_[p]ˣ, ℤ_[p]) → ℤ_[p]))
      = {F | (∀ a b, F (a + b) = F a + F b)} ∩ {F | ∀ (c : ℤ_[p]) a, F (c • a) = c • F a} := by
    ext F
    simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨μ, rfl⟩; exact ⟨fun a b => map_add μ a b, fun c a => map_smul μ c a⟩
    · rintro ⟨hadd, hsmul⟩; exact ⟨{ toFun := F, map_add' := hadd, map_smul' := hsmul }, rfl⟩
  rw [hset]
  apply IsClosed.inter
  · rw [Set.setOf_forall]; refine isClosed_iInter fun a => ?_
    rw [Set.setOf_forall]; refine isClosed_iInter fun b => ?_
    exact isClosed_eq (continuous_apply (a + b)) ((continuous_apply a).add (continuous_apply b))
  · rw [Set.setOf_forall]; refine isClosed_iInter fun c => ?_
    rw [Set.setOf_forall]; refine isClosed_iInter fun a => ?_
    exact isClosed_eq (continuous_apply (c • a)) ((continuous_apply a).const_smul c)

/-- **`Λ(ℤ_p^×)` is weak-* compact** (a p-adic Banach–Alaoglu). The coercion is inducing onto
the compact product `∏_f ℤ_[p]` (Tychonoff: `ℤ_[p]` compact) with *closed* range
(`isClosed_range_coe`), so `Λ(ℤ_p^×)` is a closed subspace of a compact space. -/
instance instCompactSpace : CompactSpace (PadicMeasure p ℤ_[p]ˣ) := by
  rw [← isCompact_univ_iff]
  have hind : Topology.IsInducing
      (DFunLike.coe : PadicMeasure p ℤ_[p]ˣ → _) := ⟨rfl⟩
  rw [hind.isCompact_iff, Set.image_univ]
  exact (isClosed_range_coe p).isCompact

/-- **Every principal ideal `(ν)` of `Λ(ℤ_p^×)` is weak-* closed**: it is the image of the
compact space `Λ` under the continuous map `r ↦ r·ν` (`continuous_mul_right`), hence compact,
hence closed (`Λ` is Hausdorff). -/
theorem isClosed_span_singleton (ν : PadicMeasure p ℤ_[p]ˣ) :
    IsClosed ((Ideal.span {ν} : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
      Set (PadicMeasure p ℤ_[p]ˣ)) := by
  have hrange : ((Ideal.span {ν} : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
        Set (PadicMeasure p ℤ_[p]ˣ)) = Set.range (fun r => r * ν) := by
    ext x
    simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Set.mem_range]
    exact ⟨fun ⟨r, hr⟩ => ⟨r, by rw [hr, mul_comm]⟩, fun ⟨r, hr⟩ => ⟨r, by rw [← hr, mul_comm]⟩⟩
  rw [hrange, ← Set.image_univ]
  exact (isCompact_univ.image (continuous_mul_right p ν)).isClosed

/-- **`I(𝒢)ζ_p` is weak-* closed.** By the principal description `I(𝒢)ζ_p = (zetaNum a₀)`
(`zetaIdeal_eq_span`, the `([a₀]−1)·ζ_p`-witness at the topological generator `a₀`), it is a
principal ideal, hence closed by `isClosed_span_singleton` (compactness of `Λ`). This supplies
the *closedness* half of the `⊆` direction of the §12.5 image computation — independently of the
image identity itself, so it is not circular. -/
theorem isClosed_zetaIdeal (hp2 : p ≠ 2) :
    IsClosed ((zetaIdeal p hp2 : Ideal (PadicMeasure p ℤ_[p]ˣ)) :
      Set (PadicMeasure p ℤ_[p]ˣ)) := by
  have hb_gen : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n
        (exists_nat_topological_generator p hp2).choose_spec.choose) = ⊤ :=
    (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2
  have hνeq : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
        (dirac p (exists_nat_topological_generator p hp2).choose_spec.choose - 1)
        * padicZeta p hp2
      = algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
          (zetaNum p (exists_nat_topological_generator p hp2).choose) := by
    rw [padicZeta]; exact IsLocalization.mk'_spec' (QuotientField p) _ _
  rw [zetaIdeal_eq_span p hp2 hb_gen hνeq]
  exact isClosed_span_singleton p _

end PadicMeasure

/-! ## Continuity of evaluation at `π_n` -/

namespace PadicLFunctions.Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- `PowerSeries ℤ_[p]` with the coefficientwise topology is (sequentially) metrizable, so
continuity equals sequential continuity (it is the countable product `(Unit →₀ ℕ) → ℤ_[p]`
of the metric space `ℤ_[p]`). -/
instance : SequentialSpace (PowerSeries ℤ_[p]) :=
  inferInstanceAs (SequentialSpace ((Unit →₀ ℕ) → ℤ_[p]))

/-- **Evaluation at `π_n` is continuous** (`n ≥ 1`): `f ↦ f(π_n)` is sequentially continuous
on `ℤ_p⟦T⟧` (`tendsto_evalPi_of_tendsto`), and `ℤ_p⟦T⟧` is sequential, so it is continuous. -/
theorem continuous_evalPi {n : ℕ} (hn : 1 ≤ n) :
    Continuous (fun f : PowerSeries ℤ_[p] => evalPi p f n) := by
  refine SeqContinuous.continuous (fun {g h} hg => ?_)
  exact tendsto_evalPi_of_tendsto p hg hn

/-! ## Continuity of the level norm `N_{n+1,n}` (ST3a, the tower-descent gateway)

In the inverse-limit topology a global `m ∈ NormCompatUnits` approximating `u` at the top
level `N` approximates it at every lower level `k < N` *for free*, because both are
norm-compatible: `u.elems k = N_{k+1,k}(N_{k+2,k+1}(⋯ u.elems N))` and likewise for `m`. This
free propagation is exactly the continuity of the level norm `N_{n+1,n} = Algebra.norm (K_n)`
on the finite extension `K_{n+1}/K_n`: `Algebra.norm = det ∘ lmul`, and on the
finite-dimensional `K_n`-algebra `K_{n+1}` both `lmul` (continuous bilinear,
`ContinuousLinearMap.mul`) and `det` (`ContinuousLinearMap.continuous_det`) are continuous.
The `K_n`-subspace topology on `K_{n+1}` matches its finite-dimensional module topology, so the
continuity transfers to the `ℂ_[p]`-coordinate form used in the tower assembly. -/

/-- `ℂ_[p]` is a normed `K_n`-algebra (`K_n ⊆ ℂ_[p]` carries the restricted norm, and the
algebra scalar action is multiplication, so `‖r • x‖ = ‖(r : ℂ_[p])‖ · ‖x‖`). The
`NormedAlgebra (subfield) (ambient)` instance is not provided by mathlib, so we supply it
locally for the level-norm continuity argument. -/
local instance instNormedAlgebra_K_Cp (n : ℕ) : NormedAlgebra (K p n) ℂ_[p] where
  norm_smul_le r x := by rw [Algebra.smul_def, norm_mul]; rfl

/-- The relative extension `K_{n+1} = extendScalars (K_n ≤ K_{n+1})` is a nontrivially normed
field for the `K_n`-structure (the same `ℂ_[p]`-subspace norm as for the `ℚ_[p]`-structure).
Supplied locally because the abstract `IntermediateField (K_n) ℂ_[p]` instance does not fire
through the nested-subfield coercion. -/
local instance instNNF_extendScalars (n : ℕ) :
    NontriviallyNormedField (IntermediateField.extendScalars (K_le_succ p n)) where
  __ := SubfieldClass.toNormedField (IntermediateField.extendScalars (K_le_succ p n))
  non_trivial := by
    obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial (K p n) _
    exact ⟨algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) k,
      by simpa using hk⟩

/-- `K_{n+1} = extendScalars (K_n ≤ K_{n+1})` is a normed `K_n`-space (restricted `ℂ_[p]`
norm; scalar action is multiplication). -/
local instance instNS_extendScalars (n : ℕ) :
    NormedSpace (K p n) (IntermediateField.extendScalars (K_le_succ p n)) where
  norm_smul_le r x := by
    change ‖(r • x : IntermediateField.extendScalars (K_le_succ p n))‖ ≤ _
    rw [Algebra.smul_def, norm_mul]; rfl

/-- `K_n` is complete (finite-dimensional over the complete `ℚ_[p]`). -/
local instance instComplete_K (n : ℕ) : CompleteSpace (K p n) := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  haveI : FiniteDimensional ℚ_[p] (K p n) :=
    IsCyclotomicExtension.finiteDimensional {p ^ n} ℚ_[p] (K p n)
  exact FiniteDimensional.complete ℚ_[p] (K p n)

set_option synthInstance.maxHeartbeats 1000000 in
-- the `det ∘ lmul` continuity runs through the nested `IntermediateField (K p n) (extendScalars …)`
-- layer (`finrank`/instance synthesis on the relative extension); both bumps exceed the defaults
set_option maxHeartbeats 1000000 in
/-- **ST3a — the level norm is continuous** (RJW §12.5 tower-descent gateway): the map
`x ↦ (N_{n+1,n}(x) : ℂ_[p])` is continuous on `K_{n+1}` (with the `ℂ_[p]`-subspace topology).
`N_{n+1,n} = Algebra.norm (K_n) = det ∘ lmul` on the finite extension `K_{n+1}/K_n`; both
`lmul` (`ContinuousLinearMap.mul`) and `det` (`ContinuousLinearMap.continuous_det`) are
continuous, and the inclusion `K_{n+1} ↪ ℂ_[p]` and projection `K_n ↪ ℂ_[p]` are continuous.
This propagates a top-level approximation down the norm-compatible tower (ST3c). -/
theorem continuous_levelNorm (n : ℕ) :
    Continuous (fun x : K p (n + 1) => (levelNorm p n (x : ℂ_[p]) : ℂ_[p])) := by
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    IsCyclotomicExtension.finiteDimensional {p ^ (n + 1)} ℚ_[p] (K p (n + 1))
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  set E := IntermediateField.extendScalars (K_le_succ p n) with hE
  -- the carrier-identity map `K_{n+1} → E` is continuous (subspace topology, `val`-compatible)
  have hmemE : ∀ x : K p (n + 1), (x : ℂ_[p]) ∈ E := fun x =>
    (IntermediateField.mem_extendScalars (K_le_succ p n)).2 x.2
  have htoE : Continuous (fun x : K p (n + 1) => (⟨(x : ℂ_[p]), hmemE x⟩ : E)) := by
    rw [continuous_induced_rng]; exact continuous_induced_dom
  -- `Algebra.norm (K_n) = det ∘ lmul` is continuous on the finite `K_n`-algebra `E`
  have hnorm : Continuous (fun y : E => Algebra.norm (K p n) y) := by
    simp_rw [Algebra.norm_apply]
    exact (ContinuousLinearMap.continuous_det (𝕜 := K p n) (E := E)).comp
      (ContinuousLinearMap.mul (K p n) E).continuous
  -- coercion `K_n ↪ ℂ_[p]` is continuous (subspace topology)
  have hcoe : Continuous (fun z : K p n => (z : ℂ_[p])) := continuous_induced_dom
  have heq : (fun x : K p (n + 1) => (levelNorm p n (x : ℂ_[p]) : ℂ_[p]))
      = fun x : K p (n + 1) =>
        ((Algebra.norm (K p n) (⟨(x : ℂ_[p]), hmemE x⟩ : E) : K p n) : ℂ_[p]) := by
    funext x; rw [levelNorm_apply p n x.2]
  rw [heq]
  exact hcoe.comp (hnorm.comp htoE)

/-! ## The inverse-limit topology on `NormCompatUnits` (the source side, ST1)

The Coleman map's source `𝒰_∞ = NormCompatUnits` is an inverse limit of the local unit groups
`𝒪_n^×`. We give it the coarsest topology making every level coordinate
`u ↦ (u.elems n : ℂ_[p])` continuous (the *induced*/inverse-limit topology), exactly mirroring
the weak-* topology `PadicMeasure.instTopologicalSpace` on the target. With it the level
coordinates are continuous (`continuous_elems`), continuity *into* `𝒰_∞` is checked
coordinatewise (`continuous_iff_elems`), and `𝒰_∞` is Hausdorff (`elems`-injective). -/

/-- The coordinate map `u ↦ (n ↦ (u.elems n : ℂ_[p]))` of a norm-compatible unit system into
the product `∏ n, ℂ_[p]`. The inverse-limit topology on `𝒰_∞` is induced along this map. -/
def elemsCoe (u : NormCompatUnits p) : ℕ → ℂ_[p] := fun n => ((u.elems n : ℂ_[p]ˣ) : ℂ_[p])

/-- **The inverse-limit topology on `𝒰_∞ = NormCompatUnits`**: the coarsest topology making
every level coordinate `u ↦ (u.elems n : ℂ_[p])` continuous, induced from the product topology
on `∏ n, ℂ_[p]` along `elemsCoe`. (Source-side analogue of `PadicMeasure.instTopologicalSpace`.)
-/
instance instTopologicalSpace : TopologicalSpace (NormCompatUnits p) :=
  TopologicalSpace.induced (elemsCoe p) inferInstance

/-- **The level coordinate `u ↦ (u.elems n : ℂ_[p])` is continuous** on `𝒰_∞`. -/
theorem continuous_elems (n : ℕ) :
    Continuous (fun u : NormCompatUnits p => ((u.elems n : ℂ_[p]ˣ) : ℂ_[p])) :=
  (continuous_apply n).comp (continuous_induced_dom (f := elemsCoe p))

/-- **Continuity into `𝒰_∞` is coordinatewise**: a map `g : Y → 𝒰_∞` is continuous iff every
level coordinate `y ↦ (g y).elems n : ℂ_[p]` is. (Source-side analogue of
`PadicMeasure.continuous_iff_eval`.) -/
theorem continuous_iff_elems {Y : Type*} [TopologicalSpace Y] (g : Y → NormCompatUnits p) :
    Continuous g ↔ ∀ n : ℕ, Continuous (fun y => (((g y).elems n : ℂ_[p]ˣ) : ℂ_[p])) := by
  rw [continuous_induced_rng, continuous_pi_iff]
  rfl

/-- `𝒰_∞` is Hausdorff: two systems agreeing at every level coordinate are equal
(`NormCompatUnits.ext` + `Units.ext`). -/
instance instT2Space : T2Space (NormCompatUnits p) := by
  refine ⟨fun u v huv => ?_⟩
  refine separated_by_continuous continuous_induced_dom (fun h => huv ?_)
  exact NormCompatUnits.ext (funext fun n => Units.ext (congrFun h n))

/-- **The unit-valued level coordinate `u ↦ u.elems n : ℂ_[p]ˣ` is continuous** on `𝒰_∞`. Since
`Units.val : ℂ_[p]ˣ → ℂ_[p]` is a topological embedding on the normed field `ℂ_[p]`
(`Units.isEmbedding_val₀`), continuity into `ℂ_[p]ˣ` is equivalent to continuity of `val ∘ ·`,
which is `continuous_elems`. -/
theorem continuous_elemsUnits (n : ℕ) :
    Continuous (fun u : NormCompatUnits p => u.elems n) := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact continuous_elems p n

/-- **T1220 — the inverse-limit closure bridge**: since the topology on `𝒰_∞` is induced along
`elemsCoe`, membership in the closure of a set `S` transfers to the product `ℕ → ℂ_[p]`:
`u ∈ closure S ↔ elemsCoe u ∈ closure (elemsCoe '' S)`. This is the foundation for the levelwise
density characterisation (RJW LemmaGeneratorCinfty1 inverse-limit step). -/
theorem mem_closure_iff_elemsCoe {S : Set (NormCompatUnits p)} {u : NormCompatUnits p} :
    u ∈ closure S ↔ elemsCoe p u ∈ closure (elemsCoe p '' S) :=
  closure_induced

/-- **T1220b — `Col` is insensitive to the level-`0` coordinate**: `Col u = Col v` whenever the
unit systems agree at every level `n ≥ 1`. `Col` factors through `colemanSeries`, which is pinned
by the `n ≥ 1` interpolation data (`colemanSeries_eq_iff`; the vestigial `elems 0` is unconstrained
by `compat`). This is the lever that lets the tower-density argument normalise the free level-`0`
coordinate without changing `Col`. -/
theorem Col_eq_of_elems_eq {u v : NormCompatUnits p} (h : ∀ n, 1 ≤ n → u.elems n = v.elems n) :
    Col p u = Col p v := by
  have hcs : colemanSeries p u = colemanSeries p v := by rw [colemanSeries_eq_iff]; exact h
  unfold Col
  rw [hcs]

/-- `levelNorm p n` is continuous on `K_{n+1}` as a map of ambient `ℂ_[p]` values (ST3a recast
through `ContinuousOn`, so the `ε`-`δ` lives in the ambient metric, not the subtype metric). -/
private theorem continuousOn_levelNorm (n : ℕ) :
    ContinuousOn (levelNorm p n) (K p (n + 1) : Set ℂ_[p]) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_levelNorm p n

/-- **Descent control**: for a norm-compatible system `u`, matching another system `s` at the top
level `N` within a suitable `δ` controls every level `1 ≤ n ≤ N`. Proof by `Nat.le_induction` on
`N`, threading the tolerance one `levelNorm`-step at a time (`continuousOn_levelNorm`, the
norm-compatibility `compat`). -/
private theorem exists_delta_descent (u : NormCompatUnits p) :
    ∀ N : ℕ, 1 ≤ N → ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ s : NormCompatUnits p,
      ‖(s.elems N : ℂ_[p]) - (u.elems N : ℂ_[p])‖ < δ →
      ∀ n, 1 ≤ n → n ≤ N → ‖(s.elems n : ℂ_[p]) - (u.elems n : ℂ_[p])‖ < ε := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
    intro ε hε
    refine ⟨ε, hε, fun s hs n hn1 hnN => ?_⟩
    obtain rfl : n = 1 := le_antisymm hnN hn1
    exact hs
  | succ N hN ih =>
    intro ε hε
    obtain ⟨δN, hδNpos, hihN⟩ := ih ε hε
    have huK1 : (u.elems (N + 1) : ℂ_[p]) ∈ K p (N + 1) := (Subring.mem_inf.1 (u.mem (N + 1))).1
    obtain ⟨δ', hδ'pos, hδ'⟩ :=
      Metric.continuousOn_iff.1 (continuousOn_levelNorm p N) _ huK1 δN hδNpos
    refine ⟨min ε δ', lt_min hε hδ'pos, fun s hs n hn1 hnN1 => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hnN1) with hlt | rfl
    · -- `n ≤ N`: propagate level-(N+1) closeness to level `N`, then apply the IH
      have hsK1 : (s.elems (N + 1) : ℂ_[p]) ∈ K p (N + 1) := (Subring.mem_inf.1 (s.mem (N + 1))).1
      have hstep := hδ' _ hsK1 (by
        rw [dist_eq_norm]; exact lt_of_lt_of_le hs (min_le_right _ _))
      rw [dist_eq_norm, s.compat N hN, u.compat N hN] at hstep
      exact hihN s hstep n hn1 (Nat.lt_succ_iff.1 hlt)
    · -- `n = N+1`
      exact lt_of_lt_of_le hs (min_le_left _ _)

/-- **T1221 — the inverse-limit (levelwise) density characterisation** (RJW LemmaGeneratorCinfty1
inverse-limit step): for a subgroup `S` whose members all share `u`'s level-`0` coordinate, if
each level-`n` (`n ≥ 1`) coordinate of `u` lies in the closure of the level-`n` image of `S`, then
`u ∈ closure S`. The level-`0` coordinate is unconstrained by `compat`, so it is matched by the
shared-value hypothesis; the higher levels are matched by a single `s ∈ S` close to `u` at the top
constrained level (`exists_delta_descent` propagates down the tower). -/
theorem mem_closure_of_levelwise {S : Subgroup (NormCompatUnits p)} {u : NormCompatUnits p}
    (h0 : ∀ s ∈ S, (s.elems 0 : ℂ_[p]) = (u.elems 0 : ℂ_[p]))
    (h : ∀ n, 1 ≤ n → (u.elems n : ℂ_[p]) ∈
      closure ((fun s : NormCompatUnits p => (s.elems n : ℂ_[p])) '' (S : Set (NormCompatUnits p)))) :
    u ∈ closure (S : Set (NormCompatUnits p)) := by
  rw [mem_closure_iff_elemsCoe, mem_closure_iff_nhds]
  intro t ht
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, V, hV, hVt⟩ := ht
  -- per-coordinate radius `εf n` with `ball (elemsCoe u n) (εf n) ⊆ V n`
  choose εf hεfpos hεfsub using fun n => Metric.mem_nhds_iff.1 (hV n)
  rcases I.eq_empty_or_nonempty with hIempty | hIne
  · -- empty box: any element of `S` works (`1 ∈ S`)
    exact ⟨elemsCoe p 1,
      hVt (Set.mem_pi.2 fun n hn => ((Set.mem_empty_iff_false n).1 (hIempty ▸ hn)).elim),
      ⟨1, one_mem _, rfl⟩⟩
  · -- nonempty: a single `s ∈ S` close at level `N' = max(bound, 1)` matches all of `I`
    obtain ⟨b, hb⟩ := hI.bddAbove
    have hN'1 : 1 ≤ max b 1 := le_max_right _ _
    have hIfne : hI.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hI).2 hIne
    set ε := hI.toFinset.inf' hIfne εf with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef, Finset.lt_inf'_iff]; exact fun n _ => hεfpos n
    obtain ⟨δ, hδpos, hδ⟩ := exists_delta_descent p u (max b 1) hN'1 ε hεpos
    obtain ⟨_, ⟨s, hsS, rfl⟩, hsclose⟩ := Metric.mem_closure_iff.1 (h _ hN'1) δ hδpos
    refine ⟨elemsCoe p s, hVt (Set.mem_pi.2 fun n hnI => ?_), ⟨s, hsS, rfl⟩⟩
    refine hεfsub n ?_
    rw [Metric.mem_ball]
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · -- level 0: shared coordinate
      simp only [elemsCoe, h0 s hsS, dist_self]; exact hεfpos 0
    · -- level n ≥ 1: descent from level `max b 1`
      have hnN' : n ≤ max b 1 := le_trans (hb hnI) (le_max_left _ _)
      have hεle : ε ≤ εf n := Finset.inf'_le εf (hI.mem_toFinset.2 hnI)
      have hsN' : ‖(s.elems (max b 1) : ℂ_[p]) - (u.elems (max b 1) : ℂ_[p])‖ < δ := by
        rw [← dist_eq_norm, dist_comm]; exact hsclose
      have hclose := hδ s hsN' n hn1 hnN'
      rw [dist_eq_norm]
      exact lt_of_lt_of_le hclose hεle

/-! ## Continuity of the measure-side pipeline `ofPowerSeries`/`Col` -/

/-- **`g ↦ (μ_g)(ψ)` is coefficientwise-continuous** for a fixed test function `ψ`:
`(ofPowerSeries g)(ψ) = ∑'_n Δⁿψ(0) · gₙ` is a uniform limit (in `g`) of its finite partial
sums `S_N(g) = ∑_{n<N} Δⁿψ(0) · gₙ` (each continuous, the tail `≤ sup_{n≥N}‖Δⁿψ(0)‖ → 0`
uniformly since `‖gₙ‖ ≤ 1`), hence continuous. -/
theorem continuous_ofPowerSeries_apply (ψ : C(ℤ_[p], ℤ_[p])) :
    Continuous (fun g : PowerSeries ℤ_[p] => PadicMeasure.ofPowerSeries p g ψ) := by
  -- the tail bound `‖∑'_{n≥N} Δⁿψ(0)·gₙ‖ ≤ sup_{n≥N} ‖Δⁿψ(0)‖` and `Δⁿψ(0) → 0`
  have hΔ : Filter.Tendsto (fun n => ‖Δ_[1]^[n] (⇑ψ) 0‖) Filter.atTop (nhds 0) := by
    have h := PadicInt.fwdDiff_tendsto_zero ψ
    rwa [tendsto_zero_iff_norm_tendsto_zero] at h
  refine continuous_of_uniform_approx_of_continuous (fun U hU => ?_)
  -- reduce the uniformity `U` to a metric ball of radius `ε`
  rw [Metric.mem_uniformity_dist] at hU
  obtain ⟨ε, hε, hball⟩ := hU
  -- choose `N` with `‖Δⁿψ(0)‖ < ε/2` for `n ≥ N`
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hΔ (ε / 2) (half_pos hε)
  refine ⟨fun g => ∑ n ∈ Finset.range N, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g, ?_, ?_⟩
  · exact continuous_finsetSum _ fun n _ =>
      continuous_const.mul (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] n)
  · intro g
    refine hball ?_
    rw [dist_eq_norm]
    have hsummable : Summable fun n => Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g := by
      refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
      rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _)
        (fun n => (?_ : ‖Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g‖ ≤ ‖Δ_[1]^[n] (⇑ψ) 0‖)) hΔ
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    -- `ofPowerSeries g ψ − S_N(g) = ∑'_{n} Δ^{n+N}ψ(0)·g_{n+N}`
    have hdiff : PadicMeasure.ofPowerSeries p g ψ
          - ∑ n ∈ Finset.range N, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g
        = ∑' n, (Δ_[1]^[n + N] (⇑ψ) 0 * PowerSeries.coeff (n + N) g) := by
      have hval : PadicMeasure.ofPowerSeries p g ψ
          = ∑' n, Δ_[1]^[n] (⇑ψ) 0 * PowerSeries.coeff n g := rfl
      rw [hval, ← (hsummable.sum_add_tsum_nat_add N)]; ring
    rw [hdiff]
    -- the tail norm is `≤ ε/2 < ε`
    refine lt_of_le_of_lt (IsUltrametricDist.norm_tsum_le_of_forall_le (C := ε / 2)
      (fun n => ?_)) (by linarith)
    rw [norm_mul]
    have hterm : ‖Δ_[1]^[n + N] (⇑ψ) 0‖ < ε / 2 := by
      have h := hN (n + N) (by omega)
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h
    exact le_of_lt (lt_of_le_of_lt
      (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hterm)

/-- **The measure-side Coleman pipeline, paired form**: from a series `f` and its inverse
`finv` (kept as a separate argument to sidestep the discontinuity of `Ring.inverse`), the
measure `x⁻¹ · Res_{ℤ_p^×}(𝒜⁻¹((1+T)·f′·finv))` — i.e. `Col` with `Ring.inverse f` replaced by
the supplied `finv`. When `finv = Ring.inverse f` this is exactly `Col` of the corresponding
unit system (`colemanPipe2_eq_Col`). -/
def colemanPipe2 (f finv : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p]ˣ :=
  PadicMeasure.unitsCmul p (PadicMeasure.invCM p)
    (((PadicMeasure.mahlerLinearEquiv p).symm
        ((1 + PowerSeries.X) * PowerSeries.derivativeFun f * finv)).comp
      (PadicMeasure.extendByZero p))

/-- `Col u = colemanPipe2 (colemanSeries u) (Ring.inverse (colemanSeries u))`: the pipeline at
`(f, finv) = (colemanSeries u, (colemanSeries u)⁻¹)` is `Col u`, since `dlog f =
(1+T)·f′·(Ring.inverse f)` by definition. -/
theorem colemanPipe2_eq_Col (u : NormCompatUnits p) :
    colemanPipe2 p (colemanSeries p u) (Ring.inverse (colemanSeries p u)) = Col p u := rfl

/-- **The paired pipeline is jointly continuous** `(f, finv) ↦ colemanPipe2 f finv`. For a fixed
test function `φ`, `(colemanPipe2 f finv)(φ) = (ofPowerSeries ((1+T)·f′·finv))(ψ)` with `ψ =
extendByZero(invCM·φ)` fixed; this is continuous in the series `(1+T)·f′·finv`
(`continuous_ofPowerSeries_apply`), which is continuous in `(f, finv)` (coefficientwise:
`derivativeFun` and `*` are continuous on the topological ring `ℤ_p⟦T⟧`). -/
theorem continuous_colemanPipe2 :
    Continuous (Function.uncurry (colemanPipe2 p)) := by
  rw [PadicMeasure.continuous_iff_eval]
  intro φ
  have hseries : Continuous (fun q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] =>
      (1 + PowerSeries.X) * PowerSeries.derivativeFun q.1 * q.2) := by
    refine (continuous_const.mul ?_).mul continuous_snd
    refine continuous_of_coeff _ (fun n => ?_)
    simp only [PowerSeries.coeff_derivativeFun]
    exact (PowerSeries.WithPiTopology.continuous_coeff ℤ_[p] (n + 1)).comp continuous_fst |>.mul
      continuous_const
  exact (continuous_ofPowerSeries_apply p _).comp hseries

/-! ## Continuity of `colemanSeries` and of `Col` (ST2)

The bottleneck for `Col '' 𝒞_{∞,1} ⊆ I(𝒢)ζ_p` is the continuity of the Coleman map, which
factors as `Col = colemanPipe2 ∘ (colemanSeries, Ring.inverse ∘ colemanSeries)` with
`continuous_colemanPipe2` already in hand; the hard factor is `colemanSeries : 𝒰_∞ →
ℤ_p⟦T⟧`. Prior agents read `colemanSeries` as an *opaque* `Classical.choose` subsequential
limit. It is in fact the *unique* solution of `coleman_existsUnique` (the `𝒩`-fixed unit
interpolating `u`), and that uniqueness — not the diagonal construction — is what makes it
continuous, via a clean compactness argument that sidesteps the opacity entirely:

* `𝒲ˣ := {f | IsUnit f ∧ 𝒩 f = f}` is **compact** (a closed subset of the compact
  `ℤ_p⟦T⟧`, `isClosed_isUnit` + `normOp_continuous`);
* the evaluation `E : 𝒲ˣ → 𝒰_∞`, `f ↦ invColeman f` (the banked inverse, `colemanSeries
  (invColeman f) = f`) is **continuous + injective**, hence a closed embedding
  (`Continuous.isClosedEmbedding`, compact→T2), so it is an *embedding*;
* therefore the section `colSec u := ⟨colemanSeries u, …⟩ : 𝒲ˣ` is continuous **iff**
  `E ∘ colSec` is (`IsEmbedding.continuous_iff`), and `(E (colSec u)).elems n = u.elems n`
  for `n ≥ 1` (by `evalPi_colemanSeries`), constant `1` at level `0` — so `E ∘ colSec` is
  continuous by `continuous_iff_elems` + `continuous_elems`. No `Classical.choose`
  discontinuity ever appears: uniqueness collapses the whole construction to a homeomorphism.

`colemanSeries = Subtype.val ∘ colSec` is then continuous, and `Col` follows by composing
with `continuous_colemanPipe2` (the `Ring.inverse` factor is `colemanSeries (·⁻¹)`, continuous
since inversion is continuous on `𝒰_∞`). -/

/-- The `𝒩`-fixed unit power series `𝒲ˣ = {f | IsUnit f ∧ 𝒩 f = f}` (the image of
`colemanSeries`). -/
def normFixedUnits : Set (PowerSeries ℤ_[p]) := {f | IsUnit f ∧ normOp f = f}

/-- `𝒲ˣ` is closed in `ℤ_p⟦T⟧`: `{IsUnit}` is closed (`isClosed_isUnit`) and `{𝒩 f = f}` is
closed (`normOp_continuous`). -/
theorem isClosed_normFixedUnits : IsClosed (normFixedUnits p) := by
  have hset : normFixedUnits p = {f : PowerSeries ℤ_[p] | IsUnit f} ∩ {f | normOp f = f} := by
    ext; simp [normFixedUnits, Set.mem_inter_iff]
  rw [hset]
  exact isClosed_isUnit.inter (isClosed_eq (normOp_continuous p) continuous_id)

/-- **`𝒲ˣ` is compact**: a closed subset of the (Tychonoff-)compact `ℤ_p⟦T⟧`
(`Coleman.instCompactSpace`). -/
instance instCompactSpace_normFixedUnits : CompactSpace (normFixedUnits p) := by
  rw [← isCompact_iff_compactSpace]
  exact (isClosed_normFixedUnits p).isCompact

/-- The evaluation `E : 𝒲ˣ → 𝒰_∞`, `f ↦ invColeman f`: a `𝒩`-fixed unit gives the
norm-compatible system of its values `(f(π_n))_n` (the banked `invColeman`, with
`colemanSeries (invColeman f) = f`). -/
def colEval (f : normFixedUnits p) : NormCompatUnits p :=
  invColeman p f.1 f.2.1 f.2.2

/-- `colemanSeries (E f) = f` (the banked `colemanSeries_invColeman`: `E` is a section of the
forgetful direction, and `colemanSeries` undoes it). -/
theorem colemanSeries_colEval (f : normFixedUnits p) :
    colemanSeries p (colEval p f) = (f : PowerSeries ℤ_[p]) :=
  colemanSeries_invColeman p f.1 f.2.1 f.2.2

/-- **`E` is continuous**: by `continuous_iff_elems`, each level coordinate `f ↦ (E f).elems n`
is continuous. For `n ≥ 1` it is `f ↦ f(π_n) = evalPi f n` (`continuous_evalPi`); at level `0`
it is the constant `1`. -/
theorem continuous_colEval : Continuous (colEval p) := by
  rw [continuous_iff_elems]
  intro n
  by_cases hn : 1 ≤ n
  · exact ((continuous_evalPi p hn).comp continuous_subtype_val).congr fun f => by
      simp only [Function.comp_apply, colEval, invColeman, dif_pos hn, Units.val_mk0]
  · exact (continuous_const (y := (1 : ℂ_[p]))).congr fun f => by
      simp only [colEval, invColeman, dif_neg hn, Units.val_one]

/-- **`E` is injective**: if `invColeman f = invColeman g`, their level values agree, so
`f = colemanSeries (E f) = colemanSeries (E g) = g` (`colemanSeries_colEval`,
`evalPi_injective`). -/
theorem injective_colEval : Function.Injective (colEval p) := by
  intro f g hfg
  refine Subtype.ext (evalPi_injective p (fun n hn => ?_))
  rw [← colemanSeries_colEval p f, ← colemanSeries_colEval p g, hfg]

/-- The section `u ↦ colemanSeries u` packaged into `𝒲ˣ` (`colemanSeries` lands in the
`𝒩`-fixed units, `colemanSeries_isUnit` + `normOp_colemanSeries`). -/
def colSec (u : NormCompatUnits p) : normFixedUnits p :=
  ⟨colemanSeries p u, colemanSeries_isUnit p u, normOp_colemanSeries p u⟩

/-- **The section `colSec` is continuous.** `E` is a closed embedding (`continuous_colEval` +
`injective_colEval`, compact→T2 `Continuous.isClosedEmbedding`), hence an embedding, so
`colSec` is continuous iff `E ∘ colSec` is (`IsEmbedding.continuous_iff`). And `(E (colSec
u)).elems n = u.elems n` for `n ≥ 1` (`evalPi_colemanSeries`: `colemanSeries u (π_n) = u_n`),
constant `1` at level `0` — continuous by `continuous_iff_elems` + `continuous_elems`. -/
theorem continuous_colSec : Continuous (colSec p) := by
  have hemb : Topology.IsEmbedding (colEval p) :=
    ((continuous_colEval p).isClosedEmbedding (injective_colEval p)).isEmbedding
  rw [hemb.continuous_iff, continuous_iff_elems]
  intro n
  by_cases hn : 1 ≤ n
  · refine (continuous_elems p n).congr fun u => ?_
    change ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]) = (((colEval p (colSec p u)).elems n : ℂ_[p]ˣ) : ℂ_[p])
    simp only [colEval, colSec, invColeman, dif_pos hn, Units.val_mk0]
    exact (evalPi_colemanSeries p u hn).symm
  · refine (continuous_const (y := (1 : ℂ_[p]))).congr fun u => ?_
    change (1 : ℂ_[p]) = (((colEval p (colSec p u)).elems n : ℂ_[p]ˣ) : ℂ_[p])
    simp only [colEval, colSec, invColeman, dif_neg hn, Units.val_one]

/-- **`colemanSeries : 𝒰_∞ → ℤ_p⟦T⟧` is continuous** (coefficientwise/`WithPiTopology`). It is
`Subtype.val ∘ colSec` with `colSec` continuous (`continuous_colSec`). The opacity of the
`Classical.choose` construction is irrelevant: `colemanSeries` is pinned by `coleman_existsUnique`
and recovered as the inverse of the embedding `E`, a genuine continuous function. -/
theorem continuous_colemanSeries : Continuous (colemanSeries p) :=
  continuous_subtype_val.comp (continuous_colSec p)

/-- `colemanSeries 1 = 1` (the trivial system maps to the unit series; both are `𝒩`-fixed units
interpolating `1`, so equal by `coleman_existsUnique`). -/
theorem colemanSeries_one' : colemanSeries p (1 : NormCompatUnits p) = 1 := by
  refine (coleman_existsUnique p 1).unique (coleman_existsUnique p 1).choose_spec.1
    ⟨isUnit_one, normOp_one, fun n hn => ?_⟩
  rw [evalPi_one]; rfl

/-- `Ring.inverse (colemanSeries u) = colemanSeries u⁻¹`: from multiplicativity
(`colemanSeries_mul`, `colemanSeries_one'`) `colemanSeries u · colemanSeries u⁻¹ = 1`, so
`colemanSeries u⁻¹` is the (two-sided) inverse of the unit `colemanSeries u`. This identifies
the `Ring.inverse` factor of `Col` with a continuous function, sidestepping its general
discontinuity. -/
theorem inverse_colemanSeries (u : NormCompatUnits p) :
    Ring.inverse (colemanSeries p u) = colemanSeries p u⁻¹ := by
  have hmul : colemanSeries p u * colemanSeries p u⁻¹ = 1 := by
    rw [← colemanSeries_mul p, mul_inv_cancel, colemanSeries_one' p]
  exact left_inv_eq_right_inv (Ring.inverse_mul_cancel _ (colemanSeries_isUnit p u)) hmul

/-- **Inversion `u ↦ u⁻¹` is continuous on `𝒰_∞`** (it is a `CommGroup` with pointwise inverse).
By `continuous_iff_elems`, each level coordinate is `u ↦ (u.elems n)⁻¹ : ℂ_[p]`, continuous as
`val ∘ inv` of the continuous unit coordinate `continuous_elemsUnits` (`ℂ_[p]ˣ` a topological
group). -/
theorem continuous_inv_NCU : Continuous (fun u : NormCompatUnits p => u⁻¹) := by
  rw [continuous_iff_elems]
  intro n
  exact Units.continuous_val.comp (continuous_inv.comp (continuous_elemsUnits p n))

/-- **`Col` is continuous** (ST2), w.r.t. the inverse-limit topology on `𝒰_∞` (ST1) and the
weak-* topology on `Λ(ℤ_p^×)`. Write `Col = colemanPipe2 ∘ (colemanSeries, Ring.inverse ∘
colemanSeries)` (`colemanPipe2_eq_Col`): the pairing is continuous — `colemanSeries` by
`continuous_colemanSeries`, and `Ring.inverse ∘ colemanSeries = colemanSeries ∘ (·⁻¹)`
(`inverse_colemanSeries`) by `continuous_colemanSeries` ∘ `continuous_inv_NCU` — and
`colemanPipe2` is jointly continuous (`continuous_colemanPipe2`). -/
theorem continuous_Col : Continuous (Col p) := by
  have hpair : Continuous (fun u : NormCompatUnits p =>
      (colemanSeries p u, Ring.inverse (colemanSeries p u))) := by
    refine (continuous_colemanSeries p).prodMk
      (((continuous_colemanSeries p).comp (continuous_inv_NCU p)).congr
        (fun u => (inverse_colemanSeries p u).symm))
  have hcol : (Col p) = (Function.uncurry (colemanPipe2 p)) ∘
      (fun u : NormCompatUnits p => (colemanSeries p u, Ring.inverse (colemanSeries p u))) := by
    funext u
    rw [Function.comp_apply, Function.uncurry_apply_pair, colemanPipe2_eq_Col]
  rw [hcol]
  exact (continuous_colemanPipe2 p).comp hpair

/-! ## Closedness of the cyclotomic-closure value sets and of `Col '' 𝒞_{∞,1}` -/

/-- `K p n` is closed in `ℂ_[p]` (re-derived; the `Theorem.lean` version is private): a
finite-dimensional `ℚ_[p]`-subspace of a normed space over the complete `ℚ_[p]` is complete,
hence closed. -/
theorem isClosed_KCp (n : ℕ) : IsClosed (X := ℂ_[p]) (K p n : Set ℂ_[p]) := by
  haveI : FiniteDimensional ℚ_[p] (K p n).toSubmodule := by
    have hint : IsIntegral ℚ_[p] (zetaSys p n) :=
      ((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).tower_top
    exact IntermediateField.adjoin.finiteDimensional hint
  exact (K p n).toSubmodule.closed_of_finiteDimensional

/-- `O p n` is closed in `ℂ_[p]` (`K p n` closed ∩ the closed unit ball). -/
theorem isClosed_OCp (n : ℕ) : IsClosed (X := ℂ_[p]) (O p n : Set ℂ_[p]) := by
  show IsClosed ((K p n : Set ℂ_[p]) ∩ {x : ℂ_[p] | ‖x‖ ≤ 1})
  exact (isClosed_KCp p n).inter (isClosed_le continuous_norm continuous_const)

/-- `localUnits p n` is closed in `ℂ_[p]ˣ`: both `(u : ℂ_[p]) ∈ O p n` and
`(u⁻¹ : ℂ_[p]) ∈ O p n` are closed conditions (`val`/`inv∘val` continuous, `O p n` closed). -/
theorem isClosed_localUnits (n : ℕ) :
    IsClosed (localUnits p n : Set ℂ_[p]ˣ) := by
  show IsClosed ((fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ⁻¹' (O p n : Set ℂ_[p])
        ∩ (fun u : ℂ_[p]ˣ => ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) ⁻¹' (O p n : Set ℂ_[p]))
  refine ((isClosed_OCp p n).preimage Units.continuous_val).inter
    ((isClosed_OCp p n).preimage ?_)
  exact Units.continuous_val.comp continuous_inv

/-- `localUnitsOne p n` is closed in `ℂ_[p]ˣ`: `localUnits` closed ∩ the closed condition
`‖(u:ℂ_[p]) − 1‖ < 1` (an ultrametric ball, hence clopen). -/
theorem isClosed_localUnitsOne (n : ℕ) :
    IsClosed (localUnitsOne p n : Set ℂ_[p]ˣ) := by
  show IsClosed ((localUnits p n : Set ℂ_[p]ˣ) ∩ {u : ℂ_[p]ˣ | ‖(u : ℂ_[p]) - 1‖ < 1})
  refine (isClosed_localUnits p n).inter ?_
  -- `{u | ‖val u − 1‖ < 1}` is the preimage of the clopen ultrametric ball `B(1,1) ⊆ ℂ_[p]`
  have hclopen : IsClosed {x : ℂ_[p] | ‖x - 1‖ < 1} := by
    have heq : {x : ℂ_[p] | ‖x - 1‖ < 1} = Metric.ball (1 : ℂ_[p]) 1 := by
      ext x; rw [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
    rw [heq]
    exact IsUltrametricDist.isClosed_ball (1 : ℂ_[p]) 1
  exact hclopen.preimage Units.continuous_val

/-- `cycloClosureOne p n` is closed in `ℂ_[p]ˣ`: the intersection of the (closed) topological
closure of the cyclotomic units with the closed `localUnits`/`localUnitsOne`. -/
theorem isClosed_cycloClosureOne (n : ℕ) :
    IsClosed (cycloClosureOne p n : Set ℂ_[p]ˣ) := by
  have h : (cycloClosureOne p n : Set ℂ_[p]ˣ)
      = ((cycloUnits p n).topologicalClosure : Set ℂ_[p]ˣ)
        ∩ (localUnits p n : Set ℂ_[p]ˣ) ∩ (localUnitsOne p n : Set ℂ_[p]ˣ) := by
    rw [cycloClosureOne, cycloClosure]; rfl
  rw [h]
  exact ((Subgroup.isClosed_topologicalClosure _).inter (isClosed_localUnits p n)).inter
    (isClosed_localUnitsOne p n)

/-- **`𝒞_{∞,1}` is closed in `𝒰_∞`** (the inverse-limit topology ST1). It is the intersection
over `n ≥ 1` of the preimages, under the continuous unit coordinate `u ↦ u.elems n`
(`continuous_elemsUnits`), of the closed level sets `𝒞_{n,1} = cycloClosureOne p n`
(`isClosed_cycloClosureOne`). -/
theorem isClosed_cycloTower1 : IsClosed (cycloTower1 p : Set (NormCompatUnits p)) := by
  have hset : (cycloTower1 p : Set (NormCompatUnits p))
      = ⋂ n, ⋂ (_ : 1 ≤ n),
          (fun u : NormCompatUnits p => u.elems n) ⁻¹' (cycloClosureOne p n : Set ℂ_[p]ˣ) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [hset]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
  exact (isClosed_cycloClosureOne p n).preimage (continuous_elemsUnits p n)

/-- **The value set `C_n := val '' 𝒞_{n,1}` is closed in `ℂ_[p]`.** `Units.val` is a topological
embedding (ℂ_[p] is a normed field, `Units.isEmbedding_val₀`), `𝒞_{n,1}` is closed in `ℂ_[p]ˣ`,
and `𝒞_{n,1} ⊆ localUnitsOne` lands in the *clopen* ball `B(1,1)`, so the image cannot
accumulate at `0`: any limit `y ∈ closure C_n ⊆ B(1,1)` is a unit `val u` with `u ∈ closure 𝒞 =
𝒞`. -/
theorem isClosed_val_cycloClosureOne (n : ℕ) :
    IsClosed ((fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)) := by
  rw [← isSeqClosed_iff_isClosed]
  intro x y hx hxy
  -- each `x k = val (u k)` with `u k ∈ 𝒞_{n,1}`
  choose u hu hux using hx
  -- `‖y − 1‖ < 1` (the clopen ball `B(1,1)` is closed and contains every `x k`)
  have hyball : ‖y - 1‖ < 1 := by
    have hxball : ∀ k, ‖x k - 1‖ < 1 := by
      intro k
      rw [← hux k]
      have hmem : u k ∈ localUnitsOne p n := by
        have h := hu k
        rw [SetLike.mem_coe, cycloClosureOne, Subgroup.mem_inf] at h
        exact h.2
      exact ((mem_localUnitsOne_iff p).1 hmem).2
    have hball : IsClosed {z : ℂ_[p] | ‖z - 1‖ < 1} := by
      have heq : {z : ℂ_[p] | ‖z - 1‖ < 1} = Metric.ball (1 : ℂ_[p]) 1 := by
        ext z; rw [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
      rw [heq]; exact IsUltrametricDist.isClosed_ball (1 : ℂ_[p]) 1
    exact hball.mem_of_tendsto hxy (Filter.Eventually.of_forall hxball)
  -- `‖y‖ = 1`, so `y ≠ 0` is a unit
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyball
    simp only [zero_sub, norm_neg, norm_one] at hyball
    exact lt_irrefl 1 hyball
  have hyunit : IsUnit y := isUnit_iff_ne_zero.2 hy0
  -- `u k → y.unit` in `ℂ_[p]ˣ` (`val` is a topological embedding) and `𝒞_{n,1}` is seq-closed
  have hutend : Filter.Tendsto u Filter.atTop (nhds hyunit.unit) := by
    rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
    have hval : (fun k => ((u k : ℂ_[p]ˣ) : ℂ_[p])) = x := funext hux
    have hyval : ((hyunit.unit : ℂ_[p]ˣ) : ℂ_[p]) = y := IsUnit.unit_spec hyunit
    rw [show ((Units.val : ℂ_[p]ˣ → ℂ_[p]) ∘ u) = x from hval, hyval]
    exact hxy
  have hyu : hyunit.unit ∈ cycloClosureOne p n :=
    (isClosed_cycloClosureOne p n).isSeqClosed hu hutend
  exact ⟨hyunit.unit, hyu, IsUnit.unit_spec hyunit⟩

/-- The compact set of Coleman-series pairs realising `𝒞_{∞,1}`: pairs `(f, finv)` with
`f · finv = 1`, `f` `𝒩`-fixed, and `f(π_n) ∈ C_n := val '' 𝒞_{n,1}` for all `n ≥ 1`. -/
def colemanPairSet : Set (PowerSeries ℤ_[p] × PowerSeries ℤ_[p]) :=
  {q | q.1 * q.2 = 1 ∧ normOp q.1 = q.1 ∧
    ∀ n, 1 ≤ n → evalPi p q.1 n
      ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)}

/-- `colemanPairSet` is closed in `ℤ_p⟦T⟧ × ℤ_p⟦T⟧` (hence compact). The three conditions are
closed: `f·finv = 1` (continuous `*` into the T2 ring, `{1}` closed); `𝒩 f = f` (`normOp`
continuous); each `f(π_n) ∈ C_n` (`evalPi (·) n` continuous, `C_n` closed
`isClosed_val_cycloClosureOne`). -/
theorem isCompact_colemanPairSet : IsCompact (colemanPairSet p) := by
  refine IsClosed.isCompact ?_
  rw [show colemanPairSet p
      = {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | q.1 * q.2 = 1}
        ∩ {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | normOp q.1 = q.1}
        ∩ {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
            evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ''
              (cycloClosureOne p n : Set ℂ_[p]ˣ)} from by
    ext q; simp only [colemanPairSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto]
  have h1 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | q.1 * q.2 = 1} :=
    isClosed_eq (continuous_fst.mul continuous_snd) continuous_const
  have h2 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | normOp q.1 = q.1} :=
    isClosed_eq ((normOp_continuous p).comp continuous_fst) continuous_fst
  have h3 : IsClosed {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
      evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)} := by
    rw [show {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] | ∀ n, 1 ≤ n →
        evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ)}
        = ⋂ n, ⋂ (_ : 1 ≤ n), {q : PowerSeries ℤ_[p] × PowerSeries ℤ_[p] |
            evalPi p q.1 n ∈ (fun u : ℂ_[p]ˣ => (u : ℂ_[p])) ''
              (cycloClosureOne p n : Set ℂ_[p]ˣ)} from by
      ext q; simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    refine isClosed_iInter fun n => isClosed_iInter fun hn => ?_
    exact (isClosed_val_cycloClosureOne p n).preimage ((continuous_evalPi p hn).comp continuous_fst)
  exact (h1.inter h2).inter h3

/-- **`Col '' 𝒞_{∞,1} = colemanPipe2 '' colemanPairSet`.** For `c ∈ 𝒞_{∞,1}`, the pair
`(colemanSeries c, (colemanSeries c)⁻¹)` lies in `colemanPairSet` and maps to `Col c`.
Conversely, any `(f, finv) ∈ colemanPairSet` has `f` a `𝒩`-fixed unit (`f·finv = 1`) and
`f(π_n) ∈ C_n`, so `invColeman f ∈ 𝒞_{∞,1}` with `colemanSeries (invColeman f) = f` and
`finv = Ring.inverse f`, giving `colemanPipe2 f finv = Col (invColeman f)`. -/
theorem col_image_eq_pipe_image :
    Col p '' (cycloTower1 p : Set (NormCompatUnits p))
      = Function.uncurry (colemanPipe2 p) '' colemanPairSet p := by
  apply Set.eq_of_subset_of_subset
  · -- `⊆`: `c ↦ (colemanSeries c, (colemanSeries c)⁻¹)`
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨(colemanSeries p c, Ring.inverse (colemanSeries p c)), ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Ring.mul_inverse_cancel _ (colemanSeries_isUnit p c)
    · exact normOp_colemanSeries p c
    · intro n hn
      refine ⟨c.elems n, hc n hn, ?_⟩
      exact (evalPi_colemanSeries p c hn).symm
    · exact colemanPipe2_eq_Col p c
  · -- `⊇`: `(f, finv) ↦ invColeman f`
    rintro _ ⟨⟨f, finv⟩, ⟨hfinv, hN, hC⟩, rfl⟩
    have hfunit : IsUnit f := IsUnit.of_mul_eq_one finv hfinv
    have hfinveq : finv = Ring.inverse f :=
      (left_inv_eq_right_inv (Ring.inverse_mul_cancel f hfunit) hfinv).symm
    set c := invColeman p f hfunit hN with hc
    have hcs : colemanSeries p c = f := colemanSeries_invColeman p f hfunit hN
    -- `c ∈ 𝒞_{∞,1}`: each `c.elems n ∈ 𝒞_{n,1}`
    have hccyclo : c ∈ cycloTower1 p := by
      intro n hn
      obtain ⟨w, hw, hwval⟩ := hC n hn
      -- `(c.elems n : ℂ_[p]) = evalPi (colemanSeries c) n = evalPi f n = val w`
      have hcval : ((c.elems n : ℂ_[p]ˣ) : ℂ_[p]) = (w : ℂ_[p]) := by
        rw [← evalPi_colemanSeries p c hn, hcs]; exact hwval.symm
      rw [show c.elems n = w from Units.ext hcval]
      exact hw
    refine ⟨c, hccyclo, ?_⟩
    rw [Function.uncurry_apply_pair, hfinveq, ← hcs, colemanPipe2_eq_Col]

/-- **`Col '' 𝒞_{∞,1}` is compact** (continuous image of the compact `colemanPairSet`), hence
closed in the weak-* topology on `Λ(ℤ_p^×)`. -/
theorem isCompact_col_image :
    IsCompact (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) := by
  rw [col_image_eq_pipe_image]
  exact (isCompact_colemanPairSet p).image (continuous_colemanPipe2 p)

theorem isClosed_col_image :
    IsClosed (Col p '' (cycloTower1 p : Set (NormCompatUnits p))) :=
  (isCompact_col_image p).isClosed

/-- Re-glue at level `0`: `glueLevel0 m u` keeps `m`'s levels `≥ 1` but takes `u`'s level-`0`
coordinate. Used to re-set a witness's free level-`0` coordinate (which `Col` ignores) so it lands
inside a given neighbourhood box. -/
def glueLevel0 (m u : NormCompatUnits p) : NormCompatUnits p where
  elems k := if k = 0 then u.elems 0 else m.elems k
  mem k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using u.mem 0
    · simpa only [if_neg hk] using m.mem k
  inv_mem k := by
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using u.inv_mem 0
    · simpa only [if_neg hk] using m.inv_mem k
  compat n hn := by
    rw [if_neg (by omega : ¬ n + 1 = 0), if_neg (by omega : ¬ n = 0)]
    exact m.compat n hn

@[simp] theorem glueLevel0_elems_zero (m u : NormCompatUnits p) :
    (glueLevel0 p m u).elems 0 = u.elems 0 := by simp [glueLevel0]

theorem glueLevel0_elems_of_pos (m u : NormCompatUnits p) {n : ℕ} (hn : 1 ≤ n) :
    (glueLevel0 p m u).elems n = m.elems n := by
  simp only [glueLevel0, if_neg (by omega : ¬ n = 0)]

/-- **The level-`0`-saturated Col-density** (the form that drives RJW LemmaGeneratorCinfty1's
inverse-limit step): if every level-`n` (`n ≥ 1`) coordinate of `u` lies in the closure of the
level-`n` image of a subgroup `S`, then `Col u ∈ closure(Col '' S)`. No level-`0` hypothesis is
needed — `Col` ignores the free level-`0` coordinate (`Col_eq_of_elems_eq`), so a witness `m ∈ S`
matching `u` only on levels `≥ 1` (found by `exists_delta_descent`) can be re-glued at level `0`
(`glueLevel0`) to land in any neighbourhood box without changing `Col m`. -/
theorem Col_mem_closure_image_of_levelwise {S : Subgroup (NormCompatUnits p)}
    {u : NormCompatUnits p}
    (h : ∀ n, 1 ≤ n → (u.elems n : ℂ_[p]) ∈
      closure ((fun s : NormCompatUnits p => (s.elems n : ℂ_[p])) '' (S : Set (NormCompatUnits p)))) :
    Col p u ∈ closure (Col p '' (S : Set (NormCompatUnits p))) := by
  rw [mem_closure_iff_nhds]
  intro W hW
  have hpre : Col p ⁻¹' W ∈ nhds u := (continuous_Col p).continuousAt.preimage_mem_nhds hW
  rw [nhds_induced, Filter.mem_comap] at hpre
  obtain ⟨t, ht, htsub⟩ := hpre
  rw [nhds_pi, Filter.mem_pi] at ht
  obtain ⟨I, hI, V, hV, hVt⟩ := ht
  choose εf hεfpos hεfsub using fun n => Metric.mem_nhds_iff.1 (hV n)
  rcases I.eq_empty_or_nonempty with hIempty | hIne
  · refine ⟨Col p 1, htsub ?_, ⟨1, one_mem _, rfl⟩⟩
    rw [Set.mem_preimage]
    exact hVt (by rw [hIempty, Set.empty_pi]; exact Set.mem_univ _)
  · obtain ⟨b, hb⟩ := hI.bddAbove
    have hN'1 : 1 ≤ max b 1 := le_max_right _ _
    have hIfne : hI.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hI).2 hIne
    set ε := hI.toFinset.inf' hIfne εf with hεdef
    have hεpos : 0 < ε := by rw [hεdef, Finset.lt_inf'_iff]; exact fun n _ => hεfpos n
    obtain ⟨δ, hδpos, hδ⟩ := exists_delta_descent p u (max b 1) hN'1 ε hεpos
    obtain ⟨_, ⟨m, hmS, rfl⟩, hmclose⟩ := Metric.mem_closure_iff.1 (h _ hN'1) δ hδpos
    refine ⟨Col p m, ?_, ⟨m, hmS, rfl⟩⟩
    have hColeq : Col p (glueLevel0 p m u) = Col p m :=
      Col_eq_of_elems_eq p (fun n hn => glueLevel0_elems_of_pos p m u hn)
    rw [← hColeq]
    refine htsub ?_
    rw [Set.mem_preimage]
    refine hVt fun n hnI => hεfsub n ?_
    rw [Metric.mem_ball]
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · simp only [elemsCoe, glueLevel0_elems_zero, dist_self]; exact hεfpos 0
    · have hnN' : n ≤ max b 1 := le_trans (hb hnI) (le_max_left _ _)
      have hεle : ε ≤ εf n := Finset.inf'_le εf (hI.mem_toFinset.2 hnI)
      have hsN' : ‖(m.elems (max b 1) : ℂ_[p]) - (u.elems (max b 1) : ℂ_[p])‖ < δ := by
        rw [← dist_eq_norm, dist_comm]; exact hmclose
      have hclose := hδ m hsN' n hn1 hnN'
      simp only [elemsCoe, glueLevel0_elems_of_pos p m u hn1]
      rw [dist_eq_norm]; exact lt_of_lt_of_le hclose hεle

end PadicLFunctions.Coleman
