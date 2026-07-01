module

public import CebotarevDensity.ForMathlib.LogOneDivSubOne
public import CebotarevDensity.NumberFieldEulerProduct
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Dirichlet density of a set of prime ideals

For a number field `K`, the Dirichlet density of a set `S` of prime ideals of `𝓞 K` is, when it
exists,

  δ(S) = lim_{s → 1⁺} ( Σ_{𝔭 ∈ S} N𝔭^{-s} ) / ( Σ_𝔭 N𝔭^{-s} ),

with both sums running over nonzero prime ideals. The denominator is asymptotic to
`log (s - 1)^{-1}` as `s ↓ 1` (Sharifi, *Algebraic Number Theory*, §7.1.12; `docs/algnum.pdf`).

## Main definitions

* `Chebotarev.primeIdealZetaSum` — the partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}`.
* `Chebotarev.HasDirichletDensity` — `S` has Dirichlet density `δ`.
* `Chebotarev.HasUpperDirichletDensity`, `Chebotarev.HasLowerDirichletDensity` — `limsup` /
  `liminf` variants used in the Chebotarev sandwich argument (Sharifi 7.2.2 Step 2).

## References

* Sharifi, *Algebraic Number Theory*, §7.1.13 (`docs/algnum.pdf`).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem* (`docs/cheb.pdf`).
-/

@[expose] public section

noncomputable section

open Filter NumberField Topology Set

namespace Chebotarev

variable {K : Type*} [Field K] [NumberField K] {S : Set (Ideal (𝓞 K))} {δ : ℝ}

/-- Partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` over nonzero prime ideals `𝔭` of `𝓞 K`
lying in the set `S`. -/
def primeIdealZetaSum (S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)

/-- Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`. -/
theorem primeIdealZetaSum_def (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    primeIdealZetaSum S s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := rfl

/-- The Dirichlet density of a set `S` of prime ideals of `𝓞 K` is `δ` when the ratio of partial
sums tends to `δ` as `s ↓ 1`.

Sharifi 7.1.13: `δ(S) = lim_{s → 1⁺} (Σ_{𝔭 ∈ S} N𝔭^{-s}) / (Σ_𝔭 N𝔭^{-s})`. -/
def HasDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  Tendsto
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) (𝓝 δ)

/-- Upper Dirichlet density (`limsup` of the ratio).

**Convention note.** This uses the standard mathematical convention: upper = `limsup`. Sharifi
*Algebraic Number Theory* §7.1.13 (p. 140) labels the `limsup` form "lower Dirichlet density" and
the `liminf` form "upper Dirichlet density" — a non-standard labelling. We follow the standard
convention, so:

* this `HasUpperDirichletDensity` (= `limsup`) is what Sharifi calls "lower Dirichlet density" and
  notates `δ_sup`;
* `HasLowerDirichletDensity` (= `liminf`) is what Sharifi calls "upper Dirichlet density" and
  notates `δ_inf`.

When transcribing Sharifi's `δ_inf` to Lean, use `HasLowerDirichletDensity`. -/
def HasUpperDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  limsup
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- Lower Dirichlet density (`liminf` of the ratio). See `HasUpperDirichletDensity` for the
convention note: this matches Sharifi's `δ_inf` notation despite Sharifi's labelling inversion. -/
def HasLowerDirichletDensity (S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop :=
  liminf
    (fun s : ℝ ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    (𝓝[>] 1) = δ

/-- The Dirichlet density of the empty set is `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := ⟨(·.2.1)⟩
  simpa only [HasDirichletDensity, primeIdealZetaSum_def, tsum_empty, zero_div]
    using tendsto_const_nhds

/-- Over the nonzero ideals of `𝓞 K`, the series `Σ_I N(I)^{-s}` is summable for `1 < s`. -/
private theorem summable_nonzeroIdeal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s)) :=
  ((hasSum_nonzeroIdeal_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).summable.norm).congr
    fun I ↦ (Complex.norm_natCast_cpow_of_pos
      (Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)) _).trans <| by simp

/-- Over the nonzero prime ideals of `𝓞 K` lying in any set `S`, the series `Σ_𝔭 N𝔭^{-s}` is
summable for `1 < s`. -/
theorem summable_prime_absNorm_rpow (S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_nonzeroIdeal_absNorm_rpow hs).comp_injective
    (i := fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (⟨𝔭.1, 𝔭.2.2.2⟩ : NonzeroIdeal K))
    fun _ _ hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab)).congr fun _ ↦ rfl

/-- The partial Dirichlet series is nonnegative. -/
private theorem primeIdealZetaSum_nonneg (S : Set (Ideal (𝓞 K))) (s : ℝ) :
    0 ≤ primeIdealZetaSum S s :=
  tsum_nonneg fun _ ↦ by positivity

/-- The partial Dirichlet series over `S` is bounded above by the one over all primes, for
`1 < s`. -/
private theorem primeIdealZetaSum_le_univ {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, mem_univ _, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs)

/-- The partial Dirichlet series over `S ⊆ T` is bounded above by the one over `T`, for
`1 < s`. -/
theorem primeIdealZetaSum_le_of_subset {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum S s ≤ primeIdealZetaSum T s := by
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def]
  refine (summable_prime_absNorm_rpow S hs).tsum_le_tsum_of_inj
    (fun 𝔭 ↦ ⟨𝔭.1, hST 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩)
    (fun a b hab ↦ Subtype.ext (Subtype.mk_eq_mk.mp hab))
    (fun c _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ ↦ le_rfl) (summable_prime_absNorm_rpow T hs)

/-- For disjoint `S` and `T`, the partial Dirichlet series over `S ∪ T` splits as the sum of those
over `S` and `T`, for `1 < s`. -/
theorem primeIdealZetaSum_union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ}
    (hs : 1 < s) :
    primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s := by
  let eS : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S} :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inl 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩, 𝔭.2.1⟩
      invFun := fun x ↦ ⟨x.1.1, x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let eT : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      ↑{x : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∪ T ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} | (x.1 : Ideal (𝓞 K)) ∈ S}ᶜ :=
    { toFun := fun 𝔭 ↦ ⟨⟨𝔭.1, Or.inr 𝔭.2.1, 𝔭.2.2.1, 𝔭.2.2.2⟩,
        fun h ↦ hDisj.le_bot ⟨h, 𝔭.2.1⟩⟩
      invFun := fun x ↦ ⟨x.1.1, x.1.2.1.resolve_left x.2, x.1.2.2.1, x.1.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← (summable_prime_absNorm_rpow (S ∪ T) hs).tsum_subtype_add_tsum_subtype_compl
      {x | (x.1 : Ideal (𝓞 K)) ∈ S},
    ← eS.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s)),
    ← eT.tsum_eq (fun x ↦ (Ideal.absNorm (x.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- The partial Dirichlet series over the empty set is `0`. -/
theorem primeIdealZetaSum_empty (s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0 := by
  have : IsEmpty {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (∅ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    ⟨(·.2.1)⟩
  rw [primeIdealZetaSum_def, tsum_empty]

/-- The partial Dirichlet series over a `Finset`-indexed pairwise-disjoint family `⋃ i ∈ t, g i`
splits as the finite sum `∑ i ∈ t, primeIdealZetaSum (g i)`, for `1 < s`. -/
theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint {ι : Type*} (t : Finset ι)
    (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) :
    primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp [primeIdealZetaSum_empty]
  | insert a t ha ih =>
      have hdisj : Disjoint (g a) (⋃ i ∈ t, g i) :=
        disjoint_iUnion₂_right.2 fun i hi ↦
          hg (t.mem_insert_self a) (Finset.mem_insert_of_mem hi) fun h ↦ ha (h ▸ hi)
      rw [Finset.set_biUnion_insert, primeIdealZetaSum_union_of_disjoint hdisj hs,
        Finset.sum_insert ha, ih (hg.subset (Finset.coe_subset.mpr (Finset.subset_insert a t)))]

/-- If `S` contains every nonzero prime ideal of `𝓞 K`, then its partial Dirichlet series agrees
with the one over `univ`. -/
theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem
    (hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) :
    primeIdealZetaSum S s = primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  let e : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ≃
      {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ (univ : Set (Ideal (𝓞 K))) ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    Equiv.subtypeEquivRight fun 𝔭 ↦
      ⟨fun h ↦ ⟨mem_univ _, h.2⟩, fun h ↦ ⟨hS 𝔭 h.2.1 h.2.2, h.2⟩⟩
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    ← e.tsum_eq (fun 𝔭 ↦ (Ideal.absNorm (𝔭.1 : Ideal (𝓞 K)) : ℝ) ^ (-s))]
  rfl

/-- The density ratio `Σ_S / Σ_univ` is bounded below (it is everywhere nonnegative). -/
private theorem isBoundedUnder_ge_primeIdealZetaSum_ratio (S : Set (Ideal (𝓞 K))) :
    IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ))
      (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) :=
  isBoundedUnder_of ⟨0, fun s ↦ div_nonneg (primeIdealZetaSum_nonneg S s)
    (primeIdealZetaSum_nonneg univ s)⟩

/-- The density ratio `Σ_S / Σ_univ` is eventually at most `1` as `s ↓ 1`, since `Σ_S ≤ Σ_univ`
and the denominator is nonnegative. -/
private theorem eventually_primeIdealZetaSum_ratio_le_one (S : Set (Ideal (𝓞 K))) :
    ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum S s / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s ≤ 1 := by
  filter_upwards [self_mem_nhdsWithin] with s hs using
    div_le_one_of_le₀ (primeIdealZetaSum_le_univ hs) (primeIdealZetaSum_nonneg univ s)

/-- If the upper density of `S` equals the lower density of `S` and both equal `δ`, then the
Dirichlet density of `S` is `δ`. (Sandwich criterion used in the Chebotarev proof: Sharifi 7.2.2
Step 2 last paragraph.) -/
theorem HasDirichletDensity.of_upper_eq_lower (hUp : HasUpperDirichletDensity S δ)
    (hLow : HasLowerDirichletDensity S δ) :
    HasDirichletDensity S δ :=
  tendsto_of_liminf_eq_limsup hLow hUp
    ⟨1, eventually_map.mpr (eventually_primeIdealZetaSum_ratio_le_one S)⟩
    (isBoundedUnder_ge_primeIdealZetaSum_ratio S)

/-- The upper Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasUpper (h : HasDirichletDensity S δ) :
    HasUpperDirichletDensity S δ :=
  h.limsup_eq

/-- The lower Dirichlet density extracted from `HasDirichletDensity`. -/
theorem HasDirichletDensity.hasLower (h : HasDirichletDensity S δ) :
    HasLowerDirichletDensity S δ :=
  h.liminf_eq

/-- The Dirichlet density of a disjoint union is the sum of the densities. -/
theorem HasDirichletDensity.union_of_disjoint {T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T)
    {ε : ℝ} (hS : HasDirichletDensity S δ) (hT : HasDirichletDensity T ε) :
    HasDirichletDensity (S ∪ T) (δ + ε) := by
  rw [HasDirichletDensity] at hS hT ⊢
  refine (hS.add hT).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [primeIdealZetaSum_union_of_disjoint hDisj hs, add_div]

/-- Monotonicity of the lower density under inclusion. -/
theorem HasLowerDirichletDensity.mono {T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ}
    (hS : HasLowerDirichletDensity S δ) (hT : HasLowerDirichletDensity T ε) :
    δ ≤ ε := by
  rw [HasLowerDirichletDensity] at hS hT
  rw [← hS, ← hT]
  refine liminf_le_liminf ?_ (isBoundedUnder_ge_primeIdealZetaSum_ratio S)
    (isCoboundedUnder_ge_of_eventually_le (x := 1) _
      (eventually_primeIdealZetaSum_ratio_le_one T))
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact div_le_div_of_nonneg_right (primeIdealZetaSum_le_of_subset hST hs)
    (primeIdealZetaSum_nonneg univ s)

/-! ### Sub-lemmas for `primeIdealZetaSum_univ_tendsto_log`

Following Sharifi 7.1.12 proof (p. 140, *Algebraic Number Theory*). The source's argument decomposes
into:

(i) Euler-product identity `ζ_K = ∏(1 - N𝔭^{-s})^{-1}` on `Re s > 1` (Sharifi 7.1.12 statement).
(ii) `log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}` as the principal term, with the higher-power tail `Σ_{k≥2,𝔭}
    N𝔭^{-ks}/k` bounded on `Re s > 1/2` (Sharifi 7.1.12 proof: "log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}").
(iii) `log ζ_K(s) ~ log(1/(s-1))` from the simple pole of `ζ_K` at `s=1` (mathlib:
    `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`).
-/

variable (K)

/-- Over the nonzero prime ideals of `𝓞 K` (the 2-part subtype, no ambient set), the series
`Σ_𝔭 N𝔭^{-s}` is summable for `1 < s`. -/
private theorem summable_prime2_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
  ((summable_prime_absNorm_rpow (univ : Set (Ideal (𝓞 K))) hs).comp_injective
    (Equiv.subtypeEquivRight fun _ ↦ ⟨(⟨mem_univ _, ·⟩), And.right⟩).injective).congr fun _ ↦ rfl

/-- A nonzero prime ideal of `𝓞 K` has absolute norm at least `2`. -/
private theorem two_le_absNorm_of_prime {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) :=
  mod_cast (Nat.two_le_iff _).2
    ⟨mt Ideal.absNorm_eq_zero_iff.1 hne, mt Ideal.absNorm_eq_one_iff.1 hp.ne_top⟩

/-- For a nonzero prime `𝔭` and `1 < s`, the Euler factor `N𝔭^{-s}` is strictly less than `1`. -/
private theorem absNorm_rpow_neg_lt_one {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ}
    (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_absNorm_of_prime K hp hne]) (by linarith)

/-- Per-prime termwise bound for the higher-power tail. For `1 < s` and a nonzero prime `𝔭`, the
geometric term `N𝔭^{-2s}/(1 - N𝔭^{-s})` is dominated by `2·N𝔭^{-2}`. -/
private theorem primeIdealHigherTail_term_le {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤
      2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2 : ℝ)) := by
  set x : ℝ := (Ideal.absNorm 𝔭 : ℝ)
  have hx : (2 : ℝ) ≤ x := two_le_absNorm_of_prime K hp hne
  have hxs_half : x ^ (-s) ≤ 1 / 2 :=
    calc x ^ (-s) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_nonpos zero_lt_two hx (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hden_pos : (0 : ℝ) < 1 - x ^ (-s) := by linarith
  have hinv_le : (1 - x ^ (-s))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden_pos (by norm_num)]; linarith
  have hexp : x ^ (-(2 : ℝ) * s) ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul hinv_le hexp (by positivity) (by positivity)

/-- Sharifi 7.1.12 proof (p. 140), bounded tail step. The geometric higher-power tail `Σ_𝔭
N𝔭^{-2s}/(1 - N𝔭^{-s}) = Σ_{𝔭, k≥2} N𝔭^{-ks}` is bounded on a right neighbourhood of `s = 1` (in
fact on `Re s > 1/2`). It dominates the weighted Euler-product log-tail `Σ_{𝔭, k≥2} N𝔭^{-ks}/k`, so
bounding it suffices for the source's "`log ζ_K(s) ~ Σ_𝔭 N𝔭^{-s}`". -/
theorem primeIdealZetaHigherTail_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C := by
  refine ⟨2 * ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs
  have hbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤
        2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ)) := fun 𝔭 ↦
    primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs
  have hnonneg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) :=
    fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
      (by have := absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs; linarith)
  have hsummable_rhs : Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      2 * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ))) :=
    (summable_prime2_absNorm_rpow K one_lt_two).mul_left 2
  exact ((Summable.of_nonneg_of_le hnonneg hbound hsummable_rhs).tsum_le_tsum hbound
    hsummable_rhs).trans_eq tsum_mul_left

/-- The partial Dirichlet sum over `univ`, re-indexed over the bare nonzero-prime subtype. -/
private theorem primeIdealZetaSum_univ_eq_tsum_prime2 (s : ℝ) :
    primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := by
  rw [primeIdealZetaSum_def, ← (Equiv.subtypeEquivRight fun 𝔭 ↦
    ⟨fun h ↦ ⟨mem_univ _, h⟩, And.right⟩).tsum_eq _]
  rfl

/-- For a nonzero prime `𝔭` and `1 < s`, the Euler-factor denominator `1 - N𝔭^{-s}` is positive. -/
private theorem one_sub_absNorm_rpow_pos {𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥)
    {s : ℝ} (hs : 1 < s) : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s) :=
  sub_pos.mpr (absNorm_rpow_neg_lt_one K hp hne hs)

/-- For `0 ≤ x < 1`, `0 ≤ -log(1 - x) - x ≤ x²/(1 - x)`. -/
private theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    0 ≤ - Real.log (1 - x) - x ∧ - Real.log (1 - x) - x ≤ x ^ 2 / (1 - x) := by
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  refine ⟨by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - x by linarith); linarith, ?_⟩
  have key := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    abs_of_nonneg hx0] at key
  linarith [(abs_le.mp key).1]

/-- For `1 < s`, the factor logs `-log(1 - N𝔭^{-s})` are summable over nonzero primes. -/
private theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) :=
  ((Real.summable_log_one_add_of_summable
    (summable_prime2_absNorm_rpow K hs).neg).neg).congr fun _ ↦ rfl

/-- For real `s > 1`, `log ζ_K(s) = Σ_𝔭 -log(1 - N𝔭^{-s})` (Sharifi 7.1.12, p. 140). -/
private theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K (s : ℂ)).re =
      ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))) := by
  set g : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))⁻¹ with hg
  have hgpos : ∀ 𝔭, 0 < g 𝔭 :=
    fun 𝔭 ↦ inv_pos.mpr (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs)
  have hlogsum : Summable (fun 𝔭 ↦ Real.log (g 𝔭)) :=
    (summable_neg_log_one_sub_absNorm_rpow K hs).congr fun 𝔭 ↦ by rw [hg, Real.log_inv]
  have hCprod : HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-(s : ℂ)))⁻¹)
      ((Real.exp (∑' 𝔭, Real.log (g 𝔭)) : ℝ) : ℂ) := by
    refine ((Real.hasProd_of_hasSum_log hgpos hlogsum.hasSum).map Complex.ofRealHom
      Complex.continuous_ofReal).congr_fun fun 𝔭 ↦ ?_
    rw [Function.comp_apply, Complex.ofRealHom_eq_coe, hg]
    push_cast [Complex.ofReal_cpow (show (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) by positivity)]
    ring
  have hre : (dedekindZeta K (s : ℂ)).re = Real.exp (∑' 𝔭, Real.log (g 𝔭)) := by
    rw [dedekindZeta_eq_tprod_primeIdeal K (by simpa using hs), hCprod.tprod_eq,
      Complex.ofReal_re]
  rw [hre, Real.log_exp]
  exact tsum_congr fun 𝔭 ↦ by rw [hg, Real.log_inv]

/-- The remainder `Σ_𝔭 (-log(1 - N𝔭^{-s}) - N𝔭^{-s})` is bounded near `s = 1` (Sharifi 7.1.12). -/
private theorem abs_tsum_neg_log_one_sub_sub_rpow_le :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (- Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))
          - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C := by
  obtain ⟨C, hC⟩ := primeIdealZetaHigherTail_bounded K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_tail hs1
  simp only [mem_Ioi] at hs1
  set f : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ - Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
  set h : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℝ :=
    fun 𝔭 ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2 : ℝ) * s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) with hh
  have hxbound : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) < 1 := fun 𝔭 ↦ absNorm_rpow_neg_lt_one K 𝔭.2.1 𝔭.2.2 hs1
  have hxnn : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      (0 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s) := fun 𝔭 ↦ Real.rpow_nonneg (by positivity) _
  have hfnn : ∀ 𝔭, 0 ≤ f 𝔭 := fun 𝔭 ↦ (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).1
  have hfle : ∀ 𝔭, f 𝔭 ≤ h 𝔭 := fun 𝔭 ↦ by
    refine (neg_log_one_sub_sub_le (hxnn 𝔭) (hxbound 𝔭)).2.trans_eq ?_
    rw [hh]
    congr 1
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
    ring_nf
  have hsummh : Summable h :=
    Summable.of_nonneg_of_le
      (fun 𝔭 ↦ div_nonneg (Real.rpow_nonneg (by positivity) _)
        (one_sub_absNorm_rpow_pos K 𝔭.2.1 𝔭.2.2 hs1).le)
      (fun 𝔭 ↦ primeIdealHigherTail_term_le K 𝔭.2.1 𝔭.2.2 hs1)
      ((summable_prime2_absNorm_rpow K one_lt_two).mul_left 2)
  have hsummf : Summable f := Summable.of_nonneg_of_le hfnn hfle hsummh
  rw [abs_of_nonneg (tsum_nonneg hfnn)]
  exact (hsummf.tsum_le_tsum hfle hsummh).trans hs_tail

/-- Euler-product-log identity: `log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1`
(Sharifi 7.1.12, p. 140). -/
theorem logDedekindZeta_sub_primeIdealZetaSum_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re
      - primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s| ≤ C := by
  obtain ⟨C, hC⟩ := abs_tsum_neg_log_one_sub_sub_rpow_le K
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with s hs_bound hs1
  simp only [mem_Ioi] at hs1
  rwa [log_dedekindZeta_re_eq_tsum_neg_log_one_sub K hs1,
    primeIdealZetaSum_univ_eq_tsum_prime2 K s,
    ← (summable_neg_log_one_sub_absNorm_rpow K hs1).tsum_sub
      (summable_prime2_absNorm_rpow K hs1)]

/-- Sharifi 7.1.12 proof (p. 140), simple-pole identity: `log ζ_K(s) = log(1/(s-1)) + O(1)` as
`s ↓ 1`, from the simple pole of `ζ_K` at `s=1` (mathlib's
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`). -/
theorem logDedekindZeta_sub_log_inv_sub_one_bounded :
    ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ),
      |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C := by
  set r := dedekindZeta_residue K
  have hrpos : 0 < r := dedekindZeta_residue_pos K
  have hF : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K (s : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 r) := by
    refine ((Complex.continuous_re.tendsto _).comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)).congr fun s ↦ ?_
    rw [Function.comp_apply, show ((s : ℂ) - 1) = ((s - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  refine ⟨max |Real.log (r / 2)| |Real.log (2 * r)|, ?_⟩
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (1 : ℝ),
      (s - 1) * (dedekindZeta K (s : ℂ)).re ∈ Ioo (r / 2) (2 * r) :=
    hF.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with s hF_s hs1
  simp only [mem_Ioi] at hs1
  have hsm1 : (0 : ℝ) < s - 1 := by linarith
  obtain ⟨hlo, hhi⟩ := hF_s
  have hFpos : (0 : ℝ) < (s - 1) * (dedekindZeta K (s : ℂ)).re := by linarith
  have hζpos : (0 : ℝ) < (dedekindZeta K (s : ℂ)).re := (mul_pos_iff_of_pos_left hsm1).mp hFpos
  rw [one_div, Real.log_inv, sub_neg_eq_add,
    ← Real.log_mul hζpos.ne' hsm1.ne', mul_comm]
  exact abs_le_max_abs_abs (Real.log_lt_log (by linarith) hlo).le (Real.log_lt_log hFpos hhi).le

/-- Sharifi 7.1.12 proof (p. 140), lower bound: `log(1/(s-1)) - C ≤ Σ_𝔭 N𝔭^{-s}`. -/
theorem log_minus_bounded_le_primeIdealZetaSum :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      Real.log (1 / (s - 1)) - C
        ≤ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- Sharifi 7.1.12 proof (p. 140), upper bound: `Σ_𝔭 N𝔭^{-s} ≤ log(1/(s-1)) + C'`. -/
theorem primeIdealZetaSum_le_log_plus_bounded :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        ≤ Real.log (1 / (s - 1)) + C := by
  obtain ⟨C₁, h₁⟩ := logDedekindZeta_sub_primeIdealZetaSum_bounded K
  obtain ⟨C₂, h₂⟩ := logDedekindZeta_sub_log_inv_sub_one_bounded K
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with s hs₁ hs₂
  linarith [abs_le.mp hs₁, abs_le.mp hs₂]

/-- **Sharifi 7.1.12**, *Algebraic Number Theory*, p. 140.

The denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`. This is the analytic
ingredient that makes the Dirichlet-density definition robust under the L-function comparisons in
the Chebotarev proof. -/
theorem primeIdealZetaSum_univ_tendsto_log :
    Tendsto
      (fun s : ℝ ↦ primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s
        / Real.log (1 / (s - 1)))
      (𝓝[>] 1) (𝓝 1) :=
  tendsto_ratio_one_of_log_pm_bounded _
    (primeIdealZetaSum_le_log_plus_bounded K)
    (log_minus_bounded_le_primeIdealZetaSum K)

/-- The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1` (it is asymptotic to
`log(1/(s-1)) → ∞`). -/
theorem primeIdealZetaSum_univ_tendsto_atTop :
    Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop := by
  have hL := tendsto_log_one_div_sub_one_atTop
  have hhalf : Tendsto (fun s : ℝ ↦ (1 / 2 : ℝ) * Real.log (1 / (s - 1))) (𝓝[>] 1) atTop :=
    hL.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' _ ?_ hhalf
  filter_upwards [(primeIdealZetaSum_univ_tendsto_log K).eventually
      (Ioi_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)), hL.eventually_gt_atTop 0] with s hs hpos
  exact ((lt_div_iff₀ hpos).mp hs).le

/-- For a finite set `S`, the partial sum `Σ_{𝔭 ∈ S} N𝔭^{-s}` is bounded above by the
number of qualifying primes: there are finitely many terms and each `N𝔭^{-s} ≤ 1`
for `s > 0` (since `N𝔭 ≥ 1`). -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite)
    {s : ℝ} (hs : 0 < s) :
    primeIdealZetaSum S s ≤
      Nat.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  have : Finite {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    (hS.subset fun _ hx ↦ hx.1).to_subtype
  have : Fintype {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := Fintype.ofFinite _
  rw [primeIdealZetaSum_def, tsum_fintype, Nat.card_eq_fintype_card]
  calc ∑ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)
      ≤ ∑ _𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (1 : ℝ) := by
        refine Finset.sum_le_sum fun 𝔭 _ ↦ Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.2.2.2)
    _ = (Fintype.card {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} : ℝ) := by simp

/-- **Squeeze to zero density from a constant numerator bound.** If the partial sum `Σ_{𝔭 ∈ U} N𝔭⁻ˢ`
is bounded above by a fixed constant `C` for all `s` near `1` (from the right), then the density
ratio `Σ_U / Σ_univ → 0`, since the denominator `→ ∞`. This is the common engine behind
`hasDirichletDensity_of_finite` (where `C = |U|`) and the degree-`≥ 2` / ramified tail bound in the
Chebotarev fixed-field reduction. -/
theorem tendsto_primeIdealZetaSum_div_univ_zero_of_le_const (U : Set (Ideal (𝓞 K))) (C : ℝ)
    (hbd : ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum U s ≤ C) :
    Tendsto (fun s : ℝ ↦ primeIdealZetaSum U s
      / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s) (𝓝[>] 1) (𝓝 0) := by
  have hUniv := primeIdealZetaSum_univ_tendsto_atTop K
  have hUnivPos : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 < primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s :=
    hUniv.eventually_gt_atTop 0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0)
    (h := fun s ↦ C / primeIdealZetaSum (univ : Set (Ideal (𝓞 K))) s)
    tendsto_const_nhds (tendsto_const_nhds.div_atTop hUniv) ?_ ?_
  · filter_upwards [hUnivPos] with s hpos
    exact div_nonneg (primeIdealZetaSum_nonneg U s) hpos.le
  · filter_upwards [hUnivPos, hbd] with s hpos hle
    exact div_le_div_of_nonneg_right hle hpos.le

/-- **Density of a finite set of primes is `0`** (Sharifi 7.1.13). The numerator `Σ_{𝔭 ∈ S} N𝔭^{-s}`
is bounded (finitely many terms, each `≤ 1`) while the denominator `Σ_𝔭 N𝔭^{-s} → ∞`, so the ratio
`→ 0`. -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) :
    HasDirichletDensity S 0 :=
  tendsto_primeIdealZetaSum_div_univ_zero_of_le_const K S _
    (eventually_nhdsWithin_of_forall fun _ hs ↦
      primeIdealZetaSum_le_card_of_finite K hS (zero_lt_one.trans hs))

/-- The Dirichlet density of the set of all (nonzero) prime ideals is `1`: the ratio
`Σ_𝔭 N𝔭⁻ˢ / Σ_𝔭 N𝔭⁻ˢ` is eventually `1` since the denominator is eventually nonzero (it `→ ∞`). -/
theorem hasDirichletDensity_univ : HasDirichletDensity (univ : Set (Ideal (𝓞 K))) 1 := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(primeIdealZetaSum_univ_tendsto_atTop K).eventually_gt_atTop 0] with s hs
  exact (div_self hs.ne').symm

end Chebotarev
