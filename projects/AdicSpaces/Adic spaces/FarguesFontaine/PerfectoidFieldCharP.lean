/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».PerfectoidRing
import «Adic spaces».PseudoUniformizer
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect

/-!
# Perfectoid fields of characteristic p: the base field of the Fargues--Fontaine curve

Let `F` be a perfectoid field of characteristic `p` (the project's `IsPerfectoidField p F`
with `CharP F p`), with ring of integers `O_F = F°` (power-bounded elements) and a
pseudo-uniformizer `ϖ`. This file establishes the facts about `O_F` needed to build
`A_inf = W(O_F)` in `AinfHuber.lean`:

* `O_F` is an integral domain of characteristic `p`;
* `O_F` is a perfect ring (`PerfectRing (OF F) p`);
* the `ϖ`-adic filtration `ϖ^n O_F` is a basis of neighbourhoods of `0` in the subspace
  topology, and `O_F` is `ϖ`-adically separated and complete
  (`IsHausdorff`/`IsAdicComplete (Ideal.span {ϖ}) (OF F)`).

## Sources

* [BFHHLWY, *Extensions of vector bundles on the Fargues–Fontaine curve*][bfhhlwy2018],
  Definition 2.1.1 (the setting: `F/F_q` perfectoid, `F°`, pseudouniformizer `ϖ`).
* [B. Bhatt, *Lecture notes for a class on perfectoid spaces*][bhatt679], §3.1
  (Example 3.1.2(3): a nonarchimedean field of characteristic `p` is perfectoid iff it is
  perfect; Corollary 3.2.3 for the `t`-adic completeness pattern).
* [Kedlaya, *Sheaves, stacks, and shtukas* (AWS 2017)][kedlaya-aws], Hypothesis 3.1.1.
-/

open TopologicalRing ValuationSpectrum

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- The ring of integers `O_F = F°` of a perfectoid field, as a type.

This is the subtype of the power-bounded subring; it is a commutative ring via the
`Subring` instance. (Binders are explicit and minimal — in particular `p`-free — so the
signature is immune to instance-search-path drift in the section variables.) -/
abbrev OF (F : Type u) [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
    [NonarchimedeanRing F] : Type u :=
  ↥(powerBoundedSubring.toSubring F)

/-- A pseudo-uniformizer `ϖ : Fˣ`, viewed as an element of `O_F`.

A pseudo-uniformizer is a topologically nilpotent unit; topologically nilpotent elements
are power-bounded, so `ϖ` lies in `F° = O_F`.

Source: [BFHHLWY, Def 2.1.1] ("pseudouniformizer ϖ", an element of `F°`). -/
def PseudoUniformizer.toOF (F : Type u) [CommRing F] [TopologicalSpace F]
    [IsTopologicalRing F] [NonarchimedeanRing F] (ϖ : PseudoUniformizer F) : OF F :=
  ⟨((ϖ.val : Fˣ) : F), (PseudoUniformizer.isTopologicallyNilpotent ϖ).isPowerBounded⟩

/-- `O_F` is an integral domain (a subring of a field). -/
instance : IsDomain (OF F) := by infer_instance

/-- `O_F` has characteristic `p` (a subring of a field of characteristic `p`).

Source: immediate from the setting of [BFHHLWY, Def 2.1.1]. -/
instance instCharPOF : CharP (OF F) p where
  cast_eq_zero_iff n := by
    rw [← CharP.cast_eq_zero_iff F p n]
    exact ⟨fun h => by simpa using congrArg (fun x : OF F => (x : F)) h,
      fun h => Subtype.ext (by push_cast; exact h)⟩

/-- The Frobenius `x ↦ x^p` is surjective on `O_F` (`O_F` is semiperfect): the
characteristic-`p` content of the perfectoid condition.

Source: [Bhatt, §3.1, Example 3.1.2(3)]: "Let K be a NA field of characteristic p. Then
K is perfectoid if and only if K is perfect. In this case, semiperfectness of K° implies
its perfectness". -/
theorem frobenius_surjective_OF : Function.Surjective (frobenius (OF F) p) := by
  intro x
  obtain ⟨y, hy, z, -, hxyz⟩ := IsPerfectoidRing.frobenius_surj (p := p) (x : F) x.2
  exact ⟨⟨y, hy⟩, Subtype.ext (by simp [frobenius_def, hxyz])⟩

/-- `O_F` is a perfect ring: the Frobenius is bijective.

Injectivity holds because `O_F` is a domain of characteristic `p`; surjectivity is
`frobenius_surjective_OF`.

Source: [Bhatt, §3.1, Example 3.1.2(3)], as above. -/
instance instPerfectRingOF : PerfectRing (OF F) p :=
  PerfectRing.ofSurjective _ p (frobenius_surjective_OF p F)

/-- The pseudo-uniformizer is nonzero in `O_F`. -/
theorem PseudoUniformizer.toOF_ne_zero (ϖ : PseudoUniformizer F) :
    PseudoUniformizer.toOF F ϖ ≠ 0 := by
  intro h
  exact ((ϖ.val : Fˣ)).ne_zero (by simpa [PseudoUniformizer.toOF] using congrArg Subtype.val h)

/-- Each `ϖ^n O_F` is a neighbourhood of `0` in `O_F` (subspace topology from `F`).

This is the standard fact that for a Tate ring with ring of definition `F°` and
pseudo-uniformizer `ϖ`, the sets `ϖ^n F°` form a neighbourhood basis of `0`.

Source: [Wedhorn, *Adic Spaces*, §5.30/6.11-style standard facts on Tate rings]; used
implicitly in [Kedlaya-AWS, Hyp. 3.1.1 and Rem. 3.1.9]. -/
theorem span_toOF_pow_mem_nhds_zero [IsPerfectoidField p F] (ϖ : PseudoUniformizer F) (n : ℕ) :
    ((Ideal.span {PseudoUniformizer.toOF F ϖ} ^ n : Ideal (OF F)) : Set (OF F)) ∈
      nhds (0 : OF F) := by
  obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := F)
  refine (mem_nhds_subtype _ _ _).mpr ⟨_, ((ϖ.val.isUnit.pow n).isOpenMap_smul _
    P.isOpen_powerBoundedSubring).mem_nhds ⟨0, isPowerBounded_zero, smul_zero _⟩, ?_⟩
  rintro y ⟨b, hb, hby⟩
  rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨⟨b, hb⟩, Subtype.ext <| by simpa [PseudoUniformizer.toOF, mul_comm] using hby⟩

/-- Every neighbourhood of `0` in `O_F` contains some `ϖ^n O_F`.

This is topological nilpotence of `ϖ` plus boundedness of `O_F` (uniformity of `F`):
`ϖ^n · F° → 0` uniformly.

Source: standard Tate-ring fact, as for `span_toOF_pow_mem_nhds_zero`. -/
theorem exists_span_toOF_pow_subset_of_mem_nhds [IsPerfectoidField p F] (ϖ : PseudoUniformizer F)
    {U : Set (OF F)} (hU : U ∈ nhds (0 : OF F)) :
    ∃ n : ℕ, ((Ideal.span {PseudoUniformizer.toOF F ϖ} ^ n : Ideal (OF F)) : Set (OF F)) ⊆ U := by
  obtain ⟨U', hU', hU'sub⟩ := (mem_nhds_subtype _ _ _).mp hU
  obtain ⟨V, hV, hFV⟩ := (IsPerfectoidRing.uniform (p := p) (A := F)).isBounded_powerBounded U' hU'
  obtain ⟨n, hn⟩ := ϖ.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds hV
  refine ⟨n, fun y hy ↦ ?_⟩
  rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨c, rfl⟩ := hy
  exact hU'sub <| by simpa [PseudoUniformizer.toOF] using hFV (Set.mul_mem_mul c.2 hn)

/-- `O_F` is `ϖ`-adically separated: `⋂ n, ϖ^n O_F = 0`.

From `exists_span_toOF_pow_subset_of_mem_nhds` and the fact that `F` (hence `O_F`) is T0 as a
topological group, the intersection of the `ϖ^n O_F` is contained in every neighbourhood
of `0`, hence is `0`.

Source: [Bhatt, Cor. 3.2.3] pattern (t-adic topology on `K°` is separated and complete). -/
theorem isHausdorff_span_toOF [IsPerfectoidField p F] (ϖ : PseudoUniformizer F) :
    IsHausdorff (Ideal.span {PseudoUniformizer.toOF F ϖ}) (OF F) := by
  haveI := IsPerfectoidRing.t0 (p := p) (A := F)
  constructor
  intro x hx
  have hmem : ∀ U ∈ nhds (0 : OF F), x ∈ U := by
    intro U hU
    obtain ⟨n, hn⟩ := exists_span_toOF_pow_subset_of_mem_nhds p F ϖ hU
    have := SModEq.sub_mem.mp (hx n)
    rw [sub_zero, Ideal.smul_eq_mul, Ideal.mul_top] at this
    exact hn this
  have h0 : (0 : OF F) ∈ closure ({x} : Set (OF F)) :=
    mem_closure_iff_nhds.mpr fun U hU ↦ ⟨x, hmem U hU, rfl⟩
  rw [IsClosed.closure_eq isClosed_singleton, Set.mem_singleton_iff] at h0
  exact h0.symm

/-- `O_F` is `ϖ`-adically complete.

A `ϖ`-adic Cauchy sequence is Cauchy for the subspace uniformity (by
`span_toOF_pow_mem_nhds_zero`), hence converges in `F` by completeness; the limit is
power-bounded (a limit of a bounded set in a uniform Tate ring), i.e. lies in `O_F`, and
the convergence is `ϖ`-adic by `exists_span_toOF_pow_subset_of_mem_nhds`.

Source: [Bhatt, Cor. 3.2.3]: "K°♭ is t-adically complete, and the t-adic topology
coincides with the given topology" — the same statement for a char-p perfectoid field
directly. -/
theorem isAdicComplete_span_toOF [IsPerfectoidField p F] (ϖ : PseudoUniformizer F) :
    IsAdicComplete (Ideal.span {PseudoUniformizer.toOF F ϖ}) (OF F) := by
  haveI := IsPerfectoidRing.complete (p := p) (A := F)
  haveI := IsPerfectoidRing.uniformAddGroup (p := p) (A := F)
  haveI := IsPerfectoidRing.t0 (p := p) (A := F)
  haveI := IsPerfectoidRing.uniform (p := p) (A := F)
  have htop := IsPerfectoidRing.topologyEq (p := p) (A := F)
  set I : Ideal (OF F) := Ideal.span {PseudoUniformizer.toOF F ϖ} with hI
  have hprec : IsPrecomplete I (OF F) := by
    constructor
    intro f hf
    -- Membership form of the coherence hypothesis: `f m - f n ∈ I^m` for `m ≤ n`.
    have hf' : ∀ {m n : ℕ}, m ≤ n → f m - f n ∈ I ^ m := by
      intro m n h
      have := SModEq.sub_mem.mp (hf h)
      rwa [Ideal.smul_eq_mul, Ideal.mul_top] at this
    -- The coerced sequence is Cauchy in `F`: differences eventually land in any
    -- `W ∈ 𝓝 0`, symmetrized through an open additive subgroup `G ⊆ W`.
    have hsmall : ∀ W ∈ nhds (0 : F), ∃ N, ∀ m n, N ≤ m → N ≤ n →
        (f m : F) - (f n : F) ∈ W := by
      intro W hW
      obtain ⟨G, hGW⟩ := NonarchimedeanAddGroup.is_nonarchimedean W hW
      obtain ⟨V, hV, hFV⟩ := IsUniform.isBounded_powerBounded (A := F) (G : Set F)
        (G.isOpen.mem_nhds G.zero_mem')
      obtain ⟨N, hN⟩ := ϖ.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds hV
      have key : ∀ {m n : ℕ}, N ≤ m → m ≤ n → (f m : F) - (f n : F) ∈ (G : Set F) := by
        intro m n hNm hmn
        have hmem : f m - f n ∈ I ^ N := Ideal.pow_le_pow_right hNm (hf' hmn)
        rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
        obtain ⟨c, hc⟩ := hmem
        have hval : (f m : F) - (f n : F) = (c : F) * ((ϖ.val : Fˣ) : F) ^ N := by
          have h := congrArg Subtype.val hc
          push_cast [PseudoUniformizer.toOF] at h
          exact h.symm
        rw [hval]
        exact hFV (Set.mul_mem_mul c.2 hN)
      refine ⟨N, fun m n hm hn ↦ ?_⟩
      rcases le_total m n with h | h
      · exact hGW (key hm h)
      · rw [show (f m : F) - (f n : F) = -((f n : F) - (f m : F)) from by ring]
        exact hGW (neg_mem (key hn h))
    -- Convergence in `F` (complete for its uniform structure), limit power-bounded.
    have hCauchy : CauchySeq (fun n ↦ (f n : F)) := by
      rw [CauchySeq, IsUniformAddGroup.cauchy_map_iff_tendsto_swapped]
      refine ⟨Filter.atTop_neBot, ?_⟩
      rw [Filter.Tendsto, Filter.map_le_iff_le_comap]
      intro U hU
      obtain ⟨W, hW, hWU⟩ := Filter.mem_comap.mp hU
      rw [htop] at hW
      obtain ⟨N, hN⟩ := hsmall W hW
      rw [Filter.prod_atTop_atTop_eq, Filter.mem_atTop_sets]
      exact ⟨(N, N), fun ⟨m, n⟩ ⟨hm, hn⟩ ↦ hWU (hN n m hn hm)⟩
    obtain ⟨L₀, hL₀⟩ := cauchySeq_tendsto_of_complete hCauchy
    have hL₀' : Filter.Tendsto (fun n ↦ (f n : F)) Filter.atTop
        (@nhds F ‹TopologicalSpace F› L₀) := by rwa [htop] at hL₀
    have hL₀pb : IsPowerBounded L₀ :=
      IsPerfectoidRing.isPowerBounded_of_tendsto_of_powerBounded (fun n ↦ (f n).2) hL₀'
    -- The limit works: `f n - L ∈ I^n` because `I^n` is an open, hence closed, subgroup.
    refine ⟨⟨L₀, hL₀pb⟩, fun n ↦ ?_⟩
    have hSopen : IsOpen ((I ^ n : Ideal (OF F)) : Set (OF F)) :=
      AddSubgroup.isOpen_of_mem_nhds (I ^ n).toAddSubgroup
        (span_toOF_pow_mem_nhds_zero p F ϖ n)
    have hSclosed : IsClosed ((I ^ n : Ideal (OF F)) : Set (OF F)) :=
      AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hSopen
    have htend : Filter.Tendsto (fun m ↦ f n - f m) Filter.atTop
        (nhds (f n - ⟨L₀, hL₀pb⟩)) :=
      tendsto_const_nhds.sub (tendsto_subtype_rng.mpr hL₀')
    have hev : ∀ᶠ m in Filter.atTop, f n - f m ∈ ((I ^ n : Ideal (OF F)) : Set (OF F)) :=
      Filter.eventually_atTop.mpr ⟨n, fun m hm ↦ hf' hm⟩
    have hlim : f n - ⟨L₀, hL₀pb⟩ ∈ ((I ^ n : Ideal (OF F)) : Set (OF F)) :=
      hSclosed.mem_of_tendsto htend hev
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hlim
  exact { toIsHausdorff := isHausdorff_span_toOF p F ϖ, toIsPrecomplete := hprec }

end FarguesFontaine

end
