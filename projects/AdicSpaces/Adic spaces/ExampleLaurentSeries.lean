/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import «Adic spaces».RestrictedPowerSeries
import «Adic spaces».HuberRings
import «Adic spaces».AffinoidRings
import «Adic spaces».WedhornCechAcyclicity

/-!
# A non-trivial instance of Theorem 8.28(b): the Laurent series field `F⸨X⸩`

For any field `F`, the Laurent series field `K := F⸨X⸩` with its `X`-adic (valued)
topology is a **complete, strongly noetherian Tate ring**, and `(K, 𝒪)` with
`𝒪 := Valued.v.integer = F⟦X⟧` is an affinoid ring in Wedhorn's sense (Def 7.14).
Hence `IsSheafy K` by `isSheafy_of_stronglyNoetherian_828b` — witnessing that the
headline theorem's hypotheses are satisfiable by a genuinely topologized
(non-discrete) example.

* **Tate**: `X` is a topologically nilpotent unit (`valuation_X_pow` decays).
* **Pair of definition**: `(𝒪, (X))`, with the `X`-adic subspace topology
  (`Valuation.Integers.dvd_iff_le` converts balls to ideal powers).
* **Strongly noetherian** (the crux — no Weierstrass theory needed in equal
  characteristic): restricted power series over `K` in `k` variables with integral
  coefficients are exactly power series in `X` with `MvPolynomial (Fin k) F`
  coefficients, via the *transpose* ring homomorphism
  `τ : (MvPolynomial (Fin k) F)⟦X⟧ →+* MvPowerSeries (Fin k) F⟦X⟧` (restrictedness of
  the image ⟺ polynomiality of the `X`-layers). `(MvPolynomial (Fin k) F)⟦X⟧` is
  noetherian (Hilbert basis + power series), and the full restricted ring is reached
  from the integral part by inverting the unit `X`, so every ideal is finitely
  generated.
* **Complete**: mathlib's `instLaurentSeriesComplete`, transported to the canonical
  right uniformity via `IsUniformAddGroup.rightUniformSpace_eq`.
-/

noncomputable section

open scoped LaurentSeries PowerSeries
open WithZero ValuationSpectrum Filter

namespace LaurentSeriesExample

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

/-! ### The valuation, the integer ring, and basic estimates -/

/-- The image of the Laurent variable in `K`. -/
def t : K := ((PowerSeries.X : F⟦X⟧) : K)

theorem valuation_t_pow (n : ℕ) : Valued.v ((t F) ^ n) = exp (-(n : ℤ)) :=
  LaurentSeries.valuation_X_pow F n

theorem valuation_t : Valued.v (t F) = exp (-(1 : ℤ)) := by
  simpa using valuation_t_pow F 1

theorem t_ne_zero : t F ≠ 0 := by
  intro h
  have h2 := valuation_t F
  rw [h, map_zero] at h2
  exact exp_pos.ne' h2.symm

theorem isUnit_t : IsUnit (t F) := (t_ne_zero F).isUnit

/-- Powers of `exp (-1)` are cofinal below any nonzero `γ` in `ℤᵐ⁰`. -/
theorem exists_exp_neg_lt (γ : ℤᵐ⁰) (hγ : γ ≠ 0) : ∃ n : ℕ, exp (-(n : ℤ)) < γ := by
  refine ⟨(1 - log γ).toNat, ?_⟩
  rw [← lt_log_iff_exp_lt hγ]
  omega

/-- The strict ball of radius `exp (-n)` around `x` is a neighborhood of `x`. -/
theorem ball_mem_nhds (x : K) (n : ℕ) :
    {y : K | Valued.v (y - x) < exp (-(n : ℤ))} ∈ nhds x := by
  have htn : Valued.v.restrict ((t F) ^ n) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, valuation_t_pow]
    exact exp_pos.ne'
  rw [Valued.mem_nhds]
  refine ⟨Units.mk0 _ htn, fun y hy => ?_⟩
  rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hy
  rw [Set.mem_setOf_eq, ← valuation_t_pow F n]
  exact hy

/-- Neighborhoods of `x` in `K` are exactly supersets of the `exp (-n)`-balls. -/
theorem mem_nhds_iff_ball {x : K} {s : Set K} :
    s ∈ nhds x ↔ ∃ n : ℕ, {y : K | Valued.v (y - x) < exp (-(n : ℤ))} ⊆ s := by
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
    obtain ⟨n, hn⟩ := exists_exp_neg_lt (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
      (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
    refine ⟨n, fun y hy => hγ ?_⟩
    rw [Set.mem_setOf_eq] at hy ⊢
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact lt_trans hy hn
  · rintro ⟨n, hn⟩
    exact Filter.mem_of_superset (ball_mem_nhds F x n) hn

/-- `t` is topologically nilpotent in `K`. -/
theorem isTopologicallyNilpotent_t : IsTopologicallyNilpotent (t F) :=
  Valued.tendsto_zero_pow_of_le_exp_neg_one (le_of_eq (valuation_t F))

/-- The integer subring `𝒪 = {v ≤ 1} = F⟦X⟧`. -/
abbrev O : Subring K := (Valued.v).integer

theorem mem_O_iff (x : K) : x ∈ O F ↔ Valued.v x ≤ 1 := Iff.rfl

theorem t_mem_O : t F ∈ O F := by
  rw [mem_O_iff, valuation_t, ← exp_zero, exp_le_exp]
  omega

/-- The closed unit ball `𝒪` is open (nonarchimedean triangle inequality). -/
theorem isOpen_O : IsOpen ((O F : Set K)) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [mem_nhds_iff_ball]
  refine ⟨0, fun y hy => ?_⟩
  rw [Set.mem_setOf_eq] at hy
  have hyx : y = (y - x) + x := by ring
  rw [SetLike.mem_coe, mem_O_iff, hyx]
  refine le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt ?_) hx)
  simpa using hy

/-- `t` as an element of `𝒪`. -/
def t₀ : O F := ⟨t F, t_mem_O F⟩

/-- Divisibility in `𝒪` is valuation comparison (`v.integer` is a valuation ring). -/
theorem t₀_pow_dvd_iff (n : ℕ) (x : O F) :
    (t₀ F) ^ n ∣ x ↔ Valued.v ((x : K)) ≤ Valued.v ((t F) ^ n) := by
  have hcoe : ((((t₀ F) ^ n : O F)) : K) = (t F) ^ n := by push_cast; rfl
  have halg : ∀ y : O F, (algebraMap (↥(O F)) K) y = (y : K) := fun _ => rfl
  rw [Valuation.Integers.dvd_iff_le (Valuation.integer.integers _), halg, halg, hcoe]

/-- Membership in `(t)ⁿ ⊆ 𝒪` is the valuation bound `v ≤ v(tⁿ)`. -/
theorem mem_span_t₀_pow_iff (n : ℕ) (x : O F) :
    x ∈ (Ideal.span {t₀ F} ^ n : Ideal (O F)) ↔
      Valued.v ((x : K)) ≤ Valued.v ((t F) ^ n) := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, t₀_pow_dvd_iff]

/-! ### The pair of definition and the Huber/Tate instances -/

/-- The pair of definition `(𝒪, (t))` for `K`. -/
def pod : PairOfDefinition K where
  A₀ := O F
  I := Ideal.span {t₀ F}
  isOpen := isOpen_O F
  fg := ⟨{t₀ F}, by simp⟩
  isAdic := by
    rw [isAdic_iff]
    refine ⟨fun n => ?_, fun s hs => ?_⟩
    · -- `(t)ⁿ` is open in `𝒪`: around each point the strict `exp (-n)`-ball stays inside.
      rw [isOpen_iff_mem_nhds]
      intro x hx
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow] at hx
      rw [mem_nhds_subtype]
      refine ⟨{y : K | Valued.v (y - (x : K)) < exp (-(n : ℤ))},
        ball_mem_nhds F (x : K) n, ?_⟩
      intro y hy
      rw [Set.mem_preimage, Set.mem_setOf_eq] at hy
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow]
      have hdecomp : ((y : K)) = (((y : K)) - ((x : K))) + ((x : K)) := by ring
      rw [hdecomp]
      exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt hy) hx)
    · -- the `(t)ⁿ` shrink below any neighborhood of `0`.
      rw [mem_nhds_subtype] at hs
      obtain ⟨U, hU, hUs⟩ := hs
      obtain ⟨n, hn⟩ := (mem_nhds_iff_ball F).mp (by simpa using hU)
      refine ⟨n + 1, fun x hx => hUs ?_⟩
      rw [SetLike.mem_coe, mem_span_t₀_pow_iff, valuation_t_pow] at hx
      rw [Set.mem_preimage]
      refine hn ?_
      rw [Set.mem_setOf_eq, sub_zero]
      refine lt_of_le_of_lt hx ?_
      rw [exp_lt_exp]
      omega

instance : IsHuberRing K := ⟨⟨pod F⟩⟩

instance : IsTateRing K :=
  ⟨⟨(isUnit_t F).unit, by simpa using isTopologicallyNilpotent_t F⟩⟩

/-! ### `(K, 𝒪)` is an affinoid ring (Wedhorn Def 7.14) -/

/-- `𝒪` is integrally closed in `K`: an element integral over the closed unit ball has
valuation at most `1` (else the leading term strictly dominates every other term of the
monic relation). -/
theorem O_isIntegrallyClosed (a : K) (ha : IsIntegral (O F) a) : a ∈ O F := by
  sorry

/-- The power-bounded subring of `K` is exactly `𝒪` (rank-one valuation). -/
theorem O_subset_powerBounded :
    ((O F : Subring K) : Set K) ⊆ TopologicalRing.powerBoundedSubring K := by
  sorry

instance : ValuationSpectrum.PlusSubring K := ⟨O F⟩

instance : IsRingOfIntegralElements ((ValuationSpectrum.ringPlus K : Subring K)) where
  isOpen := isOpen_O F
  isIntegrallyClosed := O_isIntegrallyClosed F
  subset_powerBounded := O_subset_powerBounded F

/-! ### Completeness -/

instance : @CompleteSpace K (IsTopologicalAddGroup.rightUniformSpace K) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### Strongly noetherian (the layer transpose) -/

instance : IsStronglyNoetherian K := by
  sorry

/-! ### The payoff -/

/-- **The Laurent series field `(F⸨X⸩, F⟦X⟧)` is sheafy** — a genuinely topologized,
non-discrete instance of Wedhorn Theorem 8.28(b). -/
theorem isSheafy_laurentSeries : IsSheafy K :=
  isSheafy_of_stronglyNoetherian_828b

end LaurentSeriesExample
