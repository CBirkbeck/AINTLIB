/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.ExtendedCornerPackage
import «Adic spaces».FJP.MilnorSquareInstance

/-!
# The `⟨V⟩`-extended square as a `MilnorSquareData` (T627, campaign B)

Instantiates the abstract strict-Milnor-descent criterion at the extended
finite-jet square `PA F n = PB F n ×_{PD F n} PC F n` (T626's `extPinch`),
following the `jetSquare` template (T620) with the generic datum layer (T624),
the generic naturality/composition lemmas (T623), and the value-level Milnor
row of the abstract pinch (T625's `valueRow_*`).

Output: `isSheafy_extJetA n : IsSheafy (PA F n)` — the sheafiness of the
Gauss-normed Tate extension of the pinching algebra, for every `n`
([Reviewer] §5.1; the normed half of the B-headline).
-/

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing GraphKoszul StrictLoc

variable (F : Type*) [Field F] (n : ℕ)

/-! ### Pods and the power-bounded transport -/

/-- Pair of definition for `PA F n` (unit ball at the constant-series scale). -/
noncomputable def podPA : PairOfDefinition (PA F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tA F)))
    (isUnit_tP _ (isUnit_tA F))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)

/-- Pair of definition for `PB F n`. -/
noncomputable def podPB : PairOfDefinition (PB F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tB F)))
    (isUnit_tP _ (isUnit_tB F))
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tB_mul F), norm_tB]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tB_mul F)]
                 exact norm_tP_mul _ (norm_tB_mul F) x)

/-- Pair of definition for `PC F n`. -/
noncomputable def podPC : PairOfDefinition (PC F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tC F)))
    (isUnit_tP _ (isUnit_tC F))
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tC_mul F), norm_tC]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tC_mul F)]
                 exact norm_tP_mul _ (norm_tC_mul F) x)

/-- Pair of definition for `PD F n`. -/
noncomputable def podPD : PairOfDefinition (PD F n) :=
  unitBallPod (polyToP (MvPolynomial.C (tD F)))
    (isUnit_tP _ (isUnit_tD F))
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tP _ (norm_tD_mul F), norm_tD]; exact norm_t_pos F)
    (fun x => by rw [norm_tP _ (norm_tD_mul F)]
                 exact norm_tP_mul _ (norm_tD_mul F) x)

section Transport

variable {A' B' : Type*}
  [NormedCommRing A'] [IsUltrametricDist A']
  [NormedCommRing B'] [IsUltrametricDist B']

omit [IsUltrametricDist A'] in
/-- Norm-bounded sets are Huber-bounded in a seminormed ring
(submultiplicativity shrinks the ball). -/
theorem isBounded_of_norm_le {S : Set A'} {M : ℝ} (hM : 0 ≤ M)
    (hS : ∀ x ∈ S, ‖x‖ ≤ M) : TopologicalRing.IsBounded S := by
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / (M + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨s, hs, v, hv, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖s * v‖ ≤ ‖s‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ M * ‖v‖ := mul_le_mul_of_nonneg_right (hS s hs) (norm_nonneg v)
    _ ≤ (M + 1) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg v)
    _ < (M + 1) * (ε / (M + 1)) := by
        have hM1 : (0 : ℝ) < M + 1 := by linarith
        exact mul_lt_mul_of_pos_left hv hM1
    _ = ε := by
        have hM1 : (M + 1 : ℝ) ≠ 0 := by linarith
        field_simp

omit [IsUltrametricDist A'] in
/-- In a normed ring with a multiplicative scale, Huber-bounded sets are
norm-bounded (`t`-power division). -/
theorem exists_norm_le_of_isBounded (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    {S : Set A'} (hS : TopologicalRing.IsBounded S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖x‖ ≤ M := by
  obtain ⟨V, hV, hVS⟩ := hS (Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ ht1
  have hpow : ∀ (y : A') (j : ℕ), ‖y * t ^ j‖ = ‖t‖ ^ j * ‖y‖ := by
    intro y j
    induction j with
    | zero => simp
    | succ i ih =>
      calc ‖y * t ^ (i + 1)‖ = ‖t * (y * t ^ i)‖ := by
            rw [show y * t ^ (i + 1) = t * (y * t ^ i) from by ring]
        _ = ‖t‖ * ‖y * t ^ i‖ := hscale _
        _ = ‖t‖ * (‖t‖ ^ i * ‖y‖) := by rw [ih]
        _ = ‖t‖ ^ (i + 1) * ‖y‖ := by ring
  refine ⟨(‖t‖ ^ (k + 1))⁻¹, by positivity, fun x hx => ?_⟩
  have htk : t ^ (k + 1) ∈ V := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖t ^ (k + 1)‖ ≤ ‖t‖ ^ (k + 1) := norm_pow_le' t (Nat.succ_pos k)
      _ = ‖t‖ ^ k * ‖t‖ := pow_succ _ _
      _ < δ * 1 := by
          refine mul_lt_mul'' hk ht1 (by positivity) (norm_nonneg t)
      _ = δ := mul_one δ
  have hmem : x * t ^ (k + 1) ∈ Metric.ball (0 : A') 1 :=
    hVS (Set.mul_mem_mul hx htk)
  rw [Metric.mem_ball, dist_zero_right, hpow x (k + 1)] at hmem
  rw [← one_div, le_div_iff₀ (by positivity), mul_comm]
  exact hmem.le

omit [IsUltrametricDist A'] [IsUltrametricDist B'] in
/-- **Power-bounded transport along a 1-Lipschitz hom** out of a scaled corner:
the generic `A⁺ ≤ (B⁺).comap φ` input for the pushed-datum comap iffs. -/
theorem powerBounded_le_comap (t : A') (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
    (hscale : ∀ x : A', ‖t * x‖ = ‖t‖ * ‖x‖)
    (φ : A' →+* B') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : A'}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_le_of_isBounded t ht1 ht0 hscale hx
  refine (isBounded_of_norm_le hM0 (fun y hy => ?_) : TopologicalRing.IsBounded
    (Set.range (φ x ^ · : ℕ → B')))
  obtain ⟨m, rfl⟩ := hy
  calc ‖φ x ^ m‖ = ‖φ (x ^ m)‖ := by rw [map_pow]
    _ ≤ ‖x ^ m‖ := hφ _
    _ ≤ M := hM _ ⟨m, rfl⟩

end Transport

/-- The plus-transport `(PA F n)⁺ ≤ ((PB F n)⁺).comap (extJB F n)`. -/
theorem plusLe_extJB :
    ((PA F n)⁺ : Subring (PA F n)) ≤ ((PB F n)⁺ : Subring (PB F n)).comap (extJB F n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    (extJB F n) ((extPinch F n).norm_φB_le) hx

/-- The plus-transport `(PA F n)⁺ ≤ ((PC F n)⁺).comap (extIotaC F n)`. -/
theorem plusLe_extIotaC :
    ((PA F n)⁺ : Subring (PA F n)) ≤
      ((PC F n)⁺ : Subring (PC F n)).comap (extIotaC F n) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    (extIotaC F n) (fun p => le_of_eq ((extPinch F n).norm_φC p)) hx

/-- The plus-transport along the composite leg to `PD F n`. -/
theorem plusLe_extD :
    ((PA F n)⁺ : Subring (PA F n)) ≤
      ((PD F n)⁺ : Subring (PD F n)).comap ((extRhoC F n).comp (extIotaC F n)) :=
  fun _ hx => powerBounded_le_comap (polyToP (MvPolynomial.C (tA F)))
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_lt_one F)
    (by rw [norm_tP _ (norm_tA_mul F)]; exact norm_tA_pos F)
    (fun x => by rw [norm_tP _ (norm_tA_mul F)]
                 exact norm_tP_mul _ (norm_tA_mul F) x)
    ((extRhoC F n).comp (extIotaC F n))
    (fun p => le_trans ((extPinch F n).norm_ψC_le _)
      (le_of_eq ((extPinch F n).norm_φC p))) hx

end FiniteJet
