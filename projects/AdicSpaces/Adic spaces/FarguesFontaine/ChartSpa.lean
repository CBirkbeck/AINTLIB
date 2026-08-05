/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartComparison
import «Adic spaces».NonTateRationalOpenHomeomorph

/-!
# The chart spectra of the Big windows (D-ii)

`Spa (B_n, B_n⁺) ≃ₜ` the trace of `bigWindow n` on `Spa (A_inf, A_inf)`:

* `FarguesFontaine.isTateRing_presheafChart` / `isTateRing_bigWindowChart` :
  the chart presheaf values are Tate rings (transported from `B^I`);
* `FarguesFontaine.spaChartHomeoBigWindow` / `spaChartHomeoBigWindowNeg` :
  the chart homeomorphisms, via the non-Tate-base Wedhorn 8.2(2)
  (`spaPresheafValueHomeomorphRationalOpen'`) with the nilpotent unit
  supplied by the chart ring's own Tate structure, composed with the
  Big-window rational identifications.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

/-- The trace of a rational subset (with nonempty `T`) on `Spa (A, A⁺)` is
open. -/
theorem isOpen_rationalOpen_trace {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [ValuationSpectrum.PlusSubring A]
    {T : Finset A} (hT : T.Nonempty) (s : A) :
    IsOpen {x : ↥(Spa A (ringPlus A)) | (x : Spv A) ∈ rationalOpen T s} := by
  have htrace : {x : ↥(Spa A (ringPlus A)) | (x : Spv A) ∈ rationalOpen T s}
      = Subtype.val ⁻¹' (⋂ t ∈ (T : Set A), basicOpen t s) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      rationalOpen_eq_spa_inter hT s, Set.mem_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  rw [htrace]
  refine IsOpen.preimage continuous_subtype_val ?_
  refine Set.Finite.isOpen_biInter (Set.finite_coe_iff.mp (by
    exact Set.Finite.to_subtype (T.finite_toSet))) ?_
  intro t ht
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨t, s, rfl⟩

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

noncomputable local instance instDecEqAinfChartSpa : DecidableEq (Ainf p F) :=
  Classical.decEq _

include hρ₁0 hρ₁1 hρ₂0 hρ₂1 in
/-- **The chart presheaf value is a Tate ring** (transported from `B^I`). -/
theorem isTateRing_presheafChart (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    IsTateRing (presheafValue (chartData p F ϖ 1 b a b)) :=
  isTateRing_congr
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
    (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
    (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)

/-- The Big-window chart datum is Tate at the concrete `(a, b) = (p, 1)`
interval (any twisted uniformizer). -/
theorem isTateRing_bigWindowChart (ϖ' : PseudoUniformizer F) :
    IsTateRing (presheafValue (chartData p F ϖ' 1 1 p 1)) := by
  have hp : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  exact isTateRing_presheafChart p F ϖ'
    (hρ₁0 := vpi_pos p F ϖ') (hρ₁1 := perfectoidValuation_toOF_lt_one p F ϖ')
    (hρ₂0 := rhoRight_pos p F ϖ' p 1)
    (hρ₂1 := rhoRight_lt_one p F ϖ' p 1 (by omega) one_pos)
    p 1 (by omega) one_pos (by omega) rfl
    (by
      rw [rhoRight_pow_exact p F ϖ' p 1 (by omega), pow_one])


/-- **The Big-window chart homeomorphism (nonnegative side)**:
`Spa (B_n, B_n⁺) ≃ₜ` the trace of `bigWindow n` — Wedhorn 8.2(2) over the
non-Tate base `A_inf`, with the nilpotent unit supplied by the chart ring's
own Tate structure. -/
noncomputable def spaChartHomeoBigWindow (n : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))))
      ≃ₜ ↥(bigWindow p F ϖ (n : ℤ) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have : IsTateRing (presheafValue (chartData p F
      (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)) :=
    isTateRing_bigWindowChart p F (PseudoUniformizer.frobRoot p F ϖ n)
  (spaPresheafValueHomeomorphRationalOpen'
    (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))).choose
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))).choose_spec).trans
    (Homeomorph.setCongr (by
      rw [bigWindow_eq_rationalOpen_ofNat p F ϖ n hp]
      rfl))

/-- **The Big-window chart homeomorphism (negative side).** -/
noncomputable def spaChartHomeoBigWindowNeg (m : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))))
      ≃ₜ ↥(bigWindow p F ϖ (-(m : ℤ)) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  have : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  have : IsTateRing (presheafValue (chartData p F
      (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1)) :=
    isTateRing_bigWindowChart p F _
  (spaPresheafValueHomeomorphRationalOpen'
    (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1)
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))).choose
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))).choose_spec).trans
    (Homeomorph.setCongr (by
      rw [bigWindow_eq_rationalOpen_neg p F ϖ m hp]
      rfl))

/-- `chartT` is nonempty. -/
theorem chartT_nonempty (ϖ' : PseudoUniformizer F) (a b : ℕ) :
    (chartT p F ϖ' a b).Nonempty := by
  rw [chartT]
  exact ⟨_, Finset.mem_insert_self _ _⟩

/-- **The Big-window traces are open in `Spa (A_inf, A_inf)`.** -/
theorem isOpen_bigWindow_trace (n : ℤ) (hp : 1 < p) :
    IsOpen {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ bigWindow p F ϖ n} := by
  rcases n with n | m
  · rw [show (Int.ofNat n) = (n : ℤ) from rfl]
    have h := bigWindow_eq_rationalOpen_ofNat p F ϖ n hp
    rw [show {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
        (x : Spv (Ainf p F)) ∈ bigWindow p F ϖ (n : ℤ)}
      = {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
        (x : Spv (Ainf p F)) ∈ rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1)} by
      rw [← h]]
    exact isOpen_rationalOpen_trace (chartT_nonempty p F _ p 1) _
  · rw [show (Int.negSucc m) = -((m + 1 : ℕ) : ℤ) by
      rw [Int.negSucc_eq]
      push_cast
      ring]
    have h := bigWindow_eq_rationalOpen_neg p F ϖ (m + 1) hp
    rw [show {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
        (x : Spv (Ainf p F)) ∈ bigWindow p F ϖ (-((m + 1 : ℕ) : ℤ))}
      = {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
        (x : Spv (Ainf p F)) ∈ rationalOpen
          (chartT p F (PseudoUniformizer.pPow F ϖ (p ^ (m + 1))
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) (m + 1))) p 1)
          (chartS p F (PseudoUniformizer.pPow F ϖ (p ^ (m + 1))
            (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) (m + 1))) 1 1)} by
      rw [← h]]
    exact isOpen_rationalOpen_trace (chartT_nonempty p F _ p 1) _

/-- **The `Y`-trace is open in `Spa (A_inf, A_inf)`** (covered by the Big
windows). -/
theorem isOpen_Y_trace (hp : 1 < p) :
    IsOpen {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ Y p F ϖ} := by
  rw [show {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ Y p F ϖ}
    = ⋃ n : ℤ, {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ bigWindow p F ϖ n} by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [show (Y p F ϖ) = ⋃ n : ℤ, bigWindow p F ϖ n from
      Y_eq_iUnion_bigWindow p F ϖ hp]
    simp]
  exact isOpen_iUnion fun n => isOpen_bigWindow_trace p F ϖ n hp

/-- **The right-edge circle inside the `n`-th chart spectrum**: under the chart
homeomorphism, the trace of the overlap circle `bigWindow n ∩ bigWindow (n+1)`
corresponds to the rational subset of `Spa (B_n)` with the image parameters of
the circle datum. -/
theorem spaChartHomeoBigWindow_preimage_circle (n : ℕ) (hp : 1 < p)
    [DecidableEq (presheafValue (chartData p F
      (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))]
    (w : ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))))) :
    ((spaChartHomeoBigWindow p F ϖ n hp w :
        ↥(bigWindow p F ϖ (n : ℤ) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ bigWindow p F ϖ (n : ℤ) ∩ bigWindow p F ϖ ((n : ℤ) + 1)
      ↔ (w : Spv (presheafValue (chartData p F
          (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)))
        ∈ rationalOpen
          ((chartT p F (PseudoUniformizer.frobRoot p F ϖ n) (2 * p - 1) 1).image
            (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1).canonicalMap)
          ((chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1).canonicalMap
            (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) p 1)) := by
  rw [bigWindow_inter_succ_eq_rationalOpen_ofNat p F ϖ n hp]
  have hcoe : ((spaChartHomeoBigWindow p F ϖ n hp w :
      ↥(bigWindow p F ϖ (n : ℤ) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F))
      = comap (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1).canonicalMap
        (w : Spv (presheafValue (chartData p F
          (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))) := rfl
  rw [hcoe]
  exact comap_canonicalMap_mem_rationalOpen_iff w.2 _ _


/-- **The overlap circle as the left edge of the `(n+1)`-st chart**: the same
circle, with the `κ' = 1` datum `R({p², [ϖ'']²}/(p·[ϖ'']))` at
`ϖ'' = ϖ^{1/p^{n+1}}`. -/
theorem bigWindow_inter_succ_eq_rationalOpen_left (n : ℕ) (hp : 1 < p) :
    bigWindow p F ϖ (n : ℤ) ∩ bigWindow p F ϖ ((n : ℤ) + 1)
      = rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1)
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ (n + 1) := pow_pos hppos (n + 1)
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ (n + 1) with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ (n + 1) = teichPi p F ϖ :=
    teichPi_frobRoot_pow p F ϖ (n + 1)
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    Y_eq_of_teichPi_pow p F ϖ hpk hteich
  rw [bigWindow_inter_succ p F ϖ (n : ℤ) hp]
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 1 1 1
    one_pos one_pos one_pos one_pos v
  rw [show 1 + 1 - 1 = 1 by omega] at hiff
  rw [hiff, hYeq]
  have hq : (0 : ℚ) < (p : ℚ) ^ ((n : ℤ) + 1) := zpow_pos hp0 _
  have hab : (p : ℚ) ^ ((n : ℤ) + 1) = ((p ^ (n + 1) : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
    push_cast
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    ring
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq one_pos hab).mp hge
    have hlev := (KLE_iff hY hq one_pos hab).mp hle
    rw [pow_one] at hgev hlev
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      simp only [pow_one]
      rw [hteich]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    simp only [pow_one] at hge hle
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq one_pos hab).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hteich] at h
      rw [pow_one]
      exact h
    · refine (KLE_iff hY hq one_pos hab).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hteich] at h
      rw [pow_one]
      exact h

/-- **The left-edge circle inside the `(n+1)`-st chart spectrum.** -/
theorem spaChartHomeoBigWindow_preimage_circle_left (n : ℕ) (hp : 1 < p)
    [DecidableEq (presheafValue (chartData p F
      (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1))]
    (w : ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1))))) :
    ((spaChartHomeoBigWindow p F ϖ (n + 1) hp w :
        ↥(bigWindow p F ϖ ((n + 1 : ℕ) : ℤ)
          ∩ Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F)) ∈ bigWindow p F ϖ (n : ℤ) ∩ bigWindow p F ϖ ((n : ℤ) + 1)
      ↔ (w : Spv (presheafValue (chartData p F
          (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1)))
        ∈ rationalOpen
          ((chartT p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1).image
            (chartData p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1).canonicalMap)
          ((chartData p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1).canonicalMap
            (chartS p F (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1)) := by
  rw [bigWindow_inter_succ_eq_rationalOpen_left p F ϖ n hp]
  have hcoe : ((spaChartHomeoBigWindow p F ϖ (n + 1) hp w :
      ↥(bigWindow p F ϖ ((n + 1 : ℕ) : ℤ)
        ∩ Spa (Ainf p F) (ringPlus (Ainf p F))))
      : Spv (Ainf p F))
      = comap (chartData p F
          (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1).canonicalMap
        (w : Spv (presheafValue (chartData p F
          (PseudoUniformizer.frobRoot p F ϖ (n + 1)) 1 1 p 1))) := rfl
  rw [hcoe]
  exact comap_canonicalMap_mem_rationalOpen_iff w.2 _ _

end FarguesFontaine

end
