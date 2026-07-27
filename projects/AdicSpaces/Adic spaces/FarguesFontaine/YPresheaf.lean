/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartSpa
import «Adic spaces».FarguesFontaine.FrobeniusGauss

/-!
# The interval-trace basis of `Y` (D-ii-1)

The loci `κ(v) ∈ [1/q₁, 1/q₂]` for rational radius-exponent pairs — the
index geometry of the `BIQ`-valued structure presheaf of the curve:

* `FarguesFontaine.intervalTrace` : the trace, in `KGE`/`KLE` form;
* `FarguesFontaine.bigWindow_eq_intervalTrace` : the Big windows are the
  `(1/p^n, 1/p^{n+1})`-traces;
* `FarguesFontaine.intervalTrace_mono` : traces are monotone in the interval.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **The trace of a radius-exponent interval on `Y`**: the locus
`κ(v) ∈ [1/q₁, 1/q₂]` for a decreasing exponent pair `q₂ < q₁` (radius
exponents; the `BIQ q₁ q₂`-indexing convention). -/
def intervalTrace (q₁ q₂ : ℚ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ (1 / q₁) v ∧ KLE p F ϖ (1 / q₂) v}

/-- The Big windows are interval traces. -/
theorem bigWindow_eq_intervalTrace (n : ℤ) :
    bigWindow p F ϖ n
      = intervalTrace p F ϖ (1 / (p : ℚ) ^ n) (1 / (p : ℚ) ^ (n + 1)) := by
  ext v
  show (v ∈ Y p F ϖ ∧ KGE p F ϖ ((p : ℚ) ^ n) v ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v)
    ↔ (v ∈ Y p F ϖ ∧ KGE p F ϖ (1 / (1 / (p : ℚ) ^ n)) v
        ∧ KLE p F ϖ (1 / (1 / (p : ℚ) ^ (n + 1))) v)
  rw [one_div_one_div, one_div_one_div]

/-- Interval traces are monotone: a smaller exponent interval has a smaller
trace. -/
theorem intervalTrace_mono {q₁ q₂ r₁ r₂ : ℚ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : r₁ ≤ q₁) (h₂ : q₂ ≤ r₂) :
    intervalTrace p F ϖ r₁ r₂ ⊆ intervalTrace p F ϖ q₁ q₂ := by
  rintro v ⟨hY, hge, hle⟩
  refine ⟨hY, ?_, ?_⟩
  · refine KGE_mono p F ϖ hY ?_ ?_ hge
    · positivity
    · exact one_div_le_one_div_of_le hr₁ h₁
  · refine KLE_mono p F ϖ hY ?_ ?_ hle
    · positivity
    · exact one_div_le_one_div_of_le hq₂ h₂

/-- **Dyadic interval traces are rational subsets**: the trace at exponents
`(j₁/p^s, j₂/p^s)` is the `κ' ∈ [1/j₁, 1/j₂]` chart of the `p^s`-th root
uniformizer. -/
theorem intervalTrace_dyadic_eq_rationalOpen (s j₁ j₂ : ℕ)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) :
    intervalTrace p F ϖ ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))
      = rationalOpen
          (chartT p F (PseudoUniformizer.frobRoot p F ϖ s) 1 (j₁ + j₂ - 1))
          (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hppos
  have hpk : 0 < p ^ s := pow_pos hppos s
  set ϖ' := PseudoUniformizer.frobRoot p F ϖ s with hϖ'def
  have hteich : teichPi p F ϖ' ^ p ^ s = teichPi p F ϖ :=
    teichPi_frobRoot_pow p F ϖ s
  have hYeq : Y p F ϖ' = Y p F ϖ :=
    Y_eq_of_teichPi_pow p F ϖ hpk hteich
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 j₁ 1 j₂
    one_pos hj₁ one_pos hj₂ v
  rw [show 1 + 1 - 1 = 1 from by omega] at hiff
  rw [hiff, hYeq]
  have hq1 : (0 : ℚ) < 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₁ : ℚ) := by exact_mod_cast hj₁
    positivity
  have hq2 : (0 : ℚ) < 1 / ((j₂ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₂ : ℚ) := by exact_mod_cast hj₂
    positivity
  have hab1 : 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s))
      = ((p ^ s : ℕ) : ℚ) / ((j₁ : ℕ) : ℚ) := by
    push_cast
    rw [one_div_div]
  have hab2 : 1 / ((j₂ : ℚ) / ((p : ℚ) ^ s))
      = ((p ^ s : ℕ) : ℚ) / ((j₂ : ℕ) : ℚ) := by
    push_cast
    rw [one_div_div]
  have hcolL : (teichPi p F ϖ' ^ j₁) ^ p ^ s = teichPi p F ϖ ^ j₁ := by
    rw [← pow_mul, mul_comm j₁ (p ^ s), pow_mul, hteich]
  have hcolR : (teichPi p F ϖ' ^ j₂) ^ p ^ s = teichPi p F ϖ ^ j₂ := by
    rw [← pow_mul, mul_comm j₂ (p ^ s), pow_mul, hteich]
  have hcolP : (((p : Ainf p F)) ^ 1) ^ p ^ s = ((p : Ainf p F)) ^ p ^ s := by
    rw [← pow_mul, one_mul]
  constructor
  · rintro ⟨hY, hge, hle⟩
    have hgev := (KGE_iff hY hq1 hj₁ hab1).mp hge
    have hlev := (KLE_iff hY hq2 hj₂ hab2).mp hle
    refine ⟨hY, ?_, ?_⟩
    · refine (vle_pow_iff hpk _ _).mp ?_
      rw [hcolL, hcolP]
      exact hgev
    · refine (vle_pow_iff hpk _ _).mp ?_
      rw [hcolR, hcolP]
      exact hlev
  · rintro ⟨hY, hge, hle⟩
    refine ⟨hY, ?_, ?_⟩
    · refine (KGE_iff hY hq1 hj₁ hab1).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hge
      rw [hcolL, hcolP] at h
      exact h
    · refine (KLE_iff hY hq2 hj₂ hab2).mpr ?_
      have h := (vle_pow_iff (v := v) hpk _ _).mpr hle
      rw [hcolR, hcolP] at h
      exact h


/-- **Dyadic interval traces are open in `Spa (A_inf, A_inf)`.** -/
theorem isOpen_intervalTrace_dyadic (s j₁ j₂ : ℕ)
    (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) :
    IsOpen {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ intervalTrace p F ϖ
        ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))} := by
  rw [show {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ intervalTrace p F ϖ
        ((j₁ : ℚ) / ((p : ℚ) ^ s)) ((j₂ : ℚ) / ((p : ℚ) ^ s))}
    = {x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F))) |
      (x : Spv (Ainf p F)) ∈ rationalOpen
        (chartT p F (PseudoUniformizer.frobRoot p F ϖ s) 1 (j₁ + j₂ - 1))
        (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂)} from by
    rw [← intervalTrace_dyadic_eq_rationalOpen p F ϖ s j₁ j₂ hj₁ hj₂]]
  exact isOpen_rationalOpen_trace (chartT_nonempty p F _ 1 (j₁ + j₂ - 1)) _

/-- **A dyadic interval index**: exponents `(j₁/p^s, j₂/p^s)`, decreasing. -/
structure DyadicIdx where
  /-- The denominator exponent. -/
  s : ℕ
  /-- The larger numerator (the smaller radius' exponent). -/
  j₁ : ℕ
  /-- The smaller numerator. -/
  j₂ : ℕ
  /-- Positivity of the smaller numerator. -/
  hj₂ : 0 < j₂
  /-- The exponents decrease. -/
  hlt : j₂ < j₁

namespace DyadicIdx

/-- The larger rational exponent. -/
def q₁ (i : DyadicIdx) : ℚ := (i.j₁ : ℚ) / ((p : ℚ) ^ i.s)

/-- The smaller rational exponent. -/
def q₂ (i : DyadicIdx) : ℚ := (i.j₂ : ℚ) / ((p : ℚ) ^ i.s)

theorem hj₁ (i : DyadicIdx) : 0 < i.j₁ := lt_trans i.hj₂ i.hlt

theorem q₁_pos [Fact (Nat.Prime p)] (i : DyadicIdx) : 0 < i.q₁ p := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hj : (0 : ℚ) < (i.j₁ : ℚ) := by exact_mod_cast i.hj₁
  rw [q₁]
  positivity

theorem q₂_pos [Fact (Nat.Prime p)] (i : DyadicIdx) : 0 < i.q₂ p := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hj : (0 : ℚ) < (i.j₂ : ℚ) := by exact_mod_cast i.hj₂
  rw [q₂]
  positivity

theorem q₂_lt_q₁ [Fact (Nat.Prime p)] (i : DyadicIdx) : i.q₂ p < i.q₁ p := by
  have hp : (0 : ℚ) < (p : ℚ) ^ i.s := by
    have : (0 : ℚ) < p := by
      exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
    positivity
  rw [q₁, q₂]
  gcongr
  exact_mod_cast i.hlt

/-- The nesting relation: `i'`'s interval is contained in `i`'s. -/
def Nested (i' i : DyadicIdx) : Prop :=
  i.q₂ p ≤ i'.q₂ p ∧ i'.q₁ p ≤ i.q₁ p

theorem Nested.mem₁ [Fact (Nat.Prime p)] {i' i : DyadicIdx}
    (h : Nested p i' i) : i.q₂ p ≤ i'.q₁ p ∧ i'.q₁ p ≤ i.q₁ p :=
  ⟨le_trans (le_trans h.1 (i'.q₂_lt_q₁ p).le) le_rfl, h.2⟩

theorem Nested.mem₂ [Fact (Nat.Prime p)] {i' i : DyadicIdx}
    (h : Nested p i' i) : i.q₂ p ≤ i'.q₂ p ∧ i'.q₂ p ≤ i.q₁ p :=
  ⟨h.1, le_trans (i'.q₂_lt_q₁ p).le h.2⟩

end DyadicIdx


variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- The interval ring at a dyadic index. -/
noncomputable def dyadicVal (i : DyadicIdx) : Type _ :=
  ↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p))

noncomputable instance (i : DyadicIdx) : CommRing (dyadicVal p F ϖ i) := by
  rw [dyadicVal]
  infer_instance

/-- The restriction between nested dyadic indices. -/
noncomputable def dyadicRes {i' i : DyadicIdx} (h : DyadicIdx.Nested p i' i) :
    dyadicVal p F ϖ i →+* dyadicVal p F ϖ i' :=
  biResQ' p F ϖ (i.q₁ p) (i.q₂ p) (i'.q₁ p) (i'.q₂ p)
    (i.q₁_pos p) (i.q₂_pos p) (i'.q₁_pos p) (i'.q₂_pos p)
    (i.q₂_lt_q₁ p) (h.mem₁ p) (h.mem₂ p)

/-- The trace of a dyadic index on `Y`. -/
def dyadicTrace (i : DyadicIdx) : Set (Spv (Ainf p F)) :=
  intervalTrace p F ϖ (i.q₁ p) (i.q₂ p)

/-- **The limit sections over the dyadic basis inside a set `W`**: compatible
families of interval-ring elements, one per dyadic trace contained in `W`. -/
noncomputable def limitSectionsY (W : Set (Spv (Ainf p F))) :
    Subring (Π i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W},
      dyadicVal p F ϖ i.1) where
  carrier := {f | ∀ (i' i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W})
    (h : DyadicIdx.Nested p i'.1 i.1), dyadicRes p F ϖ h (f i) = f i'}
  zero_mem' := by
    intro i' i h
    show dyadicRes p F ϖ h 0 = 0
    exact map_zero _
  one_mem' := by
    intro i' i h
    show dyadicRes p F ϖ h 1 = 1
    exact map_one _
  add_mem' := by
    intro f g hf hg i' i h
    show dyadicRes p F ϖ h (f i + g i) = f i' + g i'
    rw [map_add, hf i' i h, hg i' i h]
  mul_mem' := by
    intro f g hf hg i' i h
    show dyadicRes p F ϖ h (f i * g i) = f i' * g i'
    rw [map_mul, hf i' i h, hg i' i h]
  neg_mem' := by
    intro f hf i' i h
    show dyadicRes p F ϖ h (-(f i)) = -(f i')
    rw [map_neg, hf i' i h]


/-- **The presheaf restriction**: sections over `W` restrict to sections over
any `W' ⊆ W` by re-indexing. -/
noncomputable def limitRestrictY {W' W : Set (Spv (Ainf p F))} (hW : W' ⊆ W) :
    ↥(limitSectionsY p F ϖ W) →+* ↥(limitSectionsY p F ϖ W') where
  toFun f := ⟨fun i => f.1 ⟨i.1, Set.Subset.trans i.2 hW⟩,
    fun i' i h => f.2 ⟨i'.1, Set.Subset.trans i'.2 hW⟩
      ⟨i.1, Set.Subset.trans i.2 hW⟩ h⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction to the same set is the identity. -/
theorem limitRestrictY_id {W : Set (Spv (Ainf p F))} :
    limitRestrictY p F ϖ (le_refl W)
      = RingHom.id ↥(limitSectionsY p F ϖ W) :=
  rfl

/-- Restrictions compose. -/
theorem limitRestrictY_comp {W'' W' W : Set (Spv (Ainf p F))}
    (h₁ : W'' ⊆ W') (h₂ : W' ⊆ W) :
    (limitRestrictY p F ϖ h₁).comp (limitRestrictY p F ϖ h₂)
      = limitRestrictY p F ϖ (Set.Subset.trans h₁ h₂) :=
  rfl

end FarguesFontaine

end
