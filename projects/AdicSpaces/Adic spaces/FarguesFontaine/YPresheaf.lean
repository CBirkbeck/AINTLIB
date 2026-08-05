/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartSpa
import «Adic spaces».FarguesFontaine.FrobeniusGauss
import «Adic spaces».FarguesFontaine.IntervalSplitting

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

omit [CharP F p] in
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
  have hteich : teichPi p F ϖ' ^ p ^ s = teichPi p F ϖ := teichPi_frobRoot_pow p F ϖ s
  have hYeq : Y p F ϖ' = Y p F ϖ := Y_eq_of_teichPi_pow p F ϖ hpk hteich
  ext v
  have hiff := mem_rationalOpen_chartData_iff p F ϖ' 1 j₁ 1 j₂ one_pos hj₁ one_pos hj₂ v
  rw [show 1 + 1 - 1 = 1 by omega] at hiff
  rw [hiff, hYeq]
  have hq1 : (0 : ℚ) < 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₁ : ℚ) := by exact_mod_cast hj₁
    positivity
  have hq2 : (0 : ℚ) < 1 / ((j₂ : ℚ) / ((p : ℚ) ^ s)) := by
    have : (0 : ℚ) < (j₂ : ℚ) := by exact_mod_cast hj₂
    positivity
  have hab1 : 1 / ((j₁ : ℚ) / ((p : ℚ) ^ s)) = ((p ^ s : ℕ) : ℚ) / ((j₁ : ℕ) : ℚ) := by
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
        (chartS p F (PseudoUniformizer.frobRoot p F ϖ s) 1 j₂)} by
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

omit [Fact (Nat.Prime p)] in
theorem q₁_pos [Fact (Nat.Prime p)] (i : DyadicIdx) : 0 < i.q₁ p := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hj : (0 : ℚ) < (i.j₁ : ℚ) := by exact_mod_cast i.hj₁
  rw [q₁]
  positivity

omit [Fact (Nat.Prime p)] in
theorem q₂_pos [Fact (Nat.Prime p)] (i : DyadicIdx) : 0 < i.q₂ p := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  have hj : (0 : ℚ) < (i.j₂ : ℚ) := by exact_mod_cast i.hj₂
  rw [q₂]
  positivity

omit [Fact (Nat.Prime p)] in
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

omit [Fact (Nat.Prime p)] in
theorem Nested.mem₁ [Fact (Nat.Prime p)] {i' i : DyadicIdx}
    (h : Nested p i' i) : i.q₂ p ≤ i'.q₁ p ∧ i'.q₁ p ≤ i.q₁ p :=
  ⟨le_trans (le_trans h.1 (i'.q₂_lt_q₁ p).le) le_rfl, h.2⟩

omit [Fact (Nat.Prime p)] in
theorem Nested.mem₂ [Fact (Nat.Prime p)] {i' i : DyadicIdx}
    (h : Nested p i' i) : i.q₂ p ≤ i'.q₂ p ∧ i'.q₂ p ≤ i.q₁ p :=
  ⟨h.1, le_trans (i'.q₂_lt_q₁ p).le h.2⟩

/-- The left piece of a middle split of a dyadic index. -/
def splitL (i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (hj' : j < i.j₁) :
    DyadicIdx :=
  ⟨i.s, i.j₁, j, lt_trans i.hj₂ hj, hj'⟩

/-- The right piece of a middle split of a dyadic index. -/
def splitR (i : DyadicIdx) (j : ℕ) (hj : i.j₂ < j) (_hj' : j < i.j₁) :
    DyadicIdx :=
  ⟨i.s, j, i.j₂, i.hj₂, hj⟩

omit [Fact (Nat.Prime p)] in
theorem splitL_nested [Fact (Nat.Prime p)] (i : DyadicIdx) (j : ℕ)
    (hj : i.j₂ < j) (hj' : j < i.j₁) :
    Nested p (splitL i j hj hj') i := by
  have hp : (0 : ℚ) < (p : ℚ) ^ i.s := by
    have : (0 : ℚ) < p := by
      exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
    positivity
  constructor
  · show (i.j₂ : ℚ) / ((p : ℚ) ^ i.s) ≤ (j : ℚ) / ((p : ℚ) ^ i.s)
    gcongr
  · exact le_rfl

omit [Fact (Nat.Prime p)] in
theorem splitR_nested [Fact (Nat.Prime p)] (i : DyadicIdx) (j : ℕ)
    (hj : i.j₂ < j) (hj' : j < i.j₁) :
    Nested p (splitR i j hj hj') i := by
  have hp : (0 : ℚ) < (p : ℚ) ^ i.s := by
    have : (0 : ℚ) < p := by
      exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
    positivity
  constructor
  · exact le_rfl
  · show (j : ℚ) / ((p : ℚ) ^ i.s) ≤ (i.j₁ : ℚ) / ((p : ℚ) ^ i.s)
    gcongr

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
  biResQ p F ϖ (i.q₁ p) (i.q₂ p) (i'.q₁ p) (i'.q₂ p)
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

/-- **Evaluation of limit sections at the top index** of a dyadic trace. -/
noncomputable def limitEvalTop (i₀ : DyadicIdx) :
    ↥(limitSectionsY p F ϖ (dyadicTrace p F ϖ i₀)) →+* dyadicVal p F ϖ i₀ where
  toFun f := f.1 ⟨i₀, Set.Subset.refl _⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Evaluation is compatible with the family: the value at any nested index
is the restriction of the top value. -/
theorem limitEvalTop_spec (i₀ : DyadicIdx)
    (f : ↥(limitSectionsY p F ϖ (dyadicTrace p F ϖ i₀)))
    (i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ dyadicTrace p F ϖ i₀})
    (h : DyadicIdx.Nested p i.1 i₀) :
    f.1 i = dyadicRes p F ϖ h (limitEvalTop p F ϖ i₀ f) :=
  (f.2 i ⟨i₀, Set.Subset.refl _⟩ h).symm

omit [CharP F p] in
/-- Nat powers of rational radii multiply the exponent. -/
theorem vpiQ_pow (q : ℚ) (a : ℕ) :
    vpiQ p F ϖ q ^ a = vpiQ p F ϖ (q * a) := by
  rw [vpiQ, vpiQ, ← NNReal.rpow_natCast (_ ^ (q : ℝ)) a, ← NNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- The rational radii compare antitonically, as an iff. -/
theorem vpiQ_le_vpiQ_iff {x y : ℚ} :
    vpiQ p F ϖ x ≤ vpiQ p F ϖ y ↔ y ≤ x := by
  have hb0 : (0 : ℝ) < (perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) : ℝ) := by
    have h : (0 : NNReal) < perfectoidValuation p F
        ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
      refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
      exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
    exact_mod_cast h
  have hb1 : (perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) : ℝ) < 1 := by
    exact_mod_cast perfectoidValuation_toOF_lt_one p F ϖ
  rw [vpiQ, vpiQ, ← NNReal.coe_le_coe, NNReal.coe_rpow, NNReal.coe_rpow,
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hb1]
  exact_mod_cast Iff.rfl


/-- The Gauss valuation of `p`-powers. -/
theorem gaussVal_p_pow {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (a : ℕ) :
    gaussVal p F hρ0 hρ1 ((p : Ainf p F) ^ a) = ρ ^ a := by
  rw [Valuation.map_pow, gaussVal_apply]
  congr 1
  have h := gaussValue_p_mul p F hρ1.le (1 : Ainf p F)
  rw [mul_one, gaussValue_one p F hρ1.le, mul_one] at h
  exact h

/-- The Gauss valuation of Teichmüller powers. -/
theorem gaussVal_teichPi_pow {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ) :
    gaussVal p F hρ0 hρ1 (teichPi p F ϖ ^ b)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b := by
  rw [Valuation.map_pow, gaussVal_apply, teichPi,
    gaussValue_teichmuller p F hρ1.le]

/-- **The Gauss point at radius `vpiQ q` compares `[ϖ]^{r.num}` against `p^{r.den}`
exactly as `q` compares against `r`.** -/
private theorem gaussVal_vle_teichPi_pow_p_pow_iff {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    (ofValuation (gaussVal p F (vpiQ_pos p F ϖ q)
        (vpiQ_lt_one p F ϖ hq))).vle
        (teichPi p F ϖ ^ r.num.toNat) ((p : Ainf p F) ^ r.den)
      ↔ q ≤ r := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hden : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.den_pos
  have hcast : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by
    exact_mod_cast congrArg Int.cast (Int.toNat_of_nonneg hnum.le)
  show gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)
      (teichPi p F ϖ ^ r.num.toNat)
    ≤ gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)
        ((p : Ainf p F) ^ r.den) ↔ _
  rw [gaussVal_teichPi_pow, gaussVal_p_pow,
    show perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
        ^ r.num.toNat = vpiQ p F ϖ ((r.num.toNat : ℕ) : ℚ) from
      (vpiQ_natCast p F ϖ r.num.toNat).symm,
    vpiQ_pow p F ϖ q r.den, vpiQ_le_vpiQ_iff p F ϖ, hcast]
  rw [show (q * (r.den : ℚ) ≤ (r.num : ℚ)) ↔ q ≤ r by
    rw [← le_div_iff₀ hden, Rat.num_div_den]]

/-- **Gauss points detect the interval**: the Gauss point at radius `vpiQ q`
lies in the `(q₁, q₂)`-trace iff `q ∈ [q₂, q₁]`. -/
theorem gaussPoint_mem_intervalTrace_iff {q q₁ q₂ : ℚ}
    (hq : 0 < q) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    ofValuation (gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq))
        ∈ intervalTrace p F ϖ q₁ q₂
      ↔ q₂ ≤ q ∧ q ≤ q₁ := by
  have hY := gaussPoint_mem_Y p F ϖ (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)
  have hnum₁ : 0 < q₁.num := Rat.num_pos.mpr hq₁
  have hden₁ : (0 : ℚ) < (q₁.den : ℚ) := by exact_mod_cast q₁.den_pos
  have hnum₂ : 0 < q₂.num := Rat.num_pos.mpr hq₂
  have hden₂ : (0 : ℚ) < (q₂.den : ℚ) := by exact_mod_cast q₂.den_pos
  have hcast₁ : ((q₁.num.toNat : ℕ) : ℚ) = (q₁.num : ℚ) := by
    exact_mod_cast congrArg Int.cast (Int.toNat_of_nonneg hnum₁.le)
  have hcast₂ : ((q₂.num.toNat : ℕ) : ℚ) = (q₂.num : ℚ) := by
    exact_mod_cast congrArg Int.cast (Int.toNat_of_nonneg hnum₂.le)
  have hab₁ : 1 / q₁ = ((q₁.den : ℕ) : ℚ) / ((q₁.num.toNat : ℕ) : ℚ) := by
    rw [hcast₁]
    conv_lhs => rw [← Rat.num_div_den q₁]
    rw [one_div_div]
  have hab₂ : 1 / q₂ = ((q₂.den : ℕ) : ℚ) / ((q₂.num.toNat : ℕ) : ℚ) := by
    rw [hcast₂]
    conv_lhs => rw [← Rat.num_div_den q₂]
    rw [one_div_div]
  have hq₁inv : (0 : ℚ) < 1 / q₁ := by positivity
  have hq₂inv : (0 : ℚ) < 1 / q₂ := by positivity
  have htoNat₁ : 0 < q₁.num.toNat := by omega
  have htoNat₂ : 0 < q₂.num.toNat := by omega
  have hcompute₁ := gaussVal_vle_teichPi_pow_p_pow_iff p F ϖ hq hq₁
  have hcompute₂ : (ofValuation (gaussVal p F (vpiQ_pos p F ϖ q)
        (vpiQ_lt_one p F ϖ hq))).vle
        ((p : Ainf p F) ^ q₂.den) (teichPi p F ϖ ^ q₂.num.toNat)
      ↔ q₂ ≤ q := by
    show gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)
        ((p : Ainf p F) ^ q₂.den)
      ≤ gaussVal p F (vpiQ_pos p F ϖ q) (vpiQ_lt_one p F ϖ hq)
          (teichPi p F ϖ ^ q₂.num.toNat) ↔ _
    rw [gaussVal_teichPi_pow, gaussVal_p_pow,
      show perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ q₂.num.toNat = vpiQ p F ϖ ((q₂.num.toNat : ℕ) : ℚ) from
        (vpiQ_natCast p F ϖ q₂.num.toNat).symm,
      vpiQ_pow p F ϖ q q₂.den, vpiQ_le_vpiQ_iff p F ϖ, hcast₂]
    rw [show ((q₂.num : ℚ) ≤ q * (q₂.den : ℚ)) ↔ q₂ ≤ q by
      rw [← div_le_iff₀ hden₂, Rat.num_div_den]]
  constructor
  · rintro ⟨-, hge, hle⟩
    have h₁ := (KGE_iff hY hq₁inv htoNat₁ hab₁).mp hge
    have h₂ := (KLE_iff hY hq₂inv htoNat₂ hab₂).mp hle
    exact ⟨hcompute₂.mp h₂, hcompute₁.mp h₁⟩
  · rintro ⟨h₂, h₁⟩
    exact ⟨hY, (KGE_iff hY hq₁inv htoNat₁ hab₁).mpr (hcompute₁.mpr h₁),
      (KLE_iff hY hq₂inv htoNat₂ hab₂).mpr (hcompute₂.mpr h₂)⟩

/-- **Trace inclusion detects nesting**: if the dyadic trace of `i'` is contained
in that of `i`, then `i'`'s interval is contained in `i`'s. The proof evaluates the
inclusion at the two endpoint Gauss points of `i'`. -/
theorem dyadicTrace_subset_nested {i' i : DyadicIdx}
    (h : dyadicTrace p F ϖ i' ⊆ dyadicTrace p F ϖ i) :
    DyadicIdx.Nested p i' i := by
  have h₁ : ofValuation (gaussVal p F (vpiQ_pos p F ϖ (i'.q₁ p))
      (vpiQ_lt_one p F ϖ (i'.q₁_pos p))) ∈ dyadicTrace p F ϖ i' :=
    (gaussPoint_mem_intervalTrace_iff p F ϖ (i'.q₁_pos p) (i'.q₁_pos p)
      (i'.q₂_pos p)).mpr ⟨(i'.q₂_lt_q₁ p).le, le_rfl⟩
  have h₂ : ofValuation (gaussVal p F (vpiQ_pos p F ϖ (i'.q₂ p))
      (vpiQ_lt_one p F ϖ (i'.q₂_pos p))) ∈ dyadicTrace p F ϖ i' :=
    (gaussPoint_mem_intervalTrace_iff p F ϖ (i'.q₂_pos p) (i'.q₁_pos p)
      (i'.q₂_pos p)).mpr ⟨le_rfl, (i'.q₂_lt_q₁ p).le⟩
  have m₁ := (gaussPoint_mem_intervalTrace_iff p F ϖ (i'.q₁_pos p) (i.q₁_pos p)
    (i.q₂_pos p)).mp (h h₁)
  have m₂ := (gaussPoint_mem_intervalTrace_iff p F ϖ (i'.q₂_pos p) (i.q₁_pos p)
    (i.q₂_pos p)).mp (h h₂)
  exact ⟨m₂.1, m₁.2⟩

omit [Fact (Nat.Prime p)] in
/-- Nesting is transitive. -/
theorem DyadicIdx.Nested.trans {i'' i' i : DyadicIdx}
    (h₁ : DyadicIdx.Nested p i'' i') (h₂ : DyadicIdx.Nested p i' i) :
    DyadicIdx.Nested p i'' i :=
  ⟨le_trans h₂.1 h₁.1, le_trans h₁.2 h₂.2⟩

/-- **Identity law for dyadic restriction**: restriction along a self-nesting is
the identity. -/
theorem dyadicRes_id (i : DyadicIdx) (h : DyadicIdx.Nested p i i) :
    dyadicRes p F ϖ h = RingHom.id (dyadicVal p F ϖ i) :=
  biResQ_id p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p) (i.q₂_lt_q₁ p)

/-- **Composition law for dyadic restriction.** -/
theorem dyadicRes_comp {i'' i' i : DyadicIdx}
    (h₁ : DyadicIdx.Nested p i'' i') (h₂ : DyadicIdx.Nested p i' i) :
    (dyadicRes p F ϖ h₁).comp (dyadicRes p F ϖ h₂)
      = dyadicRes p F ϖ (h₁.trans p h₂) :=
  biResQ_comp p F ϖ (i.q₁ p) (i.q₂ p) (i'.q₁ p) (i'.q₂ p) (i''.q₁ p) (i''.q₂ p)
    (i.q₁_pos p) (i.q₂_pos p) (i'.q₁_pos p) (i'.q₂_pos p)
    (i''.q₁_pos p) (i''.q₂_pos p) (i.q₂_lt_q₁ p) (i'.q₂_lt_q₁ p)
    (h₂.mem₁ p) (h₂.mem₂ p) (h₁.mem₁ p) (h₁.mem₂ p)

/-- **The values-on-basis comparison is bijective**: evaluation at the top index
identifies the limit sections over a dyadic trace with the interval ring at its
index. Injectivity is `limitEvalTop_spec` through the geometric bridge
`dyadicTrace_subset_nested`; surjectivity restricts a top value along the
bridge. -/
theorem limitEvalTop_bijective (i₀ : DyadicIdx) :
    Function.Bijective (limitEvalTop p F ϖ i₀) := by
  constructor
  · intro f g hfg
    refine Subtype.ext (funext fun i => ?_)
    have hn : DyadicIdx.Nested p i.1 i₀ := dyadicTrace_subset_nested p F ϖ i.2
    rw [limitEvalTop_spec p F ϖ i₀ f i hn, limitEvalTop_spec p F ϖ i₀ g i hn,
      hfg]
  · intro x
    have hmem : (fun i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆
          dyadicTrace p F ϖ i₀} =>
          dyadicRes p F ϖ (dyadicTrace_subset_nested p F ϖ i.2) x)
        ∈ limitSectionsY p F ϖ (dyadicTrace p F ϖ i₀) := by
      intro i' i h
      show dyadicRes p F ϖ h
          (dyadicRes p F ϖ (dyadicTrace_subset_nested p F ϖ i.2) x)
        = dyadicRes p F ϖ (dyadicTrace_subset_nested p F ϖ i'.2) x
      rw [← RingHom.comp_apply,
        dyadicRes_comp p F ϖ h (dyadicTrace_subset_nested p F ϖ i.2)]
    refine ⟨⟨_, hmem⟩, ?_⟩
    show dyadicRes p F ϖ (dyadicTrace_subset_nested p F ϖ (Set.Subset.refl _)) x
      = x
    rw [dyadicRes_id p F ϖ i₀]
    rfl

/-- **Unique gluing over a split interval** (`∃!`-package of the split
fiber-product theorem). -/
theorem biResQ_split_existsUnique (q₁ q₂ r : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr : 0 < r) (hlt : q₂ < q₁) (hrm : q₂ ≤ r ∧ r ≤ q₁)
    (g₁ : ↥(BIQ p F ϖ q₁ r h₁ hr)) (g₂ : ↥(BIQ p F ϖ r q₂ hr h₂))
    (hmatch : biSndQ p F ϖ q₁ r h₁ hr g₁ = biFstQ p F ϖ r q₂ hr h₂ g₂) :
    ∃! f : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂),
      biResQ p F ϖ q₁ q₂ q₁ r h₁ h₂ h₁ hr hlt ⟨hlt.le, le_rfl⟩ hrm f = g₁
      ∧ biResQ p F ϖ q₁ q₂ r q₂ h₁ h₂ hr h₂ hlt hrm ⟨le_rfl, hlt.le⟩ f = g₂ := by
  obtain ⟨f, hfL, hfR⟩ := biResQ_split_surjective p F ϖ q₁ q₂ r h₁ h₂ hr
    hlt hrm g₁ g₂ hmatch
  refine ⟨f, ⟨hfL, hfR⟩, fun f' hf' => ?_⟩
  exact biResQ_split_injective p F ϖ q₁ q₂ r h₁ h₂ hr hlt hrm
    (hf'.1.trans hfL.symm) (hf'.2.trans hfR.symm)

/-- **Unique gluing over a split dyadic index**: a matching pair of sections
over the two pieces of a middle split is the pair of restrictions of a unique
section over the whole index. This is the two-piece sheaf axiom of the dyadic
interval presheaf. -/
theorem exists_unique_dyadicRes_glue (i : DyadicIdx) (j : ℕ)
    (hj : i.j₂ < j) (hj' : j < i.j₁)
    (gL : dyadicVal p F ϖ (DyadicIdx.splitL i j hj hj'))
    (gR : dyadicVal p F ϖ (DyadicIdx.splitR i j hj hj'))
    (hmatch : biSndQ p F ϖ ((DyadicIdx.splitL i j hj hj').q₁ p)
        ((DyadicIdx.splitL i j hj hj').q₂ p)
        ((DyadicIdx.splitL i j hj hj').q₁_pos p)
        ((DyadicIdx.splitL i j hj hj').q₂_pos p) gL
      = biFstQ p F ϖ ((DyadicIdx.splitR i j hj hj').q₁ p)
        ((DyadicIdx.splitR i j hj hj').q₂ p)
        ((DyadicIdx.splitR i j hj hj').q₁_pos p)
        ((DyadicIdx.splitR i j hj hj').q₂_pos p) gR) :
    ∃! f : dyadicVal p F ϖ i,
      dyadicRes p F ϖ (DyadicIdx.splitL_nested p i j hj hj') f = gL
      ∧ dyadicRes p F ϖ (DyadicIdx.splitR_nested p i j hj hj') f = gR := by
  have hrm : i.q₂ p ≤ (DyadicIdx.splitL i j hj hj').q₂ p
      ∧ (DyadicIdx.splitL i j hj hj').q₂ p ≤ i.q₁ p :=
    ⟨(DyadicIdx.splitL_nested p i j hj hj').1,
      (DyadicIdx.splitR_nested p i j hj hj').2⟩
  obtain ⟨f, hfL, hfR⟩ := biResQ_split_surjective p F ϖ (i.q₁ p) (i.q₂ p)
    ((DyadicIdx.splitL i j hj hj').q₂ p) (i.q₁_pos p) (i.q₂_pos p)
    ((DyadicIdx.splitL i j hj hj').q₂_pos p) (i.q₂_lt_q₁ p) hrm gL gR hmatch
  refine ⟨f, ⟨hfL, hfR⟩, fun f' hf' => ?_⟩
  exact biResQ_split_injective p F ϖ (i.q₁ p) (i.q₂ p)
    ((DyadicIdx.splitL i j hj hj').q₂ p) (i.q₁_pos p) (i.q₂_pos p)
    ((DyadicIdx.splitL i j hj hj').q₂_pos p) (i.q₂_lt_q₁ p) hrm
    (hf'.1.trans hfL.symm) (hf'.2.trans hfR.symm)

/-- **Unique gluing over an `N`-piece chain of rational intervals**: matching
sections over the consecutive pieces `[q t, q (t+1)]` of a strictly increasing
exponent chain are the restrictions of a unique section over the whole
interval `[q 0, q (m+1)]` — the finite-chain sheaf axiom of the interval
presheaf, by induction on the two-piece split theorem. -/
theorem biResQ_chain_glue (q : ℕ → ℚ) (hq : ∀ t, 0 < q t)
    (hlt : ∀ t, q t < q (t + 1))
    (g : ∀ t, ↥(BIQ p F ϖ (q (t + 1)) (q t) (hq (t + 1)) (hq t)))
    (hmatch : ∀ t, biSndQ p F ϖ (q (t + 2)) (q (t + 1)) (hq (t + 2))
        (hq (t + 1)) (g (t + 1))
      = biFstQ p F ϖ (q (t + 1)) (q t) (hq (t + 1)) (hq t) (g t)) :
    ∀ m : ℕ, ∃! f : ↥(BIQ p F ϖ (q (m + 1)) (q 0) (hq (m + 1)) (hq 0)),
      ∀ t, ∀ ht : t ≤ m,
        biResQ p F ϖ (q (m + 1)) (q 0) (q (t + 1)) (q t)
          (hq (m + 1)) (hq 0) (hq (t + 1)) (hq t)
          ((strictMono_nat_of_lt_succ hlt) (Nat.succ_pos m))
          ⟨(strictMono_nat_of_lt_succ hlt).monotone (Nat.zero_le (t + 1)),
            (strictMono_nat_of_lt_succ hlt).monotone (Nat.succ_le_succ ht)⟩
          ⟨(strictMono_nat_of_lt_succ hlt).monotone (Nat.zero_le t),
            (strictMono_nat_of_lt_succ hlt).monotone
              (ht.trans (Nat.le_succ m))⟩
          f = g t := by
  intro m
  induction m with
  | zero =>
    have hid := biResQ_id p F ϖ (q 1) (q 0) (hq 1) (hq 0) (hlt 0)
    refine ⟨g 0, fun t ht => ?_, fun f' hf' => ?_⟩
    · obtain rfl : t = 0 := Nat.le_zero.mp ht
      rw [hid]; rfl
    · have h0 := hf' 0 le_rfl
      rw [hid] at h0
      exact h0
  | succ m ih =>
    obtain ⟨fm, hfm, hfmu⟩ := ih
    have hsm := strictMono_nat_of_lt_succ hlt
    -- the two-step restriction `(m+2, 0) → (m+1, 0) → (t+1, t)` factors, for every `t ≤ m`
    have hcompres := fun (t : ℕ) (htm : t ≤ m) =>
      biResQ_comp p F ϖ (q (m + 2)) (q 0) (q (m + 1)) (q 0) (q (t + 1)) (q t)
        (hq (m + 2)) (hq 0) (hq (m + 1)) (hq 0) (hq (t + 1)) (hq t)
        (hsm (Nat.succ_pos (m + 1))) (hsm (Nat.succ_pos m))
        ⟨hsm.monotone (Nat.zero_le (m + 1)), hsm.monotone (Nat.le_succ (m + 1))⟩
        ⟨le_rfl, hsm.monotone (Nat.zero_le (m + 2))⟩
        ⟨hsm.monotone (Nat.zero_le (t + 1)), hsm.monotone (Nat.succ_le_succ htm)⟩
        ⟨hsm.monotone (Nat.zero_le t), hsm.monotone (htm.trans (Nat.le_succ m))⟩
    -- the top endpoint of the inductive glue is the top endpoint of `g m`
    have hend : biFstQ p F ϖ (q (m + 1)) (q 0) (hq (m + 1)) (hq 0) fm
        = biFstQ p F ϖ (q (m + 1)) (q m) (hq (m + 1)) (hq m) (g m) := by
      have h1 := RingHom.congr_fun (biFstQ_biResQ_left p F ϖ (q (m + 1)) (q 0) (q m)
        (hq (m + 1)) (hq 0) (hq m) (hsm (Nat.succ_pos m))
        ⟨hsm.monotone (Nat.zero_le m), hsm.monotone (Nat.le_succ m)⟩) fm
      rw [RingHom.comp_apply, hfm m le_rfl] at h1
      exact h1.symm
    have hm2 := (hmatch m).trans hend.symm
    obtain ⟨f, ⟨hfL, hfR⟩, hfu⟩ := biResQ_split_existsUnique p F ϖ
      (q (m + 2)) (q 0) (q (m + 1)) (hq (m + 2)) (hq 0) (hq (m + 1))
      (hsm (Nat.succ_pos (m + 1)))
      ⟨hsm.monotone (Nat.zero_le (m + 1)), hsm.monotone (Nat.le_succ (m + 1))⟩
      (g (m + 1)) fm hm2
    refine ⟨f, fun t ht => ?_, fun f' hf' => ?_⟩
    · by_cases ht' : t = m + 1
      · subst ht'
        exact hfL
      · have htm : t ≤ m := Nat.lt_succ_iff.mp (lt_of_le_of_ne ht ht')
        have h2 := RingHom.congr_fun (hcompres t htm) f
        rw [RingHom.comp_apply, hfR] at h2
        rw [← h2]; exact hfm t htm
    · refine hfu f' ⟨hf' (m + 1) le_rfl, ?_⟩
      -- NB: naming this restriction hom with `set` makes `isDefEq` blow the budget
      refine hfmu (biResQ p F ϖ (q (m + 2)) (q 0) (q (m + 1)) (q 0)
        (hq (m + 2)) (hq 0) (hq (m + 1)) (hq 0) (hsm (Nat.succ_pos (m + 1)))
        ⟨hsm.monotone (Nat.zero_le (m + 1)), hsm.monotone (Nat.le_succ (m + 1))⟩
        ⟨le_rfl, hsm.monotone (Nat.zero_le (m + 2))⟩ f') (fun t ht => ?_)
      have h2 := RingHom.congr_fun (hcompres t ht) f'
      rw [RingHom.comp_apply] at h2
      rw [h2]; exact hf' t (ht.trans (Nat.le_succ m))

/-- The uniformity on a dyadic value (the interval-ring subspace
uniformity). -/
noncomputable instance (i : DyadicIdx) :
    UniformSpace (dyadicVal p F ϖ i) :=
  inferInstanceAs (UniformSpace
    ↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p)))

/-- The dyadic values are topological rings. -/
instance (i : DyadicIdx) : IsTopologicalRing (dyadicVal p F ϖ i) :=
  inferInstanceAs (IsTopologicalRing
    ↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p)))

/-- The dyadic values are separated. -/
instance (i : DyadicIdx) : T2Space (dyadicVal p F ϖ i) :=
  inferInstanceAs (T2Space
    ↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p)))

/-- The dyadic values are complete (closed subrings of complete products). -/
instance (i : DyadicIdx) : CompleteSpace (dyadicVal p F ϖ i) :=
  (isClosed_BISub p F ϖ (hρ₁0 := vpiQ_pos p F ϖ (i.q₁ p))
    (hρ₁1 := vpiQ_lt_one p F ϖ (i.q₁_pos p))
    (hρ₂0 := vpiQ_pos p F ϖ (i.q₂ p))
    (hρ₂1 := vpiQ_lt_one p F ϖ (i.q₂_pos p))).completeSpace_coe

/-- The restriction between nested dyadic indices is continuous. -/
theorem dyadicRes_continuous {i' i : DyadicIdx}
    (h : DyadicIdx.Nested p i' i) :
    Continuous (dyadicRes p F ϖ h) :=
  biResQ_continuous p F ϖ (i.q₁ p) (i.q₂ p) (i'.q₁ p) (i'.q₂ p)
    (i.q₁_pos p) (i.q₂_pos p) (i'.q₁_pos p) (i'.q₂_pos p)
    (i.q₂_lt_q₁ p) (h.mem₁ p) (h.mem₂ p)

/-- **The compatibility locus is closed** in the product of the dyadic
values. -/
theorem isClosed_limitSectionsY (W : Set (Spv (Ainf p F))) :
    IsClosed (limitSectionsY p F ϖ W
      : Set (Π i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W},
        dyadicVal p F ϖ i.1)) := by
  have hset : (limitSectionsY p F ϖ W
      : Set (Π i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W},
        dyadicVal p F ϖ i.1))
      = ⋂ (i' : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W})
          (i : {i : DyadicIdx // dyadicTrace p F ϖ i ⊆ W})
          (h : DyadicIdx.Nested p i'.1 i.1),
          {f | dyadicRes p F ϖ h (f i) = f i'} := by
    ext f
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [hset]
  refine isClosed_iInter fun i' => isClosed_iInter fun i =>
    isClosed_iInter fun h => ?_
  exact isClosed_eq
    ((dyadicRes_continuous p F ϖ h).comp (continuous_apply i))
    (continuous_apply i')

/-- The limit sections over `W` are complete. -/
instance (W : Set (Spv (Ainf p F))) :
    CompleteSpace ↥(limitSectionsY p F ϖ W) :=
  (isClosed_limitSectionsY p F ϖ W).completeSpace_coe

/-- The limit sections over `W` are separated. -/
instance (W : Set (Spv (Ainf p F))) :
    T2Space ↥(limitSectionsY p F ϖ W) :=
  inferInstance

/-- The limit sections form a topological ring. -/
instance (W : Set (Spv (Ainf p F))) :
    IsTopologicalRing ↥(limitSectionsY p F ϖ W) :=
  inferInstance

/-- **The presheaf restriction is continuous** (a re-indexing of the
product projections). -/
theorem limitRestrictY_continuous {W' W : Set (Spv (Ainf p F))}
    (hW : W' ⊆ W) :
    Continuous (limitRestrictY p F ϖ hW) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  exact (continuous_apply _).comp continuous_subtype_val

/-- The interval subring is a uniform additive group. -/
instance (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    IsUniformAddGroup ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) :=
  IsUniformInducing.isUniformAddGroup (BIQ p F ϖ q₁ q₂ h₁ h₂).subtype
    isUniformEmbedding_subtype_val.isUniformInducing

/-- The dyadic values are uniform additive groups (subspace uniformity). -/
instance (i : DyadicIdx) : IsUniformAddGroup (dyadicVal p F ϖ i) :=
  inferInstanceAs (IsUniformAddGroup
    ↥(BIQ p F ϖ (i.q₁ p) (i.q₂ p) (i.q₁_pos p) (i.q₂_pos p)))

/-- The limit sections are a uniform additive group (subspace uniformity). -/
instance limitSectionsY.isUniformAddGroup (W : Set (Spv (Ainf p F))) :
    IsUniformAddGroup ↥(limitSectionsY p F ϖ W) :=
  IsUniformInducing.isUniformAddGroup (limitSectionsY p F ϖ W).subtype
    isUniformEmbedding_subtype_val.isUniformInducing

instance limitSectionsY.t0Space (W : Set (Spv (Ainf p F))) :
    T0Space ↥(limitSectionsY p F ϖ W) :=
  inferInstance

/-- **The Y-structure presheaf**, bundled: on an open `U ⊆ 𝒴`, the complete
topological ring of compatible dyadic families supported inside `U`. -/
def yPresheaf : TopCat.Presheaf CompleteTopCommRingCat
    (TopCat.of ↥(Y p F ϖ)) where
  obj V := CompleteTopCommRingCat.of
    ↥(limitSectionsY p F ϖ (Subtype.val '' (V.unop.1 : Set ↥(Y p F ϖ))))
  map {V W} i := ⟨limitRestrictY p F ϖ
      (Set.image_mono (CategoryTheory.leOfHom i.unop)),
    limitRestrictY_continuous p F ϖ _⟩
  map_id V := by
    refine Subtype.ext (RingHom.ext fun x => Subtype.ext (funext fun i => ?_))
    rfl
  map_comp {U V W} i j := by
    refine Subtype.ext (RingHom.ext fun x => Subtype.ext (funext fun i => ?_))
    rfl

@[simp] theorem yPresheaf_obj (V : (TopologicalSpace.Opens ↥(TopCat.of ↥(Y p F ϖ)))ᵒᵖ) :
    (yPresheaf p F ϖ).obj V = CompleteTopCommRingCat.of
      ↥(limitSectionsY p F ϖ
        (Subtype.val '' (V.unop.1 : Set ↥(Y p F ϖ)))) :=
  rfl

theorem yPresheaf_map {V W : (TopologicalSpace.Opens ↥(TopCat.of ↥(Y p F ϖ)))ᵒᵖ} (i : V ⟶ W)
    (x : ↥(limitSectionsY p F ϖ
      (Subtype.val '' (V.unop.1 : Set ↥(Y p F ϖ))))) :
    ((yPresheaf p F ϖ).map i).1 x
      = limitRestrictY p F ϖ (Set.image_mono (CategoryTheory.leOfHom i.unop)) x :=
  rfl

end FarguesFontaine

end
