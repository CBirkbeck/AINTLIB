import PadicLFunctions.KubotaLeopoldt.MuA

/-!
# The Kubota–Leopoldt p-adic L-function (RJW §4.3 and Thm. 4.1)

The restriction of `μ_a` to `ℤ_p^×` (as a measure on `ℤ_p^×`, via precomposition with
`extendByZero`), the multiplication-by-`x⁻¹` rescaling (RJW eq. 4.11,
`eq:mult by xinverse`), and the p-adic zeta function

`ζ_p = (x⁻¹ Res_{ℤ_p^×} μ_a) / ([a] − [1]) ∈ Q(ℤ_p^×)`  (RJW Def. 4.10, `DefZetap`)

for `a` an *integer* topological generator of `ℤ_p^×` (the source takes its `a`
simultaneously integral — §4.1 — and a topological generator — Def. 4.10; an integer
primitive root mod `p²` generates `(ℤ/p^n)^×` for every `n`, which is
`exists_nat_topological_generator`).

Main result (RJW Thm. 4.1, `thm:kubota leopoldt theorem`): `ζ_p` is the unique
pseudo-measure on `ℤ_p^×` with `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1}) ζ(1−k)` for all
`k > 0` — stated via the witnessing measures of `([b]−[1])·ζ_p`, the same moment
encoding as `pseudoMeasure_eq_zero_of_moments`.
-/

noncomputable section

open PowerSeries

namespace PadicMeasure

variable (p : ℕ) [hp : Fact p.Prime]

/-- The restriction of `μ_a` to `ℤ_p^×`, as a measure on `ℤ_p^×`: precomposition
with extension-by-zero. Satisfies `ι (muAUnits a) = Res_{ℤ_p^×}(μ_a)`
(`iota_muAUnits`). Source: RJW §4.2/§4.3 transition. -/
def muAUnits (a : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  (muA p a).comp (extendByZero p)

lemma iota_muAUnits (a : ℕ) :
    iota p (muAUnits p a) = res p (isClopen_units p) (muA p a) := by
  refine LinearMap.ext fun f => ?_
  change muA p a (extendByZero p (f.comp (unitsValCM p)))
      = muA p a ((LocallyConstant.charFn ℤ_[p] (isClopen_units p) : C(ℤ_[p], ℤ_[p])) * f)
  rw [extendByZero_comp_unitsVal]

lemma muAUnits_apply_unitsPowCM (a k : ℕ) :
    muAUnits p a (unitsPowCM p k)
      = res p (isClopen_units p) (muA p a) (powCM p k) := by
  change muA p a (extendByZero p (unitsPowCM p k))
      = muA p a ((LocallyConstant.charFn ℤ_[p] (isClopen_units p) : C(ℤ_[p], ℤ_[p]))
          * powCM p k)
  rw [show unitsPowCM p k = (powCM p k).comp (unitsValCM p) from
      ContinuousMap.ext fun u => rfl,
    extendByZero_comp_unitsVal]

lemma continuous_units_inv_val :
    Continuous fun u : ℤ_[p]ˣ => ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) :=
  MulOpposite.continuous_unop.comp (continuous_snd.comp Units.continuous_embedProduct)

/-- The continuous function `x ↦ x⁻¹` on `ℤ_p^×` (valued in `ℤ_p`). -/
def invCM : C(ℤ_[p]ˣ, ℤ_[p]) :=
  ⟨_, continuous_units_inv_val p⟩

/-- Multiplication of a measure on `ℤ_p^×` by a continuous function (the analogue of
`cmul` on `ℤ_p`). RJW eq. 4.11: `∫ f · (g·μ) := ∫ g·f · μ`. -/
def unitsCmul (g : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) :
    PadicMeasure p ℤ_[p]ˣ :=
  μ.comp (LinearMap.mulLeft ℤ_[p] g)

@[simp]
lemma unitsCmul_apply (g f : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) :
    unitsCmul p g μ f = μ (g * f) := rfl

/-- The numerator `x⁻¹ · Res_{ℤ_p^×}(μ_a)` of the p-adic zeta function
(RJW Def. 4.10). -/
def zetaNum (a : ℕ) : PadicMeasure p ℤ_[p]ˣ :=
  unitsCmul p (invCM p) (muAUnits p a)

lemma zetaNum_apply_unitsPowCM (a : ℕ) {k : ℕ} (hk : 0 < k) :
    zetaNum p a (unitsPowCM p k) = muAUnits p a (unitsPowCM p (k - 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.succ_sub_one]
  change muAUnits p a (invCM p * unitsPowCM p (k' + 1)) = muAUnits p a (unitsPowCM p k')
  congr 1
  ext u
  change ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) ^ (k' + 1) = (u : ℤ_[p]) ^ k'
  calc ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p]) ^ (k' + 1)
      = (u : ℤ_[p]) ^ k' * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * (u : ℤ_[p])) := by ring
    _ = (u : ℤ_[p]) ^ k' := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

/-- RJW TeX line 1561:
`∫_{ℤ_p^×} x^k · x⁻¹μ_a = (−1)^k (a^k−1)(1−p^{k−1}) ζ(1−k)`. -/
theorem zetaNum_moments {a : ℕ} (hpa : ¬ p ∣ a) {k : ℕ} (hk : 0 < k) :
    ((zetaNum p a (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
      = (-1) ^ k * ((a : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [zetaNum_apply_unitsPowCM p a hk, Nat.succ_sub_one, muAUnits_apply_unitsPowCM,
    res_units_muA_apply_powCM p hpa k', pow_succ (-1 : ℚ_[p]) k', pow_succ (a : ℚ_[p]) k']
  ring

/-- A topological generator of `ℤ_p^×` is torsion-free: `a^k ≠ 1` for `k > 0`
(the order of its image in `(ℤ/p^n)^×` grows without bound). -/
theorem topGen_pow_ne_one {a : ℤ_[p]ˣ}
    (ha : ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) :
    ∀ k, 0 < k → (a : ℤ_[p]) ^ k ≠ 1 := by
  intro k hk hak
  have hu : a ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hak, Units.val_one])
  have horder : orderOf (unitsToZModPow p (k + 1) a) = Nat.card (ZMod (p ^ (k + 1)))ˣ :=
    orderOf_eq_card_of_forall_mem_zpowers fun x => (ha (k + 1)) ▸ Subgroup.mem_top x
  have hdvd : orderOf (unitsToZModPow p (k + 1) a) ∣ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hu, map_one])
  have hcard := Nat.le_of_dvd hk (horder ▸ hdvd)
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp.out (Nat.succ_pos k), Nat.succ_sub_one] at hcard
  have h2 : k < 2 ^ k := k.lt_two_pow_self
  have h3 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
  have h4 : p ^ k ≤ p ^ k * (p - 1) :=
    Nat.le_mul_of_pos_right _ (by have := hp.out.two_le; omega)
  omega

/-- For odd `p` there is an *integer* topological generator of `ℤ_p^×`: an integer
that is a primitive root mod `p²` generates `(ℤ/p^n)^×` for every `n`. RJW takes
such an `a` implicitly (its `a` is an integer in §4.1 and a topological generator in
Def. 4.10). -/
theorem exists_nat_topological_generator (hp2 : p ≠ 2) :
    ∃ (m : ℕ) (u : ℤ_[p]ˣ), ¬ p ∣ m ∧ (u : ℤ_[p]) = (m : ℤ_[p]) ∧
      ∀ n : ℕ, Subgroup.zpowers (unitsToZModPow p n u) = ⊤ := by
  classical
  obtain ⟨u₀, hu₀⟩ := exists_topological_generator p hp2
  set m : ℕ := ((unitsToZModPow p 2 u₀ : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)).val with hm
  have hm2 : ((m : ℕ) : ZMod (p ^ 2))
      = ((unitsToZModPow p 2 u₀ : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) :=
    ZMod.natCast_rightInverse _
  have hpm : ¬ p ∣ m := by
    rintro ⟨t, ht⟩
    have hunit : IsUnit ((m : ℕ) : ZMod (p ^ 2)) := by
      rw [hm2]; exact (unitsToZModPow p 2 u₀).isUnit
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have h1 : ((p * t : ℕ) : ZMod (p ^ 2)) * v = 1 := by rw [← ht]; exact hv
    have h2 := congrArg (· * ((p : ℕ) : ZMod (p ^ 2))) h1
    simp only [one_mul] at h2
    have h3 : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * (((t : ℕ) : ZMod (p ^ 2)) * v)
        = ((p : ℕ) : ZMod (p ^ 2)) := by
      rw [← h2]; push_cast; ring
    rw [ZMod.natCast_self, zero_mul] at h3
    have h4 : (p ^ 2 : ℕ) ∣ p := by
      rwa [eq_comm, ZMod.natCast_eq_zero_iff] at h3
    have h5 := Nat.le_of_dvd hp.out.pos h4
    nlinarith [hp.out.two_le]
  have hum := PadicInt.isUnit_natCast_of_not_dvd (p := p) hpm
  refine ⟨m, hum.unit, hpm, hum.unit_spec, ?_⟩
  have hval : ∀ n : ℕ, ((unitsToZModPow p n hum.unit : (ZMod (p ^ n))ˣ) : ZMod (p ^ n))
      = ((m : ℕ) : ZMod (p ^ n)) := fun n => by
    rw [unitsToZModPow_coe, hum.unit_spec, map_natCast]
  have hgen2 : Subgroup.zpowers (unitsToZModPow p 2 hum.unit) = ⊤ := by
    have hq2 : unitsToZModPow p 2 hum.unit = unitsToZModPow p 2 u₀ :=
      Units.ext (by rw [hval 2, hm2])
    rw [hq2]; exact hu₀ 2
  have hdown : ∀ {n₁ n₂ : ℕ}, n₁ ≤ n₂ →
      Subgroup.zpowers (unitsToZModPow p n₂ hum.unit) = ⊤ →
      Subgroup.zpowers (unitsToZModPow p n₁ hum.unit) = ⊤ := by
    intro n₁ n₂ h hgen
    rw [show unitsToZModPow p n₁ hum.unit
        = ZMod.unitsMap (pow_dvd_pow p h) (unitsToZModPow p n₂ hum.unit) from
        unitsToZModPow_le p h _,
      ← MonoidHom.map_zpowers, hgen]
    exact Subgroup.map_top_of_surjective _
      (ZMod.unitsMap_surjective (pow_dvd_pow p h))
  have hgen1 : Subgroup.zpowers (unitsToZModPow p 1 hum.unit) = ⊤ :=
    hdown one_le_two hgen2
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 fun h => hpm (h ▸ dvd_zero p)
  have hmp1 : 1 ≤ m ^ (p - 1) := Nat.one_le_pow _ _ hm1
  have hfermat : (p : ℕ) ∣ m ^ (p - 1) - 1 := by
    have h1 : ((m : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpm
    have h2 := ZMod.pow_card_sub_one_eq_one h1
    have h3 : ((m ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [h2]
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact (Nat.modEq_iff_dvd' hmp1).1 h3.symm
  obtain ⟨c, hc⟩ := hfermat
  have hc' : m ^ (p - 1) = 1 + p * c := by omega
  have hpc : ¬ p ∣ c := by
    rintro ⟨d, rfl⟩
    have hsq : (p ^ 2 : ℕ) ∣ m ^ (p - 1) - 1 := ⟨d, by rw [hc]; ring⟩
    have hord2 : orderOf (unitsToZModPow p 2 hum.unit) = p * (p - 1) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers fun x => hgen2 ▸ Subgroup.mem_top x,
        Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow hp.out two_pos]
      ring_nf
    have hpow1 : (unitsToZModPow p 2 hum.unit) ^ (p - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hval 2, Units.val_one, ← Nat.cast_pow,
        show ((m ^ (p - 1) : ℕ) : ZMod (p ^ 2)) = ((1 : ℕ) : ZMod (p ^ 2)) from
          (ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.modEq_iff_dvd' hmp1).2 hsq).symm,
        Nat.cast_one]
    have hdvd := orderOf_dvd_of_pow_eq_one hpow1
    rw [hord2] at hdvd
    have h5 := Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd
    have h7 : 2 * (p - 1) ≤ p * (p - 1) := Nat.mul_le_mul_right _ hp.out.two_le
    have h8 := hp.out.two_le
    omega
  have hcz : ¬ ((p : ℤ)) ∣ ((c : ℕ) : ℤ) := by exact_mod_cast hpc
  intro n
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exact hdown (by omega) hgen2
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    set g := unitsToZModPow p (n' + 1) hum.unit with hg
    have hcard : Nat.card (ZMod (p ^ (n' + 1)))ˣ = p ^ n' * (p - 1) := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow hp.out (Nat.succ_pos n'), Nat.succ_sub_one]
    have ho1 : orderOf (unitsToZModPow p 1 hum.unit) = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers fun x => hgen1 ▸ Subgroup.mem_top x,
        Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, pow_one,
        Nat.totient_prime hp.out]
    have hd1 : (p - 1) ∣ orderOf g := by
      rw [← ho1,
        show unitsToZModPow p 1 hum.unit
          = ZMod.unitsMap (pow_dvd_pow p (by omega : 1 ≤ n' + 1)) g from
          unitsToZModPow_le p (by omega) _]
      exact orderOf_map_dvd _ _
    have hd2 : p ^ n' ∣ orderOf g := by
      have hval_pow : ((g ^ (p - 1) : (ZMod (p ^ (n' + 1)))ˣ) : ZMod (p ^ (n' + 1)))
          = (1 : ZMod (p ^ (n' + 1))) + (p : ZMod (p ^ (n' + 1))) * (c : ZMod (p ^ (n' + 1))) := by
        rw [Units.val_pow_eq_pow_val, hval (n' + 1), ← Nat.cast_pow, hc']
        push_cast
        ring
      have hord_val : orderOf ((g ^ (p - 1) : (ZMod (p ^ (n' + 1)))ˣ) : ZMod (p ^ (n' + 1)))
          = p ^ n' := by
        rw [hval_pow]
        have h := ZMod.orderOf_one_add_mul_prime hp.out hp2 ((c : ℕ) : ℤ) hcz n'
        push_cast at h
        exact h
      have : orderOf (g ^ (p - 1)) = p ^ n' := by
        rw [← orderOf_units, hord_val]
      exact this ▸ orderOf_pow_dvd (p - 1)
    have hcop : Nat.Coprime (p ^ n') (p - 1) := by
      have hbase : Nat.Coprime p (p - 1) := (Nat.Prime.coprime_iff_not_dvd hp.out).2
        fun h => by
          have h6 := Nat.le_of_dvd (by have := hp.out.two_le; omega) h
          have h7 := hp.out.two_le
          omega
      exact hbase.pow_left n'
    have hmul : p ^ n' * (p - 1) ∣ orderOf g := hcop.mul_dvd_of_dvd_of_dvd hd2 hd1
    have hog : orderOf g = Nat.card (ZMod (p ^ (n' + 1)))ˣ :=
      Nat.dvd_antisymm (orderOf_dvd_natCard g) (hcard ▸ hmul)
    exact Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hog])

/-- **RJW Def. 4.10 (`DefZetap`)**: the p-adic zeta function
`ζ_p = (x⁻¹ Res_{ℤ_p^×} μ_a) / ([a] − [1]) ∈ Q(ℤ_p^×)`, for (a choice of) an integer
topological generator `a` of `ℤ_p^×`. -/
def padicZeta (hp2 : p ≠ 2) : QuotientField p :=
  IsLocalization.mk' (QuotientField p)
    (zetaNum p (exists_nat_topological_generator p hp2).choose)
    ⟨dirac p (exists_nat_topological_generator p hp2).choose_spec.choose - 1,
      dirac_sub_one_mem_nonZeroDivisors p
        (topGen_pow_ne_one p
          (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2)⟩

lemma IsPseudoMeasure.sub {q₁ q₂ : QuotientField p}
    (h₁ : IsPseudoMeasure p q₁) (h₂ : IsPseudoMeasure p q₂) :
    IsPseudoMeasure p (q₁ - q₂) := by
  intro g
  obtain ⟨ν₁, hν₁⟩ := h₁ g
  obtain ⟨ν₂, hν₂⟩ := h₂ g
  exact ⟨ν₁ - ν₂, by rw [mul_sub, hν₁, hν₂, ← map_sub]⟩

/-- **RJW Prop. 4.11 (`PropInterpolation2`), first half**: `ζ_p` is a pseudo-measure. -/
theorem padicZeta_isPseudoMeasure (hp2 : p ≠ 2) :
    IsPseudoMeasure p (padicZeta p hp2) :=
  isPseudoMeasure_mk' p
    (exists_nat_topological_generator p hp2).choose_spec.choose_spec.2.2 _ _

/-- **RJW Prop. 4.11 (`PropInterpolation2`), interpolation**: every witness `ν` of
`([b]−[1])·ζ_p ∈ Λ(ℤ_p^×)` has moments
`∫ x^k ν = (b^k−1)(1−p^{k−1}) ζ(1−k)` — i.e.
`∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1})ζ(1−k)`
in the pseudo-measure moment encoding. -/
theorem padicZeta_moments (hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : 0 < k)
    (ν : PadicMeasure p ℤ_[p]ˣ)
    (hν : algebraMap _ (QuotientField p) (dirac p b - 1) * padicZeta p hp2
      = algebraMap _ _ ν) :
    ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
      = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
          * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  classical
  obtain ⟨hpm, huv, hgen⟩ := (exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set m := (exists_nat_topological_generator p hp2).choose with hm
  set u := (exists_nat_topological_generator p hp2).choose_spec.choose with hu
  have hspec : algebraMap _ (QuotientField p) (dirac p u - 1) * padicZeta p hp2
      = algebraMap _ _ (zetaNum p m) := by
    rw [padicZeta]
    exact IsLocalization.mk'_spec' (QuotientField p) _ _
  have hkey : (dirac p u - 1) * ν = (dirac p b - 1) * zetaNum p m := by
    apply IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
    rw [map_mul, map_mul, ← hν, ← hspec]
    ring
  have hmom := congrArg (fun μ : PadicMeasure p ℤ_[p]ˣ =>
    ((μ (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])) hkey
  simp only [units_mul_apply_unitsPowCM, LinearMap.sub_apply] at hmom
  have hdir : ∀ w : ℤ_[p]ˣ, dirac p w (unitsPowCM p k) = (w : ℤ_[p]) ^ k := fun w => rfl
  have hone : (1 : PadicMeasure p ℤ_[p]ˣ) (unitsPowCM p k) = 1 := by
    rw [units_one_def, hdir, Units.val_one, one_pow]
  rw [hdir, hdir, hone] at hmom
  push_cast at hmom
  have hne : ((u : ℤ_[p]) : ℚ_[p]) ^ k - 1 ≠ 0 := by
    refine sub_ne_zero.2 fun h => topGen_pow_ne_one p hgen k hk ?_
    exact Subtype.coe_injective (by push_cast; exact h)
  have hmu : ((m : ℕ) : ℚ_[p]) = ((u : ℤ_[p]) : ℚ_[p]) := by
    rw [huv]
    push_cast
    rfl
  rw [zetaNum_moments p hpm hk, hmu] at hmom
  have hsign := congrArg (fun q : ℚ => (q : ℚ_[p]))
    (neg_one_pow_mul_one_sub_pow_mul_zetaNeg (p : ℚ) hk)
  push_cast at hsign
  refine mul_left_cancel₀ hne ?_
  rw [hmom]
  linear_combination ((((b : ℤ_[p]) : ℚ_[p])) ^ k - 1)
    * ((((u : ℤ_[p]) : ℚ_[p])) ^ k - 1) * hsign

/-- **RJW Thm. 4.1 (`thm:kubota leopoldt theorem`)**: there is a unique pseudo-measure
`ζ_p` on `ℤ_p^×` with `∫_{ℤ_p^×} x^k ζ_p = (1−p^{k−1}) ζ(1−k)` for all `k > 0`
(moments encoded via the witnesses of `([b]−[1])·ζ_p`). -/
theorem kubotaLeopoldt (hp2 : p ≠ 2) :
    ∃! q : QuotientField p, IsPseudoMeasure p q ∧
      ∀ (b : ℤ_[p]ˣ) (k : ℕ), 0 < k → ∀ ν : PadicMeasure p ℤ_[p]ˣ,
        algebraMap _ (QuotientField p) (dirac p b - 1) * q = algebraMap _ _ ν →
          ((ν (unitsPowCM p k) : ℤ_[p]) : ℚ_[p])
            = ((b : ℚ_[p]) ^ k - 1) * (1 - (p : ℚ_[p]) ^ (k - 1))
                * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) := by
  classical
  obtain ⟨hpm, huv, hgen⟩ :=
    (exists_nat_topological_generator p hp2).choose_spec.choose_spec
  set u := (exists_nat_topological_generator p hp2).choose_spec.choose with hu
  refine ⟨padicZeta p hp2, ⟨padicZeta_isPseudoMeasure p hp2,
    fun b k hk ν hν => padicZeta_moments p hp2 b hk ν hν⟩, ?_⟩
  rintro q ⟨hq, hmom⟩
  have hd : IsPseudoMeasure p (q - padicZeta p hp2) :=
    IsPseudoMeasure.sub p hq (padicZeta_isPseudoMeasure p hp2)
  have hzero : q - padicZeta p hp2 = 0 := by
    refine pseudoMeasure_eq_zero_of_moments p (topGen_pow_ne_one p hgen) _ hd ?_
    intro k hk ν hν
    obtain ⟨ν₁, hν₁⟩ := hq u
    obtain ⟨ν₂, hν₂⟩ := padicZeta_isPseudoMeasure p hp2 u
    have hsplit : ν = ν₁ - ν₂ := by
      apply IsFractionRing.injective (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)
      rw [map_sub, ← hν₁, ← hν₂, ← hν]
      ring
    have h1 := hmom u k hk ν₁ hν₁
    have h2 := padicZeta_moments p hp2 u hk ν₂ hν₂
    rw [hsplit]
    refine Subtype.coe_injective ?_
    push_cast [LinearMap.sub_apply]
    rw [h1, h2]
    ring
  exact sub_eq_zero.1 hzero

end PadicMeasure
