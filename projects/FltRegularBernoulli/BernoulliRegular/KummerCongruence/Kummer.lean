module

public import BernoulliRegular.KummerCongruence.Voronoi

/-!
# Kummer's congruence (T011)

The classical Kummer congruence: for even positive integers
`m ≡ n (mod p − 1)` with `(p − 1) ∤ n`, `p ∤ m`, `p ∤ n`,
`p ∤ (m + 1)`, `p ∤ (n + 1)`,

  `B_m / m ≡ B_n / n (mod p)`

in `ℚ_[p]` (both `p`-integral). Proved from Voronoi's congruence plus
a permutation by a primitive root `a` of `(ℤ/pℤ)^*`.

See the umbrella `BernoulliRegular.KummerCongruence` for the full
strategy and how this feeds into T012 (the bridge theorem).
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

/-- Two `p`-adic integers with equal image under `toZMod` differ by a multiple
of `p`. -/
private theorem padicInt_sub_mem_span_p_of_toZMod_eq {p : ℕ} [Fact p.Prime]
    {x y : ℤ_[p]} (h : PadicInt.toZMod x = PadicInt.toZMod y) :
    x - y ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
  have h_sub : PadicInt.toZMod (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h_ker : x - y ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [← PadicInt.ker_toZMod]; exact h_sub
  rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker

/-- For a unit generator `g` of `(ZMod p)ˣ` whose value is the residue of `a`,
the element `(a : ℤ_[p]) ^ k - 1` is a unit whenever `p - 1 ∤ k`. -/
private theorem padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd {p k : ℕ}
    [Fact p.Prime] {a : ℕ} {g : (ZMod p)ˣ} (hg_order : orderOf g = p - 1)
    (ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p)) (hk : ¬ (p - 1) ∣ k) :
    IsUnit ((a : ℤ_[p]) ^ k - 1) := by
  rw [PadicInt.isUnit_iff]
  by_contra h_norm
  have h_mem : ((a : ℤ_[p]) ^ k - 1 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
    PadicInt.mem_nonunits.mpr (lt_of_le_of_ne (PadicInt.norm_le_one _) h_norm)
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at h_mem
  rw [map_sub, map_one, map_pow, map_natCast, ha_cast, sub_eq_zero] at h_mem
  have h_gk : g ^ k = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h_mem)
  exact hk (hg_order ▸ orderOf_dvd_of_pow_eq_one h_gk)

/-- For `j < p` with `j ≠ 0`, the powers `(j : ZMod p) ^ e` and `(j : ZMod p) ^ f`
agree whenever `e ≡ f (mod p - 1)`: `j` is a unit, so its order divides `p - 1`. -/
private theorem pow_pred_natCast_eq_of_modEq {p e f : ℕ} [Fact p.Prime]
    (hef : e ≡ f [MOD p - 1]) {j : ℕ} (hjp : j < p) (hj_ne : j ≠ 0) :
    ((j : ℕ) : ZMod p) ^ e = ((j : ℕ) : ZMod p) ^ f := by
  have hp : Nat.Prime p := ‹Fact p.Prime›.out
  have hj_coprime : Nat.Coprime j p :=
    (hp.coprime_iff_not_dvd.mpr
      (fun hdvd ↦ hj_ne (Nat.eq_zero_of_dvd_of_lt hdvd hjp))).symm
  lift (((j : ℕ) : ZMod p)) to (ZMod p)ˣ using
    (ZMod.isUnit_iff_coprime j p).mpr hj_coprime with u hu
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
  congr 1
  rw [pow_eq_pow_iff_modEq]
  have h_ord_dvd : orderOf u ∣ (p - 1) := by
    rw [← ZMod.card_units, ← Nat.card_eq_fintype_card]; exact orderOf_dvd_natCard u
  exact hef.of_dvd h_ord_dvd

/-- The Voronoi floor sums for two exponents agree in `ZMod p` when the
predecessor exponents are congruent mod `p - 1` (termwise via
`pow_pred_natCast_eq_of_modEq`, the `j = 0` term vanishing). -/
private theorem sum_floorTerm_pow_pred_natCast_eq_of_modEq {p a e f : ℕ}
    [Fact p.Prime] (he : e ≠ 0) (hf : f ≠ 0) (hef : e ≡ f [MOD p - 1]) :
    ((∑ j ∈ Finset.range p, j ^ e * (j * a / p) : ℕ) : ZMod p) =
      ((∑ j ∈ Finset.range p, j ^ f * (j * a / p) : ℕ) : ZMod p) := by
  push_cast
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  congr 1
  by_cases hj_ne : j = 0
  · rw [hj_ne]; simp [zero_pow he, zero_pow hf]
  · exact pow_pred_natCast_eq_of_modEq hef hj hj_ne

/-- Final algebraic cancellation for the divided-Bernoulli Kummer congruence over
`ℚ_[p]`. From the two single-exponent Voronoi expansions, the combined
floor-sum identity packaged in `E`, the divided-Bernoulli relations
`mQ * Bm_div = Bm` (and `n`), and the four unit inverses, the difference
`Bm_div - Bn_div` is `p` times the explicit witness. -/
private theorem bernoulli_div_sub_eq_p_mul_of_expansions {p : ℕ} [Fact p.Prime]
    {Am Bm Am1 Sm zm AmInv mQ mInv Bm_div
     An Bn An1 Sn zn AnInv nQ nInv Bn_div E : ℚ_[p]}
    (h_mBm : mQ * Bm_div = Bm) (h_nBn : nQ * Bn_div = Bn)
    (hzm : (Am - 1) * Bm - mQ * Am1 * Sm = (p : ℚ_[p]) * zm)
    (hzn : (An - 1) * Bn - nQ * An1 * Sn = (p : ℚ_[p]) * zn)
    (hE : (An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn = (p : ℚ_[p]) * E)
    (hAmInv : (Am - 1) * AmInv = 1) (hAnInv : (An - 1) * AnInv = 1)
    (hmInv : mQ * mInv = 1) (hnInv : nQ * nInv = 1) :
    Bm_div - Bn_div =
      (p : ℚ_[p]) * (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn) := by
  have h_Am_ne : Am - 1 ≠ 0 := fun h0 ↦ one_ne_zero <| by rw [← hAmInv, h0, zero_mul]
  have h_An_ne : An - 1 ≠ 0 := fun h0 ↦ one_ne_zero <| by rw [← hAnInv, h0, zero_mul]
  have h_mQ_ne : mQ ≠ 0 := fun h0 ↦ one_ne_zero <| by rw [← hmInv, h0, zero_mul]
  have h_nQ_ne : nQ ≠ 0 := fun h0 ↦ one_ne_zero <| by rw [← hnInv, h0, zero_mul]
  have h_Bm_expand : (Am - 1) * Bm = mQ * Am1 * Sm + (p : ℚ_[p]) * zm := by
    linear_combination hzm
  have h_Bn_expand : (An - 1) * Bn = nQ * An1 * Sn + (p : ℚ_[p]) * zn := by
    linear_combination hzn
  have h_key : (Am - 1) * (An - 1) * mQ * nQ * (Bm_div - Bn_div) =
      (Am - 1) * (An - 1) * mQ * nQ * ((p : ℚ_[p]) *
        (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn)) := by
    have h_lhs :
        (Am - 1) * (An - 1) * mQ * nQ * (Bm_div - Bn_div) =
        (An - 1) * nQ * ((Am - 1) * (mQ * Bm_div)) -
          (Am - 1) * mQ * ((An - 1) * (nQ * Bn_div)) := by ring
    rw [h_lhs, h_mBm, h_nBn, h_Bm_expand, h_Bn_expand]
    rw [show (An - 1) * nQ * (mQ * Am1 * Sm + (p : ℚ_[p]) * zm) -
        (Am - 1) * mQ * (nQ * An1 * Sn + (p : ℚ_[p]) * zn) =
        mQ * nQ * ((An - 1) * Am1 * Sm - (Am - 1) * An1 * Sn) +
        (p : ℚ_[p]) * ((An - 1) * nQ * zm - (Am - 1) * mQ * zn) from by ring, hE]
    rw [show (Am - 1) * (An - 1) * mQ * nQ * ((p : ℚ_[p]) *
        (AmInv * AnInv * E + AmInv * mInv * zm - AnInv * nInv * zn)) =
        (p : ℚ_[p]) * (((Am - 1) * AmInv) * ((An - 1) * AnInv) * mQ * nQ * E) +
        (p : ℚ_[p]) * ((An - 1) * ((Am - 1) * AmInv) * (mQ * mInv) * nQ * zm) -
        (p : ℚ_[p]) * ((Am - 1) * ((An - 1) * AnInv) * (nQ * nInv) * mQ * zn) from by ring,
      hAmInv, hAnInv, hmInv, hnInv]
    ring
  have h_cancel_ne : (Am - 1) * (An - 1) * mQ * nQ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h_Am_ne h_An_ne) h_mQ_ne) h_nQ_ne
  exact mul_left_cancel₀ h_cancel_ne h_key

/-- **T011** (Kummer's congruence, Washington Cor 5.14 /
Diekmann Cor 33). For even positive integers `m ≡ n (mod p-1)` with
`(p-1) ∤ n`, `p ∤ m`, `p ∤ n`, `p ∤ (m+1)`, `p ∤ (n+1)`,
  `B_m/m ≡ B_n/n (mod p)`,
with both sides `p`-integral.

**Proof outline** (via Voronoi, `voronoi_congruence_mod_p`):
apply Voronoi to `m` and `n` with a primitive root `a` of `(ℤ/pℤ)^*`.
The RHSs agree mod `p` (since `a^m ≡ a^n`, `a^{m-1} ≡ a^{n-1}`,
`S_m ≡ S_n` mod `p`, using `m ≡ n (mod p-1)` and Fermat). Dividing by
`m · n` (a `p`-unit when `p ∤ m · n`) yields the congruence.

The extra divisibility hypotheses `¬ p ∣ m`, `¬ p ∣ n`, `¬ p ∣ (m+1)`,
`¬ p ∣ (n+1)` arise from Voronoi's input (`¬ p ∣ (k+1)`) and from the
need to divide by `m` and `n` as `p`-units. They are all satisfied by
the T012 caller (where `m = p·n+1`) and the HMinus callers (where
`m = t`, `n = j+1` with `j+1 < p - 1`). -/
theorem bernoulli_div_sModEq_of_modEq
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {m n : ℕ} (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm_even : Even m) (hn_even : Even n)
    (h_pSubOne_not_dvd_n : ¬ (p - 1) ∣ n)
    (h_mn_modEq : m ≡ n [MOD (p - 1)])
    (hm_coprime_p : ¬ (p : ℕ) ∣ m) (hn_coprime_p : ¬ (p : ℕ) ∣ n)
    (hm_p_plus : ¬ (p : ℕ) ∣ (m + 1)) (hn_p_plus : ¬ (p : ℕ) ∣ (n + 1))
    (h_below_m : ∀ j, j ≤ m → ¬ (p : ℕ) ^ 3 ∣ (j + 1))
    (h_below_n : ∀ j, j ≤ n → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      (((bernoulli m : ℚ) / m : ℚ) : ℚ_[p]) -
          (((bernoulli n : ℚ) / n : ℚ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm_two : 2 ≤ m := by
    obtain ⟨r, hr⟩ := hm_even; omega
  have hn_two : 2 ≤ n := by
    obtain ⟨r, hr⟩ := hn_even; omega
  -- `¬ (p - 1) ∣ m` from `(p - 1) ∤ n` and `m ≡ n (mod p-1)`.
  have h_pSubOne_not_dvd_m : ¬ (p - 1) ∣ m := by
    intro hdvd
    have h_n_mod : n ≡ 0 [MOD (p - 1)] := h_mn_modEq.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)
    exact h_pSubOne_not_dvd_n (Nat.modEq_zero_iff_dvd.mp h_n_mod)
  -- Pick a generator `g : (ZMod p)ˣ` of the unit group of `ZMod p`.
  obtain ⟨g, hg_gen⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  -- Define `a : ℕ := (g : ZMod p).val`.
  set a : ℕ := (g : ZMod p).val with ha_def
  -- `a < p` (from `ZMod.val_lt`).
  have ha_lt : a < p := ZMod.val_lt _
  -- `a.Coprime p` (from `ZMod.val_coe_unit_coprime`).
  have ha_coprimeZ : Nat.Coprime a p := ZMod.val_coe_unit_coprime g
  -- `¬ p ∣ a` from coprimality.
  have ha_coprime : ¬ (p : ℕ) ∣ a := by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact (hp.coprime_iff_not_dvd.mp ha_coprimeZ)
  -- `((a : ℕ) : ZMod p) = (g : ZMod p)` since `a < p`.
  have ha_cast : ((a : ℕ) : ZMod p) = (g : ZMod p) := by
    rw [ha_def]; exact ZMod.natCast_zmod_val _
  -- `orderOf (g : (ZMod p)ˣ) = p - 1` from generator + cyclic structure.
  have hg_order : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen, Nat.card_eq_fintype_card, ZMod.card_units]
  -- Apply Voronoi to m and n.
  have hk_coprime_m : ¬ (p - 1) ∣ m := h_pSubOne_not_dvd_m
  have hk_coprime_n : ¬ (p - 1) ∣ n := h_pSubOne_not_dvd_n
  obtain ⟨z_m, hz_m⟩ := voronoi_congruence_mod_p hp_odd ha_coprime hm_two hm_even
    hk_coprime_m hm_p_plus h_below_m
  obtain ⟨z_n, hz_n⟩ := voronoi_congruence_mod_p hp_odd ha_coprime hn_two hn_even
    hk_coprime_n hn_p_plus h_below_n
  -- Abbreviations.
  set Am : ℤ_[p] := (a : ℤ_[p]) ^ m with hAm_def
  set An : ℤ_[p] := (a : ℤ_[p]) ^ n with hAn_def
  set Am1 : ℤ_[p] := (a : ℤ_[p]) ^ (m - 1) with hAm1_def
  set An1 : ℤ_[p] := (a : ℤ_[p]) ^ (n - 1) with hAn1_def
  set Sm : ℕ := ∑ j ∈ Finset.range p, j ^ (m - 1) * (j * a / p) with hSm_def
  set Sn : ℕ := ∑ j ∈ Finset.range p, j ^ (n - 1) * (j * a / p) with hSn_def
  -- **Mod-p congruences.**
  -- (C1) `Am ≡ An (mod p)` in `ℤ_[p]` and (C2) `Am1 ≡ An1 (mod p)`.
  -- Key: `(g : (ZMod p)ˣ)` has order `p-1`, `m ≡ n (mod p-1)` ⟹ `g^m = g^n`
  -- ⟹ `(a : ZMod p)^m = (a : ZMod p)^n` ⟹ `((a:ℤ_[p])^m - (a:ℤ_[p])^n) ∈ maximalIdeal`.
  have h_gmn_eq : g ^ m = g ^ n := by
    rw [pow_eq_pow_iff_modEq, hg_order]; exact h_mn_modEq
  have h_mn1_modEq : (m - 1) ≡ (n - 1) [MOD (p - 1)] := by
    have h1 : (m - 1) + 1 = m := Nat.succ_pred_eq_of_pos hm_pos
    have h2 : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn_pos
    have h_mod_add1 : (m - 1) + 1 ≡ (n - 1) + 1 [MOD (p - 1)] := by
      rw [h1, h2]; exact h_mn_modEq
    exact Nat.ModEq.add_right_cancel' 1 h_mod_add1
  have h_gmn1_eq : g ^ (m - 1) = g ^ (n - 1) := by
    rw [pow_eq_pow_iff_modEq, hg_order]; exact h_mn1_modEq
  -- Lift to `(ZMod p)` and then to `ℤ_[p]`.
  have h_mn_ZMod : ((a : ℕ) : ZMod p) ^ m = ((a : ℕ) : ZMod p) ^ n := by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ ↦ (u : ZMod p)) h_gmn_eq
  have h_mn1_ZMod : ((a : ℕ) : ZMod p) ^ (m - 1) = ((a : ℕ) : ZMod p) ^ (n - 1) := by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ ↦ (u : ZMod p)) h_gmn1_eq
  -- Lift (C1), (C2) to `ℤ_[p]` via `toZMod` and
  -- `padicInt_sub_mem_span_p_of_toZMod_eq`.
  have hpℤ_ne : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_toZMod_a : PadicInt.toZMod (a : ℤ_[p]) = ((a : ℕ) : ZMod p) := by rw [map_natCast]
  -- (C1): `Am - An = p * d_A` for some `d_A : ℤ_[p]`.
  have h_Am_An_toZMod : PadicInt.toZMod Am = PadicInt.toZMod An := by
    rw [hAm_def, hAn_def, map_pow, map_pow, h_toZMod_a]; exact h_mn_ZMod
  obtain ⟨d_A, hd_A⟩ :=
    Ideal.mem_span_singleton.mp (padicInt_sub_mem_span_p_of_toZMod_eq h_Am_An_toZMod)
  -- (C2): `Am1 - An1 = p * d_A1`.
  have h_Am1_An1_toZMod : PadicInt.toZMod Am1 = PadicInt.toZMod An1 := by
    rw [hAm1_def, hAn1_def, map_pow, map_pow, h_toZMod_a]; exact h_mn1_ZMod
  obtain ⟨d_A1, hd_A1⟩ :=
    Ideal.mem_span_singleton.mp (padicInt_sub_mem_span_p_of_toZMod_eq h_Am1_An1_toZMod)
  -- (C3): `Sm ≡ Sn (mod p)` in ℤ_[p] — termwise, via
  -- `sum_floorTerm_pow_pred_natCast_eq_of_modEq`.
  have h_Sm_Sn_toZMod : ((Sm : ℕ) : ZMod p) = ((Sn : ℕ) : ZMod p) := by
    rw [hSm_def, hSn_def]
    exact sum_floorTerm_pow_pred_natCast_eq_of_modEq
      (by omega) (by omega) h_mn1_modEq
  -- Lift to ℤ_[p]: `(Sm : ℤ_[p]) - (Sn : ℤ_[p]) ∈ p · ℤ_[p]`.
  have h_Sm_Sn_toZMod' : PadicInt.toZMod ((Sm : ℤ_[p])) = PadicInt.toZMod ((Sn : ℤ_[p])) := by
    rw [map_natCast, map_natCast]; exact h_Sm_Sn_toZMod
  obtain ⟨d_S, hd_S⟩ :=
    Ideal.mem_span_singleton.mp (padicInt_sub_mem_span_p_of_toZMod_eq h_Sm_Sn_toZMod')
  -- **Unit-ness of `Am - 1`, `An - 1`** (since `(p-1) ∤ m`, `(p-1) ∤ n`), via
  -- `padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd`.
  have h_Am_sub_one_unit : IsUnit (Am - 1) := by
    rw [hAm_def]
    exact padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast h_pSubOne_not_dvd_m
  have h_An_sub_one_unit : IsUnit (An - 1) := by
    rw [hAn_def]
    exact padicInt_pow_sub_one_isUnit_of_not_sub_one_dvd hg_order ha_cast h_pSubOne_not_dvd_n
  -- **Unit-ness of `m, n` in `ℤ_[p]`** (from hypotheses).
  have h_m_unit : IsUnit ((m : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hm_coprime_p
  have h_n_unit : IsUnit ((n : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hn_coprime_p
  -- Inverses in ℤ_[p]: unit * inv = 1.
  have hunit_inv : ∀ {x : ℤ_[p]} (hx : IsUnit x), x * (hx.unit⁻¹ : (ℤ_[p])ˣ).val = 1 := by
    intro x hx
    change ((hx.unit * hx.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  -- Inverses in ℤ_[p].
  set mInv : ℤ_[p] := (h_m_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hmInv_mul : ((m : ℕ) : ℤ_[p]) * mInv = 1 := hunit_inv h_m_unit
  set nInv : ℤ_[p] := (h_n_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hnInv_mul : ((n : ℕ) : ℤ_[p]) * nInv = 1 := hunit_inv h_n_unit
  set AmInv : ℤ_[p] := (h_Am_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hAmInv_mul : (Am - 1) * AmInv = 1 := hunit_inv h_Am_sub_one_unit
  set AnInv : ℤ_[p] := (h_An_sub_one_unit.unit⁻¹ : (ℤ_[p])ˣ).val
  have hAnInv_mul : (An - 1) * AnInv = 1 := hunit_inv h_An_sub_one_unit
  -- Abbreviate the ℤ_[p]-coercions of `Sm, Sn`.
  set SmZ : ℤ_[p] := ((Sm : ℕ) : ℤ_[p]) with hSmZ_def
  set SnZ : ℤ_[p] := ((Sn : ℕ) : ℤ_[p]) with hSnZ_def
  -- **Key equation in ℤ_[p]:**
  --  `(An - 1) · Am1 · SmZ - (Am - 1) · An1 · SnZ = p · E`
  -- where `E = (Am - 1) · (d_A1 · SmZ + An1 · d_S) - d_A · Am1 · SmZ`.
  set E : ℤ_[p] := (Am - 1) * (d_A1 * SmZ + An1 * d_S) - d_A * Am1 * SmZ with hE_def
  have hE_eq : (An - 1) * Am1 * SmZ - (Am - 1) * An1 * SnZ = (p : ℤ_[p]) * E := by
    -- Use `Am - An = p · d_A`, `Am1 - An1 = p · d_A1`, `SmZ - SnZ = p · d_S`.
    have h_An_eq : An = Am - (p : ℤ_[p]) * d_A := by linear_combination -hd_A
    have h_An1_eq : An1 = Am1 - (p : ℤ_[p]) * d_A1 := by linear_combination -hd_A1
    have h_SnZ_eq : SnZ = SmZ - (p : ℤ_[p]) * d_S := by linear_combination -hd_S
    rw [hE_def, h_An_eq, h_An1_eq, h_SnZ_eq]
    ring
  -- **Candidate witness.**
  refine ⟨AmInv * AnInv * E + AmInv * mInv * z_m - AnInv * nInv * z_n, ?_⟩
  -- Lift everything to ℚ_[p]: Define Q-versions.
  -- Since `Am, An, Am1, An1 : ℤ_[p]`, their Q-cast via `↑` is
  -- e.g. `((Am : ℤ_[p]) : ℚ_[p])` etc.
  -- Use `set` for ℚ_[p] shorthands.
  set Am_Q : ℚ_[p] := (Am : ℚ_[p]) with hAm_Q_def
  set An_Q : ℚ_[p] := (An : ℚ_[p]) with hAn_Q_def
  set Am1_Q : ℚ_[p] := (Am1 : ℚ_[p]) with hAm1_Q_def
  set An1_Q : ℚ_[p] := (An1 : ℚ_[p]) with hAn1_Q_def
  set Sm_Q : ℚ_[p] := (SmZ : ℚ_[p]) with hSm_Q_def
  set Sn_Q : ℚ_[p] := (SnZ : ℚ_[p]) with hSn_Q_def
  set mQ : ℚ_[p] := ((m : ℕ) : ℚ_[p]) with hmQ_def
  set nQ : ℚ_[p] := ((n : ℕ) : ℚ_[p]) with hnQ_def
  set Bm_Q : ℚ_[p] := ((bernoulli m : ℚ) : ℚ_[p]) with hBm_Q_def
  set Bn_Q : ℚ_[p] := ((bernoulli n : ℚ) : ℚ_[p]) with hBn_Q_def
  have hmQ_ne : mQ ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
  have hnQ_ne : nQ ≠ 0 := Nat.cast_ne_zero.mpr hn_pos.ne'
  -- `Bm_div := B_m / m` in ℚ_[p].
  set Bm_div : ℚ_[p] := (((bernoulli m : ℚ) / m : ℚ) : ℚ_[p]) with hBm_div_def
  set Bn_div : ℚ_[p] := (((bernoulli n : ℚ) / n : ℚ) : ℚ_[p]) with hBn_div_def
  -- `mQ · Bm_div = Bm_Q`.
  have h_mBm : mQ * Bm_div = Bm_Q := by
    rw [hBm_div_def, hmQ_def, hBm_Q_def]; push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm_pos.ne' : ((m : ℕ) : ℚ_[p]) ≠ 0)]
  have h_nBn : nQ * Bn_div = Bn_Q := by
    rw [hBn_div_def, hnQ_def, hBn_Q_def]; push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn_pos.ne' : ((n : ℕ) : ℚ_[p]) ≠ 0)]
  -- Cast Voronoi's hypotheses to Q-forms (same shape, sums coerce through).
  have h_Sm_cast : ((∑ j ∈ Finset.range p, j ^ (m - 1) * (j * a / p) : ℕ) : ℚ_[p]) = Sm_Q := by
    rw [hSm_Q_def, hSmZ_def, hSm_def, PadicInt.coe_natCast]
  have h_Sn_cast : ((∑ j ∈ Finset.range p, j ^ (n - 1) * (j * a / p) : ℕ) : ℚ_[p]) = Sn_Q := by
    rw [hSn_Q_def, hSnZ_def, hSn_def, PadicInt.coe_natCast]
  have hz_m_Q : (Am_Q - 1) * Bm_Q - mQ * Am1_Q * Sm_Q = (p : ℚ_[p]) * (z_m : ℚ_[p]) := by
    have := hz_m
    rw [hAm_Q_def, hAm1_Q_def, hAm_def, hAm1_def, hBm_Q_def, hmQ_def]
    rw [h_Sm_cast] at this; push_cast; convert this using 2
  have hz_n_Q : (An_Q - 1) * Bn_Q - nQ * An1_Q * Sn_Q = (p : ℚ_[p]) * (z_n : ℚ_[p]) := by
    have := hz_n
    rw [hAn_Q_def, hAn1_Q_def, hAn_def, hAn1_def, hBn_Q_def, hnQ_def]
    rw [h_Sn_cast] at this; push_cast; convert this using 2
  -- Cast `hE_eq` to ℚ_[p].
  have hE_eq_Q : (An_Q - 1) * Am1_Q * Sm_Q - (Am_Q - 1) * An1_Q * Sn_Q =
      (p : ℚ_[p]) * ((E : ℤ_[p]) : ℚ_[p]) := by
    have := congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hE_eq
    rw [hAm_Q_def, hAn_Q_def, hAm1_Q_def, hAn1_Q_def, hSm_Q_def, hSn_Q_def]
    push_cast at this ⊢
    linear_combination this
  -- Unit relations in ℚ_[p].
  have h_mQ_mInv : mQ * ((mInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [hmQ_def]; simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hmInv_mul
  have h_nQ_nInv : nQ * ((nInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    rw [hnQ_def]; simpa using congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hnInv_mul
  have h_Am_AmInv : (Am_Q - 1) * ((AmInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hAmInv_mul
    rw [hAm_Q_def]; push_cast at this; exact this
  have h_An_AnInv : (An_Q - 1) * ((AnInv : ℤ_[p]) : ℚ_[p]) = 1 := by
    have := congrArg (fun x : ℤ_[p] ↦ (x : ℚ_[p])) hAnInv_mul
    rw [hAn_Q_def]; push_cast at this; exact this
  -- Reshape the witness from a single `ℤ_[p]`-coercion into the split `ℚ_[p]`
  -- form expected by `bernoulli_div_sub_eq_p_mul_of_expansions`.
  set AmInv_Q : ℚ_[p] := ((AmInv : ℤ_[p]) : ℚ_[p]) with hAmInv_Q_def
  set AnInv_Q : ℚ_[p] := ((AnInv : ℤ_[p]) : ℚ_[p]) with hAnInv_Q_def
  set mInv_Q : ℚ_[p] := ((mInv : ℤ_[p]) : ℚ_[p]) with hmInv_Q_def
  set nInv_Q : ℚ_[p] := ((nInv : ℤ_[p]) : ℚ_[p]) with hnInv_Q_def
  set z_m_Q : ℚ_[p] := ((z_m : ℤ_[p]) : ℚ_[p]) with hz_m_Q_def
  set z_n_Q : ℚ_[p] := ((z_n : ℤ_[p]) : ℚ_[p]) with hz_n_Q_def
  set E_Q : ℚ_[p] := ((E : ℤ_[p]) : ℚ_[p]) with hE_Q_def
  have h_witness_eq : ((((AmInv * AnInv * E + AmInv * mInv * z_m -
      AnInv * nInv * z_n : ℤ_[p]) : ℚ_[p]))) =
      AmInv_Q * AnInv_Q * E_Q + AmInv_Q * mInv_Q * z_m_Q - AnInv_Q * nInv_Q * z_n_Q := by
    rw [hAmInv_Q_def, hAnInv_Q_def, hmInv_Q_def, hnInv_Q_def, hz_m_Q_def, hz_n_Q_def, hE_Q_def]
    push_cast; ring
  rw [h_witness_eq]
  -- Conclude by the packaged ℚ_[p] cancellation.
  exact bernoulli_div_sub_eq_p_mul_of_expansions h_mBm h_nBn hz_m_Q hz_n_Q hE_eq_Q
    h_Am_AmInv h_An_AnInv h_mQ_mInv h_nQ_nInv



end BernoulliRegular
