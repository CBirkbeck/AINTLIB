import BernoulliRegular.FLT37.Eichler.CaseII.Section91.FactorUnitRatioRealRoot

/-!
# [F3] Coprimality as a datum field: the descent stays coprime, and the FLT37 endpoint drops the
false `h_cop` universal

The FLT37 endpoint `fermatLastTheoremFor_thirtyseven_of_lemma96_coprimality`
(`CaseIIWashingtonAssumptionIIRealProof.lean`) carries

```
h_cop : ∀ {m} (D : FreeContentCaseIIDvdZData37 (37*(m+1))),
  IsCoprime (span {(toReal D).x}) (span {(toReal D).y})
```

— a **false universal** (b2 `F3-HCOP-FALSE-UNIVERSAL`): scaling a datum's `x, y, z` by a rational
prime `p ∉ {37, 149}` preserves every datum field but breaks the coprimality, so the hypothesis is
undischargeable as stated.  This file **fixes** the endpoint by threading coprimality as a **datum
field** (the same pattern as the proven `ℓ ∣ z` threading) and **proving** that the descent stays in
the coprime-restricted domain:

1. **Seed** (`caseII_int_solution_pairwise_coprime` + `exists_coprime_*`): the rational Fermat
   triple has *pairwise* coprime entries (`gcd {a,b,c} = 1` + the equation: a common prime of two
   entries divides the third, hence the gcd), and the Bézout identity casts along
   `ℤ → 𝓞 K`, so the producer's datum (`x, y` integer casts) has
   `IsCoprime ((x)) ((y))` — surviving each WLOG permutation (negation preserves coprimality).

2. **Descent-step preservation** (`caseII_descended_blocks_span_isCoprime` — Washington p. 172,
   "`ω₁, θ₁, ξ₁, λ` are pairwise relatively prime"): the descended pair
   `ω = v²·r_aσr_a`, `θ = −r_bσr_b` generates coprime ideals.  A common maximal divisor `𝔪` of
   `(r_aσr_a)` and `(r_bσr_b)` contains one of `r_a, σr_a` and one of `r_b, σr_b`, hence two of the
   four factor values `x + ζʲy` (`j ∈ {1, 36}` and `j ∈ {2, 35}` — the factor equations at `ζ, ζ²`
   and their `σ`-conjugates); the difference identities `(x+ζʲy) − (x+ζᵏy) = (ζʲ−ζᵏ)y` and
   `ζʲ(x+ζᵏy) − ζᵏ(x+ζʲy) = (ζʲ−ζᵏ)x` with `ζʲ − ζᵏ ~ ζ − 1` (associated root differences) force
   `𝔪 ∋ x, y` (killed by the **old** datum's coprimality) or `𝔪 = 𝔭 = (ζ−1)` (killed by the proven
   sharp `𝔭`-coprimality `(ζ−1) ∤ r_a, r_b` and `σ𝔭 = 𝔭`).

3. **The restricted chain**: `CoprimeFreeContentCaseIIDvdZData37` (the combined `ℓ ∣ z` free-content
   datum **with** the coprime field), the coprime-preserving `p`-content descent step (the proven
   with-units step + (2)), the well-founded factor-count closure, the bridge, and the endpoint

   `fermatLastTheoremFor_thirtyseven_of_lemma96 : h_lemma96 → Kellner → FermatLastTheoremFor 37`

   — **no** coprimality hypothesis: the field lives on the data, the seed proves it for the
   rational entry, and the step propagates it.

No `sorry`, no new axioms (`propext, Classical.choice, Quot.sound` only).  This file imports only —
it does **not** modify any existing file.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1 p. 172 ("Since
  `ω₁, θ₁, ξ₁, λ` are pairwise relatively prime …"), §9.2 pp. 176–181 (Theorem 9.5, Lemmas 9.6–9.9).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Polynomial

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-! ## 1. The rational seed arithmetic: pairwise coprimality of the Fermat triple

`gcd {a, b, c} = 1` is the gcd of the **set**; pairwise coprimality needs the equation: a common
prime `p` of (say) `a, b` divides `c³⁷ = a³⁷ + b³⁷`, hence `c`, hence the set gcd `= 1` —
contradiction. -/

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **Pairwise coprimality of a Fermat triple from the set gcd** (Washington's implicit
normalisation).  From `gcd {a, b, c} = 1` and `a³⁷ + b³⁷ = c³⁷`: `IsCoprime a b`, `IsCoprime b c`,
and `IsCoprime a c`.  A common prime of any two entries divides the third power-sum/difference,
hence the third entry (`37`-th powers, prime divisor), hence the set gcd. -/
theorem caseII_int_solution_pairwise_coprime {a b c : ℤ}
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (e : a ^ 37 + b ^ 37 = c ^ 37) :
    IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime a c := by
  -- a prime dividing all three divides the set gcd `= 1`: absurd.
  have hkey : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → (p : ℤ) ∣ c → False := by
    intro p hp ha hb hc
    have hdvd : (p : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      refine Finset.dvd_gcd ?_
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ‹_›
    rw [hgcd] at hdvd
    exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one hdvd
  -- a common prime of two entries divides the third (via the equation).
  have hprime_c : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ b → (p : ℤ) ∣ c := by
    intro p hp ha hb
    refine (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (n := 37) ?_
    rw [← e]
    exact dvd_add (dvd_pow ha (by decide)) (dvd_pow hb (by decide))
  have hprime_a : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → (p : ℤ) ∣ c → (p : ℤ) ∣ a := by
    intro p hp hb hc
    refine (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (n := 37) ?_
    have h := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
      (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
    rwa [← e, add_sub_cancel_right] at h
  have hprime_b : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → (p : ℤ) ∣ c → (p : ℤ) ∣ b := by
    intro p hp ha hc
    refine (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow (n := 37) ?_
    have h := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
      (dvd_pow ha (by decide : (37 : ℕ) ≠ 0))
    rwa [← e, add_sub_cancel_left] at h
  refine ⟨?_, ?_, ?_⟩
  · rw [Int.isCoprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpdvd
    have hpa : (p : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_left a b)
    have hpb : (p : ℤ) ∣ b := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_right a b)
    exact hkey p hp hpa hpb (hprime_c p hp hpa hpb)
  · rw [Int.isCoprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpdvd
    have hpb : (p : ℤ) ∣ b := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_left b c)
    have hpc : (p : ℤ) ∣ c := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_right b c)
    exact hkey p hp (hprime_a p hp hpb hpc) hpb hpc
  · rw [Int.isCoprime_iff_gcd_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hpdvd
    have hpa : (p : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_left a c)
    have hpc : (p : ℤ) ∣ c := (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_right a c)
    exact hkey p hp hpa (hprime_b p hp hpa hpc) hpc

omit [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
  [NumberField.IsCMField (CyclotomicField 37 ℚ)] in
/-- **Bézout casts along `ℤ → 𝓞 K`**: coprime integers generate coprime ideals of the ring of
integers.  `u·x + v·y = 1` casts to `𝓞 K`, giving `IsCoprime ((x : 𝓞 K)) ((y : 𝓞 K))`, hence the
span coprimality (`Ideal.isCoprime_span_singleton_iff`). -/
theorem caseII_intCast_span_isCoprime {x y : ℤ} (h : IsCoprime x y) :
    IsCoprime (Ideal.span ({(x : 𝓞 (CyclotomicField 37 ℚ))} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({(y : 𝓞 (CyclotomicField 37 ℚ))} : Set (𝓞 (CyclotomicField 37 ℚ)))) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  obtain ⟨u, v, huv⟩ := h
  exact ⟨(u : 𝓞 (CyclotomicField 37 ℚ)), (v : 𝓞 (CyclotomicField 37 ℚ)), by
    exact_mod_cast congrArg (fun t : ℤ ↦ (t : 𝓞 (CyclotomicField 37 ℚ))) huv⟩

/-! ## 2. The two-root-factor forcing (the kernel of Washington's "pairwise relatively prime")

If a maximal ideal `𝔪` contains two distinct root factors `x + ζʲy` and `x + ζᵏy` of a coprime
pair `x, y`, then `𝔪` contains `ζ − 1` (i.e. `𝔪 = 𝔭`): the difference identities put
`(ζʲ − ζᵏ)·y` and `(ζʲ − ζᵏ)·x` in `𝔪`; primality forces `ζʲ − ζᵏ ∈ 𝔪` (else `x, y ∈ 𝔪`,
contradicting `(x) + (y) = (1)`), and `ζʲ − ζᵏ ~ ζ − 1`. -/

/-- **[F3 — two-root-factor forcing]** A maximal ideal containing two distinct root factors
`x + ζʲ·y`, `x + ζᵏ·y` (`j ≠ k`, `j, k < 37`) of a span-coprime pair `x, y` contains `ζ − 1`. -/
theorem caseII_coprime_two_root_factor_mem_forces_p
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))))
    {𝔪 : Ideal (𝓞 (CyclotomicField 37 ℚ))} (h𝔪 : 𝔪.IsMaximal)
    {j k : ℕ} (hj : j < 37) (hk : k < 37) (hjk : j ≠ k)
    (hmemj : D.x + D.hζ.toInteger ^ j * D.y ∈ 𝔪)
    (hmemk : D.x + D.hζ.toInteger ^ k * D.y ∈ 𝔪) :
    D.hζ.toInteger - 1 ∈ 𝔪 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set ζ := D.hζ.toInteger with hζdef
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  -- difference identities: `(ζʲ − ζᵏ)·y ∈ 𝔪` and `(ζʲ − ζᵏ)·x ∈ 𝔪`.
  have hy_mem : (ζ ^ j - ζ ^ k) * D.y ∈ 𝔪 := by
    have h := 𝔪.sub_mem hmemj hmemk
    have heq : (D.x + ζ ^ j * D.y) - (D.x + ζ ^ k * D.y) = (ζ ^ j - ζ ^ k) * D.y := by ring
    rwa [heq] at h
  have hx_mem : (ζ ^ j - ζ ^ k) * D.x ∈ 𝔪 := by
    have h := 𝔪.sub_mem (𝔪.mul_mem_left (ζ ^ j) hmemk) (𝔪.mul_mem_left (ζ ^ k) hmemj)
    have heq : ζ ^ j * (D.x + ζ ^ k * D.y) - ζ ^ k * (D.x + ζ ^ j * D.y) =
        (ζ ^ j - ζ ^ k) * D.x := by ring
    rwa [heq] at h
  by_cases hd : (ζ ^ j - ζ ^ k) ∈ 𝔪
  · -- `ζʲ − ζᵏ ~ ζ − 1` (distinct `37`-th roots), so `ζ − 1 ∈ 𝔪`.
    have hmem_j' : (ζ ^ j : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      (mem_nthRootsFinset (by norm_num) _).mpr (by
        rw [← pow_mul, mul_comm, pow_mul, hζ37, one_pow])
    have hmem_k' : (ζ ^ k : 𝓞 (CyclotomicField 37 ℚ)) ∈
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
      (mem_nthRootsFinset (by norm_num) _).mpr (by
        rw [← pow_mul, mul_comm, pow_mul, hζ37, one_pow])
    have hne : (ζ ^ j : 𝓞 (CyclotomicField 37 ℚ)) ≠ ζ ^ k :=
      fun h ↦ hjk (D.hζ.toInteger_isPrimitiveRoot.pow_inj hj hk h)
    have hassoc : Associated (ζ - 1) (ζ ^ j - ζ ^ k) :=
      D.hζ.toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
        (by decide : Nat.Prime 37) hmem_j' hmem_k' hne
    obtain ⟨t, ht⟩ := hassoc.symm.dvd
    rw [ht]
    exact 𝔪.mul_mem_right t hd
  · -- primality: `x, y ∈ 𝔪`, contradicting the span coprimality.
    have hy' : D.y ∈ 𝔪 := (h𝔪.isPrime.mem_or_mem hy_mem).resolve_left hd
    have hx' : D.x ∈ 𝔪 := (h𝔪.isPrime.mem_or_mem hx_mem).resolve_left hd
    exfalso
    have hsup := Ideal.isCoprime_iff_sup_eq.mp hcop
    have hle : Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))) ⊔
        Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))) ≤ 𝔪 :=
      sup_le ((Ideal.span_singleton_le_iff_mem 𝔪).mpr hx')
        ((Ideal.span_singleton_le_iff_mem 𝔪).mpr hy')
    rw [hsup] at hle
    exact h𝔪.ne_top (top_le_iff.mp hle)

/-! ## 3. The descent-step coprimality preservation (Washington p. 172)

The descended pair's blocks `r_aσr_a`, `r_bσr_b` generate coprime ideals: a common maximal divisor
`𝔪` contains one of `r_a, σr_a` and one of `r_b, σr_b`, hence two of the four root factors
`x + ζʲy` (`j ∈ {1, 36}` resp. `{2, 35}`, via the integral factor equations and their
`σ`-conjugates); §2 forces `𝔪 = 𝔭`, killed by the proven sharp `𝔭`-coprimalities
`(ζ−1) ∤ r_a, r_b` and `(ζ−1) ∤ σr_a, σr_b` (`σ𝔭 = 𝔭`). -/

/-- **[F3 — descended blocks coprime]** From the integral §9.1 factor equations at `ζ, ζ²`
(`x + ζy = (1−ζ)·u_a·r_a³⁷`, `x + ζ²y = (1−ζ²)·u_b·r_b³⁷`, integral units `u_a, u_b`), the old
coprimality `IsCoprime ((x)) ((y))`, and the sharp `𝔭`-coprimalities `(ζ−1) ∤ r_a, r_b`:

  `IsCoprime ((r_a·σr_a)) ((r_b·σr_b))`.

This is Washington p. 172's "`ω₁, θ₁` relatively prime" for the conjugate-norm blocks. -/
theorem caseII_descended_blocks_span_isCoprime
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))))
    (ra rb : 𝓞 (CyclotomicField 37 ℚ)) (ua ub : (𝓞 (CyclotomicField 37 ℚ))ˣ)
    (hFa : D.x + D.hζ.toInteger * D.y =
      (1 - D.hζ.toInteger) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37)
    (hFb : D.x + D.hζ.toInteger ^ 2 * D.y =
      (1 - D.hζ.toInteger ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37)
    (hra_p : ¬ D.hζ.toInteger - 1 ∣ ra) (hrb_p : ¬ D.hζ.toInteger - 1 ∣ rb) :
    IsCoprime
      (Ideal.span ({ra * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ra} :
        Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({rb * ringOfIntegersComplexConj (CyclotomicField 37 ℚ) rb} :
        Set (𝓞 (CyclotomicField 37 ℚ)))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set σR := ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hσR
  set ζ := D.hζ.toInteger with hζdef
  have hζ37 : ζ ^ 37 = 1 := D.hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hσζ : σR ζ = ζ ^ 36 := caseII_ringOfIntegersComplexConj_root_of_unity hζ37
  have hx_real : σR D.x = D.x := D.x_real
  have hy_real : σR D.y = D.y := D.y_real
  -- the `σ`-conjugated factor equations: `x + ζ³⁶y = (1−ζ³⁶)·σu_a·(σr_a)³⁷`,
  -- `x + ζ³⁵y = (1−ζ³⁵)·σu_b·(σr_b)³⁷`.
  have hFa_conj : D.x + ζ ^ 36 * D.y =
      (1 - ζ ^ 36) * σR (ua : 𝓞 (CyclotomicField 37 ℚ)) * (σR ra) ^ 37 := by
    have h := congrArg σR hFa
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hx_real, hy_real, hσζ] at h
    exact h
  have hFb_conj : D.x + ζ ^ 35 * D.y =
      (1 - ζ ^ 35) * σR (ub : 𝓞 (CyclotomicField 37 ℚ)) * (σR rb) ^ 37 := by
    have h := congrArg σR hFb
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hx_real, hy_real, hσζ] at h
    have h72 : ((ζ : 𝓞 (CyclotomicField 37 ℚ)) ^ 36) ^ 2 = ζ ^ 35 := by
      rw [← pow_mul]
      calc (ζ : 𝓞 (CyclotomicField 37 ℚ)) ^ (36 * 2) = ζ ^ 37 * ζ ^ 35 := by rw [← pow_add]
      _ = ζ ^ 35 := by rw [hζ37, one_mul]
    rwa [h72] at h
  -- `𝔭`-coprimality of the conjugates (`σ𝔭 = 𝔭`).
  have hσra_p : ¬ ζ - 1 ∣ σR ra := caseII_zeta_sub_one_not_dvd_complexConj D hra_p
  have hσrb_p : ¬ ζ - 1 ∣ σR rb := caseII_zeta_sub_one_not_dvd_complexConj D hrb_p
  -- `(ζ−1)` generates a maximal ideal (nonzero prime in a Dedekind domain).
  have hprime : Prime (ζ - 1 : 𝓞 (CyclotomicField 37 ℚ)) := D.hζ.zeta_sub_one_prime'
  have hspan_prime : (Ideal.span ({ζ - 1} : Set (𝓞 (CyclotomicField 37 ℚ)))).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hspan_max : (Ideal.span ({ζ - 1} : Set (𝓞 (CyclotomicField 37 ℚ)))).IsMaximal :=
    hspan_prime.isMaximal (by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero)
  -- the sup is `⊤`: otherwise a common maximal divisor exists, and the forcing kills it.
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨𝔪, h𝔪max, hle⟩ := Ideal.exists_le_maximal _ hne
  have hs_mem : ra * σR ra ∈ 𝔪 := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have ht_mem : rb * σR rb ∈ 𝔪 := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  -- the four root-factor memberships, from the (conjugated) factor equations.
  have hmem_ra : ra ∈ 𝔪 → D.x + ζ ^ 1 * D.y ∈ 𝔪 := fun h ↦ by
    rw [pow_one, hFa]
    exact 𝔪.mul_mem_left _ (Ideal.pow_mem_of_mem 𝔪 h 37 (by norm_num))
  have hmem_σra : σR ra ∈ 𝔪 → D.x + ζ ^ 36 * D.y ∈ 𝔪 := fun h ↦ by
    rw [hFa_conj]
    exact 𝔪.mul_mem_left _ (Ideal.pow_mem_of_mem 𝔪 h 37 (by norm_num))
  have hmem_rb : rb ∈ 𝔪 → D.x + ζ ^ 2 * D.y ∈ 𝔪 := fun h ↦ by
    rw [hFb]
    exact 𝔪.mul_mem_left _ (Ideal.pow_mem_of_mem 𝔪 h 37 (by norm_num))
  have hmem_σrb : σR rb ∈ 𝔪 → D.x + ζ ^ 35 * D.y ∈ 𝔪 := fun h ↦ by
    rw [hFb_conj]
    exact 𝔪.mul_mem_left _ (Ideal.pow_mem_of_mem 𝔪 h 37 (by norm_num))
  -- the finisher: a block factor in `𝔪` together with `ζ − 1 ∈ 𝔪` forces `𝔪 = 𝔭`, contradicting
  -- the sharp `𝔭`-coprimality of that factor.
  have hfinish : ∀ s : 𝓞 (CyclotomicField 37 ℚ), s ∈ 𝔪 → ¬ ζ - 1 ∣ s → ζ - 1 ∈ 𝔪 → False := by
    intro s hs hndvd hζm
    have h𝔪eq : Ideal.span ({ζ - 1} : Set (𝓞 (CyclotomicField 37 ℚ))) = 𝔪 :=
      hspan_max.eq_of_le h𝔪max.ne_top ((Ideal.span_singleton_le_iff_mem 𝔪).mpr hζm)
    exact hndvd (Ideal.mem_span_singleton.mp (h𝔪eq ▸ hs))
  -- four cases, each pairing one `a`-block factor with one `b`-block factor.
  rcases h𝔪max.isPrime.mem_or_mem hs_mem with hra_m | hσra_m
  · rcases h𝔪max.isPrime.mem_or_mem ht_mem with hrb_m | hσrb_m
    · exact hfinish ra hra_m hra_p
        (caseII_coprime_two_root_factor_mem_forces_p D hcop h𝔪max
          (by norm_num) (by norm_num) (by norm_num) (hmem_ra hra_m) (hmem_rb hrb_m))
    · exact hfinish ra hra_m hra_p
        (caseII_coprime_two_root_factor_mem_forces_p D hcop h𝔪max
          (by norm_num) (by norm_num) (by norm_num) (hmem_ra hra_m) (hmem_σrb hσrb_m))
  · rcases h𝔪max.isPrime.mem_or_mem ht_mem with hrb_m | hσrb_m
    · exact hfinish (σR ra) hσra_m hσra_p
        (caseII_coprime_two_root_factor_mem_forces_p D hcop h𝔪max
          (by norm_num) (by norm_num) (by norm_num) (hmem_σra hσra_m) (hmem_rb hrb_m))
    · exact hfinish (σR ra) hσra_m hσra_p
        (caseII_coprime_two_root_factor_mem_forces_p D hcop h𝔪max
          (by norm_num) (by norm_num) (by norm_num) (hmem_σra hσra_m) (hmem_σrb hσrb_m))

/-! ## 4. The coprime-restricted combined datum -/

/-- **[F3 — THE COPRIME-RESTRICTED COMBINED DATUM]** A combined `ℓ ∣ z` free-content Case-II datum
`FreeContentCaseIIDvdZData37` **carrying** the coprimality of its Fermat variables as a datum
field:

* `hcop` — `IsCoprime ((x)) ((y))`: the two Fermat variables generate coprime ideals.

This is a **datum field** — true *of the data* (the rational seed has it from `gcd {a,b,c} = 1`,
and the descent preserves it, Washington p. 172) — never an abstract universal (the universal is
provably false: scale a datum by a rational prime `≠ 37, 149`). -/
structure CoprimeFreeContentCaseIIDvdZData37 (n : ℕ)
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)]
    extends FreeContentCaseIIDvdZData37 n where
  /-- The coprimality of the Fermat variables (datum field, not a universal). -/
  hcop : IsCoprime
    (Ideal.span ({toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37.x} :
      Set (𝓞 (CyclotomicField 37 ℚ))))
    (Ideal.span ({toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37.y} :
      Set (𝓞 (CyclotomicField 37 ℚ))))

/-- The coprime field transported to the real promotion (`toReal` preserves `x, y`
definitionally). -/
theorem CoprimeFreeContentCaseIIDvdZData37.hcop_toReal
    {m : ℕ} (D : CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))) :
    IsCoprime
      (Ideal.span
        ({(freeContentCaseIIData37_toReal
            D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37).x} :
          Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span
        ({(freeContentCaseIIData37_toReal
            D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37).y} :
          Set (𝓞 (CyclotomicField 37 ℚ)))) :=
  D.hcop

/-! ## 5. The coprime rational seed (Washington Lemmas 9.6/9.7 + pairwise coprimality) -/

/-- **The coprime-restricted seed at the `37 ∣ z` normal form** (proven, axiom-clean).  Mirrors
`exists_realCaseIIDvdZData37_of_Int_solution`, additionally threading the integer coprimality
`IsCoprime x y` into the produced datum's span coprimality (the producer's `D.x, D.y` are the
integer casts), and packaging into the **coprime** combined frame. -/
theorem exists_coprimeFreeContentCaseIIDvdZData37_of_Int_solution
    {x y z : ℤ} (hy_int : ¬ (37 : ℤ) ∣ y) (hz_int : (37 : ℤ) ∣ z) (hz_ne : z ≠ 0)
    (e : x ^ 37 + y ^ 37 = z ^ 37)
    (hx_lv : ¬ (149 : ℤ) ∣ x) (hy_lv : ¬ (149 : ℤ) ∣ y)
    (hxy_cop : IsCoprime x y) :
    ∃ m : ℕ, Nonempty (CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  haveI : lv149.IsPrime := lv149_isMaximal.isPrime
  -- the producer's datum with the `z = (ζ−1)^{m+1}·D.z` relation and `D.x, D.y` exposed.
  obtain ⟨m, D, hDx, hDy, hz_eq⟩ :=
    exists_realCaseIIData37_zRel_of_Int_solution hy_int hz_int hz_ne e
  -- `149 ∤ x, y` as `ZMod 149` non-vanishing.
  have hx' : ¬ (x : ZMod 149) = 0 := fun h ↦ hx_lv ((ZMod.intCast_zmod_eq_zero_iff_dvd x 149).mp h)
  have hy' : ¬ (y : ZMod 149) = 0 := fun h ↦ hy_lv ((ZMod.intCast_zmod_eq_zero_iff_dvd y 149).mp h)
  -- Lemma 9.7 at the base: `149 ∣ z` (the Furtwängler residue obstruction).
  have hz_lv_int : (z : ZMod 149) = 0 := by
    have he : (x : ZMod 149) ^ 37 + (y : ZMod 149) ^ 37 = (z : ZMod 149) ^ 37 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod 149) e
    rcases furtwangler_37_149 (x : ZMod 149) (y : ZMod 149) (z : ZMod 149) he with h | h | h
    · exact absurd h hx'
    · exact absurd h hy'
    · exact h
  have hz_mem : (z : 𝓞 (CyclotomicField 37 ℚ)) ∈ lv149 :=
    (caseII_intCast_mem_lv149_iff z).mpr hz_lv_int
  rw [hz_eq] at hz_mem
  have hDz_mem : D.z ∈ lv149 := by
    rcases Ideal.IsPrime.mem_or_mem ‹lv149.IsPrime› hz_mem with hpow | hz'
    · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹lv149.IsPrime› (m + 1) hpow)
        (caseII_zeta_sub_one_notMem_lv149 D.hζ)
    · exact hz'
  have hDx_notMem : D.x ∉ lv149 := by
    rw [hDx]; exact fun h ↦ hx' ((caseII_intCast_mem_lv149_iff x).mp h)
  have hDy_notMem : D.y ∉ lv149 := by
    rw [hDy]; exact fun h ↦ hy' ((caseII_intCast_mem_lv149_iff y).mp h)
  -- the threaded span coprimality at the seed.
  have hcopD : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) := by
    rw [hDx, hDy]
    exact caseII_intCast_span_isCoprime hxy_cop
  let Drz : RealCaseIIDvdZData37 m :=
    { toRealCaseIIData37 := D
      z_mem := hDz_mem
      x_notMem := hDx_notMem
      y_notMem := hDy_notMem }
  exact ⟨m, ⟨⟨FreeContentCaseIIDvdZData37.ofRealCaseIIDvdZData37 Drz, hcopD⟩⟩⟩

/-- **The coprime-restricted seed at the `37 ∣ c` normal form** (proven, axiom-clean), deriving
`37 ∤ b` from the equation. -/
theorem exists_coprimeFreeContentCaseIIDvdZData37_of_lemma96
    {a b c : ℤ} (ha_int : ¬ (37 : ℤ) ∣ a) (hc_int : (37 : ℤ) ∣ c) (hc_ne : c ≠ 0)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (ha_lv : ¬ (149 : ℤ) ∣ a) (hb_lv : ¬ (149 : ℤ) ∣ b)
    (hab_cop : IsCoprime a b) :
    ∃ m : ℕ, Nonempty (CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  have hb_int : ¬ (37 : ℤ) ∣ b := by
    intro hb
    refine ha_int ?_
    have h37prime := (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
    have h_dvd : (37 : ℤ) ∣ a ^ 37 := by
      have := dvd_sub (dvd_pow hc_int (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at this
    exact h37prime.dvd_of_dvd_pow h_dvd
  exact exists_coprimeFreeContentCaseIIDvdZData37_of_Int_solution hb_int hc_int hc_ne e
    ha_lv hb_lv hab_cop

/-- **The general coprime-restricted producer** (proven, axiom-clean) — from *any* Case-II integer
FLT solution with **Lemma 9.6**, the coprime combined domain is non-empty.  Mirrors
`exists_realCaseIIDvdZData37_of_caseII_int_solution`'s WLOG permutation; the pairwise coprimality
(`caseII_int_solution_pairwise_coprime`) survives each permutation (negation preserves
coprimality). -/
theorem exists_coprimeFreeContentCaseIIDvdZData37_of_caseII_int_solution
    {a b c : ℤ}
    (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcase : (37 : ℤ) ∣ a * b * c)
    (e : a ^ 37 + b ^ 37 = c ^ 37)
    (h_lemma96 : ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    ∃ m : ℕ, Nonempty (CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨hab_cop, hbc_cop, hac_cop⟩ := caseII_int_solution_pairwise_coprime hgcd e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨ha0, hb0⟩, hc0⟩ := hprod
  have h37 := (Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 37))
  have hodd' := Nat.Prime.odd_of_ne_two (by decide : Nat.Prime 37) (by decide : (37 : ℕ) ≠ 2)
  -- `37` divides at most one of `a, b, c`.
  have h37c : (37 : ℤ) ∣ a → (37 : ℤ) ∣ b → False := by
    intro ha hb
    have hc : (37 : ℤ) ∣ c := by
      have hcp : (37 : ℤ) ∣ c ^ 37 := by
        rw [← e]; exact dvd_add (dvd_pow ha (by decide)) (dvd_pow hb (by decide))
      exact h37.dvd_of_dvd_pow hcp
    have : (37 : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      rw [Finset.dvd_gcd_iff]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ‹_›
    rw [hgcd] at this
    exact absurd (Int.isUnit_iff.mp (isUnit_of_dvd_one this)) (by decide)
  have h37bc : (37 : ℤ) ∣ b → (37 : ℤ) ∣ c → False := by
    intro hb hc
    refine h37c ?_ hb
    have hap : (37 : ℤ) ∣ a ^ 37 := by
      have := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow hb (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_right] at this
    exact h37.dvd_of_dvd_pow hap
  have h37ac : (37 : ℤ) ∣ a → (37 : ℤ) ∣ c → False := by
    intro ha hc
    refine h37c ha ?_
    have hbp : (37 : ℤ) ∣ b ^ 37 := by
      have := dvd_sub (dvd_pow hc (by decide : (37 : ℕ) ≠ 0))
        (dvd_pow ha (by decide : (37 : ℕ) ≠ 0))
      rwa [← e, add_sub_cancel_left] at this
    exact h37.dvd_of_dvd_pow hbp
  obtain hab | hc := h37.dvd_or_dvd hcase
  · obtain ha | hb := h37.dvd_or_dvd hab
    · -- `37 ∣ a`: normal form `(b, -c, -a)`; the pair is `(b, -c)`.
      have he' : b ^ 37 + (-c) ^ 37 = (-a) ^ 37 := by
        rw [hodd'.neg_pow, hodd'.neg_pow]; linarith [e]
      have hb37 : ¬ (37 : ℤ) ∣ b := fun hb ↦ h37c ha hb
      have hc37 : ¬ (37 : ℤ) ∣ c := fun hc ↦ h37ac ha hc
      have hb_lv : ¬ (149 : ℤ) ∣ b := h_lemma96 b hb37 (Or.inr (Or.inl rfl))
      have hc_lv : ¬ (149 : ℤ) ∣ c := h_lemma96 c hc37 (Or.inr (Or.inr rfl))
      exact exists_coprimeFreeContentCaseIIDvdZData37_of_lemma96
        (a := b) (b := -c) (c := -a) hb37 (by rwa [dvd_neg]) (by rwa [neg_ne_zero])
        he' hb_lv (fun h ↦ hc_lv (dvd_neg.mp h)) hbc_cop.neg_right
    · -- `37 ∣ b`: normal form `(-c, a, -b)`; the pair is `(-c, a)`.
      have he' : (-c) ^ 37 + a ^ 37 = (-b) ^ 37 := by
        rw [hodd'.neg_pow, hodd'.neg_pow]; linarith [e]
      have ha37 : ¬ (37 : ℤ) ∣ a := fun ha ↦ h37c ha hb
      have hc37 : ¬ (37 : ℤ) ∣ c := fun hc ↦ h37bc hb hc
      have ha_lv : ¬ (149 : ℤ) ∣ a := h_lemma96 a ha37 (Or.inl rfl)
      have hc_lv : ¬ (149 : ℤ) ∣ c := h_lemma96 c hc37 (Or.inr (Or.inr rfl))
      exact exists_coprimeFreeContentCaseIIDvdZData37_of_lemma96
        (a := -c) (b := a) (c := -b) (by rwa [dvd_neg]) (by rwa [dvd_neg])
        (by rwa [neg_ne_zero]) he' (fun h ↦ hc_lv (dvd_neg.mp h)) ha_lv
        hac_cop.symm.neg_left
  · -- `37 ∣ c`: the producer's own normal form `(a, b, c)`; the pair is `(a, b)`.
    have ha37 : ¬ (37 : ℤ) ∣ a := fun ha ↦ h37ac ha hc
    have hb37 : ¬ (37 : ℤ) ∣ b := fun hb ↦ h37bc hb hc
    have ha_lv : ¬ (149 : ℤ) ∣ a := h_lemma96 a ha37 (Or.inl rfl)
    have hb_lv : ¬ (149 : ℤ) ∣ b := h_lemma96 b hb37 (Or.inr (Or.inl rfl))
    exact exists_coprimeFreeContentCaseIIDvdZData37_of_lemma96 ha37 hc hc0 e ha_lv hb_lv hab_cop

/-! ## 6. The coprime-preserving `p`-content descent step

The proven with-units descent step (`freeContentCaseIIDvdZData37_pContent_descend_withUnits`),
re-run on the coprime-restricted domain: the old datum's coprimality is the **datum field** (no
universal), and the **new** datum's coprimality is derived from §3 — the descended pair
`ω = v²·r_aσr_a`, `θ = −r_bσr_b` (integral identifications via the integral-closure witnesses)
generates coprime ideals. -/

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
-- The bumped `maxHeartbeats` (and `maxRecDepth`, as in the parent
-- `freeContentCaseIIDvdZData37_pContent_descend_withUnits`) is needed because destructuring the
-- very large `CaseIISection91PContentExtractionDataWithUnits37` output (a 24-conjunct `∃`-chain)
-- and re-checking the §3 coprimality derivation on top exceeds the default budgets.
/-- **[F3 — the coprime-preserving descent step]** (proven, axiom-clean *given* the with-units
extraction data): the combined `ℓ ∣ z` descent step at content `37·(m+1)` with `p`-content output,
on the **coprime-restricted** domain — the old coprimality is consumed from the datum, the new
coprimality is **proved** (Washington p. 172, via `caseII_descended_blocks_span_isCoprime`). -/
theorem coprimeFreeContentCaseIIDvdZData37_pContent_descend_withUnits
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    {m : ℕ} (D : CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1)))
    (hnonterm : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))) :
    ∃ (m' : ℕ) (D' : CoprimeFreeContentCaseIIDvdZData37 (37 * (m' + 1))),
      caseIIFreeDvdZFactorCount D'.toFreeContentCaseIIDvdZData37 <
        caseIIFreeDvdZFactorCount D.toFreeContentCaseIIDvdZData37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set Dr := freeContentCaseIIData37_toReal
    D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37 with hDr
  have hcop : IsCoprime (Ideal.span ({Dr.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({Dr.y} : Set (𝓞 (CyclotomicField 37 ℚ)))) := D.hcop_toReal
  let Drz : RealCaseIIDvdZData37 m :=
    { toRealCaseIIData37 := Dr
      z_mem := D.toFreeContentCaseIIDvdZData37.z_mem
      x_notMem := D.toFreeContentCaseIIDvdZData37.x_notMem
      y_notMem := D.toFreeContentCaseIIDvdZData37.y_notMem }
  have hnonterm' : ¬ ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      caseII_correctedRadical Dr Dr.etaOne (caseII_correctionUnit Dr.etaOne) =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ)) := by
    rw [← caseIIFree_correctedRadical_eq_real
      D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37]
    exact hnonterm
  -- The STRENGTHENED factor equations at `ζ`, `ζ²`, with integral units `u_a, u_b`.
  obtain ⟨ηa, ηb, ρa, ρb, ua, ub, hηa_real, hηb_real, hua, hub, hfa_pos, hfb_pos⟩ :=
    caseII_section91_factorEquations_etaOne_etaTwo_withUnits Dr hcop
  -- The with-units extraction data.
  obtain ⟨e, k, η0, u, ρ0, ω, θ, z', δ', he, hk, hanchor, hII, hη0real, hω, hθ, hz',
      _hδ', hω_real, hθ_real, hθ_cop, hxy', hdenom', hz'_span, hint_eq, hz'_mem, hω_notMem,
      hθ_notMem, hpc⟩ :=
    h_data Drz hcop ηa ηb ρa ρb ua ub hηa_real hηb_real hua hub hfa_pos hfb_pos
  -- `¬ (zeta_spec − 1) ∣ z'`.
  have hz'_cop : ¬ (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 ∣ z' := by
    have hnot : ¬ Ideal.span ({((zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger - 1 :
        𝓞 (CyclotomicField 37 ℚ))} : Set _) ∣
        Ideal.span ({z'} : Set (𝓞 (CyclotomicField 37 ℚ))) := by
      have hassoc := caseII_section91_zeta_sub_one_associated_zeta_spec Dr
      rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc.symm, hz'_span]; intro hdvd
      exact not_p_div_a_zero hp Dr.hζ Dr.equation Dr.hy Dr.hz
        ((Ideal.prime_span_singleton_iff.mpr Dr.hζ.zeta_sub_one_prime').dvd_of_dvd_pow hdvd)
    rwa [Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hnot
  /- ### The NEW pair's coprimality (the F3 preservation, Washington p. 172) -/
  have hinj : Function.Injective (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)) :=
    FaithfulSMul.algebraMap_injective _ _
  set σR := ringOfIntegersComplexConj (CyclotomicField 37 ℚ) with hσRdef
  -- the root subtypes `ζ`, `ζ²` and their `≠ η₀` facts.
  have hζ1 : Dr.hζ.toInteger ≠ 1 := Dr.hζ.toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
  have hetaZero : (Dr.etaZero : 𝓞 (CyclotomicField 37 ℚ)) = 1 := caseII_etaZero_eq_one Dr hp
  have hζmem : Dr.hζ.toInteger ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    Dr.hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset (by decide : 0 < 37)
  have hηOne_ne : (⟨Dr.hζ.toInteger, hζmem⟩ :
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠ Dr.etaZero := by
    intro h
    exact hζ1 (by have := Subtype.ext_iff.mp h; rw [hetaZero] at this; exact this)
  have hζ2_1 : Dr.hζ.toInteger ^ 2 ≠ 1 :=
    Dr.hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega) (by decide : 2 < 37)
  have hmem2 : Dr.hζ.toInteger ^ 2 ∈ nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ)) :=
    (mem_nthRootsFinset (by norm_num) _).mpr (by
      rw [← pow_mul, mul_comm, pow_mul, Dr.hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow])
  have hηTwo_ne : (⟨Dr.hζ.toInteger ^ 2, hmem2⟩ :
      nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) ≠ Dr.etaZero := by
    intro h
    exact hζ2_1 (by have := Subtype.ext_iff.mp h; rw [hetaZero] at this; exact this)
  -- integral generators `r_a, r_b` and the sharp `𝔭`-coprimalities.
  obtain ⟨ra, hra⟩ := caseII_factorGenerator_integral_of_unitInt Dr
    ⟨Dr.hζ.toInteger, hζmem⟩ hηOne_ne ηa ρa ua hua hfa_pos
  obtain ⟨rb, hrb⟩ := caseII_factorGenerator_integral_of_unitInt Dr
    ⟨Dr.hζ.toInteger ^ 2, hmem2⟩ hηTwo_ne ηb ρb ub hub (by
      rw [show ((⟨Dr.hζ.toInteger ^ 2, hmem2⟩ :
        nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
          𝓞 (CyclotomicField 37 ℚ)) = Dr.hζ.toInteger ^ 2 from rfl]
      exact hfb_pos)
  have hra_p : ¬ (Dr.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ ra :=
    caseII_zeta_sub_one_not_dvd_factorGenerator Dr ⟨Dr.hζ.toInteger, hζmem⟩ hηOne_ne
      ηa ρa ua ra hua hra hfa_pos
  have hrb_p : ¬ (Dr.hζ.toInteger - 1 : 𝓞 (CyclotomicField 37 ℚ)) ∣ rb :=
    caseII_zeta_sub_one_not_dvd_factorGenerator Dr ⟨Dr.hζ.toInteger ^ 2, hmem2⟩ hηTwo_ne
      ηb ρb ub rb hub hrb (by
        rw [show ((⟨Dr.hζ.toInteger ^ 2, hmem2⟩ :
          nthRootsFinset 37 (1 : 𝓞 (CyclotomicField 37 ℚ))) :
            𝓞 (CyclotomicField 37 ℚ)) = Dr.hζ.toInteger ^ 2 from rfl]
        exact hfb_pos)
  -- the Assumption-II unit is integral.
  obtain ⟨vU, hvU⟩ := caseII_assumptionII_unit_integral ηa ηb u ua ub hua hub hII
  -- the integral factor equations.
  have hFa_int : Dr.x + Dr.hζ.toInteger * Dr.y =
      (1 - Dr.hζ.toInteger) * (ua : 𝓞 (CyclotomicField 37 ℚ)) * ra ^ 37 := by
    apply hinj
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hua, hra]
    exact hfa_pos
  have hFb_int : Dr.x + Dr.hζ.toInteger ^ 2 * Dr.y =
      (1 - Dr.hζ.toInteger ^ 2) * (ub : 𝓞 (CyclotomicField 37 ℚ)) * rb ^ 37 := by
    apply hinj
    simp only [map_add, map_mul, map_sub, map_one, map_pow, hub, hrb]
    have hfb_pos' := hfb_pos
    rw [map_pow] at hfb_pos'
    exact hfb_pos'
  -- the descended blocks generate coprime ideals (§3).
  have hpair := caseII_descended_blocks_span_isCoprime Dr hcop ra rb ua ub
    hFa_int hFb_int hra_p hrb_p
  -- the integral identifications `ω = v²·r_aσr_a`, `θ = −r_bσr_b`.
  have hσRcoe : ∀ w : 𝓞 (CyclotomicField 37 ℚ),
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (σR w) =
        complexConj (CyclotomicField 37 ℚ)
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) w) := fun w ↦ by
    rw [hσRdef, ← coe_ringOfIntegersComplexConj]
  have hω_int : ω = (vU : 𝓞 (CyclotomicField 37 ℚ)) ^ 2 * (ra * σR ra) := by
    apply hinj
    simp only [map_mul, map_pow]
    rw [hvU, hra, hσRcoe ra, hra, hω]
  have hθ_int : θ = -(rb * σR rb) := by
    apply hinj
    simp only [map_neg, map_mul]
    rw [hrb, hσRcoe rb, hrb, hθ]
  have hassocω : Associated (ra * σR ra) ω :=
    ⟨vU ^ 2, by rw [hω_int, Units.val_pow_eq_pow_val]; ring⟩
  have hassocθ : Associated (rb * σR rb) θ :=
    ⟨-1, by rw [hθ_int, Units.val_neg, Units.val_one]; ring⟩
  have hcop_new : IsCoprime (Ideal.span ({ω} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({θ} : Set (𝓞 (CyclotomicField 37 ℚ)))) := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr hassocω.symm,
      Ideal.span_singleton_eq_span_singleton.mpr hassocθ.symm]
    exact hpair
  /- ### the descended datum (as in the with-units step), now with the coprime field -/
  obtain ⟨m'', hcontent⟩ := hpc
  obtain ⟨Dnew, hDnew_x, hDnew_y, hDnew_z⟩ :=
    freeContentCaseIIData37_of_descended_equation_xyz_explicit
      (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)) he
      hint_eq hω_real hθ_real hθ_cop hz'_cop hxy' hdenom'
  let Dcomb0 : FreeContentCaseIIDvdZData37 (2 * (2 * e - 1)) :=
    { toFreeContentCaseIIData37 := Dnew,
      z_mem := by rw [hDnew_z]; exact hz'_mem,
      x_notMem := by rw [hDnew_x]; exact hω_notMem,
      y_notMem := by rw [hDnew_y]; exact hθ_notMem }
  have hdrop : caseIIFreeDvdZFactorCount Dcomb0 <
      caseIIFreeDvdZFactorCount D.toFreeContentCaseIIDvdZData37 := by
    change caseIIFreeFactorCount Dnew <
      caseIIFreeFactorCount D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37
    rw [caseIIFreeFactorCount, hDnew_z,
      caseIIFreeFactorCount_toReal D.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37]
    have hsupp := caseII_anchorSupported_of_span_eq_anchorPow Dr hk hz'_span
    exact caseIIZFactorCount_strict_of_anchor_supported Dr hp hnonterm' hsupp
  refine ⟨m'', ?_⟩
  rw [show 37 * (m'' + 1) = 2 * (2 * e - 1) from hcontent.symm]
  refine ⟨{ toFreeContentCaseIIDvdZData37 := Dcomb0, hcop := ?_ }, hdrop⟩
  change IsCoprime (Ideal.span ({Dnew.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
    (Ideal.span ({Dnew.y} : Set (𝓞 (CyclotomicField 37 ℚ))))
  rw [hDnew_x, hDnew_y]
  exact hcop_new

/-! ## 7. The well-founded closure on the coprime domain, the bridge, and the endpoint -/

/-- **No coprime combined `ℓ ∣ z` datum exists, from the with-units extraction data** (proven,
axiom-clean — NO coprimality hypothesis: the field lives on the data and the descent preserves
it).  Well-founded minimality on the factor count over the coprime `p`-content combined data. -/
theorem no_coprimeFreeContentCaseIIDvdZData37_withUnits
    (h_data : CaseIISection91PContentExtractionDataWithUnits37) :
    ¬ ∃ m : ℕ, Nonempty (CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))) := by
  classical
  rintro ⟨m₀, ⟨D₀⟩⟩
  let P : ℕ → Prop := fun j ↦
    ∃ (m : ℕ) (E : CoprimeFreeContentCaseIIDvdZData37 (37 * (m + 1))),
      caseIIFreeDvdZFactorCount E.toFreeContentCaseIIDvdZData37 = j
  have hP : ∃ j, P j := ⟨_, m₀, D₀, rfl⟩
  obtain ⟨mmin, Dmin, hj⟩ := Nat.find_spec hP
  by_cases hunit : ∃ αU : (𝓞 (CyclotomicField 37 ℚ))ˣ,
      Dmin.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37.caseIIFree_correctedRadical =
        algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
          (αU : 𝓞 (CyclotomicField 37 ℚ))
  · obtain ⟨αU, hαU⟩ := hunit
    exact caseIIFreeFirstLayer_false
      Dmin.toFreeContentCaseIIDvdZData37.toFreeContentCaseIIData37 αU hαU
  · obtain ⟨m', D', hlt⟩ :=
      coprimeFreeContentCaseIIDvdZData37_pContent_descend_withUnits h_data Dmin hunit
    rw [hj] at hlt
    exact Nat.find_min hP hlt ⟨m', D', rfl⟩

/-- **The public Case-II bridge with coprimality threaded through the data** (proven, axiom-clean
*given* the with-units extraction data + Washington Lemma 9.6 — **no** coprimality hypothesis). -/
theorem caseIIBridge_thirtyseven_of_caseII_withUnits_coprimeThreaded
    (h_data : CaseIISection91PContentExtractionDataWithUnits37)
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x) :
    BernoulliRegular.CaseIIBridge 37 (CyclotomicField 37 ℚ) 32 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨?_⟩
  intro _hV _hSO a b c hprod hgcd hcase hEq
  exact (no_coprimeFreeContentCaseIIDvdZData37_withUnits h_data)
    (exists_coprimeFreeContentCaseIIDvdZData37_of_caseII_int_solution hprod hgcd hcase hEq
      (h_lemma96 a b c hprod hgcd hcase hEq))

/-- **[F3 — THE FLT37 ENDPOINT, COPRIMALITY INTERNAL]** Fermat's Last Theorem for `37` from
Washington **Lemma 9.6** (`ℓ ∤ xy` at the rational seed) and the carried **Kellner** input
(`NoSecondOrderIrregularPair 37 32`) **only**.

The false-universal coprimality hypothesis of
`fermatLastTheoremFor_thirtyseven_of_lemma96_coprimality` is **gone**: coprimality is a datum
field, proved at the rational seed (`caseII_int_solution_pairwise_coprime`, pairwise from
`gcd {a,b,c} = 1` + the equation) and **preserved by the descent**
(`caseII_descended_blocks_span_isCoprime`, Washington p. 172).  Real Assumption II (F1) and the
aux-prime `ℓ`-propagation (F2) are proven
(`caseIISection91PContentExtractionDataWithUnits37_proven`); the Case-II bridge runs the
coprime-restricted well-founded factor-count descent. -/
theorem fermatLastTheoremFor_thirtyseven_of_lemma96
    (h_lemma96 : ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x)
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : NeZero 37 := ⟨by decide⟩
  exact BernoulliRegular.fermatLastTheoremFor_thirtyseven_of_remaining
    (BernoulliRegular.cor8_19Bridge_of_not_dvd_hPlus 37 (CyclotomicField 37 ℚ)
      Sinnott.flt37_not_dvd_hPlus)
    caseIBridge_thirtyseven_eichler
    noSecondOrderIrregular
    (caseIIBridge_thirtyseven_of_caseII_withUnits_coprimeThreaded
      (caseIISection91PContentExtractionDataWithUnits37_proven noSecondOrderIrregular)
      h_lemma96)

end BernoulliRegular.FLT37.Eichler

end

end
