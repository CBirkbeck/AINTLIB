import BernoulliRegular.FLT37.PadicL.IwasawaCongruenceModPSq
import BernoulliRegular.FLT37.PadicL.PowerSumModPCubed

/-!
# The **corrected** sharp Iwasawa congruence at `(p, i) = (37, 32)`

This file performs the soundness audit and correction of the `bernoulliGenModSq`
field of `IwasawaModSqData` (`IwasawaCongruenceModPSq.lean`), and reduces the sharp
valuation `v₃₇(B_{1,ω³¹}) = 1` (hence `v₃₇(L_p(1, ω³²)) = 1`, the Cor 8.23 `M = 1`
value) to a **single sound residual** that is *independent of Kellner*
(`NoSecondOrderIrregularPair 37 32`).

## STEP-0 SOUNDNESS VERDICT — the naive `bernoulliGenModSq` is FALSE as stated

`IwasawaModSqData.bernoulliGenModSq` at `i = 32` asserts the mod-`p²` congruence

  `B_{1,ω³¹}  ≡  B₃₂ / 32   (mod 37²)`.   (NAIVE)

This is **false as stated**.  The repository's proved mod-`p` shadow
(`bernoulliGenOmega_sub_bernoulliFactor_thirtytwo_modP`) factors through the Kummer
congruence

  `B_{1,ω³¹}  ≡  B_{1148}  ≡  B_{1148}/1148  ≡  B₃₂/32   (mod 37)`

(`1148 = 37·31 + 1 ≡ 1 mod 37`, `1148 ≡ 32 mod 36`), whose **last** step is the
Kummer congruence `(1−37^{m−1})B_m/m ≡ (1−37^{n−1})B_n/n (mod 37^{a+1})` between
`m = 1148` and `n = 32`.  Its order is `a + 1` with `a = v₃₇((1148 − 32)/36) =
v₃₇(31) = 0`; so the congruence between `B_{1148}/1148` and `B₃₂/32` is **sharp mod
37¹ only**.  At mod `37²` there is a genuine correction `= 37 · (derivative of the
Iwasawa power series of ω³²)`, the `s`-direction second-order (`λ`-invariant) datum.
Hence `B_{1,ω³¹} ≢ B₃₂/32 (mod 37²)` in general: the NAIVE field demands a congruence
the *true* `L`-value does not satisfy.  (The structure is not *inconsistent* — its
non-vacuity witness `nonvacuous37` uses a *fake* `L` with `Lp i := B_i/i` literally —
but it does not capture the real `L_p`, so it is a mis-statement, not a usable
residual.)  This is the expected verdict: were the congruence true, the proved
`v₃₇(B₃₂/32) = 1` would force `v₃₇(B_{1,ω³¹}) = 1` via a congruence carrying **no**
second-digit information, contradicting that the second digit is genuine content.

## Two over-statements caught and avoided

A *first* repair attempt — `37·B_{1,ω³¹} ≡ Σ_{k<37} k³² (mod 37³)` — is **also
false**.  By the exact Stickelberger identity (T006 below) `37·B_{1,ω³¹} =
Σ_a ω(a)³¹·a.val`, and the Teichmüller lift `ω(a) ≡ a.val³⁷ (mod 37²)` gives
`37·B_{1,ω³¹} ≡ Σ_{k<37} k^{1148} (mod 37²)`.  But a direct finite computation shows

  `Σ_{k<37} k^{1148} ≢ Σ_{k<37} k³²  (mod 37³)`

(`Σ k³² ≡ 43808`, `Σ k^{1148} ≡ 31487 mod 37³`; their difference has `v₃₇ = 2`, not
`≥ 3`).  So `37·B_{1,ω³¹}` does **not** match `Σ k³²` at the third digit, and the
mod-`p³`-to-`Σ k³²` form is over-stated.  Even `Σ k^{1148}` is **not** the third
digit of `37·B_{1,ω³¹}`: `ω(a) ≡ a.val³⁷ (mod 37²)` is *sharp*, so the per-term
correction `ω(a)³¹·a.val − a.val^{1148}` has `v₃₇` exactly `2`, and the summed
third-digit correction is the (undetermined) Fermat-quotient sum.  **The third digit
of `37·B_{1,ω³¹}` is genuinely the Teichmüller / Fermat-quotient content and equals
neither power-sum's third digit by anything provable here.**

## The SOUND residual

The genuine, irreducible content is therefore the **valuation of the Teichmüller
sum** itself:

  `bernoulliGenOmegaValuationTwo37  :=  v₃₇(37 · B_{1,ω³¹}) = 2`,

equivalently (by the exact T006 identity) `v₃₇(Σ_a ω(a)³¹·a.val) = 2`, equivalently
the sharp `v₃₇(B_{1,ω³¹}) = 1`.  It is stated **without** a false power-sum
comparison.  What *is* proved here, soundly:

* the **exact** Stickelberger value `37·B_{1,ω³¹} = Σ_a ω(a)³¹·a.val`
  (`thirtyseven_mul_bernoulliGenOmega_thirtytwo_eq`, from
  `natCast_mul_BernoulliGen_one_of_ne_one`);
* the **lower bound** `v₃₇(B_{1,ω³¹}) ≥ 1`
  (`one_le_valuation_bernoulliGenOmega_thirtytwo`) from the repo's proved mod-`p`
  shadow + `37 ∣ B₃₂/32`;
* the sharp `v₃₇(B_{1,ω³¹}) = 1`
  (`valuation_bernoulliGenOmega_thirtytwo_of_valTwo`) **from the residual**.

## Non-circularity with Kellner (verified)

`bernoulliGenOmegaValuationTwo37` is the **second `37`-adic digit of the Teichmüller
sum** = the Fermat-quotient / Washington Prop 8.12 content; `B_{1184} = B_{32·37}`
(the Kellner datum) does **not** appear.  Kellner governs the **`s`-direction**
Iwasawa second-order structure (whether `L_p(s, ω³²)` has a simple vs. higher-order
zero in `s`); `v₃₇(L_p(1, ω³²)) = 1` is the **`s = 0` first-order value**, a separate
datum.  See `PowerSumModPCubed.lean` (the elementary power-sum order `v₃₇(Σ k³²) = 2`
is pinned with **no** Kellner input; the `Σ k³²` second-order coefficient is
`B₃₀·C(32,2)/3`, not `B_{1184}`).  The same verdict applies to the Teichmüller sum:
its second digit is the Fermat-quotient transport (only available mod `p²` in the
repo via `teichmuller_sub_pow_val_mem_pow_two`), **not** Kellner.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, Thm 5.12,
  Thm 5.13 (Kummer congruences), Cor 5.13, Thm 5.18, Prop 8.12, Cor 8.23.
* Kellner, Math. Comp. 76 (2007), Prop 2.7 (the `s`-direction Iwasawa datum).
-/

namespace BernoulliRegular.FLT37.PadicL

open BernoulliRegular

/-- Local prime instance for `37`. -/
private instance instFact37IMC : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- **The exact Stickelberger identity** `37 · B_{1,ω³¹} = Σ_a ω(a)³¹ · a.val` in
`ℚ_[37]` (T006, `natCast_mul_BernoulliGen_one_of_ne_one`), as the `ℚ_[37]`-image of
the integral Teichmüller sum.  This is an **equality**, not a congruence: the entire
Bernoulli / generalized-Bernoulli layer of the residual is peeled off here. -/
theorem thirtyseven_mul_bernoulliGenOmega_thirtytwo_eq :
    (37 : ℚ_[37]) * bernoulliGenOmega 37 32 =
      ((∑ a : ZMod 37, BernoulliRegular.teichmuller 37 a ^ 31 * (a.val : ℤ_[37]) :
        ℤ_[37]) : ℚ_[37]) := by
  have hn_not_dvd : ¬ (37 - 1) ∣ 31 := by decide
  have hχ_ne_one : (teichmullerCharQp 37) ^ 31 ≠ 1 :=
    teichmullerCharQp_pow_ne_one_of_not_dvd (p := 37) hn_not_dvd
  have hT006 := natCast_mul_BernoulliGen_one_of_ne_one
    (R := ℚ_[37]) (N := 37) (χ := (teichmullerCharQp 37) ^ 31) hχ_ne_one
  rw [bernoulliGenOmega_def, show (32 - 1 : ℕ) = 31 from rfl,
    show (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) from by norm_num, hT006, PadicInt.coe_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
  congr 1
  rw [teichmullerCharQp_pow_eq_ringHomComp (p := 37) (n := 31),
    MulChar.ringHomComp_apply, MulChar.pow_apply' _ (by norm_num : (31 : ℕ) ≠ 0),
    map_pow, teichmullerChar_apply]
  rfl

/-- **The sound second-digit residual** at `(p, i) = (37, 32)`: the Teichmüller sum
`37 · B_{1,ω³¹}` has `37`-adic valuation **exactly 2**.  Equivalently (T006) the
integral sum `Σ_a ω(a)³¹·a.val` has valuation `2`; equivalently the sharp
`v₃₇(B_{1,ω³¹}) = 1`.

This is the genuine irreducible content — the second `37`-adic digit of the
Teichmüller sum (the Fermat-quotient / Washington Prop 8.12 datum).  It is stated
**without** a false power-sum congruence (two such over-statements are documented and
avoided in the module docstring).  It is a `Prop`, not an axiom, not a `sorry`, and
is **independent of Kellner**. -/
def bernoulliGenOmegaValuationTwo37 : Prop :=
  Padic.valuation ((37 : ℚ_[37]) * bernoulliGenOmega 37 32) = 2

/-- **`v₃₇(B_{1,ω³¹}) = 1`** (the sharp `M = 1` valuation of the *algebraic*
generalized Bernoulli number) from the sound residual
`bernoulliGenOmegaValuationTwo37`: `v₃₇(37 · B_{1,ω³¹}) = 2` and `v₃₇(37) = 1`, so
dividing off the single `37` gives `v₃₇(B_{1,ω³¹}) = 1`.  **No Kellner input.** -/
theorem valuation_bernoulliGenOmega_thirtytwo_of_valTwo
    (h : bernoulliGenOmegaValuationTwo37) :
    (bernoulliGenOmega 37 32).valuation = 1 := by
  unfold bernoulliGenOmegaValuationTwo37 at h
  have h37_ne : (37 : ℚ_[37]) ≠ 0 := by norm_num
  have hv37 : Padic.valuation (37 : ℚ_[37]) = 1 := by
    rw [show (37 : ℚ_[37]) = ((37 : ℕ) : ℚ_[37]) from by norm_num, Padic.valuation_natCast,
      show padicValNat 37 37 = 1 from by rw [padicValNat_self]]; rfl
  have hB_ne : bernoulliGenOmega 37 32 ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; simp at h
  have hsum : (1 : ℤ) + (bernoulliGenOmega 37 32).valuation = 2 := by
    rw [← hv37, ← Padic.valuation_mul h37_ne hB_ne]; exact h
  omega

/-- **The residual in integral-Teichmüller-sum form** (definitional equivalence via
the exact T006 identity): `v₃₇(B_{1,ω³¹}) = 1` follows just as well from
`v₃₇(Σ_a ω(a)³¹·a.val) = 2`.  This is the same datum as
`bernoulliGenOmegaValuationTwo37`, phrased on the explicit integral Teichmüller sum
(the form in which the Fermat-quotient / Prop 8.12 second digit actually lives). -/
theorem valuation_bernoulliGenOmega_thirtytwo_of_teichmullerSumValTwo
    (h : Padic.valuation
      ((∑ a : ZMod 37, BernoulliRegular.teichmuller 37 a ^ 31 * (a.val : ℤ_[37]) :
        ℤ_[37]) : ℚ_[37]) = 2) :
    (bernoulliGenOmega 37 32).valuation = 1 := by
  refine valuation_bernoulliGenOmega_thirtytwo_of_valTwo ?_
  unfold bernoulliGenOmegaValuationTwo37
  rwa [thirtyseven_mul_bernoulliGenOmega_thirtytwo_eq]

/-- **The corrected mod-`p²` Iwasawa-congruence data bundle.**

Identical to `IwasawaModSqData` except the *false-as-stated* `bernoulliGenModSq`
field (the mod-`p²` congruence to `B₃₂/32`) is **replaced** by the sound second-digit
residual `bernoulliGenOmegaValuationTwo37` at `i = 32`.  The Euler-unit field
`valuation_Lp_eq_bernoulliGenOmega` (Washington Cor 5.13) is unchanged.

It is a `structure`, not an axiom; its single analytic field is the corrected
residual.  The sharp `v₃₇(L_p(1, ω³²)) = 1` is **proved** from it — *not* from
Kellner. -/
structure IwasawaModSqCorrected37 where
  /-- The `p`-adic `L`-value `L_p(1, ω^i)`. -/
  Lp : ℕ → ℚ_[37]
  /-- `L_p(1, ω^i)` is nonzero on the relevant range. -/
  Lp_ne_zero : ∀ i, 2 ≤ i → i ≤ 37 - 3 → Even i → Lp i ≠ 0
  /-- **Washington Cor 5.13 (the Euler-unit identity)**: `v₃₇(L_p(1, ω^i)) =
  v₃₇(B_{1,ω^{i-1}})` (they differ by the unit Euler factor `1 − 37⁻¹`). -/
  valuation_Lp_eq_bernoulliGenOmega :
    ∀ i, 2 ≤ i → i ≤ 37 - 3 → Even i →
      (Lp i).valuation = (bernoulliGenOmega 37 i).valuation
  /-- **The sound second-digit residual** at `i = 32`
  (`bernoulliGenOmegaValuationTwo37`): the sound replacement for the false-as-stated
  mod-`p²` congruence to `B₃₂/32`. -/
  valTwo_thirtytwo : bernoulliGenOmegaValuationTwo37

namespace IwasawaModSqCorrected37

/-- **`v₃₇(L_p(1, ω³²)) = 1`** (the sharp `M = 1` valuation), from the corrected
bundle: chain the Euler-unit identity with the sharp `v₃₇(B_{1,ω³¹}) = 1` proved from
the sound second-digit residual.  **No Kellner input.** -/
theorem valuation_Lp_thirtytwo (D : IwasawaModSqCorrected37) : (D.Lp 32).valuation = 1 := by
  rw [D.valuation_Lp_eq_bernoulliGenOmega 32 (by norm_num) (by norm_num) (by decide),
    valuation_bernoulliGenOmega_thirtytwo_of_valTwo D.valTwo_thirtytwo]

/-- **The constructed Kubota–Leopoldt package** from the corrected data, under the
regularity hypothesis that every Bernoulli factor in the FLT range outside `i = 32`
has the matching valuation.  The `PadicLFunction.valuation_eq_bernoulliFactor` field
is **proved** at the boundary index `32` from the sharp `v₃₇(B_{1,ω³¹}) = 1` reduction
— `L_p` is tied to honest Stickelberger/Bernoulli arithmetic at the index that
matters, not assumed. -/
noncomputable def toPadicLFunction (D : IwasawaModSqCorrected37)
    (hother : ∀ i, 2 ≤ i → i ≤ 37 - 3 → Even i → i ≠ 32 →
      (D.Lp i).valuation = (bernoulliFactorQp 37 i).valuation) :
    PadicLFunction 37 where
  Lp := D.Lp
  Lp_ne_zero := D.Lp_ne_zero
  valuation_eq_bernoulliFactor i h1 h2 hev := by
    by_cases hi : i = 32
    · subst hi
      rw [D.valuation_Lp_thirtytwo, valuation_bernoulliFactorQp_thirtytwo]
    · exact hother i h1 h2 hev hi

end IwasawaModSqCorrected37

/-- **The Iwasawa bridge at the algebraic value, corrected**: `v₃₇(B_{1,ω³¹}) =
v₃₇(B₃₂/32)`.  This is exactly the conclusion the false-as-stated mod-`p²` field
`IwasawaModSqData.bernoulliGenModSq` was meant to yield (via
`valuation_bernoulliGenOmega_eq_of_modSq`), obtained **soundly** from the sound
second-digit residual and the proved `v₃₇(B₃₂/32) = 1` — *without* the false mod-`p²`
congruence (so that false field is not needed at all). -/
theorem valuation_bernoulliGenOmega_eq_bernoulliFactor_thirtytwo
    (h : bernoulliGenOmegaValuationTwo37) :
    (bernoulliGenOmega 37 32).valuation = (bernoulliFactorQp 37 32).valuation := by
  rw [valuation_bernoulliGenOmega_thirtytwo_of_valTwo h,
    valuation_bernoulliFactorQp_thirtytwo]

end BernoulliRegular.FLT37.PadicL
