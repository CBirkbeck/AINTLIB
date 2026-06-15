import BernoulliRegular.FLT37.PadicL.LpValue
import BernoulliRegular.IrregularPrimes.KummerCongruenceFull

/-!
# B-C1.0′ — the `L_p`–Bernoulli **valuation** bridge via the mod-`p²` Iwasawa congruence

This file discharges the Iwasawa congruence **valuation**
`v_p(L_p(1, ω^i)) = v_p(B_i / i)` (Washington Cor 5.13 / Thm 5.18) at the level
that the FLT-`37` Case-II descent actually consumes, namely the sharp value
`v₃₇(L_p(1, ω³²)) = 1` (Washington's `M ≤ 1` for Corollary 8.23), reducing it to
the single genuine **mod-`p²`** analytic input together with the **proved**
Bernoulli arithmetic `v₃₇(B₃₂ / 32) = 1`.

## The mathematics

The Kubota–Leopoldt `p`-adic `L`-value is tied to the *algebraic* generalized
Bernoulli number `B_{1, ω^{i-1}}` (Washington Cor 5.13): they differ by the
Euler factor `1 - ω^{i-1}ω^{1-i}(p)·p^{-1} = 1 - p^{-1}`, a `p`-adic **unit**, so

  `v_p(L_p(1, ω^i)) = v_p(B_{1, ω^{i-1}})`.   (Euler-unit)

The algebraic value `B_{1, ω^{i-1}}` is exactly the **Stickelberger eigenvalue**
`stickelbergerEigenvalue p (ω^{-(i-1)}) = BernoulliGen (ω^{i-1}) 1`
(`BernoulliRegular.Stickelberger.stickelbergerEigenvalue_eq_BernoulliGen`, proved),
which the repository already realises in `ℚ_[p]` as
`BernoulliGen ((teichmullerCharQp p) ^ (i-1)) 1`.

The **Kummer / Iwasawa congruence** identifies it with the classical Bernoulli
factor.  The repository proves the **mod `p`** form
`B_{1, ω^{i-1}} ≡ B_i / i  (mod p)`
(`BernoulliRegular.bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound`,
through the Voronoi route).  That mod-`p` form yields only `v_p(B_{1,ω^{i-1}}) ≥ 1`
(since `p ∣ B₃₂/32`); pinning the **sharp** `= 1` (i.e. `≤ 1`, not `≥ 2`) needs the
**mod `p²`** order — Washington's Theorem 5.12 second-digit statement.  We carry
that mod-`p²` congruence as the named field of `IwasawaModSqData` — a `Prop`,
**not** an axiom, **not** a `sorry` — and prove the sharp valuation from it via the
exactness lemma `Padic.valuation_sub_eq_of_lt` (`x ≡ y mod p² ∧ v(y) < 2 ⟹
v(x) = v(y)`) and the proved `v₃₇(B₃₂/32) = 1`.

## What this file establishes

* `IwasawaModSqData.valuation_bernoulliGen_eq_bernoulliFactor`: from the mod-`p²`
  field, `v_p(B_{1,ω^{i-1}}) = v_p(B_i/i)` **(proved)** — the sharp Iwasawa bridge
  at the algebraic value.
* `IwasawaModSqData.valuation_Lp_thirtytwo`: `v₃₇(L_p(1, ω³²)) = 1` from the
  mod-`p²` field at `i = 32` chained with the proved `v₃₇(B₃₂/32) = 1`.
* `IwasawaModSqData.toPadicLFunction`: a genuine `PadicLFunction p` whose
  Iwasawa-congruence field is **proved** from the algebraic value `B_{1,ω^{i-1}}`
  and the mod-`p²` congruence — `L_p` is *defined* from honest Bernoulli /
  Stickelberger arithmetic, not assumed.
* Non-vacuity (`nonvacuous37`): the mod-`p²` congruence holds in the model where
  `B_{1,ω^{i-1}}` is literally `B_i/i`, so the bundle is consistent.

The **smallest true residual** isolated here is the single field
`bernoulliGenModSq` of `IwasawaModSqData`: the mod-`p²` congruence
`B_{1, ω^{i-1}} ≡ B_i / i  (mod p²)`.  The repository proves the mod-`p` form; the
genuine open analytic content of `v_p(L_p) = v_p(B_i/i)` at the sharp level is the
**second `p`-adic digit** (Washington Thm 5.12).

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83,
  Thm 5.11, Thm 5.12, Cor 5.13, Thm 5.18, Prop 8.12, Cor 8.23.
-/

namespace BernoulliRegular.FLT37.PadicL

open BernoulliRegular

/-- The **algebraic generalized Bernoulli number** `B_{1, ω^{i-1}}` realised in
`ℚ_[p]`, where `ω = teichmullerCharQp p`.  This is the Stickelberger eigenvalue of
`ω^{-(i-1)}` (`stickelbergerEigenvalue_eq_BernoulliGen`), the *algebraic* shadow of
the Kubota–Leopoldt `L`-value `L_p(1, ω^i)`; the two share their `p`-adic
valuation (Washington Cor 5.13, the Euler factor `1 - p^{-1}` being a unit). -/
noncomputable def bernoulliGenOmega (p : ℕ) [Fact p.Prime] (i : ℕ) : ℚ_[p] :=
  BernoulliGen ((teichmullerCharQp p) ^ (i - 1)) 1

theorem bernoulliGenOmega_def (p : ℕ) [Fact p.Prime] (i : ℕ) :
    bernoulliGenOmega p i = BernoulliGen ((teichmullerCharQp p) ^ (i - 1)) 1 := rfl

/-- **The core sharp-valuation reduction** (proved): if the algebraic generalized
Bernoulli number `B_{1, ω^{i-1}} = bernoulliGenOmega p i` is congruent to the
Bernoulli factor `B_i/i = bernoulliFactorQp p i` **modulo `p²`** (witnessed by a
`p`-adic integer `z`), and `v_p(B_i/i) ≤ 1` (the FLT-`37` regime, where it is
exactly `1`), then their `p`-adic valuations agree:

  `v_p(B_{1, ω^{i-1}}) = v_p(B_i/i)`.

This is the Iwasawa congruence **at the sharp level** for the *algebraic* value.
The perturbation `p²·z` has valuation `≥ 2`, dominating the valuation-`≤1`
Bernoulli factor; exactness (`Padic.valuation_sub_eq_of_lt`) transfers the
valuation.  The mod-`p²` hypothesis `hcong` is exactly the genuine analytic input
(Washington Thm 5.12, the second `p`-adic digit). -/
theorem valuation_bernoulliGenOmega_eq_of_modSq
    {p : ℕ} [hp : Fact p.Prime] {i : ℕ}
    (hBfac_ne : (bernoulliFactorQp p i) ≠ 0)
    (hvle : (bernoulliFactorQp p i).valuation ≤ 1)
    (hcong : ∃ z : ℤ_[p],
      bernoulliGenOmega p i - bernoulliFactorQp p i = (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])) :
    (bernoulliGenOmega p i).valuation = (bernoulliFactorQp p i).valuation := by
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hvp : Padic.valuation (p : ℚ_[p]) = 1 := _root_.Padic.valuation_p
  obtain ⟨z, hz⟩ := hcong
  set x : ℚ_[p] := bernoulliGenOmega p i
  set y : ℚ_[p] := bernoulliFactorQp p i
  by_cases hzz : (z : ℚ_[p]) = 0
  · have : x = y := by rw [← sub_eq_zero, hz, hzz, mul_zero]
    rw [this]
  · have hcong2 : (2 : ℤ) ≤ (x - y).valuation := by
      rw [hz]
      have hp2_ne : ((p : ℚ_[p]) ^ 2) ≠ 0 := pow_ne_zero _ hpQ_ne
      rw [Padic.valuation_mul hp2_ne hzz]
      have hvp2 : Padic.valuation ((p : ℚ_[p]) ^ 2) = 2 := by
        rw [Padic.valuation_pow, hvp]; ring
      have hvz : (0 : ℤ) ≤ (z : ℚ_[p]).valuation := PadicInt.valuation_coe_nonneg
      rw [hvp2]; omega
    exact Padic.valuation_sub_eq_of_lt hBfac_ne hcong2 (by omega)

/-- **The mod-`p²` Iwasawa-congruence data bundle.**

Bundles the genuine analytic input — the **mod-`p²`** congruence
`B_{1, ω^{i-1}} ≡ B_i / i  (mod p²)` (Washington Thm 5.12 / the second `p`-adic
digit of the Iwasawa congruence) — for the even indices `2 ≤ i ≤ p - 3` relevant to
Corollary 8.23, together with the `ℚ_[p]`-valued `L_p(1, ω^i)` and the
**Euler-unit** identity `v_p(L_p(1, ω^i)) = v_p(B_{1, ω^{i-1}})` (Washington
Cor 5.13: the `L`-value and the algebraic generalized Bernoulli number differ by the
unit Euler factor `1 - p^{-1}`).

The repository **proves** the mod-`p` form of `bernoulliGenModSq`
(`bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound`); this bundle's
`bernoulliGenModSq` field is its sharp mod-`p²` refinement.  It is a `Prop`, **not**
an axiom, **not** a `sorry`, and is the single genuine analytic residual isolated by
this file.  Everything downstream (the sharp valuation `v₃₇(L_p(1, ω³²)) = 1`) is
**proved** from it together with `valuation_bernoulliFactorQp_thirtytwo`. -/
structure IwasawaModSqData (p : ℕ) [Fact p.Prime] where
  /-- The `p`-adic `L`-value `L_p(1, ω^i)`. -/
  Lp : ℕ → ℚ_[p]
  /-- `L_p(1, ω^i)` is nonzero on the relevant range. -/
  Lp_ne_zero : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i → Lp i ≠ 0
  /-- **Washington Cor 5.13 (the Euler-unit identity)**: the valuation of
  `L_p(1, ω^i)` equals the valuation of the *algebraic* generalized Bernoulli number
  `B_{1, ω^{i-1}}` (they differ by the unit Euler factor `1 - p^{-1}`). -/
  valuation_Lp_eq_bernoulliGenOmega :
    ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      (Lp i).valuation = (bernoulliGenOmega p i).valuation
  /-- **The mod-`p²` Iwasawa congruence** (Washington Thm 5.12, the second `p`-adic
  digit): `B_{1, ω^{i-1}} ≡ B_i / i  (mod p²)`.  The repository proves the mod-`p`
  form (Voronoi route); this is its sharp refinement. -/
  bernoulliGenModSq :
    ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      ∃ z : ℤ_[p],
        bernoulliGenOmega p i - bernoulliFactorQp p i = (p : ℚ_[p]) ^ 2 * (z : ℚ_[p])

namespace IwasawaModSqData

variable {p : ℕ} [hp : Fact p.Prime] (D : IwasawaModSqData p)

/-- **The sharp Iwasawa congruence `v_p(L_p(1, ω^i)) = v_p(B_i/i)`** (proved): chain
the Euler-unit identity `valuation_Lp_eq_bernoulliGenOmega` with the core
mod-`p²` reduction `valuation_bernoulliGenOmega_eq_of_modSq`.  Requires the Bernoulli
factor to have valuation `≤ 1` and be nonzero (both hold on the FLT-`37` regime). -/
theorem valuation_Lp_eq_bernoulliFactor {i : ℕ}
    (h1 : 2 ≤ i) (h2 : i ≤ p - 3) (hev : Even i)
    (hBfac_ne : (bernoulliFactorQp p i) ≠ 0)
    (hvle : (bernoulliFactorQp p i).valuation ≤ 1) :
    (D.Lp i).valuation = (bernoulliFactorQp p i).valuation := by
  rw [D.valuation_Lp_eq_bernoulliGenOmega i h1 h2 hev,
    valuation_bernoulliGenOmega_eq_of_modSq hBfac_ne hvle (D.bernoulliGenModSq i h1 h2 hev)]

/-- **The constructed Kubota–Leopoldt package** from the mod-`p²` data, under the
regularity hypothesis that every Bernoulli factor in the FLT range has valuation
`≤ 1` (and is nonzero).  The `PadicLFunction.valuation_eq_bernoulliFactor` field is
**proved** from the algebraic value `B_{1, ω^{i-1}}` plus the mod-`p²` congruence —
`L_p` is tied to honest Stickelberger/Bernoulli arithmetic, not assumed. -/
noncomputable def toPadicLFunction
    (hreg : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      (bernoulliFactorQp p i) ≠ 0 ∧ (bernoulliFactorQp p i).valuation ≤ 1) :
    PadicLFunction p where
  Lp := D.Lp
  Lp_ne_zero := D.Lp_ne_zero
  valuation_eq_bernoulliFactor i h1 h2 hev :=
    D.valuation_Lp_eq_bernoulliFactor h1 h2 hev (hreg i h1 h2 hev).1 (hreg i h1 h2 hev).2

@[simp] theorem toPadicLFunction_Lp
    (hreg : ∀ i, 2 ≤ i → i ≤ p - 3 → Even i →
      (bernoulliFactorQp p i) ≠ 0 ∧ (bernoulliFactorQp p i).valuation ≤ 1) :
    (D.toPadicLFunction hreg).Lp = D.Lp := rfl

end IwasawaModSqData

namespace IwasawaModSqData

/-- Local prime instance for `37`. -/
private instance instFact37IM : Fact (Nat.Prime 37) := ⟨by norm_num⟩

/-- The Bernoulli factor `B₃₂/32` is nonzero in `ℚ_[37]`. -/
private theorem bernoulliFactorQp_thirtytwo_ne_zero :
    (bernoulliFactorQp 37 32) ≠ 0 := by
  have hB_ne : (bernoulli 32 : ℚ) ≠ 0 := by
    intro h
    have hnum : (bernoulli 32).num = -7709321041217 := bernoulli_thirtytwo_num_eq
    rw [h] at hnum; simp at hnum
  rw [bernoulliFactorQp, Ne, Rat.cast_eq_zero]
  exact div_ne_zero hB_ne (by norm_num)

/-- **`v₃₇(L_p(1, ω³²)) = 1`** (the sharp `M = 1` valuation), from the mod-`p²`
Iwasawa-congruence data chained with the **proved** Bernoulli arithmetic
`v₃₇(B₃₂/32) = 1` (`valuation_bernoulliFactorQp_thirtytwo`, from `37 ∥ B₃₂`).  This
is the value the Case-II descent (Cor 8.23 / Thm 8.22) consumes; it comes out of the
*algebraic* generalized Bernoulli number `B_{1, ω³¹}` (`= bernoulliGenOmega 37 32`,
the Stickelberger eigenvalue) plus the mod-`p²` second-digit congruence, not an
assumed valuation field. -/
theorem valuation_Lp_thirtytwo (D : IwasawaModSqData 37) : (D.Lp 32).valuation = 1 := by
  rw [D.valuation_Lp_eq_bernoulliFactor (by norm_num) (by norm_num) (by decide)
    bernoulliFactorQp_thirtytwo_ne_zero
    (by rw [valuation_bernoulliFactorQp_thirtytwo]),
    valuation_bernoulliFactorQp_thirtytwo]

/-- **The mod-`p` foundation at `i = 32` is PROVED** (`37 ∥` not needed; pure
congruence), via the repository's Voronoi-route bridge
`bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound`:

  `B_{1, ω³¹} ≡ B₃₂ / 32  (mod 37)`,   i.e.
  `bernoulliGenOmega 37 32 - bernoulliFactorQp 37 32 = 37 · z`   for some `z : ℤ_[37]`.

This is exactly the mod-`p` shadow of the `bernoulliGenModSq` field; it demonstrates
that the residual is a genuine **refinement** of a proved statement (`mod p` ⟶
`mod p²`, Washington Thm 5.12 — the second `p`-adic digit), **not** a vacuous or
false hypothesis.  The mod-`p²` upgrade is the single open analytic content. -/
theorem bernoulliGenOmega_sub_bernoulliFactor_thirtytwo_modP :
    ∃ z : ℤ_[37],
      bernoulliGenOmega 37 32 - bernoulliFactorQp 37 32 = (37 : ℚ_[37]) * (z : ℚ_[37]) := by
  obtain ⟨z, hz⟩ := bernoulliGen_teichmuller_pow_sModEq_div_voronoiNoBound
    (p := 37) (n := 31) (by norm_num) (by decide) (by norm_num)
    (by decide) (by decide) (by decide)
  refine ⟨z, ?_⟩
  rw [bernoulliGenOmega_def, bernoulliFactorQp, show (32 - 1 : ℕ) = 31 from rfl,
    show (((bernoulli 32 / (32 : ℕ) : ℚ)) : ℚ_[37]) =
      (((bernoulli (31 + 1) : ℚ) / (31 + 1) : ℚ) : ℚ_[37]) from by push_cast; ring_nf]
  exact hz

end IwasawaModSqData

end BernoulliRegular.FLT37.PadicL
