module

public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.CyclotomicUnitTwist

/-!
# Aggregate σ_a-twist for `pollaczekUnit` (LV005c1b — partial)

Distribute the standard cyclotomic Galois automorphism `σ_a :=
cyclotomicSigmaOfUnit p K a` over the Pollaczek product
`pollaczekUnit p K i = ∏_b ((1-ζ^b)/(1-ζ))^{b^{p-1-i}}` (over the
half-range `b ∈ {1, …, (p-1)/2}`), using the factor-wise σ-twist from
LV005c1a (`cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_cyclotomicUnit`).

This file ships the **first stage** of LV005c1b's chain:

  `σ_a(pollaczekUnit p K i : 𝓞 K) · cyclotomicUnit p K (a : ZMod p).val ^ S =
   ∏_{b ∈ Ico 1 ((p-1)/2 + 1)} cyclotomicUnit p K (((a : ZMod p) * b).val)
                                  ^ (b ^ (p - 1 - i))`,

where `S = ∑_b b^{p-1-i}` is the half-range exponent sum.

The remaining stages (half-range pair-up reducing
`cyclotomicUnit p K (((a · b).val)` back to half-range; reindex; absorb
exponent discrepancy mod `p`; Fermat reduction `(a⁻¹.val)^E ≡ a^i (mod p)`)
build the full eigenvalue identity
`σ_a(pollaczekUnit i) ≡ pollaczekUnit i ^{a^i} (mod p-th powers)`.
Those stages are **not yet shipped here**; they require the half-range
pair-up symmetry analogous to `pollaczekR_split_reindex` /
`pollaczekR_half_range_factorisation` (LV004e) at the K-side
`cyclotomicUnit` level. Track in LV005c1b's residual.

## Main result

* `cyclotomicSigmaOfUnit_smul_pollaczekUnit_aggregate` — the aggregate
  σ-twist in the substitution form (no inversion, no half-range
  pair-up yet).

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), Lemma 8.2 / Lemma 8.4 (p. 156); proof of Cor 8.19 (p. 158).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Finset
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section AggregateTwist

/-- **Pollaczek-product unfolding**: the underlying ring-element form of
`pollaczekUnit p K i` is the Finset.Ico product of cyclotomic units
raised to the Pollaczek exponents. -/
theorem pollaczekUnit_val_eq_prod (i : ℕ) :
    ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) =
      ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K b ^ (b ^ (p - 1 - i)) := by
  unfold pollaczekUnit
  rw [Units.coe_prod]
  rw [show (∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        ((pollaczekFactor p K b.2 ^ (b.1 : ℕ) ^ (p - 1 - i) :
            (𝓞 K)ˣ) : 𝓞 K)) =
      ∏ b ∈ (Finset.Ico 1 ((p - 1) / 2 + 1)).attach,
        cyclotomicUnit p K b.1 ^ (b.1 : ℕ) ^ (p - 1 - i) by
    refine Finset.prod_congr rfl ?_
    intro b _
    rw [Units.val_pow_eq_pow_val, pollaczekFactor_val]]
  rw [Finset.prod_attach (Finset.Ico 1 ((p - 1) / 2 + 1))
    (fun b => cyclotomicUnit p K b ^ (b ^ (p - 1 - i)))]

/-- **Aggregate σ_a-twist for `pollaczekUnit` (substitution form)**:
applying σ_a to the Pollaczek product, multiplied by the ζ-prefactor
`cyclotomicUnit p K (a : ZMod p).val ^ S`, yields the substituted
product over `cyclotomicUnit ((a · b).val)`:

  `σ_a(pollaczekUnit i : 𝓞 K) ·
    cyclotomicUnit p K (a : ZMod p).val ^ (∑ b, b^{p-1-i}) =
   ∏_{b ∈ half-range} cyclotomicUnit p K (((a : ZMod p) * b).val)
                       ^ (b^{p-1-i}).`

This is **stage 1** of LV005c1b's full eigenvalue chain. The remaining
stages reorganise the substituted product back into a
`pollaczekUnit ^ {a^i}` form mod `p`-th powers (half-range pair-up,
reindex, Fermat reduction); those are deferred to subsequent work. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_aggregate
    (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
      cyclotomicUnit p K ((a : ZMod p).val) ^
        (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
      ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K (((a : ZMod p) * b).val) ^ (b ^ (p - 1 - i)) := by
  set σ : 𝓞 K →+* 𝓞 K :=
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
      (cyclotomicSigmaOfUnit (p := p) K a)
  -- Distribute σ over pollaczekUnit's product.
  rw [pollaczekUnit_val_eq_prod]
  rw [show cyclotomicSigmaOfUnit (p := p) K a •
        ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K b ^ (b ^ (p - 1 - i)) =
      σ (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K b ^ (b ^ (p - 1 - i))) from rfl]
  rw [map_prod σ]
  simp only [map_pow]
  -- Goal:
  -- (∏ b, σ(cyclotomicUnit b) ^ (b^E)) · cyclotomicUnit a.val ^ S =
  --   ∏ b, cyclotomicUnit ((a · b).val) ^ (b^E)
  -- where S = ∑ b^E.

  -- Move cyclotomicUnit a.val^S inside the product:
  --   cyclotomicUnit a.val^S = ∏ cyclotomicUnit a.val^(b^E).
  rw [show cyclotomicUnit p K ((a : ZMod p).val) ^
        (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
      ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K ((a : ZMod p).val) ^ (b ^ (p - 1 - i)) by
    rw [← Finset.prod_pow_eq_pow_sum]]
  -- Now: ∏ σ(cyclotomicUnit b)^E · ∏ cyclotomicUnit a.val^E =
  --      ∏ cyclotomicUnit ((a · b).val)^E
  -- Combine the two products on the LHS into one ∏ (σ(c_b) · c_{a.val})^E.
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro b _
  -- Per-factor goal: σ(cyclotomicUnit b)^E · cyclotomicUnit a.val^E =
  --                   cyclotomicUnit ((a · b).val)^E
  -- Apply LV005c1a via mul_pow.
  rw [← mul_pow]
  congr 1
  -- Per-factor: σ(cyclotomicUnit b) · cyclotomicUnit a.val =
  --             cyclotomicUnit ((a · b).val).
  -- This is exactly LV005c1a (with the σ-action expressed as MulSemiringAction.toRingHom).
  change (cyclotomicSigmaOfUnit (p := p) K a • cyclotomicUnit p K b) *
      cyclotomicUnit p K ((a : ZMod p).val) =
    cyclotomicUnit p K (((a : ZMod p) * b).val)
  exact cyclotomicSigmaOfUnit_smul_cyclotomicUnit_mul_cyclotomicUnit p K a b

end AggregateTwist

section PairUp

/-- **Cyclotomic-unit pair-up identity**: for `1 ≤ c < p` (so `(p - c)` is
also in `Finset.Ico 1 p`),

  `ζ^c · cyclotomicUnit p K (p - c) = -cyclotomicUnit p K c` in `𝓞 K`.

Equivalently `cyclotomicUnit p K (p - c) = -ζ^{-c} · cyclotomicUnit p K c`,
expressed in the inversion-free multiplicative form.

Proof: multiply by `(ζ - 1)`. The LHS becomes
`ζ^c · (ζ^{p-c} - 1) = ζ^p - ζ^c = 1 - ζ^c = -(ζ^c - 1)`. The RHS becomes
`-(ζ - 1) · cyclotomicUnit c = -(ζ^c - 1)`. Cancel `(ζ - 1) ≠ 0`. -/
theorem zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg
    (c : ℕ) (hc : c ≤ p) :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ c * cyclotomicUnit p K (p - c) =
      -cyclotomicUnit p K c := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  have hζ_sub_one_ne_zero : (ζ - 1 : 𝓞 K) ≠ 0 :=
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
  -- ζ^p = 1.
  have hζ_p : ζ ^ p = 1 := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  -- Multiply both sides by (ζ - 1) and cancel.
  refine mul_right_cancel₀ hζ_sub_one_ne_zero ?_
  calc ζ ^ c * cyclotomicUnit p K (p - c) * (ζ - 1)
      = ζ ^ c * ((ζ - 1) * cyclotomicUnit p K (p - c)) := by ring
    _ = ζ ^ c * (ζ ^ (p - c) - 1) := by
          rw [zeta_sub_one_mul_cyclotomicUnit]
    _ = ζ ^ c * ζ ^ (p - c) - ζ ^ c := by ring
    _ = ζ ^ p - ζ ^ c := by
          rw [← pow_add, Nat.add_sub_cancel' hc]
    _ = 1 - ζ ^ c := by rw [hζ_p]
    _ = -(ζ ^ c - 1) := by ring
    _ = -((ζ - 1) * cyclotomicUnit p K c) := by
          rw [zeta_sub_one_mul_cyclotomicUnit]
    _ = -cyclotomicUnit p K c * (ζ - 1) := by ring

/-- **Inversion-free pair-up corollary**: for `1 ≤ d ≤ p`,
`cyclotomicUnit p K d = -ζ^d · cyclotomicUnit p K (p - d)` in `𝓞 K`.

Derived from `zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg` by multiplying
through by `ζ^d` and using `ζ^p = 1` to collapse `ζ^d · ζ^{p-d} = 1`. -/
theorem cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub
    (d : ℕ) (hd : d ≤ p) :
    cyclotomicUnit p K d =
      -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ d *
        cyclotomicUnit p K (p - d) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set ζ : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  have hζ_p : ζ ^ p = 1 := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  -- Apply zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg with c = p - d.
  have h := zeta_pow_mul_cyclotomicUnit_p_sub_eq_neg
    (p := p) (K := K) (p - d) (Nat.sub_le _ _)
  -- h : ζ^{p-d} · cyclotomicUnit (p - (p-d)) = -cyclotomicUnit (p-d).
  -- p - (p - d) = d (using d ≤ p).
  rw [show p - (p - d) = d from Nat.sub_sub_self hd] at h
  -- h : ζ^{p-d} · cyclotomicUnit d = -cyclotomicUnit (p-d).
  -- Multiply both sides by ζ^d, use ζ^d · ζ^{p-d} = ζ^p = 1.
  have h_pow : ζ ^ d * ζ ^ (p - d) = 1 := by
    rw [← pow_add, Nat.add_sub_cancel' hd, hζ_p]
  calc cyclotomicUnit p K d
      = (ζ ^ d * ζ ^ (p - d)) * cyclotomicUnit p K d := by rw [h_pow, one_mul]
    _ = ζ ^ d * (ζ ^ (p - d) * cyclotomicUnit p K d) := by ring
    _ = ζ ^ d * (-cyclotomicUnit p K (p - d)) := by rw [h]
    _ = -ζ ^ d * cyclotomicUnit p K (p - d) := by ring

end PairUp

section HalfRangeReduction

/-- **Per-term half-range reduction**: each factor
`cyclotomicUnit p K (((a : ZMod p) * b).val) ^ (b ^ E)` rewrites uniformly
as

  `(-1)^{b^E} · ζ^{(a · b).val · b^E} · cyclotomicUnit p K (p - (a · b).val)^{b^E}`,

regardless of whether `(a · b).val` is in the lower or upper half. (For
the lower half we accept the "swap" `cyclotomicUnit d = -ζ^d · cyclotomicUnit (p-d)`,
yielding an upper-half index `p - d`.)

This is **stage 3** of LV005c1b. The next stages partition the half-range
into the b's whose `(a · b).val` is in the lower half (where the swap is
"unnecessary" but valid) versus the upper half, and reindex to bring all
factors back into the original half-range form. -/
theorem cyclotomicUnit_pow_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub_pow
    (a : (ZMod p)ˣ) (b : ℕ) (E : ℕ) (hb_lt : ((a : ZMod p) * b).val ≤ p) :
    cyclotomicUnit p K (((a : ZMod p) * b).val) ^ (b ^ E) =
      (-1) ^ (b ^ E) *
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (((a : ZMod p) * b).val) *
          cyclotomicUnit p K (p - ((a : ZMod p) * b).val)) ^ (b ^ E) := by
  rw [cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub p K
      (((a : ZMod p) * b).val) hb_lt,
    show -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (((a : ZMod p) * b).val) *
        cyclotomicUnit p K (p - ((a : ZMod p) * b).val) =
      (-1) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (((a : ZMod p) * b).val) *
        cyclotomicUnit p K (p - ((a : ZMod p) * b).val)) by ring,
    mul_pow]

/-- **Aggregate half-range reduction**: applying the per-term swap
identity uniformly over the Pollaczek product (independently of
upper/lower half), the substituted form rewrites as

  `∏_b cyclotomicUnit p K ((a · b).val)^{b^E} =
    (-1)^{∑ b^E} · ∏_b ζ^{(a · b).val · b^E} ·
      ∏_b cyclotomicUnit p K (p - (a · b).val)^{b^E}`.

Each factor on the RHS now uses the index `p - (a · b).val`, which lies
in `{1, …, p-1}` (still potentially in the upper half). The next stage
will pair-up these indices via the unit-bijection `b ↦ b'` mapping the
half-range to itself such that `b' = (a · b).val` if `(a · b).val ≤ (p-1)/2`
or `b' = p - (a · b).val` otherwise.

This intermediate form is the "swap-uniform" stage 3 of LV005c1b. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_swap_uniform
    (a : (ZMod p)ˣ) (i : ℕ) :
    ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K (((a : ZMod p) * b).val) ^ (b ^ (p - 1 - i)) =
      (-1) ^ (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) *
        (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
            (((a : ZMod p) * b).val * b ^ (p - 1 - i))) *
        ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K (p - ((a : ZMod p) * b).val) ^ (b ^ (p - 1 - i)) := by
  -- For each b, ((a · b).val) < p, so ≤ p as required by per-term lemma.
  have h_le : ∀ b : ℕ, ((a : ZMod p) * b).val ≤ p := fun b =>
    Nat.le_of_lt ((((a : ZMod p) * b)).val_lt)
  -- Apply the per-term swap to each factor, then aggregate.
  rw [show ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K (((a : ZMod p) * b).val) ^ (b ^ (p - 1 - i)) =
      ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (-1) ^ (b ^ (p - 1 - i)) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (((a : ZMod p) * b).val) *
            cyclotomicUnit p K (p - ((a : ZMod p) * b).val)) ^ (b ^ (p - 1 - i))
      from Finset.prod_congr rfl fun b _ => by
        exact cyclotomicUnit_pow_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub_pow
          p K a b (p - 1 - i) (h_le b)]
  -- Now distribute the product over (-1)^{...} · (ζ^{...} · cycU(p - ...))^{...}.
  rw [Finset.prod_mul_distrib]
  rw [show ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (-1 : 𝓞 K) ^ (b ^ (p - 1 - i)) =
      (-1) ^ (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i))
      from Finset.prod_pow_eq_pow_sum
        (Finset.Ico 1 ((p - 1) / 2 + 1))
        (fun b => b ^ (p - 1 - i)) (-1)]
  -- Distribute (ζ^{...} · cycU)^{exp} = ζ^{... · exp} · cycU^{exp}.
  rw [show ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (((a : ZMod p) * b).val) *
          cyclotomicUnit p K (p - ((a : ZMod p) * b).val)) ^ (b ^ (p - 1 - i)) =
      (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
            (((a : ZMod p) * b).val * b ^ (p - 1 - i))) *
        ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K (p - ((a : ZMod p) * b).val) ^ (b ^ (p - 1 - i))
      from by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [mul_pow, ← pow_mul]]
  ring

end HalfRangeReduction

section HalfRangeBijection

/-- **Half-range image function**: for `a ∈ (ZMod p)ˣ` and `b : ℕ`,
returns the half-range representative of `(a · b)` modulo `p`. Maps the
half-range `{1, …, (p-1)/2}` to itself bijectively when `a` is a unit and
`p` is odd. -/
def halfReduce (a : (ZMod p)ˣ) (b : ℕ) : ℕ :=
  if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
    ((a : ZMod p) * (b : ZMod p)).val
  else p - ((a : ZMod p) * (b : ZMod p)).val

/-- **`halfReduce` lands in the half-range**: for `b ∈ Ico 1 ((p-1)/2 + 1)`,
`a` a unit, and `p` odd, `halfReduce p a b ∈ Ico 1 ((p-1)/2 + 1)`. -/
theorem halfReduce_mem_half_range (hp_odd : p ≠ 2) (a : (ZMod p)ˣ) {b : ℕ}
    (hb : b ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) :
    halfReduce p a b ∈ Finset.Ico 1 ((p - 1) / 2 + 1) := by
  rw [Finset.mem_Ico] at hb ⊢
  obtain ⟨hb_pos, hb_le⟩ := hb
  have hp_pos : 0 < p := hp.out.pos
  -- p is odd, so (p-1)/2 + (p-1)/2 = p - 1 (odd-decomposition).
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp_odd
  have hp_div2 : (p - 1) / 2 = k := by omega
  have hb_lt_p : b < p := by omega
  -- (b : ZMod p) ≠ 0 because b ∈ {1, ..., p-1}.
  have hb_zmod_ne_zero : ((b : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have : ((b : ℕ) : ZMod p).val = 0 := by rw [h]; exact ZMod.val_zero
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt_p] at this
    omega
  -- (a · b) is a unit, so its val is ≥ 1.
  have h_ab_val_pos : 1 ≤ ((a : ZMod p) * (b : ZMod p)).val := by
    have h_ne_zero : (a : ZMod p) * (b : ZMod p) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h' | h'
      · exact (a.ne_zero) h'
      · exact hb_zmod_ne_zero h'
    exact ZMod.val_pos.mpr h_ne_zero
  have h_ab_val_lt : ((a : ZMod p) * (b : ZMod p)).val < p :=
    ((a : ZMod p) * (b : ZMod p)).val_lt
  unfold halfReduce
  split_ifs with h
  · exact ⟨h_ab_val_pos, by omega⟩
  · refine ⟨by omega, ?_⟩
    -- Goal: p - (a · b).val < (p - 1) / 2 + 1.
    -- (a · b).val > (p-1)/2, so (a · b).val ≥ (p-1)/2 + 1 = k + 1.
    -- p - (a · b).val ≤ p - k - 1 = (since p = 2k+1) k = (p-1)/2.
    -- So p - (a · b).val ≤ (p-1)/2, i.e., < (p-1)/2 + 1. ✓
    omega

/-- Auxiliary: `(a⁻¹).val * a.val = 1` in `ZMod p`. -/
theorem unit_inv_val_mul_val (a : (ZMod p)ˣ) :
    ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * ((a : (ZMod p)ˣ) : ZMod p) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- **`halfReduce` round-trip**: for `b ∈ Ico 1 ((p-1)/2 + 1)`, `a` a unit,
and `p` odd, applying `halfReduce` with `a` then `a⁻¹` recovers `b`. -/
theorem halfReduce_round_trip (hp_odd : p ≠ 2) (a : (ZMod p)ˣ) {b : ℕ}
    (hb : b ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) :
    halfReduce p a⁻¹ (halfReduce p a b) = b := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [Finset.mem_Ico] at hb
  obtain ⟨hb_pos, hb_le⟩ := hb
  have hp_pos : 0 < p := hp.out.pos
  obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp_odd
  have hp_div2 : (p - 1) / 2 = k := by omega
  have hb_lt_p : b < p := by omega
  have hb_zmod_ne_zero : ((b : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have : ((b : ℕ) : ZMod p).val = 0 := by rw [h]; exact ZMod.val_zero
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt_p] at this
    omega
  have hb_val : ((b : ℕ) : ZMod p).val = b := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hb_lt_p]
  have h_ab_ne : (a : ZMod p) * (b : ZMod p) ≠ 0 := fun h => by
    rcases mul_eq_zero.mp h with h' | h'
    · exact a.ne_zero h'
    · exact hb_zmod_ne_zero h'
  have h_ab_val_pos : 1 ≤ ((a : ZMod p) * (b : ZMod p)).val :=
    ZMod.val_pos.mpr h_ab_ne
  have h_ab_val_lt : ((a : ZMod p) * (b : ZMod p)).val < p :=
    ((a : ZMod p) * (b : ZMod p)).val_lt
  -- Helper: simplify ((a⁻¹) · (((a · b).val : ZMod p)) : ZMod p) = (b : ZMod p)
  -- after natCast_val + cast_id, then unit-inverse cancellation.
  have h_simplify_α : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) *
      ((((a : ZMod p) * (b : ZMod p)).val : ℕ) : ZMod p) = (b : ZMod p) := by
    rw [ZMod.natCast_val, ZMod.cast_id, ← mul_assoc, unit_inv_val_mul_val, one_mul]
  have h_simplify_β : ((a⁻¹ : (ZMod p)ˣ) : ZMod p) *
      (((p - ((a : ZMod p) * (b : ZMod p)).val) : ℕ) : ZMod p) = -(b : ZMod p) := by
    have h_cast :
        (((p - ((a : ZMod p) * (b : ZMod p)).val) : ℕ) : ZMod p) =
          -((a : ZMod p) * (b : ZMod p)) := by
      rw [Nat.cast_sub (Nat.le_of_lt h_ab_val_lt), ZMod.natCast_self, ZMod.natCast_val,
        ZMod.cast_id]
      ring
    rw [h_cast, mul_neg, ← mul_assoc, unit_inv_val_mul_val, one_mul]
  have h_val_eq : (((a⁻¹ : (ZMod p)ˣ) : ZMod p) *
      (((p - ((a : ZMod p) * (b : ZMod p)).val) : ℕ) : ZMod p)).val = p - b := by
    rw [h_simplify_β, ZMod.neg_val]
    simp [hb_zmod_ne_zero, hb_val]
  unfold halfReduce
  split_ifs with h_outer h_inner h_inner
  · -- Case α (lower-half) → if-branch: result = (a⁻¹ · h).val = b. ✓
    rw [h_simplify_α]; exact hb_val
  · -- Case α (lower-half) → else-branch: contradicts h_simplify_α + b ≤ k.
    exfalso
    apply h_inner
    rw [h_simplify_α, hb_val]; omega
  · -- Case β (upper-half) → if-branch: contradicts h_simplify_β giving p - b > k.
    exfalso
    rw [h_val_eq] at h_inner
    omega
  · -- Case β (upper-half) → else-branch: result = p - (a⁻¹ · h).val = b. ✓
    rw [h_val_eq]; omega

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **Reindex via `halfReduce` bijection**: for any function `f : ℕ → ℕ → 𝓞 K`,
the half-range product `∏_b f(b, halfReduce p a b)` equals
`∏_{b'} f(halfReduce p a⁻¹ b', b')` (after relabelling `b' = halfReduce p a b`).

This is the architectural step used to reorganise the σ-twisted Pollaczek
product after stage 3 (swap-uniform) so that all `cyclotomicUnit` indices
land in the half-range. -/
theorem halfReduce_prod_reindex (hp_odd : p ≠ 2) (a : (ZMod p)ˣ)
    (f : ℕ → ℕ → 𝓞 K) :
    ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), f b (halfReduce p a b) =
      ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1), f (halfReduce p a⁻¹ b') b' := by
  refine Finset.prod_nbij'
    (fun b => halfReduce p a b)
    (fun b' => halfReduce p a⁻¹ b')
    ?_ ?_ ?_ ?_ ?_
  · intro b hb; exact halfReduce_mem_half_range p hp_odd a hb
  · intro b' hb'; exact halfReduce_mem_half_range p hp_odd a⁻¹ hb'
  · intro b hb; exact halfReduce_round_trip p hp_odd a hb
  · intro b' hb'
    -- halfReduce p a (halfReduce p a⁻¹ b') = b'.
    have h := halfReduce_round_trip p hp_odd a⁻¹ hb'
    rw [inv_inv] at h
    exact h
  · intro b hb
    -- f b (halfReduce p a b) = f (halfReduce p a⁻¹ (halfReduce p a b)) (halfReduce p a b).
    rw [halfReduce_round_trip p hp_odd a hb]

end HalfRangeBijection

section PerTermSwap

/-- **Per-term swap identity (if-then-else form)**: for each `b` in the
half-range, `cyclotomicUnit p K ((a · b).val)` equals
`cyclotomicUnit p K (halfReduce p a b)` modulo a sign `±1` and a
ζ-prefactor that's nontrivial only when `(a · b).val` is in the upper half. -/
theorem cyclotomicUnit_eq_if_upper_pair_up (a : (ZMod p)ˣ) (b : ℕ) :
    cyclotomicUnit p K (((a : ZMod p) * (b : ZMod p)).val) =
      (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then (1 : 𝓞 K)
       else -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
              (((a : ZMod p) * (b : ZMod p)).val)) *
        cyclotomicUnit p K (halfReduce p a b) := by
  unfold halfReduce
  by_cases h : ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2
  · simp [h]
  · simp only [h, if_false]
    -- Goal: cyclotomicUnit ((a · b).val) =
    --   -ζ^{(a · b).val} · cyclotomicUnit (p - (a · b).val).
    have h_le : ((a : ZMod p) * (b : ZMod p)).val ≤ p :=
      Nat.le_of_lt ((((a : ZMod p) * (b : ZMod p))).val_lt)
    exact cyclotomicUnit_eq_neg_zeta_pow_mul_cyclotomicUnit_p_sub p K
      (((a : ZMod p) * (b : ZMod p)).val) h_le

end PerTermSwap

section StageFive

/-- **Stage 5 (half-range reindex of the σ-twisted product)**: combining
LV005c1a's substitution form, the per-term swap (`cyclotomicUnit_eq_if_upper_pair_up`),
and the half-range bijection reindex (`halfReduce_prod_reindex`):

  `σ_a(pollaczekUnit i : 𝓞 K) · cyclotomicUnit p K (a.val)^S =
   sign · ζ^{exp_total} · ∏_{b'} cyclotomicUnit p K b'^{halfReduce p a⁻¹ b'^E}`

where
  `sign := ∏_b (if upper(b) then -1 else 1)^{b^E}`,
  `exp_total := ∑_b (if upper(b) then (a · b).val else 0) · b^E`,
  `S := ∑_b b^E`.

After reindexing via `b' = halfReduce p a b`, the cyclotomicUnit indices
land in the half-range `{1, …, (p-1)/2}`, and the exponents become
`(halfReduce p a⁻¹ b')^E`.

This is the stage-5 building block. The remaining stage 6 work (Fermat
reduction `(halfReduce p a⁻¹ b')^E ≡ b'^E · a^i (mod p)` and absorbing
the discrepancy into `p`-th powers) collapses this to the eigenvalue
identity. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_half_range_reindex
    (hp_odd : p ≠ 2) (a : (ZMod p)ˣ) (i : ℕ) :
    cyclotomicSigmaOfUnit (p := p) K a •
        ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
      cyclotomicUnit p K ((a : ZMod p).val) ^
        (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
      (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                (1 : 𝓞 K)
              else
                -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
                  (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i))) *
        ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K b' ^ ((halfReduce p a⁻¹ b') ^ (p - 1 - i)) := by
  -- Start from stage 1: σ_a(E_i) · cyclotomicUnit (a.val)^S = ∏ cyclotomicUnit ((a · b).val)^{b^E}.
  rw [cyclotomicSigmaOfUnit_smul_pollaczekUnit_aggregate p K a i]
  -- Apply per-term swap to each factor.
  rw [show ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K (((a : ZMod p) * (b : ZMod p)).val) ^ (b ^ (p - 1 - i)) =
      ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then (1 : 𝓞 K)
          else -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
                (((a : ZMod p) * (b : ZMod p)).val)) *
          cyclotomicUnit p K (halfReduce p a b)) ^ (b ^ (p - 1 - i))
      from Finset.prod_congr rfl fun b _ => by
        rw [cyclotomicUnit_eq_if_upper_pair_up]]
  -- Note: `((a : ZMod p) * b).val` (with `b : ℕ`) equals `((a : ZMod p) * (b : ZMod p)).val`
  -- after the natCast — the identity holds because `(↑b : ZMod p) = (b : ZMod p)` on naturals.
  -- Distribute (s · c)^{exp} = s^{exp} · c^{exp}.
  rw [show ∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then (1 : 𝓞 K)
          else -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
                (((a : ZMod p) * (b : ZMod p)).val)) *
          cyclotomicUnit p K (halfReduce p a b)) ^ (b ^ (p - 1 - i)) =
      (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          (if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then (1 : 𝓞 K)
            else -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
                  (((a : ZMod p) * (b : ZMod p)).val)) ^ (b ^ (p - 1 - i))) *
        (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K (halfReduce p a b) ^ (b ^ (p - 1 - i)))
      from by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [mul_pow]]
  -- Now reindex the cyclotomicUnit-product via halfReduce bijection.
  congr 1
  -- ((a : ZMod p) * b) where b : ℕ vs (a : ZMod p) * (b : ZMod p).
  -- Check: `((a : ZMod p) * b)` automatic-coerces b → ZMod p, so equals
  -- `((a : ZMod p) * (b : ZMod p))`.
  -- Use halfReduce_prod_reindex with f(b, b') := cyclotomicUnit p K b' ^ (b ^ E).
  exact halfReduce_prod_reindex (p := p) (K := K) hp_odd a
    (fun b b' => cyclotomicUnit p K b' ^ (b ^ (p - 1 - i)))

end StageFive

section StageSix

/-- **Half-reduce exponent congruence**: for `a ∈ (ZMod p)ˣ`, `b' ∈
Ico 1 ((p-1)/2 + 1)`, and any natural exponent `E`,

  `(halfReduce p a⁻¹ b')^E ≡ ±((a⁻¹).val · b')^E (mod p)`,

where the sign is `+` if `((a⁻¹) · b').val ≤ (p-1)/2` and `-` if
`((a⁻¹) · b').val > (p-1)/2`. For `E` even the sign vanishes, giving
`(halfReduce p a⁻¹ b')^E ≡ ((a⁻¹).val · b')^E (mod p)` uniformly. -/
theorem halfReduce_pow_mod_eq (a : (ZMod p)ˣ) (b' E : ℕ) :
    ((halfReduce p a⁻¹ b' : ℕ) : ZMod p) ^ E =
      (if (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)).val ≤ (p - 1) / 2 then
          (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)) ^ E
        else (-(((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p))) ^ E) := by
  unfold halfReduce
  split_ifs with h
  · rw [ZMod.natCast_val, ZMod.cast_id]
  · -- Goal: (((p - ((a⁻¹) · b').val) : ℕ) : ZMod p)^E = (-(...))^E.
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    have h_val_lt : (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)).val < p :=
      (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)).val_lt
    rw [Nat.cast_sub (Nat.le_of_lt h_val_lt), ZMod.natCast_self, ZMod.natCast_val,
      ZMod.cast_id, zero_sub]

/-- **LV005c1b-6a**: for `E` even, the case-split form of
`halfReduce_pow_mod_eq` collapses (since `(-1)^E = 1`):

  `((halfReduce p a⁻¹ b' : ℕ) : ZMod p)^E = (((a⁻¹) : ZMod p) * (b' : ZMod p))^E`. -/
theorem halfReduce_pow_mod_eq_of_even (a : (ZMod p)ˣ) (b' E : ℕ) (hE : Even E) :
    ((halfReduce p a⁻¹ b' : ℕ) : ZMod p) ^ E =
      (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)) ^ E := by
  rw [halfReduce_pow_mod_eq p a b' E]
  split_ifs with h
  · rfl
  · -- (-(a⁻¹ · b'))^E = ((-1) · (a⁻¹ · b'))^E = ((-1)^E) · (a⁻¹ · b')^E.
    -- For E even, (-1)^E = 1.
    rw [show -(((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)) =
        (-1 : ZMod p) * (((a⁻¹ : (ZMod p)ˣ) : ZMod p) * (b' : ZMod p)) by ring,
      mul_pow, hE.neg_one_pow, one_mul]

/-- **LV005c1b-6b**: For `E = p - 1 - i` and `a ∈ (ZMod p)ˣ`, Fermat's
little theorem gives

  `((a⁻¹ : (ZMod p)ˣ) : ZMod p)^E = ((a : (ZMod p)ˣ) : ZMod p)^i`.

(Both raised to power E or i in ZMod p, using `a^(p-1) = 1`.) -/
theorem unit_inv_val_pow_E_eq_pow_i (a : (ZMod p)ˣ) (i : ℕ) (hi : i ≤ p - 1) :
    ((a⁻¹ : (ZMod p)ˣ) : ZMod p) ^ (p - 1 - i) =
      ((a : (ZMod p)ˣ) : ZMod p) ^ i := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [Units.val_inv_eq_inv_val, inv_pow]
  -- Goal: (((a : ZMod p)) ^ (p-1-i))⁻¹ = ((a : ZMod p)) ^ i.
  symm
  apply eq_inv_of_mul_eq_one_left
  -- Goal: ((a : ZMod p)) ^ (p-1-i) * ((a : ZMod p)) ^ i = 1.
  rw [← pow_add, show i + (p - 1 - i) = p - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one a.ne_zero

omit hp [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
/-- **LV005c1b-6c (per-term, ∃-form)**: for `x : (𝓞 K)ˣ` and natural exponents
`M, N` with `M ≡ N (mod p)`, there exists `γ : (𝓞 K)ˣ` such that
`(x : 𝓞 K)^M = (x : 𝓞 K)^N * (γ : 𝓞 K)^p`.

Witness: `γ = x^k` where `(M : ℤ) - N = p · k`, interpreted via integer
powers on the unit group `(𝓞 K)ˣ`. -/
theorem unit_pow_eq_pow_mul_pth_power_of_modEq (x : (𝓞 K)ˣ) (M N : ℕ)
    (h : (p : ℤ) ∣ (M : ℤ) - N) :
    ∃ γ : (𝓞 K)ˣ, ((x : 𝓞 K)) ^ M = ((x : 𝓞 K)) ^ N * ((γ : 𝓞 K)) ^ p := by
  obtain ⟨k, hk⟩ := h
  refine ⟨x ^ k, ?_⟩
  -- Show in (𝓞 K)ˣ: x^M = x^N * (x^k)^p, then cast to 𝓞 K.
  have h_unit : (x : (𝓞 K)ˣ) ^ M = (x : (𝓞 K)ˣ) ^ N * ((x ^ k) ^ p : (𝓞 K)ˣ) := by
    have h_zpow : (x : (𝓞 K)ˣ) ^ ((M : ℤ) - N) = (x ^ k) ^ p := by
      rw [hk, mul_comm, zpow_mul, zpow_natCast]
    have h_eq_zpow : (x : (𝓞 K)ˣ) ^ ((M : ℤ) - N) =
        (x : (𝓞 K)ˣ) ^ M * ((x : (𝓞 K)ˣ) ^ N)⁻¹ := zpow_sub x M N
    rw [h_eq_zpow] at h_zpow
    rw [show (x : (𝓞 K)ˣ) ^ M = (x : (𝓞 K)ˣ) ^ N *
        ((x : (𝓞 K)ˣ) ^ M * ((x : (𝓞 K)ˣ) ^ N)⁻¹) from by group, h_zpow]
  -- Cast to 𝓞 K.
  rw [show ((x : 𝓞 K)) ^ M = (((x : (𝓞 K)ˣ) ^ M : (𝓞 K)ˣ) : 𝓞 K) from
        (Units.val_pow_eq_pow_val x M).symm,
      show ((x : 𝓞 K)) ^ N = (((x : (𝓞 K)ˣ) ^ N : (𝓞 K)ˣ) : 𝓞 K) from
        (Units.val_pow_eq_pow_val x N).symm,
      show (((x ^ k : (𝓞 K)ˣ) : 𝓞 K)) ^ p = (((x ^ k) ^ p : (𝓞 K)ˣ) : 𝓞 K) from
        (Units.val_pow_eq_pow_val (x ^ k) p).symm,
      ← Units.val_mul]
  exact congrArg ((↑) : (𝓞 K)ˣ → 𝓞 K) h_unit

/-- **LV005c1b-6 combined per-term Fermat reduction**: combining 6a + 6b,
when `E = p - 1 - i` is even (the Pollaczek setup), in `ZMod p`,

  `((halfReduce p a⁻¹ b' : ℕ) : ZMod p)^E = (a : ZMod p)^i · (b' : ZMod p)^E`. -/
theorem halfReduce_pow_eq_pow_mul_pow (a : (ZMod p)ˣ) (b' i : ℕ)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    ((halfReduce p a⁻¹ b' : ℕ) : ZMod p) ^ (p - 1 - i) =
      ((a : (ZMod p)ˣ) : ZMod p) ^ i * (b' : ZMod p) ^ (p - 1 - i) := by
  rw [halfReduce_pow_mod_eq_of_even p a b' (p - 1 - i) hi_even, mul_pow,
    unit_inv_val_pow_E_eq_pow_i p a i hi]

/-- **LV005c1b-6 ℕ-level mod-equivalence**: ℕ-level form of the half-range
exponent identity. -/
theorem halfReduce_pow_modEq (a : (ZMod p)ˣ) (b' i : ℕ)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    halfReduce p a⁻¹ b' ^ (p - 1 - i) ≡
      ((a^i : (ZMod p)ˣ) : ZMod p).val * b' ^ (p - 1 - i) [MOD p] := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_zmod := halfReduce_pow_eq_pow_mul_pow p a b' i hi hi_even
  apply (ZMod.natCast_eq_natCast_iff' _ _ p).mp
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id]
  exact h_zmod

/-- **Bridge: ℕ-Nat.ModEq → ℤ-divisibility**. -/
theorem natModEq_to_intDvd {a b : ℕ} {n : ℕ} (h : a ≡ b [MOD n]) :
    (n : ℤ) ∣ (a : ℤ) - b :=
  dvd_sub_comm.mp (Nat.modEq_iff_dvd.mp h)

/-- **LV005c1b-6d (per-term)**: for each `b'` in the half-range, there
exists `γ_b' : (𝓞 K)ˣ` such that

  `cyclotomicUnit p K b' ^ (halfReduce p a⁻¹ b' ^ (p - 1 - i)) =
   cyclotomicUnit p K b' ^ (((a^i : (ZMod p)ˣ) : ZMod p).val * b' ^ (p - 1 - i)) *
     (γ_b' : 𝓞 K) ^ p`. -/
theorem cyclotomicUnit_pow_halfReduce_per_term
    (a : (ZMod p)ˣ) (b' i : ℕ)
    (hb' : b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1)) (_hp_odd : p ≠ 2)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    ∃ γ : (𝓞 K)ˣ,
      cyclotomicUnit p K b' ^ (halfReduce p a⁻¹ b' ^ (p - 1 - i)) =
        cyclotomicUnit p K b' ^
          (((a^i : (ZMod p)ˣ) : ZMod p).val * b' ^ (p - 1 - i)) *
        ((γ : 𝓞 K)) ^ p := by
  rw [Finset.mem_Ico] at hb'
  obtain ⟨hb'_pos, hb'_le⟩ := hb'
  have hp_pos : 0 < p := hp.out.pos
  have hb'_lt_p : b' < p := by
    have : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
    omega
  have hb'_coprime : b'.Coprime p :=
    (Nat.coprime_of_lt_prime (Nat.one_le_iff_ne_zero.mp hb'_pos)
      hb'_lt_p hp.out).symm
  have hp_two : 2 ≤ p := hp.out.two_le
  -- Get the unit form of cyclotomicUnit and apply 6c.
  set x := cyclotomicUnitUnit p K b' hb'_coprime hp_two
  have h_x_val : ((x : (𝓞 K)ˣ) : 𝓞 K) = cyclotomicUnit p K b' :=
    cyclotomicUnitUnit_val _ _ _ _ _
  have h_modEq := halfReduce_pow_modEq p a b' i hi hi_even
  have h_dvd := natModEq_to_intDvd h_modEq
  obtain ⟨γ, hγ⟩ := unit_pow_eq_pow_mul_pth_power_of_modEq p K x _ _ h_dvd
  refine ⟨γ, ?_⟩
  rw [← h_x_val] at *
  exact hγ

/-- **LV005c1b-6e (aggregate)**: aggregate per-term p-th-power discrepancy
across the full half-range product. -/
theorem cyclotomicUnit_pow_halfReduce_aggregate
    (a : (ZMod p)ˣ) (i : ℕ) (hp_odd : p ≠ 2)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    ∃ γ : (𝓞 K)ˣ,
      ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K b' ^ (halfReduce p a⁻¹ b' ^ (p - 1 - i)) =
        (∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
          cyclotomicUnit p K b' ^
            (((a^i : (ZMod p)ˣ) : ZMod p).val * b' ^ (p - 1 - i))) *
          ((γ : 𝓞 K)) ^ p := by
  classical
  -- For each b' ∈ half-range, choose a witness γ_b' from 6d.
  let γ_fn : ℕ → (𝓞 K)ˣ := fun b' =>
    if h : b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1) then
      Classical.choose
        (cyclotomicUnit_pow_halfReduce_per_term p K a b' i h hp_odd hi hi_even)
    else 1
  refine ⟨∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1), γ_fn b', ?_⟩
  -- Per-factor: cyclotomicUnit b' ^ M = cyclotomicUnit b' ^ N · γ_b' ^ p.
  rw [show ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K b' ^ (halfReduce p a⁻¹ b' ^ (p - 1 - i)) =
      ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        (cyclotomicUnit p K b' ^
            (((a^i : (ZMod p)ˣ) : ZMod p).val * b' ^ (p - 1 - i)) *
          ((γ_fn b' : 𝓞 K)) ^ p) from
      Finset.prod_congr rfl fun b' hb' => by
        simp only [γ_fn, hb', dif_pos]
        exact Classical.choose_spec
          (cyclotomicUnit_pow_halfReduce_per_term p K a b' i hb' hp_odd hi hi_even)]
  -- ∏ (X · Y) = (∏ X) · (∏ Y).
  rw [Finset.prod_mul_distrib]
  congr 1
  -- Goal: ∏ (γ_fn b' : 𝓞 K)^p = (↑(∏ γ_fn b') : 𝓞 K)^p.
  rw [Finset.prod_pow, Units.coe_prod]

/-- **Identification with `E_i^N`**: the half-range product
`∏ cyclotomicUnit(b')^{N · b'^E}` collapses to `(pollaczekUnit i : 𝓞 K)^N`. -/
theorem prod_cyclotomicUnit_pow_mul_eq_pollaczekUnit_pow
    (i N : ℕ) :
    ∏ b' ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
        cyclotomicUnit p K b' ^ (N * b' ^ (p - 1 - i)) =
      ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^ N := by
  rw [pollaczekUnit_val_eq_prod]
  -- Goal: ∏ cyclotomicUnit b' ^ (N * b'^E) = (∏ cyclotomicUnit b' ^ b'^E)^N.
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b' _ => ?_
  rw [← pow_mul, mul_comm]

/-- **LV005c1b main theorem (almost-eigenvalue form)**: the σ_a-twist of
`pollaczekUnit p K i`, when multiplied by `cyclotomicUnit p K (a.val)^S`,
collapses (modulo p-th powers) to `(pollaczekUnit p K i)^{(a^i mod p).val}`
times an explicit sign-and-ζ-prefactor:

  `σ_a(pollaczekUnit i : 𝓞 K) · cyclotomicUnit p K (a.val)^S =
   (sign + ζ-prefactor) ·
     (pollaczekUnit p K i : 𝓞 K)^{((a^i : (ZMod p)ˣ) : ZMod p).val} ·
     γ^p`

for some explicit `γ : (𝓞 K)ˣ` and where the sign + ζ-prefactor is the
explicit factor from stage 5's half-range reindex.

The remaining residual (LV005c1b-6f / LV005c2's input) is to show that
`(sign + ζ-prefactor) · cyclotomicUnit p K (a.val)^{-S}` is itself a
`p`-th power in `(𝓞 K)ˣ`, which collapses the eigenvalue identity to
the clean form `σ_a(E_i) ≡ E_i^{(a^i mod p).val} (mod p-th powers)`. -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue
    (a : (ZMod p)ˣ) (i : ℕ) (hp_odd : p ≠ 2)
    (hi : i ≤ p - 1) (hi_even : Even (p - 1 - i)) :
    ∃ γ : (𝓞 K)ˣ,
      cyclotomicSigmaOfUnit (p := p) K a •
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) *
        cyclotomicUnit p K ((a : ZMod p).val) ^
          (∑ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1), b ^ (p - 1 - i)) =
        (∏ b ∈ Finset.Ico 1 ((p - 1) / 2 + 1),
            ((if ((a : ZMod p) * (b : ZMod p)).val ≤ (p - 1) / 2 then
                  (1 : 𝓞 K)
                else
                  -((zeta_spec p ℚ K).toInteger : 𝓞 K) ^
                    (((a : ZMod p) * (b : ZMod p)).val))) ^ (b ^ (p - 1 - i))) *
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) ^
            (((a^i : (ZMod p)ˣ) : ZMod p).val) *
          ((γ : 𝓞 K)) ^ p := by
  obtain ⟨γ, hγ⟩ := cyclotomicUnit_pow_halfReduce_aggregate p K a i hp_odd hi hi_even
  refine ⟨γ, ?_⟩
  rw [cyclotomicSigmaOfUnit_smul_pollaczekUnit_half_range_reindex p K hp_odd a i]
  -- LHS: (sign+ζ) · ∏ cyclotomicUnit(b')^{(halfReduce p a⁻¹ b')^E}.
  rw [hγ]
  -- LHS now: (sign+ζ) · (∏ cyclotomicUnit(b')^{a^i.val · b'^E}) · γ^p.
  rw [prod_cyclotomicUnit_pow_mul_eq_pollaczekUnit_pow p K i
    (((a^i : (ZMod p)ˣ) : ZMod p).val)]
  -- RHS in goal: (sign+ζ) · pollaczekUnit^{a^i.val} · γ^p.
  ring

end StageSix

/-- **Power-sum half-range divisibility for FLT37**: `S = ∑_{b=1}^{18} b^4
= 432345 = 37 · 11685`. Direct kernel-`decide` numerical computation.

This is the irregular-index power-sum divisibility specialised to FLT37,
needed to absorb `cyclotomicUnit(a.val)^S` as a `p`-th power in the
eigenvalue identity (since `S ≡ 0 (mod p)` makes `cyclotomicUnit(a.val)^S
= (cyclotomicUnit(a.val)^{S/p})^p`). -/
theorem powerSum_half_range_div_thirtyseven :
    (37 : ℤ) ∣ (∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32) : ℤ) := by
  decide

/-- **Power-sum half-range divisibility for FLT37 (ℕ form)**. -/
theorem powerSum_half_range_div_thirtyseven_nat :
    (37 : ℕ) ∣ ∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32) := by
  decide

/-- **`x^S = (x^11685)^37` for FLT37 power-sum** — abstracted to any
`Monoid` element. Direct consequence of `S = 37 · 11685`. -/
theorem pow_powerSum_eq_pow_pow_thirtyseven {M : Type*} [Monoid M] (x : M) :
    x ^ (∑ b ∈ Finset.Ico 1 ((37 - 1) / 2 + 1), b ^ (37 - 1 - 32)) =
      (x ^ 11685) ^ 37 := by
  rw [← pow_mul]
  rfl

/-- **FLT37-specialised almost-eigenvalue identity** with cycU correction
expressed as a 37-th power.

Using `pow_powerSum_eq_pow_pow_thirtyseven` (`S = 11685 · 37` for the
FLT37 power-sum), the LHS factor `cyclotomicUnit p K (a.val)^S` from
`cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue` becomes
`(cyclotomicUnit 37 K (a.val)^11685)^37`. This re-expression makes BOTH
sides of the eigenvalue identity have explicit 37-th-power correction
factors (LHS: from cycU; RHS: from γ), which is the form needed to
extract the clean eigenvalue identity at the unit level (where 37-th
powers can be combined and inverted). -/
theorem cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue_FLT37
    {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {37} ℚ K]
    [hp37 : Fact (Nat.Prime 37)]
    (a : (ZMod 37)ˣ) :
    ∃ γ : (𝓞 K)ˣ,
      cyclotomicSigmaOfUnit (p := 37) K a •
          ((pollaczekUnit 37 K 32 : (𝓞 K)ˣ) : 𝓞 K) *
        (cyclotomicUnit 37 K ((a : ZMod 37).val) ^ 11685) ^ 37 =
        (∏ b ∈ Finset.Ico (1 : ℕ) (((37 : ℕ) - 1) / 2 + 1),
            ((if ((a : ZMod 37) * (b : ZMod 37)).val ≤ ((37 : ℕ) - 1) / 2 then
                  (1 : 𝓞 K)
                else
                  -((zeta_spec 37 ℚ K).toInteger : 𝓞 K) ^
                    (((a : ZMod 37) * (b : ZMod 37)).val))) ^
              (b ^ ((37 : ℕ) - 1 - 32))) *
          ((pollaczekUnit 37 K 32 : (𝓞 K)ˣ) : 𝓞 K) ^
            (((a^32 : (ZMod 37)ˣ) : ZMod 37).val) *
          ((γ : 𝓞 K)) ^ 37 := by
  obtain ⟨γ, hγ⟩ := cyclotomicSigmaOfUnit_smul_pollaczekUnit_almost_eigenvalue
    37 K a 32 (by decide : (37 : ℕ) ≠ 2)
    (by decide : (32 : ℕ) ≤ 37 - 1)
    (by decide : Even (37 - 1 - 32))
  refine ⟨γ, ?_⟩
  rw [← pow_powerSum_eq_pow_pow_thirtyseven
    (cyclotomicUnit 37 K ((a : ZMod 37).val))]
  exact hγ

end FLT37

end BernoulliRegular

end
