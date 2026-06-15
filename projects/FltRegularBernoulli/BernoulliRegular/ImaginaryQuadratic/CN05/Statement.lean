module

public import BernoulliRegular.ImaginaryQuadratic.ClassNumber

@[expose] public section

noncomputable section

open Complex NumberField

namespace BernoulliRegular

/-! ### CN-05 strategy and scope

**CN-05 goal**: for `p ≡ 3 (mod 4)` prime, prove on `Re(s) > 1`:

  `NumberField.dedekindZeta (Kminus p) s =`
    `riemannZeta s * DirichletCharacter.LFunction (legendreDirichlet p) s`

**Reduction via Dirichlet series coefficients**:

Both sides have Dirichlet series (on `Re(s) > 1`):
  LHS: `∑_n (idealNormMultiplicity (Kminus p) n) / n^s`
  RHS: `∑_n (1 * η)(n) / n^s` (Dirichlet convolution)
  where `(1 * η)(n) = ∑_{d | n} η(d)` with `η = legendreDirichlet p` extended
  to `ℕ` via `η(d) = (d/p)_L` for `(d, p) = 1` and `η(d) = 0` for `p | d`.

Since both Dirichlet series converge absolutely on `Re(s) > 1`, it suffices to
show coefficients match:

  `(CN-05-coeff) : ∀ n : ℕ+, idealNormMultiplicity (Kminus p) n = ∑_{d | n} η(d)`

**Reduction via multiplicativity**:

Both sides are multiplicative (coprime n, m):
- `idealNormMultiplicity_mul` (already proved, T020d-2) for LHS.
- `Nat.ArithmeticFunction.coe_mul_zeta_apply` or direct calc for RHS.

So it suffices to prove CN-05-coeff at prime powers `n = q^k`:

  `idealNormMultiplicity (Kminus p) (q^k) = ∑_{j=0}^{k} η(q^j)`

Split into three sub-cases based on splitting behavior of `q` in `Kminus p`:

**Case (q = p, ramified)**: η(p) = 0 implies `∑_{j=0}^k η(p^j) = η(1) = 1`.
  On the LHS side: `p` ramifies (single prime 𝔭 of norm `p`), so
  `idealNormMultiplicity (Kminus p) (p^k) = 1` for all k.
  **Sub-task A**: Mirror the cyclotomic `idealNormMultiplicity_p_pow_eq_one`
  but for Kminus p, using that p ramifies (via disc(Kminus p) = -p).

**Case (q ≠ p, splits, η(q) = 1)**: `∑_{j=0}^k 1^j = k + 1`.
  Two primes 𝔭₁, 𝔭₂ above q (each of norm q). Ideals of norm q^k are
  `𝔭₁^a · 𝔭₂^b` with `a + b = k`, giving k+1 ideals.
  **Sub-task B1**: Prove splitting characterization `q splits in Kminus p ⟺
  η(q) = 1` for q ≠ p, q odd. Uses Legendre reciprocity machinery.

**Case (q ≠ p, inert, η(q) = -1)**: `∑_{j=0}^k (-1)^j = 1 if k even, 0 if odd`.
  One prime 𝔭 above q of norm q². Ideals of norm q^k exist iff k even;
  if k = 2m, it's 𝔭^m — exactly one.
  **Sub-task B2**: Same as B1 but inert case.

**Sub-task C**: Handle q = 2 separately (if needed, depending on parity).

**Sub-task D**: Establish the Dirichlet series convolution identity for
`ζ · L(η)`, relating it to `(1 * η)`'s LSeries. Uses `LSeries_mul` or
similar from mathlib.

**Estimated scope**: A ~30 lines, B1 ~80 lines, B2 ~80 lines, D ~40 lines.
Total ~230 lines of Euler-product / splitting machinery.

**Approach not attempted in this session**: formalizing the Artin formalism
for zeta functions of subfields (`ζ_{ℚ(√-p)} = ∏_{χ trivial on H} L(χ)` where
`H = Gal(ℚ(ζ_p)/ℚ(√-p)) = squares in (ℤ/p)^×`). This would give CN-05 as a
corollary of the cyclotomic factorization but requires substantial additional
infrastructure not in mathlib. -/
section CN05_statement

variable (p : ℕ) [hp : Fact p.Prime]

/-- The extension of `legendreDirichlet p` to `ℕ`: `η(d) = (d/p)_L` for
`(d, p) = 1`, and `η(d) = 0` for `p | d`. Matches `DirichletCharacter.LFunction`
coefficients. -/
noncomputable def legendreDirichletNat (d : ℕ) : ℂ :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  legendreDirichlet p (d : ZMod p)

/-- The Dirichlet convolution `(1 * η)(n) = ∑_{d | n} η(d)` for the Legendre
character — the "expected" arithmetic function for CN-05. -/
noncomputable def oneMulEta (n : ℕ) : ℂ :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  ∑ d ∈ n.divisors, legendreDirichletNat p d

/-- **CN-05 main statement** (currently open): the factorization of the Dedekind
zeta function of `Kminus p` as a Dirichlet L-function product. -/
def CN05Hypothesis : Prop :=
  ∀ s : ℂ, 1 < s.re →
    NumberField.dedekindZeta (Kminus p) s =
      riemannZeta s * DirichletCharacter.LFunction (legendreDirichlet p) s

/-- **Coefficient equality**: the key arithmetic identity underlying CN-05.
For all `n : ℕ`, the number of ideals of `𝒪_{Kminus p}` of absolute norm `n`
equals the Dirichlet convolution `(1 * η)(n) = ∑_{d | n} η(d)`.

This is a multiplicative function identity, so by `idealNormMultiplicity_mul`
and the multiplicativity of Dirichlet convolutions, it reduces to matching
at prime powers `n = q^k`:
- At `q = p`: both sides equal `1` (ramified/η(p) = 0).
- At `q ≠ p` split in Kminus p: both sides equal `k + 1`.
- At `q ≠ p` inert in Kminus p: both sides equal `1 if k even, 0 otherwise`. -/
def CN05CoeffEq : Prop :=
  ∀ n : ℕ,
    (idealNormMultiplicity (Kminus p) n : ℂ) =
      LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) n

/-- **Reduction theorem**: CN-05 follows from the coefficient equality
`idealNormMultiplicity (Kminus p) n = (1 * η)(n)` (as arithmetic function).

Proof: both sides of CN-05 are Dirichlet L-series on `Re(s) > 1`.
- LHS `ζ_{Kminus p}` is the L-series of `idealNormMultiplicity (Kminus p)`
  (via `dedekindZeta_eq_tsum_idealNormMultiplicity`).
- RHS `ζ · L(η)` is the L-series of `1 * legendreDirichletNat` (via
  `LSeries_convolution'`, with `LSeries 1 = ζ` and
  `LSeries legendreDirichletNat = L(η)`).
- By `CN05CoeffEq`, the coefficient sequences are equal, so the L-series match. -/
theorem CN05_of_CN05CoeffEq (h_coeff : CN05CoeffEq p) : CN05Hypothesis p := by
  intro s hs
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  -- LHS as an L-series of idealNormMultiplicity
  have h_LHS : NumberField.dedekindZeta (Kminus p) s =
      LSeries (fun n : ℕ => (idealNormMultiplicity (Kminus p) n : ℂ)) s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity (Kminus p) hs]
    unfold LSeries LSeries.term
    congr 1
    ext n
    by_cases hn : n = 0
    · simp [hn, idealNormMultiplicity_zero]
    · simp [hn, div_eq_mul_inv, Complex.cpow_neg]
  rw [h_LHS]
  -- Express coefficients via coefficient equality
  have h_coef_eq : (fun n : ℕ => (idealNormMultiplicity (Kminus p) n : ℂ)) =
      LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) := by
    ext n
    exact h_coeff n
  rw [h_coef_eq]
  -- Use convolution formula for L-series
  have h_sum1 : LSeriesSummable (fun _ : ℕ => (1 : ℂ)) s := by
    have : (fun _ : ℕ => (1 : ℂ)) = (1 : ℕ → ℂ) := rfl
    rw [this]
    exact LSeriesSummable_one_iff.mpr hs
  have h_sum2 : LSeriesSummable (legendreDirichletNat p) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re (legendreDirichlet p) hs
  rw [LSeries_convolution' h_sum1 h_sum2]
  -- LSeries (fun _ => 1) s = ζ s
  have h_zeta : LSeries (fun _ : ℕ => (1 : ℂ)) s = riemannZeta s := by
    rw [show (fun _ : ℕ => (1 : ℂ)) = (1 : ℕ → ℂ) from rfl]
    exact LSeries_one_eq_riemannZeta hs
  -- LSeries legendreDirichletNat s = L(η) s
  have h_Leta : LSeries (legendreDirichletNat p) s =
      DirichletCharacter.LFunction (legendreDirichlet p) s :=
    (DirichletCharacter.LFunction_eq_LSeries _ hs).symm
  rw [h_zeta, h_Leta]

/-- Convolution of the constant `1` function with any `g` at `p^k` equals
`∑_{j=0}^k g(p^j)`. -/
lemma convolution_one_at_prime_pow {q : ℕ} (hq : q.Prime) (k : ℕ) (g : ℕ → ℂ) :
    LSeries.convolution (fun _ : ℕ => (1 : ℂ)) g (q^k) =
      ∑ j ∈ Finset.range (k + 1), g (q^j) := by
  rw [show LSeries.convolution (fun _ : ℕ => (1 : ℂ)) g (q^k) =
      ∑ x ∈ (q^k).divisorsAntidiagonal, 1 * g x.2 from by rw [LSeries.convolution_def]]
  rw [← Nat.map_div_left_divisors, Finset.sum_map]
  rw [Nat.divisors_prime_pow hq, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- At `p` (the ramified prime), `legendreDirichletNat p (p^j) = 0` for `j ≥ 1`,
since `p = 0` in `ZMod p` and the Legendre character vanishes at `0`. -/
lemma legendreDirichletNat_at_prime_pow_pos {j : ℕ} (hj : 0 < j) :
    legendreDirichletNat p (p^j) = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change legendreDirichlet p ((p^j : ℕ) : ZMod p) = 0
  rw [show ((p^j : ℕ) : ZMod p) = (p : ZMod p)^j from by push_cast; rfl]
  rw [ZMod.natCast_self p, zero_pow hj.ne']
  exact DirichletCharacter.map_zero' _ (by
    exact_mod_cast hp.out.one_lt.ne')

/-- `legendreDirichletNat p 1 = 1`. -/
lemma legendreDirichletNat_one : legendreDirichletNat p 1 = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change legendreDirichlet p ((1 : ℕ) : ZMod p) = 1
  push_cast
  exact map_one _

/-- **CN-05 coefficient matching at prime powers of `p`** (one of three sub-cases).

The Dirichlet convolution `1 * legendreDirichletNat p` evaluated at `p^k` is `1`
for all `k`. This matches the ideal-count at the ramified prime (once that's proven).

  `(1 * η)(p^k) = η(1) + η(p) + ... + η(p^k) = 1 + 0 + ... + 0 = 1`. -/
theorem convolution_one_legendreNat_at_prime_pow_p (k : ℕ) :
    LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (p^k) = 1 := by
  rw [convolution_one_at_prime_pow hp.out k (legendreDirichletNat p)]
  rw [Finset.sum_range_succ' _ k]
  simp only [pow_zero, legendreDirichletNat_one p]
  suffices h : ∑ j ∈ Finset.range k, legendreDirichletNat p (p^(j + 1)) = 0 by
    rw [h, zero_add]
  apply Finset.sum_eq_zero
  intros j _
  exact legendreDirichletNat_at_prime_pow_pos p (Nat.succ_pos j)

/-- `legendreDirichletNat p` is completely multiplicative: `η(q^j) = η(q)^j`. -/
lemma legendreDirichletNat_pow (q j : ℕ) :
    legendreDirichletNat p (q^j) = (legendreDirichletNat p q)^j := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  change legendreDirichlet p ((q^j : ℕ) : ZMod p) =
    (legendreDirichlet p ((q : ℕ) : ZMod p))^j
  rw [show ((q^j : ℕ) : ZMod p) = ((q : ℕ) : ZMod p)^j from by push_cast; rfl]
  exact map_pow (legendreDirichlet p).toMonoidHom _ j

/-- **RHS at q ≠ p split** (η(q) = 1): `(1 * η)(q^k) = k+1`. -/
theorem convolution_one_legendreNat_at_prime_pow_split (q : ℕ) (hq : q.Prime) (k : ℕ)
    (hη : legendreDirichletNat p q = 1) :
    LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (q^k) = (k + 1 : ℕ) := by
  rw [convolution_one_at_prime_pow hq k]
  simp_rw [legendreDirichletNat_pow p q, hη, one_pow]
  simp

/-- **RHS at q ≠ p inert** (η(q) = -1): `(1 * η)(q^k) = 1 if k even, 0 if k odd`. -/
theorem convolution_one_legendreNat_at_prime_pow_inert (q : ℕ) (hq : q.Prime) (k : ℕ)
    (hη : legendreDirichletNat p q = -1) :
    LSeries.convolution (fun _ : ℕ => (1 : ℂ)) (legendreDirichletNat p) (q^k) =
      if Even k then 1 else 0 := by
  rw [convolution_one_at_prime_pow hq k]
  simp_rw [legendreDirichletNat_pow p q, hη]
  -- ∑_{j=0}^{k} (-1)^j = 1 if k even, 0 if k odd.
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · rw [if_pos hk, if_neg (Nat.not_even_iff_odd.mpr (Even.add_one hk))]
      have hk_even : Even (k + 1 - 1) := by simpa using hk
      rw [show ((-1 : ℂ))^(k+1) = -1 from by
        obtain ⟨m, hm⟩ := hk
        rw [hm]
        rw [show m + m + 1 = 2 * m + 1 from by ring, pow_add, pow_one,
          show ((-1 : ℂ))^(2 * m) = 1 from by rw [pow_mul, neg_one_sq, one_pow], one_mul]]
      ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr hk), if_pos (Odd.add_one hk)]
      obtain ⟨m, hm⟩ := hk
      rw [hm]
      rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring]
      rw [show ((-1 : ℂ))^(2 * (m + 1)) = 1 from by rw [pow_mul, neg_one_sq, one_pow]]
      ring

end CN05_statement

end BernoulliRegular
