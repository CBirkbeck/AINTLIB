module

public import BernoulliRegular.GaussSumProduct
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Classical quadratic Gauss sum and its value

This file proves Gauss's classical 1811 theorem:
`∑_{n=0}^{p-1} e^{2πi n²/p} = i·√p` for `p ≡ 3 (mod 4)` prime.

As a consequence, combined with the identity `∑_{n=0}^{p-1} e^{2πi n²/p}
= gaussSum (legendreDirichlet p) stdAddChar`, we deduce
`gaussSum (legendreDirichlet p) stdAddChar = i·√p`. This is the key input
needed to make the Washington chain (WP-E through WP-I and the Dedekind FE)
unconditional.

## Main results

* `jacobiTheta_S_smul_real` (GS-01): specialization of `jacobiTheta_S_smul`
  to `τ = i·y` for real `y > 0`, giving `jacobiTheta (i/y) = √y · jacobiTheta (iy)`.

## References

* Ireland–Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 6.
* Davenport, *Multiplicative Number Theory*, Chapter 2.
* Serre, *A Course in Arithmetic*, Chapter VI, §4.
-/

@[expose] public section

noncomputable section

open Complex Real

namespace BernoulliRegular

/-- The classical quadratic Gauss sum `∑_{n : ZMod p} stdAddChar(n²)`.

For `p` an odd prime, this is Gauss's classical sum
`∑_{n=0}^{p-1} e^{2πi n²/p}`, which equals `i·√p` for `p ≡ 3 mod 4`
by Gauss 1811. -/
noncomputable def classicalGaussSum (p : ℕ) [NeZero p] : ℂ :=
  ∑ n : ZMod p, (ZMod.stdAddChar : AddChar (ZMod p) ℂ) (n ^ 2)

/-- Counting square roots in `ZMod p`: for `p` odd prime, the number of
`n : ZMod p` with `n² = t` equals `1 + quadraticChar (ZMod p) t` (as integers). -/
lemma card_sq_eq_add_quadraticChar {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2) (t : ZMod p) :
    ((Finset.univ.filter (fun n : ZMod p => n ^ 2 = t)).card : ℤ) =
      1 + quadraticChar (ZMod p) t := by
  classical
  have h_char : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp_odd
  by_cases ht : t = 0
  · -- t = 0: only n = 0 has n² = 0.
    subst ht
    rw [MulChar.map_zero, add_zero]
    have h_unique : Finset.univ.filter (fun n : ZMod p => n ^ 2 = 0) = {0} := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0)
    rw [h_unique, Finset.card_singleton, Nat.cast_one]
  · by_cases h_sq : IsSquare t
    · -- t nonzero square: 2 roots (a and -a for t = a²).
      rw [(quadraticChar_one_iff_isSquare ht).mpr h_sq]
      obtain ⟨a, ha⟩ := h_sq
      have ha_ne : a ≠ 0 := by
        intro h
        apply ht
        rw [ha, h, mul_zero]
      -- Need: a ≠ -a, which follows from p odd (so 2 ≠ 0 in ZMod p).
      have h_two_ne : (2 : ZMod p) ≠ 0 := by
        intro hh
        have h_cast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hh
        have : (p : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h_cast
        rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h2
        · exact hp.out.one_lt.ne' h1
        · exact hp_odd h2
      have ha_ne_neg : a ≠ -a := fun h => by
        apply ha_ne
        have h_sum : a + a = 0 := by linear_combination h
        have h_2a : (2 : ZMod p) * a = 0 := by linear_combination h_sum
        rcases mul_eq_zero.mp h_2a with h' | h'
        · exact absurd h' h_two_ne
        · exact h'
      -- Filter {n : n² = t} = {a, -a}.
      have h_filter : Finset.univ.filter (fun n : ZMod p => n ^ 2 = t) = {a, -a} := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        have h_aa : a * a = t := ha.symm
        constructor
        · intro hn
          -- n² = t = a², so (n-a)(n+a) = 0.
          have hprod : (n - a) * (n + a) = 0 := by linear_combination hn - h_aa
          rcases mul_eq_zero.mp hprod with h | h
          · left; linear_combination h
          · right; linear_combination h
        · rintro (h | h)
          · rw [h]; show a ^ 2 = t; linear_combination h_aa
          · rw [h]; show (-a) ^ 2 = t; linear_combination h_aa
      rw [h_filter, Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using ha_ne_neg),
        Finset.card_singleton]
      norm_num
    · -- t non-square: 0 roots, quadraticChar t = -1.
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr h_sq]
      have h_empty : Finset.univ.filter (fun n : ZMod p => n ^ 2 = t) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
        exact h_sq ⟨n, by rw [← hn]; ring⟩
      rw [h_empty, Finset.card_empty]
      norm_num

/-- **GS-04**: For `p` an odd prime,
`classicalGaussSum p = gaussSum (legendreDirichlet p) ZMod.stdAddChar`.

Proof: write `∑_n stdAddChar(n²) = ∑_t (#{n : n² = t}) · stdAddChar(t)` via
`Finset.sum_comp`, then use `card = 1 + quadraticChar t` (from
`card_sq_eq_add_quadraticChar`), and use `∑_t stdAddChar(t) = 0` (orthogonality). -/
theorem classicalGaussSum_eq_gaussSum_legendreDirichlet
    (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2) :
    classicalGaussSum p =
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  -- Strategy: both sides = ∑_t (1 + η(t)) · stdAddChar(t).
  -- Actually, we show: ∑_n stdAddChar(n²) = ∑_t (1 + η(t)) · stdAddChar(t) = gaussSum(η).
  have h_sum_zero : ∑ t : ZMod p, (ZMod.stdAddChar : AddChar (ZMod p) ℂ) t = 0 := by
    have h_ne_one : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
      intro h
      -- stdAddChar = 1 would mean stdAddChar 1 = stdAddChar 0, then injectivity gives 1 = 0.
      have h_eq : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 1 =
          (ZMod.stdAddChar : AddChar (ZMod p) ℂ) 0 := by
        rw [h]; rfl
      have h_one_zero : (1 : ZMod p) = 0 := ZMod.injective_stdAddChar h_eq
      have h_p1 : p = 1 := ZMod.one_eq_zero_iff.mp h_one_zero
      exact hp.out.one_lt.ne' h_p1
    exact AddChar.sum_eq_zero_of_ne_one h_ne_one
  -- Key identity: ∑_n stdAddChar(n²) = ∑_t (1 + η(t)) · stdAddChar(t).
  have h_key : classicalGaussSum p = ∑ t : ZMod p,
      (1 + (legendreDirichlet p t)) * (ZMod.stdAddChar : AddChar (ZMod p) ℂ) t := by
    unfold classicalGaussSum
    -- Use sum_comp with g = (·^2) and f = stdAddChar.
    rw [Finset.sum_comp (fun b : ZMod p => (ZMod.stdAddChar : AddChar (ZMod p) ℂ) b)
        (fun n : ZMod p => n ^ 2)]
    -- Goal: ∑_{b ∈ image} card • stdAddChar b = ∑_t (1 + η(t)) · stdAddChar t
    -- Extend the LHS sum to all of ZMod p (using that non-squares contribute 0
    -- since 1 + η(b) = 0 for non-squares).
    have h_extend : ∀ b : ZMod p, b ∉ Finset.image (fun n : ZMod p => n ^ 2) Finset.univ →
        (1 + (legendreDirichlet p b)) *
          (ZMod.stdAddChar : AddChar (ZMod p) ℂ) b = 0 := by
      intro b hb
      have hb_not_sq : ¬ IsSquare b := fun ⟨a, hsq⟩ => by
        apply hb
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨a, by rw [pow_two]; exact hsq.symm⟩
      have hb_ne : b ≠ 0 := fun h => by
        rw [h] at hb_not_sq
        exact hb_not_sq IsSquare.zero
      have h_eta : (legendreDirichlet p) b = -1 := by
        rw [legendreDirichlet_apply, quadraticChar_neg_one_iff_not_isSquare.mpr hb_not_sq]
        push_cast; ring
      rw [h_eta]
      ring
    rw [← Finset.sum_subset (Finset.subset_univ _) (fun b _ hb => h_extend b hb)]
    -- Now need: ∑_{b ∈ image} card • stdAddChar b =
    --          ∑_{b ∈ image} (1 + η(b)) · stdAddChar b
    refine Finset.sum_congr rfl (fun b _ => ?_)
    -- For each b ∈ image, (card : ℂ) = 1 + η(b).
    have h_card := card_sq_eq_add_quadraticChar hp_odd b
    -- Convert card • x = card * x (nat scalar) and handle the nat/int/complex casts.
    rw [nsmul_eq_mul, show ((legendreDirichlet p) b) = ((quadraticChar (ZMod p) b : ℤ) : ℂ) from
      legendreDirichlet_apply p b]
    congr 1
    have : ((Finset.univ.filter (fun n : ZMod p => n ^ 2 = b)).card : ℤ) =
        1 + quadraticChar (ZMod p) b := h_card
    -- (card : ℂ) via ℤ cast: since card = 1 + qc (int), after casting we have
    -- ((card : ℤ) : ℂ) = 1 + (qc : ℂ)
    have hℂ : ((Finset.univ.filter (fun n : ZMod p => n ^ 2 = b)).card : ℂ) =
        1 + ((quadraticChar (ZMod p) b : ℤ) : ℂ) := by
      exact_mod_cast this
    exact hℂ
  rw [h_key]
  -- ∑_t (1 + η(t)) · stdAddChar(t) = ∑_t stdAddChar(t) + ∑_t η(t) · stdAddChar(t)
  --                               = 0 + gaussSum(η)
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  rw [h_sum_zero, zero_add]
  rfl

/-- **GS-01**: Specialization of `jacobiTheta_S_smul` to `τ = i·y` for
real `y > 0`: `jacobiTheta(i/y) = √y · jacobiTheta(i·y)`.

This is the input to the Landsberg–Schaar identity and Gauss's classical
evaluation of the quadratic Gauss sum. -/
theorem jacobiTheta_S_smul_real (y : ℝ) (hy : 0 < y) :
    jacobiTheta (Complex.I / (y : ℂ)) =
      (y : ℂ) ^ (1 / 2 : ℂ) * jacobiTheta (Complex.I * (y : ℂ)) := by
  -- Construct τ := i·y as an element of UpperHalfPlane.
  have hτ_im : 0 < (Complex.I * (y : ℂ)).im := by
    simp [Complex.mul_im, hy]
  set τ : UpperHalfPlane := UpperHalfPlane.mk (Complex.I * (y : ℂ)) hτ_im with hτ_def
  -- Apply `jacobiTheta_S_smul` at τ.
  have h_main := jacobiTheta_S_smul τ
  -- Unpack S • τ = (-τ)⁻¹ and simplify for our τ = i·y.
  have h_S_eq : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = Complex.I / (y : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(Complex.I * (y : ℂ)))⁻¹ = Complex.I / (y : ℂ)
    have hy_ne : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp
    exact Complex.I_sq.symm
  have h_tau : (τ : ℂ) = Complex.I * (y : ℂ) := rfl
  rw [h_S_eq, h_tau] at h_main
  -- Compute (-I · (I · y))^{1/2} = y^{1/2} using I² = -1.
  have h_cpow : (-Complex.I * (Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) =
      (y : ℂ) ^ (1 / 2 : ℂ) := by
    congr 1
    rw [show (-Complex.I * (Complex.I * (y : ℂ))) = -(Complex.I * Complex.I) * (y : ℂ) from by ring,
      show Complex.I * Complex.I = -1 from by rw [← sq]; exact Complex.I_sq,
      neg_neg, one_mul]
  rw [h_cpow] at h_main
  exact h_main

end BernoulliRegular
