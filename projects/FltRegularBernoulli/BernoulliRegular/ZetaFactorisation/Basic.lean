module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Finite.Vector
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization

/-!
# Basic cyclotomic zeta-factorisation infrastructure

This module contains the setup and prime-by-prime local-factor calculations for
`BernoulliRegular.ZetaFactorisation`.
-/

@[expose] public section

noncomputable section

open NumberField
open Polynomial
open scoped Topology nonZeroDivisors

namespace BernoulliRegular

section ZetaFactorisation

noncomputable instance instFintypeSym (α : Type*) [Finite α] (n : ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

lemma neZero_p : NeZero p :=
  ⟨hp.1.ne_zero⟩

/-- A chosen multiplicative equivalence between complex-valued Dirichlet
characters mod `p` and the unit group `(ZMod p)ˣ`. -/
noncomputable def dirichletCharacterMulEquivUnits : DirichletCharacter ℂ p ≃* (ZMod p)ˣ := by
  letI : NeZero p := ⟨hp.1.ne_zero⟩
  exact (DirichletCharacter.mulEquiv_units ℂ p).some

/-- There are exactly `p - 1` complex-valued Dirichlet characters modulo `p`. -/
lemma card_dirichletCharacter_complex : Nat.card (DirichletCharacter ℂ p) = p - 1 := by
  letI := neZero_p (p := p)
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.1]

/-- For prime modulus `p`, the `L`-function of the trivial character is
`(1 - p^{-s}) ζ(s)`. -/
lemma LFunction_trivial_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar p s =
      (1 - (p : ℂ) ^ (-s)) * riemannZeta s := by
  letI := neZero_p (p := p)
  have hpf : Nat.primeFactors p = {p} := by
    simpa using (Nat.primeFactors_prime_pow (p := p) (k := 1) (by decide : (1 : ℕ) ≠ 0) hp.1)
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := p) hs]
  rw [hpf, Finset.prod_singleton]

/-- The cyclotomic field `K` has degree `p - 1` over `ℚ`. -/
lemma finrank_rat_eq_card_characters : Module.finrank ℚ K = Nat.card (DirichletCharacter ℂ p) := by
  rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
    Nat.totient_prime hp.1, card_dirichletCharacter_complex (p := p)]

/-! ### Step A — local factor definitions -/

/-- The rational prime ideal `(ℓ)` inside `ℤ`. -/
noncomputable def rationalPrimeIdeal (ℓ : ℕ) : Ideal ℤ :=
  Ideal.span ({(ℓ : ℤ)} : Set ℤ)

/-- The finite set of prime ideals of `𝓞 K` lying above `(ℓ)`. -/
noncomputable def primesOverFinset (ℓ : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 K)

/-- The nontrivial Dirichlet characters mod `p`, as a finite set. -/
noncomputable def nontrivialCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.erase 1

/-- The even nontrivial Dirichlet characters mod `p`, as a finite set. -/
noncomputable def evenNontrivialCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Even ∧ χ ≠ 1

/-- The odd Dirichlet characters mod `p`, as a finite set. -/
noncomputable def oddCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Odd

/-- The inverse of an odd Dirichlet character stays in `oddCharacters`. -/
theorem inv_mem_oddCharacters (p : ℕ) {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ oddCharacters p) : χ⁻¹ ∈ oddCharacters p := by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hχ_odd : χ.Odd := (Finset.mem_filter.mp hχ).2
  rw [DirichletCharacter.Odd] at hχ_odd ⊢
  rw [MulChar.inv_apply_eq_inv', hχ_odd]
  norm_num

/-- The character-side local Euler factor at a rational prime `ℓ`. -/
noncomputable def charLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ p, (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The nontrivial part of the character-side local Euler factor. -/
noncomputable def nontrivialCharLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (nontrivialCharacters (p := p)) fun χ =>
    (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The even nontrivial part of the character-side local Euler factor. -/
noncomputable def evenCharLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ =>
    (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The odd part of the character-side local Euler factor. -/
noncomputable def oddCharLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (oddCharacters (p := p)) fun χ =>
    (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))

/-- The Dedekind-side local Euler factor at a rational prime `ℓ`, written as a
finite product over the primes of `𝓞 K` lying above `(ℓ)`. -/
noncomputable def dedekindLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (primesOverFinset K ℓ) fun P =>
    (1 - (Ideal.absNorm P : ℂ) ^ (-s))

/-- The global product of Dirichlet `L`-functions over all characters mod `p`. -/
noncomputable def LProduct (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ p, DirichletCharacter.LFunction χ s

/-- The nontrivial part of the global `L`-product. -/
noncomputable def nontrivialLProduct (s : ℂ) : ℂ :=
  Finset.prod (nontrivialCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s

/-- The even nontrivial part of the global `L`-product. -/
noncomputable def evenLProduct (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ =>
    DirichletCharacter.LFunction χ s

/-- The odd part of the global `L`-product. -/
noncomputable def oddLProduct (s : ℂ) : ℂ :=
  Finset.prod (oddCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s

/-- The distinguished primitive `p`-th root of unity viewed in `𝓞 K`. -/
noncomputable def zetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger

/-! ### Step B — easy analytic rewrites -/

/-! ### Step C — character-side local factor skeleton -/

/-- If `ℓ` is a prime different from `p`, then `p` and `ℓ` are coprime. -/
lemma coprime_of_prime_ne {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : p.Coprime ℓ :=
  (Nat.coprime_primes hp.out (Fact.out : ℓ.Prime)).mpr (Ne.symm hℓp)

/-- The unit of `(ZMod p)ˣ` represented by a prime `ℓ ≠ p`. -/
noncomputable def unitOfPrimeNe (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ℓ (coprime_of_prime_ne (p := p) hℓp).symm

/-- The residue-degree candidate on the character side: the order of `ℓ mod p`
inside `(ZMod p)ˣ`. -/
noncomputable def localResidueDegree (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  orderOf (unitOfPrimeNe (p := p) ℓ hℓp)

/-- The expected number of primes above `ℓ ≠ p`, inferred from the character
group cardinality. -/
noncomputable def localPrimeCount (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  Nat.card (DirichletCharacter ℂ p) / localResidueDegree (p := p) ℓ hℓp

lemma localResidueDegree_dvd_card_characters {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localResidueDegree (p := p) ℓ hℓp ∣ Nat.card (DirichletCharacter ℂ p) := by
  rw [card_dirichletCharacter_complex (p := p)]
  simpa [localResidueDegree, ZMod.card_units p] using
    (orderOf_dvd_card (x := unitOfPrimeNe (p := p) ℓ hℓp))

lemma localPrimeCount_mul_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCount (p := p) ℓ hℓp * localResidueDegree (p := p) ℓ hℓp =
      Nat.card (DirichletCharacter ℂ p) :=
  Nat.div_mul_cancel (localResidueDegree_dvd_card_characters (p := p) hℓp)

lemma charLocalFactor_eq_trivial_mul_nontrivial {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    charLocalFactor (p := p) ℓ s =
      (1 - (ℓ : ℂ) ^ (-s)) * nontrivialCharLocalFactor p ℓ s := by
  classical
  unfold charLocalFactor nontrivialCharLocalFactor
  rw [show nontrivialCharacters (p := p) = Finset.univ.erase 1 from rfl,
    ← Finset.mul_prod_erase Finset.univ
      (fun χ : DirichletCharacter ℂ p => 1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))
      (Finset.mem_univ 1)]
  have hℓ_unit : IsUnit ((ℓ : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (coprime_of_prime_ne (p := p) hℓp).symm
  rw [MulChar.one_apply hℓ_unit, one_mul]

lemma nontrivialCharLocalFactor_eq_even_mul_odd {ℓ : ℕ} {s : ℂ} :
    nontrivialCharLocalFactor p ℓ s =
      evenCharLocalFactor p ℓ s * oddCharLocalFactor p ℓ s := by
  classical
  unfold nontrivialCharLocalFactor evenCharLocalFactor oddCharLocalFactor
    nontrivialCharacters evenNontrivialCharacters oddCharacters
  have hdisj : Disjoint
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion : Finset.univ.erase (1 : DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    ext χ
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      and_true, true_and]
    refine ⟨fun hne => ?_, ?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he, hne⟩
      · exact Or.inr ho
    · rintro (⟨_, hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1 : DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion, Finset.prod_union hdisj]

lemma char_values_factor_through_unit_order {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (χ : DirichletCharacter ℂ p) :
    χ (ℓ : ZMod p) ^ localResidueDegree (p := p) ℓ hℓp = 1 := by
  have hval : ((unitOfPrimeNe p ℓ hℓp : (ZMod p)ˣ) : ZMod p) = (ℓ : ZMod p) := by
    simp [unitOfPrimeNe]
  unfold localResidueDegree
  rw [← hval, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
    Units.val_one, map_one]

/-- Classical polynomial identity in `ℂ`: the product of `(1 - ζ T)` over all
`d`-th roots of unity equals `1 - T^d`. -/
lemma prod_nthRootsFinset_one_sub_mul (d : ℕ) (hd : 0 < d) (T : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) = 1 - T ^ d := by
  by_cases hT : T = 0
  · subst hT; simp [zero_pow hd.ne']
  · have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard : (Polynomial.nthRootsFinset d (1 : ℂ)).card = d := hζ.card_nthRootsFinset
    have hpoly : Polynomial.X ^ d - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ),
        (Polynomial.X - Polynomial.C ζ) := Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval := congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at heval
    have key : ∀ ζ : ℂ, (1 - ζ * T) = T * (T⁻¹ - ζ) := fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _ => key ζ), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, ← heval]
    have hTT : T ^ d * T⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT, one_pow]
    linear_combination hTT

/-- Helper: if `ω` is a primitive `n`-th root of unity, then for any `a : ℕ`,
`ω^a` is a primitive `(n / gcd(n, a))`-th root of unity.

This generalises `IsPrimitiveRoot.pow_of_coprime` to arbitrary exponents. -/
lemma _root_.IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd
    {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : M} (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ a) (n / n.gcd a) := by
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  obtain ⟨a', ha'⟩ := hc_dvd_a
  have ha'_cop : a'.Coprime d := by
    have key : c * Nat.gcd a' d = c * 1 := by
      rw [mul_one]
      calc c * Nat.gcd a' d
          = (c * a').gcd (c * d) := (Nat.gcd_mul_left c a' d).symm
        _ = a.gcd n := by rw [← ha', hc_mul_d]
        _ = c := by rw [Nat.gcd_comm]
    exact Nat.eq_of_mul_eq_mul_left hc_pos key
  have hω_c : IsPrimitiveRoot (ω ^ c) d := hω.pow hn hc_mul_d.symm
  rw [ha', pow_mul]
  exact hω_c.pow_of_coprime _ ha'_cop

/-- Polynomial identity: for `ω` a primitive `n`-th root of unity in `ℂ` and any
`a : ℕ`, `∏_{k = 0..n-1} (1 - ω^{ka} T) = (1 - T^{n/gcd(n,a)})^{gcd(n,a)}`. -/
lemma prod_pow_primRoot_eq_pow {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω n) (T : ℂ) :
    ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) =
      (1 - T ^ (n / n.gcd a)) ^ n.gcd a := by
  classical
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n : d ∣ n := ⟨c, by rw [mul_comm]; exact hc_mul_d.symm⟩
  have hω_a_prim : IsPrimitiveRoot (ω ^ a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period : ∀ k : ℕ, ω ^ (k * a) = ω ^ ((k % d) * a) := by
    intro k
    have hkd : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
    have h_da : ω ^ ((k / d) * (d * a)) = 1 := by
      obtain ⟨a', ha'⟩ := hc_dvd_a
      rw [ha', show (k / d) * (d * (c * a')) = (k / d) * a' * (c * d) from by ring, hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k / d) * a', mul_comm _ _⟩
    conv_lhs => rw [hkd]
    rw [show (d * (k / d) + k % d) * a = (k % d) * a + (k / d) * (d * a) from by ring, pow_add,
      h_da, mul_one]
  rw [show (∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T)) =
      ∏ k ∈ Finset.range n, (1 - ω ^ ((k % d) * a) * T) from
    Finset.prod_congr rfl (fun k _ => by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun k : ℕ => k % d) (t := Finset.range d)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner : ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k % d = j), (1 - ω ^ ((k % d) * a) * T)) =
      (1 - ω ^ (j * a) * T) ^ c := by
    intro j hj
    have h_rewrite : ∀ k ∈ (Finset.range n).filter (fun k => k % d = j),
        (1 - ω ^ ((k % d) * a) * T) = (1 - ω ^ (j * a) * T) := fun k hk => by
      rw [Finset.mem_filter] at hk; rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite, Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c', hcd'⟩ := hd_dvd_n
    have hc_eq : c = c' := by
      have hd_mul : d * c = n := by rw [mul_comm, hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul, hcd'])
    rw [hc_eq]
    have hset : (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      refine ⟨fun ⟨hk_lt, hk_mod⟩ => ?_, ?_⟩
      · have hk_dec : k = j + (k / d) * d := by
          have h1 : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
          rw [hk_mod, mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d, ?_, hk_dec.symm⟩
        have h_lt_cd : (k / d) * d < c' * d := by
          have h_le : (k / d) * d ≤ k := Nat.div_mul_le_self k d
          rw [mul_comm c' d, ← hcd']; omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m, hm_lt, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hcd', mul_comm]; nlinarith
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hset, Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner, Finset.prod_pow]
  congr 1
  have h_inj : Set.InjOn (fun j : ℕ => (ω ^ a) ^ j) ↑(Finset.range d) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image : Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image, Finset.mem_range] at hζ
      obtain ⟨j, _, rfl⟩ := hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos, ← pow_mul, mul_comm j d, pow_mul,
        hω_a_prim.pow_eq_one, one_pow]
    · rw [hω_a_prim.card_nthRootsFinset, Finset.card_image_of_injOn h_inj, Finset.card_range]
  calc ∏ j ∈ Finset.range d, (1 - ω ^ (j * a) * T)
      = ∏ j ∈ Finset.range d, (1 - (ω ^ a) ^ j * T) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul, mul_comm a j]
    _ = ∏ ζ ∈ Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d), (1 - ζ * T) := by
        rw [Finset.prod_image h_inj]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) := by rw [h_image]
    _ = 1 - T ^ d := prod_nthRootsFinset_one_sub_mul d hd_pos T

/-- The classical finite-group character identity:
for `u : (ZMod p)ˣ` with `orderOf u = d`, as `χ` ranges over
`DirichletCharacter ℂ p`, the values `χ(u)` hit each `d`-th root of unity
exactly `(p - 1) / d` times, so the product `∏_χ (1 - χ(u) T)` is
`(1 - T^d)^{(p-1)/d}`. -/
lemma prod_characters_eval_eq_pow (u : (ZMod p)ˣ) (T : ℂ) :
    (∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T)) =
      (1 - T ^ orderOf u) ^ (Nat.card (DirichletCharacter ℂ p) / orderOf u) := by
  classical
  set d := orderOf u with hd_def
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by rw [← hn_units]; exact Fintype.card_pos
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' u
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]; exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']; exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hd_eq : d = n / n.gcd a := by
    have hfin : IsOfFinOrder g := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n, hn_pos, by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
    have : d = orderOf (g ^ a) := by rw [hd_def, ← ha]
    rw [this, hfin.orderOf_pow, hg_order]
  have hn_div_d : n / d = n.gcd a := by
    have hcd : n.gcd a ∣ n := Nat.gcd_dvd_left n a
    rw [hd_eq, Nat.div_div_self hcd hn_pos.ne']
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hχAt_u : ∀ k : ℕ, χAt k (u : ZMod p) = ω ^ (k * a) := fun k => by
    have hu_eq : (u : ZMod p) = ((g : (ZMod p)ˣ) : ZMod p) ^ a := by
      rw [← Units.val_pow_eq_pow_val, ha]
    rw [hu_eq, map_pow, hχAt_g, ← pow_mul]
  have hχAt_inj : Set.InjOn χAt ↑(Finset.range n) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χAt j ((g : (ZMod p)ˣ) : ZMod p) = χAt k ((g : (ZMod p)ˣ) : ZMod p) := by
      rw [hjk]
    rw [hχAt_g, hχAt_g] at hval
    exact hω.pow_inj hj hk hval
  have hχAt_surj_onto_univ :
      Finset.image χAt (Finset.range n) = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun _ _ => Finset.mem_univ _
    · rw [Finset.card_image_of_injOn hχAt_inj, Finset.card_range, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
  have h_transfer :
      ∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T) =
      ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) := by
    calc ∏ χ : DirichletCharacter ℂ p, (1 - χ (u : ZMod p) * T)
        = ∏ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)), (1 - χ (u : ZMod p) * T) := rfl
      _ = ∏ χ ∈ Finset.image χAt (Finset.range n), (1 - χ (u : ZMod p) * T) := by
          rw [hχAt_surj_onto_univ]
      _ = ∏ k ∈ Finset.range n, (1 - (χAt k) (u : ZMod p) * T) := by
          rw [Finset.prod_image hχAt_inj]
      _ = ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) := by
          refine Finset.prod_congr rfl (fun k _ => ?_)
          rw [hχAt_u k]
  rw [h_transfer, prod_pow_primRoot_eq_pow hn_pos a hω T, ← hd_eq, hn_div_d]

lemma prod_nontrivial_characters_eval_eq_even_mul_odd (u : (ZMod p)ˣ) (T : ℂ) :
    Finset.prod (nontrivialCharacters (p := p)) (fun χ => (1 - χ (u : ZMod p) * T)) =
      Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => (1 - χ (u : ZMod p) * T)) *
        Finset.prod (oddCharacters (p := p)) (fun χ => (1 - χ (u : ZMod p) * T)) := by
  classical
  unfold nontrivialCharacters evenNontrivialCharacters oddCharacters
  have hdisj : Disjoint
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion : Finset.univ.erase (1 : DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Odd) := by
    ext χ
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      and_true, true_and]
    refine ⟨fun hne => ?_, ?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he, hne⟩
      · exact Or.inr ho
    · rintro (⟨_, hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1 : DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion, Finset.prod_union hdisj]

lemma charLocalFactor_prime_ne_p_via_unit_order {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    charLocalFactor (p := p) ℓ s =
      (1 - ((ℓ : ℂ) ^ (-s)) ^ localResidueDegree (p := p) ℓ hℓp) ^
        (Nat.card (DirichletCharacter ℂ p) / localResidueDegree (p := p) ℓ hℓp) := by
  have hval : ((unitOfPrimeNe p ℓ hℓp : (ZMod p)ˣ) : ZMod p) = (ℓ : ZMod p) := by
    simp [unitOfPrimeNe]
  unfold charLocalFactor
  rw [← hval]
  unfold localResidueDegree
  exact prod_characters_eval_eq_pow p (unitOfPrimeNe p ℓ hℓp) ((ℓ : ℂ) ^ (-s))

/-- The fiber-size is constant for `χ ↦ χ(ℓ)` over its image (the
`localResidueDegree`-th roots of unity in `ℂ`). Each element of the image
is hit exactly `localPrimeCount = (p-1)/localResidueDegree` times.

Hypothesis `hz : z^(localResidueDegree p ℓ hℓp) = 1` restricts `z` to be
in the image; without it, the subtype can be empty and the statement fails. -/
lemma character_eval_fiber_card_constant {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {z : ℂ} (hz : z ^ localResidueDegree (p := p) ℓ hℓp = 1) :
    Nat.card {χ : DirichletCharacter ℂ p // χ (ℓ : ZMod p) = z} =
      localPrimeCount (p := p) ℓ hℓp := by
  classical
  set d := localResidueDegree (p := p) ℓ hℓp with hd_def
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by rw [← hn_units]; exact Fintype.card_pos
  have hd_pos : 0 < d := orderOf_pos _
  have hd_dvd_n : d ∣ n := by
    rw [hd_def]; exact localResidueDegree_dvd_card_characters (p := p) hℓp
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' (unitOfPrimeNe p ℓ hℓp)
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]; exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']; exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hd_eq : d = n / n.gcd a := by
    have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr
      ⟨n, hn_pos, by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
    rw [hd_def, localResidueDegree, ← ha, hfin.orderOf_pow, hg_order]
  have hn_div_d : n / d = n.gcd a := by
    rw [hd_eq, Nat.div_div_self (Nat.gcd_dvd_left n a) hn_pos.ne']
  have hℓ_eq : ((ℓ : ZMod p)) = (((g : (ZMod p)ˣ) : ZMod p)) ^ a := by
    have h1 : ((unitOfPrimeNe p ℓ hℓp : (ZMod p)ˣ) : ZMod p) = (ℓ : ZMod p) := by
      simp [unitOfPrimeNe]
    rw [← h1, ← ha, Units.val_pow_eq_pow_val]
  have hχAt_ℓ : ∀ k : ℕ, χAt k (ℓ : ZMod p) = ω ^ (k * a) := fun k => by
    rw [hℓ_eq, map_pow, hχAt_g, ← pow_mul]
  have hχAt_inj : Set.InjOn χAt ↑(Finset.range n) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χAt j ((g : (ZMod p)ˣ) : ZMod p) = χAt k ((g : (ZMod p)ˣ) : ZMod p) := by
      rw [hjk]
    rw [hχAt_g, hχAt_g] at hval
    exact hω.pow_inj hj hk hval
  have hχAt_surj_onto_univ :
      Finset.image χAt (Finset.range n) = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun _ _ => Finset.mem_univ _
    · rw [Finset.card_image_of_injOn hχAt_inj, Finset.card_range, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
  have h_card_eq :
      Nat.card {χ : DirichletCharacter ℂ p // χ (ℓ : ZMod p) = z} =
      ((Finset.range n).filter (fun k => ω ^ (k * a) = z)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    symm
    apply Finset.card_bij (fun k _ => χAt k)
    · intro k hk
      rw [Finset.mem_filter] at hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [hχAt_ℓ]; exact hk.2
    · intro j hj k hk hjk
      rw [Finset.mem_filter] at hj hk
      refine hχAt_inj ?_ ?_ hjk
      · exact Finset.mem_coe.mpr hj.1
      · exact Finset.mem_coe.mpr hk.1
    · intro χ hχ
      rw [Finset.mem_filter] at hχ
      have hχ_in_univ : χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)) := Finset.mem_univ _
      rw [← hχAt_surj_onto_univ, Finset.mem_image] at hχ_in_univ
      obtain ⟨k, hk_range, rfl⟩ := hχ_in_univ
      refine ⟨k, ?_, rfl⟩
      refine Finset.mem_filter.mpr ⟨hk_range, ?_⟩
      rw [← hχAt_ℓ]; exact hχ.2
  rw [h_card_eq]
  have hω_a_prim : IsPrimitiveRoot (ω ^ a) d := by
    rw [hd_eq]; exact IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos a hω
  have hz' : z ∈ Polynomial.nthRootsFinset d (1 : ℂ) := by
    rw [Polynomial.mem_nthRootsFinset hd_pos]; exact hz
  have h_image : Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image, Finset.mem_range] at hζ
      obtain ⟨j, _, rfl⟩ := hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos, ← pow_mul, mul_comm j d, pow_mul,
        hω_a_prim.pow_eq_one, one_pow]
    · rw [hω_a_prim.card_nthRootsFinset, Finset.card_image_of_injOn, Finset.card_range]
      intro x hx y hy hxy
      simp only [Finset.coe_range, Set.mem_Iio] at hx hy
      exact hω_a_prim.pow_inj hx hy hxy
  rw [← h_image] at hz'
  simp only [Finset.mem_image, Finset.mem_range] at hz'
  obtain ⟨j, hj_lt, hj_eq⟩ := hz'
  have h_filter : (Finset.range n).filter (fun k => ω ^ (k * a) = z) =
      (Finset.range n).filter (fun k => k % d = j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right (fun hk_lt => ?_)
    have h_pow_mod : ω ^ (k * a) = (ω ^ a) ^ (k % d) := by
      have h1 : ω ^ (k * a) = ω ^ ((k % d) * a) := by
        have hk_split : k * a = (k % d) * a + (k / d) * (d * a) := by
          have := Nat.div_add_mod k d
          nlinarith
        rw [hk_split, pow_add]
        have h_da : ω ^ ((k / d) * (d * a)) = 1 := by
          apply (hω.pow_eq_one_iff_dvd _).mpr
          have hn_dvd_da : n ∣ d * a := by
            have hga : n.gcd a ∣ a := Nat.gcd_dvd_right n a
            have hd_mul_gcd : d * n.gcd a = n := by
              rw [hd_eq, Nat.div_mul_cancel (Nat.gcd_dvd_left n a)]
            refine ⟨a / n.gcd a, ?_⟩
            calc d * a = d * (n.gcd a * (a / n.gcd a)) := by rw [Nat.mul_div_cancel' hga]
              _ = (d * n.gcd a) * (a / n.gcd a) := by ring
              _ = n * (a / n.gcd a) := by rw [hd_mul_gcd]
          exact Dvd.dvd.mul_left hn_dvd_da _
        rw [h_da, mul_one]
      rw [h1, ← pow_mul, mul_comm]
    rw [h_pow_mod, ← hj_eq]
    refine ⟨fun h => hω_a_prim.pow_inj (Nat.mod_lt _ hd_pos) hj_lt h, fun h => by rw [h]⟩
  rw [h_filter]
  have hfs : ((Finset.range n).filter (fun k => k % d = j)).card = n / d := by
    obtain ⟨c', hcd'⟩ := hd_dvd_n
    have h_n_div : n / d = c' := by rw [hcd', Nat.mul_div_cancel_left _ hd_pos]
    rw [h_n_div]
    have hset : (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      refine ⟨fun ⟨hk_lt, hk_mod⟩ => ?_, ?_⟩
      · have hk_dec : k = j + (k / d) * d := by
          have h1 : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
          rw [hk_mod, mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d, ?_, hk_dec.symm⟩
        have h_lt_cd : (k / d) * d < c' * d := by
          have h_le : (k / d) * d ≤ k := Nat.div_mul_le_self k d
          rw [mul_comm c' d, ← hcd']; omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m, hm_lt, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hcd', mul_comm]; nlinarith
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj_lt]
    rw [hset, Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [hfs, localPrimeCount, ← hd_def]

lemma charLocalFactor_eq_pow_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    charLocalFactor (p := p) ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCount (p := p) ℓ hℓp := by
  rw [charLocalFactor_prime_ne_p_via_unit_order (p := p) hℓp,
    show ((ℓ : ℂ) ^ (-s)) ^ localResidueDegree (p := p) ℓ hℓp =
        (ℓ : ℂ) ^ (-((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s) by
      rw [show -((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s =
          (-s) * ((localResidueDegree (p := p) ℓ hℓp : ℕ) : ℂ) by ring,
        Complex.cpow_mul_nat]]
  rfl

/-- At `ℓ = p`, every Dirichlet character `χ` mod `p` vanishes at `(p : ZMod p) = 0`
(since `0` is not a unit), so each factor `(1 - χ(p)·p^{-s})` equals `1` and the
full character-side local factor is `1`. This differs from the Dedekind-side
local factor `1 - p^{-s}` by exactly the `(1 - p^{-s})` factor distinguishing
`LFunctionTrivChar p s` from the primitive `ζ(s)`. -/
lemma charLocalFactor_at_p {s : ℂ} :
    charLocalFactor (p := p) p s = 1 :=
  Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]

/-! ### Step D — Dedekind-side local factor skeleton -/

lemma primesOverFinset_card_eq_ncard (ℓ : ℕ) [Fact ℓ.Prime] :
    (primesOverFinset K ℓ).card =
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)).ncard := by
  classical
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  unfold primesOverFinset
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hne]

lemma mem_primesOverFinset_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)} :
    P ∈ primesOverFinset K ℓ ↔ P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
  haveI : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)

noncomputable def primesOverSubtypeEquivFinset (ℓ : ℕ) [Fact ℓ.Prime] :
    {P : Ideal (𝓞 K) // P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)} ≃
      {P : Ideal (𝓞 K) // P ∈ primesOverFinset K ℓ} :=
  Equiv.subtypeEquivProp (funext fun _ => propext
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).symm)

lemma zetaInteger_isIntegralGenerator :
    Algebra.adjoin ℤ ({zetaInteger (p := p) (K := K)} : Set (𝓞 K)) = ⊤ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec p ℚ K)

lemma zetaInteger_exponent_eq_one :
    RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (zetaInteger_isIntegralGenerator (p := p) (K := K))

lemma prime_not_dvd_zetaInteger_exponent {ℓ : ℕ} [Fact ℓ.Prime] :
    ¬ ℓ ∣ RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) := by
  rw [zetaInteger_exponent_eq_one]
  exact Nat.Prime.not_dvd_one (Fact.out : ℓ.Prime)

noncomputable def primesOverEquivMonicFactorsMod (ℓ : ℕ) [Fact ℓ.Prime] :
  Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) ≃
      RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := K) (θ := zetaInteger (p := p) (K := K))
    (p := ℓ) (prime_not_dvd_zetaInteger_exponent (p := p) (K := K) (ℓ := ℓ))

lemma monicFactorsMod_natDegree_eq_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (Q : (ZMod ℓ)[X])
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ)) :
    Q.natDegree = localResidueDegree (p := p) ℓ hℓp := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hmin : minpoly ℤ (zetaInteger (p := p) (K := K)) = cyclotomic p ℤ := by
    rw [zetaInteger, ← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  have hcop : ℓ.Coprime p := (coprime_of_prime_ne (p := p) hℓp).symm
  have hFcard : Fintype.card (ZMod ℓ) = ℓ ^ 1 := by
    rw [pow_one]; exact ZMod.card ℓ
  have hQmem : Q ∈ UniqueFactorizationMonoid.normalizedFactors
      (cyclotomic p (ZMod ℓ)) := by
    have hQ' : Q ∈ (UniqueFactorizationMonoid.normalizedFactors
        (map (Int.castRingHom (ZMod ℓ)) (minpoly ℤ (zetaInteger (p := p) (K := K))))).toFinset := hQ
    rw [hmin, Polynomial.map_cyclotomic_int] at hQ'
    exact Multiset.mem_toFinset.mp hQ'
  rw [Polynomial.natDegree_of_mem_normalizedFactors_cyclotomic hFcard hcop hQmem]
  unfold localResidueDegree unitOfPrimeNe
  rw [← orderOf_units (y := ZMod.unitOfCoprime _ _), ← orderOf_units (y := ZMod.unitOfCoprime ℓ _),
    ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, pow_one]

lemma monicFactorsMod_card_eq_localPrimeCount {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ)).card =
      localPrimeCount (p := p) ℓ hℓp := by
  classical
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hmin : minpoly ℤ (zetaInteger (p := p) (K := K)) = cyclotomic p ℤ := by
    rw [zetaInteger, ← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  have hcop : ℓ.Coprime p := (coprime_of_prime_ne (p := p) hℓp).symm
  have hFcard : Fintype.card (ZMod ℓ) = ℓ ^ 1 := by
    rw [pow_one]; exact ZMod.card ℓ
  unfold RingOfIntegers.monicFactorsMod
  rw [hmin, Polynomial.map_cyclotomic_int,
    Polynomial.normalizedFactors_cyclotomic_card hFcard hcop]
  unfold localPrimeCount localResidueDegree unitOfPrimeNe
  rw [card_dirichletCharacter_complex (p := p), Nat.totient_prime hp.out,
    ← orderOf_units (y := ZMod.unitOfCoprime _ _), ← orderOf_units (y := ZMod.unitOfCoprime ℓ _),
    ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, pow_one]

lemma cyclotomic_mod_p_eq_X_sub_one_pow :
    map (Int.castRingHom (ZMod p))
        (minpoly ℤ (zetaInteger (p := p) (K := K))) =
      (X - 1) ^ (p - 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hmin : minpoly ℤ (zetaInteger (p := p) (K := K)) = cyclotomic p ℤ := by
    rw [zetaInteger, ← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  rw [hmin, Polynomial.map_cyclotomic_int]
  have h1 : (cyclotomic p (ZMod p)) * (X - 1) = X ^ p - 1 :=
    cyclotomic_prime_mul_X_sub_one (ZMod p) p
  have h2 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right X)]; ring
  have hne : (X - 1 : (ZMod p)[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hpow : (X - 1 : (ZMod p)[X]) ^ p = (X - 1) ^ (p - 1) * (X - 1) := by
    have hpos : 0 < p := hp.out.pos
    rw [← pow_succ]; congr 1; omega
  refine mul_right_cancel₀ hne ?_
  rw [← hpow, h2, ← h1]

lemma monicFactorsMod_at_p_singleton :
    (RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := p)).card = 1 := by
  classical
  unfold RingOfIntegers.monicFactorsMod
  rw [cyclotomic_mod_p_eq_X_sub_one_pow (p := p) (K := K)]
  have hirr : Irreducible (X - 1 : (ZMod p)[X]) :=
    irreducible_X_sub_C 1
  rw [hirr.normalizedFactors_pow, Multiset.toFinset_replicate]
  have hp_pos : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  simp [hp_pos]

lemma ncard_primesOver_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)).ncard = 1 := by
  classical
  rw [← monicFactorsMod_at_p_singleton (p := p) (K := K),
    ← Nat.card_coe_set_eq, Nat.card_congr (primesOverEquivMonicFactorsMod (p := p) (K := K) p),
    Nat.card_eq_finsetCard]

lemma primesOver_inertiaDeg_eq_one_at_p (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)) :
    (rationalPrimeIdeal p).inertiaDeg P = 1 := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP.2
  haveI hbase : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime p
  haveI hPmax : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (p := Ideal.span {(p : ℤ)}) (P := P)
  simp only [rationalPrimeIdeal, Ideal.inertiaDeg_eq_inertiaDeg']
  exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K P

lemma primesOver_ramificationIdx_eq_prime_sub_one_at_p (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)) :
    (rationalPrimeIdeal p).ramificationIdx P = p - 1 := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP.2
  have hp_ne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp [hp.out.ne_zero]
  simp only [rationalPrimeIdeal]
  rw [Ideal.ramificationIdx_eq_ramificationIdx' (Ideal.span {(p : ℤ)}) P hp_ne]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p K P

lemma primesOver_at_p_package :
    (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K),
      (rationalPrimeIdeal p).inertiaDeg P = 1) ∧
    (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K),
      (rationalPrimeIdeal p).ramificationIdx P = p - 1) ∧
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)).ncard = 1 :=
  ⟨primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K),
   primesOver_ramificationIdx_eq_prime_sub_one_at_p (p := p) (K := K),
   ncard_primesOver_at_p_eq_one (p := p) (K := K)⟩

lemma primesOver_inertiaDeg_eq_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    (rationalPrimeIdeal ℓ).inertiaDeg P = localResidueDegree (p := p) ℓ hℓp := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  haveI hbase : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  haveI hPmax : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal (p := Ideal.span {(ℓ : ℤ)}) (P := P)
  simp only [rationalPrimeIdeal, Ideal.inertiaDeg_eq_inertiaDeg',
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd ℓ K P hcop]
  unfold localResidueDegree unitOfPrimeNe
  rw [← orderOf_units]
  rfl

lemma primesOver_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    (rationalPrimeIdeal ℓ).ramificationIdx P = 1 := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  have hℓ_ne : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp [(Fact.out : ℓ.Prime).ne_zero]
  simp only [rationalPrimeIdeal]
  rw [Ideal.ramificationIdx_eq_ramificationIdx' (Ideal.span {(ℓ : ℤ)}) P hℓ_ne]
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hcop

lemma ncard_primesOver_eq_localPrimeCount {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)).ncard =
      localPrimeCount (p := p) ℓ hℓp := by
  classical
  rw [← monicFactorsMod_card_eq_localPrimeCount (p := p) (K := K) hℓp,
    ← Nat.card_coe_set_eq, Nat.card_congr (primesOverEquivMonicFactorsMod (p := p) (K := K) ℓ),
    Nat.card_eq_finsetCard]

lemma primesOver_prime_ne_p_package {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K),
      (rationalPrimeIdeal ℓ).inertiaDeg P = localResidueDegree (p := p) ℓ hℓp) ∧
    (∀ P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K),
      (rationalPrimeIdeal ℓ).ramificationIdx P = 1) ∧
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)).ncard =
      localPrimeCount (p := p) ℓ hℓp :=
  ⟨primesOver_inertiaDeg_eq_localResidueDegree p K hℓp,
   primesOver_ramificationIdx_eq_one p K hℓp,
   ncard_primesOver_eq_localPrimeCount p K hℓp⟩

lemma dedekindLocalFactor_eq_pow_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) {s : ℂ} :
    dedekindLocalFactor K ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCount (p := p) ℓ hℓp := by
  classical
  haveI : (rationalPrimeIdeal ℓ).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcoe := IsDedekindDomain.coe_primesOverFinset (p := rationalPrimeIdeal ℓ) hne (𝓞 K)
  have hcard_eq : (primesOverFinset K ℓ).card = localPrimeCount (p := p) ℓ hℓp := by
    have h1 := ncard_primesOver_eq_localPrimeCount p K hℓp
    rw [← hcoe, Set.ncard_coe_finset] at h1
    exact h1
  unfold dedekindLocalFactor
  have hprod_eq : ∀ P ∈ primesOverFinset K ℓ,
      (1 - (Ideal.absNorm P : ℂ) ^ (-s)) =
        1 - (ℓ : ℂ) ^ (-(localResidueDegree (p := p) ℓ hℓp : ℂ) * s) := by
    intro P hP
    have hPmem : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
      have : (P : Ideal _) ∈
          (↑(IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 K)) : Set _) :=
        hP
      rwa [hcoe] at this
    haveI : P.IsPrime := hPmem.1
    haveI : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hPmem.2
    have habsNorm : Ideal.absNorm P = ℓ ^ (localResidueDegree (p := p) ℓ hℓp) := by
      rw [← primesOver_inertiaDeg_eq_localResidueDegree p K hℓp P hPmem]
      exact Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out : ℓ.Prime)
    rw [habsNorm]
    push_cast
    have := Complex.natCast_cpow_natCast_mul ℓ (localResidueDegree (p := p) ℓ hℓp) (-s)
    rw [show -((localResidueDegree (p := p) ℓ hℓp : ℂ)) * s =
        ((localResidueDegree (p := p) ℓ hℓp : ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq, Finset.prod_const, hcard_eq]

lemma dedekindLocalFactor_at_p {s : ℂ} :
    dedekindLocalFactor K p s = 1 - (p : ℂ) ^ (-s) := by
  classical
  unfold dedekindLocalFactor primesOverFinset rationalPrimeIdeal
  have hne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p := (Ideal.span {(p : ℤ)} : Ideal ℤ)) hne (𝓞 K)
  have hcard :
      (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)} : Ideal ℤ) (𝓞 K)).card = 1 := by
    have hncard : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by
      simpa [rationalPrimeIdeal] using ncard_primesOver_at_p_eq_one (p := p) (K := K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨P, hP⟩ := Finset.card_eq_one.mp hcard
  rw [hP, Finset.prod_singleton]
  have hPmem : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [← hcoe]; rw [hP]; exact Finset.mem_singleton_self P
  haveI : P.IsPrime := hPmem.1
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPmem.2
  have habsNorm : Ideal.absNorm P = p ^ (1 : ℕ) := by
    rw [← primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) P]
    · exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
    · simpa [rationalPrimeIdeal] using hPmem
  rw [habsNorm]
  push_cast
  rw [pow_one]

end ZetaFactorisation

end BernoulliRegular
