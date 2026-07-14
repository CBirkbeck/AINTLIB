/-
Copyright (c) 2026 the AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ModularCurves.LevelStructure.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Multiplicity

/-!
# KM-INTEGRAL stream skeleton: the Drinfeld upgrade of Y₁(N) (Katz–Mazur Ch. 5)

Skeleton for the KM-INTEGRAL stream (see `decomposition-km-integral.md`): the regularity
theory of the moduli problem of Drinfeld `[Γ₁(N)]`-structures over all of `ℤ`, following
Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 5 (print pages 129–141;
pdf = print + 11). This file carries the leaves of KM's own proof tree that are
STATABLE with today's vocabulary — waves W0–W3 of the stream. The deep-vocabulary
waves (W4 universal formal deformations, W5 Serre–Tate / p-divisible groups, W6 the
axiomatic homogeneity engine) are API-gap charters on the board; their statements
enter this file as their vocabulary lands.

The headline (KM First Main Theorem 5.1.1, `[Γ₁(N)]` clause, verbatim print p. 129):
"Each of the four moduli problems [Γ(N)], [Γ₁(N)], [bal.Γ₁(N)], and [Γ₀(N)] is
relatively representable over (Ell). Each is finite and flat over (Ell) of constant
rank ≥ 1, and regular (necessarily of dimension two). Each tensored with ℤ[1/N] is
finite etale over (Ell/ℤ[1/N])."
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace ModularCurves

/-! ## W0 — the Drinfeld transport leaf (KM 3.6 substrate)

The integral relative-representability wave. The problem object `gammaOneProblem`
(the Drinfeld analogue of `gammaOneNaiveProblem`, with `IsGammaOne` in place of
`IsNaiveGammaOne`) is DEFERRED to ticket [KM-W0]: per the v10.8 no-sorried-data rule
the functor cannot be defined before its transport lemma is proven. The transport
lemma itself is the first skeleton leaf. -/

section Transport

variable {S T : Scheme.{u}} (E : EllipticCurve S)

/-- **[KM-W0-1] Drinfeld structures pull back.** Source: KM 1.4 / 3.6 — exact order in
the Cartier-divisor sense is stable under arbitrary base change (KM 1.4, "the formation
of the divisor commutes with base change"; the `[Γ₁(N)]`-problem's functoriality clause,
KM 3.2). Elliptic-curve form over a morphism of base schemes. -/
theorem isGammaOne_pullAlong (N : ℕ) [NeZero N] (f : T ⟶ S) (P : E.Section)
    (h : E.IsGammaOne N P) :
    (E.baseChange f).IsGammaOne N (EllipticCurve.Point.asSection E f (EllipticCurve.Point.pull E f P)) :=
  EllipticCurve.Section.HasExactOrder.baseChange E h f

end Transport

/-! ## W1 — the combinatorial core (KM 5.3.4)

KM Prop 5.3.4 (verbatim, print p. 140): "Let R be an arbitrary ring, and
G(X,Y) = X + Y + ⋯ a one-parameter commutative formal group law over R. Suppose that
for some prime power pⁿ, the equation X^{pⁿ} = 0 defines a subgroup-scheme of G. Then
p = 0 in R, and this subgroup-scheme is equal to Ker(Fⁿ)."

Stated here in the raw universal form KM's own proof uses (print p. 140–141): the
subgroup condition at the universal quotient `B = R⟦X,Y⟧/(X^{pⁿ}, Y^{pⁿ})` says
exactly `G^{pⁿ} ∈ (X₀^{pⁿ}, X₁^{pⁿ})`. Only the constant and linear coefficients of
`G` enter the argument. The `Ker(Fⁿ)` clause (5.3.4b) is stated in wave W2 with the
Frobenius vocabulary. -/

section CombinatorialCore

variable {R : Type u} [CommRing R]

open MvPowerSeries

/-- A multi-index `e : Fin 2 →₀ ℕ` of total degree `1` is `single 0 1` or `single 1 1`. -/
private lemma eq_single_of_degree_eq_one {e : Fin 2 →₀ ℕ} (he : e.degree = 1) :
    e = Finsupp.single 0 1 ∨ e = Finsupp.single 1 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at he
  rcases (by omega : e 0 = 0 ∧ e 1 = 1 ∨ e 0 = 1 ∧ e 1 = 0) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inr (Finsupp.ext fun k => by fin_cases k <;> simp [Finsupp.single_apply, h0, h1])
  · exact Or.inl (Finsupp.ext fun k => by fin_cases k <;> simp [Finsupp.single_apply, h0, h1])

/-- If every degree-one coefficient of `F` is `1`, so is the coefficient at any degree-one index. -/
private lemma coeff_eq_one_of_degree_eq_one {F : MvPowerSeries (Fin 2) R}
    (hF : ∀ s : Fin 2, coeff (Finsupp.single s 1) F = 1) {e : Fin 2 →₀ ℕ} (he : e.degree = 1) :
    coeff e F = 1 := by
  rcases eq_single_of_degree_eq_one he with rfl | rfl
  · exact hF 0
  · exact hF 1

/-- **Crux reduction.** For a power series `F ≡ X₀ + X₁ (mod deg ≥ 2)`, the total-degree-`m`
coefficients of `F ^ m` agree with those of `(X₀ + X₁) ^ m`: in the `coeff_pow` expansion, any
term with a factor of order `0` vanishes (`F` has no constant term), and in every surviving term
all `m` factors have degree exactly `1`, where `F` and `X₀ + X₁` share the same coefficient `1`. -/
private lemma coeff_pow_eq_coeff_add_pow {F : MvPowerSeries (Fin 2) R}
    (hF0 : constantCoeff F = 0) (hF1 : ∀ s : Fin 2, coeff (Finsupp.single s 1) F = 1)
    {m : ℕ} {d : Fin 2 →₀ ℕ} (hd : d.degree = m) :
    coeff d (F ^ m) = coeff d ((X 0 + X 1 : MvPowerSeries (Fin 2) R) ^ m) := by
  classical
  have hX0 : constantCoeff (X 0 + X 1 : MvPowerSeries (Fin 2) R) = 0 := by
    simp [map_add, MvPowerSeries.constantCoeff_X]
  have hX1 : ∀ s : Fin 2, coeff (Finsupp.single s 1) (X 0 + X 1 : MvPowerSeries (Fin 2) R) = 1 := by
    intro s; fin_cases s <;> simp [map_add, coeff_index_single_X]
  rw [coeff_pow, coeff_pow]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mem_finsuppAntidiag] at hl
  obtain ⟨hlsum, -⟩ := hl
  by_cases hz : ∃ j ∈ Finset.range m, l j = 0
  · obtain ⟨j, hjmem, hj0⟩ := hz
    rw [Finset.prod_eq_zero hjmem (by rw [hj0, coeff_zero_eq_constantCoeff_apply, hF0]),
        Finset.prod_eq_zero hjmem (by rw [hj0, coeff_zero_eq_constantCoeff_apply, hX0])]
  · push_neg at hz
    have hdegsum : ∑ j ∈ Finset.range m, (l j).degree = m := by
      rw [← map_sum Finsupp.degree, hlsum, hd]
    have hge : ∀ j ∈ Finset.range m, 1 ≤ (l j).degree := fun j hj =>
      Nat.one_le_iff_ne_zero.mpr fun h => hz j hj ((Finsupp.degree_eq_zero_iff (l j)).mp h)
    have heach : ∀ j ∈ Finset.range m, (l j).degree = 1 := fun j hj =>
      ((Finset.sum_eq_sum_iff_of_le (f := fun _ => (1 : ℕ)) (g := fun j => (l j).degree) hge).mp
        (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, hdegsum]) j hj).symm
    exact Finset.prod_congr rfl fun j hj => by
      rw [coeff_eq_one_of_degree_eq_one hF1 (heach j hj),
          coeff_eq_one_of_degree_eq_one hX1 (heach j hj)]

/-- The "cross" coefficient of `(X₀ + X₁) ^ m` at the index `(i, m - i)` is the binomial
coefficient `m.choose i` (for `i ≤ m`), via the coercion to `MvPolynomial` and its `coeff_add_pow`. -/
private lemma coeff_add_pow_cross (m i : ℕ) (hi : i ≤ m) :
    coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 (m - i))
      ((X 0 + X 1 : MvPowerSeries (Fin 2) R) ^ m) = (m.choose i : R) := by
  set d : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 (m - i) with hd_def
  have hcoe : (X 0 + X 1 : MvPowerSeries (Fin 2) R)
      = ((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) :
          MvPowerSeries (Fin 2) R) := by
    simp only [MvPolynomial.coe_add, MvPolynomial.coe_X]
  rw [hcoe, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
  have hd0 : d 0 = i := by rw [hd_def]; simp
  have hd1 : d 1 = m - i := by rw [hd_def]; simp
  rw [hd0, hd1]
  have hmem : i + (m - i) = m := by omega
  simp [Finset.mem_antidiagonal, hmem]

/-- **[KM-W1-1] (KM 5.3.4, first conclusion).** If a two-variable power series `G` with
`G ≡ X₀ + X₁ (mod degree ≥ 2)` satisfies `G^{pⁿ} ∈ (X₀^{pⁿ}, X₁^{pⁿ})`, then `p = 0`
in `R`. KM's proof (print p. 141): compare total-degree-`pⁿ` terms in
`G^{pⁿ} = X^{pⁿ}·A + Y^{pⁿ}·B` to get `(X+Y)^{pⁿ} = X^{pⁿ}A(0,0) + Y^{pⁿ}B(0,0)`;
coefficients of `X^{pⁿ}`, `Y^{pⁿ}` force `A(0,0) = B(0,0) = 1`; hence all intermediate
binomial coefficients `(pⁿ choose i)` vanish in `R`; `i = 1` gives `pⁿ = 0`,
`i = p^{n-1}` gives `p × (unit prime to p) = 0`, so `p = 0`. -/
theorem CharP.p_eq_zero_of_pow_mem_span (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n)
    (G : MvPowerSeries (Fin 2) R)
    (h0 : MvPowerSeries.constantCoeff G = 0)
    (hlin : ∀ i : Fin 2, MvPowerSeries.coeff (Finsupp.single i 1) G = 1)
    (hsub : G ^ p ^ n ∈ Ideal.span
      {(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) ^ p ^ n, (MvPowerSeries.X (1 : Fin 2)) ^ p ^ n}) :
    (p : R) = 0 := by
  classical
  have hp1 : 1 < p := hp.one_lt
  -- **Part A.** Every intermediate binomial coefficient `(pⁿ).choose i` vanishes in `R`.
  have hchoose : ∀ i, 0 < i → i < p ^ n → ((p ^ n).choose i : R) = 0 := by
    intro i hi0 him
    have hile : i ≤ p ^ n := him.le
    set d : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 (p ^ n - i) with hd_def
    have hd0 : d 0 = i := by rw [hd_def]; simp
    have hd1 : d 1 = p ^ n - i := by rw [hd_def]; simp
    have hddeg : d.degree = p ^ n := by
      rw [hd_def, map_add, Finsupp.degree_single, Finsupp.degree_single]; omega
    -- The cross coefficient of `Gᵖ^ⁿ` equals `(pⁿ).choose i` …
    have hLHS : coeff d (G ^ p ^ n) = ((p ^ n).choose i : R) := by
      rw [coeff_pow_eq_coeff_add_pow h0 hlin hddeg, hd_def, coeff_add_pow_cross (p ^ n) i hile]
    -- … and is `0`, since `Gᵖ^ⁿ = A · X₀ᵖ^ⁿ + B · X₁ᵖ^ⁿ` has no cross terms of that degree.
    have hRHS : coeff d (G ^ p ^ n) = 0 := by
      obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.mp hsub
      have hle0 : ¬ Finsupp.single (0 : Fin 2) (p ^ n) ≤ d := by
        rw [Finsupp.single_le_iff, hd0]; omega
      have hle1 : ¬ Finsupp.single (1 : Fin 2) (p ^ n) ≤ d := by
        rw [Finsupp.single_le_iff, hd1]; omega
      rw [← hAB, map_add, X_pow_eq, X_pow_eq, coeff_mul_monomial, coeff_mul_monomial,
          if_neg hle0, if_neg hle1, add_zero]
    exact hLHS.symm.trans hRHS
  -- **Part B.** `gcd ((pⁿ).choose 1) ((pⁿ).choose p^{n-1}) = gcd (pⁿ) (p · unit) = p`
  -- (Kummer), and both generators vanish in `R`, so `p = 0` by Bézout.
  have hklt : p ^ (n - 1) < p ^ n := Nat.pow_pred_lt_pow hp1 hn
  have hk0 : p ^ (n - 1) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hA0 : ((p ^ n : ℕ) : R) = 0 := by
    have := hchoose 1 one_pos (Nat.one_lt_pow (by omega) hp1)
    rwa [Nat.choose_one_right] at this
  have hB0 : (((p ^ n).choose (p ^ (n - 1)) : ℕ) : R) = 0 :=
    hchoose (p ^ (n - 1)) (Nat.pos_of_ne_zero hk0) hklt
  have hpB : p ∣ (p ^ n).choose (p ^ (n - 1)) := hp.dvd_choose_pow hk0 (Nat.ne_of_lt hklt)
  have hmult : emultiplicity p ((p ^ n).choose (p ^ (n - 1))) = 1 := by
    rw [hp.emultiplicity_choose_prime_pow hklt.le hk0, multiplicity_pow_self_of_prime hp.prime,
        show n - (n - 1) = 1 by omega, Nat.cast_one]
  have hnp2 : ¬ p ^ 2 ∣ (p ^ n).choose (p ^ (n - 1)) := by
    rw [← emultiplicity_lt_iff_not_dvd, hmult]; exact_mod_cast one_lt_two
  obtain ⟨mm, hmm⟩ := hpB
  have hpmm : ¬ p ∣ mm := fun hd => hnp2 (by rw [hmm, pow_two]; exact mul_dvd_mul_left p hd)
  have hpn : p ^ n = p * p ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
    rw [mul_comm]
  have hco : Nat.gcd (p ^ (n - 1)) mm = 1 :=
    Nat.Coprime.pow_left (n - 1) (hp.coprime_iff_not_dvd.mpr hpmm)
  have hgcd : Nat.gcd (p ^ n) ((p ^ n).choose (p ^ (n - 1))) = p := by
    rw [hmm, hpn, Nat.gcd_mul_left, hco, mul_one]
  have hbez := Nat.gcd_eq_gcd_ab (p ^ n) ((p ^ n).choose (p ^ (n - 1)))
  rw [hgcd] at hbez
  have hcast := congrArg (fun z : ℤ => (z : R)) hbez
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul] at hcast
  rw [hcast, hA0, hB0]; ring

end CombinatorialCore

/-! ## W2 — the zero-section proposition (KM 5.3.3, elliptic case)

KM Prop 5.3.3 (verbatim, print p. 140): "Let R be an arbitrary ring, C/R a smooth
commutative one-dimensional group-scheme over R (cf. 1.4.1), p a prime number, n ≥ 1
an integer. Suppose that the zero section 0 ∈ C(R) is a point of 'exact order pⁿ' in
C/R, i.e., that the effective Cartier divisor pⁿ[0] in C/R is a subgroup-scheme. Then
p = 0 in R, and the subgroup-scheme pⁿ[0] is none other than Ker(Fⁿ)."

Stated here for our elliptic curves over an affine base (the shape the Rigid-II
application consumes; KM's proof is Zariski-local anyway: "Zariski locally on R, we
may choose a parameter X for the formal group. Once this is done, our proposition
results from [5.3.4]."). The chart parameter comes from the repo's Weierstrass chart
machinery; the divisor-to-power-series bridge is the `sectionsDivisor`/killed-locus
layer. -/

section ZeroSection

/-- **[KM-W2 · L1]** The order divisor `[0] + [2·0] + ⋯ + [N·0]` of the zero section has
ideal `(ker 0)^N`: every constituent section `(a+1)·0` collapses to `0`, so the defining
product `∏ₐ ker((a+1)·0)` of the `sectionsDivisor` is the `N`-th power of the single
zero-section kernel. This is the divisor side of KM 5.3.3's "the Cartier divisor `pⁿ[0]`". -/
private lemma orderDivisor_zero_ideal {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) :
    (EllipticCurve.Section.orderDivisor E 0 N).ideal
      = (Scheme.Hom.ker (0 : E.Section).1) ^ N := by
  have hpos : IsSeparated E.π ∧ SmoothOfRelativeDimension 1 E.π := ⟨inferInstance, E.smooth⟩
  rw [EllipticCurve.Section.orderDivisor, RelEffCartierDiv.sectionsDivisor, dif_pos hpos]
  simp only [smul_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **[KM-W2 · L2]** Affine-locally at any point `c` of the total space, the zero-section
order divisor `[0]+⋯+[N·0]` is cut out by `fᴺ` for a local nonzerodivisor parameter `f`:
this is KM 5.3.3's "the Cartier divisor `pⁿ[0]` is `X^{pⁿ} = 0`". Combines `L1`
(ideal `= (ker 0)^N`) with the principal-parameter existence for a section of a smooth
relative curve (`exists_affineOpen_ker_principal_nonZeroDivisor`, KM 1.2.2). -/
private lemma orderDivisor_zero_ideal_principal {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ)
    (c : E.E) :
    ∃ V : E.E.affineOpens, c ∈ V.1 ∧ ∃ f : Γ(E.E, V.1),
      ((EllipticCurve.Section.orderDivisor E 0 N).ideal).ideal V = Ideal.span {f ^ N} ∧
      f ∈ nonZeroDivisors Γ(E.E, V.1) := by
  obtain ⟨V, hcV, f, hf, hfnzd⟩ :=
    RelEffCartierDiv.exists_affineOpen_ker_principal_nonZeroDivisor E.π E.smooth
      (0 : E.Section).1 (0 : E.Section).2 c
  refine ⟨V, hcV, f, ?_, hfnzd⟩
  have hpow : ((Scheme.Hom.ker (0 : E.Section).1) ^ N).ideal V
      = ((Scheme.Hom.ker (0 : E.Section).1).ideal V) ^ N := by
    rw [← Pi.pow_apply]
    exact congrFun
      (map_pow (Scheme.IdealSheafData.idealMonoidHom E.E) (Scheme.Hom.ker (0 : E.Section).1) N) V
  rw [orderDivisor_zero_ideal, hpow, hf, Ideal.span_singleton_pow]

/-- **[KM-W2-1] (KM 5.3.3, first conclusion, elliptic affine case).** If the zero
section of an elliptic curve over `Spec A` has Drinfeld exact order `pⁿ`, then
`p = 0` in `A`. -/
theorem CharP.p_eq_zero_of_isGammaOne_zero (p n : ℕ) [NeZero (p ^ n)] (hp : p.Prime) (hn : 1 ≤ n)
    (A : Type u) [CommRing A]
    (E : EllipticCurve (Spec (CommRingCat.of A)))
    (h : E.IsGammaOne (p ^ n) 0) :
    (p : A) = 0 := by sorry

end ZeroSection

/-! ## W3 — Rigidity II, first half (KM 5.3.2.2 via 5.3.5)

KM (5.3.2.2) Rigid II (verbatim, print p. 138–139): "Let k be an algebraically closed
field of characteristic p. If R is an artin local W(k)-algebra [with residue field k],
and if E/R admits 0 as a point of 'exact order pⁿ', then R is a k-algebra, i.e.,
p = 0 in R."  KM 5.3.5 (print p. 141): "Assertion II is just the proposition itself,
applied to E/R."  The second half of Case II (the `T`-invariant clause forcing `E/R`
constant) enters with wave W4's deformation vocabulary. -/

section RigidII

/-- **[KM-W3-1] (Rigid II, first conclusion).** An artin local ring whose elliptic curve
admits the zero section as a point of Drinfeld exact order `pⁿ` has `p = 0` — the
one-line corollary of [KM-W2-1] per KM 5.3.5. Stated without the Witt-vector algebra
structure (not needed for this half; W4 re-states the full deformation form). -/
theorem CharP.p_eq_zero_of_isGammaOne_zero_artinLocal (p n : ℕ) [NeZero (p ^ n)] (hp : p.Prime)
    (hn : 1 ≤ n) (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    (E : EllipticCurve (Spec (CommRingCat.of A)))
    (h : E.IsGammaOne (p ^ n) 0) :
    (p : A) = 0 :=
  -- KM 5.3.5: Rigid II is Prop 5.3.3 (= [KM-W2-1]) applied to `E/R`; the artin-local
  -- hypotheses are unused here (they feed W4's constancy half). Auto-completes once
  -- [KM-W2-1] is discharged.
  CharP.p_eq_zero_of_isGammaOne_zero p n hp hn A E h

end RigidII

end ModularCurves
