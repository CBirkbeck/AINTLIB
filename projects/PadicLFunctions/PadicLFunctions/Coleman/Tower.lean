/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import PadicLFunctions.ResidueZeta
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# The cyclotomic tower over ℚ_p (RJW §9, TeX 2466–2511)

The local objects of Part II: a fixed compatible system `ξ_{p^n}` of
primitive `p^n`-th roots of unity (`ξ_{p^{n+1}}^p = ξ_{p^n}`), the tower
`K_n = ℚ_p(μ_{p^n})`, the uniformisers `π_n = ξ_{p^n} − 1`, the integer
rings `O_n` and their unit groups `𝒰_n`, and (at the `𝒰_∞`-ticket) the
norm-inverse-limit `𝒰_∞ = lim_n 𝒰_n`.

Design (decomposition R10.1): the tower lives *inside* `ℂ_p` — matching
the source's own framing of the `π_n` as points of the open unit ball
`B(0,1) ⊂ ℂ_p` (TeX 2528–2532) — so `K_n` is an
`IntermediateField ℚ_[p] ℂ_[p]`, the integer ring is the norm-ball, and
power-series evaluation at `π_n` is the project's `seriesEval`. The
degree ladder `[K_n : ℚ_p] = φ(p^n)` comes from Eisenstein-ness of
`Φ_{p^n}(T+1)` over `ℤ_p` (R10.2); the norm collapse
`N_{n+1,n}(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1` (TeX 2581–2585) is the
engine for both the cyclotomic units and the evaluation/norm commuting
square.
-/

open PowerSeries Polynomial
open scoped IntermediateField

namespace PadicLFunctions

namespace Coleman

variable (p : ℕ) [hp : Fact p.Prime]

/-- The single tower step: from a primitive `p^n`-th root `z` we extract a
primitive `p^{n+1}`-th root `w` with `w^p = z`. For `n = 0` (`z = 1`) we take
a genuine primitive `p`-th root (`HasEnoughRootsOfUnity`, available from
`IsAlgClosed` + char `0`); for `n ≥ 1` any `p`-th root of `z` works — alg.
closure gives one, and an order count (`Nat.dvd_prime_pow`) pins its order
to `p^{n+1}`. -/
private theorem primitiveRoot_pow_succ :
    ∀ {n : ℕ} {z : ℂ_[p]}, IsPrimitiveRoot z (p ^ n) →
      ∃ w : ℂ_[p], IsPrimitiveRoot w (p ^ (n + 1)) ∧ w ^ p = z := by
  haveI : NeZero (p : ℂ_[p]) := ⟨(Nat.cast_ne_zero (R := ℂ_[p])).mpr hp.out.ne_zero⟩
  rintro (_ | n) z hz
  · obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
    have hz1 : z = 1 := by simpa using hz.pow_eq_one
    exact ⟨w, by simpa using hw, by rw [hz1, hw.pow_eq_one]⟩
  · obtain ⟨w, hwz⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ_[p]) z (n := p) hp.out.pos
    refine ⟨w, ?_, hwz⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    have hpow : w ^ p ^ (n + 1 + 1) = 1 := by
      rw [pow_succ', pow_mul, hwz, hz.pow_eq_one]
    have hdvd : orderOf w ∣ p ^ (n + 1 + 1) := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨k, hkle, hk⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd
    rcases eq_or_lt_of_le hkle with hkeq | hklt
    · rw [hk, hkeq]
    · exfalso
      have hkle' : k ≤ n + 1 := Nat.lt_succ_iff.1 hklt
      have hwpn : w ^ p ^ (n + 1) = 1 :=
        orderOf_dvd_iff_pow_eq_one.1 (hk ▸ pow_dvd_pow p hkle')
      refine hz.pow_ne_one_of_pos_of_lt (l := p ^ n) (pow_pos hp.out.pos n).ne'
        (pow_lt_pow_right₀ hp.out.one_lt n.lt_succ_self) ?_
      rw [pow_succ', pow_mul, hwz] at hwpn
      exact hwpn

/-- R9: a compatible system of primitive `p^n`-th roots of unity in `ℂ_p`
exists (`ξ_0 = 1`; each `ξ_{n+1}` is a `p`-th root of `ξ_n`, primitive of
order `p^{n+1}`): ℕ-recursion + `IsAlgClosed` roots. RJW TeX 2507: "We fix
once and for all a compatible system of roots of unity `(ξ_{p^n})_n`". -/
theorem exists_compatible_primitiveRoot :
    ∃ ξ : ℕ → ℂ_[p],
      (∀ n, IsPrimitiveRoot (ξ n) (p ^ n)) ∧ ∀ n, ξ (n + 1) ^ p = ξ n := by
  let chain : ∀ n, {z : ℂ_[p] // IsPrimitiveRoot z (p ^ n)} := fun n =>
    Nat.rec ⟨1, by simp⟩ (fun _ zn => ⟨(primitiveRoot_pow_succ p zn.2).choose,
      (primitiveRoot_pow_succ p zn.2).choose_spec.1⟩) n
  refine ⟨fun n => (chain n).1, fun n => (chain n).2, fun n => ?_⟩
  exact (primitiveRoot_pow_succ p (chain n).2).choose_spec.2

/-- The fixed compatible system `n ↦ ξ_{p^n}` (RJW TeX 2507). -/
noncomputable def zetaSys : ℕ → ℂ_[p] :=
  (exists_compatible_primitiveRoot p).choose

theorem zetaSys_primitiveRoot (n : ℕ) :
    IsPrimitiveRoot (zetaSys p n) (p ^ n) :=
  (exists_compatible_primitiveRoot p).choose_spec.1 n

theorem zetaSys_pow_p (n : ℕ) : zetaSys p (n + 1) ^ p = zetaSys p n :=
  (exists_compatible_primitiveRoot p).choose_spec.2 n

/-- R9: the local cyclotomic field `K_n = ℚ_p(μ_{p^n})`, realised inside
`ℂ_p` as `ℚ_p(ξ_{p^n})` (RJW TeX 2473). -/
noncomputable def K (n : ℕ) : IntermediateField ℚ_[p] ℂ_[p] :=
  IntermediateField.adjoin ℚ_[p] {zetaSys p n}

/-- R9: the uniformiser `π_n = ξ_{p^n} − 1` of `K_n` (RJW TeX 2507). -/
noncomputable def pi (n : ℕ) : ℂ_[p] := zetaSys p n - 1

theorem zetaSys_mem_K (n : ℕ) : zetaSys p n ∈ K p n :=
  IntermediateField.subset_adjoin ℚ_[p] {zetaSys p n} (Set.mem_singleton _)

theorem pi_mem_K (n : ℕ) : pi p n ∈ K p n :=
  sub_mem (zetaSys_mem_K p n) (one_mem _)

theorem K_le_succ (n : ℕ) : K p n ≤ K p (n + 1) := by
  refine IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 ?_)
  rw [← zetaSys_pow_p p n]
  exact pow_mem (zetaSys_mem_K p (n + 1)) p

/-- The `(p^{n+1})`-th cyclotomic polynomial is irreducible over `ℤ_p`: the
translate `Φ_{p^{n+1}}(T+1)` is Eisenstein at `(p)` (transported from `ℤ` via
`cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt`), hence irreducible, and the
`T ↦ T+1` automorphism (`algEquivAevalXAddC`) carries that back to `Φ_{p^{n+1}}`.
RJW TeX 2475. -/
private theorem cyclotomic_irreducible_Zp (n : ℕ) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℤ_[p]) := by
  set φ := algebraMap ℤ ℤ_[p] with hφ
  have hdne : ((X : ℤ_[p][X]) + 1).natDegree ≠ 0 := by
    rw [show ((X : ℤ_[p][X]) + 1) = (X : ℤ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hmonicZ : ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).Monic := by
    refine (cyclotomic.monic _ ℤ).comp (monic_X_add_C 1) ?_
    rw [show ((X : ℤ[X]) + 1) = (X : ℤ[X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hmonicZp : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).Monic :=
    (cyclotomic.monic _ ℤ_[p]).comp (monic_X_add_C 1) hdne
  have hmapeq : (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)
      = ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).map φ := by
    rw [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_one]
  have hdeg : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).natDegree
      = ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).natDegree := by
    rw [hmapeq, hmonicZ.natDegree_map]
  have hZ := cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n
  have hpspan : (Ideal.span {(p : ℤ_[p])}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)]
    exact_mod_cast (PadicInt.irreducible_p (p := p)).prime
  have himg : ∀ z : ℤ, z ∈ Ideal.span {(p : ℤ)} → φ z ∈ Ideal.span {(p : ℤ_[p])} := by
    intro z hz
    rw [Ideal.mem_span_singleton] at hz ⊢
    obtain ⟨k, rfl⟩ := hz
    exact ⟨φ k, by simp [hφ, mul_comm]⟩
  have hEis : ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmapeq, (hmonicZ.map φ).leadingCoeff, Ideal.mem_span_singleton]
      intro h
      exact hpspan.ne_top (Ideal.eq_top_of_isUnit_mem _
        (Ideal.mem_span_singleton.2 (dvd_refl _)) (isUnit_of_dvd_one h))
    · intro i hi
      rw [hmapeq, Polynomial.coeff_map]
      exact himg _ (hZ.mem (hdeg ▸ hi))
    · rw [hmapeq, Polynomial.coeff_map]
      have h0 : ((cyclotomic (p ^ (n + 1)) ℤ).comp ((X : ℤ[X]) + 1)).coeff 0 = (p : ℤ) := by
        rw [coeff_zero_eq_eval_zero, eval_comp]; simp [eval_one_cyclotomic_prime_pow]
      rw [h0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hdvd : ((p : ℤ_[p])) ^ 2 ∣ (p : ℤ_[p]) := by simpa using h
      have hpne : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      rw [pow_two] at hdvd
      obtain ⟨c, hc⟩ := hdvd
      have h1 : (p : ℤ_[p]) * 1 = (p : ℤ_[p]) * ((p : ℤ_[p]) * c) := by
        rw [mul_one]; linear_combination hc
      have h2 : (1 : ℤ_[p]) = (p : ℤ_[p]) * c := mul_left_cancel₀ hpne h1
      exact (PadicInt.irreducible_p (p := p)).not_isUnit (IsUnit.of_mul_eq_one c h2.symm)
  have hcomp_irr : Irreducible ((cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1)) := by
    refine hEis.irreducible hpspan hmonicZp.isPrimitive ?_
    rw [hdeg, natDegree_comp, natDegree_cyclotomic,
      show ((X : ℤ[X]) + 1).natDegree = 1 by
        rw [show ((X : ℤ[X]) + 1) = (X : ℤ[X]) + Polynomial.C 1 by simp, natDegree_X_add_C],
      mul_one]
    exact Nat.totient_pos.2 (pow_pos hp.out.pos _)
  have hmap : (algEquivAevalXAddC (1 : ℤ_[p])) (cyclotomic (p ^ (n + 1)) ℤ_[p])
      = (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp ((X : ℤ_[p][X]) + 1) := by
    rw [algEquivAevalXAddC_apply, comp_eq_aeval, map_one]
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℤ_[p])).toMulEquiv).mp
    (hmap ▸ hcomp_irr)

/-- `Φ_{p^n}` is irreducible over `ℚ_p` for `n ≥ 1` — Gauss's lemma transfers the
`ℤ_p`-irreducibility (`ℤ_p` is an integrally closed domain with fraction field
`ℚ_p`). This is the key input for the degree ladder and the cyclotomic-extension
structure of `K_n`. -/
theorem cyclotomic_irreducible_Qp {n : ℕ} (hn : 1 ≤ n) :
    Irreducible (cyclotomic (p ^ n) ℚ_[p]) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← map_cyclotomic (p ^ (m + 1)) (algebraMap ℤ_[p] ℚ_[p])]
  exact (Monic.irreducible_iff_irreducible_map_fraction_map
    (cyclotomic.monic _ ℤ_[p])).mp (cyclotomic_irreducible_Zp p m)

/-- `K_n = ℚ_p(ξ_{p^n})` is a cyclotomic extension of `ℚ_p`: `ξ_{p^n}` is a
primitive `p^n`-th root of unity adjoined to `ℚ_p`. (Built from the single-element
algebraicity of `ξ_{p^n}` since `ℂ_p` is not algebraic over `ℚ_p`.) -/
instance isCyclotomicExtension_K {n : ℕ} [NeZero (p ^ n)] :
    IsCyclotomicExtension {p ^ n} ℚ_[p] (K p n) := by
  have hζ := zetaSys_primitiveRoot p n
  have hint : IsIntegral ℚ_[p] (zetaSys p n) :=
    (hζ.isIntegral (pow_pos hp.out.pos n)).tower_top
  change IsCyclotomicExtension {p ^ n} ℚ_[p] (K p n).toSubalgebra
  rw [K, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ_[p]

/-- R10.2 (degree ladder): `[K_n : ℚ_p] = φ(p^n)` — irreducibility of
`Φ_{p^n}` over `ℚ_p` via Eisenstein at `(p)` after `T ↦ T+1`
(RJW TeX 2475: "totally ramified … of degree `(p−1)p^{n−1}`"). -/
theorem finrank_K (n : ℕ) :
    Module.finrank ℚ_[p] (K p n) = Nat.totient (p ^ n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, Nat.totient_one]
    have h1 : zetaSys p 0 = 1 := by simpa using (zetaSys_primitiveRoot p 0).pow_eq_one
    rw [K, h1, IntermediateField.adjoin_one]
    exact IntermediateField.finrank_bot
  · haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
    exact IsCyclotomicExtension.finrank (K p n) (cyclotomic_irreducible_Qp p (by omega))

/-- The norm of a primitive `p^n`-th root of unity in `ℂ_p` is `1`
(`‖ξ‖^{p^n} = 1` forces `‖ξ‖ = 1`). -/
private theorem norm_primitiveRoot_eq_one {n : ℕ} {ξ : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) : ‖ξ‖ = 1 := by
  have h1 : ‖ξ‖ ^ (p ^ n) = 1 := by rw [← norm_pow, hξ.pow_eq_one, norm_one]
  have hne : p ^ n ≠ 0 := (pow_pos hp.out.pos n).ne'
  refine le_antisymm ?_ ?_
  · by_contra! h; exact absurd h1 (one_lt_pow₀ h hne).ne'
  · by_contra! h; exact absurd h1 (pow_lt_one₀ (norm_nonneg ξ) h hne).ne

/-- For a norm-one element `ξ` of `ℂ_p`, `‖ξ^c − 1‖ ≤ ‖ξ − 1‖`: factor
`ξ^c − 1 = (∑_{i<c} ξ^i)(ξ − 1)` and bound the geometric factor by `1`
(ultrametric sum of norm-one terms). -/
private theorem norm_pow_sub_one_le {ξ : ℂ_[p]} (hξ1 : ‖ξ‖ = 1) (c : ℕ) :
    ‖ξ ^ c - 1‖ ≤ ‖ξ - 1‖ := by
  rw [show ξ ^ c - 1 = (∑ i ∈ Finset.range c, ξ ^ i) * (ξ - 1) from (geom_sum_mul ξ c).symm,
    norm_mul]
  have hgeom : ‖∑ i ∈ Finset.range c, ξ ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun i _ => by rw [norm_pow, hξ1, one_pow])
  nlinarith [norm_nonneg (ξ - 1), hgeom]

/-- Any two primitive `p^n`-th roots of unity `ξ, η` in `ℂ_p` satisfy
`‖ξ − 1‖ = ‖η − 1‖`: each is a power of the other (same cyclic group), so
`norm_pow_sub_one_le` gives both inequalities. This is the engine for the
`π_n`-norm: all conjugates of `π_n` have the same norm. -/
private theorem norm_sub_one_eq {n : ℕ} {ξ η : ℂ_[p]}
    (hξ : IsPrimitiveRoot ξ (p ^ n)) (hη : IsPrimitiveRoot η (p ^ n)) :
    ‖ξ - 1‖ = ‖η - 1‖ := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  obtain ⟨i, _, hi⟩ := hξ.eq_pow_of_pow_eq_one hη.pow_eq_one
  obtain ⟨j, _, hj⟩ := hη.eq_pow_of_pow_eq_one hξ.pow_eq_one
  refine le_antisymm ?_ ?_
  · rw [← hj]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hη) j
  · rw [← hi]; exact norm_pow_sub_one_le p (norm_primitiveRoot_eq_one p hξ) i

/-- Every root `r` of `Φ_{p^n}` in `ℂ_p` is a primitive `p^n`-th root, so
`‖r − 1‖ = ‖π_n‖`. -/
private theorem norm_root_sub_one_eq {n : ℕ} (r : ℂ_[p])
    (hr : r ∈ (cyclotomic (p ^ n) ℂ_[p]).roots) : ‖r - 1‖ = ‖pi p n‖ := by
  haveI : NeZero ((p ^ n : ℕ) : ℂ_[p]) := by
    refine ⟨?_⟩; rw [Nat.cast_pow]; exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [mem_roots (cyclotomic_ne_zero _ _)] at hr
  rw [pi]
  exact norm_sub_one_eq p (isRoot_cyclotomic_iff.mp hr) (zetaSys_primitiveRoot p n)

/-- R10.2: the norm of the uniformiser, rpow-free form:
`‖π_n‖^{φ(p^n)} = p⁻¹` for `n ≥ 1` (the Eisenstein constant term:
`N_{K_n/ℚ_p}(π_n) = ±Φ_{p^n}(1) = ±p`, and the spectral norm is
Galois-invariant). In particular `0 < ‖π_n‖ < 1`.

The proof works directly in `ℂ_p`: `g := Φ_{p^n}(T+1)` is monic and splits, its
roots are `{η − 1 : η ∈ μ_{p^n}^×}` each of norm `‖π_n‖` (`norm_root_sub_one_eq`),
its constant term is `Φ_{p^n}(1) = p`, and Vieta gives
`p = ±∏ roots`, so `‖π_n‖^{φ(p^n)} = ‖∏ roots‖ = ‖p‖ = p⁻¹`. -/
theorem norm_pi_pow_totient {n : ℕ} (hn : 1 ≤ n) :
    ‖pi p n‖ ^ Nat.totient (p ^ n) = (p : ℝ)⁻¹ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI : NeZero ((p ^ (m + 1) : ℕ) : ℂ_[p]) := by
    refine ⟨?_⟩; rw [Nat.cast_pow]; exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  set g : ℂ_[p][X] := (cyclotomic (p ^ (m + 1)) ℂ_[p]).comp ((X : ℂ_[p][X]) + 1) with hg
  have hgmonic : g.Monic := by
    rw [hg]; refine (cyclotomic.monic _ ℂ_[p]).comp (monic_X_add_C 1) ?_
    rw [show ((X : ℂ_[p][X]) + 1) = (X : ℂ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C]
    exact one_ne_zero
  have hgsplits : g.Splits := IsAlgClosed.splits g
  have hgdeg : g.natDegree = Nat.totient (p ^ (m + 1)) := by
    rw [hg, natDegree_comp, natDegree_cyclotomic,
      show ((X : ℂ_[p][X]) + 1).natDegree = 1 by
        rw [show ((X : ℂ_[p][X]) + 1) = (X : ℂ_[p][X]) + Polynomial.C 1 by simp, natDegree_X_add_C],
      mul_one]
  have hgc0 : g.coeff 0 = (p : ℂ_[p]) := by
    rw [hg, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add,
      eval_one_cyclotomic_prime_pow]
  have hgroots : g.roots = (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1) := by
    rw [hg]; simpa using roots_comp_C_mul_X_add_C (cyclotomic (p ^ (m + 1)) ℂ_[p]) 1 1 isUnit_one
  have hcard : Multiset.card (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots
      = Nat.totient (p ^ (m + 1)) := by
    have hcr : Multiset.card g.roots = g.natDegree := splits_iff_card_roots.mp hgsplits
    rw [hgroots, Multiset.card_map] at hcr; rw [hcr, hgdeg]
  have hprodnorm : ‖g.roots.prod‖ = ‖pi p (m + 1)‖ ^ Nat.totient (p ^ (m + 1)) := by
    rw [hgroots, show ‖((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1)).prod‖
        = (((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (· - 1)).map (‖·‖)).prod from
      map_multiset_prod (normHom (α := ℂ_[p])).toMonoidHom _, Multiset.map_map,
      show (((cyclotomic (p ^ (m + 1)) ℂ_[p]).roots).map ((‖·‖) ∘ (· - 1)))
          = (cyclotomic (p ^ (m + 1)) ℂ_[p]).roots.map (fun _ => ‖pi p (m + 1)‖) from
        Multiset.map_congr rfl (fun r hr => norm_root_sub_one_eq p r hr),
      Multiset.map_const', Multiset.prod_replicate, hcard]
  have hcoeff_prod : g.coeff 0 = (-1) ^ g.natDegree * g.roots.prod :=
    hgsplits.coeff_zero_eq_prod_roots_of_monic hgmonic
  have hpnorm : ‖g.roots.prod‖ = (p : ℝ)⁻¹ := by
    have heq : ‖g.coeff 0‖ = ‖g.roots.prod‖ := by
      rw [hcoeff_prod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    rw [← heq, hgc0,
      show ((p : ℂ_[p])) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) by rw [map_natCast],
      norm_algebraMap', Padic.norm_p]
  rw [← hprodnorm, hpnorm]

theorem norm_pi_lt_one {n : ℕ} (hn : 1 ≤ n) : ‖pi p n‖ < 1 :=
  (zetaSys_primitiveRoot p n).norm_sub_one_lt hn

theorem pi_ne_zero {n : ℕ} (hn : 1 ≤ n) : pi p n ≠ 0 := by
  rw [pi, sub_ne_zero]
  exact (zetaSys_primitiveRoot p n).ne_one (one_lt_pow₀ hp.out.one_lt (by omega))

/-- R9: the integer ring `O_n = O_{K_n}` — the norm-unit-ball of `K_n`
(equivalently the integral closure of `ℤ_p`; the identification is the
Eisenstein-monogenicity ticket). RJW TeX 2474. -/
noncomputable def O (n : ℕ) : Subring ℂ_[p] :=
  (K p n).toSubring ⊓ integerRing ℂ_[p]

theorem pi_mem_O {n : ℕ} (hn : 1 ≤ n) : pi p n ∈ O p n := by
  rw [O, Subring.mem_inf]
  exact ⟨pi_mem_K p n, (norm_pi_lt_one p hn).le⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the `Module.finrank_mul_finrank` tower needs `Module.Free (K p n) (extendScalars …)`,
-- whose synthesis through the `IntermediateField.extendScalars` layer exceeds the default
/-- R10.2 (tower step): the minimal polynomial of `ξ_{p^{n+1}}` over `K_n`
is `X^p − ξ_{p^n}` (RJW TeX 2685: "the minimal polynomial of `ξ_{p^{n+1}}`
over `K_n` is `X^p − ξ_{p^n}`"). Stated as the two halves that downstream
proofs consume: the degree of the tower step is `p`, and `ξ_{p^{n+1}}` is
a root of `X^p − ξ_{p^n}` (the latter is `zetaSys_pow_p`).

Statement note (T902): n ≥ 1 added — the first step of the tower has degree
p − 1 = φ(p), not p. -/
theorem finrank_K_succ {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (K p n) (IntermediateField.extendScalars (K_le_succ p n))
      = p := by
  haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  have htower := Module.finrank_mul_finrank ℚ_[p] (K p n)
    (IntermediateField.extendScalars (K_le_succ p n))
  have htop : Module.finrank ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n))
      = Nat.totient (p ^ (n + 1)) := finrank_K p (n + 1)
  rw [finrank_K p n, htop] at htower
  have hratio : Nat.totient (p ^ (n + 1)) = p * Nat.totient (p ^ n) := by
    rw [Nat.totient_prime_pow hp.out (by omega : 0 < n + 1),
      Nat.totient_prime_pow hp.out hn, Nat.add_sub_cancel]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← mul_assoc, ← pow_succ']
  rw [hratio] at htower
  exact (Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 (pow_pos hp.out.pos n))
    (by linarith [htower])).symm

/-- The relative field norm `N_{K_{n+1}/K_n} : K_{n+1} → K_n`, viewed as a map
`ℂ_p → ℂ_p` (junk-extended by `0` off `K_{n+1}`). For `x ∈ K_{n+1}` it is the
`Algebra.norm` of the corresponding element of
`IntermediateField.extendScalars (K_le_succ p n)` (whose carrier is `K_{n+1}`
seen as a `K_n`-algebra), coerced back into `ℂ_p` via `K_n ↪ ℂ_p`.
RJW TeX 2503. -/
noncomputable def levelNorm (n : ℕ) : ℂ_[p] → ℂ_[p] := fun x =>
  open Classical in
  if h : x ∈ K p (n + 1) then
    (Algebra.norm (K p n)
      (⟨x, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 h⟩ :
        IntermediateField.extendScalars (K_le_succ p n)) : K p n)
  else 0

/-- For `x ∈ K_{n+1}`, `levelNorm` unfolds to the `Algebra.norm` value (no junk
branch). Stated as the underlying `K_n`-element coerced into `ℂ_p`. -/
theorem levelNorm_apply (n : ℕ) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) :
    levelNorm p n x =
      (Algebra.norm (K p n)
        (⟨x, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hx⟩ :
          IntermediateField.extendScalars (K_le_succ p n)) : K p n) := by
  rw [levelNorm, dif_pos hx]

/-- The level norm lands in the base field `K_n` — by construction, the
`Algebra.norm (K p n)` value is a `K_n`-element coerced into `ℂ_p`. -/
theorem levelNorm_mem (n : ℕ) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) :
    levelNorm p n x ∈ K p n := by
  rw [levelNorm_apply p n hx]; exact (Algebra.norm (K p n) _).2

/-- The level norm is multiplicative on `K_{n+1}` (`Algebra.norm` is a
`MonoidHom`; `map_mul` plus the `dif_pos`-plumbing through `mul_mem`). -/
theorem levelNorm_mul (n : ℕ) {x y : ℂ_[p]} (hx : x ∈ K p (n + 1))
    (hy : y ∈ K p (n + 1)) :
    levelNorm p n (x * y) = levelNorm p n x * levelNorm p n y := by
  rw [levelNorm_apply p n hx, levelNorm_apply p n hy, levelNorm_apply p n (mul_mem hx hy)]
  rw [← IntermediateField.coe_mul, ← map_mul]
  rfl

/-- `levelNorm p n 1 = 1` (`Algebra.norm` is a `MonoidHom`). -/
theorem levelNorm_one (n : ℕ) : levelNorm p n 1 = 1 := by
  rw [levelNorm_apply p n (one_mem _), show
    (⟨(1 : ℂ_[p]), (IntermediateField.mem_extendScalars (K_le_succ p n)).2 (one_mem _)⟩ :
      IntermediateField.extendScalars (K_le_succ p n)) = 1 from rfl, map_one]
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- the `Algebra.norm_algebraMap`/`finrank` computation runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; instance synthesis exceeds defaults
set_option maxHeartbeats 1000000 in
/-- **The level norm of a base constant is its `p`-th power** (RJW §12.1 norm-compatibility
helper, the `N(ζ) = ζ^p` step): for `c ∈ K_n` with `n ≥ 1`, viewing `c ∈ K_{n+1}` through
the inclusion, `N_{n+1,n}(c) = c^p`. The step `K_{n+1}/K_n` has degree `p`
(`finrank_K_succ`, `n ≥ 1`), and the level norm of a `K_n`-constant is
`Algebra.norm (K_n) (algebraMap c) = c ^ [K_{n+1}:K_n]` (`Algebra.norm_algebraMap`).

This discharges the *norm-compatibility half* of the constant Teichmüller systems used in
the §12.1/§12.5 splits: a `(p−1)`-th root of unity `ζ ∈ μ_{p−1} ⊂ ℤ_p^× ⊂ K_n^×` satisfies
`N_{n+1,n}(ζ) = ζ^p = ζ` since `ζ^{p−1} = 1`. -/
theorem levelNorm_const_eq_pow {n : ℕ} (hn : 1 ≤ n) {c : ℂ_[p]} (hc : c ∈ K p n) :
    levelNorm p n c = c ^ p := by
  have hcsucc : c ∈ K p (n + 1) := K_le_succ p n hc
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    IsCyclotomicExtension.finiteDimensional {p ^ (n + 1)} ℚ_[p] (K p (n + 1))
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  rw [levelNorm_apply p n hcsucc]
  have hval : (⟨c, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hcsucc⟩ :
        IntermediateField.extendScalars (K_le_succ p n))
      = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) ⟨c, hc⟩ :=
    Subtype.ext rfl
  rw [hval, Algebra.norm_algebraMap, finrank_K_succ p hn]
  push_cast
  rfl

/-- The degree of `ℚ_p(w)` for any primitive `p^{n+1}`-th root of unity `w` is
`φ(p^{n+1})` — `ℚ_p(w)` is a cyclotomic extension (`w` generates the `p^{n+1}`-th
roots) and `Φ_{p^{n+1}}` is irreducible over `ℚ_p`. -/
private theorem finrank_adjoin_primitiveRoot {n : ℕ} {w : ℂ_[p]}
    (hw : IsPrimitiveRoot w (p ^ (n + 1))) :
    Module.finrank ℚ_[p] (IntermediateField.adjoin ℚ_[p] {w}) = Nat.totient (p ^ (n + 1)) := by
  haveI : NeZero (p ^ (n + 1)) := ⟨(pow_pos hp.out.pos (n + 1)).ne'⟩
  have hint : IsIntegral ℚ_[p] w := (hw.isIntegral (pow_pos hp.out.pos (n + 1))).tower_top
  haveI : IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {w}) := by
    change IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p]
      (IntermediateField.adjoin ℚ_[p] {w}).toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hw.adjoin_isCyclotomicExtension ℚ_[p]
  exact IsCyclotomicExtension.finrank _ (cyclotomic_irreducible_Qp p (by omega))

/-- `K_n = ℚ_p(ξ_{p^n})` is finite-dimensional over `ℚ_p` (it is a cyclotomic
extension). Phrased as a fact to feed the tower arguments. -/
private theorem finiteDimensional_K (n : ℕ) : FiniteDimensional ℚ_[p] (K p n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : zetaSys p 0 = 1 := by simpa using (zetaSys_primitiveRoot p 0).pow_eq_one
    rw [K, h1, IntermediateField.adjoin_one]; infer_instance
  · haveI : NeZero (p ^ n) := ⟨(pow_pos hp.out.pos n).ne'⟩
    exact IsCyclotomicExtension.finite_of_singleton (p ^ n) _ _

/-- A primitive `p^{n+1}`-th root of unity `w ∈ K_{n+1}` is *not* in `K_n`: it
would force `φ(p^{n+1}) = [ℚ_p(w):ℚ_p] ≤ [K_n:ℚ_p] = φ(p^n)`, false for `n ≥ 1`. -/
theorem primitiveRoot_notMem_K {n : ℕ} (hn : 1 ≤ n) {w : ℂ_[p]}
    (hw : IsPrimitiveRoot w (p ^ (n + 1))) : w ∉ K p n := by
  haveI := finiteDimensional_K p n
  intro hwK
  have hle : IntermediateField.adjoin ℚ_[p] {w} ≤ K p n :=
    IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hwK)
  have hcmp := IntermediateField.finrank_le_of_le_right hle
  rw [finrank_adjoin_primitiveRoot p hw, finrank_K p n] at hcmp
  have hgt : Nat.totient (p ^ n) < Nat.totient (p ^ (n + 1)) := by
    rw [Nat.totient_prime_pow hp.out (by omega : 0 < n + 1),
      Nat.totient_prime_pow hp.out hn]
    have hpow : p ^ (n - 1) < p ^ (n + 1 - 1) := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    exact (Nat.mul_lt_mul_right (by have := hp.out.two_le; omega : 0 < p - 1)).2 hpow
  omega

set_option synthInstance.maxHeartbeats 1000000 in
-- adjoin/finrank reasoning through the `IntermediateField.extendScalars` layer (a
-- second `IntermediateField` over `K p n`) forces nested instance synthesis past the default
/-- If the `ℂ_p`-value of `V : extendScalars (K_n ≤ K_{n+1})` is not in `K_n`,
then `V` generates `K_{n+1}` over `K_n` (the step has prime degree `p`, so the
proper subextension `K_n` is the only one below). -/
theorem extendScalars_adjoin_eq_top {n : ℕ} (hn : 1 ≤ n)
    {V : IntermediateField.extendScalars (K_le_succ p n)}
    (hbot : (V : ℂ_[p]) ∉ K p n) : (K p n)⟮V⟯ = ⊤ := by
  haveI := finiteDimensional_K p n
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    finiteDimensional_K p (n + 1)
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', finrank_K_succ p hn]
  have hdvd : Module.finrank (K p n) (K p n)⟮V⟯ ∣
      Module.finrank (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    (IntermediateField.finrank_dvd_of_le_right le_top).trans
      (by rw [IntermediateField.finrank_top'])
  rw [finrank_K_succ p hn] at hdvd
  rcases hp.out.eq_one_or_self_of_dvd _ hdvd with h1 | hp'
  · exfalso
    rw [IntermediateField.finrank_adjoin_simple_eq_one_iff, IntermediateField.mem_bot] at h1
    obtain ⟨c, hc⟩ := h1
    have hval : (V : ℂ_[p]) = (c : ℂ_[p]) := by rw [← hc]; rfl
    exact hbot (hval ▸ c.2)
  · exact hp'

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see below)
set_option maxHeartbeats 1000000 in
-- the `adjoin.powerBasis`/`norm_eq_norm_adjoin` computation runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; both instance synthesis and the
-- elaboration of the power-basis term exceed the defaults
/-- The norm of a generator `V` of `K_{n+1}/K_n` with minimal polynomial
`(X+1)^p − C c` is `c − 1` (using `p` odd: `(−1)^p · (1 − c) = c − 1`). -/
private theorem norm_extendScalars_translated {n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2)
    {V : IntermediateField.extendScalars (K_le_succ p n)} {c : K p n}
    (hbot : (V : ℂ_[p]) ∉ K p n)
    (hmp : minpoly (K p n) V = (Polynomial.X + 1) ^ p - Polynomial.C c) :
    Algebra.norm (K p n) V = c - 1 := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hm : ((Polynomial.X : (K p n)[X]) + 1).Monic := by
    rw [show ((Polynomial.X : (K p n)[X]) + 1) = Polynomial.X + Polynomial.C 1 by simp]
    exact Polynomial.monic_X_add_C 1
  have hm1 : ((Polynomial.X : (K p n)[X]) + 1).natDegree = 1 := by
    rw [show ((Polynomial.X : (K p n)[X]) + 1) = Polynomial.X + Polynomial.C 1 by simp,
      Polynomial.natDegree_X_add_C]
  have hmonic : ((Polynomial.X + 1) ^ p - Polynomial.C c : (K p n)[X]).Monic := by
    have hmp' : ((Polynomial.X + 1 : (K p n)[X]) ^ p).Monic := hm.pow p
    have hdn : ((Polynomial.X + 1 : (K p n)[X]) ^ p).natDegree = p := by
      rw [hm.natDegree_pow, hm1, mul_one]
    rw [sub_eq_add_neg, ← Polynomial.C_neg]
    refine hmp'.add_of_left ?_
    rw [Polynomial.degree_eq_natDegree hmp'.ne_zero, hdn]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.pos_of_ne_zero hp0)
  have hdeg : (minpoly (K p n) V).natDegree = p := by
    rw [hmp, sub_eq_add_neg, ← Polynomial.C_neg, Polynomial.natDegree_add_C,
      hm.natDegree_pow, hm1, mul_one]
  have hint : IsIntegral (K p n) V := by
    rw [← minpoly.ne_zero_iff, hmp]; exact hmonic.ne_zero
  have htop : (K p n)⟮V⟯ = ⊤ := extendScalars_adjoin_eq_top p hn hbot
  have hnorm : Algebra.norm (K p n) V
      = (-1) ^ (minpoly (K p n) V).natDegree * (minpoly (K p n) V).coeff 0 := by
    rw [Algebra.norm_eq_norm_adjoin (K p n) V]
    have hrank : Module.finrank (↥(K p n)⟮V⟯)
        (IntermediateField.extendScalars (K_le_succ p n)) = 1 := by
      rw [htop]; exact IntermediateField.finrank_top
    rw [hrank, pow_one]
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
      (IntermediateField.adjoin.powerBasis hint)
    rwa [IntermediateField.adjoin.powerBasis_gen, IntermediateField.adjoin.powerBasis_dim,
      IntermediateField.minpoly_gen] at hpb
  rw [hnorm, hdeg, hmp, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, zero_add, one_pow,
    (hp.out.odd_of_ne_two hp2).neg_one_pow]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see below)
set_option maxHeartbeats 1000000 in
-- `adjoin.finrank` and the divisibility argument run through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer, exceeding the default budgets
/-- The minimal polynomial over `K_n` of the extendScalars element `W` whose
value is a primitive `p^{n+1}`-th root `w` (with `w^p = (c : ℂ_p)`, `c ∈ K_n`)
is `X^p − C c` (RJW TeX 2685). Degree `p = [K_{n+1}:K_n]` from `W` generating. -/
theorem minpoly_extendScalars_of_pow {n : ℕ} (hn : 1 ≤ n)
    {W : IntermediateField.extendScalars (K_le_succ p n)} {c : K p n}
    (hWc : W ^ p = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) c)
    (htop : (K p n)⟮W⟯ = ⊤) :
    minpoly (K p n) W = (Polynomial.X : (K p n)[X]) ^ p - Polynomial.C c := by
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.extendScalars (K_le_succ p n)) :=
    finiteDimensional_K p (n + 1)
  haveI : FiniteDimensional (K p n) (IntermediateField.extendScalars (K_le_succ p n)) :=
    FiniteDimensional.right ℚ_[p] (K p n) _
  have hroot : (Polynomial.aeval W) ((Polynomial.X : (K p n)[X]) ^ p - Polynomial.C c) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hWc, sub_self]
  have hint : IsIntegral (K p n) W :=
    ⟨_, Polynomial.monic_X_pow_sub_C c hp.out.ne_zero, hroot⟩
  have hdeg : (minpoly (K p n) W).natDegree = p := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [htop, IntermediateField.finrank_top', finrank_K_succ p hn] at h1
    exact h1.symm
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (Polynomial.monic_X_pow_sub_C c hp.out.ne_zero) (minpoly.dvd _ _ hroot) ?_).symm
  rw [Polynomial.natDegree_X_pow_sub_C, hdeg]

/-- **The norm collapse** (RJW TeX 2581–2585): for `b` coprime to `p`,
`N_{n+1,n}(ξ^b_{p^{n+1}} − 1) = ξ^b_{p^n} − 1`. The fixed system gives
`(ξ^b_{p^{n+1}})^p = ξ^b_{p^n}` (`zetaSys_pow_p`), and `ξ^b_{p^{n+1}}` is a
primitive `p^{n+1}`-th root generating `K_{n+1}/K_n` with minimal polynomial
`X^p − ξ^b_{p^n}`; the constant-term/sign computation (`p` odd) finishes.

Statement note (T903): `hp2 : p ≠ 2` is added — RJW §9 fixes `p` odd (TeX 2470),
and `p = 2` would give `+(1 − ξ^b_n)` not `ξ^b_n − 1`. -/
theorem levelNorm_zetaSys_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2)
    {b : ℕ} (hb : ¬ p ∣ b) :
    levelNorm p n (zetaSys p (n + 1) ^ b - 1) = zetaSys p n ^ b - 1 := by
  -- `w := ξ^b_{p^{n+1}}` is a primitive `p^{n+1}`-th root not in `K_n`
  have hw : IsPrimitiveRoot (zetaSys p (n + 1) ^ b) (p ^ (n + 1)) :=
    (zetaSys_primitiveRoot p (n + 1)).pow_of_coprime b
      (Nat.Coprime.pow_right _ (hp.out.coprime_iff_not_dvd.2 hb).symm)
  have hwK : zetaSys p (n + 1) ^ b ∈ K p (n + 1) := pow_mem (zetaSys_mem_K p (n + 1)) b
  have hcK : zetaSys p n ^ b ∈ K p n := pow_mem (zetaSys_mem_K p n) b
  have hvK : zetaSys p (n + 1) ^ b - 1 ∈ K p (n + 1) := sub_mem hwK (one_mem _)
  -- package the extendScalars elements and the base element `c = ξ^b_n`
  set W : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨zetaSys p (n + 1) ^ b, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hwK⟩ with hW
  set c : K p n := ⟨zetaSys p n ^ b, hcK⟩ with hc
  have hWc : W ^ p = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) c := by
    apply Subtype.ext
    change (zetaSys p (n + 1) ^ b) ^ p = (zetaSys p n ^ b : ℂ_[p])
    rw [← pow_mul, mul_comm, pow_mul, zetaSys_pow_p]
  have hWbot : (W : ℂ_[p]) ∉ K p n := primitiveRoot_notMem_K p hn hw
  have hWtop : (K p n)⟮W⟯ = ⊤ := extendScalars_adjoin_eq_top p hn hWbot
  -- `V := W − 1` has value `w − 1` and minpoly `(X+1)^p − C c`
  set V : IntermediateField.extendScalars (K_le_succ p n) := W - 1 with hV
  have hVval : (V : ℂ_[p]) = zetaSys p (n + 1) ^ b - 1 := rfl
  have hWval : (W : ℂ_[p]) = zetaSys p (n + 1) ^ b := rfl
  have hVbot : (V : ℂ_[p]) ∉ K p n := by
    rw [hVval]; intro h
    refine hWbot ?_
    rw [hWval, show zetaSys p (n + 1) ^ b = (zetaSys p (n + 1) ^ b - 1) + 1 by ring]
    exact add_mem h (one_mem _)
  have hone : (1 : IntermediateField.extendScalars (K_le_succ p n))
      = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) 1 := by
    rw [map_one]
  have hmpV : minpoly (K p n) V = (Polynomial.X + 1) ^ p - Polynomial.C c := by
    rw [hV, hone, minpoly.sub_algebraMap, minpoly_extendScalars_of_pow p hn hWc hWtop]
    rw [sub_comp, pow_comp, X_comp, C_comp, map_one]
  -- the norm value, then unfold `levelNorm` and coerce
  have hnorm : Algebra.norm (K p n) V = c - 1 :=
    norm_extendScalars_translated p hn hp2 hVbot hmpV
  rw [levelNorm_apply p n hvK]
  change (Algebra.norm (K p n) V : ℂ_[p]) = zetaSys p n ^ b - 1
  rw [hnorm]
  change (zetaSys p n ^ b : ℂ_[p]) - 1 = zetaSys p n ^ b - 1
  rfl

/-- The uniformiser is norm-compatible: `N_{n+1,n}(π_{n+1}) = π_n` (RJW TeX 2581,
`b = 1` case of `levelNorm_zetaSys_pow_sub_one`; `π = ξ − 1` by definition). -/
theorem levelNorm_pi {n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2) :
    levelNorm p n (pi p (n + 1)) = pi p n := by
  have h := levelNorm_zetaSys_pow_sub_one p hn hp2 (b := 1) (by simp [hp.out.one_lt.ne'])
  simpa only [pi, pow_one] using h

/-- `𝒰_∞`, the norm-inverse-limit of the local unit groups (RJW TeX 2503): a
compatible system of units, each in its integer ring together with its inverse,
matched by the level norms `N_{n+1,n}`. The `compat` field is only imposed for
`n ≥ 1` (the level norm `N_{n+1,n}` carries the `n ≥ 1` degree-`p` step). -/
structure NormCompatUnits where
  /-- The unit at level `n`, `u_n ∈ K_n^×`. -/
  elems : ℕ → ℂ_[p]ˣ
  /-- Each `u_n` lies in the integer ring `𝒪_n`. -/
  mem : ∀ n, (elems n : ℂ_[p]) ∈ O p n
  /-- Each inverse `u_n⁻¹` lies in `𝒪_n` (so `u_n ∈ 𝒪_n^×`). -/
  inv_mem : ∀ n, ((elems n)⁻¹ : ℂ_[p]) ∈ O p n
  /-- Norm compatibility `N_{n+1,n}(u_{n+1}) = u_n` for `n ≥ 1`. -/
  compat : ∀ n, 1 ≤ n → levelNorm p n (elems (n + 1)) = elems n

namespace NormCompatUnits

variable {p}

/-- The trivial compatible system `u_n = 1` (`levelNorm` is multiplicative with
`levelNorm 1 = 1`). -/
noncomputable def one : NormCompatUnits p where
  elems _ := 1
  mem _ := one_mem _
  inv_mem _ := by simp [one_mem (O p _)]
  compat _ _ := by simpa using levelNorm_one p _

noncomputable instance : One (NormCompatUnits p) := ⟨one⟩

/-- Pointwise product of two compatible systems: memberships by `Subring.mul_mem`,
compatibility by `levelNorm_mul` (the two factors lie in `K_{n+1}` since they lie
in `𝒪_{n+1} ≤ K_{n+1}`). -/
noncomputable def mul (u v : NormCompatUnits p) : NormCompatUnits p where
  elems n := u.elems n * v.elems n
  mem n := by
    simpa only [Units.val_mul] using mul_mem (u.mem n) (v.mem n)
  inv_mem n := by
    simpa only [mul_inv_rev, Units.val_mul] using mul_mem (v.inv_mem n) (u.inv_mem n)
  compat n hn := by
    have huK : (u.elems (n + 1) : ℂ_[p]) ∈ K p (n + 1) := (Subring.mem_inf.1 (u.mem _)).1
    have hvK : (v.elems (n + 1) : ℂ_[p]) ∈ K p (n + 1) := (Subring.mem_inf.1 (v.mem _)).1
    rw [Units.val_mul, levelNorm_mul p n huK hvK, u.compat n hn, v.compat n hn, Units.val_mul]

noncomputable instance : Mul (NormCompatUnits p) := ⟨mul⟩

end NormCompatUnits

/-- The ambient `ℂ_p`-norm, restricted to a finite extension `F` of `ℚ_p` inside `ℂ_p`,
as an `AbsoluteValue F ℝ`. Used to identify it with the spectral norm. -/
private noncomputable def restrictAbs (F : IntermediateField ℚ_[p] ℂ_[p]) :
    AbsoluteValue F ℝ where
  toFun x := ‖(x : ℂ_[p])‖
  map_mul' x y := by push_cast; rw [norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero]
    exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; rfl⟩
  add_le' x y := by push_cast; exact norm_add_le _ _

/-- For `x` in a finite extension `F` of `ℚ_p` inside `ℂ_p`, the ambient `ℂ_p`-norm
agrees with the spectral norm `spectralNorm ℚ_[p] F x` — the `ℂ_p`-norm is a
multiplicative `ℚ_p`-algebra norm extending the `p`-adic norm, hence equals the
spectral norm by the unique-extension theorem (`ℚ_p` is complete). -/
private theorem norm_eq_spectralNorm {F : IntermediateField ℚ_[p] ℂ_[p]}
    [FiniteDimensional ℚ_[p] F] (x : F) : ‖(x : ℂ_[p])‖ = spectralNorm ℚ_[p] F x := by
  refine spectralNorm_unique_field_norm_ext (K := ℚ_[p]) (L := F)
    (f := restrictAbs p F) (fun k => ?_) x
  change ‖((algebraMap ℚ_[p] F k : F) : ℂ_[p])‖ = ‖k‖
  have hk : ((algebraMap ℚ_[p] F k : F) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] k := by
    rw [← IntermediateField.algebraMap_apply]; rfl
  rw [hk]; simp

/-- **Value-group fact** for `K_n`: for nonzero `c ∈ K_n`, `‖c‖^{φ(p^n)} ∈ p^ℤ`. Since
the degree `d` of the `ℚ_p`-minimal polynomial of `c` divides `φ(p^n) = [K_n:ℚ_p]` and
`‖c‖^d = ‖Φ_c(0)‖` with `Φ_c(0) ∈ ℚ_p` (spectral-norm formula, Galois-invariance), the
`φ(p^n)`-th power of `‖c‖` is a power of `‖p‖`. Washington §3 / RJW TeX 2474. -/
private theorem norm_pow_totient_mem_zpow {n : ℕ} {c : ℂ_[p]} (hc : c ∈ K p n)
    (hc0 : c ≠ 0) : ∃ k : ℤ, ‖c‖ ^ Nat.totient (p ^ n) = (p : ℝ) ^ k := by
  haveI := finiteDimensional_K p n
  set x : K p n := ⟨c, hc⟩ with hx
  have hxne : x ≠ 0 := fun h => hc0 (congrArg (Subtype.val) h)
  have hbridge := norm_eq_spectralNorm p x
  have hsn := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := K p n) x
  rw [← hbridge] at hsn
  have halg : IsAlgebraic ℚ_[p] x := Algebra.IsAlgebraic.isAlgebraic x
  have hdeg : 0 < (minpoly ℚ_[p] x).natDegree := minpoly.natDegree_pos halg.isIntegral
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  -- `‖c‖^deg = ‖Φ_c(0)‖`
  have hpow : ‖c‖ ^ (minpoly ℚ_[p] x).natDegree = ‖(minpoly ℚ_[p] x).coeff 0‖ := by
    have : (‖c‖ : ℝ)
        = ‖(minpoly ℚ_[p] x).coeff 0‖ ^ (1 / (minpoly ℚ_[p] x).natDegree : ℝ) := by
      simpa using hsn
    rw [this, ← Real.rpow_natCast (‖(minpoly ℚ_[p] x).coeff 0‖ ^ _),
      ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ (by exact_mod_cast hdeg.ne'),
      Real.rpow_one]
  -- `deg ∣ φ(p^n)`
  have hdvd : (minpoly ℚ_[p] x).natDegree ∣ Nat.totient (p ^ n) := by
    rw [← finrank_K p n]
    exact minpoly.degree_dvd halg.isIntegral
  obtain ⟨e, he⟩ := hdvd
  -- `Φ_c(0) ≠ 0` (else `‖c‖ = 0`), so `‖Φ_c(0)‖ = p^j`
  have hcoeff0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hpow; exact (pow_ne_zero _ hcpos.ne') hpow
  obtain ⟨j, hj⟩ : ∃ j : ℤ, ‖(minpoly ℚ_[p] x).coeff 0‖ = (p : ℝ) ^ j :=
    ⟨-(Padic.valuation ((minpoly ℚ_[p] x).coeff 0)),
      Padic.norm_eq_zpow_neg_valuation hcoeff0⟩
  refine ⟨j * e, ?_⟩
  rw [he, pow_mul, hpow, hj, ← zpow_natCast ((p : ℝ) ^ j) e, ← zpow_mul]

/-- **Orthogonality + integrality collapse** for the uniformiser-power basis: if
`d : Fin p → ℂ_p` has every `d j ∈ K_n` and `‖∑_{j<p} d_j π_{n+1}^j‖ ≤ 1`, then every
`‖d_j‖ ≤ 1` (`d_j ∈ O_n`). Since `K_{n+1}/K_n` is totally ramified of degree `p`, the
nonzero terms `d_j π_{n+1}^j` have *pairwise distinct* norms: their `(pφ(p^n))`-th powers
are `p^{p k_j − j}` with `j` pinned mod `p` (value-group fact `norm_pow_totient_mem_zpow`
+ `‖π_{n+1}‖^{φ(p^{n+1})} = p⁻¹`). Ultrametric orthogonality
(`norm_sum_eq_sup'_of_pairwise_ne`) gives `‖d_j π_{n+1}^j‖ ≤ ‖∑‖ ≤ 1`, and `j < p`
forces `k_j ≥ 0`, i.e. `‖d_j‖ ≤ 1`. Washington, *Cyclotomic Fields* §3. -/
private theorem forall_norm_le_one_of_norm_sum_pi_pow_le_one {n : ℕ} (hn : 1 ≤ n)
    (d : Fin p → ℂ_[p]) (hdK : ∀ j, d j ∈ K p n)
    (hsum : ‖∑ j : Fin p, d j * pi p (n + 1) ^ (j : ℕ)‖ ≤ 1) :
    ∀ j, ‖d j‖ ≤ 1 := by
  classical
  set M := Nat.totient (p ^ n) with hM
  have hMpos : 0 < M := Nat.totient_pos.2 (pow_pos hp.out.pos n)
  have hM1 : Nat.totient (p ^ (n + 1)) = p * M := by
    rw [hM, Nat.totient_prime_pow hp.out (by omega : 0 < n + 1),
      Nat.totient_prime_pow hp.out hn, Nat.add_sub_cancel]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← mul_assoc, ← pow_succ']
  have hqpM : ‖pi p (n + 1)‖ ^ (p * M) = (p : ℝ)⁻¹ := by
    rw [← hM1]; exact norm_pi_pow_totient p (by omega)
  have hpgt1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  set f : Fin p → ℂ_[p] := fun j => d j * pi p (n + 1) ^ (j : ℕ) with hf
  have hnormf : ∀ j : Fin p, ‖f j‖ = ‖d j‖ * ‖pi p (n + 1)‖ ^ (j : ℕ) := by
    intro j; rw [hf]; simp [norm_mul, norm_pow]
  -- nonzero terms have pairwise distinct norms
  have hdist : ∀ a b : Fin p, a ≠ b → f a ≠ 0 → f b ≠ 0 →
      ‖f a‖ ≠ ‖f b‖ := by
    intro a b hab hfa hfb heqn
    rw [hnormf, hnormf] at heqn
    have hda : d a ≠ 0 := by rw [hf] at hfa; exact left_ne_zero_of_mul hfa
    have hdb : d b ≠ 0 := by rw [hf] at hfb; exact left_ne_zero_of_mul hfb
    obtain ⟨ka, hka⟩ := norm_pow_totient_mem_zpow p (hdK a) hda
    obtain ⟨kb, hkb⟩ := norm_pow_totient_mem_zpow p (hdK b) hdb
    rw [← hM] at hka hkb
    have hraise : (‖d a‖ * ‖pi p (n + 1)‖ ^ (a : ℕ)) ^ (p * M)
        = (‖d b‖ * ‖pi p (n + 1)‖ ^ (b : ℕ)) ^ (p * M) := by rw [heqn]
    rw [mul_pow, mul_pow] at hraise
    have hdaM : ‖d a‖ ^ (p * M) = (p : ℝ) ^ (ka * p) := by
      rw [mul_comm p M, pow_mul, hka, ← zpow_natCast ((p : ℝ) ^ ka) p, ← zpow_mul]
    have hdbM : ‖d b‖ ^ (p * M) = (p : ℝ) ^ (kb * p) := by
      rw [mul_comm p M, pow_mul, hkb, ← zpow_natCast ((p : ℝ) ^ kb) p, ← zpow_mul]
    have hqa : (‖pi p (n + 1)‖ ^ (a : ℕ)) ^ (p * M) = (p : ℝ) ^ (-(a : ℕ) : ℤ) := by
      rw [← pow_mul, mul_comm (a : ℕ) (p * M), pow_mul, hqpM,
        ← zpow_natCast ((p : ℝ)⁻¹) (a : ℕ), inv_zpow, ← zpow_neg]
    have hqb : (‖pi p (n + 1)‖ ^ (b : ℕ)) ^ (p * M) = (p : ℝ) ^ (-(b : ℕ) : ℤ) := by
      rw [← pow_mul, mul_comm (b : ℕ) (p * M), pow_mul, hqpM,
        ← zpow_natCast ((p : ℝ)⁻¹) (b : ℕ), inv_zpow, ← zpow_neg]
    rw [hdaM, hqa, hdbM, hqb, ← zpow_add₀ hp0.ne', ← zpow_add₀ hp0.ne'] at hraise
    have hexp : ka * p + (-(a : ℕ) : ℤ) = kb * p + (-(b : ℕ) : ℤ) :=
      zpow_right_injective₀ hp0 (ne_of_gt hpgt1) hraise
    have hfactor : (ka - kb) * p = (a : ℕ) - (b : ℕ) := by
      linarith [hexp, mul_comm ka (p : ℤ)]
    have hpz : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    have hkij : ka - kb = 0 := by
      by_contra h0
      have hge : (p : ℤ) ≤ |(ka - kb) * p| := by
        rw [abs_mul, abs_of_pos hpz]
        calc (p : ℤ) = 1 * p := (one_mul _).symm
          _ ≤ |ka - kb| * p := mul_le_mul_of_nonneg_right (Int.one_le_abs h0) hpz.le
      rw [hfactor] at hge
      have ha' := a.2; have hb' := b.2
      have hbnd : |((a : ℕ) : ℤ) - (b : ℕ)| < p := by rw [abs_lt]; omega
      omega
    rw [hkij, zero_mul] at hfactor
    exact hab (Fin.ext (by omega))
  -- each term ≤ the sum norm (orthogonality on the nonzero support)
  intro j
  have hterm_le : ‖f j‖ ≤ ‖∑ jj : Fin p, f jj‖ := by
    set S : Finset (Fin p) := Finset.univ.filter (fun jj => f jj ≠ 0) with hS
    have hsumS : ∑ jj : Fin p, f jj = ∑ jj ∈ S, f jj := by
      rw [hS]; symm; exact Finset.sum_filter_of_ne (fun jj _ hne => hne)
    rcases eq_or_ne (f j) 0 with hfj | hfj
    · rw [hfj, norm_zero]; positivity
    · have hjS : j ∈ S := by rw [hS]; simp [hfj]
      have hSne : S.Nonempty := ⟨j, hjS⟩
      have hpw : (↑S : Set (Fin p)).Pairwise (fun a b => ‖f a‖ ≠ ‖f b‖) := by
        intro a ha b hb hab
        rw [hS, Finset.coe_filter] at ha hb
        exact hdist a b hab ha.2 hb.2
      rw [hsumS, IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne hSne hpw]
      exact Finset.le_sup' (fun jj => ‖f jj‖) hjS
  have hle1 : ‖d j‖ * ‖pi p (n + 1)‖ ^ (j : ℕ) ≤ 1 := by
    rw [← hnormf]; exact le_trans hterm_le hsum
  -- collapse: `d j = 0` trivial; else `‖d j‖ = q^{-pk}` with the exponent forcing `k ≥ 0`
  rcases eq_or_ne (d j) 0 with hdj0 | hdj0
  · rw [hdj0, norm_zero]; exact zero_le_one
  obtain ⟨k, hk⟩ := norm_pow_totient_mem_zpow p (hdK j) hdj0
  rw [← hM] at hk
  have hpos : (0 : ℝ) ≤ ‖d j‖ * ‖pi p (n + 1)‖ ^ (j : ℕ) := by positivity
  have hraise : (‖d j‖ * ‖pi p (n + 1)‖ ^ (j : ℕ)) ^ (p * M) ≤ 1 :=
    calc (‖d j‖ * ‖pi p (n + 1)‖ ^ (j : ℕ)) ^ (p * M) ≤ 1 ^ (p * M) :=
          pow_le_pow_left₀ hpos hle1 (p * M)
      _ = 1 := one_pow _
  rw [mul_pow] at hraise
  have hdM : ‖d j‖ ^ (p * M) = (p : ℝ) ^ (k * p) := by
    rw [mul_comm p M, pow_mul, hk, ← zpow_natCast ((p : ℝ) ^ k) p, ← zpow_mul]
  have hqj : (‖pi p (n + 1)‖ ^ (j : ℕ)) ^ (p * M) = (p : ℝ) ^ (-(j : ℕ) : ℤ) := by
    rw [← pow_mul, mul_comm (j : ℕ) (p * M), pow_mul, hqpM,
      ← zpow_natCast ((p : ℝ)⁻¹) (j : ℕ), inv_zpow, ← zpow_neg]
  rw [hdM, hqj, ← zpow_add₀ hp0.ne'] at hraise
  have hexp : k * p + (-(j : ℕ) : ℤ) ≤ 0 := by
    by_contra h; push Not at h
    exact absurd hraise (not_le.mpr (one_lt_zpow₀ hpgt1 (by omega)))
  have hjlt := j.2
  have hkle : k ≤ 0 := by nlinarith [hexp, hjlt, hp.out.pos]
  have hdMle : ‖d j‖ ^ M ≤ 1 := by
    rw [hk]
    calc (p : ℝ) ^ k ≤ (p : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ hpgt1.le hkle
      _ = 1 := by simp
  exact le_of_pow_le_pow_left₀ hMpos.ne' (by norm_num) (by rwa [one_pow])

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see below)
set_option maxHeartbeats 1000000 in
-- the `adjoin.powerBasis`/`Basis.sum_repr` computation runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer; both instance synthesis and the
-- power-basis term elaboration exceed the defaults
/-- `K_n`-coordinate expansion in the tower step: for an integral generator `W` of
`K_{n+1}/K_n` (`(K_n)⟮W⟯ = ⊤`, the step has degree `p`), every element is uniquely
`∑_{i<p} c_i W^i` with `c_i ∈ K_n` — `W` carries a power basis of dimension `p`
(`adjoin.powerBasis` + `finrank_K_succ`). RJW TeX 2685. -/
private theorem extendScalars_exists_repr {n : ℕ} (hn : 1 ≤ n)
    {W : IntermediateField.extendScalars (K_le_succ p n)}
    (hint : IsIntegral (K p n) W) (htop : (K p n)⟮W⟯ = ⊤)
    (x : IntermediateField.extendScalars (K_le_succ p n)) :
    ∃ c : Fin p → K p n, x = ∑ i : Fin p, c i • W ^ (i : ℕ) := by
  have hdim : (IntermediateField.adjoin.powerBasis hint).dim = p := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    have h1 := IntermediateField.adjoin.finrank hint
    rw [htop, IntermediateField.finrank_top', finrank_K_succ p hn] at h1
    exact h1.symm
  set e : (K p n)⟮W⟯ ≃ₐ[K p n] IntermediateField.extendScalars (K_le_succ p n) :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv with he
  set pb := (IntermediateField.adjoin.powerBasis hint).map e with hpb
  have hgen : pb.gen = W := by
    rw [hpb, PowerBasis.map_gen, IntermediateField.adjoin.powerBasis_gen, he]; rfl
  have hpbdim : pb.dim = p := by rw [hpb, PowerBasis.map_dim]; exact hdim
  refine ⟨fun i : Fin p => pb.basis.repr x (Fin.cast hpbdim.symm i), ?_⟩
  conv_lhs => rw [← pb.basis.sum_repr x, PowerBasis.coe_basis]
  refine Fintype.sum_equiv (finCongr hpbdim)
    (fun j => pb.basis.repr x j • pb.gen ^ (j : ℕ))
    (fun i => pb.basis.repr x (Fin.cast hpbdim.symm i) • W ^ (i : ℕ)) ?_
  intro j
  rw [finCongr_apply, hgen]
  congr 2

/-- The extendScalars element `⟨ξ_{n+1}, _⟩` is an integral generator of `K_{n+1}/K_n`
(it is `ξ_{n+1}`, a primitive `p^{n+1}`-th root with `ξ_{n+1}^p = ξ_n ∈ K_n` and
`ξ_{n+1} ∉ K_n`). Used to expand `K_{n+1}` in `ξ`- and (translating) `π`-powers. -/
private theorem zetaSys_extendScalars_generator {n : ℕ} (hn : 1 ≤ n) :
    ∃ W : IntermediateField.extendScalars (K_le_succ p n),
      (W : ℂ_[p]) = zetaSys p (n + 1) ∧ IsIntegral (K p n) W ∧ (K p n)⟮W⟯ = ⊤ := by
  have hwK : zetaSys p (n + 1) ∈ K p (n + 1) := zetaSys_mem_K p (n + 1)
  set W : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨zetaSys p (n + 1), (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hwK⟩ with hW
  refine ⟨W, rfl, ?_, ?_⟩
  · set cc : K p n := ⟨zetaSys p n, zetaSys_mem_K p n⟩ with hcc
    have hWc : W ^ p = algebraMap (K p n) (IntermediateField.extendScalars (K_le_succ p n)) cc := by
      apply Subtype.ext
      change (zetaSys p (n + 1)) ^ p = (zetaSys p n : ℂ_[p])
      rw [zetaSys_pow_p]
    have hroot : (Polynomial.aeval W) ((Polynomial.X : (K p n)[X]) ^ p - Polynomial.C cc) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hWc, sub_self]
    exact ⟨_, Polynomial.monic_X_pow_sub_C cc hp.out.ne_zero, hroot⟩
  · exact extendScalars_adjoin_eq_top p hn
      (primitiveRoot_notMem_K p hn (zetaSys_primitiveRoot p (n + 1)))

/-- **Uniformiser-power coordinate expansion**: every `x ∈ K_{n+1}` is `∑_{k<p} d_k π_{n+1}^k`
with `d_k ∈ K_n`. (Translate the `ξ_{n+1}`-power basis by `π_{n+1} = ξ_{n+1} − 1`:
`ξ_{n+1} − 1` is the integral generator `V = W − 1`.) Feeds the integrality collapse. -/
private theorem exists_pi_repr {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) :
    ∃ d : Fin p → ℂ_[p], (∀ k, d k ∈ K p n) ∧
      x = ∑ k : Fin p, d k * pi p (n + 1) ^ (k : ℕ) := by
  obtain ⟨W, hWval, hWint, hWtop⟩ := zetaSys_extendScalars_generator p hn
  -- V = W − 1 generates `K_{n+1}/K_n` and is integral; its value is `π_{n+1}`
  set V : IntermediateField.extendScalars (K_le_succ p n) := W - 1 with hV
  have hVval : (V : ℂ_[p]) = pi p (n + 1) := by
    rw [hV]; push_cast; rw [hWval, pi]
  have hVbot : (V : ℂ_[p]) ∉ K p n := by
    rw [hVval, pi]; intro h
    refine primitiveRoot_notMem_K p hn (zetaSys_primitiveRoot p (n + 1)) ?_
    simpa using add_mem h (one_mem (K p n))
  have hVtop : (K p n)⟮V⟯ = ⊤ := extendScalars_adjoin_eq_top p hn hVbot
  have hVint : IsIntegral (K p n) V := hWint.sub isIntegral_one
  set xes : IntermediateField.extendScalars (K_le_succ p n) :=
    ⟨x, (IntermediateField.mem_extendScalars (K_le_succ p n)).2 hx⟩ with hxes
  obtain ⟨c, hc⟩ := extendScalars_exists_repr p hn hVint hVtop xes
  refine ⟨fun k => ((c k : K p n) : ℂ_[p]), fun k => (c k).2, ?_⟩
  have hcoe : (xes : ℂ_[p])
      = ∑ k : Fin p, ((c k : K p n) : ℂ_[p]) * (V : ℂ_[p]) ^ (k : ℕ) := by
    rw [hc]; push_cast
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Algebra.smul_def]; congr 1
  rw [hVval] at hcoe
  simpa using hcoe

/-- Each uniformiser power `π_{n+1}^k` (`k < p`) lies in the `O_n`-span of the
`ξ_{n+1}`-powers `{ξ_{n+1}^i : i < p}`: expand `π_{n+1}^k = (ξ_{n+1} − 1)^k` by the
binomial theorem — the coefficients are integers (hence in `O_n`) and the exponents
`i ≤ k < p`. This is the integral change of basis `π`-powers ↦ `ξ`-powers. -/
private theorem pi_pow_mem_span {n : ℕ} {k : ℕ} (hk : k < p) :
    pi p (n + 1) ^ k ∈ Submodule.span (O p n)
      (Set.range (fun i : Fin p => zetaSys p (n + 1) ^ (i : ℕ))) := by
  have hintO : ∀ m : ℤ, (m : ℂ_[p]) ∈ O p n := fun m => by
    rw [O, Subring.mem_inf]
    exact ⟨by exact_mod_cast (K p n).intCast_mem m,
      IsUltrametricDist.norm_intCast_le_one ℂ_[p] m⟩
  rw [pi, sub_eq_add_neg, add_pow]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have hilt : i < p := by omega
  set co : ℂ_[p] := (-1 : ℂ_[p]) ^ (k - i) * (k.choose i : ℂ_[p]) with hco
  have hcoO : co ∈ O p n := by
    rw [hco, show ((-1 : ℂ_[p]) ^ (k - i) * (k.choose i : ℂ_[p]))
      = (((-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) : ℤ) : ℂ_[p]) by push_cast; ring]
    exact hintO _
  have hterm : zetaSys p (n + 1) ^ i * (-1 : ℂ_[p]) ^ (k - i) * (k.choose i : ℂ_[p])
      = co • zetaSys p (n + 1) ^ i := by rw [hco, smul_eq_mul]; ring
  rw [hterm]
  have hmem : zetaSys p (n + 1) ^ i
      ∈ Set.range (fun j : Fin p => zetaSys p (n + 1) ^ (j : ℕ)) := ⟨⟨i, hilt⟩, rfl⟩
  exact Submodule.smul_mem _ (⟨co, hcoO⟩ : O p n) (Submodule.subset_span hmem)

/-- **R10.2 / RJW TeX 2685 (existence of the integral `O_n`-basis expansion)**: every
`x ∈ O_{n+1}` is `∑_{i<p} c_i ξ_{n+1}^i` with all `c_i ∈ O_n` — i.e. `O_{n+1}` is the
`O_n`-span of `{ξ_{n+1}^i : i < p}` (one half of `O_{n+1} = ⊕_{i<p} O_n·ξ_{n+1}^i`).

Proof: expand `x` in the *uniformiser* powers `x = ∑ d_k π_{n+1}^k` (`d_k ∈ K_n`,
`exists_pi_repr`); since `‖x‖ ≤ 1` and `K_{n+1}/K_n` is totally ramified, orthogonality
forces every `d_k ∈ O_n` (`forall_norm_le_one_of_norm_sum_pi_pow_le_one`); finally each
`π_{n+1}^k` is an integral combination of the `ξ_{n+1}^i` (`pi_pow_mem_span`), so `x`
lies in the `O_n`-span of the `ξ`-powers. RJW TeX 2474 (`O_n`), 2685 (the step). -/
theorem O_succ_exists_digits {n : ℕ} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ O p (n + 1)) :
    ∃ c : Fin p → ℂ_[p], (∀ i, c i ∈ O p n) ∧
      x = ∑ i : Fin p, c i * zetaSys p (n + 1) ^ (i : ℕ) := by
  obtain ⟨hxK, hxnorm⟩ := Subring.mem_inf.1 hx
  -- uniformiser-power expansion, with all coefficients in `O_n` (orthogonality collapse)
  obtain ⟨d, hdK, hxd⟩ := exists_pi_repr p hn hxK
  have hdO : ∀ k, ‖d k‖ ≤ 1 := by
    refine forall_norm_le_one_of_norm_sum_pi_pow_le_one p hn d hdK ?_
    rw [← hxd]; exact hxnorm
  -- `x ∈ O_n`-span of the `ξ`-powers
  have hxspan : x ∈ Submodule.span (O p n)
      (Set.range (fun i : Fin p => zetaSys p (n + 1) ^ (i : ℕ))) := by
    rw [hxd]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    have hdkO : d k ∈ O p n := by
      rw [O, Subring.mem_inf]; exact ⟨hdK k, hdO k⟩
    rw [show d k * pi p (n + 1) ^ (k : ℕ)
      = (⟨d k, hdkO⟩ : O p n) • pi p (n + 1) ^ (k : ℕ) from rfl]
    exact Submodule.smul_mem _ _ (pi_pow_mem_span p k.2)
  -- extract the `ξ`-coordinates
  rw [Submodule.mem_span_range_iff_exists_fun] at hxspan
  obtain ⟨c, hc⟩ := hxspan
  refine ⟨fun i => ((c i : O p n) : ℂ_[p]), fun i => (c i).2, ?_⟩
  rw [← hc]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rfl

set_option synthInstance.maxHeartbeats 1000000 in
-- nested `IntermediateField (K p n) (extendScalars …)` instance synthesis (see below)
set_option maxHeartbeats 1000000 in
-- the `linearIndependent_pow`/`adjoin.finrank` computation runs through the nested
-- `IntermediateField (K p n) (extendScalars …)` layer, exceeding the defaults
/-- The `ξ_{n+1}`-powers `{ξ_{n+1}^i : i < p}` are `K_n`-linearly independent in `ℂ_p`:
a `K_n`-combination `∑_{i<p} e_i ξ_{n+1}^i = 0` with `e_i ∈ K_n` has all `e_i = 0`. (They
form a power basis of `K_{n+1}/K_n`, `linearIndependent_pow`.) -/
private theorem zetaSys_pow_sum_eq_zero_imp {n : ℕ} (hn : 1 ≤ n) {e : Fin p → ℂ_[p]}
    (heK : ∀ i, e i ∈ K p n) (he0 : ∑ i : Fin p, e i * zetaSys p (n + 1) ^ (i : ℕ) = 0) :
    ∀ i, e i = 0 := by
  obtain ⟨W, hWval, hWint, hWtop⟩ := zetaSys_extendScalars_generator p hn
  -- `natDegree (minpoly K_n W) = p`
  have hdeg : (minpoly (K p n) W).natDegree = p := by
    have h1 := IntermediateField.adjoin.finrank hWint
    rw [hWtop, IntermediateField.finrank_top', finrank_K_succ p hn] at h1
    exact h1.symm
  -- lift the `ℂ_p`-relation to `extendScalars`
  set ees : Fin p → K p n := fun i => ⟨e i, heK i⟩ with hees
  have hlift : ∑ i : Fin p, ees i • W ^ (i : ℕ) = 0 := by
    apply Subtype.ext
    rw [IntermediateField.coe_sum, ZeroMemClass.coe_zero, ← he0]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [IntermediateField.coe_smul, hees]
    change (e i) * (W : ℂ_[p]) ^ (i : ℕ) = e i * zetaSys p (n + 1) ^ (i : ℕ)
    rw [hWval]
  -- linear independence of `W`-powers, reindexed `Fin p ≃ Fin (natDegree)`
  have hli := linearIndependent_pow (K := K p n) W
  rw [Fintype.linearIndependent_iff] at hli
  -- transport `ees` along `Fin p = Fin (natDegree)`
  have hsum' : ∑ i : Fin (minpoly (K p n) W).natDegree,
      (fun i => ees (Fin.cast hdeg i)) i • W ^ (i : ℕ) = 0 := by
    rw [← hlift]
    refine (Fintype.sum_equiv (finCongr hdeg.symm) _ _ (fun i => ?_)).symm
    rw [finCongr_apply]
    congr 2
  have hzero := hli (fun i => ees (Fin.cast hdeg i)) hsum'
  intro i
  have := hzero (Fin.cast hdeg.symm i)
  rw [Fin.cast_cast, Fin.cast_eq_self] at this
  have hval : (ees i : ℂ_[p]) = ((0 : K p n) : ℂ_[p]) := congrArg (Subtype.val) this
  simpa [hees] using hval

/-- **R10.2 / RJW TeX 2685 (uniqueness of the integral basis expansion)**: the
`Fin p` `ξ_{n+1}`-power expansion with `K_n`-coefficients is unique — the other half of
`O_{n+1} = ⊕_{i<p} O_n·ξ_{n+1}^i`. (`K_n`-coefficients suffice; the `ξ`-powers are a
`K_n`-basis of `K_{n+1}`.) RJW TeX 2685. -/
theorem O_succ_digits_unique {n : ℕ} (hn : 1 ≤ n) {c c' : Fin p → ℂ_[p]}
    (hc : ∀ i, c i ∈ K p n) (hc' : ∀ i, c' i ∈ K p n)
    (heq : ∑ i : Fin p, c i * zetaSys p (n + 1) ^ (i : ℕ)
      = ∑ i : Fin p, c' i * zetaSys p (n + 1) ^ (i : ℕ)) :
    c = c' := by
  have hsub : ∑ i : Fin p, (c i - c' i) * zetaSys p (n + 1) ^ (i : ℕ) = 0 := by
    rw [← sub_eq_zero] at heq
    rw [← heq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have := zetaSys_pow_sum_eq_zero_imp p hn
    (e := fun i => c i - c' i) (fun i => sub_mem (hc i) (hc' i)) hsub
  funext i
  exact sub_eq_zero.mp (this i)

end Coleman

end PadicLFunctions
