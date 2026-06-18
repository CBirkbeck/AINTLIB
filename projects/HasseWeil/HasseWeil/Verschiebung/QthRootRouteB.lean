/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.GapQfKernel
import HasseWeil.Verschiebung.Cascade
import HasseWeil.Verschiebung.Route2Universal

/-!
# The universal q-th-root witness (general characteristic) — Route B

This file discharges, for an arbitrary finite field `K` (`q = #K = p^k`,
`p = char K`), the **universal q-th-root witness**

```
h_qth_root : ∀ z, ∃ g, g ^ q = [q]* z
```

(`[q]*` the pullback of the multiplication-by-q isogeny on `K(E)`), and feeds
it through the proven reducer `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`
to obtain `verschiebung_isDualOf_frobenius_general` — the GAP-QF keystone.

## Strategy (uniform in `p`, no per-prime polynomial witnesses)

The keystone reduces (via `mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness`
and `functionField_eq_intermediateField_adjoin_xy`) to two generator facts:

* `[q]* x_gen ∈ R` and `[q]* y_gen ∈ R`, where `R = (frobeniusIsog W).pullback.range = K(E)^q`.

Both are obtained from the **Kähler differential** kernel theorem
`kaehlerD_eq_zero_iff_mem_pth_powers` (`ker D = K(E)^p`, char `p`) and the
**separability** of `K(E)/K(x_gen)` (`functionField_isSeparable`), with no
characteristic-specific polynomial computation:

* **x-side base** `[p]* x_gen ∈ adjoin K {x_gen^p}`: `[p]* x_gen` is rational in
  `x_gen` (so lies in `K(x_gen)`) and has `D([p]* x_gen) = 0`
  (`D_mulByInt_p_pullback_x_gen_eq_zero`), hence is a `p`-th power `g^p` with
  `g ∈ K(E)`; since `K(E)/K(x_gen)` is separable, the purely-inseparable element
  `g` lies in `K(x_gen)`, so `[p]* x_gen = g^p ∈ adjoin K {x_gen^p}`. The
  existing induction `mulByInt_pow_pullback_x_gen_mem_adjoin_pow_of_base`-style
  bootstrap (re-derived here taking the Kähler base) lifts this to
  `[q]* x_gen ∈ adjoin K {x_gen^q} ⊆ R`.
* **y-side** `[q]* y_gen ∈ R`: `y_gen` satisfies the separable Weierstrass
  quadratic over `K(x_gen)`; applying `[q]*` gives that `[q]* y_gen` is a root of
  a **separable** quadratic over `R` (its discriminant is `([q]*(2y+a₁x+a₃))² ≠ 0`,
  using injectivity of `[q]*` and `2y+a₁x+a₃ ≠ 0`), with coefficients in `R`
  (because `[q]* x_gen ∈ R`). So `[q]* y_gen` is separable over `R`; as `K(E)/R`
  is purely inseparable (`frobeniusIsog_intermediateField_isPurelyInseparable`),
  `[q]* y_gen ∈ R`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2.12, III.5.5, III.6.2.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

local notation "Mff" => FractionRing (Polynomial K)

omit [Fintype K] [DecidableEq K] in
/-- **Separable-root descent**: if `g : K(E)` and `g ^ p ∈ Im(M → K(E))`
(`M = FractionRing K[X]`, `p = char K` prime), then `g ∈ Im(M → K(E))`. -/
theorem mem_fractionRing_range_of_pow_mem (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : KE) (hg : g ^ p ∈ (algebraMap Mff KE).range) :
    g ∈ (algebraMap Mff KE).range := by
  haveI : Algebra.IsSeparable Mff KE := functionField_isSeparable W.toAffine
  haveI : CharP (Polynomial K) p := inferInstance
  haveI : CharP Mff p := inferInstance
  haveI : ExpChar Mff p := ExpChar.prime Fact.out
  have hsep : IsSeparable Mff g := Algebra.IsSeparable.isSeparable Mff g
  have hsd1 : (minpoly Mff g).natSepDegree = 1 := by
    rw [minpoly.natSepDegree_eq_one_iff_pow_mem p]
    exact ⟨1, by rwa [pow_one]⟩
  have hsd_nd : (minpoly Mff g).natSepDegree = (minpoly Mff g).natDegree :=
    Polynomial.Separable.natSepDegree_eq_natDegree hsep
  have hnd1 : (minpoly Mff g).natDegree = 1 := by rw [← hsd_nd, hsd1]
  have hdeg1 : (minpoly Mff g).degree = 1 := by
    have hint : IsIntegral Mff g := Algebra.IsIntegral.isIntegral g
    rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), hnd1]; rfl
  exact minpoly.mem_range_of_degree_eq_one Mff g hdeg1

omit [Fintype K] [DecidableEq K] in
/-- `algebraMap (Polynomial K) K(E) q = algebraMap M K(E) (algebraMap (Polynomial K) M q)`,
the scalar-tower factoring of the structure map through `M = FractionRing K[X]`. -/
theorem algebraMap_polynomial_eq_fractionRing (q : Polynomial K) :
    algebraMap (Polynomial K) KE q =
      algebraMap Mff KE (algebraMap (Polynomial K) Mff q) := by
  haveI : IsScalarTower (Polynomial K) Mff KE := functionField_isScalarTower W.toAffine
  rw [← IsScalarTower.algebraMap_apply]

omit [Fintype K] [DecidableEq K] in
/-- `x_gen` lies in `Im(M → K(E))`. -/
theorem x_gen_mem_fractionRing_range :
    x_gen W ∈ (algebraMap Mff KE).range := by
  refine ⟨algebraMap (Polynomial K) Mff Polynomial.X, ?_⟩
  rw [← algebraMap_polynomial_eq_fractionRing]
  rfl

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- `algebraMap (Polynomial K) K(E) q ∈ K⟮x_gen⟯` — the structure map applied to a
polynomial lands in the simple adjoin (it is `aeval x_gen q` with `K`-coefficients). -/
theorem algebraMap_polynomial_mem_adjoin_x_gen (q : Polynomial K) :
    algebraMap (Polynomial K) KE q ∈ IntermediateField.adjoin K ({x_gen W} : Set KE) := by
  have hx : x_gen W ∈ IntermediateField.adjoin K ({x_gen W} : Set KE) :=
    IntermediateField.subset_adjoin _ _ rfl
  have hXgen : algebraMap (Polynomial K) KE Polynomial.X = x_gen W :=
    IsScalarTower.algebraMap_apply (Polynomial K) W.toAffine.CoordinateRing
      W.toAffine.FunctionField Polynomial.X
  induction q using Polynomial.induction_on with
  | C a =>
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (Polynomial K) KE a]
      exact IntermediateField.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
      rw [map_mul, map_pow, hXgen]
      refine mul_mem ?_ (pow_mem hx _)
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply K (Polynomial K) KE a]
      exact IntermediateField.algebraMap_mem _ a

omit [Fintype K] [DecidableEq K] in
/-- `Im(M → K(E)) ⊆ K⟮x_gen⟯`: every value of the structure map `M → K(E)` lies in
the simple adjoin `K⟮x_gen⟯`. -/
theorem mem_adjoin_x_gen_of_mem_fractionRing_range {g : KE}
    (hg : g ∈ (algebraMap Mff KE).range) :
    g ∈ IntermediateField.adjoin K ({x_gen W} : Set KE) := by
  obtain ⟨z, rfl⟩ := hg
  obtain ⟨r, s, _, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial K) z
  rw [map_div₀, ← algebraMap_polynomial_eq_fractionRing,
    ← algebraMap_polynomial_eq_fractionRing]
  exact div_mem (algebraMap_polynomial_mem_adjoin_x_gen W r)
    (algebraMap_polynomial_mem_adjoin_x_gen W s)

omit [Fintype K] [DecidableEq K] in
/-- `Φ_ff W n` and `ΨSq_ff W n` lie in `Im(M → K(E))`, hence so does
`mulByInt_x W n = [n]* x_gen`. -/
theorem mulByInt_x_mem_fractionRing_range (n : ℤ) :
    mulByInt_x W n ∈ (algebraMap Mff KE).range := by
  have hΦ : Φ_ff W n ∈ (algebraMap Mff KE).range :=
    ⟨algebraMap (Polynomial K) Mff (W.Φ n), by
      rw [← algebraMap_polynomial_eq_fractionRing]; rfl⟩
  have hΨ : ΨSq_ff W n ∈ (algebraMap Mff KE).range :=
    ⟨algebraMap (Polynomial K) Mff (W.ΨSq n), by
      rw [← algebraMap_polynomial_eq_fractionRing]; rfl⟩
  obtain ⟨a, ha⟩ := hΦ
  obtain ⟨b, hb⟩ := hΨ
  exact ⟨a / b, by rw [map_div₀, ha, hb]; rfl⟩

/-- **x-side base (general characteristic)**: `[p]* x_gen ∈ adjoin K {x_gen ^ p}`. -/
theorem mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ p} : Set KE) := by
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap K KE).injective p
  have hp_ne : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  have hD := D_mulByInt_p_pullback_x_gen_eq_zero W p
  obtain ⟨g, hg⟩ := (kaehlerD_eq_zero_iff_mem_pth_powers W p _).mp hD
  have hmul : (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W) = mulByInt_x W (p : ℤ) := by
    rw [show x_gen W = algebraMap W.toAffine.CoordinateRing KE
          (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) from rfl,
      mulByInt_pullback_x W (p : ℤ) hp_ne]
  have hpow_mem : g ^ p ∈ (algebraMap Mff KE).range := by
    rw [hg, hmul]; exact mulByInt_x_mem_fractionRing_range W (p : ℤ)
  have hg_mem : g ∈ IntermediateField.adjoin K ({x_gen W} : Set KE) :=
    mem_adjoin_x_gen_of_mem_fractionRing_range W
      (mem_fractionRing_range_of_pow_mem W p g hpow_mem)
  rw [← hg]
  exact adjoin_simple_pow_le_adjoin_simple_pow p (x_gen W) g hg_mem

omit [Fintype K] in
/-- `[p ^ (k+1)]` factors as `[p ^ k] ∘ [p]` (shared scaffolding for the x- and
y-side `p^k`-power inductions). -/
private theorem mulByInt_pow_succ_comp (p : ℕ) [Fact p.Prime] (k : ℕ) :
    mulByInt W.toAffine ((p ^ (k + 1) : ℕ) : ℤ) =
      (mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).comp
        (mulByInt W.toAffine ((p : ℕ) : ℤ)) := by
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp_ne : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp_pos.ne'
  have hpk_ne : ((p ^ k : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero k hp_pos.ne'
  rw [show ((p ^ (k + 1) : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) * ((p : ℕ) : ℤ) by
    push_cast; rw [pow_succ]]
  exact (mulByInt_comp_eq_mul W ((p ^ k : ℕ) : ℤ) ((p : ℕ) : ℤ) hpk_ne hp_ne
    (mul_ne_zero hpk_ne hp_ne)).symm

/-- **x-side, all powers (general characteristic)**: for all `k`,
`[p^k]* x_gen ∈ adjoin K {x_gen ^ (p^k)}`. -/
theorem mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∀ k, (mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (x_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ (p ^ k : ℕ)} : Set KE) := by
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap K KE).injective p
  intro k
  induction k with
  | zero => exact mulByInt_pow_zero_pullback_x_gen_mem_adjoin_pow W p
  | succ k ih =>
    rw [mulByInt_pow_succ_comp W p k]
    change (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback
        ((mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (x_gen W)) ∈ _
    have h_in_image :
        (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback
            ((mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (x_gen W)) ∈
          (IntermediateField.adjoin K ({x_gen W ^ (p ^ k : ℕ)} : Set _)).map
            (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback :=
      ⟨_, ih, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow] at h_in_image
    have h_base : (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback (x_gen W) ∈
        IntermediateField.adjoin K ({x_gen W ^ p} : Set _) := by
      have := mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB W p
      rwa [show ((p : ℕ) : ℤ) = (p : ℤ) from rfl]
    have h_pow : ((mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback (x_gen W)) ^ (p ^ k) ∈
        IntermediateField.adjoin K ({x_gen W ^ (p ^ (k + 1) : ℕ)} : Set _) := by
      have h_iter := adjoin_simple_pow_pow_le_adjoin_simple_pow_pow p (x_gen W ^ p) k
        _ h_base
      have h_eq : ((x_gen W ^ p) ^ (p ^ k) : KE) = x_gen W ^ (p ^ (k + 1) : ℕ) := by
        rw [← pow_mul]; congr 1; rw [← pow_succ']
      rwa [h_eq] at h_iter
    exact IntermediateField.adjoin_le_iff.mpr
      (Set.singleton_subset_iff.mpr h_pow) h_in_image

/-- **x-side, at `q = #K` (general characteristic)**: `[q]* x_gen ∈ adjoin K {x_gen ^ q}`. -/
theorem mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ (Fintype.card K : ℕ)} : Set KE) := by
  obtain ⟨⟨n, _⟩, _, hcard⟩ := FiniteField.card K p
  rw [hcard]
  exact mulByInt_pow_pullback_x_gen_mem_adjoin_pow_routeB W p n

/-- `adjoin K {x_gen ^ q} ≤ Im(π*)` (= `K(E)^q`): the simple adjoin of the `q`-th
power `x_gen^q` is contained in the Frobenius intermediate field, since the latter
is an intermediate field over `K` containing `x_gen^q`. -/
theorem adjoin_pow_card_x_gen_le_frobenius :
    IntermediateField.adjoin K ({x_gen W ^ (Fintype.card K : ℕ)} : Set KE) ≤
      frobeniusIsog_intermediateField W :=
  IntermediateField.adjoin_le_iff.mpr <| Set.singleton_subset_iff.mpr <|
    pow_card_mem_frobeniusIsog_intermediateField W (x_gen W)

/-- **x-side conclusion**: `[q]* x_gen ∈ Im(π*) = K(E)^q`. -/
theorem mulByInt_card_pullback_x_gen_mem_frobenius
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈
      frobeniusIsog_intermediateField W :=
  adjoin_pow_card_x_gen_le_frobenius W
    (mulByInt_card_pullback_x_gen_mem_adjoin_pow_card_routeB W p)

omit [Fintype K] in
/-- The generic Weierstrass quadratic, pulled back by `[n]*`:
`([n]* y)² + (a₁·[n]* x + a₃)·([n]* y) = ([n]* x)³ + a₂([n]* x)² + a₄([n]* x) + a₆`.
Image of `generic_equation` under the K-alg hom `[n]*`. -/
theorem mulByInt_pullback_y_gen_weierstrass (n : ℤ) :
    ((mulByInt W.toAffine n).pullback (y_gen W)) ^ 2 +
      (algebraMap K KE W.a₁ * (mulByInt W.toAffine n).pullback (x_gen W) +
        algebraMap K KE W.a₃) * (mulByInt W.toAffine n).pullback (y_gen W) =
      ((mulByInt W.toAffine n).pullback (x_gen W)) ^ 3 +
        algebraMap K KE W.a₂ * ((mulByInt W.toAffine n).pullback (x_gen W)) ^ 2 +
        algebraMap K KE W.a₄ * (mulByInt W.toAffine n).pullback (x_gen W) +
        algebraMap K KE W.a₆ := by
  have h_eq := generic_equation W
  rw [Affine.equation_iff'] at h_eq
  have h_a1 : (W_KE W).a₁ = algebraMap K KE W.a₁ := rfl
  have h_a2 : (W_KE W).a₂ = algebraMap K KE W.a₂ := rfl
  have h_a3 : (W_KE W).a₃ = algebraMap K KE W.a₃ := rfl
  have h_a4 : (W_KE W).a₄ = algebraMap K KE W.a₄ := rfl
  have h_a6 : (W_KE W).a₆ = algebraMap K KE W.a₆ := rfl
  rw [h_a1, h_a2, h_a3, h_a4, h_a6] at h_eq
  have key := congrArg (mulByInt W.toAffine n).pullback h_eq
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    AlgHom.commutes] at key
  linear_combination key

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- Differential vanishing from the Weierstrass quadratic: if `D X = 0`, `Y` and `X`
satisfy `Y² + (a₁X + a₃)Y = X³ + a₂X² + a₄X + a₆`, and `2Y + a₁X + a₃ ≠ 0`, then
`D Y = 0`. -/
theorem kaehlerD_eq_zero_of_weierstrass_quadratic
    (X Y : KE) (hDX : KaehlerDifferential.D K KE X = 0)
    (hroot : Y ^ 2 + (algebraMap K KE W.a₁ * X + algebraMap K KE W.a₃) * Y =
      X ^ 3 + algebraMap K KE W.a₂ * X ^ 2 + algebraMap K KE W.a₄ * X + algebraMap K KE W.a₆)
    (hs_ne : 2 * Y + (algebraMap K KE W.a₁ * X + algebraMap K KE W.a₃) ≠ 0) :
    KaehlerDifferential.D K KE Y = 0 := by
  set β : KE := algebraMap K KE W.a₁ * X + algebraMap K KE W.a₃ with hβ
  have hDβ : KaehlerDifferential.D K KE β = 0 := by
    rw [hβ]
    simp only [map_add, Derivation.leibniz, Derivation.map_algebraMap, hDX,
      smul_zero, add_zero]
  have hDγ : KaehlerDifferential.D K KE
      (X ^ 3 + algebraMap K KE W.a₂ * X ^ 2 + algebraMap K KE W.a₄ * X + algebraMap K KE W.a₆)
      = 0 := by
    simp only [map_add, Derivation.leibniz, Derivation.map_algebraMap,
      Derivation.leibniz_pow, hDX, smul_zero, add_zero]
  have hDquad : KaehlerDifferential.D K KE (Y ^ 2 + β * Y) =
      (2 * Y + β) • KaehlerDifferential.D K KE Y := by
    rw [map_add, Derivation.leibniz_pow, Derivation.leibniz, hDβ, smul_zero, add_zero,
      show (2 : ℕ) - 1 = 1 from rfl, pow_one, ← Nat.cast_smul_eq_nsmul KE,
      Nat.cast_ofNat, ← mul_smul, ← add_smul]
  have hcombine : (2 * Y + β) • KaehlerDifferential.D K KE Y = 0 := by
    rw [← hDquad, hroot, hDγ]
  exact (smul_eq_zero.mp hcombine).resolve_left hs_ne

/-- `D([p]* y_gen) = 0`: the Kähler differential of the `[p]`-pullback of `y_gen` vanishes. -/
theorem D_mulByInt_p_pullback_y_gen_eq_zero (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K KE ((mulByInt W.toAffine (p : ℤ)).pullback (y_gen W)) = 0 := by
  refine kaehlerD_eq_zero_of_weierstrass_quadratic W _ _
    (D_mulByInt_p_pullback_x_gen_eq_zero W p) ?_ ?_
  · linear_combination mulByInt_pullback_y_gen_weierstrass W (p : ℤ)
  · have hsu : alpha_star_u W (mulByInt W.toAffine (p : ℤ)) =
        2 * (mulByInt W.toAffine (p : ℤ)).pullback (y_gen W) +
          (algebraMap K KE W.a₁ * (mulByInt W.toAffine (p : ℤ)).pullback (x_gen W) +
            algebraMap K KE W.a₃) := by
      simp only [alpha_star_u, y_gen, x_gen]; ring
    rw [← hsu, alpha_star_u_eq]
    intro h
    exact u_gen_ne_zero W
      ((mulByInt W.toAffine (p : ℤ)).pullback_injective (by rw [h, map_zero]))

omit [Fintype K] [DecidableEq K] in
/-- **Two-generator `p`-th-power adjoin lemma**: in char `p`, `z ∈ adjoin K {a, b}`
implies `z^p ∈ adjoin K {a^p, b^p}`. -/
theorem adjoin_pair_pow_le_adjoin_pair_pow
    {L : Type*} [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (a b z : L) (hz : z ∈ IntermediateField.adjoin K ({a, b} : Set L)) :
    z ^ p ∈ IntermediateField.adjoin K ({a ^ p, b ^ p} : Set L) := by
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact IntermediateField.subset_adjoin K _ (by left; rfl)
    · exact IntermediateField.subset_adjoin K _ (by right; rfl)
  | algebraMap x => rw [← map_pow]; exact IntermediateField.algebraMap_mem _ _
  | add x w _ _ ihx ihw => rw [add_pow_expChar]; exact add_mem ihx ihw
  | inv x _ ihx => rw [inv_pow]; exact inv_mem ihx
  | mul x w _ _ ihx ihw => rw [mul_pow]; exact mul_mem ihx ihw

omit [Fintype K] [DecidableEq K] in
/-- **Iterated two-generator power adjoin lemma**:
`z ∈ adjoin K {a, b} → z^{p^n} ∈ adjoin K {a^{p^n}, b^{p^n}}`. -/
theorem adjoin_pair_pow_pow_le_adjoin_pair_pow_pow
    {L : Type*} [Field L] [Algebra K L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (a b : L) (n : ℕ) (z : L) (hz : z ∈ IntermediateField.adjoin K ({a, b} : Set L)) :
    z ^ (p ^ n) ∈ IntermediateField.adjoin K ({a ^ (p ^ n), b ^ (p ^ n)} : Set L) := by
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    simp only [pow_succ, pow_mul]
    exact adjoin_pair_pow_le_adjoin_pair_pow p (a ^ (p ^ n)) (b ^ (p ^ n)) (z ^ (p ^ n)) ih

/-- **y-side base (general characteristic)**: `[p]* y_gen ∈ adjoin K {x_gen^p, y_gen^p}`. -/
theorem mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (mulByInt W.toAffine (p : ℤ)).pullback (y_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ p, y_gen W ^ p} : Set KE) := by
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap K KE).injective p
  obtain ⟨h, hh⟩ := (kaehlerD_eq_zero_iff_mem_pth_powers W p _).mp
    (D_mulByInt_p_pullback_y_gen_eq_zero W p)
  have hh_mem : h ∈ IntermediateField.adjoin K ({x_gen W, y_gen W} : Set KE) := by
    rw [← functionField_eq_intermediateField_adjoin_xy W]; trivial
  rw [← hh]
  exact adjoin_pair_pow_le_adjoin_pair_pow p (x_gen W) (y_gen W) h hh_mem

/-- **y-side, all powers (general characteristic)**: for all `k`,
`[p^k]* y_gen ∈ adjoin K {x_gen^(p^k), y_gen^(p^k)}`. -/
theorem mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∀ k, (mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (y_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ (p ^ k : ℕ), y_gen W ^ (p ^ k : ℕ)} : Set KE) := by
  haveI : CharP KE p := charP_of_injective_algebraMap (algebraMap K KE).injective p
  intro k
  induction k with
  | zero =>
    change (mulByInt W.toAffine ((1 : ℕ) : ℤ)).pullback (y_gen W) ∈
      IntermediateField.adjoin K ({x_gen W ^ 1, y_gen W ^ 1} : Set KE)
    rw [pow_one, pow_one, show ((1 : ℕ) : ℤ) = 1 from rfl, mulByInt_one_pullback_eq_id]
    exact IntermediateField.subset_adjoin K _ (by right; rfl)
  | succ k ih =>
    rw [mulByInt_pow_succ_comp W p k]
    change (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback
        ((mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (y_gen W)) ∈ _
    have h_in_image :
        (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback
            ((mulByInt W.toAffine ((p ^ k : ℕ) : ℤ)).pullback (y_gen W)) ∈
          (IntermediateField.adjoin K
              ({x_gen W ^ (p ^ k : ℕ), y_gen W ^ (p ^ k : ℕ)} : Set _)).map
            (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback :=
      ⟨_, ih, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_pair, map_pow, map_pow] at h_in_image
    have hex : ((x_gen W ^ p) ^ (p ^ k) : KE) = x_gen W ^ (p ^ (k + 1) : ℕ) ∧
        ((y_gen W ^ p) ^ (p ^ k) : KE) = y_gen W ^ (p ^ (k + 1) : ℕ) :=
      ⟨by rw [← pow_mul, ← pow_succ'], by rw [← pow_mul, ← pow_succ']⟩
    refine IntermediateField.adjoin_le_iff.mpr ?_ h_in_image
    rintro f (rfl | rfl)
    · have hx_base : (mulByInt W.toAffine ((p : ℕ) : ℤ)).pullback (x_gen W) ∈
          IntermediateField.adjoin K ({x_gen W ^ p, y_gen W ^ p} : Set _) := by
        refine IntermediateField.adjoin.mono K _ _ ?_
          (by have := mulByInt_p_pullback_x_gen_mem_adjoin_pow_routeB W p
              rwa [show ((p : ℕ) : ℤ) = (p : ℤ) from rfl] at this)
        intro z hz; rw [Set.mem_singleton_iff] at hz; exact Or.inl hz
      have hpow := adjoin_pair_pow_pow_le_adjoin_pair_pow_pow p (x_gen W ^ p) (y_gen W ^ p) k
        _ hx_base
      rw [hex.1, hex.2] at hpow
      exact hpow
    · have hpow := adjoin_pair_pow_pow_le_adjoin_pair_pow_pow p (x_gen W ^ p) (y_gen W ^ p) k
        _ (mulByInt_p_pullback_y_gen_mem_adjoin_pair_pow W p)
      rw [hex.1, hex.2] at hpow
      exact hpow

/-- **y-side conclusion**: `[q]* y_gen ∈ Im(π*) = K(E)^q`. -/
theorem mulByInt_card_pullback_y_gen_mem_frobenius
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈
      frobeniusIsog_intermediateField W := by
  obtain ⟨⟨n, _⟩, _, hcard⟩ := FiniteField.card K p
  have hmem : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈
      IntermediateField.adjoin K
        ({x_gen W ^ (Fintype.card K : ℕ), y_gen W ^ (Fintype.card K : ℕ)} : Set KE) := by
    rw [hcard]; exact mulByInt_pow_pullback_y_gen_mem_adjoin_pair_pow W p n
  refine (IntermediateField.adjoin_le_iff.mpr ?_) hmem
  rintro f (rfl | rfl)
  · exact pow_card_mem_frobeniusIsog_intermediateField W (x_gen W)
  · exact pow_card_mem_frobeniusIsog_intermediateField W (y_gen W)

/-- **Universal q-th-root witness, char-`p` form**: every `[q]*` pullback is a `q`-th
power in `K(E)`. -/
theorem qth_root_witness_of_charP (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∀ z : KE, ∃ g : KE,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z := by
  have hx : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W) ∈
      (frobeniusIsog W).pullback.fieldRange := by
    rw [← frobeniusIsog_intermediateField_eq_fieldRange]
    exact mulByInt_card_pullback_x_gen_mem_frobenius W p
  have hy : (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (y_gen W) ∈
      (frobeniusIsog W).pullback.fieldRange := by
    rw [← frobeniusIsog_intermediateField_eq_fieldRange]
    exact mulByInt_card_pullback_y_gen_mem_frobenius W p
  intro z
  exact (mem_frobenius_range_iff W _).mp
    (mulByInt_q_pullback_fieldRange_subset_frobenius_of_xy_witness W
      (functionField_eq_intermediateField_adjoin_xy W) hx hy z)

/-- **Universal q-th-root witness (general)**: every `[q]*` pullback is a `q`-th power in
`K(E)`, for any finite field `K`. -/
theorem qth_root_witness_general :
    ∀ z : KE, ∃ g : KE,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z := by
  obtain ⟨p, hCharP, ⟨n, _⟩, hp_prime, _⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  haveI := hCharP
  exact qth_root_witness_of_charP W p

/-- **The GAP-QF keystone (general characteristic)**: the Verschiebung is the dual of
Frobenius for any elliptic curve over any finite field, uniformly in the characteristic. -/
theorem verschiebung_isDualOf_frobenius_general :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W
          (qth_root_witness_general W)))
      (frobeniusIsog W) :=
  verschiebungIsog_isDualOf_frobenius_of_qth_root_witness W (qth_root_witness_general W)

end HasseWeil
