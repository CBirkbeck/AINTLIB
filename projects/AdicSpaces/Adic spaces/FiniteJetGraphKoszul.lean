/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FiniteJetNoetherianVertices
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Strict graph–Koszul exactness in degrees ≤ 2 ([FJP] Lemma 4.2)

Source: [FJP] Lemma 4.2 (verbatim statement): "Let `D` be an affinoid k-algebra, possibly
nonreduced, and let `g, f₁, …, f_m ∈ D` generate the unit ideal. Put `P_D = D⟨T₁,…,T_m⟩`,
`r_i = gT_i − f_i`. For `m ≥ 1`, the Koszul complex `K_{P_D}(r₁,…,r_m)` is strictly exact in
positive degrees. Moreover, every differential has closed image and is strict onto that
image. In particular, `I_D = im(d₁) ⊂ P_D` is closed and `d₁ : P_D^m ↠ I_D` is strict."

Design (DD6, `plan.md`): mathlib has no Koszul complexes, and the downstream consumer
([FJP] Lemma 4.3) uses only exterior degrees ≤ 2 — (4.7) `d₁`-lifting with constant and
(4.8) `d₂`-lifting onto `ker d₁` with constant. We therefore state everything concretely:
`d₁ u = ∑ uᵢ rᵢ` on `m`-tuples and `d₂` on strictly-ordered pairs with the [FJP] p.10 sign
convention `d₂(e_i ∧ e_j) = r_i e_j − r_j e_i`.

Proof architecture (mirrors [FJP]'s proof exactly):
1. polynomial level over any commutative ring: coordinate-sequence syzygies are
   Koszul-generated (elementary induction); translation `T ↦ T + a` and unit scaling
   transport this to `(gT_i − f_i)` over `D[T]_g`; the two-case prime-local argument plus
   `Submodule.eq_top_of_localization_maximal` globalises ("the localization of every positive
   Koszul homology module at every prime … is zero; hence each such homology module is
   zero" — degrees ≤ 1 form);
2. `P_D ≅ (D₀[T])^∧_ϖ[1/ϖ]` for a noetherian ring of definition `D₀` ([FJP] (4.4)); the base
   change `D[T] → P_D` is **flat** (mathlib `AdicCompletion.flat_of_isNoetherian` = Stacks
   00MB + localisation), and only *positive-degree* exactness transfers ([FJP]: "Notice that
   `g, f_i` need not lie in `D₀`, because exactness was established before completion" —
   and `H₀` genuinely changes: `r` can become a unit in `D⟨T⟩`);
3. strictness/closedness over the noetherian `P_D` via the finite-module theory
   (`NoetherianTateModules.lean`, Wedhorn 6.18 = the Huber [4, Lemma 2.4(ii)] citation) and
   the Banach open mapping theorem with constants
   (`ContinuousLinearMap.exists_preimage_norm_le`).
-/

open Filter Topology

namespace FiniteJet

namespace GraphKoszul

/-! ### The concrete differentials -/

section Differentials

variable {S : Type*} [CommRing S] {m : ℕ}

/-- Index type for exterior degree 2: strictly ordered pairs. -/
abbrev Pairs (m : ℕ) := {p : Fin m × Fin m // p.1 < p.2}

/-- `d₁ u = ∑ᵢ uᵢ rᵢ` — the first graph–Koszul differential. -/
def d1 (r : Fin m → S) (u : Fin m → S) : S := ∑ i, u i * r i

/-- `d₂` on ordered pairs, with the [FJP] p.10 sign convention
`d₂(e_i ∧ e_j) = r_i e_j − r_j e_i` for `i < j`:
`(d₂ v)_j = ∑_{i<j} v_{ij} r_i − ∑_{k>j} v_{jk} r_k`. -/
def d2 (r : Fin m → S) (v : Pairs m → S) : Fin m → S := fun j =>
  (∑ i, if h : i < j then v ⟨(i, j), h⟩ * r i else 0) -
    ∑ k, if h : j < k then v ⟨(j, k), h⟩ * r k else 0

/-- `d₁ ∘ d₂ = 0` (the Koszul relations are syzygies). -/
theorem d1_d2 (r : Fin m → S) (v : Pairs m → S) : d1 r (d2 r v) = 0 := by
  unfold d1 d2
  simp only [sub_mul, Finset.sum_mul]
  rw [Finset.sum_sub_distrib, sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a < b
  · rw [dif_pos hab, dif_pos hab, mul_right_comm]
  · rw [dif_neg hab, dif_neg hab, zero_mul, zero_mul]

theorem d1_map {T : Type*} [CommRing T] (φ : S →+* T) (r : Fin m → S) (u : Fin m → S) :
    φ (d1 r u) = d1 (fun i => φ (r i)) (fun i => φ (u i)) := by
  unfold d1
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul φ _ _

theorem d2_map {T : Type*} [CommRing T] (φ : S →+* T) (r : Fin m → S) (v : Pairs m → S)
    (j : Fin m) :
    φ (d2 r v j) = d2 (fun i => φ (r i)) (fun p => φ (v p)) j := by
  unfold d2
  rw [map_sub, map_sum, map_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, map_mul]
    · rw [dif_neg hij, dif_neg hij, map_zero]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, map_mul]
    · rw [dif_neg hij, dif_neg hij, map_zero]

theorem d2_smul (r : Fin m → S) (c : S) (v : Pairs m → S) (j : Fin m) :
    d2 r (fun p => c * v p) j = c * d2 r v j := by
  unfold d2
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, mul_assoc]
    · rw [dif_neg hij, dif_neg hij, mul_zero]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, mul_assoc]
    · rw [dif_neg hij, dif_neg hij, mul_zero]

/-- Scaling the sequence by a unit rescales the wedge inversely. -/
theorem d2_unit_scale {c : S} (hc : IsUnit c) (ρ : Fin m → S) (v : Pairs m → S) (j : Fin m) :
    d2 (fun i => c * ρ i) (fun p => (hc.unit⁻¹ : Sˣ) * v p) j = d2 ρ v j := by
  unfold d2
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
  · by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, mul_mul_mul_comm, mul_comm ((hc.unit⁻¹ : Sˣ) : S) c,
        IsUnit.mul_val_inv, one_mul]
    · rw [dif_neg hij, dif_neg hij]
  · by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, mul_mul_mul_comm, mul_comm ((hc.unit⁻¹ : Sˣ) : S) c,
        IsUnit.mul_val_inv, one_mul]
    · rw [dif_neg hij, dif_neg hij]

theorem d2_zero (r : Fin m → S) (j : Fin m) : d2 r (fun _ => (0 : S)) j = 0 := by
  unfold d2
  dsimp only
  have h1 : (∑ i, if h : i < j then (0 : S) * r i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hij : i < j
      · rw [dif_pos hij, zero_mul]
      · rw [dif_neg hij]
  have h2 : (∑ i, if h : j < i then (0 : S) * r i else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      by_cases hij : j < i
      · rw [dif_pos hij, zero_mul]
      · rw [dif_neg hij]
  rw [h1, h2, sub_zero]

theorem d2_add (r : Fin m → S) (v w : Pairs m → S) (j : Fin m) :
    d2 r (fun p => v p + w p) j = d2 r v j + d2 r w j := by
  unfold d2
  dsimp only
  rw [sub_add_sub_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : i < j
    · rw [dif_pos hij, dif_pos hij, dif_pos hij, add_mul]
    · rw [dif_neg hij, dif_neg hij, dif_neg hij, add_zero]
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hij : j < i
    · rw [dif_pos hij, dif_pos hij, dif_pos hij, add_mul]
    · rw [dif_neg hij, dif_neg hij, dif_neg hij, add_zero]

/-- The contractibility case: multiplying a syzygy by any one `rᵢ` lands it in the Koszul
image, explicitly ([FJP] Lemma 4.2: "At a prime not containing every `rᵢ`, one generator is
a unit and the localized Koszul complex is contractible"). -/
theorem d2_koszul_single (r : Fin m → S) (u : Fin m → S) (h : d1 r u = 0) (i : Fin m) :
    d2 r (fun p => if p.1.2 = i then -u p.1.1 else if p.1.1 = i then u p.1.2 else 0) =
      fun k => r i * u k := by
  classical
  funext k
  unfold d2
  dsimp only
  rcases lt_trichotomy k i with hki | heq | hik
  · -- `k < i`: only the `(k,i)` wedge contributes, through the second sum
    have hs1 : (∑ a, if h : a < k then
        (if k = i then -u a else if a = i then u k else 0) * r a else 0) = 0 :=
      Finset.sum_eq_zero fun a _ => by
        by_cases hak : a < k
        · rw [dif_pos hak, if_neg (Fin.ne_of_lt hki), if_neg (Fin.ne_of_lt (hak.trans hki)),
            zero_mul]
        · rw [dif_neg hak]
    have hs2 : (∑ b, if h : k < b then
        (if b = i then -u k else if k = i then u b else 0) * r b else 0) = -u k * r i := by
      rw [Finset.sum_eq_single i (fun b _ hb => ?_) (fun hb => absurd (Finset.mem_univ i) hb)]
      · rw [dif_pos hki, if_pos rfl]
      · by_cases hkb : k < b
        · rw [dif_pos hkb, if_neg hb, if_neg (Fin.ne_of_lt hki), zero_mul]
        · rw [dif_neg hkb]
    rw [hs1, hs2, zero_sub, neg_mul, neg_neg, mul_comm]
  · -- `k = i`: the row collects `-∑_{j≠i} uⱼ rⱼ = uᵢ rᵢ`
    rw [heq]
    have hsum := h
    unfold d1 at hsum
    have hsplit : ∀ j : Fin m, u j * r j =
        (if j < i then u j * r j else 0) + ((if j = i then u j * r j else 0) +
          (if i < j then u j * r j else 0)) := fun j => by
      rcases lt_trichotomy j i with h1 | rfl | h1
      · rw [if_pos h1, if_neg (Fin.ne_of_lt h1), if_neg (asymm h1), add_zero, add_zero]
      · simp
      · rw [if_neg (asymm h1), if_neg (Fin.ne_of_gt h1), if_pos h1, zero_add, zero_add]
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i (fun j => u j * r j),
      if_pos (Finset.mem_univ i)] at hsum
    have h1 : (∑ a, if h : a < i then
        (if i = i then -u a else if a = i then u i else 0) * r a else 0) =
        -∑ j, if j < i then u j * r j else 0 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hai : a < i
      · rw [dif_pos hai, if_pos rfl, if_pos hai, neg_mul]
      · rw [dif_neg hai, if_neg hai, neg_zero]
    have h2 : (∑ b, if h : i < b then
        (if b = i then -u i else if i = i then u b else 0) * r b else 0) =
        ∑ j, if i < j then u j * r j else 0 := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hib : i < b
      · rw [dif_pos hib, if_neg (Fin.ne_of_gt hib), if_pos rfl, if_pos hib]
      · rw [dif_neg hib, if_neg hib]
    rw [h1, h2, mul_comm (r i) (u i)]
    linear_combination -hsum
  · -- `i < k`: only the `(i,k)` wedge contributes, through the first sum
    have hs1 : (∑ a, if h : a < k then
        (if k = i then -u a else if a = i then u k else 0) * r a else 0) = u k * r i := by
      rw [Finset.sum_eq_single i (fun a _ ha => ?_) (fun ha => absurd (Finset.mem_univ i) ha)]
      · rw [dif_pos hik, if_neg (Fin.ne_of_gt hik), if_pos rfl]
      · by_cases hak : a < k
        · rw [dif_pos hak, if_neg (Fin.ne_of_gt hik), if_neg ha, zero_mul]
        · rw [dif_neg hak]
    have hs2 : (∑ b, if h : k < b then
        (if b = i then -u k else if k = i then u b else 0) * r b else 0) = 0 :=
      Finset.sum_eq_zero fun b _ => by
        by_cases hkb : k < b
        · rw [dif_pos hkb, if_neg (Fin.ne_of_gt (hik.trans hkb)), if_neg (Fin.ne_of_gt hik),
            zero_mul]
        · rw [dif_neg hkb]
    rw [hs1, hs2, sub_zero, mul_comm]

end Differentials

/-! ### Polynomial level: syzygies of the graph sequence are Koszul-generated

[FJP] Lemma 4.2, proof (verbatim): "First work over `D[T₁,…,T_m]`. At a prime not containing
every `r_i`, one generator is a unit and the localized Koszul complex is contractible. At a
prime containing all `r_i`, choose `1 = a₀g + ∑ a_i f_i`. … Thus `g` is a unit in that local
ring … Over `D_g`, translation by the tuple `(f_i/g)_i` identifies `(T_i − f_i/g)_i` with the
coordinate sequence `(T_i)_i`. The coordinate sequence is regular over an arbitrary
coefficient ring … The polynomial Koszul complex is therefore exact in positive degrees, even
when `D` is nonreduced. Indeed, the localization of every positive Koszul homology module at
every prime of `D[T₁,…,T_m]` is zero by the two cases above; hence each such homology module
is zero." -/

section Polynomial

variable {D : Type*} [CommRing D] {m : ℕ}

open MvPolynomial in
/-- Coordinate-sequence syzygies over an arbitrary base are Koszul-generated (the elementary
multidegree induction; [FJP]: "The coordinate sequence is regular over an arbitrary
coefficient ring"). -/
theorem syzygy_coordinate (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => (X i : MvPolynomial (Fin m) D)) u = 0) :
    ∃ v, d2 (fun i => (X i : MvPolynomial (Fin m) D)) v = u := by
  classical
  induction m with
  | zero => exact ⟨fun p => 0, funext fun i => i.elim0⟩
  | succ m ih =>
    set e := MvPolynomial.finSuccEquiv D m with he
    set U : Fin (m + 1) → Polynomial (MvPolynomial (Fin m) D) := fun i => e (u i) with hUdef
    -- the relation in `A[y]`, `y := X 0`
    have hrel : U 0 * Polynomial.X +
        ∑ i : Fin m, U i.succ * Polynomial.C (X i) = 0 := by
      have h0 := congrArg e h
      rw [map_zero] at h0
      rw [← h0]
      unfold d1
      rw [map_sum, Fin.sum_univ_succ]
      congr 1
      · rw [map_mul, MvPolynomial.finSuccEquiv_X_zero]
      · exact Finset.sum_congr rfl fun i _ => by
          rw [map_mul, MvPolynomial.finSuccEquiv_X_succ]
    -- reduction mod `y`: the constant coefficients form a coordinate syzygy over `Fin m`
    set a : Fin m → MvPolynomial (Fin m) D := fun i => (U i.succ).coeff 0 with hadef
    have hared : d1 (fun i => (X i : MvPolynomial (Fin m) D)) a = 0 := by
      have hc := congrArg (fun p : Polynomial (MvPolynomial (Fin m) D) => p.coeff 0) hrel
      simp only [Polynomial.coeff_add, Polynomial.coeff_zero, Polynomial.mul_coeff_zero,
        Polynomial.coeff_X_zero, mul_zero, zero_add, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_zero] at hc
      unfold d1
      exact hc
    obtain ⟨w, hw⟩ := ih a hared
    -- the `divX` decomposition of the positive part
    set Q : Fin m → Polynomial (MvPolynomial (Fin m) D) := fun i => (U i.succ).divX with hQdef
    have hdecomp : ∀ i : Fin m, U i.succ = Polynomial.X * Q i + Polynomial.C (a i) :=
      fun i => (Polynomial.X_mul_divX_add (U i.succ)).symm
    -- cancel `y`: the top coefficient is Koszul-expressed
    have hU0 : U 0 = -∑ i : Fin m, Q i * Polynomial.C (X i) := by
      have hXmul : Polynomial.X *
          (U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i)) = 0 := by
        have hsplit : ∑ i : Fin m, U i.succ * Polynomial.C (X i) =
            Polynomial.X * ∑ i : Fin m, Q i * Polynomial.C (X i) +
              Polynomial.C (d1 (fun i => (X i : MvPolynomial (Fin m) D)) a) := by
          unfold d1
          rw [Finset.mul_sum, map_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdecomp i, add_mul, map_mul, mul_assoc]
        rw [mul_add, mul_comm Polynomial.X (U 0)]
        have h2 := hrel
        rw [hsplit, hared, map_zero, add_zero] at h2
        exact h2
      have hcancel : U 0 + ∑ i : Fin m, Q i * Polynomial.C (X i) = 0 := by
        refine Polynomial.ext fun n => ?_
        have hcn := congrArg (fun q : Polynomial (MvPolynomial (Fin m) D) =>
          q.coeff (n + 1)) hXmul
        simpa [Polynomial.coeff_X_mul] using hcn
      exact eq_neg_of_add_eq_zero_left hcancel
    -- assemble the wedge
    have hp2ne : ∀ p : Pairs (m + 1), p.1.2 ≠ 0 := fun p =>
      Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (Fin.zero_le _) p.2)
    refine ⟨fun p =>
      if h0 : p.1.1 = 0 then e.symm (Q (p.1.2.pred (hp2ne p)))
      else e.symm (Polynomial.C (w ⟨(p.1.1.pred h0, p.1.2.pred (hp2ne p)),
        (Fin.pred_lt_pred_iff (ha := h0) (hb := hp2ne p)).mpr p.2⟩)), ?_⟩
    funext j
    refine Fin.cases ?_ ?_ j
    · -- component 0: `-∑ₖ v₀ₖ Xₖ = u 0` is exactly the `y`-cofactor identity `hU0`
      unfold d2
      simp only [Fin.not_lt_zero, Fin.sum_univ_succ, lt_irrefl, Fin.succ_pos, dif_pos,
        Fin.pred_succ]
      simp only [dif_neg not_false, Finset.sum_const_zero, zero_add, zero_sub]
      have hU0' : e (u 0) = -∑ i : Fin m, Q i * Polynomial.C (X i) := hU0
      apply e.injective
      rw [map_neg, map_sum, hU0', neg_inj]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_mul, AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_succ]
    · -- component `j.succ`: the `divX` decomposition plus the IH wedge
      intro j
      unfold d2
      simp only [Fin.sum_univ_succ, Fin.succ_pos, dif_pos, Fin.not_lt_zero,
        Fin.succ_lt_succ_iff, Fin.succ_ne_zero, Fin.pred_succ]
      apply e.injective
      have hUj : e (u j.succ) = Polynomial.X * Q j +
          Polynomial.C (d2 (fun i => (X i : MvPolynomial (Fin m) D)) w j) := by
        rw [hw]
        exact hdecomp j
      rw [hUj]
      unfold d2
      have heX0 : e (X 0) = Polynomial.X := MvPolynomial.finSuccEquiv_X_zero
      have heXs : ∀ i : Fin m, e (X i.succ) = Polynomial.C (X i) := fun i =>
        MvPolynomial.finSuccEquiv_X_succ
      simp only [dif_neg not_false, zero_add, map_sub, map_add, map_sum, map_mul,
        AlgEquiv.apply_symm_apply, apply_dite e, apply_dite Polynomial.C, map_zero, heX0,
        heXs]
      ring

open MvPolynomial in
/-- Denominator clearing for the polynomial base change into `D_g`: every polynomial over
the localization is a `(C g)`-power multiple of a polynomial over `D` ([FJP] Lemma 4.2's
implicit "clear denominators" step). -/
theorem exists_pow_C_mul_eq_map (g : D) (y : MvPolynomial (Fin m) (Localization.Away g)) :
    ∃ (N : ℕ) (x : MvPolynomial (Fin m) D),
      MvPolynomial.map (algebraMap D (Localization.Away g)) x =
        C (algebraMap D (Localization.Away g) g) ^ N * y := by
  induction y using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj (Submonoid.powers g) a
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    refine ⟨n, C d, ?_⟩
    rw [MvPolynomial.map_C, ← map_pow, ← map_mul]
    congr 1
    rw [← hds, show ((s : Submonoid.powers g) : D) = g ^ n from hn.symm, map_pow]
    ring
  | add p q hp hq =>
    obtain ⟨Np, xp, hxp⟩ := hp
    obtain ⟨Nq, xq, hxq⟩ := hq
    refine ⟨Np + Nq, C g ^ Nq * xp + C g ^ Np * xq, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, MvPolynomial.map_C, hxp, hxq]
    ring
  | mul_X p i hp =>
    obtain ⟨N, x, hx⟩ := hp
    refine ⟨N, x * X i, ?_⟩
    rw [map_mul, MvPolynomial.map_X, hx]
    ring

open MvPolynomial in
/-- `g`-power torsion detects the kernel of the polynomial base change into `D_g`. -/
theorem exists_pow_C_mul_eq_zero_of_map_eq_zero (g : D) (z : MvPolynomial (Fin m) D)
    (hz : MvPolynomial.map (algebraMap D (Localization.Away g)) z = 0) :
    ∃ M : ℕ, C g ^ M * z = 0 := by
  classical
  have hcoeff : ∀ t : Fin m →₀ ℕ, ∃ n : ℕ, g ^ n * MvPolynomial.coeff t z = 0 := fun t => by
    have h0 : algebraMap D (Localization.Away g) (MvPolynomial.coeff t z) = 0 := by
      rw [← MvPolynomial.coeff_map, hz, MvPolynomial.coeff_zero]
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp h0
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    exact ⟨n, by rw [hn]; exact hs⟩
  choose nf hnf using hcoeff
  refine ⟨z.support.sup nf, ?_⟩
  ext t
  rw [← map_pow, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero]
  by_cases ht : t ∈ z.support
  · have hle : nf t ≤ z.support.sup nf := Finset.le_sup ht
    rw [show z.support.sup nf = (z.support.sup nf - nf t) + nf t by omega, pow_add,
      mul_assoc, hnf t, mul_zero]
  · rw [MvPolynomial.notMem_support_iff.mp ht, mul_zero]

open MvPolynomial in
/-- The translation `Xᵢ ↦ Xᵢ + C (c i)` as an algebra automorphism. -/
noncomputable def translationEquiv (c : Fin m → D) :
    MvPolynomial (Fin m) D ≃ₐ[D] MvPolynomial (Fin m) D :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (c i)) (aeval fun i => X i - C (c i))
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, aeval_X, map_sub, aeval_X, aeval_C, AlgHom.id_apply,
        algebraMap_eq]
      ring)
    (by
      refine MvPolynomial.algHom_ext fun i => ?_
      rw [AlgHom.comp_apply, aeval_X, map_add, aeval_X, aeval_C, AlgHom.id_apply,
        algebraMap_eq]
      ring)

open MvPolynomial in
theorem translationEquiv_X (c : Fin m → D) (i : Fin m) :
    translationEquiv c (X i) = X i + C (c i) :=
  aeval_X _ i

open MvPolynomial in
theorem translationEquiv_C (c : Fin m → D) (d : D) :
    translationEquiv c (C d) = C d := by
  rw [show translationEquiv c (C d) = aeval (fun i => X i + C (c i)) (C d) from rfl,
    aeval_C, algebraMap_eq]

open MvPolynomial in
/-- The unit-`g` case of [FJP] Lemma 4.2's polynomial layer: translation by `(g⁻¹fᵢ)ᵢ`
identifies the graph sequence with the coordinate sequence, up to the unit `C g`. -/
theorem syzygy_graph_of_isUnit (g : D) (hg : IsUnit g) (f : Fin m → D)
    (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => C g * X i - C (f i)) u = 0) :
    ∃ v, d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) v = u := by
  classical
  set c : Fin m → D := fun i => (hg.unit⁻¹ : Dˣ) * f i with hc
  set ρ : Fin m → MvPolynomial (Fin m) D := fun i => X i - C (c i) with hρ
  have hr : ∀ i, (C g * X i - C (f i) : MvPolynomial (Fin m) D) = C g * ρ i := fun i => by
    rw [hρ]
    show _ = C g * (X i - C (c i))
    rw [mul_sub, ← map_mul, hc]
    show _ = C g * X i - C (g * ((hg.unit⁻¹ : Dˣ) * f i))
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hCg : IsUnit (C g : MvPolynomial (Fin m) D) := hg.map C
  have hρsyz : d1 ρ u = 0 := by
    have hfac : d1 (fun i => C g * ρ i) u = C g * d1 ρ u := by
      unfold d1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [show (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) = fun i => C g * ρ i
      from funext hr, hfac] at h
    exact hCg.mul_right_eq_zero.mp h
  set α := translationEquiv c with hα
  have hαρ : ∀ i, α (ρ i) = X i := fun i => by
    rw [hρ]
    show α (X i - C (c i)) = X i
    rw [map_sub, hα, translationEquiv_X, translationEquiv_C]
    ring
  have hcoord : d1 (fun i => (X i : MvPolynomial (Fin m) D)) (fun i => α (u i)) = 0 := by
    have h0 := congrArg α hρsyz
    rw [map_zero] at h0
    rw [← h0]
    unfold d1
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hαρ]
  obtain ⟨w, hw⟩ := syzygy_coordinate (fun i => α (u i)) hcoord
  refine ⟨fun p => (hCg.unit⁻¹ : (MvPolynomial (Fin m) D)ˣ) * α.symm (w p), ?_⟩
  funext k
  apply α.injective
  have hpush : α (d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))
      (fun p => (hCg.unit⁻¹ : (MvPolynomial (Fin m) D)ˣ) * α.symm (w p)) k) =
      d2 (fun i => (X i : MvPolynomial (Fin m) D)) w k := by
    unfold d2
    rw [map_sub, map_sum, map_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_
    · by_cases hik : i < k
      · rw [dif_pos hik, dif_pos hik]
        dsimp only
        rw [hr i, map_mul, map_mul, map_mul, AlgEquiv.apply_symm_apply, hαρ,
          mul_mul_mul_comm, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
      · rw [dif_neg hik, dif_neg hik, map_zero]
    · by_cases hik : k < i
      · rw [dif_pos hik, dif_pos hik]
        dsimp only
        rw [hr i, map_mul, map_mul, map_mul, AlgEquiv.apply_symm_apply, hαρ,
          mul_mul_mul_comm, ← map_mul, IsUnit.val_inv_mul, map_one, one_mul]
      · rw [dif_neg hik, dif_neg hik, map_zero]
  rw [hpush]
  exact congrFun hw k

open MvPolynomial in
/-- Graph-sequence syzygies over the polynomial ring are Koszul-generated, given that
`(g, f₁, …, f_m)` generate the unit ideal (the two-case localization argument). For `m = 1`
this says `gT − f` is a nonzerodivisor (the pairs type is empty). -/
theorem syzygy_graph_polynomial (g : D) (f : Fin m → D)
    (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (u : Fin m → MvPolynomial (Fin m) D)
    (h : d1 (fun i => C g * X i - C (f i)) u = 0) :
    ∃ v, d2 (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D)) v = u := by
  classical
  set Dg := Localization.Away g with hDg
  set φ : MvPolynomial (Fin m) D →+* MvPolynomial (Fin m) Dg :=
    MvPolynomial.map (algebraMap D Dg) with hφdef
  -- the ideal of Koszul-reachable multipliers of `u`
  set A : Ideal (MvPolynomial (Fin m) D) :=
    { carrier := {a | ∃ v, d2 (fun i => C g * X i - C (f i)) v = fun k => a * u k}
      zero_mem' := ⟨fun _ => 0, funext fun k => by rw [d2_zero, zero_mul]⟩
      add_mem' := by
        rintro a b ⟨va, hva⟩ ⟨vb, hvb⟩
        refine ⟨fun p => va p + vb p, funext fun k => ?_⟩
        rw [d2_add, congrFun hva k, congrFun hvb k, add_mul]
      smul_mem' := by
        rintro b a ⟨va, hva⟩
        refine ⟨fun p => b * va p, funext fun k => ?_⟩
        rw [d2_smul, congrFun hva k, smul_eq_mul, mul_assoc] } with hAdef
  -- each `rᵢ` is reachable (contractibility)
  have hrA : ∀ i, (C g * X i - C (f i) : MvPolynomial (Fin m) D) ∈ A := fun i =>
    ⟨_, d2_koszul_single _ u h i⟩
  -- some power of `C g` is reachable (through `D_g`, translation, and clearing)
  have hgA : ∃ P : ℕ, (C g : MvPolynomial (Fin m) D) ^ P ∈ A := by
    have hg' : IsUnit (algebraMap D Dg g) :=
      IsLocalization.map_units Dg ⟨g, Submonoid.mem_powers g⟩
    have hφr : ∀ i, φ (C g * X i - C (f i)) =
        C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)) := fun i => by
      rw [hφdef]
      show MvPolynomial.map _ _ = _
      rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]
    have hsyz' : d1 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
        (fun i => φ (u i)) = 0 := by
      calc d1 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
            (fun i => φ (u i))
          = d1 (fun i => φ (C g * X i - C (f i))) (fun i => φ (u i)) := by
            congr 1
            exact funext fun i => (hφr i).symm
        _ = φ (d1 (fun i => C g * X i - C (f i)) u) := (d1_map φ _ u).symm
        _ = 0 := by rw [h, map_zero]
    obtain ⟨v', hv'⟩ := syzygy_graph_of_isUnit (algebraMap D Dg g) hg'
      (fun i => algebraMap D Dg (f i)) (fun i => φ (u i)) hsyz'
    -- uniform denominator over the finite wedge index
    choose Nf xf hxf using fun p : Pairs m => exists_pow_C_mul_eq_map g (v' p)
    set Nmax := Finset.univ.sup Nf with hNmax
    set x' : Pairs m → MvPolynomial (Fin m) D :=
      fun p => C g ^ (Nmax - Nf p) * xf p with hx'def
    have hφx' : ∀ p, φ (x' p) = C (algebraMap D Dg g) ^ Nmax * v' p := fun p => by
      have hle : Nf p ≤ Nmax := Finset.le_sup (Finset.mem_univ p)
      rw [hx'def]
      show φ (C g ^ (Nmax - Nf p) * xf p) = _
      rw [map_mul, map_pow, hφdef]
      show MvPolynomial.map _ (C g) ^ _ * MvPolynomial.map _ (xf p) = _
      rw [MvPolynomial.map_C, hxf p, ← mul_assoc, ← pow_add,
        show Nmax - Nf p + Nf p = Nmax by omega]
    -- the pushed identity vanishes, so its preimage is `g`-power torsion
    have hker : ∀ k, φ (d2 (fun i => C g * X i - C (f i)) x' k - C g ^ Nmax * u k) = 0 :=
      fun k => by
        rw [map_sub, d2_map φ]
        have hcongr : d2 (fun i => φ (C g * X i - C (f i))) (fun p => φ (x' p)) k =
            d2 (fun i => C (algebraMap D Dg g) * X i - C (algebraMap D Dg (f i)))
              (fun p => C (algebraMap D Dg g) ^ Nmax * v' p) k := by
          congr 1
          · exact funext hφr
          · exact funext hφx'
        rw [hcongr, d2_smul, congrFun hv' k, map_mul, map_pow, hφdef]
        show C (algebraMap D Dg g) ^ Nmax * MvPolynomial.map _ (u k) -
          MvPolynomial.map _ (C g) ^ Nmax * MvPolynomial.map _ (u k) = 0
        rw [MvPolynomial.map_C, sub_self]
    choose Mf hMf using fun k =>
      exists_pow_C_mul_eq_zero_of_map_eq_zero g _ (hker k)
    set Mmax := Finset.univ.sup Mf with hMmax
    refine ⟨Mmax + Nmax, fun p => C g ^ Mmax * x' p, funext fun k => ?_⟩
    rw [d2_smul]
    have hle : Mf k ≤ Mmax := Finset.le_sup (Finset.mem_univ k)
    have h0 : C g ^ Mmax * (d2 (fun i => C g * X i - C (f i)) x' k - C g ^ Nmax * u k) = 0 := by
      rw [show Mmax = Mmax - Mf k + Mf k by omega, pow_add, mul_assoc, hMf k, mul_zero]
    rw [mul_sub] at h0
    rw [sub_eq_zero.mp h0, ← mul_assoc, ← pow_add]
  obtain ⟨P, hPA⟩ := hgA
  -- the span of `(C g)^P` and the `rᵢ` is contained in the reachable ideal …
  have hJle : Ideal.span ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
      Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) ≤ A := by
    rw [Ideal.span_le]
    rintro x (hx | ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hPA
    · exact hrA i
  -- … and contains `1` ([FJP] (4.3) plus the quotient-nilpotence argument)
  have h1mem : (1 : D) ∈ Ideal.span ({g} ∪ Set.range f) := by
    rw [hunit]
    exact Submodule.mem_top
  rw [Set.singleton_union, ← Fin.range_cons g f] at h1mem
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1mem
  rw [Fin.sum_univ_succ] at hcc
  simp only [Fin.cons_zero, Fin.cons_succ] at hcc
  have hkey : (C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k) -
      ∑ k, C (cc k.succ) * (C g * X k - C (f k)) = 1 := by
    have h1 : (C (cc 0 * g + ∑ k, cc k.succ * f k) : MvPolynomial (Fin m) D) = 1 := by
      rw [hcc, map_one]
    rw [map_add, map_mul, map_sum] at h1
    simp only [map_mul] at h1
    rw [← h1, mul_add, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib,
      mul_comm (C g) (C (cc 0))]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have h1J : (1 : MvPolynomial (Fin m) D) ∈ Ideal.span
      ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
        Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) := by
    set J := Ideal.span ({(C g : MvPolynomial (Fin m) D) ^ P} ∪
      Set.range (fun i => (C g * X i - C (f i) : MvPolynomial (Fin m) D))) with hJdef
    have hmkr : ∀ k, Ideal.Quotient.mk J (C g * X k - C (f k)) = 0 := fun k =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_union_right _ ⟨k, rfl⟩))
    have hmk1 : Ideal.Quotient.mk J
        ((C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k)) = 1 := by
      have hsum0 : (∑ k, Ideal.Quotient.mk J (C (cc k.succ) * (C g * X k - C (f k)))) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [map_mul, hmkr k, mul_zero]
      have hq := congrArg (Ideal.Quotient.mk J) hkey
      rw [map_one, map_sub, map_sum, hsum0, sub_zero] at hq
      exact hq
    have hq0 : (1 : MvPolynomial (Fin m) D ⧸ J) = 0 := by
      calc (1 : MvPolynomial (Fin m) D ⧸ J)
          = (Ideal.Quotient.mk J ((C g) * (C (cc 0) + ∑ k, C (cc k.succ) * X k))) ^ P := by
            rw [hmk1, one_pow]
        _ = Ideal.Quotient.mk J ((C g) ^ P) *
            Ideal.Quotient.mk J ((C (cc 0) + ∑ k, C (cc k.succ) * X k) ^ P) := by
            rw [← map_pow, ← map_mul, mul_pow]
        _ = 0 := by
            have hmem : ((C g : MvPolynomial (Fin m) D) ^ P) ∈ J :=
              Ideal.subset_span (Set.mem_union_left _ rfl)
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, zero_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_one]; exact hq0)
  obtain ⟨v, hv⟩ := hJle h1J
  exact ⟨v, by rw [hv]; exact funext fun k => one_mul (u k)⟩

end Polynomial

/-! ### Coefficientwise maps of restricted rings (used here and in the localization layer) -/

section MapHom

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {n : ℕ}

/-- Coefficientwise application of a norm-nonincreasing ring homomorphism to restricted
multivariate power series ([FJP] Lemma 4.1's ambient maps). -/
noncomputable def mapRestricted (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (c : Fin n → ℝ) :
    MvPowerSeries.Restricted R c →+* MvPowerSeries.Restricted S c where
  toFun f := ⟨MvPowerSeries.map φ f.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    rw [← MvPowerSeries.isRestrictedGauss_abs_iff]
    have hf : MvPowerSeries.IsRestrictedGauss c f.1 := f.2
    rw [← MvPowerSeries.isRestrictedGauss_abs_iff, MvPowerSeries.IsRestrictedGauss] at hf
    rw [MvPowerSeries.IsRestrictedGauss]
    refine squeeze_zero (fun t => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)) (fun t => ?_) hf
    rw [MvPowerSeries.coeff_map]
    exact mul_le_mul_of_nonneg_right (hφ _)
      (Finset.prod_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.map φ))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.map φ) f.1 g.1)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.map φ))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.map φ) f.1 g.1)

theorem norm_mapRestricted_le (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (c : Fin n → ℝ)
    [StrongPos c] (f : MvPowerSeries.Restricted R c) :
    ‖mapRestricted φ hφ c f‖ ≤ ‖f‖ := by
  rw [MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine Real.iSup_le (fun t => ?_) (norm_nonneg f)
  show ‖MvPowerSeries.coeff t (MvPowerSeries.map φ f.1)‖ * _ ≤ _
  rw [MvPowerSeries.coeff_map]
  calc ‖φ (MvPowerSeries.coeff t f.1)‖ * t.prod (c · ^ ·)
      ≤ ‖MvPowerSeries.coeff t f.1‖ * t.prod (c · ^ ·) :=
        mul_le_mul_of_nonneg_right (hφ _)
          (Finset.prod_nonneg fun i _ => pow_nonneg (StrongPos_pos c i).le _)
    _ ≤ ‖f‖ := by
        rw [MvRestricted.norm_eq]
        exact MvPowerSeries.le_gaussNorm _ _ _ (MvRestricted.hasGaussNorm _ f) t

end MapHom

/-! ### Restricted level over an affinoid vertex

Statements are parametrised over a normed vertex `E` with a noetherian unit ball and a
noetherian restricted extension; instantiated at `E ∈ {𝓑, 𝓒, 𝓓}` via
`FiniteJetNoetherianVertices.lean`. `P := E⟨T₁,…,T_m⟩` is the vendored radius-one restricted
ring. -/

/-- `P_E = E⟨T₁,…,T_m⟩`. -/
abbrev P (E : Type*) [NormedCommRing E] [IsUltrametricDist E] (m : ℕ) : Type _ :=
  MvPowerSeries.Restricted E (fun _ : Fin m => (1 : ℝ))

section Restricted

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}

/-- The scalar embedding `MvPolynomial → P_E` ([FJP] (4.4)'s dense polynomial subring). -/
noncomputable def polyToP : MvPolynomial (Fin m) E →+* P E m where
  toFun q := ⟨q.toMvPowerSeries, MvPolynomial.IsRestrictedGauss _ q⟩
  map_one' := Subtype.ext (map_one (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)))
  map_mul' q r := Subtype.ext (map_mul (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)) q r)
  map_zero' := Subtype.ext (map_zero (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)))
  map_add' q r := Subtype.ext (map_add (MvPolynomial.coeToMvPowerSeries.ringHom
    (σ := Fin m) (R := E)) q r)

/-- The base change `E[T] → E⟨T⟩` is **flat** ([FJP] Lemma 4.2, proof: "Noetherian adic
completion is flat [8, Lemma 10.97.2, Tag 00MB], and localization preserves flatness";
via the (4.4) identification `P_E ≅ (E₀[T])^∧_ϖ[1/ϖ]` for the noetherian unit ball `E₀`). -/
theorem flat_polyToP (hE₀ : IsNoetherianRing (unitBall E)) :
    letI : Algebra (MvPolynomial (Fin m) E) (P E m) := (polyToP (E := E) (m := m)).toAlgebra
    Module.Flat (MvPolynomial (Fin m) E) (P E m) := by sorry

/-- Graph-sequence syzygies over `P_E = E⟨T⟩` are Koszul-generated **algebraically**
([FJP] Lemma 4.2: positive-degree exactness transfers along the flat base change; degree-1
form). -/
theorem syzygy_graph_restricted (hE₀ : IsNoetherianRing (unitBall E))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i)))
    (u : Fin m → P E m) (h : d1 r u = 0) :
    ∃ v, d2 r v = u := by sorry

/-- The graph ideal `I_E = im(d₁) ⊂ P_E` is **closed** ([FJP] Lemma 4.2: "every
differential has closed image … In particular `I_D = im(d₁) ⊂ P_D` is closed"; via the
noetherian finite-module theory of `NoetherianTateModules.lean`). Requires `P_E`
noetherian (strong noetherianity of the vertex). -/
theorem isClosed_graphIdeal [IsNoetherianRing (P E m)]
    (r : Fin m → P E m) :
    IsClosed ((Ideal.span (Set.range r) : Set (P E m))) := by sorry

/-- Strictness of `d₁` with an explicit constant ([FJP] (4.7): "an element `x ∈ I_E` has a
representative `u ∈ P_E^m` with `d_{1,E}(u) = x`, `‖u‖ ≤ h_E ‖x‖`"; from closedness + the
Banach open mapping theorem with constants). -/
theorem exists_d1_lift [IsNoetherianRing (P E m)] (r : Fin m → P E m) :
    ∃ h : ℝ, 1 ≤ h ∧ ∀ x ∈ Ideal.span (Set.range r),
      ∃ u : Fin m → P E m, d1 r u = x ∧ ‖u‖ ≤ h * ‖x‖ := by sorry

/-- Strictness of `d₂` onto `ker d₁` with an explicit constant ([FJP] (4.8): "every
`s ∈ ker(d_{1,D})` has `v ∈ ⋀² P_D^m` satisfying `d_{2,D}(v) = s`, `‖v‖ ≤ z_D ‖s‖`").
For `m = 1` the conclusion forces `ker d₁ = 0` (`Pairs 1` is empty), which holds because
`gT − f` is a nonzerodivisor. -/
theorem exists_d2_lift [IsNoetherianRing (P E m)]
    (hE₀ : IsNoetherianRing (unitBall E))
    (g : E) (f : Fin m → E) (hunit : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (r : Fin m → P E m)
    (hr : ∀ i, r i = polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))) :
    ∃ z : ℝ, 1 ≤ z ∧ ∀ u : Fin m → P E m, d1 r u = 0 →
      ∃ v : Pairs m → P E m, d2 r v = u ∧ ‖v‖ ≤ z * ‖u‖ := by sorry

end Restricted

end GraphKoszul

end FiniteJet
