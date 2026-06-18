/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».ValuationContinuity
import «Adic spaces».HuberRings
import «Adic spaces».ValuationSpectrum
import «Adic spaces».CharacteristicSubgroup
import «Adic spaces».Lemma745
import Mathlib.Combinatorics.Pigeonhole

/-!
# `Spv(A, I)` infrastructure (Wedhorn §7.1) — T-COMPACT-NO-HARCH foundation

Per round-22 reviewer (ChatGPT Pro, 2026-05-16): the no-`hArch` compactness
of rational opens in `Spa(A, A⁺)` for Tate rings goes via Wedhorn's
spectral space `Spv(A, I)`, **not** via the project's existing
Boolean-product encoding (which conflates Fσ cofinality with closed
conditions).

This file establishes the **definitional infrastructure** for `Spv(A, I)`
and the cofinality predicate used in Wedhorn 7.10's reverse direction.

## Main definitions

* `Valuation.CofinalValue v a` : `v(a)` is *cofinal* in `Γ_v ∪ {0}`, in
  the sense that for every `γ ∈ Γ_v` with `γ > 0`, there exists `n : ℕ`
  with `v(a)^n < γ`. This is the algebraic cofinality condition that
  Wedhorn 7.10's reverse direction uses to bridge `v(I) < 1` →
  continuity.

* `Spv.IsInSpvAI v I` : the disjunctive characterisation of
  `v ∈ Spv(A, I)` per Wedhorn Lemma 7.4: either every `a ∈ I` has
  `v(a)` cofinal in `Γ_v`, or `Γ_v = c Γ_v` (microbial).

## References

* Wedhorn, *Adic Spaces*, §7.1 (Definition 7.3, Lemma 7.4),
  arXiv:1910.05934.
-/

open Pointwise

namespace Valuation

variable {A : Type*} [CommRing A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Cofinality of `v(a)` in `Γ_v` (algebraic form, Wedhorn 7.4 prep).**
A value `v(a)` is *cofinal* if for every `γ : Γ₀` with `γ > 0`, some
power `v(a)^n` is strictly less than `γ`.

This is the algebraic predicate that Wedhorn 7.10's reverse direction
uses: combined with `v(a) < 1` it gives continuity of `v` (in the
`f`-adic / Tate setting). -/
def CofinalValue (v : Valuation A Γ₀) (a : A) : Prop :=
  ∀ γ : Γ₀, 0 < γ → ∃ n : ℕ, v a ^ n < γ

/-- `CofinalValue` implies `v(a) ≤ 1` (in fact `v(a) < 1`, unless `v(a) = 0`). -/
theorem CofinalValue.le_one {v : Valuation A Γ₀} {a : A} (h : CofinalValue v a) :
    v a ≤ 1 := by
  by_contra h_gt
  push Not at h_gt
  -- v(a) > 1 means v(a)^n ≥ 1 for all n.
  have h_pow_ge : ∀ n : ℕ, 1 ≤ v a ^ n := fun n ↦ Left.one_le_pow_of_le h_gt.le n
  -- Take γ = 1. Cofinality gives ∃ n, v(a)^n < 1. Contradicts h_pow_ge.
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  exact absurd hn (not_lt_of_ge (h_pow_ge n))

end Valuation

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- **`v ∈ Spv(A, I)` (Wedhorn 7.4 disjunction).** For `v : Spv A` and
`I : Ideal A`, `v` is *in `Spv(A, I)`* if either
- every `a ∈ I` has `v(a)` cofinal in `Γ_v`, or
- `v` is **microbial** (`Γ_v = c Γ_v` in Wedhorn 4.13 notation): every
  positive value of `v` is bounded by some `(v t)^±1` with `v t ≥ 1`.

This is the disjunctive characterisation per Wedhorn Lemma 7.4(ii). -/
def Spv.IsInSpvAI (v : Spv A) (I : Ideal A) : Prop :=
  letI : ValuativeRel A := v.toValuativeRel
  (∀ a ∈ I, Valuation.CofinalValue (ValuativeRel.valuation A) a) ∨
  Valuation.IsMicrobial (ValuativeRel.valuation A)

/-- **Per-`v` uniform decay on `I^n` from per-generator cofinality.**
Given `v : Valuation A Γ₀` with `v ≤ 1` on `P.A₀` and `CofinalValue v c`
for each generator `c` of `P.I`, conclude: for every `γ > 0`, there is
`n : ℕ` such that `v(a) < γ` for every `a ∈ P.I^n`. This discharges the
hypothesis of `Valuation.isContinuous_of_ideal_pow_lt` without
`MulArchimedean`.

The proof uses **the same pigeonhole + monomial-bound technique as the
P3 domination lemma** (`exists_ideal_pow_generators_dominated_for_half_space`),
specialised to a single `v` (no compactness needed).

This is the algebraic heart of Wedhorn 7.10's reverse direction. -/
theorem cofinalValue_ideal_pow_lt {A : Type*} [CommRing A] [TopologicalSpace A]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation A Γ₀}
    (P : PairOfDefinition A)
    (h_le_one : ∀ a : P.A₀, v (P.A₀.subtype a) ≤ 1)
    (h_cofinal : ∀ c : P.A₀, c ∈ P.I → Valuation.CofinalValue v (P.A₀.subtype c))
    (γ : Γ₀) (hγ : 0 < γ) :
    ∃ n : ℕ, ∀ a : P.A₀, a ∈ P.I ^ n → v (P.A₀.subtype a) < γ := by
  classical
  -- Extract FG generators S of P.I.
  obtain ⟨S, hS_span⟩ := P.fg
  -- Per-generator: ∀ c ∈ S, ∃ N_c with v(c)^{N_c} < γ.
  have h_per_c : ∀ c ∈ S, ∃ N : ℕ, v (P.A₀.subtype c) ^ N < γ := by
    intro c hc
    apply h_cofinal c (hS_span ▸ Ideal.subset_span hc) γ hγ
  choose N_c hN_c using h_per_c
  -- N_max := max over S of N_c.
  let N_max : ℕ := (S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc)).sup id + 1
  -- n₀ := (S.card + 1) * N_max.
  let n₀ : ℕ := (S.card + 1) * N_max
  refine ⟨n₀, fun a ha ↦ ?_⟩
  -- a ∈ P.I^n₀ = (Ideal.span S)^n₀ = Ideal.span (S^n₀ as Set).
  -- We bound v(a) ≤ max over monomials of v(monomial), and each monomial < γ.
  --
  -- Use `Submodule.span_induction` to reduce to the spanning set.
  have h_span_eq : (S : Set P.A₀) = ↑S := rfl
  have ha' : a ∈ Ideal.span ((S ^ n₀ : Finset P.A₀) : Set P.A₀) := by
    rw [Finset.coe_pow]
    rw [show (Ideal.span ((↑S : Set P.A₀) ^ n₀) : Ideal P.A₀) =
        (Ideal.span (↑S : Set P.A₀)) ^ n₀ from
      (Submodule.span_pow (↑S : Set P.A₀) n₀).symm]
    rw [hS_span]
    exact ha
  -- Now bound via induction on the span structure.
  refine Submodule.span_induction
    (M := P.A₀) (R := P.A₀)
    (s := ((S ^ n₀ : Finset P.A₀) : Set P.A₀))
    (p := fun x _ ↦ v (P.A₀.subtype x) < γ) ?_ ?_ ?_ ?_ ha'
  · -- Generator case: x ∈ S^n₀ as Finset.
    intro x hx
    -- x ∈ S^n₀ → ∃ f : Fin n₀ → ↥S with (List.ofFn fun i => ↑(f i)).prod = x.
    rw [show ((S ^ n₀ : Finset P.A₀) : Set P.A₀) = ((S ^ n₀ : Finset P.A₀) : Set P.A₀)
        from rfl] at hx
    have hx_mem : x ∈ (S ^ n₀ : Finset P.A₀) := hx
    rw [Finset.mem_pow] at hx_mem
    obtain ⟨f, hf⟩ := hx_mem
    -- Express v(P.A₀.subtype x) as ∏ via List.prod_ofFn + map_prod.
    have hx_eq : (P.A₀.subtype x : A) =
        ∏ i : Fin n₀, (P.A₀.subtype (↑(f i) : P.A₀) : A) := by
      have h_map : (P.A₀.subtype : P.A₀ →+* A)
          ((List.ofFn fun i ↦ (↑(f i) : P.A₀)).prod) =
          ((List.ofFn fun i ↦ (↑(f i) : P.A₀)).map P.A₀.subtype).prod :=
        map_list_prod P.A₀.subtype _
      rw [← hf, h_map, List.map_ofFn, List.prod_ofFn]
      rfl
    rw [hx_eq, map_prod]
    -- v(∏ i, P.A₀.subtype (↑(f i))) = ∏ i, v(P.A₀.subtype (↑(f i)))
    -- Pigeonhole: some c ∈ S has count ≥ N_max.
    by_cases hS_ne : S.Nonempty
    · haveI : Nonempty ↥S := hS_ne.coe_sort
      have h_card_le : Fintype.card ↥S * N_max ≤ Fintype.card (Fin n₀) := by
        simp only [Fintype.card_fin, Fintype.card_coe]
        change S.card * N_max ≤ (S.card + 1) * N_max
        calc S.card * N_max ≤ S.card * N_max + N_max := Nat.le_add_right _ _
          _ = (S.card + 1) * N_max := by ring
      obtain ⟨c_star, hc_count⟩ :=
        Fintype.exists_le_card_fiber_of_mul_le_card (f := f) (n := N_max) h_card_le
      -- Group by fiber.
      rw [show (∏ i : Fin n₀, v (P.A₀.subtype (↑(f i) : P.A₀))) =
          ∏ c : ↥S, ∏ i : Fin n₀ with f i = c,
            v (P.A₀.subtype (↑c : P.A₀)) by
        rw [Finset.prod_fiberwise' (s := Finset.univ) (g := f)
          (f := fun c : ↥S ↦ v (P.A₀.subtype (↑c : P.A₀)))]]
      have h_inner : ∀ c : ↥S, (∏ i ∈ Finset.univ.filter (fun i ↦ f i = c),
          v (P.A₀.subtype (↑c : P.A₀))) =
          v (P.A₀.subtype (↑c : P.A₀)) ^
          (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card := by
        intro c
        rw [Finset.prod_const]
      rw [Finset.prod_congr rfl fun c _ ↦ h_inner c]
      rw [← Finset.prod_erase_mul (Finset.univ : Finset ↥S) _ (Finset.mem_univ c_star)]
      -- Bound `others ≤ 1` and `c_star_factor < γ`.
      have h_v_c_le_one : ∀ c : ↥S, v (P.A₀.subtype (↑c : P.A₀)) ≤ 1 := fun c ↦
        h_le_one (↑c : P.A₀)
      have h_others_le_one :
          (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star,
            v (P.A₀.subtype (↑c : P.A₀)) ^
            (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card) ≤ 1 := by
        refine Finset.prod_le_one' ?_
        intro c _
        exact Left.pow_le_one_of_le (h_v_c_le_one c) _
      have h_c_star_lt : v (P.A₀.subtype (↑c_star : P.A₀)) ^
          (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card < γ := by
        set count := (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card
        set N_star := N_c (↑c_star : P.A₀) c_star.2
        have h_N_max_ge : N_max ≥ N_star + 1 := by
          change (S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc)).sup id + 1 ≥ N_star + 1
          apply Nat.add_le_add_right
          have h_mem_image : N_star ∈ S.attach.image (fun ⟨c, hc⟩ ↦ N_c c hc) := by
            rw [Finset.mem_image]
            refine ⟨⟨(↑c_star : P.A₀), c_star.2⟩, Finset.mem_attach _ _, rfl⟩
          exact Finset.le_sup (f := id) h_mem_image
        have h_count_ge_N : count ≥ N_star := by
          calc count ≥ N_max := hc_count
            _ ≥ N_star + 1 := h_N_max_ge
            _ ≥ N_star := Nat.le_succ _
        have h_v_c_le_one_star : v (P.A₀.subtype (↑c_star : P.A₀)) ≤ 1 :=
          h_v_c_le_one c_star
        have h_pow_mono :
            v (P.A₀.subtype (↑c_star : P.A₀)) ^ count ≤
            v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_count_ge_N
          rw [hk, pow_add]
          conv_rhs => rw [← mul_one (v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star)]
          exact mul_le_mul_right (Left.pow_le_one_of_le h_v_c_le_one_star k) _
        calc v (P.A₀.subtype (↑c_star : P.A₀)) ^ count
            ≤ v (P.A₀.subtype (↑c_star : P.A₀)) ^ N_star := h_pow_mono
          _ < γ := hN_c (↑c_star : P.A₀) c_star.2
      calc (∏ c ∈ (Finset.univ : Finset ↥S).erase c_star,
              v (P.A₀.subtype (↑c : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c)).card) *
            v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card
          ≤ 1 * v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card := by
            exact mul_le_mul_left h_others_le_one _
        _ = v (P.A₀.subtype (↑c_star : P.A₀)) ^
              (Finset.univ.filter (fun i : Fin n₀ ↦ f i = c_star)).card := one_mul _
        _ < γ := h_c_star_lt
    · -- S empty: f vacuous, contradiction.
      exfalso
      rw [Finset.not_nonempty_iff_eq_empty] at hS_ne
      have hn₀_pos : 0 < n₀ := by
        change 0 < (S.card + 1) * N_max
        apply Nat.mul_pos
        · exact Nat.succ_pos _
        · change 0 < (S.attach.image _).sup id + 1
          exact Nat.succ_pos _
      exact (Finset.eq_empty_iff_forall_notMem.mp hS_ne) _ (f ⟨0, hn₀_pos⟩).2
  · -- Zero case: v(0) = 0 < γ.
    simp [map_zero]; exact hγ
  · -- Add case: v(x + y) ≤ max v(x) v(y) < γ.
    intro x y _ _ hx hy
    simp only [map_add]
    calc v (P.A₀.subtype x + P.A₀.subtype y)
        ≤ max (v (P.A₀.subtype x)) (v (P.A₀.subtype y)) := v.map_add _ _
      _ < γ := max_lt hx hy
  · -- Scale case: v(r · x) = v(r) · v(x) ≤ v(x) < γ (since v(r) ≤ 1).
    intro r x _ hx
    rw [show P.A₀.subtype (r • x) = P.A₀.subtype r * P.A₀.subtype x by
      simp [smul_eq_mul]]
    rw [map_mul]
    have hr_le : v (P.A₀.subtype r) ≤ 1 := h_le_one r
    calc v (P.A₀.subtype r) * v (P.A₀.subtype x)
        ≤ 1 * v (P.A₀.subtype x) := by
          exact mul_le_mul_left hr_le _
      _ = v (P.A₀.subtype x) := one_mul _
      _ < γ := hx

/-- **Wedhorn 7.10 reverse direction (project form, cofinality disjunct
case).** For an `f`-adic ring `A` with pair of definition `P`, if
`v : Spv A` satisfies the **cofinality disjunct** of `Spv.IsInSpvAI`
(every `I`-image element has cofinal value) and `v ≤ 1` on `P.A₀`, then
`v` is continuous.

This handles the simpler case of Wedhorn 7.10. The microbial case
(`Γ_v = c Γ_v`) is a separate, more technical argument; the combined
result (both disjuncts) is `Spv.isContinuous_of_isInSpvAI_of_lt_one`
(currently TODO). -/
theorem Spv.isContinuous_of_cofinal_disjunct [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (h_cofinal : letI : ValuativeRel A := v.toValuativeRel
      ∀ a : P.A₀, a ∈ P.I →
        Valuation.CofinalValue (ValuativeRel.valuation A) (P.A₀.subtype a))
    (h_le_one : letI : ValuativeRel A := v.toValuativeRel
      ∀ a : P.A₀, (ValuativeRel.valuation A) (P.A₀.subtype a) ≤ 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  exact Valuation.isContinuous_of_ideal_pow_lt P (ValuativeRel.valuation A)
    (fun γ hγ ↦ cofinalValue_ideal_pow_lt P h_le_one h_cofinal γ hγ)

/-- **Wedhorn 7.10 reverse direction (project form).** Full proof using
both disjuncts of `Spv.IsInSpvAI`.

Cofinality disjunct: direct application of `cofinalValue_ideal_pow_lt`
+ `Valuation.isContinuous_of_ideal_pow_lt`.

Microbial disjunct (Wedhorn p. 59): for each `c ∈ P.I` and `γ' > 0`,
use `IsMicrobial.exists_inv_le` to find `t ∈ A` with `v(t)⁻¹ ≤ γ'`.
Then `c` topologically nilpotent + `exists_pow_mul_mem_A₀` gives
`c^{n₀} · t ∈ P.A₀`. Hence `c^{n₀+1} · t ∈ P.I`, so `v(c^{n₀+1} · t) < 1`
from `h_lt_one`, giving `v(c)^{n₀+1} < v(t)⁻¹ ≤ γ'`. -/
theorem Spv.isContinuous_of_isInSpvAI_of_lt_one [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (h_in : Spv.IsInSpvAI v (Ideal.map P.A₀.subtype P.I))
    (h_le_one : ∀ a : P.A₀,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) ≤ 1)
    (h_lt_one : ∀ a ∈ P.I,
      letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A) (P.A₀.subtype a) < 1) :
    letI : ValuativeRel A := v.toValuativeRel
    (ValuativeRel.valuation A).IsContinuous := by
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  -- Reduce to per-generator cofinality, then dispatch via Wedhorn 7.10.
  refine Valuation.isContinuous_of_ideal_pow_lt P wv ?_
  intro γ hγ
  apply cofinalValue_ideal_pow_lt P h_le_one ?_ γ hγ
  intro c hc
  -- Goal: CofinalValue wv (P.A₀.subtype c), i.e., ∀ γ' > 0, ∃ n, wv(c)^n < γ'.
  -- Case-split on h_in: cofinality disjunct or microbial disjunct.
  rcases h_in with h_cof | h_micr
  · -- Cofinality disjunct: P.A₀.subtype c is already in the I-image.
    apply h_cof
    exact Ideal.mem_map_of_mem _ hc
  · -- Microbial disjunct: Wedhorn 7.10's microbial argument.
    intro γ' hγ'
    -- IsMicrobial: ∃ t ∈ A with wv(t) ≠ 0 and wv(t)⁻¹ ≤ γ'.
    obtain ⟨t, h_vt_ne, h_vt_inv_le⟩ := h_micr.exists_inv_le hγ'
    -- c is topologically nilpotent in A.
    have hc_topnilp : IsTopologicallyNilpotent (P.A₀.subtype c) :=
      P.isTopologicallyNilpotent_of_mem hc
    -- ∃ n_0, (P.A₀.subtype c)^n_0 * t ∈ P.A₀.
    obtain ⟨n_0, hn_0⟩ := PairOfDefinition.exists_pow_mul_mem_A₀ P hc_topnilp t
    refine ⟨n_0 + 1, ?_⟩
    -- Construct b := c * ⟨c^n_0 * t, hn_0⟩ ∈ P.I (as P.A₀-ideal).
    let b : P.A₀ := c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩
    have hb_mem_I : b ∈ P.I :=
      Ideal.mul_mem_right _ _ hc
    -- v(b) < 1 from h_lt_one.
    have hb_lt_one : wv (P.A₀.subtype b) < 1 := h_lt_one b hb_mem_I
    -- v(b) = v(c)^(n_0+1) * v(t).
    have hb_eq : wv (P.A₀.subtype b) =
        wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t := by
      change wv (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩)) = _
      rw [show (P.A₀.subtype (c * ⟨(P.A₀.subtype c)^n_0 * t, hn_0⟩) : A) =
          P.A₀.subtype c * ((P.A₀.subtype c)^n_0 * t) from by
        simp]
      rw [map_mul, map_mul, map_pow]
      -- wv(c) * (wv(c)^n_0 * wv(t)) = wv(c)^(n_0+1) * wv(t).
      rw [show wv (P.A₀.subtype c) ^ (n_0 + 1) = wv (P.A₀.subtype c) * wv (P.A₀.subtype c) ^ n_0
        from by rw [pow_succ']]
      rw [mul_assoc]
    rw [hb_eq] at hb_lt_one
    -- v(c)^(n_0+1) * v(t) < 1 → v(c)^(n_0+1) < v(t)⁻¹.
    -- Multiply both sides by v(t)⁻¹ > 0 (v(t) ≠ 0).
    have h_pow_lt_inv : wv (P.A₀.subtype c) ^ (n_0 + 1) < (wv t)⁻¹ := by
      have h_vt_pos : 0 < wv t := zero_lt_iff.mpr h_vt_ne
      have h_inv_pos : 0 < (wv t)⁻¹ := inv_pos.mpr h_vt_pos
      -- x * y < 1, y > 0 → x < y⁻¹.
      -- Rewrite: x = (x * y) * y⁻¹ < 1 * y⁻¹ = y⁻¹.
      have h_x_eq : wv (P.A₀.subtype c) ^ (n_0 + 1) =
          (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ h_vt_ne, mul_one]
      rw [h_x_eq]
      calc (wv (P.A₀.subtype c) ^ (n_0 + 1) * wv t) * (wv t)⁻¹
          < 1 * (wv t)⁻¹ := by
            rw [mul_comm _ ((wv t)⁻¹), mul_comm 1 ((wv t)⁻¹)]
            exact (mul_lt_mul_iff_right₀ h_inv_pos).mpr hb_lt_one
        _ = (wv t)⁻¹ := one_mul _
    -- v(c)^(n_0+1) < v(t)⁻¹ ≤ γ'.
    exact lt_of_lt_of_le h_pow_lt_inv h_vt_inv_le

/-- **Wedhorn 7.11(1) forward / 7.10 forward direction.** For a continuous
valuation `v : Spv A` on an `f`-adic ring with pair of definition `P`,
`v(a)` is cofinal in `Γ_v` for every `a` in the ideal-of-definition
image.

This is the algebraic content of Wedhorn 7.11(1): continuity implies
cofinality of `v(I)`. -/
theorem Spv.cofinalValue_of_isContinuous [TopologicalSpace A]
    [IsTopologicalRing A]
    (P : PairOfDefinition A) (v : Spv A)
    (hv_cont : letI : ValuativeRel A := v.toValuativeRel
      (ValuativeRel.valuation A).IsContinuous)
    (a : P.A₀) (ha : a ∈ P.I) :
    letI : ValuativeRel A := v.toValuativeRel
    Valuation.CofinalValue (ValuativeRel.valuation A) (P.A₀.subtype a) := by
  letI : ValuativeRel A := v.toValuativeRel
  intro γ hγ
  -- v continuous → {x : v(x) < γ} open in A.
  have h_open : IsOpen {x : A | (ValuativeRel.valuation A) x < γ} := hv_cont γ
  have h_zero_mem : (0 : A) ∈ {x : A | (ValuativeRel.valuation A) x < γ} := by
    change (ValuativeRel.valuation A) 0 < γ
    rw [map_zero]; exact hγ
  have h_nhds : {x : A | (ValuativeRel.valuation A) x < γ} ∈ nhds (0 : A) :=
    h_open.mem_nhds h_zero_mem
  -- a ∈ P.I → P.A₀.subtype a is topologically nilpotent.
  have ha_topnilp : IsTopologicallyNilpotent (P.A₀.subtype a) :=
    P.isTopologicallyNilpotent_of_mem ha
  -- eventually (P.A₀.subtype a)^n is in the open neighborhood.
  obtain ⟨n, hn⟩ := (ha_topnilp.eventually h_nhds).exists
  -- hn : v((P.A₀.subtype a)^n) < γ. Convert to v(P.A₀.subtype a)^n < γ.
  rw [map_pow] at hn
  exact ⟨n, hn⟩

end ValuationSpectrum
