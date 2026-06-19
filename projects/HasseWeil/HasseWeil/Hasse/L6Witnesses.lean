/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Valuation.LocalSubring
import HasseWeil.Curves.FrobeniusFixedPoint
import HasseWeil.Curves.PicZero
import HasseWeil.Hasse.L6ViaPoleDivisor
import HasseWeil.Hasse.PointFix
import HasseWeil.Hasse.PoleDivisor2Tor
import HasseWeil.Hasse.PoleDivisorFallback

/-!
# L6 substantive witnesses — T5, T6, T6-SUB

R25h Worker-B Phase 1 (2026-05-19, after L6 chain composer shipment).
Ships the two substantive L6 witnesses needed by the top-level wrapper
`hasse_bound_from_L6_witnesses` (L6ViaPoleDivisor.lean, R23 shipment):

* **T6** (`ord_kernel_pullback_x_eq_neg_two`): `ordAtPoint T (γ.pullback
  x_gen) = -2` for every kernel point `T`. Decomposes the kernel into
  `.zero` (infinity), non-2-torsion finite points, and 2-torsion finite
  points; ships axiom-clean except for the 2-torsion case which is
  factored as the witness `h_two_torsion` per the project's
  witness-parametric closure pattern (the 2-torsion case requires the
  substantive content that lemma3_pole_at_T_unconditional defers via
  its `h_not_2_tor` hypothesis).
* **T5** (`support_card_eq_pointCount`): `|support
  (projectiveDivisorOf (γ.pullback x_gen))| = pointCount W.toAffine`.
  Witness-parametric on the substantive support-=-everywhere fact.
* **T6-SUB** (`ordAtPoint_pullback_separable_at_kernel`): the pullback
  ord formula at unramified preimages. Witness-parametric on the
  inverse-function-theorem-style content (Silverman II.2.6(c) for
  separable morphisms is itself substantial new infrastructure).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1 proof (book p.
  138), II.2.6(c).
* `tickets/R25h-FULL-STATEMENTS-AND-ADVERSARIAL.md` — the R25h plan.
* `HasseWeil/Hasse/PoleDivisorFallback.lean:2603` — `lemma3_pole_at_T_unconditional`
  (the non-2-torsion ord = -2 result).
* `HasseWeil/Hasse/PoleDivisorFallback.lean:95` —
  `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen` (the ∞ case).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

namespace Conditional

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## T6 — `ordAtPoint T (γ.pullback x_gen) = -2` at every kernel point

Decomposes into three cases:
1. `T = .zero` (= infinity): axiom-clean via shipped
   `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`.
2. `T = .some xT yT h_ns` non-2-torsion: axiom-clean via shipped
   `lemma3_pole_at_T_unconditional`.
3. `T = .some xT yT h_ns` 2-torsion: witness-parametric — the gap in
   the current lemma3 closure (covered by the
   `h_two_torsion_witness` hypothesis). -/

/-- **UNCONDITIONAL: T6 — Every kernel point of `γ = 1 − π` has pole order `-2`
of `γ.pullback x_gen`** (Silverman V.1.1).

Combines the three branches:
* `T = .zero` (infinity): `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen` (shipped)
* `T = .some xT yT h_ns` non-2-torsion: `lemma3_pole_at_T_unconditional` (PoleDivisorFallback)
* `T = .some xT yT h_ns` 2-torsion: `lemma3_pole_at_T_at_2tor` (PoleDivisor2Tor, this session)

All three branches are now axiom-clean. -/
theorem ord_kernel_pullback_x_eq_neg_two
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtPoint T.val
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      (-2 : ℤ) := by
  rcases T.val with _ | ⟨xT, yT, h_ns⟩
  · rw [SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty]
    exact ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq
  · rw [SmoothPlaneCurve.ordAtPoint_some_eq_ord_P]
    by_cases h_2tor : yT = W.toAffine.negY xT yT
    · exact lemma3_pole_at_T_at_2tor W xT yT h_ns h_2tor hq
    · exact lemma3_pole_at_T_unconditional W xT yT h_ns h_2tor hq

omit [Fintype K] [DecidableEq K] in
/-- **Polynomial-in-1/f lands in valuation integer ring**: for any polynomial `p`,
the image `polyToFieldOfInv f p` satisfies `pointValuation P ≤ 1` provided
`pointValuation P f⁻¹ ≤ 1`. Induction on polynomial structure. -/
theorem pointValuation_polyToFieldOfInv_le_one
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (P : Curves.SmoothPlaneCurve.SmoothPoint
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K))
    (f : W.toAffine.FunctionField)
    (h_inv_le_one : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
      f⁻¹ ≤ 1)
    (p : Polynomial K) :
    (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
        (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f p) ≤ 1 := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [Curves.RamificationAtInfinity.polyToFieldOfInv_C]
    exact (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation_algebraMap_F_le_one
      P c
  | add p q hp hq =>
    rw [map_add]
    exact le_trans ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation
      P |>.map_add _ _) (max_le hp hq)
  | monomial n c _ih =>
    rw [map_mul, map_pow,
        Curves.RamificationAtInfinity.polyToFieldOfInv_C,
        Curves.RamificationAtInfinity.polyToFieldOfInv_X, map_mul]
    have h_c : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
        ((algebraMap K W.toAffine.FunctionField) c) ≤ 1 :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation_algebraMap_F_le_one
        P c
    have h_inv_pow : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
        (f⁻¹ ^ (n + 1)) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one' h_inv_le_one (n + 1)
    simpa using mul_le_one' h_c h_inv_pow

omit [Fintype K] [DecidableEq K] in
/-- **General API**: for any `f : K(E)` with `1/f` in the valuation integer at a smooth
point `P`, every element of `Sinf.carrier` for `f` has nonneg ord at `P` (when viewed
in `K(E)` via the embedding). General version of
`Sinf_ord_nonneg_at_kernel_point_unconditional` (below). -/
theorem sinf_carrier_ord_nonneg_of_inv_le_one
    {W : WeierstrassCurve K} [W.toAffine.IsElliptic]
    (P : Curves.SmoothPlaneCurve.SmoothPoint
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K))
    (f : W.toAffine.FunctionField)
    (h_inv_le_one : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
      f⁻¹ ≤ 1)
    (data : Curves.RamificationAtInfinity.Sinf (k := K) f)
    (a : data.carrier) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ord_P P
        (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K) f) a) := by
  letI := data.commRing
  letI := data.algLinfAt
  letI := data.algPoly
  letI := data.isScalarTower
  letI := data.moduleFinite
  haveI : Algebra.IsIntegral (Polynomial K) data.carrier :=
    Algebra.IsIntegral.of_finite (Polynomial K) data.carrier
  have h_int_a : IsIntegral (Polynomial K) a :=
    Algebra.IsIntegral.isIntegral (R := Polynomial K) a
  have h_int_b : IsIntegral (Polynomial K)
      (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K) f) a) :=
    h_int_a.algebraMap (B := Curves.RamificationAtInfinity.LinfAt (k := K) f)
  set b : W.toAffine.FunctionField :=
    algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K) f) a
    with hb_def
  let φ : Polynomial K →+* ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).integer :=
    (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f).toRingHom.codRestrict
      _ (pointValuation_polyToFieldOfInv_le_one W P f h_inv_le_one)
  obtain ⟨p, hp_monic, hp_eval⟩ := h_int_b
  have h_int_O : IsIntegral
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).integer b := by
    refine ⟨p.map φ, hp_monic.map _, ?_⟩
    change (Polynomial.aeval b) (p.map φ) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have h_comp :
        (algebraMap ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).integer
          W.toAffine.FunctionField).comp φ =
          (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f).toRingHom := rfl
    rw [h_comp]
    exact hp_eval
  have h_v_le :
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P b ≤ 1 :=
    (Valuation.integer.integers
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P)
    ).isIntegral_iff_v_le_one.mp h_int_O
  by_cases hb : b = 0
  · rw [hb, Curves.SmoothPlaneCurve.ord_P_zero]; exact le_top
  · have hv :
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P b ≠ 0 :=
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).ne_zero_iff.mpr hb
    unfold Curves.SmoothPlaneCurve.ord_P
    rw [dif_neg hv, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]
      exact h_v_le
    exact neg_nonneg.mpr (Multiplicative.toAdd_le.mpr h_unz_le)

/-- **UNCONDITIONAL: `ord_T((γ.pullback x_gen)⁻¹) = 2`** for every kernel point `T`:
`1/f` has a zero of order 2 at every kernel point. -/
theorem inv_gamma_pullback_x_pos_at_kernel
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtPoint T.val
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ =
        (2 : WithTop ℤ) :=
  OpenLemmaPrimitives.kernel_point_is_pole_of_gamma_pullback_x W hq T
    (ord_kernel_pullback_x_eq_neg_two W hq T)

/-- Every `Sinf`-carrier element has nonnegative `ord_P` at an affine kernel point. -/
theorem Sinf_ord_nonneg_at_affine_kernel_point
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT)
    (h_T_val : T.val = Affine.Point.some xT yT h_ns)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (a : data.carrier) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ord_P
        ⟨xT, yT, h_ns⟩
        (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) := by
  have h_inv_pos := inv_gamma_pullback_x_pos_at_kernel W hq T
  rw [h_T_val, Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P] at h_inv_pos
  have h_f_inv_ne : ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ ≠ 0 := by
    intro h_zero
    rw [h_zero, Curves.SmoothPlaneCurve.ord_P_zero] at h_inv_pos
    exact WithTop.coe_ne_top h_inv_pos.symm
  have h_inv_ord_nonneg : (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ord_P ⟨xT, yT, h_ns⟩
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ := by
    rw [h_inv_pos]; norm_num
  have h_inv_le_one :
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation ⟨xT, yT, h_ns⟩
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ ≤ 1 :=
    Curves.pointValuation_le_one_of_ord_nonneg
      (W := W.toAffine) h_f_inv_ne ⟨xT, yT, h_ns⟩ h_inv_ord_nonneg
  exact sinf_carrier_ord_nonneg_of_inv_le_one
    (W := W) ⟨xT, yT, h_ns⟩
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) h_inv_le_one data a

/-! ## Decomposition skeletons (Phase 1e Step 2.5)

The following lemmas are stated with `sorry` to lock down the decomposition tree.
Each `sorry` is a planned-leaf in `.mathlib-quality/decomposition-residual-walls.md`
with attached source citation and adversarial-attack record. -/

omit [Fintype K] in
/-- **DECOMP — Obstacle 1, L2**: Polynomial in 1/f has `ord_∞ ≥ 0` when
`0 ≤ ord_∞ f⁻¹`.

Source: Silverman II.1 + IV.1 (valuation algebra at infinity). -/
theorem ordAtInfty_polyToFieldOfInv_nonneg
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (f : W.toAffine.FunctionField)
    (h_inv_nonneg : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty f⁻¹)
    (p : Polynomial K) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f p) := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [Curves.RamificationAtInfinity.polyToFieldOfInv_C]
    by_cases hc : c = 0
    · subst hc
      rw [map_zero]
      exact le_top.trans_eq (W_smooth W).ordAtInfty_zero.symm
    · rw [ordAtInfty_algebraMap_F_nonzero (W := W) hc]
  | add p q hp hq =>
    rw [map_add]
    exact le_trans (le_min hp hq) ((W_smooth W).ordAtInfty_add_ge_min _ _)
  | monomial n c _ih =>
    rw [map_mul, map_pow,
        Curves.RamificationAtInfinity.polyToFieldOfInv_C,
        Curves.RamificationAtInfinity.polyToFieldOfInv_X]
    by_cases hc : c = 0
    · subst hc
      rw [map_zero, zero_mul]
      exact le_top.trans_eq (W_smooth W).ordAtInfty_zero.symm
    · by_cases hf_inv : f⁻¹ = 0
      · rw [hf_inv, zero_pow (by omega : n + 1 ≠ 0), mul_zero]
        exact le_top.trans_eq (W_smooth W).ordAtInfty_zero.symm
      · have h_alg_ne : (algebraMap K W.toAffine.FunctionField) c ≠ 0 := fun heq ↦
          hc <| (algebraMap K W.toAffine.FunctionField).injective <| by rwa [map_zero]
        have h_pow_ne : f⁻¹ ^ (n + 1) ≠ 0 := pow_ne_zero _ hf_inv
        have h_mul : (W_smooth W).ordAtInfty
            ((algebraMap K W.toAffine.FunctionField) c * f⁻¹ ^ (n + 1)) =
            (W_smooth W).ordAtInfty ((algebraMap K W.toAffine.FunctionField) c) +
            (W_smooth W).ordAtInfty (f⁻¹ ^ (n + 1)) :=
          (W_smooth W).ordAtInfty_mul h_alg_ne h_pow_ne
        rw [h_mul, ordAtInfty_algebraMap_F_nonzero (W := W) hc, zero_add]
        have h_pow : (W_smooth W).ordAtInfty (f⁻¹ ^ (n + 1)) =
            (n + 1) • (W_smooth W).ordAtInfty f⁻¹ :=
          (W_smooth W).ordAtInfty_pow hf_inv (n + 1)
        rw [h_pow]
        exact nsmul_nonneg h_inv_nonneg (n + 1)

omit [Fintype K] [DecidableEq K] in
/-- Strict-dominance of `ord_∞` over a Finset sum: if every summand has `ord_∞` strictly
greater than some finite bound `c`, so does the sum. -/
lemma ord_finset_sum_strict_gt
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (C : Curves.SmoothPlaneCurve K) (φ : ι → C.FunctionField)
    (c : WithTop ℤ) (hc : c ≠ ⊤)
    (h : ∀ i ∈ s, c < C.ordAtInfty (φ i)) :
    c < C.ordAtInfty (∑ i ∈ s, φ i) := by
  induction s using Finset.induction with
  | empty =>
    simpa only [Finset.sum_empty, C.ordAtInfty_zero] using hc.lt_top
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (lt_min (h i (Finset.mem_insert_self _ _))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))).trans_le (C.ordAtInfty_add_ge_min _ _)

omit [Fintype K] in
/-- **DECOMP — Obstacle 1, L3**: if `g : K(E)` is integral over `Polynomial K`
(via `polyToFieldOfInv f`) and `ord_∞(1/f) ≥ 0`, then `ord_∞(g) ≥ 0`.

Source: classical valuation theory (Atiyah-Macdonald §5 / Bourbaki Comm Alg V§1). -/
theorem ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (f : W.toAffine.FunctionField)
    (h_inv_nonneg : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty f⁻¹)
    (g : W.toAffine.FunctionField)
    (h_int :
      letI : Algebra (Polynomial K) W.toAffine.FunctionField :=
        (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f).toRingHom.toAlgebra
      IsIntegral (Polynomial K) g) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty g := by
  letI : Algebra (Polynomial K) W.toAffine.FunctionField :=
    (Curves.RamificationAtInfinity.polyToFieldOfInv (k := K) f).toRingHom.toAlgebra
  by_contra h_neg
  push Not at h_neg
  -- Extract m : ℤ with ord_∞ g = m and m < 0
  have h_zero_top : (W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField) = ⊤ :=
    Curves.SmoothPlaneCurve.ordAtInfty_zero (C := W_smooth W)
  have hg_ne : g ≠ 0 := by
    intro hg
    rw [hg, h_zero_top] at h_neg
    exact not_top_lt h_neg
  have h_ne_top : (W_smooth W).ordAtInfty g ≠ ⊤ := by
    rw [Ne, (W_smooth W).ordAtInfty_eq_top_iff]; exact hg_ne
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W).ordAtInfty g = ((m : ℤ) : WithTop ℤ) := by
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
    exact ⟨m, hm.symm⟩
  have hm_neg : m < 0 := by
    rw [hm] at h_neg
    exact_mod_cast h_neg
  -- Get the monic polynomial
  obtain ⟨p, hp_monic, hp_eval⟩ := h_int
  set n := p.natDegree with hn_def
  -- Sublemma: ord(aeval g q) > k*m for any q with natDegree q < k.
  -- Uses eval₂_eq_sum_range' (avoids smul, gets f(coeff)·x^i directly).
  have h_sum_strict_gt : ∀ (q : Polynomial (Polynomial K)) (k : ℕ),
      q.natDegree < k →
      (((k : ℤ) * m : ℤ) : WithTop ℤ) < (W_smooth W).ordAtInfty
        ((Polynomial.aeval g) q) := by
    intro q k hqk
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range' _ hqk]
    apply ord_finset_sum_strict_gt _ (W_smooth W)
    · exact WithTop.coe_ne_top
    intro i hi
    rw [Finset.mem_range] at hi
    -- The summand is (algebraMap (Polynomial K) K(E)) (q.coeff i) * g^i.
    -- algebraMap here = (polyToFieldOfInv f).toRingHom = polyToFieldOfInv f as func.
    by_cases h_coef_zero :
        (algebraMap (Polynomial K) W.toAffine.FunctionField) (q.coeff i) = 0
    · -- coefficient evaluates to zero, the whole term is 0, ord = ⊤
      rw [h_coef_zero, zero_mul, h_zero_top]
      exact WithTop.coe_lt_top _
    · -- coefficient nonzero: ord(coeff) + i*m, both terms nonneg + dominate
      have h_gi_ne : g^i ≠ 0 := pow_ne_zero _ hg_ne
      have h_mul_eq : (W_smooth W).ordAtInfty
          ((algebraMap (Polynomial K) W.toAffine.FunctionField) (q.coeff i) * g^i) =
          (W_smooth W).ordAtInfty
              ((algebraMap (Polynomial K) W.toAffine.FunctionField) (q.coeff i)) +
            (W_smooth W).ordAtInfty (g^i) :=
        (W_smooth W).ordAtInfty_mul h_coef_zero h_gi_ne
      rw [h_mul_eq]
      have h_coef_nn : (0 : WithTop ℤ) ≤
          (W_smooth W).ordAtInfty
            ((algebraMap (Polynomial K) W.toAffine.FunctionField) (q.coeff i)) :=
        ordAtInfty_polyToFieldOfInv_nonneg W f h_inv_nonneg _
      have h_gi : (W_smooth W).ordAtInfty (g^i) = (((i : ℤ) * m : ℤ) : WithTop ℤ) :=
        (W_smooth W).ordAtInfty_pow_of_ord_eq hg_ne m i hm
      rw [h_gi]
      have h_im_gt_km : ((k : ℤ) * m : ℤ) < ((i : ℤ) * m : ℤ) := by
        have h_ik : (i : ℤ) < (k : ℤ) := by exact_mod_cast hi
        nlinarith
      have h_im_gt_km_wt :
          (((k : ℤ) * m : ℤ) : WithTop ℤ) < (((i : ℤ) * m : ℤ) : WithTop ℤ) := by
        exact_mod_cast h_im_gt_km
      exact h_im_gt_km_wt.trans_le (le_add_of_nonneg_left h_coef_nn)
  -- Split on n
  rcases Nat.eq_zero_or_pos n with hn_zero | hn_pos
  · -- n = 0: p is monic of degree 0, so p = 1
    have h_p_C : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hn_zero
    have h_coef_eq : p.coeff 0 = 1 := by
      have h_lc : p.leadingCoeff = 1 := hp_monic
      rw [Polynomial.leadingCoeff, ← hn_def, hn_zero] at h_lc
      exact h_lc
    have h_p_eq : p = 1 := by rw [h_p_C, h_coef_eq, Polynomial.C_1]
    have h_eval_one :
        Polynomial.eval₂ (algebraMap (Polynomial K) W.toAffine.FunctionField) g 1 = 1 :=
      Polynomial.eval₂_one _ _
    rw [h_p_eq, h_eval_one] at hp_eval
    exact one_ne_zero hp_eval
  · -- n ≥ 1: strict-dominance
    have h_lead : p.leadingCoeff = 1 := hp_monic
    have h_split : p = p.eraseLead + Polynomial.X ^ n := by
      have h := Polynomial.eraseLead_add_C_mul_X_pow p
      rw [h_lead, Polynomial.C_1, one_mul, ← hn_def] at h
      exact h.symm
    have h_aeval_split :
        (Polynomial.aeval g) p = (Polynomial.aeval g) p.eraseLead + g ^ n := by
      nth_rewrite 1 [h_split]
      rw [map_add, Polynomial.aeval_X_pow]
    have h_gn : (W_smooth W).ordAtInfty (g ^ n) = (((n : ℤ) * m : ℤ) : WithTop ℤ) :=
      (W_smooth W).ordAtInfty_pow_of_ord_eq hg_ne m n hm
    have h_erase_natDeg : p.eraseLead.natDegree < n := by
      have h_le := Polynomial.eraseLead_natDegree_le p
      omega
    have h_erase_bound : (((n : ℤ) * m : ℤ) : WithTop ℤ) <
        (W_smooth W).ordAtInfty ((Polynomial.aeval g) p.eraseLead) :=
      h_sum_strict_gt p.eraseLead n h_erase_natDeg
    -- ord(g^n) < ord(aeval g (eraseLead p)) so ord(aeval g p) = ord(g^n) = n*m
    have h_lt : (W_smooth W).ordAtInfty (g ^ n) <
        (W_smooth W).ordAtInfty ((Polynomial.aeval g) p.eraseLead) := by
      rw [h_gn]; exact h_erase_bound
    have h_add_eq : (W_smooth W).ordAtInfty
        (g ^ n + (Polynomial.aeval g) p.eraseLead) =
        (W_smooth W).ordAtInfty (g ^ n) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    have h_aeval_ord :
        (W_smooth W).ordAtInfty ((Polynomial.aeval g) p) =
        (((n : ℤ) * m : ℤ) : WithTop ℤ) := by
      rw [h_aeval_split, add_comm, h_add_eq]
      exact h_gn
    -- Convert hp_eval (eval₂ form) to aeval form via defeq, then rewrite
    have hp_eval_aeval : (Polynomial.aeval g) p = 0 := hp_eval
    rw [hp_eval_aeval, h_zero_top] at h_aeval_ord
    exact WithTop.top_ne_coe h_aeval_ord

omit [Fintype K] in
/-- **DECOMP — Obstacle 1, composer**: Sinf carrier elements have nonneg ord_∞.

Source: composes `Module.Finite → IsIntegral` (carrier) + `IsIntegral.algebraMap`
(transfer to K(E)) + `ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv`. -/
theorem sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg
    {W : WeierstrassCurve K} [W.toAffine.IsElliptic]
    (f : W.toAffine.FunctionField)
    (h_inv_nonneg : (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty f⁻¹)
    (data : Curves.RamificationAtInfinity.Sinf (k := K) f)
    (a : data.carrier) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K) f) a) := by
  letI := data.commRing
  letI := data.algLinfAt
  letI := data.algPoly
  letI := data.isScalarTower
  letI := data.moduleFinite
  haveI : Algebra.IsIntegral (Polynomial K) data.carrier :=
    Algebra.IsIntegral.of_finite (Polynomial K) data.carrier
  have h_int_a : IsIntegral (Polynomial K) a := Algebra.IsIntegral.isIntegral a
  exact ordAtInfty_nonneg_of_isIntegral_polyToFieldOfInv W f h_inv_nonneg _
    (h_int_a.algebraMap (B := Curves.RamificationAtInfinity.LinfAt (k := K) f))

/-- **DECOMP — Obstacle 1, kernel-point specialization**: at `T.val = .zero`,
Sinf-carrier elements have nonneg `ord_∞`. -/
theorem Sinf_ordAtInfty_nonneg_at_infinity_kernel_point
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (h_T_val : T.val = Affine.Point.zero)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (a : data.carrier) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤ (W_smooth W).ordAtInfty
        (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) := by
  have h_inv_pos := inv_gamma_pullback_x_pos_at_kernel W hq T
  rw [h_T_val, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] at h_inv_pos
  have h_inv_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ordAtInfty
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ := by
    change (0 : WithTop ℤ) ≤ (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtInfty
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹
    rw [h_inv_pos]
    norm_num
  exact sinf_carrier_ordAtInfty_nonneg_of_inv_nonneg
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) h_inv_nonneg data a

/-- **UNCONDITIONAL: Sinf carrier elements have nonneg ord at every kernel point**.

The downstream-located counterpart of the upstream `OpenLemmaPrimitives` stub
`Sinf_ord_nonneg_at_kernel_point` (deleted 2026-06-11), fully proven via case split on `T.val`:
* `.zero` → `Sinf_ordAtInfty_nonneg_at_infinity_kernel_point`
* `.some xT yT h_ns` → `Sinf_ord_nonneg_at_affine_kernel_point` (axiom-clean) -/
theorem Sinf_ord_nonneg_at_kernel_point_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (a : data.carrier) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) := by
  rcases h_T_val : T.val with _ | ⟨xT, yT, h_ns⟩
  · rw [Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty]
    exact Sinf_ordAtInfty_nonneg_at_infinity_kernel_point W hq T h_T_val data a
  · rw [Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P]
    exact Sinf_ord_nonneg_at_affine_kernel_point W hq T xT yT h_ns h_T_val data a

/-! ## Obstacle 2 — kernel-prime correspondence helpers

**`isIntegral_polyToFieldOfInv_gamma_pullback_x` DELETED 2026-05-25** per Attack-9
dry-run gate. The statement claimed UNIVERSAL integrality of every `g : K(E)` over
`Polynomial K` via the algebra `X ↦ 1/f` (where `f = (1-π)*x_gen`). This is FALSE:
elements like `f` itself, or `y_gen`, are transcendental over K and NOT integral
over `K[1/f]`. The docstring's "finite ⟹ integral" argument conflated **algebraic**
with **integral** — finite field extensions give algebraic elements, only the
integral closure subring is integral. The correct statement would be restricted to
`g ∈ image(algebraMap data.carrier K(E))`, which is trivially
`IsIntegralClosure.isIntegral_iff` ⟸ direction.

Zero consumers (verified by grep before deletion); leaf was stranded. B2 logged
at `.mathlib-quality/b2_log.jsonl` (entry `AUDIT-2a-E.6`, 2026-05-25). -/

theorem ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (T : (isogOneSub_negFrobenius W hq).kernel)
    -- 2-torsion witness: covers the remaining substantive subcase.
    (h_two_torsion_witness :
      ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        T.val = Affine.Point.some xT yT h_ns →
        yT = W.toAffine.negY xT yT →
        (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtPoint
            (Affine.Point.some xT yT h_ns)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          (-2 : ℤ)) :
    (⟨W.toAffine⟩ : SmoothPlaneCurve K).ordAtPoint T.val
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      (-2 : ℤ) := by
  rcases h_val_eq : T.val with _ | ⟨xT, yT, h_ns⟩
  · rw [SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty]
    exact ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq
  · by_cases h_2tor : yT = W.toAffine.negY xT yT
    · exact h_two_torsion_witness xT yT h_ns h_val_eq h_2tor
    · rw [SmoothPlaneCurve.ordAtPoint_some_eq_ord_P]
      exact lemma3_pole_at_T_unconditional W xT yT h_ns h_2tor hq

/-! ## #2 T-W2-DISCHARGE-FROM-PER-POINT-WITNESS

Sharper conditional: given that every K-rational projective point has
`projectiveDivisorOf γ.pullback x_gen` value ≠ 0 (which is per-point
W1 + lemma3 + ordAtInfty witness), conclude `support.card = pointCount`
via the `Fintype` instance + bijection shipped in #1
(`HasseWeil/Curves/PicZero.lean`).

The proof: if every `P : ProjectiveSmoothPoint` has value ≠ 0, then
`support = Finset.univ`, so `|support| = Fintype.card ProjectiveSmoothPoint
= Fintype.card W.toAffine.Point = pointCount`.

This is W2's substantive content reduced to the per-point pole-existence
witness; the latter follows from W1 (2-torsion case) + the shipped
lemma3 (non-2-torsion) + ordAtInfty witness. -/

/-- **#2 T-W2-DISCHARGE-FROM-PER-POINT-WITNESS**: support cardinality
discharge conditional on per-K-rational-point pole-existence. -/
theorem support_card_eq_pointCount_of_per_point_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    -- Per-point witness: every K-rational projective point has
    -- projectiveDivisorOf value ≠ 0. From W1 + lemma3 + ord_∞.
    (h_per_point_ne_zero :
      ∀ P : Curves.ProjectiveSmoothPoint
            (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K),
        (Curves.SmoothPlaneCurve.projectiveDivisorOf
            (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P ≠ 0) :
    (((Curves.SmoothPlaneCurve.projectiveDivisorOf
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support).card =
      pointCount W.toAffine := by
  have h_support_eq_univ :
      (Curves.SmoothPlaneCurve.projectiveDivisorOf
          (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))).support =
        (Finset.univ :
          Finset (Curves.ProjectiveSmoothPoint
            (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K))) :=
    Finset.eq_univ_of_forall fun P ↦ Finsupp.mem_support_iff.mpr (h_per_point_ne_zero P)
  rw [h_support_eq_univ, Finset.card_univ,
      Curves.ProjectiveSmoothPoint.card_eq_card_affine_point]
  rfl

/-! ## T5-T6 combined witness for `h_pole_orders`

Given T6, the `h_pole_orders` hypothesis of `lemma5_of_pole_orders_and_support_card`
becomes derivable: every point P in the support has
`(projectiveDivisorOf f) P = -2` (so `.toNat = 0` and `(-(.)).toNat = 2`).

This consumer combines T5 + T6 (via their witness-parametric closures)
to produce the input to Lemma 5. -/

/-- **T5-T6 combined: h_pole_orders derivation from T5 + T6 witnesses**:
given the support-card witness and the per-kernel-point ord = -2
witness, derive the `h_pole_orders` hypothesis of
`lemma5_of_pole_orders_and_support_card`. -/
theorem h_pole_orders_of_T5_T6_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_per_point_neg_two :
      ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
        ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P : ℤ) = -2) :
    ∀ P ∈ ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support,
      ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P).toNat = 0 ∧
      (-((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P)).toNat = 2 := by
  intro P hP
  rw [h_per_point_neg_two P hP]
  exact ⟨rfl, rfl⟩

/-! ## R25-B3-LOWER-WIRE — `finrank_pullback_fieldRange_field_eq_two`

R25h Phase 2 ticket T12. Discharges the LOWER step of the B3 tower:
`Module.finrank K⟮f⟯ γ.pullback.fieldRange = 2` for `f = γ.pullback x_gen`.

Witness-parametric on the substantive `letI Algebra → Module.Free`
typeclass synth wall + gammaBar transfer of the iso
`K⟮x_gen⟯ ≃ K⟮f⟯` (image of x_gen under the AlgEquiv
`K(E) ≃ₐ[K] γ.pullback.fieldRange`). -/

/-- **R25-B3-LOWER-WIRE (witness-parametric, `@`-explicit Module instance)**:
`Module.finrank K⟮f⟯ γ.pullback.fieldRange = 2` for `f = γ.pullback x_gen`,
given the substantive content as a single named hypothesis. -/
theorem finrank_pullback_fieldRange_field_eq_two_of_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    -- Inclusion (shipped at PoleDivisorFallback.lean:3273).
    (h_le : IntermediateField.adjoin K
              ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
                Set W.toAffine.FunctionField) ≤
            (isogOneSub_negFrobenius W hq).pullback.fieldRange)
    -- LOWER step witness (`@`-explicit Module instance avoids the letI synth
    -- wall documented in `feedback_isscalartower_letI_synth_wall`).
    (h_lower_witness :
      @Module.finrank
        ↥(IntermediateField.adjoin K
            ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
              Set W.toAffine.FunctionField))
        ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange
        _ _
        (IntermediateField.inclusion h_le).toAlgebra.toModule = 2) :
    @Module.finrank
      ↥(IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange
      _ _
      (IntermediateField.inclusion h_le).toAlgebra.toModule = 2 :=
  h_lower_witness

/-! ## R25-B3-LOWER unconditional (W5)

Ships the LOWER step of the B3 tower axiom-clean. Discharges the witness
hypothesis of `finrank_pullback_fieldRange_field_eq_two_of_witness` by
the gammaBar/e_f iso-pair transport of `finrank_functionField_eq_two`.

The proof strategy (mirrors the SEPARABILITY transport pattern at
`Hasse/PoleDivisorFallback.lean:3284-3391`):

1. The pullback range is K-iso to `K(E)` via
   `AlgEquiv.ofInjectiveField γ.pullback`.
2. `K⟮f⟯` is K-iso to `FractionRing (Polynomial K)` via
   `RatFunc.algEquivOfTranscendental f h_f` (whose K-iso sends
   `RatFunc.X` to `f`, hence the composite to `algebraMap X = X`).
3. The compatibility square: the inclusion `K⟮f⟯ ↪ γ.pullback.fieldRange`
   composed with `e_f` equals `gammaBar` composed with the algebraMap
   `FractionRing K[X] ↪ K(E)`. Checked on the generator `X`, where both
   sides reduce to `f`.
4. `Algebra.finrank_eq_of_equiv_equiv` (Mathlib) transfers the finrank
   identity through the iso pair given the compatibility square.
5. The starting point is `finrank_functionField_eq_two`
   (`HasseWeil/FrobeniusIsogeny.lean:196`):
   `Module.finrank (FractionRing K[X]) K(E) = 2`. -/

/-- **R25-B3-LOWER unconditional (W5)**: `Module.finrank K⟮f⟯
γ.pullback.fieldRange = 2` for `f = γ.pullback x_gen` axiom-clean, via the
gammaBar/e_f iso-pair transport of `finrank_functionField_eq_two`. -/
theorem finrank_pullback_fieldRange_field_eq_two_unconditional
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (h_f : Transcendental K ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (h_le : IntermediateField.adjoin K
              ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
                Set W.toAffine.FunctionField) ≤
            (isogOneSub_negFrobenius W hq).pullback.fieldRange) :
    @Module.finrank
      ↥(IntermediateField.adjoin K
          ({(isogOneSub_negFrobenius W hq).pullback (x_gen W)} :
            Set W.toAffine.FunctionField))
      ↥(isogOneSub_negFrobenius W hq).pullback.fieldRange
      _ _
      (IntermediateField.inclusion h_le).toAlgebra.toModule = 2 := by
  set γ := isogOneSub_negFrobenius W hq
  set f : W.toAffine.FunctionField := γ.pullback (x_gen W)
  -- The gammaBar iso K(E) ≃ₐ[K] γ.pullback.fieldRange.
  let gammaBar : W.toAffine.FunctionField ≃ₐ[K] ↥γ.pullback.fieldRange :=
    AlgEquiv.ofInjectiveField γ.pullback
  -- The e_f iso FractionRing K[X] ≃ₐ[K] K⟮f⟯ sending X to f.
  let e_f : FractionRing (Polynomial K) ≃ₐ[K]
            ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField)) :=
    (RatFunc.toFractionRingAlgEquiv K K).symm.trans
      (RatFunc.algEquivOfTranscendental (K := K) f h_f)
  -- Compatibility square: (inclusion K⟮f⟯ ↪ pullback.fieldRange) ∘ e_f
  --                     = gammaBar ∘ (algebraMap FractionRing K[X] → K(E))
  -- Check on the generator X (which e_f sends to f).
  -- Provide the algebra structure K⟮f⟯ → γ.pullback.fieldRange via inclusion.
  letI algKff : Algebra
      ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
      ↥γ.pullback.fieldRange :=
    (IntermediateField.inclusion h_le).toAlgebra
  have h_compat :
      (algebraMap
          ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
          ↥γ.pullback.fieldRange).comp e_f.toRingEquiv.toRingHom =
      gammaBar.toRingEquiv.toRingHom.comp
        (algebraMap (FractionRing (Polynomial K)) W.toAffine.FunctionField) := by
    -- Both sides are K[X]-algebra homs FractionRing K[X] → γ.pullback.fieldRange.
    -- It suffices to check equality on the X generator.
    apply RingHom.ext
    intro r
    -- We will show equality at the level of underlying values in K(E).
    -- Both sides, applied to r, give elements of γ.pullback.fieldRange (a
    -- subtype of K(E)). The Subtype.ext path is via .val.
    let lhs_alg : FractionRing (Polynomial K) →ₐ[K] ↥γ.pullback.fieldRange :=
      (IntermediateField.inclusion h_le).comp e_f.toAlgHom
    let rhs_alg : FractionRing (Polynomial K) →ₐ[K] ↥γ.pullback.fieldRange :=
      gammaBar.toAlgHom.comp
        (IsScalarTower.toAlgHom K (FractionRing (Polynomial K))
          W.toAffine.FunctionField)
    have h_eq : lhs_alg = rhs_alg := by
      apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
      apply Polynomial.algHom_ext
      apply Subtype.ext
      -- Both sides applied to X reduce to f in K(E).
      change ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
          Polynomial.X)) : W.toAffine.FunctionField) =
        ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
          Polynomial.X)) : W.toAffine.FunctionField)
      have h_LHS :
          ((lhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)) : W.toAffine.FunctionField) = f := by
        change ((IntermediateField.inclusion h_le)
            (e_f (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X)) : W.toAffine.FunctionField) = f
        rw [IntermediateField.coe_inclusion]
        change (((RatFunc.toFractionRingAlgEquiv K K).symm.trans
            (RatFunc.algEquivOfTranscendental (K := K) f h_f))
            (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X)).val = f
        rw [AlgEquiv.trans_apply]
        have h_e3_symm_X :
            (RatFunc.toFractionRingAlgEquiv K K).symm
              (algebraMap (Polynomial K) (FractionRing (Polynomial K))
                Polynomial.X) = (RatFunc.X : RatFunc K) := by
          have h_e3_X :
              RatFunc.toFractionRingAlgEquiv K K (RatFunc.X : RatFunc K) =
              algebraMap (Polynomial K) (FractionRing (Polynomial K))
                Polynomial.X := by
            show (RatFunc.toFractionRingAlgEquiv K K) RatFunc.X = _
            simp only [RatFunc.toFractionRingAlgEquiv_apply]
            change ((algebraMap (Polynomial K) (RatFunc K)) Polynomial.X).toFractionRing = _
            rw [← RatFunc.ofFractionRing_algebraMap (K := K)]
          rw [← h_e3_X, AlgEquiv.symm_apply_apply]
        rw [h_e3_symm_X]
        change ((RatFunc.algEquivOfTranscendental (K := K) f h_f)
            (RatFunc.X : RatFunc K)).val = f
        rw [RatFunc.algEquivOfTranscendental_X]
      have h_RHS :
          ((rhs_alg (algebraMap (Polynomial K) (FractionRing (Polynomial K))
            Polynomial.X)) : W.toAffine.FunctionField) = f := by
        change ((gammaBar (algebraMap (FractionRing (Polynomial K))
            W.toAffine.FunctionField
            (algebraMap (Polynomial K) (FractionRing (Polynomial K))
              Polynomial.X))) : W.toAffine.FunctionField) = f
        rw [← IsScalarTower.algebraMap_apply (Polynomial K)
          (FractionRing (Polynomial K)) W.toAffine.FunctionField]
        rfl
      rw [h_LHS, h_RHS]
    exact DFunLike.congr_fun h_eq r
  -- Apply `Algebra.finrank_eq_of_equiv_equiv` to transport
  -- `finrank_functionField_eq_two` through the (e_f, gammaBar) iso pair.
  have h_fin :
      Module.finrank (FractionRing (Polynomial K)) W.toAffine.FunctionField =
      @Module.finrank
        ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
        ↥γ.pullback.fieldRange _ _
        (IntermediateField.inclusion h_le).toAlgebra.toModule :=
    @Algebra.finrank_eq_of_equiv_equiv
      (FractionRing (Polynomial K)) W.toAffine.FunctionField _ _ _
      ↥(IntermediateField.adjoin K ({f} : Set W.toAffine.FunctionField))
      ↥γ.pullback.fieldRange _ _
      (IntermediateField.inclusion h_le).toAlgebra
      e_f.toRingEquiv gammaBar.toRingEquiv h_compat
  rw [← h_fin, finrank_functionField_eq_two]

/-! ## T22 substantive — support card = pointCount with 2-torsion as the
    single remaining substantive obligation

Real composition of the shipped per-point-ne-zero consumer with the per-
projective-point case analysis:

* `.infinity` branch: discharged axiom-clean via shipped
  `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen = -2`.
* `.affine ⟨xT, yT, h_ns⟩` branch: every K-rational affine point lies in
  `ker γ` (since `π` fixes K-rational points and `γ = id − π`); apply
  `ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness`, which itself
  splits into the non-2-torsion case (shipped axiom-clean via
  `lemma3_pole_at_T_unconditional`) and the 2-torsion case (factored as
  the witness hypothesis `h_2_tor`).

This isolates the 2-torsion ord at every K-rational 2-torsion point as the
single remaining substantive Worker B obligation for the L6 chain's T22
discharge. The composition is REAL (not a literal `_of_witness` wrapper):
the body discharges two of the three projective-point cases axiom-clean. -/

/-- **T22 substantive composition (2-torsion ord as single witness)**:
`|support (projectiveDivisorOf (γ.pullback x_gen))| = pointCount W.toAffine`. -/
theorem support_card_eq_pointCount_of_two_torsion_ord_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_2_tor :
      ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        yT = W.toAffine.negY xT yT →
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint
            (Affine.Point.some xT yT h_ns)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          ((-2 : ℤ) : WithTop ℤ)) :
    (((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support).card =
      pointCount W.toAffine := by
  refine support_card_eq_pointCount_of_per_point_witness W hq ?_
  intro P
  cases P with
  | infinity =>
    have h_inf : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtInfty
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) :=
      ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq
    rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity, h_inf]
    decide
  | affine Q =>
    rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine]
    obtain ⟨xT, yT, h_ns⟩ := Q
    have hP_kernel : Affine.Point.some xT yT h_ns ∈
        (isogOneSub_negFrobenius W hq).kernel := by
      change (isogOneSub_negFrobenius W hq).toAddMonoidHom
        (Affine.Point.some xT yT h_ns) = 0
      rw [isogOneSub_negFrobenius_toAddMonoidHom, AddMonoidHom.sub_apply,
        AddMonoidHom.id_apply]
      change (Affine.Point.some xT yT h_ns) - (Affine.Point.some xT yT h_ns) = 0
      exact sub_self _
    have h_ord : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint
        (Affine.Point.some xT yT h_ns)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) :=
      ord_kernel_pullback_x_eq_neg_two_of_two_torsion_witness W hq
        ⟨Affine.Point.some xT yT h_ns, hP_kernel⟩
        (fun xT' yT' h_ns' _ h_2tor ↦
          h_2_tor xT' yT' h_ns' h_2tor)
    rw [← Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P, h_ord]
    decide

/-! ## Witness-parametric L3 + L4 closures from a single 2-torsion witness

The two consumer lemmas above (`support_card_eq_pointCount_of_per_point_witness` for L4 and
`h_pole_orders_of_T5_T6_witnesses` for L3) each take a per-point hypothesis. The pointwise
helper below derives that hypothesis from a single 2-torsion witness: at every K-rational
projective smooth point P, the divisor value is exactly `-2` (as ℤ), by case-splitting on
P = ∞ (uses `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen`), P = affine non-2-torsion
(uses `lemma3_pole_at_T_unconditional`), and P = affine 2-torsion (uses the witness).

These three closures together reduce L3 + L4 to the single substantive 2-torsion-witness
sub-leaf (the addition-formula degeneracy at 2-torsion). -/

/-- **Pointwise: divisor value = -2 at every K-rational projective point** given the
2-torsion witness. -/
theorem projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (h_two_torsion_witness : ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        yT = W.toAffine.negY xT yT →
        (W_smooth W).ord_P ⟨xT, yT, h_ns⟩
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          ((-2 : ℤ) : WithTop ℤ))
    (P : Curves.ProjectiveSmoothPoint (W_smooth W)) :
    (Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P = -2 := by
  rcases P with ⟨xT, yT, h_ns⟩ | _
  · rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_affine]
    by_cases h_2tor : yT = W.toAffine.negY xT yT
    · rw [h_two_torsion_witness xT yT h_ns h_2tor]; rfl
    · rw [lemma3_pole_at_T_unconditional W xT yT h_ns h_2tor hq]; rfl
  · rw [Curves.SmoothPlaneCurve.projectiveDivisorOf_apply_infinity,
        ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen W hq]; rfl

/-- **L4 witness-parametric** (Silverman V.1.1 support cardinality, single 2-torsion witness):
the pole-divisor support has cardinality `pointCount`. -/
theorem l6_support_card_of_two_torsion_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_two_torsion_witness : ∀ (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT),
        yT = W.toAffine.negY xT yT →
        (W_smooth W).ord_P ⟨xT, yT, h_ns⟩
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
          ((-2 : ℤ) : WithTop ℤ)) :
    ((Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).support.card =
      pointCount W.toAffine :=
  support_card_eq_pointCount_of_per_point_witness W hq
    (fun P ↦ by
      change (Curves.SmoothPlaneCurve.projectiveDivisorOf (W_smooth W)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) P ≠ 0
      rw [projectiveDivisorOf_pullback_x_gen_eq_neg_two_of_two_torsion_witness
            W hq h_two_torsion_witness P]
      decide)

end Conditional

/-! ### F.1 dispatch (downstream of L6Witnesses)

The former upstream `bridge_Bi_kernelToPrime` sorry (`OpenLemmas.lean`; deleted
2026-06-11) was identified by `/develop --decompose v3` as DISPATCHABLE via the order-based v2 construction using
`ordAtPoint`, except that the required `Sinf_ord_nonneg_at_kernel_point_unconditional`
lives DOWNSTREAM of OpenLemmas.

The discharge below provides the axiom-clean order-based ideal as a **downstream** def
(in L6Witnesses, downstream of OpenLemmas), suitable for retargeting consumers that
want the genuine F.1 content. The OpenLemmas-side sorry remains pending architectural
restructure.

Composes 4 shipped axiom-clean ingredients:
- `ordAtPoint_zero_function` (zero_mem)
- `ordAtPoint_add_le` (add_mem)
- `ordAtPoint_mul` + `Sinf_ord_nonneg_at_kernel_point_unconditional` (smul_mem)
-/

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **General field-valuation helper (axiom-clean).** Two surjective
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`-valued valuations on a field that are
`Valuation.IsEquiv` are in fact *equal* (value-precise, not just equivalent). -/
theorem Valuation.isEquiv_iff_eq_of_surjective_withZeroInt
    {F : Type*} [Field F] (v w : Valuation F (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) :
    v = w := by
  obtain ⟨e, he⟩ := hv (WithZero.exp 1)
  have hvpow : ∀ k : ℤ, v (e ^ k) = WithZero.exp k := by
    intro k; rw [map_zpow₀, he, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  have hwe0 : w e ≠ 0 :=
    (h.eq_zero).ne.mp (by rw [he]; exact WithZero.exp_ne_zero)
  have key : ∀ x : F, v x ≠ 0 → w x = (w e) ^ (WithZero.log (v x)) := by
    intro x hx
    set m := WithZero.log (v x) with hm
    have hvu : v (x * e ^ (-m)) = 1 := by
      rw [map_mul, hvpow (-m), ← WithZero.exp_log hx, ← hm, ← WithZero.exp_add,
        add_neg_cancel, WithZero.exp_zero]
    have hwu : w (x * e ^ (-m)) = 1 := (h.eq_one_iff_eq_one).mp hvu
    rwa [map_mul, map_zpow₀, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hwe0)] at hwu
  have h1we : (1 : WithZero (Multiplicative ℤ)) < w e := by
    rw [← h.one_lt_iff_one_lt, he, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hc_pos : 0 < WithZero.log (w e) :=
    (WithZero.lt_log_iff_exp_lt hwe0).mpr (by rwa [WithZero.exp_zero])
  obtain ⟨x₁, hx₁⟩ := hw (WithZero.exp 1)
  have hvx₁ : v x₁ ≠ 0 :=
    (h.eq_zero).ne.mpr (by rw [hx₁]; exact WithZero.exp_ne_zero)
  have hk := key x₁ hvx₁
  rw [hx₁] at hk
  have hlog : (1 : ℤ) = WithZero.log (v x₁) * WithZero.log (w e) := by
    have h2 := congrArg WithZero.log hk
    rwa [WithZero.log_exp, WithZero.log_zpow, smul_eq_mul] at h2
  have hc1 : WithZero.log (w e) = 1 := by
    have hdvd : WithZero.log (w e) ∣ 1 := ⟨_, by rw [hlog]; ring⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with hh | hh
    · exact hh
    · omega
  ext x
  rcases eq_or_ne (v x) 0 with hx0 | hx0
  · rw [hx0, (h.eq_zero).mp hx0]
  · rw [key x hx0, ← WithZero.exp_log hwe0, hc1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one,
      WithZero.exp_log hx0]

/-- **General valuation-subring maximality glue (axiom-clean).** If the valuation
subring of `v` dominates into the valuation subring of `w` (`O_v ≤ O_w` in the
`LocalSubring` domination order), then `v.IsEquiv w`. -/
theorem Valuation.isEquiv_of_valuationSubring_le
    {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v w : Valuation F Γ₀)
    (hle : v.valuationSubring.toLocalSubring ≤ w.valuationSubring.toLocalSubring) :
    v.IsEquiv w := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  exact ValuationSubring.toLocalSubring_injective
    (v.valuationSubring.isMax_toLocalSubring.eq_of_le hle)

/-- **F.1 downstream dispatch**: the order-based ideal
`P_T = {a ∈ data.carrier | ord_T(algebraMap a) > 0}`, for a kernel point `T`. -/
noncomputable def bridge_Bi_kernelToPrime_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    Ideal data.carrier := by
  letI := data.commRing
  letI := data.algLinfAt
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  refine
    { carrier := { a : data.carrier | (0 : WithTop ℤ) <
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L a) }
      add_mem' := ?_
      zero_mem' := ?_
      smul_mem' := ?_ }
  · intro a b ha hb
    change (0 : WithTop ℤ) <
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (a + b))
    rw [map_add]
    exact lt_of_lt_of_le (lt_min ha hb)
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_add_le T.val
        (algebraMap data.carrier L a) (algebraMap data.carrier L b))
  · change (0 : WithTop ℤ) <
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (0 : data.carrier))
    rw [map_zero]
    have h_zero : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (0 : L) = ⊤ :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_zero_function T.val
    rw [h_zero]
    exact WithTop.top_pos
  · intro r a ha
    change (0 : WithTop ℤ) <
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (r • a))
    rw [smul_eq_mul (α := data.carrier), map_mul]
    have h_mul : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        ((algebraMap data.carrier L r) * (algebraMap data.carrier L a)) =
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (algebraMap data.carrier L r) +
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (algebraMap data.carrier L a) :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val _ _
    rw [h_mul]
    calc (0 : WithTop ℤ) < _ := ha
      _ ≤ _ := le_add_of_nonneg_left
        (Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T r)

/-- **F.1 companion downstream**: the v2 ideal is prime.

Composes:
- `ordAtPoint_mul` for the multiplicative property of ord
- `Sinf_ord_nonneg_at_kernel_point_unconditional` for ord ≥ 0 on data.carrier
- The valuation-ring prime characterization: {a : v(a) > 0} is prime iff v is non-trivial. -/
theorem bridge_Bi_isPrime_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    (bridge_Bi_kernelToPrime_v2 W hq data T).IsPrime := by
  letI := data.commRing
  letI := data.algLinfAt
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    change ¬ ((0 : WithTop ℤ) <
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (1 : data.carrier)))
    rw [map_one]
    have h_one : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (1 : L) = 0 :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_one T.val
    rw [h_one]
    exact lt_irrefl 0
  · intro x y hxy
    have hxy' : (0 : WithTop ℤ) <
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L (x * y)) := hxy
    rw [map_mul] at hxy'
    -- explicit `have` dodges the letI-instance rewrite snag
    have h_mul : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        ((algebraMap data.carrier L x) * (algebraMap data.carrier L y)) =
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (algebraMap data.carrier L x) +
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (algebraMap data.carrier L y) :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val _ _
    rw [h_mul] at hxy'
    have hA : (0 : WithTop ℤ) ≤
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val (algebraMap data.carrier L x) :=
      Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T x
    rcases lt_or_eq_of_le hA with h | h
    · exact Or.inl h
    · rw [← h, zero_add] at hxy'
      exact Or.inr hxy'

/-- **F.1 companion downstream**: the v2 ideal lies over `xIdeal := (X) ⊂ Polynomial K`.

Same content as the former OpenLemmas `bridge_Bi_liesOver` (an upstream sorry,
deleted 2026-06-11), but built here where the required `ord_T((γ.pullback
x_gen)⁻¹) = 2` (`inv_gamma_pullback_x_pos_at_kernel`) and `ord ≥ 0`
(`Sinf_ord_nonneg_at_kernel_point_unconditional`) are available axiom-clean.

`P.LiesOver xIdeal` unfolds to `xIdeal = P.comap (algebraMap (Polynomial K)
data.carrier)`. Via the scalar tower `data.isScalarTower` and
`polyToFieldOfInv (X ↦ f⁻¹)`, membership of `p : Polynomial K` in the comap is
`0 < ord_T (aeval f⁻¹ p)`. Since `ord_T(f⁻¹) = 2 > 0`:
* `X ∣ p` (i.e. `p ∈ (X)`) ⟹ `aeval f⁻¹ p = f⁻¹ * aeval f⁻¹ q`, order `≥ 2 > 0`;
* `X ∤ p` ⟹ `p.coeff 0 ≠ 0`, `aeval f⁻¹ p = algebraMap K c + f⁻¹ * (…)` with the
  constant term of order `0 <` the rest, so the strict non-archimedean min gives
  order `0`, hence not `> 0`. -/
theorem bridge_Bi_liesOver_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.algPoly
    (bridge_Bi_kernelToPrime_v2 W hq data T).LiesOver
      (Curves.RamificationAtInfinity.xIdeal (k := K)) := by
  letI := data.commRing
  letI := data.algLinfAt
  letI := data.algPoly
  letI := data.isScalarTower
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) with hL
  -- `LiesOver` ⇔ `xIdeal = comap`.  `Ideal.under = Ideal.comap (algebraMap …)`.
  refine ⟨?_⟩
  -- Goal: `xIdeal = (P_T).under (Polynomial K) = (P_T).comap (algebraMap …)`.
  apply Ideal.ext
  intro p
  -- `mem_comap`: `p ∈ comap ↔ algebraMap (Polynomial K) carrier p ∈ P_T`.
  rw [Ideal.mem_comap]
  -- `algebraMap (Polynomial K) carrier p ∈ P_T` ⇔ `0 < ord_T (algebraMap carrier L …)`.
  change p ∈ Curves.RamificationAtInfinity.xIdeal (k := K) ↔
    (0 : WithTop ℤ) <
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L
          (algebraMap (Polynomial K) data.carrier p))
  -- Scalar-tower collapse: outer ∘ inner algebraMap = algebraMap (Poly K) L =
  -- polyToFieldOfInv f = aeval f⁻¹.
  have h_tower : algebraMap data.carrier L
      (algebraMap (Polynomial K) data.carrier p) =
      Polynomial.aeval
        (((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ :
          W.toAffine.FunctionField) p := by
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) data.carrier L p]
    rw [Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply]
    rfl
  rw [h_tower]
  -- Notation: `g := f⁻¹` and `ord_T(g) = 2`.
  set g : W.toAffine.FunctionField :=
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ with hg
  have h_ord_g : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val g
      = (2 : WithTop ℤ) :=
    Conditional.inv_gamma_pullback_x_pos_at_kernel W hq T
  -- For any polynomial `q`, `aeval g q` lies in the carrier image, so `ord ≥ 0`.
  have h_aeval_nonneg : ∀ q : Polynomial K,
      (0 : WithTop ℤ) ≤
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (Polynomial.aeval g q) := by
    intro q
    have h_tower_q : Polynomial.aeval g q =
        algebraMap data.carrier L
          (algebraMap (Polynomial K) data.carrier q) := by
      rw [← IsScalarTower.algebraMap_apply (Polynomial K) data.carrier L q,
        Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply]
      rfl
    rw [h_tower_q]
    exact Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T _
  -- `p ∈ xIdeal = span {X}` ⇔ `X ∣ p`.
  rw [Curves.RamificationAtInfinity.xIdeal, Ideal.mem_span_singleton]
  constructor
  · -- Forward: `X ∣ p ⟹ 0 < ord_T (aeval g p)`.
    rintro ⟨q, rfl⟩
    -- `aeval g (X * q) = g * aeval g q`, so `ord = ord g + ord (aeval g q) = 2 + (≥0)`.
    rw [map_mul, Polynomial.aeval_X,
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val g
        (Polynomial.aeval g q), h_ord_g]
    exact add_pos_of_pos_of_nonneg (by decide) (h_aeval_nonneg q)
  · -- Converse, by contraposition: `¬(X ∣ p) ⟹ ord_T (aeval g p) = 0`, hence not `> 0`.
    rw [← not_imp_not]
    intro h_ndvd
    -- `¬ X ∣ p` ⇔ `p.coeff 0 ≠ 0`.
    rw [Polynomial.X_dvd_iff] at h_ndvd
    -- Split off the constant term: `p = C (p.coeff 0) + X * q`.
    have h_dvd_sub : Polynomial.X ∣ (p - Polynomial.C (p.coeff 0)) := by
      rw [Polynomial.X_dvd_iff]
      simp [Polynomial.coeff_sub]
    obtain ⟨q, hq⟩ := h_dvd_sub
    have h_decomp : p = Polynomial.C (p.coeff 0) + Polynomial.X * q := by
      rw [← hq]; ring
    -- `aeval g p = algebraMap K _ (p.coeff 0) + g * aeval g q`.
    rw [h_decomp, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    -- `ord(constant) = 0`; `ord(g * aeval g q) = 2 + (≥0) ≥ 2 > 0`.
    have h_ord_const :
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap K W.toAffine.FunctionField (p.coeff 0)) = 0 :=
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_algebraMap_F_of_ne_zero
        T.val h_ndvd
    have h_ord_rest :
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (g * Polynomial.aeval g q) =
        (2 : WithTop ℤ) +
          (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
            (Polynomial.aeval g q) := by
      rw [(⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val g
        (Polynomial.aeval g q), h_ord_g]
    -- `ord(const) = 0 < 2 ≤ ord(rest)`, so the strict non-archimedean min gives
    -- `ord(const + rest) = ord(const) = 0`.
    have h_lt :
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap K W.toAffine.FunctionField (p.coeff 0)) <
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (g * Polynomial.aeval g q) := by
      rw [h_ord_const, h_ord_rest]
      exact add_pos_of_pos_of_nonneg (by decide) (h_aeval_nonneg q)
    rw [(⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_add_eq_of_lt T.val h_lt,
      h_ord_const]
    -- Goal: `¬ (0 < 0)`.
    exact lt_irrefl 0

/-- **F.1 substrate (SHIPPABLE direction): membership in `P_T^n` forces
`ord_T ≥ n`.** For the order-based kernel prime
`P_T := bridge_Bi_kernelToPrime_v2 W hq data T`, an element of `P_T^n` has
curve-order at least `n` at `T`: `a ∈ P_T^n → (n : WithTop ℤ) ≤ ord_T(algebraMap a)`. -/
theorem Sinf_kernelPrime_pow_le_ord
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (n : ℕ) (a : data.carrier)
    (ha : a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T) ^ n) :
    letI := data.commRing
    letI := data.algLinfAt
    (n : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier
          (Curves.RamificationAtInfinity.LinfAt (k := K)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) := by
  letI := data.commRing
  letI := data.algLinfAt
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simpa only [Nat.cast_zero, Algebra.algebraMap_self_apply] using
      Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T r
  | add x y i _ _ hx hy =>
    have h_add : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (x + y)) =
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L x + algebraMap data.carrier L y) :=
      congrArg _ (map_add _ x y)
    rw [h_add]
    exact (le_min hx hy).trans
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_add_le T.val
        (algebraMap data.carrier L x) (algebraMap data.carrier L y))
  | mem_mul m hm i x _ hx =>
    have h_mul : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
        (algebraMap data.carrier L (m * x)) =
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L m) +
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L x) :=
      (congrArg _ (map_mul _ m x)).trans
        ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val
          (algebraMap data.carrier L m) (algebraMap data.carrier L x))
    rw [h_mul]
    -- `hm : 0 < ord_T(algebraMap m)`; on `WithTop ℤ`, `0 < v → 1 ≤ v`.
    have hWithTop : ∀ v : WithTop ℤ, (0 : WithTop ℤ) < v → (1 : WithTop ℤ) ≤ v := by
      intro v hv
      induction v using WithTop.recTopCoe with
      | top => exact le_top
      | coe z => norm_cast at hv ⊢
    have hm1 : (1 : WithTop ℤ) ≤
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier L m) := hWithTop _ hm
    rw [Nat.cast_succ, add_comm]
    exact add_le_add hm1 hx

/-- **F.1 infrastructure: the order-based kernel prime is nonzero (`≠ ⊥`).**

The order-based kernel prime `bridge_Bi_kernelToPrime_v2 W hq data T` is a nonzero
ideal of the carrier. -/
theorem Sinf_kernelPrime_ne_bot
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    bridge_Bi_kernelToPrime_v2 W hq data T ≠ ⊥ := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.algLinfAt
  letI := data.isScalarTower
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) with hL
  -- `xc := algebraMap (Polynomial K) carrier X`; its image in `L` is `f⁻¹`.
  set xc : data.carrier := algebraMap (Polynomial K) data.carrier Polynomial.X with hxc
  -- The image of `xc` in `L` is `f⁻¹` (scalar-tower collapse).
  have h_tower : algebraMap data.carrier L xc =
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ := by
    rw [hxc, ← IsScalarTower.algebraMap_apply (Polynomial K) data.carrier L Polynomial.X,
      Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply,
      Curves.RamificationAtInfinity.polyToFieldOfInv_X]
  -- `ord_T(image xc) = 2`.
  have h_ord_xc : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
      (algebraMap data.carrier L xc) = (2 : WithTop ℤ) := by
    rw [h_tower]; exact Conditional.inv_gamma_pullback_x_pos_at_kernel W hq T
  have h_mem : xc ∈ bridge_Bi_kernelToPrime_v2 W hq data T := by
    change (0 : WithTop ℤ) < (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
      (algebraMap data.carrier L xc)
    simp [h_ord_xc]
  -- `xc ≠ 0`: if `xc = 0` its image has `ord_T = ⊤`, contradicting `ord_T = 2`.
  have h_xc_ne : xc ≠ 0 := fun h0 =>
    WithTop.coe_ne_top <| h_ord_xc.symm.trans <| by
      rw [h0, map_zero]
      exact (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_zero_function T.val
  -- A nonzero element of `P_T` witnesses `P_T ≠ ⊥`.
  exact (Submodule.ne_bot_iff _).2 ⟨xc, h_mem, h_xc_ne⟩

/-- The order-based kernel prime `P_T`, packaged as an element of the height-one
spectrum `IsDedekindDomain.HeightOneSpectrum data.carrier` of the carrier. -/
noncomputable def Sinf_kernelPrime_heightOne
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    IsDedekindDomain.HeightOneSpectrum data.carrier :=
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  { asIdeal := bridge_Bi_kernelToPrime_v2 W hq data T
    isPrime := bridge_Bi_isPrime_v2 W hq data T
    ne_bot := Sinf_kernelPrime_ne_bot W hq data T }

/-- **Curve-side value form (axiom-clean helper).** For a finite smooth point `P`
and a nonzero function `f` whose additive order is the integer `n`
(`ord_P P f = (n : WithTop ℤ)`), the `pointValuation` is the exponential of the
negated order: `pointValuation P f = WithZero.exp (-n)`. -/
theorem Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq
    {F : Type*} [Field F] {C : Curves.SmoothPlaneCurve F} {P : C.SmoothPoint}
    {f : C.FunctionField} {n : ℤ} (hf : f ≠ 0)
    (hn : C.ord_P P f = (n : WithTop ℤ)) :
    C.pointValuation P f = WithZero.exp (-n) := by
  have hv : C.pointValuation P f ≠ 0 := (C.pointValuation P).ne_zero_iff.mpr hf
  have hord : C.ord_P P f = ((-(WithZero.unzero hv).toAdd : ℤ) : WithTop ℤ) := by
    rw [Curves.SmoothPlaneCurve.ord_P, dif_neg hv]
  have hneq : n = -(WithZero.unzero hv).toAdd := mod_cast hn.symm.trans hord
  rw [hneq, neg_neg, WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]

/-- **Curve-side surjectivity (axiom-clean helper).** The `pointValuation` at a
finite smooth point `P` is surjective onto `ℤᵐ⁰`. -/
theorem Curves.SmoothPlaneCurve.pointValuation_surjective
    {F : Type*} [Field F] (C : Curves.SmoothPlaneCurve F) (P : C.SmoothPoint) :
    Function.Surjective (C.pointValuation P) := by
  obtain ⟨t, ht⟩ := C.exists_uniformizer P
  rw [Curves.SmoothPlaneCurve.Uniformizer] at ht
  have ht_ne : t ≠ 0 := by
    intro h; rw [h, Curves.SmoothPlaneCurve.ord_P_zero] at ht; exact WithTop.top_ne_one ht
  have hvt : C.pointValuation P t = WithZero.exp (-1 : ℤ) :=
    Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq ht_ne ht
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  · refine ⟨t ^ (-(WithZero.log z)), ?_⟩
    rw [map_zpow₀, hvt, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
      WithZero.exp_log hz]

/-- **Carrier-side surjectivity (axiom-clean helper).** The height-one adic valuation
`(Sinf_kernelPrime_heightOne …).valuation` on the fraction field `L` is surjective
onto `ℤᵐ⁰`. The adic valuation always admits a uniformizer realising `ofAdd (-1)`
(`valuation_exists_uniformizer`), and the value group is `ℤ`. -/
theorem Sinf_kernelPrime_valuation_surjective
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algLinfAt
    letI := data.isFractionRing
    Function.Surjective
      ((Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  obtain ⟨π, hπ⟩ := (Sinf_kernelPrime_heightOne W hq data T).valuation_exists_uniformizer L
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  · refine ⟨π ^ (-(WithZero.log z)), ?_⟩
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
      WithZero.exp_log hz]

/-- **F.1 ABSTRACT CRUX (mathlib-shaped reusable reduction) — rank-one overring is
self-or-top.**

For a valuation subring `A` of a field `L` that is a discrete valuation ring (rank one),
any larger valuation subring `B ≥ A` with `B ≠ ⊤` must equal `A`. -/
theorem rankOne_valuationSubring_le_eq_of_ne_top {L : Type*} [Field L]
    (A B : ValuationSubring L) [IsDiscreteValuationRing A]
    (hAB : A ≤ B) (hB : B ≠ ⊤) : A = B := by
  classical
  have hPprime : (A.idealOfLE B hAB).IsPrime := ValuationSubring.prime_idealOfLE A B hAB
  -- Equal primes give equal overrings, routed through `primeSpectrumEquiv` (which bundles
  -- the `IsPrime` instance) to dodge the instance-dependent-motive wall in `ofPrime`.
  have transport : ∀ (C : ValuationSubring L) (hC : A ≤ C),
      A.idealOfLE B hAB = A.idealOfLE C hC → B = C := by
    intro C hC hEq
    have hPS : (⟨A.idealOfLE B hAB, hPprime⟩ : PrimeSpectrum A)
        = ⟨A.idealOfLE C hC, ValuationSubring.prime_idealOfLE A C hC⟩ :=
      PrimeSpectrum.ext hEq
    have hval := congrArg (fun P ↦ ((ValuationSubring.primeSpectrumEquiv A) P).1) hPS
    simpa only [ValuationSubring.primeSpectrumEquiv_apply, ValuationSubring.ofPrime_idealOfLE]
      using hval
  rcases eq_or_ne (A.idealOfLE B hAB) ⊥ with hbot | hne
  · -- Bottom prime `⊥`: would force `B = ⊤`, contradicting `hB`.
    refine absurd (transport ⊤ le_top ?_) hB
    rw [hbot, ValuationSubring.idealOfLE, IsLocalRing.maximalIdeal_eq_bot]
    refine (Ideal.comap_bot_of_injective (ValuationSubring.inclusion A ⊤ le_top) ?_).symm
    intro a b hab
    have hab' := congrArg (Subtype.val (p := (· ∈ (⊤ : ValuationSubring L)))) hab
    rw [ValuationSubring.inclusion, Subring.coe_inclusion, Subring.coe_inclusion] at hab'
    exact Subtype.ext hab'
  · -- Nonzero prime: maximal in the dimension-≤-1 ring `A`, hence `= maximalIdeal A`.
    have hmax : (A.idealOfLE B hAB).IsMaximal := hPprime.isMaximal hne
    refine (transport A le_rfl ?_).symm
    rw [IsLocalRing.eq_maximalIdeal hmax, ValuationSubring.idealOfLE]
    ext x
    rw [Ideal.mem_comap, show (ValuationSubring.inclusion A A le_rfl) x = x from rfl]

/-- **F.1 wiring helper — the carrier adic-valuation subring is a DVR.**

The valuation subring of the height-one adic valuation `(Sinf_kernelPrime_heightOne …).valuation L`
on the fraction field `L` is a discrete valuation ring. This is the rank-one / DVR
instance demanded by `rankOne_valuationSubring_le_eq_of_ne_top`. It follows from
`Valuation.valuationSubring_isDiscreteValuationRing`, whose two side instances
(`IsCyclic (valueGroup v)`, `Nontrivial (valueGroup v)`) are supplied here from the
shipped surjectivity `Sinf_kernelPrime_valuation_surjective` (surjective onto `ℤᵐ⁰`,
whence `valueGroup v = ⊤ ≃* (ℤᵐ⁰)ˣ ≃* Multiplicative ℤ`, cyclic and nontrivial). -/
theorem Sinf_kernelPrime_valuationSubring_isDVR
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algLinfAt
    letI := data.isFractionRing
    IsDiscreteValuationRing
      (((Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).valuationSubring) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set v := (Sinf_kernelPrime_heightOne W hq data T).valuation L
  have hsurj : Function.Surjective v := Sinf_kernelPrime_valuation_surjective W hq data T
  have hvg : MonoidWithZeroHom.valueGroup (.ofClass v) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
    refine ⟨1, by simp, ?_⟩
    obtain ⟨x, hx⟩ := hsurj (y : WithZero (Multiplicative ℤ))
    exact ⟨x, by rw [map_one, one_mul]; exact hx.symm⟩
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm.toMonoidHom
      WithZero.unitsWithZeroEquiv.symm.surjective
  haveI : Nontrivial (WithZero (Multiplicative ℤ))ˣ :=
    WithZero.unitsWithZeroEquiv.symm.toEquiv.nontrivial
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass v)) :=
    hvg ▸ isCyclic_of_surjective Subgroup.topEquiv.symm.toMonoidHom
      Subgroup.topEquiv.symm.surjective
  haveI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) :=
    hvg ▸ Subgroup.topEquiv.symm.toEquiv.nontrivial
  exact Valuation.valuationSubring_isDiscreteValuationRing v

/-- **F.1 field-level forward half (named residual).** For any `x` in the function field
`L`, if the carrier `P_T`-adic valuation is `≤ 1` (i.e. `x` is `P_T`-integral) then the
curve order at the kernel point is nonnegative: `ord_T(x) ≥ 0`. -/
theorem Sinf_ordAtPoint_nonneg_of_valuation_le_one
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (x : Curves.RamificationAtInfinity.LinfAt (k := K)
      ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))
    (hx : letI := data.commRing
      letI := data.isDomain
      letI := data.isDedekindDomain
      letI := data.algLinfAt
      letI := data.isFractionRing
      (Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) x ≤ 1) :
    letI := data.commRing
    letI := data.algLinfAt
    (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val x := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
      (Sinf_kernelPrime_heightOne W hq data T) x hx
  -- `.trans` matches the middle `ord_T(x * algebraMap d)` up to defeq, sidestepping the
  -- syntactic `Mul`-instance mismatch between `LinfAt` and `C.FunctionField`.
  have hord :
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val x +
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) (d : data.carrier))
      = (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
            ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) n) :=
    ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_mul T.val x
      (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) (d : data.carrier))).symm.trans
      (congrArg ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val) hnd)
  have hn_nonneg :=
    Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T n
  have hd_nonneg :=
    Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T (d : data.carrier)
  -- `d.prop : (d : carrier) ∉ asIdeal`, defeq to `¬ (0 < ord_T(algebraMap d))`.
  have hd_le : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
      (algebraMap data.carrier (Curves.RamificationAtInfinity.LinfAt (k := K)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) (d : data.carrier)) ≤ 0 :=
    not_lt.mp d.prop
  have hd_zero := le_antisymm hd_le hd_nonneg
  rw [hd_zero, add_zero] at hord
  exact hord ▸ hn_nonneg

/-- **F.1 wiring helper — the valuation-subring INCLUSION `A ≤ B`.**

The underlying-subring (SetLike) inclusion of the carrier `P_T`-adic valuation subring
into the curve's `pointValuation` subring at the finite point `⟨xT, yT, h_ns⟩` (the
*easy half* of the valuation-subring domination). -/
theorem Sinf_kernelPrime_valuationSubring_le_pointValuation_subring
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT)
    (hTval : T.val = .some xT yT h_ns) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algLinfAt
    letI := data.isFractionRing
    ((Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).valuationSubring ≤
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation
          ⟨xT, yT, h_ns⟩).valuationSubring := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  intro x hx
  have h_ord : (0 : WithTop ℤ) ≤
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val x :=
    Sinf_ordAtPoint_nonneg_of_valuation_le_one W hq data T x
      ((Valuation.mem_valuationSubring_iff _ x).mp hx)
  rw [hTval, Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P] at h_ord
  refine (Valuation.mem_valuationSubring_iff _ x).mpr ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [map_zero]; exact zero_le_one' _
  · exact Curves.pointValuation_le_one_of_ord_nonneg
      (W := W.toAffine) hx0 ⟨xT, yT, h_ns⟩ h_ord

/-- **F.1 (affine branch) — the valuation-subring domination.** For a finite kernel point
`⟨xT, yT, h_ns⟩`, the carrier's `P_T`-adic valuation subring dominates the curve's local
ring at that point in the `LocalSubring` order. -/
theorem Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT)
    (hTval : T.val = .some xT yT h_ns) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algLinfAt
    letI := data.isFractionRing
    ((Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).valuationSubring.toLocalSubring ≤
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation
          ⟨xT, yT, h_ns⟩).valuationSubring.toLocalSubring := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set P : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).SmoothPoint := ⟨xT, yT, h_ns⟩
  set A : ValuationSubring L :=
    ((Sinf_kernelPrime_heightOne W hq data T).valuation L).valuationSubring
  set B : ValuationSubring L :=
    ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).valuationSubring with hB
  haveI : IsDiscreteValuationRing A := Sinf_kernelPrime_valuationSubring_isDVR W hq data T
  have hAB : A ≤ B :=
    Sinf_kernelPrime_valuationSubring_le_pointValuation_subring W hq data T xT yT h_ns hTval
  have hBtop : B ≠ ⊤ := by
    have hNontriv : ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P).IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨x, hx⟩ := Curves.SmoothPlaneCurve.pointValuation_surjective
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K) P (WithZero.exp (1 : ℤ))
      refine ⟨x, ?_, ?_⟩
      · exact hx ▸ WithZero.exp_ne_zero
      · simp [hx, ← WithZero.exp_zero, WithZero.exp_inj]
    intro htop
    rw [hB] at htop
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  have hEq : A = B := rankOne_valuationSubring_le_eq_of_ne_top A B hAB hBtop
  exact le_of_eq (congrArg ValuationSubring.toLocalSubring hEq)

/-- **F.1 (affine branch) — the valuation equivalence.**

For a finite kernel point (`T.val = .some xT yT h_ns`), the carrier's intrinsic
`P_T`-adic valuation `(Sinf_kernelPrime_heightOne …).valuation` on `L` is
`Valuation.IsEquiv` to the curve's `pointValuation ⟨xT, yT, h_ns⟩`. -/
theorem Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT)
    (hTval : T.val = .some xT yT h_ns) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algLinfAt
    letI := data.isFractionRing
    ((Sinf_kernelPrime_heightOne W hq data T).valuation
        (Curves.RamificationAtInfinity.LinfAt (k := K)
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)))).IsEquiv
      ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation ⟨xT, yT, h_ns⟩) :=
  Valuation.isEquiv_of_valuationSubring_le _ _
    (Sinf_kernelPrime_valuationSubring_le_pointValuation_at_affine
      W hq data T xT yT h_ns hTval)

/-- **F.1 RESIDUAL (infinity branch) — value identity at the point at infinity.**

The `T.val = .zero` (= `O`, point at infinity) case of
`Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`. Here the curve-side order is the
**degree-based** `ordAtInfty` (`Curves/Infinity.lean`, `-intDegree ∘ normAsRatFunc`),
which — unlike the finite-point `ord_P` — is *not* packaged as a DVR / `Valuation`
/ `ValuationSubring` in the project. Establishing the value identity at infinity
therefore requires first packaging `ordAtInfty` as a `Valuation L ℤᵐ⁰` (equivalently a
`ValuationSubring`) so the banked maximality machinery applies, then running the same
subring-domination argument as the affine branch. Tracked as `/develop` sub-ticket
`T-V-1-3-RAMIDX-EQ-ORDATPOINT` (infinity sub-case). -/
theorem Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (hTval : T.val = .zero)
    (d : ℤ) (a : data.carrier)
    (ha0 : letI := data.commRing; a ≠ 0)
    (had : letI := data.commRing
      letI := data.algLinfAt
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier
            (Curves.RamificationAtInfinity.LinfAt (k := K)
              ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) = (d : WithTop ℤ)) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    (Sinf_kernelPrime_heightOne W hq data T).intValuation a = WithZero.exp (-d) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set v := Sinf_kernelPrime_heightOne W hq data T
  set C : Curves.SmoothPlaneCurve K := ⟨W.toAffine⟩
  -- The two valuations on `L`: the carrier `P_T`-adic `v.valuation`, and the
  -- infinity-place valuation `ordAtInftyValuation` (just packaged in `Curves/Infinity.lean`).
  set w := C.ordAtInftyValuation with hw
  set A : ValuationSubring L := (v.valuation L).valuationSubring with hA
  set B : ValuationSubring L := w.valuationSubring with hB
  -- `had` (rewritten along `T.val = .zero`): `ordAtInfty (algebraMap a) = d`.
  rw [hTval, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] at had
  -- `algebraMap a ≠ 0` (carrier ↪ L is an IsFractionRing embedding).
  have h_img_ne : algebraMap data.carrier L a ≠ 0 := by
    simpa using (IsFractionRing.injective data.carrier L).ne ha0
  -- `A` is a DVR (rank-one: cyclic + nontrivial value group from surjectivity).
  haveI : IsDiscreteValuationRing A := Sinf_kernelPrime_valuationSubring_isDVR W hq data T
  -- (1) Subring inclusion `A ≤ B`: `v(x) ≤ 1 → ordAtInfty x ≥ 0` (shipped uniform forward
  -- half `Sinf_ordAtPoint_nonneg_of_valuation_le_one` + `ordAtPoint .zero = ordAtInfty`)
  -- → `w x ≤ 1` (`ordAtInftyValuation_le_one_of_ordAtInfty_nonneg`).
  have hAB : A ≤ B := by
    intro x hx
    have hx1 : v.valuation L x ≤ 1 := (Valuation.mem_valuationSubring_iff _ x).mp hx
    have h_ord : (0 : WithTop ℤ) ≤ C.ordAtInfty x := by
      simpa only [hTval, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] using
        Sinf_ordAtPoint_nonneg_of_valuation_le_one W hq data T x hx1
    refine (Valuation.mem_valuationSubring_iff _ x).mpr ?_
    rcases eq_or_ne x 0 with rfl | hx0
    · simp only [map_zero]; exact zero_le_one' _
    · exact C.ordAtInftyValuation_le_one_of_ordAtInfty_nonneg hx0 h_ord
  -- (2) `B ≠ ⊤`: `w` is nontrivial (surjective onto `ℤᵐ⁰`, so some value `≠ 0, 1`).
  have hBtop : B ≠ ⊤ := by
    have hNontriv : w.IsNontrivial := by
      refine ⟨?_⟩
      obtain ⟨x, hx⟩ := C.ordAtInftyValuation_surjective (WithZero.exp (1 : ℤ))
      refine ⟨x, ?_, ?_⟩
      · rw [hw, hx]; exact WithZero.exp_ne_zero
      · rw [hw, hx, Ne, ← WithZero.exp_zero, WithZero.exp_inj]; norm_num
    intro htop
    rw [hB] at htop
    exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
  -- (3) DVR-domination crux: `A = B` (`rankOne_valuationSubring_le_eq_of_ne_top`).
  have hEq : A = B := rankOne_valuationSubring_le_eq_of_ne_top A B hAB hBtop
  -- The two valuations are EQUIVALENT (same valuation subring), then EQUAL
  -- (both surjective onto `ℤᵐ⁰`, banked `isEquiv_iff_eq_of_surjective_withZeroInt`).
  have h_isEquiv : (v.valuation L).IsEquiv w := by
    rw [Valuation.isEquiv_iff_valuationSubring]; rw [hA, hB] at hEq; exact hEq
  have h_eq : v.valuation L = w :=
    Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
      (Sinf_kernelPrime_valuation_surjective W hq data T)
      C.ordAtInftyValuation_surjective h_isEquiv
  -- `intValuation a = v.valuation (algebraMap a) = w (algebraMap a) = exp(-d)`.
  rw [← v.valuation_of_algebraMap (K := L) a, h_eq]
  exact C.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq h_img_ne had

/-- **F.1 RESIDUAL SUB-LEAF — the irreducible valuation identification (value identity).**

For the height-one prime `v := Sinf_kernelPrime_heightOne …` (whose `asIdeal` is `P_T`)
and any nonzero carrier element `a`, if `ord_T(algebraMap a) = (d : WithTop ℤ)` then
`v.intValuation a = WithZero.exp (-d)`. -/
theorem Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (d : ℤ) (a : data.carrier)
    (ha0 : letI := data.commRing; a ≠ 0)
    (had : letI := data.commRing
      letI := data.algLinfAt
      (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier
            (Curves.RamificationAtInfinity.LinfAt (k := K)
              ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a) = (d : WithTop ℤ)) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    (Sinf_kernelPrime_heightOne W hq data T).intValuation a = WithZero.exp (-d) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set v := Sinf_kernelPrime_heightOne W hq data T
  rcases h_T_val : T.val with _ | ⟨xT, yT, h_ns⟩
  · exact Sinf_intValuation_eq_exp_neg_ordAtInfty_at_zero W hq data T h_T_val d a ha0 had
  · set P : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).SmoothPoint := ⟨xT, yT, h_ns⟩
    set w := (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).pointValuation P
    rw [h_T_val, Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P] at had
    have h_img_ne : algebraMap data.carrier L a ≠ 0 := by
      simpa using (IsFractionRing.injective data.carrier L).ne ha0
    have h_eq : v.valuation L = w :=
      Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T)
        (Curves.SmoothPlaneCurve.pointValuation_surjective _ P)
        (Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
          W hq data T xT yT h_ns h_T_val)
    rw [← v.valuation_of_algebraMap (K := L) a, h_eq]
    exact Curves.SmoothPlaneCurve.pointValuation_eq_exp_neg_of_ord_P_eq h_img_ne had

/-- **F.1: the consumed valuation inequality.**

For the height-one prime `v := Sinf_kernelPrime_heightOne …` (whose `asIdeal` is
`P_T`) and any carrier element `a`, if `ord_T(algebraMap a) ≥ m` then
`v.intValuation a ≤ WithZero.exp (-m)`. -/
theorem Sinf_intValuation_le_exp_neg_at_kernel
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (m : ℤ) (a : data.carrier)
    (ha : letI := data.commRing
      letI := data.algLinfAt
      (m : WithTop ℤ) ≤
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier
            (Curves.RamificationAtInfinity.LinfAt (k := K)
              ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a)) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    (Sinf_kernelPrime_heightOne W hq data T).intValuation a ≤
      WithZero.exp (-m) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [(Sinf_kernelPrime_heightOne W hq data T).intValuation.map_zero]
    exact zero_le
  have h_img_ne : algebraMap data.carrier L a ≠ 0 := by
    simpa using (IsFractionRing.injective data.carrier L).ne ha0
  have h_ne_top : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
      (algebraMap data.carrier L a) ≠ ⊤ := by
    rw [Ne, (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint_eq_top_iff]
    exact h_img_ne
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
  rw [Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel W hq data T d a ha0 hd.symm]
  rw [← hd] at ha
  have hmd : m ≤ d := by exact_mod_cast ha
  exact WithZero.exp_le_exp.mpr (by omega)

/-- **F.1: the reverse membership direction.** If the curve-order at the kernel
point `T` of a carrier element's image is at least `n`, then the element lies in
the `n`-th power of the order-based kernel prime
`P_T := bridge_Bi_kernelToPrime_v2 W hq data T`. -/
theorem Sinf_kernelPrime_pow_mem_of_le_ord
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (n : ℕ) (a : data.carrier)
    (ha : letI := data.commRing
      letI := data.algLinfAt
      (n : WithTop ℤ) ≤
        (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
          (algebraMap data.carrier
            (Curves.RamificationAtInfinity.LinfAt (k := K)
              ((isogOneSub_negFrobenius W hq).pullback (x_gen W))) a)) :
    letI := data.commRing
    a ∈ (bridge_Bi_kernelToPrime_v2 W hq data T) ^ n := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  set v := Sinf_kernelPrime_heightOne W hq data T
  -- `v.asIdeal = P_T` definitionally.
  change a ∈ v.asIdeal ^ n
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem v a n]
  refine Sinf_intValuation_le_exp_neg_at_kernel W hq data T (n : ℤ) a ?_
  exact_mod_cast ha

/-- **F.1 keystone (V.1.3): carrier ramification index at a kernel prime is `2`.**

The carrier-side ramification index of the order-based kernel prime
`P_T := bridge_Bi_kernelToPrime_v2 W hq data T` over `xIdeal := (X) ⊂ Polynomial K`
equals `2`. This is the precise residual content of `bridge_Biii_ord_eq_neg_two_v2`.

**This theorem is now proved** (no bare `sorry`) by reducing to ideal membership
via `Ideal.ramificationIdx_spec` with `n = 2`: writing `xc := algebraMap
(Polynomial K) carrier X` (image `f⁻¹` in `LinfAt f`, so `xIdeal.map = span {xc}`),

  `ramificationIdx (algebraMap) (X) P_T = 2`
    ⟸ `xc ∈ P_T ^ 2`            (the reverse valuation direction, the one residual)
    ∧ `¬ (xc ∈ P_T ^ 3)`        (forward direction, SHIPPED: `Sinf_kernelPrime_pow_le_ord`)

Both feed off `ord_T(image xc) = ord_T(f⁻¹) = 2`
(`Conditional.inv_gamma_pullback_x_pos_at_kernel`). The forward fact gives `xc ∈
P_T^3 → 3 ≤ 2`, false. The membership `xc ∈ P_T^2` is supplied by the single
isolated leaf `Sinf_kernelPrime_pow_mem_of_le_ord` (`2 ≤ ord_T(f⁻¹)=2 → xc ∈
P_T^2`).

**The only open content** is therefore `Sinf_kernelPrime_pow_mem_of_le_ord`: that
`P_T^n` is *exactly* `{a | ord_T(a) ≥ n}`, i.e. that the curve's `ordAtPoint T`
valuation restricted to the abstract Sinf carrier *is* the carrier's intrinsic
`P_T`-adic (`IsDedekindDomain.HeightOneSpectrum`) valuation up to uniformizer
normalization. These are valuations on two a-priori-different Dedekind domains
sharing the fraction field `LinfAt f = W.toAffine.FunctionField`; their agreement
at `P_T` is the closed-point ↔ prime identification that underlay the
since-deleted upstream `bridge_Bii_bijective`. Tracked as `/develop` sub-ticket
`.mathlib-quality/tickets/hasse/T-V-1-3-RAMIDX-EQ-ORDATPOINT.md`. -/
theorem Sinf_ramificationIdx_eq_two_at_kernel
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) :
        W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.algPoly
    Ideal.ramificationIdx
        (Curves.RamificationAtInfinity.xIdeal (k := K))
        (bridge_Bi_kernelToPrime_v2 W hq data T) = 2 := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.algLinfAt
  letI := data.isScalarTower
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set xc : data.carrier := algebraMap (Polynomial K) data.carrier Polynomial.X with hxc
  have h_ord_xc : (⟨W.toAffine⟩ : Curves.SmoothPlaneCurve K).ordAtPoint T.val
      (algebraMap data.carrier L xc) = (2 : WithTop ℤ) := by
    -- Scalar-tower collapse: `algebraMap carrier L (algebraMap (Poly K) carrier X) = f⁻¹`.
    have h_tower : algebraMap data.carrier L xc =
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ := by
      rw [hxc, ← IsScalarTower.algebraMap_apply (Polynomial K) data.carrier L Polynomial.X,
        Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply,
        Curves.RamificationAtInfinity.polyToFieldOfInv_X]
    rw [h_tower]
    exact Conditional.inv_gamma_pullback_x_pos_at_kernel W hq T
  have h_map : (Curves.RamificationAtInfinity.xIdeal (k := K)).map
      (algebraMap (Polynomial K) data.carrier) = Ideal.span {xc} := by
    rw [Curves.RamificationAtInfinity.xIdeal, Ideal.map_span, Set.image_singleton]
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [h_map, Ideal.span_singleton_le_iff_mem]
    refine Sinf_kernelPrime_pow_mem_of_le_ord W hq data T 2 xc ?_
    rw [h_ord_xc]; norm_num
  · rw [h_map, Ideal.span_singleton_le_iff_mem]
    intro h_mem
    have h_le := Sinf_kernelPrime_pow_le_ord W hq data T 3 xc h_mem
    rw [h_ord_xc, show (2 : WithTop ℤ) = ((2 : ℕ) : WithTop ℤ) from rfl, Nat.cast_le] at h_le
    omega

/-- **F.1 downstream dispatch — Bridge B(iii): order at every kernel-prime is `−2`.**

Downstream un-import-blocked analogue of the former upstream
`HasseWeil.bridge_Biii_ord_eq_neg_two` (an OpenLemmas.lean `sorry`, deleted
2026-06-11), stated with
the same binders as `bridge_Bi_liesOver_v2` (plus `letI := data.algPoly`) and the
order-based kernel-prime `bridge_Bi_kernelToPrime_v2`.

Per the `Sinf.ordAt` definition (`RamificationAtInfinity.lean`),
`data.ordAt P = -(ramificationIdx (algebraMap (Polynomial K) data.carrier) (X) P : ℤ)`,
so the `= -2` goal reduces to the `ℕ`-level `ramificationIdx … = 2`, discharged by
`Sinf_ramificationIdx_eq_two_at_kernel` (the isolated residual: carrier-valuation
↔ curve-`ordAtPoint` identification, `= ord_T(f⁻¹) = 2`).

* **Silverman**: V.1.1 proof (book p. 138, ramification computation): every
  `F_q`-rational kernel point of `γ = 1 − π` is a double pole of `γ.pullback x_gen`,
  contributing ramification index `2`.
* **Project**: Bridge B(iii), V.1.3 substrate; on the Hasse critical path. -/
theorem bridge_Biii_ord_eq_neg_two_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.algPoly
    data.ordAt (bridge_Bi_kernelToPrime_v2 W hq data T) = (-2 : ℤ) := by
  letI := data.commRing
  letI := data.algPoly
  change -(Ideal.ramificationIdx
      (Curves.RamificationAtInfinity.xIdeal (k := K))
      (bridge_Bi_kernelToPrime_v2 W hq data T) : ℤ) = (-2 : ℤ)
  rw [Sinf_ramificationIdx_eq_two_at_kernel W hq data T]
  rfl

/-! ### F.1 linchpin — kernel ↔ primes-over-(x) membership characterization

The downstream `_v2` analogue of the (now-deleted) upstream `bridge_Bii_bijective`
stub, phrased as a `primesOverFinset` membership characterization.

The **backward** direction (`bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`) is
shipped axiom-clean: every order-based kernel-prime `P_T := bridge_Bi_kernelToPrime_v2`
is a prime of `data.carrier` lying over `xIdeal`, hence a member of the finite set
`primesOverFinset xIdeal data.carrier` (Mathlib `mem_primesOverFinset_iff`, using
`xIdeal_isMaximal` + `xIdeal_ne_bot`). It feeds the live V.1.3 chain
(`GapSpines.isogOneSub_negFrobenius_pointCount_le_degree`).

(The **forward** / surjectivity direction's sorried cone — `bridge_Bii_surjective_v2`
down to `Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount` — was deleted 2026-06-11; V.1.3
closed via the embeddings classification in GapSpines instead.) -/

/-- **F.1 linchpin (backward / injectivity-side membership)** — axiom-clean.

Every order-based kernel-prime `P_T := bridge_Bi_kernelToPrime_v2 W hq data T` is a
member of `primesOverFinset xIdeal data.carrier`. -/
theorem bridge_Bii_kernelToPrime_mem_primesOverFinset_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algPoly
    bridge_Bi_kernelToPrime_v2 W hq data T ∈
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  rw [IsDedekindDomain.mem_primesOverFinset_iff Curves.RamificationAtInfinity.xIdeal_ne_bot]
  exact ⟨bridge_Bi_isPrime_v2 W hq data T, bridge_Bi_liesOver_v2 W hq data T⟩

/-- **F.1 injectivity — the kernel-to-prime map is injective.**

The order-based kernel-to-prime map `T ↦ P_T := bridge_Bi_kernelToPrime_v2 W hq data T`
is injective: distinct `F_q`-rational kernel points of `1 − π` give distinct primes of
`data.carrier` lying over `xIdeal := (X)`. The injective half of the closed-point ↔ prime
correspondence (Silverman V.1.1, p. 138); axiom-clean, with no `IsAlgClosed`. -/
theorem Sinf_kernelToPrime_v2_injective
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField)) :
    letI := data.commRing
    Function.Injective
      (fun T : (isogOneSub_negFrobenius W hq).kernel ↦
        bridge_Bi_kernelToPrime_v2 W hq data T) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  letI := data.algLinfAt
  letI := data.isFractionRing
  set C : Curves.SmoothPlaneCurve K := ⟨W.toAffine⟩ with hC
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) with hL
  -- Reduce to: `P_{T₁} = P_{T₂} → T₁.val = T₂.val`.
  intro T₁ T₂ h_eq
  simp only at h_eq
  refine Subtype.ext ?_
  -- The two `P_T` are exactly the `asIdeal`s of the height-one spectra
  -- `v_i := Sinf_kernelPrime_heightOne … Tᵢ`, so equal primes give EQUAL height-one
  -- spectra (`HeightOneSpectrum.ext`), hence the SAME `P_T`-adic valuation on `L`.
  set v₁ := Sinf_kernelPrime_heightOne W hq data T₁ with hv₁
  set v₂ := Sinf_kernelPrime_heightOne W hq data T₂ with hv₂
  have h_asIdeal : v₁.asIdeal = v₂.asIdeal := h_eq
  have h_height_eq : v₁ = v₂ := IsDedekindDomain.HeightOneSpectrum.ext h_asIdeal
  have h_val_eq : v₁.valuation L = v₂.valuation L := by rw [h_height_eq]
  -- Curve-side helper: two `pointValuation`s that agree as valuations on `L = K(E)`
  -- have equal maximal ideals, hence (by `maximalIdealAt_injective`) equal points.
  have h_point_inj : ∀ (P Q : C.SmoothPoint),
      C.pointValuation P = C.pointValuation Q → P = Q := by
    intro P Q hPQ
    apply C.maximalIdealAt_injective
    apply Ideal.ext
    intro u
    rw [← C.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt u P,
      ← C.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt u Q, hPQ]
  -- Mixed-case helper: `coordX` is regular at every affine point
  -- (`pointValuation ≤ 1`, it is an `algebraMap` of a coordinate-ring element) but has a
  -- pole of order `2` at infinity (`ordAtInftyValuation coordX = exp 2 > 1`), so the
  -- infinity place and any affine place are DISTINCT valuations on `L`.
  have h_coordX_cr : C.coordX =
      algebraMap C.CoordinateRing C.FunctionField
        (algebraMap (Polynomial K) C.CoordinateRing Polynomial.X) := by
    rw [Curves.SmoothPlaneCurve.coordX,
      ← IsScalarTower.algebraMap_apply (Polynomial K) C.CoordinateRing C.FunctionField]
  have h_coordX_affine_le : ∀ P : C.SmoothPoint, C.pointValuation P C.coordX ≤ 1 := by
    intro P; rw [h_coordX_cr]; exact C.pointValuation_algebraMap_le_one _ P
  have h_coordX_inf : C.ordAtInftyValuation C.coordX = WithZero.exp (2 : ℤ) := by
    have := C.ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq C.coordX_ne_zero
      C.ordAtInfty_coordX
    rwa [neg_neg] at this
  have h_exp2_gt_one : (1 : WithZero (Multiplicative ℤ)) < WithZero.exp (2 : ℤ) := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  -- `ordAtInftyValuation` and `pointValuation P` differ (apply both to `coordX`).
  have h_inf_ne_affine : ∀ P : C.SmoothPoint,
      C.ordAtInftyValuation ≠ C.pointValuation P := by
    intro P hcontra
    have h1 : C.ordAtInftyValuation C.coordX = C.pointValuation P C.coordX := by
      rw [hcontra]
    rw [h_coordX_inf] at h1
    exact absurd (h1 ▸ h_coordX_affine_le P) (not_le.mpr h_exp2_gt_one)
  -- Case-split on the two kernel points.
  rcases h_T₁ : T₁.val with _ | ⟨x₁, y₁, hns₁⟩ <;>
    rcases h_T₂ : T₂.val with _ | ⟨x₂, y₂, hns₂⟩
  · -- ∞, ∞: the same point.
    rfl
  · -- ∞ vs affine: `v₁.valuation = ordAtInftyValuation` and
    -- `v₂.valuation = pointValuation P₂`, contradicting `h_val_eq` via `coordX`.
    exfalso
    -- `v₁.valuation L = ordAtInftyValuation` (infinity branch, proven via subring equality).
    have h_inf : v₁.valuation L = C.ordAtInftyValuation := by
      obtain ⟨t, ht⟩ := (Sinf_kernelPrime_heightOne W hq data T₁).valuation_exists_uniformizer L
      apply Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₁)
        C.ordAtInftyValuation_surjective
      rw [Valuation.isEquiv_iff_valuationSubring]
      have hAB : (v₁.valuation L).valuationSubring ≤ C.ordAtInftyValuation.valuationSubring := by
        intro x hx
        have hx1 : v₁.valuation L x ≤ 1 := (Valuation.mem_valuationSubring_iff _ x).mp hx
        have h_ord : (0 : WithTop ℤ) ≤ C.ordAtInfty x := by
          have := Sinf_ordAtPoint_nonneg_of_valuation_le_one W hq data T₁ x hx1
          rwa [h_T₁, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] at this
        refine (Valuation.mem_valuationSubring_iff _ x).mpr ?_
        rcases eq_or_ne x 0 with rfl | hx0
        · simp only [map_zero]; exact zero_le_one' _
        · exact C.ordAtInftyValuation_le_one_of_ordAtInfty_nonneg hx0 h_ord
      haveI : IsDiscreteValuationRing (v₁.valuation L).valuationSubring :=
        Sinf_kernelPrime_valuationSubring_isDVR W hq data T₁
      have hBtop : C.ordAtInftyValuation.valuationSubring ≠ ⊤ := by
        have hNontriv : C.ordAtInftyValuation.IsNontrivial := by
          refine ⟨?_⟩
          obtain ⟨x, hx⟩ := C.ordAtInftyValuation_surjective (WithZero.exp (1 : ℤ))
          refine ⟨x, ?_, ?_⟩
          · rw [hx]; exact WithZero.exp_ne_zero
          · rw [hx, Ne, WithZero.exp_eq_one]; norm_num
        intro htop; exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
      exact rankOne_valuationSubring_le_eq_of_ne_top _ _ hAB hBtop
    -- `v₂.valuation L = pointValuation P₂` (affine branch).
    have h_aff : v₂.valuation L =
        C.pointValuation ⟨x₂, y₂, hns₂⟩ :=
      Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₂)
        (C.pointValuation_surjective _)
        (Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
          W hq data T₂ x₂ y₂ hns₂ h_T₂)
    rw [h_val_eq, h_aff] at h_inf
    exact h_inf_ne_affine ⟨x₂, y₂, hns₂⟩ h_inf.symm
  · -- affine vs ∞: symmetric contradiction.
    exfalso
    have h_inf : v₂.valuation L = C.ordAtInftyValuation := by
      apply Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₂)
        C.ordAtInftyValuation_surjective
      rw [Valuation.isEquiv_iff_valuationSubring]
      have hAB : (v₂.valuation L).valuationSubring ≤ C.ordAtInftyValuation.valuationSubring := by
        intro x hx
        have hx1 : v₂.valuation L x ≤ 1 := (Valuation.mem_valuationSubring_iff _ x).mp hx
        have h_ord : (0 : WithTop ℤ) ≤ C.ordAtInfty x := by
          have := Sinf_ordAtPoint_nonneg_of_valuation_le_one W hq data T₂ x hx1
          rwa [h_T₂, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] at this
        refine (Valuation.mem_valuationSubring_iff _ x).mpr ?_
        rcases eq_or_ne x 0 with rfl | hx0
        · simp only [map_zero]; exact zero_le_one' _
        · exact C.ordAtInftyValuation_le_one_of_ordAtInfty_nonneg hx0 h_ord
      haveI : IsDiscreteValuationRing (v₂.valuation L).valuationSubring :=
        Sinf_kernelPrime_valuationSubring_isDVR W hq data T₂
      have hBtop : C.ordAtInftyValuation.valuationSubring ≠ ⊤ := by
        have hNontriv : C.ordAtInftyValuation.IsNontrivial := by
          refine ⟨?_⟩
          obtain ⟨x, hx⟩ := C.ordAtInftyValuation_surjective (WithZero.exp (1 : ℤ))
          refine ⟨x, ?_, ?_⟩
          · rw [hx]; exact WithZero.exp_ne_zero
          · rw [hx, Ne, WithZero.exp_eq_one]; norm_num
        intro htop; exact (Valuation.valuationSubring_eq_top_iff _).mp htop hNontriv
      exact rankOne_valuationSubring_le_eq_of_ne_top _ _ hAB hBtop
    have h_aff : v₁.valuation L =
        C.pointValuation ⟨x₁, y₁, hns₁⟩ :=
      Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₁)
        (C.pointValuation_surjective _)
        (Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
          W hq data T₁ x₁ y₁ hns₁ h_T₁)
    rw [← h_val_eq, h_aff] at h_inf
    exact h_inf_ne_affine ⟨x₁, y₁, hns₁⟩ h_inf.symm
  · -- affine vs affine: the main case. `pointValuation P₁ = pointValuation P₂`,
    -- so `P₁ = P₂` (`maximalIdealAt_injective`), hence `T₁.val = T₂.val`.
    have h_aff₁ : v₁.valuation L =
        C.pointValuation ⟨x₁, y₁, hns₁⟩ :=
      Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₁)
        (C.pointValuation_surjective _)
        (Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
          W hq data T₁ x₁ y₁ hns₁ h_T₁)
    have h_aff₂ : v₂.valuation L =
        C.pointValuation ⟨x₂, y₂, hns₂⟩ :=
      Valuation.isEquiv_iff_eq_of_surjective_withZeroInt _ _
        (Sinf_kernelPrime_valuation_surjective W hq data T₂)
        (C.pointValuation_surjective _)
        (Sinf_kernelPrime_valuation_isEquiv_pointValuation_at_affine
          W hq data T₂ x₂ y₂ hns₂ h_T₂)
    have h_pv_eq : C.pointValuation ⟨x₁, y₁, hns₁⟩ =
        C.pointValuation ⟨x₂, y₂, hns₂⟩ := by
      rw [← h_aff₁, ← h_aff₂, h_val_eq]
    have h_pt_eq : (⟨x₁, y₁, hns₁⟩ : C.SmoothPoint) = ⟨x₂, y₂, hns₂⟩ :=
      h_point_inj _ _ h_pv_eq
    have hx : x₁ = x₂ := congrArg Curves.SmoothPlaneCurve.SmoothPoint.x h_pt_eq
    have hy : y₁ = y₂ := congrArg Curves.SmoothPlaneCurve.SmoothPoint.y h_pt_eq
    subst hx; subst hy; rfl

/-- **L1 (closed leaf): a prime over `xIdeal` contains `algebraMap X`.** For any prime `P`
of `data.carrier` lying over `xIdeal := (X)`, the element
`algebraMap (Polynomial K) data.carrier X` lies in `P`. -/
theorem Sinf_algebraMap_X_mem_of_liesOver
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (P : letI := data.commRing; Ideal data.carrier)
    (hP_liesOver : letI := data.commRing; letI := data.algPoly;
      P.LiesOver (Curves.RamificationAtInfinity.xIdeal (k := K))) :
    letI := data.commRing
    letI := data.algPoly
    algebraMap (Polynomial K) data.carrier Polynomial.X ∈ P := by
  letI := data.commRing
  letI := data.algPoly
  have hX_mem : Polynomial.X ∈ Curves.RamificationAtInfinity.xIdeal (k := K) := by
    rw [Curves.RamificationAtInfinity.xIdeal, Ideal.mem_span_singleton]
  haveI := hP_liesOver
  have h_over : Curves.RamificationAtInfinity.xIdeal (k := K) =
      Ideal.comap (algebraMap (Polynomial K) data.carrier) P := by
    rw [← Ideal.under_def]
    exact Ideal.LiesOver.over
  rwa [h_over, Ideal.mem_comap] at hX_mem

/-! ### F.1 linchpin (forward / surjectivity residual) — DELETED 2026-06-11

Every prime `P` of `data.carrier` lying over `xIdeal := (X)` is one of the
order-based kernel-primes `P_T = bridge_Bi_kernelToPrime_v2 W hq data T` —
this was the statement of the deleted sorried cone (`Sinf_primeOver_xIdeal_eq_kernelPrime`
and friends); V.1.3 closed via the GapSpines embeddings classification instead.

This is the closed-point ↔ prime correspondence (Silverman V.1.1, book p. 138): a
prime over `(X)` (where `X ↦ f⁻¹`, `f = γ.pullback x_gen`) is a place where `f⁻¹` lies
in the maximal ideal, i.e. `ord(f⁻¹) > 0`, i.e. `ord(f) < 0` — a **pole** of `f`; and
the poles of `f = γ*x` are exactly the kernel points of `1 − π` (shipped:
`ord_kernel_pullback_x_eq_neg_two`, and the pole-support ↔ kernel identification). So
`P` corresponds to a kernel point `T` with `P = P_T`.

Isolated as the deep residual underlying the since-deleted upstream `bridge_Bii_bijective`
(surjectivity). Tracked as `/develop` sub-ticket `T-V-1-3-RAMIDX-EQ-ORDATPOINT` /
the closed-point ↔ prime correspondence. The injective/backward half
(`bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`) and the value identity
(`Sinf_intValuation_eq_exp_neg_ordAtPoint_at_kernel`) are shipped axiom-clean.

**Status (2026-05-27, deep pass).** The substantive content is the *inverse* of the
shipped forward map `Sinf_kernelPrime_heightOne` (`T ↦ P_T`): producing a kernel point
`T` from a bare prime `P` over `xIdeal`. This is exactly the integral-closure descent of
Worker K's affine `smoothPoint_fiber_eq_primesOver` (`NormValuation.lean:644`), which is
stated only over `IsAlgClosed F` and for `CoordinateRing` — *not* available here (`K`
finite, carrier = `integralClosure (Polynomial K) (LinfAt f)`). The entire upstream chain
factors this same content as a witness hypothesis (`Sinf_closed_point_prime_bridge`'s
`h_witness`, `OpenLemmaPrimitives.lean:191`), and the round-5 reviewer explicitly flagged
the naive distinguishing argument (`1/f − x(Tᵢ)`) as **wrong** (`1/f` vanishes at *all*
kernel poles simultaneously). It was therefore *not* reducible to any shipped Sinf /
NormValuation bijection — the reason the whole sorried cone (membership characterization,
place→point extraction, `bridge_Bii_surjective_v2`, `bridge_Bii_mem_primesOverFinset_v2`)
was retired rather than discharged. -/

/-- **L1.5 (closed leaf): `algebraMap X ∈ P` ⟹ `P.LiesOver (X)`**

For a prime `P` of the `Sinf` carrier, membership of the generator `algebraMap X ∈ P`
upgrades to the full `LiesOver` relation `P.LiesOver xIdeal`. -/
theorem Sinf_liesOver_of_algebraMap_X_mem
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (P : letI := data.commRing; Ideal data.carrier)
    (hP_prime : letI := data.commRing; P.IsPrime)
    (hX_mem : letI := data.commRing; letI := data.algPoly;
      algebraMap (Polynomial K) data.carrier Polynomial.X ∈ P) :
    letI := data.commRing
    letI := data.algPoly
    P.LiesOver (Curves.RamificationAtInfinity.xIdeal (k := K)) := by
  letI := data.commRing
  letI := data.algPoly
  have h_le : Curves.RamificationAtInfinity.xIdeal (k := K) ≤
      Ideal.comap (algebraMap (Polynomial K) data.carrier) P := by
    rwa [Curves.RamificationAtInfinity.xIdeal, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, Ideal.mem_comap]
  have h_eq : Curves.RamificationAtInfinity.xIdeal (k := K) =
      Ideal.comap (algebraMap (Polynomial K) data.carrier) P :=
    Curves.RamificationAtInfinity.xIdeal_isMaximal.eq_of_le
      (mt Ideal.comap_eq_top_iff.mp hP_prime.ne_top) h_le
  exact ⟨h_eq.trans (Ideal.under_def _ P).symm⟩

/-! ### F.1 residue residual — residue-value-is-in-`K` core

For every carrier element `a`, there is a constant `λ : K` such that `a` agrees with
`algebraMap K data.carrier λ` modulo `P_T = {ord_T > 0}` — i.e.
`0 < ord_T(algebraMap_L a − algebraMap_{K→L} λ)`. Geometrically `λ` is the *value of
`a` at the closed point `T`*: every `a : data.carrier` is regular at `T`
(`Sinf_ord_nonneg_at_kernel_point_unconditional`, `ord_T ≥ 0`), so it has a residue
in the residue field `κ(T)`; and because `T` is `F_q`-rational (its affine
coordinates lie in `K`, and the point at infinity is `K`-rational), that residue
field is `K = F_q` itself, so the residue is a genuine constant `λ ∈ K`.

This is the integral-closure / `FunctionField`-level descent of Worker K's affine
residue iso `quotientMaximalIdealAtEquiv : F[C] ⧸ maximalIdealAt P ≃ₐ[F] F`
(`Curves/NormValuation.lean:52`) — field-agnostic, stated for `CoordinateRing`. The
affine case (`.some`) is fully discharged via the `localRingAt T` residue bridge
below; the place-at-infinity case (`.zero`) is isolated as the single remaining
residual `residue_in_base_at_infinity_of_ordAtInfty_nonneg` (it needs the
local-ring-at-infinity / residue-field development absent from the current
`ordAtInfty` API). Upstream this same content is the witness hypothesis
`Sinf_inertia_one_at_kernel.h_inertia_witness`
(`Hasse/OpenLemmaPrimitives.lean:246`). -/

/-- **Residue-at-an-affine-point is in the base field** (finite-place case of the
residue residual, fully discharged).

For a smooth plane curve `C` over an arbitrary field `F`, an affine smooth point
`P` (whose residue field `C.CoordinateRing ⧸ maximalIdealAt P ≅ F` by the
field-agnostic `quotientMaximalIdealAtEquiv`), and any function `g` *regular at
`P`* (`pointValuation P g ≤ 1`, i.e. `ord_P g ≥ 0`), there is a constant
`lam : F` — the value `g(P)` — such that `g − lam` *vanishes at `P`*
(`pointValuation P (g − lam) < 1`, i.e. `ord_P (g − lam) > 0`).

Route: `g` regular at `P` lifts into the local ring
`localRingAt P = Localization.AtPrime (maximalIdealAt P)`
(`mem_localRingAt_image_of_pointValuation_le_one`). The residue field of that
local ring is `(maximalIdealAt P).ResidueField`, into which the structure map
from `F` is *surjective* (`algebraMap F (CR ⧸ M)` is onto via
`quotientMaximalIdealAtEquiv`, and `algebraMap (CR ⧸ M) (M.ResidueField)` is the
fraction-field map of the field `CR ⧸ M`, hence bijective by
`bijective_algebraMap_quotient_residueField`). Pulling the residue of the lift
back through this surjection yields `lam`; then the residue of `lift − lam`
vanishes, placing it in the maximal ideal of the local ring, i.e.
`pointValuation P (g − lam) < 1`. -/
theorem residue_in_base_affine_of_pointValuation_le_one {F : Type*} [Field F]
    (C : Curves.SmoothPlaneCurve F) (P : C.SmoothPoint) (g : C.FunctionField)
    (hg : C.pointValuation P g ≤ 1) :
    ∃ lam : F, C.pointValuation P (g - algebraMap F C.FunctionField lam) < 1 := by
  haveI : (C.maximalIdealAt P).IsMaximal := C.maximalIdealAt_isMaximal P
  haveI : (C.maximalIdealAt P).IsPrime := (C.maximalIdealAt_isMaximal P).isPrime
  obtain ⟨x, hx⟩ :=
    Curves.SmoothPlaneCurve.mem_localRingAt_image_of_pointValuation_le_one
      (C := C) (P := P) g hg
  have hsurj :
      Function.Surjective (algebraMap F (C.maximalIdealAt P).ResidueField) := by
    have hsurj_F_quot :
        Function.Surjective (algebraMap F (C.CoordinateRing ⧸ C.maximalIdealAt P)) := by
      refine fun w ↦ ⟨(C.quotientMaximalIdealAtEquiv P) w,
        (AlgEquiv.commutes (C.quotientMaximalIdealAtEquiv P).symm _).symm.trans
          ((C.quotientMaximalIdealAtEquiv P).symm_apply_apply w)⟩
    rw [IsScalarTower.algebraMap_eq F (C.CoordinateRing ⧸ C.maximalIdealAt P)
        (C.maximalIdealAt P).ResidueField, RingHom.coe_comp]
    exact ((C.maximalIdealAt P).bijective_algebraMap_quotient_residueField.surjective).comp
      hsurj_F_quot
  obtain ⟨lam, hlam⟩ := hsurj (IsLocalRing.residue (C.localRingAt P) x)
  refine ⟨lam, ?_⟩
  set xc : C.localRingAt P :=
    algebraMap C.CoordinateRing (C.localRingAt P) (algebraMap F C.CoordinateRing lam) with hxc
  have h_mem : x - xc ∈ IsLocalRing.maximalIdeal (C.localRingAt P) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, hxc, ← hlam,
      ← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt P)
        (C.maximalIdealAt P).ResidueField,
      ← IsScalarTower.algebraMap_apply F C.CoordinateRing (C.maximalIdealAt P).ResidueField]
  have h_img : algebraMap (C.localRingAt P) C.FunctionField (x - xc)
      = g - algebraMap F C.FunctionField lam := by
    rw [map_sub, hx, hxc,
      ← IsScalarTower.algebraMap_apply C.CoordinateRing (C.localRingAt P) C.FunctionField,
      ← IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField]
  rw [← h_img]
  unfold Curves.SmoothPlaneCurve.pointValuation
  rwa [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]

/-- **Residue-at-the-point-at-infinity is in the base field**: for a smooth
Weierstrass-curve wrapper `C` over a field `F`, any function `g` regular at
infinity (`0 ≤ ordAtInfty g`) has a value `lam : F` with `g − lam` vanishing at
infinity (`0 < ordAtInfty (g − lam)`). -/
theorem residue_in_base_at_infinity_of_ordAtInfty_nonneg {F : Type*} [Field F]
    (C : Curves.SmoothPlaneCurve F) (g : C.FunctionField)
    (hg : (0 : WithTop ℤ) ≤ C.ordAtInfty g) :
    ∃ lam : F, (0 : WithTop ℤ) <
      C.ordAtInfty (g - algebraMap F C.FunctionField lam) := by
  obtain ⟨p, q, hpq⟩ := C.exists_decomp g
  set α : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField p with hα
  set β : C.FunctionField :=
    algebraMap (FractionRing (Polynomial F)) C.FunctionField q with hβ
  have h_eq_g : g = α + β * C.coordYInFunctionField := by
    rw [hpq, Algebra.smul_def, mul_one, Algebra.smul_def]
  have h_ord_g : C.ordAtInfty g = min (C.ordAtInfty α)
      (C.ordAtInfty β + C.ordAtInfty C.coordYInFunctionField) := by
    rw [h_eq_g]; exact C.ordAtInfty_basis_eq_min p q
  rw [h_ord_g, le_min_iff] at hg
  obtain ⟨hg_x, hg_y⟩ := hg
  obtain ⟨lam, hlam⟩ := C.ordAtInfty_exists_const_sub_pos_of_fracPolyX_nonneg (r₀ := p) hg_x
  refine ⟨lam, ?_⟩
  have hg_y_pos : (0 : WithTop ℤ) < C.ordAtInfty (β * C.coordYInFunctionField) := by
    by_cases hβ0 : β = 0
    · rw [hβ0, zero_mul, C.ordAtInfty_zero]; exact WithTop.coe_lt_top 0
    · have hq0 : q ≠ 0 := by
        intro h; apply hβ0; rw [hβ, h, map_zero]
      have h_ord_βy : C.ordAtInfty (β * C.coordYInFunctionField) =
          (((-2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree) + (-3) : ℤ)
            : WithTop ℤ) := by
        rw [C.ordAtInfty_mul hβ0 C.coordYInFunctionField_ne_zero, hβ,
          C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hq0,
          C.ordAtInfty_coordYInFunctionField, ← WithTop.coe_add]
      rw [h_ord_βy]
      have h_int : (0 : ℤ) ≤ -2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree + -3 := by
        rw [hβ, C.ordAtInfty_algebraMap_fracPolyX_of_ne_zero hq0,
          C.ordAtInfty_coordYInFunctionField, ← WithTop.coe_add] at hg_y
        exact_mod_cast hg_y
      exact_mod_cast (by omega :
        (0 : ℤ) < -2 * (RatFunc.ofFractionRing q : RatFunc F).intDegree + -3)
  have h_sub_eq : g - algebraMap F C.FunctionField lam =
      (α - algebraMap F C.FunctionField lam) + β * C.coordYInFunctionField := by
    rw [h_eq_g]; ring
  rw [h_sub_eq]
  exact (lt_min hlam hg_y_pos).trans_le (C.ordAtInfty_add_ge_min _ _)

theorem Sinf_kappa_kernelPrime_residue_in_base
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    (a : (letI := data.commRing; data.carrier)) :
    letI := data.commRing
    letI := data.algPoly
    letI := data.algLinfAt
    ∃ lam : K, a - (algebraMap (Polynomial K) data.carrier) (Polynomial.C lam)
      ∈ bridge_Bi_kernelToPrime_v2 W hq data T := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.algLinfAt
  haveI := data.isScalarTower
  set L : Type _ := Curves.RamificationAtInfinity.LinfAt (k := K)
    ((isogOneSub_negFrobenius W hq).pullback (x_gen W))
  set C : Curves.SmoothPlaneCurve K := ⟨W.toAffine⟩
  set g : W.toAffine.FunctionField := algebraMap data.carrier L a with hg_def
  have hg_nonneg : (0 : WithTop ℤ) ≤ C.ordAtPoint T.val g :=
    Conditional.Sinf_ord_nonneg_at_kernel_point_unconditional W hq data T a
  have h_const : ∀ lam : K,
      algebraMap data.carrier L ((algebraMap (Polynomial K) data.carrier) (Polynomial.C lam))
        = algebraMap K W.toAffine.FunctionField lam := by
    intro lam
    rw [← IsScalarTower.algebraMap_apply (Polynomial K) data.carrier L,
      Curves.RamificationAtInfinity.LinfAt.algebraMap_polynomial_apply,
      Curves.RamificationAtInfinity.polyToFieldOfInv_C]
  suffices h_suff : ∃ lam : K, (0 : WithTop ℤ) <
      C.ordAtPoint T.val (g - algebraMap K W.toAffine.FunctionField lam) by
    obtain ⟨lam, hlam⟩ := h_suff
    refine ⟨lam, ?_⟩
    change (0 : WithTop ℤ) < C.ordAtPoint T.val
      (algebraMap data.carrier L (a - (algebraMap (Polynomial K) data.carrier) (Polynomial.C lam)))
    rwa [map_sub, h_const lam, ← hg_def]
  rcases h_T_val : T.val with _ | ⟨xT, yT, h_ns⟩
  · rw [h_T_val, Curves.SmoothPlaneCurve.ordAtPoint_zero_eq_ordAtInfty] at hg_nonneg
    exact residue_in_base_at_infinity_of_ordAtInfty_nonneg (F := K) C g hg_nonneg
  · rw [h_T_val, Curves.SmoothPlaneCurve.ordAtPoint_some_eq_ord_P] at hg_nonneg
    set P : C.SmoothPoint := ⟨xT, yT, h_ns⟩
    have hg_le_one : C.pointValuation P g ≤ 1 := by
      by_cases hg0 : g = 0
      · rw [hg0, map_zero]; exact zero_le_one
      · exact Curves.pointValuation_le_one_of_ord_nonneg (W := W.toAffine) hg0 P hg_nonneg
    obtain ⟨lam, hlam⟩ :=
      residue_in_base_affine_of_pointValuation_le_one C P g hg_le_one
    refine ⟨lam, ?_⟩
    rcases eq_or_ne (g - algebraMap K W.toAffine.FunctionField lam) 0 with h0 | hne
    · rw [h0]
      simp only [SmoothPlaneCurve.ordAtPoint_zero_function,
        LinearOrderedAddCommGroupWithTop.top_pos]
    · exact lt_of_lt_of_le (by norm_num)
        ((C.one_le_ord_P_iff_pointValuation_lt_one (P := P) hne).mpr hlam)

/-! ### F.1 UNIFYING BRIDGE — combinator (the sorried leaf + its cone were deleted 2026-06-11)

The combinator below
(`Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount`) closes the
prime-is-a-kernel-place bridge by PURE FINSET CARDINALITY from the sum-of-inertia
hypothesis `Σ_{P ∈ primesOverFinset (X)} f_P = #E(F_q)`, using only DONE assets
(`Sinf_kernelToPrime_v2_injective`, `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`,
`kernel_eq_top_of_hom_eq_id_sub_frobenius`, `mem_primesOverFinset_iff`,
`Ideal.inertiaDeg_pos`). The sum identity itself is proven downstream as
`GapSpines.Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower`; the sorried
L6Witnesses statement and its consumer cone were deleted. -/

/-- **F.1 UNIFYING BRIDGE combinator**: given the sum-of-inertia identity
`Σ_{P ∈ primesOverFinset (X)} f_P = pointCount`, every carrier prime `P` lying over
`xIdeal := (X)` is the place `bridge_Bi_kernelToPrime_v2 W hq data T` at some `F_q`-rational
kernel point `T`. -/
theorem Sinf_primeOver_eq_kernelPrime_place_of_sum_inertia_eq_pointCount
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (h_sum : letI := data.commRing; letI := data.isDomain; letI := data.isDedekindDomain;
      letI := data.algPoly;
      ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
          pointCount W.toAffine)
    (P : letI := data.commRing; Ideal data.carrier)
    (hP_prime : letI := data.commRing; P.IsPrime)
    (hP_liesOver : letI := data.commRing; letI := data.algPoly;
      P.LiesOver (Curves.RamificationAtInfinity.xIdeal (k := K))) :
    letI := data.commRing
    ∃ T : (isogOneSub_negFrobenius W hq).kernel,
      P = bridge_Bi_kernelToPrime_v2 W hq data T := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  letI := data.moduleFinite
  haveI := hP_prime
  haveI := hP_liesOver
  haveI : Finite W.toAffine.Point := Finite.of_fintype _
  haveI : Finite (isogOneSub_negFrobenius W hq).kernel := inferInstance
  haveI : Fintype (isogOneSub_negFrobenius W hq).kernel := Fintype.ofFinite _
  -- Step 1: P ∈ primesOverFinset via mem_primesOverFinset_iff (xIdeal maximal + ≠ ⊥).
  have hP_mem : P ∈
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    rw [IsDedekindDomain.mem_primesOverFinset_iff Curves.RamificationAtInfinity.xIdeal_ne_bot]
    exact ⟨hP_prime, hP_liesOver⟩
  -- Step 2: image of the kernel-to-prime map.
  set image : Finset (Ideal data.carrier) :=
    (Finset.univ : Finset (isogOneSub_negFrobenius W hq).kernel).image
      (fun T ↦ bridge_Bi_kernelToPrime_v2 W hq data T) with himage_def
  -- image ⊆ primesOverFinset (backward direction shipped).
  have h_image_sub : image ⊆
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    intro Q hQ
    rw [himage_def, Finset.mem_image] at hQ
    obtain ⟨T, _, rfl⟩ := hQ
    exact bridge_Bii_kernelToPrime_mem_primesOverFinset_v2 W hq data T
  -- image.card = Nat.card kernel = pointCount.
  have h_card_kernel : Nat.card (isogOneSub_negFrobenius W hq).kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  have h_image_card : image.card = pointCount W.toAffine := by
    rwa [himage_def,
      Finset.card_image_of_injective _ (Sinf_kernelToPrime_v2_injective W hq data),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
  -- Step 3: pointCount ≥ #primesOverFinset (from h_sum + inertiaDeg_pos).
  haveI hmax : (Curves.RamificationAtInfinity.xIdeal (k := K)).IsMaximal :=
    Curves.RamificationAtInfinity.xIdeal_isMaximal
  have h_sum_ge_card :
      (IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier).card ≤
        pointCount W.toAffine := by
    rw [← h_sum]
    -- Σ_{P ∈ S} inertiaDeg P ≥ Σ_{P ∈ S} 1 = S.card, since each inertiaDeg ≥ 1.
    have h_one_le : ∀ Q ∈
        IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        1 ≤ Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q := by
      intro Q hQ
      rw [IsDedekindDomain.mem_primesOverFinset_iff Curves.RamificationAtInfinity.xIdeal_ne_bot] at hQ
      obtain ⟨hQ_prime, hQ_liesOver⟩ := hQ
      haveI := hQ_prime
      haveI := hQ_liesOver
      exact Ideal.inertiaDeg_pos (Curves.RamificationAtInfinity.xIdeal (k := K)) Q
    simpa using Finset.card_nsmul_le_sum _ _ 1 h_one_le
  -- Step 4: image = primesOverFinset (same finite cardinality, subset).
  have h_image_eq :
      image = IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier :=
    Finset.eq_of_subset_of_card_le h_image_sub (by rwa [h_image_card])
  -- Step 5: P ∈ image, so P = P_T for some T.
  rw [← h_image_eq, himage_def, Finset.mem_image] at hP_mem
  obtain ⟨T, _, hPT⟩ := hP_mem
  exact ⟨T, hPT.symm⟩

/-! ### Phase 3 (K3 + K4 wiring) — geometric K̄ count = `pointCount`

Small, axiom-clean **witness-form** wiring helpers that close the K3 + K4 sub-chain of
the historical K1-K6 K̄-count plan (for the sum-of-inertia identity, now proven as
`GapSpines.Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_via_tower`):
given the K3 identity (`K̄`-poles of `f_K̄ = x ∘ (1−π)_K̄` *as a set in*
`(W.baseChange K̄).toAffine.Point` coincide with `ker((1−π)_K̄) = (oneSubGeomFrobHom W).ker`), the
cardinality identity
`Nat.card {K̄-poles} = pointCount W.toAffine` follows from L5's
`ncard_ker_oneSubGeomFrobHom_eq_pointCount` (`Curves/FrobeniusFixedPoint.lean:338`,
`Fintype.card W.toAffine.Point = pointCount`).

This is the K4 dispatcher: K3 is the *content* (a geometric statement that needs the K̄
function field x → 1/f → K̄-points correspondence, currently unshipped), and K4 is the
*L5 cardinality* (shipped). The shape of these helpers is the (witness-form) consumer the
K3 ⟹ K6 chain expects: once K3 is shipped as the K̄-pole-set identification, K4 (here) +
K2 (`smoothPoint_fiber_eq_primesOver` over `K̄`) + K1+K5 (residue-degree splitting) would
have closed the (deleted) sorried sum-of-inertia leaf. -/

/-- **Phase 3 K3 alias**: the K̄-Frobenius-fixed locus *as a `Set`*. -/
def ker_oneSubGeomFrobHom_setOfFixed_K
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    Set (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  {P | geomFrobeniusPointFun W P = P}

/-- **Phase 3 K4** (cardinality form): `#{P | geomFrob P = P}.ncard = pointCount`. -/
theorem ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    (ker_oneSubGeomFrobHom_setOfFixed_K W).ncard = Fintype.card W.toAffine.Point := by
  rw [ker_oneSubGeomFrobHom_setOfFixed_K, ← ker_oneSubGeomFrobHom_eq_fixedLocus]
  exact ncard_ker_oneSubGeomFrobHom_eq_pointCount W

/-- **Phase 3 K3+K4 dispatcher (`.ncard` form)**: if `geomPoles` is the `id − π_K̄` kernel
locus, then `geomPoles.ncard = pointCount`. -/
theorem geom_poles_card_eq_pointCount_of_pole_eq_ker
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (geomPoles : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (h_K3 : geomPoles = ker_oneSubGeomFrobHom_setOfFixed_K W) :
    geomPoles.ncard = Fintype.card W.toAffine.Point := by
  rw [h_K3, ker_oneSubGeomFrobHom_setOfFixed_card_eq_pointCount]

/-- **F.1 Phase-3 K3+K4 dispatcher (`Nat.card` form)** — the K3 + K4 composition,
phrased with `Nat.card` of the bundled subtype `↥geomPoles`. -/
theorem geom_poles_natCard_eq_pointCount_of_pole_eq_ker
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (geomPoles : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (h_K3 : geomPoles = ker_oneSubGeomFrobHom_setOfFixed_K W) :
    Nat.card geomPoles = Fintype.card W.toAffine.Point :=
  (Nat.card_coe_set_eq geomPoles).trans
    (geom_poles_card_eq_pointCount_of_pole_eq_ker W geomPoles h_K3)

/-! ### Phase 3 K3 — concrete `geomPoles` definition (deep pass 2026-05-28)

A concrete K̄-side `geomPoles_oneSubFrob` witnessing the K3 hypothesis above. The geometric
content "Q is a K̄-pole of `f_K̄ = x_K̄ ∘ (1−π)_K̄` ⟺ `Q = π_K̄(Q)`" splits as the chain
`Q ∈ poles f_K̄  ⟺  (1−π)_K̄ Q ∈ poles x_K̄  ⟺  (1−π)_K̄ Q = O_K̄  ⟺  Q = π_K̄(Q)`. The first
two iff's are pure function-field content (pullback of a pole, `x`'s only pole is `O`).
The last iff is `oneSubGeomFrobHom`'s definitional kernel identity.

We pick the **`oneSubGeomFrobHom`-kernel framing** for `geomPoles`: the set of `P` with
`oneSubGeomFrobHom W P = 0`. This is the natural K̄-side target for the K2+K5 splitting
witness (the kernel of `id − π_K̄` IS the parameterization the K̄-primes-over-`(X)`
correspondence lands in via the K3 → kernel → K-prime fiber chain). Under this framing,
the K3 hypothesis (`geomPoles = ker_oneSubGeomFrobHom_setOfFixed_K W`) is *near-tautological*:
both sides unfold to `{P | geomFrobeniusPointFun W P = P}` via
`oneSubGeomFrobHom_apply` + `sub_eq_zero` + `eq_comm`. -/

/-- **Phase 3 K3 — concrete geometric pole set** (`oneSubGeomFrobHom`-kernel framing):
the set of `K̄`-points `P` killed by `id − π_K̄` (equivalently, fixed by `π_K̄`). -/
def geomPoles_oneSubFrob
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    Set (W.baseChange (AlgebraicClosure K)).toAffine.Point :=
  {P | oneSubGeomFrobHom W P = 0}

/-- **Phase 3 K3 — concrete equality**: the `oneSubGeomFrobHom`-kernel set equals the
`setOf`-predicate fixed-locus `{P | geomFrobeniusPointFun W P = P}`. -/
theorem geomPoles_oneSubFrob_eq_ker_setOfFixed
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] :
    geomPoles_oneSubFrob W = ker_oneSubGeomFrobHom_setOfFixed_K W :=
  ker_oneSubGeomFrobHom_eq_fixedLocus W

/-- **Phase 3 K3+K4 composition (concrete form)** — the `Nat.card` cardinality of the concrete
`oneSubGeomFrobHom`-kernel geometric pole set equals `pointCount`. -/
theorem geomPoles_oneSubFrob_card_eq_pointCount
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    Nat.card (geomPoles_oneSubFrob W) = Fintype.card W.toAffine.Point :=
  geom_poles_natCard_eq_pointCount_of_pole_eq_ker W (geomPoles_oneSubFrob W)
    (geomPoles_oneSubFrob_eq_ker_setOfFixed W)

/-! ### Phase B (deep pass 2026-05-28) — K2+K5 splitting witness composer

Witness-form composer for the sum-of-inertia identity `Σ f_P = #E(F_q)`:
given K3+K4 (axiom-clean dispatchers above provide `Nat.card{K̄-poles} = pointCount`)
together with the **K2+K5 splitting witness** (`Σ_{K-primes over (X)} f_P = Nat.card{K̄-poles}`),
the target identity follows by transitivity. The K2+K5 witness factors the deep multi-file
K̄-base-change content (K2: `smoothPoint_fiber_eq_primesOver` over K̄ — the IsAlgClosed
correspondence, K5: residue-degree splitting `κ(P) ⊗_K K̄ ≃ K̄^{f_P}` summing to
`Σ f_P = #K̄-primes`) into one named hypothesis. Pure compositional dispatcher. -/

/-- **Phase B K2+K5 composer** (witness-form): given K3 (K̄-pole set = K̄-kernel) and
the K2+K5 splitting witness (`Σ_{K-primes} f_P = #K̄-poles`), conclude the sum
identity `Σ f_P = pointCount` for the abstract `Sinf` data. The K3 input feeds K4
(`geom_poles_natCard_eq_pointCount_of_pole_eq_ker`) to give `#K̄-poles = pointCount`,
and the K2+K5 splitting transports this to the K-prime sum. Axiom-clean. -/
theorem Sinf_sum_inertiaDeg_eq_pointCount_of_K3_K2K5_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (geomPoles : Set (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (h_K3 : geomPoles = ker_oneSubGeomFrobHom_setOfFixed_K W)
    (h_K2K5_split :
      letI := data.commRing
      letI := data.isDomain
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
          Nat.card geomPoles) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
        pointCount W.toAffine :=
  h_K2K5_split.trans (geom_poles_natCard_eq_pointCount_of_pole_eq_ker W geomPoles h_K3)

/-! ### F.1 downstream dispatch — Bridge B(iv): residue field is `K` at every kernel-prime

The downstream `_v2` analogue of the former upstream `bridge_Biv_inertia_eq_one`
(`OpenLemmas.lean`, deleted 2026-06-11): the inertia degree of every order-based kernel-prime over
`xIdeal := (X)` is `1`.

Per `Sinf.inertiaDeg_eq_finrank_kappa` (`RamificationAtInfinity.lean`), with the
`LiesOver` instance from `bridge_Bi_liesOver_v2`,
`inertiaDeg (X) P_T = Module.finrank (Polynomial K ⧸ (X)) (data.kappa P_T)`, so the
`= 1` goal reduces to that residue-ring–level finrank being `1`, which is the
residue-field-at-an-`F_q`-rational-point content isolated below as
`Sinf_finrank_kappa_kernelPrime_eq_one`. -/

/-- **F.1 residue residual — core surjectivity** (the residue-field-is-`K`
content). The structure algebra map `K[X]⧸(X) → data.carrier ⧸ P_T` of the residue
ring at the order-based kernel-prime `P_T := bridge_Bi_kernelToPrime_v2 W hq data T`
is surjective. Equivalently `data.carrier ⧸ P_T` is generated over the base residue
field `K[X]⧸(X)` by `1`, so it *is* the base residue field (`≅ K`), giving residue
degree `1`. -/
theorem Sinf_kappa_kernelPrime_algebraMap_surjective
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    [letI := data.commRing; letI := data.algPoly;
      (bridge_Bi_kernelToPrime_v2 W hq data T).LiesOver
        (Curves.RamificationAtInfinity.xIdeal (k := K))] :
    letI := data.commRing
    letI := data.algPoly
    letI : Algebra (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
        (data.kappa (bridge_Bi_kernelToPrime_v2 W hq data T)) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        (Ideal.LiesOver.over (p := Curves.RamificationAtInfinity.xIdeal (k := K))
          (P := bridge_Bi_kernelToPrime_v2 W hq data T)).le
    Function.Surjective
      (algebraMap (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
        (data.kappa (bridge_Bi_kernelToPrime_v2 W hq data T))) := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.algLinfAt
  set P_T : Ideal data.carrier := bridge_Bi_kernelToPrime_v2 W hq data T
  letI : Algebra (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
      (data.carrier ⧸ P_T) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.LiesOver.over (p := Curves.RamificationAtInfinity.xIdeal (k := K)) (P := P_T)).le
  have h_le : Curves.RamificationAtInfinity.xIdeal (k := K) ≤
      Ideal.comap (algebraMap (Polynomial K) data.carrier) P_T :=
    (Ideal.LiesOver.over (p := Curves.RamificationAtInfinity.xIdeal (k := K)) (P := P_T)).le
  intro w
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := P_T) w
  obtain ⟨lam, hlam⟩ := Sinf_kappa_kernelPrime_residue_in_base W hq data T a
  refine ⟨Ideal.Quotient.mk (Curves.RamificationAtInfinity.xIdeal (k := K)) (Polynomial.C lam), ?_⟩
  change Ideal.quotientMap P_T (algebraMap (Polynomial K) data.carrier) h_le
      (Ideal.Quotient.mk _ (Polynomial.C lam)) = _
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← neg_sub]
  exact neg_mem hlam

/-- **F.1 residue residual (V.1.3 B(iv)): the residue field at a kernel-prime is `K`.**

For each `F_q`-rational kernel point `T`, the residue ring `data.kappa P_T =
data.carrier ⧸ P_T` at the order-based kernel-prime `P_T :=
bridge_Bi_kernelToPrime_v2 W hq data T`, viewed as a module over the base residue
ring `Polynomial K ⧸ xIdeal` (`≅ K` via `quotientXAlgEquiv`), has finrank `1`.
Equivalently `data.carrier ⧸ P_T ≃ₐ[K] K`.

* **Silverman**: V.1.1 proof (book p. 138, inertia computation): every
  `F_q`-rational kernel point produces a prime with trivial residue extension. -/
theorem Sinf_finrank_kappa_kernelPrime_eq_one
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel)
    [letI := data.commRing; letI := data.algPoly;
      (bridge_Bi_kernelToPrime_v2 W hq data T).LiesOver
        (Curves.RamificationAtInfinity.xIdeal (k := K))] :
    letI := data.commRing
    letI := data.algPoly
    Module.finrank (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
        (data.kappa (bridge_Bi_kernelToPrime_v2 W hq data T)) = 1 := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.isDomain
  letI := data.moduleFinite
  set P_T : Ideal data.carrier := bridge_Bi_kernelToPrime_v2 W hq data T
  haveI : P_T.IsPrime := bridge_Bi_isPrime_v2 W hq data T
  haveI : (Curves.RamificationAtInfinity.xIdeal (k := K)).IsMaximal :=
    Curves.RamificationAtInfinity.xIdeal_isMaximal
  letI : Algebra (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
      (data.carrier ⧸ P_T) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.LiesOver.over (p := Curves.RamificationAtInfinity.xIdeal (k := K)) (P := P_T)).le
  have h_ge : 1 ≤ Module.finrank (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
      (data.kappa P_T) := by
    have hpos := Ideal.inertiaDeg_pos (Curves.RamificationAtInfinity.xIdeal (k := K)) P_T
    rwa [Ideal.inertiaDeg_algebraMap] at hpos
  have h_surj := Sinf_kappa_kernelPrime_algebraMap_surjective W hq data T
  have h_le : Module.finrank (Polynomial K ⧸ Curves.RamificationAtInfinity.xIdeal (k := K))
      (data.kappa P_T) ≤ 1 :=
    finrank_le_one (1 : data.kappa P_T) fun w ↦ by
      obtain ⟨c, hc⟩ := h_surj w
      exact ⟨c, by rw [Algebra.smul_def, hc, mul_one]⟩
  exact le_antisymm h_le h_ge

/-- **F.1 downstream dispatch — Bridge B(iv): inertia degree at every kernel-prime is `1`.**

* **Silverman**: V.1.1 proof (book p. 138, inertia computation): every
  `F_q`-rational kernel point of `γ = 1 − π` produces a prime with trivial residue
  extension over `K`, so its inertia degree is `1`.
* **Project**: Bridge B(iv), V.1.3 substrate; on the Hasse critical path. -/
theorem bridge_Biv_inertia_eq_one_v2
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (T : (isogOneSub_negFrobenius W hq).kernel) :
    letI := data.commRing
    letI := data.algPoly
    Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K))
        (bridge_Bi_kernelToPrime_v2 W hq data T) = 1 := by
  letI := data.commRing
  letI := data.algPoly
  haveI := bridge_Bi_liesOver_v2 W hq data T
  rw [data.inertiaDeg_eq_finrank_kappa (bridge_Bi_kernelToPrime_v2 W hq data T)]
  exact Sinf_finrank_kappa_kernelPrime_eq_one W hq data T

/-! ### Phase C (deep pass 2026-05-28) — surjective-kernel-to-prime composer

Cleanest alternative witness-form for the sum-of-inertia identity `Σ f_P = #E(F_q)`: the
SURJECTIVITY of the kernel-to-prime map (every prime over `(X)` is some `P_T`) directly
implies the sum identity. The kernel-to-prime image then EQUALS `primesOverFinset` (the
backward inclusion `bridge_Bii_kernelToPrime_mem_primesOverFinset_v2` is shipped axiom-clean),
each `P_T` has `inertiaDeg = 1` (shipped `bridge_Biv_inertia_eq_one_v2`), and the kernel has
`pointCount` elements (shipped `kernel_eq_top_of_hom_eq_id_sub_frobenius`). This factors out
the deep structural content (the surjectivity claim — every prime over `(X)` is a kernel-
prime) into one named witness hypothesis.

Note: this composer's witness IS the same content as the deleted surjectivity residual
(`bridge_Bii_surjective_v2`), but stated as a *hypothesis* of the composer (decoupling the
sum identity from the surjectivity proof chain). -/

/-- **Phase C surjective-kernel-to-prime composer**: given the surjective form of the
kernel-to-prime map (every prime over `(X)` is some `bridge_Bi_kernelToPrime_v2 W hq data T`)
as a single bundled witness, the sum identity `Σ f_P = pointCount` follows by image-equality
+ kernel-cardinality. Pure Finset/cardinality over the DONE assets
(`bridge_Bii_kernelToPrime_mem_primesOverFinset_v2`, `Sinf_kernelToPrime_v2_injective`,
`bridge_Biv_inertia_eq_one_v2`, `kernel_eq_top_of_hom_eq_id_sub_frobenius`). -/
theorem Sinf_sum_inertiaDeg_eq_pointCount_of_surjectivity_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (h_surj :
      letI := data.commRing
      letI := data.isDomain
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∀ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        ∃ T : (isogOneSub_negFrobenius W hq).kernel,
          P = bridge_Bi_kernelToPrime_v2 W hq data T) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
        pointCount W.toAffine := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  letI := data.moduleFinite
  haveI : Finite W.toAffine.Point := Finite.of_fintype _
  haveI : Finite (isogOneSub_negFrobenius W hq).kernel := inferInstance
  haveI : Fintype (isogOneSub_negFrobenius W hq).kernel := Fintype.ofFinite _
  set image : Finset (Ideal data.carrier) :=
    (Finset.univ : Finset (isogOneSub_negFrobenius W hq).kernel).image
      (fun T ↦ bridge_Bi_kernelToPrime_v2 W hq data T) with himage_def
  have h_image_sub : image ⊆
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    intro Q hQ
    rw [himage_def, Finset.mem_image] at hQ
    obtain ⟨T, _, rfl⟩ := hQ
    exact bridge_Bii_kernelToPrime_mem_primesOverFinset_v2 W hq data T
  have h_pof_sub_image :
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier ⊆ image := by
    intro P hP
    obtain ⟨T, rfl⟩ := h_surj P hP
    rw [himage_def, Finset.mem_image]
    exact ⟨T, Finset.mem_univ _, rfl⟩
  have h_image_eq :
      image = IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier :=
    le_antisymm h_image_sub h_pof_sub_image
  rw [← h_image_eq, himage_def,
    Finset.sum_image (fun T₁ _ T₂ _ h_eq ↦
      Sinf_kernelToPrime_v2_injective W hq data h_eq)]
  simp only [bridge_Biv_inertia_eq_one_v2]
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
    ← Nat.card_eq_fintype_card,
    kernel_eq_top_of_hom_eq_id_sub_frobenius W (isogOneSub_negFrobenius W hq) rfl,
    AddSubgroup.card_top]
  exact Nat.card_eq_fintype_card

/-! ### Phase B — V.1.3 squeeze composer (deep pass 2026-05-28)

Cardinality SQUEEZE closure of the sum-of-inertia identity `Σ f_P = #E(F_q)` from the LHS
finrank witness `Σ e_P · f_P = 2 · pointCount`. The witness is supplied by `l6_B3_tower`
(`[K(E):K(f)] = 2 · γ.degree`, axiom-clean in GapSpines) composed with the V.1.3 sharp
residual `isogOneSub_negFrobenius_degree_eq_pointCount` (`γ.degree = pointCount`, proven
via the embeddings classification), via `finrank_adjoin_eq_finrank_LinfAt` and
`finrank_gamma_pullback_x_eq_weightedPoleDegree` (the fundamental identity, shipped
axiom-clean in PoleDivisorFallback).

**Material content:** the squeeze. Given the LHS witness `Σ e_P · f_P = 2 · pointCount`:
* Kernel-prime image (cardinality `pointCount`, all axiom-clean shipped) sums to
  `Σ e_{P_T} · f_{P_T} = Σ 2·1 = 2·pointCount`.
* So `Σ_{image} e·f = Σ_{primesOverFinset} e·f`, complement sum = 0.
* Each prime outside image has `e·f ≥ 1` ⟹ complement is empty.
* Hence `image = primesOverFinset`, so `Σ_{primesOverFinset} f_P = Σ_T 1 = pointCount`.

The composer is pure Finset arithmetic over shipped lemmas (no new sorries). -/

/-- **F.1 Phase B squeeze composer.** Given the witness `Σ e_P · f_P = 2 · pointCount` as a
hypothesis, the sum-of-inertia identity `Σ f_P = pointCount` over the primes above `xIdeal`. -/
theorem Sinf_sum_inertiaDeg_over_xIdeal_eq_pointCount_of_finrank_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (data : Curves.RamificationAtInfinity.Sinf (k := K)
      (((isogOneSub_negFrobenius W hq).pullback (x_gen W)) : W.toAffine.FunctionField))
    (h_finrank_witness :
      letI := data.commRing
      letI := data.isDedekindDomain
      letI := data.algPoly
      ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
        (-(data.ordAt P)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P =
        2 * pointCount W.toAffine) :
    letI := data.commRing
    letI := data.isDomain
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      (Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) P) =
        pointCount W.toAffine := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.isTorsionFree
  letI := data.moduleFinite
  haveI : Finite W.toAffine.Point := Finite.of_fintype _
  haveI : Finite (isogOneSub_negFrobenius W hq).kernel := inferInstance
  haveI : Fintype (isogOneSub_negFrobenius W hq).kernel := Fintype.ofFinite _
  -- Step 1: image of the kernel-to-prime map.
  set image : Finset (Ideal data.carrier) :=
    (Finset.univ : Finset (isogOneSub_negFrobenius W hq).kernel).image
      (fun T ↦ bridge_Bi_kernelToPrime_v2 W hq data T) with himage_def
  -- image ⊆ primesOverFinset (backward direction shipped).
  have h_image_sub : image ⊆
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    intro Q hQ
    rw [himage_def, Finset.mem_image] at hQ
    obtain ⟨T, _, rfl⟩ := hQ
    exact bridge_Bii_kernelToPrime_mem_primesOverFinset_v2 W hq data T
  -- image.card = Nat.card kernel = pointCount.
  have h_card_kernel : Nat.card (isogOneSub_negFrobenius W hq).kernel = pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  -- Step 2: each kernel-prime contributes e_P · f_P = 2 · 1 = 2 to the weighted sum.
  have h_image_sum :
      ∑ Q ∈ image, (-(data.ordAt Q)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q =
        2 * pointCount W.toAffine := by
    rw [himage_def,
      Finset.sum_image (fun T₁ _ T₂ _ h_eq ↦
        Sinf_kernelToPrime_v2_injective W hq data h_eq)]
    -- Each kernel-prime P_T has e = 2 and f = 1, so weighted sum = 2 · pointCount.
    have h_each : ∀ T : (isogOneSub_negFrobenius W hq).kernel,
        (-(data.ordAt (bridge_Bi_kernelToPrime_v2 W hq data T))).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K))
            (bridge_Bi_kernelToPrime_v2 W hq data T) = 2 := by
      intro T
      -- e_{P_T} = 2: ord = -2 ⟹ (-ord).toNat = 2.
      rw [bridge_Biii_ord_eq_neg_two_v2 W hq data T,
          bridge_Biv_inertia_eq_one_v2 W hq data T]
      rfl
    simp only [h_each]
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ,
      ← Nat.card_eq_fintype_card, h_card_kernel]
    ring
  -- Step 3: SQUEEZE — the complement contributes 0, hence is empty.
  -- For every Q in primesOverFinset, e_Q · f_Q ≥ 1.
  haveI hmax : (Curves.RamificationAtInfinity.xIdeal (k := K)).IsMaximal :=
    Curves.RamificationAtInfinity.xIdeal_isMaximal
  have h_pos_each : ∀ Q ∈
      IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier,
      1 ≤ (-(data.ordAt Q)).toNat *
        Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q := by
    intro Q hQ
    rw [IsDedekindDomain.mem_primesOverFinset_iff Curves.RamificationAtInfinity.xIdeal_ne_bot] at hQ
    obtain ⟨hQ_prime, hQ_liesOver⟩ := hQ
    haveI := hQ_prime
    haveI := hQ_liesOver
    have h_f_pos := Ideal.inertiaDeg_pos
      (Curves.RamificationAtInfinity.xIdeal (k := K)) Q
    have h_e_pos : 1 ≤ (-(data.ordAt Q)).toNat := by
      rw [data.toNat_neg_ordAt_eq_ramificationIdx Q]
      have h_ne_zero : Ideal.ramificationIdx
          (Curves.RamificationAtInfinity.xIdeal (k := K)) Q ≠ 0 :=
        Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q
          Curves.RamificationAtInfinity.xIdeal_ne_bot
      omega
    exact Nat.mul_pos h_e_pos h_f_pos
  -- The sum over the complement is 0 + each term ≥ 1 ⟹ complement empty.
  have h_image_eq :
      image = IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier := by
    -- Σ_{total} = Σ_{image} + Σ_{complement} (Finset.sum_sdiff).
    have h_sum_split :=
      Finset.sum_sdiff (s₁ := image)
        (s₂ := IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier)
        h_image_sub
        (f := fun Q ↦ (-(data.ordAt Q)).toNat *
          Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q)
    -- h_sum_split: Σ_{compl} + Σ_{image} = Σ_{total}. Substitute h_finrank_witness + h_image_sum:
    -- Σ_{compl} + 2·pointCount = 2·pointCount, so Σ_{compl} = 0.
    have h_compl_sum_zero :
        ∑ Q ∈ (IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K))
            data.carrier) \ image,
          (-(data.ordAt Q)).toNat *
            Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q = 0 := by
      omega
    -- complement is empty: each term ≥ 1 but sum = 0 ⟹ no terms.
    have h_compl_empty :
        (IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K))
          data.carrier) \ image = ∅ := by
      rcases (IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K))
          data.carrier \ image).eq_empty_or_nonempty with h_emp | h_ne
      · exact h_emp
      · exfalso
        obtain ⟨Q, hQ⟩ := h_ne
        have hQ_total := (Finset.mem_sdiff.mp hQ).1
        have h_pos : 1 ≤ (-(data.ordAt Q)).toNat *
            Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q :=
          h_pos_each Q hQ_total
        have h_ge_one : (1 : ℕ) ≤ ∑ Q' ∈ (IsDedekindDomain.primesOverFinset
              (Curves.RamificationAtInfinity.xIdeal (k := K)) data.carrier) \ image,
            (-(data.ordAt Q')).toNat *
              Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q' :=
          le_trans h_pos (Finset.single_le_sum (f := fun Q' ↦
            (-(data.ordAt Q')).toNat *
              Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K)) Q')
            (fun R _ ↦ Nat.zero_le _) hQ)
        omega
    -- image = primesOverFinset (image ⊆ total + complement is empty).
    apply le_antisymm h_image_sub
    intro Q hQ
    by_contra h_ne
    have hcompl : Q ∈ (IsDedekindDomain.primesOverFinset (Curves.RamificationAtInfinity.xIdeal (k := K))
        data.carrier) \ image := Finset.mem_sdiff.mpr ⟨hQ, h_ne⟩
    rw [h_compl_empty] at hcompl
    exact absurd hcompl (Finset.notMem_empty Q)
  -- Step 4: Σ_{primesOverFinset} f_P = Σ_{image = kernel-image} f_{P_T} = Σ_T 1 = pointCount.
  rw [← h_image_eq, himage_def,
    Finset.sum_image (fun T₁ _ T₂ _ h_eq ↦
      Sinf_kernelToPrime_v2_injective W hq data h_eq)]
  -- Each kernel-prime has inertiaDeg = 1.
  have h_inertia_one : ∀ T : (isogOneSub_negFrobenius W hq).kernel,
      Ideal.inertiaDeg (Curves.RamificationAtInfinity.xIdeal (k := K))
          (bridge_Bi_kernelToPrime_v2 W hq data T) = 1 :=
    fun T ↦ bridge_Biv_inertia_eq_one_v2 W hq data T
  simp only [h_inertia_one]
  rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
    ← Nat.card_eq_fintype_card]
  exact h_card_kernel

end HasseWeil
