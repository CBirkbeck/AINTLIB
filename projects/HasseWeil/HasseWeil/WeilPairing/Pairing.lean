/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.DivisorTranslate
import HasseWeil.WeilPairing.TorsionGeometric
import HasseWeil.WeilPairing.TorsionModule

/-!
# The Weil pairing `e_ℓ(S, T)` (Silverman III.8, ticket T-R2-PAIRING-DEF)

This file assembles the **definition** of the finite-level Weil pairing
`e_ℓ : E[ℓ] × E[ℓ] → F` over an algebraically closed field `F`, via the
reviewer-endorsed **constant-ratio** approach.

## The construction (Silverman III.8.1)

For `T ∈ E[ℓ]`, the fibre-difference divisor `[ℓ]^*(T) − [ℓ]^*(O)` is principal
(`pullbackDiv_sub_isPrincipal`): there is a function `g_T = weilFunction W ℓ T`
with `div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)`.  For `S ∈ E[ℓ]` the translation
`τ_S = translateAlgEquivOfPoint W S` preserves this divisor (the fibre-shift
`projectiveDivisorOf_translate_weilFunction_div_eq_zero`), so `τ_S g_T / g_T`
has trivial divisor, hence is a nonzero constant `e_ℓ(S, T) ∈ F`
(`pairing_const_of_transport`).  This constant is the **Weil pairing value**.

## Main definitions / results

* `mulByEllTorsionHom_surjective` / `exists_preimage_of_torsion` — over `K̄`, the
  multiplication map `[ℓ] : E[ℓ²] → E[ℓ]` is **surjective** (proved by a pure
  cardinality count: `#E[ℓ²]/#E[ℓ] = ℓ² = #ker`, via
  `AddMonoidHom.surjective_of_card_ker_le_div`).  In particular every `T ∈ E[ℓ]`
  has a preimage `P₀` under `[ℓ]` with `ℓ² • P₀ = 0`.  **No deep curve-theory
  surjectivity is needed.**
* `weilFunction W ℓ T` — a chosen Weil function `g_T` (via `Classical.choose`).
* `weilPairing W ℓ S T : F` — the constant ratio `e_ℓ(S, T)`.
* `weilPairing_ne_zero` — `e_ℓ(S, T) ≠ 0`.
* `weilPairing_mul_left` — **bilinearity in the first slot**: `e_ℓ(S₁+S₂, T) =
  e_ℓ(S₁, T)·e_ℓ(S₂, T)`.  (`S ↦ e_ℓ(S, T)` is a group homomorphism `E[ℓ] → Fˣ`.)
* `weilPairing_pow_eq_one` — `e_ℓ(S, T) ^ ℓ.natAbs = 1` (the root-of-unity core),
  proved purely from bilinearity: `e_ℓ(S, T) ^ ℓ.natAbs = e_ℓ(ℓ.natAbs • S, T) =
  e_ℓ(O, T) = 1` since `ℓ.natAbs • S = 0` for `S ∈ E[ℓ]`.  **No divisor-pullback
  functoriality (`g_T^ℓ ∈ [ℓ]^* K(E)`) is needed.**
* `weilPairing_refl_left` — `e_ℓ(O, T) = 1` (sanity check; `τ_O = id`).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- `Nat.card E[ℓ] = ℓ.natAbs²` over `K̄` (the `ℕ`-valued form of
`card_torsion_ell`, whose statement is the `ℤ`-coerced `= ℓ²`). -/
private theorem natCard_torsion_eq [IsAlgClosed F] (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    Nat.card W.toAffine[(ℓ : ℤ)] = ℓ.natAbs ^ 2 := by
  have hZ : (Nat.card W.toAffine[(ℓ : ℤ)] : ℤ) = ((ℓ.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [card_torsion_ell W ℓ hℓ]; push_cast; rw [sq_abs]
  exact_mod_cast hZ

section Surjectivity

variable [IsAlgClosed F]

/-- The restriction of `[ℓ]` to `E[ℓ²] → E[ℓ]`, as an `AddMonoidHom` between the
torsion subgroups: `P ↦ ℓ • P`.  Well-defined because `ℓ • (ℓ • P) = ℓ² • P = 0`
when `P ∈ E[ℓ²]`. -/
noncomputable def mulByEllTorsionHom (ℓ : ℤ) : W.toAffine[(ℓ ^ 2 : ℤ)] →+ W.toAffine[(ℓ : ℤ)] where
  toFun P := ⟨ℓ • P.val, by
    rw [mem_torsionSubgroup, smul_smul, ← pow_two]
    exact (mem_torsionSubgroup _ _ _).mp P.property⟩
  map_zero' := by ext; simp
  map_add' P Q := by ext; simp [smul_add]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] [IsAlgClosed F] in
@[simp]
theorem mulByEllTorsionHom_val (ℓ : ℤ) (P : W.toAffine[(ℓ ^ 2 : ℤ)]) :
    (mulByEllTorsionHom W ℓ P).val = ℓ • P.val := rfl

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **`[ℓ] : E[ℓ²] → E[ℓ]` is surjective** over `K̄`, via a cardinality count
(`#E[ℓ²] / #E[ℓ] = ℓ⁴ / ℓ² = ℓ²`). -/
theorem mulByEllTorsionHom_surjective (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    Function.Surjective (mulByEllTorsionHom W ℓ) := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  have hℓ2 : ((ℓ ^ 2 : ℤ) : F) ≠ 0 := by push_cast; exact pow_ne_zero 2 hℓ
  set n := ℓ.natAbs with hn
  have hn0 : n ≠ 0 := by rw [hn]; exact Int.natAbs_ne_zero.mpr hℓ0
  have hcard_ell : Nat.card W.toAffine[(ℓ : ℤ)] = n ^ 2 := natCard_torsion_eq W ℓ hℓ
  have hcard_ell2 : Nat.card W.toAffine[(ℓ ^ 2 : ℤ)] = n ^ 4 := by
    rw [natCard_torsion_eq W (ℓ ^ 2) hℓ2, Int.natAbs_pow, ← pow_mul]
  have : Finite W.toAffine[(ℓ : ℤ)] :=
    Nat.finite_of_card_ne_zero (by rw [hcard_ell]; exact pow_ne_zero _ hn0)
  have : Finite W.toAffine[(ℓ ^ 2 : ℤ)] :=
    Nat.finite_of_card_ne_zero (by rw [hcard_ell2]; exact pow_ne_zero _ hn0)
  have hker_le : Nat.card (mulByEllTorsionHom W ℓ).ker ≤
      Nat.card W.toAffine[(ℓ : ℤ)] := by
    refine Nat.card_le_card_of_injective
      (f := fun P : (mulByEllTorsionHom W ℓ).ker ↦
        (⟨P.val.val, by
          rw [mem_torsionSubgroup]
          have hP0 : (mulByEllTorsionHom W ℓ) P.val = 0 := P.property
          simpa using congrArg Subtype.val hP0⟩ : W.toAffine[(ℓ : ℤ)])) ?_
    rintro ⟨⟨P, hP⟩, hPker⟩ ⟨⟨Q, hQ⟩, hQker⟩ h
    simpa using h
  have hdiv : Nat.card W.toAffine[(ℓ ^ 2 : ℤ)] / Nat.card W.toAffine[(ℓ : ℤ)]
      = n ^ 2 := by
    rw [hcard_ell, hcard_ell2]
    rw [show n ^ 4 = n ^ 2 * n ^ 2 by ring,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (pow_ne_zero _ hn0))]
  refine AddMonoidHom.surjective_of_card_ker_le_div (mulByEllTorsionHom W ℓ) ?_
  rw [hdiv, ← hcard_ell]; exact hker_le

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- **Preimage of a torsion point.** For `T ∈ E[ℓ]` there is `P₀ : E` with
`ℓ • P₀ = T` and `ℓ² • P₀ = 0`. -/
theorem exists_preimage_of_torsion (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    ∃ P₀ : W.toAffine.Point, ℓ • P₀ = T ∧ (ℓ ^ 2 : ℤ) • P₀ = 0 := by
  have hTmem : T ∈ W.toAffine[(ℓ : ℤ)] := (mem_torsionSubgroup _ _ _).mpr hT
  obtain ⟨P₀, hP₀⟩ := mulByEllTorsionHom_surjective W ℓ hℓ ⟨T, hTmem⟩
  refine ⟨P₀.val, ?_, (mem_torsionSubgroup _ _ _).mp P₀.property⟩
  simpa using congrArg Subtype.val hP₀

end Surjectivity

section WeilFunction

variable [IsAlgClosed F]

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- `ker[ℓ]` is finite over `K̄`: its cardinality is `ℓ² > 0`. -/
theorem mulByInt_ker_finite (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker := by
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; simp at hℓ
  have : Finite W.toAffine[(ℓ : ℤ)] := Nat.finite_of_card_ne_zero (by
    rw [natCard_torsion_eq W ℓ hℓ]; exact pow_ne_zero _ (Int.natAbs_ne_zero.mpr hℓ0))
  exact this

omit [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] in
/-- `Nat.card (ker[ℓ]) = ℓ²` (the integer `ℓ²`, as a natural-number `ZSMul`). -/
theorem nat_card_mulByInt_ker (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) :
    (Nat.card (mulByInt W.toAffine ℓ).toAddMonoidHom.ker : ℤ) = ℓ ^ 2 :=
  card_torsion_ell W ℓ hℓ

/-- **The fibre-difference divisor `[ℓ]^*(T) − [ℓ]^*(O)` is principal** for
`T ∈ E[ℓ]`: applies `pullbackDiv_sub_isPrincipal` with the preimage `P₀` of `T`
(from `exists_preimage_of_torsion`) and the annihilation `ℓ² • P₀ = 0`. -/
theorem weilFunction_isPrincipal (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    (W_smooth W).ProjIsPrincipal
      (pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) 0) := by
  obtain ⟨P₀, hP₀_eq, hP₀_ann⟩ := exists_preimage_of_torsion W ℓ hℓ T hT
  refine pullbackDiv_sub_isPrincipal
    (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
    (mulByInt_ker_finite W ℓ hℓ) (P₀ := P₀) ?_ ?_
  · rwa [mulByInt_apply]
  · rwa [← natCast_zsmul, nat_card_mulByInt_ker W ℓ hℓ]

/-- **The chosen Weil function `g_T`** for `T ∈ E[ℓ]`: a nonzero function with
`div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)` (the fibre-difference divisor), extracted from
`weilFunction_isPrincipal` via `Classical.choose`. -/
noncomputable def weilFunction (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) : KE :=
  Classical.choose (weilFunction_isPrincipal W ℓ hℓ T hT)

/-- The chosen Weil function `g_T` is nonzero. -/
theorem weilFunction_ne_zero (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    weilFunction W ℓ hℓ T hT ≠ 0 :=
  (Classical.choose_spec (weilFunction_isPrincipal W ℓ hℓ T hT)).1

/-- The chosen Weil function `g_T` has divisor `[ℓ]^*(T) − [ℓ]^*(O)`. -/
theorem weilFunction_divisor (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) :
    (W_smooth W).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) =
      pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) T -
        pullbackDiv (W := W.toAffine) (mulByInt W.toAffine ℓ).toAddMonoidHom
          (mulByInt_ker_finite W ℓ hℓ) 0 :=
  (Classical.choose_spec (weilFunction_isPrincipal W ℓ hℓ T hT)).2

end WeilFunction

section Pairing

variable [IsAlgClosed F]

/-- The transport hypothesis: for `S ∈ E[ℓ]`, the quotient `τ_S g_T / g_T` has
trivial projective divisor.  This is the fibre-shift payoff
`projectiveDivisorOf_translate_weilFunction_div_eq_zero` applied to `g_T`. -/
theorem weilFunction_transport (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    (W_smooth W).projectiveDivisorOf
        (translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT) /
          weilFunction W ℓ hℓ T hT) = 0 := by
  refine projectiveDivisorOf_translate_weilFunction_div_eq_zero
    W S (mulByInt W.toAffine ℓ).toAddMonoidHom (mulByInt_ker_finite W ℓ hℓ) T
    ?_ (weilFunction W ℓ hℓ T hT) (weilFunction_ne_zero W ℓ hℓ T hT)
    (weilFunction_divisor W ℓ hℓ T hT)
  rwa [mulByInt_apply]

/-- **The Weil pairing value** `e_ℓ(S, T) : F` (Silverman III.8.1), defined as the
constant ratio `τ_S g_T / g_T` extracted by `pairing_const_of_transport`. -/
noncomputable def weilPairing (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) : F :=
  Classical.choose
    (pairing_const_of_transport (W := W.toAffine)
      (translateAlgEquivOfPoint W S).toRingEquiv
      (weilFunction W ℓ hℓ T hT) (weilFunction_ne_zero W ℓ hℓ T hT)
      (weilFunction_transport W ℓ hℓ S T hS hT))

/-- The defining property of `e_ℓ(S, T)`: it is a nonzero scalar with
`τ_S g_T = e_ℓ(S, T) • g_T`. -/
theorem weilPairing_spec (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    weilPairing W ℓ hℓ S T hS hT ≠ 0 ∧
      (translateAlgEquivOfPoint W S).toRingEquiv (weilFunction W ℓ hℓ T hT) =
        algebraMap F KE (weilPairing W ℓ hℓ S T hS hT) *
          weilFunction W ℓ hℓ T hT :=
  Classical.choose_spec
    (pairing_const_of_transport (W := W.toAffine)
      (translateAlgEquivOfPoint W S).toRingEquiv
      (weilFunction W ℓ hℓ T hT) (weilFunction_ne_zero W ℓ hℓ T hT)
      (weilFunction_transport W ℓ hℓ S T hS hT))

/-- **`e_ℓ(S, T) ≠ 0`.** -/
theorem weilPairing_ne_zero (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    weilPairing W ℓ hℓ S T hS hT ≠ 0 :=
  (weilPairing_spec W ℓ hℓ S T hS hT).1

/-- The translation relation `τ_S g_T = e_ℓ(S, T) • g_T` (the scalar form). -/
theorem weilPairing_translate (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT) =
      algebraMap F KE (weilPairing W ℓ hℓ S T hS hT) *
        weilFunction W ℓ hℓ T hT :=
  (weilPairing_spec W ℓ hℓ S T hS hT).2

end Pairing

section Refl

variable [IsAlgClosed F]

/-- **`e_ℓ(O, T) = 1`** (Silverman III.8.1, the pairing is trivial on `O`). -/
theorem weilPairing_refl_left (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (T : W.toAffine.Point) (hT : ℓ • T = 0) (h0 : ℓ • (0 : W.toAffine.Point) = 0) :
    weilPairing W ℓ hℓ 0 T h0 hT = 1 := by
  refine pairing_const_refl (W := W.toAffine)
    (weilFunction W ℓ hℓ T hT) (weilFunction_ne_zero W ℓ hℓ T hT) ?_
  exact weilPairing_translate W ℓ hℓ 0 T h0 hT

end Refl

section Bilinearity

variable [IsAlgClosed F]

/-- **Bilinearity of the Weil pairing in the first slot** (Silverman III.8.1, the
pairing is a homomorphism `E[ℓ] → μ_ℓ` in `S`): `e_ℓ(S₁+S₂, T) =
e_ℓ(S₁, T)·e_ℓ(S₂, T)`. -/
theorem weilPairing_mul_left (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S₁ S₂ T : W.toAffine.Point) (hS₁ : ℓ • S₁ = 0) (hS₂ : ℓ • S₂ = 0)
    (hT : ℓ • T = 0) (h₁₂ : ℓ • (S₁ + S₂) = 0) :
    weilPairing W ℓ hℓ (S₁ + S₂) T h₁₂ hT =
      weilPairing W ℓ hℓ S₁ T hS₁ hT * weilPairing W ℓ hℓ S₂ T hS₂ hT := by
  have hbil := pairing_const_mul (W := W.toAffine)
    (τ₁ := (translateAlgEquivOfPoint W S₂).toRingEquiv)
    (τ₂ := (translateAlgEquivOfPoint W S₁).toRingEquiv)
    (τ₁₂ := (translateAlgEquivOfPoint W (S₁ + S₂)).toRingEquiv)
    (g := weilFunction W ℓ hℓ T hT) (weilFunction_ne_zero W ℓ hℓ T hT)
    (c₁ := weilPairing W ℓ hℓ S₂ T hS₂ hT)
    (c₂ := weilPairing W ℓ hℓ S₁ T hS₁ hT)
    (c₁₂ := weilPairing W ℓ hℓ (S₁ + S₂) T h₁₂ hT)
    (hτ₁F := (translateAlgEquivOfPoint W S₂).commutes)
    (hcomp := translateAlgEquivOfPoint_add_apply W S₁ S₂)
    (hc₁ := weilPairing_translate W ℓ hℓ S₂ T hS₂ hT)
    (hc₂ := weilPairing_translate W ℓ hℓ S₁ T hS₁ hT)
    (hc₁₂ := weilPairing_translate W ℓ hℓ (S₁ + S₂) T h₁₂ hT)
  rw [hbil, mul_comm]

/-- `e_ℓ(S, T)` depends only on the points `S, T` (the `ℓ • S = 0` proof is
propositional, hence irrelevant): equal first arguments give equal values. -/
theorem weilPairing_congr_left (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    {S S' T : W.toAffine.Point} (hS : ℓ • S = 0) (hS' : ℓ • S' = 0)
    (hT : ℓ • T = 0) (h : S = S') :
    weilPairing W ℓ hℓ S T hS hT = weilPairing W ℓ hℓ S' T hS' hT := by
  subst h; rfl

omit [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing] [IsAlgClosed F] in
/-- `ℓ • (n • S) = 0` whenever `ℓ • S = 0` (the scalars commute). -/
theorem smul_nsmul_eq_zero (ℓ : ℤ) (S : W.toAffine.Point) (hS : ℓ • S = 0)
    (n : ℕ) : ℓ • (n • S) = 0 := by
  rw [smul_comm, hS, smul_zero]

/-- **Power form of bilinearity**: `e_ℓ(n • S, T) = e_ℓ(S, T) ^ n` for `n : ℕ`. -/
theorem weilPairing_nsmul_left (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (n : ℕ) (h_ns : ℓ • (n • S) = 0) :
    weilPairing W ℓ hℓ (n • S) T h_ns hT = (weilPairing W ℓ hℓ S T hS hT) ^ n := by
  induction n with
  | zero =>
    rw [weilPairing_congr_left W ℓ hℓ h_ns
      (by simp : ℓ • (0 : W.toAffine.Point) = 0) hT (zero_smul ℕ S), pow_zero]
    exact weilPairing_refl_left W ℓ hℓ T hT _
  | succ k ih =>
    have hk : ℓ • (k • S) = 0 := smul_nsmul_eq_zero W ℓ S hS k
    have hsum : ℓ • (k • S + S) = 0 := by rw [smul_add, hk, hS, add_zero]
    rw [weilPairing_congr_left W ℓ hℓ h_ns hsum hT (succ_nsmul S k),
      weilPairing_mul_left W ℓ hℓ (k • S) S T hk hS hT hsum, ih hk, pow_succ]

end Bilinearity

section RootOfUnity

variable [IsAlgClosed F]

/-- **The Weil pairing is an `ℓ`-th root of unity** (Silverman III.8.1, `μ_ℓ`):
`e_ℓ(S, T) ^ ℓ.natAbs = 1`. -/
theorem weilPairing_pow_eq_one (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) :
    (weilPairing W ℓ hℓ S T hS hT) ^ ℓ.natAbs = 1 := by
  have hnat : (ℓ.natAbs : ℕ) • S = 0 := by
    have hz : ((ℓ.natAbs : ℤ)) • S = 0 := by
      rcases Int.natAbs_eq ℓ with h | h
      · rw [← h]; exact hS
      · rw [show ((ℓ.natAbs : ℤ)) = -ℓ by lia, neg_smul, hS, neg_zero]
    rwa [natCast_zsmul] at hz
  rw [← weilPairing_nsmul_left W ℓ hℓ S T hS hT ℓ.natAbs (by rw [hnat]; simp)]
  exact (weilPairing_congr_left W ℓ hℓ _
    (by simp : ℓ • (0 : W.toAffine.Point) = 0) hT hnat).trans
    (weilPairing_refl_left W ℓ hℓ T hT _)

end RootOfUnity

end HasseWeil.WeilPairing
