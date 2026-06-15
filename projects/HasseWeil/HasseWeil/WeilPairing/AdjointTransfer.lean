/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PairingAdjoint
import HasseWeil.WeilPairing.PairingNondeg

/-!
# Weil-pairing adjoints: uniqueness, transfer, and additivity (Silverman III.8.2 toolkit)

This file develops the **per-`ℓ` adjoint calculus** of the Weil pairing
`e_ℓ : E[ℓ] × E[ℓ] → F` over an algebraically closed field, the engine behind the
arbitrary-characteristic proof of dual additivity (Silverman III.6.2(c), Exercise 3.31): three
pieces of pure pairing algebra that turn the shipped layer — bilinearity in both slots
(`weilPairing_mul_left` / `weilPairing_mul_right`), nondegeneracy (`weilPairing_nondegenerate`),
and the separable adjoint core (`weilPairing_adjoint_core`) — into statements about *point maps*.

## The adjoint predicate

`IsWeilAdjointOn W ℓ hℓ f δ` says the point map `δ` is an `ℓ`-level Weil adjoint of `f`:
`e_ℓ(f S, T) = e_ℓ(S, δ T)` for all `S, T ∈ E[ℓ]`.  For a separable isogeny `φ` with the two
per-`(ℓ, T)` geometric witnesses of Silverman III.8.2 (translation covariance + the divisor
factorisation, bundled as `AdjointWitnesses`), the stored dual point map is such an adjoint
(`IsWeilAdjointOn.of_adjointWitnesses`, via `weilPairing_adjoint_core`); the same role is played
by `picDual` through `weilPairing_adjoint_picDual`.

## Main results

* `eq_of_weilPairing_eq_right` — **slot-2 separation**: two `ℓ`-torsion points with the same
  pairings against all of `E[ℓ]` are equal (bilinearity + nondegeneracy).
* `weilPairing_zsmul_comm` / `isWeilAdjointOn_mulByInt` — `e_ℓ(n•S, T) = e_ℓ(S, n•T)`:
  `[n]` is its own adjoint (non-vacuity of the predicate, unconditional; the pairing face
  of `[n]^ = [n]`).
* `IsWeilAdjointOn.unique` — **adjoint uniqueness** on `E[ℓ]`: two adjoints of the same `f`
  agree on `E[ℓ]`.
* `torsion_mem_range_of_comp` — **the image trick**: if `f ∘ δ' = [m]` and `gcd(ℓ, m) = 1`,
  then `E[ℓ] ⊆ im f` (pure group theory; the second composition `φ ∘ φ̂ = [deg φ]` supplies
  `f ∘ δ' = [m]` for a genuine isogeny).
* `IsWeilAdjointOn.of_comp` — **adjoint transfer**: any point map `δ` with `δ ∘ f = [m]`
  inherits adjointness from an existing adjoint `δ₀` with `δ₀ ∘ f = [m]`, for `gcd(ℓ, m) = 1`.
  This moves the adjoint identity from `picDual`-style constructions to the canonical dual's
  point map.
* `IsWeilAdjointOn.add` — **THE ADDITIVITY COMPUTATION** (the heart of III.6.2(c)): if
  `fg = f + g` pointwise and `δf, δg, δfg` are adjoints of `f, g, fg`, then
  `δfg = δf + δg` on `E[ℓ]`:
  `e(S, δfg T) = e(fg S, T) = e(f S + g S, T) = e(f S, T)·e(g S, T) = e(S, δf T)·e(S, δg T)
  = e(S, δf T + δg T)`, then separation.

The assembly into the dual-additivity statement (union over infinitely many `ℓ`, then the
function-field separation engine) is `HasseWeil/EC/IsogenyAG/DualAdditivity.lean`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1–III.8.2, III.6.2(c), Exercise 3.31.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-! ### Group-theoretic preliminaries (no pairing) -/

/-- `ℓ`-torsion is preserved by any `AddMonoidHom`. -/
theorem smul_map_eq_zero {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (f : M →+ N) {ℓ : ℤ} {S : M} (hS : ℓ • S = 0) : ℓ • f S = 0 := by
  rw [← map_zsmul, hS, map_zero]

/-- **The image trick** (pure group theory): if `f ∘ δ' = [m]` and `gcd(ℓ, m) = 1`, every
`ℓ`-torsion point is in the image of `f`.  Writing `a·ℓ + b·m = 1`, the preimage of `T` is
`δ'(b • T)`: `f(δ'(b•T)) = m•(b•T) = (1 − a·ℓ)•T = T`.  For a genuine isogeny `φ` the
hypothesis `f ∘ δ' = [m]` is the second composition `φ ∘ φ̂ = [deg φ]`
(`EC.Isogeny.compose_canonicalDual`). -/
theorem torsion_mem_range_of_comp {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {f : M →+ N} {δ' : N →+ M} {ℓ m : ℤ} (hcop : IsCoprime ℓ m)
    (hfδ' : ∀ z : N, f (δ' z) = m • z) {T : N} (hT : ℓ • T = 0) :
    ∃ z : M, f z = T := by
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨δ' (b • T), ?_⟩
  calc f (δ' (b • T)) = m • b • T := hfδ' (b • T)
    _ = b • m • T + a • ℓ • T := by rw [hT, smul_zero, add_zero, smul_comm]
    _ = (a * ℓ + b * m) • T := by rw [add_smul, mul_smul, mul_smul, add_comm]
    _ = T := by rw [hab, one_smul]

/-- **Point maps with the same `[m]`-composition agree on the image of `f`** (pure group
theory): if `δ₀ ∘ f = [m] = δ ∘ f` and `T = f z`, then `δ T = m • z = δ₀ T`. -/
theorem comp_eqOn_range {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {f : M →+ N} {δ₀ δ : N →+ M} {m : ℤ}
    (hδ₀ : ∀ z : M, δ₀ (f z) = m • z) (hδ : ∀ z : M, δ (f z) = m • z)
    {T : N} (hrange : ∃ z : M, f z = T) : δ T = δ₀ T := by
  obtain ⟨z, rfl⟩ := hrange
  rw [hδ, hδ₀]

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]

local notation "KE" => W.toAffine.FunctionField

/-! ### Slot-2 separation -/

section Separation

variable [IsAlgClosed F]

/-- **Slot-2 separation**: two `ℓ`-torsion points `T₁, T₂` with
`e_ℓ(S, T₁) = e_ℓ(S, T₂)` for every `S ∈ E[ℓ]` are equal.  The quotient point `T₁ − T₂`
pairs to `1` against all of `E[ℓ]` (slot-2 bilinearity `weilPairing_mul_right` + cancelling
the nonzero value `e_ℓ(S, T₂)`), so it is `O` by nondegeneracy
(`weilPairing_nondegenerate`). -/
theorem eq_of_weilPairing_eq_right (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    {T₁ T₂ : W.toAffine.Point} (hT₁ : ℓ • T₁ = 0) (hT₂ : ℓ • T₂ = 0)
    (h : ∀ (S : W.toAffine.Point) (hS : ℓ • S = 0),
      weilPairing W ℓ hℓ S T₁ hS hT₁ = weilPairing W ℓ hℓ S T₂ hS hT₂) :
    T₁ = T₂ := by
  have hD : ℓ • (T₁ - T₂) = 0 := by rw [smul_sub, hT₁, hT₂, sub_zero]
  -- the quotient point pairs to `1` against everything
  have hkey : ∀ (S : W.toAffine.Point) (hS : ℓ • S = 0),
      weilPairing W ℓ hℓ S (T₁ - T₂) hS hD = 1 := by
    intro S hS
    have hadd : ℓ • (T₁ - T₂ + T₂) = 0 := by rw [sub_add_cancel]; exact hT₁
    have h1 := weilPairing_mul_right W ℓ hℓ S (T₁ - T₂) T₂ hS hD hT₂ hadd
    have h2 : weilPairing W ℓ hℓ S (T₁ - T₂ + T₂) hS hadd =
        weilPairing W ℓ hℓ S T₁ hS hT₁ :=
      weilPairing_congr_right W ℓ hℓ hS hadd hT₁ (sub_add_cancel T₁ T₂)
    have h3 : (1 : F) * weilPairing W ℓ hℓ S T₂ hS hT₂ =
        weilPairing W ℓ hℓ S (T₁ - T₂) hS hD * weilPairing W ℓ hℓ S T₂ hS hT₂ := by
      rw [one_mul]
      exact (h S hS).symm.trans (h2.symm.trans h1)
    exact (mul_right_cancel₀ (weilPairing_ne_zero W ℓ hℓ S T₂ hS hT₂) h3).symm
  -- nondegeneracy forces the quotient point to vanish
  exact sub_eq_zero.mp (weilPairing_nondegenerate W ℓ hℓ (T₁ - T₂) hD hkey)

end Separation

/-! ### `[n]` moves across the pairing: `e_ℓ(n•S, T) = e_ℓ(S, n•T)`

The `ℤ`-scalar self-adjointness of multiplication, from the `nsmul` power laws in both
slots; the negative case cancels against the `natAbs` power. -/

section ZsmulComm

variable [IsAlgClosed F]

/-- **`[n]` is self-adjoint for the Weil pairing**: `e_ℓ(n•S, T) = e_ℓ(S, n•T)` for every
`n : ℤ` (Silverman III.8.1, bilinearity; the pairing-side face of `[n]^ = [n]`).  For
`n ≥ 0` both sides are `e_ℓ(S, T)^n`; for `n < 0` both sides cancel against
`e_ℓ(S, T)^{|n|}` to `1`. -/
theorem weilPairing_zsmul_comm (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (n : ℤ)
    (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hnS : ℓ • (n • S) = 0) (hnT : ℓ • (n • T) = 0) :
    weilPairing W ℓ hℓ (n • S) T hnS hT = weilPairing W ℓ hℓ S (n • T) hS hnT := by
  set k := n.natAbs with hk
  have hkS : ℓ • ((k : ℕ) • S) = 0 := smul_nsmul_eq_zero W ℓ S hS k
  have hkT : ℓ • ((k : ℕ) • T) = 0 := smul_nsmul_eq_zero_right W ℓ T hT k
  rcases Int.natAbs_eq n with hn | hn
  · -- `n = k ≥ 0`: both sides are the `k`-th power
    have e1 : weilPairing W ℓ hℓ (n • S) T hnS hT =
        weilPairing W ℓ hℓ ((k : ℕ) • S) T hkS hT :=
      weilPairing_congr_left W ℓ hℓ hnS hkS hT (by rw [hn, natCast_zsmul])
    have e2 : weilPairing W ℓ hℓ S (n • T) hS hnT =
        weilPairing W ℓ hℓ S ((k : ℕ) • T) hS hkT :=
      weilPairing_congr_right W ℓ hℓ hS hnT hkT (by rw [hn, natCast_zsmul])
    rw [e1, e2, weilPairing_nsmul_left W ℓ hℓ S T hS hT k hkS,
      weilPairing_nsmul_right W ℓ hℓ S T hS hT k hkT]
  · -- `n = −k`: both sides cancel against `e_ℓ(S, T)^k` to `1`
    have hcancelS : n • S + (k : ℕ) • S = 0 := by
      rw [← natCast_zsmul S k, ← add_smul, hn, neg_add_cancel, zero_smul]
    have hcancelT : n • T + (k : ℕ) • T = 0 := by
      rw [← natCast_zsmul T k, ← add_smul, hn, neg_add_cancel, zero_smul]
    have hsumS : ℓ • (n • S + (k : ℕ) • S) = 0 := by rw [smul_add, hnS, hkS, add_zero]
    have hsumT : ℓ • (n • T + (k : ℕ) • T) = 0 := by rw [smul_add, hnT, hkT, add_zero]
    -- left slot: `e(n•S, T) · e(S,T)^k = 1`
    have h1 : weilPairing W ℓ hℓ (n • S) T hnS hT *
        weilPairing W ℓ hℓ S T hS hT ^ k = 1 := by
      rw [← weilPairing_nsmul_left W ℓ hℓ S T hS hT k hkS,
        ← weilPairing_mul_left W ℓ hℓ (n • S) ((k : ℕ) • S) T hnS hkS hT hsumS,
        weilPairing_congr_left W ℓ hℓ hsumS
          (by simp : ℓ • (0 : W.toAffine.Point) = 0) hT hcancelS]
      exact weilPairing_refl_left W ℓ hℓ T hT _
    -- right slot: `e(S, n•T) · e(S,T)^k = 1`
    have h2 : weilPairing W ℓ hℓ S (n • T) hS hnT *
        weilPairing W ℓ hℓ S T hS hT ^ k = 1 := by
      rw [← weilPairing_nsmul_right W ℓ hℓ S T hS hT k hkT,
        ← weilPairing_mul_right W ℓ hℓ S (n • T) ((k : ℕ) • T) hS hnT hkT hsumT,
        weilPairing_congr_right W ℓ hℓ hS hsumT
          (by simp : ℓ • (0 : W.toAffine.Point) = 0) hcancelT]
      exact weilPairing_refl_right W ℓ hℓ S hS _
    exact mul_right_cancel₀
      (pow_ne_zero k (weilPairing_ne_zero W ℓ hℓ S T hS hT)) (h1.trans h2.symm)

end ZsmulComm

/-! ### The adjoint predicate and its calculus -/

section Adjoint

variable [IsAlgClosed F]

/-- **The `ℓ`-level Weil-adjoint predicate**: `δ` is an adjoint of `f` on `E[ℓ]` when
`e_ℓ(f S, T) = e_ℓ(S, δ T)` for all `S, T ∈ E[ℓ]` (all torsion side-proofs quantified, so
instances are insensitive to proof terms).  For a separable isogeny `φ` this holds for
`f = φ.toAddMonoidHom` and `δ` its dual point map (Silverman III.8.2); see
`IsWeilAdjointOn.of_adjointWitnesses` and `weilPairing_adjoint_picDual`. -/
def IsWeilAdjointOn (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0)
    (f δ : W.toAffine.Point →+ W.toAffine.Point) : Prop :=
  ∀ (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0)
    (hfS : ℓ • f S = 0) (hδT : ℓ • δ T = 0),
    weilPairing W ℓ hℓ (f S) T hfS hT = weilPairing W ℓ hℓ S (δ T) hS hδT

/-- **Non-vacuity: `[n]` is its own adjoint** at every level `ℓ` — the predicate-level face
of `[n]^ = [n]` (`mulByIntDual_mulByIntSelf`), unconditional.  Direct from
`weilPairing_zsmul_comm` (the stored point map of `mulByInt` is definitionally `n • ·`). -/
theorem isWeilAdjointOn_mulByInt (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (n : ℤ) :
    IsWeilAdjointOn W ℓ hℓ (mulByInt W.toAffine n).toAddMonoidHom
      (mulByInt W.toAffine n).toAddMonoidHom := fun S T hS hT hfS hδT =>
  weilPairing_zsmul_comm W ℓ hℓ n S T hS hT hfS hδT

variable {W}

/-- **Adjoint uniqueness on `E[ℓ]`** (Silverman III.8.2 uniqueness): two `ℓ`-level adjoints
of the same point map agree on `E[ℓ]`.  Immediate from slot-2 separation. -/
theorem IsWeilAdjointOn.unique {ℓ : ℤ} {hℓ : (ℓ : F) ≠ 0}
    {f δ₁ δ₂ : W.toAffine.Point →+ W.toAffine.Point}
    (h₁ : IsWeilAdjointOn W ℓ hℓ f δ₁) (h₂ : IsWeilAdjointOn W ℓ hℓ f δ₂)
    {T : W.toAffine.Point} (hT : ℓ • T = 0) :
    δ₁ T = δ₂ T := by
  refine eq_of_weilPairing_eq_right W ℓ hℓ (smul_map_eq_zero δ₁ hT)
    (smul_map_eq_zero δ₂ hT) (fun S hS => ?_)
  exact (h₁ S T hS hT (smul_map_eq_zero f hS) (smul_map_eq_zero δ₁ hT)).symm.trans
    (h₂ S T hS hT (smul_map_eq_zero f hS) (smul_map_eq_zero δ₂ hT))

/-- **Adjoint transfer** (the image trick in action): if `δ₀` is an `ℓ`-level adjoint of `f`
with `δ₀ ∘ f = [m]`, then *any* point map `δ` with `δ ∘ f = [m]` is also an adjoint —
provided `gcd(ℓ, m) = 1` and the second composition `f ∘ δ' = [m]` holds for some `δ'`
(so that `E[ℓ] ⊆ im f` and the two candidate adjoints agree on `E[ℓ]`).

This is the bridge from a `picDual`-style construction (which carries the adjoint identity)
to the canonical dual's point map (which carries the `[m]`-composition identities). -/
theorem IsWeilAdjointOn.of_comp {ℓ m : ℤ} {hℓ : (ℓ : F) ≠ 0}
    {f δ₀ δ δ' : W.toAffine.Point →+ W.toAffine.Point}
    (hadj₀ : IsWeilAdjointOn W ℓ hℓ f δ₀)
    (hδ₀ : ∀ z : W.toAffine.Point, δ₀ (f z) = m • z)
    (hδ : ∀ z : W.toAffine.Point, δ (f z) = m • z)
    (hfδ' : ∀ z : W.toAffine.Point, f (δ' z) = m • z)
    (hcop : IsCoprime ℓ m) :
    IsWeilAdjointOn W ℓ hℓ f δ := by
  intro S T hS hT hfS hδT
  -- the two candidate adjoints agree at `T ∈ E[ℓ] ⊆ im f`
  have heq : δ T = δ₀ T :=
    comp_eqOn_range hδ₀ hδ (torsion_mem_range_of_comp hcop hfδ' hT)
  exact (hadj₀ S T hS hT hfS (smul_map_eq_zero δ₀ hT)).trans
    (weilPairing_congr_right W ℓ hℓ hS (smul_map_eq_zero δ₀ hT) hδT heq.symm)

/-- **The additivity computation** (the per-`ℓ` heart of Silverman III.6.2(c)): if
`fg = f + g` pointwise and `δf, δg, δfg` are `ℓ`-level adjoints of `f, g, fg`, then
`δfg T = δf T + δg T` for every `T ∈ E[ℓ]`.

For every `S ∈ E[ℓ]`:
`e(S, δfg T) = e(fg S, T) = e(f S + g S, T) = e(f S, T) · e(g S, T)`
`= e(S, δf T) · e(S, δg T) = e(S, δf T + δg T)` — bilinearity in slot 1 splits the sum of
point maps, the three adjoint identities move everything to slot 2, and bilinearity in
slot 2 reassembles; conclude by slot-2 separation. -/
theorem IsWeilAdjointOn.add {ℓ : ℤ} {hℓ : (ℓ : F) ≠ 0}
    {f g fg δf δg δfg : W.toAffine.Point →+ W.toAffine.Point}
    (hf : IsWeilAdjointOn W ℓ hℓ f δf) (hg : IsWeilAdjointOn W ℓ hℓ g δg)
    (hfg : IsWeilAdjointOn W ℓ hℓ fg δfg)
    (hsum : ∀ P : W.toAffine.Point, fg P = f P + g P)
    {T : W.toAffine.Point} (hT : ℓ • T = 0) :
    δfg T = δf T + δg T := by
  have hδfT := smul_map_eq_zero δf hT
  have hδgT := smul_map_eq_zero δg hT
  have hδfgT := smul_map_eq_zero δfg hT
  have hsumT : ℓ • (δf T + δg T) = 0 := by rw [smul_add, hδfT, hδgT, add_zero]
  refine eq_of_weilPairing_eq_right W ℓ hℓ hδfgT hsumT (fun S hS => ?_)
  have hfS := smul_map_eq_zero f hS
  have hgS := smul_map_eq_zero g hS
  have hfgS := smul_map_eq_zero fg hS
  have hsumS : ℓ • (f S + g S) = 0 := by rw [smul_add, hfS, hgS, add_zero]
  calc weilPairing W ℓ hℓ S (δfg T) hS hδfgT
      = weilPairing W ℓ hℓ (fg S) T hfgS hT := (hfg S T hS hT hfgS hδfgT).symm
    _ = weilPairing W ℓ hℓ (f S + g S) T hsumS hT :=
        weilPairing_congr_left W ℓ hℓ hfgS hsumS hT (hsum S)
    _ = weilPairing W ℓ hℓ (f S) T hfS hT * weilPairing W ℓ hℓ (g S) T hgS hT :=
        weilPairing_mul_left W ℓ hℓ (f S) (g S) T hfS hgS hT hsumS
    _ = weilPairing W ℓ hℓ S (δf T) hS hδfT * weilPairing W ℓ hℓ S (δg T) hS hδgT := by
        rw [hf S T hS hT hfS hδfT, hg S T hS hT hgS hδgT]
    _ = weilPairing W ℓ hℓ S (δf T + δg T) hS hsumT :=
        (weilPairing_mul_right W ℓ hℓ S (δf T) (δg T) hS hδfT hδgT hsumT).symm

end Adjoint

/-! ### Discharging the adjoint predicate from the geometric witnesses -/

section Witnesses

variable [IsAlgClosed F]

/-- **The per-`(ℓ, T)` geometric witnesses of the separable adjoint** (Silverman III.8.2),
bundled: for every `T ∈ E[ℓ]`,

* translation covariance `τ_S^*(φ^* g_T) = φ^*(τ_{φS}^* g_T)` for all `S ∈ E[ℓ]` (the
  function-field shadow of `φ ∘ (·+S) = (·+φS) ∘ φ`), and
* the divisor factorisation `φ^* g_T = c · (g_{δT} · [ℓ]^* k)` (separability ⟹ the
  multiplicity-free pullback `φ^*((T)−(O)) ∼ (δT)−(O)`, pulled back by `[ℓ]`),

exactly the hypotheses of `weilPairing_adjoint_core` with dual point `U := δ T`.  These are
the standing per-isogeny witness costs of the pairing layer (cf. `ProjOrdTransport`,
`Naturality`), carried because the abstract `Isogeny` stores `pullback` and
`toAddMonoidHom` as independent fields. -/
def AdjointWitnesses (ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (φ : Isogeny W.toAffine W.toAffine)
    (δ : W.toAffine.Point →+ W.toAffine.Point) : Prop :=
  ∀ (T : W.toAffine.Point) (hT : ℓ • T = 0),
    (∀ S : W.toAffine.Point, ℓ • S = 0 →
      translateAlgEquivOfPoint W S (φ.pullback (weilFunction W ℓ hℓ T hT)) =
        φ.pullback (translateAlgEquivOfPoint W (φ.toAddMonoidHom S)
          (weilFunction W ℓ hℓ T hT))) ∧
    ∃ (c : F) (k : KE),
      φ.pullback (weilFunction W ℓ hℓ T hT) =
        algebraMap F KE c *
          (weilFunction W ℓ hℓ (δ T) (smul_map_eq_zero δ hT) *
            (mulByInt W.toAffine ℓ).pullback k)

variable {W}

/-- **The geometric witnesses produce an adjoint**: `AdjointWitnesses W ℓ hℓ φ δ` discharges
`IsWeilAdjointOn W ℓ hℓ φ.toAddMonoidHom δ`, via `weilPairing_adjoint_core` at each pair. -/
theorem IsWeilAdjointOn.of_adjointWitnesses {ℓ : ℤ} {hℓ : (ℓ : F) ≠ 0}
    {φ : Isogeny W.toAffine W.toAffine} {δ : W.toAffine.Point →+ W.toAffine.Point}
    (hw : AdjointWitnesses W ℓ hℓ φ δ) :
    IsWeilAdjointOn W ℓ hℓ φ.toAddMonoidHom δ := by
  intro S T hS hT hfS hδT
  obtain ⟨hcomm, c, k, hfact⟩ := hw T hT
  exact weilPairing_adjoint_core W ℓ hℓ φ S T (δ T) hS hT hδT hfS (hcomm S hS) hfact

end Witnesses

end HasseWeil.WeilPairing
