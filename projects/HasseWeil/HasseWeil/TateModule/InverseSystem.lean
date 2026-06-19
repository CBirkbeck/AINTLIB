/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.TateModule.TorsionPow

/-!
# The inverse system `… → E[ℓⁿ⁺¹] --[ℓ]--> E[ℓⁿ] → …`

The Tate module `T_ℓ(E) = lim_n E[ℓⁿ]` (Silverman III.7) is the projective limit of the
`ℓⁿ`-torsion groups along the **multiplication-by-`ℓ`** connecting maps
`[ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]`. This file defines those connecting maps and records their
basic naturality:

* `tateConn n : E[ℓⁿ⁺¹] →+ E[ℓⁿ]` (L5) — multiplication by `ℓ`, restricted; well-defined
  because `ℓⁿ · (ℓ · P) = ℓⁿ⁺¹ · P = 0` for `P ∈ E[ℓⁿ⁺¹]`;
* `tateConn_castHom_compat` (L6) — `tateConn` is semilinear along the canonical reduction
  `ZMod.castHom : ZMod (ℓⁿ⁺¹) → ZMod (ℓⁿ)`: both scalar actions reduce to the natural-number
  `•`-action, with which the `AddMonoidHom` `[ℓ]` commutes.

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.7, p. 87
("the natural maps `E[ℓⁿ⁺¹] --[ℓ]--> E[ℓⁿ]`") and p. 88 ("commutes with the
multiplication-by-`ℓ` map").
-/

open WeierstrassCurve

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime]

section Connecting

/-- **L5.** The connecting map `[ℓ] : E[ℓⁿ⁺¹] → E[ℓⁿ]` of the Tate inverse system, as an
`AddMonoidHom`. It is multiplication by `ℓ` (the integer `ℓ`-action on `E.Point`), restricted
from `E[ℓⁿ⁺¹]` to `E[ℓⁿ]`: if `P ∈ E[ℓⁿ⁺¹]` then `ℓⁿ · (ℓ · P) = ℓⁿ⁺¹ · P = 0`, so `ℓ · P ∈ E[ℓⁿ]`.
-/
noncomputable def tateConn (n : ℕ) :
    W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)] →+ W.toAffine[((ℓ ^ n : ℕ) : ℤ)] :=
  ((zsmulAddGroupHom (ℓ : ℤ)).comp (W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]).subtype).codRestrict _
    (fun P ↦ by
      rw [mem_torsionSubgroup]
      have hP : ((ℓ ^ (n + 1) : ℕ) : ℤ) • (P : W.toAffine.Point) = 0 := by
        have := P.property; rwa [mem_torsionSubgroup] at this
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
        zsmulAddGroupHom_apply]
      rw [smul_smul]
      have hcast : ((ℓ ^ n : ℕ) : ℤ) * (ℓ : ℤ) = ((ℓ ^ (n + 1) : ℕ) : ℤ) := by
        push_cast; ring
      rw [hcast, hP])

omit [IsAlgClosed F] [Fact ℓ.Prime] in
@[simp] theorem tateConn_coe (n : ℕ) (P : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
    (tateConn W ℓ n P : W.toAffine.Point) = (ℓ : ℤ) • (P : W.toAffine.Point) :=
  rfl

end Connecting

section Semilinear

open scoped HasseWeil.WeilPairing.TorsionGeometric

/-- For an `m`-torsion element `x` (so the `ZMod m`-module structure applies) the scalar action
of `c : ZMod m` is the integer action of any integer lift `(ZMod.cast c : ℤ)`. -/
private theorem zmodModule_smul_eq_zsmul_cast {m : ℕ} {G : Type*} [AddCommGroup G]
    [Module (ZMod m) G] (c : ZMod m) (x : G) : c • x = (ZMod.cast c : ℤ) • x := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast c]
  rw [Int.cast_smul_eq_zsmul]

omit [IsAlgClosed F] [Fact ℓ.Prime] in
/-- **L6.** `tateConn` is semilinear along the canonical reduction
`ZMod.castHom : ZMod (ℓⁿ⁺¹) → ZMod (ℓⁿ)`. Both `ZMod`-scalar actions are the underlying
natural-number `•`-action, and the additive map `[ℓ]` commutes with `n • ·`; the `castHom`
bookkeeping reduces the `ZMod (ℓⁿ⁺¹)`-scalar to its image in `ZMod (ℓⁿ)`. -/
theorem tateConn_castHom_compat (n : ℕ) (c : ZMod (ℓ ^ (n + 1)))
    (P : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) :
    tateConn W ℓ n (c • P) =
      (ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) c) • tateConn W ℓ n P := by
  set d : ZMod (ℓ ^ n) := ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) c with hd
  -- Reduce both `ZMod`-actions to `ℤ`-actions and use `map_zsmul`.
  rw [zmodModule_smul_eq_zsmul_cast c P, map_zsmul, zmodModule_smul_eq_zsmul_cast d]
  -- Remaining: `(cast c : ℤ) • tateConn P = (cast d : ℤ) • tateConn P` in `E[ℓⁿ]`.
  -- Both multipliers agree modulo `ℓⁿ`, which annihilates the `ℓⁿ`-torsion `tateConn P`.
  -- `cast c ≡ cast d [ZMOD ℓⁿ]`, so their difference is `ℓⁿ * t`.
  -- From the `ZMod (ℓⁿ)` equality `↑(cast c) = ↑(cast d)`, lift to an integer congruence.
  have h1 : (ZMod.cast c : ZMod (ℓ ^ n)) = d := by
    rw [hd]; exact ZMod.castHom_apply (h := pow_dvd_pow ℓ n.le_succ) c
  have h2 : (ZMod.cast d : ZMod (ℓ ^ n)) = d := ZMod.cast_id _ d
  have hdiff : ((ℓ ^ n : ℕ) : ℤ) ∣ (ZMod.cast c : ℤ) - (ZMod.cast d : ℤ) := by
    have hz : ((((ZMod.cast c : ℤ) - (ZMod.cast d : ℤ)) : ℤ) : ZMod (ℓ ^ n)) = 0 := by
      rw [Int.cast_sub, ZMod.intCast_cast, ZMod.intCast_cast, h1, h2, sub_self]
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_pow] at hz
  obtain ⟨t, ht⟩ := hdiff
  -- `cast c = cast d + ℓⁿ * t`, and `ℓⁿ • (tateConn P) = 0`.
  have hcd : (ZMod.cast c : ℤ) = (ZMod.cast d : ℤ) + ((ℓ ^ n : ℕ) : ℤ) * t := by
    rw [← ht]; ring
  rw [hcd, add_zsmul, mul_comm, mul_zsmul]
  have hkill : ((ℓ ^ n : ℕ) : ℤ) • (tateConn W ℓ n P) = 0 := by
    have := nsmul_eq_zero_of_mem_torsion_ellPow W ℓ n (tateConn W ℓ n P)
    rwa [← natCast_zsmul] at this
  rw [hkill, smul_zero, add_zero]

end Semilinear

end HasseWeil.TateModule
