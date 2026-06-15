/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionModule

/-!
# The `ℓⁿ`-torsion `E[ℓⁿ]` — cardinality and `ZMod (ℓⁿ)`-module structure

For the Tate module `T_ℓ(E) = lim_n E[ℓⁿ]` (Silverman III.7) we need the `ℓⁿ`-torsion
`E[ℓⁿ] = W.toAffine[((ℓ^n : ℕ) : ℤ)]` for every `n`, together with its basic structure. This
file instantiates the existing general-`ℤ` torsion machinery (`card_torsion_ell`, the `ZMod`
module structure) at the integer `(ℓ^n : ℤ)`:

* `pow_cast_ne_zero` (L1) — `((ℓ^n : ℕ) : F) ≠ 0` (`ℓ^n ≠ char F`);
* `card_torsion_ellPow` (L2, = Silverman III.6.4(b) at `m = ℓⁿ`) — `#E[ℓⁿ] = (ℓⁿ)²`;
* `nsmul_eq_zero_of_mem_torsion_ellPow` and `torsion_ellPow_zmodModule` (L3) — every element
  of `E[ℓⁿ]` is killed by `ℓⁿ`, giving the `ZMod (ℓⁿ)`-module structure.

No new geometry: everything is the prime-`ℓ` development re-run at the integer `ℓⁿ`.

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.7, p. 87
("each `E[ℓⁿ]` is a `ℤ/ℓⁿℤ`-module") and III.6.4(b) (`#E[m] = m²`).
-/

open WeierstrassCurve

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  (ℓ : ℕ) [Fact ℓ.Prime]

section CharNeZero

variable (hℓF : (ℓ : F) ≠ 0)

include hℓF

omit [DecidableEq F] [IsAlgClosed F] [Fact ℓ.Prime] in
/-- **L1.** `(ℓⁿ : F) ≠ 0`: if `ℓ ≠ char F` then `ℓⁿ ≠ char F`. -/
theorem pow_cast_ne_zero (n : ℕ) : ((ℓ ^ n : ℕ) : F) ≠ 0 := by
  rw [Nat.cast_pow]
  exact pow_ne_zero n hℓF

omit [Fact ℓ.Prime] in
/-- **L2** (Silverman III.6.4(b) at `m = ℓⁿ`). **`#E[ℓⁿ] = (ℓⁿ)²`.** Instantiates the
general-`ℤ` cardinality theorem `card_torsion_ell` at the integer `(ℓ^n : ℤ)`, using L1 to
discharge `(ℓⁿ : F) ≠ 0`. -/
theorem card_torsion_ellPow (n : ℕ) :
    (Nat.card W.toAffine[((ℓ ^ n : ℕ) : ℤ)] : ℤ) = (ℓ ^ n) ^ 2 := by
  have h : ((((ℓ ^ n : ℕ) : ℤ)) : F) ≠ 0 := by
    rw [Int.cast_natCast]; exact pow_cast_ne_zero ℓ hℓF n
  have := card_torsion_ell W ((ℓ ^ n : ℕ) : ℤ) h
  push_cast at this ⊢
  exact this

end CharNeZero

section ModuleStructure

omit [IsAlgClosed F] [Fact ℓ.Prime] in
/-- **L3 (annihilation).** Every element of `E[ℓⁿ]` is killed by `ℓⁿ` (the natural-number
scalar action). This is the defining property feeding the `ZMod (ℓⁿ)`-module structure; it
needs no hypothesis on the characteristic. -/
theorem nsmul_eq_zero_of_mem_torsion_ellPow (n : ℕ) (P : W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
    (ℓ ^ n) • P = 0 := by
  have hP : ((ℓ ^ n : ℕ) : ℤ) • P.val = 0 := by
    have := P.property
    rwa [mem_torsionSubgroup] at this
  have hnat : (ℓ ^ n) • P.val = 0 := by
    rw [← natCast_zsmul]; exact hP
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
  exact hnat

/-- **L3.** The `ZMod (ℓⁿ)`-module structure on `E[ℓⁿ]`, coming from the fact that every
element is killed by `ℓⁿ`. Registered as a `scoped instance`. -/
noncomputable scoped instance torsion_ellPow_zmodModule (n : ℕ) :
    Module (ZMod (ℓ ^ n)) W.toAffine[((ℓ ^ n : ℕ) : ℤ)] :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_torsion_ellPow W ℓ n)

end ModuleStructure

end HasseWeil.TateModule
