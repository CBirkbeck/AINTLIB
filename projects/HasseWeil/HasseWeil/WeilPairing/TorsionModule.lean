/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.TorsionCardEll
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# `E[ℓ] ≅ (ZMod ℓ)²` — the geometric `ℓ`-torsion as a 2-dimensional `ZMod ℓ`-vector space

For `ℓ` prime and `F` algebraically closed with `(ℓ : F) ≠ 0` (i.e. `ℓ ≠ char F`), the geometric
`ℓ`-torsion `E[ℓ] = W.toAffine[(ℓ : ℤ)]` is a 2-dimensional vector space over the field `ZMod ℓ`.

This builds on the axiom-clean cardinality theorem
`HasseWeil.WeilPairing.TorsionGeometric.card_torsion_ell` (`#E[ℓ] = ℓ²`, Silverman III.6.4(a))
and packages the structure-theoretic consequences:

* `card_torsion_ell_nat` — `Nat.card E[ℓ] = ℓ²` (no `ℤ`-coercion);
* `torsion_ell_finite` — `E[ℓ]` is finite;
* the `Module (ZMod ℓ)` structure on `E[ℓ]` (every element is killed by `ℓ`), via
  `AddCommGroup.zmodModule`;
* `finrank_torsion_ell` — `finrank (ZMod ℓ) E[ℓ] = 2`, via `Module.natCard_eq_pow_finrank`;
* `torsion_ell_basis` — a `Basis (Fin 2) (ZMod ℓ) E[ℓ]`, via `Module.finBasisOfFinrankEq`;
* `torsion_ell_linearEquiv` — `E[ℓ] ≃ₗ[ZMod ℓ] (Fin 2 → ZMod ℓ)`, via `Basis.equivFun`.

These are the structures the downstream mod-`ℓ` Galois representation
`ρ_ℓ : End(E) → GL₂(ZMod ℓ)` consumes.

Reference: Silverman III.6.4(a), III.7.
-/

open WeierstrassCurve

namespace HasseWeil.WeilPairing.TorsionGeometric

open HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

section ModuleStructure

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

omit hℓ in
/-- Every element of `E[ℓ]` is killed by `ℓ` (the natural-number scalar action). This is the
defining property feeding the `ZMod ℓ`-module structure. It needs only that `ℓ` annihilates the
torsion subgroup (no hypothesis on the characteristic). -/
theorem nsmul_eq_zero_of_mem_torsion_ell (P : W.toAffine[(ℓ : ℤ)]) :
    ℓ • P = 0 := by
  have hP : (ℓ : ℤ) • P.val = 0 := by
    have := P.property
    rwa [mem_torsionSubgroup] at this
  have hnat : ℓ • P.val = 0 := by
    rw [← natCast_zsmul]; exact hP
  -- transport the annihilation from the carrier into the subgroup
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]
  exact hnat

/-- The `ZMod ℓ`-module structure on `E[ℓ]`, coming from the fact that every element is killed by
`ℓ`. Registered as a `scoped instance` so the `finrank`/`Basis` API can find it. This does not
depend on the characteristic hypothesis `(ℓ : F) ≠ 0`. -/
noncomputable scoped instance torsion_ell_zmodModule :
    Module (ZMod ℓ) W.toAffine[(ℓ : ℤ)] :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_mem_torsion_ell W ℓ)

end ModuleStructure

section Dimension

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [IsAlgClosed F] (hℓF : (ℓ : F) ≠ 0)

include hℓF

omit hℓ in
/-- `#E[ℓ] = ℓ²` as a `Nat.card` equality, dropping the `ℤ`-coercion of
`card_torsion_ell`. -/
theorem card_torsion_ell_nat : Nat.card W.toAffine[(ℓ : ℤ)] = ℓ ^ 2 := by
  have h := card_torsion_ell W (ℓ : ℤ) (by exact_mod_cast hℓF)
  have hcast : ((Nat.card W.toAffine[(ℓ : ℤ)] : ℤ)) = ((ℓ ^ 2 : ℕ) : ℤ) := by
    push_cast; exact h
  exact_mod_cast hcast

/-- `E[ℓ]` is finite: its cardinality is `ℓ² > 0`. -/
theorem torsion_ell_finite : Finite W.toAffine[(ℓ : ℤ)] := by
  apply Nat.finite_of_card_ne_zero
  rw [card_torsion_ell_nat W ℓ hℓF]
  exact pow_ne_zero _ hℓ.out.pos.ne'

/-- **`finrank (ZMod ℓ) E[ℓ] = 2`.** Over the field `ZMod ℓ` (`ℓ` prime), the cardinality formula
`#E[ℓ] = ℓ²` together with `Module.natCard_eq_pow_finrank` (`Nat.card V = (Nat.card K)^finrank`)
forces `ℓ^finrank = ℓ²`, hence `finrank = 2` since `ℓ ≥ 2`. -/
theorem finrank_torsion_ell :
    Module.finrank (ZMod ℓ) W.toAffine[(ℓ : ℤ)] = 2 := by
  haveI := torsion_ell_finite W ℓ hℓF
  have hcard : Nat.card W.toAffine[(ℓ : ℤ)]
      = Nat.card (ZMod ℓ) ^ Module.finrank (ZMod ℓ) W.toAffine[(ℓ : ℤ)] :=
    Module.natCard_eq_pow_finrank
  rw [card_torsion_ell_nat W ℓ hℓF] at hcard
  have hZcard : Nat.card (ZMod ℓ) = ℓ := by
    haveI : NeZero ℓ := ⟨hℓ.out.pos.ne'⟩
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hZcard] at hcard
  -- `ℓ ^ 2 = ℓ ^ finrank`, and `ℓ ≥ 2`, so the exponents agree.
  exact (Nat.pow_right_injective hℓ.out.two_le hcard).symm

/-- A `ZMod ℓ`-basis of `E[ℓ]` indexed by `Fin 2`. -/
noncomputable def torsion_ell_basis :
    Module.Basis (Fin 2) (ZMod ℓ) W.toAffine[(ℓ : ℤ)] :=
  haveI := torsion_ell_finite W ℓ hℓF
  Module.finBasisOfFinrankEq (ZMod ℓ) W.toAffine[(ℓ : ℤ)] (finrank_torsion_ell W ℓ hℓF)

/-- **`E[ℓ] ≅ (ZMod ℓ)²`.** The chosen `Fin 2`-basis exhibits the geometric `ℓ`-torsion as a
`2`-dimensional `ZMod ℓ`-vector space. -/
noncomputable def torsion_ell_linearEquiv :
    W.toAffine[(ℓ : ℤ)] ≃ₗ[ZMod ℓ] (Fin 2 → ZMod ℓ) :=
  (torsion_ell_basis W ℓ hℓF).equivFun

end Dimension

end HasseWeil.WeilPairing.TorsionGeometric
