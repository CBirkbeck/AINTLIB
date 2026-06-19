/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.TateModule.PadicLimZMod
import HasseWeil.TateModule.TorsionPowStructure

/-!
# The Tate module `T_ℓ(E) = lim_n E[ℓⁿ] ≅ ℤ_ℓ²` (Silverman III.7, Prop 7.1a)

This file builds the **Tate module** of an elliptic curve as the projective limit of the
`ℓⁿ`-torsion groups along the multiplication-by-`ℓ` connecting maps `tateConn`, equips it with its
natural `ℤ_[ℓ]`-module structure, and proves the structure theorem
`T_ℓ(E) ≅ ℤ_[ℓ]²` (Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), §III.7, Prop 7.1a).

## Main definitions and results

* `tateCompat W ℓ : AddSubgroup (Π n, E[ℓⁿ])` (**L8**) — the additive group of `tateConn`-compatible
  sequences `{ f | ∀ n, tateConn n (f (n+1)) = f n }`. Mathlib has **no** generic module
  inverse limit, so the object is hand-built.
* `Module ℤ_[ℓ] (tateCompat W ℓ)` (**L8**) — the `ℓ`-adic module structure: the scalar `z : ℤ_[ℓ]`
  acts on coordinate `n` through the truncation `PadicInt.toZModPow n z : ZMod (ℓⁿ)`. The actions
  are compatible across `n` by `tateConn_castHom_compat` together with
  `PadicInt.cast_toZModPow`.
* `tateModule W ℓ` (**L8**) — the Tate module, i.e. `tateCompat W ℓ` carrying the above structure.
* `tateModuleEquiv W ℓ hℓF : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ])` (**L10**, Prop 7.1a) — the
  structure theorem. It transports the per-`n` isomorphisms `E[ℓⁿ] ≅ (ZMod ℓⁿ)²`
  (`torsion_ellPow_linearEquiv`) through the limit, using the **coherence** `tateConn_tateBasis`
  (the connecting square commutes) so that the level-`n` coordinates assemble into a compatible
  `ZMod`-sequence and hence, via `padicIntEquivLimZMod` (`ℤ_[ℓ] ≅ lim ZMod (ℓⁿ)`), into an element
  of `ℤ_[ℓ]`.

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed.), §III.7, pp. 87–88:
the Definition of `T_ℓ(E) = lim_n E[ℓⁿ]` ("natural structure as a `ℤ_ℓ`-module") and Prop 7.1a
(`T_ℓ(E) ≅ ℤ_ℓ × ℤ_ℓ` for `ℓ ≠ char K`).
-/

open WeierstrassCurve

namespace HasseWeil.TateModule

open HasseWeil HasseWeil.WeilPairing.TorsionGeometric
open scoped HasseWeil.WeilPairing.TorsionGeometric

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-! ## L8 — The Tate module as a hand-built inverse limit -/

section TateCompat

/-- **L8.** The carrier of the Tate module: the additive subgroup of the product `Π n, E[ℓⁿ]`
consisting of the `tateConn`-compatible sequences. Its element type is the projective-limit subtype
`{ f : Π n, E[ℓⁿ] // ∀ n, tateConn W ℓ n (f (n + 1)) = f n }`. -/
def tateCompat : AddSubgroup (Π n : ℕ, W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) where
  carrier := { f | ∀ n, tateConn W ℓ n (f (n + 1)) = f n }
  add_mem' {f g} hf hg n := by simp only [Pi.add_apply, map_add, hf n, hg n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {f} hf n := by simp only [Pi.neg_apply, map_neg, hf n]

omit [IsAlgClosed F] hℓ in
@[simp] theorem mem_tateCompat (f : Π n : ℕ, W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) :
    f ∈ tateCompat W ℓ ↔ ∀ n, tateConn W ℓ n (f (n + 1)) = f n := Iff.rfl

omit [IsAlgClosed F] hℓ in
/-- The defining compatibility of an element of `tateCompat`. -/
theorem tateCompat_compat (f : tateCompat W ℓ) (n : ℕ) :
    tateConn W ℓ n (f.val (n + 1)) = f.val n := f.property n

/-- The `ℓ`-adic scalar action on a compatible sequence: the scalar `z : ℤ_[ℓ]` acts on coordinate
`n` through the truncation `PadicInt.toZModPow n z : ZMod (ℓⁿ)`. The result is again compatible:
on coordinate `n` we have, by `tateConn_castHom_compat`,
`tateConn (toZModPow (n+1) z • f (n+1)) = castHom (toZModPow (n+1) z) • tateConn (f (n+1))`, then
`castHom (toZModPow (n+1) z) = toZModPow n z` (`PadicInt.cast_toZModPow`) and
`tateConn (f (n+1)) = f n` (compatibility of `f`). -/
noncomputable instance : SMul ℤ_[ℓ] (tateCompat W ℓ) where
  smul z f := ⟨fun n ↦ PadicInt.toZModPow n z • f.val n, by
    intro n
    rw [tateConn_castHom_compat, tateCompat_compat]
    congr 1
    rw [ZMod.castHom_apply, PadicInt.cast_toZModPow (p := ℓ) n (n + 1) n.le_succ z]⟩

omit [IsAlgClosed F] in
@[simp] theorem smul_tateCompat_val (z : ℤ_[ℓ]) (f : tateCompat W ℓ) (n : ℕ) :
    ((z • f : tateCompat W ℓ) : Π n : ℕ, W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) n =
      PadicInt.toZModPow n z • (f : Π n : ℕ, W.toAffine[((ℓ ^ n : ℕ) : ℤ)]) n := rfl

/-- **L8.** The `ℤ_[ℓ]`-module structure on the Tate module. Each axiom is checked coordinatewise
and reduces, via `smul_tateCompat_val`, to the corresponding `ZMod (ℓⁿ)`-module axiom together with
the ring-hom property of `PadicInt.toZModPow n` (`map_one`, `map_mul`, `map_add`). -/
noncomputable instance : Module ℤ_[ℓ] (tateCompat W ℓ) where
  one_smul f := by
    apply Subtype.ext; funext n
    rw [smul_tateCompat_val, map_one, one_smul]
  mul_smul z w f := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, map_mul, mul_smul]
  smul_zero z := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, AddSubgroup.coe_zero, Pi.zero_apply, smul_zero]
  smul_add z f g := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, AddSubgroup.coe_add, Pi.add_apply, smul_add]
  add_smul z w f := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, map_add, add_smul, AddSubgroup.coe_add, Pi.add_apply]
  zero_smul f := by
    apply Subtype.ext; funext n
    simp only [smul_tateCompat_val, map_zero, zero_smul, AddSubgroup.coe_zero, Pi.zero_apply]

/-- **L8.** The **Tate module** `T_ℓ(E) = lim_n E[ℓⁿ]` of the elliptic curve, as a `ℤ_[ℓ]`-module.
It is `tateCompat W ℓ` (the `tateConn`-compatible sequences) carrying the `ℓ`-adic module structure
above. -/
abbrev tateModule : Type _ := tateCompat W ℓ

end TateCompat

/-! ## L10 — The structure theorem `T_ℓ(E) ≅ ℤ_ℓ²` -/

section StructureTheorem

variable (hℓF : (ℓ : F) ≠ 0)

include hℓF

/-- **Naturality of the per-`n` coordinate isomorphisms.** The level-`n` coordinate of the
connecting image `tateConn n P` equals the `castHom`-reduction of the level-`(n+1)` coordinate of
`P`. This is
the commuting square `tateConn ↔ castHom` and follows from the **coherence** `tateConn_tateBasis`
of the basis sequence (`tateBasis (n+1)` lifts `tateBasis n` along `[ℓ]`). -/
theorem torsion_ellPow_linearEquiv_tateConn (n : ℕ)
    (P : W.toAffine[((ℓ ^ (n + 1) : ℕ) : ℤ)]) (i : Fin 2) :
    torsion_ellPow_linearEquiv W ℓ hℓF n (tateConn W ℓ n P) i =
      ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n))
        (torsion_ellPow_linearEquiv W ℓ hℓF (n + 1) P i) := by
  -- Abbreviate the coordinates of `P` in the level-`(n+1)` basis.
  set v : Fin 2 → ZMod (ℓ ^ (n + 1)) := (tateBasis W ℓ hℓF (n + 1)).equivFun P with hv
  -- Expand `P = Σ_j v_j • tateBasis (n+1) j`, apply `tateConn` (semilinear, additive), and use the
  -- coherence `tateConn (tateBasis (n+1) j) = tateBasis n j`.
  have hPexp : tateConn W ℓ n P =
      ∑ j, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (v j) •
        tateBasis W ℓ hℓF n j := by
    have hP : P = ∑ j, v j • tateBasis W ℓ hℓF (n + 1) j := by
      rw [hv]
      exact ((tateBasis W ℓ hℓF (n + 1)).sum_equivFun P).symm
    rw [hP, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [tateConn_castHom_compat, tateConn_tateBasis]
  -- Reading off coordinate `i` via `equivFun`.
  rw [torsion_ellPow_linearEquiv, hPexp,
    show (∑ j, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (v j) •
        tateBasis W ℓ hℓF n j) =
      (tateBasis W ℓ hℓF n).equivFun.symm
        (fun j ↦ ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (v j)) from
      (Module.Basis.equivFun_symm_apply _ _).symm,
    LinearEquiv.apply_symm_apply]
  rfl

/-- For `g : Fin 2 → ℤ_[ℓ]`, the `E`-sequence
`n ↦ (linearEquiv n).symm (fun i => toZModPow n (g i))` is `tateConn`-compatible, so it is an
element of `tateCompat`. The compatibility is the inverse form of
`torsion_ellPow_linearEquiv_tateConn` together with `PadicInt.cast_toZModPow`. -/
theorem tateConn_invFun_compat (g : Fin 2 → ℤ_[ℓ]) (n : ℕ) :
    tateConn W ℓ n
        ((torsion_ellPow_linearEquiv W ℓ hℓF (n + 1)).symm
          (fun i ↦ PadicInt.toZModPow (n + 1) (g i))) =
      (torsion_ellPow_linearEquiv W ℓ hℓF n).symm (fun i ↦ PadicInt.toZModPow n (g i)) := by
  -- Apply the (injective) level-`n` isomorphism and compare coordinatewise.
  apply (torsion_ellPow_linearEquiv W ℓ hℓF n).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rw [torsion_ellPow_linearEquiv_tateConn, LinearEquiv.apply_symm_apply]
  -- `castHom (toZModPow (n+1) (g j)) = toZModPow n (g j)`.
  rw [ZMod.castHom_apply, PadicInt.cast_toZModPow n (n + 1) n.le_succ]

/-- The forward coordinate sequence `n ↦ (linearEquiv n (f n)) i` of a compatible `E`-sequence `f`
is a `castHom`-compatible `ZMod`-sequence, hence an element of `compatSubring ℓ`
(`= lim ZMod (ℓⁿ)`). -/
noncomputable def tateForwardCompat (f : tateModule W ℓ) (i : Fin 2) : compatSubring ℓ :=
  ⟨fun n ↦ torsion_ellPow_linearEquiv W ℓ hℓF n (f.val n) i, by
    intro n
    rw [← torsion_ellPow_linearEquiv_tateConn W ℓ hℓF n (f.val (n + 1)) i, tateCompat_compat]⟩

@[simp] theorem tateForwardCompat_val (f : tateModule W ℓ) (i : Fin 2) (n : ℕ) :
    (tateForwardCompat W ℓ hℓF f i).val n = torsion_ellPow_linearEquiv W ℓ hℓF n (f.val n) i := rfl

/-- `tateForwardCompat` is additive in the sequence `f`. -/
theorem tateForwardCompat_add (f g : tateModule W ℓ) (i : Fin 2) :
    tateForwardCompat W ℓ hℓF (f + g) i =
      tateForwardCompat W ℓ hℓF f i + tateForwardCompat W ℓ hℓF g i := by
  apply Subtype.ext; funext n
  rw [tateForwardCompat_val, AddSubgroup.coe_add, Pi.add_apply, map_add]
  rfl

/-- `tateForwardCompat` carries the `ℓ`-adic scalar to multiplication by the truncation tower
`padicToLimZMod ℓ z` in the limit ring; this is the `ZMod (ℓⁿ)`-linearity of
`torsion_ellPow_linearEquiv` together with `smul_eq_mul` on `ZMod (ℓⁿ)`. -/
theorem tateForwardCompat_smul (z : ℤ_[ℓ]) (f : tateModule W ℓ) (i : Fin 2) :
    tateForwardCompat W ℓ hℓF (z • f) i =
      padicToLimZMod ℓ z * tateForwardCompat W ℓ hℓF f i := by
  apply Subtype.ext; funext n
  rw [tateForwardCompat_val, smul_tateCompat_val, map_smul]
  change PadicInt.toZModPow n z • torsion_ellPow_linearEquiv W ℓ hℓF n (f.val n) i = _
  rw [Subring.coe_mul, Pi.mul_apply, padicToLimZMod_val, tateForwardCompat_val, smul_eq_mul]

/-- **L10 (Prop 7.1a).** `T_ℓ(E) ≅ ℤ_[ℓ]²` as `ℤ_[ℓ]`-modules. The per-`n` isomorphisms
`E[ℓⁿ] ≅ (ZMod ℓⁿ)²` (`torsion_ellPow_linearEquiv`) are natural in the connecting maps
(`torsion_ellPow_linearEquiv_tateConn`, from the coherence `tateConn_tateBasis`), so the level-`n`
coordinates of a compatible sequence assemble — componentwise in `Fin 2` — into compatible
`ZMod`-sequences, which `padicIntEquivLimZMod` identifies with elements of `ℤ_[ℓ]`. -/
noncomputable def tateModuleEquiv : tateModule W ℓ ≃ₗ[ℤ_[ℓ]] (Fin 2 → ℤ_[ℓ]) where
  toFun f i := (padicIntEquivLimZMod ℓ).symm (tateForwardCompat W ℓ hℓF f i)
  map_add' f g := by
    funext i
    simp only [Pi.add_apply, tateForwardCompat_add, map_add]
  map_smul' z f := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, tateForwardCompat_smul, map_mul]
    rw [show padicToLimZMod ℓ z = padicIntEquivLimZMod ℓ z from rfl,
      RingEquiv.symm_apply_apply, smul_eq_mul]
  invFun g :=
    ⟨fun n ↦ (torsion_ellPow_linearEquiv W ℓ hℓF n).symm (fun i ↦ PadicInt.toZModPow n (g i)),
      tateConn_invFun_compat W ℓ hℓF g⟩
  left_inv f := by
    apply Subtype.ext; funext n
    change (torsion_ellPow_linearEquiv W ℓ hℓF n).symm
        (fun i ↦ PadicInt.toZModPow n ((padicIntEquivLimZMod ℓ).symm
          (tateForwardCompat W ℓ hℓF f i))) = f.val n
    have hcoord : (fun i ↦ PadicInt.toZModPow n ((padicIntEquivLimZMod ℓ).symm
        (tateForwardCompat W ℓ hℓF f i))) =
        torsion_ellPow_linearEquiv W ℓ hℓF n (f.val n) := by
      funext i
      rw [show (padicIntEquivLimZMod ℓ).symm (tateForwardCompat W ℓ hℓF f i)
          = limZModToPadic ℓ (tateForwardCompat W ℓ hℓF f i) from rfl,
        toZModPow_limZModToPadic, tateForwardCompat_val]
    rw [hcoord, LinearEquiv.symm_apply_apply]
  right_inv g := by
    funext i
    apply (padicIntEquivLimZMod ℓ).injective
    rw [RingEquiv.apply_symm_apply]
    apply Subtype.ext; funext n
    change (tateForwardCompat W ℓ hℓF
        ⟨fun n ↦ (torsion_ellPow_linearEquiv W ℓ hℓF n).symm
          (fun i ↦ PadicInt.toZModPow n (g i)), _⟩ i).val n = (padicIntEquivLimZMod ℓ (g i)).val n
    rw [tateForwardCompat_val]
    change torsion_ellPow_linearEquiv W ℓ hℓF n
        ((torsion_ellPow_linearEquiv W ℓ hℓF n).symm (fun i ↦ PadicInt.toZModPow n (g i))) i =
      (padicIntEquivLimZMod ℓ (g i)).val n
    rw [LinearEquiv.apply_symm_apply]
    rfl

end StructureTheorem

end HasseWeil.TateModule
