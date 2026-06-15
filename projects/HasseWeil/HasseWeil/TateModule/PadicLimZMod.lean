/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Ring.Pi

/-!
# `ℤ_[ℓ] ≅ lim_n ZMod (ℓ^n)` — the `ℓ`-adic integers as the projective limit of the `ZMod` tower

This file proves the load-bearing reusable bridge for the Tate-module development
(Silverman III.7): the ring of `ℓ`-adic integers `ℤ_[ℓ]` is the projective limit of the
tower `… → ZMod (ℓ^{n+1}) → ZMod (ℓ^n) → …` with connecting maps the canonical reductions
`ZMod.castHom`.

Concretely, let
```
compatSubring ℓ : Subring (Π n : ℕ, ZMod (ℓ^n))
```
be the subring of *compatible sequences*: those `f` with
`ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) (f (n+1)) = f n` for every `n`. Then
```
padicIntEquivLimZMod ℓ : ℤ_[ℓ] ≃+* ↥(compatSubring ℓ)
```
is a ring isomorphism. The element type `↥(compatSubring ℓ)` **is** the projective-limit subtype
`{ f : Π n, ZMod (ℓ^n) //`
`∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) (f (n+1)) = f n }`
(its membership predicate is exactly the displayed compatibility condition).

The forward map sends `z` to the sequence of truncations `n ↦ PadicInt.toZModPow n z`
(compatible by `PadicInt.zmod_cast_comp_toZModPow`); the inverse is `PadicInt.lift` applied
to the projection family, and the round-trips are the universal property
(`PadicInt.lift_spec`, `PadicInt.ext_of_toZModPow`).

Reference: Silverman, *The Arithmetic of Elliptic Curves* (2nd ed), §III.7, p. 87
("we mimic the inverse limit construction of the `ℓ`-adic integers `ℤ_ℓ` from the finite
groups `ℤ/ℓⁿℤ`"). Mathlib API: `Mathlib/NumberTheory/Padics/RingHoms.lean`.
-/

open PadicInt

namespace HasseWeil.TateModule

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The connecting reduction `ZMod (ℓ^(n+1)) →+* ZMod (ℓ^n)` of the tower. -/
abbrev limZModCast (n : ℕ) : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ n) :=
  ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n))

omit [Fact ℓ.Prime] in
/-- The general (non-adjacent) compatibility of a sequence implies the adjacent one. -/
theorem adjacentCompat_of_compat {f : Π n : ℕ, ZMod (ℓ ^ n)}
    (h : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k₁)) (f k₂) = f k₁) (n : ℕ) :
    limZModCast ℓ n (f (n + 1)) = f n :=
  h n (n + 1) n.le_succ

omit [Fact ℓ.Prime] in
/-- An adjacent-compatible sequence is compatible for every `k₁ ≤ k₂` (telescoping). -/
theorem compat_of_adjacentCompat {f : Π n : ℕ, ZMod (ℓ ^ n)}
    (h : ∀ n, limZModCast ℓ n (f (n + 1)) = f n)
    (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k₁)) (f k₂) = f k₁ := by
  induction k₂, hk using Nat.le_induction with
  | base => simp [ZMod.castHom_self]
  | succ k₂ hk ih =>
    have hstep : ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k₁))
        (limZModCast ℓ k₂ (f (k₂ + 1))) = f k₁ := by rw [h k₂]; exact ih
    rw [← hstep, limZModCast, ← RingHom.comp_apply, ZMod.castHom_comp]

/-- The subring of compatible sequences inside `Π n, ZMod (ℓ^n)`.
Its element type `↥(compatSubring ℓ)` **is** the projective-limit subtype
`{ f : Π n, ZMod (ℓ^n) //`
`∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) (f (n+1)) = f n }`. -/
def compatSubring : Subring (Π n : ℕ, ZMod (ℓ ^ n)) where
  carrier := { f | ∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (f (n + 1)) = f n }
  mul_mem' {f g} hf hg n := by
    simp only [Pi.mul_apply, map_mul, hf n, hg n]
  one_mem' n := by simp only [Pi.one_apply, map_one]
  add_mem' {f g} hf hg n := by
    simp only [Pi.add_apply, map_add, hf n, hg n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {f} hf n := by
    simp only [Pi.neg_apply, map_neg, hf n]

omit [Fact ℓ.Prime] in
@[simp] theorem mem_compatSubring (f : Π n : ℕ, ZMod (ℓ ^ n)) :
    f ∈ compatSubring ℓ ↔
      ∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ ^ n)) (f (n + 1)) = f n := Iff.rfl

/-- The `n`-th projection from the compatible-sequence subring to `ZMod (ℓ^n)`, as a ring hom. -/
def compatProj (n : ℕ) : compatSubring ℓ →+* ZMod (ℓ ^ n) :=
  (Pi.evalRingHom (fun n : ℕ => ZMod (ℓ ^ n)) n).comp (compatSubring ℓ).subtype

omit [Fact ℓ.Prime] in
/-- The projection family `compatProj` is compatible with the tower's connecting maps
(`ZMod.castHom`), so `PadicInt.lift` applies to it. -/
theorem compatProj_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k₁))).comp (compatProj ℓ k₂) = compatProj ℓ k₁ := by
  ext x
  simpa only [RingHom.comp_apply, compatProj, Pi.evalRingHom_apply,
    RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype]
    using compat_of_adjacentCompat ℓ x.property k₁ k₂ hk

/-- The projection family is compatible with the tower's connecting maps, so `PadicInt.lift`
applies to it; this is the inverse of `padicIntEquivLimZMod`. -/
noncomputable def limZModToPadic : compatSubring ℓ →+* ℤ_[ℓ] :=
  PadicInt.lift (f := compatProj ℓ) (compatProj_compat ℓ)

/-- The forward map `ℤ_[ℓ] → lim ZMod (ℓ^n)`: `z ↦ (n ↦ toZModPow n z)`. -/
noncomputable def padicToLimZMod : ℤ_[ℓ] →+* compatSubring ℓ :=
  RingHom.codRestrict (Pi.ringHom (fun n : ℕ => PadicInt.toZModPow n)) (compatSubring ℓ)
    (fun z n => RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) n.le_succ) z)

omit [Fact ℓ.Prime] in
@[simp] theorem compatProj_apply (n : ℕ) (x : compatSubring ℓ) :
    compatProj ℓ n x = x.val n := rfl

@[simp] theorem padicToLimZMod_val (z : ℤ_[ℓ]) (n : ℕ) :
    (padicToLimZMod ℓ z).val n = PadicInt.toZModPow n z := rfl

/-- The defining property of the inverse: `toZModPow n (limZModToPadic ℓ x) = x.val n`. -/
@[simp] theorem toZModPow_limZModToPadic (n : ℕ) (x : compatSubring ℓ) :
    PadicInt.toZModPow n (limZModToPadic ℓ x) = x.val n := by
  simpa [limZModToPadic, compatProj]
    using RingHom.congr_fun (PadicInt.lift_spec (f := compatProj ℓ) (compatProj_compat ℓ) n) x

/-- **`ℤ_[ℓ] ≅ lim_n ZMod (ℓ^n)`.** The `ℓ`-adic integers are the projective limit of the
`ZMod` tower (Silverman III.7, p. 87).

The codomain `↥(compatSubring ℓ)` is the projective-limit subtype
`{ f : Π n, ZMod (ℓ^n) //`
`∀ n, ZMod.castHom (pow_dvd_pow ℓ n.le_succ) (ZMod (ℓ^n)) (f (n+1)) = f n }`. -/
noncomputable def padicIntEquivLimZMod : ℤ_[ℓ] ≃+* compatSubring ℓ :=
  RingEquiv.ofRingHom (padicToLimZMod ℓ) (limZModToPadic ℓ)
    (by ext x n; simp)
    (by ext z; exact PadicInt.ext_of_toZModPow.mp (fun n => by simp))

end HasseWeil.TateModule
