/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.CharZeroDescent

/-!
# Splitting `μ_N` by a root of unity (route A, step 1)

The determinant model of the Weil pairing (`WeilPairing/CharZeroDescent.lean`) lands in the
*constant* scheme `(ℤ/N)_{S'}`, while the pairing must land in `μ_{N,S}`. Bridging the two
needs a chosen `N`-th root of unity on the cover: an `N`-th root `ζ ∈ Γ(S', ⊤)` gives the
splitting `k ↦ ζ^k`, `(ℤ/N)_{S'} ⟶ μ_{N,S'}`.

This is the step that makes route A honest. The determinant pairing alone is **not** enough
to produce a `μ_N`-valued pairing — one has to say *which* root of unity the value `1 ∈ ℤ/N`
maps to — and the choice is exactly what the cocycle condition later constrains: changing the
trivialisation by `g ∈ GL₂` multiplies the determinant by `det g`
(`detConstMor_gl2Both`), so the root has to change by `det g⁻¹` for the composite to be
independent of the choice.

`rootPower` is the individual power `ζ^k` as an `S'`-point of `μ_{N,S'}`; `rootSplitting`
assembles them over the constant scheme; `rootSplitting_π` records that it is a morphism over
`S'`, which the descent's `overBase` field consumes.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

variable {S' : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `k`-th power of a root of unity, as an `S'`-point of `μ_{N,S'}`. -/
noncomputable def rootPower (N : ℕ) [NeZero N]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (k : ZMod N) : S' ⟶ muN S' N :=
  ((muNPointsEquiv S' N (𝟙 S')).symm
    ⟨(ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val, by
      rw [← pow_mul, mul_comm, pow_mul, ζ.2, one_pow]⟩).1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Each power lies over the identity of `S'`. -/
theorem rootPower_π (N : ℕ) [NeZero N]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (k : ZMod N) :
    rootPower N ζ k ≫ muNπ S' N = 𝟙 S' :=
  ((muNPointsEquiv S' N (𝟙 S')).symm
    ⟨(ζ : Γ(S', (⊤ : S'.Opens))) ^ k.val, by
      rw [← pow_mul, mul_comm, pow_mul, ζ.2, one_pow]⟩).2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(route A, step 1)** The splitting of `μ_N` determined by a root of unity: the morphism
`(ℤ/N)_{S'} ⟶ μ_{N,S'}` sending the `k`-th copy of `S'` to `ζ^k`. -/
noncomputable def rootSplitting (N : ℕ) [NeZero N]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) :
    constScheme S' (ZMod N) ⟶ muN S' N :=
  Sigma.desc fun k => rootPower N ζ k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The `k`-th copy of `S'` maps to `ζ^k`. -/
@[simp] theorem rootSplitting_ι (N : ℕ) [NeZero N]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) (k : ZMod N) :
    Sigma.ι (fun _ : ZMod N => S') k ≫ rootSplitting N ζ = rootPower N ζ k := by
  simp only [rootSplitting, Sigma.ι_desc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(route A, step 1)** The splitting is a morphism over `S'` — the `overBase` input of the
Weil-pairing descent. -/
theorem rootSplitting_π (N : ℕ) [NeZero N]
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 }) :
    rootSplitting N ζ ≫ muNπ S' N = constSchemeπ S' (ZMod N) := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [← Category.assoc, rootSplitting_ι, rootPower_π]
  simp only [constSchemeπ, Sigma.ι_desc]

section LocalPairing

variable {S : Scheme.{u}} (E : EllipticCurve S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(route A, step 2)** The local Weil pairing on a trivialising cover: transport the
determinant model through a trivialisation of `E[N] ×_S E[N]`, split `ℤ/N` by the chosen
root of unity, and land in the fixed target `μ_{N,S}` via the base-change comparison. -/
noncomputable def localDetPairing (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N))) :
    pullback (E.torsionSqπ N) p ⟶ muN S N :=
  triv.hom ≫ detConstMor N ≫ rootSplitting N ζ ≫ muNMapAlong p N

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **(route A, step 2)** The local pairing is a morphism over `S`, provided the
trivialisation is one over `S'`. This is the `overBase` field of a
`WeilPairingLocalData`. -/
theorem localDetPairing_over (N : ℕ) [NeZero N] {S' : Scheme.{u}} (p : S' ⟶ S)
    (ζ : { a : Γ(S', (⊤ : S'.Opens)) // a ^ N = 1 })
    (triv : pullback (E.torsionSqπ N) p ≅
      constScheme S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)))
    (htriv : triv.hom ≫ constSchemeπ S' ((Fin 2 → ZMod N) × (Fin 2 → ZMod N)) =
      pullback.snd (E.torsionSqπ N) p) :
    localDetPairing E N p ζ triv ≫ muNπ S N =
      pullback.fst (E.torsionSqπ N) p ≫ E.torsionSqπ N := by
  rw [localDetPairing, Category.assoc, Category.assoc, Category.assoc,
    muNMapAlong_π, ← Category.assoc (rootSplitting N ζ), rootSplitting_π,
    ← Category.assoc (detConstMor N), detConstMor, constSchemeMap_π,
    ← Category.assoc, htriv]
  exact pullback.condition.symm

end LocalPairing

end ModularCurves
