/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.Dual
import HasseWeil.GapQfKernel

/-!
# The universal `DualGaloisData` statement is false (B2 refutation)

This file *refutes* the former universal-witness statement

> `universal_dualGaloisData : ∀ φ : Isogeny W₁ W₂, Nonempty (Isogeny.DualGaloisData φ)`

which used to close `HasseWeil/EC/IsogenyAG/Dual.lean` as a `sorry`.

## The counterexample: the `q`-power Frobenius

`DualGaloisData φ` (Silverman III.4.10c packaging) carries an automorphism family
`transAut` together with the **fixed-field equality**

`hfix : ∀ z, z ∈ Im(φ*) ↔ ∀ σ ∈ transAut, σ z = z`.

For the `q`-power Frobenius `π` over a finite field `K` (`q = #K = pⁿ`,
`p = char K`), `Im(π*) = K(E)^q` is a **proper, purely inseparable** subfield of
`K(E)` — and a purely inseparable proper extension is never the fixed-field of
*any* automorphism family:

* every `σ ∈ transAut` fixes every `q`-th power (the `←` consequence of `hfix`
  applied to `π* z = z^q`), and in characteristic `p` this already forces
  `σ = id`, since `(σ z)^q = σ (z^q) = z^q` and `w ↦ w^q = w^{pⁿ}` is injective
  (the iterated Frobenius ring hom of a field);
* hence the right-hand side of `hfix` is trivially true for *every* `z`, so
  `hfix` forces `π*` to be **surjective**;
* but `x = x_gen` is not even a `p`-th power in `K(E)`
  (`HasseWeil.x_gen_not_pth_power`: `D(w^p) = 0` in `Ω¹_{K(E)/K}` while
  `D x ≠ 0`), and a `q = pⁿ`-th power (`n ≥ 1`) is in particular a `p`-th
  power. Contradiction.

Note the failure is *sharper* than "the kernel-translation family does not
work": `π` is injective on points, so its kernel-translation family is trivial
and `Fix = K(E)` entire — but the structure quantifies `transAut`
existentially, so the refutation above rules out **every** candidate family.

`DualGaloisData` itself is the correct packaging for **separable** isogenies
(Silverman III.4.10c assumes separability), where it is realised unconditionally
for the discharged classes — see `dualGaloisData_mulByInt` / `dualMulByInt`
(`DualGaloisClosed.lean`), `dualGaloisData_of_class` (`WallCascade.lean`),
`dualGaloisData_of_pullbackEvaluation_general` (`KernelCountGeneral.lean`) and
`dualGaloisData_oneSub` (`WeilPairing/OneSubPullbackEvaluation.lean`). The
inseparable side realises `HasDualWitness` *directly*, with no Galois data
(Silverman III.6.1 Case 2): `hasDualWitness_frobenius` (`FrobeniusDual.lean`),
`frobeniusPowerMulByIntDualWitness` (`DualReduction.lean`), and the relative
Verschiebung route `hasDualWitnessRelativeFrobeniusOf` /
`nonempty_hasDualWitness_of_twisted_separable_witnessesOf`
(`TwistedFactorization.lean`).

## Main results

* `EC.isEmpty_dualGaloisData_frobenius` — `DualGaloisData (Isogeny.frobenius W)`
  is empty, for **every** elliptic curve over **every** finite field.
* `EC.not_universal_dualGaloisData` — the closed-form refutation of the
  universal statement, instantiated at `y² + y = x³` over `𝔽₂`.
* `EC.not_exists_dual_universal` — second B2 refutation: the legacy
  Basic-world `exists_dual` (`∃! β, IsDualOf E β α`, formerly the sole sorry
  of `DualIsogeny.lean`) is false; existence already fails at `α = [0]`.
* `EC.mulByInt_isDualOf_self` — the genuine scalar self-duality
  `IsDualOf [n] [n]` (`n ≠ 0`), replacing the deleted legacy cascade.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.10 (separability is
  required for the Galois fixed-field description), III.6.1 Case 2 (the
  inseparable side goes through Frobenius/Verschiebung instead).
-/

open WeierstrassCurve

namespace HasseWeil

namespace EC

open Curves

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

-- `[Fintype K]`/`[DecidableEq K]` are genuinely required: the statement is about
-- the `q`-power Frobenius (which only exists over a finite field with decidable
-- equality), but the linter only inspects the surface signature.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **`DualGaloisData` is empty for the `q`-power Frobenius** (B2 refutation core).
No automorphism family realises the `hfix` fixed-field equality
`Im(π*) = Fix(transAut)`: every member would fix all `q`-th powers, hence be the
identity (purely inseparable rigidity in characteristic `p`), forcing `π*` to be
surjective — contradicting `x_gen ∉ K(E)^p ⊇ K(E)^q`. -/
theorem isEmpty_dualGaloisData_frobenius (W : Affine K) [W.IsElliptic] :
    IsEmpty (Isogeny.DualGaloisData (Isogeny.frobenius W)) := by
  constructor
  intro d
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : CharP K p := hpK
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  haveI : CharP (⟨W⟩ : SmoothPlaneCurve K).FunctionField p :=
    charP_of_injective_algebraMap
      (algebraMap K (⟨W⟩ : SmoothPlaneCurve K).FunctionField).injective p
  haveI : ExpChar (⟨W⟩ : SmoothPlaneCurve K).FunctionField p := ExpChar.prime hp
  -- Purely inseparable rigidity: any `σ ∈ transAut` fixes all `q`-th powers
  -- (forward direction of `hfix` on `Im(π*)`), hence is the identity.
  have hid : ∀ σ ∈ d.transAut, ∀ z : (⟨W⟩ : SmoothPlaneCurve K).FunctionField, σ z = z := by
    intro σ hσ z
    have hfixed : σ (z ^ Fintype.card K) = z ^ Fintype.card K :=
      (d.hfix _).mp ⟨z, Isogeny.frobenius_pullback W z⟩ σ hσ
    rw [map_pow, hcard] at hfixed
    exact (iterateFrobenius (⟨W⟩ : SmoothPlaneCurve K).FunctionField p (n : ℕ)).injective hfixed
  -- So the right-hand side of `hfix` is trivially true and `π*` is surjective:
  -- in particular `x_gen` is a `q`-th power.
  obtain ⟨g, hg⟩ := (d.hfix (x_gen W)).mpr fun σ hσ => hid σ hσ (x_gen W)
  have hg' : g ^ p ^ (n : ℕ) = x_gen W := by
    rw [← hcard, ← Isogeny.frobenius_pullback W g]
    exact hg
  -- But a `q = pⁿ`-th power (`n ≥ 1`) is a `p`-th power, and `x_gen` is not one.
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
  rw [hm, pow_succ, pow_mul] at hg'
  exact x_gen_not_pth_power W p ⟨_, hg'⟩

/-! ### The closed counterexample instance

To refute the literal `∀`-statement we instantiate at a concrete elliptic curve
over a concrete finite field: `y² + y = x³` over `𝔽₂` (supersingular,
`Δ = -27 = 1`). Any curve over any finite field would do, by
`isEmpty_dualGaloisData_frobenius`. -/

/-- The elliptic curve `y² + y = x³` over `𝔽₂` (`a₁ = a₂ = a₄ = a₆ = 0`,
`a₃ = 1`), the concrete witness for `not_universal_dualGaloisData`. -/
def frobeniusCounterexampleCurve : Affine (ZMod 2) :=
  { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := 0, a₆ := 0 }

instance : frobeniusCounterexampleCurve.IsElliptic :=
  ⟨by rw [show frobeniusCounterexampleCurve.Δ = 1 by decide]; exact isUnit_one⟩

/-- **The former `universal_dualGaloisData` is false** (B2, 2026-06-10): it is
*not* the case that every isogeny carries a `DualGaloisData` — the `q`-power
Frobenius of `y² + y = x³` over `𝔽₂` is a counterexample
(`isEmpty_dualGaloisData_frobenius`). Stated at universe `0`, which the original
universe-polymorphic statement specialises to. -/
theorem not_universal_dualGaloisData :
    ¬ ∀ (F : Type) [Field F] (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic]
        (φ : Isogeny W₁ W₂), Nonempty (Isogeny.DualGaloisData φ) := fun h =>
  (h (ZMod 2) frobeniusCounterexampleCurve frobeniusCounterexampleCurve
    (Isogeny.frobenius frobeniusCounterexampleCurve)).elim
    (isEmpty_dualGaloisData_frobenius frobeniusCounterexampleCurve).false

/-! ### The legacy Basic-world `exists_dual` is false (second B2 refutation)

`HasseWeil/DualIsogeny.lean` formerly closed with the keystone sorry

> `exists_dual (α : Isogeny E E) : ∃! β : Isogeny E E, IsDualOf E β α`

for the *Basic-world* `HasseWeil.Isogeny` (pullback and point map carried as
**independent** structure fields). The statement is false. Existence fails at
`α := mulByInt E 0`: the documented junk pullback branch (`AlgHom.id`) gives
`α.degree = 1`, so the second `IsDualOf` conjunct contains the point-map
identity `(0 : ℤ) • β P = (1 : ℤ) • P`, i.e. `0 = P` — false on any curve
with a nonzero rational point, e.g. `P₀ = (0, 0)` on `y² + y = x³` over
`𝔽₂`. (Uniqueness *independently* fails for genuine `α` over
non-algebraically-closed fields: the dual equations cannot pin the
independent point-map field on a finite rational-point group; only the
pullback-level uniqueness `HasseWeil.IsDualOf.pullback_unique` survives.)

Ticket `DUAL-LEGACY-B2` in `.mathlib-quality/b2_log.jsonl`. The true
Silverman III.6.1 is the witness-gated `∃!` of
`EC/IsogenyAG/CanonicalDual.lean`.

The scalar self-duality that the legacy cascade's deleted
`isogDual_mulByInt_of_comp` was after is genuine and lives here
(`mulByInt_isDualOf_self`): its proof needs `mulByInt_comp_eq_mul`
(`EC/GenericPointZsmul.lean`), which is outside `DualIsogeny.lean`'s import
closure. -/

section LegacyExistsDual

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Scalar self-duality `IsDualOf [n] [n]`** (Silverman III.6.2(d)) for
`n ≠ 0`: both composition identities are `[n] ∘ [n] = [n²] = [deg [n]]`, from
`mulByInt_comp_eq_mul` (T-III-4-020b) and `mulByInt_degree`. The honest
replacement for the deleted `isogDual_mulByInt_of_comp` / `isogDual_mulByInt`
(which were downstream of the refuted `exists_dual`). -/
theorem mulByInt_isDualOf_self (W : WeierstrassCurve F) [W.toAffine.IsElliptic]
    (n : ℤ) (hn : n ≠ 0) :
    HasseWeil.IsDualOf W.toAffine (HasseWeil.mulByInt W.toAffine n)
      (HasseWeil.mulByInt W.toAffine n) := by
  have hcomp : (HasseWeil.mulByInt W.toAffine n).comp (HasseWeil.mulByInt W.toAffine n) =
      HasseWeil.mulByInt W.toAffine ((HasseWeil.mulByInt W.toAffine n).degree : ℤ) := by
    rw [HasseWeil.mulByInt_comp_eq_mul W n n hn hn (mul_ne_zero hn hn),
      HasseWeil.mulByInt_degree W.toAffine n hn]
    congr 1
    rw [show n * n = n ^ 2 from (sq n).symm]
    exact (Int.toNat_of_nonneg (sq_nonneg n)).symm
  exact ⟨hcomp, hcomp⟩

/-- **The former `HasseWeil.exists_dual` is false** (B2, `DUAL-LEGACY-B2`):
it is *not* the case that every Basic-world endomorphism has a unique
`IsDualOf` dual. Existence already fails at `α = [0]` (junk pullback branch
⟹ `deg = 1` ⟹ the dual equations force `0 = P₀` for the nonzero point
`P₀ = (0, 0)` of `y² + y = x³` over `𝔽₂`). Stated at universe `0`, which the
original universe-polymorphic statement specialises to. -/
theorem not_exists_dual_universal :
    ¬ ∀ (F : Type) [Field F] [DecidableEq F] (E : Affine F) [E.IsElliptic]
        (α : HasseWeil.Isogeny E E),
        ∃! β : HasseWeil.Isogeny E E, HasseWeil.IsDualOf E β α := by
  intro h
  obtain ⟨β, hβ, -⟩ := h (ZMod 2) frobeniusCounterexampleCurve
    (HasseWeil.mulByInt frobeniusCounterexampleCurve 0)
  -- The junk-branch pullback is `AlgHom.id`, so `[0].degree = 1` (the
  -- `id_degree` finrank computation, transported along the `dif_pos` branch).
  have hdeg : (HasseWeil.mulByInt frobeniusCounterexampleCurve 0).degree = 1 := by
    have hpb : (HasseWeil.mulByInt frobeniusCounterexampleCurve 0).pullback =
        AlgHom.id (ZMod 2) frobeniusCounterexampleCurve.FunctionField := by
      simp [HasseWeil.mulByInt]
    have key : (HasseWeil.mulByInt frobeniusCounterexampleCurve 0).degree =
        @Module.finrank frobeniusCounterexampleCurve.FunctionField
          frobeniusCounterexampleCurve.FunctionField _ _
          (RingHom.toAlgebra (AlgHom.id (ZMod 2)
            frobeniusCounterexampleCurve.FunctionField).toRingHom).toModule :=
      congrArg (fun a : frobeniusCounterexampleCurve.FunctionField →ₐ[ZMod 2]
            frobeniusCounterexampleCurve.FunctionField =>
          @Module.finrank frobeniusCounterexampleCurve.FunctionField
            frobeniusCounterexampleCurve.FunctionField _ _
            (RingHom.toAlgebra a.toRingHom).toModule) hpb
    rw [key]
    exact Module.finrank_self frobeniusCounterexampleCurve.FunctionField
  -- The nonzero rational point `(0, 0)`.
  have hP₀ : frobeniusCounterexampleCurve.Nonsingular 0 0 := by
    rw [Affine.nonsingular_zero]
    decide
  -- Rewrite the degree at the `IsDualOf` level, then evaluate the point-map
  -- component of the second conjunct at `P₀`.
  have h2 := hβ.2
  rw [hdeg, Nat.cast_one] at h2
  have hpt := DFunLike.congr_fun
    (congrArg HasseWeil.Isogeny.toAddMonoidHom h2)
    (Affine.Point.some 0 0 hP₀)
  simp only [HasseWeil.Isogeny.comp_toAddMonoidHom, AddMonoidHom.coe_comp,
    Function.comp_apply, HasseWeil.mulByInt_apply, zero_zsmul, one_zsmul] at hpt
  exact Affine.Point.some_ne_zero hP₀ hpt.symm

end LegacyExistsDual

end EC

end HasseWeil
