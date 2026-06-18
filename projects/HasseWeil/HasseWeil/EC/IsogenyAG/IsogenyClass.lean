/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG
import HasseWeil.EC.IsogenyAG.Dual

/-!
# The isogeny relation and isogeny classes (Silverman III.4, III.6.1)

Following Silverman III.4 (book p.66):

> Two elliptic curves `E₁` and `E₂` are *isogenous* if there is an isogeny from
> `E₁` to `E₂` with `φ(E₁) ≠ {O}`. We will see later (III.6.1) that this is an
> equivalence relation.

This file defines that relation, `IsIsogenous`, and establishes the parts of the
"equivalence relation" claim that are unconditional in the present development:

* **Reflexivity** (`IsIsogenous.refl`) — via the identity isogeny `EC.Isogeny.id`.
* **Transitivity** (`IsIsogenous.trans`) — via composition `EC.Isogeny.compose`.

Both are axiom-clean and immediate.

* **Symmetry** — the crux. It requires the **dual isogeny** `φ̂ : E₂ → E₁` of
  Silverman III.6.1, *as a morphism* (carrying a function-field pullback
  `φ̂* : K(E₁) → K(E₂)`). `HasseWeil/EC/IsogenyAG/Dual.lean` builds it —
  axiom-clean — from the per-isogeny witness package `Isogeny.HasDualWitness φ`
  (the range inclusion `Im(ν*) ⊆ Im(φ*)` + the basepoint condition), by
  factoring at the function-field level (`Curves.CurveMap.factorThrough`,
  Silverman III.4.11).

  **There is no unconditional universal witness** in the development: the former
  `EC.universal_dualGaloisData` route (`∀ φ, Nonempty (DualGaloisData φ)`) is
  **false** for purely inseparable `φ` — refuted at the `q`-power Frobenius in
  `EC/IsogenyAG/DualUniversal.lean` (B2, 2026-06-10) — and the true universal
  statement `∀ φ, Nonempty φ.HasDualWitness` (Silverman III.6.1 proper) is open
  in general, reduced over a perfect characteristic-`p` base to the separable
  side on Frobenius twists
  (`nonempty_hasDualWitness_of_twisted_separable_witnessesOf`,
  `EC/IsogenyAG/TwistedFactorization.lean`). Symmetry is therefore
  **witness-gated** here: `IsIsogenous.symm_of_witness` takes the per-pair
  witnesses, and the bundled `Equivalence`/`Setoid`/quotient take the named
  field-level hypothesis `UniversalDualWitness F`.

## Gating architecture (B2 rewiring, 2026-06-10)

Two honest packagings were considered for the downstream
`Equivalence`/`Setoid`/quotient:

1. **Hypothesis-gated** (implemented): thread `hw : UniversalDualWitness F`
   through `isIsogenous_equivalence`, `isIsogenousSetoid`, `IsogenyClass`. Cost:
   one extra argument per declaration; every consumer states exactly the open
   input it uses, and the statements specialise to the unconditional ones the
   moment the universal witness is proved.
2. **Sub-class restatement** (documented alternative): bundle the witness into
   the carrier (curves-with-witnessed-duals) and build an unconditional setoid
   there. Cost: a new carrier structure, transport of witnesses along
   composition/duals to keep the relation well-defined on the sub-class, and a
   second relation to compare with `IsIsogenous` — substantially heavier, with
   no consumer demanding it today.

## Discharged witness instances (the gate is non-vacuous)

`Nonempty φ.HasDualWitness` is a theorem for the project's concrete classes:
`[ℓ]` (`mulByIntSelfDualWitness`, `EC/IsogenyAG/MulByIntPullbackComp.lean`; over
`K̄` also `dualMulByInt` / `exists_dual_mulByInt`, `DualGaloisClosed.lean`), the
`q`-power Frobenius and its powers (`nonempty_hasDualWitness_frobenius`,
`FrobeniusDual.lean`; `frobeniusPowerMulByIntDualWitness`,
`DualReduction.lean`), the relative Frobenius / Verschiebung
(`hasDualWitnessRelativeFrobeniusOf`, `relativeVerschiebung*`,
`TwistedFactorization.lean`), `1 − π` over `K̄` (`exists_dual_oneSub`,
`oneSubCanonicalDual`, `WeilPairing/OneSubPullbackEvaluation.lean`), and the
general separable class over `K̄`
(`exists_dual_of_pullbackEvaluation_general`, `EC/KernelCountGeneral.lean`).

## The isogeny class (LMFDB)

LMFDB's *isogeny class* of an elliptic curve is the equivalence class of
`IsIsogenous`. The `Equivalence`/`Setoid` packaging is assembled here, gated on
`UniversalDualWitness F`:

* `isIsogenous_refl`, `isIsogenous_trans` — the unconditional half;
* `IsIsogenous.symm_of_witness` / `IsIsogenous.symm_of` — witness-gated symmetry;
* `isIsogenousSetoid` / `isIsogenous_equivalence` — the bundled equivalence
  relation (hence the isogeny-class quotient `IsogenyClass`), gated.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4 (definition of
  *isogenous*), III.6.1 (the dual isogeny, used for symmetry).
-/

open WeierstrassCurve

namespace HasseWeil.EC

variable {F : Type*} [Field F]

/-! ### The isogeny relation -/

/-- **Silverman III.4** (book p.66): two elliptic curves `W₁`, `W₂` over `F` are
*isogenous* if there is an isogeny from `W₁` to `W₂`.

We model "isogeny" by `EC.Isogeny`, whose underlying datum is a function-field
pullback `φ* : K(W₂) → K(W₁)`. Such a pullback is an `F`-algebra hom between
fields, hence injective, so every `EC.Isogeny` is automatically nonconstant —
exactly Silverman's side condition `φ(E₁) ≠ {O}`. Thus
`Nonempty (EC.Isogeny W₁ W₂)` is precisely the textbook relation. -/
def IsIsogenous (W₁ W₂ : Affine F) [W₁.IsElliptic] [W₂.IsElliptic] : Prop :=
  Nonempty (EC.Isogeny W₁ W₂)

/-- Unfolding: `IsIsogenous W₁ W₂` is the existence of an `EC.Isogeny W₁ W₂`. -/
theorem isIsogenous_iff {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] :
    IsIsogenous W₁ W₂ ↔ Nonempty (EC.Isogeny W₁ W₂) := Iff.rfl

/-- An explicit isogeny witnesses the isogeny relation. -/
theorem IsIsogenous.of_isogeny {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EC.Isogeny W₁ W₂) : IsIsogenous W₁ W₂ :=
  ⟨φ⟩

/-! ### Reflexivity (identity isogeny) -/

/-- **Reflexivity**: every elliptic curve is isogenous to itself, via the
identity isogeny `EC.Isogeny.id`. -/
theorem IsIsogenous.refl (W : Affine F) [W.IsElliptic] : IsIsogenous W W :=
  ⟨EC.Isogeny.id W⟩

/-- Reflexivity, named for the `Equivalence` packaging. -/
theorem isIsogenous_refl (W : Affine F) [W.IsElliptic] : IsIsogenous W W :=
  IsIsogenous.refl W

/-! ### Transitivity (composition of isogenies) -/

/-- **Transitivity**: isogenies compose. If `W₁` is isogenous to `W₂` and `W₂`
is isogenous to `W₃`, then `W₁` is isogenous to `W₃`, via `EC.Isogeny.compose`. -/
theorem IsIsogenous.trans {W₁ W₂ W₃ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    (h₁₂ : IsIsogenous W₁ W₂) (h₂₃ : IsIsogenous W₂ W₃) : IsIsogenous W₁ W₃ := by
  obtain ⟨φ⟩ := h₁₂
  obtain ⟨ψ⟩ := h₂₃
  exact ⟨ψ.compose φ⟩

/-- Transitivity, named for the `Equivalence` packaging. -/
theorem isIsogenous_trans {W₁ W₂ W₃ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    (h₁₂ : IsIsogenous W₁ W₂) (h₂₃ : IsIsogenous W₂ W₃) : IsIsogenous W₁ W₃ :=
  h₁₂.trans h₂₃

/-! ### Symmetry via the dual isogeny (Silverman III.6.1) — witness-gated

This is the crux of "isogenous is an equivalence relation". Silverman III.6.1
constructs, for a nonconstant isogeny `φ : E₁ → E₂` of degree `m`, the **dual
isogeny** `φ̂ : E₂ → E₁` with `φ̂ ∘ φ = [m]`. Being itself a nonconstant isogeny
in the reverse direction, `φ̂` immediately gives symmetry of `IsIsogenous`.

In the present formalisation the dual is built from the per-isogeny witness
package `Isogeny.HasDualWitness φ` (`Dual.lean`, axiom-clean), and **no
unconditional universal witness is available** (the former Galois-data route is
false — see the module docstring). Symmetry is therefore stated against the
witnesses; the named field-level gate is `UniversalDualWitness F`. -/

namespace IsogenyDual

variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The dual isogeny as a morphism, from a witness** (Silverman III.6.1,
existence half, witness-gated).

Given an `EC.Isogeny W₁ W₂` (a nonconstant isogeny `φ : E₁ → E₂`) together with
a dual witness — the range inclusion `Im(ν*) ⊆ Im(φ*)` for a nonconstant
endomorphism `ν` of `E₁` plus the basepoint condition, packaged as
`Isogeny.HasDualWitness φ` — there is an `EC.Isogeny W₂ W₁`. Thin wrapper over
the axiom-clean `EC.Isogeny.exists_dual_of_witness` (`Dual.lean`), which builds
`φ̂* := (φ*)⁻¹|_{range} ∘ ν*` by Silverman III.4.11 factoring.

The witness hypothesis is honest and per-isogeny: it is a theorem for the
project's discharged classes (see the module docstring's instance list), it
reduces over a perfect characteristic-`p` base to the separable side on
Frobenius twists (`nonempty_hasDualWitness_of_twisted_separable_witnessesOf`),
and it is *not* derivable from a universal Galois package
(`EC.not_universal_dualGaloisData`). -/
theorem exists_dual (φ : EC.Isogeny W₁ W₂) (w : Nonempty φ.HasDualWitness) :
    Nonempty (EC.Isogeny W₂ W₁) :=
  w.elim fun w' ↦ φ.exists_dual_of_witness w'

end IsogenyDual

/-- **The universal dual-witness hypothesis** over the field `F` (Silverman
III.6.1, hypothesis form): every isogeny between elliptic curves over `F`
carries a `HasDualWitness`.

This is the *true* universal statement of Silverman III.6.1 — the former
attempt to prove it via universal Galois data (`universal_dualGaloisData`) is
refuted in `EC/IsogenyAG/DualUniversal.lean`, since the Galois fixed-field
packaging is unsatisfiable for purely inseparable isogenies. It is carried as a
named hypothesis: discharged per concrete class (module docstring), and reduced
over a perfect characteristic-`p` base to the separable side on Frobenius
twists (`nonempty_hasDualWitness_of_twisted_separable_witnessesOf`,
`EC/IsogenyAG/TwistedFactorization.lean`). -/
def UniversalDualWitness (F : Type*) [Field F] : Prop :=
  ∀ ⦃W₁ W₂ : Affine F⦄ [W₁.IsElliptic] [W₂.IsElliptic] (φ : EC.Isogeny W₁ W₂),
    Nonempty φ.HasDualWitness

/-- **Symmetry from per-pair dual witnesses** (Silverman III.6.1): if `W₁` is
isogenous to `W₂` and every isogeny `W₁ → W₂` carries a dual witness, then `W₂`
is isogenous to `W₁`, by taking the dual of a witnessing isogeny. -/
theorem IsIsogenous.symm_of_witness {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
    (h : IsIsogenous W₁ W₂)
    (w : ∀ φ : EC.Isogeny W₁ W₂, Nonempty φ.HasDualWitness) : IsIsogenous W₂ W₁ := by
  obtain ⟨φ⟩ := h
  exact IsogenyDual.exists_dual φ (w φ)

/-- **Symmetry under the universal dual-witness hypothesis** (Silverman
III.6.1, gated form of the former `IsIsogenous.symm`). -/
theorem IsIsogenous.symm_of (hw : UniversalDualWitness F) {W₁ W₂ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : IsIsogenous W₁ W₂) : IsIsogenous W₂ W₁ :=
  h.symm_of_witness fun φ ↦ hw φ

/-- Symmetry, named for the `Equivalence` packaging (witness-gated). -/
theorem isIsogenous_symm_of (hw : UniversalDualWitness F) {W₁ W₂ : Affine F}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : IsIsogenous W₁ W₂) : IsIsogenous W₂ W₁ :=
  h.symm_of hw

/-! ### The isogeny class as an equivalence relation / setoid (witness-gated)

LMFDB's *isogeny class* is the equivalence class of `IsIsogenous`. To phrase
this as a mathlib `Equivalence`/`Setoid` we need a single carrier type, so we
bundle an elliptic curve together with its `IsElliptic` instance.

`IsIsogenous` lifts to this carrier; reflexivity and transitivity are
unconditional, and symmetry — hence the bundled `Equivalence`, the `Setoid`,
and the quotient — is gated on `UniversalDualWitness F` (the one honest open
input; see the module docstring for the gating-architecture discussion). -/

/-- An elliptic curve over `F`, bundled with its `IsElliptic` instance, as a
carrier for the isogeny-class equivalence relation. -/
structure EllipticCurveOver (F : Type*) [Field F] where
  /-- The underlying affine Weierstrass curve. -/
  toAffine : Affine F
  /-- The proof that it is an elliptic curve (smooth / non-singular). -/
  [isElliptic : toAffine.IsElliptic]

attribute [instance] EllipticCurveOver.isElliptic

/-- `IsIsogenous` lifted to the bundled carrier `EllipticCurveOver F`. This is
the relation whose equivalence classes are the LMFDB isogeny classes. -/
def IsogenousCurves (E₁ E₂ : EllipticCurveOver F) : Prop :=
  IsIsogenous E₁.toAffine E₂.toAffine

/-- **The isogeny relation is an equivalence relation, given universal dual
witnesses** (Silverman III.4 + III.6.1). Reflexivity and transitivity are
unconditional; symmetry is supplied by the witness-gated dual isogeny
(`IsIsogenous.symm_of`). -/
theorem isIsogenous_equivalence (hw : UniversalDualWitness F) :
    Equivalence (IsogenousCurves (F := F)) where
  refl E := IsIsogenous.refl E.toAffine
  symm h := IsIsogenous.symm_of hw h
  trans h₁₂ h₂₃ := IsIsogenous.trans h₁₂ h₂₃

/-- **The isogeny-class setoid**, given universal dual witnesses: the `Setoid`
on elliptic curves over `F` whose quotient is the set of LMFDB isogeny
classes. -/
def isIsogenousSetoid (hw : UniversalDualWitness F) : Setoid (EllipticCurveOver F) where
  r := IsogenousCurves
  iseqv := isIsogenous_equivalence hw

/-- The **isogeny class** quotient, given universal dual witnesses: elliptic
curves over `F` modulo the isogeny relation. The points of this quotient are
exactly LMFDB's isogeny classes. -/
abbrev IsogenyClass (F : Type*) [Field F] (hw : UniversalDualWitness F) : Type _ :=
  Quotient (isIsogenousSetoid hw)

end HasseWeil.EC
