/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG
import HasseWeil.MulByIntPullback
import HasseWeil.EC.IsogenyAG.RamificationInfty

/-!
# The dual isogeny as a morphism (Silverman III.6.1)

This file constructs the **dual isogeny** `φ̂ : E₂ → E₁` of a nonconstant
isogeny `φ : E₁ → E₂` *as an `EC.Isogeny`* — i.e. carrying a function-field
pullback `φ̂* : K(E₁) → K(E₂)`, the deep step Silverman flags on book p.81 as
"by no means clear (that `κ⁻¹ ∘ φ* ∘ κ` is an isogeny, i.e. given by a rational
map)".

## Silverman's route (III.6.1 + III.4.11)

Silverman builds `φ̂` by **factoring `[m]` through `φ`** (`m = deg φ`):

* `φ̂ ∘ φ = [m]`, so at the level of function-field pullbacks (which compose
  contravariantly) `φ* ∘ φ̂* = [m]*`.
* Hence the image of `[m]*` is contained in the image of `φ*` inside `K(E₁)`,
  and **conversely** the factoring exists precisely when `Im([m]*) ⊆ Im(φ*)`.

The algebraic content of "factor through" (Silverman III.4.11) is therefore a
**pure field-theoretic fact**: if two `F`-algebra homs `ψ*, φ*` into a common
field `K(E₁)` satisfy `Im(ψ*) ⊆ Im(φ*)`, then since `φ*` is injective there is a
unique `χ*` with `ψ* = φ* ∘ χ*`, namely `χ* := (φ*)⁻¹|_{range} ∘ ψ*`. This is
`CurveMap.factorThrough`, shipped here axiom-clean.

The inclusion `Im([m]*) ⊆ Im(φ*)` itself is the genuinely deep input (Silverman
III.6.1 Case 1 = separable + III.4.10c + III.4.11; Case 2 = Frobenius via the
invariant differential). It is isolated as the predicate
`RangeIncl φ` and the existence statement reduces to it.

## Main results

* `Curves.CurveMap.factorThrough` — the algebraic factoring (axiom-clean).
* `Curves.CurveMap.factorThrough_comp` — `ψ = χ.comp φ` (axiom-clean).
* `EC.Isogeny.dualOfWitness` / `EC.Isogeny.dual` — the dual `EC.Isogeny`, modulo
  the range-inclusion witness and the basepoint witness (`HasDualWitness`).
* `EC.Isogeny.exists_dual_of_witness` — existence of the reverse isogeny from a
  `HasDualWitness` (axiom-clean).

There is **no** unconditional `∀ φ, Nonempty φ.HasDualWitness` here: the former
`universal_dualGaloisData` route to it is *false* for purely inseparable `φ`
(B2 verdict at the end of this file; formal refutation in
`EC/IsogenyAG/DualUniversal.lean`). The witness is produced per isogeny class —
see the final section's pointers.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.11 (factor through a
  separable isogeny), III.6.1 (the dual isogeny).
-/

open WeierstrassCurve

namespace HasseWeil

namespace Curves.CurveMap

variable {F : Type*} [Field F] {C₁ C₂ C₃ : Curves.SmoothPlaneCurve F}

/-! ### Algebraic factoring (Silverman III.4.11, field-theoretic core)

Given curve maps `φ : C₁ → C₂` and `ψ : C₁ → C₃` whose pullbacks land in a
common function field `K(C₁)`, and the range inclusion `Im(ψ*) ⊆ Im(φ*)`, we
produce a curve map `χ : C₂ → C₃` with `ψ* = φ* ∘ χ*`, i.e. `ψ = χ ∘ φ`.

This is the algebraic heart of "factor through": `φ*` is an injective `F`-algebra
hom between fields, hence an `AlgEquiv` onto its range; composing its inverse
with `ψ*` (codomain-restricted to that range) gives `χ*`. -/

/-- The pullback `χ* : K(C₃) → K(C₂)` factoring `ψ*` through `φ*`, given
`Im(ψ*) ⊆ Im(φ*)`. Constructed as `(φ*)⁻¹|_{range} ∘ (ψ* restricted to Im(φ*))`.
Mirrors `HasseWeil.verschiebungPullback_of_witness`. -/
noncomputable def factorThroughPullback (φ : CurveMap C₁ C₂) (ψ : CurveMap C₁ C₃)
    (h : ψ.pullback.range ≤ φ.pullback.range) :
    C₃.FunctionField →ₐ[F] C₂.FunctionField :=
  (AlgEquiv.ofInjective φ.pullback φ.pullback.toRingHom.injective).symm.toAlgHom.comp
    (ψ.pullback.codRestrict φ.pullback.range (fun z ↦ h ⟨z, rfl⟩))

/-- The factoring curve map `χ : C₂ → C₃`. -/
noncomputable def factorThrough (φ : CurveMap C₁ C₂) (ψ : CurveMap C₁ C₃)
    (h : ψ.pullback.range ≤ φ.pullback.range) : CurveMap C₂ C₃ where
  pullback := factorThroughPullback φ ψ h

@[simp] theorem factorThrough_pullback (φ : CurveMap C₁ C₂) (ψ : CurveMap C₁ C₃)
    (h : ψ.pullback.range ≤ φ.pullback.range) :
    (factorThrough φ ψ h).pullback = factorThroughPullback φ ψ h := rfl

/-- **Factoring identity** (Silverman III.4.11): `ψ* = φ* ∘ χ*` pointwise.
The defining property of `factorThroughPullback`. -/
theorem factorThroughPullback_spec (φ : CurveMap C₁ C₂) (ψ : CurveMap C₁ C₃)
    (h : ψ.pullback.range ≤ φ.pullback.range) (z : C₃.FunctionField) :
    φ.pullback (factorThroughPullback φ ψ h z) = ψ.pullback z := by
  change φ.pullback
      ((AlgEquiv.ofInjective φ.pullback φ.pullback.toRingHom.injective).symm
        (ψ.pullback.codRestrict φ.pullback.range (fun z ↦ h ⟨z, rfl⟩) z)) = _
  -- `φ.pullback` of `(ofInjective φ).symm x` is the coercion of `x` back to K(C₁),
  -- and the codomain-restriction's coercion is just `ψ.pullback z`.
  have key : ∀ x : φ.pullback.range,
      φ.pullback ((AlgEquiv.ofInjective φ.pullback φ.pullback.toRingHom.injective).symm x)
        = (x : C₁.FunctionField) := by
    intro x
    rw [← AlgEquiv.ofInjective_apply φ.pullback φ.pullback.toRingHom.injective
        ((AlgEquiv.ofInjective φ.pullback φ.pullback.toRingHom.injective).symm x),
      AlgEquiv.apply_symm_apply]
  rw [key]
  rfl

/-- **Factoring identity, curve-map form**: `ψ = χ.comp φ`. -/
theorem factorThrough_comp (φ : CurveMap C₁ C₂) (ψ : CurveMap C₁ C₃)
    (h : ψ.pullback.range ≤ φ.pullback.range) :
    ψ = (factorThrough φ ψ h).comp φ := by
  apply CurveMap.ext
  apply AlgHom.ext
  intro z
  change ψ.pullback z = φ.pullback ((factorThrough φ ψ h).pullback z)
  rw [factorThrough_pullback, factorThroughPullback_spec]

end Curves.CurveMap

/-! ### The dual isogeny as an `EC.Isogeny` (Silverman III.6.1)

We now lift the algebraic factoring to the `EC.Isogeny` level. Given a
nonconstant isogeny `φ : E₁ → E₂` and a **nonconstant endomorphism `ν` of `E₁`**
(morally `[m]`, `m = deg φ`) whose pullback factors through `φ*`
(`Im(ν*) ⊆ Im(φ*)`), the factored map `χ* := (φ*)⁻¹|_{range} ∘ ν*` is the
pullback of a curve map `E₂ → E₁`. Endowed with a basepoint witness it becomes
an `EC.Isogeny W₂ W₁` with `χ ∘ φ = ν`. -/

namespace EC

open Curves

variable {F : Type*} [Field F]

namespace Isogeny

variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The pullback `K(W₁) →ₐ[F] K(W₂)` of the dual, factoring a nonconstant
endomorphism `ν` of `E₁` through `φ`. Here `ν` is presented just by its
function-field pullback `νPb : K(W₁) →ₐ[F] K(W₁)` (e.g. `[m]*`), with the deep
range-inclusion witness `hincl`. -/
noncomputable def dualPullback (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range) :
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField :=
  CurveMap.factorThroughPullback φ.toCurveMap ⟨νPb⟩ hincl

/-- The dual isogeny `φ̂ : E₂ → E₁` as an `EC.Isogeny`, given:
* `νPb` — the pullback of a nonconstant endomorphism `ν` of `E₁` (e.g. `[m]*`),
* `hincl` — the range inclusion `Im(ν*) ⊆ Im(φ*)` (Silverman III.6.1's deep input),
* `hbase` — the basepoint condition on the resulting factored pullback. -/
noncomputable def dualOfWitness (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range)
    (hbase :
      ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
        0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty (dualPullback φ νPb hincl f)) :
    Isogeny W₂ W₁ where
  toCurveMap := ⟨dualPullback φ νPb hincl⟩
  pullback_ordAtInfty_nonneg := hbase

@[simp] theorem dualOfWitness_pullback (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range)
    (hbase :
      ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
        0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty (dualPullback φ νPb hincl f)) :
    (dualOfWitness φ νPb hincl hbase).toCurveMap.pullback =
      dualPullback φ νPb hincl := rfl

/-- **Reduction of the basepoint condition.** The dual's basepoint witness
`hbase` follows from:
* `hν` — the basepoint condition of `ν` (`0 ≤ ord_∞ f ⟹ 0 ≤ ord_∞ (ν* f)`), and
* `hrefl` — `φ` **reflects regularity at infinity**:
  `0 ≤ ord_∞ (φ* g) ⟹ 0 ≤ ord_∞ g`.

The latter is the sign-of-ramification fact: `ord_∞ (φ* g) = e_φ(O) · ord_∞ g`
with `e_φ(O) > 0` (and `φ(O) = O`), so a regular pullback forces a regular
function. With these two, since `φ* (φ̂* f) = ν* f`, regularity of `f` gives
regularity of `ν* f = φ* (φ̂* f)`, hence regularity of `φ̂* f`. -/
theorem hbase_of_reflects (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range)
    (hν : ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (νPb f))
    (hrefl : ∀ g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) →
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g) :
    ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty (dualPullback φ νPb hincl f) := by
  intro f hf
  apply hrefl
  rw [show φ.toCurveMap.pullback (dualPullback φ νPb hincl f) = νPb f from
    CurveMap.factorThroughPullback_spec φ.toCurveMap ⟨νPb⟩ hincl f]
  exact hν f hf

/-- **Factoring identity** at the `EC.Isogeny` level: `φ* ∘ φ̂* = ν*`, i.e.
`(φ̂ ∘ φ)* = ν*`. This is the function-field shadow of `φ̂ ∘ φ = ν`. -/
theorem dualOfWitness_comp_pullback (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range)
    (hbase :
      ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
        0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
        0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty (dualPullback φ νPb hincl f))
    (z : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) :
    φ.toCurveMap.pullback ((dualOfWitness φ νPb hincl hbase).toCurveMap.pullback z) =
      νPb z :=
  CurveMap.factorThroughPullback_spec φ.toCurveMap ⟨νPb⟩ hincl z

/-! ### `exists_dual` reduced to a single witness (Silverman III.6.1)

The data needed to produce a reverse isogeny `E₂ → E₁` is packaged as
`HasDualWitness φ`: a function-field pullback `νPb` of a nonconstant
endomorphism `ν` of `E₁` whose image lies inside `Im(φ*)`, together with a
basepoint witness for the resulting factored map. The mathematically intended
`ν` is `[m]` with `m = deg φ` (then `φ̂ ∘ φ = [m]`), but for the mere existence
of a reverse isogeny any nonconstant `ν` factoring through `φ` suffices. -/

/-- **The dual-isogeny witness** (Silverman III.6.1, packaged). Bundles the two
inputs needed to build a reverse isogeny `E₂ → E₁` from `φ : E₁ → E₂`:

* `νPb` — the function-field pullback of a nonconstant endomorphism `ν` of `E₁`
  (Silverman takes `ν = [m]`, `m = deg φ`);
* `hincl` — the range inclusion `Im(ν*) ⊆ Im(φ*)` inside `K(E₁)`. This is the
  deep step of Silverman III.6.1 (Case 1 = separable via `#ker φ = m` +
  III.4.11; Case 2 = Frobenius via the invariant differential);
* `hbase` — the basepoint condition `0 ≤ ord_∞ f ⟹ 0 ≤ ord_∞ (φ̂* f)` on the
  factored pullback (the morphism is defined at `O₂`). -/
structure HasDualWitness (φ : Isogeny W₁ W₂) where
  /-- The pullback `ν* : K(E₁) → K(E₁)` of a nonconstant endomorphism of `E₁`. -/
  νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField
  /-- The range inclusion `Im(ν*) ⊆ Im(φ*)` (the deep III.6.1 content). -/
  hincl : νPb.range ≤ φ.toCurveMap.pullback.range
  /-- The basepoint condition on the factored dual pullback. -/
  hbase : ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
    0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty (dualPullback φ νPb hincl f)

/-- **Assemble a dual witness** from the genuinely-irreducible pieces (the
honest decomposition of Silverman III.6.1):
* `hincl` — `Im(ν*) ⊆ Im(φ*)` (the range inclusion, III.6.1 core);
* `hν` — `ν`'s basepoint condition;
* `hrefl` — `φ` reflects regularity at infinity.

The basepoint field is discharged by `hbase_of_reflects`. -/
noncomputable def hasDualWitness_of_reflects (φ : Isogeny W₁ W₂)
    (νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
      (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
    (hincl : νPb.range ≤ φ.toCurveMap.pullback.range)
    (hν : ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (νPb f))
    (hrefl : ∀ g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
      0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) →
      0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g) :
    HasDualWitness φ where
  νPb := νPb
  hincl := hincl
  hbase := hbase_of_reflects φ νPb hincl hν hrefl

/-- **The dual isogeny from a witness**: a `HasDualWitness φ` produces the dual
`φ̂ : E₂ → E₁` as an `EC.Isogeny`. -/
noncomputable def dual (φ : Isogeny W₁ W₂) (w : HasDualWitness φ) : Isogeny W₂ W₁ :=
  dualOfWitness φ w.νPb w.hincl w.hbase

/-- **`exists_dual` from a witness** (Silverman III.6.1): if `φ` admits a dual
witness, there is a reverse isogeny `E₂ → E₁`. -/
theorem exists_dual_of_witness (φ : Isogeny W₁ W₂) (w : HasDualWitness φ) :
    Nonempty (Isogeny W₂ W₁) :=
  ⟨φ.dual w⟩

/-! #### The dual witness via the Galois fixed field (Silverman III.4.11)

The range inclusion `Im(ν*) ⊆ Im(φ*)` — the deep input of `HasDualWitness` — is
proved by Silverman III.4.11 from the **Galois correspondence**: `Im(φ*)` is the
fixed field of the `ker φ` translation-action, and `Im(ν*)` is fixed by those
translations (for `ν = [m]`, because `[m]·k = 0` for `k ∈ ker φ`, by Lagrange
`#ker φ = m`). We package the per-`φ` Galois inputs as `DualGaloisData φ` and
consume them axiom-clean.

The fixed-field equality `hfix` is precisely the output of the project's own
`HasseWeil.pullback_fieldRange_eq_fixedField_of_card_match_intrinsic`
(`Hasse/PointFix.lean`); the bridge `HasseWeil.fixedField_hfix_of_xy_family_of_card`
(`HasseWeil/EC/IsogenyAG/DualGalois.lean`) discharges it — axiom-clean — from the
per-`φ` translation covariance and the cardinality match `#ker φ = deg φ`, so the
reduction below is genuinely non-vacuous. -/

/-- **Silverman III.4.11, function-field core** (range inclusion via fixed field).
Let `φPb, νPb : L →ₐ[F] L` and let `G` be a set of `F`-algebra automorphisms of
`L`. If `Im(φPb)` is *exactly* the `G`-fixed subset of `L` (`hfix`, the Galois
fixed-field equality) and every `νPb`-value is `G`-fixed (`hnu`, the
`[m] ∘ τ_k = [m]` covariance), then `Im(νPb) ≤ Im(φPb)`. Axiom-clean. -/
theorem rangeIncl_of_fixedField {L : Type*} [Field L] [Algebra F L]
    (φPb νPb : L →ₐ[F] L) (G : Set (L ≃ₐ[F] L))
    (hfix : ∀ z : L, z ∈ φPb.range ↔ ∀ σ ∈ G, σ z = z)
    (hnu : ∀ σ ∈ G, ∀ w : L, σ (νPb w) = νPb w) :
    νPb.range ≤ φPb.range := by
  rintro z ⟨w, rfl⟩
  change νPb w ∈ φPb.range
  rw [hfix (νPb w)]
  exact fun σ hσ ↦ hnu σ hσ w

/-- **Silverman III.6.1 Galois data** for an isogeny `φ : E₁ → E₂`. Bundles the
per-`φ` inputs of the III.4.11 fixed-field argument for the range inclusion
`Im(ν*) ⊆ Im(φ*)`, plus the `∞`-regularity data for the basepoint:

* `νPb` — the pullback of a nonconstant endomorphism `ν` of `E₁` (Silverman
  takes `ν = [m]`, `m = deg φ`);
* `transAut` — the family `G` of `F`-algebra automorphisms of `K(E₁)` acting as
  the translations by `ker φ` (Silverman III.4.10c: these are
  `Gal(K(E₁)/φ*K(E₂))`);
* `hfix` — the **Galois fixed-field equality** `Im(φ*) = Fix(G)` (the deep
  III.4.10c content; discharged by `fixedField_hfix_of_xy_family_of_card`);
* `hnu` — `ν*`'s image is `G`-fixed (`τ_k* ∘ ν* = ν*`; shadow of `[m] ∘ τ_k = [m]`);
* `hν` — `ν`'s basepoint condition;
* `hrefl` — `φ` reflects `∞`-regularity. -/
structure DualGaloisData (φ : Isogeny W₁ W₂) where
  /-- The pullback `ν* : K(E₁) → K(E₁)` of a nonconstant endomorphism of `E₁`. -/
  νPb : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField →ₐ[F]
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField
  /-- The translation automorphism family `G ≅ ker φ` of `K(E₁)`. -/
  transAut : Set ((⟨W₁⟩ : SmoothPlaneCurve F).FunctionField ≃ₐ[F]
    (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField)
  /-- The Galois fixed-field equality `Im(φ*) = Fix(G)` (Silverman III.4.10c). -/
  hfix : ∀ z : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
    z ∈ φ.toCurveMap.pullback.range ↔ ∀ σ ∈ transAut, σ z = z
  /-- `ν*`'s image is `G`-fixed (the `[m] ∘ τ_k = [m]` covariance). -/
  hnu : ∀ σ ∈ transAut,
    ∀ w : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField, σ (νPb w) = νPb w
  /-- `ν`'s basepoint condition. -/
  hν : ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (νPb f)
  /-- `φ` reflects `∞`-regularity. -/
  hrefl : ∀ g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) →
    0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g

/-- **The range inclusion from the Galois data** (Silverman III.4.11), inlined
from `rangeIncl_of_fixedField` to avoid the `whnf` blowup that unifying the core's
abstract `L` against the curve-indexed function field would trigger. Axiom-clean. -/
theorem DualGaloisData.hincl {φ : Isogeny W₁ W₂} (d : DualGaloisData φ) :
    d.νPb.range ≤ φ.toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  change d.νPb w ∈ φ.toCurveMap.pullback.range
  rw [d.hfix (d.νPb w)]
  exact fun σ hσ ↦ d.hnu σ hσ w

/-- **The dual witness from the Galois data** (Silverman III.6.1). Assembles the
range inclusion (`DualGaloisData.hincl`, via the III.4.11 fixed-field core) with
the basepoint reduction (`hbase_of_reflects`). Axiom-clean. -/
noncomputable def hasDualWitness_of_galoisData {φ : Isogeny W₁ W₂}
    (d : DualGaloisData φ) : HasDualWitness φ :=
  hasDualWitness_of_reflects φ d.νPb d.hincl d.hν d.hrefl

/-! #### The faithful `[m]`-based dual (Silverman III.6.1 with `φ̂ ∘ φ = [m]`)

Silverman's actual statement takes `ν = [m]` (`m = deg φ`), so that the dual
satisfies the *defining* identity `φ̂ ∘ φ = [m]`. We package this faithful form:
the witness uses `ν* = [n]*` (`mulByInt_pullbackAlgHom`), and the factoring
identity `dualOfWitness_comp_pullback` then reads `(φ̂ ∘ φ)* = [n]*`, i.e. the
function-field shadow of `φ̂ ∘ φ = [n]`. This requires `[DecidableEq F]` (for the
division-polynomial pullback) and a nonzero `n` (Silverman's `m ≥ 1`). -/

variable [DecidableEq F]

/-- **The faithful dual witness** using `ν = [n]`. Bundles the `[n]`-based
range inclusion and basepoint witness; the resulting dual satisfies
`(φ̂ ∘ φ)* = [n]*`. Silverman takes `n = deg φ`. -/
structure HasMulByIntDualWitness (φ : Isogeny W₁ W₂) (n : ℤ) (hn : n ≠ 0) where
  /-- `Im([n]*) ⊆ Im(φ*)` — the deep III.6.1 range inclusion. -/
  hincl : (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn).range ≤
    φ.toCurveMap.pullback.range
  /-- The basepoint condition on the factored dual pullback. -/
  hbase : ∀ f : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField,
    0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty f →
    0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty
      (dualPullback φ (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn) hincl f)

/-- A faithful `[n]`-witness yields a generic `HasDualWitness`. -/
noncomputable def HasMulByIntDualWitness.toHasDualWitness {φ : Isogeny W₁ W₂}
    {n : ℤ} {hn : n ≠ 0} (w : HasMulByIntDualWitness φ n hn) :
    HasDualWitness φ where
  νPb := HasseWeil.mulByInt_pullbackAlgHom W₁ n hn
  hincl := w.hincl
  hbase := w.hbase

/-- **The faithful dual** `φ̂ : E₂ → E₁` (Silverman III.6.1), built from an
`[n]`-witness, satisfying `(φ̂ ∘ φ)* = [n]*`. -/
noncomputable def mulByIntDual {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : HasMulByIntDualWitness φ n hn) : Isogeny W₂ W₁ :=
  φ.dual w.toHasDualWitness

-- `[DecidableEq F]` is genuinely required (it builds `mulByInt_pullbackAlgHom` and
-- `HasMulByIntDualWitness`), but the linter only inspects the type signature.
set_option linter.unusedSectionVars false in
set_option linter.unusedDecidableInType false in
/-- **Silverman III.6.1 defining identity (function-field form)**:
`(φ̂ ∘ φ)* = [n]*`. Equivalently `φ* ∘ φ̂* = [n]*`, the pullback shadow of
`φ̂ ∘ φ = [n]`. With `n = deg φ` this is `φ̂ ∘ φ = [deg φ]`. -/
theorem mulByIntDual_comp_pullback {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : HasMulByIntDualWitness φ n hn)
    (z : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) :
    φ.toCurveMap.pullback ((mulByIntDual w).toCurveMap.pullback z) =
      HasseWeil.mulByInt_pullbackAlgHom W₁ n hn z :=
  dualOfWitness_comp_pullback φ (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn)
    w.hincl w.hbase z

end Isogeny

/-! ### The universal Galois data is FALSE — B2 verdict (2026-06-10)

Everything above is axiom-clean. Earlier revisions closed this file with

`theorem universal_dualGaloisData : ∀ φ, Nonempty (Isogeny.DualGaloisData φ) := sorry`

and derived from it `universal_dual_witness : ∀ φ, Nonempty φ.HasDualWitness` and
`exists_dual : ∀ φ : Isogeny W₁ W₂, Nonempty (Isogeny W₂ W₁)`. That universal
Galois statement is **refutable**, so all three have been removed (B2,
`.mathlib-quality/b2_log.jsonl`, ticket `ISO-DUAL/universal`):

for the `q`-power Frobenius `π` (every elliptic curve over every finite field,
`q = #K = pⁿ > 1`), `Im(π*) = K(E)^q` is a *proper purely inseparable* subfield
of `K(E)`, and in characteristic `p` any field automorphism fixing every `q`-th
power is the identity (`(σ z)^q = σ(z^q) = z^q` and `w ↦ w^q` is injective).
Hence **no** automorphism family `G` realises the `hfix` equality
`Im(π*) = Fix(G)`: each `σ ∈ G` would fix `K(E)^q` pointwise, forcing `σ = id`,
whence `Fix(G) = K(E) ⊋ Im(π*)`. Note `transAut` is existentially quantified in
`DualGaloisData`, so this rules out every candidate family — not merely the
(trivial, since `π` is injective on points) kernel-translation family. The
formal refutation — `EC.isEmpty_dualGaloisData_frobenius` and the closed
counterexample `EC.not_universal_dualGaloisData` (`y² + y = x³` over `𝔽₂`) — is
in `HasseWeil/EC/IsogenyAG/DualUniversal.lean`.

`DualGaloisData` itself is *correct and realised* for **separable** isogenies —
the fixed-field route is Silverman III.4.10c, which assumes separability — e.g.
`dualGaloisData_mulByInt` / `dualMulByInt` (`DualGaloisClosed.lean`),
`dualGaloisData_of_class` (`WallCascade.lean`),
`dualGaloisData_of_pullbackEvaluation_general` (`KernelCountGeneral.lean`), and
`dualGaloisData_oneSub` (`WeilPairing/OneSubPullbackEvaluation.lean`). The
inseparable side realises `HasDualWitness` **directly** (Silverman III.6.1
Case 2, no Galois data): `hasDualWitness_frobenius` /
`nonempty_hasDualWitness_frobenius` (`FrobeniusDual.lean`),
`frobeniusPowerMulByIntDualWitness` (`DualReduction.lean`), and the relative
Verschiebung `hasDualWitnessRelativeFrobeniusOf` (`TwistedFactorization.lean`).

The honest universal statement is therefore **witness-gated**: every isogeny
admits a reverse isogeny *given* a `HasDualWitness`
(`Isogeny.exists_dual_of_witness` above — the axiom-clean Silverman III.4.11
factoring); producing the witness for arbitrary `φ` over a perfect
characteristic-`p` base reduces — axiom-clean — to the separable side on the
Frobenius twists (`nonempty_hasDualWitness_of_twisted_separable_witnessesOf`,
`TwistedFactorization.lean`). The isogeny-class consequences
(`IsIsogenous.symm` et al.) are gated on the named hypothesis
`EC.UniversalDualWitness` in `EC/IsogenyAG/IsogenyClass.lean`. -/

/-! ### Concrete demonstration: the Frobenius isogeny reflects ∞-regularity

To show the `hrefl` ("reflects regularity at infinity") leaf of the dual witness
is genuinely dischargeable for real isogenies — not vacuous — we discharge it
*axiom-clean* for the `q`-power Frobenius `π`. Its pullback is `g ↦ g^q`
(`Isogeny.frobenius_pullback`), so `ord_∞ (π* g) = q · ord_∞ g`
(`ordAtInfty_pow`), and since `q ≥ 1` a nonnegative `ord_∞ (π* g)` forces a
nonnegative `ord_∞ g`. This is the `φ̂* = V*` Verschiebung side of Silverman
III.6.1 Case 2. -/

/-- The coercion `ℤ → WithTop ℤ` commutes with `nsmul`. -/
theorem withTop_coe_nsmul (q : ℕ) (k : ℤ) :
    (q • (k : WithTop ℤ)) = (((q • k : ℤ)) : WithTop ℤ) := by
  induction q with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, ih, ← WithTop.coe_add]

/-- `0 ≤ q • x → 0 ≤ x` in `WithTop ℤ` for `q ≥ 1`. (Order-reflection of `nsmul`.) -/
theorem nonneg_of_nsmul_nonneg {q : ℕ} (hq : 1 ≤ q) {x : WithTop ℤ}
    (h : 0 ≤ q • x) : 0 ≤ x := by
  induction x with
  | top => exact le_top
  | coe k =>
    rw [withTop_coe_nsmul, ← WithTop.coe_zero, WithTop.coe_le_coe, nsmul_eq_mul] at h
    rw [← WithTop.coe_zero, WithTop.coe_le_coe]
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    exact (mul_nonneg_iff_of_pos_left hqz).mp h

/-! ### RAMI-1 — `∞`-regularity reflection from the ramification index at `O`

The `hrefl` field of the dual witness — `0 ≤ ord_∞ (φ* g) ⟹ 0 ≤ ord_∞ g` — is the
sign-of-ramification fact at the basepoint `O` (Silverman III.4.10a): under the
local model, `ord_∞ (φ* g) = e_φ(O) · ord_∞ g` with `e_φ(O) = deg_i φ ≥ 1` (the
ramification index at `O`), so a regular pullback forces a regular function.

We package the reduction: given the ramification identity `ord_∞ (φ* g) =
e • ord_∞ g` (`e ≥ 1`) at `O`, `hrefl` follows by order-reflection of `nsmul`
(`nonneg_of_nsmul_nonneg`, the same mechanism as the Frobenius case below). For a
**separable** isogeny, `e_φ(O) = deg_i φ = 1` (Silverman III.4.10a), so the
identity is `ord_∞ (φ* g) = ord_∞ g` and `hrefl` is immediate.

The ramification identity `ord_∞ (φ* g) = e_φ(O) · ord_∞ g` itself — the local
ramification index of `φ` **at the point at infinity** in the codomain — is the
genuine geometric content (the project has no general `ord_∞ ∘ φ*` formula; only
base-change `e = 1` (`ordAtInfty_functionFieldMap`) and the explicit `g ↦ g^q`
Frobenius case (`ordAtInfty_pow`)). It is carried per isogeny as `hramO`. -/

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **`∞`-regularity reflection from the ramification index at `O`** (Silverman
III.4.10a, RAMI-1). Given the local ramification identity at the basepoint
`ord_∞ (φ* g) = e • ord_∞ g` with `e ≥ 1` (`hramO`), the isogeny `φ` reflects
regularity at infinity: `0 ≤ ord_∞ (φ* g) ⟹ 0 ≤ ord_∞ g`.

Pure order-reflection of `nsmul` in `WithTop ℤ` (`nonneg_of_nsmul_nonneg`); the
`g = 0` case is trivial. This is the `hrefl` field of `DualGaloisData` /
`HasDualWitness`, reduced to the single ramification-at-`O` identity `hramO`. For
separable `φ`, `e = deg_i φ = 1` (the identity is exact). -/
theorem reflects_ordAtInfty_of_ramificationIdx
    (φ : Isogeny W₁ W₂) {e : ℕ} (he : 1 ≤ e)
    (hramO : ∀ g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField, g ≠ 0 →
      (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g) =
        e • (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g)
    (g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField)
    (h : 0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g)) :
    0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · apply nonneg_of_nsmul_nonneg he
    rwa [← hramO g hg]

/-- **`∞`-regularity reflection with `hramO` and `hnt` internalised** (Silverman
II.2.6 + III.4.10a) — *unconditional*.  This strengthens
`reflects_ordAtInfty_of_ramificationIdx` by *deriving* the ramification identity
`hramO`, the index `e_φ(O)`, **and** its positivity `e_φ(O) ≥ 1` from the
isogeny itself, via `Isogeny.exists_pos_ramificationIdx_at_infinity`
(`EC/IsogenyAG/RamificationInfty.lean`).  The former non-triviality hypothesis
`hnt` (that `φ*` carries the `∞`-uniformizer `x/y` to a function vanishing at
`O₁`) is now a theorem (`Isogeny.pos_ordAtInfty_pullback_uniformizer`): `F(E₁)`
is algebraic over `φ* F(E₂)` CoordHom-free (transcendence-degree argument,
`CurveMap.isAlgebraic_toAlgebra`), and `ord_∞ ∘ φ*` cannot vanish identically on
`F(E₂)×` when `F(E₁)` is algebraic over the image, since `ord_∞ x₁ = -2 ≠ 0`
(`ordAtInfty_eq_zero_of_isAlgebraic`).

Thus the `hrefl` field of `DualGaloisData` / `HasDualWitness` needs neither the
separately-carried ramification formula `hramO` nor `hnt`: both are theorems.
See `Isogeny.reflects_ordAtInfty` for the underlying result. -/
theorem reflects_ordAtInfty_of_nontrivial (φ : Isogeny W₁ W₂)
    (g : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField)
    (h : 0 ≤ (⟨W₁⟩ : SmoothPlaneCurve F).ordAtInfty (φ.toCurveMap.pullback g)) :
    0 ≤ (⟨W₂⟩ : SmoothPlaneCurve F).ordAtInfty g :=
  Isogeny.reflects_ordAtInfty φ g h

-- `[DecidableEq K]` is genuinely required by `Isogeny.frobenius`, but the linter
-- only inspects the type signature (where it is resolved through that term).
set_option linter.unusedDecidableInType false in
/-- **The `q`-power Frobenius reflects regularity at infinity** (axiom-clean):
`0 ≤ ord_∞ (π* g) ⟹ 0 ≤ ord_∞ g`. This discharges the `hrefl` leaf of the dual
witness for `φ = π`, the Verschiebung side of Silverman III.6.1 Case 2. -/
theorem frobenius_reflects_ordAtInfty {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (W : Affine K) [W.IsElliptic]
    (g : (⟨W⟩ : SmoothPlaneCurve K).FunctionField)
    (h : 0 ≤ (⟨W⟩ : SmoothPlaneCurve K).ordAtInfty
      ((Isogeny.frobenius W).toCurveMap.pullback g)) :
    0 ≤ (⟨W⟩ : SmoothPlaneCurve K).ordAtInfty g := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · have hq : 1 ≤ Fintype.card K := Fintype.card_pos
    apply nonneg_of_nsmul_nonneg hq
    rw [← (⟨W⟩ : SmoothPlaneCurve K).ordAtInfty_pow hg]
    rwa [Isogeny.frobenius_pullback] at h

end EC

end HasseWeil
