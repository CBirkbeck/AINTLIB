/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslationOrd

/-!
# `Affine.Point.map` is a group homomorphism (named API + specialisations)

Mathlib's `WeierstrassCurve.Affine.Point.map`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`) — the version induced by an
**algebra homomorphism** `f : F →ₐ[S] K` between two field extensions of `S` — is *already*
bundled as an `AddMonoidHom`

```
WeierstrassCurve.Affine.Point.map f : W'⟮F⟯ →+ W'⟮K⟯
```

so `map_add`, `map_zero`, `map_neg`, `map_sub` and `map_zsmul` hold for it for free via the generic
`AddMonoidHom` / `map_*` API. This file does **not** reprove that fact (there is nothing to prove);
instead it records the group-hom equations under short, directly-rewritable names in the
`WeierstrassCurve.Affine.Point` namespace, and then supplies the two specialisations this project
actually consumes:

* `liftPointToKE W = Affine.Point.map (Algebra.ofId F KE)` — the lift `E(F) → E(K(E))` used by
  `HasseWeil.liftPointToKE` (`HasseWeil/EC/TranslationOrd.lean`);
* the action of an `F`-algebra map `K(E) → K(E)` on `(W_KE).Point` via
  `Affine.Point.map (W' := W) (φ.toAlgHom)` / `(σ.toAlgHom.restrictScalars F)`, used by
  `translateAlgEquivOfPoint_map_genericPoint` and `genericPointAct`
  (`HasseWeil/EC/SeparableKernelTorsor.lean`).

## Note on mathlib status

`Point.map` carries `map_zero` (definitional), `Point.map_some`, `Point.map_id`, `Point.map_map`
and `Point.map_injective` in mathlib, and `map_add` / `map_zsmul` etc. come from its `AddMonoidHom`
structure (so they need no separate name). There is *also* a project-local ring-hom variant
`HasseWeil.Affine.Point.map (f : R →+* S) (hf : Function.Injective f)` with its own
`map_add`/`map_neg`/`map_zsmul` in `HasseWeil/EC/AffinePointMap.lean`; that one is for ring homs
between arbitrary commutative base rings and is unrelated to the algebra-hom bundling used here.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.
-/

open WeierstrassCurve

namespace WeierstrassCurve.Affine.Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra S F] [Algebra S K] {R : Type*} [CommRing R] [Algebra R S] [Algebra R F] [Algebra R K]
  [IsScalarTower R S F] [IsScalarTower R S K] {W' : Affine R} (f : F →ₐ[S] K)

/-- `Affine.Point.map f` respects addition: `(P + Q).map f = P.map f + Q.map f`.
This is `AddMonoidHom.map_add` for the bundled `Affine.Point.map`. -/
theorem map_add (P Q : (W'.baseChange F).Point) : map f (P + Q) = map f P + map f Q :=
  _root_.map_add (map f) P Q

/-- `Affine.Point.map f` respects negation: `(-P).map f = -(P.map f)`.
This is `AddMonoidHom.map_neg` for the bundled `Affine.Point.map`. -/
theorem map_neg (P : (W'.baseChange F).Point) : map f (-P) = -(map f P) :=
  _root_.map_neg (map f) P

/-- `Affine.Point.map f` respects subtraction: `(P - Q).map f = P.map f - Q.map f`. -/
theorem map_sub (P Q : (W'.baseChange F).Point) : map f (P - Q) = map f P - map f Q :=
  _root_.map_sub (map f) P Q

/-- `Affine.Point.map f` respects integer scalar multiplication: `(n • P).map f = n • P.map f`.
This is `AddMonoidHom.map_zsmul` for the bundled `Affine.Point.map`. -/
theorem map_zsmul (n : ℤ) (P : (W'.baseChange F).Point) : map f (n • P) = n • map f P :=
  AddMonoidHom.map_zsmul (map f) n P

/-- `Affine.Point.map f` respects natural-number scalar multiplication, via
`AddMonoidHom.map_nsmul` for the bundled `Affine.Point.map`. -/
theorem map_nsmul (n : ℕ) (P : (W'.baseChange F).Point) : map f (n • P) = n • map f P :=
  AddMonoidHom.map_nsmul (map f) n P

end WeierstrassCurve.Affine.Point

/-! ## Specialisation 1 — the lift `E(F) → E(K(E))` (`liftPointToKE`)

`HasseWeil.liftPointToKE W : W.toAffine.Point →+ (W_KE W).toAffine.Point` is, by definition,
`Affine.Point.map (Algebra.ofId F (W.toAffine.FunctionField))`, so it is the `AddMonoidHom`
above with `S = F`, `f = Algebra.ofId F K(E)`. We expose its group-hom equations under the
`liftPointToKE` name (the `_add` and `_zero` versions already live in `TranslationOrd`; here we add
`_neg`, `_sub`, `_zsmul`, `_nsmul`). -/

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

-- `liftPointToKE` is defined for any `W` over a field with `DecidableEq F`; it needs no
-- `IsElliptic`, so the group-hom corollaries below omit it.
omit [W.toAffine.IsElliptic] in
/-- `liftPointToKE` respects negation. -/
theorem liftPointToKE_neg (T : W.toAffine.Point) :
    liftPointToKE W (-T) = -(liftPointToKE W T) :=
  _root_.map_neg (liftPointToKE W) T

omit [W.toAffine.IsElliptic] in
/-- `liftPointToKE` respects subtraction. -/
theorem liftPointToKE_sub (T₁ T₂ : W.toAffine.Point) :
    liftPointToKE W (T₁ - T₂) = liftPointToKE W T₁ - liftPointToKE W T₂ :=
  _root_.map_sub (liftPointToKE W) T₁ T₂

omit [W.toAffine.IsElliptic] in
/-- `liftPointToKE` respects integer scalar multiplication. -/
theorem liftPointToKE_zsmul (n : ℤ) (T : W.toAffine.Point) :
    liftPointToKE W (n • T) = n • liftPointToKE W T :=
  AddMonoidHom.map_zsmul (liftPointToKE W) n T

omit [W.toAffine.IsElliptic] in
/-- `liftPointToKE` respects natural-number scalar multiplication. -/
theorem liftPointToKE_nsmul (n : ℕ) (T : W.toAffine.Point) :
    liftPointToKE W (n • T) = n • liftPointToKE W T :=
  AddMonoidHom.map_nsmul (liftPointToKE W) n T

/-! ## Specialisation 2 — the action of an `F`-algebra map of `K(E)` on `(W_KE).Point`

The function-field translations `translateAlgEquivOfPoint W k : K(E) ≃ₐ[F] K(E)` (via
`.toAlgHom`) and, more generally, any `F`-algebra map `φ : K(E) →ₐ[F] K(E)` act on the points
of `W_KE` through `Affine.Point.map (W' := W) φ`. This is mathlib's bundled `Affine.Point.map`
with `S = F`, the *same* curve on both sides (`W_KE W = W.map (algebraMap F K(E))`), so it too is
a group homomorphism; we record the equations specialised to that endo form. -/

local notation "KE" => W.toAffine.FunctionField

-- The endo lemmas below need neither `DecidableEq F` (the `(W_KE).Point` group structure routes
-- through the noncomputable `DecidableEq K(E)` from `Field`) nor `IsElliptic`.
omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Affine.Point.map (W' := W) φ` (`φ : K(E) →ₐ[F] K(E)` an `F`-algebra endomorphism of the
function field) respects addition on `(W_KE).Point`. Specialisation of
`Affine.Point.map_add` to the endo case used by `translateAlgEquivOfPoint_map_genericPoint`. -/
theorem map_genericFF_add (φ : KE →ₐ[F] KE) (P Q : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) φ (P + Q) =
      Affine.Point.map (W' := W) φ P + Affine.Point.map (W' := W) φ Q :=
  Affine.Point.map_add φ P Q

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Affine.Point.map (W' := W) φ` respects negation on `(W_KE).Point`. -/
theorem map_genericFF_neg (φ : KE →ₐ[F] KE) (P : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) φ (-P) = -(Affine.Point.map (W' := W) φ P) :=
  Affine.Point.map_neg φ P

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Affine.Point.map (W' := W) φ` respects subtraction on `(W_KE).Point`. -/
theorem map_genericFF_sub (φ : KE →ₐ[F] KE) (P Q : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) φ (P - Q) =
      Affine.Point.map (W' := W) φ P - Affine.Point.map (W' := W) φ Q :=
  Affine.Point.map_sub φ P Q

omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- `Affine.Point.map (W' := W) φ` respects integer scalar multiplication on `(W_KE).Point`.
Specialisation of `Affine.Point.map_zsmul` to the endo case used by `genericPointAct`. -/
theorem map_genericFF_zsmul (φ : KE →ₐ[F] KE) (n : ℤ) (P : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) φ (n • P) = n • Affine.Point.map (W' := W) φ P :=
  Affine.Point.map_zsmul φ n P

/-- The translation `τ = translateAlgEquivOfPoint W k`, lifted to `(W_KE).Point` via
`Affine.Point.map (W' := W) τ.toAlgHom`, respects addition. -/
theorem map_translate_add (k : W.toAffine.Point) (P Q : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom (P + Q) =
      Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom P +
        Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom Q :=
  Affine.Point.map_add _ P Q

/-- The translation `τ = translateAlgEquivOfPoint W k`, lifted via
`Affine.Point.map (W' := W) τ.toAlgHom`, respects integer scalar multiplication. -/
theorem map_translate_zsmul (k : W.toAffine.Point) (n : ℤ) (P : (W_KE W).toAffine.Point) :
    Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom (n • P) =
      n • Affine.Point.map (W' := W) (translateAlgEquivOfPoint W k).toAlgHom P :=
  Affine.Point.map_zsmul _ n P

end HasseWeil
