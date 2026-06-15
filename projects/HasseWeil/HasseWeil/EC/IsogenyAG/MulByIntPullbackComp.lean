/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.FrobeniusDual
import HasseWeil.EC.GenericPointZsmul
import HasseWeil.EC.TranslationOrd

/-!
# `[·]*`-multiplicativity and the faithful dual-of-composition (Silverman III.6.1)

`EC/IsogenyAG/FrobeniusDual.lean` ships dual-of-composition at the witness level with the
**conjugation** endomorphism `ν = φ̂ ∘ ν_ψ ∘ φ` and names the two facts blocking the
faithful Silverman form `ν = [n·m]`:

1. **multiplicativity** `[m·n]* = [n]* ∘ [m]*` of `mulByInt_pullbackAlgHom`
   (`mulByInt_pullbackAlgHom_mul` below — the pullback shadow of `[m] ∘ [n] = [m·n]`,
   Silverman III.4.2, contravariant order);
2. **pullback covariance** `[n]*_{E₁} ∘ φ* = φ* ∘ [n]*_{E₂}` (the function-field shadow of
   `[n] ∘ φ = φ ∘ [n]`, Silverman III.4.8).

This file discharges both and assembles the **faithful** composition
`Isogeny.HasMulByIntDualWitness.compose`: from an `[n]`-witness for `ψ` and an `[m]`-witness
for `φ` (plus the covariance of `φ` against `[n]`), the composite `ψ ∘ φ` carries the
faithful `[m·n]`-witness — so its dual satisfies `((ψ∘φ)^ ∘ (ψ∘φ))* = [m·n]*`, Silverman's
actual bookkeeping (`m·n = deg φ · deg ψ = deg (ψ∘φ)`, matching `Isogeny.compose_degree`).

## Multiplicativity (field-general, no carried hypotheses)

The heavy lifting already exists: `mulByInt_pullback_mulByInt_x_eq_mul` /
`mulByInt_pullback_mulByInt_y_eq_mul` (`EC/GenericPointZsmul.lean`) compute
`[n]*(mulByInt_x W m) = mulByInt_x W (m·n)` via the **all-points** division-polynomial
genuineness `zsmul_affine_point_eq` (the generic-point-only `IsGenuineWith` does *not* suffice:
the composite needs `[n]`'s action at the point `m • P_gen`, and `zsmul_affine_point_eq` with
the nonvanishing guard `ψ_m_evalEval_mulByInt_ne_zero` is exactly that action). The `AlgHom`
identity then follows from the generator extensionality `algHom_ext_x_y_gen`
(`EC/TranslationOrd.lean`).

## Covariance (per-isogeny; the honest hypothesis for abstract `φ`)

For an **abstract** `EC.Isogeny` the covariance is the project's open generic-point covariance
leaf (DUAL-2; Silverman III.4.8 is a theorem for genuine morphisms, but `EC.Isogeny` stores only
the pullback). It is packaged as `Isogeny.MulByIntPullbackCovariant` and:

* **reduced to its weakest checkable form** — the two generator equations — by
  `Isogeny.mulByIntPullbackCovariant_of_x_y_gen` (via the field-general `Ω`-codomain
  extensionality `algHom_ext_x_y_gen_into`, the `[Fintype K]`-free re-base of
  `GapSpines.algHom_ext_x_y_gen_omega`);
* **proved outright** for the two concrete isogeny families of this development:
  the `q`-power Frobenius (`Isogeny.frobenius_mulByIntPullbackCovariant`: `[n]*` is a ring hom,
  so it commutes with `g ↦ g^q`) and `[m]` itself
  (`Isogeny.mulByInt_mulByIntPullbackCovariant`: both sides are `[m·n]*` by multiplicativity).

## Main results

* `HasseWeil.mulByInt_pullbackAlgHom_mul` / `_mul'` — `[m·n]* = [n]* ∘ [m]*` (both orders),
  field-general.
* `HasseWeil.algHom_ext_x_y_gen_into` — generator extensionality into any codomain field.
* `EC.Isogeny.mulByInt_compose_mulByInt` — `[a] ∘ [b] = [a·b]` as `EC.Isogeny`s.
* `EC.Isogeny.MulByIntPullbackCovariant` + `_of_x_y_gen` + the Frobenius/`[m]` instances.
* `EC.Isogeny.HasMulByIntDualWitness.compose` — the **faithful** dual-of-composition.
* `EC.Isogeny.mulByIntDual_compose` — `φ̂ ∘ φ = [n]` in fully bundled form, for any faithful
  witness (generalizes `dualFrobenius_compose_frobenius`).
* `EC.mulByIntSelfDualWitness` — the faithful `[ℓ·ℓ]`-witness for `[ℓ]` (field-general:
  `Im [ℓ·ℓ]* ⊆ Im [ℓ]*` is *free* from multiplicativity; Silverman III.6.1 with
  `[ℓ]^ = [ℓ]`).
* `EC.frobeniusSquareMulByIntDualWitness` — the faithful `[q·q]`-witness for `π ∘ π`.
* `EC.mulByIntCompFrobeniusDualWitness` / `EC.frobeniusCompMulByIntDualWitness` — the faithful
  `[q·ℓ²]`- and `[ℓ²·q]`-witnesses for `[ℓ] ∘ π` and `π ∘ [ℓ]`.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.4.2 (`[m] ∘ [n] = [m·n]`), III.4.8
  (isogenies are group homomorphisms), III.6.1 (the dual isogeny; `(ψ∘φ)^ = φ̂ ∘ ψ̂`).
-/

open WeierstrassCurve

namespace HasseWeil

/-! ### Multiplicativity of the `[·]`-pullback (Silverman III.4.2, pullback shadow) -/

section Multiplicativity

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **Multiplicativity of the `[·]`-pullback** (Silverman III.4.2, function-field form):
`[m·n]* = [n]* ∘ [m]*` — the pullback shadow of `[m] ∘ [n] = [m·n]` (pullbacks compose
contravariantly: `[m]*` is applied first). Field-general, no carried hypotheses.

By generator extensionality (`algHom_ext_x_y_gen`) this reduces to the two division-polynomial
composition identities `[n]*(mulByInt_x/y W m) = mulByInt_x/y W (m·n)`
(`mulByInt_pullback_mulByInt_x/y_eq_mul`, `EC/GenericPointZsmul.lean`). -/
theorem mulByInt_pullbackAlgHom_mul (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    mulByInt_pullbackAlgHom W (m * n) (mul_ne_zero hm hn) =
      (mulByInt_pullbackAlgHom W n hn).comp (mulByInt_pullbackAlgHom W m hm) := by
  classical
  have hpb_n : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn :=
    dif_neg hn
  refine algHom_ext_x_y_gen W ?_ ?_
  · rw [mulByInt_pullbackAlgHom_x_gen W (m * n) (mul_ne_zero hm hn), AlgHom.comp_apply,
      mulByInt_pullbackAlgHom_x_gen W m hm, ← hpb_n,
      mulByInt_pullback_mulByInt_x_eq_mul W m n hm hn (mul_ne_zero hm hn)]
  · rw [mulByInt_pullbackAlgHom_y_gen W (m * n) (mul_ne_zero hm hn), AlgHom.comp_apply,
      mulByInt_pullbackAlgHom_y_gen W m hm, ← hpb_n,
      mulByInt_pullback_mulByInt_y_eq_mul W m n hn (mul_ne_zero hm hn)]

/-- `mulByInt_pullbackAlgHom` is congruent in the integer argument (the nonvanishing proof
transports along). -/
theorem mulByInt_pullbackAlgHom_congr {a b : ℤ} (h : a = b) (ha : a ≠ 0) :
    mulByInt_pullbackAlgHom W a ha = mulByInt_pullbackAlgHom W b (h ▸ ha) := by subst h; rfl

/-- **Multiplicativity, opposite order**: `[m·n]* = [m]* ∘ [n]*`. Since `ℤ` is commutative the
two factor pullbacks commute; this is `mulByInt_pullbackAlgHom_mul` after `mul_comm`. -/
theorem mulByInt_pullbackAlgHom_mul' (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    mulByInt_pullbackAlgHom W (m * n) (mul_ne_zero hm hn) =
      (mulByInt_pullbackAlgHom W m hm).comp (mulByInt_pullbackAlgHom W n hn) := by
  rw [mulByInt_pullbackAlgHom_congr W (mul_comm m n) (mul_ne_zero hm hn)]
  exact mulByInt_pullbackAlgHom_mul W n m hn hm

omit [W.toAffine.IsElliptic] in
/-- **Generator extensionality into an arbitrary codomain field** — the field-general re-base of
`GapSpines.algHom_ext_x_y_gen_omega` (whose section carries `[Fintype K]`): two `F`-algebra homs
`K(E) →ₐ[F] Ω` agreeing on `x_gen` and `y_gen` are equal. Same reduction chain as
`algHom_ext_x_y_gen` (`IsLocalization.algHom_ext` → `AdjoinRoot.algHom_ext'` →
`Polynomial.algHom_ext`); the codomain is irrelevant to it. -/
theorem algHom_ext_x_y_gen_into {Ω : Type*} [Field Ω] [Algebra F Ω]
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[F] Ω}
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W)) (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.toAffine.CoordinateRing)
  apply AdjoinRoot.algHom_ext'
  · apply Polynomial.algHom_ext
    change ψ₁ (algebraMap _ W.toAffine.FunctionField (algebraMap _ _ Polynomial.X)) =
      ψ₂ (algebraMap _ W.toAffine.FunctionField (algebraMap _ _ Polynomial.X))
    exact hx
  · change ψ₁ (algebraMap _ W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial)) =
      ψ₂ (algebraMap _ W.toAffine.FunctionField (AdjoinRoot.root W.toAffine.polynomial))
    exact hy

end Multiplicativity

namespace EC

open Curves

/-! ### `[a] ∘ [b] = [a·b]` as `EC.Isogeny`s -/

section ECMul

variable {F : Type*} [Field F]
variable (W : Affine F) [W.IsElliptic]

/-- **`[a] ∘ [b] = [a·b]` as `EC.Isogeny`s** (Silverman III.4.2, bundled): the EC-level
multiplication-by-integer isogenies compose multiplicatively. Pullback shadow:
`(([a]) ∘ ([b]))* = [b]* ∘ [a]* = [a·b]*` (`mulByInt_pullbackAlgHom_mul`). -/
theorem Isogeny.mulByInt_compose_mulByInt {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Isogeny.mulByInt W ha).compose (Isogeny.mulByInt W hb) =
      Isogeny.mulByInt W (mul_ne_zero ha hb) := by
  refine Isogeny.ext_toCurveMap (Curves.CurveMap.ext ?_)
  simp only [Isogeny.compose_toCurveMap, Curves.CurveMap.comp_pullback]
  exact (HasseWeil.mulByInt_pullbackAlgHom_mul W a b ha hb).symm

end ECMul

/-! ### The pullback covariance `[n]* ∘ φ* = φ* ∘ [n]*` (Silverman III.4.8, shadow)

For an abstract `EC.Isogeny` this is the open generic-point covariance leaf (DUAL-2): the
structure stores only the function-field pullback, and Silverman III.4.8 (`φ ∘ [n] = [n] ∘ φ`)
is a theorem about the *geometric* morphism, not a formal consequence of the pullback data. We
package it as a per-isogeny `Prop`, reduce it to its weakest checkable form (the two generator
equations), and discharge it outright for the concrete isogenies of this development
(Frobenius, `[m]`). -/

section Covariance

variable {F : Type*} [Field F]
variable {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The `[n]`-pullback covariance of an isogeny** (function-field shadow of
`[n] ∘ φ = φ ∘ [n]`, Silverman III.4.8): `[n]*_{E₁} ∘ φ* = φ* ∘ [n]*_{E₂}` pointwise. For
an abstract `EC.Isogeny` this is the open generic-point covariance leaf (DUAL-2), carried as a
hypothesis; it is a theorem for the concrete isogenies below
(`frobenius_mulByIntPullbackCovariant`, `mulByInt_mulByIntPullbackCovariant`). -/
def Isogeny.MulByIntPullbackCovariant (φ : Isogeny W₁ W₂) (n : ℤ) (hn : n ≠ 0) : Prop :=
  ∀ u : (⟨W₂⟩ : SmoothPlaneCurve F).FunctionField,
    HasseWeil.mulByInt_pullbackAlgHom W₁ n hn (φ.toCurveMap.pullback u) =
      φ.toCurveMap.pullback (HasseWeil.mulByInt_pullbackAlgHom W₂ n hn u)

/-- **The covariance from its generator instances** — the weakest checkable form: covariance on
all of `K(E₂)` follows from the two equations at `x_gen` and `y_gen` (where
`[n]*_{E₂} x_gen = mulByInt_x W₂ n` and `[n]*_{E₂} y_gen = mulByInt_y W₂ n` are substituted),
by the `Ω`-codomain generator extensionality applied to the two composites
`[n]*_{E₁} ∘ φ*, φ* ∘ [n]*_{E₂} : K(E₂) →ₐ[F] K(E₁)`. -/
theorem Isogeny.mulByIntPullbackCovariant_of_x_y_gen (φ : Isogeny W₁ W₂) (n : ℤ)
    (hn : n ≠ 0)
    (hx : HasseWeil.mulByInt_pullbackAlgHom W₁ n hn (φ.toCurveMap.pullback (x_gen W₂)) =
      φ.toCurveMap.pullback (mulByInt_x W₂ n))
    (hy : HasseWeil.mulByInt_pullbackAlgHom W₁ n hn (φ.toCurveMap.pullback (y_gen W₂)) =
      φ.toCurveMap.pullback (mulByInt_y W₂ n)) :
    φ.MulByIntPullbackCovariant n hn := by
  intro u
  have h : (HasseWeil.mulByInt_pullbackAlgHom W₁ n hn).comp φ.toCurveMap.pullback =
      φ.toCurveMap.pullback.comp (HasseWeil.mulByInt_pullbackAlgHom W₂ n hn) := by
    refine HasseWeil.algHom_ext_x_y_gen_into W₂ ?_ ?_
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        HasseWeil.mulByInt_pullbackAlgHom_x_gen W₂ n hn]
      exact hx
    · rw [AlgHom.comp_apply, AlgHom.comp_apply,
        HasseWeil.mulByInt_pullbackAlgHom_y_gen W₂ n hn]
      exact hy
  exact DFunLike.congr_fun h u

end Covariance

section FrobeniusCovariance

variable {K : Type*} [Field K] [Fintype K]
variable (W : Affine K) [W.IsElliptic]

/-- **The Frobenius satisfies the `[n]`-pullback covariance** (Silverman III.4.8 for `π`,
unconditional): `π* = (·)^q` and `[n]*` is a ring hom, so
`[n]*(π* u) = [n]*(u^q) = ([n]* u)^q = π*([n]* u)`. -/
theorem Isogeny.frobenius_mulByIntPullbackCovariant (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.frobenius W).MulByIntPullbackCovariant n hn := by
  classical
  intro u
  simp only [Isogeny.frobenius_pullback, map_pow]

end FrobeniusCovariance

section MulByIntCovariance

variable {F : Type*} [Field F]
variable (W : Affine F) [W.IsElliptic]

/-- **`[m]` satisfies the `[n]`-pullback covariance** (Silverman III.4.8 for `[m]`,
unconditional): both sides equal `[m·n]*` by multiplicativity (`mulByInt_pullbackAlgHom_mul`
and `_mul'`). -/
theorem Isogeny.mulByInt_mulByIntPullbackCovariant {m : ℤ} (hm : m ≠ 0) (n : ℤ)
    (hn : n ≠ 0) :
    (Isogeny.mulByInt W hm).MulByIntPullbackCovariant n hn := fun u =>
  (DFunLike.congr_fun (HasseWeil.mulByInt_pullbackAlgHom_mul W m n hm hn) u).symm.trans
    (DFunLike.congr_fun (HasseWeil.mulByInt_pullbackAlgHom_mul' W m n hm hn) u)

end MulByIntCovariance

/-! ### The faithful dual-of-composition (Silverman III.6.1 for composites)

Given the faithful `[n]`-witness for `ψ : E₂ → E₃` and the faithful `[m]`-witness for
`φ : E₁ → E₂`, plus the covariance of `φ` against `[n]`, the composite `ψ ∘ φ` carries
the faithful `[m·n]`-witness:

`[m·n]* w = [n]*([m]* w)` (multiplicativity) `= [n]*(φ* u)` (the `[m]`-witness)
`= φ*([n]* u)` (covariance) `= φ*(ψ* t)` (the `[n]`-witness) `= (ψ∘φ)* t`.

With `m = deg φ`, `n = deg ψ` this is Silverman's `(ψ∘φ)^ ∘ (ψ∘φ) = [deg φ · deg ψ]`
(`m·n = (ψ∘φ).degree` by `Isogeny.compose_degree`). -/

section FaithfulComposition

variable {F : Type*} [Field F]
variable {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

namespace Isogeny

namespace HasMulByIntDualWitness

/-- **Range inclusion for the faithful composite witness**:
`Im([m·n]*) ⊆ Im((ψ ∘ φ)*)`, from the two component inclusions, multiplicativity, and the
covariance of `φ` against `[n]`. -/
theorem compose_rangeIncl {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    {n m : ℤ} {hn : n ≠ 0} {hm : m ≠ 0}
    (wψ : ψ.HasMulByIntDualWitness n hn) (wφ : φ.HasMulByIntDualWitness m hm)
    (hcov : φ.MulByIntPullbackCovariant n hn) :
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (m * n) (mul_ne_zero hm hn)).range ≤
      (ψ.compose φ).toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := wφ.hincl ⟨w, rfl⟩
  obtain ⟨t, ht⟩ := wψ.hincl ⟨u, rfl⟩
  refine ⟨t, ?_⟩
  -- The range memberships are phrased through `.toRingHom`; recast them (defeq) in plain
  -- `AlgHom`-application form so the rewrites below match.
  have hu' : φ.toCurveMap.pullback u = HasseWeil.mulByInt_pullbackAlgHom W₁ m hm w := hu
  have ht' : ψ.toCurveMap.pullback t = HasseWeil.mulByInt_pullbackAlgHom W₂ n hn u := ht
  change φ.toCurveMap.pullback (ψ.toCurveMap.pullback t) =
    HasseWeil.mulByInt_pullbackAlgHom W₁ (m * n) (mul_ne_zero hm hn) w
  rw [ht', ← hcov u, hu']
  exact (DFunLike.congr_fun
    (HasseWeil.mulByInt_pullbackAlgHom_mul W₁ m n hm hn) w).symm

/-- **The faithful dual-of-composition** (Silverman III.6.1 for composites): faithful witnesses
compose — an `[n]`-witness for `ψ` and an `[m]`-witness for `φ` yield the `[m·n]`-witness for
`ψ ∘ φ`, given the covariance of `φ` against `[n]` (a theorem for Frobenius and `[m]`; the
open DUAL-2 leaf for an abstract isogeny). The resulting dual satisfies
`((ψ∘φ)^ ∘ (ψ∘φ))* = [m·n]*` (`mulByIntDual_comp_pullback`), with `m·n = deg(ψ∘φ)`
when `m = deg φ`, `n = deg ψ` (`compose_degree`) — the faithful Silverman bookkeeping, upgrading the
conjugation-form `HasDualWitness.compose`. -/
noncomputable def compose {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    {n m : ℤ} {hn : n ≠ 0} {hm : m ≠ 0}
    (wψ : ψ.HasMulByIntDualWitness n hn) (wφ : φ.HasMulByIntDualWitness m hm)
    (hcov : φ.MulByIntPullbackCovariant n hn) :
    (ψ.compose φ).HasMulByIntDualWitness (m * n) (mul_ne_zero hm hn) where
  hincl := compose_rangeIncl wψ wφ hcov
  hbase := Isogeny.hbase_of_reflects (ψ.compose φ)
    (HasseWeil.mulByInt_pullbackAlgHom W₁ (m * n) (mul_ne_zero hm hn))
    (compose_rangeIncl wψ wφ hcov)
    (mulByIntBasepoint_holds W₁ (mul_ne_zero hm hn))
    (Isogeny.reflects_ordAtInfty (ψ.compose φ))

end HasMulByIntDualWitness

/-- **`φ̂ ∘ φ = [n]` in fully bundled form** (Silverman III.6.1 defining identity), for *any*
faithful `[n]`-witness: the composite of the faithful dual with `φ` *is* the
multiplication-by-`n` isogeny. Generalizes `dualFrobenius_compose_frobenius`; applied to a
composed witness it is the III.6.1 identity for composites. -/
theorem mulByIntDual_compose {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) :
    (Isogeny.mulByIntDual w).compose φ = Isogeny.mulByInt W₁ hn := by
  classical
  exact Isogeny.ext_toCurveMap (Curves.CurveMap.ext (AlgHom.ext fun z =>
    Isogeny.mulByIntDual_comp_pullback w z))

end Isogeny

end FaithfulComposition

/-! ### The faithful `[ℓ·ℓ]`-witness for `[ℓ]` (field-general)

Silverman III.6.1 for `φ = [ℓ]` with `φ̂ = [ℓ]`: the range inclusion
`Im([ℓ·ℓ]*) ⊆ Im([ℓ]*)` is *free* from multiplicativity (`[ℓ·ℓ]* = [ℓ]* ∘ [ℓ]*`), and the
basepoint condition is the `MulByIntBasepoint` theorem. No `[IsAlgClosed F]` (contrast
`dualMulByInt`, `DualGaloisClosed.lean`, whose Galois route needs the rational `ℓ`-torsion of
`K̄`): the dual
*witness* here is faithful by construction rather than recovered from the fixed field. -/

section MulByIntSelfWitness

variable {F : Type*} [Field F]
variable (W : Affine F) [W.IsElliptic]

/-- The range inclusion `Im([ℓ·ℓ]*) ⊆ Im([ℓ]*)`, free from multiplicativity:
`[ℓ·ℓ]* w = [ℓ]*([ℓ]* w)`. -/
theorem mulByInt_self_rangeIncl {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    (HasseWeil.mulByInt_pullbackAlgHom W (ℓ * ℓ) (mul_ne_zero hℓ hℓ)).range ≤
      (Isogeny.mulByInt W hℓ).toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  exact ⟨HasseWeil.mulByInt_pullbackAlgHom W ℓ hℓ w,
    (DFunLike.congr_fun (HasseWeil.mulByInt_pullbackAlgHom_mul W ℓ ℓ hℓ hℓ) w).symm⟩

/-- **The faithful `[ℓ·ℓ]`-dual witness for `[ℓ]`** (Silverman III.6.1 with
`[ℓ]^ = [ℓ]`), field-general, every field a theorem: `hincl` is free from multiplicativity
(`mulByInt_self_rangeIncl`), `hbase` from the `[ℓ·ℓ]`-basepoint theorem and `∞`-regularity
reflection. -/
noncomputable def mulByIntSelfDualWitness {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    (Isogeny.mulByInt W hℓ).HasMulByIntDualWitness (ℓ * ℓ) (mul_ne_zero hℓ hℓ) where
  hincl := mulByInt_self_rangeIncl W hℓ
  hbase := Isogeny.hbase_of_reflects (Isogeny.mulByInt W hℓ)
    (HasseWeil.mulByInt_pullbackAlgHom W (ℓ * ℓ) (mul_ne_zero hℓ hℓ))
    (mulByInt_self_rangeIncl W hℓ)
    (mulByIntBasepoint_holds W (mul_ne_zero hℓ hℓ))
    (Isogeny.reflects_ordAtInfty (Isogeny.mulByInt W hℓ))

end MulByIntSelfWitness

/-! ### Demonstrations over a finite field

The faithful witnesses compose for the concrete isogenies: `π ∘ π` carries the
`[q·q]`-witness, `[ℓ] ∘ π` the `[q·ℓ²]`-witness, and `π ∘ [ℓ]` the `[ℓ²·q]`-witness — each
matching Silverman's degree bookkeeping (`deg(ψ∘φ) = deg φ · deg ψ`,
`Isogeny.compose_degree`, with `deg π = q`).
Both covariance legs are theorems here (Frobenius: ring-hom vs `q`-th power; `[ℓ]`:
multiplicativity), so **every field of every witness below is a theorem**. -/

section Demos

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

/-- **The faithful `[q·q]`-witness for `π ∘ π`** — the faithful upgrade of
`hasDualWitness_frobenius_compose_frobenius` (whose conjugation `ν` is now the genuine
`[q·q] = [deg (π∘π)]`). Every field a theorem. -/
noncomputable def frobeniusSquareMulByIntDualWitness :
    ((Isogeny.frobenius W).compose (Isogeny.frobenius W)).HasMulByIntDualWitness
      (((Fintype.card K : ℕ) : ℤ) * ((Fintype.card K : ℕ) : ℤ))
      (mul_ne_zero intCardK_ne_zero intCardK_ne_zero) :=
  (frobeniusMulByIntDualWitness W).compose (frobeniusMulByIntDualWitness W)
    (Isogeny.frobenius_mulByIntPullbackCovariant W _ intCardK_ne_zero)

-- `[DecidableEq K]` is genuinely required: the statement names the composed witness
-- `frobeniusSquareMulByIntDualWitness` (which carries it), but the witness sits in a
-- proof-irrelevant position, so the linter cannot see the dependence.
set_option linter.unusedDecidableInType false in
/-- **`(π∘π)^ ∘ (π∘π) = [q·q]` as `EC.Isogeny`s** — Silverman III.6.1 for the composite
`π ∘ π`, in fully bundled form, via the faithful composed witness. -/
theorem frobeniusSquare_mulByIntDual_compose :
    (Isogeny.mulByIntDual (frobeniusSquareMulByIntDualWitness W)).compose
        ((Isogeny.frobenius W).compose (Isogeny.frobenius W)) =
      Isogeny.mulByInt W
        (mul_ne_zero (intCardK_ne_zero (K := K)) (intCardK_ne_zero (K := K))) :=
  Isogeny.mulByIntDual_compose _

/-- **The faithful `[q·ℓ²]`-witness for `[ℓ] ∘ π`** — composing the field-general
`[ℓ·ℓ]`-witness for `[ℓ]` with the `[q]`-witness for `π` along the (free) Frobenius
covariance. `q·(ℓ·ℓ) = deg π · deg [ℓ] = deg ([ℓ]∘π)` is Silverman's bookkeeping. Every
field a theorem. -/
noncomputable def mulByIntCompFrobeniusDualWitness {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ((Isogeny.mulByInt W hℓ).compose (Isogeny.frobenius W)).HasMulByIntDualWitness
      (((Fintype.card K : ℕ) : ℤ) * (ℓ * ℓ))
      (mul_ne_zero intCardK_ne_zero (mul_ne_zero hℓ hℓ)) :=
  (mulByIntSelfDualWitness W hℓ).compose (frobeniusMulByIntDualWitness W)
    (Isogeny.frobenius_mulByIntPullbackCovariant W _ (mul_ne_zero hℓ hℓ))

/-- **The faithful `[ℓ²·q]`-witness for `π ∘ [ℓ]`** — the opposite composition order,
exercising the `[m]`-covariance instance (from multiplicativity). Every field a theorem. -/
noncomputable def frobeniusCompMulByIntDualWitness {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ((Isogeny.frobenius W).compose (Isogeny.mulByInt W hℓ)).HasMulByIntDualWitness
      ((ℓ * ℓ) * ((Fintype.card K : ℕ) : ℤ))
      (mul_ne_zero (mul_ne_zero hℓ hℓ) intCardK_ne_zero) :=
  (frobeniusMulByIntDualWitness W).compose (mulByIntSelfDualWitness W hℓ)
    (Isogeny.mulByInt_mulByIntPullbackCovariant W hℓ _ intCardK_ne_zero)

end Demos

end EC

end HasseWeil
