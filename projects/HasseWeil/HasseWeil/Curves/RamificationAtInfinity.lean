/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

import HasseWeil.Curves.Infinity

/-!
# Abstract ramification at infinity (Worker A Action 1)

For a smooth plane curve `C` over a field `k` and a nonconstant function
`f ∈ K(C)`, this file establishes the **function-field-degree-equals-pole-
divisor-degree identity**:

```
[K(C) : k(f)] = Σ_{P pole of f} (- ord_P f) · [κ(P) : k].
```

This is *not* Riemann–Roch. It is the degree formula for the finite morphism
`f : C → ℙ¹`, scoped to the fibre at `∞`. The proof goes via Mathlib's
`Ideal.sum_ramification_inertia` applied at the `(u)`-prime of `k[u]`, where
`u = 1/f` is the uniformizer at infinity on `ℙ¹`:

  * `e_P = ord_P(u) = -ord_P(f)` (ramification index),
  * `f_P = [κ(P) : κ((u))] = [κ(P) : k]` (inertia degree).

## Strategy

The proof packages Mathlib's abstract ramification–inertia machinery: pick
the integral closure `S` of `k[u]` in `K(C)` (via the algebra structure
`u ↦ 1/f`), observe `S` is Dedekind, then `Ideal.sum_ramification_inertia`
at the `(u)` prime gives the sum directly. The curve-specific notation
(`poleSupport`, `ordAt`, `kappa`) is bookkeeping over the resulting finset.

This is the deliverable for "Worker A — Action 1 abstract ramification-at-
infinity setup". Worker B's closing application combines this with their
Action 2 (translation valuation transport) plus Action 3 (a small closed-
point lemma) to discharge the project's `pc_sepDeg_eq_pointCount` witness.

## Main definitions

* `polyToFieldOfInv f`, `ratFunToFieldOfInv hf` — the `k`-algebra maps
  `Polynomial k →ₐ[k] L` and `FractionRing (Polynomial k) →ₐ[k] L` sending the
  indeterminate to `f⁻¹` (the uniformizer `u = 1/f`).
* `LinfAt f` — `L` as a type synonym carrying the `X ↦ f⁻¹` polynomial-algebra
  structure, so it does not clash with the project's pre-existing `X ↦ coordX`
  instance.
* `Sinf f` — structural package of "an integral closure of `Polynomial k` in
  `LinfAt f`": the carrier plus every typeclass instance the closing theorem
  needs as an honest field.
* `xIdeal`, `Sinf.ordAt`, `Sinf.kappa` — the prime `(X)` at infinity, the order
  `-(ramificationIdx …)`, and the residue field `carrier ⧸ P`.

## Main results

* `finrank_eq_sum_ramificationIdx_mul_inertiaDeg` — the abstract fundamental
  identity `Σ e(P) · f(P) = [LinfAt f : k(f)]` from `Ideal.sum_ramification_inertia`.
* `finrank_eq_weighted_poleDegree_of_nonconstant` — the closing corollary
  `[L : k(f)] = Σ_P (−ord_P f) · inertiaDeg P`.
* `Sinf.inertiaDeg_eq_one_of_algebraMap_surjective` — `inertiaDeg (X) P = 1`
  when the residue map `k → κ(P)` is surjective.

## Implementation notes

`LinfAt` and `Sinf` exist to dodge two Lean-elaboration hazards. `LinfAt f`
isolates the `X ↦ f⁻¹` algebra structure from the project's `X ↦ coordX` one;
transcendence is carried as `Fact (Transcendental k f⁻¹)` (use sites declare
`haveI : Fact (Transcendental k f⁻¹) := ⟨_⟩` once and the algebra instances
resolve). `Sinf` bundles the integral-closure instances as record fields so they
resolve by projection, sidestepping the `Meta.SynthInstance.tryResolve`
negative-cache anomaly that the `↥(integralClosure …)` Subalgebra coercion
triggers under `Ideal.sum_ramification_inertia` (commit 538ff64).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.2 (degree of a
  morphism between curves; formula II.2.6.a as the sum over preimages of
  one point).
* Mathlib's `Ideal.sum_ramification_inertia` provides the abstract
  fundamental identity `Σ e · f = [Frac S : Frac R]`.
-/

namespace HasseWeil.Curves

namespace RamificationAtInfinity

variable {k : Type*} [Field k]

/-- The `k`-algebra map `Polynomial k → L` sending `X` to `f⁻¹`. This is
the canonical "uniformizer at infinity" embedding used to apply Mathlib's
`Ideal.sum_ramification_inertia` for the finite morphism `f : C → ℙ¹`. -/
noncomputable def polyToFieldOfInv {L : Type*} [Field L] [Algebra k L]
    (f : L) : Polynomial k →ₐ[k] L :=
  Polynomial.aeval f⁻¹

@[simp] theorem polyToFieldOfInv_X {L : Type*} [Field L] [Algebra k L]
    (f : L) : polyToFieldOfInv (k := k) f Polynomial.X = f⁻¹ :=
  Polynomial.aeval_X f⁻¹

@[simp] theorem polyToFieldOfInv_C {L : Type*} [Field L] [Algebra k L]
    (f : L) (c : k) :
    polyToFieldOfInv (k := k) f (Polynomial.C c) = algebraMap k L c :=
  Polynomial.aeval_C f⁻¹ c

theorem polyToFieldOfInv_injective_of_transcendental
    {L : Type*} [Field L] [Algebra k L]
    {f : L} (hf : Transcendental k f⁻¹) :
    Function.Injective (polyToFieldOfInv (k := k) f) := by
  rw [polyToFieldOfInv]
  exact (transcendental_iff_injective).mp hf

/-- Sending a polynomial to its `f⁻¹`-evaluation factors as the algebra
map `k → L` composed with the constant polynomial. -/
@[simp] theorem polyToFieldOfInv_algebraMap_eq
    {L : Type*} [Field L] [Algebra k L] (f : L) (c : k) :
    polyToFieldOfInv (k := k) f (algebraMap k _ c) = algebraMap k L c := by
  rw [Polynomial.algebraMap_eq, polyToFieldOfInv_C]

/-- `polyToFieldOfInv f` is nonzero on a nonzero polynomial when `f⁻¹` is
transcendental. -/
theorem polyToFieldOfInv_ne_zero_of_ne_zero
    {L : Type*} [Field L] [Algebra k L]
    {f : L} (hf : Transcendental k f⁻¹) {p : Polynomial k} (hp : p ≠ 0) :
    polyToFieldOfInv (k := k) f p ≠ 0 := by
  intro h
  exact hp (polyToFieldOfInv_injective_of_transcendental hf
    (by simpa [map_zero] using h))

/-- The `k`-algebra map `FractionRing (Polynomial k) →ₐ[k] L` extending
`polyToFieldOfInv f`. Concretely, sends the formal indeterminate to `f⁻¹`,
and `1/X ↦ f`. Requires `f⁻¹` (equivalently, `f`) to be transcendental
over `k` so that the polynomial map is injective and the lift makes sense. -/
noncomputable def ratFunToFieldOfInv {L : Type*} [Field L] [Algebra k L]
    {f : L} (hf : Transcendental k f⁻¹) :
    FractionRing (Polynomial k) →ₐ[k] L :=
  IsFractionRing.liftAlgHom (R := k) (A := Polynomial k)
    (K := FractionRing (Polynomial k)) (L := L)
    (g := polyToFieldOfInv (k := k) f)
    (polyToFieldOfInv_injective_of_transcendental hf)

/-- `ratFunToFieldOfInv hf` is injective as a `k`-algebra map between fields. -/
theorem ratFunToFieldOfInv_injective {L : Type*} [Field L] [Algebra k L]
    {f : L} (hf : Transcendental k f⁻¹) :
    Function.Injective (ratFunToFieldOfInv hf) :=
  (ratFunToFieldOfInv hf).toRingHom.injective

/-- The function field viewed as a type-synonym, used to install a
`Polynomial k`-algebra structure via `X ↦ f⁻¹` that does not conflict with
the project's existing `X ↦ coordX` instance.
The unused argument `_f` indexes the algebra structure intended for the
synonym. -/
@[nolint unusedArguments]
def LinfAt {L : Type*} [Field L] [Algebra k L] (_f : L) : Type _ := L

namespace LinfAt

instance {L : Type*} [Field L] [Algebra k L] (f : L) :
    Field (LinfAt (k := k) f) := ‹Field L›
instance {L : Type*} [Field L] [Algebra k L] (f : L) :
    Algebra k (LinfAt (k := k) f) := ‹Algebra k L›

/-- The alternative `Polynomial k`-algebra structure on `LinfAt f` sending
`X ↦ f⁻¹`. This is the structure used by Mathlib's
`Ideal.sum_ramification_inertia` machinery in the ramification-at-infinity
setup. -/
noncomputable instance algebraPolynomial
    {L : Type*} [Field L] [Algebra k L] (f : L) :
    Algebra (Polynomial k) (LinfAt (k := k) f) :=
  ((polyToFieldOfInv (k := k) f).toRingHom : Polynomial k →+* L).toAlgebra

/-- `algebraMap (Polynomial k) (LinfAt f)` is `polyToFieldOfInv f` as a
function (composed with the identity transport to `LinfAt f`). -/
theorem algebraMap_polynomial_apply
    {L : Type*} [Field L] [Algebra k L] (f : L) (p : Polynomial k) :
    (algebraMap (Polynomial k) (LinfAt (k := k) f) p : L) =
      polyToFieldOfInv (k := k) f p :=
  rfl

/-- The `k`-action and `Polynomial k`-action on `LinfAt f` are compatible:
`k → Polynomial k → LinfAt f` and `k → LinfAt f` give the same map. -/
instance isScalarTower_k_polynomial
    {L : Type*} [Field L] [Algebra k L] (f : L) :
    IsScalarTower k (Polynomial k) (LinfAt (k := k) f) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change (algebraMap k L c : L) = polyToFieldOfInv (k := k) f
      (algebraMap k (Polynomial k) c)
    rw [polyToFieldOfInv_algebraMap_eq]

/-- The `FractionRing (Polynomial k)`-algebra structure on `LinfAt f`,
parametrised on `Fact (Transcendental k f⁻¹)` (the nonconstancy of `f`).
Sends the formal indeterminate to `f⁻¹` and `1/X ↦ f`. -/
noncomputable instance algebraFractionRing
    {L : Type*} [Field L] [Algebra k L] (f : L)
    [hf : Fact (Transcendental k f⁻¹)] :
    Algebra (FractionRing (Polynomial k)) (LinfAt (k := k) f) :=
  ((ratFunToFieldOfInv hf.out).toRingHom :
    FractionRing (Polynomial k) →+* L).toAlgebra

/-- `algebraMap (FractionRing (Polynomial k)) (LinfAt f)` is
`ratFunToFieldOfInv hf` as a function. -/
theorem algebraMap_fractionRing_apply
    {L : Type*} [Field L] [Algebra k L] (f : L)
    [hf : Fact (Transcendental k f⁻¹)]
    (q : FractionRing (Polynomial k)) :
    (algebraMap (FractionRing (Polynomial k))
        (LinfAt (k := k) f) q : L) =
      ratFunToFieldOfInv hf.out q :=
  rfl

/-- The `Polynomial k → FractionRing (Polynomial k) → LinfAt f` tower
commutes: this is the universal property of `IsFractionRing.lift` applied to
the lift `ratFunToFieldOfInv`. -/
instance isScalarTower_polynomial_fractionRing
    {L : Type*} [Field L] [Algebra k L] (f : L)
    [hf : Fact (Transcendental k f⁻¹)] :
    IsScalarTower (Polynomial k) (FractionRing (Polynomial k))
      (LinfAt (k := k) f) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    change (polyToFieldOfInv (k := k) f p : L) =
      ratFunToFieldOfInv hf.out
        (algebraMap (Polynomial k) (FractionRing (Polynomial k)) p)
    exact ((ratFunToFieldOfInv hf.out).comp
      (IsScalarTower.toAlgHom k (Polynomial k)
        (FractionRing (Polynomial k)))).congr_fun
      (by ext; simp [ratFunToFieldOfInv, polyToFieldOfInv]) p |>.symm

/-- The `k → FractionRing (Polynomial k) → LinfAt f` tower commutes: the
`k`-algebra structure on `LinfAt f` agrees with the one inherited via the
fraction-ring algebra map. -/
instance isScalarTower_k_fractionRing
    {L : Type*} [Field L] [Algebra k L] (f : L)
    [hf : Fact (Transcendental k f⁻¹)] :
    IsScalarTower k (FractionRing (Polynomial k)) (LinfAt (k := k) f) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change (algebraMap k L c : L) =
      ratFunToFieldOfInv hf.out (algebraMap k (FractionRing (Polynomial k)) c)
    exact ((ratFunToFieldOfInv hf.out).commutes c).symm

end LinfAt

/-- Structural package of "an integral closure of `Polynomial k` inside
`LinfAt f`": carrier type plus every typeclass instance the closing
`Ideal.sum_ramification_inertia` invocation requires, bundled as record
fields so `letI` can install them at the use site. Sidesteps the Lean 4
synthesis anomaly that affects the `↥(integralClosure …)` Subalgebra
coercion (commit 538ff64). -/
structure Sinf.{u} {L : Type*} [Field L] [Algebra k L] (f : L) where
  /-- Carrier type — canonically `↥(integralClosure (Polynomial k) (LinfAt f))`. -/
  carrier : Type u
  /-- Commutative-ring structure on the carrier. -/
  [commRing : CommRing carrier]
  /-- The carrier is an integral domain. -/
  [isDomain : IsDomain carrier]
  /-- The carrier is a Dedekind domain. -/
  [isDedekindDomain : IsDedekindDomain carrier]
  /-- The `Polynomial k`-algebra structure carrying `X ↦ f⁻¹` through the
  integral-closure inclusion. -/
  [algPoly : Algebra (Polynomial k) carrier]
  /-- The carrier embeds into `LinfAt f`. -/
  [algLinfAt : Algebra carrier (LinfAt (k := k) f)]
  /-- The embedding realises `LinfAt f` as the fraction field of the carrier. -/
  [isFractionRing : IsFractionRing carrier (LinfAt (k := k) f)]
  /-- Compatible scalar tower with the ambient `Polynomial k → LinfAt f`. -/
  [isScalarTower : IsScalarTower (Polynomial k) carrier (LinfAt (k := k) f)]
  /-- Finite as a `Polynomial k`-module. -/
  [moduleFinite : Module.Finite (Polynomial k) carrier]
  /-- Torsion-free as a `Polynomial k`-module (algebraMap injective). -/
  [isTorsionFree : Module.IsTorsionFree (Polynomial k) carrier]

section SinfConstruction

set_option backward.isDefEq.respectTransparency false

/-- Canonical construction of `Sinf` from Mathlib's `integralClosure`
Subalgebra. Given the ambient finite-separability hypotheses, all the
required instances are synthesised once here; downstream code consumes
them only by field projection.

The local `set_option backward.isDefEq.respectTransparency false` matches
Mathlib's `NormalClosure` pattern (see `Mathlib/RingTheory/NormalClosure.lean`
line 79) for the `Algebra ↥(integralClosure …) _` instance synthesis —
without this option the `Meta.SynthInstance.tryResolve` metavariable wall
hits us exactly here. -/
noncomputable def Sinf.ofIntegralClosure
    {L : Type*} [Field L] [Algebra k L] (f : L) [Fact (Transcendental k f⁻¹)]
    [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)]
    [Algebra.IsSeparable (FractionRing (Polynomial k)) (LinfAt (k := k) f)] :
    Sinf (k := k) f :=
  haveI : IsFractionRing
      (integralClosure (Polynomial k) (LinfAt (k := k) f)) (LinfAt (k := k) f) :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      (Polynomial k) (FractionRing (Polynomial k)) (LinfAt (k := k) f)
      (integralClosure (Polynomial k) (LinfAt (k := k) f))
  haveI : Module.Finite (Polynomial k)
      (integralClosure (Polynomial k) (LinfAt (k := k) f)) :=
    IsIntegralClosure.finite (Polynomial k) (FractionRing (Polynomial k))
      (LinfAt (k := k) f) (integralClosure (Polynomial k) (LinfAt (k := k) f))
  haveI : FaithfulSMul (Polynomial k) (LinfAt (k := k) f) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    exact polyToFieldOfInv_injective_of_transcendental
      (Fact.out (p := Transcendental k f⁻¹))
  haveI : Module.IsTorsionFree (Polynomial k) (LinfAt (k := k) f) :=
    inferInstance
  haveI : Module.IsTorsionFree (Polynomial k)
      (integralClosure (Polynomial k) (LinfAt (k := k) f)) :=
    Subalgebra.instIsTorsionFree (integralClosure (Polynomial k)
      (LinfAt (k := k) f))
  { carrier := integralClosure (Polynomial k) (LinfAt (k := k) f) }

end SinfConstruction

/-- The prime `(X) ⊂ Polynomial k`. Its quotient is `k`, so it is maximal.
Under our `X ↦ f⁻¹` algebra structure, this is the prime "at infinity" of
the morphism `f : C → ℙ¹`. -/
noncomputable abbrev xIdeal : Ideal (Polynomial k) :=
  Ideal.span {Polynomial.X}

instance xIdeal_isMaximal : (xIdeal (k := k)).IsMaximal := by
  unfold xIdeal
  exact (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
    Polynomial.prime_X |>.isMaximal
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_ne_zero)

theorem xIdeal_ne_bot : (xIdeal (k := k)) ≠ ⊥ := by
  unfold xIdeal
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact Polynomial.X_ne_zero

/-- **Abstract fundamental ramification–inertia identity at infinity.**
For a function `f` realising `LinfAt f` as a finite separable extension of
`FractionRing (Polynomial k) = k(f)` and an integral-closure package
`data : Sinf k f`, the sum over primes of the carrier lying over `(X)` of
`e(P) · f(P)` equals `[LinfAt f : k(f)]`. This is the abstract content of
the `[K(C):k(f)] = Σ (pole degree)` identity, before specialisation to
`LinfAt f = K(C)` for a smooth curve `C`. -/
theorem finrank_eq_sum_ramificationIdx_mul_inertiaDeg
    {L : Type*} [Field L] [Algebra k L] (f : L) [Fact (Transcendental k f⁻¹)]
    [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)]
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    ∑ P ∈ primesOverFinset (xIdeal (k := k)) data.carrier,
        Ideal.ramificationIdx (xIdeal (k := k)) P *
        Ideal.inertiaDeg (xIdeal (k := k)) P =
      Module.finrank (FractionRing (Polynomial k)) (LinfAt (k := k) f) := by
  letI := data.commRing
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algPoly
  letI := data.algLinfAt
  letI := data.isFractionRing
  letI := data.isScalarTower
  letI := data.moduleFinite
  exact Ideal.sum_ramification_inertia (R := Polynomial k) data.carrier
    (FractionRing (Polynomial k)) (LinfAt (k := k) f) xIdeal_ne_bot

/-- The `R[X] ⧸ (X) ≃ₐ[R] R`-style algebra equivalence specialised to
`R = k`, given by evaluation at `0`. -/
noncomputable def quotientXAlgEquiv :
    (Polynomial k ⧸ xIdeal (k := k)) ≃ₐ[k] k :=
  have h : (Ideal.span {Polynomial.X} : Ideal (Polynomial k)) =
      Ideal.span {Polynomial.X - Polynomial.C (0 : k)} := by
    congr 1
    rw [Polynomial.C_0, sub_zero]
  (Ideal.quotientEquivAlgOfEq k h).trans (Polynomial.quotientSpanXSubCAlgEquiv 0)

/-- **Bridge 2 (definitional).** Order at `P` of `f` (abstract Sinf
version): minus the ramification index. By definition. -/
noncomputable def Sinf.ordAt {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.algPoly
    Ideal data.carrier → ℤ :=
  letI := data.commRing
  letI := data.algPoly
  fun P => -(Ideal.ramificationIdx (xIdeal (k := k)) P : ℤ)

/-- The natural-number coercion: `(−ord_P f).toNat = e_P`. -/
theorem Sinf.toNat_neg_ordAt_eq_ramificationIdx
    {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.algPoly
    ∀ P : Ideal data.carrier,
      (-(data.ordAt P)).toNat =
        Ideal.ramificationIdx (xIdeal (k := k)) P := by
  letI := data.commRing
  letI := data.algPoly
  intro P
  simp [Sinf.ordAt]

/-- The residue field `κ(P) := data.carrier ⧸ P` at a prime `P` of the
Sinf carrier. Curve-side: at a smooth point `P` of the underlying curve,
this matches the residue field `O_P / m_P` of the local ring. -/
abbrev Sinf.kappa {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f) :
    letI := data.commRing
    Ideal data.carrier → Type _ :=
  letI := data.commRing
  fun P => data.carrier ⧸ P

/-- Convenience: the natural `Algebra k data.carrier` obtained by
composing `algebraMap k (Polynomial k)` with `algebraMap (Polynomial k)
data.carrier`. Not a global instance — installed at use sites via
`letI` to avoid disturbing inference elsewhere. -/
@[reducible]
noncomputable def Sinf.algBaseFromCarrier
    {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.algPoly
    Algebra k data.carrier :=
  letI := data.commRing
  letI := data.algPoly
  ((algebraMap (Polynomial k) data.carrier).comp
    (algebraMap k (Polynomial k))).toAlgebra

/-- **Bridge 3 (statement form).** Inertia degree at `P` over `(X)` equals
the residue-field degree, formulated over the residue ring `Polynomial k ⧸
xIdeal`. The further conversion to `[κ(P) : k]` is provided as
`finrank_kappa_eq_finrank_residue_k` below (uses `quotientXAlgEquiv`). -/
theorem Sinf.inertiaDeg_eq_finrank_kappa
    {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.algPoly
    ∀ (P : Ideal data.carrier) [P.LiesOver (xIdeal (k := k))],
      Ideal.inertiaDeg (xIdeal (k := k)) P =
        Module.finrank (Polynomial k ⧸ xIdeal (k := k)) (data.kappa P) := by
  letI := data.commRing
  letI := data.algPoly
  intro P _
  exact Ideal.inertiaDeg_algebraMap _ _

/-- The `Polynomial k ⧸ xIdeal`-finrank of a module agrees with its
`k`-finrank, given a compatible scalar tower `k → (Polynomial k ⧸ xIdeal)
→ M`. Uses `quotientXAlgEquiv` plus the tower formula. -/
theorem finrank_residue_eq_finrank_k
    {M : Type*} [AddCommGroup M] [Module (Polynomial k ⧸ xIdeal (k := k)) M]
    [Module k M] [IsScalarTower k (Polynomial k ⧸ xIdeal (k := k)) M]
    [Module.Free (Polynomial k ⧸ xIdeal (k := k)) M] :
    Module.finrank (Polynomial k ⧸ xIdeal (k := k)) M = Module.finrank k M := by
  rw [← Module.finrank_mul_finrank k (Polynomial k ⧸ xIdeal (k := k)) M]
  have h1 : Module.finrank k (Polynomial k ⧸ xIdeal (k := k)) = 1 := by
    rw [(quotientXAlgEquiv (k := k)).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  rw [h1, one_mul]

/-- **Abstract inertia-degree-one criterion at `(X)`.** For an *arbitrary* prime `P` of the
`Sinf` carrier lying over `xIdeal := (X)`, if the structure algebra map
`(Polynomial k ⧸ (X)) → (carrier ⧸ P)` (`≅ k → κ(P)`) is surjective, then the inertia
degree `inertiaDeg (X) P` equals `1`. This is the field-agnostic, `CoordinateRing`-free,
`IsAlgClosed`-free criterion for any prime over `(X)`. -/
theorem Sinf.inertiaDeg_eq_one_of_algebraMap_surjective
    {L : Type*} [Field L] [Algebra k L] {f : L}
    (data : Sinf (k := k) f)
    (P : letI := data.commRing; Ideal data.carrier)
    [letI := data.commRing; P.IsPrime]
    [letI := data.commRing; letI := data.algPoly; P.LiesOver (xIdeal (k := k))]
    (h_surj : letI := data.commRing; letI := data.algPoly;
      letI : Algebra (Polynomial k ⧸ xIdeal (k := k)) (data.carrier ⧸ P) :=
        Ideal.Quotient.algebraQuotientOfLEComap
          (Ideal.LiesOver.over (p := xIdeal (k := k)) (P := P)).le
      Function.Surjective
        (algebraMap (Polynomial k ⧸ xIdeal (k := k)) (data.carrier ⧸ P))) :
    letI := data.commRing
    letI := data.algPoly
    Ideal.inertiaDeg (xIdeal (k := k)) P = 1 := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.isDomain
  letI := data.moduleFinite
  haveI hmax : (xIdeal (k := k)).IsMaximal := xIdeal_isMaximal
  letI : Algebra (Polynomial k ⧸ xIdeal (k := k)) (data.carrier ⧸ P) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (Ideal.LiesOver.over (p := xIdeal (k := k)) (P := P)).le
  rw [Ideal.inertiaDeg_algebraMap]
  refine le_antisymm ?_ ?_
  · refine finrank_le_one (1 : data.carrier ⧸ P) fun w => ?_
    obtain ⟨c, hc⟩ := h_surj w
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one] at hc; exact hc⟩
  · have hpos := Ideal.inertiaDeg_pos (xIdeal (k := k)) P
    rwa [Ideal.inertiaDeg_algebraMap] at hpos

/-- **Closing corollary (abstract form).** The function-field degree
`[L : k(f)]` over the Sinf data equals the weighted pole-divisor degree
`Σ_P (−ord_P f) · f_P` (with `f_P = inertiaDeg xIdeal P`). This is the
abstract form of the `[K(C) : k(f)] = Σ_{P pole of f} (−ord_P f) · [κ(P) :
k]` identity; Worker B's PoleDivisorFallback specialisation substitutes
`L = K(E)`, `f = γ*x_gen`, and converts `inertiaDeg` to `[κ(P) : k]`
using `inertiaDeg_eq_finrank_kappa` plus the `quotientXAlgEquiv`
`Polynomial k ⧸ xIdeal ≃ k`. -/
theorem finrank_eq_weighted_poleDegree_of_nonconstant
    {L : Type*} [Field L] [Algebra k L] (f : L) [Fact (Transcendental k f⁻¹)]
    [Module.Finite (FractionRing (Polynomial k)) (LinfAt (k := k) f)]
    (data : Sinf (k := k) f) :
    letI := data.commRing
    letI := data.isDedekindDomain
    letI := data.algPoly
    Module.finrank (FractionRing (Polynomial k)) (LinfAt (k := k) f) =
    ∑ P ∈ primesOverFinset (xIdeal (k := k)) data.carrier,
      (-(data.ordAt P)).toNat *
        Ideal.inertiaDeg (xIdeal (k := k)) P := by
  letI := data.commRing
  letI := data.algPoly
  letI := data.isDomain
  letI := data.isDedekindDomain
  letI := data.algLinfAt
  letI := data.isFractionRing
  letI := data.isScalarTower
  letI := data.moduleFinite
  letI := data.isTorsionFree
  have h := finrank_eq_sum_ramificationIdx_mul_inertiaDeg
    (k := k) (L := L) f data
  rw [← h]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [data.toNat_neg_ordAt_eq_ramificationIdx]

end RamificationAtInfinity

end HasseWeil.Curves
