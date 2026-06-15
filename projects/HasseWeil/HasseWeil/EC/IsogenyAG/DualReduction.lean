/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.MulByIntPullbackComp

/-!
# The dual witness through the Frobenius factorization (Silverman II.2.12 + III.6.1)

This file ships the **capstone reduction** for the dual-isogeny story over a finite field
`K = 𝔽_q` (`q = #K`): the faithful dual witness for an arbitrary isogeny `φ : E → E` is
reduced to the witness for its **separable part**, via the Frobenius factorization
`φ = φ_sep ∘ πʳ` of Silverman II.2.12.

## The three layers

1. **The factorization** (II.2.12, `q`-power case). The iterated `q`-power Frobenius
   `πʳ = Isogeny.frobeniusPower W r` has pullback `f ↦ f^(qʳ)`, so its pullback image is the
   subfield `K(E)^(qʳ)` of `qʳ`-th powers. Given the *inseparability data*
   `hincl : Im(φ*) ⊆ Im((πʳ)*)` — the iterate of the project's `q`-th-root formulation
   (`qth_root_witness_general`, `Verschiebung/QthRootRouteB.lean`); the element-wise form is
   interchangeable via `mem_frobeniusPower_pullback_range_iff` — the algebraic factoring
   `CurveMap.factorThrough` produces the **separable part** `φ_sep = Isogeny.separablePart`
   as an `EC.Isogeny` (basepoint discharged by the unconditional
   `Isogeny.reflects_ordAtInfty`), with `φ = φ_sep.compose (πʳ)`
   (`Isogeny.separablePart_compose`) and `deg φ = qʳ · deg φ_sep`.

2. **The induction** (Silverman III.6.1 Case 2, iterated): `πʳ` carries the faithful
   `[qʳ]`-dual witness `frobeniusPowerMulByIntDualWitness`, by induction on `r` from the
   Frobenius witness (`frobeniusMulByIntDualWitness`) and the faithful witness composition
   (`HasMulByIntDualWitness.compose`), with the `[q]·[qʳ] = [q^(r+1)]` bookkeeping handled
   by the index transport `HasMulByIntDualWitness.congrInt`. Its dual is the **iterated
   Verschiebung** `dualFrobeniusPower`, with `Vᵣ ∘ πʳ = [qʳ]`
   (`frobeniusPower_mulByIntDual_compose`).

3. **The reduction** (the capstone): a faithful `[n]`-witness for `φ_sep` yields the faithful
   `[qʳ·n]`-witness for `φ` (`Isogeny.mulByIntDualWitness_of_separablePart`); at
   `n = deg φ_sep` this is the faithful `[deg φ]`-witness
   (`Isogeny.mulByIntDualWitness_degree_of_separablePart`). **No covariance hypothesis is
   carried**: the composition needs the `[n]`-pullback covariance of the *inner* factor
   `πʳ` only, and that is a theorem (`frobeniusPower_mulByIntPullbackCovariant`).
   Corollaries: `exists_dual` for every such `φ`, the conjugation-form reduction
   `hasDualWitness_of_separablePart`, and the universal capstone
   `nonempty_hasDualWitness_of_frobeniusFactorization`.

## Honest scope: what is *not* proved here

* **Existence of the inseparability data** (Silverman II.2.12 proper): that every
  `φ : E → E` over `𝔽_q` with `deg_i φ = qʳ` satisfies `Im(φ*) ⊆ Im((πʳ)*)`. This is the
  uniqueness of the purely inseparable subextension `K(E)^(qʳ)` of its degree
  (Silverman II.2.11: `π* K(E) = K(E)^q`), not yet formalized. It is **named** as
  `FrobeniusFactorization` and carried as a hypothesis by the capstone.
* **Separability of `Isogeny.separablePart`**: the project's `IsSeparable` is
  `deg / deg_s = 1`; transporting it through the tower
  `Im(φ*) ⊆ Im((πʳ)*) ⊆ K(E)` needs the EC-level finite-dimensionality of `K(E)/Im(φ*)`
  (only the *Basic*-level `isogeny_finiteDimensional` / `isogeny_degree_pos` exist, in
  `Curves/Differentials.lean`) plus `Field.finSepDegree` transport along the Frobenius
  equivalence. It is recorded inside the `FrobeniusFactorization` predicate.
* **The general `p^k` twist gap**: for `deg_i φ = p^k` with `q = p^a` and `a ∤ k` (e.g.
  `[p]` over `𝔽_{p²}`, `mulByInt_p_inseparableDegree_eq_pow`), the II.2.12 factorization
  passes through the **Frobenius twist** `E^(p^k) ≠ E`, since only `q`-power Frobenii are
  same-curve over `𝔽_q` (coefficients are `q`-power-fixed). The project has the twist only
  in trivialized forms (`frobeniusTwist_eq_self_of_prime_field`, `Curves/QuotientCurve.lean`;
  `frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`, `IsogenyBaseChange.lean`) — there
  is **no cross-curve `p`-power Frobenius `EC.Isogeny E → E^(p)`**, so the general case is
  out of reach of this file's same-curve `frobeniusPower` and is *named, not built*.

## Main definitions and results

* `EC.Isogeny.frobeniusPower` — `πʳ` as an `EC.Isogeny`, with pullback `f ↦ f^(qʳ)` and
  degree `qʳ`.
* `EC.Isogeny.MulByIntPullbackCovariant.compose` / `id_mulByIntPullbackCovariant` /
  `frobeniusPower_mulByIntPullbackCovariant` — closure of the covariance under composition.
* `EC.idMulByIntDualWitness` — the faithful `[n]`-witness for the identity (any `n ≠ 0`,
  field-general).
* `EC.frobeniusPowerMulByIntDualWitness` — **deliverable 2**: the faithful `[qʳ]`-witness
  for `πʳ`.
* `EC.dualFrobeniusPower` — the iterated Verschiebung `Vᵣ`, with `Vᵣ ∘ πʳ = [qʳ]`.
* `EC.Isogeny.separablePart` — **deliverable 1**: the separable part of `φ` from the
  inseparability data, with `φ = φ_sep ∘ πʳ` and `deg φ = qʳ · deg φ_sep`.
* `EC.Isogeny.mulByIntDualWitness_of_separablePart` — **deliverable 3**: the faithful
  `[qʳ·n]`-witness for `φ` from the `[n]`-witness of its separable part;
  `_degree_of_separablePart` for the `[deg φ]` form; `exists_dual_of_separablePart_witness`.
* `EC.nonempty_hasDualWitness_of_frobeniusFactorization` — the universal capstone:
  {II.2.12 data} + {separable-side witnesses} ⟹ every isogeny carries a dual witness.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.11–2.12 (the Frobenius
  factorization), III.6.1 (the dual isogeny).
-/

open WeierstrassCurve

namespace HasseWeil.EC

open Curves

/-! ### The iterated Frobenius `πʳ` (Silverman II.2.12's inseparable leg) -/

section FrobeniusPower

variable {K : Type*} [Field K] [Fintype K]

/-- **The iterated `q`-power Frobenius** `πʳ : E → E` (`q = #K`), as an `EC.Isogeny`:
`π⁰ = id`, `π^(r+1) = πʳ ∘ π`. Its pullback is `f ↦ f^(qʳ)`
(`frobeniusPower_pullback`) and its degree is `qʳ` (`frobeniusPower_degree`). -/
noncomputable def Isogeny.frobeniusPower (W : Affine K) [W.IsElliptic] : ℕ → Isogeny W W
  | 0 => Isogeny.id W
  | r + 1 => (Isogeny.frobeniusPower W r).compose (Isogeny.frobenius W)

variable (W : Affine K) [W.IsElliptic]

@[simp] theorem Isogeny.frobeniusPower_zero :
    Isogeny.frobeniusPower W 0 = Isogeny.id W := rfl

theorem Isogeny.frobeniusPower_succ (r : ℕ) :
    Isogeny.frobeniusPower W (r + 1) =
      (Isogeny.frobeniusPower W r).compose (Isogeny.frobenius W) := rfl

/-- `π¹ = π`: the one-fold iterate is the Frobenius itself. -/
@[simp] theorem Isogeny.frobeniusPower_one :
    Isogeny.frobeniusPower W 1 = Isogeny.frobenius W :=
  Isogeny.ext_toCurveMap (CurveMap.id_comp _)

/-- **The pullback of `πʳ` is `f ↦ f^(qʳ)`** — the iterate of
`Isogeny.frobenius_pullback`. The image `Im((πʳ)*)` is therefore the subfield
`K(E)^(qʳ)` of `qʳ`-th powers (Silverman II.2.11, iterated). -/
@[simp] theorem Isogeny.frobeniusPower_pullback (r : ℕ) (f : W.FunctionField) :
    (Isogeny.frobeniusPower W r).toCurveMap.pullback f = f ^ Fintype.card K ^ r := by
  classical
  induction r with
  | zero =>
    change f = f ^ Fintype.card K ^ 0
    rw [pow_zero, pow_one]
  | succ r ih =>
    change (Isogeny.frobenius W).toCurveMap.pullback
        ((Isogeny.frobeniusPower W r).toCurveMap.pullback f) = f ^ Fintype.card K ^ (r + 1)
    rw [Isogeny.frobenius_pullback, ih, ← pow_mul, ← pow_succ]

/-- **`deg πʳ = qʳ`** (Silverman II.2.11(c), iterated): from `deg π = q`
(`frobenius_degree`) and degree multiplicativity (`compose_degree`). -/
@[simp] theorem Isogeny.frobeniusPower_degree (r : ℕ) :
    (Isogeny.frobeniusPower W r).degree = Fintype.card K ^ r := by
  classical
  induction r with
  | zero =>
    rw [pow_zero]
    exact Isogeny.id_degree W
  | succ r ih =>
    change ((Isogeny.frobeniusPower W r).compose (Isogeny.frobenius W)).degree = _
    rw [Isogeny.compose_degree, Isogeny.frobenius_degree, ih, ← pow_succ']

/-- **Membership in `Im((πʳ)*)` is having a `qʳ`-th root** — the bridge between the
range-inclusion form of the inseparability data and the project's element-wise `q`-th-root
formulation (`qth_root_witness_general`, iterated). -/
theorem Isogeny.mem_frobeniusPower_pullback_range_iff (r : ℕ) {z : W.FunctionField} :
    z ∈ (Isogeny.frobeniusPower W r).toCurveMap.pullback.range ↔
      ∃ g : W.FunctionField, g ^ Fintype.card K ^ r = z := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, (Isogeny.frobeniusPower_pullback W r g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, Isogeny.frobeniusPower_pullback W r g⟩

end FrobeniusPower

/-! ### Closure of the `[n]`-pullback covariance (Silverman III.4.8, composite shadow)

`MulByIntPullbackCovariant` is proved outright for `π` and `[m]`
(`MulByIntPullbackComp.lean`); here we close it under identity and composition, so that it
becomes a *theorem* for `πʳ` — the key to a hypothesis-free reduction below. -/

section CovarianceClosure

variable {F : Type*} [Field F]

/-- The identity isogeny satisfies the `[n]`-pullback covariance: both sides are `[n]*`. -/
theorem Isogeny.id_mulByIntPullbackCovariant (W : Affine F) [W.IsElliptic] (n : ℤ)
    (hn : n ≠ 0) : (Isogeny.id W).MulByIntPullbackCovariant n hn :=
  fun _ => rfl

/-- **The `[n]`-pullback covariance composes**: if `ψ` and `φ` are covariant against `[n]`,
so is `ψ ∘ φ` — `[n]*((ψ∘φ)* u) = [n]*(φ*(ψ* u)) = φ*([n]*(ψ* u)) = φ*(ψ*([n]* u))`. -/
theorem Isogeny.MulByIntPullbackCovariant.compose
    {W₁ W₂ W₃ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (hψ : ψ.MulByIntPullbackCovariant n hn) (hφ : φ.MulByIntPullbackCovariant n hn) :
    (ψ.compose φ).MulByIntPullbackCovariant n hn := by
  intro u
  change HasseWeil.mulByInt_pullbackAlgHom W₁ n hn
      (φ.toCurveMap.pullback (ψ.toCurveMap.pullback u)) =
    φ.toCurveMap.pullback (ψ.toCurveMap.pullback (HasseWeil.mulByInt_pullbackAlgHom W₃ n hn u))
  rw [hφ (ψ.toCurveMap.pullback u), hψ u]

end CovarianceClosure

section FrobeniusPowerCovariance

variable {K : Type*} [Field K] [Fintype K]

/-- **`πʳ` satisfies the `[n]`-pullback covariance, unconditionally** (Silverman III.4.8 for
the iterated Frobenius): by induction from the identity and Frobenius instances under
composition. This is why the capstone reduction below carries *no* covariance hypothesis. -/
theorem Isogeny.frobeniusPower_mulByIntPullbackCovariant (W : Affine K) [W.IsElliptic]
    (r : ℕ) (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.frobeniusPower W r).MulByIntPullbackCovariant n hn := by
  induction r with
  | zero => exact Isogeny.id_mulByIntPullbackCovariant W n hn
  | succ r ih => exact ih.compose (Isogeny.frobenius_mulByIntPullbackCovariant W n hn)

end FrobeniusPowerCovariance

/-! ### Witness transports and the identity witness -/

section WitnessTransport

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- Transport a faithful `[n]`-witness along an equality of the integer index (the
`[q]·[qʳ] = [q^(r+1)]` ν-bookkeeping; the nonvanishing proofs ride along by proof
irrelevance). -/
theorem Isogeny.HasMulByIntDualWitness.congrInt {φ : Isogeny W₁ W₂} {n n' : ℤ}
    {hn : n ≠ 0} {hn' : n' ≠ 0} (h : n = n') (w : φ.HasMulByIntDualWitness n hn) :
    φ.HasMulByIntDualWitness n' hn' := h ▸ w

/-- Transport a faithful `[n]`-witness along an equality of isogenies (used to carry the
composite witness across the factorization identity `φ_sep ∘ πʳ = φ`). -/
theorem Isogeny.HasMulByIntDualWitness.congrIsog {φ φ' : Isogeny W₁ W₂} {n : ℤ}
    {hn : n ≠ 0} (h : φ = φ') (w : φ.HasMulByIntDualWitness n hn) :
    φ'.HasMulByIntDualWitness n hn := h ▸ w

/-- Transport a generic dual witness along an equality of isogenies. -/
noncomputable def Isogeny.HasDualWitness.congrIsog {φ φ' : Isogeny W₁ W₂}
    (h : φ = φ') (w : φ.HasDualWitness) : φ'.HasDualWitness := h ▸ w

end WitnessTransport

section IdWitness

variable {F : Type*} [Field F]

/-- **The faithful `[n]`-dual witness for the identity isogeny** (any `n ≠ 0`,
field-general) — the base case of the `πʳ` induction. The range inclusion is trivial
(`Im(id*) = K(E)`), and the basepoint condition follows from the `[n]`-basepoint theorem and
`∞`-regularity reflection. -/
theorem idMulByIntDualWitness (W : Affine F) [W.IsElliptic] (n : ℤ) (hn : n ≠ 0) :
    (Isogeny.id W).HasMulByIntDualWitness n hn :=
  ⟨fun z _ => ⟨z, rfl⟩,
    Isogeny.hbase_of_reflects (Isogeny.id W) (HasseWeil.mulByInt_pullbackAlgHom W n hn)
      (fun z _ => ⟨z, rfl⟩) (mulByIntBasepoint_holds W hn)
      (Isogeny.reflects_ordAtInfty (Isogeny.id W))⟩

end IdWitness

/-! ### Deliverable 2 — the faithful `[qʳ]`-witness for `πʳ` (III.6.1 Case 2, iterated) -/

section FrobeniusPowerWitness

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

-- `[DecidableEq K]` enters through the Frobenius `[q]`-witness
-- (`frobeniusMulByIntDualWitness`), used in the proof; the linter only inspects the type.
set_option linter.unusedDecidableInType false in
/-- **The faithful `[qʳ]`-dual witness for the iterated Frobenius `πʳ`** (Silverman III.6.1
Case 2, iterated) — every field a theorem. Induction on `r`: the base case is the identity
witness, the step composes the inductive witness with the Frobenius `[q]`-witness
(`frobeniusMulByIntDualWitness`) along the Frobenius covariance, and transports
`q·qʳ = q^(r+1)` by `congrInt`. -/
theorem frobeniusPowerMulByIntDualWitness (r : ℕ) :
    (Isogeny.frobeniusPower W r).HasMulByIntDualWitness
      (((Fintype.card K : ℕ) : ℤ) ^ r) (pow_ne_zero r intCardK_ne_zero) := by
  induction r with
  | zero => exact idMulByIntDualWitness W _ _
  | succ r ih =>
    exact (ih.compose (frobeniusMulByIntDualWitness W)
        (Isogeny.frobenius_mulByIntPullbackCovariant W _
          (pow_ne_zero r intCardK_ne_zero))).congrInt
      (pow_succ' _ r).symm

set_option linter.unusedDecidableInType false in
/-- **`HasDualWitness` for `πʳ`**: the iterated Frobenius admits a dual witness with every
field a theorem. -/
noncomputable def hasDualWitness_frobeniusPower (r : ℕ) :
    (Isogeny.frobeniusPower W r).HasDualWitness :=
  (frobeniusPowerMulByIntDualWitness W r).toHasDualWitness

set_option linter.unusedDecidableInType false in
/-- **The iterated Verschiebung** `Vᵣ = (πʳ)^ : E → E` — the dual of `πʳ` built from the
fully-discharged faithful `[qʳ]`-witness. Satisfies `Vᵣ ∘ πʳ = [qʳ]`
(`frobeniusPower_mulByIntDual_compose`). -/
noncomputable def dualFrobeniusPower (r : ℕ) : Isogeny W W :=
  Isogeny.mulByIntDual (frobeniusPowerMulByIntDualWitness W r)

-- `[DecidableEq K]` is genuinely required: the statement names `dualFrobeniusPower`
-- (which carries it through the Frobenius witness), in a position the linter cannot see.
set_option linter.unusedDecidableInType false in
/-- **`Vᵣ ∘ πʳ = [qʳ]` as `EC.Isogeny`s** (Silverman III.6.1 defining identity, iterated):
the composite of the iterated Verschiebung with `πʳ` *is* multiplication by `qʳ`. -/
theorem frobeniusPower_mulByIntDual_compose (r : ℕ) :
    (dualFrobeniusPower W r).compose (Isogeny.frobeniusPower W r) =
      Isogeny.mulByInt W (pow_ne_zero r (intCardK_ne_zero (K := K))) :=
  Isogeny.mulByIntDual_compose _

-- `[Fintype K]`/`[DecidableEq K]` are genuinely required: the inhabitant is the iterated
-- Verschiebung, but the linter only inspects the type `Nonempty (Isogeny W W)`.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- **`exists_dual` for `πʳ`**: the iterated Frobenius admits a reverse isogeny. -/
theorem exists_dual_frobeniusPower (r : ℕ) : Nonempty (Isogeny W W) :=
  (Isogeny.frobeniusPower W r).exists_dual_of_witness (hasDualWitness_frobeniusPower W r)

end FrobeniusPowerWitness

/-! ### Deliverable 1 — the separable part from the inseparability data (II.2.12) -/

section Factorization

variable {K : Type*} [Field K] [Fintype K]
variable {W : Affine K} [W.IsElliptic]

/-- **The separable part `φ_sep` of `φ` through `πʳ`** (Silverman II.2.12, `q`-power case):
given the inseparability data `hincl : Im(φ*) ⊆ Im((πʳ)*)` (every `φ*`-pullback is a
`qʳ`-th power, cf. `mem_frobeniusPower_pullback_range_iff`), the algebraic factoring
`CurveMap.factorThrough` produces the curve map with `φ* = (πʳ)* ∘ φ_sep*`, and the
basepoint condition is *derived*: `φ` preserves `∞`-regularity and `πʳ` reflects it
(`Isogeny.reflects_ordAtInfty`, unconditional), so `φ_sep` preserves it.

The name records the intended mathematics. The separability of `φ_sep` (when
`deg_i φ = qʳ` exactly) is *not* proved here: the project's `IsSeparable` transport through
the tower `Im(φ*) ⊆ Im((πʳ)*) ⊆ K(E)` needs EC-level finite-dimensionality of
`K(E)/Im(φ*)` (only the Basic-level `isogeny_finiteDimensional` exists) — see the module
docstring and `FrobeniusFactorization`. -/
noncomputable def Isogeny.separablePart (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range) :
    Isogeny W W where
  toCurveMap :=
    CurveMap.factorThrough (Isogeny.frobeniusPower W r).toCurveMap φ.toCurveMap hincl
  pullback_ordAtInfty_nonneg f hf := by
    refine Isogeny.reflects_ordAtInfty (Isogeny.frobeniusPower W r) _ ?_
    rw [show (Isogeny.frobeniusPower W r).toCurveMap.pullback
          ((CurveMap.factorThrough (Isogeny.frobeniusPower W r).toCurveMap
            φ.toCurveMap hincl).pullback f) = φ.toCurveMap.pullback f from
      CurveMap.factorThroughPullback_spec _ _ hincl f]
    exact φ.pullback_ordAtInfty_nonneg f hf

/-- **The pullback-level factorization** `(πʳ)* (φ_sep* z) = φ* z` — the function-field
shadow of `φ = φ_sep ∘ πʳ` (Silverman II.2.12). -/
theorem Isogeny.frobeniusPower_pullback_separablePart_pullback (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    (z : W.FunctionField) :
    (Isogeny.frobeniusPower W r).toCurveMap.pullback
        ((φ.separablePart r hincl).toCurveMap.pullback z) =
      φ.toCurveMap.pullback z :=
  CurveMap.factorThroughPullback_spec _ _ hincl z

/-- **The factorization in `qʳ`-th-power form**: `(φ_sep* z)^(qʳ) = φ* z`. -/
theorem Isogeny.separablePart_pullback_pow (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    (z : W.FunctionField) :
    (φ.separablePart r hincl).toCurveMap.pullback z ^ Fintype.card K ^ r =
      φ.toCurveMap.pullback z := by
  rw [← Isogeny.frobeniusPower_pullback W r]
  exact φ.frobeniusPower_pullback_separablePart_pullback r hincl z

/-- **The Frobenius factorization as `EC.Isogeny`s** (Silverman II.2.12, `q`-power case):
`φ_sep ∘ πʳ = φ`. -/
theorem Isogeny.separablePart_compose (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range) :
    (φ.separablePart r hincl).compose (Isogeny.frobeniusPower W r) = φ :=
  Isogeny.ext_toCurveMap (CurveMap.factorThrough_comp _ _ hincl).symm

/-- **Degree bookkeeping of the factorization**: `deg φ = qʳ · deg φ_sep` (Silverman
II.2.12's `deg_i φ = qʳ` reading, via `compose_degree` and `deg πʳ = qʳ`). -/
theorem Isogeny.degree_eq_pow_mul_separablePart_degree (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range) :
    φ.degree = Fintype.card K ^ r * (φ.separablePart r hincl).degree := by
  conv_lhs => rw [← φ.separablePart_compose r hincl]
  rw [Isogeny.compose_degree, Isogeny.frobeniusPower_degree]

/-- The integer-cast degree bookkeeping `qʳ · deg φ_sep = deg φ` feeding the `[deg φ]`-form
of the reduction. -/
theorem Isogeny.pow_mul_separablePart_degree_intCast (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range) :
    ((Fintype.card K : ℕ) : ℤ) ^ r * ((φ.separablePart r hincl).degree : ℤ) =
      (φ.degree : ℤ) := by
  rw [φ.degree_eq_pow_mul_separablePart_degree r hincl]
  push_cast
  ring

/-- The element-wise (`qʳ`-th-root) form of the inseparability data yields the
range-inclusion form consumed by `Isogeny.separablePart` — the iterate of the project's
`qth_root_witness` formulation (`Verschiebung/PurelyInsep.lean`). -/
theorem Isogeny.rangeIncl_frobeniusPower_of_pow_roots (φ : Isogeny W W) (r : ℕ)
    (h : ∀ z : W.FunctionField,
      ∃ g : W.FunctionField, g ^ Fintype.card K ^ r = φ.toCurveMap.pullback z) :
    φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  exact (Isogeny.mem_frobeniusPower_pullback_range_iff W r).mpr (h w)

/-- Any pre-composed `ψ ∘ πʳ` carries the inseparability data by construction:
`(ψ ∘ πʳ)* z = (πʳ)*(ψ* z) ∈ Im((πʳ)*)`. -/
theorem Isogeny.rangeIncl_compose_frobeniusPower (ψ : Isogeny W W) (r : ℕ) :
    (ψ.compose (Isogeny.frobeniusPower W r)).toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range := by
  rintro z ⟨w, rfl⟩
  exact ⟨ψ.toCurveMap.pullback w, rfl⟩

/-- **The separable part of `πʳ` itself is the identity**: factoring `πʳ` through `πʳ`
recovers `id` (injectivity of the pullback). A sanity check that `separablePart` computes. -/
theorem Isogeny.separablePart_frobeniusPower_self (W : Affine K) [W.IsElliptic] (r : ℕ) :
    (Isogeny.frobeniusPower W r).separablePart r le_rfl = Isogeny.id W := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z => ?_))
  apply (Isogeny.frobeniusPower W r).pullback_injective
  rw [(Isogeny.frobeniusPower W r).frobeniusPower_pullback_separablePart_pullback r le_rfl z]
  rfl

end Factorization

/-! ### Deliverable 3 — the reduction: the dual witness for `φ` from its separable part's -/

section Reduction

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {W : Affine K} [W.IsElliptic]

-- `[DecidableEq K]` enters through the `[qʳ]`-witness for `πʳ` used in the proof; the
-- linter only inspects the type.
set_option linter.unusedDecidableInType false in
/-- **The capstone reduction** (Silverman III.6.1 via II.2.12): a faithful `[n]`-dual
witness for the separable part `φ_sep` yields the faithful `[qʳ·n]`-dual witness for `φ`
itself. The composition runs along `φ = φ_sep ∘ πʳ` with the `[qʳ]`-witness for `πʳ`
(`frobeniusPowerMulByIntDualWitness`); the required covariance is that of the *inner*
factor `πʳ` against `[n]`, which is a **theorem**
(`frobeniusPower_mulByIntPullbackCovariant`) — no covariance hypothesis is carried. -/
theorem Isogeny.mulByIntDualWitness_of_separablePart (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    {n : ℤ} {hn : n ≠ 0}
    (wsep : (φ.separablePart r hincl).HasMulByIntDualWitness n hn) :
    φ.HasMulByIntDualWitness (((Fintype.card K : ℕ) : ℤ) ^ r * n)
      (mul_ne_zero (pow_ne_zero r intCardK_ne_zero) hn) :=
  (wsep.compose (frobeniusPowerMulByIntDualWitness W r)
      (Isogeny.frobeniusPower_mulByIntPullbackCovariant W r n hn)).congrIsog
    (φ.separablePart_compose r hincl)

set_option linter.unusedDecidableInType false in
/-- **The faithful `[deg φ]`-witness from the separable part** (Silverman III.6.1's exact
bookkeeping): with `n = deg φ_sep`, the reduction produces the witness at
`qʳ · deg φ_sep = deg φ` (`compose_degree` order), i.e. the dual satisfies
`(φ̂ ∘ φ)* = [deg φ]*`. The degree-nonvanishing hypotheses are carried (EC-level degree
positivity is not yet available; cf. the Basic-level `isogeny_degree_pos`). -/
theorem Isogeny.mulByIntDualWitness_degree_of_separablePart (φ : Isogeny W W)
    (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    {hd : ((φ.separablePart r hincl).degree : ℤ) ≠ 0}
    (wsep : (φ.separablePart r hincl).HasMulByIntDualWitness
      ((φ.separablePart r hincl).degree : ℤ) hd)
    (hφd : (φ.degree : ℤ) ≠ 0) :
    φ.HasMulByIntDualWitness (φ.degree : ℤ) hφd :=
  (φ.mulByIntDualWitness_of_separablePart r hincl wsep).congrInt
    (φ.pow_mul_separablePart_degree_intCast r hincl)

set_option linter.unusedDecidableInType false in
/-- **`(φ̂ ∘ φ) = [qʳ·n]` in fully bundled form** for the reduced witness: the defining
identity of the dual produced by the capstone reduction. -/
theorem Isogeny.separablePart_mulByIntDual_compose (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    {n : ℤ} {hn : n ≠ 0}
    (wsep : (φ.separablePart r hincl).HasMulByIntDualWitness n hn) :
    (Isogeny.mulByIntDual (φ.mulByIntDualWitness_of_separablePart r hincl wsep)).compose φ =
      Isogeny.mulByInt W (mul_ne_zero (pow_ne_zero r (intCardK_ne_zero (K := K))) hn) :=
  Isogeny.mulByIntDual_compose _

set_option linter.unusedDecidableInType false in
/-- **`exists_dual` from the separable part's witness**: every isogeny equipped with the
II.2.12 inseparability data and a faithful witness for its separable part admits a reverse
isogeny. -/
theorem Isogeny.exists_dual_of_separablePart_witness (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    {n : ℤ} {hn : n ≠ 0}
    (wsep : (φ.separablePart r hincl).HasMulByIntDualWitness n hn) :
    Nonempty (Isogeny W W) :=
  φ.exists_dual_of_witness
    (φ.mulByIntDualWitness_of_separablePart r hincl wsep).toHasDualWitness

set_option linter.unusedDecidableInType false in
/-- **The conjugation-form reduction**: a *generic* dual witness for the separable part
yields one for `φ`, via `HasDualWitness.compose` (no integer bookkeeping, no covariance).
Pairs with the separable-side `DualGaloisData` capstones
(`EC/IsogenyAG/DualGaloisClosed.lean`), whose output is a `HasDualWitness`. -/
noncomputable def Isogeny.hasDualWitness_of_separablePart (φ : Isogeny W W) (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range)
    (wsep : (φ.separablePart r hincl).HasDualWitness) : φ.HasDualWitness :=
  (wsep.compose (hasDualWitness_frobeniusPower W r)).congrIsog
    (φ.separablePart_compose r hincl)

end Reduction

/-! ### Stress tests: composite witnesses through `πʳ` -/

section Stress

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

set_option linter.unusedDecidableInType false in
/-- **The faithful `[qʳ·ℓ²]`-witness for `[ℓ] ∘ πʳ`** — the `r`-fold generalization of
`mulByIntCompFrobeniusDualWitness`, stressing the `[qʳ]`-witness and the theorem-level
`πʳ` covariance. Every field a theorem. -/
theorem mulByIntCompFrobeniusPowerDualWitness (r : ℕ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ((Isogeny.mulByInt W hℓ).compose (Isogeny.frobeniusPower W r)).HasMulByIntDualWitness
      (((Fintype.card K : ℕ) : ℤ) ^ r * (ℓ * ℓ))
      (mul_ne_zero (pow_ne_zero r intCardK_ne_zero) (mul_ne_zero hℓ hℓ)) :=
  (mulByIntSelfDualWitness W hℓ).compose (frobeniusPowerMulByIntDualWitness W r)
    (Isogeny.frobeniusPower_mulByIntPullbackCovariant W r _ (mul_ne_zero hℓ hℓ))

set_option linter.unusedDecidableInType false in
/-- **The faithful `[ℓ²·qʳ]`-witness for `πʳ ∘ [ℓ]`** — the opposite composition order,
exercising the `[m]`-covariance leg. Every field a theorem. -/
theorem frobeniusPowerCompMulByIntDualWitness (r : ℕ) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    ((Isogeny.frobeniusPower W r).compose (Isogeny.mulByInt W hℓ)).HasMulByIntDualWitness
      (ℓ * ℓ * ((Fintype.card K : ℕ) : ℤ) ^ r)
      (mul_ne_zero (mul_ne_zero hℓ hℓ) (pow_ne_zero r intCardK_ne_zero)) :=
  (frobeniusPowerMulByIntDualWitness W r).compose (mulByIntSelfDualWitness W hℓ)
    (Isogeny.mulByInt_mulByIntPullbackCovariant W hℓ _ (pow_ne_zero r intCardK_ne_zero))

end Stress

/-! ### The named gaps (Silverman II.2.12 existence; the `p^k` twist)

Everything above is hypothesis-honest: the reduction machinery is unconditional, and the
only carried inputs are (i) the inseparability data `hincl` and (ii) the separable-side
witness. The two genuinely open inputs are *named* here, not built:

* **II.2.12 existence over `𝔽_q` (q-power case)** — `FrobeniusFactorization` below: every
  isogeny `φ : E → E` admits `r` with `Im(φ*) ⊆ Im((πʳ)*)` and `φ_sep` separable. Its
  mathematical content is Silverman II.2.11's `π*K(E) = K(E)^q` *plus* the uniqueness of
  the degree-`qʳ` purely inseparable subextension of `K(E)` (every element of a purely
  inseparable extension of exponent dividing `qʳ` has its `qʳ`-th power in the base). The
  project's `q`-th-root machinery (`qth_root_witness_general`) discharges exactly the
  `φ = [q]`, `r = 1` instance of the inclusion.

* **The general `p^k` twist gap**: over `K = 𝔽_q` with `q = pᵃ`, the same-curve
  factorization above is available precisely when `deg_i φ` is a power of `q` — the
  `q`-power Frobenius is an endomorphism of `E` because the Weierstrass coefficients are
  `q`-power-fixed. For `deg_i φ = p^k` with `a ∤ k` (e.g. `[p]` over `𝔽_{p²}`:
  `mulByInt_p_inseparableDegree_eq_pow` gives `deg_i [p]` a nontrivial `p`-power), Silverman
  II.2.12 factors through the **Frobenius twist** `E^(p^k) ≠ E`. The project has no
  cross-curve `p`-power Frobenius `EC.Isogeny E (E^(p^k))` — only the trivialized twists
  `frobeniusTwist_eq_self_of_prime_field` (`Curves/QuotientCurve.lean`, `K = 𝔽_p`) and
  `frobeniusTwistIterate_baseChange_eq_self_of_charP_pow` (`IsogenyBaseChange.lean`, after
  base change) — so the twisted factorization is out of scope for this file's same-curve
  `frobeniusPower` and is *named, not built*. -/

section UniversalCapstone

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **The Silverman II.2.12 existence problem over `𝔽_q`, `q`-power case** (named gap):
every isogeny `φ : E → E` admits an `r` and the inseparability data
`Im(φ*) ⊆ Im((πʳ)*)` such that the resulting separable part is separable in the project's
sense (`deg_i φ_sep = 1`). The intended `r` is `deg_i φ = qʳ` (possible exactly when
`deg_i φ` is a power of `q`; cf. the twist gap above for the general `p^k` case).

Not proved in the current development; carried as the hypothesis of
`nonempty_hasDualWitness_of_frobeniusFactorization`. -/
def FrobeniusFactorization (W : Affine K) [W.IsElliptic] : Prop :=
  ∀ φ : Isogeny W W, ∃ (r : ℕ)
    (hincl : φ.toCurveMap.pullback.range ≤
      (Isogeny.frobeniusPower W r).toCurveMap.pullback.range),
    (φ.separablePart r hincl).IsSeparable

-- `[DecidableEq K]` enters through the `[qʳ]`-witness for `πʳ` used in the proof; the
-- linter only inspects the type.
set_option linter.unusedDecidableInType false in
/-- **The universal capstone** (Silverman III.6.1 over `𝔽_q`, assembled): if every isogeny
factors through a power of Frobenius with separable quotient (`FrobeniusFactorization`,
the II.2.12 gap) and every *separable* isogeny carries a faithful dual witness (the
separable-side gap, cf. the `DualGaloisData` capstones in
`EC/IsogenyAG/DualGaloisClosed.lean`), then **every** isogeny carries a dual witness —
the `universal_dual_witness` shape of `EC/IsogenyAG/Dual.lean`, reduced over a finite
field to its two honest inputs. -/
theorem nonempty_hasDualWitness_of_frobeniusFactorization (W : Affine K) [W.IsElliptic]
    (hfact : FrobeniusFactorization W)
    (hsep : ∀ ψ : Isogeny W W, ψ.IsSeparable →
      ∃ (n : ℤ) (hn : n ≠ 0), ψ.HasMulByIntDualWitness n hn) :
    ∀ φ : Isogeny W W, Nonempty φ.HasDualWitness := by
  intro φ
  obtain ⟨r, hincl, hsep_part⟩ := hfact φ
  obtain ⟨n, hn, w⟩ := hsep _ hsep_part
  exact ⟨(φ.mulByIntDualWitness_of_separablePart r hincl w).toHasDualWitness⟩

end UniversalCapstone

end HasseWeil.EC
