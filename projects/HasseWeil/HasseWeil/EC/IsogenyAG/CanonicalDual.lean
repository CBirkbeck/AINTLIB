/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG.TwistedFactorization
import HasseWeil.EC.IsogenyAG.DualGaloisClosed

/-!
# The canonical dual isogeny (Silverman III.6.1–III.6.2)

This file canonicalizes the dual-isogeny story of `EC/IsogenyAG/Dual.lean`: uniqueness,
**both** compositions, `deg φ̂ = deg φ`, the double dual `φ̂̂ = φ`, the reversal of
composition `(ψ∘φ)^ = φ̂ ∘ ψ̂`, and the canonical packaging `Isogeny.canonicalDual` with its
`∃!`-form.

## The route (Silverman III.6.1–6.2, pp. 81–83, adapted)

* **Uniqueness is a pullback-level cancellation**, cheaper than Silverman's subtraction
  argument: `(ψ₁ ∘ φ)* = φ* ∘ ψ₁*` and `φ*` is injective (a field hom), so
  `ψ₁ ∘ φ = ψ₂ ∘ φ ⟹ ψ₁ = ψ₂` (`Isogeny.compose_right_cancel`). Any two reverse isogenies
  composing with `φ` to `[n]` are therefore equal — no witness data enters.
* **The second composition** `φ ∘ φ̂ = [n]` (III.6.2(a)) follows by cancelling `φ` on the
  right in `(φ ∘ φ̂) ∘ φ = φ ∘ (φ̂ ∘ φ) = φ ∘ [n] = [n] ∘ φ`. The middle step
  `φ ∘ [n] = [n] ∘ φ` (Silverman III.4.8) is, at the pullback level, exactly
  `Isogeny.MulByIntPullbackCovariant φ n` (`EC/IsogenyAG/MulByIntPullbackComp.lean`).
* **`deg φ̂ = deg φ`**: from `φ̂ ∘ φ = [n]`, degree multiplicativity gives
  `deg φ · deg φ̂ = deg [n] = n²`; with `deg φ = |n|` cancel in `ℕ`.
* **`φ̂̂ = φ`**: `φ̂̂ ∘ φ̂ = [n]` and `φ ∘ φ̂ = [n]` (the second composition), then uniqueness
  applied to `φ̂`.
* **`(ψ∘φ)^ = φ̂ ∘ ψ̂`** (III.6.2(b)): both compose with `ψ ∘ φ` to `[m·n]`
  (`HasMulByIntDualWitness.compose` builds the composite witness), then uniqueness.

## Honest scoping

* **The covariance hypothesis.** For an *abstract* `EC.Isogeny` the pullback covariance
  `[n]* ∘ φ* = φ* ∘ [n]*` is the project's open generic-point leaf (DUAL-2): the structure
  stores only the pullback, and III.4.8 is a theorem about the geometric morphism. The
  audit (2026-06-10) found **no class discharge** — the only consumers of
  `MulByIntPullbackCovariant` are `MulByIntPullbackComp.lean` and `DualReduction.lean`, and
  a derivation from the `PullbackEvaluation` engine would need a new
  values-determine-functions principle over cofinitely many places plus evaluation
  coherence for both `φ` and `[n]` (well beyond ~150 lines). It is therefore **carried as
  the one named hypothesis** of the second composition (and of everything downstream of
  it: the double dual, the reversal, the canonical second composition). It is a *theorem*
  for the concrete isogenies of the development: `π` (`frobenius_mulByIntPullbackCovariant`),
  `[m]` (`mulByInt_mulByIntPullbackCovariant`), `id`, compositions, and `πʳ`
  (`frobeniusPower_mulByIntPullbackCovariant`) — so every concrete instance below is
  hypothesis-free.
* **Levels.** Uniqueness, both compositions, degree, double dual and the canonical
  packaging are at the **two-curve** level `φ : E₁ → E₂` (the compositions
  `φ̂ ∘ φ : E₁ → E₁` and `φ ∘ φ̂ : E₂ → E₂` involve the multiplication isogenies of the two
  *different* curves, handled explicitly); the reversal is three-curve.
* **III.6.2(c) — additivity of the dual — is explicitly out of scope**: Silverman proves it
  in characteristic `0` only and punts arbitrary characteristic to Exercise 3.31.
* **The relative Frobenius double dual** is not instantiated: it would need the covariance
  of `Frob_{p^e} : E → E^{(p^e)}` against `[p^e]`, i.e. the compatibility of division
  polynomials with the coefficient twist — genuinely new work. Its uniqueness and degree
  corollaries (which need no covariance) are wired below.

## Main results

* `EC.Isogeny.compose_right_cancel` — pullback-injectivity cancellation (uniqueness core).
* `EC.Isogeny.compose_eq_mulByInt_unique` / `eq_mulByIntDual` — the uniqueness statements.
* `EC.Isogeny.compose_mulByIntDual` — **the second composition** `φ ∘ φ̂ = [n]` (III.6.2(a)).
* `EC.Isogeny.HasMulByIntDualWitness.dual` — the dual itself carries the `[n]`-witness.
* `EC.Isogeny.mulByInt_degree` (EC-level `deg [n] = n²`),
  `degree_mul_mulByIntDual_degree`, `mulByIntDual_degree` — **`deg φ̂ = deg φ`**.
* `EC.Isogeny.mulByIntDual_mulByIntDual` — **the double dual** `φ̂̂ = φ`.
* `EC.Isogeny.mulByIntDual_compose_reverse` — **`(ψ∘φ)^ = φ̂ ∘ ψ̂`** (III.6.2(b)).
* `EC.Isogeny.canonicalDual` + `eq_canonicalDual` + `existsUnique_dual` +
  `canonicalDual_degree` + `canonicalDual_canonicalDual` — the canonical packaging at
  `n = deg φ`.
* Concrete wiring: `frobenius_compose_dualFrobenius`, `dualFrobenius_degree` (`deg V = q`),
  `dualFrobenius_dual_eq_frobenius` (`V̂ = π`), the `πʳ` analogues, `[ℓ]^ = [ℓ]`
  (`mulByIntDual_mulByIntSelf`), `dualMulByInt_eq_mulByInt` (the Galois-built dual of `[ℓ]`
  *is* `[ℓ]`), and uniqueness + degree for the relative Verschiebung.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], III.6.1–III.6.2 (pp. 81–83), III.4.8.
-/

open WeierstrassCurve

namespace HasseWeil.EC

open Curves

/-! ### Cancellation: the uniqueness core (Silverman III.6.2, pullback form) -/

section Cancellation

variable {F : Type*} [Field F] {W₁ W₂ W₃ : Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- **Right-cancellation of composition** (the uniqueness core, Silverman III.6.2 made
pullback-level): if `ψ₁ ∘ φ = ψ₂ ∘ φ` then `ψ₁ = ψ₂`. The pullback of the composite is
`φ* ∘ ψᵢ*`, and `φ*` is injective (an `F`-algebra hom of fields), so the pullbacks of
`ψ₁, ψ₂` agree; conclude by pullback extensionality. Cheaper than Silverman's subtraction
argument — no group structure on isogenies is needed. -/
theorem Isogeny.compose_right_cancel {φ : Isogeny W₁ W₂} {ψ₁ ψ₂ : Isogeny W₂ W₃}
    (h : ψ₁.compose φ = ψ₂.compose φ) : ψ₁ = ψ₂ := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z ↦ ?_))
  exact φ.pullback_injective
    (congrArg (fun χ : Isogeny W₁ W₃ ↦ χ.toCurveMap.pullback z) h)

/-- **The defining identity of the generic dual, pullback form**: for any
`w : HasDualWitness φ`, `φ* ((φ.dual w)* z) = ν* z`. Instance of
`dualOfWitness_comp_pullback` at the witness fields. -/
theorem Isogeny.dual_comp_pullback {φ : Isogeny W₁ W₂} (w : φ.HasDualWitness)
    (z : (⟨W₁⟩ : SmoothPlaneCurve F).FunctionField) :
    φ.toCurveMap.pullback ((φ.dual w).toCurveMap.pullback z) = w.νPb z :=
  Isogeny.dualOfWitness_comp_pullback φ w.νPb w.hincl w.hbase z

end Cancellation

/-! ### The EC-level degree of `[n]` and the `[n]`-congruence -/

section MulByIntDegree

variable {F : Type*} [Field F]

/-- **`deg [n] = n²` at the `EC.Isogeny` level** (Silverman III.4.2): transported from the
Basic-level `HasseWeil.mulByInt_degree` along the pullback identification
`(mulByInt W n).pullback = mulByInt_pullbackAlgHom W n hn` (`dif_neg`); both degrees are
the same `finrank` once the pullbacks are identified. -/
theorem Isogeny.mulByInt_degree (W : Affine F) [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (Isogeny.mulByInt W hn).degree = (n ^ 2).toNat := by
  classical
  have hpb : (HasseWeil.mulByInt W n).pullback =
      HasseWeil.mulByInt_pullbackAlgHom W n hn := dif_neg hn
  have key : (Isogeny.mulByInt W hn).degree = (HasseWeil.mulByInt W n).degree :=
    (congrArg (fun α : W.FunctionField →ₐ[F] W.FunctionField ↦
      @Module.finrank W.FunctionField W.FunctionField _ _
        (RingHom.toAlgebra α.toRingHom).toModule) hpb).symm
  rw [key]
  exact HasseWeil.mulByInt_degree W n hn

/-- `Isogeny.mulByInt` is congruent in the integer index (the nonvanishing proofs ride
along by proof irrelevance). -/
theorem Isogeny.mulByInt_congr (W : Affine F) [W.IsElliptic] {a b : ℤ}
    {ha : a ≠ 0} {hb : b ≠ 0} (h : a = b) :
    Isogeny.mulByInt W ha = Isogeny.mulByInt W hb := by subst h; rfl

end MulByIntDegree

/-! ### Uniqueness of the dual (Silverman III.6.2, item 1) -/

section Uniqueness

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Uniqueness of the dual, witness-free pairwise form** (Silverman III.6.2): any two
reverse isogenies composing with `φ` to the *same* `[n]` are equal. Pure right-cancellation
— no dual witness enters. -/
theorem Isogeny.compose_eq_mulByInt_unique {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    {ψ₁ ψ₂ : Isogeny W₂ W₁} (h₁ : ψ₁.compose φ = Isogeny.mulByInt W₁ hn)
    (h₂ : ψ₂.compose φ = Isogeny.mulByInt W₁ hn) : ψ₁ = ψ₂ :=
  Isogeny.compose_right_cancel (h₁.trans h₂.symm)

/-- **All witnesses agree** (Silverman III.6.1/III.6.2 uniqueness): any reverse isogeny `ψ`
with `ψ ∘ φ = [n]` *is* the faithful dual `mulByIntDual w`, for any `[n]`-witness `w`. -/
theorem Isogeny.eq_mulByIntDual {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) {ψ : Isogeny W₂ W₁}
    (hψ : ψ.compose φ = Isogeny.mulByInt W₁ hn) : ψ = Isogeny.mulByIntDual w :=
  Isogeny.compose_eq_mulByInt_unique hψ (Isogeny.mulByIntDual_compose w)

end Uniqueness

/-! ### The second composition `φ ∘ φ̂ = [n]` (Silverman III.6.2(a), item 2)

The middle step `φ ∘ [n] = [n] ∘ φ` is the carried covariance `MulByIntPullbackCovariant`
(a theorem for `π`, `[m]`, `id`, compositions and `πʳ`; the open DUAL-2 leaf for an
abstract isogeny — see the module docstring for the audit verdict). -/

section SecondComposition

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **`φ ∘ [n] = [n] ∘ φ` in fully bundled form** (Silverman III.4.8): the bundled shadow
of the pullback covariance. Note the two `[n]`'s live on the two different curves. -/
theorem Isogeny.compose_mulByInt_of_covariant {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (hcov : φ.MulByIntPullbackCovariant n hn) :
    φ.compose (Isogeny.mulByInt W₁ hn) = (Isogeny.mulByInt W₂ hn).compose φ :=
  Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z ↦ hcov z))

/-- **The second composition** `φ ∘ φ̂ = [n]` (Silverman III.6.2(a)): cancel `φ` on the
right in `(φ ∘ φ̂) ∘ φ = φ ∘ (φ̂ ∘ φ) = φ ∘ [n] = [n] ∘ φ`. The covariance `hcov` is the one
named hypothesis (a theorem for the concrete isogenies of the development). Note `[n]` here
is the multiplication isogeny of the *target* curve `E₂`. -/
theorem Isogeny.compose_mulByIntDual {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) (hcov : φ.MulByIntPullbackCovariant n hn) :
    φ.compose (Isogeny.mulByIntDual w) = Isogeny.mulByInt W₂ hn := by
  refine Isogeny.compose_right_cancel (φ := φ) ?_
  rw [Isogeny.compose_assoc, Isogeny.mulByIntDual_compose w,
    Isogeny.compose_mulByInt_of_covariant hcov]

set_option maxHeartbeats 800000 in
-- unifying the dual's pullback applications (which unfold through `dualPullback` =
-- `factorThroughPullback` = `AlgEquiv.ofInjective.symm ∘ codRestrict`) against the
-- range-membership target is `whnf`-heavy, as in `composeNuPb_rangeIncl`
/-- **The dual carries the `[n]`-witness itself** (Silverman III.6.2 bookkeeping): from the
second composition, `[n]₂* = φ̂* ∘ φ*`, so `Im([n]₂*) ⊆ Im(φ̂*)`; the basepoint condition is
assembled from the `[n]`-basepoint theorem and `∞`-regularity reflection. This is the
witness through which the double dual is taken. -/
theorem Isogeny.HasMulByIntDualWitness.dual {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) (hcov : φ.MulByIntPullbackCovariant n hn) :
    (Isogeny.mulByIntDual w).HasMulByIntDualWitness n hn := by
  have hincl : (HasseWeil.mulByInt_pullbackAlgHom W₂ n hn).range ≤
      (Isogeny.mulByIntDual w).toCurveMap.pullback.range := by
    rintro z ⟨u, rfl⟩
    exact ⟨φ.toCurveMap.pullback u,
      congrArg (fun χ : Isogeny W₂ W₂ ↦ χ.toCurveMap.pullback u)
        (Isogeny.compose_mulByIntDual w hcov)⟩
  exact ⟨hincl, Isogeny.hbase_of_reflects (Isogeny.mulByIntDual w)
    (HasseWeil.mulByInt_pullbackAlgHom W₂ n hn) hincl
    (mulByIntBasepoint_holds W₂ hn)
    (Isogeny.reflects_ordAtInfty (Isogeny.mulByIntDual w))⟩

end SecondComposition

/-! ### The degree of the dual (Silverman III.6.2(d) form, item 3) -/

section DualDegree

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Degree bookkeeping of the dual**: `deg φ · deg φ̂ = n²`, from `φ̂ ∘ φ = [n]`, degree
multiplicativity and `deg [n] = n²`. No hypotheses beyond the witness. -/
theorem Isogeny.degree_mul_mulByIntDual_degree {φ : Isogeny W₁ W₂} {n : ℤ}
    {hn : n ≠ 0} (w : φ.HasMulByIntDualWitness n hn) :
    φ.degree * (Isogeny.mulByIntDual w).degree = (n ^ 2).toNat := by
  rw [← Isogeny.compose_degree (Isogeny.mulByIntDual w) φ,
    Isogeny.mulByIntDual_compose w, Isogeny.mulByInt_degree W₁ hn]

/-- **`deg φ̂ = deg φ`** (Silverman III.6.2(d) at the faithful index): when `deg φ = |n|`
(Silverman's case is `n = deg φ`), the dual has the same degree — cancel `deg φ` in
`deg φ · deg φ̂ = n² = |n|·|n|`. -/
theorem Isogeny.mulByIntDual_degree {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn) (hdeg : φ.degree = n.natAbs) :
    (Isogeny.mulByIntDual w).degree = φ.degree := by
  have h := Isogeny.degree_mul_mulByIntDual_degree w
  have h2 : (n ^ 2).toNat = n.natAbs * n.natAbs := by
    rw [sq, ← Int.natAbs_mul_self, Int.toNat_natCast]
  rw [hdeg, h2] at h
  rw [hdeg]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)) h

end DualDegree

/-! ### The double dual `φ̂̂ = φ` (Silverman III.6.2(e), item 4) -/

section DoubleDual

variable {F : Type*} [Field F] {W₁ W₂ : Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The double dual** `φ̂̂ = φ` (Silverman III.6.2(e)): for *any* `[n]`-witness `ŵ` of the
dual, `φ̂̂ ∘ φ̂ = [n]₂` and `φ ∘ φ̂ = [n]₂` (the second composition), so uniqueness applied
to `φ̂` gives `φ̂̂ = φ`. The canonical `ŵ` is `w.dual hcov`. -/
theorem Isogeny.mulByIntDual_mulByIntDual {φ : Isogeny W₁ W₂} {n : ℤ} {hn : n ≠ 0}
    (w : φ.HasMulByIntDualWitness n hn)
    (ŵ : (Isogeny.mulByIntDual w).HasMulByIntDualWitness n hn)
    (hcov : φ.MulByIntPullbackCovariant n hn) :
    Isogeny.mulByIntDual ŵ = φ :=
  Isogeny.compose_right_cancel
    ((Isogeny.mulByIntDual_compose ŵ).trans (Isogeny.compose_mulByIntDual w hcov).symm)

end DoubleDual

/-! ### Duals reverse composition: `(ψ∘φ)^ = φ̂ ∘ ψ̂` (Silverman III.6.2(b), item 5) -/

section ReverseComposition

variable {F : Type*} [Field F] {W₁ W₂ W₃ : Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- **Duals reverse composition** `(ψ∘φ)^ = φ̂ ∘ ψ̂` (Silverman III.6.2(b)): both sides
compose with `ψ ∘ φ` to `[m·n]` — the left by the defining identity of the composite
witness, the right by the chain
`(φ̂∘ψ̂)∘(ψ∘φ) = φ̂∘((ψ̂∘ψ)∘φ) = φ̂∘([n]∘φ) = φ̂∘(φ∘[n]) = (φ̂∘φ)∘[n] = [m]∘[n] = [m·n]`
(covariance of `φ` against `[n]` in the middle) — then uniqueness. -/
theorem Isogeny.mulByIntDual_compose_reverse {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    {n m : ℤ} {hn : n ≠ 0} {hm : m ≠ 0}
    (wψ : ψ.HasMulByIntDualWitness n hn) (wφ : φ.HasMulByIntDualWitness m hm)
    (hcov : φ.MulByIntPullbackCovariant n hn) :
    Isogeny.mulByIntDual (wψ.compose wφ hcov) =
      (Isogeny.mulByIntDual wφ).compose (Isogeny.mulByIntDual wψ) := by
  refine Isogeny.compose_right_cancel (φ := ψ.compose φ) ?_
  rw [Isogeny.mulByIntDual_compose (wψ.compose wφ hcov), Isogeny.compose_assoc,
    ← Isogeny.compose_assoc (Isogeny.mulByIntDual wψ) ψ φ,
    Isogeny.mulByIntDual_compose wψ, ← Isogeny.compose_mulByInt_of_covariant hcov,
    ← Isogeny.compose_assoc, Isogeny.mulByIntDual_compose wφ,
    Isogeny.mulByInt_compose_mulByInt W₁ hm hn]

end ReverseComposition

/-! ### The canonical dual `Isogeny.canonicalDual` (item 6)

The faithful witness at the Silverman index `n = deg φ`. Since `HasMulByIntDualWitness` is
a proposition, the canonical dual is independent of the witness, and the
all-witnesses-agree theorem (`eq_canonicalDual`) plus the `∃!`-form make it *the* dual. -/

section Canonical

variable {F : Type*} [Field F] {W₁ W₂ W₃ : Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]

/-- `deg φ ≠ 0` as an integer — the canonical `ν`-index is admissible
(`Isogeny.degree_pos'` is the unconditional two-curve degree positivity). -/
theorem Isogeny.intDegree_ne_zero (φ : Isogeny W₁ W₂) : (φ.degree : ℤ) ≠ 0 :=
  Int.natCast_ne_zero.mpr φ.degree_pos'.ne'

/-- **The canonical dual witness** (Silverman III.6.1's exact bookkeeping): the faithful
`[n]`-witness at `n = deg φ`. -/
abbrev Isogeny.HasCanonicalDualWitness (φ : Isogeny W₁ W₂) : Prop :=
  φ.HasMulByIntDualWitness (φ.degree : ℤ) φ.intDegree_ne_zero

/-- The faithful dual is invariant under transporting the witness along an equality of
integer indices. -/
theorem Isogeny.mulByIntDual_congrInt {φ : Isogeny W₁ W₂} {n n' : ℤ} {hn : n ≠ 0}
    {hn' : n' ≠ 0} (h : n = n') (w : φ.HasMulByIntDualWitness n hn) :
    Isogeny.mulByIntDual (w.congrInt h (hn' := hn')) = Isogeny.mulByIntDual w := by
  subst h; rfl

/-- **The canonical dual** `φ̂ : E₂ → E₁` (Silverman III.6.1): the faithful dual at the
canonical index `n = deg φ`, satisfying `φ̂ ∘ φ = [deg φ]` (`canonicalDual_compose`). Since
the witness is a proposition, `canonicalDual` does not depend on it, and every reverse
isogeny with the defining property equals it (`eq_canonicalDual`). -/
noncomputable def Isogeny.canonicalDual (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness) : Isogeny W₂ W₁ :=
  Isogeny.mulByIntDual w

/-- **The defining identity of the canonical dual**: `φ̂ ∘ φ = [deg φ]`. -/
theorem Isogeny.canonicalDual_compose (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness) :
    (φ.canonicalDual w).compose φ = Isogeny.mulByInt W₁ φ.intDegree_ne_zero :=
  Isogeny.mulByIntDual_compose w

/-- **All witnesses agree / uniqueness of the canonical dual**: any `ψ` with
`ψ ∘ φ = [deg φ]` equals `canonicalDual φ`. -/
theorem Isogeny.eq_canonicalDual (φ : Isogeny W₁ W₂) (w : φ.HasCanonicalDualWitness)
    {ψ : Isogeny W₂ W₁}
    (hψ : ψ.compose φ = Isogeny.mulByInt W₁ φ.intDegree_ne_zero) :
    ψ = φ.canonicalDual w :=
  Isogeny.eq_mulByIntDual w hψ

/-- **`∃!`-form of the dual isogeny** (Silverman III.6.1 + III.6.2 uniqueness): given a
canonical witness, there is exactly one reverse isogeny composing with `φ` to `[deg φ]`. -/
theorem Isogeny.existsUnique_dual (φ : Isogeny W₁ W₂) (w : φ.HasCanonicalDualWitness) :
    ∃! ψ : Isogeny W₂ W₁,
      ψ.compose φ = Isogeny.mulByInt W₁ φ.intDegree_ne_zero :=
  ⟨φ.canonicalDual w, φ.canonicalDual_compose w, fun _ hψ ↦ φ.eq_canonicalDual w hψ⟩

/-- **`deg φ̂ = deg φ`** for the canonical dual (Silverman III.6.2(d) at `m = deg φ`). -/
theorem Isogeny.canonicalDual_degree (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness) :
    (φ.canonicalDual w).degree = φ.degree :=
  Isogeny.mulByIntDual_degree w (Int.natAbs_natCast φ.degree).symm

/-- **The canonical second composition** `φ ∘ φ̂ = [deg φ]` on `E₂` (Silverman
III.6.2(a)), given the covariance of `φ` against `[deg φ]`. -/
theorem Isogeny.compose_canonicalDual (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness)
    (hcov : φ.MulByIntPullbackCovariant (φ.degree : ℤ) φ.intDegree_ne_zero) :
    φ.compose (φ.canonicalDual w) = Isogeny.mulByInt W₂ φ.intDegree_ne_zero :=
  Isogeny.compose_mulByIntDual w hcov

/-- **The canonical dual carries a canonical witness**: `w.dual hcov` is an
`[deg φ]`-witness for `φ̂`, transported to the index `deg φ̂` along
`deg φ̂ = deg φ` (`canonicalDual_degree`). -/
theorem Isogeny.canonicalDual_hasCanonicalDualWitness (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness)
    (hcov : φ.MulByIntPullbackCovariant (φ.degree : ℤ) φ.intDegree_ne_zero) :
    (φ.canonicalDual w).HasCanonicalDualWitness :=
  (w.dual hcov).congrInt (by rw [φ.canonicalDual_degree w])

/-- **The canonical double dual** `φ̂̂ = φ` (Silverman III.6.2(e)). -/
theorem Isogeny.canonicalDual_canonicalDual (φ : Isogeny W₁ W₂)
    (w : φ.HasCanonicalDualWitness)
    (hcov : φ.MulByIntPullbackCovariant (φ.degree : ℤ) φ.intDegree_ne_zero) :
    (φ.canonicalDual w).canonicalDual
        (φ.canonicalDual_hasCanonicalDualWitness w hcov) = φ :=
  (Isogeny.mulByIntDual_congrInt (by rw [φ.canonicalDual_degree w])
      (Isogeny.HasMulByIntDualWitness.dual w hcov)).trans
    (Isogeny.mulByIntDual_mulByIntDual w
      (Isogeny.HasMulByIntDualWitness.dual w hcov) hcov)

/-- **Canonical witnesses compose** (the `ν`-index bookkeeping of III.6.2(b)): the
composite of the canonical witnesses, transported along
`deg φ · deg ψ = deg (ψ∘φ)` (`compose_degree`). -/
theorem Isogeny.HasCanonicalDualWitness.compose {ψ : Isogeny W₂ W₃}
    {φ : Isogeny W₁ W₂} (wψ : ψ.HasCanonicalDualWitness)
    (wφ : φ.HasCanonicalDualWitness)
    (hcov : φ.MulByIntPullbackCovariant (ψ.degree : ℤ) ψ.intDegree_ne_zero) :
    (ψ.compose φ).HasCanonicalDualWitness :=
  (Isogeny.HasMulByIntDualWitness.compose wψ wφ hcov).congrInt
    (by rw [Isogeny.compose_degree, Nat.cast_mul])

/-- **Canonical duals reverse composition** `(ψ∘φ)^ = φ̂ ∘ ψ̂` (Silverman III.6.2(b), the
canonical form). -/
theorem Isogeny.canonicalDual_compose_reverse {ψ : Isogeny W₂ W₃} {φ : Isogeny W₁ W₂}
    (wψ : ψ.HasCanonicalDualWitness) (wφ : φ.HasCanonicalDualWitness)
    (hcov : φ.MulByIntPullbackCovariant (ψ.degree : ℤ) ψ.intDegree_ne_zero) :
    (ψ.compose φ).canonicalDual (wψ.compose wφ hcov) =
      (φ.canonicalDual wφ).compose (ψ.canonicalDual wψ) :=
  (Isogeny.mulByIntDual_congrInt (by rw [Isogeny.compose_degree, Nat.cast_mul])
      (Isogeny.HasMulByIntDualWitness.compose wψ wφ hcov)).trans
    (Isogeny.mulByIntDual_compose_reverse wψ wφ hcov)

end Canonical

/-! ### Concrete instance: the Verschiebung (`φ = π`, Silverman III.6.1 Case 2)

The covariance of `π` is a theorem, so every corollary below is hypothesis-free. Spot
checks: `deg V = q` and `V̂ = π`. -/

section FrobeniusInstance

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

/-- **The second composition for Frobenius**: `π ∘ V = [q]` (Silverman III.6.2(a) for
`π`; the companion of `dualFrobenius_compose_frobenius`). Hypothesis-free: the covariance
of `π` is a theorem. -/
theorem frobenius_compose_dualFrobenius :
    (Isogeny.frobenius W).compose (dualFrobenius W) =
      Isogeny.mulByInt W (intCardK_ne_zero (K := K)) :=
  Isogeny.compose_mulByIntDual (frobeniusMulByIntDualWitness W)
    (Isogeny.frobenius_mulByIntPullbackCovariant W _ intCardK_ne_zero)

/-- **`deg V = q`** (Silverman III.6.2(d) for the Verschiebung): from
`deg π · deg V = q²` and `deg π = q`. -/
theorem dualFrobenius_degree : (dualFrobenius W).degree = Fintype.card K := by
  have h := Isogeny.mulByIntDual_degree (frobeniusMulByIntDualWitness W)
    (by rw [Isogeny.frobenius_degree, Int.natAbs_natCast])
  rw [Isogeny.frobenius_degree] at h
  exact h

/-- **Uniqueness of the Verschiebung**: any `ψ` with `ψ ∘ π = [q]` is `V`. -/
theorem eq_dualFrobenius {ψ : Isogeny W W}
    (hψ : ψ.compose (Isogeny.frobenius W) =
      Isogeny.mulByInt W (intCardK_ne_zero (K := K))) :
    ψ = dualFrobenius W :=
  Isogeny.eq_mulByIntDual (frobeniusMulByIntDualWitness W) hψ

/-- **The Verschiebung carries the `[q]`-witness** — the canonical witness through which
`V̂` is formed. -/
theorem dualFrobenius_hasMulByIntDualWitness :
    (dualFrobenius W).HasMulByIntDualWitness ((Fintype.card K : ℕ) : ℤ)
      (intCardK_ne_zero (K := K)) :=
  (frobeniusMulByIntDualWitness W).dual
    (Isogeny.frobenius_mulByIntPullbackCovariant W _ intCardK_ne_zero)

/-- **`V̂ = π`** (Silverman III.6.2(e) spot check): the dual of the Verschiebung is the
Frobenius. -/
theorem dualFrobenius_dual_eq_frobenius :
    Isogeny.mulByIntDual (dualFrobenius_hasMulByIntDualWitness W) =
      Isogeny.frobenius W :=
  Isogeny.mulByIntDual_mulByIntDual (frobeniusMulByIntDualWitness W) _
    (Isogeny.frobenius_mulByIntPullbackCovariant W _ intCardK_ne_zero)

/-- The Verschiebung **is** the canonical dual of `π` (at the canonical index
`deg π = q`). -/
theorem dualFrobenius_eq_canonicalDual :
    dualFrobenius W = (Isogeny.frobenius W).canonicalDual
      ((frobeniusMulByIntDualWitness W).congrInt
        (by rw [Isogeny.frobenius_degree])) :=
  (Isogeny.mulByIntDual_congrInt (by rw [Isogeny.frobenius_degree])
    (frobeniusMulByIntDualWitness W)).symm

end FrobeniusInstance

/-! ### Concrete instance: the iterated Verschiebung (`φ = πʳ`) -/

section FrobeniusPowerInstance

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : Affine K) [W.IsElliptic]

/-- **The second composition for `πʳ`**: `πʳ ∘ Vᵣ = [qʳ]`. Hypothesis-free. -/
theorem frobeniusPower_compose_dualFrobeniusPower (r : ℕ) :
    (Isogeny.frobeniusPower W r).compose (dualFrobeniusPower W r) =
      Isogeny.mulByInt W (pow_ne_zero r (intCardK_ne_zero (K := K))) :=
  Isogeny.compose_mulByIntDual (frobeniusPowerMulByIntDualWitness W r)
    (Isogeny.frobeniusPower_mulByIntPullbackCovariant W r _
      (pow_ne_zero r intCardK_ne_zero))

/-- **`deg Vᵣ = qʳ`**. -/
theorem dualFrobeniusPower_degree (r : ℕ) :
    (dualFrobeniusPower W r).degree = Fintype.card K ^ r := by
  have h := Isogeny.mulByIntDual_degree (frobeniusPowerMulByIntDualWitness W r)
    (by rw [Isogeny.frobeniusPower_degree, Int.natAbs_pow, Int.natAbs_natCast])
  rw [Isogeny.frobeniusPower_degree] at h
  exact h

/-- **Uniqueness of the iterated Verschiebung**: any `ψ` with `ψ ∘ πʳ = [qʳ]` is `Vᵣ`. -/
theorem eq_dualFrobeniusPower (r : ℕ) {ψ : Isogeny W W}
    (hψ : ψ.compose (Isogeny.frobeniusPower W r) =
      Isogeny.mulByInt W (pow_ne_zero r (intCardK_ne_zero (K := K)))) :
    ψ = dualFrobeniusPower W r :=
  Isogeny.eq_mulByIntDual (frobeniusPowerMulByIntDualWitness W r) hψ

/-- **The iterated Verschiebung carries the `[qʳ]`-witness.** -/
theorem dualFrobeniusPower_hasMulByIntDualWitness (r : ℕ) :
    (dualFrobeniusPower W r).HasMulByIntDualWitness
      (((Fintype.card K : ℕ) : ℤ) ^ r) (pow_ne_zero r (intCardK_ne_zero (K := K))) :=
  (frobeniusPowerMulByIntDualWitness W r).dual
    (Isogeny.frobeniusPower_mulByIntPullbackCovariant W r _
      (pow_ne_zero r intCardK_ne_zero))

/-- **`V̂ᵣ = πʳ`**: the dual of the iterated Verschiebung is the iterated Frobenius. -/
theorem dualFrobeniusPower_dual_eq_frobeniusPower (r : ℕ) :
    Isogeny.mulByIntDual (dualFrobeniusPower_hasMulByIntDualWitness W r) =
      Isogeny.frobeniusPower W r :=
  Isogeny.mulByIntDual_mulByIntDual (frobeniusPowerMulByIntDualWitness W r) _
    (Isogeny.frobeniusPower_mulByIntPullbackCovariant W r _
      (pow_ne_zero r intCardK_ne_zero))

end FrobeniusPowerInstance

/-! ### Concrete instance: `[ℓ]^ = [ℓ]` (field-general) -/

section MulByIntInstance

variable {F : Type*} [Field F] (W : Affine F) [W.IsElliptic]

/-- **`[ℓ]^ = [ℓ]`** (Silverman III.6.2's self-duality of multiplication): the faithful
dual of `[ℓ]` along its `[ℓ·ℓ]`-witness is `[ℓ]` itself — by uniqueness, since
`[ℓ] ∘ [ℓ] = [ℓ·ℓ]`. Field-general. -/
theorem mulByIntDual_mulByIntSelf {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    Isogeny.mulByIntDual (mulByIntSelfDualWitness W hℓ) = Isogeny.mulByInt W hℓ :=
  (Isogeny.eq_mulByIntDual (mulByIntSelfDualWitness W hℓ)
    (Isogeny.mulByInt_compose_mulByInt W hℓ hℓ)).symm

end MulByIntInstance

/-! ### Concrete instance: the Galois-built dual of `[ℓ]` is `[ℓ]` (over `K̄`)

`dualMulByInt` (`EC/IsogenyAG/DualGaloisClosed.lean`) was built through the III.4.11 Galois
fixed-field machinery with `ν = [deg [ℓ]]`; uniqueness now *identifies* it with `[ℓ]`. -/

section AlgClosedWiring

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

set_option maxHeartbeats 800000 in
-- unifying the Galois-built dual (whose witness fields unfold through
-- `dualGaloisData_of_separable_general`) against `dual_comp_pullback` is `whnf`-heavy
/-- **The defining composition of the Galois-built `[ℓ]`-dual**:
`dualMulByInt ∘ [ℓ] = [deg [ℓ]]` in fully bundled form. -/
theorem dualMulByInt_compose_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    (HasseWeil.dualMulByInt W ℓ hℓ hℓF).compose (Isogeny.mulByInt W.toAffine hℓ) =
      Isogeny.mulByInt W.toAffine
        (Int.natCast_ne_zero.mpr (HasseWeil.mulByInt_degree_ne_zero W.toAffine hℓ)) := by
  refine Isogeny.ext_toCurveMap (CurveMap.ext (AlgHom.ext fun z ↦ ?_))
  have h1 := Isogeny.dual_comp_pullback (φ := Isogeny.mulByInt W.toAffine hℓ)
    (Isogeny.hasDualWitness_of_galoisData
      (HasseWeil.dualGaloisData_mulByInt W ℓ hℓ hℓF)) z
  have h2 : (Isogeny.hasDualWitness_of_galoisData
      (HasseWeil.dualGaloisData_mulByInt W ℓ hℓ hℓF)).νPb z =
      HasseWeil.mulByInt_pullbackAlgHom W.toAffine
        ((HasseWeil.mulByInt W.toAffine ℓ).degree : ℤ)
        (Int.natCast_ne_zero.mpr (HasseWeil.mulByInt_degree_ne_zero W.toAffine hℓ)) z := by
    change (HasseWeil.mulByInt W.toAffine
        ((HasseWeil.mulByInt W.toAffine ℓ).degree : ℤ)).pullback z = _
    rw [show (HasseWeil.mulByInt W.toAffine
          ((HasseWeil.mulByInt W.toAffine ℓ).degree : ℤ)).pullback =
        HasseWeil.mulByInt_pullbackAlgHom W.toAffine
          ((HasseWeil.mulByInt W.toAffine ℓ).degree : ℤ)
          (Int.natCast_ne_zero.mpr (HasseWeil.mulByInt_degree_ne_zero W.toAffine hℓ)) from
      dif_neg (Int.natCast_ne_zero.mpr (HasseWeil.mulByInt_degree_ne_zero W.toAffine hℓ))]
  exact h1.trans h2

/-- **The Galois-built dual of `[ℓ]` *is* `[ℓ]`** (all-witnesses-agree in action, over
`K̄`): `dualMulByInt` and `[ℓ]` both compose with `[ℓ]` to `[ℓ²]`, so they are equal. The
two constructions of the dual — the III.4.11 fixed-field route and the faithful
multiplicativity route — produce the same isogeny. -/
theorem dualMulByInt_eq_mulByInt (ℓ : ℤ) (hℓ : ℓ ≠ 0) (hℓF : (ℓ : F) ≠ 0) :
    HasseWeil.dualMulByInt W ℓ hℓ hℓF = Isogeny.mulByInt W.toAffine hℓ := by
  have hd : ((HasseWeil.mulByInt W.toAffine ℓ).degree : ℤ) = ℓ * ℓ := by
    rw [HasseWeil.mulByInt_degree W.toAffine ℓ hℓ,
      Int.toNat_of_nonneg (sq_nonneg ℓ), sq]
  refine Isogeny.compose_right_cancel (φ := Isogeny.mulByInt W.toAffine hℓ) ?_
  rw [dualMulByInt_compose_mulByInt W ℓ hℓ hℓF,
    Isogeny.mulByInt_compose_mulByInt W.toAffine hℓ hℓ]
  exact Isogeny.mulByInt_congr W.toAffine hd

end AlgClosedWiring

/-! ### Concrete instance: the relative Verschiebung (uniqueness + degree)

The double dual for the relative Frobenius is *not* instantiated: it needs the covariance
of `Frob_{p^e} : E → E^{(p^e)}` against `[p^e]` (division polynomials vs. the coefficient
twist), which is genuinely new work; the general `mulByIntDual_mulByIntDual` applies the
moment it is provided. Uniqueness and degree need no covariance. -/

section RelativeVerschiebungInstance

variable {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p]
  [PerfectField F]
variable (E : WeierstrassCurve F) [E.toAffine.IsElliptic]

/-- **The faithful `[p^e]`-witness for the relative Frobenius** — the
`HasMulByIntDualWitness` packaging of the fields of
`hasDualWitnessRelativeFrobeniusOf` (`TwistedFactorization.lean`). -/
theorem relativeFrobeniusMulByIntDualWitness
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (Isogeny.relativeFrobenius p E e).HasMulByIntDualWitness ((p ^ e : ℕ) : ℤ)
      (intPPow_ne_zero p e) :=
  ⟨mulByInt_p_pow_range_le_relativeFrobenius p E hinsep e,
    Isogeny.hbase_of_reflects (Isogeny.relativeFrobenius p E e)
      (HasseWeil.mulByInt_pullbackAlgHom E.toAffine ((p ^ e : ℕ) : ℤ)
        (intPPow_ne_zero p e))
      (mulByInt_p_pow_range_le_relativeFrobenius p E hinsep e)
      (mulByIntBasepoint_holds E.toAffine (intPPow_ne_zero p e))
      (Isogeny.relativeFrobenius p E e).reflects_ordAtInfty⟩

/-- The relative Verschiebung **is** the faithful dual at the `[p^e]`-witness (the two
packagings of the same witness fields produce definitionally the same isogeny). -/
theorem relativeVerschiebungOf_eq_mulByIntDual
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    relativeVerschiebungOf p E hinsep e =
      Isogeny.mulByIntDual (relativeFrobeniusMulByIntDualWitness p E hinsep e) :=
  rfl

/-- **Uniqueness of the relative Verschiebung**: any `ψ` with
`ψ ∘ Frob_{p^e} = [p^e]` is `V̂_{p^e}`. -/
theorem eq_relativeVerschiebungOf
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ)
    {ψ : Isogeny (E.iterateFrobeniusTwist p e).toAffine E.toAffine}
    (hψ : ψ.compose (Isogeny.relativeFrobenius p E e) =
      Isogeny.mulByInt E.toAffine (intPPow_ne_zero p e)) :
    ψ = relativeVerschiebungOf p E hinsep e :=
  Isogeny.compose_right_cancel (hψ.trans
    (relativeVerschiebungOf_compose_relativeFrobenius p E hinsep e).symm)

/-- **`deg V̂_{p^e} = p^e`** (Silverman III.6.2(d) for the relative Verschiebung): from
`deg Frob · deg V̂ = deg [p^e] = p^(2e)` and `deg Frob = p^e`. -/
theorem relativeVerschiebungOf_degree
    (hinsep : ¬(Isogeny.mulByInt E.toAffine (intP_ne_zero p)).IsSeparable) (e : ℕ) :
    (relativeVerschiebungOf p E hinsep e).degree = p ^ e := by
  have h := Isogeny.compose_degree (relativeVerschiebungOf p E hinsep e)
    (Isogeny.relativeFrobenius p E e)
  rw [relativeVerschiebungOf_compose_relativeFrobenius p E hinsep e,
    Isogeny.mulByInt_degree E.toAffine (intPPow_ne_zero p e),
    relativeFrobenius_degree p E e] at h
  have h2 : ((((p ^ e : ℕ) : ℤ)) ^ 2).toNat = p ^ e * p ^ e := by
    rw [sq, ← Nat.cast_mul, Int.toNat_natCast]
  rw [h2] at h
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos (Fact.out : p.Prime).pos e) h).symm

/-- Uniqueness for the finite-base Verschiebung (axiom-clean instantiation). -/
theorem eq_relativeVerschiebungFinite [Fintype F] (e : ℕ)
    {ψ : Isogeny (E.iterateFrobeniusTwist p e).toAffine E.toAffine}
    (hψ : ψ.compose (Isogeny.relativeFrobenius p E e) =
      Isogeny.mulByInt E.toAffine (intPPow_ne_zero p e)) :
    ψ = relativeVerschiebungFinite p E e :=
  eq_relativeVerschiebungOf p E (Isogeny.mulByInt_p_not_isSeparable_finite p E) e hψ

/-- **`deg V̂ = p^e` for the finite-base Verschiebung** (axiom-clean instantiation). -/
theorem relativeVerschiebungFinite_degree [Fintype F] (e : ℕ) :
    (relativeVerschiebungFinite p E e).degree = p ^ e :=
  relativeVerschiebungOf_degree p E (Isogeny.mulByInt_p_not_isSeparable_finite p E) e

end RelativeVerschiebungInstance

end HasseWeil.EC
