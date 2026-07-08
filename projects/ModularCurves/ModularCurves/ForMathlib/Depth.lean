/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Module depth `≥ k` over a Noetherian local ring, and its API — [T-DEPTH]

PLANNING SKELETON (statements + `:= sorry`, no proofs) for the depth invariant that closes the
BACKWARD core of Buchsbaum–Eisenbud (Stacks 00N1 `(2)⟹(1)`) via the acyclicity lemma
(Stacks 00N0 = Lemma 10.102.8).  See
`projects/ModularCurves/.mathlib-quality/decomposition-depth.md` for the full ticket tree, the
verbatim Stacks quotes per leaf, and the route decision.

## The invariant

mathlib has NO packaged `depth` (only `RingTheory.Sequence.IsRegular`; `RingTheory/Regular/Depth.lean`
is a deprecated stub, and `RegularSequence.lean`'s own TODO lists "depth" as unbuilt).  We package
the LEAN predicate `Module.HasDepthGE R M k := "𝔪 contains an M-regular sequence of length k"`
(Stacks 00LE/00LF depth, in `≥ k` predicate form).  This is the module analogue of the existing
`Ideal.gradeGE` (`ForMathlib.Grade`, the `M = R` case): the acyclicity lemma 00N0 states its
hypothesis `depth(Mᵢ) ≥ i` and conclusion `depth(H) ≥ 1` purely in `≥`-form, so the predicate is the
leanest faithful shape (no `ℕ∞` arithmetic).

## The decisive reuse — depth⟺Ext is ALREADY PROVEN

Stacks 00LW (Lemma 10.72.5): `depth(M) = min { i | Extⁱ(R/𝔪, M) ≠ 0 }`, equivalently
`depth(M) ≥ k ⟺ Extⁱ_R(R/𝔪, M) = 0 ∀ i < k`.  This is EXACTLY `ForMathlib.Grade.rees_core`
specialised to `I = 𝔪` (that lemma is proved there in full, for a GENERAL finite module `M`, by the
classical Rees induction — it is stated `∀ M`, not just `M = R`).  So
`hasDepthGE_iff_forall_subsingleton_ext` is discharged by exposing `rees_core`; the depth⟺Ext bridge
is NOT new work.

Consequently the depth-of-a-short-exact-sequence inequalities (Stacks 00LX = Lemma 10.72.6) — the
sole engine of the acyclicity lemma — follow from that Ext characterisation plus the covariant `Ext`
long exact sequence (`Ext.covariant_sequence_exact₁/₂/₃`), the SAME machinery `ForMathlib.Grade`
already drives.  This is why the depth layer is tractable, not a wall.

## NOT needed: Auslander–Buchsbaum

The Stacks proof of the FORWARD core (00N1 `(1)⟹(2)`) does **not** use Auslander–Buchsbaum: it runs
via associated primes (depth-0 localisations), rank stability, a prime-avoidance nonzerodivisor, and
quotient-by-a-nonzerodivisor (00MZ) + induction.  Neither direction of 00N1 invokes 090V/0AVJ.  So
this file contains NO Auslander–Buchsbaum leaf.
-/
import Mathlib

noncomputable section

open RingTheory.Sequence CategoryTheory Abelian

universe u

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **[T-DEPTH.def]** `HasDepthGE R M k`: the maximal ideal `𝔪` of the local ring `R` contains an
`M`-regular sequence of length `k` (Stacks 00LE/00LF, `depth_𝔪(M) ≥ k`, predicate form).  The module
analogue of `Ideal.gradeGE` (`ForMathlib.Grade`), which is the `M = R` special case.  A real `def`
(no `sorry`); everything below is API. -/
def HasDepthGE (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ) : Prop :=
  ∃ rs : List R, rs.length = k ∧ IsRegular M rs ∧ ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R

/-- `HasDepthGE R M 0 ↔ Nontrivial M` (the empty sequence is `M`-regular iff `M ≠ 0`); documents the
convention that `depth` of the zero module is not `≥ 0` in this predicate — callers carry
`Nontrivial` exactly where Stacks 00LX/00N0 say "nonzero finite module". -/
theorem hasDepthGE_zero_iff (M : Type u) [AddCommGroup M] [Module R M] :
    HasDepthGE R M 0 ↔ Nontrivial M := by sorry

/-- **[T-DEPTH.mono]** `depth` is monotone in `k`: a prefix of an `M`-regular sequence is
`M`-regular. -/
theorem hasDepthGE_mono {M : Type u} [AddCommGroup M] [Module R M] {j k : ℕ}
    (h : HasDepthGE R M k) (hjk : j ≤ k) : HasDepthGE R M j := by sorry

/-- **[T-DEPTH.ext] Stacks 00LW (Lemma 10.72.5).**  Over a Noetherian local ring, for a nonzero
finite module, `depth(M) ≥ k` iff `Extⁱ_R(R/𝔪, M) = 0` for every `i < k`.  This is
`ForMathlib.Grade.rees_core` at `I = 𝔪` (that lemma is proved in full there, for GENERAL `M`); the
discharge is to expose `rees_core` (currently `private`) or re-run its Rees induction. -/
theorem hasDepthGE_iff_forall_subsingleton_ext [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] (k : ℕ) :
    HasDepthGE R M k ↔
      ∀ i : Fin k, Subsingleton
        (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R M) i) := by sorry

/-! ### Stacks 00LX (Lemma 10.72.6): the three depth inequalities of a short exact sequence

For `0 → A →f→ B →g→ C → 0` of nonzero finite modules, Stacks 00LX asserts
(1) `depth B ≥ min(depth A, depth C)`,
(2) `depth C ≥ min(depth B, depth A − 1)`,
(3) `depth A ≥ min(depth B, depth C + 1)`.
Each follows from the `Ext`-characterisation above and the covariant long exact `Ext`-sequence
`⋯ → Extⁱ(κ,A) → Extⁱ(κ,B) → Extⁱ(κ,C) → Extⁱ⁺¹(κ,A) → ⋯`.  **(2) and (3) are the load-bearing
ones** for the acyclicity lemma; (1) is stated for completeness.  We give them in `≥ k` predicate
form (`min(x, y) ≥ k ⟺ x ≥ k ∧ y ≥ k`), which is what 00N0's syzygy induction consumes and avoids
`ℕ∞` truncated subtraction. -/

/-- **[T-DEPTH.ses1] Stacks 00LX(1).**  `depth B ≥ min(depth A, depth C)`. -/
theorem hasDepthGE_mid_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hA : HasDepthGE R A k) (hC : HasDepthGE R C k) : HasDepthGE R B k := by sorry

/-- **[T-DEPTH.ses2] Stacks 00LX(2) — LOAD-BEARING.**  `depth C ≥ min(depth B, depth A − 1)`, i.e.
`depth B ≥ k` and `depth A ≥ k+1` force `depth C ≥ k`.  This is the inequality that drives the
acyclicity lemma (Stacks 00N0) down the syzygy tower. -/
theorem hasDepthGE_quotient_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hB : HasDepthGE R B k) (hA : HasDepthGE R A (k + 1)) : HasDepthGE R C k := by sorry

/-- **[T-DEPTH.ses3] Stacks 00LX(3) — LOAD-BEARING.**  `depth A ≥ min(depth B, depth C + 1)`, i.e.
`depth B ≥ k+1` and `depth C ≥ k` force `depth A ≥ k+1`.  Used for the `0 → Kᵢ → Mᵢ → im → 0`
kernel-depth step of the acyclicity lemma (`depth Kᵢ ≥ 1` from `depth Mᵢ ≥ i ≥ 1`, taking `k = 0`). -/
theorem hasDepthGE_sub_of_shortExact [IsNoetherianRing R]
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
    [Nontrivial A] [Nontrivial B] [Nontrivial C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {k : ℕ} (hB : HasDepthGE R B (k + 1)) (hC : HasDepthGE R C k) : HasDepthGE R A (k + 1) := by
  sorry

/-- **[T-DEPTH.ass] Stacks 00LD / 00LW base case.**  `depth(M) ≥ 1 ⟺ 𝔪 ∉ Ass(M)`: the maximal
ideal carries an `M`-regular element iff it is not an associated prime.  This turns "the homology `H`
is supported only at `𝔪` and `H ≠ 0`" into "`¬ HasDepthGE R H 1`" (since then `𝔪 ∈ Ass H`), the
contradiction that closes 00N1's backward induction. -/
theorem hasDepthGE_one_iff_notMem_associatedPrimes [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    HasDepthGE R M 1 ↔ IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := by sorry

/-- **[T-DEPTH.free]**  `depth(Rⁿ) = depth(R)` for `n ≥ 1`: an `R`-regular sequence acts diagonally,
so it is `Rⁿ`-regular.  Lets the acyclicity lemma (over abstract finite modules) be applied to the
free complex of Buchsbaum–Eisenbud, where `Mᵢ = R^{rk i}` and `depth Mᵢ = depth R`. -/
theorem hasDepthGE_pi_of_hasDepthGE {n : ℕ} (hn : 0 < n) (k : ℕ)
    (h : HasDepthGE R R k) : HasDepthGE R (Fin n → R) k := by sorry

end Module

end
