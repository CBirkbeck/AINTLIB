/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# The acyclicity lemma (Stacks 00N0) and the 00N1 scaffolding — [T-ACYC]

PLANNING SKELETON (statements + `:= sorry`, no proofs) for the pieces of Stacks 00N1
(Buchsbaum–Eisenbud, Proposition 10.102.9) that the two interior cores of
`ForMathlib.BuchsbaumEisenbud` (`be_forward_core`, `be_backward_core`) consume.  See
`projects/ModularCurves/.mathlib-quality/decomposition-depth.md` for the ticket tree, the verbatim
Stacks quotes per leaf, the 3-attacks-per-leaf audit, and the make-or-break identification.

## The make-or-break IS the acyclicity lemma 00N0 — and it is TRACTABLE

The prior decomposition feared "Peskine–Szpiro / 0AVQ" as a multi-week wall.  Two corrections from
reading the ACTUAL Stacks proofs:

* The acyclicity lemma is **Stacks 00N0 = Lemma 10.102.8**, cited "[Lemma 1.8, Peskine–Szpiro]".
  Tag **0AVQ is unrelated** (it is "Torsion free modules", Section 31.11) — the earlier locator was
  wrong.
* 00N0's ENTIRE proof is: decompose the complex `0 → Mₑ → ⋯ → M₀` into the syzygy short exact
  sequences and apply the depth-of-a-SES inequality **Stacks 00LX (Lemma 10.72.6)** repeatedly.
  00LX in turn follows from the depth⟺Ext characterisation (`ForMathlib.Grade.rees_core`, PROVED)
  and the covariant `Ext` long exact sequence (`ForMathlib.Grade` already uses it).  So the make-or-
  break rests on machinery THIS BRANCH already built.  See `ForMathlib.Depth`.

## What the two cores consume from here

* `be_backward_core` (00N1 `(2)⟹(1)`): `acyclicityLemma_hasDepthGE_homology` (00N0) below, applied at
  the largest non-exact spot after localising the lower-dimensional primes to exactness (that
  localisation of the grade conditions is `Ideal.gradeGE_localize`, PROVED in `ForMathlib.Grade`),
  plus `Module.hasDepthGE_one_iff_notMem_associatedPrimes` (a homology supported only at `𝔪` has
  depth `0`) to discharge the right disjunct.
* `be_forward_core` (00N1 `(1)⟹(2)`): `idealOfMinors_eq_top_of_exact_of_isAssociatedPrime`
  (00MY+00MW: exact free complex over a depth-`0` local ring ⟹ minor ideal `= ⊤`) at each
  associated prime, then a prime-avoidance nonzerodivisor
  (`exists_isSMulRegular_of_forall_not_le_associatedPrimes`, PROVED in `ForMathlib.BuchsbaumEisenbud`)
  and `exact_baseChange_quotient_of_isSMulRegular` (00MZ) + induction on `e`.  NO depth invariant, NO
  Auslander–Buchsbaum.
-/
import Mathlib
import ModularCurves.ForMathlib.FittingIdeals
import ModularCurves.ForMathlib.Depth

noncomputable section

open RingTheory.Sequence

universe u

/-! ## [T-ACYC.00N0] The acyclicity lemma — Stacks 00N0 (Lemma 10.102.8) — MAKE-OR-BREAK

> "Let `R` be a local Noetherian ring. Let `0 → Mₑ → Mₑ₋₁ → … → M₀` be a complex of finite
> `R`-modules. Assume `depth(Mᵢ) ≥ i`. Let `i` be the largest index such that the complex is not
> exact at `Mᵢ`. If `i > 0` then `H = ker(Mᵢ → Mᵢ₋₁)/im(Mᵢ₊₁ → Mᵢ)` has `depth(H) ≥ 1`."

We phrase it, disjunctively, at the spot `Mᵢ₊₁` (whose homology `ker(φ i)/im(φ (i+1))` uses no `ℕ`
subtraction — both are submodules of `M (i+1)`): assuming exactness at every HIGHER spot, either the
complex is already exact at `Mᵢ₊₁`, or its homology there has depth `≥ 1`.  This is exactly the
contrapositive-friendly form `be_backward_core` consumes: it rules out the depth-`≥ 1` disjunct by
supporting the homology at `𝔪`, forcing exactness. -/

/-- **[T-ACYC.00N0] Stacks 00N0 (Lemma 10.102.8), the acyclicity lemma — the make-or-break leaf.**
`M` a finite complex of finite modules over a Noetherian local ring with `depth(Mⱼ) ≥ j` for
`j ≤ e` (and `Mⱼ = 0` for `j > e`); if the complex is exact at every spot `> i+1`, then it is exact
at `Mᵢ₊₁` **or** the homology `ker(φ i) / im(φ (i+1))` there has depth `≥ 1`.

Proof (Stacks): cut `M` into the syzygy short exact sequences and push `depth(Mⱼ) ≥ j` down them with
the depth-SES inequalities `Module.hasDepthGE_quotient_of_shortExact` / `..._sub_of_shortExact`
(Stacks 00LX); the last piece `0 → im(φ (i+1)) → ker(φ i) → H → 0` yields `depth(H) ≥ 1`. -/
theorem acyclicityLemma_hasDepthGE_homology
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ℕ → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)]
    (φ : (i : ℕ) → M (i + 1) →ₗ[R] M i)
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (e : ℕ) (hbdd : ∀ j, e < j → Subsingleton (M j))
    (hdepth : ∀ j, j ≤ e → Module.HasDepthGE R (M j) j)
    (i : ℕ) (hie : i + 1 ≤ e)
    (habove : ∀ j, i < j → Function.Exact (φ (j + 1)) (φ j)) :
    Function.Exact (φ (i + 1)) (φ i) ∨
      Module.HasDepthGE R
        (LinearMap.ker (φ i) ⧸ (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype)
        1 := by
  sorry

/-! ## [T-ACYC.00MZ] Exactness modulo a nonzerodivisor — Stacks 00MZ (Lemma 10.102.7)

> "Suppose `R` is a local ring with maximal ideal `𝔪`. Suppose that `0 → R^{nₑ} → … → R^{n₀}` is
> exact at `R^{nₑ}, …, R^{n₁}`. Let `x ∈ 𝔪` be a nonzerodivisor. The complex
> `0 → (R/xR)^{nₑ} → … → (R/xR)^{n₁}` is exact at `(R/xR)^{nₑ}, …, (R/xR)^{n₂}`."

Proof (Stacks): the short exact sequence of complexes `0 → F_• →ˣ F_• → F_•/xF_• → 0` and its snake
long exact homology sequence.  Consumed by `be_forward_core`'s induction on `e`. -/

/-- **[T-ACYC.00MZ] Stacks 00MZ (Lemma 10.102.7).**  An exact finite free complex stays exact after
base change along `R → R/xR` for a nonzerodivisor `x` (snake lemma on `0 → F_• →ˣ F_• → F_•/xF_• → 0`).
The base-changed maps are `(φ i).baseChange (R ⧸ (x))`. -/
theorem exact_baseChange_quotient_of_isSMulRegular
    {R : Type u} [CommRing R] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → R) →ₗ[R] (Fin (rk i) → R))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (x : R) (hx : IsSMulRegular R x) :
    ∀ i, Function.Exact
      ((φ (i + 1)).baseChange (R ⧸ Ideal.span {x}))
      ((φ i).baseChange (R ⧸ Ideal.span {x})) := by
  sorry

/-! ## [T-ACYC.00MY+00MW] Depth-0 splitting ⟹ minor ideal `= ⊤` — Stacks 00MY+00MW (10.102.3/6)

> 00MY: "Assume `𝔪 ∈ Ass(R)`, in other words `R` has depth `0`. Suppose that `0 → R^{nₑ} → … → R^{n₀}`
> is exact at `R^{nₑ}, …, R^{n₁}`. Then the complex is isomorphic to a direct sum of trivial
> complexes."
> 00MW: for a direct sum of trivial complexes, "the maps `φᵢ` have rank `rᵢ`", "`rank(φᵢ₊₁) +
> rank(φᵢ) = nᵢ`", and "each `I(φᵢ) = R`."

Composed: over a depth-`0` Noetherian local ring, an exact free complex has every minor ideal
`I(φᵢ) = R`.  This is the fact `be_forward_core` establishes at each associated prime `𝔮 ∈ Ass(R)`
(after localising), giving `I(φᵢ) ⊄ 𝔮`, the input to the prime-avoidance nonzerodivisor. -/

/-- **[T-ACYC.00MY+00MW] Stacks 10.102.3 + 10.102.6.**  Over a Noetherian local ring of depth `0`
(`𝔪 ∈ Ass(R)`), an exact finite free complex is a direct sum of trivial complexes, so its interior
minor ideal is the unit ideal: `I(φᵢ) = ⊤` (Lean `φ (i-1)` = Stacks `φᵢ`, size `rnk i`). -/
theorem idealOfMinors_eq_top_of_exact_of_isAssociatedPrime
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth0 : IsLocalRing.maximalIdeal R ∈ associatedPrimes R R)
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → R) →ₗ[R] (Fin (rk i) → R))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (hie : i < e) :
    LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤ := by
  sorry

end
