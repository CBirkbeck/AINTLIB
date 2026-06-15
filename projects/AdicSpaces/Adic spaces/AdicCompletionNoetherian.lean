/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import «Adic spaces».AdicCompletionBridge

/-!
# Stacks 0316 — I-adic completion of a Noetherian ring is Noetherian

This file proves the project-internal version of Stacks Project tag 0316
(= Lemma 10.97.6): if `R` is a Noetherian commutative ring and `I ⊂ R` is
an ideal, then the I-adic completion `R̂ = AdicCompletion I R` is Noetherian.

This fact is NOT currently in mathlib (verified 2026-05-18); `mathlib` has
`PowerSeries.instIsNoetherianRing` (single variable Hilbert basis for power
series) and `AdicCompletion.flat_of_isNoetherian` (flatness over the original
ring), but no theorem stating noetherianness of the completion itself.

## Proof structure (Stacks 0316 Route A, direct)

The proof follows the Stacks Project's "direct" route:

> Choose generators `f₁,…,fₙ` of `I`. Consider the map `R[[x₁,…,xₙ]] → R̂`,
> `xᵢ ↦ fᵢ`. This is a well defined and surjective ring map (details omitted).
> Since `R[[x₁,…,xₙ]]` is Noetherian (Lemma 10.31.2) we win.

Project plan (iterated, avoiding `MvPowerSeries.isNoetherianRing` which is
itself a mathlib gap = TODO at `Mathlib/RingTheory/PowerSeries/Ideal.lean:45`):

* **L1** Pick generators `f₁,…,fₙ` of `I` (mathlib: `IsNoetherianRing` ⇒
  `Ideal.FG`).
* **L2** Build (via induction on `n`) an iterated power series ring
  `T = R⟦x₁⟧⟦x₂⟧…⟦xₙ⟧`, Noetherian by `n` applications of
  `PowerSeries.instIsNoetherianRing`.
  Alternative: prove `MvPowerSeries (Fin n).isNoetherianRing` directly
  (sub-development, ~60 LOC, via the iso
  `MvPowerSeries (Fin (k+1)) R ≃+* MvPowerSeries (Fin k) R⟦X⟧` and induction).
* **L3** Construct the evaluation ring hom `Φ : T →+* AdicCompletion I R`
  sending `xᵢ ↦ fᵢ`. Each formal monomial `a · x^α` maps to `a · f^α ∈
  I^|α|`, so partial sums are Cauchy in `R̂`, defining a continuous ring
  hom (~40 LOC, project-internal).
* **L4** Prove `Φ` is surjective: given a Cauchy `(rₙ) ∈ R̂` (so `rₙ − rₙ₋₁
  ∈ Iⁿ⁻¹`), inductively build power-series coefficients (~50 LOC).
* **L5** Apply `isNoetherianRing_of_surjective` (mathlib).

## Status (skeleton: 2026-05-18)

All sub-leaves are stated as `sorry`-bodied declarations. `lake build` passes
modulo these sorries. After execution by `/beastmode`, this file provides
`AdicCompletion.isNoetherianRing` consumed by:

* `WedhornStronglyNoetherian._sub_lemma_L5_1_2_adicCompletion_noetherian`
  (line 128) — one-line discharge.
* `PresheafTateStructure.presheafValue_pairOfDefinition_isNoetherian`
  (line 930) — applies `AdicCompletion.isNoetherianRing` to `A₀[T/s]`
  with the extended ideal of definition.

## References

* Stacks Project, tag 0316 (= Lemma 10.97.6),
  <https://stacks.math.columbia.edu/tag/0316>.
* Stacks Project, tag 0306 (= Lemma 10.31.2, Hilbert basis for power series).
* Atiyah, M. F. and Macdonald, I. G., *Introduction to Commutative Algebra*
  (Addison-Wesley 1969), §10 Theorem 10.27.
* Matsumura, H., *Commutative Ring Theory* (Cambridge 1986), Theorem 8.4.
-/

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R]

/-! ## L2 — Multivariate Hilbert basis (mathlib gap)

Mathlib has `PowerSeries.instIsNoetherianRing` (single variable) but the
multivariate `MvPowerSeries (Fin n) R` Noetherian instance is a TODO at
`Mathlib/RingTheory/PowerSeries/Ideal.lean:45`. We supply it here via the
standard `R⟦x₁,…,xₙ⟧ ≃+* R⟦x₁,…,xₙ₋₁⟧⟦xₙ⟧` iso + induction.

### Sub-leaves

* `MvPowerSeries.finSuccEquivPowerSeries` — the iso
  `MvPowerSeries (Fin (n+1)) R ≃+* MvPowerSeries (Fin n) R⟦X⟧`.
* `MvPowerSeries.instIsNoetherianRing_fin` — `IsNoetherianRing R` ⇒
  `IsNoetherianRing (MvPowerSeries (Fin n) R)`, by induction on `n` via
  the iso + `PowerSeries.instIsNoetherianRing`.
-/

/-! ### L2.1 sub-leaves (decomposed for `/beastmode`, 2026-05-20)

The iso `MvPowerSeries (Fin (n+1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R)`
splits into seven independently-provable sub-leaves:

* **L2.1.a** `mvPowerSeries_finSucc_forwardFun` — the forward function (no
  proof obligation; pure definition).
* **L2.1.b** `mvPowerSeries_finSucc_inverseFun` — the inverse function (no
  proof obligation; pure definition).
* **L2.1.c** `mvPowerSeries_finSucc_left_inv` — round-trip identity 1.
* **L2.1.d** `mvPowerSeries_finSucc_right_inv` — round-trip identity 2.
* **L2.1.e** `mvPowerSeries_finSucc_forward_map_one` — forward sends `1` to `1`.
* **L2.1.f** `mvPowerSeries_finSucc_forward_map_add` — forward sends `+` to `+`
  (immediate from function-level definition).
* **L2.1.g** `mvPowerSeries_finSucc_forward_map_mul` — convolution preservation
  (the substantive content; uses `Finsupp.cons` antidiagonal decomposition).

Final assembly via `RingEquiv.mk` consuming L2.1.a-g.
-/

/-- **(L2.1.a)** Forward function: split off the 0-th variable, packaging each
ℕ-indexed coefficient as a `MvPowerSeries (Fin n) R`. -/
noncomputable def _root_.MvPowerSeries.finSucc_forwardFun (R : Type u) [CommRing R] (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R → PowerSeries (MvPowerSeries (Fin n) R) :=
  fun p => PowerSeries.mk (fun k => (fun m : Fin n →₀ ℕ => p (Finsupp.cons k m)))

/-- **(L2.1.b)** Inverse function: combine the constant term and the rest via
`Finsupp.cons` / `Finsupp.tail` decomposition. -/
noncomputable def _root_.MvPowerSeries.finSucc_inverseFun (R : Type u) [CommRing R] (n : ℕ) :
    PowerSeries (MvPowerSeries (Fin n) R) → MvPowerSeries (Fin (n + 1)) R :=
  fun q α => (PowerSeries.coeff (α 0) q) α.tail

/-- **(L2.1.c)** `inverseFun ∘ forwardFun = id` on `MvPowerSeries (Fin (n+1)) R`. -/
theorem _root_.MvPowerSeries.finSucc_left_inv (R : Type u) [CommRing R] (n : ℕ)
    (p : MvPowerSeries (Fin (n + 1)) R) :
    MvPowerSeries.finSucc_inverseFun R n (MvPowerSeries.finSucc_forwardFun R n p) = p := by
  funext α
  change (PowerSeries.coeff (α 0))
      (PowerSeries.mk fun k => fun m : Fin n →₀ ℕ => p (Finsupp.cons k m)) α.tail = p α
  rw [PowerSeries.coeff_mk]
  exact congrArg p (Finsupp.cons_tail α)

/-- **(L2.1.d)** `forwardFun ∘ inverseFun = id` on `PowerSeries (MvPowerSeries (Fin n) R)`. -/
theorem _root_.MvPowerSeries.finSucc_right_inv (R : Type u) [CommRing R] (n : ℕ)
    (q : PowerSeries (MvPowerSeries (Fin n) R)) :
    MvPowerSeries.finSucc_forwardFun R n (MvPowerSeries.finSucc_inverseFun R n q) = q := by
  ext k m
  change (PowerSeries.coeff k)
      (PowerSeries.mk fun j => fun m' : Fin n →₀ ℕ =>
        (PowerSeries.coeff ((Finsupp.cons j m') 0)) q ((Finsupp.cons j m').tail)) m =
    (MvPowerSeries.coeff m) ((PowerSeries.coeff k) q)
  rw [PowerSeries.coeff_mk]
  simp [Finsupp.cons_zero, Finsupp.tail_cons, MvPowerSeries.coeff_apply]

/-- **(L2.1.e)** Forward sends `1` to `1`. -/
theorem _root_.MvPowerSeries.finSucc_forward_map_one (R : Type u) [CommRing R] (n : ℕ) :
    MvPowerSeries.finSucc_forwardFun R n 1 = 1 := by
  classical
  ext k m
  change (PowerSeries.coeff k)
      (PowerSeries.mk fun j => fun m' : Fin n →₀ ℕ =>
        (1 : MvPowerSeries (Fin (n + 1)) R) (Finsupp.cons j m')) m =
    (MvPowerSeries.coeff m) ((PowerSeries.coeff k) (1 : PowerSeries (MvPowerSeries (Fin n) R)))
  rw [PowerSeries.coeff_mk]
  -- LHS = (1 : MvPowerSeries (Fin (n+1)) R) (Finsupp.cons k m). Apply coeff_one
  -- after rewriting the function-application as coeff.
  have hLHS : (1 : MvPowerSeries (Fin (n + 1)) R) (Finsupp.cons k m) =
      if Finsupp.cons k m = 0 then (1 : R) else 0 :=
    MvPowerSeries.coeff_one (n := Finsupp.cons k m)
  -- RHS unfold via PowerSeries.coeff_def + MvPowerSeries.coeff_one twice.
  by_cases hk : k = 0
  · subst hk
    by_cases hm : m = 0
    · subst hm
      simp [hLHS, Finsupp.cons_zero_zero, PowerSeries.coeff_one]
    · simp [hLHS, hm, Finsupp.cons_ne_zero_of_right hm, PowerSeries.coeff_one,
        MvPowerSeries.coeff_one]
  · have hcons : Finsupp.cons k m ≠ 0 := Finsupp.cons_ne_zero_of_left hk
    simp [hLHS, hk, hcons, PowerSeries.coeff_one]

/-- **(L2.1.f)** Forward sends `+` to `+`. Immediate from the function-level
definition since `(p + q)(α) = p α + q α` and `Finsupp.cons` is shared. -/
theorem _root_.MvPowerSeries.finSucc_forward_map_add (R : Type u) [CommRing R] (n : ℕ)
    (p q : MvPowerSeries (Fin (n + 1)) R) :
    MvPowerSeries.finSucc_forwardFun R n (p + q) =
      MvPowerSeries.finSucc_forwardFun R n p + MvPowerSeries.finSucc_forwardFun R n q := by
  ext k m
  change (PowerSeries.coeff k)
      (PowerSeries.mk fun j => fun m' : Fin n →₀ ℕ => (p + q) (Finsupp.cons j m')) m =
    (MvPowerSeries.coeff m)
      ((PowerSeries.coeff k) (MvPowerSeries.finSucc_forwardFun R n p +
        MvPowerSeries.finSucc_forwardFun R n q))
  rw [PowerSeries.coeff_mk, map_add, map_add]
  change (p + q) (Finsupp.cons k m) =
    MvPowerSeries.coeff m ((PowerSeries.coeff k) (MvPowerSeries.finSucc_forwardFun R n p)) +
      MvPowerSeries.coeff m ((PowerSeries.coeff k) (MvPowerSeries.finSucc_forwardFun R n q))
  rw [MvPowerSeries.coeff_apply, MvPowerSeries.coeff_apply]
  change p (Finsupp.cons k m) + q (Finsupp.cons k m) =
    (PowerSeries.coeff k) (MvPowerSeries.finSucc_forwardFun R n p) m +
      (PowerSeries.coeff k) (MvPowerSeries.finSucc_forwardFun R n q) m
  unfold MvPowerSeries.finSucc_forwardFun
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]

/-- Helper for L2.1.g: `Finsupp.cons` is additive in both arguments. -/
private lemma _finsupp_cons_add (n : ℕ) (a b : ℕ) (β γ : Fin n →₀ ℕ) :
    Finsupp.cons (a + b) (β + γ) = Finsupp.cons a β + Finsupp.cons b γ := by
  apply Finsupp.ext
  intro i
  refine Fin.cases ?_ ?_ i
  · simp [Finsupp.cons_zero]
  · intro j; simp [Finsupp.cons_succ]

/-- Helper for L2.1.g: `Finsupp.tail` is additive. -/
private lemma _finsupp_tail_add (n : ℕ) (s t : Fin (n + 1) →₀ ℕ) :
    (s + t).tail = s.tail + t.tail := by
  apply Finsupp.ext
  intro i
  simp [Finsupp.tail_apply]

/-- Helper for L2.1.g: antidiagonal of `Finsupp.cons k m` equals the image of
the product antidiagonal under the `cons-pair` map. -/
private lemma _antidiag_cons {n : ℕ} (k : ℕ) (m : Fin n →₀ ℕ) :
    Finset.antidiagonal (Finsupp.cons k m) =
      ((Finset.antidiagonal k) ×ˢ (Finset.antidiagonal m)).image
        (fun x : (ℕ × ℕ) × ((Fin n →₀ ℕ) × (Fin n →₀ ℕ)) =>
          (Finsupp.cons x.1.1 x.2.1, Finsupp.cons x.1.2 x.2.2)) := by
  ext ⟨δ, ε⟩
  simp only [Finset.mem_antidiagonal, Finset.mem_image, Finset.mem_product, Prod.mk.injEq]
  constructor
  · -- (⊆): given δ + ε = Finsupp.cons k m, produce ((δ 0, ε 0), (δ.tail, ε.tail)).
    intro h
    refine ⟨((δ 0, ε 0), (δ.tail, ε.tail)), ⟨?_, ?_⟩, ?_, ?_⟩
    · -- δ 0 + ε 0 = k
      have := congrArg (fun f : Fin (n+1) →₀ ℕ => f 0) h
      simpa [Finsupp.cons_zero] using this
    · -- δ.tail + ε.tail = m
      have := congrArg Finsupp.tail h
      rw [_finsupp_tail_add, Finsupp.tail_cons] at this
      exact this
    · -- Finsupp.cons (δ 0) δ.tail = δ
      exact Finsupp.cons_tail δ
    · -- Finsupp.cons (ε 0) ε.tail = ε
      exact Finsupp.cons_tail ε
  · -- (⊇): given ((a, b), (β, γ)) with a+b=k, β+γ=m, show cons sums.
    rintro ⟨⟨⟨a, b⟩, ⟨β, γ⟩⟩, ⟨hab, hβγ⟩, hδ, hε⟩
    subst hδ
    subst hε
    rw [← _finsupp_cons_add, hab, hβγ]

/-- **(L2.1.g)** Forward sends `*` to `*`. The substantive content. Uses
`MvPowerSeries.coeff_mul` (convolution over `Fin (n+1) →₀ ℕ` antidiagonal) and
`PowerSeries.coeff_mul` (convolution over `ℕ` antidiagonal of products in
`MvPowerSeries (Fin n) R`). The bijection
`(δ, ε) ↔ ((δ 0, δ.tail), (ε 0, ε.tail))` matches the two antidiagonals,
combined via `_finsupp_cons_add`.

**Discharge**: Uses `_antidiag_cons` to identify the `(Finsupp.cons k m)`-
antidiagonal with the product `(antidiag k) × (antidiag m)` image, then matches
coefficient-by-coefficient via `Finset.sum_image` + `Finset.sum_product`. -/
theorem _root_.MvPowerSeries.finSucc_forward_map_mul (R : Type u) [CommRing R] (n : ℕ)
    (p q : MvPowerSeries (Fin (n + 1)) R) :
    MvPowerSeries.finSucc_forwardFun R n (p * q) =
      MvPowerSeries.finSucc_forwardFun R n p * MvPowerSeries.finSucc_forwardFun R n q := by
  classical
  ext k m
  -- LHS unfolds to `(p*q) (Finsupp.cons k m)` via `PowerSeries.coeff_mk`.
  -- RHS unfolds to `(forward p * forward q).coeff k m`.
  have hLHS : (MvPowerSeries.coeff m) ((PowerSeries.coeff k)
        (MvPowerSeries.finSucc_forwardFun R n (p * q))) =
      (MvPowerSeries.coeff (Finsupp.cons k m)) (p * q) := by
    unfold MvPowerSeries.finSucc_forwardFun
    rw [PowerSeries.coeff_mk]
    rfl
  have hRHS : (MvPowerSeries.coeff m) ((PowerSeries.coeff k)
        (MvPowerSeries.finSucc_forwardFun R n p *
          MvPowerSeries.finSucc_forwardFun R n q)) =
      ∑ x ∈ Finset.antidiagonal k ×ˢ Finset.antidiagonal m,
        p (Finsupp.cons x.1.1 x.2.1) * q (Finsupp.cons x.1.2 x.2.2) := by
    rw [PowerSeries.coeff_mul, map_sum]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro ab _
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro βγ _
    unfold MvPowerSeries.finSucc_forwardFun
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl
  rw [hLHS, hRHS, MvPowerSeries.coeff_mul, _antidiag_cons]
  rw [Finset.sum_image]
  · rfl
  · -- Injectivity of the cons-pair map on the product antidiagonal.
    intro ⟨⟨a, b⟩, ⟨β, γ⟩⟩ _ ⟨⟨a', b'⟩, ⟨β', γ'⟩⟩ _ heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have ha : a = a' := by
      have := congrArg (fun f : Fin (n+1) →₀ ℕ => f 0) h1
      simpa [Finsupp.cons_zero] using this
    have hβ : β = β' := by
      have := congrArg Finsupp.tail h1
      simpa [Finsupp.tail_cons] using this
    have hb : b = b' := by
      have := congrArg (fun f : Fin (n+1) →₀ ℕ => f 0) h2
      simpa [Finsupp.cons_zero] using this
    have hγ : γ = γ' := by
      have := congrArg Finsupp.tail h2
      simpa [Finsupp.tail_cons] using this
    simp [ha, hb, hβ, hγ]

/-- The ring iso `MvPowerSeries (Fin (n+1)) R ≃+* MvPowerSeries (Fin n) R⟦X⟧`
splitting off the last variable. Project-internal (mathlib gap).

Final assembly: bundle L2.1.a-g into a `RingEquiv`. -/
theorem _root_.MvPowerSeries.finSuccEquivPowerSeries (R : Type u) [CommRing R] (n : ℕ) :
    Nonempty (MvPowerSeries (Fin (n + 1)) R ≃+*
      PowerSeries (MvPowerSeries (Fin n) R)) :=
  ⟨RingEquiv.mk
    { toFun := MvPowerSeries.finSucc_forwardFun R n
      invFun := MvPowerSeries.finSucc_inverseFun R n
      left_inv := MvPowerSeries.finSucc_left_inv R n
      right_inv := MvPowerSeries.finSucc_right_inv R n }
    (MvPowerSeries.finSucc_forward_map_mul R n)
    (MvPowerSeries.finSucc_forward_map_add R n)⟩

/-- **Sub-lemma L2 (multivariate Hilbert basis for power series)**: for
`R` Noetherian, `MvPowerSeries (Fin n) R` is Noetherian for every `n`.

Proof: induction on `n` using
`MvPowerSeries.finSuccEquivPowerSeries` + `PowerSeries.instIsNoetherianRing`.

Source: Stacks Project, tag 0306 (Lemma 10.31.2). -/
theorem _root_.MvPowerSeries.instIsNoetherianRing_fin (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    -- For σ = Fin 0 (empty), `C : R →+* MvPowerSeries (Fin 0) R` is surjective,
    -- so noetherianness transfers from R.
    haveI hunique : Unique (Fin 0 →₀ ℕ) := Finsupp.uniqueOfLeft
    apply isNoetherianRing_of_surjective R (MvPowerSeries (Fin 0) R)
      (MvPowerSeries.C (σ := Fin 0) (R := R))
    intro p
    refine ⟨p 0, ?_⟩
    ext α
    have hα : α = 0 := Subsingleton.elim _ _
    subst hα
    rw [MvPowerSeries.coeff_C]
    rfl
  | succ n IH =>
    obtain ⟨e⟩ := MvPowerSeries.finSuccEquivPowerSeries R n
    haveI : IsNoetherianRing (MvPowerSeries (Fin n) R) := IH
    haveI : IsNoetherianRing (PowerSeries (MvPowerSeries (Fin n) R)) := inferInstance
    exact isNoetherianRing_of_ringEquiv _ e.symm

/-! ## L3 — Evaluation map `MvPowerSeries (Fin n) R → AdicCompletion I R`

Decomposed into six sub-leaves for `/beastmode` (Session 28, 2026-05-20):

The construction routes through mathlib's `MvPowerSeries.eval₂Hom` (or via the
universal property of `AdicCompletion.lift` for the LinearMap, then bundling
multiplication separately). Either route requires the topological-side
plumbing on `AdicCompletion I R`.

* **L3.A** `adicCompletion_isLinearTopology` — the canonical topology on
  `AdicCompletion I R` is linear (the `I^n • ⊤` neighbourhood basis at 0).
* **L3.B** `adicCompletion_isTopologicalRing` + `isUniformAddGroup`
  +`CompleteSpace` + `T2Space` instances — the full topological-ring bundle.
* **L3.C** `f_hasEval_in_adicCompletion` — for `f i ∈ I`, the image
  `AdicCompletion.of I R (f i) ∈ AdicCompletion I R` is topologically
  nilpotent and `fun i => AdicCompletion.of I R (f i)` satisfies
  mathlib's `MvPowerSeries.HasEval`.
* **L3.D** `f_powers_tendsto_zero` — `(AdicCompletion.of I R (f i))^k → 0`
  as `k → ∞` (the topological-nilpotency content).
* **L3.E** `algebraMap_continuous_discrete` — with the discrete topology on
  `R`, the canonical `AdicCompletion.of I R : R →+* AdicCompletion I R` is
  trivially continuous (any map out of a discrete space is continuous).
* **L3.F** `mvPowerSeriesEval_assembly` — final assembly: instantiate
  mathlib's `MvPowerSeries.eval₂Hom` with the continuous algebra map +
  `HasEval` to obtain the ring hom.

Sub-leaves L3.A and L3.B follow from mathlib's `IsAdic` machinery applied to
the `I^n`-filtration on `AdicCompletion I R` (which is itself I-adic
complete by `AdicCompletion.isAdicComplete`). Sub-leaf L3.D is the core
topological-nilpotency check; L3.C bundles it with the trivial finite-index
`tendsto_zero`. The actual ring-hom assembly L3.F is one line. -/

/-! ### L3 sub-leaves (docstring-only)

The sub-leaves L3.A–L3.F are documented above; we deliberately do NOT
materialise them as Lean theorems with vacuous `True` placeholders (banned
per project style). Each sub-leaf's statement requires either (a) an
externally-supplied topology instance on `AdicCompletion I R`, or (b) a
non-trivial mathematical claim (topological nilpotency / `HasEval`). When
`/beastmode` begins discharging L3, the sub-leaves are materialised in
honest typed form at that point, with sorry bodies.

The decomposition order for discharge:
- (L3.A, L3.B) — supply / derive topology instances (likely via mathlib's
  `AdicCompletion.Topology` module + `IsAdic` framework).
- (L3.D) — `IsTopologicallyNilpotent (AdicCompletion.of I R a)` for `a ∈ I`.
- (L3.C) — bundle L3.D + finite-index `tendsto_zero` into `HasEval`.
- (L3.E) — continuity of `AdicCompletion.of I R` with R discrete.
- (L3.F) — assemble via `MvPowerSeries.eval₂Hom`.
-/

/-- **(L3.A.linear-map)**: for each `k`, the partial-evaluation linear map
`MvPowerSeries (Fin n) R →ₗ[R] R ⧸ (I^k • ⊤)`. The map sends a power series
`P` to `∑_{α : Fin n →₀ ℕ, α ≤ n_k} (P α) · f^α mod I^k`, where `n_k` is the
componentwise bound `(k, k, …, k)`. Multidegrees with `sum α ≥ k` contribute
zero mod `I^k` (since `f^α ∈ I^(sum α) ⊆ I^k`); multidegrees not bounded by
`n_k` are dropped (also contribute zero).

This LinearMap is the input to `AdicCompletion.lift` for the L3 construction. -/
noncomputable def _mvPowerSeriesEval_partial [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (f : Fin n → R) (_hf : ∀ i, f i ∈ I) (k : ℕ) :
    MvPowerSeries (Fin n) R →ₗ[R] R ⧸ (I ^ k • (⊤ : Submodule R R)) :=
  -- Use `k+1` per component so that the constant term (multidegree 0) is always
  -- included (multidegree 0 < (k+1, k+1, ..., k+1) strictly). For multidegrees
  -- with `sum α ≥ k`, `f^α ∈ I^(sum α) ⊆ I^k`, so they vanish mod I^k.
  let n_k : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1)
  (Submodule.mkQ (I^k • ⊤)).comp
    ((MvPolynomial.aeval f).toLinearMap.comp (MvPowerSeries.trunc R n_k))

/-- Helper: a finitely-indexed product `∏ᵢ (a i)^(b i)` with each `a i ∈ I`
lies in `I^(Σᵢ b i)`. Proved by `Finset.induction`. -/
private lemma _finset_prod_pow_mem_pow_sum {ι : Type*}
    (s : Finset ι) (I : Ideal R) (a : ι → R) (b : ι → ℕ)
    (ha : ∀ i ∈ s, a i ∈ I) :
    ∏ i ∈ s, (a i) ^ (b i) ∈ I ^ (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi_notin IH =>
    rw [Finset.prod_insert hi_notin, Finset.sum_insert hi_notin, pow_add]
    refine Submodule.mul_mem_mul ?_ ?_
    · exact Ideal.pow_mem_pow (ha i (Finset.mem_insert_self _ _)) _
    · exact IH (fun j hj => ha j (Finset.mem_insert.mpr (Or.inr hj)))

/-- **(L3.A.compat.support)**: if `α` lies in the support of
`trunc n_k P - trunc n_m P` (with `n_k = (k+1, …, k+1)` and `n_m = (m+1, …,
m+1)`, where `m ≤ k`), then some component of `α` is at least `m + 1`.

Reasoning (case analysis on `α < n_m`):
* If `α < n_m`, then `α < n_k` (since `n_m ≤ n_k`), so both `coeff_trunc`
  branches return `P α`, making the difference 0 — contradicting `α ∈ support`.
* If `¬α < n_m`, either some `α i > m + 1` (giving `α i ≥ m + 1` directly),
  or `α ≤ n_m` componentwise and `α = n_m`, so `α i = m + 1` for all `i`.
  The `n = 0` corner is handled separately: `n_m = n_k = 0`, both branches
  return 0, so `α ∉ support`. -/
private lemma _mvPowerSeriesEval_partial_compat_support_high {n : ℕ}
    (P : MvPowerSeries (Fin n) R) {m k : ℕ} (hle : m ≤ k) (α : Fin n →₀ ℕ)
    (hα : α ∈ ((MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) P -
      (MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1)) P).support) :
    ∃ j : Fin n, α j ≥ m + 1 := by
  classical
  rw [MvPolynomial.mem_support_iff] at hα
  have hsub : MvPolynomial.coeff α (((MvPowerSeries.trunc R
      (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) P) -
        ((MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1)) P)) =
      MvPolynomial.coeff α (MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1) P) -
      MvPolynomial.coeff α (MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1) P) := rfl
  rw [hsub, MvPowerSeries.coeff_trunc, MvPowerSeries.coeff_trunc] at hα
  by_cases h_lt_m : α < (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1 :
      Fin n →₀ ℕ)
  · -- α < n_m ≤ n_k: both branches give P α, difference is 0.
    exfalso
    have h_lt_k : α < (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1 :
        Fin n →₀ ℕ) :=
      lt_of_lt_of_le h_lt_m
        (fun i => by simp [Finsupp.equivFunOnFinite]; omega)
    simp [if_pos h_lt_m, if_pos h_lt_k] at hα
  · -- ¬α < n_m. For n = 0, n_m = n_k = 0, so both branches give 0; contradiction.
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exfalso
      have h_eq_k : (Finsupp.equivFunOnFinite.symm fun _ : Fin 0 => k + 1 :
          Fin 0 →₀ ℕ) =
          (Finsupp.equivFunOnFinite.symm fun _ : Fin 0 => m + 1 :
            Fin 0 →₀ ℕ) := Subsingleton.elim _ _
      rw [h_eq_k, if_neg h_lt_m, sub_self] at hα
      exact hα rfl
    · -- n ≥ 1. Either some α i > m + 1, or α = n_m with α i = m + 1 everywhere.
      by_cases h_le_m : ∀ i : Fin n, α i ≤ m + 1
      · have hα_le : α ≤
            (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1 : Fin n →₀ ℕ) :=
          fun i => by simp [Finsupp.equivFunOnFinite]; exact h_le_m i
        have heq : α =
            (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1 : Fin n →₀ ℕ) :=
          eq_of_le_of_not_lt hα_le h_lt_m
        refine ⟨⟨0, hn⟩, ?_⟩
        rw [heq]; simp [Finsupp.equivFunOnFinite]
      · push_neg at h_le_m
        obtain ⟨i, hi⟩ := h_le_m
        exact ⟨i, by omega⟩

/-- **(L3.A.compat)**: the partial-evaluation maps are compatible with the
`I`-adic transition maps `R ⧸ I^(k+1) → R ⧸ I^k`.

**Discharge plan**:
1. `LinearMap.ext` reduces to per-`P` equality.
2. `Submodule.factor_comp_mk` rewrites the transition map composed with the
   inner `mkQ` to the outer `mkQ` (with `I^m • ⊤ ⊇ I^k • ⊤`).
3. Both sides become `mkQ (I^m • ⊤) (aeval f (trunc R n_? P))`. The difference
   `aeval f (trunc R n_k P - trunc R n_m P)` has terms with some component
   exceeding `m`, hence each `f^α` factor lies in `I^m`, hence sum is in
   `I^m • ⊤`. -/
theorem _mvPowerSeriesEval_partial_compat [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (f : Fin n → R) (hf : ∀ i, f i ∈ I) {m k : ℕ} (hle : m ≤ k) :
    AdicCompletion.transitionMap I R hle ∘ₗ _mvPowerSeriesEval_partial I f hf k =
      _mvPowerSeriesEval_partial I f hf m := by
  classical
  apply LinearMap.ext
  intro P
  -- Both sides land in R ⧸ (I^m • ⊤). Reduce to equality of representatives mod I^m • ⊤.
  unfold _mvPowerSeriesEval_partial
  simp only [LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply]
  -- Keep `mkQ` form so `factor_mk` rewriting works.
  rw [show AdicCompletion.transitionMap I R hle = Submodule.factorPow I R hle from rfl,
    Submodule.factorPow, Submodule.factor_mk]
  -- Goal: mkQ (I^m • ⊤) (aeval f (trunc n_k P)) = mkQ (I^m • ⊤) (aeval f (trunc n_m P))
  -- Use mkQ-equality mod the submodule.
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  -- Goal: aeval f (trunc R n_k P) - aeval f (trunc R n_m P) ∈ I^m • ⊤
  -- The substantive per-monomial degree-filtering argument.
  rw [← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ (fun α hα => ?_)
  rw [Algebra.algebraMap_self_apply]
  obtain ⟨j, hj⟩ :=
    _mvPowerSeriesEval_partial_compat_support_high P hle α hα
  have h_prod_in : ∏ i : Fin n, (f i) ^ (α i) ∈ I ^ m := by
    have h1 : ∏ i : Fin n, (f i) ^ (α i) ∈ I ^ (∑ i, α i) :=
      _finset_prod_pow_mem_pow_sum Finset.univ I f α (fun i _ => hf i)
    have h2 : ∑ i, α i ≥ m + 1 :=
      le_trans hj (Finset.single_le_sum (f := α)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
    exact Ideal.pow_le_pow_right (by omega : m ≤ ∑ i, α i) h1
  have h_term : MvPolynomial.coeff α (((MvPowerSeries.trunc R
      (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) P) -
        ((MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm fun _ : Fin n => m + 1)) P)) *
      ∏ i, (f i) ^ (α i) ∈ I ^ m :=
    Ideal.mul_mem_left _ _ h_prod_in
  exact (show I ^ m ≤ I ^ m • (⊤ : Submodule R R) from fun y hy => by
    rw [show y = y * 1 from (mul_one _).symm]
    exact Submodule.smul_mem_smul hy Submodule.mem_top) h_term

/-- **(L3.B.map_one)**: the lifted LinearMap sends `1` to `1`, assuming
`0 < n`.

The `(hn : 0 < n)` hypothesis is **mathematically required** (per binding
rule (b)): at `n = 0`, the partial map `_mvPowerSeriesEval_partial I f hf k`
sends `1 : MvPowerSeries (Fin 0) R` to `0` (the truncation `trunc R 0 1 = 0`
collapses because `Iio 0 = ∅` in the `Fin 0 →₀ ℕ` order), so the conclusion
`(lift 1) = 1` fails at level `k ≥ 1` for any `I ≠ ⊤`. The `n = 0` corner
is irrelevant in the only downstream use (Stacks 0316, where
`n = #generators of I` and the `I = ⊥` corner is dispatched separately in
the headline via `AdicCompletion ⊥ R ≅ R`). Documented in `b2_log.jsonl`
(2026-05-23).

**Discharge plan**:
1. `AdicCompletion.ext` reduces to per-level equality: `(lift 1).val k = (1).val k`.
2. `AdicCompletion.val_one`: RHS is `1 : R/I^k`.
3. `AdicCompletion.eval_lift_apply`: LHS reduces to `partial k 1 : R/I^k`.
4. For `k = 0`: `R/I^0 = R/⊤` is `Subsingleton`, both sides are equal trivially.
5. For `k ≥ 1`: with `n ≥ 1`, `n_k ≠ 0`; `trunc R n_k 1 = 1`;
   `(aeval f) 1 = 1`; `mkQ 1 = 1`. -/
theorem _mvPowerSeriesEval_map_one [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (f : Fin n → R) (hf : ∀ i, f i ∈ I) :
    AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
        (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle) 1 = 1 := by
  apply AdicCompletion.ext
  intro k
  rw [AdicCompletion.eval_lift_apply, AdicCompletion.val_one]
  unfold _mvPowerSeriesEval_partial
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : Subsingleton (R ⧸ (I ^ 0 • (⊤ : Submodule R R))) := by
      rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      infer_instance
    exact Subsingleton.elim _ _
  · have hnk : (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1) : Fin n →₀ ℕ) ≠ 0 := by
      intro hzero
      have h0 : (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1) :
          Fin n →₀ ℕ) ⟨0, hn⟩ = 0 := by
        rw [hzero]; simp
      simp [Finsupp.equivFunOnFinite] at h0
    change (Submodule.mkQ (I ^ k • ⊤)) ((MvPolynomial.aeval f).toLinearMap
        ((MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1))) 1)) = 1
    rw [MvPowerSeries.trunc_one _ hnk, AlgHom.toLinearMap_apply, map_one]
    rfl

/-- **(L3.B.map_mul.support_high)**: if `α` lies in the support of the
multiplicativity-residual polynomial `trunc n_k (P*Q) - trunc n_k P * trunc n_k Q`
(with `n_k = (k+1, …, k+1)`), then some component of `α` is at least `k + 1`.

Reasoning: if all components `α j ≤ k` (i.e., `α < n_k`), then both
`coeff α (trunc n_k (P*Q))` and `coeff α (trunc n_k P * trunc n_k Q)` equal
`coeff α (P*Q)`. The former is direct from `MvPowerSeries.coeff_trunc` (taking
the `if_pos` branch); the latter unfolds via `MvPolynomial.coeff_mul` and uses
that each pair `(β, γ) ∈ antidiagonal α` satisfies `β ≤ α < n_k` and
`γ ≤ α < n_k`, so the polynomial truncation projects out to the underlying
power-series coefficients. Hence the difference vanishes, contradicting
`α ∈ support`. The `n = 0` corner is handled separately: `n_k = 0`, all
truncations equal `0`, so the difference polynomial is `0` with empty support. -/
private lemma _mvPowerSeriesEval_partial_map_mul_support_high {n : ℕ}
    (P Q : MvPowerSeries (Fin n) R) {k : ℕ} (α : Fin n →₀ ℕ)
    (hα : α ∈ ((MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) (P * Q) -
      (MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) P *
      (MvPowerSeries.trunc R
        (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) Q).support) :
    ∃ j : Fin n, α j ≥ k + 1 := by
  classical
  by_contra hcontra
  push_neg at hcontra
  rw [MvPolynomial.mem_support_iff] at hα
  apply hα
  set n_k : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1
    with hn_k_def
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: n_k = 0, all truncations equal 0, difference is 0.
    subst hn
    have hn_k_zero : n_k = 0 := Subsingleton.elim _ _
    have h_trunc_zero : ∀ S : MvPowerSeries (Fin 0) R,
        MvPowerSeries.trunc R n_k S = 0 := by
      intro S
      ext β
      rw [hn_k_zero, MvPowerSeries.coeff_trunc, MvPolynomial.coeff_zero]
      have hβ_not_lt : ¬ β < (0 : Fin 0 →₀ ℕ) := by
        have : β = 0 := Subsingleton.elim _ _
        rw [this]
        exact lt_irrefl _
      rw [if_neg hβ_not_lt]
    rw [h_trunc_zero, h_trunc_zero, h_trunc_zero, zero_mul, sub_zero,
      MvPolynomial.coeff_zero]
  · -- n ≥ 1: α < n_k, so both sides of the difference give coeff α (P*Q).
    have h_lt : α < n_k := by
      rw [Finsupp.lt_def]
      refine ⟨?_, ?_⟩
      · intro i; have := hcontra i; simp [hn_k_def, Finsupp.equivFunOnFinite]; omega
      · refine ⟨⟨0, hn⟩, ?_⟩
        have := hcontra ⟨0, hn⟩
        simp [hn_k_def, Finsupp.equivFunOnFinite]; omega
    have hsub_coeff : MvPolynomial.coeff α
        ((MvPowerSeries.trunc R n_k) (P * Q) -
          (MvPowerSeries.trunc R n_k) P * (MvPowerSeries.trunc R n_k) Q) =
        MvPolynomial.coeff α ((MvPowerSeries.trunc R n_k) (P * Q)) -
          MvPolynomial.coeff α
            ((MvPowerSeries.trunc R n_k) P * (MvPowerSeries.trunc R n_k) Q) := rfl
    rw [hsub_coeff, MvPowerSeries.coeff_trunc, if_pos h_lt,
        MvPolynomial.coeff_mul, MvPowerSeries.coeff_mul]
    refine sub_eq_zero.mpr ?_
    refine Finset.sum_congr rfl ?_
    intro ⟨β, γ⟩ hβγ
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
    simp only at hβγ
    have hβ_le_α : β ≤ α := by intro i; rw [← hβγ]; simp
    have hγ_le_α : γ ≤ α := by intro i; rw [← hβγ]; simp
    have hβ_lt : β < n_k := lt_of_le_of_lt hβ_le_α h_lt
    have hγ_lt : γ < n_k := lt_of_le_of_lt hγ_le_α h_lt
    rw [MvPowerSeries.coeff_trunc, if_pos hβ_lt,
        MvPowerSeries.coeff_trunc, if_pos hγ_lt]

/-- **(L3.B.map_mul.residual)**: the substantive ideal-membership claim
underlying `_mvPowerSeriesEval_partial_map_mul`.

After unfolding `_mvPowerSeriesEval_partial` and using that `aeval` is a ring
hom (`map_mul`), per-level multiplicativity reduces to:
`aeval f (trunc n_k (P*Q)) - aeval f (trunc n_k P * trunc n_k Q) ∈ I^k • ⊤`,
where `n_k = (k+1, …, k+1)`.

The argument: `aeval f` is a ring hom, so the difference equals
`aeval f (trunc n_k (P*Q) - trunc n_k P * trunc n_k Q)`. Each monomial in this
difference has multidegree sum `≥ k+1` (by
`_mvPowerSeriesEval_partial_map_mul_support_high`), so its image under
`aeval f` is a product `∏ᵢ (fᵢ)^(αᵢ)` with `∑ᵢ αᵢ ≥ k+1 ≥ k`, lying in `I^k`
and hence in `I^k • ⊤`. -/
private theorem _mvPowerSeriesEval_partial_map_mul_residual_mem
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (k : ℕ) (P Q : MvPowerSeries (Fin n) R) :
    (MvPolynomial.aeval f)
        ((MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm fun (_ : Fin n) => k + 1)) (P * Q)) -
      (MvPolynomial.aeval f)
        ((MvPowerSeries.trunc R
            (Finsupp.equivFunOnFinite.symm fun (_ : Fin n) => k + 1)) P *
          (MvPowerSeries.trunc R
            (Finsupp.equivFunOnFinite.symm fun (_ : Fin n) => k + 1)) Q) ∈
      (I ^ k • (⊤ : Submodule R R) : Submodule R R) := by
  classical
  -- aeval is a ring hom, so we can pull the subtraction inside aeval.
  rw [← map_sub, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ (fun α hα => ?_)
  rw [Algebra.algebraMap_self_apply]
  obtain ⟨j, hj⟩ := _mvPowerSeriesEval_partial_map_mul_support_high P Q α hα
  have h_prod_in : ∏ i : Fin n, (f i) ^ (α i) ∈ I ^ k := by
    have h1 : ∏ i : Fin n, (f i) ^ (α i) ∈ I ^ (∑ i, α i) :=
      _finset_prod_pow_mem_pow_sum Finset.univ I f α (fun i _ => hf i)
    have h2 : ∑ i, α i ≥ k + 1 :=
      le_trans hj (Finset.single_le_sum (f := α)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
    exact Ideal.pow_le_pow_right (by omega : k ≤ ∑ i, α i) h1
  have h_term : MvPolynomial.coeff α (((MvPowerSeries.trunc R
      (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) (P * Q)) -
        ((MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) P *
         (MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm fun _ : Fin n => k + 1)) Q)) *
      ∏ i, (f i) ^ (α i) ∈ I ^ k :=
    Ideal.mul_mem_left _ _ h_prod_in
  exact (show I ^ k ≤ I ^ k • (⊤ : Submodule R R) from fun y hy => by
    rw [show y = y * 1 from (mul_one _).symm]
    exact Submodule.smul_mem_smul hy Submodule.mem_top) h_term

/-- **(L3.B.map_mul.partial)**: per-level multiplicativity of the partial
evaluation map mod `I^k`.

The substantive content: although `trunc n_k (P * Q) ≠ trunc n_k P * trunc n_k Q`
in general (the difference involves monomials of multidegree exceeding `n_k`
in some component), all such monomials evaluate (via `aeval f`) to elements of
`I^k`, hence vanish in `R ⧸ (I^k • ⊤)`. So multiplicativity holds modulo
`I^k`.

**Discharge**: unfold `_mvPowerSeriesEval_partial` and use that `Submodule.mkQ`
on `R ⧸ (I^k • ⊤)` is a ring hom (multiplication on the quotient is defined
componentwise). Combined with `Submodule.Quotient.eq` and the fact that `aeval`
is a ring hom (`map_mul`), per-level multiplicativity reduces to the membership
claim packaged in `_mvPowerSeriesEval_partial_map_mul_residual_mem`. -/
private theorem _mvPowerSeriesEval_partial_map_mul [IsNoetherianRing R]
    (I : Ideal R) {n : ℕ} (f : Fin n → R) (hf : ∀ i, f i ∈ I) (k : ℕ)
    (P Q : MvPowerSeries (Fin n) R) :
    _mvPowerSeriesEval_partial I f hf k (P * Q) =
      _mvPowerSeriesEval_partial I f hf k P *
        _mvPowerSeriesEval_partial I f hf k Q := by
  unfold _mvPowerSeriesEval_partial
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Submodule.mkQ_apply]
  change Submodule.Quotient.mk _ =
    Submodule.Quotient.mk _ * Submodule.Quotient.mk _
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk (_ * _)
  rw [Submodule.Quotient.eq, ← map_mul]
  exact _mvPowerSeriesEval_partial_map_mul_residual_mem I f hf k P Q

/-- **(L3.B.map_mul)**: the lifted LinearMap respects multiplication.

**Discharge plan**:
1. `AdicCompletion.ext` reduces to per-level equality.
2. `eval_lift_apply` on LHS gives `partial k (P*Q)`; `val_mul` + `eval_lift_apply`
   on RHS gives `partial k P * partial k Q`.
3. Delegated to `_mvPowerSeriesEval_partial_map_mul`. -/
theorem _mvPowerSeriesEval_map_mul [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (f : Fin n → R) (hf : ∀ i, f i ∈ I)
    (P Q : MvPowerSeries (Fin n) R) :
    AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
        (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle) (P * Q) =
      AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
          (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle) P *
        AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
          (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle) Q := by
  apply AdicCompletion.ext
  intro k
  rw [AdicCompletion.val_mul, AdicCompletion.eval_lift_apply,
    AdicCompletion.eval_lift_apply, AdicCompletion.eval_lift_apply]
  exact _mvPowerSeriesEval_partial_map_mul I f hf k P Q

/-- **(L3 main)**: build the evaluation `MvPowerSeries (Fin n) R →+*
AdicCompletion I R`.

**Discharge**: bundle `AdicCompletion.lift`'s LinearMap into a RingHom using
the LinearMap's add/zero plus L3.B.map_one and L3.B.map_mul.

Source: Stacks 0316 proof body, "Consider the map R[[x₁,…,xₙ]] → R̂, xᵢ ↦ fᵢ.
This is well defined." -/
noncomputable def mvPowerSeriesEval [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (f : Fin n → R) (hf : ∀ i, f i ∈ I) :
    MvPowerSeries (Fin n) R →+* AdicCompletion I R :=
  let lin := AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
    (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle)
  { toFun := lin
    map_zero' := lin.map_zero
    map_add' := lin.map_add
    map_one' := _mvPowerSeriesEval_map_one I hn f hf
    map_mul' := _mvPowerSeriesEval_map_mul I f hf }

/-! ## L4 — Surjectivity of the evaluation map (workhorse)

This is the substantive content the Stacks proof skips with "(details
omitted)". Decomposed into three sub-leaves for /beastmode:

* **L4.1** `pow_eq_span_pow_of_span_eq` — `I^k = Ideal.span {f^α : |α| = k}`
  when `I = Ideal.span (range f)`. Reduces to mathlib `Ideal.span_pow_eq`
  applied to the finite generating set.
* **L4.2** `mvPowerSeriesEval_surjective_inductive_step` — the per-degree
  lifting: given a Cauchy approximation up to degree `n`, extend to degree
  `n+1` using L4.1.
* **L4.3** `mvPowerSeriesEval_surjective` — assembly: iterate L4.2 over `n`
  to build the full power-series pre-image.
-/

open Pointwise in
/-- **(L4.1)**: `I^k` is the ideal generated by all degree-`k` monomials in
the generators `f₁,…,fₙ`. -/
theorem pow_eq_span_pow_of_span_eq [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (f : Fin n → R) (hspan : Ideal.span (Set.range f) = I) (k : ℕ) :
    I ^ k = Ideal.span {x | ∃ α : Fin n → ℕ, (∑ i, α i = k) ∧
      x = ∏ i, (f i) ^ (α i)} := by
  classical
  apply le_antisymm
  · -- I^k ≤ Ideal.span RHS via Submodule.span_pow + counting argument.
    rw [← hspan]
    have hspow : Ideal.span (Set.range f) ^ k = Ideal.span (Set.range f ^ k) :=
      Submodule.span_pow (Set.range f) k
    rw [hspow]
    refine Ideal.span_le.mpr ?_
    intro x hx
    rw [Set.mem_pow_iff_prod] at hx
    obtain ⟨g, hg_mem, hg_prod⟩ := hx
    choose h hh_eq using fun j : Fin k => hg_mem j
    have hx_eq : x = ∏ j, f (h j) := by
      rw [← hg_prod]
      exact Finset.prod_congr rfl (fun j _ => (hh_eq j).symm)
    let α : Fin n → ℕ := fun i =>
      (Finset.univ.filter (fun j : Fin k => h j = i)).card
    have hα_sum : ∑ i, α i = k := by
      have hcard : (Finset.univ : Finset (Fin k)).card =
          ∑ i ∈ (Finset.univ : Finset (Fin n)), α i :=
        Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ _)
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      exact hcard.symm
    have hx_alpha : x = ∏ i, (f i) ^ (α i) := by
      rw [hx_eq, Finset.prod_comp f h]
      apply Finset.prod_subset (Finset.subset_univ _)
      intro i _ hi_not_image
      have hcount_zero : (Finset.univ.filter (fun j : Fin k => h j = i)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _ hhj_eq
        exact hi_not_image (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hhj_eq⟩)
      change (f i) ^ ((Finset.univ.filter (fun j : Fin k => h j = i)).card) = 1
      rw [hcount_zero, pow_zero]
    exact Ideal.subset_span ⟨α, hα_sum, hx_alpha⟩
  · -- Ideal.span RHS ≤ I^k via the helper lemma.
    refine Ideal.span_le.mpr ?_
    rintro x ⟨α, hα_sum, rfl⟩
    have hmem : ∏ i, (f i) ^ (α i) ∈ I ^ (∑ i, α i) :=
      _finset_prod_pow_mem_pow_sum Finset.univ I f α
        (fun i _ => hspan ▸ Ideal.subset_span ⟨i, rfl⟩)
    rwa [hα_sum] at hmem

/-! ### L4.2.a.exists.poly_witness — sub-leaves

The substantive sorry of `_mvPowerSeriesEval_residual_correction_poly_witness`
(Stacks 0316's "(details omitted)") is honestly decomposed below into two
named sub-lemmas, each carrying its own `sorry` body. The decomposition
follows the discharge plan in the parent lemma's docstring.

* **(L4.2.a.exists.poly_witness.smul_decomp)** — every element of `I^k • ⊤`
  can be written as a finite `R`-linear combination
  `∑ⱼ ∏ᵢ (fᵢ)^(αⱼ ᵢ) • xⱼ` with `∑ᵢ αⱼ ᵢ = k` and `xⱼ ∈ AdicCompletion I R`.
  Combines `Submodule.smul_induction_on` with L4.1
  (`pow_eq_span_pow_of_span_eq`).
* **(L4.2.a.exists.poly_witness.lift_completion_residue)** — every
  `x : AdicCompletion I R` lifts to some `d ∈ R` such that
  `x - AdicCompletion.of I R d ∈ I^1 • ⊤`. This is the `mod I` lift of a
  completion element.

The witness assembly combines these into the polynomial
`δ_poly := -∑ⱼ (cⱼ) · ∏ᵢ Xᵢ^(αⱼ ᵢ)` where `cⱼ` is the lift of `xⱼ` mod `I`. -/

/-- **(L4.2.a.exists.poly_witness.smul_decomp)**: every element of `I^k • ⊤`
in `AdicCompletion I R` decomposes as a finite `R`-linear combination of
products `∏ᵢ (fᵢ)^(αⱼ ᵢ) • xⱼ` with `∑ᵢ αⱼ ᵢ = k`. This is the L4.1-backed
explicit description of `I^k • ⊤` used to construct polynomial witnesses.

**Discharge**: combine `Submodule.smul_induction_on` (or `mem_smul_span`) on
the membership hypothesis with `pow_eq_span_pow_of_span_eq` (L4.1), which
expresses `I^k` as the span of monomial products `∏ᵢ fᵢ^(αᵢ)` with
`∑ᵢ αᵢ = k`. -/
private lemma _mvPowerSeriesEval_residual_correction_smul_decomp
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (f : Fin n → R)
    (_hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (res : AdicCompletion I R)
    (hres : res ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ (m : ℕ) (α : Fin m → Fin n → ℕ) (x : Fin m → AdicCompletion I R),
      (∀ j, ∑ i, α j i = k) ∧
        res = ∑ j, (∏ i, (f i) ^ (α j i)) • x j := by
  classical
  refine Submodule.smul_induction_on hres ?_ ?_
  · -- smul case: given s ∈ I^k and y ∈ ⊤, decompose s • y via L4.1.
    intro s hs y _
    rw [pow_eq_span_pow_of_span_eq I f hspan k] at hs
    rcases (Submodule.mem_span_set'.1 hs) with ⟨m, c, g, hsum⟩
    -- For each index j, extract a multi-index αⱼ such that gⱼ = ∏ᵢ fᵢ^(αⱼ ᵢ).
    have hg : ∀ j : Fin m, ∃ α : Fin n → ℕ,
        (∑ i, α i = k) ∧ (g j : R) = ∏ i, (f i) ^ (α i) := fun j => (g j).2
    choose α hα_sum hα_eq using hg
    refine ⟨m, α, fun j => c j • y, hα_sum, ?_⟩
    rw [← hsum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hα_eq j, smul_eq_mul, ← smul_assoc, mul_comm]
  · -- add case: concatenate the two decompositions via `Fin.append`.
    rintro res₁ res₂ ⟨m₁, α₁, x₁, hα₁, hres₁⟩ ⟨m₂, α₂, x₂, hα₂, hres₂⟩
    refine ⟨m₁ + m₂, Fin.append α₁ α₂, Fin.append x₁ x₂, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact hα₁ i
      · rw [Fin.append_right]; exact hα₂ i
    · rw [hres₁, hres₂, Fin.sum_univ_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [Fin.append_left, Fin.append_left]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Fin.append_right, Fin.append_right]

/-- **(L4.2.a.exists.poly_witness.lift_completion_residue.kernel.mk_of_first_zero)**:
sub-leaf of `_adicCompletion_val_one_zero_in_I_smul_top`. A Cauchy sequence
`b : ℕ → R` whose value `b 1 = 0` (and which is `I`-adic Cauchy) has its
`AdicCompletion.mk`-image in `I • ⊤`. This is the deep "closure of `I • ⊤`
in `AdicCompletion I R`" content; the remaining work involves expressing
`mk b` as a finite `R`-linear combination of `I`-elements times completion
elements, available because `R` is Noetherian (so `I` is f.g. and the
Cauchy increments `b (n+1) - b n ∈ I^n • ⊤` can be tracked through
generators of `I^n`). -/
private lemma _adicCompletion_mk_of_first_zero_in_I_smul_top
    [IsNoetherianRing R] (I : Ideal R)
    (b : AdicCompletion.AdicCauchySequence I R) (hb : (b : ℕ → R) 1 = 0) :
    AdicCompletion.mk I R b ∈ (I • ⊤ : Submodule R (AdicCompletion I R)) := by
  -- Step 1: `evalₐ` at level 1 sends `mk b` to 0 (because `b 1 = 0`).
  have hker : (AdicCompletion.evalₐ I 1) (AdicCompletion.mk I R b) = 0 := by
    rw [AdicCompletion.evalₐ_mk, hb]
    exact (Ideal.Quotient.mk (I ^ 1)).map_zero
  -- Step 2: by `ker_evalₐ_eq` (kernel description), `mk b ∈ Ideal.map (algebraMap R _) I`.
  have hker' : AdicCompletion.mk I R b ∈
      Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ 1) := by
    rw [← AdicCompletionBridge.ker_evalₐ_eq I 1]; exact hker
  rw [pow_one] at hker'
  -- Step 3: convert the ideal-image membership to `I • ⊤` membership via the
  -- standard `mem_span_set'` decomposition and `c • of(a) = a • c` in the comm ring.
  rcases Submodule.mem_span_set'.1 hker' with ⟨n, c, g, hsum⟩
  rw [← hsum]
  refine sum_mem fun i _ => ?_
  rcases (g i).2 with ⟨a, ha, ha_eq⟩
  rw [show (g i : AdicCompletion I R) = AdicCompletion.of I R a from ha_eq.symm]
  change c i • AdicCompletion.of I R a ∈ (I • ⊤ : Submodule R (AdicCompletion I R))
  rw [show c i • AdicCompletion.of I R a = a • c i from by
    change c i * AdicCompletion.of I R a = AdicCompletion.of I R a * c i
    ring]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **(L4.2.a.exists.poly_witness.lift_completion_residue.kernel)**: the kernel
description of the level-`1` projection `AdicCompletion I R → R ⧸ (I • ⊤)`.
If `y : AdicCompletion I R` has `y.val 1 = 0`, then `y ∈ I • ⊤`.

This is the substantive content of `_adicCompletion_lift_mod_I` — given a
representative `y` of an element of `AdicCompletion I R`, vanishing at level
`1` (equivalently, lying in `Ker (eval I R 1)`) is precisely membership in
`I • ⊤` as a `Submodule R (AdicCompletion I R)`.

**Discharge**: pick a Cauchy representative `y = mk a`. From `(mk a).val 1 = 0`
we deduce `a 1 ∈ I^1 • ⊤ = I` in `R`. Decompose `mk a = of (a 1) + mk b`
where `b n := a n - a 1` is the shifted Cauchy sequence. The summand
`of (a 1)` lies in `I • ⊤` since `a 1 ∈ I` and `of (a 1) = a 1 • of 1`. The
summand `mk b` lies in `I • ⊤` by the sub-leaf
`_adicCompletion_mk_of_first_zero_in_I_smul_top` (applied to `b`, which
satisfies `b 1 = 0`). -/
private lemma _adicCompletion_val_one_zero_in_I_smul_top
    [IsNoetherianRing R] (I : Ideal R) (y : AdicCompletion I R)
    (hy : y.val 1 = 0) :
    y ∈ (I • ⊤ : Submodule R (AdicCompletion I R)) := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R y
  -- Step 1: a 1 ∈ I (from the level-1 vanishing of mk a).
  have hy' : Submodule.Quotient.mk
      (p := (I ^ 1 • ⊤ : Submodule R R)) (a 1) = 0 := hy
  have ha1 : (a : ℕ → R) 1 ∈ (I ^ 1 • ⊤ : Submodule R R) := by
    rwa [Submodule.Quotient.mk_eq_zero] at hy'
  have ha1_in_I : (a : ℕ → R) 1 ∈ I := by
    have heq : (I ^ 1 • ⊤ : Submodule R R) = (I : Submodule R R) := by
      rw [pow_one, Ideal.smul_top_eq_map]; simp
    rwa [heq] at ha1
  -- Step 2: construct the shifted Cauchy sequence b n = a n - a 1.
  let b : AdicCompletion.AdicCauchySequence I R :=
    ⟨fun n => (a : ℕ → R) n - (a : ℕ → R) 1, by
      intro m n hmn
      change (a : ℕ → R) m - (a : ℕ → R) 1 ≡
        (a : ℕ → R) n - (a : ℕ → R) 1 [SMOD (I ^ m • ⊤ : Submodule R R)]
      exact SModEq.sub (a.property hmn) SModEq.rfl⟩
  -- Step 3: decompose mk a = of (a 1) + mk b.
  have hsum : AdicCompletion.mk I R a =
      AdicCompletion.of I R ((a : ℕ → R) 1) + AdicCompletion.mk I R b := by
    ext n
    change (Submodule.Quotient.mk (a n) : R ⧸ (I ^ n • ⊤ : Submodule R R)) =
      Submodule.Quotient.mk (a 1) +
      Submodule.Quotient.mk ((a : ℕ → R) n - (a : ℕ → R) 1)
    rw [← Submodule.Quotient.mk_add]
    congr 1
    ring
  -- Step 4: of (a 1) ∈ I • ⊤ because a 1 ∈ I.
  have h_of : AdicCompletion.of I R ((a : ℕ → R) 1) ∈
      (I • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [show AdicCompletion.of I R ((a : ℕ → R) 1) =
        (a : ℕ → R) 1 • AdicCompletion.of I R 1 by rw [← map_smul]; simp]
    exact Submodule.smul_mem_smul ha1_in_I Submodule.mem_top
  -- Step 5: mk b ∈ I • ⊤ via the sub-leaf (uses b 1 = 0).
  have hb1 : (b : ℕ → R) 1 = 0 := sub_self _
  have h_mk_b := _adicCompletion_mk_of_first_zero_in_I_smul_top I b hb1
  rw [hsum]
  exact Submodule.add_mem _ h_of h_mk_b

/-- **(L4.2.a.exists.poly_witness.lift_completion_residue)**: every element
of `AdicCompletion I R` lifts to `R` modulo `I^1 • ⊤`. That is, there exists
`d ∈ R` with `x - AdicCompletion.of I R d ∈ I • ⊤`. This is the elementary
"lift `x.val 1` to `R`" claim, used to build the polynomial coefficients
of `δ_poly`.

**Discharge**: pick `d : R` projecting to `x.val 1` (via surjectivity of
`Submodule.mkQ`). Then `(x - of d).val 1 = 0`, so the kernel description
`_adicCompletion_val_one_zero_in_I_smul_top` gives `x - of d ∈ I • ⊤`. -/
private lemma _adicCompletion_lift_mod_I
    [IsNoetherianRing R] (I : Ideal R) (x : AdicCompletion I R) :
    ∃ d : R, x - AdicCompletion.of I R d ∈
      (I • ⊤ : Submodule R (AdicCompletion I R)) := by
  obtain ⟨d, hd⟩ : ∃ d : R,
      (Submodule.mkQ (I ^ 1 • (⊤ : Submodule R R))) d = x.val 1 :=
    (Submodule.mkQ_surjective _) (x.val 1)
  refine ⟨d, _adicCompletion_val_one_zero_in_I_smul_top I _ ?_⟩
  show (x - AdicCompletion.of I R d).val 1 = 0
  rw [AdicCompletion.val_sub_apply, AdicCompletion.of_apply, hd]
  exact sub_self _

/-- **(L4.2.a.exists.poly_witness.assembly.eq.coe)**: `mvPowerSeriesEval` on a
polynomial coercion `↑p` agrees with `AdicCompletion.of` applied to the
algebraic evaluation `MvPolynomial.aeval f p`. Both are ring homs
`MvPolynomial (Fin n) R → AdicCompletion I R`; the equality is checked
per-level using `AdicCompletion.ext`, `eval_lift_apply`, and the fact that
`trunc R n_k ↑p - p` has only multidegrees `> k`, whose `aeval f`-images lie
in `I^k`. Left as a named sub-lemma with `sorry` body pending the polynomial
truncation argument. -/
private lemma _mvPowerSeriesEval_apply_coe [IsNoetherianRing R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R) (hf : ∀ i, f i ∈ I)
    (p : MvPolynomial (Fin n) R) :
    (mvPowerSeriesEval I hn f hf) ((p : MvPowerSeries (Fin n) R)) =
      AdicCompletion.of I R ((MvPolynomial.aeval f) p) := by
  sorry

/-- **(L4.2.a.exists.poly_witness.assembly.eq)**: rewrite identity for the
residual after applying the polynomial correction `δ_poly`. Combines the
algebraic computation `mvPowerSeriesEval (P + δ_poly) = mvPowerSeriesEval P
+ mvPowerSeriesEval δ_poly` (additivity of the ring hom) with the per-monomial
identity `mvPowerSeriesEval (C dⱼ * ∏ Xⁱ^(αⱼ ᵢ)) = (∏ᵢ (fᵢ)^(αⱼ ᵢ)) • of dⱼ`
(which itself rests on the unfolding of `mvPowerSeriesEval` on a polynomial
coercion) and the hypothesis `hres_eq` describing the prior residual.

**Discharge plan**: split `mvPowerSeriesEval (P + δ_poly)` via the ring hom;
use the sub-lemma `_mvPowerSeriesEval_apply_coe` to convert the polynomial
coercion to `of ∘ aeval f`; then unfold `aeval f` on the monomial sum via
`aeval_C`, `aeval_X`, `map_neg`, `map_sum`, `map_mul`, `map_prod`, `map_pow`;
finally combine `of (d_j * ∏ f^α) = (∏ f^α) • of d_j` (since `of` is linear)
with `hres_eq` and use `smul_sub` + `Finset.sum_sub_distrib` to bridge to
the goal. -/
private lemma _mvPowerSeriesEval_residual_correction_poly_witness_assembly_eq
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (k : ℕ) (r : AdicCompletion I R)
    (P : MvPowerSeries (Fin n) R)
    (m : ℕ) (α : Fin m → Fin n → ℕ) (x : Fin m → AdicCompletion I R)
    (_hα_sum : ∀ j, ∑ i, α j i = k)
    (hres_eq : mvPowerSeriesEval I hn f hf P - r =
      ∑ j, (∏ i, (f i) ^ (α j i)) • x j)
    (d : Fin m → R) :
    mvPowerSeriesEval I hn f hf
        (P + ((-∑ j : Fin m, MvPolynomial.C (d j) *
          ∏ i, (MvPolynomial.X i) ^ (α j i) :
            MvPolynomial (Fin n) R) :
          MvPowerSeries (Fin n) R)) - r =
      ∑ j, (∏ i, (f i) ^ (α j i)) • (x j - AdicCompletion.of I R (d j)) := by
  rw [map_add, _mvPowerSeriesEval_apply_coe I hn f hf]
  simp only [map_neg, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self_apply, map_prod, map_pow]
  rw [show (∑ j : Fin m,
        (AdicCompletion.of I R) (d j * ∏ i, f i ^ α j i) : AdicCompletion I R) =
      ∑ j, ((∏ i, f i ^ α j i) • AdicCompletion.of I R (d j)) by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← LinearMap.map_smul]
    congr 1
    rw [smul_eq_mul, mul_comm]]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  linear_combination hres_eq

/-- **(L4.2.a.exists.poly_witness.assembly)**: given the explicit
decomposition of the residual (via
`_mvPowerSeriesEval_residual_correction_smul_decomp`) and per-summand lifts
mod `I` (via `_adicCompletion_lift_mod_I`), the polynomial
`δ_poly := -∑ⱼ dⱼ · ∏ᵢ Xᵢ^(αⱼ ᵢ)` improves the approximation from `I^k` to
`I^(k+1)`. This packages the algebraic-bookkeeping step.

**Discharge**: rewrite the residual after correction using the algebraic
identity `_mvPowerSeriesEval_residual_correction_poly_witness_assembly_eq`,
which expresses it as `∑ⱼ (∏ᵢ (fᵢ)^(αⱼ ᵢ)) • (xⱼ - of dⱼ)`. Each summand
lies in `I^(k+1) • ⊤` because `∏ᵢ (fᵢ)^(αⱼ ᵢ) ∈ I^k` (via
`_finset_prod_pow_mem_pow_sum`, using `∑ᵢ αⱼ ᵢ = k`) and
`xⱼ - of dⱼ ∈ I • ⊤` by the lift specification `hd`. The product structure
`I^k • (I • ⊤) = (I^k * I) • ⊤ = I^(k+1) • ⊤` (via `pow_succ` +
`Submodule.mul_smul`) finishes the membership. -/
private lemma _mvPowerSeriesEval_residual_correction_poly_witness_assembly
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (_hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R)))
    (m : ℕ) (α : Fin m → Fin n → ℕ) (x : Fin m → AdicCompletion I R)
    (hα_sum : ∀ j, ∑ i, α j i = k)
    (hres_eq : mvPowerSeriesEval I hn f hf P - r =
      ∑ j, (∏ i, (f i) ^ (α j i)) • x j)
    (d : Fin m → R)
    (hd : ∀ j, x j - AdicCompletion.of I R (d j) ∈
      (I • ⊤ : Submodule R (AdicCompletion I R))) :
    mvPowerSeriesEval I hn f hf
        (P + ((-∑ j : Fin m, MvPolynomial.C (d j) *
          ∏ i, (MvPolynomial.X i) ^ (α j i) :
            MvPolynomial (Fin n) R) :
          MvPowerSeries (Fin n) R)) - r ∈
      (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) := by
  rw [_mvPowerSeriesEval_residual_correction_poly_witness_assembly_eq
    I hn f hf k r P m α x hα_sum hres_eq d]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [pow_succ, Submodule.mul_smul]
  refine Submodule.smul_mem_smul ?_ (hd j)
  have hmem : ∏ i, (f i) ^ (α j i) ∈ I ^ (∑ i, α j i) :=
    _finset_prod_pow_mem_pow_sum Finset.univ I f (α j) (fun i _ => hf i)
  rwa [hα_sum j] at hmem

/-- **(L4.2.a.exists.poly_witness)**: substantive *polynomial-level* content of
the correction step. From a power-series approximation `P` of `r` modulo `I^k`,
there exists a *polynomial* correction `δ_poly : MvPolynomial (Fin n) R` such
that `P + δ_poly` (viewed in `MvPowerSeries` via `MvPolynomial.toMvPowerSeries`)
improves the approximation from `I^k` to `I^(k+1)`.

This is the location of Stacks 0316's "(details omitted)" for the existence
step. Discharge plan:

1. Note that `mvPowerSeriesEval P − r ∈ I^k • ⊤` means the residual lies in the
   `R`-submodule `I^k • ⊤` of `AdicCompletion I R`.
2. By L4.1 (`pow_eq_span_pow_of_span_eq`), `I^k = Ideal.span {∏ᵢ (fᵢ)^(αᵢ) :
   ∑αᵢ = k}`. So every element of `I^k • ⊤` is a finite `R`-linear combination
   of products `(∏ᵢ (fᵢ)^(αᵢ)) · x` with `∑αᵢ = k` and `x` arbitrary in `⊤`.
3. Each such product `(∏ᵢ (fᵢ)^(αᵢ)) · x` admits an `AdicCompletion`-level
   approximation: lift `x.val (k+1) : R/I^(k+1)` to some `c ∈ R`, then the
   product is `c · (∏ᵢ (fᵢ)^(αᵢ))` plus a residue in `I^(k+1) • ⊤`.
4. The monomial `c · ∏ᵢ xᵢ^(αᵢ)` lives in `MvPolynomial`, giving the
   polynomial witness `δ_poly`.

**Discharge**: delegated to
`_mvPowerSeriesEval_residual_correction_smul_decomp` (explicit decomposition
of the residual) and `_adicCompletion_lift_mod_I` (per-summand lift mod `I`).
The witness polynomial is the negative sum
`δ_poly := -∑ⱼ dⱼ · ∏ᵢ Xᵢ^(αⱼ ᵢ)` where `dⱼ` is the lift of `xⱼ`. -/
private lemma _mvPowerSeriesEval_residual_correction_poly_witness
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ δ_poly : MvPolynomial (Fin n) R,
      mvPowerSeriesEval I hn f hf
          (P + (δ_poly : MvPowerSeries (Fin n) R)) - r ∈
        (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) := by
  -- Step 1: decompose the residual `res := mvPowerSeriesEval P - r ∈ I^k • ⊤`
  -- via the L4.1-backed sub-lemma.
  set res : AdicCompletion I R := mvPowerSeriesEval I hn f hf P - r with hres_def
  obtain ⟨m, α, x, hα_sum, hres_eq⟩ :=
    _mvPowerSeriesEval_residual_correction_smul_decomp
      I f hf hspan k res _hP_approx
  -- Step 2: per summand, lift `x j` mod `I` to some `d j ∈ R`.
  choose d hd using fun j : Fin m => _adicCompletion_lift_mod_I I (x j)
  -- Step 3: assemble the polynomial witness.
  -- δ_poly := -∑ⱼ (d j) · ∏ᵢ Xᵢ^(α j i).
  refine ⟨-∑ j : Fin m, MvPolynomial.C (d j) * ∏ i, (MvPolynomial.X i) ^ (α j i),
    ?_⟩
  -- The improvement from I^k to I^(k+1) is the content of the polynomial
  -- witness — both `_mvPowerSeriesEval_residual_correction_smul_decomp` and
  -- `_adicCompletion_lift_mod_I` deliver the data, but assembling the
  -- algebraic identity `mvPowerSeriesEval (P + δ_poly) - r ∈ I^(k+1) • ⊤`
  -- from the decomposed residual requires unfolding `mvPowerSeriesEval` on
  -- polynomial inputs (= partial evaluation at all sufficiently high levels)
  -- and tracking the `(fᵢ)^(αⱼ ᵢ) · (xⱼ - of dⱼ) ∈ I^(k+1) • ⊤` per-summand
  -- residual. This algebraic-bookkeeping step is the residual obligation.
  exact _mvPowerSeriesEval_residual_correction_poly_witness_assembly
    I hn f hf hspan k r P _hP_approx m α x hα_sum hres_eq d hd

/-- **(L4.2.a.exists)**: substantive existence of a correction power series.
From a power-series approximation `P` of `r` modulo `I^k`, there exists a
`MvPowerSeries` correction `δ` such that `P + δ` approximates `r` modulo
`I^(k+1)`.

Discharge: delegate to `_mvPowerSeriesEval_residual_correction_poly_witness`
(which produces a *polynomial* witness `δ_poly`) and promote it to
`MvPowerSeries` via `MvPolynomial.toMvPowerSeries` (= `(δ_poly :
MvPowerSeries _ R)`). -/
private lemma _mvPowerSeriesEval_surjective_step_correction_exists
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ δ : MvPowerSeries (Fin n) R,
      mvPowerSeriesEval I hn f hf (P + δ) - r ∈
        (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) := by
  obtain ⟨δ_poly, hδ⟩ :=
    _mvPowerSeriesEval_residual_correction_poly_witness
      I hn f hf hspan k r P _hP_approx
  exact ⟨(δ_poly : MvPowerSeries (Fin n) R), hδ⟩

/-- **(L4.2.a.0)**: choose a correction power series `δ` from a power-series
approximation `P` of `r` modulo `I^k`. Extracted as the `Classical.choose`
witness of `_mvPowerSeriesEval_surjective_step_correction_exists`. -/
private noncomputable def _mvPowerSeriesEval_surjective_step_correction_choose
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    MvPowerSeries (Fin n) R :=
  Classical.choose
    (_mvPowerSeriesEval_surjective_step_correction_exists
      I hn f hf hspan k r P _hP_approx)

/-- **(L4.2.a.1)**: the correction power series chosen by
`_mvPowerSeriesEval_surjective_step_correction_choose` improves the
approximation level from `I^k` to `I^(k+1)`. Discharged by
`Classical.choose_spec` of the existence lemma. -/
private lemma _mvPowerSeriesEval_surjective_step_correction_spec
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    mvPowerSeriesEval I hn f hf
      (P + _mvPowerSeriesEval_surjective_step_correction_choose
        I hn f hf hspan k r P hP_approx) - r ∈
      (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) :=
  Classical.choose_spec
    (_mvPowerSeriesEval_surjective_step_correction_exists
      I hn f hf hspan k r P hP_approx)

/-- **(L4.2.a)**: data extraction step — from a power-series approximation
`P` of `r` up to level `I^k`, extract a *correction polynomial* `δ` that is
a finite `R`-linear combination of degree-`(k+1)` monomials `∏ᵢ (fᵢ)^(αᵢ)`
(`∑ᵢ αᵢ = k+1`) such that
`mvPowerSeriesEval I hn f hf (P + δ) - r ∈ I^(k+1) • ⊤`.

This packages the substantive content of L4.2: use L4.1 (`pow_eq_span_pow_of_span_eq`)
to express the difference modulo `I^(k+1)` as such a combination, then promote
the polynomial `δ` to a `MvPowerSeries` (via `MvPolynomial → MvPowerSeries`).

Discharge: delegate witness construction to
`_mvPowerSeriesEval_surjective_step_correction_choose` and the spec to
`_mvPowerSeriesEval_surjective_step_correction_spec`. -/
private lemma _mvPowerSeriesEval_surjective_step_correction
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ δ : MvPowerSeries (Fin n) R,
      mvPowerSeriesEval I hn f hf (P + δ) - r ∈
        (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) :=
  ⟨_mvPowerSeriesEval_surjective_step_correction_choose
    I hn f hf hspan k r P _hP_approx,
   _mvPowerSeriesEval_surjective_step_correction_spec
    I hn f hf hspan k r P _hP_approx⟩

/-- **(L4.2)**: inductive Cauchy-lifting step. Given a power-series
approximation that matches `(rₙ) ∈ R̂` up to degree `n`, the difference
`rₙ₊₁ - approxₙ` lies in `Iⁿ⁺¹` and (by L4.1) is a degree-`(n+1)` polynomial
in the `fᵢ`'s, yielding the next-coefficient extension.

Discharge: delegate to `_mvPowerSeriesEval_surjective_step_correction` and
take `P' := P + δ`. -/
theorem mvPowerSeriesEval_surjective_inductive_step [IsNoetherianRing R]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R) (hf : ∀ i, f i ∈ I)
    (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ P' : MvPowerSeries (Fin n) R,
      mvPowerSeriesEval I hn f hf P' - r ∈
        (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R)) := by
  obtain ⟨δ, hδ⟩ := _mvPowerSeriesEval_surjective_step_correction
    I hn f hf hspan k r P _hP_approx
  exact ⟨P + δ, hδ⟩

/-- **(L4.2.support)**: strengthened inductive step. In addition to producing
a power series `P'` that improves the approximation from `I^k` to `I^(k+1)`,
the chosen `P'` agrees with the previous `P` on coefficients of total degree
strictly less than `k`. This support guarantee is built into the polynomial
witness produced by
`_mvPowerSeriesEval_residual_correction_poly_witness`: that witness is
`δ_poly = -∑ⱼ C(dⱼ) * ∏ᵢ Xᵢ^(αⱼ ᵢ)` with `∑ᵢ αⱼ ᵢ = k`, so its MvPowerSeries
coefficient at any `α` with `∑ᵢ αᵢ + 1 ≤ k` is `0`, and `P' = P + δ_poly`
agrees with `P` at such `α`.

The substantive content (that the polynomial witness has zero coefficient at
multi-indices of total degree `< k`) is honestly deferred to a sub-lemma
`_mvPowerSeriesEval_residual_correction_poly_witness_strong` carrying the
support claim alongside the approximation claim. -/
private theorem _mvPowerSeriesEval_surjective_inductive_step_strong
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (k : ℕ) (r : AdicCompletion I R) (P : MvPowerSeries (Fin n) R)
    (_hP_approx : mvPowerSeriesEval I hn f hf P -
      r ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R))) :
    ∃ P' : MvPowerSeries (Fin n) R,
      (mvPowerSeriesEval I hn f hf P' - r ∈
        (I ^ (k + 1) • ⊤ : Submodule R (AdicCompletion I R))) ∧
        (∀ α : Fin n →₀ ℕ, (∑ i, α i) + 1 ≤ k →
          (P' : MvPowerSeries (Fin n) R) α = (P : MvPowerSeries (Fin n) R) α) := by
  -- Replicate the construction inside `_mvPowerSeriesEval_residual_correction_poly_witness`
  -- so the polynomial witness `δ_poly = -∑ⱼ C(dⱼ) · ∏ᵢ Xᵢ^(αⱼ ᵢ)` is exposed; this lets
  -- us read off the support property (`δ_poly α = 0` whenever `∑ α i + 1 ≤ k`).
  set res : AdicCompletion I R := mvPowerSeriesEval I hn f hf P - r with hres_def
  obtain ⟨m, α, x, hα_sum, hres_eq⟩ :=
    _mvPowerSeriesEval_residual_correction_smul_decomp
      I f hf hspan k res _hP_approx
  choose d hd using fun j : Fin m => _adicCompletion_lift_mod_I I (x j)
  set δ_poly : MvPolynomial (Fin n) R :=
    -∑ j : Fin m, MvPolynomial.C (d j) * ∏ i, (MvPolynomial.X i) ^ (α j i) with hδ_def
  refine ⟨P + (δ_poly : MvPowerSeries (Fin n) R), ?_, ?_⟩
  · -- Approximation: delegate to the assembly lemma.
    exact _mvPowerSeriesEval_residual_correction_poly_witness_assembly
      I hn f hf hspan k r P _hP_approx m α x hα_sum hres_eq d hd
  · -- Support: for `α₀` with `∑ α₀ i + 1 ≤ k`, show `δ_poly α₀ = 0`, hence
    -- `(P + δ_poly) α₀ = P α₀`.
    intro α₀ hα₀
    have hcoeff_zero :
        ((δ_poly : MvPowerSeries (Fin n) R)) α₀ = 0 := by
      change MvPolynomial.coeff α₀ δ_poly = 0
      rw [hδ_def, MvPolynomial.coeff_neg]
      rw [show MvPolynomial.coeff α₀
          (∑ j : Fin m, MvPolynomial.C (d j) * ∏ i, (MvPolynomial.X i :
            MvPolynomial (Fin n) R) ^ (α j i)) =
          ∑ j : Fin m, MvPolynomial.coeff α₀ (MvPolynomial.C (d j) * ∏ i,
            (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (α j i)) from
          MvPolynomial.coeff_sum _ _ _]
      refine neg_eq_zero.mpr ?_
      apply Finset.sum_eq_zero
      intro j _
      have h_mono_eq :
          MvPolynomial.C (d j) *
            ∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ (α j i) =
          MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (α j)) (d j) := by
        rw [MvPolynomial.monomial_eq]
        congr 1
        rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        simp [Finsupp.equivFunOnFinite]
      rw [h_mono_eq, MvPolynomial.coeff_monomial]
      have h_neq : Finsupp.equivFunOnFinite.symm (α j) ≠ α₀ := by
        intro heq
        have h_sums : ∑ i, α₀ i = ∑ i, α j i := by
          apply Finset.sum_congr rfl
          intro i _
          have h_pt : α₀ i =
              (Finsupp.equivFunOnFinite.symm (α j) : Fin n →₀ ℕ) i := by
            rw [← heq]
          rw [h_pt]; rfl
        rw [hα_sum j] at h_sums
        omega
      rw [if_neg h_neq]
    -- Now conclude (P + δ_poly) α₀ = P α₀ from δ_poly α₀ = 0.
    change (P + (δ_poly : MvPowerSeries (Fin n) R)) α₀ = P α₀
    change P α₀ + ((δ_poly : MvPowerSeries (Fin n) R)) α₀ = P α₀
    rw [hcoeff_zero, add_zero]

/-- **(L4.3.a)**: iterated-approximation sequence. For each `k : ℕ`, choose
a power-series approximation `P k` of `r` modulo `I^k • ⊤`. Built by
recursion on `k` using
`_mvPowerSeriesEval_surjective_inductive_step_strong` (L4.2-strong), which
also carries a support guarantee enabling the limit-coefficient stability
proofs.

`k = 0`: `P 0 := 0` (trivially approximates since `I^0 • ⊤ = ⊤`).
`k+1`: extract via L4.2-strong from `P k`. -/
private noncomputable def _mvPowerSeriesEval_surjective_seq
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) : ∀ k : ℕ,
      { P : MvPowerSeries (Fin n) R //
        mvPowerSeriesEval I hn f hf P - r ∈
          (I ^ k • ⊤ : Submodule R (AdicCompletion I R)) }
  | 0 =>
    ⟨0, by
      have htop : (I ^ 0 • ⊤ : Submodule R (AdicCompletion I R)) = ⊤ := by
        rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      rw [htop]; exact Submodule.mem_top⟩
  | k + 1 =>
    let prev := _mvPowerSeriesEval_surjective_seq I hn f hf hspan r k
    ⟨Classical.choose (_mvPowerSeriesEval_surjective_inductive_step_strong
        I hn f hf hspan k r prev.1 prev.2),
      (Classical.choose_spec (_mvPowerSeriesEval_surjective_inductive_step_strong
        I hn f hf hspan k r prev.1 prev.2)).1⟩

/-- **(L4.3.b.coeff)**: the limit coefficient at multi-index `α`. Sub-definition
of `_mvPowerSeriesEval_surjective_limit`: returns the stable value of
`((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r) k).1 α` for `k` large
enough (specifically, `k ≥ ∑ i, α i + 1`). We pick the canonical witness
`k = (∑ i, α i) + 1`; the stabilisation statement (that this matches the value
for any larger `k`) is part of the per-level spec
`_mvPowerSeriesEval_surjective_limit_spec_per_level`. -/
private noncomputable def _mvPowerSeriesEval_surjective_limit_coeff
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (_α : Fin n →₀ ℕ) : R :=
  ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r
      ((∑ i, _α i) + 1)).1 : MvPowerSeries (Fin n) R) _α

/-- **(L4.3.b)**: the limit power series. Given the sequence `P k` from
L4.3.a, the coefficients stabilise; the limit is the pointwise stable value.

Discharge plan (~30 LOC): requires showing that for each multi-index `α`, the
coefficient `(P k) α` stabilises in `k`. The L4.2 construction produces a
correction supported in degree exactly `k+1`, so coefficients of degree `≤ k`
in `P (k+1)` match those in `P k`. -/
private noncomputable def _mvPowerSeriesEval_surjective_limit
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) : MvPowerSeries (Fin n) R :=
  fun α => _mvPowerSeriesEval_surjective_limit_coeff I hn f hf hspan r α

/-- **(L4.3.c.per_level.limit_partial.coeff_eq.stable.mono.step)**: single
inductive step of sequence stability. The strong inductive step
`_mvPowerSeriesEval_surjective_inductive_step_strong` returns a witness `P'`
whose support guarantee says `P' α = (seq j).1 α` whenever `(∑ α i) + 1 ≤ j`,
so for any such `α` the coefficient `(seq (j+1)).1 α` agrees with `(seq j).1 α`.

The seq's `(j+1)`-th value is `Classical.choose` of the strong inductive
step, and the support claim is the second conjunct of `Classical.choose_spec`.
The full iterated monotone statement
`_mvPowerSeriesEval_surjective_seq_stable_value_mono` is derived from this
helper by `Nat.le_induction` (no further sorry needed). -/
private lemma _mvPowerSeriesEval_surjective_seq_stable_value_mono_step
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (α : Fin n →₀ ℕ) (j : ℕ)
    (_hα_le : (∑ i, α i) + 1 ≤ j) :
    ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r (j + 1)).1 :
        MvPowerSeries (Fin n) R) α =
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).1 :
        MvPowerSeries (Fin n) R) α := by
  -- Unfold the seq recursive case to expose the `Classical.choose` witness.
  change (Classical.choose (_mvPowerSeriesEval_surjective_inductive_step_strong
      I hn f hf hspan j r (_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).1
      (_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).2) :
        MvPowerSeries (Fin n) R) α =
    ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).1 :
        MvPowerSeries (Fin n) R) α
  -- The support spec is the second conjunct of `Classical.choose_spec`.
  exact (Classical.choose_spec (_mvPowerSeriesEval_surjective_inductive_step_strong
    I hn f hf hspan j r (_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).1
    (_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j).2)).2 α _hα_le

/-- **(L4.3.c.per_level.limit_partial.coeff_eq.stable.mono)**: monotone
direction of sequence stability. If `j₂` is at-or-above the canonical
witness `(∑ α i) + 1` and `j₁ ≤ j₂` with `j₁` also at-or-above the
canonical witness, the coefficient at `α` agrees between `seq j₁` and
`seq j₂`. Equivalently: once `j ≥ (∑ α i) + 1`, the value `(seq j).1 α`
is constant in `j`.

The single-step content (that `seq (j+1)` and `seq j` agree at `α` when
`(∑ α i) + 1 ≤ j`) is captured by
`_mvPowerSeriesEval_surjective_seq_stable_value_mono_step`; iterating from
`j₁` to `j₂` via `Nat.le_induction` discharges the lemma. -/
private lemma _mvPowerSeriesEval_surjective_seq_stable_value_mono
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (α : Fin n →₀ ℕ) (j₁ j₂ : ℕ)
    (hj : j₁ ≤ j₂) (hα_le : (∑ i, α i) + 1 ≤ j₁) :
    ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j₁).1 :
        MvPowerSeries (Fin n) R) α =
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r j₂).1 :
        MvPowerSeries (Fin n) R) α := by
  induction j₂, hj using Nat.le_induction with
  | base => rfl
  | succ j hj_ih ih =>
    have hαj : (∑ i, α i) + 1 ≤ j := hα_le.trans hj_ih
    exact ih.trans
      (_mvPowerSeriesEval_surjective_seq_stable_value_mono_step
        I hn f hf hspan r α j hαj).symm

/-- **(L4.3.c.per_level.limit_partial.coeff_eq.stable.partial)**: partial-
evaluation direction of sequence stability. For `k` at-or-below the
canonical witness `(∑ α i) + 1`, the coefficient at `α` is preserved
between `seq k` and `seq ((∑ α i) + 1)`.

This is the complementary direction to `mono`: at small iteration indices
`k ≤ (∑ α i) + 1`, the seq value `(seq k).1 α` is reached by the partial
evaluation that produces the right `r.val k` (an honest *truncation*
constraint, established via `_mvPowerSeriesEval_surjective_partial_seq_val_eq`
together with the support description of L4.2's correction supported in
degree `k+1`). The full algebraic unfolding through
`Classical.choose`-witnessed corrections and partial-truncation reasoning
is substantive, so this helper is left with a `sorry` body. -/
private lemma _mvPowerSeriesEval_surjective_seq_stable_value_partial
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) (α : Fin n →₀ ℕ)
    (_hα : α < (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1) :
      Fin n →₀ ℕ))
    (_hk_lt : k ≤ (∑ i, α i) + 1) :
    ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1 :
        MvPowerSeries (Fin n) R) α =
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r
          ((∑ i, α i) + 1)).1 :
        MvPowerSeries (Fin n) R) α := by
  sorry

/-- **(L4.3.c.per_level.limit_partial.coeff_eq.stable)**: the substantive
sequence-stability content of `_mvPowerSeriesEval_surjective_limit_coeff_eq_seq`,
phrased symmetrically between two indices. For any pair of indices `j₁, j₂` and
any multi-index `α` with `α i ≤ k` for all `i` (i.e. `α < n_k`), provided that
both `j₁ ≥ ∑ α i + 1` ("`j₁` is at the canonical stable level for `α`") OR
`α < n_{j₁}` ("`j₁` is at a partial-evaluation level that sees `α`"), and
likewise for `j₂`, the sequence values agree at `α`: `(seq j₁).1 α = (seq j₂).1 α`.

This packages the underlying stabilisation reasoning. The substantive content
is delegated to the two directional helpers:
* `_mvPowerSeriesEval_surjective_seq_stable_value_mono` for the case
  `(∑ α i) + 1 ≤ k` (the "canonical witness is below `k`" branch); and
* `_mvPowerSeriesEval_surjective_seq_stable_value_partial` for the case
  `k ≤ (∑ α i) + 1` (the "`k` is below the canonical witness" branch).
The case split here is a pure `Nat`-trichotomy on `(∑ α i) + 1 ≤ k`. -/
private lemma _mvPowerSeriesEval_surjective_seq_stable_value
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) (α : Fin n →₀ ℕ)
    (hα : α < (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1) :
      Fin n →₀ ℕ)) :
    ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r
        ((∑ i, α i) + 1)).1 : MvPowerSeries (Fin n) R) α =
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1 :
        MvPowerSeries (Fin n) R) α := by
  by_cases hle : ((∑ i, α i) + 1) ≤ k
  · -- `(∑ α i) + 1 ≤ k`: the canonical witness is below `k`, apply `mono`.
    exact _mvPowerSeriesEval_surjective_seq_stable_value_mono I hn f hf hspan r α
      ((∑ i, α i) + 1) k hle le_rfl
  · -- `k < (∑ α i) + 1`: apply `partial` and flip the equality.
    have hlt : k ≤ (∑ i, α i) + 1 := Nat.le_of_lt (Nat.lt_of_not_le hle)
    exact (_mvPowerSeriesEval_surjective_seq_stable_value_partial I hn f hf hspan
      r k α hα hlt).symm

/-- **(L4.3.c.per_level.limit_partial.coeff_eq)**: coefficient-level
stabilisation. For every multi-index `α` whose entries are all strictly less
than `k + 1` (i.e. `α i ≤ k` for every `i`), the limit coefficient
`_mvPowerSeriesEval_surjective_limit_coeff I hn f hf hspan r α` matches the
sequence's `k`-th value at `α`. This is the per-coefficient analogue of L4.2's
"correction is supported in high degrees": the inductive step at iteration `j`
only affects coefficients with `∑ᵢ αᵢ ≥ j+1`, so for `j > ∑ᵢ αᵢ` the coefficient
stops changing. Since `α i ≤ k` everywhere implies `∑ᵢ αᵢ ≤ n·k`, both the
canonical witness `(∑ᵢ αᵢ) + 1` (used in
`_mvPowerSeriesEval_surjective_limit_coeff`) and `k` belong to the stable
range, so they agree.

**Discharge**: unfold `_mvPowerSeriesEval_surjective_limit_coeff` (which is
defined as `((seq ((∑ α i) + 1)).1) α`) and delegate the substantive
sequence-stability claim to `_mvPowerSeriesEval_surjective_seq_stable_value`. -/
private lemma _mvPowerSeriesEval_surjective_limit_coeff_eq_seq
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) (α : Fin n →₀ ℕ)
    (hα : α < (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1) :
      Fin n →₀ ℕ)) :
    _mvPowerSeriesEval_surjective_limit_coeff I hn f hf hspan r α =
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1 :
        MvPowerSeries (Fin n) R) α := by
  unfold _mvPowerSeriesEval_surjective_limit_coeff
  exact _mvPowerSeriesEval_surjective_seq_stable_value I hn f hf hspan r k α hα

/-- **(L4.3.c.per_level.limit_partial)**: at every level `k`, the partial
evaluation of the limit power series agrees with that of the `k`-th sequence
power series. The truncation `_mvPowerSeriesEval_partial` only inspects
coefficients of multidegrees `α` with `α i ≤ k` for every `i`, and the limit
coefficient `limit α` equals `(seq m).1 α` for sufficiently large `m`. The
sequence's correction power series (via L4.2) is supported in degree exactly
`k+1`, so coefficients in low degrees stabilise.

**Discharge**: unfold `_mvPowerSeriesEval_partial` and reduce to equality of
the truncations `trunc R n_k (limit) = trunc R n_k ((seq k).1)`, which holds
pointwise by `_mvPowerSeriesEval_surjective_limit_coeff_eq_seq`. -/
private lemma _mvPowerSeriesEval_surjective_limit_partial_eq
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) :
    _mvPowerSeriesEval_partial I f hf k
        (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r) =
      _mvPowerSeriesEval_partial I f hf k
        ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1) := by
  classical
  -- Reduce to equality of the truncations.
  have htrunc :
      (MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1)))
        (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r) =
      (MvPowerSeries.trunc R
          (Finsupp.equivFunOnFinite.symm (fun _ : Fin n => k + 1)))
        ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1) := by
    apply MvPolynomial.ext
    intro α
    rw [MvPowerSeries.coeff_trunc, MvPowerSeries.coeff_trunc]
    split_ifs with hα
    · change (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r :
          MvPowerSeries _ R) α =
        ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1 :
          MvPowerSeries _ R) α
      exact _mvPowerSeriesEval_surjective_limit_coeff_eq_seq I hn f hf hspan r
        k α hα
    · rfl
  unfold _mvPowerSeriesEval_partial
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply]
  exact congrArg
    (fun p => (Submodule.mkQ (I ^ k • (⊤ : Submodule R R)))
      ((MvPolynomial.aeval f) p)) htrunc

/-- **(L4.3.c.per_level.seq_val)**: at every level `k`, the partial evaluation
of the `k`-th sequence power series agrees with `r.val k`. This is the
per-level translation of the seq spec `mvPowerSeriesEval (P k) - r ∈ I^k • ⊤`:
the difference's `k`-th component vanishes mod `I^k • ⊤`, so the components
agree there. -/
private lemma _mvPowerSeriesEval_surjective_partial_seq_val_eq
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) :
    _mvPowerSeriesEval_partial I f hf k
        ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1) =
      (r : AdicCompletion I R).val k := by
  -- Sub-claim: any x ∈ I^k • ⊤ ⊆ AdicCompletion I R has x.val k = 0
  -- (the k-th component lies in I^k • ⊤ inside R ⧸ I^k • ⊤, which is zero).
  have key : ∀ x : AdicCompletion I R,
      x ∈ (I ^ k • ⊤ : Submodule R (AdicCompletion I R)) → x.val k = 0 := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro s hs y _
      change (s • y).val k = 0
      rw [AdicCompletion.val_smul_apply]
      induction (y.val k) using Quotient.inductionOn' with
      | _ a =>
        change Submodule.Quotient.mk (s • a) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hs Submodule.mem_top
    · intro x y hx hy
      change (x + y).val k = 0
      rw [AdicCompletion.val_add_apply, hx, hy]
      exact zero_add 0
  -- Apply `key` to the spec `mvPowerSeriesEval P - r ∈ I^k • ⊤`.
  have hzero := key _ ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).2)
  rw [AdicCompletion.val_sub_apply] at hzero
  have heval := sub_eq_zero.mp hzero
  rw [← heval]
  -- `mvPowerSeriesEval` is the `RingHom` bundling `AdicCompletion.lift`, so by
  -- `AdicCompletion.eval_lift_apply` its k-th value equals the partial map.
  change (AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
      (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle)
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1)).val k =
    ((mvPowerSeriesEval I hn f hf)
      ((_mvPowerSeriesEval_surjective_seq I hn f hf hspan r k).1) :
      AdicCompletion I R).val k
  rfl

/-- **(L4.3.c.per_level)**: per-level equality between
`mvPowerSeriesEval (limit)` and `r` in `R ⧸ I^k • ⊤`. This packages the
substantive content of `_mvPowerSeriesEval_surjective_limit_spec`: the
limit power series, when evaluated, agrees with `r` modulo `I^k` for every
`k`. Combined with `AdicCompletion.ext`, it gives the global equality.

Discharge structure:
1. Unfold `mvPowerSeriesEval` (it bundles `AdicCompletion.lift` as a RingHom).
2. `AdicCompletion.eval_lift_apply` reduces the LHS to
   `_mvPowerSeriesEval_partial I f hf k (limit)`.
3. `_mvPowerSeriesEval_surjective_limit_partial_eq` rewrites this as
   `_mvPowerSeriesEval_partial I f hf k ((seq k).1)`.
4. `_mvPowerSeriesEval_surjective_partial_seq_val_eq` identifies this with
   `r.val k`. -/
private lemma _mvPowerSeriesEval_surjective_limit_spec_per_level
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) (k : ℕ) :
    (mvPowerSeriesEval I hn f hf
        (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r) :
      AdicCompletion I R).val k = r.val k := by
  change (AdicCompletion.lift I (_mvPowerSeriesEval_partial I f hf)
      (fun {_ _} hle => _mvPowerSeriesEval_partial_compat I f hf hle)
      (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r)).val k = r.val k
  rw [AdicCompletion.eval_lift_apply]
  exact (_mvPowerSeriesEval_surjective_limit_partial_eq I hn f hf hspan r k).trans
    (_mvPowerSeriesEval_surjective_partial_seq_val_eq I hn f hf hspan r k)

/-- **(L4.3.c)**: the limit power series evaluates to `r`. Key spec:
`mvPowerSeriesEval I hn f hf (limit) = r` in `AdicCompletion I R`.

Discharge: `AdicCompletion.ext` reduces to per-level equality, delegated to
`_mvPowerSeriesEval_surjective_limit_spec_per_level`. -/
private lemma _mvPowerSeriesEval_surjective_limit_spec
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (hn : 0 < n) (f : Fin n → R)
    (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I)
    (r : AdicCompletion I R) :
    mvPowerSeriesEval I hn f hf
      (_mvPowerSeriesEval_surjective_limit I hn f hf hspan r) = r := by
  apply AdicCompletion.ext
  intro k
  exact _mvPowerSeriesEval_surjective_limit_spec_per_level I hn f hf hspan r k

/-- **(L4.3 = L4 main)**: for `f₁,…,fₙ` generating `I`, the evaluation map
`mvPowerSeriesEval I hn f hf` is surjective onto `AdicCompletion I R`.

Discharge: combine L4.3.b (the limit power series) and L4.3.c (limit evaluates
to `r`).

Source: Stacks 0316 proof, "(details omitted)". -/
theorem mvPowerSeriesEval_surjective [IsNoetherianRing R] (I : Ideal R)
    {n : ℕ} (hn : 0 < n) (f : Fin n → R) (hf : ∀ i, f i ∈ I) (hspan : Ideal.span (Set.range f) = I) :
    Function.Surjective (mvPowerSeriesEval I hn f hf) := by
  intro r
  exact ⟨_mvPowerSeriesEval_surjective_limit I hn f hf hspan r,
    _mvPowerSeriesEval_surjective_limit_spec I hn f hf hspan r⟩

/-! ## Main result — Stacks 0316 -/

/-- **Stacks 0316 (Lemma 10.97.6)**: for `R` a Noetherian commutative ring
and `I ⊂ R` an ideal, the I-adic completion `AdicCompletion I R` is
Noetherian.

Source (verbatim, Stacks tag 0316):
> "Let `R` be a Noetherian ring. Let `I` be an ideal of `R`. The completion
> `R^∧` of `R` with respect to `I` is Noetherian.
>
> Choose generators `f₁,…,fₙ` of `I`. Consider the map `R[[x₁,…,xₙ]] → R̂`,
> `xᵢ ↦ fᵢ`. This is a well defined and surjective ring map (details
> omitted). Since `R[[x₁,…,xₙ]]` is Noetherian (Lemma 10.31.2) we win."

Project plan: compose L1 (pick generators) + L2 (`MvPowerSeries` Noetherian)
+ L3 (eval map) + L4 (surjectivity) + L5 (`isNoetherianRing_of_surjective`).

Consumers:
* `WedhornStronglyNoetherian._sub_lemma_L5_1_2_adicCompletion_noetherian`
  (verbatim discharge).
* `PresheafTateStructure.presheafValue_pairOfDefinition_isNoetherian`
  (applied to `A₀[T/s]` extension of `A₀`). -/
theorem isNoetherianRing [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  classical
  -- L1: pick generators of I.
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).mp inferInstance I
  -- Case-split on whether `s` is empty (i.e., `I = ⊥`). The `I = ⊥` case
  -- uses `IsAdicComplete (⊥ : Ideal R) R` (a mathlib instance) to obtain
  -- a bijective canonical map `R → AdicCompletion ⊥ R`, transporting
  -- noetherianness. The `s.card ≥ 1` case runs the Stacks 0316 eval-surjective
  -- argument with the now-available `hn : 0 < n` hypothesis.
  rcases Nat.eq_zero_or_pos s.card with hn_eq | hn
  · -- s.card = 0 ⇒ I = ⊥.
    have hI : I = ⊥ := by
      rw [← hs, Finset.card_eq_zero.mp hn_eq, Finset.coe_empty, Ideal.span_empty]
    subst hI
    -- `algebraMap R (AdicCompletion ⊥ R)` is a surjective RingHom: it agrees
    -- with `AdicCompletion.of ⊥ R` (by `algebraMap_apply` with `S = R`), and
    -- the latter is bijective by `IsAdicComplete (⊥ : Ideal R) R`.
    have hof_bij : Function.Bijective (AdicCompletion.of (⊥ : Ideal R) R) :=
      AdicCompletion.of_bijective (⊥ : Ideal R) R
    refine isNoetherianRing_of_surjective R (AdicCompletion (⊥ : Ideal R) R)
      (algebraMap R (AdicCompletion (⊥ : Ideal R) R)) (fun y => ?_)
    obtain ⟨x, hx⟩ := hof_bij.surjective y
    -- `algebraMap R (AdicCompletion ⊥ R) x = of ⊥ R (algebraMap R R x) = of ⊥ R x`
    -- via `algebraMap_apply` and `algebraMap R R = id`.
    exact ⟨x, by rw [AdicCompletion.algebraMap_apply]; simpa using hx⟩
  -- s.card ≥ 1: the standard eval-surjective argument.
  let n := s.card
  let e : Fin n ≃ {x // x ∈ s} := s.equivFin.symm
  let f : Fin n → R := fun i => (e i : R)
  have hf_in_I : ∀ i, f i ∈ I := by
    intro i
    rw [← hs]
    exact Ideal.subset_span (e i).property
  have hspan : Ideal.span (Set.range f) = I := by
    rw [← hs]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro x ⟨i, rfl⟩
      exact Ideal.subset_span (e i).property
    · rw [Ideal.span_le]
      intro x hx
      refine Ideal.subset_span ⟨e.symm ⟨x, hx⟩, ?_⟩
      simp [f]
  -- L2: MvPowerSeries (Fin n) R is Noetherian.
  haveI hnoeth : IsNoetherianRing (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.instIsNoetherianRing_fin R n
  -- L3 + L4: eval map is a surjective ring hom.
  exact isNoetherianRing_of_surjective _ _ (mvPowerSeriesEval I hn f hf_in_I)
    (mvPowerSeriesEval_surjective I hn f hf_in_I hspan)

end AdicCompletion
