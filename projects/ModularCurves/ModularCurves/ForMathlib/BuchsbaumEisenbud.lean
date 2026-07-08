/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.

# Openness of the flat locus — the homological residual (Stacks 00RC)

PLANNING SKELETON for closing `flatLocus_spreads_of_flat`
(`ModularCurves.ForMathlib.FlatLocus`, the sole `sorry` of the openness proof).

Every declaration here is a `:= sorry` STATEMENT ticket, ordered as a dependency tree.  The
mathematical content, verbatim source quotes (Stacks locators) and mathlib map for each leaf live in
`projects/ModularCurves/.mathlib-quality/decomposition-buchsbaum-eisenbud.md`.

## Route (decided against the ACTUAL Stacks proofs, not assumed)

The residual is the classical **Stacks 00RC (Theorem 10.129.4)** local-spreading step.  Its proof
chain, transcribed from the source, is:

  00LP  finite free resolution               — HAVE (`FiniteFreeResolution`)
  00HM  dévissage: two-of-three flat in SES   — NEW (small; `Module.Flat` SES)      [T-DEVISSAGE]
  00MH  free_of_flat_of_fibre_free            — HAVE (`LocalCriterion`)
  freeLocus openness                          — HAVE (mathlib `Module.freeLocus`)   [T-FREESPREAD]
  00RB  openness of the fibre-exact locus      — NEW (via 00N1)                       [T-RB]
    └ 00N1 Buchsbaum–Eisenbud acyclicity       — NEW (the make-or-break)             [T-BE]
        └ ideal of minors I_r(φ) / Fitting     — NEW                                 [T-FIT]
        └ grade ≥ k (regular sequences / Ext)  — NEW                                 [T-GRADE]
  00MI  coker flat from fibre-exactness        — NEW (via 00ME; NO Buchsbaum–Eisenbud)  [T-MI]
    └ 00ME two-term local criterion            — NEW (close to `LocalCriterion`)     [T-ME]

plus a reduction `Spec S ↪ Spec P = Spec R[x₁..xₙ]` so the resolution terms are `R`-flat
[T-REDUCEP], and the final assembly [T-FINAL].

## Route decision: FULL Buchsbaum–Eisenbud (00N1) is REQUIRED; "lean via Ext-support" does NOT remove it.

The full 00RB proof (10.129.3) invokes 00N1 as an **iff** over the fibres: it forms the ideals `Iᵢ`
of `rᵢ×rᵢ` minors of `φᵢ` and uses 00N1 to characterise fibre-exactness as `(Iᵢ)_𝔮 = S_𝔮` OR
`(Iᵢ)_𝔮` contains an `S_𝔮/𝔭S_𝔮`-regular sequence of length `i` (BOTH directions used).  The
strategic "grade ≥ k is open because `Extⁱ(S/I,S)` has CLOSED support" observation is REAL and
buildable (mathlib has `Module.support_eq_zeroLocus` + derived `Ext`), but it only discharges the
**openness-of-the-depth-condition** sub-step of 00RB — the SAME sub-step Stacks discharges natively
with fibre-regular sequences (Lemma 10.129.2, which mathlib already mirrors as
`RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`).  It does NOT replace the 00N1
acyclicity characterisation, whose HARD direction (rank+depth conditions ⟹ exact) is irreducibly
needed to conclude fibre-exactness NEAR `𝔮` from the (open) conditions.  Hence 00N1 is the
make-or-break; the Ext-support idea is a clean optional replacement for [T-GRADE]/10.129.2 only.

## Feasibility

[T-BE]+[T-FIT]+[T-GRADE] (minor ideals + McCoy rank + the acyclicity induction) is a large,
research-grade formalization (multi-week+).  Everything else assembles existing pieces and is
tractable.  See the decomposition doc for the per-leaf verdict.
-/
import Mathlib
import ModularCurves.ForMathlib.FlatLocus
import ModularCurves.ForMathlib.FittingIdeals
import ModularCurves.ForMathlib.Grade
import ModularCurves.ForMathlib.Acyclicity

open TensorProduct

noncomputable section

/-! [T-FIT] `LinearMap.idealOfMinors` (+ antitone, McCoy) is now in `ForMathlib.FittingIdeals`;
[T-GRADE] `Ideal.gradeGE` (+ localize, openness) is now in `ForMathlib.Grade`.  Both imported above. -/

/-! ## [T-DEVISSAGE] 00HM (Lemma 10.39.13): two-of-three flatness in a short exact sequence

`0 → A → B → C → 0` with `B, C` flat ⟹ `A` flat.  Stacks proves it from the ideal criterion
(10.39.5) + `Tor₁(C,-)` (10.39.12); likely derivable from mathlib `Module.Flat.iff_rTensor_exact`.
Carries `R`-flatness of `M` down its syzygies. -/

/-- [T-DEVISSAGE] Stacks 00HM(2): in `0 → A →f→ B →g→ C → 0`, `B, C` flat ⟹ `A` flat. -/
theorem Module.Flat.of_shortExact_of_flat_flat {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    [Module.Flat R B] [Module.Flat R C] : Module.Flat R A := by
  sorry

/-! ## [T-ME] 00ME (Lemma 10.99.1): two-term local criterion (base case of 00MI)

`R → S` local hom of local rings, `S` Noetherian; `M` `R`-flat, `N` finite `S`-module, `u : N → M`
`R`-linear with `ū : N/𝔪N → M/𝔪M` injective ⟹ `u` injective and `M/u(N)` `R`-flat.  Krull-intersection
lifting of injectivity + Tor-vanishing for the cokernel; close to
`LocalCriterion.exists_fibre_adapted_surjection`. -/

/-- [T-ME] Stacks 00ME: two-term local criterion.  `ū` injective ⟹ `u` injective and `coker u` is
`R`-flat. -/
theorem local_criterion_twoTerm {R S M N : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] [Module.Finite S N]
    (u : N →ₗ[R] M)
    (hbar : Function.Injective (LinearMap.lTensor (R ⧸ IsLocalRing.maximalIdeal R)
      (LinearMap.restrictScalars R u))) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) := by
  sorry

/-! ## Finite free complexes: the encoding used by [T-BE], [T-RB], [T-MI]

A finite homological complex of finite free `S`-modules `⋯ → F₂ →(φ 1)→ F₁ →(φ 0)→ F₀`, with
`Fᵢ = S^{rk i}` and `rk i = 0` for `i ≥ e`.  "Exact" (at every `Fᵢ`, `i ≥ 1`) is
`∀ i, Function.Exact (φ (i+1)) (φ i)`. -/

/-- Fibre complex of `φ` is exact at `𝔮` (Stacks 00RB `F̄_{•,𝔮}` exact): the complex `φ ⊗_R κ(𝔭)`
(`𝔭 = 𝔮 ∩ R`) localised at `𝔮` is exact.  Packaged predicate. -/
def FibreExactAt (R : Type*) [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (q : PrimeSpectrum S) : Prop := sorry

/-- Special-fibre complex `F_•/𝔪F_•` (mod the maximal ideal of a LOCAL `R`) is exact.  Hypothesis of
00MI. -/
def SpecialFibreExact (R : Type*) [CommRing R] [IsLocalRing R] {S : Type*} [CommRing S]
    [Algebra R S] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S)) : Prop := sorry

/-! ## [T-BE] 00N1 (Proposition 10.102.9): the Buchsbaum–Eisenbud acyclicity criterion — MAKE-OR-BREAK

Over a local Noetherian ring, the complex is exact iff for each `i` in range `rankᵢ = rᵢ` and the
minor ideal `I_{rᵢ}(φᵢ)` is the whole ring or contains a regular sequence of length `i`.  Stated in
the "ranks given" form 00RB actually uses (00RB first fixes the ranks via 00MI, then invokes the
depth half).  The rank relation `rnk i + rnk (i+1) = rk i` on the resolution range encodes condition
(2)(a); the disjunction encodes (2)(b) (grade `≥ i`).  The HARD direction (⟸) is the acyclicity
theorem.

INDEXING (corrected 2026-07-08 — the original skeleton had an off-by-one, machine-refuted):
Lean `φ j : F_{j+1} → F_j`, so Stacks' `φᵢ` (the `i`-th differential `F_i → F_{i-1}`) is Lean `φ (i-1)`.
The `i`-th condition (`1 ≤ i ≤ e`) is therefore on `φ (i-1)`, with minor size `rnk i = rank φᵢ` and
grade `≥ i`.  (Writing `(φ i)` here is FALSE: `hrnk`+`hrnk_top` force `F_e = 0`, so `φ (e-1)` is out
of the zero module and `idealOfMinors (rnk(e-1)) (φ(e-1))` would be `⊥`, making the RHS false for
every complex with `rk(e-1) ≥ 1`.) -/

/-! ### Proof of `buchsbaumEisenbud_acyclic`, decomposed into `private` lemmas.

`buchsbaumEisenbud_acyclic` is assembled below as `⟨be_forward, be_backward⟩`.  Each direction
splits into a fully-proven *trivial* part (handled here) and one *interior analytic core*
(`be_forward_core` / `be_backward_core`), each of which is the genuinely mathlib-absent
depth/acyclicity content of Stacks 00N1 (see their docstrings; no `depth`/Auslander–Buchsbaum/
Peskine–Szpiro exists in mathlib). Structural helpers and the regular-element recipe are proven. -/

/-- A pair of maps through a subsingleton middle module is exact. -/
private theorem exact_of_subsingleton_mid {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    [Subsingleton N] (f : M →ₗ[R] N) (g : N →ₗ[R] P) : Function.Exact f g := by
  intro y
  have : y = 0 := Subsingleton.elim _ _
  subst this
  exact iff_of_true (map_zero g) ⟨0, map_zero f⟩

/-- A free module `Fin n → S` with `n = 0` is a subsingleton (the zero module). -/
private theorem subsingleton_pi_fin_of_eq_zero {S : Type*} [CommRing S] {n : ℕ} (h : n = 0) :
    Subsingleton (Fin n → S) := by
  haveI : IsEmpty (Fin n) := by rw [h]; infer_instance
  exact ⟨fun a b => funext fun x => isEmptyElim x⟩

/-- **Regular element in a non-avoided ideal** (prime avoidance against the associated primes).
If `I` is contained in no associated prime of a finite module `M`, then `I` contains an
`M`-regular element (a nonzerodivisor on `M`).  This is the tool that turns a `grade`/`depth`
hypothesis into an actual regular element for the two analytic cores below. -/
private theorem exists_isSMulRegular_of_forall_not_le_associatedPrimes {S : Type*} [CommRing S]
    [IsNoetherianRing S] {M : Type*} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (I : Ideal S) (h : ∀ p ∈ associatedPrimes S M, ¬ (I : Set S) ⊆ p) :
    ∃ x ∈ I, IsSMulRegular M x := by
  have hfin : (associatedPrimes S M).Finite := associatedPrimes.finite S M
  have hnot : ¬ ((I : Set S) ⊆ ⋃ p ∈ associatedPrimes S M, (p : Set S)) := by
    rw [Ideal.subset_union_prime_finite hfin ⊥ ⊥
      (fun p hp _ _ => (AssociatedPrimes.mem_iff.mp hp).isPrime)]
    rintro ⟨p, hp, hle⟩
    exact h p hp hle
  rw [Set.not_subset] at hnot
  obtain ⟨x, hxI, hxnot⟩ := hnot
  refine ⟨x, hxI, ?_⟩
  rw [biUnion_associatedPrimes_eq_compl_regular S M] at hxnot
  simpa using hxnot

/-! ### Assembly of `be_forward_core` via the Stacks 00N1 `(1)⟹(2)` induction.

The forward core is proved with **NO depth invariant and NO Auslander–Buchsbaum** (contrary to the
old plan): the Stacks 00N1 `(1)⟹(2)` proof localises at each associated prime, uses that the depth-`0`
splitting forces `I(φᵢ)_𝔮 = S_𝔮` (00MY+00MW, `idealOfMinors_eq_top_of_exact_of_isAssociatedPrime`),
picks a nonzerodivisor `x` in `I(φᵢ)` avoiding every associated prime (prime avoidance), reduces the
complex modulo `x` (00MZ, `exact_baseChange_quotient_of_isSMulRegular`, which stays exact at spots
`≥ 2`), and inducts on `e` (equivalently on the target index `i`).  The helpers below package the
reduction of the complex along a ring map `S → S'` as honest maps of standard free modules
(`reduceMap`), so that the minor ideals map cleanly (`idealOfMinors_reduceMap`) and exactness
transfers through the pi–tensor equivalence. -/

section BEForwardHelpers

open Matrix RingTheory.Sequence

universe u

variable {S : Type*} [CommRing S] {a b c : ℕ}

/-- Reduce a map of standard free modules along an algebra map `S → S'` (the map with the
base-changed matrix, in the standard bases). -/
private def reduceMap (S' : Type*) [CommRing S'] [Algebra S S']
    (φ : (Fin a → S) →ₗ[S] (Fin b → S)) : (Fin a → S') →ₗ[S'] (Fin b → S') :=
  Matrix.toLin' ((LinearMap.toMatrix' φ).map (algebraMap S S'))

variable (S' : Type*) [CommRing S'] [Algebra S S']

@[simp] private lemma toMatrix'_reduceMap (φ : (Fin a → S) →ₗ[S] (Fin b → S)) :
    LinearMap.toMatrix' (reduceMap S' φ) = (LinearMap.toMatrix' φ).map (algebraMap S S') := by
  rw [reduceMap, LinearMap.toMatrix'_toLin']

private lemma reduceMap_apply (φ : (Fin a → S) →ₗ[S] (Fin b → S)) (v : Fin a → S') :
    reduceMap S' φ v = (LinearMap.toMatrix' φ).map (algebraMap S S') *ᵥ v := by
  rw [reduceMap, Matrix.toLin'_apply]

/-- The minor ideal of the reduced map is the image of the minor ideal. -/
private lemma idealOfMinors_reduceMap (r : ℕ) (φ : (Fin a → S) →ₗ[S] (Fin b → S)) :
    LinearMap.idealOfMinors r (reduceMap S' φ)
      = (LinearMap.idealOfMinors r φ).map (algebraMap S S') := by
  show Matrix.idealOfMinors r (LinearMap.toMatrix' (reduceMap S' φ))
     = (Matrix.idealOfMinors r (LinearMap.toMatrix' φ)).map (algebraMap S S')
  rw [toMatrix'_reduceMap, ← Matrix.idealOfMinors_map]

/-- The pi–tensor equivalence `S' ⊗[S] (Fin n → S) ≃ₗ[S'] (Fin n → S')`. -/
private def reducePiEquiv (n : ℕ) : S' ⊗[S] (Fin n → S) ≃ₗ[S'] (Fin n → S') :=
  (Algebra.TensorProduct.piScalarRight S S' S' (Fin n)).toLinearEquiv

@[simp] private lemma piEquiv_tmul (n : ℕ) (s : S') (y : Fin n → S) :
    reducePiEquiv S' n (s ⊗ₜ[S] y) = fun i => y i • s := rfl

/-- `reduceMap` is the base change conjugated by the pi–tensor equivalence: this is the ladder square
that transfers exactness between the two spellings of the reduced complex. -/
private lemma reduceMap_naturality (φ : (Fin a → S) →ₗ[S] (Fin b → S)) :
    (reduceMap S' φ) ∘ₗ (reducePiEquiv S' a).toLinearMap
      = (reducePiEquiv S' b).toLinearMap ∘ₗ (φ.baseChange S') := by
  apply LinearMap.restrictScalars_injective S
  apply TensorProduct.ext'
  intro s y
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearEquiv.coe_coe, piEquiv_tmul, LinearMap.baseChange_tmul]
  funext j
  rw [reduceMap_apply]
  have hy : φ y = LinearMap.toMatrix' φ *ᵥ y := (LinearMap.toMatrix'_mulVec φ y).symm
  simp only [Matrix.mulVec, Matrix.map_apply, dotProduct, hy, Algebra.smul_def]
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

@[simp] private lemma reduceMap_zero :
    reduceMap S' (0 : (Fin a → S) →ₗ[S] (Fin b → S)) = 0 := by
  simp [reduceMap]

private lemma reduceMap_comp (φ : (Fin b → S) →ₗ[S] (Fin c → S))
    (ψ : (Fin a → S) →ₗ[S] (Fin b → S)) :
    reduceMap S' (φ ∘ₗ ψ) = reduceMap S' φ ∘ₗ reduceMap S' ψ := by
  rw [reduceMap, reduceMap, reduceMap, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]

private lemma exact_reduceMap_iff {p q r : ℕ} (χ : (Fin p → S) →ₗ[S] (Fin q → S))
    (χ' : (Fin q → S) →ₗ[S] (Fin r → S)) :
    Function.Exact (reduceMap S' χ) (reduceMap S' χ') ↔
      Function.Exact (χ.baseChange S') (χ'.baseChange S') :=
  Function.Exact.iff_of_ladder_linearEquiv (reduceMap_naturality S' χ) (reduceMap_naturality S' χ')

private lemma exact_reduceMap_of_flat [Module.Flat S S'] {p q r : ℕ}
    (χ : (Fin p → S) →ₗ[S] (Fin q → S)) (χ' : (Fin q → S) →ₗ[S] (Fin r → S))
    (h : Function.Exact χ χ') :
    Function.Exact (reduceMap S' χ) (reduceMap S' χ') := by
  rw [exact_reduceMap_iff]
  simpa only [LinearMap.baseChange_eq_ltensor] using Module.Flat.lTensor_exact S' h

/-- **Piece A** (localisation at an associated prime, Stacks 00MY+00MW).  If the finite free complex
is exact, then for each interior index the minor ideal `I(φᵢ)` is not contained in any associated
prime `𝔮` of `S`.  Localise at `𝔮` (flat, keeps exactness); `S_𝔮` has depth `0`, so
`idealOfMinors_eq_top_of_exact_of_isAssociatedPrime` forces `I(φᵢ)·S_𝔮 = S_𝔮`, i.e. `I(φᵢ) ⊄ 𝔮`. -/
private theorem idealOfMinors_not_le_of_mem_associatedPrimes
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (hie : i < e)
    (q : Ideal S) (hq : q ∈ associatedPrimes S S) :
    ¬ (LinearMap.idealOfMinors (rnk i) (φ (i - 1)) : Set S) ⊆ q := by
  haveI hqp : q.IsPrime := (AssociatedPrimes.mem_iff.mp hq).1
  set Sq := Localization.AtPrime q with hSq
  let ψ : (j : ℕ) → (Fin (rk (j + 1)) → Sq) →ₗ[Sq] (Fin (rk j) → Sq) :=
    fun j => reduceMap Sq (φ j)
  have hcomplexψ : ∀ j, (ψ j) ∘ₗ (ψ (j + 1)) = 0 := fun j => by
    show reduceMap Sq (φ j) ∘ₗ reduceMap Sq (φ (j + 1)) = 0
    rw [← reduceMap_comp, hcomplex j, reduceMap_zero]
  have hexactψ : ∀ j, Function.Exact (ψ (j + 1)) (ψ j) := fun j =>
    exact_reduceMap_of_flat Sq _ _ (hexact j)
  have hdepth0 : IsLocalRing.maximalIdeal Sq ∈ associatedPrimes Sq Sq := by
    apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      q.primeCompl (Algebra.linearMap S Sq)
    have hcomap : (IsLocalRing.maximalIdeal Sq).comap (algebraMap S Sq) = q :=
      Localization.AtPrime.under_maximalIdeal
    rw [hcomap]; exact hq
  have htop : LinearMap.idealOfMinors (rnk i) (ψ (i - 1)) = ⊤ :=
    idealOfMinors_eq_top_of_exact_of_isAssociatedPrime hdepth0 e rk rnk hrk hrnk_top hrnk ψ
      hcomplexψ hexactψ i hi1 hie
  rw [show ψ (i - 1) = reduceMap Sq (φ (i - 1)) from rfl, idealOfMinors_reduceMap] at htop
  intro hle
  rw [SetLike.coe_subset_coe] at hle
  have h1 : (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).map (algebraMap S Sq)
      ≤ q.map (algebraMap S Sq) := Ideal.map_mono hle
  rw [htop, Localization.AtPrime.map_eq_maximalIdeal] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal Sq).ne_top (top_le_iff.mp h1)

/-- Lift a list along a function, preserving a pointwise predicate. -/
private lemma list_lift {α β : Type*} (f : α → β) (P : α → Prop) :
    ∀ (l : List β), (∀ z ∈ l, ∃ w, P w ∧ f w = z) →
      ∃ ys : List α, ys.map f = l ∧ ∀ w ∈ ys, P w
  | [], _ => ⟨[], rfl, by simp⟩
  | z :: l, h => by
    obtain ⟨w, hw, hfw⟩ := h z List.mem_cons_self
    obtain ⟨ys, hys, hym⟩ := list_lift f P l (fun z' hz' => h z' (List.mem_cons_of_mem _ hz'))
    exact ⟨w :: ys, by simp [hfw, hys], fun w' hw' => by
      rcases List.mem_cons.mp hw' with rfl | h'
      · exact hw
      · exact hym w' h'⟩

/-- **Cons step for grade.**  If `x ∈ I` is a nonzerodivisor and `I·(S/x)` has grade `≥ k`, then `I`
has grade `≥ k+1` (prepend `x` to a lift of the regular sequence). -/
private theorem gradeGE_cons_of_isSMulRegular {S : Type*} [CommRing S] (I : Ideal S) (x : S)
    (hxI : x ∈ I) (hxreg : IsSMulRegular S x) (k : ℕ)
    (h : (I.map (Ideal.Quotient.mk (Ideal.span {x}))).gradeGE k) : I.gradeGE (k + 1) := by
  obtain ⟨rs', hlen', hreg', hmem'⟩ := h
  obtain ⟨ys, hys, hymem⟩ := list_lift (Ideal.Quotient.mk (Ideal.span {x})) (· ∈ I) rs'
    (fun z hz => (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hmem' z hz))
  refine ⟨x :: ys, ?_, ?_, ?_⟩
  · rw [List.length_cons, ← List.length_map (Ideal.Quotient.mk (Ideal.span {x})), hys, hlen']
  · rw [isRegular_cons_iff']
    refine ⟨hxreg, ?_⟩
    rw [hys]
    have eBridge : QuotSMulTop x S ≃ₗ[S ⧸ Ideal.span {x}] (S ⧸ Ideal.span {x}) :=
      (LinearEquiv.trans (QuotSMulTop.equivQuotTensor x S)
        (TensorProduct.rid S (S ⧸ Ideal.span {x}))).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective
    exact (LinearEquiv.isRegular_congr eBridge rs').mpr hreg'
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxI
    · exact hymem y hy

/-- **The Stacks 00N1 `(1)⟹(2)` induction.**  Over a local Noetherian ring, an exact finite free
complex has `I(φᵢ)` of grade `≥ i` (or `= ⊤`), for each interior index `1 ≤ i < e`.  Induction on `i`:
pick a nonzerodivisor `x ∈ I(φᵢ)` avoiding the associated primes (Piece A + prime avoidance), reduce
the complex modulo `x` (00MZ) to the shifted complex over `S/x`, and prepend `x` to the grade-`(i-1)`
regular sequence obtained from the induction hypothesis (`gradeGE_cons_of_isSMulRegular`). -/
private theorem be_forward_gradeGE_aux :
    ∀ (i : ℕ) {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (e : ℕ) (rk rnk : ℕ → ℕ)
      (_hrk : ∀ i, e ≤ i → rk i = 0) (_hrnk_top : ∀ i, e ≤ i → rnk i = 0)
      (_hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
      (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
      (_hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
      (_hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i)),
      1 ≤ i → i < e →
      (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
        LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤ := by
  intro i
  induction i with
  | zero => intro S _ _ _ e rk rnk _ _ _ φ _ _ hi1 _; omega
  | succ j ih =>
    intro S _ _ _ e rk rnk hrk hrnk_top hrnk φ hcomplex hexact _ hie
    simp only [Nat.succ_sub_one]
    by_cases hItop : LinearMap.idealOfMinors (rnk (j + 1)) (φ j) = ⊤
    · exact Or.inr hItop
    · refine Or.inl ?_
      have hIm : LinearMap.idealOfMinors (rnk (j + 1)) (φ j) ≤ IsLocalRing.maximalIdeal S :=
        IsLocalRing.le_maximalIdeal hItop
      obtain ⟨x, hxI, hxreg⟩ := exists_isSMulRegular_of_forall_not_le_associatedPrimes
        (LinearMap.idealOfMinors (rnk (j + 1)) (φ j))
        (fun p hp => idealOfMinors_not_le_of_mem_associatedPrimes e rk rnk hrk hrnk_top hrnk φ
          hcomplex hexact (j + 1) (by omega) hie p hp)
      have hxm : x ∈ IsLocalRing.maximalIdeal S := hIm hxI
      have hspan : Ideal.span {x} ≠ (⊤ : Ideal S) := by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hxm)
      haveI hnt : Nontrivial (S ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hspan
      haveI : IsLocalRing (S ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      apply gradeGE_cons_of_isSMulRegular _ x hxI hxreg j
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact ⟨[], rfl, IsRegular.nil _ _, by simp⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        have hG := ih (S := S ⧸ Ideal.span {x}) (e - 1) (fun k => rk (k + 1)) (fun k => rnk (k + 1))
          (fun k _ => hrk (k + 1) (by omega)) (fun k _ => hrnk_top (k + 1) (by omega))
          (fun k _ _ => hrnk (k + 1) (by omega) (by omega))
          (fun k => reduceMap (S ⧸ Ideal.span {x}) (φ (k + 1)))
          (fun k => by
            show reduceMap (S ⧸ Ideal.span {x}) (φ (k + 1)) ∘ₗ
              reduceMap (S ⧸ Ideal.span {x}) (φ (k + 2)) = 0
            rw [← reduceMap_comp, hcomplex (k + 1), reduceMap_zero])
          (fun k => by
            rw [exact_reduceMap_iff]
            exact exact_baseChange_quotient_of_isSMulRegular φ hcomplex hexact x hxreg k)
          (by omega) (by omega)
        rw [idealOfMinors_reduceMap, Ideal.Quotient.algebraMap_eq] at hG
        rcases hG with hgrade | htop
        · exact hgrade
        · exfalso
          rw [Ideal.eq_top_iff_one,
            Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at htop
          obtain ⟨a, haI, ha1⟩ := htop
          have haspan : a - 1 ∈ Ideal.span {x} := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ha1, map_one, sub_self]
          have ha1m : a - 1 ∈ IsLocalRing.maximalIdeal S := by
            obtain ⟨cc, hcc⟩ := Ideal.mem_span_singleton.mp haspan
            rw [hcc]; exact Ideal.mul_mem_right cc _ hxm
          have hone : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
            have h1 : (1 : S) = a - (a - 1) := by ring
            rw [h1]; exact Submodule.sub_mem _ (hIm haI) ha1m
          exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
            (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

end BEForwardHelpers

/-- **[BE forward core]** Stacks 00N1, (1)⟹(2)(b), interior indices.  If the finite free complex is
exact (at every `F_{j+1}`) then for each interior index `1 ≤ i < e` the minor ideal
`I_{rnk i}(φ_{i-1})` (Stacks `I(φᵢ)`) is either the unit ideal or has grade `≥ i`.

PROOF ROUTE (Stacks 00N1 `(1)⟹(2)(b)`, **no depth invariant, no Auslander–Buchsbaum**): localise at
each associated prime `𝔮 ∈ Ass(S)` (depth `0`); the complex stays exact (flat base change), and the
depth-`0` splitting (00MY+00MW, `idealOfMinors_eq_top_of_exact_of_isAssociatedPrime`) forces
`I(φᵢ)_𝔮 = S_𝔮`, so `I(φᵢ)` avoids every associated prime.  Prime avoidance then yields a
nonzerodivisor `x ∈ I(φᵢ)`; quotienting by `x` keeps the complex exact at spots `≥ 2` (00MZ,
`exact_baseChange_quotient_of_isSMulRegular`), and induction on the target index builds a length-`i`
regular sequence in `I(φᵢ)` (`gradeGE_cons_of_isSMulRegular` + `be_forward_gradeGE_aux`).  The `∨ = ⊤`
disjunct handles the unit-ideal case (matching the `gradeGE` convention). -/
private theorem be_forward_core {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (hie : i < e) :
    (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
      LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤ :=
  be_forward_gradeGE_aux i e rk rnk hrk hrnk_top hrnk φ hcomplex hexact hi1 hie

open Matrix in
/-- **[McCoy annihilation — Cramer's rule].**  If `M *ᵥ x = 0` then every `m × m` minor of the
`n × m` matrix `M` (`m` = number of columns) annihilates `x`.  For a bijective column selection this
is `adjugate B * B = det B • 1` applied to `x ∘ ci`; a repeated column gives `det = 0`.  This is the
computational heart of the acyclicity base case. -/
private theorem det_submatrix_smul_eq_zero {S : Type*} [CommRing S] {n m : ℕ}
    (M : Matrix (Fin n) (Fin m) S) (x : Fin m → S) (hx : M *ᵥ x = 0)
    (ri : Fin m → Fin n) (ci : Fin m → Fin m) :
    (M.submatrix ri ci).det • x = 0 := by
  by_cases hci : Function.Injective ci
  · have hbij : Function.Bijective ci := ⟨hci, Finite.surjective_of_injective hci⟩
    set e₂ : Fin m ≃ Fin m := Equiv.ofBijective ci hbij with he₂
    have hcie : ci = ⇑e₂ := rfl
    have hBv : (M.submatrix ri ci) *ᵥ (x ∘ ci) = 0 := by
      rw [hcie, submatrix_mulVec_equiv]
      have hxc : (x ∘ ⇑e₂) ∘ ⇑e₂.symm = x := by funext k; simp [Function.comp]
      rw [hxc, hx]; funext i'; simp
    have hdet : (M.submatrix ri ci).det • (x ∘ ci) = 0 := by
      have h1 : ((M.submatrix ri ci).adjugate * (M.submatrix ri ci)) *ᵥ (x ∘ ci)
          = (M.submatrix ri ci).det • (x ∘ ci) := by
        rw [adjugate_mul, smul_mulVec, one_mulVec]
      rw [← h1, ← mulVec_mulVec, hBv, mulVec_zero]
    funext k
    obtain ⟨j, hj⟩ := hbij.surjective k
    have hcong := congrFun hdet j
    rw [← hj]; simpa [Function.comp] using hcong
  · rw [Function.not_injective_iff] at hci
    obtain ⟨a, b, hab, hne⟩ := hci
    have hdet0 : (M.submatrix ri ci).det = 0 :=
      det_zero_of_column_eq hne (fun k => by simp [Matrix.submatrix_apply, hab])
    rw [hdet0, zero_smul]

open Matrix in
/-- **[McCoy injectivity — the length-1 acyclicity base case].**  `φ : Sᵐ → Sⁿ` is injective as soon
as its ideal of maximal (`m × m`) column minors contains a nonzerodivisor, or is the whole ring.
This is Stacks 00N1 for a complex of length 1, and it discharges the *top* exactness spot
(= injectivity of the top differential) of the backward direction in `be_backward` below. -/
private theorem injective_of_maxMinors_nonZeroDiv {S : Type*} [CommRing S] {n m : ℕ}
    (φ : (Fin m → S) →ₗ[S] (Fin n → S))
    (hcond : (∃ r ∈ LinearMap.idealOfMinors m φ, IsSMulRegular S r) ∨
      LinearMap.idealOfMinors m φ = ⊤) :
    Function.Injective φ := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hMx : (LinearMap.toMatrix (Pi.basisFun S (Fin m)) (Pi.basisFun S (Fin n)) φ) *ᵥ x = 0 := by
    show LinearMap.toMatrix' φ *ᵥ x = 0
    rw [LinearMap.toMatrix'_mulVec]; exact hx
  have hsub : LinearMap.idealOfMinors m φ ≤ (Submodule.span S {x}).annihilator := by
    rw [LinearMap.idealOfMinors_eq]
    apply Matrix.idealOfMinors_le
    intro ri ci
    rw [Submodule.mem_annihilator_span_singleton]
    exact det_submatrix_smul_eq_zero _ x hMx ri ci
  rcases hcond with ⟨r, hrI, hr_reg⟩ | htop
  · have hrx : r • x = 0 := (Submodule.mem_annihilator_span_singleton x r).mp (hsub hrI)
    funext i
    exact hr_reg ((congrFun hrx i).trans (smul_zero r).symm)
  · have h1 : (1 : S) • x = 0 :=
      (Submodule.mem_annihilator_span_singleton x 1).mp (hsub (htop ▸ Submodule.mem_top))
    simpa using h1

/-- **[BE backward core]** Stacks 00N1, (2)⟹(1) — the Peskine–Szpiro acyclicity lemma, restricted to
the **deep interior**: spots `F_{i+1}` with a nonzero free both below and above (`rk (i+1) ≠ 0` and
`rk (i+2) ≠ 0`).  The *top* interior spot (`rk (i+2) = 0`, where exactness is injectivity of the top
differential) is fully discharged by `injective_of_maxMinors_nonZeroDiv` (McCoy) inside `be_backward`;
this residual is only the deeper homology, where genuine acyclicity (not mere injectivity) is needed.

MATHLIB-ABSENT CONTENT: the hard acyclicity direction ("what makes a complex exact").  Classical
proof: the Peskine–Szpiro acyclicity lemma — induction on the length `e`; if some homology
`H_j ≠ 0`, take an associated prime `𝔭 ∈ Ass H_j` (so `depth (H_j)_𝔭 = 0`), and the grade `≥ j`
condition on `I(φⱼ)` forces (after localising) a nonzerodivisor descent that kills `H_j`, a
contradiction.  Needs the depth-of-a-SES inequalities / associated-prime descent absent from
mathlib.  Stacks 00N1 (acyclicity lemma 0AVQ). -/
private theorem be_backward_core {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤)
    (i : ℕ) (hi : rk (i + 1) ≠ 0) (htop : rk (i + 2) ≠ 0) :
    Function.Exact (φ (i + 1)) (φ i) := sorry

/-- Forward direction, all indices: dispatches the trivial `rnk i = 0` conjunct (unit ideal) and the
interior indices to `be_forward_core`. -/
private theorem be_forward {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (hie : i ≤ e) :
    (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
      LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤ := by
  by_cases h0 : rnk i = 0
  · right
    rw [h0, LinearMap.idealOfMinors_eq, Matrix.idealOfMinors_zero]
  · have hlt : i < e := by
      by_contra hge
      exact h0 (hrnk_top i (not_lt.mp hge))
    exact be_forward_core e rk rnk hrk hrnk_top hrnk φ hcomplex hexact i hi1 hlt

/-- Backward direction, all indices: dispatches the trivial spots (`rk (i+1) = 0`, subsingleton
middle module) and the interior spots to `be_backward_core`. -/
private theorem be_backward {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤)
    (i : ℕ) :
    Function.Exact (φ (i + 1)) (φ i) := by
  by_cases h0 : rk (i + 1) = 0
  · haveI : Subsingleton (Fin (rk (i + 1)) → S) := subsingleton_pi_fin_of_eq_zero h0
    exact exact_of_subsingleton_mid _ _
  · by_cases htop : rk (i + 1 + 1) = 0
    · -- top spot: `F_{i+2} = 0` ⟹ `φ (i+1)` has range `⊥` ⟹ exactness = injectivity of `φ i`,
      -- which McCoy (`injective_of_maxMinors_nonZeroDiv`) gets from the grade condition at `i+1`.
      have hlt : i + 1 < e := by
        by_contra hge
        exact h0 (hrk (i + 1) (not_lt.mp hge))
      have hrnk2 : rnk (i + 1 + 1) = 0 := by
        by_cases hle : e ≤ i + 1 + 1
        · exact hrnk_top (i + 1 + 1) hle
        · have h := hrnk (i + 1 + 1) (by omega) (by omega)
          omega
      have hrnk_eq : rnk (i + 1) = rk (i + 1) := by
        have h := hrnk (i + 1) (by omega) hlt
        omega
      have hinj : Function.Injective (φ i) := by
        apply injective_of_maxMinors_nonZeroDiv
        have hc := hcond (i + 1) (by omega) (by omega)
        rw [show i + 1 - 1 = i from rfl, hrnk_eq] at hc
        rcases hc with hg | ht
        · refine Or.inl ?_
          obtain ⟨rs, hlen, hreg, hmem⟩ := hg
          have hne : rs ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen; omega
          obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
          rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
          exact ⟨r, hmem r (by simp), hreg.1⟩
        · exact Or.inr ht
      haveI : Subsingleton (Fin (rk (i + 1 + 1)) → S) := subsingleton_pi_fin_of_eq_zero htop
      rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr hinj]
      symm
      rw [LinearMap.range_eq_bot]
      exact Subsingleton.elim _ _
    · exact be_backward_core e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i h0 htop

/-- [T-BE] Buchsbaum–Eisenbud (Stacks 00N1), depth half in ranks-given form (Lean `φ (i-1)` = Stacks `φᵢ`). -/
theorem buchsbaumEisenbud_acyclic {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0)
    (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0) :
    (∀ i, Function.Exact (φ (i + 1)) (φ i)) ↔
      (∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤) :=
  ⟨fun hexact i hi1 hie => be_forward e rk rnk hrk hrnk_top hrnk φ hcomplex hexact i hi1 hie,
   fun hcond i => be_backward e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i⟩

/-! ## [T-RB] 00RB (Lemma 10.129.3): openness of the fibre-exact locus

From [T-BE]: at a fibre-exact `𝔮`, the (open) minor-ideal loci ([T-FIT]) + (open) grade loci
([T-GRADE.open]) give a basic-open neighbourhood keeping the complex fibre-exact.  (`R` Noetherian,
`S` a Noetherian `R`-flat algebra — in the application `S = R[x₁..xₙ]`, whose fibres are CM as 00RB
requires.) -/

/-- [T-RB] Stacks 00RB: fibre-exactness spreads to a basic open. -/
theorem fibreExact_spreads {R S : Type*} [CommRing R] [IsNoetherianRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing S] [Module.Flat R S]
    {rk : ℕ → ℕ} (e : ℕ) (hrk : ∀ i, e ≤ i → rk i = 0)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (q : PrimeSpectrum S) (hq : FibreExactAt R φ q) :
    ∃ g : S, g ∉ q.asIdeal ∧
      ∀ q' : PrimeSpectrum S, q' ∈ PrimeSpectrum.basicOpen g → FibreExactAt R φ q' := by
  sorry

/-! ## [T-MI] 00MI (Lemma 10.99.5): flatness of the cokernel from fibre-exactness — NO Buchsbaum–Eisenbud

`0 → F_e → ⋯ → F₀` a finite complex of `R`-flat finite `S`-modules whose special fibre is exact ⟹
the complex is exact and `coker(F₁ → F₀)` is `R`-flat.  Induction on `e` from [T-ME] (00ME).  Stated
with an abstract cokernel target `M` (matching the application, where `M` is the finitely-presented
module), presented by `π : F₀ ↠ M` with `Function.Exact (φ 0) π`. -/

/-- [T-MI] Stacks 00MI: special-fibre-exact ⟹ the cokernel `M` of `φ 0 : F₁ → F₀` is `R`-flat. -/
theorem coker_flat_of_specialFibreExact {R S M : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Flat R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    {rk : ℕ → ℕ} (e : ℕ) (hrk : ∀ i, e ≤ i → rk i = 0)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (π : (Fin (rk 0) → S) →ₗ[S] M) (hπ : Function.Surjective π) (hπφ : Function.Exact (φ 0) π)
    (hfib : SpecialFibreExact R φ) :
    Module.Flat R M := by
  sorry

/-! ## [T-REDUCEP] Reduce `Spec S` to the polynomial ring `P = R[x₁..xₙ]`

`R → S` finite presentation gives `P ↠ S`; `M` finitely presented over `S` is finitely presented
over `P`, `M_𝔮 ≅ M_{𝔮^P}` as `R`-modules, and a basic open of `Spec P` cuts a basic open of
`Spec S`.  This makes the resolution terms `R`-flat (free over the `R`-free `P`), the hypothesis
every homological leaf above needs. -/

/-- [T-REDUCEP] It suffices to prove flat-locus spreading when `S` is an `R`-free finitely-presented
`R`-algebra (i.e. a polynomial ring): the general case follows by restricting `M` along `P ↠ S`. -/
theorem flatLocus_spreads_reduce_to_polynomial {R S M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] {q : PrimeSpectrum S}
    (hq : q ∈ flatLocus R S M)
    (H : ∀ (P : Type) [CommRing P] [Algebra R P] [Module.Free R P] [Algebra.FinitePresentation R P]
      (M' : Type) [AddCommGroup M'] [Module R M'] [Module P M'] [IsScalarTower R P M']
      [Module.FinitePresentation P M'] (q' : PrimeSpectrum P), q' ∈ flatLocus R P M' →
        ∃ g : P, g ∉ q'.asIdeal ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum P)) ⊆ flatLocus R P M') :
    ∃ g : S, g ∉ q.asIdeal ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ flatLocus R S M := by
  sorry

/-! ## [T-FINAL] Assembly: the target `flatLocus_spreads_of_flat`

Over `P` (polynomial, `R`-free): finite free `P`-resolution (00LP, HAVE) → [T-DEVISSAGE] makes
`(Kₙ)_𝔮` `R`-flat → fibre of `Kₙ` free (`HilbertSyzygy.hasProjectiveDimensionLE_of_field`, global
dimension `n`) + 00MH (HAVE `Module.free_of_flat_of_fibre_free`) makes `(Kₙ)_𝔮` free over `P_𝔮` →
freeness spreads (mathlib `Module.basicOpen_subset_freeLocus_iff`) to `D(g₁)` → on `D(g₁)` the
truncated resolution is a finite complex of `R`-flat frees → fibre-exact at `𝔮` (`M_𝔮` flat) spreads
by [T-RB] → on the intersection [T-MI] gives `M` `R`-flat.  Then [T-REDUCEP] transports to `S`. -/

/-- [T-FINAL] The residual `flatLocus_spreads_of_flat` (identical statement to the `private` one in
`ForMathlib.FlatLocus`), assembled from the tree above. -/
theorem flatLocus_spreads_of_flat_viaBE {R S M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] {q : PrimeSpectrum S}
    (hq : q ∈ flatLocus R S M) :
    ∃ g : S, g ∉ q.asIdeal ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ flatLocus R S M := by
  sorry

end
