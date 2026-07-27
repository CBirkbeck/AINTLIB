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

## Route decision: FULL Buchsbaum–Eisenbud (00N1) is REQUIRED; "lean via Ext-support" does NOT
remove it.

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
import ModularCurves.ForMathlib.LocalizedModuleComap

open TensorProduct

noncomputable section

/-! [T-FIT] `LinearMap.idealOfMinors` (+ antitone, McCoy) is now in `ForMathlib.FittingIdeals`;
[T-GRADE] `Ideal.gradeGE` (+ localize, openness) is now in `ForMathlib.Grade`.  Both imported above.
-/

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
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ L hL
  -- `C` flat makes the SES `0 → A → B → C → 0` stay left-exact after `- ⊗ N`, i.e.
  -- `f ⊗ 𝟙 N : N ⊗ A → N ⊗ B` is injective (Stacks 00HM's Tor₁(C,N) = 0 input).
  have hcrux : Function.Injective (f.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hfg N
  -- `B` flat makes `L ⊗ 𝟙 B` injective.
  have hRB : Function.Injective (L.rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap L hL
  -- `map L f` factors two ways; the first exhibits it as injective, the second as
  -- `(𝟙 ⊗ f) ∘ (L ⊗ 𝟙 A)`, forcing `L ⊗ 𝟙 A` (the goal) injective.
  have e1 : TensorProduct.map L f = (L.rTensor B) ∘ₗ (f.lTensor N) := by
    ext n a; simp
  have e2 : TensorProduct.map L f = (f.lTensor N') ∘ₗ (L.rTensor A) := by
    ext n a; simp
  have hmap : Function.Injective (TensorProduct.map L f) := e1 ▸ hRB.comp hcrux
  rw [e2] at hmap
  simp only [LinearMap.coe_comp] at hmap
  exact hmap.of_comp

/-! ## [T-ME] 00ME (Lemma 10.99.1): two-term local criterion (base case of 00MI)

`R → S` local hom of local rings, `S` Noetherian; `M` `R`-flat, `N` finite `S`-module, `u : N → M`
`R`-linear with `ū : N/𝔪N → M/𝔪M` injective ⟹ `u` injective and `M/u(N)` `R`-flat. 
Krull-intersection
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
    (q : PrimeSpectrum S) : Prop :=
  ∀ j, Function.Exact
    ((φ (j + 1)).baseChange (Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.comap (algebraMap R S)).map
        ((algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap R S))))
    ((φ j).baseChange (Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.comap (algebraMap R S)).map
        ((algebraMap S (Localization.AtPrime q.asIdeal)).comp (algebraMap R S))))

/-- Special-fibre complex `F_•/𝔪F_•` (mod the maximal ideal of a LOCAL `R`) is exact.  Hypothesis of
00MI. -/
def SpecialFibreExact (R : Type*) [CommRing R] [IsLocalRing R] {S : Type*} [CommRing S]
    [Algebra R S] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S)) : Prop :=
  ∀ j, Function.Exact
    ((φ (j + 1)).baseChange (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))
    ((φ j).baseChange (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)))

/-! ## [T-BE] 00N1 (Proposition 10.102.9): the Buchsbaum–Eisenbud acyclicity criterion —
MAKE-OR-BREAK

Over a local Noetherian ring, the complex is exact iff for each `i` in range `rankᵢ = rᵢ` and the
minor ideal `I_{rᵢ}(φᵢ)` is the whole ring or contains a regular sequence of length `i`.  Stated in
the "ranks given" form 00RB actually uses (00RB first fixes the ranks via 00MI, then invokes the
depth half).  The rank relation `rnk i + rnk (i+1) = rk i` on the resolution range encodes condition
(2)(a); the disjunction encodes (2)(b) (grade `≥ i`).  The HARD direction (⟸) is the acyclicity
theorem.

INDEXING (corrected 2026-07-08 — the original skeleton had an off-by-one, machine-refuted):
Lean `φ j : F_{j+1} → F_j`, so Stacks' `φᵢ` (the `i`-th differential `F_i → F_{i-1}`) is Lean `φ
(i-1)`.
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
old plan): the Stacks 00N1 `(1)⟹(2)` proof localises at each associated prime, uses that the
depth-`0`
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

/-- `reduceMap` is the base change conjugated by the pi–tensor equivalence: this is the ladder
square
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
    apply
    Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
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
complex has `I(φᵢ)` of grade `≥ i` (or `= ⊤`), for each interior index `1 ≤ i < e`.  Induction on
`i`:
pick a nonzerodivisor `x ∈ I(φᵢ)` avoiding the associated primes (Piece A + prime avoidance), reduce
the complex modulo `x` (00MZ) to the shifted complex over `S/x`, and prepend `x` to the
grade-`(i-1)`
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
regular sequence in `I(φᵢ)` (`gradeGE_cons_of_isSMulRegular` + `be_forward_gradeGE_aux`).  The `∨ =
⊤`
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

/-- **[Piece 3, proper-ideal core — grade⟹depth localised].**  If an ideal `I ⊆ S` has grade `≥ k`
and `I ⊆ 𝔮` for a prime `𝔮`, then `depth(S_𝔮) ≥ k`.  Localising the length-`k` regular sequence
(`Ideal.gradeGE_localize`) it stays a regular sequence in `I·S_𝔮 ⊆ 𝔪(S_𝔮)` (the unit-ideal disjunct
is excluded because `I ⊆ 𝔮`), i.e. a regular sequence witnessing `HasDepthGE S_𝔮 S_𝔮 k`.  This is
"a regular sequence in a proper ideal of a local ring lies in `𝔪`", the non-split half of Stacks
00N1's `depth(R) ≥ e`. -/
private theorem hasDepthGE_localization_of_gradeGE {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I : Ideal S) (k : ℕ) (hI : I.gradeGE k) (q : Ideal S) [q.IsPrime] (hIq : I ≤ q) :
    Module.HasDepthGE (Localization.AtPrime q) (Localization.AtPrime q) k := by
  have hle : I.map (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.map_mono hIq
  rcases Ideal.gradeGE_localize I q.primeCompl k hI with hg | htop
  · obtain ⟨rs, hlen, hreg, hmem⟩ := hg
    exact ⟨rs, hlen, hreg, fun x hx => hle (hmem x hx)⟩
  · exact absurd (top_le_iff.mp (htop ▸ hle)) (IsLocalRing.maximalIdeal.isMaximal _).ne_top

/-- **00N0 wrapper — single-block case.**  For a finite free complex over a local Noetherian ring
that is a *single block* `[0, e)` (`rk j ≠ 0` exactly for `j < e`) with `depth L ≥ e - 1` (the top
index), the acyclicity lemma applies verbatim at any interior spot `i`: exact at `F_{i+1}`, or its
homology has depth `≥ 1`.  Directly `acyclicityLemma_hasDepthGE_homology` with `M j = L^{rk j}`
(depth of the free `L^{rk j}` is `depth L ≥ j`, `Module.hasDepthGE_pi_of_hasDepthGE`). -/
private theorem localAcyclicity_block {L : Type*} [CommRing L] [IsLocalRing L] [IsNoetherianRing L]
    (e : ℕ) (rk : ℕ → ℕ) (hrk : ∀ j, e ≤ j → rk j = 0) (hnz : ∀ j, j < e → rk j ≠ 0)
    (φ : (j : ℕ) → (Fin (rk (j + 1)) → L) →ₗ[L] (Fin (rk j) → L))
    (hcomplex : ∀ j, (φ j) ∘ₗ (φ (j + 1)) = 0)
    (hdepthL : Module.HasDepthGE L L (e - 1))
    (i : ℕ) (hie : i + 1 < e)
    (habove : ∀ j, i < j → Function.Exact (φ (j + 1)) (φ j)) :
    Function.Exact (φ (i + 1)) (φ i) ∨
      Module.HasDepthGE L (LinearMap.ker (φ i) ⧸
        (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype) 1 := by
  refine acyclicityLemma_hasDepthGE_homology (fun j => Fin (rk j) → L) φ hcomplex (e - 1)
    (fun j hj => ?_) (fun j hj => ?_) i (by omega) habove
  · haveI : IsEmpty (Fin (rk j)) := by rw [hrk j (by omega)]; infer_instance
    exact ⟨fun a b => funext fun x => isEmptyElim x⟩
  · exact Module.hasDepthGE_pi_of_hasDepthGE L (Nat.pos_of_ne_zero (hnz j (by omega))) j
      (Module.hasDepthGE_mono L hdepthL (by omega))

/-- **[Piece 1, no-gap shift].**  Reduces the interior spot `i` to spot `0` by re-indexing
`k ↦ i + k`: since `i + (k+1) ≡ (i+k)+1` and `i + 0 ≡ i` *definitionally*, the shifted complex
`k ↦ φ (i+k)` needs no casts and its spot-`0` homology is *definitionally* the spot-`i` homology of
`φ`.  If the block above `i` reaches the top with no gap (`rk j ≠ 0` for `i ≤ j < e`) and
`depth L ≥ e - i - 1`, `localAcyclicity_block` applies to the shift. -/
private theorem localAcyclicity_shift {L : Type*} [CommRing L] [IsLocalRing L] [IsNoetherianRing L]
    (e : ℕ) (rk : ℕ → ℕ) (hrk : ∀ j, e ≤ j → rk j = 0)
    (φ : (j : ℕ) → (Fin (rk (j + 1)) → L) →ₗ[L] (Fin (rk j) → L))
    (hcomplex : ∀ j, (φ j) ∘ₗ (φ (j + 1)) = 0)
    (i : ℕ) (hie : i + 1 < e)
    (hnz : ∀ j, i ≤ j → j < e → rk j ≠ 0)
    (hdepthL : Module.HasDepthGE L L (e - i - 1))
    (habove : ∀ j, i < j → Function.Exact (φ (j + 1)) (φ j)) :
    Function.Exact (φ (i + 1)) (φ i) ∨
      Module.HasDepthGE L (LinearMap.ker (φ i) ⧸
        (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype) 1 := by
  have key := localAcyclicity_block (L := L) (e - i) (fun k => rk (i + k))
    (fun k hk => hrk (i + k) (by omega)) (fun k hk => hnz (i + k) (by omega) (by omega))
    (fun k => φ (i + k)) (fun k => hcomplex (i + k)) hdepthL 0 (by omega)
    (fun k hk => habove (i + k) (by omega))
  simpa using key

/-- **[Piece 2 sub-lemma — free-module localisation iso].**  `(Fin n → S)_𝔮 ≅ (Fin n → S_𝔮)`, i.e.
localisation commutes with finite products (`IsLocalizedModule.pi` + `IsLocalizedModule.iso`). -/
private noncomputable def freeLocEquiv {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime] (n : ℕ) :
    LocalizedModule q.primeCompl (Fin n → S) ≃ₗ[S] (Fin n → Localization.AtPrime q) :=
  IsLocalizedModule.iso q.primeCompl
    (LinearMap.pi fun k => (Algebra.linearMap S (Localization.AtPrime q)).comp (LinearMap.proj k))

section LocalizedHomologyTransport

open Submodule LinearMap IsLocalizedModule Matrix

variable {R : Type*} [CommRing R] (p : Submonoid R)
variable {F G P Fq Gq Pq : Type*}
  [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G] [AddCommGroup P] [Module R P]
  [AddCommGroup Fq] [Module R Fq] [Module (Localization p) Fq] [IsScalarTower R (Localization p) Fq]
  [AddCommGroup Gq] [Module R Gq] [Module (Localization p) Gq] [IsScalarTower R (Localization p) Gq]
  [AddCommGroup Pq] [Module R Pq] [Module (Localization p) Pq] [IsScalarTower R (Localization p) Pq]
  (LF : F →ₗ[R] Fq) [IsLocalizedModule p LF]
  (LG : G →ₗ[R] Gq) [IsLocalizedModule p LG]
  (LP : P →ₗ[R] Pq) [IsLocalizedModule p LP]
  (φi : F →ₗ[R] G) (φi1 : P →ₗ[R] F)
  (ψi : Fq →ₗ[Localization p] Gq) (ψi1 : Pq →ₗ[Localization p] Fq)

/-- **[Transport, abstract core — localisation commutes with homology].**  Two-term complexes
`P --φi1--> F --φi--> G` (over `R`) and `Pq --ψi1--> Fq --ψi--> Gq` (over `Rₚ`) that are related by
localisation maps `LF, LG, LP` intertwining `ψ` with `φ` (`hnat_i`, `hnat_i1`): the localisation of
the `φ`-homology at `F` is the `ψ`-homology at `Fq`, as `Rₚ`-modules.  Assembled from the localised
submodule API: `Submodule.toLocalizedQuotient'` (localisation of a quotient is a localisation),
`LinearMap.localized'_range_eq_range_localizedMap` (localisation commutes with ranges) and
`LinearMap.ker_localizedMap_eq_localized'_ker` (with kernels); the localised maps are `ψ` by the
uniqueness `IsLocalizedModule.linearMap_ext`, and the `R`-linear equiv is upgraded to `Rₚ`-linear by
`LinearEquiv.extendScalarsOfIsLocalization`. -/
private noncomputable def localizedHomologyTransport
    (hc : ∀ x, φi (φi1 x) = 0)
    (hnat_i : ∀ x, ψi (LF x) = LG (φi x))
    (hnat_i1 : ∀ x, ψi1 (LP x) = LF (φi1 x)) :
    LocalizedModule p (ker φi ⧸ (range φi1).comap (ker φi).subtype)
      ≃ₗ[Localization p] (ker ψi ⧸ (range ψi1).comap (ker ψi).subtype) := by
  classical
  have hmapi : IsLocalizedModule.map p LF LG φi = ψi.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext p LF LG
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply,
      LinearMap.coe_restrictScalars]
    exact (hnat_i x).symm
  have hkerEq : (ker φi).localized' (Localization p) p LF = ker ψi := by
    apply Submodule.restrictScalars_injective R
    rw [← LinearMap.ker_localizedMap_eq_localized'_ker (Localization p) p LF LG φi, hmapi,
      LinearMap.ker_restrictScalars]
  have hmem : ∀ x, φi1 x ∈ ker φi := fun x => LinearMap.mem_ker.mpr (hc x)
  have hcomp0 : ∀ y, ψi (ψi1 y) = 0 := by
    have h0 : ((ψi ∘ₗ ψi1).restrictScalars R) = (0 : Pq →ₗ[R] Gq) := by
      apply IsLocalizedModule.linearMap_ext p LP LG
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
        LinearMap.zero_comp, LinearMap.zero_apply]
      rw [hnat_i1, hnat_i, hc v, map_zero]
    intro y
    simpa using DFunLike.congr_fun h0 y
  have hmem' : ∀ y, ψi1 y ∈ ker ψi := fun y => LinearMap.mem_ker.mpr (hcomp0 y)
  set g := φi1.codRestrict (ker φi) hmem with hg
  set g' := ψi1.codRestrict (ker ψi) hmem' with hg'
  set e : (ker φi).localized' (Localization p) p LF ≃ₗ[Localization p] ker ψi :=
    LinearEquiv.ofEq _ _ hkerEq with he
  set Lker : (ker φi) →ₗ[R] (ker ψi) :=
    (e.restrictScalars R) ∘ₗ Submodule.toLocalized' (Localization p) p LF (ker φi) with hLker
  haveI : IsLocalizedModule p Lker := by
    rw [hLker]; exact IsLocalizedModule.of_linearEquiv _ _ _
  have Lker_coe : ∀ w : ker φi, (Lker w : Fq) = LF (w : F) := by
    intro w
    rw [hLker]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.coe_coe, he, LinearEquiv.coe_ofEq_apply, Submodule.toLocalized',
      Submodule.toLocalized₀]
    rfl
  have hmap_g : (IsLocalizedModule.map p LP Lker g).extendScalarsOfIsLocalization p (Localization p)
      = g' := by
    apply LinearMap.restrictScalars_injective R
    rw [LinearMap.restrictScalars_extendScalarsOfIsLocalization]
    apply IsLocalizedModule.linearMap_ext p LP Lker
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, IsLocalizedModule.map_apply,
      LinearMap.coe_restrictScalars, Lker_coe, hg, hg', LinearMap.codRestrict_apply]
    exact (hnat_i1 v).symm
  have hcrux : ((range φi1).comap (ker φi).subtype).localized' (Localization p) p Lker
      = (range ψi1).comap (ker ψi).subtype := by
    rw [← LinearMap.range_codRestrict (ker φi) φi1 hmem, ← hg,
      LinearMap.localized'_range_eq_range_localizedMap (Localization p) p LP Lker g, hmap_g, hg',
      LinearMap.range_codRestrict]
  let π := Submodule.toLocalizedQuotient' (Localization p) p Lker
    ((range φi1).comap (ker φi).subtype)
  have e0 := IsLocalizedModule.iso p π
  exact ((e0 ≪≫ₗ (Submodule.quotEquivOfEq _ _ hcrux).restrictScalars
  R).extendScalarsOfIsLocalization
    p (Localization p))

variable {S : Type*} [CommRing S]

/-- Free localisation map `(Fin n → S) → (Fin n → S_𝔮)` (the map underlying `freeLocEquiv`). -/
@[reducible] private noncomputable def freeLocMap (q : Ideal S) [q.IsPrime] (n : ℕ) :
    (Fin n → S) →ₗ[S] (Fin n → Localization.AtPrime q) :=
  LinearMap.pi fun k => (Algebra.linearMap S (Localization.AtPrime q)).comp (LinearMap.proj k)

private lemma freeLocMap_apply (q : Ideal S) [q.IsPrime] (n : ℕ) (v : Fin n → S) (k : Fin n) :
    freeLocMap q n v k = algebraMap S (Localization.AtPrime q) (v k) := rfl

/-- `reduceMap` is the localised map: it intertwines the free localisation maps `freeLocMap`.  This
is the naturality that turns the abstract `localizedHomologyTransport` into a statement about the
concrete `reduceMap`-complex. -/
private lemma reduceMap_freeLocMap_naturality {a b : ℕ} (q : Ideal S) [q.IsPrime]
    (φ : (Fin a → S) →ₗ[S] (Fin b → S)) (v : Fin a → S) :
    reduceMap (Localization.AtPrime q) φ (freeLocMap q a v) = freeLocMap q b (φ v) := by
  funext l
  rw [reduceMap_apply, freeLocMap_apply, show (φ v) = LinearMap.toMatrix' φ *ᵥ v from
    (LinearMap.toMatrix'_mulVec φ v).symm]
  rw [RingHom.map_mulVec (algebraMap S (Localization.AtPrime q)) (LinearMap.toMatrix' φ) v l]
  rfl

/-- **[Transport lemma — the localised homology is the `reduceMap`-homology].**  For the finite free
complex `φ` and any prime `𝔮`, the abstract homology `(ker (φ i) / im (φ (i+1)))` localised at `𝔮`
is
`Localization.AtPrime 𝔮`-linearly isomorphic to the homology of the *localised* complex
`ψ j = reduceMap (Localization.AtPrime 𝔮) (φ j)` at the same spot.  This is the make-or-break
connective that lets the acyclicity wrapper `localAcyclicity_shift` (phrased over `reduceMap`) serve
the abstract-localised residual of `be_backward_localizedHomology_depth`: transport `Subsingleton` /
`HasDepthGE` across it. -/
private noncomputable def be_localizedHomology_reduceMapEquiv (rk : ℕ → ℕ)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (i : ℕ) (𝔮 : Ideal S) [𝔮.IsPrime] :
    LocalizedModule 𝔮.primeCompl
        (LinearMap.ker (φ i) ⧸
          (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype)
      ≃ₗ[Localization.AtPrime 𝔮]
        (LinearMap.ker (reduceMap (Localization.AtPrime 𝔮) (φ i)) ⧸
          (LinearMap.range (reduceMap (Localization.AtPrime 𝔮) (φ (i + 1)))).comap
            (LinearMap.ker (reduceMap (Localization.AtPrime 𝔮) (φ i))).subtype) :=
  localizedHomologyTransport 𝔮.primeCompl
    (freeLocMap 𝔮 (rk (i + 1))) (freeLocMap 𝔮 (rk i)) (freeLocMap 𝔮 (rk (i + 2)))
    (φ i) (φ (i + 1))
    (reduceMap (Localization.AtPrime 𝔮) (φ i)) (reduceMap (Localization.AtPrime 𝔮) (φ (i + 1)))
    (fun x => by rw [← LinearMap.comp_apply, hcomplex i, LinearMap.zero_apply])
    (fun x => reduceMap_freeLocMap_naturality 𝔮 (φ i) x)
    (fun x => reduceMap_freeLocMap_naturality 𝔮 (φ (i + 1)) x)

end LocalizedHomologyTransport

universe u

/-- A grade-`≥ k` ideal contained in the maximal ideal of a local ring witnesses `depth ≥ k`: its
regular sequence lies in `𝔪`.  (The already-localised analogue of
`hasDepthGE_localization_of_gradeGE`,
consuming the grade condition *after* it has been transported to the local ring `L = S_𝔮`.) -/
private theorem hasDepthGE_of_gradeGE_le_maximalIdeal {L : Type*} [CommRing L] [IsLocalRing L]
    {I : Ideal L} {k : ℕ} (h : I.gradeGE k) (hI : I ≤ IsLocalRing.maximalIdeal L) :
    Module.HasDepthGE L L k := by
  obtain ⟨rs, hlen, hreg, hmem⟩ := h
  exact ⟨rs, hlen, hreg, fun x hx => hI (hmem x hx)⟩

/-- Depth is a linear-equivalence invariant (a non-`private`-scoped copy of the transport used
inside
`ForMathlib.Acyclicity`): a regular sequence moves along `e : M ≃ₗ[L] N`
(`LinearEquiv.isRegular_congr`)
and membership in `𝔪` is unchanged.  Used to transport the depth disjunct across the
`be_localizedHomology_reduceMapEquiv` transport. -/
private theorem hasDepthGE_congr {L : Type u} [CommRing L] [IsLocalRing L]
    {M N : Type u} [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (e : M ≃ₗ[L] N) {k : ℕ} (h : Module.HasDepthGE L M k) : Module.HasDepthGE L N k := by
  obtain ⟨rs, hlen, hreg, hmem⟩ := h
  exact ⟨rs, hlen, (e.isRegular_congr rs).mp hreg, hmem⟩

/-- Reindexing equivalence of standard free modules from an equality of ranks. -/
private noncomputable def finPiLinearEquiv {L : Type*} [CommRing L] {a b : ℕ} (h : a = b) :
    (Fin a → L) ≃ₗ[L] (Fin b → L) :=
  LinearEquiv.piCongrLeft' L (fun _ => L) (finCongr h)

/-- **Homology transports across a ladder of linear equivalences.**  Two two-term complexes
`P₁ →g₁→ F₁ →f₁→ G₁` and `P₂ →g₂→ F₂ →f₂→ G₂` related by linear equivalences `eP, eF, eG` making both
squares commute have `L`-linearly isomorphic homologies `ker f / (range g).comap _` at the middle
spot.  This is the transport used to move the acyclicity disjunction between a complex and its
truncation / peel (whose modules differ by rank-equality reindexings). -/
private noncomputable def homologyLadderEquiv {L : Type*} [CommRing L]
    {P₁ F₁ G₁ P₂ F₂ G₂ : Type*}
    [AddCommGroup P₁] [Module L P₁] [AddCommGroup F₁] [Module L F₁] [AddCommGroup G₁] [Module L G₁]
    [AddCommGroup P₂] [Module L P₂] [AddCommGroup F₂] [Module L F₂] [AddCommGroup G₂] [Module L G₂]
    (g₁ : P₁ →ₗ[L] F₁) (f₁ : F₁ →ₗ[L] G₁) (g₂ : P₂ →ₗ[L] F₂) (f₂ : F₂ →ₗ[L] G₂)
    (eP : P₁ ≃ₗ[L] P₂) (eF : F₁ ≃ₗ[L] F₂) (eG : G₁ ≃ₗ[L] G₂)
    (sqf : f₂ ∘ₗ (eF : F₁ →ₗ[L] F₂) = (eG : G₁ →ₗ[L] G₂) ∘ₗ f₁)
    (sqg : g₂ ∘ₗ (eP : P₁ →ₗ[L] P₂) = (eF : F₁ →ₗ[L] F₂) ∘ₗ g₁) :
    (LinearMap.ker f₁ ⧸ (LinearMap.range g₁).comap (LinearMap.ker f₁).subtype) ≃ₗ[L]
      (LinearMap.ker f₂ ⧸ (LinearMap.range g₂).comap (LinearMap.ker f₂).subtype) := by
  have hsqf : ∀ x, f₂ (eF x) = eG (f₁ x) := fun x => by
    have := LinearMap.congr_fun sqf x; simpa using this
  have hsqg : ∀ p, g₂ (eP p) = eF (g₁ p) := fun p => by
    have := LinearMap.congr_fun sqg p; simpa using this
  -- `eF` maps `ker f₁` onto `ker f₂`.
  have hker : Submodule.map (eF : F₁ →ₗ[L] F₂) (LinearMap.ker f₁) = LinearMap.ker f₂ := by
    have h1 : Submodule.comap (eF : F₁ →ₗ[L] F₂) (LinearMap.ker f₂) = LinearMap.ker f₁ := by
      rw [← LinearMap.ker_comp, sqf, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    rw [← h1, Submodule.map_comap_eq_of_surjective eF.surjective]
  -- `eF` maps `range g₁` onto `range g₂`.
  have hrange : Submodule.map (eF : F₁ →ₗ[L] F₂) (LinearMap.range g₁) = LinearMap.range g₂ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      refine ⟨eP p, ?_⟩
      simp only [LinearEquiv.coe_coe]; rw [hsqg]
    · rintro _ ⟨p, rfl⟩
      refine ⟨g₁ (eP.symm p), ⟨eP.symm p, rfl⟩, ?_⟩
      simp only [LinearEquiv.coe_coe]; rw [← hsqg]; simp
  -- The induced iso on kernels, and its underlying action.
  set κ : (LinearMap.ker f₁) ≃ₗ[L] (LinearMap.ker f₂) :=
    (Submodule.equivMapOfInjective (eF : F₁ →ₗ[L] F₂) eF.injective (LinearMap.ker f₁)).trans
      (LinearEquiv.ofEq _ _ hker) with hκ
  have hκcoe : ∀ z : LinearMap.ker f₁, ((κ z : LinearMap.ker f₂) : F₂) = eF (z : F₁) := by
    intro z; rw [hκ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
      Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_coe]
  refine Submodule.Quotient.equiv _ _ κ (le_antisymm ?_ ?_)
  · rintro _ ⟨z, hz, rfl⟩
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe] at hz ⊢
    rw [hκcoe, ← hrange]
    exact Submodule.mem_map_of_mem (f := (eF : F₁ →ₗ[L] F₂)) hz
  · intro w hw
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hw
    have hcoe : ((κ.symm w : LinearMap.ker f₁) : F₁) = eF.symm (w : F₂) := by
      apply eF.injective; rw [← hκcoe]; simp
    have hg1 : eF.symm (w : F₂) ∈ LinearMap.range g₁ := by
      obtain ⟨q, hq, hqeq⟩ :=
        (hrange ▸ hw : (w : F₂) ∈ Submodule.map (eF : F₁ →ₗ[L] F₂) (LinearMap.range g₁))
      rw [← hqeq]; simpa using hq
    have hmemA1 : κ.symm w ∈ (LinearMap.range g₁).comap (LinearMap.ker f₁).subtype := by
      rw [Submodule.mem_comap, Submodule.coe_subtype, hcoe]; exact hg1
    have hmap := Submodule.mem_map_of_mem (f := (κ : LinearMap.ker f₁ →ₗ[L] LinearMap.ker f₂)) hmemA1
    simpa using hmap

@[simp] private lemma finPiLinearEquiv_rfl {L : Type*} [CommRing L] {a : ℕ} :
    finPiLinearEquiv (L := L) (rfl : a = a) = LinearEquiv.refl L (Fin a → L) := by
  ext v i
  simp [finPiLinearEquiv, LinearEquiv.piCongrLeft'_apply]

/-- Conjugating a map of standard free modules by rank-equality reindexings leaves its minor ideal
unchanged (proof: substitute the rank equalities, collapsing the reindexings to the identity). -/
private lemma idealOfMinors_finPiLinearEquiv_conj {L : Type*} [CommRing L] {a a' b b' : ℕ}
    (h₁ : a = a') (h₂ : b = b') (ψ : (Fin a' → L) →ₗ[L] (Fin b' → L)) (r : ℕ) :
    LinearMap.idealOfMinors r
        ((finPiLinearEquiv h₂).symm.toLinearMap ∘ₗ ψ ∘ₗ (finPiLinearEquiv h₁).toLinearMap)
      = LinearMap.idealOfMinors r ψ := by
  subst h₁; subst h₂
  have hid : (finPiLinearEquiv (L := L) (rfl : b = b)).symm.toLinearMap ∘ₗ ψ ∘ₗ
      (finPiLinearEquiv (L := L) (rfl : a = a)).toLinearMap = ψ := by simp
  rw [hid]

/-- The acyclicity disjunction `Exact ∨ depth ≥ 1` at the middle spot is a property of the homology
module alone: exactness is `Subsingleton` of the homology. -/
private lemma exact_iff_subsingleton_homology {L : Type*} [CommRing L]
    {P F G : Type*} [AddCommGroup P] [Module L P] [AddCommGroup F] [Module L F]
    [AddCommGroup G] [Module L G] (g : P →ₗ[L] F) (f : F →ₗ[L] G) (hc : f ∘ₗ g = 0) :
    Function.Exact g f ↔
      Subsingleton (LinearMap.ker f ⧸ (LinearMap.range g).comap (LinearMap.ker f).subtype) := by
  rw [LinearMap.exact_iff, Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  exact ⟨fun h => h.le, fun h => le_antisymm h (LinearMap.range_le_ker_iff.mpr hc)⟩

/-- **Transport the acyclicity disjunction across a ladder of linear equivalences.**  If two-term
complexes `P₁ →g₁→ F₁ →f₁→ G₁` and `P₂ →g₂→ F₂ →f₂→ G₂` are related by commuting linear equivalences,
the disjunction `Exact ∨ depth(homology) ≥ 1` transfers from the first to the second. -/
private theorem exact_or_depth_of_ladder {L : Type u} [CommRing L] [IsLocalRing L]
    {P₁ F₁ G₁ P₂ F₂ G₂ : Type u}
    [AddCommGroup P₁] [Module L P₁] [AddCommGroup F₁] [Module L F₁] [AddCommGroup G₁] [Module L G₁]
    [AddCommGroup P₂] [Module L P₂] [AddCommGroup F₂] [Module L F₂] [AddCommGroup G₂] [Module L G₂]
    (g₁ : P₁ →ₗ[L] F₁) (f₁ : F₁ →ₗ[L] G₁) (g₂ : P₂ →ₗ[L] F₂) (f₂ : F₂ →ₗ[L] G₂)
    (hc₁ : f₁ ∘ₗ g₁ = 0) (hc₂ : f₂ ∘ₗ g₂ = 0)
    (eP : P₁ ≃ₗ[L] P₂) (eF : F₁ ≃ₗ[L] F₂) (eG : G₁ ≃ₗ[L] G₂)
    (sqf : f₂ ∘ₗ (eF : F₁ →ₗ[L] F₂) = (eG : G₁ →ₗ[L] G₂) ∘ₗ f₁)
    (sqg : g₂ ∘ₗ (eP : P₁ →ₗ[L] P₂) = (eF : F₁ →ₗ[L] F₂) ∘ₗ g₁)
    (h : Function.Exact g₁ f₁ ∨
        Module.HasDepthGE L (LinearMap.ker f₁ ⧸
          (LinearMap.range g₁).comap (LinearMap.ker f₁).subtype) 1) :
    Function.Exact g₂ f₂ ∨
      Module.HasDepthGE L (LinearMap.ker f₂ ⧸
        (LinearMap.range g₂).comap (LinearMap.ker f₂).subtype) 1 := by
  have E := homologyLadderEquiv g₁ f₁ g₂ f₂ eP eF eG sqf sqg
  rcases h with hex | hd
  · left
    rw [exact_iff_subsingleton_homology g₂ f₂ hc₂]
    rw [exact_iff_subsingleton_homology g₁ f₁ hc₁] at hex
    exact (Equiv.subsingleton_congr E.toEquiv).mp hex
  · exact Or.inr (hasDepthGE_congr E hd)

/-- **[Core over the local ring `L` — the acyclicity disjunction].**  For the standard-free complex
`ψ` over a local Noetherian ring `L` with the (already localised) grade conditions `hcondL`, exact
at
every spot `> i`: either `ψ` is exact at `F_{i+1}` too, or the homology `ker(ψ i)/im(ψ (i+1))` has
`depth ≥ 1`.  This is Stacks 00N1 `(2)⟹(1)` over `L`, packaged so that
`be_backward_localizedHomology_depth` obtains it (over `L = S_𝔮`) and transports it back to the
abstract localised homology.  The interior no-gap block goes through `localAcyclicity_shift` with
the
depth supplied by the top proper minor ideal; the split (`= ⊤`) top differentials are peeled by the
00MW direct-summand argument. -/
private theorem localBE_homology_disjunction {L : Type*} [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (ψ : (i : ℕ) → (Fin (rk (i + 1)) → L) →ₗ[L] (Fin (rk i) → L))
    (hcomplex : ∀ i, (ψ i) ∘ₗ (ψ (i + 1)) = 0)
    (hcondL : ∀ k, 1 ≤ k → k ≤ e →
        (LinearMap.idealOfMinors (rnk k) (ψ (k - 1))).gradeGE k ∨
          LinearMap.idealOfMinors (rnk k) (ψ (k - 1)) = ⊤)
    (i : ℕ) (habove : ∀ j, i < j → Function.Exact (ψ (j + 1)) (ψ j)) :
    Function.Exact (ψ (i + 1)) (ψ i) ∨
      Module.HasDepthGE L (LinearMap.ker (ψ i) ⧸
        (LinearMap.range (ψ (i + 1))).comap (LinearMap.ker (ψ i)).subtype) 1 := by
  induction e using Nat.strong_induction_on generalizing rk rnk ψ hcomplex i habove with
  | _ e IH =>
  classical
  by_cases hi1 : rk (i + 1) = 0
  · -- `F_{i+1} = 0`, so the homology is a subquotient of `0`: the complex is exact at `F_{i+1}`.
    haveI : Subsingleton (Fin (rk (i + 1)) → L) := subsingleton_pi_fin_of_eq_zero hi1
    exact Or.inl (exact_of_subsingleton_mid _ _)
  · -- `rk (i+1) ≠ 0`, hence `i + 1 < e`.
    have hie : i + 1 < e := by by_contra h; exact hi1 (hrk (i + 1) (by omega))
    by_cases htop2 : rk (i + 2) = 0
    · -- **Top spot** `F_{i+2} = 0`: then `ψ (i+1) = 0` and `ψ i` is injective (maximal-minor McCoy
      -- from the grade condition at `i+1`, where `rnk (i+1) = rk (i+1)`), so the homology
      -- `ker (ψ i) / 0` vanishes — the complex is exact at `F_{i+1}`.
      have hrnk2 : rnk (i + 2) = 0 := by
        by_cases hle : e ≤ i + 2
        · exact hrnk_top (i + 2) hle
        · have h := hrnk (i + 2) (by omega) (by omega); omega
      have hrnk_eq : rnk (i + 1) = rk (i + 1) := by
        have h := hrnk (i + 1) (by omega) hie
        have h2 : rnk (i + 1 + 1) = 0 := hrnk2
        omega
      have hinj : Function.Injective (ψ i) := by
        apply injective_of_maxMinors_nonZeroDiv
        have hc := hcondL (i + 1) (by omega) (by omega)
        rw [show i + 1 - 1 = i from rfl, hrnk_eq] at hc
        rcases hc with hg | ht
        · refine Or.inl ?_
          obtain ⟨rs, hlen, hreg, hmem⟩ := hg
          have hne : rs ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen; omega
          obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
          rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
          exact ⟨r, hmem r (by simp), hreg.1⟩
        · exact Or.inr ht
      haveI : Subsingleton (Fin (rk (i + 2)) → L) := subsingleton_pi_fin_of_eq_zero htop2
      refine Or.inl ?_
      rw [LinearMap.exact_iff, LinearMap.ker_eq_bot.mpr hinj]
      symm
      rw [LinearMap.range_eq_bot]
      exact Subsingleton.elim _ _
    · -- `rk (i+2) ≠ 0`.
      -- **Trailing-zero reduction.**  If `rk (e-1) = 0`, the same complex has effective length
      -- `e-1`
      -- (its homology at `i` is unchanged), so the strong-induction hypothesis at `e-1` closes it.
      by_cases htz : rk (e - 1) = 0
      · have he1 : e - 1 + 1 = e := by omega
        have hrnk1 : rnk (e - 1) = 0 := by
          have h1 := hrnk (e - 1) (by omega) (by omega)
          rw [he1, htz] at h1
          have h2 := hrnk_top e le_rfl
          omega
        refine IH (e - 1) (by omega) rk rnk (fun j hj => ?_) (fun j hj => ?_)
          (fun j hj1 hj2 => hrnk j hj1 (by omega)) ψ hcomplex
          (fun k hk1 hk2 => hcondL k hk1 (by omega)) i habove
        · rcases eq_or_lt_of_le hj with rfl | h
          · exact htz
          · exact hrk j (by omega)
        · rcases eq_or_lt_of_le hj with rfl | h
          · exact hrnk1
          · exact hrnk_top j (by omega)
      · -- `rk (e-1) ≠ 0`: the length `e` is tight.
        by_cases hgap : ∀ j, i ≤ j → j < e → rk j ≠ 0
        · -- **No gaps in `[i, e)`.**
          by_cases htop : LinearMap.idealOfMinors (rnk (e - 1)) (ψ (e - 1 - 1)) = ⊤
          · -- **Split (`= ⊤`) top differential: peel it (Stacks 00MW).**
            -- RESIDUAL (peel): over the local ring `L`, `idealOfMinors (rnk (e-1)) (ψ (e-2)) = ⊤`
            -- with `rnk (e-1) = rk (e-1)` (the maximal *column* minors) means some `rk(e-1)×rk(e-1)`
            -- minor of `ψ (e-2)` is a unit, so `ψ (e-2) : L^{rk(e-1)} → L^{rk(e-2)}` is *split*
            -- injective with free cokernel `C ≅ L^{rk(e-2)-rk(e-1)}`.  Peel the trivial subcomplex
            -- `0 → L^{rk(e-1)} →≅→ (image) → 0` off the top: the complement is a length-`(e-1)`
            -- BE-complex with the *same* homology at spot `i`, closed by `IH (e-1)` and transported
            -- back with `exact_or_depth_of_ladder`.  Needs the cokernel-basis identification +
            -- the factoring `ψ (e-3) = χ (e-3) ∘ π` (`π : F_{e-2} ↠ C`).
            sorry
          · -- **Proper top minor ideal** ⟹ `depth L ≥ e-1 ≥ e-i-1`, then `localAcyclicity_shift`.
            have hgrade : (LinearMap.idealOfMinors (rnk (e - 1)) (ψ (e - 1 - 1))).gradeGE (e - 1) :=
            by
              rcases hcondL (e - 1) (by omega) (by omega) with hg | ht
              · exact hg
              · exact absurd ht htop
            have hdepth : Module.HasDepthGE L L (e - i - 1) :=
              Module.hasDepthGE_mono (R := L)
                (hasDepthGE_of_gradeGE_le_maximalIdeal hgrade (IsLocalRing.le_maximalIdeal htop))
                (by omega)
            exact localAcyclicity_shift e rk hrk ψ hcomplex i hie hgap hdepth habove
        · -- **Gap in `[i, e)`.**  Either there is a zero above `i + 2` (truncate the complex there
          -- and apply `IH`), or the only zero is at `i` itself — the cokernel case, in which the
          -- complex is gap-free above `i`.
          by_cases hgap3 : ∃ j₀, i + 3 ≤ j₀ ∧ j₀ < e ∧ rk j₀ = 0
          · -- **Gap `j₀ ≥ i + 3`: truncate at `j₀`, apply `IH`** (independent of `rk i`).
            obtain ⟨j₀, hj₀lb, hj₀e, hrkj₀⟩ := hgap3
            have hrnkj₀ : rnk j₀ = 0 := by
              have h := hrnk j₀ (by omega) hj₀e; rw [hrkj₀] at h; omega
            set rk' : ℕ → ℕ := fun k => if k < j₀ then rk k else 0 with hrk'def
            set rnk' : ℕ → ℕ := fun k => if k < j₀ then rnk k else 0 with hrnk'def
            have hrk'_eq : ∀ k, k ≤ j₀ → rk' k = rk k := by
              intro k hk
              rcases eq_or_lt_of_le hk with rfl | hlt
              · simp only [hrk'def, lt_irrefl, if_false]; exact hrkj₀.symm
              · simp only [hrk'def, if_pos hlt]
            have hrnk'_eq : ∀ k, k ≤ j₀ → rnk' k = rnk k := by
              intro k hk
              rcases eq_or_lt_of_le hk with rfl | hlt
              · simp only [hrnk'def, lt_irrefl, if_false]; exact hrnkj₀.symm
              · simp only [hrnk'def, if_pos hlt]
            have hrk'_IH : ∀ k, j₀ ≤ k → rk' k = 0 := by
              intro k hk
              rcases eq_or_lt_of_le hk with rfl | h
              · simp only [hrk'def, lt_irrefl, if_false]
              · simp only [hrk'def, if_neg (by omega : ¬ k < j₀)]
            have hrnk_top'_IH : ∀ k, j₀ ≤ k → rnk' k = 0 := by
              intro k hk
              rcases eq_or_lt_of_le hk with rfl | h
              · simp only [hrnk'def, lt_irrefl, if_false]
              · simp only [hrnk'def, if_neg (by omega : ¬ k < j₀)]
            set ψ' : (k : ℕ) → (Fin (rk' (k + 1)) → L) →ₗ[L] (Fin (rk' k) → L) := fun k =>
              if h : k + 1 ≤ j₀ then
                (finPiLinearEquiv (hrk'_eq k (by omega))).symm.toLinearMap ∘ₗ ψ k ∘ₗ
                  (finPiLinearEquiv (hrk'_eq (k + 1) h)).toLinearMap
              else 0 with hψ'def
            have hψ'_conj : ∀ k (h : k + 1 ≤ j₀), ψ' k =
                (finPiLinearEquiv (hrk'_eq k (by omega))).symm.toLinearMap ∘ₗ ψ k ∘ₗ
                  (finPiLinearEquiv (hrk'_eq (k + 1) h)).toLinearMap := by
              intro k h; rw [hψ'def]; exact dif_pos h
            have hψ'_zero : ∀ k, j₀ < k + 1 → ψ' k = 0 := by
              intro k h; rw [hψ'def]; exact dif_neg (by omega)
            have hsq : ∀ k (h : k + 1 ≤ j₀),
                ψ k ∘ₗ (finPiLinearEquiv (hrk'_eq (k + 1) h)).toLinearMap
                  = (finPiLinearEquiv (hrk'_eq k (by omega))).toLinearMap ∘ₗ ψ' k := by
              intro k h; rw [hψ'_conj k h]; ext v; simp
            have hrnk'_IH : ∀ k, 1 ≤ k → k < j₀ → rnk' k + rnk' (k + 1) = rk' k := by
              intro k hk1 hklt
              rw [hrnk'_eq k (by omega), hrnk'_eq (k + 1) (by omega), hrk'_eq k (by omega)]
              exact hrnk k hk1 (by omega)
            have hcomplex'_IH : ∀ k, ψ' k ∘ₗ ψ' (k + 1) = 0 := by
              intro k
              by_cases hk : k + 1 + 1 ≤ j₀
              · rw [hψ'_conj k (by omega), hψ'_conj (k + 1) hk]
                ext v
                simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearEquiv.coe_coe,
                  LinearEquiv.apply_symm_apply]
                rw [← LinearMap.comp_apply, hcomplex k, LinearMap.zero_apply, map_zero]
              · rw [hψ'_zero (k + 1) (by omega), LinearMap.comp_zero]
            have hcondL'_IH : ∀ k, 1 ≤ k → k ≤ j₀ →
                (LinearMap.idealOfMinors (rnk' k) (ψ' (k - 1))).gradeGE k ∨
                  LinearMap.idealOfMinors (rnk' k) (ψ' (k - 1)) = ⊤ := by
              intro k hk1 hkj₀
              rw [hrnk'_eq k hkj₀, hψ'_conj (k - 1) (by omega), idealOfMinors_finPiLinearEquiv_conj]
              exact hcondL k hk1 (by omega)
            have habove'_IH : ∀ j, i < j → Function.Exact (ψ' (j + 1)) (ψ' j) := by
              intro j hj
              by_cases hj2 : j + 1 + 1 ≤ j₀
              · exact (Function.Exact.iff_of_ladder_linearEquiv (hsq (j + 1) hj2)
                  (hsq j (by omega))).mp (habove j hj)
              · haveI : Subsingleton (Fin (rk' (j + 1)) → L) :=
                  subsingleton_pi_fin_of_eq_zero (hrk'_IH (j + 1) (by omega))
                exact exact_of_subsingleton_mid _ _
            have IH_res := IH j₀ hj₀e rk' rnk' hrk'_IH hrnk_top'_IH hrnk'_IH ψ' hcomplex'_IH
              hcondL'_IH i habove'_IH
            exact exact_or_depth_of_ladder (ψ' (i + 1)) (ψ' i) (ψ (i + 1)) (ψ i)
              (hcomplex'_IH i) (hcomplex i)
              (finPiLinearEquiv (hrk'_eq (i + 2) (by omega)))
              (finPiLinearEquiv (hrk'_eq (i + 1) (by omega)))
              (finPiLinearEquiv (hrk'_eq i (by omega)))
              (hsq i (by omega)) (hsq (i + 1) (by omega)) IH_res
          · -- **No zero above `i + 2`.**  With `rk (i+1), rk (i+2) ≠ 0` and a zero in `[i, e)`
            -- (`hgap`), the zero is forced to be at `i`: the **cokernel case** `rk i = 0`, with the
            -- complex gap-free above `i`.
            rw [not_forall] at hgap
            obtain ⟨jg, hjg⟩ := hgap
            push_neg at hjg
            obtain ⟨hijg, hjge, hrkjg⟩ := hjg
            push_neg at hgap3
            have hi0 : rk i = 0 := by
              rcases (show jg = i ∨ jg = i + 1 ∨ jg = i + 2 ∨ i + 3 ≤ jg by omega)
                with rfl | rfl | rfl | h
              · exact hrkjg
              · exact absurd hrkjg hi1
              · exact absurd hrkjg htop2
              · exact absurd hrkjg (hgap3 jg h hjge)
            have hnz : ∀ j, i + 1 ≤ j → j < e → rk j ≠ 0 := by
              intro j hj1 hje'
              rcases (show j = i + 1 ∨ j = i + 2 ∨ i + 3 ≤ j by omega) with rfl | rfl | h
              · exact hi1
              · exact htop2
              · exact hgap3 j h hje'
            -- `ψ i = 0` (its target `F_i = L^{rk i}` is `0`), so `ker (ψ i) = ⊤` and the homology at
            -- spot `i` is the cokernel `coker (ψ (i+1)) = F_{i+1} / im (ψ (i+1))`.
            haveI hFi0 : Subsingleton (Fin (rk i) → L) := subsingleton_pi_fin_of_eq_zero hi0
            have hψi0 : ψ i = 0 := Subsingleton.elim _ _
            -- `hcondL (i+1)` forces `rnk (i+1) = 0`: otherwise the `rnk (i+1)`-minor ideal of the
            -- zero-row map `ψ i` (matrix with `rk i = 0` rows) is `⊥`, which is neither of grade
            -- `≥ i+1` nor `⊤` over the nontrivial local ring `L`.
            have hrnki1 : rnk (i + 1) = 0 := by
              by_contra hrne
              have hpos : 0 < rnk (i + 1) := Nat.pos_of_ne_zero hrne
              have hbot : LinearMap.idealOfMinors (rnk (i + 1)) (ψ i) = ⊥ := by
                rw [LinearMap.idealOfMinors_eq, Matrix.idealOfMinors_eq_bot_iff]
                intro ri ci
                haveI : IsEmpty (Fin (rk i)) := by rw [hi0]; infer_instance
                exact isEmptyElim (ri ⟨0, hpos⟩)
              have hc := hcondL (i + 1) (by omega) (by omega)
              rw [show i + 1 - 1 = i from rfl, hbot] at hc
              rcases hc with hg | ht
              · obtain ⟨rs, hlen, hreg, hmem⟩ := hg
                have hne : rs ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen; omega
                obtain ⟨r, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
                have hr0 : r = 0 := Ideal.mem_bot.mp (hmem r (by simp))
                rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
                have hreg1 : IsSMulRegular L r := hreg.1
                rw [hr0] at hreg1
                exact zero_ne_one (hreg1 (show (0 : L) • (0 : L) = (0 : L) • (1 : L) by simp))
              · exact absurd ht (by simp [bot_ne_top])
            -- Hence `rnk (i+2) = rk (i+1)`, so `hcondL (i+2)` is about the maximal minors of `ψ (i+1)`.
            have hrnki2 : rnk (i + 2) = rk (i + 1) := by
              have h := hrnk (i + 1) (by omega) hie
              rw [hrnki1, zero_add] at h; exact h
            -- RESIDUAL: the cokernel `coker (ψ (i+1))` is subsingleton (⟹ exact) or has depth ≥ 1.
            -- The maximal minors `idealOfMinors (rk (i+1)) (ψ (i+1))` (from `hcondL (i+2)`) are `⊤`
            -- (⟹ `ψ (i+1)` surjective ⟹ cokernel `= 0`) or of grade `≥ i+2` (⟹ depth of the
            -- cokernel `≥ 1` via the acyclicity lemma over the gap-free block `[i+1, e)`).
            sorry

/-- **[RESIDUAL — the grade-via-primes depth bridge; Stacks 00N1 (2)⟹(1) last paragraph + 00N0]**
The single genuinely mathlib+branch-absent step of the backward acyclicity criterion, isolated.

For the Buchsbaum–Eisenbud free complex with grade conditions `hcond`, exact at every spot `> i`,
and ANY prime `𝔮`: the homology `H = ker(φ i)/im(φ (i+1))` at spot `F_{i+1}` localised at `𝔮`
either vanishes or has `depth_{S_𝔮} ≥ 1`.

This is the acyclicity lemma **00N0** (`acyclicityLemma_hasDepthGE_homology`) applied over the local
ring `S_𝔮`, *transported to the abstract localised homology* `(H)_𝔮`.  Its free-module depth
hypothesis `depth(S_𝔮^{rk j}) ≥ j` (needed by 00N0, via `Module.hasDepthGE_pi_of_hasDepthGE`) is the
**grade-via-primes bridge**: the grade conditions localise (`Ideal.gradeGE_localize`), and where the
localised minor ideal is proper (`⊆ 𝔪(S_𝔮)`) of grade `≥ j` one gets `depth(S_𝔮) ≥ j` (a regular
sequence in a proper ideal is a regular sequence in `𝔪`); this is exactly Stacks 00N1's
"`(2)(b)` implies `depth(R) ≥ e`", whose full proof also handles the split (`= ⊤`) top differentials
by the direct-sum splitting 00MW.  Everything *outside* this lemma in
`be_backward_exact_of_habove` — the associated-prime selection and the `depth (H)_𝔮 = 0` from
`𝔪(S_𝔮) ∈ Ass (H)_𝔮` — is discharged; only this remains.  Stacks 10.102.9 / 10.102.8. -/
private theorem be_backward_localizedHomology_depth {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤)
    (i : ℕ) (habove : ∀ j, i < j → Function.Exact (φ (j + 1)) (φ j))
    (𝔮 : Ideal S) [𝔮.IsPrime] :
    Subsingleton (LocalizedModule 𝔮.primeCompl
        (LinearMap.ker (φ i) ⧸
          (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype)) ∨
      Module.HasDepthGE (Localization.AtPrime 𝔮)
        (LocalizedModule 𝔮.primeCompl
          (LinearMap.ker (φ i) ⧸
            (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype)) 1 := by
  classical
  haveI : Module.Flat S (Localization.AtPrime 𝔮) :=
    IsLocalization.flat (Localization.AtPrime 𝔮) 𝔮.primeCompl
  -- The localised complex `ψ = reduceMap (S_𝔮) (φ ·)` over `L = S_𝔮`.
  set ψ : (j : ℕ) → (Fin (rk (j + 1)) → Localization.AtPrime 𝔮) →ₗ[Localization.AtPrime 𝔮]
      (Fin (rk j) → Localization.AtPrime 𝔮) := fun j => reduceMap (Localization.AtPrime 𝔮) (φ j)
    with hψ
  -- `ψ` is a complex.
  have hcomplexL : ∀ j, (ψ j) ∘ₗ (ψ (j + 1)) = 0 := fun j => by
    simp only [hψ, ← reduceMap_comp, hcomplex j, reduceMap_zero]
  -- `ψ` is exact above `i` (flat base change of `habove`).
  have haboveL : ∀ j, i < j → Function.Exact (ψ (j + 1)) (ψ j) := fun j hj =>
    exact_reduceMap_of_flat (Localization.AtPrime 𝔮) _ _ (habove j hj)
  -- The grade conditions localise (`Ideal.gradeGE_localize` + `idealOfMinors_reduceMap`).
  have hcondL : ∀ k, 1 ≤ k → k ≤ e →
      (LinearMap.idealOfMinors (rnk k) (ψ (k - 1))).gradeGE k ∨
        LinearMap.idealOfMinors (rnk k) (ψ (k - 1)) = ⊤ := by
    intro k hk1 hke
    have hmap : LinearMap.idealOfMinors (rnk k) (ψ (k - 1))
        = (LinearMap.idealOfMinors (rnk k) (φ (k - 1))).map
            (algebraMap S (Localization.AtPrime 𝔮)) := by
      simp only [hψ]; exact idealOfMinors_reduceMap _ _ _
    rw [hmap]
    rcases hcond k hk1 hke with hg | ht
    · exact Ideal.gradeGE_localize _ 𝔮.primeCompl k hg
    · exact Or.inr (by rw [ht, Ideal.map_top])
  -- The transport `(H)_𝔮 ≃ₗ[L] (reduceMap-homology)`.
  have transport := be_localizedHomology_reduceMapEquiv rk φ hcomplex i 𝔮
  rcases localBE_homology_disjunction e rk rnk hrk hrnk_top hrnk ψ hcomplexL hcondL i haboveL with
    hex | hd
  · -- Exact ⟹ the reduceMap-homology is subsingleton ⟹ `(H)_𝔮` is subsingleton (transport).
    refine Or.inl ?_
    have hsub : Subsingleton (LinearMap.ker (ψ i) ⧸
        (LinearMap.range (ψ (i + 1))).comap (LinearMap.ker (ψ i)).subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
      exact (LinearMap.exact_iff.mp hex).le
    exact (Equiv.subsingleton_congr transport.toEquiv).mpr hsub
  · -- Depth ≥ 1 for the reduceMap-homology ⟹ for `(H)_𝔮` (transport).
    exact Or.inr (hasDepthGE_congr transport.symm hd)

/-- **[BE backward core, per-spot acyclicity step]** Stacks 00N1, (2)⟹(1), at a single interior
spot, *given exactness at every higher spot* (`habove`).  This is the genuine acyclicity content:
the complex, exact above `F_{i+1}`, is exact at `F_{i+1}` too.

PROOF ROUTE (Stacks 00N1 `(2)⟹(1)`, via the acyclicity lemma 00N0 =
`acyclicityLemma_hasDepthGE_homology`,
NOT the stale "0AVQ / depth-invariant" route): write `H = ker(φ i)/im(φ (i+1))` for the homology at
`F_{i+1}`.  If `H ≠ 0`, pick an associated prime `𝔮 ∈ Ass_S H`; localise at `𝔮` (flat, keeps the
complex exact above `i` and keeps `H_𝔮 ≠ 0` with `𝔪(S_𝔮) ∈ Ass H_𝔮`, i.e. `depth H_𝔮 = 0`).  The
acyclicity lemma 00N0 over `S_𝔮` — whose free-module depth hypothesis `depth(S_𝔮^{rk j}) ≥ j` is
supplied by the grade conditions localised to `𝔮` (`Ideal.gradeGE_localize`), the **grade-via-primes
depth bridge** (Stacks 00N1 last paragraph: `I(φⱼ) ⊆ 𝔪` proper of grade `≥ j` ⟹ `depth ≥ j`) —
forces
`depth H_𝔮 ≥ 1`, contradicting `depth H_𝔮 = 0`.  Hence `H = 0`, i.e. exactness at `F_{i+1}`. -/
private theorem be_backward_exact_of_habove {S : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤)
    (i : ℕ) (habove : ∀ j, i < j → Function.Exact (φ (j + 1)) (φ j)) :
    Function.Exact (φ (i + 1)) (φ i) := by
  classical
  rw [LinearMap.exact_iff]
  refine le_antisymm ?_ (LinearMap.range_le_ker_iff.mpr (hcomplex i))
  rw [← Submodule.comap_subtype_eq_top, ← Submodule.Quotient.subsingleton_iff]
  -- The homology at `F_{i+1}`.
  set H := (LinearMap.ker (φ i)) ⧸
    (LinearMap.range (φ (i + 1))).comap (LinearMap.ker (φ i)).subtype with hHdef
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  haveI : Nontrivial H := hns
  -- `H` is a finite `S`-module (subquotient of the finite free `F_{i+1}`).
  haveI : IsNoetherian S (Fin (rk (i + 1)) → S) := inferInstance
  haveI : Module.Finite S (LinearMap.ker (φ i)) := inferInstance
  haveI : Module.Finite S H := inferInstance
  -- Pick an associated prime `𝔮 ∈ Ass_S H` and localise there.
  obtain ⟨𝔮, h𝔮⟩ := associatedPrimes.nonempty S H
  haveI h𝔮p : 𝔮.IsPrime := h𝔮.isPrime
  haveI : IsNoetherianRing (Localization.AtPrime 𝔮) :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance
  -- `H_𝔮 ≠ 0`, since `𝔮 ∈ Supp H` (`Ann H ≤ 𝔮`).
  haveI hH𝔮nt : Nontrivial (LocalizedModule 𝔮.primeCompl H) := by
    have hmem : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum S) ∈ Module.support S H := by
      rw [Module.mem_support_iff_of_finite]
      have hle := (AssociatedPrimes.mem_iff.mp h𝔮).annihilator_le
      rwa [Submodule.annihilator_top] at hle
    exact Module.mem_support_iff.mp hmem
  -- `𝔪(S_𝔮) ∈ Ass H_𝔮`, hence `depth H_𝔮 = 0`, i.e. `¬ HasDepthGE S_𝔮 H_𝔮 1`.
  have hmaxAss :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes (M := H) h𝔮
  have hnodepth :
      ¬ Module.HasDepthGE (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl H) 1 := by
    rw [Module.hasDepthGE_one_iff_notMem_associatedPrimes]
    exact fun h => h hmaxAss
  -- The residual: `H_𝔮` vanishes or has depth `≥ 1`; both contradict the above.
  rcases be_backward_localizedHomology_depth e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i habove 𝔮
    with hsub | hdepth
  · exact absurd hsub (not_subsingleton_iff_nontrivial.mpr hH𝔮nt)
  · exact hnodepth hdepth

/-- **[BE backward, all spots]** The backward direction at *every* spot, by strong downward
induction
on the spot index: exactness above `F_{i+1}` (the induction hypothesis, trivial once the free
modules
vanish) feeds `be_backward_exact_of_habove`. -/
private theorem be_backward_exact_all {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤) :
    ∀ i, Function.Exact (φ (i + 1)) (φ i) := by
  have key : ∀ n i, e - i = n → Function.Exact (φ (i + 1)) (φ i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hn
      rcases Nat.lt_or_ge (i + 1) e with hsmall | hbig
      · refine be_backward_exact_of_habove e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i
          (fun j hj => ?_)
        rcases Nat.lt_or_ge (j + 1) e with hjsmall | hjbig
        · exact ih (e - j) (by omega) j rfl
        · haveI : Subsingleton (Fin (rk (j + 1)) → S) :=
            subsingleton_pi_fin_of_eq_zero (hrk (j + 1) hjbig)
          exact exact_of_subsingleton_mid _ _
      · haveI : Subsingleton (Fin (rk (i + 1)) → S) :=
          subsingleton_pi_fin_of_eq_zero (hrk (i + 1) hbig)
        exact exact_of_subsingleton_mid _ _
  exact fun i => key (e - i) i rfl

/-- **[BE backward core]** Stacks 00N1, (2)⟹(1) — the deep interior spots.  Immediate from
`be_backward_exact_all` (which proves exactness at *all* spots); the `hi`/`htop` hypotheses marking
the deep interior are not needed once the general statement is available. -/
private theorem be_backward_core {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hcond : ∀ i, 1 ≤ i → i ≤ e →
        (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
          LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤)
    (i : ℕ) (_hi : rk (i + 1) ≠ 0) (_htop : rk (i + 2) ≠ 0) :
    Function.Exact (φ (i + 1)) (φ i) :=
  be_backward_exact_all e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i

/-- Forward direction, all indices: dispatches the trivial `rnk i = 0` conjunct (unit ideal) and the
interior indices to `be_forward_core`. -/
private theorem be_forward {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (_hie : i ≤ e) :
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

/-- [T-BE] Buchsbaum–Eisenbud (Stacks 00N1), depth half in ranks-given form (Lean `φ (i-1)` = Stacks
`φᵢ`). -/
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

#print axioms buchsbaumEisenbud_acyclic

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

/-! ## [T-MI] 00MI (Lemma 10.99.5): flatness of the cokernel from fibre-exactness — NO
Buchsbaum–Eisenbud

`0 → F_e → ⋯ → F₀` a finite complex of `R`-flat finite `S`-modules whose special fibre is exact ⟹
the complex is exact and `coker(F₁ → F₀)` is `R`-flat.  Induction on `e` from [T-ME] (00ME).  Stated
with an abstract cokernel target `M` (matching the application, where `M` is the finitely-presented
module), presented by `π : F₀ ↠ M` with `Function.Exact (φ 0) π`. -/

/-- [T-MI] Stacks 00MI: special-fibre-exact ⟹ the cokernel `M` of `φ 0 : F₁ → F₀` is `R`-flat. -/
theorem coker_flat_of_specialFibreExact {R S M : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Flat R
    S]
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
theorem flatLocus_spreads_reduce_to_polynomial {R S M : Type u} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation S M] {q : PrimeSpectrum S}
    (hq : q ∈ flatLocus R S M)
    (H : ∀ (P : Type u) [CommRing P] [Algebra R P] [Module.Free R P] [Algebra.FinitePresentation R P]
      (M' : Type u) [AddCommGroup M'] [Module R M'] [Module P M'] [IsScalarTower R P M']
      [Module.FinitePresentation P M'] (q' : PrimeSpectrum P), q' ∈ flatLocus R P M' →
        ∃ g : P, g ∉ q'.asIdeal ∧
          (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum P)) ⊆ flatLocus R P M') :
    ∃ g : S, g ∉ q.asIdeal ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆ flatLocus R S M := by
  classical
  -- Presentation `P = R[ι] ↠ S` with finitely generated kernel.  `iff_quotient_mvPolynomial'`
  -- packages the `ULift`-reindexed index `ι : Type u` (so `P : Type u`, avoiding the `max 0 u`
  -- universe of `MvPolynomial (Fin n) R`) together with the finitely-generated kernel.
  obtain ⟨ι, hιf, f, hf, hker⟩ :=
    (Algebra.FinitePresentation.iff_quotient_mvPolynomial'.{u, u, u} (R := R) (A := S)).mp
      inferInstance
  haveI := hιf
  letI : Algebra (MvPolynomial ι R) S := f.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  -- `M` as a `P`-module through `P → S`.
  letI : Module (MvPolynomial ι R) M := Module.compHom M (algebraMap (MvPolynomial ι R) S)
  haveI : IsScalarTower (MvPolynomial ι R) S M :=
    ⟨fun p s m => by rw [Algebra.smul_def]; exact mul_smul _ _ _⟩
  haveI : IsScalarTower R (MvPolynomial ι R) M :=
    ⟨fun r p m => by
      show algebraMap (MvPolynomial ι R) S (r • p) • m = r • (algebraMap _ S p • m)
      rw [Algebra.smul_def (R := R), map_mul,
        ← IsScalarTower.algebraMap_apply R (MvPolynomial ι R) S, mul_smul, algebraMap_smul]⟩
  haveI : Module.FinitePresentation (MvPolynomial ι R) S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap (MvPolynomial ι R) S) hf hker
  haveI : Module.FinitePresentation (MvPolynomial ι R) M :=
    Module.FinitePresentation.trans (MvPolynomial ι R) M S
  have hfsurj : Function.Surjective (algebraMap (MvPolynomial ι R) S) := hf
  -- The contracted prime `𝔮ᴾ` lands in the flat locus over `P` (localisation iso).
  have hqP : PrimeSpectrum.comap (algebraMap (MvPolynomial ι R) S) q ∈
      flatLocus R (MvPolynomial ι R) M := by
    rw [mem_flatLocus] at hq ⊢
    haveI := hq
    exact Module.Flat.of_linearEquiv (localizedModuleComapEquiv hfsurj q.asIdeal)
  -- Apply the polynomial-case hypothesis `H` and pull the basic open back to `Spec S`.
  obtain ⟨g', hg', hsub⟩ := H (MvPolynomial ι R) M _ hqP
  refine ⟨f g', ?_, ?_⟩
  · intro hmem
    exact hg' (show g' ∈ (PrimeSpectrum.comap (algebraMap _ S) q).asIdeal from hmem)
  · intro q'' hq''
    rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hq''
    have hmem : PrimeSpectrum.comap (algebraMap (MvPolynomial ι R) S) q'' ∈
        flatLocus R (MvPolynomial ι R) M := by
      apply hsub
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
      exact hq''
    rw [mem_flatLocus] at hmem ⊢
    haveI : Module.Flat R (LocalizedModule
        (q''.asIdeal.comap (algebraMap (MvPolynomial ι R) S)).primeCompl M) := hmem
    exact Module.Flat.of_linearEquiv (localizedModuleComapEquiv hfsurj q''.asIdeal).symm

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
