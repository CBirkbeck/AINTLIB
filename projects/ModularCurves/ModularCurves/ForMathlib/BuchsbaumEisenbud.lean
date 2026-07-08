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

/-- **[BE forward core]** Stacks 00N1, (1)⟹(2)(b), interior indices.  If the finite free complex is
exact (at every `F_{j+1}`) then for each interior index `1 ≤ i < e` the minor ideal
`I_{rnk i}(φ_{i-1})` (Stacks `I(φᵢ)`) is either the unit ideal or has grade `≥ i`.

MATHLIB-ABSENT CONTENT: the "exactness ⟹ depth of the minor ideals" half.  Classical proof:
`grade(I(φᵢ)) ≥ i ⟺ I(φᵢ) ⊄ 𝔭` for every `𝔭` with `depth R_𝔭 < i`; and at such `𝔭` the localised
resolution shortens past index `i` (`pd (M_𝔭) ≤ depth R_𝔭 < i` by Auslander–Buchsbaum), so
`(φᵢ)_𝔭` splits and `I(φᵢ)_𝔭 = R_𝔭`.  Needs `depth` + Auslander–Buchsbaum — both absent from mathlib
(no `Module.depth`; `RingTheory/Regular/Depth.lean` is a deprecated stub).  Stacks 00N1 / 0AVR. -/
private theorem be_forward_core {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : ℕ) (rk rnk : ℕ → ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → S) →ₗ[S] (Fin (rk i) → S))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (i : ℕ) (hi1 : 1 ≤ i) (hie : i < e) :
    (LinearMap.idealOfMinors (rnk i) (φ (i - 1))).gradeGE i ∨
      LinearMap.idealOfMinors (rnk i) (φ (i - 1)) = ⊤ := sorry

/-- **[BE backward core]** Stacks 00N1, (2)⟹(1) — the Peskine–Szpiro acyclicity lemma, interior
indices.  If for every `1 ≤ i ≤ e` the minor ideal `I_{rnk i}(φ_{i-1})` is the unit ideal or has
grade `≥ i`, then the complex is exact at every interior `F_{i+1}` (`rk (i+1) ≠ 0`).

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
    (i : ℕ) (hi : rk (i + 1) ≠ 0) :
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
  · exact be_backward_core e rk rnk hrk hrnk_top hrnk φ hcomplex hcond i h0

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
