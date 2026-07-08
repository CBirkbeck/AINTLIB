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

/-- **[T-ACYC.00MZ], reduced core.**  The complex reduced modulo `x` (via `QuotSMulTop x`, i.e.
`F • ↦ F/xF`) is exact at the interior spot `QuotSMulTop x F_{j+2}`, for every `j`.  This is the
honest content of Stacks 00MZ: exactness of the reduced complex at all spots `≥ 2` (the source
explicitly loses the bottom spot).  Direct diagram chase using the regularity of `x` on the free
term `F j`; no snake lemma needed.  Transported to the `baseChange` spelling in the main statement
below. -/
private theorem exact_map_quotSMulTop_of_isSMulRegular {R : Type u} [CommRing R] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → R) →ₗ[R] (Fin (rk i) → R))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (x : R) (hx : IsSMulRegular R x) (j : ℕ) :
    Function.Exact (QuotSMulTop.map x (φ (j + 2))) (QuotSMulTop.map x (φ (j + 1))) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · -- ker (map (φ (j+1))) ≤ range (map (φ (j+2))): the chase
    intro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    have hxw : (φ (j + 1)) v = x • w := hw.symm
    have h1 : (φ j) ((φ (j + 1)) v) = 0 := by
      have := LinearMap.congr_fun (hcomplex j) v; simpa using this
    rw [hxw, map_smul] at h1
    have hreg : IsSMulRegular (Fin (rk j) → R) x := IsSMulRegular.pi fun _ => hx
    have hw0 : (φ j) w = 0 := hreg (by simpa using h1)
    have hwr : w ∈ LinearMap.range (φ (j + 1)) := by
      rw [← LinearMap.exact_iff.mp (hexact j), LinearMap.mem_ker]; exact hw0
    obtain ⟨u, hu⟩ := hwr
    have h2 : (φ (j + 1)) (v - x • u) = 0 := by rw [map_sub, map_smul, hu, hxw, sub_self]
    have hvr : v - x • u ∈ LinearMap.range (φ (j + 2)) := by
      rw [← LinearMap.exact_iff.mp (hexact (j + 1)), LinearMap.mem_ker]; exact h2
    obtain ⟨t, ht⟩ := hvr
    refine ⟨Submodule.Quotient.mk t, ?_⟩
    rw [QuotSMulTop.map_apply_mk, ht, Submodule.Quotient.eq]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨-u, Submodule.mem_top, by rw [smul_neg]; abel⟩
  · -- range ≤ ker: the complex condition
    rw [LinearMap.range_le_ker_iff, ← QuotSMulTop.map_comp, hcomplex (j + 1), map_zero]

/-- **[T-ACYC.00MZ] Stacks 00MZ (Lemma 10.102.7).**  An exact finite free complex stays exact after
base change along `R → R/xR` for a nonzerodivisor `x` (snake lemma on `0 → F_• →ˣ F_• → F_•/xF_• → 0`).
The base-changed maps are `(φ i).baseChange (R ⧸ (x))`.

The reduced-complex core `exact_map_quotSMulTop_of_isSMulRegular` above gives exactness at every spot
`≥ 2` (the `i + 1 = j + 2` branch), transported here through
`QuotSMulTop.equivQuotTensor` (`M/xM ≃ (R/xR) ⊗ M`) and `LinearMap.baseChange_eq_ltensor`.

INDEXING (corrected 2026-07-08): the conclusion is stated at spots `≥ 2` — exactness at `(R/xR) ⊗ F_{i+2}`
for all `i` — because 00MZ loses the bottom spot: the source is exact only at `(R/xR)^{nₑ}, …, (R/xR)^{n₂}`.
The naïve `∀ i` form at `(φ (i+1))/(φ i)` is **false** at `i = 0` (the bottom spot `(R/xR) ⊗ F_1`) —
counterexample: `R = ℤ`, `x = 2`, complex `0 → ℤ →(·2)→ ℤ`; exact at `F 1` (ker(·2) = 0) but its reduction
`𝔽₂ →0→ 𝔽₂` is not exact at `𝔽₂`.  The consumer (`be_forward_core`'s induction on `e`) needs only spots
`≥ 2`, which the shifted conclusion supplies. -/
theorem exact_baseChange_quotient_of_isSMulRegular
    {R : Type u} [CommRing R] {rk : ℕ → ℕ}
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → R) →ₗ[R] (Fin (rk i) → R))
    (hcomplex : ∀ i, (φ i) ∘ₗ (φ (i + 1)) = 0)
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (x : R) (hx : IsSMulRegular R x) :
    ∀ i, Function.Exact
      ((φ (i + 2)).baseChange (R ⧸ Ideal.span {x}))
      ((φ (i + 1)).baseChange (R ⧸ Ideal.span {x})) := by
  intro i
  have key := exact_map_quotSMulTop_of_isSMulRegular φ hcomplex hexact x hx i
  have nat1 := QuotSMulTop.equivQuotTensor_naturality x (φ (i + 2))
  have nat2 := QuotSMulTop.equivQuotTensor_naturality x (φ (i + 1))
  exact (Function.Exact.iff_of_ladder_linearEquiv nat1.symm nat2.symm).mpr key

/-! ### Support lemmas for [T-ACYC.00MYW] (the socle-splitting of 00MY + the rank/McCoy of 00MW). -/

section IdealOfMinorsTopSupport

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

open TensorProduct IsLocalRing

/-- **Socle element (00MY input).**  `𝔪 ∈ Ass(R)` means `𝔪 = ann(s)` for some `s`: there is `s ≠ 0`
with `m ∈ 𝔪 ⟺ m·s = 0`. -/
private theorem socle_exists (hdepth0 : maximalIdeal R ∈ associatedPrimes R R) :
    ∃ s : R, s ≠ 0 ∧ ∀ m : R, m ∈ maximalIdeal R ↔ m * s = 0 := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hdepth0
  obtain ⟨hprime, s, hs⟩ := hdepth0
  refine ⟨s, ?_, ?_⟩
  · intro h; subst h
    apply hprime.ne_top
    rw [hs]; ext r; simp [Submodule.mem_colon_singleton]
  · intro m
    rw [hs, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]

omit [IsNoetherianRing R] in
/-- For a finite free `P` and socle `s` (`𝔪 = ann s`), `s • v = 0 ⟹ v ∈ 𝔪P` (coordinatewise). -/
private theorem mem_maximalIdeal_smul_top_of_smul_eq_zero
    {P : Type u} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    (s : R) (hmem : ∀ m : R, m ∈ maximalIdeal R ↔ m * s = 0)
    (v : P) (hv : s • v = 0) : v ∈ maximalIdeal R • (⊤ : Submodule R P) := by
  classical
  set b := Module.Free.chooseBasis R P with hb
  have hmemi : ∀ i, b.repr v i ∈ maximalIdeal R := by
    intro i
    rw [hmem]
    have h : b.repr (s • v) i = 0 := by rw [hv]; simp
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    rw [mul_comm]; exact h
  have hsum : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hmemi i) Submodule.mem_top

omit [IsNoetherianRing R] in
/-- **[Socle reduced-injectivity — 00MY heart].**  Over a depth-`0` local Noetherian ring, an
injective `R`-linear map `ψ` of finite free modules stays injective after reduction to the residue
field: `k ⊗ ψ` is injective (`k = ResidueField R`).  Proof: if `ψ v ∈ 𝔪Q` then `s·ψ v = 0 = ψ(s·v)`,
so `s·v = 0` (`ψ` injective), so `v ∈ 𝔪P`. -/
private theorem lTensor_residueField_injective_of_injective
    {P Q : Type u} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    [AddCommGroup Q] [Module R Q] [Module.Free R Q] [Module.Finite R Q]
    (s : R) (hmem : ∀ m : R, m ∈ maximalIdeal R ↔ m * s = 0)
    (ψ : P →ₗ[R] Q) (hψ : Function.Injective ψ) :
    Function.Injective (ψ.lTensor (ResidueField R)) := by
  suffices h : Function.Injective (ψ.lTensor (R ⧸ maximalIdeal R)) by exact h
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R) ξ)
  have hξv : ξ = (1 : R ⧸ maximalIdeal R) ⊗ₜ[R] v := by
    apply (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R)).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, ← hv]
  subst hξv
  rw [LinearMap.lTensor_tmul] at hξ
  have hψv : ψ v ∈ maximalIdeal R • (⊤ : Submodule R Q) := by
    have h := congrArg (TensorProduct.quotTensorEquivQuotSMul Q (maximalIdeal R)) hξ
    rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
      Submodule.Quotient.mk_eq_zero] at h
    exact h
  have hsψv : s • ψ v = 0 := by
    refine Submodule.smul_induction_on hψv (fun c hc x _ => ?_) (fun x y hx hy => ?_)
    · rw [smul_smul, mul_comm, (hmem c).mp hc, zero_smul]
    · rw [smul_add, hx, hy, add_zero]
  have hsv : s • v = 0 := hψ (by rw [map_smul, hsψv, map_zero])
  have hvmem : v ∈ maximalIdeal R • (⊤ : Submodule R P) :=
    mem_maximalIdeal_smul_top_of_smul_eq_zero s hmem v hsv
  rw [← LinearEquiv.map_eq_zero_iff (TensorProduct.quotTensorEquivQuotSMul P (maximalIdeal R)),
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  exact hvmem

omit [IsNoetherianRing R] in
/-- **[Syzygy freeness + ranks — 00MY splitting / 00MW ranks].**  Over a depth-`0` local Noetherian
ring, for the exact free complex each image `im(φ m)` is free of rank `rnk (m+1)`.  Descending
induction on `m`: at the top the image is `0`; the step feeds the syzygy SES
`0 → im(φ (m+1)) → F_{m+1} → im(φ m) → 0` to `Module.free_of_lTensor_residueField_injective`
(reduced-injective inclusion by the socle lemma) for freeness, and to `splitSurjectiveEquiv`
(projective ⟹ split) for the rank additivity, closed against `hrnk` by `omega`. -/
private theorem syzygy_free_finrank {rk rnk : ℕ → ℕ} (e : ℕ)
    (hrk : ∀ i, e ≤ i → rk i = 0) (hrnk_top : ∀ i, e ≤ i → rnk i = 0)
    (hrnk : ∀ i, 1 ≤ i → i < e → rnk i + rnk (i + 1) = rk i)
    (φ : (i : ℕ) → (Fin (rk (i + 1)) → R) →ₗ[R] (Fin (rk i) → R))
    (hexact : ∀ i, Function.Exact (φ (i + 1)) (φ i))
    (s : R) (hmem : ∀ m : R, m ∈ maximalIdeal R ↔ m * s = 0) :
    ∀ m, Module.Free R (LinearMap.range (φ m)) ∧
      Module.finrank R (LinearMap.range (φ m)) = rnk (m + 1) := by
  have main : ∀ k m, e ≤ m + 1 + k →
      Module.Free R (LinearMap.range (φ m)) ∧
        Module.finrank R (LinearMap.range (φ m)) = rnk (m + 1) := by
    intro k
    induction k with
    | zero =>
      intro m hm
      have hrk0 : rk (m + 1) = 0 := hrk (m + 1) (by omega)
      haveI : Subsingleton (Fin (rk (m + 1)) → R) := by
        haveI : IsEmpty (Fin (rk (m + 1))) := by rw [hrk0]; infer_instance
        exact ⟨fun a b => funext fun x => isEmptyElim x⟩
      have hbot : LinearMap.range (φ m) = ⊥ := by
        rw [LinearMap.range_eq_bot]
        apply LinearMap.ext; intro v; rw [show v = 0 from Subsingleton.elim _ _]; simp
      rw [hbot]
      refine ⟨Module.Free.of_subsingleton R _, ?_⟩
      rw [finrank_bot, hrnk_top (m + 1) (by omega)]
    | succ k ih =>
      intro m hm
      by_cases hbase : e ≤ m + 1
      · have hrk0 : rk (m + 1) = 0 := hrk (m + 1) hbase
        haveI : Subsingleton (Fin (rk (m + 1)) → R) := by
          haveI : IsEmpty (Fin (rk (m + 1))) := by rw [hrk0]; infer_instance
          exact ⟨fun a b => funext fun x => isEmptyElim x⟩
        have hbot : LinearMap.range (φ m) = ⊥ := by
          rw [LinearMap.range_eq_bot]
          apply LinearMap.ext; intro v; rw [show v = 0 from Subsingleton.elim _ _]; simp
        rw [hbot]
        exact ⟨Module.Free.of_subsingleton R _, by rw [finrank_bot, hrnk_top (m + 1) hbase]⟩
      · have hlt : m + 1 < e := by omega
        obtain ⟨hfree_next, hrank_next⟩ := ih (m + 1) (by omega)
        have hker : LinearMap.ker (φ m) = LinearMap.range (φ (m + 1)) :=
          LinearMap.exact_iff.mp (hexact m)
        set g := (φ m).rangeRestrict with hg
        have hgsurj : Function.Surjective g := LinearMap.surjective_rangeRestrict _
        set f := (LinearMap.range (φ (m + 1))).subtype with hf
        have hExact : Function.Exact f g := by
          rw [LinearMap.exact_iff, hg, LinearMap.ker_rangeRestrict, hker, hf,
            Submodule.range_subtype]
        haveI : Module.Free R (LinearMap.range (φ (m + 1))) := hfree_next
        have hfinj : Function.Injective (f.lTensor (ResidueField R)) :=
          lTensor_residueField_injective_of_injective s hmem f (Submodule.subtype_injective _)
        haveI hfreeKm : Module.Free R (LinearMap.range (φ m)) :=
          Module.free_of_lTensor_residueField_injective f g hgsurj hExact hfinj
        refine ⟨hfreeKm, ?_⟩
        obtain ⟨l, hl⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hgsurj)
        let E := (hExact.splitSurjectiveEquiv (Submodule.subtype_injective _) ⟨l, hl⟩).1
        have hFrank : Module.finrank R (Fin (rk (m + 1)) → R) =
            Module.finrank R (LinearMap.range (φ (m + 1))) +
              Module.finrank R (LinearMap.range (φ m)) := by
          rw [E.finrank_eq, Module.finrank_prod]
        simp only [Module.finrank_pi, Fintype.card_fin, hrank_next] at hFrank
        have hrnk_eq := hrnk (m + 1) (by omega) hlt
        omega
  intro m
  exact main e m (by omega)

omit [IsNoetherianRing R] in
/-- **[McCoy rank bridge — E1].**  The rank of the residue-field reduction of the standard-bases
matrix of `φ` equals the residue-field dimension of the range of the base-changed map
`k ⊗ φ`.  (`toMatrix_baseChange` + `Matrix.rank_eq_finrank_range_toLin`.) -/
private theorem rank_map_residue_eq_finrank_range_baseChange {a b : ℕ}
    (φ : (Fin a → R) →ₗ[R] (Fin b → R)) :
    ((LinearMap.toMatrix (Pi.basisFun R (Fin a)) (Pi.basisFun R (Fin b)) φ).map
        (residue R)).rank
      = Module.finrank (ResidueField R)
          (LinearMap.range (φ.baseChange (ResidueField R))) := by
  rw [← IsLocalRing.ResidueField.algebraMap_eq,
    ← LinearMap.toMatrix_baseChange (ResidueField R) φ (Pi.basisFun R (Fin a))
      (Pi.basisFun R (Fin b)),
    Matrix.rank_eq_finrank_range_toLin _
      (Algebra.TensorProduct.basis (ResidueField R) (Pi.basisFun R (Fin b)))
      (Algebra.TensorProduct.basis (ResidueField R) (Pi.basisFun R (Fin a))),
    Matrix.toLin_toMatrix]

end IdealOfMinorsTopSupport

/-! ## [T-ACYC.00MY+00MW] Depth-0 splitting ⟹ minor ideal `= ⊤` — Stacks 00MY+00MW (10.102.3/6)

> 00MY: "Assume `𝔪 ∈ Ass(R)`, in other words `R` has depth `0`. Suppose that `0 → R^{nₑ} → … → R^{n₀}`
> is exact at `R^{nₑ}, …, R^{n₁}`. Then the complex is isomorphic to a direct sum of trivial
> complexes."
> 00MW: for a direct sum of trivial complexes, "the maps `φᵢ` have rank `rᵢ`", "`rank(φᵢ₊₁) +
> rank(φᵢ) = nᵢ`", and "each `I(φᵢ) = R`."

Composed: over a depth-`0` Noetherian local ring, an exact free complex has every minor ideal
`I(φᵢ) = R`.  This is the fact `be_forward_core` establishes at each associated prime `𝔮 ∈ Ass(R)`
(after localising), giving `I(φᵢ) ⊄ 𝔮`, the input to the prime-avoidance nonzerodivisor. -/

open TensorProduct IsLocalRing in
/-- **[T-ACYC.00MY+00MW] Stacks 10.102.3 + 10.102.6.**  Over a Noetherian local ring of depth `0`
(`𝔪 ∈ Ass(R)`), an exact finite free complex is a direct sum of trivial complexes, so its interior
minor ideal is the unit ideal: `I(φᵢ) = ⊤` (Lean `φ (i-1)` = Stacks `φᵢ`, size `rnk i`).

Proof (00MY + 00MW): pick a socle element `s` (`𝔪 = ann s`, from `𝔪 ∈ Ass R`); the socle forces every
injective map of finite frees to stay injective mod `𝔪`, so a descending induction splits off free
syzygies (`syzygy_free_finrank`): `im(φ (i-1))` is free of rank `rnk i`.  Since `φ (i-1)` factors as
a surjection onto that free image followed by a (reduced-injective) inclusion, the residue-field
rank of `k ⊗ φ (i-1)` is exactly `rnk i`; McCoy (`idealOfMinors_le_ker_iff_rank_lt`) then rules out
`I ≤ 𝔪`, so `I = ⊤`. -/
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
  obtain ⟨s, -, hmem⟩ := socle_exists hdepth0
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨hfree, hrank_eq⟩ := syzygy_free_finrank e hrk hrnk_top hrnk φ hexact s hmem j
  haveI := hfree
  -- E2: the residue-field rank of `k ⊗ φ j` is `rnk (j+1)` (free image of that rank).
  have hinj : Function.Injective
      ((LinearMap.range (φ j)).subtype.baseChange (ResidueField R)) :=
    lTensor_residueField_injective_of_injective s hmem _ (Submodule.subtype_injective _)
  have hsurj : Function.Surjective ((φ j).rangeRestrict.baseChange (ResidueField R)) :=
    LinearMap.lTensor_surjective (ResidueField R) (LinearMap.surjective_rangeRestrict _)
  have hbc : (φ j).baseChange (ResidueField R)
      = ((LinearMap.range (φ j)).subtype.baseChange (ResidueField R)) ∘ₗ
        ((φ j).rangeRestrict.baseChange (ResidueField R)) := by
    rw [← LinearMap.baseChange_comp]; congr 1
  have hrange : LinearMap.range ((φ j).baseChange (ResidueField R))
      = LinearMap.range ((LinearMap.range (φ j)).subtype.baseChange (ResidueField R)) := by
    rw [hbc, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hE2 : Module.finrank (ResidueField R)
      (LinearMap.range ((φ j).baseChange (ResidueField R))) = rnk (j + 1) := by
    rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange, hrank_eq]
  -- McCoy: if `I ≤ 𝔪` then the reduced rank is `< rnk (j+1)`, contradicting E1 = E2 = rnk (j+1).
  by_contra hne
  have hle : LinearMap.idealOfMinors (rnk (j + 1)) (φ j) ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hne
  rw [LinearMap.idealOfMinors_eq, ← IsLocalRing.ker_residue,
    Matrix.idealOfMinors_le_ker_iff_rank_lt,
    rank_map_residue_eq_finrank_range_baseChange, hE2] at hle
  exact lt_irrefl _ hle

end
