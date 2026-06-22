module

public import BernoulliRegular.GaussSumProduct.GaussProduct

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Complex

section RootNumberConjugatePairing

variable (p : ℕ) [hp : Fact p.Prime]

/-- The inverse of an odd Dirichlet character is odd. -/
lemma DirichletCharacter.Odd.inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (h_odd : χ.Odd) : χ⁻¹.Odd := by
  change χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', show χ (-1) = -1 from h_odd]
  norm_num

/-- The inverse of an even Dirichlet character is even. -/
lemma DirichletCharacter.Even.inv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (h_even : χ.Even) : χ⁻¹.Even := by
  change χ⁻¹ (-1) = 1
  rw [MulChar.inv_apply_eq_inv', show χ (-1) = 1 from h_even]
  norm_num

/-- **WP-A**: For a non-trivial odd Dirichlet character `χ` modulo a prime `p`,
the product of conjugate root numbers equals 1:
`W_χ · W_{χ⁻¹} = 1`.

Derivation (for odd `χ`, archimedean factor `ε = I`):
  `W_χ · W_{χ⁻¹} = τ(χ)·τ(χ⁻¹) / (I² · p) = χ(-1) · p / (-p) = -χ(-1) = 1`. -/
theorem rootNumber_mul_rootNumber_inv_of_odd
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (h_odd : χ.Odd) :
    DirichletCharacter.rootNumber χ *
      DirichletCharacter.rootNumber χ⁻¹ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_inv_odd : χ⁻¹.Odd := DirichletCharacter.Odd.inv h_odd
  have h_not_even : ¬ χ.Even := h_odd.not_even
  have h_inv_not_even : ¬ χ⁻¹.Even := h_inv_odd.not_even
  have hχ_neg_one : χ (-1) = -1 := h_odd
  unfold DirichletCharacter.rootNumber
  rw [if_neg h_not_even, if_neg h_inv_not_even, pow_one]
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.cpow_mul_nat]; norm_num
  have h_prod := gaussSum_mul_gaussSum_inv_stdAddChar p hχ
  rw [hχ_neg_one] at h_prod
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_I_sq : Complex.I ^ 2 = -1 := Complex.I_sq
  have h_rearrange : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / Complex.I /
        ((p : ℂ) ^ (1 / 2 : ℂ)) *
      (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / Complex.I /
        ((p : ℂ) ^ (1 / 2 : ℂ))) =
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
      (Complex.I ^ 2 * ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2) := by
    field_simp
  rw [h_rearrange, h_prod, h_I_sq, h_half_sq]
  field_simp

/-- **WP-B**: For a non-trivial even Dirichlet character `χ` modulo a prime `p`,
the product of conjugate root numbers equals 1:
`W_χ · W_{χ⁻¹} = 1`.

Derivation (for even `χ`, archimedean factor `ε = 1`):
  `W_χ · W_{χ⁻¹} = τ(χ)·τ(χ⁻¹) / p = χ(-1) · p / p = χ(-1) = 1`. -/
theorem rootNumber_mul_rootNumber_inv_of_even
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) (h_even : χ.Even) :
    DirichletCharacter.rootNumber χ *
      DirichletCharacter.rootNumber χ⁻¹ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_inv_even : χ⁻¹.Even := DirichletCharacter.Even.inv h_even
  have hχ_neg_one : χ (-1) = 1 := h_even
  unfold DirichletCharacter.rootNumber
  rw [if_pos h_even, if_pos h_inv_even, pow_zero]
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.cpow_mul_nat]; norm_num
  have h_prod := gaussSum_mul_gaussSum_inv_stdAddChar p hχ
  rw [hχ_neg_one] at h_prod
  have h_rearrange : gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / 1 /
        ((p : ℂ) ^ (1 / 2 : ℂ)) *
      (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / 1 /
        ((p : ℂ) ^ (1 / 2 : ℂ))) =
      gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
        gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
      ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 := by
    field_simp
  rw [h_rearrange, h_prod, h_half_sq]
  field_simp

/-- **Conjugate pairing**: `W_χ · W_{χ⁻¹} = 1` for any non-trivial Dirichlet
character `χ` modulo a prime `p`. Combines WP-A (odd) and WP-B (even). -/
theorem rootNumber_mul_rootNumber_inv
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    DirichletCharacter.rootNumber χ *
      DirichletCharacter.rootNumber χ⁻¹ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rcases χ.even_or_odd with h_even | h_odd
  · exact rootNumber_mul_rootNumber_inv_of_even p hχ h_even
  · exact rootNumber_mul_rootNumber_inv_of_odd p hχ h_odd

/-- `DirichletCharacter ℂ p` is a cyclic group for `p` prime. -/
lemma dirichletCharacter_ℂ_isCyclic_prime :
    IsCyclic (DirichletCharacter ℂ p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_expo_ne : Monoid.exponent (ZMod p)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨h_expo_ne⟩
  haveI : NeZero ((Monoid.exponent (ZMod p)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr h_expo_ne⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.out
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ p
  exact (MulEquiv.isCyclic e).mpr inferInstance

/-- **Uniqueness of non-trivial quadratic character**: for `p` an odd prime, the
Legendre character `η = legendreDirichlet p` is the unique non-trivial
Dirichlet character `χ` mod `p` with `χ² = 1`. -/
lemma legendreDirichlet_eq_of_sq_eq_one (hp_odd : p ≠ 2)
    {χ : DirichletCharacter ℂ p} (h_sq : χ ^ 2 = 1) (h_ne_one : χ ≠ 1) :
    χ = legendreDirichlet p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  haveI := dirichletCharacter_ℂ_isCyclic_prime p
  have h_card_le : (Finset.univ.filter
      (fun a : DirichletCharacter ℂ p ↦ a ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by omega)
  have h_η_sq : (legendreDirichlet p) ^ 2 = 1 :=
    MulChar.isQuadratic_iff_sq_eq_one.mp (legendreDirichlet_isQuadratic p)
  have h_η_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  by_contra h_χ_ne_η
  -- 1, η, χ are three distinct elements of {a | a^2 = 1}, contradicting ≤ 2.
  have h_sub : ({1, legendreDirichlet p, χ} : Finset (DirichletCharacter ℂ p)) ⊆
      Finset.univ.filter (fun a : DirichletCharacter ℂ p ↦ a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow _
    · exact h_η_sq
    · exact h_sq
  have h3 : ({1, legendreDirichlet p, χ} : Finset (DirichletCharacter ℂ p)).card = 3 := by
    rw [show ({1, legendreDirichlet p, χ} : Finset _) =
        insert 1 (insert (legendreDirichlet p) {χ}) from rfl,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · exact fun h ↦ h_χ_ne_η (Finset.mem_singleton.mp h).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h_η_ne_one.symm, fun h ↦ h_ne_one h.symm⟩
  have : 3 ≤ 2 :=
    h3 ▸ Finset.card_le_card h_sub |>.trans h_card_le
  omega

/-- **WP-F**: For `p` an odd prime, the product of root numbers over non-trivial
Dirichlet characters mod `p` equals the root number of the Legendre character:
`∏_{χ ≠ 1} W_χ = W_η`.

Proof: Split `nontrivialCharacters = {η} ∪ S_free` where `S_free = non-trivial \ {η}`.
On `S_free`, the inversion `χ ↦ χ⁻¹` is a fixed-point-free involution (by
uniqueness of non-trivial quadratic characters) and `W_χ · W_{χ⁻¹} = 1`
(WP-A, WP-B). Apply `Finset.prod_involution`. -/
theorem prod_rootNumber_ne_one_eq_rootNumber_legendre (hp_odd : p ≠ 2) :
    ∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.rootNumber χ =
      DirichletCharacter.rootNumber (legendreDirichlet p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  have h_η_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  have h_η_mem : legendreDirichlet p ∈ nontrivialCharacters p := by
    unfold nontrivialCharacters
    simpa using h_η_ne_one
  have h_η_quad : (legendreDirichlet p).IsQuadratic := legendreDirichlet_isQuadratic p
  have h_η_sq : (legendreDirichlet p) ^ 2 = 1 :=
    MulChar.isQuadratic_iff_sq_eq_one.mp h_η_quad
  have h_η_inv : (legendreDirichlet p)⁻¹ = legendreDirichlet p := by
    have h_mul : (legendreDirichlet p) * (legendreDirichlet p) = 1 := by
      rw [← sq]; exact h_η_sq
    exact DivisionMonoid.inv_eq_of_mul _ _ h_mul
  -- S_free = nontrivial \ {η}.
  set S_free : Finset (DirichletCharacter ℂ p) :=
    (nontrivialCharacters p).erase (legendreDirichlet p) with hS_free
  have h_ins : nontrivialCharacters p = insert (legendreDirichlet p) S_free := by
    rw [hS_free, Finset.insert_erase h_η_mem]
  rw [h_ins, Finset.prod_insert (Finset.notMem_erase _ _)]
  suffices h_prod_free : ∏ χ ∈ S_free, DirichletCharacter.rootNumber χ = 1 by
    rw [h_prod_free, mul_one]
  -- Apply Finset.prod_involution to S_free with σ = inversion.
  refine Finset.prod_involution
    (fun (χ : DirichletCharacter ℂ p) _ ↦ χ⁻¹) ?_ ?_ ?_ ?_
  · -- hg₁: W_χ * W_{χ⁻¹} = 1 for χ ∈ S_free.
    intro a ha
    have h_a_ne_one : a ≠ 1 := by
      have : a ∈ nontrivialCharacters p := (Finset.mem_erase.mp ha).2
      unfold nontrivialCharacters at this
      simpa using this
    exact rootNumber_mul_rootNumber_inv p h_a_ne_one
  · -- hg₃: W_χ ≠ 1 → χ⁻¹ ≠ χ for χ ∈ S_free.
    intro a ha _ h_inv_eq
    have h_a_ne_η : a ≠ legendreDirichlet p := (Finset.mem_erase.mp ha).1
    have h_a_ne_one : a ≠ 1 := by
      have : a ∈ nontrivialCharacters p := (Finset.mem_erase.mp ha).2
      unfold nontrivialCharacters at this
      simpa using this
    have h_inv : a⁻¹ = a := h_inv_eq
    have h_a_sq : a ^ 2 = 1 := by
      rw [pow_two, show a * a = a * a⁻¹ from by rw [h_inv]]
      exact mul_inv_cancel a
    exact h_a_ne_η (legendreDirichlet_eq_of_sq_eq_one p hp_odd h_a_sq h_a_ne_one)
  · -- g_mem: χ⁻¹ ∈ S_free for χ ∈ S_free.
    intro a ha
    have h_a_ne_η : a ≠ legendreDirichlet p := (Finset.mem_erase.mp ha).1
    have h_a_nontriv : a ∈ nontrivialCharacters p := (Finset.mem_erase.mp ha).2
    have h_a_ne_one : a ≠ 1 := by
      unfold nontrivialCharacters at h_a_nontriv
      simpa using h_a_nontriv
    change a⁻¹ ∈ S_free
    simp only [hS_free, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h
      apply h_a_ne_η
      rw [← inv_inv a, h, h_η_inv]
    · unfold nontrivialCharacters
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro h
      apply h_a_ne_one
      rw [← inv_inv a, h, inv_one]
  · -- hg₄: (χ⁻¹)⁻¹ = χ.
    intros; exact inv_inv _

/-- **WP-H (conditional on WP-E)**: If `∏_{χ non-trivial mod p} W_χ = 1`, then
`W_η = 1` for the Legendre character `η = legendreDirichlet p` (`p` odd prime).

The hypothesis `h_prod` is equivalent to the statement `∏_{primitive ψ, cond ψ | p} W_ψ = 1`
(since `rootNumber_modOne = 1` absorbs the conductor-1 primitive trivial character),
which is what comes out of matching the functional equation of the product L-function
with that of the Dedekind zeta function for `ℚ(ζ_p)`. -/
theorem rootNumber_legendreDirichlet_eq_one (hp_odd : p ≠ 2)
    (h_prod : ∏ χ ∈ nontrivialCharacters p,
      DirichletCharacter.rootNumber χ = 1) :
    DirichletCharacter.rootNumber (legendreDirichlet p) = 1 := by
  rw [← prod_rootNumber_ne_one_eq_rootNumber_legendre p hp_odd]
  exact h_prod

omit hp in
/-- The product `∏_{χ ∈ nontrivialCharacters p} f χ⁻¹` equals `∏ f χ` since
inversion is an involution on non-trivial characters. -/
lemma prod_inv_reindex_nontrivialCharacters
    {G : Type*} [CommMonoid G] (f : DirichletCharacter ℂ p → G) :
    (∏ χ ∈ nontrivialCharacters p, f χ⁻¹) =
      ∏ χ ∈ nontrivialCharacters p, f χ := by
  classical
  refine Finset.prod_bij (fun χ _ ↦ χ⁻¹) ?_ ?_ ?_ ?_
  · intro χ hχ
    unfold nontrivialCharacters at hχ ⊢
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hχ ⊢
    intro h
    apply hχ
    rw [← inv_inv χ, h, inv_one]
  · intro χ₁ _ χ₂ _ h
    rw [show χ₁ = (χ₁⁻¹)⁻¹ from (inv_inv _).symm, h, inv_inv]
  · intro χ hχ
    refine ⟨χ⁻¹, ?_, inv_inv _⟩
    unfold nontrivialCharacters at hχ ⊢
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hχ ⊢
    intro h
    apply hχ
    rw [← inv_inv χ, h, inv_one]
  · intro χ _; rfl

/-- **WP-C**: functional equation of the product `∏ Λ(χ, s)` over non-trivial
Dirichlet characters mod a prime `p`.

From the individual FEs `Λ(χ, 1-s) = p^{s-1/2} · W_χ · Λ(χ⁻¹, s)` for `χ`
primitive, and reindexing `χ ↔ χ⁻¹`:

`∏_{χ≠1} Λ(χ, 1-s) = p^{(p-2)·(s-1/2)} · (∏_{χ≠1} W_χ) · ∏_{χ≠1} Λ(χ, s)`. -/
theorem prod_completedLFunction_nontrivial_one_sub (s : ℂ) :
    (∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((nontrivialCharacters p).card : ℂ) * (s - 1/2 : ℂ)) *
        (∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ) *
        ∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ s := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  have h_prim : ∀ χ ∈ nontrivialCharacters p, χ.IsPrimitive := fun χ hχ ↦ by
    unfold nontrivialCharacters at hχ
    have h_ne : χ ≠ 1 := by simpa using hχ
    exact DirichletCharacter.isPrimitive_of_ne_one p h_ne
  have h_each : ∀ χ ∈ nontrivialCharacters p,
      DirichletCharacter.completedLFunction χ (1 - s) =
      ((p : ℂ) ^ (s - 1/2) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction χ⁻¹ s := fun χ hχ ↦ by
    have := (h_prim χ hχ).completedLFunction_one_sub s
    linear_combination this
  rw [Finset.prod_congr rfl h_each, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_const,
    prod_inv_reindex_nontrivialCharacters p
      (fun χ : DirichletCharacter ℂ p ↦ DirichletCharacter.completedLFunction χ s)]
  -- Now: (p^(s-1/2))^card · ∏ W_χ · ∏ completedL(χ, s)
  -- Goal: p^(card · (s-1/2)) · ∏ W_χ · ∏ completedL(χ, s)
  rw [mul_comm ((nontrivialCharacters p).card : ℂ) (s - 1/2),
    Complex.cpow_mul_nat]

/-- For `p` prime, `|nontrivialCharacters p| = p - 2`. -/
lemma card_nontrivialCharacters : (nontrivialCharacters p).card = p - 2 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_expo_ne : Monoid.exponent (ZMod p)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨h_expo_ne⟩
  haveI : NeZero ((Monoid.exponent (ZMod p)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr h_expo_ne⟩
  classical
  unfold nontrivialCharacters
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have h_card : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    have h_nat := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
    rw [Nat.card_eq_fintype_card] at h_nat
    rw [h_nat, Nat.totient_prime hp.out]
  rw [h_card]
  omega

/-- The Dirichlet completed L-function is nonzero for `Re s > 1` (any character). -/
lemma completedLFunction_ne_zero_of_one_lt_re
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.completedLFunction χ s ≠ 0 := by
  have hs_ne_zero : s ≠ 0 := fun h ↦ by
    simp only [h, Complex.zero_re] at hs; linarith
  have hs_ne_one : s ≠ 1 := fun h ↦ by
    simp only [h, Complex.one_re] at hs; linarith
  have h_eq : DirichletCharacter.LFunction χ s =
      DirichletCharacter.completedLFunction χ s / DirichletCharacter.gammaFactor χ s :=
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs_ne_zero)
  have h_L_ne : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs_ne_one) hs.le
  intro h_comp_zero
  apply h_L_ne
  rw [h_eq, h_comp_zero, zero_div]

/-- The completed Riemann zeta is nonzero for `Re s > 1`. -/
lemma completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs_ne_zero : s ≠ 0 := fun h ↦ by
    simp only [h, Complex.zero_re] at hs; linarith
  have hs_ne_one : s ≠ 1 := fun h ↦ by
    simp only [h, Complex.one_re] at hs; linarith
  have h_zeta_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  -- completedRiemannZeta s = Gammaℝ s · riemannZeta s (away from s = 0, 1).
  have h_Γ_ne : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have h_eq : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs_ne_zero
  intro h_c_zero
  apply h_zeta_ne
  rw [h_eq, h_c_zero, zero_div]

/-- **WP-E (conditional)**: Given the Dedekind functional equation
`Λ_K(1-s) = p^{(p-2)(s-1/2)} · Λ_K(s)` for `K = ℚ(ζ_p)` at some `s` where the
factors are nonzero, we deduce `∏_{χ ≠ 1} W_χ = 1`.

The hypothesis `h_FE` encodes the (abstract) Dedekind functional equation
written in terms of `completedRiemannZeta · ∏ completedLFunction`. Proving
this hypothesis is the big remaining piece (WP-D). -/
theorem prod_rootNumber_eq_one_of_dedekindFE
    (s : ℂ)
    (hZ : completedRiemannZeta s ≠ 0)
    (hL : ∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ s ≠ 0)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h_WPC := prod_completedLFunction_nontrivial_one_sub p s
  rw [h_WPC, completedRiemannZeta_one_sub, card_nontrivialCharacters p] at h_FE
  -- h_FE : completedRiemannZeta s *
  --     (p^((p-2)·(s-1/2)) · (∏ W_χ) · ∏ completedLFunction χ s) =
  --   p^((p-2)·(s-1/2)) · (completedRiemannZeta s · ∏ completedLFunction χ s)
  have hp_cpow_ne : ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ))) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.out.ne_zero))
  have hZL_ne : completedRiemannZeta s *
      (∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ s) ≠ 0 := mul_ne_zero hZ hL
  have h_all_ne : (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
      (completedRiemannZeta s *
        ∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ s) ≠ 0 :=
    mul_ne_zero hp_cpow_ne hZL_ne
  -- Rearrange h_FE using commutativity:
  -- Z(s) · (p^... · (∏ W) · ∏ L) = p^... · Z(s) · ∏ L
  -- ↔ (∏ W) · (p^... · Z(s) · ∏ L) = p^... · Z(s) · ∏ L
  have h_eq : (∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ) *
      ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) =
      1 * ((p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) := by
    rw [one_mul]
    linear_combination h_FE
  exact mul_right_cancel₀ h_all_ne h_eq

/-- **WP-E (conditional), streamlined form**: Given the Dedekind functional
equation for `ℚ(ζ_p)` at some `s` with `Re s > 1`, we deduce `∏_{χ ≠ 1} W_χ = 1`.

This is `prod_rootNumber_eq_one_of_dedekindFE` with the nonvanishing hypotheses
automatically discharged using `completedLFunction_ne_zero_of_one_lt_re` and
`completedRiemannZeta_ne_zero_of_one_lt_re`. -/
theorem prod_rootNumber_eq_one_of_dedekindFE_of_one_lt_re (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    ∏ χ ∈ nontrivialCharacters p, DirichletCharacter.rootNumber χ = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  apply prod_rootNumber_eq_one_of_dedekindFE p s
    (completedRiemannZeta_ne_zero_of_one_lt_re hs)
    (Finset.prod_ne_zero_iff.mpr fun χ _ ↦ completedLFunction_ne_zero_of_one_lt_re χ hs)
    h_FE

/-- **WP-I (conditional)**: For `p ≡ 3 (mod 4)` prime, given the root-number
product condition, the Gauss sum of the Legendre character equals `I · √p`:
`gaussSum (legendreDirichlet p) stdAddChar = I · √p`.

Combining with `rootNumber_legendreDirichlet_eq_one`. -/
theorem gaussSum_legendreDirichlet_eq_I_mul_sqrt
    (hp_three_mod_four : p % 4 = 3)
    (h_prod : ∏ χ ∈ nontrivialCharacters p,
      DirichletCharacter.rootNumber χ = 1) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_not_even : ¬ (legendreDirichlet p).Even := h_odd.not_even
  have h_root_one : DirichletCharacter.rootNumber (legendreDirichlet p) = 1 :=
    rootNumber_legendreDirichlet_eq_one p hp_odd h_prod
  have h_def : DirichletCharacter.rootNumber (legendreDirichlet p) =
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
        Complex.I / ((p : ℂ) ^ (1 / 2 : ℂ)) := by
    unfold DirichletCharacter.rootNumber
    rw [if_neg h_not_even, pow_one]
  rw [h_root_one] at h_def
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_I_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp at h_def
  linear_combination -h_def

/-- **Capstone (conditional on Dedekind FE for `ℚ(ζ_p)`)**: For `p ≡ 3 mod 4`,
given the Dedekind functional equation at some `s` with nonvanishing factors,
the Gauss sum of the Legendre character equals `I · √p`.

This is the full Washington Corollary 4.6 proof of the Gauss sum sign theorem,
packaged conditional on WP-D (the Dedekind FE, which is the remaining missing
piece). -/
theorem gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_dedekindFE
    (hp_three_mod_four : p % 4 = 3) (s : ℂ)
    (hZ : completedRiemannZeta s ≠ 0)
    (hL : ∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ s ≠ 0)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) :=
  gaussSum_legendreDirichlet_eq_I_mul_sqrt p hp_three_mod_four
    (prod_rootNumber_eq_one_of_dedekindFE p s hZ hL h_FE)

open scoped Classical in
/-- **Signed product of Gauss sums over odd characters excluding `η`**: for
`p ≡ 3 mod 4` prime,

`∏_{χ odd, χ ≠ η} gaussSum χ = (I · √p)^{|oddCharacters \ {η}|}`.

Obtained by applying `Finset.prod_involution` to the normalised function
`f(χ) := gaussSum(χ) / (I·√p)`, which satisfies `f(χ)·f(χ⁻¹) = 1` on the
odd/non-legendre characters. -/
theorem gaussSum_oddCharacters_erase_legendre_prod
    (hp_three_mod_four : p % 4 = 3) :
    ∏ χ ∈ (oddCharacters p).erase (legendreDirichlet p),
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) ^
        ((oddCharacters p).erase (legendreDirichlet p)).card := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  classical
  -- Setup
  set η := legendreDirichlet p
  have h_η_odd : η.Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_η_mem : η ∈ oddCharacters p := by
    simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_η_odd
  have h_η_quad : η.IsQuadratic := legendreDirichlet_isQuadratic p
  have h_η_sq : η ^ 2 = 1 := MulChar.isQuadratic_iff_sq_eq_one.mp h_η_quad
  have h_η_inv : η⁻¹ = η := by
    have : η * η = 1 := by rw [← sq]; exact h_η_sq
    exact DivisionMonoid.inv_eq_of_mul _ _ this
  have h_η_ne_one : η ≠ 1 := legendreDirichlet_ne_one p hp_odd
  set S := (oddCharacters p).erase η with hS
  -- Normalisation constant c with c² = -p.
  set c : ℂ := Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) with hc
  have hp_cpow_ne : ((p : ℂ) ^ (1 / 2 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  have hc_ne : c ≠ 0 := mul_ne_zero Complex.I_ne_zero hp_cpow_ne
  have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.cpow_mul_nat]; norm_num
  have hc_sq : c ^ 2 = -(p : ℂ) := by
    calc c ^ 2 = Complex.I ^ 2 * ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 := by rw [hc]; ring
      _ = -1 * (p : ℂ) := by rw [Complex.I_sq, h_half_sq]
      _ = -(p : ℂ) := by ring
  -- Show: for χ ∈ S, gaussSum χ · gaussSum χ⁻¹ = -p (odd characters, χ ≠ 1).
  have h_pair : ∀ χ ∈ S, gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
      gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) = -(p : ℂ) := by
    intro χ hχ
    have hχ_odd_set : χ ∈ oddCharacters p := (Finset.mem_erase.mp hχ).2
    have hχ_odd : χ.Odd := by
      simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and] at hχ_odd_set
      exact hχ_odd_set
    have hχ_ne_one : χ ≠ 1 := fun h ↦ by
      rw [h] at hχ_odd
      have h1 : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_one.neg
      exact absurd hχ_odd h1.not_odd
    have hχ_neg : χ (-1) = -1 := hχ_odd
    rw [gaussSum_mul_gaussSum_inv_stdAddChar p hχ_ne_one, hχ_neg]
    ring
  -- Apply prod_involution with f(χ) := gaussSum(χ) / c.
  have h_prod_f : ∏ χ ∈ S,
      (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / c) = 1 := by
    refine Finset.prod_involution (fun (χ : DirichletCharacter ℂ p) _ ↦ χ⁻¹) ?_ ?_ ?_ ?_
    · intro χ hχ
      have h_pair_χ := h_pair χ hχ
      calc (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / c) *
          (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) / c)
          = (gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) *
              gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod p) ℂ)) / c ^ 2 := by ring
        _ = -(p : ℂ) / -(p : ℂ) := by rw [h_pair_χ, hc_sq]
        _ = 1 := div_self (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero))
    · -- f(χ) ≠ 1 → χ⁻¹ ≠ χ: on S (excluding η), χ⁻¹ ≠ χ by uniqueness.
      intro χ hχ _ h_inv_eq
      have hχ_odd_set : χ ∈ oddCharacters p := (Finset.mem_erase.mp hχ).2
      have hχ_ne_one : χ ≠ 1 := fun h ↦ by
        simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and, h] at hχ_odd_set
        have : (1 : DirichletCharacter ℂ p) (-1) = -1 := hχ_odd_set
        rw [MulChar.one_apply (isUnit_one.neg)] at this
        exact (by norm_num : (1 : ℂ) ≠ -1) this
      have hχ_ne_η : χ ≠ η := (Finset.mem_erase.mp hχ).1
      have h_inv : χ⁻¹ = χ := h_inv_eq
      have hχ_sq : χ ^ 2 = 1 := by
        have : χ * χ⁻¹ = 1 := mul_inv_cancel _
        rw [h_inv] at this
        rw [← sq] at this; exact this
      exact hχ_ne_η (legendreDirichlet_eq_of_sq_eq_one p hp_odd hχ_sq hχ_ne_one)
    · -- χ⁻¹ ∈ S (closed under inversion).
      intro χ hχ
      have hχ_odd_set : χ ∈ oddCharacters p := (Finset.mem_erase.mp hχ).2
      have hχ_ne_η : χ ≠ η := (Finset.mem_erase.mp hχ).1
      change χ⁻¹ ∈ S
      simp only [hS, Finset.mem_erase]
      refine ⟨?_, inv_mem_oddCharacters p hχ_odd_set⟩
      intro h
      apply hχ_ne_η
      rw [← inv_inv χ, h, h_η_inv]
    · intros; exact inv_inv _
  -- From h_prod_f: ∏ (gaussSum / c) = 1 ⟹ ∏ gaussSum = c^|S|.
  rw [Finset.prod_div_distrib, Finset.prod_const] at h_prod_f
  have hc_pow_ne : c ^ S.card ≠ 0 := pow_ne_zero _ hc_ne
  have h_gauss_prod : ∏ χ ∈ S, gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      c ^ S.card := by
    field_simp at h_prod_f
    exact h_prod_f
  exact h_gauss_prod

open scoped Classical in
/-- **Signed product of Gauss sums over all odd characters** (conditional on
`gaussSum η = I·√p`): for `p ≡ 3 mod 4` prime,

`∏_{χ odd} gaussSum χ = (I · √p)^{|oddCharacters|}`.

Combines `gaussSum_oddCharacters_erase_legendre_prod` (the "without-η" product)
with the hypothesis on `gaussSum η`. -/
theorem gaussSum_oddCharacters_prod_signed
    (hp_three_mod_four : p % 4 = 3)
    (h_η : gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) ^ (oddCharacters p).card := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  classical
  have h_η_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_η_mem : legendreDirichlet p ∈ oddCharacters p := by
    simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_η_odd
  rw [← Finset.insert_erase h_η_mem, Finset.prod_insert (Finset.notMem_erase _ _), h_η,
    gaussSum_oddCharacters_erase_legendre_prod p hp_three_mod_four,
    Finset.card_insert_of_notMem (Finset.notMem_erase _ _),
    pow_succ]
  ring

/-- For `p ≡ 3 mod 4` prime, `|oddCharacters p| = (p - 1) / 2`.

Proved via the bijection `χ ↦ χ · η` between even and odd characters (where
`η = legendreDirichlet p` is odd for `p ≡ 3 mod 4`). -/
lemma card_oddCharacters_of_three_mod_four (hp_three_mod_four : p % 4 = 3) :
    (oddCharacters p).card = (p - 1) / 2 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  have hp_odd : p ≠ 2 := by omega
  have h_expo_ne : Monoid.exponent (ZMod p)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨h_expo_ne⟩
  haveI : NeZero ((Monoid.exponent (ZMod p)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr h_expo_ne⟩
  set η := legendreDirichlet p
  have h_η_odd : η.Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_η_sq : η * η = 1 := by
    have h_quad : η.IsQuadratic := legendreDirichlet_isQuadratic p
    rw [← sq]; exact MulChar.isQuadratic_iff_sq_eq_one.mp h_quad
  set E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter (·.Even) with hE
  -- Bijection: E.image (· * η) = oddCharacters p.
  have h_image : E.image (· * η) = oddCharacters p := by
    ext χ
    simp only [Finset.mem_image, hE, Finset.mem_filter, Finset.mem_univ, true_and,
      oddCharacters]
    refine ⟨?_, ?_⟩
    · rintro ⟨τ, hτ_even, rfl⟩
      change (τ * η) (-1) = -1
      rw [MulChar.mul_apply, show τ (-1) = 1 from hτ_even, show η (-1) = -1 from h_η_odd]
      ring
    · intro hχ_odd
      refine ⟨χ * η, ?_, ?_⟩
      · change (χ * η) (-1) = 1
        rw [MulChar.mul_apply, show χ (-1) = -1 from hχ_odd, show η (-1) = -1 from h_η_odd]
        ring
      · rw [mul_assoc, h_η_sq, mul_one]
  have h_inj : Function.Injective (fun χ : DirichletCharacter ℂ p ↦ χ * η) :=
    fun _ _ h ↦ mul_right_cancel h
  have h_card_eq : E.card = (oddCharacters p).card := by
    rw [← h_image, Finset.card_image_of_injective E h_inj]
  -- E ⊔ oddCharacters = univ (disjoint union).
  have h_disj : Disjoint E (oddCharacters p) := by
    rw [Finset.disjoint_left]
    intro χ hχ_E hχ_odd
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hχ_E
    simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and] at hχ_odd
    exact absurd hχ_odd hχ_E.not_odd
  have h_union : E ∪ oddCharacters p = Finset.univ := by
    ext χ
    simp only [Finset.mem_union, hE, Finset.mem_filter, Finset.mem_univ, true_and,
      oddCharacters, iff_true]
    exact χ.even_or_odd
  have h_card_univ : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    have h_nat := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
    rw [Nat.card_eq_fintype_card] at h_nat
    rw [h_nat, Nat.totient_prime hp.out]
  have h_sum_card : E.card + (oddCharacters p).card = p - 1 := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ, h_card_univ]
  omega

/-- For `p ≡ 3 mod 4` prime, `|evenNontrivialCharacters p| = (p - 3) / 2`.

Follows from `card_oddCharacters_of_three_mod_four`: `|Even| = |Odd| = (p-1)/2`,
and `Even = evenNontrivialCharacters ⊔ {1}`, so `|evenNontrivial| = (p-1)/2 - 1
= (p-3)/2`. -/
lemma card_evenNontrivialCharacters_of_three_mod_four
    (hp_three_mod_four : p % 4 = 3) :
    (evenNontrivialCharacters p).card = (p - 3) / 2 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  have hp_odd : p ≠ 2 := by omega
  -- Use: Even = evenNontrivialCharacters ⊔ {1}, and |Even| + |Odd| = p - 1,
  -- |Odd| = (p-1)/2 (from card_oddCharacters_of_three_mod_four).
  have h_odd_card := card_oddCharacters_of_three_mod_four p hp_three_mod_four
  -- Let E := filter Even univ, have |E| + |Odd| = p - 1
  set E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter (·.Even) with hE
  have h_disj : Disjoint E (oddCharacters p) := by
    rw [Finset.disjoint_left]
    intro χ hχ_E hχ_O
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and] at hχ_E
    simp only [oddCharacters, Finset.mem_filter, Finset.mem_univ, true_and] at hχ_O
    exact absurd hχ_O hχ_E.not_odd
  have h_union : E ∪ oddCharacters p = Finset.univ := by
    ext χ
    simp only [Finset.mem_union, hE, Finset.mem_filter, Finset.mem_univ, true_and,
      oddCharacters, iff_true]
    exact χ.even_or_odd
  have h_expo_ne : Monoid.exponent (ZMod p)ˣ ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (ZMod p)ˣ) := ⟨h_expo_ne⟩
  haveI : NeZero ((Monoid.exponent (ZMod p)ˣ : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr h_expo_ne⟩
  have h_card_univ : Fintype.card (DirichletCharacter ℂ p) = p - 1 := by
    have h_nat := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
    rw [Nat.card_eq_fintype_card] at h_nat
    rw [h_nat, Nat.totient_prime hp.out]
  have h_card_E : E.card = (p - 1) / 2 := by
    have : E.card + (oddCharacters p).card = p - 1 := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union, Finset.card_univ, h_card_univ]
    omega
  -- evenNontrivialCharacters = E.erase 1.
  have h_one_mem : (1 : DirichletCharacter ℂ p) ∈ E := by
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and]
    change (1 : DirichletCharacter ℂ p) (-1) = 1
    rw [MulChar.one_apply isUnit_one.neg]
  have h_eq : evenNontrivialCharacters p = E.erase 1 := by
    unfold evenNontrivialCharacters
    rw [hE]
    ext χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
    tauto
  rw [h_eq, Finset.card_erase_of_mem h_one_mem, h_card_E]
  omega

/-- **Signed Gauss sum product, explicit form** (conditional on `gaussSum η = I·√p`):
for `p ≡ 3 mod 4` prime,
`∏_{χ odd} gaussSum χ = I · √p · (-p)^{(p-3)/4}`.

Obtained by unfolding `(I · √p)^|oddCharacters|` with `|oddCharacters| = (p-1)/2`
and `(I·√p)² = -p`. -/
theorem gaussSum_oddCharacters_prod_signed_explicit
    (hp_three_mod_four : p % 4 = 3)
    (h_η : gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [gaussSum_oddCharacters_prod_signed p hp_three_mod_four h_η,
    card_oddCharacters_of_three_mod_four p hp_three_mod_four]
  -- (I · √p)^{(p-1)/2} = (I · √p) · ((I·√p)²)^{(p-3)/4} = I·√p · (-p)^{(p-3)/4}
  have h_sq : (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) ^ 2 = -(p : ℂ) := by
    have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
      rw [← Complex.cpow_mul_nat]; norm_num
    calc (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) ^ 2
        = Complex.I ^ 2 * ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 := by ring
      _ = -1 * (p : ℂ) := by rw [Complex.I_sq, h_half_sq]
      _ = -(p : ℂ) := by ring
  have h_exp : (p - 1) / 2 = 2 * ((p - 3) / 4) + 1 := by omega
  rw [h_exp, pow_succ, pow_mul, h_sq]
  ring

/-- **Signed Gauss sum product, conditional on Dedekind FE**: for `p ≡ 3 mod 4`
prime, given the Dedekind functional equation for `ℚ(ζ_p)` at some `s` with
nonvanishing factors,
`∏_{χ odd} gaussSum χ = (I · √p)^{|oddCharacters|}`.

This packages the full chain (Dedekind FE → ∏W_χ = 1 → W_η = 1 → τ(η) = I·√p
→ signed product formula) into a single theorem. -/
theorem gaussSum_oddCharacters_prod_signed_of_dedekindFE
    (hp_three_mod_four : p % 4 = 3) (s : ℂ)
    (hZ : completedRiemannZeta s ≠ 0)
    (hL : ∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ s ≠ 0)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) ^ (oddCharacters p).card :=
  gaussSum_oddCharacters_prod_signed p hp_three_mod_four
    (gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_dedekindFE p hp_three_mod_four s hZ hL h_FE)

/-- **Capstone streamlined form**: for `p ≡ 3 mod 4` prime, given the Dedekind
functional equation at some `s` with `Re s > 1`, the Gauss sum of the Legendre
character equals `I · √p`. Nonvanishing hypotheses automatically discharged. -/
theorem gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_dedekindFE_of_one_lt_re
    (hp_three_mod_four : p % 4 = 3) (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) :=
  gaussSum_legendreDirichlet_eq_I_mul_sqrt p hp_three_mod_four
    (prod_rootNumber_eq_one_of_dedekindFE_of_one_lt_re p s hs h_FE)

/-- **Explicit form of the signed Gauss sum product, conditional on Dedekind FE**:
for `p ≡ 3 mod 4` prime, given the Dedekind functional equation,
`∏_{χ odd} gaussSum χ = I · √p · (-p)^{(p-3)/4}`. -/
theorem gaussSum_oddCharacters_prod_signed_explicit_of_dedekindFE
    (hp_three_mod_four : p % 4 = 3) (s : ℂ)
    (hZ : completedRiemannZeta s ≠ 0)
    (hL : ∏ χ ∈ nontrivialCharacters p,
        DirichletCharacter.completedLFunction χ s ≠ 0)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) :=
  gaussSum_oddCharacters_prod_signed_explicit p hp_three_mod_four
    (gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_dedekindFE p hp_three_mod_four s hZ hL h_FE)

/-- **Explicit capstone streamlined**: for `p ≡ 3 mod 4` prime, given the Dedekind
functional equation at some `s` with `Re s > 1`,
`∏_{χ odd} gaussSum χ = I · √p · (-p)^{(p-3)/4}`. -/
theorem gaussSum_oddCharacters_prod_signed_explicit_of_dedekindFE_of_one_lt_re
    (hp_three_mod_four : p % 4 = 3) (s : ℂ) (hs : 1 < s.re)
    (h_FE : completedRiemannZeta (1 - s) *
        (∏ χ ∈ nontrivialCharacters p,
          DirichletCharacter.completedLFunction χ (1 - s)) =
      (p : ℂ) ^ (((p : ℕ) - 2 : ℕ) * (s - 1 / 2 : ℂ)) *
        (completedRiemannZeta s *
          ∏ χ ∈ nontrivialCharacters p,
            DirichletCharacter.completedLFunction χ s)) :
    ∏ χ ∈ oddCharacters p,
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)) * (-(p : ℂ)) ^ ((p - 3) / 4) :=
  gaussSum_oddCharacters_prod_signed_explicit p hp_three_mod_four
    (gaussSum_legendreDirichlet_eq_I_mul_sqrt_of_dedekindFE_of_one_lt_re
      p hp_three_mod_four s hs h_FE)

end RootNumberConjugatePairing

end BernoulliRegular
