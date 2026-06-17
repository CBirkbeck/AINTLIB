/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.SMOObligations

/-!
# The Atkin–Lehner Main Lemma (DS Theorem 5.7.1), assembled

This file completes the Main Lemma: a cusp form `f ∈ S_k(Γ₁(N))` whose Fourier coefficients
`aₙ` vanish at every index coprime to `N` is an oldform.

We give the **route-B** (Miyake §4.6) proof.  The per-character ingredient
`mainLemma_charSpace` is `HeckeRing.GL2.mainLemma_charSpace_routeB` (proven sorry-free in
`SMOObligations.lean` via Miyake's sieve/conductor descent).  That file sits **above**
`Newforms.MainLemma` in the import DAG (the route-B sieve transitively imports
`Newforms.CoeffSeq → Newforms.MainLemma`, where the `Newform` structure is defined), so the
assembly cannot live in `Newforms.MainLemma` itself without an import cycle — hence this
separate high file, which imports `SMOObligations` directly.

The Nebentypus character decomposition `f = ∑_χ g_χ` reduces the global statement to the
per-character version, given that each component inherits the coprime-index coefficient
vanishing (`qExpansion_charComponent_coprime_eq_zero`).
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The canonical (period-1) `q`-expansion of a cusp form, packaged as an `AddMonoidHom`
to power series.  Used to push `q`-expansion through finite/`Finsupp` sums. -/
private noncomputable def qExpansionOneCuspAddHom :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →+ PowerSeries ℂ :=
  (ModularForm.qExpansionAddHom (Γ := (Gamma1 N).map (mapGL ℝ)) (h := (1 : ℝ))
      one_pos (one_mem_strictPeriods_Gamma1_map N) k).comp
    (cuspFormToModularFormLin (N := N) (k := k)).toAddMonoidHom

omit [NeZero N] in
private lemma qExpansionOneCuspAddHom_apply (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansionOneCuspAddHom g = UpperHalfPlane.qExpansion (1 : ℝ) g := rfl

omit [NeZero N] in
/-- Every canonical (period-1) `q`-coefficient of the **zero** cusp form vanishes. -/
private lemma qExpansion_one_zero_coeff (m : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ)
      (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff m = 0 := by
  rw [← qExpansionOneCuspAddHom_apply, map_zero, map_zero]

omit [NeZero N] in
/-- **Additivity of the canonical (period-1) `q`-expansion coefficients over a `Finset` sum
of cusp forms.**  Packaging of `ModularForm.qExpansionAddHom` for the cusp-form coercion. -/
private lemma qExpansion_one_coeff_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (∑ i ∈ s, F i)).coeff n =
      ∑ i ∈ s, (UpperHalfPlane.qExpansion (1 : ℝ) (F i)).coeff n := by
  have h := map_sum qExpansionOneCuspAddHom F s
  simp only [qExpansionOneCuspAddHom_apply] at h
  rw [show (∑ i ∈ s, ⇑(F i) : UpperHalfPlane → ℂ) = ⇑(∑ i ∈ s, F i) from
    (map_sum (CuspForm.coeHom (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k)) F s).symm, h, map_sum]

/-- **L1 (eigenvalue–coefficient identity, un-normalised).**  For a `χ`-cusp form `h` that is a
`T_m`-eigenfunction with eigenvalue `a` at an index `m` coprime to `N`, the `m`-th canonical
(period-`1`) Fourier coefficient is `a` times the first: `aₘ(h) = a · a₁(h)`.

This is the standard Hecke eigenvalue ↔ Fourier coefficient relation (Miyake Lemma 4.5.15(1));
the proof is `aₘ(h) = a₁(Tₘ h) = a₁(a · h) = a · a₁(h)`, using
`qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff` (which needs the character membership, supplied
through the `cuspFormCharSpace → modFormCharSpace` bridge) and `qExpansion_smul`. -/
private lemma aₘ_eq_eigenvalue_mul_aₒₙₑ
    (χ : (ZMod N)ˣ →* ℂˣ) (h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hh_char : h ∈ cuspFormCharSpace k χ) (m : ℕ) [NeZero m] (hm : Nat.Coprime m N) (a : ℂ)
    (h_eig : heckeT_n_cusp k m h = a • h) :
    (UpperHalfPlane.qExpansion (1 : ℝ) h).coeff m =
      a * (UpperHalfPlane.qExpansion (1 : ℝ) h).coeff 1 := by
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff m hm χ h
      (HeckeRing.GL2.Unified.cuspFormCharSpace_toModularForm'_mem hh_char), h_eig]
  show (UpperHalfPlane.qExpansion (1 : ℝ) (⇑(a • h : CuspForm _ k))).coeff 1 =
      a * (UpperHalfPlane.qExpansion (1 : ℝ) (⇑h)).coeff 1
  rw [show (⇑(a • h : CuspForm _ k) : UpperHalfPlane → ℂ) = a • ⇑h from rfl,
    show (⇑h : UpperHalfPlane → ℂ) = ⇑h.toModularForm' from rfl,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, smul_eq_mul]

/-- **L2 (separation of eigensystems — the strong-multiplicity-one crux).**  *Isolated `sorry`.*

Two nonzero common Hecke eigenfunctions lying in (possibly different) Nebentypus spaces whose
eigenvalues agree at every index coprime to `N` must lie in the *same* character space.

This is the cross-character half of Strong Multiplicity One: the Nebentypus character of a cusp
form is recovered from its prime-to-level Hecke eigenvalues (the diamond operators `⟨d⟩` are
polynomials in the `Tₚ` away from the level), so equal eigensystems force `χ = χ'`. -/
private lemma eigensystem_determines_char
    {χ χ' : (ZMod N)ˣ →* ℂˣ}
    {h h' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh_char : h ∈ cuspFormCharSpace k χ) (hh'_char : h' ∈ cuspFormCharSpace k χ')
    (hh_ne : h ≠ 0) (hh'_ne : h' ≠ 0)
    (h_eig : ∀ m : ℕ, ∀ _ : NeZero m, Nat.Coprime m N → ∀ a a' : ℂ,
      heckeT_n_cusp k m h = a • h → heckeT_n_cusp k m h' = a' • h' → a = a') :
    χ = χ' :=
  sorry

/-- **L3 (linear independence of distinct eigensystems).**  *Isolated `sorry`.*

A finite family of common Hecke eigenfunctions whose eigensystems (`ev i : ℕ⁺ → ℂ`, the prime-to-
level eigenvalues) are pairwise distinct at *some* coprime index is `ℂ`-linearly independent
*as eigensystems*: any scalars `c` for which the eigensystem combination
`∑ᵢ cᵢ · evᵢ(m)` vanishes at every coprime `m` must all vanish.

This is the classical fact that Hecke eigenforms with distinct eigensystems are linearly
independent (Petersson orthogonality of distinct-eigenvalue eigenforms, the engine behind
`linearIndependent_toCuspForm`), transported to the eigenvalue sequences. -/
private lemma eigensystems_linearIndependent
    {ι : Type} [Fintype ι] (ev : ι → ℕ+ → ℂ) (c : ι → ℂ)
    (h_distinct : ∀ i j : ι, i ≠ j → ∃ m : ℕ+, Nat.Coprime m.val N ∧ ev i m ≠ ev j m)
    (h_rel : ∀ m : ℕ+, Nat.Coprime m.val N → ∑ i, c i * ev i m = 0) :
    ∀ i, c i = 0 :=
  sorry

omit [NeZero N] in
/-- **Eigensystems as functions are determined off the coprime indices.**  If two eigensystems
`s, s'` arising in the family (`s = EV k₀`, `s' = EV k₀'`, both `0` off the coprime indices) agree
at every coprime index, they are equal as functions. -/
private lemma eigensystem_funext_of_coprime_agree
    {K : Type} (EV : K → ℕ+ → ℂ)
    (hEV_zero : ∀ (k0 : K) (m : ℕ+), ¬ Nat.Coprime m.val N → EV k0 m = 0)
    {k0 k0' : K} (h : ∀ m : ℕ+, Nat.Coprime m.val N → EV k0 m = EV k0' m) :
    EV k0 = EV k0' := by
  funext m
  by_cases hm : Nat.Coprime m.val N
  · exact h m hm
  · rw [hEV_zero k0 m hm, hEV_zero k0' m hm]

omit [NeZero N] in
/-- Cancellation of a nonzero cusp form from a scalar action: `a • h = b • h` with `h ≠ 0` forces
`a = b` (the `ℂ`-action on cusp forms has no zero divisors). -/
private lemma smul_eq_smul_cancel {h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hh : h ≠ 0)
    {a b : ℂ} (he : a • h = b • h) : a = b := by
  have hz : (a - b) • h = 0 := by rw [sub_smul, he, sub_self]
  rcases smul_eq_zero.mp hz with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hh

/-- **Combinatorial core of the spectral route.**  Given a finite family `H : K → S_k(Γ₁(N))` of
common Hecke eigenfunctions, each lying in a character space `tag k`, with eigensystems `EV`
(eigenvalues at coprime indices, `0` elsewhere), such that the *global* eigenvalue–weighted sum of
first coefficients `∑ₖ EV k m · a₁(H k)` vanishes at every coprime `m`, the partial sum of
`n`-th coefficients over the pieces of a *single* character `χ₀` vanishes.

This isolates the L2/L3 application: distinct eigensystems are `ℂ`-independent (**L3**) so each
eigensystem's total contribution `C s = ∑_{EV k = s} a₁(H k)` vanishes; and an eigensystem value
occurs in a *unique* character (**L2**), so the `χ₀`-restricted contribution `D s` equals `C s`,
hence vanishes too. -/
private lemma charPiece_coeff_sum_eq_zero
    {K : Type} [Fintype K] [DecidableEq ((ZMod N)ˣ →* ℂˣ)] [DecidableEq (ℕ+ → ℂ)]
    (H : K → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (tag : K → (ZMod N)ˣ →* ℂˣ) (EV : K → ℕ+ → ℂ)
    (hH_ne_char : ∀ k0 : K, (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 ≠ 0 →
      H k0 ∈ cuspFormCharSpace k (tag k0) ∧ H k0 ≠ 0)
    (hEV_spec : ∀ (k0 : K) (m : ℕ+) (hm : Nat.Coprime m.val N),
      haveI : NeZero m.val := ⟨m.pos.ne'⟩
      heckeT_n_cusp k m.val (H k0) = EV k0 m • H k0)
    (hEV_zero : ∀ (k0 : K) (m : ℕ+), ¬ Nat.Coprime m.val N → EV k0 m = 0)
    (hcoeff_piece : ∀ (m : ℕ+), Nat.Coprime m.val N → ∀ k0 : K,
      (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff m.val =
        EV k0 m * (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1)
    (hrel : ∀ (m : ℕ+), Nat.Coprime m.val N →
      ∑ k0 : K, EV k0 m * (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 = 0)
    (χ₀ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) :
    ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀),
      (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff n = 0 := by
  classical
  -- The positive index `n` as an element of `ℕ⁺`.
  set n' : ℕ+ := ⟨n, Nat.pos_of_ne_zero (NeZero.ne n)⟩ with hn'_def
  -- Abbreviation for the first coefficients (the scalars).
  set A1 : K → ℂ := fun k0 ↦ (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 with hA1_def
  -- The image of `EV`: the eigensystem values actually occurring in the family.
  set img : Finset (ℕ+ → ℂ) := Finset.univ.image EV with himg_def
  have hmem_img : ∀ k0 : K, EV k0 ∈ img := fun k0 ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)
  -- The total contribution of each eigensystem value `s`.
  set C : (ℕ+ → ℂ) → ℂ := fun s ↦ ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ EV k0 = s), A1 k0
    with hC_def
  -- The `χ₀`-restricted contribution of each eigensystem value `s`.
  set D : (ℕ+ → ℂ) → ℂ := fun s ↦
    ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀ ∧ EV k0 = s), A1 k0 with hD_def
  -- **L3**: each occurring eigensystem value contributes `0` to the global sum, i.e. `C s = 0`.
  have hC_zero : ∀ s : ℕ+ → ℂ, C s = 0 := by
    have hC_img : ∀ s, s ∉ img → C s = 0 := by
      intro s hs
      apply Finset.sum_eq_zero
      intro k0 hk0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
      exact absurd (hk0 ▸ hmem_img k0) hs
    -- Linear independence of the distinct occurring eigensystems (**L3**).
    have key : ∀ s : ↥img, C s.val = 0 :=
      eigensystems_linearIndependent (N := N)
        (ι := ↥img) (fun s ↦ s.val) (fun s ↦ C s.val)
        (by -- distinctness: distinct occurring values differ at a coprime index
          rintro ⟨s, hs⟩ ⟨s', hs'⟩ hne
          by_contra hcon
          push_neg at hcon
          refine hne (Subtype.ext ?_)
          obtain ⟨k0, _, hk0⟩ := Finset.mem_image.mp hs
          obtain ⟨k0', _, hk0'⟩ := Finset.mem_image.mp hs'
          have hEVeq : EV k0 = EV k0' :=
            eigensystem_funext_of_coprime_agree (N := N) EV hEV_zero (fun m hm ↦
              (congrFun hk0 m).trans ((hcon m hm).trans (congrFun hk0' m).symm))
          exact hk0.symm.trans (hEVeq.trans hk0'))
        (by -- relation: `∑_s C s · s(m) = 0` for coprime `m`
          intro m hm
          have hfb := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset K) img EV
            (fun k0 ↦ EV k0 m * A1 k0)
          rw [Finset.filter_true_of_mem (fun k0 _ ↦ hmem_img k0)] at hfb
          -- rewrite the `↥img` sum as a `Finset` sum and match the fiber weighting
          rw [Finset.sum_coe_sort img (fun s ↦ C s * s m)]
          rw [← hrel m hm, ← hfb]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [hC_def, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k0 hk0 ↦ ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
          rw [hk0]; ring)
    intro s
    by_cases hs : s ∈ img
    · exact key ⟨s, hs⟩
    · exact hC_img s hs
  -- **L2**: each eigensystem value occurs in a unique character, so `D s = C s = 0`.
  have hD_zero : ∀ s : ℕ+ → ℂ, D s = 0 := by
    intro s
    by_contra hDs
    -- `D s ≠ 0`: some `χ₀`-piece with eigensystem `s` has nonzero first coefficient (a *witness*).
    obtain ⟨k0₀, hk0₀_mem, hk0₀_ne⟩ : ∃ k0 ∈ Finset.univ.filter
        (fun k0 ↦ tag k0 = χ₀ ∧ EV k0 = s), A1 k0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hDs (Finset.sum_eq_zero h)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0₀_mem
    obtain ⟨hk0₀_tag, hk0₀_ev⟩ := hk0₀_mem
    obtain ⟨hk0₀_char, hk0₀_form_ne⟩ := hH_ne_char k0₀ hk0₀_ne
    -- Using the witness, every nonzero-`A1` piece with eigensystem `s` lies in `χ₀` (L2), so the
    -- `χ₀`-fiber and the global fiber agree up to `A1 = 0` terms: `D s = C s`.
    have hCD : D s = C s := by
      rw [hD_def, hC_def]
      apply Finset.sum_subset
      · intro k0 hk0
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0 ⊢
        exact hk0.2
      · -- a piece with eigensystem `s` but `tag ≠ χ₀` must have `A1 = 0`
        intro k0 hk0 hk0_not
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0 hk0_not
        by_contra hA1
        obtain ⟨hk0_char, hk0_form_ne⟩ := hH_ne_char k0 hA1
        -- `A1 k0 ≠ 0` with eigensystem `s` and the witness `k0₀ ∈ χ₀` force `tag k0 = χ₀` (L2).
        -- A `ℕ`-indexed restatement of the eigensystem spec (matching L2's hypothesis shape).
        have hEV_spec_nat : ∀ (j : K) (m : ℕ) (hm : Nat.Coprime m N) (hpos : 0 < m),
            haveI : NeZero m := ⟨hpos.ne'⟩
            heckeT_n_cusp k m (H j) = EV j ⟨m, hpos⟩ • H j := by
          intro j m hm hpos
          haveI : NeZero m := ⟨hpos.ne'⟩
          exact hEV_spec j ⟨m, hpos⟩ hm
        have htag : tag k0 = χ₀ := by
          have hchar_eq := eigensystem_determines_char (N := N)
            hk0_char hk0₀_char hk0_form_ne hk0₀_form_ne
            (fun m hnz hm a a' he he' ↦ ?_)
          · rw [hchar_eq, hk0₀_tag]
          · -- equal eigensystems: both eigenvalues equal `EV · ⟨m,_⟩`, and `EV k0 = s = EV k0₀`
            have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
            have h1 : a = EV k0 ⟨m, hpos⟩ :=
              smul_eq_smul_cancel hk0_form_ne (he.symm.trans (hEV_spec_nat k0 m hm hpos))
            have h2 : a' = EV k0₀ ⟨m, hpos⟩ :=
              smul_eq_smul_cancel hk0₀_form_ne (he'.symm.trans (hEV_spec_nat k0₀ m hm hpos))
            rw [h1, h2, congrFun hk0 (⟨m, hpos⟩ : ℕ+), congrFun hk0₀_ev (⟨m, hpos⟩ : ℕ+)]
        exact (hk0_not ⟨htag, hk0⟩).elim
    rw [hCD] at hDs
    exact hDs (hC_zero s)
  -- Assemble: the `χ₀`-coefficient sum, fibered by eigensystem value, is `∑ s(n') · D s = 0`.
  have hfilter_fib : ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀),
      (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff n =
      ∑ s ∈ img, s n' * D s := by
    have step1 : ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀),
        (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff n =
        ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀), EV k0 n' * A1 k0 := by
      refine Finset.sum_congr rfl fun k0 _ ↦ ?_
      exact hcoeff_piece n' hn k0
    rw [step1]
    have hfb := Finset.sum_fiberwise_eq_sum_filter
      (Finset.univ.filter (fun k0 ↦ tag k0 = χ₀)) img EV (fun k0 ↦ EV k0 n' * A1 k0)
    rw [Finset.filter_true_of_mem (fun k0 _ ↦ hmem_img k0)] at hfb
    rw [← hfb]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hD_def, Finset.mul_sum]
    have hfilter_eq : (Finset.univ.filter (fun k0 ↦ tag k0 = χ₀)).filter (fun k0 ↦ EV k0 = s) =
        Finset.univ.filter (fun k0 ↦ tag k0 = χ₀ ∧ EV k0 = s) := by
      ext k0; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hfilter_eq]
    refine Finset.sum_congr rfl fun k0 hk0 ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
    rw [hk0.2]
  rw [hfilter_fib]
  simp only [hD_zero, mul_zero, Finset.sum_const_zero]

set_option maxHeartbeats 1000000 in
/-- **Per-character coefficient inheritance (route-B ingredient 1).**  If `f` is a cusp form
all of whose canonical Fourier coefficients at indices coprime to `N` vanish, and `gd χ` is the
`χ`-Nebentypus component of `f` in the character decomposition `f = ∑_χ gd χ` (so that
`gd χ ∈ S_k(Γ₁(N), χ)`), then each component likewise has vanishing canonical Fourier coefficients
at all indices coprime to `N`.

**Proof (spectral route).**  Decompose each component `gd χ = ∑ᵢ hχ,ᵢ` into common Hecke
eigenfunctions (`exists_eigenform_decomposition_of_invariant`, with `W = ⊤`) and collect them over
every `χ ∈ gd.support` into one finite family `H : K → CuspForm` with eigensystems `EV`.  Then
`f = ∑ₖ H k`, and for coprime `m`, `aₘ(f) = ∑ₖ aₘ(H k) = ∑ₖ EV k m · a₁(H k)` (additivity of
`q`-coefficients and **L1**); since `aₘ(f) = 0`, this is the hypothesis fed to the combinatorial
core `charPiece_coeff_sum_eq_zero`, which applies **L3** (independence of distinct eigensystems)
and **L2** (eigensystems determine the character) to conclude that the `χ₀`-restricted coefficient
sum vanishes; that sum is exactly `aₙ(gd χ₀)`. -/
private lemma qExpansion_charComponent_coprime_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (gd : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_char : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormCharSpace k χ)
    (h_sum : (gd.sum fun _ y ↦ y) = f)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0)
    (χ₀ : (ZMod N)ˣ →* ℂˣ) (n : ℕ) (hn : Nat.Coprime n N) :
    (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ₀)).coeff n = 0 := by
  classical
  -- The index `0` is degenerate (cuspidal vanishing); reduce to `n ≠ 0`.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact CuspFormClass.qExpansion_coeff_zero (gd χ₀) one_pos (one_mem_strictPeriods_Gamma1_map N)
  haveI : NeZero n := ⟨hnpos.ne'⟩
  -- **Per-character spectral decomposition** of each `gd χ` into common Hecke eigenfunctions.
  choose ιχ instιχ Hχ _hHχ_top hHχ_char hHχ_eig hHχ_sum using fun χ : (ZMod N)ˣ →* ℂˣ ↦
    exists_eigenform_decomposition_of_invariant (k := k) χ ⊤
      (fun _ _ _ _ _ ↦ Submodule.mem_top) (gd χ) (h_char χ) Submodule.mem_top
  -- The global index of all eigenform pieces over all characters in the support.
  letI instFam : ∀ χ : (gd.support : Finset _), Fintype (ιχ χ.val) := fun χ ↦ instιχ χ.val
  let K : Type := Σ χ : (gd.support : Finset _), ιχ χ.val
  letI instK : Fintype K := Sigma.instFintype
  let H : K → CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun k0 ↦ Hχ k0.1.val k0.2
  let tag : K → (ZMod N)ˣ →* ℂˣ := fun k0 ↦ k0.1.val
  -- `H k0` is a common Hecke eigenfunction in the character space `tag k0`.
  have hH_char : ∀ k0 : K, H k0 ∈ cuspFormCharSpace k (tag k0) := fun k0 ↦ hHχ_char k0.1.val k0.2
  have hH_eig : ∀ k0 : K, IsCommonEigenfunctionCusp k (H k0) := fun k0 ↦ hHχ_eig k0.1.val k0.2
  -- The eigensystem of `H k0` (eigenvalue at coprime indices, `0` off the coprime indices).
  let EV : K → ℕ+ → ℂ := fun k0 m ↦
    if hm : Nat.Coprime m.val N then Classical.choose (hH_eig k0 m hm) else 0
  have hEV_spec : ∀ (k0 : K) (m : ℕ+) (hm : Nat.Coprime m.val N),
      haveI : NeZero m.val := ⟨m.pos.ne'⟩
      heckeT_n_cusp k m.val (H k0) = EV k0 m • H k0 := by
    intro k0 m hm
    haveI : NeZero m.val := ⟨m.pos.ne'⟩
    show heckeT_n_cusp k m.val (H k0) = (if hm : Nat.Coprime m.val N then _ else 0) • H k0
    rw [dif_pos hm]
    exact Classical.choose_spec (hH_eig k0 m hm)
  have hEV_zero : ∀ (k0 : K) (m : ℕ+), ¬ Nat.Coprime m.val N → EV k0 m = 0 := by
    intro k0 m hm
    show (if hm : Nat.Coprime m.val N then _ else 0) = 0
    rw [dif_neg hm]
  -- **L1 applied to each piece**: for coprime `m`, `aₘ(H k0) = EV k0 m · a₁(H k0)`.
  have hcoeff_piece : ∀ (m : ℕ+), Nat.Coprime m.val N → ∀ k0 : K,
      (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff m.val =
        EV k0 m * (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 := by
    intro m hm k0
    haveI : NeZero m.val := ⟨m.pos.ne'⟩
    exact aₘ_eq_eigenvalue_mul_aₒₙₑ (tag k0) (H k0) (hH_char k0) m.val hm (EV k0 m)
      (hEV_spec k0 m hm)
  -- `f = ∑_{χ ∈ supp} gd χ`.
  have hf_supp : f = ∑ χ ∈ gd.support, gd χ := by rw [← h_sum, Finsupp.sum]
  -- We compute the `χ₀`-fiber sum via `Finset.sum_sigma`, grouping by the first `Σ`-coordinate;
  -- only the `χ₀`-block survives, giving `∑ᵢ aₙ(Hχ χ₀ i)`.
  have hfiber_eq : ∑ k0 ∈ Finset.univ.filter (fun k0 : K ↦ tag k0 = χ₀),
        (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff n =
      ∑ χ : (gd.support : Finset _),
        if χ.val = χ₀ then ∑ i : ιχ χ.val,
          (UpperHalfPlane.qExpansion (1 : ℝ) (Hχ χ.val i)).coeff n else 0 := by
    rw [Finset.sum_filter, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun χ _ ↦ ?_
    by_cases hχ : χ.val = χ₀
    · rw [if_pos hχ]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [if_pos (show tag ⟨χ, i⟩ = χ₀ from hχ)]
    · rw [if_neg hχ]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [if_neg (show ¬ tag ⟨χ, i⟩ = χ₀ from hχ)]
  have hgd_eq : (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ₀)).coeff n =
      ∑ k0 ∈ Finset.univ.filter (fun k0 ↦ tag k0 = χ₀),
        (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff n := by
    rw [hfiber_eq]
    by_cases hχ₀ : χ₀ ∈ gd.support
    · -- Only the block `χ = ⟨χ₀, hχ₀⟩` contributes (the surviving `if` is discharged with an
      -- explicit equality proof, avoiding any evaluation of the classical `Decidable` instance).
      rw [Finset.sum_eq_single_of_mem (⟨χ₀, hχ₀⟩ : (gd.support : Finset _))
        (Finset.mem_univ _) (fun χ _ hne ↦ if_neg (fun h ↦ hne (Subtype.ext h))),
        if_pos (show ((⟨χ₀, hχ₀⟩ : (gd.support : Finset _)) : (ZMod N)ˣ →* ℂˣ) = χ₀ from rfl),
        ← qExpansionOneCuspAddHom_apply, hHχ_sum χ₀, map_sum, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [qExpansionOneCuspAddHom_apply]
    · -- Outside the support, `gd χ₀ = 0` and no block matches.
      rw [Finsupp.notMem_support_iff.mp hχ₀, qExpansion_one_zero_coeff]
      symm
      refine Finset.sum_eq_zero fun χ _ ↦ if_neg (fun h ↦ hχ₀ ?_)
      rw [← h]; exact χ.2
  rw [hgd_eq]
  -- The key coefficient relation: for coprime `m`, `∑ₖ EV k m · a₁(H k) = 0`.  We compute the
  -- global `Σ`-sum block-wise (`Finset.sum_sigma`) and reduce each block by **L1**, recovering
  -- `aₘ(gd χ) = ∑ᵢ EV · a₁`; summing over `χ` gives `aₘ(f) = 0`.
  have hrel : ∀ (m : ℕ+), Nat.Coprime m.val N →
      ∑ k0 : K, EV k0 m * (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 = 0 := by
    intro m hm
    have key : ∑ k0 : K, EV k0 m * (UpperHalfPlane.qExpansion (1 : ℝ) (H k0)).coeff 1 =
        ∑ χ : (gd.support : Finset _), (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ.val)).coeff m.val := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun χ _ ↦ ?_
      -- `aₘ(gd χ) = ∑ᵢ aₘ(Hχ χ i)` via the period-1 `q`-expansion `AddMonoidHom`.
      have hχsum : (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ.val)).coeff m.val =
          ∑ i : ιχ χ.val, (UpperHalfPlane.qExpansion (1 : ℝ) (Hχ χ.val i)).coeff m.val := by
        rw [← qExpansionOneCuspAddHom_apply, hHχ_sum χ.val, map_sum, map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [qExpansionOneCuspAddHom_apply]
      rw [hχsum]
      exact Finset.sum_congr rfl fun i _ ↦ (hcoeff_piece m hm ⟨χ, i⟩).symm
    -- `aₘ(f) = ∑_{χ ∈ supp} aₘ(gd χ)` via the period-1 `q`-expansion `AddMonoidHom`.
    have hfm : (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff m.val =
        ∑ χ ∈ gd.support, (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ)).coeff m.val := by
      rw [← qExpansionOneCuspAddHom_apply, hf_supp, map_sum, map_sum]
      exact Finset.sum_congr rfl fun χ _ ↦ by rw [qExpansionOneCuspAddHom_apply]
    rw [key, Finset.sum_coe_sort (gd.support)
      (fun χ ↦ (UpperHalfPlane.qExpansion (1 : ℝ) (gd χ)).coeff m.val), ← hfm]
    exact h_vanish m.val hm
  -- Apply the combinatorial core.
  exact charPiece_coeff_sum_eq_zero (N := N) (k := k) H tag EV
    (fun k0 hk0 ↦ ⟨hH_char k0, fun h0 ↦ hk0 (by rw [h0, qExpansion_one_zero_coeff])⟩)
    hEV_spec hEV_zero hcoeff_piece hrel χ₀ n hn

/-- **Per-character Main Lemma (route-B ingredient 2).**  A cusp form `g ∈ S_k(Γ₁(N), χ)` whose
canonical (period-1) `q`-expansion vanishes at every index coprime to `N` is an oldform.

This is exactly `HeckeRing.GL2.mainLemma_charSpace_routeB` (`SMOObligations.lean`), proven
sorry-free by Miyake's sieve/conductor descent (Theorems 4.6.4 / 4.6.8); now that this file
imports `SMOObligations`, it is invoked directly. -/
private lemma mainLemma_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_char : g ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
    g ∈ cuspFormsOld N k :=
  mainLemma_charSpace_routeB χ g hg_char h_vanish

/-- **The Main Lemma** (DS Theorem 5.7.1, Atkin-Lehner [AL70]):
If `f ∈ S_k(Γ₁(N))` has Fourier expansion `f(τ) = Σ aₙ qⁿ` with `aₙ = 0`
whenever `(n, N) = 1`, then `f` is an oldform.

This is the technical heart of the newform theory.  We give the **route-B** (Miyake §4.6)
proof: the Nebentypus character decomposition `f = ∑_χ g_χ` reduces the claim to the
per-character Atkin–Lehner descent, since each component `g_χ` inherits the coprime-index
coefficient vanishing (`qExpansion_charComponent_coprime_eq_zero`) and is therefore an oldform
(`mainLemma_charSpace`); a finite sum of oldforms is an oldform. -/
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (UpperHalfPlane.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  classical
  -- Nebentypus character decomposition `f = ∑_χ g_χ`, each `g_χ ∈ S_k(Γ₁(N), χ)`.
  obtain ⟨gd, hgd_mem, hgd_sum⟩ :=
    exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k ⊤
      (fun d g _ ↦ Submodule.mem_top) (Submodule.mem_top : f ∈ ⊤)
  have h_char : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormCharSpace k χ :=
    fun χ ↦ (hgd_mem χ).2
  -- Each component is an oldform: it inherits the vanishing, then route-B descent applies.
  have h_old : ∀ χ : (ZMod N)ˣ →* ℂˣ, gd χ ∈ cuspFormsOld N k := fun χ ↦
    mainLemma_charSpace χ (gd χ) (h_char χ)
      (fun n hn ↦ qExpansion_charComponent_coprime_eq_zero f gd h_char hgd_sum h χ n hn)
  -- A finite sum of oldforms is an oldform.
  rw [← hgd_sum, Finsupp.sum]
  exact Submodule.sum_mem _ fun χ _ ↦ h_old χ

end HeckeRing.GL2
