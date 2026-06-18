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

/-- **Oldforms vanish at coprime indices.**  If `g ∈ cuspFormsOld N k` and `(n, N) = 1`, then the
`n`-th canonical (period-1) Fourier coefficient of `g` is `0`.

This is the *forward* half of the Atkin–Lehner support analysis (DS §5.7): a single oldform
generator `V_d h` (`d > 1`, `d ∣ N`) has `q`-expansion supported on multiples of `d`
(`AtkinLehner.qExpansion_levelRaise_isSupportedOnDvd`), and for `(n,N) = 1` and `1 < d ∣ N` one has
`d ∤ n` (else `1 < gcd(d,n) ∣ gcd(N,n) = 1`); the statement extends to the whole span by additivity
of the `q`-coefficient (`qExpansionOneCuspAddHom`). -/
lemma coeff_eq_zero_of_mem_cuspFormsOld
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hg : g ∈ cuspFormsOld N k)
    {n : ℕ} (hn : Nat.Coprime n N) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0 := by
  -- `span_induction` on `g`, on the motive `aₙ(x) = 0`; additivity/scalar of the `q`-coefficient
  -- come from `qExpansionOneCuspAddHom`.
  rw [show (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n =
      (PowerSeries.coeff (R := ℂ) n) (qExpansionOneCuspAddHom (N := N) (k := k) g) from by
    rw [qExpansionOneCuspAddHom_apply]]
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, d, hM, hd, hd1, heq, h, rfl⟩ := hx
    haveI : NeZero M := hM
    haveI : NeZero d := hd
    -- `d ∤ n` from `1 < d`, `d ∣ N`, `(n, N) = 1`.
    have hdN : d ∣ N := ⟨M, heq.symm⟩
    have hdn : ¬ d ∣ n := fun hdvd ↦ by
      have : d ∣ Nat.gcd n N := Nat.dvd_gcd hdvd hdN
      rw [hn] at this
      exact absurd (Nat.le_of_dvd Nat.one_pos this) (Nat.not_le.mpr hd1)
    -- Support of the level-raise on multiples of `d`.
    have hsupp : AtkinLehner.QExpansionSupportedOnDvd d
        (heq ▸ levelRaise M d k h : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
      AtkinLehner.levelRaise_mem_qSupportedOnDvdSubmodule (N := N) heq h
    rw [qExpansionOneCuspAddHom_apply]; exact hsupp n hdn
  | zero => rw [map_zero, map_zero]
  | add x y _ _ ihx ihy => rw [map_add, map_add, ihx, ihy, add_zero]
  | smul c x _ ihx =>
    rw [qExpansionOneCuspAddHom_apply] at ihx ⊢
    rw [show (⇑(c • x : CuspForm _ k) : UpperHalfPlane → ℂ) = c • ⇑x.toModularForm' from rfl,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
      PowerSeries.coeff_smul, smul_eq_mul,
      show (UpperHalfPlane.qExpansion (1 : ℝ) ⇑x.toModularForm') =
        UpperHalfPlane.qExpansion (1 : ℝ) x from rfl, ihx, mul_zero]

/-! ### Eigensystem arithmetic for normalised eigenforms

The following block develops the Hecke-eigensystem identities (coprime multiplicativity, the
prime-square character relation, and the "agree off a finite set ⟹ agree everywhere" propagation)
for a **normalised period-1 eigenform** in a single Nebentypus space, working directly with the
Fourier coefficients `aₙ = (qExpansion 1 g).coeff n` (so `a₁ = 1`).  These mirror the `Eigenform`
versions in `StrongMultiplicityOneFull.lean`, but are stated for the bare normalised data
`IsNormalisedEigenform_one` so they apply to any normalised common eigenfunction (not only bundled
`Eigenform`/`Newform`s), and are the engine for the strong-multiplicity-one separation of new
eigenforms used in L3.  None of them invokes `mainLemma` (only the public
`eigenform_coeff_multiplicative_one`), so they are non-circular. -/

variable {χ : (ZMod N)ˣ →* ℂˣ}

/-- **Coprime multiplicativity of Fourier coefficients** of a normalised eigenform:
`a_{mn} = a_m · a_n` when `gcd(m, n) = 1` (`m, n` coprime to `N`).  Direct specialisation of
`eigenform_coeff_multiplicative_one` at `gcd = 1`. -/
private lemma normEigen_coeff_coprime_mul
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgχ : g.toModularForm' ∈ modFormCharSpace k χ)
    (hg_eig : IsNormalisedEigenform_one k g.toModularForm')
    (m n : ℕ+) (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (m.val * n.val) =
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff m.val *
        (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n.val := by
  have h := eigenform_coeff_multiplicative_one (N := N) k m n hm hn χ hgχ hg_eig
  rw [(hmn : Nat.gcd m.val n.val = 1), Nat.divisors_one, Finset.sum_singleton,
    dif_pos (Nat.coprime_one_left N),
    show ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 by ext; simp [ZMod.coe_unitOfCoprime]]
    at h
  simp only [Nat.cast_one, one_zpow, map_one, Units.val_one, one_mul, mul_one, Nat.div_one] at h
  -- `(qExpansion 1 g).coeff = (qExpansion 1 g.toModularForm').coeff`
  rw [show (⇑g : UpperHalfPlane → ℂ) = ⇑g.toModularForm' from rfl] at *
  exact h.symm

/-- **Prime-square character relation** for a normalised eigenform:
`a_{q²} = a_q² − χ(q)·q^{k-1}` for a prime `q ∤ N`.  Mirrors
`eigenvalue_at_prime_sq_of_coeff_one_ne_zero`, stated via coefficients. -/
private lemma normEigen_coeff_prime_sq
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgχ : g.toModularForm' ∈ modFormCharSpace k χ)
    (hg_eig : IsNormalisedEigenform_one k g.toModularForm')
    {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (q ^ 2) =
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff q ^ 2 -
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
  have hq_pos : 0 < q := hq.pos
  let q_pnat : ℕ+ := ⟨q, hq_pos⟩
  have h := eigenform_coeff_multiplicative_one (N := N) k q_pnat q_pnat hqN hqN χ hgχ hg_eig
  simp only [q_pnat, PNat.mk_coe] at h
  rw [Nat.gcd_self, hq.divisors,
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hq.ne_one.symm),
    Finset.sum_singleton, dif_pos (Nat.coprime_one_left N), dif_pos hqN,
    show q * q / (1 * 1) = q ^ 2 by rw [mul_one, Nat.div_one, sq],
    show q * q / (q * q) = 1 from Nat.div_self (by positivity),
    show ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 by
      ext; simp [ZMod.coe_unitOfCoprime]] at h
  simp only [map_one, Units.val_one, one_mul, Nat.cast_one, one_zpow] at h
  rw [hg_eig.2, mul_one] at h
  rw [show (⇑g : UpperHalfPlane → ℂ) = ⇑g.toModularForm' from rfl]
  linear_combination -h

/-- **Cofactor agreement.**  If two normalised eigenforms (same `χ`) agree at a coprime index `m`
where the common value `a_m` is nonzero, and agree at `nm` for some `n` coprime to both `N` and `m`,
then they agree at `n`.  Mirrors `eigenvalue_agree_of_cofactor_ne_zero`. -/
private lemma normEigen_coeff_agree_cofactor
    {g g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgχ : g.toModularForm' ∈ modFormCharSpace k χ)
    (hg'χ : g'.toModularForm' ∈ modFormCharSpace k χ)
    (hg_eig : IsNormalisedEigenform_one k g.toModularForm')
    (hg'_eig : IsNormalisedEigenform_one k g'.toModularForm')
    (n m : ℕ+) (hn : Nat.Coprime n.val N) (hmN : Nat.Coprime m.val N)
    (hnm : Nat.Coprime n.val m.val)
    (hm_ne : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff m.val ≠ 0)
    (hm_eq : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff m.val =
      (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff m.val)
    (hnm_eq : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (n.val * m.val) =
      (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff (n.val * m.val)) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n.val =
      (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff n.val := by
  refine mul_right_cancel₀ hm_ne ?_
  rw [← normEigen_coeff_coprime_mul hgχ hg_eig n m hn hmN hnm, hnm_eq,
    normEigen_coeff_coprime_mul hg'χ hg'_eig n m hn hmN hnm, hm_eq]

/-- **Strong-multiplicity-one eigenvalue propagation.**  Two normalised eigenforms (same `χ`) whose
Fourier coefficients agree at every index coprime to `N` *outside a finite set* `S` in fact agree at
*every* index coprime to `N`.  Mirrors `eigenvalues_eq_all_coprime_of_eq_off_finite_eigenform`: the
cofactor trick (`normEigen_coeff_agree_cofactor`) plus the prime-square relation
(`normEigen_coeff_prime_sq`) propagate the agreement into the finite exceptional set, using a prime
`q` avoiding `S` from `exists_prime_coprime_avoiding_finset`. -/
private lemma normEigen_coeff_agree_all_coprime
    {g g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hgχ : g.toModularForm' ∈ modFormCharSpace k χ)
    (hg'χ : g'.toModularForm' ∈ modFormCharSpace k χ)
    (hg_eig : IsNormalisedEigenform_one k g.toModularForm')
    (hg'_eig : IsNormalisedEigenform_one k g'.toModularForm')
    (S : Finset ℕ)
    (hyp : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n.val =
        (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff n.val) :
    ∀ n : ℕ+, Nat.Coprime n.val N →
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n.val =
        (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff n.val := by
  intro n hn
  by_cases hn_S : n.val ∈ S
  · obtain ⟨q, hq_prime, hq_N, hn_coprime_q, hq_notin_S, hqsq_notin_S,
      hnq_notin_S, hnqsq_notin_S⟩ := exists_prime_coprime_avoiding_finset (N := N) n S
    have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hq_N
    by_cases hLamq : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff q = 0
    · -- `a_q(g) = 0 ⟹ a_{q²}(g) ≠ 0`; use the `q²` cofactor.
      have hf_qsq0 : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (q ^ 2) =
          -((χ (ZMod.unitOfCoprime q hq_N) : ℂ)) * (q : ℂ) ^ (k - 1) := by
        rw [normEigen_coeff_prime_sq hgχ hg_eig hq_prime hq_N, hLamq]; ring
      have hqsq_ne : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (q ^ 2) ≠ 0 := by
        rw [hf_qsq0]
        exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _))
          (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq_prime.pos.ne'))
      have hq_eq0 : (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff q = 0 :=
        (hyp ⟨q, hq_prime.pos⟩ hq_N hq_notin_S).symm.trans hLamq
      have hqsq_eq : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff (q ^ 2) =
          (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff (q ^ 2) := by
        rw [normEigen_coeff_prime_sq hgχ hg_eig hq_prime hq_N,
          normEigen_coeff_prime_sq hg'χ hg'_eig hq_prime hq_N, hLamq, hq_eq0]
      have hnqsq_eq := hyp ⟨n.val * q ^ 2, Nat.mul_pos n.pos (pow_pos hq_prime.pos 2)⟩
        (Nat.Coprime.mul_left hn hqsq_N) hnqsq_notin_S
      exact normEigen_coeff_agree_cofactor hgχ hg'χ hg_eig hg'_eig n ⟨q ^ 2, pow_pos hq_prime.pos 2⟩
        hn hqsq_N (Nat.Coprime.pow_right 2 hn_coprime_q) hqsq_ne hqsq_eq hnqsq_eq
    · -- `a_q(g) ≠ 0`; use the `q` cofactor directly.
      have hq_eq : (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff q =
          (UpperHalfPlane.qExpansion (1 : ℝ) g').coeff q := hyp ⟨q, hq_prime.pos⟩ hq_N hq_notin_S
      have hnq_eq := hyp ⟨n.val * q, Nat.mul_pos n.pos hq_prime.pos⟩
        (Nat.Coprime.mul_left hn hq_N) hnq_notin_S
      exact normEigen_coeff_agree_cofactor hgχ hg'χ hg_eig hg'_eig n ⟨q, hq_prime.pos⟩
        hn hq_N hn_coprime_q hLamq hq_eq hnq_eq
  · exact hyp n hn hn_S

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

/-- **L2 (separation of eigensystems — the strong-multiplicity-one crux).**

Two nonzero **common Hecke eigenfunctions** lying in (possibly different) Nebentypus spaces whose
eigenvalues agree at every index coprime to `N` must lie in the *same* character space.

This is the cross-character half of Strong Multiplicity One: the Nebentypus character of a cusp
form is recovered from its prime-to-level Hecke eigenvalues, because for a prime `q ∤ N` the
operator identity `T_{q²} = T_q² − q^{k-1}⟨q⟩` (`heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond`)
gives, on the `χ`-eigenspace, `a_{q²} = a_q² − q^{k-1}·χ(q)`, hence
`χ(q) = q^{1-k}(a_q² − a_{q²})`.  Equal eigensystems thus force `χ(q) = χ'(q)` at every prime
`q ∤ N`, and every unit of `(ZMod N)ˣ` is a product of prime-residue units, so `χ = χ'`. -/
private lemma eigensystem_determines_char
    {χ χ' : (ZMod N)ˣ →* ℂˣ}
    {h h' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hh_char : h ∈ cuspFormCharSpace k χ) (hh'_char : h' ∈ cuspFormCharSpace k χ')
    (hh_ne : h ≠ 0) (hh'_ne : h' ≠ 0)
    (hh_eigen : IsCommonEigenfunctionCusp k h) (hh'_eigen : IsCommonEigenfunctionCusp k h')
    (h_eig : ∀ m : ℕ, ∀ _ : NeZero m, Nat.Coprime m N → ∀ a a' : ℂ,
      heckeT_n_cusp k m h = a • h → heckeT_n_cusp k m h' = a' • h' → a = a') :
    χ = χ' := by
  classical
  -- **Core relation.**  For a nonzero `χ₁`-eigenfunction `h₁` and a prime `q ∤ N`, the eigenvalues
  -- `a_q, a_{q²}` (at `q` and `q²`) satisfy `a_{q²} = a_q² − χ₁(q)·q^{k-1}`.  This is the cusp-form
  -- transcription of `newform_eigenvalue_at_prime_sq`, applied to `h₁.toModularForm'`.
  have core : ∀ (χ₁ : (ZMod N)ˣ →* ℂˣ) (h₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      h₁ ∈ cuspFormCharSpace k χ₁ → h₁ ≠ 0 → IsCommonEigenfunctionCusp k h₁ →
      ∀ (q : ℕ) (hq : Nat.Prime q) (hqN : Nat.Coprime q N) (aq aqsq : ℂ),
        haveI : NeZero q := ⟨hq.pos.ne'⟩
        haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
        heckeT_n_cusp k q h₁ = aq • h₁ → heckeT_n_cusp k (q ^ 2) h₁ = aqsq • h₁ →
        aqsq = aq ^ 2 - (χ₁ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
    intro χ₁ h₁ hh₁_char hh₁_ne _hh₁_eigen q hq hqN aq aqsq h_aq h_aqsq
    haveI : NeZero q := ⟨hq.pos.ne'⟩
    haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
    set F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := h₁.toModularForm' with hF_def
    have hF_char : F ∈ modFormCharSpace k χ₁ :=
      HeckeRing.GL2.Unified.cuspFormCharSpace_toModularForm'_mem hh₁_char
    have hF_ne : F ≠ 0 := fun hF0 ↦ hh₁_ne (by
      ext z; exact congrFun (congrArg (⇑· : ModularForm _ k → _) hF0) z)
    -- Transport the two eigen-equations to `ModularForm`s.
    have h_eig_q : heckeT_n k q F = aq • F := by
      rw [hF_def, ← heckeT_n_cusp_toModularForm']; exact congrArg _ h_aq
    have h_eig_qsq : heckeT_n k (q ^ 2) F = aqsq • F := by
      rw [hF_def, ← heckeT_n_cusp_toModularForm']; exact congrArg _ h_aqsq
    have h_Tq_F : heckeT_p k q hq hqN F = aq • F :=
      heckeT_n_prime_coprime k hq hqN ▸ h_eig_q
    set chiq : ℂ := (χ₁ (ZMod.unitOfCoprime q hqN) : ℂ) with hchiq_def
    have h_combined :
        heckeT_n k (q ^ 2) F = (aq ^ 2 - chiq * (q : ℂ) ^ (k - 1)) • F := by
      have h_apply : heckeT_n k (q ^ 2) F =
          heckeT_p k q hq hqN (heckeT_p k q hq hqN F) -
            (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) F := by
        simpa [Module.End.mul_apply] using congr_arg (fun T : Module.End ℂ _ ↦ T F)
          (heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond hq hqN)
      rw [h_apply, h_Tq_F, map_smul, h_Tq_F, smul_smul, sq,
        show diamondOp k (ZMod.unitOfCoprime q hqN) F = chiq • F from
        (mem_modFormCharSpace_iff k χ₁ F).mp hF_char (ZMod.unitOfCoprime q hqN), smul_smul, sub_smul,
        mul_comm chiq]
    -- Cancel the nonzero `F`.
    refine sub_eq_zero.mp ((smul_eq_zero.mp ?_).resolve_right hF_ne)
    rw [sub_smul, ← h_combined, ← h_eig_qsq, sub_self]
  -- **Per-prime equality.**  At every prime `q ∤ N`, `χ(q) = χ'(q)` as elements of `ℂ`.
  have hprime : ∀ (q : ℕ) (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      (χ (ZMod.unitOfCoprime q hqN) : ℂ) = (χ' (ZMod.unitOfCoprime q hqN) : ℂ) := by
    intro q hq hqN
    haveI : NeZero q := ⟨hq.pos.ne'⟩
    haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
    have hqsqN : Nat.Coprime (q ^ 2) N := hqN.pow_left 2
    -- Eigenvalues of `h` and `h'` at `q` and `q²`.
    obtain ⟨aq, h_aq⟩ := hh_eigen ⟨q, hq.pos⟩ hqN
    obtain ⟨aqsq, h_aqsq⟩ := hh_eigen ⟨q ^ 2, pow_pos hq.pos 2⟩ hqsqN
    obtain ⟨a'q, h_a'q⟩ := hh'_eigen ⟨q, hq.pos⟩ hqN
    obtain ⟨a'qsq, h_a'qsq⟩ := hh'_eigen ⟨q ^ 2, pow_pos hq.pos 2⟩ hqsqN
    -- The eigensystems agree (hypothesis `h_eig`).
    have heq_q : aq = a'q := h_eig q ⟨hq.pos.ne'⟩ hqN aq a'q h_aq h_a'q
    have heq_qsq : aqsq = a'qsq :=
      h_eig (q ^ 2) ⟨(pow_pos hq.pos 2).ne'⟩ hqsqN aqsq a'qsq h_aqsq h_a'qsq
    -- Apply the core relation to `h` and `h'`.
    have hc := core χ h hh_char hh_ne hh_eigen q hq hqN aq aqsq h_aq h_aqsq
    have hc' := core χ' h' hh'_char hh'_ne hh'_eigen q hq hqN a'q a'qsq h_a'q h_a'qsq
    -- `χ(q)·q^{k-1} = χ'(q)·q^{k-1}`, then cancel `q^{k-1} ≠ 0`.
    have hpow_ne : (q : ℂ) ^ (k - 1) ≠ 0 :=
      zpow_ne_zero _ (by exact_mod_cast hq.pos.ne')
    have hkey : (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) =
        (χ' (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
      have hsub : aq ^ 2 - (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) =
          a'q ^ 2 - (χ' (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
        rw [← hc, ← hc', heq_qsq]
      rw [heq_q] at hsub
      linear_combination -hsub
    exact mul_right_cancel₀ hpow_ne hkey
  -- **Lift to all units.**  `χ` and `χ'` agree on `unitOfCoprime n` for every `n` coprime to `N`,
  -- by strong induction on the prime factorisation of `n` (`induction_on_primes`).
  have hunit : ∀ n : ℕ, ∀ hn : Nat.Coprime n N,
      (χ (ZMod.unitOfCoprime n hn) : ℂ) = (χ' (ZMod.unitOfCoprime n hn) : ℂ) := by
    refine induction_on_primes ?_ ?_ ?_
    · -- `n = 0`: coprimality forces `N = 1`, so `(ZMod N)ˣ` is trivial.
      intro hn
      have hN1 : N = 1 := by simpa [Nat.coprime_zero_left] using hn
      subst hN1
      simp [Subsingleton.elim (ZMod.unitOfCoprime 0 hn) 1]
    · -- `n = 1`: `unitOfCoprime 1 = 1`.
      intro hn
      rw [show ZMod.unitOfCoprime 1 hn = 1 from Units.ext (by simp), map_one, map_one]
    · -- `n = p * a`, `p` prime: split off the prime factor.
      intro p a hp ih hpa
      have hp_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left ⟨a, rfl⟩ hpa
      have ha_cop : Nat.Coprime a N := Nat.Coprime.coprime_dvd_left ⟨p, mul_comm p a⟩ hpa
      have hsplit : ZMod.unitOfCoprime (p * a) hpa =
          ZMod.unitOfCoprime p hp_cop * ZMod.unitOfCoprime a ha_cop :=
        Units.ext (by push_cast [ZMod.coe_unitOfCoprime]; ring)
      rw [hsplit, map_mul, map_mul, Units.val_mul, Units.val_mul, hprime p hp hp_cop, ih ha_cop]
  -- Conclude `χ = χ'` via `MonoidHom.ext`, writing each unit as `unitOfCoprime` of its value.
  refine MonoidHom.ext fun u ↦ Units.ext ?_
  have hu : u = ZMod.unitOfCoprime (u : ZMod N).val (ZMod.val_coe_unit_coprime u) :=
    Units.ext (by rw [ZMod.coe_unitOfCoprime, ZMod.natCast_val, ZMod.cast_id])
  have hcast : ((χ u : ℂˣ) : ℂ) = ((χ' u : ℂˣ) : ℂ) := by
    rw [hu]; exact hunit _ (ZMod.val_coe_unit_coprime u)
  exact_mod_cast hcast

/-- **L3 (linear independence of distinct Hecke eigensystems).**  *Isolated `sorry`.*

A finite family `H i` of **nonzero common Hecke eigenfunctions** (each `H i` is a `T_m`-eigenvector
for every index `m` coprime to `N`, with eigenvalue `ev i m`, recorded by `hev`) that are pairwise
distinct at *some* coprime index (`h_distinct`) is `ℂ`-linearly independent *as eigensystems*: any
scalars `c` for which the eigensystem combination `∑ᵢ cᵢ · evᵢ(m)` vanishes at every coprime `m`
(`h_rel`) must all vanish.

This is the classical linear independence of distinct Hecke eigenforms, in its eigenvalue-sequence
form.  Carrying the eigenfunction witnesses `H i` (rather than just the abstract multiplicative
functions `ev i`) is **essential**: distinct *multiplicative arithmetic functions* alone are NOT
`ℂ`-linearly independent (e.g. over one prime `p`, the multiplicative functions
`f₁(p),f₂(p),f₃(p) = 1,2,3`, `f₁(p²),f₂(p²),f₃(p²) = 5,7,9`, all `= 1` elsewhere, satisfy
`f₁ − 2f₂ + f₃ = 0`).  Real Hecke eigensystems additionally satisfy the prime-power recursion — they
are characters of the Hecke algebra — which is what the eigenfunction witnesses supply. -/
private lemma eigensystems_linearIndependent
    {ι : Type} [Fintype ι]
    (H : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hH_ne : ∀ i, H i ≠ 0)
    (ev : ι → ℕ+ → ℂ)
    (hev : ∀ i (m : ℕ+) (_ : NeZero m.val), Nat.Coprime m.val N →
       heckeT_n_cusp k m.val (H i) = ev i m • H i)
    (h_distinct : ∀ i j, i ≠ j → ∃ m : ℕ+, Nat.Coprime m.val N ∧ ev i m ≠ ev j m)
    (c : ι → ℂ)
    (h_rel : ∀ m : ℕ+, Nat.Coprime m.val N → ∑ i, c i * ev i m = 0) :
    ∀ i, c i = 0 :=
  -- HONEST `sorry`.  This is the genuine classical theorem (DS Thm 5.8.2 / Miyake Thm 4.6.12's
  -- linear-independence step), and a faithful proof needs major new infrastructure that does not yet
  -- exist in this repo or mathlib.  The obstruction was re-derived from scratch (DS §5.8, Miyake
  -- §4.6); below is exactly what is missing and why each available route stalls, so the next worker
  -- can build the right lemmas.
  --
  -- THE FUNCTION-vs-FORM DUALITY (the crux).  `h_rel` is a relation among the eigenvalue *functions*
  -- `m ↦ ev i m`: it constrains only the SCALAR `∑ᵢ cᵢ·evᵢ(m)` (equivalently the "all-ones"
  -- functional `φ(Tₘ S)` of `S := ∑ᵢ cᵢ·Hᵢ`, with `φ Hⱼ = 1`).  But the textbook proofs run on the
  -- *forms*: from a minimal relation `∑ᵢ cᵢ fᵢ = 0` they apply the operator `(Tₚ − aₚ(f₁))`, getting
  -- `∑_{i≠1} cᵢ(aₚ(f₁) − aₚ(fᵢ)) fᵢ = 0` with strictly fewer terms, hence (minimality) `aₚ(fᵢ) =
  -- aₚ(f₁)` for every `i` and prime `p`, so `fᵢ = f₁` — a contradiction.  This works because on FORMS
  -- `Tₚ fᵢ = aₚ(fᵢ)·fᵢ` holds with NO coprimality restriction.  L3 is the DUAL (function) statement
  -- and does not inherit that clean argument.  Multiplicativity alone is provably insufficient (see
  -- the docstring's `1,2,3 / 5,7,9` counterexample), so the Hecke prime-power recursion is essential.
  --
  -- THE COPRIMALITY GAP.  Mirroring the textbook reduction on the FUNCTIONS: pick `i₁,i₂` in
  -- `support c` separated by a coprime `m₀` (`evᵢ₁(m₀) ≠ evᵢ₂(m₀)`, from `h_distinct`) and set
  -- `c'ᵢ := cᵢ·(evᵢ(m₀) − evᵢ₁(m₀))`.  Then `∑ᵢ c'ᵢ·evᵢ(m) = ∑ᵢ cᵢ·evᵢ(m)·evᵢ(m₀) −
  -- evᵢ₁(m₀)·h_rel(m)`; the second term vanishes, but the first needs `∑ᵢ cᵢ·evᵢ(m)·evᵢ(m₀) = 0`.
  -- For `m` COPRIME to `m₀` this is `h_rel(m·m₀)` (multiplicativity, `heckeT_n_mul_coprime`); for `m`
  -- NOT coprime to `m₀` it is NOT, because `evᵢ(p)·evᵢ(pᵃ) = evᵢ(p^{a+1}) + p^{k-1}·χᵢ(p)·evᵢ(p^{a-1})`
  -- carries the diamond eigenvalue `χᵢ(p)`.  Carrying a growing "excluded-prime set" through the
  -- induction fails: two distinct eigensystems may differ ONLY at primes already excluded (exactly the
  -- counterexample's shape), so the separating `m₀` need not be coprime to the excluded set.
  --
  -- WHAT ACTUALLY CLOSES IT (per character) — the route to build.  If all `Hᵢ` lay in ONE character
  -- space `χ` (extra data L3 does NOT carry — `Hᵢ` is here only a `Tₘ`-eigenform, never assumed a
  -- diamond/`⟨d⟩`-eigenform), then `χᵢ(p) = χ(p)` is a single CONSTANT, and the gap term becomes
  -- `∑ᵢ cᵢ·evᵢ(p)·evᵢ(m) = h_rel(p^{a+1}m') + p^{k-1}·χ(p)·h_rel(p^{a-1}m') = 0` for EVERY coprime `m`
  -- (`m = pᵃ·m'`).  The gap closes and the minimal-relation/Dedekind induction goes through, giving
  -- per-character independence.  This needs (i) the general eigenvalue recursion
  -- `evᵢ(p^{a+2}) = evᵢ(p)·evᵢ(p^{a+1}) − p^{k-1}·χ(p)·evᵢ(pᵃ)` (a several-dozen-line generalisation of
  -- the `a = 0` computation already done in `eigensystem_determines_char`'s `core`, via
  -- `heckeT_ppow_succ_succ` + the diamond acting by `χ(p)` on the character space + cancelling the
  -- nonzero form), and (ii) a ~150-line minimal-support induction on `support c`.
  --
  -- WHY THE CROSS-CHARACTER CASE STILL NEEDS HEAVY MACHINERY.  L3's family spans several characters
  -- (at the call site `charPiece_coeff_sum_eq_zero`, the witnesses `H (wit s)` lie in DIFFERENT
  -- `cuspFormCharSpace k (tag s)`).  Separating characters textbook-style uses the DIAMOND
  -- `(⟨d⟩ − χ₁(d))` (DS Exercise 5.8.5(a)) — but `h_rel` is a `Tₘ`-only functional with no `⟨d⟩` in
  -- the index `m`, so the diamond cannot be applied to it; and the gap-closure above breaks once the
  -- `χᵢ(p)` differ across `i`.  A faithful proof therefore must FIRST reconstruct that each `Tₘ`-eigen
  -- witness is a diamond eigenform / decompose the family into character spaces (cf.
  -- `exists_eigenform_decomposition_of_invariant` + L2 `eigensystem_determines_char`, both available),
  -- THEN run the per-character argument, THEN assemble.  Equivalently, strengthen L3's signature with
  -- `(tag : ι → (ZMod N)ˣ →* ℂˣ)` and `Hᵢ ∈ cuspFormCharSpace k (tag i)` (data the call site HAS but
  -- currently discards) and re-thread the caller.  Either way this is ~300–500 LOC of new
  -- infrastructure (eigenvalue recursion + character reconstruction + minimal-support induction +
  -- cross-character assembly), well beyond a bounded fix.
  --
  -- DEAD ENDS confirmed: `linearIndependent_monoidHom` does NOT apply — `evᵢ` is only COPRIME-
  -- multiplicative, not completely multiplicative, so it is not a monoid hom out of `(ℕ₍N₎, ×)` nor
  -- out of the free monoid on primes ∤ N (the free-monoid hom would need `evᵢ(p²) = evᵢ(p)²`, which
  -- is precisely false and is the counterexample).  The q-expansion/normalisation route
  -- (`S := ∑ cᵢ Hᵢ` normalised, `aₙ(S) = ∑ cᵢ evᵢ(n) = 0`, so `S` is old by the Main Lemma, hence `0`)
  -- is CIRCULAR — it invokes `mainLemma`, which L3 is being used to prove — and is forbidden.  The
  -- orthogonality of the `Hᵢ` (`eigenforms_orthogonal_of_ne_eigenvalues`) only re-proves that the
  -- FORMS are independent (`dim span{Hᵢ} = |ι|`), which does NOT imply the eigenvalue FUNCTIONS are
  -- independent (`rank[evᵢ(m)]ₘᵢ = |ι|`): those ranks differ exactly by the counterexample, so the
  -- scalar `h_rel` cannot be discharged from form-independence alone.
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
  -- A zero piece has vanishing first coefficient `A1` (contrapositive of `hH_ne_char`).
  have hA1_zero_of_H_zero : ∀ k0 : K, H k0 = 0 → A1 k0 = 0 := fun k0 h0 ↦ by
    by_contra hA1; exact (hH_ne_char k0 hA1).2 h0
  -- **L3**: each occurring eigensystem value contributes `0` to the global sum, i.e. `C s = 0`.
  have hC_zero : ∀ s : ℕ+ → ℂ, C s = 0 := by
    -- Eigensystem values not in the image contribute nothing.
    have hC_img : ∀ s, s ∉ img → C s = 0 := by
      intro s hs
      apply Finset.sum_eq_zero
      intro k0 hk0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
      exact absurd (hk0 ▸ hmem_img k0) hs
    -- Eigensystem values realised *only* by zero pieces also contribute nothing (each summand has
    -- `A1 = 0`).  These are precisely the `s` for which the new L3 has no nonzero witness, so they
    -- are filtered out of the L3 index set and handled here directly.
    have hC_allzero : ∀ s, (∀ k0 : K, EV k0 = s → H k0 = 0) → C s = 0 := by
      intro s hs
      apply Finset.sum_eq_zero
      intro k0 hk0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
      exact hA1_zero_of_H_zero k0 (hs k0 hk0)
    -- The L3 index: occurring eigensystem values that are realised by at least one *nonzero* piece.
    set J : Finset (ℕ+ → ℂ) := img.filter (fun s ↦ ∃ k0 : K, EV k0 = s ∧ H k0 ≠ 0) with hJ_def
    -- For each `s ∈ J`, choose a nonzero witness `k0` with `EV k0 = s`.
    have hJ_wit : ∀ s ∈ J, ∃ k0 : K, EV k0 = s ∧ H k0 ≠ 0 := fun s hs ↦
      (Finset.mem_filter.mp hs).2
    choose wit hwit_ev hwit_ne using hJ_wit
    -- Linear independence of the distinct occurring eigensystems (**L3**), indexed by `↥J`.
    have key : ∀ s : ↥J, C s.val = 0 :=
      eigensystems_linearIndependent (N := N)
        (ι := ↥J) (fun s ↦ H (wit s.val s.2)) (fun s ↦ hwit_ne s.val s.2)
        (fun s ↦ s.val) (fun s m _ hm ↦ by
          -- eigenvalue equation for the chosen nonzero witness, with `EV (wit s) = s`
          haveI : NeZero m.val := ⟨m.pos.ne'⟩
          rw [hEV_spec (wit s.val s.2) m hm, hwit_ev s.val s.2])
        (by -- distinctness: distinct occurring values differ at a coprime index
          rintro ⟨s, hs⟩ ⟨s', hs'⟩ hne
          by_contra hcon
          push_neg at hcon
          refine hne (Subtype.ext ?_)
          obtain ⟨k0, _, hk0⟩ := Finset.mem_image.mp (Finset.mem_of_mem_filter _ hs)
          obtain ⟨k0', _, hk0'⟩ := Finset.mem_image.mp (Finset.mem_of_mem_filter _ hs')
          have hEVeq : EV k0 = EV k0' :=
            eigensystem_funext_of_coprime_agree (N := N) EV hEV_zero (fun m hm ↦
              (congrFun hk0 m).trans ((hcon m hm).trans (congrFun hk0' m).symm))
          exact hk0.symm.trans (hEVeq.trans hk0'))
        (fun s ↦ C s.val)
        (by -- relation: `∑_{s ∈ J} C s · s(m) = 0` for coprime `m`
          intro m hm
          -- The global fiberwise relation `∑_{s ∈ img} C s · s(m) = 0`.
          have hfb := Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset K) img EV
            (fun k0 ↦ EV k0 m * A1 k0)
          rw [Finset.filter_true_of_mem (fun k0 _ ↦ hmem_img k0)] at hfb
          have hglob : ∑ s ∈ img, C s * s m = 0 := by
            rw [← hrel m hm, ← hfb]
            refine Finset.sum_congr rfl fun s _ ↦ ?_
            rw [hC_def, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k0 hk0 ↦ ?_
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk0
            rw [hk0]; ring
          -- Restrict to `J`: the dropped values `img \ J` are realised only by zero pieces.
          rw [Finset.sum_coe_sort J (fun s ↦ C s * s m)]
          have hJ_sub : J ⊆ img := hJ_def ▸ Finset.filter_subset _ _
          -- a dropped value `s ∈ img \ J` is realised only by zero pieces, so `C s · s m = 0`.
          have hdrop : ∀ s ∈ img, s ∉ J → C s * s m = 0 := by
            intro s hs hsJ
            have hz : ∀ k0 : K, EV k0 = s → H k0 = 0 := by
              intro k0 hk0
              by_contra h0
              exact hsJ (Finset.mem_filter.mpr ⟨hs, ⟨k0, hk0, h0⟩⟩)
            rw [hC_allzero s hz, zero_mul]
          rw [Finset.sum_subset hJ_sub hdrop, hglob])
    -- Assemble `C s = 0` for every `s`, splitting on `s ∈ J` / realised-only-by-zero / `s ∉ img`.
    intro s
    by_cases hs : s ∈ img
    · by_cases hsJ : s ∈ J
      · exact key ⟨s, hsJ⟩
      · -- `s ∈ img \ J`: realised only by zero pieces.
        apply hC_allzero s
        intro k0 hk0
        by_contra h0
        exact hsJ (Finset.mem_filter.mpr ⟨hs, ⟨k0, hk0, h0⟩⟩)
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
        -- `H k0` and `H k0₀` are common Hecke eigenfunctions (eigenvalues `EV · ⟨n, _⟩`).
        have hEV_eigen : ∀ j : K, IsCommonEigenfunctionCusp k (H j) := fun j n hn ↦
          ⟨EV j n, hEV_spec j n hn⟩
        have htag : tag k0 = χ₀ := by
          have hchar_eq := eigensystem_determines_char (N := N)
            hk0_char hk0₀_char hk0_form_ne hk0₀_form_ne (hEV_eigen k0) (hEV_eigen k0₀)
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
  -- The eigensystem of `H k0`: the eigenvalue at coprime indices (`0` off them).  When `H k0 = 0`
  -- every scalar is an "eigenvalue", so we pin the value to the *trivial multiplicative character*
  -- `1` on coprime indices; this keeps `EV k0` multiplicative even for the degenerate zero pieces.
  let EV : K → ℕ+ → ℂ := fun k0 m ↦
    if hm : Nat.Coprime m.val N then (if H k0 = 0 then 1 else Classical.choose (hH_eig k0 m hm))
    else 0
  have hEV_spec : ∀ (k0 : K) (m : ℕ+) (hm : Nat.Coprime m.val N),
      haveI : NeZero m.val := ⟨m.pos.ne'⟩
      heckeT_n_cusp k m.val (H k0) = EV k0 m • H k0 := by
    intro k0 m hm
    haveI : NeZero m.val := ⟨m.pos.ne'⟩
    show heckeT_n_cusp k m.val (H k0) =
      (if hm : Nat.Coprime m.val N then (if H k0 = 0 then 1 else _) else 0) • H k0
    rw [dif_pos hm]
    by_cases h0 : H k0 = 0
    · rw [if_pos h0, h0, smul_zero]
      exact CuspForm.ext fun τ ↦ by
        change ((heckeT_n k ↑m) (toModularForm' 0)) τ = 0
        rw [show toModularForm' (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 by rfl, map_zero]
        rfl
    · rw [if_neg h0]; exact Classical.choose_spec (hH_eig k0 m hm)
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
