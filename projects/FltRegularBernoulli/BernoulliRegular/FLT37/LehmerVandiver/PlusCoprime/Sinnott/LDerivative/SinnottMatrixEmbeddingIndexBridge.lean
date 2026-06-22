import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.FrobeniusDetFormulaCharacterMatrix

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Convolution matrix at log-norm**: alias for the convolution matrix
with the cyclotomic-unit log-norm function `f(a) = log‖1 - stdAddChar(↑a)‖`. -/
noncomputable def convolutionMatrixLogNorm :
    Matrix ((ZMod p)ˣ) ((ZMod p)ˣ) ℂ :=
  convolutionMatrix p (fun a ↦
    ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ))

/-- **Transfer lemma**: the quotient convolution matrix on `CyclotomicEvenDelta p`
agrees with the full convolution matrix `convolutionMatrixLogNorm p` on
corresponding entries (via the quotient map). Concretely,
`convolutionMatrixLogNormEven p (q a) (q b) = convolutionMatrixLogNorm p a b`
for any `a b : (ZMod p)ˣ`.

The right-hand side is the full-matrix value; the left-hand side is the
quotient-matrix value at the projected indices. This shows the quotient
matrix is the natural pull-back of the full matrix through the
`{±1}`-projection of the index. -/
theorem convolutionMatrixLogNormEven_apply_quotient_eq_full
    (a b : BernoulliRegular.CyclotomicUnitDelta p) :
    convolutionMatrixLogNormEven p
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p a)
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p b) =
      convolutionMatrixLogNorm p a b := by
  rw [convolutionMatrixLogNormEven_apply_quotient]
  unfold convolutionMatrixLogNorm convolutionMatrix
  rw [Matrix.of_apply]

/-- **Squared Frobenius determinant in DirichletLogSum form**: combining the
unconditional squared Frobenius determinant formula with the eigenvalue
identification gives:

  det(convolutionMatrixLogNorm p)² =
    (∏_{χ : DirichletCharacter ℂ p} DirichletLogSum p χ)²

(after reindexing via the Pontryagin equivalence).

The full product is over ALL Dirichlet characters mod p (size p-1).
Sinnott's identity uses a restricted product over even nontrivial characters
(size (p-3)/2), so this is the "full" Frobenius formula that needs further
restriction to match `FrobeniusDetIdentity`. -/
theorem det_convolutionMatrixLogNorm_sq_eq_prod_DirichletLogSum_sq
    (hp_two : 2 ≤ p) :
    (convolutionMatrixLogNorm p).det ^ 2 =
      (∏ χ : DirichletCharacter ℂ p, DirichletLogSum p χ) ^ 2 := by
  classical
  rw [convolutionMatrixLogNorm]
  rw [det_convolutionMatrix_sq_eq_prod_lambda_sq_unconditional (p := p) _ hp_two]
  -- Goal: (∏ k, ∑ a, (e.symm k)(↑a) · ((log ‖1 - stdAddChar(↑a)‖ : ℝ) : ℂ))² =
  --       (∏ χ, DirichletLogSum p χ)²
  -- Apply eigenvalue identification: ∑ a, χ(↑a) · log = -DirichletLogSum p χ.
  have h_eigen : ∀ k : (ZMod p)ˣ,
      ∑ a : (ZMod p)ˣ, ((dirichletCharEquivUnits p).symm k) ((a : ZMod p)) *
          ((Real.log ‖(1 : ℂ) -
            ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
        -DirichletLogSum p ((dirichletCharEquivUnits p).symm k) := fun k ↦
    frobenius_eigenvalue_eq_neg_DirichletLogSum p
      ((dirichletCharEquivUnits p).symm k)
  rw [Finset.prod_congr rfl (fun k _ ↦ h_eigen k)]
  -- Goal: (∏ k, -DirichletLogSum p (e.symm k))² = (∏ χ, DirichletLogSum p χ)²
  -- Reindex k ↔ χ via e.symm.
  have h_reindex : ∏ k : (ZMod p)ˣ,
        -DirichletLogSum p ((dirichletCharEquivUnits p).symm k) =
      ∏ χ : DirichletCharacter ℂ p, -DirichletLogSum p χ := by
    apply Fintype.prod_equiv (dirichletCharEquivUnits p).symm.toEquiv
      (fun k : (ZMod p)ˣ ↦ -DirichletLogSum p ((dirichletCharEquivUnits p).symm k))
      (fun χ : DirichletCharacter ℂ p ↦ -DirichletLogSum p χ)
    intro k
    rfl
  rw [h_reindex]
  -- (∏ χ, -X χ)² = (∏ χ, X χ)² (sign squares away).
  have h_sign : ∀ χ : DirichletCharacter ℂ p,
      -DirichletLogSum p χ = (-1) * DirichletLogSum p χ := fun _ ↦ by ring
  rw [Finset.prod_congr rfl (fun χ _ ↦ h_sign χ)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow]
  have h_sign_sq : ((-1 : ℂ) ^ Finset.card
      (Finset.univ : Finset (DirichletCharacter ℂ p))) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    rw [show ((-1 : ℂ) ^ 2) = 1 from by norm_num, one_pow]
  rw [h_sign_sq, one_mul]

/-- **Partition of nontrivial Dirichlet characters**: every non-trivial
Dirichlet character mod `p` (with `p ≠ 2`) is either even or odd
(by `DirichletCharacter.even_or_odd`), and the two are disjoint
(by `DirichletCharacter.not_even_and_odd`). -/
theorem nontrivialCharacters_eq_evenNontriv_disjUnion_odd :
    haveI : DecidableEq (DirichletCharacter ℂ p) := Classical.decEq _
    BernoulliRegular.nontrivialCharacters p =
      BernoulliRegular.evenNontrivialCharacters p ∪
      BernoulliRegular.oddCharacters p := by
  letI : DecidableEq (DirichletCharacter ℂ p) := Classical.decEq _
  ext χ
  simp only [BernoulliRegular.nontrivialCharacters,
    BernoulliRegular.evenNontrivialCharacters, BernoulliRegular.oddCharacters,
    Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
    true_and, and_true]
  constructor
  · intro hχ_ne
    haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
    rcases χ.even_or_odd with h_even | h_odd
    · left; exact ⟨h_even, hχ_ne⟩
    · right; exact h_odd
  · haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
    rintro (⟨_, hne⟩ | hodd)
    · exact hne
    · intro hχ_eq_one
      rw [hχ_eq_one] at hodd
      have h_one_even : (1 : DirichletCharacter ℂ p).Even := by
        change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
        rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
      exact (DirichletCharacter.Even.not_odd _ h_one_even) hodd

omit hp in
/-- **Trivial-character split** for products over all Dirichlet characters:
`∏ χ, f χ = f 1 · ∏ χ ∈ nontrivialCharacters p, f χ`. -/
theorem prod_dirichletCharacter_eq_trivial_mul_nontrivial (f : DirichletCharacter ℂ p → ℂ) :
    ∏ χ : DirichletCharacter ℂ p, f χ =
      f 1 * ∏ χ ∈ BernoulliRegular.nontrivialCharacters p, f χ := by
  classical
  rw [show BernoulliRegular.nontrivialCharacters p =
      (Finset.univ : Finset (DirichletCharacter ℂ p)).erase 1 from rfl]
  rw [← Finset.prod_erase_mul _ f (Finset.mem_univ (1 : DirichletCharacter ℂ p))]
  ring

omit hp in
/-- **Disjointness of evenNontrivial and odd characters**. -/
theorem disjoint_evenNontriv_oddCharacters : Disjoint (BernoulliRegular.evenNontrivialCharacters p)
      (BernoulliRegular.oddCharacters p) := by
  classical
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb h_eq
  simp only [BernoulliRegular.evenNontrivialCharacters,
    BernoulliRegular.oddCharacters, Finset.mem_filter, Finset.mem_univ,
    true_and] at ha hb
  subst h_eq
  haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  exact (DirichletCharacter.Even.not_odd _ ha.1) hb

/-- **Full character product split** for products over all Dirichlet characters:

  ∏ χ, f χ = f 1 · (∏ χ ∈ evenNontriv, f χ) · (∏ χ ∈ odd, f χ)

Composes `prod_dirichletCharacter_eq_trivial_mul_nontrivial` with the
partition `nontrivialCharacters = evenNontriv ⊔ odd`. -/
theorem prod_dirichletCharacter_split
    (f : DirichletCharacter ℂ p → ℂ) :
    ∏ χ : DirichletCharacter ℂ p, f χ =
      f 1 *
      ((∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, f χ) *
        ∏ χ ∈ BernoulliRegular.oddCharacters p, f χ) := by
  classical
  rw [prod_dirichletCharacter_eq_trivial_mul_nontrivial]
  congr 1
  rw [nontrivialCharacters_eq_evenNontriv_disjUnion_odd]
  exact Finset.prod_union (disjoint_evenNontriv_oddCharacters (p := p))

/-- **Frobenius det squared, split form**: combining the unconditional
squared Frobenius det formula
`det(convolutionMatrixLogNorm p)² = (∏_χ DLS p χ)²` with the character
product split + `DirichletLogSum_principal_eq_neg_log` gives:

  det(convolutionMatrixLogNorm p)² =
    (log p)² · ((∏_{χ ∈ evenNontriv} DLS p χ) · (∏_{χ ∈ odd} DLS p χ))²

This isolates the trivial-character contribution `(log p)²` and the
odd-character contribution `(∏_{odd} DLS)²` from the squared abstract det.
The Sinnott-side analytic identity has `(∏_{evenNontriv} DLS p χ⁻¹)² /
2^(p-3)` — so the **residual factor** that the matrix-restriction step
must contribute is `(log p)² · (∏_{odd} DLS)² · 2^(p-3)` (or its inverse). -/
theorem det_convolutionMatrixLogNorm_sq_split
    (hp_two : 2 ≤ p) :
    (convolutionMatrixLogNorm p).det ^ 2 =
      (((Real.log p : ℝ) : ℂ)) ^ 2 *
      ((∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, DirichletLogSum p χ) *
        ∏ χ ∈ BernoulliRegular.oddCharacters p, DirichletLogSum p χ) ^ 2 := by
  rw [det_convolutionMatrixLogNorm_sq_eq_prod_DirichletLogSum_sq (p := p) hp_two]
  rw [prod_dirichletCharacter_split (p := p) (DirichletLogSum p)]
  rw [DirichletLogSum_principal_eq_neg_log (p := p)]
  rw [mul_pow]
  rw [show ((-((Real.log p : ℝ) : ℂ)) ^ 2 : ℂ) =
      (((Real.log p : ℝ) : ℂ)) ^ 2 from by ring]

/-- **Convolution log-norm matrix is structurally singular**: when there
exists at least one odd Dirichlet character mod `p` (e.g. for `p` prime
with `p ≠ 2`), `det(convolutionMatrixLogNorm p) = 0`. Direct consequence
of `DirichletLogSum_eq_zero_of_odd` plugged into the full Frobenius
determinant formula `det(conv)² = (∏_χ DLS p χ)²`: the product factor at
any odd character is `0`, so the full product is `0`, so `det² = 0`,
hence `det = 0`.

This documents the dead-end of using the **full** convolution matrix
for the matrix-restriction step in PF-1: the full matrix is identically
singular (rank deficiency from the `{±1}`-symmetry of the underlying
function `f(c) = log|1 - stdAddChar(c)|`). The substantive PF-1
matrix-restriction must use the **even-character quotient** matrix on
`(ZMod p)ˣ / {±1}` (size `(p-1)/2`), where odd characters are quotiented
out and the eigenvalues are exactly the non-vanishing even-character
log-sums. -/
theorem convolutionMatrixLogNorm_det_eq_zero
    (hp_odd : p ≠ 2) (hp_two : 2 ≤ p)
    (hodd_nonempty : (BernoulliRegular.oddCharacters p).Nonempty) :
    (convolutionMatrixLogNorm p).det = 0 := by
  -- det² = 0 ⟹ det = 0.
  have h_sq : (convolutionMatrixLogNorm p).det ^ 2 = 0 := by
    rw [det_convolutionMatrixLogNorm_sq_split (p := p) hp_two]
    rw [prod_oddCharacters_DirichletLogSum_eq_zero (p := p) hp_odd hodd_nonempty]
    ring
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h_sq

omit hp in
/-- **Generalised χ ↔ χ⁻¹ reindex** for products over `evenNontrivialCharacters`:
since the set is closed under inversion, the involution χ ↔ χ⁻¹ reindexes
the product without changing its value. -/
theorem prod_evenNontriv_eq_prod_evenNontriv_inv
    (f : DirichletCharacter ℂ p → ℂ) :
    ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, f χ =
      ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, f χ⁻¹ := by
  classical
  refine (Finset.prod_bij (fun χ _ ↦ χ⁻¹) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact inv_mem_evenNontrivialCharacters (p := p) hχ
  · intro χ₁ _ χ₂ _ heq
    have := congrArg (fun ψ ↦ ψ⁻¹) heq
    simpa using this
  · intro χ hχ
    refine ⟨χ⁻¹, inv_mem_evenNontrivialCharacters (p := p) hχ, ?_⟩
    exact inv_inv χ
  · intro χ _; rfl

/-- **Sinnott analytic identity in `(∏ DLS p χ)²` form** (without inversion).
The shipped `hPlus_mul_regulator_sq_eq` uses `χ⁻¹`; by the χ ↔ χ⁻¹
reindex, this equals the same product without inversion:

  (↑hPlus K · ↑regulator K⁺)² =
    (∏ χ ∈ evenNontriv, DLS p χ)² / 2^(p-3)

This is the analytic-side closed form in the same shape as the
Frobenius-side closed form (where products are in `DLS p χ`, not
`DLS p χ⁻¹`). -/
theorem hPlus_mul_regulator_sq_eq_no_inv
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) (hp_ge : 3 ≤ p) :
    (((BernoulliRegular.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ)) ^ 2 =
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ) ^ 2 / (2 : ℂ) ^ (p - 3) := by
  rw [hPlus_mul_regulator_sq_eq (p := p) K hp_odd' hp_ge]
  rw [prod_evenNontriv_eq_prod_evenNontriv_inv (p := p) (DirichletLogSum p)]

/-- **Matrix-restriction step to the Sinnott matrix (named Prop)**: the
substantive remaining content for PF-1, expressing that the squared
determinant of the quotient convolution log-norm matrix times `2^(p-3)`
equals the squared trivial-eigenvalue times the squared regulator of the
cyclotomic-unit family:

  2^(p-3) · (det convolutionMatrixLogNormEven p)² =
    (quotientEigenvalue p 1)² · (regOfFamily ... : ℂ)²

This isolates the matrix-restriction step from the abstract Frobenius
det chain: after extracting the trivial-character row/column, the
remaining `(p-3)/2 × (p-3)/2` block is the Sinnott log-embedding matrix,
whose determinant absolute value is `2^((p-3)/2) · |det(A−B)|`. The
factor `2^(p-3) = 4^((p-3)/2)` comes from `M_Sinnott = 2 · (A − B)`,
so `regOfFamily² = 4^((p-3)/2) · det(A−B)² = 2^(p-3) · det(A−B)²`.

The matrix-restriction is the substantive Sinnott regulator content;
the abstract Frobenius det infrastructure (shipped) reduces PF-1 to
this single named identity. -/
def MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (2 : ℂ) ^ (p - 3) * ((convolutionMatrixLogNormEven p).det) ^ 2 =
    (quotientEigenvalue p (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)) ^ 2 *
      ((NumberField.Units.regOfFamily
          (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2

/-- **Even-character bijection step (named Prop)**: the
`dirichletOfQuotientChar` map restricts to a bijection between the
nontrivial multiplicative characters of `CyclotomicEvenDelta p` and the
even nontrivial Dirichlet characters mod `p`, identifying the products:

  ∏ ξ ∈ univ.erase 1, DLS p (dirichletOfQuotientChar p ξ) =
    ∏ χ ∈ evenNontrivialCharacters p, DLS p χ.

This is the Pontryagin-duality identification between the dual of
`(ZMod p)ˣ / ⟨-1⟩` and the even-character subgroup of the dual of
`(ZMod p)ˣ`. -/
def QuotientCharBijectionToEvenNontriv : Prop :=
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (∏ ξ ∈ (Finset.univ : Finset
      (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
    DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
  ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, DirichletLogSum p χ

/-- **Proof of `QuotientCharBijectionToEvenNontriv` via cardinality-and-injection**:
for `p` prime with `p > 2` (so `p ≠ 2`), the product equality holds.

Strategy:
1. The map `ξ ↦ dirichletOfQuotientChar p ξ` is injective (shipped).
2. The image of `MulChar.erase 1` under this map lies in `evenNontrivialCharacters`
   (image is even by `dirichletOfQuotientChar_even`; ≠ 1 since `ξ ≠ 1` and
   the map is injective with `dirichletOfQuotientChar_one`).
3. Cardinalities match: both `MulChar.erase 1` and `evenNontrivialCharacters`
   have card `(p-3)/2` (via shipped `nat_card_mulChar_cyclotomicEvenDelta_eq` +
   `cyclotomicEvenDelta_card`, and `card_evenNontrivialCharacters`).
4. Hence the map is a bijection. -/
theorem quotientCharBijectionToEvenNontriv_proof (hp_two : 2 < p) :
    QuotientCharBijectionToEvenNontriv (p := p) := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  change (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
      DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
    ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters p, DirichletLogSum p χ
  have h_card_mc : Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  refine Finset.prod_bij (fun ξ _ ↦ dirichletOfQuotientChar p ξ) ?_ ?_ ?_ ?_
  · intro ξ hξ
    rw [Finset.mem_erase] at hξ
    obtain ⟨hξ_ne, _⟩ := hξ
    rw [BernoulliRegular.evenNontrivialCharacters, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact dirichletOfQuotientChar_even p ξ
    · intro h_one
      apply hξ_ne
      have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
        rw [dirichletOfQuotientChar_one]
        exact h_one
      exact dirichletOfQuotientChar_injective p h_eq
  · intro ξ₁ _ ξ₂ _ h
    exact dirichletOfQuotientChar_injective p h
  · intro χ hχ
    have h_card_eq : (BernoulliRegular.evenNontrivialCharacters p).card =
        ((Finset.univ : Finset
            (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1).card := by
      rw [BernoulliRegular.card_evenNontrivialCharacters (p := p) (by omega)]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      rw [Finset.card_univ, h_card_mc]
      rcases h_p_odd with ⟨k, hk⟩
      omega
    have h_in : ∀ ξ : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ,
        ξ ∈ (Finset.univ : Finset
              (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1 →
        dirichletOfQuotientChar p ξ ∈ BernoulliRegular.evenNontrivialCharacters p := by
      intro ξ hξ
      rw [Finset.mem_erase] at hξ
      obtain ⟨hξ_ne, _⟩ := hξ
      rw [BernoulliRegular.evenNontrivialCharacters, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact dirichletOfQuotientChar_even p ξ
      · intro h_one
        apply hξ_ne
        have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
          rw [dirichletOfQuotientChar_one]
          exact h_one
        exact dirichletOfQuotientChar_injective p h_eq
    have h_surj := Finset.surj_on_of_inj_on_of_card_le
      (fun ξ (_ : ξ ∈ _) ↦ dirichletOfQuotientChar p ξ)
      (fun ξ hξ ↦ h_in ξ hξ)
      (fun ξ₁ ξ₂ _ _ h ↦ dirichletOfQuotientChar_injective p h)
      h_card_eq.le χ hχ
    obtain ⟨a, ha_mem, ha_eq⟩ := h_surj
    exact ⟨a, ha_mem, ha_eq.symm⟩
  · intro ξ _
    rfl

/-- **`FrobeniusDetIdentity` from the two named hypotheses**: combining
`MatrixRestrictionToSinnott` (substantive matrix-restriction) and
`QuotientCharBijectionToEvenNontriv` (Pontryagin duality bijection)
with the shipped abstract Frobenius det chain on the quotient,
`FrobeniusDetIdentity` follows. -/
theorem FrobeniusDetIdentity_of_named_hypotheses
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three)
    (h_bij : QuotientCharBijectionToEvenNontriv (p := p)) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  unfold FrobeniusDetIdentity
  -- Step 1: get det² in log p · (∏ nontriv DLS)² form.
  have h_det_sq := det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
      p hp_two
  -- Step 2: from MatrixRestrictionToSinnott + h_det_sq.
  unfold MatrixRestrictionToSinnott at h_matrix
  -- h_matrix : 2^(p-3) · det²(M_even) = qe(1)² · regOfFamily²
  unfold QuotientCharBijectionToEvenNontriv at h_bij
  -- Step 3: use quotientEigenvalue_trivial = (log p) / 2.
  have h_qe := quotientEigenvalue_trivial_eq_half_log_p p hp_two
  rw [h_qe] at h_matrix
  -- Step 4: cardinality
  have h_card : Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two
  -- Step 5: apply the bijection on the goal side.
  rw [← prod_evenNontriv_eq_prod_evenNontriv_inv (p := p) (DirichletLogSum p)]
  -- Step 6: log p ≠ 0
  have h_log_ne : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    have h_pos : (1 : ℝ) < (p : ℝ) := by
      have : (1 : ℝ) < (2 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (by exact_mod_cast hp_two.le)
    exact_mod_cast (Real.log_pos h_pos).ne'
  -- Step 7: combine h_det_sq + h_matrix + h_bij to derive
  -- regOfFamily² = (∏ DLS(χ⁻¹))².
  -- h_det_sq : det²(M_even) = (log p)² · (∏ DLS(dχ ξ))² / 4^card
  -- h_matrix : 2^(p-3) · det²(M_even) = ((log p)/2)² · regOfFamily²
  -- h_bij : ∏_{ξ≠1} DLS(dχ ξ) = ∏_{χ even nontriv} DLS(χ)
  rw [h_bij] at h_det_sq
  -- Substitute h_det_sq into h_matrix:
  -- 2^(p-3) · ((log p)² · (∏ DLS χ)² / 4^card) = ((log p)/2)² · regOfFamily²
  -- (log p)² · 2^(p-3) · (∏ DLS χ)² / 4^card = (log p)² / 4 · regOfFamily²
  -- Cancel (log p)²: 2^(p-3) · (∏ DLS χ)² / 4^card = regOfFamily² / 4
  -- 4^card = 2^(p-1), so 2^(p-3) / 2^(p-1) = 1/4
  -- (1/4) · (∏ DLS χ)² = regOfFamily² / 4
  -- (∏ DLS χ)² = regOfFamily²
  rw [h_det_sq] at h_matrix
  -- h_matrix : 2^(p-3) · ((log p)² · (∏ DLS χ)² / 4^card) = ((log p)/2)² · regOfFamily²
  have h_two_pow_card : (4 : ℂ) ^ Fintype.card
      (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) =
      (2 : ℂ) ^ (p - 1) := by
    rw [h_card]
    rw [show (4 : ℂ) = 2 ^ 2 from by norm_num, ← pow_mul]
    congr 1
    have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    omega
  rw [h_two_pow_card] at h_matrix
  -- h_matrix : 2^(p-3) · ((log p)² · (∏ DLS χ)² / 2^(p-1)) = ((log p)/2)² · regOfFamily²
  have h_log_sq_ne : (((Real.log p : ℝ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ h_log_ne
  have h_two_ne : ((2 : ℂ) ^ (p - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_two_ne' : ((2 : ℂ) ^ (p - 3)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_p_ge : (2 : ℂ) ^ (p - 1) = 4 * (2 : ℂ) ^ (p - 3) := by
    rw [show p - 1 = (p - 3) + 2 from by omega, pow_add]
    ring
  rw [h_p_ge] at h_matrix
  -- h_matrix : 2^(p-3) · ((log p)² · (∏)² / (4 · 2^(p-3))) = ((log p)/2)² · regOfFamily²
  -- LHS = (log p)² · (∏)² / 4. RHS = (log p)² / 4 · regOfFamily².
  -- Cancel (log p)²/4 from both sides: (∏)² = regOfFamily².
  field_simp at h_matrix
  -- h_matrix : (∏ DLS χ)² · 4 = 4 · regOfFamily²
  -- Goal: regOfFamily² = (∏ DLS χ)²
  linear_combination -h_matrix / 4

/-- **`FrobeniusDetIdentity` from `MatrixRestrictionToSinnott` alone**: with
the proven `QuotientCharBijectionToEvenNontriv` discharged, PF-1 reduces to
the SINGLE named hypothesis `MatrixRestrictionToSinnott`. -/
theorem FrobeniusDetIdentity_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three :=
  FrobeniusDetIdentity_of_named_hypotheses (p := p) K hp_odd hp_three hp_two
    h_matrix
    (quotientCharBijectionToEvenNontriv_proof (p := p) hp_two)

/-- **`KummerDirichletDeterminant` from `MatrixRestrictionToSinnott` alone**:
final compositional theorem reducing PF-1 (KummerDirichletDeterminant) to the
single substantive hypothesis `MatrixRestrictionToSinnott`. -/
theorem KummerDirichletDeterminant_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    BernoulliRegular.FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
  KummerDirichletDeterminant_of_FrobeniusDetIdentity (p := p) K hp_odd hp_three
    (FrobeniusDetIdentity_of_MatrixRestrictionToSinnott (p := p) K hp_odd
      hp_three hp_two h_matrix)


/-- **Cardinality of `InfinitePlace K`**: for K = ℚ(ζ_p) (cyclotomic field of
prime conductor p > 2), the number of infinite places equals `(p-1)/2`.
K is totally complex (CM-field, no real places), so by
`IsTotallyComplex.finrank` we have `finrank ℚ K = 2 · nrComplexPlaces K`.
Combined with `IsCyclotomicExtension.finrank` giving `finrank ℚ K = p - 1`
(totient of prime p), this yields `nrComplexPlaces = (p-1)/2`. -/
theorem fintype_card_InfinitePlace_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (_hp_two : 2 < p) :
    Fintype.card (NumberField.InfinitePlace K) = (p - 1) / 2 := by
  classical
  haveI : Fact (Nat.Prime p) := hp
  have h_finrank_eq : Module.finrank ℚ K = p - 1 := by
    have : Module.finrank ℚ K = (p : ℕ).totient :=
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.out.pos)
    rw [this, Nat.totient_prime hp.out]
  have h_totally_complex := NumberField.IsTotallyComplex.finrank K
  rw [h_finrank_eq] at h_totally_complex
  -- h_totally_complex : p - 1 = 2 * nrComplexPlaces K
  -- Since K is totally complex, card InfinitePlace = nrComplexPlaces (no real places).
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K), zero_add]
  omega

/-- **K-place ↔ CyclotomicEvenDelta bijection**: for K = ℚ(ζ_p) cyclotomic
totally complex, there is a non-canonical bijection between infinite places
of K and elements of `CyclotomicEvenDelta p`, both of cardinality `(p-1)/2`.
This is the Pontryagin-cardinality-based existence statement; the canonical
bijection comes from the Galois orbit-stabilizer correspondence (orbits of
the (ZMod p)ˣ-action with stabilizer ⟨-1⟩). -/
noncomputable def InfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (hp_two : 2 < p) :
    NumberField.InfinitePlace K ≃ BernoulliRegular.CyclotomicEvenDelta p := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [fintype_card_InfinitePlace_eq (p := p) K hp_two]
  rw [BernoulliRegular.cyclotomicEvenDelta_card (p := p) hp_two]

/-- **K⁺-place ↔ CyclotomicEvenDelta bijection**: composing the mathlib
`NumberField.IsCMField.equivInfinitePlace` (K-places ↔ K⁺-places) with
the K-place bijection gives the K⁺-place bijection. This is the actual
bijection used to index the Sinnott log-embedding matrix in
`CyclotomicEvenDelta` form. -/
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
  (NumberField.IsCMField.equivInfinitePlace K).symm.trans
    (InfinitePlaceEquivCyclotomicEvenDelta (p := p) K hp_two)

/-- **Galois action transitivity on infinite places**: for any Galois
number-field extension `K/ℚ`, the Galois group acts transitively on
infinite places of K (single orbit). Direct from
`NumberField.InfinitePlace.mem_orbit_iff` + uniqueness of ℚ's infinite
place. -/
theorem galois_isPretransitive_infinitePlace
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    MulAction.IsPretransitive Gal(K / ℚ) (NumberField.InfinitePlace K) := by
  constructor
  intro w w'
  have h_orbit : w' ∈ MulAction.orbit Gal(K/ℚ) w :=
    (NumberField.InfinitePlace.mem_orbit_iff (k := ℚ) (K := K)).mpr
      (by apply Subsingleton.elim)
  rcases h_orbit with ⟨σ, hσ⟩
  exact ⟨σ, hσ⟩

/-- **Canonical bijection InfinitePlace K ≃ Gal(K/ℚ) ⧸ stabilizer w₀** via
Galois orbit-stabilizer correspondence. For pretransitive actions
(Galois actions on infinite places of Galois K/ℚ are pretransitive,
shipped above), the orbit of any base place is the entire space, and
`MulAction.orbitEquivQuotientStabilizer` gives the bijection. -/
noncomputable def InfinitePlaceEquivGalQuotStabilizer
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K]
    (w₀ : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace K ≃
      Gal(K / ℚ) ⧸ MulAction.stabilizer Gal(K/ℚ) w₀ := by
  haveI : MulAction.IsPretransitive Gal(K/ℚ) (NumberField.InfinitePlace K) :=
    galois_isPretransitive_infinitePlace K
  have h_orbit_eq : (MulAction.orbit Gal(K/ℚ) w₀ : Set _) = Set.univ := by
    ext w
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨σ, hσ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := Gal(K/ℚ)) w₀ w
    exact ⟨σ, hσ⟩
  refine ((Equiv.Set.univ _).symm.trans ?_)
  rw [← h_orbit_eq]
  exact (MulAction.orbitEquivQuotientStabilizer Gal(K/ℚ) w₀)

/-- **Image of the Galois stabilizer under `cyclotomicGalEquivZMod` is the
even subgroup**: pushing forward `MulAction.stabilizer Gal(K/ℚ) w₀` via
the cyclotomic Galois iso `Gal(K/ℚ) ≃* (ZMod p)ˣ` yields exactly
`CyclotomicEvenDeltaSubgroup p = ⟨-1⟩`. The proof rewrites the map along
the iso into a comap along its inverse, which by definition is
`cyclotomicInfinitePlaceStabilizer K w₀`; then applies
`cyclotomicInfinitePlaceStabilizer_eq_evenSubgroup`. -/
theorem stabilizer_map_eq_evenSubgroup
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) (w₀ : NumberField.InfinitePlace K) :
    (MulAction.stabilizer Gal(K/ℚ) w₀).map
        (BernoulliRegular.cyclotomicGalEquivZMod (p := p) K).toMonoidHom
      = BernoulliRegular.CyclotomicEvenDeltaSubgroup p := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact BernoulliRegular.cyclotomicInfinitePlaceStabilizer_eq_evenSubgroup
    (p := p) (K := K) hp_gt_two w₀

/-- **Canonical Galois-equivariant bijection `InfinitePlace K ≃ CyclotomicEvenDelta p`**.

For `K = ℚ(ζ_p)` cyclotomic (`IsCyclotomicExtension {p} ℚ K`, automatically Galois
over `ℚ` with abelian Galois group `Gal(K/ℚ) ≃* (ZMod p)ˣ`), and any choice of base
infinite place `w₀`, the orbit-stabilizer bijection
`InfinitePlace K ≃ Gal(K/ℚ) ⧸ stab(w₀)` composes with the cyclotomic Galois
isomorphism (which sends `stab(w₀)` to `CyclotomicEvenDeltaSubgroup p = ⟨-1⟩` by
`cyclotomicInfinitePlaceStabilizer_eq_evenSubgroup`) to produce a canonical
bijection with `CyclotomicEvenDelta p = (ZMod p)ˣ / ⟨-1⟩`.

This is the canonical (Galois-equivariant) refinement of the non-canonical
cardinality-based `InfinitePlaceEquivCyclotomicEvenDelta`, and is the bijection
required to identify the `convolutionMatrixLogNormEven` matrix entries with the
Sinnott log-embedding matrix entries indexed by elements of `(ZMod p)ˣ`. -/
noncomputable def InfinitePlaceEquivCyclotomicEvenDelta_canonical
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hp_gt_two : 2 < p) (w₀ : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace K ≃ BernoulliRegular.CyclotomicEvenDelta p := by
  haveI : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {p} ℚ K
  refine (InfinitePlaceEquivGalQuotStabilizer K w₀).trans ?_
  exact (QuotientGroup.congr
      (MulAction.stabilizer Gal(K/ℚ) w₀)
      (BernoulliRegular.CyclotomicEvenDeltaSubgroup p)
      (BernoulliRegular.cyclotomicGalEquivZMod (p := p) K)
      (stabilizer_map_eq_evenSubgroup (p := p) K hp_gt_two w₀)).toEquiv

/-- **Sinnott matrix-entry decomposition wrapper**: gives the matrix `M_Sinnott[i, w]`
in the form `2 (log w_K(ζ^(idx_i+2) - 1) - log w_K(ζ - 1))`.

The K⁺-side cyclotomic-unit log-embedding matrix from
`regOfFamily_cyclotomicUnitFamilyKplus_eq_det` has entries decomposed by
`log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp` (per-entry). This is
the matrix-level wrapper: every entry follows the per-entry decomposition.
The second term `2 log w_K(ζ - 1)` is **column-constant** — independent of
the row index `i` — which is the key structural fact for the matrix
restriction step: row operations cancel the column-constant part.

This is a structural step toward `MatrixRestrictionToSinnott`. -/
theorem sinnottMatrix_entry_decomp
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((FLT37.realCyclotomicUnit p K
            ((((NumberField.Units.equivFinRank
                (NumberField.maximalRealSubfield K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))) + 2) : 𝓞 K) : K)) =
      2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger :
                  𝓞 K) : K) ^
                (((((NumberField.Units.equivFinRank
                    (NumberField.maximalRealSubfield K)).symm i).cast
                  ((NumberField.IsCMField.units_rank_eq_units_rank
                      (K := K)).trans
                    (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                      (p := p) (K := K)))) + 2 : ℕ)) - 1)) -
        2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              (((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger :
                  𝓞 K) : K)) - 1)) := by
  set k_idx : ℕ := ((((NumberField.Units.equivFinRank
              (NumberField.maximalRealSubfield K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ) with hk_idx
  have h_idx_coprime : k_idx.Coprime p := by
    have h_p_prime : Nat.Prime p := hp.out
    rw [Nat.coprime_comm, h_p_prime.coprime_iff_not_dvd]
    intro h_dvd
    have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    have h_fin_lt :
        (((NumberField.Units.equivFinRank
            (NumberField.maximalRealSubfield K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))).val < (p - 3) / 2 :=
      Fin.isLt _
    have h_lt_p : k_idx < p := by
      change ((((NumberField.Units.equivFinRank
                (NumberField.maximalRealSubfield K)).symm i).cast _) + 2 : ℕ) < p
      omega
    have h_pos : 0 < k_idx := by
      change 0 < ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast _) + 2 : ℕ)
      omega
    have := Nat.le_of_dvd h_pos h_dvd
    omega
  have h_p_ge_two : 2 ≤ p := by omega
  exact log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp (p := p) (K := K)
    k_idx h_idx_coprime h_p_ge_two w.val

/-- **Sinnott `A`-matrix**: the `i,w`-dependent part of the Sinnott
log-embedding matrix. `A[i, w] = log w_K((ζ_K^(idx_i+2)) - 1)`. -/
noncomputable def sinnottMatrixA
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun i w ↦
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger :
            𝓞 K) : K) ^
          (((((NumberField.Units.equivFinRank
              (NumberField.maximalRealSubfield K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ)) - 1))

/-- **Sinnott `B`-matrix**: the column-constant part of the Sinnott
log-embedding matrix. `B[i, w] = log w_K(ζ_K - 1)` — depends only on the
column `w`, not on the row `i`. This is the **rank-1 fact**: the rows
of `B` are all identical.

(Strictly, the rank may be 0 if the row vector is identically zero, but
its zero-ness is not used in the determinant analysis.) -/
noncomputable def sinnottMatrixB
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun (_ : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) w =>
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        (((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger :
            𝓞 K) : K)) - 1))

/-- **Sinnott matrix as `2·A - 2·B`**: the matrix-level decomposition
of the Sinnott log-embedding matrix
`regOfFamily_cyclotomicUnitFamilyKplus_eq_det`.

  `M_Sinnott = 2 · sinnottMatrixA - 2 · sinnottMatrixB`

where `sinnottMatrixA` is the `(i, w)`-dependent part and
`sinnottMatrixB` is the column-constant part. This is the matrix-form
lift of `sinnottMatrix_entry_decomp`. -/
theorem sinnottMatrix_eq_two_A_sub_two_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((FLT37.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • sinnottMatrixA p K - (2 : ℝ) • sinnottMatrixB p K := by
  ext i w
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sinnottMatrixA, sinnottMatrixB]
  exact sinnottMatrix_entry_decomp p K hp_odd hp_three i w

/-- **Rows of `sinnottMatrixB` are all equal** (rank-≤-1 fact): for any
two row indices `i₁ i₂`, `sinnottMatrixB p K i₁ = sinnottMatrixB p K i₂`
(as functions of the column index). This is the rank-1 structural fact
the matrix-restriction step exploits via row operations. -/
theorem sinnottMatrixB_row_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (i₁ i₂ : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (sinnottMatrixB p K) i₁ = (sinnottMatrixB p K) i₂ := by
  funext w
  simp [sinnottMatrixB]

/-- **Sinnott matrix as `2 · (A - B)`**: factored form. The Sinnott
log-embedding matrix equals `2 · (sinnottMatrixA - sinnottMatrixB)`,
which lets us pull the factor of `2` out for determinant evaluation. -/
theorem sinnottMatrix_eq_two_smul_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((FLT37.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (NumberField.maximalRealSubfield K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • (sinnottMatrixA p K - sinnottMatrixB p K) := by
  rw [sinnottMatrix_eq_two_A_sub_two_B p K hp_odd hp_three]
  rw [smul_sub]

/-- **`convolutionLogNormDescended` at the `q(a)` quotient class**: the descended
log-norm function evaluated at the quotient class of a unit `a` equals the
explicit ℝ-cast `log‖1 - stdAddChar(↑a)‖`. Direct from
`evenFunctionDescend_apply_mk` for the cyclotomic-unit log-norm. -/
theorem convolutionLogNormDescended_apply_quotient
    (a : BernoulliRegular.CyclotomicUnitDelta p) :
    convolutionLogNormDescended p
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p a) =
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  unfold convolutionLogNormDescended
  rw [show BernoulliRegular.cyclotomicEvenDeltaQuotient p a = QuotientGroup.mk a from rfl]
  rw [BernoulliRegular.evenFunctionDescend_apply_mk]

/-- **Squared det = qe(1)² · (∏ ξ≠1 qe(ξ))² (reformulation)**:
extracting the trivial-character eigenvalue factor from
`det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq`.

This is the trivial-extracted form: `det²(M_even) = qe(1)² · (∏_{ξ≠1} qe(ξ))²`.
It exhibits the substantive matrix-restriction content as
`regOfFamily² = (∏_{ξ ≠ 1} qe(ξ))²` — the eigenvalue identification that
completes `MatrixRestrictionToSinnott`. -/
theorem det_convolutionMatrixLogNormEven_sq_eq_qe_one_sq_mul_prod_nontrivial_qe_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      quotientEigenvalue p (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
          quotientEigenvalue p ξ) ^ 2 := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq p hp_two]
  rw [← Finset.prod_pow]
  rw [prod_quot_eq_prod_mulChar p (fun ξ ↦ (quotientEigenvalue p ξ) ^ 2)]
  rw [Finset.prod_pow]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ
    (1 : MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ))]
  ring

end Sinnott

end FLT37

end BernoulliRegular

end
