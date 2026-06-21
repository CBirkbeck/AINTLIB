import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part4

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

def RegOfFamilySqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  ((NumberField.Units.regOfFamily
    (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
  (2 : ℂ) ^ (p - 3) *
    (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ) ^ 2

/-- **Substantive matrix-level content** (named Prop): the rank-1
perturbation of the shifted-convolution submatrix has determinant
equal (up to sign) to the product of nontrivial eigenvalues:

  `(det(sinnottMatrixA p K − sinnottMatrixB p K) : ℂ)² =
      (∏_{ξ ≠ 1} quotientEigenvalue p ξ)²`.

This is the **substantive content** of Sinnott's identity at the
algebraic-side determinant level. The proof is via the rank-1
perturbation lemma applied to `(A − B) = U − col_one · row_v` (with
`U = sinnottShiftedConvolutionMatrix` and `v = sinnottRankOnePerturbationVec`),
plus the Frobenius determinant formula on the full convolution matrix.

The `2^(p-3)` factor in `RegOfFamilySqEqTwoPowProdNontrivialQeSq` is
recovered from this identity by the shipped `det_sinnottMatrix_eq_pow_two_mul_det`
(which says `det(M_Sinnott) = 2^N · det(A − B)`).

**Sanity check (p = 5):** `det(A − B) = s − t = −log φ`, and
`∏ qe = qe(χ) = s − t = −log φ`. -/
def DetASubBSqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    [Fintype {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  haveI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (((((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ)) ^ 2 : ℂ) =
    (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ) ^ 2

/-- **`MatrixRestrictionToSinnott` reduces to
`regOfFamily² = 2^(p-3) · (∏_{ξ≠1} qe(ξ))²`**: under the corrected
squared-eigenvalue-product identity (which folds in the K⁺-side log-norm
doubling), the matrix-restriction step reduces to the
algebraic-side identity. -/
theorem matrixRestrictionToSinnott_of_regOfFamily_sq_eq_prod_nontrivial_qe_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three) :
    MatrixRestrictionToSinnott (p := p) K hp_odd hp_three := by
  classical
  letI : Fintype (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  letI : DecidableEq (MulChar (BernoulliRegular.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  unfold MatrixRestrictionToSinnott
  unfold RegOfFamilySqEqProdNontrivialQeSq at h
  rw [det_convolutionMatrixLogNormEven_sq_eq_qe_one_sq_mul_prod_nontrivial_qe_sq p hp_two]
  -- Goal: 2^(p-3) · qe(1)² · (∏ qe)² = qe(1)² · regOfFamily²
  -- From h: regOfFamily² = 2^(p-3) · (∏ qe)², so substitute on RHS.
  rw [h]
  ring


/-- **`KummerDirichletDeterminant` from the eigenvalue-product hypothesis**:
final synthesis chain. Assuming the substantive eigenvalue-product identity
`RegOfFamilySqEqProdNontrivialQeSq`, the entire PF-1 chain
`MatrixRestrictionToSinnott → FrobeniusDetIdentity → KummerDirichletDeterminant`
discharges to `KummerDirichletDeterminant` (= `regOfFamily = hPlus · regulator(K⁺)`). -/
theorem KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three) :
    BernoulliRegular.FLT37.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
  KummerDirichletDeterminant_of_MatrixRestrictionToSinnott (p := p) K hp_odd
    hp_three hp_two
    (matrixRestrictionToSinnott_of_regOfFamily_sq_eq_prod_nontrivial_qe_sq
      (p := p) K hp_odd hp_three hp_two h)

/-- **Existence of an embedding-index for a K-place** (cyclotomic K).

For any infinite place `w` of `K = ℚ(ζ_p)`, the underlying ring hom
`w.embedding : K →+* ℂ` sends `ζ_K` to a primitive `p`-th root of unity
in ℂ, which by `Complex.isPrimitiveRoot_iff` equals `stdAddChar(a)`
(`= exp(2πi · a/p)`) for some unique `a` with `a < p` and `a.Coprime p`.
As an element of `(ZMod p)ˣ` (via `ZMod.unitOfCoprime`), this is the
**embedding-index** of `w`.

This is the existential form; the canonical bijection to
`CyclotomicEvenDelta p` factors through quotienting by `⟨-1⟩`. -/
theorem exists_embedding_index
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) :
    ∃ a : (ZMod p)ˣ,
      w.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        ZMod.stdAddChar (N := p) ((a : ZMod p)) := by
  classical
  haveI hp_prime : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  -- `cyclotomicZetaInteger` is a primitive p-th root in 𝓞 K.
  have h_zeta_OK : IsPrimitiveRoot
      (BernoulliRegular.cyclotomicZetaInteger (p := p) K) p :=
    BernoulliRegular.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
  -- Push to K via the algebraMap (𝓞 K → K), which is injective.
  have h_zeta_K : IsPrimitiveRoot
      ((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) p := by
    have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K
    exact h_zeta_OK.map_of_injective h_inj
  -- Push to ℂ via w.embedding, which is injective (it's a ring hom on a field).
  have h_emb_inj : Function.Injective (w.embedding) :=
    (w.embedding).injective
  have h_zeta_C : IsPrimitiveRoot
      (w.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K))) p :=
    h_zeta_K.map_of_injective h_emb_inj
  -- Extract the explicit form via Complex.isPrimitiveRoot_iff.
  obtain ⟨a, ha_lt, ha_cop, ha_eq⟩ :=
    (Complex.isPrimitiveRoot_iff
      (w.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)))
      p hp_prime.ne_zero).mp h_zeta_C
  -- Convert to (ZMod p)ˣ via ZMod.unitOfCoprime, then express stdAddChar via stdAddChar_coe.
  refine ⟨ZMod.unitOfCoprime a ha_cop, ?_⟩
  rw [← ha_eq]
  -- Goal: exp(2πI · (a/p)) = stdAddChar (↑(unitOfCoprime a ha_cop) : ZMod p)
  rw [ZMod.coe_unitOfCoprime]
  -- Now: exp(2πI · (a/p)) = stdAddChar (a : ZMod p).
  rw [show ((a : ℕ) : ZMod p) = ((a : ℤ) : ZMod p) from by push_cast; rfl]
  rw [ZMod.stdAddChar_coe (a : ℤ)]
  push_cast
  ring_nf

/-- **Embedding-index function** of a K-place (cyclotomic K).

Concrete extraction (via `Classical.choose` on `exists_embedding_index`)
of the unique `a : (ZMod p)ˣ` such that `w.embedding ζ_K = stdAddChar(a)`. -/
noncomputable def embeddingIndex
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) : (ZMod p)ˣ :=
  Classical.choose (exists_embedding_index (p := p) K w)

/-- **Specification of `embeddingIndex`**:
`w.embedding (ζ_K) = stdAddChar (embeddingIndex K w)`. -/
theorem embeddingIndex_spec
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) :
    w.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
      ZMod.stdAddChar (N := p) ((embeddingIndex (p := p) K w : ZMod p)) :=
  Classical.choose_spec (exists_embedding_index (p := p) K w)

/-- **K-place log evaluation in terms of `stdAddChar`**: for any infinite
place `w` of cyclotomic K and any `k : ℕ`, choosing the embedding-index
`a` via `exists_embedding_index`,

  `Real.log (w (ζ_K^k - 1)) = Real.log ‖1 - stdAddChar(k · ↑a)‖`

i.e., the K-place log evaluation translates to the standard log-norm form
indexed by the embedding-index. This is the per-entry identification that
bridges Sinnott matrix entries to convolution matrix entries. -/
theorem exists_log_w_zeta_pow_sub_one_eq_log_stdAddChar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) (k : ℕ) :
    ∃ a : (ZMod p)ˣ,
      Real.log (w (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) ^ k - 1)) =
        Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p) * k)‖ := by
  obtain ⟨a, ha_eq⟩ := exists_embedding_index (p := p) K w
  refine ⟨a, ?_⟩
  -- Step 1: rewrite w(...) = ‖w.embedding(...)‖ using `apply_eq_norm`.
  rw [← NumberField.InfinitePlace.norm_embedding_eq w]
  -- Step 2: w.embedding is a ring hom, so commutes with ^ and -.
  rw [map_sub, map_pow, map_one]
  -- Step 3: substitute w.embedding(ζ_K) = stdAddChar(a) via ha_eq.
  rw [ha_eq]
  -- Step 4: rearrange ‖stdAddChar(a)^k - 1‖ = ‖1 - stdAddChar(a*k)‖.
  have h_pow : (ZMod.stdAddChar (N := p) ((a : ZMod p))) ^ k =
      ZMod.stdAddChar (N := p) (((a : ZMod p)) * k) := by
    -- stdAddChar(k • a) = stdAddChar(a)^k via AddChar.map_nsmul_eq_pow
    have h_smul : ((a : ZMod p)) * k = k • ((a : ZMod p)) := by
      rw [nsmul_eq_mul, mul_comm]
    rw [h_smul, AddChar.map_nsmul_eq_pow]
  rw [h_pow]
  rw [show ‖ZMod.stdAddChar (N := p) (((a : ZMod p)) * k) - 1‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (((a : ZMod p)) * k)‖ from by
    rw [← neg_sub, norm_neg]]

/-- **Sinnott `A`-matrix entry in `stdAddChar` form**: under the embedding-index
identification, the per-entry expression of `sinnottMatrixA p K [i, w]` becomes
`log ‖1 - stdAddChar(a_w · (idx_i+2))‖` where `a_w = embeddingIndex K (eqIP.symm w.val)`.

This is the explicit convolution-style form for the `A`-matrix entries. -/
theorem sinnottMatrixA_apply_eq_log_stdAddChar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_odd : p ≠ 2) (_hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    let k_idx : ℕ := ((((NumberField.Units.equivFinRank
              (NumberField.maximalRealSubfield K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ)
    (sinnottMatrixA p K) i w =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K
            ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) : ZMod p) *
          (k_idx : ZMod p))‖ := by
  intro k_idx
  unfold sinnottMatrixA
  rw [Matrix.of_apply]
  -- The K-place corresponding to w.
  set w_K : NumberField.InfinitePlace K :=
    (NumberField.IsCMField.equivInfinitePlace K).symm w.val
  -- Identify zeta_spec.toInteger with cyclotomicZetaInteger at the K-element level.
  have h_zeta_eq : ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)) : K) =
      ((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) := rfl
  rw [h_zeta_eq]
  -- Apply norm_embedding_eq + ring-hom commutativity.
  rw [← NumberField.InfinitePlace.norm_embedding_eq w_K]
  rw [map_sub, map_pow, map_one]
  rw [embeddingIndex_spec (p := p) K w_K]
  have h_pow : (ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p))) ^ k_idx =
      ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p)) := by
    have h_smul : ((embeddingIndex (p := p) K w_K : ZMod p)) * (k_idx : ZMod p) =
        k_idx • ((embeddingIndex (p := p) K w_K : ZMod p)) := by
      rw [nsmul_eq_mul, mul_comm]
    rw [h_smul, AddChar.map_nsmul_eq_pow]
  rw [h_pow]
  rw [show ‖ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p)) - 1‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p))‖ from by
    rw [← neg_sub, norm_neg]]

/-- **Sinnott `B`-matrix entry in `stdAddChar` form**: the column-constant
log-evaluation entry of `sinnottMatrixB` expressed as
`log ‖1 - stdAddChar(embeddingIndex K w_K)‖`. -/
theorem sinnottMatrixB_apply_eq_log_stdAddChar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (sinnottMatrixB p K) i w =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K
            ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) : ZMod p))‖ := by
  unfold sinnottMatrixB
  rw [Matrix.of_apply]
  set w_K : NumberField.InfinitePlace K :=
    (NumberField.IsCMField.equivInfinitePlace K).symm w.val
  -- Identify zeta_spec.toInteger with cyclotomicZetaInteger at the K-element level.
  have h_zeta_eq : ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)) : K) =
      ((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) := rfl
  rw [h_zeta_eq]
  rw [← NumberField.InfinitePlace.norm_embedding_eq w_K]
  rw [map_sub, map_one]
  rw [embeddingIndex_spec (p := p) K w_K]
  rw [show ‖ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p)) - 1‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p))‖ from by
    rw [← neg_sub, norm_neg]]

/-- **K⁺-place embedding-index-quotient**: for `v : InfinitePlace K⁺`, the
embedding-index of the corresponding K-place `(equivInfinitePlace K).symm v`,
viewed mod `⟨-1⟩` in `CyclotomicEvenDelta p`.

Two complex embeddings of K above `v` (a real K⁺-place) differ by complex
conjugation, so their embedding-indices differ by sign. The quotient
`(ZMod p)ˣ → CyclotomicEvenDelta p` (mod `⟨-1⟩`) makes the map well-defined
on K⁺-places. -/
noncomputable def kplusEmbeddingIndexQuotient
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (v : NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :
    BernoulliRegular.CyclotomicEvenDelta p :=
  BernoulliRegular.cyclotomicEvenDeltaQuotient p
    (embeddingIndex (p := p) K
      ((NumberField.IsCMField.equivInfinitePlace K).symm v))

/-- **Family-index as a `ZMod p`-unit**: for any cyclotomic-unit family index
`i : Fin ((p-3)/2)`, the natural number `idx_i + 2` (the actual cyclotomic-unit
exponent) gives a non-zero element of `ZMod p`, hence a unit.

Using `ZMod.unitOfCoprime` after proving coprimality. -/
noncomputable def familyIndexAsUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) : (ZMod p)ˣ := by
  classical
  set j : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K))))
  refine ZMod.unitOfCoprime (j + 2 : ℕ) ?_
  have h_p_prime : Nat.Prime p := hp.out
  have h_fin_lt : j.val < (p - 3) / 2 := Fin.isLt _
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  rw [Nat.coprime_comm, h_p_prime.coprime_iff_not_dvd]
  intro h_dvd
  have h_lt_p : ((j : ℕ) + 2 : ℕ) < p := by
    omega
  have h_pos : 0 < ((j : ℕ) + 2 : ℕ) := by
    omega
  have := Nat.le_of_dvd h_pos h_dvd
  omega

/-- **`familyIndexAsUnit` value in `ZMod p`**: the underlying `ZMod p` element
of `familyIndexAsUnit p K hp_odd hp_three i` is `(idx_i + 2 : ZMod p)`. -/
theorem familyIndexAsUnit_val
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    let k_idx : ℕ := ((((NumberField.Units.equivFinRank
            (NumberField.maximalRealSubfield K)).symm i).cast
          ((NumberField.IsCMField.units_rank_eq_units_rank
              (K := K)).trans
            (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
              (p := p) (K := K)))) + 2 : ℕ)
    ((familyIndexAsUnit p K hp_odd hp_three i) : ZMod p) = (k_idx : ZMod p) := by
  intro k_idx
  unfold familyIndexAsUnit
  rw [ZMod.coe_unitOfCoprime]

/-- **Matrix-level identification of `sinnottMatrixA`** with a convolution-matrix
value: under the embedding-index and `familyIndexAsUnit` parameterisations,

  `sinnottMatrixA p K [i, w]
    = convolutionLogNormDescended p (q(embeddingIndex K w_K · familyIndexAsUnit i))`

where `q : (ZMod p)ˣ → CyclotomicEvenDelta p` is the quotient, and the
multiplication is in `(ZMod p)ˣ`. This is the per-entry bridge from the
Sinnott log-evaluation to the convolution descent. -/
theorem sinnottMatrixA_apply_eq_convolutionLogNormDescended
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixA p K) i w : ℂ) =
      convolutionLogNormDescended p
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p
          (embeddingIndex (p := p) K
              ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) *
            familyIndexAsUnit p K hp_odd hp_three i)) := by
  rw [convolutionLogNormDescended_apply_quotient]
  rw [sinnottMatrixA_apply_eq_log_stdAddChar p K hp_odd hp_three i w]
  push_cast
  congr 2
  rw [familyIndexAsUnit_val p K hp_odd hp_three i]
  push_cast
  ring

/-- **Sinnott A-matrix entry as a `convolutionMatrixLogNormEven` value**:
under the canonical bijections, each entry of `sinnottMatrixA` is a single
value of the quotient convolution matrix:

  `(sinnottMatrixA p K [i, w] : ℂ)
    = convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient w.val)
        (q(familyIndexAsUnit i))`.

This realises the matrix-level identification of the Sinnott A-matrix with
a "shifted" (canonically-bijected) submatrix of `convolutionMatrixLogNormEven p`.
The key fact: the multiplication `(embIdx K w_K · familyIndexAsUnit i)` in
`(ZMod p)ˣ` descends to `kplusEmbeddingIndexQuotient w.val · q(familyIndexAsUnit i)`
in `CyclotomicEvenDelta p` (via the group-hom property of the quotient map). -/
theorem sinnottMatrixA_apply_eq_convolutionMatrixLogNormEven
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixA p K) i w : ℂ) =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val)
        (BernoulliRegular.cyclotomicEvenDeltaQuotient p
          (familyIndexAsUnit p K hp_odd hp_three i)) := by
  rw [sinnottMatrixA_apply_eq_convolutionLogNormDescended p K hp_odd hp_three i w]
  unfold convolutionMatrixLogNormEven kplusEmbeddingIndexQuotient
  rw [Matrix.of_apply]
  -- q(a * b) = q(a) * q(b), where q is the quotient (a group hom).
  rw [(BernoulliRegular.cyclotomicEvenDeltaQuotient p).map_mul]

/-- **Sinnott B-matrix entry as a `convolutionMatrixLogNormEven` value at index `1`**:

  `(sinnottMatrixB p K [i, w] : ℂ)
    = convolutionMatrixLogNormEven p (kplusEmbeddingIndexQuotient w.val) 1`.

The B-matrix entry corresponds to the value of `M_even` at column 1 (the
"trivial" quotient element). -/
theorem sinnottMatrixB_apply_eq_convolutionMatrixLogNormEven
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixB p K) i w : ℂ) =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 := by
  rw [sinnottMatrixB_apply_eq_log_stdAddChar p K i w]
  unfold convolutionMatrixLogNormEven kplusEmbeddingIndexQuotient
  rw [Matrix.of_apply, mul_one, convolutionLogNormDescended_apply_quotient]

/-- **Sinnott (A - B)-matrix entries as differences of convolution-matrix
entries**: the per-entry identification
`(A - B)[i, w] = M_even[k(v), q(famIdx i)] - M_even[k(v), 1]`
where `k(v) := kplusEmbeddingIndexQuotient v`.

This is the entry-level form of "(A - B) is the column-1-subtracted submatrix
of M_even" — the structural fact the matrix-restriction step relies on. -/
theorem sinnottMatrix_A_sub_B_apply_eq_sub
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val)
          (BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 := by
  rw [Matrix.sub_apply]
  push_cast
  rw [sinnottMatrixA_apply_eq_convolutionMatrixLogNormEven p K hp_odd hp_three i w,
    sinnottMatrixB_apply_eq_convolutionMatrixLogNormEven p K i w]

/-- **Sinnott (A - B) as a matrix-level convolution difference**.

The complex-cast Sinnott (A - B) matrix equals the matrix obtained by:
- reindexing rows of `convolutionMatrixLogNormEven p` via
  `q(familyIndexAsUnit i)` and columns via `kplusEmbeddingIndexQuotient w.val`,
- then subtracting (entrywise) the "column-1 row" of `convolutionMatrixLogNormEven p`
  at the same reindexed-column.

In matrix notation:
  `(((sinnottMatrixA - sinnottMatrixB) : Matrix _ _ ℝ)[i, w] : ℂ)
    = M_even[k(w), q(famIdx i)] - M_even[k(w), 1]`

This is the matrix-level form. Composes with column-operation determinant
invariance to give `det(A - B) = det(M_even-minor)` modulo reindexing. -/
theorem sinnottMatrix_A_sub_B_matrix_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (fun (i : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (NumberField.maximalRealSubfield K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ)) =
      fun i w =>
        convolutionMatrixLogNormEven p
            (kplusEmbeddingIndexQuotient (p := p) K w.val)
            (BernoulliRegular.cyclotomicEvenDeltaQuotient p
              (familyIndexAsUnit p K hp_odd hp_three i)) -
          convolutionMatrixLogNormEven p
            (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 := by
  funext i w
  exact sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w

/-- **`convolutionMatrixLogNormEven` at column 1**: for any row index `a`,

  `convolutionMatrixLogNormEven p a 1 = convolutionLogNormDescended p a`.

(Reason: `a · 1 = a` in the group.) -/
theorem convolutionMatrixLogNormEven_col_one
    (a : BernoulliRegular.CyclotomicEvenDelta p) :
    convolutionMatrixLogNormEven p a 1 = convolutionLogNormDescended p a := by
  unfold convolutionMatrixLogNormEven
  rw [Matrix.of_apply, mul_one]

/-- **`convolutionMatrixLogNormEven` at row 1**: for any column index `b`,

  `convolutionMatrixLogNormEven p 1 b = convolutionLogNormDescended p b`.

(Reason: `1 · b = b` in the group.) -/
theorem convolutionMatrixLogNormEven_row_one
    (b : BernoulliRegular.CyclotomicEvenDelta p) :
    convolutionMatrixLogNormEven p 1 b = convolutionLogNormDescended p b := by
  unfold convolutionMatrixLogNormEven
  rw [Matrix.of_apply, one_mul]

/-- **Embedding-index uniquely determines the K-place embedding** (cyclotomic K):
two K-places `w₁ w₂ : InfinitePlace K` have the same embedding-index iff their
underlying embeddings agree.

For K = ℚ(ζ_p), an embedding K →+* ℂ is determined by its value on the generator
ζ_K (via `PowerBasis.algHom_ext`). Since `w.embedding ζ_K = stdAddChar(embIdx w)`,
the embedding-index `embIdx w` uniquely determines `w.embedding`. -/
theorem embeddingIndex_eq_iff_embedding_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K) :
    embeddingIndex (p := p) K w₁ = embeddingIndex (p := p) K w₂ ↔
      w₁.embedding = w₂.embedding := by
  classical
  haveI hp_prime : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  constructor
  · intro h_eq
    -- Use PowerBasis.algHom_ext: AlgHoms agree iff agree on ζ_K.
    -- Both embeddings send ζ_K to stdAddChar(embIdx _), which are equal.
    -- First, identify w.embedding as a ℚ-algebra hom (uniqueness of ℚ → ℂ).
    have h_emb :
        w₁.embedding
          (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        w₂.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) := by
      rw [embeddingIndex_spec, embeddingIndex_spec, h_eq]
    -- Convert to AlgHom form using uniqueness ℚ →+* ℂ.
    -- w.embedding : K →+* ℂ. Lift to K →ₐ[ℚ] ℂ.
    -- For NumberField K, K is a ℚ-algebra, ℂ is a ℚ-algebra, and any ring hom is ℚ-algebra.
    have h_pb : IsPrimitiveRoot
        (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) p := by
      have h_OK := BernoulliRegular.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
      have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
        FaithfulSMul.algebraMap_injective (𝓞 K) K
      exact h_OK.map_of_injective h_inj
    -- Lift each w.embedding to a ℚ-algebra hom.
    let φ₁ : K →ₐ[ℚ] ℂ := { w₁.embedding with commutes' := fun r => by simp }
    let φ₂ : K →ₐ[ℚ] ℂ := { w₂.embedding with commutes' := fun r => by simp }
    -- φ₁ and φ₂ have the same underlying ring hom, so we'll show φ₁ = φ₂.
    have h_phi_eq : φ₁ = φ₂ := by
      apply (h_pb.powerBasis ℚ).algHom_ext
      simp only [φ₁, φ₂]
      change w₁.embedding (h_pb.powerBasis ℚ).gen = w₂.embedding (h_pb.powerBasis ℚ).gen
      rw [IsPrimitiveRoot.powerBasis_gen]
      exact h_emb
    -- Extract the ring hom equality.
    ext x
    have := congrArg (fun (f : K →ₐ[ℚ] ℂ) => f x) h_phi_eq
    simp only [φ₁, φ₂] at this
    exact this
  · intro h_eq
    -- Same embedding image on ζ_K gives the same embedding index.
    have h_zeta_eq :
        w₁.embedding
          (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        w₂.embedding (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) := by
      rw [h_eq]
    -- Combine with embeddingIndex_spec to extract the equality.
    have h_spec_one := embeddingIndex_spec (p := p) K w₁
    have h_spec_two := embeddingIndex_spec (p := p) K w₂
    rw [h_spec_one, h_spec_two] at h_zeta_eq
    -- Now: stdAddChar (embIdx w₁) = stdAddChar (embIdx w₂)
    -- stdAddChar is injective on (ZMod p) → ℂ.
    have h_inj := ZMod.injective_stdAddChar (N := p)
    have h_zmod_eq : ((embeddingIndex (p := p) K w₁ : ZMod p)) =
        ((embeddingIndex (p := p) K w₂ : ZMod p)) :=
      h_inj h_zeta_eq
    -- Lift to units.
    exact Units.ext h_zmod_eq

/-- **`embeddingIndex` is injective**: two K-places have the same embedding-index
iff they are equal as places.

Both directions follow from `embeddingIndex_eq_iff_embedding_eq` + `mk_embedding`. -/
theorem embeddingIndex_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Function.Injective (embeddingIndex (p := p) K) := by
  intro w₁ w₂ h
  have h_emb : w₁.embedding = w₂.embedding :=
    (embeddingIndex_eq_iff_embedding_eq (p := p) K w₁ w₂).mp h
  rw [← NumberField.InfinitePlace.mk_embedding w₁,
      ← NumberField.InfinitePlace.mk_embedding w₂, h_emb]

/-- **Negation of `stdAddChar`-argument equals `Complex.conj`**: for any `a : ZMod p`
(`p ≠ 0`), `stdAddChar(-a) = conj(stdAddChar(a))`.

`stdAddChar(a)` lies on the unit circle, so `stdAddChar(a)⁻¹ = conj(stdAddChar(a))`.
And `stdAddChar(-a) = (stdAddChar(a))⁻¹` (it's an AddChar). -/
theorem stdAddChar_neg_eq_conj [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar (N := p) (-a) =
      (starRingEnd ℂ) (ZMod.stdAddChar (N := p) a) := by
  -- stdAddChar(-a) = stdAddChar(a)⁻¹ via map_neg_eq_inv
  rw [AddChar.map_neg_eq_inv]
  -- For z = stdAddChar(a) with |z| = 1, z⁻¹ = conj(z)
  have h_norm : ‖ZMod.stdAddChar (N := p) a‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  -- z⁻¹ = z̄/|z|² = z̄/1 = z̄ when |z|=1
  exact (Complex.inv_eq_conj h_norm).symm ▸ rfl

/-- **Embedding-indices that are negatives give the same place**: if
`embIdx w₁ = -embIdx w₂`, then `w₁ = w₂` as K-places.

Reason: `w₁.embedding ζ_K = stdAddChar(-embIdx w₂) = conj(stdAddChar(embIdx w₂))
= conj(w₂.embedding ζ_K)`. Lifting both `w₁.embedding` and
`(starRingEnd ℂ).comp w₂.embedding` to ℚ-AlgHoms via `RingHom.toRatAlgHom`,
they agree on the cyclotomic power-basis generator ζ_K, hence agree
everywhere by `PowerBasis.algHom_ext`. So `w₁.embedding = conj(w₂.embedding)
= ComplexEmbedding.conjugate w₂.embedding`. By `mk_conjugate_eq`,
`mk(w₁.embedding) = mk(w₂.embedding)`, i.e., `w₁ = w₂`. -/
theorem embeddingIndex_neg_implies_place_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K)
    (h : embeddingIndex (p := p) K w₁ = -(embeddingIndex (p := p) K w₂)) :
    w₁ = w₂ := by
  classical
  haveI hp_prime : Nat.Prime p := hp.out
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  -- Step 1: w₁.embedding ζ_K = conj(w₂.embedding ζ_K).
  have h_zeta_K_eq : w₁.embedding
      (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        (starRingEnd ℂ) (w₂.embedding
          (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K))) := by
    rw [embeddingIndex_spec, embeddingIndex_spec]
    have h_cast : ((embeddingIndex (p := p) K w₁) : ZMod p) =
        -((embeddingIndex (p := p) K w₂) : ZMod p) := by
      rw [show ((embeddingIndex (p := p) K w₁) : ZMod p) =
              ((embeddingIndex (p := p) K w₁ : (ZMod p)ˣ) : ZMod p) from rfl]
      rw [h]
      rw [Units.val_neg]
    rw [h_cast]
    exact stdAddChar_neg_eq_conj p _
  -- Step 2: Use power basis to extend agreement on ζ_K to agreement everywhere.
  have h_pb : IsPrimitiveRoot
      (((BernoulliRegular.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) p := by
    have h_OK := BernoulliRegular.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
    have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K
    exact h_OK.map_of_injective h_inj
  -- Lift both ring homs to ℚ-AlgHoms.
  let φ₁ : K →ₐ[ℚ] ℂ := w₁.embedding.toRatAlgHom
  let φ₂_conj : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp w₂.embedding).toRatAlgHom
  have h_phi_eq : φ₁ = φ₂_conj := by
    apply (h_pb.powerBasis ℚ).algHom_ext
    change w₁.embedding (h_pb.powerBasis ℚ).gen =
      (starRingEnd ℂ) (w₂.embedding (h_pb.powerBasis ℚ).gen)
    rw [IsPrimitiveRoot.powerBasis_gen]
    exact h_zeta_K_eq
  -- Extract w₁.embedding = ComplexEmbedding.conjugate w₂.embedding.
  have h_emb_eq : w₁.embedding =
      NumberField.ComplexEmbedding.conjugate w₂.embedding := by
    ext x
    have := congrArg (fun (f : K →ₐ[ℚ] ℂ) => f x) h_phi_eq
    simpa [φ₁, φ₂_conj, RingHom.toRatAlgHom_apply] using this
  rw [← NumberField.InfinitePlace.mk_embedding w₁,
      ← NumberField.InfinitePlace.mk_embedding w₂, h_emb_eq,
      NumberField.InfinitePlace.mk_conjugate_eq]

/-- **Embedding-indices in the same `⟨-1⟩`-coset give the same place**: combines
`embeddingIndex_injective` (same embIdx case) and
`embeddingIndex_neg_implies_place_eq` (negated embIdx case) to cover the
full kernel of the `cyclotomicEvenDeltaQuotient`. -/
theorem embeddingIndex_quotient_eq_implies_place_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K)
    (h : BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (embeddingIndex (p := p) K w₁) =
          BernoulliRegular.cyclotomicEvenDeltaQuotient p
            (embeddingIndex (p := p) K w₂)) :
    w₁ = w₂ := by
  classical
  -- q a = q b ↔ a⁻¹ · b ∈ ⟨-1⟩ = {1, -1}.
  have h_qg : (QuotientGroup.mk (embeddingIndex (p := p) K w₁) :
      BernoulliRegular.CyclotomicEvenDelta p) =
      QuotientGroup.mk (embeddingIndex (p := p) K w₂) := h
  rw [QuotientGroup.eq] at h_qg
  rw [BernoulliRegular.CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at h_qg
  obtain ⟨k, hk⟩ := h_qg
  -- hk : (-1)^k = (embIdx w₁)⁻¹ * embIdx w₂. So embIdx w₂ = embIdx w₁ * (-1)^k.
  have h_sq : ((-1 : BernoulliRegular.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h_mod with h0 | h1
  · -- (embIdx w₁)⁻¹ · embIdx w₂ = 1 → embIdx w₁ = embIdx w₂.
    rw [h0, zpow_zero] at hk
    have h_eq : embeddingIndex (p := p) K w₁ = embeddingIndex (p := p) K w₂ := by
      have : embeddingIndex (p := p) K w₁ *
          ((embeddingIndex (p := p) K w₁)⁻¹ * embeddingIndex (p := p) K w₂) =
          embeddingIndex (p := p) K w₁ * 1 := by
        rw [← hk]
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at this
      exact this.symm
    exact embeddingIndex_injective (p := p) K h_eq
  · -- (embIdx w₁)⁻¹ · embIdx w₂ = -1 → embIdx w₂ = -embIdx w₁.
    rw [h1, zpow_one] at hk
    have h_neg : embeddingIndex (p := p) K w₂ = -embeddingIndex (p := p) K w₁ := by
      have : embeddingIndex (p := p) K w₁ *
          ((embeddingIndex (p := p) K w₁)⁻¹ * embeddingIndex (p := p) K w₂) =
          embeddingIndex (p := p) K w₁ * (-1) := by
        rw [← hk]
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_neg_one] at this
      exact this
    -- Need embIdx w₁ = -embIdx w₂, but we have embIdx w₂ = -embIdx w₁.
    have h_neg' : embeddingIndex (p := p) K w₁ = -embeddingIndex (p := p) K w₂ := by
      rw [h_neg, neg_neg]
    exact embeddingIndex_neg_implies_place_eq (p := p) K w₁ w₂ h_neg'

/-- **`kplusEmbeddingIndexQuotient` is injective**: as a map
`InfinitePlace K⁺ → CyclotomicEvenDelta p`, this is injective.

Reason: if `kplusEmbeddingIndexQuotient v₁ = kplusEmbeddingIndexQuotient v₂`,
then `q(embIdx K (eqIP.symm v₁)) = q(embIdx K (eqIP.symm v₂))`. By
`embeddingIndex_quotient_eq_implies_place_eq`, the K-places agree:
`(eqIP).symm v₁ = (eqIP).symm v₂`. Applying `eqIP`, `v₁ = v₂`. -/
theorem kplusEmbeddingIndexQuotient_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Function.Injective (kplusEmbeddingIndexQuotient (p := p) K) := by
  intro v₁ v₂ h
  unfold kplusEmbeddingIndexQuotient at h
  have h_K_eq : (NumberField.IsCMField.equivInfinitePlace K).symm v₁ =
      (NumberField.IsCMField.equivInfinitePlace K).symm v₂ :=
    embeddingIndex_quotient_eq_implies_place_eq (p := p) K _ _ h
  exact (NumberField.IsCMField.equivInfinitePlace K).symm.injective h_K_eq

/-- **`kplusEmbeddingIndexQuotient` is bijective**: `InfinitePlace K⁺` and
`CyclotomicEvenDelta p` have the same cardinality `(p-1)/2`, and the
embedding-index-quotient map is injective. Hence it's bijective. -/
theorem kplusEmbeddingIndexQuotient_bijective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    Function.Bijective (kplusEmbeddingIndexQuotient (p := p) K) := by
  classical
  haveI : Fintype (NumberField.InfinitePlace (NumberField.maximalRealSubfield K)) :=
    Fintype.ofFinite _
  haveI : Fintype (BernoulliRegular.CyclotomicEvenDelta p) :=
    Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨kplusEmbeddingIndexQuotient_injective (p := p) K, ?_⟩
  -- Use the shipped non-canonical bijection `KplusInfinitePlaceEquivCyclotomicEvenDelta`
  -- to establish the cardinality equality.
  exact Fintype.card_congr (KplusInfinitePlaceEquivCyclotomicEvenDelta (p := p) K hp_two)

/-- **Canonical bijection `InfinitePlace K⁺ ≃ CyclotomicEvenDelta p`** via
embedding-index quotient: bundles `kplusEmbeddingIndexQuotient_bijective` into
a noncomputable `Equiv`. -/
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (NumberField.maximalRealSubfield K) ≃
      BernoulliRegular.CyclotomicEvenDelta p :=
  Equiv.ofBijective (kplusEmbeddingIndexQuotient (p := p) K)
    (kplusEmbeddingIndexQuotient_bijective (p := p) K hp_two)

/-- **Family-index value as ZMod p is in `[2, (p-1)/2]`**: structural fact
that `(familyIndexAsUnit i : ZMod p).val` lies in `[2, (p-1)/2]`. -/
theorem familyIndexAsUnit_val_in_range
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val ≥ 2 ∧
      ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val ≤ (p - 1) / 2 := by
  classical
  set j : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (NumberField.maximalRealSubfield K)).symm i).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (BernoulliRegular.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K))))
  have h_fin_lt : j.val < (p - 3) / 2 := Fin.isLt _
  have h_p_prime : Nat.Prime p := hp.out
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  have h_lt_p : j.val + 2 < p := by omega
  have h_le_half : j.val + 2 ≤ (p - 1) / 2 := by omega
  have h_val_eq : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
      j.val + 2 := by
    have h_val_spec :=
      familyIndexAsUnit_val (p := p) (K := K) hp_odd hp_three i
    -- h_val_spec : ((familyIndexAsUnit i : ZMod p)) = ((j.val + 2 : ℕ) : ZMod p)
    rw [h_val_spec, ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_p]
  refine ⟨?_, ?_⟩
  · rw [h_val_eq]; omega
  · rw [h_val_eq]; exact h_le_half

/-- **`familyIndexAsUnit` is not `1` or `-1`** for `p ≥ 5`. Since the value
of `familyIndexAsUnit i` in `ZMod p` lies in `[2, (p-1)/2]`, it cannot be
`1` (excluded since 1 < 2) or `-1 = p-1` (excluded since (p-1)/2 < p-1
for p ≥ 3). -/
theorem familyIndexAsUnit_ne_one_and_neg_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (NumberField.maximalRealSubfield K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    familyIndexAsUnit p K hp_odd hp_three i ≠ 1 ∧
      familyIndexAsUnit p K hp_odd hp_three i ≠ -1 := by
  classical
  obtain ⟨h_ge, h_le⟩ := familyIndexAsUnit_val_in_range (p := p) K hp_odd hp_three i
  have h_p_prime : Nat.Prime p := hp.out
  refine ⟨?_, ?_⟩
  · -- familyIndexAsUnit i ≠ 1
    intro h_eq
    have h_val : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
        ((1 : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_eq]
    have h_one : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
      change ((1 : ZMod p)).val = 1
      rw [ZMod.val_one_eq_one_mod]
      have : 1 < p := by omega
      exact Nat.mod_eq_of_lt this
    rw [h_one] at h_val
    omega
  · -- familyIndexAsUnit i ≠ -1
    intro h_eq
    have h_val : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
        ((-1 : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_eq]
    have h_neg_one : ((-1 : (ZMod p)ˣ) : ZMod p).val = p - 1 := by
      change ((-1 : ZMod p)).val = p - 1
      haveI : NeZero p := ⟨h_p_prime.ne_zero⟩
      haveI : NeZero (1 : ZMod p) := ⟨one_ne_zero⟩
      have h_v := ZMod.val_neg_of_ne_zero (a := (1 : ZMod p))
      have h_one_val : (1 : ZMod p).val = 1 := by
        rw [ZMod.val_one_eq_one_mod]
        exact Nat.mod_eq_of_lt (by omega : 1 < p)
      rw [h_v, h_one_val]
    rw [h_neg_one] at h_val
    omega

end Sinnott

end FLT37

end BernoulliRegular

end
