# Inventory: PadicLFunctions/Interpolation/TameConductor.lean

File context: `namespace PadicLFunctions`, with `variable (p : ℕ) [hp : Fact p.Prime]` and `variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`. All inside `noncomputable section`. Inner `namespace MeasureR` (with `variable {p K}`). Proves RJW Theorem 5.1 (interpolation of ζ_p at primitive characters of p-power conductor).

---

### def toFieldChar
- Type: `{N : ℕ} (χ : DirichletCharacter (integerRing K) N) : DirichletCharacter K N`
- What: Induces a `K`-valued Dirichlet character from an `integerRing K`-valued one, by post-composing with the subring inclusion `(integerRing K).subtype`.
- How: Definitional — `χ.ringHomComp (integerRing K).subtype`.
- Hypotheses: A Dirichlet character valued in the integer ring of `K`, any modulus `N`.
- Uses from project: [`integerRing`]
- Used by: `charTwist_muA_exp_identity`, `sum_char_inv_mul_exp_identity`, `X_mul_sum_char_inv_subst`, `coe_gaussSum_zmodChar`, `sum_char_inv_H_eq`, `twist_muA_moments`, `tame_conductor_theta`, `tame_conductor`
- Visibility: public
- Lines: 34–37 (def body, no proof)
- Notes: none

### lemma charTwist_muA_mahler_identity
- Type: `{ζ : integerRing K} {N : ℕ} (hζ : IsPrimitiveRoot ζ (p^N)) (c : ℕ) {a : ℕ} (hpa : ¬ p ∣ a) : (C(ζ^(c*a))·(1+X)^a − 1)·𝓐(twist (charCM (ζ^c−1)) (baseChange (muA a))) = substAffine (ζ^c−1) (map (geomSum a)) − a`
- What: T509 step (iii), the per-`c` identity (†c): the Mahler transform of the `κ_{ζ^c−1}`-twisted base change of `μ_a` equals the `substAffine`-transport of §4's `F_a`-identity.
- How: Rewrites via `mahlerTransform_charTwist_eq_substAffine`, `mahlerTransform_baseChange`, `PadicMeasure.mahlerTransform_muA`, then transports `PadicMeasure.one_add_X_pow_sub_one_mul_Fa` through `map` and `substAffine`; closes with `substAffine_one_add_X` and a `ring`-style power-rewrite.
- Hypotheses: `ζ` a primitive `p^N`-th root of unity in `integerRing K`; `a` not divisible by `p`.
- Uses from project: [`integerRing`, `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `substAffine`, `PadicMeasure.geomSum`, `mahlerTransform_charTwist_eq_substAffine`, `mahlerTransform_baseChange`, `PadicMeasure.mahlerTransform_muA`, `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`, `substAffine_one_add_X`]
- Used by: `charTwist_muA_exp_identity`
- Visibility: public
- Lines: 44–65 (proof ~12 lines)
- Notes: `omit [CharZero K]`; proof 11–12 lines, hinges on `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`

### lemma substAffine_map_geomSum
- Type: `{ζ : integerRing K} {N : ℕ} (hζ : IsPrimitiveRoot ζ (p^N)) (c a : ℕ) : substAffine (ζ^c−1) (map (geomSum a)) = Σ_{i<a} C(ζ^(c*i))·(1+X)^i`
- What: Computes the `substAffine (ζ^c−1)`-image of the base-changed geometric sum as `Σ_{i<a} ζ^{ci}·(1+X)^i`.
- How: Unfolds `PadicMeasure.geomSum`, pushes `map`/`substAffine` through the sum (`map_sum`), and per-term applies `substAffine_one_add_X` with the algebraic identity `1+(ζ^c−1)=ζ^c`.
- Hypotheses: `ζ` a primitive `p^N`-th root of unity.
- Uses from project: [`integerRing`, `substAffine`, `PadicMeasure.geomSum`, `substAffine_one_add_X`]
- Used by: `charTwist_muA_exp_identity`
- Visibility: public
- Lines: 70–81 (proof ~5 lines)
- Notes: `omit [CharZero K]`; none

### lemma charTwist_muA_exp_identity
- Type: `(hζ : IsPrimitiveRoot ζ (p^N)) (c : ℕ) (hpa : ¬ p ∣ a) : (C((ζ:K)^(c*a))·rescale a (exp K) − 1)·(map subtype 𝓐(...)).subst (exp K − 1) = (Σ_{i<a} C((ζ:K)^(c*i))·rescale i (exp K)) − a`
- What: T509 step (iv), the t-side identity (‡c): substituting `T = e^t−1` into the `K`-valued (†c), giving `(ζ^{ca}e^{at}−1)·H_c = Σ_{i<a} ζ^{ci}e^{it} − a`.
- How: Sets up `HasSubst (exp K − 1)`; maps `charTwist_muA_mahler_identity` into `K` (via `.subtype`), rewrites the RHS by `substAffine_map_geomSum`, then applies `substAlgHom` to convert `(1+X)^i` into `rescale i (exp K)` via `PowerSeries.exp_pow_eq_rescale_exp` and the substitution lemmas (`subst_X`, `commutes`).
- Hypotheses: `ζ` a primitive `p^N`-th root of unity; `a` not divisible by `p`.
- Uses from project: [`integerRing`, `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `charTwist_muA_mahler_identity`, `substAffine_map_geomSum`, `toFieldChar` (via coercion context, not directly)]
- Used by: `charTwist_muA_exp_identity_cleared`
- Visibility: public
- Lines: 86–116 (proof ~30 lines)
- Notes: long(30-50) — proof body roughly 30 lines; hinges on `PowerSeries.exp_pow_eq_rescale_exp` and `charTwist_muA_mahler_identity`

### lemma rescale_exp_pow
- Type: `(b : K) (l : ℕ) : (rescale b (exp K))^l = rescale ((l:K)*b) (exp K)`
- What: T509 (v-c): powers of rescaled exponentials, `(E_b)^l = E_{l·b}`.
- How: Induction on `l`; base uses `rescale_zero` and `constantCoeff_exp`, successor uses `exp_mul_exp_eq_exp_add` and a `push_cast; ring` cast identity.
- Hypotheses: none beyond the scalar `b` and exponent `l`.
- Uses from project: []
- Used by: `charTwist_muA_exp_identity_cleared`, `X_mul_sum_char_inv_subst`
- Visibility: public
- Lines: 120–128 (proof ~6 lines)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K]`; none

### lemma sum_range_mul_eq_sum_range
- Type: `{M : Type*} [AddCommMonoid M] (f : ℕ → M) {a : ℕ} (N : ℕ) (ha : 0 < a) : Σ_{i<a} Σ_{j<N} f(i + a*j) = Σ_{m<a*N} f m`
- What: T509 (v-b): the division-algorithm reindexing of a double sum over `[0,a)×[0,N)` to a single sum over `[0,a·N)` via `m ↦ (m%a, m/a)`.
- How: Converts to a product sum (`Finset.sum_product`), then a `Finset.sum_nbij'` bijection with forward map `(i,j)↦i+a·j` and inverse `m↦(m%a,m/a)`; membership/inverse obligations discharged by Nat div/mod lemmas (`Nat.mod_lt`, `Nat.div_lt_of_lt_mul`, `Nat.add_mul_mod_self_left`, `Nat.add_mul_div_left`, `Nat.mod_add_div`).
- Hypotheses: `a > 0`; `f` valued in any additive commutative monoid.
- Uses from project: []
- Used by: `sum_char_inv_mul_exp_identity`, `X_mul_sum_char_inv_subst`
- Visibility: public
- Lines: 132–158 (proof ~24 lines)
- Notes: none (generic combinatorial helper)

### lemma X_mul_sum_char_rescale_exp
- Type: `{N : ℕ} [NeZero N] (hN1 : 1 < N) (χK : DirichletCharacter K N) : X·Σ_{j<N} C(χK j)·rescale j (exp K) = (mk fun k => χK.genBernoulli k·(k!)⁻¹)·(rescale N (exp K) − 1)`
- What: T509 (v-d): the `j`-indexed generating-function identity (T504) over `K` for any modulus `N>1`: `X·Σ χK(j)E_j = genBPS_χK·(E_N − 1)`, boundary terms vanishing via `χK(0)=0`.
- How: Rewrites by `genBernoulliPowerSeries_mul`; introduces `h j := χK(j)•(X·rescale j (exp K))`, shows `h 0 = 0` and `h N = 0` through `χK.map_nonunit not_isUnit_zero` and `ZMod.natCast_self`; uses `Finset.sum_range_succ'` to shift the index, then a `calc` reassembling the sum.
- Hypotheses: `N > 1`; `χK` a `K`-valued Dirichlet character mod `N`.
- Uses from project: [`genBernoulliPowerSeries_mul`] (and `DirichletCharacter.genBernoulli` from project's GenBernoulli)
- Used by: `X_mul_sum_char_inv_subst`
- Visibility: public
- Lines: 165–206 (proof ~33 lines)
- Notes: long(30-50) — proof ~33 lines; hinges on `genBernoulliPowerSeries_mul` and `Finset.sum_range_succ'`; `omit` of `Fact p.Prime`/`NormedAlgebra`/`IsUltrametricDist`/`CompleteSpace`/`CharZero`

### lemma sum_inv_char_zeta_pow
- Type: `{N : ℕ} [NeZero N] {χK : DirichletCharacter K N} (hχK : χK.IsPrimitive) {ζ' : K} (hζ' : IsPrimitiveRoot ζ' N) (j : ℕ) : Σ_{c<N} χK⁻¹ c · ζ'^(c*j) = χK j · gaussSum χK⁻¹ (zmodChar N hζ'.pow_eq_one)`
- What: T509 (v-a), the `K`-valued Gauss collapse for any modulus: `Σ_c χK⁻¹(c)·ζ'^{cj} = χK(j)·G(χK⁻¹)`.
- How: Establishes `χK⁻¹` primitive via `DirichletCharacter.conductor_inv`; rewrites the range-sum as a Gauss sum of the `mulShift`-ed additive character through a `Finset.sum_nbij'` bijection (`c ↦ (c:ZMod N)`, inverse `a ↦ a.val`); collapses via `gaussSum_mulShift_of_isPrimitive` and `inv_inv`.
- Hypotheses: `χK` primitive mod `N`; `ζ'` a primitive `N`-th root of unity in `K`.
- Uses from project: []
- Used by: `sum_char_inv_mul_exp_identity`
- Visibility: public
- Lines: 215–241 (proof ~22 lines)
- Notes: `omit` of `NormedAlgebra`/`IsUltrametricDist`/`CompleteSpace`/`CharZero`; hinges on `gaussSum_mulShift_of_isPrimitive` (mathlib)

### lemma charTwist_muA_exp_identity_cleared
- Type: `(hζ : IsPrimitiveRoot ζ (p^N)) (c : ℕ) (hpa : ¬ p ∣ a) : (rescale (a*p^N) (exp K) − 1)·(map subtype 𝓐(...)).subst (exp K − 1) = ((Σ_{i<a} C((ζ:K)^(c*i))·rescale i (exp K)) − a)·Σ_{j<p^N} C((ζ:K)^(c*(a*j)))·rescale (a*j) (exp K)`
- What: T509 (v-e) step 1: the (‡c) identity with the `a`-side denominator telescoped away.
- How: Sets cofactor base `B := C((ζ:K)^(c*a))·rescale a (exp K)`; proves `(ζ:K)^(p^N)=1` from `hζ.pow_eq_one`, computes `B^j` via `rescale_exp_pow`, then the telescope `(B−1)·Σ_j B^j = B^{p^N}−1 = E_{ap^N}−1` via `geom_sum_mul`; multiplies `charTwist_muA_exp_identity` by `Σ_j B^j` and substitutes.
- Hypotheses: `ζ` a primitive `p^N`-th root of unity; `a` not divisible by `p`.
- Uses from project: [`integerRing`, `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `rescale_exp_pow`, `charTwist_muA_exp_identity`]
- Used by: `sum_char_inv_mul_exp_identity`
- Visibility: public
- Lines: 246–281 (proof ~22 lines)
- Notes: none; hinges on `geom_sum_mul` and `rescale_exp_pow`

### lemma sum_char_inv_mul_exp_identity
- Type: `{n : ℕ} {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) (hζK : IsPrimitiveRoot (ζ:K) (p^n)) (hpa : ¬ p ∣ a) (ha : 0 < a) : (rescale (a*p^n) (exp K) − 1)·Σ_c C(toFieldChar χ⁻¹ c)·(...).subst (exp K − 1) = C(gaussSum (toFieldChar χ)⁻¹ ...)·((Σ_{m<a*p^n} C(χ̄ m)·rescale m (exp K)) − C(χ̄ a)·a·Σ_{j<p^n} C(χ̄ j)·rescale (a*j) (exp K))`
- What: T509 (v-e) step 2: the `χ̄⁻¹`-weighted sum of the telescoped identities with inner character sums collapsed by the Gauss identity.
- How: Distributes the sum; per-`c` inserts `charTwist_muA_exp_identity_cleared`, expands the product, reindexes the `(i,j)`-double sum to `m<a·p^n` via `sum_range_mul_eq_sum_range` and `exp_mul_exp_eq_exp_add`; swaps `c`/`m` and `c`/`j` sums (`Finset.sum_comm`) and collapses both via `sum_inv_char_zeta_pow`, using `χ̄(a·j)=χ̄(a)·χ̄(j)`. Primitivity of `toFieldChar χ` via `DirichletCharacter.isPrimitive_ringHomComp_iff`.
- Hypotheses: `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root in `integerRing K` and its image `(ζ:K)` primitive in `K`; `a` coprime to `p` and positive.
- Uses from project: [`integerRing`, `toFieldChar`, `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `charTwist_muA_exp_identity_cleared`, `sum_range_mul_eq_sum_range`, `sum_inv_char_zeta_pow`]
- Used by: `X_mul_sum_char_inv_subst`
- Visibility: public
- Lines: 287–402 (proof ~90 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~90 lines; hinges on `sum_range_mul_eq_sum_range`, `sum_inv_char_zeta_pow`, `DirichletCharacter.isPrimitive_ringHomComp_iff`

### lemma X_mul_sum_char_inv_subst
- Type: `{n : ℕ} (hn : 1 ≤ n) {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) (hζK : IsPrimitiveRoot (ζ:K) (p^n)) (hpa : ¬ p ∣ a) : X·Σ_c C(toFieldChar χ⁻¹ c)·(...).subst (exp K − 1) = C(gaussSum (toFieldChar χ)⁻¹ ...)·((mk fun k => χ̄.genBernoulli k·(k!)⁻¹) − C(χ̄ a)·rescale a (mk fun k => χ̄.genBernoulli k·(k!)⁻¹))`
- What: T509 (v-e) FINAL-10b, the χ-analogue of §4's `X_mul_subst_exp_Fa`: `X·Σ_c χ̄⁻¹(c)·H_c = G'·(genBPS_χ̄ − χ̄(a)·rescale a genBPS_χ̄)`.
- How: Shows regular factor `E_{ap^n}−1 ≠ 0` (coeff-1 argument). Cancels it via `mul_left_cancel₀`, plugs in `sum_char_inv_mul_exp_identity`. Sub-claim (A) `X·Σ_{m<ap^n} χ̄(m)E_m = genBPS·(E_{ap^n}−1)` by block-splitting `m = i + p^n·l` (`sum_range_mul_eq_sum_range`, `rescale_exp_pow`, `ZMod.natCast_self`) and applying `X_mul_sum_char_rescale_exp` + `geom_sum_mul`. Sub-claim (B) the `a`-side via the `rescale a`-image of (v-d). Assembles with `linear_combination`.
- Hypotheses: `n ≥ 1`; `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root and `(ζ:K)` primitive; `a` coprime to `p`.
- Uses from project: [`integerRing`, `toFieldChar`, `mahlerTransform`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `sum_char_inv_mul_exp_identity`, `sum_range_mul_eq_sum_range`, `rescale_exp_pow`, `X_mul_sum_char_rescale_exp`]
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 406–534 (proof ~108 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~108 lines; hinges on `X_mul_sum_char_rescale_exp`, `sum_char_inv_mul_exp_identity`, `sum_range_mul_eq_sum_range`, `geom_sum_mul`

### def delField
- Type: `(G : PowerSeries K) : PowerSeries K`
- What: The operator `∂ = (1+t)·d/dt` over the coefficient field `K` (a `delQ`/`MeasureR.del`-analogue, to be merged at cleanup).
- How: Definitional — `(1 + X) * PowerSeries.derivativeFun G`.
- Hypotheses: A power series over `K`.
- Uses from project: []
- Used by: `map_subtype_del`, `derivativeFun_subst_exp_K`, `constantCoeff_iterate_delField`
- Visibility: public (in `section fieldBridge`, `open PowerSeries`)
- Lines: 542–543 (def, no proof)
- Notes: none; carries a "to be merged with `MeasureR.del`/`PadicMeasure.delQ` at cleanup" TODO-style note in docstring

### lemma map_subtype_derivativeFun
- Type: `(F : PowerSeries (integerRing K)) : map subtype (derivativeFun F) = derivativeFun (map subtype F)`
- What: The subring inclusion commutes with the formal derivative `derivativeFun`.
- How: `ext n` then `simp [coeff_derivativeFun]`.
- Hypotheses: A power series over `integerRing K`.
- Uses from project: [`integerRing`]
- Used by: `map_subtype_del`
- Visibility: public
- Lines: 546–549 (proof 2 lines)
- Notes: `omit [CompleteSpace K] [CharZero K]`; none

### lemma map_subtype_del
- Type: `(F : PowerSeries (integerRing K)) : map subtype (del K F) = delField (map subtype F)`
- What: The subring inclusion intertwines `del K` with `delField`.
- How: Unfolds `del`, `delField`, pushes `map` through `mul`/`add`/`X` and applies `map_subtype_derivativeFun`.
- Hypotheses: A power series over `integerRing K`.
- Uses from project: [`integerRing`, `del`, `delField`, `map_subtype_derivativeFun`]
- Used by: `map_subtype_del_iterate`
- Visibility: public
- Lines: 553–557 (proof ~2 lines)
- Notes: `omit [CompleteSpace K] [CharZero K]`; none

### lemma map_subtype_del_iterate
- Type: `(j : ℕ) (F : PowerSeries (integerRing K)) : map subtype ((del K)^[j] F) = delField^[j] (map subtype F)`
- What: The subring inclusion intertwines the `j`-fold iterate of `del K` with that of `delField`.
- How: Induction on `j` (generalizing `F`); successor uses `Function.iterate_succ_apply'` on both sides and `map_subtype_del`.
- Hypotheses: A power series over `integerRing K`; iteration count `j`.
- Uses from project: [`integerRing`, `del`, `delField`, `map_subtype_del`]
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 560–567 (proof ~5 lines)
- Notes: `omit [CompleteSpace K] [CharZero K]`; none

### lemma hasSubst_exp_sub_one_K
- Type: `: HasSubst (exp K − 1)`
- What: The power series `e^t − 1` is a valid substitution (constant coefficient zero) over `K`.
- How: `HasSubst.of_constantCoeff_zero' (by simp)`.
- Hypotheses: none.
- Uses from project: []
- Used by: `derivativeFun_subst_exp_K`, `constantCoeff_subst_exp_K`, `sum_char_inv_H_eq`
- Visibility: public
- Lines: 570–571 (proof 1 line)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K]`; none

### lemma derivativeFun_subst_exp_K
- Type: `(F : PowerSeries K) : derivativeFun (F.subst (exp K − 1)) = (delField F).subst (exp K − 1)`
- What: Chain rule for the substitution `T = e^t−1` over `K`: differentiating `F(e^t−1)` gives `(∂F)(e^t−1)`.
- How: `calc` from `derivative_subst` (the substitution chain rule), using `d⁄dX (exp K − 1) = exp K` (`derivative_exp`), then unfolds `delField` and reassembles with `subst_mul`/`subst_add`/`subst_X` and `ring_nf`.
- Hypotheses: A power series `F` over `K`.
- Uses from project: [`delField`, `hasSubst_exp_sub_one_K`]
- Used by: `constantCoeff_iterate_delField`
- Visibility: public
- Lines: 575–590 (proof ~12 lines)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K]`; proof 11–12 lines, hinges on `PowerSeries.derivative_subst` (mathlib)

### lemma constantCoeff_subst_exp_K
- Type: `(F : PowerSeries K) : constantCoeff (F.subst (exp K − 1)) = constantCoeff F`
- What: The constant coefficient is invariant under the substitution `T = e^t−1`.
- How: Rewrites via `constantCoeff_subst` (the infinite-sum formula), reduces the `finsum` to its `d = 0` term using `MvPowerSeries.constantCoeff (exp K − 1) = 0` and `zero_pow`, then `simp`.
- Hypotheses: A power series `F` over `K`.
- Uses from project: [`hasSubst_exp_sub_one_K`]
- Used by: `constantCoeff_iterate_delField`
- Visibility: public
- Lines: 593–603 (proof ~9 lines)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K]`; none

### lemma constantCoeff_iterate_derivativeFun_K
- Type: `(k : ℕ) (G : PowerSeries K) : constantCoeff (derivativeFun^[k] G) = (k!:K)·coeff k G`
- What: The constant coefficient of the `k`-fold formal derivative equals `k!·[t^k]G`.
- How: Induction on `k` (generalizing `G`); successor uses `Function.iterate_succ_apply`, `coeff_derivativeFun`, `Nat.factorial_succ`, then `push_cast; ring`.
- Hypotheses: A power series `G` over `K`; index `k`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 606–614 (proof ~7 lines)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`; none

### lemma constantCoeff_iterate_delField
- Type: `(k : ℕ) (F : PowerSeries K) : constantCoeff (delField^[k] F) = (k!:K)·coeff k (F.subst (exp K − 1))`
- What: `(∂^k F)(0) = k!·[t^k](F(e^t−1))` over `K` — links the iterated `delField` constant term to a coefficient of the exp-substituted series.
- How: Induction on `k` (generalizing `F`); base uses `constantCoeff_subst_exp_K`; successor uses `Function.iterate_succ_apply`, `derivativeFun_subst_exp_K` (reversed), `coeff_derivativeFun`, `Nat.factorial_succ`, then `push_cast; ring`.
- Hypotheses: A power series `F` over `K`; index `k`.
- Uses from project: [`delField`, `constantCoeff_subst_exp_K`, `derivativeFun_subst_exp_K`]
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 618–627 (proof ~8 lines)
- Notes: `omit [IsUltrametricDist K] [CompleteSpace K]`; none

### lemma gaussSum_inv_ne_zero
- Type: `{N : ℕ} [NeZero N] {χK : DirichletCharacter K N} (hχK : χK.IsPrimitive) {ζ' : K} (hζ' : IsPrimitiveRoot ζ' N) : gaussSum χK⁻¹ (zmodChar N hζ'.pow_eq_one) ≠ 0`
- What: The Gauss sum of a primitive character against a primitive additive character is nonzero (any modulus), via `G(χ)G(χ⁻¹)=N`.
- How: Uses `AddChar.zmodChar_primitive_of_primitive_root` for additive-character primitivity, `DirichletCharacter.conductor_inv` for `χ⁻¹` primitive, `gaussSum_mul_gaussSum_inv` for the product `= N`; shows the inverse-shift Gauss sum nonzero (else `N = 0`), then `AddChar.inv_mulShift` + `gaussSum_mulShift_of_isPrimitive` + `right_ne_zero_of_mul`.
- Hypotheses: `χK` primitive mod `N`; `ζ'` a primitive `N`-th root of unity in `K`.
- Uses from project: []
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 635–650 (proof ~13 lines)
- Notes: `omit` of `Fact p.Prime`/`NormedAlgebra`/`IsUltrametricDist`/`CompleteSpace`; proof 12–13 lines, hinges on `gaussSum_mul_gaussSum_inv` (mathlib)

### lemma coe_gaussSum_zmodChar
- Type: `{N : ℕ} [NeZero N] (χ : DirichletCharacter (integerRing K) N) (hζ : IsPrimitiveRoot ζ N) (hζK : IsPrimitiveRoot (ζ:K) N) : ((gaussSum χ⁻¹ (zmodChar N hζ.pow_eq_one) : integerRing K) : K) = gaussSum (toFieldChar χ)⁻¹ (zmodChar N hζK.pow_eq_one)`
- What: The `K`-coercion of the integral Gauss sum equals the `K`-valued Gauss sum of the induced character (any modulus).
- How: Unfolds both `gaussSum` as finite sums, pushes the coercion through (`AddSubmonoidClass.coe_finsetSum`), per-term uses `MulChar.ringHomComp_inv` (so `(toFieldChar χ)⁻¹ = toFieldChar χ⁻¹`) and `AddChar.zmodChar_apply`, closing with `rfl`.
- Hypotheses: `ζ` primitive `N`-th root in `integerRing K`; its image `(ζ:K)` primitive in `K`.
- Uses from project: [`integerRing`, `toFieldChar`]
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 655–666 (proof ~6 lines)
- Notes: `omit [CompleteSpace K] [CharZero K] [NormedAlgebra ℚ_[p] K]`; none

### lemma sum_char_inv_H_eq
- Type: `{n : ℕ} {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) {a : ℕ} : Σ_c C(toFieldChar χ⁻¹ c)·(map subtype 𝓐(twist (charCM (ζ^c−1)) ...)).subst (exp K − 1) = C((gaussSum χ⁻¹ ... : integerRing K):K)·(map subtype 𝓐(twist χ.toContinuousMapZp ...)).subst (exp K − 1)`
- What: T509 (v-f) transport: the `χ̄⁻¹`-weighted sum of the `H_c` equals the `K`-coerced Gauss sum times `H_χ` (T508 carried through the Mahler transform, the coefficient inclusion, and the exp substitution).
- How: Builds helper rewrites for `map subtype` of a scalar-`smul` and for `subst (exp K − 1)` of a `C x · F`; applies `mahler_twist_formula` (T508) and pushes it through `mahlerTransformₗ` (the linear-map form of `mahlerTransform`), then `map subtype` and the exp substitution; final per-`c` congruence uses `MulChar.ringHomComp_inv`.
- Hypotheses: `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root of unity.
- Uses from project: [`integerRing`, `toFieldChar`, `mahlerTransform`, `mahlerTransformₗ`, `twist`, `charCM`, `tendsto_pow_pow_sub_one`, `baseChange`, `PadicMeasure.muA`, `hasSubst_exp_sub_one_K`, `mahler_twist_formula`]
- Used by: `twist_muA_moments`
- Visibility: public
- Lines: 671–748 (proof ~60 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~60 lines; hinges on `mahler_twist_formula` (T508) and `MulChar.ringHomComp_inv`

### theorem twist_muA_moments
- Type: `{n : ℕ} (hn : 1 ≤ n) {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) {a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) : ((twist χ.toContinuousMapZp (baseChange (muA a)) (powCM k) : integerRing K):K) = −(1 − (χ a:K)·(a:K)^(k+1))·LvalNeg (toFieldChar χ) k`
- What: L5.1.10 (RJW eq. special value thm 1): the χ-twisted `k`-th moment of base-changed `μ_a`, namely `∫ χ(x)x^k dμ_a = −(1 − χ(a)a^{k+1})·L(χ,−k)`, in uniform `LvalNeg` form.
- How: Establishes `(ζ:K)` primitivity (`IsPrimitiveRoot.map_of_injective`), `toFieldChar χ` primitivity, Gauss sum nonvanishing (`gaussSum_inv_ne_zero`). Expresses the moment as `k!·[t^k] H_χ` via `apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`. Takes the `(k+1)`-st coefficient of `X_mul_sum_char_inv_subst`, rewrites by `coeff_succ_X_mul`, `sum_char_inv_H_eq`, `coe_gaussSum_zmodChar`; cancels the Gauss sum (`mul_left_cancel₀`); unfolds `LvalNeg` and closes with `field_simp`/`push_cast`/`ring`.
- Hypotheses: `n ≥ 1`; `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root; `a` coprime to `p`; exponent `k`.
- Uses from project: [`integerRing`, `twist`, `baseChange`, `PadicMeasure.muA`, `powCM`, `LvalNeg`, `toFieldChar`, `gaussSum_inv_ne_zero`, `apply_powCM`, `map_subtype_del_iterate`, `constantCoeff_iterate_delField`, `mahlerTransform`, `del`, `X_mul_sum_char_inv_subst`, `sum_char_inv_H_eq`, `coe_gaussSum_zmodChar`]
- Used by: `tame_conductor_theta`
- Visibility: public
- Lines: 760–820 (proof ~52 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~52 lines; hinges on `X_mul_sum_char_inv_subst`, `sum_char_inv_H_eq`, `constantCoeff_iterate_delField`; statement-replan note re: `hζ` mirroring source's `ε_{p^n}`

### lemma cmul_powCM_one_iota_zetaNum
- Type: `(a : ℕ) : cmul (powCM 1) (iota (zetaNum a)) = res (isClopen_units) (muA a)`
- What: Multiplying `ι(ζ-numerator)` by `x` recovers the unit-restriction of `μ_a` (the `x⁻¹`-shift, RJW eq. 4.11, transported through `ι`).
- How: Rewrites by `PadicMeasure.iota_muAUnits`, then `LinearMap.ext`; reduces (via `change`) to a statement about `muAUnits`, with the inner `invCM`/`unitsValCM` simplification using `pow_one`, `Units.val_mul`, `inv_mul_cancel`.
- Hypotheses: `a : ℕ`.
- Uses from project: [`PadicMeasure.cmul`, `PadicMeasure.powCM`, `PadicMeasure.iota`, `PadicMeasure.zetaNum`, `PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.muA`, `PadicMeasure.iota_muAUnits`, `PadicMeasure.muAUnits`, `PadicMeasure.invCM`, `PadicMeasure.unitsValCM`]
- Used by: `tame_conductor_theta`
- Visibility: public
- Lines: 824–839 (proof ~9 lines)
- Notes: none

### theorem tame_conductor_theta
- Type: `{n : ℕ} (hn : 1 ≤ n) {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) {a : ℕ} (hpa : ¬ p ∣ a) {k : ℕ} (hk : 0 < k) : ((baseChange (iota (zetaNum a)) (χ.toContinuousMapZp · powCM k) : integerRing K):K) = −(1 − (χ a:K)·(a:K)^k)·LvalNeg (toFieldChar χ) (k−1)`
- What: RJW Theorem 5.1, θ-form (source's engine): the χ-twisted `k`-th moment of the base change of the §4 unit-side measure `zetaNum a = x⁻¹·Res(μ_a)` equals `−(1−χ(a)a^k)·L(χ,1−k)`.
- How: Splits one power of `x` off the test function (`χ̃·x^k = (x^1)·(χ̃·x^{k−1})`), shifts through base change via `baseChange_cmul` and `cmul_powCM_one_iota_zetaNum` (restoring `μ_a`) and `baseChange_res`; shows restriction is invisible to the χ-twist (a `twist`/`res` commutation, `twist_res_units`), then applies `twist_muA_moments` at exponent `k−1` and `Nat.sub_add_cancel`.
- Hypotheses: `n ≥ 1`; `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root; `a` coprime to `p`; `k > 0`.
- Uses from project: [`integerRing`, `baseChange`, `PadicMeasure.iota`, `PadicMeasure.zetaNum`, `powCM`, `LvalNeg`, `toFieldChar`, `cmul`, `algCM`, `PadicMeasure.powCM`, `baseChange_cmul`, `cmul_powCM_one_iota_zetaNum`, `baseChange_res`, `res`, `PadicMeasure.muA`, `PadicMeasure.isClopen_units`, `twist`, `charFnCM`, `twist_res_units`, `twist_muA_moments`]
- Used by: `tame_conductor`
- Visibility: public
- Lines: 848–912 (proof ~57 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~57 lines; hinges on `twist_muA_moments`, `cmul_powCM_one_iota_zetaNum`, `twist_res_units`; statement-replan note re: `hζ`

### lemma iota_dirac_mul
- Type: `(w : ℤ_[p]ˣ) (μ : PadicMeasure p ℤ_[p]ˣ) : iota (dirac w * μ) = sigma w (iota μ)`
- What: Pushing a units-Dirac convolution through `ι` gives the dilation `σ_w`.
- How: `LinearMap.ext`; reduces via `change` to a `dirac`/`innerInt` statement, rewriting `PadicMeasure.units_mul_apply`, `dirac_apply`, `innerInt_apply`, then `rfl`.
- Hypotheses: a unit `w`; a measure `μ` on `ℤ_[p]ˣ`.
- Uses from project: [`PadicMeasure.iota`, `PadicMeasure.dirac`, `PadicMeasure.sigma`, `PadicMeasure.unitsValCM`, `PadicMeasure.mulCM`, `PadicMeasure.units_mul_apply`, `PadicMeasure.dirac_apply`, `PadicMeasure.innerInt_apply`]
- Used by: `tame_conductor`
- Visibility: public
- Lines: 915–923 (proof ~5 lines)
- Notes: none

### theorem baseChange_pushforward
- Type: `(h : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) : baseChange (pushforward h μ) = pushforward h (baseChange μ)`
- What: Base change commutes with pushforward along `ℤ_p`-self-maps.
- How: `ext_locallyConstant`; writes the test locally-constant function as a sum of scaled characteristic functions (`locallyConstant_eq_sum_smul_charFn`), pushes both `baseChange` and `pushforward` through the sum and the `smul`; per-fiber uses `algCM_charFn` and `baseChange_algCM` plus the definitional `pushforward`/`comp` equalities.
- Hypotheses: a continuous self-map `h` of `ℤ_p`; a measure `μ` on `ℤ_p`.
- Uses from project: [`baseChange`, `PadicMeasure.pushforward`, `pushforward`, `ext_locallyConstant`, `locallyConstant_eq_sum_smul_charFn`, `algCM`, `algCM_charFn`, `baseChange_algCM`]
- Used by: `tame_conductor`
- Visibility: public
- Lines: 927–947 (proof ~17 lines)
- Notes: `omit [CharZero K]`; none

### lemma char_pow_comp_mulCM
- Type: `{n : ℕ} (χ : DirichletCharacter (integerRing K) (p^n)) (w : ℤ_[p]ˣ) (k : ℕ) : (χ.toContinuousMapZp · powCM k).comp (mulCM w) = (χ̃(w)·w^k) • (χ.toContinuousMapZp · powCM k)`
- What: The character-monomial is a `w`-dilation eigenfunction: `(χ̃·x^k)(w·x) = χ̃(w)w^k·(χ̃·x^k)(x)`.
- How: `ext x`, then `congrArg Subtype.val`; reduces via `change` to a ring identity in `integerRing K`, rewriting `DirichletCharacter.toContinuousMapZp_apply` (thrice), `map_mul`, `mul_pow`, then `ring`.
- Hypotheses: a character `χ` mod `p^n`; a unit `w`; exponent `k`.
- Uses from project: [`integerRing`, `powCM`, `PadicMeasure.mulCM`, `DirichletCharacter.toContinuousMapZp`, `DirichletCharacter.toContinuousMapZp_apply`]
- Used by: `tame_conductor`
- Visibility: public
- Lines: 952–969 (proof ~10 lines)
- Notes: `omit [CompleteSpace K] [CharZero K]`; none

### theorem tame_conductor
- Type: `{n : ℕ} (hn : 1 ≤ n) (hp2 : p ≠ 2) {χ : DirichletCharacter (integerRing K) (p^n)} (hχ : χ.IsPrimitive) (hζ : IsPrimitiveRoot ζ (p^n)) {k : ℕ} (hk : 0 < k) (b : ℤ_[p]ˣ) (ν : PadicMeasure p ℤ_[p]ˣ) (hν : algebraMap (dirac b − 1)·padicZeta = algebraMap ν) : ((baseChange (iota ν) (χ.toContinuousMapZp · powCM k):integerRing K):K) = ((χ (toZModPow n b):K)·algebraMap (b^k) − 1)·LvalNeg (toFieldChar χ) (k−1)`
- What: RJW Theorem 5.1, witness form (mirroring `PadicMeasure.kubotaLeopoldt`'s encoding): for any unit `b` and any witness `ν` of `([b]−[1])·ζ_p`, the χ-twisted `k`-th moment of base-changed `ν` is `(χ(b)b^k − 1)·L(χ,1−k)`.
- How: Extracts a topological generator `u` (= `m`-th power data) from `PadicMeasure.exists_nat_topological_generator`. Pulls back the defining relation `([u]−1)·ζ_p = zetaNum m` (`IsLocalization.mk'_spec'`) and derives `([u]−1)·ν = ([b]−1)·zetaNum m` (`IsFractionRing.injective`). Defines the moment functional `Θ`, proving it subtractive (`hΘsub`) and a dilation-eigen (`heigen`, via `iota_dirac_mul`, `baseChange_pushforward`, `char_pow_comp_mulCM`). Applies `Θ` to the key relation; evaluates `Θ(zetaNum m)` by `tame_conductor_theta`; shows the `c_u−1` factor nonvanishing via finite character order (`pow_card_eq_one'`) descending `m^{kN}=1` to ℤ_p and contradicting `PadicMeasure.topGen_pow_ne_one`; cancels (`mul_left_cancel₀`) and closes with `linear_combination`.
- Hypotheses: `n ≥ 1`; `p ≠ 2`; `χ` primitive mod `p^n`; `ζ` primitive `p^n`-th root; `k > 0`; a unit `b`; a measure-witness `ν` satisfying the localization relation `hν`.
- Uses from project: [`integerRing`, `baseChange`, `PadicMeasure.iota`, `powCM`, `LvalNeg`, `toFieldChar`, `PadicMeasure.dirac`, `PadicMeasure.padicZeta`, `PadicMeasure.QuotientField`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.zetaNum`, `tame_conductor_theta`, `iota_dirac_mul`, `baseChange_pushforward`, `char_pow_comp_mulCM`, `PadicMeasure.sigma`, `PadicMeasure.pushforward`, `pushforward`, `PadicMeasure.mulCM`, `DirichletCharacter.toContinuousMapZp`, `PadicMeasure.unitsToZModPow`, `PadicMeasure.unitsToZModPow_coe`, `PadicMeasure.topGen_pow_ne_one`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 981–1116 (proof ~124 lines)
- Notes: **OVER-50** (needs /decompose-proof) — proof body ~124 lines; hinges on `tame_conductor_theta`, `char_pow_comp_mulCM`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.topGen_pow_ne_one`; uses `classical`

---

## File Summary

- **Total declarations: 24** — defs: 2 (`toFieldChar`, `delField`); lemmas + theorems: 22 (16 lemmas + 6 theorems: `twist_muA_moments`, `tame_conductor_theta`, `baseChange_pushforward`, `tame_conductor` are `theorem`; plus `map_subtype_*`, etc. are `lemma`); instances: 0; structures/classes/abbrevs/inductives: 0.
- **Key API (used by ≥3 in this file):**
  - `toFieldChar` — used by 8 decls.
  - `delField` — used by 3 (`map_subtype_del`, `derivativeFun_subst_exp_K`, `constantCoeff_iterate_delField`).
  - (Note: most engine lemmas form a single linear dependency chain, each used once.)
- **Unused in file:** `constantCoeff_iterate_derivativeFun_K` (lines 606–614); top-level results not consumed here: `tame_conductor` (the final RJW 5.1 export).
- **Decls with sorry:** none.
- **set_option:** none.
- **sorry / TODO / admit:** no `sorry`/`admit`; `delField` docstring carries a cleanup-merge note (`del`/`delQ`); several `*_muA_moments`/`tame_conductor*` docstrings carry "statement-replan" notes on the `hζ` hypothesis.
- **Proofs > 50 lines (OVER-50, need /decompose-proof): 6** — `sum_char_inv_mul_exp_identity` (~90), `X_mul_sum_char_inv_subst` (~108), `sum_char_inv_H_eq` (~60), `twist_muA_moments` (~52), `tame_conductor_theta` (~57), `tame_conductor` (~124).
- **Proofs 30–50 lines (long): 2** — `charTwist_muA_exp_identity` (~30), `X_mul_sum_char_rescale_exp` (~33).
