# Inventory: PadicLFunctions/ExtLog.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/ExtLog.lean`

Namespace: `PadicLFunctions`. Module: the extended (Iwasawa-branch) p-adic logarithm `extLog` (RJW §6, decomposition W6a), extending `padicLog` to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the exponential ball.

Global variables: `(p : ℕ) [hp : Fact p.Prime]`; `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`. Section `ExpBallSeminormedRing` additionally introduces `{R : Type*} [SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]`.

---

### theorem norm_lt_one_of_inExpBall
- Type: `{w : R} (hw : InExpBall p w) : ‖w‖ < 1`
- What: Any member of the exponential ball has norm strictly less than one.
- How: By contradiction; if `‖w‖ ≥ 1` then `‖w‖^(p-1) ≥ 1 > p⁻¹`, contradicting the ball condition via `inv_le_one_of_one_le₀` and `one_le_pow₀`.
- Hypotheses: `w` lies in the exponential ball (`‖w‖^(p-1) < p⁻¹`); `R` an ultrametric seminormed ring (norm-one/ultrametric instances omitted here).
- Uses from project: [InExpBall] (the predicate, from PadicExp)
- Used by: `mul_mem_expBall`, `norm_eq_one_of_inExpBall_sub_one`
- Visibility: public
- Lines: 44-50 (proof ~5 lines)
- Notes: none. `omit [NormOneClass R] [IsUltrametricDist R]`.

### theorem mul_mem_expBall
- Type: `{y z : R} (hy : InExpBall p (y - 1)) (hz : InExpBall p (z - 1)) : InExpBall p (y * z - 1)`
- What: The translated exponential ball `1 + B` is closed under multiplication (W6a-a1).
- How: Rewrite `y*z - 1 = (y-1)*z + (z-1)` (noncomm_ring), apply the strong (ultrametric) triangle inequality `IsUltrametricDist.norm_add_le_max`, bound `‖z‖ ≤ 1`, then bound the `(p-1)`-power by the max of the two ball radii via `pow_le_pow_left₀`.
- Hypotheses: `y-1` and `z-1` both in the exponential ball; `R` an ultrametric seminormed ring with `‖1‖=1`.
- Uses from project: [InExpBall, norm_lt_one_of_inExpBall]
- Used by: `pow_mem_expBall`, `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`
- Visibility: public
- Lines: 52-70 (proof ~15 lines)
- Notes: long(30-50)? No — ~15 lines. none.

### theorem pow_mem_expBall
- Type: `{y : R} (hy : InExpBall p (y - 1)) (n : ℕ) : InExpBall p (y ^ n - 1)`
- What: The translated exponential ball is closed under taking natural powers.
- How: Induction on `n`; base case `n=0` gives `1-1=0` with `‖0‖^(p-1)=0 < p⁻¹`; successor step uses `pow_succ` and `mul_mem_expBall`.
- Hypotheses: `y-1` in the exponential ball; `R` ultrametric seminormed ring with `‖1‖=1`.
- Uses from project: [InExpBall, mul_mem_expBall]
- Used by: `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`, `extLog_witness_smul_eq` (via padicLog_pow chain — actually used by `padicLog_pow`)
- Visibility: public
- Lines: 72-82 (proof ~9 lines)
- Notes: none.

### theorem padicLog_pow
- Type: `{y : L} (hy : InExpBall p (y - 1)) (n : ℕ) : padicLog p (y ^ n) = n • padicLog p y`
- What: The p-adic logarithm of a power equals the scalar multiple `n • log` on the ball (W6a-a2).
- How: Induction on `n`; successor step rewrites `pow_succ`, applies `padicLog_mul` (with `pow_mem_expBall` for membership of `y^k`), the IH, and `succ_nsmul`.
- Hypotheses: `y-1` in exp ball; `L` a complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [InExpBall, padicLog_mul, pow_mem_expBall]
- Used by: `extLog_witness_smul_eq`, `extLog_mul`
- Visibility: public
- Lines: 86-92 (proof ~5 lines)
- Notes: none.

### theorem norm_natCast_p
- Type: `‖((p : ℕ) : L)‖ = (p : ℝ)⁻¹`
- What: The norm of the image of `p` in `L` equals `p⁻¹`.
- How: Rewrite `(p:L)` as `algebraMap ℚ_[p] L (p:ℚ_[p])` via `map_natCast`, then `norm_algebraMap'` and `Padic.norm_p`.
- Hypotheses: `L` a normed `ℚ_[p]`-algebra (ultrametric/complete omitted).
- Uses from project: []
- Used by: `norm_pow_p_sub_one_le`, `exists_pow_sub_one_norm_le`, `extLog_witness_smul_eq`, `natCast_p_ne_zero`
- Visibility: public
- Lines: 94-99 (proof ~3 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem norm_pow_p_sub_one_le
- Type: `{w : L} (hw : ‖w - 1‖ < 1) : ‖w ^ p - 1‖ ≤ max (‖w - 1‖ ^ p) ((p : ℝ)⁻¹ * ‖w - 1‖)`
- What: One p-th power step contracts towards 1: `‖w^p - 1‖` is bounded by the max of the top term `‖w-1‖^p` and a `p⁻¹`-scaled term (W6a-a3).
- How: Binomial expansion `w^p - 1 = Σ_{i<p} t^(i+1)·(p choose i+1)` with `t=w-1`; ultrametric `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`; split top term (`i+1=p`, `choose_self=1`) from interior terms, where `hp.out.dvd_choose_self` gives `p ∣ (p choose i+1)` so `‖p choose‖ ≤ p⁻¹` via `norm_natCast_p` and `IsUltrametricDist.norm_natCast_le_one`.
- Hypotheses: `‖w-1‖ < 1`; `L` ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [norm_natCast_p]
- Used by: `exists_pPow_pow_inExpBall`
- Visibility: public
- Lines: 101-131 (proof ~27 lines)
- Notes: none (just under 30). `omit [CompleteSpace L]`. Hinges on `Nat.Prime.dvd_choose_self`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.

### theorem exists_pPow_pow_inExpBall
- Type: `{w : L} (hw : ‖w - 1‖ < 1) : ∃ j : ℕ, InExpBall p (w ^ p ^ j - 1)`
- What: From the open unit ball, some p-power iterate `w^(p^j)` lands inside the exponential ball (W6a-a4), via geometric contraction with ratio `t0 = max(‖w-1‖^(p-1), p⁻¹) < 1`.
- How: Define `t0`; prove decay bound `‖w^(p^j) - 1‖ ≤ t0^j · ‖w-1‖` by induction (step uses `norm_pow_p_sub_one_le` and `hbound` squeezing `max(...,...) ≤ t0·‖...‖`); show `(t0^j·‖w-1‖)^(p-1) → 0` via `tendsto_pow_atTop_nhds_zero_of_lt_one`; extract `N` with `Metric.tendsto_atTop` so the `(p-1)`-power is below `p⁻¹`.
- Hypotheses: `‖w-1‖ < 1`; `L` ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [InExpBall, norm_pow_p_sub_one_le]
- Used by: `extLogDomain_of_integral_norm_one`
- Visibility: public
- Lines: 133-188 (proof ~52 lines)
- Notes: OVER-50 (needs /decompose-proof). `omit [CompleteSpace L]`. Hinges on `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Metric.tendsto_atTop`.

### theorem norm_eq_one_of_inExpBall_sub_one
- Type: `{y : L} (hy : InExpBall p (y - 1)) : ‖y‖ = 1`
- What: Members of the translated exponential ball `1 + B` have norm exactly one.
- How: Ultrametric isosceles: since `‖y-1‖ < 1 = ‖1‖` are unequal, `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` gives `‖(y-1)+1‖ = max = ‖1‖ = 1`.
- Hypotheses: `y-1` in exp ball; `L` ultrametric normed field (algebra/complete omitted).
- Uses from project: [InExpBall, norm_lt_one_of_inExpBall]
- Used by: `extLog_witness_smul_eq`
- Visibility: public
- Lines: 190-199 (proof ~5 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.

### theorem norm_le_one_of_mem_adjoin_int
- Type: `{z : L} (hz1 : ‖z‖ ≤ 1) {s : L} (hs : s ∈ Algebra.adjoin ℤ ({z} : Set L)) : ‖s‖ ≤ 1`
- What: Every element of the `ℤ`-subalgebra generated by a norm-≤1 element has norm at most one.
- How: `Algebra.adjoin_induction`: the generator `z` is bounded by hypothesis; `algebraMap` (integers) bounded by `IsUltrametricDist.norm_intCast_le_one`; addition via ultrametric `norm_add_le_max`; multiplication via `norm_mul` and `mul_le_one₀`.
- Hypotheses: `‖z‖ ≤ 1`; `s` in the `ℤ`-adjoin of `{z}`; `L` ultrametric normed field (algebra/complete omitted).
- Uses from project: []
- Used by: `exists_pow_sub_one_norm_le`
- Visibility: public
- Lines: 201-214 (proof ~8 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.

### theorem finite_adjoin_int_quotient
- Type: `{z : L} (hz : IsIntegral ℤ z) : Finite ((Algebra.adjoin ℤ ({z} : Set L)) ⧸ Ideal.span {(p : Algebra.adjoin ℤ ({z} : Set L))})`
- What: The quotient `ℤ[z]/(p)` of the subalgebra generated by an integral element is finite.
- How: `ℤ[z]` is `ℤ`-module-finite by `Module.Finite.of_fg` of `hz.fg_adjoin_singleton`; the quotient is `ℤ`-module-finite (`Module.Finite.quotient`) and `ℤ`-torsion (killed by `p`, shown via `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mul_mem_right`); conclude by `Module.finite_of_fg_torsion`.
- Hypotheses: `z` integral over `ℤ`; `L` a normed field (algebra/ultrametric/complete omitted).
- Uses from project: []
- Used by: `exists_pow_sub_one_norm_le`
- Visibility: public
- Lines: 216-244 (proof ~24 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`. Hinges on `Module.finite_of_fg_torsion`, `IsIntegral.fg_adjoin_singleton`.

### theorem exists_pow_sub_one_norm_le
- Type: `{z : L} (hz : IsIntegral ℤ z) (hz1 : ‖z‖ = 1) : ∃ m : ℕ, 0 < m ∧ ‖z ^ m - 1‖ ≤ (p : ℝ)⁻¹`
- What: A norm-one element integral over `ℤ` has a positive power within `p⁻¹` of 1 (W6a-a5, pigeonhole).
- How: Let `R = ℤ[z]`, `I = (p)`; `R/I` finite by `finite_adjoin_int_quotient`. Pigeonhole `n ↦ z^n` into `R/I` via `Finite.exists_ne_map_eq_of_infinite`; WLOG `i<j`, set `m=j-i`. From equal images, `z^j - z^i ∈ (p)` so `= p·s`; push to `L`, bound `‖z^j-z^i‖ ≤ p⁻¹` (`norm_natCast_p`, `norm_le_one_of_mem_adjoin_int`); factor `z^j-z^i = z^i(z^(j-i)-1)` with `‖z^i‖=1`.
- Hypotheses: `z` integral over `ℤ`, `‖z‖ = 1`; `L` ultrametric normed `ℚ_[p]`-algebra (complete omitted).
- Uses from project: [finite_adjoin_int_quotient, norm_natCast_p, norm_le_one_of_mem_adjoin_int]
- Used by: `extLogDomain_of_integral_norm_one`
- Visibility: public
- Lines: 246-282 (proof ~31 lines)
- Notes: long(30-50). `omit [CompleteSpace L]`. Hinges on `Finite.exists_ne_map_eq_of_infinite` (pigeonhole), `Ideal.mem_span_singleton'`, `Ideal.Quotient.mk_eq_mk_iff_sub_mem`.

### def ExtLogDomain
- Type: `(x : L) : Prop := ∃ (m : ℕ) (k : ℤ) (y : L), 0 < m ∧ x ^ m = (p : L) ^ k * y ∧ InExpBall p (y - 1)`
- What: The domain of the extended logarithm — rational-valuation elements `x` such that `x^m = p^k·y` with `y` in the translated exponential ball.
- How: Definitional (existential predicate).
- Hypotheses: none beyond ambient `L`.
- Uses from project: [InExpBall]
- Used by: `extLog`, `extLog_eq_of_witness`, `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`, `extLog_prod`, `extLog_neg`, `extLogDomain_of_integral_norm_one`, `natCast_p_ne_zero` (no)
- Visibility: public
- Lines: 284-288 (def, no proof)
- Notes: none.

### def extLog
- Type: `(x : L) : L := if h : ExtLogDomain p x then ((h.choose : ℚ_[p]))⁻¹ • padicLog p h.choose_spec.choose_spec.choose else 0`
- What: The extended (Iwasawa-branch, `log_p p = 0`) logarithm, junk-total: `m⁻¹ • padicLog y` for a witness `x^m = p^k·y`, and `0` off the domain (W6a-a6).
- How: Definitional via `Classical`-choice dependent `if`, extracting witnesses `m` and `y` from the `ExtLogDomain` proof.
- Hypotheses: none (total via junk value 0).
- Uses from project: [ExtLogDomain, padicLog]
- Used by: `extLog_eq_of_witness`, and downstream `extLog_*` lemmas (via that)
- Visibility: public (noncomputable)
- Lines: 290-298 (def, no proof). `open Classical in`.
- Notes: none. noncomputable.

### theorem natCast_p_ne_zero
- Type: `(p : L) ≠ 0`
- What: The image of `p` in `L` is nonzero (its norm `p⁻¹ > 0`).
- How: `norm_ne_zero_iff` reduced to `‖(p:L)‖ ≠ 0`, computed by `norm_natCast_p` to `p⁻¹` which is positive.
- Hypotheses: `L` normed `ℚ_[p]`-algebra (ultrametric/complete omitted).
- Uses from project: [norm_natCast_p]
- Used by: `extLog_witness_smul_eq`, `extLog_mul`, `ExtLogDomain.mul`
- Visibility: public
- Lines: 300-304 (proof ~3 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem extLog_witness_smul_eq
- Type: `{x : L} {m m' : ℕ} {k k' : ℤ} {y y' : L} (hm : 0 < m) (hm' : 0 < m') (hxy : x ^ m = (p:L)^k * y) (hxy' : x ^ m' = (p:L)^k' * y') (hy : InExpBall p (y-1)) (hy' : InExpBall p (y'-1)) : ((m:ℚ_[p]))⁻¹ • padicLog p y = ((m':ℚ_[p]))⁻¹ • padicLog p y'`
- What: Two `extLog`-witnesses of the same element produce the same `ℚ_p`-scaled logarithm (well-definedness core).
- How: Raise both witnesses to `x^(m·m')`, equate the two `p^··y^·` forms; match `p`-valuations using `‖y‖=‖y'‖=1` (`norm_eq_one_of_inExpBall_sub_one`) and injectivity `zpow_right_injective₀` of `n ↦ (p⁻¹)^n` to force `k·m'=k'·m`, hence `y^m' = y'^m` (cancelling `p^·` via `natCast_p_ne_zero`); apply `padicLog_pow` to get `m'·log y = m·log y'`; finish with `ℚ_p`-scalar algebra (`inv_smul_eq_iff₀`, `smul_comm`).
- Hypotheses: two valid domain witnesses `(m,k,y)`, `(m',k',y')` for the same `x` with positive `m,m'`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [InExpBall, norm_eq_one_of_inExpBall_sub_one, natCast_p_ne_zero, padicLog_pow, norm_natCast_p]
- Used by: `extLog_eq_of_witness`
- Visibility: public
- Lines: 306-340 (proof ~29 lines)
- Notes: none (just under 30). Hinges on `zpow_right_injective₀`, `mul_left_cancel₀`.

### theorem extLog_eq_of_witness
- Type: `{x : L} {m : ℕ} {k : ℤ} {y : L} (hm : 0 < m) (hxy : x ^ m = (p:L)^k * y) (hy : InExpBall p (y-1)) : extLog p x = ((m:ℚ_[p]))⁻¹ • padicLog p y`
- What: Every witness computes `extLog` (W6a-a7, well-definedness statement).
- How: The witness gives `ExtLogDomain p x`; unfold `extLog` with `dif_pos`; the chosen witness and the given one are reconciled by `extLog_witness_smul_eq`.
- Hypotheses: a valid domain witness `(m,k,y)` for `x` with `m>0`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [InExpBall, ExtLogDomain, extLog, extLog_witness_smul_eq]
- Used by: `extLog_eq_padicLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`
- Visibility: public
- Lines: 342-349 (proof ~6 lines)
- Notes: none.

### theorem inExpBall_one_sub_one
- Type: `InExpBall p ((1 : L) - 1)`
- What: The centre `1` of the translated exponential ball is a member.
- How: `1-1=0`, `‖0‖^(p-1)=0` (since `p-1>0`), and `0 < p⁻¹`.
- Hypotheses: `L` a normed field (algebra/ultrametric/complete omitted).
- Uses from project: [InExpBall]
- Used by: `extLog_eq_padicLog` (no — via extLog_eq_of_witness path); `ExtLogDomain.prod`, `extLog_prod`, `extLog_eq_zero_of_pow_eq_one`, `extLog_neg`
- Visibility: public
- Lines: 351-356 (proof ~3 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem extLog_eq_padicLog
- Type: `{x : L} (hx : InExpBall p (x - 1)) : extLog p x = padicLog p x`
- What: `extLog` agrees with `padicLog` on the exponential ball (W6a-a8).
- How: Apply `extLog_eq_of_witness` with trivial witness `m=1, k=0, y=x` (`x^1 = p^0·x`), then `Nat.cast_one`, `inv_one`, `one_smul`.
- Hypotheses: `x-1` in exp ball; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [InExpBall, extLog, padicLog, extLog_eq_of_witness]
- Used by: `extLog_prod`
- Visibility: public
- Lines: 358-362 (proof ~2 lines)
- Notes: none.

### theorem extLog_mul
- Type: `{x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) : extLog p (x * y) = extLog p x + extLog p y`
- What: Additivity of `extLog` on the domain (W6a-a9).
- How: Extract witnesses `(m,k,a)`, `(m',k',b)`; build product witness `(x·y)^(m·m') = p^(k m'+k' m)·(a^m'·b^m)` (with `hball` via `mul_mem_expBall`/`pow_mem_expBall`); evaluate all three `extLog`s by `extLog_eq_of_witness`; expand `padicLog(a^m'·b^m)` via `padicLog_mul` and `padicLog_pow`; finish with `ℚ_p`-scalar algebra (`smul_add`, `smul_smul`, `mul_inv`, `field_simp`).
- Hypotheses: `x, y` in `ExtLogDomain`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [ExtLogDomain, extLog, mul_mem_expBall, pow_mem_expBall, extLog_eq_of_witness, padicLog_mul, padicLog_pow, natCast_p_ne_zero]
- Used by: `extLog_prod`, `extLog_neg`
- Visibility: public
- Lines: 364-389 (proof ~24 lines)
- Notes: none. Hinges on `zpow_add₀`, `padicLog_mul`.

### theorem ExtLogDomain.mul
- Type: `{x y : L} (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) : ExtLogDomain p (x * y)`
- What: The extended-log domain is closed under multiplication (the product witness of `extLog_mul`).
- How: Extract witnesses; provide product witness `(m·m', k m'+k' m, a^m'·b^m)` with ball-membership via `mul_mem_expBall`/`pow_mem_expBall`; verify the power identity by `zpow_add₀` and `ring`.
- Hypotheses: `x, y` in `ExtLogDomain`; `L` ultrametric normed `ℚ_[p]`-algebra (complete omitted).
- Uses from project: [ExtLogDomain, mul_mem_expBall, pow_mem_expBall, natCast_p_ne_zero]
- Used by: `ExtLogDomain.prod`, `extLog_prod`
- Visibility: public
- Lines: 391-404 (proof ~8 lines)
- Notes: none. `omit [CompleteSpace L]`.

### theorem ExtLogDomain.prod
- Type: `{ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, ExtLogDomain p (f i)) : ExtLogDomain p (∏ i ∈ s, f i)`
- What: The extended-log domain is closed under finite products.
- How: `Finset.induction`; empty case uses trivial witness `(1,0,1)` and `inExpBall_one_sub_one`; insert step uses `Finset.prod_insert` and `ExtLogDomain.mul`.
- Hypotheses: every `f i` (i∈s) in `ExtLogDomain`; `L` ultrametric normed `ℚ_[p]`-algebra (complete omitted).
- Uses from project: [ExtLogDomain, inExpBall_one_sub_one, ExtLogDomain.mul]
- Used by: `extLog_prod`
- Visibility: public
- Lines: 406-417 (proof ~7 lines)
- Notes: none. `omit [CompleteSpace L]`.

### theorem extLog_prod
- Type: `{ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, ExtLogDomain p (f i)) : extLog p (∏ i ∈ s, f i) = ∑ i ∈ s, extLog p (f i)`
- What: Additivity over a finite product of domain elements (W6a-a9 Finset form); drives the `μ_p`-collapse in the trace.
- How: `Finset.induction`; empty case via `extLog_eq_padicLog` of `1` and `padicLog_one`; insert step via `Finset.prod_insert`/`Finset.sum_insert`, `extLog_mul` (with `ExtLogDomain.prod` for the tail), and the IH.
- Hypotheses: every `f i` (i∈s) in `ExtLogDomain`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [ExtLogDomain, extLog, extLog_eq_padicLog, inExpBall_one_sub_one, padicLog_one, extLog_mul, ExtLogDomain.prod]
- Used by: unused in file
- Visibility: public
- Lines: 419-432 (proof ~6 lines)
- Notes: none.

### theorem extLog_eq_zero_of_pow_eq_one
- Type: `{x : L} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) : extLog p x = 0`
- What: Roots of unity have extended logarithm `0` (W6a-a10).
- How: `x^n = 1 = p^0·1` is a witness with `y=1`; `extLog_eq_of_witness` gives `n⁻¹ • padicLog 1`, and `padicLog_one`/`smul_zero` collapse to 0.
- Hypotheses: `x^n = 1` for some `n > 0`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [extLog, extLog_eq_of_witness, inExpBall_one_sub_one, padicLog_one]
- Used by: `extLog_neg`
- Visibility: public
- Lines: 434-438 (proof ~3 lines)
- Notes: none.

### theorem extLog_neg
- Type: `{x : L} (hx : ExtLogDomain p x) : extLog p (-x) = extLog p x`
- What: `log_p(x) = log_p(-x)` (W6a-a10 continued; RJW's final step, TeX 2150).
- How: `-1` lies in the domain (`(-1)^2 = 1 = p^0·1`); write `-x = (-1)·x`, apply `extLog_mul`, and `extLog(-1)=0` via `extLog_eq_zero_of_pow_eq_one` (using `neg_one_sq`).
- Hypotheses: `x` in `ExtLogDomain`; `L` complete ultrametric normed `ℚ_[p]`-algebra.
- Uses from project: [ExtLogDomain, extLog, inExpBall_one_sub_one, extLog_mul, extLog_eq_zero_of_pow_eq_one]
- Used by: unused in file
- Visibility: public
- Lines: 440-448 (proof ~5 lines)
- Notes: none.

### theorem extLogDomain_of_integral_norm_one
- Type: `{z : L} (hz : IsIntegral ℤ z) (hz1 : ‖z‖ = 1) : ExtLogDomain p z`
- What: Norm-one elements integral over `ℤ` lie in the extended-log domain (W6a-a11, the domain engine); covers all arguments `1 − ε_N^c` of RJW Thm 6.1(ii) for tame conductor `D > 1`.
- How: `exists_pow_sub_one_norm_le` gives `m>0` with `‖z^m-1‖ ≤ p⁻¹ < 1`; `exists_pPow_pow_inExpBall` then gives `j` with `(z^m)^(p^j)` in the exp ball; assemble witness `(m·p^j, 0, z^(m·p^j))`.
- Hypotheses: `z` integral over `ℤ`, `‖z‖ = 1`; `L` ultrametric normed `ℚ_[p]`-algebra (complete omitted).
- Uses from project: [ExtLogDomain, exists_pow_sub_one_norm_le, exists_pPow_pow_inExpBall]
- Used by: unused in file
- Visibility: public
- Lines: 450-463 (proof ~8 lines)
- Notes: none. `omit [CompleteSpace L]`.

---

## File Summary

- **Total declarations: 22** (defs: 2 [`ExtLogDomain`, `extLog`] / lemmas+theorems: 20 / instances: 0). No structures/classes/abbrevs/inductives.
- **Key API (used by ≥3 in-file):**
  - `norm_natCast_p` — used by 4 (`norm_pow_p_sub_one_le`, `exists_pow_sub_one_norm_le`, `extLog_witness_smul_eq`, `natCast_p_ne_zero`)
  - `mul_mem_expBall` — used by 4 (`pow_mem_expBall`, `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`)
  - `pow_mem_expBall` — used by 4 (`padicLog_pow`, `extLog_mul`, `ExtLogDomain.mul`, `ExtLogDomain.prod`)
  - `extLog_eq_of_witness` — used by 4 (`extLog_eq_padicLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`; plus `extLog_neg` indirectly)
  - `ExtLogDomain` (def) — used by ~8 downstream domain/additivity lemmas
  - `inExpBall_one_sub_one` — used by 4 (`ExtLogDomain.prod`, `extLog_prod`, `extLog_eq_zero_of_pow_eq_one`, `extLog_neg`)
  - `natCast_p_ne_zero` — used by 3 (`extLog_witness_smul_eq`, `extLog_mul`, `ExtLogDomain.mul`)
- **Unused in file (terminal API, expected to be consumed by other modules):** `extLog_prod`, `extLog_neg`, `extLogDomain_of_integral_norm_one` (the headline domain engine).
- **Declarations with `sorry`: none.**
- **`set_option`: none. TODO: none.**
- **Proofs > 50 lines (OVER-50): 1** — `exists_pPow_pow_inExpBall` (lines 133-188, ~52-line proof). Needs `/decompose-proof`.
- **Proofs 30-50 lines (long): 1** — `exists_pow_sub_one_norm_le` (lines 246-282, ~31-line proof). Two further proofs sit just under the threshold at ~27 and ~29 lines (`norm_pow_p_sub_one_le`, `extLog_witness_smul_eq`).

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_ExtLog.md`
