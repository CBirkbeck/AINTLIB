# Inventory: LutzNagell/DivisionPolynomial.lean

File-level notes: This is a copy of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, adapted to import the project's `LutzNagell.EllipticDivisibilitySequence` instead of the mathlib version (to avoid `normEDS`/`complEDS`/`preNormEDS` name conflicts). All declarations live in `namespace WeierstrassCurve`, over a `CommRing R` with `(W : WeierstrassCurve R)`. A `local macro "C_simp"` expands to a `simp only` over the ring-hom lemmas `[map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow]` (used in several proofs but is not a declaration). The functions `preNormEDS'`, `preNormEDS`, `normEDS`, and their `*_zero/one/two/three/four/even/odd/neg/ofNat` lemmas plus `map_preNormEDS'`, `map_preNormEDS`, `map_normEDS` are project EDS API from `LutzNagell.EllipticDivisibilitySequence`; they are imports, not declared here, so they are NOT listed under "Uses from project" (which tracks only decls declared in THIS file).

---

### def ψ₂
- Type: `noncomputable def ψ₂ : R[X][Y] := W.toAffine.polynomialY`
- What: The 2-division polynomial `ψ₂ = Ψ₂`, defined as the formal `Y`-partial-derivative `polynomialY` of the affine Weierstrass equation.
- How: Direct definition as `W.toAffine.polynomialY` (mathlib's `Affine.polynomialY`); no proof.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve over `R`.
- Uses from project: []
- Used by: `C_Ψ₂Sq`, `ψ₂_sq`, `Affine.CoordinateRing.mk_ψ₂_sq`, `Ψ` (and its `Ψ_two`/`Ψ_four`/`Ψ_even`/`Ψ_odd` lemmas), `ψ` (definition), `map_ψ₂`
- Visibility: public
- Lines: 35-37 (def, no proof)
- Notes: none

### def Ψ₂Sq
- Type: `noncomputable def Ψ₂Sq : R[X] := C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`
- What: The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`, given by the explicit cubic in the `b`-invariants `b₂, b₄, b₆`.
- How: Direct definition as an explicit polynomial; no proof.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve over `R`.
- Uses from project: []
- Used by: `C_Ψ₂Sq`, `ψ₂_sq`, `Affine.CoordinateRing.mk_ψ₂_sq`, `Ψ₂Sq_eq`, `preΨ'`, `preΨ`, `preΨ'_odd`, `preΨ_odd`, `ΨSq` (+ `ΨSq_two`/`ΨSq_four`/`ΨSq_even`/`ΨSq_odd`), `Φ` (+ `Φ_two`/`Φ_three`/`Φ_four`), `map_Ψ₂Sq`, `Ψ_odd`
- Visibility: public
- Lines: 39-41 (def, no proof)
- Notes: none

### lemma C_Ψ₂Sq
- Type: `C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial`
- What: States that the constant-embedded `Ψ₂Sq` equals `ψ₂²` minus four times the affine Weierstrass polynomial, i.e. `Ψ₂Sq` is congruent to `ψ₂²` modulo the curve equation.
- How: Unfold `Ψ₂Sq`, `ψ₂`, the invariants `b₂/b₄/b₆`, `Affine.polynomialY`, `Affine.polynomial`, push `C` through with the `C_simp` macro, then close by `ring1`.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: [`Ψ₂Sq`, `ψ₂`]
- Used by: `ψ₂_sq`, `Affine.CoordinateRing.mk_ψ₂_sq`, `Ψ_odd`
- Visibility: public
- Lines: 43-46 (proof 3 lines: `rw … / C_simp / ring1`)
- Notes: none

### lemma ψ₂_sq
- Type: `W.ψ₂ ^ 2 = C W.Ψ₂Sq + 4 * W.toAffine.polynomial`
- What: The rearranged form of `C_Ψ₂Sq`: `ψ₂²` equals `C Ψ₂Sq` plus four times the affine polynomial.
- How: `simp [C_Ψ₂Sq]` — rewrites by the previous lemma.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: [`ψ₂`, `Ψ₂Sq`, `C_Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 48-49 (proof 1 line)
- Notes: none

### lemma Affine.CoordinateRing.mk_ψ₂_sq
- Type: `mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq)`
- What: In the affine coordinate ring (image under `mk W`), the class of `ψ₂²` equals the class of `C Ψ₂Sq`; i.e. the congruence becomes an equality after quotienting by the curve ideal.
- How: `simp [C_Ψ₂Sq]` — the `4 * polynomial` term vanishes in the coordinate ring.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: [`ψ₂`, `Ψ₂Sq`, `C_Ψ₂Sq`]
- Used by: `Affine.CoordinateRing.mk_Ψ_sq`, `Affine.CoordinateRing.mk_ψ`
- Visibility: public (scoped in `Affine.CoordinateRing` namespace)
- Lines: 51-52 (proof 1 line)
- Notes: none

### lemma Ψ₂Sq_eq
- Type: `W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly`
- What: Identifies `Ψ₂Sq` with the `toPoly` of mathlib's existing `twoTorsionPolynomial`, recording that they are definitionally the same polynomial.
- How: `rfl` — definitional equality.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: [`Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 54-56 (proof 1 line `rfl`)
- Notes: carries a TODO comment "remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`"

### def Ψ₃
- Type: `noncomputable def Ψ₃ : R[X] := 3 * X ^ 4 + C W.b₂ * X ^ 3 + 3 * C W.b₄ * X ^ 2 + 3 * C W.b₆ * X + C W.b₈`
- What: The 3-division polynomial `ψ₃ = Ψ₃`, an explicit quartic in the `b`-invariants `b₂, b₄, b₆, b₈`.
- How: Direct definition; no proof.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: []
- Used by: `preΨ'`, `preΨ`, `preΨ'_three`, `preΨ_three`, `ΨSq_three`, `Ψ_three`, `Φ_two`, `Φ_three`, `Φ_four`, `ψ` (definition), `ψ_three`, `φ_two`, `φ_three`, `φ_four`, `map_Ψ₃`
- Visibility: public
- Lines: 64-66 (def, no proof)
- Notes: none

### def preΨ₄
- Type: `noncomputable def preΨ₄ : R[X]` — explicit degree-6 polynomial `2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + (b₂b₈−b₄b₆)X + (b₄b₈−b₆²)` (with `C`-embeddings)
- What: The auxiliary polynomial `preΨ₄` to the 4-division polynomial via `ψ₄ = Ψ₄ = preΨ₄·ψ₂`.
- How: Direct definition; no proof.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve.
- Uses from project: []
- Used by: `preΨ'`, `preΨ`, `preΨ'_four`, `preΨ_four`, `ΨSq_four`, `Ψ_four`, `Φ_three`, `Φ_four`, `ψ` (definition), `ψ_four`, `φ_three`, `φ_four`, `map_preΨ₄`
- Visibility: public
- Lines: 68-72 (def, no proof)
- Notes: none

### def preΨ'
- Type: `noncomputable def preΨ' (n : ℕ) : R[X] := preNormEDS' (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`
- What: The family `preΨₙ` for natural `n`, auxiliary univariate polynomials to the bivariate division polynomials `Ψₙ`, built as the project's normalised-EDS recurrence `preNormEDS'` seeded by `Ψ₂Sq²`, `Ψ₃`, `preΨ₄`.
- How: Direct definition in terms of `preNormEDS'`; no proof.
- Hypotheses: `R` a commutative ring; `W` a Weierstrass curve; `n : ℕ`.
- Uses from project: [`Ψ₂Sq`, `Ψ₃`, `preΨ₄`]
- Used by: `preΨ'_zero/one/two/three/four/even/odd`, `preΨ_ofNat`, `ΨSq_ofNat`, `Ψ_ofNat`, `Φ_ofNat`, `map_preΨ'`, `baseChange_preΨ'`
- Visibility: public
- Lines: 74-77 (def, no proof)
- Notes: none

### lemma preΨ'_zero
- Type: `@[simp] W.preΨ' 0 = 0`
- What: Base value: `preΨ'` at 0 is the zero polynomial.
- How: `preNormEDS'_zero ..` (EDS API lemma).
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ'`]
- Used by: unused in file
- Visibility: public
- Lines: 79-81 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ'_one
- Type: `@[simp] W.preΨ' 1 = 1`
- What: Base value: `preΨ'` at 1 is `1`.
- How: `preNormEDS'_one ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ'`]
- Used by: `Φ_two`
- Visibility: public
- Lines: 83-85 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ'_two
- Type: `@[simp] W.preΨ' 2 = 1`
- What: Base value: `preΨ'` at 2 is `1`.
- How: `preNormEDS'_two ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ'`]
- Used by: `Φ_two`, `Φ_four`
- Visibility: public
- Lines: 87-89 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ'_three
- Type: `@[simp] W.preΨ' 3 = W.Ψ₃`
- What: Base value: `preΨ'` at 3 equals `Ψ₃`.
- How: `preNormEDS'_three ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ'`, `Ψ₃`]
- Used by: `Φ_three`
- Visibility: public
- Lines: 91-93 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ'_four
- Type: `@[simp] W.preΨ' 4 = W.preΨ₄`
- What: Base value: `preΨ'` at 4 equals `preΨ₄`.
- How: `preNormEDS'_four ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ'`, `preΨ₄`]
- Used by: `Φ_three`, `Φ_four`
- Visibility: public
- Lines: 95-97 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ'_even
- Type: `W.preΨ' (2 * (m + 3)) = preΨ'(m+2)² · preΨ'(m+3) · preΨ'(m+5) − preΨ'(m+1) · preΨ'(m+3) · preΨ'(m+4)²`
- What: The even-index recurrence for `preΨ'` (the elliptic divisibility sequence even-step relation).
- How: `preNormEDS'_even ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℕ`.
- Uses from project: [`preΨ'`]
- Used by: unused in file
- Visibility: public
- Lines: 99-102 (proof 1 line)
- Notes: none

### lemma preΨ'_odd
- Type: `W.preΨ' (2*(m+2)+1) = preΨ'(m+4)·preΨ'(m+2)³·(if Even m then Ψ₂Sq² else 1) − preΨ'(m+1)·preΨ'(m+3)³·(if Even m then 1 else Ψ₂Sq²)`
- What: The odd-index recurrence for `preΨ'`, with a parity-dependent `Ψ₂Sq²` factor placement.
- How: `preNormEDS'_odd ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℕ`.
- Uses from project: [`preΨ'`, `Ψ₂Sq`]
- Used by: `Φ_four`
- Visibility: public
- Lines: 104-107 (proof 1 line)
- Notes: none

### def preΨ
- Type: `noncomputable def preΨ (n : ℤ) : R[X] := preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ n`
- What: The family `preΨₙ` extended to integer `n`, auxiliary to the bivariate `Ψₙ`, built from the integer EDS `preNormEDS` seeded by `Ψ₂Sq²`, `Ψ₃`, `preΨ₄`.
- How: Direct definition via `preNormEDS`; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`Ψ₂Sq`, `Ψ₃`, `preΨ₄`]
- Used by: `preΨ_ofNat/zero/one/two/three/four/neg/even/odd`, `ΨSq` (+ `ΨSq_even`/`ΨSq_odd`), `Ψ` (+ `Ψ_even`/`Ψ_odd`), `Φ`, `Affine.CoordinateRing.mk_ψ`, `map_preΨ`, `baseChange_preΨ`
- Visibility: public
- Lines: 115-118 (def, no proof)
- Notes: none

### lemma preΨ_ofNat
- Type: `@[simp] W.preΨ n = W.preΨ' n` (for `n : ℕ`)
- What: On natural-number arguments, the integer `preΨ` agrees with `preΨ'`.
- How: `preNormEDS_ofNat ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℕ`.
- Uses from project: [`preΨ`, `preΨ'`]
- Used by: `Φ_ofNat`
- Visibility: public
- Lines: 120-122 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_zero
- Type: `@[simp] W.preΨ 0 = 0`
- What: Base value: integer `preΨ` at 0 is 0.
- How: `preNormEDS_zero ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 124-126 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_one
- Type: `@[simp] W.preΨ 1 = 1`
- What: Base value: integer `preΨ` at 1 is 1.
- How: `preNormEDS_one ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 128-130 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_two
- Type: `@[simp] W.preΨ 2 = 1`
- What: Base value: integer `preΨ` at 2 is 1.
- How: `preNormEDS_two ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 132-134 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_three
- Type: `@[simp] W.preΨ 3 = W.Ψ₃`
- What: Base value: integer `preΨ` at 3 equals `Ψ₃`.
- How: `preNormEDS_three ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 136-138 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_four
- Type: `@[simp] W.preΨ 4 = W.preΨ₄`
- What: Base value: integer `preΨ` at 4 equals `preΨ₄`.
- How: `preNormEDS_four ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`preΨ`, `preΨ₄`]
- Used by: unused in file
- Visibility: public
- Lines: 140-142 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_neg
- Type: `@[simp] W.preΨ (-n) = -W.preΨ n` (for `n : ℤ`)
- What: `preΨ` is an odd function of its integer index (negation symmetry of the EDS).
- How: `preNormEDS_neg ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`preΨ`]
- Used by: `Ψ_neg`, `Φ_neg`
- Visibility: public
- Lines: 144-146 (proof 1 line)
- Notes: `@[simp]`

### lemma preΨ_even
- Type: `W.preΨ (2*m) = preΨ(m−1)²·preΨ m·preΨ(m+2) − preΨ(m−2)·preΨ m·preΨ(m+1)²` (for `m : ℤ`)
- What: The even-index recurrence for the integer-indexed `preΨ`.
- How: `preNormEDS_even ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`preΨ`]
- Used by: `ΨSq_even`, `Ψ_even`
- Visibility: public
- Lines: 148-151 (proof 1 line)
- Notes: none

### lemma preΨ_odd
- Type: `W.preΨ (2*m+1) = preΨ(m+2)·preΨ m³·(if Even m then Ψ₂Sq² else 1) − preΨ(m−1)·preΨ(m+1)³·(if Even m then 1 else Ψ₂Sq²)` (for `m : ℤ`)
- What: The odd-index recurrence for the integer-indexed `preΨ`, with parity-dependent `Ψ₂Sq²` factor.
- How: `preNormEDS_odd ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`preΨ`, `Ψ₂Sq`]
- Used by: `ΨSq_odd`, `Ψ_odd`
- Visibility: public
- Lines: 153-156 (proof 1 line)
- Notes: none

### def ΨSq
- Type: `noncomputable def ΨSq (n : ℤ) : R[X] := W.preΨ n ^ 2 * if Even n then W.Ψ₂Sq else 1`
- What: The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`, equal to `preΨ n²` times `Ψ₂Sq` when `n` is even and `1` when odd.
- How: Direct definition; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`preΨ`, `Ψ₂Sq`]
- Used by: `ΨSq_ofNat/zero/one/two/three/four/neg/even/odd`, `Φ`, `Affine.CoordinateRing.mk_Ψ_sq`, `map_ΨSq`, `baseChange_ΨSq`
- Visibility: public
- Lines: 164-166 (def, no proof)
- Notes: none

### lemma ΨSq_ofNat
- Type: `@[simp] W.ΨSq n = W.preΨ' n ^ 2 * if Even n then W.Ψ₂Sq else 1` (for `n : ℕ`)
- What: On natural `n`, `ΨSq` is expressed via `preΨ'` rather than `preΨ`.
- How: `simp [ΨSq]` (which unfolds and applies `preΨ_ofNat`).
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℕ`.
- Uses from project: [`ΨSq`, `preΨ'`, `Ψ₂Sq`]
- Used by: `Φ_ofNat`
- Visibility: public
- Lines: 168-170 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_zero
- Type: `@[simp] W.ΨSq 0 = 0`
- What: `ΨSq` at 0 is 0.
- How: `simp [ΨSq]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ΨSq`]
- Used by: unused in file
- Visibility: public
- Lines: 172-174 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_one
- Type: `@[simp] W.ΨSq 1 = 1`
- What: `ΨSq` at 1 is 1.
- How: `simp [ΨSq]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ΨSq`]
- Used by: unused in file
- Visibility: public
- Lines: 176-178 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_two
- Type: `@[simp] W.ΨSq 2 = W.Ψ₂Sq`
- What: `ΨSq` at 2 equals `Ψ₂Sq` (consistent with `ΨSq` being congruent to `ψ₂²`).
- How: `simp [ΨSq]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ΨSq`, `Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 180-182 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_three
- Type: `@[simp] W.ΨSq 3 = W.Ψ₃ ^ 2`
- What: `ΨSq` at 3 equals `Ψ₃²`.
- How: `simp [ΨSq, show ¬Even (3 : ℤ) by decide]` — supplies the oddness fact so the conditional resolves to the `1` branch.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ΨSq`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 184-186 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_four
- Type: `@[simp] W.ΨSq 4 = W.preΨ₄ ^ 2 * W.Ψ₂Sq`
- What: `ΨSq` at 4 equals `preΨ₄² · Ψ₂Sq`.
- How: `simp [ΨSq, show ¬Odd (4 : ℤ) by decide]` — supplies the evenness fact.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ΨSq`, `preΨ₄`, `Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 188-190 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_neg
- Type: `@[simp] W.ΨSq (-n) = W.ΨSq n` (for `n : ℤ`)
- What: `ΨSq` is an even function of its index (since it is congruent to `ψₙ²`).
- How: `simp [ΨSq]` (uses `preΨ_neg`, `even_neg`, `neg_sq`).
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`ΨSq`]
- Used by: `Φ_neg`
- Visibility: public
- Lines: 192-194 (proof 1 line)
- Notes: `@[simp]`

### lemma ΨSq_even
- Type: `W.ΨSq (2*m) = (preΨ(m−1)²·preΨ m·preΨ(m+2) − preΨ(m−2)·preΨ m·preΨ(m+1)²)² · W.Ψ₂Sq` (for `m : ℤ`)
- What: Even-index expansion of `ΨSq` in terms of `preΨ`, picking up the `Ψ₂Sq` even-factor.
- How: `rw [ΨSq, preΨ_even, if_pos <| even_two_mul m]` — unfold, substitute the even `preΨ` recurrence, resolve the even conditional.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`ΨSq`, `preΨ_even`, `preΨ`, `Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 196-199 (proof 1 line)
- Notes: none

### lemma ΨSq_odd
- Type: `W.ΨSq (2*m+1) = (preΨ(m+2)·preΨ m³·(if Even m then Ψ₂Sq² else 1) − preΨ(m−1)·preΨ(m+1)³·(if Even m then 1 else Ψ₂Sq²))²` (for `m : ℤ`)
- What: Odd-index expansion of `ΨSq` in terms of `preΨ`; odd index means the outer `Ψ₂Sq` factor is `1`.
- How: `rw [ΨSq, preΨ_odd, if_neg m.not_even_two_mul_add_one, mul_one]` — unfold, substitute the odd `preΨ` recurrence, resolve the odd conditional and drop `* 1`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`ΨSq`, `preΨ_odd`, `preΨ`, `Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 201-204 (proof 1 line)
- Notes: none

### def Ψ
- Type: `protected noncomputable def Ψ (n : ℤ) : R[X][Y] := C (W.preΨ n) * if Even n then W.ψ₂ else 1`
- What: The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`, given as `C(preΨ n)` times `ψ₂` (even `n`) or `1` (odd `n`).
- How: Direct definition; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`preΨ`, `ψ₂`]
- Used by: `Ψ_ofNat/zero/one/two/three/four/neg/even/odd`, `Affine.CoordinateRing.mk_Ψ_sq`, `Affine.CoordinateRing.mk_ψ`, `Affine.CoordinateRing.mk_φ`, `map_Ψ`, `baseChange_Ψ` (note: many later sections `open WeierstrassCurve (Ψ …)`)
- Visibility: public, `protected`
- Lines: 212-214 (def, no proof)
- Notes: none

### lemma Ψ_ofNat
- Type: `@[simp] W.Ψ n = C (W.preΨ' n) * if Even n then W.ψ₂ else 1` (for `n : ℕ`)
- What: On natural `n`, `Ψ` is expressed via `preΨ'`.
- How: `simp [Ψ]` (applies `preΨ_ofNat`).
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℕ`.
- Uses from project: [`Ψ`, `preΨ'`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 218-220 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_zero
- Type: `@[simp] W.Ψ 0 = 0`
- What: `Ψ` at 0 is 0.
- How: `simp [Ψ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 222-224 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_one
- Type: `@[simp] W.Ψ 1 = 1`
- What: `Ψ` at 1 is 1.
- How: `simp [Ψ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 226-228 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_two
- Type: `@[simp] W.Ψ 2 = W.ψ₂`
- What: `Ψ` at 2 equals `ψ₂`.
- How: `simp [Ψ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Ψ`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 230-232 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_three
- Type: `@[simp] W.Ψ 3 = C W.Ψ₃`
- What: `Ψ` at 3 equals `C Ψ₃`.
- How: `simp [Ψ, show ¬Even (3 : ℤ) by decide]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Ψ`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 234-236 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_four
- Type: `@[simp] W.Ψ 4 = C W.preΨ₄ * W.ψ₂`
- What: `Ψ` at 4 equals `C preΨ₄ · ψ₂`.
- How: `simp [Ψ, show ¬Odd (4 : ℤ) by decide]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Ψ`, `preΨ₄`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 238-240 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_neg
- Type: `@[simp] W.Ψ (-n) = -W.Ψ n` (for `n : ℤ`)
- What: `Ψ` is an odd function of its index.
- How: `simp_rw [Ψ, preΨ_neg, C_neg, neg_mul, even_neg]` — push negation through `preΨ` and the conditional.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`Ψ`, `preΨ_neg`, `preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 242-244 (proof 1 line)
- Notes: `@[simp]`

### lemma Ψ_even
- Type: `W.Ψ (2*m) * W.ψ₂ = W.Ψ (m−1)² · W.Ψ m · W.Ψ (m+2) − W.Ψ (m−2) · W.Ψ m · W.Ψ (m+1)²` (for `m : ℤ`)
- What: The even-index addition/recurrence relation for the bivariate `Ψₙ` (multiplied through by `ψ₂`).
- How: `simp_rw` unfolding `Ψ`, applying `preΨ_even`, resolving parities via `Int.even_add/even_sub/even_two/not_even_one`, then `split_ifs <;> C_simp <;> ring1` to discharge each parity branch by ring algebra.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`Ψ`, `preΨ_even`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 246-250 (proof ~5 lines: `simp_rw … / split_ifs <;> C_simp <;> ring1`)
- Notes: none

### lemma Ψ_odd
- Type: `W.Ψ (2*m+1) = W.Ψ(m+2)·W.Ψ m³ − W.Ψ(m−1)·W.Ψ(m+1)³ + W.toAffine.polynomial·(16·polynomial − 8·ψ₂²)·C(if Even m then preΨ(m+2)·preΨ m³ else −preΨ(m−1)·preΨ(m+1)³)` (for `m : ℤ`)
- What: The odd-index recurrence for the bivariate `Ψₙ`, with an explicit correction term involving the affine Weierstrass polynomial (so the identity holds in `R[X][Y]`, not just modulo the curve).
- How: `simp_rw` unfolding `Ψ`, applying `preΨ_odd`, resolving parities, then `split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1` — uses the congruence `C_Ψ₂Sq` to convert `Ψ₂Sq` into `ψ₂² − 4·polynomial` so `ring1` closes both branches.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`Ψ`, `preΨ_odd`, `C_Ψ₂Sq`, `preΨ`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 252-259 (proof ~3 lines: `simp_rw … / split_ifs <;> C_simp <;> rw [C_Ψ₂Sq] <;> ring1`)
- Notes: none

### lemma Affine.CoordinateRing.mk_Ψ_sq
- Type: `mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n)` (for `n : ℤ`)
- What: In the affine coordinate ring, the class of `Ψₙ²` equals the class of `C ΨSqₙ`; i.e. `ΨSq` represents `ψ²` after quotienting.
- How: `simp_rw` pushing `mk`/`C` through powers and conditionals, crucially using `mk_ψ₂_sq` to collapse `ψ₂²` in the coordinate ring (`map_mul, apply_ite, mul_pow, ite_pow, mk_ψ₂_sq, map_one, one_pow, map_pow`).
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`Ψ`, `ΨSq`, `Affine.CoordinateRing.mk_ψ₂_sq`]
- Used by: `Affine.CoordinateRing.mk_φ`
- Visibility: public (scoped in `Affine.CoordinateRing`)
- Lines: 261-263 (proof 1 `simp_rw`)
- Notes: none

### def Φ
- Type: `protected noncomputable def Φ (n : ℤ) : R[X] := X * W.ΨSq n - W.preΨ (n + 1) * W.preΨ (n - 1) * if Even n then 1 else W.Ψ₂Sq`
- What: The univariate polynomials `Φₙ` congruent to `φₙ` (the numerator of the `x`-coordinate of `n·P`), built from `ΨSq` and neighbouring `preΨ` values.
- How: Direct definition; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`ΨSq`, `preΨ`, `Ψ₂Sq`]
- Used by: `Φ_ofNat/zero/one/two/three/four/neg`, `Affine.CoordinateRing.mk_φ`, `map_Φ`, `baseChange_Φ` (later sections `open WeierstrassCurve (Φ …)`)
- Visibility: public, `protected`
- Lines: 271-273 (def, no proof)
- Notes: none

### lemma Φ_ofNat
- Type: `@[simp] W.Φ (n + 1) = X · preΨ'(n+1)²·(if Even n then 1 else Ψ₂Sq) − preΨ'(n+2)·preΨ' n·(if Even n then Ψ₂Sq else 1)` (for `n : ℕ`)
- What: A natural-number recurrence form of `Φ` at `n+1`, expressed via `preΨ'`, with the parity conditionals re-indexed by `Nat.even_add_one`.
- How: `rw [Φ, add_sub_cancel_right]`, `norm_cast`, then `simp_rw [ΨSq_ofNat, Nat.even_add_one, ite_not, ← mul_assoc, preΨ_ofNat]` to rewrite into `preΨ'` form and flip the parity conditions.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℕ`.
- Uses from project: [`Φ`, `ΨSq_ofNat`, `preΨ_ofNat`, `preΨ'`, `Ψ₂Sq`]
- Used by: `Φ_two`, `Φ_three`, `Φ_four`
- Visibility: public
- Lines: 277-283 (proof ~3 lines)
- Notes: `@[simp]`

### lemma Φ_zero
- Type: `@[simp] W.Φ 0 = 1`
- What: `Φ` at 0 is 1.
- How: `simp [Φ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Φ`]
- Used by: unused in file
- Visibility: public
- Lines: 285-287 (proof 1 line)
- Notes: `@[simp]`

### lemma Φ_one
- Type: `@[simp] W.Φ 1 = X`
- What: `Φ` at 1 is `X` (the `x`-coordinate numerator for `1·P` is `x`).
- How: `simp [Φ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Φ`]
- Used by: unused in file
- Visibility: public
- Lines: 289-291 (proof 1 line)
- Notes: `@[simp]`

### lemma Φ_two
- Type: `@[simp] W.Φ 2 = X ^ 4 - C W.b₄ * X ^ 2 - C (2 * W.b₆) * X - C W.b₈`
- What: Explicit closed form of `Φ` at 2 as a quartic in the `b`-invariants.
- How: `rw` rewriting `2` as `(1+1 : ℤ)`, applying `Φ_ofNat`, the base values `preΨ'_two/three/one`, oddness `if_neg Nat.not_even_one`, unfolding `Ψ₂Sq`/`Ψ₃`, then `C_simp` and `ring1`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Φ`, `Φ_ofNat`, `preΨ'_two`, `Ψ₂Sq`, `preΨ'_three`, `preΨ'_one`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 293-298 (proof ~4 lines)
- Notes: `@[simp]`

### lemma Φ_three
- Type: `@[simp] W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq`
- What: Explicit form of `Φ` at 3 in terms of `Ψ₃`, `preΨ₄`, `Ψ₂Sq`.
- How: `rw` rewriting `3` as `(2+1 : ℤ)`, applying `Φ_ofNat`, base values `preΨ'_three/four/two`, evenness facts `if_pos even_two`, `mul_one`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Φ`, `Φ_ofNat`, `preΨ'_three`, `preΨ'_four`, `preΨ'_two`, `Ψ₃`, `preΨ₄`, `Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 300-303 (proof ~2 lines)
- Notes: `@[simp]`

### lemma Φ_four
- Type: `@[simp] W.Φ 4 = X * W.preΨ₄ ^ 2 * W.Ψ₂Sq - W.Ψ₃ * (W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3)`
- What: Explicit form of `Φ` at 4 in terms of `preΨ₄`, `Ψ₂Sq`, `Ψ₃`.
- How: `rw` rewriting `4` as `(3+1 : ℤ)`, applying `Φ_ofNat`, parity `if_neg`, rewriting `3+2` as `2*2+1` to apply the odd recurrence `preΨ'_odd`, base values `preΨ'_four/two/one/three`, evenness `if_pos Even.zero`, then `ring1`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`Φ`, `Φ_ofNat`, `preΨ'_four`, `preΨ'_odd`, `preΨ'_two`, `preΨ'_one`, `preΨ'_three`, `preΨ₄`, `Ψ₂Sq`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 305-310 (proof ~5 lines)
- Notes: `@[simp]`

### lemma Φ_neg
- Type: `@[simp] W.Φ (-n) = W.Φ n` (for `n : ℤ`)
- What: `Φ` is an even function of its index (consistent with `n·P` and `(−n)·P` sharing an `x`-coordinate).
- How: `simp_rw [Φ, ΨSq_neg, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', preΨ_neg, neg_mul_neg, mul_comm <| W.preΨ <| n - 1, even_neg]` — uses evenness of `ΨSq`, oddness of `preΨ`, and a commutation of the two neighbouring `preΨ` factors.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`Φ`, `ΨSq_neg`, `preΨ_neg`, `preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 312-315 (proof 1 `simp_rw`)
- Notes: `@[simp]`

### def ψ
- Type: `protected noncomputable def ψ : ℤ → R[X][Y] := normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)`
- What: The bivariate `n`-division polynomials `ψₙ`, defined directly as the project's normalised EDS `normEDS` seeded by `ψ₂`, `C Ψ₃`, `C preΨ₄`.
- How: Direct definition via `normEDS`; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ₂`, `Ψ₃`, `preΨ₄`]
- Used by: `ψ_zero/one/two/three/four/neg/even/odd`, `Affine.CoordinateRing.mk_ψ`, `φ` (definition), `map_ψ`, `baseChange_ψ`
- Visibility: public, `protected`
- Lines: 323-325 (def, no proof)
- Notes: none

### lemma ψ_zero
- Type: `@[simp] W.ψ 0 = 0`
- What: `ψ` at 0 is 0.
- How: `normEDS_zero ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 329-331 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_one
- Type: `@[simp] W.ψ 1 = 1`
- What: `ψ` at 1 is 1.
- How: `normEDS_one ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 333-335 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_two
- Type: `@[simp] W.ψ 2 = W.ψ₂`
- What: `ψ` at 2 equals `ψ₂`.
- How: `normEDS_two ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 337-339 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_three
- Type: `@[simp] W.ψ 3 = C W.Ψ₃`
- What: `ψ` at 3 equals `C Ψ₃`.
- How: `normEDS_three ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ`, `Ψ₃`]
- Used by: `φ_four`
- Visibility: public
- Lines: 341-343 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_four
- Type: `@[simp] W.ψ 4 = C W.preΨ₄ * W.ψ₂`
- What: `ψ` at 4 equals `C preΨ₄ · ψ₂`.
- How: `normEDS_four ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`ψ`, `preΨ₄`, `ψ₂`]
- Used by: `φ_four`
- Visibility: public
- Lines: 345-347 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_neg
- Type: `@[simp] W.ψ (-n) = -W.ψ n` (for `n : ℤ`)
- What: `ψ` is an odd function of its index.
- How: `normEDS_neg ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`ψ`]
- Used by: `φ_neg`
- Visibility: public
- Lines: 349-351 (proof 1 line)
- Notes: `@[simp]`

### lemma ψ_even
- Type: `W.ψ (2*m) * W.ψ₂ = W.ψ(m−1)²·W.ψ m·W.ψ(m+2) − W.ψ(m−2)·W.ψ m·W.ψ(m+1)²` (for `m : ℤ`)
- What: The even-index recurrence for the bivariate division polynomials `ψₙ`.
- How: `normEDS_even ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`ψ`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 353-355 (proof 1 line)
- Notes: none

### lemma ψ_odd
- Type: `W.ψ (2*m+1) = W.ψ(m+2)·W.ψ m³ − W.ψ(m−1)·W.ψ(m+1)³` (for `m : ℤ`)
- What: The odd-index recurrence for the bivariate division polynomials `ψₙ`.
- How: `normEDS_odd ..`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `m : ℤ`.
- Uses from project: [`ψ`]
- Used by: `φ_four`
- Visibility: public
- Lines: 357-359 (proof 1 line)
- Notes: none

### lemma Affine.CoordinateRing.mk_ψ
- Type: `mk W (W.ψ n) = mk W (W.Ψ n)` (for `n : ℤ`)
- What: In the affine coordinate ring, the bivariate division polynomial `ψₙ` and its representative `Ψₙ` have the same class; i.e. `Ψ` is congruent to `ψ` modulo the curve.
- How: `simp_rw [ψ, normEDS, Ψ, preΨ, map_mul, map_preNormEDS, map_pow, ← mk_ψ₂_sq, ← pow_mul]` — unfold both as (pre)normEDS, push `mk` through, and use `mk_ψ₂_sq` to reconcile the `ψ₂` vs `Ψ₂Sq` seeds in the coordinate ring.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`ψ`, `Ψ`, `preΨ`, `Affine.CoordinateRing.mk_ψ₂_sq`]
- Used by: `Affine.CoordinateRing.mk_φ`
- Visibility: public (scoped in `Affine.CoordinateRing`)
- Lines: 361-362 (proof 1 `simp_rw`)
- Notes: none

### def φ
- Type: `protected noncomputable def φ (n : ℤ) : R[X][Y] := C X * (W.ψ n) ^ 2 - W.ψ (n + 1) * W.ψ (n - 1)`
- What: The bivariate polynomials `φₙ` (numerator of the `x`-coordinate of `n·P`), defined from the division polynomials `ψ` by `φₙ = x·ψₙ² − ψₙ₊₁·ψₙ₋₁`.
- How: Direct definition; no proof.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`ψ`]
- Used by: `φ_zero/one/two/three/four/neg`, `Affine.CoordinateRing.mk_φ`, `map_φ`, `baseChange_φ`
- Visibility: public, `protected`
- Lines: 370-372 (def, no proof)
- Notes: none

### lemma φ_zero
- Type: `@[simp] W.φ 0 = 1`
- What: `φ` at 0 is 1.
- How: `simp [φ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`φ`]
- Used by: unused in file
- Visibility: public
- Lines: 376-378 (proof 1 line)
- Notes: `@[simp]`

### lemma φ_one
- Type: `@[simp] W.φ 1 = C X`
- What: `φ` at 1 is `C X`.
- How: `simp [φ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`φ`]
- Used by: unused in file
- Visibility: public
- Lines: 380-382 (proof 1 line)
- Notes: `@[simp]`

### lemma φ_two
- Type: `@[simp] W.φ 2 = C X * W.ψ₂ ^ 2 - C W.Ψ₃`
- What: Explicit form of `φ` at 2.
- How: `simp [φ]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`φ`, `ψ₂`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 384-386 (proof 1 line)
- Notes: `@[simp]`

### lemma φ_three
- Type: `@[simp] W.φ 3 = C X * C W.Ψ₃ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 2`
- What: Explicit form of `φ` at 3.
- How: `simp [φ, mul_assoc, sq]`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`φ`, `Ψ₃`, `preΨ₄`, `ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 388-390 (proof 1 line)
- Notes: `@[simp]`

### lemma φ_four
- Type: `@[simp] W.φ 4 = C X * C W.preΨ₄ ^ 2 * W.ψ₂ ^ 2 - C W.preΨ₄ * W.ψ₂ ^ 4 * C W.Ψ₃ + C W.Ψ₃ ^ 4`
- What: Explicit form of `φ` at 4.
- How: `rw [φ, ψ_four, …]` rewriting `4+1` as `2*2+1` to apply `ψ_odd`, then the base values `ψ_four/two/one/three` at the reduced indices, finishing with `ring1`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve.
- Uses from project: [`φ`, `ψ_four`, `ψ_odd`, `ψ_two`, `ψ_one`, `ψ_three`, `preΨ₄`, `ψ₂`, `Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 392-398 (proof ~4 lines)
- Notes: `@[simp]`

### lemma φ_neg
- Type: `@[simp] W.φ (-n) = W.φ n` (for `n : ℤ`)
- What: `φ` is an even function of its index (consistent with `n·P` and `(−n)·P` sharing an `x`-coordinate).
- How: `simp_rw [φ, ψ_neg, neg_sq, ← sub_neg_eq_add, ← neg_sub', sub_neg_eq_add, ← neg_add', ψ_neg, neg_mul_neg, mul_comm <| W.ψ <| n - 1]` — uses oddness of `ψ` and commutes the neighbouring `ψ` factors.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`φ`, `ψ_neg`, `ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 400-403 (proof 1 `simp_rw`)
- Notes: `@[simp]`

### lemma Affine.CoordinateRing.mk_φ
- Type: `mk W (W.φ n) = mk W (C <| W.Φ n)` (for `n : ℤ`)
- What: In the affine coordinate ring, the bivariate `φₙ` and its univariate representative `Φₙ` have the same class; i.e. `Φ` is congruent to `φ` modulo the curve.
- How: `simp_rw` unfolding `φ` and `Φ`, pushing `mk` through, applying `mk_ψ` (ψ↔Ψ) and `mk_Ψ_sq` (Ψ²↔ΨSq) plus `mk_ψ₂_sq`, and reconciling parity conditionals via `Int.even_add_one`/`Int.even_sub_one`/`ite_not` and `apply_ite`.
- Hypotheses: `R` comm ring; `W` Weierstrass curve; `n : ℤ`.
- Uses from project: [`φ`, `Φ`, `Affine.CoordinateRing.mk_ψ`, `Affine.CoordinateRing.mk_Ψ_sq`, `Ψ`, `Affine.CoordinateRing.mk_ψ₂_sq`]
- Used by: unused in file
- Visibility: public (scoped in `Affine.CoordinateRing`)
- Lines: 405-408 (proof 1 `simp_rw`)
- Notes: none

### lemma map_ψ₂
- Type: `@[simp] (W.map f).ψ₂ = W.ψ₂.map (mapRingHom f)` (for `f : R →+* S`)
- What: `ψ₂` commutes with mapping the curve along a ring homomorphism `f`.
- How: `simp_rw [ψ₂, Affine.map_polynomialY]`.
- Hypotheses: `R, S` comm rings; `W` Weierstrass curve over `R`; `f : R →+* S`.
- Uses from project: [`ψ₂`]
- Used by: `map_Ψ`, `map_ψ`, `baseChange_ψ₂`
- Visibility: public
- Lines: 420-422 (proof 1 line)
- Notes: `@[simp]`

### lemma map_Ψ₂Sq
- Type: `@[simp] (W.map f).Ψ₂Sq = W.Ψ₂Sq.map f`
- What: `Ψ₂Sq` commutes with mapping along `f`.
- How: `simp [Ψ₂Sq, map_ofNat]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`.
- Uses from project: [`Ψ₂Sq`]
- Used by: `map_preΨ'`, `map_preΨ`, `map_ΨSq`, `map_Φ`, `baseChange_Ψ₂Sq`
- Visibility: public
- Lines: 424-426 (proof 1 line)
- Notes: `@[simp]`

### lemma map_Ψ₃
- Type: `@[simp] (W.map f).Ψ₃ = W.Ψ₃.map f`
- What: `Ψ₃` commutes with mapping along `f`.
- How: `simp [Ψ₃]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`.
- Uses from project: [`Ψ₃`]
- Used by: `map_preΨ'`, `map_preΨ`, `map_ψ`, `baseChange_Ψ₃`
- Visibility: public
- Lines: 428-430 (proof 1 line)
- Notes: `@[simp]`

### lemma map_preΨ₄
- Type: `@[simp] (W.map f).preΨ₄ = W.preΨ₄.map f`
- What: `preΨ₄` commutes with mapping along `f`.
- How: `simp [preΨ₄]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`.
- Uses from project: [`preΨ₄`]
- Used by: `map_preΨ'`, `map_preΨ`, `map_ψ`, `baseChange_preΨ₄`
- Visibility: public
- Lines: 432-434 (proof 1 line)
- Notes: `@[simp]`

### lemma map_preΨ'
- Type: `@[simp] (W.map f).preΨ' n = (W.preΨ' n).map f` (for `n : ℕ`)
- What: `preΨ'` commutes with mapping along `f`.
- How: Two-stage `simp only`: first `[preΨ', map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_preNormEDS']` to move the map inside the EDS, then `[map_pow, coe_mapRingHom]` to clean up.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℕ`.
- Uses from project: [`preΨ'`, `map_Ψ₂Sq`, `map_Ψ₃`, `map_preΨ₄`]
- Used by: `baseChange_preΨ'`
- Visibility: public
- Lines: 436-439 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_preΨ
- Type: `@[simp] (W.map f).preΨ n = (W.preΨ n).map f` (for `n : ℤ`)
- What: `preΨ` commutes with mapping along `f`.
- How: Two-stage `simp only`: `[preΨ, map_Ψ₂Sq, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_preNormEDS]` then `[map_pow, coe_mapRingHom]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`preΨ`, `map_Ψ₂Sq`, `map_Ψ₃`, `map_preΨ₄`]
- Used by: `map_ΨSq`, `map_Ψ`, `map_Φ`, `baseChange_preΨ`
- Visibility: public
- Lines: 441-444 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_ΨSq
- Type: `@[simp] (W.map f).ΨSq n = (W.ΨSq n).map f` (for `n : ℤ`)
- What: `ΨSq` commutes with mapping along `f`.
- How: Two-stage `simp only`: `[ΨSq, map_preΨ, map_Ψ₂Sq, ← coe_mapRingHom]` then `[map_pow, map_mul, map_one, apply_ite <| mapRingHom f, coe_mapRingHom]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`ΨSq`, `map_preΨ`, `map_Ψ₂Sq`]
- Used by: `map_Φ`, `baseChange_ΨSq`
- Visibility: public
- Lines: 446-449 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_Ψ
- Type: `@[simp] (W.map f).Ψ n = (W.Ψ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `Ψ` commutes with mapping along `f`.
- How: Two-stage `simp only`: `[Ψ, map_preΨ, map_ψ₂, ← coe_mapRingHom]` then `[map_mul, map_one, map_C, apply_ite <| mapRingHom _, coe_mapRingHom]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`Ψ`, `map_preΨ`, `map_ψ₂`]
- Used by: `baseChange_Ψ`
- Visibility: public
- Lines: 451-454 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_Φ
- Type: `@[simp] (W.map f).Φ n = (W.Φ n).map f` (for `n : ℤ`)
- What: `Φ` commutes with mapping along `f`.
- How: Two-stage `simp only`: `[Φ, map_ΨSq, map_preΨ, map_Ψ₂Sq]` then `[Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_X, apply_ite (Polynomial.map f)]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`Φ`, `map_ΨSq`, `map_preΨ`, `map_Ψ₂Sq`]
- Used by: `baseChange_Φ`
- Visibility: public
- Lines: 456-460 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_ψ
- Type: `@[simp] (W.map f).ψ n = (W.ψ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `ψ` commutes with mapping along `f`.
- How: Two-stage `simp only`: `[ψ, map_ψ₂, map_Ψ₃, map_preΨ₄, ← coe_mapRingHom, map_normEDS]` then `[map_C, coe_mapRingHom]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`ψ`, `map_ψ₂`, `map_Ψ₃`, `map_preΨ₄`]
- Used by: `map_φ`, `baseChange_ψ`
- Visibility: public
- Lines: 462-465 (proof ~2 lines)
- Notes: `@[simp]`

### lemma map_φ
- Type: `@[simp] (W.map f).φ n = (W.φ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `φ` commutes with mapping along `f`.
- How: `unfold φ`, rewrite the three `ψ` occurrences with `map_ψ` (`rw [map_ψ, map_ψ, map_ψ]`), then `simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, coe_mapRingHom]`.
- Hypotheses: `R, S` comm rings; `W` over `R`; `f : R →+* S`; `n : ℤ`.
- Uses from project: [`φ`, `map_ψ`]
- Used by: `baseChange_φ`
- Visibility: public
- Lines: 467-472 (proof ~3 lines)
- Notes: `@[simp]`

### lemma baseChange_ψ₂
- Type: `(W.baseChange B).ψ₂ = (W.baseChange A).ψ₂.map (mapRingHom f)` (for `f : A →ₐ[S] B`)
- What: `ψ₂` is compatible with base change along an `S`-algebra homomorphism `f : A →ₐ[S] B`.
- How: `rw [← map_ψ₂, map_baseChange]` — reduce to the ring-hom map lemma and the curve `map_baseChange` compatibility.
- Hypotheses: `R, S` comm rings, `[Algebra R S]`; `A, B` comm `R`- and `S`-algebras with scalar-tower; `f : A →ₐ[S] B`.
- Uses from project: [`ψ₂`, `map_ψ₂`]
- Used by: unused in file
- Visibility: public
- Lines: 483-484 (proof 1 line)
- Notes: none

### lemma baseChange_Ψ₂Sq
- Type: `(W.baseChange B).Ψ₂Sq = (W.baseChange A).Ψ₂Sq.map f`
- What: `Ψ₂Sq` is compatible with base change along `f`.
- How: `rw [← map_Ψ₂Sq, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`.
- Uses from project: [`Ψ₂Sq`, `map_Ψ₂Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 486-487 (proof 1 line)
- Notes: none

### lemma baseChange_Ψ₃
- Type: `(W.baseChange B).Ψ₃ = (W.baseChange A).Ψ₃.map f`
- What: `Ψ₃` is compatible with base change along `f`.
- How: `rw [← map_Ψ₃, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`.
- Uses from project: [`Ψ₃`, `map_Ψ₃`]
- Used by: unused in file
- Visibility: public
- Lines: 489-490 (proof 1 line)
- Notes: none

### lemma baseChange_preΨ₄
- Type: `(W.baseChange B).preΨ₄ = (W.baseChange A).preΨ₄.map f`
- What: `preΨ₄` is compatible with base change along `f`.
- How: `rw [← map_preΨ₄, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`.
- Uses from project: [`preΨ₄`, `map_preΨ₄`]
- Used by: unused in file
- Visibility: public
- Lines: 492-493 (proof 1 line)
- Notes: none

### lemma baseChange_preΨ'
- Type: `(W.baseChange B).preΨ' n = ((W.baseChange A).preΨ' n).map f` (for `n : ℕ`)
- What: `preΨ'` is compatible with base change along `f`.
- How: `rw [← map_preΨ', map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℕ`.
- Uses from project: [`preΨ'`, `map_preΨ'`]
- Used by: unused in file
- Visibility: public
- Lines: 495-496 (proof 1 line)
- Notes: none

### lemma baseChange_preΨ
- Type: `(W.baseChange B).preΨ n = ((W.baseChange A).preΨ n).map f` (for `n : ℤ`)
- What: `preΨ` is compatible with base change along `f`.
- How: `rw [← map_preΨ, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`preΨ`, `map_preΨ`]
- Used by: unused in file
- Visibility: public
- Lines: 498-499 (proof 1 line)
- Notes: none

### lemma baseChange_ΨSq
- Type: `(W.baseChange B).ΨSq n = ((W.baseChange A).ΨSq n).map f` (for `n : ℤ`)
- What: `ΨSq` is compatible with base change along `f`.
- How: `rw [← map_ΨSq, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`ΨSq`, `map_ΨSq`]
- Used by: unused in file
- Visibility: public
- Lines: 501-502 (proof 1 line)
- Notes: none

### lemma baseChange_Ψ
- Type: `(W.baseChange B).Ψ n = ((W.baseChange A).Ψ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `Ψ` is compatible with base change along `f`.
- How: `rw [← map_Ψ, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`Ψ`, `map_Ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 504-505 (proof 1 line)
- Notes: none

### lemma baseChange_Φ
- Type: `(W.baseChange B).Φ n = ((W.baseChange A).Φ n).map f` (for `n : ℤ`)
- What: `Φ` is compatible with base change along `f`.
- How: `rw [← map_Φ, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`Φ`, `map_Φ`]
- Used by: unused in file
- Visibility: public
- Lines: 507-508 (proof 1 line)
- Notes: none

### lemma baseChange_ψ
- Type: `(W.baseChange B).ψ n = ((W.baseChange A).ψ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `ψ` is compatible with base change along `f`.
- How: `rw [← map_ψ, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`ψ`, `map_ψ`]
- Used by: unused in file
- Visibility: public
- Lines: 510-511 (proof 1 line)
- Notes: none

### lemma baseChange_φ
- Type: `(W.baseChange B).φ n = ((W.baseChange A).φ n).map (mapRingHom f)` (for `n : ℤ`)
- What: `φ` is compatible with base change along `f`.
- How: `rw [← map_φ, map_baseChange]`.
- Hypotheses: as for `baseChange_ψ₂`; `n : ℤ`.
- Uses from project: [`φ`, `map_φ`]
- Used by: unused in file
- Visibility: public
- Lines: 513-514 (proof 1 line)
- Notes: none

---

## File Summary

**Total declarations documented: 80**
- Defs: 11 (`ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ'`, `preΨ`, `ΨSq`, `Ψ`, `Φ`, `ψ`, `φ`)
- Lemmas/theorems: 69
- Instances: 0 (also: 0 structures, classes, abbrevs, inductives)

**Key API (used by ≥3 in-file decls):**
- `ψ₂` (def) — used by ~9 decls (`C_Ψ₂Sq`, `ψ₂_sq`, `mk_ψ₂_sq`, `Ψ`, `ψ`, `Ψ_two/four/even/odd`, `map_ψ₂`, …)
- `Ψ₂Sq` (def) — used by ~16 decls
- `Ψ₃` (def) — used by ~15 decls
- `preΨ₄` (def) — used by ~13 decls
- `preΨ'` (def) — used by ~13 decls
- `preΨ` (def) — used by ~14 decls
- `ΨSq` (def) — used by ~10 decls
- `Ψ` (def) — used by ~8 decls
- `Φ` (def) — used by ~8 decls
- `ψ` (def) — used by ~9 decls
- `φ` (def) — used by ~7 decls
- `Affine.CoordinateRing.mk_ψ₂_sq` — used by 3 (`mk_Ψ_sq`, `mk_ψ`, `mk_φ`)
- `Φ_ofNat` — used by 3 (`Φ_two`, `Φ_three`, `Φ_four`)
- `map_Ψ₂Sq` — used by 5 (`map_preΨ'`, `map_preΨ`, `map_ΨSq`, `map_Φ`, `baseChange_Ψ₂Sq`)
- `map_preΨ` — used by 4; `map_Ψ₃`, `map_preΨ₄`, `map_ψ₂` — used by 3-4 each (map + baseChange consumers)
- `preΨ_even`, `preΨ_odd` — used by 2-3 each (the `ΨSq`/`Ψ` even/odd lemmas)

**Unused decls (within this file — most are public terminal API, e.g. base-value/recurrence/map/baseChange lemmas consumed by OTHER files):** `ψ₂_sq`, `Ψ₂Sq_eq`, `preΨ'_zero`, `preΨ'_even`, `preΨ_zero/one/two/three/four`, `ΨSq_zero/one/two/three/four`, `ΨSq_even`, `ΨSq_odd`, `Ψ_ofNat/zero/one/two/three/four/neg/even/odd`, `Φ_zero/one/two/three/four/neg`, `ψ_zero/one/two/even`, `φ_zero/one/two/three/four/neg`, `mk_φ`, and ALL 11 `baseChange_*` lemmas. (Note: "unused in file" ≠ dead — this is a library API surface; the `baseChange_*` block and base-value/`map_*`/`mk_*` lemmas are downstream-facing.)

**Decls with `sorry`: none.**

**Decls with `set_option`: none.**

**Proofs > 50 lines (OVER-50): none.** (0 declarations)

**Proofs 30-50 lines long(30-50): none.** (0 declarations)

**Other flags:** `Ψ₂Sq_eq` carries a TODO ("remove `twoTorsionPolynomial` in favour of `Ψ₂Sq`"). No `sorry`/`admit`/`set_option` anywhere. Longest proofs are `Ψ_even` (~5 lines), `Φ_four`/`Φ_two`/`φ_four` (~4-5 lines each) — all well under the 30-line threshold; this file is a port of mathlib's `DivisionPolynomial.Basic` and is uniformly short-proof (one-liner EDS-API delegations, `simp`/`rw`+`ring1`, and two-stage `simp only` for the map lemmas).
