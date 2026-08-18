# Inventory: PadicLFunctions/Interpolation/Branches.lean

Branches of the Kubota–Leopoldt p-adic L-function (RJW §5.3, TeX 1885–1979): Teichmüller character ω, the angle bracket ⟨·⟩, the one-unit power y^s, the branch character ω(x)^i⟨x⟩^s, the branch ζ_{p,i}, and the interpolation theorem.

---

### def maximalIdealQuotientEquivZMod
- Type: `noncomputable def maximalIdealQuotientEquivZMod : ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+* ZMod p`
- What: The ring isomorphism between the residue ring of ℤ_[p] (raw quotient by the maximal ideal) and ZMod p.
- How: Definitionally mathlib's `PadicInt.residueField`, restated on the raw quotient to dodge typeclass friction through the `IsLocalRing.ResidueField` wrapper.
- Hypotheses: p prime (Fact).
- Uses from project: []
- Used by: the two anonymous instances below, `teichmullerZMod`, `toZMod_teichmullerZMod`
- Visibility: public
- Lines: 45–47 (proof: 1 line)
- Notes: none

### instance (CharP)
- Type: `instance : CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p`
- What: The residue ring of ℤ_[p] has characteristic p.
- How: `charP_of_injective_ringHom` transported along the injective inverse of `maximalIdealQuotientEquivZMod`.
- Hypotheses: p prime.
- Uses from project: [maximalIdealQuotientEquivZMod]
- Used by: unused in file (instance, found by typeclass search)
- Visibility: public (instance)
- Lines: 49–51 (proof: 2 lines)
- Notes: none

### instance (Finite)
- Type: `instance : Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p])`
- What: The residue ring of ℤ_[p] is finite.
- How: `Finite.of_equiv` from the (finite) ZMod p via `maximalIdealQuotientEquivZMod`.
- Hypotheses: p prime.
- Uses from project: [maximalIdealQuotientEquivZMod]
- Used by: unused in file (instance)
- Visibility: public (instance)
- Lines: 53–54 (proof: 1 line)
- Notes: none

### def teichmullerZMod
- Type: `noncomputable def teichmullerZMod : ZMod p →*₀ ℤ_[p]`
- What: The Teichmüller map sending a nonzero residue a ∈ ZMod p to the unique (p−1)-th root of unity in ℤ_[p] reducing to a, and 0 to 0 (L5.3.1 residue form).
- How: Built from mathlib's `Perfection.teichmuller₀` (adic limit of p^n-th powers) composed through `PerfectionMap.id` and `maximalIdealQuotientEquivZMod` to identify ZMod p with the residue field.
- Hypotheses: p prime.
- Uses from project: [maximalIdealQuotientEquivZMod]
- Used by: `toZMod_teichmullerZMod`, `teichmullerZMod_pow_card_sub_one`, `exists_primitiveRoot_card_sub_one`, `teichmullerFun`, `teichmullerChar`, `teichmullerChar_apply`, `isLocallyConstant_teichmullerFun`
- Visibility: public
- Lines: 62–66 (proof: defn, 5 lines)
- Notes: none

### lemma toZMod_teichmullerZMod
- Type: `@[simp] lemma toZMod_teichmullerZMod (a : ZMod p) : toZMod (teichmullerZMod p a) = a`
- What: The Teichmüller lift is a section of reduction mod p: ω(a) ≡ a (mod p).
- How: Unfolds through the perfection construction; rewrites `toZMod` as `residueField ∘ residue`, then uses `Perfection.mk_teichmuller₀` and `PerfectionMap.comp_equiv`, finishing with the apply-symm-apply of the equiv.
- Hypotheses: p prime; a a residue.
- Uses from project: [teichmullerZMod, maximalIdealQuotientEquivZMod]
- Used by: `exists_primitiveRoot_card_sub_one`, `teichmullerFun_sub_self_mem`, `teichmullerFun_eq_of_sub_mem`, `castHom_toZModPow_eq_toZMod` (indirectly)
- Visibility: public (simp)
- Lines: 70–78 (proof: 9 lines)
- Notes: none

### lemma teichmullerZMod_pow_card_sub_one
- Type: `lemma teichmullerZMod_pow_card_sub_one {a : ZMod p} (ha : a ≠ 0) : teichmullerZMod p a ^ (p - 1) = 1`
- What: For nonzero a, the Teichmüller lift satisfies ω(a)^(p−1) = 1.
- How: Pull the power inside the multiplicative-with-zero hom (`map_pow`) and apply Fermat `ZMod.pow_card_sub_one_eq_one`, then `map_one`.
- Hypotheses: p prime; a ≠ 0.
- Uses from project: [teichmullerZMod]
- Used by: `exists_primitiveRoot_card_sub_one`, `teichmullerFun_pow_card_sub_one`
- Visibility: public
- Lines: 80–82 (proof: 2 lines)
- Notes: none

### theorem exists_primitiveRoot_card_sub_one
- Type: `theorem exists_primitiveRoot_card_sub_one : ∃ ζ : ℤ_[p], IsPrimitiveRoot ζ (p - 1)`
- What: ℤ_[p] contains a primitive (p−1)-th root of unity (the prime-to-p roots needed for character orthogonality in §5.2 determinacy).
- How: Take a generator g of the cyclic group (ZMod p)ˣ; its order is p−1 by `ZMod.card_units_eq_totient`/`Nat.totient_prime`; the Teichmüller lift of g is the root — primitivity by transporting `g^l = 1` from ℤ_[p] back to (ZMod p)ˣ via `toZMod_teichmullerZMod` and using `orderOf_dvd_of_pow_eq_one`.
- Hypotheses: p prime.
- Uses from project: [teichmullerZMod, teichmullerZMod_pow_card_sub_one, toZMod_teichmullerZMod]
- Used by: unused in file
- Visibility: public
- Lines: 87–102 (proof: 16 lines)
- Notes: none

### def teichmullerFun
- Type: `noncomputable def teichmullerFun (x : ℤ_[p]) : ℤ_[p] := teichmullerZMod p (toZMod x)`
- What: The Teichmüller lift ω(x) ∈ ℤ_[p] of the reduction of x mod p (L5.3.1, RJW Def 5.15); equals lim_n x^{p^n}.
- How: Definition: `teichmullerZMod` of `toZMod x`.
- Hypotheses: p prime.
- Uses from project: [teichmullerZMod]
- Used by: `teichmullerFun_pow_card_sub_one`, `teichmullerFun_sub_self_mem`, `teichmullerFun_mul`, `teichmullerFun_eq_of_sub_mem`, `isUnit_teichmullerFun`, `teichmuller` (via lemmas), `teichmuller_coe`, `teichmullerChar_toZMod`, `angleUnit_sub_one_mem`, `continuous_angleUnit_val`, `branchChar`
- Visibility: public
- Lines: 107 (proof: defn, 1 line)
- Notes: none

### lemma teichmullerFun_pow_card_sub_one
- Type: `@[simp] lemma teichmullerFun_pow_card_sub_one (x : ℤ_[p]ˣ) : teichmullerFun p (x : ℤ_[p]) ^ (p - 1) = 1`
- What: For a unit x, ω(x)^(p−1) = 1.
- How: Reduce to `teichmullerZMod_pow_card_sub_one` using that the image of a unit under `toZMod` is nonzero (`x.isUnit.map toZMod`).
- Hypotheses: p prime; x a unit.
- Uses from project: [teichmullerFun, teichmullerZMod_pow_card_sub_one]
- Used by: `isUnit_teichmullerFun`, `branchChar_natCast`
- Visibility: public (simp)
- Lines: 110–112 (proof: 2 lines)
- Notes: none

### lemma teichmullerFun_sub_self_mem
- Type: `lemma teichmullerFun_sub_self_mem (x : ℤ_[p]) : teichmullerFun p x - x ∈ Ideal.span {(p : ℤ_[p])}`
- What: ω(x) − x lies in pℤ_p (the lift is congruent to x mod p).
- How: Rewrite span as `ker toZMod` via `maximalIdeal_eq_span_p`/`ker_toZMod`; then `map_sub`, `toZMod_teichmullerZMod`, `sub_self`.
- Hypotheses: p prime.
- Uses from project: [teichmullerFun, toZMod_teichmullerZMod (via simp lemma)]
- Used by: `angleUnit_sub_one_mem`
- Visibility: public
- Lines: 114–117 (proof: 3 lines)
- Notes: none

### lemma teichmullerFun_mul
- Type: `lemma teichmullerFun_mul (x y : ℤ_[p]) : teichmullerFun p (x * y) = teichmullerFun p x * teichmullerFun p y`
- What: ω is multiplicative: ω(xy) = ω(x)ω(y).
- How: `simp [teichmullerFun]` using `map_mul` of `toZMod` and `teichmullerZMod`.
- Hypotheses: p prime.
- Uses from project: [teichmullerFun]
- Used by: `teichmuller` (map_mul')
- Visibility: public
- Lines: 119–121 (proof: 1 line)
- Notes: none

### lemma teichmullerFun_eq_of_sub_mem
- Type: `lemma teichmullerFun_eq_of_sub_mem {x y : ℤ_[p]} (h : x - y ∈ Ideal.span {(p : ℤ_[p])}) : teichmullerFun p x = teichmullerFun p y`
- What: ω is locally constant: it depends only on x mod p.
- How: Show `toZMod x = toZMod y` from x − y ∈ pℤ_p (via ker toZMod / maximalIdeal = span p), then both sides reduce to the same `teichmullerZMod` value.
- Hypotheses: p prime; x − y ∈ pℤ_p.
- Uses from project: [teichmullerFun]
- Used by: unused in file
- Visibility: public
- Lines: 124–130 (proof: 4 lines)
- Notes: none

### lemma isUnit_teichmullerFun
- Type: `lemma isUnit_teichmullerFun (x : ℤ_[p]ˣ) : IsUnit (teichmullerFun p (x : ℤ_[p]))`
- What: ω(x) is a unit when x is a unit.
- How: `IsUnit.of_pow_eq_one` from `teichmullerFun_pow_card_sub_one`, with p−1 ≠ 0.
- Hypotheses: p prime; x a unit.
- Uses from project: [teichmullerFun, teichmullerFun_pow_card_sub_one]
- Used by: `teichmuller`
- Visibility: public
- Lines: 133–135 (proof: 2 lines)
- Notes: none

### lemma isLocallyConstant_teichmullerFun
- Type: `lemma isLocallyConstant_teichmullerFun : IsLocallyConstant (teichmullerFun p)`
- What: ω : ℤ_p → ℤ_p is locally constant (factors through reduction mod p).
- How: Show each fibre {x | toZMod x = a} is open (ball of radius p⁻¹ via `norm_le_pow_iff_mem_span_pow`); write the preimage of any set s as a finite union of such fibres over residues whose lift lands in s; conclude via `isOpen_biUnion`.
- Hypotheses: p prime.
- Uses from project: [teichmullerFun, teichmullerZMod]
- Used by: `continuous_angleUnit_val`, `branchChar`
- Visibility: public
- Lines: 140–175 (proof: 35 lines)
- Notes: long(30-50)

### def teichmuller
- Type: `noncomputable def teichmuller : ℤ_[p]ˣ →* ℤ_[p]ˣ`
- What: The Teichmüller character ω as a multiplicative monoid hom on units (L5.3.1 packaged).
- How: `toFun x := (isUnit_teichmullerFun p x).unit`; `map_one'` and `map_mul'` via `teichmullerFun` and `teichmullerFun_mul` after `ext`.
- Hypotheses: p prime.
- Uses from project: [isUnit_teichmullerFun, teichmullerFun, teichmullerFun_mul]
- Used by: `teichmuller_coe`, `angleUnit`, `teichmuller_mul_angleUnit`, `branchChar`, `branchChar_natCast`, and consumers of `angleUnit`
- Visibility: public
- Lines: 178–185 (proof: structure, 8 lines)
- Notes: none

### lemma teichmuller_coe
- Type: `@[simp] lemma teichmuller_coe (x : ℤ_[p]ˣ) : (teichmuller p x : ℤ_[p]) = teichmullerFun p (x : ℤ_[p])`
- What: The underlying ℤ_p-value of the unit ω(x) is `teichmullerFun p x`.
- How: `rfl`.
- Hypotheses: p prime; x a unit.
- Uses from project: [teichmuller, teichmullerFun]
- Used by: `angleUnit_sub_one_mem`, `continuous_angleUnit_val`, `branchChar`, `branchChar_natCast`
- Visibility: public (simp)
- Lines: 188–189 (proof: rfl)
- Notes: none

### lemma castHom_toZModPow_eq_toZMod
- Type: `lemma castHom_toZModPow_eq_toZMod {M : ℕ} (hM : M ≠ 0) (x : ℤ_[p]) : ZMod.castHom (dvd_pow_self p hM) (ZMod p) (toZModPow M x) = toZMod x`
- What: Reduction mod p^M followed by the cast ZMod (p^M) → ZMod p equals reduction mod p (the toZMod/toZModPow bridge for ω-as-Dirichlet-character evaluations, T520).
- How: A calc through the approximant: x − appr x M ∈ maximalIdeal; cast `toZModPow M x` to `(appr x M : ZMod p)`, then `zmod_congr_of_sub_mem_max_ideal` to `(zmodRepr x : ZMod p)`, which is `toZMod x` by rfl.
- Hypotheses: p prime; M ≠ 0.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 194–205 (proof: 12 lines)
- Notes: none

### def teichmullerChar
- Type: `noncomputable def teichmullerChar : DirichletCharacter ℤ_[p] p`
- What: ω packaged as a Dirichlet character mod p — values on (ZMod p)ˣ are the (p−1)-th roots of unity, 0 ↦ 0 (L5.3.7 sub-leaf, T520).
- How: Take `(teichmullerZMod p).toMonoidHom` and supply `map_nonunit'`: a non-unit of ZMod p is 0 (via `isUnit_iff_ne_zero`), and ω(0) = 0 by `simp`.
- Hypotheses: p prime.
- Uses from project: [teichmullerZMod]
- Used by: `teichmullerChar_apply`, `teichmullerChar_toZMod`
- Visibility: public
- Lines: 210–214 (proof: 4 lines)
- Notes: none

### lemma teichmullerChar_apply
- Type: `@[simp] lemma teichmullerChar_apply (a : ZMod p) : teichmullerChar p a = teichmullerZMod p a`
- What: The Dirichlet character ω evaluated at a residue a equals `teichmullerZMod p a`.
- How: `rfl`.
- Hypotheses: p prime.
- Uses from project: [teichmullerChar, teichmullerZMod]
- Used by: unused in file
- Visibility: public (simp)
- Lines: 217–218 (proof: rfl)
- Notes: none

### lemma teichmullerChar_toZMod
- Type: `@[simp] lemma teichmullerChar_toZMod (x : ℤ_[p]) : teichmullerChar p (toZMod x) = teichmullerFun p x`
- What: The defining compatibility ω(x mod p) = ω(x) between the Dirichlet character and `teichmullerFun` (decomposition L5.3.7 attack [1]).
- How: `rfl`.
- Hypotheses: p prime.
- Uses from project: [teichmullerChar, teichmullerFun]
- Used by: unused in file
- Visibility: public (simp)
- Lines: 223–224 (proof: rfl)
- Notes: none

### def angleUnit
- Type: `noncomputable def angleUnit (x : ℤ_[p]ˣ) : ℤ_[p]ˣ := (teichmuller p x)⁻¹ * x`
- What: The projection ⟨x⟩ = ω(x)⁻¹·x onto 1 + pℤ_p, valued in units (L5.3.2, RJW Def 5.15).
- How: Definition: `(teichmuller p x)⁻¹ * x`.
- Hypotheses: p prime; x a unit.
- Uses from project: [teichmuller]
- Used by: `angleUnit_sub_one_mem`, `angleUnit_mul`, `teichmuller_mul_angleUnit`, `continuous_angleUnit_val`, `continuous_onePAdicPow_angleUnit`, `branchChar`, `branchChar_natCast`
- Visibility: public
- Lines: 233 (proof: defn, 1 line)
- Notes: none

### lemma angleUnit_sub_one_mem
- Type: `lemma angleUnit_sub_one_mem (x : ℤ_[p]ˣ) : (angleUnit p x : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}`
- What: ⟨x⟩ lies in 1 + pℤ_p: ⟨x⟩ − 1 ∈ pℤ_p.
- How: Rewrite ⟨x⟩ − 1 = ω(x)⁻¹·(x − ω(x)) using `Units.inv_mul`/`angleUnit`, then it is in the ideal because x − ω(x) is (`teichmullerFun_sub_self_mem`, after negation) and the ideal absorbs left multiplication.
- Hypotheses: p prime; x a unit.
- Uses from project: [angleUnit, teichmuller, teichmuller_coe, teichmullerFun, teichmullerFun_sub_self_mem]
- Used by: `continuous_onePAdicPow_angleUnit`, `branchChar`, `branchChar_apply`, `zetaPBranch`/interpolation (via branchChar)
- Visibility: public
- Lines: 235–242 (proof: 8 lines)
- Notes: none

### lemma angleUnit_mul
- Type: `lemma angleUnit_mul (x y : ℤ_[p]ˣ) : angleUnit p (x * y) = angleUnit p x * angleUnit p y`
- What: ⟨·⟩ is multiplicative: ⟨xy⟩ = ⟨x⟩⟨y⟩.
- How: Expand `angleUnit` and `map_mul`, then `mul_inv_rev` plus commutativity in the abelian unit group (`mul_mul_mul_comm`).
- Hypotheses: p prime.
- Uses from project: [angleUnit, teichmuller]
- Used by: unused in file
- Visibility: public
- Lines: 244–248 (proof: 3 lines)
- Notes: none

### lemma teichmuller_mul_angleUnit
- Type: `lemma teichmuller_mul_angleUnit (x : ℤ_[p]ˣ) : teichmuller p x * angleUnit p x = x`
- What: The multiplicative decomposition x = ω(x)·⟨x⟩ (RJW Def 5.15).
- How: `mul_inv_cancel_left`.
- Hypotheses: p prime; x a unit.
- Uses from project: [teichmuller, angleUnit]
- Used by: unused in file
- Visibility: public
- Lines: 252–253 (proof: 1 line)
- Notes: none

### lemma tendsto_pow_atTop_nhds_zero_of_mem_span
- Type: `lemma tendsto_pow_atTop_nhds_zero_of_mem_span {w : ℤ_[p]} (hw : w ∈ Ideal.span {(p : ℤ_[p])}) : Filter.Tendsto (w ^ ·) Filter.atTop (nhds 0)`
- What: Elements of pℤ_p are topologically unipotent: w^n → 0.
- How: ‖w‖ ≤ p^{−1} < 1 (via `norm_le_pow_iff_mem_span_pow`), then `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`.
- Hypotheses: p prime; w ∈ pℤ_p.
- Uses from project: []
- Used by: `onePAdicPow`
- Visibility: public
- Lines: 260–268 (proof: 6 lines)
- Notes: none

### lemma isClosed_span_p
- Type: `lemma isClosed_span_p : IsClosed {x : ℤ_[p] | x ∈ Ideal.span {(p : ℤ_[p])}}`
- What: The ideal pℤ_p is closed (it is the closed ball of radius p⁻¹).
- How: Rewrite the set as {‖x‖ ≤ p^{−1}} via `norm_le_pow_iff_mem_span_pow`, then `isClosed_le continuous_norm continuous_const`.
- Hypotheses: p prime.
- Uses from project: []
- Used by: `onePAdicPow_sub_one_mem`
- Visibility: public
- Lines: 271–276 (proof: 5 lines)
- Notes: none

### def onePAdicPow
- Type: `noncomputable def onePAdicPow (y : ℤ_[p]) (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) : AddChar ℤ_[p] ℤ_[p]`
- What: For y ∈ 1 + pℤ_p, the power function s ↦ y^s, the unique continuous additive character valued y at 1 (L5.3.3; source defines exp(s·log x), the two agree by uniqueness).
- How: `PadicInt.addChar_of_value_at_one (y − 1)` fed the unipotence `tendsto_pow_atTop_nhds_zero_of_mem_span`.
- Hypotheses: p prime; y − 1 ∈ pℤ_p.
- Uses from project: [tendsto_pow_atTop_nhds_zero_of_mem_span]
- Used by: `onePAdicPow_apply_one`, `onePAdicPow_natCast`, `continuous_onePAdicPow`, `onePAdicPow_congr`, `onePAdicPow_sub_one_mem`, `onePAdicPow_sub_one_mem_pow`, `onePAdicPow_mul_base`, `eq_one_of_pow_card_sub_one`, `continuous_onePAdicPow_angleUnit`, `branchChar`
- Visibility: public
- Lines: 285–288 (proof: defn, 4 lines)
- Notes: none

### lemma onePAdicPow_apply_one
- Type: `@[simp] lemma onePAdicPow_apply_one (y : ℤ_[p]) (hy : ...) : onePAdicPow p y hy 1 = y`
- What: y^1 = y.
- How: Unfold `onePAdicPow` / `addChar_of_value_at_one_def`, then `ring`.
- Hypotheses: p prime; y − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow]
- Used by: `onePAdicPow_natCast`, `onePAdicPow_mul_base`, `eq_one_of_pow_card_sub_one`
- Visibility: public (simp)
- Lines: 291–294 (proof: 2 lines)
- Notes: none

### lemma onePAdicPow_natCast
- Type: `@[simp] lemma onePAdicPow_natCast (y : ℤ_[p]) (hy : ...) (k : ℕ) : onePAdicPow p y hy (k : ℤ_[p]) = y ^ k`
- What: At a natural-number exponent, y^k coincides with the ordinary power.
- How: `← nsmul_one k`, the additive-character power law `AddChar.map_nsmul_eq_pow`, then `onePAdicPow_apply_one`.
- Hypotheses: p prime; y − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow_apply_one]
- Used by: `onePAdicPow_sub_one_mem`, `onePAdicPow_sub_one_mem_pow`, `eq_one_of_pow_card_sub_one`, `branchChar_natCast`
- Visibility: public (simp)
- Lines: 297–299 (proof: 2 lines)
- Notes: none

### lemma continuous_onePAdicPow
- Type: `lemma continuous_onePAdicPow (y : ℤ_[p]) (hy : ...) : Continuous (onePAdicPow p y hy)`
- What: The power character s ↦ y^s is continuous.
- How: `PadicInt.continuous_addChar_of_value_at_one`.
- Hypotheses: p prime; y − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow]
- Used by: `onePAdicPow_sub_one_mem`, `onePAdicPow_sub_one_mem_pow`, `onePAdicPow_mul_base`, `eq_one_of_pow_card_sub_one`, `continuous_onePAdicPow_angleUnit` (indirectly)
- Visibility: public
- Lines: 301–303 (proof: 1 line)
- Notes: none

### lemma onePAdicPow_congr
- Type: `lemma onePAdicPow_congr {y z : ℤ_[p]} (h : y = z) (hy : ...) (s : ℤ_[p]) : onePAdicPow p y hy s = onePAdicPow p z (h ▸ hy) s`
- What: Transport of the power function along an equality of bases y = z.
- How: `subst h; rfl`.
- Hypotheses: p prime; y = z; y − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow]
- Used by: `continuous_onePAdicPow_angleUnit`
- Visibility: public
- Lines: 306–310 (proof: 2 lines)
- Notes: none

### lemma onePAdicPow_sub_one_mem
- Type: `lemma onePAdicPow_sub_one_mem (y : ℤ_[p]) (hy : ...) (s : ℤ_[p]) : onePAdicPow p y hy s - 1 ∈ Ideal.span {(p : ℤ_[p])}`
- What: y^s stays in 1 + pℤ_p for every s ∈ ℤ_p.
- How: The set {x | y^x − 1 ∈ pℤ_p} is closed (`isClosed_span_p` pulled back along continuity) and contains all naturals (since y ≡ 1 mod p ⇒ y^k ≡ 1, via the quotient map); conclude by density of ℕ in ℤ_p (`denseRange_natCast`, `closure_minimal`).
- Hypotheses: p prime; y − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow, isClosed_span_p, continuous_onePAdicPow, onePAdicPow_natCast]
- Used by: unused in file
- Visibility: public
- Lines: 312–330 (proof: 18 lines)
- Notes: none

### lemma onePAdicPow_sub_one_mem_pow
- Type: `lemma onePAdicPow_sub_one_mem_pow {y : ℤ_[p]} (hy : y - 1 ∈ span {p}) {m : ℕ} (hym : y - 1 ∈ span {p^m}) (s : ℤ_[p]) : onePAdicPow p y hy s - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ m}`
- What: Strengthened congruence: if y ≡ 1 mod p^m then y^s ≡ 1 mod p^m for all s ∈ ℤ_p.
- How: Same density/closure argument as `onePAdicPow_sub_one_mem`, but run modulo p^m: closedness via the ball {‖z‖ ≤ p^{−m}}, naturals covered by the quotient mod p^m, then `closure_minimal` with `denseRange_natCast`.
- Hypotheses: p prime; y − 1 ∈ pℤ_p and y − 1 ∈ p^mℤ_p.
- Uses from project: [onePAdicPow, continuous_onePAdicPow, onePAdicPow_natCast]
- Used by: `continuous_onePAdicPow_angleUnit`
- Visibility: public
- Lines: 335–360 (proof: 25 lines)
- Notes: none

### lemma mul_sub_one_mem
- Type: `lemma mul_sub_one_mem {y z : ℤ_[p]} (hy : y - 1 ∈ span {p}) (hz : z - 1 ∈ span {p}) : y * z - 1 ∈ Ideal.span {(p : ℤ_[p])}`
- What: 1 + pℤ_p is closed under multiplication: yz − 1 ∈ pℤ_p whenever y − 1, z − 1 are.
- How: Rewrite yz − 1 = (y−1)·z + (z−1) and use `add_mem` with the ideal's absorption of multiplication.
- Hypotheses: p prime; y − 1, z − 1 ∈ pℤ_p.
- Uses from project: []
- Used by: `onePAdicPow_mul_base`, `continuous_onePAdicPow_angleUnit`
- Visibility: public
- Lines: 364–368 (proof: 2 lines)
- Notes: none

### lemma onePAdicPow_mul_base
- Type: `lemma onePAdicPow_mul_base (y z : ℤ_[p]) (hy : ...) (hz : ...) (s : ℤ_[p]) : onePAdicPow p (y * z) (mul_sub_one_mem p hy hz) s = onePAdicPow p y hy s * onePAdicPow p z hz s`
- What: Multiplicativity in the base: (yz)^s = y^s · z^s.
- How: The product character onePAdicPow y · onePAdicPow z is continuous (`AddChar.mul_apply`) and has value yz at 1, so by uniqueness `eq_addChar_of_value_at_one` it equals onePAdicPow (yz); evaluate at s.
- Hypotheses: p prime; y − 1, z − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow, mul_sub_one_mem, continuous_onePAdicPow, onePAdicPow_apply_one]
- Used by: `continuous_onePAdicPow_angleUnit`
- Visibility: public
- Lines: 371–383 (proof: 12 lines)
- Notes: none

### lemma eq_one_of_pow_card_sub_one
- Type: `lemma eq_one_of_pow_card_sub_one {u : ℤ_[p]ˣ} (hu : u ^ (p - 1) = 1) (hmem : (u : ℤ_[p]) - 1 ∈ span {p}) : u = 1`
- What: Uniqueness of the ω/⟨·⟩ decomposition: an element of μ_{p−1} ∩ (1+pℤ_p) is 1 (degenerate-but-true for p=2; substantive odd-p case rests on torsion-freeness of 1+pℤ_p for prime-to-p exponents).
- How: p−1 is a unit c of ℤ_p (residue −1 ≠ 0); the mulShift-by-(p−1) of the character s↦u^s is trivial by uniqueness (`eq_addChar_of_value_at_one`, since u^{p−1}=1); equating it with the trivial character and evaluating at c⁻¹ gives u = u^{(p−1)(p−1)⁻¹} = 1.
- Hypotheses: p prime; u^(p−1) = 1; u − 1 ∈ pℤ_p.
- Uses from project: [onePAdicPow, onePAdicPow_apply_one, onePAdicPow_natCast, continuous_onePAdicPow]
- Used by: unused in file
- Visibility: public
- Lines: 391–419 (proof: 29 lines)
- Notes: none

### lemma continuous_angleUnit_val
- Type: `lemma continuous_angleUnit_val : Continuous (fun x : ℤ_[p]ˣ => ((angleUnit p x : ℤ_[p])))`
- What: The angle map ⟨·⟩ is continuous as a ℤ_p-valued map on ℤ_pˣ.
- How: Rewrite ⟨x⟩ = ω(x⁻¹)·x = teichmullerFun(x⁻¹)·x; teichmuller is locally constant (`isLocallyConstant_teichmullerFun`) composed with continuous units-inversion (`PadicMeasure.continuous_units_inv_val`), times `Units.continuous_val`.
- Hypotheses: p prime.
- Uses from project: [angleUnit, teichmuller (via teichmuller_coe), teichmullerFun, isLocallyConstant_teichmullerFun]; external `PadicMeasure.continuous_units_inv_val`
- Used by: `continuous_onePAdicPow_angleUnit`
- Visibility: public
- Lines: 433–440 (proof: 8 lines)
- Notes: none

### lemma continuous_onePAdicPow_angleUnit
- Type: `lemma continuous_onePAdicPow_angleUnit (s : ℤ_[p]) : Continuous (fun x : ℤ_[p]ˣ => onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s)`
- What: Base-continuity of the power map: x ↦ ⟨x⟩^s is continuous on ℤ_pˣ for each fixed s.
- How: Pointwise ε–δ via `continuousAt`: choose m = max m₀ 1 with p^{−m₀} < ε; for x near x₀, the increment w = ⟨x⟩⟨x₀⟩⁻¹ satisfies w − 1 ∈ p^mℤ_p; factor ⟨x⟩^s = ⟨x₀⟩^s · w^s (`onePAdicPow_mul_base`), use `onePAdicPow_sub_one_mem_pow` to bound w^s − 1, and a norm calc (‖·‖≤1) gives the difference ≤ p^{−m} < ε.
- Hypotheses: p prime; s ∈ ℤ_p.
- Uses from project: [onePAdicPow, angleUnit, angleUnit_sub_one_mem, continuous_angleUnit_val, onePAdicPow_congr, mul_sub_one_mem, onePAdicPow_mul_base, onePAdicPow_sub_one_mem_pow]
- Used by: `branchChar`
- Visibility: public
- Lines: 446–507 (proof: 62 lines)
- Notes: OVER-50 (needs /decompose-proof)

### def branchChar
- Type: `noncomputable def branchChar (i : ℕ) (s : ℤ_[p]) : C(ℤ_[p]ˣ, ℤ_[p])`
- What: The continuous character x ↦ ω(x)^i·⟨x⟩^s on ℤ_pˣ, packaged as a continuous map into ℤ_p (L5.3.4, RJW TeX 1907–1910).
- How: `toFun` is the product; continuity = (locally-constant teichmuller composed with `Units.continuous_val`, raised to the i-th power) times `continuous_onePAdicPow_angleUnit`.
- Hypotheses: p prime; i ∈ ℕ; s ∈ ℤ_p.
- Uses from project: [teichmuller (via teichmuller_coe), teichmullerFun, isLocallyConstant_teichmullerFun, onePAdicPow, angleUnit, angleUnit_sub_one_mem, continuous_onePAdicPow_angleUnit]
- Used by: `branchChar_apply`, `branchChar_natCast`, `zetaPBranch`, `zetaPBranch_interpolation`
- Visibility: public
- Lines: 511–521 (proof: bundled continuity, ~9 lines)
- Notes: none

### lemma branchChar_apply
- Type: `@[simp] lemma branchChar_apply (i : ℕ) (s : ℤ_[p]) (x : ℤ_[p]ˣ) : branchChar p i s x = (teichmuller p x : ℤ_[p]) ^ i * onePAdicPow p (angleUnit p x : ℤ_[p]) (angleUnit_sub_one_mem p x) s`
- What: Evaluation rule for the branch character.
- How: `rfl`.
- Hypotheses: p prime.
- Uses from project: [branchChar, teichmuller, onePAdicPow, angleUnit, angleUnit_sub_one_mem]
- Used by: `branchChar_natCast`
- Visibility: public (simp)
- Lines: 524–527 (proof: rfl)
- Notes: none

### lemma branchChar_natCast
- Type: `lemma branchChar_natCast {i k : ℕ} (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) : branchChar p i (k : ℤ_[p]) = PadicMeasure.unitsPowCM p k`
- What: On the congruence class k ≡ i mod (p−1), the branch character at the integer s = k is x^k (RJW TeX 1919: ω(x)^i⟨x⟩^k = x^k iff k ≡ i mod (p−1); the "if").
- How: `ext x`; reduce to a units identity: orderOf ω(x) ∣ p−1, so ω(x)^k = ω(x)^i (`pow_eq_pow_iff_modEq` with k ≡ i [MOD p−1]); then ω(x)^i·(ω(x)⁻¹x)^k = x^k after `mul_pow`/`inv_pow`/`mul_inv_cancel`; transport to ℤ_p via `congrArg Units.val`.
- Hypotheses: p prime; k ≡ i mod (p−1).
- Uses from project: [branchChar, branchChar_apply, onePAdicPow_natCast, teichmuller (via teichmuller_coe), teichmullerFun_pow_card_sub_one, angleUnit]; external `PadicMeasure.unitsPowCM`
- Used by: `zetaPBranch_interpolation`
- Visibility: public
- Lines: 533–549 (proof: 17 lines)
- Notes: none

### def zetaPBranch
- Type: `noncomputable def zetaPBranch (hp2 : p ≠ 2) (i : ℕ) (s : ℤ_[p]) : ℚ_[p]`
- What: The i-th branch of the Kubota–Leopoldt p-adic L-function ζ_{p,i}(s) = ∫_{ℤ_p^×} ω(x)^i⟨x⟩^{1−s}·ζ_p (L5.3.5/L5.3.6, RJW Def 5.16), via the pseudo-measure pairing at the §4 topological generator and its witness `zetaNum`.
- How: Definition: ((branchChar p i (1−s) at the generator − 1)⁻¹ · zetaNum p (generator) (branchChar p i (1−s)), cast to ℚ_[p]; junk value at the pole (i,s)=(0,1)).
- Hypotheses: p prime; p ≠ 2.
- Uses from project: [branchChar]; external `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.zetaNum`
- Used by: `zetaPBranch_interpolation`
- Visibility: public
- Lines: 557–563 (proof: defn, 7 lines)
- Notes: none

### theorem zetaPBranch_interpolation
- Type: `theorem zetaPBranch_interpolation (hp2 : p ≠ 2) {i k : ℕ} (hk : 0 < k) (hik : (k : ZMod (p - 1)) = (i : ZMod (p - 1))) : zetaPBranch p hp2 i ((1:ℤ_[p]) - (k:ℤ_[p])) = (1 - (p:ℚ_[p])^((k:ℤ)-1)) * ((zetaNeg (k-1) : ℚ) : ℚ_[p])`
- What: RJW Theorem 5.17: for k ≥ 1 with k ≡ i mod (p−1), ζ_{p,i}(1−k) = (1−p^{k−1})ζ(1−k) (RHS is §4's rational `zetaNeg (k−1)`).
- How: Unpack the topological generator data; rewrite 1−(1−k)=k so the branch character becomes `unitsPowCM p k` (`branchChar_natCast`); use the witness relation ([u]−1)·ζ_p = zetaNum m and the moment formula `PadicMeasure.padicZeta_moments`; nonvanishing of u^k−1 from `topGen_pow_ne_one`; finish with `field_simp`, `zpow_natCast`, `ring`.
- Hypotheses: p prime; p ≠ 2; k > 0; k ≡ i mod (p−1).
- Uses from project: [zetaPBranch, branchChar, branchChar_natCast]; external `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.padicZeta`, `PadicMeasure.padicZeta_moments`, `PadicMeasure.zetaNum`, `PadicMeasure.dirac`, `PadicMeasure.unitsPowCM`, `PadicMeasure.topGen_pow_ne_one`, `zetaNeg`
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 571–602 (proof: 32 lines)
- Notes: long(30-50); uses `classical`

---

## File Summary

- **Total declarations: 38** — defs: 9 (`maximalIdealQuotientEquivZMod`, `teichmullerZMod`, `teichmullerFun`, `teichmuller`, `teichmullerChar`, `angleUnit`, `onePAdicPow`, `branchChar`, `zetaPBranch`) / lemmas+theorems: 27 / instances: 2 (anonymous `CharP`, `Finite`).
- **Key API (used by ≥3 decls in file):**
  - `teichmullerZMod` (used by 7) — core Teichmüller-on-residues map.
  - `teichmullerFun` (used by ~11) — ω as a ℤ_p → ℤ_p function.
  - `teichmuller` (used by several) — ω as a unit hom.
  - `onePAdicPow` (used by ~10) — the one-unit power y^s.
  - `angleUnit` (used by 7) — the ⟨·⟩ projection.
  - `branchChar` (used by 4) — the branch character ω^i⟨·⟩^s.
  - `maximalIdealQuotientEquivZMod` (used by 4) — residue-ring ≃ ZMod p.
  - `onePAdicPow_natCast` (used by 4), `continuous_onePAdicPow` (used by ~5).
- **Unused within file (terminal/exported API):** `exists_primitiveRoot_card_sub_one`, `teichmullerFun_eq_of_sub_mem`, `castHom_toZModPow_eq_toZMod`, `teichmullerChar_apply`, `teichmullerChar_toZMod`, `angleUnit_mul`, `teichmuller_mul_angleUnit`, `onePAdicPow_sub_one_mem`, `eq_one_of_pow_card_sub_one`, `zetaPBranch_interpolation` (main theorem), plus the two anonymous instances. (`teichmullerChar` family and `castHom_toZModPow_eq_toZMod` are T520 plumbing consumed elsewhere.)
- **Decls with sorry: none.**
- **set_option: none.**
- **Proofs >50 lines (OVER-50): 1** — `continuous_onePAdicPow_angleUnit` (62 lines, lines 446–507). Needs /decompose-proof.
- **Proofs 30–50 lines: 2** — `isLocallyConstant_teichmullerFun` (35 lines, 140–175); `zetaPBranch_interpolation` (32 lines, 571–602).

Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_Interpolation_Branches.md
