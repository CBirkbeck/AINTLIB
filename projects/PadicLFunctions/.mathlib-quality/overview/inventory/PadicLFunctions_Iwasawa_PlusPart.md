# Inventory: PadicLFunctions/Iwasawa/PlusPart.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/Iwasawa/PlusPart.lean`

The ±-decomposition of Λ(𝒢) and the plus quotient Λ(𝒢⁺). RJW (arXiv:2309.15692) §11.1. 𝒢 = `ℤ_[p]ˣ`, c = `(-1 : ℤ_[p]ˣ)`, 𝒢⁺ = `ℤ_[p]ˣ ⧸ zpowers (-1)`.

---

### def invariants
- Type: `(σ : M →ₗ[R] M) : Submodule R M := LinearMap.ker (σ - LinearMap.id)`
- What: The `+1`-eigenspace (invariants) of an `R`-linear endomorphism σ of a module M.
- How: Defined directly as the kernel of `σ - id`.
- Hypotheses: R a `CommRing`, M an `AddCommGroup` with `Module R M`; σ an R-linear endomorphism.
- Uses from project: []
- Used by: `mem_invariants_iff`, `smul_add_apply_mem_invariants`, `isCompl_invariants_antiInvariants`, `plusPart`
- Visibility: public
- Lines: 41–43 (proof: term, 1 line)
- Notes: none

### def antiInvariants
- Type: `(σ : M →ₗ[R] M) : Submodule R M := LinearMap.ker (σ + LinearMap.id)`
- What: The `−1`-eigenspace (anti-invariants) of an R-linear endomorphism σ.
- How: Defined directly as the kernel of `σ + id`.
- Hypotheses: R a `CommRing`, M an `AddCommGroup` with `Module R M`; σ an R-linear endomorphism.
- Uses from project: []
- Used by: `mem_antiInvariants_iff`, `smul_sub_apply_mem_antiInvariants`, `isCompl_invariants_antiInvariants`, `minusPart`
- Visibility: public
- Lines: 45–47 (proof: term, 1 line)
- Notes: none

### lemma mem_invariants_iff
- Type: `{σ : M →ₗ[R] M} {x : M} : x ∈ invariants σ ↔ σ x = x`
- What: Characterises membership in the invariants: x is invariant iff σ fixes x.
- How: Unfolds `invariants` and `LinearMap.mem_ker`, then `sub_eq_zero`.
- Hypotheses: As `invariants`; σ an endomorphism, x ∈ M.
- Uses from project: [invariants]
- Used by: `smul_add_apply_mem_invariants`, `isCompl_invariants_antiInvariants`, `mem_plusPart_iff`
- Visibility: public
- Lines: 49–50 (proof: 1 line)
- Notes: none

### lemma mem_antiInvariants_iff
- Type: `{σ : M →ₗ[R] M} {x : M} : x ∈ antiInvariants σ ↔ σ x = -x`
- What: Characterises membership in the anti-invariants: x is anti-invariant iff σx = −x.
- How: Unfolds `antiInvariants` and `LinearMap.mem_ker`, then `add_eq_zero_iff_eq_neg`.
- Hypotheses: As `antiInvariants`; σ an endomorphism, x ∈ M.
- Uses from project: [antiInvariants]
- Used by: `smul_sub_apply_mem_antiInvariants`, `isCompl_invariants_antiInvariants`, `mem_minusPart_iff`
- Visibility: public
- Lines: 52–55 (proof: 2 lines)
- Notes: none

### theorem smul_add_apply_mem_invariants
- Type: `[Invertible (2 : R)] (σ : M →ₗ[R] M) (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) : (⅟(2 : R)) • (x + σ x) ∈ invariants σ`
- What: The plus-projection `(x + σx)/2` lands in the invariants.
- How: Uses `mem_invariants_iff`; rewrites with `σ(σx) = x` (from involutivity `hσ` via `LinearMap.ext_iff`), `map_smul`, `map_add`, then `add_comm`.
- Hypotheses: 2 invertible in R; σ an involution (`σ∘σ = id`); x ∈ M.
- Uses from project: [mem_invariants_iff, invariants]
- Used by: `isCompl_invariants_antiInvariants`
- Visibility: public
- Lines: 57–62 (proof: 2 lines)
- Notes: none

### theorem smul_sub_apply_mem_antiInvariants
- Type: `[Invertible (2 : R)] (σ : M →ₗ[R] M) (hσ : σ ∘ₗ σ = LinearMap.id) (x : M) : (⅟(2 : R)) • (x - σ x) ∈ antiInvariants σ`
- What: The minus-projection `(x − σx)/2` lands in the anti-invariants.
- How: Uses `mem_antiInvariants_iff`; rewrites with `σ(σx)=x`, `map_smul`, `map_sub`, then `← smul_neg`, `neg_sub`.
- Hypotheses: 2 invertible in R; σ an involution; x ∈ M.
- Uses from project: [mem_antiInvariants_iff, antiInvariants]
- Used by: `isCompl_invariants_antiInvariants`
- Visibility: public
- Lines: 64–69 (proof: 2 lines)
- Notes: none

### theorem isCompl_invariants_antiInvariants
- Type: `[Invertible (2 : R)] (σ : M →ₗ[R] M) (hσ : σ ∘ₗ σ = LinearMap.id) : IsCompl (invariants σ) (antiInvariants σ)`
- What: RJW Lem. `lem:decompose plus minus` — for an involution σ of an R-module with 2 invertible, M is the internal direct sum of the ±1-eigenspaces.
- How: Proves disjointness (σx=x and σx=−x force `2•x=0` via `two_smul`/`add_eq_zero_iff_eq_neg`, then `invOf_smul_smul` kills x) and codisjointness (`codisjoint_iff_le_sup`, writing x = ⅟2•(x+σx) + ⅟2•(x−σx) using the two projection lemmas and `invOf_smul_smul`).
- Hypotheses: 2 invertible in R; σ an involution.
- Uses from project: [invariants, antiInvariants, mem_invariants_iff, mem_antiInvariants_iff, smul_add_apply_mem_invariants, smul_sub_apply_mem_antiInvariants]
- Used by: `isCompl_plusPart_minusPart`
- Visibility: public
- Lines: 71–95 (proof: ~17 lines)
- Notes: none (hinges on `smul_add_apply_mem_invariants`, `smul_sub_apply_mem_antiInvariants`, `invOf_smul_smul`)

### instance SMulCommClass ℤ_[p] (PadicMeasure …) (PadicMeasure …)
- Type: `instance : SMulCommClass ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ)`
- What: ℤ_[p]-scalars commute with convolution on the right factor: `c•(μ*ν) = μ*(c•ν)`.
- How: `LinearMap.ext`; via `conv_mul_apply` reduces to pulling the scalar through the inner integral `innerInt`, proved by `innerInt_apply` pointwise and `map_smul`.
- Hypotheses: p prime (`Fact p.Prime`).
- Uses from project: [conv_mul_apply, innerInt, innerInt_apply, mulCM₂]
- Used by: unused in file
- Visibility: public (instance)
- Lines: 106–115 (proof: ~10 lines)
- Notes: none

### instance IsScalarTower ℤ_[p] (PadicMeasure …) (PadicMeasure …)
- Type: `instance : IsScalarTower ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) (PadicMeasure p ℤ_[p]ˣ)`
- What: Scalar tower for convolution on the left factor: `(c•μ)*ν = c•(μ*ν)`.
- How: `LinearMap.ext`; `conv_mul_apply` twice and `LinearMap.smul_apply` — the outer measure carries the scalar pointwise.
- Hypotheses: p prime.
- Uses from project: [conv_mul_apply]
- Used by: unused in file
- Visibility: public (instance)
- Lines: 117–121 (proof: 4 lines)
- Notes: none

### def cAct
- Type: `cAct : PadicMeasure p ℤ_[p]ˣ →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ := LinearMap.mulLeft ℤ_[p] (dirac p (-1 : ℤ_[p]ˣ))`
- What: The action of complex conjugation on Λ(𝒢): convolution (left-multiplication) by the Dirac measure at c = −1.
- How: Defined as `LinearMap.mulLeft` by `dirac p (-1)`.
- Hypotheses: p prime.
- Uses from project: [dirac]
- Used by: `cAct_apply`, `cAct_involutive`, `plusPart`, `minusPart`
- Visibility: public
- Lines: 125–128 (proof: term)
- Notes: none

### lemma cAct_apply
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) : cAct p μ = dirac p (-1 : ℤ_[p]ˣ) * μ` (`@[simp]`)
- What: Evaluates `cAct` as left-convolution by `dirac (-1)`.
- How: `LinearMap.mulLeft_apply`.
- Hypotheses: p prime; μ a measure.
- Uses from project: [cAct, dirac]
- Used by: `cAct_involutive`, `mem_plusPart_iff`, `mem_minusPart_iff`
- Visibility: public
- Lines: 130–133 (proof: term, 1 line)
- Notes: none

### theorem cAct_involutive
- Type: `cAct p ∘ₗ cAct p = LinearMap.id`
- What: c is an involution: `[−1]·[−1] = [1]`.
- How: `LinearMap.ext`; rewrites with `cAct_apply` twice, `← mul_assoc`, `units_dirac_mul_dirac`, the computation `(-1)*(-1)=1`, and `units_one_def`.
- Hypotheses: p prime.
- Uses from project: [cAct, cAct_apply, dirac, units_dirac_mul_dirac, units_one_def]
- Used by: `isCompl_plusPart_minusPart`
- Visibility: public
- Lines: 135–140 (proof: 4 lines)
- Notes: none

### def plusPart
- Type: `plusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) := invariants (cAct p)`
- What: Λ(𝒢)⁺ — the c-invariant measures (image of idempotent (1+c)/2); under RJW TeX 3017 this is Λ(𝒢⁺) inside Λ(𝒢).
- How: Defined as `invariants (cAct p)`.
- Hypotheses: p prime.
- Uses from project: [invariants, cAct]
- Used by: `mem_plusPart_iff`, `mul_mem_plusPart`, `isCompl_plusPart_minusPart`, `mem_plusPart_iff_forall_odd_moment`, `plusSection_mem_plusPart`, `apply_evenPart_of_mem_plusPart`, `plusEquiv`
- Visibility: public
- Lines: 142–145 (proof: term)
- Notes: none

### def minusPart
- Type: `minusPart : Submodule ℤ_[p] (PadicMeasure p ℤ_[p]ˣ) := antiInvariants (cAct p)`
- What: Λ(𝒢)⁻ — the c-anti-invariant measures.
- How: Defined as `antiInvariants (cAct p)`.
- Hypotheses: p prime.
- Uses from project: [antiInvariants, cAct]
- Used by: `mem_minusPart_iff`, `isCompl_plusPart_minusPart`, `projPlus_eq_zero_of_mem_minusPart`, `projPlus_eq_zero_iff`
- Visibility: public
- Lines: 147–149 (proof: term)
- Notes: none

### lemma mem_plusPart_iff
- Type: `{μ : PadicMeasure p ℤ_[p]ˣ} : μ ∈ plusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = μ`
- What: Membership in Λ(𝒢)⁺ ⟺ μ is fixed by left-convolution by dirac(−1).
- How: Unfolds `plusPart`, `mem_invariants_iff`, `cAct_apply`.
- Hypotheses: p prime; μ a measure.
- Uses from project: [plusPart, mem_invariants_iff, cAct_apply, dirac]
- Used by: `mul_mem_plusPart`, `mem_plusPart_iff_forall_odd_moment`, `plusSection_mem_plusPart`, `apply_evenPart_of_mem_plusPart`
- Visibility: public
- Lines: 151–153 (proof: 1 line)
- Notes: none

### lemma mem_minusPart_iff
- Type: `{μ : PadicMeasure p ℤ_[p]ˣ} : μ ∈ minusPart p ↔ dirac p (-1 : ℤ_[p]ˣ) * μ = -μ`
- What: Membership in Λ(𝒢)⁻ ⟺ left-convolution by dirac(−1) negates μ.
- How: Unfolds `minusPart`, `mem_antiInvariants_iff`, `cAct_apply`.
- Hypotheses: p prime; μ a measure.
- Uses from project: [minusPart, mem_antiInvariants_iff, cAct_apply, dirac]
- Used by: `projPlus_eq_zero_of_mem_minusPart`, `ker_projPlus`
- Visibility: public
- Lines: 155–157 (proof: 1 line)
- Notes: none

### theorem mul_mem_plusPart
- Type: `{μ ν : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ plusPart p) : ν * μ ∈ plusPart p`
- What: plusPart is closed under multiplication by arbitrary measures (it is the ideal e⁺Λ(𝒢)).
- How: Rewrites both membership statements via `mem_plusPart_iff` and uses `mul_left_comm` with the hypothesis.
- Hypotheses: p prime; μ ∈ plusPart.
- Uses from project: [plusPart, mem_plusPart_iff]
- Used by: unused in file
- Visibility: public
- Lines: 159–164 (proof: 2 lines)
- Notes: none

### theorem isCompl_plusPart_minusPart
- Type: `(hp2 : p ≠ 2) : IsCompl (plusPart p) (minusPart p)`
- What: RJW Lem. for Λ(𝒢) — for p odd, Λ(𝒢) ≅ Λ(𝒢)⁺ ⊕ Λ(𝒢)⁻.
- How: Installs `Invertible (2 : ℤ_[p])` from `PadicLFunctions.isUnit_two_padicInt`, then applies the general `isCompl_invariants_antiInvariants` with `cAct_involutive`.
- Hypotheses: p ≠ 2.
- Uses from project: [plusPart, minusPart, isCompl_invariants_antiInvariants, cAct, cAct_involutive, PadicLFunctions.isUnit_two_padicInt]
- Used by: `projPlus_eq_zero_iff`
- Visibility: public
- Lines: 166–171 (proof: 2 lines)
- Notes: none

### theorem cAct_apply_unitsPowCM
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (k : ℕ) : (dirac p (-1 : ℤ_[p]ˣ) * μ) (unitsPowCM p k) = (-1) ^ k * μ (unitsPowCM p k)`
- What: Moments of the c-translate: `∫ x^k d([−1]·μ) = (−1)^k ∫ x^k dμ` (χ(c) = −1).
- How: Computes `dirac(−1)(unitsPowCM k) = (−1)^k` via `dirac_apply`, `Units.val_neg`, `Units.val_one`, then applies `units_mul_apply_unitsPowCM`.
- Hypotheses: p prime; μ a measure, k ∈ ℕ.
- Uses from project: [dirac, dirac_apply, unitsPowCM, units_mul_apply_unitsPowCM]
- Used by: `mem_plusPart_iff_forall_odd_moment`
- Visibility: public
- Lines: 175–183 (proof: 5 lines)
- Notes: none

### theorem mem_plusPart_iff_forall_odd_moment
- Type: `{μ : PadicMeasure p ℤ_[p]ˣ} : μ ∈ plusPart p ↔ ∀ k : ℕ, Odd k → μ (unitsPowCM p k) = 0`
- What: RJW §11.1 third lemma — μ ∈ Λ(𝒢⁺) (c-invariance) ⟺ all odd moments ∫ χ(x)^k μ (k ≥ 1 odd) vanish.
- How: Forward: from c-invariance, for odd k the moment equals its negative (`cAct_apply_unitsPowCM`, `hk.neg_one_pow`, `add_self_eq_zero`). Reverse: `eq_zero_of_forall_unitsPowCM_eq_zero` shows `dirac(−1)·μ − μ = 0` by case-splitting `Nat.even_or_odd` on each x^k.
- Hypotheses: p prime; μ a measure. (Decomposition reading would need p ≠ 2; this pair is p-general.)
- Uses from project: [plusPart, mem_plusPart_iff, cAct_apply_unitsPowCM, unitsPowCM, eq_zero_of_forall_unitsPowCM_eq_zero]
- Used by: unused in file
- Visibility: public
- Lines: 185–206 (proof: ~16 lines)
- Notes: none (hinges on `eq_zero_of_forall_unitsPowCM_eq_zero` and `cAct_apply_unitsPowCM`)

### abbrev GPlus
- Type: `GPlus := ℤ_[p]ˣ ⧸ Subgroup.zpowers (-1 : ℤ_[p]ˣ)`
- What: 𝒢⁺ = 𝒢/⟨c⟩, identified via χ with ℤ_[p]ˣ/{±1} (RJW TeX 2992): quotient of compact `ℤ_[p]ˣ` by the closed finite subgroup {±1}.
- How: Abbreviation for the `QuotientGroup` by `zpowers (-1)`.
- Hypotheses: p prime.
- Uses from project: []
- Used by: `quotientMk`, `projPlus`, `projPlus_apply`, `projPlus_dirac`, `deg_projPlus`, `plusSection`, `descendEven`, `descendEven_mk`, `plusSection_mem_plusPart`, `quotientMk_neg`, `comp_quotientMk_even`, `descendEven_comp_quotientMk`, `projPlus_plusSection`, `plusSection_projPlus`, `projPlus_surjective`, `plusEquiv`, `projPlus_eq_zero_of_mem_minusPart`, `projPlus_eq_zero_iff`
- Visibility: public
- Lines: 210–215 (proof: term)
- Notes: none

### def quotientMk
- Type: `quotientMk : C(ℤ_[p]ˣ, GPlus p) := ⟨QuotientGroup.mk, continuous_quotient_mk'⟩`
- What: The quotient projection 𝒢 → 𝒢⁺ as a continuous map.
- How: Bundles `QuotientGroup.mk` with `continuous_quotient_mk'`.
- Hypotheses: p prime.
- Uses from project: [GPlus]
- Used by: `projPlus`, `projPlus_apply`, `dirac_neg_one_mul_apply` (indirectly via negTranslate? no), `comp_quotientMk_even`, `descendEven_comp_quotientMk`, `projPlus_plusSection`, `descendEven_comp`, `plusEquiv`, `projPlus_eq_zero_of_mem_minusPart`, `quotientMk_neg`
- Visibility: public
- Lines: 217–219 (proof: term)
- Notes: none

### def projPlus
- Type: `projPlus : PadicMeasure p ℤ_[p]ˣ →+* PadicMeasure p (GPlus p)` (structure: toFun = `pushforward p (quotientMk p)`, with ring-hom fields)
- What: The pushforward π_* : Λ(𝒢) → Λ(𝒢⁺) along the quotient projection (RJW TeX 3012 "natural surjection"), as a ring hom since mk is a continuous monoid hom.
- How: `map_one'` via `conv_one_def`/`pushforward_dirac` (δ_1 ↦ δ_{mk 1} = δ_1); `map_mul'` via `LinearMap.ext`, `pushforward_apply`, `conv_mul_apply` (inner integrals agree by mk(xy)=mk x·mk y); `map_zero'`/`map_add'` by rfl.
- Hypotheses: p prime.
- Uses from project: [pushforward, quotientMk, GPlus, conv_one_def, pushforward_dirac, pushforward_apply, conv_mul_apply]
- Used by: `projPlus_apply`, `projPlus_dirac`, `deg_projPlus`, `projPlus_plusSection`, `plusSection_projPlus`, `projPlus_surjective`, `projPlus_eq_zero_of_mem_minusPart`, `projPlus_eq_zero_iff`, `ker_projPlus`, `plusEquiv` (definitionally)
- Visibility: public
- Lines: 221–235 (proof: ~12 lines bundled across fields)
- Notes: none

### lemma projPlus_apply
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (f : C(GPlus p, ℤ_[p])) : projPlus p μ f = μ (f.comp (quotientMk p))` (`@[simp]`)
- What: Evaluates the pushforward: integrate the pullback `f ∘ mk` against μ.
- How: `rfl`.
- Hypotheses: p prime; μ a measure, f a function on 𝒢⁺.
- Uses from project: [projPlus, GPlus, quotientMk]
- Used by: `deg_projPlus`, `projPlus_plusSection`, `plusSection_projPlus`, `projPlus_eq_zero_of_mem_minusPart`
- Visibility: public
- Lines: 237–239 (proof: rfl)
- Notes: none

### lemma projPlus_dirac
- Type: `(u : ℤ_[p]ˣ) : projPlus p (dirac p u) = dirac p (QuotientGroup.mk u : GPlus p)` (`@[simp]`)
- What: The pushforward sends a Dirac at u to the Dirac at mk u.
- How: `rfl`.
- Hypotheses: p prime; u a unit.
- Uses from project: [projPlus, dirac, GPlus]
- Used by: unused in file
- Visibility: public
- Lines: 241–243 (proof: rfl)
- Notes: none

### theorem deg_projPlus
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) : deg p (projPlus p μ) = deg p μ`
- What: The augmentation commutes with the projection: deg⁺ ∘ π_* = deg.
- How: Changes both `deg` to evaluation at the constant function 1, then `projPlus_apply` and `congr 1`.
- Hypotheses: p prime; μ a measure.
- Uses from project: [deg, projPlus, projPlus_apply]
- Used by: unused in file
- Visibility: public
- Lines: 245–249 (proof: 2 lines)
- Notes: none

### def negTranslate
- Type: `negTranslate : C(ℤ_[p]ˣ, ℤ_[p]ˣ) := ⟨fun u => -u, …⟩`
- What: Translation by −1 on ℤ_[p]ˣ (the c-translation of function arguments) as a continuous map.
- How: Bundles `u ↦ -u`; continuity by rewriting `-u = (-1)*u` (`neg_one_mul`) and `continuous_const.mul continuous_id`.
- Hypotheses: p prime.
- Uses from project: []
- Used by: `dirac_neg_one_mul_apply`, `evenPart`, `evenPart_even`, `evenPart_of_even`, `evenPart_comp_negTranslate`, `plusSection_mem_plusPart`, `apply_evenPart_of_mem_plusPart`, `projPlus_eq_zero_of_mem_minusPart`
- Visibility: public
- Lines: 253–259 (proof: ~4 lines)
- Notes: none

### lemma dirac_neg_one_mul_apply
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (f : C(ℤ_[p]ˣ, ℤ_[p])) : (dirac p (-1 : ℤ_[p]ˣ) * μ) f = μ (f.comp (negTranslate p))`
- What: Key computation — convolution by dirac(−1) is argument-translation by −1: `(dirac(−1) ⋆ μ) f = ∫ f(−u) dμ(u)`.
- How: `conv_mul_apply`, `dirac_apply`, `innerInt_apply`, then `ContinuousMap.ext` proving `f((-1)*u) = f(-u)` via `neg_one_mul`.
- Hypotheses: p prime; μ a measure, f a function.
- Uses from project: [dirac, negTranslate, conv_mul_apply, dirac_apply, innerInt_apply]
- Used by: `plusSection_mem_plusPart`, `apply_evenPart_of_mem_plusPart`, `projPlus_eq_zero_of_mem_minusPart`
- Visibility: private
- Lines: 261–269 (proof: 5 lines)
- Notes: none

### def evenPart
- Type: `evenPart (hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) : C(ℤ_[p]ˣ, ℤ_[p]) := ((…isUnit_two…unit⁻¹) : ℤ_[p]) • (f + f.comp (negTranslate p))`
- What: The even part of a continuous function on 𝒢: f ↦ (f + f∘c)/2.
- How: Scalar-multiplies `f + f∘negTranslate` by the inverse of 2 (from `PadicLFunctions.isUnit_two_padicInt`).
- Hypotheses: p ≠ 2; f a continuous function.
- Uses from project: [negTranslate, PadicLFunctions.isUnit_two_padicInt]
- Used by: `evenPart_even`, `evenPart_of_even`, `evenPart_comp_negTranslate`, `plusSection`, `plusSection_mem_plusPart`, `apply_evenPart_of_mem_plusPart`, `plusSection_projPlus`, `projPlus_plusSection`
- Visibility: public
- Lines: 271–274 (proof: term)
- Notes: none

### def descendEven
- Type: `descendEven (g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u, g (-u) = g u) : C(GPlus p, ℤ_[p]) := ⟨fun x => Quotient.liftOn' x g …, …⟩`
- What: An even continuous function on 𝒢 descends to a continuous function on 𝒢⁺.
- How: `Quotient.liftOn'` g; soundness via `QuotientGroup.leftRel_apply`, `Subgroup.mem_zpowers_iff`, case-splitting `Int.even_or_odd` (`neg_one_zpow`) so the {±1}-coset is {x,−x} where g is constant; continuity via `QuotientGroup.isQuotientMap_mk` + `.continuous_iff`.
- Hypotheses: p prime; g continuous and even (g(−u)=g(u)).
- Uses from project: [GPlus]
- Used by: `descendEven_mk`, `descendEven_congr`, `plusSection`, `plusSection_mem_plusPart`, `descendEven_comp_quotientMk`, `projPlus_plusSection`, `plusSection_projPlus`, `descendEven_comp`
- Visibility: public
- Lines: 276–294 (proof: ~15 lines, bundled in anonymous constructor)
- Notes: none

### lemma descendEven_mk
- Type: `(g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u, g (-u) = g u) (u : ℤ_[p]ˣ) : descendEven p g hg (QuotientGroup.mk u) = g u` (`@[simp]`)
- What: Computes descendEven on a coset representative: it just evaluates g.
- How: `rfl`.
- Hypotheses: p prime; g even, u a unit.
- Uses from project: [descendEven, GPlus]
- Used by: `evenPart_even` (no), `plusSection` (map_add'/map_smul'), `descendEven_comp_quotientMk`, `projPlus_plusSection` (no), `descendEven_comp`
- Visibility: public
- Lines: 296–299 (proof: rfl)
- Notes: none

### lemma descendEven_congr
- Type: `{g₁ g₂ : C(ℤ_[p]ˣ, ℤ_[p])} (h : g₁ = g₂) (h₁ …) (h₂ …) : descendEven p g₁ h₁ = descendEven p g₂ h₂`
- What: descendEven depends only on the underlying function (coherence proof irrelevant): equal functions descend equally.
- How: `subst h; rfl`.
- Hypotheses: p prime; g₁ = g₂, both even.
- Uses from project: [descendEven]
- Used by: `plusSection_mem_plusPart`, `projPlus_plusSection`
- Visibility: private
- Lines: 301–305 (proof: 1 line)
- Notes: none

### lemma evenPart_even
- Type: `(hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) (u : ℤ_[p]ˣ) : evenPart p hp2 f (-u) = evenPart p hp2 f u`
- What: The even part is genuinely even: evenPart f (−u) = evenPart f (u).
- How: Unfolds `evenPart` via simp, reduces to `f(-u)+f(-(-u)) = f(u)+f(-u)`, then `neg_neg`, `add_comm`.
- Hypotheses: p ≠ 2; f continuous, u a unit.
- Uses from project: [evenPart, negTranslate]
- Used by: `plusSection`, `plusSection_projPlus`
- Visibility: public
- Lines: 307–312 (proof: 3 lines)
- Notes: none

### lemma evenPart_of_even
- Type: `(hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) (hf : ∀ u, f (-u) = f u) : evenPart p hp2 f = f`
- What: The even part of an already-even function is the function itself.
- How: `ext u`, simp-unfold `evenPart`, reduce to `(2)⁻¹·(f u + f(-u)) = f u`; use `hf`, `← two_mul`, `← mul_assoc`, `isUnit_two_padicInt…val_inv_mul`, `one_mul`.
- Hypotheses: p ≠ 2; f continuous and even.
- Uses from project: [evenPart, negTranslate, PadicLFunctions.isUnit_two_padicInt]
- Used by: `projPlus_plusSection`
- Visibility: private
- Lines: 314–323 (proof: 6 lines)
- Notes: none

### lemma evenPart_comp_negTranslate
- Type: `(hp2 : p ≠ 2) (f : C(ℤ_[p]ˣ, ℤ_[p])) : evenPart p hp2 (f.comp (negTranslate p)) = evenPart p hp2 f`
- What: The even part is invariant under precomposition with the c-translation: evenPart(f∘c) = evenPart f.
- How: `ext u`, simp-unfold `evenPart`, reduce to `f(-u)+f(-(-u)) = f(u)+f(-u)`, then `neg_neg`, `add_comm`.
- Hypotheses: p ≠ 2; f continuous.
- Uses from project: [evenPart, negTranslate]
- Used by: `plusSection_mem_plusPart`
- Visibility: private
- Lines: 325–333 (proof: 3 lines)
- Notes: none

### def plusSection
- Type: `plusSection (hp2 : p ≠ 2) : PadicMeasure p (GPlus p) →ₗ[ℤ_[p]] PadicMeasure p ℤ_[p]ˣ` (toFun ν = bundled measure `f ↦ ν (descendEven (evenPart f))`, with linear-map fields)
- What: The even-part section σ : Λ(𝒢⁺) → Λ(𝒢): (σν)(f) := ν(descend((f + f∘c)/2)); functional-analytic replacement (replan R11.2) for the source's finite-level inverse.
- How: Inner `map_add'`/`map_smul'` reduce, via `← map_add`/`← map_smul` and `QuotientGroup.induction_on`, to additivity/homogeneity of `evenPart` pointwise after `mk` (`descendEven_mk`, simp on `evenPart`, then `ring`); outer `map_add'`/`map_smul'` by rfl.
- Hypotheses: p ≠ 2.
- Uses from project: [GPlus, descendEven, evenPart, evenPart_even, descendEven_mk]
- Used by: `plusSection_mem_plusPart`, `projPlus_plusSection`, `plusSection_projPlus`, `projPlus_surjective`, `plusEquiv`
- Visibility: public
- Lines: 335–367 (proof: ~30 lines bundled across the inner ContinuousLinearMap-like fields)
- Notes: long(30-50) — bundled proof obligations span ~30 lines; no sorry/set_option

### theorem plusSection_mem_plusPart
- Type: `(hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) : plusSection p hp2 ν ∈ plusPart p`
- What: The section lands in the plus part (its image is c-invariant).
- How: `mem_plusPart_iff`; `dirac_neg_one_mul_apply` reduces c-invariance to `evenPart(f∘c)=evenPart f`, closed by `descendEven_congr` with `evenPart_comp_negTranslate`.
- Hypotheses: p ≠ 2; ν a measure on 𝒢⁺.
- Uses from project: [plusSection, plusPart, mem_plusPart_iff, dirac_neg_one_mul_apply, descendEven, evenPart, descendEven_congr, evenPart_comp_negTranslate, negTranslate, GPlus]
- Used by: `plusEquiv`
- Visibility: public
- Lines: 369–379 (proof: ~8 lines)
- Notes: none

### lemma quotientMk_neg
- Type: `(u : ℤ_[p]ˣ) : (QuotientGroup.mk (-u) : GPlus p) = QuotientGroup.mk u`
- What: mk(−u) = mk(u) in 𝒢⁺ (the defining {±1}-collapse).
- How: `QuotientGroup.eq`, `Subgroup.mem_zpowers_iff`, witness 1 via `zpow_one`, `inv_neg`, `neg_mul`, `inv_mul_cancel`.
- Hypotheses: p prime; u a unit.
- Uses from project: [GPlus]
- Used by: `comp_quotientMk_even`
- Visibility: private
- Lines: 381–385 (proof: 2 lines)
- Notes: none

### lemma comp_quotientMk_even
- Type: `(g : C(GPlus p, ℤ_[p])) (u : ℤ_[p]ˣ) : (g.comp (quotientMk p)) (-u) = (g.comp (quotientMk p)) u`
- What: Any pullback g ∘ mk from 𝒢⁺ is an even function on 𝒢.
- How: Changes to `g(mk(-u)) = g(mk u)`, then `quotientMk_neg`.
- Hypotheses: p prime; g a function on 𝒢⁺, u a unit.
- Uses from project: [GPlus, quotientMk, quotientMk_neg]
- Used by: `projPlus_plusSection`, `descendEven_comp_quotientMk` (as hg arg), `projPlus_eq_zero_of_mem_minusPart`
- Visibility: private
- Lines: 387–391 (proof: 2 lines)
- Notes: none

### lemma descendEven_comp_quotientMk
- Type: `(g : C(GPlus p, ℤ_[p])) (hg : ∀ u, (g.comp (quotientMk p)) (-u) = (g.comp (quotientMk p)) u) : descendEven p (g.comp (quotientMk p)) hg = g`
- What: descendEven(g ∘ mk) = g: descending a pullback recovers the original.
- How: `ext x`, `QuotientGroup.induction_on`, then `descendEven_mk` and rfl.
- Hypotheses: p prime; g a function on 𝒢⁺, hg evenness of its pullback.
- Uses from project: [descendEven, quotientMk, GPlus, descendEven_mk]
- Used by: `projPlus_plusSection`
- Visibility: private
- Lines: 393–399 (proof: 3 lines)
- Notes: none

### theorem projPlus_plusSection
- Type: `(hp2 : p ≠ 2) (ν : PadicMeasure p (GPlus p)) : projPlus p (plusSection p hp2 ν) = ν`
- What: π_* ∘ σ = id — the section is a right inverse (hence π_* is surjective).
- How: `LinearMap.ext`; `projPlus_apply`, then `descendEven_congr` with `evenPart_of_even` (since g∘mk is even by `comp_quotientMk_even`), then `descendEven_comp_quotientMk`.
- Hypotheses: p ≠ 2; ν a measure on 𝒢⁺.
- Uses from project: [projPlus, plusSection, projPlus_apply, descendEven, evenPart, descendEven_congr, evenPart_of_even, comp_quotientMk_even, descendEven_comp_quotientMk, quotientMk, GPlus]
- Used by: `projPlus_surjective`, `plusEquiv`
- Visibility: public
- Lines: 401–411 (proof: ~8 lines)
- Notes: none

### lemma descendEven_comp
- Type: `(g : C(ℤ_[p]ˣ, ℤ_[p])) (hg : ∀ u, g (-u) = g u) : (descendEven p g hg).comp (quotientMk p) = g`
- What: Descending an even function and pulling it back recovers it: descend g ∘ mk = g.
- How: `ext u`, change to `descendEven g hg (mk u) = g u`, then `descendEven_mk`.
- Hypotheses: p prime; g continuous and even.
- Uses from project: [descendEven, quotientMk, descendEven_mk]
- Used by: `plusSection_projPlus`
- Visibility: private
- Lines: 413–417 (proof: 1 line)
- Notes: none

### lemma apply_evenPart_of_mem_plusPart
- Type: `(hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ plusPart p) (f : C(ℤ_[p]ˣ, ℤ_[p])) : μ (evenPart p hp2 f) = μ f`
- What: For a c-invariant μ, the even part integrates to the same value: μ(evenPart f) = μ f.
- How: Shows `μ(f∘c)=μf` via `← dirac_neg_one_mul_apply` and `mem_plusPart_iff`; then unfolds `evenPart`, `map_smul`/`map_add`, and clears the 2⁻¹·2 via `isUnit_two_padicInt…val_inv_mul`.
- Hypotheses: p ≠ 2; μ ∈ plusPart, f continuous.
- Uses from project: [plusPart, mem_plusPart_iff, evenPart, dirac_neg_one_mul_apply, negTranslate, PadicLFunctions.isUnit_two_padicInt]
- Used by: `plusSection_projPlus`
- Visibility: private
- Lines: 419–427 (proof: 6 lines)
- Notes: none

### theorem plusSection_projPlus
- Type: `(hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} (hμ : μ ∈ plusPart p) : plusSection p hp2 (projPlus p μ) = μ`
- What: σ ∘ π_* = id on the plus part — a c-invariant measure is determined by its pushforward (injectivity half of RJW TeX 3006–3015).
- How: `LinearMap.ext`; `projPlus_apply`, `descendEven_comp` (descend∘mk = evenPart f), then `apply_evenPart_of_mem_plusPart`.
- Hypotheses: p ≠ 2; μ ∈ plusPart.
- Uses from project: [plusSection, projPlus, plusPart, projPlus_apply, descendEven, evenPart, evenPart_even, descendEven_comp, apply_evenPart_of_mem_plusPart]
- Used by: `plusEquiv`, `projPlus_eq_zero_iff`
- Visibility: public
- Lines: 429–436 (proof: 3 lines)
- Notes: none

### theorem projPlus_surjective
- Type: `(hp2 : p ≠ 2) : Function.Surjective (projPlus p)`
- What: π_* is surjective.
- How: For each ν, exhibits `plusSection p hp2 ν` as a preimage via `projPlus_plusSection`.
- Hypotheses: p ≠ 2.
- Uses from project: [projPlus, plusSection, projPlus_plusSection]
- Used by: unused in file
- Visibility: public
- Lines: 438–440 (proof: term, 1 line)
- Notes: none

### def plusEquiv
- Type: `plusEquiv (hp2 : p ≠ 2) : plusPart p ≃ₗ[ℤ_[p]] PadicMeasure p (GPlus p)`
- What: RJW §11.1 second lemma — the natural isomorphism Λ(𝒢)⁺ ≅ Λ(𝒢⁺), realised by π_* restricted to plusPart with inverse the even-part section.
- How: `LinearEquiv.ofLinear` with forward `pushforward(quotientMk) ∘ subtype` and inverse `plusSection.codRestrict`; the two round-trips are `projPlus_plusSection` and `plusSection_projPlus` (latter via `Subtype.ext`).
- Hypotheses: p ≠ 2.
- Uses from project: [plusPart, GPlus, pushforward, quotientMk, plusSection, plusSection_mem_plusPart, projPlus_plusSection, plusSection_projPlus]
- Used by: unused in file
- Visibility: public
- Lines: 442–453 (proof: term, ~6 lines)
- Notes: none

### lemma projPlus_eq_zero_of_mem_minusPart
- Type: `{ρ : PadicMeasure p ℤ_[p]ˣ} (hρ : ρ ∈ minusPart p) : projPlus p ρ = 0`
- What: The projection kills the minus part: an even pullback g∘mk is integrated to 0 by a c-anti-invariant measure.
- How: `projPlus_apply`; the pullback is c-invariant (`comp_quotientMk_even` ⟹ `heven`), so on an anti-invariant ρ the value equals its negative (`dirac_neg_one_mul_apply`, `mem_minusPart_iff`), hence 0 via `add_self_eq_zero`.
- Hypotheses: p prime; ρ ∈ minusPart.
- Uses from project: [projPlus, minusPart, projPlus_apply, quotientMk, comp_quotientMk_even, dirac_neg_one_mul_apply, mem_minusPart_iff, negTranslate, GPlus]
- Used by: `projPlus_eq_zero_iff`
- Visibility: private
- Lines: 455–469 (proof: ~10 lines)
- Notes: none

### theorem projPlus_eq_zero_iff
- Type: `(hp2 : p ≠ 2) {μ : PadicMeasure p ℤ_[p]ˣ} : projPlus p μ = 0 ↔ μ ∈ minusPart p`
- What: The kernel of π_* is exactly the minus part.
- How: Forward: decompose μ = a + b via `Submodule.existsUnique_add_of_isCompl` (`isCompl_plusPart_minusPart`); projPlus μ = projPlus a (since projPlus kills b), so a = σ(0) = 0 by `plusSection_projPlus`, leaving μ = b ∈ minusPart. Reverse: `projPlus_eq_zero_of_mem_minusPart`.
- Hypotheses: p ≠ 2; μ a measure.
- Uses from project: [projPlus, minusPart, isCompl_plusPart_minusPart, plusSection_projPlus, projPlus_eq_zero_of_mem_minusPart]
- Used by: `ker_projPlus`
- Visibility: public
- Lines: 471–490 (proof: ~18 lines)
- Notes: none (hinges on `Submodule.existsUnique_add_of_isCompl` and `plusSection_projPlus`)

### theorem ker_projPlus
- Type: `(hp2 : p ≠ 2) : RingHom.ker (projPlus p) = Ideal.span {(dirac p (-1 : ℤ_[p]ˣ) - 1 : PadicMeasure p ℤ_[p]ˣ)}`
- What: The kernel of π_* equals the principal ideal ([−1]−[1])·Λ(𝒢) (so Λ(𝒢⁺) ≅ Λ(𝒢)/([−1]−[1])).
- How: `Ideal.ext`; `RingHom.mem_ker`, `projPlus_eq_zero_iff`, `mem_minusPart_iff`, `Ideal.mem_span_singleton`. Forward: dirac(−1)·x = −x ⟹ x = ([−1]−1)·((−½)·x) using `mul_smul_comm`, `sub_mul`, 2⁻¹·2 cancellation. Reverse: ([−1]−1)·c is anti-invariant via `units_dirac_mul_dirac`, `neg_mul_neg`, `units_one_def`.
- Hypotheses: p ≠ 2.
- Uses from project: [projPlus, projPlus_eq_zero_iff, mem_minusPart_iff, dirac, units_dirac_mul_dirac, units_one_def, PadicLFunctions.isUnit_two_padicInt]
- Used by: unused in file
- Visibility: public
- Lines: 492–514 (proof: ~16 lines)
- Notes: none (hinges on `projPlus_eq_zero_iff` and `units_dirac_mul_dirac`)

---

## File Summary

- Total decls: 38 (defs: 9 / lemmas+theorems: 27 / instances: 2)
  - defs (9): `invariants`, `antiInvariants`, `cAct`, `plusPart`, `minusPart`, `quotientMk`, `projPlus`, `negTranslate`, `evenPart`, `descendEven`, `plusSection`, `plusEquiv` — note: counting `abbrev GPlus` separately gives the breakdown below.
  - Precise count: defs/abbrevs = 11 (`invariants`, `antiInvariants`, `cAct`, `plusPart`, `minusPart`, `GPlus`(abbrev), `quotientMk`, `projPlus`, `negTranslate`, `evenPart`, `descendEven`, `plusSection`, `plusEquiv` = 13); lemmas+theorems = 23; instances = 2. Total declarations = **38**.

- Key API (used by ≥3 decls in file):
  - `invariants` (4), `antiInvariants` (4)
  - `plusPart` (7), `minusPart` (4)
  - `cAct` (4), `mem_plusPart_iff` (4)
  - `GPlus` (18), `quotientMk` (≥9), `projPlus` (≥10), `projPlus_apply` (4)
  - `negTranslate` (8), `dirac_neg_one_mul_apply` (3), `evenPart` (8), `descendEven` (8), `plusSection` (5)
  - `descendEven_mk` (3+), `comp_quotientMk_even` (3)

- Unused in file (terminal/exported API): `SMulCommClass` instance, `IsScalarTower` instance, `mul_mem_plusPart`, `mem_plusPart_iff_forall_odd_moment`, `projPlus_dirac`, `deg_projPlus`, `projPlus_surjective`, `plusEquiv`, `ker_projPlus`.

- Decls with `sorry`: none.

- `set_option`: none.

- Proofs >50 lines (OVER-50): none (count: 0).

- Proofs 30–50 lines (long): `plusSection` (~30, bundled inner field proofs) (count: 1).

Note on long-ish bundled proofs that stay <30 each but warrant attention: `descendEven` (~15-line anonymous-constructor proof), `projPlus` (~12 across ring-hom fields), `isCompl_invariants_antiInvariants` (~17), `mem_plusPart_iff_forall_odd_moment` (~16), `projPlus_eq_zero_iff` (~18), `ker_projPlus` (~16) — all under 30, none flagged OVER-50.
