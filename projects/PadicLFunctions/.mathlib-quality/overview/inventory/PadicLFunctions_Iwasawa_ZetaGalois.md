# Inventory: PadicLFunctions/Iwasawa/ZetaGalois.lean

File header: ζ_p as a pseudo-measure on `𝒢⁺` and the ideal `I(𝒢)ζ_p`. RJW (arXiv:2309.15692) §11.1 corollary + §11.2, on the identified Galois side (`𝒢⁺ = GPlus p`). All declarations live in `namespace PadicMeasure` with `variable (p : ℕ) [hp : Fact p.Prime]`, in a `noncomputable section`.

---

### theorem odd_moment_factor_eq_zero
- Type: `{k : ℕ} (hk : Odd k) : (1 - (p : ℚ_[p]) ^ (k - 1)) * ((zetaNeg (k - 1) : ℚ) : ℚ_[p]) = 0`
- What: The p-adic interpolation factor `(1 − p^{k−1})·ζ(1−k)` vanishes for every odd `k ≥ 1`.
- How: Case split on `k = 1` vs `k ≥ 3`. At `k = 1` the Euler factor `1 − p⁰ = 0` (by `simp`); at odd `k ≥ 3`, `ζ(1−k) = −B_k/k = 0` because the odd Bernoulli number vanishes — hinges on `bernoulli_eq_zero_of_odd` together with `zetaNeg`/`Nat.sub_add_cancel`.
- Hypotheses: `k` odd natural number (`Odd k`), with `p` prime via the section variable.
- Uses from project: [zetaNeg]
- Used by: `padicZeta_odd_moment_eq_zero`, `dirac_neg_one_sub_one_mul_padicZeta`
- Visibility: public
- Lines: 33–45 (proof ~8 lines)
- Notes: none

### theorem padicZeta_odd_moment_eq_zero
- Type: `(hp2 : p ≠ 2) (b : ℤ_[p]ˣ) {k : ℕ} (hk : Odd k) (ν : PadicMeasure p ℤ_[p]ˣ) (hν : … (dirac p b − 1) * padicZeta p hp2 = … ν) : ν (unitsPowCM p k) = 0`
- What: The odd moments of every witness `([b]−[1])·ζ_p` vanish (TeX 2992, including the `k = 1` case the membership criterion needs).
- How: Compute the moment via `padicZeta_moments` as `(b^k − 1)·[(1 − p^{k−1})·ζ(1−k)]`, kill the bracket using `odd_moment_factor_eq_zero` and `mul_zero`, then descend the ℚ_p equation to ℤ_p via injectivity of the coercion (`Subtype.coe_injective`).
- Hypotheses: `p ≠ 2`; `b` a p-adic unit; `k` odd; `ν` a measure that is the witness of `([b]−1)·ζ_p` in the quotient field.
- Uses from project: [PadicMeasure, dirac, padicZeta, QuotientField, unitsPowCM, padicZeta_moments, odd_moment_factor_eq_zero]
- Used by: unused in file
- Visibility: public
- Lines: 47–62 (proof ~7 lines)
- Notes: none

### theorem dirac_neg_one_sub_one_mul_padicZeta
- Type: `(hp2 : p ≠ 2) : algebraMap (PadicMeasure p ℤ_[p]ˣ) (QuotientField p) (dirac p (-1 : ℤ_[p]ˣ) − 1) * padicZeta p hp2 = 0`
- What: The descent input — `([−1]−[1])·ζ_p = 0` in `Q(𝒢)`, i.e. ζ_p is invariant under complex conjugation.
- How: Take the `b = −1` pseudo-measure witness `ν` from `padicZeta_isPseudoMeasure`, show all its moments vanish (even ones by `(−1)^k − 1 = 0` via `Even.neg_one_pow`, odd ones by `odd_moment_factor_eq_zero`), conclude `ν = 0` via `eq_zero_of_forall_unitsPowCM_eq_zero`, then rewrite in the witness equation. Hinges on `padicZeta_moments` and `eq_zero_of_forall_unitsPowCM_eq_zero`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [PadicMeasure, QuotientField, dirac, padicZeta, padicZeta_isPseudoMeasure, eq_zero_of_forall_unitsPowCM_eq_zero, padicZeta_moments, unitsPowCM, odd_moment_factor_eq_zero]
- Used by: `padicZeta_witness_neg`
- Visibility: public
- Lines: 64–89 (proof ~16 lines)
- Notes: none

### theorem padicZeta_witness_neg
- Type: `(hp2 : p ≠ 2) (g : ℤ_[p]ˣ) {ν ν' : PadicMeasure p ℤ_[p]ˣ} (hν : witness of (dirac p g − 1)·ζ_p = ν) (hν' : witness of (dirac p (−g) − 1)·ζ_p = ν') : ν = ν'`
- What: Witness symmetry — the witnesses of `([g]−[1])·ζ_p` and `([−g]−[1])·ζ_p` coincide, giving well-definedness of pushing witnesses to `𝒢⁺`.
- How: Factor `[−g]−[g] = [g]·([−1]−[1])` (via `units_dirac_mul_dirac`), so the difference of the two witness equations is `[g]·(([−1]−[1])·ζ_p) = 0` by `dirac_neg_one_sub_one_mul_padicZeta`; conclude the two images agree and apply `IsFractionRing.injective`.
- Hypotheses: `p ≠ 2`; `g` a p-adic unit; `ν`, `ν'` the witnesses of `([g]−1)·ζ_p` and `([−g]−1)·ζ_p` respectively.
- Uses from project: [PadicMeasure, QuotientField, dirac, padicZeta, units_dirac_mul_dirac, dirac_neg_one_sub_one_mul_padicZeta]
- Used by: unused in file
- Visibility: public
- Lines: 91–119 (proof ~19 lines)
- Notes: none

### abbrev QuotientFieldPlus
- Type: `:= FractionRing (PadicMeasure p (GPlus p))`
- What: The total fraction ring `Q(𝒢⁺)` of the Iwasawa algebra `Λ(𝒢⁺)`.
- How: Definitional abbreviation as `FractionRing` of the measure algebra over `GPlus p`.
- Hypotheses: none beyond the section variable `p`.
- Uses from project: [PadicMeasure, GPlus]
- Used by: `toQPlus`, `IsPlusPseudoMeasure`, `padicZetaPlus`, `projPlus_padicZeta_witness`, `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 123–124 (no proof; abbrev)
- Notes: none

### def toQPlus
- Type: `: PadicMeasure p (GPlus p) →+* QuotientFieldPlus p := algebraMap _ _`
- What: The structure (localization) map `Λ(𝒢⁺) → Q(𝒢⁺)`, named once to avoid an unresolved instance metavariable inside def-bodies over the quotient group.
- How: It is literally `algebraMap _ _`; naming sidesteps an elaboration-order postponement trap.
- Hypotheses: none beyond `p`.
- Uses from project: [PadicMeasure, GPlus, QuotientFieldPlus]
- Used by: `IsPlusPseudoMeasure`, `projPlus_padicZeta_witness`, `zetaIdealPlus`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 126–130 (no proof; def body)
- Notes: none

### def IsPlusPseudoMeasure
- Type: `(q : QuotientFieldPlus p) : Prop := ∀ g : GPlus p, ∃ ν : PadicMeasure p (GPlus p), toQPlus p (dirac p g − 1) * q = toQPlus p ν`
- What: The predicate "`q` is a pseudo-measure on `𝒢⁺`" (RJW Def. 3.34 applied to `G = 𝒢⁺`): for every group element the product with `[g]−1` lands in the image of an honest measure.
- How: Direct definition mirroring the augmentation-ideal pseudo-measure condition.
- Hypotheses: `q` an element of the fraction field `Q(𝒢⁺)`.
- Uses from project: [QuotientFieldPlus, PadicMeasure, GPlus, toQPlus, dirac]
- Used by: `isPlusPseudoMeasure_padicZetaPlus`
- Visibility: public
- Lines: 132–135 (no proof; Prop def)
- Notes: none

### theorem dirac_mk_sub_one_mem_nonZeroDivisors
- Type: `(hp2 : p ≠ 2) {a : ℤ_[p]ˣ} (ha : (dirac p a − 1) ∈ nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)) : (dirac p (QuotientGroup.mk a : GPlus p) − 1) ∈ nonZeroDivisors (PadicMeasure p (GPlus p))`
- What: Regularity transports along the projection — if `[a]−[1]` is a non-zero-divisor in `Λ(𝒢)`, then `[ā]−[1]` is one in `Λ(𝒢⁺)`.
- How: Reduce to one-sided cancellation `ν·([ā]−1) = 0 → ν = 0`; lift `ν` along the even-part section `plusSection`, push forward by `projPlus` to get `μ·([a]−1) ∈ ker π_* = minusPart` (via `projPlus_eq_zero_iff`) while also being in `plusPart` (via `mul_mem_plusPart` and `plusSection_mem_plusPart`); the two parts intersect trivially by `isCompl_plusPart_minusPart`, so `μ·([a]−1) = 0`; then `ha` gives `μ = 0` hence `ν = π_* μ = 0`. Hinges on `isCompl_plusPart_minusPart` and `projPlus_eq_zero_iff`.
- Hypotheses: `p ≠ 2`; `[a]−1` a non-zero-divisor in `Λ(𝒢)`.
- Uses from project: [dirac, PadicMeasure, GPlus, plusSection, projPlus, projPlus_dirac, projPlus_plusSection, projPlus_eq_zero_iff, minusPart, plusPart, mul_mem_plusPart, plusSection_mem_plusPart, isCompl_plusPart_minusPart]
- Used by: `padicZetaPlus`, `projPlus_padicZeta_witness`
- Visibility: public
- Lines: 137–172 (proof ~27 lines)
- Notes: none

### def padicZetaPlus
- Type: `(hp2 : p ≠ 2) : QuotientFieldPlus p := IsLocalization.mk' (QuotientFieldPlus p) (projPlus p (zetaNum p …choose)) ⟨dirac p (QuotientGroup.mk …choose_spec.choose) − 1, …⟩`
- What: ζ_p as a pseudo-measure on `𝒢⁺` (object of RJW's corollary, TeX 3033): `ζ_p⁺ := π_*(numerator) / ([ā]−1)` for the same packed integer topological generator `a` as `padicZeta`.
- How: `IsLocalization.mk'` with numerator `projPlus p (zetaNum p m)` and denominator the non-zero-divisor `[ā]−1`, whose regularity is supplied by `dirac_mk_sub_one_mem_nonZeroDivisors` applied to `dirac_sub_one_mem_nonZeroDivisors`/`topGen_pow_ne_one`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [QuotientFieldPlus, projPlus, zetaNum, exists_nat_topological_generator, dirac, GPlus, PadicMeasure, dirac_mk_sub_one_mem_nonZeroDivisors, dirac_sub_one_mem_nonZeroDivisors, topGen_pow_ne_one]
- Used by: `IsPlusPseudoMeasure` (instances), `projPlus_padicZeta_witness`, `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdealPlus`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 174–186 (no proof; def body)
- Notes: none

### theorem projPlus_padicZeta_witness
- Type: `(hp2 : p ≠ 2) (g : ℤ_[p]ˣ) {ν : PadicMeasure p ℤ_[p]ˣ} (hν : witness of (dirac p g − 1)·ζ_p = ν) : toQPlus p (dirac p (QuotientGroup.mk g) − 1) * padicZetaPlus p hp2 = toQPlus p (projPlus p ν)`
- What: Compatibility of the descents — pushing a 𝒢-side witness forward gives the 𝒢⁺-side witness at the image group element ("ζ_p descends").
- How: Using the defining relation `([u]−1)·ζ_p = zetaNum m` (from `IsLocalization.mk'_spec'` applied to `padicZeta`), pull both witness identities back to `Λ(ℤ_p^×)` via `IsFractionRing.injective` to get `([u]−1)·ν = ([g]−1)·zetaNum m`; push forward by `projPlus` (a ring hom) to `([ḡ]−1)·π_*(zetaNum m) = ([ū]−1)·π_*ν`; then conclude in `Q(𝒢⁺)` by cancelling the unit `algebraMap c` (where `c = [ū]−1`, a unit via `IsLocalization.map_units`) and reducing to the pushed-forward identity with `linear_combination`. Hinges on `IsLocalization.mk'_spec`/`mk'_spec'` and `projPlus_dirac`.
- Hypotheses: `p ≠ 2`; `g` a p-adic unit; `ν` the 𝒢-side witness of `([g]−1)·ζ_p`.
- Uses from project: [PadicMeasure, QuotientField, dirac, padicZeta, toQPlus, GPlus, padicZetaPlus, projPlus, exists_nat_topological_generator, zetaNum, projPlus_dirac, QuotientFieldPlus, dirac_mk_sub_one_mem_nonZeroDivisors, dirac_sub_one_mem_nonZeroDivisors, topGen_pow_ne_one]
- Used by: `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 188–236 (proof ~40 lines)
- Notes: long(30-50); uses `classical`

### theorem isPlusPseudoMeasure_padicZetaPlus
- Type: `(hp2 : p ≠ 2) : IsPlusPseudoMeasure p (padicZetaPlus p hp2)`
- What: RJW §11.1 Corollary (TeX 3033–3039) — the p-adic zeta function is a pseudo-measure on `𝒢⁺`.
- How: Given any `gPlus : GPlus p`, lift it to `g : ℤ_[p]ˣ` via `QuotientGroup.mk_surjective`, take its 𝒢-side pseudo-measure witness `ν` from `padicZeta_isPseudoMeasure`, and transport forward with `projPlus_padicZeta_witness` to supply the 𝒢⁺-side witness `projPlus p ν`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [IsPlusPseudoMeasure, padicZetaPlus, padicZeta_isPseudoMeasure, projPlus, projPlus_padicZeta_witness, GPlus]
- Used by: unused in file
- Visibility: public
- Lines: 238–246 (proof ~5 lines)
- Notes: none

### def zetaIdeal
- Type: `(hp2 : p ≠ 2) : Ideal (PadicMeasure p ℤ_[p]ˣ)` with `carrier := {x | ∃ l ∈ augmentationIdeal p, algebraMap … x = algebraMap … l * padicZeta p hp2}`
- What: The ideal `I(𝒢)ζ_p` (RJW Proposition, TeX 3052) — measures of the form `λ·ζ_p` with `λ` in the augmentation ideal.
- How: Bundle the carrier set with the three ideal-closure proofs: `add_mem'` via `Ideal.add_mem` + distributivity (`add_mul`), `zero_mem'` via `0` and `zero_mul`, `smul_mem'` via `Submodule.smul_mem` + `mul_assoc`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [PadicMeasure, augmentationIdeal, QuotientField, padicZeta]
- Used by: `mem_zetaIdeal_iff`, `zetaIdeal_eq_span`
- Visibility: public
- Lines: 250–265 (structure-field proofs ~8 lines total)
- Notes: none

### lemma mem_zetaIdeal_iff
- Type: `(hp2 : p ≠ 2) {x : PadicMeasure p ℤ_[p]ˣ} : x ∈ zetaIdeal p hp2 ↔ ∃ l ∈ augmentationIdeal p, algebraMap … x = algebraMap … l * padicZeta p hp2`
- What: Unfolds membership in `zetaIdeal` to the existential definition.
- How: `Iff.rfl` (definitional unfolding).
- Hypotheses: `p ≠ 2`; `x` a measure.
- Uses from project: [PadicMeasure, zetaIdeal, augmentationIdeal, QuotientField, padicZeta]
- Used by: unused in file
- Visibility: public
- Lines: 267–271 (proof 1 line)
- Notes: none

### theorem zetaIdeal_eq_span
- Type: `(hp2 : p ≠ 2) {b : ℤ_[p]ˣ} (hb : ∀ n, Subgroup.zpowers (unitsToZModPow p n b) = ⊤) {ν : PadicMeasure p ℤ_[p]ˣ} (hν : witness of (dirac p b − 1)·ζ_p = ν) : zetaIdeal p hp2 = Ideal.span {ν}`
- What: Computational description — `I(𝒢)ζ_p` is the principal ideal generated by any witness `ν` of `([b]−[1])·ζ_p` at a topological generator `b`.
- How: Show `[b]−1 ∈ augmentationIdeal` (its degree is `1 − 1 = 0`). Prove `le_antisymm`: (⊆) any `x = l·ζ_p` with `l = ([b]−1)·ρ` (using `augmentationIdeal_eq_span` + `Ideal.mem_span_singleton`) equals `ρ·ν` after cancelling into the localization (`IsFractionRing.injective`); (⊇) `ν` itself is the witness `([b]−1)·ζ_p`. Hinges on `augmentationIdeal_eq_span`.
- Hypotheses: `p ≠ 2`; `b` a topological generator (image generates each `ZMod p^n`); `ν` its witness.
- Uses from project: [PadicMeasure, dirac, padicZeta, QuotientField, zetaIdeal, augmentationIdeal, unitsToZModPow, augmentationIdeal_eq_span, deg]
- Used by: unused in file
- Visibility: public
- Lines: 273–298 (proof ~18 lines)
- Notes: none

### theorem augmentationIdealPlus_eq_span
- Type: `(hp2 : p ≠ 2) {a : ℤ_[p]ˣ} (ha : ∀ n, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) : augmentationIdeal p (G := GPlus p) = Ideal.span {(dirac p (QuotientGroup.mk a) − 1 : PadicMeasure p (GPlus p))}`
- What: The image `ā` of a topological generator generates the augmentation ideal of `Λ(𝒢⁺)`: `I(𝒢⁺) = ([ā]−[1])·Λ(𝒢⁺)`.
- How: `le_antisymm`: (⊆) lift `y = π_* x` via `projPlus_surjective`, show `deg x = deg(π_* x) = 0` so `x ∈ I(𝒢)` (using `deg_projPlus`), transfer principality from `Λ(𝒢)` via `augmentationIdeal_eq_span`, push the generated element forward by `projPlus_dirac`; (⊇) the generator `[ā]−1` has degree `1 − 1 = 0`. Hinges on `augmentationIdeal_eq_span`, `projPlus_surjective`, and `deg_projPlus`.
- Hypotheses: `p ≠ 2`; `a` a topological generator.
- Uses from project: [augmentationIdeal, GPlus, dirac, QuotientGroup.mk (via GPlus), PadicMeasure, unitsToZModPow, projPlus_surjective, deg_projPlus, augmentationIdeal_eq_span, projPlus, projPlus_dirac, deg]
- Used by: `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 300–326 (proof ~19 lines)
- Notes: none

### def zetaIdealPlus
- Type: `(hp2 : p ≠ 2) : Ideal (PadicMeasure p (GPlus p))` with `carrier := {x | ∃ l ∈ augmentationIdeal p (G := GPlus p), toQPlus p x = toQPlus p l * padicZetaPlus p hp2}`
- What: The ideal `I(𝒢⁺)ζ_p` (RJW Proposition, TeX 3052) — the right-hand side of Iwasawa's theorem, the analogue of `zetaIdeal` on `Λ(𝒢⁺)`.
- How: Same bundling as `zetaIdeal`: `add_mem'` via `Ideal.add_mem` + `add_mul`, `zero_mem'` via `zero_mul`, `smul_mem'` via `Submodule.smul_mem` + `mul_assoc`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [PadicMeasure, GPlus, augmentationIdeal, toQPlus, padicZetaPlus]
- Used by: `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`
- Visibility: public
- Lines: 328–341 (structure-field proofs ~8 lines total)
- Notes: none

### lemma mem_zetaIdealPlus_iff
- Type: `(hp2 : p ≠ 2) {x : PadicMeasure p (GPlus p)} : x ∈ zetaIdealPlus p hp2 ↔ ∃ l ∈ augmentationIdeal p (G := GPlus p), toQPlus p x = toQPlus p l * padicZetaPlus p hp2`
- What: Unfolds membership in `zetaIdealPlus` to the existential definition.
- How: `Iff.rfl` (definitional unfolding).
- Hypotheses: `p ≠ 2`; `x` a measure on `GPlus p`.
- Uses from project: [PadicMeasure, GPlus, zetaIdealPlus, augmentationIdeal, toQPlus, padicZetaPlus]
- Used by: unused in file
- Visibility: public
- Lines: 343–346 (proof 1 line)
- Notes: none

### theorem zetaIdealPlus_eq_span
- Type: `(hp2 : p ≠ 2) {a : ℤ_[p]ˣ} (ha : ∀ n, Subgroup.zpowers (unitsToZModPow p n a) = ⊤) {ν : PadicMeasure p ℤ_[p]ˣ} (hν : witness of (dirac p a − 1)·ζ_p = ν) : zetaIdealPlus p hp2 = Ideal.span {projPlus p ν}`
- What: Computational description — `I(𝒢⁺)ζ_p` is the principal ideal generated by the pushed-forward witness `π_* ν`.
- How: Get the 𝒢⁺-side witness identity at `ā` by pushing `hν` forward via `projPlus_padicZeta_witness`; show `[ā]−1 ∈ augmentationIdeal` (degree `1 − 1 = 0`). `le_antisymm`: (⊆) any `x = l·ζ_p⁺` with `l = ([ā]−1)·ρ` (using `augmentationIdealPlus_eq_span` + `Ideal.mem_span_singleton`) factors through `π_* ν` after `IsFractionRing.injective`; (⊇) `π_* ν` is the witness `([ā]−1)·ζ_p⁺`. Hinges on `projPlus_padicZeta_witness` and `augmentationIdealPlus_eq_span`.
- Hypotheses: `p ≠ 2`; `a` a topological generator; `ν` its 𝒢-side witness.
- Uses from project: [PadicMeasure, GPlus, dirac, padicZeta, QuotientField, zetaIdealPlus, projPlus, unitsToZModPow, padicZetaPlus, toQPlus, QuotientFieldPlus, augmentationIdeal, projPlus_padicZeta_witness, augmentationIdealPlus_eq_span, deg]
- Used by: unused in file
- Visibility: public
- Lines: 348–374 (proof ~21 lines)
- Notes: none

---

## File Summary

**Total declarations: 15** (defs: 5 — `toQPlus`, `IsPlusPseudoMeasure`, `padicZetaPlus`, `zetaIdeal`, `zetaIdealPlus`; abbrevs: 1 — `QuotientFieldPlus`; lemmas+theorems: 9 — `odd_moment_factor_eq_zero`, `padicZeta_odd_moment_eq_zero`, `dirac_neg_one_sub_one_mul_padicZeta`, `padicZeta_witness_neg`, `dirac_mk_sub_one_mem_nonZeroDivisors`, `projPlus_padicZeta_witness`, `isPlusPseudoMeasure_padicZetaPlus`, `mem_zetaIdeal_iff`, `zetaIdeal_eq_span`, `augmentationIdealPlus_eq_span`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span` → 12 lemmas+theorems; instances: 0). Counting `abbrev QuotientFieldPlus` separately, the breakdown is 5 defs / 12 lemmas+theorems / 0 instances / 1 abbrev = **18 declarations** if abbrev and the two `mem_*_iff` lemmas are all counted; the file contains **18 named declarations** total.

**Key API (used by ≥3 in this file):**
- `padicZetaPlus` — used by ≥6 (`projPlus_padicZeta_witness`, `isPlusPseudoMeasure_padicZetaPlus`, `zetaIdealPlus`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`, plus the pseudo-measure predicate instance).
- `toQPlus` — used by 5 (`IsPlusPseudoMeasure`, `projPlus_padicZeta_witness`, `zetaIdealPlus`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`).
- `QuotientFieldPlus` — used by 5 (`toQPlus`, `IsPlusPseudoMeasure`, `padicZetaPlus`, `projPlus_padicZeta_witness`, `zetaIdealPlus_eq_span`).
- `dirac_mk_sub_one_mem_nonZeroDivisors` — used by 2 (`padicZetaPlus`, `projPlus_padicZeta_witness`); `odd_moment_factor_eq_zero` — used by 2.

**Unused within this file (terminal/exported API):** `padicZeta_odd_moment_eq_zero`, `padicZeta_witness_neg`, `isPlusPseudoMeasure_padicZetaPlus`, `mem_zetaIdeal_iff`, `zetaIdeal_eq_span`, `mem_zetaIdealPlus_iff`, `zetaIdealPlus_eq_span`. (These are the file's externally-consumed theorems/corollaries.)

**Declarations with `sorry`:** none.

**`set_option`:** none. (`classical` is used as a tactic inside `projPlus_padicZeta_witness`, not a `set_option`.)

**Proofs > 50 lines (OVER-50):** none (count: 0).

**Proofs 30–50 lines long(30-50):** 1 — `projPlus_padicZeta_witness` (~40 lines, lines 188–236).

**Note on counts:** the file has 18 named declarations (1 abbrev + 5 defs + 12 lemmas/theorems + 0 instances). Two are pure `Iff.rfl` membership unfoldings (`mem_zetaIdeal_iff`, `mem_zetaIdealPlus_iff`). The longest single proof body is `projPlus_padicZeta_witness` at ~40 lines; nothing exceeds 50. No `sorry`, no `set_option`, no `TODO`.
