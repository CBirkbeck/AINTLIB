# Inventory: ./HasseWeil/Pic0/ClassGroupNorm.lean

**File summary**: 940 lines; 30 declarations (8 defs, 22 theorems, 0 instances); 0 sorries; 9 `set_option` occurrences. Builds the class-group relative norm `ClassGroup S →* ClassGroup R` and the extension map `ClassGroup R →* ClassGroup S`, then proves `relNorm (map c) = c^n` (the arithmetic dual relation) and the `PerfectField`-free identity `relNorm 𝔭 = comap 𝔭` at residue degree 1 (Silverman III.4.10(a)).

---

## Declarations

### `noncomputable def relNorm0`
- **Type**: `(Ideal S)⁰ →* (Ideal R)⁰`
- **What**: Packages `Ideal.relNorm R` as a monoid homomorphism on nonzero-divisor ideals.
- **How**: Nonzero-preservation uses `Ideal.relNorm_eq_bot_iff`; `map_one'` and `map_mul'` follow from `simp` via mathlib's `Ideal.relNorm` multiplicativity.
- **Hypotheses**: S/R finite Dedekind extension, module-finite, torsion-free.
- **Uses from project**: none
- **Used by**: `mk0CompRelNorm0`, `ClassGroup.relNorm_mk0`, `relNorm0_eq_comap_of_inertiaDeg_one`, `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 33–44 (proof ~11 lines)
- **Notes**: none

---

### `noncomputable def mk0CompRelNorm0`
- **Type**: `(Ideal S)⁰ →* ClassGroup R`
- **What**: The composite monoid hom "apply relNorm0 then take the class group element".
- **How**: Direct composition `ClassGroup.mk0 ∘ relNorm0`.
- **Hypotheses**: same as `relNorm0`.
- **Uses from project**: `relNorm0`
- **Used by**: `mk0CompRelNorm0_apply`, `mk0CompRelNorm0_eq_of_mk0_eq`, `ClassGroup.relNorm`
- **Visibility**: public
- **Lines**: 46–47 (term-mode, 1 line)
- **Notes**: none

---

### `theorem mk0CompRelNorm0_apply`
- **Type**: `mk0CompRelNorm0 I = ClassGroup.mk0 (relNorm0 I)`
- **What**: Definitional unfolding of `mk0CompRelNorm0` at a concrete element, tagged `@[simp]`.
- **How**: `rfl`.
- **Hypotheses**: none beyond context.
- **Uses from project**: `mk0CompRelNorm0`, `relNorm0`
- **Used by**: `mk0CompRelNorm0_eq_of_mk0_eq`
- **Visibility**: public
- **Lines**: 50–51 (1 line)
- **Notes**: none

---

### `theorem mk0CompRelNorm0_eq_of_mk0_eq`
- **Type**: `ClassGroup.mk0 I = ClassGroup.mk0 J → mk0CompRelNorm0 I = mk0CompRelNorm0 J`
- **What**: Well-definedness of the class-group descent: equal integral ideal classes have equal norms.
- **How**: Reduces via `ClassGroup.mk0_eq_mk0_iff` to the principal-ideal case; uses `Ideal.relNorm_singleton` and `Algebra.intNorm_ne_zero` (which needs `FiniteDimensional (FractionRing R) (FractionRing S)`, supplied by the locally-built `FractionRing.liftAlgebra` algebra).
- **Hypotheses**: S/R finite Dedekind extension.
- **Uses from project**: `mk0CompRelNorm0_apply`
- **Used by**: `ClassGroup.relNorm` (3 times in `map_one'`/`map_mul'`), `ClassGroup.relNorm_mk0`
- **Visibility**: public
- **Lines**: 61–84 (proof ~23 lines)
- **Notes**: none

---

### `noncomputable def ClassGroup.relNorm`
- **Type**: `ClassGroup S →* ClassGroup R`
- **What**: The class-group relative norm, the main construction of the file.
- **How**: Surjectivity of `ClassGroup.mk0` supplies integral representatives; `mk0CompRelNorm0_eq_of_mk0_eq` gives well-definedness; `Function.surjInv_eq` unfolds the `surjInv` choice at the identity and product.
- **Hypotheses**: S/R finite Dedekind extension.
- **Uses from project**: `mk0CompRelNorm0`, `mk0CompRelNorm0_eq_of_mk0_eq`
- **Used by**: `ClassGroup.relNorm_mk0`, `ClassGroup.relNorm_mk0'`, `ClassGroup.relNorm_one`, `ClassGroup.relNorm_mul`, `ClassGroup.relNorm_comp_map`, `ClassGroup.relNorm_comp_map_eq`
- **Visibility**: public
- **Lines**: 92–103 (proof ~10 lines)
- **Notes**: none

---

### `theorem ClassGroup.relNorm_mk0`
- **Type**: `ClassGroup.relNorm (ClassGroup.mk0 I) = ClassGroup.mk0 (relNorm0 I)`
- **What**: Computation rule for `relNorm` on an integral representative; `@[simp]`.
- **How**: Chains `mk0CompRelNorm0_eq_of_mk0_eq` (well-definedness at `surjInv`) with `mk0CompRelNorm0_apply` (unfolding).
- **Hypotheses**: S/R finite Dedekind extension.
- **Uses from project**: `mk0CompRelNorm0_eq_of_mk0_eq`, `mk0CompRelNorm0_apply`, `ClassGroup.relNorm`, `relNorm0`
- **Used by**: `ClassGroup.relNorm_mk0'`, `ClassGroup.relNorm_comp_map`
- **Visibility**: public
- **Lines**: 109–112 (proof ~3 lines)
- **Notes**: none

---

### `theorem ClassGroup.relNorm_mk0'`
- **Type**: `ClassGroup.relNorm (ClassGroup.mk0 I) = ClassGroup.mk0 ⟨Ideal.relNorm R I, …⟩`
- **What**: Alternative spelling of the computation rule with the nonzero membership proof written out explicitly.
- **How**: Direct application of `ClassGroup.relNorm_mk0`.
- **Hypotheses**: S/R finite Dedekind extension.
- **Uses from project**: `ClassGroup.relNorm_mk0`
- **Used by**: unused in file (external consumers)
- **Visibility**: public
- **Lines**: 116–122 (term-mode, 1 line)
- **Notes**: none

---

### `theorem Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing`
- **Type**: For a local Dedekind domain S over a Dedekind R, maximal prime p ≠ ⊥ lying under the maximal ideal m of S: `relNorm R m = p ^ inertiaDeg p m`.
- **What**: PerfectField-free local base version of `relNorm 𝔪 = p^f`; bypasses mathlib's Galois-closure route.
- **How**: Shows `p·S = m^e` via `Ideal.map_algebraMap_eq_finset_prod_pow` + `IsLocalRing.primesOver_eq` (unique prime); uses `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` (e·f = [Frac S : Frac R]) to get `(relNorm m)^e = p^(e·f)`; factors `relNorm m = p^s` via `Ideal.exists_relNorm_eq_pow_of_isPrime`, then cancels via `pow_injective_of_not_isUnit`.
- **Hypotheses**: S local Dedekind, R Dedekind, S/R module-finite torsion-free, p maximal nonzero, m lies over p.
- **Uses from project**: none
- **Used by**: `Ideal.relNorm_maximalIdeal_eq_under_of_inertiaDeg_one_of_isLocalRing`
- **Visibility**: public
- **Lines**: 182–223 (`set_option maxHeartbeats 800000`, has comment; proof ~32 lines)
- **Notes**: Proof strictly >30 lines. `set_option maxHeartbeats 800000` with comment "fraction-field tower + residue-degree finrank bookkeeping need elaboration room."

---

### `theorem Ideal.relNorm_maximalIdeal_eq_under_of_inertiaDeg_one_of_isLocalRing`
- **Type**: If inertiaDeg = 1 then `relNorm R m = m.under R` (local base, no PerfectField).
- **What**: Corollary of the above at f = 1: the power collapses via `pow_one`.
- **How**: Applies `Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing` then rewrites with `hf` and `pow_one`.
- **Hypotheses**: Same as `…_of_isLocalRing` plus inertiaDeg = 1.
- **Uses from project**: `Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing`
- **Used by**: (subsumed by `Ideal.relNorm_eq_under_of_inertiaDeg_one`; no direct callers in file)
- **Visibility**: public
- **Lines**: 230–243 (proof ~13 lines)
- **Notes**: The docstring explicitly states it is now subsumed by the general-base theorem.

---

### `theorem intNorm_eq_intNorm_of_common_fractionField`
- **Type**: For integral closures B, B' of A in a common field L, `intNorm A B x = intNorm A B' (algebraMap B B' x)`.
- **What**: Shows `intNorm` depends only on the fraction-field level, not the integral model.
- **How**: Injects via `IsFractionRing.injective A K`, applies `Algebra.algebraMap_intNorm` to both B and B' with the same ambient field L, and uses the scalar tower `B → B' → L` to identify the two field maps.
- **Hypotheses**: A, B, B' integrally closed domains, B and B' both integral closures of A in L, compatible algebra maps, FiniteDimensional K L.
- **Uses from project**: none
- **Used by**: `relNorm_eq_relNorm_localization`
- **Visibility**: public
- **Lines**: 267–282 (proof ~5 lines)
- **Notes**: none

---

### `theorem relNorm_eq_relNorm_localization`
- **Type**: For a PID B and B' sharing the fraction field, and a principal ideal Q of B: `relNorm A Q = relNorm A (Q.map (algebraMap B B'))`.
- **What**: Top-localization invariance of relNorm when the principal generator is transported.
- **How**: Writes Q = span{π}, uses `Ideal.relNorm_singleton`, `Ideal.map_span`, and `intNorm_eq_intNorm_of_common_fractionField` to equate the generators.
- **Hypotheses**: A, B (Dedekind PID), B' (Dedekind) all sharing fraction field L; B module-finite over A; Q principal; IsPrincipalIdealRing B.
- **Uses from project**: `intNorm_eq_intNorm_of_common_fractionField`
- **Used by**: (no direct callers in file; mentioned as the engine behind `relNorm_map_localization`)
- **Visibility**: public
- **Lines**: 300–318 (proof ~5 lines)
- **Notes**: The caveat docstring notes this does NOT discharge the non-local case because Localization.AtPrime is not module-finite over A.

---

### `theorem map_eq_top_of_under_ne`
- **Type**: If P is maximal in S and q is a maximal ideal of R different from P.under R, then `P.map (algebraMap S Sₚ) = ⊤` (where Sₚ is the semilocal localization away from q).
- **What**: Extension of a prime to the semilocal localization at a different prime collapses to ⊤.
- **How**: Picks an element in P.under R outside q, shows its image is a unit in the localization, then uses `Ideal.eq_top_of_isUnit_mem`.
- **Hypotheses**: P maximal in S, q maximal in R, P.under R ≠ q.
- **Uses from project**: none
- **Used by**: `relNorm_eq_under_of_localized`
- **Visibility**: public
- **Lines**: 342–355 (proof ~13 lines)
- **Notes**: `omit` drops main context's `IsDomain R` etc. (uses fewer hypotheses).

---

### `theorem relNorm_map_localization`
- **Type**: `(relNorm R P).map (R → Rₚ) = relNorm Rₚ (P.map (S → Sₚ))`
- **What**: RelNorm commutes with localizing both base and top at a maximal prime q.
- **How**: Direct application of mathlib's `Ideal.spanIntNorm_localization` (with M = q.primeCompl).
- **Hypotheses**: P ideal of S, q maximal in R, NeZero q; full Dedekind/finite context.
- **Uses from project**: none
- **Used by**: `relNorm_eq_under_of_localized` (twice)
- **Visibility**: public
- **Lines**: 368–375 (`set_option synthInstance.maxHeartbeats 400000`, comment "semilocal Sₚ instance bundle"; proof ~5 lines)
- **Notes**: none

---

### `theorem relNorm_eq_under_of_localized`
- **Type**: Given the per-prime DVR hypothesis `hlocal : relNorm Rₚ (P·Sₚ) = maximalIdeal Rₚ`, then `relNorm R P = P.under R`.
- **What**: Global-to-semilocal reduction: the general identity relNorm = comap at f = 1 follows from a single DVR-base per-prime input.
- **How**: Uses `Ideal.eq_of_localization_maximal` to check at every maximal q; at q ≠ p uses `relNorm_map_localization` + `map_eq_top_of_under_ne` + `Ideal.relNorm_top`; at q = p applies the hypothesis via `Localization.AtPrime.map_eq_maximalIdeal`.
- **Hypotheses**: P maximal in S, P ≠ ⊥, and the per-prime hypothesis hlocal.
- **Uses from project**: `relNorm_map_localization`, `map_eq_top_of_under_ne`
- **Used by**: `Ideal.relNorm_eq_under_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 395–414 (`set_option synthInstance.maxHeartbeats 400000`, comment "semilocal Sₚ instance bundle"; proof ~13 lines)
- **Notes**: none

---

### `theorem Ring.ord_finset_prod`
- **Type**: For nonzero elements cᵢ in a commutative domain, `Ring.ord (∏ᵢ cᵢ) = ∑ᵢ Ring.ord cᵢ`.
- **What**: Additivity of the order-of-vanishing under finite products.
- **How**: Induction on the finset using `Ring.ord_mul` and `Finset.prod_ne_zero_iff` for the nonzero divisor side-condition.
- **Hypotheses**: All factors nonzero.
- **Uses from project**: none
- **Used by**: `relNorm_length_eq_span`
- **Visibility**: public
- **Lines**: 438–448 (proof ~10 lines)
- **Notes**: none

---

### `theorem relNorm_length_eq_span`
- **Type**: `Module.length Rp (Rp ⧸ relNorm Rp (span{π})) = Module.length Rp (Sp ⧸ span{π})`
- **What**: The norm-length identity: for a free-finite Rp-algebra Sp (PID base) and nonzero π, the Rp-module lengths of the two quotients agree.
- **How**: Uses Smith normal form coefficients cᵢ from `Ideal.quotientEquivPiSpan`; relates `Algebra.norm` to the product of cᵢ via `associated_norm_prod_smith`; uses `Ring.ord_finset_prod` + `Ring.ord = length(·⧸·)` identity; combines with `Module.length_pi_of_fintype`.
- **Hypotheses**: Rp PID integrally closed, Sp Dedekind integrally closed, module-finite torsion-free, π ≠ 0.
- **Uses from project**: `Ring.ord_finset_prod`
- **Used by**: `relNorm_eq_maximalIdeal_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 458–486 (proof ~28 lines)
- **Notes**: none

---

### `theorem isSimpleModule_quot_of_inertiaDeg_one`
- **Type**: If Q lies over m with inertiaDeg m Q = 1, then `IsSimpleModule Rp (Sp ⧸ Q)`.
- **What**: At residue degree 1, the quotient Sp/Q is a simple Rp-module (isomorphic to Rp/m).
- **How**: Builds the residue algebra `algebraQuotientOfLEComap` (diamond-free construction); shows finrank 1 via `Ideal.inertiaDeg_algebraMap`; surjectivity of residue map via equal-rank injectivity-surjectivity equivalence; lifts to Rp-surjectivity via the scalar tower; identifies the kernel; applies `isSimpleModule_iff_quot_maximal`.
- **Hypotheses**: Q maximal in Sp, m maximal in Rp, Q lies over m, inertiaDeg = 1.
- **Uses from project**: none
- **Used by**: `relNorm_eq_maximalIdeal_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 501–534 (`set_option maxHeartbeats 800000`, comment about residue algebra structure/diamond; proof ~33 lines)
- **Notes**: Proof >30 lines. Explicitly avoids the `algebraOfLiesOver` diamond.

---

### `theorem relNorm_eq_maximalIdeal_of_inertiaDeg_one`
- **Type**: For a DVR Rp (local PID), Dedekind PID Sp, nonzero maximal Q over maximalIdeal Rp with inertiaDeg = 1: `relNorm Rp Q = maximalIdeal Rp`.
- **What**: The per-prime relative norm over a DVR base at residue degree 1 (the PerfectField-free closed residual).
- **How**: `isSimpleModule_quot_of_inertiaDeg_one` gives `length(Sp/Q) = 1`; `relNorm_length_eq_span` transports to `length(Rp/relNorm Q) = 1`; simplicity of the quotient then `IsLocalRing.eq_maximalIdeal` pins relNorm Q = maximalIdeal.
- **Hypotheses**: Rp local Dedekind PID, Sp Dedekind PID, module-finite torsion-free, Q maximal nonzero over maximalIdeal Rp, inertiaDeg = 1.
- **Uses from project**: `isSimpleModule_quot_of_inertiaDeg_one`, `relNorm_length_eq_span`
- **Used by**: `relNorm_map_eq_maximalIdeal_general`
- **Visibility**: public
- **Lines**: 536–572 (`set_option maxHeartbeats 800000`, comment about module-length chain; proof ~14 lines)
- **Notes**: none

---

### `theorem relNorm_map_eq_maximalIdeal_general`
- **Type**: Over abstract semilocal Rp/Sp localisation data, `relNorm Rp (P·Sₚ) = maximalIdeal Rp` (for P maximal over p with inertiaDeg p P = 1).
- **What**: Instantiates `relNorm_eq_maximalIdeal_of_inertiaDeg_one` at the general semilocal data, providing the `hlocal` hypothesis needed by `relNorm_eq_under_of_localized`.
- **How**: Transports IsPrime, LiesOver, nonzero-ness, IsMaximal, and inertiaDeg of P·Sₚ via `IsLocalization.AtPrime` API; then applies `relNorm_eq_maximalIdeal_of_inertiaDeg_one`.
- **Hypotheses**: Abstract Rp/Sp localisation data with full Dedekind/PID/finite/torsion-free instances, P maximal in S with inertiaDeg = 1.
- **Uses from project**: `relNorm_eq_maximalIdeal_of_inertiaDeg_one`
- **Used by**: `Ideal.relNorm_eq_under_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 574–612 (`set_option synthInstance.maxHeartbeats 400000`, comment "abstract Rp/Sₚ localisation instance bundle"; proof ~13 lines)
- **Notes**: none

---

### `theorem Ideal.relNorm_eq_under_of_inertiaDeg_one`
- **Type**: For a maximal P ≠ ⊥ of S with inertiaDeg (P.under R) P = 1: `relNorm R P = P.under R`.
- **What**: Main general-base PerfectField-free theorem: relNorm = comap at f = 1.
- **How**: Pre-establishes all heavy semilocal instances explicitly (to keep elaboration in budget), then reduces to `relNorm_eq_under_of_localized` with the `hlocal` input supplied by `relNorm_map_eq_maximalIdeal_general`.
- **Hypotheses**: S/R finite Dedekind extension; P maximal nonzero; inertiaDeg = 1.
- **Uses from project**: `relNorm_eq_under_of_localized`, `relNorm_map_eq_maximalIdeal_general`
- **Used by**: `relNorm0_eq_comap_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 614–668 (two `set_option` calls: `synthInstance.maxHeartbeats 1000000` and `maxHeartbeats 1600000`, comments about "expensive semilocal Sₚ/DVR Rₚ instance bundle"; proof ~23 lines)
- **Notes**: Two stacked `set_option` directives.

---

### `theorem relNorm0_eq_comap_of_inertiaDeg_one`
- **Type**: `(relNorm0 P : Ideal R) = Ideal.comap (algebraMap R S) (P : Ideal S)`
- **What**: The `(Ideal R)⁰`-packaged form of `relNorm_eq_under_of_inertiaDeg_one`.
- **How**: Direct application of `Ideal.relNorm_eq_under_of_inertiaDeg_one` using `mem_nonZeroDivisors_iff_ne_zero`.
- **Hypotheses**: P a nonzero maximal ideal (as a nonzerodivisor), inertiaDeg = 1.
- **Uses from project**: `relNorm0`, `Ideal.relNorm_eq_under_of_inertiaDeg_one`
- **Used by**: `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`
- **Visibility**: public
- **Lines**: 674–680 (term-mode, 2 lines)
- **Notes**: none

---

### `theorem ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one`
- **Type**: `ClassGroup.mk0 (relNorm0 P) = ClassGroup.mk0 ⟨comap (algebraMap R S) P, hcomap⟩`
- **What**: The class-group level form: mk0 of relNorm0 equals mk0 of the contraction at inertiaDeg 1. This is the Pic⁰ naturality bridge at a rational point.
- **How**: `congrArg ClassGroup.mk0` applied to `Subtype.ext` of `relNorm0_eq_comap_of_inertiaDeg_one`.
- **Hypotheses**: P nonzero maximal, inertiaDeg = 1, hcomap membership.
- **Uses from project**: `relNorm0_eq_comap_of_inertiaDeg_one`, `relNorm0`
- **Used by**: unused in file (external consumer)
- **Visibility**: public
- **Lines**: 690–696 (term-mode, 1 line)
- **Notes**: none

---

### `theorem Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one`
- **Type**: For an F-algebra R, an F-algebra hom g : R →ₐ[F] R module-finite over itself, and a maximal M with finrank F (R/M) = 1: `inertiaDeg (M.under R) M = 1`.
- **What**: Shows that at a rational point (residue field = F), the inertia degree is 1. Silverman III.4.10(a), f = 1 direction.
- **How**: Diamond-free: does NOT use `finrank_mul_finrank`; instead directly bounds finrank(R/M.under R, R/M) ≤ 1 via surjectivity of the residue map (derived by injectivity/surjectivity equivalence at equal rank 1), and ≥ 1 by `Module.finrank_pos`.
- **Hypotheses**: F field, R an F-algebra, g : R →ₐ[F] R, g module-finite, M maximal, finrank F (R/M) = 1.
- **Uses from project**: none
- **Used by**: unused in file (used externally to supply inertiaDeg = 1 input)
- **Visibility**: public
- **Lines**: 719–773 (two `set_option`: `synthInstance.maxHeartbeats 400000` and `maxHeartbeats 1600000`, with comments; proof ~36 lines)
- **Notes**: Proof strictly >30 lines. Two stacked `set_option` directives.

---

### `theorem ClassGroup.relNorm_one`
- **Type**: `ClassGroup.relNorm 1 = 1`
- **What**: Sanity check: relNorm preserves the identity.
- **How**: `map_one _`.
- **Hypotheses**: Full context.
- **Uses from project**: `ClassGroup.relNorm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 776–777 (term-mode)
- **Notes**: none

---

### `theorem ClassGroup.relNorm_mul`
- **Type**: `ClassGroup.relNorm (a * b) = ClassGroup.relNorm a * ClassGroup.relNorm b`
- **What**: Sanity check: relNorm is multiplicative.
- **How**: `map_mul _ a b`.
- **Hypotheses**: Full context.
- **Uses from project**: `ClassGroup.relNorm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 780–783 (term-mode)
- **Notes**: none

---

### `noncomputable def map0`
- **Type**: `(Ideal R)⁰ →* (Ideal S)⁰`
- **What**: Packages the ideal extension `Ideal.map (algebraMap R S)` as a monoid hom on nonzero-divisor ideals.
- **How**: Nonzero-preservation via `Ideal.map_eq_bot_iff_of_injective` + `FaithfulSMul.algebraMap_injective`; `map_one'` and `map_mul'` via `simp`.
- **Hypotheses**: S/R Dedekind extension (integrally closed hypotheses can be omitted per `omit` clauses downstream).
- **Uses from project**: none
- **Used by**: `mk0CompMap0`, `ClassGroup.map_mk0`
- **Visibility**: public
- **Lines**: 807–818 (proof ~11 lines)
- **Notes**: none

---

### `noncomputable def mk0CompMap0`
- **Type**: `(Ideal R)⁰ →* ClassGroup S`
- **What**: The composite "extend then take the class group element".
- **How**: `ClassGroup.mk0 ∘ map0`.
- **Hypotheses**: Full context (some omit clauses on callers).
- **Uses from project**: `map0`
- **Used by**: `mk0CompMap0_apply`, `mk0CompMap0_eq_of_mk0_eq`, `ClassGroup.map`
- **Visibility**: public
- **Lines**: 821–822 (term-mode)
- **Notes**: none

---

### `theorem mk0CompMap0_apply`
- **Type**: `mk0CompMap0 I = ClassGroup.mk0 (map0 I)` (`@[simp]`)
- **What**: Definitional unfolding; omits `IsIntegrallyClosed R`, `IsIntegrallyClosed S`, `Module.Finite R S`.
- **How**: `rfl`.
- **Uses from project**: `mk0CompMap0`, `map0`
- **Used by**: `mk0CompMap0_eq_of_mk0_eq`
- **Visibility**: public
- **Lines**: 824–827 (1 line)
- **Notes**: none

---

### `theorem mk0CompMap0_eq_of_mk0_eq`
- **Type**: Equal integral ideal classes in ClassGroup R have equal mk0CompMap0 images.
- **What**: Well-definedness of the class-group extension descent.
- **How**: Reduces via `ClassGroup.mk0_eq_mk0_iff`; the key `key` lemma equates span{algebraMap a} with map of span{a}; the algebraMap injectivity from `FaithfulSMul.algebraMap_injective` ensures nonzero images.
- **Hypotheses**: omit `IsIntegrallyClosed R`, `IsIntegrallyClosed S`, `Module.Finite R S`.
- **Uses from project**: `mk0CompMap0_apply`
- **Used by**: `ClassGroup.map` (3 times), `ClassGroup.map_mk0`
- **Visibility**: public
- **Lines**: 829–852 (proof ~22 lines)
- **Notes**: none

---

### `noncomputable def ClassGroup.map`
- **Type**: `ClassGroup R →* ClassGroup S`
- **What**: The class-group extension map induced by `Ideal.map (algebraMap R S)`.
- **How**: Same `surjInv`-based descent pattern as `ClassGroup.relNorm`.
- **Hypotheses**: Full context (some `IsIntegrallyClosed`/`Module.Finite` omitted downstream).
- **Uses from project**: `mk0CompMap0`, `mk0CompMap0_eq_of_mk0_eq`
- **Used by**: `ClassGroup.map_mk0`, `ClassGroup.map_one`, `ClassGroup.map_mul`, `ClassGroup.relNorm_comp_map`, `ClassGroup.relNorm_comp_map_eq`
- **Visibility**: public
- **Lines**: 860–871 (proof ~10 lines)
- **Notes**: none

---

### `theorem ClassGroup.map_mk0`
- **Type**: `ClassGroup.map (ClassGroup.mk0 I) = ClassGroup.mk0 (map0 I)` (`@[simp]`)
- **What**: Computation rule for the extension on an integral representative.
- **How**: `mk0CompMap0_eq_of_mk0_eq` + `mk0CompMap0_apply`.
- **Uses from project**: `mk0CompMap0_eq_of_mk0_eq`, `mk0CompMap0_apply`, `ClassGroup.map`, `map0`
- **Used by**: `ClassGroup.relNorm_comp_map`
- **Visibility**: public
- **Lines**: 878–881 (proof ~3 lines)
- **Notes**: omit `IsIntegrallyClosed R`, `IsIntegrallyClosed S`, `Module.Finite R S`.

---

### `theorem ClassGroup.map_one`
- **Type**: `ClassGroup.map 1 = 1`
- **What**: Sanity check.
- **How**: `_root_.map_one _`.
- **Uses from project**: `ClassGroup.map`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 885–886 (term-mode)
- **Notes**: omit `IsIntegrallyClosed R`, `IsIntegrallyClosed S`, `Module.Finite R S`.

---

### `theorem ClassGroup.map_mul`
- **Type**: `ClassGroup.map (a * b) = ClassGroup.map a * ClassGroup.map b`
- **What**: Sanity check: extension map is multiplicative.
- **How**: `_root_.map_mul _ a b`.
- **Uses from project**: `ClassGroup.map`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 890–893 (term-mode)
- **Notes**: omit `IsIntegrallyClosed R`, `IsIntegrallyClosed S`, `Module.Finite R S`.

---

### `theorem Ideal.relNorm_map_algebraMap`
- **Type**: `relNorm R (Ideal.map (algebraMap R S) I) = I ^ Module.finrank R S`
- **What**: Arithmetic core of the dual relation: norm of extended ideal equals the original raised to [Frac S : Frac R].
- **How**: Supplies the non-instance fraction-field algebra via `FractionRing.liftAlgebra`; converts finrank via `Algebra.IsAlgebraic.finrank_of_isFractionRing`; applies `Ideal.relNorm_algebraMap`.
- **Hypotheses**: S/R finite Dedekind.
- **Uses from project**: none
- **Used by**: `ClassGroup.relNorm_comp_map`
- **Visibility**: public
- **Lines**: 902–911 (proof ~9 lines)
- **Notes**: none

---

### `theorem ClassGroup.relNorm_comp_map`
- **Type**: `ClassGroup.relNorm (ClassGroup.map c) = c ^ Module.finrank R S`
- **What**: The dual relation at the class-group level: relNorm ∘ map = [n]-th power. Class-group shadow of α̂ ∘ α = [deg α].
- **How**: Picks integral representative via `mk0_surjective`; computes both sides using `ClassGroup.map_mk0` and `ClassGroup.relNorm_mk0`; reduces to `Ideal.relNorm_map_algebraMap`.
- **Hypotheses**: S/R finite Dedekind.
- **Uses from project**: `ClassGroup.map_mk0`, `ClassGroup.relNorm_mk0`, `Ideal.relNorm_map_algebraMap`
- **Used by**: `ClassGroup.relNorm_comp_map_eq`
- **Visibility**: public
- **Lines**: 923–930 (proof ~7 lines)
- **Notes**: none

---

### `theorem ClassGroup.relNorm_comp_map_eq`
- **Type**: `(ClassGroup.relNorm).comp (ClassGroup.map) = powMonoidHom (Module.finrank R S)`
- **What**: Equality of monoid hom composites stating the dual relation.
- **How**: `MonoidHom.ext` + `ClassGroup.relNorm_comp_map`.
- **Uses from project**: `ClassGroup.relNorm_comp_map`, `ClassGroup.map`, `ClassGroup.relNorm`
- **Used by**: unused in file (external consumer)
- **Visibility**: public
- **Lines**: 934–938 (proof ~4 lines)
- **Notes**: none

---

## set_option summary

| Location | Option | Value | Comment present? |
|---|---|---|---|
| L169 | `maxHeartbeats` | 800000 | Yes — fraction-field tower / residue-degree finrank |
| L359 | `synthInstance.maxHeartbeats` | 400000 | Yes — semilocal Sₚ Dedekind/finite instance bundle |
| L378 | `synthInstance.maxHeartbeats` | 400000 | Yes — semilocal Sₚ instance bundle in hlocal's type |
| L488 | `maxHeartbeats` | 800000 | Yes — residue-field algebra structure elaboration |
| L536 | `maxHeartbeats` | 800000 | Yes — module-length chain over DVR |
| L574 | `synthInstance.maxHeartbeats` | 400000 | Yes — abstract Rₚ/Sₚ localisation instance bundle |
| L614 | `synthInstance.maxHeartbeats` | 1000000 | Yes — concrete semilocal instance bundle expensive |
| L616 | `maxHeartbeats` | 1600000 | Yes — (paired with synthInstance above) |
| L719 | `synthInstance.maxHeartbeats` | 400000 | Yes — twisted self-algebra pushes past default budget |
| L721 | `maxHeartbeats` | 1600000 | Yes — residue-field finrank bookkeeping |

---

## Long proofs (>30 lines)

| Declaration | Lines |
|---|---|
| `Ideal.relNorm_maximalIdeal_eq_pow_inertiaDeg_of_isLocalRing` | ~32 |
| `isSimpleModule_quot_of_inertiaDeg_one` | ~33 |
| `Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one` | ~36 |

---

## Unused (no callers in this file)

- `ClassGroup.relNorm_mk0'` (used externally)
- `Ideal.relNorm_maximalIdeal_eq_under_of_inertiaDeg_one_of_isLocalRing` (now subsumed, retained as lighter local form)
- `relNorm_eq_relNorm_localization` (cited in comments but not directly called)
- `ClassGroup.mk0_relNorm0_eq_mk0_comap_of_inertiaDeg_one` (used externally for Pic⁰ naturality)
- `Ideal.inertiaDeg_under_eq_one_of_algHom_of_residueField_finrank_one` (used externally to produce inertiaDeg = 1)
- `ClassGroup.relNorm_one`, `ClassGroup.relNorm_mul` (sanity checks)
- `ClassGroup.map_one`, `ClassGroup.map_mul` (sanity checks)
- `ClassGroup.relNorm_comp_map_eq` (external consumer)

---

## Key API (declarations used by 3+ others in this file)

- `mk0CompRelNorm0_eq_of_mk0_eq`: used by `ClassGroup.relNorm` (map_one', map_mul'), `ClassGroup.relNorm_mk0`
- `mk0CompMap0_eq_of_mk0_eq`: used by `ClassGroup.map` (map_one', map_mul'), `ClassGroup.map_mk0`
- `ClassGroup.relNorm`: used by `ClassGroup.relNorm_mk0`, `ClassGroup.relNorm_mk0'`, `ClassGroup.relNorm_one`, `ClassGroup.relNorm_mul`, `ClassGroup.relNorm_comp_map`, `ClassGroup.relNorm_comp_map_eq`
- `ClassGroup.map`: used by `ClassGroup.map_mk0`, `ClassGroup.map_one`, `ClassGroup.map_mul`, `ClassGroup.relNorm_comp_map`, `ClassGroup.relNorm_comp_map_eq`
