# Inventory — `FixedFieldDensity.lean`

Module path: `projects/Chebotarev/CebotarevDensity/FixedFieldDensity.lean` (1224 lines).
Namespace `Chebotarev`. The whole file is in `@[expose] public section` + `noncomputable section`.
Sharifi 7.2.2 Step 1 (the cyclic-reduction core of Chebotarev): density transfer through a
fixed-field subextension `E = L^⟨σ⟩`.

File-wide variables: `{K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
[Algebra K L] [IsGalois K L]`. Several theorems re-bind `K L` as explicit args (shadowing).

---

### `theorem frobeniusFibre_card_eq_of_isConj`
- **Type**: `(K L) … (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (_hunr : UnramifiedIn K L 𝔭) (σ σ' : Gal(L/K)) (hc : IsConj σ σ') : Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ 𝔓} = Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ' 𝔓}`
- **What**: For conjugate elements `σ, σ'` of the Galois group, the set of primes `𝔓` above `𝔭` with Frobenius `σ` and the set with Frobenius `σ'` have equal cardinality.
- **How**: Extracts the conjugator `c` from `IsConj`, then builds an explicit bijection via `Equiv.subtypeEquiv (MulAction.toPerm c)` (the `c`-action permutation); both directions transport primality/lies-over/nonzero through `MulAction.injective` and `Ideal.smul_bot`, and transport the Frobenius condition through `IsArithFrobAt.conj`.
- **Hypotheses**: `𝔭` prime of `𝓞 K`, unramified in `L`; `σ`, `σ'` conjugate in `Gal(L/K)`.
- **Uses from project**: `[]` (relies on mathlib `IsArithFrobAt.conj`, `Ideal.smul_bot`).
- **Used by**: `count_frobenius_eq_sigma_mul_card_carrier` (via the `hequi` argument in `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`).
- **Visibility**: public.
- **Lines**: 54–84 (proof ≈ 23 lines).
- **Notes**: none.

### `theorem card_primesAbove_eq_card_carrier_mul_frobeniusFibre`
- **Type**: `(K L) … (σ) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C) (𝔭) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C) (hequi : ∀ σ', IsConj σ σ' → fibre-card σ = fibre-card σ') : Nat.card {𝔓 // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} = Nat.card C.carrier * Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ 𝔓}`
- **What**: If `𝔭`'s Frobenius class is `C = [σ]` and conjugate Frobenius values occur equally often, the total number of primes above `𝔭` equals `|C|` times the number with Frobenius exactly `σ`.
- **How**: Partitions the primes above `𝔭` by their (class-`C`-valued) Frobenius map `F` using `Equiv.sigmaFiberEquiv` + `Nat.card_sigma`; shows each fibre has the σ-fibre cardinality via `hequi`, using `frobeniusClass_eq_mk_of_isArithFrobAt`, `eq_arithFrobAt_of_isArithFrobAt` and `Ideal.card_stabilizer`-style finiteness; finishes with `Finset.sum_const`/`Finset.card_univ`. Hinges on project lemmas `frobeniusClass_eq_mk_of_isArithFrobAt`, `eq_arithFrobAt_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`, and `UnramifiedIn.*`.
- **Hypotheses**: `𝔭` prime, unramified in `L`, Frobenius class `C = [σ]`; conjugate fibres equinumerous.
- **Uses from project**: `UnramifiedIn.ne_bot`, `UnramifiedIn.finite_quotient`, `UnramifiedIn.ramificationIdx_eq_one`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`, `eq_arithFrobAt_of_isArithFrobAt`.
- **Used by**: `count_frobenius_eq_sigma_mul_card_carrier`.
- **Visibility**: public.
- **Lines**: 90–152 (proof ≈ 50 lines).
- **Notes**: `long (30–50)` — proof body ≈ 50 lines (borderline; treat as long).

### `theorem count_frobenius_eq_sigma_mul_card_carrier`
- **Type**: `(K L) … (σ) (C) (_hσ : ConjClasses.mk σ = C) (𝔭) [𝔭.IsPrime] (hunr) (_hCfrob : frobeniusClass K L 𝔭 = C) : Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ 𝔓} * Nat.card C.carrier = Nat.card {𝔓 // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥}`
- **What**: The number of primes above `𝔭` with Frobenius `σ`, times `|C|`, equals the total number of primes above `𝔭`.
- **How**: One-liner: commute the product and apply `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, supplying the equidistribution hypothesis from `frobeniusFibre_card_eq_of_isConj`.
- **Hypotheses**: same as the previous lemma (Frobenius class `C = [σ]`, `𝔭` unramified).
- **Uses from project**: `card_primesAbove_eq_card_carrier_mul_frobeniusFibre`, `frobeniusFibre_card_eq_of_isConj`.
- **Used by**: `count_primes_above_with_frobenius_eq_sigma`.
- **Visibility**: public.
- **Lines**: 158–168 (proof ≈ 2 lines).
- **Notes**: none.

### `theorem count_primes_above_with_frobenius_eq_sigma`
- **Type**: `(K L) … (σ) (C) (_hσ) (𝔭) [𝔭.IsPrime] (hunr) (_hCfrob) : Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ 𝔓} * orderOf σ * Nat.card C.carrier = Nat.card Gal(L/K)`
- **What**: Sharifi's "exactly `|G|/(f·|C|)` of these have Frobenius σ": the σ-Frobenius fibre over `𝔭` has cardinality `|G|/(f·|C|)`, expressed as `#fibre · f · |C| = |G|`.
- **How**: `mul_right_comm` then `count_frobenius_eq_sigma_mul_card_carrier` collapses `#fibre·|C|` to the total prime count, and the project lemma `card_primesAbove_mul_orderOf_eq` supplies `(total)·(ord σ) = |G|`.
- **Hypotheses**: `𝔭` prime, unramified in `L`, Frobenius class `C = [σ]`.
- **Uses from project**: `count_frobenius_eq_sigma_mul_card_carrier`, `card_primesAbove_mul_orderOf_eq`.
- **Used by**: `card_fibre_T1_over_prime`.
- **Visibility**: public.
- **Lines**: 182–193 (proof ≈ 3 lines).
- **Notes**: none.

### `private theorem univ_ratio_E_K_tendsto_one`
- **Type**: `(E : IntermediateField K L) : Tendsto (fun s ↦ primeIdealZetaSum univ_E s / primeIdealZetaSum univ_K s) (𝓝[>] 1) (𝓝 1)`
- **What**: The ratio of the full prime-ideal zeta sums of an intermediate field `E` and of `K` tends to `1` as `s ↓ 1` (Sharifi's `Σ_𝔭 N𝔭^{-s} ~ Σ_P NP^{-s}`).
- **How**: Both numerator and denominator are asymptotic to `log(1/(s-1))` via `primeIdealZetaSum_univ_tendsto_log` (E instance through `NumberField.of_intermediateField`); divides the two `tendsto`s, then `congr'` using `div_div_div_cancel_right₀` on the event `log(1/(s-1)) > 0`.
- **Hypotheses**: `E` an intermediate field of `L/K`.
- **Uses from project**: `primeIdealZetaSum`, `primeIdealZetaSum_univ_tendsto_log`.
- **Used by**: `density_lift_through_fixedField`.
- **Visibility**: private.
- **Lines**: 195–210 (`omit [IsGalois K L]`; proof ≈ 8 lines).
- **Notes**: none.

### `theorem arithFrobAt_restrictScalars_eq`
- **Type**: `(E : IntermediateField K L) (𝔓) [𝔓.IsPrime] (hunrK : ramificationIdx (𝔓.under 𝓞K) 𝔓 = 1) (_hunrE : ramificationIdx (𝔓.under 𝓞E) 𝔓 = 1) (hnorm : Nat.card (𝓞E/𝔓∩𝓞E) = Nat.card (𝓞K/𝔓∩𝓞K)) : (arithFrobAt (𝓞 ↥E) Gal(L/E) 𝔓).restrictScalars K = arithFrobAt (𝓞 K) Gal(L/K) 𝔓`
- **What**: The E-bridge core: for an unramified `𝔓` whose residue field over `E` has the same size as over `K`, the E-Frobenius `Frob^E_𝔓` restricted to `Gal(L/K)` equals the K-Frobenius `Frob^K_𝔓`.
- **How**: Shows the restricted automorphism `σE.restrictScalars K` is itself a K-Frobenius (`IsArithFrobAt`) — it raises residue classes to the `N(𝔓∩𝓞K)`-th power, which by `hnorm` equals the `N(𝔓∩𝓞E)`-th, the defining property of `arithFrobAt (𝓞 E)`; via `AlgEquiv.restrictScalars_apply`. Then uniqueness at an unramified prime: `IsArithFrobAt.mul_inv_mem_inertia` lands the quotient in the inertia group, which is trivial by the project lemma `inertiaGroup_trivial_of_unramified`.
- **Hypotheses**: `𝔓` prime of `𝓞 L`; ramification index 1 over both `K` and `E`; equal residue-field cardinalities over `E` and `K`.
- **Uses from project**: `ne_bot_of_ramificationIdx_eq_one`, `IsArithFrobAt.arithFrobAt`, `inertiaGroup_trivial_of_unramified`, `IsGalois.tower_top_intermediateField` (mathlib otherwise: `Ideal.finiteQuotientOfFreeOfNeBot`, `IsArithFrobAt.mul_inv_mem_inertia`).
- **Used by**: `arithFrobAt_E_eq_of_isArithFrobAt`, `exists_arithFrobAt_over_fibrePrime`.
- **Visibility**: public.
- **Lines**: 229–259 (proof ≈ 22 lines).
- **Notes**: none.

### `private theorem stabilizer_intermediate_eq_top_of_frobenius`
- **Type**: `(σ) (𝔓) [𝔓.IsPrime] (hunrK : UnramifiedIn K L (𝔓.under 𝓞K)) (hPK : 𝔓.LiesOver (𝔓.under 𝓞K)) (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) (_horderE : orderOf σ = Nat.card Gal(L/E)) : MulAction.stabilizer Gal(L/E) 𝔓 = ⊤` (E = `fixedField (zpowers σ)`)
- **What**: The decomposition group `D_𝔓 = stab_{Gal(L/K)} 𝔓` is cyclic of order `f = ord σ`, generated by `σ`, hence equals `⟨σ⟩ = fixingSubgroup E`; therefore every E-automorphism fixes `𝔓`, i.e. `stab_{Gal(L/E)} 𝔓 = ⊤`.
- **How**: Computes `|D_𝔓| = e·f = 1·(ord σ)` via `Ideal.card_stabilizer_eq` together with `inertiaDeg = ord σ` (project `orderOf_eq_finrank_of_isArithFrobAt`); since `⟨σ⟩ ≤ D_𝔓` (Frobenius is in the stabiliser, `hfrob.mem_stabilizer`) and the cardinalities match, `Subgroup.eq_of_le_of_card_ge` gives `zpowers σ = D_𝔓`. Then for any `τ ∈ Gal(L/E)`, `τ.restrictScalars K` lies in `fixingSubgroup (fixedField (zpowers σ)) = zpowers σ` (via `IntermediateField.fixingSubgroup_fixedField`), so it fixes `𝔓`.
- **Hypotheses**: `𝔓` prime, unramified over `K`, lies over `𝔓∩𝓞K`, K-Frobenius `σ`; `ord σ = |Gal(L/E)|`.
- **Uses from project**: `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `orderOf_eq_finrank_of_isArithFrobAt`, `IsArithFrobAt.mem_stabilizer` (mathlib: `Ideal.card_stabilizer_eq`, `Subgroup.eq_of_le_of_card_ge`, `IntermediateField.fixingSubgroup_fixedField`).
- **Used by**: `inertiaDeg_under_E_eq_one_of_frobenius`, `eq_of_liesOver_under_E_of_frobenius`.
- **Visibility**: private.
- **Lines**: 269–310 (`open scoped Pointwise`; proof ≈ 33 lines).
- **Notes**: `long (30–50)` — ≈ 33 lines.

### `private theorem inertiaDeg_under_E_eq_one_of_frobenius`
- **Type**: `(σ) (𝔓) [𝔓.IsPrime] (hunrK) (hPK) (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) (horderE) : ramificationIdx (𝔓.under 𝓞E) 𝔓 = 1 ∧ (𝔓.under 𝓞K).inertiaDeg (𝔓.under 𝓞E) = 1 ∧ Nat.card (𝓞E/𝔓∩𝓞E) = Nat.card (𝓞K/𝔓∩𝓞K)`
- **What**: With `P = 𝔓∩𝓞E`, `𝔓` is unramified over `E` (`e=1`), the fibre prime `P` has degree one over `K` (`f(P∣𝔭)=1`), and `N P = N 𝔭`.
- **How**: `e(𝔓∣P)=1` by the tower law `Ideal.ramificationIdx_algebra_tower'` from `e(𝔓∣𝔭)=1`. Uses `stabilizer_intermediate_eq_top_of_frobenius` to get `stab_{Gal(L/E)} 𝔓 = ⊤`, so `|stab| = f(𝔓∣P) = [L:E] = ord σ` via `Ideal.card_stabilizer_eq`; combined with `f(𝔓∣𝔭) = ord σ` (project `orderOf_eq_finrank_of_isArithFrobAt`) and the inertia tower law `Ideal.inertiaDeg_algebra_tower`, cancels to `f(P∣𝔭)=1`; the norm equality follows from `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`.
- **Hypotheses**: `𝔓` prime, unramified over `K`, K-Frobenius `σ`; `ord σ = |Gal(L/E)|`.
- **Uses from project**: `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `IsGalois.tower_top_intermediateField`, `orderOf_eq_finrank_of_isArithFrobAt`, `stabilizer_intermediate_eq_top_of_frobenius`.
- **Used by**: `under_E_mem_fibre_of_isArithFrobAt`.
- **Visibility**: private.
- **Lines**: 319–384 (`open scoped Pointwise`; proof ≈ 50 lines).
- **Notes**: `long (30–50)` — proof body ≈ 50 lines (borderline; treat as long).

### `private theorem eq_of_liesOver_under_E_of_frobenius`
- **Type**: `(σ) (𝔓) [𝔓.IsPrime] (hunrK) (hPK) (hfrob) (horderE) (𝔔) [𝔔.IsPrime] (hQ : 𝔔.LiesOver (𝔓.under 𝓞E)) : 𝔔 = 𝔓`
- **What**: `𝔓` is the unique prime of `𝓞 L` above `P = 𝔓∩𝓞E` (it is inert in `L/E`).
- **How**: Since `stab_{Gal(L/E)} 𝔓 = ⊤` (`stabilizer_intermediate_eq_top_of_frobenius`) and `Gal(L/E)` acts transitively on primes above `P` (`Ideal.exists_smul_eq_of_isGaloisGroup`), any `𝔔` above `P` is `τ • 𝔓 = 𝔓` for the conjugating `τ` (in the stabiliser).
- **Hypotheses**: as above, plus a second prime `𝔔` of `𝓞 L` above `𝔓∩𝓞E`.
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `IsGaloisGroup.of_isGalois`, `stabilizer_intermediate_eq_top_of_frobenius` (mathlib: `Ideal.exists_smul_eq_of_isGaloisGroup`, `Ideal.over_under`).
- **Used by**: `under_E_mem_fibre_of_isArithFrobAt`, `card_fibre_E_eq_card_fibre_L`.
- **Visibility**: private.
- **Lines**: 390–412 (`open scoped Pointwise`; proof ≈ 12 lines).
- **Notes**: none.

### `private theorem arithFrobAt_E_eq_of_isArithFrobAt`
- **Type**: `(σ) (σE : Gal(L/E)) (hσE : σE.restrictScalars K = σ) (𝔓) [𝔓.IsPrime] (hunrK) (hPK) (hfrob) (_horderE) (hraE : ramificationIdx (𝔓.under 𝓞E) 𝔓 = 1) (hnorm) : arithFrobAt (𝓞 E) Gal(L/E) 𝔓 = σE`
- **What**: The E-Frobenius below `𝔓` is `σ_E`: for `𝔓` with `Frob^K_𝔓 = σ` over a degree-one fibre prime, `Frob^E_𝔓 = σ_E`.
- **How**: By `arithFrobAt_restrictScalars_eq`, `(Frob^E_𝔓).restrictScalars K = Frob^K_𝔓 = σ` (using `eq_arithFrobAt_of_isArithFrobAt` to rewrite `σ` as `Frob^K_𝔓`); since `σE` also restricts to `σ` and `AlgEquiv.restrictScalars_injective` over `K`, the two E-automorphisms coincide.
- **Hypotheses**: `σE` restricts to `σ`; `𝔓` unramified over `K` and over `E` (`hraE`); equal residue cardinalities.
- **Uses from project**: `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `IsGalois.tower_top_intermediateField`, `arithFrobAt_restrictScalars_eq`, `eq_arithFrobAt_of_isArithFrobAt`.
- **Used by**: `under_E_mem_fibre_of_isArithFrobAt`.
- **Visibility**: private.
- **Lines**: 418–454 (proof ≈ 14 lines).
- **Notes**: none.

### `private theorem exists_arithFrobAt_over_fibrePrime`
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (P : Ideal (𝓞 E)) [P.IsPrime] (hunrP : UnramifiedIn K L (P.under 𝓞K)) (hPunr : UnramifiedIn E L P) (hPfrob : frobeniusClass E L P = ConjClasses.mk σE) (hPdeg : (P.under 𝓞K).inertiaDeg P = 1) (hPbot) : ∃ 𝔓 …, 𝔓.under (𝓞 E) = P ∧ IsArithFrobAt (𝓞 K) σ 𝔓`
- **What**: The surjective half of the fibre bijection: a degree-one fibre prime `P` of `𝓞 E` (with `Frob^E_P = [σ_E]`) has some prime `𝔓` of `𝓞 L` above it with `Frob^K_𝔓 = σ`.
- **How**: Lifts `P` to a prime `𝔓` of `L` (`exists_prime_liesOver`); transports norm/inertia/ramification data down (`f(P∣𝔭)=1` ⇒ `N P = N 𝔭` via `Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`, `hraE` via `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`); identifies `Frob^E_𝔓 = σ_E` from the class equality `hPfrob` (`frobeniusClass_eq_mk_of_isArithFrobAt` + `isConj_iff_eq` in the abelian group `IsMulCommutative`); then bridges to `Frob^K_𝔓 = σ` via `arithFrobAt_restrictScalars_eq` and `hσE`.
- **Hypotheses**: `Gal(L/E)` commutative; `P` prime of `𝓞 E`, unramified in `L` and (its `K`-prime) over `K`, `Frob^E_P = [σ_E]`, degree one over `K`.
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `exists_prime_liesOver`, `UnramifiedIn.ramificationIdx_eq_one`, `UnramifiedIn.ne_bot`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`, `arithFrobAt_restrictScalars_eq`.
- **Used by**: `card_fibre_E_eq_card_fibre_L`, `frobeniusClass_under_eq_of_mem_fibre`.
- **Visibility**: private.
- **Lines**: 461–527 (proof ≈ 50 lines).
- **Notes**: `long (30–50)` — proof body ≈ 50 lines (borderline; treat as long).

### `private theorem under_E_mem_fibre_of_isArithFrobAt`
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (horderE) (𝔭) [𝔭.IsPrime] (hunr) (𝔓) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) (hPbot) (hfrob : IsArithFrobAt (𝓞 K) σ 𝔓) : (𝔓.under 𝓞E) ∈ {degree-one fibre set} ∧ (𝔓.under 𝓞E).LiesOver 𝔭 ∧ (𝔓.under 𝓞E) ≠ ⊥`
- **What**: The forward (injective-side) map of the fibre bijection: for `𝔓` above `𝔭` with `Frob^K_𝔓 = σ`, the contraction `P = 𝔓∩𝓞E` is a degree-one fibre prime (prime, unramified in `L`, `Frob^E_P = [σ_E]`, `f(P∣𝔭)=1`).
- **How**: Combines `inertiaDeg_under_E_eq_one_of_frobenius` (for `e=1`, `f(P∣𝔭)=1`, norm) and `arithFrobAt_E_eq_of_isArithFrobAt` (for `Frob^E_𝔓 = σ_E`); uniqueness of `𝔓` over `P` (`eq_of_liesOver_under_E_of_frobenius`) gives unramifiedness `UnramifiedIn E L P`; the Frobenius class is read off via `frobeniusClass_eq_mk_of_isArithFrobAt` and `ConjClasses.mk_eq_mk_iff_isConj`; `f(P∣𝔭)` is moved through `Ideal.under_under`.
- **Hypotheses**: `Gal(L/E)` commutative; `𝔓` prime above unramified `𝔭`, nonzero, K-Frobenius `σ`; `ord σ = |Gal(L/E)|`.
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `inertiaDeg_under_E_eq_one_of_frobenius`, `arithFrobAt_E_eq_of_isArithFrobAt`, `eq_of_liesOver_under_E_of_frobenius`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `IsArithFrobAt.arithFrobAt`.
- **Used by**: `card_fibre_E_eq_card_fibre_L`.
- **Visibility**: private.
- **Lines**: 533–590 (proof ≈ 38 lines).
- **Notes**: `long (30–50)` — ≈ 38 lines.

### `private theorem card_fibre_E_eq_card_fibre_L`
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (horderE) (𝔭) [𝔭.IsPrime] (hunr) (_hCfrob : frobeniusClass K L 𝔭 = ConjClasses.mk σ) : Nat.card {P // degree-one fibre over 𝔭} = Nat.card {𝔓 // ∃ …, IsArithFrobAt (𝓞 K) σ 𝔓}`
- **What**: Fibre bijection: the map `𝔓 ↦ 𝔓∩𝓞E` is a bijection from L-primes above `𝔭` with `Frob^K_𝔓 = σ` onto the degree-one E-primes above `𝔭` with `Frob^E_P = [σ_E]`; hence the fibres are equinumerous.
- **How**: `Nat.card_congr (Equiv.ofBijective …)` with the contraction map; well-definedness from `under_E_mem_fibre_of_isArithFrobAt`; injectivity from uniqueness `eq_of_liesOver_under_E_of_frobenius`; surjectivity from `exists_arithFrobAt_over_fibrePrime`.
- **Hypotheses**: `Gal(L/E)` commutative; `𝔭` unramified, Frobenius class `[σ]`; `ord σ = |Gal(L/E)|`.
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `under_E_mem_fibre_of_isArithFrobAt`, `eq_of_liesOver_under_E_of_frobenius`, `exists_arithFrobAt_over_fibrePrime`.
- **Used by**: `card_fibre_T1_over_prime`.
- **Visibility**: private.
- **Lines**: 599–659 (proof ≈ 38 lines).
- **Notes**: `long (30–50)` — ≈ 38 lines.

### `private theorem frobeniusClass_under_eq_of_mem_fibre`
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (_horderE) (P) [P.IsPrime] (hunrP) (hPunr) (hPfrob) (hPdeg) (hPbot) : frobeniusClass K L (P.under (𝓞 K)) = ConjClasses.mk σ`
- **What**: A degree-one fibre prime `P` of `𝓞 E` (with `Frob^E_P = [σ_E]`) sits over a `K`-prime `𝔭 = P∩𝓞K` whose K-Frobenius class is `[σ]`.
- **How**: Produces a prime `𝔓` of `L` above `P` with `Frob^K_𝔓 = σ` (`exists_arithFrobAt_over_fibrePrime`); rewrites `P∩𝓞K = 𝔓∩𝓞K` (`Ideal.under_under`) and reads off the class via `frobeniusClass_eq_mk_of_isArithFrobAt`.
- **Hypotheses**: `Gal(L/E)` commutative; `P` a degree-one fibre prime of `𝓞 E` (unramified in `L`, `Frob^E_P = [σ_E]`, deg one over `K`).
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `exists_arithFrobAt_over_fibrePrime`, `frobeniusClass_eq_mk_of_isArithFrobAt`.
- **Used by**: `primeIdealZetaSum_fibre_eq_smul`.
- **Visibility**: private.
- **Lines**: 664–690 (proof ≈ 12 lines).
- **Notes**: none.

### `private theorem tsum_comp_eq_card_fibre_smul`
- **Type**: `{β γ} (g : β → γ) (h : γ → ℝ) (c : ℝ) (hsumm : Summable (h ∘ g)) (hfin : ∀ y, Finite (g⁻¹'{y})) (hcard : ∀ y, Nat.card (g⁻¹'{y}) = c) : ∑' b, h (g b) = c * ∑' y, h y`
- **What**: Real-valued fibre-counting equality: if every fibre is finite of the same size `c`, then `Σ_b h(g b) = c·Σ_y h y`.
- **How**: Regroups `b` by image via `HasSum.tsum_fiberwise`, pulls out the constant with `tsum_mul_left`; on each (finite) fibre the summand is the constant `h y` summed `c` times (`tsum_fintype`, `Finset.sum_const`).
- **Hypotheses**: `h ∘ g` summable; every fibre finite of cardinality exactly `c`.
- **Uses from project**: `[]`.
- **Used by**: `primeIdealZetaSum_fibre_eq_smul`.
- **Visibility**: private.
- **Lines**: 696–705 (proof ≈ 6 lines).
- **Notes**: none.

### `private theorem card_fibre_T1_over_prime`
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (horderE) (𝔭) [𝔭.IsPrime] (hunr𝔭) (hfrob𝔭 : frobeniusClass K L 𝔭 = ConjClasses.mk σ) : (orderOf σ * Nat.card (ConjClasses.mk σ).carrier) * Nat.card {P // degree-one fibre over 𝔭} = Nat.card Gal(L/K)`
- **What**: The degree-one fibre over an unramified `K`-prime `𝔭` (with `Frob^K = [σ]`) has cardinality `|G|/(f·|C|)`, i.e. `(f·|C|)·#fibre = |G|`.
- **How**: Rewrites the fibre count by the bijection `card_fibre_E_eq_card_fibre_L`, then applies the established count `count_primes_above_with_frobenius_eq_sigma`.
- **Hypotheses**: `Gal(L/E)` commutative; `𝔭` unramified, Frobenius class `[σ]`; `ord σ = |Gal(L/E)|`.
- **Uses from project**: `card_fibre_E_eq_card_fibre_L`, `count_primes_above_with_frobenius_eq_sigma`.
- **Used by**: `primeIdealZetaSum_fibre_eq_smul`.
- **Visibility**: private.
- **Lines**: 711–729 (proof ≈ 2 lines).
- **Notes**: none.

### `private theorem primeIdealZetaSum_fibre_eq_smul`  (LEAF A)
- **Type**: `(σ) (σE) (hσE) [IsMulCommutative Gal(L/E)] (horderE) {s} (hs : 1 < s) : primeIdealZetaSum {T₁ set} s = ((Nat.card Gal(L/K))/(orderOf σ * Nat.card (mk σ).carrier)) * primeIdealZetaSum {S set} s`
- **What**: LEAF A — the degree-one part `T₁` of `T` carries the main term: for `1 < s`, the partial Dirichlet sum over the degree-one E-primes with `Frob^E = [σ_E]` equals `|G|/(f·|C|)` times the partial sum over `S` (the `K`-primes with `Frob^K = [σ]`).
- **How**: Sets up the contraction map `g : T₁ → S'` (well-defined by `frobeniusClass_under_eq_of_mem_fibre`); shows `N P = N 𝔭` for degree-one `P` (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`); each fibre is finite (`IsDedekindDomain.primesOver_finite`) of constant card `|G|/(f·|C|)` (re-indexed to `card_fibre_T1_over_prime`); finishes with the real-valued fibre-counting identity `tsum_comp_eq_card_fibre_smul`. Relies on the project summability lemma `summable_prime_absNorm_rpow`.
- **Hypotheses**: `Gal(L/E)` commutative; `ord σ = |Gal(L/E)|`; `s > 1`.
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `primeIdealZetaSum`, `primeIdealZetaSum_def`, `frobeniusClass_under_eq_of_mem_fibre`, `card_fibre_T1_over_prime`, `tsum_comp_eq_card_fibre_smul`, `summable_prime_absNorm_rpow`.
- **Used by**: `density_lift_through_fixedField`.
- **Visibility**: private.
- **Lines**: 738–842 (proof ≈ 82 lines).
- **Notes**: `OVER-50 — needs further /decompose-proof pass` (proof ≈ 82 lines).

### `private theorem tsum_comp_le_card_fibre_mul`
- **Type**: `{β γ} (g : β → γ) (f : γ → ℝ≥0∞) (d : ℕ) (hfin : ∀ y, Finite (g⁻¹'{y})) (hfib : ∀ y, Nat.card (g⁻¹'{y}) ≤ d) : ∑' b, f (g b) ≤ d * ∑' y, f y`
- **What**: `ℝ≥0∞`-valued fibre-counting bound: if every fibre has `≤ d` elements, then `Σ_b f(g b) ≤ d·Σ_y f y`.
- **How**: Regroups by image (`ENNReal.tsum_fiberwise`), pulls out the factor (`ENNReal.tsum_mul_left`); on each finite fibre the summand is constant `f y` over `≤ d` terms, bounded by `gcongr`.
- **Hypotheses**: every fibre finite with `≤ d` elements.
- **Uses from project**: `[]`.
- **Used by**: `tsum_real_comp_le_card_fibre_mul`.
- **Visibility**: private.
- **Lines**: 860–870 (proof ≈ 7 lines).
- **Notes**: none.

### `private theorem tsum_real_comp_le_card_fibre_mul`
- **Type**: `{β γ} (g) (FA : β → ℝ) (FK : γ → ℝ) (d : ℕ) (hsummA) (hsummK) (hnonnegA) (hnonnegK) (hterm : ∀ b, FA b ≤ FK (g b)) (hfin) (hfib : ∀ y, Nat.card (g⁻¹'{y}) ≤ d) : ∑' b, FA b ≤ d * ∑' y, FK y`
- **What**: Real-valued companion of the previous: for nonnegative summable `FA, FK` with `FA b ≤ FK(g b)` and fibres of size `≤ d`, `Σ_b FA b ≤ d·Σ_y FK y`.
- **How**: Passes to `ENNReal.ofReal`, chains `ENNReal.tsum_le_tsum` (termwise `hterm`) with `tsum_comp_le_card_fibre_mul`, then descends back to `ℝ` via `ENNReal.ofReal_tsum_of_nonneg` / `ENNReal.toReal_*`.
- **Hypotheses**: `FA, FK` summable nonnegative; `FA b ≤ FK(g b)`; fibres finite of size `≤ d`.
- **Uses from project**: `tsum_comp_le_card_fibre_mul`.
- **Used by**: `primeIdealZetaSum_degTwo_le`.
- **Visibility**: private.
- **Lines**: 875–891 (proof ≈ 13 lines).
- **Notes**: none.

### `private theorem absNorm_rpow_neg_le_under_sq`
- **Type**: `(σ) (P : Ideal (𝓞 E)) [P.IsPrime] (hPb : P ≠ ⊥) {s} (hs : 1 < s) (hdeg : 2 ≤ (P.under 𝓞K).inertiaDeg P) : (Ideal.absNorm P : ℝ) ^ (-s) ≤ (Ideal.absNorm (P.under 𝓞K) : ℝ) ^ (-(2:ℝ))`
- **What**: For a degree-`≥2` prime `P` of `𝓞 E` over `𝔭 = P∩𝓞K`, the Dirichlet term is dominated by the `𝔭`-square term: `N P^{-s} ≤ N𝔭^{-2}` for `1 < s`.
- **How**: `N P = N𝔭^{f}` with `f ≥ 2` (`Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver`); `N𝔭 ≥ 2` (norm not 0 or 1, via `Ideal.absNorm_eq_zero_iff`/`absNorm_eq_one_iff` + `omega`); then `Real.rpow_le_rpow_of_exponent_le` since `f·s ≥ 2` (`nlinarith`).
- **Hypotheses**: `P` nonzero prime of `𝓞 E`; `s > 1`; inertia degree of `P` over `K` is `≥ 2`.
- **Uses from project**: `[]` (`omit [IsGalois K L]`).
- **Used by**: `primeIdealZetaSum_degTwo_le`.
- **Visibility**: private.
- **Lines**: 897–914 (`omit [IsGalois K L]`; proof ≈ 14 lines).
- **Notes**: none.

### `private theorem card_primesOver_le_finrank`
- **Type**: `(σ) [NoZeroSMulDivisors (𝓞 K) (𝓞 E)] (𝔭) [𝔭.IsMaximal] (h𝔭 : 𝔭 ≠ ⊥) : Nat.card {P : Ideal (𝓞 E) // P.IsPrime ∧ P.LiesOver 𝔭} ≤ Module.finrank K ↥E`
- **What**: The number of primes of `𝓞 E` over a fixed maximal `K`-prime `𝔭` is at most `[E:K]`.
- **How**: A `Nat.card` repackaging — identifies the subtype with `𝔭.primesOver (𝓞 E)`, rewrites via `IsDedekindDomain.coe_primesOverFinset` and `Set.ncard_coe_finset`, then `Ideal.card_primesOverFinset_le_finrank`.
- **Hypotheses**: `NoZeroSMulDivisors (𝓞 K) (𝓞 E)`; `𝔭` nonzero maximal.
- **Uses from project**: `[]`.
- **Used by**: `primeIdealZetaSum_degTwo_le`.
- **Visibility**: private.
- **Lines**: 919–933 (proof ≈ 9 lines).
- **Notes**: none.

### `private theorem primeIdealZetaSum_degTwo_le`
- **Type**: `(σ) {s} (hs : 1 < s) (Aset) (hA : Aset = {P | P prime ∧ P ≠ ⊥ ∧ UnramifiedIn K L (P.under 𝓞K) ∧ 2 ≤ (P.under 𝓞K).inertiaDeg P}) : primeIdealZetaSum Aset s ≤ (Module.finrank K ↥E : ℝ) * primeIdealZetaSum univ_K 2`
- **What**: The degree-`≥2` part `A` of `T₂` is bounded by a constant: for `1 < s`, the partial sum over `A` is `≤ [E:K]·Σ_𝔭 N𝔭^{-2}`.
- **How**: Synthesizes `NoZeroSMulDivisors (𝓞K)(𝓞E)`; sets contraction map `g : A → K`-primes; termwise bound `absNorm_rpow_neg_le_under_sq`; fibres finite of size `≤ [E:K]` (`card_primesOver_le_finrank` + `IsDedekindDomain.primesOver_finite`); applies `tsum_real_comp_le_card_fibre_mul` with the project summability lemma `summable_prime_absNorm_rpow`.
- **Hypotheses**: `s > 1`; `Aset` is the unramified-below, inertia-`≥2` set.
- **Uses from project**: `primeIdealZetaSum`, `primeIdealZetaSum_def`, `absNorm_rpow_neg_le_under_sq`, `card_primesOver_le_finrank`, `tsum_real_comp_le_card_fibre_mul`, `summable_prime_absNorm_rpow`.
- **Used by**: `primeIdealZetaSum_T2_div_univ_tendsto_zero`.
- **Visibility**: private.
- **Lines**: 941–993 (proof ≈ 44 lines).
- **Notes**: `long (30–50)` — ≈ 44 lines.

### `private theorem ramifiedBelow_finite`
- **Type**: `(σ) (Bset) (hB : Bset = {P | P prime ∧ P ≠ ⊥ ∧ ¬ UnramifiedIn K L (P.under 𝓞K)}) : Bset.Finite`
- **What**: The ramified part `B` of `T₂` — primes `P` of `𝓞 E` whose `K`-prime is ramified in `L` — is a finite set.
- **How**: `B` is a subset of the bi-union over the finitely many ramified `K`-primes (project `finite_ramifiedIn`) of their (finite, `IsDedekindDomain.primesOver_finite`) primes-over sets; `Set.Finite.subset` + `Set.Finite.biUnion`.
- **Hypotheses**: `Bset` is the ramified-below prime set.
- **Uses from project**: `finite_ramifiedIn`.
- **Used by**: `primeIdealZetaSum_T2_div_univ_tendsto_zero`.
- **Visibility**: private.
- **Lines**: 999–1013 (proof ≈ 12 lines).
- **Notes**: none.

### `private theorem primeIdealZetaSum_T2_div_univ_tendsto_zero`  (LEAF B)
- **Type**: `(σ) (σE) (T₂set) (hT₂ : T₂set = Tset \ T₁set) : Tendsto (fun s ↦ primeIdealZetaSum T₂set s / primeIdealZetaSum univ_E s) (𝓝[>] 1) (𝓝 0)`
- **What**: LEAF B — the degree-`≥2` complement `T₂ = T∖T₁` vanishes in the density ratio: `Σ_{T₂}/Σ_univ^E → 0` as `s ↓ 1` (Sharifi's `Σ_𝔭 N𝔭^{-s} ~ Σ_P NP^{-s}`).
- **How**: Splits `T₂ ⊆ A ∪ B` with `A` (deg `≥2`) and `B` (ramified-below) disjoint; bounds `Σ_{T₂} s ≤ Σ_A s + Σ_B s ≤ [E:K]·Σ_𝔭 N𝔭^{-2} + |B|`, a constant in `s`, via `primeIdealZetaSum_degTwo_le`, `ramifiedBelow_finite`, `primeIdealZetaSum_le_card_of_finite`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`; concludes with the project lemma `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const` since `Σ_univ^E → ∞`.
- **Hypotheses**: `T₂set` is `Tset \ T₁set` (degree-one E-primes with `Frob^E = [σ_E]` removed).
- **Uses from project**: `IsGalois.tower_top_intermediateField`, `primeIdealZetaSum`, `ramifiedBelow_finite`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_degTwo_le`, `primeIdealZetaSum_le_card_of_finite`, `UnramifiedIn.ne_bot`, `Ideal.inertiaDeg_pos'`.
- **Used by**: `density_lift_through_fixedField`.
- **Visibility**: private.
- **Lines**: 1025–1084 (proof ≈ 45 lines).
- **Notes**: `long (30–50)` — ≈ 45 lines.

### `private theorem isMulCommutative_galGroup_fixedField`
- **Type**: `(σ) : IsMulCommutative Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ))))`
- **What**: `Gal(L/L^⟨σ⟩)` is commutative.
- **How**: It is the image of the cyclic subgroup `⟨σ⟩` under the iso `IntermediateField.subgroupEquivAlgEquiv`; commutativity transports from `mul_comm'` on `zpowers σ` via `.of_comm` and `map_mul`.
- **Hypotheses**: none beyond the file variables (`omit [IsGalois K L]`).
- **Uses from project**: `[]`.
- **Used by**: `density_lift_through_fixedField`.
- **Visibility**: private.
- **Lines**: 1086–1094 (`omit [IsGalois K L]`; proof ≈ 5 lines).
- **Notes**: none.

### `private theorem card_galGroup_fixedField_eq_orderOf`
- **Type**: `(σ) : Nat.card Gal(L/(↥(IntermediateField.fixedField (Subgroup.zpowers σ)))) = orderOf σ`
- **What**: `Gal(L/L^⟨σ⟩)` has order `ord σ`.
- **How**: Transports cardinality across `IntermediateField.subgroupEquivAlgEquiv (zpowers σ)` and uses `Nat.card_zpowers`.
- **Hypotheses**: none beyond file variables (`omit [IsGalois K L]`).
- **Uses from project**: `[]`.
- **Used by**: `density_lift_through_fixedField`.
- **Visibility**: private.
- **Lines**: 1096–1102 (`omit [IsGalois K L]`; proof ≈ 3 lines).
- **Notes**: none.

### `theorem density_lift_through_fixedField`
- **Type**: `(σ) (E : IntermediateField K L) (σE : Gal(L/E)) (hσE : σE.restrictScalars K = σ) (_hEfix : E = IntermediateField.fixedField (Subgroup.zpowers σ)) (_hab : HasDirichletDensity {E-fibre of σE} ((Nat.card Gal(L/E))⁻¹)) : HasDirichletDensity {K-fibre class of σ} ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card Gal(L/K))`
- **What**: The main result — density-lift through the fixed-field subextension: given the abelian (cyclic) density `1/|Gal(L/E)|` of the `σ_E`-fibre over `E`, the density over `K` of the Frobenius **class** of `σ` is `|C|/|G|`.
- **How**: Substitutes `E = L^⟨σ⟩`; supplies `IsMulCommutative` (`isMulCommutative_galGroup_fixedField`) and `ord σ = |Gal(L/E)|` (`card_galGroup_fixedField_eq_orderOf`). Splits `T = T₁ ⊔ T₂`; LEAF B (`primeIdealZetaSum_T2_div_univ_tendsto_zero`) kills the `T₂` ratio, so `Σ_{T₁}/Σ_univ^E → 1/|Gal(L/E)|`; multiplies by the constant `f·|C|/|G|` and by `univ_ratio_E_K_tendsto_one` (E-to-K zeta ratio → 1); LEAF A (`primeIdealZetaSum_fibre_eq_smul`) rewrites `Σ_S = (f·|C|/|G|)·Σ_{T₁}`; algebra (`field_simp`/`ring`) collapses the limit to `|C|/|G|`. Hinges on `primeIdealZetaSum_univ_tendsto_atTop`.
- **Hypotheses**: `E = L^⟨σ⟩`; `σ_E` restricts to `σ`; abelian-case density `1/|Gal(L/E)|` for the `σ_E`-fibre over `E`.
- **Uses from project**: `isMulCommutative_galGroup_fixedField`, `card_galGroup_fixedField_eq_orderOf`, `primeIdealZetaSum`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_T2_div_univ_tendsto_zero`, `primeIdealZetaSum_fibre_eq_smul`, `univ_ratio_E_K_tendsto_one`, `primeIdealZetaSum_univ_tendsto_atTop`, `HasDirichletDensity`.
- **Used by**: unused in file (the module's exported entry point; consumed by `Main.lean`/`Abelian.lean`).
- **Visibility**: public.
- **Lines**: 1122–1221 (proof ≈ 88 lines).
- **Notes**: `OVER-50 — needs further /decompose-proof pass` (proof ≈ 88 lines).

---

## File Summary

**Total declarations: 26** — defs: 0 / lemmas+theorems: 26 / instances: 0
(structures/classes/abbrevs/inductives: 0). 6 are public `theorem`s; 20 are `private theorem`s.

**Key API (used by ≥ 3 in-file):**
- None. The file is a deep linear chain (each lemma feeds 1–2 successors); no single in-file
  declaration is referenced by ≥ 3 others. The most-reused are
  `exists_arithFrobAt_over_fibrePrime` (used by 2), `eq_of_liesOver_under_E_of_frobenius` (2),
  `arithFrobAt_restrictScalars_eq` (2), and `stabilizer_intermediate_eq_top_of_frobenius` (2).
  Note many lemmas lean heavily on *external-to-this-file* project API
  (`frobeniusClass_eq_mk_of_isArithFrobAt`, `summable_prime_absNorm_rpow`, `primeIdealZetaSum_*`,
  `UnramifiedIn.*`, `orderOf_eq_finrank_of_isArithFrobAt`, …) imported from other Chebotarev
  modules (`Frobenius.lean`, `Density.lean`, `ZetaProduct.lean`, `Cyclotomic.lean`).

**Unused declarations (no in-file consumer):**
- `density_lift_through_fixedField` — the module's exported result (consumed downstream by
  `Main.lean` / `Abelian.lean`), so "unused in file" is expected, not dead code.

**Declarations with `sorry`:** none.

**Declarations with `set_option`:** none.

**Proofs > 50 lines (decompose-needed):**
- `density_lift_through_fixedField` — ≈ 88 lines (1122–1221).
- `primeIdealZetaSum_fibre_eq_smul` (LEAF A) — ≈ 82 lines (738–842).

**Proofs 30–50 lines (long):**
- `inertiaDeg_under_E_eq_one_of_frobenius` — ≈ 50 (319–384).
- `card_primesAbove_eq_card_carrier_mul_frobeniusFibre` — ≈ 50 (90–152).
- `exists_arithFrobAt_over_fibrePrime` — ≈ 50 (461–527).
- `primeIdealZetaSum_T2_div_univ_tendsto_zero` (LEAF B) — ≈ 45 (1025–1084).
- `primeIdealZetaSum_degTwo_le` — ≈ 44 (941–993).
- `under_E_mem_fibre_of_isArithFrobAt` — ≈ 38 (533–590).
- `card_fibre_E_eq_card_fibre_L` — ≈ 38 (599–659).
- `stabilizer_intermediate_eq_top_of_frobenius` — ≈ 33 (269–310).

**Note:** `frobeniusFibre_card_eq_of_isConj` (≈ 23) and `arithFrobAt_restrictScalars_eq` (≈ 22)
sit just under the 30-line long threshold but are nontrivial bijection/uniqueness proofs.
