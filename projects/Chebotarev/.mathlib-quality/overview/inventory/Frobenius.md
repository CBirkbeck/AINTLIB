# Inventory — `projects/Chebotarev/CebotarevDensity/Frobenius.lean`

File-level: `module`; `@[expose] public section`; `noncomputable section`.
Imports: mathlib `Galois.IsGaloisGroup`, `DedekindDomain.Different`, `DedekindDomain.Factorization`, `RingTheory.Frobenius`; project `CebotarevDensity.Density`.
Common variables: `(K L : Type*) [Field K] [Field L] [Algebra K L]`; from line 86 also `[NumberField K] [NumberField L]`.

---

### `def UnramifiedIn`
- **Type**: `[IsGalois K L] (𝔭 : Ideal (𝓞 K)) : Prop`, defined as `𝔭 ≠ ⊥ ∧ ∀ (𝔓 : Ideal (𝓞 L)) (_ : 𝔓.IsMaximal), 𝔓.LiesOver 𝔭 → Algebra.IsUnramifiedAt (𝓞 K) 𝔓`.
- **What**: A prime `𝔭` of `𝓞 K` is *unramified in* `L` when it is nonzero and every maximal prime `𝔓` of `𝓞 L` lying over `𝔭` is unramified over `𝓞 K`.
- **How**: A plain conjunction; no proof. The `𝔭 ≠ ⊥` clause is carried so the Frobenius needs a finite residue field; for nonzero `𝔭` maximal primes over it are exactly its prime divisors.
- **Hypotheses**: `L/K` Galois; `𝔭` an ideal of `𝓞 K`.
- **Uses from project**: `[]`
- **Used by**: `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `UnramifiedIn.finite_quotient`, `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `frobeniusClass`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn`
- **Visibility**: public
- **Lines**: 62–63 (def, 1 line)
- **Notes**: none

---

### `theorem ne_bot_of_ramificationIdx_eq_one`
- **Type**: `{𝔓 : Ideal (𝓞 L)} (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : 𝔓 ≠ ⊥`
- **What**: A prime `𝔓` of `𝓞 L` with ramification index `1` over its contraction is nonzero.
- **How**: Contrapositive: substitute `𝔓 = ⊥`, then `simp` reduces `ramificationIdx … ⊥ = 1` to a falsehood (ramification index of `⊥` is not `1`).
- **Hypotheses**: `e(𝔓 ∣ 𝔓.under (𝓞 K)) = 1`.
- **Uses from project**: `[]`
- **Used by**: `UnramifiedIn.finite_quotient`, `inertiaGroup_trivial_of_unramified`, `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`
- **Visibility**: public
- **Lines**: 66–69 (proof 2 lines)
- **Notes**: none

---

### `theorem UnramifiedIn.ne_bot`
- **Type**: `[IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) : 𝔭 ≠ ⊥`
- **What**: An unramified prime is nonzero — extracts the first conjunct of `UnramifiedIn`.
- **How**: Projection `hunr.1`.
- **Hypotheses**: `L/K` Galois; `𝔭` unramified in `L`.
- **Uses from project**: `UnramifiedIn`
- **Used by**: `exists_frobeniusClass`, `card_primesAbove_mul_finrank_eq`, `card_primesAbove_mul_orderOf_eq`
- **Visibility**: public
- **Lines**: 72–74 (proof 1 line)
- **Notes**: none

---

### `theorem exists_prime_liesOver`
- **Type**: `(𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hnz : 𝔭 ≠ ⊥) : ∃ 𝔓 : Ideal (𝓞 L), 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥`
- **What**: A nonzero prime `𝔭` of `𝓞 K` has at least one prime `𝔓` of `𝓞 L` lying over it, and any such `𝔓` is nonzero.
- **How**: Invokes mathlib `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain` for existence of a prime over `𝔭`, packages `LiesOver` from the comap equality, and gets nonvanishing via `Ideal.ne_bot_of_liesOver_of_ne_bot`.
- **Hypotheses**: `𝔭` prime and nonzero.
- **Uses from project**: `[]`
- **Used by**: `exists_frobeniusClass`, `card_primesAbove_mul_orderOf_eq`
- **Visibility**: public
- **Lines**: 78–84 (proof 4 lines)
- **Notes**: none

---

### `theorem UnramifiedIn.ramificationIdx_eq_one`
- **Type**: `[IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1`
- **What**: For a prime `𝔓` of `𝓞 L` over an unramified `𝔭`, the ramification index `e(𝔓 ∣ 𝔭)` is `1`.
- **How**: From `𝔭 ≠ ⊥` get `𝔓 ≠ ⊥` (`Ideal.ne_bot_of_liesOver_of_ne_bot`), then translate the unramified-at hypothesis into `e = 1` via mathlib `Algebra.isUnramifiedAt_iff_of_isDedekindDomain`, feeding the maximality `𝔓.IsPrime.isMaximal`.
- **Hypotheses**: `L/K` Galois; `𝔭` unramified; `𝔓` prime over `𝔭`.
- **Uses from project**: `UnramifiedIn`
- **Used by**: `UnramifiedIn.finite_quotient`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_finrank_eq`
- **Visibility**: public
- **Lines**: 90–96 (proof 4 lines)
- **Notes**: none

---

### `theorem UnramifiedIn.finite_quotient`
- **Type**: `[IsGalois K L] {𝔭 : Ideal (𝓞 K)} (hunr : UnramifiedIn K L 𝔭) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hP : 𝔓.LiesOver 𝔭) : Finite (𝓞 L ⧸ 𝔓)`
- **What**: The residue ring `𝓞 L ⧸ 𝔓` at a prime over an unramified `𝔭` is finite.
- **How**: Applies mathlib `Ideal.finiteQuotientOfFreeOfNeBot` to `𝔓`, with nonvanishing supplied by `ne_bot_of_ramificationIdx_eq_one` fed by `UnramifiedIn.ramificationIdx_eq_one`.
- **Hypotheses**: `L/K` Galois; `𝔭` unramified; `𝔓` prime over `𝔭`.
- **Uses from project**: `UnramifiedIn`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.ramificationIdx_eq_one`
- **Used by**: `isConj_of_isArithFrobAt`, `exists_frobeniusClass`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_finrank_eq`
- **Visibility**: public
- **Lines**: 100–104 (proof 3 lines)
- **Notes**: none

---

### `theorem inertiaGroup_trivial_of_unramified`
- **Type**: `[IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hunr : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) : Ideal.inertia Gal(L/K) 𝔓 = ⊥`
- **What**: When `e(𝔓 ∣ 𝔭) = 1` the inertia subgroup of `Gal(L/K)` at `𝔓` is trivial.
- **How**: Sets up nonvanishing/maximality/finiteness/separability instances, then rewrites `Subgroup.eq_bot_iff_card` and uses mathlib `Ideal.card_inertia_eq_ramificationIdxIn` together with `Ideal.ramificationIdxIn_eq_ramificationIdx` to read off `|I| = e = 1`; separability comes from `IsGalois.to_isSeparable` after locally installing the residue `Field` instances.
- **Hypotheses**: `L/K` Galois; `𝔓` prime with `e(𝔓 ∣ 𝔭) = 1`.
- **Uses from project**: `ne_bot_of_ramificationIdx_eq_one`
- **Used by**: `orderOf_eq_finrank_of_isArithFrobAt`, `card_primesAbove_mul_finrank_eq`
- **Visibility**: public
- **Lines**: 108–123 (proof 13 lines)
- **Notes**: none

---

### `instance faithfulSMul_galois`
- **Type**: `[IsGalois K L] : FaithfulSMul Gal(L/K) (𝓞 L)`
- **What**: The Galois group acts faithfully on `𝓞 L`, pinning the base `𝓞 K` so instance search finds it at every call site.
- **How**: `IsGaloisGroup.faithful (𝓞 K)` for the ring extension `(𝓞 K, 𝓞 L)`.
- **Hypotheses**: `L/K` Galois.
- **Uses from project**: `[]`
- **Used by**: unused in file (consumed implicitly via instance search; no explicit reference)
- **Visibility**: private
- **Lines**: 129–130 (proof 1 line)
- **Notes**: none

---

### `theorem eq_arithFrobAt_of_isArithFrobAt`
- **Type**: `[IsGalois K L] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [Finite (𝓞 L ⧸ 𝔓)] [Algebra.IsUnramifiedAt (𝓞 K) 𝔓] (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) : σ = arithFrobAt (𝓞 K) Gal(L/K) 𝔓`
- **What**: Any arithmetic Frobenius element at an unramified `𝔓` equals the canonical `arithFrobAt 𝔓`.
- **How**: Uniqueness of the Frobenius `AlgHom` via mathlib `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` (with `𝔓.primeCompl_le_nonZeroDivisors`), transferred to the group through injectivity of `MulSemiringAction.toAlgHom` (relying on the private `faithfulSMul_galois`).
- **Hypotheses**: `L/K` Galois; `𝔓` prime, unramified, finite residue field; `σ` an arithmetic Frobenius at `𝔓`.
- **Uses from project**: `[]` (depends on `faithfulSMul_galois` only via instance resolution)
- **Used by**: `isConj_of_isArithFrobAt`, `orderOf_eq_finrank_of_isArithFrobAt`
- **Visibility**: public
- **Lines**: 134–140 (proof 3 lines)
- **Notes**: none

---

### `theorem isConj_of_isArithFrobAt`
- **Type**: `[IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (σ σ' : Gal(L/K)) (𝔓 𝔓' : Ideal (𝓞 L)) [𝔓.IsPrime] [𝔓'.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hσ' : IsArithFrobAt (𝓞 K) σ' 𝔓') (hP : 𝔓.LiesOver 𝔭) (hP' : 𝔓'.LiesOver 𝔭) : IsConj σ σ'`
- **What**: For `𝔭` unramified in `L`, any two arithmetic Frobenius elements at primes `𝔓`, `𝔓'` above `𝔭` are conjugate.
- **How**: Establishes finiteness (`UnramifiedIn.finite_quotient`) and unramified-at instances for `𝔓`, `𝔓'`, rewrites both `σ`, `σ'` to canonical Frobenii via `eq_arithFrobAt_of_isArithFrobAt`, then applies mathlib `isConj_arithFrobAt` (the canonical Frobenii at two primes over the same base are conjugate), with the base equality from `hP.over.symm.trans hP'.over`.
- **Hypotheses**: `L/K` Galois; `𝔭` unramified; `σ, σ'` arithmetic Frobenii at `𝔓, 𝔓'`, each over `𝔭`.
- **Uses from project**: `UnramifiedIn` (`.2`, `.1`), `UnramifiedIn.finite_quotient`, `eq_arithFrobAt_of_isArithFrobAt`
- **Used by**: `exists_frobeniusClass`
- **Visibility**: public
- **Lines**: 145–161 (proof 11 lines)
- **Notes**: long (30–50)? No — proof is 11 lines; flag `none`. Hinges on mathlib `isConj_arithFrobAt` and project `eq_arithFrobAt_of_isArithFrobAt`.

---

### `theorem exists_frobeniusClass`
- **Type**: `[IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) : ∃ C : ConjClasses Gal(L/K), ∀ (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (_ : IsArithFrobAt (𝓞 K) σ 𝔓) (_ : 𝔓.LiesOver 𝔭), C = ConjClasses.mk σ`
- **What**: For an unramified `𝔭` there is a single conjugacy class `C` equal to `[σ]` for every arithmetic Frobenius `σ` at any prime above `𝔭` — existence and well-definedness of the Frobenius class.
- **How**: Picks a reference prime `𝔓₀` above `𝔭` (`exists_prime_liesOver`), takes `C := [arithFrobAt … 𝔓₀]`, and for any candidate `σ` shows `C = [σ]` via `ConjClasses.mk_eq_mk_iff_isConj` reduced to conjugacy by `isConj_of_isArithFrobAt`; finiteness of `𝓞 L ⧸ 𝔓₀` from `UnramifiedIn.finite_quotient`.
- **Hypotheses**: `L/K` Galois; `𝔭` prime, unramified.
- **Uses from project**: `UnramifiedIn`, `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `UnramifiedIn.finite_quotient`, `isConj_of_isArithFrobAt`
- **Used by**: `frobeniusClass`, `frobeniusClass_eq_mk_of_isArithFrobAt`
- **Visibility**: public
- **Lines**: 168–180 (proof 8 lines)
- **Notes**: none

---

### `def frobeniusClass`
- **Type**: `[IsGalois K L] (𝔭 : Ideal (𝓞 K)) : ConjClasses Gal(L/K)`
- **What**: The Frobenius conjugacy class of `𝔭`; for nonzero unramified `𝔭` it is `[σ]` for any arithmetic Frobenius at a prime above `𝔭`, otherwise the junk value `[1]` (never used in the Chebotarev statement).
- **How**: Classical `if`-then-`else` on `𝔭.IsPrime ∧ UnramifiedIn K L 𝔭`; in the positive branch returns `(exists_frobeniusClass K L 𝔭 h.2).choose`, in the negative `ConjClasses.mk 1`.
- **Hypotheses**: `L/K` Galois.
- **Uses from project**: `UnramifiedIn`, `exists_frobeniusClass`
- **Used by**: `frobeniusClass_eq_mk_of_isArithFrobAt`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_orderOf_eq`
- **Visibility**: public
- **Lines**: 188–194 (def body 6 lines; uses `open Classical in`)
- **Notes**: none

---

### `theorem frobeniusClass_eq_mk_of_isArithFrobAt`
- **Type**: `[IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) (hP : 𝔓.LiesOver 𝔭) : frobeniusClass K L 𝔭 = ConjClasses.mk σ`
- **What**: `frobeniusClass K L 𝔭` is the class `[σ]` of any arithmetic Frobenius `σ` at any prime `𝔓` above `𝔭`.
- **How**: Unfolds `frobeniusClass` and takes the positive `dif_pos` branch (using the prime + unramified hypotheses), then applies `(exists_frobeniusClass …).choose_spec` to `σ`, `𝔓`.
- **Hypotheses**: `L/K` Galois; `𝔭` prime, unramified; `σ` arithmetic Frobenius at `𝔓` over `𝔭`.
- **Uses from project**: `UnramifiedIn`, `frobeniusClass`, `exists_frobeniusClass`
- **Used by**: `finrank_residue_eq_orderOf`
- **Visibility**: public
- **Lines**: 198–204 (proof 2 lines)
- **Notes**: none

---

### `theorem orderOf_eq_finrank_of_isArithFrobAt`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (h : Ideal.ramificationIdx (𝔓.under (𝓞 K)) 𝔓 = 1) (hσ : IsArithFrobAt (𝓞 K) σ 𝔓) : orderOf σ = Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓)`
- **What**: At an unramified `𝔓`, the order of the arithmetic Frobenius `σ` equals the residue degree `f = [κ(𝔓) : κ(𝔭)]` (decomposition group is cyclic of order `f`, generated by Frobenius). Flagged in the docstring as an **API gap**.
- **How**: Reduces `σ` to canonical `arithFrobAt` (`eq_arithFrobAt_of_isArithFrobAt`); installs residue `Field`/finiteness/separability/algebraic instances; identifies the image of Frobenius in `Gal(κ(𝔓)/κ(𝔭))` with `FiniteField.frobeniusAlgEquivOfAlgebraic` via `Ideal.Quotient.stabilizerHom_apply` and `IsArithFrobAt.arithFrobAt … .mk_apply`; proves the stabilizer hom injective using `Ideal.Quotient.ker_stabilizerHom` + `inertiaGroup_trivial_of_unramified`; then a `calc` chains `orderOf (arithFrobAt) = orderOf g₀ = orderOf (stabilizerHom g₀) = orderOf (frobeniusAlgEquiv) = finrank` via `Subgroup.orderOf_mk`, `orderOf_injective`, and `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`.
- **Hypotheses**: `L/K` Galois of number fields; `𝔓` prime with `e(𝔓 ∣ 𝔭) = 1`; `σ` arithmetic Frobenius at `𝔓`.
- **Uses from project**: `ne_bot_of_ramificationIdx_eq_one`, `eq_arithFrobAt_of_isArithFrobAt`, `inertiaGroup_trivial_of_unramified`
- **Used by**: `finrank_residue_eq_orderOf`
- **Visibility**: public
- **Lines**: 212–254 (proof 38 lines)
- **Notes**: long (30–50) — proof 38 lines, candidate for `/decompose-proof`. Hinges on mathlib `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`, `Ideal.Quotient.stabilizerHom`/`ker_stabilizerHom`, and project `inertiaGroup_trivial_of_unramified`. Docstring marks the result itself as an API gap (Frobenius generates `D_𝔓`). `open scoped Pointwise in` precedes it.

---

### `theorem card_primesAbove_mul_finrank_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (𝔓₀ : Ideal (𝓞 L)) [𝔓₀.IsPrime] (hlo : 𝔓₀.LiesOver 𝔭) : Nat.card {𝔓 // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * Module.finrank (𝓞 K ⧸ 𝔓₀.under (𝓞 K)) (𝓞 L ⧸ 𝔓₀) = Nat.card Gal(L/K)`
- **What**: (Number of primes of `𝓞 L` above `𝔭`) × (residue degree `[κ(𝔓₀) : κ(𝔭)]`) = `|Gal(L/K)|`, for an unramified `𝔭`.
- **How**: Sets up nonvanishing/maximality/finiteness/separability for `𝔓₀` and `𝔭` (using `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.finite_quotient`); takes mathlib `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank`, kills the inertia factor with `inertiaGroup_trivial_of_unramified` + `Subgroup.card_bot`, then rewrites the `primesOver` set to the subtype set `{𝔓 // IsPrime ∧ LiesOver 𝔭 ∧ ≠ ⊥}` via a set-extensionality argument and `Nat.card_coe_set_eq`.
- **Hypotheses**: `L/K` Galois of number fields; `𝔭` prime, unramified; `𝔓₀` prime over `𝔭`.
- **Uses from project**: `UnramifiedIn.ne_bot`, `UnramifiedIn.ramificationIdx_eq_one`, `ne_bot_of_ramificationIdx_eq_one`, `UnramifiedIn.finite_quotient`, `inertiaGroup_trivial_of_unramified`
- **Used by**: `card_primesAbove_mul_orderOf_eq`
- **Visibility**: public
- **Lines**: 259–289 (proof 25 lines)
- **Notes**: none (25 < 30). Hinges on mathlib `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank` and project `inertiaGroup_trivial_of_unramified`.

---

### `theorem finrank_residue_eq_orderOf`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (hCfrob : frobeniusClass K L 𝔭 = C) (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hlo : 𝔓.LiesOver 𝔭) : Module.finrank (𝓞 K ⧸ 𝔓.under (𝓞 K)) (𝓞 L ⧸ 𝔓) = orderOf σ`
- **What**: When the Frobenius class of `𝔭` is `C = [σ]`, the residue degree `[κ(𝔓) : κ(𝔭)]` at any prime `𝔓` above `𝔭` equals `orderOf σ`.
- **How**: Gets `e = 1` (`UnramifiedIn.ramificationIdx_eq_one`) and finiteness (`UnramifiedIn.finite_quotient`); produces a conjugacy `IsConj (arithFrobAt … 𝔓) σ` by rewriting through `ConjClasses.mk_eq_mk_iff_isConj`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `hCfrob`, `hσ`; then rewrites by `hc.orderOf_eq` (conjugate elements share order) and `orderOf_eq_finrank_of_isArithFrobAt`.
- **Hypotheses**: `L/K` Galois of number fields; `[σ] = C`; `𝔭` prime, unramified; `frobeniusClass 𝔭 = C`; `𝔓` prime over `𝔭`.
- **Uses from project**: `UnramifiedIn.ramificationIdx_eq_one`, `UnramifiedIn.finite_quotient`, `frobeniusClass_eq_mk_of_isArithFrobAt`, `orderOf_eq_finrank_of_isArithFrobAt`, `frobeniusClass` (in hyp)
- **Used by**: `card_primesAbove_mul_orderOf_eq`
- **Visibility**: public
- **Lines**: 293–306 (proof 8 lines)
- **Notes**: none

---

### `theorem card_primesAbove_mul_orderOf_eq`
- **Type**: `(K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (σ : Gal(L/K)) (C : ConjClasses Gal(L/K)) (_hσ : ConjClasses.mk σ = C) (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (hunr : UnramifiedIn K L 𝔭) (_hCfrob : frobeniusClass K L 𝔭 = C) : Nat.card {𝔓 // 𝔓.IsPrime ∧ 𝔓.LiesOver 𝔭 ∧ 𝔓 ≠ ⊥} * orderOf σ = Nat.card Gal(L/K)`
- **What**: Orbit–stabilizer count: (number of primes above `𝔭`) × `orderOf σ` = `|Gal(L/K)|`, with `[σ]` the Frobenius class of the unramified `𝔭`.
- **How**: Picks a prime `𝔓₀` above `𝔭` (`exists_prime_liesOver`), rewrites `orderOf σ` to the residue degree at `𝔓₀` (`finrank_residue_eq_orderOf`), then closes with `card_primesAbove_mul_finrank_eq`.
- **Hypotheses**: `L/K` Galois of number fields; `[σ] = C`; `𝔭` prime, unramified; `frobeniusClass 𝔭 = C`.
- **Uses from project**: `exists_prime_liesOver`, `UnramifiedIn.ne_bot`, `finrank_residue_eq_orderOf`, `card_primesAbove_mul_finrank_eq`, `frobeniusClass` (in hyp)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 313–322 (proof 3 lines)
- **Notes**: none

---

### `theorem finite_ramifiedIn`
- **Type**: `[IsGalois K L] : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ UnramifiedIn K L 𝔭}.Finite`
- **What**: Only finitely many nonzero primes of `K` ramify in `L`.
- **How**: Installs the fraction-field tower/separability for `(𝓞 K, 𝓞 L)`; uses `differentIdeal_ne_bot` to get a nonzero different ideal, so its prime factors are finite (`Ideal.finite_factors`); shows the ramified set is contained in the image of those factors under `under (𝓞 K)`: for a ramified `𝔭` extract a non-unramified maximal `𝔓` over it, and `not_dvd_differentIdeal_iff` forces `𝔓 ∣ differentIdeal`, so `𝔓` is one of the finitely many factors.
- **Hypotheses**: `L/K` Galois (of number fields).
- **Uses from project**: `UnramifiedIn` (unfolded)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 325–346 (proof 20 lines)
- **Notes**: none (20 < 30). Hinges on mathlib `differentIdeal_ne_bot`, `not_dvd_differentIdeal_iff`, and `Ideal.finite_factors`.

---

### `theorem exists_prime_dvd_natCast_mem`
- **Type**: `(𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (n : ℕ) (hn1 : 1 < n) (hmem : (n : 𝓞 K) ∈ 𝔭) : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ (r : 𝓞 K) ∈ 𝔭`
- **What**: If the cast `(n : 𝓞 K)` with `1 < n` lies in a prime `𝔭`, some rational prime factor `r ∣ n` already casts into `𝔭`.
- **How**: Strong induction on `n`: factor `n = r * k` (`Nat.exists_prime_and_dvd`), push the cast, and split with `IsPrime.mem_or_mem`; if `r ∈ 𝔭` done, else recurse on `k` (handling `k = 1` via `Ideal.eq_top_of_isUnit_mem` contradicting `ne_top`), with `k < r*k` justifying the induction.
- **Hypotheses**: `𝔭` prime; `1 < n`; `(n : 𝓞 K) ∈ 𝔭`. (`[NumberField K]` omitted via `omit`.)
- **Uses from project**: `[]`
- **Used by**: `exists_primeFactor_natCast_mem_of_not_coprime`
- **Visibility**: public
- **Lines**: 362–382 (proof 16 lines, in `section BadPrimesFinite` with `variable (m : ℕ)`)
- **Notes**: none. `omit [NumberField K]`. Uses `lia` (Lean-int linear arith tactic).

---

### `theorem exists_primeFactor_natCast_mem_of_not_coprime`
- **Type**: `[NeZero m] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) (hncop : ¬ (Ideal.absNorm 𝔭).Coprime m) : ∃ p ∈ m.primeFactors, (p : 𝓞 K) ∈ 𝔭`
- **What**: A nonzero prime whose norm is not coprime to `m` contains `(p : 𝓞 K)` for some prime factor `p ∣ m`.
- **How**: From `absNorm 𝔭 ≠ 0,1` and `Ideal.absNorm_mem` get (via `exists_prime_dvd_natCast_mem`) a rational prime `r ∈ 𝔭`; show `N𝔭 ∣ r^(finrank ℤ (𝓞 K))` using `Ideal.absNorm_dvd_absNorm_of_le` and `absNorm_span_singleton`/`Algebra.norm_algebraMap`; pick prime `p ∣ gcd(N𝔭, m)`, deduce `p ∣ r^d` hence `p = r` (`Nat.prime_dvd_prime_iff_eq`), giving `p ∈ m.primeFactors` and `(p:𝓞 K) = (r:𝓞 K) ∈ 𝔭`.
- **Hypotheses**: `m ≠ 0`; `𝔭` prime, nonzero; `gcd(N𝔭, m) ≠ 1`.
- **Uses from project**: `exists_prime_dvd_natCast_mem`
- **Used by**: `finite_badPrimes`
- **Visibility**: public
- **Lines**: 387–404 (proof 13 lines)
- **Notes**: none. Uses `lia`.

---

### `theorem finite_primes_natCast_mem`
- **Type**: `(p : ℕ) (hp : p ≠ 0) : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (p : 𝓞 K) ∈ 𝔭}.Finite`
- **What**: The nonzero primes containing a fixed nonzero cast `(p : 𝓞 K)` form a finite set (the prime divisors of `(p)`).
- **How**: `(p)` nonzero (`Ideal.span_singleton_eq_bot`), so `Ideal.finite_factors` makes its factors a finite set; identify membership of the set with being a factor via `Ideal.dvd_iff_le` and `Ideal.span_singleton_le_iff_mem`, using `Set.Finite.ofFinset` over the image of the factor finset.
- **Hypotheses**: `p ≠ 0`.
- **Uses from project**: `[]`
- **Used by**: `finite_badPrimes`
- **Visibility**: public
- **Lines**: 408–423 (proof 12 lines)
- **Notes**: none. `classical`.

---

### `theorem finite_badPrimes`
- **Type**: `[NeZero m] : {𝔭 : Ideal (𝓞 K) | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ (Ideal.absNorm 𝔭).Coprime m}.Finite`
- **What**: The bad-prime set — nonzero primes whose norm is not coprime to `m` — is finite.
- **How**: Covers it by the finite union over `p ∈ m.primeFactors` of `finite_primes_natCast_mem K p` (each `p` nonzero via `Nat.pos_of_mem_primeFactors`); membership in the union for a bad `𝔭` is supplied by `exists_primeFactor_natCast_mem_of_not_coprime`. Uses `Set.Finite.biUnion`/`Set.Finite.subset`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `finite_primes_natCast_mem`, `exists_primeFactor_natCast_mem_of_not_coprime`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 427–437 (proof 8 lines)
- **Notes**: none. `classical`.

---

## File Summary

- **Total declarations: 22** — defs: 2 (`UnramifiedIn`, `frobeniusClass`); lemmas/theorems: 19; instances: 1 (`faithfulSMul_galois`, private). (Also one `section BadPrimesFinite` with `variable (m : ℕ)`.)
- **Key API (used by ≥3 in-file):**
  - `UnramifiedIn` (def) — referenced by 11 in-file decls.
  - `UnramifiedIn.finite_quotient` — used by 4.
  - `ne_bot_of_ramificationIdx_eq_one` — used by 4.
  - `UnramifiedIn.ramificationIdx_eq_one` — used by 3.
  - `inertiaGroup_trivial_of_unramified` — used by 3 (`orderOf_eq_finrank…`, `card_primesAbove_mul_finrank_eq`; +`finrank_residue` transitively — direct count 2; see note).
  - `frobeniusClass` (def) — used by 3.
  - `exists_frobeniusClass` — used by 3.
- **Unused decls (no in-file consumer):** `faithfulSMul_galois` (private instance — used implicitly by instance search, no explicit reference), `card_primesAbove_mul_orderOf_eq`, `finite_ramifiedIn`, `finite_badPrimes`. These four are terminal API for downstream files (the Chebotarev counting/density layer).
- **Decls with `sorry`:** none.
- **Decls with `set_option`:** none.
- **Proofs >50 lines (decompose-needed):** none.
- **Proofs 30–50 lines (long):** `orderOf_eq_finrank_of_isArithFrobAt` — 38 lines (lines 212–254); flagged `long (30–50)`, candidate for `/decompose-proof`. (`card_primesAbove_mul_finrank_eq` is 25 and `finite_ramifiedIn` 20 — under threshold.)
- **API-gap note:** `orderOf_eq_finrank_of_isArithFrobAt` is documented as a genuine mathlib API gap (mathlib lacks "Frobenius generates `D_𝔓`").
