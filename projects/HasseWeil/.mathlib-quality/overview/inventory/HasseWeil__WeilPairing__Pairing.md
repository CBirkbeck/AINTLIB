# Inventory: ./HasseWeil/WeilPairing/Pairing.lean

**File purpose**: Assembles the **definition** of the finite-level Weil pairing `e_ℓ : E[ℓ] × E[ℓ] → F` over an algebraically closed field `F` (with `(ℓ : F) ≠ 0`), via the reviewer-endorsed **constant-ratio** approach (Silverman III.8.1). Ships: the cardinality-based `[ℓ]`-surjectivity on torsion needed to build the Weil function; the chosen Weil function `g_T` with `div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)`; the pairing value `e_ℓ(S,T)` as the constant `τ_S g_T / g_T`; and slot-1 bilinearity plus the root-of-unity core `e_ℓ(S,T)^ℓ = 1`. This is the central definitional spine that every other Weil-pairing file consumes.

**Imports**: `HasseWeil.WeilPairing.DivisorTranslate`, `HasseWeil.WeilPairing.TorsionGeometric`, `HasseWeil.WeilPairing.TorsionModule`

**Total declarations**: 21 (3 `noncomputable def`, 18 `theorem`, of which 1 is `@[simp]`)

**Module options**: `set_option linter.unusedSectionVars false`, `linter.unusedDecidableInType false`, `linter.style.longLine false`. No `sorry`, no `maxHeartbeats`.

**Standing hypotheses** (whole file): `{F : Type*} [Field F] [DecidableEq F]`, `(W : WeierstrassCurve F) [W.toAffine.IsElliptic] [IsIntegrallyClosed (⟨W.toAffine⟩ : SmoothPlaneCurve F).CoordinateRing]`. Most sections additionally open `variable [IsAlgClosed F]`.

---

## Declarations

### `noncomputable def mulByEllTorsionHom`
- **Type**: `(ℓ : ℤ) : W.toAffine[(ℓ ^ 2 : ℤ)] →+ W.toAffine[(ℓ : ℤ)]`
- **What**: The restriction of multiplication-by-`ℓ` to the torsion subgroups, `P ↦ ℓ • P : E[ℓ²] → E[ℓ]`, as an `AddMonoidHom`.
- **How**: Bundles the map `P ↦ ⟨ℓ • P.val, _⟩`; well-definedness is `ℓ • (ℓ • P) = ℓ² • P = 0` for `P ∈ E[ℓ²]` (`smul_smul` + `pow_two` + `mem_torsionSubgroup`); `map_zero'`/`map_add'` by `simp [smul_add]`.
- **Hypotheses**: `[IsAlgClosed F]` (section), `ℓ : ℤ`.
- **Uses from project**: `mem_torsionSubgroup` (TorsionModule)
- **Used by (within file)**: `mulByEllTorsionHom_val`, `mulByEllTorsionHom_surjective`, `exists_preimage_of_torsion`
- **Visibility**: public
- **Lines**: 84–91, proof length: ~6 lines (struct fields)

### `@[simp] theorem mulByEllTorsionHom_val`
- **Type**: `(ℓ : ℤ) (P : W.toAffine[(ℓ ^ 2 : ℤ)]) : (mulByEllTorsionHom W ℓ P).val = ℓ • P.val`
- **What**: The underlying point of `mulByEllTorsionHom W ℓ P` is `ℓ • P.val`.
- **How**: `rfl`.
- **Hypotheses**: `[IsAlgClosed F]`.
- **Uses from project**: `mulByEllTorsionHom` (this file)
- **Used by (within file)**: none referenced by name (proofs use `simp`/`simpa` directly)
- **Visibility**: public
- **Lines**: 93–94, proof length: 1 line
- **Notes**: **Dead-candidate (named).** Never invoked by name anywhere in the project; as a `@[simp]` lemma it may still fire implicitly, but no proof relies on it. The companion `mulByEllTorsionHom` is itself file-internal-only.

### `theorem mulByEllTorsionHom_surjective`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) : Function.Surjective (mulByEllTorsionHom W ℓ)`
- **What**: Over `K̄`, the restricted map `[ℓ] : E[ℓ²] → E[ℓ]` is surjective.
- **How**: A **pure cardinality count**, not curve geometry. Computes `#E[ℓ] = ℓ²` and `#E[ℓ²] = ℓ⁴` (both from `card_torsion_ell`), establishes finiteness of both via `Nat.finite_of_card_ne_zero`, shows the kernel injects into `E[ℓ]` (`Nat.card_le_card_of_injective`) so `#ker ≤ ℓ² = ℓ⁴/ℓ²`, then closes with `AddMonoidHom.surjective_of_card_ker_le_div`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `mulByEllTorsionHom` (this file), `card_torsion_ell` (TorsionCardEll)
- **Used by (within file)**: `exists_preimage_of_torsion`
- **Visibility**: public
- **Lines**: 99–142, proof length: ~43 lines
- **Notes**: Proof >30 lines. Distinct from `mulByInt_point_surjective` (PairingNondeg.lean), which is the full point-surjectivity of `[ℓ]` via division polynomials; this one is only the cardinality-restricted `E[ℓ²]→E[ℓ]` version (see moral-overlap note in summary).

### `theorem exists_preimage_of_torsion`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) : ∃ P₀, ℓ • P₀ = T ∧ (ℓ ^ 2 : ℤ) • P₀ = 0`
- **What**: Every `T ∈ E[ℓ]` has a preimage `P₀` under `[ℓ]` lying in `E[ℓ²]`.
- **How**: Applies `mulByEllTorsionHom_surjective` to `⟨T, _⟩ : E[ℓ]` and reads off the witness and its annihilation from `mem_torsionSubgroup`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `mulByEllTorsionHom_surjective` (this file), `mem_torsionSubgroup` (TorsionModule)
- **Used by (within file)**: `weilFunction_isPrincipal`. **Used by (project)**: `PairingProps.lean` (`weilPairing_self`)
- **Visibility**: public
- **Lines**: 144–153, proof length: ~7 lines

### `theorem mulByInt_ker_finite`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) : Finite (mulByInt W.toAffine ℓ).toAddMonoidHom.ker`
- **What**: Over `K̄`, the kernel `ker[ℓ] = E[ℓ]` is finite.
- **How**: Computes `#E[ℓ] = ℓ.natAbs²` (from `card_torsion_ell`) and concludes finiteness via `Nat.finite_of_card_ne_zero`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `card_torsion_ell` (TorsionCardEll)
- **Used by (within file)**: `weilFunction_isPrincipal`, `weilFunction_divisor`, `weilFunction_transport`. **Used by (project)**: `PairingNondeg`, `PairingProps`, `HfactLemma`, `FrobeniusDivisorGalois`, `DivisorPullback` (the canonical `Finite ker[ℓ]` source over `K̄`).
- **Visibility**: public
- **Lines**: 170–181, proof length: ~9 lines

### `theorem nat_card_mulByInt_ker`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) : (Nat.card (mulByInt W.toAffine ℓ).toAddMonoidHom.ker : ℤ) = ℓ ^ 2`
- **What**: `#ker[ℓ] = ℓ²` (as an integer).
- **How**: Direct restatement of `card_torsion_ell W ℓ hℓ`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`.
- **Uses from project**: `card_torsion_ell` (TorsionCardEll)
- **Used by (within file)**: `weilFunction_isPrincipal`. **Used by (project)**: `PicDualDivisorClassLemma`.
- **Visibility**: public
- **Lines**: 184–186, proof length: 1 line (term)

### `theorem weilFunction_isPrincipal`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) : (W_smooth W).ProjIsPrincipal (pullbackDiv [ℓ] _ T − pullbackDiv [ℓ] _ 0)`
- **What**: The fibre-difference divisor `[ℓ]^*(T) − [ℓ]^*(O)` is principal for `T ∈ E[ℓ]`.
- **How**: Obtains a preimage `P₀` with `ℓ²•P₀ = 0` (`exists_preimage_of_torsion`), then applies `pullbackDiv_sub_isPrincipal` (the Abel–Jacobi step from WeilFunction.lean) with `f P₀ = T` and the annihilation `#ker[ℓ]•P₀ = 0` (rewriting `#ker = ℓ²` via `nat_card_mulByInt_ker`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `pullbackDiv_sub_isPrincipal` (WeilFunction), `exists_preimage_of_torsion`, `mulByInt_ker_finite`, `nat_card_mulByInt_ker` (this file), `mulByInt_apply` (mulByInt API)
- **Used by (within file)**: `weilFunction`, `weilFunction_ne_zero`, `weilFunction_divisor`
- **Visibility**: public
- **Lines**: 191–203, proof length: ~6 lines
- **Notes**: File-internal-only (the "principal" fact is consumed only to define `weilFunction`).

### `noncomputable def weilFunction`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T : W.toAffine.Point) (hT : ℓ • T = 0) : KE`
- **What**: A chosen nonzero function `g_T` with `div(g_T) = [ℓ]^*(T) − [ℓ]^*(O)`.
- **How**: `Classical.choose (weilFunction_isPrincipal …)`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `weilFunction_isPrincipal` (this file)
- **Used by (within file)**: `weilFunction_ne_zero`, `weilFunction_divisor`, `weilFunction_transport`, `weilPairing`, and all pairing theorems. **Used by (project)**: ~20 files (the canonical Weil function `g_T`).
- **Visibility**: public
- **Lines**: 208–210, proof length: 1 line

### `theorem weilFunction_ne_zero`
- **Type**: `… : weilFunction W ℓ hℓ T hT ≠ 0`
- **What**: `g_T ≠ 0`.
- **How**: First component of `Classical.choose_spec (weilFunction_isPrincipal …)`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `weilFunction`, `weilFunction_isPrincipal` (this file)
- **Used by (within file)**: `weilFunction_transport`, `weilPairing`, `weilPairing_spec`. **Used by (project)**: `FrobeniusGaloisScaling`, `SeparableScaling`, `PairingNondeg`, `PairingAdjoint`, `HfactLemma`, `FrobeniusDivisorGalois`, `PairingProps`.
- **Visibility**: public
- **Lines**: 212–215, proof length: 1 line

### `theorem weilFunction_divisor`
- **Type**: `… : (W_smooth W).projectiveDivisorOf (weilFunction W ℓ hℓ T hT) = pullbackDiv [ℓ] _ T − pullbackDiv [ℓ] _ 0`
- **What**: The divisor of `g_T` is the fibre difference `[ℓ]^*(T) − [ℓ]^*(O)`.
- **How**: Second component of `Classical.choose_spec (weilFunction_isPrincipal …)`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `weilFunction`, `weilFunction_isPrincipal` (this file)
- **Used by (within file)**: `weilFunction_transport` (indirectly). **Used by (project)**: `HfactLemma`, `PairingNondeg`, `PairingProps`, `FrobeniusDivisorGalois`, `DivisorPullback` (the divisor identity for `g_T`).
- **Visibility**: public
- **Lines**: 217–224, proof length: 1 line

### `theorem weilFunction_transport`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) : (W_smooth W).projectiveDivisorOf (τ_S g_T / g_T) = 0`
- **What**: For `S ∈ E[ℓ]`, the quotient `τ_S g_T / g_T` has trivial divisor (the fibre-shift payoff that makes the pairing a constant).
- **How**: Applies `projectiveDivisorOf_translate_weilFunction_div_eq_zero` (DivisorTranslate) to `g_T` with `div(g_T)` supplied by `weilFunction_divisor`, discharging the side condition `[ℓ]·S = 0` via `mulByInt_apply` and `hS`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `projectiveDivisorOf_translate_weilFunction_div_eq_zero` (DivisorTranslate), `weilFunction`, `weilFunction_ne_zero`, `weilFunction_divisor`, `mulByInt_ker_finite` (this file), `translateAlgEquivOfPoint` (TranslationOrd)
- **Used by (within file)**: `weilPairing`, `weilPairing_spec`
- **Visibility**: public
- **Lines**: 242–252, proof length: ~5 lines
- **Notes**: File-internal-only.

### `noncomputable def weilPairing`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (S T : W.toAffine.Point) (hS : ℓ • S = 0) (hT : ℓ • T = 0) : F`
- **What**: **The Weil pairing value `e_ℓ(S,T) : F`** (Silverman III.8.1), the constant ratio `τ_S g_T / g_T`.
- **How**: `Classical.choose (pairing_const_of_transport … (weilFunction_transport …))` — extracts the constant from the trivial-divisor hypothesis.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `pairing_const_of_transport` (DivisorTranslate / Constancy chain), `weilFunction`, `weilFunction_ne_zero`, `weilFunction_transport`, `translateAlgEquivOfPoint`
- **Used by (within file)**: all `weilPairing_*` theorems. **Used by (project)**: 16+ files — the core API object.
- **Visibility**: public
- **Lines**: 256–262, proof length: 1 line

### `theorem weilPairing_spec`
- **Type**: `… : weilPairing W ℓ hℓ S T hS hT ≠ 0 ∧ τ_S g_T = algebraMap F KE (e_ℓ(S,T)) * g_T`
- **What**: The defining property of `e_ℓ(S,T)`: a nonzero scalar with `τ_S g_T = e_ℓ(S,T) • g_T`.
- **How**: `Classical.choose_spec (pairing_const_of_transport …)`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `pairing_const_of_transport`, `weilFunction`, `weilFunction_ne_zero`, `weilFunction_transport`, `weilPairing`, `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_ne_zero`, `weilPairing_translate`
- **Visibility**: public
- **Lines**: 266–276, proof length: 1 line
- **Notes**: File-internal-only (consumed via its two projections).

### `theorem weilPairing_ne_zero`
- **Type**: `… : weilPairing W ℓ hℓ S T hS hT ≠ 0`
- **What**: `e_ℓ(S,T) ≠ 0`.
- **How**: First projection of `weilPairing_spec`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `weilPairing_spec`, `weilPairing` (this file)
- **Used by (within file)**: none. **Used by (project)**: `PairingAdjoint`.
- **Visibility**: public
- **Lines**: 279–282, proof length: 1 line

### `theorem weilPairing_translate`
- **Type**: `… : translateAlgEquivOfPoint W S (weilFunction W ℓ hℓ T hT) = algebraMap F KE (e_ℓ(S,T)) * weilFunction W ℓ hℓ T hT`
- **What**: The scalar translation relation `τ_S g_T = e_ℓ(S,T) • g_T`.
- **How**: Second projection of `weilPairing_spec`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S, T ∈ E[ℓ]`.
- **Uses from project**: `weilPairing_spec`, `weilFunction`, `weilPairing`, `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_refl_left`, `weilPairing_mul_left`. **Used by (project)**: `PairingAdjoint`, `FrobeniusGaloisScaling`, `PairingNondeg`, `PairingProps`.
- **Visibility**: public
- **Lines**: 285–290, proof length: 1 line

### `theorem weilPairing_refl_left`
- **Type**: `(ℓ : ℤ) (hℓ : (ℓ : F) ≠ 0) (T) (hT) (h0 : ℓ • (0 : Point) = 0) : weilPairing W ℓ hℓ 0 T h0 hT = 1`
- **What**: `e_ℓ(O,T) = 1` (the pairing is trivial in the first slot at `O`).
- **How**: Since `τ_O = id` (`translateAlgEquivOfPoint W 0 = refl`, definitionally), the relation `τ_O g_T = e_ℓ(O,T)•g_T` becomes `g_T = c•g_T`, forcing `c = 1` via `pairing_const_refl`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `T ∈ E[ℓ]`.
- **Uses from project**: `pairing_const_refl` (DivisorTranslate/Constancy chain), `weilFunction`, `weilFunction_ne_zero`, `weilPairing_translate` (this file), `translateAlgEquivOfPoint`
- **Used by (within file)**: `weilPairing_nsmul_left`, `weilPairing_pow_eq_one`. **Used by (project)**: `PairingAdjoint`, `PairingProps`.
- **Visibility**: public
- **Lines**: 304–314, proof length: ~6 lines

### `theorem weilPairing_mul_left`
- **Type**: `(ℓ) (hℓ) (S₁ S₂ T) (hS₁ hS₂ hT h₁₂) : weilPairing W ℓ hℓ (S₁+S₂) T h₁₂ hT = weilPairing W ℓ hℓ S₁ T hS₁ hT * weilPairing W ℓ hℓ S₂ T hS₂ hT`
- **What**: **Bilinearity in the first slot** (Silverman III.8.1): `e_ℓ(S₁+S₂, T) = e_ℓ(S₁,T)·e_ℓ(S₂,T)`.
- **How**: The translations compose `τ_{S₁+S₂} = τ_{S₂} ∘ τ_{S₁}` (`translateAlgEquivOfPoint_add_apply`); each fixes `F` (`AlgEquiv.commutes`); the three relations `τ_{Sᵢ} g_T = e_ℓ(Sᵢ,T)·g_T` all use the **same** `g_T`. Feeds these to the value-multiplicativity engine `pairing_const_mul`, then `mul_comm`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S₁, S₂, T, S₁+S₂` all in `E[ℓ]`.
- **Uses from project**: `pairing_const_mul` (DivisorTranslate/Constancy chain), `translateAlgEquivOfPoint`, `translateAlgEquivOfPoint_add_apply` (TranslationOrd), `weilFunction`, `weilFunction_ne_zero`, `weilPairing`, `weilPairing_translate` (this file)
- **Used by (within file)**: `weilPairing_nsmul_left`. **Used by (project)**: `PairingProps`, `DetDeg`.
- **Visibility**: public
- **Lines**: 338–358, proof length: ~14 lines

### `theorem weilPairing_congr_left`
- **Type**: `(ℓ) (hℓ) {S S' T} (hS hS' hT) (h : S = S') : weilPairing W ℓ hℓ S T hS hT = weilPairing W ℓ hℓ S' T hS' hT`
- **What**: `e_ℓ(S,T)` depends only on the points (the torsion proofs are irrelevant): equal first arguments give equal values.
- **How**: `subst h; rfl` (proof irrelevance of the `ℓ • S = 0` hypothesis).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, `S = S'`.
- **Uses from project**: `weilPairing` (this file)
- **Used by (within file)**: `weilPairing_nsmul_left`, `weilPairing_pow_eq_one`. **Used by (project)**: `PairingProps`.
- **Visibility**: public
- **Lines**: 362–366, proof length: 1 line

### `theorem smul_nsmul_eq_zero`
- **Type**: `(ℓ : ℤ) (S : W.toAffine.Point) (hS : ℓ • S = 0) (n : ℕ) : ℓ • (n • S) = 0`
- **What**: `n • S` stays `ℓ`-torsion when `S` is (the `ℤ`- and `ℕ`-scalars commute).
- **How**: `smul_comm`, `hS`, `smul_zero`.
- **Hypotheses**: `ℓ • S = 0`. (No `[IsAlgClosed F]` needed; lives in the `Bilinearity` section.)
- **Uses from project**: none (pure mathlib smul algebra)
- **Used by (within file)**: `weilPairing_nsmul_left`. **Used by (project)**: `PairingAdjoint`, `FrobeniusGalois`, `SeparableScaling`.
- **Visibility**: public
- **Lines**: 369–371, proof length: 1 line
- **Notes**: Very general (no curve hypotheses used in body); could be stated for an arbitrary `AddCommGroup` with `ℤ`-action.

### `theorem weilPairing_nsmul_left`
- **Type**: `(ℓ) (hℓ) (S T) (hS hT) (n : ℕ) (h_ns : ℓ • (n • S) = 0) : weilPairing W ℓ hℓ (n • S) T h_ns hT = (weilPairing W ℓ hℓ S T hS hT) ^ n`
- **What**: **Power form of slot-1 bilinearity**: `e_ℓ(n•S, T) = e_ℓ(S,T)^n`.
- **How**: Induction on `n`. Base: `0•S = 0` reduces to `weilPairing_refl_left`. Step: rewrite `(k+1)•S = k•S + S` (`succ_nsmul`), apply `weilPairing_mul_left` and the IH, then `pow_succ`.
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, torsion conditions.
- **Uses from project**: `weilPairing_congr_left`, `weilPairing_refl_left`, `smul_nsmul_eq_zero`, `weilPairing_mul_left`, `weilPairing` (this file)
- **Used by (within file)**: `weilPairing_pow_eq_one`. **Used by (project)**: `PairingAdjoint`.
- **Visibility**: public
- **Lines**: 376–389, proof length: ~10 lines

### `theorem weilPairing_pow_eq_one`
- **Type**: `(ℓ) (hℓ) (S T) (hS hT) : (weilPairing W ℓ hℓ S T hS hT) ^ ℓ.natAbs = 1`
- **What**: **The Weil pairing is an `ℓ`-th root of unity** (Silverman III.8.1, the `μ_ℓ`-valuedness): `e_ℓ(S,T)^ℓ.natAbs = 1`.
- **How**: Pure consequence of slot-1 bilinearity — **no divisor-pullback functoriality**. Shows `(ℓ.natAbs : ℕ)•S = 0` (case-split on `Int.natAbs_eq`), so `e_ℓ(S,T)^ℓ.natAbs = e_ℓ(ℓ.natAbs•S, T)` (`weilPairing_nsmul_left`) `= e_ℓ(O,T) = 1` (`weilPairing_congr_left` + `weilPairing_refl_left`).
- **Hypotheses**: `[IsAlgClosed F]`, `(ℓ : F) ≠ 0`, torsion conditions.
- **Uses from project**: `weilPairing_nsmul_left`, `weilPairing_congr_left`, `weilPairing_refl_left`, `weilPairing` (this file)
- **Used by (within file)**: none. **Used by (project)**: `PairingProps` (`weilPairing_self`/alternating), `DetDeg` (the root-of-unity input to det=deg).
- **Visibility**: public
- **Lines**: 410–423, proof length: ~10 lines

---

## Cross-reference summary

| Declaration | Used by (within file) |
|---|---|
| `mulByEllTorsionHom` | `mulByEllTorsionHom_val`, `mulByEllTorsionHom_surjective`, `exists_preimage_of_torsion` |
| `mulByEllTorsionHom_val` | (none by name) |
| `mulByEllTorsionHom_surjective` | `exists_preimage_of_torsion` |
| `exists_preimage_of_torsion` | `weilFunction_isPrincipal` (+ project: PairingProps) |
| `mulByInt_ker_finite` | `weilFunction_isPrincipal`, `weilFunction_divisor`, `weilFunction_transport` (+ many project) |
| `nat_card_mulByInt_ker` | `weilFunction_isPrincipal` (+ project: PicDualDivisorClassLemma) |
| `weilFunction_isPrincipal` | `weilFunction`, `weilFunction_ne_zero`, `weilFunction_divisor` |
| `weilFunction` | all pairing decls (+ ~20 project files) |
| `weilFunction_ne_zero` | `weilFunction_transport`, `weilPairing`, `weilPairing_spec` (+ project) |
| `weilFunction_divisor` | (project: PairingNondeg/Props, HfactLemma, …) |
| `weilFunction_transport` | `weilPairing`, `weilPairing_spec` |
| `weilPairing` | all `weilPairing_*` (+ 16 project files) |
| `weilPairing_spec` | `weilPairing_ne_zero`, `weilPairing_translate` |
| `weilPairing_ne_zero` | (project: PairingAdjoint) |
| `weilPairing_translate` | `weilPairing_refl_left`, `weilPairing_mul_left` (+ project) |
| `weilPairing_refl_left` | `weilPairing_nsmul_left`, `weilPairing_pow_eq_one` (+ project) |
| `weilPairing_mul_left` | `weilPairing_nsmul_left` (+ project) |
| `weilPairing_congr_left` | `weilPairing_nsmul_left`, `weilPairing_pow_eq_one` (+ project) |
| `smul_nsmul_eq_zero` | `weilPairing_nsmul_left` (+ project) |
| `weilPairing_nsmul_left` | `weilPairing_pow_eq_one` (+ project: PairingAdjoint) |
| `weilPairing_pow_eq_one` | (project: PairingProps, DetDeg) |

**Key API** (the live spine, used widely across the project): `weilFunction`, `weilPairing`, `weilFunction_ne_zero`, `weilFunction_divisor`, `weilPairing_translate`, `mulByInt_ker_finite`, `weilPairing_mul_left`, `weilPairing_pow_eq_one`.

## Notes / cleanup analysis

- **(a) Unused within file**: `weilPairing_pow_eq_one`, `weilPairing_ne_zero`, `weilFunction_divisor`, `mulByInt_ker_finite`, `nat_card_mulByInt_ker`, `exists_preimage_of_torsion`, `smul_nsmul_eq_zero` are not used by later declarations *in this file* but ARE used elsewhere in the project — so not dead. The genuinely file-internal-only declarations (`weilFunction_isPrincipal`, `weilFunction_transport`, `weilPairing_spec`) are intermediate scaffolding and are fine.
- **(a/c) Dead candidate**: `mulByEllTorsionHom_val` (`@[simp]`, L93) is never referenced by name anywhere in the project, and its parent `mulByEllTorsionHom` is file-internal-only. The whole `mulByEllTorsionHom` mini-development (def + simp lemma + `mulByEllTorsionHom_surjective` + `exists_preimage_of_torsion`) exists solely to prove `exists_preimage_of_torsion`; `mulByEllTorsionHom_val` could likely be dropped.
- **(d) Moral overlap (cross-file)**: `mulByEllTorsionHom_surjective` (cardinality `[ℓ] : E[ℓ²]→E[ℓ]`) vs `PairingNondeg.mulByInt_point_surjective` (full division-polynomial `[ℓ]` surjectivity on `E(K̄)`). The latter is strictly stronger; if one prefers a single surjectivity lemma, `exists_preimage_of_torsion` could be re-derived from `mulByInt_point_surjective` + a torsion-membership argument, retiring the cardinality machinery. Kept separate deliberately (the cardinality route avoids the geometric input where it is not needed).
- **(e) Generalisation**: `smul_nsmul_eq_zero` uses no curve structure; it is a general `ℤ`/`ℕ`-smul commutation fact and could be stated for any `AddCommGroup`.
- **No `sorry`, no `maxHeartbeats`.** `mulByEllTorsionHom_surjective` (~43 lines) is the only proof >30 lines.
