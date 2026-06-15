# Inventory: ./HasseWeil/IsogenyBaseChange.lean

**File**: `HasseWeil/IsogenyBaseChange.lean`
**Total declarations**: 24 (0 instances, 9 defs, 15 lemmas/theorems)
**Sorries**: none
**maxHeartbeats overrides**: none

---

## Overview

This file provides the witness-parametric API for base-changing isogenies from a field `F` to an `F`-algebra `L`. It covers: (1) the `mkBaseChange` explicit constructor for base-changed isogenies; (2) the degree-preservation identity under base-change; (3) the Pic⁰-level dual construction (`dualOfPicZeroPullback`) feeding the §5.5 polarisation cascade; (4) the Frobenius-twist trivialisation lemmas for curves over `F_p` and `F_{p^r}`; and (5) the `frobeniusIsog_relative_iterate` / `frobeniusIsog_baseChange_charP_pow` / `iteratedFrobenius_isog` constructions for the iterated relative Frobenius endomorphism.

---

### `noncomputable def mkBaseChange`

- **Type**: `(pullback_L : FF(W₂_L) →ₐ[L] FF(W₁_L)) → (toAddMonoidHom_L : W₁_L.Point →+ W₂_L.Point) → Isogeny (W₁.baseChange L) (W₂.baseChange L)`
- **What**: Explicit record constructor for a base-changed isogeny, packaging a supplied function-field pullback and point group hom.
- **How**: Pure structure literal `{ pullback := pullback_L, toAddMonoidHom := toAddMonoidHom_L }`.
- **Hypotheses**: `L` is a field and an `F`-algebra; both base-changed curves are elliptic.
- **Uses from project**: `HasseWeil.Isogeny` (the record type)
- **Used by**: `mkBaseChange_pullback`, `mkBaseChange_toAddMonoidHom` (simp lemmas in this file)
- **Visibility**: public
- **Lines**: 57–65, proof length ~9 lines
- **Notes**: none

---

### `@[simp] theorem mkBaseChange_pullback`

- **Type**: `(mkBaseChange L pullback_L toAddMonoidHom_L).pullback = pullback_L`
- **What**: The `pullback` field of `mkBaseChange` is definitionally equal to the supplied `pullback_L`.
- **How**: `rfl`.
- **Hypotheses**: same as `mkBaseChange`.
- **Uses from project**: `mkBaseChange`
- **Used by**: unused in this file (external callers)
- **Visibility**: public (simp lemma)
- **Lines**: 67–73, proof 1 line
- **Notes**: none

---

### `@[simp] theorem mkBaseChange_toAddMonoidHom`

- **Type**: `(mkBaseChange L pullback_L toAddMonoidHom_L).toAddMonoidHom = toAddMonoidHom_L`
- **What**: The `toAddMonoidHom` field of `mkBaseChange` is definitionally equal to the supplied hom.
- **How**: `rfl`.
- **Hypotheses**: same as `mkBaseChange`.
- **Uses from project**: `mkBaseChange`
- **Used by**: unused in this file (external callers)
- **Visibility**: public (simp lemma)
- **Lines**: 75–82, proof 1 line
- **Notes**: none

---

### `theorem degree_eq_of_finrank_eq`

- **Type**: Given isogenies `α : Isogeny W₁ W₂` and `α_L : Isogeny (W₁.baseChange L) (W₂.baseChange L)`, and a proof that the `Module.finrank` of the corresponding field extensions agree, concludes `α_L.degree = α.degree`.
- **What**: Witness-parametric degree-preservation under base-change: the degree of the base-changed isogeny equals the original degree, once the function-field finrank equality is supplied.
- **How**: One-line: `h_finrank` is literally the proof (since `Isogeny.degree` is defined as `Module.finrank`).
- **Hypotheses**: A finrank equality witness between the two field extensions (the substantive content, derivable from `Module.finrank_baseChange`).
- **Uses from project**: `HasseWeil.Isogeny` (degree field)
- **Used by**: unused in this file (external callers in downstream base-change pipeline)
- **Visibility**: public
- **Lines**: 92–102, proof 1 line (body is exactly `h_finrank`)
- **Notes**: The 48 "lines" counted above include the long hypothesis block; the proof body is 1 line.

---

### `noncomputable def dualOfPicZeroPullback`

- **Type**: Given `iso : Pic0_W ≃+ W.Point`, an endomorphism `α : Isogeny W W`, Pic⁰-level pushforward `α_pushforward` and pullback `α_pullback`, and a function-field pullback `dual_pullback`, produces the candidate dual `Isogeny W W` whose point map is `iso ∘ α_pullback ∘ iso.symm`.
- **What**: Constructs the candidate dual isogeny via Pic⁰ conjugation: the point-level dual is the iso-conjugate of the Pic⁰ pullback, paired with the externally supplied function-field pullback.
- **How**: Pure record literal; the Pic⁰ conjugate at point level is `iso.toAddMonoidHom.comp (α_pullback.comp iso.symm.toAddMonoidHom)`.
- **Hypotheses**: `Pic0_W` is an abelian group; `iso` is a group equivalence with the elliptic curve points.
- **Uses from project**: `HasseWeil.Isogeny` (record type)
- **Used by**: `dualOfPicZeroPullback_property`, `h_dual_comp_from_picZeroPullback_witness`
- **Visibility**: public
- **Lines**: 141–154, proof ~14 lines
- **Notes**: The function-field pullback is supplied externally (not derivable from Pic⁰ data alone, as noted in the docstring).

---

### `theorem dualOfPicZeroPullback_property`

- **Type**: Under compatibility hypotheses `h_pushforward_compat` and `h_pic_id`, proves `∀ P, (dualOfPicZeroPullback ...).toAddMonoidHom (α.toAddMonoidHom P) = α.degree • P`.
- **What**: The candidate dual satisfies the ℕ-scalar dual composition identity `β ∘ α = [deg α]` at the point level, following from the Pic⁰ identity hypothesis.
- **How**: Rewrites using `h_pushforward_compat` to replace `iso.symm(α P)` by `α_pushforward(iso.symm P)`, then uses `h_pic_id` to get `(deg α) • (iso.symm P)`, then `simp [AddMonoidHom.smul_apply]` and `iso` invertibility.
- **Hypotheses**: `h_pushforward_compat : iso.symm (α P) = α_pushforward (iso.symm P)` for all P; `h_pic_id : α_pullback ∘ α_pushforward = [deg α]` on Pic⁰.
- **Uses from project**: `dualOfPicZeroPullback`
- **Used by**: `h_dual_comp_from_picZeroPullback_witness`
- **Visibility**: public
- **Lines**: 158–182, proof ~25 lines
- **Notes**: none

---

### `theorem cross_compose_zPi_witness`

- **Type**: Given `π, V_π : Isogeny W W`, `q : ℕ`, `t : ℤ`, point-level trace identity `h_trace`, and Frobenius–Verschiebung identity `h_q`, proves the §5.5 cross-composition formula `r • V_π(r • π P − s • P) − s • (r • π P − s • P) = (q r² − t r s + s²) • P` for all `r, s : ℤ`, `P`.
- **What**: Establishes the key §5.4/5.5 polarisation identity in End(E): `(r V_π − s)(r π − s) = q r² − t r s + s²` at the point level, given the trace and degree hypotheses.
- **How**: Applies `map_sub`, `map_zsmul` for the additive hom `V_π.toAddMonoidHom`, substitutes `h_q P` for `V_π(π P) = q • P`, rearranges via `smul_sub/smul_smul`, uses an `abel` helper for group rearrangement, applies `h_trace P` for `V_π P + π P = t • P`, then closes with `ring` on the integer coefficient.
- **Hypotheses**: Trace: `V_π + π = [t]` pointwise; Frobenius–Verschiebung: `V_π ∘ π = [q]` pointwise.
- **Uses from project**: `HasseWeil.Isogeny` (toAddMonoidHom)
- **Used by**: unused in this file (docstring mention only; consumed externally by the §5.5 degree-quadratic-form cascade)
- **Visibility**: public
- **Lines**: 196–233, proof ~38 lines
- **Notes**: Proof >30 lines. This is the core endomorphism algebra identity for the Hasse bound; the heavy use of `smul_smul` and integer ring arithmetic is characteristic.

---

### `theorem qf_nonneg_from_polarisation_witness`

- **Type**: Given `h_realised : ∀ r s : ℤ, ∃ α : Isogeny W W, (q r² − t r s + s²) = (α.degree : ℤ)`, concludes `0 ≤ q r² − t r s + s²`.
- **What**: The quadratic form `q r² − t r s + s²` is non-negative, following from its realisation as an isogeny degree (which is a `ℕ`).
- **How**: Destructs the witness `α` from `h_realised`, rewrites by `hα`, then `Int.natCast_nonneg`.
- **Hypotheses**: Every value of the quadratic form is the cast of some isogeny degree.
- **Uses from project**: `HasseWeil.Isogeny` (degree : ℕ)
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 253–261, proof ~9 lines
- **Notes**: A very thin wrapper; the substantive content is entirely in `h_realised`.

---

### `theorem h_dual_comp_from_picZeroPullback_witness`

- **Type**: Same hypotheses as `dualOfPicZeroPullback_property`, but concludes the ℤ-scalar form `(dualOfPicZeroPullback ...).toAddMonoidHom (α.toAddMonoidHom P) = (α.degree : ℤ) • P`.
- **What**: Converts the ℕ-scalar dual composition identity from `dualOfPicZeroPullback_property` to the ℤ-scalar form expected by downstream consumers (e.g., `DegreeQuadraticForm.degree_quadratic_closed`).
- **How**: Calls `dualOfPicZeroPullback_property` and rewrites via `Nat.cast_smul_eq_nsmul ℤ`.
- **Hypotheses**: Same as `dualOfPicZeroPullback_property`.
- **Uses from project**: `dualOfPicZeroPullback`, `dualOfPicZeroPullback_property`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 274–291, proof ~18 lines
- **Notes**: none

---

### `noncomputable def isogPicPushforward`

- **Type**: `(α : Isogeny W W) : Pic0 →+ Pic0`, defined as `iso.symm ∘ α.toAddMonoidHom ∘ iso`.
- **What**: Transfers an isogeny's point-level action to Pic⁰ by iso-conjugation (the "pushforward" on Pic⁰).
- **How**: Pure composition of additive group homs.
- **Hypotheses**: `iso : Pic0 ≃+ W.Point` is an additive group equivalence.
- **Uses from project**: `HasseWeil.Isogeny`
- **Used by**: `isogPicPushforward_compat`, `isogPicPullback_comp_pushforward`, `isogPicPushforward_compat_frobenius_baseChange_charP_prime`
- **Visibility**: public
- **Lines**: 313–315, proof/def ~3 lines
- **Notes**: keyApi — used by 3+ declarations in this file.

---

### `noncomputable def isogPicPullback`

- **Type**: `(α_dual : Isogeny W W) : Pic0 →+ Pic0`, defined as `iso.symm ∘ α_dual.toAddMonoidHom ∘ iso`.
- **What**: Transfers the dual isogeny's point action to Pic⁰ as the "pullback" (same formula as pushforward, with the dual as input).
- **How**: Pure composition of additive group homs.
- **Hypotheses**: `iso : Pic0 ≃+ W.Point`.
- **Uses from project**: `HasseWeil.Isogeny`
- **Used by**: `isogPicPullback_comp_pushforward`
- **Visibility**: public
- **Lines**: 320–322, proof/def ~3 lines
- **Notes**: none

---

### `theorem isogPicPushforward_compat`

- **Type**: `isogPicPushforward iso α (iso.symm P) = iso.symm (α.toAddMonoidHom P)`
- **What**: The Pic⁰-level pushforward of `iso.symm P` is `iso.symm (α P)` — pure iso inverse cancellation.
- **How**: Unfolds definition, rewrites by `iso.apply_symm_apply`.
- **Hypotheses**: none beyond typing.
- **Uses from project**: `isogPicPushforward`
- **Used by**: `isogPicPushforward_compat_frobenius_baseChange_charP_prime`
- **Visibility**: public
- **Lines**: 327–330, proof ~4 lines
- **Notes**: none

---

### `theorem isogPicPullback_comp_pushforward`

- **Type**: Under `h_dual : ∀ P, α_dual.toAddMonoidHom (α.toAddMonoidHom P) = α.degree • P`, proves `(isogPicPullback iso α_dual).comp (isogPicPushforward iso α) = (AddMonoidHom.id Pic0).comp (α.degree • AddMonoidHom.id Pic0)`.
- **What**: The composition of the Pic⁰-pullback and pushforward equals scalar multiplication by `deg α` on Pic⁰, given the point-level dual composition identity.
- **How**: Extends via `ext D`, unfolds definitions, applies `iso.apply_symm_apply` and `h_dual`, then uses `map_nsmul` and `iso.symm_apply_apply` to finish.
- **Hypotheses**: `h_dual` : the dual composition identity `α_dual ∘ α = [deg α]` at point level.
- **Uses from project**: `isogPicPullback`, `isogPicPushforward`
- **Used by**: unused in this file (external callers)
- **Visibility**: public
- **Lines**: 338–351, proof ~14 lines
- **Notes**: none

---

### `theorem frobenius_eq_id_of_charP_prime`

- **Type**: Under `[Fintype k] [CharP k p] [Fact (Fintype.card k = p)]`, proves `(frobenius k p : k →+* k) = RingHom.id k`.
- **What**: The p-Frobenius ring hom on `F_p` is the identity (Fermat's little theorem).
- **How**: Reduces to showing `x^p = x` for all x ∈ k, uses `FiniteField.pow_card` and the `[Fact (Fintype.card k = p)]` instance to equate `p` and `#k`.
- **Hypotheses**: `k` is a finite field of cardinality `p`.
- **Uses from project**: none
- **Used by**: `frobeniusTwist_baseChange_eq_self_of_charP_prime`
- **Visibility**: public
- **Lines**: 371–381, proof ~11 lines
- **Notes**: none

---

### `theorem frobeniusTwist_baseChange_eq_self_of_charP_prime`

- **Type**: Under `[Fact (Fintype.card k = p)]`, proves `(W.baseChange L).frobeniusTwist p = W.baseChange L` for any `W : WeierstrassCurve k`.
- **What**: For a curve over `F_p` base-changed to any characteristic-p field `L`, the p-Frobenius twist of the base-changed curve is itself.
- **How**: Unfolds `frobeniusTwist` and `baseChange` to a `W.map` composition, uses `RingHom.frobenius_comm` to commute Frobenius past `algebraMap`, then applies `frobenius_eq_id_of_charP_prime` and `RingHom.comp_id`.
- **Hypotheses**: `k = F_p`, `L` has characteristic p (`[ExpChar L p]`).
- **Uses from project**: `frobenius_eq_id_of_charP_prime`
- **Used by**: `frobeniusIsog_baseChange_charP_prime`
- **Visibility**: public
- **Lines**: 385–399, proof ~15 lines
- **Notes**: none

---

### `noncomputable def frobeniusIsog_baseChange_charP_prime`

- **Type**: Returns `Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine` — the p-Frobenius endomorphism on `W.baseChange L` when `k = F_p`.
- **What**: Constructs the p-Frobenius isogeny on `E_L` (for `E` over `F_p`) by casting `frobeniusIsog_relative p (W.baseChange L)` through the type equality `(W.baseChange L).frobeniusTwist p = W.baseChange L`.
- **How**: Uses `cast` with a `congr 2` proof that invokes `frobeniusTwist_baseChange_eq_self_of_charP_prime`; wraps `HasseWeil.frobeniusIsog_relative p (W.baseChange L)`.
- **Hypotheses**: `k = F_p`, `L` has characteristic p, both affine base-changed curves are elliptic.
- **Uses from project**: `frobeniusTwist_baseChange_eq_self_of_charP_prime`, `HasseWeil.frobeniusIsog_relative`
- **Used by**: `isogPicPushforward_compat_frobenius_baseChange_charP_prime`
- **Visibility**: public
- **Lines**: 417–431, def ~15 lines
- **Notes**: Uses `cast` on a type equality proof — a known fragile pattern that can cause downstream `rfl`-failures if the equality changes.

---

### `theorem isogPicPushforward_compat_frobenius_baseChange_charP_prime`

- **Type**: Proves `isogPicPushforward iso (frobeniusIsog_baseChange_charP_prime p W L) (iso.symm P) = iso.symm ((frobeniusIsog_baseChange_charP_prime p W L).toAddMonoidHom P)`.
- **What**: Specialises the general `isogPicPushforward_compat` to the Frobenius isogeny over k̄; provides the `h_pushforward_compat` input needed for `dualOfPicZeroPullback` in the Frobenius case.
- **How**: Direct application of `isogPicPushforward_compat iso (frobeniusIsog_baseChange_charP_prime p W L) P`.
- **Hypotheses**: Same as `frobeniusIsog_baseChange_charP_prime`.
- **Uses from project**: `isogPicPushforward`, `isogPicPushforward_compat`, `frobeniusIsog_baseChange_charP_prime`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 449–463, proof 1 line
- **Notes**: This is essentially a specialised alias for the general compat lemma; may be redundant if callers can use `isogPicPushforward_compat` directly.

---

### `theorem iterateFrobenius_eq_id_of_charP_pow`

- **Type**: Under `[Fact (Fintype.card k = p ^ r)]`, proves `(iterateFrobenius k p r : k →+* k) = RingHom.id k`.
- **What**: The r-fold iterated p-Frobenius on `F_{p^r}` is the identity (generalises `frobenius_eq_id_of_charP_prime` to finite fields).
- **How**: Expands `iterateFrobenius_def` to `x^{p^r}`, rewrites `p^r = Fintype.card k`, then applies `FiniteField.pow_card`.
- **Hypotheses**: `k` is a finite field of cardinality `p^r`.
- **Uses from project**: none
- **Used by**: `frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`, `map_iterateFrobenius_eq_self_of_card_eq_pow`
- **Visibility**: public
- **Lines**: 476–483, proof ~8 lines
- **Notes**: keyApi — used by 2+ declarations in this file. Together with `frobenius_eq_id_of_charP_prime`, these are the foundational Fermat-level facts.

---

### `theorem frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`

- **Type**: Under `[Fact (Fintype.card k = p ^ r)]`, proves `(W.baseChange L).map (iterateFrobenius L p r) = W.baseChange L`.
- **What**: Generalises `frobeniusTwist_baseChange_eq_self_of_charP_prime` to the iterated case: for `E` over `F_{p^r}` base-changed to `L`, the r-fold Frobenius twist of `E_L` is `E_L`.
- **How**: Unfolds to a `W.map` composition, uses `WeierstrassCurve.map_map`, then `RingHom.iterateFrobenius_comm` (naturality of iterated Frobenius), then `iterateFrobenius_eq_id_of_charP_pow` and `RingHom.comp_id`.
- **Hypotheses**: `k = F_{p^r}`, `L` has characteristic p.
- **Uses from project**: `iterateFrobenius_eq_id_of_charP_pow`
- **Used by**: `frobeniusIsog_baseChange_charP_pow`
- **Visibility**: public
- **Lines**: 489–504, proof ~16 lines
- **Notes**: none

---

### `noncomputable def frobeniusIsog_relative_iterate`

- **Type**: `∀ (r : ℕ), Isogeny W.toAffine (W.map (iterateFrobenius k p r)).toAffine` — the r-fold composition of the relative p-Frobenius.
- **What**: Constructs the r-fold iterated relative p-Frobenius isogeny `W → W.map(iter^r)` by recursion on r; base case is the identity (cast through `iterateFrobenius_zero`); inductive case composes via `HasseWeil.frobeniusIsog_relative` and the inductive hypothesis.
- **How**: Recursive definition. Base: `Isogeny.id` cast via `iterateFrobenius_zero + WeierstrassCurve.map_id`. Step: `(frobeniusIsog_relative p (W.map (iter k p n))).comp (frobeniusIsog_relative_iterate p W n)` cast via `WeierstrassCurve.map_map + iterateFrobenius_add + iterateFrobenius_one`.
- **Hypotheses**: `[ExpChar k p]`, `W` is an elliptic curve over `k`.
- **Uses from project**: `HasseWeil.Isogeny.id`, `HasseWeil.frobeniusIsog_relative`, `HasseWeil.Isogeny.comp`
- **Used by**: `frobeniusIsog_baseChange_charP_pow`, `iteratedFrobenius_isog`
- **Visibility**: public
- **Lines**: 519–549, def ~31 lines
- **Notes**: Proof >30 lines. Uses `cast` in both branches; the step-case cast proof invokes `iterateFrobenius_add`. keyApi — used by 2 declarations.

---

### `noncomputable def frobeniusIsog_baseChange_charP_pow`

- **Type**: Returns `Isogeny (W.baseChange L).toAffine (W.baseChange L).toAffine` — the q-Frobenius endomorphism (q = p^r) on `W.baseChange L` for `k = F_{p^r}`.
- **What**: Constructs the q-Frobenius isogeny on `E_L` by casting `frobeniusIsog_relative_iterate p (W.baseChange L) r` through the equality `(W.baseChange L).map(iter L p r) = W.baseChange L`.
- **How**: `cast` using `frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`, applied to `frobeniusIsog_relative_iterate p (W.baseChange L) r`.
- **Hypotheses**: `k = F_{p^r}`, `L` has characteristic p, base-changed curve is elliptic.
- **Uses from project**: `frobeniusTwistIterate_baseChange_eq_self_of_charP_pow`, `frobeniusIsog_relative_iterate`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 556–567, def ~12 lines
- **Notes**: none

---

### `theorem map_iterateFrobenius_eq_self_of_card_eq_pow`

- **Type**: Under `[Fact (Fintype.card k = p^r)]`, proves `W.map (iterateFrobenius k p r) = W` for `W : WeierstrassCurve k`.
- **What**: For a curve over `F_{p^r}` (same-field), the r-fold Frobenius twist of the curve equals itself.
- **How**: Rewrites the iterated Frobenius hom to `RingHom.id k` via `iterateFrobenius_eq_id_of_charP_pow`, then applies `WeierstrassCurve.map_id`.
- **Hypotheses**: `k` is a finite field of cardinality `p^r`.
- **Uses from project**: `iterateFrobenius_eq_id_of_charP_pow`
- **Used by**: `frobeniusTwist_eq_self_of_card_eq_p`
- **Visibility**: public
- **Lines**: 603–610, proof ~8 lines
- **Notes**: none

---

### `theorem frobeniusTwist_eq_self_of_card_eq_p`

- **Type**: Under `[Fact (Fintype.card k = p)]`, proves `W.frobeniusTwist p = W`.
- **What**: Corollary of `map_iterateFrobenius_eq_self_of_card_eq_pow` at `r = 1`: the single p-Frobenius twist of a curve over `F_p` is the curve itself.
- **How**: Constructs `Fact (Fintype.card k = p^1)` from the `p`-case fact, applies `map_iterateFrobenius_eq_self_of_card_eq_pow p 1`, then rewrites by `iterateFrobenius_one`.
- **Hypotheses**: `k` is a finite field of cardinality `p`.
- **Uses from project**: `map_iterateFrobenius_eq_self_of_card_eq_pow`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 617–626, proof ~10 lines
- **Notes**: none

---

### `noncomputable def iteratedFrobenius_isog`

- **Type**: `Σ' (_isElliptic : (W.iterateFrobeniusTwist p e).toAffine.IsElliptic), Isogeny W.toAffine (W.iterateFrobeniusTwist p e).toAffine`
- **What**: Bundles the IsElliptic instance and the e-fold iterated relative Frobenius isogeny `W → W.iterateFrobeniusTwist p e` into a dependent pair (for use in T08/R27 downstream).
- **How**: Derives `ExpChar K p` from `Fact p.Prime`, infers IsElliptic on the codomain, then pairs with `frobeniusIsog_relative_iterate p W e`.
- **Hypotheses**: `K` is a field of characteristic p, `W` is an elliptic curve over `K`.
- **Uses from project**: `frobeniusIsog_relative_iterate`
- **Used by**: unused in this file
- **Visibility**: public
- **Lines**: 639–649, def ~11 lines
- **Notes**: The `Σ'` (anonymous constructor) avoids adding a new named structure; the caller destructures to get both the instance and the isogeny.
