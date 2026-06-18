# Inventory: ./HasseWeil/Hasse/OpenLemmaPrimitives.lean

**Total lines**: ~2205  
**Imports**: `HasseWeil.Hasse.OpenLemmas`, `HasseWeil.Curves.OrdAtPoint`, `HasseWeil.Curves.MillerAllChar`  
**Namespace**: `HasseWeil.OpenLemmaPrimitives`

Purpose: a staging file that states (many with `sorry`) all new primitive lemmas required by the Hasse bound proof that are not in `OpenLemmas.lean`. Grouped into 5 sections mirroring a proof-dependency trace.

---

## Group 1 — Bridge B(i) chain (L2 unblock)

Variables: `K : Type*` `[Field K] [Fintype K] [DecidableEq K]`, `W : WeierstrassCurve K` `[W.toAffine.IsElliptic]`, `hq : 2 ≤ Fintype.card K`

### `theorem kernel_point_is_pole_of_gamma_pullback_x`
- **Type**: `(T : (isogOneSub_negFrobenius W hq).kernel) → (h_witness : ordAtPoint T.val ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) = -2) → ordAtPoint T.val ((isogOneSub_negFrobenius W hq).pullback (x_gen W))⁻¹ = 2`
- **What**: Given a witness hypothesis that the pullback of `x_gen` under `1 − π` has order `−2` at a kernel point `T`, concludes that the inverse has order exactly `2`. The substantive geometry (pullback ord formula) is factored into the hypothesis.
- **How**: One-liner: `rw [SmoothPlaneCurve.ordAtPoint_inv, h_witness]; rfl`. Uses `ordAtPoint_inv` from `OrdAtPoint.lean`.
- **Hypotheses**: Elliptic curve over a finite field with `#K ≥ 2`; a kernel point `T`; a witness providing `ord_T(pullback x_gen) = −2`.
- **Uses from project**: `isogOneSub_negFrobenius`, `x_gen`, `SmoothPlaneCurve.ordAtPoint_inv`
- **Used by**: Unused within this file (intended for external callers)
- **Visibility**: public
- **Lines**: 96–108, proof 3 lines
- **Notes**: Witness-parametric closure pattern; substantive Silverman II.1 + III.4 content remains in `h_witness`.

### `theorem Sinf_ord_nonneg_at_kernel_point`
- **Type**: For a `Sinf` data structure on the pullback of `x_gen`, every element `a` of `data.carrier` has nonneg order at any kernel point `T`.
- **What**: States that Sinf-carrier elements (functions with controlled pole behavior) have nonneg `ordAtPoint` at every kernel point of `1 − π`. Analogous to the affine version shipped in `L6Witnesses.lean`.
- **How**: Left as `sorry`. The proof requires `inv_gamma_pullback_x_pos_at_kernel` which depends on `ord_kernel_pullback_x_eq_neg_two`, which depends on `lemma3_pole_at_T_at_2tor` from `PoleDivisor2Tor.lean` — a downstream file.
- **Hypotheses**: As above plus `data : Sinf` on the pullback, `T : (isogOneSub_negFrobenius W hq).kernel`, `a : data.carrier`.
- **Uses from project**: `isogOneSub_negFrobenius`, `Sinf`, `SmoothPlaneCurve.ordAtPoint`, `LinfAt`, `xIdeal` (implicitly)
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 124–137, proof is `sorry`
- **Notes**: **sorry**. Comment explains the upstream stub remains sorry because the discharge requires a downstream lemma from `PoleDivisor2Tor.lean` — a genuine circular dependency.

### `theorem Sinf_closed_point_prime_bridge`
- **Type**: Given a witness equivalence `(isogOneSub_negFrobenius W hq).kernel ≃ {P : Ideal data.carrier // P.IsPrime ∧ P.LiesOver xIdeal}`, produces `Nonempty` of the same type.
- **What**: The kernel points of `1 − π` are in bijection with prime ideals of the Sinf carrier lying over `xIdeal`. This is the Sinf-side version of Worker K's affine `smoothPoint_fiber_eq_primesOver`.
- **How**: Trivial: `⟨h_witness⟩`. The substantive integral-closure descent content is entirely in the witness hypothesis.
- **Hypotheses**: `data : Sinf` plus a witness bijection `h_witness`.
- **Uses from project**: `isogOneSub_negFrobenius`, `Sinf`, `xIdeal`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 191–213, proof 1 line
- **Notes**: Witness-parametric; the real content (integral closure + closed-point/prime correspondence) remains open per ticket `T-SINF-CLOSED-POINT-PRIME-BRIDGE`.

### `theorem Sinf_inertia_one_at_kernel`
- **Type**: Given a witness `h_inertia_witness` asserting that `inertiaDeg xIdeal (φ T) = 1` for every kernel-prime, re-exports that witness identically.
- **What**: Inertia degree equals 1 at every kernel-prime of `data.carrier` (since kernel points are `𝔽_q`-rational). Trivial wrapper.
- **How**: `h_inertia_witness` (identity).
- **Hypotheses**: `data : Sinf` and a per-kernel-prime inertia witness.
- **Uses from project**: `isogOneSub_negFrobenius`, `Sinf`, `xIdeal`, `Ideal.inertiaDeg`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 238–259, proof 1 line
- **Notes**: Witness-parametric; the residue-field isomorphism `data.carrier ⧸ P_T ≃ₐ[K] K` is the open obligation.

---

## Group 2 — REMOVED

(Group 2 was removed per round-5 reviewer; no declarations.)

---

## Group 3 — L9/L10 deep primitives

Variables: `K : Type*` `[Field K] [Fintype K] [DecidableEq K]`, `W : WeierstrassCurve K` `[W.toAffine.IsElliptic]`

### `theorem mulByP_factors_through_relativeFrobenius`
- **Type**: `(p : ℕ) [Fact p.Prime] [CharP K p] (_h_K_card : Fintype.card K = p) → ∃ ψ : Isogeny W.toAffine W.toAffine, mulByInt W.toAffine (p : ℤ) = ψ.comp (frobeniusIsog W)`
- **What**: In characteristic `p` with `K = 𝔽_p`, the multiplication-by-`p` isogeny factors as `ψ ∘ Frob_p` for some isogeny `ψ` (the cofactor, generally inseparable in the supersingular case).
- **How**: `sorry`. The content is Silverman II.2.12; `ψ.IsSeparable` was removed (round-9 B2 correction, since `ψ` is inseparable for supersingular `E`).
- **Hypotheses**: Prime characteristic `p`, `K = 𝔽_p`.
- **Uses from project**: `mulByInt`, `frobeniusIsog`, `Isogeny`
- **Used by**: Unused within this file (deprecated in favour of `T-RANGE-INCLUSION-PRIMITIVE`)
- **Visibility**: public
- **Lines**: 361–376, proof is `sorry`
- **Notes**: **sorry**. Deprecated per the ticket; workers should target `mulByQ_pullback_range_le_frobenius_pullback_range` instead.

### `theorem mulByPN_factors_through_iterated_pFrobenius`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)] → ∃ ψ : Isogeny W.toAffine W.toAffine, mulByInt W.toAffine ((p : ℤ) ^ r) = ψ.comp (frobeniusIsog W)`
- **What**: Universal-`r` version: `[p^r]` factors through the `q`-Frobenius. Cofactor `ψ` is generally not separable (round-9 correction).
- **How**: `sorry`. Requires Frobenius-tower regrouping + twist iso `E^(q^k) ≃ E` (T-FROBENIUS-TWIST-EQUIV-SELF).
- **Hypotheses**: `K = 𝔽_{p^r}` via `Fact`.
- **Uses from project**: `mulByInt`, `frobeniusIsog`
- **Used by**: Unused within this file (deprecated; prefer B6 form)
- **Visibility**: public
- **Lines**: 427–441, proof is `sorry`
- **Notes**: **sorry**. Marked DEPRECATED; workers should target `T-RANGE-INCLUSION-PRIMITIVE` (B6).

### `theorem mulByPN_factors_unconditional`
- **Type**: `(p r : ℕ) [Fact p.Prime] [CharP K p] (h_card : Fintype.card K = p ^ r) → ∃ ψ : Isogeny W.toAffine W.toAffine, mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) = ψ.comp (frobeniusIsog W)`
- **What**: Explicit-hypothesis version of the `[q]`-factorisation (uses `h_card` instead of `Fact`). The skeleton awaiting `P0-D` (`Isogeny.inseparable_factors_through_pFrobenius`).
- **How**: `sorry`. Proof plan documented inline: iterate P0-D `r` times + twist iso.
- **Hypotheses**: Explicit `h_card : Fintype.card K = p ^ r`.
- **Uses from project**: `mulByInt`, `frobeniusIsog`
- **Used by**: `verschiebung_isDualOf_frobenius_universal` (line 515)
- **Visibility**: public
- **Lines**: 470–480, proof is `sorry`
- **Notes**: **sorry**. Skeleton; intended to discharge once P0-D lands.

### `theorem qth_root_universal_of_factorisation`
- **Type**: Given a factorisation hypothesis `∃ ψ, mulByInt W q = ψ.comp (frobeniusIsog W)`, proves `∀ z, ∃ g, g ^ (#K) = (mulByInt W q).pullback z`.
- **What**: Derives the universal q-th root witness from the factorisation hypothesis by delegating to the Cascade shipped lemma `qth_root_of_q_factors_through_frobenius` (with reversed equation direction via `.symm`).
- **How**: `obtain` the factorisation, apply `HasseWeil.qth_root_of_q_factors_through_frobenius W ⟨ψ, h_eq.symm⟩`.
- **Hypotheses**: The factorisation `∃ ψ, mulByInt W q = ψ.comp (frobeniusIsog W)`.
- **Uses from project**: `HasseWeil.qth_root_of_q_factors_through_frobenius`
- **Used by**: `verschiebung_isDualOf_frobenius_universal` (line 516)
- **Visibility**: public
- **Lines**: 491–500, proof ~10 lines
- **Notes**: Axiom-clean wire-up (no sorry); non-trivial only in the `.symm` direction.

### `theorem verschiebung_isDualOf_frobenius_universal`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ∃ V : Isogeny W.toAffine W.toAffine, IsDualOf W.toAffine V (frobeniusIsog W)`
- **What**: Unconditional Verschiebung existence: there exists an isogeny `V` dual to the Frobenius. Composes `mulByPN_factors_unconditional` + `qth_root_universal_of_factorisation` + Cascade's `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **How**: Calls `FiniteField.card'` to extract `p` and `r`, then chains T7 → T8 → `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`.
- **Hypotheses**: `hq : 2 ≤ Fintype.card K` (K finite).
- **Uses from project**: `mulByPN_factors_unconditional`, `qth_root_universal_of_factorisation`, `HasseWeil.verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`, `frobeniusIsog`
- **Used by**: Unused within this file (exported for `OpenLemmas` consumption)
- **Visibility**: public
- **Lines**: 509–518, proof ~10 lines
- **Notes**: Carries `sorry` via `mulByPN_factors_unconditional` (T7 is still `sorry`).

### `theorem qth_root_witness_universal`
- **Type**: `(z : W.toAffine.FunctionField) → ∃ g, g ^ Fintype.card K = (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z`
- **What**: Route A alternative: every element of `K(E)` has a `q`-th root in the `[q]`-pullback range (universal Φ_q). Downgraded to non-primary route.
- **How**: `sorry`. The content is `Φ_q ∈ K[X^q]` for arbitrary `q = p^r`, research-scale.
- **Hypotheses**: None beyond the curve setting.
- **Uses from project**: `mulByInt`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 540–545, proof is `sorry`
- **Notes**: **sorry**. Downgraded to Route A alternative; NOT the active worker target.

### `theorem verschiebung_from_universal_dual_existence`
- **Type**: `(universal_dual : ∀ α : Isogeny W.toAffine W.toAffine, ∃ α_dual, IsDualOf W.toAffine α_dual α) → ∃ V, IsDualOf W.toAffine V (frobeniusIsog W)`
- **What**: Route C alternative: given a universal dual-existence oracle (Silverman III.6.1 in full generality), the Verschiebung exists trivially by applying it to `frobeniusIsog W`.
- **How**: `obtain ⟨V, hV⟩ := universal_dual (frobeniusIsog W); exact ⟨V, hV⟩`.
- **Hypotheses**: A universal dual existence hypothesis.
- **Uses from project**: `frobeniusIsog`, `IsDualOf`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 560–566, proof 3 lines
- **Notes**: Trivial once `T-III-6-001` lands; kept as alternative statement.

### `theorem dual_additivity_for_one_sub_pi`
- **Type**: `(hq : 2 ≤ Fintype.card K) (V : Isogeny W.toAffine W.toAffine) (_hV : IsDualOf W.toAffine V (frobeniusIsog W)) → ∃ one_sub_V : Isogeny W.toAffine W.toAffine, one_sub_V.toAddMonoidHom = AddMonoidHom.id _ - V.toAddMonoidHom ∧ IsDualOf W.toAffine one_sub_V (isogOneSub_negFrobenius W hq)`
- **What**: Silverman III.6.2(b): from `IsDualOf V π`, constructs the genuine isogeny `1 − V` dual to `1 − π`, with the correct AddMonoidHom identification. The earlier `ψ.IsSeparable` and linear-pullback conjuncts have been removed per the adversarial pass.
- **How**: `sorry`. The obstruction is constructing `1 − V` as a genuine isogeny with its real pullback (requires CLOSE-A `addPullbackAlgHomPair` for the `(id, −V)` pair, 3 outstanding sub-sorries).
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `isogOneSub_negFrobenius`, `frobeniusIsog`, `IsDualOf`, `addIsog` (implied via `addIsog` machinery)
- **Used by**: `trace_eq_pi_plus_dualFrobenius_unconditional_for_V` (line 1651), `l10_trace_eq_witness` (line 1708)
- **Visibility**: public
- **Lines**: 668–696, proof is `sorry`
- **Notes**: **sorry**. Key blocker for L10; requires CLOSE-A with ~660 LOC remaining work.

---

### `private theorem sigma_mulByInt_q_pullback_comm`
- **Type**: `(mulByInt W.toAffine (-1)).pullback.comp (mulByInt W.toAffine (q : ℤ)).pullback = (mulByInt W.toAffine (q : ℤ)).pullback.comp (mulByInt W.toAffine (-1)).pullback`
- **What**: The involution σ = `mulByInt(−1).pullback` commutes with `[q].pullback` at the AlgHom level. Used as a sub-lemma in the σ-V commute proof.
- **How**: Shows `[q] ∘ [−1] = [−q] = [−1] ∘ [q]` using `mulByInt_comp_eq_mul` twice (ring commutativity of `ℤ`), then takes pullbacks.
- **Hypotheses**: None beyond the curve.
- **Uses from project**: `mulByInt_comp_eq_mul`, `frobeniusIsog_degree`, `Isogeny.pullback`
- **Used by**: `sigma_V_pullback_commute_of_isDualOf` (line 799)
- **Visibility**: private
- **Lines**: 716–754, proof 39 lines
- **Notes**: Proof >30 lines. Private helper.

### `theorem sigma_V_pullback_commute_of_isDualOf`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) (hV : IsDualOf W.toAffine V (frobeniusIsog W)) → (mulByInt W.toAffine (-1)).pullback.comp V.pullback = V.pullback.comp (mulByInt W.toAffine (-1)).pullback`
- **What**: σ = `[−1].pullback` commutes with `V.pullback` for any `V` satisfying `IsDualOf V π`. Key structural fact for the σ-invariance chain.
- **How**: `apply AlgHom.ext; intro z; apply (frobeniusIsog W).pullback_injective`. Chain: (A) extract `π.pb ∘ V.pb = [q].pb` from `hV.1`; (B) π-σ commute via `frobeniusIsog_pullback_universal_commute`; (C) σ-[q] commute via `sigma_mulByInt_q_pullback_comm`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `frobeniusIsog_pullback_universal_commute`, `sigma_mulByInt_q_pullback_comm`, `IsDualOf`, `mulByInt`, `frobeniusIsog`
- **Used by**: `sigma_V_pullback_x_eq_of_isDualOf` (line 832), `sigma_V_pullback_y_eq_of_isDualOf` (line 850)
- **Visibility**: public
- **Lines**: 763–815, proof 53 lines
- **Notes**: Proof >30 lines. Core structural lemma for the σ-V chain.

### `theorem sigma_V_pullback_x_eq_of_isDualOf`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) (hV : IsDualOf W.toAffine V (frobeniusIsog W)) → (mulByInt W.toAffine (-1)).pullback (V.pullback (x_gen W)) = V.pullback (x_gen W)`
- **What**: σ fixes `V.pullback (x_gen W)`. Direct consequence of σ-V commute + `mulByInt_pullback_x_neg_one`.
- **How**: Apply `sigma_V_pullback_commute_of_isDualOf` at `x_gen`, then `mulByInt_pullback_x_neg_one`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `sigma_V_pullback_commute_of_isDualOf`, `mulByInt_pullback_x_neg_one`, `x_gen`
- **Used by**: `addPullback_x_pair_frobenius_V_sigma_invariant` (line 881), `sigma_zsmul_neg_one_V_pullback_x_eq_of_isDualOf` (line 946), `sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf` (line 976)
- **Visibility**: public
- **Lines**: 827–837, proof ~11 lines
- **Notes**: 3 callers within file — key API.

### `theorem sigma_V_pullback_y_eq_of_isDualOf`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) (hV : IsDualOf W.toAffine V (frobeniusIsog W)) → (mulByInt W.toAffine (-1)).pullback (V.pullback (y_gen W)) = -V.pullback (y_gen W) - a₁ · V.pullback (x_gen W) - a₃`
- **What**: σ acts on `V.pullback (y_gen W)` as the standard negY formula. Combines σ-V commute with `mulByInt_pullback_y_neg_one` and the K-AlgHom property.
- **How**: Apply `sigma_V_pullback_commute_of_isDualOf` at `y_gen`, rewrite with `mulByInt_pullback_y_neg_one`, then `simp` with `map_sub/neg/mul` + `AlgHom.commutes`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `sigma_V_pullback_commute_of_isDualOf`, `mulByInt_pullback_y_neg_one`, `y_gen`
- **Used by**: `addPullback_x_pair_frobenius_V_sigma_invariant` (line 887), `sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf` (lines 976–977)
- **Visibility**: public
- **Lines**: 842–855, proof ~14 lines
- **Notes**: 3 callers within file — key API.

### `theorem addPullback_x_pair_frobenius_V_sigma_invariant`
- **Type**: σ fixes `addPullback_x_pair (frobeniusIsog W) V`, assuming `h_x_ne` and `IsDualOf V π`.
- **What**: The x-coordinate of the addition pullback for the (π, V) pair is σ-invariant. Feeds the `K(x_gen)` image step for the (π, V) pair.
- **How**: Apply generic `addPullback_x_pair_sigma_invariant` with four σ-action arguments drawn from shipped lemmas (`sigma_frobenius_pullback_x_eq`, `sigma_V_pullback_x_eq_of_isDualOf`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y` + `negFrobeniusIsog_pullback_y_gen`, `sigma_V_pullback_y_eq_of_isDualOf`).
- **Hypotheses**: `IsDualOf V π`, `h_x_ne : π.pb x ≠ V.pb x`.
- **Uses from project**: `addPullback_x_pair_sigma_invariant`, `sigma_frobenius_pullback_x_eq`, `sigma_V_pullback_x_eq_of_isDualOf`, `sigma_frobenius_pullback_y_eq_negFrobenius_pullback_y`, `negFrobeniusIsog_pullback_y_gen`, `sigma_V_pullback_y_eq_of_isDualOf`
- **Used by**: `addPullback_x_pair_frobenius_V_in_KX_image` (line 901)
- **Visibility**: public
- **Lines**: 872–888, proof 17 lines

### `theorem addPullback_x_pair_frobenius_V_in_KX_image`
- **Type**: `(V : Isogeny ...) (hV : IsDualOf ...) (h_x_ne : ...) → ∃ a : FractionRing (Polynomial K), addPullback_x_pair (frobeniusIsog W) V = algebraMap _ _ a`
- **What**: `addPullback_x_pair(π, V)` lies in the `K(x_gen)` subfield, from σ-invariance.
- **How**: One line: `sigma_fixed_implies_in_KX_image W _ (addPullback_x_pair_frobenius_V_sigma_invariant W V hV h_x_ne)`.
- **Hypotheses**: `IsDualOf V π`, `h_x_ne`.
- **Uses from project**: `sigma_fixed_implies_in_KX_image`, `addPullback_x_pair_frobenius_V_sigma_invariant`
- **Used by**: Unused within this file (leaf; feeds T3 externally)
- **Visibility**: public
- **Lines**: 893–901, proof 2 lines

---

### `private theorem sigma_zsmul_neg_one_V_pullback_x_eq_of_isDualOf`
- **Type**: σ fixes `(V.zsmul (-1)).pullback (x_gen W)` given `IsDualOf V π`.
- **What**: Unfolds `(V.zsmul -1).pullback x_gen = V.pullback x_gen` via `mulByInt_pullback_x_neg_one`, then applies `sigma_V_pullback_x_eq_of_isDualOf`.
- **How**: Unfold via `AlgHom.comp_apply` + `mulByInt_pullback_x_neg_one`, then `exact sigma_V_pullback_x_eq_of_isDualOf`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `mulByInt_pullback_x_neg_one`, `sigma_V_pullback_x_eq_of_isDualOf`
- **Used by**: `addPullback_x_pair_id_zsmul_neg_V_sigma_invariant` (line 1005)
- **Visibility**: private
- **Lines**: 934–946, proof ~13 lines

### `private theorem sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf`
- **Type**: σ acts on `(V.zsmul (-1)).pullback (y_gen W)` as the negY formula for `(V.zsmul -1)`, given `IsDualOf V π`.
- **What**: Verifies the standard `negY`-shape σ-action on `(−V).pullback y_gen` by unfolding `(V.zsmul -1).pullback y_gen` and applying `sigma_V_pullback_x/y_eq_of_isDualOf`.
- **How**: Unfold x and y via `mulByInt_pullback_x/y_neg_one`; then distribute σ over the unfolded expression, apply `sigma_V_pullback_x/y_eq_of_isDualOf`, finish with `simp` over map lemmas.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `mulByInt_pullback_x_neg_one`, `mulByInt_pullback_y_neg_one`, `sigma_V_pullback_x_eq_of_isDualOf`, `sigma_V_pullback_y_eq_of_isDualOf`
- **Used by**: `addPullback_x_pair_id_zsmul_neg_V_sigma_invariant` (line 1012)
- **Visibility**: private
- **Lines**: 953–985, proof 33 lines
- **Notes**: Proof >30 lines (33 lines). Private helper.

### `theorem addPullback_x_pair_id_zsmul_neg_V_sigma_invariant`
- **Type**: σ fixes `addPullback_x_pair (Isogeny.id W.toAffine) (V.zsmul (-1))`, assuming `h_x_ne` and `IsDualOf V π`.
- **What**: σ-invariance of the x-coordinate of the `(id, −V)` addition pullback pair. Feeds the `K(x_gen)` image step for T11.
- **How**: `refine addPullback_x_pair_sigma_invariant h_x_ne ?_ ?_ ?_ ?_` with four goals discharged by `mulByInt_pullback_x_neg_one`, `sigma_zsmul_neg_one_V_pullback_x_eq_of_isDualOf`, `mulByInt_pullback_y_neg_one`, `sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf`.
- **Hypotheses**: `IsDualOf V π`, `h_x_ne : id.pb x ≠ (V.zsmul -1).pb x`.
- **Uses from project**: `addPullback_x_pair_sigma_invariant`, `mulByInt_pullback_x_neg_one`, `mulByInt_pullback_y_neg_one`, `sigma_zsmul_neg_one_V_pullback_x_eq_of_isDualOf`, `sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf`
- **Used by**: `addPullback_x_pair_id_zsmul_neg_V_in_KX_image` (line 1027)
- **Visibility**: public
- **Lines**: 992–1012, proof 21 lines

### `theorem addPullback_x_pair_id_zsmul_neg_V_in_KX_image`
- **Type**: `→ ∃ a : FractionRing (Polynomial K), addPullback_x_pair (Isogeny.id) (V.zsmul -1) = algebraMap _ _ a`
- **What**: `addPullback_x_pair(id, −V)` lies in `K(x_gen)`. One-line via σ-fixed → in image.
- **How**: `sigma_fixed_implies_in_KX_image W _ (addPullback_x_pair_id_zsmul_neg_V_sigma_invariant W V hV h_x_ne)`.
- **Hypotheses**: `IsDualOf V π`, `h_x_ne`.
- **Uses from project**: `sigma_fixed_implies_in_KX_image`, `addPullback_x_pair_id_zsmul_neg_V_sigma_invariant`
- **Used by**: `addBaseHomPair_injective_id_zsmul_neg_V_of_pole` (line 1048)
- **Visibility**: public
- **Lines**: 1017–1027, proof 2 lines

### `theorem addBaseHomPair_injective_id_zsmul_neg_V_of_pole`
- **Type**: Given `IsDualOf V π`, `h_x_ne`, `h_pole : ordAtInfty (addPullback_x_pair id (V.zsmul -1)) < 0`, proves `Function.Injective (addBaseHomPair (Isogeny.id) (V.zsmul -1))`.
- **What**: The base hom for the `(id, −V)` pair is injective (so `addIsog` can be constructed). Reduces to showing the candidate is transcendental over `K` by contradiction: if algebraic, the `K(x_gen)` element `a` would be a constant (via `algebraic_in_fracRing_eq_const`), contradicting the pole bound.
- **How**: `rw [addBaseHomPair_eq_aeval]; apply transcendental_iff_injective.mp`. Contradiction via `addPullback_x_pair_id_zsmul_neg_V_in_KX_image` + `algebraic_in_fracRing_eq_const`: the element is a nonzero constant with zero `ordAtInfty` (via `ordAtInfty_algebraMap_F_nonzero`) contradicting `h_pole < 0`; or zero with `ordAtInfty = ⊤`.
- **Hypotheses**: `IsDualOf V π`, `h_x_ne`, `h_pole`.
- **Uses from project**: `addBaseHomPair_eq_aeval`, `transcendental_iff_injective`, `addPullback_x_pair_id_zsmul_neg_V_in_KX_image`, `algebraic_in_fracRing_eq_const`, `ordAtInfty_algebraMap_F_nonzero`, `W_smooth`
- **Used by**: `addCoordAlgHomPair_injective_id_zsmul_neg_V_of_pole` (line 1098)
- **Visibility**: public
- **Lines**: 1033–1079, proof 47 lines
- **Notes**: Proof >30 lines.

### `theorem addCoordAlgHomPair_injective_id_zsmul_neg_V_of_pole`
- **Type**: Given same hypotheses as above, proves `Function.Injective (addCoordAlgHomPair (AddNonInversePair_of_x_ne h_x_ne))`.
- **What**: Injectivity of the coord AlgHom for `(id, −V)`. One-line composition.
- **How**: `addCoordAlgHomPair_injective_of_baseHom_inj _ (addBaseHomPair_injective_id_zsmul_neg_V_of_pole W V hV h_x_ne h_pole)`.
- **Hypotheses**: Same as `addBaseHomPair_injective_id_zsmul_neg_V_of_pole`.
- **Uses from project**: `addCoordAlgHomPair_injective_of_baseHom_inj`, `addBaseHomPair_injective_id_zsmul_neg_V_of_pole`, `AddNonInversePair_of_x_ne`
- **Used by**: `isogOneSub_V` (line 1133)
- **Visibility**: public
- **Lines**: 1084–1098, proof 2 lines

### `noncomputable def isogOneSub_V`
- **Type**: `(V : Isogeny W.toAffine W.toAffine) (hV : IsDualOf ...) (h_x_ne : ...) (h_pole : ...) → Isogeny W.toAffine W.toAffine`
- **What**: Constructs `1 − V` as a genuine isogeny via `addIsog` for the `(Isogeny.id, V.zsmul -1)` pair. The pullback is the genuine addition-formula pullback; the AddMonoidHom is `id − V.toAddMonoidHom`.
- **How**: `addIsog (AddNonInversePair_of_x_ne h_x_ne) (addCoordAlgHomPair_injective_id_zsmul_neg_V_of_pole W V hV h_x_ne h_pole)`.
- **Hypotheses**: `IsDualOf V π`, `h_x_ne`, `h_pole`.
- **Uses from project**: `addIsog`, `AddNonInversePair_of_x_ne`, `addCoordAlgHomPair_injective_id_zsmul_neg_V_of_pole`
- **Used by**: `isogOneSub_V_toAddMonoidHom`, `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply`, `pi_plus_V_eq_isogTrace_toAddMonoidHom_of_T14_witness`, `trace_eq_pi_plus_dualFrobenius_unconditional_for_V` (indirectly)
- **Visibility**: public
- **Lines**: 1122–1133, def body 2 lines

### `@[simp] theorem isogOneSub_V_toAddMonoidHom`
- **Type**: `(isogOneSub_V W V hV h_x_ne h_pole).toAddMonoidHom = AddMonoidHom.id _ - V.toAddMonoidHom`
- **What**: The AddMonoidHom of `isogOneSub_V` is `id − V.toAddMonoidHom`. Direct from `addIsog_toAddMonoidHom` + `Isogeny.zsmul_apply (-1)`.
- **How**: `unfold isogOneSub_V; ext P; rw [addIsog_toAddMonoidHom, ...]` chain of rewrites.
- **Hypotheses**: Same as `isogOneSub_V`.
- **Uses from project**: `isogOneSub_V`, `addIsog_toAddMonoidHom`, `Isogeny.id_toAddMonoidHom`, `Isogeny.zsmul_apply`
- **Used by**: `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply` (line 1522)
- **Visibility**: public (simp lemma)
- **Lines**: 1142–1157, proof ~16 lines

### `theorem V_pullback_x_gen_eq_qth_root`
- **Type**: `(V : Isogeny ...) (hV : IsDualOf ...) → ∃ g, V.pullback (x_gen W) = g ∧ g ^ (#K) = (mulByInt W (#K)).pullback (x_gen W)`
- **What**: `V.pullback (x_gen)` is a `q`-th root of `[q].pullback (x_gen)`. Derived from `hV.1` + Frobenius pullback.
- **How**: `refine ⟨V.pullback (x_gen W), rfl, ?_⟩`. Convert via `congrArg Isogeny.pullback hV.1`, apply `frobeniusIsog_pullback_apply` + `frobeniusIsog_degree`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `frobeniusIsog_pullback_apply`, `frobeniusIsog_degree`, `mulByInt`, `x_gen`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1173–1192, proof ~20 lines

### `theorem isogTrace_def_unfold`
- **Type**: `(hq : 2 ≤ Fintype.card K) → ((isogOneSub_negFrobenius W hq).degree : ℤ) = 1 + ((frobeniusIsog W).degree : ℤ) - isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq)`
- **What**: Rearrangement of the `isogTrace` definition to isolate `(1−π).degree`. Pure algebra from the definition `isogTrace α (1−α) = 1 + α.degree − (1−α).degree`.
- **How**: `unfold isogTrace; ring`.
- **Hypotheses**: `hq`.
- **Uses from project**: `isogOneSub_negFrobenius`, `frobeniusIsog`, `isogTrace`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1204–1209, proof 2 lines

### `theorem h_subset_of_isDualOf`
- **Type**: `(V : Isogeny ...) (hV : IsDualOf ...) → (mulByInt W (#K : ℤ)).pullback.range ≤ (frobeniusIsog W).pullback.range`
- **What**: The Session-3 range inclusion `Im([q]^∗) ⊆ Im(π^∗)` derived from `hV.1`. Every element of `[q]^∗` range is `π^∗(V^∗z)`.
- **How**: `intro f ⟨z, hz⟩; refine ⟨V.pullback z, ?_⟩` then convert via `congrArg Isogeny.pullback hV.1`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `frobeniusIsog_degree`, `IsDualOf`
- **Used by**: `V_pullback_x_gen_eq_verschiebungPullback_of_isDualOf` (lines 1264, 1282, 1284), `V_pullback_y_gen_eq_verschiebungPullback_of_isDualOf` (lines 1294, 1307, 1309), `V_pullback_eq_verschiebungPullback_of_isDualOf` (line 1318)
- **Visibility**: public
- **Lines**: 1237–1254, proof 18 lines
- **Notes**: Used by 3+ declarations — key API.

### `theorem V_pullback_x_gen_eq_verschiebungPullback_of_isDualOf`
- **Type**: `V.pullback (x_gen W) = verschiebungPullback_of_witness W (h_subset_of_isDualOf W V hV) (x_gen W)`
- **What**: The V-pullback of `x_gen` agrees with the canonical verschiebung construction at `x_gen`. Both have the same q-th power; Frobenius injectivity gives equality.
- **How**: `apply (frobeniusIsog W).pullback_injective`. LHS q-th power from `hV.1`; RHS from `mulByInt_q_factor_via_witness`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `h_subset_of_isDualOf`, `verschiebungPullback_of_witness`, `mulByInt_q_factor_via_witness`, `frobeniusIsog_degree`, `frobeniusIsog`
- **Used by**: `V_pullback_eq_verschiebungPullback_of_isDualOf` (line 1320)
- **Visibility**: public
- **Lines**: 1260–1285, proof 26 lines

### `theorem V_pullback_y_gen_eq_verschiebungPullback_of_isDualOf`
- **Type**: Same as x version but for `y_gen`.
- **What**: The V-pullback of `y_gen` agrees with the canonical verschiebung construction at `y_gen`.
- **How**: Identical argument to the x version.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `h_subset_of_isDualOf`, `verschiebungPullback_of_witness`, `mulByInt_q_factor_via_witness`, `frobeniusIsog`
- **Used by**: `V_pullback_eq_verschiebungPullback_of_isDualOf` (line 1321)
- **Visibility**: public
- **Lines**: 1290–1310, proof 21 lines

### `theorem V_pullback_eq_verschiebungPullback_of_isDualOf`
- **Type**: `V.pullback = verschiebungPullback_of_witness W (h_subset_of_isDualOf W V hV)` (as AlgHom equality)
- **What**: Full AlgHom identification: `V.pullback` agrees with the canonical verschiebung pullback construction.
- **How**: `algHom_ext_x_y_gen W (V_pullback_x_gen_eq_verschiebungPullback_of_isDualOf W V hV) (V_pullback_y_gen_eq_verschiebungPullback_of_isDualOf W V hV)`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `algHom_ext_x_y_gen`, `V_pullback_x_gen_eq_verschiebungPullback_of_isDualOf`, `V_pullback_y_gen_eq_verschiebungPullback_of_isDualOf`, `h_subset_of_isDualOf`, `verschiebungPullback_of_witness`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1315–1321, proof 3 lines

### `theorem addPullback_x_pair_frobenius_V_explicit`
- **Type**: `(V : Isogeny ...) (h_x_ne : π.pb x ≠ V.pb x) → addPullback_x_pair (frobeniusIsog W) V = L² + a₁·L − a₂ − x^q − V.pb x` where `L = (y^q − V.pb y)/(x^q − V.pb x)`
- **What**: Explicit rational-function formula for `addPullback_x_pair(π, V)` using the secant-slope form, after substituting `π.pb f = f^q`.
- **How**: `unfold addPullback_x_pair; rw [... addSlopePair_eq_of_x_ne h_x_ne, frobeniusIsog_pullback_apply, frobeniusIsog_pullback_apply]; rfl`.
- **Hypotheses**: `h_x_ne`.
- **Uses from project**: `addSlopePair_eq_of_x_ne`, `frobeniusIsog_pullback_apply`, `addPullback_x_pair`, `x_gen`, `y_gen`, `W_KE`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1339–1367, proof ~29 lines

### `theorem addPullbackAlgHomPair_x_gen_eq`
- **Type**: `addPullbackAlgHomPair hxy hinj (x_gen W) = addPullback_x_pair α₁ α₂`
- **What**: Evaluation of `addPullbackAlgHomPair` at `x_gen`: it equals `addPullback_x_pair`. Direct unfolding via `IsFractionRing.liftAlgHom_apply` + `AdjoinRoot.lift_mk`.
- **How**: `unfold addPullbackAlgHomPair; rw [IsFractionRing.liftAlgHom_apply]; ...` chain ending in `simp [addBaseHomPair, Polynomial.eval₂_C]`.
- **Hypotheses**: `hxy : AddNonInversePair α₁ α₂`, `hinj`.
- **Uses from project**: `addPullbackAlgHomPair`, `addCoordAlgHomPair`, `addCoordRingHomPair`, `addBaseHomPair`, `addPullback_x_pair`, `x_gen`
- **Used by**: `addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses` (line 1457)
- **Visibility**: public
- **Lines**: 1396–1413, proof 18 lines

### `theorem addPullbackAlgHomPair_y_gen_eq`
- **Type**: `addPullbackAlgHomPair hxy hinj (y_gen W) = addPullback_y_pair α₁ α₂`
- **What**: Same as x version but for `y_gen`. Uses `AdjoinRoot.lift_root` + `AdjoinRoot.mk_X.symm` + `AdjoinRoot.lift_mk` + `simp [Polynomial.eval₂_X]`.
- **How**: Analogous to x version; uses `AdjoinRoot.lift_root` at the root point.
- **Hypotheses**: Same as x version.
- **Uses from project**: `addPullbackAlgHomPair`, `addCoordRingHomPair`, `addBaseHomPair`, `addPullback_y_pair`, `y_gen`
- **Used by**: `addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses` (line 1459)
- **Visibility**: public
- **Lines**: 1418–1435, proof 18 lines

### `theorem addIsog_pullback_eq_mulByInt_tr_pullback_of_xy_witnesses`
- **Type**: Given x-coord and y-coord equalities `addPullback_x_pair(π,V) = (mulByInt W tr).pb (x_gen)` and `addPullback_y_pair(π,V) = (mulByInt W tr).pb (y_gen)`, proves `(addIsog hxy hinj).pullback = (mulByInt W tr).pullback`.
- **What**: AlgHom lift: two homs from a function field agree iff they agree on generators. Composes T13.f helpers.
- **How**: `rw [addIsog_pullback]; apply algHom_ext_x_y_gen; rw [addPullbackAlgHomPair_x_gen_eq W hxy hinj]; exact h_x; rw [addPullbackAlgHomPair_y_gen_eq W hxy hinj]; exact h_y`.
- **Hypotheses**: `hxy`, `hinj`, `h_x`, `h_y`.
- **Uses from project**: `addIsog_pullback`, `algHom_ext_x_y_gen`, `addPullbackAlgHomPair_x_gen_eq`, `addPullbackAlgHomPair_y_gen_eq`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1445–1460, proof 16 lines

### `theorem V_comp_frobenius_toAddMonoidHom_apply`
- **Type**: `(V : Isogeny ...) (hV : IsDualOf ...) (P : W.toAffine.Point) → V.toAddMonoidHom ((frobeniusIsog W).toAddMonoidHom P) = ((#K : ℕ) : ℤ) • P`
- **What**: `V(π(P)) = q • P` at AddMonoidHom level. Direct from `hV.1` + `mulByInt_apply`.
- **How**: Extract from `hV.1` via `congrArg Isogeny.toAddMonoidHom` + `DFunLike.congr_fun`, then `Isogeny.comp_apply` + `mulByInt_apply`.
- **Hypotheses**: `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `frobeniusIsog_degree`, `mulByInt_apply`, `Isogeny.comp_apply`
- **Used by**: `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply` (line 1529)
- **Visibility**: public
- **Lines**: 1479–1493, proof 15 lines

### `theorem isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply`
- **Type**: At any point `P`, `((1−V).comp (1−π)).toAddMonoidHom P = P + q•P − π.toAddMonoidHom P − V.toAddMonoidHom P`.
- **What**: AddMonoidHom-level expansion of `(1−V) ∘ (1−π)` applied to `P`. Key precursor for T14 (IsDualOf for `(1−V, 1−π)`) and T15 (trace identity).
- **How**: `rw [Isogeny.comp_apply, isogOneSub_V_toAddMonoidHom, isogOneSub_negFrobenius_toAddMonoidHom]`; expand `(id−V)(P−πP)` by group algebra; apply `V_comp_frobenius_toAddMonoidHom_apply`; `abel`.
- **Hypotheses**: `hq`, `IsDualOf V π`, `h_x_ne`, `h_pole`.
- **Uses from project**: `isogOneSub_V_toAddMonoidHom`, `isogOneSub_negFrobenius_toAddMonoidHom`, `V_comp_frobenius_toAddMonoidHom_apply`, `isogOneSub_V`, `isogOneSub_negFrobenius`
- **Used by**: `pi_plus_V_eq_isogTrace_toAddMonoidHom_of_T14_witness` (line 1569)
- **Visibility**: public
- **Lines**: 1499–1531, proof 33 lines
- **Notes**: Proof >30 lines.

### `theorem pi_plus_V_eq_isogTrace_toAddMonoidHom_of_T14_witness`
- **Type**: Given `IsDualOf (isogOneSub_V ...) (isogOneSub_negFrobenius W hq)`, proves `(frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom = (mulByInt W isogTrace).toAddMonoidHom`.
- **What**: Conditional T15: from the `IsDualOf (1−V, 1−π)` witness (h_T14), derives the trace identity `π + V = [tr]` at AddMonoidHom level. Rearranges T14-PARTIAL expansion via `h_T14.1`.
- **How**: Extract `h_T14.1` → AddMonoidHom level → `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply` gives the expansion; solve the rearrangement algebra.
- **Hypotheses**: `hq`, `IsDualOf V π`, `h_x_ne`, `h_pole`, `h_T14`.
- **Uses from project**: `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply`, `isogOneSub_V`, `mulByInt_apply`, `isogTrace`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1546–1595, proof 50 lines
- **Notes**: Proof >30 lines.

### `theorem trace_eq_pi_plus_dualFrobenius_unconditional_for_V`
- **Type**: Given `IsDualOf V π`, `hxy : AddNonInversePair (π, V)`, `hinj`, proves `addIsog hxy hinj = mulByInt W isogTrace`.
- **What**: L10 unconditional trace identity for any V satisfying `IsDualOf V π`. Composes F-3 (`dual_additivity_for_one_sub_pi`) with the shipped `trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness`. The F-4-PULLBACK sub-deliverable `h_pullback_trace` is a `sorry`.
- **How**: `obtain ⟨one_sub_V, h1, h2⟩ := dual_additivity_for_one_sub_pi`; then sorry for the pullback bridge; then `exact OpenLemmas.trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness ...`.
- **Hypotheses**: `hq`, `IsDualOf V π`, `hxy`, `hinj`.
- **Uses from project**: `dual_additivity_for_one_sub_pi`, `OpenLemmas.trace_eq_pi_plus_dualFrobenius_of_dual_additivity_witness`
- **Used by**: `trace_eq_pi_plus_dualFrobenius_unconditional` (line 1685), `l10_trace_eq_witness` (line 1708)
- **Visibility**: public
- **Lines**: 1639–1666, proof 28 lines
- **Notes**: Contains an internal `sorry` (line 1662) for the F-4-PULLBACK bridge.

### `theorem trace_eq_pi_plus_dualFrobenius_unconditional`
- **Type**: For the V extracted from L9 via `.choose`, the trace identity holds.
- **What**: Specialises the V-parametric form to the canonical V from `OpenLemmas.verschiebung_isDualOf_frobenius`.
- **How**: `set V := ... .choose; have hV := ... .choose_spec; intro hxy hinj; exact trace_eq_pi_plus_dualFrobenius_unconditional_for_V W hq V hV hxy hinj`.
- **Hypotheses**: `hq`.
- **Uses from project**: `trace_eq_pi_plus_dualFrobenius_unconditional_for_V`, `OpenLemmas.verschiebung_isDualOf_frobenius`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1672–1685, proof 14 lines

### `theorem l10_trace_eq_witness`
- **Type**: `∀ V, IsDualOf W.toAffine V (frobeniusIsog W) → ∀ hxy hinj, addIsog hxy hinj = mulByInt W isogTrace`
- **What**: Direct witness for `HasseOpenLemmaPack.l10_trace_eq`. Wraps the V-parametric form.
- **How**: `fun V hV hxy hinj => trace_eq_pi_plus_dualFrobenius_unconditional_for_V W hq V hV hxy hinj`.
- **Hypotheses**: `hq`.
- **Uses from project**: `trace_eq_pi_plus_dualFrobenius_unconditional_for_V`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1697–1708, proof ~12 lines

### `theorem pi_plus_V_eq_isogTrace_addMonoidHom`
- **Type**: `[Fintype W.toAffine.Point] (hq : ...) (V : Isogeny ...) (hV : IsDualOf ...) → (frobeniusIsog W).toAddMonoidHom + V.toAddMonoidHom = (mulByInt W isogTrace).toAddMonoidHom`
- **What**: Unconditional trace identity `π + V = [tr]` at AddMonoidHom level, without needing T14/T15 chain. Uses Lagrange (`card_nsmul_eq_zero`) + L6/V.1.3 (`(1−π).degree = pointCount`) to show `(1−π).degree • P = 0`.
- **How**: Step 1: `V.hom = [q].hom` from `hV.2` + `π.hom = id`; Step 2: `(1−π).degree = pointCount` from `OpenLemmas.witness_pc_sep/fin/sepDeg`; Step 3: `card_nsmul_eq_zero` → `(1−π).degree • P = 0`; combine algebra with `abel`.
- **Hypotheses**: `[Fintype W.toAffine.Point]`, `hq`, `IsDualOf V (frobeniusIsog W)`.
- **Uses from project**: `OpenLemmas.witness_pc_sep`, `OpenLemmas.witness_pc_fin`, `OpenLemmas.witness_pc_sepDeg`, `Isogeny.isSeparable_iff_sepDegree_eq_degree`, `frobeniusIsog_degree`, `mulByInt_apply`, `isogTrace`, `isogOneSub_negFrobenius`, `pointCount`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1732–1815, proof 84 lines
- **Notes**: Proof >30 lines (84 lines). Uses `card_nsmul_eq_zero` (mathlib).

---

## Group 4 — char 2/3 generality primitives

Variables: `F : Type*` `[Field F] [DecidableEq F]`, then sometimes `W : Affine F` `[W.IsElliptic]`

### `theorem miller_hypothesis_allChar`
- **Type**: `(W : Affine F) [W.IsElliptic] [IsAlgClosed F] [IsDedekindDomain] [IsIntegrallyClosed] → MillerHypothesis W`
- **What**: All-characteristic `MillerHypothesis` (drops `[NeZero 2]` and `[NeZero 3]`). One-line wrapper delegating to `miller_hypothesis_holds_allChar`.
- **How**: `HasseWeil.Curves.miller_hypothesis_holds_allChar W`.
- **Hypotheses**: Elliptic, algebraically closed, Dedekind, integrally closed.
- **Uses from project**: `HasseWeil.Curves.miller_hypothesis_holds_allChar`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1860–1865, proof 1 line

### `theorem divZeroReduce_allChar`
- **Type**: `(W : Affine F) [W.IsElliptic] [IsAlgClosed F] [IsDedekindDomain] [IsIntegrallyClosed] → DivZeroReduce W`
- **What**: All-characteristic `DivZeroReduce`. One-line wrapper.
- **How**: `HasseWeil.Curves.divZeroReduce_holds_allChar W`.
- **Hypotheses**: Same as above.
- **Uses from project**: `HasseWeil.Curves.divZeroReduce_holds_allChar`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1880–1885, proof 1 line

### `theorem h_pdz_principal_mem_degZero_allChar`
- **Type**: Principal projective divisors on a smooth elliptic curve (alg. closed) have degree 0, for all `F`.
- **What**: Char-uniform version of `principal_mem_degZero`. One-line via `HasseWeil.Curves.SmoothPlaneCurve.principal_mem_degZero`.
- **How**: `fun _ hD => HasseWeil.Curves.SmoothPlaneCurve.principal_mem_degZero (C := ⟨W⟩) hD`.
- **Hypotheses**: `W` elliptic, algebraically closed, Dedekind, integrally closed.
- **Uses from project**: `SmoothPlaneCurve.principal_mem_degZero`
- **Used by**: `picZeroIsoE_of_AFInputs_allChar` (line 1933)
- **Visibility**: public
- **Lines**: 1915–1923, proof 2 lines

### `noncomputable def picZeroIsoE_of_AFInputs_allChar`
- **Type**: `{W : Affine F} [W.IsElliptic] [IsAlgClosed F] [IsDedekindDomain] [IsIntegrallyClosed] (a : AFInputs W) → SmoothPlaneCurve.PicProj₀ ⟨W⟩ ≃+ W.Point`
- **What**: All-characteristic `Pic⁰(E) ≃ E` isomorphism from `AFInputs`. Drops `[NeZero 2/3]`.
- **How**: `HasseWeil.Curves.picZeroIsoE_of_AFInputs_witness_pdz_allChar W a (h_pdz_principal_mem_degZero_allChar W)`.
- **Hypotheses**: Elliptic, algebraically closed, Dedekind, integrally closed; `AFInputs W`.
- **Uses from project**: `HasseWeil.Curves.picZeroIsoE_of_AFInputs_witness_pdz_allChar`, `h_pdz_principal_mem_degZero_allChar`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1925–1933, def body 3 lines

### `theorem isIntegrallyClosed_coordinateRing_allChar`
- **Type**: `(C : SmoothPlaneCurve F) [C.toAffine.IsElliptic] → IsIntegrallyClosed C.CoordinateRing`
- **What**: Char-uniform integral-closedness of the coordinate ring. Currently `sorry`.
- **How**: `sorry`. Requires `T-INTEGRAL-CLOSURE-SEPARABILITY-PIVOT` + `T-DISCRIMINANT-CHAR2-3` sub-tickets.
- **Hypotheses**: Smooth plane elliptic curve over `F`.
- **Uses from project**: None (stub)
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 1951–1954, proof is `sorry`
- **Notes**: **sorry**. Estimated 50–150 LOC.

### `noncomputable def lineThrough`
- **Type**: `(P Q : W.Point) (_hP : P ≠ 0) (_hQ : Q ≠ 0) → (⟨W⟩ : SmoothPlaneCurve F).FunctionField`
- **What**: Projective chord through two distinct non-zero affine points. Returns the linear form as a function-field element.
- **How**: `sorry`.
- **Hypotheses**: `W` elliptic, `P ≠ O`, `Q ≠ O`.
- **Uses from project**: `SmoothPlaneCurve.FunctionField`
- **Used by**: `div_lineThrough` (line 2063)
- **Visibility**: public
- **Lines**: 2007–2009, body is `sorry`
- **Notes**: **sorry**. Estimated 500–1000 LOC for the full `miller_hypothesis_allChar`.

### `noncomputable def tangentLineAt`
- **Type**: `(P : W.Point) (_hP : P ≠ 0) → (⟨W⟩ : SmoothPlaneCurve F).FunctionField`
- **What**: Projective tangent line at a non-zero smooth point. Returns the linear form.
- **How**: `sorry`.
- **Hypotheses**: `W` elliptic, `P ≠ O`.
- **Uses from project**: `SmoothPlaneCurve.FunctionField`
- **Used by**: `div_tangent` (line 2083)
- **Visibility**: public
- **Lines**: 2021–2023, body is `sorry`
- **Notes**: **sorry**.

### `noncomputable def verticalLineThrough`
- **Type**: `(P : W.Point) (_hP : P ≠ 0) → (⟨W⟩ : SmoothPlaneCurve F).FunctionField`
- **What**: Vertical line through a non-zero affine point (returns `X − x(P)` projectivised).
- **How**: `sorry`.
- **Hypotheses**: `W` elliptic, `P ≠ O`.
- **Uses from project**: `SmoothPlaneCurve.FunctionField`
- **Used by**: `div_vertical` (line 2103)
- **Visibility**: public
- **Lines**: 2033–2035, body is `sorry`
- **Notes**: **sorry**.

### `theorem div_lineThrough`
- **Type**: `(P Q : W.Point) (hP : P ≠ 0) (hQ : Q ≠ 0) (_h_ne : P ≠ Q) → projectiveDivisorOf (lineThrough W P Q hP hQ) = (P) + (Q) + (-(P+Q)) - 3·(O)`
- **What**: The projective divisor of the chord equals `(P)+(Q)+(−(P+Q))−3(O)` (Bézout intersection). Silverman III.3.4(e).
- **How**: `sorry`.
- **Hypotheses**: Two distinct non-zero affine points.
- **Uses from project**: `lineThrough`, `SmoothPlaneCurve.projectiveDivisorOf`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 2062–2070, proof is `sorry`
- **Notes**: **sorry**.

### `theorem div_tangent`
- **Type**: `(P : W.Point) (hP : P ≠ 0) → projectiveDivisorOf (tangentLineAt W P hP) = 2·(P) + (−(2P)) − 3·(O)`
- **What**: The projective divisor of the tangent.
- **How**: `sorry`.
- **Uses from project**: `tangentLineAt`, `SmoothPlaneCurve.projectiveDivisorOf`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 2082–2089, proof is `sorry`
- **Notes**: **sorry**.

### `theorem div_vertical`
- **Type**: `(P : W.Point) (hP : P ≠ 0) → projectiveDivisorOf (verticalLineThrough W P hP) = (P) + (−P) − 2·(O)`
- **What**: The projective divisor of the vertical line.
- **How**: `sorry`.
- **Uses from project**: `verticalLineThrough`, `SmoothPlaneCurve.projectiveDivisorOf`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 2102–2109, proof is `sorry`
- **Notes**: **sorry**.

### `theorem legendreFormReplace_a`
- **Type**: `(W : WeierstrassCurve F) → W.toAffine.IsElliptic ↔ W.Δ ≠ 0`
- **What**: Char-uniform smoothness criterion: `IsElliptic ↔ Δ ≠ 0`. Replaces `legendreCurve_Δ_ne_zero_iff` (char ≠ 2 only).
- **How**: `rw [WeierstrassCurve.isElliptic_iff]; exact isUnit_iff_ne_zero`. Two-liner using existing mathlib.
- **Hypotheses**: None.
- **Uses from project**: `WeierstrassCurve.isElliptic_iff`
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 2140–2143, proof 2 lines

---

## Group 5 — final char-uniform Hasse bound

### `theorem hasse_bound_universal`
- **Type**: `{K : Type*} [Field K] [Fintype K] [DecidableEq K] (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] → |pointCount W.toAffine − #K − 1| ≤ 2√(#K)`
- **What**: The final char-uniform Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q` for any elliptic curve over any finite field. Currently `sorry`.
- **How**: `sorry`. Will be a wrapper around `hasse_bound_from_HasseOpenLemmaPack` once Group 4 primitives + existing 12 open lemmas are discharged.
- **Hypotheses**: Elliptic curve over a finite field, `Fintype` on `W.toAffine.Point`.
- **Uses from project**: None (stub)
- **Used by**: Unused within this file
- **Visibility**: public
- **Lines**: 2194–2199, proof is `sorry`
- **Notes**: **sorry**. The ultimate project goal.

---

## Summary statistics

- **Total declarations**: 57 (53 theorems, 5 defs — of which 4 noncomputable, 1 simp theorem, 2 private)
- **Sorries in bodies**: 15 declarations
- **maxHeartbeats**: none set
- **Long proofs (>30 lines)**: `sigma_mulByInt_q_pullback_comm` (39), `sigma_V_pullback_commute_of_isDualOf` (53), `addBaseHomPair_injective_id_zsmul_neg_V_of_pole` (47), `sigma_zsmul_neg_one_V_pullback_y_eq_of_isDualOf` (33), `isogOneSub_V_comp_isogOneSub_negFrobenius_toAddMonoidHom_apply` (33), `pi_plus_V_eq_isogTrace_toAddMonoidHom_of_T14_witness` (50), `pi_plus_V_eq_isogTrace_addMonoidHom` (84)
- **Key API** (used by 3+ in file): `sigma_V_pullback_x_eq_of_isDualOf`, `sigma_V_pullback_y_eq_of_isDualOf`, `h_subset_of_isDualOf`, `dual_additivity_for_one_sub_pi`, `trace_eq_pi_plus_dualFrobenius_unconditional_for_V`
