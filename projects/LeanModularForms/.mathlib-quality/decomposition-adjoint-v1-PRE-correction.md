# Decomposition — Petersson/Hecke-adjoint frontier (diamond-twisted T_p self-adjointness)

**Target.** Close the two residual sorries in
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory/ConcreteFamily.lean` at lines **5198, 5201**,
both inside `petN_heckeT_p_symmetric_form`, so that
`AdjointTheoryPetersson.exists_simultaneous_eigenform_basis` (line 880) becomes axiom-clean
(currently carries `sorryAx` solely through these two leaves; the rest of the chain is
sorry-free — verified: `grep -c sorry` gives 0 in DeltaBSystem, FDTransport, SummandAdjoint,
TileBridge, PeterssonLevelN, AdjointTheory, AdjointTheoryPetersson; 2 in ConcreteFamily).

The two residuals are:
- `SigmaQPermResidual_M_infty p hp hpN f g` (sorry @ 5198) — the M_∞ tile residual.
- `SigmaQPermResidual_upper p hp hpN f g` (sorry @ 5201) — the upper-triangular tile residual.

---

## 0. Mathematical proof actually read from the PDFs (page pointers)

### Diamond–Shurman, *A First Course in Modular Forms*, §5.4–5.5 (the measure-theoretic FD-tile version the Lean proof mirrors)

**Petersson inner product (Def 5.4.1, DS book p.182, PDF idx 194).** Verbatim:
> "Definition 5.4.1. Let Γ ⊂ SL₂(ℤ) be a congruence subgroup. The Petersson inner product,
> ⟨,⟩_Γ : S_k(Γ) × S_k(Γ) → C, is given by
> ⟨f,g⟩_Γ = (1/V_Γ) ∫_{X(Γ)} f(τ) ḡ(τ) (Im(τ))^k dμ(τ)."

**FD-tile decomposition of the integral (DS book p.181, PDF idx 193).** Verbatim:
> "Let Γ ⊂ SL₂(ℤ) be a congruence subgroup and let {α_j} ⊂ SL₂(ℤ) represent the coset space
> {±I}Γ\SL₂(ℤ) … If the function ϕ is Γ-invariant then the sum ∑_j ∫_{D*} ϕ(α_j(τ)) dµ(τ) is
> independent of the choice of coset representatives α_j. Since dµ is SL₂(ℤ)-invariant the sum
> is ∫_{⋃ α_j(D*)} ϕ(τ) dµ(τ). … ∫_{X(Γ)} ϕ(τ)dµ(τ) = ∫_{⋃ α_j(D*)} ϕ(τ)dµ(τ) = ∑_j ∫_{D*} ϕ(α_j(τ)) dµ(τ)."

**GL₂⁺-invariance of dµ (DS Exercise 5.4.1(a), p.181/183, PDF idx 193/195).** Verbatim:
> "Define the hyperbolic measure on the upper half plane, dµ(τ) = dx dy / y², … This is invariant
> under the automorphism group GL₂⁺(ℝ) of H, meaning dµ(α(τ)) = dµ(τ) for all α ∈ GL₂⁺(ℝ) and τ ∈ H."

**Lemma 5.5.1 (technical FD-tile points, DS book p.184, PDF idx 196).** Verbatim:
> "Lemma 5.5.1. Let Γ ⊂ SL₂(ℤ) be a congruence subgroup, and let α ∈ GL₂⁺(ℚ).
> (a) If ϕ : H⁻ → C is continuous, bounded, and Γ-invariant, then
>     ∫_{α⁻¹Γα\H*} ϕ(α(τ)) dµ(τ) = ∫_{X(Γ)} ϕ(τ) dµ(τ).
> (b) If α⁻¹Γα ⊂ SL₂(ℤ) then V_{α⁻¹Γα} = V_Γ and [SL₂(ℤ):α⁻¹Γα] = [SL₂(ℤ):Γ].
> (c) There exist β₁,…,β_n ∈ GL₂⁺(ℚ), where n = [Γ:α⁻¹Γα∩Γ] = [Γ:αΓα⁻¹∩Γ], such that
>     ΓαΓ = ⋃ Γβ_j = ⋃ β_jΓ, with both unions disjoint."

**Proposition 5.5.2 (the adjoint, DS book p.184–186, PDF idx 196–198).** Verbatim:
> "Proposition 5.5.2. Let Γ ⊂ SL₂(ℤ) be a congruence subgroup, and let α ∈ GL₂⁺(ℚ).
> Set α′ = det(α)α⁻¹. Then
> (a) If α⁻¹Γα ⊂ SL₂(ℤ) then for all f ∈ S_k(Γ) and g ∈ S_k(α⁻¹Γα),
>     ⟨f[α]_k, g⟩_{α⁻¹Γα} = ⟨f, g[α′]_k⟩_Γ.
> (b) For all f,g ∈ S_k(Γ), ⟨f[ΓαΓ]_k, g⟩ = ⟨f, g[Γα′Γ]_k⟩.
> In particular, … in any case [ΓαΓ]∗_k = [Γα′Γ]_k."

**Proof of 5.5.2(a) (the change-of-variables, DS book p.185, PDF idx 197).** Verbatim:
> "For part (a), expand the [α]_k operator, note that α′ acts as α⁻¹ on H*, and apply Lemma 5.5.1(a)
> to get ∫_{α⁻¹Γα\H*} (f[α]_k)(τ) ḡ(τ)(Im τ)^k dµ(τ) = ∫_{α⁻¹Γα\H*} (detα)^{k-1} f(α(τ)) j(α,τ)^{-k}
> ḡ(τ)(Im τ)^k dµ(τ) = ∫_{X(Γ)} (detα)^{k-1} f(τ) j(α,α′(τ))^{-k} ḡ(α′(τ)) (Im α′(τ))^k dµ(τ).
> The cocycle condition j(αα′,τ) = j(α,α′(τ)) j(α′,τ), the upper half plane identity
> Im(α′(τ)) = (detα′) Im(τ) |j(α′,τ)|^{-2}, and the observation det α′ = det α reduce the integral to
> ∫_{X(Γ)} f(τ) (g[α′]_k)(τ) (Im τ)^k dµ(τ). Since also V_{α⁻¹Γα} = V_Γ by Lemma 5.5.1(b), the result follows."

**Proof of 5.5.2(b) (sum over double-coset orbit reps, DS book p.185–186, PDF idx 197–198).** Verbatim:
> "For part (b), the relation ΓαΓ = ⋃ Γβ_j from Lemma 5.5.1(c) shows that the {β_j} can serve in
> Definition 5.1.3 of the operator [ΓαΓ]_k. And the relation ΓαΓ = ⋃ β_jΓ gives Γα′Γ = ⋃ Γβ′_j where
> β′_j = det(β)β⁻¹ … Now the result is immediate from (a) with each Γ ∩ β_jΓβ_j⁻¹ in place of Γ,
> ⟨f[ΓαΓ]_k, g⟩_Γ = ∑_j ⟨f[β_j]_k, g⟩_{β_j⁻¹Γβ_j ∩ Γ} = ∑_j ⟨f, g[β′_j]_k⟩_{Γ ∩ β_jΓβ_j⁻¹} = ⟨f, g[Γα′Γ]_k⟩_Γ."

**T_p adjoint specialisation (DS Thm 5.5.3, p.186, PDF idx 198).** Verbatim:
> "Theorem 5.5.3. In the inner product space S_k(Γ₁(N)), the Hecke operators ⟨p⟩ and T_p for p∤N have
> adjoints ⟨p⟩∗ = ⟨p⟩⁻¹ and T_p∗ = ⟨p⟩⁻¹ T_p. … For the second formula, Proposition 5.5.2(b) gives
> T_p∗ = [Γ₁(N) [[1,0],[0,p]] Γ₁(N)]∗_k = [Γ₁(N) [[p,0],[0,1]] Γ₁(N)]_k. … shows that
> Γ₁(N)[[p,0],[0,1]]Γ₁(N) = Γ₁(N)[[1,0],[0,p]]Γ₁(N)[[p,n],[N,m]]. … Since m ≡ p⁻¹ (mod N), the result
> T_p∗ = ⟨p⟩⁻¹ T_p follows."

### Miyake, *Modular Forms*, §2.8 + §4.5 (the abstract adjoint; cross-check)

**Theorem 2.8.2 (Miyake book p.76, PDF idx 84).** Verbatim:
> "Theorem 2.8.2. For α ∈ GL₂(ℝ), we put α′ = det(α)α⁻¹.
> (1) Assume α⁻¹Γ₁α ⊂ Γ₂. Then for α ∈ Γ₁(=Γ₂), (f|_k α, g) = (f, g|_k α′), f(z) ∈ S_k(Γ₁), g(z) ∈ S_k(Γ₂).
> (2) For α ∈ Γ, (f|_k ΓαΓ, g) = (f, g|_k Γα′Γ), f(z) ∈ S_k(Γ), g(z) ∈ S_k(Γ)."

Miyake's proof of 2.8.2(1) is the **same** substitution `z ↦ α⁻¹z = α′z` with
`j(α,α⁻¹z) = j(α,α′z) = det(α)j(α′,z)⁻¹`, `Im(α⁻¹z) = Im(α′z) = det(α′)|j(α′,z)|⁻² Im(z)`,
`det(α)=det(α′)`, `v(αΓα⁻¹\H) = v(Γ\H)`. Part (2) sums over a **common representative set**
`ΓαΓ = ⊔ Γαᵥ = ⊔ αᵥΓ`, so `Γα⁻¹Γ = ⊔ Γα′ᵥ` (Theorem 4.5.3(2)).

**Theorem 4.5.4(2) (Miyake book p.136, PDF idx 144).** Verbatim:
> "(2) T(1, m) and T*(m, l) (resp. T(n) and T*(n)) are the mutual adjoint operators with respect to
> the Petersson inner product on S_k(N, χ)."
and the diamond-twist is 4.5.4(1) (PDF idx 144):
> "(1) For any element f(z) of S_k(N,χ), we have f|T*(n) = χ̄(n)(f|T(n)) if (n,N)=1."

### Lean ↔ source match (one paragraph)

The Lean target `petN_heckeT_p_symmetric_form` is exactly **DS Prop 5.5.2(b)** / **Miyake 4.5.4**
in diamond-twisted form `⟨T_p f, g⟩ = ⟨⟨p⟩f, T_p g⟩` (the `diamondOp_cusp (unitOfCoprime p hpN)`
is the `⟨p⟩` operator). The Lean proof realises the DS sum `⟨f[ΓαΓ]_k,g⟩ = ∑_j ⟨f[β_j]_k,g⟩` as
`peterssonInner ModularGroup.fd` summed over `q : SL(2,ℤ)⧸Γ₁(N)` and over the double-coset orbit
reps `b ∈ range p` (T_p_upper) ⊔ {M_∞} (the explicit β_j set, computed in the project's
`HeckeT_p` files). Each summand identity `⟨f[β_j]_k,g⟩_{fd} = ⟨f, g[β′_j]_k⟩_{β_j • fd}` is exactly
**DS Prop 5.5.2(a)** = **Miyake 2.8.2(1)**, realised in Lean as the FULLY-PROVEN
`peterssonInner_slash_adjoint` (AdjointTheory.lean:770) — whose proof literally performs DS's
substitution: `petersson_slash` (the cocycle + Im identity packaged as
`petersson k (f∣[k]α) g τ = |α.det|^(k-2) · petersson k f (g∣[k]α⁻¹) (α•τ)`) followed by
`(measurePreserving_smul ⟨α,hα⟩ μ_hyp).setIntegral_image_emb` (= DS Exercise 5.4.1(a),
GL₂⁺-invariance of dµ). The `α′ = det(α)α⁻¹` is the project's `peterssonAdj α`. The
`V_{α⁻¹Γα} = V_Γ` volume cancellation is absorbed because the project integrates over the
SAME `μ_hyp` on `ModularGroup.fd` tiles (un-normalised; the `1/V_Γ` factor cancels in the
`petN`-vs-`petN` identity). The double-coset orbit-rep set `ΓαΓ = ⊔ β_jΓ` (DS Lemma 5.5.1(c))
is the project's `T_p_upper(b)` ⊔ `M_∞` decomposition, already established and threaded through
`DSDoubleCosetTileBridge`.

---

## 1. The reduction already in place (no work needed — verified proven)

`petN_heckeT_p_symmetric_form` (5185) reduces via:
`petN_heckeT_p_symmetric_form_of_doubleCosetTileBridge` → `DSDoubleCosetTileBridge` →
`DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed` (2441) → `Finset.sum_add_distrib` →
`congr_arg₂ (·+·)` to the **two residual goals** `SigmaQPermResidual_M_infty` (5198) and
`SigmaQPermResidual_upper` (5201). This entire reduction is sorry-free.

**Both residuals already have PROVEN assemblers** (this is the key finding):
- `SigmaQPermResidual_M_infty_of_TileFormIntegralResidual` (ConcreteFamily:4856) — discharges
  the M_∞ residual GIVEN `h_meas`/`h_disj`/`h_LHS_int`/`h_RHS_int` (M_∞ tiles, nested-`•` shape)
  + `h_tile : TileFormIntegralResidual_M_infty`.
- `SigmaQPermResidual_upper_of_TileFormIntegralResidual` (ConcreteFamily:5135) — discharges the
  upper residual GIVEN the same four hyps `∀ b ∈ range p` + `h_tile : ∀ b, TileFormIntegralResidual_upper`.

There is ALSO a per-q / sigma_p reduction chain for the tile-form identity:
`SigmaQPermResidual_M_infty_of_sigma_p_reduced` (4967), `_of_per_q_tile_form` (4955),
`TileFormIntegralResidual_M_infty_of_sigma_p_reduced` (4845). The per-q analytic identity
`TileFormIntegralResidual_*_per_q` reduces to the PROVEN
`peterssonInner_M_infty_slash_adjoint_coset` (SummandAdjoint:1689) and
`peterssonInner_slash_adj_T_p_upper_q_summand_eq` (SummandAdjoint:~640).

**So the open frontier is precisely: discharge the four FD-tile measure hypotheses (×2 families).**

---

## 2. Leaf tree (closing the 2 residuals)

```
petN_heckeT_p_symmetric_form  [5185, has 2 sorries]
├── (residual 1) SigmaQPermResidual_M_infty                                        [EXIST asm @4856]
│   ├── L-asm-∞: SigmaQPermResidual_M_infty_of_TileFormIntegralResidual            [EXIST, proven]
│   ├── leaf N-∞: ∀q NullMeasurableSet (M_∞ tile)            → nullMeasurableSet_M_infty_q_tile_star   [BUILD-tiny; engine EXIST @SummandAdjoint:1589]
│   ├── leaf D-∞: Pairwise-over-q AEDisjoint (M_∞ tiles)     → aedisjoint_pairwise_M_infty_q_tiles      [BUILD; engine EXIST @SummandAdjoint:1020]
│   ├── leaf I-∞-LHS: IntegrableOn LHS over M_∞ iUnion       → integrableOn_LHS_M_infty_iUnion          [BUILD; per-tile EXIST @DeltaBSystem:1122 + mathlib integrableOn_finset_iUnion]
│   ├── leaf I-∞-RHS: IntegrableOn RHS over M_∞ iUnion       → integrableOn_RHS_M_infty_iUnion          [BUILD; same]
│   └── leaf T-∞: TileFormIntegralResidual_M_infty           [EXIST chain: _of_sigma_p_reduced/_of_per_q_tile_form → peterssonInner_M_infty_slash_adjoint_coset, proven]
├── (residual 2) SigmaQPermResidual_upper                                          [EXIST asm @5135]
│   ├── L-asm-U: SigmaQPermResidual_upper_of_TileFormIntegralResidual              [EXIST, proven]
│   ├── leaf N-U: ∀b∀q NullMeasurableSet (T_p_upper tile)    → nullMeasurableSet_T_p_upper_q_tile_star  [BUILD-tiny; engine EXIST @SummandAdjoint:1162/1214]
│   ├── leaf D-U: ∀b Pairwise-over-q AEDisjoint (T_p_upper)  → aedisjoint_pairwise_T_p_upper_q_tiles     [BUILD; engine EXIST @SummandAdjoint:1020]
│   ├── leaf I-U-LHS: ∀b IntegrableOn LHS over iUnion        → integrableOn_LHS_T_p_upper_iUnion         [BUILD; per-tile EXIST @DeltaBSystem:1122]
│   ├── leaf I-U-RHS: ∀b IntegrableOn RHS over iUnion        → integrableOn_RHS_T_p_upper_iUnion         [BUILD; same]
│   └── leaf T-U: ∀b TileFormIntegralResidual_upper          [EXIST per-q route: peterssonInner_slash_adj_T_p_upper_q_summand_eq, proven]
└── (wiring) bridge composed-`*` shape ⇄ nested-`•` shape; construct TpHeckeFamilyMeasureHypotheses;
    feed assemblers. [BUILD-wiring; mul_smul, done inside ConcreteFamily during EXECUTION]
```

### Underlying analytic substrate (all PROVEN — verified sorry-free)
- `peterssonInner_slash_adjoint` (AdjointTheory:770) = DS 5.5.2(a)/Miyake 2.8.2(1) change-of-variables.
  Rests on mathlib `measurePreserving_smul (⟨α,hα⟩ : GL(2,ℝ)⁺) μ_hyp` = DS Exercise 5.4.1(a).
- `peterssonInner_slash_adjoint_coset` (SummandAdjoint:593), `peterssonInner_M_infty_slash_adjoint_coset`
  (1689), `peterssonInner_slash_adj_T_p_upper_q_summand_eq` (~640): per-q tile identities, proven.
- `peterssonInner_iUnion_finite_aedisjoint` (PeterssonLevelN:1140): tile-sum ⇄ iUnion-integral collapse
  (needs `NullMeasurableSet` ∀i, `Pairwise AEDisjoint`, `IntegrableOn` over the iUnion).
- `measurePreserving_glPos_smul` (SummandAdjoint:902), `aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1`
  (1020), `isFundamentalDomain_Gamma1_coset_tiling` (PeterssonLevelN), `nullMeasurableSet_M_infty_q_tile`
  (1589), `integrableOn_petersson_combinedGL_tile_on_fd` (DeltaBSystem:1122): the leaf engines.
- `Fintype (SL(2,ℤ)⧸Gamma1 N)` (PeterssonLevelN:51); mathlib `integrableOn_finset_iUnion`
  (`Mathlib/MeasureTheory/Integral/IntegrableOn.lean:227`) + its `Fintype.univ` corollary.

---

## 3. Per-leaf verbatim-source + Lean-citation map

| Leaf | Source (verbatim §) | Lean discharge route (EXIST vs BUILD) |
|---|---|---|
| **N-∞** NullMeas M_∞ tile | DS p.181 "Since the set ℚ∪{∞} … has measure zero, and so dµ suffices … D* = {…}" (D* measurable) | BUILD-tiny: `mul_smul` + EXIST `nullMeasurableSet_M_infty_q_tile` (SummandAdjoint:1589). |
| **N-U** NullMeas T_p_upper tile | same DS p.181 | BUILD-tiny: `nullMeasurableSet_fd_aux` (SummandAdjoint:1162) + `measurePreserving_glPos_smul` preimage (pattern @1214). |
| **D-∞** Pairwise-q AEDisjoint M_∞ | DS Lemma 5.5.1 + Def 5.4.1 setup p.181 "the union SL₂(ℤ)=⋃_j {±I}Γα_j is disjoint" | BUILD: EXIST engine `aedisjoint_glMap_smul_of_mul_inv_eq_mapGL_Gamma1` (SummandAdjoint:1020) with `α=glMap M_∞`; need `(glMap M_∞ · mapGL q₁.out⁻¹)⁻¹·(glMap M_∞ · mapGL q₂.out⁻¹) = mapGL(γ)`, γ∈Γ₁(N), q₁≠q₂⇒PSL≠1. |
| **D-U** Pairwise-q AEDisjoint T_p_upper(b) | same | BUILD: same engine, `α=glMap (T_p_upper p hp.pos b)`. |
| **I-∞-LHS/RHS** IntegrableOn M_∞ iUnion | DS p.182 "ϕ(α(τ))→0 as Im(τ)→∞ and ϕ∘α is bounded on D … the integral is well defined and convergent" | BUILD: EXIST per-tile `integrableOn_petersson_combinedGL_tile_on_fd` (DeltaBSystem:1122) + mathlib `integrableOn_finset_iUnion` over `Fintype.univ`; rewrite `peterssonAdj` slot → mixed-slash. |
| **I-U-LHS/RHS** IntegrableOn T_p_upper iUnion | same DS p.182 | BUILD: same. |
| **T-∞** TileFormIntegralResidual_M_infty | DS 5.5.2(a) p.185 (the per-tile change-of-variables) | EXIST: `_of_sigma_p_reduced`/`_of_per_q_tile_form` → `peterssonInner_M_infty_slash_adjoint_coset` (proven). |
| **T-U** TileFormIntegralResidual_upper(b) | DS 5.5.2(a) p.185 | EXIST per-q: `peterssonInner_slash_adj_T_p_upper_q_summand_eq` (proven). |

---

## 4. Skeleton file

`LeanModularForms/SMOObligations/PeterssonHeckeAdjoint.lean` — 8 `theorem … := by sorry`
(the four FD-tile obligations × two tile families), all in the composed-`*` shape matching
`TpHeckeFamilyMeasureHypotheses`. Verified: imports + statements type-check, **8 sorry warnings,
0 errors, 0 failed dependencies** (`lean_diagnostic_messages`).

Note: the residual ASSEMBLERS and the bundle `TpHeckeFamilyMeasureHypotheses` are `private` in
ConcreteFamily, so the final wiring (constructing the bundle from these 8 lemmas, bridging
`*`-shape ⇄ nested-`•`-shape via `mul_smul`, and feeding the assemblers) is an EXECUTION step
that happens INSIDE ConcreteFamily.lean — these 8 standalone public lemmas are `exact`-citable
from there.
