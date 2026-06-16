# Decomposition (v2, CORRECTED) — T_p Petersson self-adjointness via the GLOBAL double coset

**Supersedes** `decomposition-adjoint-v1-PRE-correction.md`, which planned an 8-leaf
"FD-tile measure" pass assuming a PER-TILE adjoint identity. EXECUTION proved that route
mathematically WRONG (learnings.jsonl id `d6e58f26`). This v2 mirrors DS's / Miyake's
GLOBAL double-coset proof.

**Target.** `petN_heckeT_p_symmetric_form` (`ConcreteFamily.lean:5185`) currently discharges
via a split into two residuals with `sorry` at **5198** (`SigmaQPermResidual_M_infty`) and
**5201** (`SigmaQPermResidual_upper`). Those two residuals are individually FALSE; only their
sum holds. We close the theorem by an alternative GLOBAL route
(`petN_heckeT_p_symmetric_form_global`) that never performs the split. Closing it makes
`AdjointTheoryPetersson.exists_simultaneous_eigenform_basis` axiom-clean (the rest of the
adjoint/spectral chain is sorry-free).

---

## 0. The GLOBAL proof, read from the PDFs (page pointers + verbatim)

### Diamond–Shurman, *A First Course in Modular Forms*, §5.4–5.5

**Petersson inner product (Def 5.4.1, book p.182, PDF idx 194).**
> "⟨f,g⟩_Γ = (1/V_Γ) ∫_{X(Γ)} f(τ) g̅(τ) (Im(τ))^k dµ(τ)."

**FD-tile decomposition (book p.181, PDF idx 193).**
> "Let {α_j} ⊂ SL₂(ℤ) represent {±I}Γ\SL₂(ℤ) … Since dµ is SL₂(ℤ)-invariant the sum is
> ∫_{⋃ α_j(D*)} ϕ … = ∑_j ∫_{D*} ϕ(α_j(τ)) dµ(τ)."

**Lemma 5.5.1 (book p.184, PDF idx 196) — the GLOBAL technical core.** Verbatim:
> "(a) If ϕ … is continuous, bounded, and Γ-invariant, then
>     ∫_{α⁻¹Γα\H*} ϕ(α(τ)) dµ(τ) = ∫_{X(Γ)} ϕ(τ) dµ(τ).
> (b) If α⁻¹Γα ⊂ SL₂(ℤ) then V_{α⁻¹Γα} = V_Γ and [SL₂(ℤ):α⁻¹Γα] = [SL₂(ℤ):Γ].
> (c) There exist β₁,…,β_n ∈ GL₂⁺(ℚ), where n = [Γ:α⁻¹Γα∩Γ] = [Γ:αΓα⁻¹∩Γ], such that
>     ΓαΓ = ⋃ Γβ_j = ⋃ β_jΓ, with both unions disjoint."

**Prop 5.5.2(a) — the per-rep change-of-variables (book p.185, PDF idx 197).** Verbatim:
> "expand the [α]_k operator, note that α′ acts as α⁻¹ on H*, and apply Lemma 5.5.1(a):
> ∫_{α⁻¹Γα\H*} (f[α]_k)(τ) g̅(τ)(Imτ)^k dµ = ∫_{X(Γ)} (detα)^{k-1} f(α(τ)) j(α,τ)⁻ᵏ g̅(τ)(Imτ)^k dµ
> = ∫_{X(Γ)} (detα)^{k-1} f(τ) j(α,α′(τ))⁻ᵏ g̅(α′(τ)) (Im α′(τ))^k dµ. The cocycle condition
> j(αα′,τ)=j(α,α′(τ))j(α′,τ), the upper-half-plane identity Im(α′(τ))=(detα′)Im(τ)|j(α′,τ)|⁻²,
> and det α′ = det α reduce the integral to ∫_{X(Γ)} f(τ)(g[α′]_k)(τ)(Imτ)^k dµ. Since also
> V_{α⁻¹Γα}=V_Γ by Lemma 5.5.1(b), the result follows."

**Prop 5.5.2(b) — the GLOBAL sum over double-coset orbit reps (book p.185–186, PDF idx 197–198).**
THE KEY PASSAGE — note the base group is `β_j⁻¹Γβ_j ∩ Γ` (NOT Γ), and the sum is over the
WHOLE orbit-rep set. Verbatim:
> "the relation ΓαΓ = ⋃ Γβ_j … shows that the {β_j} can serve in Definition 5.1.3 of [ΓαΓ]_k.
> And ΓαΓ = ⋃ β_jΓ gives Γα′Γ = ⋃ Γβ′_j where β′_j = det(β)β⁻¹ … Now the result is immediate
> from (a) with each Γ ∩ β_jΓβ_j⁻¹ in place of Γ,
>   ⟨f[ΓαΓ]_k,g⟩_Γ = ∑_j ⟨f[β_j]_k,g⟩_{β_j⁻¹Γβ_j∩Γ}
>                  = ∑_j ⟨f,g[β′_j]_k⟩_{Γ∩β_jΓβ_j⁻¹} = ⟨f,g[Γα′Γ]_k⟩_Γ."

**Thm 5.5.3 (book p.186, PDF idx 198).**
> "T_p* = [Γ₁(N) [[1,0],[0,p]] Γ₁(N)]*_k = [Γ₁(N) [[p,0],[0,1]] Γ₁(N)]_k … Since m ≡ p⁻¹ (mod N),
> the result T_p* = ⟨p⟩⁻¹ T_p follows."

### Miyake §2.8 (cross-check)
**Thm 2.8.2 (book p.76, PDF idx 84).**
> "(1) Assume α⁻¹Γ₁α ⊂ Γ₂. Then (f|_k α, g) = (f, g|_k α′). (2) For α∈Γ, (f|_k ΓαΓ, g) = (f, g|_k Γα′Γ)."

Miyake (2) sums over a **common rep set** `ΓαΓ = ⊔ Γα_v = ⊔ α_vΓ` (Thm 4.5.3(2)) — identical
structure to DS 5.5.2(b). **Both proofs are GLOBAL: a single sum over the full double coset,
with each term's change-of-variables taken over the conjugate-intersection base group.**

### THE CORRECTION (why the per-tile route is wrong)
DS 5.5.2(b) does NOT assert `⟨f[β_j]_k,g⟩_Γ = ⟨f,g[β′_j]_k⟩_Γ` per `j`. It asserts the per-`j`
identity over the **smaller** group `β_j⁻¹Γβ_j ∩ Γ` (a fundamental domain that is `[Γ:β_j⁻¹Γβ_j∩Γ]`
copies of `D*`), and the equality of the **summed** quantities. Splitting the family sum into
the `M_∞` term and the `T_p_upper b` terms and demanding each be self-adjoint over `Γ`'s own FD
is FALSE — `det M_∞ = p`, so `M_∞•(Γ-tile)` is not a `Γ`-tile. This is exactly the prior
EXECUTION failure.

---

## 1. Lean ↔ source match (the GLOBAL realisation already PRESENT in the repo)

`Σ_i f∣β_i` (sum over the Hecke family `Option (Fin p) = {M_∞} ⊔ {T_p_upper b}`) **is** the
double-coset operator `f[ΓαΓ]_k = T_p f` (DS Def 5.1.3 / Lemma 5.5.1(c): the `β_j` serve as the
reps). The repo's proven-but-UNUSED lemma

`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` (`ConcreteFamily.lean:122`) and its
PSL twin `_PSL_R` (`:202`) state exactly DS 5.5.2(b)'s aggregate identity:

  `⟨D₁⟩ (Σ_i f∣β_i) g = ⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower)`,  `D₁ = Gamma1_fundDomain_PSL N`.

The base-group change-of-variables of DS 5.5.2(a) over `Γ∩β_jΓβ_j⁻¹` is the repo's
`Γ_p(α) := conjGL Γ₁(N) α ⊓ Γ₁(N)` (`FDTransport.lean:41`) machinery: the proven
`peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (`ConcreteFamily.lean:291`) realises
`⟨β_i•Γ_p(α)-FD⟩ = Σ_{Γ_p(α)-cosets} ⟨β_i·q⁻¹•Γ₁-FD⟩`, and
`sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (`FDTransport.lean:1169`) is DS Lemma
5.5.1(b)'s index/volume relation `Σ_{SL⧸Γ_p(α)} ⟨fd⟩(F∣q⁻¹)(G∣q⁻¹) = relIndex • petN F G`.
The `α′ = det(α)α⁻¹` is `peterssonAdj` (`AdjointTheory.lean:598`); the single-domain
change-of-variables DS 5.5.2(a) is the proven `peterssonInner_slash_adjoint`
(`AdjointTheory.lean:770`), resting on mathlib `measurePreserving_smul (⟨α,hα⟩:GL(2,ℝ)⁺) μ_hyp`
(= DS Exercise 5.4.1(a)).

**Conclusion: the entire GLOBAL apparatus is present and proven; only the assembly that routes
`petN(T_p f,g)` through the aggregate (NOT through the M_∞/upper split) is missing.**

---

## 2. Corrected leaf tree

```
petN_heckeT_p_symmetric_form_global  [NEW top assembler, ConcreteFamily ~5455]   BOUNDED
├── leaf 1  petN_heckeT_p_LHS_eq_aggregate            [NEW, ConcreteFamily ~5397]  BUILD
│     petN(T_p f, g) = ⟨D₁⟩ (Σ_i f∣β_i) g
│     ├── heckeT_p_fun_eq_coset_sum (T_p as family sum)            [EXIST, HeckeT_n / DeltaBSystem:1646]
│     ├── peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum   [EXIST, FDTransport:410]
│     └── petN = Σ_q ⟨fd⟩(·∣q⁻¹)(·∣q⁻¹)  (def of petN)            [EXIST, PeterssonLevelN]
├── (proven aggregate)  peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R  [EXIST, :202]
│     ⟨D₁⟩ (Σ_i f∣β_i) g = ⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower)            [PROVEN, sorry-free]
│     └── needs leaf 3 (its 3 measure hyps)
├── leaf 3  aggregate_HeckeFD_measure_hyps           [NEW, ConcreteFamily ~5437]  BUILD
│     (∀i NullMeas β_i•D₁) ∧ (∀i IntegrableOn swapped on D₁) ∧ (IntegrableOn fwd on ⋃_i β_i•D₁)
│     ├── per-tile integrability  integrableOn_petersson_combinedGL_tile_on_fd  [EXIST, DeltaBSystem:1122]
│     │     + the per-q distribute patterns                        [EXIST, DeltaBSystem:1666–1736]
│     ├── NullMeas of β_i•(PSL FD)                                  [EXIST engines, FDTransport / SummandAdjoint]
│     └── iUnion integrability via integrableOn_finset_iUnion       [mathlib]
└── leaf 2  petN_heckeT_p_RHS_aggregate_eq           [NEW, ConcreteFamily ~5417]  BUILD  ⚠ RISKIEST
      ⟨⋃_i β_i•D₁⟩ f (g∣T_p_lower) = petN(⟨p⟩f, T_p g)
      ├── split family iUnion per-i  peterssonInner_iUnion_finite_aedisjoint   [EXIST, PeterssonLevelN:1140]
      ├── per-i tile collapse  peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q   [EXIST, ConcreteFamily:291]
      │     (β_i•Γ_p(α)-FD ⇒ Σ over Γ_p(α)-cosets of β_i·q⁻¹•Γ₁-FD tiles)
      ├── Γ_p(α)-coset sum ⇒ relIndex•petN
      │     sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN     [EXIST, FDTransport:1169]
      ├── relIndex cancellation: same relIndex on LHS & RHS family terms (DS Lemma 5.5.1(b))
      └── recombine via the diamond / T_p_lower↔T_p_upper slash identities
            slash_diamond_inv_T_p_upper_eq_T_p_lower_delta          [EXIST, DeltaBSystem:1739]
            slash_T_p_upper_eq_diamond_slash_T_p_lower_factor       [EXIST, used in TileBridge:3647]
```

### Underlying analytic substrate — all PROVEN, verified sorry-free
- `peterssonInner_slash_adjoint` (AdjointTheory:770) = DS 5.5.2(a) / Miyake 2.8.2(1).
- `peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD(_PSL_R)` (ConcreteFamily:122/202) =
  DS 5.5.2(b) aggregate (the GLOBAL identity). **Currently UNUSED — this is the key asset.**
- `Gamma_p_α` engine: `Gamma_p_α` (FDTransport:41), `isFundamentalDomain_Gamma_p_α_*`
  (176/220/492/860), `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (ConcreteFamily:291),
  `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDTransport:1169),
  `sum_SL_tile_Gamma_p_α_eq_fiberCard_mul_SL_tile_Gamma1` (FDTransport:1104).
- `peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum` (FDTransport:410).
- `peterssonInner_iUnion_finite_aedisjoint` (PeterssonLevelN:1140).
- Family slash identities (DeltaBSystem:1739 ff.; TileBridge:3593/3647).

---

## 3. Per-leaf verbatim-source + Lean-citation map

| Leaf | Source (verbatim §) | Lean route (EXIST vs BUILD) |
|---|---|---|
| **1** LHS=aggregate | DS Def 5.1.3 + 5.5.1(c): "{β_j} serve in Definition 5.1.3 of [ΓαΓ]_k" → `Σ_i f∣β_i = T_p f` | BUILD: `heckeT_p_fun_eq_coset_sum` (EXIST) + `peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum` (EXIST, FDTransport:410). |
| **2** aggregate=RHS | DS 5.5.2(b): "∑_j ⟨f,g[β′_j]_k⟩_{Γ∩β_jΓβ_j⁻¹} = ⟨f,g[Γα′Γ]_k⟩" + Thm 5.5.3 "= ⟨p⟩⁻¹T_p" | BUILD ⚠: per-i split (EXIST PeterssonLevelN:1140) + `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (EXIST :291) + `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (EXIST FDTransport:1169) + slash identities (EXIST DeltaBSystem:1739). |
| **3** measure hyps | DS p.182 "ϕ(α(τ))→0 as Im→∞ … integral well defined and convergent" (one of f,g a cusp form) + p.181 "ℚ∪{∞} measure zero, dµ suffices" | BUILD: per-tile `integrableOn_petersson_combinedGL_tile_on_fd` (EXIST DeltaBSystem:1122) + distribute patterns (EXIST :1666–1736) + NullMeas/iUnion-integrable engines (EXIST) + mathlib `integrableOn_finset_iUnion`. |
| **top** wiring | DS 5.5.2(b) statement | BUILD: `obtain` leaf 3, `rw` leaf 1 → aggregate → leaf 2. Needs `simp only [Finset.sum_option, Set.iUnion_option]` to expand the `match` before `rw` (default-budget `whnf` issue, NOT a gap; verified the term-mode form type-checks). |

---

## 4. Skeleton (in `ConcreteFamily.lean`, before `end HeckeRing.GL2`)

Four `:= by sorry` declarations were added and verified by `lean_diagnostic_messages`
(lines 5376–5475): **4 sorry warnings, 0 errors, 0 failed dependencies.**

- `petN_heckeT_p_LHS_eq_aggregate`     (leaf 1)  ~5397
- `petN_heckeT_p_RHS_aggregate_eq`     (leaf 2)  ~5417
- `aggregate_HeckeFD_measure_hyps`     (leaf 3)  ~5437
- `petN_heckeT_p_symmetric_form_global`(top)     ~5455

The 2 PRE-EXISTING sorries at 5198/5201 remain untouched (they belong to the now-superseded
split route). At EXECUTION the consumer `heckeT_p_adjoint` is repointed from
`petN_heckeT_p_symmetric_form` to `petN_heckeT_p_symmetric_form_global` (via
`petN_heckeT_p_adjoint_of_diamond_shift`, which calls `petN_heckeT_p_diamond_shift`); the old
split lemmas + their 2 sorries are then deleted. The bridge lives upstream in ConcreteFamily
(the discharge is here), satisfying the "no downstream file" constraint.

---

## 5. Feasibility verdict — BOUNDED

Every leaf has a cited PROVEN engine. The hard analytic core (the GL₂⁺ change-of-variables, the
`Γ_p(α)` fundamental-domain tiling, the index/volume relation, AND the full GLOBAL aggregate
identity DS 5.5.2(b)) is already proven. The remaining work is assembly:
- **leaf 1, 3**: bookkeeping over engines already exercised at DeltaBSystem:1666–1736.
- **leaf 2 (riskiest)**: threading the per-i `Γ_p(α)` collapse + the relIndex cancellation +
  recombining via the family slash identities. The relIndex must cancel between LHS and RHS
  family terms — guaranteed by DS Lemma 5.5.1(b) (`[SL:Γ_p(α)]` depends only on the double
  coset, identical for `α` and `α′`). No open-ended piece.

The only NON-mathematical risk is `match`-expansion / heartbeat hygiene in the wiring (handled
by `simp only [Finset.sum_option, Set.iUnion_option]` before the rewrites; no
`set_option maxHeartbeats`).
