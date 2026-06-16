# Decomposition (v3, ADVERSARIAL — RED TEAM) — leaf 2 `petN_heckeT_p_RHS_aggregate_eq`

**Supersedes** `decomposition-adjoint-v2-PRE-leaf2.md`, whose **BOUNDED verdict is WRONG**.
This is the THIRD decompose; the prior two UNDER-SCOPED leaf 2. Disposition: find the flaw.

**Verdict up front: OPEN.** Leaf 2 is mathematically TRUE (DS 5.5.2(b) at α=diag(1,p)) but is
**logically equivalent, modulo only PROVEN trivial rewrites, to the entire symmetric-form goal**.
The "global aggregate" the v2 plan leaned on does NOT discharge any of DS 5.5.2(b)'s cross-term
content — it is only DS Def 5.1.3 (the LHS expansion). The genuine missing piece is DS 5.5.2(a)
instantiated over the conjugate-intersection group `Γ_p(α_j)` together with the
fundamental-domain image identification `β_j•(Γ_p(α_j)-FD) ≈ Γ₁-FD` — **not proven, and a
multi-week analytic build**, not a <150-LOC API gap.

---

## 0. The obligation (verbatim, ConcreteFamily.lean:5450)

```
private theorem petN_heckeT_p_RHS_aggregate_eq (p hp hpN) (f g) :
  slToPslQuot_fiberCard N • peterssonInner k
      (⋃ i ∈ univ, (match i | none => glMap M_∞ | some b => glMap (T_p_upper b)) • Γ₁_FD_PSL)
      f (g ∣[k] glMap T_p_lower)
  = petN (diamondOp_cusp k ⟨p⟩ f) (heckeT_p_cusp k p g)
```
(`Γ₁_FD_PSL = Gamma1_fundDomain_PSL N`, `c_N = slToPslQuot_fiberCard N`,
`⟨p⟩ = ZMod.unitOfCoprime p hpN`.)

The global assembler `petN_heckeT_p_symmetric_form_global` (5537) discharges the symmetric form
`petN(T_p f,g) = petN(⟨p⟩f,T_p g)` by `rw [leaf1, aggregate, leaf2]`. leaf1
(`petN_heckeT_p_LHS_eq_aggregate`, 5403) and leaf3 (`aggregate_HeckeFD_measure_hyps`, 5470) are
PROVEN (bodies complete, no sorry); the aggregate
`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD` (122) is PROVEN. Only leaf 2 is sorry.

---

## 1. THE SMOKING GUN — leaf 2 IS the goal (circularity proof)

`lean_goal` at line 5550 (inside `petN_heckeT_p_symmetric_form_global`, AFTER `obtain` +
`rw [leaf1, aggregate]`, BEFORE the leaf2 rewrite) returns a single residual goal that is
**`petN_heckeT_p_RHS_aggregate_eq`'s statement verbatim**, and `goals_after = []` once leaf2
fires. Therefore:

```
symmetric form  --(leaf1, PROVEN)-->  petN(T_p f,g) = c_N·⟨D₁⟩(Σf∣β_i) g
                --(aggregate, PROVEN)-->  petN(T_p f,g) = c_N·⟨⋃β_i•D₁⟩ f (g∣T_p_lower)
                                              \_________ this IS leaf2's LHS _________/
                ⟹  leaf2 ⟺ [c_N·⟨⋃β_i•D₁⟩ f (g∣T_p_lower) = petN(⟨p⟩f,T_p g)]
                       ⟺ [petN(T_p f,g) = petN(⟨p⟩f,T_p g)]   = THE GOAL
```
Since leaf1 + aggregate are **proven equalities**, the composite
`petN(T_p f,g) = c_N·⟨⋃β_i•D₁⟩ f (g∣T_p_lower)` is a theorem, so **leaf 2 is logically
equivalent to the symmetric-form goal itself.** The global route reduces the goal to … the goal.

### Why the aggregate carries NO cross-term content
The aggregate (122) is proven via
`peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable` (SummandAdjoint:1487) →
`peterssonInner_sum_slash_adjoint_constantRHS` (SummandAdjoint:864). Decisive hypothesis:
```
(hadj : ∀ i ∈ s, g ∣[k] peterssonAdj (α i) = g')   -- ONE common g' for ALL reps
```
discharged for the T_p family by `slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower` /
`..._T_p_upper_...` (SummandAdjoint:1925/1934): every Hecke rep β_i satisfies
`g∣peterssonAdj(β_i) = g∣T_p_lower`. So the aggregate is the *trivial* slot-swap
`⟨D₁⟩(Σf∣β_i)g = ⟨⋃β_i•D₁⟩ f (g∣T_p_lower)` — it rewrites the **LHS of the symmetric form into
itself** (DS's "the {β_j} serve in Def 5.1.3 of [ΓαΓ]_k" step). It never references
`petN(⟨p⟩f,·)` and never crosses to the RHS. **DS 5.5.2(b) ≠ this aggregate; DS 5.5.2(b) is the
cross identity, which lives entirely inside leaf 2.**

---

## 2. L_cov VERDICT — is DS 5.5.2(a) over Γ_p(α_j) proven?

**The change-of-variables `z↦α•z` IS proven, generally:** `peterssonInner_slash_adjoint`
(AdjointTheory.lean:770, sorry-free, docstring "DS Proposition 5.5.2a"):
```
peterssonInner k D (f∣[k]α) g = peterssonInner k (α•D) f (g∣[k] peterssonAdj α)   -- any D, det α>0
```
the genuine measure-preserving CoV on an ARBITRARY domain (rests on mathlib
`measurePreserving_smul (⟨α,hα⟩:GL(2,ℝ)⁺) μ_hyp`). **But this is NOT the full DS 5.5.2(a).**

**DS 5.5.2(a)'s actual content** is `⟨f[α]_k,g⟩_{α⁻¹Γα} = ⟨f,g[α′]_k⟩_Γ`: the integral over the
FD of the *smaller* group `α⁻¹Γα` equals the integral over the FD of `Γ`. The CoV lemma maps
`D↦α•D`; to land DS 5.5.2(a) you must additionally **identify `α•(FD of α⁻¹Γα)` with `FD of Γ`**
(DS Lemma 5.5.1(a)+(b): equal volume, conjugate index). In the repo `α⁻¹Γα∩Γ = Γ_p(α)`
(`FDTransport.lean:41`). **There is NO lemma `β_j • Gamma_p_α_fundDomain_PSL(α_j) = Γ₁_FD` (or its
measure-zero-symmetric-difference form), and NO per-rep CoV lemma swapping `f∣β_j` against
`g∣β_j′` over `Γ_p(α_j)`.** The `Γ_p(α)` apparatus that exists
(`isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R` 860;
`setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum` 916;
`peterssonInner_petersson_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum` 957;
`sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` 1169) is exclusively **DS Lemma 5.5.1(b)**
(index/volume): it sums `petersson k f g` (the SAME-domain kernel, Γ₁-invariant since Γ_p(α)≤Γ₁)
over `SL/Γ_p(α)` to get `fiberCard • petN f g`. None of it performs the `f∣α ↔ g∣α′` exchange.

> **L_cov VERDICT: DS 5.5.2(a) is NOT proven over Γ_p(α_j).** Only the domain-agnostic CoV
> `peterssonInner_slash_adjoint` (AdjointTheory:770) is proven. The FD-image identification +
> per-rep exchange over the conjugate-intersection group is the unbuilt core.

---

## 3. The irreducible content, located: `h_HeckeFD_swap`

The repo already factors the symmetric form (DeltaBSystem 1436/1525 + ConcreteFamily 1898):
```
petN_heckeT_p_diamond_shift_core_from_HeckeFD_swap (1898):
  symm  :=  h_LHS_aggregate.trans (h_HeckeFD_swap.trans h_RHS_aggregate.symm)   -- line 1966
```
where, over the SL-tiled representation `⋃_q β·q⁻¹•fd`:
- `h_LHS_aggregate` = `petN_heckeT_p_eq_per_alpha_HeckeFD_form` (DeltaBSystem:1436) — PROVEN.
- `h_RHS_aggregate` = `petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form` (DeltaBSystem:1525) — PROVEN.
- `h_HeckeFD_swap`:
  `Σ_family ⟨⋃_q β q⁻¹•fd⟩ f (g∣T_p_lower) = Σ_family ⟨⋃_q β q⁻¹•fd⟩ (⟨p⟩f∣T_p_lower) g`.

`petN_heckeT_p_HeckeFD_swap_from_petN_symm` (2300) derives `h_HeckeFD_swap` FROM `h_sym`; line
1966 derives `h_sym` FROM `h_HeckeFD_swap`. **So `h_HeckeFD_swap ⟺ h_sym`** — the swap is
logically equivalent to the goal. It is exactly what the deleted-route residuals
`SigmaQPermResidual_M_infty/upper` (4698/4731) tried to prove per-`q` and which the prior
EXECUTION proved **false per-block** (learnings id `d6e58f26`): the `q`-reindex permutation
`Gamma1QuotEquivOfGamma0` rearranges terms *between* the M_∞ block and the upper block, so only
the whole-double-coset sum closes. This is DS 5.5.2(b)'s "over the full ΓαΓ" subtlety made
concrete.

leaf 2 (PSL `⋃β_i•D₁` form) and `h_HeckeFD_swap` (SL `⋃_q βq⁻¹fd` form) are the **same content
in two representations** (related by the `c_N`/PSL-vs-SL fiber bookkeeping). There is no proven
bridge between the two forms either (`grep`: no lemma equates `⋃_i β_i•D₁` with the per-family
`⋃_q β q⁻¹ fd`), so even re-routing leaf 2 to `h_HeckeFD_swap` would itself need a new lemma.

---

## 4. Constant arithmetic (does c_N close to the stated leaf-2 form?)

The `c_N` IS consistent — it is NOT the obstruction. Trace:
- leaf1: `petN(T_p f,g) = c_N • ⟨D₁⟩(Σf∣β_i) g` via `petN_eq_setIntegral_Gamma1_fundDomain_PSL`
  (`petN` = `Σ_{SL/Γ₁} ∫_{q⁻¹fd}` ; `setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum`
  (FDTransport:381) gives `Σ_{SL/Γ₁} ∫_{q⁻¹fd} h = c_N • ∫_{D₁} h` for **Γ₁-invariant h**).
- aggregate: PSL-level, fiber-count-free, rewrites under the `c_N •`.
- leaf2 therefore correctly carries the SAME `c_N •` on its LHS. So leaf-2's stated form (with
  `slToPslQuot_fiberCard N •`) is the CORRECT statement — **no c_N correction needed.**

The arithmetic that would FAIL is the prior v2 plan's *route*: it wanted to apply
`peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (291) to expand `β_i•Γ_p(α_i)-FD` into
`Γ₁/Γ_p(α_i)` tiles, then collapse via `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN`
(1169) which is over `SL/Γ_p(α_i)`. These index sets differ by `c_N`
(`slToPslQuot_fiberCard_Gamma_p_α` vs `slToPslQuot_fiberCard`), and — fatally — the aggregate
supplies only the single tile `β_i•D₁`, not `β_i•Γ_p(α_i)-FD = [Γ₁:Γ_p(α_i)]` copies of it. So
lemma 291 is **not even applicable** to leaf 2's LHS. The v2 "relIndex cancels by Lemma 5.5.1(b)"
claim is vacuous: lemma 291's hypotheses are never met, and even if patched, the residual is
`h_HeckeFD_swap` = the goal. (This matches the corrected leaf-2 docstring at 5438–5449 written by
the most recent pass — that docstring is correct; the v2 *plan/decomposition/tickets* that still
say BOUNDED are the stale ones superseded here.)

---

## 5. Per-leaf table

| Leaf | Classification | Discharge cite | Attack outcome |
|---|---|---|---|
| **L_reps** (ΓαΓ=⊔β_jΓ common reps {M_∞}⊔{T_p_upper b}) | DISCHARGED-project | `heckeT_p_fun_eq_coset_sum`; in leaf1 body 5412–5428 (PROVEN) | OK — `Fintype.sum_option` splits the `Option (Fin p)` family; no gap. |
| **L_cov** (DS 5.5.2(a) over Γ_p(α_j)) | **API-GAP → OPEN** | only `peterssonInner_slash_adjoint` (AdjT:770, CoV over any D); **no FD-image id, no per-rep exchange over Γ_p(α)** | Counterexample to "done": per-block residuals 4698/4731 are FALSE (id d6e58f26). Hyp-strength: 770 needs only det>0 — true — but yields `α•D`, not "FD of α⁻¹Γα ↦ FD of Γ". Discharge-attack: grep finds zero `β•Γ_p(α)-FD = Γ₁-FD`. |
| **L_index** (n=[Γ₁:Γ_p], c_N) | lemmas EXIST but NOT wireable to leaf2 | `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDT:1169); `slGamma_p_αToGamma1_fiberCard`; `slToPslQuot_fiberCard` | 1169 is over `SL/Γ_p(α)` summing the SAME-domain kernel — Lemma 5.5.1(b), unrelated to the `f∣α↔g∣α′` exchange. Cannot fire on leaf2's single-tile LHS. |
| **L_reassemble** (Σ g∣β'_j = g∣T_p adjoint·diamond) | DISCHARGED-project (as RHS *expansion* only) | `slash_diamond_inv_T_p_upper_eq_T_p_lower_delta` (DeltaBSystem:1739); `petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form` (1525, PROVEN) | OK as RHS expansion; its equality to the LHS-expansion is exactly `h_HeckeFD_swap`. Reassembly does not supply the swap. |
| **leaf 2 (whole)** | **OPEN** (⟺ symm-form goal) | — | §1 smoking gun: post-(leaf1,aggregate) goal == leaf2 verbatim, goals_after=[]. |

---

## 6. What "OPEN" concretely requires (the multi-week piece)

To prove `h_HeckeFD_swap` (= leaf 2 = the goal) one must build **DS 5.5.2(a) over Γ_p(α_j)**:
1. `β_j • (Gamma_p_α_fundDomain_PSL α_j)` is (a.e.) a fundamental domain for the *adjoint*
   conjugate group `β_j Γ₁ β_j⁻¹ ∩ Γ₁` — an FD-image identification under the det-`p` matrix β_j.
   **New analytic lemma; nontrivial because det β_j = p ⇒ β_j is not a Γ₁-FD symmetry in PSL(2,ℝ).**
2. The per-rep exchange `⟨Γ_p(α_j)-FD⟩ (f∣β_j) g = ⟨β_j•Γ_p(α_j)-FD⟩ f (g∣β_j′)` with det-weighted
   cocycle bookkeeping (`peterssonInner_slash_adjoint` gives the CoV step, but **both domains must
   be the conjugate-group FDs**, requiring (1)).
3. Summation over `j` with `[Γ₁:Γ_p(α_j)]` indices reconciled against `c_N` and the cross-block
   `Gamma1QuotEquivOfGamma0` reindex (the part false per-block, closing only globally).

This is the full Diamond–Shurman §5.5 / Miyake §2.8 upper-half-plane double-coset
change-of-variables machinery over conjugate-intersection fundamental domains — estimated
**multi-week** (several hundred LOC of genuinely new measure-theoretic + FD-combinatorial
development), NOT a bounded <150-LOC wiring gap. The proven `peterssonInner_slash_adjoint`,
`Γ_p(α)` FD/index lemmas, and per-alpha forms are *necessary substrate* but are exactly the
pieces DS uses BEFORE 5.5.2(a)'s FD-image step; the binding step is unbuilt.

---

## 7. Adversarial attack log (each honestly attempted)

- **Counterexample to v2 "aggregate = DS 5.5.2(b)":** read the aggregate's proof to `constantRHS`
  (864); its `hadj` shows it is the same-adjoint slot-swap = DS Def 5.1.3, not the cross identity.
  FOUND the flaw.
- **Edge-case (c_N):** could the stated `c_N •` be wrong, making leaf2 false? Traced
  `setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum` (381): `c_N` is consistent on leaf1 and
  leaf2; statement correct. Not the obstruction.
- **Hypothesis-strength (lemma 291/1169):** lemma 291 needs `β_i•Γ_p(α_i)-FD` (multi-tile); leaf2
  supplies single `β_i•D₁`. Hypotheses unsatisfiable on leaf2 ⇒ v2's relIndex cancellation vacuous.
- **Source-drift:** DS 5.5.2(b)'s "each Γ∩β_jΓβ_j⁻¹ in place of Γ" (verbatim) confirms the base
  group is the conjugate-intersection group, NOT Γ — matching the `Γ_p(α)` requirement, unbuilt
  for the exchange.
- **Discharge-attack (find any swap lemma):** grep for `β•Γ_p(α)-FD = Γ₁-FD`, for a swap over
  `Γ_p(α)`, and for a bridge `⋃β_i•D₁ ↔ Σ_family ⋃β q⁻¹ fd` — **all empty.** The only swap-shaped
  lemmas (2300, 1966) are the two directions of `h_HeckeFD_swap ⟺ h_sym` (circular).
- **Circularity confirmation:** `lean_goal` @5550 == leaf2 verbatim, `goals_after=[]`. BINDING.

---

## 8. Skeleton status

No skeleton edits made (RED-TEAM/planning-only; the existing corrected leaf-2 docstring at
5432–5449 already states the API gap correctly, and the leaf-2 `sorry` is the right placeholder).
ConcreteFamily.lean sorry count: **3** (5198, 5201 false-split; 5461 leaf 2). No banned tokens
(`native_decide`/`set_option maxHeartbeats`/custom `axiom`: grep-clean). Protected statements
`heckeT_p_adjoint` (5368), `exists_simultaneous_eigenform_basis` (AdjointTheoryPetersson:880),
`petN_heckeT_p_symmetric_form` (5185) signatures untouched; `strongMultiplicityOne_axiom_clean`
(SMOObligations:397) and `miyake_4_6_14_delta_slash_sum_coeff_zero` (Lemma4_6_14:303) untouched.
