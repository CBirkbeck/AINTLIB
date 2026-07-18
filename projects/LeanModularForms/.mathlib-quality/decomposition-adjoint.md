# Decomposition (v4, ADVERSARIAL — RED TEAM, re-armed against the OPEN verdict)

**Supersedes** `decomposition-adjoint-v3.md`, whose **OPEN verdict is now STALE.**
v3 concluded "multi-week OPEN: the FD-image identification + per-rep exchange over the
conjugate-intersection group `Γ_p(α)` + the `c_p`-vs-`c_N` reconciliation are *unbuilt*."
**Those three pieces are now BUILT, axiom-clean, in `FDTransport.lean` (0 sorries):**
`smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (879, the FD-image id),
`peterssonInner_slash_adjoint_over_Gamma_p_α` (1235, per-rep exchange over `Γ_p(α)`),
`setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain` (1612,
the `c_p•∫_{Γ_p-FD} = c_N•∫_{Γ₁-FD}(trace)` reconciliation — DS Ex 5.4.4).

> **VERDICT (binding): BOUNDED.** The consolidated lemma decomposes into a finite,
> dischargeable leaf chain via the **trace route** (DS Ex 5.4.4 + DS 5.5.2(a) per-rep,
> assembled exactly as Miyake 2.8.2(2)). The genuinely-open core v3 named no longer
> exists. The residue is **one API-GAP leaf** (`heckeT_p_g_traceSlash_family_identity`,
> the DS family-trace bookkeeping `tr(g|adjustment) = the T_p g family-sum`) plus routine
> wiring, all sketched below with `:= by sorry` skeletons (type-check-deferred). Estimated
> ~250–400 LOC of *finite combinatorial + linearity* glue, NOT multi-week analysis.

> **Decisive: the σ/trace route SUPERSEDES `h_tile_shift_to_prefactored`.** YES (see §6).
> The trace route never invokes the false per-tile / per-`q` `h_tile_shift_to_prefactored`;
> it routes through `Γ_p(α)`-FD integrals and the well-defined global trace, where the
> determinant mismatch (det β = p vs det = 1) is absorbed *measure-theoretically* by the
> proven `peterssonInner_slash_adjoint` CoV, not by a (false) per-tile change of variables.

---

## 0. The obligation (verbatim, ConcreteFamily.lean:5212, the ONLY real `sorry` @5218)

```
private theorem petN_heckeT_p_symmetric_form_doubleCoset
    (p hp hpN) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
  petN (heckeT_p_cusp k p hp hpN f) g =
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) (heckeT_p_cusp k p hp hpN g)
```
(`⟨p⟩ = diamondOp ZMod.unitOfCoprime p hpN`; DS 5.5.2(b)/5.5.3, Miyake 2.8.2(2)/4.5.4(2)
at `α = diag(1,p)` on Γ₁(N). `T*_p = ⟨p⟩⁻¹ T_p`.) Everything downstream
(`heckeT_p_adjoint` @5393, the spectral theorem) bottoms out here.

**On v3's "smoking gun" (leaf-2 ⟺ goal):** TRUE but IRRELEVANT to the verdict. v3 proved
the *global-aggregate framing* is circular (post-(leaf1,aggregate) residual == leaf 2
verbatim). Correct — but that only kills the *aggregate route*. The **trace route attacks
the consolidated lemma DIRECTLY** and never passes through the circular aggregate. The
aggregate (122) is a red herring for the verdict: it is DS Def 5.1.3 (LHS expansion), not
DS 5.5.2(b). We abandon it and prove `petN_heckeT_p_symmetric_form_doubleCoset` head-on.

---

## 1. MIYAKE 2.8.2(2) ↔ Lean correspondence (the spec, verbatim)

> **Miyake 2.8.2(1)** (per-rep, over `Γ'=α⁻¹Γ₁α∩Γ₂`): `(f|ₖα,g) = (f,g|ₖα')`, `α'=det(α)α⁻¹`.
> proof = `z↦α'z` CoV, `j(α,α⁻¹z)=det(α)j(α',z)⁻¹`, `Im(α⁻¹z)=det(α')|j(α',z)|⁻²Im(z)`,
> `v(Γ'\H)=v(αΓ'α⁻¹\H)`, normalized by `v(Γ'\H)⁻¹`.

**Lean match.** The CoV `z↦α•z` with the `det^{k-2}`/`|j|²` cocycle bookkeeping IS
`peterssonInner_slash_adjoint` (AdjointTheory.lean:770, docstring "DS Proposition 5.5.2a",
**proven**): `⟪D⟫(f∣α) g = ⟪α•D⟫ f (g∣ peterssonAdj α)` for any `D`, `det α>0`. The
`v(Γ'\H)=v(αΓ'α⁻¹\H)` FD-image (Γ' = `Γ_p(α)`) is
`smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDTransport:879, **proven**:
`α•(Γ_p(α)-FD)` is an FD for `Γ₁∩αΓ₁α⁻¹`). The repo's UN-normalized convention drops the
`v⁻¹`; the index/volume reconciliation reappears as `c_p`-vs-`c_N` in leaf T below.

> **Miyake 4.5.3(2)** (common reps): `Γ\ΓαΓ` and `ΓαΓ/Γ` share reps `{αᵥ}`, so
> `ΓαΓ=⊔Γαᵥ=⊔αᵥΓ`.

**Lean match — CORRECTION to the prompt.** `Gamma1QuotEquivOfGamma0` (PeterssonLevelN:823)
is **NOT** the Miyake-4.5.3(2) common-reps bijection. It is the diamond reindexing
`[δ] ↦ [δγ⁻¹]` of `SL/Γ₁(N)` by `γ ∈ Γ₀(N)`, used (PeterssonLevelN:932, in
`petN_slash_invariant`) to prove `petN(f∣γ,g∣γ)=petN(f,g)` (diamond Petersson-invariance).
Its proven property is exactly that diamond invariance — useful, but it is a *single-coset*
right-translation, not a left↔right double-coset rep matching. The Lean realization of
4.5.3(2) for THIS problem is instead the explicit Hecke decomposition
`heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307): `T_p f = f∣M_∞ + Σ_b f∣T_p_upper(b)`,
i.e. `ΓαΓ = ⊔_i Γβ_i` with explicit `β_i ∈ {M_∞}⊔{T_p_upper b}` (det `β_i = p`). The
left-vs-right reconciliation is then carried by the per-rep `Γ_p(α_i)`-FD apparatus
(`α_T_p_Q` ↔ `Gamma_p_α`, ConcreteFamily:255–326) + the trace (1612), not by a single σ.

> **Miyake 2.8.2(2)** (reassembly): `(f|ΓαΓ,g) = det(α)^{k-1} Σᵥ (f|ₖαᵥ,g)
>   = det(α)^{k-1} Σᵥ (f,g|ₖα'ᵥ) = (f,g|Γα'Γ)` — pull the operator-sum through the bilinear
>   inner product (linearity), per-rep 2.8.2(1) term-by-term over `Γ'ᵥ`, re-fold via `Γα'Γ=⊔Γα'ᵥ`.

**Lean match = THE ASSEMBLY (§4).** "Pull the sum through" = `petN` (conj-)linearity
(`petN_add_left/right`, `peterssonInner` linearity, ConcreteFamily uses `map_add`/`map_sum`
at DeltaBSystem:1613). "Per-rep 2.8.2(1)" = `peterssonInner_slash_adjoint_over_Gamma_p_α`
(1235) per `i`. "Re-fold via `Γα'Γ=⊔Γα'ᵥ`" = the trace transfer (1612) + the family-trace
bookkeeping leaf (`heckeT_p_g_traceSlash_family_identity`, the one API-GAP).

---

## 2. THE BANKED MACHINERY (each PROVEN; FDTransport.lean has 0 sorries, grep-clean of
banned tokens). v3 wrote its OPEN verdict as if 879/1235/1612 did not exist; they do.

| Lemma (file:line) | Statement (abridged) | Role (Miyake) | Proven? |
|---|---|---|---|
| `peterssonInner_slash_adjoint` (AdjT:770) | `⟪D⟫(f∣α)g = ⟪α•D⟫ f (g∣adj α)`, any D, detα>0 | per-rep CoV 2.8.2(1) | YES |
| `smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDT:879) | `α•(Γ_p(α)-FD)` is FD for `Γ₁∩αΓ₁α⁻¹` | `v(Γ'\H)=v(αΓ'α⁻¹\H)` | YES |
| `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235) | per-rep CoV specialized to `D=Γ_p(α)-FD` | 2.8.2(1) over Γ' | YES |
| `traceSlash_Gamma_p_α` (FDT:1332 def) | `tr_{q'} G = Σ_{fiber} G∣(q.out⁻¹·q'.out)` | DS trace `tr g=Σ g[αᵢ]` | def |
| `traceSlash_Gamma_p_α_indep` (FDT:1449) | `tr_{q'}` indep of `q'` (`G` Γ_p-inv) | `tr g` well-defined | YES |
| `traceSlash_Gamma_p_α_slash_Gamma1` (FDT:1522) | `tr G ∈ S_k(Γ₁)` (slash-inv) | `tr g ∈ S_k(Γ)` | YES |
| `setIntegral_..._eq_traceSlash_Gamma1_fundDomain` (FDT:1612) | `c_p•∫_{Γ_p-FD}pet F G = c_N•∫_{Γ₁-FD}pet F (tr G)` | DS Ex 5.4.4 (index reconcile) | YES |
| `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291) | `⟪α_i•Γ_p(α_i)-FD⟫ = Σ_q ⟪tiles⟫` | β_i•Γ_p-FD decomposition | YES |
| `slash_peterssonAdj_glMap_{M_infty,T_p_upper}_eq_slash_T_p_lower` (SA:1925/1934) | `g∣adj β_i = g∣T_p_lower` | common adjoint target | YES |
| `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (PLN:1069) | `petN f g = c_N•∫_{Γ₁-FD} pet f g` | petN↔FD integral | YES |
| `petN_slash_invariant` (PLN:923) | `petN(f∣γ,g∣γ)=petN f g`, γ∈Γ₀ | diamond Petersson-inv | YES |

---

## 3. The trace `tr G` is *literally* the DS adjoint family — the crux that closes it

For `α = α_i` (det `p`) and `G = ⇑g`, unfolding `traceSlash_Gamma_p_α α_i g q'` (def 1332):
`tr_{q'} g = Σ_{q ∈ fiber(q')} g∣(q.out⁻¹·q'.out)`, the fiber `q` ranging over the
`Γ₁/Γ_p(α_i)` cosets above `q'`. By `traceSlash_Gamma_p_α_indep` (1449), with `q'=q₀` the
base coset this is a single well-defined Γ₁-form (1522). DS 5.4.4 is *precisely*
`tr g = Σ_v g[α_{i,v}]_k`: the `Γ₁/Γ_p(α_i)`-coset sum. **Summed over `i`, the union of all
these cosets is exactly the right double-coset `Γ₁α'Γ₁ = ⊔_i Γ₁ α'_{i,v}` whose form-sum is
`T_p g` (up to `⟨p⟩` and det-weight).** This is the content of the ONE API-GAP leaf
(`heckeT_p_g_traceSlash_family_identity`): a *finite group-theoretic* identification of
`⊔_i {Γ₁/Γ_p(α_i)-cosets}` with the `T_p g` representative family — NO analysis, only coset
combinatorics + the proven `peterssonAdj β_i = T_p_lower`-shape facts (SA:1925/1934).

---

## 4. THE EXACT ASSEMBLY (head-on, NOT via the circular aggregate)

Target `petN(T_p f, g) = petN(⟨p⟩f, T_p g)`. Strategy: reduce BOTH sides to the same
`Σ_i c_N • ∫_{Γ₁-FD} pet f (tr_i (g∣adj β_i))` shape.

```text
LHS  petN(T_p f, g)
 (A) = petN((Σ_i f∣β_i), g)                         -- heckeT_p_fun_eq_coset_sum (PROVEN)
 (B) = Σ_i petN(f∣β_i, g)                            -- petN linearity slot-1 (PROVEN API)
 (C) per i:  petN(f∣β_i, g)
        = c_N • ∫_{Γ₁-FD} pet (f∣β_i) g              -- petN_eq_setIntegral (PROVEN)
        = c_p,i • ∫_{Γ_p(α_i)-FD} pet (f∣β_i) g      -- LEAF C1 (index transfer, see §5)
        = c_p,i • ∫_{α_i•Γ_p(α_i)-FD} pet f (g∣adj β_i)   -- 1235 (PROVEN per-rep CoV)
        = c_p,i • ∫_{Γ_p(α_i')-FD} pet f (g∣adj β_i)      -- LEAF C2 (α_i•Γ_p(α_i)-FD ≈ Γ_p(α_i')-FD; from 879)
        = c_N • ∫_{Γ₁-FD} pet f (tr_i (g∣adj β_i))   -- 1612 (PROVEN trace transfer)
 (D) sum over i, then re-fold:
        Σ_i c_N • ∫_{Γ₁-FD} pet f (tr_i (g∣adj β_i))
        = c_N • ∫_{Γ₁-FD} pet f (Σ_i tr_i (g∣adj β_i))   -- petN/∫ linearity (PROVEN)
        = c_N • ∫_{Γ₁-FD} pet f (⟨p⟩-twist of T_p g)     -- LEAF D (family-trace bookkeeping; §3)
        = petN(⟨p⟩f, T_p g)                              -- petN_eq_setIntegral back + petN_slash_invariant ⟨p⟩
```
Each `=` is either a PROVEN lemma (cited) or one of the **three named leaves** C1, C2, D.

---

## 5. THE THREE LEAVES (skeletons; type-check-deferred — NOT inserted into build)

### LEAF C2 — `α_i•Γ_p(α_i)-FD` is (a.e.) `Γ_p(α_i')-FD` for the adjoint `α_i' = det·α_i⁻¹`
This is the per-rep half of DS 5.5.2(a) and is **essentially already 879** (which gives the
FD-image for the conjugate group `Γ₁∩α_iΓ₁α_i⁻¹`). C2 only needs that 1612's hypothesis
"`G` is `Γ_p(α_i')`-slash-invariant" is met by `G = g∣adj β_i`. Since `adj β_i` differs from
`α_i'` by a Γ₁ factor, and `g` is Γ₁-invariant, this is a slash-invariance check.
```lean
private theorem g_slash_adj_beta_Gamma_p_alpha_inv_slash_invariant
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (i : Option (Fin p))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ γ ∈ Gamma_p_α (N := N) (α_T_p_Q p hp hpN i),
      (⇑g ∣[k] peterssonAdj (α_T_p_GLPos p hp hpN i : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2,ℤ)) =
        ⇑g ∣[k] peterssonAdj (α_T_p_GLPos p hp hpN i : GL (Fin 2) ℝ) := by
  sorry  -- type-check-deferred: conj of Γ_p(α_i)-element by adj β_i lands in Γ₁; g absorbs.
```
**Classification: API-GAP, BOUNDED (~40 LOC).** Discharge: `Gamma_p_α_conj_mem_Gamma1`
(FDT:68) gives the conjugate δ∈Γ₁; `SlashInvariantFormClass.slash_action_eq g`. 3 attacks:
(i) direct conj computation; (ii) reuse the `Γ_p(α)`-invariance pattern at SA:1917–1922;
(iii) reduce to `peterssonAdj β_i = β_i'·(Γ₁ factor)` then `g∣Γ₁ = g`.

### LEAF C1 — per-rep index transfer `c_N • ∫_{Γ₁-FD} pet(f∣β_i) g = c_p,i • ∫_{Γ_p(α_i)-FD} pet(f∣β_i) g`
Both are honest integrals of the SAME `Γ₁`-invariant integrand `pet(f∣β_i) g`
(`f∣β_i` is NOT Γ₁-inv, but `pet(f∣β_i) g` need not be — CAUTION, see attack (iii)).
Resolved by the **substrate Lemma 5.5.1(b)** already in the repo:
`sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDT:1169) + the fiber-count identity
`slToPslQuot_fiberCard_Gamma_p_α`. Actually cleanest: 1612 *itself* with `F=f`, `G=g`
already bundles C1+trace; C1 is only needed to first move `f∣β_i` off slot-1 — which the CoV
(C, step 1235) does, AFTER which the integrand `pet f (g∣adj β_i)` has `g∣adj β_i` that is
`Γ_p(α_i')`-invariant (LEAF C2) and `f` Γ₁-invariant, so **1612 applies verbatim.** Thus C1
collapses: apply 1235 FIRST (on the `c_N•∫_{Γ₁-FD}` form is wrong — 1235 needs the domain to
be `Γ_p(α_i)-FD`). Correct order:
```lean
private theorem petN_slash_beta_eq_cp_setIntegral_Gamma_p_alpha
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (i : Option (Fin p))
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k (Gamma_p_α_fundDomain_PSL (N := N) (α_T_p_Q p hp hpN i))
        (⇑f ∣[k] (α_T_p_GLPos p hp hpN i : GL (Fin 2) ℝ)) ⇑g =
      peterssonInner k (Gamma_p_α_fundDomain_PSL (N := N) (α_T_p_Q p hp hpN i))
        (⇑f ∣[k] (α_T_p_GLPos p hp hpN i : GL (Fin 2) ℝ)) ⇑g := by
  rfl  -- placeholder; C1's real content is the c_p,i•∫_{Γ_p-FD} ↔ c_N•∫_{Γ₁-FD} via 1612 on slot-2 after CoV.
```
**Classification: BOUNDED, mostly DISCHARGED-project.** The hard direction (index
reconciliation) IS 1612. C1 is the routing that turns leaf-1's `c_N•∫_{Γ₁-FD} pet(f∣β_i) g`
into the `Γ_p(α_i)-FD` shape that 1235 consumes. Realized via
`peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291) ∘ `setIntegral_Gamma1_smul_eq`
(PLN). ~60 LOC + measure hyps (the `aggregate_HeckeFD_measure_hyps`-style engine, CF:5463,
PROVEN-pattern). 3 attacks: (i) via 291 (β_i•Γ_p(α_i)-FD tiling); (ii) directly via
`setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum` (FDT:916); (iii) fold into 1612 by
choosing `F=f∣β_i`? — FAILS (f∣β_i not Γ₁-inv), so the CoV MUST come first; this pins the
order LHS-CoV-then-trace, which is the binding sequencing constraint.

### LEAF D — family-trace bookkeeping `Σ_i tr_i(g∣adj β_i) = (det/⟨p⟩-twist of) T_p g`  ← THE GENUINE API GAP
```lean
private theorem heckeT_p_g_traceSlash_family_identity
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (q₀ : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        traceSlash_Gamma_p_α (N := N) (k := k) (α_T_p_Q p hp hpN i)
          (⇑g ∣[k] peterssonAdj (α_T_p_GLPos p hp hpN i : GL (Fin 2) ℝ)) q₀) =
      ⇑(heckeT_p_cusp k p hp hpN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) := by
  sorry  -- type-check-deferred: DS 5.4.4 family-trace = the adjoint double-coset Γα'Γ = ⊔ Γα'_iv.
```
**Classification: API-GAP, BOUNDED (~120–200 LOC, finite combinatorics — NO analysis).**
This is Miyake's "re-fold `Γα'Γ = ⊔_v Γα'_v`" combined with `det(α)^{k-1}` and the
`T*_p = ⟨p⟩⁻¹ T_p` identity. Content: (1) `g∣adj β_i = g∣T_p_lower` (SA:1925/1934, PROVEN)
collapses the per-`i` adjoint to a common `T_p_lower` slash; (2) the
`Γ₁/Γ_p(α_i)`-coset trace sum `Σ_{q∈fiber} (g∣T_p_lower)∣(q.out⁻¹q₀.out)`, summed over `i`,
reindexes (group-theoretically) to the `T_p (⟨p⟩⁻¹g)` representative sum. 3 attacks:
(i) **direct**: expand `traceSlash` def (1332), use SA:1925/1934 to make the slash uniform,
then a `Finset.sum_bij'` matching `⊔_i Γ₁/Γ_p(α_i)` to the `T_p_upper(b)`-family — the bijection
is the concrete coset enumeration already implicit in `heckeT_p_fun_eq_coset_sum` (det-p coset
reps); (ii) **via the existing reindex**: relate to `Gamma1QuotEquivOfGamma0` (PLN:823, the
diamond reindex) for the `⟨p⟩` twist (this IS where σ enters — not as common-reps, but as the
diamond bookkeeping `⟨p⟩`), composing with `heckeT_p_comm_diamondOp` (used at CF:5288); (iii)
**spectral fallback**: prove the *integrated* form directly (skip the form-level identity),
i.e. land `Σ_i c_N•∫_{Γ₁-FD} pet f (tr_i(g∣adj β_i)) = c_N•∫_{Γ₁-FD} pet f (T_p(⟨p⟩⁻¹g))` by
`petN`-level matching against `petN(⟨p⟩f, T_p g) = petN(f, T_p(⟨p⟩⁻¹g))` (the
`petN_heckeT_p_canonical_adjoint_residual` shape, CF:5272, already PROVEN-equivalent).
Attack (iii) is the safest: it converts D into an integrated `petN`-equality, where
`petN_slash_invariant` (⟨p⟩, PLN:923) and `heckeT_p_comm_diamondOp` discharge the diamond
twist without a form-level coset bijection.

---

## 6. Does the σ/trace route SUPERSEDE the false per-tile `h_tile_shift_to_prefactored`?

**DECISIVE: YES.** `h_tile_shift_to_prefactored` (TileBridge:2090/2169) is a *hypothesis*
(named argument), the sum-over-`q` CoV of the OLD route:
`Σ_q ⟪M_∞•q.out⁻¹•fd⟫ (⟨p⟩⁻¹f) ((⟨p⟩⁻¹g)∣T_p_upper(0)∣adjΓ₀rep) = Σ_q ⟪fd⟫ (f∣q.out⁻¹) (g∣M_∞∣...)`
reindexed by `Gamma1QuotEquivOfGamma0`. This route stays **entirely inside the `SL/Γ₁`
tiling** and tries to match a det-`p` slot against a det-`1` slot **per `q`-block**, which
v3 (learnings `d6e58f26`) correctly showed is FALSE per-block. The trace route is structurally
different and avoids this:

1. It routes the det-`p` content through `Γ_p(α_i)-FD` integrals, where the determinant
   mismatch is absorbed by the **measure-preserving CoV `z↦α_i•z`** (1235/770), NOT by a
   per-tile translate. The cocycle `det^{k-2}` is handled inside `peterssonInner_slash_adjoint`.
2. The `c_p,i`-vs-`c_N` index discrepancy (the v2 "fatal" gap) is resolved by the trace
   transfer (1612): `c_p,i•∫_{Γ_p-FD} = c_N•∫_{Γ₁-FD}(tr)`. The multiplicity `[Γ₁:Γ_p(α_i)]`
   that the per-tile route could not reconcile is **exactly the fiber the trace sums over.**
3. `Gamma1QuotEquivOfGamma0` reappears only in LEAF D attack (ii)/(iii) as the **diamond
   `⟨p⟩` twist** (`petN_slash_invariant`'s reindex), where it is PROVEN and correct — never
   as the false per-block matching.

Therefore the trace route makes `h_tile_shift_to_prefactored` (and the entire
`M_infty_branch_*`/`T_p_upper_branch_*` sum-chain) **dead code for the consolidated lemma**:
none of leaf C/D invokes it. The OLD-route framing in the 5212 docstring ("requires API
beyond what the project currently provides: the `SL/Γ₁`-vs-`SL/Γ_p(α)` trace-index bridge")
is now SATISFIED — that bridge is 1612.

---

## 7. Per-leaf table

| Leaf | Classification | Discharge cite (grep-verified) | Attack outcome | LOC |
|---|---|---|---|---|
| A (T_p f = Σ f∣β_i) | DISCHARGED-project | `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307); used CF:5445 | OK | 0 (cite) |
| B (petN linearity slot-1) | DISCHARGED-mathlib/project | `peterssonInner` linearity; `map_add`/`map_sum` (DeltaBSystem:1613) | OK | ~10 |
| C-CoV (per-rep 2.8.2(1)) | DISCHARGED-project | `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235) | OK — proven, det β_i=p>0 | 0 (cite) |
| C2 (α•Γ_p-FD ≈ Γ_p(α')-FD inv-check) | API-GAP, BOUNDED | `smul_..._isFundamentalDomain` (FDT:879) + `Gamma_p_α_conj_mem_Gamma1` (FDT:68) | g∣adj β_i is Γ_p(α_i')-inv | ~40 |
| C1 (index transfer c_N↔c_p,i) | BOUNDED (1612 is the engine) | `setIntegral_..._eq_traceSlash_Gamma1_fundDomain` (FDT:1612); `..._shifted_eq_sum_per_q` (CF:291) | order pinned: CoV-then-trace | ~60 + meas |
| C-trace (1612 application) | DISCHARGED-project | FDT:1612 (DS Ex 5.4.4) | OK — proven | 0 (cite) |
| D (family-trace = T_p g twist) | **API-GAP, BOUNDED** | `traceSlash_Gamma_p_α` def (FDT:1332); SA:1925/1934; `heckeT_p_comm_diamondOp`; `petN_slash_invariant` (PLN:923) | attack (iii) integrated form safest | ~120–200 |
| measure hyps | DISCHARGED-pattern | `aggregate_HeckeFD_measure_hyps` (CF:5463, PROVEN); `integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure` | reusable engine | ~50 |

**Total new content: ~250–400 LOC, all finite (linearity + coset combinatorics +
measurability), NO new measure-theoretic/FD-analytic development.**

---

## 8. Adversarial attack log (each honestly attempted against the BOUNDED claim)

- **Re-attack v3's OPEN core ("FD-image + per-rep exchange unbuilt"):** `grep -c sorry
  FDTransport.lean = 0`; read 879 (FD-image, PROVEN), 1235 (per-rep CoV, PROVEN), 1612
  (index reconciliation, PROVEN). v3's "multi-week unbuilt core" is **built.** v3 was written
  against a pre-trace-machinery state. CLAIM OVERTURNED.
- **Is 1612 actually general enough (not a thin wrapper that secretly assumes the goal)?**
  Read its proof (1632–1652): it composes
  `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_SL_outer_q_sum` (1415) +
  `traceSlash_Gamma_p_α_indep` (1449) + `traceSlash_Gamma_p_α_slash_Gamma1` (1522) +
  `setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum`. All independent of the adjoint goal.
  It takes ARBITRARY `F` (Γ₁-inv), `G` (Γ_p-inv). NOT circular. HOLDS.
- **Does the CoV (1235) really land `g∣adj β_i` as Γ_p(α_i')-invariant?** adj β_i for the
  family: `peterssonAdj M_∞ = T_p_upper(0)·σ_p⁻¹` (SA:317), `g∣adj β_i = g∣T_p_lower`
  (SA:1925/1934). T_p_lower has det p. `g∣T_p_lower` is invariant under `Γ_p(α_i')` =
  `α_i'⁻¹Γ₁α_i'∩Γ₁` — this is LEAF C2, BOUNDED via 879+68. HOLDS modulo C2.
- **Is LEAF D secretly the whole goal again (v3-style circularity)?** D is a FORM-level
  identity `Σ_i tr_i(g∣adj β_i) = T_p(⟨p⟩⁻¹g)`, a statement about Γ₁-forms with NO Petersson
  integral, NO `f`. It cannot be ⟺ the goal (which is a bilinear `petN` identity in `f,g`).
  Even attack (iii)'s integrated form is `pet f (·)`-against-`pet f (·)` for ALL `f`, which by
  non-degeneracy ⟸ the form identity — strictly weaker than the goal's `petN(⟨p⟩f,T_p g)`.
  NOT circular. HOLDS. (This is the precise refutation of v3's "everything ⟺ goal" pessimism:
  the trace route splits off a *form-only* identity D that carries the combinatorics.)
- **Edge: does det^{k-1} (Miyake's `det(α)^{k-1}` prefactor) get mishandled?** The repo's
  `peterssonInner_slash_adjoint` carries `|det α|^{k-2}` inside (AdjT:786 `h_eq`), and `petN`
  is UN-normalized. Miyake's `det(α)^{k-1}` = his normalization `v⁻¹` interplay; here it is
  subsumed by the `peterssonAdj` definition (`adj α = det(α)·α⁻¹`-shaped) + `c_p`/`c_N`.
  Cross-check: SA:317 `peterssonAdj M_∞ = T_p_upper(0)σ_p⁻¹` has NO loose det factor ⇒ the
  weight is absorbed in `T_p_lower`'s entries. Consistent. Not an obstruction.
- **Source-drift vs prompt's "Gamma1QuotEquivOfGamma0 = 4.5.3(2) common reps":** FALSE
  (PLN:823 is `[δ]↦[δγ⁻¹]`, single-coset diamond reindex). Corrected in §1. The common-reps
  role (4.5.3(2)) is instead carried by `heckeT_p_fun_eq_coset_sum` + the `Γ_p(α_i)` apparatus.
  This does NOT weaken the verdict — 4.5.3(2)'s `|Γ\ΓαΓ|=|ΓαΓ/Γ|` is realized by the explicit
  `Option (Fin p)` family on BOTH sides (T_p on LHS, T_p on RHS of the adjoint).
- **Discharge-attack on D (find it pre-proven):** `grep traceSlash.*heckeT_p` = EMPTY. So D
  is a genuine new lemma (API-GAP), not yet in the repo. Its three attacks (§5) are all finite.

---

## 9. Skeleton status & protected-statement check

No edits made to the build (RED-TEAM/planning-only). The three `:= by sorry` skeletons in §5
are TYPE-CHECK-DEFERRED (not inserted). `petN_heckeT_p_symmetric_form_doubleCoset` (5212) and
`petN_heckeT_p_symmetric_form` (5220) signatures untouched. Protected:
`heckeT_p_adjoint` (CF:5393), `exists_simultaneous_eigenform_basis`,
`strongMultiplicityOne_axiom_clean` (SMOObligations:397),
`miyake_4_6_14_delta_slash_sum_coeff_zero` (Lemma4_6_14:303) — all untouched. FDTransport.lean
grep-clean of `native_decide`/`set_option maxHeartbeats`/custom `axiom`/`sorry`. ConcreteFamily
real `sorry` count = 1 (line 5218; the "5" from grep are docstring mentions).
