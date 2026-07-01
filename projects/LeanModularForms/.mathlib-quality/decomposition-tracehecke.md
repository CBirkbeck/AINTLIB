# Decomposition — `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p` (ADVERSARIAL, READ-ONLY)

**Date:** 2026-05-27. **Branch:** hecke-ring. **Mode:** /develop --decompose, planning-only,
no build run, no protected edits.

**TARGET LEAF (proposed, UNBUILT — confirmed absent from the tree):**
```lean
private theorem traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
        (⇑f ∣[k] ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) q₀
      = ⇑(heckeT_p_cusp k p hp hpN f) := by sorry
```
`tr_{q₀}(f∣A) := Σ_{q : SL/Γ_p(A), slGamma_p_αToGamma1 A q = q₀} (f∣A)∣(q.out⁻¹·q₀.out)`,
`A = T_p_lower = diag(p,1)`.

---

## 0. STATE OF THE TREE (grep-verified, not memory)

- The ONLY executable `sorry` in the whole AdjointTheory chain is
  `heckeT_p_aggregate_peeled_diagonal_balance` (ConcreteFamily.lean:5391). Everything
  downstream (`petN_heckeT_p_symmetric_form_doubleCoset` 5400 → `…_global` 5641 →
  `heckeT_p_adjoint` → `exists_simultaneous_eigenform_basis`) bottoms out there.
- **The proposed leaf does NOT exist anywhere** (`grep traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p`
  = EMPTY in `LeanModularForms/` and `.mathlib-quality/`). The brief's claim "proven by the
  prior worker via reversible lemmas" refers to the **logical** equivalence recorded in
  `learnings.jsonl` (ids `00f97f28`, `ca13d40b`), NOT to built Lean reduction lemmas. There is
  NO chain in the tree wiring the residual `sorry` to this leaf. **This must be supplied.**
- The peeled-diagonal balance (the residual) is, verbatim (CF:5372–5391):
  ```
  ⟨D⟩ f (g∣A)  =  ⟨D⟩ ((⟨p⟩f)∣A) g,   D = ⋃_{i:Option(Fin p)} β_i • Γ₁-FD,
  β_none = M_∞,  β_(some b) = T_p_upper(b),  A = glMap(T_p_lower).
  ```
  Its own docstring (CF:5337–5371, recent worker) asserts the proven `Γ_p(α)` engine
  (1235/1612) does **NOT** discharge it as-is, because `D` is the single-tile aggregate
  (`β_i•Γ₁-FD`, det β_i = p) while the engine consumes `Γ_p(α_i)-FD` (= `[Γ₁:Γ_p(α_i)]`
  det-1 tiles), a different decomposition.

## 1. MIYAKE CROSS-CHECK (verbatim, fresh PDF read — `docs/Toshitsune Miyake.pdf`)

**Lemma 4.5.6(1) (p.138, PDF pg 146):** "As a complete set of representatives of
`Γ₀(N)\Γ₀(N)[[1,0],[0,pᵉ]]Γ₀(N)` we may take: `{[[1,m],[0,pᵉ]] : 0≤m<pᵉ, (m,pᵉ,pᵉ⁻¹)=1}`
if p∤N, `pᵉ⁻¹` … `if p|N`." **(2):** "`deg(Γ₀(N)[[1,0],[0,pᵉ]]Γ₀(N)) = pᵉ+pᵉ⁻¹` if p∤N,
`pᵉ` if p|N." For e=1 (T(p)), p∤N: **p+1 reps** = `{[[1,m],[0,p]] : 0≤m<p}` (p reps) plus the
`[[p,0],[0,1]]`-type rep = p+1.

**(4.5.26) (p.142, PDF pg 150):** "for `f(z)∈M_k(N,χ)`,
`(f|T(n))(z) = n^{k-1} Σ_{ad=n, 0≤b<d} χ(a) d^{-k} f((az+b)/d)`."

**Theorem 2.8.2 (p.76, PDF pg 84):** "(1) `r' = α⁻¹r₁α ∩ r₂`, `(f|ₖα,g) = (f,g|ₖα')`,
`α'=det(α)α⁻¹`. (2) `(f|ΓαΓ,g) = (f,g|Γα'Γ)`," proof: "`ΓαΓ=⊔Γαᵥ=⊔αᵥΓ` … common set of
representatives by Lemma 2.7.7 … `(f|ΓαΓ,g)=det(α)^{k-1}Σ_v(f|ₖαᵥ,g)=det(α)^{k-1}Σ_v(f,g|ₖα'ᵥ)
=(f,g|Γα'Γ)`."

**Lean ↔ source match.** `heckeT_p_fun` (HeckeT_p:111) `= Σ_{b<p} f∣[[1,b],[0,p]] +
(⟨p⟩f)∣[[p,0],[0,1]]` is exactly (4.5.26)/4.5.6(1) at n=p (the diamond ⟨p⟩=χ(a)|_{a=p} twist
sits on the `[[p,0],[0,1]]` term). `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307, PROVEN)
unfolds it to `f∣M_∞ + Σ_b f∣T_p_upper(b)` (M_∞ = σ_p·diag(p,1) absorbs the ⟨p⟩). The proposed
leaf's `A = T_p_lower = diag(p,1)` is the **transpose/lower orientation** of Miyake's
`diag(1,p)`; the verified `peterssonAdj(A) = adjugate(A) = [[1,0],[0,p]] = T_p_upper(0)`
(SummandAdjoint:273) realizes the `α↦α'` of 2.8.2(1). The leaf is the Lean form of "the
`Γ'\Γ`-coset trace of `f|ₖA` equals `f|ΓαΓ = T_p f`," i.e. the FIRST identity in 2.8.2(2)'s
chain read fiberwise. **Verdict: the leaf is source-faithful to Miyake 2.8.2 + 4.5.6.**

CAUTION on orientation (adversarial): Miyake 4.5.6 enumerates the **left** cosets of `Γα`;
the `traceSlash` def sums over the **fiber** `q.out⁻¹·q₀.out` (a `Γ_p(A)\Γ₁` enumeration on
the right). The bijection between these is Miyake's "`ΓαΓ=⊔Γαᵥ=⊔αᵥΓ` common reps" (2.7.7) —
which is exactly the part that is NOT yet Lean-built (see Leaf L2 below). So the leaf hides the
common-reps fact.

---

## 2. WHAT THE LEAF MEANS, UNFOLDED (the crux is here)

Unfold `traceSlash_Gamma_p_α A (f∣A) q₀` (def FDTransport:1332):
```
tr_{q₀}(f∣A) = Σ_{q ∈ fiber(q₀)} (f∣A)∣(q.out⁻¹·q₀.out)
            = Σ_{q ∈ fiber(q₀)} f∣(A·δ_q),   δ_q := q.out⁻¹·q₀.out ∈ Γ₁(N).
```
(`(f∣A)∣δ = f∣(A·δ)` by `SlashAction.slash_mul`; `δ_q ∈ Γ₁` because both `q.out, q₀.out` lie
in the same `Γ₁`-coset `q₀`, as `slGamma_p_αToGamma1 q = q₀`.)

Target: this equals `Σ_i f∣β_i = T_p f` (via `heckeT_p_fun_eq_coset_sum`).

**So the leaf is EXACTLY:** the multiset `{A·δ_q : q ∈ fiber(q₀)}` coincides, modulo right-`Γ₁`
(which `f∣·` cannot see, since `f` is `Γ₁`-invariant) **and with equal det weight p**, with the
Hecke family `{β_i : i ∈ Option(Fin p)}`. This is a **FORM-level, `f`-only, `g`-free identity**
— strictly weaker than the bilinear balance, hence (as the prior v4 decomposition argued for the
analogous "Leaf D") **NOT circular** with the symmetric form. GOOD: boundedness is at least not
self-defeating.

**MATHEMATICAL CONTENT (3 facts, all genuinely about the group `Γ_p(A)`):**
- (i) `|fiber(q₀)| = [Γ₁ : Γ_p(A)] = p+1`. **UNPROVEN** (no `= p+1` fact anywhere; the fiber
  cards `slGamma_p_αToGamma1_fiberCard`, `slToPslQuot_fiberCard_Gamma_p_α` are all abstract).
- (ii) an EXPLICIT bijection `fiber(q₀) ≃ Option(Fin p)`, `q ↦ i(q)`, with `A·δ_q ∈ β_{i(q)}·Γ₁`
  and det A·δ_q = p. **UNPROVEN** — this is Miyake's common-reps (`ΓαΓ=⊔Γαᵥ=⊔αᵥΓ`).
- (iii) reassembly `Σ_q f∣(A·δ_q) = Σ_i f∣β_i`, then `= T_p f` via `heckeT_p_fun_eq_coset_sum`
  (PROVEN). Given (i)+(ii), this is a `Finset.sum_bij'` + `f∣(β_i·γ)=f∣β_i` (`f` Γ₁-inv).

The det-weight is automatic: `A·δ_q` and `β_i` both have det p, and `f∣(p-scaled SL elt)`
matches because `β_i = A·δ_q·γ⁻¹` with γ∈Γ₁ gives the SAME slash. No `p^{k-2}` central factor
survives at the FORM level (it only appears in the SMUL↔matrix identity `A·β_i = pI·γ_i`, which
is the **inverse** direction and is the engine/balance content, NOT the leaf content).

---

## 3. VERIFIED PROJECT MACHINERY (grep + read confirmed)

| Fact (file:line) | Statement | Proven? | Role for leaf |
|---|---|---|---|
| `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307) | `T_p f = f∣M_∞ + Σ_b f∣T_p_upper(b)` | YES | step (iii) target = T_p f |
| `traceSlash_Gamma_p_α` (FDTransport:1332 def) | `tr_{q'}G = Σ_{fiber} G∣(q.out⁻¹q'.out)` | def | the leaf LHS |
| `slGamma_p_αToGamma1` (FDT:1003) + `_surjective` (1021) + `_fiber_card_uniform` (1030) | quotient map, surjective, uniform fibers | YES | gives the fiber & its uniformity |
| `slGamma_p_αToGamma1_fiberCard` (FDT:1084 def) + `_eq` (1090) | def of fiber card, indep of q' | YES (def) | (i) needs its VALUE = p+1 |
| `Gamma_p_α` (FDT:41) = `conjGL Γ₁ (α.map ℝ) ⊓ Γ₁` | the group | def | A = T_p_lower instance |
| `Gamma_p_α_le_Gamma1` (FDT:55), `_finiteIndex` (46), `_finiteIndex_in_Gamma1` (61) | Γ_p ≤ Γ₁, finite idx | YES | δ_q ∈ Γ₁, fiber finite |
| `slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152) | `(f∣α)∣γ = f∣α`, γ∈Γ_p(α) | YES | trace summands well-def / engine slot-2 |
| `T_p_lower_mul_T_p_upper_smul_eq_shift_smul` (DeltaB:456) | `A·T_p_upper(b)•τ = shiftSL(b)•τ` (SMUL, central scalar dropped) | YES | the A·β_i↔Γ₁ geometry |
| `T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul` (DeltaB:483) | `A·M_∞•τ = M_∞_Γ₁_factor•τ` | YES | M_∞ branch of (ii) |
| `T_p_lower_smul_Hecke_FD_eq_iUnion_tile` (DeltaB:700) | `A•(⋃_iβ_i•S)=⋃_i γ_i•S`, γ_i∈Γ₁ | YES | **A•D = union of p+1 Γ₁-tiles** |
| `T_p_lower_tile_family` (DeltaB:687) | `none↦M_∞_Γ₁_factor, some b↦shiftSL(b)` ∈ Γ₁ | def | the γ_i of A·β_i |
| `mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower` (DeltaB:794) | `γ_i · adj(β_i) = A` (matrix, GL ℝ) | YES | β_i = adj-related to A·γ_i |
| `M_infty_Gamma1_factor_mem_Gamma1` (SummandAdj:1308), `shiftSL_loc_mem_Gamma1` (SA:344) | γ_i ∈ Γ₁ | YES | (ii) lands in Γ₁ |
| `peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero` (SA:273) | `adj(A)=T_p_upper(0)` | YES | 2.8.2(1) α↦α' |
| `slash_diag_scalar` (NebentypusHeckeRingHom:794) | `f∣(diag(c,c)) = c^{k-2}•f` | YES | central scalar IF needed (it isn't, form-level) |
| **trace engine** `setIntegral_…_eq_traceSlash_Gamma1_fundDomain` (FDT:1612) | `c_p•∫_{Γ_p(α)-FD}pet F G = c_N•∫_{Γ₁-FD}pet F (tr_{q₀}G)` | YES | the INTEGRATED transfer (needs G Γ_p-inv) |
| `peterssonInner_slash_adjoint_over_Gamma_p_α` (FDT:1235) | `⟪Γ_p(α)-FD⟫(f∣α)g = ⟪α•Γ_p(α)-FD⟫ f (g∣adjα)` | YES | per-rep CoV 2.8.2(1) |
| `smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDT:879) | `α•Γ_p(α)-FD` is FD for `Γ₁∩αΓ₁α⁻¹` | YES | FD-image |
| `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291) | `⟪α_i•Γ_p(α_i)-FD⟫ = Σ_q⟪(α_i·q.out⁻¹)•Γ₁-FD⟫` | YES | per-i tile decomposition |
| `aggregate_HeckeFD_measure_hyps` (CF:5233) | null-meas + integrability for D | YES | reusable measure engine |
| `aedisjoint_pairwise_T_p_family` (SA:1431) | the p+1 β_i•Γ₁-FD tiles AE-disjoint | YES | for sum splitting |

**NOT proven anywhere (grep-confirmed):** `[Γ₁:Γ_p(T_p_lower)] = p+1`; `D =ₐₑ A•Γ_p(A)-FD`;
any explicit coset-rep enumeration of `Γ_p(A)\Γ₁`; `traceSlash_Gamma_p_α … = heckeT_p …`.

---

## 4. SUB-LEMMA DECOMPOSITION (the leaf, split)

Write `A = T_p_lower p hp.pos`, `Ar = A.map (Rat.castHom ℝ) = glMap A`.

| Sub-lemma | Classification | Discharge cite (grep-verified) | Best attack | LOC |
|---|---|---|---|---|
| **L0** `(f∣Ar)∣δ = f∣(Ar·δ)` and `δ_q∈Γ₁` for q∈fiber(q₀) | DISCHARGED-mathlib | `SlashAction.slash_mul`; `QuotientGroup.eq`/`slGamma_p_αToGamma1` defeq + `Gamma_p_α_le_Gamma1` | direct | ~15 |
| **L1** `slGamma_p_αToGamma1_fiberCard (T_p_lower) = p+1` | **API-GAP, the HARD core** | NONE pre-proven; `slGamma_p_αToGamma1_fiber_card_uniform` (FDT:1030) reduces "any q'" to "q'=1"; needs index `[Γ₁:Γ_p(A)]`=p+1 | see §5 | **~120–250** |
| **L2** explicit bijection `fiber(q₀) ≃ Option(Fin p)`, `q↦i`, with `Ar·δ_q ∈ glMap β_{i}·Γ₁` | **API-GAP, the CRUX** | `T_p_lower_mul_{T_p_upper,M_infty}_smul_eq_…` (DeltaB:456/483) give the GEOMETRY; `T_p_lower_tile_family`/`mapGL_tile_mul_peterssonAdj…` (DeltaB:687/794) the matrix bridge — but ALL at SMUL/matrix level, NOT a coset-rep bijection | see §5 | **~150–300** |
| **L3** `Σ_{q∈fiber} f∣(Ar·δ_q) = Σ_i f∣(glMap β_i)` | DISCHARGED-once-L2 | `Finset.sum_bij'` (mathlib) + `f∣(βγ)=f∣β` via `slash_Gamma1_eq f` (used FDT:162) | sum_bij' | ~40 |
| **L4** `Σ_i f∣(glMap β_i) = ⇑(heckeT_p_cusp f)` | DISCHARGED-project | `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307), reshaped exactly as `petN_heckeT_p_LHS_eq_aggregate` (CF:5207–5223) | copy CF:5207 | ~25 |

**Leaf-internal total: ~350–630 LOC**, dominated by L1+L2.

### 4b. THE WIRING the leaf is supposed to close (separate from the leaf itself!)

The brief asserts: residual `heckeT_p_aggregate_peeled_diagonal_balance` ⟺ symmetric form;
and "engine 1612 + 1235 + THIS leaf → close symmetric form." But the leaf is a **form identity
about `tr(f∣A)`**, while the balance is a **bilinear integral over `D`**. Connecting them is
NOT free. The honest wiring chain (each piece a SEPARATE obligation, NOT inside the leaf):

| Wire | Classification | Discharge | LOC |
|---|---|---|---|
| **W1** `(f∣A)` is `Γ_p(A)`-slash-invariant (engine slot-2 hyp) | DISCHARGED | `slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152) | 0 (cite) |
| **W2** `D =ₐₑ A•Γ_p(A)-FD` (so the balance domain = the engine's transported FD) | **API-GAP, BOUNDED-ish** | `T_p_lower_smul_Hecke_FD_eq_iUnion_tile` (DeltaB:700) gives `A•D=⋃γ_i•Γ₁-FD`; must match `A•Γ_p(A)-FD=⋃(A·q.out⁻¹)•Γ₁-FD` — needs **L1+L2** again (the tile sets coincide iff the coset enumerations match) | ~80 + L1/L2 |
| **W3** apply engine 1612 with F=f, G=f∣A (or the ⟨p⟩f side): `c_p•∫_{Γ_p(A)-FD}pet f (f∣A) = c_N•∫_{Γ₁-FD}pet f (tr_{q₀}(f∣A))` | DISCHARGED | FDT:1612 | 0 (cite) + meas |
| **W4** substitute leaf `tr(f∣A)=T_p f` and re-fold `c_N•∫_{Γ₁-FD}pet f (T_p f) = petN(f,T_p f)` | DISCHARGED | `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (PLN), `slToPslQuot_fiberCard` | ~40 |
| **W5** reconcile `c_p` (engine) with `c_N` and the det-`p^{k-2}` weight between the two integrals to actually produce the BILINEAR balance both-slots | **API-GAP, the SAME analytic content** | NONE; this is where the recent worker's docstring (CF:5337–5371) says the route stalls | **UNBOUNDED at present** |

**W2 and W5 re-import the very combinatorics (L1/L2) and the c_p/c_N reconciliation the residual
docstring flags as "genuine multi-lemma development."** The leaf does NOT make W2/W5 disappear;
it relocates L1/L2 into them.

---

## 5. ≥3 ATTACKS ON THE TWO CRUX SUB-LEMMAS (L1, L2)

### L1 — `slGamma_p_αToGamma1_fiberCard (T_p_lower) = p+1` (= `[Γ₁ : Γ_p(A)]`)

(i) **Index-arithmetic attack.** `[Γ₁ : Γ_p(A)] = [Γ₁ : A⁻¹Γ₁A ∩ Γ₁] = deg(Γ₁ A Γ₁)`. For
A=diag(p,1), p∤N, this is `p+1` (Miyake 4.5.6(2)). Lean route: relate `Gamma_p_α A` to the
double-coset degree. **No project lemma computes any `Γ_p(α)` index numerically** — the entire
FDTransport machinery is index-agnostic (uses abstract `slToPslQuot_fiberCard_Gamma_p_α`). Would
need: a NEW lemma `[Γ₁(N) : Γ₁(N) ∩ A⁻¹Γ₁(N)A] = p+1`, provable via the orbit-stabilizer on
`ℙ¹(ℤ/p)` or by exhibiting the p+1 reps explicitly. Mathlib has `Subgroup.relIndex`,
`Subgroup.card_quotient_…`, but the diag(p,1)-conjugate-intersection index is NOT in mathlib.
**Estimate ~120–250 LOC** (this is a genuine congruence-subgroup index computation).

(ii) **Explicit-reps attack (BEST, dovetails L2).** Exhibit p+1 explicit reps of `Γ_p(A)\Γ₁`
and prove they are a complete irredundant set, then `Fintype.card = p+1`. The reps are forced by
L2's bijection. Once L2 is built, L1 = `Fintype.card_eq` of the bijection's codomain
`Option(Fin p)` = `p+1` (`Fintype.card_option`, `Fintype.card_fin`). **So L1 collapses INTO L2**
(card of the enumerated set). This is the right framing: **don't prove L1 independently; get it
free from L2.** ~10 LOC given L2.

(iii) **Geometric/measure attack.** `A•D` and `A•Γ_p(A)-FD` are both FDs for `Γ₁∩AΓ₁A⁻¹`
(879); D has p+1 tiles, Γ_p(A)-FD has `[Γ₁:Γ_p(A)]` tiles; equal a.e. measures force the counts
equal. But "equal measures ⇒ equal tile counts" needs `μ(Γ₁-FD) ≠ 0, < ∞` AND AE-disjointness
on BOTH sides — circular with W2 and still needs the count to be p+1 from D's side (which is
`Fintype.card_option = p+1`, free). Viable but routes through measure theory unnecessarily.
**Attack (ii) is decisively best: L1 ⊂ L2.**

### L2 — the coset↔Hecke-rep bijection `fiber(q₀) ≃ Option(Fin p)`, `Ar·δ_q ∈ glMap β_i·Γ₁`

**This is THE CRUX of the whole leaf (and of the residual `sorry`).**

(i) **Forward matrix-enumeration attack.** Define `i ↦ q_i ∈ SL/Γ_p(A)` by `q_i := mk(γ_i⁻¹)`
where `γ_i = T_p_lower_tile_family i ∈ Γ₁` (DeltaB:687). Claim: `{q_i}` is exactly `fiber(q₀)`
for q₀=mk(1), and `Ar·δ_{q_i} = glMap β_i` (matrix), because `Ar·γ_i⁻¹·(stuff) =` … Use the
PROVEN matrix bridge `mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower`:
`γ_i·adj(β_i) = A` ⟹ `A·γ_i⁻¹ = A·γ_i⁻¹`; but we need `A·δ_q` not `A·γ_i`. The δ_q = q.out⁻¹q₀.out
are the `Γ_p(A)\Γ₁` connectors, and relating them to `γ_i⁻¹` requires `q_i.out ≡ γ_i⁻¹ mod Γ_p(A)`,
which is NOT automatic (`.out` is a `Classical.choice` rep). **This is the real friction:** the
`traceSlash` uses `q.out` (arbitrary coset reps), while the verified geometry uses the SPECIFIC
`γ_i`. Bridging needs `(f∣A)∣q.out⁻¹q₀.out = (f∣A)∣γ_{i(q)}⁻¹` for the matching i — provable via
`slash_α_Gamma_p_α_invariant` (FDT:134, the Γ_p(A)-invariance absorbs the `q.out ↔ γ_i⁻¹`
discrepancy since they differ by a Γ_p(A) element). **~150–250 LOC**, genuine.

(ii) **Injectivity-via-distinctness attack.** The p+1 candidate reps are distinct mod Γ_p(A):
reuse the PROVEN `adj_upper_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:348) and
`adj_M_infty_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:378) — these show the β_i are pairwise
distinct in `Γ₁\Γ₁AΓ₁` (different (0,1)-entries mod p). Transport to `Γ_p(A)\Γ₁` via the
A-conjugation. Then surjectivity onto fiber(q₀) by counting (= L1, circular) OR by direct
`Γ₁ = ⊔_i Γ_p(A)·γ_i⁻¹` decomposition. The distinctness facts are PROVEN and reusable; the
"complete" (surjectivity) half is the new work. **~120–200 LOC.**

(iii) **Bypass via the SMUL/FD identity (the route W2 wants).** Skip the coset-rep bijection;
instead prove `D =ₐₑ A•Γ_p(A)-FD` directly: `A•Γ_p(A)-FD = ⋃_{q:Γ₁/Γ_p(A)}(A·q.out⁻¹)•Γ₁-FD`
(by `Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted_eq_smul`, CF:285/FDT:366) and `A•D =
⋃_i γ_i•Γ₁-FD` (DeltaB:700); both are FDs for `Γ₁∩AΓ₁A⁻¹` (879), hence a.e. equal **as SETS** —
which does NOT require matching the index reps, only `IsFundamentalDomain.ae_eq` style uniqueness.
**This is the most promising for the INTEGRATED form** (W2/W5), and sidesteps the `.out`-vs-`γ_i`
friction of (i). BUT it proves a SET identity, not the FORM identity the leaf states, so it serves
the integrated route (W-chain) rather than the leaf as literally written. **~80–150 LOC** but
only closes W2, leaving W5's c_p/c_N + det-weight reconciliation — the residual's stated gap.

---

## 6. BINDING VERDICT

### Is the coset↔Hecke matching (L2) the crux? — **YES.**
L1 collapses into L2 (attack (ii): card = `Fintype.card_option`). L0/L3/L4 are routine
(`slash_mul`, `sum_bij'`, copy of `petN_heckeT_p_LHS_eq_aggregate`). **L2 carries the entire new
mathematical content of the leaf**: the explicit bijection `Γ_p(A)\Γ₁ ≃ {Hecke reps}` with
`A·δ_q ≡ β_i mod Γ₁`. This is precisely Miyake's "`ΓαΓ=⊔Γαᵥ=⊔αᵥΓ` common reps" (Lemma 2.7.7 /
4.5.3(2)), which is **NOT yet Lean-built** for this group.

### Is L2 finite/elementary (bounded) or does it hide a hard structural fact?
**Bounded-but-substantial.** It is FINITE (p+1 explicit matrices) and ELEMENTARY (matrix
products mod N, distinctness via (0,1)-entries mod p, all `Fin 2` / `ZMod` arithmetic). It hides
**no analysis** and no deep structural theorem — the orbit/coset structure of diag(p,1) on Γ₁ is
classical. The friction is engineering: bridging `Classical.choice` reps (`q.out`) to the
explicit `γ_i = T_p_lower_tile_family i`, and proving the enumeration is complete (surjective).
The PROVEN distinctness lemmas (`adj_upper_inv_mul_upper_not_mem_Gamma1`,
`adj_M_infty_inv_mul_upper_not_mem_Gamma1`) supply half of it. **It is NOT a thin wrapper, and
NOT a multi-week structural wall — it is a real but bounded congruence-coset combinatorics
lemma.**

### LOC: verify/refute the ~400–800 estimate.
- **Leaf alone** (L0–L4, with L1⊂L2): **~350–630 LOC** (L2 ~150–300, L1 ~10 given L2, L0 ~15,
  L3 ~40, L4 ~25, plus reuse glue ~40–80).
- **BUT the leaf does NOT close the residual `sorry` by itself.** The brief's "engine + leaf →
  symmetric form" needs **W2 (D=ₐₑA•Γ_p(A)-FD, ~80–150 + re-uses L1/L2)** and crucially **W5
  (c_p/c_N + det-`p^{k-2}` reconciliation to get the BILINEAR both-slot balance)** — and W5 is
  the exact content the residual docstring (CF:5337–5371) and the most-recent learning
  (`ca13d40b`, 2026-05-27) call "genuine multi-lemma development, est 400–800 LOC, NOT bounded
  glue." **W5 is NOT discharged by this leaf.**

### THE VERDICT: **MIXED — leaf BOUNDED, full closure OPEN.**

> **The leaf `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p` is BOUNDED at ~350–630 LOC**, crux =
> L2 (a finite, elementary, but real congruence-coset bijection; L1 ⊂ L2). The prior ~400–800
> estimate is **slightly HIGH for the leaf-in-isolation** (because L1 collapses into L2 and L3/L4
> are near-free), but **CORRECT-to-LOW for the full closure of the residual `sorry`**, which
> additionally needs W2 (~80–150) and the genuinely-open **W5** (the c_p/c_N + det-weight
> bilinear reconciliation). **The brief's premise that "engine 1612 + 1235 + this leaf close
> everything" is OPTIMISTIC: it omits W5.** With W5 unresolved, the chain leaf→residual is NOT
> complete. The leaf converts the residual's *combinatorial* half (L1/L2) into a clean named,
> bounded target — a genuine and worthwhile decomposition — but the *index/det-weight transfer*
> half (W5) remains the open analytic-bookkeeping piece.

**REFINEMENT of both prior errors the brief warned about:**
- The leaf is NOT a thin wrapper (L2 is real ~150–300 LOC of coset combinatorics) — refutes
  under-estimation.
- The leaf is NOT a multi-week wall either — L2 is finite/elementary with half its content
  (distinctness) already PROVEN — refutes over-estimation.
- The genuine remaining wall is **W5 (index/trace/det reconciliation)**, which the leaf does NOT
  remove. This matches the residual docstring and learning `ca13d40b`.

---

## 7. SKELETONS (type-check-DEFERRED, NOT inserted into build)

```lean
-- L0
private lemma traceSummand_eq_slash_mul
    (p : ℕ) (hp : Nat.Prime p) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N)
    {q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos)}
    (hq : slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q₀) :
    (⇑f ∣[k] ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) ∣[k]
        ((q.out : SL(2, ℤ))⁻¹ * q₀.out)
      = ⇑f ∣[k] (((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹ * q₀.out) : GL (Fin 2) ℝ)) := by
  sorry -- SlashAction.slash_mul; (q.out⁻¹q₀.out) ∈ Γ₁ from hq + Gamma_p_α_le_Gamma1

-- L2 (THE CRUX): explicit bijection fiber(q₀) ≃ Option(Fin p) realizing A·δ_q ∈ glMap β_i·Γ₁
private def fiber_T_p_lower_equiv_HeckeReps
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    {q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos) //
        slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q₀} ≃ Option (Fin p) :=
  sorry -- forced by T_p_lower_tile_family (DeltaB:687) + distinctness
        -- (adj_upper_inv_mul_upper_not_mem_Gamma1, adj_M_infty_inv_mul_upper_not_mem_Gamma1)

private lemma slash_A_delta_eq_slash_Hecke_rep
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N)
    (q : {q // slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q₀}) :
    ⇑f ∣[k] (((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((q.1.out : SL(2, ℤ))⁻¹ * q₀.out) : GL (Fin 2) ℝ))
      = ⇑f ∣[k] (match fiber_T_p_lower_equiv_HeckeReps p hp hpN q₀ q with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) := by
  sorry -- A·δ_q = β_i·γ, γ∈Γ₁; f∣(β_i·γ)=f∣β_i via slash_Gamma1_eq f
        -- core uses slash_α_Gamma_p_α_invariant to absorb q.out↔γ_i discrepancy

-- L1 (collapses into L2's codomain card)
private lemma slGamma_p_αToGamma1_fiberCard_T_p_lower
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    slGamma_p_αToGamma1_fiberCard (N := N) (T_p_lower p hp.pos) = p + 1 := by
  sorry -- Fintype.card via fiber_T_p_lower_equiv_HeckeReps; Fintype.card_option + card_fin

-- THE LEAF (assembles L0/L2/L3/L4)
private theorem traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
        (⇑f ∣[k] ((T_p_lower p hp.pos).map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) q₀
      = ⇑(heckeT_p_cusp k p hp hpN f) := by
  sorry -- unfold traceSlash (FDT:1332); L0; Finset.sum_bij' along
        -- fiber_T_p_lower_equiv_HeckeReps with slash_A_delta_eq_slash_Hecke_rep;
        -- = Σ_i f∣β_i = heckeT_p_fun_eq_coset_sum (copy CF:5207–5223)
```

```lean
-- W2 (the SET identity the integrated route needs; SEPARATE from the leaf)
private lemma aggregate_D_ae_eq_T_p_lower_smul_Gamma_p_α_fundDomain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      =ᵐ[μ_hyp]
    ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        Gamma_p_α_fundDomain_PSL (N := N) (T_p_lower p hp.pos)) := by
  sorry -- A•D = ⋃γ_i•Γ₁-FD (DeltaB:700); A•Γ_p(A)-FD = ⋃(A·q.out⁻¹)•Γ₁-FD (FDT:366);
        -- both FDs for Γ₁∩AΓ₁A⁻¹ (879) ⇒ ae_eq.  NB still routes through L1/L2 counts.
-- W5 remains OPEN: no skeleton closes the c_p/c_N + det-p^{k-2} bilinear reconciliation.
```

---

## 8. ADVERSARIAL ATTACK LOG (each honestly attempted)

- **"Is the leaf circular with the symmetric form?"** NO. The leaf is `f`-only, `g`-free,
  integral-free (a `ℍ→ℂ` function identity). The bilinear balance quantifies over all f,g with a
  Petersson integral. Form identity ⊭ bilinear identity. (Same non-circularity logic the prior v4
  used for "Leaf D".) HOLDS — boundedness is not self-defeating.
- **"Does the leaf close the residual `sorry` (brief's premise)?"** NOT by itself. The residual
  is the BILINEAR balance over D. The leaf feeds the INTEGRATED route only after W2 + W3 + W4,
  and W5 (c_p/c_N + det-weight) is still open. `grep` shows the engine 1612 is PROVEN but UNUSED
  anywhere — confirming the wiring leaf→residual is NOT built. The brief over-credits the leaf.
- **"Is `[Γ₁:Γ_p(T_p_lower)]=p+1` proven?"** NO (grep: no numeric Γ_p index anywhere). L1 is a
  genuine gap; best discharged AS a corollary of L2's bijection (card_option), not standalone.
- **"Is L2 already proven (find it)?"** `grep` for `fiber.*equiv`, `Gamma_p.*equiv.*Option`,
  `traceSlash.*heckeT` = EMPTY. The GEOMETRY (A·β_i↔Γ₁ smul, DeltaB:456/483/700) and the
  matrix bridge (DeltaB:794) and the DISTINCTNESS (HeckeT_p_Gamma1:348/378) are PROVEN, but the
  coset-rep BIJECTION on `Γ_p(A)\Γ₁` (with `.out` reps) is NOT. Genuine new lemma.
- **"Is the central scalar `p^{k-2}` an obstruction to the leaf?"** NO at form level: `A·δ_q`
  and `β_i` both have det p; `f∣(A·δ_q)=f∣β_i` because they differ by a right-Γ₁ factor that `f`
  absorbs. `slash_diag_scalar` (Nebentypus:794) is only needed if one factors out `pI` — which
  the SMUL/matrix geometry does, but the FORM leaf does not. The `p^{k-2}` reappears in W5 (the
  integrated det-weight bookkeeping), NOT in the leaf.
- **"Could the leaf be done over `α_T_p_Q i` family instead (prior v4 Leaf D)?"** The single-α
  framing (THIS leaf, α=A=T_p_lower) is GENUINELY SIMPLER than the v4 family-trace `Σ_i tr_i(g∣adj
  β_i)` — one group `Γ_p(A)`, one trace, p+1 cosets, vs. p+1 groups `Γ_p(α_i)` each with its own
  fiber. So the brief's reframing IS a real simplification of the COMBINATORIAL leaf. But it does
  not simplify W5. CONFIRMED: reframing helps L1/L2, not the analytic reconciliation.

## 9. PROTECTED-STATEMENT / BUILD CHECK
No build run (`lake build`/`lean` not invoked). No edits to the tree. All skeletons in §7 are
type-check-DEFERRED (this file only). `heckeT_p_aggregate_peeled_diagonal_balance` (CF:5391, the
residual `sorry`), `heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`,
`strongMultiplicityOne_axiom_clean`, `miyake_4_6_14_*` — all untouched. Miyake 4.5.6/(4.5.26)/2.8.2
cross-checked verbatim from `docs/Toshitsune Miyake.pdf` (PDF pages 84, 146, 147, 150).
