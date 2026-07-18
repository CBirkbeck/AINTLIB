# Decomposition — W5: the `c_p/c_N + det-p^{k-2}` bilinear reconciliation (ADVERSARIAL, READ-ONLY)

**Date:** 2026-05-27. **Branch:** hecke-ring. **Mode:** `/develop --decompose`, planning-only,
no `lake build`, no protected edits. **Build: GREEN/QUIESCENT.**

**SCOPE.** W5 is the open analytic core of the `T_p` Petersson adjoint. After the proven,
reversible aggregate expansions, the entire adjoint collapses to the single residual `sorry`
`heckeT_p_aggregate_peeled_diagonal_balance` (ConcreteFamily.lean:5391). The combinatorial
family-trace leaf (`tr(f∣A)=T_p f`) is decomposed+bounded in `decomposition-tracehecke.md`.
W5 is the *remaining* bilinear `⟨D⟩ pet F G` ↔ `∫_{Γ₁-FD} pet F (tr G)` reconciliation.

---

## 0. W5 — FORMAL LEAN STATEMENT (= the residual `sorry`, verbatim CF:5372–5391)

W5 **is** `heckeT_p_aggregate_peeled_diagonal_balance`. There is NO separate "W5 lemma":
grep-confirmed that `petN_heckeT_p_RHS_aggregate_eq` (CF:5619, the route's nominal "leaf 2")
discharges by `rw`-ing back to `petN_heckeT_p_symmetric_form_doubleCoset` (CF:5400) which is
`rw`-ed to the residual sorry (CF:5412). The chain leaf2→residual is **circular**; the residual
carries 100% of W5's content. Formal statement (`A = glMap (T_p_lower) = diag(p,1)`,
`D = ⋃_{i:Option(Fin p)} β_i•Γ₁-FD`, `β_none=M_∞`, `β_(some b)=T_p_upper(b)`):

```lean
private theorem heckeT_p_aggregate_peeled_diagonal_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))            -- = D
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =   -- ⟨D⟩ f (g∣A)
    peterssonInner k
      (⋃ i ∈ … same D …)
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))     -- (⟨p⟩f)∣A
      ⇑g := by sorry
```
i.e. `⟨D⟩ f (g∣A) = ⟨D⟩ ((⟨p⟩f)∣A) g`. Both sides are honest integrals over the *same* `D`.

### Lean ↔ DS Ex 5.4.4 match (verbatim source, cross-checked NOT from memory)
DS Ex 5.4.4 (p.183), un-normalized: `Γ'⊂Γ`, `Γ=⊔Γ'α_i`, `tr g=Σ g[α_i]_k`; then
`∫_{Γ'-FD} f·ḡ·y^k = ∫_{Γ-FD} f·(tr g)·y^k`. W5 is THIS with `Γ'=Γ_p(A)`, `Γ=Γ₁`, plus the
`det-p^{k-2}` weight from `A`'s center and the `c_p/c_N` fiber factors. **Source-faithful.** The
project's `peterssonInner k F G = ∫ conj(F)·G·y^k` is conjugate-linear in `F`, linear in `G`, so
the trace lands on the linear slot exactly as DS requires. The trace engine FDT:1612 is the
un-normalized DS 5.4.4: `c_p•∫_{Γ_p(α)-FD} pet F G = c_N•∫_{Γ₁-FD} pet F (tr_{q₀} G)` — VERIFIED
verbatim (FDT:1606–1631).

---

## 1. STATE OF THE TREE (grep-verified, not memory)

| Fact | Status |
|---|---|
| Trace engine `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain` (FDT:1612) | PROVEN; **referenced NOWHERE** (grep empty) |
| `traceSlash_Gamma_p_α` def (FDT:1332) | PROVEN; **referenced NOWHERE in ConcreteFamily** |
| `peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q` (CF:291) | PROVEN; **used NOWHERE** |
| `sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN` (FDT:1198) | PROVEN; used only to prove its own sibling (not in the live chain) |
| `petN_heckeT_p_RHS_aggregate_eq` (CF:5619, nominal "leaf 2") | reduces (CIRCULARLY) to the residual sorry |
| `[Γ₁ : Γ_p(T_p_lower)] = p+1` | **UNPROVEN** (no numeric Γ_p index anywhere) |
| `D =ᵃᵉ Γ_p(A)-FD` (or `D` is a Γ_p(A)-FD) | **UNPROVEN; no such lemma** |
| `⋃_i γ_i•Γ₁-FD` is a FD for `Γ₁∩AΓ₁A⁻¹` | **UNPROVEN** (878 gives this only for `A•Γ_p(A)-FD`) |
| `aedisjoint_pairwise_T_p_family` (SA:1431): p+1 tiles AE-disjoint | PROVEN (only the *disjoint* half of "FD") |

**The entire `Γ_p(α)` trace/transfer engine is built and proven but UNWIRED.** This is the
single most important grep fact: the brief's "engine 1612 fires" presupposes a bridge from `D`
to `Γ_p(A)-FD` that does not exist in the tree.

---

## 2. THE HYPOTHESIS UNDER TEST (brief's W5a): is `D =ᵃᵉ Γ_p(A)-FD`?

**Claim to attack:** the p+1 tiles `{β_i•Γ₁-FD}` form a fundamental domain for
`Γ_p(A) = A⁻¹Γ₁A∩Γ₁`, so `⟨D⟩ pet F G = ∫_{Γ_p(A)-FD} pet F G` and the engine fires.

### Set-level analysis (the det-p is NOT a set obstruction — confirmed)
`β_i` has `det = p`, but the `•` on `ℍ` factors through `PGL₂⁺(ℝ)`, so `β_i` and `β_i/√p`
(det 1) act identically: `β_i•Γ₁-FD` as a SET equals `β̃_i•Γ₁-FD`, `β̃_i ∈ PSL₂(ℝ)`. So the
det-p does not block a set equality. **The brief is right that det is form-level, not set-level.**

### But `Γ_p(A)-FD` is built from Γ₁-translates (det 1), and so is `A•D` — NOT `D` itself
- `Gamma_p_α_fundDomain_PSL A := ⋃_{q∈Γ₁/Γ_p(A)} q.out⁻¹•Γ₁-FD` (FDT:357–362). The tiles are
  translated by `q.out⁻¹ ∈ Γ₁` (det 1). It is a FD for `Γ_p(A)` (isFundamentalDomain…, FDT:860).
- `D = ⋃_i β_i•Γ₁-FD` — tiles translated by `β_i` (det p, NOT in Γ₁, NOT in Γ_p(A)).
- PROVEN (DeltaB:700 `T_p_lower_smul_Hecke_FD_eq_iUnion_tile`):
  `A•D = ⋃_i γ_i•Γ₁-FD`, where `γ_i = T_p_lower_tile_family(i) ∈ Γ₁` (det 1).
- FD-image (FDT:879): `A•Γ_p(A)-FD` is a FD for `Γ₁∩AΓ₁A⁻¹`.

**So the honest reformulation of W5a is: apply A to both sides.** `D =ᵃᵉ Γ_p(A)-FD` ⟺
`A•D =ᵃᵉ A•Γ_p(A)-FD` ⟺ **`⋃_i γ_i•Γ₁-FD` is a FD for `Γ₁∩AΓ₁A⁻¹`** ⟺ the p+1 elements
`{γ_i} ⊂ Γ₁` are a **complete, irredundant set of coset reps for `(Γ₁∩AΓ₁A⁻¹)\Γ₁`** AND
`[Γ₁:Γ₁∩AΓ₁A⁻¹] = p+1`.

### VERDICT on W5a: it is EXACTLY the L1+L2 combinatorial core of `decomposition-tracehecke.md`
The brief's "tile-FD identification" is NOT a free consequence of the proven facts. It REQUIRES:
- (W5a-i) `[Γ₁ : Γ_p(A)] = p+1` — UNPROVEN, no numeric Γ_p index in the tree.
- (W5a-ii) `{γ_i}` are complete coset reps of `(Γ₁∩AΓ₁A⁻¹)\Γ₁` — UNPROVEN. The DISJOINT half is
  proven (SA:1431); the COVERING half (surjectivity / completeness) is the new work.
This is the *same* finite congruence-coset combinatorics as L2 in the trace decomposition —
**bounded-but-substantial (~150–300 LOC), elementary, no analysis, half (distinctness) proven.**

**The brief's hypothesis "W5 reduces to (tile-FD identification + proven engine)" is therefore
TRUE in spirit BUT the tile-FD identification is itself the unbuilt hard core, not a citation.**

---

## 3. W5 sub-lemma decomposition (W5a–W5d)

Granting the honest reformulation, the cleanest route fires the proven engine 1612. Write
`A = glMap(T_p_lower)`, `c_p = slToPslQuot_fiberCard_Gamma_p_α A`, `c_N = slToPslQuot_fiberCard N`.

| Sub-lemma | Statement | Classification | Discharge cite (grep-verified) | LOC |
|---|---|---|---|---|
| **W5a** | `⋃_i γ_i•Γ₁-FD` is a FD for `Γ₁∩AΓ₁A⁻¹` (⟺ `D=ᵃᵉΓ_p(A)-FD` after A); equiv. `{γ_i}` complete reps + `[Γ₁:Γ_p(A)]=p+1` | **API-GAP, the CRUX** | DISJOINT half: `aedisjoint_pairwise_T_p_family` (SA:1431); geometry: DeltaB:700; distinctness half: `adj_upper_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:348), `adj_M_infty_inv_mul_upper_not_mem_Gamma1` (HeckeT_p_Gamma1:378). COVERING + INDEX=p+1: **NONE** | **~150–300** |
| **W5b** | `⟨D⟩ f (g∣A) = ∫_{Γ_p(A)-FD} pet f (g∣A)` (and the `(⟨p⟩f)∣A` side); transfer the integral via W5a | **API-GAP, bounded given W5a** | `IsFundamentalDomain.setIntegral_eq` (mathlib) + `smul_Gamma_p_α_fundDomain_PSL_ae_isFundamentalDomain` (FDT:879) + `setIntegral_iUnion`/`peterssonInner_iUnion_finite_aedisjoint` (PLN:1140); the A-CoV is `peterssonInner_slash_adjoint` (AdjointTheory:770) | **~80–150** |
| **W5c** | fire FDT:1612: `c_p•∫_{Γ_p(A)-FD} pet f (g∣A) = c_N•∫_{Γ₁-FD} pet f (tr_{q₀}(g∣A))`; cancel `c_p` against the matching factor on both balance sides | DISCHARGED-project (engine) + `c_p/c_N` ℂ-scalar algebra | `setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain` (FDT:1612, PROVEN); `slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152) for `hG_slash`; integrability hyps from `aggregate_HeckeFD_measure_hyps` (CF:5233)-pattern + `integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical` (FDT:972) | **~120–200** |
| **W5d** | `tr_{q₀}(g∣A) = T_p g` (via the trace leaf) AND the `det/⟨p⟩` reconciliation: re-fold `c_N•∫_{Γ₁-FD} pet f (T_p g) = petN(f, T_p g)`, then transport `f → ⟨p⟩f` to land both balance sides on `petN((⟨p⟩f)…, …)` | API-GAP (trace leaf) + DISCHARGED weight | trace leaf `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p` (UNBUILT — see `decomposition-tracehecke.md`, ~350–630 LOC); weight `g∣(A·β_i)=p^{k-2}g` via `A·T_p_upper(b)=pI·shiftSL(b)` (DeltaB:456), `A·M_∞=pI·γ'` (DeltaB:483), `slash_diag_scalar` (Nebentypus:794, `f∣(cI)=c^{k-2}f`); `peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero` (SA:273) | **~60–120 + trace-leaf** |

**W5 total (excluding the trace leaf, which is a separate ticket): ~410–770 LOC.**
**With the trace leaf folded in (it appears in W5d): ~760–1400 LOC.**

---

## 4. ≥3 ATTACKS PER SUB-LEMMA (each honestly attempted)

### W5a — `⋃_i γ_i•Γ₁-FD` is a FD for `Γ₁∩AΓ₁A⁻¹` (THE CRUX)

(i) **Direct FD-from-coset-reps attack.** Build `IsFundamentalDomain (Γ₁∩AΓ₁A⁻¹)
(⋃_i γ_i•Γ₁-FD)` from: DISJOINT (SA:1431, PROVEN) + COVERS (every orbit meets it). The
"covers" half = `{γ_i}` surject onto `(Γ₁∩AΓ₁A⁻¹)\Γ₁`. Mathlib `IsFundamentalDomain.iUnion…`
needs a coset-rep family with `⋃ rep•FD` covering. The reps must be proven complete — this is
the unbuilt surjectivity. **~150–250 LOC.** No mathlib lemma computes a diag(p,1)-conjugate
index. (The brief's "L2 bijection" framing is the same object.)

(ii) **Measure-counting attack.** Both `A•D` and `A•Γ_p(A)-FD` are FDs for `Γ₁∩AΓ₁A⁻¹` ⟹ equal
measure ⟹ tile counts equal. BUT `A•D` is only KNOWN to be a FD if W5a already holds — circular.
Counting needs `μ(Γ₁-FD)∈(0,∞)` + AE-disjoint on BOTH sides + the count p+1 from D's side
(`Fintype.card_option=p+1`, free) + the count `[Γ₁:Γ_p(A)]` from the other side (= the unproven
index). Routes through measure theory but still needs the index. **Not decisively better.**

(iii) **Bypass: never identify D with Γ_p(A)-FD; use the per-i family `Γ_p(α_i)` directly.** This
is what CF:291 (`peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q`) + FDT:1198
(`sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN`) were built for: split
`⟨D⟩ = Σ_i ⟨β_i•Γ₁-FD⟩`, lift each `β_i•Γ₁-FD` to `β_i•Γ_p(α_i)-FD` (= `[Γ₁:Γ_p(α_i)]` copies),
apply the per-rep exchange + relIndex collapse, cancel the relIndex (DS 5.5.1(b): index depends
only on the double coset). **THIS IS THE v2-PLAN ROUTE** (`decomposition-adjoint-v2`), and it is
EXACTLY where prior workers ERRED OPTIMISTIC: the per-i `β_i•Γ₁-FD` is a SINGLE tile while the
engine consumes `[Γ₁:Γ_p(α_i)]` tiles; bridging the multiplicity (the
"family-trace bookkeeping") is genuine multi-lemma work, not "relIndex cancels" glue. Learning
`ca13d40b`/`00f97f28` corrected this. So (iii) does NOT make W5a disappear; it relocates it into
a per-i index/multiplicity reconciliation of equal difficulty. **~200–400 LOC, NOT bounded glue.**

**Best framing: (i) — prove `{γ_i}` are complete coset reps once, get `[Γ₁:Γ_p(A)]=p+1` as
`Fintype.card_option`. This is finite/elementary but real (~150–300 LOC).**

### W5b — integral transfer `⟨D⟩ = ∫_{Γ_p(A)-FD}` given W5a

(i) **`IsFundamentalDomain.setIntegral_eq` attack.** Two FDs (D and Γ_p(A)-FD) for the SAME
group + invariant integrand ⟹ equal integrals. Needs the integrand `pet f (g∣A)` to be
`(Γ₁∩AΓ₁A⁻¹)`- (resp. `Γ_p(A)`-) invariant. `g∣A` is `Γ_p(A)`-invariant (FDT:152, PROVEN). The
domain is `A•(stuff)`, so the relevant group is the conjugate one. Bounded GIVEN W5a; the
invariance citation is clean. **~80 LOC.**

(ii) **`integral_iUnion` + per-tile CoV attack.** Split `⟨D⟩ = Σ_i ⟨β_i•Γ₁-FD⟩` (AE-disjoint,
SA:1431) and `∫_{Γ_p(A)-FD} = Σ_q ∫_{q.out⁻¹•Γ₁-FD}` (FDT:357), then match termwise under the
W5a bijection. Avoids the abstract FD-uniqueness but needs the explicit tile↔tile matching (= W5a
again, termwise). **~120 LOC, re-imports W5a.**

(iii) **Skip transfer; keep `⟨D⟩` and prove the balance directly on D.** The balance
`⟨D⟩ f (g∣A) = ⟨D⟩ ((⟨p⟩f)∣A) g` could be attacked by `peterssonInner_slash_adjoint` on each
slot: `⟨D⟩ f (g∣A) = ⟨A•D⟩ (f∣A†) g` (move slot via adjoint, A†=adjugate). Then `A•D = ⋃γ_i•Γ₁-FD`
(DeltaB:700) and `A†=T_p_upper(0)` (SA:273). The RHS similarly. The two reduce to a balance over
`⋃γ_i•Γ₁-FD` with `f∣A†` vs `g` — but `f∣A†` is NOT Γ₁-invariant (det p), so it cannot be folded
back to a single `petN` without the trace bookkeeping. **This is the learning-`ca13d40b`
TARGET-FINAL form: `Σ_i⟨D₁⟩(f∣β_i)g = Σ_i⟨D₁⟩(⟨p⟩f)(g∣β_i)` ⟺ symmetric form — CIRCULAR.**
Confirms W5b-without-W5a routes back to the residual. **Dead as a shortcut.**

### W5c — fire the trace engine FDT:1612

(i) **Direct application attack.** `hF_slash` (F=f, Γ₁-inv): `slash_Gamma1_eq f` (PROVEN).
`hG_slash` (G=g∣A, Γ_p(A)-inv): `slash_α_Gamma_p_α_invariant_cuspForm` (FDT:152, PROVEN). The 3
integrability hyps: `integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical` (FDT:972) + the
per-tile/trace integrability (DeltaB:1666-pattern, `aggregate_HeckeFD_measure_hyps`-style). The
engine then yields `c_p•∫_{Γ_p(A)-FD} = c_N•∫_{Γ₁-FD}(tr)`. **Clean, ~120 LOC, given W5b put the
LHS into `∫_{Γ_p(A)-FD}` form.** This is the part the brief is RIGHT about — once data is over
`Γ_p(A)-FD`, the engine genuinely fires.

(ii) **`c_p/c_N` cancellation attack.** Both balance sides carry `c_p` (engine) and `c_N`
(re-fold to petN). The residual's two `peterssonInner k D` ends carry the SAME `c_N` factor
(CF docstring: "the c_N • fiber factors are identical on both ends and cancel"). `c_p, c_N` are
fixed ℕ → invertible ℂ-scalars. `smul_right_injective`/`nsmul_eq` algebra. **~40 LOC.** No
obstruction — the fiber counts are uniform (FDT fiber_card_uniform, PROVEN).

(iii) **Reverse-engine attack (skip W5b).** Apply the engine in reverse to go from `∫_{Γ₁-FD}(tr)`
directly to `c_p/c_N•∫_{Γ_p(A)-FD}`, then identify `∫_{Γ_p(A)-FD} pet f (g∣A)` with `⟨D⟩`. Same
content as W5b+W5c, reordered. No saving.

**W5c is genuinely BOUNDED and largely DISCHARGED (engine PROVEN) — given W5a/W5b.**

### W5d — `tr(g∣A)=T_p g` + det/⟨p⟩ reconciliation

(i) **Trace-leaf attack.** `tr_{q₀}(g∣A) = T_p g` is `traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p`
— the UNBUILT leaf decomposed in `decomposition-tracehecke.md` (BOUNDED ~350–630 LOC, crux = the
L2 coset bijection = the SAME object as W5a). So W5d's main cost IS the trace leaf, and the trace
leaf's crux = W5a's crux. **W5a and W5d-trace are the same combinatorial fact viewed two ways**
(coset reps for `(Γ₁∩AΓ₁A⁻¹)\Γ₁`). ~350–630 LOC, but shared with W5a.

(ii) **Weight attack (the `det-p^{k-2}` / ⟨p⟩).** `g∣(A·β_i)=p^{k-2}g`: `A·T_p_upper(b)=pI·γ`
(DeltaB:456), `A·M_∞=pI·γ'` (DeltaB:483), both Γ₁-trivial up to central `pI`; `g∣(pI)=p^{k-2}g`
(`slash_diag_scalar`, Nebentypus:794). The `⟨p⟩` on the `f` slot comes from `M_∞=σ_p·A` (the σ_p
is the diamond `⟨p⟩` rep). `peterssonAdj(A)=T_p_upper(0)` (SA:273) realizes DS's `α↦α'`. All
PROVEN; reconciliation is finite ℂ-scalar + diamond-unitary (`diamondOp_petersson_unitary`, used
CF:5508) algebra. **~60–120 LOC, DISCHARGED-from-project.**

(iii) **Diamond-shift bypass.** Note the residual already has `⟨p⟩f` on the LHS slot-1 of the RHS
side. The downstream `petN_heckeT_p_diamond_shift_core` (CF:5489) already handles the `⟨p⟩↔⟨p⟩⁻¹`
unitary shuffle PROVENLY. So W5d's diamond part is essentially DONE downstream; W5d's residual
content is purely (i) the trace identity + (ii) the `p^{k-2}` weight. **No new diamond work.**

**W5d = trace-leaf (shared with W5a) + ~60–120 LOC bounded weight algebra.**

---

## 5. BINDING VERDICT

### Does W5 reduce to (tile-FD identification + proven trace engine + verified weight)?
**YES — that is the correct route.** W5c (engine) is PROVEN. W5d-weight is PROVEN-from-project.
W5b (integral transfer) is bounded mathlib glue GIVEN W5a. The reduction the brief proposes is
mathematically sound and is the right architecture.

### Is W5 therefore BOUNDED?
**BOUNDED — but the "tile-FD identification" (W5a) is itself the unbuilt hard core, NOT a free
citation.** The brief's framing that the engine "then fires" and W5 "reduces to the tile-FD
identification" is CORRECT, but it understates W5a: W5a is not discharged by FDT:879 (which only
covers `A•Γ_p(A)-FD`, not `D`). W5a requires the NEW, finite, elementary, but real proof that the
p+1 elements `{γ_i}⊂Γ₁` are complete coset reps for `(Γ₁∩AΓ₁A⁻¹)\Γ₁` with index p+1. This is the
SAME object as L2 in `decomposition-tracehecke.md` and as the trace leaf's crux.

### THE BINDING NUMBER
- **W5a (crux):** ~150–300 LOC — API-GAP, finite congruence-coset combinatorics, half proven.
- **W5b:** ~80–150 LOC — bounded mathlib glue given W5a.
- **W5c:** ~120–200 LOC — engine PROVEN; integrability + `c_p/c_N` algebra.
- **W5d:** ~60–120 LOC weight (PROVEN-from-project) + the trace leaf (~350–630 LOC, crux SHARED
  with W5a — counts once).
- **W5 total, de-duplicated (W5a and trace-leaf crux shared):** **~700–1100 LOC.**

**This CONFIRMS learning `ca13d40b`'s "400–800 LOC genuine multi-lemma development, NOT bounded
glue"** — and is slightly HIGHER once W5b's transfer and W5c's integrability are counted honestly.
It REFUTES the v2-plan's "BOUNDED assembly over proven engines" optimism (which omitted the
unbuilt W5a/multiplicity bridge).

### VERDICT: **BOUNDED-BUT-SUBSTANTIAL (~700–1100 LOC). NOT OPEN (no hard analysis), NOT free
glue. The crux is W5a — a finite, elementary, real coset-completeness/index fact, NOT analysis.**

> W5 = `heckeT_p_aggregate_peeled_diagonal_balance` reduces, via the brief's route, to:
> **W5a (the tile-FD identification = `{γ_i}` complete coset reps for `(Γ₁∩AΓ₁A⁻¹)\Γ₁`,
> `[Γ₁:Γ_p(A)]=p+1`) + the PROVEN trace engine FDT:1612 (W5c) + PROVEN-from-project weight
> (W5d).** The engine genuinely fires and the weight is verified; the ONLY genuinely-unbuilt
> mathematical content is W5a (≡ the trace leaf's L2), which is FINITE & ELEMENTARY (matrix
> products mod N, (0,1)-entries mod p, `Fin 2`/`ZMod` arithmetic) — no analysis, no deep
> structure — with its DISJOINT and DISTINCTNESS halves already PROVEN. **It is a real ~150–300
> LOC congruence-coset lemma, NOT a multi-week wall, NOT routine glue.**

### REFUTATION of both prior error directions (the brief warned)
- **Over-credit (v2 plan, `decomposition-adjoint-v2`):** claimed leaf2 BOUNDED via relIndex
  cancellation over proven engines. WRONG: it omitted W5a (the `D`↔`Γ_p(A)-FD` identification /
  per-i multiplicity bridge), which is unbuilt. The engine does NOT fire on `D` as-is.
- **Under-credit ("genuinely OPEN, hard analysis"):** WRONG. There is NO hard analysis left. The
  CoV (`peterssonInner_slash_adjoint`), the FD-image (879), the trace engine (1612), the
  measure/integrability, and the weight are ALL PROVEN. W5a is finite, elementary, half-done.
- **CORRECT (this decomposition, matching `ca13d40b`/`00f97f28`):** bounded-but-substantial; one
  finite combinatorial crux (W5a ≡ trace-leaf L2), the rest is proven-engine + glue. ~700–1100.

---

## 6. SKELETONS (type-check-DEFERRED, NOT inserted into the build)

```lean
-- W5a (THE CRUX): the p+1 Γ₁-translates γ_i•Γ₁-FD form a FD for the conjugate group.
-- Equivalent form: {γ_i} is a complete irredundant set of coset reps for (Γ₁∩AΓ₁A⁻¹)\Γ₁.
open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
private theorem iUnion_T_p_lower_tile_family_isFundamentalDomain_conj
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    IsFundamentalDomain
      ((ConjAct.toConjAct
          (GLPos_to_PSL_R_term ⟨(glMap (T_p_lower p hp.pos)), glMap_T_p_lower_det_val_pos p hp.pos⟩) •
        ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R)) : Subgroup PSL(2, ℝ))
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  sorry -- DISJOINT half: aedisjoint_pairwise_T_p_family (SA:1431) [PROVEN]
        -- COVERS half + index = p+1: NEW. {γ_i} complete reps for (Γ₁∩AΓ₁A⁻¹)\Γ₁.
        -- distinctness via adj_upper_inv_mul_upper_not_mem_Gamma1 (HeckeT_p_Gamma1:348),
        -- adj_M_infty_inv_mul_upper_not_mem_Gamma1 (:378) [PROVEN]; surjectivity NEW.

-- Corollary (the brief's W5a as literally stated): D =ᵃᵉ Γ_p(A)-FD.
open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
private theorem aggregate_D_ae_eq_Gamma_p_A_fundDomain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      =ᵐ[μ_hyp] Gamma_p_α_fundDomain_PSL (N := N) (T_p_lower p hp.pos) := by
  sorry -- apply A⁻¹ to W5a's A•D = ⋃γ_i•Γ₁-FD; both FDs for Γ₁∩AΓ₁A⁻¹ ⟹ ae_eq
        -- via IsFundamentalDomain.ae_eq (mathlib) + FDT:879 + DeltaB:700.

-- W5b: integral transfer (bounded given W5a).
open UpperHalfPlane ModularGroup MeasureTheory in
private theorem aggregate_D_petersson_eq_Gamma_p_A_fundDomain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))), …D…)
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) (T_p_lower p hp.pos),
      petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ ∂μ_hyp := by
  sorry -- aggregate_D_ae_eq_Gamma_p_A_fundDomain + setIntegral_congr_set_ae;
        -- or IsFundamentalDomain.setIntegral_eq (g∣A is Γ_p(A)-inv, FDT:152).

-- W5c: fire the PROVEN trace engine (the part the brief is right about).
-- Direct application of setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain
-- (FDT:1612) with α=T_p_lower, F=f, G=g∣A; hF=slash_Gamma1_eq f, hG=slash_α_Gamma_p_α_invariant_cuspForm.

-- W5d: trace identity (= the UNBUILT trace leaf) + weight.
-- traceSlash_Gamma_p_α_T_p_lower_eq_heckeT_p  (see decomposition-tracehecke.md, ~350–630 LOC)
-- + slash_diag_scalar (Nebentypus:794) for the p^{k-2} central weight.

-- W5 = the residual (assembles W5a–W5d through the engine; both slots symmetric).
-- heckeT_p_aggregate_peeled_diagonal_balance  (CF:5391) — the live sorry.
```

---

## 7. ADVERSARIAL ATTACK LOG (each honestly attempted)

- **"Is W5 a SEPARATE lemma from the residual sorry?"** NO. grep: `petN_heckeT_p_RHS_aggregate_eq`
  (CF:5619) reduces by `rw` to `petN_heckeT_p_symmetric_form_doubleCoset` (CF:5400) → residual
  sorry (CF:5412). The chain is CIRCULAR. W5 ≡ `heckeT_p_aggregate_peeled_diagonal_balance`.
- **"Does the engine FDT:1612 fire on `D` directly (brief's premise)?"** NO. The engine consumes
  `∫_{Γ_p(A)-FD}` (det-1 Γ₁-tiles); `D` has det-p `β_i`-tiles. They coincide only after W5a (the
  `D=ᵃᵉΓ_p(A)-FD` identification), which is UNBUILT. grep: engine referenced NOWHERE.
- **"Is `D=ᵃᵉΓ_p(A)-FD` proven (find it)?"** NO. grep for any FD property of `D`/`⋃γ_i•Γ₁-FD` =
  EMPTY. FDT:879 covers ONLY `A•Γ_p(A)-FD`. SA:1431 gives only the DISJOINT half.
- **"Is `[Γ₁:Γ_p(T_p_lower)]=p+1` proven?"** NO. grep: no numeric Γ_p index anywhere; all fiber
  cards are abstract (`slGamma_p_αToGamma1_fiberCard`, `slToPslQuot_fiberCard_Gamma_p_α`).
- **"Is the det-p^{k-2} weight an obstruction?"** NO. It is form-level only; PROVEN via
  DeltaB:456/483 + Nebentypus:794. Set-level, det is invisible (PGL action). W5d.
- **"Is W5a the same as the trace-leaf L2?"** YES. Both are coset reps for `Γ_p(A)` in `Γ₁`
  (one phrased as `(Γ₁∩AΓ₁A⁻¹)\Γ₁`, the other as `Γ_p(A)\Γ₁` — A-conjugate, same index p+1, same
  γ_i). They count ONCE in the LOC.
- **"Could W5 be OPEN (hard analysis)?"** NO. Every analytic ingredient (CoV 770, FD-image 879,
  trace engine 1612, measure/integrability, weight) is PROVEN. The only gap is finite combinatorics
  (W5a). Refutes the "genuinely open" direction.
- **"Could the v2 'relIndex cancels' route close it without W5a?"** NO. That route (per-i
  `Γ_p(α_i)`, CF:291 + FDT:1198) needs to bridge the single tile `β_i•Γ₁-FD` to the
  `[Γ₁:Γ_p(α_i)]`-tile `β_i•Γ_p(α_i)-FD` — the "family-trace multiplicity bookkeeping" that is
  itself unbuilt and of equal difficulty to W5a (learning `ca13d40b`). Refutes the over-credit.

## 8. PROTECTED-STATEMENT / BUILD CHECK
No build run (`lake build`/`lake env lean` not invoked). No edits to the tree. All skeletons in §6
are type-check-DEFERRED (this file only). `heckeT_p_aggregate_peeled_diagonal_balance` (CF:5391),
`heckeT_p_adjoint`, `exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_axiom_clean`,
`miyake_4_6_14_*` — all UNTOUCHED. DS Ex 5.4.4 (p.183) cross-checked against the un-normalized
trace engine FDT:1606–1631 (verbatim). Confirmed vs `decomposition-tracehecke.md` (W5a ≡ L2) and
learnings `ca13d40b`, `00f97f28` (logical equivalence to symmetric form; engine reachable not
dead; family-trace bookkeeping unbuilt).
