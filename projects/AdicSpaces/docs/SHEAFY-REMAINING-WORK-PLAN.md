# Wedhorn 8.28(b) — complete remaining-work plan

*Produced 2026-06-15. Synthesises (1) Wedhorn's proof structure (source PDF
`Wedhorn-Adic_Spaces-1910.05934v1.pdf`, read directly), (2) the prior plans
(`WEDHORN-8.28b-PROOFMAP.md` — Wedhorn-faithful node tree, **stale on status**;
`SHEAFY-FEASIBILITY-MAP.md` — verified leaf-set 2026-06-14), and (3) the live repo
state (`lake build` green, 3188 jobs; `git` `516de9a` on branch `faithful-LL-pairfree`).*

`wedhorn.txt` is absent; citations are statement-no. + PDF page (the CLAUDE.md `/tmp`
path is stale — the PDF is in the repo root).

---

## 0. Where we are

`ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b` (WedhornCechAcyclicity:13458)
is **fully wired** (`:= ⟨embedding, gluing⟩`) and type-checks; it rests on `sorryAx`
solely through the leaves below. Wedhorn's framing (Remark 8.20 / Prop A.4): a sheaf of
**complete topological** rings = sheaf of rings (separation + gluing) + the canonical map
to the product is a **topological embedding**. The repo's `IsSheafy` mirrors this:

```
isSheafy_of_stronglyNoetherian_828b
├── embedding = cor_8_32_productRestrictionSub_isEmbedding  = ⟨isInducing, injective⟩
│   ├── injective  ── Cor 8.32 (faithfully flat) ── Prop 8.30 flat ──► LEAF A
│   └── isInducing ── Prop 6.18 open-mapping (Remark 8.20) ─────────► LEAF B
└── gluing    = lemma_8_34_gluing ── every_rational_cover_is_OXAcyclic ─► LEAF C
```

**This session (2026-06-15) closed the keystone that gated Leaf A** — the faithful
`HasLocLiftPowerBounded` for completions (K1), now pair-free (no `IsDomain`, no
`CompatiblePlusSubring`), resting on exactly two honest Wedhorn leaves (A2, A3 below).
Committed `516de9a`.

---

## 1. The leaves (current status)

### LEAF A — separation / flatness  (Prop 8.30 → Cor 8.32 injective)
Target: `prop_8_30_imagePiece_wholeSpace_flat` (RelativePieceKeystone:1384, `sorry`) —
whole-space flatness `B → 𝒪_B(im E)` over `B = presheafValue D`, via Wedhorn **Remark 7.55**
(p.70). The "X=V" reduction (`prop_8_30_remark755_chain`) and per-step engine
(`prop_8_30_basic_laurent_step_flat`) are **proven**.

- **K1 — faithful (LL) for `B`: ✅ DONE this session** (`hasLocLiftPowerBounded_faithful`,
  WCA; pair-free). Rests only on A2 + A3.
- **A1 — the Remark-7.55 chain construction** (the remaining flatness content; NOW
  UNBLOCKED by K1). NO new math; ~250 intricate lines:
  - **A1a** widen the per-step engine to **arbitrary `f`**. `prop_8_30_basic_laurent_step_flat`
    requires `hD'_T_pb : D'.T ⊆ E.P.A₀` (generators in ring-of-def) — TOO NARROW (the
    chain's `s·u⁻¹`, `tⱼ/s` need not be in `A₀`). Align with the proven arbitrary-`f`
    `lemma_8_31_fSubX_flat`/`_oneSubfX_flat` (Wedhorn828:824/753) via the relative Example
    6.38 iso. (Reviewer's exact instruction; faithful (LL)-for-`B` discharges the iso's
    `hLocLift_B` encumbrance.)
  - **A1b** the chain object `X : ℕ → RationalLocData B`: `X₀ = {1≤x(W.s/u)}` (step 0
    **DONE**: `remark755_dominating_unit_over_presheafValue`), `Xᵢ = Xᵢ₋₁ ∩ {x(tᵢ)≤x(W.s)}`
    (`interSamePair`+`unitDatum`/`coUnitDatum`), maintaining the `LaurentNormalized`/
    composition invariant `restrictionMap_flat_chain` needs.
  - **A1c** the fold (`restrictionMap_flat_chain`, proven) + the `presheafValue(X₀-whole)≅B`
    and `Xₙ = imagePieceDatum` identifications → close the sorry.
- **A2 — integral criterion** `isPowerBounded_of_forall_vle_one_spa_of_complete`
  (WCA:11508, `sorry`). = Wedhorn **7.52(1) = Prop 7.18(1) = [Hu2] Lemma 3.3**. **EXTERNAL**
  (Wedhorn defers to Huber's book). Stays a documented leaf unless [Hu2] 3.3 is formalised
  as a separate effort.
- **A3 — non-open Prop 7.51(2)** `exists_spa_point_supp_eq_nonOpen_maxIdeal_of_complete`
  (Presheaf:2710, `sorry`; open case PROVEN this session). Wedhorn **7.51 → Prop 7.49**:
  `𝔪` closed (proven) ⇒ `A/𝔪` nonzero Hausdorff Tate ⇒ `Spa(A/𝔪)≠∅` (Prop 7.49) ⇒ pull
  back. DEEP but in-Wedhorn: needs **Prop 7.49** (Spa-nonemptiness; repo's 7.45 is
  pair-based) + the **quotient-affinoid structure** on `A/𝔪` (`A/𝔪` IS Tate by
  `IsTateRing.quotient`, but its plus-subring/canonical valuation must be built).

### LEAF B — inducing / topological embedding  (Prop 6.18 OMT)
Target: `productRestrictionSub_isInducing_tate` (StructureSheaf:1384, **bare `sorry`**) —
`IsInducing (productRestrictionSub A C)`, the "complete topological rings" strictness.
= Wedhorn **Prop 6.18** open-mapping (p.50, *"Proof. Missing"* — external, [BGR]/Banach-OMT).
- **B1** the σ-compact-free OMT **core landed** (`wedhorn_6_16_of_topNilpUnit`, memory).
  Remaining = the **equalizer route** (reviewer Q4): `E` = equalizer subring of `∏ 𝒪(Uᵢ)`;
  prove `E` closed (⇒ complete); algebraic surjection `𝒪(U) ↠ E`; apply the OMT to that map
  (NOT the full product) ⇒ homeomorphism ⇒ inducing. Reviewer: **no separate Pettis-lift**
  if the OMT is the Tate/Baire theorem. The FEASIBILITY-MAP flagged Pettis-lift as a
  missing-infra risk; the equalizer route is the way around it.

### LEAF C — gluing / acyclicity  (Lemma 8.34 Čech)
Target: `lemma_8_34_gluing` ── `every_rational_cover_is_OXAcyclic` (WCA:13328). Per Wedhorn
**Prop A.4** the whole sheaf+`H^q=0` reduces to rational-cover acyclicity (Lemma 8.34).
- **C1** the Čech residuals (`TateAcyclicityResiduals.lean` ×9, `LaurentRefinementAcyclic`:160):
  the Laurent-tree induction (A.3(3)), dominating-unit σ-walk (8.34(ii)), and the
  **R2-transport** for general (non-whole-space) bases (instantiate the absolute
  `every_rational_cover_is_OXAcyclic` at `B := 𝒪(U)`, transport via `Spa(B)≅U` = Prop 8.2 +
  Rmk 8.4 + Prop 8.16). Memory: whole-space chain (7.54+8.34+A.3) is COMPLETE sorry-free;
  the live residual is R2-transport + the diffuse `TateAcyclicityResiduals` leaves. K4 =
  grind, no single deep keystone; mirrors machinery already mostly built.

---

## 2. Classification of the remaining work

| Item | Kind | Size | Risk | Note |
|---|---|---|---|---|
| **A1** Remark-7.55 chain | in-repo construction | large (~250 ln) | low (no new math; parts proven) | step 0 done; biggest single buildable win |
| **C1** Čech residuals | in-repo grind | medium (~10 residuals) | low–med (combinatorial) | machinery mostly built; R2-transport the key one |
| **A3** Prop 7.49 + quotient-affinoid | in-Wedhorn, new infra | large | med (Tate-field valuation) | Wedhorn's own route; substantial new structure |
| **B1** Prop 6.18 OMT (equalizer) | in-Wedhorn + external core | medium–large | med (was Pettis-lift risk; equalizer route avoids) | OMT core landed |
| **A2** [Hu2] 3.3 integral criterion | **EXTERNAL** | — | — | Huber's book; leave documented OR separate formalisation project |

**External / "Proof Missing" leaves** (faithful, NOT drift — Wedhorn's own cites): A2
([Hu2] 3.3), Prop 6.18 core (in B1). These bottom out at Huber/[BGR]; they stay as precise
documented leaves unless separately formalised.

---

## 3. Recommended order

1. **A1 — Remark-7.55 chain** (close `prop_8_30_imagePiece_wholeSpace_flat`). Biggest
   in-repo-completable win, advances embedding/injective. Sub-order: A1a (arbitrary-`f`
   per-step) → A1b (chain object, step 0 done) → A1c (fold + connection).
2. **C1 — Čech residuals** (close Leaf C gluing). Grind; start with R2-transport.
3. **A3 — Prop 7.49 + quotient-affinoid** (eliminate the non-open 7.51(2) leaf; removes one
   of the faithful (LL)'s two sorries). New infra, but Wedhorn's route.
4. **B1 — Prop 6.18 equalizer-OMT** (close Leaf B inducing). Assess the equalizer route;
   OMT core landed.
5. **A2 — [Hu2] 3.3**: leave as a documented external leaf (or scope a separate effort to
   formalise the integral criterion). The headline will rest on `sorryAx` through A2 until
   then — faithful, not drift.

After A1 + C1 + A3 + B1, the headline rests only on the external A2 (+ Prop 6.18 core),
i.e. on Wedhorn's own external citations — the faithful end state.
