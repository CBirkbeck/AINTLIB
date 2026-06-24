# Decomposition — Separation spine (Leaf A) of Wedhorn Thm 8.28(b)

*Produced 2026-06-23 by /develop, source-grounded against the regenerated
`references/wedhorn.txt` (pdftotext of `Wedhorn-Adic_Spaces-1910.05934v1.pdf`) and
verified against the code by `lean_verify` axiom-tracing (NOT memory).*

## Target

The **injective half** of the `IsSheafy` embedding:
`cor_8_32_productRestriction_faithfullyFlat` (RelativePieceKeystone:2342) — for a finite
rational covering `(Uᵢ)` of `X = Spa A`, the map `𝒪_X(X) → ∏ᵢ 𝒪_X(Uᵢ)` is faithfully flat
(hence injective). `lean_verify` ⇒ `sorryAx` (open).

## Wedhorn's actual proof (read at wedhorn.txt:4051–4180, 3504–3517, 3393–3477)

```
Cor 8.32  (∏ faithfully flat)                                    wedhorn.txt:4142
  └─ Prop 8.30  (𝒪_X(V) → 𝒪_X(U) flat,  U ⊆ V rational)         wedhorn.txt:4095
       ├─ Example 6.38  (𝒪_X(V) strongly-noeth Tate;            wedhorn.txt:4099,4103
       │   𝒪_X(U₁)=Â⟨X⟩/(f−X),  𝒪_X(U₂)=Â⟨X⟩/(1−fX))
       ├─ Remark 7.55   (reduce arbitrary U to single-f chain    wedhorn.txt:3504
       │   Spa A ⊇ X₀ ⊇ … ⊇ Xₙ = U;  X₀={1≤x(s/u)} via Cor 7.32 dominating unit)
       └─ Lemma 8.31    (Â⟨X⟩/(f−X), Â⟨X⟩/(1−fX) flat over        wedhorn.txt:4106
            noetherian complete Tate Â)
            └─ Remark 8.29  (µ_M : M⊗_Â Â⟨X⟩ ≅ M⟨X⟩)             wedhorn.txt:4074
                 └─ Prop 6.18  (canonical topology; presentation maps continuous+open)
```

**Crucial source fact:** Wedhorn's flatness proof goes through **Example 6.38 +
Remark 7.55 + Lemma 8.31** — it does **NOT** use `HasLocLiftPowerBounded`, the
Nullstellensatz, or the ring-of-integral-elements correspondence (7.47). IRIE/HasLocLift
enter only as foundational infrastructure for the **presheaf restriction-map construction**
(`restrictionMapHom`), which the headline carries as the instance hypothesis
`[HasLocLiftPowerBounded A]`.

## Project status (verified by `lean_verify`, 2026-06-23)

| Node | Lean decl | Source | Status |
|------|-----------|--------|--------|
| Cor 8.32 | `cor_8_32_productRestriction_faithfullyFlat` (RPK:2342) | 7.53/8.32 | sorryAx (bottoms at L-A1, L-A3) |
| Prop 8.30 | `prop_8_30_restriction_flat` (RPK:2263) | 8.30 | sorryAx (→ L-A1) |
| Prop 8.30 reduction "X=V" | `prop_8_30_remark755_chain` (RPK:2147) via `relativePiece_equiv` (8.16) | 8.30 | **proven** (reduction); residual = L-A1 |
| Prop 8.30 per-step | `prop_8_30_basic_laurent_step_flat` (RPK:1242) | 8.31 (single f) | **AXIOM-CLEAN** ✓ (faithful `presheafValue_flat_of_canonical_faithful`; NO noeth-A₀/CompatiblePlusSubring/IsDomain) |
| Example 6.38 strong-noeth | `presheafValue_isStronglyNoetherian_faithful` (Wedhorn828:2674) | 6.38 | **AXIOM-CLEAN** ✓ (L-A2 DONE; mvRestricted surjection proven) |
| Example 6.38 iso | `example638Plus_equiv` / `unitDatum_quotEquiv` (Example638) | 6.38 | proven |
| per-step continuity (mem_plus) | `mem_plus_of_forall_spa_vle_one` (FaithfulLocLift:337) | 7.10/Hu Thm 3.1 | **continuity sorry ELIMINATED 2026-06-22** (T-SPVAI-4); residual = L-A3 (IRIE) only |

## The THREE residual leaves

### L-A1 — Remark-7.55 geometric chain  (the one genuine FLATNESS residual)
- **Lean:** `prop_8_30_imagePiece_wholeSpace_flat` (RPK:2129) → `prop_8_30_imagePiece_assembled`
  (RPK:2052). `sorryAx`.
- **Source (verbatim, wedhorn.txt:3504–3517):**
  > "Since U is quasi-compact, there exists by Corollary 7.32 a unit u ∈ A× such that
  > |u(x)| < |s(x)| for all x ∈ U. We set X₀ := { x ∈ Spa A ; 1 ≤ x(s/u) } … Define now
  > inductively rational subsets X₁,…,Xₙ of Spa A by Xᵢ := { x ∈ Xᵢ₋₁ ; x(tᵢ/s) ≤ 1 } …
  > Thus we obtain a chain of rational subsets Spa A ⊇ X₀ ⊇ X₁ ⊇ ⋯ ⊇ Xₙ = U."
- **What's built:** X₀'s dominating unit `cor_7_32_dominating_unit` (proven); the per-step
  flatness `prop_8_30_basic_laurent_step_flat` (axiom-clean); the fold
  `restrictionMap_flat_chain` (RestrictionFlatness:894, by `Module.Flat.trans`).
- **What's missing (the leaf):** the inductive chain object `X : ℕ → RationalLocData A`
  with the containments `rationalOpen Xᵢ₊₁ ⊆ rationalOpen Xᵢ`, the LaurentNormalized
  structure per step, and the identifications `presheafValue(X₀) ≅ B` /
  `Xₙ = imagePieceDatum`. ("`laurent_cover_from_dominating_unit` + the inductive chain not
  yet built" — RPK:2257.) **NOT decomposable into one sub-lemma; the theorem IS the
  construction** (~300 lines).
- **Lean ↔ source:** the Lean `imagePieceDatum D E.T E.s` is `U = R(E.T/E.s)`; the chain
  X₀⊇…⊇Xₙ is exactly Remark 7.55's; each `Xᵢ→Xᵢ₋₁` flatness is the per-step (single-f)
  Lemma-8.31 flatness already proven. Faithful.

### L-A3 — IRIE #68  (discharges the `[HasLocLiftPowerBounded A]` LL-bdd hypothesis)
- **Lean:** `presheafValuePlus_isRingOfIntegralElements` (Presheaf:502), 3 fields
  `isOpen`/`isIntegrallyClosed`/`subset_powerBounded`. 3 `sorry`s.
- **Source (verbatim, wedhorn.txt:3404–3405):**
  > "(4) Rings of integral elements of A and rings of integral elements of Â [correspond].
  > Proof. [Hu1] 2.4.3."
- **Decompose (faithful, mirrors Wedhorn 7.47(4) via 7.19):**
  - **L-A3a:** Prop 7.19 (wedhorn.txt:3015) — `C = (A⁺[T/s])^int` (integral closure of
    `A⁺[T/s]` in `A_s`) IS a ring of integral elements (open, integrally closed, ⊆ A_s°).
    The *precompletion* statement.
  - **L-A3b:** Lemma 7.47(4) — completion preserves rings of integral elements
    (`Ĉ ↔ C` under the open-subgroup bijection of Example 5.33). Source = **[Hu1] 2.4.3**
    (`huber1.txt:7467`, German, "Vervollständigung").
- **Role:** discharges the LL-bdd half of `[HasLocLiftPowerBounded A]` —
  `mem_plus → isPowerBounded_of_forall_vle_one_spa_of_complete →
  locLift_divByS_isPowerBounded_faithful` all bottom *solely* here (T-SPVAI-4 made the
  continuity dependency clean). **Off the FLATNESS path; only on the HasLocLift discharge.**
- ⚠️ **Red flag (CLAUDE.md rule 4):** the proof is "by [Hu1] 2.4.3", a German-source
  external cite. If discharging it in Lean needs *substantial* missing topological-group
  infrastructure (open-subgroup ↔ correspondence + integral-closure-commutes-with-
  completion), STOP and treat as a cited external leaf rather than building it.

### L-A4 — LL-unit discharge  (discharges the `[HasLocLiftPowerBounded A]` LL-unit hypothesis)
- **Lean:** `isUnit_canonicalMap_s_faithful` (FaithfulLocLift) routes through the pairFree
  7.52(2) → `exists_spa_point_supp_eq_nonOpen_maxIdeal_of_complete` (Presheaf:2750, sorry).
- **Source:** Prop 7.52(2) (wedhorn.txt:3472) = reformulation of **Prop 7.51**
  (wedhorn.txt:3457): "m closed + ∃v∈Spa, supp v = m", whose proof needs **Prop 7.49**
  (wedhorn.txt:3417, Spa(A/m)≠∅) — Wedhorn's own proof via Lemma 7.45 + Lemma 7.44 +
  retraction 7.1.2 (NOT [Hu]-deferred).
- **Two faithful options:**
  - **(a)** Build Prop 7.49 (Wedhorn 7.45+7.44+7.1.2 — but 7.45 = Leaf #3, itself deep:
    analytic non-open-prime point).
  - **(b)** Reroute: a `hAplus_le_A₀`-free, mem_plus-style supp-construction (mirror the
    T-SPVAI-4 machinery for the `supp ⊇ 𝔪` direction) → makes LL-unit bottom at IRIE
    (L-A3) instead of Prop 7.49, **collapsing the HasLocLift discharge to the single L-A3
    keystone.** Preferred (reuses just-built machinery, no new deep Spa-nonemptiness).
- The clean `≥`-form `exists_spa_point_supp_ge_maxIdeal_of_complete` (Lemma745, axiom-clean)
  is NOT usable: it needs `hAplus_le_A₀ : A⁺ ⊆ A₀`, FALSE for completions.

## Net

- **Flatness path:** done except **L-A1** (Remark-7.55 geometric chain).
- **HasLocLift discharge:** **L-A3** (IRIE, the keystone) + **L-A4** (LL-unit; reroutable
  into L-A3 via option (b)).
- **L-A2** (Example-6.38 strong-noeth) and the per-step flatness are already axiom-clean.

**Suggested order:** L-A1 (self-contained flatness construction, unblocks the injective
half modulo the HasLocLift hypothesis) → L-A3 (IRIE keystone, discharges HasLocLift LL-bdd)
→ L-A4 option (b) (reroute LL-unit into L-A3).
