# Source map — Thm 8.28(b) sheafiness, the 4 residual leaves

All references are **local** in this `references/` dir (PDFs are git-ignored; the `*.txt`
extractions are grep-able with line numbers). Page/line pointers are into the `pdftotext`
extractions unless noted.

## Reference inventory (corrected mapping — verified from Wedhorn's bibliography, NOT memory)

Wedhorn bibliography (`wedhorn.txt:5725-5745`):
- **[Hu1]** = R. Huber, *Bewertungsspektrum und rigide Geometrie*, Regensburger Math. Schriften 23 (1993)
  — the **Habilitation** (the "private copy" Wedhorn was sent). 328 pp, German, OCR text layer.
  FILE: `huber1-bewertungsspektrum.pdf` / `huber1.txt`. Downloaded from Huber's own server
  (`www2.math.uni-wuppertal.de/~huber/preprints/`). The comprehensive Spv/Cont(A) source.
- **[Hu2]** = R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477. **IN HAND** (2026-06-19):
  FILE `huber2-continuous-valuations.pdf` / `huber2.txt` (OCR), from Conrad's perfectoid-seminar mirror
  (`virtualmath1.stanford.edu/~conrad/Perfseminar/refs/Hubercontval.pdf`). **§3 "Continuous valuations
  of f-adic rings" (`huber2.txt:573+`) carries Lemma 3.3 (= Wedhorn 7.18) directly — do NOT assume
  [Hu1] "subsumes" it; the specific σ/τ membership bijection is [Hu2] 3.3, verified there, not located
  in [Hu1] by grep.** Lemma 3.3(i) (`huber2.txt:624-627`) = σ/τ inverse bijection; (ii) density;
  (iii) Tate+noeth converse. Definition of "ring of integral elements" + "affinoid ring" + Spa: `:716-723`.
- **[Hu3]** = R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994). FILE: `huber-formal-rigid-1994.pdf` / `huber1994.txt` (English).
- **[Hu4]** = Étale Cohomology book (1996) — not needed for these leaves.
- Wedhorn: `Wedhorn-Adic_Spaces-1910.05934v1.pdf` / `wedhorn.txt`.
- BGR (Bosch–Güntzer–Remmert), Henkel (open-mapping w/ zero-unit-sequence) — for leaf #1.

## The headline

`isSheafy_of_stronglyNoetherian_828b` (`WedhornCechAcyclicity.lean:12856`) builds green;
`IsSheafy = embedding (= inducing ∧ injective) ∧ gluing`. Reduces to 4 leaf-sorries:

### Leaf #1 — topological inducing via the equalizer + the landed σ-compact-free OMT (NOT 6.18)
- Lean: `productRestrictionSub_isInducing_tate` (`StructureSheaf.lean:1384`, bare `sorry`).
- Route (reviewer Q2, 2026-06-19): corestrict `ρ : R → ∏ᵢ 𝒪_X(Uᵢ)` to the closed equalizer
  `E = ker(overlap-diff)`; `ρ̃ : R → E` bijective (injectivity ∧ gluing = Leaf C); apply
  **`wedhorn_6_16_of_topNilpUnit`** (WedhornBanachTheorem:408, σ-compact-FREE — do NOT use the
  σ-compact `isOpenMap_of_completeSpace_of_countablyGenerated`, false for Tate R) → `ρ̃` homeo →
  inducing. **Prop 6.18 is UNNECESSARY** for this application. The pattern is already implemented at
  module level (`_sub_lemma_L4_3_strict_via_closed_image`); T-L1 instances it on the closed equalizer
  (closedness from `sectionEqualizer_isClosed`, NOT module-finiteness/6.18-noetherian).
- Wedhorn: **Thm 6.16** (= BGR §3.7.2/1, "Proof Missing"; landed sorry-free as `wedhorn_6_16_of_topNilpUnit`).
- Note: T-L1c is GATED on Leaf C (gluing) — `ρ̃` surjective ⟺ the gluing axiom.

### Leaf #2 — `(presheafValue D)⁺ = Ĉ` is a ring of integral elements (Wedhorn **7.47(4)**)
- Lean: `presheafValuePlus_isRingOfIntegralElements` 3 fields (`Presheaf.lean:505-507`).
- Wedhorn: **Lemma 7.47** (`wedhorn.txt:3557`) "(4) Rings of integral elements of A ↔ of Â.
  Proof. [Hu1] 2.4.3."
- Source: **[Hu1] §2.4.3** (`huber1.txt:7467`; §2.4 "Affinoide Ringe / Ganzheitsringe" begins 7434;
  2.4.1 = def of Ganzheitsring = ring of integral elements; 2.4.3 = the completion correspondence,
  "Vervollständigung" at 7477). German.

### Leaf #3 — analytic Spa-point of a non-open prime (Wedhorn **7.45 + 7.41 + Rem 4.12**)
- Lean: `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` (`Presheaf.lean:2785`, bare `sorry`).
- Wedhorn: **Prop 7.41** (`wedhorn.txt:3438`, height-1 x ∈ Cont(A)ᵃ ⟹ x(a)≤1 on A°),
  **Lemma 7.45** (`wedhorn.txt:3487`, complete affinoid non-open prime ⟹ analytic point),
  Remark 4.12 (height-1 vertical generalization).
- Source: **[Hu1]** Cont(A) / height-1 valuation-spectrum theory (`huber1.txt:272+`).

### Leaf #4 — power-bounded from Spa-bound (the flatness LL-bdd input) = Wedhorn 7.52(1)/7.18(1)
- Lean: `isPowerBounded_of_forall_vle_one_spa_of_complete` (`FaithfulLocLift.lean:85`).
- Wedhorn: **Prop 7.52(1)** (`wedhorn.txt:3619`, "|f(x)|≤1 ∀x∈Spa A iff f∈A⁺") = **Prop 7.18(1)**
  (`wedhorn.txt:3161`, "Proof. [Hu2] Lemma 3.3"); + Def 7.14(1) `A⁺ ⊆ A°`. ℂ_p red flag WITHDRAWN
  (this is the bijection 7.18(1), NOT the noetherian *density* converse 7.18(3)).
- Source: **[Hu2] Lemma 3.3(i)**, p.466 (`huber2.txt:624-627`); proof `:633-658` **hypothesis-free
  (no [IsDomain]/noeth/Tate)** — uses a minimal prime of `G[a⁻¹]` + a dominating valuation ring.
  Genuine cited external leaf (NOT a trivial in-repo wrapper: the in-repo
  `isIntegral_of_forall_continuous_valuation_le_one` is [IsDomain]-gated + has a 7.22 continuity sorry;
  case-(b) `presheafValue D'` is a non-domain). Decision (user): sourced [Hu2], leaf parked-and-cited.

### Already CLOSED (not leaves anymore)
- Wedhorn **7.48** = [Hu2] Prop 3.9 (`wedhorn.txt:3570`) — `comap_coeRingHom_injOn_spa`, proven.
- Wedhorn **7.54** = [Hu3] Lemma 2.6 (`wedhorn.txt:3647`) — proven (in `huber1994.txt`).
- The Spa-QC keystone; the noeth-A₀ defect + false `B⁺⊆B₀` (this session's ROIE migration).
