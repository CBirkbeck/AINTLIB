# Source map — Thm 8.28(b) sheafiness, the 4 residual leaves

All references are **local** in this `references/` dir (PDFs are git-ignored; the `*.txt`
extractions are grep-able with line numbers). Page/line pointers are into the `pdftotext`
extractions unless noted.

## Reference inventory (corrected mapping — verified from Wedhorn's bibliography, NOT memory)

Wedhorn bibliography (`wedhorn.txt:5725-5745`):
- **[Hu1]** = R. Huber, *Bewertungsspektrum und rigide Geometrie*, Regensburger Math. Schriften 23 (1993)
  — the **Habilitation** (the "private copy" Wedhorn was sent). 328 pp, German, OCR text layer.
  FILE: `huber1-bewertungsspektrum.pdf` / `huber1.txt`. Downloaded from Huber's own server
  (`www2.math.uni-wuppertal.de/~huber/preprints/`). **This is the comprehensive source — it
  subsumes [Hu2].**
- **[Hu2]** = R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477. On GDZ
  (PPN GDZPPN002441314; viewer `gdz.sub.uni-goettingen.de/id/PPN266833020_0212`, page-image only,
  no direct PDF). **Content is in [Hu1] §2.x (Cont(A) theory) — not separately required.**
- **[Hu3]** = R. Huber, *A generalization of formal schemes and rigid analytic varieties*,
  Math. Z. 217 (1994). FILE: `huber-formal-rigid-1994.pdf` / `huber1994.txt` (English).
- **[Hu4]** = Étale Cohomology book (1996) — not needed for these leaves.
- Wedhorn: `Wedhorn-Adic_Spaces-1910.05934v1.pdf` / `wedhorn.txt`.
- BGR (Bosch–Güntzer–Remmert), Henkel (open-mapping w/ zero-unit-sequence) — for leaf #1.

## The headline

`isSheafy_of_stronglyNoetherian_828b` (`WedhornCechAcyclicity.lean:12856`) builds green;
`IsSheafy = embedding (= inducing ∧ injective) ∧ gluing`. Reduces to 4 leaf-sorries:

### Leaf #1 — topological inducing (Wedhorn **Prop 6.18**, Banach-OMT)
- Lean: `productRestrictionSub_isInducing_tate` (`StructureSheaf.lean:1384`, bare `sorry`).
- Wedhorn: **Thm 6.16** (`wedhorn.txt:2597`, Banach for rings with units→0 — *landed sorry-free*
  as `wedhorn_6_16_of_topNilpUnit`), **Prop 6.17** (`wedhorn.txt:2610`, ideals closed),
  **Prop 6.18** (`wedhorn.txt:2615`, the inducing statement). This is the remaining in-project MATH.
- Sources: Wedhorn 6.16-6.18 + BGR (Banach) + Henkel (units→0 open-mapping, `Henkel-...pdf`).

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

### Leaf #4 — power-bounded from Spa-bound (the flatness LL-bdd input, [Hu2] 3.3-flavour)
- Lean: `isPowerBounded_of_forall_vle_one_spa_of_complete` (`FaithfulLocLift.lean:92`).
- Wedhorn: the σ(A⁺)-dense / Cont(A) characterization remark (`wedhorn.txt:3168-3175`,
  "Proof. [Hu2] Lemma 3.3").
- Source: **[Hu1]** Cont(A) density/specialization theory (subsumes [Hu2] §3).

### Already CLOSED (not leaves anymore)
- Wedhorn **7.48** = [Hu2] Prop 3.9 (`wedhorn.txt:3570`) — `comap_coeRingHom_injOn_spa`, proven.
- Wedhorn **7.54** = [Hu3] Lemma 2.6 (`wedhorn.txt:3647`) — proven (in `huber1994.txt`).
- The Spa-QC keystone; the noeth-A₀ defect + false `B⁺⊆B₀` (this session's ROIE migration).
