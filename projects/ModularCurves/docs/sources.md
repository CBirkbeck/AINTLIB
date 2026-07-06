# Sources — Modular Curves (Katz–Mazur arithmetic-moduli programme)

Reference library for the project. **All books/PDFs live in `refs/ModularCurves/`**
(gitignored, local-only, reachable via the `refs → ../AINTLIB/refs` symlink) — never in
the repo. This file records what we have, what each source is *for*, and what is missing.

Priorities: `[P0]` = spine of the current plan · `[P1]` = active secondary · `[P2]` = later phase.

## Acquired (in `refs/ModularCurves/`)

| File | Source | Role | Pri |
|------|--------|------|-----|
| `katz-mazur-arithmetic-moduli-FULL.pdf` | **Katz–Mazur**, *Arithmetic Moduli of Elliptic Curves* (AM-108, 1985) — **FULL TEXT (acquired 2026-07-06)**; scanned, renders fine in session tooling (TOC verified: Ch. 1–14) | THE primary reference, now complete: Ch. 2 (group structure 2.1, Weierstrass families 2.2, [N] 2.3, pairings 2.8), Ch. 3 (the four moduli problems), Ch. 4 (representability), Ch. 5+ — all ⧗KM quote-gates are now source-unblocked. Supersedes the preview for everything | P0 |
| `preview-9781400881710_A26691730.pdf` | **Katz–Mazur** preview (frontmatter + Intro + Ch. 1 §§1.1–1.9, book pp. i–39) | Superseded by the full text; keep for page-number cross-checks of the Ch. 1 quotes already mined | P2 |
| `modcurvesnotes.pdf` | **D. Loeffler**, *Modular Curves* lecture notes (21 pp.) | The concise spine actually driving Phase 1–2: §3.3 EC over base schemes + Tate normal form + explicit `Y₁(N)`; §3.4 smoothness; §3.6 quotients & `Y₀(N)`; §3.7 Ell/R + KM representability theorem; §3.8 general level structures `P_H`; §4 Katz forms + Tate curve. Verbatim-quotable throughout | P0 |
| `buzzard-tcc-20260326.pdf` | **K. Buzzard**, *Formalizing Fermat* Lecture 8 slides (TCC course, 2026-03-26) | The endgame spec: p. 33 defines `Y(ρ̄_N)` requirements (functor on ℚ-schemes, representations-with-pairing, smooth geometrically irreducible); pp. 34–39 Moret–Bailly application (black-boxed) | P0 |
| `Haruzo Hida - Geometric Modular Forms and Elliptic Curves (2001…).pdf` | **Hida**, *GME* (371 pp., full text) | Full-text secondary for the KM-missing chapters until full KM lands: EC over schemes, moduli & level structures, geometric modular forms. Use for cross-referenced quotes where the KM preview runs out | P1 |
| `padicpropMFMS.pdf` | **Katz**, *p-adic properties of modular schemes and modular forms* (Antwerp III, 1972; 122 pp., full) | Moduli schemes M_n & the q-expansion principle (Ch. 1); later: p-adic modular forms, canonical subgroup (Phase 3+) | P1 |
| `[…] Faltings, Chai - Degeneration of abelian varieties (1990).djvu` | **Faltings–Chai** | Compactification/degeneration theory — Phase 4 (X(N) over ℤ, cusps). ⚠ **DJVU: unreadable by the session tooling — replace with PDF if/when Phase 4 starts** | P2 |
| `[…] Hida - p-Adic Automorphic Forms on Shimura Varieties (2004).pdf` | **Hida**, *PAF* | Shimura-variety generalisations — far horizon; the FLT Shimura-surface material is black-boxed anyway | P2 |

## Wanted (please drop into `refs/ModularCurves/`)

1. ~~**Katz–Mazur, FULL TEXT**~~ — **ACQUIRED 2026-07-06** (`katz-mazur-arithmetic-moduli-FULL.pdf`).
   WS-C and the KM-gated parts of WS-A/E are no longer PENDING-SOURCE; per-ticket ⧗KM
   quote-gates (T-A4 KM 2.2.5, T-A6 KM 2.1, T-B2 KM 1.12 reconciliation, T-D* Ch. 1
   cross-checks) can now be satisfied by verbatim quotes. Historical note: all planning
   to date used the 54-page preview (Ch. 1 §§1.1–1.9 only) for KM-verbatim material;
   Ch. 2+ routes were sourced from Hida GME (full) + Loeffler instead, as recorded in
   each ticket.
2. *(Phase 4, optional now)* Deligne–Rapoport, *Les schémas de modules de courbes
   elliptiques* (LNM 349) — generalized elliptic curves, cusps.
3. *(nice-to-have)* Conrad, *Arithmetic moduli of generalized elliptic curves* — modern
   DR/KM exposition.

## Existing Lean infrastructure — reuse first (survey 2026-07-05)

**mathlib** (pin `11b908e5cdd9`): Weierstrass curves over rings + division polynomials +
`VariableChange` + `IsElliptic`; group law over fields; morphism classes
(smooth/étale/proper/flat/finite + `finrank`); ZMT; fibres; `GrpObj` in `Over S`;
fppf/fpqc precoverages; fibered categories + `Pseudofunctor.IsStack`;
`CyclotomicCharacter`; `Field.absoluteGaloisGroup`. **Absent**: everything
scheme-theoretic about elliptic curves (see `.mathlib-quality/plan.md` inventory).

**AINTLIB**: HasseWeil (field-level Weil pairing, `E[N] ≅ (ℤ/N)²` alg. closed, Tate
modules, dual isogenies, formal groups — fibre anchors); NagellLutz (`Universal.lean`
universal Weierstrass curve over `ℤ[A₁..A₆]`; division polynomials are a mathlib fork —
use mathlib's); LeanModularForms (congruence subgroups, Hecke, analytic side; no
geometric `Γ\ℍ` object exists anywhere in the repo).

## Bibliography (cite keys used in Lean docstrings & tickets)

- **[KM]** N. Katz, B. Mazur. *Arithmetic Moduli of Elliptic Curves.* Ann. of Math.
  Studies 108, Princeton, 1985.
- **[Loe]** D. Loeffler. *Modular Curves.* Lecture notes (TCC-style course), 21 pp.
- **[Buz-L8]** K. Buzzard. *Formalizing Fermat*, Lecture 8 slides, 2026-03-26 (in
  `ImperialCollegeLondon/FLT`, `2026_EPSRC_TCC_course/20260326.pdf`).
- **[Hida-GME]** H. Hida. *Geometric Modular Forms and Elliptic Curves.* World
  Scientific, 2001.
- **[Katz-Antwerp]** N. Katz. *p-adic properties of modular schemes and modular forms.*
  In: Modular Functions of One Variable III, LNM 350, Springer, 1973.
- **[Sil]** J. Silverman. *The Arithmetic of Elliptic Curves.* GTM 106 (for the
  field-level dictionary: III.3, III.6, III.8; used fibrewise only).
- **[FC]** G. Faltings, C.-L. Chai. *Degeneration of Abelian Varieties.* Ergebnisse 22,
  Springer, 1990.
- **[Hida-PAF]** H. Hida. *p-Adic Automorphic Forms on Shimura Varieties.* Springer, 2004.
- **[DR]** P. Deligne, M. Rapoport. *Les schémas de modules de courbes elliptiques.*
  LNM 349, 1973. *(not yet in refs/)*
