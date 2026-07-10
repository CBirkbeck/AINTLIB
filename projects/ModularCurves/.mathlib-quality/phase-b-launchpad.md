# CHARTER-FP4 Phase B — launchpad (written at Phase-A close, 2026-07-10)

**Dispatch (coordinator, post-v10.98 ratification):** GO on Phase B, fresh session, full budget.
First act = `/develop --decompose` of **α_univ-descent** (VERBATIM KM quotes per v10.8 — same
protocol as km-71-quotient-quotes.md), then the **representability bijection** → **T-E5c** →
**Y(N) route A + Γ_H**. [OWNER-FLW] boundary as before (fibrewise ⟷ locally-Weierstrass is
owner-reserved; consume as pin; cite, never duplicate).

## Source for the quote file
`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (LOCAL ONLY, gitignored; symlink
`ln -s ../AINTLIB/refs refs` if absent). **Offset: pdf page = printed page + 11.** The α_univ
descent is in the KM 4.7 proof (printed p. 114 ⟹ pdf p. 125): the auxiliary level structure
`α_univ` on the universal curve descends through `E → E/G` because it is `G`-invariant — read the
surrounding pages (KM 4.7.0–4.7.2, printed ~113–116) and quote verbatim into
`.mathlib-quality/km-47-alpha-univ-quotes.md`.

## Phase-A interface (all FULLY AXIOM-CLEAN, [propext, Classical.choice, Quot.sound])
- `ModularCurves.RouteA.exists_ellipticCurveGeom_quotient_of_globalModel` (EngineDescent.lean):
  free `G` ↷ affine `X`, `IsCurveAction σ C σE`, global model `φ : C.E ≅ projModel W₀` (+ hW₀
  elliptic, hπφ, hzeroφ compats) ⟹ `∃ C' : EllipticCurveGeom (σ.quotient V hVs hVa), ∃ q : C.E ⟶
  C'.E, IsPullback q C.π C'.π (σ.quotientπ …) ∧ C.zero ≫ q = σ.quotientπ … ≫ C'.zero`.
- `locallyWeierstrass_quotientπ_of_globalModel`, `smoothOfRelativeDimension_of_locallyWeierstrass`
  (T-A3 wired), `lw_chart_at` + the discharge lemmas, `isPullback_quotientπ`,
  `exists_quotient_π_zero` — all in EngineDescent.lean.
- The [a1] seam: `ModuliProblem.simulSchemeActionTotal` (+ `_π`, `_zero`, `_isPullback`,
  `free_simulSchemeAction`) — produces the `IsCurveAction` from a moduli-problem action.
- GH staging: `GammaHRepresentability.lean` — `gammaH_relativelyRepresentable`,
  `gammaHNaive_toQuotient`, `gammaH_representable_of_rigid` (gated on the engine ⟸ now open);
  the corrected T-H4/T-H6 statements per the B2 repoint (km-71-quotient-quotes.md).

## Phase-B shape (from the charter + v10.98)
1. **α_univ descent**: the auxiliary rigid level structure on `C.E` descends along `q : C.E ⟶
   C'.E` to a level structure on `C'`; G-invariance of α_univ ⟹ the descended structure is
   well-defined; KM's simultaneous-representability argument. Decompose per /develop (statement,
   sketch, mathlib lemmas, sources with verbatim quotes, generality).
2. **Representability bijection**: `𝕸(𝒫, δ)/G ≅ 𝕸(𝒫)`-style: points of the quotient = P-structures
   (KM 4.7.1); wires the engine's `C'` into the moduli functor.
3. **T-E5c**: the amended `representable_iff` consuming 1+2.
4. **Applications**: Y(N) route A + Γ_H (`gammaH_representable_of_rigid` etc.).

## Standing constraints
Never `maxHeartbeats` (split into private toplevel lemmas — the per-declaration-budget
architecture of Phase A is the proven pattern; opaque-shape lemmas for anything touching
`Γ(X,⊤)`-instance-carrying terms). Commit-early with explicit pathspecs. B2 protocol for any
statement changes. `2>&1` never `2>/dev/null`. RR sole standing assumable.
