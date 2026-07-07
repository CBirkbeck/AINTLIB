# T-W7 — constructive group-scheme structure (v2: reviewer reply integrated, adversarially audited)

**Planned:** beastmode-A 2026-07-07 (v1); **v2 2026-07-07** after the expert reply
(`.mathlib-quality/expert-review/2026-07-07-tw7/{brief,reply,integration}.md` — integration.md holds
the full adversarial audit). **Scope:** full `GrpObj` + canonicity, every hard bit planned to the
leaf; the ONE remaining source-required leaf is rigidity-globalization (R3, canonicity-only).

## Sharp goal

Discharge `abelEnrichment_exists` (GroupLaw.lean:74): construct `GrpObj (Over.mk G.π)` for any
`EllipticCurveGeom G` over any `S` (milestone **T-W7a**), then canonicity `abelEnrichment_unique`
(milestone **T-W7b**, off the critical path to `E[N]`/Drinfeld/`Y(N)`).

## Design (post-reply, audited)

Construct once over the universal integral atlas `U = Spec R`, `R = ℤ[a₁..a₆][Δ⁻¹]` (domain);
axioms over `U` by **evaluation at the generic point** (a single `L`-point lying in every nonempty
open — all degeneracy loci vanish at `η`); descend to any `S` by base change + gluing along a bundled
Weierstrass atlas. Overlap agreement = **comparison theorem** (pointed iso of projModels = variable
change — the dependency the reviewer missed, caught in audit A1) + **global VC-equivariance** of
`m_U`. `π_*O = O` is proved **uniformly per-ring** (2-chart computation, universality by
instantiation — **BB-COHBC retired**); rigidity consumes it for canonicity.

**Sources — ALL ACQUIRED 2026-07-07** (local `refs/ModularCurves/`, verbatim quotes with locators in
`tw7-source-quotes.md`): ① Mumford GIT ✓ (djvu+pdf, text layer — §6.1 + Cor 6.2–6.6 transcribed);
② Bosma–Lenstra JNT 53 (1995) ✓ (author copy, Lenstra's Leiden archive; OCR done); ③ Lange–Ruppert
Invent. Math. 79 (1985) ✓ (GDZ scan); ④ Mumford *Abelian Varieties* ✓ (scan, backup for field case).
**No source-required leaves remain**; the only scope caveat is noetherian (see T-W7.8).

## Leaves (ⓜ mathlib / ⓟ project-done / ⚙ new-provable / ⛔ source-required)

### Part 0 — over the universal atlas

- **T-W7.0a `atlasRing_isDomain`** ⚙ `IsLocalization.isDomain_localization` ⓜ + `Δ ≠ 0` in
  `MvPolynomial (Fin 5) ℤ` (evaluate at `y² = x³ − x`: `Δ = 64 ≠ 0` — beware char-2 traps in the
  evaluation target: use `ℚ`). 1-liner + a small evaluation lemma.
- **T-W7.0b `negHom_U`** ⚙ negation on `projModel` (denominator-free; fixes `O`; infinity chart:
  linear). Includes `negHom_U ≫ π = π`, involution, `zero`-fixing.
- **T-W7.0c `mulHom_U`** ⚙ **Bosma–Lenstra route, now concrete** (quotes: B–L Thm 1/Thm 2 +
  "lines y=0, z=0" + universality-over-rings, `tw7-source-quotes.md`): take the two (2,2)-laws of
  the lines **`Z=0`** (exceptional ⟺ `P₁−P₂ ∈ E∩{Z=0} = {O}` ⟺ diagonal) and **`Y=0`**
  (exceptional ⟺ `P₁−P₂ ∈ E∩{Y=0}`); disjoint over every field since `O = (0:1:0) ∉ {Y=0}`.
  Explicit polynomials: B–L §5 (transcribe from the PDF at implementation; verify by CAS before
  Lean). Leaves: (c1) each `ℓᵢ` a morphism on the open complement `Vᵢ` of its exceptional divisor;
  (c2) `V₁ ∪ V₂ = E_U ×_U E_U` (fibrewise disjointness over all fields ⟹ topological cover); (c3)
  `ℓ₁ = ℓ₂` on `V₁ ∩ V₂` (polynomial identity mod the two curve relations — `linear_combination`
  with precomputed cofactors, split per coordinate; NO maxHeartbeats); (c4) glue
  (`Scheme.Cover.glueMorphisms` ⓜ); (c5) lands on the curve + over `U` (identities mod relations);
  (c6) restriction to the affine secant open = mathlib `addX`/`addY` formulas (feeds 0g and 0h).
- **T-W7.0e `E_U^n` integral** ⚙ route: "smooth over integral base + geometrically integral fibres ⟹
  integral" (check mathlib at implementation; else the specialized chart/generic-fibre fallback —
  both sketched in reply §Q4).
- **T-W7.0f points dictionary** ⚙ over any field `L`: points of `projModel W` valued in `L` =
  `W.toAffine.Point` (chart casework `D₊(Y)/D₊(Z)`; nonsingularity from `Δ` unit ⓜ-adjacent). Plus:
  the generic-point inclusion `Spec κ(η) ⟶ E_U^n` is dominant (`fromSpecResidueField` ⓜ + closure of
  `{η}` = ⊤).
- **T-W7.0g atlas group axioms** ⚙ each axiom = two morphisms `E_U^n ⟶ E_U`; equal ⟸
  (`ext_of_isDominant` ⓜ; source reduced by 0e, target separated) agreement at `η` ⟸ 0f dictionary +
  0c(c6) + mathlib `Affine.Point.instAddCommGroup` over `L = κ(η)` (`add_assoc`, `add_comm`,
  `add_zero`, `neg_add_cancel`). **Audit A5: purely pointwise over `L`; no field-level addition
  morphism needed.**
- **T-W7.0h global VC-equivariance** ⚙ `m_{C•W} ∘ (φ_C × φ_C) = φ_C ∘ m_W` as morphisms of
  projModels, proven over the universal VC-base `R ⊗ ℤ[u^±, r, s, t]` (still a domain — same
  generic-point method as 0g; affine cocycle ⓟ supplies the `η`-evaluation). Reviewer caveat #2
  upgraded to a leaf.
- **T-W7.0i pole filtration + global sections** ⚙ (shared foundation; audit A3): on the 2-chart
  model (`A` free ⓜ `CoordinateRing`-basis; `B = R[t][s]/(monic cubic)` free; `A_y` normal-form
  basis, one element per pole order): (i1) `F_n` filtration via the ideal `(s)` of `O` on `D(u)`;
  (i2) `F₀ = R`, `F₂ = R⊕Rx`, `F₃ = R⊕Rx⊕Ry` free; (i3) **`Γ(projModel W, O) ≅ R` for EVERY
  ring** (equalizer computation; `x²y^{-1}` = the `H¹` witness excluded); (i4) `E∖O` scheme-dense in
  `projModel` (`s` nonzerodivisor via McCoy); (i5) sheafify: `π_*O = O_S` for every locally-
  Weierstrass family, **universally by instantiation** (`W.map`; base-change compat ⓟ
  `isPullback_projModelBaseChange`).

### Part I — descent to general `E/S` (existence)

- **T-W7.1a′ bundled atlas** ⚙ extract `WeierstrassAtlas`-structure (indexed affine opens + curves +
  pointed isos) from the `LocallyWeierstrass` predicate by choice (reviewer caveat #3).
- **T-W7.1a charts = base change of `E_U`** ⚙ classifying map via localization universal property
  (`Δ ↦` unit); `projModel(W_i) = E_U ×_U —` ⓟ.
- **T-W7.1b comparison theorem** ⚙ (audit A1 — NEW, on the existence path): a pointed iso of
  projective Weierstrass models over any ring is induced by a unique `VariableChange`. Leaves: (b1)
  pointed iso preserves `E∖O` ⟹ ring iso `Φ` of affine coordinate rings; (b2) `Φ` preserves `F_n`
  (0i; intrinsic via the section's ideal sheaf); (b3) extract `(u,r,s,t)`: `Φ(x') = αx+β`,
  `Φ(y') = γy+δx+ε`, units `α,γ`; matching relations ⟹ `α³ = γ²`, `u := γ/α`; (b4) affine
  determines projective (0i(i4) + separatedness); (b5) uniqueness of the VC.
- **T-W7.1 `negHom` / T-W7.2 `mulHom` over `S`** ⚙ per chart = base change of 0b/0c via 1a; overlap
  agreement: transition = VC (1b) + equivariance (0h, base-changed); glue (`glueMorphisms` ⓜ over the
  pullback cover of `E ×_S E`).
- **T-W7.3 axioms over `S`** ⚙ each = base change of the universal identity (0g) per chart;
  `Cover.hom_ext` ⓜ. No flatness needed (audit #10).
- **T-W7.6 assemble = MILESTONE T-W7a** ⚙ `MonObj`/`GrpObj`/`IsCommMonObj` packaging;
  `abelEnrichment_exists`. **No rigidity, no cohomology, no source gaps anywhere above.**

### Part III — canonicity (T-W7b) — **R3 RESOLVED: GIT §6.1 transcribed** (`tw7-source-quotes.md`)

The globalization mechanism the reviewer's sketch was missing is now sourced verbatim (GIT p. 115,
case-2 proof): nilpotents are handled by **Artinian thickenings + Krull intersection**, not density.
GIT Ch. 6 convention: **locally noetherian** schemes; Prop 6.1 needs **S connected** — both honest
hypotheses (components of loc.-noeth. are clopen ⟹ componentwise application is fine).

- **T-W7.7a rigidity** (GIT Prop 6.1, cases 1–2 only — our `X = E` has the zero section, so the
  sectionless case 3 / fppf descent is NOT needed):
  - **R1 one-point/Artinian case** ⚙ (GIT case 1): `η := f∘e`; `f = η∘p` topologically; the sheaf
    map `O_Y → f_*O_X ≅ η_*(p_*O_X) ≅ η_*O_S` makes `η` a scheme morphism. The input
    `p_*O_X = O_S` over the Artinian base is **0i(i3) instantiated at the Artinian ring** — no
    cohomology. (Hypothesis note: we replace GIT's fibrewise `H⁰(X_s) = κ(s)` by universal
    O-connectedness-by-instantiation, which is what 0i supplies and makes case 1 immediate.)
  - **R2 thickening ⟹ neighbourhood** ⚙ (GIT case 2, first half): `Z := (f, η∘p)⁻¹(Δ)` the
    equalizer closed subscheme (target separated); if `Z ⊇ p⁻¹(t)` set-theoretically then R1 over
    every Artin subscheme `T ⊆ S` at `t` gives `Z ⊇ p⁻¹(T)` scheme-theoretically ⟹ `I_Z ⊆
    ⋂_n m_t^n·O_X` along the fibre ⟹ `I_Z = 0` near it (**Krull intersection**, noetherian local —
    mathlib name to verify at implementation) ⟹ coherence + `p` closed ⟹ `Z ⊇ p⁻¹(U₀)`, `U₀ ∋ t`
    open.
  - **R3 clopen + connected** ⚙ (GIT case 2, second half): `U₁ := {t : p⁻¹(t) ⊆ Z} = S ∖ p(X−Z)`
    closed (`p` flat ⟹ open map; `Z` closed) and open (R2) ⟹ `S` connected ⟹ `U₁ = S` ⟹ `Z = X`.
- **Corollary chain** ⚙ (transcribed): **C1** = Cor 6.2 (`f_s = g_s` at one point ⟹ `f = (η∘p)·g`,
  via 6.1 on `f·g⁻¹`); **C2** = Cor 6.3 (`f(x,y) = g(x)·h(y)`; connectedness runs along `Y`; needs
  `E` connected when `S` is — small leaf: flat proper surjective + connected fibres + `S` connected);
  **C3** = Cor 6.4 (pointed ⟹ homomorphism: apply C2 to `f∘μ`); **C4** = Cor 6.6 (**uniqueness**:
  apply C3 to `1_X` with the two group laws on domain and image).
- **T-W7.7 `abelEnrichment_unique`** ⚙ = C4 packaged for `EllipticCurve S` — **over locally
  noetherian `S`** (state as `abelEnrichment_unique_of_locallyNoetherian` alongside the general
  statement; do NOT change the existing statement).
- **T-W7.8 arbitrary-`S` upgrade** (NEW, genuine infra, LOW priority): extend canonicity from
  locally-noetherian to arbitrary `S` via EGA IV §8 spreading-out (FC Rem. 1.2(a) names exactly this
  vehicle): `(E, e, m, m')` of finite presentation descend to a f.g. `ℤ`-subalgebra; equality
  descends. Needs Hom-spreading-out along filtered colimits — **absent from mathlib** (watch the
  noetherian-approximation work). Gates only the fully-general `abelEnrichment_unique`; the moduli
  programme lives in the locally-noetherian world (confirm with reviewer — follow-up F1′).

## Parallelization map (owner request: workers can be assigned per lane NOW)

Independent lanes — no shared files, no shared dependencies until the marked joins:

| Lane | Tickets (in order) | Gate | Can start |
|------|--------------------|------|-----------|
| **P0** | T-W7.0a → 0b | none | **NOW** |
| **P1** | T-W7.0c (c1–c6; c3 splits into per-coordinate worker-parallel lemmas) | none (B–L acquired ✓) | **NOW** |
| **P2** | T-W7.0e → 0f | none | **NOW** |
| **P3** | T-W7.0i (i1–i5) → 1b (b1–b5) | none | **NOW** |
| **P4** | R1 → R2 → R3 → C1 → C2 → C3 → C4 (all GIT-transcribed; state with `π_*O=O` as hypothesis; discharge via 0i later) | none (GIT acquired ✓) | **NOW** |
| **P5** | T-W7.1a′ + 1a (atlas plumbing) | none | **NOW** |

**All six lanes are now unblocked** — every lane can take a worker immediately. Joins: **0g** needs
P0+P1+P2 · **0h** needs P1 · **1/2/3** need 0g+0h+P3+P5 · **T-W7a milestone** joins P0–P3+P5 ·
**T-W7b** joins P4+P3 (+T-W7.6); only the arbitrary-`S` polish T-W7.8 remains gated (mathlib
spreading-out infra). Suggested file split to keep workers collision-free:
`GroupLawConstruction.lean` (P0/P1), `PointsDictionary.lean` (P2), `PoleFiltration.lean` (P3),
`Rigidity.lean` (P4), `WeierstrassAtlasBundle.lean` (P5).

## Cleanup cadence

`[CLEANUP-W7-1]` after 0g; `[CLEANUP-W7-2]` after 1b; `[CLEANUP-ALL-W7]` before T-W7.6 (milestone);
`[CLEANUP-W7-3]` after T-W7.7.
