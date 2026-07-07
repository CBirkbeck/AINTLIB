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

**Sources to acquire** (gate the marked tickets, nothing else): ① Mumford GIT (R3); ② Bosma–Lenstra,
*Complete systems of two addition laws for elliptic curves*, JNT 53 (1995); ③ Lange–Ruppert, Invent.
Math. 79 (1985); (optional ④ Deligne *Formulaire*, LNM 476, cross-check for 1b).

## Leaves (ⓜ mathlib / ⓟ project-done / ⚙ new-provable / ⛔ source-required)

### Part 0 — over the universal atlas

- **T-W7.0a `atlasRing_isDomain`** ⚙ `IsLocalization.isDomain_localization` ⓜ + `Δ ≠ 0` in
  `MvPolynomial (Fin 5) ℤ` (evaluate at `y² = x³ − x`: `Δ = 64 ≠ 0` — beware char-2 traps in the
  evaluation target: use `ℚ`). 1-liner + a small evaluation lemma.
- **T-W7.0b `negHom_U`** ⚙ negation on `projModel` (denominator-free; fixes `O`; infinity chart:
  linear). Includes `negHom_U ≫ π = π`, involution, `zero`-fixing.
- **T-W7.0c `mulHom_U`** ⚙(② ③ acquired first) **Bosma–Lenstra route**: two bidegree-(2,2)
  polynomial law triples `ℓ₁, ℓ₂` for the long Weierstrass cubic; leaves: (c1) each `ℓᵢ` defines a
  morphism on the open complement `Vᵢ` of its exceptional divisor; (c2) `V₁ ∪ V₂ = E_U ×_U E_U`
  (B–L disjointness of exceptional divisors, fibrewise over all fields ⟹ topological cover); (c3)
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

### Part III — canonicity (T-W7b)

- **T-W7.7a rigidity**, split (audit A4): **R1 affine core** ⚙ `Hom_S(X ×_S Y, Z_aff) ≅ Hom_S(Y,
  Z_aff)` from `(pr₂)_*O = O_Y` (= 0i(i5) instantiated); **R2 local factorization** ⚙ proper
  closed-image shrinking ⟹ `h ≡ e` on `A ×_S Y'`, `Y' ⊇ e(S)` open; **R3 globalization** ⛔ the
  passage to all of `A ×_S A` over non-reduced `S` — the reviewer's sketch does NOT close it (their
  own Q6 argument blocks open-neighbourhood ⟹ global). **SOURCE-REQUIRED: Mumford GIT §6.1 verbatim**
  (mechanism unknown: connectedness along which factor / EGA IV §8 noetherian reduction / infinitesimal
  argument). Follow-up F1 filed with the reviewer.
- **T-W7.7 `abelEnrichment_unique`** ⚙(after R3) `h(x,y) = (x +_m y) −_{m'} (x +_{m'} y)` vanishes on
  both axes; rigidity twice ⟹ `m = m'`.

## Parallelization map (owner request: workers can be assigned per lane NOW)

Independent lanes — no shared files, no shared dependencies until the marked joins:

| Lane | Tickets (in order) | Gate | Can start |
|------|--------------------|------|-----------|
| **P0** | T-W7.0a → 0b | none | **NOW** |
| **P1** | T-W7.0c (c1–c6; c3 splits into per-coordinate worker-parallel lemmas) | acquire ②③ | on acquisition |
| **P2** | T-W7.0e → 0f | none | **NOW** |
| **P3** | T-W7.0i (i1–i5) → 1b (b1–b5) | none | **NOW** |
| **P4** | R1 → R2 (state with `π_*O=O` as hypothesis; discharge via 0i later) | none | **NOW** |
| **P5** | T-W7.1a′ + 1a (atlas plumbing) | none | **NOW** |

Joins: **0g** needs P0+P1+P2 · **0h** needs P1 · **1/2/3** need 0g+0h+P3+P5 · **T-W7a milestone**
joins all of P0–P3+P5 · **R3** blocked on GIT (unblocks T-W7b with P4). Suggested file split to keep
workers collision-free: `GroupLawConstruction.lean` (P0/P1), `PointsDictionary.lean` (P2),
`PoleFiltration.lean` (P3), `Rigidity.lean` (P4), `WeierstrassAtlasBundle.lean` (P5).

## Cleanup cadence

`[CLEANUP-W7-1]` after 0g; `[CLEANUP-W7-2]` after 1b; `[CLEANUP-ALL-W7]` before T-W7.6 (milestone);
`[CLEANUP-W7-3]` after T-W7.7.
