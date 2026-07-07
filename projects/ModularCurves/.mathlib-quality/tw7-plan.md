# T-W7 — constructive group-scheme structure (`/develop` full decomposition, no deferrals)

**Planned:** beastmode-A 2026-07-07. **Scope:** full `GrpObj` + canonicity, **every subtlety and
black box planned to the leaf** (owner: "do not defer any hard bits"). Genuinely-opaque leaves are
routed to `/expert-review` (questions in §"Expert-review queue").

## Sharp goal + design principle

Discharge `abelEnrichment_exists` (GroupLaw.lean:74): construct `GrpObj (Over.mk G.π)` for any
`EllipticCurveGeom G` over any `S`. Downstream (`mulBy`/[N], `pointAddCommGroup`, `baseChange`) is
already derived from `grp`.

**Design principle (load-bearing, decided after the FC source check):** construct the group law
**once over the universal integral atlas** `U = weierstrassAtlas = Spec R`, `R = ℤ[a₁..a₆][Δ⁻¹]`,
then obtain the group law on **every** `E/S` by **base change + gluing** via the invariance cocycle.
Consequences:
- The only genuinely new *construction* is `mulHom_U`/`negHom_U` over `R` (Part 0).
- **All axioms** (assoc/comm/unit/inverse) are proven **once over `R`** by reduction to the generic
  fibre (a field, where mathlib supplies the group law), then base-change to all `S` (a morphism
  identity is stable under base change and checkable on the chart cover).
- The affine cocycle (`addX_smul`/`slope_smul`/`negY_smul`, DONE) is used precisely to check that the
  per-chart base-changes of `mulHom_U` **agree on overlaps** for the gluing.

## Infrastructure ledger (verified against mathlib)

| Need | Status |
|---|---|
| `GrpObj`/`MonObj`, cartesian-monoidal `Over S` (product = pullback) | mathlib (`Monoidal.Grp_`, `cartesianMonoidalCategoryOver`) |
| **density**: reduced source, separated target, dominant `ι`, agree on `ι` ⇒ equal | mathlib **`ext_of_isDominant`** / `ext_of_isDominant_of_isSeparated'` |
| **glue morphisms** on an open cover agreeing on overlaps; `hom_ext` | mathlib **`Scheme.Cover.glueMorphisms`** / `Cover.hom_ext` / `glueMorphismsOverOfLocallyDirected` |
| rational-map / partial-map with dense domain | mathlib **`Scheme.RationalMap`/`PartialMap`** |
| affine formulas + `equation_add`/`nonsingular_add`; **field group law** `Affine.Point.instAddCommGroup` | mathlib |
| `addX_smul`/`slope_smul`/`negY_smul` + `pointEquiv` (variableChange-invariance) | **DONE** |
| `LocallyWeierstrass`+`baseChange`, `projModel`, `isPullback_projModelBaseChange`, `projModelZero_baseChange`, `universalEllipticCurve` | **DONE** |
| `IsDomain (Localization.Away Δ (MvPolynomial (Fin 5) ℤ))` | mathlib (`Localization` of domain) — T-W7.0a |
| **`p_*O_E = O_S`** (proper, geom-connected-reduced fibres) / cohomology & base change / Stein | **GAP — no mathlib infra** (BB-COHBC). Crux black box inside rigidity. |
| **rigidity lemma** over an arbitrary base (GIT §6.1) | **GAP** — build it (needs the above) |
| **`mulHom_U` as a scheme morphism** from the formulas | **GAP — the construction crux** |

## Full decomposition (leaves marked ⓜ mathlib / ⓟ project-done / ⚙ new-provable / ⛔ gap / 🧠 expert)

### Part 0 — the group law over the universal atlas (all math lives here)

- **T-W7.0a `atlasRing_isDomain`** ⚙ `instance : IsDomain WeierstrassAtlasRing`.
  `Localization.Away Δ` of the domain `MvPolynomial (Fin 5) ℤ`. *Subtlety*: need `Δ ≠ 0` in
  `MvPolynomial` so the localization isn't the zero ring — true (`Δ` is a nonzero polynomial). **1-liner.**

- **T-W7.0b `negHom_U`** ⚙ `E_U ⟶ E_U`. `negY` is denominator-free ⇒ a morphism on the affine chart;
  fixes `O`. *Subtlety*: define it globally on `projModel` (affine chart + point at infinity — `negY`
  extends since `[-1]` is a linear automorphism of the projective model). **Tractable.**

- **T-W7.0c `mulHom_U`** 🧠 `pullback (projModelπ) (projModelπ) ⟶ E_U`. **THE construction crux.**
  Two candidate routes — *expert-review Q1 to choose*:
  - **(chord-tangent-as-total-morphism)** the "third intersection point of the line `PQ` with the
    cubic" is given by *total* projective/resultant formulas (no equality case-split), and
    `P +_U Q = neg(third(P,Q))`. Avoids the affine case-explosion; needs the projective/`Jacobian`
    resultant formulas (partly in mathlib `WeierstrassCurve.Jacobian`?).
  - **(affine-cover-and-glue)** cover `E_U ×_R E_U` by `V_secant = {x₁≠x₂}` (secant formula),
    the tangent locus, and the `O`/`-P` loci (via a coordinate change moving the point), define `mul`
    by the regular formula on each, glue with `glueMorphisms`. *Subtleties*: (i) proving the opens
    **cover** `E_U ×_R E_U` incl. the diagonal, `O`, and the anti-diagonal `{Q=-P}`; (ii) at `O` use
    the projective chart; (iii) overlaps agree — a polynomial identity.
  - *Either way, subtle enough to warrant expert input on the cleanest formalizable construction.*

- **T-W7.0d `mulHom_U` lands on the curve / is over `R`** ⚙ `mulHom_U ≫ projModelπ = fst ≫ projModelπ`
  and image satisfies the Weierstrass equation. From `equation_add`/`nonsingular_add` ⓜ + the
  construction. *Subtlety*: `nonsingular_add`'s hypothesis `¬(x₁=x₂ ∧ y₁=negY x₂ y₂)` is exactly the
  non-degenerate locus — must match the cover of T-W7.0c.

- **T-W7.0e `E_U` powers are integral** ⚙ `IsIntegral (E_U ×_R E_U ×_R E_U)` (and pairs). *Subtleties*:
  (i) `E_U` smooth over the **domain** `R` ⇒ reduced; (ii) elliptic-curve fibres are **geometrically
  integral** (smooth proper geom-connected genus-1) ⇒ `E_U` irreducible; (iii) fibre products of
  geom-integral smooth `R`-schemes over an irreducible base are integral. Need mathlib lemmas for
  "smooth over reduced ⇒ reduced" and "irreducible base + geom-irreducible fibres ⇒ irreducible" —
  **check availability; possible ⚙ sub-lemmas.** *expert-review Q4 (exact statements).*

- **T-W7.0f generic-fibre identification** 🧠 `mulHom_U`, restricted to the generic fibre
  `E_{U,K} = E_U ×_R Spec K` (`K = Frac R`), **equals** the field-level addition of
  `WeierstrassCurve.Affine.Point` over `K`. *Subtlety*: this is the bridge from the *scheme* `mulHom_U`
  to mathlib's *field* `Point.add` — needs: the generic fibre's points ↔ `Point`, and the two
  agree on the non-degenerate locus (both `= (addX,addY)`) + at `O`/degenerate by continuity. *This
  bridge is the second-subtlest leaf — expert-review Q4.*

- **T-W7.0g atlas group axioms** ⚙ `mulHom_U` is associative/commutative and `zero_U` is a two-sided
  unit with `negHom_U` inverse, **as morphism identities over `R`**. *Route (now fully grounded)*: each
  axiom is an equality of two morphisms `E_U^n ⟶ E_U`; they agree on the generic fibre (T-W7.0f +
  mathlib `Point.instAddCommGroup` `add_assoc`/`add_comm`/`add_zero`/`add_left_neg` over `K`); `E_U^n`
  is integral (T-W7.0e, so the generic-point inclusion is **dominant** and `E_U^n` is **reduced**),
  `E_U` is separated ⇒ **`ext_of_isDominant`** ⓜ ⇒ equal over `R`. *No rigidity, no `ℤ[ε]` identity.*

### Part I — descent to a general `EllipticCurveGeom G/S`

- **T-W7.1a chart = base change of `E_U`** ⚙ for each `LocallyWeierstrass` chart `(U_i, W_i, e_i)`:
  the classifying ring map `ℤ[a..][Δ⁻¹] → Γ(U_i)` (`Xⱼ ↦ W_i.aⱼ`, well-defined since `W_i.Δ` is a
  unit = `IsElliptic`) makes `projModel(W_i) = E_U ×_U (classifying)`; compose with the witness iso
  `pullback(π, U_i.ι) ≅ projModel(W_i)`. *Subtlety*: the localization universal property (needs
  `Δ ↦ unit`); functoriality `projModel(W.map φ) = projModel(W) ×_ φ` = `isPullback_projModelBaseChange`
  ⓟ.

- **T-W7.1 `negHom`** ⚙ glue the per-chart `(base change of negHom_U)` via `negY_smul` (overlaps agree)
  with `glueMorphisms`. **T-W7.2 `mulHom`** ⚙ likewise, glue `(base change of mulHom_U)` via
  `addX_smul`/`slope_smul` (the cocycle checks the two chart-classifying-maps' base-changed muls agree
  on `U_i ∩ U_j`, related by a `variableChange`). **T-W7.3 axioms for `G`**: each axiom holds on each
  chart (base change of T-W7.0g ⓜ-stable) ⇒ holds on `G` (`Cover.hom_ext` ⓜ). *Subtlety*: the
  base-change stability of an associativity morphism identity — `pullback`/`baseChange` functoriality.

- **T-W7.6 assemble** ⚙ package as `MonObj`/`GrpObj`/`IsCommMonObj`; `abelEnrichment_exists G :=
  ⟨{…, grp := grpObj G,…}, rfl⟩`. **MILESTONE — retires T-A6 existence; depends on NO rigidity.**

### Part III — canonicity (the genuine rigidity + cohomology black boxes; NOT deferred)

- **T-W7.7a-i `properPushforwardStructureSheaf`** ⛔🧠 `p_*O_E = O_S` for `E/S` (proper, smooth,
  geom-connected genus-1). **mathlib GAP** (no cohomology & base change / Stein). Sub-route options —
  *expert-review Q2*: (a) full "cohomology and base change" (Grauert; large — BB-COHBC); (b) an
  **elementary genus-1 argument** via the explicit `projModel` (`H⁰(ℙ¹-bundle-ish)`)/the `|O|`
  linear system — possibly much smaller; (c) reduce to the universal `E_U/U` (integral) + base change,
  as with the axioms — *does `p_*O = O` base-change? Yes if flat + the fibrewise `H⁰ = k` is constant
  (Grauert), so this still needs the fibre statement.* **Plan both (b) and the BB-COHBC fallback.**

- **T-W7.7a-ii `rigidityLemma`** 🧠 (GIT §6.1, over arbitrary base). Given T-W7.7a-i + proper
  `X ×_S Y → Y`, "constant along the `e`-axis ⇒ factors through `Y`". *Proof (to transcribe from a
  readable source — GIT §6.1 not in refs; Katz–Mazur 2.1 / Hida GME cite it — expert-review Q3):*
  take affine `V ∋ z₀`; `p_Y(f⁻¹(Z∖V))` closed missing `y₀` ⇒ open `W ∋ y₀` with `X×W ⊆ f⁻¹(V)`;
  `f|_{X×W}` to affine `V` is constant on the proper connected reduced fibres (`p_*O=O`) ⇒ factors
  through `W`; spread out / connectedness of `Y`. *Subtleties*: proper pushforward of closed sets
  ⓜ?; "morphism to affine constant on `p_*O=O` fibres factors" (the Stein core) ⚙/⛔.

- **T-W7.7 `abelEnrichment_unique`** ⚙ two group structures `m, m'` with the same zero: `id : (E,m) →
  (E,m')` is pointed ⇒ homomorphism (T-W7.7a-ii applied to `m'(m⁻¹×m⁻¹)…` / the standard corollary
  "pointed morphism of abelian schemes is a homomorphism") ⇒ `m = m'`, over **arbitrary** `S`.
  *Subtlety*: deriving "pointed ⇒ homomorphism" from the raw rigidity lemma (the standard two-line
  corollary — transcribe).

## Dependency graph

```
DONE ── T-W7.0a domain
        T-W7.0b negHom_U ─┐
        T-W7.0c mulHom_U ─┤ (🧠 Q1)
        T-W7.0d on-curve  ┤
        T-W7.0e integral ─┤ (Q4)      ┌ T-W7.1 negHom ┐
        T-W7.0f generic ══╪ (🧠 Q4)   ├ T-W7.2 mulHom ┼ T-W7.3 axioms ─ T-W7.6 assemble ▸ EXISTENCE ✔
        T-W7.0g axioms  ══�┘           └ T-W7.1a chart=bc┘        (no rigidity)
                          (via ext_of_isDominant ⓜ)
   T-W7.7a-i p_*O=O (⛔🧠 Q2, BB-COHBC/elementary) ─ T-W7.7a-ii rigidity (🧠 Q3) ─ T-W7.7 canonicity ✔
```
- **Existence path uses NO rigidity** — the big de-risk.
- **Canonicity path is fully planned** (not deferred): its two hard leaves are `p_*O=O` (Q2) and the
  rigidity proof (Q3); both routed to expert-review with concrete sub-routes.

## Expert-review queue — BRIEF WRITTEN

**Brief filed 2026-07-07** (topic-scoped): `projects/ModularCurves/REVIEW_BRIEF-tw7-group-law.md`
(dated copy + `state.md` under `.mathlib-quality/expert-review/2026-07-07-tw7/`). Send to a senior
arithmetic geometer; integrate the reply with `/expert-review --reply`. **Why a brief and not a
transcription:** GIT (the canonical rigidity source) is not in `refs/`; FC only *cites* GIT 6.1; KM
and Hida GME are image-only scans (no text layer to quote-mine). Source-faithfulness forbids inventing
the GIT proof from memory, so the two genuinely-opaque leaves (Q2, Q3) go to the reviewer; the
construction/design leaves (Q1, Q4–Q6) go too, since the best *formalizable* route is a design call.

- **Q1** (→ T-W7.0c) — cleanest construction of the **multiplication morphism** `E_U ×_R E_U → E_U`
  over the *domain* `R`: chord-tangent-via-resultant (total) vs. affine-cover-and-glue; `O` and the
  anti-diagonal; does the secant rational map extend across `{x₁=x₂}`.
- **Q2** (→ T-W7.7a-i) — is `p_*O_E = O_S` obtainable **elementarily** for a `projModel` genus-1 curve
  (explicit `H⁰` / the section + ampleness of `O`) avoiding cohomology-and-base-change, or is BB-COHBC
  unavoidable? Does it base-change from `E_U/U`, and with what flatness/constancy input?
- **Q3** (→ T-W7.7a-ii) — formalization-friendly statement + proof of the **rigidity lemma** (GIT §6.1)
  over an arbitrary base + "pointed ⇒ homomorphism"; which ingredient is the real obstruction; **may
  the base be assumed reduced/normal without loss for our canonicity application** (would drop the
  arbitrary-base requirement entirely).
- **Q4** (→ T-W7.0e/0f) — (a) the **generic-fibre bridge** `mulHom_U|_{E_{U,K}} = Affine.Point.add`
  (scheme-mul ↔ field-`Point.add`), cleanest statement; (b) minimal hypotheses for **`E_U^n` integral**.
- **Q5** (→ T-W7.0g/3) — **soundness of reduce-to-universal**: axioms as morphism identities over the
  integral atlas, obtained over arbitrary non-reduced `S` by base change + gluing, no reducedness of
  `S`. Pitfalls (classifying map non-flat; charts failing to glue)?
- **Q6** (→ T-W7.7) — **alternative to rigidity for canonicity**: construction-level uniqueness (`m`
  the unique morphism restricting to chord-tangent on a dense open; flat `E×_S E`, closed graph);
  survives over non-reduced `S`?

**Plan status after the reply:** Q2/Q3 answers convert T-W7.7a-i/-ii from ⛔ to transcribed leaves (or
Q3(b)/Q6 may excise the arbitrary-base rigidity lemma from the critical path); Q1 fixes the T-W7.0c
construction route; Q4/Q5 confirm the atlas-axiom mechanics. **Nothing in the existence path (→ T-W7.6
milestone) is blocked on the reply** — it can start now; the reply de-risks the construction route and
unblocks canonicity.

## Cleanup cadence

New file `EllipticCurve/GroupLawConstruction.lean`. `[CLEANUP-W7-1]` after T-W7.0g; `[CLEANUP-W7-2]`
after T-W7.3; `[CLEANUP-ALL-W7]` before T-W7.6 (existence milestone); `[CLEANUP-W7-3]` after T-W7.7.
