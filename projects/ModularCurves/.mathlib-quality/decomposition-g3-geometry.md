# Worker decomposition — the G3 geometry frontier (hfix + T-G3d), KM 2.7.2/2.3

*p0, 2026-07-08 (coordinator v10.27 dispatch). `/develop --decompose` for the two geometry bridges
that remain in the rigidity box after the arithmetic heart (`aut_endo_eq_one`) and `hdeg` landed.
Both bottom out on the **E[N] finite-étale** layer (`N` invertible), currently the sorried
`BB-QF`/`BB-FLAT` of `EllipticCurve/Torsion.lean`. Diagnosis is exhaustive: exact mathlib lemmas +
p2 infra reuse + the single linchpin gate are named, so whoever discharges the torsion-étale layer
can close both immediately.*

## [T-G3h-hfix] — the box's last bridge

**Goal** (in `aut_hom_eq_id_of_fullLevel`, `Moduli/Groupoid.lean`):

    E.torsionι N ≫ ε.left = E.torsionι N

for `N ≥ 3` invertible on `S` (`hinv`), `ε.left = e.hom.hom` the underlying automorphism, given
`hP : P.1 ≫ e.hom.hom = P.1`, `hQ : Q.1 ≫ e.hom.hom = Q.1`, and `hPQ : E.IsNaiveFullLevel N P Q`.
On landing: `aut_trivial_of_fullLevel` is **fully proven modulo the PIC0 data** — the rigidity milestone.

### Reduction to `torsion_hom_ext` + agreement

`hfix = torsion_hom_ext (torsionι ≫ ε.left) (torsionι) (agreement)`, where:

- **[L-ext] `torsion_hom_ext`** (THE GATE): for `N` invertible, two `S`-morphisms
  `f g : E.torsion N ⟶ E.E` agreeing on the level-structure generators (equivalently on all
  geometric `N`-torsion points) are equal. This is **finite-étale descent** for `torsionι`.
- **[L2] agreement** (MINE, uses the proven `endMonHom`): `ε.left` fixes each section `aP+bQ`
  (from `hP`, `hQ` + additivity of `ε` on points), and by `hPQ` these generate `E[N]`.

### Three concrete routes for [L-ext] — all need E[N] finite étale

1. **Reduced-density** (mathlib `ext_of_isDominant_of_isSeparated'`, `Separated.lean:321`):
   `[IsReduced (E.torsion N)]` + `[IsSeparated (E.E ↘ S)]` + a dominant `ι : W ⟶ E.torsion N` +
   agreement ⟹ equal. `IsSeparated (E.E ↘ S) = IsSeparated E.π` is FREE (`IsProper E.π`,
   `Proper.lean:42` `IsProper extends IsSeparated`). Dominant `ι` = the N²-section cover, whose
   scheme-theoretic image is `E[N]` by `isFullLevel_iff_naive` (`LevelStructure/Basic.lean:130`) +
   the `IsFullLevel` divisor = `torsionIdeal`. **Gate**: `IsReduced (E.torsion N)` needs `S` reduced
   AND E[N] étale — fails over a non-reduced base.
2. **Trivialization**: full level ⟹ `∐_{(ℤ/N)²} S ≅ E.torsion N` (the sections split E[N]), then
   morphisms out of a coproduct are determined componentwise (no reducedness). **Gate**: the sections
   are open immersions only if E[N] → S is **étale**; for merely finite-locally-free (p2's
   `torsionSubgroup`) they are closed immersions and E[N] need not split.
3. **Functor-of-points** (p2 `GroupScheme/Subgroup.lean:424` `torsionι_factors_iff`): the universal
   torsion point `u` is fixed by `ε.left`. **Gate**: `IsNaiveFullLevel` controls only GEOMETRIC
   points (`Spec k̄`); lifting to the universal point over `torsionπ N` needs étale descent.

**Linchpin gate (all routes): E[N] → S finite étale for `N` invertible** = KM 2.3.2, i.e.
Torsion.lean `mulByHom_locallyQuasiFinite` (BB-QF, `:sorry`) + BB-FLAT (`:sorry`) ⟹ `[N]` étale ⟹
`torsionπ N` finite étale. p2's `torsionSubgroup N` gives finite locally FREE only (their line-448
note explicitly avoids étaleness), so it does **not** substitute.

## [T-G3d] — `exists_eq_one_add_mulBy_comp_of_fixesTorsion`

**Goal**: `ε` fixes `E[N]` ⟹ `∃ g, ε = 1 + g∘[N]` (KM 2.7.2 proof "ε−1 = g·N"). This is the
**isogeny-quotient universal property**: `ε−1` kills `ker[N] = E[N]`, so it factors through
`[N] : E → E/E[N] ≅ E`.

### Reuse assessment (per coordinator — p2's Layer-B machinery)
- `ForMathlib/SchemeQuotient.lean` provides quotient by a **finite GROUP action** (`SchemeAction G X`,
  `quotient`, `quotientπ`, `quotientπ_hom_ext`) — this is `E/G` for a CONSTANT finite `G`, not
  `E/E[N]` for the subgroup SCHEME in general. It DOES apply in the box's context (full level ⟹ E[N]
  ≅ (ℤ/N)² constant ⟹ `E/E[N] = E/(ℤ/N)²` via translation action), but not for a general base.
- `GroupScheme/Subgroup.lean` `torsionSubgroup N` (E[N] as `FiniteLocallyFreeSubgroup`),
  `torsionι_factors_iff` — the subgroup + divisor structure; the quotient `E/E[N]` and the iso
  `E/E[N] ≅ E` (via `[N]`) are NOT yet built.

**Gate**: the quotient-by-finite-subgroup-SCHEME + the isogeny iso `E/E[N] ≅ E`. Reuse p2's
`SchemeQuotient` glue-data pattern; build the subgroup-scheme quotient on top of it. Infra-scale.

## Status / handoff

Both bridges are **decomposed to a single named gate each**: hfix → `torsion_hom_ext` (E[N] finite
étale, BB-QF/BB-FLAT); T-G3d → the isogeny-quotient (build on p2's `SchemeQuotient`). [L2] agreement
is mine and lands the moment `torsion_hom_ext`'s interface is fixed. The linchpin is the **E[N]
finite-étale layer** — discharging BB-QF/BB-FLAT unblocks hfix directly and feeds T-G3d.
