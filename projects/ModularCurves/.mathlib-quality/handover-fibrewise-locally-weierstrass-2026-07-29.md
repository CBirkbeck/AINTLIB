# Handover: fibrewise elliptic versus locally Weierstrass

Date: 2026-07-29

This is the authoritative handover for the abstract
`FibrewiseElliptic` versus `LocallyWeierstrass` comparison. It records the
main-tree reconciliation, the axiom-clean proof frontier, and the next concrete
Lean work. Do not reconstruct the campaign from the old stacked branches.

## 1. Repository state

- Worktree:
  `/Users/mcu22seu/Documents/GitHub/aintlib-mc-fibrewise`
- Remote: `https://github.com/CBirkbeck/AINTLIB.git`
- Integration branch:
  `codex/fibrewise-weierstrass-picard-tranche3-monoidal`
- Current fetched `origin/main`: `dd7e0f33693e2c71f8527ab4bc104e94407fa542`
- The branch merge-base with `origin/main` is exactly `dd7e0f336`.
- Proved pole-Cech tranche tip:
  `589c11a83b8b74a00a8c8e74e9a3ad10375e4e86`
- Maintenance tip before this handover:
  `88246b84b` (`Remove orphaned Cech H1 comparison`)
- Current integration PR:
  [#8567](https://github.com/CBirkbeck/AINTLIB/pull/8567), targeting `main`

At the proof tip the branch was 9 commits ahead and 0 behind current `main`.
The maintenance and handover commits are intentionally on the same integration
branch and therefore update PR #8567.

Start every session with:

```bash
cd /Users/mcu22seu/Documents/GitHub/aintlib-mc-fibrewise
git branch --show-current
git fetch origin main codex/fibrewise-weierstrass-picard-tranche3-monoidal
git rev-list --left-right --count origin/main...HEAD
git status --short
```

The branch check must print
`codex/fibrewise-weierstrass-picard-tranche3-monoidal`.
Rebase only at a clean mathematical boundary and only after preserving the
unrelated dirty work listed below.

## 2. Preserve unrelated work

The following tracked modifications predate the final tranche and are not part
of this handover:

- `.mathlib-quality/decomposition-fibrewise-locally-weierstrass.md`
- `ModularCurves/ForMathlib/FlasqueCohomology.lean`

There are also many untracked `Probe*`, `Audit*`, and `Check*` files, including
an untracked `ForMathlib/StalkTensor.lean`. Preserve all of them.

Never use:

```text
git add -A
git clean
git reset --hard
git checkout -- <path>
```

Stage only explicitly named files. Do not stash, discard, or fold the two dirty
tracked files into this proof without first establishing their owner and state.

## 3. Exact final targets

The final statements must be exactly:

```lean
theorem locallyWeierstrass_iff_abstractConditions
    {E S : Scheme} {pi : E ⟶ S} {z : S ⟶ E}
    {hz : z ≫ pi = 𝟙 S} :
    LocallyWeierstrass pi z hz ↔
      SmoothOfRelativeDimension 1 pi ∧ IsProper pi ∧
        FibrewiseElliptic pi z hz
```

and

```lean
theorem FibrewiseElliptic.locallyWeierstrass
    (hsm : SmoothOfRelativeDimension 1 pi)
    (hproper : IsProper pi)
    (h : FibrewiseElliptic pi z hz) :
    LocallyWeierstrass pi z hz
```

The smoothness and properness assumptions are load-bearing parts of the
abstract definition. They are not junk hypotheses. No further hypotheses may
appear in either final statement.

## 4. Non-negotiable drift guards

- Do not add Noetherianity to either final theorem.
- A Noetherian intermediate is allowed only through the already-landed
  arbitrary-base approximation theorem and must be removed before assembly.
- Do not introduce `CohomologyPackage`, an axiom, `unsafe`, `sorry`, `admit`,
  or an unboarded placeholder.
- Do not add any `set_option`. If elaboration is slow, split the proof and pass
  implicit arguments explicitly.
- Do not route through `Pic^0`, Abel's theorem, or the group law.
- Do not assume a projective presentation or a Weierstrass model in the final
  converse. Construct it locally from the pole sheaves.
- Do not rebuild monoidal sheafification, E[N], torsion, or group-law
  infrastructure. Consume the APIs already on `main`.
- Search all of AINTLIB and mathlib before adding an abstraction.
- Add every new Lean module to `projects/ModularCurves/ModularCurves.lean`.
- Run a focused build, style checks, a public-theorem axiom audit, and the root
  build at each natural dependency boundary.

## 5. Main-tree reconciliation

`main` at `dd7e0f336` is the single tree. It already contains the Line B work
through the packaged Noetherian pole-sheaf model. Do not merge the old Line A
branch:

```text
origin/codex/fibrewise-weierstrass-affine-chart-base-change
```

The apparent Line A residue was audited declaration by declaration:

1. `ForMathlib/CoactionCharpoly.lean`

   The 13 apparent unique declarations are the old left-slot column
   (`leftCoeff`, `comulMatrix`, and companions). Current `main` contains the
   right-slot API (`rightCoeff`, `comulMatrixR`, and companions) used by the
   characteristic-polynomial proof. Commit `ca1e47540` intentionally deleted
   the dead left-slot column. Do not restore it.

2. `EllipticCurve/AdditionSpecPoints.lean`

   The 31 apparent unique declarations were generalized, namespaced, or
   deduplicated. The live API is under `SpecPoint`, `ChartPointTriple`, and
   `Dictionary`; the generic iSup lift was moved to ForMathlib. Do not restore
   the pre-namespace spellings.

3. `EllipticCurve/GroupLawAxioms.lean`

   The base-change plumbing is present under the private `BaseChangeOf`
   namespace and the final atlas laws are present. Cleanup commit `9bde93146`
   removed dead declarations and renamed the live helpers. Do not restore the
   old spellings.

4. `EllipticCurve/PoleSheaf.lean`

   The eight private recursive pullback-trivialization helpers are superseded
   by the generic monoidal restriction lemmas
   `restrictMonoidalUnitTrivialization_restrictOpen` and
   `restrictMonoidalTensorTrivialization_restrictOpen`. The public theorem
   `sectionPoleSheafPowerTrivialization_restrictOpen` is present, simpler, and
   already consumed by `PoleSheafModel.lean` and
   `PoleSheafWeierstrassOverlap.lean`. Do not port the private helpers.

5. `LevelStructure/CartierDivisor.lean`

   The old `*Aux*` declarations are pre-rename spellings of the current
   `KerPrincipal.*`, `SectionsIdeal.*`, and related APIs. Current `main` is
   ahead. Do not port them.

6. `EllipticCurve/MulByHomUnramified.lean`

   This obsolete file was deliberately replaced by
   `TorsionUnramifiedFibre.lean`. Do not restore it.

All 105 open PRs with head names beginning
`codex/fibrewise-weierstrass-` were closed as superseded on 2026-07-29. A fresh
query then returned zero. The archival branches remain remote history; do not
merge or extend them. Also preserve
`codex/fibrewise-weierstrass-comparison-pre-rebase`, whose old pullback-tensor
map layer was retained for archaeological/PIC0 integration purposes.

The unindexed, failing
`ForMathlib/SheafCechHOneComparison.lean` was deleted in `88246b84b`. Nothing
imported it, and its two public results were superseded by the live
`SheafCechInjectiveComparison` / `AcyclicAffineCechComparison` route. This
removed three prohibited transparency options instead of maintaining a second
Cech-H1 API.

## 6. What is proved

### 6.1 Globally presented models

In `EllipticCurve/Comparison.lean`:

- `fibrewiseElliptic_projModel_iff_isElliptic`
- `locallyWeierstrass_projModel_iff_isElliptic`
- the resulting equivalence between the two predicates for `projModel W`

Thus equation recognition and the discriminant argument are complete once a
general family has been locally identified with a projective Weierstrass model.

### 6.2 Arbitrary-base Noetherian pole model

In `EllipticCurve/PoleSheafNoetherianStage.lean`:

```lean
FibrewiseElliptic.exists_noetherianPoleSheafModel
```

For an arbitrary affine smooth proper fibrewise elliptic family, it supplies:

- a Noetherian presentation-system stage `B`;
- a proper, smooth, locally finitely presented stage family `Y -> Spec B`;
- an invertible stage module `L`;
- an isomorphism after base change to the original family;
- the transported section, relative dimension, and fibrewise ellipticity;
- an isomorphism between the pullback of `L` and `O([0])`.

This is the explicit arbitrary-base removal step. Do not replace it by a final
Noetherian assumption.

### 6.3 Ordered Cech and iterated base change

The nine-commit tranche from `dd7e0f336` to `589c11a83` is:

```text
8b02bd56c Index fibrewise Weierstrass tranche modules
68692efa9 Relate cochain exactness to exactAt
a88d70ad2 Transport ordered Cech exactness across base change
6c77aba05 Record ordered Cech exactness bridge
7d307f434 Identify iterated scheme-module pullback
b44b6c818 Transport pole models through iterated base change
b5268fe8d Reflect pole Cech exactness over field bases
ee4f48981 Reflect stage pole Cech exactness to residue fields
589c11a83 Spread stage pole Cech exactness locally
```

New root-indexed modules:

- `ForMathlib/SchemeModuleOrderedBaseCechBaseChangeExact.lean`
- `ForMathlib/SchemeModulePullbackIteratedBaseChange.lean`
- `EllipticCurve/PoleSheafIteratedBaseChange.lean`
- `EllipticCurve/PoleSheafNoetherianStageCech.lean`

Key public declarations:

```text
cochainComplex_functionExact_iff_exactAt
orderedBaseCechComplex_baseChange_exact_iff_of_iso
pullbackIteratedBaseChangeIso
sectionIteratedBaseChangeDirect
sectionIteratedBaseChangeDirect_snd
sectionIteratedBaseChangeDirect_assoc_inv
sectionPoleSheafPowerDirectBaseChangeIso
FibrewiseElliptic.sectionPoleSheafPower_orderedBaseCech_differential_exact_of_isField
FibrewiseElliptic.orderedBaseCech_baseChange_exact_of_poleSheafModel
FibrewiseElliptic.orderedBaseCech_residueField_exact_of_poleSheafModel
FibrewiseElliptic.exists_away_orderedBaseCech_exact_of_poleSheafModel
```

The last theorem says that field-valued exactness of the simple-pole ordered
Cech complex reflects to the kernel residue field and spreads to
`Localization.Away r` on the Noetherian stage.

No public theorem in this tranche uses more than:

```text
propext
Classical.choice
Quot.sound
```

There are no new options, sorries, admits, axioms, or unsafe declarations.

Verification at `589c11a83`:

- focused build of
  `ModularCurves.EllipticCurve.PoleSheafNoetherianStageCech`: green,
  4,582 jobs;
- official style lint: green;
- full `lake build ModularCurves`: green, 9,535 jobs;
- all new public theorem axiom audits: expected three axioms only.

## 7. Immediate proof frontier

The next proof must apply the stage spreading theorem to the package returned
by `exists_noetherianPoleSheafModel`, at a chosen point of the original affine
base.

Use this route:

1. Start with affine `S`, a point `s : S`, `hsm`, `hproper`, and
   `h : FibrewiseElliptic pi z hz`.
2. Apply `h.exists_noetherianPoleSheafModel hsm z hz`.
3. Unpack the stage ring `B`, family `yPi`, invertible sheaf `L`, base-change
   map `gA : Spec A -> Spec B`, section `zA`, `hsmA`, `hfibA`, and the pole
   model isomorphism.
4. Take the field-valued point
   `(Spec A).fromSpecResidueField s`. Establish the field structure on its
   top global sections through the existing `Gamma(Spec -, top)` isomorphism.
5. Choose a finite affine cover trivializing `L` using
   `IsInvertible.exists_finite_affine_trivializingCover`. Add the classical
   `Fintype` and `LinearOrder` locally; do not add them to a public theorem.
6. Apply
   `hfibA.exists_away_orderedBaseCech_exact_of_poleSheafModel`
   with `t := gA`, the unpacked section and pole-model isomorphism, and the
   residue-field point.
7. Translate `r` not belonging to the kernel of the composite top-section
   map into nonvanishing of the image of `r` at `s`.
8. Replace this stage principal neighborhood by the corresponding principal
   neighborhood `D(algebraMap B A r)` of the original point. Use the existing
   localization scalar-tower and iterated-base-change APIs; do not create a
   parallel localization model.
9. Transport the exact ordered Cech complex to that original-base
   neighborhood.

Before writing this cluster, append one board claim naming its exact Lean
statement. A reasonable theorem boundary is: around every point of an affine
smooth proper fibrewise elliptic family, after one affine base restriction,
the ordered Cech differentials for `O([0])` are exact in all positive degrees
needed by the finite cover. Keep the point-neighborhood result free of a
Noetherian hypothesis.

The likely friction is not the field exactness anymore. It is the ring and
scheme bookkeeping that turns the stage element `r` into an open neighborhood
on `Spec A`. Search first for:

```text
Spec.fromSpecResidueField
Scheme.ΓSpecIso
IsLocalization.Away
LocalizedModule.Away
Spec.map
basicOpen
```

Pass `B`, `A`, the algebra maps, and scalar-tower instances explicitly if
elaboration starts unfolding large pullback terms.

## 8. Remaining mathematical chain

After the immediate stage-to-original-neighborhood theorem:

1. **Cech exactness to H1 vanishing**

   Consume, rather than rebuild:

   - `EllipticCurve/PoleSheafCechHOne.lean`
   - `ForMathlib/AcyclicAffineCechComparison.lean`
   - `ForMathlib/SheafCechInjectiveComparison.lean`
   - `EllipticCurve/PoleSheafBaseCechHOne.lean`
   - `ForMathlib/LowDegreeFiniteProjectiveReplacement.lean`
   - `ForMathlib/BaseChangeKerCoker.lean`

   The target is local vanishing of `H^1(O([0]))`, finite projectivity of the
   degree-zero kernel/base-section module, and base-change compatibility.

2. **Propagate pole modules and choose coordinates**

   Much of this layer is already landed:

   - `PoleSheafSuccessorHOne.lean`
   - `PoleSheafSuccessorSections.lean`
   - `PoleSheafSuccessorBasis.lean`
   - `PoleSheafSuccessorProductBasis.lean`
   - `PoleSheafSuccessorCoordinateMul.lean`

   Use these to obtain compatible bases
   `P1 = <1>`, `P2 = <1,x>`, and `P3 = <1,x,y>` after shrinking. Do not
   reprove the successor quotient, normalized lift, or basis-extension
   machinery.

3. **Derive the generalized Weierstrass relation**

   In the rank-six module `P6`, express the dependence among
   `1, x, y, x^2, x*y, y^2, x^3` and normalize it to

   ```text
   y^2 + a1*x*y + a3*y =
     x^3 + a2*x^2 + a4*x + a6.
   ```

   Reuse the landed multiplication-coordinate lemmas.

4. **Construct and identify the projective cubic**

   The basis of `P3` gives the map to `P^2`. Prove it is a closed immersion
   with image the cubic and sends the section to `(0:1:0)`.

   Existing `PoleSheafProjectiveCoordinates*` results are useful only after a
   projective presentation is available; do not assume their
   `IsClosedImmersion` hypothesis in the abstract converse.

5. **Recognize ellipticity and assemble**

   Apply the globally presented comparison and
   `isElliptic_of_fibrewiseElliptic_projModel`. Then cover the base by the
   local neighborhoods and prove `FibrewiseElliptic.locallyWeierstrass`.
   Combine it with:

   - `LocallyWeierstrass.fibrewiseElliptic`;
   - `isProper_of_locallyWeierstrass`;
   - `smoothOfRelativeDimension_of_locallyWeierstrass`;

   to obtain `locallyWeierstrass_iff_abstractConditions`.

## 9. Sources and imported external work

The source-faithful route is:

- Katz--Mazur, *Arithmetic Moduli of Elliptic Curves*,
  Sections 2.2.1--2.2.5;
- Hida, *Geometric Modular Forms and Elliptic Curves*,
  Definition 2.2.1 and Sections 2.2.4--2.2.5;
- Stacks Project Tags 072J, 072T, and 0A1G.

The relevant parts of Vilin97/Clawristotle's coherent-cohomology development
have already been split and adapted into AINTLIB. In particular, search the
existing `ForMathlib/SchemeModule*`, support, projective-factorization, Segre,
and finite-Cech files before consulting or copying `MainTheorem.lean`.
Do not import that external theorem wholesale or create duplicate projective
and support APIs.

## 10. Verification commands

Focused proof build:

```bash
lake build ModularCurves.EllipticCurve.PoleSheafNoetherianStageCech
```

Full indexed build:

```bash
lake build ModularCurves
```

Official style lint for a module requires the temporary root symlink in this
worktree:

```bash
test ! -e ModularCurves
ln -s projects/ModularCurves/ModularCurves ModularCurves
lake exe lint-style ModularCurves.EllipticCurve.PoleSheafNoetherianStageCech
rm ModularCurves
```

Use an untracked audit file containing imports and `#print axioms` for every new
public theorem, then run it with `lake env lean`. Do not commit the audit file.

The Lean LSP connector currently fails in this worktree because it cannot find
`lake`. Use shell `lake build` and `lake env lean` until that environment issue
is fixed. This is not a mathematical blocker.

## 11. Definition of done for the next worker

A dependency is not done until:

- its statement is on the exact no-drift route;
- repository and mathlib search found no existing replacement;
- it has no new option, sorry, admit, axiom, unsafe declaration, or junk
  typeclass;
- its focused build passes;
- style checks pass;
- each new public theorem has the expected axiom audit;
- any new module is root-indexed;
- the full root build passes;
- only intended files are staged;
- the green increment is committed and pushed to the integration branch;
- PR #8567 is updated rather than creating another stacked micro-PR.

The final two comparison theorems are not yet proved. The current frontier is
substantive progress on their only source-faithful converse route, not an
assembly theorem hidden behind extra hypotheses.
