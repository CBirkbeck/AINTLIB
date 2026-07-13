# Decomposition — [HG-C3]: the G-stable affine cover of E (STREAM-G0, 2026-07-13)

**Goal.** Supply the geometric input that `[HG-C4]` (the GlueData that discharges the six
`SubgroupQuotient` pins) consumes: a cover of `E` by `G`-stable affine opens, each lying over an
affine base patch of `S` on which `groupRing` is **free** (the `Module.Free P.baseRing P.groupRing`
hypothesis of `chartData`/`isHopfGalois_chartCoaction`, M6). Concretely, produce enough
`AffineChartPatch`es (with the freeness upgrade) whose chart opens `{U_i}` cover `E`, together with
the fact that pairwise intersections stay `G`-stable affine (for the glue).

## Why the existing orbit-cover machinery does NOT apply

`ForMathlib/SchemeQuotient.exists_isStableOpen_isAffineOpen [Finite G]` and
`Moduli/EngineDescent.exists_isStableOpen_isAffineOpen_of_orbit/_of_globalModel` (PROVEN) build a
stable affine atlas — but only for a **constant finite group** `G` acting by automorphisms
(`SchemeAction G X`, `[Group G] [Finite G]`). Our `FiniteLocallyFreeSubgroup` is an **fppf subgroup
group-scheme** (possibly non-étale — `E[p]` in char `p` is infinitesimal), acting by translation.
There is no constant group, no finite orbit of closed points in the naive sense. So C3 for the
subgroup-scheme quotient is a **separate, harder** construction — the divisor-complement route.
(Read-only inventory: the constant-group files are the C4-glue TEMPLATE, not a C3 shortcut.)

## Substrate that DOES exist (reuse)

- `E.π : E ⟶ S` is **proper** (`EndomorphismDegree:67 IsProper E.π`) and **Proj-presented**
  (projective Weierstrass; `EllipticCurve/Comparison.lean` uses `Proj.basicOpenIsoAway`,
  `quotientGrading (projIdeal W)`). ⟹ E is projective over S.
- `G.toRelEffCartierDiv : RelEffCartierDiv E.π` (`Subgroup.lean:239`) with
  `toRelEffCartierDiv_degree s = ` rank (`:275`), `_ideal`, `_isSubgroup`. So **G is a relative
  effective Cartier divisor of fibrewise degree `N = rank G ≥ 1`** — already in hand.
- `StableCharts`: `IsStableOpen`, `AffineChartPatch`, `isStableOpen_top`. `instModuleFiniteGroupRing`.

## Leaves

- **[C3a] translate of the divisor by a section.** For a section `x : S ⟶ E` (an `E.Point (𝟙 S)`),
  the translate `x + G` as a relative effective Cartier divisor of degree `N` (translation is an
  automorphism of `E/S`, carries eff. Cartier divisors to eff. Cartier divisors). Build from the
  translation automorphism `t_x : E ≅ E` (add x) applied to `G.toRelEffCartierDiv`.
- **[C3b] stability of the complement.** `E ∖ (⋃_{i} (x_i + G))` is `G`-stable: translation by a
  `G`-point permutes each coset `x_i + G` (setwise), hence preserves the union and its complement.
  This is the functor-of-points/`IsStableOpen` statement; likely the most self-contained leaf
  (elementary, Hopf-free — a good FIRST brick).
- **[C3c] affineness of the complement — THE CRUX GAP.** `E ∖ D` is affine for `D` a fibrewise-ample
  relative effective Cartier divisor (degree `≥ 1` on a genus-1 fibre ⟹ ample). **No off-the-shelf
  mathlib lemma** ("complement of ample divisor is affine" is absent). Candidate routes:
  - **(RECOMMENDED) Proj basic-open.** E is `Proj` of the Weierstrass graded ring. A degree-`N`
    divisor `D` = vanishing of a homogeneous section `f`; then `E ∖ D = D₊(f)` (the Proj basic open),
    affine by `Proj.isAffineOpen_basicOpen (hf : f ∈ 𝒜 m) (0 < m)`. Work: relate `x_i + G` (as a
    Cartier divisor) to a homogeneous `f` on `quotientGrading (projIdeal W)`, relatively over `S`.
    Reuses `Comparison.lean`'s Proj machinery. This is the shortest gap-closer.
  - (alt) KM 3.7 verbatim (`refs/katz-mazur`) — the relative "`E ∖ ample` affine" directly.
  - (alt) `Serre`-style: `Dᶜ` affine ⟺ `D` support of an ample; via cohomology vanishing (heavier).
- **[C3d] freeness per chart.** On the affine base patch `V = Spec R`, `groupRing = Γ(G|_V)` is a
  finite projective (`= Module.Finite` ✓ + flat `G.flat`) `R`-module; **free** after shrinking `V`
  to a basic open where the projective module trivializes (`Module.Free` of a f.g. projective over a
  local/appropriately-small ring; or `Module.free_of_flat_of_isLocalRing`-style + basic-open
  refinement). Supplies the `chartData` hypothesis.
- **[C3e] coverage.** The chosen cosets `{x_i + G}` have empty common intersection so the complements
  cover `E`. Cheapest: **two charts** — `E ∖ G` and `E ∖ (x_0 + G)` for a section `x_0` with
  `(x_0 + G) ∩ G = ∅`, existing Zariski-locally on `S` by smoothness of `E ∖ G → S`. (Global sections
  may be scarce ⟹ work Zariski-locally on `S`; the pins are global, so cover argument is Zariski-local
  on the base, then assemble.)
- **[C3f] assembly.** Package into the cover structure C4 consumes: a finite family of
  `AffineChartPatch` (+ freeness) with `⨆ U_i = ⊤` and `G`-stable affine pairwise intersections.

## Ordering / recommendation

1. **[C3b]** stability of the complement — self-contained, elementary, Hopf-free. FIRST brick.
2. **[C3a]** translate divisor by a section (translation automorphism + Cartier transport).
3. **[C3c]** the affineness gap via the **Proj basic-open** route — the crux; a focused sub-effort.
4. **[C3d]** freeness per chart (shrink the base patch).
5. **[C3e]/[C3f]** two-chart coverage + assembly.

**Estimate:** C3c (the affineness gap) is the true long pole — a dedicated sub-session even via Proj.
C3b/C3a/C3d are each ~1 brick. Total: a full focused session (or two), matching "hardest geometry leaf."

**Interaction with C2/C4:** C3 is independent of the C2 sorry (`chartPrecursorSpec_isClosedImmersion`)
— both feed the sorry-free `isHopfGalois_chartCoaction` that C4 consumes. C4 (GlueData) can be
prototyped against the constant-group `SchemeQuotient` template once C3's cover exists.

## Appendix: C3 execution state (STREAM-G0, 2026-07-13, resume)

LANDED sorry-free (reusable infra):
- **C3a** `TranslationBySection.translateByIso x : E.asOver ≅ E.asOver` (p↦p+x).
- **RelEffCartierDiv.mapIso** (CartierDivisorMapIso.lean) — pushforward of a rel eff Cartier divisor
  along an S-automorphism; coset `x+D := mapIso (translateByIso x) …`.
- **C3b-half** `StableComplement.actionShear : G×_S E ≅ G×_S E` `(t,x)↦(t,x+ιt)`, with
  `actionShear_hom_comp_actionProj : actionShear.hom ≫ actionProj = translationAction`.

REMAINING C3b (the group-closure witness — the real content of `IsStableOpen (E∖G)`):
With `translationAction.left = actionShear.hom.left ≫ actionProj.left` and `actionShear.hom.left`
a homeomorphism, `IsStableOpen(E∖G)` reduces to `V ≤ actionShear.hom.left⁻¹ᵁ V`
(`V := actionProj.left⁻¹ᵁ(E∖G) = {(t,x):x∉G}`), i.e. the topological inclusion
`translationAction.left.base⁻¹(range ι) ⊆ actionProj.left.base⁻¹(range ι)` (`x+ιt∈G ⟹ x∈G`).
WITNESS: on `Z := pullback translationAction.left G.ι` (base = the preimage; `pullback.fst` a closed
immersion of base-range = that preimage), build `q : Z → G.G` = `⟨pullback.snd (=x+ιt∈G),
invHom(pullback.fst≫fst-to-G) (=−ιt)⟩ ≫ mulHom`, and prove `q ≫ G.ι = pullback.fst ≫ actionProj.left`
via `mulHom_ι` + `invHom_ι` (ι intertwines the group laws; `x=(x+ιt)+(−ιt)`). Then range of
`pullback.fst.base` = the preimage ⟹ `actionProj.left.base(preimage) ⊆ range ι`. ~80–100 lines;
the base/range plumbing (`range pullback.fst` = topological preimage for a closed immersion) is the
fiddly part. Dedicated sub-session.

REMAINING C3c bridge: `x+G = V(fᵢ)` for homogeneous `fᵢ` ⟹ `E∖(x+G)=D₊(fᵢ)` affine via mathlib
`Proj.isAffineOpen_basicOpen` (grep `sectionsDivisor`/`sectionDivisor` — `sectionDivisor` = single
section's `ker` divisor; need degree-N divisor→homogeneous-section via the Weierstrass grading).
