# Prose Context for Blueprint Authoring

This document is the single prose-context file consulted by every blueprint
worker dispatched in Phase 4. Its purpose is to fix the mathematical narrative,
the notational conventions, and the source-mapping tables once and for all so
that no worker needs to re-read source papers or the project-level overview
markdown.

The project is the **LeanModularForms** repository at
`/Users/mcu22seu/Documents/GitHub/LeanModularForms`, branch `feat/mathlib-prs`.
Blueprint scope is the **transitive dependency closure** of the two protected
theorems:

* `LeanModularForms.hw_3_3_clean_full_mero` in `ForMathlib/HW33Clean.lean`
* `valence_formula_textbook` in `ForMathlib/ValenceFormulaFinal.lean`

Together the closure spans ~118 `.lean` files / ~36k lines / ~1,762
declarations.

## Project narrative

The LeanModularForms project formalises in **Lean 4** two headline theorems of
complex-analytic number theory. The first is the
**Hungerbühler–Wasem generalised residue theorem** (Theorem 3.3 of
arXiv:1808.00997v2) in its maximally general "multi-crossing, higher-order
meromorphic" form. The second is the classical **textbook valence formula**
for weight-$k$ modular forms on the full modular group $\operatorname{SL}_2(\mathbb{Z})$.

The HW residue theorem extends the classical residue theorem to the situation
where a closed piecewise-$C^{1}$ immersion $\gamma$ in an open set $U \subseteq \mathbb{C}$
may **pass through** poles of $f$. Classical residue formulas require $\gamma$
to avoid the singular set $S$ entirely; HW3.3 instead replaces the ordinary
contour integral by a **Cauchy principal value** and a **generalised winding
number** that is permitted to take half-integer or fractional values when
$\gamma$ crosses $S$. The protected statement
`hw_3_3_clean_full_mero` asserts: for an open $U \subseteq \mathbb{C}$, a finite singular set
$S \subseteq U$, a function $f$ differentiable on $U \setminus S$ and meromorphic at
each point of $S$, a closed piecewise-$C^{1}$ immersion
$\gamma : [0,1] \to U$ null-homologous in $U$, and with paper conditions $(A')$
and $(B)$ on the crossing geometry,
$$ \operatorname{PV}\!\!\int_\gamma f(z)\,\mathrm{d}z
 \;=\; \sum_{s \in S} 2\pi i\,\operatorname{gWN}(\gamma, s)\,\operatorname{Res}(f, s). $$

The valence formula is the classical dimension-counting identity for modular
forms. The protected statement `valence_formula_textbook` says: for any
nonzero weight-$k$ modular form $f$ on $\operatorname{SL}_2(\mathbb{Z})$,
$$ \operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
 + \tfrac{1}{3}\operatorname{ord}_\rho(f)
 + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}, $$
where $i$ and $\rho = e^{2\pi i / 3}$ are the two elliptic points of $\operatorname{SL}_2(\mathbb{Z})$ in the
standard fundamental domain $\mathcal{D}$, and the last sum runs over the
non-elliptic $\operatorname{SL}_2(\mathbb{Z})$-orbits. The proof is the textbook contour-integral
argument: one takes the logarithmic derivative $f'/f$ around the FD boundary
contour at height $H$, applies HW3.3 to the boundary (which crosses the three
elliptic points), and exploits modular invariance to identify the resulting
sum with $k/12$.

Both theorems have been verified to compile with the standard Lean axiom basis
`[propext, Classical.choice, Quot.sound]`. The two proofs together drive the
entire dependency closure: 16 files under `ForMathlib/HungerbuhlerWasem/`
(6,340 LOC) for the HW machinery, 16 files under `ForMathlib/ValenceFormula/`
(8,034 LOC) for the modular side, 16 files under
`ForMathlib/GeneralizedResidueTheory/` (4,130 LOC) for the residue chain
bridging the two, plus 69 files in `ForMathlib/` (root, 17,235 LOC) for the
shared analytic infrastructure (curve types, Cauchy PV, generalised winding
numbers, Dixon's theorem, fundamental-domain boundary parametrisation, FTC
providers).

## Notational conventions

The following symbols are used uniformly across the blueprint LaTeX. They are
listed with their Lean source, the file where they are introduced, and the
preferred LaTeX form.

* $\mathbb{C}$ — the complex numbers (Lean: `ℂ`). Always set in `\mathbb{C}`.
* $\mathbb{R}$ — the reals (Lean: `ℝ`). Always set in `\mathbb{R}`.
* $\mathbb{Z}$ — the integers (Lean: `ℤ`). Always set in `\mathbb{Z}`.
* $\mathbb{H}$ or $\mathcal{H}$ — the upper half-plane $\{z \in \mathbb{C} : \operatorname{Im}(z) > 0\}$
  (Lean: `UpperHalfPlane` / `ℍ`, imported from
  `Mathlib.NumberTheory.ModularForms.Basic`). Prefer `\mathbb{H}`.
* $\mathcal{D}$ — the standard fundamental domain
  $\{z \in \mathbb{H} : |z| \ge 1, |\operatorname{Re}(z)| \le 1/2\}$
  (Lean: `𝒟` = `ModularGroup.fd`, imported from mathlib).
* $i$ — the elliptic point $i = \sqrt{-1}$ (Lean: `Complex.I`,
  `ellipticPointI'`).
* $\rho$ — the elliptic point $\rho = e^{2\pi i / 3} = -1/2 + (\sqrt{3}/2) i$
  (Lean: `ellipticPointRho'` in `ForMathlib/EllipticPoints.lean`, `Complex`
  form `ellipticPointRho`).
* $\rho + 1 = e^{\pi i / 3} = 1/2 + (\sqrt{3}/2) i$ — the $T$-translate of
  $\rho$ on the right boundary of $\mathcal{D}$ (Lean:
  `ellipticPointRhoPlusOne'` / `ellipticPointRhoPlusOne`).
* $\gamma$ — a closed piecewise-$C^{1}$ immersion (Lean: `ClosedPwC1Immersion`
  or `PwC1Immersion`, in `ForMathlib/PaperPwC1Immersion.lean` and
  `ForMathlib/PiecewiseC1Path.lean`). When acting as a path it is also
  available as `γ.toPath : Path x y` and `γ.toPath.extend : ℝ → ℂ`.
* $\gamma'(t)$ — the derivative `deriv γ.toPath.extend t` (Lean shorthand
  $\gamma'$ where unambiguous).
* $\dot{\Lambda}$ — paper alias for the derivative of a paper immersion
  $\Lambda$, used only when paraphrasing Hungerbühler–Wasem directly.
* $H$ — the height cutoff for the fundamental-domain boundary (Lean: `H : ℝ`).
* $S$ — the finite singular set (Lean: `S : Finset ℂ`).
* $s$ — a generic element of $S$ (a pole / on-curve point).
* $f$ — the integrand: either a meromorphic function on $\mathbb{C}$ (HW context) or
  a weight-$k$ modular form $f \in M_k(\Gamma(1))$ (valence context).
* $U$ — an open subset of $\mathbb{C}$ (Lean: `U : Set ℂ`, `IsOpen U`).
* $k$ — the weight of a modular form (Lean: `k : ℤ`).
* $t$, $t_0$ — real parameters in $[0,1]$ (Lean: `t t₀ : ℝ`).
* $L$, $L_+$, $L_-$ — tangent vectors at a crossing: $L_+$ is the right-side
  one-sided derivative limit, $L_-$ the left-side limit. In Lean code these
  appear as `L_R`/`L_L` or `L_plus`/`L_minus`.
* $r$, $\varepsilon$, $\delta$ — small positive reals; $r$ is typically a
  window radius around a crossing, $\varepsilon$ is the CPV cutoff, $\delta$
  is an exit-time cutoff.
* $w$, $z_0$ — variable points in $\mathbb{C}$ used as test points (e.g. for the
  Dixon function, the residue formula).
* $\alpha$, $\theta$, $\theta_0$ — angles (radians). $\theta_0$ is typically
  the angle of an elliptic point on the unit circle.
* $\partial \mathcal{D}_H$ — the height-$H$ truncated boundary of $\mathcal{D}$
  (Lean: `fdBoundary_H H` parametrised on $[0,5]$, or `fdBoundaryFun H`
  parametrised on $[0,1]$).
* $\operatorname{gWN}(\gamma, s)$ — generalised winding number
  (Lean: `generalizedWindingNumber γ s`).
* $\operatorname{Res}(f, s)$ — residue (Lean: `residue f s`).
* $\operatorname{ord}_p(f)$ — order of vanishing at $p$ (Lean:
  `orderOfVanishingAt' f p` for $p \in \mathbb{H}$; takes values in $\mathbb{Z}$).
* $\operatorname{ord}_\infty(f)$ — order at the cusp (Lean: `orderAtCusp' f`,
  the order of the q-expansion power series).
* $\operatorname{PV}\!\!\int_\gamma f(z)\,\mathrm{d}z$ — Cauchy principal value
  along $\gamma$ (Lean: predicate `HasCauchyPVOn S f γ.extend L` /
  `HasCauchyPV f γ z₀ L`; value extractor `cauchyPV`).

## Mathematical objects and their LaTeX

A worker writing the LaTeX for a Lean declaration should consult this table
to render the mathematical object in the project's preferred style. Typeclass
arguments (`[FunLike F α β]`, `[NormedAddCommGroup E]`, decidability
instances) and `Classical.propDecidable` `attribute` injections are **always
dropped** from the LaTeX. Mathlib-standard structures appear by their
mathematical name (modular form, meromorphic function, etc.) and not by their
Lean type name.

* `ModularForm Γ k` → "a modular form $f$ of weight $k$ on the congruence
  subgroup $\Gamma$".
* `ModularForm (Gamma 1) k` → "a weight-$k$ modular form $f$ on
  $\operatorname{SL}_2(\mathbb{Z})$" (= $\Gamma(1)$).
* `MeromorphicAt f s` → "$f$ is meromorphic at $s$".
* `MeromorphicAt.order f s` → the meromorphic order
  $\operatorname{ord}_s(f) \in \mathbb{Z}_{\le \infty}$ (a `WithTop ℤ`).
* `DifferentiableOn ℂ f (U \ S)` → "$f$ is holomorphic on $U \setminus S$".
* `AnalyticAt ℂ g s` → "$g$ is analytic at $s$".
* `PiecewiseC1PathOn a b hab x y` → "a piecewise-$C^{1}$ path
  $\gamma : [a, b] \to E$ from $x = \gamma(a)$ to $y = \gamma(b)$".
* `PiecewiseC1Path x y` → "a piecewise-$C^{1}$ path $\gamma : [0,1] \to E$
  from $x$ to $y$ (the unit-interval specialisation, bundled with a mathlib
  `Path`)".
* `PwC1Immersion x y` → "a piecewise-$C^{1}$ immersion $\gamma$ from $x$ to
  $y$ (piecewise-$C^{1}$ path with non-vanishing derivative on each piece
  and nonzero one-sided derivative limits at partition points)".
* `ClosedPwC1Curve x` → "a closed piecewise-$C^{1}$ curve based at $x$
  (paper-faithful Hungerbühler–Wasem definition: partition $0 = a_0 < a_1 <
  \cdots < a_n = 1$, $C^{1}$ on each **closed** sub-interval $[a_k, a_{k+1}]$,
  $\gamma(0) = \gamma(1) = x$)".
* `ClosedPwC1Immersion x` → "a closed piecewise-$C^{1}$ immersion based at
  $x$ (closed piecewise-$C^{1}$ curve with $\dot{\gamma}|_{[a_k, a_{k+1}]}
  \ne 0$ for all consecutive partition members)".
* `IsNullHomologous γ U` → "$\gamma$ is null-homologous in the open set $U$
  ($\gamma$ has image in $U$ and winds zero times around every point of
  $\mathbb{C} \setminus U$)".
* `IsFlatOfOrder γ t₀ n` → "$\gamma$ is **flat of order $n$** at $t_0$
  (Definition 3.2 of HW: the tangent-deviation is $o(\|\gamma(t) - \gamma(t_0)\|^n)$
  from each side)".
* `tangentDeviation w L` → "the component of $w \in \mathbb{C}$ orthogonal to direction
  $L$ ($\mathbb{C}$ viewed as $\mathbb{R}^2$)".
* `orthogonalProjectionComplex w L` → "the orthogonal projection of $w$ onto
  the real line $\mathbb{R} L$".
* `SatisfiesConditionA' γ f S poleOrder` → "$\gamma$ satisfies HW
  **condition (A')** with pole-order data: for every $s \in S$ and every
  $t_0 \in (0,1)$ with $\gamma(t_0) = s$, the curve is flat of order
  $\operatorname{poleOrder}(s)$ at $t_0$".
* `SatisfiesConditionB γ f S` → "$\gamma$ and $f$ satisfy HW
  **condition (B)**: at every crossing the angle is a rational multiple of
  $\pi$, and the Laurent coefficients of $f$ at each crossing pole satisfy the
  angle-compatibility identity $k \alpha \in 2\pi \mathbb{Z}$ (for every non-vanishing
  coefficient $a_k$ with $k \ge 1$)".
* `angleAtCrossing γ t₀ ht₀` → "the **crossing angle** of $\gamma$ at $t_0$
  ($\pi$ at smooth points; $\arg L_R - \arg(-L_L)$ at corner partition
  points)".
* `PolarPartDecomposition f S U` → "a **polar-part decomposition** of $f$:
  for each $s \in S$, an explicit Laurent polar part $P_s(z) = \sum_{k=0}^{N_s - 1}
  a_{s,k}/(z-s)^{k+1}$ such that $f - \sum_s P_s$ extends analytically to all of
  $U$".
* `PolarPartDecomposition.order s` → "$N_s$, the order of the polar part at $s$".
* `PolarPartDecomposition.coeff s k` → "$a_{s,k}$, the $k$-th Laurent coefficient
  at $s$".
* `PolarPartDecomposition.analyticRemainder` → "$f - \sum_s P_s$, the analytic
  remainder, holomorphic on all of $U$".
* `residue f s` → "the residue $\operatorname{Res}(f, s) = \lim_{r \to 0^+}
  (2\pi i)^{-1} \oint_{|z-s|=r} f(z)\, \mathrm{d}z$".
* `HasSimplePoleAt f z₀` → "$f$ has a simple pole at $z_0$: there exist
  $c \in \mathbb{C}$ and an analytic $g$ near $z_0$ with $f(z) = c/(z-z_0) + g(z)$".
* `HasSimplePoleAt.coeff` → "the coefficient $c$ in the simple-pole
  decomposition".
* `cpvIntegrand f γ z₀ ε t` → "the $\varepsilon$-cutoff integrand:
  $f(\gamma(t))\,\gamma'(t)$ if $\|\gamma(t) - z_0\| > \varepsilon$, else $0$".
* `cpvIntegrandOn S f γ ε t` → "the multi-point $\varepsilon$-cutoff
  integrand: zero whenever $\gamma(t)$ is within $\varepsilon$ of any $s \in S$".
* `HasCauchyPV f γ z₀ L` → "the Cauchy principal value of
  $\oint_\gamma f(z)\,\mathrm{d}z$ at the singularity $z_0$ exists and equals
  $L$ (Tendsto formulation: the $\varepsilon$-cutoff integral tends to $L$ as
  $\varepsilon \to 0^+$)".
* `cauchyPV f γ z₀` → "the CPV value, via `limUnder`. Returns junk when the
  limit does not exist".
* `HasCauchyPVOn S f γ L` → "multi-point CPV: the $\varepsilon$-cutoff integral
  excluding $\varepsilon$-balls around every $s \in S$ tends to $L$ as
  $\varepsilon \to 0^+$".
* `HasGeneralizedWindingNumber γ z₀ w` → "$\gamma$ has generalised winding
  number $w$ around $z_0$ (the CPV of $(z - z_0)^{-1}$ along $\gamma$ exists
  and equals $2 \pi i \, w$)".
* `generalizedWindingNumber γ z₀` → "$\operatorname{gWN}(\gamma, z_0) =
  (2 \pi i)^{-1} \cdot \operatorname{PV}\!\!\int_\gamma (z - z_0)^{-1}\,\mathrm{d}z$".
* `dixonFunction f U γ w` → "the **Dixon function** at $w$: an entire-valued
  combinator that vanishes when $\gamma$ is null-homologous in $U$ and $f$ is
  holomorphic on $U$; it provides the homological Cauchy integral formula".
* `dixonH1`, `dixonH2` — "the two pieces of the Dixon function (the
  `dslope`-integral piece and the Cauchy-type piece)".
* `SingleCrossingData γ z₀` → "**single-crossing data** at $z_0$: a bundled
  package of the symmetric cutoff $\delta(\varepsilon)$, the near/far bounds
  $\|\gamma(t) - z_0\| > \varepsilon$ outside $[t_0-\delta, t_0+\delta]$ and
  $\le \varepsilon$ inside, the FTC telescoping witness, and an FTC limit
  target $L$. Yields existence of the CPV and the generalised winding
  number".
* `AsymmetricSingleCrossingData γ z₀` → "**asymmetric** single-crossing data
  with independent left/right cutoffs $\delta_-, \delta_+$ — used at corner
  crossings where $L_+ \ne L_-$".
* `CornerFTCHyp`, `ArcFTCHyp` → "FTC providers for corner / arc segments;
  bundles of FTC + integrability + limit hypotheses driving the
  per-elliptic-point chains".
* `FDWindingData H` → "winding-number data for the fundamental-domain
  boundary at height $H$: the boundary as a `PiecewiseC1Path`, the interior
  winding (= $-1$), and the elliptic winding numbers at $i$ ($-1/2$), $\rho$
  ($-1/6$), $\rho+1$ ($-1/6$)".
* `FDWindingDataFull H` → "$\operatorname{FDWindingData}$ extended with
  smooth-boundary winding ($= -1/2$ at every non-elliptic boundary point)".
* `SmoothBoundaryWindingData` → "winding-number bundle at a smooth boundary
  point (arc-or-vertical interior)".
* `fdBoundaryFun H : ℝ → ℂ` → "the five-segment fundamental-domain boundary
  parametrised on $[0,1]$ with breakpoints $1/5, 2/5, 3/5, 4/5$".
* `fdBoundary_H H : ℝ → ℂ` → "the same five-segment boundary parametrised on
  $[0,5]$ with integer breakpoints".
* `fdBoundaryPath H`, `fdBoundaryPC1Path H` → mathlib `Path` /
  `PiecewiseC1Path` wrappers of `fdBoundaryFun`.
* `fdStart H` → "the start/end point $1/2 + iH$ of $\partial \mathcal{D}_H$".
* `fdBox` → "an open rectangle containing $\mathcal{D}$ up to height $H$ (used as
  the domain of holomorphy for $\log f$)".
* `modularFormCompOfComplex f` → "the composition $f \circ \operatorname{ofComplex}$,
  the modular form as a function $\mathbb{C} \to \mathbb{C}$ supported on $\mathbb{H}$".
* `orderOfVanishingAt' f z` → "$\operatorname{ord}_z(f)$ as an integer (the
  meromorphic order at $z$, untopped to $0$)".
* `orderAtCusp' f` → "$\operatorname{ord}_\infty(f)$ via the order of the
  q-expansion".
* `OrbitFM` → "the quotient $\mathbb{H} / \operatorname{SL}_2(\mathbb{Z})$".
* `orbFM p` → "the orbit of $p \in \mathbb{H}$".
* `NonEllOrbitFM` → "the set of non-elliptic orbits (those distinct from the
  orbit of $i$ and the orbit of $\rho$)".
* `ordOrbitFM`, `ordOrbitQ` → "the order of vanishing lifted to orbits, with
  `ordOrbitQ` the $\mathbb{C}$-valued cast used in the final theorem".
* `repCanon f hf` → "canonical representatives of non-elliptic orbits with
  non-vanishing order; splits as `repStrict ⊔ repLeftVert ⊔ repLeftArc`".

## Source mappings (per Lean directory / namespace)

### `LeanModularForms/ForMathlib/` (root, 69 files, ~17,235 LOC)

Module-docstring summary: this is the general-purpose analytic core shared by
both protected theorems. It contains: piecewise-$C^{1}$ path / immersion types
(`PiecewiseC1Path`, `PiecewiseC1PathOn`, `PaperPwC1Immersion`); Cauchy
principal value API (`CauchyPrincipalValue`, `MultipointPV`); generalised
winding numbers (`GeneralizedWindingNumber`, `WindingInteger`,
`WindingArgDiff`); null-homology (`NullHomologous`); the Dixon-theorem chain
(`DixonDef`, `DixonDiff`, `DixonTheorem`, `DslopeIntegral`); the
fundamental-domain boundary chain (`FDBoundary`, `FDBoundaryH`,
`FDBoundaryPath`, `FDBoundaryReparametrization`,
`FDWindingDataFullAssembly`, `FDWindingDataFullSeg1Seg4`); FTC providers and
crossing data (`SingleCrossing`, `AsymmetricSingleCrossing`, `CrossingAtI`,
`CrossingAtRho`, `ArcFTCAtI`, `ArcGenericFTCProvider`, `CornerFTCAtRho`,
`Seg1FTCProvider`, `Seg4FTCProvider`, `VertSegFTCProvider`,
`ArcFTC`, `ArcFTCLimit`); winding-weight / smooth-boundary supports
(`WindingWeightProofs`, `WindingWeightsUnconditional`, `BoundaryWinding`,
`BoundaryWindingArcProof`, `BoundaryWindingSeg1Proof`,
`BoundaryWindingSeg4Proof`, `SmoothBoundaryWindingProof`,
`InteriorWinding`, `InteriorContourIntegral`); the modular-form bridge
(`EllipticPoints`, `ModularInvariance`, `Orbits`, `OrbitPairing`,
`CanonicalReps`); orbit-level definitions and the topmost two leaves
(`ValenceFormula.lean`, `ValenceFormulaBridged.lean`, `ValenceFormulaFinal.lean`,
`HungerbuhlerWasem.lean`, `HW33Clean.lean`); plus utilities
(`Instances`, `TrigLemmas`, `CurveUtilities`, `CurveMeasureZero`,
`ClassicalCPV`, `Residue`, `ResidueCircleIntegral`, `ResidueSide`,
`ResidueSideBridge`, `SimplePoleIntegral`, `PiecewiseContourIntegral`,
`SegmentAnalysis`, `SegmentFTC`, `WindingDecomposition`, `ExitTime`,
`FlatChordBound`, `FlatnessConditions`, `PiecewiseC1Path`,
`PiecewiseC1PathOn`, `PVChainProof`, `PVSplitting`, `CrossingAnalysis`,
`CoreIdentityProof`, `Orbits`, `OrbitPairing`).

Cited references: Hungerbühler–Wasem (arXiv:1808.00997v2, especially the
paper-faithful curve definition on page 3, Definition 3.2 on flatness, and
Theorem 3.3 on the residue theorem); Diamond–Shurman, *A First Course in
Modular Forms*, Theorem 3.1.1 (the textbook valence formula); J.-P. Serre,
*A Course in Arithmetic*, Chapter VII (for the order-counting identity).

Key declarations driving Phase 4: `hw_3_3_clean_full_mero` (the final
maximally-general HW3.3); `valence_formula_textbook` (the unconditional
valence formula); `HungerbuhlerWasem.PolarPartDecomposition`;
`HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`;
`HasCauchyPV` / `HasCauchyPVOn`; `HasGeneralizedWindingNumber` /
`generalizedWindingNumber`; `IsNullHomologous`; `SatisfiesConditionA'`;
`SatisfiesConditionB`; `IsFlatOfOrder`; `angleAtCrossing`;
`ClosedPwC1Immersion`; `dixonFunction`; `FDWindingDataFull`;
`fdBoundary_H`; `fdBoundaryFun`; `modularFormCompOfComplex`;
`orderOfVanishingAt'`; `orderAtCusp'`; `OrbitFM`; `repCanon`;
`valence_formula_textbook_orbit_finsum_FM`.

### `LeanModularForms/ForMathlib/HungerbuhlerWasem/` (12 files, ~6,340 LOC)

Module-docstring summary: the full HW residue-theorem machinery for the
multi-crossing higher-order meromorphic form. Files: `MultiCrossingCPV`
(the multi-crossing CPV existence theorem T-BR-Y9d/e, the largest single
file at ~1,537 LOC); `Crossing` (per-pole CPV composition combining
simple-pole and sector-cancellation arguments); `CrossingCPV` (single-pole
CPV at a transverse crossing, T-CC-01); `CrossingHigherOrder` (paper-faithful
higher-order CPV discharger from immersion data, T-BR-03);
`SectorCancellation` (the sector-even CPV vanishing under condition (B),
equation 3.4 of HW, T-SC-01); `LaurentExtraction` (extracts the Laurent
polar-part data from a `SatisfiesConditionB.laurent_compatible` witness via
`Classical.choose`, builds the `PolarPartDecomposition`);
`CPVExistence` (single-crossing CPV existence via exit-time / chord-to-tangent
machinery); `CPVExistenceMulti` (geometric setup for multi-crossing);
`LocalCutoffs` (per-crossing exit-time cutoffs);
`CrossingDataBuilder` (`SingleCrossingData` builders from immersion data);
`HigherOrderAsymptotics` (F-diff asymptotic chain T-SC-00a);
`MultiPoleDCT` (DCT lift from single-pole CPV to multi-pole `HasCauchyPVOn`,
T-BR-Y5).

Cited references: Hungerbühler–Wasem §3 (residue theorem proof) and §4
(the proof of equation 3.4 sector identity). The numbering scheme T-XX-NN
inside Lean docstrings refers to the project's internal proof-task tree
(captured in the `decomposition.md` artifacts under `.mathlib-quality/`).

Key declarations driving Phase 4:
`HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean` (the
discharged 8-paper-hypothesis theorem that `hw_3_3_clean_full_mero` calls);
`HungerbuhlerWasem.hasCauchyPVOn_multiCrossing_higherOrder`;
`HungerbuhlerWasem.cpv_polarPart_at_pole_under_conditions`;
`HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB`;
`HungerbuhlerWasem.HasCauchyPV.add` / `.zero_fun` / `.finset_sum` /
`.congr_pointwise`;
`HungerbuhlerWasem.analyticRemainder_contourIntegral_zero`;
`HungerbuhlerWasem.analyticRemainder_hasCauchyPVOn_zero`;
`HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full`;
`HungerbuhlerWasem.MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole`;
`HungerbuhlerWasem.sector_pv_formula_vanishes_under_conditionB`;
`HungerbuhlerWasem.hasCauchyPVOn_singleton_pow_of_conditionB_assembled`;
`HungerbuhlerWasem.hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`.

### `LeanModularForms/ForMathlib/ValenceFormula/` (16 files, ~8,034 LOC)

Module-docstring summary: the modular-side chain that uses the HW machinery
to derive the valence formula. Sub-folders:

* `Boundary/` (`Bounds.lean`, `Smooth.lean`): segment selectors,
  trigonometric helpers, geometric bounds, differentiability /
  derivative-limit infrastructure for `fdBoundary_H H`.
* `OnCurvePV/` (`Basic.lean`, `EndpointCorner.lean`, `Main.lean`): proves
  CPV existence at every point of $\partial \mathcal{D}_H$ — the three
  elliptic on-curve points, smooth boundary points, and the corner/endpoint
  cases.
* `WindingWeights/` (`I.lean`, `Rho.lean`, `RhoPlusOne.lean`, `Common.lean`):
  computes the generalised winding numbers $-1/2$ at $i$, $-1/6$ at $\rho$,
  $-1/6$ at $\rho+1$ via the PV integral converging respectively to $-i\pi$
  and $-i\pi/3$. `Common.lean` factors the shared piecewise-FTC scaffolding
  (`heq_deriv_of_eq_on_nhds`, `hasDerivAt_arc_sub_const`, `ftc_log_pieceFM`).
* `PVChain/` (`Helpers.lean`, `ArcContribution.lean`, `OnCurveCapture.lean`,
  `Seg5CuspIntegral.lean`, `ResidueSideInfra.lean`, `Assembly.lean`):
  builds the modular side of the PV chain ($\varepsilon$-truncated integral
  of $f'/f$ around $\partial \mathcal{D}_H$ tends to
  $-(2\pi i (k/12 - \operatorname{ord}_\infty(f)))$), the residue-side
  infrastructure (logDeriv-of-zero gives simple poles, residue identification
  with $\operatorname{ord}_p(f)$), and the assembly equating the two limits.

Cited references: Diamond–Shurman §3 / Theorem 3.1.1 (the textbook proof);
the unit-circle arc identities. The Seg5 cusp-integral file additionally
references mathlib's $q$-expansion machinery.

Key declarations driving Phase 4: `valence_formula_textbook_unconditional_FM`;
`valence_formula_textbook_orbit_finsum`;
`valence_formula_textbook_orbit_finsum_FM`; `pv_integral_at_i_tendsto`;
`pv_integral_at_rho_tendsto`; `pv_integral_at_rho_plus_one_tendsto`;
`gWN_fdBoundary_H_at_i` (= $-1/2$); `gWN_fdBoundary_H_at_rho` (= $-1/6$);
`gWN_fdBoundary_H_at_rho_plus_one` (= $-1/6$);
`cpv_residue_side_HasCauchyPVOn`; `cpv_modular_side_HasCauchyPVOn`;
`cpv_modular_side_tendsto`; `cpv_exists_at_rho`;
`fdBoundary_H_eq_arc`; `oncurve_full_capture`;
`tendsto_pvIntegral_arc_bridge`;
`fdBoundaryFun_log_diff_core_tendsto`;
`hasSimplePoleAt_logDeriv_of_zero'`;
`residueSimplePole_logDeriv_eq_order`.

### `LeanModularForms/ForMathlib/GeneralizedResidueTheory/` (16 files, ~4,130 LOC)

Module-docstring summary: the GRT residue chain, used by HW33 (via the
`residueTheorem_simplePoles_convex` corollaries) and by the valence-formula
bridge (`generalizedResidueTheorem'`). Sub-folders:

* `Residue/` (`MeasureHelpers.lean`, `MultipointPV.lean`,
  `MultipointPV/DominatedConvergence.lean`, `GeneralizedTheoremBase.lean`): the
  multi-point Cauchy principal value $\operatorname{PV}_S$, the residue at a
  simple pole `residueSimplePole`, `residueAt`, `HasSimplePoleAt`
  (re-exported from `ForMathlib.Residue`), and the headline
  `generalizedResidueTheorem'` for convex domains with explicit PV
  hypothesis.
* `Homotopy/` (`Integrality.lean`, `Invariance.lean`): the bridge from PV
  winding number to classical contour integral when $\gamma$ avoids
  $z_0$ (`generalizedWindingNumber_eq_classical_away`).
* `OnCurvePV/Basic.lean`: GRT-side per-point CPV existence on the
  fundamental-domain boundary (specialisation of the HW machinery to
  $f(z) = (z-s)^{-1}$).
* `PVInfrastructure/`: the dominated-convergence + annulus-bound +
  step-bound + remainder-analysis pile that delivers
  `generalizedResidueTheorem_higher_order_tendsto`.
* `ArcCalculus.lean`: a small general-purpose unit-circle arc API.
* `CauchyPrimitive.lean`: holomorphic primitive on a convex set via the
  segment integral.
* `Residue.lean`: ties the file structure together; defines the multi-point
  PV integrand and existence predicate; states the classical
  `integral_eq_sum_residues_of_avoids` and `pv_integral_simple_pole`.

Cited references: classical results on Cauchy integrals (Ahlfors, Conway).
The dominated-convergence portion follows mathlib's
`MeasureTheory.intervalIntegral.tendsto_integral_filter_of_dominated_convergence`.

Key declarations driving Phase 4: `generalizedResidueTheorem'`;
`generalizedResidueTheorem_higher_order_tendsto`;
`residueAt`; `residueSimplePole`; `cauchyPrincipalValueIntegrandOn`;
`cauchyPrincipalValueOn`; `CauchyPrincipalValueExistsOn`;
`HasSimplePoleAt`; `cauchyPrincipalValueOn_singular_sum`;
`generalizedWindingNumber_eq_classical_away`;
`holomorphic_convex_primitive`; `cpv_exists_on_smooth_subinterval`.

### `LeanModularForms/ForMathlib/ContourIntegral/` (3 files, ~289 LOC)

Module-docstring summary: a thin slice of contour-integral lemmas. Files:
`PVSplit.lean` (splits the PV cutoff integral at a single crossing into
left + middle (zero) + right pieces); `SegmentFTC.lean` (telescoping FTC
for log-derivatives on consecutive segments); `CrossingLimit.lean` (the
master crossing-limit theorem reducing PV computation to a log-difference
limit at the crossing).

Cited references: standard FTC + change-of-variables (no external paper).

Key declarations driving Phase 4: `ContourIntegral.pv_split_at_crossing`;
`ContourIntegral.pv_tendsto_of_crossing_limit`;
`ContourIntegral.pv_tendsto_of_crossing_limit_asymmetric`;
`ContourIntegral.ftc_telescope_closed_split`.

### Top-level umbrella + protected leaves

`LeanModularForms.lean` (44 lines, 44 imports) is the umbrella file. The two
protected leaves `HW33Clean.lean` (82 lines) and `ValenceFormulaFinal.lean`
(70 lines) are each a single-theorem invocation file that imports the
appropriate sub-chain root.

## High-priority unformalisation sources (in order)

When a worker writes the LaTeX statement and informal proof sketch for a
Lean declaration, the following sources should be consulted in this order:

1. The Lean file's top-of-file `## Main results` docstring — gives the
   project's preferred informal naming and the place of the declaration in
   the proof tree.
2. The declaration's own `/-- ... -/` docstring — gives the precise informal
   statement intended by the author.
3. `.mathlib-quality/plan.md`, `.mathlib-quality/plan-tight.md`, and the
   ticket markdowns (`tickets-tight.md`, `tickets.md`) — give the
   decomposition rationale for the multi-step proofs (especially in
   `HungerbuhlerWasem/` where the proofs are decomposed into named tickets
   T-BR-NN, T-SC-NN, T-CC-NN).
4. `PROJECT_OVERVIEW.md` — gives the project-level narrative, the
   namespace-by-namespace LOC summary, the most-imported-leaf table, and the
   axiom audit.
5. Cited references (Hungerbühler–Wasem arXiv:1808.00997v2,
   Diamond–Shurman, Serre) — ground truth for paper notation and
   mathematical statements when the Lean docstring is terse.
6. `CONSOLIDATION_PLAN.md` and `P4_PLAN.md` — supply structural context on
   the curve-type unification, the FD-boundary canonical form, and the
   reduction history of the project.

## Conventions for Phase 4 worker outputs

* All Lean type signatures should be **unformalised** in the LaTeX:
  `(γ : ClosedPwC1Immersion x)` becomes "Let $\gamma$ be a closed piecewise
  $C^{1}$ immersion based at $x$".
* Typeclass arguments (`[FunLike F α β]`, `[NormedAddCommGroup E]`,
  `[NormedSpace ℝ E]`, decidability instances) and `Classical.propDecidable`
  injections **MUST** be dropped from the LaTeX. They are scaffolding for
  Lean, not part of the mathematical content.
* `attribute [local instance] Classical.propDecidable` and similar local
  attribute injections **MUST** be dropped.
* `noncomputable section` markers, `open ...` directives, and
  `variable {x : ℂ}`-style binder lists **MUST** be dropped.
* Variables should be in math italic: $f$, $g$, $\gamma$, not `f`, `g`,
  `gamma`. Greek letters in Lean (`γ`, `ρ`, `σ`, `θ`, `α`, `δ`,
  `ε`) become `\gamma`, `\rho`, `\sigma`, `\theta`, `\alpha`, `\delta`,
  `\varepsilon` in LaTeX.
* Mathlib structures appearing as types in the signature should be rendered
  by their **mathematical name**, not the Lean type name. Examples:
  `MeromorphicAt f s` → "$f$ is meromorphic at $s$"; `Path x y` → "a
  continuous path from $x$ to $y$"; `Finset ℂ` → "a finite set
  $S \subseteq \mathbb{C}$".
* Universal quantifiers spelled `∀` and existential `∃` in Lean become
  `\forall` and `\exists` in LaTeX. Lean's `→` between propositions is "if
  ... then ...". Lean's `↔` is "if and only if".
* Project-specific abbreviations: prefer `gWN` written
  `\operatorname{gWN}` for the generalised winding number; prefer `Res`
  written `\operatorname{Res}` for the residue; prefer `ord_p(f)` written
  `\operatorname{ord}_p(f)` for vanishing orders.
* When a Lean theorem statement is a long chain of universally-quantified
  variables and hypotheses, **break the LaTeX statement into multiple
  English sentences**: "Let $\gamma$ be a closed piecewise-$C^{1}$
  immersion based at $x$. Let $U \subseteq \mathbb{C}$ be open, and let $S \subseteq U$ be a
  finite set. Suppose ...". Avoid one-paragraph wall-of-symbols
  unformalisations.
* When citing the Hungerbühler–Wasem paper, write `Hungerbühler–Wasem` (with
  the en-dash and umlaut) and cite as "Hungerbühler–Wasem 2018, Theorem 3.3"
  on first reference; subsequent references may say "HW3.3" once the
  context is clear.
* When citing Diamond–Shurman, write "Diamond–Shurman, Theorem 3.1.1"
  (chapter 3 of *A First Course in Modular Forms*).
* When the LaTeX statement refers to a Lean structure with many fields
  (`PolarPartDecomposition`, `SingleCrossingData`, `FDWindingData`,
  `CornerFTCHyp`, etc.), give the structure a short prose explanation
  (one sentence) then bullet-list the fields if the worker is writing a
  definition. For a theorem **using** the structure, just say
  "a polar-part decomposition of $f$" / "single-crossing data for $\gamma$
  at $z_0$" / "winding-number data for $\partial \mathcal{D}_H$".
* `LeanModularForms` is the umbrella namespace; declarations inside
  `namespace HungerbuhlerWasem` are referred to in the LaTeX **without** the
  namespace prefix unless disambiguation is needed.
* Private helpers (`private theorem`, `private lemma`, `private def`)
  **MUST** receive a brief LaTeX rendering — they are part of the dependency
  graph — but the entry should explicitly note the helper status: "(private
  helper) ...". Workers may collapse a chain of trivially-named helpers
  into a single LaTeX paragraph if the structure is read-once and the
  helpers contribute no new mathematical idea.

## Known gaps / caveats

* No copy of Hungerbühler–Wasem (arXiv:1808.00997v2) or Diamond–Shurman is
  stored in `.mathlib-quality/references/` at the time of writing; workers
  should rely on the Lean docstrings (which paraphrase the relevant
  statements) and the project narrative above.
* The notational collisions between the legacy `Residue` chain
  (`ForMathlib/Residue.lean`, `ForMathlib/MultipointPV.lean`) and the new
  GRT chain (`ForMathlib/GeneralizedResidueTheory/Residue.lean`,
  `ForMathlib/GeneralizedResidueTheory/Residue/MultipointPV.lean`) are
  intentional: both define `HasSimplePoleAt`, and both define
  `disjoint_balls_of_small_epsilon`. `HungerbuhlerWasem.lean` commits to the
  legacy chain; the valence-side `ResidueSideInfra` uses the GRT chain. When
  describing one of these duplicates, prefer the namespace-qualified name
  (`HungerbuhlerWasem.PolarPartDecomposition`, `GeneralizedResidueTheory.Residue.HasSimplePoleAt`,
  …) in the LaTeX prose so readers can disambiguate.
* The free-interval `PiecewiseC1PathOn a b hab x y` co-exists with the
  unit-interval `PiecewiseC1Path x y`. Both forms appear in the dependency
  closure. Workers should follow the rule: if the statement uses the
  parametrisation interval $[0,1]$, write "piecewise-$C^{1}$ path on the
  unit interval"; if the parametrisation interval is free $[a,b]$, write
  "piecewise-$C^{1}$ path on $[a, b]$". The `extends` chain is
  `PwC1Immersion` → `PiecewiseC1Path` → `PiecewiseC1PathOn 0 1 _`. For
  closed forms: `ClosedPwC1Immersion x` → `ClosedPwC1Curve x` →
  `PiecewiseC1Path x x`.
* `ValenceFormula.lean` (the orbit-sum form, conditional on
  `valence_formula_orbit_sum`) and `ValenceFormulaBridged.lean` (the
  unconditional in-FM-chain form) form a two-step bridge to
  `ValenceFormulaFinal.lean`. The final theorem invokes
  `valence_formula_textbook_orbit_finsum_FM` (no `_unconditional` suffix,
  but the underlying chain is closed).
* The `FDWindingData` vs `FDWindingDataFull` distinction: `FDWindingData`
  carries the interior + 3 elliptic winding numbers ($-1, -1/2, -1/6, -1/6$);
  `FDWindingDataFull` additionally requires the smooth-boundary winding to be
  $-1/2$ at every other on-curve point. Both structures appear in the
  blueprint; their statements differ only by the additional smooth-boundary
  field.
* Numbered tickets in Lean docstrings (T-BR-NN, T-SC-NN, T-CC-NN, T-AR-01,
  T-CC-01, T-BR-Y5/6/9, T-GL-01, T-LE-01, T-SC-00a, T-SC-01) are the
  project's internal decomposition labels. Workers should **not** propagate
  these into the LaTeX (they are blueprint-irrelevant). Instead, use prose:
  "the per-pole CPV composition theorem", "the sector-cancellation
  identity under condition (B)", "the multi-pole DCT lift", etc.
* The HW33-side and valence-side share the following base modules: the
  `Path`-bundled curve type chain (`PiecewiseC1Path` etc.), the residue and
  CPV definitions, `Dixon` and `NullHomologous`, and the elliptic-point
  numerics (`EllipticPoints`). Workers writing for declarations in these
  shared modules should describe the declaration **once**, with cross-links
  to both protected theorems' usage.
