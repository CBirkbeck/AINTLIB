# Decomposition: `twoCurveGeometricDualData` (DualDescent.lean:1590) — the sole residual

*Source-faithful pass against Silverman, *The Arithmetic of Elliptic Curves* 2nd ed., read
verbatim from `refs/HasseWeil/Silverman-Arithmetic_of_EC.pdf` (PDF page = book page + 18) on
2026-06-17. NOT from memory.*

## What the residual is

`TwoCurveGeometricDualData φ` (φ : EC.Isogeny W₁ W₂, char-0 F, separable) must produce, over a
finite Galois `L ⊆ K̄ = AlgebraicClosure F`:
- `βL : HasseWeil.Isogeny (W₁.baseChange L) (W₂.baseChange L)` — a **points-bearing** realization
  (Basic-world Isogeny = `pullback` + `toAddMonoidHom`, two independent fields, Basic.lean:61).
- `h_pbL : βL.pullback = (bcIsog W₁ W₂ φ L).toCurveMap.pullback` — βL realizes the ofEquation
  base-change `bcIsog` (DualDescent.lean:1191, built via `EC.Isogeny.ofEquation`, CoordHom-free).
- `h_xy_family` — kernel-translation covariance on `x_gen₂/y_gen₂`.
- `h_card : Nat.card βL.kernel = βL.degree`.
- `h_deg : βL.degree = φ.degree`, `h_mPbL` (mulByInt base-change identification).

Everything downstream (`twoCurveKbarRangeInclData_of_geometric`, `TwoCurveFixedField.lean`,
`TwoCurveDualRange.lean`, the L→F Galois descent DUAL-Q1, the field-of-definition MOVE 1,
`HasDualWitness` via `factorThrough`) is **already PROVEN axiom-clean**.

## Why this is exactly Silverman's argument (verbatim anchors)

### `h_xy_family` = Silverman III.4.10(b), book p.73

> "First, if T ∈ ker φ and f ∈ K̄(E₂), then  τ_T*(φ*f) = (φ∘τ_T)*f = φ*f,  since φ∘τ_T = φ.
> Hence as an automorphism of K̄(E₁), the map τ_T* fixes φ*K̄(E₂) …"

`h_xy_family` is the `f = x_gen₂` and `f = y_gen₂` cases: `τ_T*(βL.pullback x_gen₂) = βL.pullback
x_gen₂` for `T ∈ ker βL`. Silverman gets it **free** from contravariant functoriality
(`τ_T*∘φ* = (φ∘τ_T)*`) + the geometric identity `φ∘τ_T = φ`. The project's `Isogeny` carries
`pullback` and `toAddMonoidHom` as **independent** fields, so functoriality is NOT free — the
point-map↔pullback bridge (`PullbackEvaluation` + the separation lemma) is exactly what recovers
Silverman's free step.

### `h_card` = Silverman III.4.10(c), book p.73

> "If φ is separable, then from (a) we see that #φ⁻¹(Q) = deg φ for all Q ∈ E₂. Hence φ is
> unramified … #ker φ = deg φ, … K̄(E₁)/φ*K̄(E₂) is a Galois extension."

### The downstream range inclusion = Silverman III.6.1(a) Case 1 + III.4.11, book pp.74, 81

III.6.1(a), φ separable: "#ker φ = m, so every element of ker φ has order dividing m, i.e.
ker φ ⊂ ker[m]. It follows immediately from (III.4.11) that there is an isogeny φ̂ : E₂→E₁
satisfying φ̂∘φ = [m]." III.4.11's field inclusion `[m]*K̄(E₁) ⊂ φ*K̄(E₂) ⊂ K̄(E₁)` is the
project's `hLincl : Im([m]*) ⊆ Im(φ*)` (over L). PROVEN two-curve in TwoCurveDualRange.

### Descent L→F = III.6.2(c) footnote 1, book p.83

> "¹This is where we use the characteristic 0 assumption, since all of our results on elliptic
> curves have assumed that the base field is perfect."

The project formalizes the implicit descent via DUAL-Q1 (function-field Galois descent) + MOVE 1
(field of definition). PROVEN axiom-clean.

## The deep core: the point-map realization (Silverman III.4.8, general isogeny)

`bcIsog` is built by `ofEquation` from explicit coordinate functions
`u = bcXgen, v = bcYgen ∈ K(E₁_L)` with `bcIsog.pullback (x_gen₂) = bcXgen`,
`bcIsog.pullback (y_gen₂) = bcYgen` (DualDescent.lean:1199/1205). `ofEquation` gives ONLY the
function-field pullback + basepoint — **no point map**. The point map must be constructed.

Natural construction: `βL.toAddMonoidHom : P ↦ (bcXgen(P), bcYgen(P))` (evaluate the coordinate
functions). Then:
- The **two-curve `PullbackEvaluation` coherence is near-tautological**: `bcXgen` evaluates at `P`
  to `bcXgen(P)` by definition of `EvaluatesTo`; the evaluated point lies on E₂_L by `ofEquation`'s
  `h_eqn` (the equation witness). `bad` = poles of `bcXgen/bcYgen` = the affine kernel (finite).
- The **WALL is the group-hom property** (Silverman III.4.8): `P ↦ (bcXgen(P), bcYgen(P))` respects
  addition. This is the project's standing "geometric realization" gap for a GENERAL isogeny
  (existing PullbackEvaluation witnesses — [n] via division polys, Frobenius via frobeniusCoordHom,
  1−π via the addition formula — all rest on SPECIFIC coordinate formulas; a general φ has none).

## Leaf plan (ordered)

- **PE-0** `PullbackEvaluation_twoCurve (β : Isogeny W₁ W₂) (bad) : Prop` — the two-curve def
  (`EvaluatesTo W₁ P (β.pullback (x_gen W₂)) x'` is single-curve on E₁; the point lands in E₂).
  Trivial, ~10 LOC.
- **PE-1a** the evaluation point map + near-tautological `PullbackEvaluation_twoCurve βL bad`
  witness with `bad` finite. Tractable GIVEN a point map; the obstruction is making it an
  `AddMonoidHom` (needs PE-1b).
- **PE-1b** (THE WALL) the evaluation map is a group hom (Silverman III.4.8, general). Candidate
  routes for a worker to explore: (i) via Pic⁰ (`picZeroIsoE_allChar` + divisor-pullback dual is
  a group hom by construction; identify the evaluation map with it); (ii) the addition formula
  directly; (iii) place-restriction comorphism + rigidity. **Deepest leaf; spawn its own
  sub-development.**
- **PE-2** `h_xy_family` from PE-0/PE-1 via the **single-curve** separation lemma
  `eq_of_evaluatesTo_cofinite` (GenericCovarianceGeneral.lean:267) + `evaluatesTo_translate`
  (L302), both reusable as-is (both functions live in K(E₁), evaluated on E₁ points). At good P:
  RHS↦x'(βP); LHS=τ_k(...)↦x'(β(P+k))=x'(βP+βk)=x'(βP) since βk=0. ~120 LOC.
- **PE-3** `h_card` via `card_kernel_eq_degree_of_separable_witness` (IsogenyKernel.lean:357,
  two-curve) — needs Finite kernel + hsep + hfin + a fiber witness `∃P₀, #fiber = sepDegree`
  (= III.4.10a). Fiber finiteness from `PullbackEvaluation.finite_fiber` (two-curve port).
- **PE-4** `h_deg` (base-change preserves degree), `h_mPbL` (mulByInt base-change) — plumbing.
- **PE-5** choose `L` = finite Galois closure of the kernel field of φ; assemble.

## Honest scope

PE-1b is the genuine wall — the geometric realization of a general isogeny's point map as a group
hom (III.4.8). It is deep *within* the project's area (the project did it for [n]/Frob/1−π via
specific formulas), NOT off-track. The Pic⁰ route (i) is the most promising: the project HAS
`picZeroIsoE_allChar` and a divisor-pullback group-hom dual; the task is to identify the
evaluation point map with the Pic⁰-induced map. This is the marathon's target.

## Crystallized assembly architecture (2026-06-17)

The `DescentData`/`SomeDescentData` chain (DualDescent.lean:786/845) is over a finite Galois `L`
(a `Type`). **PE-5 (the L-choice) is already discharged by MOVE 1**:
`exists_finiteGalois_fieldOfDefinition` (DualDescent.lean:914) places any finite set of K̄-elements
in a finite Galois `L ⊆ K̄`; apply it to the kernel-point coordinates. So PE-5 reduces to
identifying the kernel — which needs PE-1.

Cleanest build order:
1. **PE-1 over K̄ = AlgebraicClosure F**: realize `bcIsog_K̄` as a group-hom point map (PE-1b, THE
   WALL) + `PullbackEvaluation_twoCurve` witness (PE-1a, near-tautological given the map). Over
   alg-closed K̄ the kernel is finite with `#ker = deg` automatic, and `h_card` is cleanest.
2. **PE-5**: `L :=` MOVE-1 field of definition of the (finite) kernel coords. Descend the
   realization K̄ → L (point map + PE witness restrict, since `bcIsog` is already over `L`).
3. Over `L`: `βL` with `#ker βL = deg` (L splits the kernel), `h_xy_family` (PE-2, Worker A),
   `h_card` (PE-3).
4. Assemble `TwoCurveGeometricDualData` (the L, βL, h_pbL, h_xy_family, h_card, h_deg, h_mPbL).

## Execution state (2026-06-17)

- Worker A (`lean4-sorry-filler-deep`, bg): building `WeilPairing/TwoCurveGenericCovariance.lean` =
  PE-0 (`PullbackEvaluation_twoCurve` def) + PE-2 (`xy_family_of_pullbackEvaluation_twoCurve`,
  sorry-free, via the reusable single-curve separation). Foundation/de-risk.
- Worker B (Explore, bg): ranking PE-1b group-hom routes (Pic⁰ / addition-formula / existing) +
  verdict on the `h_card` fiber-count witness (III.4.10a) availability.
- NEXT after reports: commit Worker A's engine; pick PE-1b route; build PE-1 over K̄; assemble.

## PE-1b route resolution (2026-06-17, verified against the actual code, NOT agent optimism)

Worker B proposed the Pic⁰ pushforward route as "EXTREMELY HIGH feasibility." **Scrutiny refutes
the shortcut**: `Curves/PicZeroPushforward.lean:36` `pushforwardProjectiveDivisor φ cd` is DEFINED
as `Finsupp.mapDomain (fun P => (φ.toPointMap cd P).toProjectiveSmoothPoint)` — i.e. it (a) requires
a `CoordHom cd` (which affine-kernel `bcIsog` LACKS — the project's standing obstruction) and (b) is
built FROM the point map, so it cannot CONSTRUCT one (circular). The existing Pic⁰ pushforward is
useless for PE-1b.

Likewise `AddHomProperty_of_picZero_witnesses` (HomProperty.lean:165) is typed with a `CoordHom`
argument → also CoordHom-gated. And RouteC (TheoremOfSquare / AddFormula) is `.md` inventory only,
no `.lean`. **Conclusion: PE-1b has NO shipped shortcut.** Every viable route needs NEW AG infra:
- (A) CoordHom-free divisor pushforward via the **field norm** Div(E₁)→Div(E₂) (place-restriction
  with residue weights, from the function-field extension `bcIsog.pullback`, no point map); then the
  Pic⁰-induced point map `κ₂∘norm∘κ₁⁻¹` is group-hom-FREE; prove PullbackEvaluation coherence.
- (B) point map via PullbackEvaluation (bad = kernel) + addition-formula group-hom (III.4.8 from
  scratch).
- (C) function-field kernel `G = {P : τ_P fixes Im(φ*)}` (h_xy_family automatic) + `#G = deg`
  via Galois normality — but requires reworking the (proven) TwoCurveDualRange/FixedField to a
  G-keyed kernel, and #G=deg still bottoms at III.4.10a (fiber count).

`h_card` is the lesser wall: `fiber_witness_of_ker_card_eq_sepDegree` (IsogenyKernel.lean:330)
reduces it to `#ker = sepDegree`, but that still needs the realized kernel.

**Honest classification:** PE-1b = the geometric realization of a GENERAL CoordHom-free isogeny
(Silverman III.4.8 + III.4.10a), two-curve. Deep WITHIN the project's area (core isogeny theory),
NOT off-track, but a genuine multi-file new-infrastructure development — the single largest remaining
piece, deliberately avoided in the Hasse work (which used [n]/Frob/1−π with explicit coordinate
formulas). Route (A) (norm pushforward → group-hom-free Pic⁰ point map) is the cleanest because it
makes the group-hom property free.

## DEFINITIVE SPINE FINDING (2026-06-17) — III.4.8 IS proven, but CoordHom-gated

The project HAS the Silverman III.4.8 spine, more than first thought:
- `EC.Isogeny.addHomProperty` (GroupHom.lean:66): III.4.8 (group-hom), **two-curve**, over
  `[IsAlgClosed F]`, **given `cd : φ.toCurveMap.CoordHom`** — via the Pic⁰ diagram chase.
- `addHomProperty_descend` / `toBasicIsogenyOfCoordHom` (GroupHomDescend.lean:213/185):
  III.4.8 over a general base field + the `EC.Isogeny → HasseWeil.Isogeny` promotion — but
  **single-curve (W→W) and CoordHom-gated**.
- Field/ideal norm `Ideal.relNorm` + norm–conorm `pushforward_preserves_principal`
  (PushforwardDivisor.lean:1096) + Pic⁰ `κ` (`picZeroIsoE_allChar`) — the full II.3.6/III.3.4
  spine — but the divisor pushforward `pushforwardDivisorVal` is realized via the **place-image
  map `P ↦ toPointMap cd P`**, i.e. **CoordHom-gated**.

**THE WALL, precisely:** every spine piece needs a `CoordHom`; affine-kernel `bcIsog` (deg m>1 ⟹
m−1 affine kernel points = poles of `bcXgen`) has NONE. So none of the shipped III.4.8 applies to
`bcIsog`. PE-1 = make the realization **CoordHom-free for the affine-kernel case**. The project did
this only for `[n]` (CovarianceDischarge, via the division-polynomial coordinate formula — hom-ness
is FREE since `[n]` = `zsmul`) and for `1−π` (addition formula); a GENERAL isogeny has neither.

Why symmetry needs MORE than Hasse did: the Hasse bound used the **abstract divisor dual**
`δ = κ∘φ*∘κ⁻¹` (an `AddMonoidHom`, `weilScales_of_dualComp`), which never needed a geometric
realization. But `IsIsogenous = Nonempty (EC.Isogeny)` needs an actual **CurveMap** dual; that comes
from `factorThrough` on the range inclusion `Im([m]*) ⊆ Im(φ*)`, whose K̄-proof (fixed-field) needs
the kernel realized — hence the geometric point map. This is the irreducible new input.

**Route forward (A, refined):** build a CoordHom-FREE divisor pushforward on `Pic⁰` via `relNorm` /
place-restriction (the comap of maximal ideals — no point map), descend it to `Pic⁰` (norm preserves
principal, CoordHom-free version of `pushforward_preserves_principal`), then `κ₂∘(it)∘κ₁⁻¹` is a
group-hom point map (FREE); prove PullbackEvaluation coherence (it realizes `bcIsog.pullback`); then
`h_card` via `#ker = sepDeg` (over K̄, separable) + `fiber_witness_of_ker_card_eq_sepDegree`.

This is the project's single largest remaining piece — a genuine multi-file new-infrastructure
development, deep WITHIN the project's area (core isogeny theory), NOT off-track. Grinding it is the
marathon; it spans well beyond a single session. Foundation in flight: Worker A's PE-2 covariance
engine (reusable, lands first).

## CONSOLIDATED STATUS (2026-06-17) — PE-1b is the SOLE remaining wall

Committed this session: aafa54c (fixed-field milestone), 729e8eb (PE-2 covariance engine,
TwoCurveGenericCovariance.lean), 81db557 (PE-1a point-image realization, TwoCurvePointImage.lean,
Route I + Route II, CoordHom-free, axiom-clean).

Per-leaf status:
- **PE-1a** (point-IMAGE realization + PullbackEvaluation coherence): ✅ DONE (81db557). Route II
  (residue values exist → satisfy E₂ eqn → nonsingular E₂ point) bypasses the place→point/e=1 wall.
- **PE-1-pointmap** (concrete `placeRestrictionPointMap` E₁→E₂ + free witness): worker building
  (Task A, bounded — all ingredients sorry-free).
- **PE-1b** (group-hom, Silverman III.4.8, CoordHom-FREE): ⛔ THE SOLE WALL. Project HAS it
  CoordHom-GATED (GroupHom.lean `addHomProperty` via `AddHomProperty_of_AFInputs` Pic⁰ diagram chase
  + `pushforward_preserves_principal`). Route: re-wire the diagram chase with `placeRestrictionPointMap`
  in place of `toPointMap cd` — CoordHom-free divisor pushforward (mapDomain) + CoordHom-free
  norm–conorm (the relNorm content is CoordHom-free; re-wire the place-image via PE-1a Route-I
  `twoCurve_evaluatesTo_of_comap_eq` / comap_pointValuation place equality) + the diagram chase.
- **PE-2** (h_xy_family): ✅ DONE (729e8eb).
- **PE-3** (h_card, #ker βL = deg): ✅ TRACTABLE — two-curve port of
  `card_kernel_eq_degree_of_separable` (KernelCountGeneral.lean:71). The single-curve ≤-direction
  uses the FULL `mapTranslateGenericPoint` engine ONLY as a convenience to get `hcov` (kernel
  covariance, all z); the two-curve port gets `hcov` from the committed PE-2
  (`xy_family_of_pullbackEvaluation_twoCurve` on x_gen/y_gen ⟹ all z, since τ_k is an F-algebra hom
  fixing the generators of Im(β.pullback)). The ≥-direction uses `LocalizedDictionary` (already
  two-curve). So PE-3 = a parametric port, no new deep input.
- **PE-4** (h_deg, h_mPbL): plumbing — base-change of degree + mulByInt.
- **PE-5** (L-choice): MOVE 1 `exists_finiteGalois_fieldOfDefinition` (DualDescent:914) on the
  kernel coords — given the kernel (from PE-1-pointmap).
- **Assembly** (Step C): wire βL + PE-2 + PE-3 + plumbing + L into `twoCurveGeometricDualData`.

Bottom line: the ENTIRE char-0 isogeny-symmetry goal is reduced to ONE classical statement —
**Silverman III.4.8 (group-hom) for the place-restriction point map, CoordHom-free** — plus
mechanical assembly. Everything else is done or tractable.

## FINAL REDUCTION (2026-06-17, commit a6b004b): the goal = ONE Prop

Committed: a6b004b (CoordHom-free III.4.8 Pic⁰ diagram chase). `TwoCurveGroupHom.lean` now proves
`hgrouphom` for `placeRestrictionPointMap` modulo a SINGLE named Prop:

  `PlaceRestrictionPreservesPrincipal φ` :  ∀ D principal on E₁, `placeRestrictionPushforward φ D`
  is principal on E₂   (= Silverman II.3.6/II.3.7, the norm–conorm, CoordHom-free).

`placeRestrictionRealizationOfPreservesPrincipal` yields the geometric `HasseWeil.Isogeny` directly
from this one Prop. So char-0 isogeny symmetry (UniversalDualWitness → IsIsogenous.symm) hangs on
`PlaceRestrictionPreservesPrincipal` alone (+ the tractable assembly PE-3/4/5).

### The remaining wall, precisely (verified against the code + Silverman)

`PlaceRestrictionPreservesPrincipal` = Silverman II.3.6 CoordHom-free. THREE routes:
- ✗ relNorm-at-affine-coordinate-ring (the project's `pushforward_preserves_principal`,
  PushforwardDivisor:978/1096, via `Ideal.relNorm C₂.CoordinateRing (C₁.maximalIdealAt R)`): needs
  the integral restriction `F[E₂] → F[E₁]` = a CoordHom, which a genuine isogeny LACKS.
- ✗ comap-place-equality: needs generic same-place (`comap_pointValuation_eq_of_isEquiv_of_ord_eq_one`),
  which the project has only for [n]/1−π; generic same-place recorded UNPROVABLE (FormalGroupBridge:47).
- ✓ **integral-closure route (Silverman's ACTUAL II.3.6, via II.2.6a fiber-ramification):** the
  norm–conorm over `B := integralClosure(φ*F[E₂], K(E₁))` (NOT the affine F[E₁]). B's maximal ideals
  ↔ ALL places of E₁ (including the affine kernel = the CoordHom poles). `F[E₂] → B` IS finite, so
  `Ideal.relNorm` over B works. Separable + alg-closed ⟹ every `e_φ(P)=1` (III.4.10c). The project's
  `LocalizedDictionary` (two-curve) already has the integral-closure machinery: `coordRingToClosure`
  (:360), `coordRing_mem_integralClosure` (:320), `residue_closure_bijective` (:437),
  `inertiaDeg_eq_one_of_under_eq` (:476), `exists_good_fiber_points` (:808). The dead worker assessed
  the first two routes (blocked) but NOT this one. This is the genuine route — a multi-day re-derivation
  of PushforwardDivisor's norm–conorm over B instead of F[E₁], CoordHom-free.

This is the project's standing geometric-realization wall, deep WITHIN the area (core curve theory,
II.3.6), NOT off-track. It is the one remaining piece.
