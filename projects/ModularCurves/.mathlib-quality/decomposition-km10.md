# Decomposition — T-IRR0: geometric irreducibility `yRho_geometricallyIrreducible`

*`/develop --decompose` (adversarial, planning-only) for stream IRR. Source read at decompose
time from `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf` (Katz–Mazur, *Arithmetic
Moduli of Elliptic Curves*, Annals 108, 1985), Chapter 10 "THE CALCULUS OF CUSPS AND COMPONENTS
VIA THE GROUPS T[N] AND THE GLOBAL STRUCTURE OF THE BASIC MODULI PROBLEMS", pp. 286–338. Page
offset: PDF page = book page + 11. All quotes below are transcribed verbatim from the pages, not
from memory. NO tickets created; NO held file edited.*

## Target

`ModularCurves.yRho_geometricallyIrreducible` (`ModularCurve/YRho.lean:467`):

```lean
theorem yRho_geometricallyIrreducible {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (D : GaloisRepData N) (Y : Scheme.{0}) (sY : Y ⟶ Spec (.of ℚ))
    (hY : RepresentsYRho D Y sY) :
    IrreducibleSpace ↥(pullback sY
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) := by sorry
```

i.e. any curve `Y` representing the `ρ`-level moduli problem over `ℚ` (predicate `RepresentsYRho`,
which supplies `SmoothOfRelativeDimension 1 sY` and `IsAffineHom sY`) has irreducible base change to
`ℚ̄`. Consumer: `T-F5` (BB-IRR). Buzzard sanctions sorrying this ("see 1980s"); the owner directs
planning it anyway (late-phase, parallel).

## Skeleton location

`ModularCurve/IrreducibilityScoping.lean` (NEW). `lake build
ModularCurves.ModularCurve.IrreducibilityScoping` passes (sorries only). Contains the tractable
leaves `irreducibleSpace_of_connectedSpace_of_smooth` (L1) and `connectedSpace_quotient_orbitRel`
(L4), and the master reduction `yRho_geometricallyIrreducible_of_connected`. The analytic gaps
L2/L3/L5 are documented here (their objects are absent from mathlib + AINTLIB, so they are not yet
stateable in compilable Lean — that statement work is itself part of the gap's sub-development).

---

## THE decompose finding (drives the whole route choice)

**KM's Chapter 10 is the "algebraic route", but its connectedness proof is not algebraic — it uses
the transcendental (upper-half-plane) description.** Two verbatim anchors:

- §10.1 Motivation, **p. 287**:
  > "By combining this information with two other ingredients, (1) the homogeneity principle,
  > (which already played so large a role in Chapter 5), (2) the *transcendental* description of our
  > moduli spaces as quotients of the upper-half plane, (a description which we have up to now
  > avoided), used in the proof of 10.9.2, we obtain a good picture of the global structure of our
  > moduli schemes (cf. 10.9 through 10.13)."

- Cor. 10.9.2 proof, **p. 303** (the connectedness core):
  > "By the connectedness theorem, for the connectedness it suffices to show that its geometric
  > generic fiber is connected, i.e., to study the situation after the base change `Z[ζ_N,1/N] ↪ ℂ`
  > defined by, say, `ζ_N ↦ exp(2πi/N)`. To show that the smooth ℂ-curve `M̄(𝒫)⊗ℂ` is connected, it
  > suffices to show that the complement of the finitely many cusps, `M(𝒫)⊗ℂ`, is connected. But
  > this is standard, because the underlying complex manifold to `M(𝒫)⊗ℂ` is isomorphic to the
  > quotient of the upper half plane by the subgroup `Γ̃ ⊂ SL(2,ℤ)` which is the complete inverse
  > image of `Γ` by reduction mod N."

So the algebraic shell of Ch. 10 (finite-étale-Galois `SL(2,ℤ/N)`-structure over `Z[ζ_N]`; cusps
via `T[N]`) **reduces** geometric irreducibility to the connectedness of `ℍ/Γ̃`, but does not prove
it algebraically. This matches Buzzard verbatim (YRho.lean header, Buzzard TCC lecture 8 p. 33–34):
> "irreducible curve `Y(ρ̄_N)` over ℚ. NB irreducibility is proved complex-analytically by
> uniformising the ℂ-points of the curve by the upper half plane." … "Proof: See 1980s."

**Route conclusion.** The two routes are not independent — both bottom out at `Y⊗ℂ ≅ ℍ/Γ̃`
connected. Therefore the *shortest source-faithful route* to `yRho_geometricallyIrreducible` is the
analytic one (a single geometric fibre over `ℚ̄`/`ℂ`), NOT the full arithmetic KM Ch. 10 machinery
(which additionally develops the `Z[ζ_N]`-family, the `T[N]` calculus, and the mod-p component
theory that this target does not need). The KM "algebraic components via T[N]" material is
recommended **only** if a *purely algebraic* proof (geometric-monodromy surjectivity onto
`SL(2,ℤ/N)` via Tate-curve unipotent local monodromy) is later wanted to avoid complex analysis
entirely — see "Route C" below; that argument is NOT in KM and would be its own development.

---

## Plain-English proof (recommended = analytic route, following KM 10.9.2 for a single fibre)

Write `Ȳ := Y ⊗_ℚ ℚ̄` (the `pullback`). We want `Ȳ` irreducible.

1. `Y → Spec ℚ` is smooth of relative dimension 1 (`RepresentsYRho`), so `Ȳ → Spec ℚ̄` is smooth of
   relative dimension 1 (base change). A smooth scheme over a field is regular, and a regular
   scheme's connected components are irreducible; hence, `Ȳ` being nonempty and connected forces `Ȳ`
   irreducible. **⟹ reduces the target to: `Ȳ` connected.** (L1.)
2. Connectedness of `Ȳ = Y⊗ℚ̄` is unchanged under the extension of algebraically closed fields
   `ℚ̄ ↪ ℂ`: `Y⊗ℚ̄` connected ⟺ `Y⊗ℂ` connected. (L2, API gap.)
3. The analytification `(Y⊗ℂ)^an` is isomorphic, as a Riemann surface, to `ℍ/Γ̃` where
   `Γ̃ ⊂ SL(2,ℤ)` is the preimage of the `ρ`-level group under reduction mod `N` — the transcendental
   uniformisation of KM 10.9.2. (L3, API gap — the `MAJOR-INFRA` core; LeanModularForms bridge.)
4. `ℍ` (upper half plane) is connected; the quotient map `ℍ → ℍ/Γ̃` is a continuous surjection; the
   continuous image of a connected space is connected. So `ℍ/Γ̃` is connected. (L4.)
5. A `ℂ`-scheme is connected iff its analytification is connected (GAGA / analytification
   comparison). With (3)+(4): `Y⊗ℂ` connected; with (2): `Ȳ` connected; with (1): `Ȳ` irreducible. ∎
   (L5, API gap.)

---

## Lemmas (in order)

### L1 — reduce irreducibility to connectedness  ·  leaf (tractable)

- Lean declaration: `IrreducibilityScoping.lean` `irreducibleSpace_of_connectedSpace_of_smooth`.
  ```lean
  theorem irreducibleSpace_of_connectedSpace_of_smooth
      {X : Scheme.{0}} (sX : X ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
      (hsm : SmoothOfRelativeDimension 1 sX) [Nonempty ↥X] [ConnectedSpace ↥X] :
      IrreducibleSpace ↥X := by sorry
  ```
- Source: KM 10.9.2(2) works with "the smooth ℂ-curve `M̄(𝒫)⊗ℂ`" and proves *connectedness*, taking
  the smooth-curve ⟹ (connected ⟺ irreducible) step as standard. Standard-text anchor: Hartshorne
  II.3 (a scheme is irreducible iff nonempty + connected + all local rings have a unique minimal
  prime; smooth/regular gives the latter).
- Source claim (verbatim, KM p. 303): "M̄(𝒫)⊗ℂ is *connected*" is what KM proves for a scheme
  already known to be "a proper *smooth* curve"; the identification of connected smooth with
  irreducible is used implicitly throughout Ch. 10 (e.g. "geometrically connected fibers", 10.9.2(2)
  title).
- Lean ↔ source match: `hsm : SmoothOfRelativeDimension 1 sX` is "smooth curve over `ℚ̄`";
  `ConnectedSpace ↥X` is KM's "connected"; `IrreducibleSpace ↥X` is the geometric irreducibility the
  target wants. The lemma is the "smooth + connected ⟹ irreducible" step KM leaves implicit.
- Discharged by (planned): mathlib `regular ⟹ irreducible components = connected components`. Search
  status: `smooth ⟹ regular` is `AlgebraicGeometry` (`IsSmooth`/`Smooth` → `IsRegular`, verify exact
  name at execution); `IrreducibleSpace` from `ConnectedSpace + PreirreducibleSpace` via unique
  generic points on a regular scheme. Small composition, but the exact mathlib lemma chain for
  "regular scheme: connected ⟹ irreducible" must be pinned at execution (candidate: irreducible
  components are the closures of the minimal primes; on a regular — hence normal — scheme they are
  disjoint, so connected ⟹ one component). **≤ a handful of lemmas; genuinely tractable.**
- Attacks attempted:
  - [1] Counterexample search: is "smooth connected ⟹ irreducible" false? Over a field, a
    *disconnected* regular scheme (`Spec(k×k)`) is reducible — but that needs disconnected, excluded
    by `ConnectedSpace`. A connected non-reduced scheme can be irreducible-or-not, but smooth ⟹
    reduced. No counterexample among smooth connected `k`-schemes.
  - [2] Edge cases: `X = Spec ℚ̄` (dim 0 smooth, connected) → irreducible ✓ (a point). `X` empty →
    excluded by `[Nonempty ↥X]` (an empty space is connected-vacuously in some conventions but not
    `ConnectedSpace`, which requires nonempty; and irreducible requires nonempty — consistent).
    Relative dimension 1 vs the `Spec ℚ̄` dim-0 edge: the lemma statement doesn't actually need
    `dim = 1`, only regularity; keeping `SmoothOfRelativeDimension 1` is faithful to the target but
    over-specifies — flagged, not fatal (a `hsm`-generalisation to any relative dimension is a
    `/generalise` item, not a blocker).
  - [3] Hypothesis test: drop `ConnectedSpace` → false (`Spec(ℚ̄[x]) ⊔ Spec(ℚ̄[x])`). Drop
    `Nonempty` → false (`IrreducibleSpace` requires nonempty). Drop smoothness → false (`Spec
    ℚ̄[x,y]/(xy)` is connected, reduced even, but reducible; it is *not* regular at the origin). All
    three hypotheses necessary. No hidden typeclass beyond `Scheme`/field.
  - [4] Source-drift attack: the Lean claim is exactly KM's "smooth ⟹ (connected ⟺ irreducible)"
    over the algebraically closed `ℚ̄`; KM works over `ℂ` but connectedness/irreducibility of a
    finite-type scheme over an algebraically closed field is invariant under alg-closed extension
    (see L2). No drift.
  - [5] Discharge attack: "regular ⟹ components disjoint" — mathlib has `UniqueFactorizationMonoid`/
    normal-domain infrastructure and `IrreducibleSpace` API; the exact one-liner is not yet pinned
    (hence "leaf, tractable" not "leaf, discharged"). Marked for a `lean_loogle`/`lean_leansearch`
    pin at ticket time; if the composition exceeds 3 lemmas it becomes a small internal node — still
    tractable. Verdict: SURVIVED; tractable leaf, discharge to pin at execution.

### L4 — connectedness of `ℍ/Γ̃`  ·  leaf (tractable, mathlib)

- Lean declaration: `IrreducibilityScoping.lean` `connectedSpace_quotient_orbitRel`.
  ```lean
  theorem connectedSpace_quotient_orbitRel
      {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
      {G : Type*} [Group G] [MulAction G X] :
      ConnectedSpace (Quotient (MulAction.orbitRel G X)) := by sorry
  ```
- Source: KM 10.9.2 proof, p. 303 (quoted above): connectedness of `M(𝒫)⊗ℂ` follows because it "is
  isomorphic to the quotient of the upper half plane by the subgroup `Γ̃ ⊂ SL(2,ℤ)`". The
  *connectedness* of that quotient is the elementary fact that the upper half plane is connected and
  a quotient of a connected space is connected.
- Lean ↔ source match: `X := ℍ` (mathlib `UpperHalfPlane`, connected via
  `LocallyPathConnectedSpace ℍ` + convexity of the half-plane), `G := Γ̃`. `Quotient (orbitRel G X)`
  is the orbit space `ℍ/Γ̃`. The lemma isolates the *only* property of `ℍ/Γ̃` KM's argument uses.
- Discharged by (planned): `ConnectedSpace` is preserved by continuous surjections;
  `Quotient.mk` is continuous and surjective. mathlib: `IsPreconnected.image`,
  `Quotient.surjective_Quotient_mk''`, `continuous_quotient_mk`; assemble
  `PreconnectedSpace (Quotient …)` + nonempty. **Fully in mathlib.**
- Attacks attempted:
  - [1] Counterexample search: quotient of connected is disconnected? Impossible — continuous image
    of connected is connected; `Quotient.mk` is continuous surjective. No counterexample.
  - [2] Edge cases: `G` trivial → quotient ≅ `X`, connected ✓. `X` a single point → quotient a
    point, connected ✓. `G` acting with a single orbit → quotient a point ✓.
  - [3] Hypothesis test: drop `ConnectedSpace X` → false (quotient of a disconnected space by the
    trivial group is disconnected). `Group G` can be weakened to `Monoid`/any `MulAction`/even any
    surjection — over-specified but harmless (we only need `ℍ/Γ̃`, `Γ̃` a group); a generalisation to
    a plain quotient-by-a-relation is a `/generalise` item.
  - [4] Source-drift attack: KM claims the *complex manifold* is `ℍ/Γ̃`; our Lean claim is only the
    connectedness of the abstract quotient space, which is strictly weaker (topology only, no complex
    structure) and is exactly the part of KM's sentence that closes connectedness. No drift; if
    anything, deliberately narrower than the source (correct — we need less).
  - [5] Discharge attack: `IsPreconnected.image` exists (`Mathlib.Topology.Connected.Basic`);
    `Quotient.mk` continuity + surjectivity are standard. Composition ≤ 3 lemmas. `ConnectedSpace ℍ`
    itself: mathlib has `LocallyPathConnectedSpace ℍ` (`UpperHalfPlane/Topology.lean:72`) and `ℍ` is
    convex ⟹ path-connected ⟹ connected — pin the exact instance at execution (likely
    `inferInstance` or one convexity lemma). Verdict: SURVIVED; tractable mathlib leaf.

### MASTER — `yRho_geometricallyIrreducible_of_connected`  ·  internal (assembly of L1 + base change)

- Lean declaration: `IrreducibilityScoping.lean` `yRho_geometricallyIrreducible_of_connected`
  (mirrors the target but adds the hypothesis `hconn : ConnectedSpace ↥(Ȳ)`).
- Composition: base-change smoothness (`SmoothOfRelativeDimension 1 sY` ⟹ same for `pullback.snd`)
  + L1. This is the algebraic reduction; it isolates ALL analytic content into `hconn`.
- Source: the reduction is exactly KM 10.9.2's move "for the connectedness it suffices to show …
  geometric generic fiber is connected" specialised to the single geometric fibre `Ȳ` (we do not
  need the `Z[ζ_N]`-family, so the "connectedness theorem" spreading-out step is replaced by working
  directly at `ℚ̄`).
- Attacks (composition): could L1 + base-change-smoothness be true yet the master false? Only if
  `pullback.snd` failed to be smooth of rel. dim. 1 — but smoothness is stable under base change
  (mathlib `MorphismProperty.StableUnderBaseChange` for `Smooth`), and `Ȳ` is nonempty because `Y`
  is (representing a nonempty moduli problem; `RepresentsYRho` gives a `T`-point over `ℚ̄` from the
  identity, so `Ȳ` is nonempty — pin at execution). No composition gap. `hconn` is deliberately a
  hypothesis: the master is HONEST that connectedness is imported, not proved here.

---

## API gaps (analytic core — `MAJOR-INFRA`; absent from mathlib AND AINTLIB per ecosystem-survey)

### L2 — geometric connectedness is insensitive to `ℚ̄ ↪ ℂ`

- Claim: for a finite-type `ℚ̄`-scheme `X`, `ConnectedSpace (X⊗ℚ̄)` ⟺ `ConnectedSpace (X⊗ℂ)`.
- Source: standard (EGA IV 4.5.x / Stacks 0363 "geometrically connected is insensitive to further
  algebraically closed extension"); used implicitly when KM base-changes `Z[ζ_N,1/N] ↪ ℂ`.
- Status: mathlib has `Scheme.pullback` and some geometric-connectedness API for *varieties over a
  field*, but the "extension of algebraically closed base fields preserves connectedness" statement
  for schemes is **not present**; this is a real sub-development (spreading out / limit of the
  connectedness locus, or the number-of-connected-components base-change lemma). Sub-tree: (a)
  connected components of `X⊗k` are geometrically connected; (b) `π₀` is invariant under
  `k ↪ k'` for `k, k'` alg. closed. **Own mini-project.**

### L3 — transcendental uniformisation `(Y⊗ℂ)^an ≅ ℍ/Γ̃`  ·  **the core, `MAJOR-INFRA`**

- Claim: the analytification of `Y⊗ℂ` (an algebraic curve) is isomorphic as a Riemann surface to
  `ℍ/Γ̃`, `Γ̃` = preimage of the `ρ`-level group in `SL(2,ℤ)`.
- Source: KM 10.9.2, p. 303 (verbatim above); the full construction is the classical analytic theory
  of modular curves (Shimura *Introduction to the Arithmetic Theory of Automorphic Functions* Ch. 1;
  Diamond–Shurman Ch. 2–3). KM calls it "standard" and "a description which we have up to now
  avoided" — i.e. deliberately outside their algebraic development.
- Status: requires (i) the analytic modular curve `ℍ/Γ̃` as a Riemann surface with its moduli
  interpretation via the analytic family `ℂ/(ℤ+τℤ)` over `ℍ` and level structures — the
  **LeanModularForms** bridge; (ii) analytification of a `ℂ`-scheme (a functor `Scheme/ℂ ⤳
  ComplexAnalyticSpace`) — **absent from mathlib**; (iii) the identification of the two moduli
  interpretations (algebraic `Y(ρ)(ℂ)` ↔ analytic `ℍ/Γ̃`). This is the single biggest piece and the
  reason BB-IRR "likely stays a registered assumption longest" (black-box-plan.md). Sub-tree is a
  multi-component development in its own right; NOT decomposed further here (a decompose pass on L3
  alone is a separate `/develop --decompose` once the analytic objects exist).

### L5 — GAGA connectedness comparison

- Claim: a `ℂ`-scheme `X` of finite type is connected (Zariski) iff `X^an` is connected (analytic).
- Source: GAGA (Serre, *Géométrie algébrique et géométrie analytique*); Stacks "analytification"
  chapter. Standard, but needs the analytification functor of L3(ii).
- Status: depends on L3's analytification infrastructure; **absent from mathlib**. Own sub-step once
  analytification exists (the connectedness direction is the easy half of GAGA — comparison of `π₀`).

---

## Prior-B2 log consultation

`.mathlib-quality/b2_log.jsonl`: not present in the worktree (no prior beastmode B2 on this project
recorded here). The one *known* prior scope correction on this target is **DEF-6**
(`decomposition-2026-07-05-phase1.md:350`): the earlier `yRho_geometricallyIrreducible` quantified
over ALL smooth relative curves (with `D` unused) and was **false** (`ℙ¹ ⊔ ℙ¹` counterexample); it
was corrected to be conditional on `RepresentsYRho`. The current target (YRho.lean:467) already
carries that fix (`hY : RepresentsYRho D Y sY` is a hypothesis). **Addressed.** Every leaf above is
stated relative to the representing curve, so the `ℙ¹ ⊔ ℙ¹` counterexample (two components, not
representing the moduli problem) is excluded at L1 by the smoothness+representability of `Y` and does
not reappear.

---

## Feasibility assessment

The target decomposes cleanly into a small **tractable algebraic shell** (L1 reduce-to-connected, L4
`ℍ/Γ̃`-connected, MASTER assembly) and a large **analytic core** (L2 alg-closed-base-change, L3
uniformisation `(Y⊗ℂ)^an ≅ ℍ/Γ̃`, L5 GAGA). The shell is genuinely buildable now against mathlib +
the project (L1, L4, MASTER are stateable and their discharges are ≤ a few mathlib lemmas). The core
is **`MAJOR-INFRA`**: L3 requires the complex-analytic modular-curve theory (LeanModularForms bridge)
*and* a scheme-analytification functor absent from mathlib, and L2/L5 require geometric-connectedness
base-change / GAGA comparison also absent. No purely-algebraic KM route avoids this: KM 10.9.2 itself
uses the transcendental description (the decompose finding above). A genuinely complex-analysis-free
proof would need **Route C** — geometric-monodromy surjectivity onto `SL(2,ℤ/N)` via Tate-curve
unipotent local monodromy (KM 10.8.2 gives the local `(1 f_i; 0 1)` monodromy; generation of
`SL(2,ℤ/N)` by these unipotents forces connectedness) — which is NOT in KM and is its own
multi-session development on top of the `T[N]`/Tate-curve infrastructure (KM Ch. 8–10).

**Recommendation.** Keep BB-IRR a registered assumption (Buzzard-sanctioned) for now; land the
tractable shell (L1, L4, MASTER) so the reduction is on record and the only remaining `sorry` is the
clearly-labelled analytic `hconn`. Schedule the analytic core (L3) as a dependent stream once the
LeanModularForms uniformisation bridge and a scheme-analytification functor exist — i.e. this stays
latest-phase, exactly as `black-box-plan.md` predicted. Route C is the alternative if a
complex-analysis-free formalisation is later mandated.

## Next step

This is `--decompose` (planning-only) — no tickets created. When the shell is approved, a `/develop`
(full) / `/develop --continue` pass would ticket L1, L4, MASTER (shell, buildable now) and file
L2/L3/L5 as `MAJOR-INFRA` API-gap streams (L3 gated on the LeanModularForms analytic bridge). Update
`plan.md`'s IRR row + `black-box-plan.md` BB-IRR with this finding (KM's algebraic route is not
analytic-free) and the shell/core split.
