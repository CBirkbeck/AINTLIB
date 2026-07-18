# Decomposition — T-B5D (BB-DIFF): `mulByHom_formallyUnramified` + T-DISC

*`/develop --decompose` (adversarial, planning-only) for stream v10.10 (invertible-N étale
bottleneck). Sources read at decompose time: Katz–Mazur §2.3 "The structure of [N]"
(`refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`, pp. 73–75 = PDF 84–86, offset +11);
Loeffler §3.4.2(2) (quoted in `Torsion.lean:20-24`); beastmode-B's route analysis
`tb5z_architecture.md` (route (c)); HasseWeil decls verified present in-repo. All quotes verbatim.
NO held file edited (`Torsion.lean`, `GroupLawConstruction.lean` held); NEW bridge file only.*

## Target

`ModularCurves.EllipticCurve.mulByHom_formallyUnramified` (`EllipticCurve/Torsion.lean:228`, held):

```lean
theorem mulByHom_formallyUnramified (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) := by sorry
```

`[N] : E ⟶ E` (the categorical `mulByHom = (E.mulBy N).left` on the `GrpObj` structure) is formally
unramified when `N` is invertible on `S`. Discharging it removes BB-DIFF from `mulBy_etale` ⟹
`torsionπ_etale` ⟹ the whole invertible-`N` étale theory (consumers: T-B5 → T-B6 fibre chain →
T-D8-bridge → **T-E7 Y₁(N) milestone**; also T-D6c/T-D7-bridge, T-B7).

## Skeleton location

`EllipticCurve/MulByHomUnramified.lean` (NEW). `lake build
ModularCurves.EllipticCurve.MulByHomUnramified` passes (L-A, L-BC sorried; MASTER `sorry`-free
term assembly). Leaves: `formallyUnramified_mulByHom_of_torsionπ` (L-A),
`formallyUnramified_torsionπ` (L-BC), `mulByHom_formallyUnramified'` (MASTER = L-A ∘ L-BC).

---

## Mapped dead ends (from the v9.3 T-B5z finding — do NOT re-litigate)

1. **Invariant-differential / scheme `Ω¹`** (T-B5y): mathlib has NO invariant differential for
   `WeierstrassCurve` and NO relative-differentials sheaf API for schemes. This is KM's *own*
   argument ("tangent map at the origin ... multiplication by N") but it is not directly
   formalisable at current mathlib.
2. **Chart route**: `mulByHom` is the **categorical** `[N]` (`GrpObj`, `(E.mulBy N).left`), not a
   Weierstrass-chart map; the categorical-`[N]` ↔ chart-`[N]` comparison is **T-W7 scope** (A-lane).
3. **Circularity**: `torsionπ_etale ⟸ mulBy_etale ⟸ mulByHom_formallyUnramified` and T-B6
   `torsion_geometricFibre_rank_two` both consume the target — cannot be used to discharge it.

**Correction banked in the T-B5z finding (2026-07-07):** the "blocked, mathlib-only" conclusion was
superseded — AINTLIB's **HasseWeil** already has the field-level invariant-differential /
`[N]`-separability machinery. So BB-DIFF is **not blocked**; it needs the non-circular
HasseWeil-anchored route below. (Prior-B2 note: there is no `b2_log.jsonl` entry; the T-B5z record is
a *claim release with a route*, not a SCOPE/DEFINITION error — the statement is correct as stated.)

---

## Plain-English proof (KM §2.3, non-circular; = beastmode-B route (c))

Want: `[N]` formally unramified, `N` invertible on `S`.

1. **KM Cor. 2.3.2 — the torsor bridge.** `[N] : E → E` is an f.p.p.f `E[N]`-torsor (`E[N] = ker[N]`,
   `torsion N = pullback (mulByHom N) zero`). A torsor under `E[N]` is formally unramified iff `E[N]
   → S` is: two infinitesimal lifts `g₁, g₂` of `[N]` agreeing on a square-zero `T₀ ⊂ T` differ by
   `h := g₁ - g₂ : T → E` (group structure) landing in `E[N]` (`[N]∘h = 0`) with `h|T₀ = 0`; if
   `E[N] → S` is formally unramified then `h = 0`, so `g₁ = g₂`. **⟹ reduces the target to: `E[N] →
   S` formally unramified** (L-A). Uses only the `GrpObj` group structure + mathlib's
   `FormallyUnramified` (uniqueness-of-lifts) definition — self-contained, route-independent.
2. **KM Thm 2.3.1 — `E[N] → S` finite étale for `N` invertible.** `E[N] → S` is finite
   (`torsionπ_isFinite`, proven). Formal unramifiedness is checked on geometric fibres: for `k̄`
   algebraically closed with `char k̄ ∤ N`, `E[N]_{k̄}` is étale because "the tangent map [of `[N]`]
   at the origin [is] multiplication by `N`" (KM p. 74 / Loeffler 3.4.2(2)), an isomorphism. **This
   fibre fact is field-level and lives in AINTLIB's HasseWeil** (`InvariantDifferential`,
   `OmegaPullbackCoeff` = the `[N]*ω = Nω` coefficient, `card_kernel_eq_degree_of_separable`,
   `mulByInt_degree`, `TorsionGeneralN`). Transport to the scheme fibre `E[N]_{k̄}` is the crux
   **T-B6** comparison (scheme fibre ↔ `WeierstrassCurve k̄`), and "finite + geometric fibres
   unramified ⟹ unramified" is **T-DISC** (L-BC). **⟹ `E[N] → S` formally unramified.**
3. Compose (1)+(2): `[N]` formally unramified. ∎ (MASTER = L-A ∘ L-BC.)

---

## Lemmas (in order)

### L-A — `formallyUnramified_mulByHom_of_torsionπ` · leaf (self-contained core, BUILD FIRST)

- Lean: `MulByHomUnramified.lean` `formallyUnramified_mulByHom_of_torsionπ`
  `(N) (htors : FormallyUnramified (E.torsionπ N)) : FormallyUnramified (E.mulByHom N)`.
- Source: **KM Cor. 2.3.2, p. 75** (verbatim):
  > "By 2.3.1, the map `[N]: E → E` is an f.p.p.f `E[N]`-torsor. Therefore if `E[N]` is finite etale
  > over `S`, the map `[N]: E → E` is finite etale."
- Lean ↔ source: `htors` = "`E[N]` [formally un]ramified over `S`"; conclusion = "`[N]` formally
  unramified". The torsor structure (`torsion N = pullback (mulByHom N) zero`) makes the two
  equivalent; we only need the ⟸ direction (the ⟹ direction is base-change stability of
  `FormallyUnramified`). Formalised via `FormallyUnramified`'s uniqueness-of-infinitesimal-lifts
  definition + the `GrpObj` group structure (`pointAddCommGroup`), not the finite-étale packaging —
  strictly what KM's torsor sentence asserts, restricted to the unramified (lift-uniqueness) part.
- Discharge (planned): mathlib `AlgebraicGeometry.FormallyUnramified` (categorical lifting form) +
  the project's `GrpObj`/`pointAddCommGroup` + `E[N] = ker[N]` (`torsion` def). ≤ a self-contained
  lifting argument; no cross-project or held-file dependency.
- Attacks attempted:
  - [1] Counterexample: is "`E[N]` unramified ⟹ `[N]` unramified" false? For a homomorphism of
    smooth `S`-group schemes with kernel `K`, the relative cotangent of the map equals that of `K`
    at the identity (translation-invariance); if `K/S` is unramified the map is unramified. No
    counterexample among group-scheme homs.
  - [2] Edge cases: `N = 0` → `[0]` is the constant `zero` map, `E[0] = E`; the statement degenerates
    but `htors` (`FormallyUnramified (torsionπ 0)` = `FormallyUnramified E.π`) is false in general
    (E/S is smooth of rel dim 1, not unramified) so the implication is vacuous/consistent — flagged:
    the lemma is used only with `N` invertible (`N ≠ 0`), where `E[N]` is 0-dimensional. `N = 1` →
    `[1] = id`, `E[1] = S`, both unramified ✓.
  - [3] Hypothesis test: drop `htors` → false (`[N]` is NOT unramified when `E[N] → S` is ramified,
    e.g. `char | N`). Necessary. No hidden typeclass beyond `EllipticCurve S`.
  - [4] Source-drift: KM says "finite *étale*"; our Lean isolates the *unramified* (lift-uniqueness)
    part, strictly weaker than KM's sentence — deliberately narrower (we compose with flat+lfp
    elsewhere for étale). No over-claim.
  - [5] Discharge attack: `FormallyUnramified` morphism property exists
    (`Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean`, verified). The group difference
    `h := g₁ - g₂` needs `pointAddCommGroup` on `T`-points (project, present) + `[N]∘h = 0 ⟹ h`
    factors through `E[N]` (universal property of the `torsion` pullback, `pointToTorsion` present).
    Composition is a genuine several-step argument (an internal node in disguise?) — but it is
    self-contained and small; if it exceeds a clean leaf it splits into "difference lands in E[N]" +
    "unramified kills it", both tractable. Verdict: SURVIVED; the primary first landing.

### L-BC — `formallyUnramified_torsionπ` · internal (API-gap sub-tree: L-B + L-C/T-DISC)

- Lean: `MulByHomUnramified.lean` `formallyUnramified_torsionπ`
  `(N) (h : NIsInvertible S N) : FormallyUnramified (E.torsionπ N)`.
- Source: **KM Thm 2.3.1, p. 73** (verbatim):
  > "Then the S-homomorphism 'multiplication by N' `[N]: E → E` is finite locally free of rank `N²`.
  > If `N` is invertible on `S`, its kernel `E[N]` is finite etale over `S`, locally for the etale
  > topology on `S` isomorphic to `Z/NZ × Z/NZ`."
- Composition = **L-B** (geometric fibres étale) + **L-C = T-DISC** (finite + fibres unramified ⟹
  unramified). KM's proof (p. 74) reduces fibre-by-fibre and gives the fibre fact via the tangent
  map; we substitute HasseWeil for the fibre and T-DISC for the reduction.

#### L-B — geometric fibres `E[N]_{k̄}` étale · leaf via HasseWeil + T-B6 bridge (MODERATE)
- Source: **KM 2.3.1 proof, p. 74** (verbatim):
  > "If char(k) does not divide N, then `[N]` is etale (its tangent map at the origin being
  > multiplication by N), hence non-constant, hence finite and flat. Therefore `[N]: E → E` is finite
  > etale over any algebraically closed field of characteristic prime to `[N]`."
  and **Loeffler 3.4.2(2)** (`Torsion.lean:20-24`): "The morphism `[N]` multiplies a global
  differential by `N`, so it induces an isomorphism of tangent space. In other words, it is an étale
  morphism."
- Lean ↔ source: the "tangent map = mult by N" is exactly HasseWeil's `OmegaPullbackCoeff` /
  `InvariantDifferential` (`[N]*ω = Nω`); "finite étale over `k̄`" ⟸
  `card_kernel_eq_degree_of_separable` (`#ker[N] = deg[N] = N²`, `mulByInt_degree`) +
  `TorsionGeneralN` (`E[N]_{k̄} ≅ (ℤ/N)²`). **Crux = T-B6**: the scheme fibre `E_{k̄}` ↔ HasseWeil
  `WeierstrassCurve k̄` comparison (template: `WeilPairing/GaloisEquivariance.lean`'s
  `E.Point t ↔ W.toAffine.Point` identification), which must be built **non-circularly** (the current
  T-B6 routes through `torsionπ_etale`). Status: MODERATE — the field math is in HasseWeil; the
  bridge is the WeilPairing-style point comparison. Own sub-ticket **T-B6′** (non-circular).
- Attacks: [1] `char k̄ ∤ N` needed (else `[N]` inseparable, fibre non-reduced) — matches `NIsInvertible`
  descending to fibres. [3] HasseWeil hyps `[Field][DecidableEq][IsElliptic]` on `WeierstrassCurve k̄`
  — the fibre `E_{k̄}` supplies these via the LocallyWeierstrass model + T-B6. [5] `mulByInt_degree`,
  `card_kernel_eq_degree_of_separable`, `TorsionGeneralN` verified present in HasseWeil; the
  comparison decl is what T-B6′ must build. Verdict: SURVIVED as an internal node; T-B6′ is its leaf.

#### L-C = T-DISC — finite + geometric fibres unramified ⟹ unramified · leaf (MODERATE, ForMathlib)
- Claim: a finite (locally free) morphism whose geometric fibres are unramified/étale is
  unramified/étale (⟺ discriminant a unit). The general **flf ⟺ discriminant-étale** criterion.
- Source: KM 2.3.1 proof, p. 75 ("`[N]` is finite flat and fiber-by-fiber etale, so finite etale");
  standard (EGA IV / Stacks 02GU "étale ⟺ flat + unramified", 0C13 fibrewise criteria).
- Status: mathlib has `Etale` = `Flat` + `FormallyUnramified` + `LFP`
  (`Etale.of_formallyUnramified_of_flat`, used at `Torsion.lean:243`) and fibrewise criteria for some
  properties; the exact "unramified ⟺ geometric fibres unramified for finite/lft" packaging must be
  pinned (candidate: `FormallyUnramified` via `Locus.lean` `IsUnramifiedAt` pointwise + fibre base
  change). **T-DISC proper** = the discriminant-a-unit refinement, useful beyond `E[N]` (T-D6c/
  T-D7-bridge sit on it). Own ForMathlib sub-ticket. MODERATE.
- Attacks: [1] false without finiteness/properness (an open immersion has étale fibres but needn't be
  proper — but we have finite). [3] "geometric fibres" (not just fibres) needed for the field-extension
  subtlety. [5] the pointwise `IsUnramifiedAt` + fibre criterion is the pin-at-execution risk.

### MASTER — `mulByHom_formallyUnramified'` · assembly (term-mode, `sorry`-free)
- `E.formallyUnramified_mulByHom_of_torsionπ N (E.formallyUnramified_torsionπ N h)` — proves the
  decomposition composes at the exact target type; discharging L-A + L-BC discharges
  `Torsion.lean:228`. Composition attack: the two leaf types compose iff `htors`'s type is exactly
  `formallyUnramified_torsionπ`'s conclusion — verified by the skeleton's `lake build` (Step 2.5).

---

## Feasibility assessment

BB-DIFF decomposes into a **self-contained core** (L-A, the `E[N]`-torsor ⟹ `[N]`-unramified
reduction — buildable now, route-independent, collides with no lane; **land this first**) and an
**arithmetic sub-tree** L-BC = L-B (geometric fibres, MODERATE, needs the **non-circular T-B6′**
scheme-fibre ↔ HasseWeil comparison — the field math is already in HasseWeil, verified) + L-C/**T-DISC**
(fibrewise-unramified criterion, MODERATE, ForMathlib). This is **MODERATE-MAJOR but genuinely
dischargeable** — a decisive improvement on the earlier "invariant-differential route infeasible"
read, because the fibre-level invariant-differential math lives in HasseWeil, not mathlib. No route
touches the mapped dead ends (scheme `Ω¹`, chart-`[N]`, the circular chain). **Recommendation:** land
L-A immediately (self-contained; unblocks nothing but is the clean anchor and de-risks the reduction),
then T-B6′ (non-circular fibre comparison) and T-DISC in parallel; `formallyUnramified_torsionπ`
(L-BC) then closes, and MASTER discharges BB-DIFF. Per v10.8 RR-only: BB-DIFF stays a sorried target
with this now-planned discharge route; nothing becomes a permanent assumption.

## Next step

Planning-only — no proof executed. When approved, `/develop --continue` tickets L-A (buildable now),
T-B6′ (non-circular scheme-fibre ↔ HasseWeil `WeierstrassCurve` comparison), and T-DISC (ForMathlib
flf⟺discriminant/fibrewise-étale). L-A is the recommended first `/beastmode` claim (self-contained,
non-colliding). File discipline: new bridge files only; `Torsion.lean`/`GroupLawConstruction.lean` held.
