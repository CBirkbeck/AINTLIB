# Decomposition — CHARTER-C5B-2: the E[N] group-scheme package + level substrate

`/develop --decompose` (adversarial) run by c5β, 2026-07-11. Source: Katz–Mazur,
*Arithmetic Moduli of Elliptic Curves* (refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf),
§2.3, §3.1–3.7 (read verbatim; quotes below). **Headline: an ecosystem re-check shows the
package is ~90% already built — the reuse-not-duplicate rule dominates this charter.**

## Source anchors (verbatim quotes read from the PDF)

- **KM Thm 2.3.1** (p.73): *"the S-homomorphism 'multiplication by N' [N]: E → E is finite
  locally free of rank N². If N is invertible on S, its kernel E[N] is finite étale over S,
  locally for the étale topology on S isomorphic to Z/NZ × Z/NZ."* — the finiteness/flat/rank-N²
  box (BB-QF/BB-FLAT), hypothesis-wired per charter.
- **KM Cor 2.3.2** (p.75): E[N] finite étale over S ⟹ N invertible on S.
- **KM §3.1** (p.98): a Γ(N)-structure ("full level N structure" / "Drinfeld basis of E[N]") is
  φ:(ℤ/N)²→E[N](S) a *generator* (1.5), i.e. `E[N] = Σ_{a,b} [φ(a,b)]` as effective Cartier
  divisors; P=φ(1,0), Q=φ(0,1) the Drinfeld basis.
- **KM §3.2** (p.99): a Γ₁(N)-structure = a point P of exact order N (generator of cyclic
  `Ker π = Σ_a [aP]`).
- **KM §3.4** (p.100): a Γ₀(N)-structure = a finite flat subgroup-scheme `K ⊂ E[N]` locally
  free of rank N that is *cyclic* (locally f.p.p.f. admits a generator).
- **KM Prop 3.6.3** (p.103): Γ(N)/Γ₁(N)/bal-Γ₁/Γ₀ structures *"depend only on the underlying
  S-group-scheme E[N]"* — so E[N] as a group scheme IS the substrate.
- **KM §2.8 "Pairings"** (p.87): the Weil pairing — **BOUNDARY, p2's [T-C1-KM28]; cite, do NOT
  build.**

## Ecosystem re-check — what is ALREADY BUILT (do NOT re-plan; the cardinal sin)

| Charter item | Status | Where |
|---|---|---|
| E[N] = ker([N]) as `FiniteLocallyFreeSubgroup` (KM 2.3.1) | **DONE, sorry-free** | `GroupScheme/Subgroup.lean:461` `torsionSubgroup` (finite/flat rest on BB-QF/BB-FLAT boxes — correctly hypothesis-wired) |
| GrpObj structure (unitHom/invHom/mulHom, laws) inherited from mulOver | **DONE** | `GroupScheme/SubgroupGroupObject.lean` (unitHom_ι/invHom_ι/mulHom_ι) |
| Cyclic subgroup substrate (KM 3.4/1.4.1, the Γ₀ datum) | **DONE** | `GroupScheme/CyclicSubgroup.lean` `IsCyclic`, `GammaZeroStructure`, `isCyclic_iff_isGammaZeroFppf`, `ofIsCyclic` |
| H-orbit substrate — P_H = H-orbits of full level structures (Loeffler 3.8.1) | **DONE** | `Moduli/GammaH.lean` `hOrbitSetoid`, `gammaHNaiveProblem` (functor laws proven) |
| GL₂(ℤ/N) action on FullLevelPt (functor-of-points) + MulAction laws | **DONE** | `Moduli/GammaH.lean` `glSmul`, `glSmul_one`, `glSmul_mul`, `FullLevelPt.pullAlong` |
| Subgroup base change | **PARTIAL** — `T-SG1b` field sorried | `GroupScheme/Subgroup.lean:371` (parked; a divisor-base-change route exists) |
| Cartier-divisor subgroups (Σ[aP] ⟶ subgroup scheme) | **DONE** | `GroupScheme/Subgroup.lean:292` |

## The genuine GAP the charter names

- **GL₂(ℤ/N) action AT SCHEME LEVEL** — CONFIRMED ABSENT (grep for a `MulAction … GeneralLinearGroup`
  on `E.torsion`/E[N], or scheme automorphisms, returns nothing). `glSmul` is only the
  functor-of-points action on the *Type* `E.FullLevelPt N`. The charter: *"glSmul exists —
  upgrade it to the scheme level."* NEW-GH (GH-2 v10.141) will **consume** exactly this package
  for `P_H = [Γ(N)]/H` (KM 7.1.2); the seam is boarded.

## SCOPE FLAG (adversarial — before any ticket)

The charter headline ("build E[N] finite-locally-free group scheme + cyclic/H-orbit substrate +
GL₂ action") overlaps existing landed infra by ~90%. The single clear green-field deliverable is
the **scheme-level** GL₂(ℤ/N) action. But "scheme level" admits ≥2 readings that land in
different lanes:

1. **`GL₂(ℤ/N) → Aut_{grp-sch}(E[N])`** — realize `glSmul`'s change-of-basis as automorphisms of
   the E[N] group scheme via a chosen full level structure (a genuine C5B-2 deliverable, on the
   built substrate; the natural "upgrade").
2. **The action on the Γ(N)-*representing* scheme**, with `P_H = [Γ(N)]/H` the quotient — this is
   KM §3.6/§3.7 + Ch.7 quotient machinery, which is **NEW-GH's headline** (they `/develop
   --decompose` vs KM 7.1.2/7.1.3). Building it here would duplicate GH-2's lane.

Reading (1) is the reuse-respecting C5B-2 scope; reading (2) belongs to NEW-GH. **Recommend
confirming reading (1)** (+ closing the `T-SG1b` base-change sorry if it blocks the seam) before
ticketing — this avoids the cardinal sin and the C5B-2/GH-2 collision the board's seam note warns of.

## Proposed focused decomposition (reading (1) — the scheme-level action)

- **L1** `torsionSubgroup_baseChange` compat (if T-SG1b needed by the action's functoriality) —
  source: KM 2.3.1 base change; discharge: existing divisor base change `T-D20` + `toRelEffCartierDiv`.
- **L2** `FullLevelPt` ≅ (scheme-level) `Iso_{grp-sch}((ℤ/N)²_S, E[N])` bridge — a full level structure
  as a scheme iso, not just a functor point. Source: KM §3.1 (generator ⟺ full set of sections);
  discharge: `torsionSubgroup` + the generator/`IsFullSet` layer already in `GammaH`/`LevelStructure`.
- **L3** `glSchemeSmul : GL₂(ℤ/N) → E[N] ≃ₛ E[N]` (scheme automorphisms) via L2 + `glSmul`; the
  MulAction laws transport from `glSmul_one`/`glSmul_mul`. Single-conclusion API: `_one`, `_mul`,
  `_comp_ι`, base-change compat.
- **L4** seam lemma consumed by NEW-GH: the action's compatibility with `hOrbitSetoid`/`gammaHNaive`
  (so `[Γ(N)]/H` sees the scheme action). Source: Loeffler 3.8.1 + KM 7.1.2 (cite; NEW-GH owns the quotient).

Each leaf discharges from landed infra + the hypothesis-wired BB boxes; no leaf needs the Weil
pairing (boundary respected). LOC: small (the hard substrate is already built) — this is wiring,
~a few dozen lines per leaf, grounded in the existing `glSmul`/`torsionSubgroup` line counts.

## Feasibility

Feasible and small **conditional on the scope confirmation above**. The package is essentially
built; C5B-2's incremental value is the scheme-level GL₂ action (reading (1)) + closing the seam
for NEW-GH. Re-planning the built E[N]/cyclic/H-orbit layer would violate reuse-not-duplicate and
collide with GH-2. Recommend: confirm reading (1), then `/develop --continue` to ticket L1–L4.

## Scope CONFIRMED (owner, 2026-07-11): reading (1) — build glSchemeSmul

## Refined design after adversarial provability check (L2/L3)

`FullLevelPt = {(P,Q) : E.Section² // IsNaiveFullLevel N}`; `IsNaiveFullLevel` (LevelStructure/
Basic.lean:45) = `(N•P=0 ∧ N•Q=0)` ∧ fibrewise-generation (every geom-fibre N-torsion pt is an
ℤ-combo of P,Q) — the **N-invertible** setting (E[N] finite étale ≅ (ℤ/N)², KM 2.3.1). So:

- **L2 feasible for N invertible**: a naive full level (P,Q) trivializes E[N] fibrewise; via the
  finite-étale structure this yields the scheme iso `(ℤ/N)²_S ≅ E[N]`. Discharge substrate:
  `torsionSubgroup` + `torsion_rank`/`natCard_sections_eq_finrank` (TorsionFibre) + BB étale box.
- **L3 core is genuinely NEW infra**: `glSchemeSmul g L : E.torsion N ≅ E.torsion N` (Scheme iso,
  ideally in `Over S`) — the automorphism sending section `aP+bQ ↦ a·(gL).P + b·(gL).Q`. Building a
  Scheme morphism from its action on the generating sections needs the finite-étale universal
  property. `_one`/`_mul` transport from `glSmul_one`/`glSmul_mul` (landed); base-change compat from
  `pullAlong`. This is the real green-field content of C5B-2.
- **L1** (torsionSubgroup base-change / T-SG1b) only if L3's functoriality needs it — check at build.
- **L4** seam: `glSchemeSmul`-vs-`hOrbitSetoid` compatibility (NEW-GH consumes; they own the quotient).

NEXT: `/develop --continue` to ticket L1–L4, then `/beastmode`. L3's finite-étale scheme-morphism
construction is the sizing driver (the rest is transport from landed `glSmul`/substrate).

## L3 construction — final sizing note (adjacent infra found)

Groupoid.lean has the **rigidity/uniqueness** apparatus already: `aut_hom_eq_id_of_fullLevel`
(N≥3, N inv: an aut fixing a naive full level is `𝟙`), `torsionFixed_of_fixesLevel` (a curve
aut fixing (P,Q) fixes `E.torsionι N`), `aut_endo_eq_one`, `endDeg`. These give L3's
well-definedness/uniqueness for free. The green-field piece is the **existence** of
`glSchemeSmul`'s automorphism — realizing the linear section-action as an actual Scheme
morphism `E.torsion N ⟶ E.torsion N` — via the finite-étale universal property (a
section-level map on a finite-étale S-scheme extends to a scheme morphism). Route to check at
build: (a) does `torsionFixed_of_fixesLevel`'s converse/construction give the map directly, or
(b) build it from the étale trivialization `(ℤ/N)²_S ≅ E[N]` (L2) + the linear map on `(ℤ/N)²`.
Prefer (b): compose L2's iso, the constant GL₂ scheme automorphism of `(ℤ/N)²_S`, and L2⁻¹.
That makes L3 = `L2.symm ≪≫ (glConst g) ≪≫ L2` — turning L3 into pure transport once L2 lands.
So **L2 (the étale scheme-iso) is the true crux; L3 is then a 3-line composition.**

## EXECUTION STATUS (2026-07-11, c5β) — group-action layer LANDED, L2 crux staged

Committed `GroupScheme/GLSchemeAction.lean` (compiling; one sorry = L2):
- **BANKED (proven)**: `glEquiv`(+`_one`/`_mul`), `constGL`(+`_one`/`_mul`, self-contained via
  `Sigma.desc` — no p2 coupling), `glSchemeSmul`, and the group-action laws
  `glSchemeSmul_one`/`glSchemeSmul_mul` (L2-independent — proven from `constGL` laws + iso
  cancellation; they inherit sorryAx only through `fullLevelIso`, resolving when L2 lands).
- **REMAINING (the crux, one sorry)**: `fullLevelIso : (ℤ/N)²_S ≅ E.torsion N`. Sub-decomposition
  (a focused sub-development — the finite-étale trivialisation, KM 2.3.1 N-invertible):
  - **L2a** `fullLevelHom := Sigma.desc (fun v => pointToTorsion (v 0 • P + v 1 • Q, killed-by-N))`
    — the map φ; constructible now (`pointToTorsion` Torsion.lean:67 + section arithmetic), fiddly.
  - **L2b (sub-crux)** `IsIso fullLevelHom` — the fibrewise-iso⟹iso criterion, ABSENT from
    mathlib/project. Route: `isIso_of_isPullback_of_fppf` (ForMathlib/PullbackLocalAtTarget.lean:120)
    on an fppf cover trivialising `E[N]` to `(ℤ/N)²` (the KM 2.3.1 étale-local structure). This is
    the real green-field sub-lemma; the WeilPairing lane built the analogous trivialisation for the
    pairing (p2) — consume the *criterion* if it factors out, else build via `torsionπ_etale`.
  - **L2** `fullLevelIso := asIso fullLevelHom` given L2b.
- **L4** seam (`glSchemeSmul` ↔ `hOrbitSetoid`, NEW-GH's consumption) — state once L2 lands + NEW-GH pins the form.

## v10.155 EXECUTION — interface pushed, L2a landed, T-F1/L2b root identified

DONE this session (committed):
- **T-F1 INTERFACE** `torsion_etaleLocal_triv` (GroupScheme/TorsionEtaleTriv.lean) — sorried,
  boarded v10.155, **NEW-Y1 CLOPEN-β unblocked** (the priority first act).
- **glSchemeSmul group-action layer** (GLSchemeAction.lean) — glEquiv/constGL/glSchemeSmul +
  _one/_mul, all proven.
- **L2a `fullLevelHom`** — the map φ, proven (Sigma.desc ∘ pointToTorsion ∘ N-killed combo).
- `fullLevelIso := asIso fullLevelHom` given L2b.

THE SHARED CRUX (root of both remaining sorries — L2b `fullLevelHom_isIso` AND T-F1
`torsion_etaleLocal_triv`):
- `isIso_of_isPullback_of_fppf` (h : IsPullback fst snd f g, f fppf [Surj+Flat+QuasiCompact],
  IsIso fst ⟹ IsIso g) needs a **trivialising fppf cover** of E[N]. That cover IS T-F1.
- **T-F1 is the true root**: construct the étale cover over which the finite-étale `E[N]`
  (`torsionπ_etale`, N inv) becomes constant `(ℤ/N)²` — KM 2.3.1's étale-locally-constant
  structure. Route: the finite-étale Galois/fundamental-group structure
  (`ForMathlib/FiniteEtaleFundamentalGroup.lean` `finiteEtaleEquivContAction`) — E[N] as a
  π₁-set trivialises on the cover killing the action; OR a direct rank-N² finite-étale
  structure lemma. This is the deep sub-development (the KM 2.3.1 local structure) — its own
  focused pass; NEW-Y1 codes to the pushed interface meanwhile.
- Once T-F1 lands: L2b = base-change φ along the cover (becomes iso between two constant
  (ℤ/N)², by the full-level bijection) + `isIso_of_isPullback_of_fppf`; then L4 seam for NEW-GH.

## T-F1 UNLOCKED — the 8-link assembly (all mathlib lemmas named; execution plan)

The crux `torsion_etaleLocal_triv` = scheme-level globalisation of mathlib's ring-level
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` (Lenstra 5.10). NO scheme-level shortcut
(mathlib Galois category is field-level; confirmed). Assembly, all links named:
1. `isAffine_of_isAffineHom` — for S affine, E[N]=E.torsion N is affine (IsFinite extends IsAffineHom).
2. `HasRingHomProperty.iff_of_isAffine` (the `@Etale` instance) — Etale (E.torsionπ N) → RingHom.Etale (R→A), A:=Γ(E.torsion N).
3. `torsionπ_isFinite` + `Scheme.Hom.finrank`/`torsion_rank` (=N²) — Module.Finite R A + rankAtStalk A = N².
4. **`exists_tensorProduct_of_etale`** — the totally-split cover T (étale FaithfullyFlat R-algebra, IsFiniteSplit T (T⊗A)).
5. `IsFiniteSplit.nonempty_algEquiv_fun` — T⊗A ≅ (Fin N² → T); Spec ⟹ E[N]×_S Spec T ≅ ∐_{N²} Spec T.
6. `∐_{N²} Spec T = constScheme (Spec T) (Fin 2 → ZMod N)` (N² = card, scheme-level; (ℤ/N)² labels irrelevant here).
7. Spec T → S étale (FaithfullyFlat+Etale) surjective — the cover.
8. General S: affine `OpenCover` + `∐_i` the local covers, Sigma-commute reindex (rank N² constant ⟹ global const iso).
Then L2b `fullLevelHom_isIso` = base-change φ along the cover (iso of two const N²-sheet schemes) +
`isIso_of_isPullback_of_fppf`; then L4 seam. Execution effort: substantial (multi-build), but each
link is a named lemma — no open mathematical gap remains.
