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
