# Decomposition — [KM-W0] rel-rep wave: Drinfeld Γ(N)/Γ₁(N) relative representability

**Chartered `/develop --decompose` of KM §§1.4–1.11 + 3.5–3.7** (source-faithful; page convention **pdf = print + 11**; source `refs/ModularCurves/katz-mazur-arithmetic-moduli-FULL.pdf`). Produced 2026-07-13 from a focused source scout; every leaf carries a KM locator + verbatim quote. No renumbering found.

## Target
- `ModularCurves.gammaFullDrinfeld_representable` (GammaH:1032) — `(gammaFullDrinfeldProblem R N).Rigid ∧ .Representable`, `3 ≤ N`, `IsUnit (N:R)`.
- `ModularCurves.gammaOneDrinfeld_representable` (GammaH:1045) — same for `gammaOneDrinfeldProblem`, `4 ≤ N`.
- In KM's language: `gammaFullDrinfeldProblem = (ℤ/Nℤ)²-Gen(E[N]/S)`, `gammaOneDrinfeldProblem = ℤ/Nℤ-Str(E/S)` (KM 3.1/3.2).

## The KM spine (bottom-up; KM 3.6.0 is a two-line reduction onto Ch. 1)
`1.6.1` Hom-scheme `Hom_{S-gp}(A,C) = C[N₁]×…×C[N_r]` (needs `E[N]` finite) → `1.9.1 / 1.3.7` closed conditions (full-set-of-sections / is-a-subgroup) → `1.10.1 / 1.10.7` Cartier-divisor ⟺ full-set bridge + reduction to `C[N]` → `1.10.13(1) / 1.6.5` A-Gen finite  &  `1.6.2 / 1.10.11` A-Str finite → **`3.6.0`** assembly (finite ⟹ affine ⟹ `RelativelyRepresentable`) → **`4.7.0`** (+ rigidity ⟺ `Representable`).

**Verbatim, KM 3.6.0 (print 102 / pdf 113):** *"…each is represented by a finite S-scheme. … the first two functors are respectively `(ℤ/Nℤ)²-Gen(E[N]/S)` and `ℤ/Nℤ-Str(E/S)`."*
**Verbatim, KM 1.6.2 (print 23 / pdf 34):** *"`A-Str(C/S)` … is represented by a closed subscheme of `Hom_{S-gp}(A,C) ≃ C[N₁]×…×C[N_r]` definable locally by `1 + #(A) + (#(A))²` equations."*
**Verbatim, KM 1.10.13(1) (print 47 / pdf 58):** *"`A-Gen(G/S)` … is representable by a finite S-scheme … the closed subscheme of `Hom_{S-gp}(A,G)` over which the image sections … form a 'full set of sections.'"*
**Verbatim, KM 1.9.1 (print 38 / pdf 49):** *"unique closed subscheme `W ⊂ S` … universal for 'P₁,…,P_N are a full set of sections of Z/S' … Locally on S, W is defined by finitely many equations."*
**Verbatim, KM 4.7.0 / Scholie (print 111 / pdf 122):** *"Let 𝒫 be relatively representable and affine over (Ell); then a necessary and sufficient condition that 𝒫 be representable is that 𝒫 be rigid."*

## Feasibility verdict: BOUNDED (not published-paper-scale)
KM's proof of the target is a two-line reduction onto Ch. 1, whose **affine heart is already proven sorry-free** (`IsFullSetOfSectionsAlg`, `…Charpoly`, `isFullSetOfSectionsAlg_iff_fields` in `LevelStructure/CartierDivisor.lean`), whose ambient object `E.torsion N` **exists and is proven finite** (`torsionπ_isFinite`), and whose endgame engine `4.7.0` is **already coded** (`ModuliProblem.representable_iff`, EllCategory). The whole distance is the leaves below.

## The four (c)-class leaves + ownership routing (binding boundaries: LevelStructure read-only for KM; E[N]/Hopf = STREAM-G0)
- **(c1) T-D4 — full-set-of-sections globalisation** (KM 1.9.1 → 1.10.13(1)): promote the *affine* full-set criterion (proven, `CartierDivisor.lean`) to the closed subscheme of `Hom_{S-gp}(A,E[N])` cut out over the whole base (norm-coefficient equations glued across a trivialising cover). **THE LINCHPIN.** Yields `A-Gen`/`A-Str` representable (L16/L17). Affine heart lives in read-only LevelStructure ⇒ **new work goes in a Moduli file importing it** (or coordinate a LevelStructure add). Size: moderate–large.
- **(c2) Hom-group-scheme** `Hom_{S-gp}(A,E[N]) = ∏ E[Nᵢ]` (KM 1.6.1): assemble the group-hom functor-of-points on the already-built `E.torsion N`. For the two targets: `Hom(ℤ/N,E)=E[N]` (Γ₁, one factor), `Hom((ℤ/N)²,E)=E[N]×_S E[N]` (Γ(N), the (P,Q) pair). **Moduli-side / mine.** Size: moderate (bookkeeping on torsion schemes).
- **(c3) incidence "is-a-subgroup" closed condition** (KM 1.3.4/1.3.7): **AVOIDABLE** for Γ(N)/Γ₁(N) via 1.10.7 + 1.10.11 (route through the full-set engine on `E[N]`); mandatory only for divisor-native / balanced-Γ₁ / Γ₀. Skip for now.
- **(c4) `E[N]` locally free of rank exactly N²** (KM 2.3.1): **currently SORRIED** (`Torsion.lean:153/194` ⟸ `endDeg_mulBy = n²` `EndomorphismDegree.lean:107`). Required on the Γ(N) side (`#((ℤ/N)²)=N²`); NOT needed for Γ₁. **E[N] ⇒ STREAM-G0 territory.** Size: moderate.

## Shared endgame caveat
Final `.Representable` consumes `representable_iff`'s `⇐` direction (sorried, gated on engine tickets T-Q6e/T-E14/T-E15) — the **same** endgame already accepted for the naive problems (`gammaFullNaive_representable`), not new Ch. 1 math.

## Invertible-N shortcut already in code (the tractable-by-me bridge)
`isFullLevel_iff_naive` (Basic:130) + `isGammaOne_iff_naive` (Basic:143) are **sorry-free**; `ModuliProblem.relativelyRepresentable_of_iso` (GammaHRep) exists. So `gammaFullDrinfeldProblem ≅ gammaFullNaiveProblem` (functor iso from the pointwise iff, N inv) transports `RelativelyRepresentable`/`Rigid` from the naive problem. **But** the naive rep `gammaFullNaive_representable`/`gammaOneNaive_representable` (Representability:250/264) is itself SORRIED (= KM 3.7.1 finite-étale case), and the naive problem maps (Representability:214/229) are sorried (naive transport, arbitrary base). So the bridge re-points the goal at the naive rep; it does not close it alone.

## Recommended execution order (mine-first, coordinate cross-stream)
1. **[mine] Hom-scheme (c2)** — `E.torsion N ×_S E.torsion N` as `Hom((ℤ/N)²,E)` functor-of-points; small, self-contained, unblocks the ambient object for c1.
2. **[mine] Drinfeld↔naive functor iso** (from the sorry-free bridges) — makes the invertible-N reduction explicit; re-points 1032/1045 at the naive rep.
3. **[coordinate: G0] rank-N² (c4)** — `endDeg_mulBy = n²` (`EndomorphismDegree:107`) is E[N]/isogeny-degree = G0 territory; board to G0.
4. **[mine/LevelStructure-coordinate] T-D4 (c1)** — the linchpin globalisation; affine heart is in read-only LevelStructure, so build the scheme-level wrapper in Moduli.
5. **assembly 3.6.0 → 4.7.0** — once c1/c2 land, `.RelativelyRepresentable` + `.Rigid` ⟹ `.Representable` via the coded Scholie engine.

## Full leaf table
See the scout report locators L1–L25 (this file's git history / STREAM-KM board). Key project files: `Moduli/EllCategory.lean` (Scholie 4.7.0), `LevelStructure/CartierDivisor.lean` (affine full-set, KM 1.8.2/1.9.1/1.10.1), `LevelStructure/Basic.lean` (Drinfeld defs + T-D4 note), `EllipticCurve/Torsion.lean`+`TorsionFibre.lean` (`E.torsion N`, `torsionπ_isFinite`, rank-N² sorry), `GroupScheme/NIsogeny.lean` (`D^×` scheme-of-generators precedent, KM 1.10.13), `ModularCurve/YFullRoute.lean` (finished naive Γ(N) route to imitate).

## POST-DECOMPOSE EXECUTION FINDING (2026-07-13, traced through code) — the naive bridge is canonicity-blocked
The invertible-N shortcut (§ above) is a **dead-end for closing 1032/1045**, on BOTH ends:
- **Naive maps** (`Representability:214`/`229`) are **structurally blocked** on **T-W7.8** (owner-parked arbitrary-base canonicity), NOT hard. Killing clause `(N:ℤ)•pullSection f Q = 0` needs `mulByHom N ≫ f.top = f.top ≫ mulByHom N` (`f.top` a group-scheme hom = T-E4a); sorried at `Representability:204`; the records de-sorry only exists downstream (`_of_finitePresentation`, `GammaHRep:1442`) — unreachable from the upstream naive maps.
- **Naive rep** (`:250`/`:264`) is the separate (c)-scale KM 3.7.1 crux.

**Route-defining reason:** Drinfeld `HasExactOrder` transports **canonicity-free** (divisor/ideal condition via base-change of ideals — why `hasExactOrder_pullSection` + L4 close), naive exact-order via the point-group ℤ-action (canonicity-fragile). **⟹ The DIRECT Drinfeld route (c1/c2/c4 → 3.6.0 → 4.7.0) is THE route; the naive bridge is not** — unless the owner un-parks T-W7.8, which would open it as a *second* route.

**Free building blocks verified** (cartesian-only, arbitrary-base): `pullSection_zero`; the zero-transport `pull t (pullSection f Q) = 0 ↔ pull (t≫baseHom) Q = 0`. These discharge the naive **≠0-clauses**; only the **killing clause** is T-W7.8-gated.

## Γ₁ REL-REP DELIVERED + rigid-gating finding (2026-07-13, committed `3aef6f052`)
The direct Drinfeld route's Γ₁ half is now **assembled and green** — `Moduli/DrinfeldRepresentability.lean`:
- **`gammaOneDrinfeld_affineOverEll`** — the FULL functor-of-points equiv (toFun/invFun/left_inv/right_inv/**naturality**) proven, assembling c2 `torsionPointsEquiv` + c1 `exists_exactOrderLocus`. **No c4.** The equiv is genuinely **sorry-free** (all helpers verified axiom-clean).
- **`gammaOneDrinfeld_relativelyRepresentable`** = `AffineOverEll.relativelyRepresentable` — the **Γ₁ rel-rep ★**.
- **Axiom status:** affineOverEll's only `sorryAx` is inherited via the affineness witness `torsionπ_isFinite → mulByHom_isFinite → mulByHom_locallyQuasiFinite` (`Torsion.lean:141` sorry) = the accepted **KM 2.3.1 E[N]-finiteness BB (G0/BB-FLAT funnel)**. Not rank/c4 — quasi-finiteness. Same baseline as the shipped naive route.

**RIGID IS A SECOND CROSS-STREAM GATE (new).** The endgame `equiv → gammaOneDrinfeld_rigid → .Representable` has `rigid` gated like c4: `Rigid` quantifies over **every** base-fixing automorphism. The **[-1] core is in-hand** (`EllObj.pullSection_negHom = -P` (GammaH:551, proven); `-P=P ⟹ 2P=0` contra order `N≥3`), but the **CM automorphisms** (order 3/4/6 at `j=0,1728`) need `α(P)=P ⟹ α=𝟙` via `P∈ker(α-1)`, `|ker(α-1)|=deg(α-1)<N` = **endomorphism-degree `mulByHom_finrank`/`endDeg_mulBy` (SORRIED, STREAM-G0, same family as c4)**. The general criterion `gammaHNaive_rigid_iff` (GammaH:447, Loeffler 3.8.3) is **also SORRIED, H-lane**. ⟹ **`gammaOneDrinfeld_rigid` → G0 (degree) or H-lane (3.8.3); routed for dispatch, not in-stream-forced.** `.Representable` (GammaH:1045) thus has TWO gates: rigid (G0/H) + engine `representable_iff`⇐ (OMEGA). Not wired (would inject a rigid sorry into shared GammaH.lean).
