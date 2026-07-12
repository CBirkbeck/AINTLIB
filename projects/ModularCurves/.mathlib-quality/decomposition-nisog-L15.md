# Decomposition — [L15] `exists_nIsogSpace` (KM 6.5.1) — STREAM-NISOG wave M2

**Scoped by beastmode-D2, 2026-07-11, verbatim source read** (KM print pp. 164–166 = pdf
175–177). Target (NIsogeny.lean, sorried): `exists_nIsogSpace : ∃ (W : Scheme) (w : W ⟶ S),
IsFinite w ∧ ∀ t : T ⟶ S, Nonempty (NIsogenyStructure (E.baseChange t) N ≃ {h // h ≫ w = t})`.
Gate delivered: fable-FP's `ForMathlib/GrassmannianGlueData.lean` (1148 lines, ZERO sorries):
`grassmannianScheme R k n`, `pointOfMember` (T-point forward map, PROVEN), chart-local
round-trips; the global-descent (inverse) leaf is their boarded mathlib-TODO —
**hypothesis-wire it if it bites, don't build it** (charter v10.141).

## Verbatim source (Prop 6.5.1, print p. 165)

> "Given E/S, view E[N]/S as the Spec of a coherent sheaf 𝓕 of bi-algebras on S which is
> locally free of rank N². A subgroup G ⊆ E[N] of the type being sought is nothing other
> than a locally free rank-N quotient 𝔥 of 𝓕, such that the locally free rank N²−N kernel
> 𝒦 ⊆ 𝓕 is a bi-ideal in 𝓕. Therefore [N-Isog] is relatively represented by a closed
> subscheme of the Grassmannian of all rank N quotients of 𝓕, i.e., [N-Isog] is relatively
> representable and projective over (Ell). To see that it is finite over (Ell), we must
> show it has finite fibers, i.e., we must show that [N-Isog](E/k) = {a finite set} when k
> is an algebraically closed field."

Fibre-finiteness (pp. 165–166): factor `N = ∏ pᵢ^{nᵢ}`, `[N-Isog] = ∏ [pᵢ^{nᵢ}-Isog]`;
prime-power case by char: `char(k) ≠ p` "physically obvious ((ℤ/pⁿℤ)² has only finitely
many subgroups)"; `char(k) = p` supersingular: "the unique subgroup of E/k of rank pⁿ is
Ker(Fⁿ)"; ordinary: `E[pⁿ] ≅ μ_{pⁿ} × ℤ/pⁿℤ`, `G ≅ G^conn × G^ét` — "the n+1 subgroups".

## Leaf tree

| Leaf | Content | Source | Status/gate |
|---|---|---|---|
| [L15-a] | `𝓕` := the rank-N² bi-algebra sheaf of `E[N]` (E[N] finite locally free of rank N²) | 6.5.1 setup | **hypothesis-wire**: c5β's CHARTER-C5B-2 builds the E[N]-package (BB-boxes); consume as pins per the boarded seam |
| [L15-b] | dictionary: `NIsogenyStructure (E_T) N` ≃ rank-N quotients of `𝓕_T` with bi-ideal kernel | "nothing other than" | project-side; uses FiniteLocallyFreeSubgroup ↔ quotient-module translation |
| [L15-c] | relative Grassmannian of rank-N quotients of `𝓕`: relativize affine-locally over S-affines trivializing `𝓕` (charts = `grassmannianScheme Γ(U) N N²`), glue via the transition data | "the Grassmannian of all rank N quotients of 𝓕" | consume the DELIVERED gate; the relativization layer is new (chart-independence via the SPEC per the boarded consumption pattern) |
| [L15-d] | the bi-ideal locus is CLOSED in the Grassmannian (comultiplication/counit compatibility of 𝒦 = finitely many equations on the universal quotient; cut with T-D15-style incidence machinery in the charts) | "such that … is a bi-ideal" | new; the LFP-arc toolbox (vanishing loci, fg) directly reusable |
| [L15-e] | T-point classification of the cut locus = `NIsogenyStructure` (forward via `pointOfMember`; inverse = the global-descent leaf) | "relatively represented by a closed subscheme" | forward: gate-PROVEN; inverse: **hypothesis-wire fable-FP's boarded leaf** |
| [L15-f] | `IsFinite w`: projective + finite fibres (the char-case analysis) OR the KM-verbatim route; NOTE: our ∃ asks IsFinite directly — KM proves projective + quasi-finite ⟹ finite (ZMT); the fibre-count leaves land on c5β's E[N]-structure theory | pp. 165–166 | new; fibre-counting gated on c5β's ordinary/supersingular substrate — hypothesis-wire those cases |

## Attacks
- [L15-b] faithfulness: our `NIsogenyStructure` is (subgroup, rank-N) — KM's "of the type
  being sought" = exactly that; the bi-ideal-kernel form is KM's own equivalent phrasing
  (Hopf-ideal ↔ subgroup-scheme quotient — NEW-HOPF's layer supplies the abstract
  correspondence when its pins land; until then the dictionary can be stated against the
  raw comultiplication compatibility).
- [L15-c] the free-module gate vs coherent 𝓕: over trivializing affines 𝓕|U ≅ O_U^{N²} —
  KM's own reduction (p. 164's presentation argument shrinks U); the glue data across
  trivializations is GL_{N²}-transition — the SPEC-based chart-independence in the boarded
  pattern is precisely this.
- [L15-f] `IsFinite` vs KM's "projective + finite fibres": mathlib route
  IsFinite ⟺ affine + proper?? — audit at execution; if the ZMT-composite is heavy,
  restate the ∃ with the available conjuncts and board the delta (statement-change needs
  a b2-style note since the target is a boarded skeleton statement).

## Execution order (next stretch)
1. [L15-b] dictionary statement + the 𝓕-pins interface (hypothesis-wired c5β inputs).
2. [L15-c] relativization skeleton (chart family + glue via delivered gate).
3. [L15-d] bi-ideal locus (LFP-toolbox).
4. [L15-e] classification wiring (pointOfMember + hypothesis-wired descent).
5. [L15-f] finiteness assembly.

## EXECUTION LEDGER (beastmode-D2, 2026-07-12, v10.162 marathon)

**Buildable-by-D2-now, DONE (axiom-clean, `GroupScheme/NIsogSpace.lean`):**
- [L15-a] `IsBiIdeal` (the cut condition) + `IsBiIdeal.toIdeal` (F-ideal structure) +
  `IsBiIdeal.counit_eq_zero` accessors.
- [L15-b] `NIsogRepresentation` pins-record + `exists_nIsogSpace_of_representation`
  assembly — `exists_nIsogSpace` closes with zero wiring the moment the record is populated.

**WALL-LEDGER — remaining leaves are blocked on OTHER LANES' unbuilt infrastructure (charter:
"hypothesis-wire ... don't build it"):**
- [L15-c] relativize the Grassmannian → needs 𝓕 = O(E[N]) as a concrete locally-free sheaf
  with trivialization/transition data. The `torsionπ_isFinite/_flat/torsion_rank` facts are
  STATED but sorry-backed (c5β's BB-boxes) AND expose no local-trivialization data; a general
  "relative Grassmannian of a finite locally free sheaf" is mathlib-absent and overlaps
  fable-FP's Grassmannian domain. **Gate: c5β E[N]-package + a relative-Grassmannian scheme.**
- [L15-d] cut the bi-ideal locus → needs (i) the **universal member/quotient family** of the
  Grassmannian exposed as a sheaf map (fable-FP's `GrassmannianGlueData` exposes `ChartRing`
  but not the universal family) and (ii) 𝓕's comultiplication/counit Δ,ε (**NEW-HOPF's
  C-layer, unbuilt**). My LFP/T-D15 toolbox cuts it the moment both are present.
- [L15-e] classify → `pointOfMember` forward map is PROVEN; the inverse is fable-FP's boarded
  global-descent leaf. Wires once [L15-c/d] land.
- [L15-f] finiteness → KM's prime-power fibre count needs c5β's ordinary/supersingular E[N]
  fibre structure. **Gate: c5β substrate.**

**Verdict**: L15 is a genuine multi-lane dependency wall. D2's buildable core ([L15-a/b]) is
complete and axiom-clean; the assembly interface makes `exists_nIsogSpace` a one-line
extraction once the record is populated by c5β (E[N] + fibre structure) + NEW-HOPF (comul +
dictionary) + fable-FP (relative representability). No D2-buildable leaf remains that does not
require constructing another lane's chartered gate.

## Y₀(N) ASSEMBLY FINDING (D2, 2026-07-12)

The Γ₀(N) representability `exists_gammaZeroSpace` (KM 6.6.1, NIsogeny.lean:2926, sorried)
= "the closed subscheme of `[N-Isog]` over which the universal `N`-isogeny is cyclic". The
assembly route is: `exists_nIsogSpace` → `W_isog`; the universal `NIsogenyStructure` over
`W_isog` → its subgroup `G_univ` → `G_univ.toRelEffCartierDiv` (T-SG1, HAVE); apply
`exists_cyclicityLocus` (my capstone) to it → the cyclicity locus `Z ⊆ W_isog`;
`W_Γ₀ := Z.subscheme`, finite over `S` via `Z.subschemeι` (closed imm) ∘ `w_isog`.

**BLOCKER (new finding, boarding for the coordinator):** the current `exists_nIsogSpace`
statement gives only `Nonempty` of *per-`T`* equivalences with NO naturality. The Γ₀(N)
assembly needs the classifying point of a `T`-structure to *pull back the universal
structure over `W_isog`* — i.e. `exists_nIsogSpace` must be **functorial/representing**, not
just pointwise-equivalent. GammaZeroStructure ≃ cyclic-NIsogenyStructure (via `IsCyclic` =
`toRelEffCartierDiv` is `IsGammaZeroFppf`, CyclicSubgroup.lean) then composes with `Z`'s
universal property. **So Y₀(N) is transitively wall-blocked on a naturality-strengthened
`exists_nIsogSpace`** — which needs L15's real `NIsogRepresentation` construction. The
`classify` field of `NIsogRepresentation` should be upgraded to a natural-iso / representable
form when L15 is built (noted for the construction lane). All other Y₀(N) handles
(`toRelEffCartierDiv`, `GammaZeroStructure`/`IsCyclic`, `exists_cyclicityLocus`) are HAVE.

## Y₀(N) CYCLICITY-TRANSFER CRUX — DELIVERED (D2, 2026-07-12, continuation)

The Y₀(N) assembly's hardest compatibility (flagged in the finding above) is now PROVEN
(`GroupScheme/NIsogSpace.lean`):
- `FiniteLocallyFreeSubgroup.toRelEffCartierDiv_baseChange_ideal` — the subgroup-divisor
  commutes with base change: `(G.baseChange g).toRelEffCartierDiv.ideal =
  (G.toRelEffCartierDiv.baseChange g).ideal` (both `= G.ι.ker.comap (pullback.fst E.π g)`,
  via the pullbackSymmetry + `ker_fst_of_isClosedImmersion` route). [sorryAx via upstream
  T-SG1b `subgroup.baseChange`, not D2.]
- `isGammaZeroFppf_congr` — cyclicity is ideal-determined (via `RelEffCartierDiv.ext`).
  **Fully axiom-clean.**
- `isCyclic_baseChange_iff` — `(G.baseChange g).IsCyclic N ↔ IsGammaZeroFppf N
  (G.toRelEffCartierDiv.baseChange g)` — **the exact shape `exists_cyclicityLocus` consumes.**

So the Y₀(N) assembly `exists_gammaZeroSpace = cut cyclicity locus on [N-Isog]` now has its
cyclicity-transfer step DONE. **Remaining** (not a wall — a design+coherence build whose
interface shape L15's real construction dictates): (i) the functorial `NIsogRepresentation`
(a `classify` that is natural, so a `T`-structure is the pullback of the universal one); (ii)
the classify-naturality / L5-style curve-composition coherence (`E.baseChange (h≫w)` vs
`(E.baseChange w).baseChange h` for the subgroup). With those, the equivalence chain
`GammaZeroStructure_T ≃ cyclic-NIsog_T ≃ {h through Z}` closes via `isCyclic_baseChange_iff`
+ `exists_cyclicityLocus` + the functorial classify.
