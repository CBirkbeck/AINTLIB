# Worker decomposition — [CHARTER-HOPF]: `IsHopfGalois (translation co-action)`

*NEW-HOPF, 2026-07-09 (`/develop --decompose`, v10.8 discipline). The [T-G3d-infra] Piece-3 crux
(v10.95 charter): prove `IsHopfGalois ρ` — `Bijective (canonicalGaloisMap ρ)` +
`Module.FaithfullyFlat (coinvariants ρ) B` — for the translation co-action of a finite locally
free subgroup scheme, then glue. Everything downstream is PROVEN (v10.41-p0/v10.42-p0):
`isColimit_of_isHopfGalois` + `exists_unique_lift_of_isColimit` + `isInvariant_iff_coequalizes`
discharge the six `SubgroupQuotient` pins per chart once `IsHopfGalois` holds there.*

## ROUTE DECISION (recon complete): Stacks 39.23, comodule-native

**The theorem to formalize is Stacks project, Groupoid Schemes, Section 39.23 "Finite flat
groupoids, affine case" (tag 03BE), Proposition 39.23.9 (tag 03BM)** — verbatim statement:

> "Let S be a scheme. Let (U, R, s, t, c) be a groupoid scheme over S. Assume
> (1) U = Spec(A), and R = Spec(B) are affine, (2) s, t : R → U finite locally free, and
> (3) j = (t, s) is an equivalence relation. In this case, let C ⊂ A be as in (39.23.0.1)
> [C = {a ∈ A | t♯(a) = s♯(a)}]. Then U → M = Spec(C) is finite locally free and
> R = U ×_M U. Moreover, M represents the quotient sheaf U/R in the fppf topology."

This is the affine case of SGA 3 Exp. V Thm 4.1 (KM's own deferral: *"In the absence of
noetherian hypotheses, this is rather delicate (SGA III, Exp V, 4.1 or Demazure–Gabriel,
III §2, 6.1)"* — KM A7.1, quoted in `ForMathlib/InvariantTorsor.lean`; SGA 3 V 4.1 (iv):
*"X₁ ⟶ X₀ ×_Y X₀ est un isomorphisme"*). The Stacks text is complete, non-noetherian, and
ring-theoretic — the whole §39.23 source was captured verbatim during recon (fetched from
stacks-project/groupoids.tex; quotes below are from that capture).

**Routes REJECTED**: (i) *Hopf-native Kreimer–Takeuchi/Morita* (dual Hopf algebra + smash
products + Morita bootstrap ≈ three infrastructure projects; integrals theory
(Larson–Sweedler/Pareigis) absent from mathlib and multi-week by itself). (ii) *CHR Galois
coordinates* (the proven constant-group route, `InvariantTorsor.lean`): does NOT generalize —
the separability idempotent "indicator of 1 ∈ G" does not exist for non-étale G (e.g. μ_p in
char p: O(G) is local, no idempotents). (iii) *SGA 3 literal / Mumford AV §12 / vdG–M ch. 4*:
same mathematics as Stacks but semi-local Lemme 4.2 in French / field-noetherian shading; used
as citations only. (iv) *E[N]-étale shortcut*: does not serve Γ₀(N) (non-étale C in char p) —
out of charter scope.

**Comodule-native (per the v10.50 no-formulation-bridge ruling)**: no abstract
`RingGroupoid` layer. Every Stacks lemma is stated directly for the translation groupoid of a
co-action, i.e. against the pinned substrate: `s♯ = Algebra.TensorProduct.includeLeft`,
`t♯ = ρ`, `C = coinvariants ρ`, with `IsCoaction ρ` + `[HopfAlgebra R A]` supplying the
groupoid axioms. Constant-group parallels are cited, never unified.

## The dictionary (Stacks ↔ ours)

| Stacks 39.23 | ours |
|---|---|
| A (ring of U) | `B` — the G-stable affine chart of E |
| B (ring of R) | `B ⊗[R] A` — A = O(G) over the base ring R |
| s♯ : A → B | `Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] A` |
| t♯ : A → B | `ρ : B →ₐ[R] B ⊗[R] A` (the co-action) |
| C = {a : t♯a = s♯a} | `coinvariants ρ` (`AlgHom.equalizer ρ includeLeft`) |
| t ⊗ s : A ⊗_C A → B | `canonicalGaloisMap ρ` ∘ factor swap (`TensorProduct.comm`) |
| j = (t,s) : R → U ×_S U | `actPair` (`TranslationAction.lean`; **mono PROVEN**) |
| groupoid axioms (c, e, i) | `IsCoaction ρ` (counit/coassoc) + antipode (`HopfAlgebra`) |
| s,t finite locally free | `[Module.Free R A]` + `[Module.Finite R A]` (chart-shrunk) + shear |
| conclusion: C → A f.l.f. + R = U ×_M U | **`IsHopfGalois ρ`** + bonus `Module.Free (coinvariants ρ) B` |

**Design pin (rank)**: hypothesize `[Module.Free R A]`, `finrank R A = r`, `0 < r` at the
abstract layer. Stacks 39.23.3 (rank decomposition, 03BI) is then VACUOUS — the application
shrinks the affine cover of S until O(G) is literally free (locally free ⟹ Zariski-locally
free), which the glue step (C4) does anyway. `0 < r` is automatic from the counit (ε splits
R ↪ A).

**Design pin (instances, v10.24(e))**: only the LEFT-factor B-module structure on `B ⊗[R] A`
is ever an instance. Everything t-sided (`ρ`-twisted) goes through the **shear automorphism**
Φ : B⊗A ≅ B⊗A (Φ(b⊗a) = ρ(b)·(1⊗a), inverse via the antipode: Ψ(b⊗a) = ρ(b)·(1⊗S(a)); note
Φ ∘ includeLeft = ρ) as an explicit term-built iso — never a second `Module` instance, never
rw-then-exact (v10.24(d)).

## The 03BM proof skeleton (verbatim-anchored)

1. **Surjectivity**: *"j is a monomorphism, and also finite (since already s and t are
   finite). Hence we see that j is a closed immersion […]. Hence A ⊗_C A → B is surjective."*
   Ours: `actPair_mono` (PROVEN) + finite (cancellation: source finite over E, target
   separated) + mathlib `IsClosedImmersion.iff_isFinite_and_mono` ⟹ Γ-surjectivity on the
   chart ⟹ `Surjective (canonicalGaloisMap ρ)`-precursor. This is the ONLY hypothesis of the
   abstract theorem beyond the comodule structure.
2. **Integrality** (03BJ): P(x) := charpoly of mult-by-`ρ(f)` on B⊗A (as B-module, left) —
   monic of degree r; coefficients land in `coinvariants ρ` (03BH pasting argument, becomes a
   coassociativity + `LinearMap.charpoly_baseChange` computation); Cayley–Hamilton
   (`LinearMap.aeval_self_charpoly`) + t♯ injective (shear + ff) ⟹ P(f) = 0. So B is
   integral over C, every element of degree exactly r.
3. **Surjectivity of Spec B → Spec C** (03BL(1) easy half): integral + injective ⟹ lying
   over (`Ideal.exists_ideal_over_prime_of_isIntegral`).
4. **Per-prime bootstrap**: for each prime p ⊆ C base change along a local flat
   C_p → C'_p with **infinite residue field** (03C3 gadget: C[x] localized at m[x]);
   invariants commute with flat base change (03BK(3) = mathlib `Flat/Equalizer.lean`).
5. **Semi-locality** (03BL(2) + 03BM): over local C with infinite residue field: all
   maximals of B lie over m (integrality); the k̄-points orbit theorem (03BL(2): the norm
   non-unit argument + prime avoidance + 03BK(2)) ⟹ B has finitely many maximals, mB ⊆ rad.
6. **Basis selection** (03C1): C local ∞ residue field, B semi-local, B⊗A free rank r over
   B-via-ρ (shear!), generated by the C-submodule s(B)… ⟹ ∃ x₁…x_r ∈ B basis of shape:
   B⊗A = ⊕ᵢ ρ(B)·(xᵢ⊗1). (Nakayama + infinite-field general position + induction.)
7. **Descent bootstrap** (03C8): with such a basis, the two-row equalizer comparison —
   top row = Amitsur equalizer of the ff map ρ (via shear iso, Descent 35.3.6 = GAP-1),
   bottom row = ⊕ᵢ C xᵢ by definition of C; cocartesian squares + middle iso ⟹
   **B = ⊕ᵢ C xᵢ free rank r, galois map iso**. Verbatim anchor: *"the middle vertical arrow
   is an isomorphism by assumption. Since the left two squares are cocartesian we conclude
   that also the left vertical arrow is an isomorphism. On the other hand, the horizontal
   rows are exact […]. Hence we conclude that also the right vertical arrow is an
   isomorphism."*
8. **Globalize**: injectivity of the galois map descends (kernel commutes with flat base
   change + ff `injective_of_tensorProduct` + zero-iff-zero-at-primes); flatness of C → B
   per-prime (`Module.Flat.of_flat_tensorProduct` + flat-at-primes); + step 3 surjectivity ⟹
   `Module.FaithfullyFlat` (`of_comap_surjective`); then B ⊗_C B ≅ B⊗A ⟹ B finitely
   presented C-module (GAP-2 ff descent of fp) ⟹ f.l.f.
   (`Module.Flat.projective_of_finitePresentation`). **IsHopfGalois ρ done.**

## mathlib inventory (verified in-tree, 2026-07-09 pin)

PRESENT: `Module.FaithfullyFlat` + `Descent.lean` (inj/surj/bij descent),
`Module.Flat.of_flat_tensorProduct` (flatness descent), `Flat/Equalizer.lean` +
`AlgHom.tensorEqualizer` (equalizer vs flat base change = 03BK(3)),
`Module.Flat.projective_of_finitePresentation` (00NX), `LinearMap.charpoly` +
`aeval_self_charpoly` (CH) + `charpoly_baseChange` + `det_baseChange`,
`LinearMap.isUnit_iff_isUnit_det`, `IsClosedImmersion.iff_isFinite_and_mono` (29.45.15),
`Ideal.exists_ideal_over_{prime,maximal}_of_isIntegral` (lying over),
`Module.FaithfullyFlat.{of_comap_surjective, tensorProduct_mk_injective}`,
`Module.free_of_flat_of_isLocalRing`, `Ideal.subset_union_prime` (avoidance),
`HopfAlgebra`/`Bialgebra` classes.

GAPS (all route-independent, upstreamable):
- **GAP-1 Amitsur equalizer** (Descent 35.3.6, degree ≤ 1): ff R→S ⟹
  range (algebraMap R S) = eqLocus(·⊗1, 1⊗·). ~20 lines on `tensorProduct_mk_injective`.
- **GAP-2 ff descent of `Module.Finite` + `Module.FinitePresentation`** (03C4).
- **GAP-3 flat local extension with infinite residue field** (03C3): C[x] at m·C[x].
- **GAP-4 semi-local basis selection** (03C1) + semi-local bookkeeping (maximals over m,
  mB ⊆ rad under integrality, finitely-many-maximals from orbit finiteness).
- **GAP-5 charpoly-coefficient invariance** (03BH in comodule form) — the pasting square as
  a coassoc + charpoly_baseChange computation. The mathematically novel translation.
- **GAP-6 the k̄-points orbit theorem** (03BL(2)) — norm-unit linear algebra
  (`isUnit_iff_isUnit_det` on fiber rings) + prime avoidance + 03BK(2)(a)'s (x−f)^n trick.
  (Stacks' two "insert future reference on property determinant here" gaps close with:
  unit at all fiber points ⟹ unit in finite k-algebra ⟹ det unit; ff reflects units.)

NOTE (contingency, likely SKIPPABLE): "f.g. projective of constant rank over semi-local is
free" — not needed on the planned path because every module 03C1 touches is free via the
shear; revisit only if a leaf walls.

## Leaves

**Wave A — mathlib gaps (parallel-safe, no comodules)**
- **[HG-A1]** `ForMathlib/FaithfullyFlatEqualizer.lean` — GAP-1. (~1 session)
- **[HG-A2]** `ForMathlib/FaithfullyFlatFiniteDescent.lean` — GAP-2. (~1 session)
- **[HG-A3]** `ForMathlib/FlatLocalInfiniteResidue.lean` — GAP-3. (~0.5 session)
- **[HG-A4]** `ForMathlib/SemilocalBasis.lean` — GAP-4 (03C1 + bookkeeping). (~2 sessions)

**Wave B — the comodule-native core (sequential-ish)**
- **[HG-B1]** `ForMathlib/CoactionShear.lean` — shear automorphism Φ/Ψ (antipode),
  Φ∘includeLeft = ρ, t-side freeness transport, the tensor forms of lemma-diagram /
  lemma-diagram-pull (cocartesian squares; the (α,β)↦(α,α⁻¹β) iso). (~2 sessions)
- **[HG-B2]** `ForMathlib/CoactionCharpoly.lean` — GAP-5 + 03BJ: coefficient invariance,
  CH, **B integral over coinvariants**. FIRST HARD LEAF. (~2–3 sessions)
- **[HG-B3]** `ForMathlib/CoinvariantsBaseChange.lean` — 03BK(1)(3) + the (2)(a)
  (x−f)^n statement (03BK(2)(b) only if B4 needs it). (~1–2 sessions)
- **[HG-B4]** `ForMathlib/CoinvariantsPoints.lean` — GAP-6 + 03BL: Spec-surjectivity,
  k̄-orbit theorem, finitely-many-maximals. SECOND HARD LEAF. (~2–3 sessions)
- **[HG-B5]** `ForMathlib/HopfGaloisBootstrap.lean` — 03C8 comodule form (two-row equalizer
  comparison; consumes A1 + B1). THIRD HARD LEAF (Lean-treacherous: the two tensor
  structures; named handles, term isos). (~2 sessions)
- **[HG-B6]** `ForMathlib/HopfGaloisTheorem.lean` — 03BM assembly:
  `theorem isHopfGalois_of_surjective_galoisPrecursor`: [HopfAlgebra R A] [Module.Free R A]
  (finrank = r, 0 < r) (hco : IsCoaction ρ) (hsurj : Surjective β₀) → `IsHopfGalois ρ`
  (+ bonus `Module.Free (coinvariants ρ) B`). (~2 sessions)

**Wave C — E-geometry application (C1/C2 parallel with B)**
- **[HG-C1]** `GroupScheme/TranslationCoaction.lean` — 3a-ii: ρ on a G-stable chart via
  O(G ×_S U) ≅ B ⊗ A; `IsCoaction ρ` from the group axioms; Hopf instances from p2's layer
  (CONSUME-check their Milestone 1 each session; if slipped, take `[HopfAlgebra]` as a
  section hypothesis and wire later — no gate). (~3–4 sessions)
- **[HG-C2]** `GroupScheme/TranslationFreeness.lean` — actPair finite (cancellation) +
  closed immersion + chart Γ-surjectivity ⟹ the `hsurj` input. (~1–2 sessions)
- **[HG-C3]** `GroupScheme/StableAffineCover.lean` — 3a-iii: Stacks lemma-find-invariant-
  affine (norm-shrinking, reuses B2's machinery); E quasi-projective over affine base
  pieces ⟹ finite orbits in affines. (~2–3 sessions)
- **[HG-C4]** `GroupScheme/SubgroupQuotientConstruction.lean` — 3a-iv: glue per-chart
  `Spec (coinvariants ρ)` on the `SchemeQuotient` GlueData pattern; discharge the six
  `SubgroupQuotient` pins via `isColimit_of_isHopfGalois` + `exists_unique_lift_of_isColimit`
  + `isInvariant_iff_coequalizes`. p2-stack-scale. (~3–5 sessions)

## Milestones (charter report points)
- **M1** = this document (leaf plan boarded). — DONE
- **M2** = Wave A green (4 gap files, axiom-clean).
- **M3** = [HG-B2] integrality landed.
- **M4** = [HG-B4] + [HG-B5] landed (hard cores done).
- **M5** = **[HG-B6]: the abstract `IsHopfGalois` theorem** — the headline milestone.
- **M6** = [HG-C1]+[HG-C2]: the translation co-action on each chart is Hopf-Galois.
- **M7** = [HG-C3]+[HG-C4]: E/G exists, six pins discharged — CHARTER COMPLETE.

## Risks / walls (pre-registered)
1. **B5's two-tensor-structure bookkeeping** — the known minefield (v10.24(d)/(e) apply in
   full; every seam its own private lemma with explicit instance args).
2. **B2's invariance computation** — the pasting square in tensor coordinates; if the direct
   computation grinds, decompose via `Coalgebra.repr` sums (sweedler-style finite sums) per
   v10.24(a).
3. **C1 plumbing** (O(G×U) ≅ B⊗A over varying opens) — the "never let unification meet a
   concrete scheme" rule; named handles for every chart iso.
4. **p2 dependency** is soft (hypothesis-parametric until their Milestone 1) — no gate.
5. 03BL(2)'s Stacks proof has two "future reference" holes — closed above (norm-unit facts);
   if a third hole appears in formalization, board it before grinding (v10.24).

## [HG-B2] design refinement (NEW-HOPF, post-B1): the Δ-matrix conjugation route

The 03BH coefficient-invariance is formalized NOT by norm-base-change through the
cartesian squares (twisted-algebra `letI` diamonds) but by **matrix conjugation**:

- Fix an R-basis `e` of A (rank r). `E := B⊗A` has B-basis `1⊗eⱼ`; mult-by-`ρ(f)` has
  matrix `M(f) ∈ Mat_r(B)`; `P = charpoly (M(f))` (`Matrix.charpoly`, bridged to
  `LinearMap.charpoly` via `charpoly_toMatrix`).
- **The Δ-matrix**: `Δ(eⱼ) = ∑ᵢ eᵢ ⊗ Tᵢⱼ`, `T ∈ Mat_r(A)`. Basis-expansion of
  coassoc/counit gives the matrix-coalgebra identities `Δ(Tᵢⱼ) = ∑ₖ Tᵢₖ⊗Tₖⱼ`,
  `ε(Tᵢⱼ) = δᵢⱼ`; the antipode axiom then gives **`T·S(T) = 1 = S(T)·T`** (entrywise S) —
  `T ∈ GL_r(A ⊆ B⊗A)`.
- **The conjugation identity**: applying `id_B⊗Δ` to the defining expansion of `M(f)` and
  re-expanding via coassociativity yields `ρ(M(f)) = T⁻¹ · (M(f)⊗1) · T` (orientation to
  be fixed in-proof) in `Mat_r(B⊗A)`.
- Charpoly is conjugation-invariant and commutes with `Polynomial.map` of entrywise ring
  maps (`Matrix.charpoly_map`), so `map ρ P = charpoly ρ(M(f)) = charpoly (M(f)⊗1) =
  map includeLeft P` — i.e. every coefficient lies in `coinvariants ρ`. **Hopf (antipode)
  IS used** (T-invertibility); freeness of A over R is the only other input.
- Integrality (03BJ) then: CH (`aeval_self_charpoly`) evaluated at 1 gives
  `∑ includeLeft(Pᵢ)·(ρf)^i = 0`; coefficients coinvariant ⟹ `= ρ(∑Pᵢf^i) = ρ(P(f))`;
  `ρ` injective from counitality (retraction `rid∘(id⊗ε)`) ⟹ `P(f) = 0` — monic degree-r
  integrality of every `f : B` over `coinvariants ρ`. No twisted instances anywhere.

## [HG-B2] the conjugation identity — precise derivation (banked mid-build)

Status: Δ-matrix machine LANDED (comulMatrix T, εT = δ, ΔT = matrix-comul, T·S(T) =
S(T)·T = 1, isUnit). Remaining chain (each its own increment):

1. **Right-slot mirror**: `rightCoeff`/`comulMatrixR` (T̃ᵢⱼ := right-slot expansion,
   `Δ(eⱼ) = ∑ₚ T̃ₚⱼ ⊗ eₚ`) + mirrored identities via `rTensor_counit_comp_comul` and the
   other coassoc grouping ⟹ `isUnit (comulMatrixR)`. Same proof skeletons.
2. **Multiplication matrix**: `mulMatrix u ∈ Mat_r(B)` of `lmul u` on `E = B⊗A`, basis
   `vⱼ = 1⊗eⱼ`: `u·vⱼ = ∑ᵢ (mulMatrix u)ᵢⱼ ⊗ eᵢ`. Transport lemma: for an R-algebra map
   `φ : B → B''`: `mulMatrix ((φ ⊗ id_A) u) = φ(mulMatrix u)` entrywise (apply φ̂ to the
   defining expansion; φ̂ fixes `1⊗eⱼ`).
3. **The (★) identity**: in `D = (B⊗A)⊗[R]A` with B' := B⊗A acting on the first two slots
   and last-slot basis `w'ₚ = (1⊗1)⊗eₚ`: apply `δ := id_B⊗Δ` (equivalently
   `assoc∘(ρ⊗id_A)`, by IsCoaction.coassoc) to the defining expansion of
   `M := mulMatrix (ρ f)`:
   - LHS: `δ(ρf)·δ(vⱼ)`; `δ(vⱼ) = ∑ₚ Θₚⱼ • w'ₚ` with `Θₚⱼ := 1_B ⊗ T̃ₚⱼ ∈ B'`;
     `(ρ⊗id)(ρf)·w'ₚ = ∑ᵢ ρ(Mᵢₚ) • w'ᵢ` (transport lemma at φ = ρ, coassoc);
     ⟹ LHS = `∑ᵢ (∑ₚ ρ(Mᵢₚ)·Θₚⱼ) • w'ᵢ`.
   - RHS: `δ(∑ᵢ Mᵢⱼ⊗eᵢ) = ∑ᵢ Mᵢⱼ ⊗ Δ(eᵢ) = ∑ₚ (∑ᵢ Θₚᵢ·ι(Mᵢⱼ)) • w'ₚ` (right-slot
     expansion of Δ(eᵢ)).
   - last-slot coefficient injectivity (the generic extractor at M := B⊗A) ⟹
     **`ρ(M)·Θ = Θ·ι(M)` in Mat_r(B⊗A)** (★), where `Θ = (comulMatrixR).map (1⊗·)` is a
     unit (step 1 + Matrix map of a unit along a ring hom).
4. **Invariance + integrality**: (★) ⟹ `ρ(M) = Θ·ι(M)·Θ⁻¹` ⟹ `charpoly (ρ M) =
   charpoly (ι M)` (det-conjugation, explicit two-sided inverse) ⟹ with
   `Matrix.charpoly_map`: `map ρ (charpoly M) = map ι (charpoly M)` ⟹ every coefficient
   ∈ `coinvariants ρ`. Then CH (`Matrix.aeval_self_charpoly` on M / or the eval₂ form) at
   `f`: `eval₂ ι (ρf) P = 0` ⟹ (coefficients coinvariant: ι(Pᵢ) = ρ(Pᵢ)) `ρ(P(f)) = 0`
   ⟹ (ρ injective via counit retraction `rid∘(id⊗ε)∘ρ = id`) `P(f) = 0`: **every f : B
   is integral of monic degree r over coinvariants ρ** = the 03BJ deliverable
   `isIntegral_coinvariants`.

## [HG-B6] input inventory update (post-B3-core)

- `Algebra.IsIntegral.tensorProduct : Algebra.IsIntegral C B → Algebra.IsIntegral C' (C' ⊗[C] B)`
  EXISTS in mathlib — so per-prime integrality of the base-changed situation is FREE from
  03BJ (`isIntegral_coinvariants` packaged as `Algebra.IsIntegral C B` via the tower) and
  needs NO base-changed co-action for the integrality leg. The base-changed co-action
  (`coactionBaseChange`, B3) is still consumed by the 03C1-application and the 03C8
  bootstrap upstairs.
- B3 status: `coactionBaseChange` + 03BK(3) (`mem_coinvariants_coactionBaseChange_iff`,
  flat) + counit transport LANDED. Remaining: coassoc transport (pentagon-style auxes
  through `baseChangeAssoc` — do ext-two-legs on B′ = C′-leg + B-leg, then per-leg pure-
  tensor inductions), then package `IsCoaction (coactionBaseChange …)`.

## [HG-B4] the k̄-orbit theorem — sharpened plan (all inputs LANDED)

Landed in `CoinvariantsPoints.lean`: 03BL-surjectivity (lying-over), the invariant
charpoly = (X−f)^r, `coactionBaseChange_naturality`, and **the power witness**
`pow_card_mem_range_algebraMap_of_mem_coinvariants` (03BK(2)(a) constant-coefficient
form via the MvPolynomial flat cover).

The orbit core, reduced to landed machinery + elementary facts:
**Statement**: k alg. closed field, C-algebra via c; a₀ a₁ : B →ₐ k with a₀|C = a₁|C ⟹
∃ b : B⊗A →ₐ k, b∘ρ = a₀ ∧ b∘includeLeft = a₁.
**Proof**: suppose not. Work in B_k := k ⊗[C] B with ρ_k := coactionBaseChange.
(i) the k-points of B⊗A over a₁ (i.e. χ∘ι = ā₁-precomposites) = k-points of the finite
k-algebra k⊗[B,a₁](B⊗A) ≅ k⊗[R?]A-twist — finitely many (finite k-algebra: finitely many
maximals, residue k by alg-closedness); call their ρ-restrictions a₁',…,aₙ' ≠ a₀ (else b
exists).
(ii) prime avoidance (`Ideal.subset_union_prime`): f̃ ∈ ker(ā₀) ∖ ⋃ ker(āᵢ') in B_k
(distinct maximals).
(iii) g := coactionCharpoly-const-coeff = ±det (mulMatrix (ρ_k f̃)) ∈ coinvariants ρ_k
(coeff-mem, B2).
(iv) g is NOT a unit: else det unit ⟹ mulMatrix invertible ⟹ lmul(ρ_k f̃) surjective ⟹
ρ_k f̃ unit ⟹ (counit retraction reflects units) f̃ unit — contra f̃ ∈ ker ā₀.
(v) ā₁(g) ≠ 0: transport det along ā₁ (`mulMatrix_map` + `RingHom.map_det`); the image of
ρ_k(f̃) in the artinian k-algebra k⊗A is non-vanishing at every maximal (the maximals =
the χ's of (i); value at χ = aᵢ'(f̃) ≠ 0 by (ii)) ⟹ unit ⟹ det unit ⟹ ≠ 0.
(vi) power witness: g^r = scalar c ∈ k; (v) ⟹ c ≠ 0 ⟹ c unit ⟹ g unit — contradicts
(iv). ∎
**Corollary (GAP-6, what 03BM consumes)**: C local ⟹ B_loc semi-local: maximals of B over
m_C are pairwise related through k̄-points (the theorem at k := algebraic closure of the
residue field) and each relation-class over a fixed maximal is bounded by the finite
ι-fibre — finitely many maximals, m·B ⊆ rad.

Elementary gaps to build alongside: finitely-many-k-points of a finite k-algebra
(alg-closed residue fields); "outside all maximals ⟹ unit"; the χ-vs-bᵢ evaluation
bookkeeping. All mathlib-adjacent.

## [HG-B4] final assembly — interface pinned (all ingredients green as of this commit)

**Statement (R-algebra-map form; no k-structure on B)**:
`theorem exists_algHom_comp_eq [IsAlgClosed k] [Algebra R k] (hρ : IsCoaction ρ)
  (a₀ a₁ : B →ₐ[R] k) (hagree : ∀ x ∈ coinvariants ρ, a₀ x = a₁ x) :
  ∃ χ : (B ⊗[R] A) →ₐ[R] k, χ.comp ρ = a₀ ∧ χ.comp includeLeft = a₁`.
Proof over the k-situation: `letI : Algebra (coinvariants ρ) k := (a₁-restricted).toAlgebra`
(hagree makes a₀,a₁ the SAME C-structure); B_k := k⊗[C]B, ρ_k := coactionBaseChange;
ā₀ ā₁ : B_k →ₐ[k] k the tensor-lifts. Contradiction pipeline (all LANDED):
S := the (finite) k-points over ā₁ (`finite_setOf_comp_includeLeft_eq`); if no χ works, ā₀
∉ ρ_k-restrictions of S; avoidance `exists_mem_ker_notMem_ker` gives f̃;
g := det (mulMatrix (ρ_k f̃)): non-unit (`not_isUnit_det_mulMatrix_coaction`); ā₁(g) ≠ 0:
`RingHom.map_det` + `mulMatrix_map` at φ := ā₁ gives det (mulMatrix_k u) for
u := (map ā₁ id)(ρ_k f̃) ∈ k⊗A; u is a unit by `isUnit_of_forall_algHom_ne_zero` (each
ψ-value = (ψ∘(map ā₁ id))∘ρ_k at f̃ = a member-of-S∘ρ_k-value ≠ 0 — the composite
ψ∘(map ā₁ id) IS an S-member since its ι-restriction is ā₁); unit ⟹ det-unit ⟹ ≠ 0;
POWER WITNESS: g^r = scalar c, ā₁-image ≠ 0 ⟹ c ≠ 0 ⟹ g unit — contradiction.
NOTE: g ∈ coinvariants ρ_k via `coactionCharpoly_coeff_mem` at coeff 0 up to sign
((−1)^r·det = coeff 0; adjust by the unit sign).

**GAP-6 corollary** (what 03BM consumes): C' local (κ := residue, k := κ̄), B' = C'⊗[C]B
flat base change, integral (Algebra.IsIntegral.tensorProduct): every maximal n of B' gives
χ_n : B' →ₐ[R] k via `IsAlgClosed.lift` over κ extending the CANONICAL κ↪k (so all χ_n
agree on C'-scalars = coinvariants ρ' by 03BK(3)); pairwise the orbit theorem connects
them through the finite ā-fibre S ⟹ the kernel map n ↦ ker χ_n is finite-to-one into a
finite set ⟹ **finitely many maximals; m·B' ⊆ rad** (all maximals over m by integrality).

## Appendix: [HG-B5] derivation — 03C8 WITHOUT the two-row diagram (banked 2026-07-10)

Stacks 03C8 dictionary check (fetched): hypothesis "B = ⊕ᵢ s♯(A)·t♯(xᵢ)" = ours
"`hb : Basis ι' B (B⊗[R]A)` (canonical LEFT structure) with `hb i = ρ (x i)`";
conclusions "A = ⊕ᵢ C·xᵢ" + "B ≅ A⊗_C A" = ours "`Basis ι' C B` on the `x i`" +
"`canonicalGaloisMap ρ` bijective". The Stacks two-row equalizer comparison is
REPLACED by an elementwise coassociativity computation — no Amitsur, no ff of ι,
no twisted instances, no r=0 edge case:

- **L1 `includeLeftBasis`**: `(hb.baseChange D).map cancelBaseChange` (D := B⊗A) is a
  D-basis of D⊗[R]A with vectors vᵢ = (map ι id)(hb i). [`cancelBaseChange`
  Tower.lean:436, formula (a•m)⊗n.]
- **L2 `w-cancellation`**: wᵢ := (map ρ id)(hb i); ∑ dᵢ•wᵢ = 0 ⟹ d = 0. Via
  Ξ := congr(shearEquiv, refl): map ρ id = Ξ∘(map ι id) (elementwise, Φ∘ι=ρ) and
  Ξ((d⊗1)z) = (Φd⊗1)Ξ(z), so ∑dᵢ•wᵢ = Ξ(∑ Φ⁻¹(dᵢ)•vᵢ); L1-independence kills.
- **L3 `coords in C`**: cᵢ := hb.repr (ρ f) i. deltaTilde vs (map ρ id) on the
  expansion ρf = ∑ ι(cᵢ)·hb i: bridge (`deltaTilde_comp_coaction`) at f AND at each
  x i; `deltaTilde_tmul_one` gives deltaTilde(ι c) = ι_D(ι c); subtract ⟹
  ∑(ι cᵢ − ρ cᵢ)•wᵢ = 0 ⟹ [L2] ρ(cᵢ) = ι(cᵢ) ⟹ cᵢ ∈ C (AlgHom.mem_equalizer).
- **L4 `coinvariantsBasis`**: Basis.mk on x. Independence: apply ρ to ∑gᵢxᵢ=0,
  gᵢ∈C turns ρ-coeffs into ι-coeffs = B-smul on hb ⟹ zero. Span: f = σ(ρf)
  = ∑ cᵢxᵢ with cᵢ ∈ C by L3 (σ = counitRetraction, both retraction laws).
- **L5 `bijective_canonicalGaloisMap_of_basis`**: γ is left-B-linear
  (γ(b⊗1)=b⊗1); (coinvariantsBasis).baseChange B has vectors 1⊗xᵢ ↦γ ρ(xᵢ) = hb i:
  basis-to-basis ⟹ bijective (Basis.equiv + Basis.ext + congrFun).

B6 consumes: L4 ⟹ Free+Finite ⟹ FaithfullyFlat C B (nonempty index when B
nontrivial via σ-retraction; subsingleton branch separate); L5 = galois half.

## Appendix: [HG-B6] assembly plan (banked 2026-07-10)

Target: `isHopfGalois_of_surjective_galoisPrecursor` — hypotheses `IsCoaction ρ`,
`[Module.Free R A] [Module.Finite R A]`, and `hsurj : Surjective (productMap ι ρ :
B⊗[R]B → B⊗[R]A)` (the action-pair/closed-immersion input; rules out the trivial
co-action). Conclusion `IsHopfGalois ρ` (galois + faithfullyFlat).

Sub-leaves (file `HopfGaloisTheorem.lean`):
- **[B6-a] generalized galois map**: `bijective_galoisProductMap_of_basis` — for ANY
  `C₀` with `[Algebra C₀ B] [Algebra C₀ (B⊗[R]A)] [IsScalarTower C₀ B (B⊗[R]A)]`,
  `hcoinv : ∀ c, ρ (algebraMap C₀ B c) = (algebraMap C₀ B c) ⊗ₜ 1`, and a C₀-basis
  `(x i)` of `B` with `ρ (x i)` a left-B-basis of `B⊗A`: the productMap
  `B⊗[C₀]B →ₐ[C₀] B⊗[R]A` (left inclusion ⊗ ρ-as-C₀-hom) is bijective. Proof =
  verbatim B5-L5 (left-B-linear, basis-to-basis). KILLS the C''-vs-C' juggling: at
  the per-prime site C₀ := C'ₚ works directly.
- **[B6-b] flat-cover injectivity**: `f : M →ₗ[C] N` injective ⟸ ∀ p maximal,
  `C'ₚ ⊗[C] f` injective, where C'ₚ := LocalPolynomialExtension(Localization.AtPrime p)
  (A3). Chain per p: flat ⟹ ker commutes with ⊗; ff(C_p → C'ₚ) ⟹ ker(f_p) = 0;
  `Submodule.eq_bot_of_localization`-style glue. cancelBaseChange for the composite
  C'⊗[C_p](C_p⊗[C]M) ≅ C'⊗[C]M.
- **[B6-c] per-prime instantiation** (p maximal in C := coinvariants ρ):
  ρ' := coactionBaseChange (B3) over C'ₚ; IsLocalRing (coinvariants ρ') via
  `IsLocalRing.of_surjective'` from B3's 03BK(3) iff (flat ✓); π : C' ↠ coinvariants ρ'
  INJECTIVE too (C ↪ B tensored with flat C' + rid — so π is a RingEquiv-ish);
  Infinite (ResidueField (coinvariants ρ')) via the max-preimage quotient iso from
  Infinite (ResidueField C') (A3); GAP-6 (B4) ⟹ enumerate ALL maximals Fin s;
  hmn = B4 add-on; hN: B'-span of range(ρ'-as-C''-linear) = ⊤ from hsurj base-changed;
  hr: finrank B' (B'⊗A) = card (hopfBasisIndex) via baseChange basis; A4-03C1 ⟹
  y i = ρ'(x i) basis ⟹ B5-L4 C''-basis of B' ⟹ convert to C'-basis along π
  (independence via π injective, span via π surjective) ⟹ B6-a at C₀ := C'.
- **[B6-d] comparison squares**: C'⊗[C]γ ≅ γ̂ under (assoc + cancelBaseChange) on the
  source and baseChangeAssoc (B3) on the target; elementwise on c'⊗b₁⊗b₂. ⟹
  Injective (C'⊗[C]γ) ∀p ⟹ [B6-b] γ injective. Surjectivity of γ: GLOBAL one-liner
  from hsurj (γ ∘ (B⊗[R]B ↠ B⊗[C]B) = productMap).
- **[B6-e] faithful flatness**: per-p: B' free over C' (the converted basis) ⟹
  Flat C' B'; descend along ff C_p → C'ₚ (`Module.Flat.of_flat_tensorProduct`-family)
  + flat-is-local ⟹ Flat C B. Then Spec-surjectivity = B4's
  `exists_prime_over_coinvariants` (lying-over, global) ⟹
  `Module.FaithfullyFlat.of_comap_surjective`-family ⟹ FaithfullyFlat C B.
- **[B6-f]**: assemble `IsHopfGalois ρ` = ⟨⟨inj, surj⟩, ff⟩. = **M5**.

Name-verification queue (before writing): Algebra.TensorProduct.productMap;
Descent.lean's injective-descent names; flat-local-property lemma; of_comap_surjective
exact form; Submodule.eq_bot_of_localization; AlgebraTensorModule.assoc heterobasic.

## Appendix: Wave C scoping (banked 2026-07-10, post-M5)

Substrate map (all p0, READ-ONLY): `GroupScheme/Subgroup.lean` (`FiniteLocallyFreeSubgroup E`:
fields incl. `ι : G.X ⟶ E.E`, `π : G.X ⟶ S`, group-scheme structure over S),
`GroupScheme/TranslationAction.lean` (`translationAction G : (Over-mk) ⟶ E.asOver` =
translation `G ×ₛ E → E`, `actionProj`, `actPair G` (graph map), `translationAction_eq_mul`,
`isInvariant_iff_coequalizes`, `exists_unique_lift_of_isColimit`),
`GroupScheme/SubgroupQuotient.lean` (SIX sorried pins = the target),
`ForMathlib/HopfGaloisQuotient.lean` (`isColimit_of_isHopfGalois` — consumes M5's
`IsHopfGalois` per chart). p2's Hopf-instance layer NOT yet landed (their sentinel: BB-DELIGNE
L6c) ⟹ hypothesis-wired `[HopfAlgebra R A]` throughout Wave C (charter's soft edge).

Wave-C leaves (revised post-M5):
- **[HG-C1] chart co-action**: for a G-stable affine open `U = Spec B ⊆ E` with A := Γ(G)
  (finite locally free Hopf over Γ(S)-charts; work over affine base S = Spec R first),
  define `ρ_U := Γ(act|_U) ∘ (Γ(G ×ₛ U) ≅ B ⊗[R] A)` and prove `IsCoaction ρ_U` from the
  action diagrams under Spec-Γ (mechanical AffineScheme-equivalence plumbing; the Künneth
  iso for affine `G` over affine base is `Algebra.TensorProduct`-Spec).
- **[HG-C2] precursor surjectivity**: `actPair G` is a closed immersion (freeness of
  translation on a group: actPair = (mul, pr₂) is an iso onto graph — actually for
  E-translation actPair is a MONO + finite ⟹ closed immersion ⟹ Γ-surjective on charts) —
  gives `Surjective (galoisPrecursor)` per chart. KEY: for a GROUP acting on ITSELF by
  translation the action is free — actPair is even an isomorphism G×E ≅ G×E?? NO — onto its
  image E×_{E/G}E; the ring-level surjectivity is what M5 needs; route through
  `IsClosedImmersion.iff_isFinite_and_mono` (inventory) + mono-of-free-action.
- **[HG-C3] G-stable affine cover** of E (KM-style: E/S projective + G-orbits finite ⟹
  stable affine refinement; hardest geometry leaf).
- **[HG-C4] glue**: per-chart `isColimit_of_isHopfGalois` + GlueData ⟹ global E/G ⟹
  six pins (via `exists_unique_lift_of_isColimit` + `isInvariant_iff_coequalizes`).

M5's interface consumed per chart: `isHopfGalois_of_surjective_galoisPrecursor R A ρ_U
(hρ : IsCoaction ρ_U) (hsurj : Surjective (galoisPrecursor R A ρ_U))` with
`[Module.Free R A] [Module.Finite R A]` from G finite-locally-free (free per chart after
shrinking — or hypothesis-wire freeness and let C3 provide free charts).

## Appendix: Wave C — pin-map + C3 cover strategy (banked 2026-07-10)

**The six pins** (`GroupScheme/SubgroupQuotient.lean`): DATA `quotient`, `quotientS`,
`quotientπ`; PROPS `quotientπ_over`, `quotientπ_isInvariant`, `quotient_lift`.
`quotientπ_hom_ext` + the `[N]`-factorization layer are ALREADY proven against the pins.
Discharge order: C3 cover → C1 per-chart coaction (fills `StableAffineChartData`) →
C2 precursor-surjectivity → per-chart `isColimit_of_isHopfGalois` (p0, proven) →
C4 GlueData assembly = the three DATA + three PROP pins.

**C3 strategy (KM 3.7-style, sketched)**: `G ⊆ E` is itself an effective relative Cartier
divisor (T-SG1 bridge `toRelEffCartierDiv` exists on the board). Stable opens: for any
finite set of sections `x i : S → E`, the complement `E ∖ ⋃ᵢ (xᵢ + G)` is `G`-stable
(translation permutes each coset `xᵢ + G`). Cover: affineness of `E ∖ (x + G)`: the
divisor `x + G` has degree `N = rank G ≥ 1` ⟹ ample on fibres (genus-1: any degree ≥ 1
divisor is ample) ⟹ complement affine (relative version needed — the KM-style
`E ∖ D` affine for `D` fibrewise-ample relative effective Cartier). Coverage: need the
cosets `xᵢ + G` to have empty common intersection — locally on `S` pick sections through
distinct residue-field points; if `E(S)`-sections are scarce, fppf-localize the base
(the pins are fppf-local?? NO — pins are global statements: the cover argument must work
Zariski-locally on `S`; KM use: after Zariski-shrinking `S`, `E → S` has enough sections
through any fibre-point avoiding a divisor — via smoothness (étale-local sections) +
spreading. ALTERNATIVE cheaper: two charts suffice if `S` affine + a section `x₀` with
`(x₀+G) ∩ G = ∅` — such `x₀` exists Zariski-locally by smoothness of `E∖G → S`
(surjective smooth ⟹ étale-locally sections; Zariski on the base after finite-flat
spreading...). Precise route to be fixed at C3-start; candidates: (a) KM 3.7 verbatim
(refs/katz-mazur), (b) Deligne's trick via the group law: cover by `E∖G` and
`translate-by-generic-2-torsion`, (c) fppf-descend the QUOTIENT construction itself
(needs quotient-descent lemmas — heavier).

**C1 bridge-shape** (`StableAffineChartData` producer): affine base patch `Spec R ⊆ S`,
`G|_R = Spec A`, stable chart `U = Spec B`; the restricted action
`G ×_R U → U` (from stability) dualizes: `ρ := ΓSpecIso ∘ Γ(act|) ∘ pullbackSpecIso⁻¹`;
IsCoaction from the two action-diagrams under Γ (contravariant-functor chases);
C2: `actPair|_U : G ×_R U → U ×_R U` closed immersion (finite + mono; mono from
free translation: (t,x)↦(x+t,x) has the retraction-difference (y,x)↦(y−x,x)?! —
actPair is an ISO onto `(x+G)-graph`?? NO — actPair (t,x) ↦ (x+t, x): INJECTIVE with
left-inverse (y,x) ↦ (y−x, x) defined on the IMAGE — actually (y,x)↦(y−x,x) is defined
on ALL of E×E and retracts actPair ⟹ actPair is a SPLIT MONO ✓✓ even a closed immersion
via finite+mono; Γ-dual of split mono with finite... ⟹ precursor surjective needs
Γ(actPair) surjective on the chart: closed immersion of affines ⟹ surjective ✓).
NOTE: the retraction (y,x) ↦ (y−x, x) needs y−x ∈ G on the image — as a map E×E → E×E
it retracts INTO G×E only on the image; the SPLIT-MONO statement: r ∘ actPair = id where
r := (sub, pr₂) : E×E → E×E restricted... r∘actPair(t,x) = ((x+t)−x, x) = (t,x) ✓ BUT r
lands in E×E not G×E — the retraction must corestrict: (x+t)−x = ι(t) factors through G
⟹ r∘actPair = ι×id-section... the correct split-mono: actPair : G×E → E×E has
`(sub, pr₂) ∘ actPair = (ι, id)-inclusion` — so actPair is mono because (ι,id) is ✓
(ι closed immersion). Finite: G×E → E×E is finite (base change of finite ι?? actPair =
(shear iso of E×E) ∘ (ι × id): the SHEAR (y,x)↦(y+x,x) is an AUTOMORPHISM of E×E and
actPair = shear ∘ (ι ×ₛ id_E) ✓✓ ⟹ actPair = iso ∘ closed-immersion ⟹ CLOSED IMMERSION,
free ✓ — C2 is EASY given the shear-automorphism of E ×ₛ E (group-scheme shear, mathlib
`?`; buildable from μ, inv as an iso with explicit inverse (y,x)↦(y−x,x)).

## [HG-C2] last-mile route (banked 2026-07-10; shear+decomposition COMMITTED green)

Remaining: `IsClosedImmersion G.actPair.left`. Route:
`(ι⊗𝟙).left`-closed-immersion via `pullbackRightPullbackFstIso E.π E.π G.ι :
pullback G.ι (fst E.π E.π) ≅ pullback (G.ι ≫ E.π) E.π` (note `G.ι ≫ E.π = G.π` rfl) +
mathlib instance `IsClosedImmersion (pullback.snd G.ι (fst E.π E.π))` (base change of ι)
+ iso-composition; identify `(ι⊗𝟙).left = iso.inv ≫ pullback.snd _ _` by
`pullback.hom_ext` + the `pullbackRightPullbackFstIso_inv_{fst,snd}` simp-set. Then
`actPair_eq_shear` + `shearAuto.left`-iso ⟹ done. CAUTION (cost sink discovered):
`pullback.map` is an *abbrev* for `pullback.lift`; heq-style comparisons flake on
HasPullback-instance-term mismatches between the Over-monoidal chosen pullbacks and
fresh synthesis — prefer mathlib's own iso-simp-lemmas over hand-built `pullback.lift`
comparisons, or go through `IsPullback.of_isoPullback`. Downstream consumer: per-chart
Γ-surjectivity = `IsClosedImmersion.isAffine`-restriction + surjective-on-sections
(`IsClosedImmersion` on affines ⟹ `Function.Surjective (Γ-map)` — mathlib
`IsClosedImmersion.isAffine_iff`-adjacent / `Scheme.Hom.appTop`-surjectivity:
`IsClosedImmersion` over affine ⟹ surjective appTop ✓ exists as
`IsClosedImmersion.surjective_appTop`-ish; verify name).

[HG-C2]-mile addendum (2026-07-10 second attempt): the `pullbackRightPullbackFstIso`-route
ALSO hits motive-not-type-correct (its domain `pullback (G.ι ≫ E.π) E.π` is defeq-but-not-
syntactic to `pullback G.π E.π`; even `rw [Category.assoc]` fails on the heterogeneous ≫).
NEXT ROUTE (fresh session): build the `IsPullback ((ι⊗𝟙).left) (snd G-side) (snd E-side) (𝟙 E)`
-square?? NO — correct square: `IsPullback ((ι⊗𝟙).left) (pullback.fst G.π E.π)
(pullback.fst E.π E.π) G.ι` via `IsPullback.of_right` against the two `of_hasPullback`
squares (paste along the fst-legs; the comm-square is `pullback.lift_fst`-rfl), then
`MorphismProperty.of_isPullback`. All objects stay in the `G.π`-spelling — no defeq-cast
crossings. Alternatively: prove the CHART-LEVEL Γ-surjectivity directly in C1's affine
setting (Spec-side: the chart-restricted actPair between affines; closed-immersion there
= surjective ring map via `IsClosedImmersion` iff on affines) — may bypass the global
statement entirely.

## [HG-C1] leaf decomposition (banked 2026-07-10; API verified)

Toolkit verified in-tree: `Scheme.Hom.resLE (f) U V (e : V ≤ f⁻¹ᵁ U) : V ⟶ U` +
`MorphismProperty.resLE` (local-at-target stability, Morphisms/Basic:312),
`Scheme.Hom.appLE` (the Γ-side), `⁻¹ᵁ`-preimage-opens algebra (Restrict.lean),
`pullbackSpecIso R S T : pullback (Spec.map _) (Spec.map _) ≅ Spec (S ⊗[R] T)`
(Pullbacks.lean:719), `Scheme.ΓSpecIso`.

- **[C1a] stability predicate**: `IsStableOpen G (U : E.E.Opens) : Prop :=
  G.actionProj.left ⁻¹ᵁ U ≤ G.translationAction.left ⁻¹ᵁ U` ("x ∈ U ⟹ x+t ∈ U").
  Restricted action := `(G.translationAction.left).resLE U (G.actionProj.left ⁻¹ᵁ U) h`
  : (pr⁻¹U) ⟶ U; restricted projection similarly (with `le_refl`).
- **[C1b] the chart Künneth**: for U affine over affine base-patch, identify the OPEN
  `pr⁻¹U ⊆ G ×ₛ E` with the pullback-scheme `G ×ₛ U` (pullback of the open immersion
  `U.ι` — `IsOpenImmersion`-pullback lemmas / `pullbackRestrictIsoRestrict`), then
  `Γ(G ×ₛ U) ≅ B ⊗[R] A` via `pullbackSpecIso` + `ΓSpecIso` (after `Spec`-writing U, G,
  base). Output: `ρ_U : B →ₐ[R] B ⊗[R] A` := ΓSpecIso ∘ (restricted-act).appLE ∘ iso.
- **[C1c] IsCoaction ρ_U**: counit from the group-object unit-law restricted (the
  section 0 ×ₛ U ⟶ pr⁻¹U composed with act| = inclusion), coassoc from μ-associativity
  restricted; both contravariant appLE-functoriality chases (mechanical but fiddly;
  budget a session).
- **[C1d]**: assemble `StableAffineChartData R A B` with C2's chart-Γ-surjectivity
  (actPair| closed immersion of affines ⟹ appTop surjective).

[HG-C2]-mile addendum-2 (third attempt, 90% skeleton): the CORRECT pasting is
`IsPullback.of_bot` with s := of_hasPullback G.π E.π (transported along
tensorHom_left_snd), p := (Over.tensorHom_left_fst E.π E.π G.ιOver (𝟙 E.asOver)).symm,
t := of_hasPullback E.π E.π; conclusion-square IsPullback fstG (ι⊗𝟙).left G.ι fstE; then
`MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) sq
G.closedImmersion` (NOTE: IsClosedImmersion G.ι is the STRUCTURE FIELD
`G.closedImmersion`, not an instance!). KEY DISCOVERY: `Over.tensorHom_left_fst/snd`
(Monoidal/Cartesian/Over.lean:178+) are THE ready component lemmas
(`(f⊗ₘg).left ≫ pullback.snd fS fU = pullback.snd R.hom T.hom ≫ g.left`), and
`pullback.lift_fst/snd` are NOT simp-tagged in current mathlib. Blocker at park-time:
neither rw nor simp-only match tensorHom_left_snd against the of_bot-s-goal (suspect
`E.asOver`-abbrev vs `Over.mk E.π` unification inside the ⊗ₘ-implicits, or the
attributed-local `Over.cartesianMonoidalCategory` instance-path). FRESH-SESSION MOVE:
pp.explicit-diff the goal's ⊗ₘ-implicits against the lemma's via lean_goal, then align
by `show`-restatement. WIP file parked at scratchpad/ActPairImmersion-wip.lean (session
50a95a14); the committed file has shearAuto + actPair_eq_shear green.

## [HG-C1b] leg-3 design (banked 2026-07-10; legs 1-2 COMMITTED)

Status: `chartPullbackIso G U : (pr⁻¹U).toScheme ≅ pullback G.π (U.ι ≫ E.π)` proven
(StableCharts.lean) — the scheme-level Künneth. Leg 3 = the affine patch datum:

```
structure AffineChartPatch (G : FiniteLocallyFreeSubgroup E) where
  V : S.Opens;  hV : IsAffineOpen V          -- affine base patch
  U : E.E.Opens; hU : IsAffineOpen U         -- stable affine chart
  hstable : G.IsStableOpen U
  hover : U ≤ E.π ⁻¹ᵁ V                      -- chart lies over the patch
```
Derived: `R := Γ(V)`, `B := Γ(U)`; `G|_V := (G.π)⁻¹ᵁ V`-open of `G.G` is affine
(G.π = ι ≫ E.π is finite ⟹ IsAffineHom ⟹ affine-preimage-of-affine), `A := Γ(G|_V)`
with the Hopf structure from p2's layer when landed (hypothesis-wired meanwhile: state
the C1c/C1d outputs against `[HopfAlgebra R A]`-instances given as arguments/fields).
Then: `Γ(pullback G.π (U.ι≫E.π))`-restricted-to-the-V-patch ≅ `B ⊗[R] A` via
`pullbackSpecIso R A B` after `Spec`-writing (`IsAffineOpen.isoSpec`, arrows via
`Spec.map`-functoriality); `ρ_U := (ΓSpecIso _).hom ∘ (chartPullbackIso ≫ Spec-iso).inv-Γ
∘ (restrictedAction hstable).appTop`-chain. CAUTION (from C2-mile experience): fix ONE
spelling per object; prefer direct term-application of the mathlib iso-component lemmas
over rw/simp keying; keep every pullback in the `G.π`/`E.π`-spelling.
C1c then proves `IsCoaction ρ_U` by appTop-functoriality chases against the restricted
group-object diagrams (associativity from `MonObj.mul_assoc` of `E.asOver` restricted;
counit from the unit-law composed with the zero-section-through-U... NOTE: the counit
chase needs `0 ∈ U`?? NO — the counit of the HOPF algebra A is the identity-section of
G (0 ∈ G always: the group-object unit factors through G|_V for V-patches since G is an
S-GROUP: η : S → G restricted to V lands in G|_V ✓) — the counit-diagram restricts fine
on ANY stable U (the identity-translation is trivial); coassoc similarly needs the
μ_G-restriction (G|_V is a V-group: p0's Subgroup-structure carries the group-object
data — check field names at C1c-time).

[HG-C1b] leg-3 second-half subtlety (banked): `pullback G.π (P.U.ι ≫ E.π)` is the
S-LEVEL fibre product; to Spec-write it, first restrict the base: since both legs factor
through the OPEN V ⊆ S (U over V by `hover`; use G|_V := π⁻¹V-restriction on the G-leg
too — the U-leg factoring makes the G|_V-part carry the whole product), identify with
the V-level product `pullback (G|_V → V) (U → V)` — the categorical fact "pullback over
S of maps factoring through a mono/open V→S = pullback over V" (grep candidates:
`pullbackRestrictIsoRestrict` applied twice, `IsPullback` + mono-cancellation, or
`pullback.congrHom`-family; possibly cleanest via `IsOpenImmersion`-pullback pasting:
pullback_{S}(X,Y) with X,Y→V: the map to V×_S V = V (open immersion mono ⟹ diagonal iso)
...). THEN all three (V, U-over-V, G|_V-over-V) are affine ⟹ `IsAffineOpen.isoSpec`-write
+ `pullbackSpecIso` ⟹ Γ ≅ B ⊗[R] A. Watch the one-spelling rule throughout.

[HG-C1b] leg-3 second-half FULL CHAIN (banked; names verified):
`pullback G.π (P.U.ι ≫ E.π)`
  ≅ [`(pullbackLeftPullbackSndIso G.π V.ι (U→V)).symm` after aligning
     `(U→V) ≫ V.ι = U.ι ≫ E.π` where U→V := `E.π.resLE V U hover`-composite-with-ι-forms
     (`resLE`-ι-compat lemma; or define U→V as `U.ι ≫ E.π`-corestriction)]
`pullback (pullback.snd G.π V.ι) (U→V)`
  ≅ [transport the FIRST leg along `pullbackRestrictIsoRestrict G.π V`
     (pullback G.π V.ι ≅ (G.π⁻¹ᵁV).toScheme = groupOpen-scheme, snd ↦ G.π-restriction);
     use `pullback.congrHom`/`Iso`-of-legs-lemmas or `IsPullback.of_iso`]
`pullback (groupOpen-scheme → V) (U→V)`   -- all V-level, all three affine
  ≅ [`hV.isoSpec`, `hU.isoSpec`, groupOpen-affine (`IsFinite G.π` ⟹ `IsAffineHom` ⟹
     `IsAffineOpen (G.π⁻¹ᵁV)` from hV) + `Spec.map`-writing + `pullbackSpecIso`]
`Spec (chartRing ⊗[baseRing] groupRing)`; then `ΓSpecIso` ⟹
`kunnethIso : Γ(pullback G.π (U.ι≫E.π), ⊤) ≅ (B ⊗[R] A : CommRingCat)`.
ρ_U := `coactionToPullback ≫ kunnethIso.hom` — then C1c.
Also needed: `Mono V.ι` (open immersion ⟹ mono ✓ OpenImmersion.lean:537) and the
`pullbackIsPullbackOfCompMono`-family (Pullback/Mono.lean:150+) as alternates.

## [HG-C1c] design (banked 2026-07-10, post-v10.106)

**AlgHom-upgrade** of `coactionRing`: the R-linearity square. Obligation:
`coactionRing ∘ (E.π.appLE V U hover) = (algebraMap R (A⊗[R]B))-as-CommRingCat`.
Decompose along the chain: (i) `restrictedAction` is a V-morphism:
`restrictedAction hstable ≫ chartToBase = (pr⁻¹U-to-V)` — from `Over.w
translationAction` restricted (`resLE_comp_resLE`, Restrict.lean:783); (ii) each Künneth
iso is V-compatible (they're built from V-level pullback data — the projections to V
commute by `pullback.condition`/`lift`-computations); (iii) `pullbackSpecIso`-side: the
algebraMap into A⊗B = includeLeft∘(algebraMap R A)-or-right — mathlib
`pullbackSpecIso_inv_fst/snd` + `Spec.map`-functoriality give the base-compat. Assemble
as: appTop-of-(everything over V) ⟹ the square. ALTERNATIVE cheaper route: define the
ALGHOM directly as the appLE-composite in the category of V-SCHEMES?? — or: prove
R-linearity ELEMENTWISE via the section-language (`Scheme.Hom.appLE_map`-naturality) —
choose at write-time; the chain-over-V route is canonical.

**IsCoaction**: counit — the identity-section `e : S → G` restricts to `V → G|_V`
(group-over-S structure field; find its name in Subgroup.lean); `(id ⊗ ε)∘ρ = id`
Γ-dualizes `act ∘ (e ×ₛ id_U) = id_U` (the action-unit law — from `MonObj.one_mul` of
`E.asOver` + `ιOver`-compat: translation by 0 is the identity — p0 may already have
`translationAction`-unit-lemmas; grep). coassoc — Γ-dual of
`act∘(μ ×ₛ id) = act∘(id ×ₛ act)` (action-associativity from `MonObj.mul_assoc` +
`ιOver`-multiplicativity `G.ιOver`-hom-of-groups — the Subgroup-structure's
homomorphism field). Both need the Künneth-chain NATURALITY (the iso commutes with the
G-side maps) — the heaviest chases; budget a full session; consider proving the two
laws first at the SCHEME level (composites of restricted actions) and dualizing ONCE.

## [HG-C1c-ii] R-linearity square decomposition (banked 2026-07-11)

Obligation: `(E.π.appLE V U hover) ≫ coactionRing = ofHom (algebraMap R (A⊗[R]B))` in
CommRingCat. Strategy: dualize the PROVEN scheme square `restrictedAction ≫ chartToBase
= prOpenToBase` and conjugate by the chain-isos. Needs exactly ONE new naturality:
**`chartSpecIso`-base-compat**: `chartSpecIso.hom ≫ Spec.map (ofHom (algebraMap R (A⊗B)))
= (pullback-to-S-structure)-composite-with V.toSpecΓ` — prove by chaining the six
constituent isos' second-projection/base compat lemmas:
`pullbackRestrictIsoRestrict_inv_fst`/`hom_ι`, `pullbackLeftPullbackSndIso_hom_snd`-family,
`pullback.congrHom`-components, `pullback.map`-lift computations (use `pullback.lift_snd`
explicitly — NOT simp-tagged), `pullbackSpecIso_inv_fst` (+ its snd-analog; base-compat =
fst-leg ≫ Spec (R→A)). U-side compat is mathlib (`toSpecΓ_SpecMap_appLE`). Then
R-linearity = paste (scheme-square-appTop) with the two compats. Fallback if the chase
swamps: prove R-linearity ELEMENTWISE on sections via `Scheme.Hom.appLE_map`-naturality
(the composite of the ring maps applied to `algebraMap r` traced through the topIso's).

## [HG-C1c-ii] over-lemma execution skeleton (banked 2026-07-11)

TARGET: `chartCoactionSpec ≫ P.chartToBase ≫ P.V.toSpecΓ
  = Spec.map (CommRingCat.ofHom (algebraMap ↑P.baseRing (↑P.groupRing ⊗ ↑P.chartRing)))`.
Three bounded pieces:
- **(L2)** `(G.chartPullbackIso P.U).inv ≫ P.prOpenToBase
    = pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.chartToBase` — chase the two constituent isos:
  `restrictedDomainIso.inv` = `(pullbackRestrictIsoRestrict actionProj.left U).hom`
  (symm-inv!) with its `hom_ι`-compat; the pasting `pullbackLeftPullbackSndIso`
  `hom/inv_snd`-lemmas. NOTE prOpenToBase-def is resLE of the ⊗-obj-hom; relate via
  `resLE`-uniqueness (`resLE`-maps agree iff compose-with-ι agree: cancel_mono U-side —
  or `Scheme.Hom.resLE`-ext-lemma; alternatively prove both sides ≫ V.ι equal and use
  `cancel_mono P.V.ι` — V.ι is a mono (open immersion) ✓ CLEANEST: all these maps-to-V
  compare after ≫V.ι into S where everything is pullback.condition-algebra).
- **(L3-hom)** `pullback.snd G.π (P.U.ι ≫ E.π) ≫ P.chartToBase ≫ P.V.toSpecΓ
    = P.chartSpecIso.hom ≫ Spec.map (ofHom (algebraMap ...))` — chase hom-ward through
  chartSpecIso = (congrHom.symm ≪≫ pasting.symm) ≪≫ (pullback.map-asIso) ≪≫
  (kunnethToSpec ≪≫ pullbackSpecIso): snd-compats: congrHom-snd (simp),
  pasting-inv-snd (`pullbackLeftPullbackSndIso_inv_snd`?), map≫snd = snd≫U.toSpecΓ
  (lift_snd explicit), pullbackSpecIso-base: `pullbackSpecIso_inv_snd` gives
  inv≫snd = Spec.map(ofHom includeRight); base-compat: algebraMap R (A⊗B) =
  includeRight ∘ (algebraMap R B)?? — canonical: algebraMap R (A⊗B) r = 1⊗(algMap r) =
  includeRight(algMap-B r) ✓ `Algebra.TensorProduct.algebraMap_def`-forms; combine with
  `toSpecΓ_SpecMap_appLE` on the U-side (cTB-leg).
- **Assembly**: substitute `restrictedAction_comp_chartToBase`, then (L2), then (L3-hom),
  close with `Iso.inv_hom_id_assoc`. THEN: R-linearity of `coactionRing` via
  `coactionRing_eq_appTop` + appTop-of-the-over-lemma + topIso/ΓSpecIso-bookkeeping
  (`Scheme.ΓSpecIso_naturality`-family); package `coactionAlg : B →ₐ[R] A⊗[R]B`; the
  comm-swap `Algebra.TensorProduct.comm` to `B ⊗[R] A`; then C1c-counit/coassoc
  (scheme-level-first per previous bank), C1d assembly, C3, C4 → pins → BOARD-SIGNAL.

## [HG-C1c-0] NEW LEAF: the group-scheme structure on G (banked 2026-07-10)

DISCOVERY at C1c-start: p0's `FiniteLocallyFreeSubgroup` carries NO μ_G / unit / inverse
as data — only the functor-of-points `subgroup` field (`∀ g, ∃ H : AddSubgroup (E.Point g),
∀ P, P ∈ H ↔ ∃ h : T ⟶ G, h ≫ ι = P.1`) and `pointSubgroup` (carrier = the factoring set,
`mem` is Iff.rfl). p2's Hopf layer (`DeligneOrder.subgroupHopfAlgebra`) is AFFINE-BASE-only
(`E : EllipticCurve (Spec R)`) and RelEffCartierDiv-indexed — not directly our A.
Both the counit and coassoc chases need the STRUCTURE MAPS. They are derivable, uniquely,
by ι-mono cancellation:

- `mulHom : G ×ₛ G ⟶ G` — apply `pointSubgroup.add_mem` to the two universal points
  `pr₁ ≫ ι`, `pr₂ ≫ ι` of `T := (Over.mk G.π ⊗ Over.mk G.π).left` over S; `Classical.choose`
  the factoring h. Spec: `mulHom ≫ ι = ((pr₁ ≫ ιOver) * (pr₂ ≫ ιOver)).left` (hom-group).
- `unitHom : S ⟶ G` — `zero_mem'` at `g := 𝟙 S`; spec `unitHom ≫ ι = E.zero`.
- `invHom : G ⟶ G` — `neg_mem'` at the universal point `ι` of `g := G.π`; spec
  `invHom ≫ ι = (-(id-point)).1 = ι ≫ E.negHom`(-ish).
- Over-S-ness: each spec-composite is over S, so `homMk` lifts them into `Over S`.
- LAWS (assoc, unit, inv, comm) — all by `cancel_mono G.ι` + the corresponding law in
  `E.Point`'s AddCommGroup (transported hom-group). Uniqueness of each structure map:
  same cancellation. ⟹ `G` is a commutative group object in `Over S`, and `ιOver` is a
  group-object hom.

CONSUMERS: (a) the translation-action unit/assoc diagrams — hence C1c's counit/coassoc
after Γ-dualization; (b) any future Hopf structure on `groupRing` (comul := Γ(mulHom)
through the affine Künneth over the patch, counit := Γ(unitHom), antipode := Γ(invHom)) —
this is our OWN route to `[HopfAlgebra R A]`, avoiding the p2-affine-base restriction, and
it is NEW-file work (p0/p2 files untouched). File: `GroupScheme/SubgroupGroupObject.lean`.

## [HG-C1c-1] NEW LEAF: the Hopf algebra on `groupRing` (banked 2026-07-10)

`IsCoaction ρ` needs `[Bialgebra R A]` — so before the two axioms can even be STATED for
`chartCoaction`, `A = groupRing` must carry comul/counit (and, for M5, antipode). With
[HG-C1c-0] done (`mulOver`/`unitOver`/`invOver` + laws) these are the Γ-duals:
- `counit ε : A → R` := `unitHom.appLE groupOpen V _` (note `unitHom ≫ π = 𝟙 S`, so
  `V ≤ unitHom ⁻¹ᵁ groupOpen` — the `le` is `le_of_eq` on preimages);
- `comul Δ : A → A ⊗[R] A` := Γ(mulHom restricted) through the affine Künneth for the
  square `G|_V ×_V G|_V`;
- `antipode S : A → A` := `invHom.appLE groupOpen groupOpen _`.
The coalgebra/bialgebra/Hopf axioms are then the Γ-duals of C1c-0's laws — each one
`Spec`-side first (as with `chartCoactionSpec_over`), dualized once.

**PREREQUISITE (this increment)**: generalize the chart Künneth. `StableCharts`'
`kunnethToSpec`/`kunnethSpecIso` are already generic in shape but tied to
`(G.π, E.π, groupOpen, U)`. Extract into `GroupScheme/PatchKunneth.lean`:

  `affinePatchKunneth (hV : IsAffineOpen V) (f : X ⟶ S) (g : Y ⟶ S)
     (W₁ : X.Opens) (hW₁ : IsAffineOpen W₁) (e₁ : W₁ ≤ f ⁻¹ᵁ V)
     (W₂ : Y.Opens) (hW₂ : IsAffineOpen W₂) (e₂ : W₂ ≤ g ⁻¹ᵁ V) :
     pullback (f.resLE V W₁ e₁) (g.resLE V W₂ e₂)
       ≅ Spec (.of (Γ(X,W₁) ⊗[Γ(S,V)] Γ(Y,W₂)))`

(the algebra structures being the `appLE` maps — the rfl-alignment that made C1b's legs
match `pullbackSpecIso` for free). Instantiations: chart case `(G.π, E.π, groupOpen, U)`
recovers `kunnethSpecIso`; Hopf case `(G.π, G.π, groupOpen, groupOpen)` gives the target
of `comul`. Same `toSpecΓ`-iso + `toSpecΓ_SpecMap_appLE` proof as C1b's leg 4a.

## [HG-C1c-1] Hopf-axiom leaf: measured decomposition (banked 2026-07-11)

Transport tools now ALL in place (PatchKunneth.lean, generic + axiom-clean):
`patchKunneth`, `patchKunneth_hom_comp_includeLeft/Right`, `patchKunneth_hom_base`,
`IsAffineOpen.isIso_toSpecΓ`; plus `appLE_id`, `appLE_congr_hom` (PatchHopf).

Landed: ε and S are R-linear (Γ-duals of `unitHom_π`, `invHom_π`, one `appLE_comp_appLE`
each). Remaining, in cost order:
- **(1b) Δ R-linear** — same shape as `appLE_comp_coactionRing`: Spec-side via
  `patchKunneth_hom_base` + `squareMul ≫ π = fst ≫ resLE ≫ V.ι` (proven inside
  `top_le_preimage_groupOpen_squareMul`; EXTRACT it as a named lemma first), then the
  Γ-transfer (appTop + topIso/ΓSpecIso bookkeeping). ~1 measured route.
- **(1c) counit laws** (2) — Γ-duals of `unitOver_mulOver_left` (+ a right unit law: PROVE
  `unitOver_mulOver_right` first, or derive from `mulOver`-commutativity, which itself is
  a one-liner by ι-cancellation + `_root_.mul_comm` in the hom-group).
- **(1d) coassoc** — Γ-dual of `mulOver_assoc`. NEEDS a triple Künneth
  `Spec (A ⊗ A ⊗ A) ≅ G|_V ×_V G|_V ×_V G|_V` and its three leg lemmas. Biggest piece;
  budget its own route. Design: iterate `patchKunneth` (the square is affine — its
  `IsAffineOpen`-ness is `pullback`-of-affines, i.e. `Spec` via the iso itself), then
  `Algebra.TensorProduct.assoc` alignment.
- **(1e) antipode axioms** — Γ-duals of `invOver_mulOver_left` (+ right). Needs the
  ring-multiplication ↔ Spec-diagonal dictionary (`diagonal_SpecMap`, Pullbacks.lean:797)
  since `mul_antipode_rTensor_comul` involves `Algebra.TensorProduct.lmul'`.

STOP-LINE POLICY for this leaf: 3–4 measured iterations per sub-route, then ledger the
state and move to the next sub-route (do NOT grind 1d/1e ahead of 1b/1c). If 1d or 1e
prove multi-session, the honest fallback is to HYPOTHESIS-WIRE `[HopfAlgebra R A]` into
C1d/C4 (the charter's soft-edge provision, as originally planned for p2's layer) and
discharge the pins against it — the geometry (C2/C3/C4) does not depend on the Hopf
axioms' proofs, only on their existence.

## [HG-C1c-1d] coassoc: architectural finding (banked 2026-07-11)

Building `affineKunneth` (⊤-level, `Γ(B,⊤)`-algebras = `appTop`) revealed the right shape:
its legs and Γ-duals are **strictly simpler** than the opens-level ones (no `topIso`
conjugation anywhere). For coassoc we need a TRIPLE identification
`Γ(G|_V ×_V (G|_V ×_V G|_V), ⊤) ≅ A ⊗[R] (A ⊗[R] A)`, obtained by ITERATING
`affineKunneth` with `Y := groupSquare` (affine, via `IsAffine.of_isIso` on
`patchKunneth`). But iterating at the *opens* level would force a base-ring iso
`Γ(S,V) ≅ Γ(V.toScheme,⊤)` inside the tensor product — mathlib's
`Algebra.TensorProduct.congr` only handles a FIXED base ring, so that route needs
`mapOfCompatible`-style plumbing.

**DECISION** (banked; execute next): restate the patch Hopf structure at the ⊤-level:
`R' := Γ(V.toScheme, ⊤)`, `A' := Γ(G|_V.toScheme, ⊤)`, with
- `ε' := unitSection.appTop`,
- `Δ' := squareMulRes.appTop ≫ affineKunnethΓ groupToBase groupToBase _ _`,
- `S' := invSection.appTop`,
where `squareMulRes : groupSquare ⟶ groupOpen.toScheme` is the corestriction of
`squareMul` (exists: `top_le_preimage_groupOpen_squareMul` + `Scheme.topIso`).
Every law already proven at scheme level (`unitSection_comp_groupToBase`,
`left/rightUnitSection_comp_squareMul`, and, for coassoc, the restriction of
`mulOver_assoc`) dualises with the SAME two-step pattern, now with no topIso terms.
The old opens-level maps are recovered by conjugating with `topIso` (`ε = topIso.hom ≫ ε'
≫ topIso.inv`-style) — record those as bridge lemmas so `chartCoaction`/M5 keep consuming
`A = Γ(G, groupOpen)`.

Cost estimate: ~1 session for the ⊤-level restatement + coassoc; the counit/antipode laws
transfer mechanically (their scheme identities are already proven and are stated purely in
terms of `unitSection`, `leftUnitSection`, `squareMul`).
