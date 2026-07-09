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
