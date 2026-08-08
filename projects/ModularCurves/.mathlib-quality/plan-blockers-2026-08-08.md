# Plan: the four live blockers (2026-08-08)

Produced by `/develop` (resume mode) against HEAD `d04680926`. Scope: the sorries that gate
the DS4 Weil-pairing line.

## The blockers, and what actually gates what

```
AP-D4/D5-existence/D6/D7   (Weil pairing construction)
      ↑
exists_invertible_tensor_idealModule_add        Picard/SelfAdjointN.lean:267   [BLOCKER 3]
      ↑  (route: prove on the universal pair, reduced base, then base-change down)
exists_pullback_iso_of_fibrewise_trivial_of_isReduced   ForMathlib/Seesaw.lean:245 (assembled)
      ↑                                    ↑
 KM-SEESAW-1′ :159  [BLOCKER 1]      KM-SEESAW-2″ :235  [BLOCKER 2]
 (residue kernel rank one)           (reduced descent)
                                            ↑
                              **NEW API GAP — not in mathlib** (§B2.1)

AP2-B2 / AP2-B3   ← IsIso (subschemeι ≫ π)     EllipticCurve/AbelEquivalence.lean:971 [BLOCKER 4]
   (independent line — does NOT gate AP-D)
```

Blockers 1–3 are one chain; blocker 4 is independent.

---

## BLOCKER 1 — `orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial` (Seesaw.lean:159)

### Statement now (after the 2026-08-08 repair, commit `59c1f0155`)

```lean
theorem orderedBaseCech_residueField_kernel_finrank_of_fibre_trivial
    {X S : Scheme.{u}} [IsAffine S] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (s : S)
    (hfib : ∀ {k : Type u} [Field k] (x : Spec (.of k) ⟶ S),
      Nonempty ((Scheme.Modules.pullback (pullback.fst π x)).obj M ≅ unitObj (pullback π x))) :
    letI : Algebra Γ(S, ⊤) ↥(S.residueField s) :=
      ((S.fromSpecResidueField s).appTop ≫ (Scheme.ΓSpecIso (S.residueField s)).hom).hom.toAlgebra
    Module.finrank ↥(S.residueField s)
      (LinearMap.ker (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange ↥(S.residueField s))) = 1
```

### Diagnosis of the failed attempt

The five-step route in the docstring is correct, but the skeleton failed with
`failed to synthesize instance` because the two engines speak different rings:

* `orderedBaseCechComplexBaseChangeIso` (`ForMathlib/AffineModuleCechBaseChange.lean:1037`)
  produces `ModuleCat.extendScalars t.appTop.hom` — scalars in `Γ(Spec κ(s), ⊤)`;
* the goal's `LinearMap.baseChange` is over `↥(S.residueField s)` — scalars in `κ(s)`.

They differ by exactly the ring iso `Scheme.ΓSpecIso (S.residueField s)`, which is *already*
the bridge baked into the statement's `letI`.

### Fix: prove the scheme-side statement first, transport once at the end

Three new declarations, in `ForMathlib/Seesaw.lean` above the current theorem.

**S1.1 — `finrank_eq_one_of_bijective_algebraMap`** (pure algebra, ~8 LOC)

```lean
theorem Module.finrank_eq_one_of_bijective_algebraMap
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] [Nontrivial R]
    (h : Function.Bijective (algebraMap R A)) : Module.finrank R A = 1
```

Proof: `Algebra.linearMap R A : R →ₗ[R] A` is bijective by `h`; `LinearEquiv.ofBijective`
then `LinearEquiv.finrank_eq` and `Module.finrank_self`.
(NOTE — `.mathlib-quality` memory "Lean elaboration stall patterns": `ofBijective _` with an
underscore stalls; give the map explicitly.)

**S1.2 — `orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial`** (the real content)

Scheme-side, over `Γ(T, ⊤)`, no residue field anywhere, and **no field hypothesis at all**:

```lean
theorem orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial
    {X S T : Scheme.{u}} [IsAffine S] [IsAffine T] [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ S} [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    (hπ : UniversallyOConnected π)
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (t : T ⟶ S) [Nontrivial Γ(T, ⊤)]
    (hfibt : Nonempty ((Scheme.Modules.pullback (pullback.fst π t)).obj M ≅
      unitObj (pullback π t))) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := t.appTop.hom.toAlgebra
    Module.finrank Γ(T, ⊤)
      (LinearMap.ker (((orderedBaseCechComplex π M U).d 0 1).hom.baseChange Γ(T, ⊤))) = 1
```

Proof — a chain of five linear equivalences, each already in the tree:

1. `HomologicalComplex.baseChangeKernelZeroLinearEquiv C Γ(T,⊤)`
   (`ForMathlib/LowDegreeFiniteProjectiveReplacement.lean:164`).
   With `letI := t.appTop.hom.toAlgebra`, `algebraMap Γ(S,⊤) Γ(T,⊤)` is `t.appTop.hom` by
   `rfl`, so the `ModuleCat.extendScalars` arguments now match **syntactically** — this is the
   step that failed before.
2. `HomologicalComplex.kernelZeroLinearEquivOfHom` fed with
   `(orderedBaseCechComplexBaseChangeIso π t M U hUaff).hom / .inv`
   (`AffineModuleCechBaseChange.lean:1037`; instances `[IsAffine S] [IsAffine T]
   [X.IsSeparated] [M.IsQuasicoherent]`, the last from `hM.isQuasicoherent`). Model:
   `baseCechKernelOrderedBaseChangeLinearEquiv` (`SchemeModuleOrderedBaseCechZero.lean:161`)
   uses `kernelZeroLinearEquivOfHom` in exactly this shape.
3. `(baseSectionsIsoKernelOrderedBaseCechDifferential (pullback.snd π t) M_t U_t hU_t).symm`
   (`SchemeModuleOrderedBaseCechZero.lean:256`), where `U_t i = pullback.fst π t ⁻¹ᵁ U i` and
   `hU_t := (pullback.fst π t).iSup_preimage_eq_top hU`.
4. `baseSectionsMapIso (pullback.snd π t) hfibt.some`
   (`SchemeModuleBaseCechZero.lean:119`) — replaces `M_t` by `unitObj (pullback π t)`.
5. `baseSectionsIsoRestrictScalarsTop` (`SchemeModuleBaseCechZero.lean:191`) turns
   `baseSections (pullback.snd π t) (unitObj _)` into
   `restrictScalars (pullback.snd π t).appTop.hom Γ(X_T, ⊤)`; and
   `hπ t ⊤ : IsIso ((pullback.snd π t).app ⊤)` — this *is* the definition of
   `UniversallyOConnected π` (`EllipticCurve/Rigidity.lean:54`) — says that scalar map is
   bijective. Close with **S1.1**.

`Module.finrank` is transported along the composite by `LinearEquiv.finrank_eq`.

Size estimate: Stacks 0EX7 spends no lines on this (it is "H⁰ of the fibre is κ(s)"); the LOC
is entirely the five transports, each ~10–20 lines by the `baseCechKernelOrdered…` model.
Estimate **90–140 LOC**.

**S1.3 — the residue-field corollary** (the current sorry)

Instantiate S1.2 at `T = Spec (S.residueField s)`, `t = S.fromSpecResidueField s`, then
transport `finrank` along the ring iso `Scheme.ΓSpecIso (S.residueField s)`. Needs one small
lemma: `finrank` is invariant under a compatible ring iso on the scalars,

```lean
theorem Module.finrank_eq_of_ringEquiv_of_compatible
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃+* B) (he : ∀ r, e (algebraMap R A r) = algebraMap R B r)
    (N : Type*) [AddCommGroup N] [Module A N] [Module B N] … 
```

— or, cheaper and preferred, avoid it: `LinearMap.baseChange` over `Γ(T,⊤)` versus over
`κ(s)` are related by `moduleCatExtendScalarsIsoRestrictScalarsOfRingEquiv`
(`LowDegreeFiniteProjectiveReplacement.lean:56`), which already exists for exactly this
purpose. **Check this first — if it applies, S1.3 is ~15 LOC.**

### A simplification worth taking (flagged for review)

With S1.2 in hand, `orderedBaseCech_kernel_finrank_of_fibre_trivial` (:168, currently proved
from S1.3 via a residue-field detour) can be proved **directly** at `T = Spec (.of K)` for the
arbitrary field `K`, deleting the use of `LinearMap.finrank_ker_baseChange_eq`,
`Scheme.SpecToEquivOfField` and `affineFieldFactor_residue_isScalarTower`. The only thing to
check is that `(Scheme.ΓSpecIso (.of K)).hom ∘ t.appTop = algebraMap Γ(S,⊤) K` for
`t = Spec.map (ofHom (algebraMap _ K)) ≫ S.isoSpec.inv`. **Do not delete the residue-field
form** — Blocker 2 needs it per prime.

---

## BLOCKER 2 — `exists_pullback_iso_of_kernel_finrank_of_fibre_trivial` (Seesaw.lean:235)

This is the substantive one. Statement: over a **reduced** affine base, constant residue-kernel
rank 1 + fibrewise triviality ⟹ `∃ N, IsInvertible N ∧ M ≅ π^* N`.

### Two halves

**Half A (descent — ALREADY PROVED, needs re-shaping).**
`ModularCurves.exists_pullback_twist_of_locally` (`WeilPairing/RelPicLocal.lean:1157`,
AP2-B1, zero sorries) says: if `M, M'` invertible on `X ×_S T` and Zariski-locally **on the
base** `M ≅ M' ⊗ pr^*(N i)`, then globally `M ≅ M' ⊗ pr^* N₀` with
`N₀ = pr_*(M ⊗ M'^∨)` invertible. Taking `M' = unitObj` this is precisely Blocker 2's
conclusion. So **Blocker 2 reduces to: Zariski-locally on the base, `M` is trivial.**

Caveat: `exists_pullback_twist_of_locally` is stated for the base-changed shape
`pullback.snd p g`, while Seesaw has a bare `π : X ⟶ S`. Two options —
 (i) instantiate `p := π`, `g := 𝟙 S` and transport along `pullback π (𝟙 S) ≅ X`; or
 (ii) generalise the RelPicLocal chain from `pullback.snd p g` to an arbitrary
 `f : Y ⟶ T` with `UniversallyOConnected f` (mechanical, touches ~8 declarations).
**Recommend (ii)** — the consumer `exists_invertible_tensor_idealModule_add` lives on
`pullback E.π t`, so a general `f` serves both without further transport.

**Half B (the new mathematics).** Locally on the base, `M` is trivial. Decomposes as:

* **B.1 — the API gap (below): `ker d⁰` is finite projective of rank 1**, i.e. `π_*M` is
  invertible.
* **B.2 — the counit is an isomorphism.** With `π_*M` invertible, a local basis `ℓ` of
  `Γ(X_V, M)` over `V ∋ s` gives `𝒪_{X_V} → M|_{X_V}`, `1 ↦ ℓ`. It is an iso because on every
  fibre over `V` it is a nonzero map `κ(x) → M_x ≅ 𝒪_{X_x}` between line bundles whose fibre
  `h⁰` is 1 — `hfib` is exactly what makes `ℓ` nowhere-vanishing (this is why the docstring's
  b2_log entry records that `hrank` alone is FALSE: `𝒪_E(P)` on a genus-1 curve has `h⁰ = 1`
  but its generator vanishes at `P`). Discharge with
  `Scheme.Modules.isIso_of_bijective_app_on_cover` / the `GlueTrivialization.lean`
  `globalSectionHom` machinery, plus Nakayama on stalks.

### B2.1 — THE API GAP (verified absent from mathlib, 2026-08-08)

> **Stacks 0FWG.** *Let `R` be a reduced ring and `M` a finite `R`-module such that
> `p ↦ dim_{κ(p)} (M ⊗_R κ(p))` is locally constant. Then `M` is finite locally free.*

Searched and **not found**: `leansearch` ("finitely generated module over reduced ring with
locally constant fibre dimension is projective"), `local_search "rankAtStalk"` (26 hits, none
reduced), `grep IsReduced` in `RingTheory/Spectrum/Prime/FreeLocus.lean`,
`RingTheory/Flat/Rank.lean`, `RingTheory/LocalProperties/Projective.lean` — zero hits in all
three. This is a genuine mathlib gap and it is the *only* new commutative algebra the seesaw
needs.

Proof (short — this is why the gap is worth filling rather than routing around):
fix `p`; pick `x₁ … xₙ ∈ M` lifting a `κ(p)`-basis of `M ⊗ κ(p)`; Nakayama makes
`R_p^n ↠ M_p`; the cokernel is finite with vanishing stalk at `p`, so it vanishes on a basic
open `D(f) ∋ p`. On `D(f)`, let `K = ker(R_f^n → M_f)`. For every prime `q ∈ D(f)`, both sides
have `κ(q)`-dimension `n`, so `κ(q)^n → M ⊗ κ(q)` is bijective, forcing `K_q ⊆ q·R_q^n`, i.e.
every coordinate of every `x ∈ K` lies in `q`. Intersecting over all `q ∈ D(f)` puts those
coordinates in the nilradical, which is `0` since `R` is reduced. Hence `K = 0` and
`M_f ≅ R_f^n` is free.

Estimate **150–250 LOC**. Lands in `ForMathlib/` (new file `ReducedConstantRankFree.lean`),
`/generalise`-able to mathlib later.

### B2.2 — how B.1 uses the gap (this is the delicate point)

`ker d⁰` is **not** the module to apply B2.1 to. What Blocker 1 supplies is
`dim_κ ker(d⁰ ⊗ κ) = 1`, and *without exactness* the comparison
`ker(d⁰) ⊗ κ → ker(d⁰ ⊗ κ)` is not known to be bijective — so `rankAtStalk (ker d⁰)` is not
directly 1. (The AP2-A2 engine `kernel_data_of_hasDegreeOneFibreCohomology`
(`EllipticCurve/DegreeOneFibreCohomology.lean:126`) gets that bijectivity from
`hexact`, i.e. positive-degree exactness — which is **false here**: `H¹(E_s, 𝒪) = κ(s)` on a
genus-1 fibre. The Seesaw module docstring already records that the `hpkg` route is
unusable.) Instead run **Mumford's argument** on the tree's own replacement complex:

1. `LowDegreeFiniteReplacement` (`LowDegreeFiniteProjectiveReplacement.lean`) gives
   `u := kZeroToKOne f : K⁰ →ₗ[R] K¹` with `K¹` finite free, `kZero_projective : Projective R K⁰`
   (:522), and — crucially, **unconditionally** —
   `baseChangeKernelEquiv A : ker (u.baseChange A) ≃ₗ[A] ker (f.baseChange A)` (:799) for
   *every* `R`-algebra `A`. Hypotheses needed: `Module.Finite R (HOne f)` and flatness of the
   two terms, both available (`orderedBaseCechHomologyFinite_of_isProper` and
   `orderedBaseCechObject_flat_of_isInvertible`, used the same way at
   `DegreeOneFibreCohomology.lean:150`).
2. `coker u ⊗ κ(p) = coker(u ⊗ κ(p))` — right-exactness of `⊗`, unconditional. Its dimension is
   `rank K¹ − rank_{κ(p)} K⁰ + dim ker(u ⊗ κ(p)) = n − rank_{κ(p)} K⁰ + 1`, and
   `rank_{κ(p)} K⁰` is locally constant by `Module.isLocallyConstant_rankAtStalk`
   (mathlib, `FreeLocus.lean` — VERIFIED to exist) since `K⁰` is finite projective. So
   **`coker u` has locally constant fibre dimension**.
3. Apply **B2.1** to `coker u`: it is finite locally free.
4. `K⁰ → K¹ → coker u → 0` with `coker u` projective splits, so `im u` is a direct summand of
   `K¹`, hence finite projective; then `0 → ker u → K⁰ → im u → 0` splits, so `ker u` is a
   direct summand of `K⁰` — **finite projective**, and its formation commutes with every base
   change (splittings survive `⊗`). Combined with step 1 at `A = R`,
   `ker d⁰ ≅ ker u` is finite projective with `rankAtStalk = 1`.
5. `Module.Invertible.of_finite_of_projective_of_rankAtStalk_eq_one`
   (`ForMathlib/InvertibleOfRankOne.lean`, proved this week) upgrades that to
   `Module.Invertible R (ker d⁰)`, and
   `baseSectionsIsoKernelOrderedBaseCechDifferential` transports it to `baseSections π M`.

This is exactly the shape of `kernel_data_of_hasDegreeOneFibreCohomology`, with `hexact`
replaced by `IsReduced` + B2.1. **The two engines should end up sharing a common core.**

### B2.3 — SELF-CORRECTION (found while verifying B2.2's citations, 2026-08-08)

Step 1 of B2.2 as first written is **incomplete**. The replacement is applied not to
`d⁰ : C⁰ → C¹` but to its corestriction `f : C⁰ → Z¹ := ker d¹` (it must be: `HOne f` has to
be a *finite* module, and `C¹/im d⁰` is not — only `Z¹/im d⁰ = H¹` is). The actual entry point
is `shortComplexBaseChangeKernelEquiv`
(`LowDegreeFiniteProjectiveReplacement.lean:834`), whose instance hypotheses are

```
[Module.Flat R S.X₁]                     -- C⁰      ✓ (F3)
[Module.Flat R (LinearMap.ker S.g.hom)]  -- Z¹      ← NOT automatic
[Module.Finite R (LinearMap.ker S.f.hom)]-- ker d⁰  ✓ finite_kernel_zero_of_finite_homology
[Module.Finite R S.homology]             -- H¹      ✓ (F3)
```

plus an explicit argument `hbij : Function.Bijective (kerBaseChangeComparison A S.g.hom)` —
i.e. `Z¹ ⊗ A → ker(d¹ ⊗ A)` bijective. In `kernel_data_of_hasDegreeOneFibreCohomology` **both**
come from `hexact`, which is exactly what is unavailable here. Without them,
`ker(u ⊗ A) ≅ ker(f ⊗ A)` does not upgrade to `ker(u ⊗ A) ≅ ker(d⁰ ⊗ A)`.

**Both are supplied by exactness of `C^•` at positions `≥ 2` only** (a much weaker demand than
`hexact`, and true here since the fibres are curves: `H^{≥2}(X_s, M_s) = 0`, while
`H¹(E_s, 𝒪) = κ(s) ≠ 0` is what killed `hexact`). Descending induction from the top of the
bounded complex: `Z^N = C^N` is flat; and `0 → Z^i → C^i → Z^{i+1} → 0` is exact once
`im d^i = Z^{i+1}` (exactness at `i+1`), so `C^i` flat + `Z^{i+1}` flat ⟹ `Z^i` flat, down to
`i = 1`. The same short exact sequences give `ker(d¹ ⊗ A) = Z¹ ⊗ A`.

**Cheapest discharge: take a two-element affine cover.** Then
`orderedBaseCechObject_subsingleton_of_card_le π M U q (hq : 2 ≤ q)` makes `C^q = 0` for
`q ≥ 2`, so `d¹ = 0`, `Z¹ = C¹` is flat by (F3), and `kerBaseChangeComparison A 0` is the
identity — every hypothesis holds with no exactness argument at all. The tree already reasons
with two-affine-cover fibre models (`EllipticCurve/FibreCechPresentation.lean`,
`subsingleton_H_add_two_of_two_affine_open_cover`), so this should be the route; the open
question is whether `IsInvertible.exists_finiteAffineBaseCech_flat`
(`Picard/InvertibleSheafBaseCechFlat.lean:23`) can be strengthened to produce `card ι = 2`
for a relative curve (`E ∖ (ample relative divisor)` affine + an affine neighbourhood of that
divisor), or whether Blocker 2 should simply carry `card ι = 2` as a hypothesis and let the
elliptic-curve consumer supply it.

**Add ticket T4b** (before T5): supply `Flat R Z¹` + cycles base change, via a two-element
cover or via exactness at positions ≥ 2. Est. 60–150 LOC.

---

## BLOCKER 3 — `exists_invertible_tensor_idealModule_add` (SelfAdjointN.lean:267)

Unchanged from the recorded route (module docstring, "The route (revised 2026-07-27)"):
prove the identity on the **universal pair of points** over the reduced base
`B = C ×_U C`, where every residue fibre is trivial by the field theorem
`HasseWeil.Pic0.RouteCTheoremOfSquareDiv.kappaDivisor_add_linEquiv`, apply the seesaw
(Blockers 1+2), pull back along the zero section to kill `N`, and base-change down to an
arbitrary — possibly non-reduced — base.

**Do not start this before Blockers 1–2 land.** The one thing to settle up front is the
docstring's own flag: *"the expected bottleneck is not the seesaw but the comparison between
HasseWeil's projective-divisor linear equivalence and the scheme-theoretic `picClass`,
together with its base-change naturality."*

**Strategic alternative to price before committing.** The docstring's rejected route (A) —
the chart-local exact iso `I(D_Q) ⊗ I(D_{Q'}) ≅ I(D_{Q+Q'}) ⊗ I(D_0)` on `f⁻¹U` from the
line-and-vertical function, glued by `nonempty_unitObj_iso_of_normalized_glue`
(`Picard/RigidDescent.lean:65`, proved) — needs **no seesaw and no B2.1 gap**. It was ranked
below the seesaw route when the seesaw looked cheap. Now that the seesaw carries a 150–250
LOC mathlib gap plus B2.2's replacement-complex argument, route (A)'s cost (complete
projective addition-law charts; degenerate loci `Q = Q'`, `Q = −Q'`, either `= 0` as closed
subschemes) should be re-priced. **This is the main question for external review.**

---

## BLOCKER 4 — `IsIso ((sectionVanishingIdeal M hM σ).subschemeι ≫ π)` (AbelEquivalence.lean:971)

Independent of the AP-D chain; completes AP2-B2/B3 (KM pp. 66–67).

Everything around it is proved: `relEffCartierDiv_of_isIso_subschemeι` (:939),
`degree_eq_one_iff_exists_section` (:897), `exists_relEffCartierDiv_of_section` (:913),
`isInvertible_idealModule_of_section` (:926), `sectionVanishingIdeal_locally_span` (:717).
Note `exists_section_of_degree_one` (:877) already discharges the *same shape* via
`Scheme.Hom.isIso_iff_finrank_eq` — but it may assume `D.finite/flat/lfp`, which is what we
are trying to produce, so that path is circular here.

**Route (recommended — route (b) on the board).** Under `HasDegreeOneFibreCohomology`, AP2-A2
gives `baseSections π M` invertible (`baseSections_invertible_of_hasDegreeOneFibreCohomology`,
`DegreeOneFibreCohomology.lean:224`). Pick the basis `σ`; the counit
`𝒪_E → M`, `1 ↦ σ`, has image ideal `sectionVanishingIdeal M hM σ`, locally principal
generated by a nonzerodivisor (`sectionVanishingIdeal_locally_span` + the nonzerodivisor
ladder at :660–828). Then `Z = V(σ) → Spec R` is finite locally free of rank 1 — rank from
the fibre `h⁰ = 1` in `hpkg` — hence an iso by `Scheme.Hom.isIso_iff_finrank_eq`.

**The one input still missing** is the nonzerodivisor property of the local generator, i.e.
`evalGenerator_mem_nonZeroDivisors` (:836, still `sorry`). The ladder below it
(`mem_nonZeroDivisors_of_forall_maximal_residueField_fibre_injective`, :791, PROVED) reduces
it to a per-maximal-ideal fibre injectivity. **WARNING (recorded 2026-08-07):**
`evaluation_ne_zero_iff_mem_basicOpen` shows the generator *vanishes* on the divisor, so the
naive *total-space* fibrewise hypothesis is FALSE; KM's reduction is over the **base**, and the
base-side criterion `injective_of_lTensor_residueField_injective_sModule`
(`ForMathlib/LocalFlatnessCriterion.lean:448`) **contains a `sorry` (Artin–Rees) and must not
be routed through**. So either (a) prove that criterion, or (b) get flatness of `Z → Spec R`
from the *section* side, where the tree is already sorry-free
(`RelEffCartierDiv.exists_affineOpen_ker_principal_nonZeroDivisor`).

Estimate: **(b) 100–200 LOC** if the section-side reroute closes; **(a) is a separate
Artin–Rees development** and should not be attempted inside this ticket.

---

## Ticket order

| # | Ticket | File | Depends | Est. |
|---|--------|------|---------|------|
| T1 | `finrank_eq_one_of_bijective_algebraMap` | `ForMathlib/Seesaw.lean` | — | 10 |
| T2 | `orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial` | `ForMathlib/Seesaw.lean` | T1 | 90–140 |
| T3 | residue-field corollary = fill Seesaw.lean:159 | `ForMathlib/Seesaw.lean` | T2 | 15–40 |
| CLEANUP-S | `/cleanup` on `ForMathlib/Seesaw.lean` | | T3 | — |
| T4 | **`ReducedConstantRankFree.lean`** (Stacks 0FWG) | new `ForMathlib/` | — (parallel with T1–T3) | 150–250 |
| T5 | replacement-complex assembly: `π_*M` invertible | `ForMathlib/Seesaw.lean` | T3, T4 | 120–200 |
| T6 | counit iso ⟹ base-locally trivial | `ForMathlib/Seesaw.lean` | T5 | 80–150 |
| T7 | generalise RelPicLocal to bare `f : Y ⟶ T` | `WeilPairing/RelPicLocal.lean` | — (parallel) | 60–120 |
| T8 | fill Seesaw.lean:235 from T6 + T7 | `ForMathlib/Seesaw.lean` | T6, T7 | 30–60 |
| CLEANUP-S2 | `/cleanup` on `ForMathlib/Seesaw.lean` | | T8 | — |
| T9 | universal-pair route ⟹ SelfAdjointN.lean:267 | `Picard/SelfAdjointN.lean` | T8 | large |
| T10 | `evalGenerator_mem_nonZeroDivisors` via the section side | `AbelEquivalence.lean` | — (parallel) | 100–200 |
| T11 | fill AbelEquivalence.lean:971 | `AbelEquivalence.lean` | T10 | 40–80 |
| CLEANUP-A | `/cleanup` on `EllipticCurve/AbelEquivalence.lean` | | T11 | — |

T1–T3, T4, T7, T10 are all startable immediately and independent.

## External review (ChatGPT 5.6 Sol, effort max, 2026-08-08) — verdict and amendments

Verdict: *"Blocker 1 is false for arbitrary affine `T`. Blocker 2 has a genuine missing
comparison, but reducedness supplies a short minimal-prime argument that repairs it. After that
repair, B.1 and B.2 work. R1 is still substantially cheaper than complete addition laws. For
Blocker 4, candidate (i) is exactly the local flatness criterion; the real alternative is a
smooth-transversality/Jacobian argument."*

### A1 — Blocker 1: the Lean statement survives; the *prose* claim I sent did not

The reviewer's counterexample: `π = id_S` with `S = Spec R`, `R` Dedekind with nontrivial class
group, `M = N` a nonprincipal invertible ideal. `π` is proper, flat, fp and universally
`O`-connected; every field-valued fibre of `N` is 1-dimensional hence trivial; but for `T = S`,
`Γ(X_T, M_T) = N` is not free. So **"trivial on every field-valued fibre" does NOT give rank one
over `Γ(T,⊤)` for a general affine `T`.**

This does **not** hit `orderedBaseCech_appTop_kernel_finrank_of_fibre_trivial` as stated in
Lean, because its hypothesis is `hfibt : M_T ≅ 𝒪_{X_T}` **for that specific `T`**, not fibrewise
triviality — and in the counterexample `hfibt` fails. The reviewer explicitly allows this case
(*"or when you independently know `M_T ≅ O_{X_T}`"*). **Amendment: none to the statement;
docstring warning added** so nobody later "simplifies" `hfibt` to the fibrewise hypothesis. Both
call sites (residue field `κ(s)`, and the direct `Spec K` route) are field-valued, so `hfibt` is
supplied by `hfib` there.

### A2 — Blocker 2: a REAL gap, independent of my B2.3 self-correction

`dim_{κ(p)} ker(u ⊗ κ(p)) = 1` does **not** follow from (F4) plus
`dim ker(d⁰ ⊗ κ(p)) = 1`. (F4) compares `ker(u_A)` with `ker(f_A)` where `f : C⁰ → Z¹` is the
corestriction, while the fibre `H⁰` is `ker(d⁰_A)`; and `d⁰_A = i_A ∘ f_A` with
`i : Z¹ ↪ C¹` **not** injective after non-flat base change.

Reviewer's counterexample (Koszul on `R = k[x,y]`):
`R --(r ↦ (−yr, xr))--> R² --((a,b) ↦ xa+yb)--> R`. Here `Z¹ = R·(−y,x) ≅ R`, `f` is an
isomorphism and `H¹ = 0`; but at `p = (x,y)`, `d⁰ ⊗ κ(p) = 0` so `ker(d⁰ ⊗ κ(p)) = κ(p)`, while
`ker(f ⊗ κ(p)) = 0`. So `F_p ⊊ H_p` really happens.

**Two independent repairs; take whichever is cheaper in Lean.**

*Repair (a) — reviewer's minimal-prime sandwich (general).* Write `F_p = ker(f ⊗ κ(p))`,
`H_p = ker(d⁰ ⊗ κ(p))`.
 1. `d⁰_p = i_p ∘ f_p` gives `F_p ↪ H_p`, so `dim F_p ≤ 1`.
 2. Let `η ⊆ p` be a minimal prime. `R` reduced ⟹ `R_η = κ(η)` is a **field**, hence flat over
    `R`, hence `i ⊗ κ(η)` stays injective and `F_η = H_η`, so `dim F_η = 1`.
 3. By (F4), `dim ker(u_η) = 1` and `dim ker(u_p) = dim F_p ≤ 1`.
 4. Trivialise `K⁰` on a basic open containing both `η` and `p`; matrix rank only drops under
    specialisation `η ⤳ p`, so `dim ker(u_p) ≥ dim ker(u_η) = 1`.
 Hence `dim ker(u_p) = 1`. **Reducedness is used twice in Blocker 2** — here, and again in 0FWG.

*Repair (b) — the two-element cover (my B2.3, cheaper when available).* If `C^q = 0` for
`q ≥ 2` then `Z¹ = C¹`, `i = id`, and the gap simply does not exist; simultaneously
`Flat R Z¹` and `hbij` (the hypotheses of `shortComplexBaseChangeKernelEquiv`) hold trivially.

**Recommendation: pursue (b) first**, fall back to (a). They repair the same defect from
different directions — (b) removes `i` from the picture, (a) tolerates it.

#### A2′ — follow-up (checked 2026-08-08, after the review): BOTH repairs are needed, and (b) is not free

Two corrections to the recommendation above.

*(b) is not freely available.* `IsInvertible.exists_finiteAffineBaseCech_flat`
(`Picard/InvertibleSheafBaseCechFlat.lean:23`) is a thin wrapper over
`hM.exists_finite_affine_trivializingCover`, a generic quasi-compactness argument with **no
control on `card ι`**. A two-element trivialising affine cover is false for a general proper
scheme; for a relative curve it is plausible (complement of an ample relative divisor is affine)
but proving it is its own development.

*(a) does not remove the flatness requirement.* The minimal-prime sandwich repairs the
**dimension identification** `dim ker(u_p) = 1`. It does **not** discharge
`[Module.Flat R (ker d¹)]`, which is a *variable* of the `LowDegreeFiniteReplacement` namespace
(`variable [Module.Flat R C0] [Module.Flat R Z1]`) and so is needed to construct the replacement
at all. Nor can it be dodged by applying the replacement to `d⁰ : C⁰ → C¹` directly: that needs
`Module.Finite R (C¹/im d⁰)`, and only `H¹ = Z¹/im d⁰` is finite — `C¹/Z¹` is not.

**Conclusion — KM-SEESAW-2″ must carry one extra hypothesis: exactness of `C^•` at positions
`≥ 2`.** In the shape the tree already uses,

```lean
(hhigh : ∀ q, 1 ≤ q → Function.Exact ((C.d q (q + 1)).hom) ((C.d (q + 1) (q + 2)).hom))
```

This is strictly weaker than AP2-A2's `hexact` (which also demands position 1, i.e. `H¹ = 0` —
false here) and it is **automatic in the application**: the fibres are curves, so
`H^{≥2}(X_s, M_s) = 0`, and the tree's spreading lemma
`HomologicalComplex.functionExact_of_bounded_flat_forall_field_baseChange_exact_of_finite_homology`
lifts per-field exactness to `R`, exactly as `kernel_data_of_hasDegreeOneFibreCohomology` does —
just over `q ≥ 1` instead of all `q`. The tree already has the fibre input
(`subsingleton_H_add_two_of_two_affine_open_cover`, via a two-affine-cover fibre model).

From `hhigh`, `Flat R Z¹` follows by **descending induction** on the bounded complex: `Z^N = C^N`
is flat; and for `1 ≤ i < N`, `im d^i = Z^{i+1}` by exactness at `i+1`, so
`0 → Z^i → C^i → Z^{i+1} → 0` is exact with `C^i` and `Z^{i+1}` flat, hence `Z^i` is flat. The
same short exact sequences give `ker(d¹ ⊗ A) = Z¹ ⊗ A`, i.e. the `hbij` argument.

So the corrected ticket set is: **T4c(i)** `hhigh ⟹ Flat R Z¹ + hbij` (descending induction),
and **T4c(ii)** the minimal-prime sandwich for `dim ker(u_p) = 1`. Both are required; neither
alone suffices.

#### A2″ — **T4c(i) IS ALREADY PROVED IN THE TREE** (found 2026-08-08; zero new work)

Grepping for the *conclusion* rather than the inputs turned up both halves, already sorry-free in
`ForMathlib/BaseChangeKerCoker.lean`, each stated with exactly the "exact from degree `k` onward"
hypothesis this section derived — no full exactness:

```lean
theorem Module.Flat.ker_of_bounded_exact_from [∀ n, Module.Flat R (M n)]
    (N k : ℕ) (hk : k ≤ N) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, k ≤ n → n < N → Function.Exact (d n) (d (n + 1))) :
    Module.Flat R (LinearMap.ker (d k))                                    -- :292

theorem kerBaseChangeComparison_bijective_of_bounded_exact_from
    (M) (d) (A) [CommRing A] [Algebra R A] [∀ n, Module.Flat R (M n)]
    (N k : ℕ) (hk : k ≤ N) [Subsingleton (M (N + 1))]
    (hexact : ∀ n, k ≤ n → n < N → Function.Exact (d n) (d (n + 1))) :
    Function.Bijective (kerBaseChangeComparison A (d k))                   -- :625
```

Its own docstring says it: *"The cycle module in degree `k` is flat when a bounded complex of flat
modules is exact from degree `k` onward. **No exactness in lower degrees is required.**"*
Instantiate both at `k = 1`: `hhigh` is precisely their `hexact`, and they deliver `Flat R Z¹` and
`hbij` directly. Supporting lemma `Module.Flat.quotient_range_of_bounded_exact_from` (:270) gives
`Flat R (C² ⧸ range d¹)`, which is what feeds `kerBaseChangeComparison_bijective`.

**T4c(i) is therefore closed with no new declarations.** What remains of T4c is only (ii), the
minimal-prime sandwich. (Lesson, already in memory as `grep-the-conclusion-not-the-inputs`: the
descending-induction argument was re-derived from scratch here before anyone grepped for
`Module.Flat` + "bounded" + "from".)

With the repair inserted, the reviewer confirms the rest of B.1: the dimension count
`dim coker(u_p) = rk K¹ − rk_p K⁰ + 1`, local constancy from `K⁰` finite projective, right
exactness `(coker u) ⊗ κ(p) ≅ coker(u_p)`, and — explicitly — that **applying 0FWG only to
`coker u` is legitimate**, the two splittings then giving `ker(u_A) = (ker u) ⊗ A` for all `A`.

Caveat recorded by the reviewer: this proves arbitrary base change for `ker u` and `ker f`, **not
automatically for Čech `H⁰`**; for residue fields the 1-dimensional comparison forces it, for
general `A` it may not.

### A3 — Blocker 2 / B2.1 (Stacks 0FWG): proof CONFIRMED correct

No Noetherian hypothesis is needed anywhere; `Module.Finite R M` suffices. Two wording fixes:
choose `x₁ … xₙ ∈ M` **whose images form** a basis (rather than "lifting a preselected basis");
and state the conclusion as "the composite `K_q → R_q^n → κ(q)^n` is zero, hence
`K_q ⊆ q R_q^n`" — **not** as `K ⊗ κ(q) = 0`, which does not follow. `q R_q ∩ R_g = q` is the
step that puts the coordinates in every prime, hence in the nilradical, hence at `0`.

### A4 — Blocker 2 / B.2: not circular, but needs the comparison diagram written out

The order must be: `P := ker u ≅ Γ(X,M)`, then
`P ⊗ κ(p) ≅ ker(u_p) ≅ ker(f_p) ↪ H⁰(X_p, M_p)` — first iso from the splittings, second from
(F4), last arrow induced by `Z¹_p → C¹_p` — and this injection is an **isomorphism by dimension
count** (both sides are 1-dimensional, by A2). Only then: a local basis `ℓ` restricts to a
nonzero element of `H⁰(X_p, M_p) ≅ κ(p)`, so `ℓ_p` is nowhere vanishing on `X_p`; finally at
`y ∈ X` over `p`, evaluation is multiplication by `a ∈ 𝒪_{X,y}` whose class mod `p𝒪_{X,y}` is a
unit, so `a` is a unit. Reviewer's warning: *"splitting alone gives the cohomological base-change
isomorphism"* is **too strong** — it is splitting **plus** the 1-dimensional injection.

### A5 — Blocker 3: R1 confirmed cheaper, with two new obligations

Ranking returned: **(1) R1 with the repaired B.1; (2) a generic-vertical-divisor route, if a
Weil/Cartier package already exists; (3) complete projective addition-law charts (R2).**

Two obligations R1 acquires that my plan did not list:

* **`B = C ×_U C` need not be affine.** The seesaw as stated carries `[IsAffine S]`. Apply it on
  an affine open cover of `B` and glue with the descent lemma. **New ticket T8b.**
* **The passage from an arbitrary elliptic curve to the universal Weierstrass parameter space is
  only Zariski-local** — globally there is a moduli-stack issue. The base-change-down step (route
  item 5) must be stated locally on `T` and glued, not globally. **New ticket T9b.**

Why the cheap R2 shortcut fails, recorded so it is not re-derived: the diagonal, antidiagonal and
zero-section loci in the universal pair are **codimension 1**, so an isomorphism of line bundles
on their complement need not extend (reflexivity only extends across codimension ≥ 2).

The third route, for the record: trivialise the ratio bundle on the generic fibre, view it as a
rational trivialisation on `E_B`, observe its divisor is vertical, note every vertical prime
divisor is a whole fibre over a codimension-one point of the regular `B`, hence Cartier, so
`div(s) = f^*D` and `L ≅ f^*𝒪_B(D)`. Uses only the theorem of the square over the generic field —
but needs rational sections, vertical-prime classification, codimension formulas and pullback
multiplicities. Compare Stacks 0BF0 / 0EX8.

### A6 — Blocker 4: my recorded reasoning was WRONG, and route (i) does not dodge Artin–Rees

**Correction to the board note of 2026-08-07.** *"The local generator vanishes on `Z`, therefore
it is not a nonzerodivisor"* is **false reasoning**: `t ∈ k[t]` vanishes on `V(t)` and is a
nonzerodivisor. Vanishing geometrically and being a zerodivisor are unrelated; what fails is only
that it is a *unit*. The board note must be amended.

**Route (i) is exactly the local criterion.** Locally, after trivialising `M`, the map is
multiplication by `h : B → B`; "`h̄` a nonzerodivisor in `B/𝔪_A B` ⟹ `h` a nonzerodivisor and
`B/hB` flat over `A`" **is** Stacks 00MF, the principal-element specialisation of 00ME, whose
standard proof runs through Krull intersection, i.e. Artin–Rees. So (i) does not avoid the gap.

**Route (ii) — build the section from the fibre points — is not viable.** `S_red → S` has exactly
the same residue-field fibres as `S → S` and is generally not an isomorphism; fibre points say
nothing in nilpotent directions.

**The genuine Artin–Rees-free alternative is transversality.** At `z ∈ Z_s`: trivialise `M` near
`z`, write `σ` as `h`; since `Z_s = Spec κ(s)` scheme-theoretically and `E_s` is a smooth curve,
`h̄` generates the maximal ideal of the DVR `𝒪_{E_s,z}`, so `dh̄ ≠ 0` in
`Ω_{E_s/κ(s),z} ⊗ κ(z)`. Then `h : U → 𝔸¹_S` has both sides smooth of relative dimension 1 and an
isomorphism on relative differentials at `z`, hence is **étale** near `z`; so
`Z ∩ U = U ×_{𝔸¹_S} S` is étale over `S`; `Z` is closed in the proper `E` hence proper; proper +
étale ⟹ finite étale; fibre degree 1 ⟹ isomorphism. (Stacks §37.38 / 055S. Prove the special
case from a standard-smooth Jacobian presentation — the *general* Stacks slicing lemma internally
routes through fibrewise flatness, which would reintroduce the gap.)

**Hypothesis audit for Blocker 4** (reviewer): `h⁰ = 1` and `H¹ = 0` alone do **not** encode what
is needed. The statement must also carry smooth, geometrically integral, genus-one fibres;
`deg M_s = 1`; and the base-change isomorphism making the chosen generator satisfy `σ_s ≠ 0`.

### Revised ticket deltas

| New/changed | Ticket | Note |
|---|---|---|
| changed | T2 | statement stands; docstring records the `hfibt`-vs-fibrewise counterexample |
| **new** | T4c | the A2 repair: two-element cover (preferred) or minimal-prime sandwich |
| changed | T4 | 0FWG: drop `IsNoetherianRing`; fix the two wordings in A3 |
| changed | T6 | write the A4 comparison diagram explicitly; do not claim base change from splitting alone |
| **new** | T8b | affine-cover + glue, since `B = C ×_U C` is not affine |
| **new** | T9b | universal-curve comparison is Zariski-local on `T`; state and glue locally |
| changed | T10/T11 | abandon the nonzerodivisor/local-criterion route; **re-plan as the étale transversality argument**, and strengthen the hypotheses per the audit above |

## Open questions for external review

1. Is B2.2 (replacement complex + `coker` has locally constant fibre rank + reduced ⟹ locally
   free) the right way to get Grauert-at-rank-one without cohomology-and-base-change, or is
   there a shorter route given `dim ker(d ⊗ κ) ≡ 1`?
2. Is the B2.1 proof sketch correct as stated (in particular the step `K_q ⊆ q R_q^n` ⟹
   coordinates in the nilradical)?
3. Blocker 3: seesaw route vs. the chart/line-function route (A) — which is genuinely cheaper
   now that the seesaw's gap is priced?
4. Blocker 4: does the section-side reroute actually avoid the sorried Artin–Rees criterion?
