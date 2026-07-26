# Decomposition — DS4 M1c: the field-level Weil pairing as a scheme morphism

`/develop --decompose`, 2026-07-26. Adversarial pass. **No tickets created.**

## Goal (top-level result R)

```lean
theorem exists_weilPairingHom_of_field (k : Type u) [Field k] [CharZero k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) (N : ℕ) [NeZero N] (hk : (N : k) ≠ 0) :
    ∃ w : muNAlgebra k N hk ⟶ torsionPairAlgebra k E N hk,
      ∀ f : ((torsionPairAlgebra k E N hk).obj →ₐ[k] AlgebraicClosure k),
        f.comp w.hom.hom = weilPairingFibreMap k E N hk
          (torsionPairAlgebraPointsEquiv k E N hk f)
```

i.e. the DS4 pairing `e_N : E[N] ×_{Spec k} E[N] ⟶ μ_{N,Spec k}` **over a field of
characteristic zero**, pinned on geometric fibres to the Weil pairing.

### Mathematical source (already formalised)

The mathematics is done. `HasseWeil` proves Silverman AEC III.8 over an algebraically
closed field; this project proved its Galois equivariance last session:

> `ModularCurves.weilPairing_galois` (`WeilPairing/GaloisFunctionField.lean`)
> ```
> e_N(σ·S, σ·T) = σ (e_N(S, T))   for every σ ∈ Gal(L/k), L alg. closed
> ```
> axioms: `propext`, `Classical.choice`, `Quot.sound`.

and the descent engine exists:

> `ModularCurves.EllipticCurve.exists_pairingAlgebraHom_of_galoisEquivariant`
> (`WeilPairing/EtaleDescent.lean:440`) — a `Gal(k̄/k)`-equivariant map on
> fibre-functor values is induced by an actual morphism of finite étale `k`-algebras.

**Everything below is transport engineering between the two.** There is no new
mathematics; each leaf's "source" is therefore a Lean declaration in this repo or in
mathlib, quoted verbatim, rather than a textbook page. That is the honest citation: the
textbook step (KM 2.8 / Silverman III.8) is `weilPairing_galois`, already discharged.

---

## The transport chain, and why it is mostly associativity

The Galois action shows up on four different objects. Write `σ : k̄ ≃ₐ[k] k̄`,
`t := Spec.map (CommRingCat.ofHom (algebraMap k k̄))`, `Σ := Spec.map (CommRingCat.ofHom σ)`.

| object | Galois action | established |
|---|---|---|
| fibre-functor values `A →ₐ[k] k̄` | `f ↦ σ ∘ f` | given (this is what the descent engine consumes) |
| `Spec k̄`-points of an affine `k`-scheme | `g ↦ Σ ≫ g` | **`algHomEquivSpecOver_comp_algEquiv`** ✔ landed |
| scheme points `E.Point t` | `P ↦ Σ ≫ P.1` | ditto (through `torsionAlgebraFibreEquiv_comp_algEquiv` ✔ landed) |
| affine Weierstrass points `(W ⊗ k̄).toAffine.Point` | `Affine.Point.map σ` = `galoisPointEquiv` | **this is 4b** |

`chartAffinePointEquiv` (`WeilPairing/FibrePointDict.lean:49`) is the composite

```
E.Point (t' ≫ chartρ V)  --chartPointsEquiv-->  (modelEllipticCurve Pr.W).Point t'
                         --modelPointAddEquiv-->  (Pr.W.baseChange k̄).toAffine.Point
```

and unwinding the definitions:

* `chartPointsEquiv Pr t' = (Point.baseChangeEquiv E (chartρ V) t').symm.trans
  (pointAddEquiv (chartRecordIso Pr) _ t')` — and both factors are **postcomposition
  with a fixed morphism**:
  * `Point.baseChangeEquiv_apply_coe` : `(baseChangeEquiv E σ t x).1 = x.1 ≫ pullback.fst E.π σ` — `rfl`;
  * `pointMapOfHom_coe` : `(pointMapOfHom e P).1 = P.1 ≫ e.left` — `rfl`;
  * the inverse of `baseChangeEquiv` is `y ↦ ⟨pullback.lift y.1 t y.2, _⟩`, and
    `pullback.lift` composed on the left with `Σ` is `pullback.lift (Σ ≫ y.1) (Σ ≫ t)`
    by `pullback.hom_ext`.

  So `chartPointsEquiv` commutes with `P ↦ Σ ≫ P.1` **by associativity alone**. No
  coordinates, no elaboration risk.

* `modelPointAddEquiv W = Equiv.subtypeEquivProp rfl |>.trans (projModelPointsEquiv W k̄)`
  — so the entire mathematical content of 4b sits in `projModelPointsEquiv`.

And `projModelPointsEquiv` is pinned by exactly two value lemmas, so the naturality is a
two-case argument:

* `projModelPointsEquivEll_infinity` : `¬ InZChart W g → projModelPointsEquiv W K g = 0`
* `projModelPointsEquivEll_some` : `InZChart W g → x,y read off → = Affine.Point.some x y _`

with the coordinate readout being, **verbatim from the repo** (`AutFixedPoints.lean:594`):

```lean
have h0 : (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k ⟨g, hZ⟩)).1 ⟨0, by decide⟩ =
    (chartHomEquiv W 2 k ⟨g, hZ⟩).1
      (chartCoordEquiv W 2 (Ideal.Quotient.mk _
        (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})))) :=
  rfl
```

i.e. `x = φ(u₀)`, `y = φ(u₁)` where `φ := chartHomEquiv W 2 K ⟨g, hZ⟩` and `u₀, u₁` are
**fixed elements of the Away-algebra, independent of `K` and of the point**. So once we
know `φ` conjugates to `σ ∘ φ`, the coordinates transform by `σ` and we are done.

**This is why 4b is a ~5-leaf job, not the multi-hundred-line chapter I scoped it as
last session.** The earlier scoping (recorded in `decomposition-caveats.md`) assumed the
readout was buried; it is not — `AutFixedPoints.lean` already surfaced it as `rfl`.

---

## Decomposition tree

### Node A — `projModelPointsEquiv` is `σ`-natural (the only content of 4b)

Internal node. Sub-decomposition mirrors the two value lemmas of the dictionary.

---

- **A1** (leaf, project): `specMap_algEquiv_isIso` — `Spec (ofHom σ)` is an isomorphism.
  - Lean statement (to be written, `EllipticCurve/PointsDictionaryGalois.lean`):
    ```lean
    theorem isIso_specMap_ofHom_algEquiv {K : Type u} [CommRing K] [Algebra R K]
        (σ : K ≃ₐ[R] K) : IsIso (Spec.map (CommRingCat.ofHom (σ : K →+* K))) := by sorry
    ```
  - Source (verbatim, mathlib `AlgebraicGeometry/Scheme.lean`):
    > `Spec.map_comp : Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f`
    > `Spec.map_id : Spec.map (𝟙 R) = 𝟙 (Spec R)`
  - Lean ↔ source match: `ofHom σ ≫ ofHom σ.symm = 𝟙` and symmetrically (both by
    `CommRingCat.hom_ext` + `σ.symm_apply_apply`), so `Spec.map (ofHom σ.symm)` is a
    two-sided inverse of `Spec.map (ofHom σ)`.
  - Discharged by: `Spec.map_comp`, `Spec.map_id`, `CommRingCat.hom_ext` (3 lemmas).
  - **Attacks attempted:**
    - [1] Counterexample: none possible — `Spec` is a functor and functors preserve isos;
      the statement is an instance of `Functor.map_isIso`. Searched `lean_local_search`
      for a contradicting `¬ IsIso (Spec.map _)` — nothing.
    - [2] Edge cases: `σ = 1` (then `Spec.map (ofHom 1) = 𝟙` ✓); `K` trivial ring
      (`Spec K = ∅`, identity is an iso ✓).
    - [3] Hypothesis test: `[Algebra R K]` is not used — the statement holds for any
      `σ : K ≃+* K`. **Flaw found (over-specified).** Fix: state for `K ≃+* K` and let
      the caller pass `σ.toRingEquiv`. Statement corrected above → restated as
      `isIso_specMap_ofHom_ringEquiv (σ : K ≃+* K)`.
    - [4] Source drift: n/a (pure category theory).
    - [5] Discharge attack: `Spec.map_comp`/`Spec.map_id` verified to exist with the
      quoted types (mathlib `AlgebraicGeometry/Scheme.lean`).
    - Verdict: SURVIVED after weakening the hypothesis.
  - Prior-B2 log: `b2_log.jsonl` has 1 entry (`legendreDelta_surjective_of`); no name or
    shape match.

- **A2** (leaf, project): `InZChart` is invariant under the `σ`-action.
  - Lean statement:
    ```lean
    theorem inZChart_specMap_comp_iff (W : WeierstrassCurve R) {K : Type u} [Field K]
        [Algebra R K] (σ : K ≃ₐ[R] K) (g : SpecPoints (projModel W) (projModelπ W) K) :
        InZChart W (specMapCompPoint W σ g) ↔ InZChart W g := by sorry
    ```
    where `specMapCompPoint W σ g : SpecPoints … K` is `⟨Spec.map (ofHom σ) ≫ g.1, _⟩`
    (the side condition uses `specMap_algEquiv_comp_specMap_algebraMap`, already landed
    in `WeilPairing/GaloisFibre.lean`).
  - Source (verbatim, `EllipticCurve/WeierstrassModel.lean`, definition of `InZChart`):
    > ```lean
    > ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (projIdeal W))
    >     ((quotientGradingHom (projIdeal W)) (MvPolynomial.X i)))),
    >   h ≫ Proj.awayι (quotientGrading (projIdeal W)) _
    >     (mk_X_mem_quotientGrading_one W i) one_pos = g.1
    > ```
  - Lean ↔ source match: `InZChart` asserts a factorisation through the chart immersion.
    (→) if `h ≫ ι = g.1` then `(Σ ≫ h) ≫ ι = Σ ≫ g.1`. (←) precompose with the inverse
    from A1.
  - Discharged by: `Category.assoc`, A1 (2 lemmas).
  - **Attacks attempted:**
    - [1] Counterexample: the ← direction genuinely needs `Σ` to be *epi*/iso; searched
      for a version of `InZChart` that is not stable under precomposition — none. Without
      A1 the ← direction is **false** for a general ring map (a point of the `Y`-chart can
      pull back into the `Z`-chart along a non-surjective base change? no — precomposition
      only shrinks the image, so ← really does need invertibility). A1 supplies it.
    - [2] Edge cases: `g` = the infinity point (`infPoint_not_inZ`), `σ = 1`. Both fine.
    - [3] Hypothesis test: `[Field K]` is not needed for this leaf (`InZChart` is defined
      for `CommRing K`). **Flaw found (over-specified)** — weaken to `[CommRing K]`.
    - [4] Source drift: re-read the `InZChart` definition at
      `WeierstrassModel.lean`; the quote above is the definition verbatim. No drift.
    - [5] Discharge attack: A1 is a leaf of this same tree (not yet proved) — so A2
      **depends on A1**; recorded as an edge, not a discharge.
    - Verdict: SURVIVED after weakening to `[CommRing K]`.

- **A3** (leaf, project): the chart hom conjugates.
  - Lean statement:
    ```lean
    theorem chartHomEquiv_specMap_comp (W : WeierstrassCurve R) {K : Type u} [CommRing K]
        [Algebra R K] (σ : K ≃ₐ[R] K)
        (g : SpecPoints (projModel W) (projModelπ W) K) (hZ : InZChart W g)
        (hZ' : InZChart W (specMapCompPoint W σ g)) :
        (chartHomEquiv W 2 K ⟨specMapCompPoint W σ g, hZ'⟩).1 =
          (σ : K →+* K).comp (chartHomEquiv W 2 K ⟨g, hZ⟩).1 := by sorry
    ```
  - Source (verbatim, `EllipticCurve/WeierstrassModel.lean:792`):
    > ```lean
    > lemma chartHomEquiv_eq_of_specMap (W : WeierstrassCurve R) (i : Fin 3) … (g) (φ)
    >     (hfac : Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι … = g.1.1) :
    >     chartHomEquiv W i K g = φ
    > ```
  - Lean ↔ source match: `chartHomEquiv` is characterised by the factorisation. Put
    `φ := chartHomEquiv W 2 K ⟨g, hZ⟩`, so `Spec.map (ofHom φ) ≫ ι = g.1`. Then
    `Spec.map (ofHom (σ ∘ φ)) ≫ ι = Spec.map (ofHom φ ≫ ofHom σ) ≫ ι
      = Spec.map (ofHom σ) ≫ Spec.map (ofHom φ) ≫ ι = Σ ≫ g.1`,
    which is the factorisation for `specMapCompPoint W σ g`; apply the quoted lemma.
    The side condition (`φ` restricted to grade zero is `algebraMap R K`) survives because
    `σ` is `R`-linear: `σ ∘ algebraMap R K = algebraMap R K`.
  - Discharged by: `chartHomEquiv_eq_of_specMap`, `Spec.map_comp`, `Category.assoc`,
    plus the recovery of the factorisation from `hZ` (`Equiv.symm_apply_apply` on
    `chartHomEquiv`) — 4 steps, at the ≤3 threshold's edge, so **A3 is written as two
    lemmas**: `chartHomEquiv_factors` (recover the factorisation) and the conjugation.
  - **Attacks attempted:**
    - [1] Counterexample search: `lean_local_search "chartHomEquiv"` — no lemma asserting
      the opposite; the equiv is injective so at most one `φ` can satisfy the
      factorisation, hence the claim is forced once the factorisation is exhibited.
    - [2] Edge cases: `σ = 1` gives `φ = φ` ✓. `g` the infinity point is excluded by `hZ`.
    - [3] Hypothesis test: `R`-linearity of `σ` is **necessary** — the subtype condition
      on `chartHomEquiv`'s codomain pins the restriction to `algebraMap R K`, and a
      non-`R`-linear `σ` would break it. Not over-specified.
    - [4] Source drift: the quoted `chartHomEquiv_eq_of_specMap` is at
      `WeierstrassModel.lean:792` and says exactly "a chart-factoring point that IS
      `Spec.map φ` followed by the chart immersion reads out as `φ`". Match.
    - [5] Discharge attack: `chartHomEquiv_eq_of_specMap` verified present at the cited
      line with the quoted signature (read this session).
    - Verdict: SURVIVED; split into two declarations on the ≤3-lemma rule.

- **A4** (leaf, project): the coordinate readout transforms by `σ`.
  - Lean statement:
    ```lean
    theorem chartSolution_specMap_comp (W : WeierstrassCurve R) {K : Type u} [CommRing K]
        [Algebra R K] (σ : K ≃ₐ[R] K) (g) (hZ) (hZ') (j : {j : Fin 3 // j ≠ 2}) :
        (chartSolutionsEquiv W 2 K
            (chartHomEquiv W 2 K ⟨specMapCompPoint W σ g, hZ'⟩)).1 j =
          σ ((chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 j) := by sorry
    ```
  - Source (verbatim, `EllipticCurve/AutFixedPoints.lean:592-598`):
    > ```lean
    > have h0 : (chartSolutionsEquiv W 2 k (chartHomEquiv W 2 k ⟨…⟩)).1 ⟨0, by decide⟩ =
    >     (chartHomEquiv W 2 k ⟨…⟩).1
    >       (chartCoordEquiv W 2 (Ideal.Quotient.mk _
    >         (MvPolynomial.X (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2})))) :=
    >   rfl
    > ```
  - Lean ↔ source match: the quoted `rfl` says the `j`-th solution coordinate is literally
    `φ` applied to a **fixed** element `uⱼ := chartCoordEquiv W 2 (mk (X j))` of the
    Away-algebra. With A3, `φ' = σ ∘ φ`, so coordinate `j` becomes `σ (φ uⱼ)`. Two `rfl`s
    and one rewrite.
  - Discharged by: A3 + the two `rfl`s (2 steps).
  - **Attacks attempted:**
    - [1] Counterexample: the `rfl` is quoted from compiled repo code, so the readout
      formula is verified by the compiler, not by me. No counterexample possible.
    - [2] Edge cases: `j = ⟨0,_⟩` and `j = ⟨1,_⟩` are the only inhabitants used downstream;
      the statement is uniform in `j` so no case analysis is needed.
    - [3] Hypothesis test: does the leaf need `[Field K]`? No — `chartSolutionsEquiv` is
      stated for `[CommRing K]`. Kept at `CommRing`.
    - [4] Source drift: the quoted `rfl` appears twice in `AutFixedPoints.lean` (indices 0
      and 1) and is in *compiled* code. Verified by reading the file this session.
    - [5] Discharge attack: A3 is a tree edge. The `rfl`s are compiler-verified.
    - Verdict: SURVIVED.

- **A5** (internal → the node-A conclusion): `projModelPointsEquiv` naturality.
  - Lean statement:
    ```lean
    theorem projModelPointsEquiv_specMap_comp (W : WeierstrassCurve R) [W.IsElliptic]
        {K : Type u} [Field K] [Algebra R K] (σ : K ≃ₐ[R] K)
        (g : SpecPoints (projModel W) (projModelπ W) K) :
        projModelPointsEquiv W K (specMapCompPoint W σ g) =
          WeierstrassCurve.Affine.Point.map (baseChangeAlgHom W σ)
            (projModelPointsEquiv W K g) := by sorry
    ```
    (`baseChangeAlgHom W σ : (W ⊗ K) →ₐ[?] (W ⊗ K)` — the mathlib `Affine.Point.map`
    input; see the API-design note below.)
  - Sub-decomposition: case split on `InZChart W g`.
    * `¬ InZChart`: both sides are `0` — LHS by `projModelPointsEquivEll_infinity` (using
      A2 to transport `¬ InZChart`), RHS by `Affine.Point.map` of `0` being `0` (mathlib
      `Point.map` is an `AddMonoidHom`, `map_zero`).
    * `InZChart`: both sides are `some`, LHS with coordinates `(σ x, σ y)` by A4 and RHS
      with the same by mathlib's `Affine.Point.map_some`.
  - **Composition attack (internal node):** could A1–A4 all hold and A5 fail?
    * The two cases are exhaustive and mutually exclusive (`Classical.em`). ✔
    * In the `some` case both sides need the *same* nonsingularity witness — but
      `Affine.Point.some` is proof-irrelevant in its third argument (`Nonsingular` is a
      `Prop`), and `projModelPointsEquivEll_some` takes the witness as a hypothesis
      precisely so the caller supplies it. ✔
    * The `¬InZChart ⇒ 0` case needs A2's **←** direction, which is the one that needs
      A1. Flagged as the composition's single fragile edge; A1 supplies it. ✔
    - Verdict: composition SURVIVED.

### Node B — `modelPointAddEquiv` naturality
- **B1** (leaf, project): `Point.restrict` along `Spec σ` is precomposition — `rfl` from
  `Point.restrict` (`GroupLaw.lean:144`: `⟨k ≫ P.1, _⟩`), plus a `base_congr` transport
  along `specMap_algEquiv_comp_specMap_algebraMap` (**already landed**,
  `WeilPairing/GaloisFibre.lean`).
- **B2** (leaf): `modelPointAddEquiv` naturality = A5 through `Equiv.subtypeEquivProp rfl`.
  - Attacks: [1] the `subtypeEquivProp rfl` is definitionally the identity on carriers, so
    nothing can go wrong; [2] edge case `P = 0` ✓; [3] no hypotheses to weaken;
    [4]/[5] discharge is A5. SURVIVED.

### Node C — `chartPointsEquiv` naturality (pure associativity)
- **C1** (leaf): `(Point.baseChangeEquiv E ρ t).symm` commutes with `Σ ≫ ·`.
  - Discharged by `pullback.hom_ext` + `pullback.lift_fst`/`_snd` + `Category.assoc`.
  - Verbatim source: `Point.baseChangeEquiv` (`GroupLaw.lean:392-401`), whose `invFun` is
    > `invFun y := ⟨pullback.lift y.1 t y.2, pullback.lift_snd _ _ _⟩`
  - Attacks: [1] no counterexample — `pullback.lift` is characterised by its two
    projections and both slide past `Σ`; [2] edge `Σ = 𝟙`; [3] no unnecessary hypotheses;
    [4] the quoted `invFun` is the definition; [5] `pullback.hom_ext` verified in mathlib.
    SURVIVED.
- **C2** (leaf): `pointAddEquiv` commutes with `Σ ≫ ·` — `pointMapOfHom_coe` is
  `P.1 ≫ e.left`, so this is `Category.assoc` alone.
  - Verbatim source: `pointMapOfHom` (`LevelStructure/IsoTransport.lean:155-158`):
    > `⟨P.1 ≫ e.left, (Category.assoc _ _ _).trans (…)⟩`
  - Attacks: [1]–[5] as C1; the statement is literally associativity. SURVIVED.

### Node D — `chartAffinePointEquiv` naturality
Internal; `= C ∘ B`. Composition attack: the two equivs are composed in the order
`chartPointsEquiv` then `modelPointAddEquiv`, and both naturality squares are stated with
the same `Σ ≫ ·` action on the middle object, so they paste. ✔

### Node E — `fibreWeilPairing` is `σ`-equivariant
- **E1** (leaf): from `fieldWeilPairing_galois` (**already landed**,
  `WeilPairing/GaloisFieldPairing.lean`) + D + `fieldWeilPairing_congr`.
  - Verbatim source (this repo):
    > ```lean
    > theorem fieldWeilPairing_galois (N : ℕ) (hN : (N : L) ≠ 0) (P Q) (hP) (hQ) (hσP) (hσQ) :
    >     (fieldWeilPairing (W.baseChange L) N hN
    >         (galoisPointEquiv W σ P) (galoisPointEquiv W σ Q) hσP hσQ : L) =
    >       σ (fieldWeilPairing (W.baseChange L) N hN P Q hP hQ : L)
    > ```
  - Lean ↔ source match: D says the chart dictionary carries `Σ ≫ ·` to
    `galoisPointEquiv`; substituting into the quoted identity gives the claim.
  - Attacks: [1] no counterexample (the identity is proved); [2] edge `P = Q = 0`
    (pairing = 1, `σ 1 = 1` ✓); [3] the `(N : L) ≠ 0` hypothesis is needed and present;
    [4] no drift — quoted from the compiled repo; [5] `galoisPointEquiv` = `Affine.Point.map σ`
    **by definition** (`GaloisFunctionField.lean:583`: `toFun := Affine.Point.map σ.toAlgHom`)
    — this is the join point between D and E and is `rfl`. SURVIVED.

### Node F — the geometric point over `Spec k` matches the chart's
- **F1** (leaf): for `S = Spec (of k)`, `V = ⊤`,
  `Spec.map (ofHom (algebraMap Γ(S,⊤) k̄)) ≫ chartρ ⊤ = Spec.map (ofHom (algebraMap k k̄))`
  after the `ΓSpecIso` identification.
  - Verbatim source: `chartρ` (`Moduli/E3DatumAssembly.lean:66`):
    > `noncomputable abbrev chartρ (V : S.affineOpens) : Spec Γ(S, V.1) ⟶ S := V.2.isoSpec.inv ≫ V.1.ι`
  - Discharged by `Scheme.ΓSpecIso_naturality` + `Scheme.isoSpec_Spec_inv` + `Opens.ι` at `⊤`
    being the identity (3 lemmas).
  - Attacks: [1] counterexample would need `Spec k` to have a second affine open containing
    the point — impossible, `Subsingleton (PrimeSpectrum k)` (used already in
    `GlobalChartOverField.lean`); [2] edge: `k̄ = k` ✓; [3] hypotheses minimal;
    [4] the `chartρ` quote is the definition; [5] the three mathlib lemmas verified.
    SURVIVED.
  - **Risk note**: this is the leaf most likely to need patience with `Opens ⊤` coercions.
    Break it into `chartρ_top` (`chartρ ⊤ = (ΓSpecIso _).inv-transport`) and the composite.

### Node G — step 5, the assembly
- **G1** (leaf): define `weilPairingFibreMap` and prove its equivariance from E, using the
  already-landed `torsionAlgebraFibreEquiv_comp_algEquiv` and
  `muNAlgebraFibreEquiv_comp_algEquiv`.
- **G2** (assembly node): `exists_weilPairingHom_of_field := exists_pairingAlgebraHom_of_galoisEquivariant … G1`.
  - Verbatim source (this repo, `WeilPairing/EtaleDescent.lean:440`):
    > ```lean
    > theorem exists_pairingAlgebraHom_of_galoisEquivariant (k) [Field k] [CharZero k] (E) (N)
    >     [NeZero N] (hk) (p) (hp : ∀ σ x, p (σ.toAlgHom.comp x.1, σ.toAlgHom.comp x.2) =
    >       σ.toAlgHom.comp (p x)) : ∃ w, ∀ f, f.comp w.hom.hom = p (torsionPairAlgebraPointsEquiv k E N hk f)
    > ```
  - Composition attack: `hp`'s shape is **postcomposition on both slots simultaneously**;
    E gives equivariance one slot at a time — but the pairing is a function of the pair, and
    E is stated for both arguments moved together, so the shapes match. ✔ The `[CharZero k]`
    hypothesis is inherited from the descent engine (it bridges `AlgebraicClosure` to
    `SeparableClosure`); our target `k = ℚ` satisfies it. ✔

---

## Ordering, and the elaboration discipline (binding for the worker)

Dependency order: **A1 → A2 → A3 → A4 → A5 → B → C → D → F → E → G**.

The owner's constraint is absolute: **no `set_option maxHeartbeats`.** The plan is built
around it:

1. **One `rfl`-sized step per declaration.** A4 is a separate lemma from A3 precisely so
   the coordinate `rfl` never has to elaborate inside a larger goal.
2. **Pass implicit arguments explicitly.** At base-changed curves and at `Proj`-chart
   terms the elaborator unfolds records and instance search diverges — every call to
   `projModelPointsEquiv`, `chartHomEquiv`, `chartSolutionsEquiv` names `W`, `i`, `K`
   explicitly, and `IsElliptic` / `Algebra` instances are passed positionally where the
   signature allows.
3. **Never `show` on heavy composites** — use `simp only [...]` with an explicit lemma
   list (the technique that unblocked `galois_conj_translateAlgHom_*` last session).
4. **`set … with h` is banned around `Ideal`/`Localization` carriers** — it caused an
   `instSemiring` mismatch in `SmoothRegularLocal` this session; write the term out.
5. If any single declaration exceeds the default heartbeat budget, the fix is to **split
   it further**, never to raise the budget.

## Feasibility assessment

Feasible, and materially smaller than the previous scoping. The decisive discovery is
that the coordinate readout of `projModelPointsEquiv` is already `rfl` in compiled repo
code (`AutFixedPoints.lean:592`), so node A is five short lemmas rather than a
re-derivation of the chart machinery; and that every other layer of
`chartAffinePointEquiv` is postcomposition, hence associativity. The only genuinely
fiddly leaf is F1 (`⊤`-open coercions). Estimated total ~350–450 LOC across two new files
(`EllipticCurve/PointsDictionaryGalois.lean` for A–B, `WeilPairing/FibreGalois.lean` for
C–G), grounded in: node A mirrors the ~40 lines of `AutFixedPoints.lean:580-640`; nodes
C/D are ~10 lines each by associativity; G mirrors the ~30-line call shape at
`EtaleDescent.lean:440-470`.

No API gap. No REVIEW-PENDING leaf. Two leaves were **corrected** by the adversarial pass
(A1 and A2 were over-specified). One composition edge (A5's `¬InZChart` case needing A1)
was flagged and is covered.


---

# ChatGPT (gpt-5.6-sol, max effort) review — corrections applied

Consulted after the tree was written, before execution. Verdict: *"The decomposition is
mathematically sound"*, with two corrections and several implementation hazards. All are
folded in below; the tree above is superseded where they conflict.

## Correction 1 — nodes C/D: `baseChangeEquiv.symm` is NOT pure associativity

> "your actual `chartPointsEquiv` uses `(Point.baseChangeEquiv ...).symm` and its
> underlying morphism is `pullback.lift`. Thus the claim 'pure associativity' is too
> strong for the composite you actually use."

The required identity is
`pullback.lift (a ≫ y) (a ≫ t) = a ≫ pullback.lift y t`,
discharged by `pullback.hom_ext` + `pullback.lift_fst` + `pullback.lift_snd` +
associativity — or, structurally, by applying the *forward* `baseChangeEquiv` to both
sides (the inverse of a natural iso is natural). **C1 is re-specified accordingly**; it is
still short, but it is not one `Category.assoc`.

## Correction 2 — ordering: node F must come FIRST

> "Step F should come earlier. Besides proving the chart open is `⊤`, you must handle the
> canonical isomorphism `Γ(Spec k, ⊤) ≃ k`, install the resulting field/algebra
> structures, prove that `σ` is linear over this global-sections field, and identify the
> composite geometric point."

**Revised order: F → A → C → B → D → E → G.** (A is already done and is independent.)

## Hazard 3 — state naturality with the base point *moving*, then specialise

> "`Spec σ ≫ t = t` will usually be propositional, not definitional. Formulate naturality
> first on underlying morphisms and use `Subtype.ext`/base-point casts... It is best to
> prove this first with the base point changing from `t` to `a ≫ t`. Only afterwards
> specialize."

Adopted. Node A already follows this shape (`specMapCompPoint` carries the base-point
proof in its subtype, and every lemma about it is stated on the underlying morphism via
`specMapCompPoint_coe`).

## Hazard 4 — chart-independence is a SEPARATE obligation

> "If the global presentation is chosen noncanonically and you need the canonical Weil
> pairing, chart independence is a separate obligation. Galois equivariance does not prove
> this; you need invariance of the field Weil pairing under pointed curve isomorphisms.
> Alternating perfect pairings are not uniquely determined by those properties alone."

**Accepted and scoped out.** `localPresentationTop` is `Nonempty.some`, so the pairing we
build depends on a chosen chart. Our target R is **existential** (`∃ w, …`), so this is not
a gap for R. It *becomes* one the moment a downstream consumer needs "the" pairing with
pinned specs. Recorded as a new leaf **H (deferred)**: `fieldWeilPairing` is invariant
under pointed isomorphisms of Weierstrass curves. Not required for R; do not ticket yet.

## Hazard 5 — `[CharZero k]` in the descent engine is not essential

> "An immediate weakening is from `[CharZero k]` to `[PerfectField k]` … For an arbitrary
> imperfect field the result remains true … If `char k ∣ N`, this particular method
> genuinely fails."

Noted; `k = ℚ` for the application, so no action. If ever generalised, the route is
`Hom_k(A, k^sep) ≃ Hom_k(A, k̄)` fibrewise rather than identifying the two closures.

## Confirmations (no change needed)

* **A5's case split is sound** — "a point cannot acquire a chart factorisation after
  precomposition by an automorphism"; invertibility of `Spec σ` is exactly what makes the
  converse safe. Also: *"Do not expect the two `some` terms to be definitionally equal:
  their nonsingularity witnesses will generally differ."* — handled by
  `affinePoint_some_congr` (proof irrelevance).
* **No coordinate-free route** — "That does not characterize the dictionary: `[-1]` is
  already a nontrivial additive automorphism fixing zero." Confirms the coordinate route
  is necessary. (ChatGPT's alternative — case-split on the *value* rather than on
  `InZChart` — was considered; the `InZChart` split is already implemented and green.)
* **Set-level Galois equivariance genuinely suffices for the descent**; no compatibility
  with group structures is needed to get the scheme morphism. Bilinearity/alternation can
  be descended afterwards by faithfulness. Three things still to check in G: *"diagonal
  equivariance on the pair fibre; equivariance of the tensor-product/pair dictionary; the
  variance"* (the algebra map goes `O(μ_N) → O(E[N]) ⊗ O(E[N])`).

# Execution log

* **Node A COMPLETE** (2026-07-26), axiom-clean:
  `EllipticCurve/PointsDictionaryGalois.lean` — A1 `isIso_specMap_ofHom_ringEquiv`,
  `specMapCompPoint`, A2 `inZChart_specMapCompPoint_iff`, A3
  `chartHomEquiv_specMapCompPoint`, A4 `chartSolution_specMapCompPoint`, A5
  `projModelPointsEquiv_specMapCompPoint`.
  Plus two new public lemmas in `EllipticCurve/WeierstrassModel.lean`
  (`chartHomEquiv_specMap_factors`, `nonsingular_chartSolution`) — both were only
  reachable through `private` defs.
  **The plan's elaboration discipline paid for itself immediately**: the first draft of A5
  timed out at `simp only [Point.some.injEq]`; splitting out
  `projModelPointsEquiv_eq_some_chartSolution`, `..._eq_zero_of_notInZChart` and
  `affinePoint_some_congr` (and letting unification supply the nonsingularity witness
  instead of naming it) made every step cheap. No heartbeat bump.

* **Nodes B, C, D COMPLETE** (2026-07-26), axiom-clean:
  `Moduli/ChartPointsGalois.lean` (B, C, `chartPointsEquiv_coe`,
  `chartPointsEquiv_congr_base`) and `WeilPairing/FibreGalois.lean` (D).
  ChatGPT's Correction 1 was right and load-bearing: C needed `pullback.hom_ext` +
  `lift_fst`/`lift_snd`, not associativity. Two `rw` motive failures (dependent on the
  base point inside `Q`'s type) were sidestepped by the morphism-level formulation, also
  as advised.

## NEW FINDING (surfaced entering node E) — the base-ring mismatch

`fieldWeilPairing_galois` is stated for a Weierstrass curve over a **field** `F` with
`σ : L ≃ₐ[F] L`. But `LocalPresentation` fixes `Pr.W : WeierstrassCurve Γ(S, V.1)`, and
`Γ(S, V.1)` is a general commutative ring. Over `S = Spec k` it *is* a field — but only
through `Scheme.ΓSpecIso`, and hypothesising `[Field Γ(S, ⊤)]` alongside the ambient
`CommRing Γ(S, ⊤)` instance creates a genuine instance diamond. So node E cannot be
stated at the `Γ(S, V.1)`-level.

This is exactly ChatGPT's hazard 6: *"you must handle the canonical isomorphism
`Γ(Spec k, ⊤) ≃ k`, install the resulting field/algebra structures, prove that `σ` is
linear over this global-sections field, and identify the composite geometric point."*

### Revised plan for E / F / G (supersedes nodes E–G above)

Decouple, so that F is the only remaining obligation and E/G do not wait on it. Introduce
the chart as **labelled data** (the pattern `weilPairingCharZero` already uses):

```lean
/-- A `k`-rational Weierstrass chart for `E` at the geometric point, with its Galois
equivariance. -/
structure GaloisFibreChart (k : Type u) [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (L : Type u) [Field L] [DecidableEq L] [IsAlgClosed L] [Algebra k L] where
  W : WeierstrassCurve k
  elliptic : (W.baseChange L).toAffine.IsElliptic
  dict : E.Point (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≃+
    (W.baseChange L).toAffine.Point
  equivariant : ∀ (σ : L ≃ₐ[k] L) (P Q : _),
    (Q.1 : _ ⟶ E.E) = Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ (P.1 : _ ⟶ E.E) →
      dict Q = galoisPointEquiv W σ (dict P)
```

* **E′** — from a `GaloisFibreChart`, transport `fieldWeilPairing_galois`: the pairing on
  scheme points is `σ`-equivariant. Short; no chart internals.
* **G′** — assemble `p` from E′ + the two landed fibre dictionaries
  (`torsionAlgebraFibreEquiv_comp_algEquiv`, `muNAlgebraFibreEquiv_comp_algEquiv`) and
  call `exists_pairingAlgebraHom_of_galoisEquivariant`. Per the review, check the three
  named items: diagonal equivariance on the pair fibre, equivariance of the pair
  dictionary, and the variance `O(μ_N) → O(E[N]) ⊗ O(E[N])`.
* **F′** (the remaining obligation) — construct a `GaloisFibreChart` over `Spec k` from
  `localPresentationTop` (`EllipticCurve/GlobalChartOverField.lean`) + nodes A–D. This is
  where `Γ(Spec k, ⊤) ≅ k` is installed: set `W := Pr.W.map (ΓSpecIso (of k)).hom.hom`,
  give `L` the induced `Γ(Spec k, ⊤)`-algebra structure through the iso, check `σ` is
  `Γ(Spec k, ⊤)`-linear (it is, since the iso is over `k`), and identify
  `Spec.map (ofHom (algebraMap Γ(Spec k,⊤) L)) ≫ chartρ ⊤` with
  `Spec.map (ofHom (algebraMap k L))`. **Node D is exactly the `equivariant` field**, so
  F′ is transport only — no new mathematics — but it is the fiddly leaf, and it must not
  be attacked as one goal (split: `chartρ_top`, the algebra-structure transport, the
  curve-map comparison, then the assembly).

With E′/G′ done, R holds **conditionally on a `GaloisFibreChart`**; F′ makes it
unconditional.
